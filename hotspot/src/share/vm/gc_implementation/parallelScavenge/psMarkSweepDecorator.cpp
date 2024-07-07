/*
 * Copyright (c) 2001, 2012, Oracle and/or its affiliates. All rights reserved.
 * DO NOT ALTER OR REMOVE COPYRIGHT NOTICES OR THIS FILE HEADER.
 *
 * This code is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License version 2 only, as
 * published by the Free Software Foundation.
 *
 * This code is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
 * version 2 for more details (a copy is included in the LICENSE file that
 * accompanied this code).
 *
 * You should have received a copy of the GNU General Public License version
 * 2 along with this work; if not, write to the Free Software Foundation,
 * Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301 USA.
 *
 * Please contact Oracle, 500 Oracle Parkway, Redwood Shores, CA 94065 USA
 * or visit www.oracle.com if you need additional information or have any
 * questions.
 *
 */

#include "precompiled.hpp"
#include "classfile/systemDictionary.hpp"
#include "gc_implementation/parallelScavenge/objectStartArray.hpp"
#include "gc_implementation/parallelScavenge/parallelScavengeHeap.hpp"
#include "gc_implementation/parallelScavenge/psMarkSweep.hpp"
#include "gc_implementation/parallelScavenge/psMarkSweepDecorator.hpp"
#include "gc_implementation/shared/liveRange.hpp"
#include "gc_implementation/shared/markSweep.inline.hpp"
#include "gc_implementation/shared/spaceDecorator.hpp"
#include "oops/oop.inline.hpp"

PSMarkSweepDecorator* PSMarkSweepDecorator::_destination_decorator = NULL;


void PSMarkSweepDecorator::set_destination_decorator_tenured() {
  ParallelScavengeHeap* heap = (ParallelScavengeHeap*)Universe::heap();
  assert(heap->kind() == CollectedHeap::ParallelScavengeHeap, "Sanity");

  _destination_decorator = heap->old_gen()->object_mark_sweep();
}

void PSMarkSweepDecorator::advance_destination_decorator() {
  ParallelScavengeHeap* heap = (ParallelScavengeHeap*)Universe::heap();
  assert(heap->kind() == CollectedHeap::ParallelScavengeHeap, "Sanity");

  assert(_destination_decorator != NULL, "Sanity");

  PSMarkSweepDecorator* first = heap->old_gen()->object_mark_sweep();
  PSMarkSweepDecorator* second = heap->young_gen()->eden_mark_sweep();
  PSMarkSweepDecorator* third = heap->young_gen()->from_mark_sweep();
  PSMarkSweepDecorator* fourth = heap->young_gen()->to_mark_sweep();

  if ( _destination_decorator == first ) {
    _destination_decorator = second;
  } else if ( _destination_decorator == second ) {
    _destination_decorator = third;
  } else if ( _destination_decorator == third ) {
    _destination_decorator = fourth;
  } else {
    fatal("PSMarkSweep attempting to advance past last compaction area");
  }
}

PSMarkSweepDecorator* PSMarkSweepDecorator::destination_decorator() {
  assert(_destination_decorator != NULL, "Sanity");

  return _destination_decorator;
}

// FIX ME FIX ME FIX ME FIX ME!!!!!!!!!
// The object forwarding code is duplicated. Factor this out!!!!!
//
// This method "precompacts" objects inside its space to dest. It places forwarding
// pointers into markOops for use by adjust_pointers. If "dest" should overflow, we
// finish by compacting into our own space.

//整理算法，遍历堆各个区域对象，从区域头部开始，将存活对象向头部方向移动
//设置一个压缩头部指针，每次遍历对象，若对象存活，则指针向前移动，且如果前面存在不存活对象，则需要移动该对象到压缩头部指针处
//若对象不存活，则继续向后查找，直到找到存活一个存活对象
void PSMarkSweepDecorator::precompact() {
  // Reset our own compact top.
  set_compaction_top(space()->bottom());

  /* We allow some amount of garbage towards the bottom of the space, so
   * we don't start compacting before there is a significant gain to be made.
   * Occasionally, we want to ensure a full compaction, which is determined
   * by the MarkSweepAlwaysCompactCount parameter. This is a significant
   * performance improvement!
   */
  bool skip_dead = ((PSMarkSweep::total_invocations() % MarkSweepAlwaysCompactCount) != 0);

  size_t allowed_deadspace = 0;
  if (skip_dead) {
      //跳过不存或对象，即忽略一定的空间间隙
    const size_t ratio = allowed_dead_ratio();
    allowed_deadspace = space()->capacity_in_words() * ratio / 100;
  }

  // Fetch the current destination decorator
  PSMarkSweepDecorator* dest = destination_decorator();
  ObjectStartArray* start_array = dest->start_array();

  HeapWord* compact_top = dest->compaction_top(); //压缩头部指针
  HeapWord* compact_end = dest->space()->end();//压缩尾部指针

  HeapWord* q = space()->bottom();//头部对象
  HeapWord* t = space()->top();//尾部对象

  HeapWord*  end_of_live= q;//最后面一个存活对象    /* One byte beyond the last byte of the last
                                   live object. */
  HeapWord*  first_dead = space()->end();//第一个不存活对象  /* The first dead object. */
  LiveRange* liveRange  = NULL;//连续存活对象区域   /* The current live range, recorded in the
                                   first header of preceding free area. */
  _first_dead = first_dead;

  const intx interval = PrefetchScanIntervalInBytes;

  //遍历对象
  while (q < t) {
    assert(oop(q)->mark()->is_marked() || oop(q)->mark()->is_unlocked() ||
           oop(q)->mark()->has_bias_pattern(),
           "these are the only valid states during a mark sweep");
    if (oop(q)->is_gc_marked()) {
        //对象被标记，存活
      /* prefetch beyond q */
      Prefetch::write(q, interval);
      size_t size = oop(q)->size();

      //最大可压缩大小
      size_t compaction_max_size = pointer_delta(compact_end, compact_top);

      // This should only happen if a space in the young gen overflows the
      // old gen. If that should happen, we null out the start_array, because
      // the young spaces are not covered by one.
      //对象的大小比可压缩区域更大，说明这个对象跨区域了
      while(size > compaction_max_size) {
        // First record the last compact_top
        dest->set_compaction_top(compact_top);

        // Advance to the next compaction decorator
        //变更 收集区域
        advance_destination_decorator();
        dest = destination_decorator();

        // Update compaction info
        start_array = dest->start_array();
        compact_top = dest->compaction_top();
        compact_end = dest->space()->end();
        assert(compact_top == dest->space()->bottom(), "Advanced to space already in use");
        assert(compact_end > compact_top, "Must always be space remaining");
        compaction_max_size =
          pointer_delta(compact_end, compact_top);
      }

      // store the forwarding pointer into the mark word
      //说明前面存在着不存活对象，或者发生区域变换，将该对象转发到区域，此处仅仅变更了对象头
      if (q != compact_top) {
        oop(q)->forward_to(oop(compact_top));
        assert(oop(q)->is_gc_marked(), "encoding the pointer should preserve the mark");
      } else {
        // if the object isn't moving we can just set the mark to the default
        // mark and handle it specially later on.
        //无需转移，标记头为默认值
        oop(q)->init_mark();
        assert(oop(q)->forwardee() == NULL, "should be forwarded to NULL");
      }

      // Update object start array
      if (start_array) {
        start_array->allocate_block(compact_top);
      }

      //整理指针 向前偏移对象大小
      compact_top += size;
      assert(compact_top <= dest->space()->end(),
        "Exceeding space in destination");
      //对象指针向前偏移
      q += size;
      //设置最后一个存活对象
      end_of_live = q;
    } else {
        //对象没被标记，说明对象不存活
      /* run over all the contiguous dead objects */
      HeapWord* end = q;
      do {
        /* prefetch beyond end */
        Prefetch::write(end, interval);
        end += oop(end)->size();
        //向后查找一个，直到找到一个被标记，即存活对象
      } while (end < t && (!oop(end)->is_gc_marked()));

      /* see if we might want to pretend this object is alive so that
       * we don't have to compact quite as often.
       */
      //允许存在不存活和对象区域，并且前面都是连续存活的对象
      //该做法通过不整理不存活对象的空间，以达到存活对象空间的连续性，来减少存活对象的复制次数
      if (allowed_deadspace > 0 && q == compact_top) {
          //不存活对象空间大小
        size_t sz = pointer_delta(end, q);
        //向不存活区域插入 sz 大小的数组对象
        if (insert_deadspace(allowed_deadspace, q, sz)) {
            //最大压缩空间
          size_t compaction_max_size = pointer_delta(compact_end, compact_top);

          // This should only happen if a space in the young gen overflows the
          // old gen. If that should happen, we null out the start_array, because
          // the young spaces are not covered by one.
          //不存活对象连续空间大小，超过了该区域的最大压缩空间
          while (sz > compaction_max_size) {
            // First record the last compact_top
            dest->set_compaction_top(compact_top);

            // Advance to the next compaction decorator
            //变更区域
            advance_destination_decorator();
            dest = destination_decorator();

            // Update compaction info
            start_array = dest->start_array();
            compact_top = dest->compaction_top();
            compact_end = dest->space()->end();
            assert(compact_top == dest->space()->bottom(), "Advanced to space already in use");
            assert(compact_end > compact_top, "Must always be space remaining");
            compaction_max_size =
              pointer_delta(compact_end, compact_top);
          }

          // store the forwarding pointer into the mark word
          //前面存在不存活对象
          if (q != compact_top) {
              //设置 下一个存活对象的位置，  该设置是为了在后续真正整理对象时，可以快速跳转。因为该位置会有一个存活对象被转发过来
            oop(q)->forward_to(oop(compact_top));
            assert(oop(q)->is_gc_marked(), "encoding the pointer should preserve the mark");
          } else {
            // if the object isn't moving we can just set the mark to the default
            // mark and handle it specially later on.
            //没发生变更，恢复对象头
            oop(q)->init_mark();
            assert(oop(q)->forwardee() == NULL, "should be forwarded to NULL");
          }

          // Update object start array
          if (start_array) {
            start_array->allocate_block(compact_top);
          }

          //压缩指针后移
          compact_top += sz;
          assert(compact_top <= dest->space()->end(),
            "Exceeding space in destination");

          q = end;
          end_of_live = end;
          continue;
        }
      }

      /* for the previous LiveRange, record the end of the live objects. */
      if (liveRange) {
          //设置存活对象的范围的结束区域
        liveRange->set_end(q);
      }

      /* record the current LiveRange object.
       * liveRange->start() is overlaid on the mark word.
       */
      //创建新的存活对象范围， 将第一个不存活对象当作LiveRange
      liveRange = (LiveRange*)q;
      //设置第一个存活的对象位置，由于 LiveRange 和 Oop的第一个字段都是指针， LiveRange 第一个字段设置为 下一个存活对象的指针，相当于 Oop对象设置对象头为 下一个存活对象指针
      liveRange->set_start(end);
      liveRange->set_end(end);

      /* see if this is the first dead region. */
      if (q < first_dead) {
        first_dead = q;
      }

      /* move on to the next object */
      //偏移到下一个存活对象处
      q = end;
    }
  }

  assert(q == t, "just checking");
  if (liveRange != NULL) {
    liveRange->set_end(q);
  }
  _end_of_live = end_of_live;
  if (end_of_live < first_dead) {
    first_dead = end_of_live;
  }
  _first_dead = first_dead;

  // Update compaction top
  dest->set_compaction_top(compact_top);
}

bool PSMarkSweepDecorator::insert_deadspace(size_t& allowed_deadspace_words,
                                            HeapWord* q, size_t deadlength) {
  if (allowed_deadspace_words >= deadlength) {
    allowed_deadspace_words -= deadlength;
    CollectedHeap::fill_with_object(q, deadlength);
    oop(q)->set_mark(oop(q)->mark()->set_marked());
    assert((int) deadlength == oop(q)->size(), "bad filler object size");
    // Recall that we required "q == compaction_top".
    return true;
  } else {
    allowed_deadspace_words = 0;
    return false;
  }
}

//调整对象指针，调整为转发位置或者不变
void PSMarkSweepDecorator::adjust_pointers() {
  // adjust all the interior pointers to point at the new locations of objects
  // Used by MarkSweep::mark_sweep_phase3()

  HeapWord* q = space()->bottom();
  HeapWord* t = _end_of_live;  // Established by "prepare_for_compaction".

  assert(_first_dead <= _end_of_live, "Stands to reason, no?");

  if (q < t && _first_dead > q &&
      !oop(q)->is_gc_marked()) {
    // we have a chunk of the space which hasn't moved and we've
    // reinitialized the mark word during the previous pass, so we can't
    // use is_gc_marked for the traversal.
    HeapWord* end = _first_dead;

    while (q < end) {
      // point all the oops to the new location
      size_t size = oop(q)->adjust_pointers();
      q += size;
    }

    if (_first_dead == t) {
      q = t;
    } else {
      // $$$ This is funky.  Using this to read the previously written
      // LiveRange.  See also use below.
      q = (HeapWord*)oop(_first_dead)->mark()->decode_pointer();
    }
  }
  const intx interval = PrefetchScanIntervalInBytes;

  debug_only(HeapWord* prev_q = NULL);
  while (q < t) {
    // prefetch beyond q
    Prefetch::write(q, interval);
    if (oop(q)->is_gc_marked()) {
      // q is alive
      // point all the oops to the new location
      // 对象是存活的，获取对象新位置，变更对象引用为新位置
      size_t size = oop(q)->adjust_pointers();
      debug_only(prev_q = q);
      q += size;
    } else {
      // q is not a live object, so its mark should point at the next
      // live object
      debug_only(prev_q = q);
      //如果对象不存活，则应该指向下一个存活对象， 该操作在LiveRange设置
      q = (HeapWord*) oop(q)->mark()->decode_pointer();
      assert(q > prev_q, "we should be moving forward through memory");
    }
  }

  assert(q == t, "just checking");
}

//整理对象，从头部向最后一个存活对象遍历，移动存活对象到端界
void PSMarkSweepDecorator::compact(bool mangle_free_space ) {
  // Copy all live objects to their new location
  // Used by MarkSweep::mark_sweep_phase4()

  HeapWord*       q = space()->bottom(); //第一个对象
  HeapWord* const t = _end_of_live;//最后一个存活对象
  debug_only(HeapWord* prev_q = NULL);

  if (q < t && _first_dead > q &&
      !oop(q)->is_gc_marked()) {
#ifdef ASSERT
    // we have a chunk of the space which hasn't moved and we've reinitialized the
    // mark word during the previous pass, so we can't use is_gc_marked for the
    // traversal.
    HeapWord* const end = _first_dead;

    while (q < end) {
      size_t size = oop(q)->size();
      assert(!oop(q)->is_gc_marked(), "should be unmarked (special dense prefix handling)");
      debug_only(prev_q = q);
      q += size;
    }
#endif

    if (_first_dead == t) {
      q = t;
    } else {
      // $$$ Funky
      q = (HeapWord*) oop(_first_dead)->mark()->decode_pointer();
    }
  }

  const intx scan_interval = PrefetchScanIntervalInBytes;
  const intx copy_interval = PrefetchCopyIntervalInBytes;

  while (q < t) {
    if (!oop(q)->is_gc_marked()) {
        //没被标记，不存活
      // mark is pointer to next marked oop
      debug_only(prev_q = q);
      //从对象头中取出下一个存活对象的指针， 该操作在LiveRange设置
      q = (HeapWord*) oop(q)->mark()->decode_pointer();
      assert(q > prev_q, "we should be moving forward through memory");
    } else {
      // prefetch beyond q
      Prefetch::read(q, scan_interval);

      // size and destination
      size_t size = oop(q)->size();
      //获取要转移的位置，该地址在 preCompact存放
      HeapWord* compaction_top = (HeapWord*)oop(q)->forwardee();

      // prefetch beyond compaction_top
      Prefetch::write(compaction_top, copy_interval);

      // copy object and reinit its mark
      assert(q != compaction_top, "everything in this pass should be moving");
      //复制对象过去
      Copy::aligned_conjoint_words(q, compaction_top, size);
      //初始化头部，未标记
      oop(compaction_top)->init_mark();
      assert(oop(compaction_top)->klass() != NULL, "should have a class");

      debug_only(prev_q = q);
      //指针向后偏移
      q += size;
    }
  }

  assert(compaction_top() >= space()->bottom() && compaction_top() <= space()->end(),
         "should point inside space");
  //设置已经使用区域结尾为压缩指针处
  space()->set_top(compaction_top());

  if (mangle_free_space) {
    space()->mangle_unused_area();
  }
}
