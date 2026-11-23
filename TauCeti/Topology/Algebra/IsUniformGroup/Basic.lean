/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Topology.Algebra.IsUniformGroup.Basic

/-!
# Finite products of locally uniformly convergent families

In a commutative uniform group, a finite product of families converging locally uniformly on a
set converges locally uniformly to the product of the limits
(`TendstoLocallyUniformlyOn.finsetProd`, additively `TendstoLocallyUniformlyOn.finsetSum`). This
iterates Mathlib's `TendstoLocallyUniformlyOn.mul`.
-/

public section

open Filter

variable {α ι κ X : Type*} [UniformSpace α] [CommGroup α] [IsUniformGroup α] [TopologicalSpace X]
  {l : Filter ι} {s : Set X}

/-- A finite product of families converging locally uniformly on `s` converges locally uniformly on
`s` to the product of the limits. -/
@[to_additive /-- A finite sum of families converging locally uniformly on `s` converges locally
uniformly on `s` to the sum of the limits. -/]
theorem TendstoLocallyUniformlyOn.finsetProd {F : κ → ι → X → α} {f : κ → X → α} (t : Finset κ)
    (h : ∀ k ∈ t, TendstoLocallyUniformlyOn (F k) (f k) l s) :
    TendstoLocallyUniformlyOn (fun i x => ∏ k ∈ t, F k i x) (fun x => ∏ k ∈ t, f k x) l s := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    simpa only [Finset.prod_empty] using
      (tendsto_const_nhds (x := (1 : α)) (f := l)).tendstoUniformlyOn_const s
        |>.tendstoLocallyUniformlyOn
  | insert a t ha ih =>
    simp only [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a t)).fun_mul
      (ih fun k hk => h k (Finset.mem_insert_of_mem hk))
