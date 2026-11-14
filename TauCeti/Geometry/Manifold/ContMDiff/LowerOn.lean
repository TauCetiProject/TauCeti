/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Algebra.Order.Group.Indicator
import Mathlib.Geometry.Manifold.Algebra.LieGroup

/-!
# Lowering a function on disjoint open sets

Given pairwise disjoint sets `U i` and functions `g i`, the function `TauCeti.lowerOn U g f` is
`f - g i` on `U i` and `f` outside the `U i`. When each `g i` is smooth on the open set `U i` and
vanishes on `U i` outside a closed set `K i ⊆ U i`, the lowered function is smooth and agrees
with `f` near every point outside the `K i`.

This is the localization step of Milnor's proof of the cell attachment theorem (Theorem 3.2 of
*Morse Theory*), which replaces a function `f` near each critical point by
`F = f - μ(‖u‖² + 2‖v‖²)`, lowered by a cutoff in a chart and equal to `f` elsewhere; Bott's
attachment of negative disc bundles runs the same construction fibrewise in normal forms over
critical submanifolds.

## Main definitions

* `TauCeti.lowerOn`: the function `f - ∑ i, (U i).indicator (g i)`.

## Main results

* `TauCeti.setOf_lowerOn_le`: lowering where `f` is below `b` keeps the sublevel `{f ≤ b}`.
* `TauCeti.lowerOn_eq_of_notMem`: the lowered function is `f` outside the supports `K i`.
* `TauCeti.contMDiff_lowerOn`: the lowered function is smooth.
* `TauCeti.lowerOn_eventuallyEq`: it agrees with `f` near points outside the supports `K i`.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  proof of Theorem 3.2.
-/

public section

noncomputable section

open Function Set Filter Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {M ι : Type*} {U K : ι → Set M} {g : ι → M → ℝ} {f : M → ℝ} {i : ι} {x : M}

/-- The function `f` lowered by `g i` on each `U i`: it is `f - g i` on `U i` when the `U i` are
pairwise disjoint, and `f` outside the `U i`. -/
def lowerOn [Fintype ι] (U : ι → Set M) (g : ι → M → ℝ) (f : M → ℝ) (x : M) : ℝ :=
  f x - ∑ i, (U i).indicator (g i) x

variable [Fintype ι]

theorem lowerOn_def (U : ι → Set M) (g : ι → M → ℝ) (f : M → ℝ) (x : M) :
    lowerOn U g f x = f x - ∑ i, (U i).indicator (g i) x := by
  rw [lowerOn]

theorem lowerOn_of_mem (hU : Pairwise (Disjoint on U)) (hx : x ∈ U i) :
    lowerOn U g f x = f x - g i x := by
  rw [lowerOn_def, Finset.sum_eq_single i (fun j _ hji ↦ indicator_of_notMem
    (fun hj ↦ (hU hji).ne_of_mem hj hx rfl) _) (by simp), indicator_of_mem hx]

@[simp]
theorem lowerOn_of_forall_notMem (hx : ∀ i, x ∉ U i) : lowerOn U g f x = f x := by
  simp [lowerOn_def, indicator_of_notMem (hx _)]

theorem lowerOn_le (hg : ∀ i, ∀ y ∈ U i, 0 ≤ g i y) (x : M) : lowerOn U g f x ≤ f x :=
  sub_le_self _ (Finset.sum_nonneg fun i _ ↦ indicator_nonneg (hg i) _)

/-- Lowering by nonnegative functions does not change the sublevel `{f ≤ b}` if `f ≤ b` wherever
some `g i` is nonzero on `U i`. -/
theorem setOf_lowerOn_le (hU : Pairwise (Disjoint on U)) (hg : ∀ i, ∀ y ∈ U i, 0 ≤ g i y)
    {b : ℝ} (hgb : ∀ i, ∀ y ∈ U i, g i y ≠ 0 → f y ≤ b) :
    {x | lowerOn U g f x ≤ b} = {x | f x ≤ b} := by
  ext x
  refine ⟨fun hx ↦ ?_, fun hx ↦ (lowerOn_le hg x).trans hx⟩
  rw [mem_ofPred_eq] at hx ⊢
  by_cases hxU : ∃ i, x ∈ U i
  · obtain ⟨i, hi⟩ := hxU
    by_cases h : g i x = 0
    · rwa [lowerOn_of_mem hU hi, h, sub_zero] at hx
    · exact hgb i x hi h
  · rwa [lowerOn_of_forall_notMem (not_exists.1 hxU)] at hx

variable (hgK : ∀ i, EqOn (g i) 0 (U i \ K i))
include hgK

omit [Fintype ι] in
private theorem indicator_eq_zero_of_notMem (i : ι) {y : M} (hy : y ∉ K i) :
    (U i).indicator (g i) y = 0 := by
  by_cases hyU : y ∈ U i
  · rw [indicator_of_mem hyU]
    exact hgK i ⟨hyU, hy⟩
  · exact indicator_of_notMem hyU _

/-- Outside the sets `K i`, the lowered function is `f`. -/
theorem lowerOn_eq_of_notMem (hx : x ∉ ⋃ i, K i) : lowerOn U g f x = f x := by
  rw [lowerOn_def, Finset.sum_eq_zero fun i _ ↦
    indicator_eq_zero_of_notMem hgK i fun h ↦ hx (mem_iUnion.2 ⟨i, h⟩), sub_zero]

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  (hK : ∀ i, IsClosed (K i))
include hK

/-- Outside the closed sets `K i`, the lowered function agrees with `f` on a neighbourhood. -/
theorem lowerOn_eventuallyEq (hx : x ∉ ⋃ i, K i) : lowerOn U g f =ᶠ[𝓝 x] f := by
  filter_upwards [(isClosed_iUnion_of_finite hK).isOpen_compl.mem_nhds hx] with y hy
  exact lowerOn_eq_of_notMem hgK hy

/-- **The lowered function is smooth** when `f` is smooth and each `g i` is smooth on the open set
`U i` and vanishes on `U i` outside the closed set `K i ⊆ U i`. -/
theorem contMDiff_lowerOn {n : ℕ∞ω} (hU : ∀ i, IsOpen (U i)) (hKU : ∀ i, K i ⊆ U i)
    (hf : ContMDiff I 𝓘(ℝ) n f) (hg : ∀ i, ContMDiffOn I 𝓘(ℝ) n (g i) (U i)) :
    ContMDiff I 𝓘(ℝ) n (lowerOn U g f) := by
  refine ContMDiff.sub hf (ContMDiff.sum fun i _ ↦ contMDiff_of_tsupport fun y hy ↦ ?_)
  -- The lowering term is supported in `K i`, inside the open set `U i` where it equals `g i`.
  have hsupp : support ((U i).indicator (g i)) ⊆ K i := fun y hy ↦
    not_not.1 fun h ↦ hy (indicator_eq_zero_of_notMem hgK i h)
  have hyU : y ∈ U i := hKU i (closure_minimal hsupp (hK i) hy)
  exact ((hg i).contMDiffAt ((hU i).mem_nhds hyU)).congr_of_eventuallyEq
    (eventuallyEq_of_mem ((hU i).mem_nhds hyU) fun y hy ↦ indicator_of_mem hy _)

end TauCeti
