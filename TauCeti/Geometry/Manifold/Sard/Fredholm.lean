/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Fredholm.Basic
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import TauCeti.Geometry.Manifold.RegularValue
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Index
import TauCeti.Analysis.Fredholm.SardSmale
import TauCeti.Geometry.Manifold.Sard.Meagre

/-!
# The Sard--Smale theorem for Fredholm maps between Banach manifolds

A map `f : M → N` between manifolds modelled on real Banach spaces is a *Fredholm map* when its
manifold derivative `mfderiv I J f x` is a Fredholm operator at every point. This file proves
Smale's theorem for such maps at his sharp regularity, in index at most two: if the derivative at
each point `x` has index `i x ≤ 2` and `f` is `C^k` at `x` with `k > max (i x, 0)`, then the
critical values of `f` form a meagre set, so its regular values form a residual set. The source
is hereditarily Lindelöf, for instance second countable; both manifolds are without boundary.
The models need not be finite-dimensional.

The proof reads `f` in pairs of extended charts. Within the chart sources the coordinate expression
`extChartAt J y₀ ∘ f ∘ (extChartAt I x₀).symm` has Fréchet derivative equal to the manifold
derivative of `f` composed on both sides with the invertible derivatives of the charts
(`HasMFDerivAt.hasFDerivWithinAt_of_mem_source`). So it is again a Fredholm map, with the same index
and the same critical points, and the Sard--Smale theorem on Banach spaces
(`TauCeti.isMeagre_image_criticalPoints_of_isFredholm_of_index_le_two`) applies in coordinates.
Inverse charts carry meagre sets to meagre sets, and countably many pairs of charts cover the
source (`TauCeti.isMeagre_image_of_forall_isMeagre_image_extChartAt`).

Index at most two is the range in which the finite-dimensional Morse--Sard theorem is available at
the sharp regularity (`TauCeti.interior_image_criticalPoints_eq_empty_of_finrank_le_add_two`), and
it covers the moduli spaces of index one and two that are counted by Morse and Floer differentials
and their squares.

## Main results

* `TauCeti.isMeagre_image_of_not_isRegularPoint_of_index_le_two`: the image of a set of critical
  points at which `f` is Fredholm of index at most two and sharply regular is meagre.
* `ContMDiff.isMeagre_image_criticalPoints_of_index_le_two`: the critical values of a sharply
  regular Fredholm map of index at most two are meagre.
* `ContMDiff.mem_residual_setOf_isRegularValue_of_index_le_two`: its regular values form a
  residual set.

## References

* S. Smale, *An infinite dimensional version of Sard's theorem*, Amer. J. Math. 87 (1965),
  861--866, Theorem 1.3.
* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Appendix A.5.
-/

public section

open Function Set Filter
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {n : ℕ∞ω}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I n M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [J.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J n N]
  {f : M → N} {s : Set M}

omit [J.Boundaryless] in
/-- The critical points seen by a fixed pair of charts have meagre coordinate image. -/
private theorem isMeagre_image_extChartAt_inter_chartAt_source [HereditarilyLindelofSpace M]
    (hf : ∀ x ∈ s, ContMDiffAt I J n f x) (hFred : ∀ x ∈ s, (mfderiv I J f x).IsFredholm)
    (hindex : ∀ x ∈ s, (mfderiv I J f x).index ≤ 2)
    (hn : ∀ x ∈ s, (((mfderiv I J f x).index.toNat + 1 : ℕ) : ℕ∞ω) ≤ n)
    (hs : ∀ x ∈ s, ¬ IsRegularPoint I J f x) (x₀ : M) (y₀ : N) :
    IsMeagre ((extChartAt J y₀ ∘ f ∘ (extChartAt I x₀).symm) ''
      (extChartAt I x₀ '' (s ∩ (chartAt H x₀).source ∩ f ⁻¹' (chartAt H' y₀).source))) := by
  let g : E → E' := extChartAt J y₀ ∘ f ∘ (extChartAt I x₀).symm
  let u := s ∩ (chartAt H x₀).source ∩ f ⁻¹' (chartAt H' y₀).source
  let v := extChartAt I x₀ '' u
  rcases u.eq_empty_or_nonempty with hu | ⟨x₁, hx₁⟩
  · change IsMeagre (g '' (extChartAt I x₀ '' u))
    rw [hu, image_empty, image_empty]
    exact IsMeagre.empty
  -- The regularity is at least `C¹`, so the charts of both atlases are differentiable.
  have hn1 : (1 : ℕ∞ω) ≤ n := le_trans (by exact_mod_cast Nat.le_add_left 1 _) (hn x₁ hx₁.1.1)
  have : IsManifold I 1 M := IsManifold.of_le hn1
  have : IsManifold J 1 N := IsManifold.of_le hn1
  have hn0 : n ≠ 0 := fun h ↦ by simp [h] at hn1
  have hgs : ∀ z ∈ v, ContDiffAt ℝ n g z := by
    rintro _ ⟨x, hx, rfl⟩
    exact ((contMDiffAt_iff_of_mem_source hx.1.2 hx.2).1 (hf x hx.1.1)).2.contDiffAt
      (by simp [I.range_eq_univ])
  -- In coordinates, the derivative of `f` is its manifold derivative between two equivalences,
  -- so it is Fredholm with the same index.
  have hderiv : ∀ x ∈ u, (fderiv ℝ g (extChartAt I x₀ x)).IsFredholm ∧
      (fderiv ℝ g (extChartAt I x₀ x)).index = (mfderiv I J f x).index := by
    intro x hx
    have hx' : x ∈ (extChartAt I x₀).source := by rw [extChartAt_source]; exact hx.1.2
    have hfx' : f x ∈ (extChartAt J y₀).source := by rw [extChartAt_source]; exact hx.2
    obtain ⟨A, hA⟩ := isInvertible_mfderiv_extChartAt (I := J) hfx'
    obtain ⟨B, hB⟩ := isInvertible_mfderivWithin_extChartAt_symm (I := I)
      ((extChartAt I x₀).map_source hx')
    -- The chart derivatives, typed by the model spaces (`TangentSpace` unfolds to the model).
    let A' : TangentSpace J (f x) ≃L[ℝ] E' := A
    let B' : E ≃L[ℝ] TangentSpace I x := B
    have h := ((hf x hx.1.1).mdifferentiableAt hn0).hasMFDerivAt
      |>.hasFDerivWithinAt_of_mem_source hx.1.2 hx.2
      |>.hasFDerivAt (by rw [I.range_eq_univ]; exact univ_mem)
    have hfd : fderiv ℝ g (extChartAt I x₀ x) =
        (A' : TangentSpace J (f x) →L[ℝ] E') ∘L mfderiv I J f x ∘L
          (B' : E →L[ℝ] TangentSpace I x) := by
      rw [h.fderiv, ← hA, ← hB]
      rfl
    rw [hfd]
    exact ⟨ContinuousLinearMap.isFredholm_equiv_comp.2
        (ContinuousLinearMap.isFredholm_comp_equiv.2 (hFred x hx.1.1)),
      by rw [ContinuousLinearMap.index_equiv_comp, ContinuousLinearMap.index_comp_equiv]⟩
  have hcrit : ∀ z ∈ v, ¬ Surjective (fderiv ℝ g z) := by
    rintro _ ⟨x, hx, rfl⟩
    have h := isRegularPoint_iff_surjective_fderivWithin
      ((hf x hx.1.1).mdifferentiableAt hn0) hx.1.2 hx.2
    simpa only [I.range_eq_univ, fderivWithin_univ] using (h.not.mp (hs x hx.1.1))
  have : LindelofSpace v := isLindelof_iff_lindelofSpace.1 <|
    (HereditarilyLindelofSpace.isLindelof u).image_of_continuousOn
      ((continuousOn_extChartAt x₀).mono fun x hx ↦ by rw [extChartAt_source]; exact hx.1.2)
  have h := isMeagre_image_criticalPoints_of_isFredholm_of_index_le_two (U := v) hgs
    (by rintro _ ⟨x, hx, rfl⟩; exact (hderiv x hx).1)
    (by rintro _ ⟨x, hx, rfl⟩; rw [(hderiv x hx).2]; exact hindex x hx.1.1)
    (by rintro _ ⟨x, hx, rfl⟩; rw [(hderiv x hx).2]; exact hn x hx.1.1)
  apply h.mono
  rintro _ ⟨z, hz, rfl⟩
  exact ⟨z, ⟨hz, hcrit z hz⟩, rfl⟩

/-- **The Sard--Smale theorem on Banach manifolds, at the sharp regularity, in index at most two.**
Let `s` be a set of critical points of `f` at each of which `mfderiv I J f x` is a Fredholm
operator of index `i x ≤ 2` and `f` is `C^k` with `k > max (i x, 0)`. Then `f '' s` is meagre.
The source is hereditarily Lindelöf, for instance second countable, and both manifolds are without
boundary; the regularity is required in the ambient manifold at the points of `s`. -/
theorem isMeagre_image_of_not_isRegularPoint_of_index_le_two [HereditarilyLindelofSpace M]
    (hf : ∀ x ∈ s, ContMDiffAt I J n f x) (hFred : ∀ x ∈ s, (mfderiv I J f x).IsFredholm)
    (hindex : ∀ x ∈ s, (mfderiv I J f x).index ≤ 2)
    (hn : ∀ x ∈ s, (((mfderiv I J f x).index.toNat + 1 : ℕ) : ℕ∞ω) ≤ n)
    (hs : ∀ x ∈ s, ¬ IsRegularPoint I J f x) : IsMeagre (f '' s) :=
  have : LindelofSpace s := isLindelof_iff_lindelofSpace.1 (HereditarilyLindelofSpace.isLindelof s)
  isMeagre_image_of_forall_isMeagre_image_extChartAt (fun x hx ↦ (hf x hx).continuousAt)
    (isMeagre_image_extChartAt_inter_chartAt_source hf hFred hindex hn hs)

/-- **The Sard--Smale theorem on Banach manifolds, at the sharp regularity, in index at most two.**
The critical values of a `C^n` Fredholm map whose derivative at each point `x` has index
`i x ≤ 2`, with `n > max (i x, 0)`, form a meagre set. The source is hereditarily Lindelöf, for
instance second countable, and both manifolds are without boundary. -/
theorem _root_.ContMDiff.isMeagre_image_criticalPoints_of_index_le_two
    [HereditarilyLindelofSpace M] (hf : ContMDiff I J n f)
    (hFred : ∀ x, (mfderiv I J f x).IsFredholm) (hindex : ∀ x, (mfderiv I J f x).index ≤ 2)
    (hn : ∀ x, (((mfderiv I J f x).index.toNat + 1 : ℕ) : ℕ∞ω) ≤ n) :
    IsMeagre (f '' {x | ¬ IsRegularPoint I J f x}) :=
  isMeagre_image_of_not_isRegularPoint_of_index_le_two (fun x _ ↦ hf x) (fun x _ ↦ hFred x)
    (fun x _ ↦ hindex x) (fun x _ ↦ hn x) fun _ hx ↦ hx

/-- The regular values of a `C^n` Fredholm map of index at most two between Banach manifolds, with
`n` greater than the index and positive, form a residual set; in particular they are dense when
the target is a Baire space. The hypotheses are those of
`ContMDiff.isMeagre_image_criticalPoints_of_index_le_two`. -/
theorem _root_.ContMDiff.mem_residual_setOf_isRegularValue_of_index_le_two
    [HereditarilyLindelofSpace M] (hf : ContMDiff I J n f)
    (hFred : ∀ x, (mfderiv I J f x).IsFredholm) (hindex : ∀ x, (mfderiv I J f x).index ≤ 2)
    (hn : ∀ x, (((mfderiv I J f x).index.toNat + 1 : ℕ) : ℕ∞ω) ≤ n) :
    {y | IsRegularValue I J f y} ∈ residual N := by
  rw [setOf_isRegularValue_eq_compl_image]
  exact hf.isMeagre_image_criticalPoints_of_index_le_two hFred hindex hn

end TauCeti

end
