/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.DefiningFunction.Basic
public import TauCeti.Geometry.Manifold.RegularValue.Scalar.Sublevel.Basic

/-!
# The boundary defining function of a regular sublevel

Let `f : M → ℝ` be a smooth function on a boundaryless smooth manifold modelled on a real space `E`
of dimension `n + 1`, and let `a` be a regular value of `f`. The sublevel `{f ≤ a}` is a smooth
manifold with boundary for the atlas `TauCeti.scalarRegularSublevelChartedSpace`, with interior
`{f < a}` and boundary the level `f⁻¹(a)`. This file shows that `a - f` is a global boundary
defining function of it (`TauCeti.isBoundaryDefiningFunctionOn_scalarRegularSublevel`): its
differential at a boundary point is `-df ∘ dj`, where the differential `dj` of the inclusion is
invertible and `df ≠ 0` by regularity.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Proposition 5.47 (regular sublevel sets are regular domains) and the subsequent
  discussion of boundary defining functions.
-/

public section

open Module Set
open scoped ContDiff Manifold

namespace TauCeti

variable {n : ℕ} {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] {f : M → ℝ} {a : ℝ}

/-- **The function of a regular sublevel is a global boundary defining function.** On the regular
sublevel `{f ≤ a}`, the function `a - f` is smooth, positive on the interior `{f < a}`, zero on the
boundary `f⁻¹(a)` and has nonzero differential there. -/
theorem isBoundaryDefiningFunctionOn_scalarRegularSublevel (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hreg : IsRegularValue I 𝓘(ℝ) f a) (hn : finrank ℝ E = n + 1) :
    letI := scalarRegularSublevelChartedSpace (hf.of_le ENat.LEInfty.out) hreg hn
    IsBoundaryDefiningFunctionOn n (fun x : {x | f x ≤ a} ↦ a - f x) univ := by
  let := scalarRegularSublevelChartedSpace (hf.of_le ENat.LEInfty.out) hreg hn
  have := isManifold_scalarRegularSublevel hreg hn ENat.LEInfty.out hf
  have hj := contMDiff_subtypeVal_scalarRegularSublevel hreg hn ENat.LEInfty.out hf
  have hfj : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ (fun x : {x | f x ≤ a} ↦ f x) := hf.comp hj
  refine ⟨isOpen_univ, (contMDiff_const.sub hfj).contMDiffOn, fun x _ hx ↦ ?_, fun x _ hx ↦ ?_,
    fun x _ hx h0 ↦ ?_⟩
  · rw [interior_scalarRegularSublevel hreg hn ENat.LEInfty.out hf] at hx
    exact sub_pos.2 hx
  · rw [boundary_scalarRegularSublevel hreg hn ENat.LEInfty.out hf] at hx
    exact sub_eq_zero.2 hx.symm
  · rw [boundary_scalarRegularSublevel hreg hn ENat.LEInfty.out hf] at hx
    -- `d(a - f ∘ j) = -df ∘ dj`, so it vanishes only if `df` vanishes on the range of `dj`,
    -- which is everything; but `df ≠ 0` at the regular point `x`.
    obtain ⟨w, hw⟩ := isRegularPoint_iff.1 (isRegularValue_iff.1 hreg (x : M) hx) (1 : ℝ)
    obtain ⟨v, rfl⟩ := (isInvertible_mfderiv_subtypeVal_scalarRegularSublevel
      (hf.of_le ENat.LEInfty.out) hreg hn x).surjective w
    rw [mvfderiv_fun_sub mdifferentiableAt_const (hfj.mdifferentiableAt (by simp)),
      mvfderiv_const, zero_sub, neg_eq_zero] at h0
    have h1 := mvfderiv_comp_apply (g := f) (f := Subtype.val) x (hf.mdifferentiableAt (by simp))
      (hj.mdifferentiableAt (by simp)) v
    rw [Function.comp_def, h0, zero_apply] at h1
    exact one_ne_zero (α := ℝ) (hw.symm.trans h1.symm)

end TauCeti
