/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.GraphFlattening.Direction
public import TauCeti.Analysis.Holder.C2HolderBoundary.Basic
public import TauCeti.Analysis.Sobolev.Wkp.ChangeOfVariables
import TauCeti.Analysis.InnerProductSpace.GraphPatch

/-!
# Flattening charts at the boundary of a domain with `C^{2,α}` boundary

Let `Ω` be a set with `C^{2,α}` boundary (`Set.HasC2HolderBoundary Ω α`) in a finite-dimensional
real inner product space `E`: near each frontier point `z`, in a ball `B(z, r)`, `Ω` is the region
`{x | γ x < ⟪x, ν⟫}` above the graph of a `C^{2,α}` function `γ` over the hyperplane `ν^⊥`. The
shear `Φ = shearAlong γ ν`, `Φ y = y + γ y ν`, flattens this region: it carries the half-space
`{0 < ⟪y, ν⟫}` onto `{γ x < ⟪x, ν⟫}` and the hyperplane `{⟪y, ν⟫ = 0}` onto the graph, and its
inverse is the shear `Ψ = shearAlong (-γ) ν` (`TauCeti.shearAlong_neg_shearAlong`).

This file packages these shears as the charts in which boundary regularity is proved by
flattening the boundary (Gilbarg–Trudinger, Section 6.2; Evans, §6.3.2):

* `TauCeti.Wkp.isChangeOfVariables_shearAlong`: the shear by a `C²` function `γ` invariant along a
  vector `ν` with `‖ν‖ ≤ 1`, whose first two derivatives are bounded by `G` on `U`, is a change of
  variables of order two on `U` (`TauCeti.Wkp.IsChangeOfVariables`) with constant `1 + G` and
  Jacobian determinant one.
* `Set.HasC2HolderBoundary.exists_isChangeOfVariables_halfSpace`: every frontier point `z` of a
  set with `C^{2,α}` boundary lies in an open set `U` with a pair of mutually inverse changes of
  variables of order two `Φ : U' → U`, `Ψ : U → U'`, whose second derivatives are `α`-Hölder, such
  that `Φ` maps the part of `U'` in a half-space `{0 < ⟪y, ν⟫}` onto `Ω ∩ U` and the part of `U'`
  in the hyperplane `{⟪y, ν⟫ = 0}` onto `frontier Ω ∩ U`.

The Hölder continuity of `D²Ψ` is what keeps the coefficients of a divergence-form equation
pulled back along `Φ` in `C^{1,α}`, so that a `C^{2,α}` estimate on the flat side transfers back to
`Ω`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 6.2.
* L. C. Evans, *Partial Differential Equations*, 2nd ed., Appendix C.1 and §6.3.2.
-/

public section

open Metric Set TopologicalSpace
open scoped InnerProductSpace NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

namespace TauCeti.Wkp

/-- **A shear is a change of variables of order two.** Let `γ` be `C²` and invariant along `ν`,
with `‖ν‖ ≤ 1`, and let `Dγ` and `D²γ` be bounded by `G` on an open set `U`. Then the shear
`shearAlong γ ν`, `y ↦ y + γ y ν`, is a change of variables of order two from `U` into every open
set `V` into which it maps `U`, with constant `1 + G` and Jacobian determinant one. -/
theorem isChangeOfVariables_shearAlong {γ : E → ℝ} {ν : E} {G : ℝ≥0} {U V : Opens E}
    (hν : ‖ν‖ ≤ 1) (hγ : ContDiff ℝ 2 γ) (hγν : ∀ x (t : ℝ), γ (x + t • ν) = γ x)
    (hG1 : ∀ x ∈ (U : Set E), ‖fderiv ℝ γ x‖ ≤ G)
    (hG2 : ∀ x ∈ (U : Set E), ‖fderiv ℝ (fderiv ℝ γ) x‖ ≤ G)
    (hUV : MapsTo (shearAlong γ ν) U V) :
    IsChangeOfVariables 2 U V (shearAlong γ ν) (1 + G) 1 where
  contDiffOn := (contDiff_shearAlong hγ).contDiffOn
  differentiableOn := (differentiable_shearAlong (hγ.differentiable (by norm_num))).differentiableOn
  injOn := (injective_shearAlong hγν).injOn
  mapsTo := hUV
  norm_iteratedFDeriv_le i hi hi2 x hx := by
    obtain rfl | rfl : i = 1 ∨ i = 2 := by omega
    · rw [norm_iteratedFDeriv_one]
      exact norm_fderiv_shearAlong_le hν (hγ.differentiable (by norm_num) x) (hG1 x hx)
    · rw [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one]
      exact (norm_fderiv_fderiv_shearAlong_le hν hγ.contDiffAt).trans
        ((hG2 x hx).trans (le_add_of_nonneg_left zero_le_one))
  pos := one_pos
  le_abs_det x _ := (abs_det_fderiv_shearAlong (hγ.differentiable (by norm_num)) hγν x).ge

end TauCeti.Wkp

namespace Set.HasC2HolderBoundary

open TauCeti

variable {Ω : Set E} {α : ℝ≥0}

/-- **Flattening charts at the boundary of a domain with `C^{2,α}` boundary.** Let `Ω` have
`C^{2,α}` boundary and let `z` be a frontier point of `Ω`. Then there are open sets `U ∋ z` and
`U'`, mutually inverse changes of variables of order two `Φ : U' → U` and `Ψ : U → U'` with
Jacobian determinant one and `α`-Hölder second derivatives, and a unit vector `ν`, such that `Φ`
maps the part of `U'` in the half-space `{0 < ⟪y, ν⟫}` onto `Ω ∩ U` and the part of `U'` in the
hyperplane `{⟪y, ν⟫ = 0}` onto `frontier Ω ∩ U`. The charts are the shears by the boundary graph:
`Φ = shearAlong γ ν` and `Ψ = shearAlong (-γ) ν`. -/
theorem exists_isChangeOfVariables_halfSpace (h : Ω.HasC2HolderBoundary α) {z : E}
    (hz : z ∈ frontier Ω) :
    ∃ (U' U : Opens E) (Φ Ψ : E → E) (L : ℝ) (K : ℝ≥0) (ν : E),
      Wkp.IsChangeOfVariables 2 U' U Φ L 1 ∧ Wkp.IsChangeOfVariables 2 U U' Ψ L 1 ∧
      LeftInvOn Ψ Φ U' ∧ RightInvOn Ψ Φ U ∧
      HolderOnWith K α (fderiv ℝ (fderiv ℝ Φ)) U' ∧
      HolderOnWith K α (fderiv ℝ (fderiv ℝ Ψ)) U ∧ ‖ν‖ = 1 ∧
      Φ '' ({y | 0 < ⟪y, ν⟫_ℝ} ∩ U') = Ω ∩ U ∧
      Φ '' ({y | ⟪y, ν⟫_ℝ = 0} ∩ U') = frontier Ω ∩ U ∧ z ∈ U := by
  obtain ⟨ν, γ, G, r, hν, hγ, hγν, hG1, hG2, hGH, hr, hpatch⟩ :=
    hasC2HolderBoundary_iff.1 h z hz
  have hΦΨ : Function.LeftInverse (shearAlong γ ν) (shearAlong (-γ) ν) :=
    shearAlong_shearAlong_neg hγν
  let U : Opens E := ⟨ball z r, isOpen_ball⟩
  let U' : Opens E := ⟨shearAlong γ ν ⁻¹' ball z r,
    isOpen_ball.preimage (contDiff_shearAlong hγ).continuous⟩
  -- The derivatives of `-γ` are those of `γ`, negated.
  have hD1 : fderiv ℝ (-γ) = -fderiv ℝ γ := funext fun _ => fderiv_neg
  have hD2 : fderiv ℝ (fderiv ℝ (-γ)) = -fderiv ℝ (fderiv ℝ γ) := by
    rw [hD1]
    exact funext fun _ => fderiv_neg
  have hU : (U : Set E) = ball z r := rfl
  have hU' : (U' : Set E) = shearAlong γ ν ⁻¹' ball z r := rfl
  -- `Φ` is onto, so it maps the preimage of `S ∩ B(z, r)` onto `S ∩ B(z, r)`.
  have himage (S : Set E) :
      shearAlong γ ν '' (shearAlong γ ν ⁻¹' S ∩ U') = S ∩ ball z r := by
    rw [hU', ← preimage_inter, image_preimage_eq _ hΦΨ.surjective]
  -- The hyperplane `{⟪y, ν⟫ = 0}` is the preimage of the graph of `γ`.
  have hF : {y : E | ⟪y, ν⟫_ℝ = 0} = shearAlong γ ν ⁻¹' {x | ⟪x, ν⟫_ℝ = γ x} := by
    ext y
    rw [mem_preimage, mem_ofPred_eq, mem_ofPred_eq, ← real_inner_shearAlong_sub hν hγν y,
      sub_eq_zero]
  have hν0 : ν ≠ 0 := ne_zero_of_norm_ne_zero (hν ▸ one_ne_zero)
  have hfr := inter_frontier_eq_inter_setOf_inner_eq (Ω := Ω) isOpen_ball hν0
    hγ.continuous.continuousOn hγν (by rw [inter_comm (ball z r) Ω, hpatch, inter_comm])
  refine ⟨U', U, shearAlong γ ν, shearAlong (-γ) ν, 1 + G, G, ν,
    Wkp.isChangeOfVariables_shearAlong hν.le hγ hγν (fun x _ => hG1 x) (fun x _ => hG2 x)
      fun _ hy => hy,
    Wkp.isChangeOfVariables_shearAlong hν.le hγ.neg (neg_apply_add_smul_eq hγν)
      (fun x _ => by simpa [hD1] using hG1 x)
      (fun x _ => by rw [hD2, Pi.neg_apply, ContinuousLinearMap.opNorm_neg]; exact hG2 x)
      fun x hx => mem_preimage.2 ((hΦΨ x).symm ▸ hx),
    fun y _ => shearAlong_neg_shearAlong hγν y, fun x _ => hΦΨ x,
    holderOnWith_fderiv_fderiv_shearAlong hν.le (fun _ _ => hγ.contDiffAt) (hGH.holderOnWith _),
    holderOnWith_fderiv_fderiv_shearAlong hν.le (fun _ _ => hγ.neg.contDiffAt)
      (by rw [hD2]; exact hGH.neg.holderOnWith _), hν, ?_, ?_, mem_ball_self hr⟩
  · rw [← preimage_shearAlong_setOf_lt_inner hν hγν, himage, hU, ← hpatch]
  · rw [hF, himage, hU, inter_comm, ← hfr, inter_comm]

end Set.HasC2HolderBoundary
