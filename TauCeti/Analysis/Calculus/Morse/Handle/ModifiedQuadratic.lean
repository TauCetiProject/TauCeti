/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import TauCeti.Analysis.Calculus.Morse.Handle.Retraction

/-!
# Milnor's modification of the quadratic model at a critical point

Near a nondegenerate critical point a Morse function has the form `f = c - ‖u‖² + ‖v‖²`, with
`u ∈ Eᵤ` the negative and `v ∈ Eₛ` the positive directions. To pass the critical level `c`, Milnor
lowers `f` near the critical point: for a cutoff function `μ` he replaces `f` by
`F = f - μ(‖u‖² + 2‖v‖²)`. Translating the critical value to `0`, this file studies the modified
quadratic model `TauCeti.modifiedQuadratic μ`, given by
`(u, v) ↦ -‖u‖² + ‖v‖² - μ(‖u‖² + 2‖v‖²)`.

The cutoff `μ` satisfies Milnor's conditions `TauCeti.IsHandleCutoff ε μ`: it is smooth,
`μ 0 > ε`, `μ r = 0` for `r ≥ 2ε`, and `-1 < μ' ≤ 0`. Such cutoffs exist for every `ε > 0`
(`TauCeti.exists_isHandleCutoff`). For such a cutoff:

* the modification lowers the quadratic model, and only on the ellipsoid
  `‖u‖² + 2‖v‖² < 2ε` (`TauCeti.modifiedQuadratic_le`, `TauCeti.modifiedQuadratic_eq_of_le`);
* it does not change the sublevels at levels `a ≥ ε`
  (`TauCeti.modifiedQuadratic_le_iff`), so on a manifold `{F ≤ c + ε} = {f ≤ c + ε}`;
* its only critical point is the origin (`TauCeti.fderiv_modifiedQuadratic_eq_zero_iff`), where
  its value is `-μ 0 < -ε`, so it has no critical point at levels `≥ -ε`
  (`TauCeti.fderiv_modifiedQuadratic_ne_zero`);
* its sublevel `{F ≤ -ε}` contains the lower quadratic sublevel `{-‖u‖² + ‖v‖² ≤ -ε}` together
  with the cell `{‖u‖² ≤ ε, v = 0}`, and deformation retracts onto this union
  (`TauCeti.exists_modifiedQuadratic_sublevel_deformation`), because `F` does not decrease as `v`
  is scaled up.

These are local facts about the model. In Milnor's argument on a manifold, one additionally
assumes that `f⁻¹[c - ε, c + ε]` is compact and contains no critical point other than the given
one, that the Morse chart contains the ellipsoid `‖u‖² + 2‖v‖² ≤ 2ε`, and that `F` is the global
function equal to `f - μ(‖u‖² + 2‖v‖²)` in the chart and to `f` elsewhere. Under those
hypotheses the first three facts make the band `F⁻¹[c - ε, c + ε]` free of critical points, so
that the gradient flow deformation retracts `{f ≤ c + ε}` onto `{F ≤ c - ε}`; the last one
retracts `{F ≤ c - ε}` onto `{f ≤ c - ε}` with a `λ`-cell attached. None of these manifold-level
consequences are proved in this file.

## Main declarations

* `TauCeti.IsHandleCutoff`: Milnor's conditions on the cutoff, with
  `TauCeti.exists_isHandleCutoff`.
* `TauCeti.modifiedQuadratic`: the modified quadratic model.
* `TauCeti.modifiedQuadratic_le_iff`: the modification does not change sublevels above `ε`.
* `TauCeti.hasFDerivAt_modifiedQuadratic` and `TauCeti.fderiv_modifiedQuadratic_eq_zero_iff`: the
  derivative, which vanishes only at the origin.
* `TauCeti.exists_modifiedQuadratic_sublevel_deformation`: the strong deformation retraction of
  `{F ≤ -ε}` onto `TauCeti.quadraticSublevelUnionCell ε`.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  proof of Theorem 3.2.
-/

public section

open Set
open scoped ContDiff

noncomputable section

namespace TauCeti

/-! ### Cutoff functions -/

/-- **Milnor's cutoff conditions** at level `ε`: `μ` is smooth, `μ 0 > ε`, `μ r = 0` for
`r ≥ 2ε`, and `-1 < μ' r ≤ 0` for all `r`. These are the conditions under which
`TauCeti.modifiedQuadratic μ` has the origin as its only critical point and agrees with the
quadratic model outside the ellipsoid `‖u‖² + 2‖v‖² < 2ε`. -/
structure IsHandleCutoff (ε : ℝ) (μ : ℝ → ℝ) : Prop where
  contDiff : ContDiff ℝ ∞ μ
  lt_apply_zero : ε < μ 0
  apply_eq_zero : ∀ ⦃r⦄, 2 * ε ≤ r → μ r = 0
  neg_one_lt_deriv : ∀ r, -1 < deriv μ r
  deriv_nonpos : ∀ r, deriv μ r ≤ 0

namespace IsHandleCutoff

variable {ε : ℝ} {μ : ℝ → ℝ}

/-- A cutoff function is differentiable. -/
theorem differentiable (hμ : IsHandleCutoff ε μ) : Differentiable ℝ μ :=
  hμ.contDiff.differentiable (by simp)

/-- A cutoff function is antitone, since `μ' ≤ 0`. -/
theorem antitone (hμ : IsHandleCutoff ε μ) : Antitone μ :=
  antitone_of_deriv_nonpos hμ.differentiable hμ.deriv_nonpos

/-- A cutoff function is nonnegative: it decreases to `0`. -/
theorem nonneg (hμ : IsHandleCutoff ε μ) (r : ℝ) : 0 ≤ μ r := by
  rw [← hμ.apply_eq_zero (le_max_right r (2 * ε))]
  exact hμ.antitone (le_max_left _ _)

/-- Since `μ' > -1`, the function `r ↦ r + μ r` is monotone. -/
theorem monotone_add (hμ : IsHandleCutoff ε μ) : Monotone fun r ↦ r + μ r :=
  have h (r : ℝ) : HasDerivAt (fun r ↦ r + μ r) (1 + deriv μ r) r :=
    (hasDerivAt_id' r).add (hμ.differentiable r).hasDerivAt
  monotone_of_deriv_nonneg (fun r ↦ (h r).differentiableAt) fun r ↦ by
    rw [(h r).deriv]
    linarith [hμ.neg_one_lt_deriv r]

end IsHandleCutoff

/-- Milnor's cutoff functions exist at every positive level `ε`. One is
`r ↦ ∫ t in r..2ε, ρ t`, where `ρ` is a smooth function with values in `[0, 7/8]` which equals
`7/8` up to `7ε/4` and vanishes from `2ε` on. -/
theorem exists_isHandleCutoff {ε : ℝ} (hε : 0 < ε) : ∃ μ, IsHandleCutoff ε μ := by
  set ρ : ℝ → ℝ := fun t ↦ 7 / 8 * Real.smoothTransition (8 - 4 * t / ε) with hρ
  have hρc : ContDiff ℝ ∞ ρ :=
    contDiff_const.mul (Real.smoothTransition.contDiff.comp (by fun_prop))
  have hρ₀ (t : ℝ) : 0 ≤ ρ t := mul_nonneg (by norm_num) (Real.smoothTransition.nonneg _)
  have hρ₁ (t : ℝ) : ρ t ≤ 7 / 8 := by
    have := Real.smoothTransition.le_one (8 - 4 * t / ε)
    simp only [hρ]
    linarith
  have hderiv (r : ℝ) : HasDerivAt (fun r ↦ ∫ t in r..2 * ε, ρ t) (-ρ r) r :=
    intervalIntegral.integral_hasDerivAt_left (hρc.continuous.intervalIntegrable _ _)
      (hρc.continuous.stronglyMeasurableAtFilter _ _) hρc.continuous.continuousAt
  have hd : deriv (fun r ↦ ∫ t in r..2 * ε, ρ t) = fun r ↦ -ρ r :=
    funext fun r ↦ (hderiv r).deriv
  refine ⟨fun r ↦ ∫ t in r..2 * ε, ρ t, ⟨?_, ?_, fun r hr ↦ ?_, fun r ↦ ?_, fun r ↦ ?_⟩⟩
  · exact contDiff_infty_iff_deriv.2 ⟨fun r ↦ (hderiv r).differentiableAt, hd ▸ hρc.neg⟩
  · have h₁ : ∫ t in (0 : ℝ)..7 * ε / 4, ρ t = ∫ _ in (0 : ℝ)..7 * ε / 4, (7 / 8 : ℝ) := by
      refine intervalIntegral.integral_congr fun t ht ↦ ?_
      rw [uIcc_of_le (by positivity)] at ht
      have : 4 * t / ε ≤ 7 := by
        rw [div_le_iff₀ hε]
        linarith [ht.2]
      simp only [hρ]
      rw [Real.smoothTransition.one_of_one_le (by linarith), mul_one]
    have h₂ : 0 ≤ ∫ t in 7 * ε / 4..2 * ε, ρ t :=
      intervalIntegral.integral_nonneg (by linarith) fun t _ ↦ hρ₀ t
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := 7 * ε / 4)
      (hρc.continuous.intervalIntegrable _ _) (hρc.continuous.intervalIntegrable _ _), h₁,
      intervalIntegral.integral_const, smul_eq_mul]
    linarith
  · refine (intervalIntegral.integral_congr (g := fun _ ↦ (0 : ℝ)) fun t ht ↦ ?_).trans
      intervalIntegral.integral_zero
    rw [uIcc_of_ge hr] at ht
    have : 8 ≤ 4 * t / ε := by
      rw [le_div_iff₀ hε]
      linarith [ht.1]
    simp only [hρ]
    rw [Real.smoothTransition.zero_of_nonpos (by linarith), mul_zero]
  · rw [hd]
    linarith [hρ₁ r]
  · rw [hd]
    linarith [hρ₀ r]

/-! ### The modified quadratic model -/

variable {Eᵤ Eₛ : Type*} [NormedAddCommGroup Eᵤ] [NormedAddCommGroup Eₛ] {ε a : ℝ}
  {μ : ℝ → ℝ} {z : Eᵤ × Eₛ}

/-- **Milnor's modification** `(u, v) ↦ -‖u‖² + ‖v‖² - μ(‖u‖² + 2‖v‖²)` of the quadratic model
`-‖u‖² + ‖v‖²` of a Morse function at a critical point with critical value `0`. -/
def modifiedQuadratic (μ : ℝ → ℝ) (z : Eᵤ × Eₛ) : ℝ :=
  -‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 - μ (‖z.1‖ ^ 2 + 2 * ‖z.2‖ ^ 2)

theorem modifiedQuadratic_def (μ : ℝ → ℝ) :
    modifiedQuadratic (Eᵤ := Eᵤ) (Eₛ := Eₛ) μ =
      fun z ↦ -‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 - μ (‖z.1‖ ^ 2 + 2 * ‖z.2‖ ^ 2) :=
  (rfl)

@[simp]
theorem modifiedQuadratic_apply (μ : ℝ → ℝ) (z : Eᵤ × Eₛ) :
    modifiedQuadratic μ z = -‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 - μ (‖z.1‖ ^ 2 + 2 * ‖z.2‖ ^ 2) :=
  (rfl)

/-- The modification lowers the quadratic model. -/
theorem modifiedQuadratic_le (hμ : IsHandleCutoff ε μ) (z : Eᵤ × Eₛ) :
    modifiedQuadratic μ z ≤ -‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 := by
  rw [modifiedQuadratic_apply]
  linarith [hμ.nonneg (‖z.1‖ ^ 2 + 2 * ‖z.2‖ ^ 2)]

/-- Outside the ellipsoid `‖u‖² + 2‖v‖² < 2ε`, the modification is the quadratic model. -/
theorem modifiedQuadratic_eq_of_le (hμ : IsHandleCutoff ε μ)
    (hz : 2 * ε ≤ ‖z.1‖ ^ 2 + 2 * ‖z.2‖ ^ 2) :
    modifiedQuadratic μ z = -‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 := by
  rw [modifiedQuadratic_apply, hμ.apply_eq_zero hz, sub_zero]

/-- The modification has the same sublevels as the quadratic model at every level `a ≥ ε`:
the quadratic model is at most `ε` on the ellipsoid where the two differ. -/
theorem modifiedQuadratic_le_iff (hμ : IsHandleCutoff ε μ) (ha : ε ≤ a) :
    modifiedQuadratic μ z ≤ a ↔ -‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 ≤ a := by
  refine ⟨fun h ↦ ?_, (modifiedQuadratic_le hμ z).trans⟩
  rcases le_or_gt (2 * ε) (‖z.1‖ ^ 2 + 2 * ‖z.2‖ ^ 2) with hz | hz
  · rwa [← modifiedQuadratic_eq_of_le hμ hz]
  · linarith [sq_nonneg ‖z.1‖]

/-- At the critical point the modification takes the value `-μ 0`. -/
theorem modifiedQuadratic_zero (μ : ℝ → ℝ) : modifiedQuadratic μ (0 : Eᵤ × Eₛ) = -μ 0 := by
  simp

/-- On the negative directions `v = 0`, the modification stays below `-ε`. -/
theorem modifiedQuadratic_mk_zero_lt (hμ : IsHandleCutoff ε μ) (u : Eᵤ) :
    modifiedQuadratic μ (u, (0 : Eₛ)) < -ε := by
  have := hμ.monotone_add (sq_nonneg ‖u‖)
  simp only [zero_add] at this
  simp only [modifiedQuadratic_apply, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, mul_zero, add_zero]
  linarith [hμ.lt_apply_zero]

/-- The modification does not decrease when the positive component grows in norm. -/
theorem modifiedQuadratic_mk_le_of_norm_le (hμ : IsHandleCutoff ε μ) (u : Eᵤ) {v w : Eₛ}
    (h : ‖v‖ ≤ ‖w‖) : modifiedQuadratic μ (u, v) ≤ modifiedQuadratic μ (u, w) := by
  have hsq : ‖v‖ ^ 2 ≤ ‖w‖ ^ 2 := by gcongr
  have := hμ.antitone (by linarith : ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 ≤ ‖u‖ ^ 2 + 2 * ‖w‖ ^ 2)
  simp only [modifiedQuadratic_apply]
  linarith

/-- The lower quadratic sublevel with the cell attached lies in the sublevel `{F ≤ -ε}` of the
modification. -/
theorem quadraticSublevelUnionCell_subset_setOf_modifiedQuadratic_le (hμ : IsHandleCutoff ε μ) :
    quadraticSublevelUnionCell ε ⊆ {z : Eᵤ × Eₛ | modifiedQuadratic μ z ≤ -ε} := by
  intro z hz
  rcases mem_quadraticSublevelUnionCell.1 hz with h | ⟨-, h⟩
  · exact (modifiedQuadratic_le hμ z).trans h
  · have := (modifiedQuadratic_mk_zero_lt (Eₛ := Eₛ) hμ z.1).le
    rwa [← h, Prod.mk.eta] at this

section NormedSpace

variable [NormedSpace ℝ Eₛ]

/-- The fibres `{v | F (u, v) ≤ a}` of the sublevels of the modification are star-shaped about
the origin. -/
theorem starConvex_modifiedQuadratic_le (hμ : IsHandleCutoff ε μ) (u : Eᵤ) (a : ℝ) :
    StarConvex ℝ 0 {v : Eₛ | modifiedQuadratic μ (u, v) ≤ a} := by
  refine starConvex_zero_iff.2 fun v hv t ht₀ ht₁ ↦ ?_
  refine (modifiedQuadratic_mk_le_of_norm_le hμ u ?_).trans hv
  rw [norm_smul, Real.norm_of_nonneg ht₀]
  exact mul_le_of_le_one_left (norm_nonneg _) ht₁

/-- **Milnor's handle retraction for the modified function.** The lower quadratic sublevel with
the cell attached, `TauCeti.quadraticSublevelUnionCell ε`, is a strong deformation retract of the
sublevel `{F ≤ -ε}` of the modification: there is a retraction onto it, and a homotopy in
`{F ≤ -ε}` from this retraction to the identity which fixes `TauCeti.quadraticSublevelUnionCell ε`.
Both are restrictions of `TauCeti.quadraticHandleRetraction ε` and
`TauCeti.quadraticHandleDeformation ε`. -/
theorem exists_modifiedQuadratic_sublevel_deformation (hμ : IsHandleCutoff ε μ) :
    ∃ r : C({z : Eᵤ × Eₛ | modifiedQuadratic μ z ≤ -ε}, quadraticSublevelUnionCell ε),
      (∀ x, r (ContinuousMap.inclusion
        (quadraticSublevelUnionCell_subset_setOf_modifiedQuadratic_le hμ) x) = x) ∧
      Nonempty (((ContinuousMap.inclusion
          (quadraticSublevelUnionCell_subset_setOf_modifiedQuadratic_le hμ)).comp r).HomotopyRel
        (ContinuousMap.id _) {x | (x : Eᵤ × Eₛ) ∈ quadraticSublevelUnionCell ε}) := by
  have hsub : quadraticSublevelUnionCell (Eᵤ := Eᵤ) (Eₛ := Eₛ) ε ⊆ _ :=
    quadraticSublevelUnionCell_subset_setOf_modifiedQuadratic_le hμ
  obtain ⟨r, hr, ⟨H⟩⟩ := exists_inter_quadraticSublevelUnionCell_deformation
    (X := {z : Eᵤ × Eₛ | modifiedQuadratic μ z ≤ -ε})
    (fun u ↦ starConvex_modifiedQuadratic_le hμ u (-ε)) ε
  refine ⟨(ContinuousMap.inclusion inter_subset_right).comp r, fun x ↦ ?_, ⟨H.cast ?_ rfl⟩⟩
  · -- The inclusions of `x` and of `⟨x, hsub x.2, x.2⟩` into the sublevel agree by proof
    -- irrelevance, and `ContinuousMap.inclusion` does not change underlying points.
    have h := congrArg Subtype.val (hr ⟨x, hsub x.2, x.2⟩)
    exact Subtype.ext h
  · ext x <;> simp

end NormedSpace

/-! ### The derivative -/

section InnerProductSpace

variable [InnerProductSpace ℝ Eᵤ] [InnerProductSpace ℝ Eₛ]

/-- The modified quadratic model is `Cⁿ` whenever the cutoff `μ` is `Cⁿ`. -/
theorem contDiff_modifiedQuadratic {n : WithTop ℕ∞} (hμ : ContDiff ℝ n μ) :
    ContDiff ℝ n (modifiedQuadratic (Eᵤ := Eᵤ) (Eₛ := Eₛ) μ) := by
  have h₁ : ContDiff ℝ n fun z : Eᵤ × Eₛ ↦ ‖z.1‖ ^ 2 := contDiff_norm_sq ℝ |>.comp contDiff_fst
  have h₂ : ContDiff ℝ n fun z : Eᵤ × Eₛ ↦ ‖z.2‖ ^ 2 := contDiff_norm_sq ℝ |>.comp contDiff_snd
  rw [modifiedQuadratic_def]
  exact (h₁.neg.add h₂).sub (hμ.comp (h₁.add (contDiff_const.mul h₂)))

/-- The derivative of the modification at `z = (u, v)` is
`h ↦ -2 (1 + μ' r) ⟪u, h.1⟫ + 2 (1 - 2 μ' r) ⟪v, h.2⟫`, where `r = ‖u‖² + 2‖v‖²`. -/
theorem hasFDerivAt_modifiedQuadratic
    (hμ : DifferentiableAt ℝ μ (‖z.1‖ ^ 2 + 2 * ‖z.2‖ ^ 2)) :
    HasFDerivAt (modifiedQuadratic μ)
      ((-2 * (1 + deriv μ (‖z.1‖ ^ 2 + 2 * ‖z.2‖ ^ 2))) •
          (innerSL ℝ z.1).comp (ContinuousLinearMap.fst ℝ Eᵤ Eₛ) +
        (2 * (1 - 2 * deriv μ (‖z.1‖ ^ 2 + 2 * ‖z.2‖ ^ 2))) •
          (innerSL ℝ z.2).comp (ContinuousLinearMap.snd ℝ Eᵤ Eₛ)) z := by
  have h₁ := (hasFDerivAt_fst (p := z) (𝕜 := ℝ)).norm_sq
  have h₂ := (hasFDerivAt_snd (p := z) (𝕜 := ℝ)).norm_sq
  have h₃ := hμ.hasDerivAt.comp_hasFDerivAt z (h₁.add (h₂.const_mul 2))
  rw [modifiedQuadratic_def]
  refine ((h₁.neg.add h₂).sub h₃).congr_fderiv ?_
  ext v <;> simp <;> ring

/-- **The only critical point of the modification is the origin.** -/
theorem fderiv_modifiedQuadratic_eq_zero_iff (hμ : IsHandleCutoff ε μ) :
    fderiv ℝ (modifiedQuadratic μ) z = 0 ↔ z = 0 := by
  rw [(hasFDerivAt_modifiedQuadratic (hμ.differentiable _)).fderiv]
  have h₁ := hμ.neg_one_lt_deriv (‖z.1‖ ^ 2 + 2 * ‖z.2‖ ^ 2)
  have h₂ := hμ.deriv_nonpos (‖z.1‖ ^ 2 + 2 * ‖z.2‖ ^ 2)
  refine ⟨fun h ↦ ?_, fun h ↦ by subst h; simp⟩
  have hu := congr($h (z.1, 0))
  have hv := congr($h (0, z.2))
  simp at hu hv
  exact Prod.ext (hu.resolve_left (by linarith)) (hv.resolve_left (by linarith))

/-- The modification has no critical point at levels `≥ -ε`. -/
theorem fderiv_modifiedQuadratic_ne_zero (hμ : IsHandleCutoff ε μ)
    (hz : -ε ≤ modifiedQuadratic μ z) : fderiv ℝ (modifiedQuadratic μ) z ≠ 0 := by
  rw [ne_eq, fderiv_modifiedQuadratic_eq_zero_iff hμ]
  rintro rfl
  have : modifiedQuadratic μ (0 : Eᵤ × Eₛ) < -ε := by
    simpa using modifiedQuadratic_mk_zero_lt (Eₛ := Eₛ) hμ (0 : Eᵤ)
  linarith

end InnerProductSpace

end TauCeti
