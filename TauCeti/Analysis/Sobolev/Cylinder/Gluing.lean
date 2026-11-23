/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Gluing.Coefficient
public import TauCeti.Analysis.Sobolev.Cylinder.Parametrix
public import TauCeti.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.Analysis.Normed.Operator.Surjective
import TauCeti.MeasureTheory.Function.Lp.Multiplication

/-!
# Gluing first-order operators on the cylinder along a long neck

Let `D₁` and `D₂` be first-order operators `D ξ = M (ξ, ∂s ξ, ∂t ξ)` on the cylinder `ℝ × S¹`,
realized from `W^{1,2}(ℝ × S¹, V)` to `L²(ℝ × S¹, W)` by `TauCeti.jetOperator stripMeasure`, with
essentially bounded coefficient fields `M₁` and `M₂` whose ends match: `M₁(s, t) → M(t)` as
`s → +∞` and `M₂(s, t) → M(t)` as `s → -∞`, uniformly in `t`. Gluing the positive end of `M₁` to
the negative end of `M₂` along a neck of length `2 R` gives the coefficient field

`M_R(s, t) = M₁(s + R, t)` for `s < 0`, and `M_R(s, t) = M₂(s - R, t)` for `s ≥ 0`,

which is `Function.uncurry (TauCeti.gluedCoeff (Function.curry M₁) (Function.curry M₂) R)`.

The main theorem
(`TauCeti.CylinderSobolev.exists_forall_ge_exists_rightInverse_jetOperator_gluedCoeff`) is the
linear gluing estimate for surjective pieces: if `D₁` and `D₂` have bounded linear right inverses
`Q₁` and `Q₂` on `W^{1,2}`, then for every sufficiently long neck the glued operator `D_R` has a
bounded linear right inverse of norm at most `4 (‖Q₁‖ + ‖Q₂‖)`, independently of `R`. Nothing is
assumed about the common limit `M`, nor about the principal parts, beyond the matching of the ends.

Written in a trivialization along a broken Floer trajectory, the linearized Floer operators
`∂s + J ∂t + S` along its two cylinders, the first ending and the second starting at the same
nondegenerate orbit, are operators of this form. When they are onto, as for regular trajectories,
the theorem gives uniformly bounded right inverses for the operators of the glued coefficient field.
The linearization along the pre-glued cylinder differs from these by an error that is small in
`L^∞` for long necks. Absorbing it gives the uniformly bounded right inverses that are the linear
input of the Newton iteration gluing broken Floer trajectories: if `S` is that linearization and
`Q` the right inverse given here for the glued operator `T`, then
`‖S Q - id‖ = ‖(S - T) Q‖ ≤ ‖S - T‖ ‖Q‖ ≤ 1 / 2` once the error is small, and
`ContinuousLinearMap.exists_rightInverse_of_norm_comp_sub_id_le_half` turns `Q` into a right
inverse of `S` of norm at most `2 ‖Q‖`.

* **Translation.** Translation in `s` commutes with first-order operators, the coefficient field
  being translated too (`TauCeti.CylinderSobolev.translateLp_jetOperator`), so a right inverse of
  `D_M` translates to a right inverse of the operator of the translated coefficient field, of the
  same norm (`TauCeti.CylinderSobolev.exists_rightInverse_jetOperator_comp_add`).
* **Splicing.** Cut `η ∈ L²` into its parts `η₁` and `η₂` on `s < 0` and `s ≥ 0`, solve
  `D₁ ξ₁ = η₁(· - R)` and `D₂ ξ₂ = η₂(· + R)`, translate the solutions back to the two ends of the
  neck and multiply them by the cutoffs `β₁ = TauCeti.neckCutoff (-(2 / R))` and
  `β₂ = TauCeti.neckCutoff (2 / R)`, equal to `1` on the two half-lines and vanishing beyond
  `± R / 2` (`TauCeti.CylinderSobolev.cutoffL`). For the spliced inverse
  `Q₀ η = β₁ ξ₁(· + R) + β₂ ξ₂(· - R)`, the error `D_R Q₀ η - η` is the sum over the two pieces of
  `βᵢ (M_R - Mᵢ(· ± R)) ξᵢ + βᵢ' M_R (0, ξᵢ, 0)`. The second term is small because
  `|βᵢ'| = O(1 / R)`, the first because on the support of `βᵢ` the coefficient `M_R` and the
  translate of `Mᵢ` differ only where both are close to `M`. So `D_R Q₀` is within `1 / 2` of the
  identity for large `R`, and its Neumann series corrects `Q₀` to an exact right inverse
  (`ContinuousLinearMap.exists_rightInverse_of_norm_comp_sub_id_lt`).

This is the cylinder version of
`TauCeti.WeakDerivStep.exists_forall_ge_exists_rightInverse_trajectoryOperator_gluedCoeff`, which
glues trajectory operators on the line, and it uses the same glued coefficient and cutoffs.

## References

* A. Floer, *The unregularized gradient flow of the symplectic action*, Comm. Pure Appl. Math. 41
  (1988), 775–813, on the gluing of Floer trajectories.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 3, on gluing and the uniformly bounded right inverses of the glued
  linearized operators.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Chapter 10
  (gluing: pregluing, uniformly bounded right inverses and Newton iteration).
-/

public section

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal

namespace TauCeti.CylinderSobolev

open StripSobolev

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-! ### The error of one spliced piece -/

/-- **The error of one piece.** Let `x ∈ W^{1,2}` solve `D_N x = 𝟙_S η` for a coefficient field
`N`, and let `β` be a cutoff equal to `1` on `S`. If `‖G‖ ≤ B` and `|β'| ≤ d`, and `G` is within `ε`
of `N` wherever `β ≠ 0`, then `D_G (β x)` is within `(ε + d B) ‖x‖` of `𝟙_S η`. -/
private theorem norm_jetOperator_cutoffL_sub_le {G N : ℝ × ℝ → V × V × V →L[ℝ] W}
    (hG : MemLp G ∞ stripMeasure) (hN : MemLp N ∞ stripMeasure) {β : ℝ → ℝ}
    (hβ : ContDiff ℝ 2 β) (hβ1 : ∀ s, |β s| ≤ 1) (hβ'1 : ∀ s, |deriv β s| ≤ 1)
    {S : Set (ℝ × ℝ)} (hS : MeasurableSet S) (hβS : ∀ z ∈ S, β z.1 = 1) {B d ε : ℝ}
    (hB : ∀ᵐ z ∂stripMeasure, ‖G z‖ ≤ B) (hd : ∀ s, |deriv β s| ≤ d) (hε : 0 ≤ ε)
    (hGN : ∀ᵐ z ∂stripMeasure, β z.1 ≠ 0 → ‖G z - N z‖ ≤ ε) {η : Lp W 2 stripMeasure}
    {x : H1 V} (hx : jetOperator stripMeasure N (x : Lp (V × V × V) 2 stripMeasure) =
      Lp.multiplicationOperator (linftyIndicator stripMeasure S hS) η) :
    ‖jetOperator stripMeasure G (cutoffL hβ hβ1 hβ'1 x : Lp (V × V × V) 2 stripMeasure) -
        Lp.multiplicationOperator (linftyIndicator stripMeasure S hS) η‖ ≤ (ε + d * B) * ‖x‖ := by
  rw [← Submodule.norm_coe x]
  refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
  have hx' := coeFn_jetOperator hN (x : Lp (V × V × V) 2 stripMeasure)
  rw [hx] at hx'
  filter_upwards [Lp.coeFn_sub (jetOperator stripMeasure G
      (cutoffL hβ hβ1 hβ'1 x : Lp (V × V × V) 2 stripMeasure))
      (Lp.multiplicationOperator (linftyIndicator stripMeasure S hS) η),
    coeFn_jetOperator hG (cutoffL hβ hβ1 hβ'1 x : Lp (V × V × V) 2 stripMeasure),
    coeFn_jetOperator (memLp_cutoffCoeff (hβ.of_le one_le_two) hβ1 hβ'1)
      (x : Lp (V × V × V) 2 stripMeasure),
    Lp.multiplicationOperator_linftyIndicator_ae hS η, hx', hB, hGN] with z h₁ h₂ h₃ h₄ h₅ h₆ h₇
  set v := (x : Lp (V × V × V) 2 stripMeasure) z
  -- `𝟙_S η = β 𝟙_S η`, since `β = 1` on `S`.
  have hβη : S.indicator η z = β z.1 • N z v := by
    rw [← h₅, h₄]
    by_cases hz : z ∈ S
    · rw [hβS z hz, one_smul]
    · rw [indicator_of_notMem hz, smul_zero]
  have hd0 : 0 ≤ d := (abs_nonneg _).trans (hd 0)
  have hsv : ‖sSlot V v‖ ≤ ‖v‖ := by simp [Prod.norm_def]
  have key : G z (cutoffCoeff V β z v) - β z.1 • N z v =
      β z.1 • (G z - N z) v + deriv β z.1 • G z (sSlot V v) := by
    simp only [cutoffCoeff_def, add_apply, smul_apply,
      ContinuousLinearMap.id_apply, map_add, map_smul, sub_apply, smul_sub]
    abel
  rw [h₁, Pi.sub_apply, h₂, coe_cutoffL, h₃, h₄, hβη, key]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, add_mul]
  refine add_le_add ?_ ?_
  · by_cases hβ0 : β z.1 = 0
    · rw [hβ0, abs_zero, zero_mul]
      positivity
    · calc |β z.1| * ‖(G z - N z) v‖ ≤ 1 * (ε * ‖v‖) :=
            mul_le_mul (hβ1 _) (((G z - N z).le_opNorm v).trans
              (mul_le_mul_of_nonneg_right (h₇ hβ0) (norm_nonneg v))) (norm_nonneg _) zero_le_one
        _ = ε * ‖v‖ := one_mul _
  · calc |deriv β z.1| * ‖G z (sSlot V v)‖ ≤ d * (B * ‖v‖) :=
          mul_le_mul (hd _) (((G z).le_opNorm _).trans (mul_le_mul h₆ hsv (norm_nonneg _)
            ((norm_nonneg _).trans h₆))) (norm_nonneg _) hd0
      _ = d * B * ‖v‖ := by ring

/-- The error of one piece of the spliced inverse: with `Q` a right inverse of `D_N`, the piece
`β Q (𝟙_S η)` satisfies `‖D_G (β Q (𝟙_S η)) - 𝟙_S η‖ ≤ (ε + d B) ‖Q‖ ‖η‖` under the hypotheses of
`norm_jetOperator_cutoffL_sub_le`. -/
private theorem norm_jetOperator_cutoffL_apply_sub_le {G N : ℝ × ℝ → V × V × V →L[ℝ] W}
    (hG : MemLp G ∞ stripMeasure) (hN : MemLp N ∞ stripMeasure) {β : ℝ → ℝ}
    (hβ : ContDiff ℝ 2 β) (hβ1 : ∀ s, |β s| ≤ 1) (hβ'1 : ∀ s, |deriv β s| ≤ 1)
    {S : Set (ℝ × ℝ)} (hS : MeasurableSet S) (hβS : ∀ z ∈ S, β z.1 = 1) {B d ε : ℝ}
    (hB : ∀ᵐ z ∂stripMeasure, ‖G z‖ ≤ B) (hB0 : 0 ≤ B) (hd : ∀ s, |deriv β s| ≤ d) (hε : 0 ≤ ε)
    (hGN : ∀ᵐ z ∂stripMeasure, β z.1 ≠ 0 → ‖G z - N z‖ ≤ ε)
    {Q : Lp W 2 stripMeasure →L[ℝ] H1 V}
    (hQ : ((jetOperator stripMeasure N).comp (H1 V).subtypeL).comp Q =
      ContinuousLinearMap.id ℝ _) (η : Lp W 2 stripMeasure) :
    ‖jetOperator stripMeasure G (cutoffL hβ hβ1 hβ'1
          (Q (Lp.multiplicationOperator (linftyIndicator stripMeasure S hS) η)) :
          Lp (V × V × V) 2 stripMeasure) -
        Lp.multiplicationOperator (linftyIndicator stripMeasure S hS) η‖ ≤
      (ε + d * B) * (‖Q‖ * ‖η‖) := by
  have hx := congrArg (fun T ↦ T (Lp.multiplicationOperator (linftyIndicator stripMeasure S hS) η))
    hQ
  simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
    ContinuousLinearMap.id_apply] at hx
  have hδ : 0 ≤ ε + d * B := add_nonneg hε (mul_nonneg ((abs_nonneg _).trans (hd 0)) hB0)
  refine (norm_jetOperator_cutoffL_sub_le hG hN hβ hβ1 hβ'1 hS hβS hB hd hε hGN hx).trans
    (mul_le_mul_of_nonneg_left ((Q.le_opNorm _).trans (mul_le_mul_of_nonneg_left
      (Lp.norm_multiplicationOperator_linftyIndicator_apply_le hS η) (norm_nonneg _))) hδ)

/-! ### The glued coefficient field -/

/-- On `s < 0` the glued coefficient field is `M₁` translated by `R`. -/
theorem uncurry_gluedCoeff_of_neg (M₁ M₂ : ℝ × ℝ → V × V × V →L[ℝ] W) (R : ℝ)
    {z : ℝ × ℝ} (hz : z.1 < 0) :
    Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R) z =
      M₁ (z + (R, 0)) := by
  rw [Function.uncurry_apply_pair, gluedCoeff_of_neg _ _ _ hz]
  congr 1
  simp

/-- On `s ≥ 0` the glued coefficient field is `M₂` translated by `-R`. -/
theorem uncurry_gluedCoeff_of_nonneg (M₁ M₂ : ℝ × ℝ → V × V × V →L[ℝ] W) (R : ℝ)
    {z : ℝ × ℝ} (hz : 0 ≤ z.1) :
    Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R) z =
      M₂ (z + (-R, 0)) := by
  rw [Function.uncurry_apply_pair, gluedCoeff_of_nonneg _ _ _ hz]
  congr 1
  simp

/-- The glued coefficient field is essentially bounded, by the sum of the bounds of the pieces. -/
theorem memLp_uncurry_gluedCoeff {M₁ M₂ : ℝ × ℝ → V × V × V →L[ℝ] W}
    (hM₁ : MemLp M₁ ∞ stripMeasure) (hM₂ : MemLp M₂ ∞ stripMeasure) (R : ℝ) :
    MemLp (Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R)) ∞
        stripMeasure ∧
      ∀ᵐ z ∂stripMeasure,
        ‖Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R) z‖ ≤
          lpNorm M₁ ∞ stripMeasure + lpNorm M₂ ∞ stripMeasure := by
  set S : Set (ℝ × ℝ) := {z | z.1 < 0}
  have hS : MeasurableSet S := measurableSet_lt measurable_fst measurable_const
  have heq : Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R) =
      S.indicator (fun z ↦ M₁ (z + (R, 0))) + Sᶜ.indicator (fun z ↦ M₂ (z + (-R, 0))) := by
    funext z
    by_cases hz : z.1 < 0
    · simp [S, hz, uncurry_gluedCoeff_of_neg M₁ M₂ R hz]
    · simp [S, hz, uncurry_gluedCoeff_of_nonneg M₁ M₂ R (not_lt.1 hz)]
  have hN₁ := hM₁.comp_measurePreserving (measurePreserving_add_strip R)
  have hN₂ := hM₂.comp_measurePreserving (measurePreserving_add_strip (-R))
  refine ⟨heq ▸ (hN₁.indicator hS.nullMeasurableSet).add
    (hN₂.indicator hS.compl.nullMeasurableSet), ?_⟩
  filter_upwards [(measurePreserving_add_strip R).quasiMeasurePreserving.ae
      (ae_le_lpNorm_exponent_top hM₁),
    (measurePreserving_add_strip (-R)).quasiMeasurePreserving.ae
      (ae_le_lpNorm_exponent_top hM₂)] with z h₁ h₂
  have h₁0 : 0 ≤ lpNorm M₁ ∞ stripMeasure := lpNorm_nonneg
  have h₂0 : 0 ≤ lpNorm M₂ ∞ stripMeasure := lpNorm_nonneg
  by_cases hz : z.1 < 0
  · rw [uncurry_gluedCoeff_of_neg M₁ M₂ R hz]
    linarith
  · rw [uncurry_gluedCoeff_of_nonneg M₁ M₂ R (not_lt.1 hz)]
    linarith

/-! ### The error on the neck -/

/-- On the support of the left cutoff `TauCeti.neckCutoff (-(2 / R))`, the glued coefficient field
is within `2 ε` of `M₁(· + R, ·)`: they agree on `s < 0`, and on `[0, R / 2)` both are close to
`M`. -/
private theorem ae_neck_bound_left {M₁ M₂ : ℝ × ℝ → V × V × V →L[ℝ] W}
    {M : ℝ → V × V × V →L[ℝ] W} {ε T₁ T₂ R : ℝ}
    (hT₁ : ∀ s ≥ T₁, ∀ t ∈ Icc (0 : ℝ) 1, dist (M t) (M₁ (s, t)) < ε)
    (hT₂ : ∀ s ≤ T₂, ∀ t ∈ Icc (0 : ℝ) 1, dist (M t) (M₂ (s, t)) < ε) (hε : 0 ≤ ε)
    (hR : 0 < R) (hRT₁ : 2 * T₁ ≤ R) (hRT₂ : -2 * T₂ ≤ R) :
    ∀ᵐ z ∂stripMeasure, neckCutoff (-(2 / R)) z.1 ≠ 0 →
      ‖Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R) z -
        M₁ (z + (R, 0))‖ ≤ 2 * ε := by
  filter_upwards [ae_restrict_mem (MeasurableSet.univ.prod measurableSet_Icc)] with z hz hβ
  rcases lt_or_ge z.1 0 with h0 | h0
  · rw [uncurry_gluedCoeff_of_neg _ _ _ h0, sub_self, norm_zero]
    positivity
  have hs : z.1 < R / 2 := by
    by_contra h
    exact hβ (neckCutoff_neg_two_div_eq_zero hR (not_lt.1 h))
  rw [uncurry_gluedCoeff_of_nonneg _ _ _ h0]
  have e₁ : z + (R, 0) = (z.1 + R, z.2) := by ext <;> simp
  have e₂ : z + (-R, 0) = (z.1 + -R, z.2) := by ext <;> simp
  rw [e₁, e₂, ← dist_eq_norm]
  linarith [dist_triangle_left (M₂ (z.1 + -R, z.2)) (M₁ (z.1 + R, z.2)) (M z.2),
    hT₂ (z.1 + -R) (by linarith) _ hz.2, hT₁ (z.1 + R) (by linarith) _ hz.2]

/-- On the support of the right cutoff `TauCeti.neckCutoff (2 / R)`, the glued coefficient field is
within `2 ε` of `M₂(· - R, ·)`: they agree on `s ≥ 0`, and on `(-R / 2, 0)` both are close to
`M`. -/
private theorem ae_neck_bound_right {M₁ M₂ : ℝ × ℝ → V × V × V →L[ℝ] W}
    {M : ℝ → V × V × V →L[ℝ] W} {ε T₁ T₂ R : ℝ}
    (hT₁ : ∀ s ≥ T₁, ∀ t ∈ Icc (0 : ℝ) 1, dist (M t) (M₁ (s, t)) < ε)
    (hT₂ : ∀ s ≤ T₂, ∀ t ∈ Icc (0 : ℝ) 1, dist (M t) (M₂ (s, t)) < ε) (hε : 0 ≤ ε)
    (hR : 0 < R) (hRT₁ : 2 * T₁ ≤ R) (hRT₂ : -2 * T₂ ≤ R) :
    ∀ᵐ z ∂stripMeasure, neckCutoff (2 / R) z.1 ≠ 0 →
      ‖Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R) z -
        M₂ (z + (-R, 0))‖ ≤ 2 * ε := by
  filter_upwards [ae_restrict_mem (MeasurableSet.univ.prod measurableSet_Icc)] with z hz hβ
  rcases le_or_gt 0 z.1 with h0 | h0
  · rw [uncurry_gluedCoeff_of_nonneg _ _ _ h0, sub_self, norm_zero]
    positivity
  have hs : -(R / 2) < z.1 := by
    by_contra h
    exact hβ (neckCutoff_two_div_eq_zero hR (not_lt.1 h))
  rw [uncurry_gluedCoeff_of_neg _ _ _ h0]
  have e₁ : z + (R, 0) = (z.1 + R, z.2) := by ext <;> simp
  have e₂ : z + (-R, 0) = (z.1 + -R, z.2) := by ext <;> simp
  rw [e₁, e₂, ← dist_eq_norm]
  linarith [dist_triangle_left (M₁ (z.1 + R, z.2)) (M₂ (z.1 + -R, z.2)) (M z.2),
    hT₁ (z.1 + R) (by linarith) _ hz.2, hT₂ (z.1 + -R) (by linarith) _ hz.2]

/-! ### The spliced right inverse -/

/-- A cut-off piece `β Q (χ η)` of the spliced inverse, with `|β|, |β'| ≤ 1` and `χ` of norm at
most one, has norm at most `2 ‖Q‖ ‖η‖`. -/
private theorem norm_cutoffL_apply_apply_le {β : ℝ → ℝ} (hβ : ContDiff ℝ 2 β)
    (hβ1 : ∀ s, |β s| ≤ 1) (hβ'1 : ∀ s, |deriv β s| ≤ 1) (Q : Lp W 2 stripMeasure →L[ℝ] H1 V)
    {χ : Lp W 2 stripMeasure →L[ℝ] Lp W 2 stripMeasure} (hχ : ∀ η, ‖χ η‖ ≤ ‖η‖)
    (η : Lp W 2 stripMeasure) : ‖cutoffL hβ hβ1 hβ'1 (Q (χ η))‖ ≤ 2 * (‖Q‖ * ‖η‖) := by
  refine (norm_cutoffL_apply_le hβ hβ1 hβ'1 _).trans ?_
  rw [one_add_one_eq_two]
  exact mul_le_mul_of_nonneg_left ((Q.le_opNorm _).trans
    (mul_le_mul_of_nonneg_left (hχ η) (norm_nonneg Q))) zero_le_two

/-- **The spliced inverse.** Let `G` be glued from `N₁` on `s < 0` and `N₂` on `s ≥ 0`, in the
sense that `G` is within `ε` of `Nᵢ` on the support of the cutoff `βᵢ`, and let `Qᵢ` be right
inverses of the operators of `Nᵢ`. Then `Q₀ η = β₁ Q₁ (𝟙_{s < 0} η) + β₂ Q₂ (𝟙_{s ≥ 0} η)` has norm
at most `2 (‖Q₁‖ + ‖Q₂‖)`, and `D_G Q₀` is within `(ε + 2 L B / R) (‖Q₁‖ + ‖Q₂‖)` of the
identity. -/
private theorem exists_splicedInverse {G N₁ N₂ : ℝ × ℝ → V × V × V →L[ℝ] W}
    (hG : MemLp G ∞ stripMeasure) (hN₁ : MemLp N₁ ∞ stripMeasure)
    (hN₂ : MemLp N₂ ∞ stripMeasure) {B ε L R : ℝ} (hB : ∀ᵐ z ∂stripMeasure, ‖G z‖ ≤ B)
    (hB0 : 0 ≤ B) (hε : 0 ≤ ε) (hR : 0 < R) (hL : ∀ t, ‖deriv Real.smoothTransition t‖ ≤ L)
    (hRL : 2 / R * L ≤ 1)
    (hGN₁ : ∀ᵐ z ∂stripMeasure, neckCutoff (-(2 / R)) z.1 ≠ 0 → ‖G z - N₁ z‖ ≤ ε)
    (hGN₂ : ∀ᵐ z ∂stripMeasure, neckCutoff (2 / R) z.1 ≠ 0 → ‖G z - N₂ z‖ ≤ ε)
    {Q₁ Q₂ : Lp W 2 stripMeasure →L[ℝ] H1 V}
    (hQ₁ : ((jetOperator stripMeasure N₁).comp (H1 V).subtypeL).comp Q₁ =
      ContinuousLinearMap.id ℝ _)
    (hQ₂ : ((jetOperator stripMeasure N₂).comp (H1 V).subtypeL).comp Q₂ =
      ContinuousLinearMap.id ℝ _) :
    ∃ Q₀ : Lp W 2 stripMeasure →L[ℝ] H1 V, ‖Q₀‖ ≤ 2 * (‖Q₁‖ + ‖Q₂‖) ∧
      ‖((jetOperator stripMeasure G).comp (H1 V).subtypeL).comp Q₀ -
        ContinuousLinearMap.id ℝ _‖ ≤ (ε + 2 / R * L * B) * (‖Q₁‖ + ‖Q₂‖) := by
  set S : Set (ℝ × ℝ) := {z | z.1 < 0}
  have hS : MeasurableSet S := measurableSet_lt measurable_fst measurable_const
  -- The cutoffs and the cut-offs of `η` to the two half-planes.
  have hR2 : 0 < 2 / R := div_pos two_pos hR
  have hd₁ (s : ℝ) : |deriv (neckCutoff (-(2 / R))) s| ≤ 2 / R * L :=
    (abs_deriv_neckCutoff_le hL _ s).trans_eq (by rw [abs_neg, abs_of_pos hR2])
  have hd₂ (s : ℝ) : |deriv (neckCutoff (2 / R)) s| ≤ 2 / R * L :=
    (abs_deriv_neckCutoff_le hL _ s).trans_eq (by rw [abs_of_pos hR2])
  have hd₁' (s : ℝ) := (hd₁ s).trans hRL
  have hd₂' (s : ℝ) := (hd₂ s).trans hRL
  have hc₁ := contDiff_neckCutoff (-(2 / R)) (n := 2)
  have hc₂ := contDiff_neckCutoff (2 / R) (n := 2)
  set β₁ := cutoffL (V := V) hc₁ (abs_neckCutoff_le_one _) hd₁'
  set β₂ := cutoffL (V := V) hc₂ (abs_neckCutoff_le_one _) hd₂'
  set χ₁ := Lp.multiplicationOperator (E := W) (p := 2) (linftyIndicator stripMeasure S hS)
  set χ₂ := Lp.multiplicationOperator (E := W) (p := 2)
    (linftyIndicator stripMeasure Sᶜ hS.compl)
  have hδ : 0 ≤ ε + 2 / R * L * B :=
    add_nonneg hε (mul_nonneg (mul_nonneg hR2.le ((norm_nonneg _).trans (hL 0))) hB0)
  refine ⟨β₁.comp (Q₁.comp χ₁) + β₂.comp (Q₂.comp χ₂), ?_, ?_⟩
  · refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun η ↦ ?_
    simp only [add_apply, ContinuousLinearMap.comp_apply]
    refine (norm_add_le _ _).trans ((add_le_add
      (norm_cutoffL_apply_apply_le hc₁ (abs_neckCutoff_le_one _) hd₁' Q₁
        (Lp.norm_multiplicationOperator_linftyIndicator_apply_le hS) η)
      (norm_cutoffL_apply_apply_le hc₂ (abs_neckCutoff_le_one _) hd₂' Q₂
        (Lp.norm_multiplicationOperator_linftyIndicator_apply_le hS.compl) η)).trans_eq ?_)
    ring
  · refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hδ (by positivity)) fun η ↦ ?_
    have e₁ := norm_jetOperator_cutoffL_apply_sub_le hG hN₁ hc₁ (abs_neckCutoff_le_one _) hd₁' hS
      (fun z hz ↦ neckCutoff_neg_two_div_eq_one hR.le (le_of_lt hz)) hB hB0 hd₁ hε hGN₁
      hQ₁ η
    have e₂ := norm_jetOperator_cutoffL_apply_sub_le hG hN₂ hc₂ (abs_neckCutoff_le_one _) hd₂'
      hS.compl (fun z hz ↦ neckCutoff_two_div_eq_one hR.le (not_lt.1 hz)) hB hB0 hd₂ hε
      hGN₂ hQ₂ η
    simp only [sub_apply, ContinuousLinearMap.comp_apply, add_apply, Submodule.subtypeL_apply,
      map_add, ContinuousLinearMap.id_apply]
    calc _ = ‖(jetOperator stripMeasure G (β₁ (Q₁ (χ₁ η)) : Lp (V × V × V) 2 stripMeasure) -
            χ₁ η) + (jetOperator stripMeasure G (β₂ (Q₂ (χ₂ η)) : Lp (V × V × V) 2 stripMeasure) -
            χ₂ η)‖ := by
          rw [sub_add_sub_comm, Lp.multiplicationOperator_linftyIndicator_add_compl hS η]
      _ ≤ (ε + 2 / R * L * B) * (‖Q₁‖ * ‖η‖) + (ε + 2 / R * L * B) * (‖Q₂‖ * ‖η‖) :=
          (norm_add_le _ _).trans (add_le_add e₁ e₂)
      _ = _ := by ring

variable [CompleteSpace W]

/-- **Gluing cylinder operators with surjective pieces.** Let `M₁` and `M₂` be essentially bounded
coefficient fields of first-order operators on the cylinder, with `M₁(s, t) → M(t)` as `s → +∞`
and `M₂(s, t) → M(t)` as `s → -∞`, uniformly in `t ∈ [0, 1]`, and suppose that the operators
`D₁` and `D₂` of `M₁` and `M₂` from `W^{1,2}(ℝ × S¹, V)` to `L²` have bounded linear right inverses
`Q₁` and `Q₂`. Then for every sufficiently large `R`, the operator of the glued coefficient field
`M_R(s, t)`, equal to `M₁(s + R, t)` for `s < 0` and to `M₂(s - R, t)` for `s ≥ 0` (neck length
`2 R`), has a bounded linear right inverse of norm at most `4 (‖Q₁‖ + ‖Q₂‖)`. -/
theorem exists_forall_ge_exists_rightInverse_jetOperator_gluedCoeff
    {M₁ M₂ : ℝ × ℝ → V × V × V →L[ℝ] W} {M : ℝ → V × V × V →L[ℝ] W}
    (hM₁ : MemLp M₁ ∞ stripMeasure) (hM₂ : MemLp M₂ ∞ stripMeasure)
    (h₁ : TendstoUniformlyOn (Function.curry M₁) M atTop (Icc 0 1))
    (h₂ : TendstoUniformlyOn (Function.curry M₂) M atBot (Icc 0 1))
    {Q₁ Q₂ : Lp W 2 stripMeasure →L[ℝ] H1 V}
    (hQ₁ : ((jetOperator stripMeasure M₁).comp (H1 V).subtypeL).comp Q₁ =
      ContinuousLinearMap.id ℝ _)
    (hQ₂ : ((jetOperator stripMeasure M₂).comp (H1 V).subtypeL).comp Q₂ =
      ContinuousLinearMap.id ℝ _) :
    ∃ R₀ : ℝ, ∀ R ≥ R₀, ∃ Q : Lp W 2 stripMeasure →L[ℝ] H1 V,
      ((jetOperator stripMeasure
          (Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R))).comp
          (H1 V).subtypeL).comp Q = ContinuousLinearMap.id ℝ _ ∧
        ‖Q‖ ≤ 4 * (‖Q₁‖ + ‖Q₂‖) := by
  obtain ⟨L, hL⟩ := Real.smoothTransition.exists_forall_norm_deriv_le
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL 0)
  -- Opaque names for the constants keep the arithmetic below away from the operator norms.
  obtain ⟨K, hK⟩ : ∃ K, K = ‖Q₁‖ + ‖Q₂‖ := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  obtain ⟨B, hB⟩ : ∃ B, B = lpNorm M₁ ∞ stripMeasure + lpNorm M₂ ∞ stripMeasure := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by rw [hB]; exact add_nonneg lpNorm_nonneg lpNorm_nonneg
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = 1 / (8 * (K + 1)) := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hε]; positivity
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.1 (Metric.tendstoUniformlyOn_iff.1 h₁ ε hε0)
  obtain ⟨T₂, hT₂⟩ := eventually_atBot.1 (Metric.tendstoUniformlyOn_iff.1 h₂ ε hε0)
  refine ⟨max (max (2 * T₁) (-2 * T₂)) (max 1 (max (2 * L) (8 * L * B * (K + 1)))),
    fun R hR ↦ ?_⟩
  simp only [ge_iff_le, max_le_iff] at hR
  obtain ⟨⟨hRT₁, hRT₂⟩, hR1, hR2L, hRL⟩ := hR
  have hRpos : 0 < R := by linarith
  obtain ⟨Q₁', hQ₁', hQ₁'n⟩ := exists_rightInverse_jetOperator_comp_add hM₁ hQ₁ R
  obtain ⟨Q₂', hQ₂', hQ₂'n⟩ := exists_rightInverse_jetOperator_comp_add hM₂ hQ₂ (-R)
  obtain ⟨hG, hGB⟩ := memLp_uncurry_gluedCoeff hM₁ hM₂ R
  have hcut : 2 / R * L ≤ 1 := by rw [div_mul_eq_mul_div, div_le_one hRpos]; linarith
  obtain ⟨Q₀, hQ₀n, hE⟩ := exists_splicedInverse hG
    (hM₁.comp_measurePreserving (measurePreserving_add_strip R))
    (hM₂.comp_measurePreserving (measurePreserving_add_strip (-R))) (hB ▸ hGB) hB0
    (by positivity) hRpos hL hcut
    (ae_neck_bound_left hT₁ hT₂ hε0.le hRpos hRT₁ hRT₂)
    (ae_neck_bound_right hT₁ hT₂ hε0.le hRpos hRT₁ hRT₂) hQ₁' hQ₂'
  -- The arithmetic making the error at most `1 / 2`.
  have hK' : ‖Q₁'‖ + ‖Q₂'‖ ≤ K := hK ▸ add_le_add hQ₁'n hQ₂'n
  have hδ : (2 * ε + 2 / R * L * B) * (‖Q₁'‖ + ‖Q₂'‖) ≤ 1 / 2 := by
    have hLR : 2 / R * L * B * (K + 1) ≤ 1 / 4 := by
      rw [show 2 / R * L * B * (K + 1) = 2 * L * B * (K + 1) / R by ring, div_le_iff₀ hRpos]
      linarith
    have hεK : 2 * ε * (K + 1) = 1 / 4 := by
      rw [hε]
      field_simp
      ring
    have h0 : 0 ≤ 2 * ε + 2 / R * L * B := by positivity
    calc _ ≤ (2 * ε + 2 / R * L * B) * (K + 1) :=
          mul_le_mul_of_nonneg_left (hK'.trans (le_add_of_nonneg_right zero_le_one)) h0
      _ ≤ 1 / 2 := by linarith
  obtain ⟨Q, hQ, hQn⟩ :=
    ContinuousLinearMap.exists_rightInverse_of_norm_comp_sub_id_le_half _ Q₀ (hE.trans hδ)
  refine ⟨Q, hQ, hQn.trans ?_⟩
  rw [← hK]
  linarith

end TauCeti.CylinderSobolev
