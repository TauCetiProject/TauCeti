/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Gluing.Coefficient
public import TauCeti.Analysis.Sobolev.Cylinder.Parametrix
public import TauCeti.Analysis.SpecialFunctions.SmoothTransition
public import TauCeti.MeasureTheory.Function.Lp.Multiplication
import Mathlib.Analysis.Normed.Operator.Prod
import TauCeti.Analysis.Normed.Operator.FiniteDimensional
import TauCeti.Analysis.Normed.Operator.Prod
import TauCeti.Analysis.Normed.Operator.Surjective
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Coprod

/-!
# Gluing first-order operators on the cylinder along a long neck

Let `D₁` and `D₂` be first-order operators `D ξ = M (ξ, ∂s ξ, ∂t ξ)` on the cylinder `ℝ × S¹`,
realized from `W^{1,2}(ℝ × S¹, V)` to `L²(ℝ × S¹, W)` by `TauCeti.jetOperator stripMeasure`, with
essentially bounded coefficient fields `M₁` and `M₂` whose ends match: `M₁(s, t) → M(t)` as
`s → +∞` and `M₂(s, t) → M(t)` as `s → -∞`, uniformly in `t`. Gluing the positive end of `M₁` to
the negative end of `M₂` along a neck of length `2 R` gives the coefficient field

`M_R(s, t) = M₁(s + R, t)` for `s < 0`, and `M_R(s, t) = M₂(s - R, t)` for `s ≥ 0`,

which is `Function.uncurry (TauCeti.gluedCoeff (Function.curry M₁) (Function.curry M₂) R)`.

**Stabilized gluing.** The pieces need not be onto. Choose bounded linear maps `ι₁ : S₁ → L²` and
`ι₂ : S₂ → L²`, the *stabilizers*, such that the stabilized operators `(ξ, σ) ↦ Dᵢ ξ + ιᵢ σ` on
`W^{1,2} × Sᵢ` are onto; typically `Sᵢ` is a finite-dimensional space of compactly supported
sections whose image complements the range of `Dᵢ`. Suppose the sections `ι₁ σ₁` vanish for
`s > T` and the sections `ι₂ σ₂` for `s < -T`, so that they stay away from the ends that are glued.
Their translates to the two ends of the neck,
`j_R (σ₁, σ₂) = (ι₁ σ₁)(· + R, ·) + (ι₂ σ₂)(· - R, ·)`
(`TauCeti.CylinderSobolev.gluedStabilizer`), stabilize the glued operator `D_R`. The main
theorem
(`TauCeti.CylinderSobolev.exists_forall_ge_exists_rightInverse_coprod_jetOperator_gluedCoeff`)
is the linear gluing estimate for stabilized pieces: if the stabilized operators `D₁ + ι₁` and
`D₂ + ι₂` have bounded linear right inverses `Q₁` and `Q₂`, then for every sufficiently long neck
the stabilized glued operator `(ξ, σ₁, σ₂) ↦ D_R ξ + j_R (σ₁, σ₂)` has a bounded linear right
inverse of norm at most `4 (‖Q₁‖ + ‖Q₂‖)`, independently of `R`. Nothing is assumed about the
common limit `M`, nor about the principal parts, beyond the matching of the ends.

For surjective pieces no stabilizer is needed: if `D₁` and `D₂` themselves have bounded linear right
inverses `Q₁` and `Q₂`, then so does `D_R` for every sufficiently long neck, of norm at most
`4 (‖Q₁‖ + ‖Q₂‖)`
(`TauCeti.CylinderSobolev.exists_forall_ge_exists_rightInverse_jetOperator_gluedCoeff`). This is
the case of zero stabilizers.

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
inverse of `S` of norm at most `2 ‖Q‖`. When the pieces are not onto, the stabilized version gives
the same uniform control on the stabilized glued operators, from which the kernel and cokernel of
`D_R` are compared with those of `D₁` and `D₂`.

* **Translation.** Translation in `s` commutes with first-order operators, the coefficient field
  being translated too (`TauCeti.CylinderSobolev.translateLp_jetOperator`), so a right inverse of
  the stabilized operator of `(M, ι)` translates to a right inverse of the stabilized operator of
  the translated data, of the same norm
  (`TauCeti.CylinderSobolev.exists_rightInverse_coprod_jetOperator_comp_add`).
* **Splicing.** Cut `η ∈ L²` into its parts `η₁` and `η₂` on `s < 0` and `s ≥ 0`, solve
  `D₁ ξ₁ + ι₁ σ₁ = η₁(· - R)` and `D₂ ξ₂ + ι₂ σ₂ = η₂(· + R)`, translate the solutions back to the
  two ends of the neck and multiply them by the cutoffs `β₁ = TauCeti.neckCutoff (-(2 / R))` and
  `β₂ = TauCeti.neckCutoff (2 / R)`, equal to `1` on the two half-lines and vanishing beyond
  `± R / 2` (`TauCeti.CylinderSobolev.cutoffL`). Once `R ≥ T`, the translated stabilizers are
  supported where the cutoffs are `1`, so the cutoffs do not affect them. For the spliced inverse
  `Q₀ η = (β₁ ξ₁(· + R) + β₂ ξ₂(· - R), σ₁, σ₂)`, the error of the stabilized glued operator
  applied to `Q₀ η`, minus `η`, is the sum over the two pieces of
  `βᵢ (M_R - Mᵢ(· ± R)) ξᵢ + βᵢ' M_R (0, ξᵢ, 0)`. The second term is small because
  `|βᵢ'| = O(1 / R)`, the first because on the support of `βᵢ` the coefficient `M_R` and the
  translate of `Mᵢ` differ only where both are close to `M`. So the composite is within `1 / 2` of
  the identity for large `R`, and its Neumann series corrects `Q₀` to an exact right inverse
  (`ContinuousLinearMap.exists_rightInverse_of_norm_comp_sub_id_lt`).

This is the cylinder version of
`TauCeti.WeakDerivStep.exists_forall_ge_exists_rightInverse_trajectoryOperator_gluedCoeff`, which
glues trajectory operators on the line, and it uses the same glued coefficient and cutoffs.

**Cut-offs beyond the neck.** Translating the cut-off of an `L²` section to a set is cutting off
its translate to the translated set
(`TauCeti.CylinderSobolev.translateLp_multiplicationOperator_linftyIndicator`), and the parts on
`s ≥ R` and on `s ≤ -R` of the sections of a finite-dimensional space of `L²` sections are
uniformly small for large `R`
(`TauCeti.CylinderSobolev.eventually_forall_norm_multiplicationOperator_le`). These control the
tails of kernel elements of the pieces beyond the neck when comparing kernels of glued operators.

## References

* A. Floer, *The unregularized gradient flow of the symplectic action*, Comm. Pure Appl. Math. 41
  (1988), 775–813, on the gluing of Floer trajectories.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 3, on gluing and the uniformly bounded right inverses of the glued
  linearized operators.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Chapter 10
  (gluing: pregluing, uniformly bounded right inverses and Newton iteration), and Section 3.1
  (stabilizing a Fredholm operator by a finite-dimensional space complementing its range).
-/

public section

noncomputable section

open Filter MeasureTheory Set Topology
open scoped ENNReal

namespace TauCeti.CylinderSobolev

open StripSobolev

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {S₁ S₂ : Type*} [NormedAddCommGroup S₁] [NormedSpace ℝ S₁]
  [NormedAddCommGroup S₂] [NormedSpace ℝ S₂]

/-! ### The error of one spliced piece -/

/-- **The error of a cutoff.** Let `x ∈ W^{1,2}`, let `N` be a coefficient field and let `ζ` be
`β(s) D_N x` for a cutoff `β`. If `‖G‖ ≤ B` and `|β'| ≤ d`, and `G` is within `ε` of `N` wherever
`β ≠ 0`, then `D_G (β x)` is within `(ε + d B) ‖x‖` of `ζ`: the two differ by `β (G - N) x` and by
the term `β' G (0, x, 0)` of the derivative of the cutoff. -/
theorem norm_jetOperator_cutoffL_sub_le {G N : ℝ × ℝ → V × V × V →L[ℝ] W}
    (hG : MemLp G ∞ stripMeasure) (hN : MemLp N ∞ stripMeasure) {β : ℝ → ℝ}
    (hβ : ContDiff ℝ 2 β) (hβ1 : ∀ s, |β s| ≤ 1) (hβ'1 : ∀ s, |deriv β s| ≤ 1) {B d ε : ℝ}
    (hB : ∀ᵐ z ∂stripMeasure, ‖G z‖ ≤ B) (hd : ∀ s, |deriv β s| ≤ d) (hε : 0 ≤ ε)
    (hGN : ∀ᵐ z ∂stripMeasure, β z.1 ≠ 0 → ‖G z - N z‖ ≤ ε) {x : H1 V}
    {ζ : Lp W 2 stripMeasure} (hζ : ∀ᵐ z ∂stripMeasure,
      ζ z = β z.1 • jetOperator stripMeasure N (x : Lp (V × V × V) 2 stripMeasure) z) :
    ‖jetOperator stripMeasure G (cutoffL hβ hβ1 hβ'1 x : Lp (V × V × V) 2 stripMeasure) - ζ‖ ≤
      (ε + d * B) * ‖x‖ := by
  rw [← Submodule.norm_coe x]
  refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
  filter_upwards [Lp.coeFn_sub (jetOperator stripMeasure G
      (cutoffL hβ hβ1 hβ'1 x : Lp (V × V × V) 2 stripMeasure)) ζ,
    coeFn_jetOperator hG (cutoffL hβ hβ1 hβ'1 x : Lp (V × V × V) 2 stripMeasure),
    coeFn_jetOperator (memLp_cutoffCoeff (hβ.of_le one_le_two) hβ1 hβ'1)
      (x : Lp (V × V × V) 2 stripMeasure), coeFn_jetOperator hN (x : Lp (V × V × V) 2 stripMeasure),
    hζ, hB, hGN] with z h₁ h₂ h₃ h₄ h₅ h₆ h₇
  set v := (x : Lp (V × V × V) 2 stripMeasure) z
  have hβζ : ζ z = β z.1 • N z v := by rw [h₅, h₄]
  have hd0 : 0 ≤ d := (abs_nonneg _).trans (hd 0)
  have hsv : ‖sSlot V v‖ ≤ ‖v‖ := by simp [Prod.norm_def]
  have key : G z (cutoffCoeff V β z v) - β z.1 • N z v =
      β z.1 • (G z - N z) v + deriv β z.1 • G z (sSlot V v) := by
    simp only [cutoffCoeff_def, add_apply, smul_apply,
      ContinuousLinearMap.id_apply, map_add, map_smul, sub_apply, smul_sub]
    abel
  rw [h₁, Pi.sub_apply, h₂, coe_cutoffL, h₃, hβζ, key]
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

/-- The error of one piece of the spliced inverse: let `Q` be a right inverse of the stabilized
operator `(ξ, σ) ↦ D_N ξ + ι σ` whose sections `ι σ` vanish off `A`, and let `β` be a cutoff equal
to `1` on `A`. Then `(x, σ) = Q (𝟙_A η)` satisfies
`‖D_G (β x) + ι σ - 𝟙_A η‖ ≤ (ε + d B) ‖Q‖ ‖η‖` under the hypotheses of
`norm_jetOperator_cutoffL_sub_le`. -/
private theorem norm_jetOperator_cutoffL_add_sub_le {S : Type*} [NormedAddCommGroup S]
    [NormedSpace ℝ S] {G N : ℝ × ℝ → V × V × V →L[ℝ] W}
    (hG : MemLp G ∞ stripMeasure) (hN : MemLp N ∞ stripMeasure) {β : ℝ → ℝ}
    (hβ : ContDiff ℝ 2 β) (hβ1 : ∀ s, |β s| ≤ 1) (hβ'1 : ∀ s, |deriv β s| ≤ 1)
    {A : Set (ℝ × ℝ)} (hA : MeasurableSet A) (hβA : ∀ z ∈ A, β z.1 = 1) {B d ε : ℝ}
    (hB : ∀ᵐ z ∂stripMeasure, ‖G z‖ ≤ B) (hB0 : 0 ≤ B) (hd : ∀ s, |deriv β s| ≤ d) (hε : 0 ≤ ε)
    (hGN : ∀ᵐ z ∂stripMeasure, β z.1 ≠ 0 → ‖G z - N z‖ ≤ ε) {ι : S →L[ℝ] Lp W 2 stripMeasure}
    (hι : ∀ σ, ∀ᵐ z ∂stripMeasure, z ∉ A → ι σ z = 0) {Q : Lp W 2 stripMeasure →L[ℝ] H1 V × S}
    (hQ : (((jetOperator stripMeasure N).comp (H1 V).subtypeL).coprod ι).comp Q =
      ContinuousLinearMap.id ℝ _) (η : Lp W 2 stripMeasure) :
    ‖jetOperator stripMeasure G (cutoffL hβ hβ1 hβ'1
          (Q (Lp.multiplicationOperator (linftyIndicator stripMeasure A hA) η)).1 :
          Lp (V × V × V) 2 stripMeasure) +
        ι (Q (Lp.multiplicationOperator (linftyIndicator stripMeasure A hA) η)).2 -
        Lp.multiplicationOperator (linftyIndicator stripMeasure A hA) η‖ ≤
      (ε + d * B) * (‖Q‖ * ‖η‖) := by
  set χη := Lp.multiplicationOperator (linftyIndicator stripMeasure A hA) η
  set y := Q χη
  have hy : jetOperator stripMeasure N (y.1 : Lp (V × V × V) 2 stripMeasure) + ι y.2 = χη := by
    simpa using congrArg (fun T ↦ T χη) hQ
  -- `D_N x = 𝟙_A η - ι σ`, which vanishes wherever `β ≠ 1`, so it is `β D_N x`.
  have hζ : ∀ᵐ z ∂stripMeasure, (χη - ι y.2) z =
      β z.1 • jetOperator stripMeasure N (y.1 : Lp (V × V × V) 2 stripMeasure) z := by
    rw [eq_sub_of_add_eq hy]
    filter_upwards [Lp.coeFn_sub χη (ι y.2), Lp.multiplicationOperator_linftyIndicator_ae hA η,
      hι y.2] with z h₁ h₂ h₃
    by_cases hz : β z.1 = 1
    · rw [hz, one_smul]
    have hzA : z ∉ A := fun hzA ↦ hz (hβA z hzA)
    rw [h₁, Pi.sub_apply, h₂, h₃ hzA, indicator_of_notMem hzA, sub_zero, smul_zero]
  have hδ : 0 ≤ ε + d * B := add_nonneg hε (mul_nonneg ((abs_nonneg _).trans (hd 0)) hB0)
  calc _ = ‖jetOperator stripMeasure G (cutoffL hβ hβ1 hβ'1 y.1 : Lp (V × V × V) 2 stripMeasure) -
        (χη - ι y.2)‖ := by rw [sub_sub_eq_add_sub]
    _ ≤ (ε + d * B) * ‖y.1‖ :=
        norm_jetOperator_cutoffL_sub_le hG hN hβ hβ1 hβ'1 hB hd hε hGN hζ
    _ ≤ (ε + d * B) * (‖Q‖ * ‖η‖) :=
        mul_le_mul_of_nonneg_left ((norm_fst_le y).trans ((Q.le_opNorm _).trans
          (mul_le_mul_of_nonneg_left (Lp.norm_multiplicationOperator_linftyIndicator_apply_le hA η)
            (norm_nonneg _)))) hδ

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
theorem ae_norm_uncurry_gluedCoeff_sub_le_left {M₁ M₂ : ℝ × ℝ → V × V × V →L[ℝ] W}
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
theorem ae_norm_uncurry_gluedCoeff_sub_le_right {M₁ M₂ : ℝ × ℝ → V × V × V →L[ℝ] W}
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

/-- The norm of a spliced inverse: if `βᵢ` multiply norms by at most `2` and `χᵢ` do not increase
them, then `η ↦ (β₁ x₁ + β₂ x₂, σ₁, σ₂)`, where `(xᵢ, σᵢ) = Qᵢ (χᵢ η)`, has norm at most
`2 (‖Q₁‖ + ‖Q₂‖)`. -/
private theorem norm_splice_le {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {β₁ β₂ : E →L[ℝ] E} (hβ₁ : ∀ x, ‖β₁ x‖ ≤ 2 * ‖x‖)
    (hβ₂ : ∀ x, ‖β₂ x‖ ≤ 2 * ‖x‖) {χ₁ χ₂ : F →L[ℝ] F} (hχ₁ : ∀ η, ‖χ₁ η‖ ≤ ‖η‖)
    (hχ₂ : ∀ η, ‖χ₂ η‖ ≤ ‖η‖) (Q₁ : F →L[ℝ] E × S₁) (Q₂ : F →L[ℝ] E × S₂) :
    ‖(β₁.comp ((ContinuousLinearMap.fst ℝ _ _).comp (Q₁.comp χ₁)) +
        β₂.comp ((ContinuousLinearMap.fst ℝ _ _).comp (Q₂.comp χ₂))).prod
      (((ContinuousLinearMap.snd ℝ _ _).comp (Q₁.comp χ₁)).prod
        ((ContinuousLinearMap.snd ℝ _ _).comp (Q₂.comp χ₂)))‖ ≤ 2 * (‖Q₁‖ + ‖Q₂‖) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun η ↦ ?_
  have hQ₁ : ‖Q₁ (χ₁ η)‖ ≤ ‖Q₁‖ * ‖η‖ :=
    (Q₁.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hχ₁ η) (norm_nonneg _))
  have hQ₂ : ‖Q₂ (χ₂ η)‖ ≤ ‖Q₂‖ * ‖η‖ :=
    (Q₂.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hχ₂ η) (norm_nonneg _))
  have h₁ := (hβ₁ (Q₁ (χ₁ η)).1).trans
    (mul_le_mul_of_nonneg_left ((norm_fst_le _).trans hQ₁) zero_le_two)
  have h₂ := (hβ₂ (Q₂ (χ₂ η)).1).trans
    (mul_le_mul_of_nonneg_left ((norm_fst_le _).trans hQ₂) zero_le_two)
  have h0 : 0 ≤ ‖Q₁‖ * ‖η‖ := by positivity
  have h0' : 0 ≤ ‖Q₂‖ * ‖η‖ := by positivity
  simp only [ContinuousLinearMap.prod_apply, add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', norm_prod_le_iff]
  exact ⟨(norm_add_le _ _).trans ((add_le_add h₁ h₂).trans_eq (by ring)),
    (norm_snd_le _).trans (hQ₁.trans (by linarith)),
    (norm_snd_le _).trans (hQ₂.trans (by linarith))⟩

/-- **The spliced inverse.** Let `G` be glued from `N₁` on `s < 0` and `N₂` on `s ≥ 0`, in the
sense that `G` is within `ε` of `Nᵢ` on the support of the cutoff `βᵢ`, let the sections `ι₁ σ₁`
vanish on `s ≥ 0` and the sections `ι₂ σ₂` on `s < 0`, and let `Qᵢ` be right inverses of the
stabilized operators `(ξ, σ) ↦ D_{Nᵢ} ξ + ιᵢ σ`. Write `(xᵢ, σᵢ) = Qᵢ (𝟙ᵢ η)` for the cut-offs
`𝟙₁ η = 𝟙_{s < 0} η` and `𝟙₂ η = 𝟙_{s ≥ 0} η`. Then `Q₀ η = (β₁ x₁ + β₂ x₂, σ₁, σ₂)` has norm at
most `2 (‖Q₁‖ + ‖Q₂‖)`, and the stabilized operator `(ξ, σ₁, σ₂) ↦ D_G ξ + ι₁ σ₁ + ι₂ σ₂` composed
with `Q₀` is within `(ε + 2 L B / R) (‖Q₁‖ + ‖Q₂‖)` of the identity. -/
private theorem exists_splicedInverse {G N₁ N₂ : ℝ × ℝ → V × V × V →L[ℝ] W}
    (hG : MemLp G ∞ stripMeasure) (hN₁ : MemLp N₁ ∞ stripMeasure)
    (hN₂ : MemLp N₂ ∞ stripMeasure) {B ε L R : ℝ} (hB : ∀ᵐ z ∂stripMeasure, ‖G z‖ ≤ B)
    (hB0 : 0 ≤ B) (hε : 0 ≤ ε) (hR : 0 < R) (hL : ∀ t, ‖deriv Real.smoothTransition t‖ ≤ L)
    (hRL : 2 / R * L ≤ 1)
    (hGN₁ : ∀ᵐ z ∂stripMeasure, neckCutoff (-(2 / R)) z.1 ≠ 0 → ‖G z - N₁ z‖ ≤ ε)
    (hGN₂ : ∀ᵐ z ∂stripMeasure, neckCutoff (2 / R) z.1 ≠ 0 → ‖G z - N₂ z‖ ≤ ε)
    {ι₁ : S₁ →L[ℝ] Lp W 2 stripMeasure} {ι₂ : S₂ →L[ℝ] Lp W 2 stripMeasure}
    (hι₁ : ∀ σ, ∀ᵐ z ∂stripMeasure, 0 ≤ z.1 → ι₁ σ z = 0)
    (hι₂ : ∀ σ, ∀ᵐ z ∂stripMeasure, z.1 < 0 → ι₂ σ z = 0)
    {Q₁ : Lp W 2 stripMeasure →L[ℝ] H1 V × S₁} {Q₂ : Lp W 2 stripMeasure →L[ℝ] H1 V × S₂}
    (hQ₁ : (((jetOperator stripMeasure N₁).comp (H1 V).subtypeL).coprod ι₁).comp Q₁ =
      ContinuousLinearMap.id ℝ _)
    (hQ₂ : (((jetOperator stripMeasure N₂).comp (H1 V).subtypeL).coprod ι₂).comp Q₂ =
      ContinuousLinearMap.id ℝ _) :
    ∃ Q₀ : Lp W 2 stripMeasure →L[ℝ] H1 V × (S₁ × S₂), ‖Q₀‖ ≤ 2 * (‖Q₁‖ + ‖Q₂‖) ∧
      ‖(((jetOperator stripMeasure G).comp (H1 V).subtypeL).coprod (ι₁.coprod ι₂)).comp Q₀ -
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
  refine ⟨(β₁.comp ((ContinuousLinearMap.fst ℝ _ _).comp (Q₁.comp χ₁)) +
      β₂.comp ((ContinuousLinearMap.fst ℝ _ _).comp (Q₂.comp χ₂))).prod
    (((ContinuousLinearMap.snd ℝ _ _).comp (Q₁.comp χ₁)).prod
      ((ContinuousLinearMap.snd ℝ _ _).comp (Q₂.comp χ₂))), ?_, ?_⟩
  · exact norm_splice_le (β₁ := β₁) (β₂ := β₂) (χ₁ := χ₁) (χ₂ := χ₂)
      (fun x ↦ (norm_cutoffL_apply_le hc₁ (abs_neckCutoff_le_one _) hd₁' x).trans_eq
        (by rw [one_add_one_eq_two]))
      (fun x ↦ (norm_cutoffL_apply_le hc₂ (abs_neckCutoff_le_one _) hd₂' x).trans_eq
        (by rw [one_add_one_eq_two]))
      (Lp.norm_multiplicationOperator_linftyIndicator_apply_le hS)
      (Lp.norm_multiplicationOperator_linftyIndicator_apply_le hS.compl) Q₁ Q₂
  · refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hδ (by positivity)) fun η ↦ ?_
    have e₁ := norm_jetOperator_cutoffL_add_sub_le hG hN₁ hc₁ (abs_neckCutoff_le_one _) hd₁' hS
      (fun z hz ↦ neckCutoff_neg_two_div_eq_one hR.le (le_of_lt hz)) hB hB0 hd₁ hε hGN₁
      (fun σ ↦ (hι₁ σ).mono fun _ h hz ↦ h (not_lt.1 hz)) hQ₁ η
    have e₂ := norm_jetOperator_cutoffL_add_sub_le hG hN₂ hc₂ (abs_neckCutoff_le_one _) hd₂'
      hS.compl (fun z hz ↦ neckCutoff_two_div_eq_one hR.le (not_lt.1 hz)) hB hB0 hd₂ hε hGN₂
      (fun σ ↦ (hι₂ σ).mono fun _ h hz ↦ h (not_not.1 hz)) hQ₂ η
    simp only [sub_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coprod_apply,
      ContinuousLinearMap.prod_apply, add_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', Submodule.subtypeL_apply, map_add,
      ContinuousLinearMap.id_apply]
    calc _ = ‖(jetOperator stripMeasure G (β₁ (Q₁ (χ₁ η)).1 : Lp (V × V × V) 2 stripMeasure) +
            ι₁ (Q₁ (χ₁ η)).2 - χ₁ η) +
          (jetOperator stripMeasure G (β₂ (Q₂ (χ₂ η)).1 : Lp (V × V × V) 2 stripMeasure) +
            ι₂ (Q₂ (χ₂ η)).2 - χ₂ η)‖ := by
          rw [sub_add_sub_comm, Lp.multiplicationOperator_linftyIndicator_add_compl hS η]
          abel_nf
      _ ≤ (ε + 2 / R * L * B) * (‖Q₁‖ * ‖η‖) + (ε + 2 / R * L * B) * (‖Q₂‖ * ‖η‖) :=
          (norm_add_le _ _).trans (add_le_add e₁ e₂)
      _ = _ := by ring

/-! ### The stabilizers of the glued operator -/

/-- **The stabilizers of the glued operator.** For stabilizers `ι₁ : S₁ → L²` and `ι₂ : S₂ → L²` of
the operators of two coefficient fields `M₁` and `M₂`, the map
`j_R (σ₁, σ₂) = (ι₁ σ₁)(· + R, ·) + (ι₂ σ₂)(· - R, ·)` translates them to the two ends of the neck
of length `2 R`, where `TauCeti.gluedCoeff` places `M₁` and `M₂`. -/
def gluedStabilizer (ι₁ : S₁ →L[ℝ] Lp W 2 stripMeasure) (ι₂ : S₂ →L[ℝ] Lp W 2 stripMeasure)
    (R : ℝ) : S₁ × S₂ →L[ℝ] Lp W 2 stripMeasure :=
  ((translateLp (E := W) (p := 2) R).toContinuousLinearEquiv.toContinuousLinearMap.comp ι₁).coprod
    ((translateLp (E := W) (p := 2) (-R)).toContinuousLinearEquiv.toContinuousLinearMap.comp ι₂)

/-- `TauCeti.CylinderSobolev.gluedStabilizer` is the sum of the translates of the two
stabilizers. -/
theorem gluedStabilizer_def (ι₁ : S₁ →L[ℝ] Lp W 2 stripMeasure)
    (ι₂ : S₂ →L[ℝ] Lp W 2 stripMeasure) (R : ℝ) :
    gluedStabilizer ι₁ ι₂ R =
      ((translateLp (E := W) (p := 2) R).toContinuousLinearEquiv.toContinuousLinearMap.comp
        ι₁).coprod
        ((translateLp (E := W) (p := 2) (-R)).toContinuousLinearEquiv.toContinuousLinearMap.comp
          ι₂) :=
  (rfl)

/-- The glued stabilizer of `(σ₁, σ₂)` is `(ι₁ σ₁)(· + R, ·) + (ι₂ σ₂)(· - R, ·)`. -/
@[simp]
theorem gluedStabilizer_apply (ι₁ : S₁ →L[ℝ] Lp W 2 stripMeasure)
    (ι₂ : S₂ →L[ℝ] Lp W 2 stripMeasure) (R : ℝ) (σ : S₁ × S₂) :
    gluedStabilizer ι₁ ι₂ R σ = translateLp R (ι₁ σ.1) + translateLp (-R) (ι₂ σ.2) :=
  (rfl)

/-- If the sections `ι σ` vanish for `s > T`, then their translates `(ι σ)(· + a, ·)` vanish for
`s > T - a`. -/
theorem ae_translateLp_eq_zero_of_sub_lt {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
    {ι : S →L[ℝ] Lp W 2 stripMeasure} {T : ℝ}
    (hι : ∀ σ, ∀ᵐ z ∂stripMeasure, T < z.1 → ι σ z = 0) (a : ℝ) (σ : S) :
    ∀ᵐ z ∂stripMeasure, T - a < z.1 → translateLp a (ι σ) z = 0 := by
  filter_upwards [coeFn_translateLp a (ι σ),
    (measurePreserving_add_strip a).quasiMeasurePreserving.ae (hι σ)] with z h₁ h₂ hz
  rw [h₁]
  exact h₂ (by rw [Prod.fst_add]; linarith)

/-- If the sections `ι σ` vanish for `s < -T`, then their translates `(ι σ)(· + a, ·)` vanish for
`s < -T - a`. -/
theorem ae_translateLp_eq_zero_of_lt_neg_sub {S : Type*} [NormedAddCommGroup S]
    [NormedSpace ℝ S] {ι : S →L[ℝ] Lp W 2 stripMeasure} {T : ℝ}
    (hι : ∀ σ, ∀ᵐ z ∂stripMeasure, z.1 < -T → ι σ z = 0) (a : ℝ) (σ : S) :
    ∀ᵐ z ∂stripMeasure, z.1 < -T - a → translateLp a (ι σ) z = 0 := by
  filter_upwards [coeFn_translateLp a (ι σ),
    (measurePreserving_add_strip a).quasiMeasurePreserving.ae (hι σ)] with z h₁ h₂ hz
  rw [h₁]
  exact h₂ (by rw [Prod.fst_add]; linarith)

/-! ### Cut-offs beyond the neck -/

/-- Translating the cut-off of an `L²` class to `A` by `a` is cutting off its translate to the set
`B` of the points that `z ↦ z + (a, 0)` maps into `A`. -/
theorem translateLp_multiplicationOperator_linftyIndicator {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {A B : Set (ℝ × ℝ)} (hA : MeasurableSet A) (hB : MeasurableSet B) (a : ℝ)
    (hAB : ∀ z, z ∈ B ↔ z + (a, 0) ∈ A) (f : Lp E 2 stripMeasure) :
    translateLp a (Lp.multiplicationOperator (linftyIndicator stripMeasure A hA) f) =
      Lp.multiplicationOperator (linftyIndicator stripMeasure B hB) (translateLp a f) := by
  refine Lp.ext ?_
  filter_upwards [coeFn_translateLp a
      (Lp.multiplicationOperator (linftyIndicator stripMeasure A hA) f),
    Lp.multiplicationOperator_linftyIndicator_ae hB (translateLp a f), coeFn_translateLp a f,
    (measurePreserving_add_strip a).quasiMeasurePreserving.ae
      (Lp.multiplicationOperator_linftyIndicator_ae hA f)] with z h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₄]
  by_cases hz : z ∈ B
  · rw [indicator_of_mem ((hAB z).1 hz), indicator_of_mem hz, h₃]
  · rw [indicator_of_notMem (mt (hAB z).2 hz), indicator_of_notMem hz]

/-- **Uniformly small tails.** The parts on `s ≥ R` and on `s ≤ -R` of the sections in a
finite-dimensional space `K` of `L²` sections are, for large `R`, at most `θ` times the norms of
the sections. -/
theorem eventually_forall_norm_multiplicationOperator_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (K : Submodule ℝ (Lp E 2 stripMeasure)) [FiniteDimensional ℝ K] {θ : ℝ}
    (hθ : 0 < θ) :
    (∀ᶠ R in atTop, ∀ f ∈ K, ‖Lp.multiplicationOperator (linftyIndicator stripMeasure
        {z : ℝ × ℝ | R ≤ z.1} (measurableSet_le measurable_const measurable_fst)) f‖ ≤ θ * ‖f‖) ∧
      ∀ᶠ R in atTop, ∀ f ∈ K, ‖Lp.multiplicationOperator (linftyIndicator stripMeasure
        {z : ℝ × ℝ | z.1 ≤ -R} (measurableSet_le measurable_fst measurable_const)) f‖ ≤
          θ * ‖f‖ := by
  -- The cut-offs to a decreasing family of sets with empty intersection, as operators on `K`,
  -- tend to zero in operator norm.
  have key {s : ℝ → Set (ℝ × ℝ)} (hs : ∀ R, MeasurableSet (s R)) (hanti : Antitone s)
      (hempty : ⋂ R, s R = ∅) : ∀ᶠ R in atTop, ∀ f ∈ K, ‖Lp.multiplicationOperator
        (linftyIndicator stripMeasure (s R) (hs R)) f‖ ≤ θ * ‖f‖ := by
    let T (R : ℝ) : K →L[ℝ] Lp E 2 stripMeasure :=
      (Lp.multiplicationOperator (linftyIndicator stripMeasure (s R) (hs R))).comp K.subtypeL
    have hT : Tendsto (fun R ↦ ‖T R‖) atTop (𝓝 0) :=
      ContinuousLinearMap.tendsto_opNorm_zero_of_forall_tendsto_zero fun f ↦
        tendsto_zero_iff_norm_tendsto_zero.2 (Lp.tendsto_norm_multiplicationOperator_linftyIndicator
          ENNReal.ofNat_ne_top hs hanti hempty _)
    filter_upwards [hT.eventually (ge_mem_nhds hθ)] with R hR f hf
    exact ((T R).le_opNorm ⟨f, hf⟩).trans (mul_le_mul_of_nonneg_right hR (norm_nonneg _))
  refine ⟨key _ (fun _ _ hab _ h ↦ by simp only [mem_ofPred_eq] at h ⊢; linarith) ?_,
    key _ (fun _ _ hab _ h ↦ by simp only [mem_ofPred_eq] at h ⊢; linarith) ?_⟩
  · refine eq_empty_of_forall_notMem fun z hz ↦ ?_
    have := mem_iInter.1 hz (z.1 + 1)
    simp only [mem_ofPred_eq] at this
    linarith
  · refine eq_empty_of_forall_notMem fun z hz ↦ ?_
    have := mem_iInter.1 hz (-z.1 + 1)
    simp only [mem_ofPred_eq] at this
    linarith

variable [CompleteSpace W]

/-- **Gluing stabilized cylinder operators.** Let `M₁` and `M₂` be essentially bounded coefficient
fields of first-order operators `D₁` and `D₂` on the cylinder, from `W^{1,2}(ℝ × S¹, V)` to `L²`,
with `M₁(s, t) → M(t)` as `s → +∞` and `M₂(s, t) → M(t)` as `s → -∞`, uniformly in `t ∈ [0, 1]`.
Let `ι₁ : S₁ → L²` and `ι₂ : S₂ → L²` be bounded linear maps whose sections `ι₁ σ₁` vanish for
`s > T` and `ι₂ σ₂` for `s < -T`, and suppose that the stabilized operators
`(ξ, σ) ↦ Dᵢ ξ + ιᵢ σ` have bounded linear right inverses `Q₁` and `Q₂`. Then for every
sufficiently large `R`, the stabilized operator `(ξ, σ₁, σ₂) ↦ D_R ξ + j_R (σ₁, σ₂)` of the glued
coefficient field `M_R(s, t)`, equal to `M₁(s + R, t)` for `s < 0` and to `M₂(s - R, t)` for
`s ≥ 0` (neck length `2 R`), with the stabilizers
`j_R (σ₁, σ₂) = (ι₁ σ₁)(· + R, ·) + (ι₂ σ₂)(· - R, ·)` (`gluedStabilizer`), has a bounded linear
right inverse of norm at most `4 (‖Q₁‖ + ‖Q₂‖)`. -/
theorem exists_forall_ge_exists_rightInverse_coprod_jetOperator_gluedCoeff
    {M₁ M₂ : ℝ × ℝ → V × V × V →L[ℝ] W} {M : ℝ → V × V × V →L[ℝ] W}
    (hM₁ : MemLp M₁ ∞ stripMeasure) (hM₂ : MemLp M₂ ∞ stripMeasure)
    (h₁ : TendstoUniformlyOn (Function.curry M₁) M atTop (Icc 0 1))
    (h₂ : TendstoUniformlyOn (Function.curry M₂) M atBot (Icc 0 1))
    {ι₁ : S₁ →L[ℝ] Lp W 2 stripMeasure} {ι₂ : S₂ →L[ℝ] Lp W 2 stripMeasure} {T : ℝ}
    (hι₁ : ∀ σ, ∀ᵐ z ∂stripMeasure, T < z.1 → ι₁ σ z = 0)
    (hι₂ : ∀ σ, ∀ᵐ z ∂stripMeasure, z.1 < -T → ι₂ σ z = 0)
    {Q₁ : Lp W 2 stripMeasure →L[ℝ] H1 V × S₁} {Q₂ : Lp W 2 stripMeasure →L[ℝ] H1 V × S₂}
    (hQ₁ : (((jetOperator stripMeasure M₁).comp (H1 V).subtypeL).coprod ι₁).comp Q₁ =
      ContinuousLinearMap.id ℝ _)
    (hQ₂ : (((jetOperator stripMeasure M₂).comp (H1 V).subtypeL).coprod ι₂).comp Q₂ =
      ContinuousLinearMap.id ℝ _) :
    ∃ R₀ : ℝ, ∀ R ≥ R₀, ∃ Q : Lp W 2 stripMeasure →L[ℝ] H1 V × (S₁ × S₂),
      (((jetOperator stripMeasure
          (Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R))).comp
          (H1 V).subtypeL).coprod (gluedStabilizer ι₁ ι₂ R)).comp Q =
          ContinuousLinearMap.id ℝ _ ∧
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
  refine ⟨max (max (max (2 * T₁) (-2 * T₂)) (T + 1)) (max 1 (max (2 * L) (8 * L * B * (K + 1)))),
    fun R hR ↦ ?_⟩
  simp only [ge_iff_le, max_le_iff] at hR
  obtain ⟨⟨⟨hRT₁, hRT₂⟩, hRT⟩, hR1, hR2L, hRL⟩ := hR
  have hRpos : 0 < R := by linarith
  obtain ⟨Q₁', hQ₁', hQ₁'n⟩ := exists_rightInverse_coprod_jetOperator_comp_add hM₁ hQ₁ R
  obtain ⟨Q₂', hQ₂', hQ₂'n⟩ := exists_rightInverse_coprod_jetOperator_comp_add hM₂ hQ₂ (-R)
  obtain ⟨hG, hGB⟩ := memLp_uncurry_gluedCoeff hM₁ hM₂ R
  have hcut : 2 / R * L ≤ 1 := by rw [div_mul_eq_mul_div, div_le_one hRpos]; linarith
  obtain ⟨Q₀, hQ₀n, hE⟩ := exists_splicedInverse hG
    (hM₁.comp_measurePreserving (measurePreserving_add_strip R))
    (hM₂.comp_measurePreserving (measurePreserving_add_strip (-R))) (hB ▸ hGB) hB0
    (by positivity) hRpos hL hcut
    (ae_norm_uncurry_gluedCoeff_sub_le_left hT₁ hT₂ hε0.le hRpos hRT₁ hRT₂)
    (ae_norm_uncurry_gluedCoeff_sub_le_right hT₁ hT₂ hε0.le hRpos hRT₁ hRT₂)
    (fun σ ↦ (ae_translateLp_eq_zero_of_sub_lt hι₁ R σ).mono fun _ h hz ↦ h (by linarith))
    (fun σ ↦ (ae_translateLp_eq_zero_of_lt_neg_sub hι₂ (-R) σ).mono fun _ h hz ↦ h (by linarith))
    hQ₁' hQ₂'
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
  refine ⟨Q, by rwa [gluedStabilizer_def], hQn.trans ?_⟩
  rw [← hK]
  linarith

/-- **Gluing cylinder operators with surjective pieces.** Let `M₁` and `M₂` be essentially bounded
coefficient fields of first-order operators on the cylinder, with `M₁(s, t) → M(t)` as `s → +∞`
and `M₂(s, t) → M(t)` as `s → -∞`, uniformly in `t ∈ [0, 1]`, and suppose that the operators
`D₁` and `D₂` of `M₁` and `M₂` from `W^{1,2}(ℝ × S¹, V)` to `L²` have bounded linear right inverses
`Q₁` and `Q₂`. Then for every sufficiently large `R`, the operator of the glued coefficient field
`M_R(s, t)`, equal to `M₁(s + R, t)` for `s < 0` and to `M₂(s - R, t)` for `s ≥ 0` (neck length
`2 R`), has a bounded linear right inverse of norm at most `4 (‖Q₁‖ + ‖Q₂‖)`. This is the case of
zero stabilizers in `exists_forall_ge_exists_rightInverse_coprod_jetOperator_gluedCoeff`. -/
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
  -- The zero stabilizer on the zero space.
  have h0 : ∀ σ : Unit, ∀ᵐ z ∂stripMeasure,
      (0 : Unit →L[ℝ] Lp W 2 stripMeasure) σ z = 0 := fun σ ↦ by
    filter_upwards [Lp.coeFn_zero W 2 stripMeasure] with z hz
    rw [zero_apply, hz, Pi.zero_apply]
  obtain ⟨R₀, hR₀⟩ := exists_forall_ge_exists_rightInverse_coprod_jetOperator_gluedCoeff hM₁ hM₂
    h₁ h₂ (T := 0) (fun σ ↦ (h0 σ).mono fun z hz _ ↦ hz) (fun σ ↦ (h0 σ).mono fun z hz _ ↦ hz)
    (Q₁ := Q₁.prod 0) (Q₂ := Q₂.prod 0)
    (by rw [ContinuousLinearMap.coprod_zero_comp_prod_zero, hQ₁])
    (by rw [ContinuousLinearMap.coprod_zero_comp_prod_zero, hQ₂])
  refine ⟨R₀, fun R hR ↦ ?_⟩
  obtain ⟨Q, hQ, hQn⟩ := hR₀ R hR
  refine ⟨(ContinuousLinearMap.fst ℝ _ _).comp Q, ?_, ?_⟩
  · have hj : gluedStabilizer (0 : Unit →L[ℝ] Lp W 2 stripMeasure)
        (0 : Unit →L[ℝ] Lp W 2 stripMeasure) R = 0 := by
      ext <;> simp
    rw [← hQ, hj, ContinuousLinearMap.coprod_zero_right, ← ContinuousLinearMap.comp_assoc]
  · rw [← Q₁.opNorm_prod_zero (G := Unit), ← Q₂.opNorm_prod_zero (G := Unit)]
    exact Q.opNorm_fst_comp_le.trans hQn

end TauCeti.CylinderSobolev
