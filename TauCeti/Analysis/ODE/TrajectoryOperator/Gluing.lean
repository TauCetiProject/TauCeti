/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.TrajectoryOperator
public import TauCeti.Analysis.Sobolev.GraphStep.Multiplication
public import TauCeti.Analysis.Sobolev.GraphStep.Translation
import TauCeti.Analysis.Normed.Operator.Surjective
import TauCeti.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.MeasureTheory.Function.Lp.Multiplication.Basic

/-!
# Gluing trajectory operators along a long neck

Let `A₁, A₂ : ℝ → End(F)` be essentially bounded coefficients of trajectory operators
`D_{Aᵢ} u = u' + Aᵢ u` from `W^{1,p}(ℝ, F)` to `Lᵖ(ℝ, F)`, on a real Banach space `F`, whose ends
match: `A₁(s) → A` as `s → +∞` and `A₂(s) → A` as `s → -∞`. Gluing the positive end of `A₁` to the
negative end of `A₂` along a neck of length `2 R` gives the coefficient

`A_R(s) = A₁(s + R)` for `s < 0`, and `A_R(s) = A₂(s - R)` for `s ≥ 0`

(`TauCeti.gluedCoeff`). Near `-R` the glued operator `D_{A_R}` is `D_{A₁}` translated by `-R`, and
near `R` it is `D_{A₂}` translated by `R`.

The main theorem
(`TauCeti.WeakDerivStep.exists_forall_ge_exists_rightInverse_trajectoryOperator_gluedCoeff`) is
the linear gluing estimate for surjective pieces: if `D_{A₁}` and `D_{A₂}` have bounded linear right
inverses, then for every sufficiently long neck the glued operator `D_{A_R}` has a bounded linear
right inverse, with a norm bound independent of `R`. Nothing is assumed about the common limit `A`
beyond its existence; it is the surjectivity of the pieces that is glued. The coefficient of each
operator is any `L∞` class of the given function.

The right inverse is spliced from those of the pieces. Cut `f ∈ Lᵖ` into its parts `f₁` and `f₂` on
`(-∞, 0)` and `[0, ∞)`, solve `D_{A₁} w₁ = f₁(· - R)` and `D_{A₂} w₂ = f₂(· + R)`, translate the
solutions back to the two ends of the neck and multiply them by smooth cutoffs `β₁`, `β₂` equal to
`1` on the two half-lines and supported in `(-∞, R/2]` and `[-R/2, ∞)`. For
`Q_R f = β₁ w₁(· + R) + β₂ w₂(· - R)` the error `D_{A_R} Q_R f - f` is the sum, over the two pieces,
of `βᵢ' wᵢ` and `βᵢ (A_R - Aᵢ) wᵢ` (translated). The first is small because `|βᵢ'| ≤ C / R`, the
second because on the support of `βᵢ` the coefficients `A_R` and the translated `Aᵢ` differ only
where both are close to `A`. So `D_{A_R} Q_R` is within `1 / 2` of the identity for large `R`, and
inverting it by its Neumann series corrects `Q_R` to an exact right inverse
(`ContinuousLinearMap.exists_rightInverse_of_norm_comp_sub_id_lt`).

In Morse theory the pieces are the linearized operators along the two components of a broken
trajectory, which are onto by transversality, and the uniformly bounded right inverse of the glued
operator is the linear input of the Newton iteration that glues broken trajectories.

## Main declarations

* `TauCeti.gluedCoeff`: the coefficient of two operators glued along a neck of length `2 R`.
* `TauCeti.WeakDerivStep.exists_forall_ge_exists_rightInverse_trajectoryOperator_gluedCoeff`: the
  glued operator has right inverses bounded uniformly in the neck length.

## References

* M. Schwarz, *Morse Homology*, Progress in Mathematics 111, Birkhäuser, 1993, Chapter 2 (the
  gluing of trajectories and the uniform right inverses of the glued linearized operators).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Chapter 10
  (gluing: pregluing, uniformly bounded right inverses and Newton iteration).
-/

public section

noncomputable section

open Filter MeasureTheory Set TopologicalSpace Topology
open scoped ENNReal ContDiff

namespace TauCeti

/-- **The glued coefficient.** The coefficient obtained by gluing the positive end of `A₁` to the
negative end of `A₂` along a neck of length `2 R`: it is `A₁` translated by `-R` on `(-∞, 0)` and
`A₂` translated by `R` on `[0, ∞)`. -/
def gluedCoeff {X : Type*} (A₁ A₂ : ℝ → X) (R s : ℝ) : X :=
  if s < 0 then A₁ (s + R) else A₂ (s - R)

theorem gluedCoeff_of_neg {X : Type*} (A₁ A₂ : ℝ → X) (R : ℝ) {s : ℝ} (hs : s < 0) :
    gluedCoeff A₁ A₂ R s = A₁ (s + R) := by
  simp [gluedCoeff, hs]

theorem gluedCoeff_of_nonneg {X : Type*} (A₁ A₂ : ℝ → X) (R : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    gluedCoeff A₁ A₂ R s = A₂ (s - R) := by
  simp [gluedCoeff, not_lt.2 hs]

namespace WeakDerivStep

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ℝ≥0∞} [Fact (1 ≤ p)]

local instance gluing_isAddHaarMeasure :
    (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)).IsAddHaarMeasure := by
  rw [Opens.coe_top, Measure.restrict_univ]
  infer_instance

/- Instance search through the closed-graph structure of the Sobolev space is expensive, and these
instances are needed in every statement below; naming them once keeps elaboration within budget. -/

/-- The normed group structure of `W^{1,p}(ℝ, F)`, named once for the statements below. -/
local instance gluingNormedAddCommGroup [CompleteSpace F] :
    NormedAddCommGroup (WeakDerivStep volume ⊤ p
      (ContinuousLinearMap.id ℝ (Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))) :=
  inferInstance

/-- The normed space structure of `W^{1,p}(ℝ, F)`, named once for the statements below. -/
local instance gluingNormedSpace [CompleteSpace F] :
    NormedSpace ℝ (WeakDerivStep volume ⊤ p
      (ContinuousLinearMap.id ℝ (Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))) :=
  inferInstance

/-- The normed group of bounded operators `Lᵖ(ℝ, F) → W^{1,p}(ℝ, F)`, named once for the
statements below. -/
local instance gluingNormedAddCommGroupCLM [CompleteSpace F] :
    NormedAddCommGroup (Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) →L[ℝ]
      WeakDerivStep volume ⊤ p
        (ContinuousLinearMap.id ℝ (Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))) :=
  inferInstance

/-! ### Cutoffs -/

/-- The cutoff `s ↦ ψ (1 + a s)` built from the smooth transition `ψ`. -/
private def neckCutoff (a s : ℝ) : ℝ :=
  Real.smoothTransition (1 + a * s)

private theorem contDiffOn_neckCutoff (a : ℝ) :
    ContDiffOn ℝ ∞ (neckCutoff a) ((⊤ : Opens ℝ) : Set ℝ) :=
  (Real.smoothTransition.contDiff.comp (by fun_prop)).contDiffOn

private theorem abs_neckCutoff_le_one (a s : ℝ) : |neckCutoff a s| ≤ 1 :=
  Real.smoothTransition.abs_le_one _

private theorem hasDerivAt_neckCutoff (a s : ℝ) :
    HasDerivAt (neckCutoff a) (deriv Real.smoothTransition (1 + a * s) * a) s := by
  unfold neckCutoff
  simpa using (((hasDerivAt_id s).const_mul a).const_add 1).smoothTransition

private theorem abs_deriv_neckCutoff_le {L : ℝ}
    (hL : ∀ t, ‖deriv Real.smoothTransition t‖ ≤ L) (a s : ℝ) :
    |deriv (neckCutoff a) s| ≤ |a| * L := by
  rw [(hasDerivAt_neckCutoff a s).deriv, abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_left (hL _) (abs_nonneg a)

private theorem exists_norm_neckCutoff_le (a : ℝ) :
    ∃ C, ∀ x ∈ (⊤ : Opens ℝ), ‖neckCutoff a x‖ ≤ C :=
  ⟨1, fun x _ ↦ abs_neckCutoff_le_one a x⟩

private theorem exists_norm_fderiv_neckCutoff_le (a : ℝ) :
    ∃ C, ∀ x ∈ (⊤ : Opens ℝ), ‖fderiv ℝ (neckCutoff a) x‖ ≤ C := by
  obtain ⟨L, hL⟩ := Real.smoothTransition.exists_forall_norm_deriv_le
  exact ⟨|a| * L, fun x _ ↦ by
    rw [← norm_deriv_eq_norm_fderiv]
    exact abs_deriv_neckCutoff_le hL a x⟩

private theorem neckCutoff_eq_one {a s : ℝ} (h : 0 ≤ a * s) : neckCutoff a s = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

private theorem neckCutoff_left_eq_one {R : ℝ} (hR : 0 < R) :
    ∀ s ∈ Iio (0 : ℝ), neckCutoff (-(2 / R)) s = 1 := fun s hs ↦
  neckCutoff_eq_one (mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.2 (by positivity))
    (mem_Iio.1 hs).le)

private theorem neckCutoff_right_eq_one {R : ℝ} (hR : 0 < R) :
    ∀ s ∈ (Iio (0 : ℝ))ᶜ, neckCutoff (2 / R) s = 1 := fun s hs ↦
  neckCutoff_eq_one (mul_nonneg (by positivity) (not_lt.1 hs))

private theorem neckCutoff_eq_zero {a s : ℝ} (h : 1 + a * s ≤ 0) : neckCutoff a s = 0 :=
  Real.smoothTransition.zero_of_nonpos h

/-! ### The error on the neck -/

/-- Two operators within `ε` of `A` are within `2 ε` of each other. -/
private theorem norm_sub_le_of_dist_lt {A X Y : F →L[ℝ] F} {ε : ℝ} (hX : dist X A < ε)
    (hY : dist Y A < ε) : ‖X - Y‖ ≤ 2 * ε := by
  rw [← dist_eq_norm]
  linarith [dist_triangle_right X Y A]

/-- The pointwise error of one piece: if the cutoff vanishes at `s` or the coefficients there are
within `2 ε`, the error weight is at most `d + 2 ε`, for a bound `d` on the derivative. -/
private theorem abs_deriv_add_abs_mul_le {a s d ε : ℝ} {X : F →L[ℝ] F} (hε : 0 ≤ ε)
    (hd : |deriv (neckCutoff a) s| ≤ d) (h : neckCutoff a s = 0 ∨ ‖X‖ ≤ 2 * ε) :
    |deriv (neckCutoff a) s| + |neckCutoff a s| * ‖X‖ ≤ d + 2 * ε := by
  rcases h with h | h
  · rw [h, abs_zero, zero_mul, add_zero]
    linarith
  · have := mul_le_mul (abs_neckCutoff_le_one a s) h (norm_nonneg X) zero_le_one
    linarith

/-- The error weight of the left piece is small: on `(-∞, 0)` the glued coefficient is `A₁(· + R)`
exactly, on `[0, R/2)` both coefficients are close to `A`, and beyond `R/2` the cutoff vanishes. -/
private theorem ae_neck_bound_left {A : F →L[ℝ] F} {A₁ A₂ : ℝ → F →L[ℝ] F} {ε T₁ T₂ R L : ℝ}
    (hε : 0 ≤ ε) (hT₁ : ∀ s ≥ T₁, dist (A₁ s) A < ε) (hT₂ : ∀ s ≤ T₂, dist (A₂ s) A < ε)
    (hR : 0 < R) (hRT₁ : 2 * T₁ ≤ R) (hRT₂ : -2 * T₂ ≤ R)
    (hL : ∀ t, ‖deriv Real.smoothTransition t‖ ≤ L)
    {AL : Lp (F →L[ℝ] F) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] gluedCoeff A₁ A₂ R) :
    ∀ᵐ s ∂volume.restrict ((⊤ : Opens ℝ) : Set ℝ),
      |deriv (neckCutoff (-(2 / R))) s| + |neckCutoff (-(2 / R)) s| * ‖AL s - A₁ (s + R)‖ ≤
        2 / R * L + 2 * ε := by
  filter_upwards [hAL] with s hs
  have hd := abs_deriv_neckCutoff_le hL (-(2 / R)) s
  rw [abs_neg, abs_of_pos (show (0 : ℝ) < 2 / R by positivity)] at hd
  refine abs_deriv_add_abs_mul_le hε hd ?_
  rw [hs]
  rcases lt_or_ge s 0 with h0 | h0
  · right
    rw [gluedCoeff_of_neg _ _ _ h0, sub_self, norm_zero]
    positivity
  rcases lt_or_ge s (R / 2) with hR2 | hR2
  · right
    rw [gluedCoeff_of_nonneg _ _ _ h0]
    exact norm_sub_le_of_dist_lt (hT₂ _ (by linarith)) (hT₁ _ (by linarith))
  · left
    refine neckCutoff_eq_zero ?_
    rw [neg_mul, div_mul_eq_mul_div, ← sub_eq_add_neg, sub_nonpos, le_div_iff₀ hR]
    linarith

/-- The error weight of the right piece is small: on `[0, ∞)` the glued coefficient is `A₂(· - R)`
exactly, on `(-R/2, 0)` both coefficients are close to `A`, and below `-R/2` the cutoff
vanishes. -/
private theorem ae_neck_bound_right {A : F →L[ℝ] F} {A₁ A₂ : ℝ → F →L[ℝ] F} {ε T₁ T₂ R L : ℝ}
    (hε : 0 ≤ ε) (hT₁ : ∀ s ≥ T₁, dist (A₁ s) A < ε) (hT₂ : ∀ s ≤ T₂, dist (A₂ s) A < ε)
    (hR : 0 < R) (hRT₁ : 2 * T₁ ≤ R) (hRT₂ : -2 * T₂ ≤ R)
    (hL : ∀ t, ‖deriv Real.smoothTransition t‖ ≤ L)
    {AL : Lp (F →L[ℝ] F) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] gluedCoeff A₁ A₂ R) :
    ∀ᵐ s ∂volume.restrict ((⊤ : Opens ℝ) : Set ℝ),
      |deriv (neckCutoff (2 / R)) s| + |neckCutoff (2 / R) s| * ‖AL s - A₂ (s + -R)‖ ≤
        2 / R * L + 2 * ε := by
  filter_upwards [hAL] with s hs
  have hd := abs_deriv_neckCutoff_le hL (2 / R) s
  rw [abs_of_pos (show (0 : ℝ) < 2 / R by positivity)] at hd
  refine abs_deriv_add_abs_mul_le hε hd ?_
  rw [hs]
  rcases le_or_gt 0 s with h0 | h0
  · right
    rw [gluedCoeff_of_nonneg _ _ _ h0, ← sub_eq_add_neg, sub_self, norm_zero]
    positivity
  rcases lt_or_ge (-(R / 2)) s with hR2 | hR2
  · right
    rw [gluedCoeff_of_neg _ _ _ h0]
    exact norm_sub_le_of_dist_lt (hT₁ _ (by linarith)) (hT₂ _ (by linarith))
  · left
    refine neckCutoff_eq_zero ?_
    rw [div_mul_eq_mul_div, ← le_neg_iff_add_nonpos_left, div_le_iff₀ hR]
    linarith

variable [CompleteSpace F]

/-! ### The trajectory operator on a cut-off translate -/

omit [CompleteSpace F] in
/-- The pointwise algebra of the trajectory operator on a cut-off field: with `b = β s`, `φ = Dβ s`,
the weak derivative `W` and value `y` of the field, the coefficient `M` of the operator and `N` of
the piece, the error is `(φ 1) y + b (M - N) y`. -/
private theorem norm_smul_add_smulRight_sub_le (b : ℝ) (φ : ℝ →L[ℝ] ℝ) (W : ℝ →L[ℝ] F) (y : F)
    (M N : F →L[ℝ] F) :
    ‖(b • W + φ.smulRight y) 1 + M (b • y) - b • (W 1 + N y)‖ ≤
      (|φ 1| + |b| * ‖M - N‖) * ‖y‖ := by
  have key : (b • W + φ.smulRight y) 1 + M (b • y) - b • (W 1 + N y) =
      φ 1 • y + b • ((M - N) y) := by
    rw [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, map_smul, sub_apply,
      smul_add, smul_sub]
    abel
  rw [key]
  calc ‖φ 1 • y + b • ((M - N) y)‖ ≤ |φ 1| * ‖y‖ + |b| * (‖M - N‖ * ‖y‖) := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
        gcongr
        exact (M - N).le_opNorm y
    _ = (|φ 1| + |b| * ‖M - N‖) * ‖y‖ := by ring

/-- On a cut-off translate `β w(· + c)`, the trajectory operator with coefficient `AL` differs from
`β (D_B w)(· + c)` by `β' w(· + c) + β (AL - B(· + c)) w(· + c)`. So if
`|β'| + |β| ‖AL - B(· + c)‖ ≤ δ` almost everywhere, the difference is at most `δ ‖w‖`. -/
private theorem norm_trajectoryOperator_smulLeftCLM_translateLIE_sub_le {β : ℝ → ℝ}
    (hβ : ContDiffOn ℝ ∞ β ((⊤ : Opens ℝ) : Set ℝ)) (h₀ : ∃ C, ∀ x ∈ (⊤ : Opens ℝ), ‖β x‖ ≤ C)
    (h₁ : ∃ C, ∀ x ∈ (⊤ : Opens ℝ), ‖fderiv ℝ β x‖ ≤ C) (c : ℝ) {B : ℝ → F →L[ℝ] F}
    {AL BL : Lp (F →L[ℝ] F) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hBL : BL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] B) {δ : ℝ} (hδ : 0 ≤ δ)
    (hδB : ∀ᵐ s ∂volume.restrict ((⊤ : Opens ℝ) : Set ℝ),
      |deriv β s| + |β s| * ‖AL s - B (s + c)‖ ≤ δ)
    (w : WeakDerivStep volume ⊤ p
      (ContinuousLinearMap.id ℝ (Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))))
    {g : Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hg : ∀ᵐ s ∂volume.restrict ((⊤ : Opens ℝ) : Set ℝ),
      β s • trajectoryOperator BL w (s + c) = g s) :
    ‖trajectoryOperator AL (smulLeftCLM β hβ h₀ h₁ (fun _ _ ↦ rfl) (translateLIE c w)) - g‖ ≤
      δ * ‖w‖ := by
  have hq := (measurePreserving_add_right (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))
    c).quasiMeasurePreserving
  refine (Lp.norm_le_mul_norm_of_ae_le_mul (c := δ) (g := prev (ContinuousLinearMap.id ℝ
    (Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) (translateLIE c w)) ?_).trans ?_
  · filter_upwards [Lp.coeFn_sub (trajectoryOperator AL
        (smulLeftCLM β hβ h₀ h₁ (fun _ _ ↦ rfl) (translateLIE c w))) g,
      trajectoryOperator_apply_ae AL (smulLeftCLM β hβ h₀ h₁ (fun _ _ ↦ rfl) (translateLIE c w)),
      prev_smulLeftCLM_ae hβ h₀ h₁ (fun _ _ ↦ rfl) (translateLIE c w),
      weakFDeriv_smulLeftCLM_ae hβ h₀ h₁ (fun _ _ ↦ rfl) (translateLIE c w),
      prev_translateLIE_ae c w,
      weakFDeriv_translateLIE_ae c w, hq.tendsto_ae.eventually (trajectoryOperator_apply_ae BL w),
      hq.tendsto_ae.eventually hBL, hg, hδB] with s hsub hT hp hd hpt hdt hD hB hgs hδs
    -- `rw` times out matching these coercions; `simp only` rewrites them directly.
    simp only [hsub, Pi.sub_apply, hT, hd, ContinuousLinearMap.id_apply, hp, hpt, hdt]
    rw [← hgs, hD, hB]
    refine (norm_smul_add_smulRight_sub_le _ _ _ _ _ _).trans ?_
    rw [fderiv_apply_one_eq_deriv]
    exact mul_le_mul_of_nonneg_right hδs (norm_nonneg _)
  · gcongr
    exact (norm_prev_le _ _).trans_eq (LinearIsometryEquiv.norm_map _ _)

/-- One piece of the spliced right inverse: cut along `S`, translate by `-c`, apply `Q`,
translate back by `c` and multiply by the cutoff `β`. -/
private def splicedPiece {β : ℝ → ℝ} (hβ : ContDiffOn ℝ ∞ β ((⊤ : Opens ℝ) : Set ℝ))
    (h₀ : ∃ C, ∀ x ∈ (⊤ : Opens ℝ), ‖β x‖ ≤ C)
    (h₁ : ∃ C, ∀ x ∈ (⊤ : Opens ℝ), ‖fderiv ℝ β x‖ ≤ C) (c : ℝ) (S : Set ℝ)
    (hS : MeasurableSet S)
    (Q : Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) →L[ℝ] WeakDerivStep volume ⊤ p
      (ContinuousLinearMap.id ℝ (Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))) :
    Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) →L[ℝ] WeakDerivStep volume ⊤ p
      (ContinuousLinearMap.id ℝ (Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) :=
  (smulLeftCLM β hβ h₀ h₁ (fun _ _ ↦ rfl)).comp
    ((translateLIE c : WeakDerivStep volume ⊤ p
      (ContinuousLinearMap.id ℝ (Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) ≃ₗᵢ[ℝ] _
      ).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (Q.comp (((volume.restrict ((⊤ : Opens ℝ) : Set ℝ)).translateLp p (-c) :
      Lp F p _ ≃ₗᵢ[ℝ] Lp F p _).toContinuousLinearEquiv.toContinuousLinearMap.comp
        (Lp.multiplicationOperator (linftyIndicator _ ℝ S hS)))))

private theorem splicedPiece_apply {β : ℝ → ℝ} (hβ : ContDiffOn ℝ ∞ β ((⊤ : Opens ℝ) : Set ℝ))
    (h₀ : ∃ C, ∀ x ∈ (⊤ : Opens ℝ), ‖β x‖ ≤ C)
    (h₁ : ∃ C, ∀ x ∈ (⊤ : Opens ℝ), ‖fderiv ℝ β x‖ ≤ C) (c : ℝ) (S : Set ℝ)
    (hS : MeasurableSet S)
    (Q : Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) →L[ℝ] WeakDerivStep volume ⊤ p
      (ContinuousLinearMap.id ℝ (Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))))
    (f : Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) :
    splicedPiece hβ h₀ h₁ c S hS Q f = smulLeftCLM β hβ h₀ h₁ (fun _ _ ↦ rfl) (translateLIE c
      (Q ((volume.restrict ((⊤ : Opens ℝ) : Set ℝ)).translateLp p (-c)
        (Lp.multiplicationOperator (linftyIndicator _ ℝ S hS) f)))) :=
  rfl

private theorem norm_splicedPiece_apply_le {β : ℝ → ℝ}
    (hβ : ContDiffOn ℝ ∞ β ((⊤ : Opens ℝ) : Set ℝ)) (h₀ : ∃ C, ∀ x ∈ (⊤ : Opens ℝ), ‖β x‖ ≤ C)
    (h₁ : ∃ C, ∀ x ∈ (⊤ : Opens ℝ), ‖fderiv ℝ β x‖ ≤ C) (c : ℝ) (S : Set ℝ)
    (hS : MeasurableSet S)
    (Q : Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) →L[ℝ] WeakDerivStep volume ⊤ p
      (ContinuousLinearMap.id ℝ (Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))))
    {C₀ C₁ : ℝ} (hC₀ : ∀ x ∈ (⊤ : Opens ℝ), ‖β x‖ ≤ C₀)
    (hC₁ : ∀ x ∈ (⊤ : Opens ℝ), ‖fderiv ℝ β x‖ ≤ C₁) (hC : 0 ≤ √2 * C₀ + C₁)
    (f : Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) :
    ‖splicedPiece hβ h₀ h₁ c S hS Q f‖ ≤ (√2 * C₀ + C₁) * ‖Q‖ * ‖f‖ := by
  rw [splicedPiece_apply, mul_assoc]
  refine (norm_smulLeftCLM_apply_le hβ h₀ h₁ hC₀ hC₁ _).trans (mul_le_mul_of_nonneg_left ?_ hC)
  rw [LinearIsometryEquiv.norm_map]
  calc _ ≤ ‖Q‖ * ‖(volume.restrict ((⊤ : Opens ℝ) : Set ℝ)).translateLp p (-c)
          (Lp.multiplicationOperator (linftyIndicator _ ℝ S hS) f)‖ :=
        Q.le_opNorm _
    _ = ‖Q‖ * ‖Lp.multiplicationOperator (linftyIndicator _ ℝ S hS) f‖ := by
        rw [LinearIsometryEquiv.norm_map]
    _ ≤ ‖Q‖ * ‖f‖ := by
        gcongr
        exact Lp.norm_multiplicationOperator_linftyIndicator_apply_le hS f

/-- The spliced approximate right inverse of the operator glued along a neck of length `2 R`. -/
private def splicedInverse (R : ℝ)
    (Q₁ Q₂ : Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) →L[ℝ] WeakDerivStep volume ⊤ p
      (ContinuousLinearMap.id ℝ (Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))) :
    Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) →L[ℝ] WeakDerivStep volume ⊤ p
      (ContinuousLinearMap.id ℝ (Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) :=
  splicedPiece (contDiffOn_neckCutoff (-(2 / R))) (exists_norm_neckCutoff_le _)
      (exists_norm_fderiv_neckCutoff_le _) R (Iio 0) measurableSet_Iio Q₁ +
    splicedPiece (contDiffOn_neckCutoff (2 / R)) (exists_norm_neckCutoff_le _)
      (exists_norm_fderiv_neckCutoff_le _) (-R) (Iio 0)ᶜ measurableSet_Iio.compl Q₂

private theorem splicedInverse_apply (R : ℝ)
    (Q₁ Q₂ : Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) →L[ℝ] WeakDerivStep volume ⊤ p
      (ContinuousLinearMap.id ℝ (Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))))
    (f : Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) :
    splicedInverse R Q₁ Q₂ f =
      splicedPiece (contDiffOn_neckCutoff (-(2 / R))) (exists_norm_neckCutoff_le _)
          (exists_norm_fderiv_neckCutoff_le _) R (Iio 0) measurableSet_Iio Q₁ f +
        splicedPiece (contDiffOn_neckCutoff (2 / R)) (exists_norm_neckCutoff_le _)
          (exists_norm_fderiv_neckCutoff_le _) (-R) (Iio 0)ᶜ measurableSet_Iio.compl Q₂ f :=
  rfl

private theorem trajectoryOperator_splicedInverse_apply (R : ℝ)
    (AL : Lp (F →L[ℝ] F) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (Q₁ Q₂ : Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) →L[ℝ] WeakDerivStep volume ⊤ p
      (ContinuousLinearMap.id ℝ (Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))))
    (f : Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) :
    trajectoryOperator AL (splicedInverse R Q₁ Q₂ f) =
      trajectoryOperator AL (splicedPiece (contDiffOn_neckCutoff (-(2 / R)))
          (exists_norm_neckCutoff_le _) (exists_norm_fderiv_neckCutoff_le _) R (Iio 0)
          measurableSet_Iio Q₁ f) +
        trajectoryOperator AL (splicedPiece (contDiffOn_neckCutoff (2 / R))
          (exists_norm_neckCutoff_le _) (exists_norm_fderiv_neckCutoff_le _) (-R) (Iio 0)ᶜ
          measurableSet_Iio.compl Q₂ f) := by
  rw [splicedInverse_apply, map_add]

private theorem norm_splicedInverse_apply_le {R L : ℝ} (hR : 0 < R)
    (hL : ∀ t, ‖deriv Real.smoothTransition t‖ ≤ L) (hRL : 2 / R * L ≤ 1)
    (Q₁ Q₂ : Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) →L[ℝ] WeakDerivStep volume ⊤ p
      (ContinuousLinearMap.id ℝ (Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))))
    (f : Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) :
    ‖splicedInverse R Q₁ Q₂ f‖ ≤ (√2 + 1) * (‖Q₁‖ + ‖Q₂‖) * ‖f‖ := by
  have hd (a : ℝ) (ha : |a| = 2 / R) (x : ℝ) (_ : x ∈ (⊤ : Opens ℝ)) :
      ‖fderiv ℝ (neckCutoff a) x‖ ≤ 1 := by
    rw [← norm_deriv_eq_norm_fderiv]
    exact (abs_deriv_neckCutoff_le hL a x).trans (by rwa [ha])
  have h₁ := norm_splicedPiece_apply_le (contDiffOn_neckCutoff (-(2 / R)))
    (exists_norm_neckCutoff_le _) (exists_norm_fderiv_neckCutoff_le _) R (Iio 0)
    measurableSet_Iio Q₁ (fun x _ ↦ abs_neckCutoff_le_one _ x)
    (hd _ (by rw [abs_neg, abs_of_pos (by positivity)])) (by positivity) f
  have h₂ := norm_splicedPiece_apply_le (contDiffOn_neckCutoff (2 / R))
    (exists_norm_neckCutoff_le _) (exists_norm_fderiv_neckCutoff_le _) (-R) (Iio 0)ᶜ
    measurableSet_Iio.compl Q₂ (fun x _ ↦ abs_neckCutoff_le_one _ x)
    (hd _ (abs_of_pos (by positivity))) (by positivity) f
  rw [splicedInverse_apply]
  refine (norm_add_le _ _).trans ((add_le_add h₁ h₂).trans (le_of_eq ?_))
  ring

/-- **One piece of the spliced right inverse.** Solve `D_B w = (𝟙_S f)(· - c)` by a right inverse
`Q` of `D_B`, translate back by `c` and cut off by `β`, equal to `1` on `S`. Under the bound of
`norm_trajectoryOperator_smulLeftCLM_translateLIE_sub_le`, the trajectory operator with coefficient
`AL` sends the result to `𝟙_S f` up to an error at most `δ ‖Q‖ ‖f‖`. -/
private theorem norm_trajectoryOperator_piece_sub_le {β : ℝ → ℝ}
    (hβ : ContDiffOn ℝ ∞ β ((⊤ : Opens ℝ) : Set ℝ)) (h₀ : ∃ C, ∀ x ∈ (⊤ : Opens ℝ), ‖β x‖ ≤ C)
    (h₁ : ∃ C, ∀ x ∈ (⊤ : Opens ℝ), ‖fderiv ℝ β x‖ ≤ C) (c : ℝ) {S : Set ℝ}
    (hS : MeasurableSet S) (hβS : ∀ s ∈ S, β s = 1) {B : ℝ → F →L[ℝ] F}
    {AL BL : Lp (F →L[ℝ] F) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hBL : BL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] B) {δ : ℝ} (hδ : 0 ≤ δ)
    (hδB : ∀ᵐ s ∂volume.restrict ((⊤ : Opens ℝ) : Set ℝ),
      |deriv β s| + |β s| * ‖AL s - B (s + c)‖ ≤ δ)
    (Q : Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) →L[ℝ] WeakDerivStep volume ⊤ p
      (ContinuousLinearMap.id ℝ (Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))))
    (hQ : (trajectoryOperator BL).comp Q = ContinuousLinearMap.id ℝ _)
    (f : Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) :
    ‖trajectoryOperator AL (splicedPiece hβ h₀ h₁ c S hS Q f) -
        Lp.multiplicationOperator (linftyIndicator _ ℝ S hS) f‖ ≤
      δ * ‖Q‖ * ‖f‖ := by
  rw [splicedPiece_apply]
  have hDw : trajectoryOperator BL
        (Q ((volume.restrict ((⊤ : Opens ℝ) : Set ℝ)).translateLp p (-c)
          (Lp.multiplicationOperator (linftyIndicator _ ℝ S hS) f))) =
      (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)).translateLp p (-c)
        (Lp.multiplicationOperator (linftyIndicator _ ℝ S hS) f) :=
    (ContinuousLinearMap.ext_iff.1 hQ _).trans (ContinuousLinearMap.id_apply _)
  have hg : ∀ᵐ s ∂volume.restrict ((⊤ : Opens ℝ) : Set ℝ),
      β s • trajectoryOperator BL
        (Q ((volume.restrict ((⊤ : Opens ℝ) : Set ℝ)).translateLp p (-c)
          (Lp.multiplicationOperator (linftyIndicator _ ℝ S hS) f)))
        (s + c) = Lp.multiplicationOperator (linftyIndicator _ ℝ S hS) f s := by
    have hq := (measurePreserving_add_right (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))
      c).quasiMeasurePreserving
    filter_upwards [hq.tendsto_ae.eventually
        (Measure.coeFn_translateLp (-c) (Lp.multiplicationOperator (linftyIndicator _ ℝ S hS) f)),
      Lp.multiplicationOperator_linftyIndicator_ae hS f] with s hs hcut
    rw [hDw, hs, Function.comp_apply, add_neg_cancel_right, hcut]
    by_cases hsS : s ∈ S
    · rw [hβS s hsS, one_smul]
    · simp [indicator_of_notMem hsS]
  refine (norm_trajectoryOperator_smulLeftCLM_translateLIE_sub_le hβ h₀ h₁ c hBL hδ hδB _
    hg).trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ((Q.le_opNorm _).trans ?_) hδ
  rw [LinearIsometryEquiv.norm_map]
  exact mul_le_mul_of_nonneg_left
    (Lp.norm_multiplicationOperator_linftyIndicator_apply_le hS f) (norm_nonneg Q)

/-- **The spliced right inverse is approximate.** For a neck long enough that the coefficients are
within `ε` of their common limit beyond `R / 2`, the spliced inverse `Q_R` satisfies
`‖D_{A_R} Q_R f - f‖ ≤ (2 L / R + 2 ε) (‖Q₁‖ + ‖Q₂‖) ‖f‖`, where `L` bounds the derivative of the
smooth transition. -/
private theorem norm_trajectoryOperator_splicedInverse_sub_le {A : F →L[ℝ] F}
    {A₁ A₂ : ℝ → F →L[ℝ] F} {ε T₁ T₂ R L : ℝ} (hε : 0 ≤ ε)
    (hT₁ : ∀ s ≥ T₁, dist (A₁ s) A < ε) (hT₂ : ∀ s ≤ T₂, dist (A₂ s) A < ε) (hR : 0 < R)
    (hRT₁ : 2 * T₁ ≤ R) (hRT₂ : -2 * T₂ ≤ R) (hL : ∀ t, ‖deriv Real.smoothTransition t‖ ≤ L)
    {A₁L A₂L AL : Lp (F →L[ℝ] F) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hA₁L : A₁L =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A₁)
    (hA₂L : A₂L =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A₂)
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] gluedCoeff A₁ A₂ R)
    {Q₁ Q₂ : Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) →L[ℝ] WeakDerivStep volume ⊤ p
      (ContinuousLinearMap.id ℝ (Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))}
    (hQ₁ : (trajectoryOperator A₁L).comp Q₁ = ContinuousLinearMap.id ℝ _)
    (hQ₂ : (trajectoryOperator A₂L).comp Q₂ = ContinuousLinearMap.id ℝ _)
    (f : Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) :
    ‖trajectoryOperator AL (splicedInverse R Q₁ Q₂ f) - f‖ ≤
      (2 / R * L + 2 * ε) * (‖Q₁‖ + ‖Q₂‖) * ‖f‖ := by
  have hδ0 : 0 ≤ 2 / R * L + 2 * ε :=
    add_nonneg (mul_nonneg (by positivity) ((norm_nonneg _).trans (hL 0))) (by positivity)
  have e₁ := norm_trajectoryOperator_piece_sub_le (contDiffOn_neckCutoff _)
    (exists_norm_neckCutoff_le _) (exists_norm_fderiv_neckCutoff_le _) R measurableSet_Iio
    (neckCutoff_left_eq_one hR) hA₁L hδ0 (ae_neck_bound_left hε hT₁ hT₂ hR hRT₁ hRT₂ hL hAL)
    Q₁ hQ₁ f
  have e₂ := norm_trajectoryOperator_piece_sub_le (contDiffOn_neckCutoff _)
    (exists_norm_neckCutoff_le _) (exists_norm_fderiv_neckCutoff_le _) (-R)
    measurableSet_Iio.compl (neckCutoff_right_eq_one hR) hA₂L hδ0
    (ae_neck_bound_right hε hT₁ hT₂ hR hRT₁ hRT₂ hL hAL) Q₂ hQ₂ f
  have hsplit := Lp.multiplicationOperator_linftyIndicator_add_compl (s := Iio (0 : ℝ))
    measurableSet_Iio f
  rw [trajectoryOperator_splicedInverse_apply]
  -- Split `f` as `𝟙_{(-∞, 0)} f + 𝟙_{[0, ∞)} f` and estimate the two pieces.
  refine (norm_sub_le_norm_sub_add_norm_sub _
    (Lp.multiplicationOperator (linftyIndicator _ ℝ (Iio 0) measurableSet_Iio) f +
      Lp.multiplicationOperator (linftyIndicator _ ℝ (Iio 0)ᶜ measurableSet_Iio.compl) f)
    f).trans ?_
  rw [sub_eq_zero.2 hsplit, norm_zero, add_zero, add_sub_add_comm]
  refine (norm_add_le _ _).trans ((add_le_add e₁ e₂).trans (le_of_eq ?_))
  rw [← add_mul, ← mul_add]

/-- **Correcting the spliced right inverse.** If the spliced inverse is within `1 / 2` of a right
inverse of `D_{A_R}`, then `D_{A_R}` has a right inverse of norm at most
`2 (√2 + 1) (‖Q₁‖ + ‖Q₂‖)`. -/
private theorem exists_rightInverse_of_splicedInverse {R L : ℝ} (hR : 0 < R)
    (hL : ∀ t, ‖deriv Real.smoothTransition t‖ ≤ L) (hRL : 2 / R * L ≤ 1)
    (AL : Lp (F →L[ℝ] F) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (Q₁ Q₂ : Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) →L[ℝ] WeakDerivStep volume ⊤ p
      (ContinuousLinearMap.id ℝ (Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))))
    (happrox : ∀ f, ‖trajectoryOperator AL (splicedInverse R Q₁ Q₂ f) - f‖ ≤ 1 / 2 * ‖f‖) :
    ∃ Q : Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) →L[ℝ] WeakDerivStep volume ⊤ p
      (ContinuousLinearMap.id ℝ (Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))),
      (trajectoryOperator AL).comp Q = ContinuousLinearMap.id ℝ _ ∧
      ‖Q‖ ≤ 2 * ((√2 + 1) * (‖Q₁‖ + ‖Q₂‖)) := by
  have hE : ‖(trajectoryOperator AL).comp (splicedInverse R Q₁ Q₂) -
      ContinuousLinearMap.id ℝ _‖ ≤ 1 / 2 :=
    ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun f ↦ by
      rw [sub_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
      exact happrox f
  obtain ⟨Q, hQ, hQn⟩ := (trajectoryOperator AL).exists_rightInverse_of_norm_comp_sub_id_lt
    (splicedInverse R Q₁ Q₂) (by linarith)
  refine ⟨Q, hQ, hQn.trans ?_⟩
  have hQ₀ : ‖splicedInverse R Q₁ Q₂‖ ≤ (√2 + 1) * (‖Q₁‖ + ‖Q₂‖) :=
    ContinuousLinearMap.opNorm_le_bound _ (by positivity)
      (norm_splicedInverse_apply_le hR hL hRL Q₁ Q₂)
  have hinv : (1 - ‖(trajectoryOperator AL).comp (splicedInverse R Q₁ Q₂) -
      ContinuousLinearMap.id ℝ _‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  calc _ ≤ ((√2 + 1) * (‖Q₁‖ + ‖Q₂‖)) * 2 :=
        mul_le_mul hQ₀ hinv (inv_nonneg.2 (by linarith)) (by positivity)
    _ = 2 * ((√2 + 1) * (‖Q₁‖ + ‖Q₂‖)) := by ring

/-! ### The glued operator -/

/-- **Gluing trajectory operators with surjective pieces.** Let `A₁` and `A₂` be coefficients with
`A₁(s) → A` as `s → +∞` and `A₂(s) → A` as `s → -∞`, and suppose that the trajectory operators
`D_{A₁}` and `D_{A₂}` from `W^{1,p}(ℝ, F)` to `Lᵖ(ℝ, F)` have bounded linear right inverses
`Q₁` and `Q₂`. Then there are `C` and `R₀` such that for every `R ≥ R₀` the trajectory operator of
the glued coefficient `TauCeti.gluedCoeff A₁ A₂ R` (neck length `2 R`) has a bounded linear right
inverse of norm at most `C`. The coefficients of the operators are any `L∞` classes of the given
functions. -/
theorem exists_forall_ge_exists_rightInverse_trajectoryOperator_gluedCoeff {A : F →L[ℝ] F}
    {A₁ A₂ : ℝ → F →L[ℝ] F} (h₁ : Tendsto A₁ atTop (𝓝 A)) (h₂ : Tendsto A₂ atBot (𝓝 A))
    {A₁L A₂L : Lp (F →L[ℝ] F) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hA₁L : A₁L =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A₁)
    (hA₂L : A₂L =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A₂)
    (Q₁ Q₂ : Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) →L[ℝ] WeakDerivStep volume ⊤ p
      (ContinuousLinearMap.id ℝ (Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))))
    (hQ₁ : (trajectoryOperator A₁L).comp Q₁ = ContinuousLinearMap.id ℝ _)
    (hQ₂ : (trajectoryOperator A₂L).comp Q₂ = ContinuousLinearMap.id ℝ _) :
    ∃ C R₀ : ℝ, ∀ R ≥ R₀, ∀ AL : Lp (F →L[ℝ] F) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)),
      AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] gluedCoeff A₁ A₂ R →
        ∃ Q : Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) →L[ℝ] WeakDerivStep volume ⊤ p
            (ContinuousLinearMap.id ℝ (Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))),
          (trajectoryOperator AL).comp Q = ContinuousLinearMap.id ℝ _ ∧ ‖Q‖ ≤ C := by
  obtain ⟨L, hL⟩ := Real.smoothTransition.exists_forall_norm_deriv_le
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL 0)
  -- Opaque names for the constants keep the arithmetic below away from the operator norms.
  obtain ⟨K, hK⟩ : ∃ K, K = ‖Q₁‖ + ‖Q₂‖ := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = 1 / (8 * (K + 1)) := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hε]; positivity
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.1 (Metric.tendsto_nhds.1 h₁ ε hε0)
  obtain ⟨T₂, hT₂⟩ := eventually_atBot.1 (Metric.tendsto_nhds.1 h₂ ε hε0)
  refine ⟨2 * ((√2 + 1) * K), max (max (2 * T₁) (-2 * T₂)) (max 1 (8 * L * (K + 1))),
    fun R hR AL hAL ↦ ?_⟩
  simp only [ge_iff_le, max_le_iff] at hR
  obtain ⟨⟨hRT₁, hRT₂⟩, hR1, hRL⟩ := hR
  have hRpos : 0 < R := by linarith
  -- The error weight `δ` on the neck, and the arithmetic making `δ K ≤ 1 / 2`.
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = 2 / R * L + 2 * ε := ⟨_, rfl⟩
  have hδ0 : 0 ≤ δ := by rw [hδ]; positivity
  have hLR : 2 / R * L * (K + 1) ≤ 1 / 4 := by
    rw [show 2 / R * L * (K + 1) = 2 * L * (K + 1) / R by ring, div_le_iff₀ hRpos]
    linarith
  have hεK : 2 * ε * (K + 1) = 1 / 4 := by
    rw [hε]
    field_simp
    ring
  have hδK : δ * K ≤ 1 / 2 := by
    have : δ * K ≤ δ * (K + 1) := mul_le_mul_of_nonneg_left (by linarith) hδ0
    linarith [show δ * (K + 1) = 2 / R * L * (K + 1) + 2 * ε * (K + 1) by rw [hδ]; ring]
  have hcut : 2 / R * L ≤ 1 := by
    have : 2 / R * L ≤ 2 / R * L * (K + 1) :=
      le_mul_of_one_le_right (by positivity) (by linarith)
    linarith
  rw [hK] at hδK ⊢
  refine exists_rightInverse_of_splicedInverse hRpos hL hcut AL Q₁ Q₂ fun f ↦ ?_
  refine (norm_trajectoryOperator_splicedInverse_sub_le hε0.le hT₁ hT₂ hRpos hRT₁ hRT₂ hL hA₁L
    hA₂L hAL hQ₁ hQ₂ f).trans ?_
  rw [← hδ]
  exact mul_le_mul_of_nonneg_right hδK (norm_nonneg f)

end WeakDerivStep

end TauCeti
