/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Circle.Lp
public import TauCeti.Analysis.Sobolev.Circle.Rotation
public import TauCeti.MeasureTheory.Function.Lp.Precomposition
public import TauCeti.MeasureTheory.Integral.IntervalIntegral.Periodic

import TauCeti.Analysis.Fourier.Monomial

/-!
# Precomposition with circle diffeomorphisms on `H⁰`

A boundary circle of a cut Riemann surface carries no preferred coordinate, so the Sobolev spaces
of boundary maps must not depend on the parametrization: a fixed diffeomorphism `φ` of the circle
should induce a bounded isomorphism `u ↦ u ∘ φ` of every `H^s`. This file treats the order
`s = 0`, where `H⁰` is `L²` of the circle (`TauCeti.CircleSobolev.toLpₗᵢ`).

Precomposition with a measurable map `φ` of the circle is well defined and bounded on `L²` as
soon as `φ` pushes Haar measure forward to at most `C` times Haar measure, and then its norm is
at most `√C` (`TauCeti.CircleSobolev.precomp`). For `s > 1/2` it is honest composition of the
continuous representatives. An orientation-preserving diffeomorphism of the circle is given by a
lift `F : ℝ → ℝ` with `F (x + T) = F x + T` whose derivative satisfies `0 < c ≤ F' ≤ M`; it pushes
Haar measure forward to at most `c⁻¹` times Haar measure, and its inverse to at most `M` times
Haar measure (`AddCircle.map_haarAddCircle_le_of_lift`). Precomposition with it is therefore a
continuous linear automorphism of `H⁰`, with `‖u ∘ φ‖ ≤ c^(-1/2) ‖u‖` and
`‖u ∘ φ⁻¹‖ ≤ M^(1/2) ‖u‖` (`TauCeti.CircleSobolev.precompEquivOfLift`). Such constants exist for
every lift with continuous positive derivative (`AddCircle.exists_pos_le_deriv_le_of_lift`).
For the rotations `x ↦ x + θ` precomposition is the rotation `TauCeti.CircleSobolev.rotate θ`.

## Main definitions

* `TauCeti.CircleSobolev.precomp T hφ hC hmap`: precomposition with `φ` on `H⁰`, for `φ`
  measurable with `haarAddCircle.map φ ≤ C • haarAddCircle` and `C < ∞`.
* `TauCeti.CircleSobolev.precompEquivOfLift`: for `φ` with lift `F`, `0 < c ≤ F' ≤ M`, the
  continuous linear automorphism `u ↦ u ∘ φ` of `H⁰`.

## Main statements

* `TauCeti.CircleSobolev.toLpₗᵢ_precomp`: the `L²` function of `precomp T hφ hC hmap a` is
  `toLpₗᵢ T a ∘ φ` almost everywhere.
* `TauCeti.CircleSobolev.norm_precomp_le`: `‖a ∘ φ‖ ≤ √C ‖a‖`.
* `TauCeti.CircleSobolev.toLpₗᵢ_precomp_inclusion`: for `s > 1/2` and continuous `φ`,
  precomposition is composition of the continuous representatives.
* `TauCeti.CircleSobolev.precomp_comp`: precomposition is contravariant in `φ`.
* `TauCeti.CircleSobolev.precomp_add_const`: precomposition with a rotation is
  `TauCeti.CircleSobolev.rotate`.
* `TauCeti.CircleSobolev.norm_precompEquivOfLift_le` and
  `TauCeti.CircleSobolev.norm_precompEquivOfLift_symm_le`: the bounds `c^(-1/2)` and `M^(1/2)`.

## References

* J. W. Robbin and D. A. Salamon, *A construction of the Deligne–Mumford orbifold*,
  J. Eur. Math. Soc. **8** (2006), 611–699, for the Sobolev spaces of boundary maps on which
  the Hardy decompositions of cut Riemann surfaces are carried out.
* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Proposition 9.6 (change of variables in Sobolev spaces under diffeomorphisms).
-/

public section

noncomputable section

open MeasureTheory AddCircle
open scoped ENNReal

namespace TauCeti

namespace CircleSobolev

variable (T : ℝ) [hT : Fact (0 < T)] {φ ψ : AddCircle T → AddCircle T} {C D : ℝ≥0∞}

/-- **Precomposition on `H⁰`.** For a measurable map `φ` of the circle pushing normalized Haar
measure forward to at most `C` times itself, `C < ∞`, the continuous linear map `a ↦ a ∘ φ` of
`H⁰ = L²(AddCircle T)`. -/
def precomp (hφ : Measurable φ) (hC : C ≠ ∞)
    (hmap : (haarAddCircle : Measure (AddCircle T)).map φ ≤ C • haarAddCircle) :
    CircleSobolev 0 ℂ →L[ℂ] CircleSobolev 0 ℂ :=
  (toLpₗᵢ T).symm.toLinearIsometry.toContinuousLinearMap.comp
    ((Lp.compOfMapLeSmul ℂ hφ hC hmap).comp (toLpₗᵢ T).toLinearIsometry.toContinuousLinearMap)

variable {T}

theorem precomp_apply (hφ : Measurable φ) (hC : C ≠ ∞)
    (hmap : (haarAddCircle : Measure (AddCircle T)).map φ ≤ C • haarAddCircle)
    (a : CircleSobolev 0 ℂ) :
    precomp T hφ hC hmap a = (toLpₗᵢ T).symm (Lp.compOfMapLeSmul ℂ hφ hC hmap (toLpₗᵢ T a)) :=
  (rfl)

/-- `precomp` conjugates the precomposition operator of `L²` by the identification of `H⁰` with
`L²`. -/
theorem toLpₗᵢ_precomp_apply (hφ : Measurable φ) (hC : C ≠ ∞)
    (hmap : (haarAddCircle : Measure (AddCircle T)).map φ ≤ C • haarAddCircle)
    (a : CircleSobolev 0 ℂ) :
    toLpₗᵢ T (precomp T hφ hC hmap a) = Lp.compOfMapLeSmul ℂ hφ hC hmap (toLpₗᵢ T a) := by
  rw [precomp_apply, LinearIsometryEquiv.apply_symm_apply]

/-- The `L²` function of `precomp T hφ hC hmap a` is the `L²` function of `a` composed with `φ`. -/
theorem toLpₗᵢ_precomp (hφ : Measurable φ) (hC : C ≠ ∞)
    (hmap : (haarAddCircle : Measure (AddCircle T)).map φ ≤ C • haarAddCircle)
    (a : CircleSobolev 0 ℂ) :
    toLpₗᵢ T (precomp T hφ hC hmap a) =ᵐ[haarAddCircle] toLpₗᵢ T a ∘ φ := by
  rw [toLpₗᵢ_precomp_apply]
  exact Lp.coeFn_compOfMapLeSmul hφ hC hmap (toLpₗᵢ T a)

/-- The coefficients of `precomp T hφ hC hmap a` are the Fourier coefficients of the `L²` function
of `a` composed with `φ`. -/
theorem coeff_precomp (hφ : Measurable φ) (hC : C ≠ ∞)
    (hmap : (haarAddCircle : Measure (AddCircle T)).map φ ≤ C • haarAddCircle)
    (a : CircleSobolev 0 ℂ) (n : ℤ) :
    (precomp T hφ hC hmap a).coeff n = fourierCoeff (toLpₗᵢ T a ∘ φ) n := by
  rw [← fourierCoeff_toLpₗᵢ T, fourierCoeff, fourierCoeff]
  exact integral_congr_ae ((toLpₗᵢ_precomp hφ hC hmap a).mono fun x hx ↦ by simp only [hx])

/-- **The norm of precomposition.** If `φ` pushes Haar measure forward to at most `C` times Haar
measure, then `‖a ∘ φ‖ ≤ √C ‖a‖` in `H⁰`. -/
theorem norm_precomp_le (hφ : Measurable φ) (hC : C ≠ ∞)
    (hmap : (haarAddCircle : Measure (AddCircle T)).map φ ≤ C • haarAddCircle)
    (a : CircleSobolev 0 ℂ) :
    ‖precomp T hφ hC hmap a‖ ≤ √C.toReal * ‖a‖ := by
  have h := Lp.norm_compOfMapLeSmul_le (𝕜 := ℂ) hφ hC hmap (toLpₗᵢ T a)
  have hexp : (1 / (2 : ℝ≥0∞)).toReal = 1 / 2 := by norm_num
  rw [LinearIsometryEquiv.norm_map, ← toLpₗᵢ_precomp_apply, LinearIsometryEquiv.norm_map,
    ← ENNReal.toReal_rpow, hexp, ← Real.sqrt_eq_rpow] at h
  exact h

/-- **Precomposition of continuous representatives.** For `s > 1/2`, `a ∈ H^s` and a continuous
map `φ`, the `L²` function of `precomp T hφ hC hmap a` is the class of the continuous function
`x ↦ a (φ x)`. -/
theorem toLpₗᵢ_precomp_inclusion {s : ℝ} (hs : 1 / 2 < s) (hφc : Continuous φ) (hC : C ≠ ∞)
    (hmap : (haarAddCircle : Measure (AddCircle T)).map φ ≤ C • haarAddCircle)
    (a : CircleSobolev s ℂ) :
    toLpₗᵢ T (precomp T hφc.measurable hC hmap (inclusion (by linarith) a)) =
      ContinuousMap.toLp 2 haarAddCircle ℂ ((toContinuousMap T hs a).comp ⟨φ, hφc⟩) := by
  refine Lp.ext ((toLpₗᵢ_precomp _ hC hmap _).trans ?_)
  rw [toLpₗᵢ_inclusion_eq_toLp_toContinuousMap T hs]
  have h₁ := (QuasiMeasurePreserving.of_map_le_smul hφc.measurable hmap).ae_eq_comp
    (ContinuousMap.coeFn_toLp (p := 2) (μ := haarAddCircle) (𝕜 := ℂ) (toContinuousMap T hs a))
  have h₂ := ContinuousMap.coeFn_toLp (p := 2) (μ := haarAddCircle) (𝕜 := ℂ)
    ((toContinuousMap T hs a).comp ⟨φ, hφc⟩)
  exact h₁.trans h₂.symm

/-- Precomposition is contravariant: precomposing with `ψ ∘ φ` is precomposing with `ψ`, then
with `φ`. -/
theorem precomp_comp (hφ : Measurable φ) (hC : C ≠ ∞)
    (hmap : (haarAddCircle : Measure (AddCircle T)).map φ ≤ C • haarAddCircle)
    (hψ : Measurable ψ) (hD : D ≠ ∞)
    (hmapψ : (haarAddCircle : Measure (AddCircle T)).map ψ ≤ D • haarAddCircle)
    {B : ℝ≥0∞} (hB : B ≠ ∞)
    (hmapψφ : (haarAddCircle : Measure (AddCircle T)).map (ψ ∘ φ) ≤ B • haarAddCircle) :
    precomp T (hψ.comp hφ) hB hmapψφ = (precomp T hφ hC hmap).comp (precomp T hψ hD hmapψ) := by
  ext1 a
  rw [ContinuousLinearMap.comp_apply, precomp_apply, precomp_apply, precomp_apply,
    LinearIsometryEquiv.apply_symm_apply, Lp.compOfMapLeSmul_comp hφ hC hmap hψ hD hmapψ hB hmapψφ,
    ContinuousLinearMap.comp_apply]

/-- Precomposition with the identity is the identity. -/
@[simp]
theorem precomp_id (hC : C ≠ ∞)
    (hmap : (haarAddCircle : Measure (AddCircle T)).map id ≤ C • haarAddCircle) :
    precomp T measurable_id hC hmap = ContinuousLinearMap.id ℂ _ := by
  ext1 a
  rw [precomp_apply, Lp.compOfMapLeSmul_id hC hmap, ContinuousLinearMap.id_apply,
    LinearIsometryEquiv.symm_apply_apply, ContinuousLinearMap.id_apply]

/-- **Rotations.** Precomposition with the rotation `x ↦ x + θ` of the circle is the rotation
`CircleSobolev.rotate θ` of `H⁰`, which multiplies the `n`-th coefficient by `e^{2πinθ/T}`. -/
theorem precomp_add_const (θ : AddCircle T) (hC : C ≠ ∞)
    (hmap : (haarAddCircle : Measure (AddCircle T)).map (· + θ) ≤ C • haarAddCircle)
    (a : CircleSobolev 0 ℂ) :
    precomp T (measurable_add_const θ) hC hmap a = rotate θ a := by
  ext n
  rw [coeff_precomp, coeff_rotate, ← fourierCoeff_toLpₗᵢ T a, fourierCoeff, fourierCoeff,
    ← integral_smul, ← integral_add_right_eq_self (μ := haarAddCircle)
      (fun y ↦ fourier n θ • fourier (-n) y • toLpₗᵢ T a y) θ]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
  have h : fourier n θ * fourier (-n) θ = 1 := by
    rw [← fourier_add, add_neg_cancel, fourier_zero]
  simp only [Function.comp_apply, smul_eq_mul, fourier_apply_add]
  linear_combination (-(fourier (-n) x * toLpₗᵢ T a (x + θ))) * h

section Lift

variable {F F' : ℝ → ℝ} {c M : ℝ} (hF : ∀ x, HasDerivAt F (F' x) x)
  (hper : ∀ x, F (x + T) = F x + T) (hφ : ∀ x : ℝ, φ x = F x) (hc : 0 < c)
  (hcF : ∀ x, c ≤ F' x) (hMF : ∀ x, F' x ≤ M)

/-- The inverse map of the circle, for `φ` with lift `F`, `0 < c ≤ F'`. -/
private def symmOfLift : AddCircle T ≃ₜ AddCircle T :=
  (homeomorphOfLift φ (strictMono_of_hasDerivAt_pos hF fun x ↦ hc.trans_le (hcF x))
    (continuous_iff_continuousAt.2 fun x ↦ (hF x).continuousAt) hper hφ).symm

private theorem symmOfLift_apply_apply (x : AddCircle T) :
    symmOfLift hF hper hφ hc hcF (φ x) = x :=
  homeomorphOfLift_symm_apply_apply _ _ _ _ x

private theorem apply_symmOfLift_apply (x : AddCircle T) :
    φ (symmOfLift hF hper hφ hc hcF x) = x :=
  apply_homeomorphOfLift_symm_apply _ _ _ _ x

/-- **Circle diffeomorphisms act on `H⁰`.** Let `φ` be the map of the circle with lift `F`, so that
`F (x + T) = F x + T` and `φ x = F x`, and suppose that `F` is differentiable with
`0 < c ≤ F' ≤ M`. Then `a ↦ a ∘ φ` is a continuous linear automorphism of `H⁰ = L²(AddCircle T)`,
whose inverse is precomposition with the inverse map of the circle. -/
def precompEquivOfLift : CircleSobolev 0 ℂ ≃L[ℂ] CircleSobolev 0 ℂ :=
  ((toLpₗᵢ T).toContinuousLinearEquiv.trans
    (Lp.compEquivOfMapLeSmul ℂ
      (continuous_of_lift (continuous_iff_continuousAt.2 fun x ↦ (hF x).continuousAt) hφ).measurable
      (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hc).ne')
      (map_haarAddCircle_le_of_lift hF hper hφ hc hcF)
      (symmOfLift hF hper hφ hc hcF).continuous.measurable ENNReal.ofReal_ne_top
      (map_haarAddCircle_le_of_lift_of_leftInverse hF hper hφ (fun x ↦ hc.trans_le (hcF x)) hMF
        (symmOfLift hF hper hφ hc hcF).continuous.measurable
        (symmOfLift_apply_apply hF hper hφ hc hcF))
      (symmOfLift_apply_apply hF hper hφ hc hcF) (apply_symmOfLift_apply hF hper hφ hc hcF))).trans
    (toLpₗᵢ T).symm.toContinuousLinearEquiv

/-- `precompEquivOfLift` is precomposition with `φ`. -/
theorem precompEquivOfLift_apply (a : CircleSobolev 0 ℂ) :
    precompEquivOfLift hF hper hφ hc hcF hMF a =
      precomp T (continuous_of_lift (continuous_iff_continuousAt.2 fun x ↦ (hF x).continuousAt)
        hφ).measurable (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hc).ne')
        (map_haarAddCircle_le_of_lift hF hper hφ hc hcF) a := by
  simp only [precompEquivOfLift, ContinuousLinearEquiv.trans_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, Lp.compEquivOfMapLeSmul_apply, precomp_apply]

/-- The `L²` function of `precompEquivOfLift hF hper hφ hc hcF hMF a` is `toLpₗᵢ T a ∘ φ`. -/
theorem toLpₗᵢ_precompEquivOfLift (a : CircleSobolev 0 ℂ) :
    toLpₗᵢ T (precompEquivOfLift hF hper hφ hc hcF hMF a) =ᵐ[haarAddCircle] toLpₗᵢ T a ∘ φ := by
  rw [precompEquivOfLift_apply]
  exact toLpₗᵢ_precomp _ _ _ a

/-- The inverse of `precompEquivOfLift` is precomposition with the inverse map of the circle. -/
private theorem precompEquivOfLift_symm_apply (a : CircleSobolev 0 ℂ) :
    (precompEquivOfLift hF hper hφ hc hcF hMF).symm a =
      precomp T (symmOfLift hF hper hφ hc hcF).continuous.measurable ENNReal.ofReal_ne_top
        (map_haarAddCircle_le_of_lift_of_leftInverse hF hper hφ (fun x ↦ hc.trans_le (hcF x))
          hMF (symmOfLift hF hper hφ hc hcF).continuous.measurable
          (symmOfLift_apply_apply hF hper hφ hc hcF)) a := by
  simp only [precompEquivOfLift, ContinuousLinearEquiv.symm_trans_apply,
    LinearIsometryEquiv.coe_symm_toContinuousLinearEquiv, LinearIsometryEquiv.symm_symm,
    Lp.compEquivOfMapLeSmul_symm_apply, precomp_apply]

/-- The inverse of `precompEquivOfLift` is precomposition with the inverse `ψ` of `φ`: the `L²`
function of `(precompEquivOfLift hF hper hφ hc hcF hMF).symm a` is `toLpₗᵢ T a ∘ ψ`. -/
theorem toLpₗᵢ_precompEquivOfLift_symm {ψ : AddCircle T → AddCircle T}
    (hψφ : Function.LeftInverse ψ φ) (a : CircleSobolev 0 ℂ) :
    toLpₗᵢ T ((precompEquivOfLift hF hper hφ hc hcF hMF).symm a) =ᵐ[haarAddCircle]
      toLpₗᵢ T a ∘ ψ := by
  have hψ : ψ = symmOfLift hF hper hφ hc hcF := funext fun y ↦ by
    obtain ⟨x, rfl⟩ := (bijective_of_lift
      (strictMono_of_hasDerivAt_pos hF fun x ↦ hc.trans_le (hcF x))
      (continuous_iff_continuousAt.2 fun x ↦ (hF x).continuousAt) hper hφ).2 y
    rw [hψφ x, symmOfLift_apply_apply]
  subst hψ
  rw [precompEquivOfLift_symm_apply]
  exact toLpₗᵢ_precomp _ _ _ a

/-- The norm of precomposition with a circle diffeomorphism whose lift has derivative at least
`c`: `‖a ∘ φ‖ ≤ c^(-1/2) ‖a‖`. -/
theorem norm_precompEquivOfLift_le (a : CircleSobolev 0 ℂ) :
    ‖precompEquivOfLift hF hper hφ hc hcF hMF a‖ ≤ (√c)⁻¹ * ‖a‖ := by
  rw [precompEquivOfLift_apply]
  refine (norm_precomp_le _ _ _ a).trans_eq ?_
  rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal hc.le, Real.sqrt_inv]

/-- The norm of the inverse of precomposition with a circle diffeomorphism whose lift has
derivative at most `M`: `‖a ∘ φ⁻¹‖ ≤ M^(1/2) ‖a‖`. -/
theorem norm_precompEquivOfLift_symm_le (a : CircleSobolev 0 ℂ) :
    ‖(precompEquivOfLift hF hper hφ hc hcF hMF).symm a‖ ≤ √M * ‖a‖ := by
  rw [precompEquivOfLift_symm_apply]
  refine (norm_precomp_le _ _ _ a).trans_eq ?_
  rw [ENNReal.toReal_ofReal (hc.le.trans ((hcF 0).trans (hMF 0)))]

end Lift

end CircleSobolev

end TauCeti
