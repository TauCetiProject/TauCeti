/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.Weak
public import TauCeti.Analysis.Complex.Wirtinger.RealBoundaryReflection
import TauCeti.Analysis.Complex.CauchyRiemann.Weak.Comparison
import TauCeti.Analysis.Complex.Wirtinger.Regularity
import TauCeti.Analysis.Complex.Wirtinger.Similarity.Examples

/-!
# Linear Cauchy–Riemann equations with a real boundary condition: reflection

Let `F` be a complex normed space whose real structure is its `star` operation, so that `x : F`
is real when `star x = x`. A solution `ξ` of the linear Cauchy–Riemann equation
`∂ₛξ + i ∂ₜξ + C(z) ξ = 0` on the closed upper part `Ω ∩ {0 ≤ im}` of a conjugation-invariant
open set `Ω`, real on the real axis, is reflected to a solution on all of `Ω`: the reflection
`TauCeti.starSchwarzReflection ξ` (`ξ z` on `0 ≤ im`, `star (ξ (conj z))` below) solves the same
kind of equation with the reflected coefficient `TauCeti.starSchwarzReflectionCoeff C`, which is
`C z` on `0 ≤ im` and `star ∘ C (conj z) ∘ star` below. This is the reflection step of the
boundary version of the similarity principle and unique continuation, in the model where the
structure is `i` everywhere.

The weak equation on the half-plane part is
`TauCeti.HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ (fun z ↦ -(2 : ℂ)⁻¹ • C z (ξ z))`, the weak
form of `\bar∂ξ = -C ξ / 2` with the real boundary condition encoded by the test functions; in
McDuff–Salamon's normalization `∂ₛ + i ∂ₜ = 2 \bar∂` this is `∂ₛξ + i ∂ₜξ + C ξ = 0`.

## Main results

* `TauCeti.starSchwarzReflectionCoeff`: the reflected coefficient field, and
  `TauCeti.starSchwarzReflection_clm_apply`, the pointwise identity
  `R (C ξ) = (R C) (R ξ)`.
* `TauCeti.MemLpLoc.starSchwarzReflectionCoeff`: a coefficient field locally `Lᵖ` up to the
  boundary reflects to one locally `Lᵖ` on the doubled domain.
* `HasWeakConjWirtingerDerivRealBoundaryOn.isWeakLinearCauchyRiemannOn_starSchwarzReflection`:
  for `1 < p < ∞` and finite-dimensional `F`, a continuous solution real on the axis with
  coefficient locally `Lᵖ` up to the boundary reflects to a weak solution
  `TauCeti.IsWeakLinearCauchyRiemannOn p Ω (fun _ ↦ I • id) (R C) (R ξ)` on `Ω`.
* Checks: the reflected coefficient of `0` is `0` and the reflection of `z` solves the reflected
  equation; the constant real coefficient `2` and `z e^{-conj z}` are fixed by the reflections, and
  the reflection of `z e^{-conj z}` solves the reflected equation; the constant coefficient `i` is
  reflected to `-i` below the axis, so the coefficient is genuinely conjugated.

The general facts about the reflection used here are in
`Analysis/Complex/Conformal/Reflection/Basic.lean` and
`Analysis/Complex/Wirtinger/RealBoundaryReflection.lean`: continuity of the reflection
(`TauCeti.continuousOn_starSchwarzReflection_of_symmetric`), local `Lᵖ` bounds on the doubled
domain (`TauCeti.MemLpLoc.starSchwarzReflection`), and the transfer of zeros
(`TauCeti.eqOn_starSchwarzReflection_of_subset_im_nonneg`) and of vanishing order
(`TauCeti.isBigO_starSchwarzReflection_sub_pow`) from the closed upper half-plane, so that the
interior unique continuation theorems apply to the reflected solution.

Only the structure `i` is treated: a variable structure equal to `i` on the axis is first
trivialized to `i`, which is not done here.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  AMS Colloquium Publications **52**, 2012, Section 2.3 and Appendix B.4.
-/

public noncomputable section

open Complex MeasureTheory TopologicalSpace Set
open scoped ComplexConjugate ENNReal

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F]

section Real

variable [NormedSpace ℝ F] [StarAddMonoid F] [StarModule ℝ F] [ContinuousStar F]

/-! ### The reflected coefficient -/

/-- The reflection of a field of real-linear endomorphisms across the real axis: `C z` on the
closed upper half-plane and `star ∘ C (conj z) ∘ star` below it. It is the coefficient of the
reflected equation, by `TauCeti.starSchwarzReflection_clm_apply`. -/
def starSchwarzReflectionCoeff (C : ℂ → F →L[ℝ] F) (z : ℂ) : F →L[ℝ] F :=
  if 0 ≤ z.im then C z else (starL' ℝ : F ≃L[ℝ] F).arrowCongr (starL' ℝ) (C (conj z))

variable {C : ℂ → F →L[ℝ] F}

/-- The reflected coefficient is the explicit upper/lower half-plane witness. -/
theorem starSchwarzReflectionCoeff_def (C : ℂ → F →L[ℝ] F) (z : ℂ) :
    starSchwarzReflectionCoeff C z =
      if 0 ≤ z.im then C z else (starL' ℝ : F ≃L[ℝ] F).arrowCongr (starL' ℝ) (C (conj z)) := by
  rw [starSchwarzReflectionCoeff]

@[simp]
theorem starSchwarzReflectionCoeff_of_im_nonneg {z : ℂ} (hz : 0 ≤ z.im) :
    starSchwarzReflectionCoeff C z = C z := ite_eq_left_iff.2 fun h ↦ (h hz).elim

@[simp]
theorem starSchwarzReflectionCoeff_apply_of_im_neg {z : ℂ} (hz : z.im < 0) (x : F) :
    starSchwarzReflectionCoeff C z x = star (C (conj z) (star x)) := by
  simp [starSchwarzReflectionCoeff, hz.not_ge]

/-- **The reflected equation, pointwise.** Reflecting `z ↦ C z (ξ z)` is applying the reflected
coefficient to the reflected function. -/
theorem starSchwarzReflection_clm_apply (C : ℂ → F →L[ℝ] F) (ξ : ℂ → F) :
    starSchwarzReflection (fun z ↦ C z (ξ z)) =
      fun z ↦ starSchwarzReflectionCoeff C z (starSchwarzReflection ξ z) := by
  funext z
  by_cases hz : 0 ≤ z.im
  · simp [hz]
  · simp [not_le.1 hz]

/-- The reflection of a coefficient field locally `Lᵖ` up to the boundary is locally `Lᵖ` on the
doubled domain. -/
theorem MemLpLoc.starSchwarzReflectionCoeff {p : ℝ≥0∞} {Ω : Set ℂ}
    (hΩ : MapsTo (starRingEnd ℂ) Ω Ω) (hC : MemLpLoc p (Ω ∩ {z | 0 ≤ z.im}) C) :
    MemLpLoc p Ω (starSchwarzReflectionCoeff C) := by
  rw [funext (starSchwarzReflectionCoeff_def C)]
  simpa only [ContinuousLinearEquiv.coe_coe] using
    hC.ite_conj hΩ ((starL' ℝ : F ≃L[ℝ] F).arrowCongr (starL' ℝ)).toContinuousLinearMap

end Real

/-! ### The reflected equation -/

section Complex

variable [NormedSpace ℂ F] [StarAddMonoid F] [StarModule ℂ F] [ContinuousStar F]
  {C : ℂ → F →L[ℝ] F} {ξ : ℂ → F}

/-- **Reflection of the linear Cauchy–Riemann equation with a real boundary condition.** Let
`1 < p < ∞`, let `F` be finite-dimensional, let `Ω` be conjugation invariant, and let `ξ` be
continuous on `Ω ∩ {0 ≤ im}` and real on `Ω ∩ ℝ`, solving `∂ₛξ + i ∂ₜξ + C(z) ξ = 0` weakly on
`Ω ∩ {0 ≤ im}` with the real boundary condition, for a coefficient field `C` locally `Lᵖ` up to the
boundary. Then the reflection of `ξ` is a weak solution on all of `Ω` of the same equation with
the reflected coefficient field. -/
theorem HasWeakConjWirtingerDerivRealBoundaryOn.isWeakLinearCauchyRiemannOn_starSchwarzReflection
    [FiniteDimensional ℂ F] {p : ℝ≥0∞} (hp : 1 < p) (hp_top : p ≠ ⊤) {Ω : Opens ℂ}
    (hΩ : MapsTo (starRingEnd ℂ) Ω Ω) (hC : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) C)
    (hξc : ContinuousOn ξ ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hξr : ∀ x : ℝ, (x : ℂ) ∈ Ω → star (ξ x) = ξ x)
    (h : HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ fun z ↦ -(2 : ℂ)⁻¹ • C z (ξ z)) :
    IsWeakLinearCauchyRiemannOn p Ω (fun _ ↦ I • ContinuousLinearMap.id ℝ F)
      (starSchwarzReflectionCoeff C) (starSchwarzReflection ξ) := by
  -- The normalizing factor `-1/2` is real, so it commutes with the reflection.
  have hs (x : F) : -(2 : ℂ)⁻¹ • x = (-(2 : ℝ)⁻¹) • x := by
    rw [← Complex.coe_smul]
    norm_num
  have hc := continuousOn_starSchwarzReflection_of_symmetric hΩ hξc hξr
  have hw := h.hasWeakConjWirtingerDerivOn_starSchwarzReflection hΩ
  simp only [hs, starSchwarzReflection_const_smul, starSchwarzReflection_clm_apply] at hw
  have hf : MemLpLoc p Ω
      (fun z ↦ (-(2 : ℝ)⁻¹) • starSchwarzReflectionCoeff C z (starSchwarzReflection ξ z)) :=
    ((hC.starSchwarzReflectionCoeff hΩ).clm_apply_continuousOn hc).const_smul _
  refine isWeakCauchyRiemannOn_I_smul_id_iff.2 ⟨hc, hw.memWkpLoc_one hp hp_top hc.memLpLoc hf, ?_⟩
  simpa only [smul_neg, ← neg_smul, hs] using hw

end Complex

/-! ### Checks -/

section Real

variable [NormedSpace ℝ F] [StarAddMonoid F] [StarModule ℝ F] [ContinuousStar F]

@[simp]
theorem starSchwarzReflectionCoeff_zero :
    starSchwarzReflectionCoeff (0 : ℂ → F →L[ℝ] F) = 0 := by
  funext z
  by_cases hz : 0 ≤ z.im
  · simp [hz]
  · ext x
    simp [not_le.1 hz]

/-- **Check.** A constant real multiple of the identity is its own reflected coefficient. -/
theorem starSchwarzReflectionCoeff_const_real_smul_id (c : ℝ) :
    starSchwarzReflectionCoeff (fun _ ↦ c • ContinuousLinearMap.id ℝ F) =
      fun _ ↦ c • ContinuousLinearMap.id ℝ F := by
  funext z
  by_cases hz : 0 ≤ z.im
  · simp [hz]
  · ext x
    simp [not_le.1 hz, star_smul]

end Real

/-- **Check.** For `C = 0` the reflected equation is `\bar∂ = 0`, solved by the reflection of the
real-boundary solution `z`, which is `z` itself. -/
theorem isWeakLinearCauchyRiemannOn_starSchwarzReflection_id {p : ℝ≥0∞} {Ω : Opens ℂ} :
    IsWeakLinearCauchyRiemannOn p Ω (fun _ ↦ I • ContinuousLinearMap.id ℝ ℂ)
      (starSchwarzReflectionCoeff 0) (starSchwarzReflection id) := by
  rw [starSchwarzReflectionCoeff_zero, starSchwarzReflection_id]
  exact isWeakCauchyRiemannOn_of_contDiffOn contDiff_id.contDiffOn fun z _ ↦ by simp

/-- **Check.** The constant coefficient `i` is reflected to `-i` below the axis: the reflected
coefficient is the conjugate, not the even reflection. -/
theorem starSchwarzReflectionCoeff_const_I_smul_id_of_im_neg [NormedSpace ℂ F] [StarAddMonoid F]
    [StarModule ℂ F] [ContinuousStar F] {z : ℂ} (hz : z.im < 0) :
    starSchwarzReflectionCoeff (fun _ ↦ I • ContinuousLinearMap.id ℝ F) z =
      -(I • ContinuousLinearMap.id ℝ F) := by
  ext x
  simp [hz, star_smul]

/-- **Check.** The solution `z e^{-conj z}` of `∂ₛξ + i ∂ₜξ + 2ξ = 0`, which is real on the real
axis, is its own reflection. -/
theorem starSchwarzReflection_mul_cexp_neg_conj :
    starSchwarzReflection (fun z : ℂ ↦ z * cexp (-conj z)) = fun z ↦ z * cexp (-conj z) := by
  funext z
  by_cases hz : 0 ≤ z.im
  · rw [starSchwarzReflection_of_im_nonneg hz]
  · rw [starSchwarzReflection_of_im_neg (not_le.1 hz), Complex.star_def, map_mul,
      ← Complex.exp_conj, map_neg, conj_conj]

/-- **Check.** With the nonzero coefficient `C = 2`, the reflection of the real-boundary solution
`z e^{-conj z}` solves the reflected equation `∂ₛξ + i ∂ₜξ + 2ξ = 0` on every open set. -/
theorem isWeakLinearCauchyRiemannOn_starSchwarzReflection_mul_cexp_neg_conj {p : ℝ≥0∞}
    {Ω : Opens ℂ} :
    IsWeakLinearCauchyRiemannOn p Ω (fun _ ↦ I • ContinuousLinearMap.id ℝ ℂ)
      (starSchwarzReflectionCoeff fun _ ↦ (2 : ℝ) • ContinuousLinearMap.id ℝ ℂ)
      (starSchwarzReflection fun z : ℂ ↦ z * cexp (-conj z)) := by
  rw [starSchwarzReflectionCoeff_const_real_smul_id, starSchwarzReflection_mul_cexp_neg_conj]
  have hd : ContDiff ℝ 1 fun z : ℂ ↦ z * cexp (-conj z) := by
    simpa only [Complex.conjCLE_apply, id_eq] using contDiff_id.mul conjCLE.contDiff.neg.cexp
  refine isWeakCauchyRiemannOn_of_contDiffOn hd.contDiffOn fun z _ ↦ ?_
  have := fderiv_mul_cexp_neg_conj_add_eq_zero z
  simp only [smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul, Complex.real_smul]
  push_cast
  linear_combination this

end TauCeti
