/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.EnergyForm.HyperplaneReflection
public import TauCeti.Analysis.PDE.Regularity.ConstantCoefficientDecay
import TauCeti.Analysis.InnerProductSpace.Transvection
import TauCeti.Analysis.InnerProductSpace.Reflection
import TauCeti.Analysis.PDE.EnergyForm.ConstantCoefficient
import TauCeti.Analysis.PDE.EnergyForm.Restriction
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Integral.Average

/-!
# Decay estimates at a flat boundary for constant coefficients

Let `H = {x | c₀ < ⟪x, ν⟫}`, let `z` lie on its boundary hyperplane, and let `A` be a constant
matrix with `λ ‖ξ‖² ≤ ξᵀ A ξ` and `|ηᵀ A ξ| ≤ Λ ‖η‖ ‖ξ‖`, `λ > 0`. Let `u ∈ H¹(U)`,
`B(z, r) ⊆ U`, vanish on `U ∖ H` and solve `-div(A ∇u) = 0` weakly on `U ∩ H`: zero boundary values
on the flat part of the boundary. With `B_s⁺ = B(z, s) ∩ H` and `0 ≤ ρ ≤ r`, this file proves the
half-ball versions of the decay estimates for constant coefficients on balls
(`TauCeti.PDE.setIntegral_ball_norm_gradient_sq_le_of_forall_energyFormH1_eq_zero` and
`TauCeti.PDE.setIntegral_ball_norm_gradient_sub_setAverage_sq_le_of_forall_energyFormH1_eq_zero`),
with `C` depending only on `n`, `λ` and `Λ`:

* `∫_{B_ρ⁺} ‖∇u‖² ≤ C (ρ / r)ⁿ ∫_{B_r⁺} ‖∇u‖²`
  (`TauCeti.PDE.exists_setIntegral_ball_inter_norm_gradient_sq_le`);
* `∫_{B_ρ⁺} ‖∇u - p_ρ‖² ≤ C (ρ / r)^(n + 2) ∫_{B_r⁺} ‖∇u - t ν‖²` for every real `t`, where `p_ρ`
  is the multiple of `ν` closest to `∇u` in `L²(B_ρ⁺)`
  (`TauCeti.PDE.exists_setIntegral_ball_inter_norm_gradient_sub_inner_setAverage_div_smul_sq_le`).

Only multiples of the normal are compared with `∇u`: `t ν` is the gradient of `t (⟪x, ν⟫ - c₀)`,
which vanishes on the hyperplane. These are the decay estimates of the frozen problem at boundary
points in Campanato's approach to `C^{1,α}` estimates up to a flat boundary; for the Laplacian on
`ℝ × E` they are `TauCeti.WeaklyHarmonicOn.setIntegral_ball_inter_normalHalfSpace_norm_sq_le` and
`TauCeti.WeaklyHarmonicOn.setIntegral_ball_inter_normalHalfSpace_norm_sub_sq_le`.

## The argument

Tested against `H¹₀`, the constant-coefficient equation only sees the symmetric part of `A`
(`TauCeti.PDE.energyFormH1_const_coefficientSymmetricPart`), which has the same constants, so `A`
may be taken symmetric. The odd reflection of `u` solves the equation with coefficient `A` above
the hyperplane and `R A R` below it, `R` the linear part of the reflection; this is constant
exactly when `A ν ∥ ν`.
The shear `P y = y + (⟪ν, y⟫ - c₀) s`, `s = A ν / ⟪ν, A ν⟫ - ν / ‖ν‖²`, fixes the hyperplane,
preserves `H` and the Lebesgue measure, and turns `A` into a constant `B` with `B ν ∥ ν`. So the
odd reflection of `u ∘ P` solves `-div(B ∇w) = 0` on a whole ball centred at `z`
(`TauCeti.PDE.energyFormH1_reflectPrincipal_sub_compHyperplaneReflectionL`), where the estimates
on balls apply. As `P`, `P⁻¹` and their transposes have norm at most `κ = 1 + Λ / λ`, these
transfer back to `u`; radii with `κ² ρ > r` are handled by the trivial estimate.

## References

* M. Giaquinta, L. Martinazzi, *An Introduction to the Regularity Theory for Elliptic Systems,
  Harmonic Maps and Minimal Graphs*, 2nd ed., Chapter 5.
* D. Gilbarg, N. S. Trudinger, *Elliptic PDE of Second Order*, Theorem 8.33 and its proof.
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace InnerProductSpace Metric Matrix

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι]

/-! ### The conormal shear vector -/

variable [DecidableEq ι]

/-- The **conormal shear vector** of a matrix `A` and a normal `ν`:
`s = A ν / ⟪ν, A ν⟫ - ν / ‖ν‖²`. It is orthogonal to `ν`, and the shear along it carries the
conormal direction `A ν` to a multiple of `ν`. -/
private def conormalShearVector (A : Matrix ι ι ℝ) (ν : EuclideanSpace ℝ ι) :
    EuclideanSpace ℝ ι :=
  (matrixBilinearForm A ν ν)⁻¹ • toEuclideanCLM (𝕜 := ℝ) A ν - (‖ν‖ ^ 2)⁻¹ • ν

private theorem inner_conormalShearVector (A : Matrix ι ι ℝ) (ν x : EuclideanSpace ℝ ι) :
    ⟪conormalShearVector A ν, x⟫_ℝ =
      (matrixBilinearForm A ν ν)⁻¹ * matrixBilinearForm A x ν - (‖ν‖ ^ 2)⁻¹ * ⟪ν, x⟫_ℝ := by
  rw [conormalShearVector, inner_sub_left, inner_smul_left, inner_smul_left, RCLike.conj_to_real,
    RCLike.conj_to_real, real_inner_comm, inner_toEuclideanCLM, matrixBilinearForm_apply,
    matrixBilinearForm_apply]

private theorem inner_conormalShearVector_self {A : Matrix ι ι ℝ} {ν : EuclideanSpace ℝ ι}
    (hν : ν ≠ 0) (hq : matrixBilinearForm A ν ν ≠ 0) :
    ⟪ν, conormalShearVector A ν⟫_ℝ = 0 := by
  rw [real_inner_comm, inner_conormalShearVector, real_inner_self_eq_norm_sq,
    inv_mul_cancel₀ hq, inv_mul_cancel₀ (by positivity), sub_self]

private theorem norm_mul_norm_conormalShearVector_le {A : Matrix ι ι ℝ} {ν : EuclideanSpace ℝ ι}
    {lam Lam : ℝ} (hlam : 0 < lam) (hν : ν ≠ 0)
    (hA : ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hA' : ∀ η ξ : EuclideanSpace ℝ ι, |η ⬝ᵥ (A *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖) :
    ‖ν‖ * ‖conormalShearVector A ν‖ ≤ Lam / lam := by
  set s := conormalShearVector A ν
  have hν' : 0 < ‖ν‖ := norm_pos_iff.2 hν
  have hq : lam * ‖ν‖ ^ 2 ≤ matrixBilinearForm A ν ν := by
    simpa [matrixBilinearForm_apply, toQuadraticForm'_apply] using hA ν
  have hq0 : 0 < matrixBilinearForm A ν ν := lt_of_lt_of_le (by positivity) hq
  -- `‖s‖² β(ν, ν) = β(s, ν)`, since `s ⊥ ν`.
  have hss : ‖s‖ ^ 2 * matrixBilinearForm A ν ν = matrixBilinearForm A s ν := by
    have hsν : ⟪ν, s⟫_ℝ = 0 := inner_conormalShearVector_self hν hq0.ne'
    rw [← real_inner_self_eq_norm_sq]
    conv_lhs => rw [inner_conormalShearVector]
    rw [hsν, mul_zero, sub_zero]
    field_simp
  have hβ : matrixBilinearForm A s ν ≤ Lam * ‖s‖ * ‖ν‖ := by
    rw [matrixBilinearForm_apply]
    exact (le_abs_self _).trans (hA' s ν)
  have h1 : ‖s‖ * (‖s‖ * (lam * ‖ν‖ ^ 2)) ≤ ‖s‖ * (Lam * ‖ν‖) := by
    calc ‖s‖ * (‖s‖ * (lam * ‖ν‖ ^ 2)) ≤ ‖s‖ ^ 2 * matrixBilinearForm A ν ν := by
          rw [← mul_assoc, ← sq]; exact mul_le_mul_of_nonneg_left hq (sq_nonneg _)
      _ ≤ ‖s‖ * (Lam * ‖ν‖) := by rw [hss]; linarith
  have hLam : 0 ≤ Lam := by nlinarith [(abs_nonneg _).trans (hA' ν ν), mul_pos hν' hν']
  rcases eq_or_lt_of_le (norm_nonneg s) with hs | hs
  · rw [← hs, mul_zero]; exact div_nonneg hLam hlam.le
  have h2 : ‖s‖ * (lam * ‖ν‖ ^ 2) ≤ Lam * ‖ν‖ := le_of_mul_le_mul_left h1 hs
  rw [le_div_iff₀ hlam]
  nlinarith [h2, hν']

/-- **The sheared form is invariant under the reflection.** For symmetric `A` with `⟪ν, A ν⟫ ≠ 0`
and `M x = x - ⟪s, x⟫ ν`, `s` the conormal shear vector, the form `(ξ, η) ↦ ⟪M ξ, A M η⟫` is
invariant under the reflection `R` in `ν⊥`. -/
private theorem matrixBilinearForm_transvectionL_reflection {A : Matrix ι ι ℝ}
    {ν : EuclideanSpace ℝ ι} (hν : ν ≠ 0) (hq : matrixBilinearForm A ν ν ≠ 0)
    (hAs : ∀ η ξ : EuclideanSpace ℝ ι, matrixBilinearForm A η ξ = matrixBilinearForm A ξ η)
    (ξ η : EuclideanSpace ℝ ι) :
    matrixBilinearForm A (transvectionL (conormalShearVector A ν) (-ν) ((ℝ ∙ ν)ᗮ.reflection ξ))
        (transvectionL (conormalShearVector A ν) (-ν) ((ℝ ∙ ν)ᗮ.reflection η)) =
      matrixBilinearForm A (transvectionL (conormalShearVector A ν) (-ν) ξ)
        (transvectionL (conormalShearVector A ν) (-ν) η) := by
  have hsν : ⟪conormalShearVector A ν, ν⟫_ℝ = 0 := by
    rw [real_inner_comm]; exact inner_conormalShearVector_self hν hq
  have : ‖ν‖ ^ 2 ≠ 0 := by positivity
  have hM : ∀ x, transvectionL (conormalShearVector A ν) (-ν) x =
      x - ⟪conormalShearVector A ν, x⟫_ℝ • ν := fun x => by
    rw [transvectionL_apply, smul_neg, sub_eq_add_neg]
  simp only [hM, reflection_orthogonal_singleton_apply_div_norm_sq, map_sub, map_smul,
    sub_apply, smul_apply, inner_sub_right,
    inner_smul_right, hsν, smul_eq_mul, inner_conormalShearVector]
  rw [hAs ν η]
  field_simp
  ring

/-! ### The shear as a change of variables -/

section ShearMap

variable {A : Matrix ι ι ℝ} {ν : EuclideanSpace ℝ ι} {c₀ : ℝ}

/-- The affine shear `y ↦ y + (⟪ν, y⟫ - c₀) s` along the conormal shear vector `s` of `A`. When
`⟪ν, s⟫ = 0`, it fixes the hyperplane `⟪ν, y⟫ = c₀` pointwise and preserves `⟪ν, ·⟫`. -/
private def boundaryShear (A : Matrix ι ι ℝ) (ν : EuclideanSpace ℝ ι) (c₀ : ℝ)
    (h : ⟪ν, conormalShearVector A ν⟫_ℝ = 0) : EuclideanSpace ℝ ι ≃ₜ EuclideanSpace ℝ ι :=
  (transvectionEquivL h).toHomeomorph.trans (Homeomorph.subRight (c₀ • conormalShearVector A ν))

private theorem boundaryShear_apply (h : ⟪ν, conormalShearVector A ν⟫_ℝ = 0)
    (y : EuclideanSpace ℝ ι) :
    boundaryShear A ν c₀ h y =
      transvectionL ν (conormalShearVector A ν) y - c₀ • conormalShearVector A ν := by
  rw [boundaryShear, Homeomorph.trans_apply, ContinuousLinearEquiv.coe_toHomeomorph,
    transvectionEquivL_apply, Homeomorph.subRight_apply]

private theorem boundaryShear_symm_apply (h : ⟪ν, conormalShearVector A ν⟫_ℝ = 0)
    (x : EuclideanSpace ℝ ι) :
    (boundaryShear A ν c₀ h).symm x =
      transvectionL ν (-conormalShearVector A ν) x + c₀ • conormalShearVector A ν := by
  rw [Homeomorph.symm_apply_eq, boundaryShear_apply, map_add, transvectionL_transvectionL_neg h,
    map_smul, transvectionL_apply ν _ (conormalShearVector A ν), h, zero_smul, add_zero,
    add_sub_cancel_right]

private theorem coe_boundaryShear (h : ⟪ν, conormalShearVector A ν⟫_ℝ = 0) :
    ⇑(boundaryShear A ν c₀ h) =
      fun y => transvectionL ν (conormalShearVector A ν) y - c₀ • conormalShearVector A ν :=
  funext (boundaryShear_apply h)

private theorem coe_boundaryShear_symm (h : ⟪ν, conormalShearVector A ν⟫_ℝ = 0) :
    ⇑(boundaryShear A ν c₀ h).symm =
      fun x => transvectionL ν (-conormalShearVector A ν) x + c₀ • conormalShearVector A ν :=
  funext (boundaryShear_symm_apply h)

private theorem inner_boundaryShear (h : ⟪ν, conormalShearVector A ν⟫_ℝ = 0)
    (y : EuclideanSpace ℝ ι) :
    ⟪boundaryShear A ν c₀ h y, ν⟫_ℝ = ⟪y, ν⟫_ℝ := by
  rw [boundaryShear_apply, real_inner_comm, inner_sub_right, inner_transvectionL h,
    inner_smul_right, h, mul_zero, sub_zero, real_inner_comm]

/-- The shear fixes the points of the hyperplane `⟪x, ν⟫ = c₀`. -/
private theorem boundaryShear_eq_self (h : ⟪ν, conormalShearVector A ν⟫_ℝ = 0)
    {z : EuclideanSpace ℝ ι} (hz : ⟪z, ν⟫_ℝ = c₀) :
    boundaryShear A ν c₀ h z = z := by
  rw [boundaryShear_apply, transvectionL_apply, real_inner_comm, hz, add_sub_cancel_right]

private theorem dist_boundaryShear_le (h : ⟪ν, conormalShearVector A ν⟫_ℝ = 0)
    {z : EuclideanSpace ℝ ι} (hz : ⟪z, ν⟫_ℝ = c₀) (y : EuclideanSpace ℝ ι) :
    dist (boundaryShear A ν c₀ h y) z ≤
      ‖transvectionL ν (conormalShearVector A ν)‖ * dist y z := by
  conv_lhs => rw [← boundaryShear_eq_self h hz]
  rw [dist_eq_norm, dist_eq_norm, boundaryShear_apply, boundaryShear_apply,
    sub_sub_sub_cancel_right, ← map_sub]
  exact (transvectionL ν _).le_opNorm _

private theorem dist_boundaryShear_symm_le (h : ⟪ν, conormalShearVector A ν⟫_ℝ = 0)
    {z : EuclideanSpace ℝ ι} (hz : ⟪z, ν⟫_ℝ = c₀) (x : EuclideanSpace ℝ ι) :
    dist ((boundaryShear A ν c₀ h).symm x) z ≤
      ‖transvectionL ν (-conormalShearVector A ν)‖ * dist x z := by
  conv_lhs => rw [← (boundaryShear A ν c₀ h).symm_apply_apply z, boundaryShear_eq_self h hz]
  rw [dist_eq_norm, dist_eq_norm, boundaryShear_symm_apply, boundaryShear_symm_apply,
    add_sub_add_right_eq_sub, ← map_sub]
  exact (transvectionL ν _).le_opNorm _

/-- The shear preserves the Lebesgue measure: its linear part has determinant one. -/
private theorem measurePreserving_boundaryShear (h : ⟪ν, conormalShearVector A ν⟫_ℝ = 0) :
    MeasurePreserving (boundaryShear A ν c₀ h) volume volume := by
  have hdet : LinearMap.det (transvectionL ν (conormalShearVector A ν)).toLinearMap = 1 := by
    simp [h]
  have hL : MeasurePreserving (transvectionL ν (conormalShearVector A ν)) volume volume := by
    refine ⟨(transvectionL ν _).continuous.measurable, ?_⟩
    simpa [hdet] using Measure.map_linearMap_addHaar_eq_smul_addHaar volume
      (f := (transvectionL ν (conormalShearVector A ν)).toLinearMap) (by simp [hdet])
  rw [coe_boundaryShear]
  exact (measurePreserving_sub_right volume _).comp hL

private theorem fderiv_boundaryShear (h : ⟪ν, conormalShearVector A ν⟫_ℝ = 0)
    (y : EuclideanSpace ℝ ι) :
    fderiv ℝ (boundaryShear A ν c₀ h) y = transvectionL ν (conormalShearVector A ν) := by
  rw [coe_boundaryShear]
  exact ((transvectionL ν _).hasFDerivAt.sub_const _).fderiv

private theorem fderiv_boundaryShear_symm (h : ⟪ν, conormalShearVector A ν⟫_ℝ = 0)
    (x : EuclideanSpace ℝ ι) :
    fderiv ℝ (boundaryShear A ν c₀ h).symm x = transvectionL ν (-conormalShearVector A ν) := by
  rw [coe_boundaryShear_symm]
  exact ((transvectionL ν _).hasFDerivAt.add_const _).fderiv

private theorem abs_det_fderiv_boundaryShear (h : ⟪ν, conormalShearVector A ν⟫_ℝ = 0)
    (y : EuclideanSpace ℝ ι) : |(fderiv ℝ (boundaryShear A ν c₀ h) y).det| = 1 := by
  rw [fderiv_boundaryShear, det_transvectionL, h, add_zero, abs_one]

private theorem abs_det_fderiv_boundaryShear_symm (h : ⟪ν, conormalShearVector A ν⟫_ℝ = 0)
    (x : EuclideanSpace ℝ ι) : |(fderiv ℝ (boundaryShear A ν c₀ h).symm x).det| = 1 := by
  rw [fderiv_boundaryShear_symm, det_transvectionL, inner_neg_right, h, neg_zero, add_zero, abs_one]

private theorem boundaryShear_mem_iff (h : ⟪ν, conormalShearVector A ν⟫_ℝ = 0)
    {H : Set (EuclideanSpace ℝ ι)} (hH : ∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) (y : EuclideanSpace ℝ ι) :
    boundaryShear A ν c₀ h y ∈ H ↔ y ∈ H := by
  rw [hH, hH, inner_boundaryShear h]

private theorem mapsTo_boundaryShear_ball (h : ⟪ν, conormalShearVector A ν⟫_ℝ = 0)
    {z : EuclideanSpace ℝ ι} (hz : ⟪z, ν⟫_ℝ = c₀) {r κ : ℝ} (hκ : 0 < κ)
    (hL : ‖transvectionL ν (conormalShearVector A ν)‖ ≤ κ) :
    MapsTo (boundaryShear A ν c₀ h) (ball z (r / κ)) (ball z r) := fun y hy => by
  rw [mem_ball] at hy ⊢
  calc dist (boundaryShear A ν c₀ h y) z ≤ ‖transvectionL ν (conormalShearVector A ν)‖ * dist y z :=
        dist_boundaryShear_le h hz y
    _ ≤ κ * dist y z := mul_le_mul_of_nonneg_right hL dist_nonneg
    _ < κ * (r / κ) := mul_lt_mul_of_pos_left hy hκ
    _ = r := mul_div_cancel₀ r hκ.ne'

private theorem differentiable_boundaryShear (h : ⟪ν, conormalShearVector A ν⟫_ℝ = 0) :
    Differentiable ℝ (boundaryShear A ν c₀ h) := by
  rw [coe_boundaryShear]
  exact fun _ => ((transvectionL ν _).hasFDerivAt.sub_const _).differentiableAt

private theorem differentiable_boundaryShear_symm (h : ⟪ν, conormalShearVector A ν⟫_ℝ = 0) :
    Differentiable ℝ (boundaryShear A ν c₀ h).symm := by
  rw [coe_boundaryShear_symm]
  exact fun _ => ((transvectionL ν _).hasFDerivAt.add_const _).differentiableAt

/-- The preimage of `B(z, R) ∩ H` under the inverse shear lies in `U ∩ H` whenever
`B(z, κ R) ⊆ U` and the shear has norm at most `κ`. -/
private theorem preimage_boundaryShear_symm_subset (h : ⟪ν, conormalShearVector A ν⟫_ℝ = 0)
    {z : EuclideanSpace ℝ ι} (hz : ⟪z, ν⟫_ℝ = c₀) {r κ : ℝ} (hκ : 0 < κ)
    (hL : ‖transvectionL ν (conormalShearVector A ν)‖ ≤ κ) {H U : Set (EuclideanSpace ℝ ι)}
    (hH : ∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) (hball : ball z r ⊆ U) :
    (boundaryShear A ν c₀ h).symm ⁻¹' (ball z (r / κ) ∩ H) ⊆ U ∩ H := fun x hx => by
  have hxr := mapsTo_boundaryShear_ball h hz hκ hL hx.1
  have hxH := (boundaryShear_mem_iff h hH _).2 hx.2
  rw [Homeomorph.apply_symm_apply] at hxr hxH
  exact ⟨hball hxr, hxH⟩

/-- Almost-everywhere statements pull back along the measure-preserving shear. -/
private theorem ae_restrict_comp_boundaryShear (h : ⟪ν, conormalShearVector A ν⟫_ℝ = 0)
    {S T : Set (EuclideanSpace ℝ ι)} (hST : MapsTo (boundaryShear A ν c₀ h) S T)
    (hT : MeasurableSet T) {p : EuclideanSpace ℝ ι → Prop} (hp : ∀ᵐ x ∂volume.restrict T, p x) :
    ∀ᵐ y ∂volume.restrict S, p (boundaryShear A ν c₀ h y) :=
  ae_restrict_of_ae_restrict_of_subset hST
    (((measurePreserving_boundaryShear h).restrict_preimage hT).quasiMeasurePreserving.ae hp)

/-- The pulled-back coefficients of a constant matrix are constant, with no lower-order terms. -/
private theorem energyFormH1_pullback_boundaryShear (h : ⟪ν, conormalShearVector A ν⟫_ℝ = 0)
    (z : EuclideanSpace ℝ ι) (Ω : Opens (EuclideanSpace ℝ ι)) :
    energyFormH1 (mu := volume) (Omega := Ω) (pullbackPrincipal (boundaryShear A ν c₀ h)
        fun _ => A) (pullbackDrift (boundaryShear A ν c₀ h) 0)
        (pullbackDensity (boundaryShear A ν c₀ h) 0) =
      energyFormH1 (fun _ => pullbackPrincipal (boundaryShear A ν c₀ h) (fun _ => A) z) 0 0 := by
  have hA : pullbackPrincipal (boundaryShear A ν c₀ h) (fun _ => A) =
      fun _ => pullbackPrincipal (boundaryShear A ν c₀ h) (fun _ => A) z := by
    funext y; simp only [pullbackPrincipal_apply, fderiv_boundaryShear]
  rw [hA, pullbackDrift_zero, pullbackDensity_zero]

/-- Precomposition with the shear, `W^{1,2}(V) → W^{1,2}(U)`, for open `U` mapped into `V` and a
bound `κ` on the norm of its linear part. -/
private def boundaryShearCompL (h : ⟪ν, conormalShearVector A ν⟫_ℝ = 0) {κ : ℝ}
    (hL : ‖transvectionL ν (conormalShearVector A ν)‖ ≤ κ) {U V : Opens (EuclideanSpace ℝ ι)}
    (hUV : MapsTo (boundaryShear A ν c₀ h) U V) : W1p volume V 2 →L[ℝ] W1p volume U 2 :=
  W1p.compL (boundaryShear A ν c₀ h) ENNReal.ofNat_ne_top
    (differentiable_boundaryShear h).differentiableOn (boundaryShear A ν c₀ h).injective.injOn hUV
    (fun y _ => (congrArg norm (fderiv_boundaryShear h y)).trans_le hL) one_pos
    (fun y _ => (abs_det_fderiv_boundaryShear h y).ge)

private theorem value_boundaryShearCompL_ae (h : ⟪ν, conormalShearVector A ν⟫_ℝ = 0) {κ : ℝ}
    (hL : ‖transvectionL ν (conormalShearVector A ν)‖ ≤ κ) {U V : Opens (EuclideanSpace ℝ ι)}
    (hUV : MapsTo (boundaryShear A ν c₀ h) U V) (u : W1p volume V 2) :
    W1p.value (boundaryShearCompL h hL hUV u) =ᵐ[volume.restrict U]
      fun y => W1p.value u (boundaryShear A ν c₀ h y) :=
  W1p.value_compL_ae _ _ _ _ _ _ _ _ u

/-- The weak gradient of `u ∘ P` is `K (∇u ∘ P)`, for the transposed shear `K x = x + ⟪s, x⟫ ν`. -/
private theorem gradient_boundaryShearCompL_ae (h : ⟪ν, conormalShearVector A ν⟫_ℝ = 0) {κ : ℝ}
    (hL : ‖transvectionL ν (conormalShearVector A ν)‖ ≤ κ) {U V : Opens (EuclideanSpace ℝ ι)}
    (hUV : MapsTo (boundaryShear A ν c₀ h) U V) (u : W1p volume V 2) :
    W1p.gradient (boundaryShearCompL h hL hUV u) =ᵐ[volume.restrict U]
      fun y => transvectionL (conormalShearVector A ν) ν
        (W1p.gradient u (boundaryShear A ν c₀ h y)) := by
  refine (W1p.gradient_compL_ae _ _ _ _ _ _ _ _ u).trans (ae_of_all _ fun y => ?_)
  dsimp only
  rw [fderiv_boundaryShear, adjoint_transvectionL]

end ShearMap

/-! ### The weak equation in sheared coordinates -/

omit [DecidableEq ι] in
/-- A half-ball `B(z, r) ∩ H` has finite measure. -/
private theorem volume_ball_inter_ne_top (z : EuclideanSpace ℝ ι) (r : ℝ)
    (H : Set (EuclideanSpace ℝ ι)) : volume (ball z r ∩ H) ≠ ⊤ :=
  ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono inter_subset_left)

section Transfer

variable {A : Matrix ι ι ℝ} {ν z : EuclideanSpace ℝ ι} {c₀ r κ : ℝ}
  {U H : Opens (EuclideanSpace ℝ ι)}

/-- **The weak equation in sheared coordinates.** Let `u ∈ H¹(U)` solve `-div(A ∇u) = 0` weakly
on `U ∩ H`, with `ball z r ⊆ U` and `z` on the hyperplane, and let `h ∈ H¹(ball z (r / κ))` agree
almost everywhere with `u ∘ P` for the shear `P`. Then `h` solves weakly on `ball z (r / κ) ∩ H`
the equation with the constant pulled-back matrix. -/
private theorem forall_energyFormH1_restrictL_eq_zero_of_comp_boundaryShear
    (hs : ⟪ν, conormalShearVector A ν⟫_ℝ = 0) (hH : ∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ)
    (hz : ⟪z, ν⟫_ℝ = c₀) (hκ : 0 < κ) (hL : ‖transvectionL ν (conormalShearVector A ν)‖ ≤ κ)
    (hL' : ‖transvectionL ν (-conormalShearVector A ν)‖ ≤ κ) (hball : ball z r ⊆ U)
    {u : W1p volume U 2} (hu : ∀ v : W1p0 volume (U ⊓ H) 2,
      energyFormH1 (fun _ => A) 0 0 (W1p.restrictL inf_le_left u) (v : W1p volume (U ⊓ H) 2) = 0)
    {h : W1p volume (⟨ball z (r / κ), isOpen_ball⟩ : Opens (EuclideanSpace ℝ ι)) 2}
    (hval : ∀ᵐ y ∂volume.restrict (ball z (r / κ)),
      W1p.value h y = W1p.value u (boundaryShear A ν c₀ hs y))
    (v : W1p0 volume ((⟨ball z (r / κ), isOpen_ball⟩ : Opens (EuclideanSpace ℝ ι)) ⊓ H) 2) :
    energyFormH1 (fun _ => pullbackPrincipal (boundaryShear A ν c₀ hs) (fun _ => A) z) 0 0
      (W1p.restrictL inf_le_left h)
      (v : W1p volume ((⟨ball z (r / κ), isOpen_ball⟩ : Opens (EuclideanSpace ℝ ι)) ⊓ H) 2) =
        0 := by
  set P := boundaryShear A ν c₀ hs
  have hLb : ∀ y, ‖fderiv ℝ P y‖ ≤ κ := fun y => by rw [fderiv_boundaryShear]; exact hL
  have hLb' : ∀ x, ‖fderiv ℝ P.symm x‖ ≤ κ := fun x => by rw [fderiv_boundaryShear_symm]; exact hL'
  have hPd := differentiable_boundaryShear hs (c₀ := c₀)
  -- The image `V` of `ball z (r / κ) ∩ H` under the shear lies in `U ∩ H`, where `u` solves the
  -- equation; the change of variables carries the equation back to `ball z (r / κ) ∩ H`.
  let V : Opens (EuclideanSpace ℝ ι) :=
    ⟨P.symm ⁻¹' (ball z (r / κ) ∩ H), (isOpen_ball.inter H.isOpen).preimage P.symm.continuous⟩
  have hVUH : V ≤ U ⊓ H := preimage_boundaryShear_symm_subset hs hz hκ hL hH hball
  have hu' : ∀ v : W1p0 volume V 2, energyFormH1 (fun _ => A) 0 0
      (W1p.restrictL (hVUH.trans inf_le_left) u) (v : W1p volume V 2) =
        ∫ x in V, (0 : EuclideanSpace ℝ ι → ℝ) x * W1p.value (v : W1p volume V 2) x := by
    intro v
    have h1 := energyFormH1_restrictL_eq_setIntegral (a := fun _ => A) (b := 0) (c := 0) hVUH
      (u := W1p.restrictL inf_le_left u) (f := 0) (fun v => by rw [hu v]; simp) v
    rwa [W1p.restrictL_restrictL] at h1
  have hPV : MapsTo P (ball z (r / κ) ∩ H) V := fun y hy =>
    (by rwa [P.symm_apply_apply] : P.symm (P y) ∈ ball z (r / κ) ∩ (H : Set (EuclideanSpace ℝ ι)))
  have hcomp := energyFormH1_compL_eq_setIntegral (mu := volume)
    (U := (⟨ball z (r / κ), isOpen_ball⟩ : Opens (EuclideanSpace ℝ ι)) ⊓ H) (V := V)
    hPd.differentiableOn P.injective.injOn hPV (fun y _ => hLb y) one_pos
    (fun y _ => (abs_det_fderiv_boundaryShear hs y).ge)
    (differentiable_boundaryShear_symm hs).differentiableOn (fun x hx => hx) (fun x _ => hLb' x)
    one_pos
    (fun x _ => (abs_det_fderiv_boundaryShear_symm hs x).ge) (fun y _ => P.symm_apply_apply y)
    (fun x _ => P.apply_symm_apply x) hu'
  have hid : boundaryShearCompL hs hL hPV (W1p.restrictL (hVUH.trans inf_le_left) u) =
      W1p.restrictL inf_le_left h := by
    refine W1p.ext_value (Lp.ext ?_)
    filter_upwards [value_boundaryShearCompL_ae hs hL hPV
        (W1p.restrictL (hVUH.trans inf_le_left) u),
      ae_restrict_comp_boundaryShear hs hPV V.isOpen.measurableSet
        (W1p.value_restrictL_ae (hVUH.trans inf_le_left) u),
      W1p.value_restrictL_ae inf_le_left h,
      ae_restrict_of_ae_restrict_of_subset inter_subset_left hval] with y h1 h2 h3 h4
    rw [h1, h2, h3, h4]
  have key : energyFormH1 (pullbackPrincipal P fun _ => A) (pullbackDrift P 0)
      (pullbackDensity P 0) (boundaryShearCompL hs hL
        (U := (⟨ball z (r / κ), isOpen_ball⟩ : Opens (EuclideanSpace ℝ ι)) ⊓ H) (V := V) hPV
        (W1p.restrictL (hVUH.trans inf_le_left) u)) =
      energyFormH1 (fun _ => pullbackPrincipal P (fun _ => A) z) 0 0
        (W1p.restrictL (inf_le_left : (⟨ball z (r / κ), isOpen_ball⟩ :
          Opens (EuclideanSpace ℝ ι)) ⊓ H ≤ _) h) := by
    rw [hid, energyFormH1_pullback_boundaryShear hs z]
  -- `boundaryShearCompL hs hL hPV` is by definition the `W1p.compL` appearing in `hcomp`.
  exact (congrFun key _).symm.trans ((hcomp v).trans (by simp))

/-- **Pulling a weak solution back along the shear.** Let `u ∈ H¹(U)` vanish on `U ∖ H` and
solve `-div(A ∇u) = 0` weakly on `U ∩ H`, and let `ball z r ⊆ U` with `z` on the hyperplane. If
the shear `P` and its inverse have linear parts of norm at most `κ`, then `h = u ∘ P` lies in
`H¹(ball z (r / κ))`, vanishes off `H`, has gradient `K (∇u ∘ P)` with `K` the transposed shear,
and solves weakly on `ball z (r / κ) ∩ H` the equation with the constant pulled-back matrix. -/
private theorem exists_comp_boundaryShear (hs : ⟪ν, conormalShearVector A ν⟫_ℝ = 0)
    (hH : ∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) (hz : ⟪z, ν⟫_ℝ = c₀) (hκ : 0 < κ)
    (hL : ‖transvectionL ν (conormalShearVector A ν)‖ ≤ κ)
    (hL' : ‖transvectionL ν (-conormalShearVector A ν)‖ ≤ κ) (hball : ball z r ⊆ U)
    {u : W1p volume U 2} (hu0 : ∀ᵐ x ∂volume.restrict U, x ∉ H → W1p.value u x = 0)
    (hu : ∀ v : W1p0 volume (U ⊓ H) 2,
      energyFormH1 (fun _ => A) 0 0 (W1p.restrictL inf_le_left u) (v : W1p volume (U ⊓ H) 2) = 0) :
    ∃ h : W1p volume (⟨ball z (r / κ), isOpen_ball⟩ : Opens (EuclideanSpace ℝ ι)) 2,
      (∀ v : W1p0 volume ((⟨ball z (r / κ), isOpen_ball⟩ : Opens (EuclideanSpace ℝ ι)) ⊓ H) 2,
        energyFormH1 (fun _ => pullbackPrincipal (boundaryShear A ν c₀ hs) (fun _ => A) z) 0 0
          (W1p.restrictL inf_le_left h)
          (v : W1p volume ((⟨ball z (r / κ), isOpen_ball⟩ : Opens (EuclideanSpace ℝ ι)) ⊓ H) 2) =
            0) ∧
      (∀ᵐ y ∂volume.restrict (ball z (r / κ)), y ∉ H → W1p.value h y = 0) ∧
      (∀ᵐ y ∂volume.restrict (ball z (r / κ)),
        W1p.gradient h y = transvectionL (conormalShearVector A ν) ν
          (W1p.gradient u (boundaryShear A ν c₀ hs y))) := by
  set P := boundaryShear A ν c₀ hs
  have hBr : (⟨ball z r, isOpen_ball⟩ : Opens (EuclideanSpace ℝ ι)) ≤ U := hball
  have hPY := mapsTo_boundaryShear_ball hs hz hκ hL (r := r)
  obtain ⟨h, hh⟩ : ∃ h, boundaryShearCompL hs hL (U := ⟨ball z (r / κ), isOpen_ball⟩)
      (V := ⟨ball z r, isOpen_ball⟩) hPY (W1p.restrictL hBr u) = h := ⟨_, rfl⟩
  have hval : ∀ᵐ y ∂volume.restrict (ball z (r / κ)), W1p.value h y = W1p.value u (P y) := by
    rw [← hh]
    filter_upwards [value_boundaryShearCompL_ae hs hL (U := ⟨ball z (r / κ), isOpen_ball⟩)
      (V := ⟨ball z r, isOpen_ball⟩) hPY (W1p.restrictL hBr u),
      ae_restrict_comp_boundaryShear hs hPY measurableSet_ball (W1p.value_restrictL_ae hBr u)]
      with y h1 h2
    rw [h1, h2]
  refine ⟨h, forall_energyFormH1_restrictL_eq_zero_of_comp_boundaryShear hs hH hz hκ hL hL'
    hball hu hval, ?_, ?_⟩
  · filter_upwards [hval, ae_restrict_comp_boundaryShear hs hPY measurableSet_ball
      (ae_restrict_of_ae_restrict_of_subset hball hu0)] with y h1 h2 hy
    rw [h1, h2 fun hPy => hy ((boundaryShear_mem_iff hs (H := (H : Set _)) hH y).1 hPy)]
  · rw [← hh]
    filter_upwards [gradient_boundaryShearCompL_ae hs hL (U := ⟨ball z (r / κ), isOpen_ball⟩)
      (V := ⟨ball z r, isOpen_ball⟩) hPY (W1p.restrictL hBr u),
      ae_restrict_comp_boundaryShear hs hPY measurableSet_ball
        (W1p.gradient_restrictL_ae hBr u)] with y h1 h2
    rw [h1, h2]

/-- The pulled-back matrix `B` in sheared coordinates satisfies `B(K η, K ξ) = A(η, ξ)` for the
transposed shear `K x = x + ⟪s, x⟫ ν`. -/
private theorem matrixBilinearForm_pullbackPrincipal_transvectionL
    (hs : ⟪ν, conormalShearVector A ν⟫_ℝ = 0) (η ξ : EuclideanSpace ℝ ι) :
    matrixBilinearForm (pullbackPrincipal (boundaryShear A ν c₀ hs) (fun _ => A) z)
        (transvectionL (conormalShearVector A ν) ν η)
        (transvectionL (conormalShearVector A ν) ν ξ) =
      matrixBilinearForm A η ξ := by
  have hfd := fderiv_boundaryShear hs (c₀ := c₀) z
  have h := matrixBilinearForm_pullbackPrincipal (Φ := boundaryShear A ν c₀ hs) (fun _ => A)
    (x := z) (by rw [hfd, det_transvectionL, hs, add_zero]; exact one_ne_zero) η ξ
  rwa [hfd, adjoint_transvectionL, det_transvectionL, hs, add_zero, abs_one, one_mul] at h

/-- The pulled-back matrix is invariant under the reflection in the hyperplane `ν⊥`: in sheared
coordinates the conormal direction of `A` is the normal `ν`. -/
private theorem matrixBilinearForm_pullbackPrincipal_reflection
    (hν : ν ≠ 0) (hq : matrixBilinearForm A ν ν ≠ 0)
    (hAs : ∀ η ξ : EuclideanSpace ℝ ι, matrixBilinearForm A η ξ = matrixBilinearForm A ξ η)
    (hs : ⟪ν, conormalShearVector A ν⟫_ℝ = 0) (ξ η : EuclideanSpace ℝ ι) :
    matrixBilinearForm (pullbackPrincipal (boundaryShear A ν c₀ hs) (fun _ => A) z)
        ((ℝ ∙ ν)ᗮ.reflection ξ) ((ℝ ∙ ν)ᗮ.reflection η) =
      matrixBilinearForm (pullbackPrincipal (boundaryShear A ν c₀ hs) (fun _ => A) z) ξ η := by
  set s := conormalShearVector A ν
  have hs' : ⟪s, ν⟫_ℝ = 0 := by rw [real_inner_comm]; exact hs
  have hBK := matrixBilinearForm_pullbackPrincipal_transvectionL (c₀ := c₀) (z := z) hs
  have hK : ∀ x, transvectionL s ν (transvectionL s (-ν) x) = x :=
    transvectionL_transvectionL_neg hs'
  rw [← hK ((ℝ ∙ ν)ᗮ.reflection ξ), ← hK ((ℝ ∙ ν)ᗮ.reflection η), hBK,
    matrixBilinearForm_transvectionL_reflection hν hq hAs, ← hBK, hK, hK]

/-- The energy integrand of the reflected constant coefficient `B` is that of `B` itself. -/
private theorem energyIntegrand_reflectPrincipal_pullbackPrincipal
    (hν : ν ≠ 0) (hq : matrixBilinearForm A ν ν ≠ 0)
    (hAs : ∀ η ξ : EuclideanSpace ℝ ι, matrixBilinearForm A η ξ = matrixBilinearForm A ξ η)
    (hs : ⟪ν, conormalShearVector A ν⟫_ℝ = 0) (x : EuclideanSpace ℝ ι) :
    energyIntegrand
        (reflectPrincipal ν c₀ (fun _ => pullbackPrincipal (boundaryShear A ν c₀ hs) (fun _ => A) z)
          x) (reflectDrift ν c₀ 0 x) (reflectDensity ν c₀ 0 x) =
      energyIntegrand (pullbackPrincipal (boundaryShear A ν c₀ hs) (fun _ => A) z) 0 0 := by
  rw [reflectDrift_zero, reflectDensity_zero, Pi.zero_apply, Pi.zero_apply]
  rcases lt_or_ge ⟪x, ν⟫_ℝ c₀ with hx | hx
  · rw [reflectPrincipal_of_lt hx]
    refine ContinuousLinearMap.ext fun W => ContinuousLinearMap.ext fun W' => ?_
    have h := energyIntegrand_pullback_hyperplaneReflection (ν := ν) (c₀ := c₀) (x := x)
      (a := fun _ => pullbackPrincipal (boundaryShear A ν c₀ hs) (fun _ => A) z) (b := 0) (c := 0)
      W W'
    rw [pullbackDrift_zero, pullbackDensity_zero, Pi.zero_apply, Pi.zero_apply] at h
    rw [h]
    simp only [energyIntegrand_apply, Pi.zero_apply, driftForm_apply, inner_zero_left,
      matrixBilinearForm_pullbackPrincipal_reflection hν hq hAs hs]
  · rw [reflectPrincipal_of_le hx]

/-- The pulled-back matrix is uniformly elliptic, with constants `λ / κ²` and `Λ κ²` when the
transposed shear and its inverse have norm at most `κ`. -/
private theorem toQuadraticForm'_pullbackPrincipal_boundaryShear_bounds {lam Lam : ℝ}
    (hlam : 0 < lam) (hs : ⟪ν, conormalShearVector A ν⟫_ℝ = 0)
    (hA : ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hA' : ∀ η ξ : EuclideanSpace ℝ ι, |η ⬝ᵥ (A *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖) (hLam : 0 ≤ Lam)
    (hκ : 0 < κ) (hK : ‖transvectionL (conormalShearVector A ν) ν‖ ≤ κ)
    (hK' : ‖transvectionL (conormalShearVector A ν) (-ν)‖ ≤ κ) (ξ : EuclideanSpace ℝ ι) :
    lam / κ ^ 2 * ‖ξ‖ ^ 2 ≤
        (pullbackPrincipal (boundaryShear A ν c₀ hs) (fun _ => A) z).toQuadraticForm' ξ ∧
      (pullbackPrincipal (boundaryShear A ν c₀ hs) (fun _ => A) z).toQuadraticForm' ξ ≤
        Lam * κ ^ 2 * ‖ξ‖ ^ 2 := by
  set s := conormalShearVector A ν
  set ζ := transvectionL s (-ν) ξ
  have hξ : transvectionL s ν ζ = ξ :=
    transvectionL_transvectionL_neg (by rw [real_inner_comm]; exact hs) ξ
  have hQ : (pullbackPrincipal (boundaryShear A ν c₀ hs) (fun _ => A) z).toQuadraticForm' ξ =
      A.toQuadraticForm' ζ := by
    rw [toQuadraticForm'_apply, toQuadraticForm'_apply, ← matrixBilinearForm_apply,
      ← matrixBilinearForm_apply, ← hξ, matrixBilinearForm_pullbackPrincipal_transvectionL hs]
  have h1 : ‖ξ‖ ≤ κ * ‖ζ‖ := by
    conv_lhs => rw [← hξ]
    exact ((transvectionL s ν).le_opNorm ζ).trans (mul_le_mul_of_nonneg_right hK (norm_nonneg _))
  have h2 : ‖ζ‖ ≤ κ * ‖ξ‖ :=
    ((transvectionL s (-ν)).le_opNorm ξ).trans (mul_le_mul_of_nonneg_right hK' (norm_nonneg _))
  rw [hQ]
  have hlo := hA ζ
  have hup : A.toQuadraticForm' ζ ≤ Lam * ‖ζ‖ * ‖ζ‖ := by
    rw [toQuadraticForm'_apply]; exact (le_abs_self _).trans (hA' ζ ζ)
  constructor
  · have h3 : ‖ξ‖ ^ 2 ≤ κ ^ 2 * ‖ζ‖ ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) h1 2
    calc lam / κ ^ 2 * ‖ξ‖ ^ 2 ≤ lam / κ ^ 2 * (κ ^ 2 * ‖ζ‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = lam * ‖ζ‖ ^ 2 := by field_simp
      _ ≤ _ := hlo
  · calc A.toQuadraticForm' ζ ≤ Lam * ‖ζ‖ * ‖ζ‖ := hup
      _ = Lam * ‖ζ‖ ^ 2 := by ring
      _ ≤ Lam * (κ * ‖ξ‖) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) h2 2) hLam
      _ = Lam * κ ^ 2 * ‖ξ‖ ^ 2 := by ring

/-- **The odd reflection solves the constant-coefficient equation.** If `h ∈ H¹(B(z, R))`
vanishes off `H` and solves weakly on `B(z, R) ∩ H` the equation with the pulled-back matrix
`B`, then its odd reflection `h - h ∘ ρ` solves the same equation weakly on all of `B(z, R)`. -/
private theorem energyFormH1_sub_compHyperplaneReflectionL_eq_zero (hν : ν ≠ 0)
    (hq : matrixBilinearForm A ν ν ≠ 0)
    (hAs : ∀ η ξ : EuclideanSpace ℝ ι, matrixBilinearForm A η ξ = matrixBilinearForm A ξ η)
    (hs : ⟪ν, conormalShearVector A ν⟫_ℝ = 0) (hH : ∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ)
    (hz : ⟪z, ν⟫_ℝ = c₀) {R : ℝ}
    {h : W1p volume (⟨ball z R, isOpen_ball⟩ : Opens (EuclideanSpace ℝ ι)) 2}
    (heq : ∀ v : W1p0 volume ((⟨ball z R, isOpen_ball⟩ : Opens (EuclideanSpace ℝ ι)) ⊓ H) 2,
      energyFormH1 (fun _ => pullbackPrincipal (boundaryShear A ν c₀ hs) (fun _ => A) z) 0 0
        (W1p.restrictL inf_le_left h)
        (v : W1p volume ((⟨ball z R, isOpen_ball⟩ : Opens (EuclideanSpace ℝ ι)) ⊓ H) 2) = 0)
    (hvan : ∀ᵐ y ∂volume.restrict (ball z R), y ∉ H → W1p.value h y = 0)
    (v : W1p0 volume (⟨ball z R, isOpen_ball⟩ : Opens (EuclideanSpace ℝ ι)) 2) :
    energyFormH1 (fun _ => pullbackPrincipal (boundaryShear A ν c₀ hs) (fun _ => A) z) 0 0
      (h - W1p.compHyperplaneReflectionL (U := ⟨ball z R, isOpen_ball⟩) ENNReal.ofNat_ne_top ν c₀
        (mapsTo_hyperplaneReflection_ball hz R) h)
      (v : W1p volume (⟨ball z R, isOpen_ball⟩ : Opens (EuclideanSpace ℝ ι)) 2) = 0 := by
  -- The reflected coefficient has the energy integrand of `B`, so the reflection principle
  -- applies with the constant coefficient `B` on the whole ball.
  have hint := energyIntegrand_reflectPrincipal_pullbackPrincipal (z := z) (c₀ := c₀) hν hq hAs hs
  have hcoeff : MemLp (fun x => energyIntegrand (reflectPrincipal ν c₀
      (fun _ => pullbackPrincipal (boundaryShear A ν c₀ hs) (fun _ => A) z) x)
        (reflectDrift ν c₀ 0 x) (reflectDensity ν c₀ 0 x)) ⊤ (volume.restrict (ball z R)) := by
    rw [show (fun x => energyIntegrand (reflectPrincipal ν c₀
        (fun _ => pullbackPrincipal (boundaryShear A ν c₀ hs) (fun _ => A) z) x)
          (reflectDrift ν c₀ 0 x) (reflectDensity ν c₀ 0 x)) =
        fun _ => energyIntegrand (pullbackPrincipal (boundaryShear A ν c₀ hs) (fun _ => A) z)
          0 0 from funext hint]
    exact memLp_top_const
      (energyIntegrand (pullbackPrincipal (boundaryShear A ν c₀ hs) (fun _ => A) z) 0 0)
  have he : energyFormH1 (mu := volume)
      (Omega := (⟨ball z R, isOpen_ball⟩ : Opens (EuclideanSpace ℝ ι)))
      (reflectPrincipal ν c₀ fun _ => pullbackPrincipal (boundaryShear A ν c₀ hs)
        (fun _ => A) z) (reflectDrift ν c₀ 0) (reflectDensity ν c₀ 0) =
      energyFormH1 (fun _ => pullbackPrincipal (boundaryShear A ν c₀ hs) (fun _ => A) z) 0 0 := by
    funext u' v'
    rw [energyFormH1_def, energyFormH1_def]
    simp only [hint, Pi.zero_apply]
  have hr := energyFormH1_reflectPrincipal_sub_compHyperplaneReflectionL (mu := volume)
    (U := ⟨ball z R, isOpen_ball⟩) (H := H) hν hH (mapsTo_hyperplaneReflection_ball hz R) hcoeff
    hvan (ℓ := 0) (fun v => (heq v).trans (zero_apply _).symm) v
  exact (congrFun (congrFun he _) _).symm.trans (hr.trans (zero_apply _))

/-- **Back to `u`.** If `∇h = K (∇u ∘ P)` on `B(z, r / κ)` for the shear `P` and its transpose
`K`, both of norm at most `κ`, then for every real `t`,
`∫_{B(z, r / κ) ∩ H} ‖∇h - t ν‖² ≤ κ² ∫_{B(z, r) ∩ H} ‖∇u - t ν‖²`. -/
private theorem setIntegral_ball_inter_norm_gradient_sub_sq_le_of_comp_boundaryShear
    (hs : ⟪ν, conormalShearVector A ν⟫_ℝ = 0) (hH : ∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ)
    (hz : ⟪z, ν⟫_ℝ = c₀) (hκ : 0 < κ) (hL : ‖transvectionL ν (conormalShearVector A ν)‖ ≤ κ)
    (hK : ‖transvectionL (conormalShearVector A ν) ν‖ ≤ κ) (hball : ball z r ⊆ U)
    {u : W1p volume U 2}
    {h : W1p volume (⟨ball z (r / κ), isOpen_ball⟩ : Opens (EuclideanSpace ℝ ι)) 2}
    (hgrad : ∀ᵐ y ∂volume.restrict (ball z (r / κ)), W1p.gradient h y =
      transvectionL (conormalShearVector A ν) ν (W1p.gradient u (boundaryShear A ν c₀ hs y)))
    (t : ℝ) :
    ∫ y in ball z (r / κ) ∩ H, ‖W1p.gradient h y - t • ν‖ ^ 2 ≤
      κ ^ 2 * ∫ x in ball z r ∩ H, ‖W1p.gradient u x - t • ν‖ ^ 2 := by
  set P := boundaryShear A ν c₀ hs
  have hP := measurePreserving_boundaryShear hs (c₀ := c₀)
  have hPe := P.measurableEmbedding
  have hgint : IntegrableOn (fun x => ‖W1p.gradient u x - t • ν‖ ^ 2) (ball z r ∩ H) :=
    (Lp.memLp (W1p.gradient u)).integrableOn_norm_sub_sq_of_subset
      (inter_subset_left.trans hball) (volume_ball_inter_ne_top z r H) (t • ν)
  -- The shear maps `B(z, r / κ) ∩ H` into `B(z, r) ∩ H`.
  have hYP : ball z (r / κ) ∩ (H : Set (EuclideanSpace ℝ ι)) ⊆ P ⁻¹' (ball z r ∩ H) :=
    fun y hy => ⟨mapsTo_boundaryShear_ball hs hz hκ hL hy.1,
      (boundaryShear_mem_iff hs (H := (H : Set _)) hH y).2 hy.2⟩
  have hgPint : IntegrableOn (fun y => ‖W1p.gradient u (P y) - t • ν‖ ^ 2)
      (P ⁻¹' (ball z r ∩ H)) := (hP.integrableOn_comp_preimage hPe).2 hgint
  have hKν : transvectionL (conormalShearVector A ν) ν ν = ν :=
    transvectionL_apply_of_inner_eq_zero ν ((real_inner_comm ν _).trans hs)
  calc _ ≤ ∫ y in ball z (r / κ) ∩ H, κ ^ 2 * ‖W1p.gradient u (P y) - t • ν‖ ^ 2 := by
        have hhint : IntegrableOn (fun y => ‖W1p.gradient h y - t • ν‖ ^ 2) (ball z (r / κ)) :=
          (Lp.memLp (W1p.gradient h)).integrableOn_norm_sub_sq_of_subset subset_rfl
            measure_ball_lt_top.ne (t • ν)
        refine integral_mono_ae (hhint.mono_set inter_subset_left)
          ((hgPint.mono_set hYP).const_mul _) ?_
        filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_left hgrad] with y hy
        rw [hy, ← mul_pow]
        have hb := (transvectionL (conormalShearVector A ν) ν).le_opNorm
          (W1p.gradient u (P y) - t • ν)
        rw [map_sub, map_smul, hKν] at hb
        gcongr
        exact hb.trans (mul_le_mul_of_nonneg_right hK (norm_nonneg _))
    _ = κ ^ 2 * ∫ y in ball z (r / κ) ∩ H, ‖W1p.gradient u (P y) - t • ν‖ ^ 2 :=
        integral_const_mul _ _
    _ ≤ κ ^ 2 * ∫ x in ball z r ∩ H, ‖W1p.gradient u x - t • ν‖ ^ 2 := by
        gcongr
        rw [← hP.setIntegral_preimage_emb hPe (fun x => ‖W1p.gradient u x - t • ν‖ ^ 2)]
        exact setIntegral_mono_set hgPint (Filter.Eventually.of_forall fun _ => by positivity)
          (Filter.Eventually.of_forall hYP)

/-- If `∇w = K (∇u ∘ P)` above the hyperplane, then for every vector `c`,
`∫_{B(z, ρ) ∩ H} ‖∇u - K⁻¹ c‖² ≤ κ² ∫_{B(z, κ ρ)} ‖∇w - c‖²`. -/
private theorem setIntegral_ball_inter_norm_gradient_sub_sq_le_of_boundaryShear
    (hs : ⟪ν, conormalShearVector A ν⟫_ℝ = 0) (hH : ∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ)
    (hz : ⟪z, ν⟫_ℝ = c₀) (hκ : 0 < κ) (hL' : ‖transvectionL ν (-conormalShearVector A ν)‖ ≤ κ)
    (hK' : ‖transvectionL (conormalShearVector A ν) (-ν)‖ ≤ κ) {ρ : ℝ} {u : W1p volume U 2}
    (hρU : ball z ρ ⊆ U)
    {w : W1p volume (⟨ball z r, isOpen_ball⟩ : Opens (EuclideanSpace ℝ ι)) 2}
    (hw : ∀ᵐ y ∂volume.restrict (ball z r ∩ H), W1p.gradient w y =
      transvectionL (conormalShearVector A ν) ν (W1p.gradient u (boundaryShear A ν c₀ hs y)))
    (hρ : κ * ρ ≤ r) (c : EuclideanSpace ℝ ι) :
    ∫ x in ball z ρ ∩ H, ‖W1p.gradient u x - transvectionL (conormalShearVector A ν) (-ν) c‖ ^ 2 ≤
      κ ^ 2 * ∫ y in ball z (κ * ρ), ‖W1p.gradient w y - c‖ ^ 2 := by
  set s := conormalShearVector A ν
  set P := boundaryShear A ν c₀ hs
  have hP := measurePreserving_boundaryShear hs (c₀ := c₀)
  have hPe := P.measurableEmbedding
  have hgint : IntegrableOn (fun x => ‖W1p.gradient u x - transvectionL s (-ν) c‖ ^ 2)
      (ball z ρ ∩ H) :=
    (Lp.memLp (W1p.gradient u)).integrableOn_norm_sub_sq_of_subset
      (inter_subset_left.trans hρU) (volume_ball_inter_ne_top z ρ H) _
  have hwint : IntegrableOn (fun y => ‖W1p.gradient w y - c‖ ^ 2) (ball z r) :=
    (Lp.memLp (W1p.gradient w)).integrableOn_norm_sub_sq_of_subset subset_rfl
      measure_ball_lt_top.ne c
  -- The preimage of `B(z, ρ) ∩ H` under the shear lies in `B(z, κ ρ) ∩ H`.
  have hpre : P ⁻¹' (ball z ρ ∩ H) ⊆ ball z (κ * ρ) ∩ H := fun y hy => by
    refine ⟨?_, by
      have h := hy.2
      rwa [SetLike.mem_coe, hH, inner_boundaryShear hs, ← hH] at h⟩
    have hy1 : dist (P y) z < ρ := hy.1
    rw [mem_ball]
    calc dist y z = dist (P.symm (P y)) z := by rw [P.symm_apply_apply]
      _ ≤ ‖transvectionL ν (-s)‖ * dist (P y) z := dist_boundaryShear_symm_le hs hz (P y)
      _ ≤ κ * dist (P y) z := mul_le_mul_of_nonneg_right hL' dist_nonneg
      _ < κ * ρ := mul_lt_mul_of_pos_left hy1 hκ
  have hpre' : P ⁻¹' (ball z ρ ∩ H) ⊆ ball z r ∩ H :=
    hpre.trans (inter_subset_inter_left _ (ball_subset_ball hρ))
  have hKinv : ∀ a, transvectionL s (-ν) (transvectionL s ν a) = a := fun a => by
    simpa using transvectionL_transvectionL_neg (ν := s) (s := -ν)
      (by rw [inner_neg_right, real_inner_comm, hs, neg_zero]) a
  rw [← hP.setIntegral_preimage_emb hPe (fun x => ‖W1p.gradient u x - transvectionL s (-ν) c‖ ^ 2)]
  calc _ ≤ ∫ y in P ⁻¹' (ball z ρ ∩ H), κ ^ 2 * ‖W1p.gradient w y - c‖ ^ 2 := by
        refine integral_mono_ae ((hP.integrableOn_comp_preimage hPe).2 hgint)
          ((hwint.mono_set (hpre'.trans inter_subset_left)).const_mul _) ?_
        filter_upwards [ae_restrict_of_ae_restrict_of_subset hpre' hw] with y hy
        rw [hy, ← hKinv (W1p.gradient u (P y)), ← map_sub, hKinv, ← mul_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (((transvectionL s (-ν)).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right hK' (norm_nonneg _))) 2
    _ = κ ^ 2 * ∫ y in P ⁻¹' (ball z ρ ∩ H), ‖W1p.gradient w y - c‖ ^ 2 := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (setIntegral_mono_set
          (hwint.mono_set (ball_subset_ball hρ))
          (Filter.Eventually.of_forall fun _ => by positivity)
          (Filter.Eventually.of_forall (hpre.trans inter_subset_left))) (by positivity)

/-- The constants of the shear: for `λ ‖ξ‖² ≤ ξᵀ A ξ` and `|ηᵀ A ξ| ≤ Λ ‖η‖ ‖ξ‖` with `λ > 0`, the
conormal shear vector is orthogonal to `ν`, and the shear, its inverse and their transposes have
norm at most `1 + Λ / λ`. -/
private theorem boundaryShear_constants {lam Lam : ℝ} (hlam : 0 < lam) (hν : ν ≠ 0)
    (hA : ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hA' : ∀ η ξ : EuclideanSpace ℝ ι, |η ⬝ᵥ (A *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖) :
    ⟪ν, conormalShearVector A ν⟫_ℝ = 0 ∧ matrixBilinearForm A ν ν ≠ 0 ∧ 0 ≤ Lam ∧
      ‖transvectionL ν (conormalShearVector A ν)‖ ≤ 1 + Lam / lam ∧
      ‖transvectionL ν (-conormalShearVector A ν)‖ ≤ 1 + Lam / lam ∧
      ‖transvectionL (conormalShearVector A ν) ν‖ ≤ 1 + Lam / lam ∧
      ‖transvectionL (conormalShearVector A ν) (-ν)‖ ≤ 1 + Lam / lam := by
  have hq : 0 < matrixBilinearForm A ν ν := by
    have h := hA ν
    rw [toQuadraticForm'_apply, ← matrixBilinearForm_apply] at h
    exact lt_of_lt_of_le (by have := norm_pos_iff.2 hν; positivity) h
  have hN := norm_mul_norm_conormalShearVector_le hlam hν hA hA'
  have h0 : 0 ≤ Lam / lam := (by positivity : (0 : ℝ) ≤ ‖ν‖ * _).trans hN
  have hN' : 1 + ‖conormalShearVector A ν‖ * ‖ν‖ ≤ 1 + Lam / lam := by
    rw [mul_comm]; linarith
  refine ⟨inner_conormalShearVector_self hν hq.ne', hq.ne', ?_, ?_, ?_, ?_, ?_⟩
  · have h := mul_nonneg h0 hlam.le
    rwa [div_mul_cancel₀ _ hlam.ne'] at h
  · exact (norm_transvectionL_le _ _).trans (by linarith)
  · exact (norm_transvectionL_le _ _).trans (by rw [norm_neg]; linarith)
  · exact (norm_transvectionL_le _ _).trans hN'
  · exact (norm_transvectionL_le _ _).trans (by rw [norm_neg]; exact hN')

/-- **The reflected sheared solution.** With `κ = 1 + Λ / λ`, there are a constant matrix `B` with
ellipticity constants `λ / κ²` and `Λ κ²`, a linear map `M` fixing `ν` and a weak solution `w` of
`-div(B ∇w) = 0` on `B(z, r / κ)`, odd under the reflection, whose ball integrals control the
half-ball integrals of `u`, and conversely. -/
private theorem exists_boundaryReflection {lam Lam : ℝ} (hlam : 0 < lam)
    (hA : ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hA' : ∀ η ξ : EuclideanSpace ℝ ι, |η ⬝ᵥ (A *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖)
    (hν : ν ≠ 0) (hH : ∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) (hz : ⟪z, ν⟫_ℝ = c₀) (hball : ball z r ⊆ U)
    {u : W1p volume U 2} (hu0 : ∀ᵐ x ∂volume.restrict U, x ∉ H → W1p.value u x = 0)
    (hu : ∀ v : W1p0 volume (U ⊓ H) 2,
      energyFormH1 (fun _ => A) 0 0 (W1p.restrictL inf_le_left u) (v : W1p volume (U ⊓ H) 2) = 0) :
    ∃ (B : Matrix ι ι ℝ) (M : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)
      (w : W1p volume (⟨ball z (r / (1 + Lam / lam)), isOpen_ball⟩ :
        Opens (EuclideanSpace ℝ ι)) 2),
      (∀ ξ : EuclideanSpace ℝ ι, lam / (1 + Lam / lam) ^ 2 * ‖ξ‖ ^ 2 ≤ B.toQuadraticForm' ξ) ∧
      (∀ ξ : EuclideanSpace ℝ ι, B.toQuadraticForm' ξ ≤ Lam * (1 + Lam / lam) ^ 2 * ‖ξ‖ ^ 2) ∧
      (∀ v : W1p0 volume (⟨ball z (r / (1 + Lam / lam)), isOpen_ball⟩ :
          Opens (EuclideanSpace ℝ ι)) 2,
        energyFormH1 (fun _ => B) 0 0 w (v : W1p volume (⟨ball z (r / (1 + Lam / lam)),
          isOpen_ball⟩ : Opens (EuclideanSpace ℝ ι)) 2) = 0) ∧
      (∀ ρ, (1 + Lam / lam) * ρ ≤ r / (1 + Lam / lam) → ball z ρ ⊆ U →
        ∀ c, ∫ x in ball z ρ ∩ H, ‖W1p.gradient u x - M c‖ ^ 2 ≤
          (1 + Lam / lam) ^ 2 * ∫ y in ball z ((1 + Lam / lam) * ρ), ‖W1p.gradient w y - c‖ ^ 2) ∧
      (∀ t : ℝ, M (t • ν) = t • ν) ∧
      (∀ᵐ y ∂volume.restrict (ball z (r / (1 + Lam / lam))), W1p.gradient w
        (hyperplaneReflection ν c₀ y) = -(ℝ ∙ ν)ᗮ.reflection (W1p.gradient w y)) ∧
      ∀ t : ℝ, ∫ y in ball z (r / (1 + Lam / lam)), ‖W1p.gradient w y - t • ν‖ ^ 2 ≤
        2 * (1 + Lam / lam) ^ 2 * ∫ x in ball z r ∩ H, ‖W1p.gradient u x - t • ν‖ ^ 2 := by
  -- Only the symmetric part of `A` enters the weak equation, with the same constants.
  wlog hAs : A.IsSymm generalizing A
  · exact this (by simpa using hA) (abs_dotProduct_coefficientSymmetricPart_mulVec_le hA')
      (fun v => (energyFormH1_const_coefficientSymmetricPart A _ v).trans (hu v))
      (coefficientSymmetricPart_isSymm A)
  obtain ⟨hs, hq, hLam, hL, hL', hK, hK'⟩ := boundaryShear_constants hlam hν hA hA'
  set κ := 1 + Lam / lam
  have hκ : 0 < κ := by positivity
  have hAs' : ∀ η ξ : EuclideanSpace ℝ ι, matrixBilinearForm A η ξ = matrixBilinearForm A ξ η :=
    fun η ξ => by rw [← matrixBilinearForm_transpose_apply, hAs.eq]
  -- The odd reflection `w` of `h = u ∘ P` across the hyperplane.
  obtain ⟨h, heq, hvan, hgrad⟩ := exists_comp_boundaryShear hs hH hz hκ hL hL' hball hu0 hu
  have hYρ := mapsTo_hyperplaneReflection_ball hz (r / κ)
  -- Above the hyperplane the reflected part vanishes, so `∇w = ∇h = K (∇u ∘ P)` there.
  have hw1 : ∀ᵐ y ∂volume.restrict (ball z (r / κ) ∩ H),
      W1p.gradient (h - W1p.compHyperplaneReflectionL (U := ⟨ball z (r / κ), isOpen_ball⟩)
        ENNReal.ofNat_ne_top ν c₀ hYρ h) y =
      transvectionL (conormalShearVector A ν) ν (W1p.gradient u (boundaryShear A ν c₀ hs y)) := by
    have hgh0 := W1p.gradient_ae_eq_zero_of_value_ae_eq_zero_of_inner_lt hH hvan
    have hsub : MeasurableSet (ball z (r / κ) ∩ (H : Set (EuclideanSpace ℝ ι))) :=
      measurableSet_ball.inter H.isOpen.measurableSet
    filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_left
      (Lp.coeFn_sub (W1p.gradient h) (W1p.gradient (W1p.compHyperplaneReflectionL
        (U := ⟨ball z (r / κ), isOpen_ball⟩) ENNReal.ofNat_ne_top ν c₀ hYρ h))),
      ae_restrict_of_ae_restrict_of_subset inter_subset_left
        (W1p.gradient_compHyperplaneReflectionL_ae ENNReal.ofNat_ne_top hYρ h),
      ae_restrict_of_ae_restrict_of_subset inter_subset_left
        ((measurePreserving_restrict_hyperplaneReflection hYρ
          measurableSet_ball).quasiMeasurePreserving.ae hgh0),
      ae_restrict_of_ae_restrict_of_subset inter_subset_left hgrad, ae_restrict_mem hsub]
      with y h1 h2 h3 h4 hy
    rw [W1p.gradient_sub, h1, Pi.sub_apply, h2,
      h3 ((inner_hyperplaneReflection_lt_iff hν c₀).2 ((hH y).1 hy.2)), map_zero, sub_zero, h4]
  refine ⟨_, _, _, fun ξ => (toQuadraticForm'_pullbackPrincipal_boundaryShear_bounds (z := z)
    hlam hs hA hA' hLam hκ hK hK' ξ).1, fun ξ =>
    (toQuadraticForm'_pullbackPrincipal_boundaryShear_bounds hlam hs hA hA' hLam hκ hK hK' ξ).2,
    energyFormH1_sub_compHyperplaneReflectionL_eq_zero hν hq hAs' hs hH hz heq hvan,
    fun ρ hρ hρU c => setIntegral_ball_inter_norm_gradient_sub_sq_le_of_boundaryShear hs hH hz hκ
      hL' hK' hρU hw1 hρ c, fun t => ?_,
    W1p.gradient_sub_compHyperplaneReflectionL_hyperplaneReflection_ae ENNReal.ofNat_ne_top hYρ h,
    fun t => ?_⟩
  · rw [map_smul, transvectionL_apply_of_inner_eq_zero _ ((real_inner_comm ν _).trans hs)]
  · calc _ ≤ 2 * ∫ y in ball z (r / κ) ∩ H, ‖W1p.gradient h y - t • ν‖ ^ 2 :=
          W1p.setIntegral_norm_gradient_sub_compHyperplaneReflectionL_sub_smul_sq_le hν hH hYρ
            measure_ball_lt_top.ne hvan t
      _ ≤ 2 * (κ ^ 2 * ∫ x in ball z r ∩ H, ‖W1p.gradient u x - t • ν‖ ^ 2) := by
          gcongr
          exact setIntegral_ball_inter_norm_gradient_sub_sq_le_of_comp_boundaryShear hs hH hz hκ hL
            hK hball hgrad t
      _ = _ := by ring

end Transfer

/-! ### Decay estimates -/

section Decay

/-- The bookkeeping of the decay estimates: a bound at radii `κ ρ ≤ r / κ` and the trivial bound
at the other radii combine into one decay estimate with exponent `m`. -/
private theorem le_mul_div_pow_mul_of_le {X Z D κ ρ r : ℝ} (m : ℕ) (hκ : 1 ≤ κ) (hρ : 0 < ρ)
    (hρr : ρ ≤ r) (hZ : 0 ≤ Z) (hD : 0 ≤ D)
    (hsmall : κ * ρ ≤ r / κ → X ≤ κ ^ 2 * (D * (κ * ρ / (r / κ)) ^ m * (2 * κ ^ 2 * Z)))
    (hlarge : X ≤ Z) :
    X ≤ (2 * (κ ^ 2) ^ (m + 2) * D + (κ ^ 2) ^ m + 1) * (ρ / r) ^ m * Z := by
  have hr : 0 < r := hρ.trans_le hρr
  have hκ0 : 0 < κ := one_pos.trans_le hκ
  have hp : 0 ≤ (κ ^ 2) ^ m := by positivity
  rcases le_or_gt (κ * ρ) (r / κ) with hs | hl
  · have hscale : (κ * ρ / (r / κ)) ^ m = (κ ^ 2) ^ m * (ρ / r) ^ m := by
      rw [← mul_pow]; congr 1; field_simp
    calc X ≤ κ ^ 2 * (D * (κ * ρ / (r / κ)) ^ m * (2 * κ ^ 2 * Z)) := hsmall hs
      _ = 2 * (κ ^ 2) ^ (m + 2) * D * (ρ / r) ^ m * Z := by rw [hscale]; ring
      _ ≤ _ := by gcongr; linarith
  · have h1 : 1 ≤ (κ ^ 2) ^ m * (ρ / r) ^ m := by
      rw [← mul_pow]
      refine one_le_pow₀ ?_
      rw [div_lt_iff₀ hκ0] at hl
      rw [mul_div_assoc', le_div_iff₀ hr]
      nlinarith
    calc X ≤ Z := hlarge
      _ ≤ (κ ^ 2) ^ m * (ρ / r) ^ m * Z := le_mul_of_one_le_left hZ h1
      _ ≤ _ := by
          gcongr
          nlinarith [(by positivity : (0 : ℝ) ≤ 2 * (κ ^ 2) ^ (m + 2) * D)]

/-- **Decay of the `L²` mass of the gradient at a flat boundary, for constant coefficients.** Let
`n` be the dimension and `0 < λ`. There is `C > 0`, depending only on `n`, `λ` and `Λ`, with the
following property. Let `H = {x | c₀ < ⟪x, ν⟫}` with `ν ≠ 0`, let `z` lie on the boundary
hyperplane, and let `A` be a matrix with `λ ‖ξ‖² ≤ ξᵀ A ξ` and `|ηᵀ A ξ| ≤ Λ ‖η‖ ‖ξ‖`.
Let `u ∈ H¹(U)` vanish on `U ∖ H`, where `ball z r ⊆ U`, and solve `-div(A ∇u) = 0` weakly on
`U ∩ H`. Then for `0 ≤ ρ ≤ r`,

`∫_{B(z, ρ) ∩ H} ‖∇u‖² ≤ C (ρ / r)ⁿ ∫_{B(z, r) ∩ H} ‖∇u‖²`. -/
theorem exists_setIntegral_ball_inter_norm_gradient_sq_le {lam Lam : ℝ} (hlam : 0 < lam) :
    ∃ C : ℝ, 0 < C ∧ ∀ {U H : Opens (EuclideanSpace ℝ ι)} {A : Matrix ι ι ℝ}
      {ν z : EuclideanSpace ℝ ι} {c₀ r ρ : ℝ} {u : W1p volume U 2},
      (∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ) →
      (∀ η ξ : EuclideanSpace ℝ ι, |η ⬝ᵥ (A *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖) → ν ≠ 0 →
      (∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) → ⟪z, ν⟫_ℝ = c₀ → ball z r ⊆ U →
      (∀ᵐ x ∂volume.restrict U, x ∉ H → W1p.value u x = 0) →
      (∀ v : W1p0 volume (U ⊓ H) 2, energyFormH1 (fun _ => A) 0 0 (W1p.restrictL inf_le_left u)
        (v : W1p volume (U ⊓ H) 2) = 0) →
      0 ≤ ρ → ρ ≤ r →
      ∫ x in ball z ρ ∩ H, ‖W1p.gradient u x‖ ^ 2 ≤
        C * (ρ / r) ^ Fintype.card ι * ∫ x in ball z r ∩ H, ‖W1p.gradient u x‖ ^ 2 := by
  set κ := 1 + Lam / lam
  set n := Fintype.card ι
  set D := 2 ^ n * √(Lam * κ ^ 2 / (lam / κ ^ 2)) ^ n
  refine ⟨2 * (κ ^ 2) ^ (n + 2) * D + (κ ^ 2) ^ n + 1, by positivity, ?_⟩
  intro U H A ν z c₀ r ρ u hA hA' hν hH hz hball hu0 hu hρ hρr
  obtain ⟨-, -, hLam, -⟩ := boundaryShear_constants hlam hν hA hA'
  have hI : 0 ≤ ∫ x in ball z r ∩ H, ‖W1p.gradient u x‖ ^ 2 :=
    setIntegral_nonneg (measurableSet_ball.inter H.isOpen.measurableSet) fun _ _ => by positivity
  rcases hρ.eq_or_lt with rfl | hρ0
  · rw [ball_zero, empty_inter, Measure.restrict_empty, integral_zero_measure]
    positivity
  refine le_mul_div_pow_mul_of_le n (le_add_of_nonneg_right (div_nonneg hLam hlam.le)) hρ0 hρr hI
    (by positivity) (fun hsmall => ?_) (setIntegral_mono_set
      (by simpa using ((Lp.memLp (W1p.gradient u)).integrableOn_norm_sub_sq_of_subset
        (inter_subset_left.trans hball) (volume_ball_inter_ne_top z r H) 0))
      (Filter.Eventually.of_forall fun _ => by positivity)
      (Filter.Eventually.of_forall (inter_subset_inter_left _ (ball_subset_ball hρr))))
  obtain ⟨B, M, w, hB, hB', hw, hT, -, -, hR⟩ :=
    exists_boundaryReflection hlam hA hA' hν hH hz hball hu0 hu
  have : 0 < κ := add_pos_of_pos_of_nonneg one_pos (div_nonneg hLam hlam.le)
  have hr : 0 < r := hρ0.trans_le hρr
  have h1 := hT ρ hsmall ((ball_subset_ball hρr).trans hball) 0
  simp only [map_zero, sub_zero] at h1
  have h3 := hR 0
  simp only [zero_smul, sub_zero] at h3
  calc _ ≤ κ ^ 2 * ∫ y in ball z (κ * ρ), ‖W1p.gradient w y‖ ^ 2 := h1
    _ ≤ κ ^ 2 * (D * (κ * ρ / (r / κ)) ^ n *
          ∫ y in ball z (r / κ), ‖W1p.gradient w y‖ ^ 2) := by
        gcongr
        exact setIntegral_ball_norm_gradient_sq_le_of_forall_energyFormH1_eq_zero
          (Omega := ⟨ball z (r / κ), isOpen_ball⟩) (by positivity) hB hB' hw subset_rfl
          (by positivity) hsmall
    _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 (by positivity))
        (by positivity)

/-- **Decay of the gradient's distance to the normal constants at a flat boundary, for constant
coefficients.** Let `n` be the dimension and `0 < λ`. There is `C > 0`, depending only on `n`, `λ`
and `Λ`, with the following property. Let `H = {x | c₀ < ⟪x, ν⟫}` with `ν ≠ 0`, let `z` lie on the
boundary hyperplane, and let `A` be a matrix with `λ ‖ξ‖² ≤ ξᵀ A ξ` and
`|ηᵀ A ξ| ≤ Λ ‖η‖ ‖ξ‖`. Let `u ∈ H¹(U)` vanish on `U ∖ H`, where `ball z r ⊆ U`, and solve
`-div(A ∇u) = 0` weakly on `U ∩ H`. Write `B_s⁺ = B(z, s) ∩ H`. Then for `0 ≤ ρ ≤ r` and real `t`,

`∫_{B_ρ⁺} ‖∇u - p_ρ‖² ≤ C (ρ / r)^(n + 2) ∫_{B_r⁺} ‖∇u - t ν‖²`,

where `p_ρ = (⟪(∇u)_{B_ρ⁺}, ν⟫ / ‖ν‖²) ν` is the multiple of `ν` closest to `∇u` in `L²(B_ρ⁺)`
(`TauCeti.setIntegral_norm_sub_starProjection_setAverage_sq_le` for `ℝ ∙ ν`), so that the
estimate can be iterated. The multiples of `ν` are the gradients of the linear functions
`t (⟪x, ν⟫ - c₀)`, which vanish on the hyperplane and solve the equation. -/
theorem exists_setIntegral_ball_inter_norm_gradient_sub_inner_setAverage_div_smul_sq_le
    {lam Lam : ℝ} (hlam : 0 < lam) :
    ∃ C : ℝ, 0 < C ∧ ∀ {U H : Opens (EuclideanSpace ℝ ι)} {A : Matrix ι ι ℝ}
      {ν z : EuclideanSpace ℝ ι} {c₀ r ρ : ℝ} {u : W1p volume U 2},
      (∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ) →
      (∀ η ξ : EuclideanSpace ℝ ι, |η ⬝ᵥ (A *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖) → ν ≠ 0 →
      (∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) → ⟪z, ν⟫_ℝ = c₀ → ball z r ⊆ U →
      (∀ᵐ x ∂volume.restrict U, x ∉ H → W1p.value u x = 0) →
      (∀ v : W1p0 volume (U ⊓ H) 2, energyFormH1 (fun _ => A) 0 0 (W1p.restrictL inf_le_left u)
        (v : W1p volume (U ⊓ H) 2) = 0) →
      0 ≤ ρ → ρ ≤ r → ∀ t : ℝ,
      ∫ x in ball z ρ ∩ H, ‖W1p.gradient u x -
          (⟪⨍ y in ball z ρ ∩ H, W1p.gradient u y, ν⟫_ℝ / ‖ν‖ ^ 2) • ν‖ ^ 2 ≤
        C * (ρ / r) ^ (Fintype.card ι + 2) *
          ∫ x in ball z r ∩ H, ‖W1p.gradient u x - t • ν‖ ^ 2 := by
  set κ := 1 + Lam / lam
  set n := Fintype.card ι
  set D := 2 ^ (3 * n + 10) * (n + 1) ^ 2 * √(Lam * κ ^ 2 / (lam / κ ^ 2)) ^ (n + 2)
  refine ⟨2 * (κ ^ 2) ^ (n + 2 + 2) * D + (κ ^ 2) ^ (n + 2) + 1, by positivity, ?_⟩
  intro U H A ν z c₀ r ρ u hA hA' hν hH hz hball hu0 hu hρ hρr t
  obtain ⟨-, -, hLam, -⟩ := boundaryShear_constants hlam hν hA hA'
  have hI : 0 ≤ ∫ x in ball z r ∩ H, ‖W1p.gradient u x - t • ν‖ ^ 2 :=
    setIntegral_nonneg (measurableSet_ball.inter H.isOpen.measurableSet) fun _ _ => by positivity
  rcases hρ.eq_or_lt with rfl | hρ0
  · rw [ball_zero, empty_inter, Measure.restrict_empty, integral_zero_measure]
    positivity
  -- Among the multiples of `ν`, the projection of the average of `∇u` is the best constant.
  have hmin := fun {c} => setIntegral_norm_sub_starProjection_setAverage_sq_le (c := c)
    (volume_ball_inter_ne_top z ρ H) ((Lp.aestronglyMeasurable (W1p.gradient u)).mono_measure
      (Measure.restrict_mono (inter_subset_left.trans ((ball_subset_ball hρr).trans hball))
        le_rfl)) (ℝ ∙ ν)
  rw [Submodule.starProjection_singleton, RCLike.ofReal_real_eq_id, id_eq, real_inner_comm] at hmin
  have hmem : ∀ t : ℝ, t • ν ∈ ℝ ∙ ν := fun t =>
    Submodule.smul_mem _ t (Submodule.mem_span_singleton_self ν)
  refine le_mul_div_pow_mul_of_le (n + 2) (le_add_of_nonneg_right (div_nonneg hLam hlam.le)) hρ0
    hρr hI (by positivity) (fun hsmall => ?_) ((hmin (hmem t)).trans (setIntegral_mono_set
      ((Lp.memLp (W1p.gradient u)).integrableOn_norm_sub_sq_of_subset
        (inter_subset_left.trans hball) (volume_ball_inter_ne_top z r H) _)
      (Filter.Eventually.of_forall fun _ => by positivity)
      (Filter.Eventually.of_forall (inter_subset_inter_left _ (ball_subset_ball hρr)))))
  obtain ⟨B, M, w, hB, hB', hw, hT, hM, hodd, hR⟩ :=
    exists_boundaryReflection hlam hA hA' hν hH hz hball hu0 hu
  have : 0 < κ := add_pos_of_pos_of_nonneg one_pos (div_nonneg hLam hlam.le)
  have hr : 0 < r := hρ0.trans_le hρr
  -- The average `m` of the odd field `∇w` over a ball centred on the hyperplane is normal.
  set m := ⨍ y in ball z (κ * ρ), W1p.gradient w y
  have hm : m = (⟪m, ν⟫_ℝ / ‖ν‖ ^ 2) • ν :=
    setAverage_eq_inner_div_smul_of_ae_comp_hyperplaneReflection
      (mapsTo_hyperplaneReflection_ball hz _) measurableSet_ball
      (ae_restrict_of_ae_restrict_of_subset (ball_subset_ball hsmall) hodd)
  have hMm : M m = (⟪m, ν⟫_ℝ / ‖ν‖ ^ 2) • ν := (congrArg M hm).trans (hM _)
  calc _ ≤ ∫ x in ball z ρ ∩ H, ‖W1p.gradient u x - M m‖ ^ 2 := by rw [hMm]; exact hmin (hmem _)
    _ ≤ κ ^ 2 * ∫ y in ball z (κ * ρ), ‖W1p.gradient w y - m‖ ^ 2 :=
        hT ρ hsmall ((ball_subset_ball hρr).trans hball) m
    _ ≤ κ ^ 2 * (D * (κ * ρ / (r / κ)) ^ (n + 2) *
          ∫ y in ball z (r / κ), ‖W1p.gradient w y - t • ν‖ ^ 2) := by
        gcongr
        exact setIntegral_ball_norm_gradient_sub_setAverage_sq_le_of_forall_energyFormH1_eq_zero
          (Omega := ⟨ball z (r / κ), isOpen_ball⟩) (by positivity) hB hB' hw subset_rfl (t • ν)
          (by positivity) hsmall
    _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hR t) (by positivity))
        (by positivity)

end Decay

end PDE

end TauCeti
