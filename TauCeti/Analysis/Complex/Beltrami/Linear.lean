/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cayley.Smooth
public import TauCeti.Geometry.Symplectic.Complex.Line
public import TauCeti.Analysis.Complex.Wirtinger.Basic
public import TauCeti.LinearAlgebra.Complex.LinearPart
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.Analysis.Complex.UnitDisc.Basic
import Mathlib.LinearAlgebra.Complex.Determinant
import TauCeti.LinearAlgebra.Complex.Module

/-!
# Scalar Beltrami coordinates and the affine normalizer

The affine map `z ↦ z + μ conj z` normalizes an almost complex structure on the oriented real
plane. Its real determinant is `1 - ‖μ‖²`; hence the open unit disc is the nondegenerate positive
component. The scalar coordinate of a tame almost complex structure is the value at one of its
native Cayley transform. The general Cayley equivalence and its finite-regularity family
calculus are reused rather than reconstructed.

A real-linear map `A` intertwines a tame structure `J` with multiplication by `i` exactly when it
is a complex multiple of the affine normalizer. For the differential of `f` at `z` this is the
pointwise Beltrami equation `\bar∂f(z) = μ_J ∂f(z)`
(`TauCeti.Beltrami.isComplexLinear_iff_conjWirtingerDeriv_eq`). The coefficient vanishes exactly
at the standard structure (`TauCeti.Beltrami.coefficientEquiv_eq_zero_iff`).

This is the pointwise normalization used before solving the variable-coefficient Beltrami
equation. It does not construct isothermal charts or assume a solution of that equation.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix E, for the Beltrami normalization in the surface integrability argument.
-/

public noncomputable section

open Complex Manifold
open scoped ComplexConjugate ContDiff

namespace TauCeti.Beltrami

/-- The real-linear affine Beltrami map has value zero at zero and holomorphic Wirtinger
derivative one. -/
def linearMap (μ : ℂ) : ℂ →L[ℝ] ℂ :=
  ContinuousLinearMap.id ℝ ℂ + μ • Complex.conjCLE.toContinuousLinearMap

@[simp]
theorem linearMap_apply (μ z : ℂ) : linearMap μ z = z + μ * conj z := (rfl)

@[simp]
theorem linearMap_zero : linearMap 0 = ContinuousLinearMap.id ℝ ℂ := by
  ext z
  simp

/-- The affine Beltrami map is close to the identity in the actual operator norm. -/
theorem norm_linearMap_sub_id_le (μ : ℂ) :
    ‖linearMap μ - ContinuousLinearMap.id ℝ ℂ‖ ≤ ‖μ‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg μ)
  intro z
  simp [linearMap_apply]

private theorem linearMap_sub_conj (μ z : ℂ) :
    linearMap μ (z - μ * conj z) = (1 - Complex.normSq μ) • z := by
  simp only [linearMap_apply, map_sub, map_mul, conj_conj, Complex.real_smul]
  rw [← mul_assoc, Complex.mul_conj]
  simp only [Complex.ofReal_sub, Complex.ofReal_one]
  ring

private theorem sub_conj_linearMap (μ z : ℂ) :
    linearMap μ z - μ * conj (linearMap μ z) = (1 - Complex.normSq μ) • z := by
  simp only [linearMap_apply, map_add, map_mul, conj_conj, Complex.real_smul]
  rw [mul_add, ← mul_assoc, Complex.mul_conj]
  simp only [Complex.ofReal_sub, Complex.ofReal_one]
  ring

private theorem left_inverse (μ : ℂ) (hμ : Complex.normSq μ ≠ 1) :
    Function.LeftInverse (fun z => (1 - Complex.normSq μ)⁻¹ • (z - μ * conj z))
      (linearMap μ) := by
  intro z
  dsimp only
  rw [sub_conj_linearMap, smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hμ.symm), one_smul]

private theorem right_inverse (μ : ℂ) (hμ : Complex.normSq μ ≠ 1) :
    Function.RightInverse (fun z => (1 - Complex.normSq μ)⁻¹ • (z - μ * conj z))
      (linearMap μ) := by
  intro z
  dsimp only
  rw [map_smul, linearMap_sub_conj, smul_smul,
    inv_mul_cancel₀ (sub_ne_zero.mpr hμ.symm), one_smul]

/-- The actual continuous real-linear equivalence of the affine Beltrami map for `normSq μ ≠ 1`. -/
def linearEquiv (μ : ℂ) (hμ : Complex.normSq μ ≠ 1) : ℂ ≃L[ℝ] ℂ :=
  (LinearEquiv.ofBijective (linearMap μ).toLinearMap
    ⟨(left_inverse μ hμ).injective, (right_inverse μ hμ).surjective⟩).toContinuousLinearEquiv

@[simp]
theorem linearEquiv_apply (μ : ℂ) (hμ : Complex.normSq μ ≠ 1) (z : ℂ) :
    linearEquiv μ hμ z = z + μ * conj z := (rfl)

/-- The continuous linear map underlying the equivalence is the affine Beltrami map. -/
@[simp]
theorem linearEquiv_toContinuousLinearMap (μ : ℂ) (hμ : Complex.normSq μ ≠ 1) :
    (linearEquiv μ hμ).toContinuousLinearMap = linearMap μ := (rfl)

/-- The explicit inverse has denominator equal to the nonzero real Jacobian factor. -/
@[simp]
theorem linearEquiv_symm_apply (μ : ℂ) (hμ : Complex.normSq μ ≠ 1) (z : ℂ) :
    (linearEquiv μ hμ).symm z = (1 - Complex.normSq μ)⁻¹ • (z - μ * conj z) := by
  apply (linearEquiv μ hμ).injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  rw [linearEquiv_apply]
  simpa only [linearMap_apply] using (right_inverse μ hμ z).symm

/-- The real matrix of the affine normalizer in the native `1,I` basis. -/
theorem toMatrix_linearMap (μ : ℂ) :
    LinearMap.toMatrix Complex.basisOneI Complex.basisOneI (linearMap μ).toLinearMap =
      !![1 + μ.re, μ.im; μ.im, 1 - μ.re] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [LinearMap.toMatrix_apply, Complex.coe_basisOneI, Complex.coe_basisOneI_repr]; ring

/-- The affine normalizer has the real Jacobian `1 - |μ|²`. -/
theorem det_linearMap (μ : ℂ) : (linearMap μ).toLinearMap.det = 1 - Complex.normSq μ := by
  rw [← LinearMap.det_toMatrix Complex.basisOneI, toMatrix_linearMap,
    Matrix.det_fin_two_of, Complex.normSq_apply]
  ring

/-- The standard area form changes by the actual real Jacobian factor. -/
theorem area_linearMap (μ z w : ℂ) :
    stdComplexSymplecticForm (linearMap μ z) (linearMap μ w) =
      (1 - Complex.normSq μ) * stdComplexSymplecticForm z w := by
  simp [stdComplexSymplecticForm_apply, linearMap_apply, Complex.normSq_apply]
  ring

/-- The antiholomorphic derivative of the affine normalizer is the coefficient itself. -/
@[simp]
theorem conjWirtingerDeriv_linearMap (μ z : ℂ) :
    conjWirtingerDeriv (linearMap μ) z 1 = μ := by
  simp [conjWirtingerDeriv_apply, linearMap_apply]
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- The holomorphic derivative of the affine normalizer is one. -/
@[simp]
theorem wirtingerDeriv_linearMap (μ z : ℂ) :
    wirtingerDeriv (linearMap μ) z 1 = 1 := by
  simp [wirtingerDeriv_apply, linearMap_apply]
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- At coefficient one, the affine map collapses the imaginary direction. -/
theorem not_injective_linearMap_one : ¬ Function.Injective (linearMap 1) := by
  intro h
  have he : linearMap 1 Complex.I = linearMap 1 0 := by simp
  exact Complex.I_ne_zero (h he)

/-- On the complex line an antilinear endomorphism is determined by its value at one. -/
theorem antilinear_apply {C : Module.End ℝ ℂ}
    (hC : IsComplexAntilinear (AlmostComplexStructure.ofComplexModule ℂ).toLinearMap
      (AlmostComplexStructure.ofComplexModule ℂ).toLinearMap C) (z : ℂ) :
    C z = C 1 * conj z := by
  have hI : C Complex.I = -(Complex.I * C 1) := by
    simpa [AlmostComplexStructure.ofComplexModule_apply] using hC.apply 1
  have hz : z = z.re • (1 : ℂ) + z.im • Complex.I := by
    simp [Complex.real_smul]
  rw [hz, map_add, map_smul, map_smul, hI]
  simp only [map_add, map_one, map_mul, Complex.conj_ofReal, Complex.conj_I,
    Complex.real_smul]
  ring

/-- The antilinear real endomorphism with scalar coefficient `μ`. -/
def antilinearMap (μ : ℂ) : ℂ →L[ℝ] ℂ :=
  μ • Complex.conjCLE.toContinuousLinearMap

@[simp]
theorem antilinearMap_apply (μ z : ℂ) : antilinearMap μ z = μ * conj z := (rfl)

/-- Scalar conjugate multiplication is antilinear for the standard complex structure. -/
theorem isComplexAntilinear_antilinearMap (μ : ℂ) :
    IsComplexAntilinear (AlmostComplexStructure.ofComplexModule ℂ).toLinearMap
      (AlmostComplexStructure.ofComplexModule ℂ).toLinearMap (antilinearMap μ).toLinearMap := by
  apply isComplexAntilinear_of_apply
  intro z
  simp [AlmostComplexStructure.ofComplexModule_apply]
  ring

/-- The Cayley contraction condition on the complex line is precisely the scalar unit disc. -/
theorem antilinearMap_mem_cayleyBall_iff (μ : ℂ) :
    (antilinearMap μ).toLinearMap ∈
      stdComplexSymplecticForm.cayleyBall (AlmostComplexStructure.ofComplexModule ℂ) ↔
      ‖μ‖ < 1 := by
  rw [SymplecticForm.mem_cayleyBall]
  constructor
  · intro h
    have h1 := h.2 1 one_ne_zero
    simp only [stdComplexSymplecticForm_apply_ofComplexModule,
      ContinuousLinearMap.coe_coe, antilinearMap_apply, map_one, mul_one] at h1
    rw [Complex.normSq_eq_norm_sq] at h1
    nlinarith [norm_nonneg μ]
  · intro h
    refine ⟨isComplexAntilinear_antilinearMap μ, fun z hz => ?_⟩
    simp only [stdComplexSymplecticForm_apply_ofComplexModule,
      ContinuousLinearMap.coe_coe, antilinearMap_apply,
      Complex.normSq_mul, Complex.normSq_conj]
    have hm : Complex.normSq μ < 1 := by
      simpa only [Complex.UnitDisc.coe_mk] using
        Complex.UnitDisc.normSq_lt_one (Complex.UnitDisc.mk μ h)
    simpa using mul_lt_mul_of_pos_right hm (Complex.normSq_pos.mpr hz)

/-- Evaluation at one identifies the native plane Cayley ball with the complex unit disc. -/
def cayleyBallEquiv :
    stdComplexSymplecticForm.cayleyBall (AlmostComplexStructure.ofComplexModule ℂ) ≃
      {μ : ℂ // ‖μ‖ < 1} where
  toFun C := ⟨C.val 1, by
    have he : (antilinearMap (C.val 1)).toLinearMap = C.val := by
      ext z
      exact (antilinear_apply (SymplecticForm.mem_cayleyBall.mp C.property).1 z).symm
    exact (antilinearMap_mem_cayleyBall_iff _).mp (he.symm ▸ C.property)⟩
  invFun μ := ⟨(antilinearMap μ.val).toLinearMap,
    (antilinearMap_mem_cayleyBall_iff _).mpr μ.property⟩
  left_inv C := by
    apply Subtype.ext
    ext z
    exact (antilinear_apply (SymplecticForm.mem_cayleyBall.mp C.property).1 z).symm
  right_inv μ := by
    apply Subtype.ext
    simp

@[simp]
theorem cayleyBallEquiv_apply
    (C : stdComplexSymplecticForm.cayleyBall (AlmostComplexStructure.ofComplexModule ℂ)) :
    (cayleyBallEquiv C).val = C.val 1 := (rfl)

@[simp]
theorem cayleyBallEquiv_symm_apply (μ : {μ : ℂ // ‖μ‖ < 1}) :
    (cayleyBallEquiv.symm μ).val = (antilinearMap μ.val).toLinearMap := (rfl)

/-- The native tame Cayley chart, expressed by a single scalar Beltrami coefficient. Its domain
is the positive orientation component; see `stdComplexSymplecticForm_tames_iff_im_pos`. -/
def coefficientEquiv :
    {J : AlmostComplexStructure ℂ // stdComplexSymplecticForm.Tames J} ≃
      {μ : ℂ // ‖μ‖ < 1} :=
  stdComplexSymplecticForm_compatible.cayleyEquiv.trans cayleyBallEquiv

@[simp]
theorem coefficientEquiv_apply (J : AlmostComplexStructure ℂ)
    (hJ : stdComplexSymplecticForm.Tames J) :
    (coefficientEquiv ⟨J, hJ⟩).val =
      (AlmostComplexStructure.ofComplexModule ℂ).cayley J 1 := by
  simp only [coefficientEquiv, Equiv.trans_apply, cayleyBallEquiv_apply,
    SymplecticForm.Compatible.cayleyEquiv_apply_coe]

/-- The affine map for the scalar Cayley coefficient actually intertwines the given structure
with multiplication by `I`. -/
theorem linearMap_intertwines (J : AlmostComplexStructure ℂ)
    (hJ : stdComplexSymplecticForm.Tames J) (z : ℂ) :
    linearMap (coefficientEquiv ⟨J, hJ⟩).val (J z) =
      Complex.I * linearMap (coefficientEquiv ⟨J, hJ⟩).val z := by
  let J₀ := AlmostComplexStructure.ofComplexModule ℂ
  let C := J₀.cayley J
  have hC := stdComplexSymplecticForm_compatible.cayley_mem_cayleyBall hJ
  have ha : IsComplexAntilinear J₀.toLinearMap J₀.toLinearMap C :=
    (SymplecticForm.mem_cayleyBall.mp hC).1
  have hrel := LinearMap.congr_fun
    (stdComplexSymplecticForm_tames.cayley_mul_one_sub_mul hJ) z
  simp only [mul_apply_eq_comp, LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.neg_apply, one_apply_eq_self] at hrel
  rw [map_sub, ha.apply] at hrel
  have hh : J₀ (J z) + J₀ (C (J z)) = -(z + C z) := by
    linear_combination hrel
  have he (w : ℂ) : linearMap (coefficientEquiv ⟨J, hJ⟩).val w = w + C w := by
    rw [linearMap_apply, coefficientEquiv_apply, ← antilinear_apply ha]
  rw [he, he]
  have hstd (w : ℂ) : J₀ w = Complex.I * w :=
    AlmostComplexStructure.ofComplexModule_apply w
  rw [← hstd]
  apply J₀.injective
  simpa only [map_add, J₀.apply_apply, neg_add_rev, add_comm] using hh

/-- The real-linear coordinate change given by the coefficient makes `J` exactly standard.
Applied to the value of a field at a chosen point, this is the normalization `μ(0) = 0`. -/
theorem transport_linearEquiv_eq_std (J : AlmostComplexStructure ℂ)
    (hJ : stdComplexSymplecticForm.Tames J) :
    J.transport (linearEquiv (coefficientEquiv ⟨J, hJ⟩).val
      (by
        simpa only [Complex.UnitDisc.coe_mk] using
          (Complex.UnitDisc.normSq_lt_one (Complex.UnitDisc.mk _
            (coefficientEquiv ⟨J, hJ⟩).property)).ne)).toLinearEquiv =
      AlmostComplexStructure.ofComplexModule ℂ := by
  let e := linearEquiv (coefficientEquiv ⟨J, hJ⟩).val
    (by
      simpa only [Complex.UnitDisc.coe_mk] using
        (Complex.UnitDisc.normSq_lt_one (Complex.UnitDisc.mk _
          (coefficientEquiv ⟨J, hJ⟩).property)).ne)
  apply AlmostComplexStructure.ext
  intro z
  rw [AlmostComplexStructure.transport_apply, AlmostComplexStructure.ofComplexModule_apply]
  have h := linearMap_intertwines J hJ (e.symm z)
  have he : e.toContinuousLinearMap = linearMap (coefficientEquiv ⟨J, hJ⟩).val :=
    linearEquiv_toContinuousLinearMap _ _
  rw [← he] at h
  simpa only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply,
    smul_eq_mul, ContinuousLinearEquiv.coe_toLinearEquiv,
    ContinuousLinearEquiv.coe_symm_toLinearEquiv] using h

/-- Every coefficient with nonzero real Jacobian gives an actual smooth local diffeomorphism. -/
theorem isLocalDiffeomorph_linearMap (μ : ℂ) (hμ : Complex.normSq μ ≠ 1) :
    IsLocalDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (linearMap μ) :=
  (linearEquiv μ hμ).toDiffeomorph.isLocalDiffeomorph

/-- The inverse scalar Cayley chart is conjugation of the standard structure by the actual
real-linear affine normalizer. -/
theorem coefficientEquiv_symm_apply (μ : {μ : ℂ // ‖μ‖ < 1}) (z : ℂ) :
    (coefficientEquiv.symm μ).val z =
      (linearEquiv μ.val (by
        simpa only [Complex.UnitDisc.coe_mk] using
          (Complex.UnitDisc.normSq_lt_one (Complex.UnitDisc.mk μ.val μ.property)).ne)).symm
        (Complex.I * linearEquiv μ.val (by
          simpa only [Complex.UnitDisc.coe_mk] using
            (Complex.UnitDisc.normSq_lt_one (Complex.UnitDisc.mk μ.val μ.property)).ne) z) := by
  apply (linearEquiv μ.val (by
        simpa only [Complex.UnitDisc.coe_mk] using
          (Complex.UnitDisc.normSq_lt_one (Complex.UnitDisc.mk μ.val μ.property)).ne)).injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  have h := linearMap_intertwines (coefficientEquiv.symm μ).val
    (coefficientEquiv.symm μ).property z
  rw [coefficientEquiv.apply_symm_apply] at h
  exact h

/-- The standard structure has zero scalar coefficient. -/
theorem coefficientEquiv_std :
    (coefficientEquiv ⟨AlmostComplexStructure.ofComplexModule ℂ,
      stdComplexSymplecticForm_tames⟩).val = 0 := by
  rw [coefficientEquiv_apply, AlmostComplexStructure.cayley_self]
  rfl

/-- The coefficient of a tame structure has squared norm different from one. -/
private theorem normSq_coefficient_ne_one (J : AlmostComplexStructure ℂ)
    (hJ : stdComplexSymplecticForm.Tames J) :
    Complex.normSq (coefficientEquiv ⟨J, hJ⟩).val ≠ 1 := by
  simpa only [Complex.UnitDisc.coe_mk] using
    (Complex.UnitDisc.normSq_lt_one (Complex.UnitDisc.mk _
      (coefficientEquiv ⟨J, hJ⟩).property)).ne

/-- A real-linear map intertwining `J` with `i` is a complex multiple of the affine normalizer of
`J`, and conversely. -/
private theorem isComplexLinear_iff_exists_eq_mul_linearMap (J : AlmostComplexStructure ℂ)
    (hJ : stdComplexSymplecticForm.Tames J) (A : ℂ →L[ℝ] ℂ) :
    IsComplexLinear J.toLinearMap (AlmostComplexStructure.ofComplexModule ℂ).toLinearMap
        A.toLinearMap ↔
      ∃ β : ℂ, ∀ v, A v = β * linearMap (coefficientEquiv ⟨J, hJ⟩).val v := by
  set μ := (coefficientEquiv ⟨J, hJ⟩).val
  have hstd (w : ℂ) : AlmostComplexStructure.ofComplexModule ℂ w = I * w :=
    AlmostComplexStructure.ofComplexModule_apply w
  constructor
  · intro hA
    have hA' (v : ℂ) : A (J v) = I * A v := by
      simpa [hstd] using hA.apply v
    set e := linearEquiv μ (normSq_coefficient_ne_one J hJ)
    have hJe (w : ℂ) : J (e.symm w) = e.symm (I * w) := by
      apply e.injective
      have he (x : ℂ) : e x = linearMap μ x := by simp [e]
      rw [he, linearMap_intertwines J hJ (e.symm w), ← he, ContinuousLinearEquiv.apply_symm_apply,
        ContinuousLinearEquiv.apply_symm_apply]
    have hB (w : ℂ) : A (e.symm w) = w * A (e.symm 1) := by
      -- `A ∘ e⁻¹` commutes with `I`, so it is complex linear.
      let B := (A.toLinearMap.comp e.symm.toLinearEquiv.toLinearMap).complexOfMapISmul
        fun v => by simpa [smul_eq_mul, hJe] using hA' (e.symm v)
      simpa [B] using B.map_smul w 1
    refine ⟨A (e.symm 1), fun v => ?_⟩
    have := hB (e v)
    rw [ContinuousLinearEquiv.symm_apply_apply] at this
    rw [this, linearEquiv_apply, linearMap_apply]
    ring
  · rintro ⟨β, hβ⟩
    apply isComplexLinear_of_apply
    intro v
    simp only [ContinuousLinearMap.coe_coe, hβ, hstd]
    have h := linearMap_intertwines J hJ v
    rw [h]
    ring

/-- **Pointwise Beltrami equation.** A real-linear map of the plane is complex linear from a tame
structure `J` to `i` iff its antiholomorphic part is `μ_J` times its holomorphic part, in terms of
the values `A 1` and `A i`: `A 1 + i A i = μ_J (A 1 - i A i)`. -/
theorem isComplexLinear_iff_apply_one_add_I_mul_apply_I (J : AlmostComplexStructure ℂ)
    (hJ : stdComplexSymplecticForm.Tames J) (A : ℂ →L[ℝ] ℂ) :
    IsComplexLinear J.toLinearMap (AlmostComplexStructure.ofComplexModule ℂ).toLinearMap
        A.toLinearMap ↔
      A 1 + I * A I = (coefficientEquiv ⟨J, hJ⟩).val * (A 1 - I * A I) := by
  rw [isComplexLinear_iff_exists_eq_mul_linearMap J hJ]
  set μ := (coefficientEquiv ⟨J, hJ⟩).val
  constructor
  · rintro ⟨β, hβ⟩
    rw [hβ, hβ, linearMap_apply, linearMap_apply, map_one, Complex.conj_I]
    ring_nf
    rw [Complex.I_sq]
    ring
  · intro h
    refine ⟨(2 : ℂ)⁻¹ * (A 1 - I * A I), fun v => ?_⟩
    have hc : conj v = v.re - v.im * I := by
      apply Complex.ext <;> simp
    have hAv : A v = v.re * A 1 + v.im * A I := by
      simpa only [ContinuousLinearMap.coe_coe, Complex.real_smul] using
        A.toLinearMap.apply_eq_re_smul_one_add_im_smul_I v
    rw [hAv, linearMap_apply, hc]
    linear_combination (norm := (ring_nf; simp only [I_sq]; ring_nf))
      ((2 : ℂ)⁻¹ * (↑v.re - ↑v.im * I)) * h + ((2 : ℂ)⁻¹ * (A 1 - I * A I)) * Complex.re_add_im v

/-- **Pointwise Beltrami equation for a differential.** The real differential of `f` at `z` is
complex linear from a tame structure `J` to `i` iff `\bar∂f(z) = μ_J ∂f(z)`. No
differentiability is needed: both sides use the totalized derivative. -/
theorem isComplexLinear_iff_conjWirtingerDeriv_eq (J : AlmostComplexStructure ℂ)
    (hJ : stdComplexSymplecticForm.Tames J) (f : ℂ → ℂ) (z : ℂ) :
    IsComplexLinear J.toLinearMap (AlmostComplexStructure.ofComplexModule ℂ).toLinearMap
        (fderiv ℝ f z).toLinearMap ↔
      conjWirtingerDeriv f z 1 = (coefficientEquiv ⟨J, hJ⟩).val * wirtingerDeriv f z 1 := by
  rw [isComplexLinear_iff_apply_one_add_I_mul_apply_I J hJ, wirtingerDeriv_apply,
    conjWirtingerDeriv_apply]
  simp only [smul_eq_mul, mul_one]
  constructor
  · intro h
    rw [h]
    ring
  · intro h
    linear_combination 2 * h

/-- The scalar coefficient of a tame structure vanishes exactly at the standard structure. -/
theorem coefficientEquiv_eq_zero_iff (J : AlmostComplexStructure ℂ)
    (hJ : stdComplexSymplecticForm.Tames J) :
    (coefficientEquiv ⟨J, hJ⟩).val = 0 ↔ J = AlmostComplexStructure.ofComplexModule ℂ := by
  constructor
  · intro h
    have h' : coefficientEquiv ⟨J, hJ⟩ =
        coefficientEquiv ⟨AlmostComplexStructure.ofComplexModule ℂ,
          stdComplexSymplecticForm_tames⟩ :=
      Subtype.ext (h.trans coefficientEquiv_std.symm)
    exact congrArg Subtype.val (coefficientEquiv.injective h')
  · rintro rfl
    exact coefficientEquiv_std

/-- At coefficient one the affine map fails to be a local diffeomorphism at every point,
not just to be globally injective. -/
theorem not_isLocalDiffeomorphAt_linearMap_one (z : ℂ) {n : WithTop ℕ∞} (hn : n ≠ 0) :
    ¬ IsLocalDiffeomorphAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) n (linearMap 1) z := by
  intro h
  have hd := h.isInvertible_mfderiv hn
  let e := NormedSpace.fromTangentSpace (𝕜 := ℝ) z
  have hk : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (linearMap 1) z (e.symm Complex.I) =
      mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (linearMap 1) z 0 := by
    simp [mfderiv_eq_fderiv, (linearMap 1).fderiv, e]
  have he := congrArg e (hd.bijective.injective hk)
  simp at he

section Families

variable {E G N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace N] [ChartedSpace G N]
  {n : WithTop ℕ∞} {p : N}

/-- Scalar Beltrami coefficients preserve the actual finite regularity of a tame family.
No derivative of the family is used by this pointwise chart. -/
theorem contMDiffAt_coefficient {J : N → AlmostComplexStructure ℂ}
    (hJ : ∀ y, stdComplexSymplecticForm.Tames (J y))
    (hJs : ContMDiffAt I 𝓘(ℝ, ℂ →L[ℝ] ℂ) n
      (fun y => LinearMap.toContinuousLinearMap (J y).toLinearMap) p) :
    ContMDiffAt I 𝓘(ℝ, ℂ) n
      (fun y => (coefficientEquiv ⟨J y, hJ y⟩).val) p := by
  simp only [coefficientEquiv_apply]
  exact (stdComplexSymplecticForm_tames.contMDiffAt_cayley (hJ p) hJs).clm_apply
    (contMDiffAt_const (c := (1 : ℂ)))

/-- The inverse scalar Cayley chart preserves every finite differentiability order as well
as smoothness, by the native inverse Cayley family calculus. -/
theorem contMDiffAt_coefficientEquiv_symm {μ : N → ℂ} (hμ : ∀ y, ‖μ y‖ < 1)
    (hμs : ContMDiffAt I 𝓘(ℝ, ℂ) n μ p) :
    ContMDiffAt I 𝓘(ℝ, ℂ →L[ℝ] ℂ) n (fun y => LinearMap.toContinuousLinearMap
      (coefficientEquiv.symm ⟨μ y, hμ y⟩).val.toLinearMap) p := by
  have hs : ContMDiffAt I 𝓘(ℝ, ℂ →L[ℝ] ℂ) n (fun y => antilinearMap (μ y)) p :=
    (contDiff_smul_const Complex.conjCLE.toContinuousLinearMap).contDiffAt.comp_contMDiffAt hμs
  exact stdComplexSymplecticForm_compatible.contMDiffAt_cayleyEquiv_symm
    (fun y => (antilinearMap_mem_cayleyBall_iff _).mpr (hμ y)) hs

/-- The global scalar coefficient chart preserves finite-order regularity of tame families. -/
theorem contMDiff_coefficient {J : N → AlmostComplexStructure ℂ}
    (hJ : ∀ y, stdComplexSymplecticForm.Tames (J y))
    (hJs : ContMDiff I 𝓘(ℝ, ℂ →L[ℝ] ℂ) n
      (fun y => LinearMap.toContinuousLinearMap (J y).toLinearMap)) :
    ContMDiff I 𝓘(ℝ, ℂ) n (fun y => (coefficientEquiv ⟨J y, hJ y⟩).val) :=
  fun _ => contMDiffAt_coefficient hJ (hJs _)

/-- The global inverse scalar chart preserves finite-order regularity. -/
theorem contMDiff_coefficientEquiv_symm {μ : N → ℂ} (hμ : ∀ y, ‖μ y‖ < 1)
    (hμs : ContMDiff I 𝓘(ℝ, ℂ) n μ) :
    ContMDiff I 𝓘(ℝ, ℂ →L[ℝ] ℂ) n (fun y => LinearMap.toContinuousLinearMap
      (coefficientEquiv.symm ⟨μ y, hμ y⟩).val.toLinearMap) :=
  fun _ => contMDiffAt_coefficientEquiv_symm hμ (hμs _)

end Families

end TauCeti.Beltrami
