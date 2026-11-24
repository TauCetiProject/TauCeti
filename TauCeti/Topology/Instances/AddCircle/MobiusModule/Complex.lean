/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import TauCeti.LinearAlgebra.TensorProduct.Balanced.Extension
public import TauCeti.Topology.Instances.AddCircle.MobiusModule

/-!
# The complexified Möbius module is free of rank one

The Möbius module `M = TauCeti.mobiusSections` over `R = C(ℝ / ℤ, ℝ)`, the fixed module of the
reflection `ρ([t]) = [[cos 2πt, sin 2πt], [sin 2πt, −cos 2πt]]` acting on `R²`, is finitely
generated projective but not free (`TauCeti.not_free_mobiusSections`): it is the module of
continuous sections of the Möbius line bundle, which is nontrivial. Over the complex numbers every
line bundle on the circle is trivial. This file proves the module-theoretic form of that fact:
extending scalars along the pointwise inclusion `R → R_ℂ = C(ℝ / ℤ, ℂ)` makes `M` free of rank
one.

1. **Complexification.** The complex Möbius module `M_ℂ = TauCeti.complexMobiusSections` is the
   fixed module of the same reflection acting on `R_ℂ²`. Since `M` is the image of the symmetric
   idempotent `p = (1 + ρ) / 2` (`TauCeti.range_vecMulLinear_mobiusProjection`), the balanced
   extension of scalars `R_ℂ ⊗_R M` is the image of `p` acting on `R_ℂ²`, which is `M_ℂ`
   (`TauCeti.mobiusSectionsComplexifyEquiv`, through `c ⊗ w ↦ c w`).
2. **A complex frame.** With `z = fourier 1`, the function `[t] ↦ exp (2πit)`, the pair
   `s = ((1 + z) / 2, i (1 − z) / 2)` (`TauCeti.mobiusComplexFrame`) is a continuous section of
   `M_ℂ` with `s* s = 1` and `s s* = p`. At `[t]` it is `exp (πit) (cos πt, sin πt)`: the twist of
   the real line `ℝ (cos πt, sin πt)` is undone by the complex phase `exp (πit)`, which also
   changes sign over one turn. Hence `g ↦ g s` is an isomorphism `R_ℂ ≃ M_ℂ` with inverse
   `w ↦ s* w` (`TauCeti.complexMobiusSectionsEquiv`), and `R_ℂ ⊗_R M ≃ R_ℂ`
   (`TauCeti.mobiusSectionsComplexTrivializationEquiv`).

Read in `K₀`, this is the vanishing of the image in `K₀(R_ℂ)` of the class `[M] − [R]`, which has
order two in `K₀(R)`: extension of scalars sends `[M]` to `[R_ℂ ⊗_R M] = [R_ℂ]`.

## Main definitions

* `TauCeti.complexMobiusSections`: the complex Möbius module, the kernel of `ρ − 1` acting on
  `C(ℝ / ℤ, ℂ)²`.
* `TauCeti.mobiusSectionsComplexifyEquiv`: `C(ℝ / ℤ, ℂ) ⊗_R M ≃ M_ℂ`, `c ⊗ w ↦ c w`.
* `TauCeti.mobiusComplexFrame`: the unit section `s = ((1 + z) / 2, i (1 − z) / 2)` of `M_ℂ`.
* `TauCeti.complexMobiusSectionsEquiv`: `C(ℝ / ℤ, ℂ) ≃ M_ℂ`, `g ↦ g s`.
* `TauCeti.mobiusSectionsComplexTrivializationEquiv`: `C(ℝ / ℤ, ℂ) ⊗_R M ≃ C(ℝ / ℤ, ℂ)`.

## Main results

* `TauCeti.mem_complexMobiusSections_iff`: the pointwise description of `M_ℂ`.
* `TauCeti.mobiusComplexFrame_apply_mk`: `s([t]) = exp (πit) (cos πt, sin πt)`.
* `TauCeti.vecMulVec_mobiusComplexFrame_star`: `s s* = p`.
* `TauCeti.star_mobiusComplexFrame_dotProduct_self`: `s* s = 1`.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Graduate Studies in
  Mathematics 145 (2013), Chapter I, (4.9.1), for the Möbius bundle and the triviality of complex
  line bundles on the circle; the frame `s` above is a direct elementary construction.
-/

public section

noncomputable section

open Matrix Real

namespace TauCeti

local notation "𝓒" => C(AddCircle (1 : ℝ), ℝ)

local notation "𝓒ℂ" => C(AddCircle (1 : ℝ), ℂ)

/-- The pointwise inclusion `C(ℝ / ℤ, ℝ) →+* C(ℝ / ℤ, ℂ)`. -/
local notation "ofRealCM" =>
  RingHom.compLeftContinuous (AddCircle (1 : ℝ)) (algebraMap ℝ ℂ) Complex.continuous_ofReal

/-! ### The complex Möbius module -/

/-- The **complex Möbius module** over `C(ℝ / ℤ, ℂ)`: the pairs `w` of continuous complex
functions on the circle fixed by the reflection `mobiusReflection`, that is, the continuous fields
with `w([t])` on the complex line spanned by `(cos πt, sin πt)`. -/
def complexMobiusSections : Submodule 𝓒ℂ (Fin 2 → 𝓒ℂ) :=
  LinearMap.ker (mulVecLin (mobiusReflection.map ofRealCM - 1))

theorem complexMobiusSections_def :
    complexMobiusSections = LinearMap.ker (mulVecLin (mobiusReflection.map ofRealCM - 1)) :=
  (rfl)

/-- The complex Möbius module is the fixed module of the reflection `ρ`. -/
theorem mem_complexMobiusSections_iff_mulVec {w : Fin 2 → 𝓒ℂ} :
    w ∈ complexMobiusSections ↔ mobiusReflection.map ofRealCM *ᵥ w = w := by
  simp [complexMobiusSections_def, sub_eq_zero]

/-- A pair `w = (w₀, w₁)` lies in the complex Möbius module iff
`cos(2πt) w₀ + sin(2πt) w₁ = w₀` and `sin(2πt) w₀ − cos(2πt) w₁ = w₁` at every point `[t]` of the
circle. -/
theorem mem_complexMobiusSections_iff {w : Fin 2 → 𝓒ℂ} :
    w ∈ complexMobiusSections ↔ ∀ t : ℝ,
      cos (2 * π * t) * w 0 t + sin (2 * π * t) * w 1 t = w 0 t ∧
        sin (2 * π * t) * w 0 t - cos (2 * π * t) * w 1 t = w 1 t := by
  simp only [mem_complexMobiusSections_iff_mulVec, funext_iff, Fin.forall_fin_two,
    ContinuousMap.ext_iff, QuotientAddGroup.mk_surjective.forall, ← forall_and]
  simp [mobiusReflection_def, mulVec, dotProduct, Fin.sum_univ_two, sub_eq_add_neg]

/-! ### The complexified projection -/

private theorem map_mobiusProjection :
    mobiusProjection.map ofRealCM = (2⁻¹ : ℝ) • (1 + mobiusReflection.map ofRealCM) := by
  rw [mobiusProjection_def, Matrix.map_smul _ _ fun _ ↦ by ext; simp, Matrix.map_add _ (map_add _),
    Matrix.map_one _ (map_zero _) (map_one _)]

private theorem map_mobiusProjection_mulVec (w : Fin 2 → 𝓒ℂ) :
    mobiusProjection.map ofRealCM *ᵥ w = (2⁻¹ : ℝ) • (w + mobiusReflection.map ofRealCM *ᵥ w) := by
  rw [map_mobiusProjection, smul_mulVec, add_mulVec, one_mulVec]

/-! ### The complex frame -/

/-- The continuous section `s = ((1 + z) / 2, i (1 − z) / 2)` of the complex Möbius module, where
`z = fourier 1` is the function `[t] ↦ exp (2πit)`. At `[t]` it is `exp (πit) (cos πt, sin πt)`
(`mobiusComplexFrame_apply_mk`), a unit vector on the line of the Möbius bundle at `[t]`. -/
def mobiusComplexFrame : Fin 2 → 𝓒ℂ :=
  ![(2⁻¹ : ℂ) • (1 + fourier 1), (2⁻¹ * Complex.I) • (1 - fourier 1)]

@[simp]
theorem mobiusComplexFrame_zero_apply (x : AddCircle (1 : ℝ)) :
    mobiusComplexFrame 0 x = (1 + AddCircle.toCircle x) / 2 := by
  simp [mobiusComplexFrame, div_eq_inv_mul]

@[simp]
theorem mobiusComplexFrame_one_apply (x : AddCircle (1 : ℝ)) :
    mobiusComplexFrame 1 x = Complex.I * (1 - AddCircle.toCircle x) / 2 := by
  simp [mobiusComplexFrame, div_eq_inv_mul, mul_assoc]

/-- At `[t]`, the frame is `s([t]) = exp (πit) (cos πt, sin πt)`: the real unit vector
`(cos πt, sin πt)` spanning the line of the Möbius bundle, which changes sign over one turn,
times the phase `exp (πit)`, which changes sign too. -/
theorem mobiusComplexFrame_apply_mk (i : Fin 2) (t : ℝ) :
    mobiusComplexFrame i t =
      Complex.exp ((π * t : ℝ) * Complex.I) * (![cos (π * t), sin (π * t)] i : ℝ) := by
  have hz : (AddCircle.toCircle (t : AddCircle (1 : ℝ)) : ℂ) =
      Complex.exp ((π * t : ℝ) * Complex.I) ^ 2 := by
    rw [AddCircle.toCircle_apply_mk, Circle.coe_exp, ← Complex.exp_natCast_mul]
    push_cast
    ring_nf
  have hsq : (cos (π * t) : ℂ) ^ 2 + (sin (π * t) : ℂ) ^ 2 = 1 := by
    exact_mod_cast cos_sq_add_sin_sq (π * t)
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin] at hz ⊢
  fin_cases i
  · rw [Fin.zero_eta, mobiusComplexFrame_zero_apply, hz, cons_val_zero]
    linear_combination (-1 / 2 : ℂ) * hsq + ((sin (π * t) : ℂ) ^ 2 / 2) * Complex.I_sq
  · rw [Fin.mk_one, mobiusComplexFrame_one_apply, hz, cons_val_one, cons_val_zero]
    linear_combination (-Complex.I / 2) * hsq -
      (Complex.I * (sin (π * t) : ℂ) ^ 2 / 2 + (cos (π * t) : ℂ) * sin (π * t)) * Complex.I_sq

/-- Multiplying two real numbers by a common phase does not change their Hermitian product. -/
private theorem exp_mul_I_mul_ofReal_mul_star (θ a b : ℝ) :
    Complex.exp (θ * Complex.I) * a * star (Complex.exp (θ * Complex.I) * b) = (a * b : ℝ) := by
  have h : Complex.exp (θ * Complex.I) * (starRingEnd ℂ) (Complex.exp (θ * Complex.I)) = 1 := by
    rw [← Complex.exp_conj, ← Complex.exp_add]
    simp
  rw [star_mul', Complex.star_def, Complex.conj_ofReal]
  push_cast
  linear_combination (a * b : ℂ) * h

/-- The frame `s` spans the image of `p`: `s s* = p` pointwise, with `s*` the conjugate transpose.
Equivalently `ρ = 2 s s* − 1`, so `ρ` is the reflection in the complex line spanned by `s`. -/
theorem vecMulVec_mobiusComplexFrame_star :
    vecMulVec mobiusComplexFrame (star mobiusComplexFrame) = mobiusProjection.map ofRealCM := by
  ext i j x
  induction x using QuotientAddGroup.induction_on with | H t => ?_
  rw [vecMulVec_apply, Pi.star_apply, ContinuousMap.mul_apply, ContinuousMap.star_apply,
    map_apply, RingHom.compLeftContinuous_apply_apply, Complex.coe_algebraMap,
    mobiusProjection_apply_mk, mobiusComplexFrame_apply_mk, mobiusComplexFrame_apply_mk,
    exp_mul_I_mul_ofReal_mul_star]

/-- The frame `s` is a unit vector at every point: `s* s = 1`. -/
theorem star_mobiusComplexFrame_dotProduct_self :
    star mobiusComplexFrame ⬝ᵥ mobiusComplexFrame = 1 := by
  ext x
  induction x using QuotientAddGroup.induction_on with | H t => ?_
  simp only [dotProduct, Fin.sum_univ_two, Pi.star_apply, ContinuousMap.add_apply,
    ContinuousMap.mul_apply, ContinuousMap.star_apply, ContinuousMap.one_apply,
    mobiusComplexFrame_apply_mk]
  rw [mul_comm (star _), exp_mul_I_mul_ofReal_mul_star, mul_comm (star _),
    exp_mul_I_mul_ofReal_mul_star]
  simp only [cons_val_zero, cons_val_one, ← sq]
  exact_mod_cast cos_sq_add_sin_sq (π * t)

/-- The reflection `ρ` acts on `C(ℝ / ℤ, ℂ)²` as `w ↦ 2 (s* w) s − w`. -/
private theorem map_mobiusReflection_mulVec (w : Fin 2 → 𝓒ℂ) :
    mobiusReflection.map ofRealCM *ᵥ w =
      (2 : ℝ) • ((star mobiusComplexFrame ⬝ᵥ w) • mobiusComplexFrame) - w := by
  have h := map_mobiusProjection_mulVec w
  rw [← vecMulVec_mobiusComplexFrame_star, vecMulVec_mulVec, op_smul_eq_smul] at h
  rw [h, smul_inv_smul₀ (two_ne_zero' ℝ), add_sub_cancel_left]

/-- The frame `s` is a section of the complex Möbius module. -/
theorem mobiusComplexFrame_mem_complexMobiusSections :
    mobiusComplexFrame ∈ complexMobiusSections := by
  rw [mem_complexMobiusSections_iff_mulVec, map_mobiusReflection_mulVec,
    star_mobiusComplexFrame_dotProduct_self, one_smul]
  module

/-- Every section `w` of the complex Möbius module is `(s* w) s`. -/
theorem star_mobiusComplexFrame_dotProduct_smul {w : Fin 2 → 𝓒ℂ}
    (hw : w ∈ complexMobiusSections) :
    (star mobiusComplexFrame ⬝ᵥ w) • mobiusComplexFrame = w := by
  rw [mem_complexMobiusSections_iff_mulVec, map_mobiusReflection_mulVec, sub_eq_iff_eq_add,
    ← two_smul ℝ w] at hw
  simpa only [inv_smul_smul₀ (two_ne_zero' ℝ)] using congr((2⁻¹ : ℝ) • $hw)

/-! ### The complex Möbius module is free of rank one -/

/-- The complex Möbius module is free of rank one: `g ↦ g s` is an isomorphism
`C(ℝ / ℤ, ℂ) ≃ M_ℂ`, with inverse `w ↦ s* w`. Since `s([t]) = exp (πit) (cos πt, sin πt)`, the
section `g s` has coefficient `t ↦ exp (πit) g([t])` along `(cos πt, sin πt)`, an antiperiodic
function of `t`. -/
def complexMobiusSectionsEquiv : 𝓒ℂ ≃ₗ[𝓒ℂ] complexMobiusSections where
  toFun g := ⟨g • mobiusComplexFrame,
    Submodule.smul_mem _ g mobiusComplexFrame_mem_complexMobiusSections⟩
  map_add' g h := Subtype.ext <| by exact add_smul g h mobiusComplexFrame
  map_smul' c g := Subtype.ext <| by exact smul_assoc c g mobiusComplexFrame
  invFun w := star mobiusComplexFrame ⬝ᵥ (w : Fin 2 → 𝓒ℂ)
  left_inv g := by
    refine (dotProduct_smul g (star mobiusComplexFrame) mobiusComplexFrame).trans ?_
    rw [star_mobiusComplexFrame_dotProduct_self, smul_eq_mul, mul_one]
  right_inv w := Subtype.ext (star_mobiusComplexFrame_dotProduct_smul w.property)

@[simp]
theorem coe_complexMobiusSectionsEquiv_apply (g : 𝓒ℂ) :
    (complexMobiusSectionsEquiv g : Fin 2 → 𝓒ℂ) = g • mobiusComplexFrame :=
  (rfl)

@[simp]
theorem complexMobiusSectionsEquiv_symm_apply (w : complexMobiusSections) :
    complexMobiusSectionsEquiv.symm w = star mobiusComplexFrame ⬝ᵥ (w : Fin 2 → 𝓒ℂ) :=
  (rfl)

instance : Module.Free 𝓒ℂ complexMobiusSections :=
  .of_equiv complexMobiusSectionsEquiv

instance : Module.Finite 𝓒ℂ complexMobiusSections :=
  .equiv complexMobiusSectionsEquiv

/-! ### Complexification -/

/-- The complex Möbius module is the image of the complexified projection `p` acting on rows. -/
theorem range_vecMulLinear_map_mobiusProjection :
    LinearMap.range (vecMulLinear (mobiusProjection.map ofRealCM)) = complexMobiusSections := by
  have hp (w : Fin 2 → 𝓒ℂ) : w ᵥ* mobiusProjection.map ofRealCM =
      (star mobiusComplexFrame ⬝ᵥ w) • mobiusComplexFrame := by
    rw [← transpose_mobiusProjection, transpose_map, vecMul_transpose,
      ← vecMulVec_mobiusComplexFrame_star, vecMulVec_mulVec, op_smul_eq_smul]
  refine le_antisymm ?_ fun w hw ↦ ⟨w, ?_⟩
  · rintro _ ⟨w, rfl⟩
    rw [vecMulLinear_apply, hp]
    exact Submodule.smul_mem _ _ mobiusComplexFrame_mem_complexMobiusSections
  · rw [vecMulLinear_apply, hp, star_mobiusComplexFrame_dotProduct_smul hw]

/-- **Complexification of the Möbius module.** Extending scalars along the pointwise inclusion
`C(ℝ / ℤ, ℝ) →+* C(ℝ / ℤ, ℂ)` identifies the balanced tensor product
`C(ℝ / ℤ, ℂ) ⊗_{C(ℝ / ℤ, ℝ)} M` with the complex Möbius module, sending `c ⊗ w` to `c w`. -/
def mobiusSectionsComplexifyEquiv :
    BalancedExtension ofRealCM mobiusSections ≃ₗ[𝓒ℂ] complexMobiusSections :=
  (BalancedExtension.congr _ (LinearEquiv.ofEq _ _ range_vecMulLinear_mobiusProjection.symm)).trans
    ((BalancedExtension.rangeVecMulLinearEquiv _ isIdempotentElem_mobiusProjection).trans
      (LinearEquiv.ofEq _ _ range_vecMulLinear_map_mobiusProjection))

@[simp]
theorem coe_mobiusSectionsComplexifyEquiv_tmul (c : 𝓒ℂ) (w : mobiusSections) :
    (mobiusSectionsComplexifyEquiv (BalancedExtension.tmul ofRealCM c w) : Fin 2 → 𝓒ℂ) =
      fun i ↦ c * ofRealCM ((w : Fin 2 → 𝓒) i) := by
  simp only [mobiusSectionsComplexifyEquiv, LinearEquiv.trans_apply, BalancedExtension.congr_tmul,
    LinearEquiv.coe_ofEq_apply, BalancedExtension.coe_rangeVecMulLinearEquiv_tmul]

/-- The complexified Möbius module is free of rank one:
`C(ℝ / ℤ, ℂ) ⊗_{C(ℝ / ℤ, ℝ)} M ≃ C(ℝ / ℤ, ℂ)`, sending `c ⊗ w` to `s* (c w)`, although `M`
itself is not free (`not_free_mobiusSections`). -/
def mobiusSectionsComplexTrivializationEquiv :
    BalancedExtension ofRealCM mobiusSections ≃ₗ[𝓒ℂ] 𝓒ℂ :=
  mobiusSectionsComplexifyEquiv.trans complexMobiusSectionsEquiv.symm

@[simp]
theorem mobiusSectionsComplexTrivializationEquiv_tmul (c : 𝓒ℂ) (w : mobiusSections) :
    mobiusSectionsComplexTrivializationEquiv (BalancedExtension.tmul ofRealCM c w) =
      star mobiusComplexFrame ⬝ᵥ fun i ↦ c * ofRealCM ((w : Fin 2 → 𝓒) i) := by
  simp [mobiusSectionsComplexTrivializationEquiv]

instance : Module.Free 𝓒ℂ (BalancedExtension ofRealCM mobiusSections) :=
  .of_equiv mobiusSectionsComplexTrivializationEquiv.symm

end TauCeti
