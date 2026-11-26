/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import TauCeti.LinearAlgebra.TensorProduct.Balanced.Extension
public import TauCeti.Topology.Instances.AddCircle.MobiusModule.Basic

/-!
# The complexified Möbius module is free of rank one

The Möbius module `M = TauCeti.mobiusSections ℝ` over `R = C(ℝ / ℤ, ℝ)`, the fixed module of the
reflection `ρ([t]) = [[cos 2πt, sin 2πt], [sin 2πt, −cos 2πt]]` acting on `R²`, is finitely
generated projective but not free (`TauCeti.not_free_mobiusSections`): it is the module of
continuous sections of the Möbius line bundle, which is nontrivial. Over the complex numbers every
line bundle on the circle is trivial. This file proves the module-theoretic form of that fact:
extending scalars along the pointwise inclusion `R → R_ℂ = C(ℝ / ℤ, ℂ)` makes `M` free of rank
one.

1. **Extension of scalars.** Since `M` is the image of the symmetric idempotent `p = (1 + ρ) / 2`
   (`TauCeti.range_vecMulLinear_mobiusProjection`), for a continuous `ℝ`-algebra homomorphism
   `A → B` the balanced extension of scalars of `mobiusSections A` is the image of `p` acting on
   `C(ℝ / ℤ, B)²`, which is `mobiusSections B` (`TauCeti.mobiusSectionsExtendEquiv`, through
   `c ⊗ w ↦ c w`). For `ℝ → ℂ` this identifies `R_ℂ ⊗_R M` with the complex Möbius module
   `M_ℂ = TauCeti.mobiusSections ℂ` (`TauCeti.mobiusSectionsComplexifyEquiv`).
2. **A complex frame.** With `z = fourier 1`, the function `[t] ↦ exp (2πit)`, the pair
   `s = ((1 + z) / 2, i (1 − z) / 2)` (`TauCeti.mobiusComplexFrame`) is a continuous section of
   `M_ℂ` with `s* s = 1` and `s s* = p`. At `[t]` it is `exp (πit) (cos πt, sin πt)`: the twist of
   the real line `ℝ (cos πt, sin πt)` is undone by the complex phase `exp (πit)`, which also
   changes sign over one turn. Hence `g ↦ g s` is an isomorphism `R_ℂ ≃ M_ℂ` with inverse
   `w ↦ s* w` (`TauCeti.mobiusSectionsComplexEquiv`), and `R_ℂ ⊗_R M ≃ R_ℂ`
   (`TauCeti.mobiusSectionsComplexTrivializationEquiv`).

Read in `K₀`, this is the vanishing of the image in `K₀(R_ℂ)` of the class `[M] − [R]`, which has
order two in `K₀(R)`: extension of scalars sends `[M]` to `[R_ℂ ⊗_R M] = [R_ℂ]`.

## Main definitions

* `TauCeti.mobiusSectionsExtendEquiv`: `C(ℝ / ℤ, B) ⊗ mobiusSections A ≃ mobiusSections B`.
* `TauCeti.mobiusSectionsComplexifyEquiv`: `C(ℝ / ℤ, ℂ) ⊗_R M ≃ M_ℂ`, `c ⊗ w ↦ c w`.
* `TauCeti.mobiusComplexFrame`: the unit section `s = ((1 + z) / 2, i (1 − z) / 2)` of `M_ℂ`.
* `TauCeti.mobiusSectionsComplexEquiv`: `C(ℝ / ℤ, ℂ) ≃ M_ℂ`, `g ↦ g s`.
* `TauCeti.mobiusSectionsComplexTrivializationEquiv`: `C(ℝ / ℤ, ℂ) ⊗_R M ≃ C(ℝ / ℤ, ℂ)`.

## Main results

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

/-! ### Extension of scalars -/

section ScalarExtension

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [Algebra ℝ A] [ContinuousSMul ℝ A]
  {B : Type*} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
  [Algebra ℝ B] [ContinuousSMul ℝ B]

/-- **Balanced scalar extension of the Möbius module.** For a continuous `ℝ`-algebra homomorphism
`φ : A →ₐ[ℝ] B` with induced ring homomorphism
`f = (φ : A →+* B).compLeftContinuous _ hφ : C(ℝ / ℤ, A) →+* C(ℝ / ℤ, B)`, the balanced tensor
product `BalancedExtension f (mobiusSections A)` is isomorphic as a `C(ℝ / ℤ, B)`-module to
`mobiusSections B`, sending `c ⊗ w` to `i ↦ c * f (w i)`. -/
def mobiusSectionsExtendEquiv (φ : A →ₐ[ℝ] B) (hφ : Continuous φ) :
    BalancedExtension ((φ : A →+* B).compLeftContinuous (AddCircle (1 : ℝ)) hφ)
      (mobiusSections A) ≃ₗ[C(AddCircle (1 : ℝ), B)] mobiusSections B :=
  (BalancedExtension.congr _ (LinearEquiv.ofEq _ _ range_vecMulLinear_mobiusProjection.symm)).trans
    ((BalancedExtension.rangeVecMulLinearEquiv _ isIdempotentElem_mobiusProjection).trans
      (LinearEquiv.ofEq _ _ <| by
        rw [map_mobiusProjection, range_vecMulLinear_mobiusProjection]))

@[simp]
theorem coe_mobiusSectionsExtendEquiv_tmul (φ : A →ₐ[ℝ] B) (hφ : Continuous φ)
    (c : C(AddCircle (1 : ℝ), B)) (w : mobiusSections A) :
    (mobiusSectionsExtendEquiv φ hφ
      (BalancedExtension.tmul ((φ : A →+* B).compLeftContinuous (AddCircle (1 : ℝ)) hφ) c w) :
      Fin 2 → C(AddCircle (1 : ℝ), B)) =
      fun i ↦ c *
        (φ : A →+* B).compLeftContinuous _ hφ ((w : Fin 2 → C(AddCircle (1 : ℝ), A)) i) := by
  simp only [mobiusSectionsExtendEquiv, LinearEquiv.trans_apply, BalancedExtension.congr_tmul,
    LinearEquiv.coe_ofEq_apply, BalancedExtension.coe_rangeVecMulLinearEquiv_tmul]

/-- Explicit formula for the inverse of `mobiusSectionsExtendEquiv` through the rows of the
projection `p = (1 + ρ) / 2`: a section `w` of `mobiusSections B` maps to `∑ i, wᵢ ⊗ pᵢ`. -/
theorem mobiusSectionsExtendEquiv_symm_apply (φ : A →ₐ[ℝ] B) (hφ : Continuous φ)
    (w : mobiusSections B) :
    (mobiusSectionsExtendEquiv φ hφ).symm w =
      ∑ i : Fin 2, BalancedExtension.tmul
        ((φ : A →+* B).compLeftContinuous (AddCircle (1 : ℝ)) hφ)
        ((w : Fin 2 → C(AddCircle (1 : ℝ), B)) i)
        ⟨mobiusProjection A i, mobiusProjection_mem_mobiusSections i⟩ := by
  simp only [mobiusSectionsExtendEquiv, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    LinearEquiv.ofEq_symm, BalancedExtension.congr_symm,
    BalancedExtension.rangeVecMulLinearEquiv_symm_apply, map_sum, BalancedExtension.congr_tmul,
    LinearEquiv.coe_ofEq_apply]
  exact Finset.sum_congr rfl fun i _ ↦
    congrArg _ (Subtype.ext (LinearEquiv.coe_ofEq_apply _ _))

end ScalarExtension

local notation "𝓒" => C(AddCircle (1 : ℝ), ℝ)

local notation "𝓒ℂ" => C(AddCircle (1 : ℝ), ℂ)

/-- The pointwise inclusion `C(ℝ / ℤ, ℝ) →+* C(ℝ / ℤ, ℂ)`. -/
local notation "ofRealCM" =>
  RingHom.compLeftContinuous (AddCircle (1 : ℝ)) (algebraMap ℝ ℂ) Complex.continuous_ofReal

/-- **Complexification of the Möbius module.** Extending scalars along the pointwise inclusion
`C(ℝ / ℤ, ℝ) →+* C(ℝ / ℤ, ℂ)` identifies the balanced tensor product
`C(ℝ / ℤ, ℂ) ⊗_{C(ℝ / ℤ, ℝ)} M` with the complex Möbius module, sending `c ⊗ w` to `c w`. -/
def mobiusSectionsComplexifyEquiv :
    BalancedExtension ofRealCM (mobiusSections ℝ) ≃ₗ[𝓒ℂ] mobiusSections ℂ :=
  mobiusSectionsExtendEquiv (Algebra.ofId ℝ ℂ) Complex.continuous_ofReal

@[simp]
theorem coe_mobiusSectionsComplexifyEquiv_tmul (c : 𝓒ℂ) (w : mobiusSections ℝ) :
    (mobiusSectionsComplexifyEquiv (BalancedExtension.tmul ofRealCM c w) : Fin 2 → 𝓒ℂ) =
      fun i ↦ c * ofRealCM ((w : Fin 2 → 𝓒) i) :=
  coe_mobiusSectionsExtendEquiv_tmul (Algebra.ofId ℝ ℂ) Complex.continuous_ofReal c w

/-- Explicit formula for the inverse of `mobiusSectionsComplexifyEquiv`: a section `w` of the
complex Möbius module maps to `∑ i, wᵢ ⊗ pᵢ`, through the rows `pᵢ` of the real projection
`p = (1 + ρ) / 2`. -/
theorem mobiusSectionsComplexifyEquiv_symm_apply (w : mobiusSections ℂ) :
    mobiusSectionsComplexifyEquiv.symm w =
      ∑ i : Fin 2, BalancedExtension.tmul ofRealCM ((w : Fin 2 → 𝓒ℂ) i)
        ⟨mobiusProjection ℝ i, mobiusProjection_mem_mobiusSections i⟩ :=
  mobiusSectionsExtendEquiv_symm_apply (Algebra.ofId ℝ ℂ) Complex.continuous_ofReal w

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

/-- The frame `s` spans the image of `p`: `s s* = p` pointwise, with `s*` the conjugate transpose.
Equivalently `ρ = 2 s s* − 1`, so `ρ` is the reflection in the complex line spanned by `s`. -/
theorem vecMulVec_mobiusComplexFrame_star :
    vecMulVec mobiusComplexFrame (star mobiusComplexFrame) = mobiusProjection ℂ := by
  ext i j x
  induction x using QuotientAddGroup.induction_on with | H t => ?_
  have h : Complex.exp ((π * t : ℝ) * Complex.I) *
      starRingEnd ℂ (Complex.exp ((π * t : ℝ) * Complex.I)) = 1 := by
    rw [Complex.mul_conj', Complex.norm_exp_ofReal_mul_I]
    simp
  simp only [vecMulVec_apply, Pi.star_apply, ContinuousMap.mul_apply, ContinuousMap.star_apply,
    mobiusProjection_apply_mk, mobiusComplexFrame_apply_mk, star_mul', Complex.star_def,
    Complex.conj_ofReal, Complex.coe_algebraMap, Complex.ofReal_mul] at h ⊢
  linear_combination (↑(![cos (π * t), sin (π * t)] i) * ↑(![cos (π * t), sin (π * t)] j) : ℂ) * h

/-- The frame `s` is a unit vector at every point: `s* s = 1`. -/
theorem star_mobiusComplexFrame_dotProduct_self :
    star mobiusComplexFrame ⬝ᵥ mobiusComplexFrame = 1 := by
  ext x
  induction x using QuotientAddGroup.induction_on with | H t => ?_
  simp only [dotProduct, Fin.sum_univ_two, Pi.star_apply, ContinuousMap.add_apply,
    ContinuousMap.mul_apply, ContinuousMap.star_apply, ContinuousMap.one_apply,
    mobiusComplexFrame_apply_mk, Complex.star_def, Complex.conj_mul', norm_mul,
    Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
    cons_val_zero, cons_val_one]
  norm_cast
  rw [sq_abs, sq_abs, cos_sq_add_sin_sq]

/-- The reflection `ρ` acts on `C(ℝ / ℤ, ℂ)²` as `w ↦ 2 (s* w) s − w`. -/
private theorem mobiusReflection_complex_mulVec (w : Fin 2 → 𝓒ℂ) :
    mobiusReflection ℂ *ᵥ w =
      (2 : ℝ) • ((star mobiusComplexFrame ⬝ᵥ w) • mobiusComplexFrame) - w := by
  have h := mobiusProjection_mulVec w
  rw [← vecMulVec_mobiusComplexFrame_star, vecMulVec_mulVec, op_smul_eq_smul] at h
  rw [h, smul_inv_smul₀ (two_ne_zero' ℝ), add_sub_cancel_left]

/-- The frame `s` is a section of the complex Möbius module. -/
theorem mobiusComplexFrame_mem_mobiusSections : mobiusComplexFrame ∈ mobiusSections ℂ := by
  rw [mem_mobiusSections_iff_mulVec, mobiusReflection_complex_mulVec,
    star_mobiusComplexFrame_dotProduct_self, one_smul]
  module

/-- Every section `w` of the complex Möbius module is `(s* w) s`. -/
theorem star_mobiusComplexFrame_dotProduct_smul {w : Fin 2 → 𝓒ℂ} (hw : w ∈ mobiusSections ℂ) :
    (star mobiusComplexFrame ⬝ᵥ w) • mobiusComplexFrame = w := by
  rw [mem_mobiusSections_iff_mulVec, mobiusReflection_complex_mulVec, sub_eq_iff_eq_add,
    ← two_smul ℝ w] at hw
  simpa only [inv_smul_smul₀ (two_ne_zero' ℝ)] using congr((2⁻¹ : ℝ) • $hw)

/-! ### The complex Möbius module is free of rank one -/

/-- The complex Möbius module is free of rank one: `g ↦ g s` is an isomorphism
`C(ℝ / ℤ, ℂ) ≃ M_ℂ`, with inverse `w ↦ s* w`. Since `s([t]) = exp (πit) (cos πt, sin πt)`, the
section `g s` has coefficient `t ↦ exp (πit) g([t])` along `(cos πt, sin πt)`, an antiperiodic
function of `t`. -/
def mobiusSectionsComplexEquiv : 𝓒ℂ ≃ₗ[𝓒ℂ] mobiusSections ℂ where
  toFun g := ⟨g • mobiusComplexFrame,
    Submodule.smul_mem _ g mobiusComplexFrame_mem_mobiusSections⟩
  map_add' g h := Subtype.ext <| by
    simp only [Submodule.coe_add]
    exact add_smul g h mobiusComplexFrame
  map_smul' c g := Subtype.ext <| by
    simp only [Submodule.coe_smul, RingHom.id_apply, smul_assoc]
  invFun w := star mobiusComplexFrame ⬝ᵥ (w : Fin 2 → 𝓒ℂ)
  left_inv g := by
    refine (dotProduct_smul g (star mobiusComplexFrame) mobiusComplexFrame).trans ?_
    rw [star_mobiusComplexFrame_dotProduct_self, smul_eq_mul, mul_one]
  right_inv w := Subtype.ext (star_mobiusComplexFrame_dotProduct_smul w.property)

@[simp]
theorem coe_mobiusSectionsComplexEquiv_apply (g : 𝓒ℂ) :
    (mobiusSectionsComplexEquiv g : Fin 2 → 𝓒ℂ) = g • mobiusComplexFrame :=
  (rfl)

@[simp]
theorem mobiusSectionsComplexEquiv_symm_apply (w : mobiusSections ℂ) :
    mobiusSectionsComplexEquiv.symm w = star mobiusComplexFrame ⬝ᵥ (w : Fin 2 → 𝓒ℂ) :=
  (rfl)

instance : Module.Free 𝓒ℂ (mobiusSections ℂ) :=
  .of_equiv mobiusSectionsComplexEquiv

/-- The complexified Möbius module is free of rank one:
`C(ℝ / ℤ, ℂ) ⊗_{C(ℝ / ℤ, ℝ)} M ≃ C(ℝ / ℤ, ℂ)`, sending `c ⊗ w` to `s* (c w)`, although `M`
itself is not free (`not_free_mobiusSections`). -/
def mobiusSectionsComplexTrivializationEquiv :
    BalancedExtension ofRealCM (mobiusSections ℝ) ≃ₗ[𝓒ℂ] 𝓒ℂ :=
  mobiusSectionsComplexifyEquiv.trans mobiusSectionsComplexEquiv.symm

@[simp]
theorem mobiusSectionsComplexTrivializationEquiv_tmul (c : 𝓒ℂ) (w : mobiusSections ℝ) :
    mobiusSectionsComplexTrivializationEquiv (BalancedExtension.tmul ofRealCM c w) =
      star mobiusComplexFrame ⬝ᵥ fun i ↦ c * ofRealCM ((w : Fin 2 → 𝓒) i) := by
  simp [mobiusSectionsComplexTrivializationEquiv]

instance : Module.Free 𝓒ℂ (BalancedExtension ofRealCM (mobiusSections ℝ)) :=
  .of_equiv mobiusSectionsComplexTrivializationEquiv.symm

end TauCeti
