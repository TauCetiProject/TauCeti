/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import TauCeti.NumberTheory.ModularForms.DedekindEta.Power
import TauCeti.LinearAlgebra.Matrix.Diagonal
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic
import TauCeti.NumberTheory.Modular.Abelianization

/-!
# Galois conjugation of the character of `η²`

Squaring the eta multiplier `ε(γ)` removes the choice of square root in the transformation law of
`η`: `η(γ τ)² = ε(γ)² (c τ + d) η(τ)²`. Since `c τ + d` is a cocycle, `γ ↦ ε(γ)²` is a character
of `SL(2, ℤ)` (`TauCeti.ModularForm.etaMultiplier_mul_sq`), with values in the twelfth roots of
unity and trivial on `Γ(12)`.

This file computes how a ring endomorphism `σ` of `ℂ` acts on this character. For a level `M`
divisible by `12`, let `σ (ζ_M) = ζ_M ^ d` with `ζ_M = e^{2πi/M}` and `d` a unit modulo `M`, and
let `D = diag(1, d)`. If `γ D = D γ'` modulo `M`, then `ε(γ')² = σ(ε(γ)²)`
(`TauCeti.ModularForm.etaMultiplier_sq_eq_of_mul_diagonal_eq`). Both sides are characters of `γ`:
the left one because `ε²` factors through `SL(2, ℤ/Mℤ)` and `γ ↦ D⁻¹ γ D` is a homomorphism there.
A character of `SL(2, ℤ)` with values in a commutative group is determined by its value at `T`,
whose class generates the abelianization, and at `T` both sides are `e^{2πi d/12}`, since
`D⁻¹ T D = T^d` and `ε(T)² = e^{2πi/12} = ζ_M^{M/12}`.

This is the transformation rule that makes the Fourier-coefficient action of `σ` on modular
functions compatible with division by powers of `η²`: the quotient `f / η^{2k}` of a modular form
of weight `k` and level `N` is a modular function of level `12 N`, and `σ` twists its
transformation under `SL(2, ℤ)` exactly by this rule.

## Main results

* `TauCeti.ModularForm.etaMultiplier_mul_sq`: `ε(γ δ)² = ε(γ)² ε(δ)²`.
* `TauCeti.ModularForm.etaMultiplier_sq_eq_of_mul_diagonal_eq`: `ε(γ')² = σ(ε(γ)²)` when
  `γ diag(1, d) = diag(1, d) γ'` modulo `M` and `σ(ζ_M) = ζ_M ^ d`.

## References

* Goro Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, Princeton
  University Press, 1971, §6.1, for the twisted action of `σ` through `diag(1, d)`.
-/

public section

open Complex Matrix ModularGroup
open scoped Real ModularForm MatrixGroups UpperHalfPlane

namespace TauCeti.ModularForm

/-- **The square of the eta multiplier is a character**: `ε(γ δ)² = ε(γ)² ε(δ)²`, because `η²`
transforms in weight one with the multiplier `ε²`. -/
theorem etaMultiplier_mul_sq (γ δ : SL(2, ℤ)) :
    etaMultiplier (γ * δ) ^ 2 = etaMultiplier γ ^ 2 * etaMultiplier δ ^ 2 := by
  have h := eta_zpow_two_mul_slash 1 (γ * δ)
  rw [SlashAction.slash_mul, eta_zpow_two_mul_slash, _root_.ModularForm.SL_smul_slash,
    eta_zpow_two_mul_slash, smul_smul] at h
  have hI := congrFun h UpperHalfPlane.I
  simp only [Pi.smul_apply, smul_eq_mul, mul_one] at hI
  have hη : (η (UpperHalfPlane.I : ℂ)) ^ (2 : ℤ) ≠ 0 :=
    zpow_ne_zero _ (_root_.ModularForm.eta_ne_zero UpperHalfPlane.I.im_pos)
  have := mul_right_cancel₀ hη hI
  norm_num at this
  exact_mod_cast this.symm

/-- The character `γ ↦ ε(γ)²` of `SL(2, ℤ)`, with values in `ℂˣ`. -/
private noncomputable def etaMultiplierSqHom : SL(2, ℤ) →* ℂˣ where
  toFun γ := Units.mk0 (etaMultiplier γ ^ 2) (pow_ne_zero _ (etaMultiplier_ne_zero γ))
  map_one' := Units.ext (by simp)
  map_mul' γ δ := Units.ext (by simp [etaMultiplier_mul_sq])

private theorem coe_etaMultiplierSqHom (γ : SL(2, ℤ)) :
    (etaMultiplierSqHom γ : ℂ) = etaMultiplier γ ^ 2 :=
  rfl

/-- Conjugation `g ↦ diag(1, d)⁻¹ g diag(1, d)` of `SL(2, R)` by a diagonal matrix of
`GL(2, R)`. -/
private def conjDiagonal {R : Type*} [CommRing R] (d : Rˣ) : SL(2, R) →* SL(2, R) where
  toFun g := ⟨diagonal ![1, ((d⁻¹ : Rˣ) : R)] * g * diagonal ![1, (d : R)], by
    simp [det_mul, det_diagonal, Fin.prod_univ_two]⟩
  map_one' := by
    ext i j
    -- the matrix of the identity of `SL(2, R)` is the identity matrix
    change (diagonal ![1, ((d⁻¹ : Rˣ) : R)] * (1 : Matrix (Fin 2) (Fin 2) R) *
      diagonal ![1, (d : R)]) i j = (1 : Matrix (Fin 2) (Fin 2) R) i j
    rw [Matrix.mul_one, TauCeti.diagonal_vec2_one_mul_eq_one d.inv_mul]
  map_mul' g h := by
    ext i j
    -- the matrix of a product in `SL(2, R)` is the product of the matrices of the factors
    change (diagonal ![1, ((d⁻¹ : Rˣ) : R)] * ((g : Matrix (Fin 2) (Fin 2) R) * h) *
        diagonal ![1, (d : R)]) i j = ((diagonal ![1, ((d⁻¹ : Rˣ) : R)] * g *
        diagonal ![1, (d : R)]) *
          (diagonal ![1, ((d⁻¹ : Rˣ) : R)] * h * diagonal ![1, (d : R)])) i j
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (diagonal ![1, (d : R)]),
      TauCeti.diagonal_vec2_one_mul_eq_one d.mul_inv, Matrix.one_mul]

private theorem coe_conjDiagonal {R : Type*} [CommRing R] (d : Rˣ) (g : SL(2, R)) :
    (conjDiagonal d g : Matrix (Fin 2) (Fin 2) R) =
      diagonal ![1, ((d⁻¹ : Rˣ) : R)] * g * diagonal ![1, (d : R)] :=
  rfl

/-- **Galois conjugation of the character of `η²`.** Let `12 ∣ M`, let `σ` be a ring endomorphism
of `ℂ` with `σ (ζ_M) = ζ_M ^ d` for `ζ_M = e^{2πi/M}` and a unit `d` modulo `M`, and let
`γ, γ' ∈ SL(2, ℤ)` satisfy `γ diag(1, d) = diag(1, d) γ'` modulo `M`. Then
`ε(γ')² = σ(ε(γ)²)`. -/
theorem etaMultiplier_sq_eq_of_mul_diagonal_eq {M : ℕ} [NeZero M] (hM : 12 ∣ M)
    {σ : ℂ →+* ℂ} {d : (ZMod M)ˣ}
    (hσ : σ (ZMod.stdAddChar (1 : ZMod M)) = ZMod.stdAddChar (d : ZMod M)) {γ γ' : SL(2, ℤ)}
    (h : ((SpecialLinearGroup.map (Int.castRingHom (ZMod M)) γ : SL(2, ZMod M)) :
        Matrix (Fin 2) (Fin 2) (ZMod M)) * diagonal ![1, (d : ZMod M)] =
      diagonal ![1, (d : ZMod M)] * (SpecialLinearGroup.map (Int.castRingHom (ZMod M)) γ')) :
    etaMultiplier γ' ^ 2 = σ (etaMultiplier γ ^ 2) := by
  set red : SL(2, ℤ) →* SL(2, ZMod M) := SpecialLinearGroup.map (Int.castRingHom (ZMod M))
  have hsurj : Function.Surjective red := SpecialLinearGroup.map_intCast_zmod_surjective
  -- `ε²` is trivial on `Γ(M) = ker red`, so it factors through `SL(2, ℤ/Mℤ)`
  have hker : red.ker ≤ etaMultiplierSqHom.ker := fun γ hγ ↦ by
    refine MonoidHom.mem_ker.2 (Units.ext ?_)
    rw [coe_etaMultiplierSqHom, Units.val_one, ← zpow_natCast]
    exact etaMultiplier_zpow_eq_one_of_mem_Gamma even_two
      (by rw [show (24 : ℤ) = 2 * 12 by norm_num]; exact mul_dvd_mul_left 2 (by exact_mod_cast hM))
      (CongruenceSubgroup.Gamma_mem'.2 hγ)
  let χ := red.liftOfRightInverse (Function.surjInv hsurj) (Function.rightInverse_surjInv hsurj)
    ⟨etaMultiplierSqHom, hker⟩
  have hχ (γ : SL(2, ℤ)) : χ (red γ) = etaMultiplierSqHom γ :=
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ γ
  -- the two characters `γ ↦ ε²(D⁻¹ γ D)` and `σ ∘ ε²` agree at `T`, hence everywhere
  have hT : conjDiagonal d (red T) = red (T ^ ((d : ZMod M).val : ℤ)) := by
    ext i j
    rw [coe_conjDiagonal]
    fin_cases i <;> fin_cases j <;>
      simp [red, -map_zpow, SpecialLinearGroup.map_apply_coe, coe_T, coe_T_zpow, Matrix.mul_apply,
        diagonal, ZMod.natCast_val]
  have hζ : ∀ n : ℕ, cexp (π * I * n / 12) ^ 2 =
      ZMod.stdAddChar (n : ZMod M) ^ (M / 12) := by
    intro n
    have h12 : ((M / 12 : ℕ) : ℂ) * 12 = M := by exact_mod_cast Nat.div_mul_cancel hM
    have hM0 : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne M)
    rw [show (n : ZMod M) = ((n : ℤ) : ZMod M) by simp, ZMod.stdAddChar_coe,
      ← Complex.exp_natCast_mul, ← Complex.exp_natCast_mul]
    congr 1
    field_simp
    rw [← h12]
    push_cast
    ring
  have key : χ.comp ((conjDiagonal d).comp red) = (Units.map σ.toMonoidHom).comp
      etaMultiplierSqHom := by
    refine TauCeti.ModularGroup.sl2z_hom_ext_T (Units.ext ?_)
    simp only [MonoidHom.comp_apply, hT, hχ, coe_etaMultiplierSqHom, Units.coe_map,
      RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, etaMultiplier_T_zpow, etaMultiplier_T]
    rw [Int.cast_natCast, hζ, show π * I / 12 = π * I * ((1 : ℕ) : ℂ) / 12 by simp, hζ,
      map_pow, Nat.cast_one, hσ, ZMod.natCast_zmod_val]
  have hγ' : conjDiagonal d (red γ) = red γ' := by
    ext : 1
    rw [coe_conjDiagonal, Matrix.mul_assoc, h, ← Matrix.mul_assoc,
      TauCeti.diagonal_vec2_one_mul_eq_one d.inv_mul, Matrix.one_mul]
  have := congrArg Units.val (DFunLike.congr_fun key γ)
  simpa [hγ', hχ, coe_etaMultiplierSqHom] using this

end TauCeti.ModularForm
