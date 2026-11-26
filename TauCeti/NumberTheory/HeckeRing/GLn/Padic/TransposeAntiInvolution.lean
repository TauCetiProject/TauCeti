/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Transpose
public import TauCeti.NumberTheory.HeckeRing.Commutativity
public import TauCeti.NumberTheory.HeckeRing.GLn.Padic.Cosets

/-!
# Commutativity of the local `p`-adic `GL_n` Hecke rings

Matrix transposition `g ↦ gᵀ` is an anti-automorphism of `GL_n(ℚ_p)` preserving both `GL_n(ℤ_p)`
(`TauCeti.GLPadicInt.transpose_mem`) and `M_n(ℤ_p) ∩ GL_n(ℚ_p)`
(`HeckeRing.GLn.transposeMulEquiv_mem_padicIntEntries`), so it restricts to a
`HeckeAntiInvolution` on both `(padicIntEntries (Fin n) p, GLPadicInt (Fin n) p)` and
`(⊤, GLPadicInt (Fin n) p)`. Every double coset has a diagonal representative
(`HeckeRing.GLn.padicNatPowDiagCosetEquiv` and `HeckeRing.GLn.padicIntPowDiagCosetEquiv`), and
transposition fixes diagonal matrices, so Shimura's Proposition 3.8 makes both the integral and
rational local `p`-adic Hecke rings commutative over any commutative coefficient semiring.

## Main definitions and results

* `HeckeRing.GLn.padicIntegralTransposeAntiInvolution`,
  `HeckeRing.GLn.padicRationalTransposeAntiInvolution`: transposition as a `HeckeAntiInvolution` on
  the integral and rational local `p`-adic Hecke pairs.
* `HeckeRing.GLn.mul_comm_padicIntegralHeckeRing`,
  `HeckeRing.GLn.commSemiringPadicIntegralHeckeRing`,
  `HeckeRing.GLn.commRingPadicIntegralHeckeRing`: commutativity of the integral local Hecke ring.
* `HeckeRing.GLn.mul_comm_padicRationalHeckeRing`,
  `HeckeRing.GLn.commSemiringPadicRationalHeckeRing`,
  `HeckeRing.GLn.commRingPadicRationalHeckeRing`: commutativity of the rational local Hecke ring.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  Proposition 3.8.
* [J. A. Rhodes and T. R. Shemanske,
  *Rationality theorems for Hecke operators on GL_n*][rhodes1999], §2.
-/

public section

open Matrix TauCeti
open scoped HeckeCosetModule

namespace HeckeRing.GLn

variable (n p : ℕ) [Fact p.Prime]

/-- Transposition as an anti-involution of `(padicIntEntries (Fin n) p, GLPadicInt (Fin n) p)`. -/
noncomputable def padicIntegralTransposeAntiInvolution :
    _root_.HeckeAntiInvolution (padicIntEntries (Fin n) p) (GLPadicInt (Fin n) p) :=
  _root_.HeckeAntiInvolution.ofAmbient
    (Matrix.GeneralLinearGroup.transposeMulEquiv (R := ℚ_[p]) (Fin n)).toMonoidHom
    Matrix.GeneralLinearGroup.transposeMulEquiv_transposeMulEquiv
    (fun _ hg ↦ GLPadicInt.transpose_mem hg)
    (fun _ hg ↦ transposeMulEquiv_mem_padicIntEntries hg)

/-- Transposition as an anti-involution of `(⊤, GLPadicInt (Fin n) p)` in `GL_n(ℚ_p)`. -/
noncomputable def padicRationalTransposeAntiInvolution :
    _root_.HeckeAntiInvolution (⊤ : Submonoid (GL (Fin n) ℚ_[p])) (GLPadicInt (Fin n) p) :=
  _root_.HeckeAntiInvolution.ofAmbient
    (Matrix.GeneralLinearGroup.transposeMulEquiv (R := ℚ_[p]) (Fin n)).toMonoidHom
    Matrix.GeneralLinearGroup.transposeMulEquiv_transposeMulEquiv
    (fun _ hg ↦ GLPadicInt.transpose_mem hg)
    (fun _ _ ↦ trivial)

/-- The integral `p`-adic anti-involution acts as matrix transposition. -/
@[simp]
theorem padicIntegralTransposeAntiInvolution_bar {x : GL (Fin n) ℚ_[p]}
    (hx : x ∈ padicIntEntries (Fin n) p) :
    (padicIntegralTransposeAntiInvolution n p).bar x hx =
      (Matrix.GeneralLinearGroup.transposeMulEquiv (Fin n) x).unop :=
  _root_.HeckeAntiInvolution.ofAmbient_bar _ _ _ _ x hx

/-- The rational `p`-adic anti-involution acts as matrix transposition. -/
@[simp]
theorem padicRationalTransposeAntiInvolution_bar {x : GL (Fin n) ℚ_[p]}
    (hx : x ∈ (⊤ : Submonoid (GL (Fin n) ℚ_[p]))) :
    (padicRationalTransposeAntiInvolution n p).bar x hx =
      (Matrix.GeneralLinearGroup.transposeMulEquiv (Fin n) x).unop :=
  _root_.HeckeAntiInvolution.ofAmbient_bar _ _ _ _ x hx

/-- Transposition fixes every integral `p`-adic Hecke double coset. -/
@[simp]
theorem padicIntegralTransposeAntiInvolution_onHeckeCoset_eq_self
    (D : HeckeCoset (padicIntEntries (Fin n) p) (GLPadicInt (Fin n) p) (GLPadicInt (Fin n) p)) :
    (padicIntegralTransposeAntiInvolution n p).onHeckeCoset D = D := by
  obtain ⟨⟨e, -⟩, rfl⟩ := (padicNatPowDiagCosetEquiv n p).surjective D
  rw [padicNatPowDiagCosetEquiv_apply, padicNatPowDiagCoset_def,
    (padicIntegralTransposeAntiInvolution n p).onHeckeCoset_mk]
  exact congrArg (HeckeCoset.mk (GLPadicInt (Fin n) p) (GLPadicInt (Fin n) p))
    (Subtype.ext ((padicIntegralTransposeAntiInvolution_bar n p _).trans
      (Units.ext (by simp [padicNatPowDiagGL_coe]))))

/-- Transposition fixes every rational `p`-adic Hecke double coset. -/
@[simp]
theorem padicRationalTransposeAntiInvolution_onHeckeCoset_eq_self
    (D : HeckeCoset (⊤ : Submonoid (GL (Fin n) ℚ_[p]))
      (GLPadicInt (Fin n) p) (GLPadicInt (Fin n) p)) :
    (padicRationalTransposeAntiInvolution n p).onHeckeCoset D = D := by
  obtain ⟨⟨e, -⟩, rfl⟩ := (padicIntPowDiagCosetEquiv n p).surjective D
  rw [padicIntPowDiagCosetEquiv_apply, padicIntPowDiagCoset_def,
    (padicRationalTransposeAntiInvolution n p).onHeckeCoset_mk]
  exact congrArg (HeckeCoset.mk (GLPadicInt (Fin n) p) (GLPadicInt (Fin n) p))
    (Subtype.ext ((padicRationalTransposeAntiInvolution_bar n p _).trans
      (Units.ext (by simp [padicIntPowDiagGL_coe]))))

/-- Multiplication in `𝕋 (padicIntEntries (Fin n) p) (GLPadicInt (Fin n) p) R` is commutative over
any commutative semiring `R`. -/
theorem mul_comm_padicIntegralHeckeRing (R : Type*) [CommSemiring R]
    (f g : 𝕋 (padicIntEntries (Fin n) p) (GLPadicInt (Fin n) p) R) : f * g = g * f :=
  HeckeCosetModule.mul_comm_of_antiInvolution R (padicIntegralTransposeAntiInvolution n p)
    (padicIntegralTransposeAntiInvolution_onHeckeCoset_eq_self n p) f g

/-- Commutativity of `𝕋 (padicIntEntries (Fin n) p) (GLPadicInt (Fin n) p) R` over any commutative
semiring `R`. -/
@[instance_reducible]
noncomputable def commSemiringPadicIntegralHeckeRing (R : Type*) [CommSemiring R] :
    CommSemiring (𝕋 (padicIntEntries (Fin n) p) (GLPadicInt (Fin n) p) R) :=
  HeckeCosetModule.commSemiringOfAntiInvolution R (padicIntegralTransposeAntiInvolution n p)
    (padicIntegralTransposeAntiInvolution_onHeckeCoset_eq_self n p)

/-- Commutativity of `𝕋 (padicIntEntries (Fin n) p) (GLPadicInt (Fin n) p) R` over any commutative
ring `R`, extending the ambient `Ring` instance without a `Mul` diamond. -/
-- `@[expose]` keeps `toRing` definitionally equal to the ambient `Ring` instance when this is
-- activated as a local instance downstream.
@[expose, instance_reducible]
noncomputable def commRingPadicIntegralHeckeRing (R : Type*) [CommRing R] :
    CommRing (𝕋 (padicIntEntries (Fin n) p) (GLPadicInt (Fin n) p) R) :=
  { (inferInstance : Ring (𝕋 (padicIntEntries (Fin n) p) (GLPadicInt (Fin n) p) R)) with
    mul_comm := mul_comm_padicIntegralHeckeRing n p R }

/-- Multiplication in `𝕋 ⊤ (GLPadicInt (Fin n) p) R` is commutative over any commutative semiring
`R`. -/
theorem mul_comm_padicRationalHeckeRing (R : Type*) [CommSemiring R]
    (f g : 𝕋 (⊤ : Submonoid (GL (Fin n) ℚ_[p])) (GLPadicInt (Fin n) p) R) : f * g = g * f :=
  HeckeCosetModule.mul_comm_of_antiInvolution R (padicRationalTransposeAntiInvolution n p)
    (padicRationalTransposeAntiInvolution_onHeckeCoset_eq_self n p) f g

/-- Commutativity of `𝕋 ⊤ (GLPadicInt (Fin n) p) R` over any commutative semiring `R`. -/
@[instance_reducible]
noncomputable def commSemiringPadicRationalHeckeRing (R : Type*) [CommSemiring R] :
    CommSemiring (𝕋 (⊤ : Submonoid (GL (Fin n) ℚ_[p])) (GLPadicInt (Fin n) p) R) :=
  HeckeCosetModule.commSemiringOfAntiInvolution R (padicRationalTransposeAntiInvolution n p)
    (padicRationalTransposeAntiInvolution_onHeckeCoset_eq_self n p)

/-- Commutativity of `𝕋 ⊤ (GLPadicInt (Fin n) p) R` over any commutative ring `R`, extending the
ambient `Ring` instance without a `Mul` diamond. -/
-- `@[expose]` keeps `toRing` definitionally equal to the ambient `Ring` instance when this is
-- activated as a local instance downstream.
@[expose, instance_reducible]
noncomputable def commRingPadicRationalHeckeRing (R : Type*) [CommRing R] :
    CommRing (𝕋 (⊤ : Submonoid (GL (Fin n) ℚ_[p])) (GLPadicInt (Fin n) p) R) :=
  { (inferInstance : Ring (𝕋 (⊤ : Submonoid (GL (Fin n) ℚ_[p])) (GLPadicInt (Fin n) p) R)) with
    mul_comm := mul_comm_padicRationalHeckeRing n p R }

end HeckeRing.GLn

end
