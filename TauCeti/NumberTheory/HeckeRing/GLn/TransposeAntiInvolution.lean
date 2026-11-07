/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.NumberTheory.HeckeRing.Commutativity
public import TauCeti.NumberTheory.HeckeRing.GLn.DiagonalCosets
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Transpose

/-!
# Commutativity of the `GL_n` Hecke ring

Transposition `ξ ↦ ᵗξ` is an anti-automorphism of `GL_n(ℚ)` preserving both `SL_n(ℤ)` and
the submonoid `Δ` of integral matrices of positive determinant, so it restricts to a
`HeckeAntiInvolution` of the arithmetic Hecke datum. Every double coset has a diagonal
representative and transposition fixes a diagonal matrix, so the involution it induces on
`SL_n(ℤ) \ Δ / SL_n(ℤ)` is the identity. Shimura's Proposition 3.8 then applies: the
integral Hecke ring of `GL_n` is commutative.

## Main definitions

* `HeckeRing.GLn.transposeAntiInvolution`: the induced `HeckeAntiInvolution` of `(Δ, SL_n(ℤ))`.

## Main results

* `HeckeRing.GLn.transposeAntiInvolution_onHeckeCoset_eq_self`: transposition fixes every
  double coset.
* `HeckeRing.GLn.commSemiringHeckeRing`: **Shimura's Proposition 3.8 for `GL_n`** — the
  Hecke ring is commutative over any commutative semiring of coefficients, with
  `HeckeRing.GLn.commSemiringIntegralHeckeRing` the integral case.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  Proposition 3.8.

Ported from the AINTLIB `LeanModularForms` project
([`LeanModularForms/HeckeRIngs/GLn/TransposeAntiInvolution.lean`](https://github.com/CBirkbeck/AINTLIB),
Chris Birkbeck).
-/

public section

open Matrix Matrix.SpecialLinearGroup HeckeRing HeckeCosetModule

namespace HeckeRing.GLn

variable (n : ℕ)

/-- Transposition preserves `SL_n(ℤ)`: the transpose of an integral matrix of determinant
one again has determinant one. -/
lemma transposeMulEquiv_mem_SLnZ {g : GL (Fin n) ℚ} (hg : g ∈ SLnZ n) :
    (Matrix.GeneralLinearGroup.transposeMulEquiv (Fin n) g).unop ∈ SLnZ n := by
  obtain ⟨σ, rfl⟩ := (mem_SLnZ_iff n).mp hg
  refine (mem_SLnZ_iff n).mpr ⟨σ.transpose, Units.ext ?_⟩
  ext i j
  simp [mapGL_coe_matrix, algebraMap_int_eq, SpecialLinearGroup.coe_transpose]

/-- Transposition preserves `Δ`: it transposes the integral witness and leaves the
determinant unchanged. -/
lemma transposeMulEquiv_mem_posDetInt {g : GL (Fin n) ℚ} (hg : g ∈ posDetInt n) :
    (Matrix.GeneralLinearGroup.transposeMulEquiv (Fin n) g).unop ∈ posDetInt n := by
  obtain ⟨hint, hdet⟩ := (mem_posDetInt_iff n).mp hg
  obtain ⟨A, hA⟩ := (hasIntEntries_iff n).mp hint
  refine (mem_posDetInt_iff n).mpr ⟨(hasIntEntries_iff n).mpr ⟨Aᵀ, ?_⟩, ?_⟩
  · rw [Matrix.GeneralLinearGroup.coe_unop_transposeMulEquiv, hA, Matrix.transpose_map]
  · rwa [Matrix.GeneralLinearGroup.coe_unop_transposeMulEquiv, Matrix.det_transpose]

/-- Transposition fixes every diagonal matrix, including the junk value `1` taken when
some entry vanishes. -/
@[simp] lemma transposeMulEquiv_natDiagGL (a : Fin n → ℕ) :
    (Matrix.GeneralLinearGroup.transposeMulEquiv (Fin n) (natDiagGL n a)).unop =
      natDiagGL n a := by
  by_cases ha : ∀ i, 0 < a i
  · exact Units.ext (by simp [natDiagGL_coe n a ha])
  · rw [natDiagGL_of_not_pos n ha]
    exact Units.ext (by simp)

/-- Transposition as an anti-involution of the arithmetic Hecke datum `(Δ, SL_n(ℤ))`. -/
noncomputable def transposeAntiInvolution :
    HeckeAntiInvolution (posDetInt n) (SLnZ n) :=
  HeckeAntiInvolution.ofAmbient
    (Matrix.GeneralLinearGroup.transposeMulEquiv (R := ℚ) (Fin n)).toMonoidHom
    Matrix.GeneralLinearGroup.transposeMulEquiv_transposeMulEquiv
    (fun _ hg ↦ transposeMulEquiv_mem_SLnZ n hg)
    (fun _ hg ↦ transposeMulEquiv_mem_posDetInt n hg)

/-- The anti-involution acts as transposition, unfolding the sealed definition. -/
@[simp] lemma transposeAntiInvolution_bar {x : GL (Fin n) ℚ} (hx : x ∈ posDetInt n) :
    (transposeAntiInvolution n).bar x hx =
      (Matrix.GeneralLinearGroup.transposeMulEquiv (Fin n) x).unop :=
  HeckeAntiInvolution.ofAmbient_bar _ _ _ _ x hx

/-- Transposition fixes every double coset: each one has a diagonal representative, and
transposition fixes diagonal matrices. -/
@[simp] lemma transposeAntiInvolution_onHeckeCoset_eq_self
    (D : HeckeCoset (posDetInt n) (SLnZ n) (SLnZ n)) :
    (transposeAntiInvolution n).onHeckeCoset D = D := by
  obtain ⟨a, -, -, rfl⟩ := exists_diagonal_representative D
  rw [diagCoset_def, (transposeAntiInvolution n).onHeckeCoset_mk]
  exact congrArg (HeckeCoset.mk (SLnZ n) (SLnZ n))
    (Subtype.ext ((transposeAntiInvolution_bar n _).trans (transposeMulEquiv_natDiagGL n a)))

/-- **Shimura's Proposition 3.8 for `GL_n`**: the Hecke ring of `GL_n` over any commutative
semiring is commutative, transposition being an anti-involution that fixes every double
coset. -/
@[instance_reducible]
noncomputable def commSemiringHeckeRing (R : Type*) [CommSemiring R] :
    CommSemiring (𝕋 (posDetInt n) (SLnZ n) R) :=
  commSemiringOfAntiInvolution R (transposeAntiInvolution n)
    (transposeAntiInvolution_onHeckeCoset_eq_self n)

/-- The integral Hecke ring of `GL_n` is commutative. -/
@[instance_reducible]
noncomputable def commSemiringIntegralHeckeRing : CommSemiring (IntegralHeckeRing n) :=
  commSemiringHeckeRing n ℤ

end HeckeRing.GLn
