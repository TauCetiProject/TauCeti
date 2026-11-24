/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Basic

/-!
# The polynomial presentation of the special linear coordinate algebra

The coordinate algebra of `SLₙ` is canonically `R[Xᵢⱼ] / (det X - 1)`. This identifies the
existing determinant-kernel quotient of `O(GLₙ)` with a polynomial quotient, removing the
determinant localization. The equivalence sends each generic matrix entry to the corresponding
polynomial class; its inverse evaluates polynomials at the generic matrix of `SLₙ`.

The construction works over every commutative ring, including the zero ring, and in every
rank, including zero. It uses the algebra-valued points equivalence: the generic matrix in
the polynomial quotient has determinant one, so it gives a point of the existing `SLₙ`
coordinate Hopf algebra. The two inverse identities follow on the matrix entries, which
generate that algebra.

## Main declarations

* `TauCeti.SpecialLinear.polynomialPresentation`: the polynomial presentation of `O(SLₙ)`.
* `TauCeti.SpecialLinear.polynomialPresentation_genericMatrix`: its value on a matrix entry.
* `TauCeti.SpecialLinear.polynomialPresentation_symm_mk`: its inverse on a polynomial class.

## References

* J. S. Milne, *Algebraic Groups* (2017), §2.a, the matrix-group coordinate descriptions.

The construction uses `TauCeti.SpecialLinear.pointsMulEquiv` and the generic-entry generation
theorem `TauCeti.SpecialLinear.adjoin_range_map_genericMatrix`.
-/

public section

namespace TauCeti.SpecialLinear

universe u

variable (R : Type u) [CommRing R] (n : ℕ)

private noncomputable def polynomialQuotientMatrix :
    Matrix.SpecialLinearGroup (Fin n)
      (MvPolynomial (Fin n × Fin n) R ⧸
        Ideal.span {Matrix.det (Matrix.mvPolynomialX (Fin n) (Fin n) R) - 1}) :=
  ⟨(Matrix.mvPolynomialX (Fin n) (Fin n) R).map (Ideal.Quotient.mk _), by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det,
      Ideal.Quotient.mk_eq_one_iff_sub_mem]
    exact Ideal.mem_span_singleton_self _⟩

private noncomputable def toPolynomialQuotient :
    coordinateHopfAlgebra R n →ₐ[R]
      MvPolynomial (Fin n × Fin n) R ⧸
        Ideal.span {Matrix.det (Matrix.mvPolynomialX (Fin n) (Fin n) R) - 1} :=
  ((pointsMulEquiv (R := R)
    (A := MvPolynomial (Fin n × Fin n) R ⧸
      Ideal.span {Matrix.det (Matrix.mvPolynomialX (Fin n) (Fin n) R) - 1}) n).symm
        (polynomialQuotientMatrix R n)).ofConv

private theorem toPolynomialQuotient_genericMatrix (i j : Fin n) :
    toPolynomialQuotient R n
        ((GeneralLinear.genericMatrix R n).map (coordinateMap R n).hom i j) =
      Ideal.Quotient.mk _ (MvPolynomial.X (i, j)) :=
  ofConv_pointsMulEquiv_symm_genericMatrix R n (polynomialQuotientMatrix R n) i j

private noncomputable def fromPolynomialQuotient :
    (MvPolynomial (Fin n × Fin n) R ⧸
        Ideal.span {Matrix.det (Matrix.mvPolynomialX (Fin n) (Fin n) R) - 1}) →ₐ[R]
      coordinateHopfAlgebra R n :=
  let f := MvPolynomial.aeval fun ij : Fin n × Fin n ↦
    (GeneralLinear.genericMatrix R n).map (coordinateMap R n).hom ij.1 ij.2
  Ideal.Quotient.liftₐ _ f
    (by
      intro p hp
      have h : Ideal.span {Matrix.det (Matrix.mvPolynomialX (Fin n) (Fin n) R) - 1} ≤
          RingHom.ker f.toRingHom := by
        rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker]
        simp only [f, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, map_sub, map_one,
          AlgHom.map_det, Matrix.mvPolynomialX_mapMatrix_aeval]
        exact sub_eq_zero.mpr (det_map_genericMatrix_coordinateMap R n)
      exact h hp)

private theorem fromPolynomialQuotient_mk (p : MvPolynomial (Fin n × Fin n) R) :
    fromPolynomialQuotient R n (Ideal.Quotient.mk _ p) =
      MvPolynomial.aeval (fun ij : Fin n × Fin n ↦
        (GeneralLinear.genericMatrix R n).map (coordinateMap R n).hom ij.1 ij.2) p :=
  (rfl)

private theorem fromPolynomialQuotient_comp_toPolynomialQuotient :
    (fromPolynomialQuotient R n).comp (toPolynomialQuotient R n) =
      AlgHom.id R (coordinateHopfAlgebra R n) := by
  apply AlgHom.ext_of_adjoin_eq_top (adjoin_range_map_genericMatrix R n)
  rintro x ⟨⟨i, j⟩, rfl⟩
  rw [AlgHom.comp_apply, toPolynomialQuotient_genericMatrix, fromPolynomialQuotient_mk,
    MvPolynomial.aeval_X, AlgHom.id_apply]

private theorem toPolynomialQuotient_comp_fromPolynomialQuotient :
    (toPolynomialQuotient R n).comp (fromPolynomialQuotient R n) = AlgHom.id R _ := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro ij
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, AlgHom.id_apply]
  rw [fromPolynomialQuotient_mk, MvPolynomial.aeval_X, toPolynomialQuotient_genericMatrix]

/-- The coordinate algebra of `SLₙ` is the polynomial algebra on its matrix entries modulo
the single relation `det X = 1`, over any commutative ring and in every rank. -/
noncomputable def polynomialPresentation :
    coordinateHopfAlgebra R n ≃ₐ[R]
      MvPolynomial (Fin n × Fin n) R ⧸
        Ideal.span {Matrix.det (Matrix.mvPolynomialX (Fin n) (Fin n) R) - 1} :=
  AlgEquiv.ofAlgHom (toPolynomialQuotient R n) (fromPolynomialQuotient R n)
    (toPolynomialQuotient_comp_fromPolynomialQuotient R n)
    (fromPolynomialQuotient_comp_toPolynomialQuotient R n)

/-- The polynomial presentation sends a generic matrix entry to the corresponding variable
class. -/
-- Run before the generic entry expands into its localized coordinate formula.
@[simp↓]
theorem polynomialPresentation_genericMatrix (i j : Fin n) :
    polynomialPresentation R n
        ((GeneralLinear.genericMatrix R n).map (coordinateMap R n).hom i j) =
      Ideal.Quotient.mk _ (MvPolynomial.X (i, j)) :=
  toPolynomialQuotient_genericMatrix R n i j

/-- The inverse polynomial presentation evaluates a representative at the generic matrix
of `SLₙ`. -/
@[simp]
theorem polynomialPresentation_symm_mk (p : MvPolynomial (Fin n × Fin n) R) :
    (polynomialPresentation R n).symm (Ideal.Quotient.mk _ p) =
      MvPolynomial.aeval (fun ij : Fin n × Fin n ↦
        (GeneralLinear.genericMatrix R n).map (coordinateMap R n).hom ij.1 ij.2) p :=
  fromPolynomialQuotient_mk R n p

end TauCeti.SpecialLinear
