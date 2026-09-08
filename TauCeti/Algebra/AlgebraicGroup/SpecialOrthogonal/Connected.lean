/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Connected.CommHopfAlgCat
public import TauCeti.Algebra.AlgebraicGroup.SpecialOrthogonal.BaseChange
import TauCeti.Algebra.AlgebraicGroup.SpecialOrthogonal.Naturality
import TauCeti.Algebra.AlgebraicGroup.BaseChange.Naturality
import TauCeti.Algebra.AlgebraicGroup.Connected.AlgebraicallyClosed
import TauCeti.Algebra.AlgebraicGroup.MultiplicativeGroup.Basic
import TauCeti.LinearAlgebra.Matrix.SpecialOrthogonalGroup.FinTwo

/-!
# Geometric connectedness of the two-dimensional special orthogonal group

Away from characteristic two, the coordinate Hopf algebra of the standard group `SO₂` is
geometrically connected.  After extending to an algebraically closed field, choose a square root
`i` of `-1`.  The explicit equivalence `SO₂(K) ≃* Kˣ` writes every rational point on a Laurent
polynomial path from the identity.  An idempotent regular function is constant on each such path,
so all right translations fix it; the standard Hopf-algebra criterion then proves connectedness.

The argument uses Laurent rather than ordinary polynomial paths because the parameter is a unit.
It treats the standard symmetric form used by `TauCeti.SpecialOrthogonal`, whose characteristic-two
behaviour is intentionally outside this statement.

## Main declaration

* `TauCeti.SpecialOrthogonal.geometricallyConnectedCommHopfAlgProperty_coordinateHopfAlgebra_two`:
  `SO₂` is geometrically connected when two is invertible.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§2.3 and 18.c.
-/

public section

open CategoryTheory WithConv
open scoped LaurentPolynomial TensorProduct

namespace TauCeti.SpecialOrthogonal

universe u

noncomputable section

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

local instance : IsScalarTower k K (LaurentPolynomial K) :=
  IsScalarTower.of_algebraMap_eq (by simp)

/-- Base-changed `SO₂` points identified with special orthogonal matrices. -/
private def baseChangePointsMulEquiv
    (A : Type u) [CommRing A] [Algebra k A] [Algebra K A] [IsScalarTower k K A] :
    WithConv (K ⊗[k] coordinateHopfAlgebra k 2 →ₐ[K] A) ≃*
      Matrix.specialOrthogonalGroup (Fin 2) A :=
  (AlgHom.baseChangePointsMulEquiv (k := k) (K := K)
    (A := coordinateHopfAlgebra k 2) (R := A)).symm.trans
      (pointsMulEquiv k 2 (A := A))

private theorem baseChangePointsMulEquiv_mapValue
    {A B : Type u} [CommRing A] [CommRing B]
    [Algebra k A] [Algebra K A] [IsScalarTower k K A]
    [Algebra k B] [Algebra K B] [IsScalarTower k K B]
    (phi : A →ₐ[K] B) (f : WithConv (K ⊗[k] coordinateHopfAlgebra k 2 →ₐ[K] A)) :
    baseChangePointsMulEquiv (k := k) (K := K) B
        (AlgHom.mapValue (H := K ⊗[k] coordinateHopfAlgebra k 2) phi f) =
      Matrix.SpecialOrthogonalGroup.map phi.toRingHom
        (baseChangePointsMulEquiv (k := k) (K := K) A f) := by
  rw [baseChangePointsMulEquiv, MulEquiv.trans_apply,
    AlgHom.baseChangePointsMulEquiv_symm_mapValue,
    baseChangePointsMulEquiv, MulEquiv.trans_apply]
  exact pointsMulEquiv_mapValue (R := k) (n := 2) (phi.restrictScalars k) _

/-- The Laurent-polynomial path in `SO₂` attached to the generic unit. -/
private def laurentPath (i half : K) (hi : i ^ 2 = -1) (hhalf : 2 * half = 1) :
    WithConv (K ⊗[k] coordinateHopfAlgebra k 2 →ₐ[K] LaurentPolynomial K) :=
  (baseChangePointsMulEquiv (k := k) (K := K) (LaurentPolynomial K)).symm
    (Matrix.SpecialOrthogonalGroup.finTwoOfUnit
      (LaurentPolynomial.C i) (LaurentPolynomial.C half)
      (by simpa only [map_pow, map_neg, map_one] using
        congrArg LaurentPolynomial.C hi)
      (by simpa only [map_ofNat, map_mul, map_one] using
        congrArg LaurentPolynomial.C hhalf)
      (MultiplicativeGroup.genericUnit K))

private theorem mapValue_laurentPath
    (i half : K) (hi : i ^ 2 = -1) (hhalf : 2 * half = 1) (u : Kˣ) :
    AlgHom.mapValue (H := K ⊗[k] coordinateHopfAlgebra k 2)
        (MultiplicativeGroup.point u) (laurentPath (k := k) i half hi hhalf) =
      (baseChangePointsMulEquiv (k := k) (K := K) K).symm
        (Matrix.SpecialOrthogonalGroup.finTwoOfUnit i half hi hhalf u) := by
  apply (baseChangePointsMulEquiv (k := k) (K := K) K).injective
  rw [baseChangePointsMulEquiv_mapValue]
  simp only [laurentPath, MulEquiv.apply_symm_apply]
  rw [Matrix.SpecialOrthogonalGroup.map_finTwoOfUnit]
  have hu : Units.map (MultiplicativeGroup.point u).toRingHom.toMonoidHom
      (MultiplicativeGroup.genericUnit K) = u := by
    apply Units.ext
    simp
  apply Subtype.ext
  rw [Matrix.SpecialOrthogonalGroup.coe_finTwoOfUnit,
    Matrix.SpecialOrthogonalGroup.coe_finTwoOfUnit]
  ext j k
  fin_cases j
  · fin_cases k <;> norm_num [Matrix.of_apply, hu, MultiplicativeGroup.point_C]
  · fin_cases k <;> norm_num [Matrix.of_apply, hu, MultiplicativeGroup.point_C]

private theorem rightTranslationAlgHom_eq_self
    [Invertible (2 : k)] [IsAlgClosed K]
    (e : K ⊗[k] coordinateHopfAlgebra k 2) (he : IsIdempotentElem e)
    (g : WithConv (K ⊗[k] coordinateHopfAlgebra k 2 →ₐ[K] K)) :
    HopfAlgebra.rightTranslationAlgHom g e = e := by
  obtain ⟨i, hi⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : K) (n := 2) (by norm_num)
  have h2k : (2 : k) ≠ 0 := Invertible.ne_zero _
  have h2 : (2 : K) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap k K)).2 h2k
  let half : K := (2 : K)⁻¹
  have hhalf : 2 * half = 1 := by
    exact mul_inv_cancel₀ h2
  let E := baseChangePointsMulEquiv (k := k) (K := K) K
  let u : Kˣ := Matrix.SpecialOrthogonalGroup.finTwoToUnit i hi (E g)
  let eval (v : Kˣ) : LaurentPolynomial K →ₐ[K] K := MultiplicativeGroup.point v
  apply HopfAlgebra.rightTranslationAlgHom_eq_self_of_path e he g
    (laurentPath (k := k) i half hi hhalf) (eval u) (eval 1)
  · rw [mapValue_laurentPath]
    simpa only [u, E, MulEquiv.symm_apply_apply] using
      congrArg E.symm
        (Matrix.SpecialOrthogonalGroup.finTwoOfUnit_finTwoToUnit i half hi hhalf (E g))
  · rw [mapValue_laurentPath]
    simp

/-- The coordinate Hopf algebra of the standard `SO₂` is geometrically connected over every
field in which two is invertible. -/
theorem geometricallyConnectedCommHopfAlgProperty_coordinateHopfAlgebra_two
    (k : Type u) [Field k] [Invertible (2 : k)] :
    geometricallyConnectedCommHopfAlgProperty k (coordinateHopfAlgebra k 2) := by
  rw [geometricallyConnectedCommHopfAlgProperty_iff_connectedSpace_of_isAlgClosed]
  intro K _ _ _
  let H := coordinateHopfAlgebra k 2
  let _ : Nontrivial H := Bialgebra.nontrivial (A := H) k
  let _ : Nontrivial (K ⊗[k] H) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_left k K H
      (RingHom.injective (algebraMap k H))
  have hconnected : ConnectedSpace (PrimeSpectrum (K ⊗[k] H)) :=
    HopfAlgebra.connectedSpace_primeSpectrum_of_forall_rightTranslationAlgHom_eq_self
      (fun e he g ↦ rightTranslationAlgHom_eq_self (k := k) (K := K) e he g)
  let equiv : (H : Type u) ⊗[k] K ≃+* K ⊗[k] H :=
    (Algebra.TensorProduct.comm k H K).toRingEquiv
  exact (PrimeSpectrum.homeomorphOfRingEquiv equiv).connectedSpace_iff.mpr hconnected

end

end TauCeti.SpecialOrthogonal
