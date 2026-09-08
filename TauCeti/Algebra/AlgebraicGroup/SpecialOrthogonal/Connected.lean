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

The coordinate Hopf algebra of the standard group `SO₂` is geometrically connected over every
field. Away from characteristic two, after extending to an algebraically closed field, choose a
square root `i` of `-1`. The explicit equivalence `SO₂(K) ≃* Kˣ` writes every rational point on a
Laurent-polynomial path from the identity. In characteristic two, every rational point lies on an
affine-line path of matrices `!![1 + tb, tb; -tb, 1 + tb]`. An idempotent regular function is
constant on either kind of path, so all right translations fix it; the standard Hopf-algebra
criterion then proves connectedness.

The argument away from characteristic two uses Laurent rather than ordinary polynomial paths
because the parameter is a unit. It treats the standard symmetric form used by
`TauCeti.SpecialOrthogonal`; in characteristic two this determinant-one model is nonreduced but
has connected underlying space.

## Main declaration

* `TauCeti.SpecialOrthogonal.geometricallyConnectedCommHopfAlgProperty_coordinateHopfAlgebra_two`:
  `SO₂` is geometrically connected over every field.

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

/-- The characteristic-two affine-line path with parameter `b`. -/
private noncomputable def charTwoMatrixPath (b : K) (h2 : (2 : K) = 0) :
    Matrix.specialOrthogonalGroup (Fin 2) (Polynomial K) := by
  let _ : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
  let t : Polynomial K := Polynomial.X * Polynomial.C b
  refine ⟨!![1 + t, t; -t, 1 + t], ?_⟩
  rw [Matrix.of_mem_specialOrthogonalGroup_fin_two_iff]
  refine ⟨rfl, (neg_neg t).symm, ?_⟩
  rw [CharTwo.add_sq]
  simpa only [one_pow] using CharTwo.add_cancel_right (1 : Polynomial K) (t ^ 2)

private theorem coe_charTwoMatrixPath (b : K) (h2 : (2 : K) = 0) :
    (charTwoMatrixPath b h2 : Matrix (Fin 2) (Fin 2) (Polynomial K)) =
      let t := Polynomial.X * Polynomial.C b
      !![1 + t, t; -t, 1 + t] :=
  by
    unfold charTwoMatrixPath
    rfl

private theorem rightTranslationAlgHom_eq_self_of_char_two
    [IsAlgClosed K] (h2 : (2 : K) = 0)
    (e : K ⊗[k] coordinateHopfAlgebra k 2) (he : IsIdempotentElem e)
    (g : WithConv (K ⊗[k] coordinateHopfAlgebra k 2 →ₐ[K] K)) :
    HopfAlgebra.rightTranslationAlgHom g e = e := by
  let _ : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
  let E := baseChangePointsMulEquiv (k := k) (K := K) K
  let M := E g
  let b : K := M.val 0 1
  let xX : WithConv (K ⊗[k] coordinateHopfAlgebra k 2 →ₐ[K] Polynomial K) :=
    (baseChangePointsMulEquiv (k := k) (K := K) (Polynomial K)).symm
      (charTwoMatrixPath b h2)
  let eval (c : K) : Polynomial K →ₐ[K] K :=
    Polynomial.aevalTower (AlgHom.id K K) c
  have hM := Matrix.mem_specialOrthogonalGroup_fin_two_iff.mp M.2
  have hM00 : M.val 0 0 = 1 + b := by
    have hab : M.val 0 0 + b = 1 := by
      apply CharTwo.sq_inj.mp
      rw [CharTwo.add_sq, hM.2.2, one_pow]
    calc
      M.val 0 0 = M.val 0 0 + b + b := (CharTwo.add_cancel_right _ _).symm
      _ = 1 + b := congrArg (· + b) hab
  have hM10 : M.val 1 0 = -b := by
    simpa only [b, neg_neg] using (congrArg Neg.neg hM.2.1).symm
  apply HopfAlgebra.rightTranslationAlgHom_eq_self_of_path e he g xX (eval 1) (eval 0)
  · apply E.injective
    rw [baseChangePointsMulEquiv_mapValue]
    simp only [xX, MulEquiv.apply_symm_apply, E]
    apply Subtype.ext
    rw [Matrix.SpecialOrthogonalGroup.coe_map, coe_charTwoMatrixPath]
    -- Expose the local name `M` so its entry relations rewrite the target matrix.
    change _ = (M : Matrix (Fin 2) (Fin 2) K)
    ext i j
    fin_cases i
    · fin_cases j <;>
        norm_num [Matrix.of_apply, eval, b, hM00]
    · fin_cases j
      · norm_num [Matrix.of_apply, eval, b, hM10]
      · norm_num [Matrix.of_apply, eval, b]
        exact hM00.symm.trans hM.1
  · apply E.injective
    rw [baseChangePointsMulEquiv_mapValue]
    simp only [xX, MulEquiv.apply_symm_apply, map_one, E]
    apply Subtype.ext
    rw [Matrix.SpecialOrthogonalGroup.coe_map, coe_charTwoMatrixPath]
    ext i j
    fin_cases i
    · fin_cases j <;> norm_num [Matrix.of_apply, eval]
    · fin_cases j <;> norm_num [Matrix.of_apply, eval]

private theorem rightTranslationAlgHom_eq_self_of_two_ne_zero
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

private theorem rightTranslationAlgHom_eq_self
    [IsAlgClosed K]
    (e : K ⊗[k] coordinateHopfAlgebra k 2) (he : IsIdempotentElem e)
    (g : WithConv (K ⊗[k] coordinateHopfAlgebra k 2 →ₐ[K] K)) :
    HopfAlgebra.rightTranslationAlgHom g e = e := by
  by_cases h2k : (2 : k) = 0
  · have h2K : (2 : K) = 0 := by
      simpa only [map_ofNat, map_zero] using congrArg (algebraMap k K) h2k
    exact rightTranslationAlgHom_eq_self_of_char_two (k := k) h2K e he g
  · let _ : Invertible (2 : k) := invertibleOfNonzero h2k
    exact rightTranslationAlgHom_eq_self_of_two_ne_zero (k := k) (K := K) e he g

/-- The coordinate Hopf algebra of the standard `SO₂` is geometrically connected over every
field. -/
theorem geometricallyConnectedCommHopfAlgProperty_coordinateHopfAlgebra_two
    (k : Type u) [Field k] :
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
