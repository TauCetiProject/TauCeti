/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.Finite
public import TauCeti.GroupTheory.Coxeter.Hecke.Basic
public import TauCeti.GroupTheory.Coxeter.Matrix

/-!
# The type-A Hecke algebra is the Hecke algebra of the type-A Coxeter matrix

The type-A Hecke algebra `TypeAHeckeAlgebra R q n` is presented by the quadratic relation with
parameter `q - q⁻¹`, the braid relation for adjacent generators and commutation of distant
generators. These are exactly the relations of the Iwahori–Hecke algebra
`(CoxeterMatrix.A (n - 1)).HeckeAlgebra (q - q⁻¹)` of the type-A Coxeter matrix, whose braid
relations have length `3` for adjacent and `2` for distant indices. The generator-preserving map
`TauCeti.TypeAHeckeAlgebra.algEquivHeckeAlgebra` is therefore an isomorphism. Through it the
reduced-word elements `T_w`, the regular representation and the basis theorem of the type-A Hecke
algebra are obtained from those of the general Hecke algebra, in
`TauCeti.Algebra.TypeAHeckeAlgebra.ReducedWord` and `TauCeti.Algebra.TypeAHeckeAlgebra.Basis`.

## Main definitions

* `TauCeti.TypeAHeckeAlgebra.algEquivHeckeAlgebra`: the isomorphism `T i ↦ T i` from the type-A
  Hecke algebra on `n` strands to the Hecke algebra of the Coxeter matrix of type `A_(n-1)`.

## Main results

* `TauCeti.TypeAHeckeAlgebra.prod_map_T_braidWord`: the generators of the type-A Hecke algebra
  satisfy the braid relations of the type-A Coxeter matrix.
* `TauCeti.TypeAHeckeAlgebra.algEquivHeckeAlgebra_T` and
  `TauCeti.TypeAHeckeAlgebra.algEquivHeckeAlgebra_symm_T`: the isomorphism preserves generators.
-/

public section

namespace TauCeti

namespace TypeAHeckeAlgebra

open CoxeterSystem

/-- The Hecke generators satisfy every braid relation of the type-A Coxeter matrix: for all
`i` and `j`, the two alternating words in `T i` and `T j` whose length is the Coxeter-matrix
entry at `(i, j)` have the same product. -/
theorem prod_map_T_braidWord {R : Type*} [CommRing R] {q : Rˣ} {n : ℕ} (i j : Fin (n - 1)) :
    ((braidWord (CoxeterMatrix.A (n - 1)) i j).map (T (R := R) q)).prod =
      ((braidWord (CoxeterMatrix.A (n - 1)) j i).map (T q)).prod := by
  have hgen (k : Fin (n - 1)) :
      ((Units.coeHom _).comp (braidHom R q n)) (ArtinGroup.gen (CoxeterMatrix.A (n - 1)) k) =
        T q k := by
    simp [← BraidGroup.sigma_eq_gen]
  have h := congrArg ((Units.coeHom _).comp (braidHom R q n))
    (ArtinGroup.prod_map_gen_braidWord (CoxeterMatrix.A (n - 1)) i j)
  simpa only [map_list_prod, List.map_map, Function.comp_def, hgen] using h

variable (R : Type*) [CommRing R] (q : Rˣ) (n : ℕ)

/-- The **type-A Hecke algebra on `n` strands is the Hecke algebra of the type-A Coxeter matrix**
`A_(n-1)` with quadratic parameter `q - q⁻¹`, by the isomorphism sending each generator `T i` to
the generator `T i`. -/
noncomputable def algEquivHeckeAlgebra :
    TypeAHeckeAlgebra R q n ≃ₐ[R] (CoxeterMatrix.A (n - 1)).HeckeAlgebra ((q : R) - ↑q⁻¹) :=
  AlgEquiv.ofAlgHom
    (lift (CoxeterMatrix.HeckeAlgebra.T _ _)
      (CoxeterMatrix.HeckeAlgebra.T_mul_self _ _)
      (fun h ↦ mul_mul_eq_of_prod_map_braidWord
        (CoxeterMatrix.HeckeAlgebra.prod_map_T_braidWord _ _ _ _)
        (coxeterMatrixA_eq_three (.inl h)))
      (fun h ↦ (commute_of_prod_map_braidWord
        (CoxeterMatrix.HeckeAlgebra.prod_map_T_braidWord _ _ _ _)
        (coxeterMatrixA_eq_two (.inl h))).eq))
    (CoxeterMatrix.HeckeAlgebra.lift (T q) T_mul_self prod_map_T_braidWord)
    (CoxeterMatrix.HeckeAlgebra.hom_ext fun i ↦ by simp)
    (hom_ext fun i ↦ by simp)

variable {R q n}

/-- The isomorphism `TauCeti.TypeAHeckeAlgebra.algEquivHeckeAlgebra` preserves the generators. -/
@[simp]
theorem algEquivHeckeAlgebra_T (i : Fin (n - 1)) :
    algEquivHeckeAlgebra R q n (T q i) = CoxeterMatrix.HeckeAlgebra.T _ _ i :=
  lift_T _ _ _ _ i

/-- The inverse of `TauCeti.TypeAHeckeAlgebra.algEquivHeckeAlgebra` preserves the generators. -/
@[simp]
theorem algEquivHeckeAlgebra_symm_T (i : Fin (n - 1)) :
    (algEquivHeckeAlgebra R q n).symm (CoxeterMatrix.HeckeAlgebra.T _ _ i) = T q i :=
  CoxeterMatrix.HeckeAlgebra.lift_T _ _ _ i

end TypeAHeckeAlgebra

end TauCeti
