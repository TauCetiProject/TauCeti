/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.ReducedWord
public import TauCeti.GroupTheory.Coxeter.Hecke.Basic
public import TauCeti.GroupTheory.Coxeter.Matrix

/-!
# The type-A Hecke algebra is the Hecke algebra of the type-A Coxeter matrix

The type-A Hecke algebra `TypeAHeckeAlgebra R q n` is presented by the quadratic relation with
parameter `q - q⁻¹`, the braid relation for adjacent generators and commutation of distant
generators. These are exactly the relations of the Iwahori–Hecke algebra
`(CoxeterMatrix.A (n - 1)).HeckeAlgebra (q - q⁻¹)` of the type-A Coxeter matrix, whose braid
relations have length `3` for adjacent and `2` for distant indices. The generator-preserving map
`TauCeti.TypeAHeckeAlgebra.algEquivHeckeAlgebra` is therefore an isomorphism, and it matches the
reduced-word elements `T_w` of the two algebras
(`TauCeti.TypeAHeckeAlgebra.algEquivHeckeAlgebra_Tw`).

## Main definitions

* `TauCeti.TypeAHeckeAlgebra.algEquivHeckeAlgebra`: the isomorphism `T i ↦ T i` from the type-A
  Hecke algebra on `n` strands to the Hecke algebra of the Coxeter matrix of type `A_(n-1)`.

## Main results

* `TauCeti.TypeAHeckeAlgebra.algEquivHeckeAlgebra_T` and
  `TauCeti.TypeAHeckeAlgebra.algEquivHeckeAlgebra_symm_T`: the isomorphism preserves generators.
* `TauCeti.TypeAHeckeAlgebra.algEquivHeckeAlgebra_Tw`: it preserves the elements `T_w`.
-/

public section

namespace TauCeti

namespace TypeAHeckeAlgebra

open CoxeterSystem

variable (R : Type*) [CommRing R] (q : Rˣ) (n : ℕ)

/-- The **type-A Hecke algebra on `n` strands is the Hecke algebra of the type-A Coxeter matrix**
`A_(n-1)` with quadratic parameter `q - q⁻¹`, by the isomorphism sending each generator `T i` to
the generator `T i`. -/
noncomputable def algEquivHeckeAlgebra :
    TypeAHeckeAlgebra R q n ≃ₐ[R] (CoxeterMatrix.A (n - 1)).HeckeAlgebra ((q : R) - ↑q⁻¹) :=
  AlgEquiv.ofAlgHom
    (lift (CoxeterMatrix.HeckeAlgebra.T _ _)
      (CoxeterMatrix.HeckeAlgebra.T_mul_self _ _)
      (fun {i j} h ↦ by
        have hb := CoxeterMatrix.HeckeAlgebra.prod_map_T_braidWord
          (CoxeterMatrix.A (n - 1)) ((q : R) - ↑q⁻¹) i j
        rw [braidWord, coxeterMatrixA_eq_three (.inl h), braidWord,
          coxeterMatrixA_eq_three (.inr h), prod_map_alternatingWord_three,
          prod_map_alternatingWord_three] at hb
        exact hb.symm)
      (fun {i j} h ↦ by
        have hb := CoxeterMatrix.HeckeAlgebra.prod_map_T_braidWord
          (CoxeterMatrix.A (n - 1)) ((q : R) - ↑q⁻¹) i j
        rw [braidWord, coxeterMatrixA_eq_two (.inl h), braidWord,
          coxeterMatrixA_eq_two (.inr h), prod_map_alternatingWord_two,
          prod_map_alternatingWord_two] at hb
        exact hb))
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

/-- The isomorphism `TauCeti.TypeAHeckeAlgebra.algEquivHeckeAlgebra` takes the element `T_w` of the
type-A Hecke algebra to the element `T_w` of the Hecke algebra of the Coxeter matrix. -/
@[simp]
theorem algEquivHeckeAlgebra_Tw {W : Type*} [Group W]
    (cs : CoxeterSystem (CoxeterMatrix.A (n - 1)) W) (w : W) :
    algEquivHeckeAlgebra R q n (Tw q cs w) = CoxeterMatrix.HeckeAlgebra.Tw _ cs w := by
  obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced w
  rw [Tw_wordProd cs hω, CoxeterMatrix.HeckeAlgebra.Tw_wordProd hω, map_list_prod, List.map_map]
  congr 1
  exact List.map_congr_left fun i _ ↦ algEquivHeckeAlgebra_T i

end TypeAHeckeAlgebra

end TauCeti
