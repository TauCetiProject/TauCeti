/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.Induction
public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.Ring
-- Non-public: `TauCeti.indFDRepProjection`, the projection formula on representations.
import TauCeti.RepresentationTheory.Induction.FiniteDimensional.Projection

/-!
# The projection formula in the Grothendieck ring of a group algebra

Let `k` be a field, `G` a finite group and `S` a subgroup. Induction
`TauCeti.indK0 k S : G₀(k[S]) →+ G₀(k[G])` is not a ring homomorphism, but it is a homomorphism of
`G₀(k[G])`-modules, where `G₀(k[S])` is a `G₀(k[G])`-module through restriction:

`Ind_S^G (y · Res_S^G x) = (Ind_S^G y) · x`  in  `G₀(k[G])`

(`TauCeti.indK0_mul_resK0`). This is the representation-level projection formula
`Ind_S^G (A ⊗ Res_S^G B) ≅ (Ind_S^G A) ⊗ B` (`TauCeti.indFDRepProjection`) read on classes, both
sides being additive in each variable. It holds in every characteristic, with the relations of
`G₀(k[G])` coming from all short exact sequences, split or not.

Applied to `y = 1`, it says that multiplying a class by the permutation class `[k[G ⧸ S]]`, the
induction of the unit (`TauCeti.indK0_one`), is inducing its restriction. This is how an identity
among permutation classes, such as Artin's identity, spreads to every class of `G₀(k[G])`.

## Main results

* `TauCeti.indK0_fdRepK0RingEquiv_of`: induction of the class of a representation, read through
  `TauCeti.fdRepK0RingEquiv`, is the class of the induced representation.
* `TauCeti.indK0_mul_resK0`: the projection formula.
* `TauCeti.indK0_one`: induction of the unit is the permutation class of the cosets.
* `TauCeti.indK0_resK0`: inducing a restricted class multiplies it by that permutation class.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, Springer GTM 42 (1977), §14.1, for
  restriction, induction and the projection formula on `R_k(G)` in arbitrary characteristic.
-/

public section

open CategoryTheory MonoidalCategory
open scoped MonoidAlgebra

namespace TauCeti

universe u

variable {k G : Type u} [Field k] [Group G] [Finite G] {S : Subgroup G}

/-- **Induction of the class of a representation**, read through `TauCeti.fdRepK0RingEquiv`: it is
the class of the induced representation `TauCeti.indFDRep A`. -/
theorem indK0_fdRepK0RingEquiv_of (A : FDRep k S) :
    indK0 k S (fdRepK0RingEquiv k S (ExactK0.of A)) =
      fdRepK0RingEquiv k G (ExactK0.of (indFDRep A)) := by
  rw [fdRepK0RingEquiv_of, fdRepK0RingEquiv_of, indK0_of_indFDRep]

/-- **The projection formula in `G₀(k[G])`**, `Ind_S^G (y · Res_S^G x) = (Ind_S^G y) · x`:
induction from a subgroup is a homomorphism of `G₀(k[G])`-modules, where `G₀(k[S])` is a
`G₀(k[G])`-module through restriction. -/
@[simp]
theorem indK0_mul_resK0 (y : ExactK0 (finiteModulesExactStructure k[S]))
    (x : ExactK0 (finiteModulesExactStructure k[G])) :
    indK0 k S (y * resK0 k S.subtype x) = indK0 k S y * x := by
  refine AddMonoidHom.ext_iff₂.1
    (fdRepK0RingEquiv_hom_ext₂
      (f := (AddMonoidHom.mul.compl₂ (resK0 k S.subtype)).compr₂ (indK0 k S))
      (g := AddMonoidHom.mul.comp (indK0 k S)) fun A B ↦ ?_) y x
  simp only [AddMonoidHom.compr₂_apply, AddMonoidHom.compl₂_apply, AddMonoidHom.coe_comp,
    Function.comp_apply, AddMonoidHom.mul_apply]
  rw [resK0_fdRepK0RingEquiv_of, ← map_mul, ExactK0.of_mul_of, indK0_fdRepK0RingEquiv_of,
    indK0_fdRepK0RingEquiv_of, ← map_mul, ExactK0.of_mul_of]
  exact congrArg _ (ExactK0.of_congr (indFDRepProjection A B))

/-- **Induction of the unit** is the permutation class `[k[G ⧸ S]]` of the cosets of `S`. -/
@[simp]
theorem indK0_one : indK0 k S 1 = permK0 k G (G ⧸ S) := by
  rw [exactK0_one_eq_of_trivial, indK0_of_trivial]

/-- **Inducing a restricted class multiplies it by the permutation class of the cosets**:
`Ind_S^G (Res_S^G x) = [k[G ⧸ S]] · x`, the projection formula at the unit. -/
theorem indK0_resK0 (x : ExactK0 (finiteModulesExactStructure k[G])) :
    indK0 k S (resK0 k S.subtype x) = permK0 k G (G ⧸ S) * x := by
  rw [← indK0_one, ← indK0_mul_resK0, one_mul]

end TauCeti
