/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
public import Mathlib.Algebra.Category.Grp.Preadditive
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex

/-!
# The differential of the alternating coface map complex

Mathlib describes the differential of the alternating face map complex of a simplicial object
(`AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq`). This file states the cosimplicial
counterpart: the differential of the alternating coface map complex of a cosimplicial object in a
preadditive category is the alternating sum `∑ᵢ (-1)ⁱ δⁱ` of the cofaces
(`AlgebraicTopology.AlternatingCofaceMapComplex.obj_d_eq`). For a cosimplicial abelian group it is
evaluated at a cochain (`AlgebraicTopology.AlternatingCofaceMapComplex.obj_d_hom_apply`).
-/

public section

universe u

open CategoryTheory Simplicial

namespace AlgebraicTopology.AlternatingCofaceMapComplex

/-- The differential of the alternating coface map complex of a cosimplicial object is the
alternating sum `∑ᵢ (-1)ⁱ δⁱ` of the cofaces. -/
theorem obj_d_eq {C : Type*} [Category* C] [Preadditive C] (X : CosimplicialObject C) (n : ℕ) :
    ((alternatingCofaceMapComplex C).obj X).d n (n + 1) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • X.δ i :=
  CochainComplex.of_d (fun n ↦ X.obj ⦋n⦌) (objD X) n

/-- The differential of the alternating coface map complex of a cosimplicial abelian group,
evaluated at a cochain, is the alternating sum `∑ᵢ (-1)ⁱ δⁱ` of the cofaces. -/
theorem obj_d_hom_apply (X : CosimplicialObject AddCommGrpCat.{u}) (n : ℕ) (x : X.obj ⦋n⦌) :
    (((alternatingCofaceMapComplex AddCommGrpCat).obj X).d n (n + 1)).hom x =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (X.δ i).hom x := by
  rw [obj_d_eq]
  -- Restate the goal with the morphism typed by the cosimplicial object, not the complex, and
  -- its underlying map `Hom.hom` as the additive equivalence `homAddEquiv`, which is additive in
  -- the morphism.
  change AddCommGrpCat.homAddEquiv (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • X.δ i) x = _
  rw [map_sum, AddMonoidHom.finsetSum_apply]
  simp only [map_zsmul, AddCommGrpCat.homAddEquiv_apply, AddMonoidHom.zsmul_apply]

end AlgebraicTopology.AlternatingCofaceMapComplex
