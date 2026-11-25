/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.Category.Grp.Preadditive
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import TauCeti.Algebra.Ring.NegOnePow
public import TauCeti.AlgebraicTopology.CosimplicialObject.Op

/-!
# The alternating coface map complex: differential, augmentation and reversal

This file adds API to Mathlib's alternating coface map complex
`AlgebraicTopology.alternatingCofaceMapComplex`, the cochain complex with the alternating sums
of cofaces as differentials.

* Mathlib describes the differential of the alternating face map complex of a simplicial object
  (`AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq`). The cosimplicial counterpart
  `AlgebraicTopology.AlternatingCofaceMapComplex.obj_d_eq` states that the differential of the
  alternating coface map complex of a cosimplicial object in a preadditive category is the
  alternating sum `∑ᵢ (-1)ⁱ δⁱ` of the cofaces. For a cosimplicial abelian group it is evaluated
  at a cochain (`AlgebraicTopology.AlternatingCofaceMapComplex.obj_d_hom_apply`).
* `AlgebraicTopology.AlternatingCofaceMapComplex.ε` is the natural cochain map from the
  augmentation object, placed in degree `0`, to the alternating coface map complex of an augmented
  cosimplicial object. Its degree `0` component is the augmentation. It is the cosimplicial
  counterpart of Mathlib's `AlgebraicTopology.AlternatingFaceMapComplex.ε`.
* `AlgebraicTopology.opFunctorCompAlternatingCofaceMapComplexIso` compares the complex of the
  reversal `CosimplicialObject.opFunctor.obj X` with that of `X`. Reversing the cofaces
  multiplies the degree `n` differential by `(-1) ^ (n + 1)`, so the identity maps need not form
  a cochain map; multiplying by `q n = (-1) ^ (n * (n + 1) / 2)` in degree `n` always does,
  because `q (n + 1) = (-1) ^ (n + 1) * q n`. Since `q 0 = 1`, the comparison is compatible with the
  augmentations (`ε_app_comp_opFunctorCompAlternatingCofaceMapComplexIso_hom_app`).

The comparison is what transports a contraction of the complex of a reversed object to the
original complex. Such a contraction comes, for example, from an extra codegeneracy of the
reversal: maps splitting the last cofaces of the original object, together with a retraction of
its augmentation, that satisfy all the identities of an extra codegeneracy once reversed.
-/

public noncomputable section

open CategoryTheory Category Limits

open scoped Simplicial

universe v u

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

namespace AlgebraicTopology

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- The differentials of the alternating coface map complex are the differentials
`AlternatingCofaceMapComplex.objD` of its construction; this is
`AlternatingCofaceMapComplex.obj_d_eq` with the alternating sum of the cofaces kept folded. -/
@[simp]
lemma alternatingCofaceMapComplex_obj_d (X : CosimplicialObject C) (n : ℕ) :
    ((alternatingCofaceMapComplex C).obj X).d n (n + 1) = AlternatingCofaceMapComplex.objD X n :=
  AlternatingCofaceMapComplex.obj_d_eq X n

/-- The alternating coface map complex of a morphism is the morphism in each degree. -/
lemma alternatingCofaceMapComplex_map_f {X Y : CosimplicialObject C} (f : X ⟶ Y) (n : ℕ) :
    ((alternatingCofaceMapComplex C).map f).f n = f.app ⦋n⦌ := (rfl)

namespace AlternatingCofaceMapComplex

/-- A morphism from a constant cosimplicial object equalizes the two cofaces in degree `0`, so
its degree `0` component is a cocycle of the alternating coface map complex. -/
@[reassoc]
lemma app_zero_comp_objD_zero {A : C} {X : CosimplicialObject C}
    (g : (CosimplicialObject.const C).obj A ⟶ X) :
    g.app ⦋0⦌ ≫ objD X 0 = 0 := by
  have h (i : Fin 2) : g.app ⦋0⦌ ≫ X.δ i = g.app ⦋1⦌ := by
    simpa [CosimplicialObject.δ] using (g.naturality (SimplexCategory.δ i)).symm
  simp [Fin.sum_univ_two, h]

/-- The augmentation of an augmented cosimplicial object, as a natural cochain map from the
augmentation object placed in degree `0` to the alternating coface map complex. -/
def ε [HasZeroObject C] :
    CosimplicialObject.Augmented.point ⋙ CochainComplex.single₀ C ⟶
      CosimplicialObject.Augmented.drop ⋙ alternatingCofaceMapComplex C where
  -- The complex `(drop ⋙ alternatingCofaceMapComplex C).obj X` is that of `X.right`.
  app X := (CochainComplex.fromSingle₀Equiv _ _).symm ⟨X.hom.app ⦋0⦌,
    (congrArg (X.hom.app ⦋0⦌ ≫ ·) (alternatingCofaceMapComplex_obj_d X.right 0)).trans
      (app_zero_comp_objD_zero X.hom)⟩
  naturality X Y f := HomologicalComplex.from_single_hom_ext <| by
    -- `CosimplicialObject.Augmented` is not `@[implicit_reducible]`, unlike Mathlib's
    -- `SimplicialObject.Augmented`, so a goal mentioning `X.right` is not type-correct at the
    -- transparency of `simp` and `rw`, which fail on it. We compose the degree `0` component
    -- equations directly instead.
    refine (congrArg₂ (· ≫ ·) (CochainComplex.single₀_map_f_zero f.left)
      (CochainComplex.fromSingle₀Equiv_symm_apply_f_zero (Y.hom.app ⦋0⦌) _)).trans
      (Eq.trans ?_ (congrArg (· ≫ ((alternatingCofaceMapComplex C).map f.right).f 0)
        (CochainComplex.fromSingle₀Equiv_symm_apply_f_zero (X.hom.app ⦋0⦌) _).symm))
    exact CosimplicialObject.Augmented.w_app (η := f)

/-- The degree `0` component of the augmentation cochain map is the augmentation. -/
@[simp]
lemma ε_app_f_zero [HasZeroObject C] (X : CosimplicialObject.Augmented C) :
    (ε.app X).f 0 = X.hom.app ⦋0⦌ :=
  CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _

/-- The augmentation cochain map vanishes in positive degrees. -/
@[simp]
lemma ε_app_f_succ [HasZeroObject C] (X : CosimplicialObject.Augmented C) (n : ℕ) :
    (ε.app X).f (n + 1) = 0 :=
  (HomologicalComplex.isZero_single_obj_X _ _ _ _ (by simp)).eq_of_src _ _

/-- Reversing the cofaces multiplies the degree `n` differential by `(-1) ^ (n + 1)`. -/
lemma objD_opFunctor_obj (X : CosimplicialObject C) (n : ℕ) :
    objD (CosimplicialObject.opFunctor.obj X) n =
      (-1 : ℤ) ^ (n + 1) •
        (CosimplicialObject.opObjIso.hom ≫ objD X n ≫ CosimplicialObject.opObjIso.inv) := by
  simp only [objD, CosimplicialObject.opFunctor_obj_δ, Preadditive.comp_sum,
    Preadditive.sum_comp, Finset.smul_sum, Preadditive.comp_zsmul, Preadditive.zsmul_comp]
  rw [← Equiv.sum_comp (Fin.revPerm (n := n + 2))]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [Fin.revPerm_apply, Fin.rev_rev, smul_smul]
  congr 1
  -- The reversed index of `i : Fin (n + 2)` is `n + 1 - i`.
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (Nat.lt_succ_iff.mp i.is_lt)
  rw [Fin.val_rev, show n + 2 - (i + 1) = k by omega, hk, pow_add, mul_right_comm, ← mul_pow]
  simp

end AlternatingCofaceMapComplex

/-- Multiplying by `(-1) ^ (n * (n + 1) / 2)` in degree `n` intertwines the differentials of the
alternating coface map complexes of the reversal of `X` and of `X`. -/
private lemma neg_one_pow_triangle_smul_comp_objD (X : CosimplicialObject C) (n : ℕ) :
    ((-1 : ℤˣ) ^ (n * (n + 1) / 2) • CosimplicialObject.opObjIso.hom) ≫
        AlternatingCofaceMapComplex.objD X n =
      AlternatingCofaceMapComplex.objD (CosimplicialObject.opFunctor.obj X) n ≫
        ((-1 : ℤˣ) ^ ((n + 1) * (n + 1 + 1) / 2) • CosimplicialObject.opObjIso.hom) := by
  rw [AlternatingCofaceMapComplex.objD_opFunctor_obj, TauCeti.neg_one_pow_mul_succ_div_two_succ]
  simp only [Units.smul_def, Preadditive.zsmul_comp, Preadditive.comp_zsmul, assoc, Iso.inv_hom_id,
    comp_id, smul_smul]
  congr 1
  push_cast
  rw [mul_right_comm, ← mul_pow]
  simp

/-- The signed identity isomorphisms `opObjIso` commute with the components of a morphism. -/
private lemma opObjIso_hom_comp_app_comp_inv_comp_smul {X Y : CosimplicialObject C} (f : X ⟶ Y)
    (n : ℕ) (u : ℤˣ) :
    (CosimplicialObject.opObjIso.hom ≫ f.app ⦋n⦌ ≫ CosimplicialObject.opObjIso.inv) ≫
        (u • CosimplicialObject.opObjIso.hom) =
      (u • CosimplicialObject.opObjIso.hom) ≫ f.app ⦋n⦌ := by
  simp only [Units.smul_def, Preadditive.comp_zsmul, Preadditive.zsmul_comp, assoc,
    Iso.inv_hom_id, comp_id]

/-- The alternating coface map complex of the reversal of `X` is isomorphic to that of `X`, by
the sign `(-1) ^ (n * (n + 1) / 2)` in degree `n`. -/
def opFunctorCompAlternatingCofaceMapComplexIso :
    CosimplicialObject.opFunctor ⋙ alternatingCofaceMapComplex C ≅
      alternatingCofaceMapComplex C :=
  NatIso.ofComponents
    (fun X ↦ HomologicalComplex.Hom.isoOfComponents
      (fun n ↦ (-1 : ℤˣ) ^ (n * (n + 1) / 2) •
        (CosimplicialObject.opObjIso : (CosimplicialObject.opFunctor.obj X).obj ⦋n⦌ ≅ X.obj ⦋n⦌))
      (by
        rintro n _ rfl
        -- Both differentials are the alternating sums of the cofaces.
        exact (congrArg (_ ≫ ·) (alternatingCofaceMapComplex_obj_d X n)).trans
          ((neg_one_pow_triangle_smul_comp_objD X n).trans
            (congrArg (· ≫ _) (alternatingCofaceMapComplex_obj_d _ n).symm))))
    (fun f ↦ by
      ext n
      simp only [Functor.comp_map, HomologicalComplex.comp_f, alternatingCofaceMapComplex_map_f,
        CosimplicialObject.opFunctor_map_app]
      -- The components of the comparison are the signed isomorphisms `opObjIso`.
      exact opObjIso_hom_comp_app_comp_inv_comp_smul f n _)

/-- In degree `n`, the comparison is `opObjIso` multiplied by `(-1) ^ (n * (n + 1) / 2)`. -/
@[simp]
lemma opFunctorCompAlternatingCofaceMapComplexIso_hom_app_f (X : CosimplicialObject C) (n : ℕ) :
    (opFunctorCompAlternatingCofaceMapComplexIso.hom.app X).f n =
      (-1 : ℤˣ) ^ (n * (n + 1) / 2) •
        (CosimplicialObject.opObjIso.hom : (CosimplicialObject.opFunctor.obj X).obj ⦋n⦌ ⟶ _) :=
  (rfl)

/-- In degree `n`, the inverse comparison is the inverse of `opObjIso` multiplied by the inverse
of the sign `(-1) ^ (n * (n + 1) / 2)`. -/
@[simp]
lemma opFunctorCompAlternatingCofaceMapComplexIso_inv_app_f (X : CosimplicialObject C) (n : ℕ) :
    (opFunctorCompAlternatingCofaceMapComplexIso.inv.app X).f n =
      ((-1 : ℤˣ) ^ (n * (n + 1) / 2))⁻¹ •
        (CosimplicialObject.opObjIso.inv : X.obj ⦋n⦌ ⟶ _) :=
  (rfl)

/-- In degree `0` the sign is `1`, so the comparison is the identity isomorphism `opObjIso`. -/
lemma opFunctorCompAlternatingCofaceMapComplexIso_hom_app_f_zero (X : CosimplicialObject C) :
    (opFunctorCompAlternatingCofaceMapComplexIso.hom.app X).f 0 =
      (CosimplicialObject.opObjIso.hom : (CosimplicialObject.opFunctor.obj X).obj ⦋0⦌ ⟶ _) := by
  rw [opFunctorCompAlternatingCofaceMapComplexIso_hom_app_f, Nat.zero_mul, Nat.zero_div, pow_zero,
    one_smul]

/-- In degree `0` the sign is `1`, so the inverse comparison is the inverse of the identity
isomorphism `opObjIso`. -/
lemma opFunctorCompAlternatingCofaceMapComplexIso_inv_app_f_zero (X : CosimplicialObject C) :
    (opFunctorCompAlternatingCofaceMapComplexIso.inv.app X).f 0 =
      (CosimplicialObject.opObjIso.inv :
        X.obj ⦋0⦌ ⟶ (CosimplicialObject.opFunctor.obj X).obj ⦋0⦌) := by
  rw [opFunctorCompAlternatingCofaceMapComplexIso_inv_app_f, Nat.zero_mul, Nat.zero_div, pow_zero,
    inv_one, one_smul]

/-- The sign comparison of the complexes of `X` and of its reversal is compatible with the
augmentations. -/
@[simp, reassoc]
lemma ε_app_comp_opFunctorCompAlternatingCofaceMapComplexIso_hom_app [HasZeroObject C]
    (X : CosimplicialObject.Augmented C) :
    AlternatingCofaceMapComplex.ε.app (CosimplicialObject.Augmented.opFunctor.obj X) ≫
        opFunctorCompAlternatingCofaceMapComplexIso.hom.app X.right =
      AlternatingCofaceMapComplex.ε.app X := by
  apply HomologicalComplex.from_single_hom_ext
  refine (HomologicalComplex.comp_f _ _ 0).trans ?_
  rw [AlternatingCofaceMapComplex.ε_app_f_zero, AlternatingCofaceMapComplex.ε_app_f_zero,
    opFunctorCompAlternatingCofaceMapComplexIso_hom_app_f_zero,
    CosimplicialObject.Augmented.opFunctor_obj_hom_app]
  exact (assoc _ _ _).trans ((congrArg (X.hom.app ⦋0⦌ ≫ ·)
    CosimplicialObject.opObjIso.inv_hom_id).trans (comp_id _))

end AlgebraicTopology
