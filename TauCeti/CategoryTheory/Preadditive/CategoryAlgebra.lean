/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Preadditive.SingleObj
public import Mathlib.Data.DFinsupp.Module
public import Mathlib.RingTheory.Idempotents

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Ring.Associator
import Mathlib.Data.DFinsupp.BigOperators
import Mathlib.Data.DFinsupp.Small

/-!
# Category algebras of preadditive categories

The category algebra is the direct sum of all morphism groups. Its multiplication
composes single entries in diagrammatic order and is zero on noncomposable entries.
For a finite object type, the sum of the identity entries is a unit. The corresponding
orthogonal idempotents recover the object components of modules over the algebra.

For finite object types this is the ring of Mitchell, *Rings with several objects*,
§7, p. 33. For arbitrary object types we use the finite-support variant of Harada,
*Perfect categories I*, pp. 338–339, before Lemma 7.

## Main declarations

* `TauCeti.CategoryAlgebra`: the finitely supported morphism matrices of a preadditive category.
* `TauCeti.CategoryAlgebra.mul_apply`: the entrywise product formula for finitely many objects.
* `TauCeti.categoryAlgebraSingleObjRingEquiv`: the one-object comparison with the original ring.
-/

public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive

namespace TauCeti

universe u v w

/-- The direct sum of the morphism groups of a preadditive category, with diagrammatic
matrix multiplication. The representation is exposed for the inherited additive and
function-like instances. -/
@[expose] def CategoryAlgebra (C : Type u) [Category.{v} C] [Preadditive C] : Type (max u v) :=
  Π₀ p : C × C, (p.1 ⟶ p.2)

namespace CategoryAlgebra

variable {C : Type u} [Category.{v} C] [Preadditive C]

instance : DFunLike (CategoryAlgebra C) (C × C) (fun p ↦ p.1 ⟶ p.2) :=
  inferInstanceAs (DFunLike (Π₀ p : C × C, (p.1 ⟶ p.2)) (C × C) (fun p ↦ p.1 ⟶ p.2))

instance : AddCommGroup (CategoryAlgebra C) :=
  inferInstanceAs (AddCommGroup (Π₀ p : C × C, (p.1 ⟶ p.2)))

@[ext]
theorem ext {a b : CategoryAlgebra C} (h : ∀ p, a p = b p) : a = b :=
  DFunLike.ext a b h

@[simp]
theorem zero_apply (p : C × C) : (0 : CategoryAlgebra C) p = 0 := (rfl)

@[simp]
theorem add_apply (a b : CategoryAlgebra C) (p : C × C) : (a + b) p = a p + b p := (rfl)

open Classical in
/-- The matrix with a single morphism in the indicated entry. -/
noncomputable def single (p : C × C) (f : p.1 ⟶ p.2) : CategoryAlgebra C :=
  DFinsupp.single p f

open Classical in
private noncomputable def singleAddHom (p : C × C) : (p.1 ⟶ p.2) →+ CategoryAlgebra C :=
  DFinsupp.singleAddHom (fun p : C × C ↦ p.1 ⟶ p.2) p

@[simp]
theorem single_apply_same (p : C × C) (f : p.1 ⟶ p.2) : single p f p = f := by
  classical
  exact DFinsupp.single_eq_same (β := fun q : C × C ↦ q.1 ⟶ q.2)

@[simp]
theorem single_apply_of_ne {p q : C × C} (h : q ≠ p) (f : p.1 ⟶ p.2) :
    single p f q = 0 := by
  classical
  exact DFinsupp.single_eq_of_ne (β := fun q : C × C ↦ q.1 ⟶ q.2) h

@[simp]
theorem single_zero (p : C × C) : single p 0 = 0 := by
  classical
  exact DFinsupp.single_zero p

theorem single_add (p : C × C) (f g : p.1 ⟶ p.2) :
    single p (f + g) = single p f + single p g :=
  map_add (singleAddHom p) f g

/-- An additive map out of the category algebra is determined by its values on single entries. -/
theorem addHom_ext {M : Type*} [AddZeroClass M] {f g : CategoryAlgebra C →+ M}
    (h : ∀ p a, f (single p a) = g (single p a)) : f = g := by
  classical
  exact DFinsupp.addHom_ext h

open Classical in
/-- Extend additive maps on the entries to an additive map on their direct sum. -/
noncomputable def liftAddHom {M : Type*} [AddCommMonoid M] (f : ∀ p : C × C, (p.1 ⟶ p.2) →+ M) :
    CategoryAlgebra C →+ M :=
  DFinsupp.sumAddHom f

@[simp]
theorem liftAddHom_single {M : Type*} [AddCommMonoid M]
    (f : ∀ p : C × C, (p.1 ⟶ p.2) →+ M) (p : C × C) (a : p.1 ⟶ p.2) :
    liftAddHom f (single p a) = f p a := by
  classical
  exact DFinsupp.sumAddHom_single f p a

private noncomputable def mulEntry (p q : C × C) :
    (p.1 ⟶ p.2) →+ (q.1 ⟶ q.2) →+ CategoryAlgebra C := by
  classical
  exact if h : p.2 = q.1 then
    (AddMonoidHom.compr₂ compHom (singleAddHom (p.1, q.2))).comp
      (rightComp _ (eqToHom h))
  else 0

private noncomputable def mulHom : CategoryAlgebra C →+ CategoryAlgebra C →+ CategoryAlgebra C :=
  liftAddHom fun p ↦
    { toFun := fun f ↦ liftAddHom fun q ↦ mulEntry p q f
      map_zero' := addHom_ext fun q g ↦ by simp
      map_add' := fun f f' ↦ addHom_ext fun q g ↦ by simp }

@[no_expose]
noncomputable instance : Mul (CategoryAlgebra C) :=
  ⟨fun a b ↦ mulHom a b⟩

private theorem mul_def (a b : CategoryAlgebra C) : a * b = mulHom a b := (rfl)

noncomputable instance : NonUnitalNonAssocRing (CategoryAlgebra C) where
  __ := (inferInstance : AddCommGroup (CategoryAlgebra C))
  __ := (inferInstance : Mul (CategoryAlgebra C))
  zero_mul a := by
    rw [mul_def, map_zero, AddMonoidHom.zero_apply]
  mul_zero a := by rw [mul_def, map_zero]
  left_distrib a b c := by simp only [mul_def, map_add]
  right_distrib a b c := by simp only [mul_def, map_add, AddMonoidHom.add_apply]

open Classical in
private theorem single_mul_single_eq (p q : C × C) (f : p.1 ⟶ p.2) (g : q.1 ⟶ q.2) :
    single p f * single q g =
      if h : p.2 = q.1 then single (p.1, q.2) (f ≫ eqToHom h ≫ g) else 0 := by
  calc
    _ = mulEntry p q f g := by
      rw [mul_def, mulHom, liftAddHom_single]
      exact liftAddHom_single _ _ _
    _ = _ := by
      unfold mulEntry
      split_ifs
      · exact congrArg (single (p.1, q.2)) (Category.assoc _ _ _)
      · exact AddMonoidHom.zero_apply _

/-- Single entries multiply by composing their morphisms at the common object. -/
@[simp]
theorem single_mul_single {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    single (X, Y) f * single (Y, Z) g = single (X, Z) (f ≫ g) := by
  rw [single_mul_single_eq]
  simp

/-- Single entries with mismatched middle objects multiply to zero. -/
@[simp]
theorem single_mul_single_of_ne {X Y Z W : C} (h : Y ≠ Z) (f : X ⟶ Y) (g : Z ⟶ W) :
    single (X, Y) f * single (Z, W) g = 0 := by
  rw [single_mul_single_eq]
  exact dite_eq_right h

private theorem single_mul_assoc {X Y Z W U V : C} (f : X ⟶ Y) (g : Z ⟶ W) (h : U ⟶ V) :
    single (X, Y) f * single (Z, W) g * single (U, V) h =
      single (X, Y) f * (single (Z, W) g * single (U, V) h) := by
  by_cases h₁ : Y = Z
  · subst Z
    by_cases h₂ : W = U
    · subst U
      simp [Category.assoc]
    · simp [h₂]
  · by_cases h₂ : W = U
    · subst U
      simp [h₁]
    · simp [h₁, h₂]

noncomputable instance : NonUnitalRing (CategoryAlgebra C) where
  __ := (inferInstance : NonUnitalNonAssocRing (CategoryAlgebra C))
  mul_assoc := by
    have heq : AddMonoidHom.mulLeft₃ (R := CategoryAlgebra C) = AddMonoidHom.mulRight₃ := by
      apply addHom_ext
      rintro ⟨X, Y⟩ f
      apply addHom_ext
      rintro ⟨Z, W⟩ g
      apply addHom_ext
      rintro ⟨U, V⟩ h
      simpa only [AddMonoidHom.mulLeft₃_apply, AddMonoidHom.mulRight₃_apply] using
        single_mul_assoc f g h
    exact (AddMonoidHom.mulLeft₃_eq_mulRight₃_iff_associative.mp heq).assoc

section Linear

variable {R : Type*} [Semiring R] [Linear R C]

instance : Module R (CategoryAlgebra C) :=
  inferInstanceAs (Module R (Π₀ p : C × C, (p.1 ⟶ p.2)))

@[simp]
theorem smul_apply (r : R) (a : CategoryAlgebra C) (p : C × C) :
    (r • a) p = r • a p := (rfl)

end Linear

instance [Small.{w} C] [LocallySmall.{w} C] : Small.{w} (CategoryAlgebra C) :=
  inferInstanceAs (Small.{w} (Π₀ p : C × C, (p.1 ⟶ p.2)))

section Finite

variable [Finite C]

private noncomputable def identity : CategoryAlgebra C :=
  letI := Fintype.ofFinite C
  ∑ X : C, single (X, X) (𝟙 X)

private theorem identity_mul_single (p : C × C) (f : p.1 ⟶ p.2) :
    identity * single p f = single p f := by
  classical
  let := Fintype.ofFinite C
  rw [identity, Finset.sum_mul, Finset.sum_eq_single p.1]
  · rcases p with ⟨X, Y⟩
    simp
  · intro X _ h
    exact single_mul_single_of_ne h _ _
  · simp

private theorem single_mul_identity (p : C × C) (f : p.1 ⟶ p.2) :
    single p f * identity = single p f := by
  classical
  let := Fintype.ofFinite C
  rw [identity, Finset.mul_sum, Finset.sum_eq_single p.2]
  · rcases p with ⟨X, Y⟩
    simp
  · intro X _ h
    exact single_mul_single_of_ne h.symm _ _
  · simp

@[no_expose]
noncomputable instance : One (CategoryAlgebra C) := ⟨identity⟩

private theorem one_mul' (a : CategoryAlgebra C) : identity * a = a := by
  have h : AddMonoidHom.mulLeft (identity : CategoryAlgebra C) = AddMonoidHom.id _ :=
    addHom_ext identity_mul_single
  exact DFunLike.congr_fun h a

private theorem mul_one' (a : CategoryAlgebra C) : a * identity = a := by
  have h : AddMonoidHom.mulRight (identity : CategoryAlgebra C) = AddMonoidHom.id _ :=
    addHom_ext single_mul_identity
  exact DFunLike.congr_fun h a

noncomputable instance : Ring (CategoryAlgebra C) where
  __ := (inferInstance : AddCommGroup (CategoryAlgebra C))
  __ := (inferInstance : NonUnitalSemiring (CategoryAlgebra C))
  __ := (inferInstance : One (CategoryAlgebra C))
  one_mul a := by exact one_mul' a
  mul_one a := by exact mul_one' a
  natCast := fun n ↦ n • (1 : CategoryAlgebra C)
  natCast_zero := zero_nsmul _
  natCast_succ := fun n ↦ succ_nsmul _ n
  intCast := fun n ↦ n • (1 : CategoryAlgebra C)
  intCast_ofNat := fun n ↦ natCast_zsmul _ n
  intCast_negSucc := fun n ↦ negSucc_zsmul _ n

end Finite

/-- The unit is the sum of the identity morphisms in the diagonal entries. -/
theorem one_eq_sum_single [Fintype C] :
    (1 : CategoryAlgebra C) = ∑ X : C, single (X, X) (𝟙 X) := by
  -- The two sums differ only in their chosen enumeration of the finite object type.
  have h : Fintype.ofFinite C = (inferInstance : Fintype C) := Subsingleton.elim _ _
  exact congrArg (fun i : Fintype C ↦ @Finset.univ C i |>.sum (fun X ↦ single (X, X) (𝟙 X))) h

private def evalAddHom (p : C × C) : CategoryAlgebra C →+ (p.1 ⟶ p.2) :=
  DFinsupp.evalAddMonoidHom (β := fun q : C × C ↦ q.1 ⟶ q.2) p

private theorem evalAddHom_apply (p : C × C) (a : CategoryAlgebra C) :
    evalAddHom p a = a p := (rfl)

@[simp]
theorem one_apply_diag [Finite C] (X : C) : (1 : CategoryAlgebra C) (X, X) = 𝟙 X := by
  classical
  let := Fintype.ofFinite C
  rw [one_eq_sum_single, ← evalAddHom_apply, map_sum, Finset.sum_eq_single X]
  · exact single_apply_same _ _
  · intro Y _ h
    exact single_apply_of_ne (fun e ↦ h (congrArg Prod.fst e).symm) _
  · simp

@[simp]
theorem one_apply_of_ne [Finite C] {X Y : C} (h : X ≠ Y) : (1 : CategoryAlgebra C) (X, Y) = 0 := by
  let := Fintype.ofFinite C
  rw [one_eq_sum_single, ← evalAddHom_apply, map_sum]
  exact Finset.sum_eq_zero fun Z _ ↦ single_apply_of_ne
    (fun e ↦ h ((congrArg Prod.fst e).trans (congrArg Prod.snd e).symm)) _

/-- The diagonal identity entries are a complete family of orthogonal idempotents. -/
theorem completeOrthogonalIdempotents_single_id [Fintype C] :
    CompleteOrthogonalIdempotents (fun X : C ↦ single (X, X) (𝟙 X)) :=
  CompleteOrthogonalIdempotents.iff_ortho_complete.mpr
    ⟨fun _ _ h ↦ single_mul_single_of_ne h _ _, one_eq_sum_single.symm⟩

private theorem sum_comp_single [Fintype C] {X Z U V W T : C} (f : U ⟶ V) (g : W ⟶ T) :
    (single (U, V) f * single (W, T) g) (X, Z) =
      ∑ Y : C, (single (U, V) f) (X, Y) ≫ (single (W, T) g) (Y, Z) := by
  classical
  by_cases h : V = W
  · subst W
    rw [single_mul_single f g, Finset.sum_eq_single V]
    · by_cases h₁ : X = U
      · subst U
        by_cases h₂ : Z = T
        · subst T
          simp
        · rw [single_apply_of_ne (p := (X, T)) (q := (X, Z))
            (fun e ↦ h₂ (congrArg Prod.snd e)) (f ≫ g),
            single_apply_of_ne (p := (V, T)) (q := (V, Z))
              (fun e ↦ h₂ (congrArg Prod.snd e)) g, comp_zero]
      · rw [single_apply_of_ne (p := (U, T)) (q := (X, Z))
            (fun e ↦ h₁ (congrArg Prod.fst e)) (f ≫ g),
          single_apply_of_ne (p := (U, V)) (q := (X, V))
            (fun e ↦ h₁ (congrArg Prod.fst e)) f, zero_comp]
    · intro Y _ hY
      rw [single_apply_of_ne (p := (U, V)) (q := (X, Y))
            (fun e ↦ hY (congrArg Prod.snd e)) f, zero_comp]
    · simp
  · rw [single_mul_single_of_ne h f g, zero_apply]
    symm
    apply Finset.sum_eq_zero
    intro Y _
    by_cases hY : Y = V
    · subst Y
      rw [single_apply_of_ne (p := (W, T)) (q := (V, Z))
            (fun e ↦ h (congrArg Prod.fst e)) g, comp_zero]
    · rw [single_apply_of_ne (p := (U, V)) (q := (X, Y))
            (fun e ↦ hY (congrArg Prod.snd e)) f, zero_comp]

/-- Each product entry is the sum of the composites through the intermediate objects. -/
theorem mul_apply [Fintype C] (a b : CategoryAlgebra C) (X Z : C) :
    (a * b) (X, Z) = ∑ Y : C, a (X, Y) ≫ b (Y, Z) := by
  let product := AddMonoidHom.compr₂ AddMonoidHom.mul (evalAddHom (X, Z))
  let contraction : CategoryAlgebra C →+ CategoryAlgebra C →+ (X ⟶ Z) :=
    ∑ Y : C, (AddMonoidHom.compl₂ compHom (evalAddHom (Y, Z))).comp (evalAddHom (X, Y))
  have h : product = contraction := by
    apply addHom_ext
    rintro ⟨U, V⟩ f
    apply addHom_ext
    rintro ⟨W, T⟩ g
    simp only [product, contraction, AddMonoidHom.compr₂_apply, AddMonoidHom.mul_apply,
      AddMonoidHom.finsetSum_apply, AddMonoidHom.comp_apply, AddMonoidHom.compl₂_apply]
    exact sum_comp_single (X := X) (Z := Z) (U := U) (V := V) (W := W) (T := T) f g
  have hab := DFunLike.congr_fun (DFunLike.congr_fun h a) b
  simp only [product, contraction, AddMonoidHom.compr₂_apply, AddMonoidHom.mul_apply,
    AddMonoidHom.finsetSum_apply, AddMonoidHom.comp_apply, AddMonoidHom.compl₂_apply] at hab
  exact hab

section Linear

variable [Finite C] (R : Type*) [CommSemiring R] [Linear R C]

/-- The entrywise scalar action makes the finite-object category ring an algebra. -/
noncomputable instance : Algebra R (CategoryAlgebra C) :=
  Algebra.ofModule
    (fun r a b ↦ by
      let := Fintype.ofFinite C
      apply ext
      rintro ⟨X, Z⟩
      simp only [mul_apply, smul_apply, Linear.smul_comp, Finset.smul_sum])
    (fun r a b ↦ by
      let := Fintype.ofFinite C
      apply ext
      rintro ⟨X, Z⟩
      simp only [mul_apply, smul_apply, Linear.comp_smul, Finset.smul_sum])

@[simp]
theorem algebraMap_apply_diag (r : R) (X : C) :
    (algebraMap R (CategoryAlgebra C) r) (X, X) = r • 𝟙 X := by
  rw [Algebra.algebraMap_eq_smul_one, smul_apply, one_apply_diag]

@[simp]
theorem algebraMap_apply_of_ne (r : R) {X Y : C} (h : X ≠ Y) :
    (algebraMap R (CategoryAlgebra C) r) (X, Y) = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, smul_apply, one_apply_of_ne h, smul_zero]

end Linear

@[simp]
theorem intCast_apply_diag [Finite C] (n : ℤ) (X : C) : (n : CategoryAlgebra C) (X, X) = n • 𝟙 X :=
  algebraMap_apply_diag ℤ n X

@[simp]
theorem intCast_apply_of_ne [Finite C] (n : ℤ) {X Y : C} (h : X ≠ Y) :
    (n : CategoryAlgebra C) (X, Y) = 0 :=
  algebraMap_apply_of_ne ℤ n h

end CategoryAlgebra

open CategoryAlgebra in
/-- Evaluation at the unique entry identifies the category algebra of `SingleObj Aᵐᵒᵖ` with
`A`. Diagrammatic composition reverses the multiplication in `Aᵐᵒᵖ`. -/
noncomputable def categoryAlgebraSingleObjRingEquiv (A : Type u) [Ring A] :
    CategoryAlgebra (SingleObj Aᵐᵒᵖ) ≃+* A where
  toFun a := MulOpposite.unop (a (SingleObj.star _, SingleObj.star _))
  invFun a := single (SingleObj.star _, SingleObj.star _) (MulOpposite.op a)
  left_inv a := by
    apply CategoryAlgebra.ext
    intro p
    have h : p = (SingleObj.star _, SingleObj.star _) := Subsingleton.elim _ _
    subst p
    exact single_apply_same _ _
  right_inv a := congrArg MulOpposite.unop (single_apply_same _ _)
  map_mul' a b := by
    rw [CategoryAlgebra.mul_apply, Fintype.sum_unique, SingleObj.comp_as_mul, MulOpposite.unop_mul]
    rfl
  map_add' a b := by rw [CategoryAlgebra.add_apply, MulOpposite.unop_add]

@[simp]
theorem categoryAlgebraSingleObjRingEquiv_apply (A : Type u) [Ring A]
    (a : CategoryAlgebra (SingleObj Aᵐᵒᵖ)) :
    categoryAlgebraSingleObjRingEquiv A a =
      MulOpposite.unop (a (SingleObj.star _, SingleObj.star _)) := (rfl)

@[simp]
theorem categoryAlgebraSingleObjRingEquiv_symm_apply (A : Type u) [Ring A] (a : A) :
    (categoryAlgebraSingleObjRingEquiv A).symm a =
      CategoryAlgebra.single (SingleObj.star _, SingleObj.star _) (MulOpposite.op a) := (rfl)

end TauCeti
