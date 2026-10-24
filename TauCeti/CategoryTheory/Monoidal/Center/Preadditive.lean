/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Center
public import Mathlib.CategoryTheory.Monoidal.Linear
public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# The Drinfeld centre of a preadditive monoidal category

Mathlib makes the Drinfeld centre `Center C` of a monoidal category a braided monoidal category,
with the monoidal forgetful functor `Center.forget C : Center C ⥤ C`. This file equips the centre
with the additive structure induced from `C`, which is what is needed to treat the centre of a
fusion category as a linear category in its own right.

A morphism `(X, β_X) ⟶ (Y, β_Y)` of the centre is a morphism `f : X ⟶ Y` of `C` satisfying
`(f ▷ U) ≫ β_Y U = β_X U ≫ (U ◁ f)` for every `U`. When the whiskerings of `C` are additive
(`MonoidalPreadditive C`), or `R`-linear (`MonoidalLinear R C`), this condition is preserved by
sums, negatives and scalar multiples, so `Center C` is preadditive, or `R`-linear, with the
operations computed on underlying morphisms. The forgetful functor, which is faithful for any
monoidal category, is then additive and `R`-linear, and the centre is again monoidal preadditive,
or monoidal `R`-linear.

Finite biproducts are also computed in `C`. If each summand `f j` of a finite biproduct `⨁ f`
carries a half-braiding `b j`, then `⨁ f` carries the half-braiding `HalfBraiding.biproduct f b`,
which restricts to `b j` on the summand `f j`: its component at `U` distributes `(⨁ f) ⊗ U` over
the summands, applies the half-braidings `b j`, and collects the result into `U ⊗ ⨁ f` again.
The projections and inclusions of the biproduct are then morphisms of the centre, and form a
biproduct there. Since the forgetful functor is additive, it preserves these biproducts.

## Main declarations

* `CategoryTheory.Center.instPreadditive` and `CategoryTheory.Center.instLinear`: the centre of a
  monoidal preadditive (resp. `R`-linear) category is preadditive (resp. `R`-linear), with the
  operations computed by `CategoryTheory.Center.add_f`, `CategoryTheory.Center.smul_f` and their
  relatives;
* `CategoryTheory.Center.instFaithfulForget`, `CategoryTheory.Center.instAdditiveForget` and
  `CategoryTheory.Center.instLinearForget`: the forgetful functor is faithful, additive and
  linear;
* `CategoryTheory.Center.instMonoidalPreadditive` and `CategoryTheory.Center.instMonoidalLinear`:
  the centre is monoidal preadditive (resp. monoidal `R`-linear);
* `CategoryTheory.HalfBraiding.biproduct`: the half-braiding on a finite biproduct of objects
  with half-braidings, characterized by
  `CategoryTheory.HalfBraiding.biproduct_ι_comp_biproduct_β_hom` and
  `CategoryTheory.HalfBraiding.biproduct_β_hom_comp_biproduct_π`;
* `CategoryTheory.Center.biproductBicone` and `CategoryTheory.Center.isBilimitBiproductBicone`:
  the biproduct of a finite family of objects of the centre, giving the instance
  `HasFiniteBiproducts (Center C)`.

## References

* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §7.13
-/

public section

universe v u

namespace CategoryTheory

open MonoidalCategory Limits

namespace HalfBraiding

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C] [MonoidalPreadditive C]
  [HasFiniteBiproducts C] {J : Type} [Finite J]

/-- The half-braiding on a finite biproduct `⨁ f` of objects carrying half-braidings `b j`: its
component at `U` distributes `(⨁ f) ⊗ U` over the summands, applies the half-braidings of the
summands, and collects `U ⊗ ⨁ f` again. -/
noncomputable def biproduct (f : J → C) (b : ∀ j, HalfBraiding (f j)) :
    HalfBraiding (⨁ f) where
  β U := rightDistributor f U ≪≫ biproduct.mapIso (fun j ↦ (b j).β U) ≪≫
    (leftDistributor U f).symm
  monoidal U U' := by
    refine rightDistributor_ext_left fun j ↦ ?_
    have key (V : C) : biproduct.ι f j ▷ V ≫ (rightDistributor f V ≪≫
        biproduct.mapIso (fun j ↦ (b j).β V) ≪≫ (leftDistributor V f).symm).hom =
          ((b j).β V).hom ≫ V ◁ biproduct.ι f j := by
      simp
    rw [key, (b j).monoidal, associator_inv_naturality_left_assoc, ← comp_whiskerRight_assoc,
      key, comp_whiskerRight_assoc, associator_naturality_middle_assoc,
      ← whiskerLeft_comp_assoc, key, whiskerLeft_comp_assoc, associator_inv_naturality_right]
    simp only [Category.assoc]
  naturality g := by
    refine rightDistributor_ext_left fun j ↦ ?_
    rw [← whisker_exchange_assoc]
    simp [whisker_exchange, HalfBraiding.naturality_assoc]

/-- On the summand `f j`, the half-braiding of `⨁ f` is that of `f j`. -/
@[reassoc (attr := simp)]
theorem biproduct_ι_comp_biproduct_β_hom (f : J → C) (b : ∀ j, HalfBraiding (f j)) (U : C)
    (j : J) :
    biproduct.ι f j ▷ U ≫ ((HalfBraiding.biproduct f b).β U).hom =
      ((b j).β U).hom ≫ U ◁ biproduct.ι f j := by
  simp [HalfBraiding.biproduct]

/-- Projected to the summand `f j`, the half-braiding of `⨁ f` is that of `f j`. -/
@[reassoc (attr := simp)]
theorem biproduct_β_hom_comp_biproduct_π (f : J → C) (b : ∀ j, HalfBraiding (f j)) (U : C)
    (j : J) :
    ((HalfBraiding.biproduct f b).β U).hom ≫ U ◁ biproduct.π f j =
      biproduct.π f j ▷ U ≫ ((b j).β U).hom := by
  simp [HalfBraiding.biproduct]

end HalfBraiding

namespace Center

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The forgetful functor from the centre is faithful: a morphism of the centre is determined by
its underlying morphism. -/
instance instFaithfulForget : (forget C).Faithful where
  map_injective h := ext _ _ h

section Preadditive

variable [Preadditive C] [MonoidalPreadditive C] {X Y : Center C}

attribute [local simp] MonoidalPreadditive.whiskerLeft_add MonoidalPreadditive.add_whiskerRight

instance instZeroHom : Zero (X ⟶ Y) where
  zero := { f := 0 }

instance instAddHom : Add (X ⟶ Y) where
  add f g := { f := f.f + g.f }

instance instNegHom : Neg (X ⟶ Y) where
  neg f :=
    { f := -f.f
      comm U := by
        rw [show (-f.f) ▷ U = -(f.f ▷ U) from (tensorRight U).map_neg,
          show U ◁ (-f.f) = -(U ◁ f.f) from (tensorLeft U).map_neg]
        simp }

instance instSubHom : Sub (X ⟶ Y) where
  sub f g :=
    { f := f.f - g.f
      comm U := by
        rw [show (f.f - g.f) ▷ U = f.f ▷ U - g.f ▷ U from (tensorRight U).map_sub,
          show U ◁ (f.f - g.f) = U ◁ f.f - U ◁ g.f from (tensorLeft U).map_sub]
        simp }

instance instSMulNatHom : SMul ℕ (X ⟶ Y) where
  smul n f :=
    { f := n • f.f
      comm U := by
        rw [show (n • f.f) ▷ U = n • (f.f ▷ U) from (tensorRight U).map_nsmul,
          show U ◁ (n • f.f) = n • (U ◁ f.f) from (tensorLeft U).map_nsmul]
        simp }

instance instSMulIntHom : SMul ℤ (X ⟶ Y) where
  smul n f :=
    { f := n • f.f
      comm U := by
        rw [show (n • f.f) ▷ U = n • (f.f ▷ U) from (tensorRight U).map_zsmul,
          show U ◁ (n • f.f) = n • (U ◁ f.f) from (tensorLeft U).map_zsmul]
        simp }

@[simp] theorem zero_f : (0 : X ⟶ Y).f = 0 := rfl
@[simp] theorem add_f (f g : X ⟶ Y) : (f + g).f = f.f + g.f := rfl
@[simp] theorem neg_f (f : X ⟶ Y) : (-f).f = -f.f := rfl
@[simp] theorem sub_f (f g : X ⟶ Y) : (f - g).f = f.f - g.f := rfl
@[simp] theorem nsmul_f (n : ℕ) (f : X ⟶ Y) : (n • f).f = n • f.f := rfl
@[simp] theorem zsmul_f (n : ℤ) (f : X ⟶ Y) : (n • f).f = n • f.f := rfl

/-- The centre of a monoidal preadditive category is preadditive, with the additive structure on
morphisms computed on underlying morphisms. -/
instance instPreadditive : Preadditive (Center C) where
  homGroup _ _ :=
    (forget C).map_injective.addCommGroup _ zero_f add_f neg_f sub_f (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
  add_comp _ _ _ _ _ _ := by ext; exact Preadditive.add_comp _ _ _ _ _ _
  comp_add _ _ _ _ _ _ := by ext; exact Preadditive.comp_add _ _ _ _ _ _

/-- The forgetful functor from the centre is additive. -/
instance instAdditiveForget : (forget C).Additive where

@[simp]
theorem sum_f {ι : Type*} (s : Finset ι) (f : ι → (X ⟶ Y)) :
    (∑ i ∈ s, f i).f = ∑ i ∈ s, (f i).f :=
  (forget C).map_sum f s

/-- The centre of a monoidal preadditive category is monoidal preadditive. -/
instance instMonoidalPreadditive : MonoidalPreadditive (Center C) :=
  monoidalPreadditive_of_faithful (forget C)

end Preadditive

section Linear

variable [Preadditive C] [MonoidalPreadditive C] {R : Type*} [Semiring R] [Linear R C]
  [MonoidalLinear R C]

/-- The centre of a monoidal `R`-linear category is `R`-linear, with scalar multiplication
computed on underlying morphisms. -/
instance instLinear : Linear R (Center C) where
  homModule X Y :=
    { smul r f := { f := r • f.f }
      one_smul _ := by ext; exact one_smul _ _
      mul_smul _ _ _ := by ext; exact mul_smul _ _ _
      smul_zero _ := by ext; exact smul_zero _
      smul_add _ _ _ := by ext; exact smul_add _ _ _
      add_smul _ _ _ := by ext; exact add_smul _ _ _
      zero_smul _ := by ext; exact zero_smul _ _ }
  smul_comp _ _ _ _ _ _ := by ext; exact Linear.smul_comp _ _ _ _ _ _
  comp_smul _ _ _ _ _ _ := by ext; exact Linear.comp_smul _ _ _ _ _ _

@[simp]
theorem smul_f {X Y : Center C} (r : R) (f : X ⟶ Y) : (r • f).f = r • f.f :=
  rfl

/-- The forgetful functor from the centre is `R`-linear. -/
instance instLinearForget : (forget C).Linear R where

/-- The centre of a monoidal `R`-linear category is monoidal `R`-linear. -/
instance instMonoidalLinear : MonoidalLinear R (Center C) where

end Linear

section Biproduct

variable [Preadditive C] [MonoidalPreadditive C] [HasFiniteBiproducts C] {J : Type} [Finite J]
  (F : J → Center C)

/-- The biproduct bicone of a finite family `F` of objects of the centre: its cone point is the
biproduct of the underlying objects with the half-braiding `HalfBraiding.biproduct`, and its
projections and inclusions are those of the biproduct in `C`. -/
@[expose]
noncomputable def biproductBicone : Bicone F where
  pt := ⟨⨁ fun j ↦ (F j).1, HalfBraiding.biproduct _ fun j ↦ (F j).2⟩
  π j :=
    { f := biproduct.π (fun j ↦ (F j).1) j
      comm U :=
        (HalfBraiding.biproduct_β_hom_comp_biproduct_π _ (fun j ↦ (F j).2) U j).symm }
  ι j :=
    { f := biproduct.ι (fun j ↦ (F j).1) j
      comm U :=
        HalfBraiding.biproduct_ι_comp_biproduct_β_hom _ (fun j ↦ (F j).2) U j }
  ι_π j j' := by
    split_ifs with h
    · subst h
      ext
      exact biproduct.ι_π_self _ j
    · ext
      exact biproduct.ι_π_ne _ h

@[simp]
theorem biproductBicone_pt_fst : (biproductBicone F).pt.1 = ⨁ fun j ↦ (F j).1 :=
  (rfl)

@[simp]
theorem biproductBicone_π_f (j : J) :
    ((biproductBicone F).π j).f = biproduct.π (fun j ↦ (F j).1) j :=
  rfl

@[simp]
theorem biproductBicone_ι_f (j : J) :
    ((biproductBicone F).ι j).f = biproduct.ι (fun j ↦ (F j).1) j :=
  rfl

/-- The bicone `biproductBicone F` is a biproduct in the centre. -/
noncomputable def isBilimitBiproductBicone : (biproductBicone F).IsBilimit :=
  haveI := Fintype.ofFinite J
  isBilimitOfTotal _ <| by
    ext
    simp only [sum_f, comp_f, id_f, biproductBicone_π_f, biproductBicone_ι_f]
    exact biproduct.total

instance : HasBiproduct F :=
  HasBiproduct.mk ⟨_, isBilimitBiproductBicone F⟩

instance : HasBiproductsOfShape J (Center C) where
  has_biproduct _ := inferInstance

instance : HasFiniteBiproducts (Center C) where
  out _ := inferInstance

end Biproduct

end Center

end CategoryTheory
