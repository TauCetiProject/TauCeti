/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Biproduct
public import TauCeti.CategoryTheory.Monoidal.Center.Relative.Basic
public import TauCeti.CategoryTheory.Monoidal.Preadditive

/-!
# The centre of a lax monoidal functor into a preadditive monoidal category

Let `F : C ⥤ D` be a lax monoidal functor. This file equips the centre
`Functor.RelativeCenter F` of `F` with the additive structure induced from `D`, as
`CategoryTheory.Center` is equipped with that of `C` in
`TauCeti.CategoryTheory.Monoidal.Center.Preadditive`.

A morphism `X ⟶ Y` of the centre of `F` is a morphism `f : X.obj ⟶ Y.obj` of `D` satisfying
`f ▷ F.obj U ≫ β_Y U = β_X U ≫ F.obj U ◁ f` for every `U`. When the whiskerings of `D` are additive
(`MonoidalPreadditive D`), or `R`-linear (`MonoidalLinear R D`), this condition is preserved by
sums, negatives and scalar multiples, so the centre of `F` is preadditive, or `R`-linear, with the
operations computed on underlying morphisms. The forgetful functor is then additive and `R`-linear,
and the centre of `F` is again monoidal preadditive, or monoidal `R`-linear.

Finite biproducts are also computed in `D`. If each summand `f j` of a finite biproduct `⨁ f`
carries a half-braiding `b j` relative to `F`, then `⨁ f` carries the half-braiding
`RelativeHalfBraiding.biproduct f b`, which restricts to `b j` on the summand `f j`: its component
at `U` distributes `(⨁ f) ⊗ F.obj U` over the summands, applies the half-braidings `b j`, and
collects the result into `F.obj U ⊗ ⨁ f` again. The projections and inclusions of the biproduct
are then morphisms of the centre of `F`, and form a biproduct there.

None of this needs `F` to be additive or linear: only the target category enters.

## Main declarations

* `CategoryTheory.Functor.RelativeCenter.instPreadditive` and
  `CategoryTheory.Functor.RelativeCenter.instLinear`: the centre of a lax monoidal functor into a
  monoidal preadditive (resp. `R`-linear) category is preadditive (resp. `R`-linear);
* `CategoryTheory.Functor.RelativeCenter.instAdditiveForget` and
  `CategoryTheory.Functor.RelativeCenter.instLinearForget`: the forgetful functor is additive and
  linear;
* `CategoryTheory.Functor.RelativeCenter.instMonoidalPreadditive` and
  `CategoryTheory.Functor.RelativeCenter.instMonoidalLinear`: the centre is monoidal preadditive
  (resp. monoidal `R`-linear);
* `CategoryTheory.Functor.RelativeHalfBraiding.biproduct`: the half-braiding relative to `F` on a
  finite biproduct of objects with such half-braidings;
* `CategoryTheory.Functor.RelativeCenter.biproductBicone` and
  `CategoryTheory.Functor.RelativeCenter.isBilimitBiproductBicone`: the biproduct of a finite family
  of objects of the centre, giving the instance `HasFiniteBiproducts F.RelativeCenter`.

## References

* A. M. Gainutdinov, J. Haferkamp, C. Schweigert, *Davydov–Yetter cohomology, comonads and
  Ocneanu rigidity*, Adv. Math. 414 (2023), arXiv:1910.06094, Section 3.2, Definitions 3.1 and
  3.2.
-/

public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open MonoidalCategory Limits Functor.LaxMonoidal

namespace Functor

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
  {F : C ⥤ D} [F.LaxMonoidal]

namespace RelativeHalfBraiding

variable [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D] {J : Type} [Finite J]

/-- The half-braiding relative to `F` on a finite biproduct `⨁ f` of objects carrying
half-braidings `b j` relative to `F`: its component `(biproduct f b).β U` distributes
`(⨁ f) ⊗ F.obj U` over the summands, applies the half-braidings `(b j).β U`, and collects
`F.obj U ⊗ ⨁ f` again. -/
noncomputable def biproduct (f : J → D) (b : ∀ j, F.RelativeHalfBraiding (f j)) :
    F.RelativeHalfBraiding (⨁ f) where
  β U := biproductCommIso f (F.obj U) fun j ↦ (b j).β U
  monoidal U U' := by
    refine rightDistributor_ext_left fun j ↦ ?_
    calc
      _ = (f j ◁ μ F U U' ≫ ((b j).β (U ⊗ U')).hom) ≫ F.obj (U ⊗ U') ◁ biproduct.ι f j := by
        rw [← whisker_exchange_assoc, biproduct_ι_comp_biproductCommIso_hom, Category.assoc]
      _ = 𝟙 _ ⊗≫ ((b j).β U).hom ▷ F.obj U' ⊗≫ F.obj U ◁ ((b j).β U').hom ⊗≫
            (μ F U U' ▷ f j ≫ F.obj (U ⊗ U') ◁ biproduct.ι f j) := by
        rw [(b j).monoidal]; monoidal
      _ = 𝟙 _ ⊗≫ ((b j).β U).hom ▷ F.obj U' ⊗≫
            F.obj U ◁ (((b j).β U').hom ≫ F.obj U' ◁ biproduct.ι f j) ⊗≫ μ F U U' ▷ ⨁ f := by
        rw [← whisker_exchange]; monoidal
      _ = 𝟙 _ ⊗≫ (((b j).β U).hom ≫ F.obj U ◁ biproduct.ι f j) ▷ F.obj U' ⊗≫
            F.obj U ◁ (biproductCommIso f (F.obj U') fun j ↦ (b j).β U').hom ⊗≫
            μ F U U' ▷ ⨁ f := by
        rw [← biproduct_ι_comp_biproductCommIso_hom f _ (fun j ↦ (b j).β U') j]; monoidal
      _ = _ := by
        rw [← biproduct_ι_comp_biproductCommIso_hom f _ (fun j ↦ (b j).β U) j]; monoidal
  unit := by
    refine rightDistributor_ext_left fun j ↦ ?_
    rw [← whisker_exchange_assoc, biproduct_ι_comp_biproductCommIso_hom, (b j).unit_assoc]
    simp [← whisker_exchange]
  naturality g := by
    refine rightDistributor_ext_left fun j ↦ ?_
    rw [← whisker_exchange_assoc]
    simp [whisker_exchange, RelativeHalfBraiding.naturality_assoc]

/-- On the summand `f j`, the half-braiding of `⨁ f` is that of `f j`. -/
@[reassoc (attr := simp)]
theorem biproduct_ι_comp_biproduct_β_hom (f : J → D) (b : ∀ j, F.RelativeHalfBraiding (f j))
    (U : C) (j : J) :
    biproduct.ι f j ▷ F.obj U ≫ ((RelativeHalfBraiding.biproduct f b).β U).hom =
      ((b j).β U).hom ≫ F.obj U ◁ biproduct.ι f j :=
  biproduct_ι_comp_biproductCommIso_hom f _ _ j

/-- Projected to the summand `f j`, the half-braiding of `⨁ f` is that of `f j`. -/
@[reassoc (attr := simp)]
theorem biproduct_β_hom_comp_biproduct_π (f : J → D) (b : ∀ j, F.RelativeHalfBraiding (f j))
    (U : C) (j : J) :
    ((RelativeHalfBraiding.biproduct f b).β U).hom ≫ F.obj U ◁ biproduct.π f j =
      biproduct.π f j ▷ F.obj U ≫ ((b j).β U).hom :=
  biproductCommIso_hom_comp_biproduct_π f _ _ j

end RelativeHalfBraiding

namespace RelativeCenter

section Preadditive

variable [Preadditive D] [MonoidalPreadditive D] {X Y : F.RelativeCenter}

instance instZeroHom : Zero (X ⟶ Y) where
  zero := { f := 0 }

instance instAddHom : Add (X ⟶ Y) where
  add f g := { f := f.f + g.f }

instance instNegHom : Neg (X ⟶ Y) where
  neg f := { f := -f.f }

instance instSubHom : Sub (X ⟶ Y) where
  sub f g := { f := f.f - g.f }

instance instSMulNatHom : SMul ℕ (X ⟶ Y) where
  smul n f := { f := n • f.f }

instance instSMulIntHom : SMul ℤ (X ⟶ Y) where
  smul n f := { f := n • f.f }

@[simp] theorem zero_f : (0 : X ⟶ Y).f = 0 := rfl
@[simp] theorem add_f (f g : X ⟶ Y) : (f + g).f = f.f + g.f := rfl
@[simp] theorem neg_f (f : X ⟶ Y) : (-f).f = -f.f := rfl
@[simp] theorem sub_f (f g : X ⟶ Y) : (f - g).f = f.f - g.f := rfl
@[simp] theorem nsmul_f (n : ℕ) (f : X ⟶ Y) : (n • f).f = n • f.f := rfl
@[simp] theorem zsmul_f (n : ℤ) (f : X ⟶ Y) : (n • f).f = n • f.f := rfl

/-- The centre of a lax monoidal functor into a monoidal preadditive category is preadditive, with
the additive structure on morphisms computed on underlying morphisms. -/
instance instPreadditive : Preadditive F.RelativeCenter where
  homGroup _ _ :=
    (forget F).map_injective.addCommGroup _ zero_f add_f neg_f sub_f (fun _ _ ↦ rfl)
      (fun _ _ ↦ rfl)
  add_comp _ _ _ _ _ _ := by ext; exact Preadditive.add_comp _ _ _ _ _ _
  comp_add _ _ _ _ _ _ := by ext; exact Preadditive.comp_add _ _ _ _ _ _

/-- The forgetful functor from the centre of `F` is additive. -/
instance instAdditiveForget : (forget F).Additive where

@[simp]
theorem sum_f {ι : Type*} (s : Finset ι) (f : ι → (X ⟶ Y)) :
    (∑ i ∈ s, f i).f = ∑ i ∈ s, (f i).f :=
  (forget F).map_sum f s

/-- The centre of a lax monoidal functor into a monoidal preadditive category is monoidal
preadditive. -/
instance instMonoidalPreadditive : MonoidalPreadditive F.RelativeCenter :=
  monoidalPreadditive_of_faithful (forget F)

end Preadditive

section Linear

variable [Preadditive D] [MonoidalPreadditive D] {R : Type*} [Semiring R]
  [CategoryTheory.Linear R D] [MonoidalLinear R D]

/-- The centre of a lax monoidal functor into a monoidal `R`-linear category is `R`-linear, with
scalar multiplication computed on underlying morphisms. -/
instance instLinear : CategoryTheory.Linear R F.RelativeCenter where
  homModule X Y :=
    letI : SMul R (X ⟶ Y) := ⟨fun r f ↦ { f := r • f.f }⟩
    Function.Injective.module R (forget F).mapAddHom (forget F).map_injective fun _ _ ↦ rfl
  smul_comp _ _ _ _ _ _ := by ext; exact CategoryTheory.Linear.smul_comp _ _ _ _ _ _
  comp_smul _ _ _ _ _ _ := by ext; exact CategoryTheory.Linear.comp_smul _ _ _ _ _ _

@[simp]
theorem smul_f {X Y : F.RelativeCenter} (r : R) (f : X ⟶ Y) : (r • f).f = r • f.f :=
  rfl

/-- The forgetful functor from the centre of `F` is `R`-linear. -/
instance instLinearForget : (forget F).Linear R where

/-- The centre of a lax monoidal functor into a monoidal `R`-linear category is monoidal
`R`-linear. -/
instance instMonoidalLinear : MonoidalLinear R F.RelativeCenter :=
  MonoidalLinear.ofFaithful R (forget F)

end Linear

section Biproduct

variable [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D] {J : Type} [Finite J]
  (P : J → F.RelativeCenter)

/-- The biproduct bicone of a finite family `P` of objects of the centre of `F`: its cone point is
the biproduct of the underlying objects with the half-braiding `RelativeHalfBraiding.biproduct`,
and its projections and inclusions are those of the biproduct in `D`. -/
@[expose]
noncomputable def biproductBicone : Bicone P where
  pt := ⟨⨁ fun j ↦ (P j).obj, RelativeHalfBraiding.biproduct _ fun j ↦ (P j).halfBraiding⟩
  π j :=
    { f := biproduct.π (fun j ↦ (P j).obj) j
      comm U := (RelativeHalfBraiding.biproduct_β_hom_comp_biproduct_π _
        (fun j ↦ (P j).halfBraiding) U j).symm }
  ι j :=
    { f := biproduct.ι (fun j ↦ (P j).obj) j
      comm U := RelativeHalfBraiding.biproduct_ι_comp_biproduct_β_hom _
        (fun j ↦ (P j).halfBraiding) U j }
  ι_π j j' := by
    split_ifs with h
    · subst h
      ext
      exact biproduct.ι_π_self _ j
    · ext
      exact biproduct.ι_π_ne _ h

@[simp]
theorem biproductBicone_pt_obj : (biproductBicone P).pt.obj = ⨁ fun j ↦ (P j).obj :=
  rfl

@[simp]
theorem biproductBicone_pt_halfBraiding :
    (biproductBicone P).pt.halfBraiding =
      RelativeHalfBraiding.biproduct _ fun j ↦ (P j).halfBraiding :=
  rfl

@[simp]
theorem biproductBicone_π_f (j : J) :
    ((biproductBicone P).π j).f = biproduct.π (fun j ↦ (P j).obj) j :=
  rfl

@[simp]
theorem biproductBicone_ι_f (j : J) :
    ((biproductBicone P).ι j).f = biproduct.ι (fun j ↦ (P j).obj) j :=
  rfl

/-- The bicone `biproductBicone P` is a biproduct in the centre of `F`. -/
noncomputable def isBilimitBiproductBicone : (biproductBicone P).IsBilimit :=
  haveI := Fintype.ofFinite J
  isBilimitOfTotal _ <| by
    ext
    simp only [sum_f, comp_f, id_f, biproductBicone_π_f, biproductBicone_ι_f]
    exact biproduct.total

instance : HasBiproduct P :=
  HasBiproduct.mk ⟨_, isBilimitBiproductBicone P⟩

instance : HasBiproductsOfShape J F.RelativeCenter where
  has_biproduct _ := inferInstance

/-- The centre of a lax monoidal functor into a monoidal preadditive category with finite
biproducts has finite biproducts, computed in the target. -/
instance : HasFiniteBiproducts F.RelativeCenter where
  out _ := inferInstance

end Biproduct

end RelativeCenter

end Functor

end CategoryTheory
