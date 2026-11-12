/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Creates
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Monoidal.Center
public import TauCeti.CategoryTheory.Monoidal.Limits

/-!
# Limits and colimits in the Drinfeld centre

Let `K : J ⥤ Center C` be a diagram in the Drinfeld centre of a monoidal category `C`, and let `c`
be a limit cone of the underlying diagram `K ⋙ Center.forget C` in `C`. If tensoring on either
side with any `U : C` preserves this limit, then the cone point `c.pt` carries a half-braiding
making the legs of `c` morphisms of the centre: its component at `U` is the isomorphism
`c.pt ⊗ U ≅ U ⊗ c.pt` of limit points induced by the half-braidings of the objects `K.obj j`.
The resulting cone in the centre is a limit cone, so the forgetful functor `Center.forget C`
creates such limits. The dual statements hold for colimits. The half-braiding is built for any
diagram `F : J ⥤ C` of objects carrying half-braidings compatible with the morphisms of the
diagram, not only for diagrams in the centre.

Since `Center.forget C` creates the limits and colimits that tensoring preserves, the centre has
them and `Center.forget C` preserves them. In particular, when tensoring with every object of `C`
is exact on both sides, as in a rigid category, the centre has the finite limits and colimits of
`C` and they are computed in `C`. This is how the centre of a rigid abelian monoidal category is
shown to be abelian.

## Main declarations

* `CategoryTheory.HalfBraiding.ofIsLimit`: the half-braiding on a limit of objects carrying
  compatible half-braidings, characterized by
  `CategoryTheory.HalfBraiding.ofIsLimit_β_hom_whiskerLeft_π`; lifts of cones of intertwining
  morphisms intertwine, by `CategoryTheory.HalfBraiding.lift_whiskerRight_ofIsLimit_β_hom`;
* `CategoryTheory.Center.coneOfIsLimit` and `CategoryTheory.Center.isLimitConeOfIsLimit`: the
  lifted cone in the centre, which is a limit cone;
* `CategoryTheory.Center.forgetCreatesLimit`: `Center.forget C` creates the limits which tensoring
  on both sides preserves;
* `CategoryTheory.HalfBraiding.ofIsColimit`, `CategoryTheory.Center.coconeOfIsColimit`,
  `CategoryTheory.Center.isColimitCoconeOfIsColimit` and
  `CategoryTheory.Center.forgetCreatesColimit`: the corresponding statements for colimits;
* `CategoryTheory.Center.hasFiniteLimits` and `CategoryTheory.Center.preservesFiniteLimits_forget`,
  and their duals for colimits: when tensoring with every object preserves finite limits, the
  centre has finite limits and they are computed in `C`.

## References

* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §7.13
-/

public section

universe w' w v u

namespace CategoryTheory

open MonoidalCategory Limits

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {J : Type w} [Category.{w'} J]

namespace HalfBraiding

section Limit

variable {F : J ⥤ C} (b : ∀ j, HalfBraiding (F.obj j))
  (hb : ∀ ⦃i j : J⦄ (f : i ⟶ j) (U : C),
    F.map f ▷ U ≫ ((b j).β U).hom = ((b i).β U).hom ≫ U ◁ F.map f)
  {c : Cone F} (hc : IsLimit c)
  [∀ U : C, PreservesLimit F (tensorLeft U)] [∀ U : C, PreservesLimit F (tensorRight U)]

/-- The component at `U` of the half-braiding on a limit `c.pt` of objects `F.obj j` carrying
compatible half-braidings `b j`: the isomorphism of limit points `c.pt ⊗ U ≅ U ⊗ c.pt` induced by
the half-braidings `b j`. -/
noncomputable def ofIsLimitβ (U : C) : c.pt ⊗ U ≅ U ⊗ c.pt :=
  IsLimit.conePointsIsoOfNatIso (isLimitOfPreserves (tensorRight U) hc)
    (isLimitOfPreserves (tensorLeft U) hc)
    (NatIso.ofComponents (fun j ↦ (b j).β U) (fun f ↦ hb f U))

/-- Composed with the leg at `j`, the component `ofIsLimitβ b hb hc U` is the half-braiding
`b j`. -/
@[reassoc (attr := simp)]
theorem ofIsLimitβ_hom_whiskerLeft_π (U : C) (j : J) :
    (ofIsLimitβ b hb hc U).hom ≫ U ◁ c.π.app j = c.π.app j ▷ U ≫ ((b j).β U).hom :=
  IsLimit.conePointsIsoOfNatIso_hom_comp _ _ _ j

/-- The half-braiding on a limit `c.pt` of objects `F.obj j` carrying half-braidings `b j`
compatible with the morphisms of the diagram, when tensoring on either side preserves the limit.
Each leg `c.π.app j` intertwines it with `b j`. -/
noncomputable def ofIsLimit : HalfBraiding c.pt where
  β := ofIsLimitβ b hb hc
  -- After each leg, both sides become the monoidal axiom of `b j`: the leg is moved past the
  -- two half-braiding components using `ofIsLimitβ_hom_whiskerLeft_π`, and `monoidal` handles
  -- the associators and whiskerings in between.
  monoidal U U' := hc.hom_ext_whiskerLeft fun j ↦ by
    have h := ofIsLimitβ_hom_whiskerLeft_π b hb hc
    rw [h, HalfBraiding.monoidal]
    calc _ = (α_ _ _ _).inv ≫ (c.π.app j ▷ U ≫ ((b j).β U).hom) ▷ U' ≫ (α_ _ _ _).hom ≫
          U ◁ ((b j).β U').hom ≫ (α_ _ _ _).inv := by monoidal
      _ = (α_ _ _ _).inv ≫ (ofIsLimitβ b hb hc U).hom ▷ U' ≫ (α_ _ _ _).hom ≫
          U ◁ (c.π.app j ▷ U' ≫ ((b j).β U').hom) ≫ (α_ _ _ _).inv := by rw [← h]; monoidal
      _ = _ := by rw [← h]; monoidal
  -- After each leg, both sides become `c.π.app j ▷ U ≫ ((b j).β U).hom ≫ f ▷ F.obj j`, by
  -- exchanging the whiskerings and using naturality of `b j`.
  naturality {U U'} f := hc.hom_ext_whiskerLeft fun j ↦ by
    simp only [Category.assoc, ← whisker_exchange]
    simp only [ofIsLimitβ_hom_whiskerLeft_π, ofIsLimitβ_hom_whiskerLeft_π_assoc,
      whisker_exchange_assoc, HalfBraiding.naturality]

/-- Composed with the leg at `j`, the half-braiding of the limit is `b j`. -/
@[reassoc (attr := simp)]
theorem ofIsLimit_β_hom_whiskerLeft_π (U : C) (j : J) :
    ((ofIsLimit b hb hc).β U).hom ≫ U ◁ c.π.app j = c.π.app j ▷ U ≫ ((b j).β U).hom :=
  ofIsLimitβ_hom_whiskerLeft_π b hb hc U j

/-- The lift to `c.pt` of a cone `s` whose legs intertwine a half-braiding `bs` on `s.pt` with the
half-braidings `b j` intertwines `bs` with the half-braiding of the limit. -/
theorem lift_whiskerRight_ofIsLimit_β_hom (s : Cone F) (bs : HalfBraiding s.pt)
    (hs : ∀ j U, s.π.app j ▷ U ≫ ((b j).β U).hom = (bs.β U).hom ≫ U ◁ s.π.app j) (U : C) :
    hc.lift s ▷ U ≫ ((ofIsLimit b hb hc).β U).hom = (bs.β U).hom ≫ U ◁ hc.lift s :=
  hc.hom_ext_whiskerLeft fun j ↦ by
    simp [← comp_whiskerRight_assoc, ← whiskerLeft_comp, hs]

end Limit

section Colimit

variable {F : J ⥤ C} (b : ∀ j, HalfBraiding (F.obj j))
  (hb : ∀ ⦃i j : J⦄ (f : i ⟶ j) (U : C),
    F.map f ▷ U ≫ ((b j).β U).hom = ((b i).β U).hom ≫ U ◁ F.map f)
  {c : Cocone F} (hc : IsColimit c)
  [∀ U : C, PreservesColimit F (tensorLeft U)] [∀ U : C, PreservesColimit F (tensorRight U)]

/-- The component at `U` of the half-braiding on a colimit `c.pt` of objects `F.obj j` carrying
compatible half-braidings `b j`: the isomorphism of colimit points `c.pt ⊗ U ≅ U ⊗ c.pt` induced
by the half-braidings `b j`. -/
noncomputable def ofIsColimitβ (U : C) : c.pt ⊗ U ≅ U ⊗ c.pt :=
  IsColimit.coconePointsIsoOfNatIso (isColimitOfPreserves (tensorRight U) hc)
    (isColimitOfPreserves (tensorLeft U) hc)
    (NatIso.ofComponents (fun j ↦ (b j).β U) (fun f ↦ hb f U))

/-- Precomposed with the leg at `j`, the component `ofIsColimitβ b hb hc U` is the half-braiding
`b j`. -/
@[reassoc (attr := simp)]
theorem ι_whiskerRight_ofIsColimitβ_hom (U : C) (j : J) :
    c.ι.app j ▷ U ≫ (ofIsColimitβ b hb hc U).hom = ((b j).β U).hom ≫ U ◁ c.ι.app j :=
  IsColimit.comp_coconePointsIsoOfNatIso_hom (isColimitOfPreserves (tensorRight U) hc)
    (isColimitOfPreserves (tensorLeft U) hc) _ j

/-- The half-braiding on a colimit `c.pt` of objects `F.obj j` carrying half-braidings `b j`
compatible with the morphisms of the diagram, when tensoring on either side preserves the
colimit. Each leg `c.ι.app j` intertwines `b j` with it. -/
noncomputable def ofIsColimit : HalfBraiding c.pt where
  β := ofIsColimitβ b hb hc
  -- Before each leg, both sides become the monoidal axiom of `b j`: the leg is moved past the
  -- two half-braiding components using `ι_whiskerRight_ofIsColimitβ_hom`, and `monoidal`
  -- handles the associators and whiskerings in between.
  monoidal U U' := hc.hom_ext_whiskerRight fun j ↦ by
    have h := ι_whiskerRight_ofIsColimitβ_hom b hb hc
    rw [h, HalfBraiding.monoidal]
    calc _ = (α_ _ _ _).inv ≫ ((b j).β U).hom ▷ U' ≫ (α_ _ _ _).hom ≫
          U ◁ (((b j).β U').hom ≫ U' ◁ c.ι.app j) ≫ (α_ _ _ _).inv := by monoidal
      _ = (α_ _ _ _).inv ≫ (((b j).β U).hom ≫ U ◁ c.ι.app j) ▷ U' ≫ (α_ _ _ _).hom ≫
          U ◁ (ofIsColimitβ b hb hc U').hom ≫ (α_ _ _ _).inv := by rw [← h]; monoidal
      _ = _ := by rw [← h]; monoidal
  -- Before each leg, both sides become `((b j).β U).hom ≫ U ◁ c.ι.app j ≫ f ▷ _`, by exchanging
  -- the whiskerings and using naturality of `b j`. The leg `c.ι.app j` lands in
  -- `((Functor.const J).obj c.pt).obj j`, so the two sides agree only up to `rfl`.
  naturality {U U'} f := hc.hom_ext_whiskerRight fun j ↦ by
    dsimp only [Functor.const_obj_obj]
    simp only [← whisker_exchange, ← whisker_exchange_assoc, ι_whiskerRight_ofIsColimitβ_hom,
      ι_whiskerRight_ofIsColimitβ_hom_assoc, HalfBraiding.naturality_assoc]
    rfl

/-- Precomposed with the leg at `j`, the half-braiding of the colimit is `b j`. -/
@[reassoc (attr := simp)]
theorem ι_whiskerRight_ofIsColimit_β_hom (U : C) (j : J) :
    c.ι.app j ▷ U ≫ ((ofIsColimit b hb hc).β U).hom = ((b j).β U).hom ≫ U ◁ c.ι.app j :=
  ι_whiskerRight_ofIsColimitβ_hom b hb hc U j

/-- The descent from `c.pt` of a cocone `s` whose legs intertwine the half-braidings `b j` with a
half-braiding `bs` on `s.pt` intertwines the half-braiding of the colimit with `bs`. -/
theorem desc_whiskerRight_β_hom (s : Cocone F) (bs : HalfBraiding s.pt)
    (hs : ∀ j U, s.ι.app j ▷ U ≫ (bs.β U).hom = ((b j).β U).hom ≫ U ◁ s.ι.app j) (U : C) :
    hc.desc s ▷ U ≫ (bs.β U).hom = ((ofIsColimit b hb hc).β U).hom ≫ U ◁ hc.desc s :=
  hc.hom_ext_whiskerRight fun j ↦ by
    simp [← comp_whiskerRight_assoc, ← whiskerLeft_comp, hs]

end Colimit

end HalfBraiding

namespace Center

section Limit

variable {K : J ⥤ Center C} {c : Cone (K ⋙ forget C)} (hc : IsLimit c)
  [∀ U : C, PreservesLimit (K ⋙ forget C) (tensorLeft U)]
  [∀ U : C, PreservesLimit (K ⋙ forget C) (tensorRight U)]

/-- The lift to the centre of a limit cone `c` of the underlying diagram of `K : J ⥤ Center C`,
when tensoring on either side preserves that limit: its point is `c.pt` with the half-braiding
`HalfBraiding.ofIsLimit`, and its legs are those of `c`. -/
@[expose]
noncomputable def coneOfIsLimit : Cone K where
  pt := ⟨c.pt, HalfBraiding.ofIsLimit (F := K ⋙ forget C) (fun j ↦ (K.obj j).2)
    (fun _ _ f U ↦ (K.map f).comm U) hc⟩
  π :=
    { app j :=
        { f := c.π.app j
          comm U := (HalfBraiding.ofIsLimit_β_hom_whiskerLeft_π (F := K ⋙ forget C)
            (fun j ↦ (K.obj j).2) (fun _ _ f U ↦ (K.map f).comm U) hc U j).symm }
      naturality _ _ f := ext _ _ ((Category.id_comp _).trans (c.w f).symm) }

/-- The underlying object of the point of the lifted cone is `c.pt`. -/
@[simp]
theorem coneOfIsLimit_pt_fst : (coneOfIsLimit hc).pt.1 = c.pt :=
  rfl

/-- The half-braiding of the point of the lifted cone is `HalfBraiding.ofIsLimit`. -/
@[simp]
theorem coneOfIsLimit_pt_snd :
    (coneOfIsLimit hc).pt.2 = HalfBraiding.ofIsLimit (F := K ⋙ forget C) (fun j ↦ (K.obj j).2)
      (fun _ _ f U ↦ (K.map f).comm U) hc :=
  rfl

/-- The legs of the lifted cone are those of `c`. -/
@[simp]
theorem coneOfIsLimit_π_app_f (j : J) : ((coneOfIsLimit hc).π.app j).f = c.π.app j :=
  rfl

/-- Forgetting the half-braiding of the lifted cone recovers `c`. -/
noncomputable def forgetMapConeOfIsLimitIso : (forget C).mapCone (coneOfIsLimit hc) ≅ c :=
  Cone.ext (Iso.refl _) fun _ ↦ (Category.id_comp _).symm

/-- The lift `coneOfIsLimit hc` of a limit cone is a limit cone in the centre. -/
noncomputable def isLimitConeOfIsLimit : IsLimit (coneOfIsLimit hc) where
  lift s :=
    { f := hc.lift ((forget C).mapCone s)
      comm := HalfBraiding.lift_whiskerRight_ofIsLimit_β_hom (F := K ⋙ forget C)
        (fun j ↦ (K.obj j).2) (fun _ _ f U ↦ (K.map f).comm U) hc ((forget C).mapCone s) s.pt.2
        fun j U ↦ (s.π.app j).comm U }
  fac s j := ext _ _ (hc.fac ((forget C).mapCone s) j)
  uniq s m hm := ext _ _ (hc.uniq ((forget C).mapCone s) m.f fun j ↦ congr_arg Hom.f (hm j))

/-- The forgetful functor from the centre creates the limits which tensoring on either side
preserves. -/
noncomputable instance forgetCreatesLimit : CreatesLimit K (forget C) :=
  createsLimitOfReflectsIso fun _ hc ↦
    { liftedCone := coneOfIsLimit hc
      validLift := forgetMapConeOfIsLimitIso hc
      makesLimit := isLimitConeOfIsLimit hc }

end Limit

section Colimit

variable {K : J ⥤ Center C} {c : Cocone (K ⋙ forget C)} (hc : IsColimit c)
  [∀ U : C, PreservesColimit (K ⋙ forget C) (tensorLeft U)]
  [∀ U : C, PreservesColimit (K ⋙ forget C) (tensorRight U)]

/-- The lift to the centre of a colimit cocone `c` of the underlying diagram of
`K : J ⥤ Center C`, when tensoring on either side preserves that colimit: its point is `c.pt`
with the half-braiding `HalfBraiding.ofIsColimit`, and its legs are those of `c`. -/
@[expose]
noncomputable def coconeOfIsColimit : Cocone K where
  pt := ⟨c.pt, HalfBraiding.ofIsColimit (F := K ⋙ forget C) (fun j ↦ (K.obj j).2)
    (fun _ _ f U ↦ (K.map f).comm U) hc⟩
  ι :=
    { app j :=
        { f := c.ι.app j
          comm U := HalfBraiding.ι_whiskerRight_ofIsColimit_β_hom (F := K ⋙ forget C)
            (fun j ↦ (K.obj j).2) (fun _ _ f U ↦ (K.map f).comm U) hc U j }
      naturality _ _ f := ext _ _ ((c.w f).trans (Category.comp_id _).symm) }

/-- The underlying object of the point of the lifted cocone is `c.pt`. -/
@[simp]
theorem coconeOfIsColimit_pt_fst : (coconeOfIsColimit hc).pt.1 = c.pt :=
  rfl

/-- The half-braiding of the point of the lifted cocone is `HalfBraiding.ofIsColimit`. -/
@[simp]
theorem coconeOfIsColimit_pt_snd :
    (coconeOfIsColimit hc).pt.2 = HalfBraiding.ofIsColimit (F := K ⋙ forget C)
      (fun j ↦ (K.obj j).2) (fun _ _ f U ↦ (K.map f).comm U) hc :=
  rfl

/-- The legs of the lifted cocone are those of `c`. -/
@[simp]
theorem coconeOfIsColimit_ι_app_f (j : J) : ((coconeOfIsColimit hc).ι.app j).f = c.ι.app j :=
  rfl

/-- Forgetting the half-braiding of the lifted cocone recovers `c`. -/
noncomputable def forgetMapCoconeOfIsColimitIso :
    (forget C).mapCocone (coconeOfIsColimit hc) ≅ c :=
  Cocone.ext (Iso.refl _) fun _ ↦ Category.comp_id _

/-- The lift `coconeOfIsColimit hc` of a colimit cocone is a colimit cocone in the centre. -/
noncomputable def isColimitCoconeOfIsColimit : IsColimit (coconeOfIsColimit hc) where
  desc s :=
    { f := hc.desc ((forget C).mapCocone s)
      comm := HalfBraiding.desc_whiskerRight_β_hom (F := K ⋙ forget C)
        (fun j ↦ (K.obj j).2) (fun _ _ f U ↦ (K.map f).comm U) hc ((forget C).mapCocone s) s.pt.2
        fun j U ↦ (s.ι.app j).comm U }
  fac s j := ext _ _ (hc.fac ((forget C).mapCocone s) j)
  uniq s m hm := ext _ _ (hc.uniq ((forget C).mapCocone s) m.f fun j ↦ congr_arg Hom.f (hm j))

/-- The forgetful functor from the centre creates the colimits which tensoring on either side
preserves. -/
noncomputable instance forgetCreatesColimit : CreatesColimit K (forget C) :=
  createsColimitOfReflectsIso fun _ hc ↦
    { liftedCocone := coconeOfIsColimit hc
      validLift := forgetMapCoconeOfIsColimitIso hc
      makesColimit := isColimitCoconeOfIsColimit hc }

end Colimit

section Shape

variable (J)

/-- The forgetful functor from the centre creates the limits of shape `J` when tensoring on
either side with every object preserves them. -/
noncomputable instance forgetCreatesLimitsOfShape
    [∀ U : C, PreservesLimitsOfShape J (tensorLeft U)]
    [∀ U : C, PreservesLimitsOfShape J (tensorRight U)] :
    CreatesLimitsOfShape J (forget C) where

/-- The forgetful functor from the centre creates the colimits of shape `J` when tensoring on
either side with every object preserves them. -/
noncomputable instance forgetCreatesColimitsOfShape
    [∀ U : C, PreservesColimitsOfShape J (tensorLeft U)]
    [∀ U : C, PreservesColimitsOfShape J (tensorRight U)] :
    CreatesColimitsOfShape J (forget C) where

/-- If `C` has limits of shape `J` and tensoring on either side with any object preserves them,
then so does the centre. -/
instance hasLimitsOfShape [HasLimitsOfShape J C]
    [∀ U : C, PreservesLimitsOfShape J (tensorLeft U)]
    [∀ U : C, PreservesLimitsOfShape J (tensorRight U)] : HasLimitsOfShape J (Center C) :=
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (forget C)

/-- If `C` has colimits of shape `J` and tensoring on either side with any object preserves them,
then so does the centre. -/
instance hasColimitsOfShape [HasColimitsOfShape J C]
    [∀ U : C, PreservesColimitsOfShape J (tensorLeft U)]
    [∀ U : C, PreservesColimitsOfShape J (tensorRight U)] : HasColimitsOfShape J (Center C) :=
  hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape (forget C)

end Shape

section Finite

variable [∀ U : C, PreservesFiniteLimits (tensorLeft U)]
  [∀ U : C, PreservesFiniteLimits (tensorRight U)]

/-- If `C` has finite limits and tensoring on either side with any object preserves them, then
the centre has finite limits. -/
instance hasFiniteLimits [HasFiniteLimits C] : HasFiniteLimits (Center C) :=
  ⟨fun _ _ _ ↦ inferInstance⟩

/-- If `C` has finite limits and tensoring on either side with any object preserves them, then
the forgetful functor from the centre preserves finite limits. -/
instance preservesFiniteLimits_forget [HasFiniteLimits C] : PreservesFiniteLimits (forget C) :=
  ⟨fun _ _ _ ↦ inferInstance⟩

end Finite

section FiniteColimits

variable [∀ U : C, PreservesFiniteColimits (tensorLeft U)]
  [∀ U : C, PreservesFiniteColimits (tensorRight U)]

/-- If `C` has finite colimits and tensoring on either side with any object preserves them, then
the centre has finite colimits. -/
instance hasFiniteColimits [HasFiniteColimits C] : HasFiniteColimits (Center C) :=
  ⟨fun _ _ _ ↦ inferInstance⟩

/-- If `C` has finite colimits and tensoring on either side with any object preserves them, then
the forgetful functor from the centre preserves finite colimits. -/
instance preservesFiniteColimits_forget [HasFiniteColimits C] :
    PreservesFiniteColimits (forget C) :=
  ⟨fun _ _ _ ↦ inferInstance⟩

end FiniteColimits

end Center

end CategoryTheory
