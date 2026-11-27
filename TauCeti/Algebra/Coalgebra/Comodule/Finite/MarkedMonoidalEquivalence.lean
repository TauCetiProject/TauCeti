/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Finite.Symmetric
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

/-!
# Marked monoidal equivalences with finite comodules

A comparison with a strong monoidal fibre functor specifies the underlying tensor and unit
comparisons of a functor into finite comodules. Tensor colinearity is the substantive
hypothesis. Essential surjectivity then forces the marked unit comparison to be colinear.
This permits lifting the monoidal structure while retaining the given fibre comparison.
The construction works over a commutative semiring. For a commutative bialgebra it also
preserves a braided fibre marking. Scalar markings of the identity compute the effect of
rescaling the chosen fibre comparison.

The tensor lift uses `TauCeti.FGComoduleCat.isoOfLinearEquiv`; the coherence proofs use
Mathlib's `Functor.Monoidal.transport` through the faithful forgetful functor. Applied to an
equivalence, `markedMonoidal` combines with `Equivalence.inverseMonoidal` to make both
functors monoidal. The argument follows Deligne–Milne, *Tannakian categories*, Proposition 2.16.
-/

public section

attribute [local instance] TauCeti.Comodule.tensor

open CategoryTheory MonoidalCategory
open TauCeti TauCeti.FGComoduleCat
open scoped TensorProduct

namespace CategoryTheory.Functor

universe u v w w'

variable {k : Type u} [CommSemiring k] {B : Type v} [Semiring B] [Bialgebra k B]
variable {C : Type w} [Category.{w'} C] [MonoidalCategory C]
variable (E : C ⥤ FGComoduleCat.{u, v, u} k B)
variable (ω : C ⥤ SemimoduleCat.{u} k) [ω.Monoidal]

variable (θ : E ⋙ (forget₂ (FGComoduleCat.{u, v, u} k B) (SemimoduleCat.{u} k)) ≅ ω)

/-- The tensor comparison specified by a marking of the underlying fibre functor. -/
noncomputable def markedTensorIso (X Y : C) :
    (forget₂ (FGComoduleCat.{u, v, u} k B) (SemimoduleCat.{u} k)).obj (E.obj X ⊗ E.obj Y)
    ≅ (forget₂ (FGComoduleCat.{u, v, u} k B) (SemimoduleCat.{u} k)).obj (E.obj (X ⊗ Y)) :=
  (Functor.Monoidal.μIso (forget₂ (FGComoduleCat.{u, v, u} k B) (SemimoduleCat.{u} k)) (E.obj X)
    (E.obj Y)).symm ≪≫
    tensorIso (θ.app X) (θ.app Y) ≪≫ Functor.Monoidal.μIso ω X Y ≪≫ (θ.app (X ⊗ Y)).symm

/-- The marked tensor map is the fibre tensorator conjugated by the marking. -/
theorem markedTensorIso_hom (X Y : C) :
    (markedTensorIso E ω θ X Y).hom =
      Functor.OplaxMonoidal.δ
          (forget₂ (FGComoduleCat.{u, v, u} k B) (SemimoduleCat.{u} k)) (E.obj X) (E.obj Y) ≫
        (θ.hom.app X ⊗ₘ θ.hom.app Y) ≫ Functor.LaxMonoidal.μ ω X Y ≫
          θ.inv.app (X ⊗ Y) :=
  (rfl)

/-- The unit comparison specified by the same marking. -/
noncomputable def markedUnitIso : (forget₂ (FGComoduleCat.{u, v, u} k B) (SemimoduleCat.{u} k)).obj
      (𝟙_ (FGComoduleCat.{u, v, u} k B)) ≅
    (forget₂ (FGComoduleCat.{u, v, u} k B) (SemimoduleCat.{u} k)).obj (E.obj (𝟙_ C)) :=
  (Functor.Monoidal.εIso (forget₂ (FGComoduleCat.{u, v, u} k B) (SemimoduleCat.{u} k))).symm
    ≪≫ Functor.Monoidal.εIso ω ≪≫ (θ.app (𝟙_ C)).symm

/-- The marked unit map is the fibre unit map followed by the inverse marking. -/
theorem markedUnitIso_hom :
    (markedUnitIso E ω θ).hom =
      Functor.OplaxMonoidal.η
          (forget₂ (FGComoduleCat.{u, v, u} k B) (SemimoduleCat.{u} k)) ≫
        Functor.LaxMonoidal.ε ω ≫ θ.inv.app (𝟙_ C) :=
  (rfl)

/-- Tensor colinearity for the comparisons prescribed by the marking. -/
def MarkedTensorColinear : Prop :=
  ∀ X Y : C,
    TensorProduct.map (markedTensorIso E ω θ X Y).hom.hom LinearMap.id ∘ₗ
        Comodule.coact (R := k) (C := B) (M := ↥(E.obj X) ⊗[k] ↥(E.obj Y)) =
      Comodule.coact (R := k) (C := B) (M := E.obj (X ⊗ Y)) ∘ₗ
        (markedTensorIso E ω θ X Y).hom.hom

/-- Construct or use tensor colinearity through the underlying coaction equation. -/
theorem markedTensorColinear_iff : MarkedTensorColinear E ω θ ↔
    ∀ X Y : C,
      TensorProduct.map (markedTensorIso E ω θ X Y).hom.hom LinearMap.id ∘ₗ
          Comodule.coact (R := k) (C := B) (M := ↥(E.obj X) ⊗[k] ↥(E.obj Y)) =
        Comodule.coact (R := k) (C := B) (M := E.obj (X ⊗ Y)) ∘ₗ
          (markedTensorIso E ω θ X Y).hom.hom :=
  Iff.rfl

variable (h : MarkedTensorColinear E ω θ)

/-- Lift the marked tensor comparison to a comodule isomorphism. -/
noncomputable def markedTensorComoduleIso (X Y : C) :
    E.obj X ⊗ E.obj Y ≅ E.obj (X ⊗ Y) :=
  isoOfLinearEquiv (markedTensorIso E ω θ X Y).toLinearEquivₛ (h X Y)

@[simp]
theorem markedTensorComoduleIso_hom_toLinearMap (X Y : C) :
    (markedTensorComoduleIso E ω θ h X Y).hom.hom.toLinearMap =
      (markedTensorIso E ω θ X Y).hom.hom :=
  (rfl)

/-- Forgetting the inverse tensor lift recovers the inverse marked comparison. -/
@[simp]
theorem markedTensorComoduleIso_inv_toLinearMap (X Y : C) :
    (markedTensorComoduleIso E ω θ h X Y).inv.hom.toLinearMap =
      (markedTensorIso E ω θ X Y).inv.hom :=
  (rfl)

-- The transport comparisons and the marked comparisons agree after the forgetful
-- functor's identity comparisons have been removed.
private theorem transport_μ_eq_markedTensorIso_hom (X Y : C) :
    letI := Functor.Monoidal.transport θ.symm
    Functor.LaxMonoidal.μ
      (E ⋙ (forget₂ (FGComoduleCat.{u, v, u} k B) (SemimoduleCat.{u} k))) X Y =
      (markedTensorIso E ω θ X Y).hom := by
  rw [Functor.Monoidal.transport_μ, markedTensorIso_hom, forget₂_semimoduleCat_δ]
  exact (Category.id_comp _).symm

private theorem transport_ε_eq_markedUnitIso_hom :
    letI := Functor.Monoidal.transport θ.symm
    Functor.LaxMonoidal.ε
      (E ⋙ (forget₂ (FGComoduleCat.{u, v, u} k B) (SemimoduleCat.{u} k))) =
      (markedUnitIso E ω θ).hom := by
  rw [Functor.Monoidal.transport_ε, markedUnitIso_hom, forget₂_semimoduleCat_η]
  exact (Category.id_comp _).symm

-- A preimage of the native tensor unit turns the left unit comparison into an isomorphism
-- from the image of the source unit to the native unit.
private noncomputable def unitCandidate (X : C) (e : E.obj X ≅ 𝟙_ _) :
    E.obj (𝟙_ C) ≅ 𝟙_ (FGComoduleCat.{u, v, u} k B) :=
  (ρ_ (E.obj (𝟙_ C))).symm ≪≫ tensorIso (Iso.refl _) e.symm ≪≫
    markedTensorComoduleIso E ω θ h (𝟙_ C) X ≪≫ E.mapIso (λ_ X) ≪≫ e

private theorem map_unitCandidate_hom (X : C) (e : E.obj X ≅ 𝟙_ _) :
    (forget₂ (FGComoduleCat.{u, v, u} k B) (SemimoduleCat.{u} k)).map
      (unitCandidate E ω θ h X e).hom = (markedUnitIso E ω θ).inv := by
  let : (E ⋙ (forget₂ (FGComoduleCat.{u, v, u} k B) (SemimoduleCat.{u} k))).Monoidal :=
    Functor.Monoidal.transport θ.symm
  apply (cancel_epi (markedUnitIso E ω θ).hom).mp
  rw [Iso.hom_inv_id]
  have hu := Functor.LaxMonoidal.tensorUnit_whiskerLeft_comp_leftUnitor_hom
    (E ⋙ (forget₂ (FGComoduleCat.{u, v, u} k B) (SemimoduleCat.{u} k)))
      ((forget₂ (FGComoduleCat.{u, v, u} k B) (SemimoduleCat.{u} k)).map e.inv)
  simp only [unitCandidate, Iso.trans_hom, Iso.symm_hom, tensorIso_hom, Iso.refl_hom,
    Functor.map_comp, Functor.mapIso_hom]
  simp only [Functor.Monoidal.map_rightUnitor_inv, Functor.Monoidal.map_tensor]
  -- Apply the monoidal map laws before forgetting to linear maps, so the categorical
  -- coherence maps remain visible. The existing linear-map API identifies the tensor lift.
  simp only [forget₂_semimoduleCat_map, ComoduleCat.forget₂_map,
    markedTensorComoduleIso_hom_toLinearMap,
    ← transport_μ_eq_markedTensorIso_hom E ω θ, ← transport_ε_eq_markedUnitIso_hom E ω θ]
  -- The induced tensor/unit objects have the same carriers as their semimodule counterparts.
  -- change removes the identity comparisons and their bundled-object wrappers together;
  -- the categorical rewrites below then use these definitionally equal objects.
  change Functor.LaxMonoidal.ε (E ⋙ (forget₂ (FGComoduleCat.{u, v, u} k B)
      (SemimoduleCat.{u} k))) ≫
      (ρ_ ((forget₂ (FGComoduleCat.{u, v, u} k B) (SemimoduleCat.{u} k)).obj
        (E.obj (𝟙_ C)))).inv ≫
      (𝟙 _ ⊗ₘ (forget₂ (FGComoduleCat.{u, v, u} k B) (SemimoduleCat.{u} k)).map e.inv) ≫
      Functor.LaxMonoidal.μ (E ⋙ (forget₂ (FGComoduleCat.{u, v, u} k B)
        (SemimoduleCat.{u} k))) (𝟙_ C) X ≫ _ ≫ _ = 𝟙 _
  -- Naturality moves the chosen preimage inverse past the right unitor; erw matches
  -- the native unit carrier with the semimodule tensor unit.
  erw [rightUnitor_inv_naturality_assoc]
  rw [← tensorHom_id, tensorHom_comp_tensorHom_assoc]
  -- The tensor-hom identities have definitionally equal bundled tensor sources.
  erw [Category.comp_id, Category.id_comp]
  -- Apply the transported left unit law and move the preimage map past the left unitor;
  -- their objects still use the induced tensor/unit wrappers.
  erw [← reassoc_of% hu, leftUnitor_naturality_assoc]
  -- Cancel the preimage isomorphism after identifying composite-functor object wrappers.
  erw [← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id]
  simp only [Category.comp_id]
  apply SemimoduleCat.hom_ext
  apply LinearMap.ext
  intro r
  -- On the base semiring, the remaining left/right unitors send r to r * 1.
  exact mul_one r

variable [E.EssSurj]

/-- The marked unit comparison is a comodule isomorphism; tensor colinearity and essential
surjectivity suffice, without an additional hypothesis on the unit coaction. -/
noncomputable def markedUnitComoduleIso : 𝟙_ (FGComoduleCat.{u, v, u} k B) ≅ E.obj (𝟙_ C) :=
  (unitCandidate E ω θ h (E.objPreimage (𝟙_ _)) (E.objObjPreimageIso (𝟙_ _))).symm

/-- Forgetting the lifted unit recovers the prescribed marking. -/
@[simp]
theorem markedUnitComoduleIso_hom_toLinearMap :
    (markedUnitComoduleIso E ω θ h).hom.hom.toLinearMap =
      (markedUnitIso E ω θ).hom.hom := by
  have hi : (forget₂ (FGComoduleCat.{u, v, u} k B) (SemimoduleCat.{u} k)).mapIso
      (unitCandidate E ω θ h (E.objPreimage (𝟙_ _)) (E.objObjPreimageIso (𝟙_ _))) =
      (markedUnitIso E ω θ).symm := Iso.ext
    (map_unitCandidate_hom E ω θ h _ _)
  exact congrArg (fun i => i.inv.hom) hi

/-- Forgetting the inverse unit lift recovers the inverse marked comparison. -/
@[simp]
theorem markedUnitComoduleIso_inv_toLinearMap :
    (markedUnitComoduleIso E ω θ h).inv.hom.toLinearMap =
      (markedUnitIso E ω θ).inv.hom :=
  congrArg (fun f => f.hom) (map_unitCandidate_hom E ω θ h _ _)

omit [E.EssSurj] in
private theorem markedTensor_natural_left {X Y : C} (f : X ⟶ Y) (Z : C) :
    E.map f ▷ E.obj Z ≫ (markedTensorComoduleIso E ω θ h Y Z).hom =
      (markedTensorComoduleIso E ω θ h X Z).hom ≫ E.map (f ▷ Z) := by
  let : (E ⋙ (forget₂ (FGComoduleCat.{u, v, u} k B) (SemimoduleCat.{u} k))).Monoidal :=
    Functor.Monoidal.transport θ.symm
  apply (forget₂ (FGComoduleCat.{u, v, u} k B) (SemimoduleCat.{u} k)).map_injective
  simp only [Functor.map_comp, Functor.Monoidal.map_whiskerRight]
  convert Functor.LaxMonoidal.μ_natural_left
    (E ⋙ (forget₂ (FGComoduleCat.{u, v, u} k B) (SemimoduleCat.{u} k))) f Z using 1 <;>
    rfl

omit [E.EssSurj] in
private theorem markedTensor_natural_right {X Y : C} (Z : C) (f : X ⟶ Y) :
    E.obj Z ◁ E.map f ≫ (markedTensorComoduleIso E ω θ h Z Y).hom =
      (markedTensorComoduleIso E ω θ h Z X).hom ≫ E.map (Z ◁ f) := by
  let : (E ⋙ (forget₂ (FGComoduleCat.{u, v, u} k B) (SemimoduleCat.{u} k))).Monoidal :=
    Functor.Monoidal.transport θ.symm
  apply (forget₂ (FGComoduleCat.{u, v, u} k B) (SemimoduleCat.{u} k)).map_injective
  simp only [Functor.map_comp, Functor.Monoidal.map_whiskerLeft]
  convert Functor.LaxMonoidal.μ_natural_right
    (E ⋙ (forget₂ (FGComoduleCat.{u, v, u} k B) (SemimoduleCat.{u} k))) Z f using 1 <;>
    rfl

omit [E.EssSurj] in
private theorem markedTensor_associativity (X Y Z : C) :
    (markedTensorComoduleIso E ω θ h X Y).hom ▷ E.obj Z ≫
        (markedTensorComoduleIso E ω θ h (X ⊗ Y) Z).hom ≫ E.map (α_ X Y Z).hom =
      (α_ (E.obj X) (E.obj Y) (E.obj Z)).hom ≫
        E.obj X ◁ (markedTensorComoduleIso E ω θ h Y Z).hom ≫
          (markedTensorComoduleIso E ω θ h X (Y ⊗ Z)).hom := by
  let : (E ⋙ (forget₂ (FGComoduleCat.{u, v, u} k B) (SemimoduleCat.{u} k))).Monoidal :=
    Functor.Monoidal.transport θ.symm
  apply (forget₂ (FGComoduleCat.{u, v, u} k B) (SemimoduleCat.{u} k)).map_injective
  simp only [Functor.map_comp, Functor.Monoidal.map_whiskerLeft,
    Functor.Monoidal.map_whiskerRight, Functor.Monoidal.map_associator]
  -- Transport gives the same tensor maps; the remaining heterogeneous equalities only
  -- compare the induced tensor objects with their underlying semimodule tensor products.
  -- Normalize those object wrappers before removing the identity comparisons.
  convert Functor.LaxMonoidal.associativity
    (E ⋙ (forget₂ (FGComoduleCat.{u, v, u} k B) (SemimoduleCat.{u} k))) X Y Z using 1 <;>
    first
    | rfl
    | apply heq_of_eq
      simp_all only [forget₂_semimoduleCat_δ, forget₂_semimoduleCat_μ,
        forget₂_semimoduleCat_obj, ComoduleCat.forget₂_obj,
        SemimoduleCat.of_coe, forget₂_semimoduleCat_map, ComoduleCat.forget₂_map,
        Functor.comp_obj]
      (repeat' first | erw [Category.id_comp] | erw [Category.comp_id] |
          erw [id_whiskerRight] | erw [MonoidalCategory.whiskerLeft_id])
      rfl

private theorem markedUnit_left_unitality (X : C) :
    (λ_ (E.obj X)).hom = (markedUnitComoduleIso E ω θ h).hom ▷ E.obj X ≫
      (markedTensorComoduleIso E ω θ h (𝟙_ C) X).hom ≫ E.map (λ_ X).hom := by
  let : (E ⋙ (forget₂ (FGComoduleCat.{u, v, u} k B) (SemimoduleCat.{u} k))).Monoidal :=
    Functor.Monoidal.transport θ.symm
  apply (forget₂ (FGComoduleCat.{u, v, u} k B) (SemimoduleCat.{u} k)).map_injective
  simp only [Functor.map_comp, Functor.Monoidal.map_whiskerRight,
    Functor.Monoidal.map_leftUnitor]
  simp only [forget₂_semimoduleCat_map, ComoduleCat.forget₂_map,
    markedUnitComoduleIso_hom_toLinearMap, markedTensorComoduleIso_hom_toLinearMap,
    SemimoduleCat.ofHom_hom]
  -- The source objects differ syntactically by forgetting the native unit and tensor.
  -- After normalizing these wrappers, the transported unit/tensor maps agree by definition;
  -- the remaining identity whiskering is removed with erw across those equal objects.
  convert Functor.LaxMonoidal.left_unitality
    (E ⋙ (forget₂ (FGComoduleCat.{u, v, u} k B) (SemimoduleCat.{u} k))) X
    using 1 <;>
    first
    | rfl
    | apply heq_of_eq
      simp_all only [forget₂_semimoduleCat_δ, forget₂_semimoduleCat_η,
        forget₂_semimoduleCat_obj, ComoduleCat.forget₂_obj,
        SemimoduleCat.of_coe, Functor.comp_obj]
      erw [Category.id_comp, id_whiskerRight, Category.id_comp]

private theorem markedUnit_right_unitality (X : C) :
    (ρ_ (E.obj X)).hom = E.obj X ◁ (markedUnitComoduleIso E ω θ h).hom ≫
      (markedTensorComoduleIso E ω θ h X (𝟙_ C)).hom ≫ E.map (ρ_ X).hom := by
  let : (E ⋙ (forget₂ (FGComoduleCat.{u, v, u} k B) (SemimoduleCat.{u} k))).Monoidal :=
    Functor.Monoidal.transport θ.symm
  apply (forget₂ (FGComoduleCat.{u, v, u} k B) (SemimoduleCat.{u} k)).map_injective
  simp only [Functor.map_comp, Functor.Monoidal.map_whiskerLeft,
    Functor.Monoidal.map_rightUnitor]
  simp only [forget₂_semimoduleCat_map, ComoduleCat.forget₂_map,
    markedUnitComoduleIso_hom_toLinearMap, markedTensorComoduleIso_hom_toLinearMap,
    SemimoduleCat.ofHom_hom]
  -- As on the left, convert separates the transported maps from the induced object wrappers.
  -- The heterogeneous goal normalizes to identity whiskering on semimodules.
  convert Functor.LaxMonoidal.right_unitality
    (E ⋙ (forget₂ (FGComoduleCat.{u, v, u} k B) (SemimoduleCat.{u} k))) X
    using 1 <;>
    first
    | rfl
    | apply heq_of_eq
      simp_all only [forget₂_semimoduleCat_δ, forget₂_semimoduleCat_η,
        forget₂_semimoduleCat_obj, ComoduleCat.forget₂_obj,
        SemimoduleCat.of_coe, Functor.comp_obj]
      erw [Category.id_comp, MonoidalCategory.whiskerLeft_id, Category.id_comp]

/-- The monoidal structure on an essentially surjective marked functor to finite comodules.
Only compatibility of the marked tensor comparison with coactions is assumed. -/
noncomputable def markedCoreMonoidal : E.CoreMonoidal where
  εIso := markedUnitComoduleIso E ω θ h
  μIso := markedTensorComoduleIso E ω θ h
  μIso_hom_natural_left f Z := markedTensor_natural_left E ω θ h f Z
  μIso_hom_natural_right Z f := markedTensor_natural_right E ω θ h Z f
  associativity := markedTensor_associativity E ω θ h
  left_unitality := markedUnit_left_unitality E ω θ h
  right_unitality := markedUnit_right_unitality E ω θ h

/-- Equip the marked functor with its lifted strong monoidal structure. -/
@[instance_reducible]
noncomputable def markedMonoidal : E.Monoidal :=
  (markedCoreMonoidal E ω θ h).toMonoidal

/-- The lifted unit has exactly the underlying unit map specified by the marking. -/
@[simp]
theorem markedMonoidal_ε : letI := markedMonoidal E ω θ h
    (Functor.LaxMonoidal.ε E).hom.toLinearMap = (markedUnitIso E ω θ).hom.hom :=
  markedUnitComoduleIso_hom_toLinearMap E ω θ h

/-- The lifted tensorator has exactly the underlying tensor map specified by the marking. -/
@[simp]
theorem markedMonoidal_μ (X Y : C) : letI := markedMonoidal E ω θ h
    (Functor.LaxMonoidal.μ E X Y).hom.toLinearMap =
      (markedTensorIso E ω θ X Y).hom.hom :=
  markedTensorComoduleIso_hom_toLinearMap E ω θ h X Y

/-- The lifted inverse tensorator has the inverse tensor map specified by the marking. -/
@[simp]
theorem markedMonoidal_δ (X Y : C) : letI := markedMonoidal E ω θ h
    (Functor.OplaxMonoidal.δ E X Y).hom.toLinearMap =
      (markedTensorIso E ω θ X Y).inv.hom :=
  markedTensorComoduleIso_inv_toLinearMap E ω θ h X Y

/-- The lifted inverse unit has the inverse unit map specified by the marking. -/
@[simp]
theorem markedMonoidal_η : letI := markedMonoidal E ω θ h
    (Functor.OplaxMonoidal.η E).hom.toLinearMap = (markedUnitIso E ω θ).inv.hom :=
  markedUnitComoduleIso_inv_toLinearMap E ω θ h

/-- The original fibre comparison becomes monoidal for the lifted structure. -/
theorem markedMonoidal_isMonoidal : letI := markedMonoidal E ω θ h
    θ.hom.IsMonoidal := by
  let := markedMonoidal E ω θ h
  have hε : (forget₂ (FGComoduleCat.{u, v, u} k B) (SemimoduleCat.{u} k)).map
      (Functor.LaxMonoidal.ε E) = (markedUnitIso E ω θ).hom := by
    apply SemimoduleCat.hom_ext
    exact markedMonoidal_ε E ω θ h
  have hμ (X Y : C) :
      (forget₂ (FGComoduleCat.{u, v, u} k B) (SemimoduleCat.{u} k)).map
        (Functor.LaxMonoidal.μ E X Y) = (markedTensorIso E ω θ X Y).hom := by
    apply SemimoduleCat.hom_ext
    exact markedMonoidal_μ E ω θ h X Y
  constructor
  · simp only [Functor.LaxMonoidal.comp_ε, hε]
    simp [markedUnitIso]
  · intro X Y
    simp only [Functor.LaxMonoidal.comp_μ, hμ]
    simp [markedTensorIso]

omit [E.EssSurj] in
/-- Every monoidal structure preserving the marking has this unit comparison. -/
theorem map_ε_eq_markedUnitIso_hom [E.Monoidal] [θ.hom.IsMonoidal] :
    (forget₂ (FGComoduleCat.{u, v, u} k B) (SemimoduleCat.{u} k)).map
      (Functor.LaxMonoidal.ε E) = (markedUnitIso E ω θ).hom := by
  apply (cancel_epi (Functor.LaxMonoidal.ε
    (forget₂ (FGComoduleCat.{u, v, u} k B) (SemimoduleCat.{u} k)))).mp
  apply (cancel_mono (θ.app (𝟙_ C)).hom).mp
  simp [markedUnitIso, Functor.LaxMonoidal.comp_ε, Category.assoc]

omit [E.EssSurj] in
/-- Every monoidal structure preserving the marking has this tensor comparison. -/
theorem map_μ_eq_markedTensorIso_hom [E.Monoidal] [θ.hom.IsMonoidal] (X Y : C) :
    (forget₂ (FGComoduleCat.{u, v, u} k B) (SemimoduleCat.{u} k)).map
      (Functor.LaxMonoidal.μ E X Y) = (markedTensorIso E ω θ X Y).hom := by
  apply (cancel_epi (Functor.LaxMonoidal.μ
    (forget₂ (FGComoduleCat.{u, v, u} k B) (SemimoduleCat.{u} k)) (E.obj X) (E.obj Y))).mp
  apply (cancel_mono (θ.app (X ⊗ Y)).hom).mp
  simp [markedTensorIso, Functor.LaxMonoidal.comp_μ, Category.assoc]

/-- Faithfulness makes the marked unit lift unique among monoidal lifts. -/
theorem ε_eq_markedUnitComoduleIso_hom [E.Monoidal] [θ.hom.IsMonoidal] :
    Functor.LaxMonoidal.ε E = (markedUnitComoduleIso E ω θ h).hom := by
  apply (forget₂ (FGComoduleCat.{u, v, u} k B) (SemimoduleCat.{u} k)).map_injective
  rw [map_ε_eq_markedUnitIso_hom E ω θ]
  simp only [forget₂_semimoduleCat_map, ComoduleCat.forget₂_map,
    markedUnitComoduleIso_hom_toLinearMap, SemimoduleCat.ofHom_hom]

omit [E.EssSurj] in
/-- Faithfulness makes each marked tensor lift unique among monoidal lifts. -/
theorem μ_eq_markedTensorComoduleIso_hom [E.Monoidal] [θ.hom.IsMonoidal] (X Y : C) :
    Functor.LaxMonoidal.μ E X Y = (markedTensorComoduleIso E ω θ h X Y).hom := by
  apply (forget₂ (FGComoduleCat.{u, v, u} k B) (SemimoduleCat.{u} k)).map_injective
  rw [map_μ_eq_markedTensorIso_hom E ω θ]
  simp only [forget₂_semimoduleCat_map, ComoduleCat.forget₂_map,
    markedTensorComoduleIso_hom_toLinearMap, SemimoduleCat.ofHom_hom]

omit [E.EssSurj] in
/-- A monoidal fibre marking supplies the tensor-colinearity hypothesis. -/
theorem markedTensorColinear_of_isMonoidal [E.Monoidal] [θ.hom.IsMonoidal] :
    MarkedTensorColinear E ω θ := by
  intro X Y
  rw [← map_μ_eq_markedTensorIso_hom E ω θ]
  exact (Functor.LaxMonoidal.μ E X Y).hom.map_coact

end CategoryTheory.Functor

namespace Units

open CategoryTheory.Functor

universe u v

variable {k : Type u} [CommSemiring k] {B : Type v} [Semiring B] [Bialgebra k B]

/-- Mark the underlying identity functor on finite comodules by multiplying every fibre by
an invertible scalar. -/
noncomputable def fgComoduleScalarMarking (a : kˣ) :
    (𝟭 (FGComoduleCat.{u, v, u} k B)) ⋙ forget₂ _ (SemimoduleCat.{u} k) ≅
      forget₂ _ (SemimoduleCat.{u} k) :=
  NatIso.ofComponents (fun M => (LinearEquiv.smulOfUnit a : M ≃ₗ[k] M).toModuleIsoₛ) (by
    intro M N f
    ext m
    exact (map_smul f.hom.toLinearMap (a : k) m).symm)

/-- The forward scalar marking acts on each fibre by the chosen scalar. -/
@[simp]
theorem fgComoduleScalarMarking_hom_app_apply (a : kˣ)
    (M : FGComoduleCat.{u, v, u} k B) (m : M) :
    @DFunLike.coe (M →ₗ[k] M) M (fun _ => M) _
      ((a.fgComoduleScalarMarking (B := B)).hom.app M).hom m =
      (a : k) • m :=
  (rfl)

/-- The inverse scalar marking acts on each fibre by the inverse scalar. -/
@[simp]
theorem fgComoduleScalarMarking_inv_app_apply (a : kˣ)
    (M : FGComoduleCat.{u, v, u} k B) (m : M) :
    @DFunLike.coe (M →ₗ[k] M) M (fun _ => M) _
      ((a.fgComoduleScalarMarking (B := B)).inv.app M).hom m =
      ((a⁻¹ : kˣ) : k) • m :=
  (rfl)

/-- Rescaling the identity marking multiplies its tensorator by the same scalar. -/
@[simp]
theorem markedTensorIso_fgComoduleScalarMarking_hom_apply (a : kˣ)
    (M N : FGComoduleCat.{u, v, u} k B) (m : M) (n : N) :
    @DFunLike.coe (M ⊗[k] N →ₗ[k] M ⊗[k] N) (M ⊗[k] N) (fun _ => M ⊗[k] N) _
      (markedTensorIso (𝟭 _) (forget₂ _ (SemimoduleCat k))
        (fgComoduleScalarMarking a) M N).hom.hom (m ⊗ₜ[k] n) = (a : k) • (m ⊗ₜ[k] n) := by
  -- The comparisons of the forgetful functor are identities. Expressing the remaining
  -- linear equivalences as scalar actions avoids unfolding their categorical wrappers.
  change (a⁻¹ : kˣ) • (((a : k) • m) ⊗ₜ[k] ((a : k) • n)) =
    (a : k) • (m ⊗ₜ[k] n)
  simp [Units.smul_def, TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul]

/-- Rescaling the identity marking multiplies its unit comparison by the inverse scalar. -/
@[simp]
theorem markedUnitIso_fgComoduleScalarMarking_hom_apply (a : kˣ) (r : k) :
    @DFunLike.coe (k →ₗ[k] k) k (fun _ => k) _
      (markedUnitIso (𝟭 _) (forget₂ _ (SemimoduleCat k))
        (fgComoduleScalarMarking (B := B) a)).hom.hom r =
        ((a⁻¹ : kˣ) : k) • r := by
  -- As above, the unit of the forgetful functor has the identity linear map underneath.
  change (a⁻¹ : kˣ) • r = _
  simp [Units.smul_def]

/-- Scalar markings satisfy tensor colinearity, so they give monoidal lifts even when the
scalar differs from one. -/
theorem markedTensorColinear_fgComoduleScalarMarking (a : kˣ) :
    MarkedTensorColinear (𝟭 (FGComoduleCat.{u, v, u} k B))
      (forget₂ _ (SemimoduleCat.{u} k)) (fgComoduleScalarMarking a) := by
  intro M N
  have ht : (markedTensorIso (𝟭 _) (forget₂ _ (SemimoduleCat k))
      (fgComoduleScalarMarking a) M N).hom.hom = (a : k) • LinearMap.id := by
    apply TensorProduct.ext'
    intro m n
    exact markedTensorIso_fgComoduleScalarMarking_hom_apply a M N m n
  rw [ht, TensorProduct.map_smul_left]
  -- The identity functor's tensor object has the same carrier and coaction as M ⊗ N;
  -- erw crosses that bundled-object wrapper to use the concrete coaction formula.
  erw [FGComoduleCat.tensor_coact k B M N]
  ext z
  simp

end Units

namespace CategoryTheory.Functor

universe u v w w'

variable {k : Type u} [CommSemiring k] {B : Type v} [CommSemiring B] [Bialgebra k B]
variable {C : Type w} [Category.{w'} C] [MonoidalCategory C] [BraidedCategory C]
variable (E : C ⥤ FGComoduleCat.{u, v, u} k B) [E.EssSurj]
variable (ω : C ⥤ SemimoduleCat.{u} k) [ω.Braided]
variable (θ : E ⋙ forget₂ (FGComoduleCat.{u, v, u} k B) (SemimoduleCat.{u} k) ≅ ω)
variable (h : MarkedTensorColinear E ω θ)

/-- A braided fibre marking lifts to a braided functor when the bialgebra is commutative. -/
@[instance_reducible]
noncomputable def markedBraided : letI := markedMonoidal E ω θ h
    E.Braided := by
  letI := markedMonoidal E ω θ h
  letI : θ.hom.IsMonoidal := markedMonoidal_isMonoidal E ω θ h
  letI : θ.symm.hom.IsMonoidal := inferInstanceAs θ.inv.IsMonoidal
  letI : (E ⋙ forget₂ (FGComoduleCat.{u, v, u} k B) (SemimoduleCat.{u} k)).LaxBraided :=
    Functor.LaxBraided.ofNatIso θ.symm
  refine { braided := fun X Y => ?_ }
  apply (forget₂ (FGComoduleCat.{u, v, u} k B) (SemimoduleCat.{u} k)).map_injective
  have hb := Functor.LaxBraided.braided
    (F := E ⋙ forget₂ (FGComoduleCat.{u, v, u} k B) (SemimoduleCat.{u} k)) X Y
  simp only [Functor.map_comp, Functor.map_braiding]
  simp only [Functor.LaxMonoidal.comp_μ, forget₂_semimoduleCat_μ] at hb
  simp only [forget₂_semimoduleCat_δ, forget₂_semimoduleCat_μ]
  -- Forgetting the tensor object and tensoring the forgotten objects give the same
  -- semimodule only definitionally; erw removes the identities at those two presentations.
  erw [Category.id_comp, Category.comp_id]
  -- The composite tensorator has one additional identity comparison at the same carrier.
  erw [Category.id_comp, Category.id_comp] at hb
  exact hb

end CategoryTheory.Functor
