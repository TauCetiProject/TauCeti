/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.RingTheory.DividedPowers.DPMorphism
public import TauCeti.AlgebraicGeometry.IdealSheaf.Module
public import TauCeti.AlgebraicGeometry.Morphisms.Thickening

/-!
# Divided power schemes

A divided power scheme equips a quasi-coherent ideal sheaf with divided powers on sections,
compatible with restriction. The closed subscheme cut out by the ideal is its closed fibre.
The closed fibre functor is right adjoint to equipping a scheme with the zero divided power ideal.

## References

* The Stacks Project, [Divided power schemes](https://stacks.math.columbia.edu/tag/07I1).
-/

public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Scheme.IdealSheafData

namespace TauCeti

universe u

/-- A scheme with a quasi-coherent ideal sheaf carrying restriction-compatible divided powers. -/
structure DividedPowerScheme where
  /-- The ambient scheme. -/
  scheme : Scheme.{u}
  /-- The quasi-coherent ideal sheaf carrying the divided powers. -/
  ideal : scheme.IdealSheafData
  /-- The divided power structure on sections of the ideal over each open. -/
  dividedPowers (U : scheme.Opens) : DividedPowers (ideal.sections U)
  /-- Restriction of regular functions preserves divided powers on the ideal. -/
  isDPMorphism_res {U V : scheme.Opens} (i : V ⟶ U) :
    DividedPowers.IsDPMorphism (dividedPowers U) (dividedPowers V) (scheme.presheaf.map i.op).hom

namespace DividedPowerScheme

noncomputable section

variable {X Y Z : DividedPowerScheme.{u}}

/-- A morphism of divided power schemes is a scheme morphism that carries the target ideal into
the source ideal and commutes with divided powers on sections. -/
@[ext]
structure Hom (X Y : DividedPowerScheme.{u}) where
  /-- The underlying morphism of schemes. -/
  hom : X.scheme ⟶ Y.scheme
  /-- The pullback on sections preserves the ideals and their divided powers. -/
  isDPMorphism_appLE (U : Y.scheme.Opens) (V : X.scheme.Opens) (h : V ≤ hom ⁻¹ᵁ U) :
    DividedPowers.IsDPMorphism (Y.dividedPowers U) (X.dividedPowers V) (hom.appLE U V h).hom

/-- The pullback over an open and its inverse image is a divided power morphism. -/
theorem Hom.isDPMorphism_app (f : Hom X Y) (U : Y.scheme.Opens) :
    DividedPowers.IsDPMorphism (Y.dividedPowers U) (X.dividedPowers (f.hom ⁻¹ᵁ U))
      (f.hom.app U).hom := by
  rw [f.hom.app_eq_appLE]
  exact f.isDPMorphism_appLE U _ le_rfl

/-- Construct a morphism from a scheme map preserving divided powers over each open and its
inverse image. -/
def Hom.mkOfApp (f : X.scheme ⟶ Y.scheme)
    (hf : ∀ U, DividedPowers.IsDPMorphism (Y.dividedPowers U)
      (X.dividedPowers (f ⁻¹ᵁ U)) (f.app U).hom) : Hom X Y where
  hom := f
  isDPMorphism_appLE U _ h :=
    (X.isDPMorphism_res (homOfLE h)).comp _ (hf U)

/-- A morphism constructed from its action on opens has the specified ambient morphism. -/
@[simp]
theorem Hom.mkOfApp_hom (f : X.scheme ⟶ Y.scheme) (h) : (Hom.mkOfApp f h).hom = f := (rfl)

/-- The identity and composition of divided power morphisms are given by those of schemes. -/
instance : Category DividedPowerScheme.{u} where
  Hom := Hom
  id X :=
    { hom := 𝟙 X.scheme
      isDPMorphism_appLE := fun U V h ↦ by
        have hVU : V ≤ U := Scheme.Hom.id_preimage U ▸ h
        have he : Scheme.Hom.appLE (𝟙 X.scheme) U V h =
            X.scheme.presheaf.map (homOfLE hVU).op := by
          simp only [Scheme.Hom.appLE, Scheme.Hom.id_app]
          exact Category.id_comp _
        rw [he]
        exact X.isDPMorphism_res (homOfLE hVU) }
  comp f g :=
    { hom := f.hom ≫ g.hom
      isDPMorphism_appLE := fun U V h ↦ by
        rw [Scheme.Hom.comp_appLE]
        exact (f.isDPMorphism_appLE (g.hom ⁻¹ᵁ U) V h).comp _ (g.isDPMorphism_app U) }
  id_comp _ := Hom.ext (Category.id_comp _)
  comp_id _ := Hom.ext (Category.comp_id _)
  assoc _ _ _ := Hom.ext (Category.assoc _ _ _)

/-- The identity of a divided power scheme has underlying scheme map the identity. -/
@[simp]
theorem Hom.id_hom (X : DividedPowerScheme.{u}) : Hom.hom (𝟙 X) = 𝟙 X.scheme := (rfl)

/-- The underlying scheme map of a composite is the composite of the underlying scheme maps. -/
@[simp]
theorem Hom.comp_hom (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).hom = f.hom ≫ g.hom := (rfl)

/-- Forget the ideal and divided powers. -/
abbrev forget : DividedPowerScheme.{u} ⥤ Scheme.{u} where
  obj X := X.scheme
  map f := f.hom

/-- The forgetful functor evaluates to the underlying scheme. -/
@[simp]
theorem forget_obj (X : DividedPowerScheme.{u}) : forget.obj X = X.scheme := (rfl)

/-- The forgetful functor evaluates to the underlying scheme morphism. -/
@[simp]
theorem forget_map (f : X ⟶ Y) : forget.map f = f.hom := (rfl)

/-- Divided power scheme morphisms are determined by their underlying scheme morphisms. -/
instance : forget.Faithful where
  map_injective h := Hom.ext h

/-- Pullback of sections along a morphism commutes with every divided power. -/
@[simp]
theorem Hom.app_dpow (f : X ⟶ Y) (U : Y.scheme.Opens) {x : Γ(Y.scheme, U)}
    (hx : x ∈ Y.ideal.sections U) (n : ℕ) :
    f.hom.app U ((Y.dividedPowers U).dpow n x) =
      (X.dividedPowers (f.hom ⁻¹ᵁ U)).dpow n (f.hom.app U x) :=
  (f.isDPMorphism_app U).map_dpow hx

/-- The inverse image of the target ideal lies in the source ideal. -/
theorem Hom.ideal_comap_le (f : X ⟶ Y) : Y.ideal.comap f.hom ≤ X.ideal := by
  rw [← le_map_iff_comap_le]
  -- The kernel of a scheme map is the ideal sheaf generated by its sectionwise kernels.
  refine le_trans (le_of_eq (ofIdeals_ideal Y.ideal).symm) (ofIdeals_mono fun U ↦ ?_)
  rw [← sections_eq_ideal]
  intro x hx
  have hm := (f.isDPMorphism_app U.val).ideal_comp (Ideal.mem_map_of_mem _ hx)
  -- The section map of the composite evaluates by successive pullback.
  exact RingHom.mem_ker.mpr ((X.ideal.mem_sections_iff).mp hm)

/-- The closed subscheme cut out by the divided power ideal. -/
abbrev closedFiber (X : DividedPowerScheme.{u}) : Scheme.{u} :=
  X.ideal.subscheme

/-- The closed immersion of the closed fibre into the ambient scheme. -/
abbrev closedFiberι (X : DividedPowerScheme.{u}) : X.closedFiber ⟶ X.scheme :=
  X.ideal.subschemeι

/-- The affine-open ideal inherits its divided powers from the sections of the ideal sheaf. -/
def dividedPowersOnAffine (X : DividedPowerScheme.{u}) (U : X.scheme.affineOpens) :
    DividedPowers (X.ideal.ideal U) :=
  DividedPowers.ofRingEquiv (e := RingEquiv.refl _) (by
    exact (Ideal.map_id (I := X.ideal.sections U.val)).trans (X.ideal.sections_eq_ideal U))
    (X.dividedPowers U.val)

/-- On an affine open the inherited operations are the sectionwise divided powers. -/
@[simp]
theorem dividedPowersOnAffine_dpow (X : DividedPowerScheme.{u}) (U : X.scheme.affineOpens)
    (n : ℕ) (x : Γ(X.scheme, U.val)) :
    (X.dividedPowersOnAffine U).dpow n x = (X.dividedPowers U.val).dpow n x := by
  unfold dividedPowersOnAffine
  exact DividedPowers.ofRingEquiv_dpow _ _

/-- A divided power morphism induces a map of closed fibres. -/
def Hom.closedFiberMap (f : X ⟶ Y) : X.closedFiber ⟶ Y.closedFiber :=
  subschemeMap X.ideal Y.ideal f.hom (le_map_iff_comap_le.mpr f.ideal_comap_le)

/-- The map of closed fibres commutes with their inclusions into the ambient schemes. -/
@[reassoc (attr := simp)]
theorem Hom.closedFiberMap_comp_ι (f : X ⟶ Y) :
    f.closedFiberMap ≫ Y.closedFiberι = X.closedFiberι ≫ f.hom :=
  subschemeMap_subschemeι _ _ _ _

/-- The closed fibre construction is functorial. -/
@[expose, implicit_reducible] def closedFiberFunctor : DividedPowerScheme.{u} ⥤ Scheme.{u} where
  obj := closedFiber
  map f := f.closedFiberMap
  map_id X := by
    rw [← cancel_mono X.closedFiberι]
    simp
  map_comp f g := by
    rw [← cancel_mono (closedFiberι _)]
    simp

/-- The closed fibre functor sends a divided power scheme to its closed fibre. -/
@[simp]
theorem closedFiberFunctor_obj (X : DividedPowerScheme.{u}) :
    closedFiberFunctor.obj X = X.closedFiber := (rfl)

/-- The closed fibre functor sends a morphism to its induced map on closed fibres. -/
@[simp]
theorem closedFiberFunctor_map (f : X ⟶ Y) : closedFiberFunctor.map f = f.closedFiberMap := (rfl)

/-- The closed fibres form a closed subscheme of the underlying schemes, naturally in the
divided power scheme. -/
def closedFiberInclusion : closedFiberFunctor.{u} ⟶ forget where
  app X := X.closedFiberι
  naturality _ _ f := f.closedFiberMap_comp_ι

/-- The component of the natural inclusion is the closed fibre immersion. -/
@[simp]
theorem closedFiberInclusion_app (X : DividedPowerScheme.{u}) :
    closedFiberInclusion.app X = X.closedFiberι := (rfl)

/-- A divided power scheme is a divided power thickening when its closed fibre is a thickening. -/
abbrev IsPDThickening (X : DividedPowerScheme.{u}) : Prop :=
  AlgebraicGeometry.IsThickening X.closedFiberι

/-- A divided power scheme is a divided power thickening exactly when its ideal lies in the
nilradical. -/
theorem isPDThickening_iff (X : DividedPowerScheme.{u}) :
    X.IsPDThickening ↔ X.ideal ≤ X.scheme.nilradical := by
  unfold IsPDThickening
  rw [AlgebraicGeometry.isThickening_iff_ker_le_nilradical, ker_subschemeι]

/-- Equip ordinary schemes with the zero divided power ideal. -/
@[expose, implicit_reducible] def trivial : Scheme.{u} ⥤ DividedPowerScheme.{u} :=
  have isDPMorphism {T T' : Scheme.{u}} {U : T.Opens} {V : T'.Opens}
      {hU : DividedPowers ((⊥ : T.IdealSheafData).sections U)}
      {hV : DividedPowers ((⊥ : T'.IdealSheafData).sections V)}
      (f : Γ(T, U) →+* Γ(T', V)) : DividedPowers.IsDPMorphism hU hV f := by
    apply DividedPowers.IsDPMorphism.on_span (S := ∅) <;> simp [sections_bot]
  { obj T :=
      { scheme := T
        ideal := ⊥
        dividedPowers U := DividedPowers.ofRingEquiv (e := RingEquiv.refl _)
          (by rw [Ideal.map_bot, sections_bot]) (dividedPowersBot Γ(T, U))
        isDPMorphism_res i := isDPMorphism (T.presheaf.map i.op).hom }
    map f := Hom.mkOfApp f fun U ↦ isDPMorphism (f.app U).hom
    map_id _ := Hom.ext (by simp only [Hom.mkOfApp_hom, Hom.id_hom])
    map_comp _ _ := Hom.ext (by simp only [Hom.mkOfApp_hom, Hom.comp_hom]) }

/-- The ambient scheme of a trivial divided power scheme is the original scheme. -/
@[simp]
theorem trivial_obj_scheme (T : Scheme.{u}) : (trivial.obj T).scheme = T := (rfl)

/-- The trivial divided power scheme has zero ideal sheaf. -/
@[simp]
theorem trivial_obj_ideal (T : Scheme.{u}) :
    ((trivial.obj T).ideal : (trivial.obj T).scheme.IdealSheafData) = ⊥ := (rfl)

/-- The zero-ideal functor retains the underlying scheme map. -/
@[simp]
theorem trivial_map_hom {T T' : Scheme.{u}} (f : T ⟶ T') : (trivial.map f).hom = f := (rfl)

/-- A scheme map from a scheme with zero ideal is a divided power morphism when it kills the
target ideal on sections. -/
def Hom.fromTrivial {T : Scheme.{u}} (f : T ⟶ X.scheme)
    (hf : ∀ (U : X.scheme.Opens) (x : Γ(X.scheme, U)), x ∈ X.ideal.sections U →
      f.app U x = 0) : trivial.obj T ⟶ X :=
  Hom.mkOfApp f fun U ↦ by
    refine (DividedPowers.isDPMorphism_iff _ _ _).mpr ⟨?_, fun n hn x hx ↦ ?_⟩
    · refine Ideal.map_le_iff_le_comap.mpr fun x hx ↦ ?_
      exact (sections_bot (f ⁻¹ᵁ U)).symm ▸ (Ideal.mem_bot.mpr (hf U x hx))
    · rw [hf U x hx, DividedPowers.dpow_eval_zero _ hn]
      exact (hf U _ ((X.dividedPowers U).dpow_mem hn hx)).symm

/-- The morphism from a zero-ideal scheme has the specified ambient map. -/
@[simp]
theorem Hom.fromTrivial_hom {T : Scheme.{u}} (f : T ⟶ X.scheme) (h) :
    (Hom.fromTrivial f h).hom = f := (rfl)

/-- The trivial divided power scheme is a divided power thickening. -/
@[simp]
theorem isPDThickening_trivial_obj (T : Scheme.{u}) : (trivial.obj T).IsPDThickening := by
  rw [isPDThickening_iff, trivial_obj_ideal]
  exact bot_le

/-- Maps from a trivial divided power scheme factor uniquely through the closed fibre. -/
private def trivialHomEquiv (T : Scheme.{u}) (X : DividedPowerScheme.{u}) :
    (trivial.obj T ⟶ X) ≃ (T ⟶ closedFiberFunctor.obj X) where
  toFun f := by
    refine IsClosedImmersion.lift X.closedFiberι f.hom ?_
    have h : X.ideal.comap f.hom ≤ ⊥ := by
      simpa only [trivial_obj_ideal] using f.ideal_comap_le
    exact X.ideal.ker_subschemeι.trans_le
      ((le_map_iff_comap_le.mpr h).trans_eq (map_bot f.hom))
  invFun g := by
    refine Hom.fromTrivial (X := X) (g ≫ X.closedFiberι) fun U x hx ↦ ?_
    -- The composite on sections first restricts to the closed fibre, where the ideal vanishes.
    have h := congrArg (g.app (X.closedFiberι ⁻¹ᵁ U)).hom (X.ideal.mem_sections_iff.mp hx)
    exact h.trans (map_zero _)
  left_inv f := Hom.ext (IsClosedImmersion.lift_fac _ _ _)
  right_inv g := by
    rw [← cancel_mono X.closedFiberι]
    exact IsClosedImmersion.lift_fac _ _ _

/-- The scheme map underlying a morphism from the zero ideal is obtained by composing its
factorization with the closed fibre inclusion. -/
private theorem trivialHomEquiv_comp_ι (T : Scheme.{u}) (X : DividedPowerScheme.{u})
    (f : trivial.obj T ⟶ X) :
    trivialHomEquiv T X f ≫ X.closedFiberι = (f.hom : T ⟶ X.scheme) :=
  IsClosedImmersion.lift_fac _ _ _

private theorem trivialHomEquiv_symm_hom (T : Scheme.{u}) (X : DividedPowerScheme.{u})
    (g : T ⟶ X.closedFiber) :
    ((trivialHomEquiv T X).symm g).hom = g ≫ X.closedFiberι := by
  simp only [trivialHomEquiv, Equiv.coe_fn_symm_mk]
  apply Hom.fromTrivial_hom

/-- The trivial divided power functor is left adjoint to taking the closed fibre. -/
def trivialAdjunction : trivial.{u} ⊣ closedFiberFunctor.{u} :=
  Adjunction.mkOfHomEquiv
    { homEquiv := trivialHomEquiv
      homEquiv_naturality_left_symm := by
        intro T T' X f g
        apply Hom.ext
        simp [trivialHomEquiv_symm_hom]
      homEquiv_naturality_right := by
        intro T X Y f g
        rw [← cancel_mono Y.closedFiberι]
        simp [trivialHomEquiv_comp_ι, reassoc_of% trivialHomEquiv_comp_ι] }

/-- The factorization supplied by the adjunction recovers the ambient map after the inclusion. -/
@[reassoc (attr := simp)]
theorem trivialAdjunction_homEquiv_comp_ι (T : Scheme.{u}) (X : DividedPowerScheme.{u})
    (f : trivial.obj T ⟶ X) :
    trivialAdjunction.homEquiv T X f ≫ X.closedFiberι = (f.hom : T ⟶ X.scheme) := by
  rw [trivialAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  exact trivialHomEquiv_comp_ι T X f

/-- The inverse hom equivalence sends a map into the closed fibre to its composite with the
closed immersion. -/
@[simp]
theorem trivialAdjunction_homEquiv_symm_hom (T : Scheme.{u}) (X : DividedPowerScheme.{u})
    (g : T ⟶ X.closedFiber) :
    ((trivialAdjunction.homEquiv T X).symm g).hom = g ≫ X.closedFiberι := by
  rw [trivialAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  exact trivialHomEquiv_symm_hom T X g

/-- The counit of the zero-ideal adjunction has underlying map the closed fibre immersion. -/
@[simp]
theorem trivialAdjunction_counit_app_hom (X : DividedPowerScheme.{u}) :
    (trivialAdjunction.counit.app X).hom = X.closedFiberι := by
  rw [← trivialAdjunction.homEquiv_symm_id, trivialAdjunction_homEquiv_symm_hom, Category.id_comp]

/-- The unit of the zero-ideal adjunction is a section of the closed fibre immersion. -/
@[reassoc (attr := simp)]
theorem trivialAdjunction_unit_app_comp_ι (T : Scheme.{u}) :
    trivialAdjunction.unit.app T ≫ (trivial.obj T).closedFiberι = 𝟙 T := by
  rw [← trivialAdjunction.homEquiv_id]
  exact (trivialAdjunction_homEquiv_comp_ι T (trivial.obj T) (𝟙 _)).trans (Hom.id_hom _)

end

end DividedPowerScheme
end TauCeti
