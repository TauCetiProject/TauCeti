/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.ExtensionClosed
public import TauCeti.RepresentationTheory.Continuous.BanachRep.Exact
public import TauCeti.RepresentationTheory.FDRep.Continuous
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Finite-dimensional Banach representations

The finite-dimensional representations form an extension-closed full subcategory of
`TauCeti.BanachRep`. The construction `TauCeti.ExactStructure.fullSubcategory` restricts the
strict exact structure to this subcategory using `isExtensionClosed_isFiniteDimensional`.

Over a complete nontrivially normed field, forgetting the norm on carriers in the same universe
as the field gives an equivalence with `TauCeti.ContFDRep`, the category defined by continuity
of matrix coefficients. Thus a continuous finite-dimensional representation can be used in Banach
extensions independently of a choice of norm, with all its equivariant linear maps as morphisms.
Under the inverse equivalence, algebraically short exact sequences give Banach conflations.

## References

* J.-M. Fontaine, *Presque `C_p`-représentations*, Documenta Mathematica, Extra Volume Kato
  (2003), §1.2.
-/

public section

universe w u v

open CategoryTheory CategoryTheory.Limits ZeroObject

namespace TauCeti

variable (𝕜 : Type u) [NontriviallyNormedField 𝕜] (G : Type v) [Monoid G] [TopologicalSpace G]

namespace BanachRep

/-- The object property cutting out the finite-dimensional Banach representations. -/
def isFiniteDimensional : ObjectProperty (BanachRep.{w} 𝕜 G) :=
  fun X => FiniteDimensional 𝕜 X

variable {𝕜 G}

@[simp]
theorem isFiniteDimensional_iff (X : BanachRep.{w} 𝕜 G) :
    isFiniteDimensional 𝕜 G X ↔ FiniteDimensional 𝕜 X :=
  Iff.rfl

instance (X : (isFiniteDimensional.{w} 𝕜 G).FullSubcategory) :
    FiniteDimensional 𝕜 X.obj :=
  X.property

/-- An extension in Banach representations of two finite-dimensional representations is
finite-dimensional. -/
theorem isExtensionClosed_isFiniteDimensional :
    exactStructure.IsExtensionClosed (isFiniteDimensional.{w} 𝕜 G) where
  prop_X₂ {S} hS h₁ h₃ := by
    -- As in `TauCeti.isExtensionClosed_finiteModules`, exactness and surjectivity of the
    -- underlying linear maps give finite generation of the middle term.
    have := (isFiniteDimensional_iff S.X₁).mp h₁
    have := (isFiniteDimensional_iff S.X₃).mp h₃
    obtain ⟨_, hsurj, hex⟩ := (exactStructure_conflation_iff S).mp hS
    exact Module.Finite.of_exact (f := S.f.hom.toLinearMap) (g := S.g.hom.toLinearMap) hex hsurj

instance : (isFiniteDimensional.{w} 𝕜 G).ContainsZero where
  exists_zero := by
    have := isZero_iff_subsingleton.mp (isZero_zero (BanachRep.{w} 𝕜 G))
    exact ⟨0, isZero_zero _, (isFiniteDimensional_iff _).mpr inferInstance⟩

instance : (isFiniteDimensional.{w} 𝕜 G).IsClosedUnderIsomorphisms :=
  isExtensionClosed_isFiniteDimensional.isClosedUnderIsomorphisms

instance : (isFiniteDimensional.{w} 𝕜 G).IsClosedUnderBinaryProducts :=
  isExtensionClosed_isFiniteDimensional.isClosedUnderBinaryProducts

variable (𝕜 G) [CompleteSpace 𝕜]

/-- Forget the norm of a finite-dimensional Banach representation, retaining the representation
on its original vector space so that mapped morphisms act on the same vectors. The related
constructor `ContFDRep.ofContRepresentation` uses `FDRep.ofShrink` to change carrier universes.
The object map is transparent to `simp` when it identifies the carriers in morphism evaluations. -/
@[expose, implicit_reducible] noncomputable def toContFDRep :
    (isFiniteDimensional.{u} 𝕜 G).FullSubcategory ⥤ ContFDRep 𝕜 G where
  obj X := ⟨FDRep.of X.obj.ρ.toRepresentation, by
    have : IsModuleTopology 𝕜 X.obj := isModuleTopologyOfFiniteDimensional
    exact (FDRep.isContinuous_iff_continuous_action _).2 X.obj.ρ.continuous_action⟩
  map f := ObjectProperty.homMk
    ⟨FGModuleCat.ofHom f.hom.hom.toLinearMap, fun g =>
      FGModuleCat.hom_ext (LinearMap.ext (f.hom.hom_comm_apply g))⟩

variable {𝕜 G}

/-- The underlying `FDRep` bundles the original linear action on the same carrier. -/
@[simp]
theorem toContFDRep_obj_obj (X : (isFiniteDimensional.{u} 𝕜 G).FullSubcategory) :
    ((toContFDRep 𝕜 G).obj X).obj = FDRep.of X.obj.ρ.toRepresentation :=
  (rfl)

/-- Forgetting the norm sends a continuous intertwiner to its underlying linear map. -/
@[simp]
theorem toContFDRep_map_hom_hom_hom_hom {X Y : (isFiniteDimensional.{u} 𝕜 G).FullSubcategory}
    (f : X ⟶ Y) : ((toContFDRep 𝕜 G).map f).hom.hom.hom.hom = f.hom.hom.toLinearMap :=
  (rfl)

private noncomputable def toContFDRepPreimage {X Y : (isFiniteDimensional.{u} 𝕜 G).FullSubcategory}
    (f : (toContFDRep 𝕜 G).obj X ⟶ (toContFDRep 𝕜 G).obj Y) : X ⟶ Y :=
  let φ : X.obj →ₗ[𝕜] Y.obj := f.hom.hom.hom.hom
  ObjectProperty.homMk ⟨LinearMap.toContinuousLinearMap φ, fun g x => by
    simp only [LinearMap.coe_toContinuousLinearMap']
    exact LinearMap.congr_fun (FDRep.hom_hom_hom_comm f.hom g) x⟩

private theorem toContFDRepPreimage_apply {X Y : (isFiniteDimensional.{u} 𝕜 G).FullSubcategory}
    (f : (toContFDRep 𝕜 G).obj X ⟶ (toContFDRep 𝕜 G).obj Y) (x : X.obj) :
    (toContFDRepPreimage f).hom.hom x = f.hom.hom.hom.hom x := by
  simp only [toContFDRepPreimage, ObjectProperty.homMk_hom, LinearMap.coe_toContinuousLinearMap']

/-- Forgetting the norm is fully faithful since every linear map on a finite-dimensional space
over a complete field is continuous. -/
noncomputable def fullyFaithfulToContFDRep : (toContFDRep 𝕜 G).FullyFaithful where
  preimage := toContFDRepPreimage
  map_preimage {X Y} f := by
    ext x
    rw [toContFDRep_map_hom_hom_hom_hom]
    exact toContFDRepPreimage_apply f x
  preimage_map f := by
    ext x
    simp only [toContFDRepPreimage_apply, toContFDRep_map_hom_hom_hom_hom,
      ContinuousLinearMap.coe_coe]

/-- The lifted continuous intertwiner agrees with the original intertwiner on every vector. -/
@[simp]
theorem fullyFaithfulToContFDRep_preimage_apply
    {X Y : (isFiniteDimensional.{u} 𝕜 G).FullSubcategory}
    (f : (toContFDRep 𝕜 G).obj X ⟶ (toContFDRep 𝕜 G).obj Y) (x : X.obj) :
    (fullyFaithfulToContFDRep.preimage f).hom.hom x = f.hom.hom.hom.hom x :=
  toContFDRepPreimage_apply f x

end BanachRep

variable {𝕜 G} [CompleteSpace 𝕜]

namespace ContFDRep

open BanachRep

/-- Equip the original carrier of a continuous finite-dimensional representation with the
sup norm in finite-basis coordinates, giving a Banach realization of its action. -/
@[expose] noncomputable def toBanachRep (X : ContFDRep 𝕜 G) :
    (isFiniteDimensional.{u} 𝕜 G).FullSubcategory :=
  let e := (Module.finBasis 𝕜 X.obj).equivFun
  letI := NormedAddCommGroup.induced _ _ e e.injective
  letI := NormedSpace.induced 𝕜 _ _ e
  haveI := FiniteDimensional.completeSpace 𝕜 X.obj
  haveI : IsModuleTopology 𝕜 X.obj := isModuleTopologyOfFiniteDimensional
  let ρ : ContinuousRep G 𝕜 X.obj :=
    ⟨X.obj.ρ, (FDRep.isContinuous_iff_continuous_action X.obj).1 X.property⟩
  ⟨of ρ, (isFiniteDimensional_iff _).2 (inferInstanceAs (FiniteDimensional 𝕜 X.obj))⟩

/-- The Banach realization has the original carrier and linear action. -/
@[simp]
theorem toBanachRep_ρ (X : ContFDRep 𝕜 G) : X.toBanachRep.obj.ρ.toRepresentation = X.obj.ρ :=
  (rfl)

/-- Forgetting the norm of the Banach realization recovers the original bundled representation. -/
@[simp]
theorem toContFDRep_obj_toBanachRep (X : ContFDRep 𝕜 G) :
    (toContFDRep 𝕜 G).obj X.toBanachRep = X := by
  apply ObjectProperty.FullSubcategory.ext
  rw [toContFDRep_obj_obj, toBanachRep_ρ]
  exact FDRep.of_ρ_eq_self X.obj

end ContFDRep

namespace BanachRep

/-- Every finite-dimensional representation with continuous matrix coefficients has a Banach
realization, unique up to isomorphism. -/
instance : (toContFDRep 𝕜 G).IsEquivalence where
  full := fullyFaithfulToContFDRep.full
  faithful := fullyFaithfulToContFDRep.faithful
  essSurj := Functor.essSurj_of_surj fun X => ⟨X.toBanachRep, X.toContFDRep_obj_toBanachRep⟩

/-- A complex of finite-dimensional Banach representations is a conflation under inclusion
exactly when its image under the comparison is short exact on underlying modules. -/
theorem _root_.CategoryTheory.ShortComplex.conflation_map_ι_iff_shortExact_map_toContFDRep
    (S : ShortComplex (isFiniteDimensional.{u} 𝕜 G).FullSubcategory) :
    exactStructure.Conflation (S.map (isFiniteDimensional 𝕜 G).ι) ↔
      ((S.map (toContFDRep 𝕜 G)).map (forget₂ (ContFDRep 𝕜 G) (ModuleCat 𝕜))).ShortExact := by
  let M := (S.map (toContFDRep 𝕜 G)).map (forget₂ (ContFDRep 𝕜 G) (ModuleCat 𝕜))
  have hmap {X Y : (isFiniteDimensional.{u} 𝕜 G).FullSubcategory} (f : X ⟶ Y) :
      ⇑((forget₂ (ContFDRep 𝕜 G) (ModuleCat 𝕜)).map ((toContFDRep 𝕜 G).map f)) = ⇑f.hom.hom := by
    simp only [ContFDRep.forget₂_map, toContFDRep_map_hom_hom_hom_hom, ContinuousLinearMap.coe_coe]
  simp only [exactStructure_conflation_iff, ShortComplex.map_f, ShortComplex.map_g,
    ObjectProperty.ι_map, ← hmap S.f, ← hmap S.g]
  exact ⟨fun ⟨hi, hs, he⟩ => ModuleCat.shortComplex_shortExact M he hi hs, fun h =>
    ⟨h.moduleCat_injective_f, h.moduleCat_surjective_g,
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact M).1 h.exact⟩⟩

/-- An algebraically short exact sequence of continuous finite-dimensional representations
gives a conflation under the inverse comparison and inclusion into Banach representations. -/
theorem _root_.CategoryTheory.ShortComplex.conflation_map_inv_toContFDRep
    (S : ShortComplex (ContFDRep 𝕜 G))
    (hS : (S.map (forget₂ (ContFDRep 𝕜 G) (ModuleCat 𝕜))).ShortExact) :
    exactStructure.Conflation (S.map ((toContFDRep 𝕜 G).inv ⋙ (isFiniteDimensional 𝕜 G).ι)) := by
  let U := forget₂ (ContFDRep 𝕜 G) (ModuleCat 𝕜)
  rw [ShortComplex.map_comp, ShortComplex.conflation_map_ι_iff_shortExact_map_toContFDRep]
  -- The counit identifies the underlying complex of the Banach realization with the original.
  exact ShortComplex.shortExact_of_iso
    (U.mapShortComplex.mapIso (S.mapNatIso (toContFDRep 𝕜 G).asEquivalence.counitIso).symm) hS

end BanachRep

end TauCeti
