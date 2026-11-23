/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.ExtensionClosed
public import TauCeti.RepresentationTheory.Continuous.BanachRep.Exact
public import TauCeti.RepresentationTheory.FDRep.Continuous

/-!
# Finite-dimensional Banach representations

The finite-dimensional representations form an extension-closed full subcategory of
`TauCeti.BanachRep`. In particular the strict exact structure restricts to this subcategory.

Over a complete nontrivially normed field, forgetting the norm gives an equivalence with
`TauCeti.ContFDRep`, the category defined by continuity of matrix coefficients. Thus a continuous
finite-dimensional representation can be used in Banach extensions independently of a choice
of norm, with all its equivariant linear maps as morphisms.

## References

* J.-M. Fontaine, *Presque `C_p`-représentations*, Documenta Mathematica, Extra Volume Kato
  (2003), §1.2.
-/

public section

universe w u v

open CategoryTheory CategoryTheory.Limits ZeroObject

namespace TauCeti.BanachRep

variable (𝕜 : Type u) [NontriviallyNormedField 𝕜] (G : Type v) [Monoid G] [TopologicalSpace G]

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

section Comparison

variable (𝕜 G) [CompleteSpace 𝕜]

/-- Forget the norm of a finite-dimensional Banach representation, retaining the representation
with continuous matrix coefficients on the same vector space. The object map is transparent
so its morphisms can be evaluated on vectors of the original Banach space. -/
@[expose] noncomputable def toContFDRep :
    (isFiniteDimensional.{u} 𝕜 G).FullSubcategory ⥤ ContFDRep 𝕜 G where
  obj X := ⟨FDRep.of X.obj.ρ.toRepresentation, FDRep.isContinuous_iff.mpr fun f x =>
    f.continuous_of_finiteDimensional.comp (X.obj.ρ.continuous_orbit x)⟩
  map f := ObjectProperty.homMk
    ⟨FGModuleCat.ofHom f.hom.hom.toLinearMap, fun g =>
      FGModuleCat.hom_ext (LinearMap.ext (f.hom.hom_comm_apply g))⟩

variable {𝕜 G}

@[simp]
theorem toContFDRep_obj_obj (X : (isFiniteDimensional.{u} 𝕜 G).FullSubcategory) :
    ((toContFDRep 𝕜 G).obj X).obj = FDRep.of X.obj.ρ.toRepresentation :=
  (rfl)

@[simp]
theorem toContFDRep_map_hom_hom_hom_hom {X Y : (isFiniteDimensional.{u} 𝕜 G).FullSubcategory}
    (f : X ⟶ Y) : ((toContFDRep 𝕜 G).map f).hom.hom.hom.hom = f.hom.hom.toLinearMap :=
  (rfl)

/-- Forgetting the norm is fully faithful since every linear map on a finite-dimensional space
over a complete field is continuous. -/
noncomputable def fullyFaithfulToContFDRep : (toContFDRep 𝕜 G).FullyFaithful where
  preimage f := ObjectProperty.homMk
    ⟨LinearMap.toContinuousLinearMap f.hom.hom.hom.hom,
      fun g x => LinearMap.congr_fun (FDRep.hom_hom_hom_comm f.hom g) x⟩
  map_preimage _ := rfl
  preimage_map _ := rfl

/-- Every finite-dimensional representation with continuous matrix coefficients has a Banach
realization, unique up to isomorphism. -/
instance : (toContFDRep 𝕜 G).IsEquivalence where
  full := fullyFaithfulToContFDRep.full
  faithful := fullyFaithfulToContFDRep.faithful
  essSurj := by
    refine Functor.essSurj_of_surj fun X => ?_
    -- Pull back the sup norm along the coordinate isomorphism.
    let b := Module.finBasis 𝕜 X.obj
    let e := b.equivFun
    let := NormedAddCommGroup.induced _ _ e e.injective
    let := NormedSpace.induced 𝕜 _ _ e
    have := FiniteDimensional.completeSpace 𝕜 X.obj
    have : IsModuleTopology 𝕜 X.obj := isModuleTopologyOfFiniteDimensional
    let ρ : ContinuousRep G 𝕜 X.obj :=
      { toRepresentation := X.obj.ρ
        continuous_action := (ModuleTopology.continuous_linearMap_apply_iff_continuous_toMatrix
          b b X.obj.ρ).mpr (continuous_matrix fun i j => by
            simpa only [LinearMap.toMatrix_apply, Module.Basis.coord_apply] using
              FDRep.isContinuous_iff.mp X.property (b.coord i) (b j)) }
    refine ⟨⟨of ρ, inferInstanceAs (FiniteDimensional 𝕜 X.obj)⟩, ?_⟩
    exact ObjectProperty.FullSubcategory.ext (FDRep.of_ρ_eq_self X.obj)

end Comparison

end TauCeti.BanachRep
