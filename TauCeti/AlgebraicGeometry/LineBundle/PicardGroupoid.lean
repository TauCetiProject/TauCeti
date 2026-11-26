/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.Functoriality
public import TauCeti.CategoryTheory.Monoidal.PicardGroupoid

/-!
# The Picard groupoid of a scheme

The Picard groupoid of a scheme `X` is the groupoid of line bundles on `X` and their isomorphisms,
`picardGroupoid X := Core (InvertibleSheaf X)`, with the symmetric monoidal structure of the tensor
product of line bundles. It is a Picard groupoid in the sense of `TauCeti.PicardGroupoid`: the
inverse of a line bundle `L` is its dual, through `L ⊗ L^∨ ≅ 𝒪_X`.

Its invariants are the Picard group and the units of the global functions:

* `π₀` is the Picard group `LineBundleClass X` (`picardGroupoid.pi0Equiv`);
* `π₁`, the automorphism group of the trivial line bundle, is `Γ(X, 𝒪_X)ˣ`
  (`picardGroupoid.pi1Equiv`), an automorphism being multiplication by a global unit.

Pullback of line bundles along `f : X ⟶ Y` induces a symmetric monoidal functor
`picardGroupoid.pullback f : picardGroupoid Y ⥤ picardGroupoid X`, whose tensor comparison is
`InvertibleSheaf.pullbackTensorProductIso` (`InvertibleSheaf.pullback_μIso` with
`Functor.core_μ_iso`). It is compatible with identities and composites up to the monoidal natural
isomorphisms `picardGroupoid.pullbackId` and `picardGroupoid.pullbackComp`, induced by
`InvertibleSheaf.pullbackId` and `InvertibleSheaf.pullbackComp`.

## References

* B. Bhatt and P. Scholze, *Projectivity of the Witt vector affine Grassmannian*, Invent. Math.
  209 (2017), Definition 12.14 and Proposition 12.15.
* P. Deligne, *La formule de dualité globale*, SGA 4, Exposé XVIII, §1.4.
-/

public section

open CategoryTheory MonoidalCategory

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {X Y Z : Scheme.{u}}

/-- The Picard groupoid of a scheme: line bundles on `X` and their isomorphisms, with the
symmetric monoidal structure of the tensor product of line bundles. -/
abbrev picardGroupoid (X : Scheme.{u}) : Type (u + 1) :=
  Core (InvertibleSheaf X)

namespace picardGroupoid

/-- Every line bundle `L` has the tensor inverse `L^∨`: `L ⊗ L^∨ ≅ 𝒪_X`. -/
instance (X : Scheme.{u}) : PicardGroupoid (picardGroupoid X) :=
  picardGroupoid_core_iff.mpr fun L ↦
    ⟨L.dual, ⟨(L.tensorProductIsoTensor L.dual).symm ≪≫ L.tensorDualIso ≪≫
      InvertibleSheaf.trivialIsoTensorUnit X⟩⟩

/-- The group `π₀` of the Picard groupoid of `X` is the Picard group of `X`. -/
def pi0Equiv (X : Scheme.{u}) : PicardGroupoid.pi0 (picardGroupoid X) ≃* LineBundleClass X :=
  Core.skeletonMulEquiv.trans (LineBundleClass.skeletonMulEquiv X)

/-- `pi0Equiv X` sends the class of a line bundle to its class in the Picard group. -/
@[simp]
lemma pi0Equiv_toSkeleton (L : picardGroupoid X) :
    pi0Equiv X (toSkeleton L) = LineBundleClass.mk L.of := by
  simp [pi0Equiv]

/-- The inverse of `pi0Equiv X` sends the class of a line bundle in the Picard group to its
isomorphism class. -/
@[simp]
lemma pi0Equiv_symm_mk (L : InvertibleSheaf X) :
    (pi0Equiv X).symm (LineBundleClass.mk L) = toSkeleton (⟨L⟩ : picardGroupoid X) := by
  rw [MulEquiv.symm_apply_eq, pi0Equiv_toSkeleton]

/-- The group `π₁` of the Picard groupoid of `X`, the automorphisms of the trivial line bundle,
is the group of units of the global functions on `X`. -/
def pi1Equiv (X : Scheme.{u}) : PicardGroupoid.pi1 (picardGroupoid X) ≃* Γ(X, ⊤)ˣ :=
  (Core.autMulEquiv _).trans <|
    ((SheafOfModules.isInvertible X).fullyFaithfulι.autMulEquivOfFullyFaithful _).trans
      (Scheme.Modules.unitsGlobalSectionsMulEquivAut (𝟙_ X.Modules)).symm

/-- An automorphism `a` of the trivial line bundle is multiplication by the global unit
`pi1Equiv X a`. -/
@[simp]
lemma globalSectionsSmul_pi1Equiv (a : PicardGroupoid.pi1 (picardGroupoid X)) :
    (𝟙_ X.Modules).globalSectionsSmul (pi1Equiv X a) = a.asIso.hom.iso.hom.hom := by
  simp only [pi1Equiv, MulEquiv.trans_apply,
    Scheme.Modules.globalSectionsSmul_unitsGlobalSectionsMulEquivAut_symm]
  -- The full inclusion of line bundles into modules forgets the line-bundle structure.
  exact ((SheafOfModules.isInvertible X).fullyFaithfulι.autMulEquivOfFullyFaithful_apply_asIso_hom
    _ _).trans (congrArg (fun e ↦ e.hom.hom) (Core.autMulEquiv_apply_asIso _ a))

/-- Pullback of line bundles along `f : X ⟶ Y`, as a functor of Picard groupoids. It is
symmetric monoidal, through `Functor.instBraidedCore` and `InvertibleSheaf.pullbackBraided`. -/
abbrev pullback (f : X ⟶ Y) : picardGroupoid Y ⥤ picardGroupoid X :=
  (InvertibleSheaf.pullback f).core

/-- Pullback of line bundles along the identity is isomorphic to the identity functor of the
Picard groupoid, through `InvertibleSheaf.pullbackId`. -/
def pullbackId (X : Scheme.{u}) : pullback (𝟙 X) ≅ 𝟭 (picardGroupoid X) :=
  Iso.core (InvertibleSheaf.pullbackId X) ≪≫ Functor.coreId _

/-- The identity comparison of pullback of Picard groupoids is a monoidal natural
isomorphism. -/
instance isMonoidal_pullbackId_hom (X : Scheme.{u}) :
    NatTrans.IsMonoidal (pullbackId X).hom :=
  inferInstanceAs (NatTrans.IsMonoidal
    ((Iso.core (InvertibleSheaf.pullbackId X)).hom ≫ (Functor.coreId _).hom))

@[simp]
lemma pullbackId_hom_app_iso (L : picardGroupoid X) :
    ((pullbackId X).hom.app L).iso = (InvertibleSheaf.pullbackId X).app L.of := by
  ext
  simp [pullbackId]

/-- Pullback of line bundles along a composite is isomorphic to successive pullback of Picard
groupoids, through `InvertibleSheaf.pullbackComp`. -/
def pullbackComp (f : X ⟶ Y) (g : Y ⟶ Z) : pullback g ⋙ pullback f ≅ pullback (f ≫ g) :=
  (Functor.coreComp _ _).symm ≪≫ Iso.core (InvertibleSheaf.pullbackComp f g)

/-- The composition comparison of pullback of Picard groupoids is a monoidal natural
isomorphism. -/
instance isMonoidal_pullbackComp_hom (f : X ⟶ Y) (g : Y ⟶ Z) :
    NatTrans.IsMonoidal (pullbackComp f g).hom :=
  inferInstanceAs (NatTrans.IsMonoidal
    ((Functor.coreComp _ _).inv ≫ (Iso.core (InvertibleSheaf.pullbackComp f g)).hom))

@[simp]
lemma pullbackComp_hom_app_iso (f : X ⟶ Y) (g : Y ⟶ Z) (L : picardGroupoid Z) :
    ((pullbackComp f g).hom.app L).iso = (InvertibleSheaf.pullbackComp f g).app L.of := by
  ext
  simp [pullbackComp]

end picardGroupoid

end

end TauCeti.AlgebraicGeometry
