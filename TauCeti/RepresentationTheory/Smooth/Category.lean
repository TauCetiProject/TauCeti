/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monad.Limits
public import Mathlib.RepresentationTheory.Rep.Basic
public import TauCeti.RepresentationTheory.Smooth.Basic
import TauCeti.RepresentationTheory.OfMulAction

/-!
# The category of smooth representations

Let `G` be a topological group and `A` a semiring. The smooth representations of `G` over `A`,
those in which every vector has an open stabilizer, form a full subcategory `SmoothRep A G` of
Mathlib's category `Rep A G`. Its morphisms are all `G`-equivariant `A`-linear maps.

Every intertwining map sends smooth vectors to smooth vectors. So over a ring, where the smooth
vectors `V^∞` of `V : Rep A G` again form an object of `Rep A G`, taking smooth vectors is a
functor `SmoothRep.smoothPart : Rep A G ⥤ SmoothRep A G`. It is right adjoint to the inclusion
`SmoothRep.ι`: an intertwining map from a smooth representation lands in the smooth vectors of its
target. The counit `ι (V^∞) ⟶ V` is the inclusion of the smooth vectors, and it is an isomorphism
exactly when `V` is smooth. So `SmoothRep A G` is a coreflective full subcategory of `Rep A G`,
and it has all limits: the limit of a diagram of smooth representations is the smooth part of its
limit in `Rep A G`. When `G` is discrete every representation is smooth and the inclusion is an
equivalence; in particular the regular representation `A[G]` is smooth, and every vector `v` of a
smooth representation `V` gives the morphism `A[G] ⟶ V`, `x ↦ x • v`.

## Main definitions

* `TauCeti.SmoothRep.isSmoothProperty A G`: the property "smooth" on `Rep A G`.
* `TauCeti.SmoothRep A G`: the full subcategory of `Rep A G` on the smooth representations.
* `TauCeti.SmoothRep.ι`: the fully faithful inclusion `SmoothRep A G ⥤ Rep A G`.
* `TauCeti.SmoothRep.of ρ`: a smooth representation `ρ`, bundled as an object of `SmoothRep A G`.
* `TauCeti.SmoothRep.mkIso e he`: the isomorphism of smooth representations given by an
  intertwining linear equivalence `e`.
* `TauCeti.SmoothRep.smoothPart`: the functor `Rep A G ⥤ SmoothRep A G` sending `V` to `V^∞`.
* `TauCeti.SmoothRep.smoothPartAdjunction`: the adjunction `ι ⊣ smoothPart`, whose counit is the
  inclusion of the smooth vectors.
* `TauCeti.SmoothRep.orbitHom`: for a discrete group, the morphism `A[G] ⟶ V`, `x ↦ x • v`, from
  the regular representation.

## Main results

* `TauCeti.SmoothRep.isIso_counit_app_iff`: the counit `ι (V^∞) ⟶ V` is an isomorphism exactly
  when `V` is smooth.
* `TauCeti.SmoothRep.coreflectiveι`: over a ring, `SmoothRep A G` is a coreflective subcategory
  of `Rep A G`, and so it has all limits (`TauCeti.SmoothRep.hasLimits`).
* `TauCeti.SmoothRep.isEquivalence_ι`: for a discrete group, the inclusion is an equivalence.

## References

* J. Bernstein, *Representations of p-adic groups*, Harvard lectures 1992, written by
  K. Rumelhart, Chapter I, §1.1, Proposition 1, p. 7 (the smooth part), and §2, p. 11 (the
  category of smooth representations).
-/

@[expose] public section

open CategoryTheory Limits Representation

universe w u v

namespace TauCeti

variable (A : Type u) (G : Type v) [Group G] [TopologicalSpace G]

section Semiring

variable [Semiring A]

/-- The property "smooth" on `Rep A G`, the property cutting out `SmoothRep A G`. -/
abbrev SmoothRep.isSmoothProperty : ObjectProperty (Rep.{w} A G) := fun V ↦ IsSmooth V.ρ

/-- The category of smooth representations of a topological group `G` over a semiring `A`: the full
subcategory of `Rep A G` on the representations in which every vector has an open stabilizer.
Its morphisms are all intertwining maps. -/
abbrev SmoothRep : Type _ :=
  (SmoothRep.isSmoothProperty.{w} A G).FullSubcategory

namespace SmoothRep

variable {A G}

/-- The representation underlying an object of `SmoothRep A G` is smooth. -/
instance (V : SmoothRep.{w} A G) : IsSmooth V.obj.ρ :=
  V.property

variable (A G) in
/-- The inclusion of the smooth representations into all representations. It is fully faithful
(`ObjectProperty.fullyFaithfulι`). -/
abbrev ι : SmoothRep.{w} A G ⥤ Rep.{w} A G :=
  ObjectProperty.ι _

/-- A smooth representation `ρ`, bundled as an object of `SmoothRep A G`. -/
abbrev of {V : Type w} [AddCommGroup V] [Module A V] (ρ : Representation A G V) [IsSmooth ρ] :
    SmoothRep.{w} A G :=
  ⟨Rep.of ρ, ‹_›⟩

/-- The isomorphism of smooth representations given by a linear equivalence of the underlying
modules that intertwines the actions. -/
def mkIso {V W : SmoothRep.{w} A G} (e : V.obj.V ≃ₗ[A] W.obj.V)
    (he : ∀ g, e ∘ₗ V.obj.ρ g = W.obj.ρ g ∘ₗ e) : V ≅ W :=
  ObjectProperty.isoMk _ (Rep.mkIso { toLinearEquiv := e, isIntertwining' := he })

@[simp]
theorem mkIso_hom_hom_hom_apply {V W : SmoothRep.{w} A G} (e : V.obj.V ≃ₗ[A] W.obj.V)
    (he : ∀ g, e ∘ₗ V.obj.ρ g = W.obj.ρ g ∘ₗ e) (v : V.obj.V) :
    (mkIso e he).hom.hom.hom v = e v :=
  rfl

@[simp]
theorem mkIso_inv_hom_hom_apply {V W : SmoothRep.{w} A G} (e : V.obj.V ≃ₗ[A] W.obj.V)
    (he : ∀ g, e ∘ₗ V.obj.ρ g = W.obj.ρ g ∘ₗ e) (w : W.obj.V) :
    (mkIso e he).inv.hom.hom w = e.symm w :=
  rfl

/-- For a discrete group every representation is smooth, so the inclusion `SmoothRep A G ⥤ Rep A G`
is an equivalence of categories. -/
instance isEquivalence_ι [DiscreteTopology G] : (ι.{w} A G).IsEquivalence where
  essSurj := ⟨fun V ↦ ⟨⟨V, inferInstance⟩, ⟨Iso.refl _⟩⟩⟩

end SmoothRep

end Semiring

/-! ### The smooth part -/

namespace SmoothRep

section SmoothPart

variable {A G} [Ring A] [SeparatelyContinuousMul G]

variable (A G) in
/-- The *smooth part* functor `Rep A G ⥤ SmoothRep A G`, sending a representation `V` to its
subrepresentation of smooth vectors `V^∞` and an intertwining map to its restriction. It is right
adjoint to the inclusion (`smoothPartAdjunction`). -/
-- An abbreviation, so that `simp` sees the object `(smoothPart A G).obj V` as the subrepresentation
-- `V^∞` bundled by `Rep.of`, and applies the lemmas about corestrictions and inclusions to it.
noncomputable abbrev smoothPart : Rep.{w} A G ⥤ SmoothRep.{w} A G where
  obj V := of V.ρ.smoothVectors.toRepresentation
  map {V W} f := ObjectProperty.homMk <| Rep.ofHom <|
    (f.hom.comp V.ρ.smoothVectors.subtype).codRestrict W.ρ.smoothVectors
      fun v ↦ by simpa using f.hom.apply_mem_smoothVectors v.property

variable (A G) in
/-- **The smooth part is right adjoint to the inclusion.** An intertwining map from a smooth
representation `V` to any representation `W` takes values in the smooth vectors `W^∞`. The unit
corestricts the identity of a smooth representation to its smooth vectors, and the counit is the
inclusion `ι (W^∞) ⟶ W` (`smoothPartAdjunction_counit_app`). -/
@[simps! unit_app counit_app]
noncomputable def smoothPartAdjunction : ι.{w} A G ⊣ smoothPart A G :=
  Adjunction.mkOfUnitCounit
    { unit :=
        { app V := ObjectProperty.homMk <| Rep.ofHom <|
            (IntertwiningMap.id V.obj.ρ).codRestrict V.obj.ρ.smoothVectors
              fun _ ↦ Subrepresentation.mem_toSubmodule.2 (IsSmooth.mem_smoothVectors _)
          naturality V W f := by
            ext (v : V.obj)
            apply Subtype.ext
            simp }
      counit :=
        { app W := Rep.ofHom W.ρ.smoothVectors.subtype
          naturality _ _ f := by
            ext v
            simp }
      left_triangle := by
        ext V (v : V.obj)
        simp
      right_triangle := by
        ext W v
        apply Subtype.ext
        simp }

/-- The counit `ι (W^∞) ⟶ W` of `smoothPartAdjunction` is an isomorphism exactly when `W` is
smooth. -/
theorem isIso_counit_app_iff {W : Rep.{w} A G} :
    IsIso ((smoothPartAdjunction A G).counit.app W) ↔ IsSmooth W.ρ := by
  refine ⟨fun _ ↦ isSmooth_iff_forall_mem_smoothVectors.2 fun w ↦ ?_, fun _ ↦ ?_⟩
  · -- `w` is the image under the counit, the inclusion of `W^∞`, of `inv` applied to `w`.
    let e : Rep.of W.ρ.smoothVectors.toRepresentation ≅ W :=
      asIso ((smoothPartAdjunction A G).counit.app W)
    rw [← Rep.hom_inv_apply _ _ e w]
    simp [e]
  · exact (smoothPartAdjunction A G).isIso_counit_app_of_iso (Y := ⟨W, ‹_›⟩) (Iso.refl _)

/-- The counit `ι (W^∞) ⟶ W` is an isomorphism when `W` is smooth. -/
instance {W : Rep.{w} A G} [IsSmooth W.ρ] : IsIso ((smoothPartAdjunction A G).counit.app W) :=
  isIso_counit_app_iff.2 ‹_›

/-- **Smooth representations are coreflective**: the inclusion `SmoothRep A G ⥤ Rep A G` has the
smooth part as right adjoint. -/
noncomputable instance coreflectiveι : Coreflective (ι.{w} A G) where
  R := smoothPart A G
  adj := smoothPartAdjunction A G

/-- The category of smooth representations has all limits, computed by applying the smooth part
to limits in `Rep A G`. -/
instance hasLimits : HasLimits (SmoothRep.{w} A G) :=
  hasLimits_of_coreflective (ι A G)

end SmoothPart

section Discrete

variable {A G} [CommRing A] [DiscreteTopology G]

/-- For a vector `v` of a smooth representation `V` of a discrete group, the morphism
`A[G] ⟶ V`, `x ↦ x • v`, from the regular representation: Mathlib's `Rep.leftRegularHom`. -/
noncomputable def orbitHom (V : SmoothRep.{max u v} A G) (v : V.obj) :
    of (ofMulAction A G G) ⟶ V :=
  ObjectProperty.homMk (Rep.leftRegularHom V.obj v)

@[simp] lemma orbitHom_hom_hom_apply (V : SmoothRep.{max u v} A G) (v : V.obj)
    (x : MonoidAlgebra A G) :
    (orbitHom V v).hom.hom x = V.obj.ρ.asAlgebraHom x v :=
  Rep.leftRegularHom_hom_apply v x

end Discrete

end SmoothRep

end TauCeti
