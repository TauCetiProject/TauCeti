/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Basic

/-!
# Equivariant maps of C⋆-algebra actions

This file develops morphisms between point-norm continuous C⋆-actions. A nonunital star-algebra
homomorphism is equivariant when it intertwines the two actions. Equivariance is preserved by
identity, composition, pullback of the acting group, and passage to the inverse of a star-algebra
equivalence.

Invariant subsets are also introduced. Their elementary API gives invariant preimages and images
under equivariant maps. A closed invariant nonunital star subalgebra inherits a continuous action,
and its canonical inclusion is equivariant. These constructions are the functorial foundation for
invariant ideals, quotient actions, and crossed-product maps.

The conventions follow Dana Williams, *Crossed Products of C*-Algebras*, Chapter 2.
-/

public section

noncomputable section

namespace TauCeti.CStarAction

variable {G H A B C : Type*}
  [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]

/-- A subset is invariant under an action when every group element maps it into itself. -/
def IsInvariant (α : CStarAction G A) (s : Set A) : Prop :=
  ∀ g, Set.MapsTo (α g) s s

namespace IsInvariant

variable {α : CStarAction G A} {s t : Set A}

/-- An invariant subset contains the image of each of its elements under the action. -/
theorem apply_mem (hs : α.IsInvariant s) (g : G) {a : A} (ha : a ∈ s) : α g a ∈ s :=
  hs g ha

/-- Membership in an invariant subset is unchanged by the action. -/
@[simp]
theorem apply_mem_iff (hs : α.IsInvariant s) (g : G) (a : A) : α g a ∈ s ↔ a ∈ s := by
  refine ⟨fun h ↦ ?_, hs.apply_mem g⟩
  simpa only [inv_apply_apply] using hs.apply_mem g⁻¹ h

/-- The empty subset is invariant. -/
protected theorem empty : α.IsInvariant ∅ :=
  fun _ _ h ↦ h.elim

/-- The whole algebra is invariant. -/
protected theorem univ : α.IsInvariant Set.univ :=
  fun _ _ _ ↦ Set.mem_univ _

/-- Intersections of invariant subsets are invariant. -/
theorem inter (hs : α.IsInvariant s) (ht : α.IsInvariant t) : α.IsInvariant (s ∩ t) :=
  fun g _ ha ↦ ⟨hs.apply_mem g ha.1, ht.apply_mem g ha.2⟩

/-- Arbitrary intersections of invariant subsets are invariant. -/
theorem iInter {ι : Type*} {s : ι → Set A} (hs : ∀ i, α.IsInvariant (s i)) :
    α.IsInvariant (⋂ i, s i) := by
  intro g a ha
  simp only [Set.mem_iInter] at ha ⊢
  exact fun i ↦ (hs i).apply_mem g (ha i)

end IsInvariant

/-- A nonunital star-algebra homomorphism is equivariant when it intertwines two actions. -/
def IsEquivariant (α : CStarAction G A) (β : CStarAction G B)
    (f : A →⋆ₙₐ[ℂ] B) : Prop :=
  ∀ g, Function.Semiconj f (α g) (β g)

namespace IsEquivariant

variable {α : CStarAction G A} {β : CStarAction G B} {γ : CStarAction G C}
  {f : A →⋆ₙₐ[ℂ] B} {k : B →⋆ₙₐ[ℂ] C}

/-- The defining intertwining identity for an equivariant homomorphism. -/
theorem apply (hf : α.IsEquivariant β f) (g : G) (a : A) :
    f (α g a) = β g (f a) :=
  hf g a

/-- Identity homomorphisms are equivariant. -/
protected theorem id : α.IsEquivariant α (NonUnitalStarAlgHom.id ℂ A) :=
  fun _ _ ↦ rfl

/-- A composite of equivariant homomorphisms is equivariant. -/
theorem comp (hk : β.IsEquivariant γ k) (hf : α.IsEquivariant β f) :
    α.IsEquivariant γ (k.comp f) := by
  intro g a
  simp only [NonUnitalStarAlgHom.comp_apply, hf.apply, hk.apply]

/-- The zero homomorphism is equivariant for any two actions. -/
protected theorem zero : α.IsEquivariant β (0 : A →⋆ₙₐ[ℂ] B) := by
  intro g a
  simp

/-- Equivariance is preserved when both actions are pulled back along the same group map. -/
theorem comp_action (hf : α.IsEquivariant β f) (φ : ContinuousMonoidHom H G) :
    (α.comp φ).IsEquivariant (β.comp φ) f :=
  fun h a ↦ by simpa only [CStarAction.comp_apply] using hf (φ h) a

/-- Every homomorphism between trivial actions is equivariant. -/
theorem trivial (f : A →⋆ₙₐ[ℂ] B) :
    (CStarAction.trivial (G := G) (A := A)).IsEquivariant
      (CStarAction.trivial (G := G) (A := B)) f :=
  fun g a ↦ by simp only [CStarAction.trivial_apply]

/-- The equivalence used to transport an action is equivariant for the transported action. -/
theorem conjugate (α : CStarAction G A) (e : A ≃⋆ₐ[ℂ] B) :
    α.IsEquivariant (α.conjugate e) e.toNonUnitalStarAlgHom := by
  intro g a
  simp

/-- An equivariant star-algebra equivalence has equivariant inverse. -/
theorem symm (e : A ≃⋆ₐ[ℂ] B) (he : α.IsEquivariant β e.toNonUnitalStarAlgHom) :
    β.IsEquivariant α e.symm.toNonUnitalStarAlgHom := by
  intro g b
  simpa only [StarAlgEquiv.toNonUnitalStarAlgHom_apply, e.apply_symm_apply,
    e.symm_apply_apply] using congrArg e.symm (he.apply g (e.symm b)).symm

/-- A star-algebra equivalence is equivariant exactly when transport along it gives the target
action. -/
theorem starAlgEquiv_iff_conjugate_eq (e : A ≃⋆ₐ[ℂ] B) :
    α.IsEquivariant β e.toNonUnitalStarAlgHom ↔ α.conjugate e = β := by
  constructor
  · intro he
    ext g b
    simpa only [conjugate_apply, StarAlgEquiv.toNonUnitalStarAlgHom_apply,
      e.apply_symm_apply] using he.apply g (e.symm b)
  · rintro rfl
    exact IsEquivariant.conjugate α e

/-- The preimage of an invariant subset under an equivariant homomorphism is invariant. -/
theorem isInvariant_preimage (hf : α.IsEquivariant β f) {s : Set B}
    (hs : β.IsInvariant s) : α.IsInvariant (f ⁻¹' s) := by
  intro g a ha
  simpa only [Set.mem_preimage, hf.apply] using hs.apply_mem g ha

/-- The image of an invariant subset under an equivariant homomorphism is invariant. -/
theorem isInvariant_image (hf : α.IsEquivariant β f) {s : Set A}
    (hs : α.IsInvariant s) : β.IsInvariant (f '' s) := by
  intro g _
  rintro ⟨a, ha, rfl⟩
  exact ⟨α g a, hs.apply_mem g ha, hf.apply g a⟩

/-- The range of an equivariant homomorphism is invariant. -/
theorem isInvariant_range (hf : α.IsEquivariant β f) :
    β.IsInvariant (f.range : Set B) := by
  rw [NonUnitalStarAlgHom.coe_range]
  simpa only [Set.image_univ] using hf.isInvariant_image IsInvariant.univ

end IsEquivariant

section Restrict

variable (α : CStarAction G A) (S : NonUnitalStarSubalgebra ℂ A)
  (hS : α.IsInvariant (S : Set A)) [IsClosed (S : Set A)]

/-- Restriction of an action to a closed invariant nonunital star subalgebra. -/
def restrict : CStarAction G S where
  toMonoidHom :=
    { toFun g :=
        { toFun := fun a ↦ ⟨α g a, hS.apply_mem g a.property⟩
          invFun := fun a ↦ ⟨α g⁻¹ a, hS.apply_mem g⁻¹ a.property⟩
          left_inv := fun a ↦ Subtype.ext (α.inv_apply_apply g a)
          right_inv := fun a ↦ Subtype.ext (α.apply_inv_apply g a)
          map_add' := fun _ _ ↦ Subtype.ext (map_add (α g) _ _)
          map_mul' := fun _ _ ↦ Subtype.ext (map_mul (α g) _ _)
          map_star' := fun _ ↦ Subtype.ext (map_star (α g) _)
          map_smul' := fun _ _ ↦ Subtype.ext (map_smul (α g) _ _) }
      map_one' := by
        ext a
        exact α.one_apply a
      map_mul' g h := by
        ext a
        exact α.mul_apply g h a }
  continuous_orbit a := (α.continuous_orbit a).subtype_mk _

@[simp]
theorem coe_restrict_apply (g : G) (a : S) :
    ((α.restrict S hS g a : S) : A) = α g a := (rfl)

/-- The inclusion of a closed invariant subalgebra is equivariant for the restricted action. -/
theorem isEquivariant_subtype :
    (α.restrict S hS).IsEquivariant α (NonUnitalStarSubalgebraClass.subtype S) :=
  fun g a ↦ α.coe_restrict_apply S hS g a

end Restrict

end TauCeti.CStarAction
