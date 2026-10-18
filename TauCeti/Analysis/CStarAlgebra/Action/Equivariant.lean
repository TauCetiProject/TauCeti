/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Basic
public import Mathlib.Dynamics.Flow

/-!
# Equivariant maps of C⋆-algebra actions

This file develops morphisms between point-norm continuous C⋆-actions. A nonunital star-algebra
homomorphism is equivariant when it intertwines the two actions. Equivariance is preserved by
identity, composition, pullback of the acting group, and passage to the inverse of a star-algebra
equivalence.

Mathlib's invariant-subset predicate is used to give invariant preimages and images under
equivariant maps. A closed invariant nonunital star subalgebra inherits a continuous action, and
its canonical inclusion is equivariant. These constructions are the functorial foundation for
invariant ideals, quotient actions, and crossed-product maps.

The conventions follow Dana Williams, *Crossed Products of C*-Algebras*, Chapter 2.
-/

public section

noncomputable section

namespace TauCeti.CStarAction

variable {G H A B C : Type*}
  [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]

namespace IsInvariant

variable {α : CStarAction G A} {s t : Set A}

/-- An invariant subset contains the image of each of its elements under the action. -/
theorem apply_mem (hs : _root_.IsInvariant (fun g a ↦ α g a) s)
    (g : G) {a : A} (ha : a ∈ s) : α g a ∈ s :=
  hs g ha

/-- Membership in an invariant subset is unchanged by the action. -/
@[simp]
theorem apply_mem_iff (hs : _root_.IsInvariant (fun g a ↦ α g a) s)
    (g : G) (a : A) : α g a ∈ s ↔ a ∈ s := by
  refine ⟨fun h ↦ ?_, fun ha ↦ hs g ha⟩
  simpa only [inv_apply_apply] using hs g⁻¹ h

/-- The empty subset is invariant. -/
protected theorem empty : _root_.IsInvariant (fun g a ↦ α g a) ∅ :=
  fun _ _ h ↦ h.elim

/-- The whole algebra is invariant. -/
protected theorem univ : _root_.IsInvariant (fun g a ↦ α g a) Set.univ :=
  fun _ _ _ ↦ Set.mem_univ _

/-- Intersections of invariant subsets are invariant. -/
theorem inter (hs : _root_.IsInvariant (fun g a ↦ α g a) s)
    (ht : _root_.IsInvariant (fun g a ↦ α g a) t) :
    _root_.IsInvariant (fun g a ↦ α g a) (s ∩ t) :=
  fun g _ ha ↦ ⟨hs g ha.1, ht g ha.2⟩

/-- Arbitrary intersections of invariant subsets are invariant. -/
theorem iInter {ι : Type*} {s : ι → Set A}
    (hs : ∀ i, _root_.IsInvariant (fun g a ↦ α g a) (s i)) :
    _root_.IsInvariant (fun g a ↦ α g a) (⋂ i, s i) := by
  intro g a ha
  simp only [Set.mem_iInter] at ha ⊢
  exact fun i ↦ hs i g (ha i)

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
    α.IsEquivariant γ (k.comp f) :=
  fun g ↦ (hk g).comp_left (hf g)

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
    β.IsEquivariant α e.symm.toNonUnitalStarAlgHom :=
  fun g ↦ (he g).inverse_left e.symm_apply_apply e.apply_symm_apply

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
    (hs : _root_.IsInvariant (fun g b ↦ β g b) s) :
    _root_.IsInvariant (fun g a ↦ α g a) (f ⁻¹' s) :=
  fun g ↦ (hf g).mapsTo_preimage (hs g)

/-- The image of an invariant subset under an equivariant homomorphism is invariant. -/
theorem isInvariant_image (hf : α.IsEquivariant β f) {s : Set A}
    (hs : _root_.IsInvariant (fun g a ↦ α g a) s) :
    _root_.IsInvariant (fun g b ↦ β g b) (f '' s) :=
  fun g ↦ (hf g).mapsTo_image (hs g)

/-- The range of an equivariant homomorphism is invariant. -/
theorem isInvariant_range (hf : α.IsEquivariant β f) :
    _root_.IsInvariant (fun g b ↦ β g b) (f.range : Set B) := by
  rw [NonUnitalStarAlgHom.coe_range]
  exact fun g ↦ (hf g).mapsTo_range

end IsEquivariant

section Restrict

variable (α : CStarAction G A) (S : NonUnitalStarSubalgebra ℂ A)
  (hS : _root_.IsInvariant (fun g a ↦ α g a) (S : Set A)) [IsClosed (S : Set A)]

/-- Restriction of an action to a closed invariant nonunital star subalgebra. -/
def restrict : CStarAction G S where
  toMonoidHom :=
    { toFun g :=
        { toFun := fun a ↦ ⟨α g a, hS g a.property⟩
          invFun := fun a ↦ ⟨α g⁻¹ a, hS g⁻¹ a.property⟩
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
