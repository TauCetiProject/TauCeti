/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Basic
public import Mathlib.Dynamics.Flow

/-!
# Equivariant homomorphisms and invariant C⋆-subalgebras

This file develops the functorial layer of point-norm continuous C⋆-actions. An equivariant
homomorphism is a nonunital complex star-algebra homomorphism commuting with the actions.
Invariant nonunital star subalgebras can be mapped and pulled back along such homomorphisms,
and their topological closures remain invariant.

A closed invariant star subalgebra inherits the restricted point-norm continuous action. Its
canonical inclusion into the ambient algebra is equivariant. These constructions are the
coefficient-side input for functoriality and ideal exact sequences of crossed products.

The conventions follow Dana Williams, *Crossed Products of C*-Algebras*, Chapter 2.
-/

public section

noncomputable section

namespace TauCeti.CStarAction

variable {G A B C : Type*} [Group G] [TopologicalSpace G]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]

/-- An equivariant nonunital star-algebra homomorphism between C⋆-actions. -/
structure Hom (α : CStarAction G A) (β : CStarAction G B) extends A →⋆ₙₐ[ℂ] B where
  /-- The homomorphism commutes with the action of every group element. -/
  map_action' (g : G) (a : A) : toNonUnitalStarAlgHom (α g a) = β g (toNonUnitalStarAlgHom a)

namespace Hom

variable {α : CStarAction G A} {β : CStarAction G B} {γ : CStarAction G C}

/-- The underlying star-algebra homomorphism determines an equivariant homomorphism. -/
theorem toNonUnitalStarAlgHom_injective :
    Function.Injective (toNonUnitalStarAlgHom : Hom α β → A →⋆ₙₐ[ℂ] B) := by
  rintro ⟨f, hf⟩ ⟨g, hg⟩ h
  cases h
  rfl

instance : FunLike (Hom α β) A B where
  coe f := f.toNonUnitalStarAlgHom
  coe_injective _ _ h :=
    toNonUnitalStarAlgHom_injective <| NonUnitalStarAlgHom.ext fun a => congrFun h a

instance : NonUnitalAlgHomClass (Hom α β) ℂ A B where
  map_add f := map_add f.toNonUnitalStarAlgHom
  map_zero f := map_zero f.toNonUnitalStarAlgHom
  map_mul f := map_mul f.toNonUnitalStarAlgHom
  map_smulₛₗ f := map_smul f.toNonUnitalStarAlgHom

instance : StarHomClass (Hom α β) A B where
  map_star f := map_star f.toNonUnitalStarAlgHom

instance : CoeOut (Hom α β) (A →⋆ₙₐ[ℂ] B) :=
  ⟨toNonUnitalStarAlgHom⟩

@[simp]
theorem coe_toNonUnitalStarAlgHom (f : Hom α β) : ⇑f.toNonUnitalStarAlgHom = f :=
  (rfl)

@[simp]
theorem coe_mk (f : A →⋆ₙₐ[ℂ] B) (hf) : ⇑(Hom.mk f hf : Hom α β) = f :=
  (rfl)

/-- Two equivariant homomorphisms are equal if they agree on every coefficient. -/
@[ext]
theorem ext {f g : Hom α β} (h : ∀ a, f a = g a) : f = g :=
  toNonUnitalStarAlgHom_injective <| NonUnitalStarAlgHom.ext h

/-- An equivariant homomorphism commutes with the group actions. -/
@[simp]
theorem map_action (f : Hom α β) (g : G) (a : A) : f (α g a) = β g (f a) :=
  f.map_action' g a

/-- The identity equivariant homomorphism of a C⋆-action. -/
protected def id (α : CStarAction G A) : Hom α α where
  toNonUnitalStarAlgHom := NonUnitalStarAlgHom.id ℂ A
  map_action' _ _ := rfl

@[simp]
theorem id_toNonUnitalStarAlgHom (α : CStarAction G A) :
    (Hom.id α).toNonUnitalStarAlgHom = NonUnitalStarAlgHom.id ℂ A :=
  (rfl)

@[simp]
theorem coe_id (α : CStarAction G A) : ⇑(Hom.id α) = _root_.id :=
  (rfl)

@[simp]
theorem id_apply (α : CStarAction G A) (a : A) : Hom.id α a = a :=
  (rfl)

/-- Composition of equivariant homomorphisms. -/
def comp (g : Hom β γ) (f : Hom α β) : Hom α γ where
  toNonUnitalStarAlgHom := g.toNonUnitalStarAlgHom.comp f.toNonUnitalStarAlgHom
  map_action' s a :=
    calc
      g.toNonUnitalStarAlgHom (f.toNonUnitalStarAlgHom (α s a)) =
          g.toNonUnitalStarAlgHom (β s (f.toNonUnitalStarAlgHom a)) :=
        congrArg g.toNonUnitalStarAlgHom (f.map_action' s a)
      _ = γ s (g.toNonUnitalStarAlgHom (f.toNonUnitalStarAlgHom a)) :=
        g.map_action' s (f.toNonUnitalStarAlgHom a)

@[simp]
theorem comp_toNonUnitalStarAlgHom (g : Hom β γ) (f : Hom α β) :
    (g.comp f).toNonUnitalStarAlgHom =
      g.toNonUnitalStarAlgHom.comp f.toNonUnitalStarAlgHom :=
  (rfl)

@[simp]
theorem coe_comp (g : Hom β γ) (f : Hom α β) : ⇑(g.comp f) = g ∘ f :=
  (rfl)

@[simp]
theorem comp_apply (g : Hom β γ) (f : Hom α β) (a : A) : g.comp f a = g (f a) :=
  (rfl)

@[simp]
theorem comp_id (f : Hom α β) : f.comp (Hom.id α) = f := by
  ext
  rfl

@[simp]
theorem id_comp (f : Hom α β) : (Hom.id β).comp f = f := by
  ext
  rfl

/-- Composition of equivariant homomorphisms is associative. -/
@[simp]
theorem comp_assoc {D : Type*} [NonUnitalCStarAlgebra D] {δ : CStarAction G D}
    (h : Hom γ δ) (g : Hom β γ) (f : Hom α β) :
    (h.comp g).comp f = h.comp (g.comp f) := by
  ext
  rfl

end Hom

end TauCeti.CStarAction

namespace IsInvariant

open TauCeti

variable {G A B : Type*} [Group G] [TopologicalSpace G]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

variable {S : NonUnitalStarSubalgebra ℂ A} {T : NonUnitalStarSubalgebra ℂ B}
  {s : Set A} {t : Set B}
  {α : CStarAction G A} {β : CStarAction G B}

/-- Apply invariance to a member of the set. -/
theorem apply_mem (hs : _root_.IsInvariant (fun g a => α g a) s)
    (g : G) {a : A} (ha : a ∈ s) : α g a ∈ s :=
  hs g ha

/-- Invariance under a group action can equivalently be stated as equality with every image. -/
theorem image_eq {s : Set A} (hs : _root_.IsInvariant (fun g a => α g a) s)
    (g : G) : α g '' s = s := by
  apply Set.Subset.antisymm
  · rintro _ ⟨a, ha, rfl⟩
    exact hs g ha
  · intro a ha
    exact ⟨α g⁻¹ a, hs g⁻¹ ha, α.apply_inv_apply g a⟩

/-- A set is invariant exactly when every group element maps it onto itself. -/
theorem iff_image_eq {s : Set A} :
    _root_.IsInvariant (fun g a => α g a) s ↔ ∀ g : G, α g '' s = s := by
  constructor
  · exact fun hS g => hS.image_eq g
  · intro hS g a ha
    have : α g a ∈ α g '' s := ⟨a, ha, rfl⟩
    rwa [hS g] at this

/-- The topological closure of an invariant set is invariant. -/
theorem topologicalClosure (hs : _root_.IsInvariant (fun g a => α g a) s) :
    _root_.IsInvariant (fun g a => α g a) (closure s) := by
  intro g a ha
  exact map_mem_closure (StarAlgEquiv.isometry (α g)).continuous ha fun x hx => hs g hx

/-- The topological closure of an invariant star subalgebra is invariant. -/
theorem topologicalClosure_subalgebra
    (hS : _root_.IsInvariant (fun g a => α g a) (S : Set A)) :
    _root_.IsInvariant (fun g a => α g a) (S.topologicalClosure : Set A) :=
  hS.topologicalClosure

/-- The universal set is invariant under every C⋆-action. -/
@[simp]
theorem top (α : CStarAction G A) :
    _root_.IsInvariant (fun g a => α g a) Set.univ :=
  fun _ _ _ => Set.mem_univ _

/-- The zero singleton is invariant under every C⋆-action. -/
@[simp]
theorem singleton_zero (α : CStarAction G A) :
    _root_.IsInvariant (fun g a => α g a) {0} := by
  intro g a ha
  simp only [Set.mem_singleton_iff] at ha ⊢
  rw [ha, map_zero]

/-- The image of an invariant set under an equivariant homomorphism is invariant. -/
theorem map (hs : _root_.IsInvariant (fun g a => α g a) s)
    (f : CStarAction.Hom α β) :
    _root_.IsInvariant (fun g b => β g b) (f '' s) := by
  intro g b hb
  obtain ⟨a, ha, rfl⟩ := hb
  exact ⟨α g a, hs g ha, f.map_action g a⟩

/-- The image of an invariant star subalgebra under an equivariant homomorphism is invariant. -/
theorem map_subalgebra (hS : _root_.IsInvariant (fun g a => α g a) (S : Set A))
    (f : CStarAction.Hom α β) :
    _root_.IsInvariant (fun g b => β g b) (S.map f.toNonUnitalStarAlgHom : Set B) :=
  hS.map f

/-- The preimage of an invariant set under an equivariant homomorphism is invariant. -/
theorem comap (ht : _root_.IsInvariant (fun g b => β g b) t)
    (f : CStarAction.Hom α β) :
    _root_.IsInvariant (fun g a => α g a) (f ⁻¹' t) := by
  intro g a ha
  simpa only [Set.mem_preimage, f.map_action] using ht g ha

/-- The preimage of an invariant star subalgebra under an equivariant homomorphism is invariant. -/
theorem comap_subalgebra (hT : _root_.IsInvariant (fun g b => β g b) (T : Set B))
    (f : CStarAction.Hom α β) :
    _root_.IsInvariant (fun g a => α g a) (T.comap f.toNonUnitalStarAlgHom : Set A) :=
  hT.comap f

/-- The range of an equivariant homomorphism is an invariant star subalgebra. -/
theorem range (f : CStarAction.Hom α β) :
    _root_.IsInvariant (fun g b => β g b)
      (NonUnitalStarAlgHom.range f.toNonUnitalStarAlgHom : Set B) := by
  have htop : _root_.IsInvariant (fun g a => α g a)
      ((⊤ : NonUnitalStarSubalgebra ℂ A) : Set A) := by
    simpa only [NonUnitalStarAlgebra.coe_top] using top α
  simpa only [NonUnitalStarAlgebra.map_top] using htop.map_subalgebra f

/-- Restrict an automorphism from an action to an invariant star subalgebra. -/
def restrictEquiv (hS : _root_.IsInvariant (fun g a => α g a) (S : Set A))
    (g : G) : S ≃⋆ₐ[ℂ] S where
  toFun a := ⟨α g a, hS.apply_mem g a.property⟩
  invFun a := ⟨α g⁻¹ a, hS.apply_mem g⁻¹ a.property⟩
  left_inv a := Subtype.ext (α.inv_apply_apply g a)
  right_inv a := Subtype.ext (α.apply_inv_apply g a)
  map_add' a b := Subtype.ext (map_add (α g) (a : A) (b : A))
  map_mul' a b := Subtype.ext (map_mul (α g) (a : A) (b : A))
  map_star' a := Subtype.ext (map_star (α g) (a : A))
  map_smul' z a := Subtype.ext (map_smul (α g) z (a : A))

@[simp]
theorem coe_restrictEquiv
    (hS : _root_.IsInvariant (fun g a => α g a) (S : Set A)) (g : G) :
    ((hS.restrictEquiv g : S ≃⋆ₐ[ℂ] S) : S → S) =
      fun a => ⟨α g a, hS.apply_mem g a.property⟩ :=
  (rfl)

@[simp]
theorem restrictEquiv_apply
    (hS : _root_.IsInvariant (fun g a => α g a) (S : Set A)) (g : G) (a : S) :
    hS.restrictEquiv g a = ⟨α g a, hS.apply_mem g a.property⟩ :=
  (rfl)

/-- Restrict a C⋆-action to a closed invariant star subalgebra. -/
def restrict (hS : _root_.IsInvariant (fun g a => α g a) (S : Set A))
    [IsClosed (S : Set A)] : CStarAction G S where
  toMonoidHom :=
    { toFun := hS.restrictEquiv
      map_one' := by
        ext
        simp
      map_mul' g k := by
        ext
        simp [TauCeti.CStarAction.mul_apply] }
  continuous_orbit a :=
    (α.continuous_orbit a).subtype_mk fun g => hS.apply_mem g a.property

@[simp]
theorem restrict_apply (hS : _root_.IsInvariant (fun g a => α g a) (S : Set A))
    [IsClosed (S : Set A)] (g : G) (a : S) :
    hS.restrict g a = ⟨α g a, hS.apply_mem g a.property⟩ :=
  (rfl)

/-- The canonical inclusion of a closed invariant star subalgebra is equivariant. -/
def subtypeHom (hS : _root_.IsInvariant (fun g a => α g a) (S : Set A))
    [IsClosed (S : Set A)] :
    CStarAction.Hom hS.restrict α where
  toNonUnitalStarAlgHom := NonUnitalStarSubalgebraClass.subtype S
  map_action' _ _ := rfl

@[simp]
theorem subtypeHom_apply (hS : _root_.IsInvariant (fun g a => α g a) (S : Set A))
    [IsClosed (S : Set A)] (a : S) :
    hS.subtypeHom a = a :=
  (rfl)

end IsInvariant
