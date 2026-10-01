/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AbelianVariety.Hom.Rigidity
public import TauCeti.AlgebraicGeometry.AbelianVariety.Trivial

/-!
# The Albanese property of a pointed morphism to an abelian variety

Let `X` be a scheme over a field `K` with a `K`-rational point `x₀ : Spec K ⟶ X`, written as a
morphism `𝟙_ (Over (Spec K)) ⟶ X` over `Spec K`. A pointed morphism `a : X ⟶ J` to an abelian
variety `J` (one sending `x₀` to the identity of `J`) has the **Albanese property** if every
pointed morphism `f : X ⟶ A` to an abelian variety `A` factors as `f = a ≫ φ` through a *unique
homomorphism* `φ : J ⟶ A` of abelian varieties. This is the universal property characterizing the
Jacobian `Jac X = Pic⁰ X` of a smooth proper geometrically connected curve together with its
Abel–Jacobi morphism `aj : X ⟶ Jac X`, `x₀ ↦ 0`: for curves the Jacobian is the Albanese variety.

The universal property makes any two solutions canonically isomorphic (`IsAlbanese.uniqueIso`), so
independently built Jacobians are compared through it rather than through their constructions.
Every abelian variety `A`, pointed at its identity, is its own Albanese variety via the identity
morphism (`isAlbanese_id`), because pointed morphisms between abelian varieties are homomorphisms
(`AbelianVariety.Hom.equivPointed`, a consequence of the rigidity lemma). Combined with
`IsAlbanese.uniqueIso`, any Albanese morphism `a : A ⟶ J` for `(A, 0)` therefore identifies `J`
with `A`; this is the form of the genus-one comparison `Jac (E, O) ≅ E` once an elliptic curve is
known to be an abelian variety.

## Main declarations

* `AbelianVariety.IsAlbanese x₀ a`: the pointed morphism `a : X ⟶ J.toOver` has the Albanese
  property;
* `AbelianVariety.IsAlbanese.homEquiv`: homomorphisms `J ⟶ A` are in bijection with pointed
  morphisms `X ⟶ A.toOver`, by composition with `a`;
* `AbelianVariety.IsAlbanese.lift`, `AbelianVariety.IsAlbanese.fac`,
  `AbelianVariety.IsAlbanese.hom_ext`: the factorization of a pointed morphism through `a` and its
  uniqueness;
* `AbelianVariety.IsAlbanese.uniqueIso`: two Albanese morphisms from the same pointed scheme have
  isomorphic targets, compatibly with the morphisms;
* `AbelianVariety.IsAlbanese.of_iso`: the Albanese property is transported along isomorphisms of
  the target;
* `AbelianVariety.isAlbanese_id`: an abelian variety pointed at its identity is its own Albanese
  variety;
* `AbelianVariety.isAlbanese_trivial`: the Albanese variety of `Spec K` is the trivial abelian
  variety.

## References

* J. S. Milne, *Jacobian varieties*, in *Arithmetic Geometry* (G. Cornell and J. H. Silverman,
  eds.), Springer, 1986, Section 6 (the universal property of the Abel–Jacobi map).
* J. S. Milne, *Abelian Varieties*, Corollary 1.2 (pointed morphisms of abelian varieties are
  homomorphisms).
-/

public section

open CategoryTheory MonoidalCategory MonObj

open scoped CategoryTheory.MonObj

namespace TauCeti

namespace AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

namespace AbelianVariety

variable {K : Type u} [Field K]

open Hom

/-- A pointed morphism `a : X ⟶ J.toOver` from a scheme `X` over `K` with a `K`-rational point
`x₀` to an abelian variety `J` has the **Albanese property** if every morphism `f : X ⟶ A.toOver`
to an abelian variety sending `x₀` to the identity factors as `f = a ≫ φ` through a unique
homomorphism `φ : J ⟶ A` of abelian varieties. -/
structure IsAlbanese {X : Over (Spec (.of K))} (x₀ : 𝟙_ (Over (Spec (.of K))) ⟶ X)
    {J : AbelianVariety K} (a : X ⟶ J.toOver) : Prop where
  /-- The morphism `a` sends the base point `x₀` to the identity of `J`. -/
  comp_eq_one : x₀ ≫ a = η[J.toOver]
  /-- Every pointed morphism to an abelian variety factors uniquely through `a` by a
  homomorphism. -/
  existsUnique_fac (A : AbelianVariety K) (f : X ⟶ A.toOver) (hf : x₀ ≫ f = η[A.toOver]) :
    ∃! φ : J ⟶ A, a ≫ toOverHom φ = f

variable {X : Over (Spec (.of K))} {x₀ : 𝟙_ (Over (Spec (.of K))) ⟶ X}

/-- Composing a pointed morphism with a homomorphism of abelian varieties gives a pointed
morphism. -/
lemma comp_toOverHom_eq_one {J A : AbelianVariety K} {a : X ⟶ J.toOver}
    (ha : x₀ ≫ a = η[J.toOver]) (φ : J ⟶ A) : x₀ ≫ a ≫ toOverHom φ = η[A.toOver] := by
  rw [reassoc_of% ha, one_hom]

namespace IsAlbanese

variable {J : AbelianVariety K} {a : X ⟶ J.toOver} (h : IsAlbanese x₀ a)

include h

/-- Homomorphisms out of the Albanese variety `J` are the pointed morphisms out of `X`: a
homomorphism `φ : J ⟶ A` corresponds to `a ≫ φ`. -/
noncomputable def homEquiv (A : AbelianVariety K) :
    (J ⟶ A) ≃ {f : X ⟶ A.toOver // x₀ ≫ f = η[A.toOver]} :=
  Equiv.ofBijective (fun φ ↦ ⟨a ≫ toOverHom φ, comp_toOverHom_eq_one h.comp_eq_one φ⟩)
    ⟨fun _ ψ e ↦ (h.existsUnique_fac A _ (comp_toOverHom_eq_one h.comp_eq_one ψ)).unique
        (congrArg Subtype.val e) rfl,
      fun f ↦ (h.existsUnique_fac A f.1 f.2).exists.imp fun _ hφ ↦ Subtype.ext hφ⟩

/-- `homEquiv` sends a homomorphism `φ : J ⟶ A` to the pointed morphism `a ≫ φ`. -/
@[simp]
lemma coe_homEquiv_apply {A : AbelianVariety K} (φ : J ⟶ A) :
    (h.homEquiv A φ : X ⟶ A.toOver) = a ≫ toOverHom φ :=
  (rfl)

/-- The homomorphism `J ⟶ A` through which a pointed morphism `f : X ⟶ A.toOver` factors. -/
noncomputable def lift {A : AbelianVariety K} (f : X ⟶ A.toOver) (hf : x₀ ≫ f = η[A.toOver]) :
    J ⟶ A :=
  (h.homEquiv A).symm ⟨f, hf⟩

/-- The inverse of `homEquiv` is `lift`. -/
@[simp]
lemma homEquiv_symm_apply {A : AbelianVariety K}
    (f : {f : X ⟶ A.toOver // x₀ ≫ f = η[A.toOver]}) :
    (h.homEquiv A).symm f = h.lift f.1 f.2 :=
  (rfl)

/-- The homomorphism `lift f` factors `f` through the Albanese morphism. -/
@[reassoc (attr := simp)]
lemma fac {A : AbelianVariety K} (f : X ⟶ A.toOver) (hf : x₀ ≫ f = η[A.toOver]) :
    a ≫ toOverHom (h.lift f hf) = f :=
  congrArg Subtype.val ((h.homEquiv A).apply_symm_apply ⟨f, hf⟩)

/-- Two homomorphisms out of the Albanese variety agree once they agree after composition with
the Albanese morphism. -/
lemma hom_ext {A : AbelianVariety K} {φ ψ : J ⟶ A} (e : a ≫ toOverHom φ = a ≫ toOverHom ψ) :
    φ = ψ :=
  (h.homEquiv A).injective (Subtype.ext e)

/-- A homomorphism out of the Albanese variety is the lift of a pointed morphism exactly when it
factors that morphism. -/
lemma eq_lift_iff {A : AbelianVariety K} {f : X ⟶ A.toOver} (hf : x₀ ≫ f = η[A.toOver])
    {φ : J ⟶ A} : φ = h.lift f hf ↔ a ≫ toOverHom φ = f :=
  ⟨fun e ↦ e ▸ h.fac f hf, fun e ↦ h.hom_ext (e.trans (h.fac f hf).symm)⟩

/-- Lifting the composite of the Albanese morphism with a homomorphism recovers the
homomorphism. -/
@[simp]
lemma lift_comp_toOverHom {A : AbelianVariety K} (φ : J ⟶ A) :
    h.lift (a ≫ toOverHom φ) (comp_toOverHom_eq_one h.comp_eq_one φ) = φ :=
  ((h.eq_lift_iff _).2 rfl).symm

/-- The lift of the Albanese morphism itself is the identity. -/
@[simp]
lemma lift_self : h.lift a h.comp_eq_one = 𝟙 J :=
  ((h.eq_lift_iff _).2 (by rw [toOverHom_id, Category.comp_id])).symm

/-- Lifting is compatible with composition by a homomorphism on the target. -/
lemma lift_comp {A B : AbelianVariety K} (f : X ⟶ A.toOver) (hf : x₀ ≫ f = η[A.toOver])
    (ψ : A ⟶ B) :
    h.lift f hf ≫ ψ = h.lift (f ≫ toOverHom ψ) (comp_toOverHom_eq_one hf ψ) :=
  (h.eq_lift_iff _).2 (by rw [toOverHom_comp, fac_assoc])

/-- The Albanese variety is unique up to unique isomorphism: if `a : X ⟶ J` and `a' : X ⟶ J'`
both have the Albanese property for the base point `x₀`, then `J ≅ J'` by the isomorphism
carrying `a` to `a'`. -/
noncomputable def uniqueIso {J' : AbelianVariety K} {a' : X ⟶ J'.toOver}
    (h' : IsAlbanese x₀ a') : J ≅ J' where
  hom := h.lift a' h'.comp_eq_one
  inv := h'.lift a h.comp_eq_one
  hom_inv_id := h.hom_ext (by rw [toOverHom_comp, fac_assoc, fac, toOverHom_id, Category.comp_id])
  inv_hom_id :=
    h'.hom_ext (by rw [toOverHom_comp, fac_assoc, fac, toOverHom_id, Category.comp_id])

/-- The isomorphism `uniqueIso` carries the first Albanese morphism to the second. -/
@[reassoc (attr := simp)]
lemma fac_uniqueIso_hom {J' : AbelianVariety K} {a' : X ⟶ J'.toOver} (h' : IsAlbanese x₀ a') :
    a ≫ toOverHom (h.uniqueIso h').hom = a' :=
  h.fac a' h'.comp_eq_one

/-- The inverse of `uniqueIso` carries the second Albanese morphism to the first. -/
@[reassoc (attr := simp)]
lemma fac_uniqueIso_inv {J' : AbelianVariety K} {a' : X ⟶ J'.toOver} (h' : IsAlbanese x₀ a') :
    a' ≫ toOverHom (h.uniqueIso h').inv = a :=
  h'.fac a h.comp_eq_one

/-- The isomorphism `uniqueIso` is the only homomorphism carrying the first Albanese morphism to
the second. -/
lemma eq_uniqueIso_hom {J' : AbelianVariety K} {a' : X ⟶ J'.toOver} (h' : IsAlbanese x₀ a')
    {φ : J ⟶ J'} (e : a ≫ toOverHom φ = a') : φ = (h.uniqueIso h').hom :=
  (h.eq_lift_iff h'.comp_eq_one).2 e

/-- The Albanese property is transported along an isomorphism of the target abelian variety. -/
lemma of_iso {J' : AbelianVariety K} (e : J ≅ J') : IsAlbanese x₀ (a ≫ toOverHom e.hom) where
  comp_eq_one := comp_toOverHom_eq_one h.comp_eq_one e.hom
  existsUnique_fac A f hf := by
    refine ⟨e.inv ≫ h.lift f hf, ?_, fun ψ (hψ : _ = f) ↦ ?_⟩
    · dsimp only
      rw [Category.assoc, ← toOverHom_comp, e.hom_inv_id_assoc, fac]
    · rw [Category.assoc, ← toOverHom_comp] at hψ
      rw [← (h.eq_lift_iff hf).2 hψ, e.inv_hom_id_assoc]

end IsAlbanese

/-- An abelian variety, pointed at its identity, is its own Albanese variety via the identity
morphism: by rigidity, every pointed morphism `A ⟶ B` to an abelian variety is a homomorphism. -/
theorem isAlbanese_id (A : AbelianVariety K) : IsAlbanese η[A.toOver] (𝟙 A.toOver) where
  comp_eq_one := Category.comp_id _
  existsUnique_fac B f hf := by
    refine ⟨(equivPointed A B).symm ⟨f, hf⟩, by simp, fun φ (hφ : _ = f) ↦ ?_⟩
    rw [Category.id_comp] at hφ
    exact ((equivPointed A B).symm_apply_eq.2
      (Subtype.ext ((coe_equivPointed_apply φ).trans hφ).symm)).symm

/-- The Albanese variety of `Spec K`, pointed by the identity, is the trivial abelian variety:
the only pointed morphism out of `Spec K` is the identity section, and the trivial abelian
variety is initial. -/
theorem isAlbanese_trivial :
    IsAlbanese (𝟙 (𝟙_ (Over (Spec (.of K))))) η[(trivial K).toOver] where
  comp_eq_one := Category.id_comp _
  existsUnique_fac A f hf := by
    rw [Category.id_comp] at hf
    exact ⟨fromTrivial A, (one_hom _).trans hf.symm, fun _ _ ↦ (isInitialTrivial K).hom_ext _ _⟩

end AbelianVariety

end AlgebraicGeometry

end TauCeti
