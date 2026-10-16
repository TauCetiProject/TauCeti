/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Group.Affine

/-!
# Morphisms of affine schemes over an affine base

For commutative `R`-algebras `A` and `B`, the scheme `Spec B` is a scheme over `Spec R` through
Mathlib's `AlgebraicGeometry.specOverSpec`. This file identifies the morphisms
`Spec B ⟶ Spec A` over `Spec R`, in the vocabulary `Scheme.Hom.IsOver` of schemes over a base,
with the `R`-algebra homomorphisms `A →ₐ[R] B`. It is the `OverClass` form of Mathlib's
`AlgebraicGeometry.Spec.homEquivAlgHom`, whose compatibility condition is the explicit equation
of structure morphisms.

In particular, for a field `K`, the `K`-points of an affine `K`-scheme `Spec A` in the
functor-of-points sense, the morphisms `Spec K ⟶ Spec A` over `Spec K`, are the
`K`-algebra homomorphisms `A →ₐ[K] K`. A bare scheme morphism `Spec K ⟶ Spec A` is a ring
homomorphism `A →+* K` and need not be `K`-linear.

A morphism `Spec B ⟶ X` over `Spec R` whose image lies in an affine open `Spec A ⟶ X` over
`Spec R` factors through it by an `R`-algebra homomorphism `A →ₐ[R] B`.

## Main declarations

* `TauCeti.AlgebraicGeometry.specOverHomEquivAlgHom`: morphisms `Spec B ⟶ Spec A` over `Spec R`
  are the `R`-algebra homomorphisms `A →ₐ[R] B`.
* `TauCeti.AlgebraicGeometry.exists_spec_map_comp_eq_of_range_subset`: a morphism over `Spec R`
  with image in an affine open over `Spec R` factors through it by an algebra homomorphism.
-/

public section

open _root_.AlgebraicGeometry CategoryTheory

namespace TauCeti.AlgebraicGeometry

universe u

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- Morphisms `Spec B ⟶ Spec A` over `Spec R` are the `R`-algebra homomorphisms `A →ₐ[R] B`.
This is Mathlib's `AlgebraicGeometry.Spec.homEquivAlgHom`, with the compatibility with the
structure morphisms expressed by `Scheme.Hom.IsOver`. -/
noncomputable def specOverHomEquivAlgHom :
    {f : Spec (.of B) ⟶ Spec (.of A) // f.IsOver (Spec (.of R))} ≃ (A →ₐ[R] B) :=
  (Equiv.subtypeEquivRight fun f ↦ by
    rw [Scheme.Hom.isOver_iff, specOverSpec_over, specOverSpec_over]).trans
    Spec.homEquivAlgHom

/-- The inverse of `specOverHomEquivAlgHom` applies `Spec` to an algebra homomorphism. -/
@[simp]
theorem coe_specOverHomEquivAlgHom_symm_apply (φ : A →ₐ[R] B) :
    (specOverHomEquivAlgHom.symm φ).1 = Spec.map (CommRingCat.ofHom (φ : A →+* B)) :=
  (rfl)

/-- Applying `Spec` to the algebra homomorphism of a morphism over `Spec R` recovers the
morphism. -/
@[simp]
theorem spec_map_specOverHomEquivAlgHom
    (f : {f : Spec (.of B) ⟶ Spec (.of A) // f.IsOver (Spec (.of R))}) :
    Spec.map (CommRingCat.ofHom (specOverHomEquivAlgHom f : A →+* B)) = f.1 := by
  rw [← coe_specOverHomEquivAlgHom_symm_apply, Equiv.symm_apply_apply]

/-- A morphism `p : Spec B ⟶ X` over `Spec R` whose image lies in the image of an open immersion
`f : Spec A ⟶ X` over `Spec R` factors through `f` by an `R`-algebra homomorphism
`A →ₐ[R] B`. -/
theorem exists_spec_map_comp_eq_of_range_subset {X : Scheme.{u}} [X.Over (Spec (.of R))]
    (f : Spec (.of A) ⟶ X) [IsOpenImmersion f] [f.IsOver (Spec (.of R))]
    (p : Spec (.of B) ⟶ X) [p.IsOver (Spec (.of R))] (h : Set.range p ⊆ Set.range f) :
    ∃ φ : A →ₐ[R] B, Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ f = p := by
  have hlift : (IsOpenImmersion.lift f p h).IsOver (Spec (.of R)) := by
    rw [Scheme.Hom.isOver_iff, ← comp_over f, IsOpenImmersion.lift_fac_assoc, comp_over]
  refine ⟨specOverHomEquivAlgHom ⟨_, hlift⟩, ?_⟩
  rw [AlgHom.toRingHom_eq_coe, spec_map_specOverHomEquivAlgHom, IsOpenImmersion.lift_fac]

end TauCeti.AlgebraicGeometry
