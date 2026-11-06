/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Bicategory.Functor.EquivariantGroupoidLift.NormalizedTransport.Hom
public import TauCeti.CategoryTheory.Bicategory.Functor.EquivariantGroupoidLift.Hom.TransportEquivariance
public import TauCeti.CategoryTheory.Bicategory.Functor.EquivariantGroupoidLift.Transport
public import TauCeti.CategoryTheory.Bicategory.Functor.EquivariantGroupoidLift.Bicategory

/-!
# Normalization of morphisms of equivariant lifts

A morphism of equivariant groupoid lifts induces a morphism between their normalized
transports, including its equivariance for the prescribed actions. Normalization preserves
identities and composition, and compatible modifications identify the induced morphisms.

These are the morphism formulas for normalization on fixed prescribed fibers. They do not
assert a biequivalence of the bicategories of lifts and normalized transports. The conventions
follow Johnson–Yau, *2-Dimensional Categories*, Chapter 4.
-/

public section

universe w v u₂ v₁ u₁

namespace TauCeti.EquivariantGroupoidLift.Hom

open CategoryTheory Bicategory

variable {Γ : Type u₁} [Category.{v₁} Γ] {H : Type u₂} [Monoid H]
  {actions : Γ → LocallyDiscrete (SingleObj H) ⥤ᵖ Cat.{v, w}}
  {L L' L'' : EquivariantGroupoidLift Γ actions}

/-- Normalize a morphism of equivariant lifts on the prescribed fibers. Its comparison
along an arrow is the canonical transport isomorphism of the original morphism. -/
noncomputable def normalizedTransportHom (φ : L.Hom L') :
    L.normalizedTransport ⟶ L'.normalizedTransport where
  transportIso := φ.transportIso
  transportIso_unit := φ.transportIso_hom_app_comp_transportId
  transportIso_comp := φ.transportIso_transportComp_hom_app
  transportIso_comm := φ.transportIso_transportCommIso

-- Keep this equation named: simplifying its dependent functor endpoints does not give
-- a stable reflexivity test for the simplifier in an importing module.
lemma normalizedTransportHom_transportIso (φ : L.Hom L') {p q : Γ} (g : p ⟶ q) :
    φ.normalizedTransportHom.transportIso g = φ.transportIso g := (rfl)

/-- Normalization sends the identity lift morphism to the identity normalized comparison. -/
@[simp]
lemma id_normalizedTransportHom (L : EquivariantGroupoidLift Γ actions) :
    normalizedTransportHom (𝟙 L) = 𝟙 L.normalizedTransport := by
  rw [EquivariantGroupoidLift.id_eq]
  apply NormalizedTransport.Hom.ext
  intro p q g
  simp only [NormalizedTransport.id_transportIso, normalizedTransportHom_transportIso]
  simpa only [normalizedTransport] using id_transportIso L g

/-- Normalization preserves composition of lift morphisms on the prescribed fibers. -/
@[simp]
lemma comp_normalizedTransportHom (φ : L ⟶ L') (ψ : L' ⟶ L'') :
    normalizedTransportHom (φ ≫ ψ) = φ.normalizedTransportHom ≫ ψ.normalizedTransportHom := by
  rw [EquivariantGroupoidLift.comp_eq]
  apply NormalizedTransport.Hom.ext
  intro p q g
  simp only [NormalizedTransport.comp_transportIso, normalizedTransportHom_transportIso]
  simpa only [normalizedTransport] using comp_transportIso φ ψ g

namespace Hom₂

variable {φ ψ : L.Hom L'} (Θ : φ ⟶ ψ)

include Θ in
/-- Compatible modifications identify the normalized morphisms, including all their
equivariance and coherence data. -/
lemma normalizedTransportHom_eq : φ.normalizedTransportHom = ψ.normalizedTransportHom := by
  apply NormalizedTransport.Hom.ext
  intro p q g
  rw [normalizedTransportHom_transportIso, normalizedTransportHom_transportIso]
  simpa only [normalizedTransport] using Θ.transportIso_eq g

end Hom₂

end TauCeti.EquivariantGroupoidLift.Hom
