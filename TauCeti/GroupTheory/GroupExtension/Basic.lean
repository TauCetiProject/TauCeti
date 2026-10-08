/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupExtension.Defs

/-!
# Basic operations on group extensions

This file provides operations on an existing group extension.

## Main definitions and results

* `GroupExtension.card_fiber_rightHom`: every fiber of the projection has the cardinality of the
  kernel term.
* `GroupExtension.relabelKer`: relabels the kernel term of a group extension.
* `GroupExtension.Section.monoidHomComp`: transports a section along a homomorphism of extensions
  over the identity of the quotient group.
* `GroupExtension.surjective_of_comp_inl_eq`: a homomorphism of extensions over the identity of
  the quotient group is surjective as soon as it is surjective on the kernel terms.

The constructions are mirrored for additive groups by `to_additive`.
-/

public section

universe u v w

namespace GroupExtension

variable {N : Type u} {E : Type v} {G : Type w} [Group N] [Group E] [Group G]

/-- Every fiber of the projection in a group extension has the cardinality of its kernel term. -/
@[to_additive
  /-- Every fiber of the projection in an additive group extension has the cardinality of its
  kernel term. -/]
theorem card_fiber_rightHom (S : GroupExtension N E G) (g : G) :
    Nat.card (S.rightHom ⁻¹' {g}) = Nat.card N := by
  calc
    Nat.card (S.rightHom ⁻¹' {g}) = Nat.card S.rightHom.ker :=
      Nat.card_congr (MonoidHom.fiberEquivKerOfSurjective S.rightHom_surjective g)
    _ = Nat.card S.inl.range := by rw [S.range_inl_eq_ker_rightHom]
    _ = Nat.card N :=
      (Nat.card_congr (Equiv.ofInjective S.inl S.inl_injective)).symm

/-- Relabel the kernel term of a group extension along a multiplicative equivalence. -/
@[to_additive /-- Relabel the kernel term of an additive group extension along an additive
equivalence. -/]
def relabelKer (S : GroupExtension N E G) {N' : Type*} [Group N'] (e : N' ≃* N) :
    GroupExtension N' E G where
  inl := S.inl.comp e.toMonoidHom
  rightHom := S.rightHom
  inl_injective := S.inl_injective.comp e.injective
  range_inl_eq_ker_rightHom := by
    rw [MonoidHom.range_comp, MulEquiv.toMonoidHom_eq_coe, e.range_eq_top,
      ← MonoidHom.range_eq_map, S.range_inl_eq_ker_rightHom]
  rightHom_surjective := S.rightHom_surjective

/-- The inclusion of `S.relabelKer e` is the original inclusion after `e`. -/
@[to_additive (attr := simp)
  /-- The inclusion of `S.relabelKer e` is the original inclusion after `e`. -/]
theorem relabelKer_inl (S : GroupExtension N E G) {N' : Type*} [Group N'] (e : N' ≃* N) :
    (S.relabelKer e).inl = S.inl.comp e.toMonoidHom :=
  (rfl)

/-- Relabelling the kernel does not change the projection. -/
@[to_additive (attr := simp) /-- Relabelling the kernel does not change the projection. -/]
theorem relabelKer_rightHom (S : GroupExtension N E G) {N' : Type*} [Group N'] (e : N' ≃* N) :
    (S.relabelKer e).rightHom = S.rightHom :=
  (rfl)

section Hom

variable {N' : Type*} {E' : Type*} [Group N'] [Group E'] {S : GroupExtension N E G}
  {S' : GroupExtension N' E' G}

/-- Transport a section of an extension along a homomorphism `φ` of extensions over the identity
of the quotient group: `φ ∘ σ` is a section of the target extension. The kernel terms of the two
extensions may differ; for an equivalence of extensions with the same kernel this is
`GroupExtension.Section.equivComp`. -/
@[to_additive
  /-- Transport a section of an additive extension along a homomorphism `φ` of extensions over the
  identity of the quotient group: `φ ∘ σ` is a section of the target extension. The kernel terms of
  the two extensions may differ; for an equivalence of extensions with the same kernel this is
  `AddGroupExtension.Section.equivComp`. -/]
def Section.monoidHomComp (σ : S.Section) (φ : E →* E')
    (hright : S'.rightHom.comp φ = S.rightHom) : S'.Section where
  toFun g := φ (σ g)
  rightInverse_rightHom g := by
    rw [← MonoidHom.comp_apply, hright, Section.rightHom_section]

@[to_additive (attr := simp)]
theorem Section.monoidHomComp_apply (σ : S.Section) (φ : E →* E')
    (hright : S'.rightHom.comp φ = S.rightHom) (g : G) :
    σ.monoidHomComp φ hright g = φ (σ g) :=
  (rfl)

/-- **A homomorphism of extensions over the identity of the quotient group is surjective as soon
as its restriction `f` to the kernel terms is.** It meets every fibre of the projection, because
it covers the identity, and within a fibre it reaches every translate of the kernel, because `f`
is surjective. -/
@[to_additive
  /-- **A homomorphism of additive extensions over the identity of the quotient group is surjective
  as soon as its restriction `f` to the kernel terms is.** It meets every fibre of the projection,
  because it covers the identity, and within a fibre it reaches every translate of the kernel,
  because `f` is surjective. -/]
theorem surjective_of_comp_inl_eq (f : N →* N') (hf : Function.Surjective f) (φ : E →* E')
    (hinl : φ.comp S.inl = S'.inl.comp f) (hright : S'.rightHom.comp φ = S.rightHom) :
    Function.Surjective φ := by
  intro y
  obtain ⟨x, hx⟩ := S.rightHom_surjective (S'.rightHom y)
  have hker : (φ x)⁻¹ * y ∈ S'.inl.range := by
    rw [S'.range_inl_eq_ker_rightHom, MonoidHom.mem_ker, map_mul, map_inv, ← MonoidHom.comp_apply,
      hright, hx, inv_mul_cancel]
  obtain ⟨n, hn⟩ := hker
  obtain ⟨m, rfl⟩ := hf n
  refine ⟨x * S.inl m, ?_⟩
  rw [map_mul, ← MonoidHom.comp_apply φ S.inl, hinl, MonoidHom.comp_apply, hn, mul_inv_cancel_left]

end Hom

end GroupExtension
