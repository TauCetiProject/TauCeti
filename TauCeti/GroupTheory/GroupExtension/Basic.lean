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
* `GroupExtension.relabelQuotient`: relabels the quotient term of a group extension.
* `GroupExtension.relabel`: relabels both the kernel and quotient terms of a group extension.
* `GroupExtension.Section.monoidHomComp`: transports a section along a homomorphism of extensions
  over the identity of the quotient group.
* `GroupExtension.surjective_of_comp_inl_eq`: a homomorphism of extensions over the identity of
  the quotient group is surjective as soon as it is surjective on the kernel terms.

The relabelling and homomorphism constructions are mirrored for additive groups by `to_additive`.
Central extensions also admit character twists, preserved by equivalences of extensions.
-/

public section

universe u v w

namespace GroupExtension

variable {N : Type u} {E : Type v} {G : Type w} [Group N] [Group E] [Group G]

/-- Evaluating the underlying section of a splitting agrees with evaluating the splitting. -/
@[simp]
theorem Splitting.toSection_apply {S : GroupExtension N E G} (s : S.Splitting) (g : G) :
    s.toSection g = s g := (rfl)

/-- Inclusion of the kernel intertwines the specified action with conjugation by `s`. -/
theorem Splitting.inl_smul {S : GroupExtension N E G} [SMul G N] (s : S.Splitting)
    (hact : ∀ g n, g • n = S.conjAct (s g) n) (g : G) (n : N) :
    S.inl (g • n) = s g * S.inl n * (s g)⁻¹ := by
  rw [hact, GroupExtension.inl_conjAct_comm]

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

/-- Relabel the quotient term of a group extension along a multiplicative equivalence. -/
@[to_additive /-- Relabel the quotient term of an additive group extension along an additive
equivalence. -/]
def relabelQuotient (S : GroupExtension N E G) {G' : Type*} [Group G'] (e : G ≃* G') :
    GroupExtension N E G' where
  inl := S.inl
  rightHom := e.toMonoidHom.comp S.rightHom
  inl_injective := S.inl_injective
  range_inl_eq_ker_rightHom := by
    rw [S.range_inl_eq_ker_rightHom,
      MonoidHom.ker_comp_of_injective S.rightHom e.toMonoidHom e.injective]
  rightHom_surjective := e.surjective.comp S.rightHom_surjective

/-- Relabelling the quotient preserves the inclusion of the kernel. -/
@[to_additive (attr := simp) /-- Relabelling the quotient preserves the inclusion of the
kernel. -/]
theorem relabelQuotient_inl (S : GroupExtension N E G) {G' : Type*} [Group G'] (e : G ≃* G') :
    (S.relabelQuotient e).inl = S.inl :=
  (rfl)

/-- The projection of a relabelled extension is its original projection followed by the
quotient equivalence. -/
@[to_additive (attr := simp) /-- The projection of a relabelled extension is its original
projection followed by the quotient equivalence. -/]
theorem relabelQuotient_rightHom (S : GroupExtension N E G) {G' : Type*} [Group G']
    (e : G ≃* G') :
    (S.relabelQuotient e).rightHom = e.toMonoidHom.comp S.rightHom :=
  (rfl)

/-- Relabel both the kernel and quotient terms of a group extension along multiplicative
equivalences. The middle group is unchanged. -/
@[to_additive
  /-- Relabel both the kernel and quotient terms of an additive group extension along additive
  equivalences. The middle group is unchanged. -/]
def relabel (S : GroupExtension N E G) {N' G' : Type*} [Group N'] [Group G']
    (eN : N' ≃* N) (eG : G ≃* G') : GroupExtension N' E G' :=
  (S.relabelKer eN).relabelQuotient eG

/-- The inclusion of a relabelled extension is the original inclusion after the kernel
equivalence. -/
@[to_additive (attr := simp) /-- The inclusion of a relabelled additive extension is the original
inclusion after the kernel equivalence. -/]
theorem relabel_inl (S : GroupExtension N E G) {N' G' : Type*} [Group N'] [Group G']
    (eN : N' ≃* N) (eG : G ≃* G') :
    (S.relabel eN eG).inl = S.inl.comp eN.toMonoidHom :=
  (rfl)

/-- The projection of a relabelled extension is the quotient equivalence after the original
projection. -/
@[to_additive (attr := simp) /-- The projection of a relabelled additive extension is the quotient
equivalence after the original projection. -/]
theorem relabel_rightHom (S : GroupExtension N E G) {N' G' : Type*} [Group N'] [Group G']
    (eN : N' ≃* N) (eG : G ≃* G') :
    (S.relabel eN eG).rightHom = eG.toMonoidHom.comp S.rightHom :=
  (rfl)

/-- Relabelling the quotient does not change conjugation on the kernel. -/
@[simp]
theorem _root_.TauCeti.GroupExtension.relabelQuotient_conjAct {S : GroupExtension N E G}
    {H : Type*} [Group H] (e : G ≃* H) :
    (S.relabelQuotient e).conjAct = S.conjAct := by
  ext x m
  apply S.inl_injective
  rw [← GroupExtension.relabelQuotient_inl S e, GroupExtension.inl_conjAct_comm,
    GroupExtension.relabelQuotient_inl, GroupExtension.inl_conjAct_comm]

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

section Central

variable (S : GroupExtension N E G) (hcentral : S.inl.range ≤ Subgroup.center E)

/-- The automorphism obtained by multiplying each element by its character value. -/
def twist (χ : G →* N) : MulAut E where
  toFun e := S.inl (χ (S.rightHom e)) * e
  invFun e := S.inl (χ (S.rightHom e))⁻¹ * e
  left_inv e := by simp
  right_inv e := by simp
  map_mul' e f := by
    simp only [map_mul]
    exact (show Commute (S.inl (χ (S.rightHom f))) e from
      (Subgroup.mem_center_iff.mp (hcentral ⟨_, rfl⟩) e).symm).mul_mul_mul_comm _ _

@[simp]
theorem twist_apply (χ : G →* N) (e : E) :
    twist S hcentral χ e = S.inl (χ (S.rightHom e)) * e :=
  (rfl)

@[simp]
theorem twist_symm_apply (χ : G →* N) (e : E) :
    (twist S hcentral χ).symm e = S.inl (χ (S.rightHom e))⁻¹ * e :=
  (rfl)

theorem twist_inl (χ : G →* N) (n : N) :
    twist S hcentral χ (S.inl n) = S.inl n := by
  simp

theorem rightHom_twist (χ : G →* N) (e : E) :
    S.rightHom (twist S hcentral χ e) = S.rightHom e := by
  simp

end Central

namespace Equiv

variable {E' : Type*} [Group E'] {S : GroupExtension N E G} {S' : GroupExtension N E' G}

/-- An equivalence of extensions preserves centrality of the included kernel. -/
@[to_additive
  /-- An equivalence of additive extensions preserves centrality of the included kernel. -/]
theorem inl_range_le_center (F : S.Equiv S') (hcentral : S.inl.range ≤ Subgroup.center E) :
    S'.inl.range ≤ Subgroup.center E' := by
  rintro _ ⟨n, rfl⟩
  rw [← F.map_inl]
  exact MulEquivClass.apply_mem_center F (hcentral ⟨n, rfl⟩)

@[to_additive (attr := simp)]
theorem symm_apply_apply (F : S.Equiv S') (e : E) : F.symm (F e) = e :=
  F.toMulEquiv.symm_apply_apply e

@[to_additive (attr := simp)]
theorem apply_symm_apply (F : S.Equiv S') (e : E') : F (F.symm e) = e :=
  F.toMulEquiv.apply_symm_apply e

@[to_additive (attr := simp)]
theorem symm_symm (F : S.Equiv S') : F.symm.symm = F :=
  rfl

/-- Transport through an extension equivalence preserves each character twist. -/
theorem mulAutCongr_twist (F : S.Equiv S') (hcentral : S.inl.range ≤ Subgroup.center E)
    (χ : G →* N) :
    MulAut.congr F.toMulEquiv (twist S hcentral χ) =
      twist S' (F.inl_range_le_center hcentral) χ := by
  ext e
  simp [MulAut.congr_apply, MulEquiv.trans_apply]

end Equiv

end GroupExtension
