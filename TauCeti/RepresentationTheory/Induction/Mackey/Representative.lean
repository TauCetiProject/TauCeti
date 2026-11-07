/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Induction.Mackey.Basic
public import TauCeti.CategoryTheory.Action.Restriction
import Mathlib.Tactic.Group

/-!
# Changing representatives in Mackey intertwining spaces

Replacing a representative `s` of `H \ G / K` by `h₁ * s * h₂`, with `h₁ ∈ H` and
`h₂ ∈ K`, identifies the corresponding intertwining spaces. The identification sends `f`
at the new representative to `B(h₂) ∘ f ∘ A(h₁)` at the old representative. It is linear
and natural in both representations. In particular it preserves the actual intertwining
spaces, rather than only their dimensions or the vanishing of their character pairings.

`Action.mackeyHomCongr` works for actions in any linear category, including modules and
finite-dimensional representations. Its definition uses restriction along the conjugation
isomorphism of the intersection subgroups. The transport depends on the supplied `h₁` and
`h₂`; no canonical choice of such elements is asserted.

## References

* C. W. Curtis and I. Reiner, *Methods of Representation Theory*, Vol. I, §10.
-/

public section

open CategoryTheory TauCeti

namespace Action

universe u v w t

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {k : Type t} [Semiring k] [Linear k C]
  {G : Type w} [Group G] {H K : Subgroup G}

/-- Changing `s` to `h₁ * s * h₂` in a Mackey intertwining space. The map goes from the
new representative to the old one, by precomposition with `A(h₁)` and postcomposition
with `B(h₂)`. No finiteness or semisimplicity assumption is needed. -/
noncomputable def mackeyHomCongr (k : Type t) [Semiring k] [Linear k C]
    (A : Action C H) (B : Action C K)
    {h₁ h₂ : G} (hh₁ : h₁ ∈ H) (hh₂ : h₂ ∈ K) (s : G) :
    ((res C ((mackeySubgroup (h₁ * s * h₂) K H).subgroupOf H).subtype).obj A ⟶
      (res C (mackeyToH (h₁ * s * h₂) K H)).obj B) ≃ₗ[k]
    ((res C ((mackeySubgroup s K H).subgroupOf H).subtype).obj A ⟶
      (res C (mackeyToH s K H)).obj B) :=
  let e := mackeySubgroupOfCongr hh₁ hh₂ s
  let F := res C e.toMonoidHom
  letI : F.Full := full_res C e.toMonoidHom e.surjective
  let α : F.obj ((res C
      ((mackeySubgroup (h₁ * s * h₂) K H).subgroupOf H).subtype).obj A) ≅
      (res C ((mackeySubgroup s K H).subgroupOf H).subtype).obj A :=
    mkIso (ρAut A (⟨h₁, hh₁⟩ : H)⁻¹).asIso <|
      res_ρ_comm_ρAut_hom A (⟨h₁, hh₁⟩ : H)⁻¹ _ _ _ fun y => Subtype.ext (by
        simp only [e, MulEquiv.coe_toMonoidHom,
          Subgroup.coe_subtype, coe_mackeySubgroupOfCongr_apply, Subgroup.coe_mul,
          Subgroup.coe_inv]
        group)
  let β : F.obj ((res C (mackeyToH (h₁ * s * h₂) K H)).obj B) ≅
      (res C (mackeyToH s K H)).obj B :=
    mkIso (ρAut B ⟨h₂, hh₂⟩).asIso <|
      res_ρ_comm_ρAut_hom B ⟨h₂, hh₂⟩ _ _ _ fun y => Subtype.ext (by
        simp only [e, MulEquiv.coe_toMonoidHom,
          coe_mackeyToH_apply, coe_mackeySubgroupOfCongr_apply, Subgroup.coe_mul]
        group)
  (F.homLinearEquiv k _ _).trans (Linear.homCongr k α β)

/-- The representative transport on underlying morphisms. -/
@[simp]
theorem mackeyHomCongr_apply_hom (A : Action C H) (B : Action C K)
    {h₁ h₂ : G} (hh₁ : h₁ ∈ H) (hh₂ : h₂ ∈ K) (s : G)
    (f : (res C ((mackeySubgroup (h₁ * s * h₂) K H).subgroupOf H).subtype).obj A ⟶
      (res C (mackeyToH (h₁ * s * h₂) K H)).obj B) :
    ((mackeyHomCongr k A B hh₁ hh₂ s f).hom : A.V ⟶ B.V) =
      (A.ρ ⟨h₁, hh₁⟩).asHom ≫ (f.hom : A.V ⟶ B.V) ≫ (B.ρ ⟨h₂, hh₂⟩).asHom := by
  simp only [mackeyHomCongr, LinearEquiv.trans_apply, Functor.homLinearEquiv_apply,
    Linear.homCongr_apply, comp_hom, res_map_hom]
  simp only [MulEquiv.toMonoidHom_eq_coe, map_inv, Aut.inv_asIso]
  -- Restriction retains the underlying object. After reducing the MonoidHom and Aut
  -- projections in ρAut, the remaining equality is associativity in the original Hom space.
  exact Category.assoc _ _ _

/-- The inverse representative transport on underlying morphisms. -/
@[simp]
theorem mackeyHomCongr_symm_apply_hom (A : Action C H) (B : Action C K)
    {h₁ h₂ : G} (hh₁ : h₁ ∈ H) (hh₂ : h₂ ∈ K) (s : G)
    (f : (res C ((mackeySubgroup s K H).subgroupOf H).subtype).obj A ⟶
      (res C (mackeyToH s K H)).obj B) :
    (((mackeyHomCongr k A B hh₁ hh₂ s).symm f).hom : A.V ⟶ B.V) =
      (A.ρ (⟨h₁, hh₁⟩ : H)⁻¹).asHom ≫ (f.hom : A.V ⟶ B.V) ≫ (B.ρ (⟨h₂, hh₂⟩ : K)⁻¹).asHom := by
  let φ : A.V ⟶ B.V := f.hom
  let ψ : A.V ⟶ B.V := ((mackeyHomCongr k A B hh₁ hh₂ s).symm f).hom
  have h := congrArg Hom.hom ((mackeyHomCongr k A B hh₁ hh₂ s).apply_symm_apply f)
  rw [mackeyHomCongr_apply_hom] at h
  -- All restrictions retain the underlying objects; use their common Hom space.
  change (A.ρ ⟨h₁, hh₁⟩).asHom ≫ ψ ≫ (B.ρ ⟨h₂, hh₂⟩).asHom = φ at h
  change ψ = (A.ρ (⟨h₁, hh₁⟩ : H)⁻¹).asHom ≫ φ ≫
    (B.ρ (⟨h₂, hh₂⟩ : K)⁻¹).asHom
  rw [← h]
  -- Associate left to cancel the source action with its inverse, then right to cancel
  -- the target action with its inverse. End multiplication reverses composition order.
  simp only [← Category.assoc, ← End.mul_asHom, ← map_mul, mul_inv_cancel,
    map_one, End.one_asHom, Category.id_comp]
  simp only [Category.assoc, ← End.mul_asHom, ← map_mul, inv_mul_cancel,
    map_one, End.one_asHom, Category.comp_id]

/-- Representative transport is contravariantly natural in the source action. -/
theorem mackeyHomCongr_naturality_left {A A' : Action C H} (B : Action C K)
    {h₁ h₂ : G} (hh₁ : h₁ ∈ H) (hh₂ : h₂ ∈ K) (s : G) (a : A' ⟶ A)
    (f : (res C ((mackeySubgroup (h₁ * s * h₂) K H).subgroupOf H).subtype).obj A ⟶
      (res C (mackeyToH (h₁ * s * h₂) K H)).obj B) :
    mackeyHomCongr k A' B hh₁ hh₂ s
        ((res C ((mackeySubgroup (h₁ * s * h₂) K H).subgroupOf H).subtype).map a ≫ f) =
      (res C ((mackeySubgroup s K H).subgroupOf H).subtype).map a ≫
        mackeyHomCongr k A B hh₁ hh₂ s f := by
  apply Hom.ext
  simp only [mackeyHomCongr_apply_hom, comp_hom, res_map_hom]
  let φ : A.V ⟶ B.V := f.hom
  -- Restriction changes only the action, so the compositions are in the original Hom spaces.
  change (A'.ρ ⟨h₁, hh₁⟩).asHom ≫ (a.hom ≫ φ) ≫ (B.ρ ⟨h₂, hh₂⟩).asHom =
    a.hom ≫ (A.ρ ⟨h₁, hh₁⟩).asHom ≫ φ ≫ (B.ρ ⟨h₂, hh₂⟩).asHom
  simpa only [Category.assoc] using
    congrArg (fun g : A'.V ⟶ A.V => g ≫ φ ≫ (B.ρ ⟨h₂, hh₂⟩).asHom) (a.comm ⟨h₁, hh₁⟩)

/-- Representative transport is covariantly natural in the target action. -/
theorem mackeyHomCongr_naturality_right (A : Action C H) {B B' : Action C K}
    {h₁ h₂ : G} (hh₁ : h₁ ∈ H) (hh₂ : h₂ ∈ K) (s : G)
    (f : (res C ((mackeySubgroup (h₁ * s * h₂) K H).subgroupOf H).subtype).obj A ⟶
      (res C (mackeyToH (h₁ * s * h₂) K H)).obj B) (b : B ⟶ B') :
    mackeyHomCongr k A B' hh₁ hh₂ s
        (f ≫ (res C (mackeyToH (h₁ * s * h₂) K H)).map b) =
      mackeyHomCongr k A B hh₁ hh₂ s f ≫ (res C (mackeyToH s K H)).map b := by
  apply Hom.ext
  simp only [mackeyHomCongr_apply_hom, comp_hom, res_map_hom]
  let φ : A.V ⟶ B.V := f.hom
  -- As above, use the original underlying objects to normalize the compositions.
  change (A.ρ ⟨h₁, hh₁⟩).asHom ≫ (φ ≫ b.hom) ≫ (B'.ρ ⟨h₂, hh₂⟩).asHom =
    ((A.ρ ⟨h₁, hh₁⟩).asHom ≫ φ ≫ (B.ρ ⟨h₂, hh₂⟩).asHom) ≫ b.hom
  simpa only [Category.assoc] using
    congrArg (fun g : B.V ⟶ B'.V => (A.ρ ⟨h₁, hh₁⟩).asHom ≫ φ ≫ g)
      (b.comm ⟨h₂, hh₂⟩).symm

end Action
