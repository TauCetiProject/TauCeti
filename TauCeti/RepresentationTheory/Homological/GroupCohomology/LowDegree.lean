/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import TauCeti.RepresentationTheory.Invariants

/-!
# Low-degree group cohomology

For a trivial representation `A` of a group `G`, Mathlib identifies `H¹(G, A)` with the group of
additive homomorphisms `G →+ A`. This file records the consequence that `H¹(G, A)` vanishes when
`G` is finite and `A` has no additive torsion, since a homomorphism from a finite group into a
torsion-free group is zero.

It also records the `H¹` criterion for taking invariants under a normal subgroup `S` to preserve a
short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0`: it suffices that `H¹(S, X₁) = 0`, since an
`S`-invariant element of `X₃` lifts to `X₂` up to a `1`-cocycle of `S` with values in `X₁`.

## Main statements

* `TauCeti.groupCohomology.isZero_H1_of_isTrivial`: `H¹(G, A) = 0` for a trivial representation `A`
  of a finite group `G` without additive torsion.
* `TauCeti.groupCohomology.shortExact_map_quotientToInvariantsFunctor`: taking `S`-invariants
  preserves a short exact sequence whose kernel `X₁` has `H¹(S, X₁) = 0`.
-/

public noncomputable section

universe u

open CategoryTheory Limits Rep

namespace TauCeti.groupCohomology

open _root_.groupCohomology

variable {k G : Type u} [CommRing k] [Group G]

/-- `H¹(G, A) = 0` for a trivial representation `A` of a finite group `G` whose underlying module
has no additive torsion. -/
theorem isZero_H1_of_isTrivial [Finite G] (A : Rep k G) [A.IsTrivial] [IsAddTorsionFree A] :
    IsZero (groupCohomology A 1) :=
  -- `H¹(G, A)` is `Hom(G, A)`, and a homomorphism from a finite group to a torsion-free group
  -- vanishes
  have : Subsingleton (Additive G →+ A) := subsingleton_of_forall_eq 0 fun f ↦
    AddMonoidHom.ext fun g ↦ (f.isOfFinAddOrder (isOfFinAddOrder_of_finite g)).eq_zero'
  (ModuleCat.isZero_of_subsingleton (ModuleCat.of k (Additive G →+ A))).of_iso <|
    H1IsoOfIsTrivial A

variable (S : Subgroup G) [S.Normal]

/-- **Taking invariants preserves a short exact sequence when `H¹` of its kernel vanishes.** If
`0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` is short exact and `H¹(S, X₁) = 0`, then so is
`0 ⟶ X₁^S ⟶ X₂^S ⟶ X₃^S ⟶ 0` as a sequence of representations of `G ⧸ S`. Only surjectivity on
the right needs the hypothesis. -/
theorem shortExact_map_quotientToInvariantsFunctor {X : ShortComplex (Rep k G)}
    (hX : X.ShortExact) (h1 : IsZero (groupCohomology (res S.subtype X.X₁) 1)) :
    (X.map (quotientToInvariantsFunctor k S)).ShortExact := by
  -- Mathlib has no evaluation lemmas for `quotientToInvariantsFunctor` or for a short complex
  -- mapped by `forget₂`: both act on elements through the underlying maps of `X`, by definition.
  -- The type ascriptions below and the final `change` read the goals in that form.
  have hf := (Rep.mono_iff_injective X.f).1 hX.mono_f
  have hex : ∀ y : X.X₂, X.g.hom y = 0 → ∃ x, X.f.hom x = y :=
    (ShortComplex.moduleCat_exact_iff _).1 (hX.exact.map (forget₂ (Rep k G) (ModuleCat k)))
  -- The action identity shared by both steps below: `X.f` commutes with the action of `S`.
  have hρ : ∀ (s : S) (x : X.X₁), X.f.hom ((res S.subtype X.X₁).ρ s x) = X.X₂.ρ s (X.f.hom x) :=
    fun s x => hom_comm_apply X.f s.1 x
  refine
    { exact := (forget₂ (Rep k (G ⧸ S)) (ModuleCat k)).reflects_exact_of_faithful _ <|
        (ShortComplex.moduleCat_exact_iff _).2 fun y hy => ?_
      mono_f := (Rep.mono_iff_injective _).2 fun a b h => Subtype.ext (hf (congrArg Subtype.val h))
      epi_g := (Rep.epi_iff_surjective _).2 fun z => ?_ }
  · obtain ⟨x, hx⟩ := hex y.1 (congrArg Subtype.val hy)
    refine ⟨⟨x, fun s => hf ?_⟩, Subtype.ext hx⟩
    have hx' : X.f.hom x = y.1 := hx
    have h2 : X.X₂.ρ s y.1 = y.1 := y.2 s
    rw [hρ, hx', h2]
  · obtain ⟨y, hy⟩ := (Rep.epi_iff_surjective X.g).1 hX.epi_g z.1
    -- `s ↦ s • y - y` takes values in `X.X₁`, where it is a `1`-cocycle of `S`.
    have hc : ∀ s : S, ∃ x : X.X₁, X.f.hom x = X.X₂.ρ s y - y := fun s =>
      hex _ (by rw [map_sub, hom_comm_apply, hy]; exact sub_eq_zero.2 (z.2 s))
    choose c hc using hc
    have hcoc : c ∈ cocycles₁ (res S.subtype X.X₁) := by
      rw [mem_cocycles₁_iff]
      intro s t
      apply hf
      simp only [map_add, hρ, hc, map_sub, Subgroup.coe_mul, map_mul, Module.End.mul_apply]
      abel
    -- It is a coboundary `s ↦ s • x - x`, and `y - x` is the required invariant lift.
    obtain ⟨x, hx⟩ := (H1π_eq_zero_iff (A := res S.subtype X.X₁) ⟨c, hcoc⟩).1
      ((ModuleCat.subsingleton_of_isZero h1).elim _ _)
    have hx' : ∀ s : S, (res S.subtype X.X₁).ρ s x = c s + x := fun s =>
      sub_eq_iff_eq_add.1 (congr_fun hx s)
    have hgf : X.g.hom (X.f.hom x) = 0 := congrArg (fun φ => φ.hom x) X.zero
    refine ⟨⟨y - X.f.hom x, fun s => ?_⟩, Subtype.ext ?_⟩
    · rw [MonoidHom.comp_apply, Subgroup.coe_subtype, map_sub, ← hρ, hx', map_add, hc]
      abel
    · change X.g.hom (y - X.f.hom x) = z.1
      rw [map_sub, hy, hgf, sub_zero]

end TauCeti.groupCohomology
