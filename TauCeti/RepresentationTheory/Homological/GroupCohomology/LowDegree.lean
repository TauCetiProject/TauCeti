/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

import Mathlib.GroupTheory.OrderOfElement
import Mathlib.CategoryTheory.Abelian.ShortExact
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import TauCeti.RepresentationTheory.Invariants

/-!
# Low-degree group cohomology

For a trivial representation `A` of a group `G`, Mathlib identifies `H¹(G, A)` with the group of
additive homomorphisms `G →+ A`. This file records the consequence that `H¹(G, A)` vanishes when
`G` is finite and `A` has no additive torsion, since a homomorphism from a finite group into a
torsion-free group is zero.

It also records the `H¹` criterion for taking invariants to preserve a short exact sequence
`0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0`. The general result for `G`-invariants follows from the degree-zero
part of Mathlib's long exact cohomology sequence. The result for a normal subgroup `S` applies it
to the restricted sequence and retains the quotient-group action.

## Main statements

* `TauCeti.groupCohomology.isZero_H1_of_isTrivial`: `H¹(G, A) = 0` for a trivial representation `A`
  of a finite group `G` without additive torsion.
* `TauCeti.groupCohomology.shortExact_map_invariantsFunctor`: taking `G`-invariants preserves a
  short exact sequence when `H¹(G, X₁) = 0`.
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

variable (k G) in
/-- Taking invariants preserves a short exact sequence of `G`-representations when the first
cohomology of its kernel vanishes. -/
theorem shortExact_map_invariantsFunctor {X : ShortComplex (Rep k G)}
    (hX : X.ShortExact) (h1 : IsZero (groupCohomology X.X₁ 1)) :
    (X.map (invariantsFunctor k G)).ShortExact := by
  have h0 : (X.map (functor k G 0)).ShortExact := by
    refine { exact := mapShortComplex₂_exact hX 0, mono_f := ?_, epi_g := ?_ }
    · -- The first map of `X.map (functor k G 0)` unfolds to the degree-zero
      -- cohomology map; rewriting `functor_map` alone does not unfold the
      -- mapped short complex's `f` projection.
      change Mono (map (MonoidHom.id G) X.f 0)
      exact @mono_map_0_of_mono _ _ _ _ _ _ X.f hX.mono_f
    · exact (mapShortComplex₃_exact hX (i := 0) (j := 1) rfl).epi_f
        (h1.eq_of_tgt _ _)
  exact ShortComplex.shortExact_of_iso
    (ShortComplex.isoMk (H0Iso X.X₁) (H0Iso X.X₂) (H0Iso X.X₃)
      (by exact (map_id_comp_H0Iso_hom X.f).symm)
      (by exact (map_id_comp_H0Iso_hom X.g).symm)) h0

variable (S : Subgroup G) [S.Normal]

/-- If `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` is short exact and `H¹(S, X₁) = 0`, then taking `S`-invariants
preserves short exactness as a sequence of representations of `G ⧸ S`. -/
theorem shortExact_map_quotientToInvariantsFunctor {X : ShortComplex (Rep k G)}
    (hX : X.ShortExact) (h1 : IsZero (groupCohomology (res S.subtype X.X₁) 1)) :
    (X.map (quotientToInvariantsFunctor k S)).ShortExact := by
  have hXS : (X.map (resFunctor S.subtype)).ShortExact :=
    (Rep.shortExact_res S.subtype).2 hX
  have h := shortExact_map_invariantsFunctor k S hXS h1
  exact (CategoryTheory.ShortExact.reflects_shortExact_of_faithful
    (forget₂ (Rep k (G ⧸ S)) (ModuleCat k))) (by
      -- After forgetting the quotient action, the object and maps of
      -- `quotientToInvariantsFunctor` unfold to invariants of the restriction;
      -- rewriting functor composition alone does not identify these fields.
      change ((X.map (resFunctor S.subtype)).map (invariantsFunctor k S)).ShortExact
      exact h)

end TauCeti.groupCohomology
