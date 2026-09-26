/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Localization.CompletedHomeomorph
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Integral

/-!
# `A_U⁺` is the sub-unit locus of the rational subset

For a rational subset `U = R(T/s)` of `X = Spa (A, A⁺)`, the coordinate ring of `U` is
`A_U = A⟨T/s⟩` and its plus ring is `A_U⁺ = completedPlusSubring`. This file identifies `A_U⁺`
with the locus of `A_U` on which every point of `U` is sub-unit:

```text
A_U⁺ = { g ∈ A⟨T/s⟩ : v_x(g) ≤ 1 for every x ∈ R(T/s) }.
```

A point of `U` is read as a point of `Spa (A_U, A_U⁺)` through
`spaCompletedLocalizationHomeomorph`, which is what makes the right-hand side a condition indexed
by `U` rather than by the adic spectrum of `A_U`. This is the value of Wedhorn's `𝒪_X⁺` on the
basis of rational subsets, the second component of his Proposition 8.16.

The two sides meet at that homeomorphism. Proposition 7.52 (1), available as
`TauCeti.ValuationSpectrum.mem_iff_forall_vle_one`, describes `A_U⁺` as the sub-unit locus of
`Spa (A_U, A_U⁺)`; transporting the quantifier along the homeomorphism replaces the adic spectrum
of `A_U` by `U`.

## What the plus ring has to satisfy

Proposition 7.52 (1) asks two things of `A_U⁺`: that it be open and that it be integrally closed
in `A⟨T/s⟩`, supplied by `TauCeti.Huber.PairOfDefinition.isOpen_completedPlusSubring` and
`TauCeti.Huber.PairOfDefinition.isIntegrallyClosedIn_completedPlusSubring`, each asking only that
`A⁺` contain the image of the ideal of definition — which the hypothesis `A₀ ≤ A⁺` carried by
`spaCompletedLocalizationHomeomorph` already gives. As in
`Spa/Localization/CompletedHomeomorph.lean` and `Spa/Localization/CompletedRationalSubset.lean`,
no completeness, Tate or Noetherian hypothesis enters and `A⁺` is otherwise an arbitrary subring.

## Main results

* `TauCeti.ValuationSpectrum.mem_completedPlusSubring_iff_forall_mem_rationalSubset_vle_one`:
  membership in `A_U⁺` is sub-unitness at every point of `R(T/s)`.
* `TauCeti.ValuationSpectrum.coe_completedPlusSubring_eq_setOf_forall_mem_rationalSubset_vle_one`:
  the same statement as the displayed set equality.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Proposition 7.52 (1) and
  Proposition 8.16.
-/

public section

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber TauCeti.Huber.PairOfDefinition UniformSpace

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- **`A_U⁺` is the sub-unit locus of `U`** — the value of Wedhorn's `𝒪_X⁺` on a rational subset,
which is the second component of his Proposition 8.16. An element of `A⟨T/s⟩` lies in `A_U⁺`
exactly when its value is at most `1` at every point of `R(T/s)`, each point being read as a point
of `Spa (A⟨T/s⟩, A_U⁺)` through `spaCompletedLocalizationHomeomorph`. -/
-- Deliberately not `@[simp]`: `TauCeti.Huber.PairOfDefinition.mem_completedPlusSubring_iff` is
-- already a simp lemma and rewrites `g ∈ completedPlusSubring …` to `g ∈ closure (…)`, so this
-- left-hand side is not in simp-normal form. `lake build` accepts the attribute;
-- `scripts/lint-env.sh` reports a new simpNF violation.
theorem mem_completedPlusSubring_iff_forall_mem_rationalSubset_vle_one (P : PairOfDefinition A)
    (Aplus : Subring A) (hP : P.ringOfDefinition ≤ Aplus) (T : Finset A) (s : A) (S : Type*)
    [CommRing S] [Algebra A S] [IsLocalization.Away s S] (hden : HasDenominatorPower P T s S) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    ∀ g : Completion S, g ∈ completedPlusSubring P Aplus T s S hden ↔
      ∀ (x : ↥(spa Aplus)) (hx : (x : Spv A) ∈ rationalSubset Aplus T s),
        ((spaCompletedLocalizationHomeomorph P Aplus hP T s S hden).symm ⟨x, hx⟩ :
          Spv (Completion S)).toValuativeRel.vle g 1 := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  -- Proposition 7.52 (1) is a statement about a Huber ring, and `A⟨T/s⟩` is one
  have _ := isHuberRing_completion_locTopology P T s S hden
  -- `A₀ ≤ A⁺` supplies in particular the image of the ideal of definition, which is all that the
  -- two conditions 7.52 (1) puts on a plus ring ask for
  have _ := isIntegrallyClosedIn_completedPlusSubring P Aplus (fun j _ ↦ hP j.2) T s S hden
  -- 7.52 (1) quantifies over `Spa (A⟨T/s⟩, A_U⁺)`; the homeomorphism carries that quantifier
  -- to one over `R(T/s)`
  exact fun g ↦ (mem_iff_forall_vle_one
      (isOpen_completedPlusSubring P Aplus (fun j _ ↦ hP j.2) T s S hden)).trans <|
    (Subtype.forall (q := fun v ↦ (v : Spv (Completion S)).toValuativeRel.vle g 1)).symm.trans <|
      (spaCompletedLocalizationHomeomorph P Aplus hP T s S hden).symm.surjective.forall.trans
        Subtype.forall

/-- **`A_U⁺` is the sub-unit locus of `U`**, as the set equality Wedhorn displays in the proof of
his Proposition 8.16. -/
theorem coe_completedPlusSubring_eq_setOf_forall_mem_rationalSubset_vle_one (P : PairOfDefinition A)
    (Aplus : Subring A) (hP : P.ringOfDefinition ≤ Aplus) (T : Finset A) (s : A) (S : Type*)
    [CommRing S] [Algebra A S] [IsLocalization.Away s S] (hden : HasDenominatorPower P T s S) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    (completedPlusSubring P Aplus T s S hden : Set (Completion S)) =
      {g | ∀ (x : ↥(spa Aplus)) (hx : (x : Spv A) ∈ rationalSubset Aplus T s),
        ((spaCompletedLocalizationHomeomorph P Aplus hP T s S hden).symm ⟨x, hx⟩ :
          Spv (Completion S)).toValuativeRel.vle g 1} :=
  Set.ext (mem_completedPlusSubring_iff_forall_mem_rationalSubset_vle_one P Aplus hP T s S hden)

end TauCeti.ValuationSpectrum

end
