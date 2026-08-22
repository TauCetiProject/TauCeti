/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.PresentationLimit.Basic
public import TauCeti.RingTheory.Huber.PowerBounded

/-!
# Power-bounded sections of the presentation-indexed presheaf

Wedhorn §8.1 pairs the structure presheaf with an integral subpresheaf `𝒪_X⁺`. **This file does
not define that object.** It defines the subring of sections all of whose components are
power-bounded, and proves that restriction preserves it — so the assignment is a subpresheaf of
`presentationLimitPresheaf` in the only sense available before sheafification questions arise: a
compatible family of subrings.

## What this is not: the relation to `𝒪_X⁺`

The integral subpresheaf is the *valuation-defined* object

```text
𝒪_X⁺(U) = {f ∈ 𝒪_X(U) : v_x(f_x) ≤ 1 for every x ∈ U}.
```

Power-boundedness of every component is a different predicate, and nothing here relates the two.
Identifying them needs the valuation at a point of `Spa(A,A⁺)` extended to the rational
localizations — an extension this import chain does not have — after which `𝒪_X⁺` should be
*defined* by the displayed condition and its agreement with power-boundedness proved as a
theorem. Until that exists, the declarations below are named for the condition they impose and
claim no `𝒪_X⁺` notation.

## Main definitions

* `TauCeti.ValuationSpectrum.presentationLimitPowerBoundedSubring` : the subring of
  `presentationLimitObj P Aplus V` of sections with power-bounded components.

## Main results

* `TauCeti.ValuationSpectrum.mem_presentationLimitPowerBoundedSubring_iff` : membership is
  component-wise power-boundedness.
* `TauCeti.ValuationSpectrum.presentationLimitMap_mem_presentationLimitPowerBoundedSubring` :
  restriction preserves the subring, with no continuity input — a restriction's components are a
  subset of the original's (`presentationLimitMap_π`), so the condition is inherited outright.

## Why per-component, not power-bounded in the limit ring

`presentationLimitObj P Aplus V` is itself a topological ring, so "power-bounded in it" is
statable — but a
continuous ring homomorphism need not preserve power-boundedness (`IsPowerBounded.map` needs an
image condition beyond continuity), so restriction-compatibility of that definition is a real
theorem needing real hypotheses. The component-wise definition makes compatibility a reindexing
triviality, and it is the faithful generalisation of the source's per-value definition, which it
reproduces at each component by construction.

Nothing here relates this subring to power-boundedness *in the limit ring*: neither implication
between "every component is power-bounded" and "the section is power-bounded in
`presentationLimitObj`" is proved, or used. The subring is componentwise by definition, and that
is all it is.

## Provenance

Adapted from AINTLIB's `IntegralStructureSheaf.lean` (see References), which defines
`integralPresheafValue D = powerBoundedSubring (presheafValue D)` on each rational value and
stops there — no compatibility with restriction is stated, and the sheaf-cohomology placeholders
in that file are not ported. The generalisation from per-value to a subring of every
`presentationLimitObj P Aplus V` with restriction-compatibility is new here; the nonarchimedean
instance it needs on the values comes from `isHuberRing_completion_locTopology`
(`LocalizationTopology/Completion.lean`) through the global `IsHuberRing.toNonarchimedeanRing`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), §8.1.
* [C. Birkbeck, *AINTLIB*](https://github.com/CBirkbeck/AINTLIB), branch `dev/adic-spaces`,
  commit `37bbdaeb`, `projects/AdicSpaces/Adic spaces/IntegralStructureSheaf.lean`.
-/

namespace TauCeti.ValuationSpectrum

open CategoryTheory CategoryTheory.Limits _root_.TopologicalSpace TauCeti.Huber

public section

universe v

variable {A : Type v} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  {P : PairOfDefinition A} {Aplus : Subring A} {V : Opens ↥(spa Aplus)}

variable (P) in
/-- The limit's projection at `i`, with its codomain read as that presentation's own completed
localization rather than as a value of the diagram.

The transport is definitional (`rationalDiagram_obj`) but **load-bearing**, not cosmetic:
`powerBoundedSubring` needs a `NonarchimedeanRing` instance, and at the diagram-value spelling
instance search does not find one. Using `presentationLimitπ` unascribed fails to synthesize
`NonarchimedeanRing` at the diagram-value spelling of the codomain — tested. Naming it here puts
that ascription in one place instead of at each use site. -/
noncomputable def presentationLimitπCompletion (Aplus : Subring A) (V : Opens ↥(spa Aplus))
    (i : RationalIndex P Aplus V) :
    presentationLimitObj P Aplus V ⟶ i.right.obj.completionLocObj :=
  presentationLimitπ P Aplus V i

variable (P) in
/-- **The power-bounded sections**: the subring of `presentationLimitObj P Aplus V` — the
candidate for `𝒪_X(V)`, not known to be it — of sections all of whose components
are power-bounded — the intersection over the index of the comaps of the power-bounded subrings
of the values. This is not the valuation-defined `𝒪_X⁺`; see the module docstring. -/
noncomputable def presentationLimitPowerBoundedSubring (Aplus : Subring A)
    (V : Opens ↥(spa Aplus)) :
    Subring ↥(presentationLimitObj P Aplus V) :=
  ⨅ i : RationalIndex P Aplus V,
    (powerBoundedSubring _).comap
      (presentationLimitπCompletion P Aplus V i).1.1

/-- Membership is power-boundedness of every component. -/
@[simp]
theorem mem_presentationLimitPowerBoundedSubring_iff {f : ↥(presentationLimitObj P Aplus V)} :
    f ∈ presentationLimitPowerBoundedSubring P Aplus V ↔
      ∀ i : RationalIndex P Aplus V, IsPowerBounded
        ((presentationLimitπCompletion P Aplus V i).1.1 f) := by
  simp [presentationLimitPowerBoundedSubring, Subring.mem_iInf]

/-- **Restriction preserves the power-bounded sections**: the components of a restriction are a
subset of the original section's components (`presentationLimitMap_π`), so no continuity or
boundedness of the restriction map enters. -/
theorem presentationLimitMap_mem_presentationLimitPowerBoundedSubring {V W : Opens ↥(spa Aplus)}
    (h : W ≤ V) {f : ↥(presentationLimitObj P Aplus V)}
    (hf : f ∈ presentationLimitPowerBoundedSubring P Aplus V) :
    (presentationLimitMap P h).1.1 f ∈ presentationLimitPowerBoundedSubring P Aplus W := by
  rw [mem_presentationLimitPowerBoundedSubring_iff] at hf ⊢
  intro i
  have hπ := congrArg (fun g ↦ g.1.1 f) (presentationLimitMap_π P h i)
  simpa using hπ ▸ hf ((StructuredArrow.map (homOfLE h).op).obj i)

end

end TauCeti.ValuationSpectrum
