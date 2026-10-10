/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 4.8

Staged for Tau Ceti, roadmap topic T14.  Mathlib is not the destination
(`ForTauCeti/README.md`); what follows is where this material would have gone on
the closed Mathlib track —
addition to
`Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/` (measurability of
`ω ↦ cfc f (a ω)`) and `Mathlib/MeasureTheory/MeasurableSpace/` (a countable
restrict-cover measurability criterion).

Formalized by Claude Opus 4.8 (claude-opus-4-8[1m]).
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
public import Mathlib.Analysis.Normed.Algebra.Spectrum
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding


/-! # Measurability of the continuous functional calculus in the element

For a *fixed* continuous `f : ℝ → ℝ`, the map `ω ↦ cfc f (a ω)` is measurable
whenever `a` is measurable and self-adjoint-valued in a C⋆-algebra `A`.

The point is that no measurable selection of an eigenbasis is needed — even
though `cfc f a = ∑ₖ f(λₖ) uₖ uₖ*` is built from eigenvectors `uₖ` that depend
*discontinuously* on `a` at eigenvalue crossings.  The functional-calculus map
`a ↦ cfc f a` is itself continuous on each set of uniformly bounded spectrum
(`continuousOn_cfc`), and `A` is covered by countably many such sets
`{a | ‖a‖ ≤ k}`; measurability glues over the cover.

This is exactly the tool that lets a "spectral embedding" `ψ̂(ω)` enter a
probability statement: while `ψ̂(ω)` (an eigenvector configuration) need not be
measurable, its Gram matrix — a rank-`d` *spectral truncation* `cfc f` of the
sample matrix — is, and the events one cares about depend only on that Gram.

## Main results

* `TauCeti.measurable_of_iUnion_restrict` — measurability from a countable
  measurable cover on which the restrictions are measurable.
* `TauCeti.measurable_cfc_comp` — `ω ↦ cfc f (a ω)` is measurable.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `ForMathlib.MeasureTheory.CfcMeasurable`, moved to
  `ForTauCeti` in the Wave-1 staging migration; introduced at Davis--Kahan
  commit `fab5250`.
* Extraction class: **moved**.  The Wave-1 migration renamed the namespace
  `ForMathlib` to `TauCeti`; declaration names and proofs are unchanged.
* Original authors / copyright: Jon Crall, Claude Opus 4.8; Copyright (c) 2026 Kitware, Inc.;
  Apache 2.0.
* Spectra influence: **none** — this module imports only Mathlib and sibling
  `ForTauCeti` staging modules.
-/

public section

namespace TauCeti

open MeasureTheory Set

/--
**Measurability from a countable restrict-cover.**

If `Ω = ⋃ₖ sₖ` with each `sₖ` measurable and the restriction of `g` to each
`sₖ` measurable, then `g` is measurable.  (The two-set case is
`measurable_of_restrict_of_restrict_compl`; this is the countable version.)
-/
theorem measurable_of_iUnion_restrict {Ω A : Type*}
    [MeasurableSpace Ω] [MeasurableSpace A]
    {g : Ω → A} {s : ℕ → Set Ω}
    (hs : ∀ k, MeasurableSet (s k)) (hcov : (⋃ k, s k) = univ)
    (hg : ∀ k, Measurable ((s k).domRestrict g)) : Measurable g := by
  intro t ht
  have hpre : g ⁻¹' t = ⋃ k, ((↑) : s k → Ω) '' ((s k).domRestrict g ⁻¹' t) := by
    apply Set.eq_of_subset_of_subset
    · intro ω hω
      have hmem : ω ∈ (⋃ k, s k) := by rw [hcov]; trivial
      rw [Set.mem_iUnion] at hmem
      obtain ⟨k, hk⟩ := hmem
      rw [Set.mem_iUnion]
      exact ⟨k, ⟨ω, hk⟩, hω, rfl⟩
    · intro ω hω
      rw [Set.mem_iUnion] at hω
      obtain ⟨k, ⟨x, hx⟩, hxt, rfl⟩ := hω
      exact hxt
  rw [hpre]
  refine MeasurableSet.iUnion fun k => ?_
  exact (MeasurableEmbedding.subtype_coe (hs k)).measurableSet_image.mpr (hg k ht)

variable {Ω A : Type*} [MeasurableSpace Ω]
  [NormedRing A] [StarRing A] [NormedAlgebra ℝ A] [ContinuousStar A] [CompleteSpace A]
  [IsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint] [NormOneClass A]
  [MeasurableSpace A] [BorelSpace A]

/--
**Measurability of the continuous functional calculus in the element.**

For a fixed continuous `f : ℝ → ℝ`, if `B : Ω → A` is measurable and
self-adjoint-valued, then `ω ↦ cfc f (B ω)` is measurable — with no measurable
selection of an eigenbasis.
-/
theorem measurable_cfc_comp
    (f : ℝ → ℝ) (hf : Continuous f)
    (B : Ω → A) (hB : Measurable B) (hsa : ∀ ω, IsSelfAdjoint (B ω)) :
    Measurable (fun ω => cfc f (B ω)) := by
  -- Cover `Ω` by the pieces `{ω | ‖B ω‖ ≤ k}`, `k : ℕ`.
  set s : ℕ → Set Ω := fun k => {ω | ‖B ω‖ ≤ (k : ℝ)} with hsdef
  have hsmeas : ∀ k, MeasurableSet (s k) := fun k => hB.norm measurableSet_Iic
  have hcover : (⋃ k, s k) = univ := by
    ext ω
    simp only [hsdef, Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    obtain ⟨k, hk⟩ := exists_nat_ge ‖B ω‖
    exact ⟨k, hk⟩
  refine measurable_of_iUnion_restrict hsmeas hcover (fun k => ?_)
  -- On `{a | IsSelfAdjoint a ∧ spectrum ⊆ closedBall 0 k}`, `cfc f` is continuous.
  have hcontOn : ContinuousOn (cfc f)
      {a : A | IsSelfAdjoint a ∧ spectrum ℝ a ⊆ Metric.closedBall 0 (k : ℝ)} :=
    continuousOn_cfc A (isCompact_closedBall 0 (k : ℝ)) f hf.continuousOn
  -- `B` maps the `k`-piece into that set (spectrum bounded by the norm).
  have hmaps : ∀ ω : (s k),
      B ω ∈ {a : A | IsSelfAdjoint a ∧ spectrum ℝ a ⊆ Metric.closedBall 0 (k : ℝ)} := by
    rintro ⟨ω, hω⟩
    exact ⟨hsa ω, (spectrum.subset_closedBall_norm (B ω)).trans
      (Metric.closedBall_subset_closedBall hω)⟩
  -- Restrict `cfc f` to a continuous map and compose with the measurable corestriction.
  have hcont' : Continuous
      (fun x : {a : A | IsSelfAdjoint a ∧ spectrum ℝ a ⊆ Metric.closedBall 0 (k : ℝ)} =>
        cfc f (x : A)) := continuousOn_iff_continuous_domRestrict.mp hcontOn
  have hcore : Measurable
      (fun ω : (s k) =>
        (⟨B ω, hmaps ω⟩ :
          {a : A | IsSelfAdjoint a ∧ spectrum ℝ a ⊆ Metric.closedBall 0 (k : ℝ)})) :=
    (hB.comp measurable_subtype_coe).subtype_mk
  exact hcont'.measurable.comp hcore

end TauCeti
