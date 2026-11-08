/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
public import TauCeti.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.Separation.Regular
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.MeasureTheory.Function.Gluing

/-!
# Locality of weak derivatives

A weak derivative on an open domain can be detected on all open subdomains whose closures
are compact and contained in the domain. No boundary regularity or boundedness of the domain
is needed. Thus completeness, local integrability, and the test-function identities defining
the weak derivative can be verified on relatively compact subdomains.

In finite-dimensional domains, a fixed candidate is a weak derivative if it is one near every
point. In particular weak derivatives can be checked on any open cover, including overlapping
covers of unbounded domains. The open-cover equivalences assume a complete codomain, since an
empty cover cannot supply the completeness required by the weak-derivative predicate.

When the measurable space is the Borel one, local weak Fréchet derivative fields need not be
given by a fixed global candidate: uniqueness makes them agree almost everywhere on overlaps,
and they assemble into a global weak derivative. A countable subcover suffices even when the
original cover is uncountable.

## Main results

* `hasWeakLineDerivOn_iff_forall_isCompact_closure`: detection of weak directional derivatives.
* `hasWeakFDerivOn_iff_forall_isCompact_closure`: detection of weak Fréchet derivatives.
* `hasWeakLineDerivOn_iff_locally` and `hasWeakFDerivOn_iff_locally`: neighborhood locality.
* `hasWeakLineDerivOn_iSup_iff` and `hasWeakFDerivOn_iSup_iff`: open-cover locality.
* `exists_hasWeakFDerivOn_iSup`: gluing local derivative fields up to almost-everywhere equality.
* `exists_hasWeakFDerivOn_iff_locally`: local existence is equivalent to global existence.

## Attribution

The reduction to relatively compact subdomains follows Mathlib's
`exists_open_between_and_isCompact_closure`, which places each test function's compact support
inside a single testing subdomain.
Open-cover locality uses `AddMonoidHom.eq_zero_of_locally_vanishing`, the finite
partition-of-unity localization API for test functions.
Derivative-field gluing uses `exists_forall_ae_eq_restrict_of_ae_eq_restrict_inter` after
Mathlib's `isOpen_iUnion_countable` reduces the cover to a sequence.
-/

public section

open MeasureTheory Set TopologicalSpace
open scoped Distributions

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [MeasurableSpace E] {μ : Measure E} {Ω : Opens E} {u u' : E → F} {v : E}

section RelativelyCompact

variable [LocallyCompactSpace E]

/-- Weak directional derivatives are detected on relatively compact open subdomains.
The closure of each testing subdomain must lie inside `Ω`. Completeness and local
integrability need not be assumed separately: they follow from the subdomain hypotheses,
including the empty subdomain when `Ω` is empty. -/
theorem hasWeakLineDerivOn_iff_forall_isCompact_closure :
    HasWeakLineDerivOn μ Ω u u' v ↔
      ∀ V : Opens E, IsCompact (closure (V : Set E)) → closure (V : Set E) ⊆ Ω →
        HasWeakLineDerivOn μ V u u' v := by
  constructor
  · intro h V _ hV
    exact h.mono (subset_closure.trans hV)
  · intro h
    have hc : CompleteSpace F :=
      (h ⊥ (by simp) (by simp)).completeSpace
    refine hasWeakLineDerivOn_iff_testFunction.2 ⟨hc,
      locallyIntegrableOn_iff_forall_isCompact_closure.2
        (fun V hVc hVΩ => (h V hVc hVΩ).locallyIntegrableOn),
      locallyIntegrableOn_iff_forall_isCompact_closure.2
        (fun V hVc hVΩ => (h V hVc hVΩ).locallyIntegrableOn_deriv), ?_⟩
    intro φ
    obtain ⟨V, hVo, hφV, hVΩ, hVc⟩ :=
      exists_open_between_and_isCompact_closure φ.hasCompactSupport Ω.isOpen φ.tsupport_subset
    exact (h ⟨V, hVo⟩ hVc hVΩ).integral_lineDeriv_smul_eq_neg_integral_smul
      ⟨φ, φ.contDiff, φ.hasCompactSupport, hφV⟩

/-- Weak Fréchet derivatives are detected on relatively compact open subdomains.
The equivalence holds for arbitrary real normed codomain and measure, without assumptions on the
boundary of the domain. -/
theorem hasWeakFDerivOn_iff_forall_isCompact_closure {U : E → E →L[ℝ] F} :
    HasWeakFDerivOn μ Ω u U ↔
      ∀ V : Opens E, IsCompact (closure (V : Set E)) → closure (V : Set E) ⊆ Ω →
        HasWeakFDerivOn μ V u U := by
  constructor
  · intro h V _ hV
    exact h.mono (subset_closure.trans hV)
  · intro h
    refine hasWeakFDerivOn_iff.2 fun v =>
      hasWeakLineDerivOn_iff_forall_isCompact_closure.2 ?_
    intro V hVc hVΩ
    exact (h V hVc hVΩ).hasWeakLineDerivOn v

end RelativelyCompact

section OpenCover

variable [FiniteDimensional ℝ E] [OpensMeasurableSpace E] [CompleteSpace F]

/-- A fixed candidate weak directional derivative can be checked on open neighborhoods of
each point. Neither the measure nor the neighborhoods need be finite. -/
theorem hasWeakLineDerivOn_iff_locally :
    HasWeakLineDerivOn μ Ω u u' v ↔
      ∀ x ∈ Ω, ∃ V : Opens E, x ∈ V ∧ HasWeakLineDerivOn μ V u u' v := by
  constructor
  · exact fun h x hx ↦ ⟨Ω, hx, h⟩
  · intro h
    have hu : LocallyIntegrableOn u Ω μ := by
      intro x hx
      obtain ⟨V, hxV, hV⟩ := h x hx
      have hi := hV.locallyIntegrableOn x hxV
      rw [V.isOpen.nhdsWithin_eq hxV] at hi
      exact hi.filter_mono nhdsWithin_le_nhds
    have hu' : LocallyIntegrableOn u' Ω μ := by
      intro x hx
      obtain ⟨V, hxV, hV⟩ := h x hx
      have hi := hV.locallyIntegrableOn_deriv x hxV
      rw [V.isOpen.nhdsWithin_eq hxV] at hi
      exact hi.filter_mono nhdsWithin_le_nhds
    let T : 𝓓(Ω, ℝ) →+ F := AddMonoidHom.ofClass (
      (TestFunction.integralAgainstBilinCLM (ContinuousLinearMap.lsmul ℝ ℝ) μ u).comp
        (TestFunction.lineDerivCLM ℝ v : 𝓓(Ω, ℝ) →L[ℝ] 𝓓(Ω, ℝ)) +
      TestFunction.integralAgainstBilinCLM (ContinuousLinearMap.lsmul ℝ ℝ) μ u')
    have hT (φ : 𝓓(Ω, ℝ)) : T φ =
        (∫ x, lineDeriv ℝ (φ : E → ℝ) x v • u x ∂μ) +
          ∫ x, (φ : E → ℝ) x • u' x ∂μ := by
      simp only [T, AddMonoidHom.coe_ofClass, add_apply, ContinuousLinearMap.comp_apply,
        TestFunction.integralAgainstBilinCLM_eq_integral hu,
        TestFunction.integralAgainstBilinCLM_eq_integral hu',
        ContinuousLinearMap.lsmul_apply, TestFunction.lineDerivCLM_apply_of_le le_top]
    have hzero := AddMonoidHom.eq_zero_of_locally_vanishing
      T fun x hx ↦ ?_
    · refine hasWeakLineDerivOn_iff_testFunction.2 ⟨inferInstance, hu, hu', fun φ ↦ ?_⟩
      apply eq_neg_iff_add_eq_zero.2
      simpa only [← hT, AddMonoidHom.zero_apply] using DFunLike.congr_fun hzero φ
    · obtain ⟨V, hxV, hV⟩ := h x hx
      refine ⟨V, V.isOpen, hxV, fun φ hφ ↦ ?_⟩
      let ψ : 𝓓(V, ℝ) := ⟨φ, φ.contDiff, φ.hasCompactSupport, hφ⟩
      rw [hT]
      exact eq_neg_iff_add_eq_zero.1
        (hV.integral_lineDeriv_smul_eq_neg_integral_smul ψ)

/-- A fixed candidate weak Fréchet derivative can be checked near each point of its domain.
This applies to arbitrary measures and complete real normed codomains. -/
theorem hasWeakFDerivOn_iff_locally {U : E → E →L[ℝ] F} :
    HasWeakFDerivOn μ Ω u U ↔
      ∀ x ∈ Ω, ∃ V : Opens E, x ∈ V ∧ HasWeakFDerivOn μ V u U := by
  constructor
  · exact fun h x hx ↦ ⟨Ω, hx, h⟩
  · intro h
    refine hasWeakFDerivOn_iff.2 fun v ↦ hasWeakLineDerivOn_iff_locally.2 ?_
    intro x hx
    obtain ⟨V, hxV, hV⟩ := h x hx
    exact ⟨V, hxV, hV.hasWeakLineDerivOn v⟩

/-- Weak directional derivatives are local on arbitrary unions of open sets. The completeness
assumption also covers the empty indexed family. -/
theorem hasWeakLineDerivOn_iSup_iff {ι : Sort*} (V : ι → Opens E) :
    HasWeakLineDerivOn μ (⨆ i, V i) u u' v ↔
      ∀ i, HasWeakLineDerivOn μ (V i) u u' v := by
  constructor
  · exact fun h i ↦ h.mono (le_iSup V i)
  · intro h
    refine hasWeakLineDerivOn_iff_locally.2 fun x hx ↦ ?_
    obtain ⟨i, hxi⟩ : ∃ i, x ∈ V i := by
      simpa only [← SetLike.mem_coe, Opens.coe_iSup, mem_iUnion] using hx
    exact ⟨V i, hxi, h i⟩

/-- Weak Fréchet derivatives are local on arbitrary unions of open sets, including the empty
union when the codomain is complete. -/
theorem hasWeakFDerivOn_iSup_iff {ι : Sort*} (V : ι → Opens E) {U : E → E →L[ℝ] F} :
    HasWeakFDerivOn μ (⨆ i, V i) u U ↔ ∀ i, HasWeakFDerivOn μ (V i) u U := by
  simp only [hasWeakFDerivOn_iff, hasWeakLineDerivOn_iSup_iff]
  exact forall_comm

end OpenCover

section Gluing

variable [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F]

/-- Local weak Fréchet derivatives of the same function glue along any open cover. The glued
field agrees almost everywhere with each local field; overlap compatibility follows from
uniqueness of weak derivatives. The cover may be uncountable or empty. -/
theorem exists_hasWeakFDerivOn_iSup {ι : Type*} (V : ι → Opens E)
    (W : ι → E → E →L[ℝ] F) (h : ∀ i, HasWeakFDerivOn μ (V i) u (W i)) :
    ∃ U : E → E →L[ℝ] F, HasWeakFDerivOn μ (⨆ i, V i) u U ∧
      ∀ i, U =ᵐ[μ.restrict (V i)] W i := by
  classical
  obtain ⟨T, hTc, hT⟩ := isOpen_iUnion_countable (fun i ↦ (V i : Set E))
    (fun i ↦ (V i).isOpen)
  have hex : ∃ U : E → E →L[ℝ] F, HasWeakFDerivOn μ (⨆ i, V i) u U := by
    by_cases hne : T.Nonempty
    · obtain ⟨f, hf⟩ := hTc.exists_eq_range hne
      have hcover : (⨆ n, V (f n)) = ⨆ i, V i := by
        apply SetLike.coe_injective
        simpa only [Opens.coe_iSup, hf, biUnion_range] using hT
      obtain ⟨U, hU⟩ := exists_forall_ae_eq_restrict_of_ae_eq_restrict_inter
        (fun n ↦ (V (f n)).isOpen.measurableSet) (a := fun n ↦ W (f n))
        (fun k m ↦ ((h (f k)).mono (Ω' := V (f k) ⊓ V (f m)) inf_le_left).ae_eq
          ((h (f m)).mono inf_le_right))
      refine ⟨U, hcover ▸ (hasWeakFDerivOn_iSup_iff (fun n ↦ V (f n))).2 (fun n ↦ ?_)⟩
      exact (h (f n)).congr_ae_deriv (hU n).symm
    · have hempty : (⨆ i, V i : Opens E) = ⊥ := by
        apply SetLike.coe_injective
        simpa [Opens.coe_iSup, not_nonempty_iff_eq_empty.mp hne] using hT.symm
      refine ⟨0, hasWeakFDerivOn_iff_locally.2 ?_⟩
      simp [hempty]
  obtain ⟨U, hU⟩ := hex
  exact ⟨U, hU, fun i ↦ (hU.mono (le_iSup V i)).ae_eq (h i)⟩

/-- Existence of a weak Fréchet derivative is local. Local fields are not required to agree
pointwise, and no candidate global derivative needs to be chosen in advance. -/
theorem exists_hasWeakFDerivOn_iff_locally :
    (∃ U : E → E →L[ℝ] F, HasWeakFDerivOn μ Ω u U) ↔
      ∀ x ∈ Ω, ∃ V : Opens E, x ∈ V ∧
        ∃ U : E → E →L[ℝ] F, HasWeakFDerivOn μ V u U := by
  constructor
  · rintro ⟨U, hU⟩ x hx
    exact ⟨Ω, hx, U, hU⟩
  · intro h
    choose V hxV W hW using fun x : Ω ↦ h x x.2
    obtain ⟨U, hU, -⟩ := exists_hasWeakFDerivOn_iSup V W hW
    refine ⟨U, hU.mono fun x hx ↦ ?_⟩
    exact (le_iSup V ⟨x, hx⟩) (hxV ⟨x, hx⟩)

end Gluing

/-- Weak directional derivatives on two open sets glue on their union. -/
theorem HasWeakLineDerivOn.sup [FiniteDimensional ℝ E] [OpensMeasurableSpace E]
    {V : Opens E} (hΩ : HasWeakLineDerivOn μ Ω u u' v)
    (hV : HasWeakLineDerivOn μ V u u' v) : HasWeakLineDerivOn μ (Ω ⊔ V) u u' v := by
  have := hΩ.completeSpace
  refine hasWeakLineDerivOn_iff_locally.2 fun x hx ↦ ?_
  rcases hx with hx | hx
  · exact ⟨Ω, hx, hΩ⟩
  · exact ⟨V, hx, hV⟩

/-- Weak Fréchet derivatives on two open sets glue on their union. -/
theorem HasWeakFDerivOn.sup [FiniteDimensional ℝ E] [OpensMeasurableSpace E]
    {V : Opens E} {U : E → E →L[ℝ] F} (hΩ : HasWeakFDerivOn μ Ω u U)
    (hV : HasWeakFDerivOn μ V u U) : HasWeakFDerivOn μ (Ω ⊔ V) u U := by
  exact hasWeakFDerivOn_iff.2 fun v ↦ (hΩ.hasWeakLineDerivOn v).sup (hV.hasWeakLineDerivOn v)

end TauCeti
