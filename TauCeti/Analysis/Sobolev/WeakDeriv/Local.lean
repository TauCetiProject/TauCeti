/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
import Mathlib.Topology.Separation.Regular

/-!
# Detecting weak derivatives on relatively compact subdomains

A weak derivative on an open domain can be detected on all open subdomains whose closures
are compact and contained in the domain. No boundary regularity or boundedness of the domain
is needed. Thus completeness, local integrability, and the test-function identities defining
the weak derivative can be verified on relatively compact subdomains.

## Main results

* `hasWeakLineDerivOn_iff_forall_isCompact_closure`: detection of weak directional derivatives.
* `hasWeakFDerivOn_iff_forall_isCompact_closure`: detection of weak Fréchet derivatives.
-/

public section

open MeasureTheory Set TopologicalSpace
open scoped Distributions

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [LocallyCompactSpace E]
  [MeasurableSpace E] {μ : Measure E} {Ω : Opens E} {u u' : E → F} {v : E}

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
    have hli (w : E → F)
        (hw : ∀ V : Opens E, IsCompact (closure (V : Set E)) →
          closure (V : Set E) ⊆ Ω → LocallyIntegrableOn w V μ) :
        LocallyIntegrableOn w Ω μ := by
      refine (locallyIntegrableOn_iff Ω.isOpen.isLocallyClosed).2 ?_
      intro K hKΩ hK
      obtain ⟨V, hVo, hKV, hVΩ, hVc⟩ :=
        exists_open_between_and_isCompact_closure hK Ω.isOpen hKΩ
      exact (hw ⟨V, hVo⟩ hVc hVΩ).integrableOn_compact_subset hKV hK
    refine hasWeakLineDerivOn_iff_testFunction.2 ⟨hc,
      hli u (fun V hVc hVΩ => (h V hVc hVΩ).locallyIntegrableOn),
      hli u' (fun V hVc hVΩ => (h V hVc hVΩ).locallyIntegrableOn_deriv), ?_⟩
    intro φ
    obtain ⟨V, hVo, hφV, hVΩ, hVc⟩ :=
      exists_open_between_and_isCompact_closure φ.hasCompactSupport Ω.isOpen φ.tsupport_subset
    exact (h ⟨V, hVo⟩ hVc hVΩ).integral_lineDeriv_smul_eq_neg_integral_smul
      ⟨φ, φ.contDiff, φ.hasCompactSupport, hφV⟩

/-- Weak Fréchet derivatives are detected on relatively compact open subdomains.
The equivalence holds for arbitrary codomain and measure, without assumptions on the boundary
of the domain. -/
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

end TauCeti
