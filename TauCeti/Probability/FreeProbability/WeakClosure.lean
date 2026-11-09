/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.FreeProbability.Topology
public import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology

/-!
# Free independence and weak operator closure

Free subalgebras of bounded operators remain free after weak operator closure for a normalized
vector functional. We use Mathlib's `ContinuousLinearMapWOT` to take these closures, transporting
both the subalgebras and the functional through its canonical algebra equivalence. No trace or
faithfulness is needed. In particular the result applies to a trace represented by its GNS
vector; it does not assert that every normal state is weak-operator continuous in an arbitrary
representation.

Multiplication in the weak operator topology is separately, not jointly, continuous. The
one-letter approximation theorem for free independence therefore applies, although continuity
of the whole word-product map cannot be used.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Lecture 5.
-/

public section

open scoped InnerProductSpace

namespace TauCeti

section NormedSpace

variable {𝕜 H ι : Type*} [NormedField 𝕜] [NormedAddCommGroup H] [NormedSpace 𝕜 H]

/-- Freeness of operator subalgebras can be tested after weak operator closure, provided the
functional is continuous for that topology. The functional and subalgebras on the norm-topology
carrier are transported using Mathlib's canonical algebra equivalence. -/
theorem isFreelyIndependent_weakOperatorClosure_iff
    {φ : (H →L[𝕜] H) →ₗ[𝕜] 𝕜} {B : ι → Subalgebra 𝕜 (H →L[𝕜] H)}
    (hφ : φ 1 = 1)
    (hcont : Continuous (fun T : H →WOT[𝕜] H => φ T.toCLM)) :
    IsFreelyIndependent (φ.comp (ContinuousLinearMapWOT.algEquiv 𝕜).toLinearMap)
        (fun i => ((B i).map (ContinuousLinearMapWOT.algEquiv 𝕜).symm.toAlgHom).topologicalClosure)
      ↔ IsFreelyIndependent φ B := by
  let e := ContinuousLinearMapWOT.algEquiv (𝕜₁ := 𝕜) (E := H) 𝕜
  let ψ := φ.comp e.toLinearMap
  have hψ : ψ 1 = 1 := by simp [ψ, hφ]
  rw [isFreelyIndependent_topologicalClosure_iff hψ hcont]
  constructor
  · intro h
    have hpull := h.comap e.symm.toAlgHom
    have hcomp : ψ.comp e.symm.toAlgHom.toLinearMap = φ := by
      ext T
      simp [ψ]
    rw [hcomp] at hpull
    exact hpull.mono fun i => Subalgebra.map_le.mp le_rfl
  · intro h
    exact h.map e.symm.toAlgHom (by ext T; simp [ψ])

end NormedSpace

variable {𝕜 H ι : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- A normalized vector functional preserves and reflects freeness when the subalgebras are
replaced by their weak operator closures. This includes vector realizations of tracial states,
without requiring traciality of the vector state on all bounded operators. -/
theorem isFreelyIndependent_weakOperatorClosure_iff_of_vectorState
    {φ : (H →L[𝕜] H) →ₗ[𝕜] 𝕜} {B : ι → Subalgebra 𝕜 (H →L[𝕜] H)}
    (hφ : φ 1 = 1) (ξ : H) (hξ : ∀ T, φ T = ⟪ξ, T ξ⟫_𝕜) :
    IsFreelyIndependent (φ.comp (ContinuousLinearMapWOT.algEquiv 𝕜).toLinearMap)
        (fun i => ((B i).map (ContinuousLinearMapWOT.algEquiv 𝕜).symm.toAlgHom).topologicalClosure)
      ↔ IsFreelyIndependent φ B := by
  apply isFreelyIndependent_weakOperatorClosure_iff hφ
  simp only [hξ]
  exact ContinuousLinearMapWOT.continuous_dual_apply ξ (innerSL 𝕜 ξ)

end TauCeti
