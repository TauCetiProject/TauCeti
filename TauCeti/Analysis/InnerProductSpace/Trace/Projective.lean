/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Trace.Free
public import Mathlib.Algebra.Lie.OfAssociative

/-!
# Trace-free parts and projective endomorphisms

The trace-free projection identifies endomorphisms modulo scalar multiples of the identity.
It commutes with changes of frame and adjoints, preserves skew-adjointness, and preserves
commutators. In particular, adding a scalar one-form to a unitary connection does not change
the trace-free part of its local connection form or its commutator term. These are pointwise
algebraic statements; no bundle, curvature, or holonomy comparison is asserted here.

The splitting into scalar and trace-free parts is the algebra underlying fixed-determinant
unitary connections and their projective parts. See Wehrheim–Woodward, *Floer field theory
for coprime rank and degree*, §3.2.
-/

public section

noncomputable section

open Module (finrank)

namespace TauCeti

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

section FiniteDimensional

variable [FiniteDimensional 𝕜 E]

/-- The kernel of the trace-free projection consists exactly of scalar endomorphisms. -/
theorem traceFreePart_eq_zero_iff (T : E →L[𝕜] E) :
    traceFreePart 𝕜 E T = 0 ↔ ∃ c : 𝕜, T = c • ContinuousLinearMap.id 𝕜 E := by
  constructor
  · intro h
    exact ⟨LinearMap.trace 𝕜 E T / finrank 𝕜 E,
      sub_eq_zero.mp ((traceFreePart_apply T).symm.trans h)⟩
  · rintro ⟨c, rfl⟩
    simp

/-- Two endomorphisms have the same trace-free part exactly when their difference is scalar. -/
theorem traceFreePart_eq_iff (S T : E →L[𝕜] E) :
    traceFreePart 𝕜 E S = traceFreePart 𝕜 E T ↔
      ∃ c : 𝕜, S - T = c • ContinuousLinearMap.id 𝕜 E := by
  rw [← traceFreePart_eq_zero_iff, map_sub, sub_eq_zero]

/-- A specified trace together with vanishing trace-free part characterizes a central
endomorphism. This also includes the zero-dimensional space. -/
@[simp]
theorem traceFreePart_eq_zero_and_trace_eq_iff (T : E →L[𝕜] E) (c : 𝕜) :
    (traceFreePart 𝕜 E T = 0 ∧ LinearMap.trace 𝕜 E T = (finrank 𝕜 E : 𝕜) * c) ↔
      T = c • ContinuousLinearMap.id 𝕜 E := by
  constructor
  · rintro ⟨h, htr⟩
    by_cases hn : finrank 𝕜 E = 0
    · have : Subsingleton E := Module.finrank_zero_iff.mp hn
      exact Subsingleton.elim _ _
    · rw [traceFreePart_apply, htr, mul_div_cancel_left₀ c (Nat.cast_ne_zero.mpr hn)] at h
      exact sub_eq_zero.mp h
  · rintro rfl
    simp [mul_comm]

end FiniteDimensional

section Adjoint

variable [FiniteDimensional 𝕜 E] [CompleteSpace E]

/-- Taking the trace-free part commutes with taking the adjoint. -/
@[simp]
theorem traceFreePart_star (T : E →L[𝕜] E) :
    traceFreePart 𝕜 E (star T) = star (traceFreePart 𝕜 E T) := by
  simp [traceFreePart_apply, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_id]

/-- Taking the trace-free part preserves skew-adjoint endomorphisms. -/
theorem traceFreePart_mem_skewAdjoint {T : E →L[𝕜] E}
    (hT : T ∈ skewAdjoint (E →L[𝕜] E)) :
    traceFreePart 𝕜 E T ∈ skewAdjoint (E →L[𝕜] E) := by
  rw [skewAdjoint.mem_iff] at hT ⊢
  rw [← traceFreePart_star, hT, map_neg]

end Adjoint

/-- A commutator is already trace free. -/
@[simp]
theorem traceFreePart_lie (S T : E →L[𝕜] E) :
    traceFreePart 𝕜 E ⁅S, T⁆ = ⁅S, T⁆ := by
  apply traceFreePart_of_trace_eq_zero
  simpa only [Ring.lie_def, ContinuousLinearMap.toLinearMap_sub,
    ContinuousLinearMap.toLinearMap_mul] using
    LinearMap.trace_lie (S : E →ₗ[𝕜] E) (T : E →ₗ[𝕜] E)

/-- Removing scalar parts from both inputs leaves the commutator unchanged. -/
@[simp]
theorem lie_traceFreePart (S T : E →L[𝕜] E) :
    ⁅traceFreePart 𝕜 E S, traceFreePart 𝕜 E T⁆ = ⁅S, T⁆ := by
  simp only [traceFreePart_apply, ← ContinuousLinearMap.one_def, Ring.lie_def,
    sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
    smul_sub, smul_smul]
  rw [mul_comm (LinearMap.trace 𝕜 E T / finrank 𝕜 E)]
  abel

end TauCeti

namespace ContinuousLinearEquiv

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]

/-- Taking the trace-free part commutes with change of frame, even between different spaces. -/
@[simp]
theorem traceFreePart_conjContinuousAlgEquiv (e : E ≃L[𝕜] F) (T : E →L[𝕜] E) :
    TauCeti.traceFreePart 𝕜 F (e.conjContinuousAlgEquiv T) =
      e.conjContinuousAlgEquiv (TauCeti.traceFreePart 𝕜 E T) := by
  have htr : LinearMap.trace 𝕜 F (e.conjContinuousAlgEquiv T) = LinearMap.trace 𝕜 E T := by
    simpa only [conjContinuousAlgEquiv_apply, TauCeti.traceCLM_apply] using
      e.traceCLM_comp_comp_symm T
  have hn := e.toLinearEquiv.finrank_eq
  ext x
  simp [TauCeti.traceFreePart_apply, htr, ← hn]

end ContinuousLinearEquiv
