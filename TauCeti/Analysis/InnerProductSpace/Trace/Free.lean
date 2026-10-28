/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Trace
public import TauCeti.LinearAlgebra.Complex.Conjugation

/-!
# Trace-free self-adjoint endomorphisms

For a finite-dimensional inner product space `E` over `𝕜 = ℝ` or `ℂ`, the trace of the adjoint
of an endomorphism is the conjugate of its trace (`LinearMap.trace_adjoint`), so the trace pairing
`tr (T U)` of two self-adjoint endomorphisms is real. Consequently the
**trace-free part** `T - (tr T / n) Id`, `n = dim E`, of an endomorphism `T`
(`TauCeti.traceFreePart`) is again self-adjoint when `T` is. It is the projection of `T` onto the
trace-free endomorphisms along the scalars: it is idempotent, kills `Id` and fixes every
trace-free `T`, and it is orthogonal for the trace pairing `(T, U) ↦ tr (T U)`.

Over `ℂ`, the trace-free self-adjoint endomorphisms form a real subspace
`TauCeti.traceFreeSelfAdjoint E` of dimension `n² - 1`: the self-adjoint endomorphisms are a real
form of all endomorphisms, so they have real dimension `n²`, and the real trace is a nonzero real
functional on them. In complex dimension two this is the three-dimensional real space
`{T : T* = T, tr T = 0}`, the target of Clifford multiplication by imaginary self-dual two-forms on
the positive half-spinors of a four-dimensional `Spinᶜ` structure, on which the Hilbert–Schmidt
pairing `tr (T* U) = tr (T U)` is real.

## Main definitions

* `TauCeti.traceFreePart 𝕜 E`: the linear projection `T ↦ T - (tr T / n) Id` onto the trace-free
  endomorphisms.
* `TauCeti.traceFreeSelfAdjoint E`: the real subspace of trace-free self-adjoint endomorphisms of a
  complex inner product space.

## Main results

* `LinearMap.trace_adjoint`, `ContinuousLinearMap.trace_adjoint`: `tr T* = conj (tr T)`.
* `IsSelfAdjoint.conj_trace`, `IsSelfAdjoint.conj_trace_mul`: the trace of a self-adjoint
  endomorphism, and the trace pairing `tr (T U)` of two of them, are real.
* `InnerProductSpace.trace_rankOne_mul`, `InnerProductSpace.trace_mul_rankOne`: the trace pairing
  of `T` with a rank-one endomorphism, `tr (x y* T) = tr (T x y*) = ⟪y, T x⟫`.
* `TauCeti.trace_traceFreePart`, `TauCeti.traceFreePart_of_trace_eq_zero`,
  `TauCeti.traceFreePart_id`: `traceFreePart` projects onto the trace-free endomorphisms along the
  scalars.
* `TauCeti.trace_traceFreePart_mul`: the projection is orthogonal for the trace pairing.
* `TauCeti.finrank_traceFreeSelfAdjoint`: the trace-free self-adjoint endomorphisms of a complex
  inner product space of dimension `n` have real dimension `n² - 1`.
-/

public section

noncomputable section

open Module (finrank)
open scoped ComplexConjugate InnerProductSpace

namespace LinearMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- The trace of the adjoint of an endomorphism is the conjugate of its trace. -/
@[simp]
theorem trace_adjoint (T : E →ₗ[𝕜] E) : trace 𝕜 E T.adjoint = conj (trace 𝕜 E T) := by
  let b := stdOrthonormalBasis 𝕜 E
  simp [trace_eq_sum_inner _ b, adjoint_inner_right, map_sum]

end LinearMap

namespace ContinuousLinearMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- The trace of the adjoint of an endomorphism is the conjugate of its trace. -/
@[simp]
theorem trace_adjoint [CompleteSpace E] (T : E →L[𝕜] E) :
    LinearMap.trace 𝕜 E (adjoint T) = conj (LinearMap.trace 𝕜 E T) := by
  let b := stdOrthonormalBasis 𝕜 E
  simp [LinearMap.trace_eq_sum_inner _ b, adjoint_inner_right, map_sum]

/-- The trace of a self-adjoint endomorphism is real. -/
theorem _root_.IsSelfAdjoint.conj_trace [CompleteSpace E] {T : E →L[𝕜] E} (hT : IsSelfAdjoint T) :
    conj (LinearMap.trace 𝕜 E T) = LinearMap.trace 𝕜 E T := by
  rw [← trace_adjoint, ← star_eq_adjoint, hT.star_eq]

/-- The trace pairing `tr (T U)` of two self-adjoint endomorphisms is real. -/
theorem _root_.IsSelfAdjoint.conj_trace_mul [CompleteSpace E] {T U : E →L[𝕜] E}
    (hT : IsSelfAdjoint T) (hU : IsSelfAdjoint U) :
    conj (LinearMap.trace 𝕜 E (T * U)) = LinearMap.trace 𝕜 E (T * U) := by
  rw [← toLinearMap_mul, ← trace_adjoint, ← star_eq_adjoint, star_mul, hT.star_eq, hU.star_eq]
  simpa using LinearMap.trace_mul_comm 𝕜 (U : E →ₗ[𝕜] E) T

end ContinuousLinearMap

namespace InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- The trace pairing of `T` with a rank-one endomorphism: `tr (T x y*) = ⟪y, T x⟫`. -/
theorem trace_mul_rankOne (T : E →L[𝕜] E) (x y : E) :
    LinearMap.trace 𝕜 E (T * rankOne 𝕜 x y) = ⟪y, T x⟫_𝕜 := by
  rw [← ContinuousLinearMap.toLinearMap_mul, ContinuousLinearMap.mul_def,
    comp_rankOne, trace_rankOne]

/-- The trace pairing of a rank-one endomorphism with `T`: `tr (x y* T) = ⟪y, T x⟫`. -/
theorem trace_rankOne_mul (x y : E) (T : E →L[𝕜] E) :
    LinearMap.trace 𝕜 E (rankOne 𝕜 x y * T) = ⟪y, T x⟫_𝕜 := by
  rw [LinearMap.trace_mul_comm, trace_mul_rankOne]

end InnerProductSpace

namespace TauCeti

section TraceFreePart

variable (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The trace-free part `T - (tr T / n) Id` of an endomorphism `T` of an `n`-dimensional space,
as a linear projection onto the trace-free endomorphisms. -/
def traceFreePart : (E →L[𝕜] E) →ₗ[𝕜] E →L[𝕜] E :=
  LinearMap.id - ((finrank 𝕜 E : 𝕜)⁻¹ • (LinearMap.trace 𝕜 E ∘ₗ
    (ContinuousLinearMap.coeLM 𝕜 : (E →L[𝕜] E) →ₗ[𝕜] E →ₗ[𝕜] E)).smulRight
      (ContinuousLinearMap.id 𝕜 E))

variable {𝕜 E}

/-- `traceFreePart T = T - (tr T / n) Id`. -/
theorem traceFreePart_apply (T : E →L[𝕜] E) :
    traceFreePart 𝕜 E T =
      T - (LinearMap.trace 𝕜 E T / finrank 𝕜 E) • ContinuousLinearMap.id 𝕜 E := by
  simp [traceFreePart, div_eq_inv_mul, mul_smul]

/-- The trace-free part of an endomorphism is trace free. -/
@[simp]
theorem trace_traceFreePart [FiniteDimensional 𝕜 E] (T : E →L[𝕜] E) :
    LinearMap.trace 𝕜 E (traceFreePart 𝕜 E T) = 0 := by
  rcases eq_or_ne (finrank 𝕜 E) 0 with h | h
  · have : Subsingleton E := Module.finrank_zero_iff.mp h
    simp [Subsingleton.elim (traceFreePart 𝕜 E T) 0]
  · simp [traceFreePart_apply, h]

/-- `traceFreePart` fixes every trace-free endomorphism. -/
theorem traceFreePart_of_trace_eq_zero {T : E →L[𝕜] E} (hT : LinearMap.trace 𝕜 E T = 0) :
    traceFreePart 𝕜 E T = T := by
  simp [traceFreePart_apply, hT]

/-- `traceFreePart` kills the scalars. -/
@[simp]
theorem traceFreePart_id [FiniteDimensional 𝕜 E] :
    traceFreePart 𝕜 E (ContinuousLinearMap.id 𝕜 E) = 0 := by
  rcases eq_or_ne (finrank 𝕜 E) 0 with h | h
  · have : Subsingleton E := Module.finrank_zero_iff.mp h
    exact Subsingleton.elim _ _
  · simp [traceFreePart_apply, h]

/-- `traceFreePart` is idempotent. -/
@[simp]
theorem traceFreePart_traceFreePart [FiniteDimensional 𝕜 E] (T : E →L[𝕜] E) :
    traceFreePart 𝕜 E (traceFreePart 𝕜 E T) = traceFreePart 𝕜 E T :=
  traceFreePart_of_trace_eq_zero (trace_traceFreePart T)

/-- `traceFreePart` is orthogonal for the trace pairing: against a trace-free `U`, the trace-free
part of `T` pairs as `T` does. -/
theorem trace_traceFreePart_mul {U : E →L[𝕜] E} (hU : LinearMap.trace 𝕜 E U = 0)
    (T : E →L[𝕜] E) :
    LinearMap.trace 𝕜 E (traceFreePart 𝕜 E T * U) = LinearMap.trace 𝕜 E (T * U) := by
  simp [traceFreePart_apply, sub_mul, hU, Module.End.mul_eq_comp]

/-- The trace-free part of a self-adjoint endomorphism is self-adjoint. -/
theorem _root_.IsSelfAdjoint.traceFreePart [FiniteDimensional 𝕜 E] [CompleteSpace E]
    {T : E →L[𝕜] E} (hT : IsSelfAdjoint T) : IsSelfAdjoint (traceFreePart 𝕜 E T) := by
  have htr : IsSelfAdjoint (LinearMap.trace 𝕜 E T) := hT.conj_trace
  rw [traceFreePart_apply]
  exact hT.sub ((htr.div (.natCast _)).smul (by
    rw [IsSelfAdjoint, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_id]))

end TraceFreePart

section TraceFreeSelfAdjoint

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The real subspace `{T : T* = T, tr T = 0}` of trace-free self-adjoint endomorphisms of a complex
inner product space. -/
def traceFreeSelfAdjoint : Submodule ℝ (E →L[ℂ] E) where
  carrier := {T | IsSelfAdjoint T ∧ LinearMap.trace ℂ E T = 0}
  add_mem' hS hT := ⟨hS.1.add hT.1, by simp [hS.2, hT.2]⟩
  zero_mem' := ⟨.zero _, by simp⟩
  smul_mem' r T hT := ⟨(IsSelfAdjoint.all r).smul hT.1, by simp [hT.2]⟩

variable {E}

/-- An endomorphism lies in `traceFreeSelfAdjoint E` exactly when it is self-adjoint and trace
free. -/
@[simp]
theorem mem_traceFreeSelfAdjoint {T : E →L[ℂ] E} :
    T ∈ traceFreeSelfAdjoint E ↔ IsSelfAdjoint T ∧ LinearMap.trace ℂ E T = 0 :=
  (Iff.rfl)

/-- The trace-free part of a self-adjoint endomorphism is a trace-free self-adjoint
endomorphism. -/
theorem _root_.IsSelfAdjoint.traceFreePart_mem [FiniteDimensional ℂ E] {T : E →L[ℂ] E}
    (hT : IsSelfAdjoint T) : traceFreePart ℂ E T ∈ traceFreeSelfAdjoint E :=
  mem_traceFreeSelfAdjoint.2 ⟨hT.traceFreePart, trace_traceFreePart T⟩

/-- The trace-free self-adjoint endomorphisms of an `n`-dimensional complex inner product space
form a real vector space of dimension `n² - 1`. -/
theorem finrank_traceFreeSelfAdjoint [FiniteDimensional ℂ E] :
    finrank ℝ (traceFreeSelfAdjoint E) = finrank ℂ E ^ 2 - 1 := by
  -- The trace-free self-adjoint endomorphisms are the kernel of the real part of the trace on the
  -- self-adjoint ones, which have real dimension `n²`.
  set S := selfAdjoint.submodule ℝ (E →L[ℂ] E)
  let φ : S →ₗ[ℝ] ℝ := Complex.reLm ∘ₗ (LinearMap.trace ℂ E).restrictScalars ℝ ∘ₗ
    (ContinuousLinearMap.coeLM ℂ).restrictScalars ℝ ∘ₗ S.subtype
  have hφ (T : S) : φ T = (LinearMap.trace ℂ E (T : E →L[ℂ] E)).re := rfl
  have hker : LinearMap.ker φ = (traceFreeSelfAdjoint E).comap S.subtype := by
    ext ⟨T, hT : IsSelfAdjoint T⟩
    have him : (LinearMap.trace ℂ E T).im = 0 := Complex.conj_eq_iff_im.1 hT.conj_trace
    simp [hφ, hT, Complex.ext_iff, him]
  have hS : finrank ℝ S = finrank ℂ E ^ 2 := by
    rw [finrank_selfAdjoint_submodule, ← (LinearMap.toContinuousLinearMap (𝕜 := ℂ) (E := E)
      (F' := E)).finrank_eq, Module.finrank_linearMap, sq]
  have : FiniteDimensional ℝ (E →L[ℂ] E) := Module.Finite.trans ℂ _
  have hle : traceFreeSelfAdjoint E ≤ S := fun T hT ↦ hT.1
  have hrk := LinearMap.finrank_range_add_finrank_ker φ
  rw [← (Submodule.comapSubtypeEquivOfLe hle).finrank_eq, ← hker]
  rcases eq_or_ne (finrank ℂ E) 0 with h | h
  · rw [hS] at hrk
    rw [h, zero_pow two_ne_zero] at hrk ⊢
    omega
  · have hrange : LinearMap.range φ = ⊤ := by
      refine LinearMap.range_eq_top.2 fun r ↦ ⟨(r / finrank ℂ E : ℝ) • ⟨_, .one _⟩, ?_⟩
      simp [hφ, h]
    rw [hrange, finrank_top, Module.finrank_self, hS] at hrk
    omega

end TraceFreeSelfAdjoint

end TauCeti
