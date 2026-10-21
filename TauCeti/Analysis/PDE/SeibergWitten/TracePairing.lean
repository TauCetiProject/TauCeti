/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Trace.Free
public import TauCeti.Analysis.PDE.SeibergWitten.QuadraticEnd

/-!
# The Seiberg–Witten quadratic map in the trace-free self-adjoint endomorphisms

On a complex inner product space `E` of dimension two (a fibre of the positive half-spinor
bundle), the quadratic endomorphism `Q₀(ψ) = ψψ* - (‖ψ‖² / 2) Id` and its polarization
`B(ψ, φ) = φψ* + ψφ* - Re⟪ψ, φ⟫ Id` take values in the three-dimensional real space
`TauCeti.traceFreeSelfAdjoint E` of trace-free self-adjoint endomorphisms; `Q₀(ψ)` is the
trace-free part of `ψψ*`. Clifford multiplication identifies this space with the imaginary
self-dual two-forms, so these are the values of the quadratic term of the curvature equation
`F_A⁺ = q(ψ) + η` and of its derivative.

On that space the Hilbert–Schmidt pairing is `tr (T* U) = tr (T U)`. This file computes the
pairings of `Q₀(ψ)` and `B(ψ, φ)` with a trace-free endomorphism `T`:
`tr (Q₀(ψ) T) = ⟪ψ, T ψ⟫` and, for self-adjoint `T`, `tr (B(ψ, φ) T) = 2 Re⟪T ψ, φ⟫`. The first
turns the curvature term `⟪C(F_A⁺) ψ, ψ⟫` of the Weitzenböck formula into a Hilbert–Schmidt
pairing with `Q₀(ψ)`; the second says that the formal adjoint of the derivative `B(ψ, ·)` of
`Q₀` is `T ↦ 2 T ψ`. In particular `tr (Q₀(ψ)²) = ‖ψ‖⁴ / 2`.

## Main results

* `quadraticEnd_eq_traceFreePart`: `Q₀(ψ)` is the trace-free part of `ψψ*` in dimension two.
* `quadraticEnd_mem_traceFreeSelfAdjoint`, `quadraticEndPolar_mem_traceFreeSelfAdjoint`: `Q₀(ψ)`
  and `B(ψ, φ)` are trace-free self-adjoint in dimension two.
* `trace_quadraticEnd_mul`: `tr (Q₀(ψ) T) = ⟪ψ, T ψ⟫ - (‖ψ‖² / 2) tr T`; for trace-free `T` this
  is `trace_quadraticEnd_mul_of_trace_eq_zero`, `tr (Q₀(ψ) T) = ⟪ψ, T ψ⟫`.
* `trace_quadraticEnd_mul_self`: `tr (Q₀(ψ)²) = ‖ψ‖⁴ / 2` in dimension two.
* `trace_quadraticEndPolar_mul`: `tr (B(ψ, φ) T) = ⟪ψ, T φ⟫ + ⟪φ, T ψ⟫ - Re⟪ψ, φ⟫ tr T`.
* `trace_quadraticEndPolar_mul_of_mem_traceFreeSelfAdjoint`: `tr (B(ψ, φ) T) = 2 Re⟪T ψ, φ⟫`
  for trace-free self-adjoint `T`.

## References

* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996.
-/

public section

noncomputable section

namespace TauCeti.SeibergWitten

open InnerProductSpace
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- In complex dimension two, `Q₀(ψ)` is the trace-free part of `ψψ*`. -/
theorem quadraticEnd_eq_traceFreePart (h₂ : Module.finrank ℂ E = 2) (ψ : E) :
    quadraticEnd ψ = traceFreePart ℂ E (rankOne ℂ ψ ψ) := by
  simp [quadraticEnd_def, traceFreePart_apply, trace_rankOne, h₂, inner_self_eq_norm_sq_to_K]

/-- The trace pairing of `Q₀(ψ)` with an endomorphism `T`:
`tr (Q₀(ψ) T) = ⟪ψ, T ψ⟫ - (‖ψ‖² / 2) tr T`. -/
theorem trace_quadraticEnd_mul (ψ : E) (T : E →L[ℂ] E) :
    LinearMap.trace ℂ E (quadraticEnd ψ * T) =
      ⟪ψ, T ψ⟫_ℂ - (‖ψ‖ : ℂ) ^ 2 / 2 * LinearMap.trace ℂ E T := by
  rw [← trace_rankOne_mul]
  simp [quadraticEnd_def, sub_mul, Module.End.mul_eq_comp]

/-- Against a trace-free endomorphism `T`, `Q₀(ψ)` pairs as `tr (Q₀(ψ) T) = ⟪ψ, T ψ⟫`. -/
theorem trace_quadraticEnd_mul_of_trace_eq_zero {T : E →L[ℂ] E}
    (hT : LinearMap.trace ℂ E T = 0) (ψ : E) :
    LinearMap.trace ℂ E (quadraticEnd ψ * T) = ⟪ψ, T ψ⟫_ℂ := by
  rw [trace_quadraticEnd_mul, hT, mul_zero, sub_zero]

/-- In complex dimension two, the Hilbert–Schmidt square of `Q₀(ψ)` is
`tr (Q₀(ψ)²) = ‖ψ‖⁴ / 2`. -/
theorem trace_quadraticEnd_mul_self (h₂ : Module.finrank ℂ E = 2) (ψ : E) :
    LinearMap.trace ℂ E (quadraticEnd ψ * quadraticEnd ψ) = (‖ψ‖ : ℂ) ^ 4 / 2 := by
  rw [trace_quadraticEnd_mul_of_trace_eq_zero (trace_quadraticEnd h₂ ψ), quadraticEnd_apply_self,
    inner_smul_right, inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal]
  ring

/-- The trace pairing of the polarization `B(ψ, φ)` with an endomorphism `T`:
`tr (B(ψ, φ) T) = ⟪ψ, T φ⟫ + ⟪φ, T ψ⟫ - Re⟪ψ, φ⟫ tr T`. -/
theorem trace_quadraticEndPolar_mul (ψ φ : E) (T : E →L[ℂ] E) :
    LinearMap.trace ℂ E (quadraticEndPolar ψ φ * T) =
      ⟪ψ, T φ⟫_ℂ + ⟪φ, T ψ⟫_ℂ - (Complex.re ⟪ψ, φ⟫_ℂ : ℂ) * LinearMap.trace ℂ E T := by
  rw [← trace_rankOne_mul, ← trace_rankOne_mul]
  simp [quadraticEndPolar_apply, sub_mul, add_mul, Module.End.mul_eq_comp]

variable [CompleteSpace E]

/-- In complex dimension two, `Q₀(ψ)` is a trace-free self-adjoint endomorphism. -/
theorem quadraticEnd_mem_traceFreeSelfAdjoint (h₂ : Module.finrank ℂ E = 2) (ψ : E) :
    quadraticEnd ψ ∈ traceFreeSelfAdjoint E :=
  mem_traceFreeSelfAdjoint.2 ⟨isSelfAdjoint_quadraticEnd ψ, trace_quadraticEnd h₂ ψ⟩

/-- In complex dimension two, the polarization `B(ψ, φ)` of `Q₀` is a trace-free self-adjoint
endomorphism. -/
theorem quadraticEndPolar_mem_traceFreeSelfAdjoint (h₂ : Module.finrank ℂ E = 2) (ψ φ : E) :
    quadraticEndPolar ψ φ ∈ traceFreeSelfAdjoint E :=
  mem_traceFreeSelfAdjoint.2
    ⟨isSelfAdjoint_quadraticEndPolar ψ φ, trace_quadraticEndPolar h₂ ψ φ⟩

/-- Against a trace-free self-adjoint `T`, the polarization of `Q₀` pairs as
`tr (B(ψ, φ) T) = 2 Re⟪T ψ, φ⟫`: the formal adjoint of the derivative `B(ψ, ·)` of `Q₀` is
`T ↦ 2 T ψ`. -/
theorem trace_quadraticEndPolar_mul_of_mem_traceFreeSelfAdjoint {T : E →L[ℂ] E}
    (hT : T ∈ traceFreeSelfAdjoint E) (ψ φ : E) :
    LinearMap.trace ℂ E (quadraticEndPolar ψ φ * T) = 2 * Complex.re ⟪T ψ, φ⟫_ℂ := by
  obtain ⟨hsa, htr⟩ := mem_traceFreeSelfAdjoint.1 hT
  have h : ⟪ψ, T φ⟫_ℂ = ⟪T ψ, φ⟫_ℂ := (hsa.isSymmetric ψ φ).symm
  rw [trace_quadraticEndPolar_mul, htr, h, ← inner_conj_symm φ (T ψ), Complex.add_conj]
  simp

end TauCeti.SeibergWitten
