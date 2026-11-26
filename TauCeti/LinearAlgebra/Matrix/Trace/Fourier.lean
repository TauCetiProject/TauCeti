/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import TauCeti.Analysis.Fourier.FiniteAbelian.ModuleDual

/-!
# The Fourier transform on square matrices for the trace pairing

For an additive character `ψ` of a finite commutative ring `R` with values in a commutative
semiring `Λ`, `AddChar.traceFourier ψ f y = ∑ x, f x * ψ (Tr (y x))` is the unnormalized Fourier
transform of a function `f` on `n × n` matrices over `R` for the trace pairing
`(y, x) ↦ Tr (y x)`, `AddChar.traceFourier_apply`.

When `ψ` is primitive and `Λ` is a domain the trace pairing is orthogonal: the sum of
`ψ (Tr (y x))` over all `x` vanishes for every nonzero `y`,
`AddChar.IsPrimitive.sum_trace_mul_eq_zero`. This is the orthogonality relation behind Fourier
inversion on matrices.

## Provenance

The orthogonality relation adapts `New.sum_addChar_trace_mul` (file
`src/Lib/General/Analysis/FiniteFourier.lean`) of L. Alpöge's Lean formalization of the
Riemann hypothesis for Dirichlet L-functions,
https://github.com/leanprover-community/riemann-hypothesis
(commit `af5639fc3c5697fd8050d3fb58515e2efc606139`), there stated for complex values and
rectangular matrices. The transform here is `AddChar.fourierTransform` for the trace functional.
-/

public section

namespace AddChar

open Finset

variable {R Λ n : Type*} [CommRing R] [Fintype R] [Fintype n] [DecidableEq n]

section CommSemiring

variable [CommSemiring Λ]

/-- The unnormalized Fourier transform on square matrices for the trace pairing. -/
noncomputable def traceFourier (ψ : AddChar R Λ) (f : Matrix n n R → Λ)
    (y : Matrix n n R) : Λ :=
  ψ.fourierTransform f ((Matrix.traceLinearMap n R R).comp (LinearMap.mulLeft R y))

/-- The value of the matrix Fourier transform is the sum against the trace character. -/
theorem traceFourier_apply (ψ : AddChar R Λ) (f : Matrix n n R → Λ) (y : Matrix n n R) :
    ψ.traceFourier f y = ∑ x, f x * ψ (y * x).trace := by
  simp [traceFourier, fourierTransform_apply]

end CommSemiring

/-- For a primitive additive character with values in a domain, the trace pairing is
orthogonal: the sum of `ψ (Tr (y x))` over all square matrices `x` vanishes when `y ≠ 0`. -/
theorem IsPrimitive.sum_trace_mul_eq_zero [CommRing Λ] [IsDomain Λ] {ψ : AddChar R Λ}
    (hψ : ψ.IsPrimitive) {y : Matrix n n R} (hy : y ≠ 0) :
    ∑ x : Matrix n n R, ψ (y * x).trace = 0 := by
  let κ : AddChar (Matrix n n R) Λ :=
    ψ.compAddMonoidHom ((Matrix.traceAddMonoidHom n R).comp (AddMonoidHom.mulLeft y))
  have hκ (x : Matrix n n R) : κ x = ψ (y * x).trace := by
    rw [compAddMonoidHom_apply, AddMonoidHom.comp_apply, AddMonoidHom.coe_mulLeft,
      Matrix.traceAddMonoidHom_apply]
  rw [← Fintype.sum_congr _ _ hκ]
  refine sum_eq_zero_of_ne_one fun h ↦ ?_
  obtain ⟨i, j, hij⟩ : ∃ i j, y i j ≠ 0 := by
    by_contra! h
    exact hy (Matrix.ext h)
  refine hψ hij (eq_one_iff.mpr fun r ↦ ?_)
  simpa [hκ, mulShift_apply, Matrix.trace_mul_single, mul_comm] using
    eq_one_iff.mp h (Matrix.single j i r)

end AddChar
