/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Bilinear
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import TauCeti.Analysis.Fourier.FiniteAbelian.ModuleDual
import TauCeti.Data.Matrix.Block

/-!
# The Fourier transform on matrices for the trace pairing

For an additive character `ψ` of a finite commutative semiring `R` with values in a commutative
semiring `Λ`, `AddChar.traceFourier ψ f y = ∑ x, f x * ψ (Tr (y x))` is the unnormalized Fourier
transform of a function `f` on `m × n` matrices over `R`, a function of the `n × m` matrices `y`,
for the trace pairing `(y, x) ↦ Tr (y x)`, `AddChar.traceFourier_apply`. The transform is
`Λ`-linear in `f`, and it is symmetric for the pairing of functions by summation:
`∑ y, F(f) y * g y = ∑ x, f x * F(g) x`, `AddChar.sum_traceFourier_mul`.

When `R` is a ring, `ψ` is primitive and `Λ` is a domain, the trace pairing is orthogonal:
the sum of `ψ (Tr (y x))` over all `x` vanishes for every nonzero `y`,
`AddChar.IsPrimitive.sum_trace_mul_eq_zero`, and is the number of matrices for `y = 0`,
`AddChar.IsPrimitive.sum_trace_mul_eq_ite`. This is the orthogonality relation behind Fourier
inversion on matrices. Applied to the off-diagonal block `s` of the block matrices `(η s; 0 1)`,
it shows that summing the transform of a function `G` of `(m ⊕ l) × (n ⊕ l)` matrices at these
points over `s` keeps only the block matrices `(A B; 0 D)`, with weight `ψ (Tr (η A)) ψ (Tr D)`,
`AddChar.IsPrimitive.sum_traceFourier_fromBlocks`.

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

variable {R Λ m n : Type*} [Fintype R] [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

section CommSemiring

variable [CommSemiring R] [CommSemiring Λ]

/-- The unnormalized Fourier transform on `m × n` matrices for the trace pairing with the
`n × m` matrices. -/
noncomputable def traceFourier (ψ : AddChar R Λ) (f : Matrix m n R → Λ)
    (y : Matrix n m R) : Λ :=
  ψ.fourierTransform f ((Matrix.traceLinearMap n R R).comp (mulLeftLinearMap n R y))

/-- The value of the matrix Fourier transform is the sum against the trace character. -/
theorem traceFourier_apply (ψ : AddChar R Λ) (f : Matrix m n R → Λ) (y : Matrix n m R) :
    ψ.traceFourier f y = ∑ x, f x * ψ (y * x).trace := by
  simp [traceFourier, fourierTransform_apply]

/-- The trace Fourier transform sends the zero function to zero. -/
@[simp]
theorem traceFourier_zero (ψ : AddChar R Λ) :
    ψ.traceFourier (0 : Matrix m n R → Λ) = 0 := by
  funext y
  simp only [traceFourier, map_zero, Pi.zero_apply]

/-- The trace Fourier transform preserves addition. -/
@[simp]
theorem traceFourier_add (ψ : AddChar R Λ) (f g : Matrix m n R → Λ) :
    ψ.traceFourier (f + g) = ψ.traceFourier f + ψ.traceFourier g := by
  funext y
  simp only [traceFourier, map_add, Pi.add_apply]

/-- The trace Fourier transform commutes with scalar multiplication. -/
@[simp]
theorem traceFourier_smul (ψ : AddChar R Λ) (c : Λ) (f : Matrix m n R → Λ) :
    ψ.traceFourier (c • f) = c • ψ.traceFourier f := by
  funext y
  simp only [traceFourier, map_smul, Pi.smul_apply]

/-- The trace Fourier transform is symmetric for the pairing of functions by summation: pairing
the transform of `f` with `g` is pairing `f` with the transform of `g`. -/
theorem sum_traceFourier_mul (ψ : AddChar R Λ) (f : Matrix m n R → Λ) (g : Matrix n m R → Λ) :
    ∑ y, ψ.traceFourier f y * g y = ∑ x, f x * ψ.traceFourier g x := by
  simp only [traceFourier_apply, sum_mul, mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun x _ ↦ sum_congr rfl fun y _ ↦ by
    rw [Matrix.trace_mul_comm y x]
    ring

end CommSemiring

variable [CommRing R]

/-- For a primitive additive character with values in a domain, the trace pairing is
orthogonal: the sum of `ψ (Tr (y x))` over all `m × n` matrices `x` vanishes when the
`n × m` matrix `y` is nonzero. -/
theorem IsPrimitive.sum_trace_mul_eq_zero [CommRing Λ] [IsDomain Λ] {ψ : AddChar R Λ}
    (hψ : ψ.IsPrimitive) {y : Matrix n m R} (hy : y ≠ 0) :
    ∑ x : Matrix m n R, ψ (y * x).trace = 0 := by
  let κ : AddChar (Matrix m n R) Λ :=
    ψ.compAddMonoidHom ((Matrix.traceAddMonoidHom n R).comp
      (mulLeftLinearMap n R y).toAddMonoidHom)
  have hκ (x : Matrix m n R) : κ x = ψ (y * x).trace := by
    simp [κ]
  rw [← Fintype.sum_congr _ _ hκ]
  refine sum_eq_zero_of_ne_one fun h ↦ ?_
  obtain ⟨i, j, hij⟩ : ∃ i j, y i j ≠ 0 := by
    by_contra! h
    exact hy (Matrix.ext h)
  refine hψ hij (eq_one_iff.mpr fun r ↦ ?_)
  simpa [hκ, mulShift_apply, Matrix.trace_mul_single, mul_comm] using
    eq_one_iff.mp h (Matrix.single j i r)

/-- For a primitive additive character with values in a domain, the sum of `ψ (Tr (y x))` over all
`m × n` matrices `x` is the number of these matrices when `y = 0`, and `0` otherwise. -/
theorem IsPrimitive.sum_trace_mul_eq_ite [DecidableEq R] [CommRing Λ] [IsDomain Λ]
    {ψ : AddChar R Λ} (hψ : ψ.IsPrimitive) (y : Matrix n m R) :
    ∑ x : Matrix m n R, ψ (y * x).trace =
      if y = 0 then (Fintype.card (Matrix m n R) : Λ) else 0 := by
  split_ifs with hy
  · simp [hy]
  · exact hψ.sum_trace_mul_eq_zero hy

/-- **Averaging the transform over an off-diagonal block.** For a primitive additive character
with values in a domain and a function `G` of `(m ⊕ l) × (n ⊕ l)` matrices, the sum over the
blocks `s` of the Fourier transform of `G` at the block matrices `(η s; 0 1)` is `#M_{n×l}(R)`
times the sum of `G (A B; 0 D) * (ψ (Tr (η A)) * ψ (Tr D))` over the blocks `A`, `B`, `D`: by
orthogonality in `s`, the matrices with a nonzero lower left block do not contribute. -/
theorem IsPrimitive.sum_traceFourier_fromBlocks {l : Type*} [Fintype l] [DecidableEq l]
    [CommRing Λ] [IsDomain Λ] {ψ : AddChar R Λ} (hψ : ψ.IsPrimitive)
    (G : Matrix (m ⊕ l) (n ⊕ l) R → Λ) (η : Matrix n m R) :
    ∑ s : Matrix n l R, ψ.traceFourier G (Matrix.fromBlocks η s 0 1) =
      Nat.card (Matrix n l R) * ∑ A, ∑ B, ∑ D,
        G (Matrix.fromBlocks A B 0 D) * (ψ (η * A).trace * ψ D.trace) := by
  classical
  have hS (A : Matrix m n R) (B : Matrix m l R) (C : Matrix l n R) (D : Matrix l l R) :
      ∑ s : Matrix n l R, ψ (Matrix.fromBlocks η s 0 1 * Matrix.fromBlocks A B C D).trace =
        ψ (η * A).trace * ψ D.trace * if C = 0 then (Nat.card (Matrix n l R) : Λ) else 0 := by
    rw [Nat.card_eq_fintype_card, ← hψ.sum_trace_mul_eq_ite C, mul_sum]
    refine sum_congr rfl fun s _ ↦ ?_
    rw [Matrix.fromBlocks_multiply, Matrix.trace_fromBlocks, Matrix.zero_mul, Matrix.one_mul,
      zero_add, Matrix.trace_add, Matrix.trace_mul_comm s C, map_add_eq_mul, map_add_eq_mul]
    ring
  calc ∑ s : Matrix n l R, ψ.traceFourier G (Matrix.fromBlocks η s 0 1)
      = ∑ x, G x * ∑ s : Matrix n l R, ψ (Matrix.fromBlocks η s 0 1 * x).trace := by
        simp_rw [traceFourier_apply, mul_sum]
        exact sum_comm
    _ = _ := by
        simp_rw [Matrix.sum_fromBlocks (fun x ↦ G x * _), hS, mul_sum]
        refine sum_congr rfl fun A _ ↦ sum_congr rfl fun B _ ↦ ?_
        rw [sum_eq_single (0 : Matrix l n R) (fun C _ hC ↦ by simp [hC]) (by simp)]
        exact sum_congr rfl fun D _ ↦ by simp only [ite_true]; ring

end AddChar
