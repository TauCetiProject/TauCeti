/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.Chebyshev.Divisibility

/-!
# Quantum integers at a loop parameter

For an element `δ` of a commutative ring, the quantum integers `[n]` at `δ` are defined by
`[0] = 0`, `[1] = 1` and `[n + 2] = δ [n + 1] - [n]`. When `δ = q + q⁻¹` for a unit `q` they are
the symmetric quantum integers `[n] = q^(n-1) + q^(n-3) + ⋯ + q^(1-n)`, but no `q` is needed to
define them: `[n]` is the value at `δ` of the rescaled Chebyshev polynomial of the second kind
`S_(n-1)`, Mathlib's `Polynomial.Chebyshev.S` at the integer index `n - 1`. This is the form in
which they enter diagrammatic algebra, where `δ` is the value of a closed loop: the Jones–Wenzl
recursions, the trace of the Jones–Wenzl projections and the Gram determinants of Temperley–Lieb
cell modules are all expressed through `[n]` at the loop value `δ`.

This file defines `TauCeti.qInt R δ n` as that Chebyshev evaluation, absorbing the shift of the
index by one, and transfers the polynomial identities of
`TauCeti/RingTheory/Polynomial/Chebyshev/Divisibility.lean` to it. Note that `[0] = 0` for every
`δ`, so nonvanishing hypotheses on quantum integers concern the indices `n ≥ 1` only.

## Main definitions

* `TauCeti.qInt R δ n`: the quantum integer `[n]` at the loop parameter `δ`.

## Main results

* `TauCeti.qInt_add_two`: the recurrence `[n + 2] = δ [n + 1] - [n]`.
* `TauCeti.qInt_add_add_one`: `[m + n + 1] = [m + 1] [n + 1] - [m] [n]`.
* `TauCeti.qInt_mul`: `[mn]` at `δ` is `[m]` at `δ` times `[n]` at `Cₘ(δ)`, where `Cₘ` is the
  rescaled Chebyshev polynomial of the first kind, so that `Cₘ(q + q⁻¹) = qᵐ + q⁻ᵐ`.
* `TauCeti.qInt_dvd_qInt`: `[m] ∣ [n]` whenever `m ∣ n`.
* `TauCeti.qInt_two_left`, `TauCeti.qInt_neg_two_left`: at `δ = 2` and `δ = -2`, `[n]` is `n` and
  `(-1)^(n+1) n`; in characteristic zero these never vanish for `n ≥ 1`, while in characteristic
  `p` they vanish at `n = p`.
* `RingHom.map_qInt`: quantum integers commute with ring homomorphisms.

## References

* L. H. Kauffman and S. L. Lins, *Temperley–Lieb Recoupling Theory and Invariants of
  3-Manifolds*, Annals of Mathematics Studies 134, Princeton University Press, 1994, for the
  quantum integers as functions of the loop value.
-/

public section

open Polynomial Polynomial.Chebyshev

namespace TauCeti

variable (R : Type*) [CommRing R]

/-- The **quantum integer** `[n]` at the loop parameter `δ`: the value at `δ` of the rescaled
Chebyshev polynomial of the second kind `S_(n-1)`, with the index taken in `ℤ` so that
`[0] = S_(-1)(δ) = 0`. It satisfies `[1] = 1`, `[2] = δ` and `[n + 2] = δ [n + 1] - [n]`
(`TauCeti.qInt_add_two`), and for a unit `q` with `δ = q + q⁻¹` it is
`q^(n-1) + q^(n-3) + ⋯ + q^(1-n)`. -/
noncomputable def qInt (δ : R) (n : ℕ) : R :=
  (S R ((n : ℤ) - 1)).eval δ

variable {R}

/-- Unfolding `TauCeti.qInt` as the value at `δ` of the Chebyshev polynomial `S_(n-1)`. -/
theorem qInt_def (δ : R) (n : ℕ) : qInt R δ n = (S R ((n : ℤ) - 1)).eval δ := (rfl)

/-- `[0] = 0` at every loop parameter. -/
@[simp]
theorem qInt_zero (δ : R) : qInt R δ 0 = 0 := by
  simp [qInt_def]

/-- `[1] = 1` at every loop parameter. -/
@[simp]
theorem qInt_one (δ : R) : qInt R δ 1 = 1 := by
  simp [qInt_def]

/-- `[2] = δ`. -/
@[simp]
theorem qInt_two (δ : R) : qInt R δ 2 = δ := by
  simp [qInt_def]

/-- The defining recurrence of the quantum integers: `[n + 2] = δ [n + 1] - [n]`. -/
theorem qInt_add_two (δ : R) (n : ℕ) :
    qInt R δ (n + 2) = δ * qInt R δ (n + 1) - qInt R δ n := by
  have h : ((n + 2 : ℕ) : ℤ) - 1 = n + 1 := by push_cast; ring
  rw [qInt_def, h, S_add_one]
  simp [qInt_def]

/-- The **addition formula** for quantum integers: `[m + n + 1] = [m + 1] [n + 1] - [m] [n]`. -/
theorem qInt_add_add_one (δ : R) (m n : ℕ) :
    qInt R δ (m + n + 1) = qInt R δ (m + 1) * qInt R δ (n + 1) - qInt R δ m * qInt R δ n := by
  have h := congrArg (eval δ) (S_add R m n)
  simp only [eval_sub, eval_mul] at h
  simpa [qInt_def] using h

/-- The **multiplication formula** for quantum integers: `[mn]` at `δ` is `[m]` at `δ` times `[n]`
at `Cₘ(δ)`, where `Cₘ` is the rescaled Chebyshev polynomial of the first kind. For a unit `q` with
`δ = q + q⁻¹` this is `[mn]_q = [m]_q [n]_{qᵐ}`, since `Cₘ(q + q⁻¹) = qᵐ + q⁻ᵐ`. -/
theorem qInt_mul (δ : R) (m n : ℕ) :
    qInt R δ (m * n) = qInt R δ m * qInt R ((C R m).eval δ) n := by
  have h := congrArg (eval δ) (S_mul_sub_one R m n)
  simpa [qInt_def, eval_comp] using h

/-- **Divisibility** of quantum integers: `[m] ∣ [n]` whenever `m ∣ n`. -/
theorem qInt_dvd_qInt (δ : R) {m n : ℕ} (h : m ∣ n) : qInt R δ m ∣ qInt R δ n := by
  obtain ⟨k, rfl⟩ := h
  exact Dvd.intro _ (qInt_mul δ m k).symm

/-- At the loop parameter `δ = 2` the quantum integer `[n]` is the integer `n`. -/
@[simp]
theorem qInt_two_left (n : ℕ) : qInt R 2 n = n := by
  simp [qInt_def]

/-- At the loop parameter `δ = -2` the quantum integer `[n]` is `(-1)^(n+1) n`. -/
@[simp]
theorem qInt_neg_two_left (n : ℕ) : qInt R (-2) n = (-1) ^ (n + 1) * n := by
  rcases n with _ | n
  · simp
  · simp [qInt_def, pow_succ]

end TauCeti

namespace RingHom

open TauCeti

variable {R R' : Type*} [CommRing R] [CommRing R']

/-- Quantum integers commute with ring homomorphisms: `f [n]_δ = [n]_{f δ}`. -/
@[simp]
theorem map_qInt (f : R →+* R') (δ : R) (n : ℕ) :
    f (qInt R δ n) = qInt R' (f δ) n := by
  rw [qInt_def, qInt_def, ← eval_map_apply, map_S]

end RingHom
