/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TemperleyLieb.JonesWenzl
public import TauCeti.Algebra.TemperleyLieb.MarkovTrace
import Mathlib.Tactic.LinearCombination

/-!
# Quantum dimensions of Jones–Wenzl projections

Every unnormalized Markov trace takes the value `qInt R δ (n + 1)` on the Jones–Wenzl
projection on `n` strands, whenever `[1], …, [n]` are units. In particular the next quantum
integer may vanish: this is the quantum-dimension calculation used to detect negligible
projections. The result also applies to any normalized element annihilated by the generators,
by uniqueness of the projection, and specializes to the spin-model trace `markovTrace`.

## References

* H. Wenzl, *On sequences of projections*, C. R. Math. Rep. Acad. Sci. Canada 9 (1987), 5–9.
* L. H. Kauffman and S. L. Lins, *Temperley–Lieb Recoupling Theory and Invariants of
  3-Manifolds*, Annals of Mathematics Studies 134, Princeton University Press, 1994.

The calculation uses `TauCeti.TemperleyLieb.jonesWenzl_add_two` and its idempotence theorem.
-/

public section

namespace TauCeti.TemperleyLieb

variable {R : Type*} [CommRing R] {δ : R}
  {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}

namespace IsMarkovTrace

/-- Every Markov trace takes the value `[n + 1]` on the Jones–Wenzl projection on `n`
strands, provided `[1], …, [n]` are units. No assumption on `[n + 1]` is needed. -/
@[simp]
theorem map_jonesWenzl (htr : IsMarkovTrace R δ tr) :
    ∀ n, (∀ k ∈ Finset.Icc 1 n, IsUnit (qInt R δ k)) →
      tr n (jonesWenzl δ n) = qInt R δ (n + 1)
  | 0, _ => by simp [htr.map_one]
  | 1, _ => by simp [htr.map_one]
  | m + 2, h => by
    have hprev : ∀ k ∈ Finset.Icc 1 (m + 1), IsUnit (qInt R δ k) :=
      fun k hk ↦ h k (Finset.Icc_subset_Icc le_rfl (by omega) hk)
    have hid := (isIdempotentElem_jonesWenzl hprev).eq
    rw [jonesWenzl_add_two, map_sub, map_smul, htr.map_strandIncl,
      htr.map_strandIncl_mul_e_last_mul, hid, htr.map_jonesWenzl (m + 1) hprev,
      smul_eq_mul, qInt_add_two δ (m + 1)]
    linear_combination -(qInt R δ (m + 1)) *
      Ring.inverse_mul_cancel _ (h (m + 2) (by simp))

/-- The quantum-dimension formula for any element of augmentation `1` annihilated on the
left by the generators. One-sided annihilation already characterizes the Jones–Wenzl projection.
-/
theorem apply_jonesWenzl (htr : IsMarkovTrace R δ tr) {n : ℕ}
    (h : ∀ k ∈ Finset.Icc 1 n, IsUnit (qInt R δ k)) (f : TemperleyLieb R δ n)
    (hf : aug f = 1)
    (hfe : ∀ i : Fin (n - 1), e δ i * f = 0) :
    tr n f = qInt R δ (n + 1) := by
  rw [eq_jonesWenzl_of_e_mul_eq_zero h hf hfe]
  exact htr.map_jonesWenzl n h

end IsMarkovTrace

/-- The spin-model trace of the Jones–Wenzl projection is its quantum dimension. -/
theorem markovTrace_jonesWenzl (q : Rˣ) (hδ : δ = -((q : R) + ((q⁻¹ : Rˣ) : R))) {n : ℕ}
    (h : ∀ k ∈ Finset.Icc 1 n, IsUnit (qInt R δ k)) :
    markovTrace q hδ (jonesWenzl δ n) = qInt R δ (n + 1) :=
  (isMarkovTrace_markovTrace q hδ).map_jonesWenzl n h

end TauCeti.TemperleyLieb
