/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Topology of the complement of the nonpositive integers in `ℂ`

The nonpositive integers `-{0, 1, 2, …}` form a closed countable subset of `ℂ`, so their
complement `{s : ℂ | ∀ n : ℕ, s ≠ -(n : ℂ)}` (the domain of holomorphy of `Complex.Gamma` and
`Complex.digamma`, and of denominator parameters in `₂F₁`) is open and connected in `ℂ`.
Shifting by `1` shows that `{b : ℂ | ∀ m : ℕ, b ≠ -((m + 1 : ℕ) : ℂ)}` is likewise open.

## Main results

* `Complex.isOpen_ne_neg_natCast`: `{s : ℂ | ∀ n : ℕ, s ≠ -(n : ℂ)}` is open.
* `Complex.isConnected_ne_neg_natCast`: `{s : ℂ | ∀ n : ℕ, s ≠ -(n : ℂ)}` is connected.
* `Complex.isPreconnected_ne_neg_natCast`: `{s : ℂ | ∀ n : ℕ, s ≠ -(n : ℂ)}` is preconnected.
* `Complex.isOpen_ne_neg_succ`: `{b : ℂ | ∀ m : ℕ, b ≠ -((m + 1 : ℕ) : ℂ)}` is open.
-/

public section

namespace Complex

/-- The complement of the nonpositive integers in `ℂ` is open. -/
theorem isOpen_ne_neg_natCast : IsOpen {s : ℂ | ∀ n : ℕ, s ≠ -(n : ℂ)} := by
  have hcl : IsClosed (Set.range fun n : ℕ ↦ -(n : ℂ)) := by
    have hnat : IsClosed (Set.range fun n : ℕ ↦ ((n : ℝ) : ℂ)) :=
      (isometry_ofReal.isClosedEmbedding.comp Nat.isClosedEmbedding_coe_real).isClosed_range
    convert hnat.preimage continuous_neg using 1
    ext z
    simp only [Set.mem_range, Set.mem_preimage, ofReal_natCast]
    exact exists_congr fun _ ↦ neg_eq_iff_eq_neg
  convert hcl.isOpen_compl using 1
  ext s
  simp [eq_comm]

/-- The complement of the nonpositive integers in `ℂ` is connected. -/
theorem isConnected_ne_neg_natCast : IsConnected {s : ℂ | ∀ n : ℕ, s ≠ -(n : ℂ)} := by
  have heq : {s : ℂ | ∀ n : ℕ, s ≠ -(n : ℂ)} = (Set.range fun n : ℕ ↦ -(n : ℂ))ᶜ := by
    ext s
    simp [eq_comm]
  rw [heq]
  exact (Set.countable_range _).isConnected_compl_of_one_lt_rank
    (rank_real_complex ▸ Nat.one_lt_ofNat)

/-- The complement of the nonpositive integers in `ℂ` is preconnected. -/
theorem isPreconnected_ne_neg_natCast : IsPreconnected {s : ℂ | ∀ n : ℕ, s ≠ -(n : ℂ)} :=
  isConnected_ne_neg_natCast.isPreconnected

/-- The complement of the negative integers `-1, -2, …` in `ℂ` is open. -/
theorem isOpen_ne_neg_succ : IsOpen {b : ℂ | ∀ m : ℕ, b ≠ -((m + 1 : ℕ) : ℂ)} := by
  convert isOpen_ne_neg_natCast.preimage (by fun_prop : Continuous fun b : ℂ ↦ b + 1) using 1
  ext b
  exact forall_congr' fun m ↦ not_congr
    ⟨fun h ↦ by rw [h]; push_cast; ring, fun h ↦ by push_cast; linear_combination h⟩

end Complex
