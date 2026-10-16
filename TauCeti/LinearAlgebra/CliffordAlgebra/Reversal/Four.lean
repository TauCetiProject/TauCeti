/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Grading
public import TauCeti.LinearAlgebra.CliffordAlgebra.Filtration
-- Private: the homogeneity of the powers of the vectors is used only in the parity bookkeeping.
import TauCeti.LinearAlgebra.CliffordAlgebra.Grading
-- Private: the reversal of a product of three vectors is used only in the odd-part computation.
import TauCeti.LinearAlgebra.CliffordAlgebra.Reversal.Basic

/-!
# Reversal on odd elements in dimension at most four

Reversal fixes every vector and, up to a vector, negates every product of three vectors
(`CliffordAlgebra.ι_mul_ι_mul_ι_add_reverse` in
`TauCeti/LinearAlgebra/CliffordAlgebra/Reversal/Basic.lean`). In dimension at most four the odd
part of the Clifford algebra is spanned by the vectors and the products of three vectors, so for
every odd element `y` the sum `y + reverse y` is a vector, and an odd element fixed by reversal is
a vector as soon as `2` is invertible.

This is the odd counterpart of `TauCeti/LinearAlgebra/CliffordAlgebra/Reversal/Three.lean`, where
an even element plus its reversal is a scalar in dimension three. Its use is the low-dimensional
identification of Spin groups: an even unit `x` with `reverse x * x = 1` sends a vector `ι v` to
the odd element `x * ι v * reverse x`, which reversal fixes, so in dimension at most four it is a
vector again. The bound is sharp: in dimension five the odd part also contains the volume element,
which reversal fixes.

## Main results

* `CliffordAlgebra.add_reverse_mem_range_ι_of_mem_evenOdd_one_of_finrank_le_four`: in dimension
  at most four, an odd element plus its reversal is a vector.
* `CliffordAlgebra.mem_range_ι_of_mem_evenOdd_one_of_reverse_eq_of_finrank_le_four`: in
  dimension at most four, an odd element fixed by reversal is a vector.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §2.
-/

public section

namespace CliffordAlgebra

universe u v

section Field

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] (Q : QuadraticForm K V)

/-- **In dimension at most four, an odd element plus its reversal is a vector.** The odd part is
then spanned by the vectors and the products of three vectors, and reversal fixes the former and
negates the latter up to a vector. -/
theorem add_reverse_mem_range_ι_of_mem_evenOdd_one_of_finrank_le_four
    (hV : Module.finrank K V ≤ 4) {y : CliffordAlgebra Q} (hy : y ∈ evenOdd Q 1) :
    y + reverse y ∈ LinearMap.range (ι Q) := by
  -- `P` is the submodule of elements whose sum with their reversal is a vector.
  let P : Submodule K (CliffordAlgebra Q) := (LinearMap.range (ι Q)).comap (LinearMap.id + reverse)
  let A : Submodule K (CliffordAlgebra Q) := LinearMap.range (ι Q)
  let E : Submodule K (CliffordAlgebra Q) := A ^ 0 ⊔ A ^ 2 ⊔ A ^ 4
  let O : Submodule K (CliffordAlgebra Q) := A ^ 1 ⊔ A ^ 3
  -- The dimension bound truncates the filtration at degree four; split those powers by parity.
  have hsplit : filtration Q 4 ≤ E ⊔ O := by
    rw [filtration_le_iff]
    intro l hl
    have hp := prod_map_ι_mem_pow Q l
    interval_cases _ : l.length
    · exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left hp))
    · exact Submodule.mem_sup_right (Submodule.mem_sup_left hp)
    · exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_right hp))
    · exact Submodule.mem_sup_right (Submodule.mem_sup_right hp)
    · exact Submodule.mem_sup_left (Submodule.mem_sup_right hp)
  have hE : E ≤ evenOdd Q 0 :=
    sup_le (sup_le (ι_range_pow_le_evenOdd 0) (ι_range_pow_le_evenOdd 2))
      (ι_range_pow_le_evenOdd 4)
  have hO : O ≤ evenOdd Q 1 :=
    sup_le (ι_range_pow_le_evenOdd 1) (ι_range_pow_le_evenOdd 3)
  -- Reversal fixes a vector and sends a product of three vectors to a vector minus itself.
  have hA1P : A ^ 1 ≤ P := by
    rw [pow_one]
    rintro _ ⟨v, rfl⟩
    exact ⟨v + v, by simp⟩
  have hA3P : A ^ 3 ≤ P := by
    rw [pow_succ, pow_two]
    refine Submodule.mul_le.2 fun x hx n hn => ?_
    obtain ⟨c, rfl⟩ := hn
    refine Submodule.mul_induction_on hx ?_ fun x y hx hy => ?_
    · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      exact ⟨_, (ι_mul_ι_mul_ι_add_reverse Q a b c).symm⟩
    · rw [add_mul]
      exact P.add_mem hx hy
  have hOP : O ≤ P := sup_le hA1P hA3P
  -- Decompose `y` along the parity split; its even component vanishes.
  have hyfiltration : y ∈ filtration Q 4 := by
    rw [filtration_eq_top_of_finrank_le Q hV]
    trivial
  obtain ⟨e, he, o, ho, rfl⟩ := Submodule.mem_sup.mp (hsplit hyfiltration)
  have heodd : e ∈ evenOdd Q 1 := by
    simpa using (evenOdd Q 1).sub_mem hy (hO ho)
  have hezero : e = 0 :=
    (Submodule.disjoint_def.mp (evenOdd_isCompl (Q := Q)).disjoint) e (hE he) heodd
  rw [hezero, zero_add]
  exact hOP ho

variable [Invertible (2 : K)]

/-- **In dimension at most four, an odd element fixed by reversal is a vector.** -/
theorem mem_range_ι_of_mem_evenOdd_one_of_reverse_eq_of_finrank_le_four
    (hV : Module.finrank K V ≤ 4) {y : CliffordAlgebra Q} (hy : y ∈ evenOdd Q 1)
    (hrev : reverse y = y) : y ∈ LinearMap.range (ι Q) := by
  have h := add_reverse_mem_range_ι_of_mem_evenOdd_one_of_finrank_le_four Q hV hy
  rw [hrev, ← two_smul K y] at h
  simpa using (LinearMap.range (ι Q)).smul_mem (⅟(2 : K)) h

end Field

end CliffordAlgebra
