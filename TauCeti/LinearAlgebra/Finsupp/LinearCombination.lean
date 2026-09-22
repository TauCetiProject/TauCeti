/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.RingTheory.Noetherian.Defs

/-!
# Linear combinations from independence and from Noetherianity

This file collects two complements to Mathlib's description of the span of a family by linear
combinations: membership in the span of a *linearly independent* family is witnessed by a unique
finitely supported combination, and in a *Noetherian* module every sequence has a term that is a
linear combination of its predecessors.

## Main statements

* `LinearIndependent.mem_span_range_iff_existsUnique`: membership in the span of a
  linearly independent family is equivalent to having unique finitely supported coordinates.
* `TauCeti.exists_sum_smul_eq_of_isNoetherian`: in a Noetherian module some term of a sequence is
  a linear combination of its predecessors.
-/

public section

section

variable {ι R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-- An element lies in the span of a linearly independent family exactly when it has a unique
finitely supported expression in that family. -/
theorem _root_.LinearIndependent.mem_span_range_iff_existsUnique {v : ι → M}
    (h : LinearIndependent R v) (x : M) :
    x ∈ Submodule.span R (Set.range v) ↔
      ∃! a : ι →₀ R, a.sum (fun i r => r • v i) = x := by
  rw [Finsupp.mem_span_range_iff_exists_finsupp]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, ha, fun b hb => ?_⟩
    apply h.finsuppLinearCombination_injective
    simpa only [Finsupp.linearCombination_apply] using hb.trans ha.symm
  · exact ExistsUnique.exists

end

namespace TauCeti

variable (R : Type*) {M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-- **In a Noetherian module some term of a sequence is a linear combination of its
predecessors.**  The spans of the initial segments of `v` form an increasing chain of submodules,
which must stabilize; at the first repetition `v n` already lies in the span of the earlier terms.
-/
theorem exists_sum_smul_eq_of_isNoetherian [IsNoetherian R M] (v : ℕ → M) :
    ∃ (n : ℕ) (c : Fin n → R), ∑ i : Fin n, c i • v i = v n := by
  obtain ⟨n, hn⟩ := monotone_stabilizes_iff_noetherian.mpr ‹IsNoetherian R M›
    ⟨fun m => Submodule.span R (v '' Set.Iio m),
      fun i j hij => Submodule.span_mono (Set.image_mono (Set.Iio_subset_Iio hij))⟩
  have hstep : Submodule.span R (v '' Set.Iio n) = Submodule.span R (v '' Set.Iio (n + 1)) :=
    hn (n + 1) (Nat.le_succ n)
  have hrange : (Set.range fun i : Fin n => v i) = v '' Set.Iio n := by
    ext z
    exact ⟨fun ⟨i, hi⟩ => ⟨i, i.isLt, hi⟩, fun ⟨i, hi, hiz⟩ => ⟨⟨i, hi⟩, hiz⟩⟩
  have hmem : v n ∈ Submodule.span R (Set.range fun i : Fin n => v i) := by
    rw [hrange, hstep]
    exact Submodule.subset_span ⟨n, Nat.lt_succ_self n, rfl⟩
  exact ⟨n, (Submodule.mem_span_range_iff_exists_fun _).mp hmem⟩

end TauCeti
