/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Common complements of subspaces

Two subspaces of a finite-dimensional vector space have a common complement if and only if
they have the same dimension. In particular, kernels of two surjective linear maps to
equal-dimensional spaces admit a common transverse subspace. In differential geometry this
lets one choose a slice transverse to both the source and target fibres of a groupoid.

The argument works over any division ring, including finite fields. Choose a maximal subspace
disjoint from both given subspaces. If neither sum is the whole space, a vector outside the
union of the two sums extends this subspace, contradicting maximality. Equal dimensions then
ensure that complementarity to either subspace implies complementarity to both.
-/

public section

namespace Submodule

open Module

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- Subspaces of equal dimension in a finite-dimensional vector space have a common
complement. No assumption on the cardinality of the division ring is needed. -/
theorem exists_isCompl_isCompl_of_finrank_eq (P Q : Submodule K V)
    (hPQ : finrank K P = finrank K Q) :
    ∃ C : Submodule K V, IsCompl P C ∧ IsCompl Q C := by
  classical
  obtain ⟨C, hC, hmax⟩ := exists_maximal_of_wellFoundedGT
    (fun C : Submodule K V ↦ Disjoint P C ∧ Disjoint Q C) ⟨⊥, by simp⟩
  -- A vector outside both sums would enlarge the maximal common disjoint subspace.
  have htop : P ⊔ C = ⊤ ∨ Q ⊔ C = ⊤ := by
    by_contra! h
    obtain ⟨u, hu⟩ := SetLike.exists_notMem_of_ne_top (P ⊔ C) h.1
    obtain ⟨v, hv⟩ := SetLike.exists_notMem_of_ne_top (Q ⊔ C) h.2
    have hex : ∃ w : V, w ∉ P ⊔ C ∧ w ∉ Q ⊔ C := by
      by_cases huQ : u ∈ Q ⊔ C
      · by_cases hvP : v ∈ P ⊔ C
        · exact ⟨u + v, fun hw ↦ hu ((P ⊔ C).add_mem_iff_left hvP |>.mp hw),
            fun hw ↦ hv ((Q ⊔ C).add_mem_iff_right huQ |>.mp hw)⟩
        · exact ⟨v, hvP, hv⟩
      · exact ⟨u, hu, huQ⟩
    obtain ⟨w, hwP, hwQ⟩ := hex
    have hPw := hC.1.disjoint_sup_right_of_disjoint_sup_left
      (disjoint_span_singleton_of_notMem hwP)
    have hQw := hC.2.disjoint_sup_right_of_disjoint_sup_left
      (disjoint_span_singleton_of_notMem hwQ)
    have hle := hmax ⟨hPw, hQw⟩ le_sup_left
    have hwC : w ∈ C := hle (mem_sup_right (mem_span_singleton_self w))
    exact hwP (mem_sup_right hwC)
  -- Disjointness and equality of dimensions turn either spanning sum into both complements.
  have hdimP := finrank_sup_add_finrank_inf_eq P C
  have hdimQ := finrank_sup_add_finrank_inf_eq Q C
  rw [hC.1.eq_bot, finrank_bot, add_zero] at hdimP
  rw [hC.2.eq_bot, finrank_bot, add_zero] at hdimQ
  have hdim : finrank K V = finrank K P + finrank K C := by
    rcases htop with htop | htop
    · rw [htop, finrank_top] at hdimP
      exact hdimP
    · rw [htop, finrank_top, ← hPQ] at hdimQ
      exact hdimQ
  exact ⟨C, (isCompl_iff_disjoint P C hdim.le).2 hC.1,
    (isCompl_iff_disjoint Q C (by omega)).2 hC.2⟩

/-- Two subspaces of a finite-dimensional vector space have a common complement exactly when
their dimensions agree. -/
theorem exists_isCompl_isCompl_iff_finrank_eq (P Q : Submodule K V) :
    (∃ C : Submodule K V, IsCompl P C ∧ IsCompl Q C) ↔ finrank K P = finrank K Q := by
  constructor
  · rintro ⟨C, hP, hQ⟩
    have := finrank_add_eq_of_isCompl hP
    have := finrank_add_eq_of_isCompl hQ
    omega
  · exact exists_isCompl_isCompl_of_finrank_eq P Q

end Submodule
