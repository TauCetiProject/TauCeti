/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.LimitGroup.ResiduallyFree
import TauCeti.GroupTheory.FreeGroup.ProperPower.Commutator

/-!
# Commutators in residually free groups

A nontrivial commutator of a free group is not a proper power (Schützenberger,
`IsFreeGroup.not_isProperPower_commutator`). The same holds in every residually free group, since
a homomorphism to a free group keeping the commutator nontrivial keeps it from being a proper
power.

Two commuting nontrivial commutators of a free group are therefore equal or inverse to each other:
both generate the centralizer of either. The same holds in every fully residually free group, by
discrimination of the two commutators, their product and their quotient.

## Main results

* `TauCeti.LimitGroup.IsResiduallyFree.not_isProperPower_commutator`: a nontrivial commutator of a
  residually free group is not a proper power.
* `TauCeti.LimitGroup.IsFullyResiduallyFree.commutator_eq_or_eq_inv_of_commute`: two commuting
  nontrivial commutators of a fully residually free group are equal or inverse to each other.

## References

* O. Kharlampovich, A. Myasnikov, *Irreducible affine varieties over a free group. I*,
  J. Algebra 200 (1998), §2, Lemma 12, and §3, Form 1.
* M. P. Schützenberger, *Sur l'équation `a^{2+n} = b^{2+m} c^{2+p}` dans un groupe libre*,
  C. R. Acad. Sci. Paris 248 (1959), 2435–2436.
-/

public section

open scoped commutatorElement

open Monoid

namespace TauCeti.LimitGroup

variable {G : Type*} [Group G]

/-- A nontrivial commutator of a residually free group is not a proper power. -/
theorem IsResiduallyFree.not_isProperPower_commutator (hG : IsResiduallyFree G) {a b : G}
    (h : ⁅a, b⁆ ≠ 1) : ¬IsProperPower ⁅a, b⁆ := fun hp => by
  obtain ⟨ι, φ, hφ⟩ := isResiduallyFree_def.1 hG _ h
  rw [map_commutatorElement] at hφ
  exact IsFreeGroup.not_isProperPower_commutator hφ (by simpa using hp.map φ)

/-- Two commuting nontrivial commutators of a fully residually free group are equal or inverse to
each other. -/
theorem IsFullyResiduallyFree.commutator_eq_or_eq_inv_of_commute (hG : IsFullyResiduallyFree G)
    {a b c d : G} (hab : ⁅a, b⁆ ≠ 1) (hcd : ⁅c, d⁆ ≠ 1) (h : Commute ⁅a, b⁆ ⁅c, d⁆) :
    ⁅a, b⁆ = ⁅c, d⁆ ∨ ⁅a, b⁆ = ⁅c, d⁆⁻¹ := by
  classical
  by_contra! hne
  -- one homomorphism to a free group keeps both commutators, their quotient and their product
  -- nontrivial
  obtain ⟨ι, φ, hφ⟩ := isFullyResiduallyFree_def.1 hG
    {⁅a, b⁆, ⁅c, d⁆, ⁅a, b⁆ * ⁅c, d⁆⁻¹, ⁅a, b⁆ * ⁅c, d⁆} <| by
      simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
      exact ⟨hab, hcd, mul_inv_eq_one.not.2 hne.1, mul_eq_one_iff_eq_inv.not.2 hne.2⟩
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq, map_mul,
    map_inv, map_commutatorElement] at hφ
  obtain ⟨hab', hcd', h₁, h₂⟩ := hφ
  rcases IsFreeGroup.eq_or_eq_inv_of_commute (IsFreeGroup.not_isProperPower_commutator hab')
    (IsFreeGroup.not_isProperPower_commutator hcd') (by simpa using h.map φ) with he | he
  · exact h₁ (by rw [he, mul_inv_cancel])
  · exact h₂ (by rw [he, inv_mul_cancel])

end TauCeti.LimitGroup
