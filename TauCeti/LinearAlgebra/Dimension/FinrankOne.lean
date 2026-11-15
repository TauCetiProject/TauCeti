/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.Ray
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Spanning vectors and linear relations in a one-dimensional space

In a one-dimensional vector space over a division ring, a single vector spans exactly when it is
nonzero (`TauCeti.span_singleton_eq_top_iff_ne_zero_of_finrank_eq_one`), and any two vectors
satisfy a nontrivial linear relation (`TauCeti.exists_smul_add_smul_eq_zero_of_finrank_eq_one`).

Over a linearly ordered field, a one-dimensional space is a line with two open half-lines. A
predicate `P` whose members are nonzero and pairwise positive multiples of each other cannot hold
for both `x` and `-x` (`TauCeti.not_neg_of_exists_pos_smul_eq`); if it is moreover closed under
positive scaling and holds for one nonzero vector, then it holds for `x` or `-x` for every nonzero
`x` (`TauCeti.or_neg_of_finrank_eq_one`). Two functionals positive at the same vector are positive
multiples of each other (`TauCeti.exists_pos_smul_eq_of_apply_pos_of_finrank_eq_one`).

Conversely, a nontrivial space that is not one-dimensional has rank greater than `1`
(`TauCeti.one_lt_rank_of_finrank_ne_one`).
-/

public section

open Module (finrank)

namespace TauCeti

/-- In a one-dimensional vector space, a singleton spans exactly when its vector is nonzero. -/
theorem span_singleton_eq_top_iff_ne_zero_of_finrank_eq_one {K V : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] (hV : finrank K V = 1) (v : V) :
    Submodule.span K {v} = ⊤ ↔ v ≠ 0 := by
  refine ⟨?_, fun hv ↦ (finrank_eq_one_iff_of_ne_zero v hv).mp hV⟩
  rintro h rfl
  have := Module.nontrivial_of_finrank_eq_succ hV
  simp at h

/-- Any two vectors of a one-dimensional vector space satisfy a nontrivial linear relation. -/
theorem exists_smul_add_smul_eq_zero_of_finrank_eq_one {K V : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] (hV : finrank K V = 1) (x y : V) :
    ∃ a b : K, (a ≠ 0 ∨ b ≠ 0) ∧ a • x + b • y = 0 := by
  have : Module.Finite K V := Module.finite_of_finrank_eq_succ hV
  have hxy : ¬LinearIndependent K ![x, y] := fun h ↦ by
    simpa [hV] using h.fintype_card_le_finrank
  simp only [LinearIndependent.pair_iff, not_forall, not_and_or] at hxy
  obtain ⟨a, b, h, hab⟩ := hxy
  exact ⟨a, b, hab, h⟩

section HalfLine

variable {K M : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [AddCommGroup M]
  [Module K M] {P : M → Prop}

/-- If a predicate `P` holds only for nonzero vectors, and any two vectors satisfying it differ by a
positive factor, then `P x` and `P (-x)` do not both hold. -/
theorem not_neg_of_exists_pos_smul_eq (hne : ∀ x, P x → x ≠ 0)
    (hpos : ∀ x y, P x → P y → ∃ c : K, 0 < c ∧ y = c • x) {x : M} (hx : P x) : ¬ P (-x) :=
  fun hnx ↦ by
    obtain ⟨c, hc, h⟩ := hpos x (-x) hx hnx
    exact hne x hx
      (eq_zero_of_sameRay_self_neg (R := K) (h ▸ SameRay.sameRay_nonneg_smul_right x hc.le))

/-- In a one-dimensional space over a linearly ordered field, if a predicate `P` is closed under
positive scaling and holds for some nonzero vector, then for every nonzero `x`, `P x` or `P (-x)`
holds. -/
theorem or_neg_of_finrank_eq_one (hM : finrank K M = 1)
    (hsmul : ∀ x, P x → ∀ c : K, 0 < c → P (c • x)) {x₀ : M} (hx₀ : P x₀) (h₀ : x₀ ≠ 0) {x : M}
    (hx : x ≠ 0) : P x ∨ P (-x) := by
  have : Module.Finite K M := Module.finite_of_finrank_eq_succ hM
  -- Two vectors of a line are linearly dependent.
  have hdep : ¬ LinearIndependent K ![x₀, x] := fun h ↦ by
    simpa [hM] using h.fintype_card_le_finrank
  rcases sameRay_or_sameRay_neg_iff_not_linearIndependent.2 hdep with h | h
  · obtain ⟨c, hc, rfl⟩ := h.exists_pos_left h₀ hx
    exact Or.inl (hsmul x₀ hx₀ c hc)
  · obtain ⟨c, hc, h⟩ := h.exists_pos_left h₀ (neg_ne_zero.2 hx)
    exact Or.inr (h ▸ hsmul x₀ hx₀ c hc)

/-- On a one-dimensional space over a linearly ordered field, two functionals that are positive at
the same vector differ by a positive factor. -/
theorem exists_pos_smul_eq_of_apply_pos_of_finrank_eq_one (hM : finrank K M = 1)
    {φ ψ : Module.Dual K M} {x : M} (hφ : 0 < φ x) (hψ : 0 < ψ x) :
    ∃ c : K, 0 < c ∧ ψ = c • φ := by
  have hx : x ≠ 0 := fun h ↦ by simp [h] at hφ
  refine ⟨ψ x / φ x, div_pos hψ hφ, LinearMap.ext fun y ↦ ?_⟩
  obtain ⟨t, rfl⟩ := (finrank_eq_one_iff_of_ne_zero' x hx).1 hM y
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  field_simp

end HalfLine

/-- A nontrivial module whose dimension is not `1` has rank greater than `1`. Infinite-dimensional
modules have rank at least `ℵ₀`, and a finite-dimensional nontrivial one has `finrank ≥ 1`, hence
`finrank > 1`. -/
theorem one_lt_rank_of_finrank_ne_one {K V : Type*} [DivisionRing K] [AddCommGroup V]
    [Module K V] [Nontrivial V] (h : finrank K V ≠ 1) : 1 < Module.rank K V := by
  by_cases hfin : Module.Finite K V
  · have := Module.finrank_pos (R := K) (M := V)
    exact Module.one_lt_rank_of_one_lt_finrank (by omega)
  · exact Cardinal.one_lt_aleph0.trans_le (not_lt.1 (mt Module.rank_lt_aleph0_iff.1 hfin))

end TauCeti
