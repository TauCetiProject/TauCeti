/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import TauCeti.Order.Lattice.Submodular

import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Pi
import TauCeti.Data.Finset.Basic

/-!
# Unanimity games and Harsanyi dividends

The unanimity function of a coalition is the indicator of the coalitions that contain it, given
by the corresponding row of Mathlib's `IncidenceAlgebra.zeta`.
Harsanyi dividends are the signed Möbius transform of a set function on the subset lattice.
A set function is recovered by summing the dividends of subcoalitions. On a finite player type,
this gives the coordinates in the unanimity basis. The nonempty coalitions index the
corresponding basis of the submodule of functions vanishing at the empty coalition.

Nonnegative dividends on coalitions of size at least two imply supermodularity. The empty
coalition contributes a constant and the singletons contribute an additive function, so their
dividends may have either sign.

## References

* L. S. Shapley, *A value for n-person games*, RAND P-295, Lemma 3 and formulas (7)–(8).
-/

public section

namespace Finset

variable {ι : Type*}

/-- The unanimity function of `S` pays one to a coalition containing `S` and zero otherwise. -/
def unanimity [DecidableEq ι] (S : Finset ι) : Finset ι → ℝ := IncidenceAlgebra.zeta ℝ S

/-- The value of a unanimity function is determined by coalition inclusion. -/
theorem unanimity_apply [DecidableEq ι] (S T : Finset ι) :
    unanimity S T = if S ⊆ T then 1 else 0 := IncidenceAlgebra.zeta_apply S T

/-- A coalition containing the required players has unanimity worth one. -/
@[simp]
theorem unanimity_apply_of_subset [DecidableEq ι] {S T : Finset ι} (h : S ⊆ T) :
    unanimity S T = 1 := by rw [unanimity_apply, ite_eq_left h]

/-- A coalition missing a required player has unanimity worth zero. -/
@[simp]
theorem unanimity_apply_of_not_subset [DecidableEq ι] {S T : Finset ι} (h : ¬ S ⊆ T) :
    unanimity S T = 0 := by rw [unanimity_apply, ite_eq_right h]

/-- The unanimity function takes only the values zero and one. -/
theorem unanimity_eq_zero_or_eq_one [DecidableEq ι] (S T : Finset ι) :
    unanimity S T = 0 ∨ unanimity S T = 1 := by
  rw [unanimity_apply]
  split_ifs <;> simp

/-- The unanimity function of the empty coalition is constant one. -/
@[simp]
theorem unanimity_empty [DecidableEq ι] : unanimity (∅ : Finset ι) = 1 := by
  ext T
  exact unanimity_apply_of_subset (empty_subset T)

/-- A unanimity function vanishes at the empty coalition exactly when its required coalition
is nonempty. -/
@[simp]
theorem unanimity_apply_empty_eq_zero_iff [DecidableEq ι] (S : Finset ι) :
    unanimity S ∅ = 0 ↔ S.Nonempty := by
  by_cases h : S = ∅
  · subst S
    simp
  · rw [unanimity_apply_of_not_subset (fun hs ↦ h (subset_empty.mp hs))]
    simp [ne_empty_iff_nonempty.mp h]

/-- A unanimity function is monotone under coalition inclusion. -/
theorem monotone_unanimity [DecidableEq ι] (S : Finset ι) : Monotone (unanimity S) := by
  intro A B hAB
  by_cases hA : S ⊆ A
  · simp [hA, hA.trans hAB]
  · rw [unanimity_apply_of_not_subset hA]
    obtain h | h := unanimity_eq_zero_or_eq_one S B <;> simp [h]

/-- Every unanimity function is supermodular. -/
theorem isSubmodular_neg_unanimity [DecidableEq ι] (S : Finset ι) :
    TauCeti.IsSubmodular (-unanimity S) := by
  rw [TauCeti.isSubmodular_def]
  intro A B
  simp only [Pi.neg_apply, ← neg_add, neg_le_neg_iff]
  by_cases hA : S ⊆ A <;> by_cases hB : S ⊆ B
  · simp [hA, hB, hA.trans subset_union_left, subset_inter]
  · simp [hA, hB, hA.trans subset_union_left]
  · simp [hA, hB, hB.trans subset_union_right]
  · simp [hA, hB, unanimity_apply]
    split_ifs <;> norm_num

end Finset

open Finset

namespace TauCeti

variable {ι : Type*}

/-- The Harsanyi dividend of a coalition is the alternating sum of the worths of its
subcoalitions, with sign determined by the number of omitted players. -/
noncomputable def dividend (v : Finset ι → ℝ) (S : Finset ι) : ℝ :=
  ∑ R ∈ S.powerset, (-1 : ℝ) ^ (S.card - R.card) * v R

/-- The signed subset formula for the Harsanyi dividend. -/
theorem dividend_apply (v : Finset ι → ℝ) (S : Finset ι) :
    dividend v S = ∑ R ∈ S.powerset, (-1 : ℝ) ^ (S.card - R.card) * v R := (rfl)

/-- The dividend at the empty coalition is its worth. -/
@[simp]
theorem dividend_empty (v : Finset ι → ℝ) : dividend v ∅ = v ∅ := by
  simp [dividend_apply]

/-- The worth of a coalition is the sum of the dividends of its subcoalitions. -/
theorem sum_powerset_dividend (v : Finset ι → ℝ) (T : Finset ι) :
    ∑ S ∈ T.powerset, dividend v S = v T := by
  classical
  simp only [dividend_apply]
  rw [sum_comm' (t' := T.powerset) (s' := fun R ↦ Icc R T) fun S R ↦ by
    simp only [mem_powerset, mem_Icc]
    exact ⟨fun ⟨hST, hRS⟩ ↦ ⟨⟨hRS, hST⟩, hRS.trans hST⟩,
      fun h ↦ ⟨h.1.2, h.1.1⟩⟩]
  simp [← sum_mul]

/-- The map sending a set function to its family of Harsanyi dividends is linear. -/
noncomputable def dividendLinearMap : (Finset ι → ℝ) →ₗ[ℝ] (Finset ι → ℝ) where
  toFun := dividend
  map_add' v w := by
    ext S
    simp [dividend_apply, mul_add, sum_add_distrib]
  map_smul' c v := by
    ext S
    simp [dividend_apply, Pi.smul_apply, smul_eq_mul, mul_sum, mul_left_comm]

/-- Evaluating the dividend linear map gives the dividend function. -/
@[simp]
theorem dividendLinearMap_apply (v : Finset ι → ℝ) : dividendLinearMap v = dividend v :=
  (rfl)

/-- A unanimity function has a single unit dividend, at its required coalition. -/
@[simp]
theorem _root_.Finset.dividend_unanimity [DecidableEq ι] (S T : Finset ι) :
    dividend (unanimity S) T = if S = T then 1 else 0 := by
  rw [dividend_apply, ← sum_Icc_neg_one_pow_card_sub_card_right (R := ℝ) S T,
    Icc_eq_filter_powerset, sum_filter]
  simp only [unanimity_apply, mul_ite, mul_one, mul_zero]

/-- An additive set function has the player's worth at each singleton dividend and has zero
dividend on every other coalition. -/
theorem dividend_sum (a : ι → ℝ) (T : Finset ι) :
    dividend (fun S ↦ ∑ i ∈ S, a i) T = if T.card = 1 then ∑ i ∈ T, a i else 0 := by
  classical
  simp only [dividend_apply, mul_sum]
  rw [sum_comm' (t' := T) (s' := fun i ↦ Icc {i} T) fun S i ↦ by
    simp only [mem_powerset, mem_Icc, singleton_subset_iff]
    exact ⟨fun ⟨hST, hiS⟩ ↦ ⟨⟨hiS, hST⟩, hST hiS⟩, fun h ↦ ⟨h.1.2, h.1.1⟩⟩]
  simp_rw [← sum_mul, sum_Icc_neg_one_pow_card_sub_card_right]
  by_cases h : T.card = 1
  · obtain ⟨i, rfl⟩ := card_eq_one.mp h
    simp
  · rw [ite_eq_right h]
    refine sum_eq_zero fun i _ ↦ ?_
    have hi : ({i} : Finset ι) ≠ T := fun heq ↦ h (by simp [← heq])
    simp [hi]

/-- The singleton dividend of an additive set function is the corresponding player's worth. -/
@[simp]
theorem dividend_sum_singleton (a : ι → ℝ) (i : ι) :
    dividend (fun S ↦ ∑ j ∈ S, a j) {i} = a i := by
  simp [dividend_sum]

section DecidableEq

variable [DecidableEq ι]

private theorem sum_smul_unanimity_apply
    {A : Finset (Finset ι)} {T : Finset ι} (hT : T.powerset ⊆ A)
    (d : Finset ι → ℝ) :
    (∑ S ∈ A, d S • unanimity S) T = ∑ S ∈ T.powerset, d S := by
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, unanimity_apply, mul_ite, mul_one,
    mul_zero]
  rw [← sum_filter]
  congr 1
  ext S
  simp only [mem_powerset, mem_filter]
  exact ⟨And.right, fun h ↦ ⟨hT (mem_powerset.mpr h), h⟩⟩

private theorem unanimity_add_eq_of_card_le_one {S : Finset ι} (hS : S.card ≤ 1)
    (A B : Finset ι) :
    unanimity S A + unanimity S B = unanimity S (A ∪ B) + unanimity S (A ∩ B) := by
  by_cases h : S = ∅
  · simp [h]
  have hcard : S.card = 1 := by
    have := card_pos.mpr (ne_empty_iff_nonempty.mp h)
    omega
  obtain ⟨i, rfl⟩ := card_eq_one.mp hcard
  simp only [unanimity_apply, singleton_subset_iff, mem_union, mem_inter]
  by_cases hA : i ∈ A <;> by_cases hB : i ∈ B <;> simp [hA, hB]

/-- A set function with nonnegative dividends on all coalitions of size at least two is
supermodular. -/
theorem isSubmodular_neg_of_dividend_nonneg {v : Finset ι → ℝ}
    (h : ∀ S : Finset ι, 2 ≤ S.card → 0 ≤ dividend v S) : IsSubmodular (-v) := by
  rw [isSubmodular_def]
  intro A B
  simp only [Pi.neg_apply, ← neg_add, neg_le_neg_iff]
  -- Expand all four values using the same family, indexed by subsets of the union.
  have hexpand (T : Finset ι) (hT : T ⊆ A ∪ B) :
      (∑ S ∈ (A ∪ B).powerset, dividend v S • unanimity S) T = v T :=
    (sum_smul_unanimity_apply (powerset_mono.mpr hT) _).trans (sum_powerset_dividend v T)
  rw [← hexpand A subset_union_left, ← hexpand B subset_union_right,
    ← hexpand (A ∪ B) Subset.rfl,
    ← hexpand (A ∩ B) (inter_subset_left.trans subset_union_left)]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ← sum_add_distrib, ← mul_add]
  refine sum_le_sum fun S _ ↦ ?_
  by_cases hS : 2 ≤ S.card
  · apply mul_le_mul_of_nonneg_left _ (h S hS)
    simpa only [Pi.neg_apply, ← neg_add, neg_le_neg_iff] using
      (isSubmodular_neg_unanimity S).apply A B
  · rw [unanimity_add_eq_of_card_le_one (by omega) A B]

section FinitePlayers

variable [Fintype ι]

/-- An expansion in unanimity functions exists with exactly the dividend coefficients. -/
theorem eq_sum_smul_unanimity_iff (v d : Finset ι → ℝ) :
    v = ∑ S : Finset ι, d S • unanimity S ↔ d = dividend v := by
  constructor
  · intro hv
    symm
    rw [← dividendLinearMap_apply, hv, map_sum]
    ext T
    simp [Pi.smul_apply, smul_eq_mul, mul_ite]
  · rintro rfl
    ext T
    rw [sum_smul_unanimity_apply (subset_univ _), sum_powerset_dividend]

end FinitePlayers

end DecidableEq

private noncomputable def dividendEquiv [Finite ι] :
    (Finset ι → ℝ) ≃ₗ[ℝ] (Finset ι → ℝ) :=
  LinearEquiv.ofBijective dividendLinearMap <| by
    classical
    let := Fintype.ofFinite ι
    constructor
    · intro v w h
      simp only [dividendLinearMap_apply] at h
      ext T
      rw [← sum_powerset_dividend v T, ← sum_powerset_dividend w T, h]
    · intro d
      refine ⟨∑ S : Finset ι, d S • unanimity S, ?_⟩
      rw [dividendLinearMap_apply]
      exact ((eq_sum_smul_unanimity_iff _ _).mp rfl).symm

private theorem dividendEquiv_apply [Finite ι] (v : Finset ι → ℝ) :
    dividendEquiv v = dividend v :=
  (LinearEquiv.ofBijective_apply dividendLinearMap v).trans (dividendLinearMap_apply v)

section FinitePlayers

variable [Finite ι]

/-- The basis of real coalition set functions whose vectors are the unanimity functions. -/
noncomputable def unanimityBasis : Module.Basis (Finset ι) ℝ (Finset ι → ℝ) :=
  letI := Fintype.ofFinite ι
  Module.Basis.ofEquivFun dividendEquiv

/-- The coordinates of a set function in the unanimity basis are its Harsanyi dividends. -/
@[simp]
theorem unanimityBasis_repr (v : Finset ι → ℝ) (S : Finset ι) :
    unanimityBasis.repr v S = dividend v S := by
  let := Fintype.ofFinite ι
  rw [unanimityBasis, Module.Basis.ofEquivFun_repr_apply, dividendEquiv_apply]

/-- The basis vector indexed by a coalition is its unanimity function. -/
@[simp]
theorem _root_.Finset.unanimityBasis_apply [DecidableEq ι] (S : Finset ι) :
    unanimityBasis S = unanimity S := by
  apply unanimityBasis.repr.injective
  ext T
  rw [Module.Basis.repr_self_apply, unanimityBasis_repr, dividend_unanimity]

end FinitePlayers

/-- The submodule of games normalized to have zero worth at the empty coalition. -/
def normalizedGameSubmodule (ι : Type*) : Submodule ℝ (Finset ι → ℝ) :=
  LinearMap.ker (LinearMap.proj ∅)

/-- Normalization of a game is vanishing at the empty coalition. -/
@[simp]
theorem mem_normalizedGameSubmodule (v : Finset ι → ℝ) :
    v ∈ normalizedGameSubmodule ι ↔ v ∅ = 0 := by
  rw [normalizedGameSubmodule, LinearMap.mem_ker, LinearMap.proj_apply]

section FinitePlayers

variable [Finite ι]

private noncomputable def normalizedDividendEquiv :
    normalizedGameSubmodule ι ≃ₗ[ℝ] ({S : Finset ι // S.Nonempty} → ℝ) := by
  classical
  let omitEmpty := LinearMap.iInfKerProjEquiv ℝ (fun _ : Finset ι ↦ ℝ)
    (I := {S | S.Nonempty}) (J := {∅})
    (by simp [Set.disjoint_singleton_right]) (by
      intro S _
      exact (eq_empty_or_nonempty S).elim Or.inr Or.inl)
  let K := ⨅ S ∈ ({∅} : Set (Finset ι)), LinearMap.ker
    (LinearMap.proj S : (Finset ι → ℝ) →ₗ[ℝ] ℝ)
  have h : normalizedGameSubmodule ι = K.comap dividendEquiv.toLinearMap := by
    apply Submodule.ext
    intro v
    simp [K, Submodule.mem_comap, LinearMap.mem_ker, dividendEquiv_apply]
  exact (LinearEquiv.ofEq _ _ h).trans ((dividendEquiv.ofSubmodule' K).trans omitEmpty)

private theorem normalizedDividendEquiv_apply (v : normalizedGameSubmodule ι)
    (S : {S : Finset ι // S.Nonempty}) :
    normalizedDividendEquiv v S = dividend v.val S.val := by
  simp only [normalizedDividendEquiv, LinearEquiv.trans_apply, LinearMap.iInfKerProjEquiv,
    LinearEquiv.coe_ofLinearMap, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    Submodule.subtype_apply, LinearEquiv.ofSubmodule'_apply, LinearEquiv.coe_ofEq_apply,
    dividendEquiv_apply]

/-- The unanimity basis of normalized games, indexed by nonempty coalitions. -/
noncomputable def normalizedUnanimityBasis :
    Module.Basis {S : Finset ι // S.Nonempty} ℝ (normalizedGameSubmodule ι) :=
  letI := Fintype.ofFinite ι
  Module.Basis.ofEquivFun normalizedDividendEquiv

/-- The normalized unanimity basis has the same dividend coordinates on nonempty coalitions. -/
@[simp]
theorem normalizedUnanimityBasis_repr (v : normalizedGameSubmodule ι)
    (S : {S : Finset ι // S.Nonempty}) :
    normalizedUnanimityBasis.repr v S = dividend v.val S.val := by
  let := Fintype.ofFinite ι
  rw [normalizedUnanimityBasis, Module.Basis.ofEquivFun_repr_apply, normalizedDividendEquiv_apply]

/-- The normalized basis vector of a nonempty coalition is its unanimity function. -/
@[simp]
theorem normalizedUnanimityBasis_apply [DecidableEq ι] (S : {S : Finset ι // S.Nonempty}) :
    (normalizedUnanimityBasis S).val = unanimity S.val := by
  let u : normalizedGameSubmodule ι :=
    ⟨unanimity S.val, (mem_normalizedGameSubmodule _).mpr
      ((unanimity_apply_empty_eq_zero_iff _).mpr S.property)⟩
  suffices h : normalizedUnanimityBasis S = u from congrArg Subtype.val h
  apply normalizedUnanimityBasis.repr.injective
  ext T
  classical
  rw [Module.Basis.repr_self_apply, normalizedUnanimityBasis_repr]
  simp only [u, dividend_unanimity, Subtype.val_inj]

end FinitePlayers

section FintypePlayers

variable [Fintype ι]

/-- The dimension of the space of real coalition set functions is the number of coalitions. -/
theorem finrank_setFunctions :
    Module.finrank ℝ (Finset ι → ℝ) = 2 ^ Fintype.card ι := by
  rw [Module.finrank_eq_card_basis (unanimityBasis (ι := ι)), Fintype.card_finset]

/-- The normalized game space has one dimension for each nonempty coalition. -/
theorem finrank_normalizedGameSubmodule :
    Module.finrank ℝ (normalizedGameSubmodule ι) = 2 ^ Fintype.card ι - 1 := by
  rw [Module.finrank_eq_nat_card_basis (normalizedUnanimityBasis (ι := ι)), card_nonempty_finset,
    Nat.card_eq_fintype_card]

end FintypePlayers

end TauCeti
