/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Int.Units
public import Mathlib.GroupTheory.Index

import Mathlib.Algebra.Order.SuccPred
import Mathlib.Data.Nat.Prime.Basic

/-!
# The sign indicator of a subgroup

For a subgroup `H` of a group `G`, its sign indicator is the function which is `1` on `H` and
`-1` off `H`.  This function is multiplicative exactly when the index of `H` divides two.  For a
finite quotient, this is the familiar criterion that the index is at most two.

The divisibility formulation is the unrestricted one because Mathlib defines the index of an
infinite-index subgroup to be zero.  It therefore excludes infinite index without an additional
finiteness assumption, while the numerical bound `H.index ≤ 2` does not.

This elementary character packages the last group-theoretic step in arguments where a subgroup
is proved to have index two.  In particular, it turns a norm subgroup of index two into the
sign-valued character used to prove bimultiplicativity of the Hilbert symbol.

## Main declarations

* `Subgroup.signIndicator`: the function equal to `1` on a subgroup and `-1` off it.
* `Subgroup.signIndicator_mul_iff_index_dvd_two`: the unrestricted multiplicativity
  criterion.
* `Subgroup.signIndicator_mul_iff_index_le_two`: the finite-index form of the criterion.
* `Subgroup.signIndicatorHom`: the resulting homomorphism when the index divides two.
-/

public section

namespace TauCeti

variable {G : Type*} [Group G]

open scoped Classical in
/-- The sign indicator of a subgroup: it is `1` on the subgroup and `-1` off it. -/
noncomputable def _root_.Subgroup.signIndicator (H : Subgroup G) (x : G) : ℤˣ :=
  if x ∈ H then 1 else -1

/-- The sign indicator is `1` on its subgroup. -/
@[simp]
theorem _root_.Subgroup.signIndicator_of_mem (H : Subgroup G) {x : G} (hx : x ∈ H) :
    H.signIndicator x = 1 := by
  simp [Subgroup.signIndicator, hx]

/-- The sign indicator is `-1` outside its subgroup. -/
@[simp]
theorem _root_.Subgroup.signIndicator_of_notMem (H : Subgroup G) {x : G} (hx : x ∉ H) :
    H.signIndicator x = -1 := by
  simp [Subgroup.signIndicator, hx]

/-- The sign indicator detects membership by taking the value `1`. -/
@[simp]
theorem _root_.Subgroup.signIndicator_eq_one_iff (H : Subgroup G) {x : G} :
    H.signIndicator x = 1 ↔ x ∈ H := by
  by_cases hx : x ∈ H
  · simp [hx]
  · simp only [H.signIndicator_of_notMem hx, hx, iff_false]
    exact Int.units_ne_iff_eq_neg.mpr rfl

/-- The sign indicator detects nonmembership by taking the value `-1`. -/
@[simp]
theorem _root_.Subgroup.signIndicator_eq_neg_one_iff (H : Subgroup G) {x : G} :
    H.signIndicator x = -1 ↔ x ∉ H := by
  by_cases hx : x ∈ H
  · simp only [H.signIndicator_of_mem hx, hx, not_true_eq_false, iff_false]
    exact Int.units_ne_iff_eq_neg.mpr (by simp)
  · simp [hx]

/-- **The sign indicator is multiplicative exactly when the subgroup index divides two.**

This is the version without a finiteness assumption.  The divisibility condition is essential:
Mathlib records an infinite index as zero, which satisfies `H.index ≤ 2` but does not divide
two. -/
theorem _root_.Subgroup.signIndicator_mul_iff_index_dvd_two (H : Subgroup G) :
    (∀ x y : G, H.signIndicator (x * y) = H.signIndicator x * H.signIndicator y) ↔
      H.index ∣ 2 := by
  constructor
  · intro hmul
    rw [Subgroup.index_dvd_two_iff]
    by_cases htop : H = ⊤
    · subst H
      exact ⟨1, by simp⟩
    · obtain ⟨a, -, ha⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr htop)
      refine ⟨a, fun b ↦ ?_⟩
      by_cases hb : b ∈ H
      · exact Or.inr hb
      · left
        by_contra hba
        have h := hmul b a
        rw [H.signIndicator_of_notMem hba, H.signIndicator_of_notMem hb,
          H.signIndicator_of_notMem ha] at h
        have hbad : (-1 : ℤˣ) = 1 := by
          simpa only [neg_mul, one_mul, neg_neg] using h
        exact Int.units_ne_iff_eq_neg.mpr rfl hbad
  · intro hindex
    rcases (Nat.dvd_prime Nat.prime_two).mp hindex with hindex | hindex
    · have htop := Subgroup.index_eq_one.mp hindex
      subst H
      simp [Subgroup.signIndicator]
    · intro x y
      by_cases hx : x ∈ H <;> by_cases hy : y ∈ H <;>
        simp [Subgroup.signIndicator, hx, hy, H.mul_mem_iff_of_index_two hindex]

/-- For a subgroup with finite quotient, the sign indicator is multiplicative exactly when the
subgroup has index at most two. -/
theorem _root_.Subgroup.signIndicator_mul_iff_index_le_two (H : Subgroup G) [H.FiniteIndex] :
    (∀ x y : G, H.signIndicator (x * y) = H.signIndicator x * H.signIndicator y) ↔
      H.index ≤ 2 := by
  rw [H.signIndicator_mul_iff_index_dvd_two]
  constructor
  · exact fun h ↦ Nat.le_of_dvd (by decide) h
  · intro hle
    have hne : H.index ≠ 0 := H.index_ne_zero_of_finite
    rcases Order.le_two_iff.mp hle with hindex | hindex | hindex
    · exact (hne hindex).elim
    · simp [hindex]
    · simp [hindex]

/-- The sign indicator, bundled as a homomorphism when the subgroup index divides two. -/
@[expose] noncomputable def _root_.Subgroup.signIndicatorHom (H : Subgroup G)
    (hindex : H.index ∣ 2) :
    G →* ℤˣ where
  toFun := H.signIndicator
  map_one' := H.signIndicator_of_mem H.one_mem
  map_mul' := H.signIndicator_mul_iff_index_dvd_two.mpr hindex

/-- The bundled sign-indicator homomorphism evaluates to the underlying sign indicator. -/
@[simp]
theorem _root_.Subgroup.signIndicatorHom_apply (H : Subgroup G) (hindex : H.index ∣ 2)
    (x : G) :
    H.signIndicatorHom hindex x = H.signIndicator x :=
  rfl

/-- The kernel of the sign-indicator homomorphism is the original subgroup. -/
@[simp]
theorem _root_.Subgroup.ker_signIndicatorHom (H : Subgroup G) (hindex : H.index ∣ 2) :
    (H.signIndicatorHom hindex).ker = H := by
  ext x
  simp

/-- The sign-indicator homomorphism is onto precisely when the subgroup is proper. -/
theorem _root_.Subgroup.signIndicatorHom_surjective_iff (H : Subgroup G)
    (hindex : H.index ∣ 2) :
    Function.Surjective (H.signIndicatorHom hindex) ↔ H ≠ ⊤ := by
  constructor
  · intro hsurj htop
    obtain ⟨x, hx⟩ := hsurj (-1)
    subst H
    have hxone : (⊤ : Subgroup G).signIndicatorHom hindex x = 1 := by simp
    exact Int.units_ne_iff_eq_neg.mpr (by simp) (hxone.symm.trans hx)
  · intro htop u
    obtain ⟨a, -, ha⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr htop)
    rcases Int.units_eq_one_or u with rfl | rfl
    · exact ⟨1, by simp⟩
    · exact ⟨a, by simp [ha]⟩

/-- The sign-indicator homomorphism is onto precisely for a subgroup of index two. -/
theorem _root_.Subgroup.signIndicatorHom_surjective_iff_index_eq_two (H : Subgroup G)
    (hindex : H.index ∣ 2) :
    Function.Surjective (H.signIndicatorHom hindex) ↔ H.index = 2 := by
  rw [H.signIndicatorHom_surjective_iff hindex]
  rcases (Nat.dvd_prime Nat.prime_two).mp hindex with hindex | hindex
  · have htop := Subgroup.index_eq_one.mp hindex
    subst H
    simp
  · simp only [hindex, iff_true]
    intro htop
    subst H
    simp at hindex

end TauCeti
