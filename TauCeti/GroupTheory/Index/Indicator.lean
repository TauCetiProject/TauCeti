/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Int.Units
public import Mathlib.GroupTheory.Index

import Mathlib.Algebra.GroupWithZero.Units.Fintype
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

## References

* Mathlib's `Subgroup.mul_mem_iff_of_index_two` and `Subgroup.index_ker` provide the two
  directions of the multiplicativity criterion.
-/

public section

namespace Subgroup

variable {G : Type*} [Group G]

open scoped Classical in
/-- The sign indicator of a subgroup: it is `1` on the subgroup and `-1` off it. -/
noncomputable def signIndicator (H : Subgroup G) (x : G) : ℤˣ :=
  (H : Set G)ᶜ.mulIndicator (fun _ ↦ (-1 : ℤˣ)) x

/-- The sign indicator is `1` on its subgroup. -/
@[simp]
theorem signIndicator_of_mem (H : Subgroup G) {x : G} (hx : x ∈ H) :
    H.signIndicator x = 1 := by
  simp [signIndicator, hx]

/-- The sign indicator is `-1` outside its subgroup. -/
@[simp]
theorem signIndicator_of_notMem (H : Subgroup G) {x : G} (hx : x ∉ H) :
    H.signIndicator x = -1 := by
  simp [signIndicator, hx]

/-- The sign indicator detects membership by taking the value `1`. -/
@[simp]
theorem signIndicator_eq_one_iff (H : Subgroup G) {x : G} :
    H.signIndicator x = 1 ↔ x ∈ H := by
  by_cases hx : x ∈ H <;> simp [hx, Units.ext_iff]

/-- The sign indicator detects nonmembership by taking the value `-1`. -/
@[simp]
theorem signIndicator_eq_neg_one_iff (H : Subgroup G) {x : G} :
    H.signIndicator x = -1 ↔ x ∉ H := by
  by_cases hx : x ∈ H <;> simp [hx, Units.ext_iff]

/-- **The sign indicator is multiplicative exactly when the subgroup index divides two.**

This is the version without a finiteness assumption.  The divisibility condition is essential:
Mathlib records an infinite index as zero, which satisfies `H.index ≤ 2` but does not divide
two. -/
theorem signIndicator_mul_iff_index_dvd_two (H : Subgroup G) :
    (∀ x y : G, H.signIndicator (x * y) = H.signIndicator x * H.signIndicator y) ↔
      H.index ∣ 2 := by
  refine ⟨fun hmul ↦ ?_, fun hindex x y ↦ ?_⟩
  · -- A multiplicative sign indicator is a homomorphism with kernel `H`, so the index of `H`
    -- is the order of a subgroup of `ℤˣ`.
    let f : G →* ℤˣ := MonoidHom.mk' H.signIndicator hmul
    have hker : f.ker = H := by ext; simp [f]
    rw [← hker, index_ker f, ← Fintype.card_units_int, ← Nat.card_eq_fintype_card]
    exact card_subgroup_dvd_card f.range
  · rcases (Nat.dvd_prime Nat.prime_two).mp hindex with hindex | hindex
    · obtain rfl := index_eq_one.mp hindex
      simp
    · by_cases hx : x ∈ H <;> by_cases hy : y ∈ H <;>
        simp [hx, hy, H.mul_mem_iff_of_index_two hindex]

/-- For a subgroup with finite quotient, the sign indicator is multiplicative exactly when the
subgroup has index at most two. -/
theorem signIndicator_mul_iff_index_le_two (H : Subgroup G) [H.FiniteIndex] :
    (∀ x y : G, H.signIndicator (x * y) = H.signIndicator x * H.signIndicator y) ↔
      H.index ≤ 2 := by
  rw [H.signIndicator_mul_iff_index_dvd_two, Nat.dvd_prime Nat.prime_two]
  have := H.index_ne_zero_of_finite
  omega

/-- The sign indicator, bundled as a homomorphism when the subgroup index divides two. -/
noncomputable def signIndicatorHom (H : Subgroup G)
    (hindex : H.index ∣ 2) :
    G →* ℤˣ where
  toFun := H.signIndicator
  map_one' := H.signIndicator_of_mem H.one_mem
  map_mul' := H.signIndicator_mul_iff_index_dvd_two.mpr hindex

/-- The bundled sign-indicator homomorphism evaluates to the underlying sign indicator. -/
@[simp]
theorem signIndicatorHom_apply (H : Subgroup G) (hindex : H.index ∣ 2)
    (x : G) :
    H.signIndicatorHom hindex x = H.signIndicator x := by
  simp [signIndicatorHom]

/-- The kernel of the sign-indicator homomorphism is the original subgroup. -/
@[simp]
theorem ker_signIndicatorHom (H : Subgroup G) (hindex : H.index ∣ 2) :
    (H.signIndicatorHom hindex).ker = H := by
  ext x
  simp

/-- The sign-indicator homomorphism is onto precisely when the subgroup is proper. -/
theorem signIndicatorHom_surjective_iff (H : Subgroup G)
    (hindex : H.index ∣ 2) :
    Function.Surjective (H.signIndicatorHom hindex) ↔ H ≠ ⊤ := by
  refine ⟨fun hsurj htop ↦ ?_, fun htop u ↦ ?_⟩
  · obtain ⟨x, hx⟩ := hsurj (-1)
    simp [htop, Units.ext_iff] at hx
  · obtain ⟨a, -, ha⟩ := IsConcreteLE.exists_of_lt (lt_top_iff_ne_top.mpr htop)
    rcases Int.units_eq_one_or u with rfl | rfl
    · exact ⟨1, by simp⟩
    · exact ⟨a, by simp [ha]⟩

/-- The sign-indicator homomorphism is onto precisely for a subgroup of index two. -/
theorem signIndicatorHom_surjective_iff_index_eq_two (H : Subgroup G)
    (hindex : H.index ∣ 2) :
    Function.Surjective (H.signIndicatorHom hindex) ↔ H.index = 2 := by
  rw [H.signIndicatorHom_surjective_iff hindex, Ne, ← index_eq_one]
  rcases (Nat.dvd_prime Nat.prime_two).mp hindex with hindex | hindex <;> simp [hindex]

end Subgroup
