/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Finite.CanonicalBilinear
public import TauCeti.LinearAlgebra.RootSystem.HighestRoot
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Vector

/-!
# The dual Coxeter number

Let `b` be a base of a finite, reduced, irreducible, crystallographic root system `P`, with highest
root `θ` (`RootPairing.Base.highestRoot`). Expanding the coroot `θ^∨` in the simple coroots,
`θ^∨ = ∑ aᵢ^∨ αᵢ^∨`, the **dual Coxeter number** is

`h^∨ = 1 + ∑ aᵢ^∨ = 1 + ht(θ^∨)`

(`RootPairing.Base.dualCoxeterNumber`). Since the Weyl vector `ρ` pairs to `1` with every simple
coroot, this is also `h^∨ = 1 + ⟨ρ, θ^∨⟩`
(`RootPairing.Base.coroot'_highestRoot_weylVector`).

The main result computes the length of `θ^∨` for Mathlib's canonical form on the coweight space,
`P.CorootForm x y = ∑_α ⟨α, x⟩ ⟨α, y⟩`:

`P.CorootForm θ^∨ θ^∨ = ∑_α ⟨α, θ^∨⟩² = 4 h^∨`

(`RootPairing.Base.corootForm_coroot_highestRoot`). For the root system of a semisimple Lie
algebra in characteristic zero, the coweight space is a Cartan subalgebra and `P.CorootForm` is the
restriction of the Killing form to it, since every root space is one-dimensional. The identity is
then the computation behind `Killing = 2 h^∨ κ₀`, where `κ₀` is the invariant form with
`κ₀(θ^∨, θ^∨) = 2`: the normalisation in which long roots have squared length `2` for the dual
form. That comparison with the Killing form is not made in this file.

The proof is the classical one. The highest root is long
(`RootPairing.Base.rootLength_le_rootLength_highestRoot`), so `⟨α, θ^∨⟩ ∈ {-1, 0, 1}` for every
root `α ≠ ±θ` (`RootPairing.Base.pairingIn_highestRoot_right_mem`). It is also the root of
greatest height, so `⟨α, θ^∨⟩ ≥ 0` for every positive root `α`: otherwise `α + θ` would be a
higher root (`RootPairing.Base.pairingIn_highestRoot_right_nonneg`). Hence
`⟨α, θ^∨⟩² = ⟨α, θ^∨⟩` for the positive roots `α ≠ θ`, while `⟨θ, θ^∨⟩² = 4`, and summing over the
positive roots gives `2 + ⟨2ρ, θ^∨⟩`. The negative roots contribute the same amount, and
`⟨2ρ, θ^∨⟩ = 2 ht(θ^∨) = 2 (h^∨ - 1)`.

## Main definitions

* `RootPairing.Base.dualCoxeterNumber`: the dual Coxeter number `h^∨ = 1 + ht(θ^∨)` of a base.

## Main results

* `RootPairing.Base.coroot'_highestRoot_twoWeylVector` and
  `RootPairing.Base.coroot'_highestRoot_weylVector`: `⟨2ρ, θ^∨⟩ = 2 (h^∨ - 1)` and
  `⟨ρ, θ^∨⟩ = h^∨ - 1`, with `RootPairing.Base.sum_pairingIn_highestRoot_right_posRootsFinset`
  the integer form `∑_{α > 0} ⟨α, θ^∨⟩ = 2 (h^∨ - 1)`.
* `RootPairing.Base.two_le_dualCoxeterNumber`: `2 ≤ h^∨`.
* `RootPairing.Base.sum_pairingIn_highestRoot_right_sq`: `∑_α ⟨α, θ^∨⟩² = 4 h^∨`, an identity of
  integers.
* `RootPairing.Base.corootForm_coroot_highestRoot`: `P.CorootForm θ^∨ θ^∨ = 4 h^∨`.

## Implementation notes

The definition depends on the base through its highest root; that it is the same for every base,
since the Weyl group acts transitively on bases, is not proved here. The identity
`P.CorootForm θ^∨ θ^∨ = 4 h^∨` holds for each base separately.

## References

* V. G. Kac, *Infinite-Dimensional Lie Algebras*, 3rd ed., Chapter 6, for the dual Coxeter
  number, the normalised invariant form and its comparison with the Killing form.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, Ch. VI, §1.8, for the highest root
  and the pairings of the roots with its coroot.
-/

public section

namespace RootPairing.Base

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] {P : RootPairing ι R M N} [CharZero R] (b : P.Base) [Finite ι] [Nonempty ι]

/-- The **dual Coxeter number** `h^∨ = 1 + ht(θ^∨)` of a base: one more than the sum of the
coefficients of the coroot of the highest root `θ` in the simple coroots. Equivalently
`h^∨ = 1 + ⟨ρ, θ^∨⟩` (`RootPairing.Base.coroot'_highestRoot_weylVector`). -/
noncomputable def dualCoxeterNumber : ℤ :=
  b.flip.height b.highestRoot + 1

theorem dualCoxeterNumber_def : b.dualCoxeterNumber = b.flip.height b.highestRoot + 1 :=
  (rfl)

variable [P.IsCrystallographic] [IsDomain R]

variable [P.IsReduced]

/-- **The Weyl vector pairs with the coroot of the highest root to `h^∨ - 1`**, in its integer
form: the pairings `⟨α, θ^∨⟩` of the positive roots sum to `2 (h^∨ - 1)`. -/
theorem sum_pairingIn_highestRoot_right_posRootsFinset :
    ∑ j ∈ TauCeti.posRootsFinset P b, P.pairingIn ℤ j b.highestRoot =
      2 * (b.dualCoxeterNumber - 1) := by
  apply FaithfulSMul.algebraMap_injective ℤ R
  rw [map_sum]
  simp only [algebraMap_pairingIn, ← root_coroot'_eq_pairing]
  rw [← map_sum, ← TauCeti.twoWeylVector_def,
    TauCeti.coroot'_twoWeylVector_eq_two_mul_height_flip, dualCoxeterNumber_def]
  simp

/-- **The sum of the positive roots pairs with the coroot of the highest root to `2 (h^∨ - 1)`.**
-/
theorem coroot'_highestRoot_twoWeylVector :
    P.coroot' b.highestRoot (TauCeti.twoWeylVector P b) = 2 * ((b.dualCoxeterNumber : R) - 1) := by
  rw [TauCeti.coroot'_twoWeylVector_eq_two_mul_height_flip, dualCoxeterNumber_def]
  push_cast
  ring

/-- **The Weyl vector pairs with the coroot of the highest root to `h^∨ - 1`**, so
`h^∨ = 1 + ⟨ρ, θ^∨⟩`. -/
theorem coroot'_highestRoot_weylVector [Invertible (2 : R)] :
    P.coroot' b.highestRoot (TauCeti.weylVector P b) = (b.dualCoxeterNumber : R) - 1 := by
  rw [TauCeti.coroot'_weylVector_eq_height_flip, dualCoxeterNumber_def]
  push_cast
  ring

/-- **The dual Coxeter number is at least `2`**: the coroot of the highest root is positive, so
its height is at least `1`. -/
theorem two_le_dualCoxeterNumber : 2 ≤ b.dualCoxeterNumber := by
  -- the weight and coweight modules are reflexive, so the coroots form a reduced system too
  have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  have : Module.IsReflexive R N := .of_isPerfPair P.flip.toLinearMap
  have h := (isPos_flip_iff P b _).mpr b.isPos_highestRoot
  rw [isPos_iff] at h
  rw [dualCoxeterNumber_def]
  omega

variable [P.IsIrreducible]

/-- **The squares of the pairings of the roots with the coroot of the highest root sum to
`4 h^∨`**, `∑_α ⟨α, θ^∨⟩² = 4 h^∨`. -/
theorem sum_pairingIn_highestRoot_right_sq [Fintype ι] :
    ∑ j, P.pairingIn ℤ j b.highestRoot ^ 2 = 4 * b.dualCoxeterNumber := by
  classical
  have hpos : Finset.univ.filter b.IsPos = TauCeti.posRootsFinset P b :=
    (TauCeti.posRootsFinset_eq_filter P b).symm
  -- Over the positive roots `⟨α, θ^∨⟩² - ⟨α, θ^∨⟩` vanishes except at `θ`, where it is `4 - 2`.
  have hsq : ∑ j ∈ Finset.univ.filter b.IsPos,
      (P.pairingIn ℤ j b.highestRoot ^ 2 - P.pairingIn ℤ j b.highestRoot) = 2 := by
    rw [Finset.sum_eq_single b.highestRoot]
    · simp [pairingIn_same]
    · intro j hj hne
      rcases b.pairingIn_highestRoot_right_eq_zero_or_eq_one (Finset.mem_filter.mp hj).2 hne
        with h | h <;> simp [h]
    · intro h
      exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, b.isPos_highestRoot⟩) h
  -- Root negation exchanges the negative and the positive roots and preserves `⟨α, θ^∨⟩²`.
  have hneg : ∑ j ∈ Finset.univ.filter (fun j ↦ ¬ b.IsPos j), P.pairingIn ℤ j b.highestRoot ^ 2 =
      ∑ j ∈ Finset.univ.filter b.IsPos, P.pairingIn ℤ j b.highestRoot ^ 2 := by
    refine Finset.sum_nbij' (fun j ↦ P.reflectionPerm j j) (fun j ↦ P.reflectionPerm j j)
      (fun j hj ↦ ?_) (fun j hj ↦ ?_) (fun j _ ↦ TauCeti.reflectionPerm_self_involutive P j)
      (fun j _ ↦ TauCeti.reflectionPerm_self_involutive P j) (fun j _ ↦ by simp)
    · simpa [TauCeti.isPos_reflectionPerm_self_iff_mem_negRoots] using hj
    · simpa [TauCeti.isPos_reflectionPerm_self_iff_mem_negRoots] using
        (Finset.mem_filter.mp hj).2
  have hsum := b.sum_pairingIn_highestRoot_right_posRootsFinset
  rw [Finset.sum_sub_distrib, hpos, hsum] at hsq
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ b.IsPos, hneg, hpos]
  linarith

/-- **The coroot of the highest root has length `4 h^∨` for the canonical coroot form**,
`P.CorootForm θ^∨ θ^∨ = ∑_α ⟨α, θ^∨⟩² = 4 h^∨`. For the root system of a semisimple Lie algebra
`P.CorootForm` is the Killing form on the Cartan subalgebra. -/
theorem corootForm_coroot_highestRoot [Fintype ι] :
    P.CorootForm (P.coroot b.highestRoot) (P.coroot b.highestRoot) =
      4 * (b.dualCoxeterNumber : R) := by
  have h := congrArg (Int.cast : ℤ → R) b.sum_pairingIn_highestRoot_right_sq
  push_cast at h
  rw [corootForm_apply_apply, ← h]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [root'_coroot_eq_pairing, ← P.algebraMap_pairingIn ℤ, eq_intCast, sq]

end RootPairing.Base
