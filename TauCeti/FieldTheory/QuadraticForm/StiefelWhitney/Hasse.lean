/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.QuadraticForm.StiefelWhitney.Class
public import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.Hasse.Basic

/-!
# The second Stiefel–Whitney class and the Hasse invariant

For a regular quadratic form over a field `K` in which `2` is invertible, the second
Stiefel–Whitney class is the image of its Hasse invariant under the canonical comparison
`TauCeti.brauer2EquivH2 K : Additive Br(K)[2] ≃+ H²(G_K, 𝔽₂)`. Both invariants are defined
on `TauCeti.RegularFormClass K`, so this identity requires no choice of diagonalization.
In particular, two regular forms have the same `w₂` exactly when their Hasse invariants agree,
and `w₂` vanishes exactly when the Hasse invariant is trivial.

The Hasse invariant here is Lam's `s(q) = ∏_{i<j} [(aᵢ,aⱼ)]`, also Serre's `ε`, not the
Witt–Clifford invariant `c(q)`. The latter differs by dimension-dependent correction terms.
The comparison follows termwise from `TauCeti.brauerCohomologyEquiv_quaternionClass`:
products of quaternion symbols become sums of Kummer cup products.

## Main results

* `TauCeti.brauerCohomologyEquiv_hasseInvariant`: the comparison with multiplicative
  coefficients sends the Hasse invariant to `h2MuToUnits K (w₂(q))`.
* `TauCeti.brauer2EquivH2_hasseInvariant`: the two-torsion comparison sends `s(q)` to `w₂(q)`.
* `TauCeti.sw2Class_eq_iff_hasseInvariant_eq` and
  `TauCeti.sw2Class_eq_zero_iff_hasseInvariant_eq_one`: equality and vanishing criteria.
* `TauCeti.sw2Class_mk_rankOne_mul`: the scaling formula for `w₂`, transported from the scaling
  formula for the Hasse invariant.
* `TauCeti.sw2Class_mk_rankOne_mul_of_four_dvd`: scaling does not change `w₂` of a form whose
  rank is divisible by `4` and whose first class vanishes.
* `TauCeti.sw2Class_add_mk_rankOne_mul`: the second class of `q ⊥ ⟨c⟩ ⊗ q`, which depends on `q`
  only through its rank and its first class.

## References

* J. Milnor, *Algebraic K-theory and quadratic forms*, Invent. Math. 9 (1970), §3.
* T. Y. Lam, *Introduction to Quadratic Forms over Fields*, GSM 67 (2005), V.3.17–18.
* J.-P. Serre, *Local Fields*, GTM 67 (1979), XIV §2, Proposition 5.
-/

public section

universe u

namespace TauCeti

open Finset _root_.ContinuousCohomology

variable {K : Type u} [Field K] [Invertible (2 : K)]

/-- The comparison with multiplicative coefficients sends the Hasse invariant of a regular
form class to the image of its second Stiefel–Whitney class under the Kummer injection. -/
theorem brauerCohomologyEquiv_hasseInvariant (q : RegularFormClass K) :
    brauerCohomologyEquiv K (Additive.ofMul q.hasseInvariant) =
      (h2MuToUnits K).hom (sw2Class q) := by
  induction q using Quotient.inductionOn with
  | h p =>
    rw [RegularFormClass.hasseInvariant_mk, sw2Class_mk, sw2_def]
    simp only [ofMul_prod, map_sum, brauerCohomologyEquiv_quaternionClass,
      kummerCup_squareClass_squareClass]

/-- **The second Stiefel–Whitney class is the image of the Hasse invariant.** The source is
`Br(K)[2]`, with membership supplied by the two-torsion theorem for the Hasse invariant. -/
@[simp]
theorem brauer2EquivH2_hasseInvariant (q : RegularFormClass K) :
    brauer2EquivH2 K (Additive.ofMul
      ⟨q.hasseInvariant, BrauerGroup.mem_twoTorsion.mpr (q.hasseInvariant_sq)⟩) =
      sw2Class q := by
  apply h2MuToUnits_injective K
  rw [brauer2EquivH2_h2MuToUnits, brauerCohomologyEquiv_hasseInvariant]

/-- Two regular form classes have the same second Stiefel–Whitney class exactly when their
Hasse invariants agree. No equality of ranks or discriminants is required. -/
theorem sw2Class_eq_iff_hasseInvariant_eq (q r : RegularFormClass K) :
    sw2Class q = sw2Class r ↔ q.hasseInvariant = r.hasseInvariant := by
  rw [← (h2MuToUnits_injective K).eq_iff, ← brauerCohomologyEquiv_hasseInvariant,
    ← brauerCohomologyEquiv_hasseInvariant, (brauerCohomologyEquiv K).injective.eq_iff,
    EmbeddingLike.apply_eq_iff_eq]

/-- The second Stiefel–Whitney class vanishes exactly when the Hasse invariant is trivial. -/
theorem sw2Class_eq_zero_iff_hasseInvariant_eq_one (q : RegularFormClass K) :
    sw2Class q = 0 ↔ q.hasseInvariant = 1 := by
  simpa only [sw2Class_zero, RegularFormClass.hasseInvariant_zero] using
    sw2Class_eq_iff_hasseInvariant_eq q 0

/-- **Scaling formula for `w₂`**: for `q` of rank `n`,
`w₂(⟨c⟩ ⊗ q) = w₂(q) + C(n, 2) · (c) ∪ (-1) + (n - 1) · (c) ∪ w₁(q)`.
It is the image of the scaling formula `TauCeti.RegularFormClass.hasseInvariant_mk_rankOne_mul`
for the Hasse invariant. -/
theorem sw2Class_mk_rankOne_mul (c : Kˣ) (x : RegularFormClass K) :
    sw2Class (Quotient.mk (regularFormSetoid K) ⟨1, fun _ => c⟩ * x) =
      sw2Class x + x.rank.choose 2 • (trivialF2TopPairing (AbsoluteGaloisGroup K)).cup 1 1
          (kummerClass c) (kummerClass (-1)) +
        (x.rank - 1) • (trivialF2TopPairing (AbsoluteGaloisGroup K)).cup 1 1
          (kummerClass c) (sw1Class x) := by
  apply h2MuToUnits_injective K
  induction x using Quotient.inductionOn with
  | h p =>
    rw [← brauerCohomologyEquiv_hasseInvariant, RegularFormClass.hasseInvariant_mk_rankOne_mul_mk,
      RegularFormClass.rank_mk, sw1Class_mk, sw1_eq_kummerClass_prod]
    simp only [ofMul_mul, ofMul_pow, map_add, map_nsmul, brauerCohomologyEquiv_hasseInvariant,
      brauerCohomologyEquiv_quaternionClass]

/-- **Scaling invariance of `w₂`**: `w₂(⟨c⟩ ⊗ q) = w₂(q)` when the rank of `q` is divisible by
`4` and `w₁(q) = 0`, since then both correction terms of `TauCeti.sw2Class_mk_rankOne_mul`
vanish. -/
theorem sw2Class_mk_rankOne_mul_of_four_dvd (c : Kˣ) {x : RegularFormClass K}
    (h4 : 4 ∣ x.rank) (h1 : sw1Class x = 0) :
    sw2Class (Quotient.mk (regularFormSetoid K) ⟨1, fun _ => c⟩ * x) = sw2Class x := by
  -- `C(n, 2) = n (n - 1) / 2` is even when `4 ∣ n`
  obtain ⟨k, hk⟩ : 2 ∣ x.rank.choose 2 := by
    rw [Nat.choose_two_right]
    exact Nat.dvd_div_of_mul_dvd (h4.mul_right _)
  rw [sw2Class_mk_rankOne_mul, h1, hk, two_mul, add_nsmul, ZModModule.add_self, map_zero,
    smul_zero, add_zero, add_zero]

/-- **The second Stiefel–Whitney class of `q ⊥ ⟨c⟩ ⊗ q`**, that is of `⟨1, c⟩ ⊗ q`: for `q` of
rank `n`,
`w₂(q ⊥ ⟨c⟩ ⊗ q) = C(n, 2) · (c) ∪ (-1) + (c) ∪ w₁(q) + w₁(q) ∪ (-1)`.
In particular it depends on `q` only through its rank and its first class. -/
theorem sw2Class_add_mk_rankOne_mul (c : Kˣ) (x : RegularFormClass K) :
    sw2Class (x + Quotient.mk (regularFormSetoid K) ⟨1, fun _ => c⟩ * x) =
      x.rank.choose 2 • (trivialF2TopPairing (AbsoluteGaloisGroup K)).cup 1 1
          (kummerClass c) (kummerClass (-1)) +
        (trivialF2TopPairing (AbsoluteGaloisGroup K)).cup 1 1 (kummerClass c) (sw1Class x) +
        (trivialF2TopPairing (AbsoluteGaloisGroup K)).cup 1 1 (sw1Class x)
          (kummerClass (-1)) := by
  induction x using Quotient.inductionOn with
  | h p =>
    obtain ⟨n, w⟩ := p
    rw [sw2Class_add, sw2Class_mk_rankOne_mul, sw1Class_mk_rankOne_mul, RegularFormClass.rank_mk,
      sw1Class_mk, sw2Class_mk, sw1_eq_kummerClass_prod, map_add, map_nsmul, cup_kummerClass_self,
      trivialF2TopPairing_cup_one_one_comm _ (kummerClass (∏ i, w i))]
    rcases n with _ | m
    · simp
    · rw [Nat.add_sub_cancel, succ_nsmul]
      set W := sw2 w
      set A := (trivialF2TopPairing (AbsoluteGaloisGroup K)).cup 1 1
        (kummerClass c) (kummerClass (-1))
      set B := (trivialF2TopPairing (AbsoluteGaloisGroup K)).cup 1 1
        (kummerClass c) (kummerClass (∏ i, w i))
      set E := (trivialF2TopPairing (AbsoluteGaloisGroup K)).cup 1 1
        (kummerClass (∏ i, w i)) (kummerClass (-1))
      calc _ = (m + 1).choose 2 • A + B + E + (W + W) + (m • B + m • B) := by abel
        _ = _ := by simp only [ZModModule.add_self, add_zero]

end TauCeti
