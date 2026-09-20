/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Inversions.StrongExchange
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Numerator

/-!
# The Weyl orbit and the Weyl numerator of a dominant integral weight

A weight `λ` of a root pairing is *dominant integral* for a base `b` when every simple coroot
takes a natural value on it. This file proves, **without any order on the coefficient ring**, the
two facts about such a weight that the Weyl character formula needs about the Weyl numerator
`N(λ) = ∑_{w ∈ W} sgn(w) e^{w ⬝ λ}`: its dot orbit lies below `λ` in the positive root cone, and
it is free, so that `N(λ)` has coefficient `1` at `λ` and coefficient `0` at every other dominant
integral weight.

Both facts are already available over a linearly ordered ring, where the dominant weights form a
chamber: `TauCeti.eq_one_of_smul_eq_self_of_mem_openDominantChamber` is the freeness and
`TauCeti.dotAction_eq_dotAction_iff_of_mem_dominantChamber` its dot form. The Weyl character
formula, however, is an identity about a Lie module over an algebraically closed field, which
carries no linear order making it a strictly ordered ring, so the chamber statements do not apply
to it. As in `TauCeti/LinearAlgebra/RootSystem/Weyl/IntegralDetermination.lean`, the fundamental
domain is therefore described arithmetically: `λ` is dominant integral when `⟨λ, αᵢ^∨⟩ ∈ ℕ` for
every simple root `αᵢ`.

## The arguments

Both go through the inversion set `TauCeti.inversions` of a Weyl-group element, whose cardinality
is its Coxeter length, rather than through chambers.

* *Freeness.* A weight `x` with `⟨x, αᵢ^∨⟩ ∈ 1 + ℕ` at every simple root takes a value in `1 + ℕ`
  at every positive coroot, because a positive coroot is a nonnegative integer combination of the
  simple ones with at least one nonzero coefficient. If `w • x = x` and `w ≠ 1`, then `w` inverts
  some simple root `αᵢ` (`TauCeti.exists_mem_support_mem_inversions_of_ne_one`), and
  `⟨x, (w αᵢ)^∨⟩ = ⟨w x, (w αᵢ)^∨⟩ = ⟨x, αᵢ^∨⟩` exhibits the same element of `R` as a member of
  `1 + ℕ` and as the negative of one, which characteristic zero forbids.
* *The orbit lies below.* Induction on the number of inversions of `w`. If `w ≠ 1`, pick a simple
  inversion `αᵢ` and set `v = w sᵢ`, which has fewer inversions, so that `x - v x` lies in the
  cone by induction. Then `x - w x = (x - v x) + ⟨x, αᵢ^∨⟩ · v αᵢ`, and `v αᵢ` is a positive root
  because `sᵢ` lengthens `v`.

The dot-action versions follow by applying these to the `ρ`-shift `x = λ + ρ`, which satisfies
`⟨x, αᵢ^∨⟩ = ⟨λ, αᵢ^∨⟩ + 1` by `TauCeti.coroot'_weylVector`.

## Main results

* `TauCeti.eq_one_of_smul_eq_self_of_forall_coroot'_eq_natCast_add_one`: **the Weyl group acts
  freely on the strictly dominant integral weights**, with
  `TauCeti.dotAction_injective_of_dominantIntegral` the dot-action form at a dominant integral
  weight.
* `TauCeti.sub_weylGroup_smul_mem_posRootCone_of_dominantIntegral`: **the Weyl orbit of a dominant
  integral weight lies below it in the positive root cone**, with
  `TauCeti.sub_dotAction_mem_posRootCone_of_dominantIntegral` the dot-action form.
* `TauCeti.coeff_weylNumerator_self_of_dominantIntegral`: **`N(λ)` has coefficient `1` at `λ`**,
  and `TauCeti.coeff_weylNumerator_eq_zero_of_dominantIntegral_of_ne`: **coefficient `0` at every
  other dominant integral weight**, with
  `TauCeti.sub_mem_posRootCone_of_coeff_weylNumerator_ne_zero` placing the whole support below
  `λ`.

## References

These facts about the Weyl numerator match the corresponding facts about `ch M · Δ` and together
yield the Weyl character formula.

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §10.3 and
  §13.2 for the two arguments, and Ch. VI, §24 for their use.
-/

public section

namespace TauCeti

universe u v w x

variable {ι : Type u} {R : Type v} {M : Type w} {N : Type x}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : _root_.RootPairing ι R M N} [Finite ι] [CharZero R] [IsDomain R]
  [P.IsCrystallographic] [P.IsReduced] {b : P.Base} {lam x : M}

/-! ### Freeness on the strictly dominant integral weights -/

section Free

variable [P.flip.IsReduced]

/-- **Strict dominance extends from the simple coroots to all the positive ones.** A weight taking
a value in `1 + ℕ` on every simple coroot takes a value in `1 + ℕ` on the coroot of every positive
root, because such a coroot is a nonnegative integer combination of the simple coroots
(`TauCeti.exists_coroot'_eq_sum_nat_of_mem_posRoots`) in which some coefficient is nonzero. -/
theorem exists_coroot'_eq_natCast_add_one_of_mem_posRoots
    (hx : ∀ i ∈ b.support, ∃ n : ℕ, P.coroot' i x = (n : R) + 1)
    {j : ι} (hj : j ∈ posRoots P b) : ∃ n : ℕ, P.coroot' j x = (n : R) + 1 := by
  classical
  obtain ⟨f, ⟨k, hk, hfk⟩, hsum⟩ := exists_coroot'_eq_sum_nat_of_mem_posRoots P b hj
  choose! g hg using hx
  set S : ℕ := ∑ i ∈ b.support, f i * (g i + 1) with hS
  have hcast : P.coroot' j x = (S : R) := by
    rw [hsum, LinearMap.sum_apply, hS]
    simp only [LinearMap.smul_apply, smul_eq_mul]
    push_cast
    exact Finset.sum_congr rfl fun i hi ↦ by rw [hg i hi]
  have hone : 1 ≤ S := by
    have hle : f k * (g k + 1) ≤ S :=
      Finset.single_le_sum (f := fun i ↦ f i * (g i + 1)) (fun _ _ ↦ Nat.zero_le _) hk
    exact le_trans (Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero hfk (Nat.succ_ne_zero (g k)))) hle
  refine ⟨S - 1, ?_⟩
  rw [hcast, Nat.cast_sub hone]
  push_cast
  ring

/-- **The Weyl group acts freely on the strictly dominant integral weights.** If every simple
coroot takes a value in `1 + ℕ` on `x`, then only the identity fixes `x`.

An element other than the identity inverts some simple root `αᵢ`
(`TauCeti.exists_mem_support_mem_inversions_of_ne_one`), and a weight fixed by it would take the
same value on `αᵢ^∨` and on the coroot of the negative root `w αᵢ`; the first value lies in
`1 + ℕ` and the second is the negative of such a value, which is impossible in characteristic
zero. -/
theorem eq_one_of_smul_eq_self_of_forall_coroot'_eq_natCast_add_one {w : P.weylGroup}
    (hx : ∀ i ∈ b.support, ∃ n : ℕ, P.coroot' i x = (n : R) + 1) (hw : w • x = x) : w = 1 := by
  by_contra hne
  obtain ⟨i, hi, hmem⟩ := exists_mem_support_mem_inversions_of_ne_one P b hne
  obtain ⟨-, hneg⟩ := (mem_inversions P b w i).mp hmem
  obtain ⟨n, hn⟩ := hx i hi
  -- the value of `x` on the image coroot is its value on `αᵢ^∨`
  have hjx : P.coroot' (P.weylGroupToPerm w i) x = (n : R) + 1 := by
    have h := _root_.RootPairing.coroot'_weylGroupToPerm_smul P w i x
    rw [hw, hn] at h
    exact h
  -- but the image is a negative root, so that value is the negative of one in `1 + ℕ`
  obtain ⟨m, hm⟩ := exists_coroot'_eq_natCast_add_one_of_mem_posRoots hx
    ((reflectionPerm_self_mem_posRoots_iff_mem_negRoots P b _).mpr
      ((mem_negRoots P b _).mpr hneg))
  rw [_root_.RootPairing.coroot'_reflectionPerm_self, LinearMap.neg_apply, hjx] at hm
  have : ((n + m + 2 : ℕ) : R) = 0 := by push_cast; linear_combination -hm
  simp only [Nat.cast_eq_zero] at this
  omega

end Free

/-! ### The Weyl orbit of a dominant integral weight -/

omit [Finite ι] [CharZero R] [IsDomain R] [P.IsCrystallographic] [P.IsReduced] in
/-- The reflection identity used in the inversion descent for a dominant integral weight. -/
private theorem sub_mul_ofIdx_smul (v : P.weylGroup) (i : ι) :
    x - (v * _root_.RootPairing.weylGroup.ofIdx P i) • x =
      (x - v • x) + P.coroot' i x • P.root (P.weylGroupToPerm v i) := by
  simp only [mul_smul, _root_.RootPairing.weylGroup.ofIdx_smul,
    _root_.RootPairing.Equiv.reflection_smul, _root_.RootPairing.reflection_apply, smul_sub,
    smul_comm, P.weylGroup_apply_root]
  abel

/-- **The Weyl orbit of a dominant integral weight lies below it in the positive root cone.**

The induction is on the number of inversions of `w`: choosing a simple inversion `αᵢ` and writing
`w = v sᵢ` with `v = w sᵢ` shorter, the reflection formula gives
`x - w x = (x - v x) + ⟨x, αᵢ^∨⟩ · v αᵢ`, where `v αᵢ` is positive because `sᵢ` lengthens `v`
(`TauCeti.lt_ncard_inversions_mul_ofIdx_iff`). -/
theorem sub_weylGroup_smul_mem_posRootCone_of_dominantIntegral
    (hx : ∀ i ∈ b.support, ∃ n : ℕ, P.coroot' i x = (n : R)) (w : P.weylGroup) :
    x - w • x ∈ posRootCone P b := by
  suffices h : ∀ n : ℕ, ∀ v : P.weylGroup, (inversions P b v).ncard = n →
      x - v • x ∈ posRootCone P b from h _ w rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro w hw
    rcases eq_or_ne w 1 with rfl | hne
    · simp
    obtain ⟨i, hi, hmem⟩ := exists_mem_support_mem_inversions_of_ne_one P b hne
    have hipos : b.IsPos i := b.isPos_of_mem_support hi
    set v := w * _root_.RootPairing.weylGroup.ofIdx P i with hv
    have hlt : (inversions P b v).ncard < n := by
      rw [← hw, hv]
      exact ncard_inversions_mul_ofIdx_lt_of_mem P b w hmem
    have hwv : w = v * _root_.RootPairing.weylGroup.ofIdx P i := by
      rw [hv, mul_assoc, _root_.RootPairing.weylGroup.ofIdx_mul_self, mul_one]
    -- the simple root `αᵢ` is not yet an inversion of the shorter element `v`
    have hnotinv : i ∉ inversions P b v := by
      rw [← lt_ncard_inversions_mul_ofIdx_iff P b v hipos, ← hwv, hw]
      exact hlt
    have hvpos : P.weylGroupToPerm v i ∈ posRoots P b :=
      (mem_posRoots P b _).mpr
        (by by_contra hc; exact hnotinv ((mem_inversions P b v i).mpr ⟨hipos, hc⟩))
    obtain ⟨m, hm⟩ := hx i hi
    -- the reflection formula, with the coefficient read as a natural multiple
    have hstep : x - w • x = (x - v • x) + m • P.root (P.weylGroupToPerm v i) := by
      rw [hwv, sub_mul_ofIdx_smul, hm, Nat.cast_smul_eq_nsmul]
    rw [hstep]
    exact add_mem (ih _ hlt v rfl)
      (nsmul_mem (root_mem_posRootCone_of_mem_posRoots P b hvpos) m)

/-! ### The dot action -/

section DotAction

variable [Invertible (2 : R)]

/-- The `ρ`-shift of a dominant integral weight is strictly dominant integral, since `ρ` pairs to
`1` with every simple coroot (`TauCeti.coroot'_weylVector`). -/
private theorem forall_coroot'_add_weylVector_eq_natCast_add_one
    (hlam : ∀ i ∈ b.support, ∃ n : ℕ, P.coroot' i lam = (n : R)) (i : ι) (hi : i ∈ b.support) :
    ∃ n : ℕ, P.coroot' i (lam + weylVector P b) = (n : R) + 1 := by
  obtain ⟨n, hn⟩ := hlam i hi
  exact ⟨n, by rw [coroot'_add_weylVector P b hi, hn]⟩

/-- **The dot orbit of a dominant integral weight lies below it in the positive root cone**: the
dot orbit of `λ` is the `ρ`-shift of the linear orbit of `λ + ρ`, which is dominant integral. -/
theorem sub_dotAction_mem_posRootCone_of_dominantIntegral
    (hlam : ∀ i ∈ b.support, ∃ n : ℕ, P.coroot' i lam = (n : R)) (w : P.weylGroup) :
    lam - dotAction P b w lam ∈ posRootCone P b := by
  have hshift : ∀ i ∈ b.support, ∃ n : ℕ, P.coroot' i (lam + weylVector P b) = (n : R) := by
    intro i hi
    obtain ⟨n, hn⟩ := forall_coroot'_add_weylVector_eq_natCast_add_one hlam i hi
    exact ⟨n + 1, by rw [hn]; push_cast; ring⟩
  have h := sub_weylGroup_smul_mem_posRootCone_of_dominantIntegral hshift w
  rwa [← dotAction_add_weylVector P b w lam, add_sub_add_right_eq_sub] at h

variable [P.flip.IsReduced]

/-- **The dot action is free at a dominant integral weight**: no two Weyl-group elements carry `λ`
to the same place, because the `ρ`-shift `λ + ρ` is strictly dominant integral. -/
theorem dotAction_injective_of_dominantIntegral
    (hlam : ∀ i ∈ b.support, ∃ n : ℕ, P.coroot' i lam = (n : R)) :
    Function.Injective fun w : P.weylGroup ↦ dotAction P b w lam := by
  intro v w hvw
  -- Expose the applications hidden by the lambda in `Function.Injective` before rewriting.
  have hdot : dotAction P b v lam = dotAction P b w lam := hvw
  have hshift : v • (lam + weylVector P b) = w • (lam + weylVector P b) := by
    rw [← dotAction_add_weylVector P b v lam, ← dotAction_add_weylVector P b w lam,
      hdot]
  have hfix : (w⁻¹ * v) • (lam + weylVector P b) = lam + weylVector P b := by
    rw [mul_smul, hshift, inv_smul_smul]
  have hone := eq_one_of_smul_eq_self_of_forall_coroot'_eq_natCast_add_one
    (forall_coroot'_add_weylVector_eq_natCast_add_one hlam) hfix
  rw [inv_mul_eq_one] at hone
  exact hone.symm

end DotAction

/-! ### The Weyl numerator -/

section Numerator

variable [Invertible (2 : R)] [Fintype P.weylGroup]

/-- **The Weyl numerator of a dominant integral weight is supported in `λ - Q⁺`**: it is supported
on the dot orbit of `λ`, which lies below `λ`. -/
theorem sub_mem_posRootCone_of_coeff_weylNumerator_ne_zero
    (hlam : ∀ i ∈ b.support, ∃ n : ℕ, P.coroot' i lam = (n : R))
    (hx : (weylNumerator P b lam).coeff x ≠ 0) : lam - x ∈ posRootCone P b := by
  by_contra hcone
  refine hx (coeff_weylNumerator_eq_zero P b fun w h ↦ hcone ?_)
  rw [← h]
  exact sub_dotAction_mem_posRootCone_of_dominantIntegral hlam w

/-- **The Weyl numerator of a dominant integral weight vanishes at every other dominant integral
weight.** A weight of the dot orbit of `λ` lies below `λ`, and if it is itself dominant integral
then `λ` lies below it too, so the two agree because the positive root cone is pointed. -/
theorem coeff_weylNumerator_eq_zero_of_dominantIntegral_of_ne
    (hlam : ∀ i ∈ b.support, ∃ n : ℕ, P.coroot' i lam = (n : R))
    (hx : ∀ i ∈ b.support, ∃ n : ℕ, P.coroot' i x = (n : R)) (hne : x ≠ lam) :
    (weylNumerator P b lam).coeff x = 0 := by
  refine coeff_weylNumerator_eq_zero P b fun w h ↦ hne ?_
  have hdown : lam - x ∈ posRootCone P b := by
    rw [← h]
    exact sub_dotAction_mem_posRootCone_of_dominantIntegral hlam w
  have hup : x - lam ∈ posRootCone P b := by
    have hxl : dotAction P b w⁻¹ x = lam := by rw [← h, dotAction_inv_dotAction]
    have hinv := sub_dotAction_mem_posRootCone_of_dominantIntegral (lam := x) hx w⁻¹
    rwa [hxl] at hinv
  have := eq_zero_of_add_eq_zero_of_mem_posRootCone P b hup hdown (by abel)
  rwa [sub_eq_zero] at this

variable [P.flip.IsReduced]

/-- **The Weyl numerator of a dominant integral weight has coefficient `1` there**: the dot orbit
is free, so the term of the identity sits alone at `λ`. -/
theorem coeff_weylNumerator_self_of_dominantIntegral
    (hlam : ∀ i ∈ b.support, ∃ n : ℕ, P.coroot' i lam = (n : R)) :
    (weylNumerator P b lam).coeff lam = 1 := by
  have h := coeff_weylNumerator_dotAction_of_injective P b
    (dotAction_injective_of_dominantIntegral hlam) 1
  rwa [dotAction_one, map_one, Units.val_one] at h

end Numerator

end TauCeti
