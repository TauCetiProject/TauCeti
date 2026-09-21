/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Chamber

/-!
# The Weyl vector of a base

The **Weyl vector** `ρ` of a base of a root pairing is the half-sum of the positive roots. It is
the shift that turns the Weyl group action on weights into the dot action, and it appears in the
Weyl character, dimension and Kostant formulas as the correction `λ ↦ λ + ρ`.

Which roots are positive is defined only over a coefficient ring of characteristic zero, and
halving asks for `2` to be invertible on top of that. So the sum of the positive roots is
introduced first, as `TauCeti.twoWeylVector`, over a characteristic-zero coefficient ring, and the
Weyl vector itself only once `2` is invertible as well. The simple-coroot pairing and the simple
reflection identity are proved for the sum first and then divided by two; the statements that
speak of `ρ` alone — the dot action and the dominance results — are proved only in the halved
form. So nothing below assumes more of the coefficient ring than its own statement needs.

The one theorem the notion exists for is that `ρ` pairs to `1` with every simple coroot,
equivalently that the simple reflection `sᵢ` sends `ρ` to `ρ - αᵢ`. Its proof is the classical
one: `sᵢ` negates `αᵢ` and permutes the remaining positive roots, so the pairings of those
remaining roots with `αᵢ^∨` cancel in pairs and only `⟨αᵢ, αᵢ^∨⟩ = 2` survives.

Those values on the simple coroots determine the values on all of them, and the answer is the
**height** of the coroot: expanding `α^∨` in the simple coroots and pairing termwise gives
`⟨ρ, α^∨⟩ = ht(α^∨)`, the sum of the coefficients. Two consequences of that identity are recorded
below. First, `⟨ρ, α^∨⟩` is never zero, because no root has height zero — so `ρ` is a **regular**
weight, with no order on the coefficient ring needed. Over a linearly ordered ring that already
follows from strict dominance, but a root system attached to a Lie algebra over an algebraically
closed field carries no order, and it is there that the Weyl dimension formula needs its
denominators `⟨ρ, α^∨⟩` to be invertible. Second, where there *is* an order, the pairing with a
positive coroot is not merely positive but at least `1`, being a positive integer.

## Main definitions

* `TauCeti.twoWeylVector`: the sum of the positive roots, that is `2ρ`.
* `TauCeti.weylVector`: the Weyl vector `ρ`, the half-sum of the positive roots, defined when `2`
  is invertible in the coefficient ring.

## Main results

* `TauCeti.coroot'_twoWeylVector` and `TauCeti.coroot'_weylVector`: `⟨2ρ, αᵢ^∨⟩ = 2` and
  `⟨ρ, αᵢ^∨⟩ = 1` for every simple root `αᵢ`.
* `TauCeti.reflection_twoWeylVector` and `TauCeti.reflection_weylVector`: `sᵢ(2ρ) = 2ρ - 2αᵢ` and
  `sᵢ(ρ) = ρ - αᵢ`.
* `TauCeti.sum_root_negRootsFinset`: the sum of the negative roots is `-2ρ`.
* `TauCeti.coroot'_twoWeylVector_eq_two_mul_height_flip` and
  `TauCeti.coroot'_weylVector_eq_height_flip`: `⟨2ρ, α^∨⟩ = 2 ht(α^∨)` and `⟨ρ, α^∨⟩ = ht(α^∨)` for
  an arbitrary root `α`, the general form of the two preceding identities.
* `TauCeti.isRegularWeight_twoWeylVector` and `TauCeti.isRegularWeight_weylVector`: `2ρ` and `ρ`
  are regular weights, needing no order on the coefficient ring, with
  `TauCeti.coroot'_twoWeylVector_ne_zero` and `TauCeti.coroot'_weylVector_ne_zero` the pairings
  that witness it and `TauCeti.twoWeylVector_ne_zero`, `TauCeti.weylVector_ne_zero` the resulting
  nonvanishing.
* `TauCeti.reflection_add_weylVector_sub_weylVector`: the dot action of a simple reflection,
  `sᵢ ⬝ λ = λ - (⟨λ, αᵢ^∨⟩ + 1) αᵢ`.
* `TauCeti.add_weylVector_mem_openDominantChamber` and
  `TauCeti.weylVector_mem_openDominantChamber`: over a linearly ordered coefficient ring the
  `ρ`-shift of a dominant weight is strictly dominant, and `ρ` itself is a regular weight.
* `TauCeti.openDominantChamber_nonempty`: consequently the open dominant chamber has a point,
  which over a general coefficient ring is a genuine hypothesis rather than a formality.
* `TauCeti.one_le_coroot'_weylVector_of_mem_posRoots` and
  `TauCeti.coroot'_weylVector_le_neg_one_of_mem_negRoots`: over a linearly ordered coefficient ring
  `⟨ρ, α^∨⟩ ≥ 1` for a positive root and `≤ -1` for a negative one.

## References

This file supplies the root-pairing-level prerequisite of the Weyl vector of the highest-weight
theory: the nonvanishing and integrality of `⟨ρ, α^∨⟩` proved below are what makes the denominator
of the Weyl dimension formula `dim L(λ) = ∏_{α>0} ⟨λ+ρ, α^∨⟩ / ⟨ρ, α^∨⟩` meaningful. Nothing here
is a Lie-algebra-level declaration: `ρ` is built for an abstract root pairing, where the
positive-root combinatorics it needs already lives, so that the Lie-algebra version is a
specialization rather than a rebuild.

The argument is the one in J. E. Humphreys, *Introduction to Lie Algebras and Representation
Theory*, GTM 9, Ch. III, §10.2 and §13.3.
-/

public section

namespace TauCeti

universe u v w x

variable {ι : Type u} {R : Type v} {M : Type w} {N : Type x}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N)

variable [CharZero R] (b : P.Base) [Finite ι]

/-- **Twice the Weyl vector**: the sum of the positive roots of a base.

The Weyl vector itself is `TauCeti.weylVector`, this element halved; it needs `2` to be invertible
in the coefficient ring, whereas the sum needs only the characteristic-zero hypothesis under which
the positive roots are defined at all, and carries all the content. -/
noncomputable def twoWeylVector : M := ∑ i ∈ posRootsFinset P b, P.root i

/-- `2ρ` is the sum of the positive roots, by definition. -/
lemma twoWeylVector_def : twoWeylVector P b = ∑ i ∈ posRootsFinset P b, P.root i := by
  rw [twoWeylVector]

section Reduced

variable [IsDomain R] [P.IsCrystallographic] [P.IsReduced]

/-- **The pairings of the positive roots other than `αᵢ` with `αᵢ^∨` cancel.** The simple
reflection `sᵢ` permutes those roots and negates each of their pairings with `αᵢ^∨`, so the sum is
its own negative. -/
private theorem sum_pairing_posRootsFinset_erase_eq_zero [DecidableEq ι] {i : ι}
    (hi : i ∈ b.support) :
    ∑ j ∈ (posRootsFinset P b).erase i, P.pairing j i = 0 := by
  set E := (posRootsFinset P b).erase i
  have key : ∑ j ∈ E, P.pairing (P.reflectionPerm i j) i = ∑ j ∈ E, P.pairing j i :=
    sum_posRootsFinset_erase_comp_reflectionPerm P b hi fun j ↦ P.pairing j i
  have hneg : ∑ j ∈ E, P.pairing (P.reflectionPerm i j) i = -∑ j ∈ E, P.pairing j i := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ ↦ by
      rw [← P.pairing_reflectionPerm i j i, P.pairing_reflectionPerm_self_right]
  have hself : ∑ j ∈ E, P.pairing j i = -∑ j ∈ E, P.pairing j i := key.symm.trans hneg
  exact CharZero.eq_neg_self_iff.mp hself

/-- **The sum of the positive roots pairs to `2` with every simple coroot.** All the positive roots
other than `αᵢ` cancel, leaving `⟨αᵢ, αᵢ^∨⟩ = 2`.

Not `@[simp]`: `RootPairing.coroot'` is an `abbrev`, so `simp` unfolds this left-hand side through
`LinearMap.flip_apply` and the `simpNF` linter rejects the tag. The `simp`-usable form of this
identity is `TauCeti.reflection_twoWeylVector` below. -/
theorem coroot'_twoWeylVector {i : ι} (hi : i ∈ b.support) :
    P.coroot' i (twoWeylVector P b) = 2 := by
  classical
  have hmem : i ∈ posRootsFinset P b :=
    (mem_posRootsFinset P b i).mpr (support_subset_posRoots P b (Finset.mem_coe.mpr hi))
  rw [twoWeylVector_def, map_sum]
  simp only [RootPairing.root_coroot'_eq_pairing]
  rw [← Finset.add_sum_erase _ _ hmem, sum_pairing_posRootsFinset_erase_eq_zero P b hi, add_zero,
    RootPairing.pairing_same]

/-- **A simple reflection subtracts `2αᵢ` from the sum of the positive roots.** -/
@[simp]
theorem reflection_twoWeylVector {i : ι} (hi : i ∈ b.support) :
    P.reflection i (twoWeylVector P b) = twoWeylVector P b - (2 : R) • P.root i := by
  rw [RootPairing.reflection_apply, coroot'_twoWeylVector P b hi]

/-- **The sum of the positive roots pairs with an arbitrary coroot to twice the height of that
coroot**, `⟨2ρ, α^∨⟩ = 2 ht(α^∨)`, the height being taken relative to the flipped base. In
particular the pairing is an even integer; a simple coroot has height `1`, so there it is the
value `2` of `TauCeti.coroot'_twoWeylVector`. -/
theorem coroot'_twoWeylVector_eq_two_mul_height_flip (i : ι) :
    P.coroot' i (twoWeylVector P b) = 2 * (b.flip.height i : R) := by
  -- Pairing with `2ρ` is a linear functional on the coweight space, which is the weight space of
  -- `P.flip`; the roots of `P.flip` are the coroots of `P`, and on the simple ones among them the
  -- functional is constantly `2`.
  have hpair : ∀ j : ι, P.coroot' j (twoWeylVector P b)
      = P.toLinearMap (twoWeylVector P b) (P.flip.root j) := fun j ↦ by
    rw [RootPairing.flip_root, LinearMap.flip_apply]
  have hg : ∀ j ∈ b.flip.support, P.toLinearMap (twoWeylVector P b) (P.flip.root j) = 2 := by
    intro j hj
    rw [RootPairing.Base.flip_support] at hj
    rw [← hpair]
    exact coroot'_twoWeylVector P b hj
  rw [hpair i]
  have hval := apply_root_eq_height_zsmul P.flip b.flip
    (P.toLinearMap (twoWeylVector P b)).toAddMonoidHom hg i
  rwa [LinearMap.toAddMonoidHom_coe, zsmul_eq_mul, mul_comm] at hval

/-- **The sum of the positive roots pairs to a nonzero scalar with every coroot.** No order on the
coefficient ring is involved: the pairing is twice the height of the coroot, and no root has height
zero. -/
theorem coroot'_twoWeylVector_ne_zero (i : ι) : P.coroot' i (twoWeylVector P b) ≠ 0 := by
  rw [coroot'_twoWeylVector_eq_two_mul_height_flip]
  have h : (2 : R) * (b.flip.height i : R) = ((2 * b.flip.height i : ℤ) : R) := by push_cast; ring
  rw [h, Int.cast_ne_zero]
  exact mul_ne_zero two_ne_zero (b.flip.height_ne_zero i)

/-- **The sum of the positive roots is a regular weight**, lying on no wall. -/
theorem isRegularWeight_twoWeylVector : IsRegularWeight P (twoWeylVector P b) :=
  (isRegularWeight_iff P _).mpr (coroot'_twoWeylVector_ne_zero P b)

/-- The sum of the positive roots is nonzero as soon as there is a root at all. -/
theorem twoWeylVector_ne_zero [Nonempty ι] : twoWeylVector P b ≠ 0 := fun h ↦
  coroot'_twoWeylVector_ne_zero P b (Classical.arbitrary ι) (by rw [h, map_zero])

end Reduced

/-- **The sum of the negative roots is `-2ρ`.** Root negation is a bijection from the negative
roots onto the positive ones. -/
theorem sum_root_negRootsFinset :
    ∑ i ∈ negRootsFinset P b, P.root i = -twoWeylVector P b := by
  have hinv := reflectionPerm_self_involutive P
  rw [twoWeylVector_def, ← Finset.sum_neg_distrib]
  refine Finset.sum_equiv hinv.toPerm (fun j ↦ ?_) fun j _ ↦ ?_
  · rw [mem_negRootsFinset, mem_posRootsFinset, Function.Involutive.coe_toPerm]
    exact (reflectionPerm_self_mem_posRoots_iff_mem_negRoots P b j).symm
  · simp

section Weyl

variable [Invertible (2 : R)]

/-- **The Weyl vector `ρ`**: the half-sum of the positive roots of a base. -/
noncomputable def weylVector : M := ⅟(2 : R) • twoWeylVector P b

/-- `ρ` is half the sum of the positive roots, by definition. -/
lemma weylVector_def : weylVector P b = ⅟(2 : R) • twoWeylVector P b := by
  rw [weylVector]

/-- Doubling the Weyl vector recovers the sum of the positive roots. -/
@[simp]
lemma two_smul_weylVector : (2 : R) • weylVector P b = twoWeylVector P b := by
  rw [weylVector, smul_smul, mul_invOf_self, one_smul]

variable [IsDomain R] [P.IsCrystallographic] [P.IsReduced]

/-- **The Weyl vector pairs to `1` with every simple coroot**, `⟨ρ, αᵢ^∨⟩ = 1`. This is the
characteristic pairing identity that `ρ` is introduced for; it records the values of `ρ` on the
simple coroots, and over an abstract root pairing those values need not pin `ρ` down, since
nothing here says the simple coroots separate the points of `M`.

Not `@[simp]`, for the same reason as `TauCeti.coroot'_twoWeylVector`. -/
theorem coroot'_weylVector {i : ι} (hi : i ∈ b.support) : P.coroot' i (weylVector P b) = 1 := by
  rw [weylVector, map_smul, coroot'_twoWeylVector P b hi, smul_eq_mul, invOf_mul_self]

/-- **A simple reflection subtracts its simple root from the Weyl vector**, `sᵢ(ρ) = ρ - αᵢ`. -/
@[simp]
theorem reflection_weylVector {i : ι} (hi : i ∈ b.support) :
    P.reflection i (weylVector P b) = weylVector P b - P.root i := by
  rw [RootPairing.reflection_apply, coroot'_weylVector P b hi, one_smul]

/-- **The `ρ`-shift raises every simple coroot pairing by one.** This is the whole role of `ρ` in
the highest-weight theory: it converts the dominance condition `0 ≤ ⟨λ, αᵢ^∨⟩` into the strict one
`0 < ⟨λ + ρ, αᵢ^∨⟩`. -/
theorem coroot'_add_weylVector {i : ι} (hi : i ∈ b.support) (x : M) :
    P.coroot' i (x + weylVector P b) = P.coroot' i x + 1 := by
  rw [map_add, coroot'_weylVector P b hi]

/-- **The dot action of a simple reflection.** Conjugating the reflection `sᵢ` by the translation
by `ρ` gives `sᵢ ⬝ λ = λ - (⟨λ, αᵢ^∨⟩ + 1) αᵢ`. Only this formula on weights is proved here; it is
the shifted Weyl group action that the highest-weight theory uses in place of the linear one, but
the statement that it permutes the highest weights of a given central character belongs to that
setting and needs its hypotheses. -/
theorem reflection_add_weylVector_sub_weylVector {i : ι} (hi : i ∈ b.support) (x : M) :
    P.reflection i (x + weylVector P b) - weylVector P b
      = x - (P.coroot' i x + 1) • P.root i := by
  rw [RootPairing.reflection_apply, coroot'_add_weylVector P b hi]
  abel

/-- **The Weyl vector pairs with an arbitrary coroot to give the height of that coroot**,
`⟨ρ, α^∨⟩ = ht(α^∨)`. In particular the pairing is an integer, which for a simple coroot is the
value `1` of `TauCeti.coroot'_weylVector`.

Not `@[simp]`, for the same reason as `TauCeti.coroot'_twoWeylVector`. -/
theorem coroot'_weylVector_eq_height_flip (i : ι) :
    P.coroot' i (weylVector P b) = (b.flip.height i : R) := by
  rw [weylVector_def, map_smul, coroot'_twoWeylVector_eq_two_mul_height_flip, smul_eq_mul,
    ← mul_assoc, invOf_mul_self, one_mul]

/-- **The Weyl vector pairs to a nonzero scalar with every coroot.** This is the nonvanishing of
the denominators `⟨ρ, α^∨⟩` of the Weyl dimension formula, and it needs no order on the coefficient
ring: the pairing is the height of the coroot, and no root has height zero. -/
theorem coroot'_weylVector_ne_zero (i : ι) : P.coroot' i (weylVector P b) ≠ 0 := by
  rw [coroot'_weylVector_eq_height_flip]
  exact_mod_cast b.flip.height_ne_zero i

/-- **The Weyl vector is a regular weight**, lying on no wall. Over a linearly ordered coefficient
ring this also follows from `TauCeti.weylVector_mem_openDominantChamber`; the point of the present
form is that it holds with no order at all, which is the situation of a root system attached to a
Lie algebra over an algebraically closed field. -/
theorem isRegularWeight_weylVector : IsRegularWeight P (weylVector P b) :=
  (isRegularWeight_iff P _).mpr (coroot'_weylVector_ne_zero P b)

/-- The Weyl vector is nonzero as soon as there is a root at all. -/
theorem weylVector_ne_zero [Nonempty ι] : weylVector P b ≠ 0 := fun h ↦
  coroot'_weylVector_ne_zero P b (Classical.arbitrary ι) (by rw [h, map_zero])

end Weyl

section Ordered

variable [LinearOrder R] [IsStrictOrderedRing R] [Invertible (2 : R)]
  [P.IsCrystallographic] [P.IsReduced]

/-- **Shifting a dominant weight by `ρ` makes it strictly dominant.** -/
theorem add_weylVector_mem_openDominantChamber {x : M} (hx : x ∈ dominantChamber P b) :
    x + weylVector P b ∈ openDominantChamber P b := by
  rw [mem_openDominantChamber]
  intro i hi
  rw [coroot'_add_weylVector P b hi]
  exact lt_of_le_of_lt ((mem_dominantChamber P b x).mp hx i hi) (lt_add_one _)

/-- **The Weyl vector is strictly dominant**, hence a regular weight: it lies on no wall of the
dominant chamber. -/
theorem weylVector_mem_openDominantChamber :
    weylVector P b ∈ openDominantChamber P b := by
  simpa using add_weylVector_mem_openDominantChamber P b (zero_mem_dominantChamber P b)

/-- **The open dominant chamber is nonempty** once `2` is invertible: the Weyl vector `ρ` pairs to
`1` with every simple coroot, so it is strictly dominant. -/
theorem openDominantChamber_nonempty : (openDominantChamber P b).Nonempty :=
  ⟨weylVector P b, weylVector_mem_openDominantChamber P b⟩

/-- **The Weyl vector pairs to at least `1` with the coroot of every positive root.** This sharpens
`TauCeti.coroot'_pos_of_mem_posRoots` at `ρ` from a strict inequality to an integral one: the
pairing is the height of the coroot, a positive integer. It is the positivity of the denominators
of the Weyl dimension formula. -/
theorem one_le_coroot'_weylVector_of_mem_posRoots [P.flip.IsReduced] {i : ι}
    (hi : i ∈ posRoots P b) : 1 ≤ P.coroot' i (weylVector P b) := by
  rw [coroot'_weylVector_eq_height_flip]
  exact_mod_cast one_le_height_of_mem_posRoots P.flip b.flip (by rwa [posRoots_flip])

/-- **The Weyl vector pairs to at most `-1` with the coroot of every negative root.** -/
theorem coroot'_weylVector_le_neg_one_of_mem_negRoots [P.flip.IsReduced] {i : ι}
    (hi : i ∈ negRoots P b) : P.coroot' i (weylVector P b) ≤ -1 := by
  rw [coroot'_weylVector_eq_height_flip]
  have h : b.flip.height i ≤ -1 := by
    have := height_neg_of_mem_negRoots P.flip b.flip (by rwa [negRoots_flip])
    omega
  exact_mod_cast h

end Ordered

end TauCeti
