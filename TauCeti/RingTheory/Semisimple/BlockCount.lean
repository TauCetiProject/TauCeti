/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.CentralIdempotent
public import Mathlib.RingTheory.SimpleRing.Matrix

/-!
# Block counts and factor matching for products of simple rings

Artin--Wedderburn presents a semisimple ring `R` as a finite product of positive-size matrix
algebras over division rings. The results here compare any two such presentations: the number of
blocks is an invariant (`RingEquiv.card_blocks_eq`), and the factors match by ring isomorphisms
(`RingEquiv.exists_equiv_factors`).

Factor matching holds for arbitrary products of simple rings, including infinite products. A
coordinate central idempotent `δᵢ` is primitive among central idempotents: the only central
idempotents `e` satisfying `e * δᵢ = e` are `0` and `δᵢ`. A ring isomorphism therefore carries
`δᵢ` to exactly one coordinate central idempotent. Applying
the inverse isomorphism gives a bijection of the indices, and restricting the original
isomorphism gives the matched factor isomorphisms. The images of the coordinate idempotents
determine this bijection even when some factors are isomorphic. The central-idempotent dichotomy
used here is `TauCeti.centralIdempotents_eq_pair`.

Simplicity of the factors is all the argument uses. In particular, `RingEquiv.card_blocks_eq`
applies to matrix algebras over arbitrary simple rings. Positivity of their sizes is essential:
a zero-size matrix algebra is trivial, so any presentation could be padded with such blocks.
These are the same `NeZero` hypotheses produced by
`IsSemisimpleRing.exists_ringEquiv_pi_matrix_divisionRing`. Semisimplicity of `R` guarantees a
Wedderburn presentation exists, but is not needed to compare presentations.

The finer uniqueness of the matrix sizes and division rings is
`TauCeti.wedderburn_blocks_unique` in
`TauCeti/RingTheory/Semisimple/Wedderburn/Uniqueness.lean`. It applies
`TauCeti.wedderburn_data_unique` to the matched matrix blocks.

## Main results

* `RingEquiv.exists_equiv_factors`: an isomorphism between products of simple rings induces an
  equivalence of their index sets and compatible isomorphisms of the matched factors.
* `RingEquiv.card_eq_of_pi_of_isSimpleRing`: two presentations of a ring as products of simple
  rings have equal `Nat.card` of their index sets.
* `RingEquiv.card_blocks_eq`: two presentations as finite products of positive-size matrix
  algebras over simple rings have the same number of blocks.

## References

T. Y. Lam, *A First Course in Noncommutative Rings*, §3, or C. W. Curtis and I. Reiner,
*Representation Theory of Finite Groups and Associative Algebras*, §25.
-/

public section

namespace RingEquiv

open TauCeti

universe u v w x

section Products

variable {ι : Type u} {κ : Type v} [DecidableEq ι] [DecidableEq κ]
  {A : ι → Type w} {B : κ → Type x}
  [∀ i, Ring (A i)] [∀ i, IsSimpleRing (A i)]
  [∀ j, Ring (B j)] [∀ j, IsSimpleRing (B j)]

omit [∀ i, IsSimpleRing (A i)] [DecidableEq κ] in
private theorem image_coordinate_eq_zero_or_one (f : (∀ i, A i) ≃+* (∀ j, B j))
    (i : ι) (j : κ) :
    f (Pi.single i (1 : A i)) j = 0 ∨ f (Pi.single i (1 : A i)) j = 1 := by
  have hsingle : Pi.single i (1 : A i) ∈ centralIdempotents (∀ i, A i) := by
    rw [mem_centralIdempotents_pi]
    intro k
    by_cases h : k = i
    · subst k
      simpa using (one_mem_centralIdempotents (R := A i))
    · simpa [Pi.single_eq_of_ne h] using (zero_mem_centralIdempotents (R := A k))
  have hmem := (mem_centralIdempotents_pi B).mp (map_mem_centralIdempotents f hsingle) j
  simpa [centralIdempotents_eq_pair] using hmem

variable (f : (∀ i, A i) ≃+* (∀ j, B j))

omit [∀ j, IsSimpleRing (B j)] in
private theorem image_single_one_of_coordinate_eq_one [∀ j, Nontrivial (B j)] {i : ι} {j : κ}
    (h : f (Pi.single i (1 : A i)) j = 1) :
    f (Pi.single i (1 : A i)) = Pi.single j (1 : B j) := by
  -- Pulling back the target coordinate idempotent gives a nonzero central idempotent supported
  -- at `i`; simplicity of `A i` forces its value there to be `1`.
  have hmul : Pi.single j (1 : B j) * f (Pi.single i (1 : A i)) =
      Pi.single j (1 : B j) := by rw [← Pi.single_mul_left, h, one_mul]
  have hpre := congrArg f.symm hmul
  rw [map_mul, f.symm_apply_apply, ← Pi.single_mul_right, mul_one] at hpre
  have hcoord : f.symm (Pi.single j (1 : B j)) i = 1 := by
    rcases image_coordinate_eq_zero_or_one f.symm j i with hz | ho
    · rw [hz, Pi.single_zero] at hpre
      have hz' := congrArg f hpre
      have := congrFun hz' j
      simp at this
    · exact ho
  rw [hcoord] at hpre
  exact (congrArg f hpre).trans (f.apply_symm_apply _)

private theorem exists_image_single_one (i : ι) :
    ∃ j : κ, f (Pi.single i (1 : A i)) = Pi.single j (1 : B j) := by
  have himage : f (Pi.single i (1 : A i)) ≠ 0 := by simp
  obtain ⟨j, hj⟩ := Function.ne_iff.mp himage
  exact ⟨j, image_single_one_of_coordinate_eq_one f
    ((image_coordinate_eq_zero_or_one f i j).resolve_left hj)⟩

private noncomputable def targetIndex (i : ι) : κ :=
  (exists_image_single_one f i).choose

private theorem image_single_one_targetIndex (i : ι) :
    f (Pi.single i (1 : A i)) = Pi.single (targetIndex f i) (1 : B (targetIndex f i)) :=
  (exists_image_single_one f i).choose_spec

private theorem targetIndex_bijective : Function.Bijective (targetIndex f) := by
  constructor
  · intro i i' h
    have hsingle : Pi.single i (1 : A i) = Pi.single i' (1 : A i') := f.injective (by
      rw [image_single_one_targetIndex, image_single_one_targetIndex, h])
    by_contra hi
    have := congrFun hsingle i
    simp [Pi.single_eq_of_ne hi] at this
  · intro j
    obtain ⟨i, hi⟩ := exists_image_single_one f.symm j
    refine ⟨i, ?_⟩
    have hsingle : Pi.single (targetIndex f i) (1 : B (targetIndex f i)) =
        Pi.single j (1 : B j) := by
      rw [← image_single_one_targetIndex, ← hi, f.apply_symm_apply]
    by_contra hj
    have := congrFun hsingle j
    simp [Pi.single_eq_of_ne (Ne.symm hj)] at this

private noncomputable def blockEquiv : ι ≃ κ :=
  Equiv.ofBijective (targetIndex f) (targetIndex_bijective f)

private theorem image_single_one_blockEquiv (i : ι) :
    f (Pi.single i (1 : A i)) = Pi.single (blockEquiv f i) (1 : B (blockEquiv f i)) :=
  image_single_one_targetIndex f i

private theorem map_single_eq_single (i : ι) (x : A i) :
    f (Pi.single i x) =
      Pi.single (blockEquiv f i) (f (Pi.single i x) (blockEquiv f i)) := by
  have hmul : Pi.single i (1 : A i) * Pi.single i x = Pi.single i x := by
    rw [← Pi.single_mul, one_mul]
  have h := congrArg f hmul
  rw [map_mul, image_single_one_blockEquiv, ← Pi.single_mul_left, one_mul] at h
  exact h.symm

private theorem symm_map_single_eq_single (i : ι) (y : B (blockEquiv f i)) :
    f.symm (Pi.single (blockEquiv f i) y) =
      Pi.single i (f.symm (Pi.single (blockEquiv f i) y) i) := by
  have hcoord : f.symm (Pi.single (blockEquiv f i) (1 : B (blockEquiv f i))) =
      Pi.single i (1 : A i) := by rw [← image_single_one_blockEquiv, f.symm_apply_apply]
  have hmul : Pi.single (blockEquiv f i) (1 : B (blockEquiv f i)) *
      Pi.single (blockEquiv f i) y = Pi.single (blockEquiv f i) y := by
    rw [← Pi.single_mul, one_mul]
  have h := congrArg f.symm hmul
  rw [map_mul, hcoord, ← Pi.single_mul_left, one_mul] at h
  exact h.symm

private noncomputable def factorRingEquiv (i : ι) : A i ≃+* B (blockEquiv f i) where
  toFun x := f (Pi.single i x) (blockEquiv f i)
  invFun y := f.symm (Pi.single (blockEquiv f i) y) i
  map_add' x y := by rw [Pi.single_add, map_add]; rfl
  map_mul' x y := by rw [Pi.single_mul, map_mul]; rfl
  left_inv x := by
    have h := congrFun (congrArg f.symm (map_single_eq_single f i x)) i
    rw [f.symm_apply_apply, Pi.single_eq_same] at h
    exact h.symm
  right_inv y := by
    have h := congrFun (congrArg f (symm_map_single_eq_single f i y)) (blockEquiv f i)
    rw [f.apply_symm_apply, Pi.single_eq_same] at h
    exact h.symm

/-- **A ring isomorphism between products of simple rings permutes their factors.**

The returned factor isomorphisms are restrictions of the original isomorphism: mapping an element
supported at `i` gives the corresponding element supported at `σ i`. The images of the coordinate
central idempotents determine `σ`, even when some factors are isomorphic. No finiteness assumption
on either index set is needed. -/
theorem exists_equiv_factors (f : (∀ i, A i) ≃+* (∀ j, B j)) :
    ∃ σ : ι ≃ κ, ∀ i, ∃ e : A i ≃+* B (σ i),
      ∀ x, f (Pi.single i x) = Pi.single (σ i) (e x) :=
  ⟨blockEquiv f, fun i ↦ ⟨factorRingEquiv f i, map_single_eq_single f i⟩⟩

end Products

/-- Two presentations of a ring as products of simple rings have equal `Nat.card` of their
index sets. In particular, two finite products have the same number of factors.

The index sets are in fact equivalent, by `RingEquiv.exists_equiv_factors`. -/
theorem card_eq_of_pi_of_isSimpleRing {R : Type*} [Ring R]
    {ι κ : Type*} {A : ι → Type*} {B : κ → Type*}
    [∀ i, Ring (A i)] [∀ i, IsSimpleRing (A i)]
    [∀ j, Ring (B j)] [∀ j, IsSimpleRing (B j)]
    (f : R ≃+* ∀ i, A i) (g : R ≃+* ∀ j, B j) : Nat.card ι = Nat.card κ := by
  classical
  obtain ⟨σ, -⟩ := (f.symm.trans g).exists_equiv_factors
  exact Nat.card_congr σ

/-- **Invariance of the block count.** Two presentations of the same ring as finite products of
positive-size matrix algebras over simple rings have the same number of blocks.

This applies in particular to two Wedderburn presentations. The `NeZero` hypotheses are essential:
a zero-size matrix algebra is trivial, so any presentation could be padded with empty blocks.
Semisimplicity of `R` guarantees a Wedderburn presentation exists, but is not needed here. -/
theorem card_blocks_eq {R : Type*} [Ring R] {m n : ℕ} {D : Fin m → Type*} {D' : Fin n → Type*}
    [∀ i, Ring (D i)] [∀ i, IsSimpleRing (D i)] [∀ i, Ring (D' i)] [∀ i, IsSimpleRing (D' i)]
    {d : Fin m → ℕ} {d' : Fin n → ℕ} [∀ i, NeZero (d i)] [∀ i, NeZero (d' i)]
    (f : R ≃+* ∀ i, Matrix (Fin (d i)) (Fin (d i)) (D i))
    (g : R ≃+* ∀ i, Matrix (Fin (d' i)) (Fin (d' i)) (D' i)) : m = n := by
  have : ∀ i, Nonempty (Fin (d i)) := fun i ↦ ⟨⟨0, NeZero.pos (d i)⟩⟩
  have : ∀ i, Nonempty (Fin (d' i)) := fun i ↦ ⟨⟨0, NeZero.pos (d' i)⟩⟩
  simpa using f.card_eq_of_pi_of_isSimpleRing g

end RingEquiv
