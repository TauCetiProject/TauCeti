/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.CentralIdempotent
public import Mathlib.RingTheory.SimpleRing.Defs
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Isomorphisms between products of simple rings

A ring isomorphism between arbitrary products of simple rings induces an equivalence of their
index sets and isomorphisms between the matched factors. The original isomorphism acts
coordinatewise through these factor isomorphisms, including on elements with infinite support.

A coordinate central idempotent `δᵢ` is primitive among central idempotents: the only central
idempotents `e` satisfying `e * δᵢ = e` are `0` and `δᵢ`. A ring isomorphism therefore carries
`δᵢ` to exactly one coordinate central idempotent. Applying the inverse isomorphism gives a
bijection of the indices. Multiplying an arbitrary product element by `δᵢ` then identifies its
image at the matched coordinate and gives the factor isomorphism. The central-idempotent dichotomy
used here is `TauCeti.centralIdempotents_eq_pair`.

No finiteness or semisimplicity hypothesis is needed. In particular, this applies to genuinely
infinite products. The matrix-block specialization for Wedderburn presentations is
`RingEquiv.card_blocks_eq` in `TauCeti/RingTheory/Semisimple/BlockCount.lean`.

## Main results

* `RingEquiv.exists_equiv_factors`: an isomorphism between products of simple rings acts
  coordinatewise through an equivalence of their index sets and matched factor isomorphisms.
* `RingEquiv.card_eq_of_pi_of_isSimpleRing`: two presentations of a ring as products of simple
  rings have equal `Nat.card` of their index sets.

## References

T. Y. Lam, *A First Course in Noncommutative Rings*, §3, or C. W. Curtis and I. Reiner,
*Representation Theory of Finite Groups and Associative Algebras*, §25.
-/

public section

namespace RingEquiv

open TauCeti

universe u v w x

section Products

variable {ι : Type u} {κ : Type v}
  {A : ι → Type w} {B : κ → Type x}
  [∀ i, Ring (A i)] [∀ i, IsSimpleRing (A i)]
  [∀ j, Ring (B j)] [∀ j, IsSimpleRing (B j)]

section

variable [DecidableEq ι] [DecidableEq κ]

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

end

/-- **A ring isomorphism between products of simple rings permutes their factors.**

The returned factor isomorphisms describe the original isomorphism coordinatewise: the value at
`σ i` of the image of any product element depends only on its value at `i`. The images of the
coordinate central idempotents determine `σ`, even when some factors are isomorphic. No finiteness
or decidable-equality assumption on either index set is needed. -/
theorem exists_equiv_factors (f : (∀ i, A i) ≃+* (∀ j, B j)) :
    ∃ σ : ι ≃ κ, ∀ i, ∃ e : A i ≃+* B (σ i), ∀ a, f a (σ i) = e (a i) := by
  classical
  refine ⟨blockEquiv f, fun i ↦ ⟨factorRingEquiv f i, fun a ↦ ?_⟩⟩
  have hmul : Pi.single i (1 : A i) * a = Pi.single i (a i) := by
    rw [← Pi.single_mul_left, one_mul]
  have h := congrFun (congrArg f hmul) (blockEquiv f i)
  -- Expose `factorRingEquiv`'s defining coordinate map through its `RingEquiv` coercion, so
  -- the following `simpa only` matches the target with the equality obtained from `hmul`.
  change f a (blockEquiv f i) = f (Pi.single i (a i)) (blockEquiv f i)
  simpa only [map_mul, image_single_one_blockEquiv, Pi.mul_apply, Pi.single_eq_same, one_mul]
    using h

end Products

/-- Two presentations of a ring as products of simple rings have equal `Nat.card` of their
index sets. In particular, two finite products have the same number of factors.

The index sets are in fact equivalent, by `RingEquiv.exists_equiv_factors`. -/
theorem card_eq_of_pi_of_isSimpleRing {R : Type*} [Ring R]
    {ι κ : Type*} {A : ι → Type*} {B : κ → Type*}
    [∀ i, Ring (A i)] [∀ i, IsSimpleRing (A i)]
    [∀ j, Ring (B j)] [∀ j, IsSimpleRing (B j)]
    (f : R ≃+* ∀ i, A i) (g : R ≃+* ∀ j, B j) : Nat.card ι = Nat.card κ := by
  obtain ⟨σ, -⟩ := (f.symm.trans g).exists_equiv_factors
  exact Nat.card_congr σ

end RingEquiv
