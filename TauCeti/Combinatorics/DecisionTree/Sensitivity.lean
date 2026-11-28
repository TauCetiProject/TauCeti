/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Finset.Piecewise
public import Mathlib.Order.Lattice.Nat
import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-!
# Certificates, sensitivity and block sensitivity

Let `f : (Fin n → Bool) → Bool` be a Boolean function on `n` variables. A set `S` of variables
is a certificate for `f` at the input `x` when every input that agrees with `x` on `S` has the
value `f x`. The certificate complexity `C(f)` is the largest, over all inputs, of the least size
of a certificate. The sensitivity `s(f)` is the largest, over all inputs `x`, of the number of
variables whose flip changes the value of `f` at `x`; the block sensitivity `bs(f)` is the same
with pairwise disjoint blocks of variables in place of single variables.

This file defines these measures and proves the chain `s(f) ≤ bs(f) ≤ C(f)`. The sensitive single
variables at `x` form disjoint sensitive blocks, and a certificate at `x` meets every sensitive
block at `x`, in distinct variables for disjoint blocks.

## Main definitions

* `TauCeti.flipBlock x B`: the input `x` with the variables of `B` negated.
* `TauCeti.IsCertificate f x S`: every input that agrees with `x` on `S` has the value `f x`.
* `TauCeti.certComplexityAt f x`: the least size of a certificate for `f` at `x`.
* `TauCeti.certComplexity f`: the certificate complexity `C(f)`.
* `TauCeti.certComplexityOn f b`: the largest certificate complexity at an input where `f` takes
  the value `b`.
* `TauCeti.sensitivityAt f x` and `TauCeti.sensitivity f`: the sensitivity at `x` and `s(f)`.
* `TauCeti.blockSensitivityAt f x` and `TauCeti.blockSensitivity f`: the block sensitivity at
  `x` and `bs(f)`.

## Main results

* `TauCeti.certComplexityAt_le_iff`: the certificate complexity at `x` is at most `k` exactly
  when some certificate at `x` has at most `k` variables.
* `TauCeti.certComplexity_eq_max`: `C(f)` is the larger of the certificate complexities on the
  inputs with value `false` and on the inputs with value `true`.
* `TauCeti.certComplexity_eq_zero_iff`: `C(f) = 0` exactly when `f` is constant.
* `TauCeti.sensitivity_le_blockSensitivity`: `s(f) ≤ bs(f)`.
* `TauCeti.blockSensitivity_le_certComplexity`: `bs(f) ≤ C(f)`.

## References

* Harry Buhrman and Ronald de Wolf, *Complexity measures and decision tree complexity: a
  survey*, Theoretical Computer Science 288 (2002), 21–43, Definitions 1 and 2 and
  Proposition 1.
-/

public section

open Finset

namespace TauCeti

variable {n : ℕ}

/-! ### Flipping a block of variables -/

/-- The input `x` with the variables of the block `B` negated. -/
def flipBlock (x : Fin n → Bool) (B : Finset (Fin n)) : Fin n → Bool :=
  fun i => if i ∈ B then !x i else x i

/-- The value of `flipBlock x B` at a variable `i`. -/
theorem flipBlock_apply (x : Fin n → Bool) (B : Finset (Fin n)) (i : Fin n) :
    flipBlock x B i = if i ∈ B then !x i else x i := by
  rw [flipBlock]

/-- Flipping a block is the piecewise function that negates `x` on the block and keeps `x`
outside it. -/
theorem flipBlock_eq_piecewise (x : Fin n → Bool) (B : Finset (Fin n)) :
    flipBlock x B = B.piecewise (fun i => !x i) x := by
  ext i
  rw [flipBlock_apply, piecewise]

/-- Flipping a block negates the variables of the block. -/
@[simp]
theorem flipBlock_apply_of_mem {x : Fin n → Bool} {B : Finset (Fin n)} {i : Fin n}
    (hi : i ∈ B) : flipBlock x B i = !x i := by
  rw [flipBlock_eq_piecewise, piecewise_eq_of_mem _ _ _ hi]

/-- Flipping a block does not change the variables outside the block. -/
@[simp]
theorem flipBlock_apply_of_notMem {x : Fin n → Bool} {B : Finset (Fin n)} {i : Fin n}
    (hi : i ∉ B) : flipBlock x B i = x i := by
  rw [flipBlock_eq_piecewise, piecewise_eq_of_notMem _ _ _ hi]

/-- Flipping the empty block does not change the input. -/
@[simp]
theorem flipBlock_empty (x : Fin n → Bool) : flipBlock x ∅ = x := by
  ext i
  simp

/-! ### Certificates and certificate complexity -/

/-- A set `S` of variables is a certificate for `f` at `x` when every input that agrees with `x`
on `S` has the value `f x`. -/
def IsCertificate (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) (S : Finset (Fin n)) : Prop :=
  ∀ y : Fin n → Bool, (∀ i ∈ S, y i = x i) → f y = f x

/-- The defining property of a certificate. -/
theorem isCertificate_iff {f : (Fin n → Bool) → Bool} {x : Fin n → Bool} {S : Finset (Fin n)} :
    IsCertificate f x S ↔ ∀ y : Fin n → Bool, (∀ i ∈ S, y i = x i) → f y = f x := by
  rw [IsCertificate]

variable {f : (Fin n → Bool) → Bool} {x : Fin n → Bool} {S T : Finset (Fin n)}

/-- An input that agrees on a certificate at `x` with `x` has the value `f x`. -/
theorem IsCertificate.apply_eq (hS : IsCertificate f x S) {y : Fin n → Bool}
    (hy : ∀ i ∈ S, y i = x i) : f y = f x :=
  isCertificate_iff.1 hS y hy

/-- A set of variables that contains a certificate is a certificate. -/
theorem IsCertificate.mono (hS : IsCertificate f x S) (hST : S ⊆ T) : IsCertificate f x T :=
  isCertificate_iff.2 fun _ hy => hS.apply_eq fun i hi => hy i (hST hi)

/-- The set of all variables is a certificate at every input. -/
theorem isCertificate_univ (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) :
    IsCertificate f x univ :=
  isCertificate_iff.2 fun y hy => by rw [show y = x from funext fun i => hy i (mem_univ i)]

/-- The empty set is a certificate at `x` exactly when every input has the value `f x`. -/
theorem isCertificate_empty_iff : IsCertificate f x ∅ ↔ ∀ y, f y = f x := by
  simp [isCertificate_iff]

/-- A certificate at `x` meets every block whose flip changes the value of `f` at `x`. -/
theorem IsCertificate.inter_nonempty (hS : IsCertificate f x S) {B : Finset (Fin n)}
    (hB : f (flipBlock x B) ≠ f x) : (S ∩ B).Nonempty := by
  rw [← not_disjoint_iff_nonempty_inter]
  exact fun hSB => hB (hS.apply_eq fun i hi => flipBlock_apply_of_notMem (disjoint_left.1 hSB hi))

variable (f x) in
/-- The certificate complexity of `f` at `x`: the least size of a certificate for `f` at `x`. -/
noncomputable def certComplexityAt : ℕ :=
  sInf (card '' {S | IsCertificate f x S})

variable (f x) in
/-- Some certificate at `x` has exactly `certComplexityAt f x` variables. -/
theorem exists_isCertificate_card_eq :
    ∃ S, IsCertificate f x S ∧ #S = certComplexityAt f x := by
  rw [certComplexityAt]
  exact Nat.sInf_mem (s := card '' {S | IsCertificate f x S}) ⟨_, univ, isCertificate_univ f x, rfl⟩

/-- The certificate complexity at `x` is at most the size of each certificate at `x`. -/
theorem IsCertificate.certComplexityAt_le (hS : IsCertificate f x S) :
    certComplexityAt f x ≤ #S := by
  rw [certComplexityAt]
  exact Nat.sInf_le ⟨S, hS, rfl⟩

/-- The certificate complexity at `x` is at most `k` exactly when some certificate at `x` has at
most `k` variables. -/
theorem certComplexityAt_le_iff {k : ℕ} :
    certComplexityAt f x ≤ k ↔ ∃ S, IsCertificate f x S ∧ #S ≤ k := by
  refine ⟨fun h => ?_, fun ⟨S, hS, hk⟩ => hS.certComplexityAt_le.trans hk⟩
  obtain ⟨S, hS, hcard⟩ := exists_isCertificate_card_eq f x
  exact ⟨S, hS, hcard.trans_le h⟩

variable (f x) in
/-- The certificate complexity at an input is at most the number `n` of variables. -/
theorem certComplexityAt_le : certComplexityAt f x ≤ n :=
  (isCertificate_univ f x).certComplexityAt_le.trans_eq (card_fin n)

/-- The certificate complexity at `x` is `0` exactly when every input has the value `f x`. -/
theorem certComplexityAt_eq_zero_iff : certComplexityAt f x = 0 ↔ ∀ y, f y = f x := by
  rw [← Nat.le_zero, certComplexityAt_le_iff]
  simp [isCertificate_empty_iff]

variable (f) in
/-- The certificate complexity `C(f)`: the largest certificate complexity at an input. -/
noncomputable def certComplexity : ℕ :=
  univ.sup (certComplexityAt f)

variable (f x) in
/-- The certificate complexity at an input is at most `C(f)`. -/
theorem certComplexityAt_le_certComplexity : certComplexityAt f x ≤ certComplexity f := by
  rw [certComplexity]
  exact le_sup (mem_univ x)

/-- `C(f) ≤ k` exactly when the certificate complexity at every input is at most `k`. -/
theorem certComplexity_le_iff {k : ℕ} :
    certComplexity f ≤ k ↔ ∀ x, certComplexityAt f x ≤ k := by
  simp [certComplexity]

variable (f) in
/-- The certificate complexity of a Boolean function on `n` variables is at most `n`. -/
theorem certComplexity_le : certComplexity f ≤ n :=
  certComplexity_le_iff.2 (certComplexityAt_le f)

/-- The certificate complexity of a Boolean function is `0` exactly when the function is
constant. -/
theorem certComplexity_eq_zero_iff : certComplexity f = 0 ↔ ∃ b, f = fun _ => b := by
  rw [← Nat.le_zero, certComplexity_le_iff]
  simp only [Nat.le_zero, certComplexityAt_eq_zero_iff]
  refine ⟨fun h => ⟨f fun _ => false, funext fun y => h _ y⟩, ?_⟩
  rintro ⟨b, rfl⟩ _ _
  rfl

/-- A constant Boolean function has certificate complexity `0`. -/
@[simp]
theorem certComplexity_const (b : Bool) : certComplexity (fun _ : Fin n → Bool => b) = 0 :=
  certComplexity_eq_zero_iff.2 ⟨b, rfl⟩

variable (f) in
/-- The `b`-certificate complexity `C^(b)(f)`: the largest certificate complexity at an input
where `f` takes the value `b`, and `0` when there is no such input. -/
noncomputable def certComplexityOn (b : Bool) : ℕ :=
  ({x | f x = b} : Finset (Fin n → Bool)).sup (certComplexityAt f)

/-- The certificate complexity at an input where `f` takes the value `b` is at most
`C^(b)(f)`. -/
theorem certComplexityAt_le_certComplexityOn {b : Bool} (hx : f x = b) :
    certComplexityAt f x ≤ certComplexityOn f b := by
  rw [certComplexityOn]
  exact le_sup (mem_filter.2 ⟨mem_univ x, hx⟩)

/-- `C^(b)(f) ≤ k` exactly when the certificate complexity at every input where `f` takes the
value `b` is at most `k`. -/
theorem certComplexityOn_le_iff {b : Bool} {k : ℕ} :
    certComplexityOn f b ≤ k ↔ ∀ x, f x = b → certComplexityAt f x ≤ k := by
  simp [certComplexityOn]

variable (f) in
/-- `C(f)` is the larger of `C^(0)(f)` and `C^(1)(f)`, since every input has one of the two
values. -/
theorem certComplexity_eq_max :
    certComplexity f = max (certComplexityOn f false) (certComplexityOn f true) := by
  refine le_antisymm (certComplexity_le_iff.2 fun x => ?_) (max_le ?_ ?_)
  · cases hx : f x
    · exact (certComplexityAt_le_certComplexityOn hx).trans (le_max_left _ _)
    · exact (certComplexityAt_le_certComplexityOn hx).trans (le_max_right _ _)
  all_goals exact certComplexityOn_le_iff.2 fun x _ => certComplexityAt_le_certComplexity f x

/-! ### Sensitivity and block sensitivity -/

variable (f x) in
/-- The sensitivity of `f` at `x`: the number of variables whose flip changes the value of `f`
at `x`. -/
def sensitivityAt : ℕ :=
  #{i | f (flipBlock x {i}) ≠ f x}

/-- The sensitivity at `x` is the number of variables whose flip changes the value of `f` at
`x`. -/
theorem sensitivityAt_eq_card : sensitivityAt f x = #{i | f (flipBlock x {i}) ≠ f x} := by
  rw [sensitivityAt]

variable (f) in
/-- The sensitivity `s(f)`: the largest sensitivity at an input. -/
def sensitivity : ℕ :=
  univ.sup (sensitivityAt f)

variable (f x) in
/-- The sensitivity at an input is at most `s(f)`. -/
theorem sensitivityAt_le_sensitivity : sensitivityAt f x ≤ sensitivity f := by
  rw [sensitivity]
  exact le_sup (mem_univ x)

/-- `s(f) ≤ k` exactly when the sensitivity at every input is at most `k`. -/
theorem sensitivity_le_iff {k : ℕ} : sensitivity f ≤ k ↔ ∀ x, sensitivityAt f x ≤ k := by
  simp [sensitivity]

open Classical in
variable (f x) in
/-- The block sensitivity of `f` at `x`: the largest number of pairwise disjoint blocks of
variables whose flip changes the value of `f` at `x`. -/
noncomputable def blockSensitivityAt : ℕ :=
  ({𝓑 | (𝓑 : Set (Finset (Fin n))).PairwiseDisjoint id ∧ ∀ B ∈ 𝓑, f (flipBlock x B) ≠ f x} :
    Finset (Finset (Finset (Fin n)))).sup card

/-- A family of pairwise disjoint blocks whose flips change the value of `f` at `x` has at most
`blockSensitivityAt f x` members. -/
theorem card_le_blockSensitivityAt {𝓑 : Finset (Finset (Fin n))}
    (h𝓑 : (𝓑 : Set (Finset (Fin n))).PairwiseDisjoint id)
    (hf : ∀ B ∈ 𝓑, f (flipBlock x B) ≠ f x) : #𝓑 ≤ blockSensitivityAt f x := by
  rw [blockSensitivityAt]
  refine le_sup (f := card) ?_
  simp only [mem_filter, mem_univ, true_and]
  exact ⟨h𝓑, hf⟩

/-- The block sensitivity at `x` is at most `k` exactly when every family of pairwise disjoint
blocks whose flips change the value of `f` at `x` has at most `k` members. -/
theorem blockSensitivityAt_le_iff {k : ℕ} :
    blockSensitivityAt f x ≤ k ↔ ∀ 𝓑 : Finset (Finset (Fin n)),
      (𝓑 : Set (Finset (Fin n))).PairwiseDisjoint id →
        (∀ B ∈ 𝓑, f (flipBlock x B) ≠ f x) → #𝓑 ≤ k := by
  simp [blockSensitivityAt]

variable (f x) in
/-- Some family of pairwise disjoint blocks whose flips change the value of `f` at `x` has
exactly `blockSensitivityAt f x` members. -/
theorem exists_card_eq_blockSensitivityAt :
    ∃ 𝓑 : Finset (Finset (Fin n)), (𝓑 : Set (Finset (Fin n))).PairwiseDisjoint id ∧
      (∀ B ∈ 𝓑, f (flipBlock x B) ≠ f x) ∧ #𝓑 = blockSensitivityAt f x := by
  classical
  rw [blockSensitivityAt]
  obtain ⟨𝓑, h𝓑, hcard⟩ := exists_mem_eq_sup
    ({𝓑 | (𝓑 : Set (Finset (Fin n))).PairwiseDisjoint id ∧ ∀ B ∈ 𝓑, f (flipBlock x B) ≠ f x} :
      Finset (Finset (Finset (Fin n)))) ⟨∅, by simp⟩ card
  obtain ⟨-, h𝓑, hf⟩ := mem_filter.1 h𝓑
  exact ⟨𝓑, h𝓑, hf, hcard.symm⟩

variable (f) in
/-- The block sensitivity `bs(f)`: the largest block sensitivity at an input. -/
noncomputable def blockSensitivity : ℕ :=
  univ.sup (blockSensitivityAt f)

variable (f x) in
/-- The block sensitivity at an input is at most `bs(f)`. -/
theorem blockSensitivityAt_le_blockSensitivity :
    blockSensitivityAt f x ≤ blockSensitivity f := by
  rw [blockSensitivity]
  exact le_sup (mem_univ x)

/-- `bs(f) ≤ k` exactly when the block sensitivity at every input is at most `k`. -/
theorem blockSensitivity_le_iff {k : ℕ} :
    blockSensitivity f ≤ k ↔ ∀ x, blockSensitivityAt f x ≤ k := by
  simp [blockSensitivity]

/-! ### The chain `s(f) ≤ bs(f) ≤ C(f)` -/

variable (f x) in
/-- The sensitivity at `x` is at most the block sensitivity at `x`. -/
theorem sensitivityAt_le_blockSensitivityAt : sensitivityAt f x ≤ blockSensitivityAt f x := by
  rw [sensitivityAt_eq_card, ← card_map ⟨singleton, singleton_injective⟩]
  refine card_le_blockSensitivityAt ?_ ?_
  · intro B hB C hC hBC
    simp only [coe_map, Set.mem_image, mem_coe] at hB hC
    obtain ⟨i, -, rfl⟩ := hB
    obtain ⟨j, -, rfl⟩ := hC
    exact disjoint_singleton.2 fun hij => hBC (by simp [hij])
  · simp

variable (f x) in
/-- The block sensitivity at `x` is at most the certificate complexity at `x`. -/
theorem blockSensitivityAt_le_certComplexityAt :
    blockSensitivityAt f x ≤ certComplexityAt f x := by
  obtain ⟨S, hS, hcard⟩ := exists_isCertificate_card_eq f x
  refine blockSensitivityAt_le_iff.2 fun 𝓑 h𝓑 hf => hcard ▸ ?_
  refine card_le_card_of_forall_subsingleton (fun B i => i ∈ B)
    (fun B hB => (hS.inter_nonempty (hf B hB)).imp fun i hi => mem_inter.1 hi) ?_
  rintro i - B ⟨hB, hiB⟩ C ⟨hC, hiC⟩
  by_contra hBC
  exact disjoint_left.1 (h𝓑 hB hC hBC) hiB hiC

variable (f) in
/-- Sensitivity is at most block sensitivity: `s(f) ≤ bs(f)`. -/
theorem sensitivity_le_blockSensitivity : sensitivity f ≤ blockSensitivity f :=
  sensitivity_le_iff.2 fun x =>
    (sensitivityAt_le_blockSensitivityAt f x).trans (blockSensitivityAt_le_blockSensitivity f x)

variable (f) in
/-- Block sensitivity is at most certificate complexity: `bs(f) ≤ C(f)`. -/
theorem blockSensitivity_le_certComplexity : blockSensitivity f ≤ certComplexity f :=
  blockSensitivity_le_iff.2 fun x =>
    (blockSensitivityAt_le_certComplexityAt f x).trans (certComplexityAt_le_certComplexity f x)

variable (f) in
/-- The block sensitivity of a Boolean function on `n` variables is at most `n`: at most `n`
pairwise disjoint blocks are sensitive at an input. -/
theorem blockSensitivity_le : blockSensitivity f ≤ n :=
  (blockSensitivity_le_certComplexity f).trans (certComplexity_le f)

/-- A constant Boolean function has block sensitivity `0`. -/
@[simp]
theorem blockSensitivity_const (b : Bool) : blockSensitivity (fun _ : Fin n → Bool => b) = 0 :=
  Nat.le_zero.1 ((blockSensitivity_le_certComplexity _).trans_eq (certComplexity_const b))

/-- A constant Boolean function has sensitivity `0`. -/
@[simp]
theorem sensitivity_const (b : Bool) : sensitivity (fun _ : Fin n → Bool => b) = 0 :=
  Nat.le_zero.1 ((sensitivity_le_blockSensitivity _).trans_eq (blockSensitivity_const b))

end TauCeti
