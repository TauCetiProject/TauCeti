/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorCoalgebra.Basic

/-!
# Primitive elements of the reduced tensor coalgebra

For an `R`-module `M`, the reduced tensor words `⨁_{n ≥ 1} M^{⊗n}` carry the reduced
deconcatenation coproduct `Δ` built in `TauCeti.ReducedTensorWords.deconcatenation`.  This file
computes its primitive elements: a tensor word killed by deconcatenation is a single letter.

Indeed the `(1, n - 1)` bidegree part of `Δ` on a word of length `n` is the cut after its first
letter, and cutting is injective, so no component of length at least two can survive.

## Main definitions

* `TauCeti.ReducedTensorWords.letter`, `TauCeti.ReducedTensorWords.ofLetter`: the length-one
  component of a tensor word, and a single letter viewed as a tensor word.

## Main results

* `TauCeti.ReducedTensorWords.subword_one`: a block of length one is a single letter.
* `TauCeti.ReducedTensorWords.deconcatenation_prepend`: the cuts of a prepended word.
* `TauCeti.ReducedTensorWords.prepend_ofLetter` and
  `TauCeti.ReducedTensorWords.deconcatenation_of_two`: the two-letter word and its only cut.
* `TauCeti.ReducedTensorWords.map_letter_letter_deconcatenation_of_ne_two`: `letter ⊗ letter`
  annihilates the deconcatenation of any pure word of length other than two.
* `TauCeti.ReducedTensorWords.eq_zero_of_factor_letter_pair`: any linear map factoring through
  `(f ∘ₗ letter) ⊗ (g ∘ₗ letter) ∘ₗ deconcatenation` vanishes on pure words of length other than
  two.
* `TauCeti.ReducedTensorWords.letter_comp_map`: the letter of a letterwise-mapped word is the
  image of its letter.
* `TauCeti.ReducedTensorWords.deconcatenation_eq_zero_iff`: the primitives of the reduced tensor
  coalgebra are exactly the single letters.

## References

* E. Getzler and J. D. S. Jones, *A-infinity algebras and the cyclic bar complex*, Sections 1--2.
* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.1 and 3.6.
-/

public section

open scoped BigOperators DirectSum TensorProduct

universe uR uM uN

namespace TauCeti

namespace ReducedTensorWords

section Semiring

variable (R : Type uR) (M : Type uM) [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- The letter of a reduced tensor word: its length-one component, read as an element of `M`. -/
noncomputable def letter : ReducedTensorWords R M →ₗ[R] M :=
  (TensorPower.oneEquiv R M).toLinearMap ∘ₗ component R M 1

/-- A single letter, viewed as a reduced tensor word of length one. -/
noncomputable def ofLetter : M →ₗ[R] ReducedTensorWords R M :=
  of R M 1 ∘ₗ (TensorPower.oneEquiv R M).symm.toLinearMap

/-- A single letter is the pure tensor word of length one on that letter. -/
theorem ofLetter_eq_of_tprod (a : M) :
    ofLetter R M a = of R M 1 (PiTensorProduct.tprod R fun _ ↦ a) := by
  rw [ofLetter, LinearMap.comp_apply, LinearEquiv.coe_coe, TensorPower.oneEquiv_symm_apply]
  rfl

/-- A pure tensor word of length one equals the single letter at index `0`. -/
theorem of_one_tprod {hn : 0 < 1} (x : Fin 1 → M) :
    of R M ⟨1, hn⟩ (PiTensorProduct.tprod R x) = ofLetter R M (x 0) := by
  rw [ofLetter_eq_of_tprod]
  exact of_tprod_congr R M hn rfl <| Fin.forall_fin_one.2 rfl

/-- The length-one component of a single letter is that letter under the tensor-power
identification. -/
theorem component_ofLetter (a : M) :
    component R M 1 (ofLetter R M a) = (TensorPower.oneEquiv R M).symm a := by
  rw [ofLetter, LinearMap.comp_apply, component_of, LinearEquiv.coe_coe]

/-- Every component of a single letter away from length one vanishes. -/
@[simp]
theorem component_ofLetter_of_ne {n : {n : ℕ // 0 < n}} (hn : n ≠ 1) (a : M) :
    component R M n (ofLetter R M a) = 0 := by
  rw [ofLetter, LinearMap.comp_apply, component_of_of_ne R M hn.symm]

/-- The letter of a tensor word is its length-one component, read through the length-one
identification. -/
theorem letter_apply (x : ReducedTensorWords R M) :
    letter R M x = TensorPower.oneEquiv R M (component R M 1 x) :=
  (rfl)

/-- Reading off the letter of a single letter returns it. -/
@[simp]
theorem letter_ofLetter (a : M) : letter R M (ofLetter R M a) = a := by
  rw [letter_apply, ofLetter, LinearMap.comp_apply, component_of, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]

/-- A single letter has no nontrivial cut. -/
@[simp]
theorem deconcatenation_ofLetter (a : M) : deconcatenation R M (ofLetter R M a) = 0 := by
  rw [ofLetter, LinearMap.comp_apply]
  exact deconcatenation_of_length_one R M _

/-- The `(1, n - 1)` bidegree part of reduced deconcatenation, evaluated on a pure tensor word of
length `m`: only the cut after the first letter can contribute, and it does so exactly when
`m = n`. -/
private theorem map_component_deconcatenation_tprod (n m : {n : ℕ // 0 < n}) (hn : 2 ≤ n.val)
    (x : Fin m.val → M) :
    TensorProduct.map (component R M 1) (component R M ⟨n.val - 1, by omega⟩)
        (deconcatenation R M (of R M m (PiTensorProduct.tprod R x))) =
      TensorPower.splitAt R M n.val 1 (by omega)
        (component R M n (of R M m (PiTensorProduct.tprod R x))) := by
  rw [deconcatenation_of, deconcatenationComponent_tprod]
  simp only [map_sum, TensorProduct.map_tmul]
  rcases eq_or_ne m n with rfl | hmn
  · rw [component_of, TensorPower.splitAt_tprod,
      Finset.sum_eq_single (⟨0, by omega⟩ : Fin (m.val - 1))]
    · simp only [Fin.val_mk, Nat.zero_add]
      erw [component_of, component_of]
    · intro i _ hi
      have hi0 : i.val ≠ 0 := fun h ↦ hi (Fin.ext h)
      rw [component_of_of_ne R M
        (by simp only [ne_eq, Subtype.ext_iff, Positive.val_one]; omega),
        TensorProduct.zero_tmul]
    · intro hi
      exact absurd (Finset.mem_univ _) hi
  · rw [component_of_of_ne R M hmn, map_zero]
    have hmn' : (m : ℕ) ≠ (n : ℕ) := fun h ↦ hmn (Subtype.ext h)
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    have hi1 : i.val + 1 < (m : ℕ) := by have := i.isLt; omega
    rcases eq_or_ne i.val 0 with hi | hi
    · have h2 := component_of_of_ne R M
        (m := (⟨(m : ℕ) - (i.val + 1), by omega⟩ : {n : ℕ // 0 < n}))
        (n := (⟨(n : ℕ) - 1, by omega⟩ : {n : ℕ // 0 < n}))
        (by simp only [ne_eq, Subtype.mk.injEq]; omega)
      rw [h2, TensorProduct.tmul_zero]
    · have h1 := component_of_of_ne R M
        (m := (⟨i.val + 1, by omega⟩ : {n : ℕ // 0 < n})) (n := 1)
        (by simp only [ne_eq, Subtype.ext_iff, Positive.val_one]; omega)
      rw [h1, TensorProduct.zero_tmul]

/-- Reading off the `(1, n - 1)` bidegree part of reduced deconcatenation recovers the cut of a
word of length `n` after its first letter. -/
theorem map_component_deconcatenation (n : {n : ℕ // 0 < n}) (hn : 2 ≤ n.val) :
    TensorProduct.map (component R M 1) (component R M ⟨n.val - 1, by omega⟩) ∘ₗ
        deconcatenation R M =
      TensorPower.splitAt R M n.val 1 (by omega) ∘ₗ component R M n := by
  refine linearMap_ext R M fun m x ↦ ?_
  simp only [LinearMap.comp_apply]
  exact map_component_deconcatenation_tprod R M n m hn x

/-- A reduced tensor word is determined by its deconcatenation together with its letter: the
components of length at least two are read off from the cut after the first letter, and the
length-one component is the letter. -/
theorem eq_of_deconcatenation_eq_of_letter_eq {x y : ReducedTensorWords R M}
    (hd : deconcatenation R M x = deconcatenation R M y) (hl : letter R M x = letter R M y) :
    x = y := by
  apply DirectSum.ext_component R
  intro n
  rw [← DirectSum.apply_eq_component R x n, ← DirectSum.apply_eq_component R y n]
  rw [apply_eq_component R M x n, apply_eq_component R M y n]
  rcases eq_or_ne n 1 with rfl | hn
  · have h := congrArg (TensorPower.oneEquiv R M).symm hl
    rwa [letter_apply, letter_apply, LinearEquiv.symm_apply_apply,
      LinearEquiv.symm_apply_apply] at h
  · have h2 : 2 ≤ n.val := by
      rcases Nat.lt_or_ge n.val 2 with h | h
      · exact absurd (Subtype.ext (by omega : n.val = 1)) hn
      · exact h
    refine TensorPower.splitAt_injective R M n.val 1 (by omega) ?_
    have hx := congrArg (fun f ↦ f x) (map_component_deconcatenation R M n h2)
    have hy := congrArg (fun f ↦ f y) (map_component_deconcatenation R M n h2)
    simp only [LinearMap.comp_apply] at hx hy
    rw [← hx, ← hy, hd]

/-- A block of length one is the corresponding single letter. -/
theorem subword_one {n : ℕ} (z : Fin n → M) {a : ℕ} (ha : a < n) :
    subword R z a 1 = ofLetter R M (z ⟨a, ha⟩) := by
  refine eq_of_deconcatenation_eq_of_letter_eq R M ?_ ?_
  · rw [deconcatenation_subword, deconcatenation_ofLetter]
    exact Finset.sum_eq_zero fun c hc ↦ by simp only [Finset.mem_Ioo] at hc; omega
  · rw [letter_ofLetter, letter_apply, subword_eq_of_tprod R z Nat.one_pos (by omega),
      component_of_eq R M (m := ⟨1, Nat.one_pos⟩) (n := 1) (Subtype.ext rfl),
      TensorPower.cast_refl, LinearEquiv.refl_apply, TauCeti.TensorPower.oneEquiv_tprod]
    exact congrArg z (Fin.ext (Nat.add_zero a))

/-- A block whose length is not one has no letter component. -/
theorem letter_subword_of_ne_one {n : ℕ} (z : Fin n → M) (a : ℕ) {b : ℕ} (hb : b ≠ 1) :
    letter R M (subword R z a b) = 0 := by
  rcases Nat.eq_zero_or_pos b with rfl | hb0
  · rw [subword_length_zero, map_zero]
  by_cases hab : a + b ≤ n
  · rw [letter_apply, subword_eq_of_tprod R z hb0 hab,
      component_of_of_ne R M (by simp only [ne_eq, Subtype.ext_iff, Positive.val_one]; omega),
      map_zero]
  · rw [subword_eq_zero_of_lt_add R z (by omega), map_zero]

/-- The letter of a word of length `n` is its only letter if `n = 1`, and zero otherwise. -/
theorem letter_of_tprod {n : ℕ} (hn : 0 < n) (z : ℕ → M) :
    letter R M (of R M ⟨n, hn⟩ (PiTensorProduct.tprod R fun i : Fin n ↦ z i)) =
      if n = 1 then z 0 else 0 := by
  rw [of_tprod_eq_subword R hn]
  split_ifs with h
  · subst h
    rw [subword_one R M _ Nat.one_pos, letter_ofLetter]
  · exact letter_subword_of_ne_one R M _ 0 h

/-- Applying `letter ⊗ letter` to the deconcatenation of a pure word of length other than two gives
zero, because every nontrivial cut leaves a factor of length at least two. -/
theorem map_letter_letter_deconcatenation_of_ne_two (n : {n : ℕ // 0 < n}) (hn : n.val ≠ 2)
    (x : Fin n.val → M) :
    TensorProduct.map (letter R M) (letter R M)
      (deconcatenation R M (of R M n (PiTensorProduct.tprod R x))) = 0 := by
  have hn0 : 0 < n.val := n.property
  rw [of_tprod_eq_subword R hn0, deconcatenation_subword, map_sum]
  refine Finset.sum_eq_zero fun d hd ↦ ?_
  rw [Finset.mem_Ioo] at hd
  rw [TensorProduct.map_tmul]
  by_cases hd1 : d = 1
  · rw [zero_add, letter_subword_of_ne_one R M x d (by omega), TensorProduct.tmul_zero]
  · rw [letter_subword_of_ne_one R M x 0 hd1, TensorProduct.zero_tmul]

/-- Any linear map factoring through `(letter ⊗ letter) ∘ deconcatenation` vanishes on pure words
of length other than two. -/
theorem eq_zero_of_factor_letter_pair {P Q N : Type*}
    [AddCommMonoid P] [Module R P] [AddCommMonoid Q] [Module R Q]
    [AddCommMonoid N] [Module R N]
    {h : ReducedTensorWords R M →ₗ[R] N} (F : P ⊗[R] Q →ₗ[R] N)
    (f : M →ₗ[R] P) (g : M →ₗ[R] Q)
    (hfac : h = F ∘ₗ TensorProduct.map (f ∘ₗ letter R M) (g ∘ₗ letter R M) ∘ₗ
      deconcatenation R M)
    (n : {n : ℕ // 0 < n}) (hn : n.val ≠ 2) (x : Fin n.val → M) :
    h (of R M n (PiTensorProduct.tprod R x)) = 0 := by
  rw [hfac, LinearMap.comp_apply, LinearMap.comp_apply, TensorProduct.map_comp,
    LinearMap.comp_apply, map_letter_letter_deconcatenation_of_ne_two R M n hn x,
    map_zero, map_zero]

section Prepend

variable {R M}

/-- A prepended word has length at least two, so it has no letter component. -/
@[simp]
theorem letter_prepend (a : M) (w : ReducedTensorWords R M) : letter R M (prepend R M a w) = 0 := by
  have h : letter R M ∘ₗ prepend R M a = 0 := by
    refine linearMap_ext R M fun k y ↦ ?_
    rw [LinearMap.comp_apply, prepend_of_tprod, letter_apply,
      component_of_of_ne R M (by simp only [ne_eq, Subtype.ext_iff, Positive.val_one]; omega),
      map_zero, LinearMap.zero_apply]
  exact LinearMap.congr_fun h w

/-- Cutting a prepended word `a · w` either separates the new letter from `w`, or cuts `w` and
prepends `a` to the left half. -/
theorem deconcatenation_prepend (a : M) (w : ReducedTensorWords R M) :
    deconcatenation R M (prepend R M a w) =
      ofLetter R M a ⊗ₜ[R] w +
        LinearMap.rTensor (ReducedTensorWords R M) (prepend R M a) (deconcatenation R M w) := by
  have h : deconcatenation R M ∘ₗ prepend R M a =
      (TensorProduct.mk R _ _ (ofLetter R M a)) +
        LinearMap.rTensor (ReducedTensorWords R M) (prepend R M a) ∘ₗ deconcatenation R M := by
    refine linearMap_ext R M fun k y ↦ ?_
    obtain ⟨k, hk⟩ := k
    -- Read `a · y` as the whole of the tuple `z = a y`, and `y` as its block after position `0`.
    set z : Fin (k + 1) → M := Fin.cons a y with hz
    have hw : of R M ⟨k, hk⟩ (PiTensorProduct.tprod R y) = subword R z 1 k := by
      rw [subword_eq_of_tprod R z hk (by omega)]
      exact of_tprod_congr R M _ rfl fun i ↦ by
        simp only [hz, Fin.cast_eq_self]
        exact (Fin.cons_succ (α := fun _ ↦ M) a y i).symm.trans
          (congrArg (Fin.cons a y) (Fin.ext ((Fin.val_succ i).trans (Nat.add_comm _ _))))
    have ha : z ⟨0, Nat.succ_pos k⟩ = a := Fin.cons_zero _ _
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.add_apply,
      TensorProduct.mk_apply]
    rw [hw, ← ha, prepend_subword z (Nat.succ_pos _) hk, deconcatenation_subword,
      deconcatenation_subword, map_sum,
      sum_Ioo_eq_sum_range _ _ (by rw [subword_length_zero, TensorProduct.zero_tmul]),
      sum_Ioo_eq_sum_range _ _ (by rw [subword_length_zero, TensorProduct.zero_tmul, map_zero]),
      Finset.sum_range_succ', Finset.sum_range_succ', Finset.sum_range_succ']
    simp only [subword_length_zero, TensorProduct.zero_tmul, map_zero, add_zero]
    rw [subword_one R M z (Nat.succ_pos _), add_comm]
    congr 1
    · refine Finset.sum_congr rfl fun c _ ↦ ?_
      rw [LinearMap.rTensor_tmul, prepend_subword z (Nat.succ_pos _) (Nat.succ_pos c)]
      exact congrArg _ (congrArg₂ (subword R z) (by omega) (by omega))
  simpa only [LinearMap.coe_comp, Function.comp_apply, LinearMap.add_apply,
    TensorProduct.mk_apply] using LinearMap.congr_fun h w

/-- Prepending a letter to a single letter is the two-letter word. -/
theorem prepend_ofLetter (a b : M) :
    prepend R M a (ofLetter R M b) =
      of R M (2 : ℕ+) (PiTensorProduct.tprod R ![a, b]) := by
  have hz0 : (![a, b] : Fin 2 → M) ⟨0, by omega⟩ = a := by simp
  have hz1 : (![a, b] : Fin 2 → M) ⟨1, by omega⟩ = b := by simp
  have h1 : subword R (![a, b] : Fin 2 → M) 1 1 = ofLetter R M b := by
    rw [subword_one R M (![a, b] : Fin 2 → M) (by omega), hz1]
  have h2 := prepend_subword (R := R) (N := M) (a := 0) (b := 1) (![a, b] : Fin 2 → M)
    (by omega) Nat.one_pos
  rw [hz0, h1] at h2
  rw [h2]
  exact (of_tprod_eq_subword R (Nat.succ_pos 1) (![a, b] : Fin 2 → M)).symm

/-- The only cut of a two-letter word separates its two letters. -/
theorem deconcatenation_of_two (a b : M) :
    deconcatenation R M (of R M (2 : ℕ+) (PiTensorProduct.tprod R ![a, b])) =
      ofLetter R M a ⊗ₜ[R] ofLetter R M b := by
  rw [← prepend_ofLetter, deconcatenation_prepend, deconcatenation_ofLetter, map_zero, add_zero]

/-- A two-letter word has no letter component. -/
@[simp]
theorem letter_of_two (a b : M) :
    letter R M (of R M (2 : ℕ+) (PiTensorProduct.tprod R ![a, b])) = 0 := by
  rw [← prepend_ofLetter, letter_prepend]

/-- Two linear maps out of `ReducedTensorWords R M` agree if they agree on single letters and on
prepended words. -/
theorem linearMap_ext_ofLetter_prepend {N : Type*} [AddCommMonoid N] [Module R N]
    {f g : ReducedTensorWords R M →ₗ[R] N}
    (h1 : ∀ a, f (ofLetter R M a) = g (ofLetter R M a))
    (h2 : ∀ a w, f (prepend R M a w) = g (prepend R M a w)) : f = g :=
  linearMap_ext R M fun ⟨n, hn⟩ x ↦ by match n with
    | 0 => omega
    | 1 => rw [of_one_tprod, h1]
    | k + 2 =>
      have hx : of R M ⟨k + 2, hn⟩ (PiTensorProduct.tprod R x) = prepend R M (x 0)
          (of R M ⟨k + 1, Nat.succ_pos k⟩ (PiTensorProduct.tprod R fun i ↦ x i.succ)) := by
        rw [prepend_of_tprod]
        exact of_tprod_congr R M hn rfl fun i ↦ by cases i using Fin.cases <;> simp
      rw [hx, h2]

end Prepend

/-- A word whose length is not one has no letter component. -/
theorem letter_of_of_ne_one {n : {n : ℕ // 0 < n}} (hn : n ≠ 1) (z : TensorPower R n.val M) :
    letter R M (of R M n z) = 0 := by
  rw [letter_apply, component_of_of_ne R M hn z, map_zero]

/-- The primitive elements of the reduced tensor coalgebra are exactly the single letters. -/
theorem deconcatenation_eq_zero_iff {x : ReducedTensorWords R M} :
    deconcatenation R M x = 0 ↔ x ∈ LinearMap.range (ofLetter R M) := by
  refine ⟨fun hx ↦ ⟨letter R M x, ?_⟩, ?_⟩
  · refine (eq_of_deconcatenation_eq_of_letter_eq R M ?_ ?_).symm
    · rw [deconcatenation_ofLetter, hx]
    · rw [letter_ofLetter]
  · rintro ⟨a, rfl⟩
    exact deconcatenation_ofLetter R M a

end Semiring

section Map

variable {R : Type uR} {M : Type uM} {N : Type uN} [CommSemiring R] [AddCommMonoid M]
  [Module R M] [AddCommMonoid N] [Module R N]

/-- Mapping a single letter applies the map to that letter. -/
@[simp]
theorem map_ofLetter (g : M →ₗ[R] N) (a : M) :
    ReducedTensorWords.map (R := R) g (ofLetter R M a) = ofLetter R N (g a) := by
  have hz : (![a] : Fin 1 → M) ⟨0, Nat.one_pos⟩ = a := by simp
  have h : subword R (![a] : Fin 1 → M) 0 1 = ofLetter R M a := by
    rw [subword_one R M (![a] : Fin 1 → M) Nat.one_pos, hz]
  rw [← h, map_subword, subword_one R N _ Nat.one_pos, hz]

/-- The letter of a letterwise-mapped word is the image of its letter. -/
@[simp]
theorem letter_comp_map (g : M →ₗ[R] N) :
    letter R N ∘ₗ ReducedTensorWords.map (R := R) g = g ∘ₗ letter R M := by
  refine linearMap_ext R M fun n x ↦ ?_
  simp only [LinearMap.comp_apply, letter_apply, component_map]
  have h : (TensorPower.oneEquiv R N).toLinearMap ∘ₗ PiTensorProduct.map (fun _ ↦ g) =
      g ∘ₗ (TensorPower.oneEquiv R M).toLinearMap := by
    refine PiTensorProduct.ext (MultilinearMap.ext fun y ↦ ?_)
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearEquiv.coe_coe, PiTensorProduct.map_tprod, TauCeti.TensorPower.oneEquiv_tprod]
  exact LinearMap.congr_fun h _

end Map

end ReducedTensorWords

end TauCeti
