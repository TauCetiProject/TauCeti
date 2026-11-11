/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorCoalgebra.CoalgHom
public import TauCeti.LinearAlgebra.TensorCoalgebra.GradedCoderivation

/-!
# Block families of tensor words

The blocks `[a, a + b)` of consecutive positions of a tensor word are cut by reduced
deconcatenation into a left block `[a, a + c)` and a right block `[a + c, a + b)`
(`TauCeti.ReducedTensorWords.deconcatenation_subword`).  A *block family* is any family of tensor
words `V a b`, indexed by the blocks, which deconcatenates in the same way,

`Δ (V a b) = ∑_{0 < c < b} V a c ⊗ V (a + c) (b - c)`.

Besides the blocks of a single word, two families of this shape occur in the theory of Massey
products: the images of the blocks of a word under a coalgebra morphism
(`TauCeti.ReducedTensorWords.IsBlockFamily.map`), and the words assembled from an arbitrary
family of letters `e a b`, one for each block, by summing over all ways of cutting a block into
consecutive sub-blocks and replacing each sub-block `[c, c + d)` by the letter `e c d`.  The
latter is `TauCeti.ReducedTensorWords.blockWord`; it is the unique block family with the letters
`e a b` (`TauCeti.ReducedTensorWords.IsBlockFamily.eq_blockWord`).

The main property of block families concerns graded coderivations `d`.  The co-Leibniz rule
expresses the cuts of `d (V a b)` through the values of `d` on the proper sub-blocks.  If the
letter component of `d` vanishes on all sub-blocks of `[a, a + b)`, then so does `d` itself
(`TauCeti.ReducedTensorWords.IsGradedCoderivation.apply_eq_zero_of_isBlockFamily`); if it vanishes
on the proper sub-blocks only, then `d (V a b)` is the single letter given by its letter
component (`TauCeti.ReducedTensorWords.IsGradedCoderivation.apply_eq_ofLetter_of_isBlockFamily`).
Applied to the bar differential of an `A∞` algebra this is the reason why the value of a defining
system of a higher Massey product is a cycle.

## Main definitions

* `TauCeti.ReducedTensorWords.IsBlockFamily`: a family of tensor words deconcatenating like the
  blocks of a word.
* `TauCeti.ReducedTensorWords.blockWord`: the sum over all cuttings of a block into sub-blocks of
  the words formed by the letters of the sub-blocks.

## Main results

* `TauCeti.ReducedTensorWords.isBlockFamily_subword` and
  `TauCeti.ReducedTensorWords.IsBlockFamily.map`: the blocks of a word form a block family, and
  coalgebra morphisms preserve block families.
* `TauCeti.ReducedTensorWords.isBlockFamily_blockWord` and
  `TauCeti.ReducedTensorWords.letter_blockWord`: the words assembled from a family of letters form
  a block family with these letters.
* `TauCeti.ReducedTensorWords.IsBlockFamily.eq_blockWord`: a block family is determined by its
  letters.
* `TauCeti.ReducedTensorWords.blockWord_add_ofLetter`: away from its uncut term, a block word only
  depends on the letters of the proper sub-blocks.
* `TauCeti.ReducedTensorWords.IsGradedCoderivation.apply_eq_zero_of_isBlockFamily` and
  `TauCeti.ReducedTensorWords.IsGradedCoderivation.apply_eq_ofLetter_of_isBlockFamily`: a graded
  coderivation on a block family is controlled by its letter component.

## References

* J. P. May, *Matric Massey products*, J. Algebra 12 (1969), 533--568, Section 1.
* D.-M. Lu, J. H. Palmieri, Q.-S. Wu, J. J. Zhang, *A-infinity structure on Ext-algebras*,
  J. Pure Appl. Algebra 213 (2009), Section 3.
-/

public section

open scoped TensorProduct

universe uR uM uN

namespace TauCeti

namespace ReducedTensorWords

section Semiring

variable {R : Type uR} {M : Type uM} {N : Type uN} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]

variable (R) in
/-- A family of tensor words `V a b`, indexed by the blocks `[a, a + b)` of consecutive
positions, is a **block family** when it deconcatenates like the blocks of a single word:
`Δ (V a b) = ∑_{0 < c < b} V a c ⊗ V (a + c) (b - c)`. -/
def IsBlockFamily (V : ℕ → ℕ → ReducedTensorWords R M) : Prop :=
  ∀ a b, deconcatenation R M (V a b) = ∑ c ∈ Finset.Ioo 0 b, V a c ⊗ₜ[R] V (a + c) (b - c)

/-- The defining identity of a block family, as a reusable `Iff`. -/
theorem isBlockFamily_iff {V : ℕ → ℕ → ReducedTensorWords R M} :
    IsBlockFamily R V ↔
      ∀ a b, deconcatenation R M (V a b) = ∑ c ∈ Finset.Ioo 0 b, V a c ⊗ₜ[R] V (a + c) (b - c) :=
  Iff.rfl

/-- The blocks of a single word form a block family. -/
theorem isBlockFamily_subword {n : ℕ} (x : Fin n → M) : IsBlockFamily R (subword R x) :=
  fun _ _ ↦ deconcatenation_subword R x

/-- A coalgebra morphism maps a block family to a block family. -/
theorem IsBlockFamily.map {V : ℕ → ℕ → ReducedTensorWords R M} (hV : IsBlockFamily R V)
    {F : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N} (hF : IsCoalgHom R F) :
    IsBlockFamily R fun a b ↦ F (V a b) := by
  intro a b
  rw [hF.deconcatenation_apply, hV a b, map_sum]
  simp only [TensorProduct.map_tmul]

variable (R) in
/-- The **block word** of a family of letters `e a b`, one for each block `[a, a + b)`: the sum,
over all ways of cutting the block `[a, a + b)` into consecutive nonempty sub-blocks
`[c₀, c₁), [c₁, c₂), …`, of the words `e c₀ (c₁ - c₀) ⊗ e c₁ (c₂ - c₁) ⊗ ⋯`.  It is defined by
recursion on the length of the first sub-block, and vanishes on the empty block. -/
noncomputable def blockWord (e : ℕ → ℕ → M) : ℕ → ℕ → ReducedTensorWords R M
  | _, 0 => 0
  | a, b + 1 => ofLetter R M (e a (b + 1)) +
      ∑ c : Fin b, prepend R M (e a (c + 1)) (blockWord e (a + c + 1) (b - c))
termination_by _ b => b
decreasing_by omega

variable (e : ℕ → ℕ → M)

/-- The block word of the empty block vanishes. -/
@[simp]
theorem blockWord_zero (a : ℕ) : blockWord R e a 0 = 0 := by
  rw [blockWord]

/-- The recursion for block words: either the block is not cut, or its first sub-block is
`[a, a + c + 1)` and the rest is the block word of `[a + c + 1, a + b + 1)`. -/
theorem blockWord_succ (a b : ℕ) :
    blockWord R e a (b + 1) = ofLetter R M (e a (b + 1)) +
      ∑ c ∈ Finset.range b, prepend R M (e a (c + 1)) (blockWord R e (a + c + 1) (b - c)) := by
  rw [blockWord, Fin.sum_univ_eq_sum_range
    (fun c ↦ prepend R M (e a (c + 1)) (blockWord R e (a + c + 1) (b - c)))]

/-- The block word of a block of length one is its letter. -/
@[simp]
theorem blockWord_one (a : ℕ) : blockWord R e a 1 = ofLetter R M (e a 1) := by
  rw [blockWord_succ, Finset.range_zero, Finset.sum_empty, add_zero]

/-- The letter of the block word of a nonempty block is the letter of that block. -/
@[simp]
theorem letter_blockWord {a b : ℕ} (hb : 0 < b) : letter R M (blockWord R e a b) = e a b := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_lt hb
  rw [zero_add, blockWord_succ, map_add, map_sum, letter_ofLetter]
  simp only [letter_prepend, Finset.sum_const_zero, add_zero]

/-- Splitting off the first letter of the left block reindexes the pairs of a block of length
`b + 1` by the length `c + 1` of the left block. -/
private theorem sum_Ioo_blockWord_tmul (a b : ℕ) :
    ∑ c ∈ Finset.Ioo 0 (b + 1), blockWord R e a c ⊗ₜ[R] blockWord R e (a + c) (b + 1 - c) =
      ∑ c ∈ Finset.range b,
        blockWord R e a (c + 1) ⊗ₜ[R] blockWord R e (a + c + 1) (b - c) := by
  rw [← Finset.Ico_add_one_left_eq_Ioo, Finset.sum_Ico_eq_sum_range]
  refine Finset.sum_congr (by simp) fun c _ ↦ ?_
  rw [zero_add, add_comm 1 c, ← add_assoc, show b + 1 - (c + 1) = b - c by omega]

/-- Block words form a block family. -/
theorem isBlockFamily_blockWord : IsBlockFamily R (blockWord R e) := by
  intro a b
  induction b using Nat.strong_induction_on generalizing a with
  | _ b ih =>
    rcases b with _ | b
    · simp
    -- Cutting `e a (c + 1) · W` either right after the first letter, or inside `W`.
    have hcut : ∀ c ∈ Finset.range b, deconcatenation R M
        (prepend R M (e a (c + 1)) (blockWord R e (a + c + 1) (b - c))) =
          ofLetter R M (e a (c + 1)) ⊗ₜ[R] blockWord R e (a + c + 1) (b - c) +
            ∑ k ∈ Finset.Ioo 0 (b - c),
              prepend R M (e a (c + 1)) (blockWord R e (a + c + 1) k) ⊗ₜ[R]
                blockWord R e (a + c + 1 + k) (b - c - k) := by
      intro c hc
      rw [deconcatenation_prepend, ih (b - c) (by simp at hc; omega), map_sum]
      simp only [LinearMap.rTensor_tmul]
    rw [blockWord_succ, map_add, deconcatenation_ofLetter, zero_add, map_sum,
      Finset.sum_congr rfl hcut, Finset.sum_add_distrib]
    rw [sum_Ioo_blockWord_tmul]
    simp only [blockWord_succ, TensorProduct.add_tmul, Finset.sum_add_distrib,
      TensorProduct.sum_tmul]
    congr 1
    -- Reindex the pairs `d < c < b` of the expanded left blocks by the pairs `(d, k = c - d)`.
    rw [Finset.sum_sigma', Finset.sum_sigma']
    refine Finset.sum_nbij' (fun p ↦ ⟨p.1 + p.2, p.1⟩) (fun p ↦ ⟨p.2, p.1 - p.2⟩) ?_ ?_ ?_ ?_ ?_
    · rintro ⟨c, k⟩ h
      simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_Ioo] at h ⊢
      omega
    · rintro ⟨c, d⟩ h
      simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_Ioo] at h ⊢
      omega
    · rintro ⟨c, k⟩ _
      dsimp only
      rw [Sigma.mk.injEq]
      exact ⟨rfl, heq_of_eq (by omega)⟩
    · rintro ⟨c, d⟩ h
      simp only [Finset.mem_sigma, Finset.mem_range] at h
      dsimp only
      rw [Sigma.mk.injEq]
      exact ⟨by omega, HEq.rfl⟩
    · rintro ⟨c, k⟩ h
      simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_Ioo] at h
      have h₁ : c + k - c = k := by omega
      have h₂ : a + (c + k) + 1 = a + c + 1 + k := by omega
      have h₃ : b - (c + k) = b - c - k := by omega
      rw [h₁, h₂, h₃]

/-- **A block family is determined by its letters**: if the letters of a block family agree with
`e` on every sub-block of a nonempty block, then on that block the family is the block word
of `e`. -/
theorem IsBlockFamily.eq_blockWord {V : ℕ → ℕ → ReducedTensorWords R M} (hV : IsBlockFamily R V)
    {a b : ℕ} (hb : 0 < b)
    (h : ∀ c k, 0 < k → a ≤ c → c + k ≤ a + b → letter R M (V c k) = e c k) :
    V a b = blockWord R e a b := by
  induction b using Nat.strong_induction_on generalizing a with
  | _ b ih =>
    refine eq_of_deconcatenation_eq_of_letter_eq R M ?_ ?_
    · rw [hV a b, isBlockFamily_blockWord e a b]
      refine Finset.sum_congr rfl fun c hc ↦ ?_
      rw [Finset.mem_Ioo] at hc
      rw [ih c hc.2 hc.1 fun c' k hk h₁ h₂ ↦ h c' k hk h₁ (by omega),
        ih (b - c) (by omega) (by omega) fun c' k hk h₁ h₂ ↦ h c' k hk (by omega) (by omega)]
    · rw [letter_blockWord e hb, h a b hb le_rfl le_rfl]

/-- A block word only depends on the letters of the sub-blocks of its block. -/
theorem blockWord_congr {e' : ℕ → ℕ → M} {a b : ℕ}
    (h : ∀ c k, 0 < k → a ≤ c → c + k ≤ a + b → e c k = e' c k) :
    blockWord R e a b = blockWord R e' a b := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp
  exact (isBlockFamily_blockWord e).eq_blockWord e' hb fun c k hk h₁ h₂ ↦ by
    rw [letter_blockWord e hk, h c k hk h₁ h₂]

/-- The block word of a block of length two: the letter of the block, plus the word of the
letters of its two halves. -/
theorem blockWord_two (a : ℕ) :
    blockWord R e a 2 =
      ofLetter R M (e a 2) + prepend R M (e a 1) (ofLetter R M (e (a + 1) 1)) := by
  rw [blockWord_succ, Finset.sum_range_one, zero_add, blockWord_one]

/-- Changing the letter of the whole block only changes the uncut term of a block word: if `e` and
`e'` agree on the proper sub-blocks of a nonempty block, their block words on that block differ by
the difference of the single letters `e a b` and `e' a b`. -/
theorem blockWord_add_ofLetter {e' : ℕ → ℕ → M} {a b : ℕ} (hb : 0 < b)
    (h : ∀ c k, 0 < k → k < b → a ≤ c → c + k ≤ a + b → e c k = e' c k) :
    blockWord R e a b + ofLetter R M (e' a b) = blockWord R e' a b + ofLetter R M (e a b) := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_lt hb
  rw [zero_add] at h ⊢
  have hsum :
      ∑ c ∈ Finset.range b, prepend R M (e a (c + 1)) (blockWord R e (a + c + 1) (b - c)) =
        ∑ c ∈ Finset.range b, prepend R M (e' a (c + 1)) (blockWord R e' (a + c + 1) (b - c)) := by
    refine Finset.sum_congr rfl fun c hc ↦ ?_
    rw [Finset.mem_range] at hc
    rw [h a (c + 1) (by omega) (by omega) le_rfl (by omega),
      blockWord_congr e fun c' k hk h₁ h₂ ↦ h c' k hk (by omega) (by omega) (by omega)]
  rw [blockWord_succ, blockWord_succ, hsum]
  abel

end Semiring

section Coderivation

variable {R : Type uR} {M : Type uM} [CommRing R] [AddCommMonoid M] [Module R M]
  {G : InternalGrading R M} {q : ℤ} {d : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M}
  {V : ℕ → ℕ → ReducedTensorWords R M}

/-- **A graded coderivation vanishing on the letters of a block family vanishes on it**: if the
letter component of `d (V c k)` vanishes for every sub-block `[c, c + k)` of a nonempty block
`[a, a + b)`, then `d (V a b) = 0`. -/
theorem IsGradedCoderivation.apply_eq_zero_of_isBlockFamily (hd : IsGradedCoderivation G q d)
    (hV : IsBlockFamily R V) {a b : ℕ} (hb : 0 < b)
    (h : ∀ c k, 0 < k → a ≤ c → c + k ≤ a + b → letter R M (d (V c k)) = 0) :
    d (V a b) = 0 := by
  induction b using Nat.strong_induction_on generalizing a with
  | _ b ih =>
    refine eq_of_deconcatenation_eq_of_letter_eq R M ?_ ?_
    · rw [hd.deconcatenation_apply, hV a b, map_zero (deconcatenation R M)]
      simp only [map_sum, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero fun c hc ↦ ?_
      rw [Finset.mem_Ioo] at hc
      rw [ih c hc.2 hc.1 fun c' k hk h₁ h₂ ↦ h c' k hk h₁ (by omega),
        ih (b - c) (by omega) (by omega) fun c' k hk h₁ h₂ ↦ h c' k hk (by omega) (by omega)]
      simp
    · rw [map_zero (letter R M)]
      exact h a b hb le_rfl le_rfl

/-- **On a block family a graded coderivation is a letter once it vanishes on proper blocks**: if
the letter component of `d (V c k)` vanishes for every proper sub-block `[c, c + k)` of the
block `[a, a + b)`, then `d (V a b)` is the single letter given by its letter component. -/
theorem IsGradedCoderivation.apply_eq_ofLetter_of_isBlockFamily (hd : IsGradedCoderivation G q d)
    (hV : IsBlockFamily R V) {a b : ℕ}
    (h : ∀ c k, 0 < k → k < b → a ≤ c → c + k ≤ a + b → letter R M (d (V c k)) = 0) :
    d (V a b) = ofLetter R M (letter R M (d (V a b))) := by
  have hΔ : deconcatenation R M (d (V a b)) = 0 := by
    rw [hd.deconcatenation_apply, hV a b]
    simp only [map_sum, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun c hc ↦ ?_
    rw [Finset.mem_Ioo] at hc
    rw [hd.apply_eq_zero_of_isBlockFamily hV hc.1
        fun c' k hk h₁ h₂ ↦ h c' k hk (by omega) h₁ (by omega),
      hd.apply_eq_zero_of_isBlockFamily hV (b := b - c) (by omega)
        fun c' k hk h₁ h₂ ↦ h c' k hk (by omega) (by omega) (by omega)]
    simp
  obtain ⟨y, hy⟩ := (deconcatenation_eq_zero_iff R M).1 hΔ
  rw [← hy, letter_ofLetter]

end Coderivation

end ReducedTensorWords

end TauCeti
