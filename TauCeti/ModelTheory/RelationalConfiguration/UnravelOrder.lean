/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Rat.Denumerable
public import TauCeti.ModelTheory.RelationalConfiguration.OrderClass
public import TauCeti.ModelTheory.RelationalConfiguration.Unravelling

/-!
# The linear order of an unravelled graph code

For a code `c : RelationalConfiguration Language.graph ℕ` with the colouring `χ_c = unravelColor c`
of `List ℚ`, order `List ℚ × ℕ` lexicographically, first by the `List ℚ` coordinate and then,
inside the block of `x`, by the order of type `ω + (χ_c(x) + 2)` on `ℕ` that puts the indices
`≥ χ_c(x) + 2` first, in increasing order, and then the indices `< χ_c(x) + 2`, in increasing
order. Relabelled along the fixed bijection `ℕ ≃ List ℚ × ℕ`, this is a code
`unravelOrderCode c` of `Language.order`.

This file proves that `unravelOrderCode` is continuous, that its values are coded linear orders
for every code, simple graph or not, and that it sends isomorphic codes to isomorphic codes:
an order automorphism `Φ` of `List ℚ` with `χ_d ∘ Φ = χ_c`, given by the unravelling lemma,
extends block by block. That isomorphic images come only from isomorphic codes is the remaining
half of the reduction of isomorphism of graph codes to isomorphism of coded linear orders.

## Main definitions

* `TauCeti.RelationalConfiguration.unravelOrderRel χ`: the order of `List ℚ × ℕ` for a colouring
  `χ` of `List ℚ`.
* `TauCeti.RelationalConfiguration.unravelOrderCode c`: the code on `ℕ` of the order for the
  colouring `unravelColor c`.

## Main results

* `TauCeti.RelationalConfiguration.continuous_unravelOrderCode`: the map is continuous.
* `TauCeti.RelationalConfiguration.unravelOrderCode_mem_linearOrderClass`: its values are coded
  linear orders.
* `TauCeti.RelationalConfiguration.isoSetoid_unravelOrderCode`: isomorphic codes have isomorphic
  images.

## References

* H. Friedman and L. Stanley, *A Borel reducibility theory for classes of countable structures*,
  J. Symbolic Logic 54 (1989), §2.
* A. Montalbán, *Computable structure theory: within the arithmetic*, author's draft of Part 1
  (2019), Lemma VI.18.
-/

public section

open FirstOrder FirstOrder.Language Set

namespace TauCeti.RelationalConfiguration

/-! ### The block order and the order of `List ℚ × ℕ` -/

/-- The position of the index `i` in a block of colour `n`, ordered as `ω + (n + 2)`: the indices
`≥ n + 2` come first, in increasing order, and then the indices `< n + 2`. -/
def blockKey (n i : ℕ) : Lex (Bool × ℕ) :=
  toLex (decide (i < n + 2), i)

/-- Distinct indices have distinct positions in a block. -/
theorem blockKey_injective (n : ℕ) : Function.Injective (blockKey n) := fun i j h => by
  simpa [blockKey] using congrArg (fun p => (ofLex p).2) h

/-- In a block of colour `n`, `i` comes before `j` exactly when `i ≥ n + 2` and `j < n + 2`, or
`i` and `j` are on the same side of `n + 2` and `i ≤ j`. -/
@[simp]
theorem blockKey_le_blockKey_iff {n i j : ℕ} :
    blockKey n i ≤ blockKey n j ↔ n + 2 ≤ i ∧ j < n + 2 ∨ (i < n + 2 ↔ j < n + 2) ∧ i ≤ j := by
  rw [blockKey, blockKey, Prod.Lex.toLex_le_toLex]
  rcases lt_or_ge i (n + 2) with hi | hi <;> rcases lt_or_ge j (n + 2) with hj | hj <;>
    simp [hi, hj, hi.not_gt, hj.not_gt]

/-- In a block of colour `n`, `i` comes strictly before `j` exactly when `i ≥ n + 2` and
`j < n + 2`, or `i` and `j` are on the same side of `n + 2` and `i < j`. -/
@[simp]
theorem blockKey_lt_blockKey_iff {n i j : ℕ} :
    blockKey n i < blockKey n j ↔ n + 2 ≤ i ∧ j < n + 2 ∨ (i < n + 2 ↔ j < n + 2) ∧ i < j := by
  rw [blockKey, blockKey, Prod.Lex.toLex_lt_toLex]
  rcases lt_or_ge i (n + 2) with hi | hi <;> rcases lt_or_ge j (n + 2) with hj | hj <;>
    simp [hi, hj, hi.not_gt, hj.not_gt]

/-- The position of a point `(x, i)` of `List ℚ × ℕ` for the colouring `χ`: first `x`, then the
position of `i` in the block of colour `χ x`. -/
private def unravelOrderKey (χ : List ℚ → ℕ) (p : List ℚ × ℕ) : Lex (List ℚ × Lex (Bool × ℕ)) :=
  toLex (p.1, blockKey (χ p.1) p.2)

/-- Distinct points have distinct positions. -/
private theorem unravelOrderKey_injective (χ : List ℚ → ℕ) :
    Function.Injective (unravelOrderKey χ) := by
  rintro ⟨x, i⟩ ⟨y, j⟩ h
  simp only [unravelOrderKey, toLex_inj, Prod.mk.injEq] at h
  obtain ⟨rfl, h⟩ := h
  rw [blockKey_injective _ h]

/-- The order of `List ℚ × ℕ` for a colouring `χ` of `List ℚ`: the lexicographic sum over the
order of `List ℚ` of the blocks `ω + (χ x + 2)`. -/
def unravelOrderRel (χ : List ℚ → ℕ) (p q : List ℚ × ℕ) : Prop :=
  unravelOrderKey χ p ≤ unravelOrderKey χ q

/-- Points of distinct blocks compare by their `List ℚ` coordinates; two points of the block of
`x` compare by their positions in the block of colour `χ x`. -/
theorem unravelOrderRel_iff {χ : List ℚ → ℕ} {p q : List ℚ × ℕ} :
    unravelOrderRel χ p q ↔
      p.1 < q.1 ∨ p.1 = q.1 ∧ blockKey (χ p.1) p.2 ≤ blockKey (χ p.1) q.2 := by
  rw [unravelOrderRel, unravelOrderKey, unravelOrderKey, Prod.Lex.toLex_le_toLex]
  constructor
  · rintro (h | ⟨h, h'⟩)
    · exact Or.inl h
    · refine Or.inr ⟨h, ?_⟩
      dsimp only at h'
      rwa [← h] at h'
  · rintro (h | ⟨h, h'⟩)
    · exact Or.inl h
    · refine Or.inr ⟨h, ?_⟩
      dsimp only
      rwa [← h]

/-- The order of `List ℚ × ℕ` for a colouring is a linear order, being the pullback of a linear
order along an injective map. -/
instance isLinearOrder_unravelOrderRel (χ : List ℚ → ℕ) :
    IsLinearOrder (List ℚ × ℕ) (unravelOrderRel χ) :=
  (RelEmbedding.preimage ⟨_, unravelOrderKey_injective χ⟩ (· ≤ ·)).isLinearOrder

/-- An order automorphism `Φ` of `List ℚ` with `χ' ∘ Φ = χ`, applied to the `List ℚ`
coordinate, carries the order for `χ` to the order for `χ'`. -/
theorem unravelOrderRel_map {χ χ' : List ℚ → ℕ} (Φ : List ℚ ≃o List ℚ) (hΦ : ∀ x, χ' (Φ x) = χ x)
    (p q : List ℚ × ℕ) :
    unravelOrderRel χ' (Φ p.1, p.2) (Φ q.1, q.2) ↔ unravelOrderRel χ p q := by
  rw [unravelOrderRel_iff, unravelOrderRel_iff, Φ.lt_iff_lt, Φ.injective.eq_iff, hΦ]

/-! ### The code -/

/-- The fixed enumeration of `List ℚ × ℕ` by `ℕ`. -/
noncomputable def unravelOrderEquiv : ℕ ≃ List ℚ × ℕ :=
  (Denumerable.eqv (List ℚ × ℕ)).symm

/-- The code on `ℕ` of the order of `List ℚ × ℕ` for the colouring `unravelColor c`, relabelled
along `unravelOrderEquiv`. -/
noncomputable def unravelOrderCode (c : RelationalConfiguration Language.graph ℕ) :
    RelationalConfiguration Language.order ℕ :=
  ofRel fun m n => unravelOrderRel (unravelColor c) (unravelOrderEquiv m) (unravelOrderEquiv n)

/-- The code `unravelOrderCode c` reads `leSymb` as the order for `unravelColor c`. -/
@[simp]
theorem codeRel_unravelOrderCode (c : RelationalConfiguration Language.graph ℕ) (m n : ℕ) :
    codeRel leSymb (unravelOrderCode c) m n ↔
      unravelOrderRel (unravelColor c) (unravelOrderEquiv m) (unravelOrderEquiv n) := by
  rw [unravelOrderCode, codeRel_ofRel]

/-- **The values are coded linear orders**, for every code of the language of graphs. -/
theorem unravelOrderCode_mem_linearOrderClass (c : RelationalConfiguration Language.graph ℕ) :
    unravelOrderCode c ∈ linearOrderClass := by
  rw [mem_linearOrderClass, unravelOrderCode, codeRel_ofRel]
  exact (RelEmbedding.preimage unravelOrderEquiv.toEmbedding
    (unravelOrderRel (unravelColor c))).isLinearOrder

/-! ### Continuity -/

/-- **`unravelOrderCode` is continuous**: each coordinate compares two points of `List ℚ × ℕ`,
which depends on the code at most through the colour of their common block. -/
theorem continuous_unravelOrderCode : Continuous unravelOrderCode := by
  classical
  refine continuous_iff.2 fun a => ?_
  induction a using Atom.induction_atom with | @h k R v => ?_
  obtain rfl : k = 2 := by cases R; rfl
  rw [order.relation_eq_leSymb R]
  set p := unravelOrderEquiv (v 0)
  set q := unravelOrderEquiv (v 1)
  have h : (fun c => (unravelOrderCode c).eval (atom leSymb v)) =
      (fun n => decide (p.1 < q.1 ∨ p.1 = q.1 ∧ blockKey n p.2 ≤ blockKey n q.2)) ∘
        fun c => unravelColor c p.1 := by
    funext c
    rw [unravelOrderCode, eval_ofRel, Function.comp_apply]
    exact decide_eq_decide.2 unravelOrderRel_iff
  rw [h]
  exact continuous_of_discreteTopology.comp (continuous_unravelColor p.1)

/-! ### Isomorphic codes have isomorphic images -/

/-- **Isomorphic codes have isomorphic images.** By the unravelling lemma an isomorphism gives an
order automorphism `Φ` of `List ℚ` with `χ_d ∘ Φ = χ_c`; applied to the `List ℚ` coordinate and
relabelled to `ℕ`, it carries the order of `c` to the order of `d`. -/
theorem isoSetoid_unravelOrderCode {c d : RelationalConfiguration Language.graph ℕ}
    (h : isoSetoid Language.graph ℕ c d) :
    isoSetoid Language.order ℕ (unravelOrderCode c) (unravelOrderCode d) := by
  obtain ⟨Φ, hΦ⟩ := isoSetoid_iff_exists_orderIso_unravelColor.1 h
  let ψ : List ℚ × ℕ ≃ List ℚ × ℕ := Φ.toEquiv.prodCongr (Equiv.refl ℕ)
  let σ : Equiv.Perm ℕ := (unravelOrderEquiv.trans ψ).trans unravelOrderEquiv.symm
  refine isoSetoid_iff_exists_perm_smul_eq.2 ⟨σ, ?_⟩
  rw [← ofRel_codeRel (σ • unravelOrderCode c)]
  refine congrArg ofRel (funext fun m => funext fun n => propext ?_)
  have he (k : ℕ) : unravelOrderEquiv (σ.symm k) =
      (Φ.symm (unravelOrderEquiv k).1, (unravelOrderEquiv k).2) := by
    ext <;> simp [σ, ψ]
  rw [codeRel_perm_smul, codeRel_unravelOrderCode, he, he, ← unravelOrderRel_map Φ
    (fun x => congrFun hΦ x)]
  simp

end TauCeti.RelationalConfiguration
