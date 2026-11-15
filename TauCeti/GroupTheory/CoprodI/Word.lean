/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.CoprodI

/-!
# Reduced words in a free product: functorial images and word length

Let `f i : M i →* N i` be a family of monoid homomorphisms sending no nonidentity element to `1`.
Replacing every letter `m : M i` of a reduced word of the free product `CoprodI M` by `f i m`
gives a reduced word of `CoprodI N`, whose product is the image of the product of the original
word under the homomorphism `CoprodI M →* CoprodI N` induced by the `f i`.

We also record basic length properties of reduced words (`Word` and `NeWord`): left-multiplying a
reduced word whose leading letter lies in `M i` by an element of `M i` does not increase its word
length, and inverting a nonempty reduced word in a free product of groups preserves its word length.

## Main definitions

* `Monoid.CoprodI.Word.map`: the image of a reduced word under the `f i`.

## Main results

* `Monoid.CoprodI.Word.prod_map`: the product of the image is the image of the product.
* `Monoid.CoprodI.Word.length_toList_of_smul_le_of_fstIdx_eq`: left-multiplying by `of m` does not
  increase word length when the first letter lies in the same factor.
* `Monoid.CoprodI.NeWord.length_toList_inv`: inverting a nonempty reduced word preserves its length.
-/

public section

namespace Monoid.CoprodI.Word

section Map

variable {ι : Type*} {M N : ι → Type*} [∀ i, Monoid (M i)] [∀ i, Monoid (N i)]

/-- The image of a reduced word of the free product `CoprodI M` under homomorphisms
`f i : M i →* N i` of the factors that send no nonidentity element to `1`: each letter `m : M i`
is replaced by `f i m`. -/
def map (f : ∀ i, M i →* N i) (hf : ∀ i (m : M i), f i m = 1 → m = 1) (w : Word M) : Word N where
  toList := w.toList.map fun l => ⟨l.1, f l.1 l.2⟩
  ne_one := by
    simp only [List.mem_map, forall_exists_index, and_imp]
    rintro _ l hl rfl h1
    exact w.ne_one l hl (hf _ _ h1)
  chain_ne := (List.isChain_map _).2 w.chain_ne

variable (f : ∀ i, M i →* N i) (hf : ∀ i (m : M i), f i m = 1 → m = 1)

@[simp]
theorem toList_map (w : Word M) : (w.map f hf).toList = w.toList.map fun l => ⟨l.1, f l.1 l.2⟩ :=
  (rfl)

@[simp]
theorem map_empty : (empty : Word M).map f hf = empty :=
  (rfl)

/-- The product of the image of a reduced word is the image of its product under the
homomorphism of free products induced by the `f i`. -/
theorem prod_map (w : Word M) : (w.map f hf).prod = lift (fun i => of.comp (f i)) w.prod := by
  simp [prod, map_list_prod, Function.comp_def]

end Map

/-- Left-multiplying a reduced word whose first letter lies in `M i` by an element of `M i` does
not increase its word length: the leading `M i` letter merges with the new factor. -/
theorem length_toList_of_smul_le_of_fstIdx_eq {ι : Type*} {M : ι → Type*} [∀ i, Monoid (M i)]
    [DecidableEq ι] [∀ i, DecidableEq (M i)] {i : ι} (m : M i) {w : Word M}
    (hw : w.fstIdx = some i) :
    (of m • w).toList.length ≤ w.toList.length := by
  let p := equivPair i w
  have hp : rcons p = w := (equivPair i).symm_apply_apply w
  have hp1 : p.head ≠ 1 := fun h1 =>
    p.fstIdx_ne (by simpa [rcons, h1, hw] using congrArg fstIdx hp)
  have hw_len : w.toList.length = p.tail.toList.length + 1 := by
    rw [← hp, rcons, dite_eq_right hp1]
    rfl
  rw [of_smul_def, rcons]
  split_ifs <;> simp [p, hw_len]

end Monoid.CoprodI.Word

namespace Monoid.CoprodI.NeWord

/-- Inverting a nonempty reduced word preserves its length. -/
@[simp]
theorem length_toList_inv {ι : Type*} {G : ι → Type*} [∀ i, Group (G i)] {i j : ι}
    (w : NeWord G i j) : w.inv.toList.length = w.toList.length := by
  induction w with
  | singleton => rfl
  | append _ _ _ ih₁ ih₂ =>
    simp only [inv, toList, List.length_append, ih₁, ih₂, Nat.add_comm]

end Monoid.CoprodI.NeWord
