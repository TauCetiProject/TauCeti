/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.CoprodI
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Reduced words in a free product: functorial images and word length

Let `f i : M i →* N i` be a family of monoid homomorphisms and `w` a reduced word of the free
product `CoprodI M` none of whose letters is sent to `1`. Replacing every letter `m : M i` of `w`
by `f i m` gives a reduced word of `CoprodI N`, whose product is the image of the product of `w`
under the homomorphism `CoprodI M →* CoprodI N` induced by the `f i`. In particular that image is
`1` only if `w` is empty, since an element of a free product is the product of exactly one reduced
word. Likewise, injective homomorphisms of the factors induce an injective homomorphism of free
products.

We also record basic length and power properties of reduced words (`Word` and `NeWord`):
left-multiplying a reduced word whose leading letter lies in `M i` by an element of `M i` does not
increase its word length, inverting a nonempty reduced word in a free product of groups preserves
its word length, and concatenating a nonempty reduced word whose endpoints lie in distinct factors
with itself gives all of its positive powers as reduced words, so its product has infinite order.

## Main definitions

* `Monoid.CoprodI.Word.map`: the image of a reduced word under the `f i`.
* `Monoid.CoprodI.NeWord.powSucc`: iterated concatenation `u^(n + 1)` of a nonempty reduced word
  `u` with distinct endpoint indices.

## Main results

* `Monoid.CoprodI.Word.prod_injective`, `Monoid.CoprodI.Word.prod_surjective`: every element of
  the free product is the product of exactly one reduced word.
* `Monoid.CoprodI.Word.prod_map`: the product of the image is the image of the product.
* `Monoid.CoprodI.Word.eq_empty_of_lift_prod_eq_one`: a reduced word whose product the
  homomorphism induced by the `f i` sends to `1` is empty.
* `Monoid.CoprodI.Word.length_toList_of_smul_le_of_fstIdx_eq`: left-multiplying by `of m` does not
  increase word length when the first letter lies in the same factor.
* `Monoid.CoprodI.NeWord.length_toList_inv`: inverting a nonempty reduced word preserves its length.
* `Monoid.CoprodI.NeWord.powSucc_prod`, `Monoid.CoprodI.NeWord.not_isOfFinOrder_prod_of_ne`:
  product of `u.powSucc` and infinite order of a nonempty reduced word with distinct endpoint
  indices.
* `Monoid.CoprodI.lift_of_comp_injective`: injective homomorphisms of the factors induce an
  injective homomorphism of free products.
-/

public section

namespace Monoid.CoprodI.Word

section Map

variable {ι : Type*} {M N : ι → Type*} [∀ i, Monoid (M i)] [∀ i, Monoid (N i)]

section Equiv

variable [DecidableEq ι] [∀ i, DecidableEq (M i)]

@[simp]
theorem equiv_symm_apply (w : Word M) : equiv.symm w = w.prod :=
  (rfl)

@[simp]
theorem equiv_prod (w : Word M) : equiv w.prod = w := by
  rw [← equiv_symm_apply, Equiv.apply_symm_apply]

@[simp]
theorem prod_equiv (m : CoprodI M) : (equiv m).prod = m := by
  rw [← equiv_symm_apply, Equiv.symm_apply_apply]

end Equiv

/-- A reduced word of a free product is determined by its product. -/
theorem prod_injective : Function.Injective (prod : Word M → CoprodI M) := by
  classical
  exact Function.LeftInverse.injective equiv_prod

/-- Every element of a free product is the product of a reduced word. -/
theorem prod_surjective : Function.Surjective (prod : Word M → CoprodI M) := by
  classical
  exact Function.RightInverse.surjective prod_equiv

/-- The image of a reduced word `w` of the free product `CoprodI M` under homomorphisms
`f i : M i →* N i` of the factors that send no letter of `w` to `1`: each letter `m : M i` is
replaced by `f i m`. -/
def map (f : ∀ i, M i →* N i) (w : Word M) (hf : ∀ l ∈ w.toList, f l.1 l.2 ≠ 1) : Word N where
  toList := w.toList.map fun l => ⟨l.1, f l.1 l.2⟩
  ne_one := by
    simp only [List.mem_map, forall_exists_index, and_imp]
    rintro _ l hl rfl
    exact hf l hl
  chain_ne := (List.isChain_map _).2 w.chain_ne

variable (f : ∀ i, M i →* N i) {w : Word M} (hf : ∀ l ∈ w.toList, f l.1 l.2 ≠ 1)

@[simp]
theorem toList_map : (w.map f hf).toList = w.toList.map fun l => ⟨l.1, f l.1 l.2⟩ :=
  (rfl)

@[simp]
theorem map_empty (hf : ∀ l ∈ (empty : Word M).toList, f l.1 l.2 ≠ 1) :
    (empty : Word M).map f hf = empty :=
  (rfl)

@[simp]
theorem map_eq_empty_iff : w.map f hf = empty ↔ w = empty := by
  simp [Word.ext_iff, empty]

/-- The product of the image of a reduced word is the image of its product under the
homomorphism of free products induced by the `f i`. -/
@[simp]
theorem prod_map : (w.map f hf).prod = lift (fun i => of.comp (f i)) w.prod := by
  simp [prod, map_list_prod, Function.comp_def]

/-- A reduced word of `CoprodI M` none of whose letters the `f i : M i →* N i` send to `1` is empty
if the homomorphism `CoprodI M →* CoprodI N` induced by the `f i` sends its product to `1`. -/
theorem eq_empty_of_lift_prod_eq_one (hf : ∀ l ∈ w.toList, f l.1 l.2 ≠ 1)
    (h : lift (fun i => of.comp (f i)) w.prod = 1) : w = empty := by
  rw [← map_eq_empty_iff f hf]
  exact prod_injective (by rw [prod_map, h, prod_empty])

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

section Monoid

variable {ι : Type*} {M : ι → Type*} [∀ i, Monoid (M i)]

/-- Iterated concatenation `u^(n + 1)` of a nonempty reduced word `u : NeWord M i j` whose first
and last letters lie in distinct factors (`j ≠ i`), so no cancellation occurs between copies. -/
def powSucc {i j : ι} (u : NeWord M i j) (hji : j ≠ i) : ℕ → NeWord M i j
  | 0 => u
  | n + 1 => u.append hji (u.powSucc hji n)

/-- The product of the iterated concatenation `u.powSucc hji n` is `u.prod ^ (n + 1)`. -/
@[simp]
theorem powSucc_prod {i j : ι} (u : NeWord M i j) (hji : j ≠ i) (n : ℕ) :
    (u.powSucc hji n).prod = u.prod ^ (n + 1) := by
  induction n with
  | zero => simp [powSucc]
  | succ n ih => rw [powSucc, append_prod, ih, ← pow_succ']

/-- A nonempty reduced word whose first and last letters lie in distinct factors represents an
element of infinite order in `CoprodI M`. -/
theorem not_isOfFinOrder_prod_of_ne {i j : ι} (u : NeWord M i j) (hij : i ≠ j) :
    ¬IsOfFinOrder u.prod := by
  rw [isOfFinOrder_iff_pow_eq_one]
  rintro ⟨n, hn, hpow⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have hprod : (u.powSucc hij.symm k).toWord.prod = (Word.empty : Word M).prod := by
    rw [← NeWord.prod, powSucc_prod, hpow, Word.prod_empty]
  have hempty : (u.powSucc hij.symm k).toWord = Word.empty :=
    Word.prod_injective hprod
  exact (u.powSucc hij.symm k).toList_ne_nil (congrArg Word.toList hempty)

end Monoid

/-- Inverting a nonempty reduced word preserves its length. -/
@[simp]
theorem length_toList_inv {ι : Type*} {G : ι → Type*} [∀ i, Group (G i)] {i j : ι}
    (w : NeWord G i j) : w.inv.toList.length = w.toList.length := by
  induction w with
  | singleton => rfl
  | append _ _ _ ih₁ ih₂ =>
    simp only [inv, toList, List.length_append, ih₁, ih₂, Nat.add_comm]

end Monoid.CoprodI.NeWord

namespace Monoid.CoprodI

variable {ι : Type*} {M N : ι → Type*} [∀ i, Monoid (M i)] [∀ i, Monoid (N i)]

/-- Injective homomorphisms `f i : M i →* N i` of the factors induce an injective homomorphism
`CoprodI M →* CoprodI N` of free products. -/
theorem lift_of_comp_injective {f : ∀ i, M i →* N i} (hf : ∀ i, Function.Injective (f i)) :
    Function.Injective (lift fun i => of.comp (f i)) := by
  have hf₁ (w : Word M) : ∀ l ∈ w.toList, f l.1 l.2 ≠ 1 := fun l hl =>
    (map_ne_one_iff (f l.1) (hf l.1)).2 (w.ne_one l hl)
  intro x y hxy
  obtain ⟨v, rfl⟩ := Word.prod_surjective x
  obtain ⟨w, rfl⟩ := Word.prod_surjective y
  rw [← Word.prod_map f (hf₁ v), ← Word.prod_map f (hf₁ w)] at hxy
  exact congrArg Word.prod <| Word.ext <| List.map_injective_iff.2
    (Function.injective_id.sigma_map hf) (congrArg Word.toList (Word.prod_injective hxy))

end Monoid.CoprodI
