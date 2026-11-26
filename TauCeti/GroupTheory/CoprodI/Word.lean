/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.CoprodI

/-!
# Images of reduced words of a free product

Let `f i : M i →* N i` be a family of monoid homomorphisms and `w` a reduced word of the free
product `CoprodI M` none of whose letters is sent to `1`. Replacing every letter `m : M i` of `w`
by `f i m` gives a reduced word of `CoprodI N`, whose product is the image of the product of `w`
under the homomorphism `CoprodI M →* CoprodI N` induced by the `f i`. In particular that image is
`1` only if `w` is empty, since an element of a free product is the product of exactly one reduced
word. Likewise, injective homomorphisms of the factors induce an injective homomorphism of free
products.

## Main definitions

* `Monoid.CoprodI.Word.map`: the image of a reduced word under the `f i`.

## Main results

* `Monoid.CoprodI.Word.prod_injective`, `Monoid.CoprodI.Word.prod_surjective`: every element of
  the free product is the product of exactly one reduced word.
* `Monoid.CoprodI.Word.prod_map`: the product of the image is the image of the product.
* `Monoid.CoprodI.Word.eq_empty_of_lift_prod_eq_one`: a reduced word whose product the
  homomorphism induced by the `f i` sends to `1` is empty.
* `Monoid.CoprodI.NeWord.injective_pow_prod_of_ne`: a nonempty reduced word whose endpoints lie
  in distinct factors has injective power map `n ↦ w.prod ^ n`.
* `Monoid.CoprodI.lift_of_comp_injective`: injective homomorphisms of the factors induce an
  injective homomorphism of free products.
-/

public section

namespace Monoid.CoprodI

section Word

namespace Word

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

end Word

end Word

section NeWord

namespace NeWord

variable {ι : Type*} {M : ι → Type*} [∀ i, Monoid (M i)]

/-- The `(n + 1)`-fold reduced concatenation of a `NeWord M i j` with `i ≠ j`. -/
private def npowSucc {i j : ι} (hij : i ≠ j) (w : NeWord M i j) : ℕ → NeWord M i j
  | 0 => w
  | n + 1 => append w hij.symm (npowSucc hij w n)

private theorem prod_npowSucc {i j : ι} (hij : i ≠ j) (w : NeWord M i j) :
    ∀ n : ℕ, (npowSucc hij w n).prod = w.prod ^ (n + 1)
  | 0 => (pow_one w.prod).symm
  | n + 1 => by rw [npowSucc, append_prod, prod_npowSucc hij w n, ← pow_succ']

private theorem length_toList_npowSucc {i j : ι} (hij : i ≠ j) (w : NeWord M i j) :
    ∀ n : ℕ, (npowSucc hij w n).toList.length = (n + 1) * w.toList.length
  | 0 => (one_mul _).symm
  | n + 1 => by
      rw [npowSucc, toList, List.length_append, length_toList_npowSucc hij w n,
        Nat.add_mul (n + 1) 1 w.toList.length, one_mul, add_comm]

/-- A nonempty reduced word whose first and last letters lie in distinct factors has injective
power map `n ↦ w.prod ^ n`: adjacent copies of `w` do not cancel at their boundary. -/
theorem injective_pow_prod_of_ne {i j : ι} (hij : i ≠ j) (w : NeWord M i j) :
    Function.Injective (w.prod ^ · : ℕ → CoprodI M) := by
  classical
  have hlen : ∀ n : ℕ, (Word.equiv (w.prod ^ n)).toList.length = n * w.toList.length := by
    rintro (_ | n)
    · rw [pow_zero, ← Word.prod_empty, Word.equiv_prod]
      simp
    · rw [← prod_npowSucc hij w n, NeWord.prod, Word.equiv_prod]
      exact length_toList_npowSucc hij w n
  have hpos : 0 < w.toList.length := List.length_pos_iff.mpr w.toList_ne_nil
  intro m n (hmn : w.prod ^ m = w.prod ^ n)
  exact Nat.eq_of_mul_eq_mul_right hpos ((hlen m).symm.trans (by rw [hmn, hlen n]))

end NeWord

end NeWord

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
