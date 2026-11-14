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
`1` only if `w` is empty.

## Main definitions

* `Monoid.CoprodI.Word.map`: the image of a reduced word under the `f i`.

## Main results

* `Monoid.CoprodI.Word.prod_map`: the product of the image is the image of the product.
* `Monoid.CoprodI.Word.eq_empty_of_lift_prod_eq_one`: a reduced word whose product the
  homomorphism induced by the `f i` sends to `1` is empty.
-/

public section

namespace Monoid.CoprodI.Word

variable {ι : Type*} {M N : ι → Type*} [∀ i, Monoid (M i)] [∀ i, Monoid (N i)]

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
theorem prod_map : (w.map f hf).prod = lift (fun i => of.comp (f i)) w.prod := by
  simp [prod, map_list_prod, Function.comp_def]

/-- A reduced word of `CoprodI M` none of whose letters the `f i : M i →* N i` send to `1` is empty
if the homomorphism `CoprodI M →* CoprodI N` induced by the `f i` sends its product to `1`. -/
theorem eq_empty_of_lift_prod_eq_one (hf : ∀ l ∈ w.toList, f l.1 l.2 ≠ 1)
    (h : lift (fun i => of.comp (f i)) w.prod = 1) : w = empty := by
  classical
  rw [← map_eq_empty_iff f hf]
  exact equiv.symm.injective ((prod_map f hf).trans h)

end Monoid.CoprodI.Word
