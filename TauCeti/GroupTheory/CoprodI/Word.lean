/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.CoprodI

/-!
# Images of reduced words of a free product

Let `f i : M i →* N i` be a family of monoid homomorphisms sending no nonidentity element to `1`.
Replacing every letter `m : M i` of a reduced word of the free product `CoprodI M` by `f i m`
gives a reduced word of `CoprodI N`, whose product is the image of the product of the original
word under the homomorphism `CoprodI M →* CoprodI N` induced by the `f i`. Since an element of a
free product is the product of exactly one reduced word (Mathlib's `Monoid.CoprodI.Word.equiv`),
injective homomorphisms of the factors induce an injective homomorphism of free products.

## Main definitions

* `Monoid.CoprodI.Word.map`: the image of a reduced word under the `f i`.

## Main results

* `Monoid.CoprodI.Word.prod_map`: the product of the image is the image of the product.
* `Monoid.CoprodI.lift_of_comp_injective`: injective homomorphisms of the factors induce an
  injective homomorphism of free products.
-/

public section

namespace Monoid.CoprodI.Word

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

end Monoid.CoprodI.Word

namespace Monoid.CoprodI

variable {ι : Type*} {M N : ι → Type*} [∀ i, Monoid (M i)] [∀ i, Monoid (N i)]

/-- Injective homomorphisms `f i : M i →* N i` of the factors induce an injective homomorphism
`CoprodI M →* CoprodI N` of free products. -/
theorem lift_of_comp_injective {f : ∀ i, M i →* N i} (hf : ∀ i, Function.Injective (f i)) :
    Function.Injective (lift fun i => of.comp (f i)) := by
  classical
  have hf₁ (i : ι) (m : M i) : f i m = 1 → m = 1 := (map_eq_one_iff (f i) (hf i)).1
  -- `Word.equiv` is the bijection `CoprodI _ ≃ Word _` whose inverse is `Word.prod`.
  have hsurj : Function.Surjective (Word.prod : Word M → CoprodI M) := Word.equiv.symm.surjective
  have hinj : Function.Injective (Word.prod : Word N → CoprodI N) := Word.equiv.symm.injective
  intro x y hxy
  obtain ⟨v, rfl⟩ := hsurj x
  obtain ⟨w, rfl⟩ := hsurj y
  rw [← Word.prod_map f hf₁, ← Word.prod_map f hf₁] at hxy
  exact congrArg Word.prod <| Word.ext <|
    List.map_injective_iff.2 (Function.injective_id.sigma_map hf) (congrArg Word.toList (hinj hxy))

end Monoid.CoprodI
