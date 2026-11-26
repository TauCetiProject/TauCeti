/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Coprod.Basic
import TauCeti.GroupTheory.Coprod.Factors

/-!
# Uniqueness of reduced words in a free product

A word in the letters `M ⊕ N` is *reduced* when none of its letters is `1` and consecutive letters
lie in different factors. Distinct reduced words have distinct images in the free product `M ∗ N`.
This is the uniqueness part of the normal form theorem for free products; in particular the image of
a nonempty reduced word is not `1`.

Consequently a pair of homomorphisms `f : M →* M'`, `g : N →* N'` keeps a nonidentity element of
`M ∗ N` away from `1` as soon as it keeps every letter of one of its reduced words away from `1`:
the image under `Monoid.Coprod.map f g` of the word is again a nonempty reduced word.

## Main results

* `Monoid.Coprod.mk_ofList_inj`: two reduced words with the same image in `M ∗ N` are equal.
* `Monoid.Coprod.mk_ofList_ne_one`: the image of a nonempty reduced word is not `1`.
* `Monoid.Coprod.map_mk_ofList_ne_one`: `Monoid.Coprod.map f g` sends a nonempty reduced word
  to an element other than `1` when `f` and `g` send none of its letters to `1`.

## Implementation notes

Mathlib builds `M ∗ N` independently of the free product `Monoid.CoprodI` of an indexed family.
The free product of two monoids, possibly in different universes, is identified with the free
product `Monoid.CoprodI` of the family `Monoid.Coprod.Factors M N` of their `ULift`s indexed by
`Bool` (`Monoid.Coprod.equivCoprodI`), whose reduced words are unique (`Monoid.CoprodI.Word.equiv`),
and reduced words of `M ∗ N` go to reduced words there.

## References

* R. C. Lyndon, P. E. Schupp, *Combinatorial group theory*, Springer, 1977, Chapter IV, §1
  (the normal form theorem for free products).
-/

public section

namespace Monoid.Coprod

universe u v

section Monoid

variable {M : Type u} {N : Type v}

/-! ### Reduced words of `M ∗ N` as reduced words of `Monoid.CoprodI` -/

-- `toSigma` is reducible so that unification identifies the factor `(toSigma s).1` of a letter
-- `s = .inl m` with `false` (and of `s = .inr n` with `true`): `simp` cannot rewrite `toSigma s`
-- inside the dependent index of `Monoid.CoprodI.of`.
/-- A letter of `M ⊕ N` as a letter of the family `Factors M N`. -/
private abbrev toSigma : M ⊕ N → Σ b, Factors M N b
  | .inl m => ⟨false, ULift.up m⟩
  | .inr n => ⟨true, ULift.up n⟩

private theorem toSigma_fst (s : M ⊕ N) : (toSigma s).1 = s.isRight := by
  cases s <;> rfl

private theorem toSigma_injective : Function.Injective (toSigma (M := M) (N := N)) := by
  rintro (m | n) (m' | n') h <;> simp_all [toSigma]

variable [Monoid M] [Monoid N]

private theorem equivCoprodI_mk_ofList (L : List (M ⊕ N)) :
    equivCoprodI (mk (FreeMonoid.ofList L)) = (L.map fun s => CoprodI.of (toSigma s).2).prod := by
  induction L with
  | nil => simp
  | cons s L ih =>
    rw [FreeMonoid.ofList_cons, map_mul, map_mul, ih, List.map_cons, List.prod_cons]
    cases s <;> simp [toSigma]

/-- A reduced word of `M ∗ N` as a reduced word of `Monoid.CoprodI (Factors M N)`. -/
private def toWord (L : List (M ⊕ N)) (hc : (L.map Sum.isRight).IsChain (· ≠ ·))
    (h₁ : Sum.inl 1 ∉ L) (h₂ : Sum.inr 1 ∉ L) : CoprodI.Word (Factors M N) where
  toList := L.map toSigma
  ne_one := by
    simp only [List.mem_map, forall_exists_index, and_imp]
    rintro _ (m | n) hs rfl h <;> simp_all [toSigma, ULift.ext_iff]
  chain_ne := by
    rw [List.isChain_map]
    simpa [toSigma_fst, List.isChain_map] using hc

private theorem prod_toWord (L : List (M ⊕ N)) (hc : (L.map Sum.isRight).IsChain (· ≠ ·))
    (h₁ : Sum.inl 1 ∉ L) (h₂ : Sum.inr 1 ∉ L) :
    (toWord L hc h₁ h₂).prod = equivCoprodI (mk (FreeMonoid.ofList L)) := by
  simp [CoprodI.Word.prod, toWord, equivCoprodI_mk_ofList, Function.comp_def]

/-! ### Uniqueness of reduced words -/

/-- **Uniqueness of reduced words in a free product.** Two words in the letters `M ⊕ N`, none of
whose letters is `1` and whose consecutive letters lie in different factors, have the same image
in `M ∗ N` only if they are equal. -/
@[simp]
theorem mk_ofList_inj {L L' : List (M ⊕ N)} (hc : (L.map Sum.isRight).IsChain (· ≠ ·))
    (h₁ : Sum.inl 1 ∉ L) (h₂ : Sum.inr 1 ∉ L) (hc' : (L'.map Sum.isRight).IsChain (· ≠ ·))
    (h₁' : Sum.inl 1 ∉ L') (h₂' : Sum.inr 1 ∉ L') :
    (mk (FreeMonoid.ofList L) : M ∗ N) = mk (FreeMonoid.ofList L') ↔ L = L' := by
  classical
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  -- The corresponding reduced words of `Monoid.CoprodI` have the same product. A reduced word is
  -- determined by its product: `Word.prod` is, by definition, the inverse of the bijection
  -- `Word.equiv` from `Monoid.CoprodI` to its reduced words.
  have hprod : Function.Injective (CoprodI.Word.prod (M := Factors M N)) :=
    CoprodI.Word.equiv.symm.injective
  have hw : toWord L hc h₁ h₂ = toWord L' hc' h₁' h₂' :=
    hprod (by rw [prod_toWord, prod_toWord, h])
  exact List.map_injective_iff.2 toSigma_injective (congrArg CoprodI.Word.toList hw)

/-- The image in `M ∗ N` of a nonempty word in the letters `M ⊕ N`, none of whose letters is `1`
and whose consecutive letters lie in different factors, is not `1`. -/
@[simp]
theorem mk_ofList_ne_one {L : List (M ⊕ N)} (hL : L ≠ []) (hc : (L.map Sum.isRight).IsChain (· ≠ ·))
    (h₁ : Sum.inl 1 ∉ L) (h₂ : Sum.inr 1 ∉ L) : (mk (FreeMonoid.ofList L) : M ∗ N) ≠ 1 := fun h =>
  hL ((mk_ofList_inj (L' := []) hc h₁ h₂ (by simp) (by simp) (by simp)).1 (by simpa using h))

end Monoid

/-- Let `L` be a nonempty word in the letters `M ⊕ N` whose consecutive letters lie in different
factors. If `f : M →* M'` and `g : N →* N'` send none of the letters of `L` to `1`, then
`Monoid.Coprod.map f g` does not send the image of `L` to `1`. -/
theorem map_mk_ofList_ne_one {M N M' N' : Type*} [MulOneClass M] [MulOneClass N] [Monoid M']
    [Monoid N'] (f : M →* M') (g : N →* N') {L : List (M ⊕ N)} (hL : L ≠ [])
    (hc : (L.map Sum.isRight).IsChain (· ≠ ·)) (hf : ∀ m, Sum.inl m ∈ L → f m ≠ 1)
    (hg : ∀ n, Sum.inr n ∈ L → g n ≠ 1) : map f g (mk (FreeMonoid.ofList L)) ≠ 1 := by
  rw [map_mk_ofList]
  -- The image of `L` is again a nonempty reduced word.
  refine mk_ofList_ne_one (by simpa using hL) (by simpa [List.map_map, Function.comp_def] using hc)
    ?_ ?_
  · simpa using hf
  · simpa using hg

end Monoid.Coprod
