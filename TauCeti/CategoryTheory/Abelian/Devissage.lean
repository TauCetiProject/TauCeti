/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.ObjectProperty.Basic
import Mathlib.CategoryTheory.Abelian.Exact

/-!
# Dévissage along short exact sequences

Let `f X n : A X n → B X n` be a family of maps indexed by the objects `X` of a category with zero
morphisms and by the degrees `n : ℕ`, typically a natural map between two contravariant
cohomological functors such as `Extⁿ(-, Y)`. Order the conditions on `f` at `X` as

`f X 0` injective, `f X 0` surjective, `f X 1` injective, `f X 1` surjective, …

For a morphism of contravariant cohomological δ-functors, the four lemma applied to the long exact
sequences of a short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` derives each condition at `X₃` from
the conditions up to it at `X₂` and those before it at `X₁`: injectivity in degree `n` at `X₃`
follows from bijectivity below `n` at `X₁` and `X₂` and injectivity in degree `n` at `X₂`, and
surjectivity in degree `n` at `X₃` follows from bijectivity below `n` at `X₁`, injectivity in
degree `n` at `X₁` and bijectivity up to degree `n` at `X₂`. The theorems below take these two
steps as their hypotheses `hinj` and `hsurj`, and prove the conditions in their order, at all
objects of a class at once: the kernel of a presentation `0 ⟶ K ⟶ Q ⟶ X ⟶ 0` by an object `Q` at
which `f` is bijective supplies the conditions before the current one (dimension shifting).

## Main results

* `TauCeti.bijective_of_forall_exists_shortExact`: if every object `X` of a class `P` is the
  cokernel of a short exact sequence `0 ⟶ K ⟶ Q ⟶ X ⟶ 0` with `K` in `P` and `f Q n` bijective for
  every `n`, then `f X n` is bijective for every `X` in `P` and every `n`. This applies to the chain
  of short exact sequences into which a resolution is cut.
* `TauCeti.bijective_of_forall_exists_epi`: in an abelian category, if every object is a quotient
  of an object at which `f` is bijective in all degrees, then `f` is bijective in all degrees at
  every object.

## References

* C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge Studies in Advanced
  Mathematics 38, Cambridge University Press, 1994, Section 2.4 (dimension shifting).
* `grh-lean`, https://github.com/lsernau/grh-lean, file
  `src/Lib/Cohomology/LerayHirsch.lean` (declaration
  `New.Variety.Devissage.allBijective_of_allBijective_sigma_reprBy`); Apache 2.0, Copyright 2026
  Anthropic, PBC. The formulation of the hypotheses through the ordered conditions follows it; the
  statements here are for a category with zero morphisms, respectively an abelian category.
-/
public section

open CategoryTheory hiding Injective
open Limits Function

namespace TauCeti

variable {𝒜 : Type*} [Category* 𝒜] {A B : 𝒜 → ℕ → Type*} {f : ∀ X n, A X n → B X n}

/-- **Dévissage along short exact sequences.** Let `f X n : A X n → B X n` be maps such that, for
every short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` and every `n`, if `f` is bijective below `n` at
`X₁` and `X₂`, then injectivity of `f X₂ n` gives injectivity of `f X₃ n` (`hinj`), and injectivity
of `f X₁ n` together with bijectivity of `f X₂ n` gives surjectivity of `f X₃ n` (`hsurj`). Let `P`
be a class of objects each of which is the cokernel of a short exact sequence `0 ⟶ K ⟶ Q ⟶ X ⟶ 0`
with `K` in `P` and `f Q n` bijective for every `n`. Then `f X n` is bijective for every `X` in `P`
and every `n`. -/
theorem bijective_of_forall_exists_shortExact [HasZeroMorphisms 𝒜] {P : ObjectProperty 𝒜}
    (hinj : ∀ ⦃S : ShortComplex 𝒜⦄, S.ShortExact → ∀ n, (∀ m < n, Bijective (f S.X₁ m)) →
      (∀ m < n, Bijective (f S.X₂ m)) → Injective (f S.X₂ n) → Injective (f S.X₃ n))
    (hsurj : ∀ ⦃S : ShortComplex 𝒜⦄, S.ShortExact → ∀ n, (∀ m < n, Bijective (f S.X₁ m)) →
      Injective (f S.X₁ n) → (∀ m ≤ n, Bijective (f S.X₂ m)) → Surjective (f S.X₃ n))
    (hP : ∀ X, P X → ∃ (K Q : 𝒜) (i : K ⟶ Q) (p : Q ⟶ X) (w : i ≫ p = 0),
      (ShortComplex.mk i p w).ShortExact ∧ P K ∧ ∀ n, Bijective (f Q n))
    {X : 𝒜} (hX : P X) (n : ℕ) : Bijective (f X n) := by
  induction n using Nat.strong_induction_on generalizing X with
  | _ n ih =>
  -- First injectivity in degree `n` at every member of `P`, then surjectivity, which uses
  -- injectivity at the kernel of the presentation.
  have hi : ∀ X, P X → Injective (f X n) := fun X hX ↦ by
    obtain ⟨K, Q, i, p, w, hS, hK, hQ⟩ := hP X hX
    exact hinj hS n (fun m hm ↦ ih m hm hK) (fun m _ ↦ hQ m) (hQ n).1
  obtain ⟨K, Q, i, p, w, hS, hK, hQ⟩ := hP X hX
  exact ⟨hi X hX, hsurj hS n (fun m hm ↦ ih m hm hK) (hi K hK) fun m _ ↦ hQ m⟩

/-- **Dévissage from a class of presenting objects.** In an abelian category, let
`f X n : A X n → B X n` be maps satisfying the two steps `hinj` and `hsurj` of
`TauCeti.bijective_of_forall_exists_shortExact` along short exact sequences. If every object is a
quotient of an object at which `f` is bijective in all degrees, then `f` is bijective in all
degrees at every object. -/
theorem bijective_of_forall_exists_epi [Abelian 𝒜]
    (hinj : ∀ ⦃S : ShortComplex 𝒜⦄, S.ShortExact → ∀ n, (∀ m < n, Bijective (f S.X₁ m)) →
      (∀ m < n, Bijective (f S.X₂ m)) → Injective (f S.X₂ n) → Injective (f S.X₃ n))
    (hsurj : ∀ ⦃S : ShortComplex 𝒜⦄, S.ShortExact → ∀ n, (∀ m < n, Bijective (f S.X₁ m)) →
      Injective (f S.X₁ n) → (∀ m ≤ n, Bijective (f S.X₂ m)) → Surjective (f S.X₃ n))
    (h : ∀ X, ∃ (Q : 𝒜) (p : Q ⟶ X), Epi p ∧ ∀ n, Bijective (f Q n)) (X : 𝒜) (n : ℕ) :
    Bijective (f X n) :=
  bijective_of_forall_exists_shortExact (P := ⊤) hinj hsurj (fun X _ ↦ by
    obtain ⟨Q, p, hp, hQ⟩ := h X
    exact ⟨_, Q, kernel.ι p, p, kernel.condition p, { exact := ShortComplex.exact_kernel p },
      trivial, hQ⟩) trivial n

end TauCeti
