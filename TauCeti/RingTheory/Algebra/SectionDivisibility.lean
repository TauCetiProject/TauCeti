/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.SetTheory.Cardinal.Finite

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Card

/-!
# Vanishing along finitely many algebra sections with bounded divisibility

Let `S` be a commutative `O`-algebra, `θ : J → S →ₐ[O] O` a finite family of sections, `k` a
commutative `O`-algebra with an `O`-algebra map `o : S →ₐ[O] k`, and `χ : S →+* B` a ring
homomorphism sending every element of `S` outside `ker o` to a unit of `B`. Given `T : S` and
`g : B` such that `χ (algebraMap O S (θ j T) - T) ∣ g` for every section `θ j` passing through `o`
(meaning `algebraMap O k (θ j a) = o a` for all `a : S`), there exists an element `F : S`
vanishing along all `θ j` whose image `χ F` divides `g ^ N`, where `N` is the number of sections
`θ j` passing through `o`.

## Main results

* `Algebra.exists_dvd_pow_card_of_sections`: existence of `F : S` vanishing along every `θ j` with
  `χ F ∣ g ^ Nat.card {j : J // ∀ a : S, algebraMap O k (θ j a) = o a}`.

## Proof idea

For each `j : J`, choose a factor `y j : S` with `θ j (y j) = 0`: if `θ j` passes through `o`, take
`algebraMap O S (θ j T) - T` (whose image under `χ` divides `g`); otherwise pick `a : S` with
`algebraMap O k (θ j a) ≠ o a` and take `algebraMap O S (θ j a) - a`, whose image under `χ` is a
unit and hence divides `1`. The product `F = ∏ j, y j` vanishes along every `θ j` and satisfies
`χ F ∣ g ^ N`.

## Provenance

Adapted from grh-lean (https://github.com/lsernau/grh-lean at commit
`72fead102f663d5c7a407964a13dc0cf9d977207`, Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/Lib/Shimura/CongruenceRelation/KernelReduction.lean` (`exists_dvd_pow_card_of_sections`),
generalized from a field `k` to an arbitrary commutative `O`-algebra `k`.
-/

@[expose] public section

namespace Algebra

/-- Given a finite family of sections `θ : J → S →ₐ[O] O` of a commutative `O`-algebra `S`, an
`O`-algebra map `o : S →ₐ[O] k`, and a ring homomorphism `χ : S →+* B` sending elements outside
`ker o` to units, if `χ (algebraMap O S (θ j T) - T) ∣ g` whenever `θ j` passes through `o`, then
some `F : S` vanishes along every `θ j` and satisfies `χ F ∣ g ^ N`, where `N` counts the sections
passing through `o`. -/
theorem exists_dvd_pow_card_of_sections {O S k B J : Type*} [CommRing O] [CommRing S]
    [Algebra O S] [CommRing k] [Algebra O k] [CommRing B] [Finite J] {o : S →ₐ[O] k} {T : S}
    (θ : J → S →ₐ[O] O) {χ : S →+* B} (hχ : ∀ a : S, o a ≠ 0 → IsUnit (χ a)) {g : B}
    (hg : ∀ j : J, (∀ a : S, algebraMap O k (θ j a) = o a) →
      χ (algebraMap O S (θ j T) - T) ∣ g) :
    ∃ F : S, (∀ j : J, θ j F = 0) ∧
      χ F ∣ g ^ Nat.card {j : J // ∀ a : S, algebraMap O k (θ j a) = o a} := by
  classical
  cases nonempty_fintype J
  have h_factor (j : J) : ∃ y : S, θ j y = 0 ∧
      χ y ∣ if ∀ a : S, algebraMap O k (θ j a) = o a then g else 1 := by
    split_ifs with hj
    · exact ⟨algebraMap O S (θ j T) - T, by simp, hg j hj⟩
    · obtain ⟨a, ha⟩ := not_forall.mp hj
      have ho : o (algebraMap O S (θ j a) - a) ≠ 0 := by
        simpa [sub_eq_zero] using ha
      exact ⟨algebraMap O S (θ j a) - a, by simp, (hχ _ ho).dvd⟩
  choose y hy_zero hy_dvd using h_factor
  refine ⟨∏ j : J, y j, fun j ↦ ?_, ?_⟩
  · exact (map_prod (θ j) y Finset.univ).trans (Finset.prod_eq_zero (Finset.mem_univ j) (hy_zero j))
  · calc χ (∏ j : J, y j) = ∏ j : J, χ (y j) := map_prod χ y Finset.univ
      _ ∣ ∏ j : J, if ∀ a : S, algebraMap O k (θ j a) = o a then g else 1 :=
        Finset.univ.prod_dvd_prod_of_dvd _ _ fun j _ ↦ hy_dvd j
      _ = g ^ Nat.card {j : J // ∀ a : S, algebraMap O k (θ j a) = o a} := by
        simp [Finset.prod_ite, Nat.card_eq_fintype_card, Fintype.card_subtype]

end Algebra
