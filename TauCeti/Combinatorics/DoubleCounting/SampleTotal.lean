/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Card
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Double counting of moves between weighted samples of pairs

Let `R` be a commutative semiring, `M : P → P → Set A` a family of "move sets" between points of
`P`, and `F : P → R` a function. A value `a : R` is a *sample total* of `F` with move-count
constant `c : R` (`TauCeti.IsSampleTotal M F c a`) if there is a finitely supported weight function
`w : P →₀ R` such that `a = ∑ x, w x * F x`, and `∑ x, w x * #(M x y) = c` for every `y : P` whose
incoming moves only originate at points where `F` is nonzero.

Given two such sample totals `a, b` with constants `c, d` and a map `m : P → Q` matching values
and bijectively matching moves on the support set `S`, double counting yields `b * c = d * a`.

## Main definitions and results

* `TauCeti.IsSampleTotal`: weighted sample total with constant incoming move count.
* `TauCeti.IsSampleTotal.zero`: the zero weight witnesses `IsSampleTotal M F 0 0`.
* `TauCeti.IsSampleTotal.smul`: scaling weights scales both `c` and `a`.
* `TauCeti.IsSampleTotal.mul_eq_mul_of_bijOn`: double counting yields `b * c = d * a`.

## Provenance

Adapted from `New.IsSampleTotal` and `New.IsSampleTotal.mul_eq_mul_of_bijOn` in
`src/Lib/GaloisRep/BaseChange/TwistedTraceIdentity.lean` of
[lsernau/grh-lean](https://github.com/lsernau/grh-lean), commit
`72fead102f663d5c7a407964a13dc0cf9d977207` (Apache 2.0, Copyright 2026 Anthropic, PBC).
-/

public section

namespace TauCeti

open Set Finsupp

section SampleTotal

variable {R : Type*} [CommSemiring R]

/-- There is a finitely supported weight `w : P →₀ R` such that `a = ∑ x, w x * F x` and
`∑ x, w x * (M x y).ncard = c` for every `y : P` such that `F x ≠ 0` whenever `M x y` is
nonempty. -/
def IsSampleTotal {P A : Type*} (M : P → P → Set A) (F : P → R) (c a : R) : Prop :=
  ∃ w : P →₀ R,
    a = lift R R P F w ∧
    ∀ y : P, (∀ x : P, ∀ g ∈ M x y, F x ≠ 0) → lift R R P (fun x ↦ ((M x y).ncard : R)) w = c

/-- The zero weight witnesses `IsSampleTotal M F 0 0`. -/
theorem IsSampleTotal.zero {P A : Type*} (M : P → P → Set A) (F : P → R) :
    IsSampleTotal M F (0 : R) 0 :=
  ⟨0, by simp, fun _ _ ↦ by simp⟩

/-- Scaling a sample total by `r : R` scales both the move-count constant `c` and the total `a`. -/
theorem IsSampleTotal.smul {P A : Type*} {M : P → P → Set A} {F : P → R} {c a : R}
    (h : IsSampleTotal M F c a) (r : R) :
    IsSampleTotal M F (r * c) (r * a) := by
  obtain ⟨w, rfl, hw⟩ := h
  refine ⟨r • w, by simp [map_smul, smul_eq_mul], fun y hy ↦ ?_⟩
  simp [map_smul, smul_eq_mul, hw y hy]

/-- Double counting of moves between two weighted samples. If `a` is a sample total of `F` with
constant `c` for moves `M`, `b` is a sample total of `F'` with constant `d` for moves `N`, `F` is
supported on `S`, `F' y = F x` whenever `x ∈ S` and `N y (m x)` is nonempty, and for each `y` with
`F' y ≠ 0` some `z` and `J` map `M x z` bijectively onto `{g ∈ N y (m x) | x ∈ S}` for every `x`,
then `b * c = d * a`. -/
theorem IsSampleTotal.mul_eq_mul_of_bijOn {P Q A B : Type*} {c d a b : R}
    {M : P → P → Set A} {N : Q → Q → Set B} {F : P → R} (F' : Q → R)
    (h_tot : IsSampleTotal M F c a) (h_tot' : IsSampleTotal N F' d b) (m : P → Q) (S : Set P)
    (hF_supp : ∀ x : P, F x ≠ 0 → x ∈ S)
    (hF'_eq : ∀ x ∈ S, ∀ y : Q, ∀ g ∈ N y (m x), F' y = F x)
    (h_bij : ∀ y : Q, F' y ≠ 0 →
      ∃ (z : P) (J : A → B), ∀ x : P, BijOn J (M x z) {g ∈ N y (m x) | x ∈ S}) :
    b * c = d * a := by
  obtain ⟨w, rfl, hw⟩ := h_tot
  obtain ⟨u, rfl, hu⟩ := h_tot'
  simp only [lift_apply, Finsupp.sum, smul_eq_mul] at hw hu ⊢
  have sum_from (y : Q) :
      F' y * c = F' y * ∑ x ∈ w.support, w x * ({g ∈ N y (m x) | x ∈ S}.ncard : R) := by
    by_cases hy : F' y = 0
    · simp [hy]
    obtain ⟨z, J, hJ⟩ := h_bij y hy
    have hF_ne_zero : ∀ x : P, ∀ g ∈ M x z, F x ≠ 0 := fun x g hg ↦ by
      obtain ⟨hg_move, hx_mem⟩ := (hJ x).mapsTo hg
      rwa [← hF'_eq x hx_mem y (J g) hg_move]
    simp only [← hw z hF_ne_zero, (hJ _).ncard_eq]
  have sum_to (x : P) :
      d * F x = F x * ∑ y ∈ u.support, u y * ((N y (m x)).ncard : R) := by
    by_cases hx : F x = 0
    · simp [hx]
    rw [← hu (m x) fun y g hg ↦ by rwa [hF'_eq x (hF_supp x hx) y g hg], mul_comm]
  have term_eq (x : P) (y : Q) :
      F' y * ({g ∈ N y (m x) | x ∈ S}.ncard : R) = F x * ((N y (m x)).ncard : R) := by
    by_cases hx : x ∈ S
    · obtain h_empty | ⟨g, hg⟩ := (N y (m x)).eq_empty_or_nonempty
      · simp [h_empty]
      · simp [hx, hF'_eq x hx y g hg]
    · simp [hx, not_imp_comm.mp (hF_supp x) hx]
  calc
    _ = ∑ y ∈ u.support, u y * (F' y * c) := by simp only [Finset.sum_mul, mul_assoc]
    _ = ∑ y ∈ u.support, ∑ x ∈ w.support,
          w x * u y * (F' y * ({g ∈ N y (m x) | x ∈ S}.ncard : R)) := by
      simp only [sum_from, Finset.mul_sum, mul_assoc, mul_left_comm]
    _ = ∑ x ∈ w.support, ∑ y ∈ u.support, w x * u y * (F x * ((N y (m x)).ncard : R)) := by
      simp only [term_eq]
      exact Finset.sum_comm
    _ = ∑ x ∈ w.support, w x * (d * F x) := by
      simp only [sum_to, Finset.mul_sum, mul_assoc, mul_left_comm]
    _ = _ := by simp only [Finset.mul_sum, mul_left_comm]

end SampleTotal

end TauCeti
