/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.RealProjective.Homology
public import TauCeti.AlgebraicTopology.Cohomology.UniversalCoefficient

/-!
# The singular cohomology of real projective space

Let `k` be a commutative ring in which `2 = 0` or `2` is a unit. Then every singular homology
module `Hₙ(RPᴺ; k)`, computed from the CW structure of `RPᴺ` in
`TauCeti.AlgebraicTopology.Cellular.RealProjective.Homology`, is either zero or isomorphic to `k`,
so it is projective. The universal coefficient theorem with projective homology
(`TopCat.singularKroneckerEquivOfProjectiveHomology`) then identifies `Hᵈ(RPᴺ; k, M)` with the dual
`Hom(H_d(RPᴺ; k), M)`. The answer depends on the characteristic of `k`:

* if `2 = 0` in `k`, then `Hᵈ(RPᴺ; k)` has rank `1` for every `d ≤ N` and rank `0` above;
* if `2` is a unit in `k`, for instance `k = ℚ`, then `Hᵈ(RPᴺ; k, M)` vanishes in every positive
  degree `d`, except in degree `N` for odd `N`, and `Hᵈ(RPᴺ; k)` has rank `1` in degree `0` and,
  for odd `N`, in degree `N`. So over such a ring `RPᴺ` has the cohomology of a point for even `N`,
  and that of the sphere `Sᴺ` for odd `N`.

These are the inputs to the cup length of `RPᴺ`, and so to the cup-length lower bound for its
Lusternik–Schnirelmann category.

## Main declarations

* `TauCeti.RealProjectiveSpace.finrank_singularCohomology_of_two_eq_zero`: the ranks of the
  cohomology of `RPᴺ` when `2 = 0`.
* `TauCeti.RealProjectiveSpace.finrank_singularCohomology_of_isUnit_two`: the ranks of the
  cohomology of `RPᴺ` when `2` is a unit.
* `TauCeti.RealProjectiveSpace.subsingleton_singularCohomology_of_isUnit_two`: when `2` is a unit,
  the cohomology of `RPᴺ` vanishes in every positive degree other than an odd `N`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.2, Example 2.42, and Section 3.1, Theorem 3.2.
-/

public section

noncomputable section

open CategoryTheory Limits Module

namespace TauCeti.RealProjectiveSpace

variable {N : ℕ} {k : Type} [CommRing k]

/-- If `2 = 0` in `k`, then `Hₙ(RPᴺ; k) ≅ k` for `n ≤ N`. -/
private lemma nonempty_singularHomology_linearEquiv_of_two_eq_zero (h2 : (2 : k) = 0) {n : ℕ}
    (hn : n ≤ N) :
    Nonempty (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} k) n).obj
      (ModuleCat.of k k)).obj (TopCat.of (RealProjectiveSpace N)) ≃ₗ[k] k) := by
  rcases Nat.even_or_odd n with hn' | hn'
  · rcases eq_or_ne n 0 with rfl | hn0
    · exact ⟨singularHomologyZeroLinearEquiv k⟩
    · have hker : LinearMap.ker (LinearMap.toSpanSingleton k k 2) = ⊤ := by
        rw [h2, LinearMap.toSpanSingleton_zero, LinearMap.ker_zero]
      exact ⟨(singularHomologyLinearEquivOfEven k hn' hn0 hn).trans (LinearEquiv.ofTop _ hker)⟩
  · rcases hn.lt_or_eq with hn | rfl
    · have hspan : k ∙ (2 : k) = ⊥ := by rw [h2, Submodule.span_singleton_eq_bot]
      exact ⟨(singularHomologyLinearEquivOfOdd k hn' hn).trans
        (Submodule.quotEquivOfEqBot _ hspan)⟩
    · exact ⟨singularHomologyTopLinearEquivOfOdd k hn'⟩

/-- If `2` is a unit in `k`, then `Hₙ(RPᴺ; k)` vanishes in every positive degree `n`, except in
degree `N` when `N` is odd. -/
private lemma isZero_singularHomology_of_isUnit_two (h2 : IsUnit (2 : k)) {n : ℕ} (hn : n ≠ 0)
    (hnN : n = N → Even N) :
    IsZero (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} k) n).obj
      (ModuleCat.of k k)).obj (TopCat.of (RealProjectiveSpace N))) := by
  rcases n.even_or_odd with hn' | hn'
  · exact isZero_singularHomology_of_even k h2.isRegular.right hn' hn
  rcases lt_trichotomy n N with hlt | rfl | hlt
  · have : Subsingleton (k ⧸ k ∙ (2 : k)) :=
      Submodule.Quotient.subsingleton_iff.2 (Ideal.span_singleton_eq_top.2 h2)
    exact ModuleCat.isZero_iff_subsingleton.2
      (singularHomologyLinearEquivOfOdd k hn' hlt).toEquiv.subsingleton
  · exact absurd (hnN rfl) (Nat.not_even_iff_odd.2 hn')
  · exact isZero_singularHomology_of_lt k hlt

/-- A module isomorphic to `k` is projective. -/
private lemma projective_of_linearEquiv {P : ModuleCat.{0} k} (e : P ≃ₗ[k] k) : Projective P :=
  ModuleCat.projective_of_free ((Basis.singleton Unit k).map e.symm)

/-- If `2 = 0` or `2` is a unit in `k`, then every `Hₙ(RPᴺ; k)` is projective. -/
private lemma projective_singularHomology (h2 : (2 : k) = 0 ∨ IsUnit (2 : k)) (n : ℕ) :
    Projective (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} k) n).obj
      (ModuleCat.of k k)).obj (TopCat.of (RealProjectiveSpace N))) := by
  obtain h2 | h2 := h2
  · rcases le_or_gt n N with hn | hn
    · exact projective_of_linearEquiv
        (nonempty_singularHomology_linearEquiv_of_two_eq_zero h2 hn).some
    · exact (isZero_singularHomology_of_lt k hn).projective
  · by_cases hn : n = 0 ∨ n = N ∧ Odd N
    · rcases hn with rfl | ⟨rfl, hN⟩
      exacts [projective_of_linearEquiv (singularHomologyZeroLinearEquiv k),
        projective_of_linearEquiv (singularHomologyTopLinearEquivOfOdd k hN)]
    · refine (isZero_singularHomology_of_isUnit_two h2 (fun h ↦ hn (.inl h)) fun h ↦ ?_).projective
      exact Nat.not_odd_iff_even.1 fun hN ↦ hn (.inr ⟨h, hN⟩)

/-- If `2 = 0` or `2` is a unit in `k` and `H_d(RPᴺ; k) ≅ k`, then `Hᵈ(RPᴺ; k)` has rank `1`. -/
private lemma finrank_singularCohomology_eq_one [Nontrivial k]
    (h2 : (2 : k) = 0 ∨ IsUnit (2 : k)) {d : ℕ}
    (e : ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} k) d).obj
      (ModuleCat.of k k)).obj (TopCat.of (RealProjectiveSpace N)) ≃ₗ[k] k) :
    finrank k ((TopCat.of (RealProjectiveSpace N)).singularCohomology (ModuleCat.of k k) k
      (ModuleCat.of k k) d) = 1 := by
  have := projective_singularHomology (N := N) h2
  rw [((TopCat.of (RealProjectiveSpace N)).singularKroneckerEquivOfProjectiveHomology
    (ModuleCat.of k k) (ModuleCat.of k k) d ≪≫ₗ ModuleCat.homLinearEquiv ≪≫ₗ
    e.arrowCongr (LinearEquiv.refl k k) ≪≫ₗ LinearMap.ringLmapEquivSelf k k k).finrank_eq,
    finrank_self]

/-- If `2 = 0` or `2` is a unit in `k` and `H_d(RPᴺ; k) = 0`, then `Hᵈ(RPᴺ; k, M) = 0`. -/
private lemma subsingleton_singularCohomology_of_isZero (h2 : (2 : k) = 0 ∨ IsUnit (2 : k))
    (M : ModuleCat.{0} k) {d : ℕ}
    (h : IsZero (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} k) d).obj
      (ModuleCat.of k k)).obj (TopCat.of (RealProjectiveSpace N)))) :
    Subsingleton ((TopCat.of (RealProjectiveSpace N)).singularCohomology (ModuleCat.of k k) k M
      d) := by
  have := projective_singularHomology (N := N) h2
  have : Subsingleton (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} k) d).obj
      (ModuleCat.of k k)).obj (TopCat.of (RealProjectiveSpace N)) ⟶ M) := ⟨h.eq_of_src⟩
  exact ((TopCat.of (RealProjectiveSpace N)).singularKroneckerEquivOfProjectiveHomology
    (ModuleCat.of k k) M d).toEquiv.subsingleton

/-- **Cohomology of real projective space in characteristic two.** If `2 = 0` in the nontrivial
commutative ring `k`, then `finrank k Hᵈ(RPᴺ; k)` is `1` for `d ≤ N` and `0` for `d > N`. -/
theorem finrank_singularCohomology_of_two_eq_zero [Nontrivial k] (h2 : (2 : k) = 0) (d : ℕ) :
    finrank k ((TopCat.of (RealProjectiveSpace N)).singularCohomology (ModuleCat.of k k) k
      (ModuleCat.of k k) d) = if d ≤ N then 1 else 0 := by
  split_ifs with hd
  · exact finrank_singularCohomology_eq_one (.inl h2)
      (nonempty_singularHomology_linearEquiv_of_two_eq_zero h2 hd).some
  · have := subsingleton_singularCohomology_of_isZero (.inl h2) (ModuleCat.of k k)
      (isZero_singularHomology_of_lt (N := N) k (Nat.lt_of_not_le hd))
    exact finrank_zero_of_subsingleton

/-- If `2` is a unit in `k`, then `Hᵈ(RPᴺ; k, M)` vanishes in every positive degree `d`, except in
degree `N` when `N` is odd. -/
theorem subsingleton_singularCohomology_of_isUnit_two (h2 : IsUnit (2 : k)) (M : ModuleCat.{0} k)
    {d : ℕ} (hd : d ≠ 0) (hdN : d = N → Even N) :
    Subsingleton ((TopCat.of (RealProjectiveSpace N)).singularCohomology (ModuleCat.of k k) k M
      d) :=
  subsingleton_singularCohomology_of_isZero (.inr h2) M
    (isZero_singularHomology_of_isUnit_two h2 hd hdN)

/-- **Cohomology of real projective space away from characteristic two.** If `2` is a unit in the
nontrivial commutative ring `k`, for instance `k = ℚ`, then `finrank k Hᵈ(RPᴺ; k)` is `1` in degree
`0` and, for odd `N`, in degree `N`, and `0` in every other degree. -/
theorem finrank_singularCohomology_of_isUnit_two [Nontrivial k] (h2 : IsUnit (2 : k)) (d : ℕ) :
    finrank k ((TopCat.of (RealProjectiveSpace N)).singularCohomology (ModuleCat.of k k) k
      (ModuleCat.of k k) d) = if d = 0 ∨ d = N ∧ Odd N then 1 else 0 := by
  split_ifs with hd
  · rcases hd with rfl | ⟨rfl, hN⟩
    exacts [finrank_singularCohomology_eq_one (.inr h2) (singularHomologyZeroLinearEquiv k),
      finrank_singularCohomology_eq_one (.inr h2) (singularHomologyTopLinearEquivOfOdd k hN)]
  · have := subsingleton_singularCohomology_of_isUnit_two (N := N) h2 (ModuleCat.of k k)
      (d := d) (fun h ↦ hd (.inl h)) fun h ↦ Nat.not_odd_iff_even.1 fun hN ↦ hd (.inr ⟨h, hN⟩)
    exact finrank_zero_of_subsingleton

end TauCeti.RealProjectiveSpace
