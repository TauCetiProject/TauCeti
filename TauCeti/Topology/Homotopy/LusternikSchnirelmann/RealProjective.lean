/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.RealProjective.Cohomology
public import TauCeti.AlgebraicTopology.Cellular.RealProjective.Cup
public import TauCeti.AlgebraicTopology.UniversalCover.RealProjective.Projectivization
public import TauCeti.Topology.Homotopy.LusternikSchnirelmann.CupLength

/-!
# The cup length of real projective space

Over a nontrivial commutative ring `k` in which `2` is a unit, for instance `k = ℚ`, the cohomology
of `RPᴺ` is that of a point for even `N` and that of the sphere `Sᴺ` for odd `N`
(`TauCeti.RealProjectiveSpace.finrank_singularCohomology_of_isUnit_two`). So its cup length over
`k` is `0` for even `N`, since every class of positive degree vanishes, and `1` for odd `N`: the
top class is nonzero, while a product of two classes of positive degree vanishes, since it would
lie in degree `2N`.

For even `N`, in particular for the real projective plane, the cup-length lower bound
`lsCupLength X k + 1 ≤ lsCategoryCount X univ` therefore gives no information over such a ring:
it only says that the nonempty space `RPᴺ` needs at least one categorical open set.

The coefficients matter: over `ZMod 2` the cohomology ring of `RPᴺ` is `𝔽₂[α] / (α ^ (N + 1))`
with `α` of degree `1` (Hatcher, Theorem 3.12), so its cup length there is `N`. This file proves
the part of that computation which uses only the square of `α`: for `N ≥ 2` the square `α ⌣ α` is
nonzero (`TauCeti.RealProjectiveSpace.singularCup_self_eq_zero_iff`), so the cup length over
`ZMod 2` is at least `2`. Since the cohomology of `RPᴺ` vanishes above degree `N`, the cup length
of the real projective plane over `ZMod 2` is exactly `2`, and the cup-length lower bound gives
that it needs at least three categorical open sets.

## Main results

* `TauCeti.lsCupLength_realProjectiveSpace_of_isUnit_two`: the cup length of `RPᴺ` over a
  nontrivial commutative ring in which `2` is a unit is `1` for odd `N` and `0` for even `N`.
* `TauCeti.lsCupLength_projectivization_real_of_isUnit_two`: the same for the projectivization
  `ℙ ℝ (Fin (N + 1) → ℝ)`.
* `TauCeti.lsCupLength_realProjectiveSpace_le`: if `2 = 0` or `2` is a unit, the cup length of
  `RPᴺ` is at most `N`.
* `TauCeti.two_le_lsCupLength_realProjectiveSpace_zmod_two` and
  `TauCeti.two_le_lsCupLength_projectivization_real_zmod_two`: for `N ≥ 2` the cup length of `RPᴺ`
  over `ZMod 2` is at least `2`.
* `TauCeti.lsCupLength_realProjectiveSpace_two_zmod_two` and
  `TauCeti.lsCupLength_projectivization_real_fin_three_zmod_two`: the cup length of the real
  projective plane over `ZMod 2` is `2`.
* `TauCeti.three_le_lsCategoryCount_univ_realProjectiveSpace` and
  `TauCeti.three_le_lsCategoryCount_univ_projectivization_real`: for `N ≥ 2`, the
  Lusternik–Schnirelmann count of `RPᴺ` is at least `3`.

## References

* O. Cornea, G. Lupton, J. Oprea and D. Tanré, *Lusternik–Schnirelmann Category*, Mathematical
  Surveys and Monographs 103, American Mathematical Society, 2003, Chapter 1.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.2, Theorem 3.12, the cohomology rings of real projective spaces.
-/

public section

noncomputable section

open scoped LinearAlgebra.Projectivization

namespace TauCeti

open RealProjectiveSpace

variable {N : ℕ} {k : Type} [CommRing k] [Nontrivial k]

/-- **The cup length of real projective space away from characteristic two.** If `2` is a unit in
the nontrivial commutative ring `k`, for instance `k = ℚ`, the cup length of `RPᴺ` over `k` is `1`
for odd `N` and `0` for even `N`. -/
theorem lsCupLength_realProjectiveSpace_of_isUnit_two (h2 : IsUnit (2 : k)) :
    lsCupLength (RealProjectiveSpace N) k = if Odd N then 1 else 0 := by
  split_ifs with hN
  · refine le_antisymm (lsCupLength_le_one_of_subsingleton (N := N) fun p hp hpN ↦
      subsingleton_singularCohomology_of_isUnit_two h2 _ hp fun h ↦ absurd h hpN) ?_
    -- The top class of `RPᴺ` is nonzero, since `Hᴺ(RPᴺ; k)` is one-dimensional.
    have hrank := finrank_singularCohomology_of_isUnit_two (N := N) h2 N
    rw [ite_eq_left (Or.inr ⟨rfl, hN⟩)] at hrank
    have := Module.nontrivial_of_finrank_pos (R := k) (hrank ▸ one_pos)
    obtain ⟨a, ha⟩ := exists_ne (0 : (TopCat.of (RealProjectiveSpace N)).singularCohomology
      (ModuleCat.of k k) k (ModuleCat.of k k) N)
    exact_mod_cast le_lsCupLength (.single hN.pos.ne' a) ha
  · exact lsCupLength_eq_zero_iff.2 fun p hp a ↦
      (subsingleton_singularCohomology_of_isUnit_two h2 _ hp fun _ ↦
        Nat.not_odd_iff_even.1 hN).elim a 0

/-- **The cup length of the projectivization of `ℝᴺ⁺¹` away from characteristic two.** If `2` is a
unit in the nontrivial commutative ring `k`, for instance `k = ℚ`, the cup length of
`ℙ ℝ (Fin (N + 1) → ℝ)` over `k` is `1` for odd `N` and `0` for even `N`. -/
theorem lsCupLength_projectivization_real_of_isUnit_two (h2 : IsUnit (2 : k)) :
    lsCupLength (ℙ ℝ (Fin (N + 1) → ℝ)) k = if Odd N then 1 else 0 := by
  rw [← (homeomorphProjectivization N).toHomotopyEquiv.lsCupLength_eq,
    lsCupLength_realProjectiveSpace_of_isUnit_two h2]

omit [Nontrivial k] in
/-- **The cup length of real projective space is at most its dimension**, over a commutative ring
`k` in which `2 = 0` or `2` is a unit, since the cohomology of `RPᴺ` vanishes above degree `N`. -/
theorem lsCupLength_realProjectiveSpace_le (h2 : (2 : k) = 0 ∨ IsUnit (2 : k)) :
    lsCupLength (RealProjectiveSpace N) k ≤ N :=
  lsCupLength_le_of_subsingleton fun _ hp ↦ subsingleton_singularCohomology_of_lt h2 _ hp

/-- **The mod-two cup length of real projective space is at least two**: for `N ≥ 2`, the cup
length of `RPᴺ` over `ZMod 2` is at least `2`. -/
theorem two_le_lsCupLength_realProjectiveSpace_zmod_two (hN : 2 ≤ N) :
    2 ≤ lsCupLength (RealProjectiveSpace N) (ZMod 2) := by
  have hrank := finrank_singularCohomology_of_two_eq_zero (N := N) (k := ZMod 2) (by decide) 1
  rw [ite_eq_left (by omega)] at hrank
  have := Module.nontrivial_of_finrank_pos (R := ZMod 2) (hrank ▸ one_pos)
  -- `w` lives in cohomology with coefficients `ModuleCat.of (ZMod 2) (ZMod 2)`, where `hrank`
  -- gives the nontriviality, while the cup product and `lsCupLength` use the monoidal unit
  -- `𝟙_ (ModuleCat (ZMod 2))`; the two agree by definition in Mathlib's monoidal structure on
  -- `ModuleCat (ZMod 2)`.
  obtain ⟨w, hw⟩ := exists_ne (0 : (TopCat.of (RealProjectiveSpace N)).singularCohomology
    (ModuleCat.of (ZMod 2) (ZMod 2)) (ZMod 2) (ModuleCat.of (ZMod 2) (ZMod 2)) 1)
  exact_mod_cast le_lsCupLength (.cup one_ne_zero rfl w (.single one_ne_zero w))
    ((singularCup_self_eq_zero_iff hN).not.2 hw)

/-- **The mod-two cup length of the real projective plane** is `2`. -/
theorem lsCupLength_realProjectiveSpace_two_zmod_two :
    lsCupLength (RealProjectiveSpace 2) (ZMod 2) = 2 :=
  le_antisymm (lsCupLength_le_of_subsingleton fun _ hp ↦
      subsingleton_singularCohomology_of_lt (.inl (by decide)) _ hp)
    (two_le_lsCupLength_realProjectiveSpace_zmod_two le_rfl)

/-- **The mod-two cup length of the projectivization of `ℝᴺ⁺¹` is at least two**: for `N ≥ 2`,
the cup length of `ℙ ℝ (Fin (N + 1) → ℝ)` over `ZMod 2` is at least `2`. -/
theorem two_le_lsCupLength_projectivization_real_zmod_two (hN : 2 ≤ N) :
    2 ≤ lsCupLength (ℙ ℝ (Fin (N + 1) → ℝ)) (ZMod 2) := by
  rw [← (homeomorphProjectivization N).toHomotopyEquiv.lsCupLength_eq]
  exact two_le_lsCupLength_realProjectiveSpace_zmod_two hN

/-- **The mod-two cup length of `ℙ ℝ (Fin 3 → ℝ)`**, the real projective plane, is `2`. -/
theorem lsCupLength_projectivization_real_fin_three_zmod_two :
    lsCupLength (ℙ ℝ (Fin 3 → ℝ)) (ZMod 2) = 2 := by
  rw [← (homeomorphProjectivization 2).toHomotopyEquiv.lsCupLength_eq,
    lsCupLength_realProjectiveSpace_two_zmod_two]

/-- **Real projective space needs three categorical open sets.** For `N ≥ 2`, the
Lusternik–Schnirelmann count of `RPᴺ` is at least `3`, by the cup-length bound over `ZMod 2`. -/
theorem three_le_lsCategoryCount_univ_realProjectiveSpace (hN : 2 ≤ N) :
    3 ≤ lsCategoryCount (RealProjectiveSpace N) Set.univ :=
  (add_le_add_left (two_le_lsCupLength_realProjectiveSpace_zmod_two hN) 1).trans
    (lsCupLength_add_one_le_lsCategoryCount_univ (R := ZMod 2))

/-- For `N ≥ 2`, the Lusternik–Schnirelmann count of the projectivization of `ℝᴺ⁺¹` is at least
`3`. -/
theorem three_le_lsCategoryCount_univ_projectivization_real (hN : 2 ≤ N) :
    3 ≤ lsCategoryCount (ℙ ℝ (Fin (N + 1) → ℝ)) Set.univ := by
  rw [← (homeomorphProjectivization N).toHomotopyEquiv.lsCategoryCount_univ_eq]
  exact three_le_lsCategoryCount_univ_realProjectiveSpace hN

end TauCeti
