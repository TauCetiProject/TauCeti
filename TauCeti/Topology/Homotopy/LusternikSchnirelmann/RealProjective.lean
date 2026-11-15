/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.RealProjective.Cohomology
public import TauCeti.AlgebraicTopology.UniversalCover.RealProjective.Projectivization
public import TauCeti.Topology.Homotopy.LusternikSchnirelmann.CupLength

/-!
# The cup length of real projective space away from characteristic two

Over a nontrivial commutative ring `k` in which `2` is a unit, for instance `k = ℚ`, the cohomology
of `RPᴺ` is that of a point for even `N` and that of the sphere `Sᴺ` for odd `N`
(`TauCeti.RealProjectiveSpace.finrank_singularCohomology_of_isUnit_two`). So its cup length over
`k` is `0` for even `N`, since every class of positive degree vanishes, and `1` for odd `N`: the
top class is nonzero, while a product of two classes of positive degree vanishes, since it would
lie in degree `2N`.

For even `N`, in particular for the real projective plane, the cup-length lower bound
`lsCupLength X k + 1 ≤ lsCategoryCount X univ` therefore gives no information over such a ring:
it only says that the nonempty space `RPᴺ` needs at least one categorical open set. The
coefficients matter: over `ZMod 2` the cohomology ring of `RPᴺ` is `𝔽₂[α] / (α ^ (N + 1))` with `α`
of degree `1` (Hatcher, Theorem 3.12), so its cup length there is `N`. That computation needs the
mod `2` cup product of `RPᴺ` and is not made here.

## Main results

* `TauCeti.lsCupLength_realProjectiveSpace_of_isUnit_two`: the cup length of `RPᴺ` over a
  nontrivial commutative ring in which `2` is a unit is `1` for odd `N` and `0` for even `N`.
* `TauCeti.lsCupLength_projectivization_real_of_isUnit_two`: the same for the projectivization
  `ℙ ℝ (Fin (N + 1) → ℝ)`.

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

end TauCeti
