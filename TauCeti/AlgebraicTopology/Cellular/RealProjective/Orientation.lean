/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.RealProjective.Homology
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Character
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Smooth
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.TopHomology
public import TauCeti.AlgebraicTopology.UniversalCover.RealProjective.FundamentalGroup.Classification
public import TauCeti.Geometry.Manifold.Instances.Projectivization
import TauCeti.AlgebraicTopology.Singular.LocalHomology.FundamentalClass

/-!
# Orientability of real projective space

Real projective space `ℝℙᴺ = ℙ ℝ (Fin (N + 1) → ℝ)`, a compact connected manifold of dimension
`N` modelled on `Fin N → ℝ`, is orientable exactly when `N` is zero or odd
(`TauCeti.RealProjectiveSpace.nonempty_homologicalOrientation_projectivization_iff`). This is read
off its integral top homology: a compact connected manifold of dimension `N` is orientable exactly
when `H_N(M; ℤ)` is nonzero
(`TauCeti.nontrivial_singularHomology_iff_nonempty_homologicalOrientation`), and the cellular
computation gives `H_N(ℝℙᴺ; ℤ) ≅ ℤ` for `N` odd or zero and `H_N(ℝℙᴺ; ℤ) = 0` for `N` even and
positive (`TauCeti.RealProjectiveSpace.nontrivial_singularHomology_projectivization_top_iff`).

For `N` even and positive the orientation character `w₁ : π₁(ℝℙᴺ, x) →* ℤˣ` is therefore
nontrivial. Since `π₁(ℝℙᴺ, x)` has two elements, it is an isomorphism onto `ℤˣ`
(`TauCeti.RealProjectiveSpace.bijective_orientationCharacter_projectivization`): transport along
the nontrivial loop class reverses the local orientations
(`TauCeti.RealProjectiveSpace.orientationCharacter_projectivization_eq_neg_one_iff`). In
particular `ℝℙ²` is not orientable, its integral top homology `H₂(ℝℙ²; ℤ)` vanishes, and a
statement about a nonorientable base such as `ℝℙ²` needs coefficients twisted by its orientation
local system.

A smooth orientation is a homological one
(`TauCeti.Manifold.Orientation.toHomologicalOrientation`), so for `N` even and positive `ℝℙᴺ` is
not orientable as a smooth manifold either
(`TauCeti.RealProjectiveSpace.not_orientable_projectivization_of_even`); by
`TauCeti.orientable_iff_nonempty_vectorBundleOrientation`, its tangent bundle then has no
orientation as a vector bundle.

## Main results

* `TauCeti.RealProjectiveSpace.nonempty_homologicalOrientation_projectivization_iff`: `ℝℙᴺ` has a
  homological orientation exactly when `N = 0` or `N` is odd.
* `TauCeti.RealProjectiveSpace.orientationCharacter_projectivization_eq_one_iff`: its orientation
  character is trivial exactly when `N = 0` or `N` is odd.
* `TauCeti.RealProjectiveSpace.bijective_orientationCharacter_projectivization`: for `N` even and
  positive, the orientation character is an isomorphism `π₁(ℝℙᴺ, x) ≅ ℤˣ`.
* `TauCeti.RealProjectiveSpace.orientationCharacter_projectivization_eq_neg_one_iff`: for `N` even
  and positive, the orientation character of a loop class is `-1` exactly when the class is
  nontrivial.
* `TauCeti.RealProjectiveSpace.not_orientable_projectivization_of_even`: for `N` even and positive,
  `ℝℙᴺ` is not orientable as a smooth manifold.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3, Theorem 3.26.
-/

public section

open CategoryTheory Limits
open scoped LinearAlgebra.Projectivization Manifold

namespace TauCeti.RealProjectiveSpace

variable {N : ℕ}

/-- **Orientability of real projective space.** The real projective space
`ℝℙᴺ = ℙ ℝ (Fin (N + 1) → ℝ)`, a compact connected manifold of dimension `N`, has a homological
orientation exactly when `N = 0` or `N` is odd. -/
theorem nonempty_homologicalOrientation_projectivization_iff :
    Nonempty (HomologicalOrientation (ℙ ℝ (Fin (N + 1) → ℝ)) (Fin N → ℝ) N) ↔ N = 0 ∨ Odd N := by
  rw [← nontrivial_singularHomology_iff_nonempty_homologicalOrientation
    (Module.finrank_fin_fun ℝ (n := N)), ← nontrivial_singularHomology_projectivization_top_iff]
  exact (uliftIntHomologyIso (TopCat.of (ℙ ℝ (Fin (N + 1) → ℝ))) N).toLinearEquiv.nontrivial_congr

/-- **Even-dimensional real projective space is not orientable.** For `N` even and positive,
`ℝℙᴺ` has no homological orientation. -/
theorem isEmpty_homologicalOrientation_projectivization_of_even (hN : Even N) (hN0 : N ≠ 0) :
    IsEmpty (HomologicalOrientation (ℙ ℝ (Fin (N + 1) → ℝ)) (Fin N → ℝ) N) := by
  rw [← not_nonempty_iff, nonempty_homologicalOrientation_projectivization_iff]
  rintro (h | h)
  exacts [hN0 h, Nat.not_even_iff_odd.2 h hN]

/-- The orientation character of `ℝℙᴺ` is trivial exactly when `N = 0` or `N` is odd. -/
theorem orientationCharacter_projectivization_eq_one_iff (x : ℙ ℝ (Fin (N + 1) → ℝ)) :
    orientationCharacter (Module.finrank_fin_fun ℝ (n := N)) x = 1 ↔ N = 0 ∨ Odd N := by
  rw [← nonempty_homologicalOrientation_iff (Module.finrank_fin_fun ℝ (n := N)) x,
    nonempty_homologicalOrientation_projectivization_iff]

/-- **The orientation character of an even-dimensional real projective space.** For `N` even and
positive, the orientation character `π₁(ℝℙᴺ, x) →* ℤˣ` is bijective: both groups have two
elements, and the character is nontrivial because `ℝℙᴺ` is not orientable. -/
theorem bijective_orientationCharacter_projectivization (hN : Even N) (hN0 : N ≠ 0)
    (x : ℙ ℝ (Fin (N + 1) → ℝ)) :
    Function.Bijective (orientationCharacter (Module.finrank_fin_fun ℝ (n := N)) x) := by
  have hcard : Nat.card (FundamentalGroup (ℙ ℝ (Fin (N + 1) → ℝ)) x) = 2 := by
    rw [← card_fundamentalGroup_of_two_le N (by grind) ((homeomorphProjectivization N).symm x),
      Nat.card_congr (FundamentalGroup.homeomorphMulEquiv
        (homeomorphProjectivization N).symm x).toEquiv]
  have := Nat.finite_of_card_ne_zero (hcard.trans_ne two_ne_zero)
  have hne : orientationCharacter (Module.finrank_fin_fun ℝ (n := N)) x ≠ 1 := by
    rw [Ne, orientationCharacter_projectivization_eq_one_iff]
    rintro (h | h)
    exacts [hN0 h, Nat.not_even_iff_odd.2 h hN]
  -- A nontrivial homomorphism to `ℤˣ = {1, -1}` is surjective, and both groups have two elements.
  obtain ⟨γ, hγ⟩ := DFunLike.ne_iff.1 hne
  refine Function.Surjective.bijective_of_nat_card_le (fun u ↦ ?_) ?_
  · rcases Int.units_eq_one_or u with rfl | rfl
    exacts [⟨1, map_one _⟩, ⟨γ, Int.units_ne_iff_eq_neg.1 hγ⟩]
  · rw [hcard, Nat.card_eq_fintype_card, Fintype.card_units_int]

/-- For `N` even and positive, the orientation character of a loop class of `ℝℙᴺ` is `-1` exactly
when the class is nontrivial: transport along the nontrivial loop class reverses the local
orientations. -/
theorem orientationCharacter_projectivization_eq_neg_one_iff (hN : Even N) (hN0 : N ≠ 0)
    {x : ℙ ℝ (Fin (N + 1) → ℝ)} (γ : FundamentalGroup (ℙ ℝ (Fin (N + 1) → ℝ)) x) :
    orientationCharacter (Module.finrank_fin_fun ℝ (n := N)) x γ = -1 ↔ γ ≠ 1 := by
  rw [← Int.units_ne_iff_eq_neg,
    ← map_one (orientationCharacter (Module.finrank_fin_fun ℝ (n := N)) x),
    (bijective_orientationCharacter_projectivization hN hN0 x).injective.ne_iff]

/-- **Even-dimensional real projective space is not smoothly orientable.** For `N` even and
positive, `ℝℙᴺ` with its standard affine charts admits no smooth orientation, since a smooth
orientation would give a homological one. -/
theorem not_orientable_projectivization_of_even (hN : Even N) (hN0 : N ≠ 0) :
    ¬ Orientable 𝓘(ℝ, Fin N → ℝ) (ℙ ℝ (Fin (N + 1) → ℝ)) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN0
  rintro ⟨⟨o⟩⟩
  have hE := Module.finrank_fin_fun ℝ (n := n + 1)
  have := isEmpty_homologicalOrientation_projectivization_of_even hN hN0
  exact isEmptyElim ((o.reindex (finCongr hE)).toHomologicalOrientation hE)

end TauCeti.RealProjectiveSpace
