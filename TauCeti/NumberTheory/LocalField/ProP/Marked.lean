/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.ProP.Demushkin
public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.Marked

import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Cyclotomic.OddDegree

/-!
# Marked presentations of local maximal pro-`p` Galois groups

Let `K` be a nonarchimedean local field that is a finite extension of `ℚ_[p]` and contains a
primitive `p`th root of unity. Then `G_K(p)` is a Demushkin group of rank `N + 2`, where
`N = [K : ℚ_[p]]`, and its canonical character is the cyclotomic orientation. Labute's marked
classification of Demushkin groups therefore presents `G_K(p)` by a single relator on `N + 2`
generators, and records the values of the cyclotomic character on the generators.

This file treats the dyadic case of odd degree: `p = 2` and `N` odd. The cyclotomic character of
`K` is then onto `ℤ₂ˣ` (`TauCeti.range_localCyclotomicCharacter_of_odd_finrank`), which is the
image `{±1} × U^(2)`, so the level of Labute's odd-rank relator is `f = 2` and

`G_K(2) ≃ ⟨x₁, …, x_{N+2} ∣ x₁² x₂⁴ (x₂, x₃) (x₄, x₅) ⋯ (x_{N+1}, x_{N+2})⟩`,

with `χ(x₁) = -1`, `χ(x₃) = (1 - 4)⁻¹ = -1/3` and `χ(xᵢ) = 1` for the other generators. For
`K = ℚ₂` this is the standard dyadic group `⟨x₁, x₂, x₃ ∣ x₁² x₂⁴ (x₂, x₃)⟩`.

The theorem is the abstract marked classification `TauCeti.isDemushkin_marked_of_q_two_odd`
after substituting the rank `TauCeti.demushkinRank_absoluteGaloisGroupProP`, the canonical
character `TauCeti.demushkinCharacter_absoluteGaloisGroupProP` and that image. Its only hypothesis
on `K` is odd degree, which already forces `K` to contain no primitive fourth root of unity; so it
applies to every field satisfying `TauCeti.IsDyadicOddCase`, through
`TauCeti.IsDyadicOddCase.odd_finrank`.

## Main results

* `TauCeti.absoluteGaloisGroupProP_two_marked_of_degree_odd`: the marked presentation of
  `G_K(2)` for a finite extension `K` of `ℚ₂` of odd degree.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Chapter VII, §5.
-/

public section

namespace TauCeti

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra ℚ_[2] K] [ValuativeExtension ℚ_[2] K]

/-- **The marked presentation of `G_K(2)` in odd degree.** Let `K` be a finite extension of `ℚ₂`
of odd degree `N`. Then `G_K(2)` is isomorphic to
`⟨x₁, …, x_{N+2} ∣ x₁² x₂⁴ (x₂, x₃) (x₄, x₅) ⋯ (x_{N+1}, x_{N+2})⟩`, and under this isomorphism
the cyclotomic orientation takes the value `-1` on the first marked generator, the value
`(1 - 4)⁻¹` on the third, and is trivial on every other marked generator. -/
theorem absoluteGaloisGroupProP_two_marked_of_degree_odd (hmu : ∃ ζ : K, IsPrimitiveRoot ζ 2)
    (hodd : Odd (Module.finrank ℚ_[2] K)) :
    ∃ e : absoluteGaloisGroupProP 2 K ≃ₜ*
        presentedProP 2 (Fin (Module.finrank ℚ_[2] K + 2))
          {demushkinWordTwoOdd 2 (Module.finrank ℚ_[2] K + 2)
            (freeProPGen 2 (Module.finrank ℚ_[2] K + 2))},
      cyclotomicOrientation 2 K hmu
          (e.symm (presentedProPGen 2 (Module.finrank ℚ_[2] K + 2) _ 0)) = -1 ∧
        ((cyclotomicOrientation 2 K hmu
            (e.symm (presentedProPGen 2 (Module.finrank ℚ_[2] K + 2) _ 2)) : ℤ_[2]) *
          (1 - 2 ^ 2) = 1) ∧
        ∀ i : ℕ, i ≠ 0 → i ≠ 2 → i < Module.finrank ℚ_[2] K + 2 →
          cyclotomicOrientation 2 K hmu
            (e.symm (presentedProPGen 2 (Module.finrank ℚ_[2] K + 2) _ i)) = 1 := by
  have : FiniteDimensional ℚ_[2] K := .of_finrank_pos hodd.pos
  have hG := isDemushkin_absoluteGaloisGroupProP_of_mu 2 K hmu
  have hrank : demushkinRank hG = Module.finrank ℚ_[2] K + 2 :=
    demushkinRank_absoluteGaloisGroupProP 2 K hmu
  have hrange : (demushkinCharacter hG).toMonoidHom.range = unitsPlusMinus 2 := by
    rw [unitsPlusMinus_two, ← range_localCyclotomicCharacter_of_odd_finrank K hodd]
    exact range_demushkinCharacter_absoluteGaloisGroupProP 2 K hmu
  have hmarked := isDemushkin_marked_of_q_two_odd hG (hrank ▸ hodd.add_even even_two)
    (hrank ▸ by have := hodd.pos; omega) le_rfl hrange
  rwa [demushkinCharacter_absoluteGaloisGroupProP, hrank] at hmarked

end TauCeti
