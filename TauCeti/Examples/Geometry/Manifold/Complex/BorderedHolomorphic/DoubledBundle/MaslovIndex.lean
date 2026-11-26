/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.BorderedHolomorphic.DoubledBundle.MaslovIndex
public import TauCeti.Examples.Geometry.Manifold.Complex.BorderedHolomorphic.DoubledBundle.CollarForm

/-!
# The Maslov index of bundle pairs over the closed unit disc

The closed unit disc is a compact Riemann surface with boundary the unit circle, whose Schottky
double is the Riemann sphere. The trivial pair `(ℂʳ, ℝʳ)`, the case `k = 0` of the pairs
`(ℂ, e^{ikθ/2}ℝ)` of the normalization axiom, has Maslov index `0`: its doubled bundle is the
trivial bundle over the sphere. The Maslov index of a smooth bundle pair over the disc is
independent of the choices made to give its doubled bundle a smooth structure: a collar form comes
with an isomorphism to the pair commuting with conjugation over the circle, so it has the Maslov
index of the pair (`TauCeti.FiniteRankBundleCore.maslovIndex_eq_of_iso`).
-/

public section

open CategoryTheory Set
open scoped Manifold ContDiff Complex.UnitDisc

namespace TauCeti.Examples.MaslovIndex

open SchottkyDouble FiniteRankBundleCore

local notation "A" => (borderedInterior 𝕔𝔻 : Set 𝕔𝔻)ᶜ

/-- The trivial pair `(ℂʳ, ℝʳ)` over the closed unit disc has Maslov index `0`. -/
example (r : ℕ) : (trivial ℂ 𝕔𝔻 r).maslovIndex (isRealAlong_trivial r A) = 0 :=
  maslovIndex_trivial r

/-- Every smooth bundle pair over the closed unit disc is isomorphic, by an isomorphism which
commutes with conjugation over the circle, to a bundle pair with the same Maslov index whose
doubled bundle over the Riemann sphere has smooth transitions. -/
theorem exists_maslovIndex_eq_smooth_doubledBundleCore (C : FiniteRankBundleCore ℂ 𝕔𝔻)
    (hC : C.IsRealAlong A)
    (hg : ∀ i j, ContMDiffOn closedUpperHalfPlaneModel
      𝓘(ℝ, (Fin C.rank → ℂ) →L[ℂ] (Fin C.rank → ℂ)) ∞
      (C.core.coordChange i j) (C.core.baseSet i ∩ C.core.baseSet j)) :
    ∃ (G : FiniteRankBundleCore ℂ 𝕔𝔻) (hG : G.IsRealAlong A) (e : G ≅ C),
      (∀ a ∈ A, ∀ v, e.hom.fiberMap a (star v) = star (e.hom.fiberMap a v)) ∧
      G.maslovIndex hG = C.maslovIndex hC ∧
      ∀ i j, ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, (Fin (doubledBundleCore G hG).rank → ℂ) →L[ℂ]
        (Fin (doubledBundleCore G hG).rank → ℂ)) ∞
        ((doubledBundleCore G hG).core.coordChange i j)
        ((doubledBundleCore G hG).core.baseSet i ∩ (doubledBundleCore G hG).core.baseSet j) := by
  obtain ⟨G, hG, e, he, hD⟩ := CollarForm.exists_iso_smooth_doubledBundleCore C hC hg
  exact ⟨G, hG, e, he, maslovIndex_eq_of_iso hG hC e he, hD⟩

end TauCeti.Examples.MaslovIndex
