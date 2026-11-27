/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.BorderedHolomorphic.DoubledBundle.CollarForm
public import TauCeti.Examples.Geometry.Manifold.Complex.BorderedHolomorphic.SchottkyDouble.CollarProjection

/-!
# Smooth doubled bundles over the Riemann sphere

The closed unit disc is a compact Riemann surface with boundary the unit circle, and its Schottky
double is a sphere. Every smooth bundle pair over the closed disc is isomorphic, compatibly with the
real subbundles over the circle, to a smooth bundle pair whose doubled bundle over the sphere is
smooth. This applies for instance to the pairs `(ℂ, e^{ikθ/2}ℝ)` of the normalization axiom of the
Maslov index, once they are presented by a complex core real along the circle.
-/

public section

open Set
open scoped Manifold ContDiff Complex.UnitDisc

namespace TauCeti.Examples.CollarForm

open SchottkyDouble

local notation "A" => (borderedInterior 𝕔𝔻 : Set 𝕔𝔻)ᶜ

/-- Every smooth bundle pair over the closed unit disc is isomorphic, by an isomorphism which
commutes with conjugation over the circle, to a bundle pair whose doubled bundle over the Riemann
sphere has smooth transitions. -/
theorem exists_iso_smooth_doubledBundleCore (C : FiniteRankBundleCore ℂ 𝕔𝔻) (hC : C.IsRealAlong A)
    (hg : ∀ i j, ContMDiffOn closedUpperHalfPlaneModel
      𝓘(ℝ, (Fin C.rank → ℂ) →L[ℂ] (Fin C.rank → ℂ)) ∞
      (C.core.coordChange i j) (C.core.baseSet i ∩ C.core.baseSet j)) :
    ∃ (G : FiniteRankBundleCore ℂ 𝕔𝔻) (hG : G.IsRealAlong A) (e : G ≅ C),
      (∀ a ∈ A, ∀ v, e.hom.fiberMap a (star v) = star (e.hom.fiberMap a v)) ∧
      ∀ i j, ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, (Fin (doubledBundleCore G hG).rank → ℂ) →L[ℂ]
        (Fin (doubledBundleCore G hG).rank → ℂ)) ∞
        ((doubledBundleCore G hG).core.coordChange i j)
        ((doubledBundleCore G hG).core.baseSet i ∩ (doubledBundleCore G hG).core.baseSet j) := by
  obtain ⟨G, hG, e, -, -, -, he, hD⟩ := exists_iso_contMDiffOn_coordChange_doubledBundleCore
    CollarProjection.isCompact_boundary C hC hg
  exact ⟨G, hG, e, he, hD⟩

/-- The trivial pair `(ℂʳ, ℝʳ)` over the closed unit disc is isomorphic to a pair with a smooth
doubled bundle over the Riemann sphere. -/
example (r : ℕ) :
    ∃ (G : FiniteRankBundleCore ℂ 𝕔𝔻) (hG : G.IsRealAlong A),
      Nonempty (G ≅ FiniteRankBundleCore.trivial ℂ 𝕔𝔻 r) ∧
      ∀ i j, ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, (Fin (doubledBundleCore G hG).rank → ℂ) →L[ℂ]
        (Fin (doubledBundleCore G hG).rank → ℂ)) ∞
        ((doubledBundleCore G hG).core.coordChange i j)
        ((doubledBundleCore G hG).core.baseSet i ∩ (doubledBundleCore G hG).core.baseSet j) := by
  obtain ⟨G, hG, e, -, hD⟩ := exists_iso_smooth_doubledBundleCore _
    (FiniteRankBundleCore.isRealAlong_trivial r A) fun _ _ ↦ contMDiffOn_const.congr fun _ _ ↦ rfl
  exact ⟨G, hG, ⟨e⟩, hD⟩

end TauCeti.Examples.CollarForm
