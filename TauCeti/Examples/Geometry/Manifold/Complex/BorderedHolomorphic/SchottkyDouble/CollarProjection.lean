/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.BorderedHolomorphic.SchottkyDouble.CollarProjection
public import TauCeti.Geometry.Manifold.Complex.BorderedHolomorphic.DoubledBundle
public import TauCeti.Geometry.Manifold.Complex.BorderedHolomorphic.ClosedDisc

/-!
# A collar projection of the closed unit disc

The closed unit disc is a compact Riemann surface with boundary the unit circle, so it has a collar
projection which is smooth when read on its Schottky double, a sphere. Through it, the
double of a complex core whose transitions are constant near the boundary is smooth; the trivial
core is the basic instance.
-/

public section

open Set
open scoped Manifold ContDiff Complex.UnitDisc

namespace TauCeti.Examples.CollarProjection

open SchottkyDouble

local notation "A" => (borderedInterior 𝕔𝔻 : Set 𝕔𝔻)ᶜ

/-- The boundary circle of the closed unit disc is compact. -/
theorem isCompact_boundary : IsCompact A :=
  (borderedInterior 𝕔𝔻).isOpen.isClosed_compl.isCompact

/-- The closed unit disc has a collar projection onto its boundary circle which is smooth when read
on the Schottky double through the fold. -/
example :
    ∃ U : Set 𝕔𝔻, IsOpen U ∧ A ⊆ U ∧ ∃ ρ : 𝕔𝔻 → 𝕔𝔻, Continuous ρ ∧ MapsTo ρ U A ∧
      (∀ x ∈ A, ρ x = x) ∧
      ContMDiffOn 𝓘(ℝ, ℂ) closedUpperHalfPlaneModel ∞ (ρ ∘ DoubleAlong.fold A)
        (DoubleAlong.fold A ⁻¹' U) ∧
      ContMDiffOn closedUpperHalfPlaneModel closedUpperHalfPlaneModel ∞ ρ U :=
  exists_collarProjection isCompact_boundary

/-- The double of the trivial core over the closed unit disc has smooth transitions on the Riemann
sphere, through the collar projection of `TauCeti.SchottkyDouble.exists_collarProjection`. -/
example (r : ℕ) (i j : SchottkyDouble 𝕔𝔻) :
    ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, (Fin (doubledBundleCore (FiniteRankBundleCore.trivial ℂ 𝕔𝔻 r)
        (FiniteRankBundleCore.isRealAlong_trivial r A)).rank → ℂ) →L[ℂ]
        (Fin (doubledBundleCore (FiniteRankBundleCore.trivial ℂ 𝕔𝔻 r)
        (FiniteRankBundleCore.isRealAlong_trivial r A)).rank → ℂ)) ∞
      ((doubledBundleCore _ (FiniteRankBundleCore.isRealAlong_trivial r A)).core.coordChange i j)
      ((doubledBundleCore _ (FiniteRankBundleCore.isRealAlong_trivial r A)).core.baseSet i ∩
        (doubledBundleCore _ (FiniteRankBundleCore.isRealAlong_trivial r A)).core.baseSet j) := by
  obtain ⟨U, hU, hAU, ρ, -, hρA, -, hρ, -⟩ := exists_collarProjection isCompact_boundary
  exact contMDiffOn_coordChange_doubledBundleCore _ _
    (fun _ _ ↦ contMDiffOn_const.congr fun _ _ ↦ rfl) hU hAU hρA hρ
    (fun _ _ _ _ _ _ ↦ ⟨mem_univ _, mem_univ _, rfl⟩) i j

end TauCeti.Examples.CollarProjection
