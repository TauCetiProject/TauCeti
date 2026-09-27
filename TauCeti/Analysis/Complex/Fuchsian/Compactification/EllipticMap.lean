/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Compactification.Map
public import TauCeti.Analysis.Complex.Fuchsian.Compactification.Manifold
public import TauCeti.Analysis.Complex.Fuchsian.Elliptic

/-!
# Elliptic ramification of maps between Fuchsian quotients

For an inclusion `Δ ≤ Γ` of discrete projective subgroups, the stabilizer of a point for `Δ`
embeds in its stabilizer for `Γ`. Thus the smaller stabilizer order divides the larger one.
In the canonical disc coordinates, the map of orbit quotients is the power map whose exponent
is the ratio of those orders. This gives the elliptic local ramification index of the
compactified quotient map in charts with a common admissible radius.

The local cyclic quotient model is described in Farkas–Kra, *Riemann Surfaces*, Chapter I,
§§4–5, and Katok, *Fuchsian Groups*, §2.4.
-/

public noncomputable section

open MulAction Set Topology UpperHalfPlane
open scoped MatrixGroups

namespace Subgroup

variable {Δ Γ : Subgroup PSL(2, ℝ)} (h : Δ ≤ Γ) (z : ℍ)

/-- The compactified quotient map has elliptic local expression `u ↦ u ^ e` in the
transported charts at points of the uncompactified quotient. -/
theorem ofQuotientChart_compactifiedQuotientMap_eq_pow_ellipticRamificationIndex
    [DiscreteTopology Γ]
    {ε : ℝ} (hε : 0 < ε)
    (hopenΔ : IsOpenEmbedding (stabilizerBallQuotientToQuotient Δ z ε))
    (hopenΓ : IsOpenEmbedding (stabilizerBallQuotientToQuotient Γ z ε))
    {q : orbitRel.Quotient Δ ℍ} :
    let : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
    q ∈ (stabilizerBallQuotientChart hε hopenΔ).source →
    CompactifiedQuotient.ofQuotientChart (stabilizerBallQuotientChart hε hopenΓ)
      (compactifiedQuotientMap h (.ofQuotient q)) =
      (CompactifiedQuotient.ofQuotientChart (stabilizerBallQuotientChart hε hopenΔ)
        (.ofQuotient q)) ^ ellipticRamificationIndex h z := by
  dsimp only
  let : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
  intro hq
  simpa only [compactifiedQuotientMap_ofQuotient,
    CompactifiedQuotient.ofQuotientChart_ofQuotient] using
    (stabilizerBallQuotientChart_map_eq_pow_ellipticRamificationIndex
      h z hε hopenΔ hopenΓ hq)

end Subgroup
