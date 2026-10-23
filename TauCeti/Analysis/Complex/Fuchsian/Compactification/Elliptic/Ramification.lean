/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Compactification.Map
public import TauCeti.Analysis.Complex.Fuchsian.Compactification.Manifold
public import TauCeti.Analysis.Complex.Fuchsian.Elliptic.Ramification

/-!
# Elliptic ramification of maps between Fuchsian quotients

For an inclusion `Δ ≤ Γ` of discrete subgroups of `PSL(2, ℝ)`, the compactified
quotient map has the same elliptic power-map expression as the coarse quotient map.

The local model is the cyclic disc quotient of Farkas--Kra, *Riemann Surfaces*, Chapter I,
§§4--5.
-/

public noncomputable section

open Filter Metric MulAction TauCeti Topology UpperHalfPlane
open scoped MatrixGroups

namespace Subgroup

variable {Δ Γ : Subgroup PSL(2, ℝ)}

/-- The compactified quotient map has the same power expression at an elliptic orbit, using
the charts of the coarse quotient transported into the compactification. -/
theorem compactifiedQuotientMap_ellipticChart (h : Δ ≤ Γ) (z : ℍ)
    [DiscreteTopology Γ] :
    letI : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
    ∀ {ε : ℝ} (hε : 0 < ε)
      (hΔ : IsOpenEmbedding (stabilizerBallQuotientToQuotient Δ z ε))
      (hΓ : IsOpenEmbedding (stabilizerBallQuotientToQuotient Γ z ε))
      {u : ℂ} (_hu : u ∈ (stabilizerBallQuotientChart hε hΔ).target),
      CompactifiedQuotient.ofQuotientChart (stabilizerBallQuotientChart hε hΓ)
          (compactifiedQuotientMap h
            ((CompactifiedQuotient.ofQuotientChart
              (stabilizerBallQuotientChart hε hΔ)).symm u)) =
        u ^ ellipticRamificationIndex h z := by
  have : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
  intro ε hε hΔ hΓ u hu
  rw [CompactifiedQuotient.ofQuotientChart_symm_apply,
    compactifiedQuotientMap_ofQuotient,
    CompactifiedQuotient.ofQuotientChart_ofQuotient]
  exact stabilizerBallQuotientChart_map_of_le_symm h z hε hΔ hΓ hu

end Subgroup

namespace Subgroup.CompactifiedQuotient

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
    ofQuotientChart (stabilizerBallQuotientChart hε hopenΓ)
      (compactifiedQuotientMap h (.ofQuotient q)) =
      (ofQuotientChart (stabilizerBallQuotientChart hε hopenΔ)
        (.ofQuotient q)) ^ ellipticRamificationIndex h z := by
  dsimp only
  let : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
  intro hq
  simpa only [compactifiedQuotientMap_ofQuotient,
    ofQuotientChart_ofQuotient] using
    (stabilizerBallQuotientChart_map_eq_pow_ellipticRamificationIndex
      h z hε hopenΔ hopenΓ hq)

end Subgroup.CompactifiedQuotient
