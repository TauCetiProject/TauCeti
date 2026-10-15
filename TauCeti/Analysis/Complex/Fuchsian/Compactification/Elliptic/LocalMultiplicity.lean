/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Compactification.Holomorphic
public import TauCeti.Analysis.Complex.RiemannSurface.LocalMultiplicity

/-!
# Local multiplicity of a compactified quotient map at an elliptic orbit

For an inclusion of discrete Fuchsian groups, the induced map of compactified quotients has
local multiplicity at an interior orbit equal to the relative index of the two point stabilizers.
This follows from the power-map expression in the compatible elliptic charts.

The local cyclic quotient model follows Farkas--Kra, *Riemann Surfaces*, Chapter I, §§4--5.
-/

public noncomputable section

open Filter IsManifold Metric MulAction TauCeti TauCeti.RiemannSurface Topology UpperHalfPlane
open scoped Manifold MatrixGroups

namespace Subgroup.CompactifiedQuotient

variable {Δ Γ : Subgroup PSL(2, ℝ)}

/-- At an interior orbit, the local multiplicity of a compactified quotient map is the relative
index of the source point stabilizer in the target point stabilizer. -/
theorem localMultiplicity_compactifiedQuotientMap_ofQuotient_eq_ellipticRamificationIndex
    [DiscreteTopology Γ] (h : Δ ≤ Γ) (z : ℍ) :
    letI : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
    localMultiplicity (compactifiedQuotientMap h) (ofQuotient (Quotient.mk'' z)) =
      ellipticRamificationIndex h z := by
  have : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
  obtain ⟨ε, hε, hopenΔ, hopenΓ⟩ :=
    exists_common_elliptic_chart_radius (Δ := Δ) (Γ := Γ) z
  let e := stabilizerBallQuotientChart hε hopenΔ
  let e' := stabilizerBallQuotientChart hε hopenΓ
  let c := ofQuotientChart e
  let c' := ofQuotientChart e'
  let x : Δ.CompactifiedQuotient := ofQuotient (Quotient.mk'' z)
  have hze : Quotient.mk'' z ∈ e.source := by
    rw [mem_stabilizerBallQuotientChart_source_iff hε hopenΔ]
    exact ⟨1, by simpa using hε⟩
  have hze' : Quotient.mk'' z ∈ e'.source := by
    rw [mem_stabilizerBallQuotientChart_source_iff hε hopenΓ]
    exact ⟨1, by simpa using hε⟩
  have hxc : x ∈ c.source := by
    simpa [x, c] using hze
  have hfxc : compactifiedQuotientMap h x ∈ c'.source := by
    simpa [x, c'] using hze'
  have hc : c ∈ maximalAtlas 𝓘(ℂ) 1 Δ.CompactifiedQuotient :=
    IsManifold.subset_maximalAtlas
      (ofQuotientChart_mem_atlas
        (stabilizerBallQuotientChart_mem_atlas (Γ := Δ) hε hopenΔ))
  have hc' : c' ∈ maximalAtlas 𝓘(ℂ) 1 Γ.CompactifiedQuotient :=
    IsManifold.subset_maximalAtlas
      (ofQuotientChart_mem_atlas
        (stabilizerBallQuotientChart_mem_atlas (Γ := Γ) hε hopenΓ))
  have hf : ∀ᶠ y in 𝓝 x,
      MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (compactifiedQuotientMap h) y :=
    .of_forall (mdifferentiable_compactifiedQuotientMap h)
  have hcx : c x = 0 := by
    simp only [c, x, ofQuotientChart_ofQuotient]
    rw [stabilizerBallQuotientChart_mk hε hopenΔ (by simpa using hε),
      discCoordinate_self, zero_pow Nat.card_pos.ne']
  have hcfx : c' (compactifiedQuotientMap h x) = 0 := by
    simp only [c', x, compactifiedQuotientMap_ofQuotient,
      ofQuotientChart_ofQuotient, TauCeti.Setoid.map_of_le_mk]
    rw [stabilizerBallQuotientChart_mk hε hopenΓ (by simpa using hε),
      discCoordinate_self, zero_pow Nat.card_pos.ne']
  have hn : 0 < ellipticRamificationIndex h z := ellipticRamificationIndex_pos h z
  have hpow :
      (fun u ↦ c' (compactifiedQuotientMap h (c.symm u))) =ᶠ[𝓝 0]
        fun u : ℂ ↦ u ^ ellipticRamificationIndex h z := by
    filter_upwards [hcx ▸ c.open_target.mem_nhds (c.map_source hxc)] with u hu
    have hu' : u ∈ e.target := by simpa [c] using hu
    exact compactifiedQuotientMap_ellipticChart h z hε hopenΔ hopenΓ hu'
  exact localMultiplicity_eq_of_coordinate_eventuallyEq_pow_zero
    hc hc' hxc hfxc hf hn hcx hcfx hpow

end Subgroup.CompactifiedQuotient
