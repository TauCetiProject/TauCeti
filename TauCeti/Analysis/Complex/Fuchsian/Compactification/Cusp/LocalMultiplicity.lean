/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Compactification.Cusp.Index
public import TauCeti.Analysis.Complex.Fuchsian.Compactification.EllipticRamification
public import TauCeti.Analysis.Complex.RiemannSurface.LocalMultiplicity

/-!
# Local multiplicity of a compactified quotient map at a cusp

For an inclusion of discrete Fuchsian groups, compatible normalized cusp data give local
coordinates in which the induced map of compactified quotients is a power map. Consequently the
map is holomorphic near the adjoined cusp and its local multiplicity there is the canonical cusp
width index.

The cusp-coordinate and width conventions follow Diamond and Shurman, *A First Course in Modular
Forms*, §2.4.
-/

public noncomputable section

open Filter Function IsManifold MulAction Set Topology TauCeti.Subgroup.CuspDatum
  TauCeti.RiemannSurface UpperHalfPlane
open scoped Manifold MatrixGroups

namespace Subgroup.CompactifiedQuotient

variable {Δ Γ : Subgroup PSL(2, ℝ)}

private theorem mdifferentiableAt_compactifiedQuotientMap_of_mem_cuspNhd
    [DiscreteTopology Δ] [DiscreteTopology Γ] (h : Δ ≤ Γ)
    (D : Δ.CuspDatum) (E : Γ.CuspDatum)
    (hσ : D.scaling = E.scaling)
    {A : ℝ} (hD : D.width ≤ A) {x : Δ.CompactifiedQuotient} (hx : x ∈ cuspNhd D A) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (compactifiedQuotientMap h) x := by
  have hc : D.cusp = E.cusp := D.cusp_eq_of_scaling_eq E hσ
  let n := widthIndex h D E hc hσ
  have hn : 0 < n := widthIndex_pos h D E hc hσ
  have hw : D.width = n * E.width := width_eq_widthIndex_mul h D E hc hσ
  have hE : E.width ≤ A := width_le_of_width_eq_nat_mul D E hw hD
  let e := cuspChart D hD
  let e' := cuspChart E hE
  have he : e ∈ maximalAtlas 𝓘(ℂ) 1 Δ.CompactifiedQuotient :=
    IsManifold.subset_maximalAtlas (cuspChart_mem_atlas D hD)
  have he' : e' ∈ maximalAtlas 𝓘(ℂ) 1 Γ.CompactifiedQuotient :=
    IsManifold.subset_maximalAtlas (cuspChart_mem_atlas E hE)
  have hxe : x ∈ e.source := by simpa [e] using hx
  have hfxe : compactifiedQuotientMap h x ∈ e'.source := by
    simpa [e'] using
      (image_compactifiedQuotientMap_cuspNhd_subset_cuspNhd h D E hσ.symm A ⟨x, hx, rfl⟩)
  rw [← mdifferentiableWithinAt_univ,
    mdifferentiableWithinAt_iff_of_mem_maximalAtlas he he' hxe hfxe]
  refine ⟨(continuous_compactifiedQuotientMap h).continuousAt.continuousWithinAt, ?_⟩
  simp only [mfld_simps]
  rw [differentiableWithinAt_univ]
  refine ((analyticAt_id.pow n).differentiableAt).congr_of_eventuallyEq ?_
  filter_upwards [e.open_target.mem_nhds (e.map_source hxe)] with z hz
  have hz' : e.symm z ∈ cuspNhd D A := by
    simpa [e] using e.map_target hz
  simpa [e, e', n, comp_apply, e.right_inv hz] using
    (cuspChart_compactifiedQuotientMap_eq_pow_widthIndex h D E hc hσ hD hz')

/-- The map of compactified quotients induced by an inclusion of discrete projective subgroups is
holomorphic. -/
theorem mdifferentiable_compactifiedQuotientMap [DiscreteTopology Γ] (h : Δ ≤ Γ) :
    letI : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (compactifiedQuotientMap h) := by
  have : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
  intro x
  cases x with
  | ofQuotient p =>
      induction p using Quotient.inductionOn' with
      | h z =>
          obtain ⟨ε, hε, hΔ, hΓ⟩ :=
            (eventually_mem_nhdsWithin.and
              ((eventually_isOpenEmbedding_stabilizerBallQuotientToQuotient Δ z).and
                (eventually_isOpenEmbedding_stabilizerBallQuotientToQuotient Γ z))).exists
          let e := stabilizerBallQuotientChart hε hΔ
          let e' := stabilizerBallQuotientChart hε hΓ
          let c := ofQuotientChart e
          let c' := ofQuotientChart e'
          have hze : Quotient.mk (orbitRel Δ ℍ) z ∈ e.source := by
            rw [mem_stabilizerBallQuotientChart_source_iff hε hΔ]
            exact ⟨1, by simpa using hε⟩
          have hze' : Quotient.mk (orbitRel Γ ℍ) z ∈ e'.source := by
            rw [mem_stabilizerBallQuotientChart_source_iff hε hΓ]
            exact ⟨1, by simpa using hε⟩
          have hxc : ofQuotient (Quotient.mk (orbitRel Δ ℍ) z) ∈ c.source := by
            simpa [c, e] using hze
          have hfxc : compactifiedQuotientMap h
                (ofQuotient (Quotient.mk (orbitRel Δ ℍ) z)) ∈ c'.source := by
            simpa [c', e'] using hze'
          have hc : c ∈ maximalAtlas 𝓘(ℂ) 1 Δ.CompactifiedQuotient :=
            IsManifold.subset_maximalAtlas
              (ofQuotientChart_mem_atlas
                (stabilizerBallQuotientChart_mem_atlas (Γ := Δ) hε hΔ))
          have hc' : c' ∈ maximalAtlas 𝓘(ℂ) 1 Γ.CompactifiedQuotient :=
            IsManifold.subset_maximalAtlas
              (ofQuotientChart_mem_atlas
                (stabilizerBallQuotientChart_mem_atlas (Γ := Γ) hε hΓ))
          rw [← mdifferentiableWithinAt_univ,
            mdifferentiableWithinAt_iff_of_mem_maximalAtlas hc hc' hxc hfxc]
          refine ⟨(continuous_compactifiedQuotientMap h).continuousAt.continuousWithinAt, ?_⟩
          simp only [mfld_simps]
          rw [differentiableWithinAt_univ]
          refine ((analyticAt_id.pow
            (ellipticRamificationIndex h z)).differentiableAt).congr_of_eventuallyEq ?_
          filter_upwards [c.open_target.mem_nhds (c.map_source hxc)] with u hu
          have hu' : u ∈ e.target := by simpa [c] using hu
          simpa [c, c', e, e', comp_apply] using
            (compactifiedQuotientMap_ellipticChart h z hε hΔ hΓ hu')
  | ofCusp C =>
      obtain ⟨D, rfl⟩ := CuspDatum.cuspOrbit_surjective C
      obtain ⟨E, -, hσ⟩ :=
        (D.isCuspPoint.mono h).exists_cuspDatum D.scaling_smul_cusp
      exact mdifferentiableAt_compactifiedQuotientMap_of_mem_cuspNhd h D E hσ.symm
        le_rfl (ofCusp_mem_cuspNhd D D.width)

/-- For normalized cusp data with the same scaling, the local multiplicity at an adjoined cusp of
a compactified quotient map is the canonical positive integer by which the cusp width changes. -/
theorem localMultiplicity_compactifiedQuotientMap_ofCusp_eq_widthIndex [DiscreteTopology Γ]
    (h : Δ ≤ Γ)
    (D : Δ.CuspDatum) (E : Γ.CuspDatum)
    (hσ : D.scaling = E.scaling) :
    letI : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
    localMultiplicity (compactifiedQuotientMap h) (ofCusp D.cuspOrbit) =
      widthIndex h D E (D.cusp_eq_of_scaling_eq E hσ) hσ := by
  have : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
  let hc : D.cusp = E.cusp := D.cusp_eq_of_scaling_eq E hσ
  let n := widthIndex h D E hc hσ
  have hn : 0 < n := widthIndex_pos h D E hc hσ
  have hw : D.width = n * E.width := width_eq_widthIndex_mul h D E hc hσ
  have hD : D.width ≤ D.width := le_rfl
  have hE : E.width ≤ D.width := width_le_of_width_eq_nat_mul D E hw hD
  let e := cuspChart D hD
  let e' := cuspChart E hE
  let x : Δ.CompactifiedQuotient := ofCusp D.cuspOrbit
  have hxe : x ∈ e.source := by
    simp [x, e]
  have hfx : compactifiedQuotientMap h x = ofCusp E.cuspOrbit := by
    simp [x, cuspOrbitMap_cuspOrbit_eq_of_cusp_eq h hc.symm]
  have hfxe : compactifiedQuotientMap h x ∈ e'.source := by
    rw [hfx]
    simp [e']
  have he : e ∈ maximalAtlas 𝓘(ℂ) 1 Δ.CompactifiedQuotient :=
    IsManifold.subset_maximalAtlas (cuspChart_mem_atlas D hD)
  have he' : e' ∈ maximalAtlas 𝓘(ℂ) 1 Γ.CompactifiedQuotient :=
    IsManifold.subset_maximalAtlas (cuspChart_mem_atlas E hE)
  have hf : ∀ᶠ y in 𝓝 x,
      MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (compactifiedQuotientMap h) y := by
    exact Filter.Eventually.of_forall (mdifferentiable_compactifiedQuotientMap h)
  rw [localMultiplicity_eq_analyticOrderNatAt he he' hxe hfxe hf]
  have hex : e x = 0 := by simp [e, x]
  have hefx : e' (compactifiedQuotientMap h x) = 0 := by simp [e', hfx]
  rw [hex]
  simp only [hefx]
  have heq : (fun z ↦ e' (compactifiedQuotientMap h (e.symm z)) - 0) =ᶠ[𝓝 0]
      fun z : ℂ ↦ z ^ n - 0 ^ n := by
    filter_upwards [hex ▸ e.open_target.mem_nhds (e.map_source hxe)] with z hz
    have hz' : e.symm z ∈ cuspNhd D D.width := by
      simpa [e] using e.map_target hz
    rw [cuspChart_compactifiedQuotientMap_eq_pow_widthIndex h D E hc hσ hD hz']
    simp [e, n, e.right_inv hz, zero_pow hn.ne']
  calc
    analyticOrderNatAt (fun z ↦ e' (compactifiedQuotientMap h (e.symm z)) - 0) 0 =
        analyticOrderNatAt (fun z : ℂ ↦ z ^ n - 0 ^ n) 0 := by
      exact TauCeti.analyticOrderNatAt_congr heq
    _ = localMultiplicity (fun z : ℂ ↦ z ^ n) 0 := by
      rw [localMultiplicity_eq_analyticOrderNatAt_sub]
    _ = n := localMultiplicity_pow_zero n
    _ = widthIndex h D E hc hσ := rfl

end Subgroup.CompactifiedQuotient
