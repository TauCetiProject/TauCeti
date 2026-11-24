/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Compactification.Holomorphic
public import TauCeti.Analysis.Complex.RiemannSurface.LocalMultiplicity

/-!
# Local multiplicity of a compactified quotient map at a cusp

For an inclusion of discrete Fuchsian groups, compatible normalized cusp data give local
coordinates in which the induced map of compactified quotients is a power map. Consequently its
local multiplicity at the adjoined cusp is the canonical cusp width index. Since that index is the
relative index of the cusp stabilizers, the local multiplicity at the orbit of a cusp point `c`
is `[stabilizer Γ c : stabilizer Δ c]`, with no choice of cusp data. When `Δ` is normal in `Γ`,
conjugating the stabilizers shows that all cusps of `Δ` over one cusp of `Γ` have the same local
multiplicity.

The cusp-coordinate and width conventions follow Diamond and Shurman, *A First Course in Modular
Forms*, §2.4.
-/

public noncomputable section

open Filter IsManifold MulAction OnePoint Topology TauCeti.Subgroup.CuspDatum TauCeti.RiemannSurface
open scoped Manifold MatrixGroups

namespace Subgroup.CompactifiedQuotient

variable {Δ Γ : Subgroup PSL(2, ℝ)}

/-- For normalized cusp data with the same scaling, the local multiplicity at an adjoined cusp of
a compactified quotient map is the canonical positive integer by which the cusp width changes. -/
theorem localMultiplicity_compactifiedQuotientMap_ofCusp_eq_widthIndex [DiscreteTopology Γ]
    (h : Δ ≤ Γ)
    (D : Δ.CuspDatum) (E : Γ.CuspDatum)
    (hσ : D.scaling = E.scaling) :
    letI : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
    localMultiplicity (compactifiedQuotientMap h) (ofCusp D.cuspOrbit) =
      widthIndex h D E hσ := by
  have : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
  let hc : D.cusp = E.cusp := D.cusp_eq_of_scaling_eq E hσ
  let n := widthIndex h D E hσ
  have hw : D.width = n * E.width := width_eq_widthIndex_mul h D E hσ
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
  have hex : e x = 0 := by simp [e, x]
  have hefx : e' (compactifiedQuotientMap h x) = 0 := by simp [e', hfx]
  have hpow : (fun z ↦ e' (compactifiedQuotientMap h (e.symm z))) =ᶠ[𝓝 0]
      fun z : ℂ ↦ z ^ n := by
    filter_upwards [hex ▸ e.open_target.mem_nhds (e.map_source hxe)] with z hz
    have hz' : e.symm z ∈ cuspNhd D D.width := by
      simpa [e] using e.map_target hz
    rw [cuspChart_compactifiedQuotientMap_eq_pow_widthIndex h D E hσ hD hz']
    simp [e, n, e.right_inv hz]
  exact localMultiplicity_eq_of_coordinate_eventuallyEq_pow_zero
    he he' hxe hfxe hf hex hefx hpow

/-- The local multiplicity of a compactified quotient map at the orbit of a cusp point `c` is the
relative index of the smaller group in the stabilizer of `c` in the larger group, that is,
`[stabilizer Γ c : stabilizer Δ c]`. -/
theorem localMultiplicity_compactifiedQuotientMap_ofCusp_cuspOrbitMk [DiscreteTopology Γ]
    (h : Δ ≤ Γ) (c : Δ.cuspPoints) :
    letI : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
    localMultiplicity (compactifiedQuotientMap h) (ofCusp (Δ.cuspOrbitMk c)) =
      (Δ.subgroupOf Γ).relIndex (stabilizer Γ (c : OnePoint ℝ)) := by
  have : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
  have hc := mem_cuspPoints.mp c.property
  obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq PSL(2, ℝ) (c : OnePoint ℝ) ∞
  obtain ⟨D, hDc, hDσ⟩ := hc.exists_cuspDatum hσ
  obtain ⟨E, hEc, hEσ⟩ := (hc.mono h).exists_cuspDatum hσ
  have hD : D.cuspOrbit = Δ.cuspOrbitMk c := Subtype.ext (by simp [hDc])
  rw [← hD, localMultiplicity_compactifiedQuotientMap_ofCusp_eq_widthIndex h D E
    (hDσ.trans hEσ.symm), widthIndex_eq_relIndex, hEc]

/-- **Cusps over one cusp of a normal cover have the same local multiplicity.** When `Δ` is normal
in `Γ`, two cusps of `Δ` over the same cusp of `Γ` are translates `c₁ = g • c₂` by some `g ∈ Γ`.
Conjugation by `g` carries the stabilizer of `c₂` to that of `c₁` and preserves `Δ`, so the
relative indices of the stabilizers agree. -/
theorem localMultiplicity_compactifiedQuotientMap_ofCusp_eq_of_cuspOrbitMap_eq
    [DiscreteTopology Γ] (h : Δ ≤ Γ) [(Δ.subgroupOf Γ).Normal] {C₁ C₂ : Δ.CuspOrbit}
    (hC : cuspOrbitMap h C₁ = cuspOrbitMap h C₂) :
    letI : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
    localMultiplicity (compactifiedQuotientMap h) (ofCusp C₁) =
      localMultiplicity (compactifiedQuotientMap h) (ofCusp C₂) := by
  obtain ⟨c₁, rfl⟩ := cuspOrbitMk_surjective C₁
  obtain ⟨c₂, rfl⟩ := cuspOrbitMk_surjective C₂
  rw [cuspOrbitMap_cuspOrbitMk, cuspOrbitMap_cuspOrbitMk, cuspOrbitMk_eq_iff] at hC
  obtain ⟨g, hg⟩ := mem_orbit_iff.mp hC
  dsimp only at hg
  rw [localMultiplicity_compactifiedQuotientMap_ofCusp_cuspOrbitMk,
    localMultiplicity_compactifiedQuotientMap_ofCusp_cuspOrbitMk, ← hg,
    stabilizer_smul_eq_stabilizer_map_conj]
  have hΔ : (Δ.subgroupOf Γ).map (MulAut.conj g).toMonoidHom = Δ.subgroupOf Γ :=
    normal_iff_map_conj_eq.mp ‹_› g
  conv_lhs => rw [← hΔ]
  exact relIndex_map_map_of_injective _ _ (MulAut.conj g).injective

end Subgroup.CompactifiedQuotient
