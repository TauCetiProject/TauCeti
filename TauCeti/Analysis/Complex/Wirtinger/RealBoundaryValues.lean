/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.RealBoundaryReflection
import TauCeti.Analysis.Complex.Wirtinger.Regularity
import TauCeti.Analysis.Sobolev.Local.Morrey
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Pointwise real boundary values of weak real-boundary solutions

`TauCeti.HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ η` imposes the boundary condition that `ξ` be
real on the real axis only weakly, through the choice of test functions. This file shows that for
data `η` locally `Lᵖ` up to the axis with `p > 2`, a solution `ξ` continuous up to the axis takes
real values there: `star (ξ x) = ξ x` for every real `x ∈ Ω`. So for such solutions the weak
boundary condition implies the pointwise one, which is how the condition reads for `W^{1,q}` maps
with `q > 2`.

## Main results

* `TauCeti.HasWeakConjWirtingerDerivRealBoundaryOn.mono`: the weak real-boundary equation restricts
  to smaller open sets.
* `TauCeti.HasWeakConjWirtingerDerivRealBoundaryOn.star_eq_of_continuousOn`: a weak real-boundary
  solution with finite-dimensional coefficients and data locally `Lᵖ` up to the axis, `p > 2`,
  which is continuous on `Ω ∩ {0 ≤ im}`, is real on `Ω ∩ ℝ`. No conjugation invariance of `Ω` is
  assumed.
* `TauCeti.HasWeakConjWirtingerDerivRealBoundaryOn.star_eq_of_continuousOn_clm`: the same for the
  linear equation `∂ₛξ + i ∂ₜξ + C ξ = 0` with a coefficient field `C` locally `Lᵖ` up to the axis.
* Check: the constant `i` is not a weak real-boundary solution of `\bar∂ξ = η` for any `η` locally
  `Lᵖ` up to the axis, `p > 2`, on an open set meeting the real axis.

## Proof

After shrinking `Ω` to the conjugation-invariant open set `Ω ∩ conj Ω`, which has the same real
points, the reflection `starSchwarzReflection ξ` solves `\bar∂ (Rξ) = Rη` on `Ω` in the sense of
distributions, with `Rξ` and `Rη` locally `Lᵖ`. Interior regularity puts `Rξ` in `W^{1,p}_loc`,
and Morrey's embedding gives a representative `g` continuous on `Ω`. Off the axis `g` agrees with
the continuous functions `ξ` above and `star ∘ ξ ∘ conj` below, so at a real point `x` the limits
from the two sides give `ξ x = g x = star (ξ x)`.
-/

public section

open Complex MeasureTheory TopologicalSpace Set Filter Topology
open scoped ComplexConjugate

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [StarAddMonoid F] [StarModule ℂ F]
  {Ω : Opens ℂ} {ξ η : ℂ → F}

/-- The weak real-boundary equation restricts to smaller open sets. -/
theorem HasWeakConjWirtingerDerivRealBoundaryOn.mono {Ω' : Opens ℂ}
    (h : HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ η) (hΩ : Ω' ≤ Ω) :
    HasWeakConjWirtingerDerivRealBoundaryOn Ω' ξ η := by
  obtain ⟨hF, hξ, hη, hχ⟩ := hasWeakConjWirtingerDerivRealBoundaryOn_iff.1 h
  have hs : (Ω' : Set ℂ) ∩ {z | 0 ≤ z.im} ⊆ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im} :=
    inter_subset_inter_left _ hΩ
  exact hasWeakConjWirtingerDerivRealBoundaryOn_iff.2 ⟨hF, hξ.mono_set hs, hη.mono_set hs,
    fun χ hχr ↦ hχ ⟨χ, χ.contDiff, χ.hasCompactSupport, χ.tsupport_subset.trans hΩ⟩ hχr⟩

variable [FiniteDimensional ℂ F] {p : ENNReal}

/-- With finite-dimensional coefficients `star` is continuous, being real-linear. -/
private theorem continuousStar_of_finiteDimensional : ContinuousStar F := by
  let L : F →ₗ[ℝ] F :=
    { toFun := star
      map_add' := star_add
      map_smul' := fun r x ↦ by simp [← Complex.coe_smul, star_smul] }
  exact ⟨L.continuous_of_finiteDimensional⟩

/-- The pointwise boundary values on a conjugation-invariant open set, for a finite exponent. -/
private theorem star_eq_of_continuousOn_of_mapsTo [ContinuousStar F]
    (hΩ : MapsTo (starRingEnd ℂ) Ω Ω)
    (hp : 2 < p) (hp_top : p ≠ ⊤) (hη : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) η)
    (hξc : ContinuousOn ξ ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (h : HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ η) {x : ℝ} (hx : (x : ℂ) ∈ Ω) :
    star (ξ x) = ξ x := by
  have hp1 : 1 < p := (by norm_num : (1 : ENNReal) < 2).trans hp
  have := FiniteDimensional.completeSpace ℂ F
  have hRξ : MemLpLoc p Ω (starSchwarzReflection ξ) := hξc.memLpLoc.starSchwarzReflection hΩ
  have hW := (h.hasWeakConjWirtingerDerivOn_starSchwarzReflection hΩ).memWkpLoc_one hp1 hp_top
    hRξ (hη.starSchwarzReflection hΩ)
  -- `g` is a representative of the reflection, continuous on `Ω`.
  set g := MeasureTheory.preciseRepresentative volume (starSchwarzReflection ξ)
  have hg : ContinuousAt g x :=
    (hW.continuousOn_preciseRepresentative hp).continuousAt (Ω.isOpen.mem_nhds hx)
  have hae := hRξ.ae_eq_preciseRepresentative hp1.le
  -- Off the real axis `g` agrees with the continuous functions it represents almost everywhere.
  have hside {s : Set ℂ} (hso : IsOpen s) {f : ℂ → F} (hf : ContinuousOn f ((Ω : Set ℂ) ∩ s))
      (hRf : EqOn (starSchwarzReflection ξ) f s) : EqOn f g ((Ω : Set ℂ) ∩ s) := by
    refine Measure.eqOn_open_of_ae_eq (μ := volume) ?_ (Ω.isOpen.inter hso) hf
      ((hW.continuousOn_preciseRepresentative hp).mono inter_subset_left)
    filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_left hae,
      ae_restrict_mem (Ω.isOpen.inter hso).measurableSet] with z hz hzs
    exact (hRf hzs.2).symm.trans hz
  have hsub : (Ω : Set ℂ) ∩ {z | 0 < z.im} ⊆ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im} :=
    fun z hz ↦ ⟨hz.1, hz.2.out.le⟩
  have hup := hside (isOpen_lt continuous_const continuous_im) (hξc.mono hsub)
    fun z hz ↦ starSchwarzReflection_of_im_nonneg hz.out.le
  have hconj : MapsTo (starRingEnd ℂ) ((Ω : Set ℂ) ∩ {z | z.im < 0})
      ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) := fun z hz ↦
    ⟨hΩ hz.1, by simpa using hz.2.out.le⟩
  have hdown := hside (isOpen_lt continuous_im continuous_const)
    (continuous_star.comp_continuousOn (hξc.comp continuous_conj.continuousOn hconj))
    fun z hz ↦ starSchwarzReflection_of_im_neg hz.out
  have hξx : ContinuousWithinAt ξ ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) x := hξc x ⟨hx, by simp⟩
  have hΩx : (Ω : Set ℂ) ∈ 𝓝 (x : ℂ) := Ω.isOpen.mem_nhds hx
  -- The limit of `g` at `x` from above is `ξ x`.
  have hgx : g x = ξ x := by
    have : (𝓝[(Ω : Set ℂ) ∩ {z | 0 < z.im}] (x : ℂ)).NeBot := by
      rw [inter_comm, nhdsWithin_inter_of_mem' (mem_nhdsWithin_of_mem_nhds hΩx)]
      exact mem_closure_iff_nhdsWithin_neBot.1 (by simp)
    refine tendsto_nhds_unique (l := 𝓝[(Ω : Set ℂ) ∩ {z | 0 < z.im}] (x : ℂ))
      (hg.tendsto.mono_left nhdsWithin_le_nhds) ?_
    exact (hξx.tendsto.mono_left (nhdsWithin_mono _ hsub)).congr'
      (eventually_nhdsWithin_of_forall hup)
  -- The limit of `g` at `x` from below is `star (ξ x)`.
  have : (𝓝[(Ω : Set ℂ) ∩ {z | z.im < 0}] (x : ℂ)).NeBot := by
    rw [inter_comm, nhdsWithin_inter_of_mem' (mem_nhdsWithin_of_mem_nhds hΩx)]
    exact mem_closure_iff_nhdsWithin_neBot.1 (by simp)
  have hc : Tendsto (starRingEnd ℂ) (𝓝[(Ω : Set ℂ) ∩ {z | z.im < 0}] (x : ℂ))
      (𝓝[(Ω : Set ℂ) ∩ {z | 0 ≤ z.im}] (x : ℂ)) :=
    tendsto_nhdsWithin_iff.2 ⟨(continuous_conj.tendsto' _ _ (conj_ofReal x)).mono_left
      nhdsWithin_le_nhds, eventually_nhdsWithin_of_forall hconj⟩
  refine (tendsto_nhds_unique ((continuous_star.tendsto _).comp (hξx.tendsto.comp hc)) ?_).trans hgx
  exact (hg.tendsto.mono_left nhdsWithin_le_nhds).congr'
    (eventually_nhdsWithin_of_forall fun z hz ↦ (hdown hz).symm)

/-- **Weak real boundary values are pointwise real.** Let `p > 2` and let `ξ` be continuous on
`Ω ∩ {0 ≤ im}`, solving `\bar∂ξ = η` weakly on `Ω ∩ {0 ≤ im}` with the real boundary condition,
for `η` locally `Lᵖ` up to the axis and finite-dimensional coefficients. Then `ξ` is real on
`Ω ∩ ℝ`. -/
theorem HasWeakConjWirtingerDerivRealBoundaryOn.star_eq_of_continuousOn (hp : 2 < p)
    (hη : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) η)
    (hξc : ContinuousOn ξ ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (h : HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ η) :
    ∀ x : ℝ, (x : ℂ) ∈ Ω → star (ξ x) = ξ x := by
  intro x hx
  have := continuousStar_of_finiteDimensional (F := F)
  -- Shrink `Ω` to the conjugation-invariant open set `Ω ∩ conj Ω` and `p` to a finite exponent.
  let Ω' : Opens ℂ := ⟨(Ω : Set ℂ) ∩ conj ⁻¹' Ω, Ω.isOpen.inter (Ω.isOpen.preimage continuous_conj)⟩
  have hΩ' : Ω' ≤ Ω := fun z hz ↦ hz.1
  have hs : (Ω' : Set ℂ) ∩ {z | 0 ≤ z.im} ⊆ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im} :=
    inter_subset_inter_left _ hΩ'
  exact star_eq_of_continuousOn_of_mapsTo (Ω := Ω') (fun z hz ↦ ⟨hz.2, by simpa using hz.1⟩)
    (lt_min hp (by norm_num)) (ne_top_of_le_ne_top ENNReal.ofNat_ne_top (min_le_right p 3))
    ((hη.mono_set hs).mono_exponent (min_le_left p 3)) (hξc.mono hs) (h.mono hΩ')
    ⟨hx, by simpa using hx⟩

/-- **Weak real boundary values are pointwise real, linear form.** Let `p > 2` and let `ξ` be
continuous on `Ω ∩ {0 ≤ im}`, solving `∂ₛξ + i ∂ₜξ + C ξ = 0` weakly on `Ω ∩ {0 ≤ im}` with the
real boundary condition, for a coefficient field `C` locally `Lᵖ` up to the axis and
finite-dimensional coefficients. Then `ξ` is real on `Ω ∩ ℝ`. -/
theorem HasWeakConjWirtingerDerivRealBoundaryOn.star_eq_of_continuousOn_clm {C : ℂ → F →L[ℝ] F}
    (hp : 2 < p) (hC : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) C)
    (hξc : ContinuousOn ξ ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (h : HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ fun z ↦ -(2 : ℂ)⁻¹ • C z (ξ z)) :
    ∀ x : ℝ, (x : ℂ) ∈ Ω → star (ξ x) = ξ x := by
  refine h.star_eq_of_continuousOn hp ?_ hξc
  convert (hC.clm_apply_continuousOn hξc).const_smul (-(2 : ℝ)⁻¹) using 1
  ext z
  simp [← Complex.coe_smul]

/-- **Check.** The constant `i`, which is not real on the axis, is not a weak real-boundary
solution of `\bar∂ξ = η` for any `η` locally `Lᵖ` up to the axis with `p > 2`, on an open set
meeting the real axis. -/
theorem not_hasWeakConjWirtingerDerivRealBoundaryOn_const_I_of_memLpLoc (hp : 2 < p) {x₀ : ℝ}
    (hx₀ : (x₀ : ℂ) ∈ Ω) {η : ℂ → ℂ} (hη : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) η) :
    ¬ HasWeakConjWirtingerDerivRealBoundaryOn Ω (fun _ ↦ I) η := fun h ↦ by
  have := h.star_eq_of_continuousOn hp hη continuousOn_const x₀ hx₀
  norm_num [Complex.ext_iff] at this

end TauCeti
