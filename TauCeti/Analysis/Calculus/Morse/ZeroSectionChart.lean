/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.Parametric
import TauCeti.Analysis.Calculus.BumpFunction.FiniteDimension
import TauCeti.Analysis.Calculus.InverseFunctionTheorem
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Injective
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# The parametric Morse lemma along the whole zero section

The canonical parametric Morse coordinate `TauCeti.parametricMorseCoord F (b, v) = R (b, v) v` of
`TauCeti.Analysis.Calculus.Morse.Parametric`, where `R (b, v)` is Palais's operator square root
comparing the averaged vertical Hessian with the vertical Hessian at `(b, 0)`, is determined by the
family `F` alone, with no choices. It also only depends on `F` along the segment from `(b, 0)` to
`(b, v)` (`TauCeti.parametricMorseCoord_congr_of_eqOn`). So the local normal forms it gives near the
points of the zero section glue: over an open set `U` of the base on which the zero section is
critical and nondegenerate, `(b, v) ↦ (b, parametricMorseCoord F (b, v))` is a single `C^n` chart on
a neighbourhood of the whole zero section over `U`, in which `F` is its vertical Hessian quadratic
form (`TauCeti.exists_parametricMorseCoord_chart`). The family need only be `C^{n+2}` on an open set
containing the zero section over `U`. The source of the chart is a union of products of open sets of
the base with balls about `0`; over each base point these balls are nested, so the chart is
injective.

## Main declarations

* `TauCeti.parametricMorseCoord_congr_of_eqOn`: the coordinate only depends on the family near
  the segment in the fibre.
* `TauCeti.exists_parametricMorseCoord_chart`: the parametric Morse lemma along the whole zero
  section over an open set of the base, in a single chart given by the canonical coordinate.

## References

* R. S. Palais, *Morse theory on Hilbert manifolds*, Topology **2** (1963), 299--340, Section 2,
  for the operator square root.
* R. S. Palais, *The Morse lemma for Banach spaces*, Bull. Amer. Math. Soc. **75** (1969),
  968--971.
-/

public section

noncomputable section

open Filter Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
/-- The **canonical parametric Morse coordinate only depends on the family near the segment** in
the fibre from `0` to `z.2`: families whose slices over `z.1` agree on an open set star-convex
about `0` and containing `z.2` have the same coordinate at `z`. -/
theorem parametricMorseCoord_congr_of_eqOn {f g : P × E → ℝ} {z : P × E} {V : Set E}
    (hV : IsOpen V) (hV₀ : StarConvex ℝ 0 V)
    (hfg : EqOn (fun v ↦ f (z.1, v)) (fun v ↦ g (z.1, v)) V) (hz : z.2 ∈ V) :
    parametricMorseCoord f z = parametricMorseCoord g z := by
  have hD : ∀ y ∈ V, fderiv ℝ (fderiv ℝ fun v ↦ f (z.1, v)) y =
      fderiv ℝ (fderiv ℝ fun v ↦ g (z.1, v)) y := fun y hy ↦
    (hfg.eventuallyEq_of_mem (hV.mem_nhds hy)).fderiv.fderiv_eq
  have hseg : ∀ t ∈ uIcc (0 : ℝ) 1, (0 : E) + t • z.2 ∈ V := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    simpa using hV₀.smul_mem hz ht.1 ht.2
  have hA : hessianAverage (fun v ↦ f (z.1, v)) 0 z.2 =
      hessianAverage (fun v ↦ g (z.1, v)) 0 z.2 := by
    rw [hessianAverage_eq_integral_Icc, hessianAverage_eq_integral_Icc]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun t ht ↦ ?_
    rw [hD _ (hseg t (by rwa [uIcc_of_le zero_le_one]))]
  rw [parametricMorseCoord_def, parametricMorseCoord_def, hA,
    hD 0 (by simpa using hseg 0 (by simp))]

section Chart

/-- For a jointly `C^{n+2}` family, with `1 ≤ n ≤ ∞`, the map
`z ↦ (z.1, parametricMorseCoord G z)` is a `C^n` local diffeomorphism at each point `(b₀, 0)` of
the zero section with invertible vertical Hessian. -/
private theorem exists_partialDiffeomorph_parametricMorseCoord [CompleteSpace P]
    {G : P × E → ℝ} {b₀ : P} {n : ℕ∞} (hG : ContDiff ℝ (n + 2) G)
    (hH : (fderiv ℝ (fderiv ℝ (fun v ↦ G (b₀, v))) 0).IsInvertible) (hn : n ≠ 0) :
    ∃ Θ : PartialDiffeomorph 𝓘(ℝ, P × E) 𝓘(ℝ, P × E) (P × E) (P × E) n,
      (b₀, (0 : E)) ∈ Θ.source ∧
      ∀ z ∈ Θ.source, Θ z = (z.1, parametricMorseCoord G z) := by
  set Φ : P × E → P × E := fun z ↦ (z.1, parametricMorseCoord G z) with hΦdef
  obtain ⟨s, hsR, hs, hb₀s⟩ := mem_nhds_iff.mp (eventually_contDiffAt_parametricMorseCoord hG hH)
  have hΦs : ContDiffOn ℝ n Φ s := fun z hz ↦ (contDiffAt_fst.prodMk (hsR hz)).contDiffWithinAt
  have hΦd : HasFDerivAt Φ (ContinuousLinearMap.id ℝ (P × E)) (b₀, 0) := by
    simpa only [ContinuousLinearMap.fst_prod_snd] using
      hasFDerivAt_fst.prodMk (hasFDerivAt_parametricMorseCoord (hG.of_le le_add_self) hH)
  obtain ⟨Θ, hΘ, hb₀Θ, hΘs, hΘsymm⟩ := ContDiffOn.exists_openPartialHomeomorph hΦs hs hb₀s
    (ENat.one_le_iff_ne_zero_withTop.2 (by simpa using hn))
    (e := ContinuousLinearEquiv.refl ℝ (P × E)) hΦd.fderiv.symm
  refine ⟨{ toPartialEquiv := Θ.toPartialEquiv
            open_source := Θ.open_source
            open_target := Θ.open_target
            contMDiffOn_toFun := (hΘ ▸ hΦs.mono hΘs).contMDiffOn
            contMDiffOn_invFun := hΘsymm.contMDiffOn }, hb₀Θ, fun z _ ↦ ?_⟩
  -- the partial diffeomorphism just built has the forward map of `Θ`
  exact (by rw [hΘ] : Θ z = Φ z)

variable [FiniteDimensional ℝ P] [FiniteDimensional ℝ E] {F : P × E → ℝ} {W : Set (P × E)}
  {U : Set P} {n : ℕ∞}

/-- The local step of `TauCeti.exists_parametricMorseCoord_chart`: near a point `(b₀, 0)` of the
zero section, on a product of an open set `U₀ ∋ b₀` with a ball, the map
`z ↦ (z.1, parametricMorseCoord F z)` is a `C^n` partial diffeomorphism and `F` is in normal
form. -/
private theorem exists_parametricMorseCoord_local (hW : IsOpen W)
    (hF : ContDiffOn ℝ (n + 2) F W) (hU : IsOpen U)
    (hcrit : ∀ b ∈ U, fderiv ℝ (fun v ↦ F (b, v)) 0 = 0)
    {b₀ : P} (hb₀ : b₀ ∈ U) (hb₀W : (b₀, (0 : E)) ∈ W)
    (hH : (fderiv ℝ (fderiv ℝ (fun v ↦ F (b₀, v))) 0).IsInvertible) (hn : n ≠ 0) :
    ∃ (U₀ : Set P) (r : ℝ) (Θ : PartialDiffeomorph 𝓘(ℝ, P × E) 𝓘(ℝ, P × E) (P × E) (P × E) n),
      IsOpen U₀ ∧ b₀ ∈ U₀ ∧ 0 < r ∧ Θ.source = U₀ ×ˢ Metric.ball 0 r ∧
      U₀ ×ˢ Metric.ball 0 r ⊆ W ∧
      (∀ z ∈ U₀ ×ˢ Metric.ball 0 r,
        Θ z = (z.1, parametricMorseCoord F z)) ∧
      ∀ z ∈ U₀ ×ˢ Metric.ball 0 r, F z = F (z.1, 0) + (2 : ℝ)⁻¹ *
        fderiv ℝ (fderiv ℝ (fun v ↦ F (z.1, v))) 0
          (parametricMorseCoord F z)
          (parametricMorseCoord F z) := by
  -- Replace `F` by a globally `C^{n+2}` function `G` agreeing with it near `(b₀, 0)`.
  obtain ⟨G, hG, -, hGF⟩ := hF.exists_contDiff_eventuallyEq_of_finiteDimensional
    (hW.mem_nhds hb₀W)
  obtain ⟨U₁, V₁, hU₁, hb₀U₁, hV₁, h0V₁, hUV₁⟩ := mem_nhds_prod_iff'.mp hGF
  have hslice {b : P} (hb : b ∈ U₁) : (fun v ↦ G (b, v)) =ᶠ[𝓝 0] fun v ↦ F (b, v) :=
    Filter.mem_of_superset (hV₁.mem_nhds h0V₁) fun v hv ↦ hUV₁ (mk_mem_prod hb hv)
  have hHG {b : P} (hb : b ∈ U₁) : fderiv ℝ (fderiv ℝ (fun v ↦ G (b, v))) 0 =
      fderiv ℝ (fderiv ℝ (fun v ↦ F (b, v))) 0 :=
    (hslice hb).fderiv.fderiv_eq
  have hHG₀ : (fderiv ℝ (fderiv ℝ (fun v ↦ G (b₀, v))) 0).IsInvertible := by
    rwa [hHG hb₀U₁]
  have hcritG : ∀ᶠ b in 𝓝 b₀, fderiv ℝ (fun v ↦ G (b, v)) 0 = 0 := by
    filter_upwards [hU₁.mem_nhds hb₀U₁, hU.mem_nhds hb₀] with b hb hbU
    rw [(hslice hb).fderiv_eq, hcrit b hbU]
  obtain ⟨Θ, hb₀Θ, hΘ⟩ := exists_partialDiffeomorph_parametricMorseCoord hG hHG₀ hn
  -- Shrink to a product of an open set with a ball on which `G = F` and the normal form holds.
  have hmem : (Θ.source ∩ W) ∩ (U₁ ×ˢ V₁ ∩ {z | G z = G (z.1, 0) + (2 : ℝ)⁻¹ *
      fderiv ℝ (fderiv ℝ (fun v ↦ G (z.1, v))) 0
        (parametricMorseCoord G z)
        (parametricMorseCoord G z)}) ∈ 𝓝 (b₀, (0 : E)) :=
    Filter.inter_mem (Filter.inter_mem (Θ.open_source.mem_nhds hb₀Θ) (hW.mem_nhds hb₀W))
      (Filter.inter_mem ((hU₁.prod hV₁).mem_nhds ⟨hb₀U₁, h0V₁⟩)
        (eventually_eq_add_parametricMorseCoord (hG.of_le (by simp)) hcritG hHG₀))
  obtain ⟨U₀, V₀, hU₀, hb₀U₀, hV₀, h0V₀, hUV₀⟩ := mem_nhds_prod_iff'.mp hmem
  obtain ⟨r, hr, hrV₀⟩ := Metric.isOpen_iff.mp hV₀ 0 h0V₀
  have hsub : U₀ ×ˢ Metric.ball 0 r ⊆ U₀ ×ˢ V₀ := prod_mono le_rfl hrV₀
  -- On this product the operators of `F` and `G` agree, and so do their vertical Hessians.
  have hRF {z : P × E} (hz : z ∈ U₀ ×ˢ Metric.ball 0 r) :
      parametricMorseCoord F z = parametricMorseCoord G z := by
    refine parametricMorseCoord_congr_of_eqOn Metric.isOpen_ball
      ((convex_ball 0 r).starConvex (Metric.mem_ball_self hr)) (fun v hv ↦ ?_) hz.2
    exact (hUV₁ (hUV₀ (hsub (mk_mem_prod hz.1 hv))).2.1).symm
  have hzero {b : P} (hb : b ∈ U₀) : (b, (0 : E)) ∈ U₀ ×ˢ Metric.ball 0 r :=
    mk_mem_prod hb (Metric.mem_ball_self hr)
  have hprod : IsOpen (U₀ ×ˢ Metric.ball (0 : E) r) := hU₀.prod Metric.isOpen_ball
  refine ⟨U₀, r, Θ.restrOpen _ hprod, hU₀, hb₀U₀, hr, ?_, fun z hz ↦ (hUV₀ (hsub hz)).1.2,
    fun z hz ↦ ?_, fun z hz ↦ ?_⟩
  · rw [PartialDiffeomorph.restrOpen_source]
    exact inter_eq_right.mpr fun z hz ↦ (hUV₀ (hsub hz)).1.1
  · rw [PartialDiffeomorph.coe_restrOpen, hΘ z (hUV₀ (hsub hz)).1.1, hRF hz]
  · have hz' := hUV₀ (hsub hz)
    have hz₀ := hUV₀ (hsub (hzero hz.1))
    rw [hRF hz, ← hUV₁ hz'.2.1, ← hUV₁ hz₀.2.1, ← hHG hz₀.2.1.1]
    exact hz'.2.2

/-- **The parametric Morse lemma along the whole zero section.** Let `F (b, v)` be `C^{n+2}`, with
`1 ≤ n ≤ ∞`, on an open set `W` containing the zero section over an open set `U` of the base,
with critical zero section and invertible vertical Hessian `H_b` at every `(b, 0)`, `b ∈ U`.
Then there is a single chart `ψ`, `C^n` in both directions and with source in `W` containing the
whole zero section over `U`, which is given on its source by the canonical parametric Morse
coordinate, `ψ (b, v) = (b, parametricMorseCoord F (b, v))`, preserves the base in both
directions, and puts `F` in normal form:
`F (b, v) = F (b, 0) + ½ H_b (ψ (b, v)).2 (ψ (b, v)).2`. -/
theorem exists_parametricMorseCoord_chart (hW : IsOpen W) (hF : ContDiffOn ℝ (n + 2) F W)
    (hU : IsOpen U) (hUW : ∀ b ∈ U, (b, (0 : E)) ∈ W)
    (hcrit : ∀ b ∈ U, fderiv ℝ (fun v ↦ F (b, v)) 0 = 0)
    (hH : ∀ b ∈ U, (fderiv ℝ (fderiv ℝ (fun v ↦ F (b, v))) 0).IsInvertible) (hn : n ≠ 0) :
    ∃ ψ : OpenPartialHomeomorph (P × E) (P × E),
      ψ.source ⊆ W ∧ (∀ b ∈ U, (b, (0 : E)) ∈ ψ.source) ∧
      (∀ z ∈ ψ.source, ψ z = (z.1, parametricMorseCoord F z)) ∧
      (∀ z ∈ ψ.target, (ψ.symm z).1 = z.1) ∧
      ContDiffOn ℝ n ψ ψ.source ∧ ContDiffOn ℝ n ψ.symm ψ.target ∧
      ∀ z ∈ ψ.source, F z = F (z.1, 0) + (2 : ℝ)⁻¹ *
        fderiv ℝ (fderiv ℝ (fun v ↦ F (z.1, v))) 0 (ψ z).2 (ψ z).2 := by
  have : Nonempty (PartialDiffeomorph 𝓘(ℝ, P × E) 𝓘(ℝ, P × E) (P × E) (P × E) n) :=
    ⟨(Diffeomorph.refl 𝓘(ℝ, P × E) (P × E) n).toPartialDiffeomorph⟩
  choose! U₀ r Θ hU₀ hbU₀ hr hΘsource hsubW hΘeq hnf using fun b (hb : b ∈ U) ↦
    exists_parametricMorseCoord_local hW hF hU hcrit hb (hUW b hb) (hH b hb) hn
  set Φ : P × E → P × E := fun z ↦ (z.1, parametricMorseCoord F z)
    with hΦdef
  set S : Set (P × E) := ⋃ b ∈ U, U₀ b ×ˢ Metric.ball 0 (r b) with hSdef
  have hS : IsOpen S :=
    isOpen_biUnion fun b hb ↦ (hU₀ b hb).prod Metric.isOpen_ball
  have hmemS {z : P × E} : z ∈ S ↔ ∃ b ∈ U, z ∈ U₀ b ×ˢ Metric.ball 0 (r b) := by
    simp only [hSdef, mem_iUnion, exists_prop]
  -- On each product piece, `Φ` is the partial diffeomorphism `Θ b`.
  have hΦΘ {b : P} (hb : b ∈ U) {z : P × E} (hz : z ∈ U₀ b ×ˢ Metric.ball 0 (r b)) :
      Φ z = Θ b z := (hΘeq b hb z hz).symm
  -- The fibres of the pieces are nested balls about `0`, so `Φ` is injective on their union.
  have hinj : InjOn Φ S := by
    intro z hz z' hz' h
    obtain ⟨b, hb, hzb⟩ := hmemS.mp hz
    obtain ⟨b', hb', hzb'⟩ := hmemS.mp hz'
    have h1 : z.1 = z'.1 := by simpa [hΦdef] using congrArg Prod.fst h
    wlog hle : r b ≤ r b' generalizing z z' b b'
    · exact (this hz' hz h.symm b' hb' hzb' b hb hzb h1.symm (le_of_not_ge hle)).symm
    have hzb'' : z ∈ U₀ b' ×ˢ Metric.ball 0 (r b') :=
      ⟨h1 ▸ hzb'.1, Metric.ball_subset_ball hle hzb.2⟩
    refine (Θ b').toPartialEquiv.injOn (hΘsource b' hb' ▸ hzb'') (hΘsource b' hb' ▸ hzb') ?_
    rw [← hΦΘ hb' hzb'', ← hΦΘ hb' hzb', h]
  have hld : IsLocalDiffeomorphOn 𝓘(ℝ, P × E) 𝓘(ℝ, P × E) n Φ S := fun ⟨z, hz⟩ ↦ by
    obtain ⟨b, hb, hzb⟩ := hmemS.mp hz
    exact isLocalDiffeomorphAt_of_eqOn (hΘsource b hb ▸ hzb) fun z' hz' ↦
      hΦΘ hb (hΘsource b hb ▸ hz')
  have : Nonempty (P × E) := ⟨0⟩
  let ψ := (hld.partialDiffeomorphOfInjOn hS hinj).toOpenPartialHomeomorph
  have hψ : (ψ : P × E → P × E) = Φ := by
    simp only [ψ, PartialDiffeomorph.toFun'_toOpenPartialHomeomorph,
      IsLocalDiffeomorphOn.coe_partialDiffeomorphOfInjOn]
  have hψsource : ψ.source = S := by
    simp only [ψ, PartialDiffeomorph.toOpenPartialHomeomorph_source,
      IsLocalDiffeomorphOn.partialDiffeomorphOfInjOn_source]
  refine ⟨ψ, fun z hz ↦ ?_, fun b hb ↦ ?_, fun z _ ↦ by rw [hψ], fun z hz ↦ ?_,
    (hld.partialDiffeomorphOfInjOn hS hinj).contMDiffOn_toFun.contDiffOn,
    (hld.partialDiffeomorphOfInjOn hS hinj).contMDiffOn_invFun.contDiffOn, fun z hz ↦ ?_⟩
  · obtain ⟨b, hb, hzb⟩ := hmemS.mp (hψsource ▸ hz)
    exact hsubW b hb hzb
  · rw [hψsource]
    exact hmemS.mpr ⟨b, hb, hbU₀ b hb, Metric.mem_ball_self (hr b hb)⟩
  · -- the first coordinate of `ψ (ψ.symm z) = z` is that of `ψ.symm z`
    have h := congrArg Prod.fst (ψ.right_inv hz)
    rwa [hψ] at h
  · obtain ⟨b, hb, hzb⟩ := hmemS.mp (hψsource ▸ hz)
    rw [hψ]
    exact hnf b hb z hzb

end Chart

end TauCeti
