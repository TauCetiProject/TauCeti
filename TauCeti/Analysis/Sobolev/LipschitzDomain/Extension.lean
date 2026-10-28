/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.LipschitzDomain.Localization
public import TauCeti.Analysis.Sobolev.Trace.Epigraph.Extension
import TauCeti.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Sobolev extension through a Lipschitz boundary chart

Let `Ω` be an open subset of the Euclidean product `ℝ × E` with a Lipschitz boundary chart: rigid
coordinates `e` identify `Ω` inside the cylinder `normalCylinder a b` with the region above the
graph of an `L`-Lipschitz function `φ` with `φ 0 = 0`. Let `ψ` be a smooth cutoff whose support
lies, in chart coordinates, in the shorter cylinder `normalCylinder (a - 2 * L * b) b`. This file
constructs a bounded operator

`TauCeti.W1p.lipschitzChartExtensionL : W^{1,p}(Ω) →L[ℝ] W^{1,p}(ℝ × E)`

for every `1 ≤ p ≤ ∞`, whose value on `Ω` is `ψ u`
(`TauCeti.W1p.restrictL_lipschitzChartExtensionL`) and which vanishes outside the chart cylinder
(`TauCeti.W1p.value_lipschitzChartExtensionL_ae_eq_zero`). Its norm is at most `4 M (1 + L)²`
when `ψ` and its gradient are bounded by `M`.

The construction localizes `ψ u` to the whole epigraph in chart coordinates
(`TauCeti.W1p.lipschitzChartLocalizeL`), extends across the graph by flattening and even
reflection (`TauCeti.W1p.normalEpigraphExtensionL`), and returns to the original coordinates.
The shorter normal radius of the support is what keeps the reflected function inside
the chart cylinder: over a tangential point `y` with `‖y‖ < b`, the graph height satisfies
`|φ y| ≤ L b`, so the reflection `t ↦ 2 φ y - t` maps `(-(a - 2 L b), a - 2 L b)` into `(-a, a)`.
Without it the reflected values could reach points of `Ω` outside the chart, and the extension
would not restrict to `ψ u`.

These local extensions are the boundary pieces of the classical extension operator for a bounded
Lipschitz domain: one sums them over a partition of unity subordinate to a finite chart cover
(`Set.IsLipschitzDomainWith.exists_finset_isLipschitzChartWith_cover`), together with the
extension by zero of an interior piece.

## Main declarations

* `TauCeti.W1p.lipschitzChartExtensionL`: the extension operator through one chart.
* `TauCeti.W1p.value_lipschitzChartExtensionL_ae`: its value on `Ω` is `ψ u`.
* `TauCeti.W1p.restrictL_lipschitzChartExtensionL`: restricted to `Ω`, it is
  `TauCeti.W1p.contDiffSMul ψ u`.
* `TauCeti.W1p.value_lipschitzChartExtensionL_ae_eq_zero`: it vanishes outside the chart
  cylinder.
* `TauCeti.W1p.norm_lipschitzChartExtensionL_le`, `TauCeti.W1p.opNorm_lipschitzChartExtensionL_le`:
  the bound `4 M (1 + L)²`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.4, Theorem 1 (extension by local
  flattening, reflection and a partition of unity, for `C¹` boundaries).
* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised ed.,
  §4.4 (the `W^{1,p}` extension for Lipschitz boundaries, by reflection across the local
  Lipschitz graph).
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal ContDiff Gradient

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {Ω : Opens (WithLp 2 (ℝ × E))} {L : ℝ≥0} {e : WithLp 2 (ℝ × E) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)}
  {φ : E → ℝ} {a b : ℝ} {ψ : WithLp 2 (ℝ × E) → ℝ} {M : ℝ}

/-! ### Reflection across the graph -/

/-- Reflection across the graph of `φ` along the normal coordinate:
`(t, y) ↦ (2 φ y - t, y)`. -/
private def graphReflection (φ : E → ℝ) (z : WithLp 2 (ℝ × E)) : WithLp 2 (ℝ × E) :=
  WithLp.toLp 2 (2 * φ z.snd - z.fst, z.snd)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
private theorem graphReflection_graphReflection (z : WithLp 2 (ℝ × E)) :
    graphReflection φ (graphReflection φ z) = z := by
  cases z
  simp [graphReflection]

omit [InnerProductSpace ℝ E] in
/-- The reflection of a point below the graph lies above it. -/
private theorem graphReflection_mem_normalEpigraph_iff (hφ : Continuous φ)
    (z : WithLp 2 (ℝ × E)) :
    graphReflection φ z ∈ normalEpigraph ⟨φ, hφ⟩ ↔ z.fst < φ z.snd := by
  rw [mem_normalEpigraph]
  simp only [graphReflection, ContinuousMap.coe_mk, WithLp.toLp_fst, WithLp.toLp_snd]
  constructor <;> intro h <;> linarith

omit [InnerProductSpace ℝ E] in
/-- Reflection across an `L`-Lipschitz graph through the origin maps the cylinder of normal
radius `a - 2 L b` and tangential radius `b` into the cylinder of radii `a` and `b`. -/
private theorem graphReflection_mem_normalCylinder (h0 : φ 0 = 0) (hφ : LipschitzWith L φ)
    {z : WithLp 2 (ℝ × E)} (hz : z ∈ normalCylinder (a - 2 * L * b) b) :
    graphReflection φ z ∈ normalCylinder a b := by
  rw [mem_normalCylinder] at hz ⊢
  obtain ⟨h1, h2, h3⟩ := hz
  have hheight : |φ z.snd| ≤ L * b := by
    have := hφ.dist_le_mul z.snd 0
    rw [h0, Real.dist_eq, sub_zero, dist_zero_right] at this
    exact this.trans (mul_le_mul_of_nonneg_left h3.le L.coe_nonneg)
  simp only [graphReflection, WithLp.toLp_fst, WithLp.toLp_snd]
  refine ⟨?_, ?_, h3⟩ <;> linarith [abs_le.mp hheight]

/-! ### The open sets of the construction -/

/-- The points whose chart coordinates lie in the cylinder `normalCylinder a b`. -/
private def chartCylinder (e : WithLp 2 (ℝ × E) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (a b : ℝ) :
    Opens (WithLp 2 (ℝ × E)) :=
  ⟨e ⁻¹' normalCylinder a b, (isOpen_normalCylinder a b).preimage e.continuous⟩

/-- The cylinder carrying the support of the cutoff lies in the chart cylinder. -/
private theorem normalCylinder_sub_subset
    (h : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzChartWith L e φ a b) :
    normalCylinder (E := E) (a - 2 * L * b) b ⊆ normalCylinder a b :=
  normalCylinder_mono (by nlinarith [((Set.isLipschitzChartWith_iff ..).1 h).2.1, L.coe_nonneg])
    le_rfl

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Reflection across the graph is reflection in the flat boundary, conjugated by graph
flattening; in particular it preserves Lebesgue measure. -/
private theorem measurePreserving_graphReflection (hφ : Continuous φ) :
    MeasurePreserving (graphReflection φ) := by
  convert (measurePreserving_graphFlattening_symm φ hφ).comp
    ((measurePreserving_normalReflection (E := E) 0).comp
      (measurePreserving_graphFlattening φ hφ)) using 1
  funext z
  simp only [graphReflection, Function.comp_apply, graphFlattening_apply, normalReflection_apply,
    graphFlattening_symm_apply, WithLp.toLp_fst, WithLp.toLp_snd]
  congr 2
  ring

/-! ### The extension operator -/

/-- **Sobolev extension through a Lipschitz boundary chart.** For a Lipschitz boundary chart of
`Ω` with coordinates `e`, graph `φ` and radii `a`, `b`, and a smooth cutoff `ψ` whose support has
chart coordinates in the shortened cylinder `normalCylinder (a - 2 * L * b) b`, the operator
sends `u ∈ W^{1,p}(Ω)` to a whole-space Sobolev function equal to `ψ u` on `Ω`
(`TauCeti.W1p.restrictL_lipschitzChartExtensionL`): multiply by the cutoff, extend across the
graph by reflection in flattened chart coordinates, and return to the original coordinates. -/
def W1p.lipschitzChartExtensionL
    (h : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzChartWith L e φ a b)
    (ψ : WithLp 2 (ℝ × E) → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hM : 0 ≤ M)
    (hψM : ∀ x ∈ Ω, |ψ x| ≤ M) (hgM : ∀ x ∈ Ω, ‖∇ ψ x‖ ≤ M)
    (hs : tsupport ψ ⊆ e ⁻¹' normalCylinder (a - 2 * L * b) b) :
    W1p volume Ω p →L[ℝ] W1p volume (⊤ : Opens (WithLp 2 (ℝ × E))) p :=
  (W1p.compAffineIsometryEquivL e (by simp)).comp <|
    (W1p.normalEpigraphExtensionL (φ := ⟨φ, _⟩) h.lipschitzWith).comp <|
    W1p.lipschitzChartLocalizeL h ψ hψ hM hψM hgM
      (hs.trans (preimage_mono (normalCylinder_sub_subset h)))

private theorem lipschitzChartExtensionL_apply
    (h : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzChartWith L e φ a b)
    (hψ : ContDiff ℝ ∞ ψ) (hM : 0 ≤ M)
    (hψM : ∀ x ∈ Ω, |ψ x| ≤ M) (hgM : ∀ x ∈ Ω, ‖∇ ψ x‖ ≤ M)
    (hs : tsupport ψ ⊆ e ⁻¹' normalCylinder (a - 2 * L * b) b) (u : W1p volume Ω p) :
    W1p.lipschitzChartExtensionL h ψ hψ hM hψM hgM hs u =
      W1p.compAffineIsometryEquivL e (by simp)
        (W1p.normalEpigraphExtensionL (φ := ⟨φ, _⟩) h.lipschitzWith
          (W1p.lipschitzChartLocalizeL h ψ hψ hM hψM hgM
            (hs.trans (preimage_mono (normalCylinder_sub_subset h))) u)) :=
  (rfl)

/-- The pointwise description of the extension behind its two value theorems: above the graph it
is the cutoff product `ψ u` extended by zero from the chart cylinder, and below the graph it is
the same function at the reflected point. -/
private theorem value_lipschitzChartExtensionL_ae_aux
    (h : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzChartWith L e φ a b)
    (hψ : ContDiff ℝ ∞ ψ) (hM : 0 ≤ M)
    (hψM : ∀ x ∈ Ω, |ψ x| ≤ M) (hgM : ∀ x ∈ Ω, ‖∇ ψ x‖ ≤ M)
    (hs : tsupport ψ ⊆ e ⁻¹' normalCylinder (a - 2 * L * b) b) (u : W1p volume Ω p) :
    let f := ((Ω ⊓ chartCylinder e a b : Opens (WithLp 2 (ℝ × E))) : Set _).indicator
      fun x => ψ x • W1p.value u x
    ∀ᵐ x ∂volume, W1p.value (W1p.lipschitzChartExtensionL h ψ hψ hM hψM hgM hs u) x =
      if φ (e x).snd < (e x).fst then f x
      else if (e x).fst < φ (e x).snd then f (e.symm (graphReflection φ (e x))) else 0 := by
  intro f
  have hφc : Continuous φ := h.lipschitzWith.continuous
  have hs' := hs.trans (preimage_mono (normalCylinder_sub_subset h))
  let v := W1p.lipschitzChartLocalizeL h ψ hψ hM hψM hgM hs' u
  have hchart : ∀ᵐ z ∂volume, z ∈ normalEpigraph ⟨φ, hφc⟩ → W1p.value v z = f (e.symm z) := by
    have h1 := (ae_restrict_iff' (normalEpigraph ⟨φ, hφc⟩).isOpen.measurableSet).1
      (W1p.value_lipschitzChartLocalizeL_ae h hψ hM hψM hgM hs' u)
    filter_upwards [h1] with z hz hzG
    rw [hz hzG]
    by_cases hzC : e (e.symm z) ∈ normalCylinder a b
    · by_cases hzΩ : e.symm z ∈ Ω
      · have hzU : e.symm z ∈ (Ω ⊓ chartCylinder e a b : Opens _) := ⟨hzΩ, hzC⟩
        simp only [f, indicator_of_mem hzΩ, indicator_of_mem hzU]
      · have hzU : e.symm z ∉ (Ω ⊓ chartCylinder e a b : Opens _) := fun hx => hzΩ hx.1
        simp only [f, indicator_of_notMem hzΩ, indicator_of_notMem hzU]
    · have hψz : ψ (e.symm z) = 0 :=
        image_eq_zero_of_notMem_tsupport fun hzs => hzC (hs' hzs)
      simp [f, indicator, hψz]
  have hext := W1p.value_normalEpigraphExtensionL_ae (φ := ⟨φ, hφc⟩) h.lipschitzWith v
  have hfrom := W1p.value_compAffineIsometryEquivL_ae (p := p) (U := ⊤) (V := ⊤) e (by simp)
    (W1p.normalEpigraphExtensionL (φ := ⟨φ, hφc⟩) h.lipschitzWith v)
  rw [← lipschitzChartExtensionL_apply h hψ hM hψM hgM hs] at hfrom
  simp only [Opens.coe_top, Measure.restrict_univ] at hfrom
  have he := e.measurePreserving.quasiMeasurePreserving
  filter_upwards [hfrom, he.ae hext, he.ae hchart,
    ((measurePreserving_graphReflection hφc).comp e.measurePreserving).quasiMeasurePreserving.ae
      hchart] with x hx1 hx2 hx3 hx4
  simp only [Function.comp_apply, ContinuousMap.coe_mk] at hx2 hx4
  rw [hx1, hx2]
  split_ifs with habove hbelow
  · rw [hx3 ((mem_normalEpigraph _ _).2 habove), AffineIsometryEquiv.symm_apply_apply]
  · exact hx4 ((graphReflection_mem_normalEpigraph_iff hφc _).2 hbelow)
  · rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- A point where the cutoff product is nonzero has chart coordinates in the shorter cylinder. -/
private theorem mem_normalCylinder_of_indicator_ne_zero
    (hs : tsupport ψ ⊆ e ⁻¹' normalCylinder (a - 2 * L * b) b) {g : WithLp 2 (ℝ × E) → ℝ}
    {S : Set (WithLp 2 (ℝ × E))} {y : WithLp 2 (ℝ × E)}
    (hy : S.indicator (fun x => ψ x • g x) y ≠ 0) :
    e y ∈ normalCylinder (a - 2 * L * b) b := by
  refine hs (subset_tsupport ψ fun hψy => hy ?_)
  by_cases hyS : y ∈ S <;> simp [indicator, hyS, hψy]

/-- **The extension is supported in the chart cylinder.** Outside the points whose chart
coordinates lie in `normalCylinder a b`, the extension vanishes almost everywhere. -/
theorem W1p.value_lipschitzChartExtensionL_ae_eq_zero
    (h : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzChartWith L e φ a b)
    (hψ : ContDiff ℝ ∞ ψ) (hM : 0 ≤ M)
    (hψM : ∀ x ∈ Ω, |ψ x| ≤ M) (hgM : ∀ x ∈ Ω, ‖∇ ψ x‖ ≤ M)
    (hs : tsupport ψ ⊆ e ⁻¹' normalCylinder (a - 2 * L * b) b) (u : W1p volume Ω p) :
    ∀ᵐ x ∂volume, e x ∉ normalCylinder a b →
      W1p.value (W1p.lipschitzChartExtensionL h ψ hψ hM hψM hgM hs u) x = 0 := by
  filter_upwards [value_lipschitzChartExtensionL_ae_aux h hψ hM hψM hgM hs u] with x hx hxC
  rw [hx]
  have hxU : x ∉ ((Ω ⊓ chartCylinder e a b : Opens (WithLp 2 (ℝ × E))) : Set _) :=
    fun hxU => hxC hxU.2
  split_ifs
  · exact indicator_of_notMem hxU _
  · by_contra hne
    have hR := graphReflection_mem_normalCylinder h.apply_zero h.lipschitzWith
      (by simpa using mem_normalCylinder_of_indicator_ne_zero hs hne)
    exact hxC (by simpa [graphReflection_graphReflection] using hR)
  · rfl

/-- **The extension restricts to the cutoff product.** On `Ω`, the value of the extension of
`u` is `ψ u` almost everywhere. -/
theorem W1p.value_lipschitzChartExtensionL_ae
    (h : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzChartWith L e φ a b)
    (hψ : ContDiff ℝ ∞ ψ) (hM : 0 ≤ M)
    (hψM : ∀ x ∈ Ω, |ψ x| ≤ M) (hgM : ∀ x ∈ Ω, ‖∇ ψ x‖ ≤ M)
    (hs : tsupport ψ ⊆ e ⁻¹' normalCylinder (a - 2 * L * b) b) (u : W1p volume Ω p) :
    W1p.value (W1p.lipschitzChartExtensionL h ψ hψ hM hψM hgM hs u) =ᵐ[volume.restrict Ω]
      fun x => ψ x • W1p.value u x := by
  filter_upwards [ae_restrict_of_ae (value_lipschitzChartExtensionL_ae_aux h hψ hM hψM hgM hs u),
    ae_restrict_of_ae (W1p.value_lipschitzChartExtensionL_ae_eq_zero h hψ hM hψM hgM hs u),
    ae_restrict_mem Ω.isOpen.measurableSet] with x hx hzero hxΩ
  by_cases hxC : e x ∈ normalCylinder a b
  · have hxU : x ∈ ((Ω ⊓ chartCylinder e a b : Opens (WithLp 2 (ℝ × E))) : Set _) :=
      ⟨hxΩ, hxC⟩
    rw [hx, ite_eq_left ((h.toIsLipschitzChart.mem_iff hxC).1 hxΩ), indicator_of_mem hxU]
  · have hψx : ψ x = 0 := image_eq_zero_of_notMem_tsupport fun hxs =>
      hxC (normalCylinder_sub_subset h (hs hxs))
    rw [hzero hxC, hψx, zero_smul]

-- As for `W1p.restrictL_normalEpigraphExtensionL`, this is a pre-simp lemma: `simp` would
-- otherwise first rewrite the coercion of `⊤` in the type of the extension.
/-- **The extension is a right inverse of restriction up to the cutoff.** Restricting the
extension of `u` to `Ω` gives the cutoff product `ψ u`. -/
@[simp↓]
theorem W1p.restrictL_lipschitzChartExtensionL
    (h : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzChartWith L e φ a b)
    (hψ : ContDiff ℝ ∞ ψ) (hM : 0 ≤ M)
    (hψM : ∀ x ∈ Ω, |ψ x| ≤ M) (hgM : ∀ x ∈ Ω, ‖∇ ψ x‖ ≤ M)
    (hs : tsupport ψ ⊆ e ⁻¹' normalCylinder (a - 2 * L * b) b) (u : W1p volume Ω p) :
    W1p.restrictL le_top (W1p.lipschitzChartExtensionL h ψ hψ hM hψM hgM hs u) =
      W1p.contDiffSMul ψ hψ hM hψM hgM u := by
  apply W1p.ext_value
  apply Lp.ext
  filter_upwards [W1p.value_restrictL_ae le_top
      (W1p.lipschitzChartExtensionL h ψ hψ hM hψM hgM hs u),
    W1p.value_lipschitzChartExtensionL_ae h hψ hM hψM hgM hs u,
    W1p.value_contDiffSMul_ae hψ hM hψM hgM u] with x h1 h2 h3
  rw [h1, h2, h3]

/-- The extension through a chart multiplies the `W^{1,p}` norm by at most `4 M (1 + L)²`. -/
theorem W1p.norm_lipschitzChartExtensionL_le
    (h : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzChartWith L e φ a b)
    (hψ : ContDiff ℝ ∞ ψ) (hM : 0 ≤ M)
    (hψM : ∀ x ∈ Ω, |ψ x| ≤ M) (hgM : ∀ x ∈ Ω, ‖∇ ψ x‖ ≤ M)
    (hs : tsupport ψ ⊆ e ⁻¹' normalCylinder (a - 2 * L * b) b) (u : W1p volume Ω p) :
    ‖W1p.lipschitzChartExtensionL h ψ hψ hM hψM hgM hs u‖ ≤ 4 * M * (1 + L) ^ 2 * ‖u‖ := by
  rw [lipschitzChartExtensionL_apply]
  refine (W1p.norm_compAffineIsometryEquivL_le e _ _).trans
    ((W1p.norm_normalEpigraphExtensionL_le _ _).trans ?_)
  have hloc := W1p.norm_lipschitzChartLocalizeL_le h hψ hM hψM hgM
    (hs.trans (preimage_mono (normalCylinder_sub_subset h))) u
  calc _ ≤ 2 * (1 + (L : ℝ)) ^ 2 * (2 * M * ‖u‖) := by gcongr
    _ = _ := by ring

/-- The extension through a chart has operator norm at most `4 M (1 + L)²`. -/
theorem W1p.opNorm_lipschitzChartExtensionL_le
    (h : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzChartWith L e φ a b)
    (hψ : ContDiff ℝ ∞ ψ) (hM : 0 ≤ M)
    (hψM : ∀ x ∈ Ω, |ψ x| ≤ M) (hgM : ∀ x ∈ Ω, ‖∇ ψ x‖ ≤ M)
    (hs : tsupport ψ ⊆ e ⁻¹' normalCylinder (a - 2 * L * b) b) :
    ‖W1p.lipschitzChartExtensionL (p := p) h ψ hψ hM hψM hgM hs‖ ≤ 4 * M * (1 + L) ^ 2 :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    (W1p.norm_lipschitzChartExtensionL_le h hψ hM hψM hgM hs)

end TauCeti
