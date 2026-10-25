/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.LipschitzDomain.Extension
import Mathlib.Geometry.Manifold.PartitionOfUnity
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Sobolev.W1p.Density

/-!
# Extension from bounded Lipschitz domains

Every bounded Lipschitz domain in `WithLp 2 (ℝ × E)` admits a bounded linear extension
`W^{1,p}(Ω) → W^{1,p}(ℝ × E)` for every `1 ≤ p ≤ ∞`. Restriction is a left inverse of this
operator. The construction uses a finite smooth partition of unity on the closure of the
domain, the local graph-reflection extension at boundary points, and zero extension of the
interior pieces. No differentiability of the boundary graphs is required.

As a consequence, restrictions to `Ω` of test functions on the whole space are dense in
`W^{1,p}(Ω)` for `p < ∞` (`TauCeti.W1p.denseRange_restrictL_ofTestFunctionₗ_top`). These
restrictions are smooth up to the boundary, so a bounded operator on `W^{1,p}(Ω)` is determined
by its values on functions continuous on `closure Ω`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.4, Theorem 1, for the
  partition-of-unity construction for smooth boundaries.
* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised ed.,
  §4.4, for extension across Lipschitz graphs.
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace Metric
open scoped ContDiff ENNReal NNReal Gradient Manifold Distributions

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {Ω : Opens (WithLp 2 (ℝ × E))} {L : ℝ≥0} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Near each point of the closure, cutoffs supported in a sufficiently small neighbourhood
admit extensions. The neighbourhood is bounded to give compactly supported partition functions. -/
private theorem exists_local_extension
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    {x : WithLp 2 (ℝ × E)} (hx : x ∈ closure (Ω : Set (WithLp 2 (ℝ × E)))) :
    ∃ U : Set (WithLp 2 (ℝ × E)), IsOpen U ∧ x ∈ U ∧ Bornology.IsBounded U ∧
      ∀ (ψ : WithLp 2 (ℝ × E) → ℝ) (hψ : ContDiff ℝ ∞ ψ) (M : ℝ) (hM : 0 ≤ M)
        (hv : ∀ y ∈ Ω, |ψ y| ≤ M) (hg : ∀ y ∈ Ω, ‖∇ ψ y‖ ≤ M), tsupport ψ ⊆ U →
        ∃ T : W1p volume Ω p →L[ℝ] W1p volume (⊤ : Opens (WithLp 2 (ℝ × E))) p,
          ∀ u, W1p.restrictL le_top (T u) = W1p.contDiffSMul ψ hψ hM hv hg u := by
  by_cases hxΩ : x ∈ Ω
  · refine ⟨(Ω : Set _) ∩ ball x 1, Ω.isOpen.inter isOpen_ball,
      ⟨hxΩ, mem_ball_self zero_lt_one⟩, isBounded_ball.subset inter_subset_right, ?_⟩
    intro ψ hψ M hM hv hg hs
    have hsΩ : tsupport ψ ⊆ Ω := hs.trans inter_subset_left
    refine ⟨W1p.localizeL le_top ψ hψ hM hv hg (fun _ hy => hsΩ hy.2), ?_⟩
    intro u
    exact W1p.restrictL_localizeL le_top hψ hM hv hg _ u
  · have hxf : x ∈ frontier (Ω : Set (WithLp 2 (ℝ × E))) := by
      rw [frontier, Ω.isOpen.interior_eq]
      exact ⟨hx, hxΩ⟩
    obtain ⟨e, φ, a, b, hex, hc⟩ := (Set.isLipschitzDomainAtWith_iff ..).1
      (((Set.isLipschitzDomainWith_iff ..).1 hΩ).2 x hxf)
    have ha := ((Set.isLipschitzChartWith_iff ..).1 hc).1
    have hb := ((Set.isLipschitzChartWith_iff ..).1 hc).2.1
    -- Keep a positive margin for reflection in the normal direction.
    let b' := min b (a / (4 * (L + 1)))
    have hb' : 0 < b' := lt_min hb (div_pos ha (by positivity))
    have hb'b : b' ≤ b := min_le_left _ _
    have hmargin : 0 < a - 2 * L * b' := by
      have hle := min_le_right b (a / (4 * (L + 1)))
      have hden : (0 : ℝ) < 4 * (L + 1) := by positivity
      have hprod := (le_div_iff₀ hden).1 hle
      nlinarith [L.coe_nonneg, ha]
    have hc' := hc.mono_radii ha hb' le_rfl hb'b
    refine ⟨(e ⁻¹' normalCylinder (a - 2 * L * b') b') ∩ ball x 1,
      ((isOpen_normalCylinder _ _).preimage e.continuous).inter isOpen_ball,
      ⟨by simpa [hex] using zero_mem_normalCylinder (E := E) hmargin hb',
        mem_ball_self zero_lt_one⟩, isBounded_ball.subset inter_subset_right, ?_⟩
    intro ψ hψ M hM hv hg hs
    exact ⟨W1p.lipschitzChartExtensionL hc' ψ hψ hM hv hg (hs.trans inter_subset_left),
      W1p.restrictL_lipschitzChartExtensionL hc' hψ hM hv hg _⟩

/-- **Extension theorem for bounded Lipschitz domains.** There is a bounded linear extension
from `W^{1,p}(Ω)` to the whole space, and restriction to `Ω` recovers the original function.
Both endpoint exponents `p = 1` and `p = ∞` are included. -/
theorem W1p.exists_extensionL_of_isLipschitzDomainWith
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : Bornology.IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) :
    ∃ T : W1p volume Ω p →L[ℝ] W1p volume (⊤ : Opens (WithLp 2 (ℝ × E))) p,
      (W1p.restrictL le_top).comp T = ContinuousLinearMap.id ℝ (W1p volume Ω p) := by
  classical
  let K := closure (Ω : Set (WithLp 2 (ℝ × E)))
  have hK : IsCompact K := isCompact_of_isClosed_isBounded isClosed_closure hb.closure
  choose U ho hxU hbound hlocal using fun x : K => exists_local_extension (p := p) hΩ x.property
  obtain ⟨t, hcover⟩ := hK.elim_finite_subcover U ho (by
    intro x hx
    exact mem_iUnion.2 ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩)
  let V : t → Set (WithLp 2 (ℝ × E)) := fun i => U i.val
  have hV : K ⊆ ⋃ i, V i := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.1 (hcover hx)
    exact mem_iUnion.2 ⟨⟨i, hi⟩, hxi⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate (𝓘(ℝ, WithLp 2 (ℝ × E)))
    isClosed_closure V (fun i => ho i.val) hV
  have hdiff (i : t) : ContDiff ℝ ∞ (ρ i) := contMDiff_iff_contDiff.1 (ρ i).contMDiff
  have hcpt (i : t) : HasCompactSupport (ρ i) :=
    isCompact_of_isClosed_isBounded (isClosed_tsupport _) ((hbound i.val).subset (hρ i))
  choose M hM hv hg using fun i : t =>
    ((hdiff i).of_le (by simp)).exists_abs_le_and_norm_gradient_le (hcpt i)
  choose T hT using fun i : t => hlocal i.val (ρ i) (hdiff i) (M i) (hM i)
    (fun x _ => hv i x) (fun x _ => hg i x) (hρ i)
  refine ⟨∑ i, T i, ?_⟩
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply, sum_apply,
    ContinuousLinearMap.id_apply, map_sum]
  apply W1p.ext_value
  apply Lp.ext
  have hsum := W1p.value_finsetSum_ae (Omega := Ω) Finset.univ
    (fun i : t => W1p.restrictL le_top (T i u))
  have hval (i : t) := W1p.value_contDiffSMul_ae (hdiff i) (hM i)
    (fun x _ => hv i x) (fun x _ => hg i x) u
  filter_upwards [hsum, ae_all_iff.2 hval, ae_restrict_mem Ω.isOpen.measurableSet]
    with x hx hxv hxΩ
  rw [hx]
  simp only [hT, hxv, smul_eq_mul, ← Finset.sum_mul]
  have hone := ρ.sum_eq_one (subset_closure hxΩ)
  rw [finsum_eq_sum_of_fintype] at hone
  rw [hone, one_mul]

/-- **Density of functions smooth up to the boundary.** On a bounded Lipschitz domain and for
`p < ∞`, the restrictions to `Ω` of test functions on the whole space are dense in
`W^{1,p}(Ω)`. -/
theorem W1p.denseRange_restrictL_ofTestFunctionₗ_top (hp : p ≠ (∞ : ℝ≥0∞))
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : Bornology.IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) :
    DenseRange fun φ : 𝓓((⊤ : Opens (WithLp 2 (ℝ × E))), ℝ) =>
      W1p.restrictL (le_top : Ω ≤ ⊤) (W1p.ofTestFunctionₗ volume ⊤ p φ) := by
  obtain ⟨T, hT⟩ := W1p.exists_extensionL_of_isLipschitzDomainWith (p := p) hΩ hb
  have hsurj : Function.Surjective (W1p.restrictL (p := p) (mu := volume)
      (le_top : Ω ≤ ⊤)) := fun u => ⟨T u, by simpa using congrArg (· u) hT⟩
  exact hsurj.denseRange.comp (W1p.denseRange_ofTestFunctionₗ_top hp)
    (W1p.restrictL le_top).continuous

end TauCeti
