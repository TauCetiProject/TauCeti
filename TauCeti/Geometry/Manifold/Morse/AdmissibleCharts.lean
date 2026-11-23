/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.CriticalPoints
public import TauCeti.Geometry.Manifold.Morse.NormalizedChart
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Disjoint Morse charts at a critical level

Passing a critical value `c` of a Morse function `f` attaches one handle at each critical point
on the level `f⁻¹(c)`. Milnor's construction (*Morse Theory*, Theorem 3.2) works in normalized
Morse charts around these points, in which

`f = c - Σ_{i < λ} yᵢ² + Σ_{i ≥ λ} yᵢ²`,

modifies `f` inside the ellipsoid `‖u‖² + 2‖v‖² ≤ 2ε` of each chart, and attaches the cell
`{‖u‖² ≤ ε, v = 0}`; here `u` collects the `λ` negative coordinates and `v` the others. Before any
of this can be done, the charts and the width `ε` have to be chosen compatibly:

* the band `f⁻¹[c - ε, c + ε]` contains no critical points except those on the level `f⁻¹(c)`;
* the charts at the distinct critical points on that level have pairwise disjoint sources;
* the image of every chart contains the closed ball of radius `√(2ε)` about its centre, and hence
  both the ellipsoid and the closed negative-coordinate disc of radius `√ε`.

This file proves that such choices exist when the band `f⁻¹[c - δ, c + δ]` is compact, for every
`0 < δ`. Each condition persists when `ε` decreases. The charts can moreover be placed inside
prescribed neighbourhoods of their centres; the disjoint charts themselves come from
`TauCeti.exists_pairwise_disjoint_normalized_morseCharts`.

A critical point lying in the source of a normal-form chart is on the level `f⁻¹(c)`
(`PartialDiffeomorph.eq_of_mem_criticalPoints_of_mem_source`), so a band whose critical points lie
in such charts has no critical value other than `c`.

## Main results

* `TauCeti.IsMorse.exists_admissible_morseCharts`: the compatible choice of the width `ε` and of
  disjoint normalized Morse charts at all critical points on the level `f⁻¹(c)`.
* `TauCeti.IsMorse.exists_admissible_width`: a bound on the admissible widths shared by finitely
  many compact families of coordinate domains whose joint domains are neighbourhoods of their
  centres.
* `PartialDiffeomorph.eq_of_mem_criticalPoints_of_mem_source`: a critical point in a normal-form
  chart lies on the critical level.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §3, proof of Theorem 3.2 and Remark 3.3.
-/

public section

open Function Set Filter Topology Metric
open scoped ContDiff Manifold

namespace TauCeti

/-- Finitely many compact families of coordinate domains in a compact Morse band admit a common
positive bound `ε₀`. At every width `0 < ε ≤ ε₀` the band is compact, has no critical point
whose value is different from `c`, and every domain contains the closed ball of radius `√(2ε)`.
The joint domains need only contain a neighbourhood of each `(p, 0)`, not be open everywhere. -/
theorem IsMorse.exists_admissible_width {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] {f : M → ℝ} (hf : IsMorse I f) {c δ : ℝ}
    {P : Type*} [TopologicalSpace P] [CompactSpace P] {ι : Type*} [Finite ι]
    {F : Type*} [PseudoMetricSpace F] [Zero F] (U : P → ι → Set F)
    (hnhds : ∀ p i, {q : P × F | q.2 ∈ U q.1 i} ∈ 𝓝 (p, 0))
    (hδ : 0 < δ) (hcompact : IsCompact (f ⁻¹' Icc (c - δ) (c + δ))) :
    ∃ ε₀ ∈ Ioc 0 δ, ∀ ε ∈ Ioc 0 ε₀,
      IsCompact (f ⁻¹' Icc (c - ε) (c + ε)) ∧
      (∀ x, c - ε ≤ f x → f x ≤ c + ε → f x ≠ c → mfderiv I 𝓘(ℝ) f x ≠ 0) ∧
      ∀ p i, closedBall (0 : F) √(2 * ε) ⊆ U p i := by
  -- Compactness turns the joint neighbourhoods into one neighbourhood of zero.
  have htarget : ∀ᶠ z : F in 𝓝 0, ∀ i p, z ∈ U p i := by
    apply eventually_all.2
    intro i
    have hi := isCompact_univ.eventually_forall_of_forall_eventually
      (X := F) (Y := P) (x₀ := 0) (P := fun z p ↦ z ∈ U p i)
      (fun p _ ↦ (continuous_swap.continuousAt (x := ((0 : F), p))).preimage_mem_nhds (hnhds p i))
    simpa only [mem_univ, forall_const] using hi
  obtain ⟨r, hr, hball⟩ := nhds_basis_closedBall.eventually_iff.1 htarget
  obtain ⟨η, hη, hηδ, hcrit⟩ := hf.exists_criticalPoints_inter_preimage_Icc_subset hδ hcompact
  refine ⟨min η (r ^ 2 / 2), ⟨lt_min hη (by positivity), (min_le_left _ _).trans hηδ⟩,
    fun ε hε ↦ ?_⟩
  have hεη : ε ≤ η := hε.2.trans (min_le_left _ _)
  have hεδ : ε ≤ δ := hεη.trans hηδ
  refine ⟨hcompact.of_isClosed_subset (isClosed_Icc.preimage hf.contMDiff.continuous)
    (preimage_mono (Icc_subset_Icc (by linarith [hεδ]) (by linarith [hεδ]))), ?_, ?_⟩
  · intro x hlow hupp hne hderiv
    exact hne (hcrit ⟨mem_criticalPoints_iff_mfderiv_eq_zero.mpr hderiv,
      by constructor <;> linarith⟩)
  · intro p i z hz
    apply hball (closedBall_subset_closedBall (ε₁ := √(2 * ε)) (ε₂ := r) ?_ hz) i p
    rw [Real.sqrt_le_left hr.le]
    linarith [hε.2.trans (min_le_right η (r ^ 2 / 2))]

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] {f : M → ℝ} {x : M}

/-- **Admissible Morse charts at a critical level.** Let `f` be a Morse function on a Hausdorff
manifold whose band `f⁻¹[c - δ, c + δ]` is compact, for some `0 < δ`. Then there are a width
`0 < ε ≤ δ` and normalized Morse charts `ψ p`, indexed by the critical points `p` on the level
`f⁻¹(c)`, such that

* the only critical points in the band `f⁻¹[c - ε, c + ε]` are those on the level `f⁻¹(c)`;
* the chart sources are pairwise disjoint, and each lies in a prescribed neighbourhood `U p`;
* `ψ p p = 0`, and `f = c - Σ_{i < λ} (ψ p)ᵢ² + Σ_{i ≥ λ} (ψ p)ᵢ²` on the source of `ψ p`, where
  `λ` is the Morse index of `f` at `p`;
* the target of each chart contains the closed ball of radius `√(2ε)` about `0`.

The last condition places Milnor's ellipsoid `‖u‖² + 2‖v‖² ≤ 2ε` inside every chart. All of these
conditions persist when `ε` is decreased. -/
theorem IsMorse.exists_admissible_morseCharts [T2Space M] (hf : IsMorse I f) {c δ : ℝ}
    (hδ : 0 < δ) (hcompact : IsCompact (f ⁻¹' Icc (c - δ) (c + δ))) {U : M → Set M}
    (hU : ∀ x ∈ criticalPoints I f ∩ f ⁻¹' {c}, U x ∈ 𝓝 x) :
    ∃ ε, 0 < ε ∧ ε ≤ δ ∧ criticalPoints I f ∩ f ⁻¹' Icc (c - ε) (c + ε) ⊆ f ⁻¹' {c} ∧
      ∃ ψ : ↥(criticalPoints I f ∩ f ⁻¹' {c}) →
          PartialDiffeomorph I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) M
            (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) ∞,
        Pairwise (Disjoint on fun p ↦ (ψ p).source) ∧ ∀ p,
          ↑p ∈ (ψ p).source ∧ (ψ p).source ⊆ U p ∧ ψ p p = 0 ∧
          closedBall 0 √(2 * ε) ⊆ (ψ p).target ∧ ∀ y ∈ (ψ p).source,
            f y = c + ∑ i, (if i.val < manifoldMorseIndex I f p then -1 else 1) * ψ p y i ^ 2 := by
  set S := criticalPoints I f ∩ f ⁻¹' {c}
  have hS : S.Finite := (hf.finite_criticalPoints_inter hcompact).subset
    (inter_subset_inter_right _ (preimage_mono (by simp [hδ.le])))
  have : Finite S := hS.to_subtype
  obtain ⟨ε₁, hε₁, hε₁δ, hband⟩ := hf.exists_criticalPoints_inter_preimage_Icc_subset hδ hcompact
  obtain ⟨ψ, hdisj, hψ⟩ := exists_pairwise_disjoint_normalized_morseCharts hS
    (fun _ _ ↦ Eventually.of_forall fun _ ↦ hf.contMDiff.contMDiffAt)
    (fun x hx ↦ hf.isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints hx.1) hU
  -- The finitely many chart targets are neighbourhoods of `0`, so they share a closed ball.
  have htarget : ∀ᶠ v in 𝓝 0, ∀ p, v ∈ (ψ p).target := eventually_all.2 fun p ↦
    (ψ p).open_target.mem_nhds ((hψ p).2.2.1 ▸ (ψ p).map_source (hψ p).1)
  obtain ⟨r, hr, hrball⟩ := nhds_basis_closedBall.eventually_iff.1 htarget
  refine ⟨min ε₁ (r ^ 2 / 2), lt_min hε₁ (by positivity), (min_le_left _ _).trans hε₁δ,
    fun y ⟨hy, hyε⟩ ↦ hband ⟨hy, Icc_subset_Icc ?_ ?_ hyε⟩, ψ, hdisj, fun p ↦
      ⟨(hψ p).1, (hψ p).2.1, (hψ p).2.2.1, fun v hv ↦ hrball (closedBall_subset_closedBall ?_ hv) p,
        fun y hy ↦ p.property.2 ▸ (hψ p).2.2.2 y hy⟩⟩
  · linarith [min_le_left ε₁ (r ^ 2 / 2)]
  · linarith [min_le_left ε₁ (r ^ 2 / 2)]
  · rw [Real.sqrt_le_left hr.le]
    linarith [min_le_right ε₁ (r ^ 2 / 2)]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] in
/-- **A critical point in a normal-form chart lies on the critical level.** If
`f = c + Σ_{j < k} -yⱼ² + Σ_{j ≥ k} yⱼ²` on the source of a smooth chart `ψ`, then every critical
point of `f` in that source has value `c`. -/
theorem _root_.PartialDiffeomorph.eq_of_mem_criticalPoints_of_mem_source {c : ℝ} {n k : ℕ}
    (ψ : PartialDiffeomorph I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M (EuclideanSpace ℝ (Fin n)) ∞)
    (hf : ∀ y ∈ ψ.source, f y = c + ∑ j, (if j.val < k then -1 else 1) * ψ y j ^ 2)
    (hx : x ∈ ψ.source) (hcrit : x ∈ criticalPoints I f) : f x = c := by
  -- Along the curve `γ t = ψ⁻¹(t • ψ x)` the function is `c + t² (f x - c)`, whose derivative
  -- `2 (f x - c)` at `t = 1` vanishes since `x` is a critical point.
  set φ := ψ.toOpenPartialHomeomorph
  set Q : ℝ := ∑ j, (if j.val < k then -1 else 1) * ψ x j ^ 2
  set γ : ℝ → M := fun t ↦ φ.symm (t • ψ x)
  have hγ1 : γ 1 = x := by simp only [γ, one_smul]; exact φ.left_inv hx
  have ht : ψ x ∈ ψ.target := φ.map_source hx
  -- Near `x`, `f` is a polynomial in the smooth coordinates of `ψ`, so it is differentiable at `x`.
  have hfd : MDifferentiableAt I 𝓘(ℝ) f x := by
    have hq : Differentiable ℝ fun v : EuclideanSpace ℝ (Fin n) ↦
        c + ∑ j, (if j.val < k then -1 else 1) * v j ^ 2 := by
      have hj (j : Fin n) : Differentiable ℝ fun v : EuclideanSpace ℝ (Fin n) ↦ v j :=
        (EuclideanSpace.proj (𝕜 := ℝ) j).differentiable
      fun_prop
    refine ((hq (ψ x)).comp_mdifferentiableAt (((ψ.contMDiffOn_toFun.contMDiffAt
      (ψ.open_source.mem_nhds hx)).mdifferentiableAt (by simp)))).congr_of_eventuallyEq ?_
    filter_upwards [ψ.open_source.mem_nhds hx] with y hy using hf y hy
  -- `f ∘ γ` has derivative `0` at `1`, since `γ 1 = x` is a critical point of `f`.
  have hd : HasFDerivAt (f ∘ γ) (0 : ℝ →L[ℝ] ℝ) 1 := by
    have hγ : MDifferentiableAt 𝓘(ℝ) I γ 1 :=
      ((ψ.contMDiffOn_invFun.contMDiffAt
        (ψ.open_target.mem_nhds (by simpa using ht))).mdifferentiableAt (by simp)).comp 1
          (mdifferentiableAt_iff_differentiableAt.2 (differentiableAt_id.smul_const _))
    have h0 : mfderiv I 𝓘(ℝ) f (γ 1) = 0 := by
      rw [hγ1]
      exact mem_criticalPoints_iff_mfderiv_eq_zero.1 hcrit
    have h := (hγ1 ▸ hfd).hasMFDerivAt.comp 1 hγ.hasMFDerivAt
    rwa [h0, ContinuousLinearMap.zero_comp, hasMFDerivAt_iff_hasFDerivAt] at h
  -- Explicitly, `f (γ t) = c + t² Q` near `t = 1`.
  have heq : f ∘ γ =ᶠ[𝓝 1] fun t ↦ c + t ^ 2 * Q := by
    filter_upwards [(continuous_id.smul continuous_const).continuousAt.preimage_mem_nhds
      (ψ.open_target.mem_nhds (by simpa using ht))] with t htt
    have hmem : γ t ∈ ψ.source := φ.map_target htt
    have hγt : ψ (γ t) = t • ψ x := φ.right_inv htt
    rw [Function.comp_apply, hf _ hmem, hγt, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp only [PiLp.smul_apply, smul_eq_mul]
    ring
  have hg := ((hasDerivAt_pow 2 (1 : ℝ)).mul_const Q).const_add c
  have hval := (hg.congr_of_eventuallyEq heq).unique (by simpa using hd.hasDerivAt)
  have hQ : Q = 0 := by simpa using hval
  rw [hf x hx]
  exact add_eq_left.2 hQ

end TauCeti
