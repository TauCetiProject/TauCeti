/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Analysis.Calculus.Morse.ChartRescaling
public import TauCeti.Analysis.InnerProductSpace.Indefinite
public import TauCeti.Analysis.InnerProductSpace.Polar.Det
public import TauCeti.Analysis.Normed.Module.NegativeSubspace
public import TauCeti.Topology.Algebra.OrthogonalGroup
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv

/-!
# Transitions between split Morse charts

Two partial diffeomorphisms centred at the same point and expressing the same function as
`f(x) - ‖u‖² + ‖v‖²` have a transition whose derivative at zero preserves that quadratic form.
Its negative-to-negative block is therefore invertible in finite dimension. This supplies the
linear map to which one applies polar decomposition when comparing the negative disks of
different Morse charts. No assertion about overlap of the whole negative disks is needed:
the coordinate equations are used only on an open neighbourhood of their common centre.

With `h` the polar factor of that block, the small negative disk `u ↦ ψ₁⁻¹(u, 0)` of the second
chart is homotopic to the disk `u ↦ ψ₀⁻¹(h u, 0)` of the first chart, by a homotopy along which
`f` stays at or below `f(x) - ‖u‖²` over each point `u`
(`PartialDiffeomorph.exists_negative_disk_homotopy_polarFactor`). In particular the boundary
sphere of radius `δ` stays in the sublevel `{f ≤ f(x) - δ²}` throughout. This is the comparison
of characteristic maps of Morse cells near the critical point, before the outer annuli of the
cells are taken into account.

The product target can be obtained from normalized Euclidean Morse coordinates by splitting
negative and positive coordinates with `EuclideanSpace.sumComplEquivProd`.

Read in the coordinates of the first chart, the negative space `E × 0` of the second chart is
carried by this derivative `A` strictly inside the negative cone `‖v‖ < ‖u‖`, so it is a maximal
negative subspace: the graph of a unique operator `E → F` of norm less than one. Its orientation,
given by the frame `A ∘ inl`, can therefore be transported through the space of negative
subspaces to the negative space `E × 0` of the first chart, and compared with that chart's own
orientation. The result is read off from the polar factor `h = A_uu (A_uuᵀ A_uu)^{-1/2}` of the
negative block `A_uu`, the orthogonal map comparing the negative discs of the two charts: the
orientations agree exactly when `det h = 1`
(`PartialDiffeomorph.det_polarFactor_fst_fderiv_transition_inl_eq_one_iff`).

For three charts the polar factors are not multiplicative, `h₀₂ ≠ h₀₁ h₁₂` in general, since the
negative block of the composite transition also involves the off-diagonal blocks. Their
determinants are: orientation transport through negative subspaces is multiplicative
(`ContinuousLinearMap.sign_det_fst_comp_comp_of_norm_snd_lt`), so
`det h₀₂ = det h₀₁ * det h₁₂`
(`PartialDiffeomorph.det_polarFactor_fst_fderiv_transition_inl_eq_mul`). Hence, for Euclidean
negative coordinates, `h₀₁ h₁₂` and `h₀₂` lie in the same component of the orthogonal group and are
joined by a path of orthogonal maps
(`PartialDiffeomorph.exists_path_linearIsometryEquiv_of_polarFactor_transition`).

## Main results

* `PartialDiffeomorph.norm_sq_sub_fderiv_transition`: the derivative of the transition preserves
  `‖u‖² - ‖v‖²`.
* `PartialDiffeomorph.isInvertible_fst_fderiv_transition_inl`: its negative block is invertible.
* `PartialDiffeomorph.existsUnique_range_fderiv_transition_inl_eq_graph`: the negative space of
  the second chart is the graph of a unique strict contraction in the coordinates of the first.
* `PartialDiffeomorph.det_polarFactor_fst_fderiv_transition_inl_eq_one_iff`: the polar factor of
  the negative block has determinant one exactly when the charts induce the same orientation on
  their negative spaces, compared through the space of negative subspaces.
* `PartialDiffeomorph.det_polarFactor_fst_fderiv_transition_inl_eq_mul`: for three charts,
  `det h₀₂ = det h₀₁ * det h₁₂`.
* `PartialDiffeomorph.exists_path_linearIsometryEquiv_of_polarFactor_transition`: for three charts
  with Euclidean negative coordinates, `h₀₁ h₁₂` is joined to `h₀₂` by a path of orthogonal maps.
* `PartialDiffeomorph.exists_negative_disk_homotopy_polarFactor`: the small negative disk
  `u ↦ ψ₁⁻¹(u, 0)` is homotopic to `u ↦ ψ₀⁻¹(h u, 0)`, staying in a given neighbourhood of `x`
  with `f ≤ f(x) - ‖u‖²` over each point `u`.

## References

* J. Milnor, *Morse Theory*, Princeton University Press, 1963, §§2–3.
-/

public section

open Filter Set Topology
open scoped ContDiff Manifold

namespace PartialDiffeomorph

section SplitChart

variable {V H M E F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [TopologicalSpace H]
  {I : ModelWithCorners ℝ V H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {n : ℕ∞ω} (ψ₀ ψ₁ : PartialDiffeomorph I 𝓘(ℝ, E × F) M (E × F) n) (hn : 1 ≤ n)
  {f : M → ℝ} {x : M}
  (hx₀ : x ∈ ψ₀.source) (hx₁ : x ∈ ψ₁.source) (hψ₀ : ψ₀ x = 0) (hψ₁ : ψ₁ x = 0)
  (hf₀ : ∀ y ∈ ψ₀.source, f y = f x - ‖(ψ₀ y).1‖ ^ 2 + ‖(ψ₀ y).2‖ ^ 2)
  (hf₁ : ∀ y ∈ ψ₁.source, f y = f x - ‖(ψ₁ y).1‖ ^ 2 + ‖(ψ₁ y).2‖ ^ 2)

include hn hx₀ hx₁ hψ₀ hψ₁ hf₀ hf₁

private theorem split_transition_data :
    DifferentiableAt ℝ (fun z ↦ ψ₀ (ψ₁.symm z)) 0 ∧ ψ₀ (ψ₁.symm 0) = 0 ∧
      ∀ᶠ z in 𝓝 0,
        ‖(ψ₀ (ψ₁.symm z)).1‖ ^ 2 - ‖(ψ₀ (ψ₁.symm z)).2‖ ^ 2 =
          ‖z.1‖ ^ 2 - ‖z.2‖ ^ 2 := by
  have htarget : (0 : E × F) ∈ ψ₁.target := hψ₁ ▸ ψ₁.map_source hx₁
  have hinv : ψ₁.symm 0 = x := by
    rw [← hψ₁]
    exact ψ₁.left_inv hx₁
  have hn' : n ≠ 0 := (zero_lt_one.trans_le hn).ne'
  have hdiff := ψ₀.differentiableAt_comp_symm ψ₁ hn' hx₀ hx₁
  rw [hψ₁] at hdiff
  refine ⟨hdiff, hinv ▸ hψ₀, ?_⟩
  have hsource : ∀ᶠ z in 𝓝 0, ψ₁.symm z ∈ ψ₀.source :=
    (ψ₁.symm.mdifferentiableAt hn' htarget).continuousAt.preimage_mem_nhds
      (hinv ▸ ψ₀.open_source.mem_nhds hx₀)
  filter_upwards [hsource, ψ₁.open_target.mem_nhds htarget] with z hz₀ hz₁
  have h₀ := hf₀ _ hz₀
  have h₁ := hf₁ _ (ψ₁.map_target hz₁)
  rw [ψ₁.right_inv hz₁] at h₁
  simp only [PartialDiffeomorph.symm_toPartialEquiv] at h₀ ⊢
  linarith

/-- The derivative of a transition between two split Morse charts preserves the signed
sum of squared norms. Only a neighbourhood of the common centre is used. -/
theorem norm_sq_sub_fderiv_transition (z : E × F) :
    ‖(fderiv ℝ (fun w ↦ ψ₀ (ψ₁.symm w)) 0 z).1‖ ^ 2 -
        ‖(fderiv ℝ (fun w ↦ ψ₀ (ψ₁.symm w)) 0 z).2‖ ^ 2 =
      ‖z.1‖ ^ 2 - ‖z.2‖ ^ 2 := by
  obtain ⟨hreg, hzero, hQ⟩ := ψ₀.split_transition_data ψ₁ hn hx₀ hx₁ hψ₀ hψ₁ hf₀ hf₁
  exact hreg.norm_sq_sub_fderiv hzero hQ z

/-- The negative-to-negative block of the derivative of a transition between split Morse
charts is invertible. No finite-dimensionality assumption on the positive factor is needed. -/
theorem isInvertible_fst_fderiv_transition_inl [FiniteDimensional ℝ E] :
    ((ContinuousLinearMap.fst ℝ E F).comp
      ((fderiv ℝ (fun w ↦ ψ₀ (ψ₁.symm w)) 0).comp
        (ContinuousLinearMap.inl ℝ E F))).IsInvertible := by
  obtain ⟨hreg, hzero, hQ⟩ := ψ₀.split_transition_data ψ₁ hn hx₀ hx₁ hψ₀ hψ₁ hf₀ hf₁
  exact hreg.isInvertible_fst_fderiv_inl hzero hQ

/-- **The small negative disks of two split Morse charts are homotopic** (Milnor, *Morse
Theory*, §3). Let `h` be the polar factor of the negative-to-negative block of the derivative at
`0` of the transition `ψ₀ ∘ ψ₁⁻¹`. For every neighbourhood `W` of the common centre `x` there are
`δ > 0` and a homotopy `G` from the negative disk `u ↦ ψ₁⁻¹(u, 0)`, `‖u‖ ≤ δ`, of `ψ₁` to the
disk `u ↦ ψ₀⁻¹(h u, 0)` of `ψ₀`, staying in `W`, with `f (G (t, u)) ≤ f x - ‖u‖²` throughout.
In particular the boundary sphere `‖u‖ = δ` stays in the sublevel `{f ≤ f x - δ²}`. -/
theorem exists_negative_disk_homotopy_polarFactor [CompleteSpace E] {W : Set M} (hW : W ∈ 𝓝 x) :
    ∃ δ > 0, ∃ G : C(unitInterval × Metric.closedBall (0 : E) δ, M),
      (∀ u, G (0, u) = ψ₁.symm ((u : E), 0)) ∧
      (∀ u, G (1, u) = ψ₀.symm (((ContinuousLinearMap.fst ℝ E F).comp
        ((fderiv ℝ (fun w ↦ ψ₀ (ψ₁.symm w)) 0).comp
          (ContinuousLinearMap.inl ℝ E F))).polarFactor u, 0)) ∧
      ∀ p, G p ∈ W ∧ f (G p) ≤ f x - ‖(p.2 : E)‖ ^ 2 := by
  obtain ⟨hreg, hzero, hQ⟩ := ψ₀.split_transition_data ψ₁ hn hx₀ hx₁ hψ₀ hψ₁ hf₀ hf₁
  have htarget₀ : (0 : E × F) ∈ ψ₀.target := hψ₀ ▸ ψ₀.map_source hx₀
  have htarget₁ : (0 : E × F) ∈ ψ₁.target := hψ₁ ▸ ψ₁.map_source hx₁
  have hinv₀ : ψ₀.toPartialEquiv.symm 0 = x := hψ₀ ▸ ψ₀.left_inv hx₀
  have hinv₁ : ψ₁.toPartialEquiv.symm 0 = x := hψ₁ ▸ ψ₁.left_inv hx₁
  have hcont₀ := ψ₀.contMDiffOn.continuousOn
  have hcont₀' := ψ₀.symm.contMDiffOn.continuousOn
  have hcont₁' := ψ₁.symm.contMDiffOn.continuousOn
  -- Near `0` the transition is defined and continuous.
  set U := ψ₁.target ∩ ψ₁.symm ⁻¹' ψ₀.source
  have hU : U ∈ 𝓝 0 := (hcont₁'.isOpen_inter_preimage ψ₁.open_target ψ₀.open_source).mem_nhds
    ⟨htarget₁, by simpa [hinv₁] using hx₀⟩
  have hc : ∀ᶠ z in 𝓝 0, ContinuousAt (fun w ↦ ψ₀ (ψ₁.symm w)) z := by
    filter_upwards [ψ₁.open_target.mem_nhds htarget₁, hU] with z hz hzU
    exact (hcont₀.continuousAt (ψ₀.open_source.mem_nhds hzU.2)).comp
      (hcont₁'.continuousAt (ψ₁.open_target.mem_nhds hz))
  -- Chart coordinates of points of `W` near `0`.
  set V := ψ₀.target ∩ ψ₀.symm ⁻¹' W
  have hV : V ∈ 𝓝 0 := inter_mem (ψ₀.open_target.mem_nhds htarget₀)
    ((hcont₀'.continuousAt (ψ₀.open_target.mem_nhds htarget₀)).preimage_mem_nhds
      (by rwa [PartialDiffeomorph.symm_toPartialEquiv, hinv₀]))
  obtain ⟨δ, hδ, hδU, H, hH₀, hH₁, hH⟩ :=
    hreg.hasFDerivAt.exists_negative_disk_homotopy_polarFactor hzero hc hQ hU hV
  refine ⟨δ, hδ, ⟨fun p ↦ ψ₀.symm (H p), hcont₀'.comp_continuous H.continuous
    fun p ↦ (hH p).1.1⟩, fun u ↦ ?_, fun u ↦ ?_, fun p ↦ ⟨(hH p).1.2, ?_⟩⟩
  · have hu : ((u : E), (0 : F)) ∈ U := hδU <|
      (closedBall_prod_same (0 : E) (0 : F) δ).subset ⟨u.2, Metric.mem_closedBall_self hδ.le⟩
    simp only [ContinuousMap.coe_mk, hH₀]
    exact ψ₀.left_inv hu.2
  · simp only [ContinuousMap.coe_mk, hH₁]
  · have h := hf₀ _ (ψ₀.map_target (hH p).1.1)
    rw [ψ₀.right_inv (hH p).1.1] at h
    simp only [ContinuousMap.coe_mk, PartialDiffeomorph.symm_toPartialEquiv] at h ⊢
    linarith [(hH p).2]

/-- The derivative of a transition between split Morse charts carries the negative space
`E × 0` of the second chart strictly inside the negative cone `‖v‖ < ‖u‖` of the first. -/
theorem norm_snd_fderiv_transition_lt {u : E} (hu : u ≠ 0) :
    ‖(fderiv ℝ (fun w ↦ ψ₀ (ψ₁.symm w)) 0 (u, 0)).2‖ <
      ‖(fderiv ℝ (fun w ↦ ψ₀ (ψ₁.symm w)) 0 (u, 0)).1‖ := by
  have hL (v : E) :
      ‖((fderiv ℝ (fun w ↦ ψ₀ (ψ₁.symm w)) 0).comp (ContinuousLinearMap.inl ℝ E F) v).1‖ ^ 2 -
        ‖((fderiv ℝ (fun w ↦ ψ₀ (ψ₁.symm w)) 0).comp (ContinuousLinearMap.inl ℝ E F) v).2‖ ^ 2 =
          ‖v‖ ^ 2 := by
    simpa using ψ₀.norm_sq_sub_fderiv_transition ψ₁ hn hx₀ hx₁ hψ₀ hψ₁ hf₀ hf₁ (v, 0)
  simpa using ContinuousLinearMap.norm_snd_lt_norm_fst_of_norm_sq_sub _ hL hu

/-- **The negative space of one Morse chart in the coordinates of another.** The derivative of
the transition carries the negative space `E × 0` of the second chart onto the graph of a unique
operator `E →L[ℝ] F` of norm less than one: a maximal negative subspace for the first chart. -/
theorem existsUnique_range_fderiv_transition_inl_eq_graph [FiniteDimensional ℝ E] :
    ∃! A : E →L[ℝ] F, ‖A‖ < 1 ∧
      LinearMap.range ((fderiv ℝ (fun w ↦ ψ₀ (ψ₁.symm w)) 0).comp
        (ContinuousLinearMap.inl ℝ E F) : E →ₗ[ℝ] E × F) = A.toLinearMap.graph := by
  set L := (fderiv ℝ (fun w ↦ ψ₀ (ψ₁.symm w)) 0).comp (ContinuousLinearMap.inl ℝ E F)
  have hneg (u : E) (hu : u ≠ 0) : ‖(L u).2‖ < ‖(L u).1‖ := by
    simpa [L] using ψ₀.norm_snd_fderiv_transition_lt ψ₁ hn hx₀ hx₁ hψ₀ hψ₁ hf₀ hf₁ hu
  refine (Submodule.existsUnique_eq_graph_iff_finrank_eq_and_isSplitNegative _).2
    ⟨?_, L.isSplitNegative_range_of_norm_snd_lt hneg⟩
  refine LinearMap.finrank_range_of_inj fun u v huv ↦ L.injective_fst_comp_of_norm_snd_lt hneg ?_
  simpa using congrArg Prod.fst huv

/-- **Orientation comparison of Morse charts.** Let `h` be the polar factor of the negative block
`A_uu = fst ∘ A ∘ inl` of the derivative `A` of the transition between two split Morse charts:
the orthogonal map `A_uu (A_uuᵀ A_uu)^{-1/2}` comparing their negative discs. The second chart
orients its negative space by the frame `A ∘ inl`. Then `det h = 1` exactly when this frame can
be moved, through frames whose nonzero values stay in the negative cone, to a frame `inl ∘ B` of
the negative space `E × 0` of the first chart with `det B > 0`: the two charts induce the same
orientation on their negative spaces. The sign of `det B` does not depend on the chosen family
(`ContinuousLinearMap.det_fst_comp_pos_iff_of_norm_snd_lt`); the straight-line contraction of
graph coordinates gives one, with `B = A_uu`. -/
theorem det_polarFactor_fst_fderiv_transition_inl_eq_one_iff [FiniteDimensional ℝ E] :
    ((ContinuousLinearMap.fst ℝ E F).comp ((fderiv ℝ (fun w ↦ ψ₀ (ψ₁.symm w)) 0).comp
      (ContinuousLinearMap.inl ℝ E F))).polarFactor.det = 1 ↔
      ∃ (L : C(unitInterval, E →L[ℝ] E × F)) (B : E →L[ℝ] E),
        L 0 = (fderiv ℝ (fun w ↦ ψ₀ (ψ₁.symm w)) 0).comp (ContinuousLinearMap.inl ℝ E F) ∧
        L 1 = (ContinuousLinearMap.inl ℝ E F).comp B ∧
        (∀ t u, u ≠ 0 → ‖(L t u).2‖ < ‖(L t u).1‖) ∧ 0 < B.det := by
  set L₀ := (fderiv ℝ (fun w ↦ ψ₀ (ψ₁.symm w)) 0).comp (ContinuousLinearMap.inl ℝ E F)
  have hneg (u : E) (hu : u ≠ 0) : ‖(L₀ u).2‖ < ‖(L₀ u).1‖ := by
    simpa [L₀] using ψ₀.norm_snd_fderiv_transition_lt ψ₁ hn hx₀ hx₁ hψ₀ hψ₁ hf₀ hf₁ hu
  rw [ContinuousLinearMap.det_polarFactor_eq_one_iff,
    L₀.det_fst_comp_pos_iff_exists_path_of_norm_snd_lt hneg]

variable (ψ₂ : PartialDiffeomorph I 𝓘(ℝ, E × F) M (E × F) n) (hx₂ : x ∈ ψ₂.source)
  (hψ₂ : ψ₂ x = 0) (hf₂ : ∀ y ∈ ψ₂.source, f y = f x - ‖(ψ₂ y).1‖ ^ 2 + ‖(ψ₂ y).2‖ ^ 2)

include hx₂ hψ₂ hf₂

/-- **Orientation comparisons of three Morse charts multiply.** For split Morse charts `ψ₀`,
`ψ₁`, `ψ₂` centred at the same point, write `h_ij` for the polar factor of the negative block of
the derivative at the origin of the transition `ψ_i ∘ ψ_j⁻¹`. Then
`det h₀₂ = det h₀₁ * det h₁₂`. The polar factors themselves need not satisfy `h₀₂ = h₀₁ h₁₂`. -/
theorem det_polarFactor_fst_fderiv_transition_inl_eq_mul [FiniteDimensional ℝ E] :
    ((ContinuousLinearMap.fst ℝ E F).comp ((fderiv ℝ (fun w ↦ ψ₀ (ψ₂.symm w)) 0).comp
      (ContinuousLinearMap.inl ℝ E F))).polarFactor.det =
      ((ContinuousLinearMap.fst ℝ E F).comp ((fderiv ℝ (fun w ↦ ψ₀ (ψ₁.symm w)) 0).comp
        (ContinuousLinearMap.inl ℝ E F))).polarFactor.det *
      ((ContinuousLinearMap.fst ℝ E F).comp ((fderiv ℝ (fun w ↦ ψ₁ (ψ₂.symm w)) 0).comp
        (ContinuousLinearMap.inl ℝ E F))).polarFactor.det := by
  set A₀₁ := fderiv ℝ (fun w ↦ ψ₀ (ψ₁.symm w)) 0
  set A₁₂ := fderiv ℝ (fun w ↦ ψ₁ (ψ₂.symm w)) 0
  -- The derivative of `ψ₀ ∘ ψ₂⁻¹` is `A₀₁ ∘ A₁₂`, by the chain rule.
  have hA : fderiv ℝ (fun w ↦ ψ₀ (ψ₂.symm w)) 0 = A₀₁.comp A₁₂ := by
    have h := ψ₀.fderiv_comp_symm_eq_comp ψ₁ ψ₂ (zero_lt_one.trans_le hn).ne' hx₀ hx₁ hx₂
    rwa [hψ₁, hψ₂] at h
  -- `A₀₁` preserves `‖u‖² - ‖v‖²`, so it maps the negative cone into itself.
  have hcone (z : E × F) (hz : ‖z.2‖ < ‖z.1‖) : ‖(A₀₁ z).2‖ < ‖(A₀₁ z).1‖ := by
    have hQ := ψ₀.norm_sq_sub_fderiv_transition ψ₁ hn hx₀ hx₁ hψ₀ hψ₁ hf₀ hf₁ z
    have hz2 : ‖z.2‖ ^ 2 < ‖z.1‖ ^ 2 := pow_lt_pow_left₀ hz (norm_nonneg _) two_ne_zero
    exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) (by linarith)
  have hneg (u : E) (hu : u ≠ 0) :
      ‖(A₁₂.comp (ContinuousLinearMap.inl ℝ E F) u).2‖ <
        ‖(A₁₂.comp (ContinuousLinearMap.inl ℝ E F) u).1‖ := by
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]
    exact ψ₁.norm_snd_fderiv_transition_lt ψ₂ hn hx₁ hx₂ hψ₁ hψ₂ hf₁ hf₂ hu
  rw [hA, ContinuousLinearMap.comp_assoc, ContinuousLinearMap.det_polarFactor_eq_sign,
    ContinuousLinearMap.det_polarFactor_eq_sign, ContinuousLinearMap.det_polarFactor_eq_sign,
    ContinuousLinearMap.sign_det_fst_comp_comp_of_norm_snd_lt A₀₁ hcone _ hneg, SignType.coe_mul]

end SplitChart

section EuclideanNegative

variable {V H M F ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [TopologicalSpace H]
  {I : ModelWithCorners ℝ V H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [Fintype ι] {n : ℕ∞ω}
  {f : M → ℝ} {x : M}

/-- **The polar factors of three Morse charts agree up to a path.** Let `ψ₀`, `ψ₁`, `ψ₂` be split
Morse charts centred at the same point, with Euclidean negative coordinates, and let `h_ij` be
the polar factor of the negative block of the derivative at the origin of the transition
`ψ_i ∘ ψ_j⁻¹`, a linear isometry. Then `h₀₁ ∘ h₁₂` and `h₀₂` are joined by a path of linear
isometries, continuous in the operator-norm topology, although they need not be equal. -/
theorem exists_path_linearIsometryEquiv_of_polarFactor_transition
    (ψ₀ ψ₁ ψ₂ : PartialDiffeomorph I 𝓘(ℝ, EuclideanSpace ℝ ι × F) M (EuclideanSpace ℝ ι × F) n)
    (hn : 1 ≤ n) (hx₀ : x ∈ ψ₀.source) (hx₁ : x ∈ ψ₁.source) (hx₂ : x ∈ ψ₂.source)
    (hψ₀ : ψ₀ x = 0) (hψ₁ : ψ₁ x = 0) (hψ₂ : ψ₂ x = 0)
    (hf₀ : ∀ y ∈ ψ₀.source, f y = f x - ‖(ψ₀ y).1‖ ^ 2 + ‖(ψ₀ y).2‖ ^ 2)
    (hf₁ : ∀ y ∈ ψ₁.source, f y = f x - ‖(ψ₁ y).1‖ ^ 2 + ‖(ψ₁ y).2‖ ^ 2)
    (hf₂ : ∀ y ∈ ψ₂.source, f y = f x - ‖(ψ₂ y).1‖ ^ 2 + ‖(ψ₂ y).2‖ ^ 2)
    {h₀₁ h₁₂ h₀₂ : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι}
    (hh₀₁ : ⇑h₀₁ = ((ContinuousLinearMap.fst ℝ _ F).comp
      ((fderiv ℝ (fun w ↦ ψ₀ (ψ₁.symm w)) 0).comp (ContinuousLinearMap.inl ℝ _ F))).polarFactor)
    (hh₁₂ : ⇑h₁₂ = ((ContinuousLinearMap.fst ℝ _ F).comp
      ((fderiv ℝ (fun w ↦ ψ₁ (ψ₂.symm w)) 0).comp (ContinuousLinearMap.inl ℝ _ F))).polarFactor)
    (hh₀₂ : ⇑h₀₂ = ((ContinuousLinearMap.fst ℝ _ F).comp
      ((fderiv ℝ (fun w ↦ ψ₀ (ψ₂.symm w)) 0).comp (ContinuousLinearMap.inl ℝ _ F))).polarFactor) :
    ∃ γ : unitInterval → (EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι),
      Continuous (fun t ↦ ((γ t).toContinuousLinearEquiv :
        EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)) ∧
      γ 0 = h₁₂.trans h₀₁ ∧ γ 1 = h₀₂ := by
  have hdet (h : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι)
      (T : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) (hT : ⇑h = ⇑T) :
      LinearMap.det h.toLinearMap = T.det :=
    congrArg LinearMap.det (LinearMap.ext (congrFun hT))
  refine TauCeti.exists_path_linearIsometryEquiv_of_det_eq ?_
  rw [hdet h₀₂ _ hh₀₂, det_polarFactor_fst_fderiv_transition_inl_eq_mul ψ₀ ψ₁ hn hx₀ hx₁ hψ₀ hψ₁
    hf₀ hf₁ ψ₂ hx₂ hψ₂ hf₂, ← hdet h₀₁ _ hh₀₁, ← hdet h₁₂ _ hh₁₂, ← LinearMap.det_comp]
  exact congrArg LinearMap.det (LinearMap.ext fun v ↦ h₁₂.trans_apply h₀₁ v)

end EuclideanNegative

end PartialDiffeomorph
