/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Analysis.InnerProductSpace.Indefinite
public import TauCeti.Analysis.InnerProductSpace.Polar.Det
public import TauCeti.Analysis.Normed.Module.NegativeSubspace

/-!
# The derivative of a transition between split Morse charts

Two partial diffeomorphisms centred at the same point and expressing the same function as
`f(x) - ‖u‖² + ‖v‖²` have a transition whose derivative at zero preserves that quadratic form.
Its negative-to-negative block is therefore invertible in finite dimension. This supplies the
linear map to which one applies polar decomposition when comparing the negative disks of
different Morse charts. No assertion about overlap of the whole negative disks is needed:
the coordinate equations are used only on an open neighbourhood of their common centre.

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

## Main results

* `PartialDiffeomorph.norm_sq_sub_fderiv_transition`: the derivative of the transition preserves
  `‖u‖² - ‖v‖²`.
* `PartialDiffeomorph.isInvertible_fst_fderiv_transition_inl`: its negative block is invertible.
* `PartialDiffeomorph.existsUnique_range_fderiv_transition_inl_eq_graph`: the negative space of
  the second chart is the graph of a unique strict contraction in the coordinates of the first.
* `PartialDiffeomorph.det_polarFactor_fst_fderiv_transition_inl_eq_one_iff`: the polar factor of
  the negative block has determinant one exactly when the charts induce the same orientation on
  their negative spaces, compared through the space of negative subspaces.

## References

* J. Milnor, *Morse Theory*, Princeton University Press, 1963, §§2–3.
-/

public section

open Filter Set Topology
open scoped ContDiff Manifold

namespace PartialDiffeomorph

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
  have hreg₀ := (ψ₀.contMDiffOn.contMDiffAt (ψ₀.open_source.mem_nhds hx₀)).of_le hn
  have hreg₁ := (ψ₁.symm.contMDiffOn.contMDiffAt (ψ₁.open_target.mem_nhds htarget)).of_le hn
  have hreg : ContMDiffAt 𝓘(ℝ, E × F) 𝓘(ℝ, E × F) 1
      (fun z ↦ ψ₀ (ψ₁.symm z)) 0 :=
    hreg₀.comp_of_eq hreg₁ hinv
  refine ⟨(contMDiffAt_iff_contDiffAt.mp hreg).differentiableAt one_ne_zero, hinv ▸ hψ₀, ?_⟩
  have hsource : ∀ᶠ z in 𝓝 0, ψ₁.symm z ∈ ψ₀.source :=
    hreg₁.continuousAt.preimage_mem_nhds (hinv ▸ ψ₀.open_source.mem_nhds hx₀)
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
  refine (Submodule.existsUnique_eq_graph_iff_finrank_eq_and_norm_snd_lt _).2 ⟨?_, ?_⟩
  · refine LinearMap.finrank_range_of_inj fun u v huv ↦ L.injective_fst_comp_of_norm_snd_lt hneg ?_
    simpa using congrArg Prod.fst huv
  · rintro z ⟨u, rfl⟩ hz
    exact hneg u fun hu ↦ hz (by simp [hu])

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
  rw [ContinuousLinearMap.det_polarFactor_eq_one_iff (L₀.injective_fst_comp_of_norm_snd_lt hneg)]
  constructor
  · intro hdet
    refine ⟨⟨fun t ↦ L₀.negativeContraction (1 - t), by fun_prop⟩,
      (ContinuousLinearMap.fst ℝ E F).comp L₀, by simp, by simp, fun t u hu ↦ ?_, hdet⟩
    refine L₀.norm_snd_negativeContraction_lt hneg ?_ hu
    rw [abs_le]
    constructor <;> linarith [t.2.1, t.2.2]
  · rintro ⟨L, B, h₀, h₁, hL, hB⟩
    rwa [← h₀, ContinuousLinearMap.det_fst_comp_pos_iff_of_norm_snd_lt L.continuous hL 0 1, h₁,
      ← ContinuousLinearMap.comp_assoc, ContinuousLinearMap.fst_comp_inl,
      ContinuousLinearMap.id_comp]

end PartialDiffeomorph
