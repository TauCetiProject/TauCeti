/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Stable.Manifold
public import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import TauCeti.Analysis.SpecialFunctions.Log.ExpNegLogOneAdd
import TauCeti.Geometry.Manifold.Immersion.Basic
import TauCeti.Geometry.Manifold.MFDeriv.ModelChart

/-!
# Stable and unstable manifolds as smoothly embedded vector spaces

Let `f` be a Morse function on a compact boundaryless manifold `M` of dimension `n`, `X` a
pseudo-gradient field adapted to `f`, and `x` a critical point of index `k`. The stable manifold
`W^s(x)` is the image of a smooth embedding of a real vector space of dimension `n - k`, sending `0`
to `x`, and the unstable manifold `W^u(x)` is the image of a smooth embedding of a real vector space
of dimension `k`.

The parametrization is read off the flow `Φ` of `X`. In a Morse chart `φ` at `x` in which `X` is
linear, the flow contracts the stable subspace `L` of the chart: for small `w ∈ L` and `t ≥ 0` it
moves `φ⁻¹ w` to `φ⁻¹ (e^{-t} w)`. The parametrization sends `v ∈ L` to `Φ_{-T} (φ⁻¹ (e^{-T} v))`
for any time `T` that makes `e^{-T} v` small; by the contraction, the result does not depend on
`T`. Near `0` it is `φ⁻¹` restricted to `L`, so it is an immersion there, and it intertwines the
scaling `v ↦ e^{-s} v` of `L` with the time-`s` map of the flow, so it is an immersion everywhere.
It covers `W^s(x)` because every point of `W^s(x)` reaches the small cube of the chart where
`W^s(x)` is `L`.

## Main declarations

* `TauCeti.IsAdaptedPseudoGradient.stableParam`: the parametrization of `W^s(x)` by the stable
  subspace of a Morse chart.
* `TauCeti.IsAdaptedPseudoGradient.stableParam_smul`: it intertwines the scaling of the stable
  subspace with the flow.
* `TauCeti.IsAdaptedPseudoGradient.mfderiv_toChart_comp_stableParam_zero`: read in the chart, its
  derivative at `0` is the inclusion of the stable subspace, so the tangent space of `W^s(x)` at `x`
  is the stable subspace of the chart.
* `TauCeti.IsAdaptedPseudoGradient.isSmoothEmbedding_stableParam` and
  `TauCeti.IsAdaptedPseudoGradient.range_stableParam`: it is a smooth embedding with image
  `W^s(x)`.
* `TauCeti.IsAdaptedPseudoGradient.exists_stableParam`: a Morse chart and a scale for which the
  parametrization is a smooth embedding onto `W^s(x)` with the expected derivative at `0`.
* `TauCeti.IsAdaptedPseudoGradient.exists_isSmoothEmbedding_stableSet` and
  `TauCeti.IsAdaptedPseudoGradient.exists_isSmoothEmbedding_unstableSet`: `W^s(x)` and `W^u(x)` are
  images of smooth embeddings of vector spaces of dimensions `n - k` and `k`.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Section 2.1.
-/

public section

open Filter Function Manifold Metric Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {x : M} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

namespace MorseChart

variable (φ : MorseChart E f x)

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M] in
/-- The time `log (1 + ‖v‖ / δ)` used by the parametrization of the stable manifold brings `v`
into the ball of radius `δ`, in norm form. -/
theorem norm_exp_neg_log_smul_lt {δ : ℝ} (hδ : 0 < δ) (v : φ.stableSubspace) :
    ‖Real.exp (-Real.log (1 + ‖v‖ / δ)) • v‖ < δ := by
  rw [norm_smul_of_nonneg (Real.exp_pos _).le]
  exact Real.exp_neg_log_one_add_div_mul_lt hδ (norm_nonneg v)

omit [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M] in
/-- The small cube of a Morse chart, where the coordinates and the chart value are small, is
open. -/
theorem isOpen_smallCube (ε δ : ℝ) :
    IsOpen (φ.toChart.source ∩ φ.toChart ⁻¹' {w : E | ‖φ.coord w‖ < ε ∧ ‖w‖ < δ}) :=
  φ.toChart.continuousOn.isOpen_inter_preimage φ.toChart.open_source
    ((isOpen_lt (continuous_norm.comp (φ.coordL.continuous.congr φ.coordL_apply))
      continuous_const).inter (isOpen_lt continuous_norm continuous_const))

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M] in
/-- The centre of a Morse chart lies in each of its small cubes. -/
theorem mem_smallCube {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    x ∈ φ.toChart.source ∩ φ.toChart ⁻¹' {w : E | ‖φ.coord w‖ < ε ∧ ‖w‖ < δ} :=
  ⟨φ.mem_source, by simpa using ⟨hε, hδ⟩⟩

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M] in
/-- Small vectors of the stable subspace are coordinates of points of the chart. -/
theorem coe_mem_target_of_norm_lt {r δ : ℝ}
    (hrT : ∀ z, ‖z‖ < r → φ.coord.symm z ∈ φ.toChart.target)
    (hδr : ∀ w : φ.stableSubspace, ‖w‖ < δ → ‖φ.coord w‖ < r / 2) {w : φ.stableSubspace}
    (hw : ‖w‖ < δ) : (w : E) ∈ φ.toChart.target := by
  have hr : 0 < r := by linarith [norm_nonneg (φ.coord w), hδr w hw]
  simpa using hrT _ ((hδr w hw).trans (half_lt_self hr))

end MorseChart

namespace IsAdaptedPseudoGradient

variable (hX : IsAdaptedPseudoGradient f X) (φ : MorseChart E f x)

/-- The **parametrization of the stable manifold** by the stable subspace `L` of a Morse chart `φ`:
the point `Φ_{-T} (φ⁻¹ (e^{-T} v))`, where `Φ` is the flow, for the time
`T = log (1 + ‖v‖ / δ)`, which makes `‖e^{-T} v‖ < δ`. When `X` is linear in the chart and `δ` is
small enough, the result does not depend on the choice of such a time
(`TauCeti.IsAdaptedPseudoGradient.stableParam_eq`). -/
noncomputable def stableParam (δ : ℝ) (v : φ.stableSubspace) : M :=
  hX.flow (-Real.log (1 + ‖v‖ / δ))
    (φ.toChart.symm (Real.exp (-Real.log (1 + ‖v‖ / δ)) • (v : E)))

variable (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
    fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
  {r : ℝ} (hrT : ∀ z, ‖z‖ < r → φ.coord.symm z ∈ φ.toChart.target)
  {δ : ℝ} (hδr : ∀ w : φ.stableSubspace, ‖w‖ < δ → ‖φ.coord w‖ < r / 2)
include hφ hrT hδr

/-- **The flow contracts the stable subspace.** For small `w` in the stable subspace and `s ≥ 0`,
the flow moves `φ⁻¹ w` to `φ⁻¹ (e^{-s} w)`. -/
theorem flow_toChart_symm_stableSubspace {w : φ.stableSubspace} (hw : ‖w‖ < δ) {s : ℝ}
    (hs : 0 ≤ s) : hX.flow s (φ.toChart.symm w) = φ.toChart.symm (Real.exp (-s) • (w : E)) := by
  simpa using hX.flow_toChart_symm_of_forall_coord_eq_zero φ hφ hrT (hδr w hw)
    (φ.mem_stableSubspace.1 w.2) hs

/-- Small vectors of the stable subspace parametrize points of the stable manifold. -/
theorem toChart_symm_mem_stableSet {w : φ.stableSubspace} (hw : ‖w‖ < δ) :
    φ.toChart.symm w ∈ hX.flow.stableSet x := by
  have ht := φ.coe_mem_target_of_norm_lt hrT hδr hw
  refine hX.mem_stableSet_of_forall_coord_eq_zero φ hφ hrT (φ.toChart.map_target ht) ?_ ?_ <;>
    rw [φ.toChart.right_inv ht]
  · exact hδr w hw
  · exact φ.mem_stableSubspace.1 w.2

/-- **Flowing along the stable subspace adds times.** If `e^{-T} ‖v‖ < δ`, the flow for a time
`s ≥ 0` moves `φ⁻¹ (e^{-T} v)` to `φ⁻¹ (e^{-(T + s)} v)`. -/
theorem flow_toChart_symm_exp_smul {v : φ.stableSubspace} {T s : ℝ}
    (hT : Real.exp (-T) * ‖v‖ < δ) (hs : 0 ≤ s) :
    hX.flow s (φ.toChart.symm (Real.exp (-T) • (v : E))) =
      φ.toChart.symm (Real.exp (-(T + s)) • (v : E)) := by
  have hw : ‖Real.exp (-T) • v‖ < δ := by
    rwa [norm_smul_of_nonneg (Real.exp_pos _).le]
  rw [← Submodule.coe_smul, hX.flow_toChart_symm_stableSubspace φ hφ hrT hδr hw hs,
    Submodule.coe_smul, smul_smul, ← Real.exp_add, neg_add, add_comm]

/-- Two admissible times give the same point. -/
theorem flow_neg_toChart_symm_eq {v : φ.stableSubspace} {T T' : ℝ} (hTT' : T ≤ T')
    (hT : Real.exp (-T) * ‖v‖ < δ) :
    hX.flow (-T) (φ.toChart.symm (Real.exp (-T) • (v : E))) =
      hX.flow (-T') (φ.toChart.symm (Real.exp (-T') • (v : E))) := by
  have h := hX.flow_toChart_symm_exp_smul φ hφ hrT hδr hT (sub_nonneg.2 hTT')
  rw [add_sub_cancel] at h
  rw [← h, ← Flow.map_add, neg_add_eq_sub, sub_sub_cancel_left]

/-- **The parametrization does not depend on the time.** For every time `T` with
`e^{-T} ‖v‖ < δ`, the parametrization of `v` is `Φ_{-T} (φ⁻¹ (e^{-T} v))`. -/
theorem stableParam_eq (hδ : 0 < δ) {v : φ.stableSubspace} {T : ℝ}
    (hT : Real.exp (-T) * ‖v‖ < δ) :
    hX.stableParam φ δ v = hX.flow (-T) (φ.toChart.symm (Real.exp (-T) • (v : E))) := by
  have hτ := Real.exp_neg_log_one_add_div_mul_lt hδ (norm_nonneg v)
  rw [stableParam]
  rcases le_total T (Real.log (1 + ‖v‖ / δ)) with h | h
  · exact (hX.flow_neg_toChart_symm_eq φ hφ hrT hδr h hT).symm
  · exact hX.flow_neg_toChart_symm_eq φ hφ hrT hδr h hτ

/-- Near `0`, the parametrization is the inverse of the chart. -/
theorem stableParam_of_norm_lt {v : φ.stableSubspace} (hv : ‖v‖ < δ) :
    hX.stableParam φ δ v = φ.toChart.symm v := by
  have hδ : 0 < δ := (norm_nonneg v).trans_lt hv
  rw [hX.stableParam_eq φ hφ hrT hδr hδ (T := 0) (by simpa using hv)]
  simp

/-- The parametrization sends `0` to the critical point. -/
theorem stableParam_zero (hδ : 0 < δ) : hX.stableParam φ δ 0 = x := by
  rw [hX.stableParam_of_norm_lt φ hφ hrT hδr (by simpa using hδ), ZeroMemClass.coe_zero,
    ← φ.apply_self, φ.toChart.left_inv φ.mem_source]

/-- **The tangent space of the stable manifold at the critical point.** Read in the Morse chart,
the derivative of the parametrization at `0` is the inclusion of the stable subspace. -/
theorem mfderiv_toChart_comp_stableParam_zero (hδ : 0 < δ) :
    mfderiv 𝓘(ℝ, φ.stableSubspace) 𝓘(ℝ, E) (φ.toChart ∘ hX.stableParam φ δ) 0 =
      φ.stableSubspace.subtypeL := by
  -- Near `0` the chart undoes the parametrization.
  have h : φ.toChart ∘ hX.stableParam φ δ =ᶠ[𝓝 0] φ.stableSubspace.subtypeL := by
    filter_upwards [ball_mem_nhds (0 : φ.stableSubspace) hδ] with v hv
    have hv' : ‖v‖ < δ := mem_ball_zero_iff.1 hv
    rw [comp_apply, hX.stableParam_of_norm_lt φ hφ hrT hδr hv',
      φ.toChart.right_inv (φ.coe_mem_target_of_norm_lt hrT hδr hv')]
    rfl
  rw [h.mfderiv_eq, mfderiv_eq_fderiv, ContinuousLinearMap.fderiv]
  -- The identifications of the tangent spaces with the model spaces are identities.
  rfl

/-- **The parametrization intertwines the scaling with the flow.** Scaling `v` by `e^{-s}` moves its
image by the time-`s` map of the flow. -/
theorem stableParam_smul (hδ : 0 < δ) (v : φ.stableSubspace) (s : ℝ) :
    hX.stableParam φ δ (Real.exp (-s) • v) = hX.flow s (hX.stableParam φ δ v) := by
  set τ := Real.log (1 + ‖v‖ / δ)
  have hτ : Real.exp (-τ) * ‖v‖ < δ := Real.exp_neg_log_one_add_div_mul_lt hδ (norm_nonneg v)
  -- Rescaling `v` by `e^{-s}` shifts the admissible time from `τ` to `τ - s`.
  have hexp : Real.exp (-(τ - s)) * Real.exp (-s) = Real.exp (-τ) := by
    rw [← Real.exp_add]; ring_nf
  have hτs : Real.exp (-(τ - s)) * ‖Real.exp (-s) • v‖ < δ := by
    rwa [norm_smul_of_nonneg (Real.exp_pos _).le, ← mul_assoc, hexp]
  rw [hX.stableParam_eq φ hφ hrT hδr hδ hτs, hX.stableParam_eq φ hφ hrT hδr hδ hτ,
    ← Flow.map_add, Submodule.coe_smul, smul_smul, hexp, neg_sub, sub_eq_add_neg]

/-- The parametrization takes values in the stable manifold. -/
theorem stableParam_mem_stableSet (hδ : 0 < δ) (v : φ.stableSubspace) :
    hX.stableParam φ δ v ∈ hX.flow.stableSet x := by
  rw [hX.stableParam_eq φ hφ hrT hδr hδ (Real.exp_neg_log_one_add_div_mul_lt hδ (norm_nonneg v)),
    Flow.apply_mem_stableSet_iff, ← Submodule.coe_smul]
  exact hX.toChart_symm_mem_stableSet φ hφ hrT hδr (φ.norm_exp_neg_log_smul_lt hδ v)

/-- The parametrization is injective. -/
theorem stableParam_injective (hδ : 0 < δ) : Injective (hX.stableParam φ δ) := by
  intro v v' h
  set T := max (Real.log (1 + ‖v‖ / δ)) (Real.log (1 + ‖v'‖ / δ))
  have hle {a : ℝ} (ha : a ≤ T) (w : φ.stableSubspace) :
      Real.exp (-T) * ‖w‖ ≤ Real.exp (-a) * ‖w‖ := by
    gcongr
  have hT := (hle (le_max_left _ _) v).trans_lt
    (Real.exp_neg_log_one_add_div_mul_lt hδ (norm_nonneg v))
  have hT' := (hle (le_max_right _ _) v').trans_lt
    (Real.exp_neg_log_one_add_div_mul_lt hδ (norm_nonneg v'))
  have hsmall {w : φ.stableSubspace} (hw : Real.exp (-T) * ‖w‖ < δ) :
      ‖Real.exp (-T) • w‖ < δ := by
    rwa [norm_smul_of_nonneg (Real.exp_pos _).le]
  rw [hX.stableParam_eq φ hφ hrT hδr hδ hT, hX.stableParam_eq φ hφ hrT hδr hδ hT'] at h
  have h1 := congrArg (hX.flow T) h
  simp only [← Flow.map_add, add_neg_cancel, Flow.map_zero_apply] at h1
  have h2 := φ.toChart.symm.injOn
    (by simpa using φ.coe_mem_target_of_norm_lt hrT hδr (hsmall hT))
    (by simpa using φ.coe_mem_target_of_norm_lt hrT hδr (hsmall hT')) h1
  exact Subtype.ext (smul_right_injective E (Real.exp_pos _).ne' h2)

/-- **Points of the stable manifold near the critical point.** Let `y ∈ W^s(x)` reach, at time
`T`, a point of the small cube of the chart in which `W^s(x)` is the stable subspace. Then the
coordinates `u` of that point lie in the stable subspace, and `y` is the image of `e^T u`. -/
theorem exists_eq_stableParam {ε : ℝ}
    (hε : ∀ y ∈ φ.toChart.source, ‖φ.coord (φ.toChart y)‖ < ε →
      y ∈ hX.flow.stableSet x → ∀ i, φ.weight i < 0 → φ.coord (φ.toChart y) i = 0)
    {y : M} (hy : y ∈ hX.flow.stableSet x) {T : ℝ} (hTs : hX.flow T y ∈ φ.toChart.source)
    (hTε : ‖φ.coord (φ.toChart (hX.flow T y))‖ < ε) (hTδ : ‖φ.toChart (hX.flow T y)‖ < δ) :
    ∃ u : φ.stableSubspace, (u : E) = φ.toChart (hX.flow T y) ∧
      y = hX.stableParam φ δ (Real.exp T • u) := by
  have hδ : 0 < δ := (norm_nonneg _).trans_lt hTδ
  have hu : φ.toChart (hX.flow T y) ∈ φ.stableSubspace :=
    φ.mem_stableSubspace.2 (hε _ hTs hTε ((Flow.apply_mem_stableSet_iff _ _).2 hy))
  refine ⟨⟨_, hu⟩, rfl, ?_⟩
  have hT : Real.exp (-T) * ‖Real.exp T • (⟨_, hu⟩ : φ.stableSubspace)‖ < δ := by
    rwa [norm_smul_of_nonneg (Real.exp_pos _).le, Real.exp_neg,
      inv_mul_cancel_left₀ (Real.exp_ne_zero T)]
  rw [hX.stableParam_eq φ hφ hrT hδr hδ hT, Submodule.coe_smul, Real.exp_neg,
    inv_smul_smul₀ (Real.exp_ne_zero T), Submodule.coe_mk, φ.toChart.left_inv hTs,
    ← Flow.map_add, neg_add_cancel, Flow.map_zero_apply]

/-- **The parametrization covers the stable manifold.** Its image is `W^s(x)`. -/
theorem range_stableParam (hδ : 0 < δ) {ε : ℝ} (hε0 : 0 < ε)
    (hε : ∀ y ∈ φ.toChart.source, ‖φ.coord (φ.toChart y)‖ < ε →
      y ∈ hX.flow.stableSet x → ∀ i, φ.weight i < 0 → φ.coord (φ.toChart y) i = 0) :
    range (hX.stableParam φ δ) = hX.flow.stableSet x := by
  refine (range_subset_iff.2 (hX.stableParam_mem_stableSet φ hφ hrT hδr hδ)).antisymm
    fun y hy ↦ ?_
  -- Every point of `W^s(x)` reaches the small cube of the chart, where `W^s(x)` is `L`.
  obtain ⟨T, hTs, hTε, hTδ⟩ := ((Flow.mem_stableSet.1 hy).eventually
    ((φ.isOpen_smallCube ε δ).mem_nhds (φ.mem_smallCube hε0 hδ))).exists
  obtain ⟨u, -, hyu⟩ := hX.exists_eq_stableParam φ hφ hrT hδr hε hy hTs hTε hTδ
  exact ⟨_, hyu.symm⟩

/-- Near `0`, the parametrization is an immersion. -/
theorem isImmersionAt_stableParam_of_norm_lt {v : φ.stableSubspace}
    (hv : ‖v‖ < δ) : IsImmersionAt 𝓘(ℝ, φ.stableSubspace) 𝓘(ℝ, E) ∞ (hX.stableParam φ δ) v := by
  -- Near `0` the parametrization is the inverse of the chart, restricted to the stable subspace.
  have hδ : 0 < δ := (norm_nonneg v).trans_lt hv
  obtain ⟨N, hN⟩ := φ.stableSubspace.exists_isCompl
  have hball : IsOpen (ball (0 : φ.stableSubspace) δ) := isOpen_ball
  refine (IsImmersionAtOfComplement.mk_of_charts (F := N)
    (Submodule.prodEquivOfIsCompl _ _ hN).toContinuousLinearEquiv
    ((chartAt φ.stableSubspace v).restr (ball 0 δ)) φ.toChart ?_ ?_
    (restr_mem_maximalAtlas _ (IsManifold.chart_mem_maximalAtlas v) hball) φ.mem_maximalAtlas
    ?_ ?_).isImmersionAt
  · simpa [hball.interior_eq] using hv
  · rw [hX.stableParam_of_norm_lt φ hφ hrT hδr hv]
    exact φ.toChart.map_target (φ.coe_mem_target_of_norm_lt hrT hδr hv)
  · intro w hw
    have hw' : ‖w‖ < δ := by simpa [hball.interior_eq] using hw
    rw [mem_preimage, hX.stableParam_of_norm_lt φ hφ hrT hδr hw']
    exact φ.toChart.map_target (φ.coe_mem_target_of_norm_lt hrT hδr hw')
  · intro u hu
    have hu' : ‖u‖ < δ := by simpa [hball.interior_eq] using hu
    simp [hX.stableParam_of_norm_lt φ hφ hrT hδr hu',
      φ.toChart.right_inv (φ.coe_mem_target_of_norm_lt hrT hδr hu')]

/-- **The parametrization is an immersion.** -/
theorem isImmersion_stableParam (hδ : 0 < δ) :
    IsImmersion 𝓘(ℝ, φ.stableSubspace) 𝓘(ℝ, E) ∞ (hX.stableParam φ δ) := by
  refine isImmersion_iff_forall_isImmersionAt.2 fun v ↦ ?_
  set T := Real.log (1 + ‖v‖ / δ)
  have hc : Real.exp (-T) ≠ 0 := (Real.exp_pos _).ne'
  set e : φ.stableSubspace ≃ₘ^∞⟮𝓘(ℝ, φ.stableSubspace), 𝓘(ℝ, φ.stableSubspace)⟯ φ.stableSubspace :=
    (LinearEquiv.smulOfNeZero ℝ φ.stableSubspace _ hc).toContinuousLinearEquiv.toDiffeomorph
  have he (w : φ.stableSubspace) : e w = Real.exp (-T) • w := rfl
  have hcomp : hX.stableParam φ δ = hX.flowDiffeomorph (-T) ∘ hX.stableParam φ δ ∘ e := by
    funext w
    rw [comp_apply, comp_apply, he, hX.stableParam_smul φ hφ hrT hδr hδ, flowDiffeomorph_apply,
      ← Flow.map_add, neg_add_cancel, Flow.map_zero_apply]
  rw [hcomp, isImmersionAt_diffeomorph_comp_iff, isImmersionAt_comp_diffeomorph_iff, he]
  exact hX.isImmersionAt_stableParam_of_norm_lt φ hφ hrT hδr (φ.norm_exp_neg_log_smul_lt hδ v)

/-- **The parametrization is a topological embedding.** -/
theorem isEmbedding_stableParam (hδ : 0 < δ) {ε : ℝ} (hεδ : ∀ w : φ.stableSubspace, ‖w‖ < δ →
      ‖φ.coord w‖ < ε)
    (hε : ∀ y ∈ φ.toChart.source, ‖φ.coord (φ.toChart y)‖ < ε →
      y ∈ hX.flow.stableSet x → ∀ i, φ.weight i < 0 → φ.coord (φ.toChart y) i = 0) :
    IsEmbedding (hX.stableParam φ δ) := by
  have hcont : Continuous (hX.stableParam φ δ) := continuous_iff_continuousAt.2 fun v ↦
    ((hX.isImmersion_stableParam φ hφ hrT hδr hδ).isImmersionAt v).contMDiffAt.continuousAt
  refine ⟨isInducing_iff_nhds.2 fun v ↦ le_antisymm (hcont.tendsto v).le_comap ?_,
    hX.stableParam_injective φ hφ hrT hδr hδ⟩
  set T := Real.log (1 + ‖v‖ / δ)
  have hw₀ : ‖Real.exp (-T) • v‖ < δ := φ.norm_exp_neg_log_smul_lt hδ v
  have ht := φ.coe_mem_target_of_norm_lt hrT hδr hw₀
  have hy₀ : hX.flow T (hX.stableParam φ δ v) =
      φ.toChart.symm (Real.exp (-T) • v : φ.stableSubspace) := by
    rw [← hX.stableParam_smul φ hφ hrT hδr hδ, hX.stableParam_of_norm_lt φ hφ hrT hδr hw₀]
  have hsrc : hX.flow T (hX.stableParam φ δ v) ∈ φ.toChart.source := hy₀ ▸ φ.toChart.map_target ht
  have hchart : φ.toChart (hX.flow T (hX.stableParam φ δ v)) =
      (Real.exp (-T) • v : φ.stableSubspace) := by
    rw [hy₀, φ.toChart.right_inv ht]
  -- The neighbourhood of the image of `v` that the flow takes into the small cube.
  set V := hX.flow T ⁻¹' (φ.toChart.source ∩ φ.toChart ⁻¹' {w : E | ‖φ.coord w‖ < ε ∧ ‖w‖ < δ})
  have hV : V ∈ 𝓝 (hX.stableParam φ δ v) :=
    ((φ.isOpen_smallCube ε δ).preimage (hX.flow.continuous_toFun T)).mem_nhds
      ⟨hsrc, by rw [mem_preimage, hchart]; exact ⟨hεδ _ hw₀, hw₀⟩⟩
  -- On that neighbourhood, `y ↦ e^T φ (Φ_T y)` is a continuous left inverse.
  set h : M → E := fun y ↦ Real.exp T • φ.toChart (hX.flow T y)
  have hh : Tendsto h (𝓝 (hX.stableParam φ δ v)) (𝓝 (v : E)) := by
    have hv : (v : E) = h (hX.stableParam φ δ v) := by
      simp only [h, hchart, Submodule.coe_smul, Real.exp_neg, smul_inv_smul₀ (Real.exp_ne_zero T)]
    rw [hv]
    exact (((φ.toChart.continuousAt hsrc).comp
      (hX.flow.continuous_toFun T).continuousAt).const_smul (Real.exp T)).tendsto
  have hinv (w : φ.stableSubspace) (hw : hX.stableParam φ δ w ∈ V) :
      h (hX.stableParam φ δ w) = w := by
    obtain ⟨hTs, hTε, hTδ⟩ := hw
    obtain ⟨u, hu, hwu⟩ := hX.exists_eq_stableParam φ hφ hrT hδr hε
      (hX.stableParam_mem_stableSet φ hφ hrT hδr hδ w) hTs hTε hTδ
    conv_rhs => rw [hX.stableParam_injective φ hφ hrT hδr hδ hwu]
    rw [Submodule.coe_smul, hu]
  rw [Topology.IsInducing.subtypeVal.nhds_eq_comap, ← tendsto_iff_comap]
  exact (hh.comp tendsto_comap).congr' (mem_of_superset (preimage_mem_comap hV) hinv)

/-- **The parametrization is a smooth embedding.** -/
theorem isSmoothEmbedding_stableParam (hδ : 0 < δ) {ε : ℝ} (hεδ : ∀ w : φ.stableSubspace,
      ‖w‖ < δ → ‖φ.coord w‖ < ε)
    (hε : ∀ y ∈ φ.toChart.source, ‖φ.coord (φ.toChart y)‖ < ε →
      y ∈ hX.flow.stableSet x → ∀ i, φ.weight i < 0 → φ.coord (φ.toChart y) i = 0) :
    IsSmoothEmbedding 𝓘(ℝ, φ.stableSubspace) 𝓘(ℝ, E) ∞ (hX.stableParam φ δ) :=
  ⟨hX.isImmersion_stableParam φ hφ hrT hδr hδ,
    hX.isEmbedding_stableParam φ hφ hrT hδr hδ hεδ hε⟩

omit hφ hrT hδr

/-- **The parametrization of the stable manifold, with its chart.** For a critical point `x`, there
are a Morse chart `φ` at `x` and a scale `δ` for which `stableParam φ δ` is a smooth embedding of
the stable subspace of `φ` with image `W^s(x)`, sending `0` to `x`, whose derivative at `0`, read in
the chart, is the inclusion of the stable subspace. -/
theorem exists_stableParam (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f)
    (hx : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0) :
    ∃ (φ : MorseChart E f x) (δ : ℝ),
      IsSmoothEmbedding 𝓘(ℝ, φ.stableSubspace) 𝓘(ℝ, E) ∞ (hX.stableParam φ δ) ∧
      range (hX.stableParam φ δ) = hX.flow.stableSet x ∧ hX.stableParam φ δ 0 = x ∧
      mfderiv 𝓘(ℝ, φ.stableSubspace) 𝓘(ℝ, E) (φ.toChart ∘ hX.stableParam φ δ) 0 =
        φ.stableSubspace.subtypeL := by
  obtain ⟨φ, hφ⟩ := hX.exists_morseChart x hx
  obtain ⟨r, hr, hrT⟩ := φ.exists_pos_forall_norm_lt_mem_target
  obtain ⟨ε, hε0, hε⟩ := hX.exists_forall_mem_stableSet_iff φ hφ hf
  set A := ‖(φ.coordL : E →L[ℝ] Fin (Module.finrank ℝ E) → ℝ)‖
  set δ := min ε (r / 2) / (A + 1)
  have hc : 0 < min ε (r / 2) := lt_min hε0 (half_pos hr)
  have hA : 0 < A + 1 := by positivity
  have hδ : 0 < δ := by positivity
  have hsmall (w : φ.stableSubspace) (hw : ‖w‖ < δ) : ‖φ.coord w‖ < min ε (r / 2) := by
    calc ‖φ.coord w‖ = ‖(φ.coordL : E →L[ℝ] Fin (Module.finrank ℝ E) → ℝ) w‖ := by simp
      _ ≤ A * ‖w‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ A * δ := by gcongr
      _ < (A + 1) * δ := by nlinarith
      _ = min ε (r / 2) := mul_div_cancel₀ _ hA.ne'
  have hδr (w : φ.stableSubspace) (hw : ‖w‖ < δ) : ‖φ.coord w‖ < r / 2 :=
    (hsmall w hw).trans_le (min_le_right _ _)
  have hεδ (w : φ.stableSubspace) (hw : ‖w‖ < δ) : ‖φ.coord w‖ < ε :=
    (hsmall w hw).trans_le (min_le_left _ _)
  have hεs := fun y hy hyε ↦ (hε y hy hyε).1
  exact ⟨φ, δ, hX.isSmoothEmbedding_stableParam φ hφ hrT hδr hδ hεδ hεs,
    hX.range_stableParam φ hφ hrT hδr hδ hε0 hεs, hX.stableParam_zero φ hφ hrT hδr hδ,
    hX.mfderiv_toChart_comp_stableParam_zero φ hφ hrT hδr hδ⟩

/-- **The stable manifold is a smoothly embedded vector space.** For a critical point `x` of
index `k`, the stable manifold `W^s(x)` of the flow of an adapted pseudo-gradient is the image of
a smooth embedding of a real vector space of dimension `n - k`, sending `0` to `x`. -/
theorem exists_isSmoothEmbedding_stableSet (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f)
    (hx : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0) :
    ∃ L : Submodule ℝ E,
      Module.finrank ℝ L + manifoldMorseIndex 𝓘(ℝ, E) f x = Module.finrank ℝ E ∧
      ∃ ι : L → M, IsSmoothEmbedding 𝓘(ℝ, L) 𝓘(ℝ, E) ∞ ι ∧
        range ι = hX.flow.stableSet x ∧ ι 0 = x := by
  obtain ⟨φ, δ, hemb, hrange, h0, -⟩ := hX.exists_stableParam hf hx
  exact ⟨φ.stableSubspace, φ.finrank_stableSubspace_add_manifoldMorseIndex,
    hX.stableParam φ δ, hemb, hrange, h0⟩

/-- **The unstable manifold is a smoothly embedded vector space.** For a critical point `x` of
index `k` of a Morse function, the unstable manifold `W^u(x)` of the flow of an adapted
pseudo-gradient is the image of a smooth embedding of a real vector space of dimension `k`, sending
`0` to `x`. -/
theorem exists_isSmoothEmbedding_unstableSet (hf : IsMorse 𝓘(ℝ, E) f)
    (hx : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0) :
    ∃ L : Submodule ℝ E, Module.finrank ℝ L = manifoldMorseIndex 𝓘(ℝ, E) f x ∧
      ∃ ι : L → M, IsSmoothEmbedding 𝓘(ℝ, L) 𝓘(ℝ, E) ∞ ι ∧
        range ι = hX.flow.unstableSet x ∧ ι 0 = x := by
  obtain ⟨L, hL, hemb⟩ := (hX.neg hf).exists_isSmoothEmbedding_stableSet
    (hf.neg.contMDiff.mdifferentiable (by simp)) (mfderiv_neg_eq_zero_iff.2 hx)
  have hidx := (hf.isManifoldNondegenerateCriticalPoint_of_mfderiv_eq_zero hx
    ).manifoldMorseIndex_neg_add_manifoldMorseIndex_eq_finrank
  rw [hX.unstableSet_eq_stableSet_neg hf]
  exact ⟨L, by omega, hemb⟩

end IsAdaptedPseudoGradient

end TauCeti
