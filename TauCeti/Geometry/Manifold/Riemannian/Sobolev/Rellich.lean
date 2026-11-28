/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Sobolev.Embedding
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import TauCeti.Analysis.Normed.Operator.Compact.Interpolation
import TauCeti.Analysis.Normed.Operator.Compact.Domination
import TauCeti.Analysis.Sobolev.W1p.LocalCompactness
import TauCeti.Data.ENNReal.InterpolatedExponent
import TauCeti.Geometry.Manifold.Riemannian.Sobolev.Chart
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Volume
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# The Rellich–Kondrachov theorem on a closed Riemannian manifold

Let `M` be a compact manifold without boundary with a continuous Riemannian metric, its Riemannian
volume `dV`, and the Sobolev space `H¹(M)` (`TauCeti.Manifold.SobolevH1`). This file proves that
the value map `H¹(M) → L²(M)` is a compact operator
(`TauCeti.Manifold.SobolevH1.isCompactOperator_toLp`): a bounded sequence in `H¹(M)` has a
subsequence converging in `L²(M)`. In dimension `n > 2`, interpolating with the critical Sobolev
embedding `H¹(M) → L^{2n/(n-2)}(M)` gives compactness of `H¹(M) → L^q(M)` for every
`1 ≤ q < 2n/(n-2)` (`TauCeti.Manifold.SobolevH1.isCompactOperator_toLpOfLE`); the critical
exponent itself is excluded.

Compactness of these embeddings is the input of the direct method of the calculus of variations
on `H¹(M)`: it turns minimizing sequences of Rayleigh quotients, such as that of a Schrödinger
operator `Δ⁺ + V`, or of the subcritical Yamabe quotients, into convergent ones.

## The argument

Compactness is local. Around every point `p`, reading in a chart is a continuous linear map
`T : H¹(M) → W^{1,2}(Ω)` to the Sobolev space of an open set `Ω` of coordinates
(`TauCeti.Manifold.SobolevH1.exists_continuousLinearMap_w1p_extChartAt`). On a coordinate ball `V`
whose closure lies in `Ω`, restricting values from `W^{1,2}(Ω)` to `L²(V)` is compact by the
local Rellich–Kondrachov theorem (`TauCeti.W1p.isCompactOperator_valueL_restrictL`). Since the chart
density of the Riemannian volume is bounded on the compact closure of `V`, the `L²` norm of an
element of `H¹(M)` on the corresponding open set `U ∋ p` of `M` is bounded by a multiple of the
`L²(V)` norm of its chart reading. Finitely many such sets `U` cover `M`, so the `L²(M)` norm is
dominated by the sum of the norms of finitely many compact operators, and an operator so dominated
is compact (`IsCompactOperator.of_enorm_le_mul_sum`).

## Main results

* `TauCeti.Manifold.SobolevH1.isCompactOperator_toLp`: **Rellich–Kondrachov**, the value map
  `H¹(M) → L²(M)` is compact.
* `TauCeti.Manifold.SobolevH1.isCompactOperator_toLpOfLE`: the Sobolev embedding
  `H¹(M) → L^q(M)` is compact for `1 ≤ q < 2n/(n-2)`.

## References

* T. Aubin, *Some Nonlinear Problems in Riemannian Geometry*, Springer (1998), Theorem 2.34.
* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987),
  Theorem 2.2.
-/

public section

open Bundle MeasureTheory Metric Module Set TopologicalSpace
open scoped ContDiff ENNReal Manifold NNReal Topology

noncomputable section

namespace TauCeti.Manifold.SobolevH1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [CompactSpace M] [IsManifold I 1 M]
  [MeasurableSpace M] [BorelSpace M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

section Local

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasureSpace F] [BorelSpace F] [(volume : Measure F).IsAddHaarMeasure]

/-- **Rellich compactness near a point.** Around every point `p` of `M` there are an open set
`U ∋ p` and a compact operator `R` from `H¹(M)` into an `L²` space of coordinates whose norm
controls the `L²` norm on `U` of elements of `H¹(M)`. -/
private theorem exists_isCompactOperator_setLIntegral_le (L : E ≃L[ℝ] F) (p : M) :
    ∃ U : Set M, IsOpen U ∧ p ∈ U ∧ ∃ (V : Set F)
      (R : SobolevH1 I M →L[ℝ] Lp ℝ 2 (volume.restrict V)) (C : ℝ≥0∞), C ≠ ⊤ ∧
        IsCompactOperator R ∧ ∀ w : SobolevH1 I M,
          ∫⁻ x in U, ‖toLp w x‖ₑ ^ (2 : ℝ) ∂riemannianVolume I M ≤ C * ‖R w‖ₑ ^ (2 : ℝ) := by
  obtain ⟨Ω, hpΩ, hΩt, T, -, hT⟩ := exists_continuousLinearMap_w1p_extChartAt (I := I) (M := M) p L
  set y₀ := L (extChartAt I p p)
  obtain ⟨r, hr, hrΩ⟩ := Metric.isOpen_iff.1 Ω.isOpen y₀ hpΩ
  -- A coordinate ball `V` whose closure is a compact subset of `Ω`.
  let V : Opens F := ⟨ball y₀ (r / 2), isOpen_ball⟩
  have hVK : closure (V : Set F) ⊆ closedBall y₀ (r / 2) := closure_ball_subset_closedBall
  have hKΩ : closedBall y₀ (r / 2) ⊆ Ω := (closedBall_subset_ball (half_lt_self hr)).trans hrΩ
  have hVc : IsCompact (closure (V : Set F)) :=
    (isCompact_closedBall y₀ (r / 2)).of_isClosed_subset isClosed_closure hVK
  have hVΩ : closure (V : Set F) ⊆ Ω := hVK.trans hKΩ
  have hVΩ' : V ≤ Ω := SetLike.coe_subset_coe.mp (subset_closure.trans hVΩ)
  -- The compact operator: read in the chart, then restrict the values to `V`.
  set R := ((W1p.valueL (mu := volume) (Omega := V) (p := 2)).comp (W1p.restrictL hVΩ')).comp T
  have hR : IsCompactOperator R := (W1p.isCompactOperator_valueL_restrictL hVc hVΩ).comp_clm T
  have hRw (w : SobolevH1 I M) : R w =ᵐ[volume.restrict (V : Set F)]
      fun y ↦ toLp w ((extChartAt I p).symm (L.symm y)) := by
    simp only [R, ContinuousLinearMap.comp_apply, W1p.valueL_apply]
    exact (W1p.value_restrictL_ae hVΩ' (T w)).trans
      ((hT w).filter_mono (ae_mono (Measure.restrict_mono_set _ (subset_closure.trans hVΩ))))
  obtain ⟨C, hC, hle⟩ := exists_setLIntegral_inter_preimage_le_mul_setLIntegral_comp_extChartAt_symm
    (I := I) L p V.isOpen (isCompact_closedBall y₀ (r / 2)) ball_subset_closedBall
    fun y hy ↦ hΩt (hKΩ hy)
  refine ⟨_, isOpen_extChartAt_preimage' p (L.symm.toHomeomorph.isOpenMap _ V.isOpen),
    ⟨mem_extChartAt_source p, y₀, mem_ball_self (half_pos hr), L.symm_apply_apply _⟩, V, R, C,
    hC, hR, fun w ↦ (hle _).trans_eq ?_⟩
  -- The integral over `V` of the chart reading of `w` is the squared norm of `R w`.
  rw [Lp.eNorm_rpow_two_eq_lintegral]
  congr 1
  refine lintegral_congr_ae ?_
  filter_upwards [hRw w] with y hy
  rw [hy]

end Local

/-- **The Rellich–Kondrachov theorem on a closed manifold.** On a compact manifold without
boundary with a continuous Riemannian metric, the value map `H¹(M) → L²(M)` is a compact operator:
every bounded sequence in `H¹(M)` has a subsequence converging in `L²(M)`. -/
theorem isCompactOperator_toLp :
    IsCompactOperator (toLp : SobolevH1 I M →L[ℝ] Lp ℝ 2 (riemannianVolume I M)) := by
  choose U hUo hpU V R C hC hR hRle using
    fun p : M ↦ exists_isCompactOperator_setLIntegral_le (I := I) (toEuclidean (E := E)) p
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hUo fun p _ ↦ mem_iUnion.2 ⟨p, hpU p⟩
  have hcov : univ ⊆ ⋃ p : t, U p := fun x _ ↦ by
    obtain ⟨p, hp, hx⟩ := mem_iUnion₂.1 (ht (mem_univ x))
    exact mem_iUnion.2 ⟨⟨p, hp⟩, hx⟩
  set D := ∑ p : t, C p
  -- The `L²(M)` norm is dominated by the sum of the norms of the local compact operators.
  have hle (w : SobolevH1 I M) :
      ‖toLp w‖ₑ ^ (2 : ℝ) ≤ D * (∑ p : t, ‖R p w‖ₑ) ^ (2 : ℝ) := by
    rw [Lp.eNorm_rpow_two_eq_lintegral, ← setLIntegral_univ, Finset.sum_mul]
    calc ∫⁻ x in univ, ‖toLp w x‖ₑ ^ (2 : ℝ) ∂riemannianVolume I M
        ≤ ∫⁻ x in ⋃ p : t, U p, ‖toLp w x‖ₑ ^ (2 : ℝ) ∂riemannianVolume I M :=
          lintegral_mono_set hcov
      _ ≤ ∑' p : t, ∫⁻ x in U p, ‖toLp w x‖ₑ ^ (2 : ℝ) ∂riemannianVolume I M :=
          lintegral_iUnion_le _ _
      _ = ∑ p : t, ∫⁻ x in U p, ‖toLp w x‖ₑ ^ (2 : ℝ) ∂riemannianVolume I M := tsum_fintype _
      _ ≤ ∑ p : t, C p * (∑ q : t, ‖R q w‖ₑ) ^ (2 : ℝ) := Finset.sum_le_sum fun p _ ↦ by
          refine (hRle p w).trans ?_
          have h : ‖R p w‖ₑ ≤ ∑ q : t, ‖R q w‖ₑ :=
            Finset.single_le_sum (f := fun q : t ↦ ‖R q w‖ₑ) (fun _ _ ↦ zero_le) (Finset.mem_univ p)
          gcongr
  refine IsCompactOperator.of_enorm_le_mul_sum
    (toLp : SobolevH1 I M →L[ℝ] Lp ℝ 2 (riemannianVolume I M)).toLinearMap (fun p : t ↦ R p)
    (fun p ↦ hR p) (C := D ^ (2⁻¹ : ℝ))
    (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (ENNReal.sum_ne_top.2 fun p _ ↦ hC p)) fun w ↦ ?_
  rw [ContinuousLinearMap.coe_coe, ← ENNReal.rpow_le_rpow_iff two_pos,
    ENNReal.mul_rpow_of_nonneg _ _ zero_le_two, ENNReal.rpow_inv_rpow two_ne_zero]
  exact hle w

/-- **Compact Sobolev embeddings on a closed manifold.** On a compact manifold without boundary of
dimension `n > 2` with a continuous Riemannian metric, the Sobolev embedding `H¹(M) → L^q(M)` is a
compact operator for every `1 ≤ q < 2n/(n-2)`. -/
theorem isCompactOperator_toLpOfLE {q : ℝ≥0∞} [Fact (1 ≤ q)] (hn : 2 < finrank ℝ E)
    (hq : q < ENNReal.ofReal (2 * finrank ℝ E / (finrank ℝ E - 2))) :
    IsCompactOperator (toLpOfLE (I := I) (M := M) hn hq.le) := by
  rcases le_or_gt q 2 with hq2 | hq2
  · exact isCompactOperator_toLp.of_forall_ae_eq_of_le hq2 fun w ↦ by rw [coeFn_toLpOfLE]
  -- For `2 < q`, interpolate between `L²` and the critical exponent `pₙ = 2n/(n-2)`:
  -- `1/q = (1 - θ)/2 + θ/pₙ` for some `θ ∈ (0, 1)`.
  have : Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal (2 * finrank ℝ E / (finrank ℝ E - 2))) :=
    ⟨one_le_two.trans (hq2.le.trans hq.le)⟩
  obtain ⟨θ, hθ, hrel⟩ := exists_inv_eq_of_mem_Ioo two_ne_zero ⟨hq2, hq⟩
  exact isCompactOperator_toLp.of_forall_ae_eq_of_interpolation (toLpOfLE hn le_rfl) hθ.1.le
    hθ.2 hrel (fun w ↦ by rw [coeFn_toLpOfLE]) fun w ↦ by rw [coeFn_toLpOfLE, coeFn_toLpOfLE]

end TauCeti.Manifold.SobolevH1
