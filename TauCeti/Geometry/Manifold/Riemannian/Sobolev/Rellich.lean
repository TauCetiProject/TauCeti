/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Sobolev.Embedding
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import TauCeti.Analysis.Normed.Operator.Compact.Interpolation
import TauCeti.Analysis.Normed.Operator.Compact.Pi
import TauCeti.Analysis.Sobolev.W1p.LocalCompactness
import TauCeti.Geometry.Manifold.Riemannian.Sobolev.Chart
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Volume

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
dominated by the norm of a compact operator into a finite product of `L²` spaces
(`IsCompactOperator.pi`), and an operator dominated by a compact one is compact
(`IsCompactOperator.of_norm_le_mul_rpow_mul_rpow`).

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

/-- The squared norm of an element of `L²` is the integral of its squared pointwise norm. -/
private theorem eNorm_rpow_two_eq_lintegral {α G : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup G] (f : Lp G 2 μ) :
    ‖f‖ₑ ^ (2 : ℝ) = ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ := by
  simpa only [ENNReal.coe_ofNat, NNReal.coe_ofNat, ← Lp.eNorm_def] using
    eLpNorm_nnreal_pow_eq_lintegral (p := 2) two_ne_zero (Lp.aestronglyMeasurable f)

section Local

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasureSpace F] [BorelSpace F] [(volume : Measure F).IsAddHaarMeasure]

omit [I.Boundaryless] [FiniteDimensional ℝ F] in
/-- **Integrals over a chart neighbourhood in coordinates.** Let `L` identify the model space
with `F`, and let `V` be an open subset of a compact set `K` of `F` that `L⁻¹` maps into the chart
target at `p`. The integral of a function `g ≥ 0` over the corresponding open set of `M` is at
most a constant multiple, independent of `g`, of the integral over `V` of `g` read in the chart. -/
private theorem exists_setLIntegral_le_mul_setLIntegral_comp (L : E ≃L[ℝ] F) (p : M) {V K : Set F}
    (hV : IsOpen V) (hK : IsCompact K) (hVK : V ⊆ K)
    (hKt : MapsTo L.symm K (extChartAt I p).target) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ g : M → ℝ≥0∞,
      ∫⁻ x in (extChartAt I p).source ∩ extChartAt I p ⁻¹' (L.symm '' V), g x
          ∂riemannianVolume I M ≤
        C * ∫⁻ y in V, g ((extChartAt I p).symm (L.symm y)) ∂volume := by
  let _ : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  set W := L.symm '' V
  have hWo : IsOpen W := L.symm.toHomeomorph.isOpenMap _ hV
  have hWt : W ⊆ (extChartAt I p).target := (image_mono hVK).trans (mapsTo_iff_image_subset.1 hKt)
  -- The chart density is bounded by `D` over `W`.
  obtain ⟨D, hD⟩ := (hK.image L.symm.continuous).exists_bound_of_continuousOn
    ((continuousOn_chartVolumeDensity_extChartAt_symm (I := I) p).mono
      (mapsTo_iff_image_subset.1 hKt))
  -- The image of the Haar measure of `F` is a positive multiple `c` of the Haar measure of `E`.
  have : ((volume : Measure F).map L.symm).IsAddHaarMeasure := L.symm.isAddHaarMeasure_map volume
  set c := Measure.addHaarScalarFactor ((volume : Measure F).map L.symm)
    (Module.finBasis ℝ E).addHaar
  have hc : (volume : Measure F).map L.symm = (c : ℝ≥0∞) • (Module.finBasis ℝ E).addHaar := by
    rw [← ENNReal.smul_def]
    exact Measure.isAddLeftInvariant_eq_smul _ _
  have hc0 : (c : ℝ≥0∞) ≠ 0 :=
    ENNReal.coe_ne_zero.2 (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _).ne'
  refine ⟨ENNReal.ofReal D * (c : ℝ≥0∞)⁻¹,
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.inv_ne_top.2 hc0), fun g ↦ ?_⟩
  -- Changing variables along `L⁻¹`, the integral over `W` is `c⁻¹` times that over `V`.
  set e := L.symm.toHomeomorph.toMeasurableEquiv
  have he : (e : F → E) = L.symm := by
    rw [Homeomorph.toMeasurableEquiv_coe, ContinuousLinearEquiv.coe_toHomeomorph]
  have hcoord : (c : ℝ≥0∞) * ∫⁻ z in W, g ((extChartAt I p).symm z)
      ∂(Module.finBasis ℝ E).addHaar = ∫⁻ y in V, g ((extChartAt I p).symm (L.symm y)) := by
    rw [← smul_eq_mul, ← lintegral_smul_measure, ← Measure.restrict_smul, ← hc, ← he,
      e.restrict_map, lintegral_map_equiv, he, L.symm.injective.preimage_image]
  calc ∫⁻ x in (extChartAt I p).source ∩ extChartAt I p ⁻¹' W, g x ∂riemannianVolume I M
      ≤ ENNReal.ofReal D * ∫⁻ z in W, g ((extChartAt I p).symm z)
          ∂(Module.finBasis ℝ E).addHaar :=
        setLIntegral_inter_preimage_le_mul_setLIntegral_comp_extChartAt_symm p hWo hWt
          (fun z hz ↦ (Real.le_norm_self _).trans (hD z (image_mono hVK hz))) g
    _ = ENNReal.ofReal D * (c : ℝ≥0∞)⁻¹ *
          ∫⁻ y in V, g ((extChartAt I p).symm (L.symm y)) := by
        rw [← hcoord, mul_assoc, ENNReal.inv_mul_cancel_left hc0 ENNReal.coe_ne_top]

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
  obtain ⟨C, hC, hle⟩ := exists_setLIntegral_le_mul_setLIntegral_comp (I := I) L p V.isOpen
    (isCompact_closedBall y₀ (r / 2)) ball_subset_closedBall fun y hy ↦ hΩt (hKΩ hy)
  refine ⟨_, isOpen_extChartAt_preimage' p (L.symm.toHomeomorph.isOpenMap _ V.isOpen),
    ⟨mem_extChartAt_source p, y₀, mem_ball_self (half_pos hr), L.symm_apply_apply _⟩, V, R, C,
    hC, hR, fun w ↦ (hle _).trans_eq ?_⟩
  -- The integral over `V` of the chart reading of `w` is the squared norm of `R w`.
  rw [eNorm_rpow_two_eq_lintegral]
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
  -- The finitely many local compact operators, as one compact operator into a product.
  let R' : SobolevH1 I M →L[ℝ] (∀ p : t, Lp ℝ 2 (volume.restrict (V p))) :=
    ContinuousLinearMap.pi fun p ↦ R p
  have hR' : IsCompactOperator R' := IsCompactOperator.pi fun p ↦ hR p
  set D := ∑ p : t, C p
  have hD : D ≠ ⊤ := ENNReal.sum_ne_top.2 fun p _ ↦ hC p
  -- The `L²(M)` norm is dominated by the norm of `R'`.
  have hle (w : SobolevH1 I M) : ‖toLp w‖ₑ ^ (2 : ℝ) ≤ D * ‖R' w‖ₑ ^ (2 : ℝ) := by
    rw [eNorm_rpow_two_eq_lintegral, ← setLIntegral_univ, Finset.sum_mul]
    calc ∫⁻ x in univ, ‖toLp w x‖ₑ ^ (2 : ℝ) ∂riemannianVolume I M
        ≤ ∫⁻ x in ⋃ p : t, U p, ‖toLp w x‖ₑ ^ (2 : ℝ) ∂riemannianVolume I M :=
          lintegral_mono_set hcov
      _ ≤ ∑' p : t, ∫⁻ x in U p, ‖toLp w x‖ₑ ^ (2 : ℝ) ∂riemannianVolume I M :=
          lintegral_iUnion_le _ _
      _ = ∑ p : t, ∫⁻ x in U p, ‖toLp w x‖ₑ ^ (2 : ℝ) ∂riemannianVolume I M := tsum_fintype _
      _ ≤ ∑ p : t, C p * ‖R' w‖ₑ ^ (2 : ℝ) := Finset.sum_le_sum fun p _ ↦ by
          refine (hRle p w).trans ?_
          have h : ‖R p w‖ₑ ≤ ‖R' w‖ₑ := by
            rw [← ofReal_norm, ← ofReal_norm]
            exact ENNReal.ofReal_le_ofReal (norm_le_pi_norm (R' w) p)
          gcongr
  refine IsCompactOperator.of_norm_le_mul_rpow_mul_rpow (T₀ := R'.toLinearMap) hR' R'
    (T := (toLp : SobolevH1 I M →L[ℝ] Lp ℝ 2 (riemannianVolume I M)).toLinearMap)
    (C := (D ^ (2⁻¹ : ℝ)).toReal) le_rfl zero_lt_one fun w ↦ ?_
  simp only [ContinuousLinearMap.coe_coe, sub_zero, Real.rpow_one, Real.rpow_zero, mul_one]
  have h : ‖toLp w‖ₑ ≤ D ^ (2⁻¹ : ℝ) * ‖R' w‖ₑ := by
    rw [← ENNReal.rpow_le_rpow_iff two_pos, ENNReal.mul_rpow_of_nonneg _ _ zero_le_two,
      ENNReal.rpow_inv_rpow two_ne_zero]
    exact hle w
  simpa only [ENNReal.toReal_mul, toReal_eNorm] using ENNReal.toReal_mono (by finiteness) h

/-- **Compact Sobolev embeddings on a closed manifold.** On a compact manifold without boundary of
dimension `n > 2` with a continuous Riemannian metric, the Sobolev embedding `H¹(M) → L^q(M)` is a
compact operator for every `1 ≤ q < 2n/(n-2)`. -/
theorem isCompactOperator_toLpOfLE {q : ℝ≥0∞} [Fact (1 ≤ q)] (hn : 2 < finrank ℝ E)
    (hq : q < ENNReal.ofReal (2 * finrank ℝ E / (finrank ℝ E - 2))) :
    IsCompactOperator (toLpOfLE (I := I) (M := M) hn hq.le) := by
  rcases le_or_gt q 2 with hq2 | hq2
  · exact isCompactOperator_toLp.of_forall_ae_eq_of_le hq2 fun w ↦ by rw [coeFn_toLpOfLE]
  -- For `2 < q`, interpolate between `L²` and the critical exponent `pₙ = 2n/(n-2)`:
  -- `1/q = (1 - θ)/2 + θ/pₙ` with `θ = n/2 - n/q ∈ (0, 1)`.
  have hn' : (2 : ℝ) < finrank ℝ E := by exact_mod_cast hn
  set n : ℝ := (finrank ℝ E : ℝ)
  have hq0 : q ≠ ⊤ := hq.ne_top
  set a := q.toReal
  have hqa : q = ENNReal.ofReal a := (ENNReal.ofReal_toReal hq0).symm
  have ha2 : 2 < a := by
    rw [hqa] at hq2
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg zero_le_two).1 (by simpa using hq2)
  have hapn : a < 2 * n / (n - 2) := by
    rw [hqa] at hq
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by linarith)).1 hq
  have hpn1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (2 * n / (n - 2)) :=
    hq2.le.trans' one_le_two |>.trans hq.le
  have : Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal (2 * n / (n - 2))) := ⟨hpn1⟩
  have ha0 : 0 < a := by linarith
  have hθ0 : 0 ≤ n / 2 - n / a := by
    rw [sub_nonneg]
    exact div_le_div_of_nonneg_left (by linarith) zero_lt_two ha2.le
  have hθ1 : n / 2 - n / a < 1 := by
    have h : a * (n - 2) < 2 * n := (lt_div_iff₀ (by linarith)).1 hapn
    have h' : (n - 2) / 2 < n / a := by
      rw [div_lt_div_iff₀ two_pos ha0]
      linarith
    linarith
  refine isCompactOperator_toLp.of_forall_ae_eq_of_interpolation (toLpOfLE hn le_rfl) hθ0 hθ1 ?_
    (fun w ↦ by rw [coeFn_toLpOfLE]) fun w ↦ by rw [coeFn_toLpOfLE, coeFn_toLpOfLE]
  have h : a⁻¹ = (1 - (n / 2 - n / a)) * 2⁻¹ + (n / 2 - n / a) * (2 * n / (n - 2))⁻¹ := by
    field_simp
    ring
  rw [hqa, ← ENNReal.ofReal_inv_of_pos ha0, h,
    ENNReal.ofReal_add (mul_nonneg (by linarith) (by norm_num)) (by positivity),
    ENNReal.ofReal_mul (by linarith), ENNReal.ofReal_mul hθ0, ENNReal.ofReal_inv_of_pos two_pos,
    ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_ofNat]

end TauCeti.Manifold.SobolevH1
