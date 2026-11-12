/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Yamabe.LowerBound
import Mathlib.Topology.Order.DenselyOrdered
import TauCeti.Geometry.Manifold.ContMDiff.Sqrt
import TauCeti.Geometry.Manifold.Riemannian.Gradient.ChainRule
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Support
import TauCeti.MeasureTheory.Integral.AbsRpow
import TauCeti.MeasureTheory.Integral.Bochner.Set
import TauCeti.MeasureTheory.Integral.ContinuousMap

/-!
# Positive smooth test functions for the Yamabe quotient

On a nonempty compact Riemannian manifold of dimension greater than two, the infimum of the
Yamabe quotient over nonzero `C^n` real functions equals its infimum over strictly positive
`C^n` functions, for every `n ≥ 1`. More precisely, every strict upper bound for the quotient of a
signed test function is also realized by a positive test function of the same regularity.

The regularization `v = √(u² + ε)`, for `ε > 0`, decreases the gradient term, while its scalar
curvature term differs from that of `u` by `ε ∫ Scal`. Its critical mass converges to that of
`u`. This argument needs no assumption on the sign of scalar curvature and does not require
regularity of the nodal set of `u`.

These are statements about `C^n` test functions, not an identification of their infimum with
an infimum over a weak Sobolev domain.

## References

* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), §2.
-/

public section

open Bundle Filter MeasureTheory Module TauCeti.Manifold
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.Yamabe

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

variable [FiniteDimensional ℝ E] [T2Space M] [CompactSpace M]
  [IsManifold I ∞ M] [MeasurableSpace M] [BorelSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

private theorem regularized_energy_le (hn : 2 < finrank ℝ E) {u : M → ℝ}
    (hu : ContMDiff I 𝓘(ℝ) 1 u) {ε : ℝ} (hε : 0 < ε) :
    (∫ x, (conformalCoefficient (finrank ℝ E) *
        ‖mgradient I (fun y ↦ Real.sqrt (u y ^ 2 + ε)) x‖ ^ 2 +
        (CovariantDerivative.leviCivitaConnection I M).scalarCurvature x *
          Real.sqrt (u x ^ 2 + ε) ^ 2) ∂riemannianVolume I M) ≤
      (∫ x, (conformalCoefficient (finrank ℝ E) * ‖mgradient I u x‖ ^ 2 +
        (CovariantDerivative.leviCivitaConnection I M).scalarCurvature x * u x ^ 2)
        ∂riemannianVolume I M) +
      ε * ∫ x, (CovariantDerivative.leviCivitaConnection I M).scalarCurvature x
        ∂riemannianVolume I M := by
  let S := (CovariantDerivative.leviCivitaConnection I M).scalarCurvature
  have hS : Continuous S :=
    (CovariantDerivative.leviCivitaConnection I M).contMDiff_scalarCurvature.continuous
  have hv := ((hu.pow 2).add (contMDiff_const (c := ε))).sqrt
    (fun x ↦ (by positivity : 0 < u x ^ 2 + ε).ne')
  have hgrad (x : M) : ‖mgradient I (fun y ↦ Real.sqrt (u y ^ 2 + ε)) x‖ ^ 2 ≤
      ‖mgradient I u x‖ ^ 2 := by
    have hx : 0 < u x ^ 2 + ε := by positivity
    have hd : HasDerivAt (fun t : ℝ ↦ Real.sqrt (t ^ 2 + ε))
        (u x / Real.sqrt (u x ^ 2 + ε)) (u x) := by
      convert (Real.hasDerivAt_sqrt hx.ne').comp (u x)
        ((hasDerivAt_pow 2 (u x)).add_const ε) using 1
      · funext t
        simp
      · ring
    have hg := mgradient_comp_hasDerivAt hd (hu.mdifferentiableAt one_ne_zero)
    simp only [Function.comp_def] at hg
    rw [hg, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    have hs := Real.sq_sqrt hx.le
    have hratio : (u x / Real.sqrt (u x ^ 2 + ε)) ^ 2 ≤ 1 := by
      rw [div_pow, hs, div_le_one hx]
      linarith
    exact mul_le_of_le_one_left (sq_nonneg _) hratio
  have hi : Integrable (fun x ↦ conformalCoefficient (finrank ℝ E) *
      ‖mgradient I u x‖ ^ 2 + S x * u x ^ 2) (riemannianVolume I M) :=
    ((continuous_const.mul (continuous_norm_sq_mgradient hu)).add
      (hS.mul (hu.continuous.pow 2))).integrable_of_compactSpace
  have hi' : Integrable (fun x ↦ conformalCoefficient (finrank ℝ E) *
      ‖mgradient I (fun y ↦ Real.sqrt (u y ^ 2 + ε)) x‖ ^ 2 +
      S x * Real.sqrt (u x ^ 2 + ε) ^ 2) (riemannianVolume I M) :=
    ((continuous_const.mul (continuous_norm_sq_mgradient hv)).add
      (hS.mul (hv.continuous.pow 2))).integrable_of_compactSpace
  have hSi : Integrable S (riemannianVolume I M) := hS.integrable_of_compactSpace
  dsimp only [S] at hi hi' hSi
  rw [← integral_const_mul, ← integral_add hi (hSi.const_mul ε)]
  apply integral_mono hi' (hi.add (hSi.const_mul ε))
  intro x
  dsimp only [Pi.add_apply]
  rw [Real.sq_sqrt (by positivity)]
  have := mul_le_mul_of_nonneg_left (hgrad x) (conformalCoefficient_pos hn).le
  nlinarith

omit [T2Space M] [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
private theorem continuous_regularized_criticalMass (hn : 2 < finrank ℝ E) {u : M → ℝ}
    (hu : Continuous u) :
    Continuous (fun ε : ℝ ↦ ∫ x, |Real.sqrt (u x ^ 2 + ε)| ^
      criticalExponent (finrank ℝ E) ∂riemannianVolume I M) := by
  apply continuous_integral_of_compact_support (K := Set.univ) (riemannianVolume I M)
    isCompact_univ _ (fun _ _ _ ↦ Set.mem_univ _)
  exact (((hu.comp continuous_snd).pow 2 |>.add continuous_fst).sqrt.abs).rpow_const
    (fun _ ↦ Or.inr (criticalExponent_pos hn).le)

/-- On a compact Riemannian manifold of dimension greater than two, every strict upper bound
for the Yamabe quotient of a nonzero `C^n` real function, `n ≥ 1`, is realized by a strictly
positive `C^n` function. No sign condition on scalar curvature is needed. -/
theorem exists_contMDiff_pos_yamabeQuotient_lt (hn : 2 < finrank ℝ E) {n : ℕ∞ω}
    (hn1 : 1 ≤ n) {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ) n u) (hu0 : u ≠ 0)
    {c : ℝ} (hc : yamabeQuotient I u < c) :
    ∃ v : M → ℝ, ContMDiff I 𝓘(ℝ) n v ∧ (∀ x, 0 < v x) ∧ yamabeQuotient I v < c := by
  let μ := riemannianVolume I M
  let S := (CovariantDerivative.leviCivitaConnection I M).scalarCurvature
  let A := ∫ x, (conformalCoefficient (finrank ℝ E) * ‖mgradient I u x‖ ^ 2 +
    S x * u x ^ 2) ∂μ
  let N : ℝ → ℝ := fun ε ↦ ∫ x, |Real.sqrt (u x ^ 2 + ε)| ^
    criticalExponent (finrank ℝ E) ∂μ
  have hN : Continuous N := continuous_regularized_criticalMass hn hu.continuous
  have hN0 : N 0 = ∫ x, |u x| ^ criticalExponent (finrank ℝ E) ∂μ := by
    simp [N, Real.sqrt_sq_eq_abs]
  have hpos : 0 < N 0 := hN0 ▸ integral_abs_rpow_pos hu.continuous hu0
    (criticalExponent_pos hn)
  have hlim : Tendsto (fun ε : ℝ ↦ (A + ε * ∫ x, S x ∂μ) /
      (N ε) ^ (2 / criticalExponent (finrank ℝ E))) (𝓝 0) (𝓝 (yamabeQuotient I u)) := by
    have ht : ContinuousAt (fun ε : ℝ ↦ (A + ε * ∫ x, S x ∂μ) /
        (N ε) ^ (2 / criticalExponent (finrank ℝ E))) 0 :=
      (continuous_const.add (continuous_id.mul continuous_const)).continuousAt.div
        (hN.continuousAt.rpow_const (Or.inl hpos.ne'))
        (Real.rpow_pos_of_pos hpos _).ne'
    have h0 : (A + 0 * ∫ x, S x ∂μ) / (N 0) ^
        (2 / criticalExponent (finrank ℝ E)) = yamabeQuotient I u := by
      rw [zero_mul, add_zero, hN0, yamabeQuotient_def]
    exact h0 ▸ ht.tendsto
  have hev : ∀ᶠ ε : ℝ in 𝓝[>] 0, (A + ε * ∫ x, S x ∂μ) /
      (N ε) ^ (2 / criticalExponent (finrank ℝ E)) < c :=
    (hlim.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds hc)
  have hev' : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), 0 < ε ∧
      (A + ε * ∫ x, S x ∂μ) / (N ε) ^ (2 / criticalExponent (finrank ℝ E)) < c :=
    Filter.Eventually.and self_mem_nhdsWithin hev
  obtain ⟨ε, hε, hbound⟩ := hev'.exists
  refine ⟨fun x ↦ Real.sqrt (u x ^ 2 + ε), ?_, ?_, ?_⟩
  · exact ((hu.pow 2).add (contMDiff_const (c := ε))).sqrt
      (fun x ↦ (by positivity : 0 < u x ^ 2 + ε).ne')
  · intro x
    exact Real.sqrt_pos.2 (by positivity)
  · apply lt_of_le_of_lt _ hbound
    rw [yamabeQuotient_def]
    exact div_le_div_of_nonneg_right (regularized_energy_le hn (hu.of_le hn1) hε)
      (Real.rpow_nonneg (integral_nonneg fun _ ↦ Real.rpow_nonneg (abs_nonneg _) _) _)

/-- On a nonempty compact Riemannian manifold of dimension greater than two, the infimum of the
Yamabe quotient over positive `C^n` functions is its infimum over all nonzero `C^n` real functions,
for every `n ≥ 1`. -/
theorem sInf_yamabeQuotient_pos_eq [Nonempty M] (hn : 2 < finrank ℝ E) {n : ℕ∞ω}
    (hn1 : 1 ≤ n) :
    sInf (yamabeQuotient I '' {u : M → ℝ | ContMDiff I 𝓘(ℝ) n u ∧ ∀ x, 0 < u x}) =
      sInf (yamabeQuotient I '' {u : M → ℝ | ContMDiff I 𝓘(ℝ) n u ∧ u ≠ 0}) := by
  let P := yamabeQuotient I '' {u : M → ℝ | ContMDiff I 𝓘(ℝ) n u ∧ ∀ x, 0 < u x}
  let T := yamabeQuotient I '' {u : M → ℝ | ContMDiff I 𝓘(ℝ) n u ∧ u ≠ 0}
  have hPT : P ⊆ T := by
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨u, ⟨hu.1, fun h ↦ (hu.2 (Classical.arbitrary M)).ne' (congrFun h _)⟩, rfl⟩
  have hP : P.Nonempty := ⟨_, ⟨fun _ ↦ 1, ⟨contMDiff_const, fun _ ↦ one_pos⟩, rfl⟩⟩
  have hbT : BddBelow T := (bddBelow_image_yamabeQuotient (I := I) hn).mono (by
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨u, ⟨hu.1.of_le hn1, hu.2⟩, rfl⟩)
  have hbP := hbT.mono hPT
  apply le_antisymm
  · apply le_csInf (hP.mono hPT)
    rintro _ ⟨u, hu, rfl⟩
    apply le_of_forall_gt_imp_ge_of_dense
    intro c hc
    obtain ⟨v, hv, hvpos, hvc⟩ := exists_contMDiff_pos_yamabeQuotient_lt hn hn1 hu.1 hu.2 hc
    exact (csInf_le hbP ⟨v, ⟨hv, hvpos⟩, rfl⟩).trans hvc.le
  · exact csInf_le_csInf hbT hP hPT

end TauCeti.Yamabe
