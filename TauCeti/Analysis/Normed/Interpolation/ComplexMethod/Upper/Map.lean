/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Interpolation.ComplexMethod.Upper.Basic
import TauCeti.Analysis.Complex.HasPrimitives
import TauCeti.Analysis.Complex.VerticalStrip
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds

/-!
# Functoriality and exact interpolation for Calderón's upper complex method

Continuous linear maps `T₀ : X₀ →L[ℂ] Y₀` and `T₁ : X₁ →L[ℂ] Y₁` between the endpoints of two
compatible couples that agree on the intersection induce a continuous linear map
`UpperComplexMethodSpace.map θ T₀ T₁ h : [X₀, X₁]^θ →L[ℂ] [Y₀, Y₁]^θ` lying over the sum-space lift
`x₀ + x₁ ↦ T₀ x₀ + T₁ x₁` (`UpperComplexMethodSpace.toSum_map`).

When the target endpoints `Y₀` and `Y₁` are complete, Calderón's upper method is an exact
interpolation functor of exponent `θ` (Bergh–Löfström, Theorem 4.1.4): if `‖T₀ x‖ ≤ M₀ * ‖x‖` and
`‖T₁ x‖ ≤ M₁ * ‖x‖` with `M₀, M₁ ≥ 0`, then for `0 < θ < 1`,
`‖map θ T₀ T₁ h u‖ ≤ M₀ ^ (1 - θ) * M₁ ^ θ * ‖u‖` (`UpperComplexMethodSpace.norm_map_le`).
Notice that unlike `[X₀, X₁]_θ`, multiplying an upper strip function `H` pointwise by the analytic
weight `M₀ ^ (z - 1) * M₁ ^ (-z)` alters its complex derivative at `θ`; the exact bound integrates
that weight against `deriv H` by parts via `Complex.wedgeIntegral`.

Functoriality yields left-inverse functoriality for retracts
(`UpperComplexMethodSpace.leftInverse_map`) and invariance under endpoint continuous linear
equivalences (`UpperComplexMethodSpace.mapEquiv`), while quantitative retract norm bounds
(`UpperComplexMethodSpace.norm_le_mul_norm_map_of_leftInverse`) follow from the exact bound
`UpperComplexMethodSpace.norm_map_le` under completeness of the retract's endpoints. For
contractions (`M₀ = M₁ = 1`), the induced map is contractive without completeness assumptions
(`UpperComplexMethodSpace.norm_map_le_of_norm_le`), giving isometric invariance under endpoint
linear isometries (`UpperComplexMethodSpace.norm_mapEquiv`), following the interface of
`TauCeti.Analysis.Normed.Interpolation.ComplexMethod.Basic`.

## References

* A.-P. Calderón, *Intermediate spaces and interpolation, the complex method*, Studia Math. 24
  (1964), 113–190, §§5–6.
* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Grundlehren 223,
  Springer, 1976, §4.1 (Theorem 4.1.4).
* M. Cwikel, *Lecture notes on duality and interpolation spaces*, arXiv:0803.3558 (2008), §2.4.
-/

public noncomputable section

open Asymptotics Bornology Complex Complex.HadamardThreeLines Filter MeasureTheory Set Topology
open scoped BoundedContinuousFunction Interval NNReal

namespace TauCeti

open Complex.HadamardThreeLines

namespace CompatibleCouple

variable {X₀ X₁ V : Type*}
  [NormedAddCommGroup X₀] [NormedSpace ℂ X₀] [NormedAddCommGroup X₁] [NormedSpace ℂ X₁]
  [AddCommGroup V] [Module ℂ V] [TopologicalSpace V] [ContinuousAdd V] [T1Space V]
  {C : CompatibleCouple ℂ X₀ X₁ V}

/-! ### Induced map on upper boundary traces and functoriality -/

section Map

variable {Y₀ Y₁ W : Type*}
  [NormedAddCommGroup Y₀] [NormedSpace ℂ Y₀] [NormedAddCommGroup Y₁] [NormedSpace ℂ Y₁]
  [AddCommGroup W] [Module ℂ W] [TopologicalSpace W] [ContinuousAdd W] [T1Space W]
  {D : CompatibleCouple ℂ Y₀ Y₁ W} {θ : ℝ}
  (T₀ : X₀ →L[ℂ] Y₀) (T₁ : X₁ →L[ℂ] Y₁)
  (h : ∀ x : C.inter, D.fstToSum (T₀ (C.interFst x)) = D.sndToSum (T₁ (C.interSnd x)))

/-- Postcomposition with endpoint operators `(T₀, T₁)` preserves upper strip functions. -/
theorem IsUpperStripFunction.map {G : ℂ → C.SumSpace}
    {q : (offDiag (univ : Set ℝ) →ᵇ X₀) × (offDiag (univ : Set ℝ) →ᵇ X₁)}
    (hG : C.IsUpperStripFunction G q) :
    D.IsUpperStripFunction
      (fun z => C.sumLift (D.fstToSum.comp T₀) (D.sndToSum.comp T₁) h (G z))
      (T₀.compLeftContinuousBounded _ q.1, T₁.compLeftContinuousBounded _ q.2) where
  diffContOnCl :=
    (C.sumLift (D.fstToSum.comp T₀) (D.sndToSum.comp T₁) h).differentiable.comp_diffContOnCl
      hG.diffContOnCl
  exists_norm_le := by
    let S := C.sumLift (D.fstToSum.comp T₀) (D.sndToSum.comp T₁) h
    obtain ⟨K, hK⟩ := hG.exists_norm_le
    refine ⟨‖S‖ * max K 0, fun z hz => (S.le_opNorm (G z)).trans <|
      (mul_le_mul_of_nonneg_left (hK z hz) (norm_nonneg S)).trans ?_⟩
    rw [mul_assoc]; gcongr; exact le_max_left K 0
  sub_mul_I hne := by
    rw [← map_sub, hG.sub_mul_I hne, map_smul]; exact congrArg (_ • ·) (C.sumLift_fstToSum _ _ h _)
  sub_one_add_mul_I hne := by
    rw [← map_sub, hG.sub_one_add_mul_I hne, map_smul]
    exact congrArg (_ • ·) (C.sumLift_sndToSum _ _ h _)

/-- The map of upper boundary difference quotients `(q₀, q₁) ↦ (T₀ ∘ q₀, T₁ ∘ q₁)` induced by
compatible endpoint maps `T₀` and `T₁`. -/
def upperStripTracesMap : C.upperStripTraces →L[ℂ] D.upperStripTraces :=
  LinearMap.mkContinuous
    { toFun g := ⟨(T₀.compLeftContinuousBounded _ g.1.1, T₁.compLeftContinuousBounded _ g.1.2),
        mem_upperStripTraces_iff.2 ⟨_, (C.isUpperStripFunction_upperStripFunction g).map T₀ T₁ h⟩⟩
      map_add' _ _ := Subtype.ext <| Prod.ext (BoundedContinuousFunction.ext fun _ => by simp)
        (BoundedContinuousFunction.ext fun _ => by simp)
      map_smul' _ _ := Subtype.ext <| Prod.ext (BoundedContinuousFunction.ext fun _ => by simp)
        (BoundedContinuousFunction.ext fun _ => by simp) }
    (max ‖T₀‖ ‖T₁‖) fun g => norm_prod_le_iff.2
      ⟨(T₀.norm_compLeftContinuousBounded_apply_le _).trans (mul_le_mul (le_max_left _ _)
          (norm_fst_le g.1) (norm_nonneg _) ((norm_nonneg T₀).trans (le_max_left _ _))),
        (T₁.norm_compLeftContinuousBounded_apply_le _).trans (mul_le_mul (le_max_right _ _)
          (norm_snd_le g.1) (norm_nonneg _) ((norm_nonneg T₀).trans (le_max_left _ _)))⟩

@[simp]
theorem upperStripTracesMap_apply_fst (g : C.upperStripTraces) (p : offDiag (univ : Set ℝ)) :
    (upperStripTracesMap T₀ T₁ h g).1.1 p = T₀ (g.1.1 p) := (rfl)

@[simp]
theorem upperStripTracesMap_apply_snd (g : C.upperStripTraces) (p : offDiag (univ : Set ℝ)) :
    (upperStripTracesMap T₀ T₁ h g).1.2 p = T₁ (g.1.2 p) := (rfl)

theorem norm_upperStripTracesMap_fst_le {M₀ : ℝ} (hM₀ : 0 ≤ M₀) (h₀ : ∀ x, ‖T₀ x‖ ≤ M₀ * ‖x‖)
    (g : C.upperStripTraces) : ‖(upperStripTracesMap T₀ T₁ h g).1.1‖ ≤ M₀ * ‖g‖ :=
  (T₀.norm_compLeftContinuousBounded_apply_le _).trans
    (mul_le_mul (T₀.opNorm_le_bound hM₀ h₀) (norm_fst_le g.1) (norm_nonneg _) hM₀)

theorem norm_upperStripTracesMap_snd_le {M₁ : ℝ} (hM₁ : 0 ≤ M₁) (h₁ : ∀ x, ‖T₁ x‖ ≤ M₁ * ‖x‖)
    (g : C.upperStripTraces) : ‖(upperStripTracesMap T₀ T₁ h g).1.2‖ ≤ M₁ * ‖g‖ :=
  (T₁.norm_compLeftContinuousBounded_apply_le _).trans
    (mul_le_mul (T₁.opNorm_le_bound hM₁ h₁) (norm_snd_le g.1) (norm_nonneg _) hM₁)

/-- Complex derivative evaluation commutes with `upperStripTracesMap`. -/
theorem upperStripDerivEval_upperStripTracesMap (z : ℂ) (g : C.upperStripTraces) :
    D.upperStripDerivEval z (upperStripTracesMap T₀ T₁ h g) =
      C.sumLift (D.fstToSum.comp T₀) (D.sndToSum.comp T₁) h (C.upperStripDerivEval z g) := by
  by_cases hz : z ∈ verticalStrip 0 1
  · rw [upperStripDerivEval_eq_deriv hz ((C.isUpperStripFunction_upperStripFunction g).map T₀ T₁ h),
      C.upperStripDerivEval_apply hz]
    exact ((C.sumLift _ _ h).hasFDerivAt.comp_hasDerivAt z
      ((C.isUpperStripFunction_upperStripFunction g).differentiableAt hz).hasDerivAt).deriv
  · simp [D.upperStripDerivEval_eq_zero hz, C.upperStripDerivEval_eq_zero hz]

/-! ### Boundary integration by parts against `scaleFactor` -/

/-- Integrated-by-parts boundary curve along the vertical line `re z = c`. -/
private def ibpCurve {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (M₀ M₁ c : ℝ)
    (y : ℝ → E) (t : ℝ) : E :=
  scaleFactor M₀ M₁ (c + t * I) • y t -
    ((Real.log M₀ - Real.log M₁ : ℂ) * I) • ∫ u in (0 : ℝ)..t, scaleFactor M₀ M₁ (c + u * I) • y u

private theorem ibpCurve_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (M₀ M₁ c : ℝ)
    {y : ℝ → E} (hy_cont : Continuous y) (t t₀ : ℝ) :
    ibpCurve M₀ M₁ c y t - ibpCurve M₀ M₁ c y t₀ =
      scaleFactor M₀ M₁ (c + t * I) • y t - scaleFactor M₀ M₁ (c + t₀ * I) • y t₀ -
        ((Real.log M₀ - Real.log M₁ : ℂ) * I) •
          ∫ u in t₀..t, scaleFactor M₀ M₁ (c + u * I) • y u := by
  have hsy : Continuous fun u : ℝ => scaleFactor M₀ M₁ (c + u * I) • y u :=
    ((differentiable_scaleFactor M₀ M₁).continuous.comp (by fun_prop)).smul hy_cont
  dsimp only [ibpCurve]
  rw [← intervalIntegral.integral_add_adjacent_intervals (hsy.intervalIntegrable 0 t₀)
    (hsy.intervalIntegrable t₀ t), smul_add]
  abel

/-- One-step quadratic-remainder bound on increments of `ibpCurve`. -/
private theorem norm_ibpCurve_sub_le_quad {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {M₀ M₁ c M : ℝ} (hM : 0 < M) {L : ℝ≥0}
    (hs_norm : ∀ t : ℝ, ‖scaleFactor M₀ M₁ (c + t * I)‖ = M⁻¹) {y : ℝ → E} (hy_cont : Continuous y)
    (hy_lip : ∀ t t₀ : ℝ, ‖y t - y t₀‖ ≤ M * L * |t - t₀|) (t t₀ : ℝ) :
    ‖ibpCurve M₀ M₁ c y t - ibpCurve M₀ M₁ c y t₀‖ ≤
      (L : ℝ) * |t - t₀| + ‖(Real.log M₀ - Real.log M₁ : ℂ)‖ * L * |t - t₀| ^ 2 := by
  let a : ℂ := Real.log M₀ - Real.log M₁
  let s := scaleFactor M₀ M₁
  have hs_cont : Continuous fun u : ℝ => s (c + u * I) :=
    (differentiable_scaleFactor M₀ M₁).continuous.comp (by fun_prop)
  have hrem : ibpCurve M₀ M₁ c y t - ibpCurve M₀ M₁ c y t₀ = s (c + t * I) • (y t - y t₀) -
      (a * I) • ∫ u in t₀..t, s (c + u * I) • (y u - y t₀) := by
    have hdiff_int : (∫ u in t₀..t, s (c + u * I) • (y u - y t₀)) =
        (∫ u in t₀..t, s (c + u * I) • y u) - ∫ u in t₀..t, s (c + u * I) • y t₀ := by
      simp_rw [smul_sub]
      exact intervalIntegral.integral_sub ((hs_cont.smul hy_cont).intervalIntegrable _ _)
        ((hs_cont.smul continuous_const).intervalIntegrable _ _)
    dsimp only [a, s]
    rw [ibpCurve_sub M₀ M₁ c hy_cont, hdiff_int, intervalIntegral.integral_smul_const, smul_sub,
      smul_sub, smul_smul, ← intervalIntegral.integral_const_mul,
      integral_deriv_scaleFactor_add_mul_I, sub_smul]
    abel
  have h1 : ‖s (c + t * I) • (y t - y t₀)‖ ≤ (L : ℝ) * |t - t₀| := by
    rw [norm_smul, hs_norm t, inv_mul_le_iff₀ hM]; exact (hy_lip t t₀).trans_eq (mul_assoc _ _ _)
  have hint_le : ‖∫ u in t₀..t, s (c + u * I) • (y u - y t₀)‖ ≤ (L : ℝ) * |t - t₀| * |t - t₀| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun u hu => by
      rw [norm_smul, hs_norm u, inv_mul_le_iff₀ hM]
      exact ((hy_lip u t₀).trans (mul_le_mul_of_nonneg_left
        (abs_sub_left_of_mem_uIcc (uIoc_subset_uIcc hu)) (by positivity))).trans_eq
        (mul_assoc _ _ _)
  refine hrem ▸ (norm_sub_le _ _).trans (add_le_add h1 ?_)
  rw [norm_smul, norm_mul, norm_I, mul_one]
  exact (mul_le_mul_of_nonneg_left hint_le (norm_nonneg a)).trans_eq (by ring)

/-- `N`-step subdivision upgrades `norm_ibpCurve_sub_le_quad` to exact `L`-Lipschitz continuity. -/
private theorem lipschitzWith_ibpCurve {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {M₀ M₁ c M : ℝ} (hM : 0 < M) {L : ℝ≥0}
    (hs_norm : ∀ t : ℝ, ‖scaleFactor M₀ M₁ (c + t * I)‖ = M⁻¹) {y : ℝ → E} (hy_cont : Continuous y)
    (hy_lip : ∀ t t₀ : ℝ, ‖y t - y t₀‖ ≤ M * L * |t - t₀|) :
    LipschitzWith L (ibpCurve M₀ M₁ c y) := by
  let a : ℂ := Real.log M₀ - Real.log M₁
  let k := ibpCurve M₀ M₁ c y
  refine LipschitzWith.of_dist_le_mul fun t t₀ => ?_
  rw [dist_eq_norm, Real.dist_eq]
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨N, hN⟩ := exists_nat_gt (‖a‖ * L * |t - t₀| ^ 2 / ε)
  have hNpos : 0 < (N : ℝ) := (div_nonneg (by positivity) hε.le).trans_lt hN
  let p : ℕ → ℝ := fun m => t₀ + (m : ℝ) / N * (t - t₀)
  have hdiff (j : ℕ) : |p (j + 1) - p j| = |t - t₀| / N := by
    rw [show p (j + 1) - p j = (t - t₀) / N by dsimp [p]; push_cast; ring,
      abs_div, abs_of_pos hNpos]
  have hpN : p N = t := by simp [p, div_self hNpos.ne']
  have hp0 : p 0 = t₀ := by simp [p]
  have hsum_norm : ‖k t - k t₀‖ ≤ (L : ℝ) * |t - t₀| + ‖a‖ * L * |t - t₀| ^ 2 / N := by
    conv_lhs => rw [← hpN, ← hp0, ← Finset.sum_range_sub (fun j => k (p j)) N]
    refine ((norm_sum_le _ _).trans (Finset.sum_le_sum
      (g := fun _ => (L : ℝ) * (|t - t₀| / N) + ‖a‖ * L * (|t - t₀| / N) ^ 2)
      fun j _ => ?_)).trans_eq ?_
    · simpa [k, a, hdiff j] using
        norm_ibpCurve_sub_le_quad hM hs_norm hy_cont hy_lip (p (j + 1)) (p j)
    · simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, div_pow]
      field_simp [hNpos.ne']
  linarith [(div_lt_iff₀ hNpos).2 (by linarith [(div_lt_iff₀ hε).1 hN, mul_comm ε (N : ℝ)] :
    ‖a‖ * L * |t - t₀| ^ 2 < ε * N)]

/-- The integrated-by-parts upper strip function
`z ↦ scaleFactor M₀ M₁ z • H z - (log M₀ - log M₁) • wedgeIntegral θ z (scaleFactor M₀ M₁ • H)`,
whose complex derivative at `θ` is `scaleFactor M₀ M₁ θ • deriv H θ`. -/
private def ibpStripFunction {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (θ M₀ M₁ : ℝ) (H : ℂ → F) (z : ℂ) : F :=
  scaleFactor M₀ M₁ z • H z -
    (Real.log M₀ - Real.log M₁ : ℂ) • wedgeIntegral θ z fun w => scaleFactor M₀ M₁ w • H w

/-- Sum-space boundary increment identity for `ibpStripFunction`. -/
private theorem wedgeIntegral_ibp_sub_eq {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {θ M₀ M₁ : ℝ} (c : ℝ) {H : ℂ → F}
    (hdH : DiffContOnCl ℂ H (verticalStrip 0 1)) (hθ : (θ : ℂ) ∈ verticalClosedStrip 0 1)
    (ι : E →L[ℂ] F) (hc : c ∈ Icc 0 1) {y : ℝ → E} (hy_cont : Continuous y)
    (hH_eq : ∀ u : ℝ, ι (y u) = H (c + u * I) - H c) (t t₀ : ℝ) :
    ibpStripFunction θ M₀ M₁ H (c + t * I) - ibpStripFunction θ M₀ M₁ H (c + t₀ * I) =
      ι (ibpCurve M₀ M₁ c y t - ibpCurve M₀ M₁ c y t₀) := by
  let a : ℂ := Real.log M₀ - Real.log M₁
  let s := scaleFactor M₀ M₁
  have hH_add (u : ℝ) : H (c + u * I) = ι (y u) + H c := by rw [hH_eq]; abel
  have hs_cont : Continuous fun u : ℝ => s (c + u * I) :=
    (differentiable_scaleFactor M₀ M₁).continuous.comp (by fun_prop)
  have hsy_cont : Continuous fun u : ℝ => s (c + u * I) • y u := hs_cont.smul hy_cont
  have hf : DiffContOnCl ℂ (fun w => s w • H w) (verticalStrip 0 1) :=
    (differentiable_scaleFactor M₀ M₁).diffContOnCl.smul hdH
  have hwedge : wedgeIntegral θ (c + t * I) (fun w => s w • H w) -
      wedgeIntegral θ (c + t₀ * I) (fun w => s w • H w) =
      I • ∫ u in t₀..t, s (c + u * I) • H (c + u * I) := by
    rw [hf.wedgeIntegral_sub_wedgeIntegral_eq_of_mem_verticalClosedStrip zero_lt_one hθ
      (by simpa using hc) (by simpa using hc)]
    simp [wedgeIntegral]
  have hint_split : (a * I) • (∫ u in t₀..t, s (c + u * I) • H (c + u * I)) =
      ι ((a * I) • ∫ u in t₀..t, s (c + u * I) • y u) +
        (s (c + t * I) - s (c + t₀ * I)) • H c := by
    have hi1 : IntervalIntegrable (fun u => ι (s (c + u * I) • y u)) volume t₀ t :=
      (ι.continuous.comp hsy_cont).intervalIntegrable _ _
    have hi2 : IntervalIntegrable (fun u => s (c + u * I) • H c) volume t₀ t :=
      (hs_cont.smul continuous_const).intervalIntegrable _ _
    simp_rw [hH_add, smul_add, ← map_smul]
    rw [intervalIntegral.integral_add hi1 hi2,
      ι.intervalIntegral_comp_comm (hsy_cont.intervalIntegrable _ _),
      intervalIntegral.integral_smul_const, smul_add, ← map_smul, ← smul_assoc, smul_eq_mul,
      ← intervalIntegral.integral_const_mul]
    dsimp only [a, s]
    rw [integral_deriv_scaleFactor_add_mul_I]
  change (s (c + t * I) • H (c + t * I) - a • wedgeIntegral θ (c + t * I) fun w => s w • H w) -
      (s (c + t₀ * I) • H (c + t₀ * I) - a • wedgeIntegral θ (c + t₀ * I) fun w => s w • H w) = _
  rw [sub_sub_sub_comm, ← smul_sub, hwedge, smul_smul, hint_split, hH_add t, hH_add t₀,
    ibpCurve_sub M₀ M₁ c hy_cont]
  simp only [a, s, smul_add, sub_smul, map_sub, map_smul]; abel

namespace UpperComplexMethodSpace

variable (θ) in
/-- The continuous linear map `[X₀, X₁]^θ →L[ℂ] [Y₀, Y₁]^θ` induced by continuous linear maps
`T₀ : X₀ →L[ℂ] Y₀` and `T₁ : X₁ →L[ℂ] Y₁` agreeing on `X₀ ∩ X₁`. -/
def map : C.UpperComplexMethodSpace θ →L[ℂ] D.UpperComplexMethodSpace θ :=
  lift ((mk θ).comp (upperStripTracesMap T₀ T₁ h)) fun g hg => by
    rw [ContinuousLinearMap.comp_apply, ← map_zero (mk (C := D) θ), mk_eq_mk_iff,
      upperStripDerivEval_upperStripTracesMap, hg, map_zero, map_zero]

@[simp]
theorem map_mk (g : C.upperStripTraces) :
    map θ T₀ T₁ h (mk θ g) = mk θ (upperStripTracesMap T₀ T₁ h g) := by simp [map]

/-- The induced map lies over `x₀ + x₁ ↦ T₀ x₀ + T₁ x₁` on the sum spaces. -/
@[simp]
theorem toSum_map (u : C.UpperComplexMethodSpace θ) :
    toSum (map θ T₀ T₁ h u) = C.sumLift (D.fstToSum.comp T₀) (D.sndToSum.comp T₁) h (toSum u) := by
  obtain ⟨g, rfl⟩ := mk_surjective u
  rw [map_mk, toSum_mk, toSum_mk, upperStripDerivEval_upperStripTracesMap]

theorem map_id
    (h : ∀ x : C.inter, C.fstToSum (ContinuousLinearMap.id ℂ X₀ (C.interFst x)) =
      C.sndToSum (ContinuousLinearMap.id ℂ X₁ (C.interSnd x))) :
    map θ (ContinuousLinearMap.id ℂ X₀) (ContinuousLinearMap.id ℂ X₁) h =
      ContinuousLinearMap.id ℂ (C.UpperComplexMethodSpace θ) := by
  refine ContinuousLinearMap.ext fun u => ?_
  obtain ⟨g, rfl⟩ := mk_surjective u
  rw [map_mk, ContinuousLinearMap.id_apply]
  exact congrArg (mk θ) (Subtype.ext <| Prod.ext
    (BoundedContinuousFunction.ext fun _ => rfl) (BoundedContinuousFunction.ext fun _ => rfl))

section Comp

variable {Z₀ Z₁ U : Type*}
  [NormedAddCommGroup Z₀] [NormedSpace ℂ Z₀] [NormedAddCommGroup Z₁] [NormedSpace ℂ Z₁]
  [AddCommGroup U] [Module ℂ U] [TopologicalSpace U] [ContinuousAdd U] [T1Space U]
  {E : CompatibleCouple ℂ Z₀ Z₁ U} (S₀ : Y₀ →L[ℂ] Z₀) (S₁ : Y₁ →L[ℂ] Z₁)
  (hS : ∀ x : D.inter, E.fstToSum (S₀ (D.interFst x)) = E.sndToSum (S₁ (D.interSnd x)))
  (hST : ∀ x : C.inter,
    E.fstToSum (S₀.comp T₀ (C.interFst x)) = E.sndToSum (S₁.comp T₁ (C.interSnd x)))

theorem map_comp :
    map θ (S₀.comp T₀) (S₁.comp T₁) hST = (map θ S₀ S₁ hS).comp (map θ T₀ T₁ h) := by
  refine ContinuousLinearMap.ext fun u => ?_
  obtain ⟨g, rfl⟩ := mk_surjective u
  rw [map_mk, ContinuousLinearMap.comp_apply, map_mk, map_mk]
  exact congrArg (mk θ) (Subtype.ext <| Prod.ext
    (BoundedContinuousFunction.ext fun _ => rfl) (BoundedContinuousFunction.ext fun _ => rfl))

end Comp

/-- For `0 < θ < 1`, `UpperComplexMethodSpace.map` commutes with the inclusions of the
intersections. -/
theorem map_ofInter (hθ : θ ∈ Ioo 0 1) {x : C.inter} {y : D.inter}
    (hy : D.interFst y = T₀ (C.interFst x)) : map θ T₀ T₁ h (ofInter θ x) = ofInter θ y := by
  ext; rw [toSum_map, toSum_ofInter hθ, toSum_ofInter hθ, hy]; exact C.sumLift_fstToSum _ _ h _

/-- Without completeness hypotheses, `UpperComplexMethodSpace.map` is bounded by `max M₀ M₁`. -/
theorem norm_map_le_max {M₀ M₁ : ℝ} (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁)
    (h₀ : ∀ x, ‖T₀ x‖ ≤ M₀ * ‖x‖) (h₁ : ∀ x, ‖T₁ x‖ ≤ M₁ * ‖x‖)
    (u : C.UpperComplexMethodSpace θ) :
    ‖map θ T₀ T₁ h u‖ ≤ max M₀ M₁ * ‖u‖ := by
  set M := max M₀ M₁
  have hM : 0 ≤ M := hM₀.trans (le_max_left _ _)
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨g, rfl, hg⟩ := norm_lt_iff.1
    (lt_add_of_pos_right ‖u‖ (div_pos hε (by linarith : 0 < M + 1)))
  have htrace : ‖upperStripTracesMap T₀ T₁ h g‖ ≤ M * ‖g‖ := max_le
    ((norm_upperStripTracesMap_fst_le T₀ T₁ h hM₀ h₀ g).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg g)))
    ((norm_upperStripTracesMap_snd_le T₀ T₁ h hM₁ h₁ g).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg g)))
  rw [map_mk]
  exact ((norm_mk_le _).trans (htrace.trans (mul_le_mul_of_nonneg_left hg.le hM))).trans
    (by nlinarith [mul_div_cancel₀ ε (by linarith : M + 1 ≠ 0),
      div_pos hε (by linarith : 0 < M + 1)])

/-- Contractive endpoint maps induce a contractive map on `[X₀, X₁]^θ`, without completeness
assumptions. -/
theorem norm_map_le_of_norm_le (h₀ : ∀ x, ‖T₀ x‖ ≤ ‖x‖) (h₁ : ∀ x, ‖T₁ x‖ ≤ ‖x‖)
    (u : C.UpperComplexMethodSpace θ) : ‖map θ T₀ T₁ h u‖ ≤ ‖u‖ := by
  simpa using norm_map_le_max T₀ T₁ h zero_le_one zero_le_one
    (fun x => by simpa using h₀ x) (fun x => by simpa using h₁ x) u

/-! ### Exact interpolation of exponent `θ` (Bergh–Löfström Theorem 4.1.4) -/

/-- Quadratic-exponential growth of `ibpStripFunction` on the open strip. -/
private theorem isBigO_exp_sq_ibp (hθ : θ ∈ Ioo 0 1) (M₀ M₁ : ℝ) (qY : D.upperStripTraces) :
    ∃ A B : ℝ, ibpStripFunction θ M₀ M₁ (D.upperStripFunction qY)
      =O[cobounded ℂ ⊓ 𝓟 (verticalStrip 0 1)] fun w => Real.exp (B * ‖w‖ ^ A) := by
  let a : ℂ := Real.log M₀ - Real.log M₁
  let s := scaleFactor M₀ M₁
  let H := D.upperStripFunction qY
  set S := Real.exp (|Real.log M₀| + |Real.log M₁|)
  have hθ_norm : ‖(θ : ℂ)‖ ≤ 1 := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hθ.1.le] using hθ.2.le
  refine ⟨2, S * ‖qY‖ + ‖a‖ * (12 * S * ‖qY‖) + 1, IsBigO.of_norm_eventuallyLE ?_⟩
  filter_upwards [(tendsto_norm_cobounded_atTop.eventually (eventually_ge_atTop 1)).filter_mono
      inf_le_left,
    (eventually_mem_principal (verticalStrip 0 1)).filter_mono inf_le_right] with z hz1 hz
  have hz_cl := verticalStrip_subset_verticalClosedStrip 0 1 hz
  have hsH {w : ℂ} (hw : w ∈ verticalClosedStrip 0 1) : ‖s w • H w‖ ≤ S * ‖qY‖ * ‖w‖ := by
    rw [norm_smul]; exact (mul_le_mul (norm_scaleFactor_le hw) (D.norm_upperStripFunction_le qY w)
      (norm_nonneg _) (by positivity)).trans_eq (mul_assoc _ _ _).symm
  have hprod : (‖(θ : ℂ)‖ + ‖z - θ‖) * ‖z - θ‖ ≤ 6 * ‖z‖ ^ 2 := by
    nlinarith [norm_sub_le z θ, norm_nonneg (z - θ)]
  have hw : ‖wedgeIntegral θ z (fun w => s w • H w)‖ ≤ 12 * S * ‖qY‖ * ‖z‖ ^ 2 :=
    (TauCeti.norm_wedgeIntegral_le_of_norm_le_mul_norm fun u hu =>
      hsH (ordConnected_Icc.uIcc_subset ⟨hθ.1.le, hθ.2.le⟩ hz_cl (by simpa using hu.1))).trans
      (((mul_assoc _ _ _).le.trans (mul_le_mul_of_nonneg_left hprod (by positivity))).trans_eq
        (by ring))
  have h1 : ‖s z • H z‖ ≤ S * ‖qY‖ * ‖z‖ ^ 2 :=
    (hsH hz_cl).trans (mul_le_mul_of_nonneg_left (by nlinarith) (by positivity))
  have h2 : ‖a • wedgeIntegral θ z (fun w => s w • H w)‖ ≤ ‖a‖ * (12 * S * ‖qY‖) * ‖z‖ ^ 2 := by
    rw [norm_smul, mul_assoc]; exact mul_le_mul_of_nonneg_left hw (norm_nonneg a)
  rw [Real.rpow_two]; dsimp only [ibpStripFunction]
  exact (((norm_sub_le _ _).trans (add_le_add h1 h2)).trans (by nlinarith [sq_nonneg ‖z‖])).trans
    ((le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _))

private theorem norm_scaleFactor_smul_map_mk_le [CompleteSpace Y₀] [CompleteSpace Y₁]
    (hθ : θ ∈ Ioo 0 1) {M₀ M₁ : ℝ} (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
    (h₀ : ∀ x, ‖T₀ x‖ ≤ M₀ * ‖x‖) (h₁ : ∀ x, ‖T₁ x‖ ≤ M₁ * ‖x‖) (g : C.upperStripTraces) :
    ‖scaleFactor M₀ M₁ θ • map θ T₀ T₁ h (mk θ g)‖ ≤ ‖g‖ := by
  have hθ_open : (θ : ℂ) ∈ verticalStrip 0 1 := by simpa using hθ
  have hθ_cl : (θ : ℂ) ∈ verticalClosedStrip 0 1 := ⟨hθ.1.le, hθ.2.le⟩
  let qY := upperStripTracesMap T₀ T₁ h g
  let H := D.upperStripFunction qY
  have hH : D.IsUpperStripFunction H qY := D.isUpperStripFunction_upperStripFunction qY
  let a : ℂ := Real.log M₀ - Real.log M₁
  let s := scaleFactor M₀ M₁
  -- 1. Holomorphy on the open strip and continuity on the closed strip for `ibpStripFunction`.
  have hf : DiffContOnCl ℂ (fun w => s w • H w) (verticalStrip 0 1) :=
    (differentiable_scaleFactor M₀ M₁).diffContOnCl.smul hH.diffContOnCl
  have hdK : DiffContOnCl ℂ (ibpStripFunction θ M₀ M₁ H) (verticalStrip 0 1) :=
    hf.sub ((hf.diffContOnCl_wedgeIntegral_verticalStrip zero_lt_one hθ_cl).const_smul a)
  -- 2. Differentiating `ibpStripFunction` at `θ` cancels `deriv scaleFactor` with `wedgeIntegral`.
  have hderivK : toSum (s θ • map θ T₀ T₁ h (mk θ g)) = deriv (ibpStripFunction θ M₀ M₁ H) θ := by
    have hKθ : HasDerivAt (ibpStripFunction θ M₀ M₁ H) (s θ • deriv H θ) θ := by
      change HasDerivAt (fun z => s z • H z - a • wedgeIntegral θ z fun w => s w • H w) _ θ
      convert ((hasDerivAt_scaleFactor M₀ M₁ θ).smul (hH.differentiableAt hθ_open).hasDerivAt).sub
        ((hf.hasDerivAt_wedgeIntegral_verticalStrip zero_lt_one hθ_cl hθ_open).const_smul a) using 1
      rw [smul_smul]; abel
    rw [hKθ.deriv, map_smul, map_mk, toSum_mk, D.upperStripDerivEval_apply hθ_open]
  -- 3. `‖g‖`-Lipschitz bounds for the integrated-by-parts boundary curves on `re = 0` and `re = 1`.
  have hlip₀ := lipschitzWith_ibpCurve (M₀ := M₀) (M₁ := M₁) (c := 0) hM₀ (L := ‖g‖₊)
    (fun t => by simpa using norm_scaleFactor_mul_I (M₁ := M₁) hM₀ t)
    hH.lipschitzWith_pinnedCurve_fst.continuous fun t t₀ =>
      (hH.norm_pinnedCurve_fst_sub_le t t₀).trans (mul_le_mul_of_nonneg_right
        (norm_upperStripTracesMap_fst_le T₀ T₁ h hM₀.le h₀ g) (abs_nonneg _))
  have hlip₁ := lipschitzWith_ibpCurve (M₀ := M₀) (M₁ := M₁) (c := 1) hM₁ (L := ‖g‖₊)
    (fun t => by simpa using norm_scaleFactor_one_add_mul_I (M₀ := M₀) hM₁ t)
    hH.lipschitzWith_pinnedCurve_snd.continuous fun t t₀ =>
      (hH.norm_pinnedCurve_snd_sub_le t t₀).trans (mul_le_mul_of_nonneg_right
        (norm_upperStripTracesMap_snd_le T₀ T₁ h hM₁.le h₁ g) (abs_nonneg _))
  -- 4. Identify boundary increments via `wedgeIntegral_ibp_sub_eq` and conclude.
  simpa using norm_le_of_lipschitz hθ hdK (isBigO_exp_sq_ibp hθ M₀ M₁ qY) hlip₀ hlip₁
    (fun t t₀ => by
      simpa using wedgeIntegral_ibp_sub_eq 0 hH.diffContOnCl hθ_cl D.fstToSum ⟨le_rfl, zero_le_one⟩
        hH.lipschitzWith_pinnedCurve_fst.continuous
        (fun u => by simpa using hH.fstToSum_pinnedCurve u) t t₀)
    (fun t t₀ => by
      simpa using wedgeIntegral_ibp_sub_eq 1 hH.diffContOnCl hθ_cl D.sndToSum ⟨zero_le_one, le_rfl⟩
        hH.lipschitzWith_pinnedCurve_snd.continuous hH.sndToSum_pinnedCurve t t₀)
    hderivK

private theorem norm_map_le_of_pos [CompleteSpace Y₀] [CompleteSpace Y₁] (hθ : θ ∈ Ioo 0 1)
    {M₀ M₁ : ℝ} (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
    (h₀ : ∀ x, ‖T₀ x‖ ≤ M₀ * ‖x‖) (h₁ : ∀ x, ‖T₁ x‖ ≤ M₁ * ‖x‖)
    (u : C.UpperComplexMethodSpace θ) :
    ‖map θ T₀ T₁ h u‖ ≤ M₀ ^ (1 - θ) * M₁ ^ θ * ‖u‖ := by
  set K := M₀ ^ (1 - θ) * M₁ ^ θ
  have hKpos : 0 < K := by positivity
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨g, rfl, hg⟩ := norm_lt_iff.1 (lt_add_of_pos_right ‖u‖ (div_pos hε hKpos))
  calc ‖map θ T₀ T₁ h (mk θ g)‖
      = K * ‖scaleFactor M₀ M₁ θ • map θ T₀ T₁ h (mk θ g)‖ := by
        rw [norm_smul, ← mul_assoc, mul_comm K, norm_scaleFactor_mul_rpow hM₀ hM₁, one_mul]
    _ ≤ K * (‖mk θ g‖ + ε / K) := mul_le_mul_of_nonneg_left
        ((norm_scaleFactor_smul_map_mk_le T₀ T₁ h hθ hM₀ hM₁ h₀ h₁ g).trans hg.le) hKpos.le
    _ = K * ‖mk θ g‖ + ε := by rw [mul_add, mul_div_cancel₀ _ hKpos.ne']

/-- **Bergh–Löfström Theorem 4.1.4 (exact interpolation for Calderón's upper method).** When `Y₀`
and `Y₁` are complete, if `‖T₀ x‖ ≤ M₀ * ‖x‖` and `‖T₁ x‖ ≤ M₁ * ‖x‖` with `M₀, M₁ ≥ 0`, then for
`0 < θ < 1` the induced map `[X₀, X₁]^θ → [Y₀, Y₁]^θ` satisfies
`‖map θ T₀ T₁ h u‖ ≤ M₀ ^ (1 - θ) * M₁ ^ θ * ‖u‖`. -/
theorem norm_map_le [CompleteSpace Y₀] [CompleteSpace Y₁] (hθ : θ ∈ Ioo 0 1) {M₀ M₁ : ℝ}
    (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁) (h₀ : ∀ x, ‖T₀ x‖ ≤ M₀ * ‖x‖) (h₁ : ∀ x, ‖T₁ x‖ ≤ M₁ * ‖x‖)
    (u : C.UpperComplexMethodSpace θ) :
    ‖map θ T₀ T₁ h u‖ ≤ M₀ ^ (1 - θ) * M₁ ^ θ * ‖u‖ :=
  le_rpow_mul_rpow_mul_of_forall_pos ⟨hθ.1.le, hθ.2.le⟩ fun _ hε =>
    norm_map_le_of_pos T₀ T₁ h hθ (by positivity) (by positivity)
      (fun x => (h₀ x).trans (by gcongr; linarith))
      (fun x => (h₁ x).trans (by gcongr; linarith)) u

/-- Operator-norm form of `UpperComplexMethodSpace.norm_map_le`. -/
theorem opNorm_map_le [CompleteSpace Y₀] [CompleteSpace Y₁] (hθ : θ ∈ Ioo 0 1) {M₀ M₁ : ℝ}
    (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁) (h₀ : ∀ x, ‖T₀ x‖ ≤ M₀ * ‖x‖) (h₁ : ∀ x, ‖T₁ x‖ ≤ M₁ * ‖x‖) :
    ‖map θ T₀ T₁ h‖ ≤ M₀ ^ (1 - θ) * M₁ ^ θ :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) (norm_map_le T₀ T₁ h hθ hM₀ hM₁ h₀ h₁)

/-- Exact interpolation of exponent `θ` in terms of endpoint operator norms:
`‖map θ T₀ T₁ h‖ ≤ ‖T₀‖ ^ (1 - θ) * ‖T₁‖ ^ θ` for `0 < θ < 1`. -/
theorem opNorm_map_le_opNorm [CompleteSpace Y₀] [CompleteSpace Y₁] (hθ : θ ∈ Ioo 0 1) :
    ‖map θ T₀ T₁ h‖ ≤ ‖T₀‖ ^ (1 - θ) * ‖T₁‖ ^ θ :=
  opNorm_map_le T₀ T₁ h hθ (norm_nonneg _) (norm_nonneg _) T₀.le_opNorm T₁.le_opNorm

end UpperComplexMethodSpace

end Map

/-! ### Retracts and isomorphisms of couples -/

section RetractAndEquiv

variable {Y₀ Y₁ W : Type*}
  [NormedAddCommGroup Y₀] [NormedSpace ℂ Y₀] [NormedAddCommGroup Y₁] [NormedSpace ℂ Y₁]
  [AddCommGroup W] [Module ℂ W] [TopologicalSpace W] [ContinuousAdd W] [T1Space W]
  {D : CompatibleCouple ℂ Y₀ Y₁ W} {θ : ℝ}

namespace UpperComplexMethodSpace

section Retract

variable (I₀ : X₀ →L[ℂ] Y₀) (I₁ : X₁ →L[ℂ] Y₁)
  (hI : ∀ x : C.inter, D.fstToSum (I₀ (C.interFst x)) = D.sndToSum (I₁ (C.interSnd x)))
  (P₀ : Y₀ →L[ℂ] X₀) (P₁ : Y₁ →L[ℂ] X₁)
  (hP : ∀ y : D.inter, C.fstToSum (P₀ (D.interFst y)) = C.sndToSum (P₁ (D.interSnd y)))

/-- **Retracts.** Left-inverse endpoint operators induce a left inverse on `[X₀, X₁]^θ`. -/
theorem leftInverse_map (hPI₀ : Function.LeftInverse P₀ I₀) (hPI₁ : Function.LeftInverse P₁ I₁) :
    Function.LeftInverse (map θ P₀ P₁ hP) (map θ I₀ I₁ hI) := fun u => by
  ext; rw [toSum_map, toSum_map]; exact leftInverse_sumLift I₀ I₁ hI P₀ P₁ hP hPI₀ hPI₁ _

include hP in
/-- **Retract norm bound.** When `X₀` and `X₁` are complete, if `(P₀, P₁)` is a left inverse to
`(I₀, I₁)` with `‖P₀ y‖ ≤ N₀ * ‖y‖` and `‖P₁ y‖ ≤ N₁ * ‖y‖`, then
`‖u‖ ≤ N₀ ^ (1 - θ) * N₁ ^ θ * ‖map θ I₀ I₁ hI u‖`. -/
theorem norm_le_mul_norm_map_of_leftInverse [CompleteSpace X₀] [CompleteSpace X₁]
    (hPI₀ : Function.LeftInverse P₀ I₀) (hPI₁ : Function.LeftInverse P₁ I₁)
    {N₀ N₁ : ℝ} (hN₀ : 0 ≤ N₀) (hN₁ : 0 ≤ N₁)
    (h₀ : ∀ y, ‖P₀ y‖ ≤ N₀ * ‖y‖) (h₁ : ∀ y, ‖P₁ y‖ ≤ N₁ * ‖y‖)
    (u : C.UpperComplexMethodSpace θ) :
    ‖u‖ ≤ N₀ ^ (1 - θ) * N₁ ^ θ * ‖map θ I₀ I₁ hI u‖ := by
  by_cases hθ : θ ∈ Ioo 0 1
  · conv_lhs => rw [← leftInverse_map I₀ I₁ hI P₀ P₁ hP hPI₀ hPI₁ u]
    exact norm_map_le P₀ P₁ hP hθ hN₀ hN₁ h₀ h₁ _
  · simp [eq_zero_of_notMem hθ u]

end Retract

section Equiv

variable (e₀ : X₀ ≃L[ℂ] Y₀) (e₁ : X₁ ≃L[ℂ] Y₁)
  (h : ∀ x : C.inter, D.fstToSum (e₀ (C.interFst x)) = D.sndToSum (e₁ (C.interSnd x)))
  (hsymm : ∀ y : D.inter,
    C.fstToSum (e₀.symm (D.interFst y)) = C.sndToSum (e₁.symm (D.interSnd y)))

variable (θ) in
/-- **Invariance under endpoint isomorphisms.** Compatible continuous linear equivalences of the
endpoints induce a continuous linear equivalence `[X₀, X₁]^θ ≃L[ℂ] [Y₀, Y₁]^θ` lying over the
sum-space lift. -/
def mapEquiv : C.UpperComplexMethodSpace θ ≃L[ℂ] D.UpperComplexMethodSpace θ :=
  ContinuousLinearEquiv.equivOfInverse (map θ e₀ e₁ h) (map θ e₀.symm e₁.symm hsymm)
    (leftInverse_map _ _ h _ _ hsymm e₀.symm_apply_apply e₁.symm_apply_apply)
    (leftInverse_map _ _ hsymm _ _ h e₀.apply_symm_apply e₁.apply_symm_apply)

theorem mapEquiv_apply (u : C.UpperComplexMethodSpace θ) :
    mapEquiv θ e₀ e₁ h hsymm u = map θ e₀ e₁ h u := (rfl)

theorem mapEquiv_symm_apply (v : D.UpperComplexMethodSpace θ) :
    (mapEquiv θ e₀ e₁ h hsymm).symm v = map θ e₀.symm e₁.symm hsymm v := (rfl)

@[simp]
theorem toSum_mapEquiv (u : C.UpperComplexMethodSpace θ) :
    toSum (mapEquiv θ e₀ e₁ h hsymm u) =
      C.sumLift (D.fstToSum.comp (e₀ : X₀ →L[ℂ] Y₀)) (D.sndToSum.comp (e₁ : X₁ →L[ℂ] Y₁)) h
        (toSum u) := toSum_map _ _ h u

@[simp]
theorem toSum_mapEquiv_symm (v : D.UpperComplexMethodSpace θ) :
    toSum ((mapEquiv θ e₀ e₁ h hsymm).symm v) =
      D.sumLift (C.fstToSum.comp (e₀.symm : Y₀ →L[ℂ] X₀))
        (C.sndToSum.comp (e₁.symm : Y₁ →L[ℂ] X₁)) hsymm (toSum v) := toSum_map _ _ hsymm v

/-- Isometric endpoint equivalences induce an isometry `[X₀, X₁]^θ ≃ [Y₀, Y₁]^θ`, without
completeness assumptions. -/
theorem norm_mapEquiv (h₀ : ∀ x, ‖e₀ x‖ = ‖x‖) (h₁ : ∀ x, ‖e₁ x‖ = ‖x‖)
    (u : C.UpperComplexMethodSpace θ) : ‖mapEquiv θ e₀ e₁ h hsymm u‖ = ‖u‖ := by
  refine le_antisymm (norm_map_le_of_norm_le _ _ h (fun x => (h₀ x).le) (fun x => (h₁ x).le) u)
    ?_
  conv_lhs => rw [← (mapEquiv θ e₀ e₁ h hsymm).symm_apply_apply u, mapEquiv_symm_apply]
  refine norm_map_le_of_norm_le _ _ hsymm (fun y => ?_) (fun y => ?_) _
  · rw [ContinuousLinearEquiv.coe_coe, ← h₀ (e₀.symm y), ContinuousLinearEquiv.apply_symm_apply]
  · rw [ContinuousLinearEquiv.coe_coe, ← h₁ (e₁.symm y), ContinuousLinearEquiv.apply_symm_apply]

end Equiv

end UpperComplexMethodSpace

end RetractAndEquiv

end CompatibleCouple

end TauCeti
