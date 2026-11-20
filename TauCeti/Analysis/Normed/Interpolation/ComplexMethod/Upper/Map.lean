/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Interpolation.ComplexMethod.Upper.Basic
import TauCeti.Analysis.Complex.HasPrimitives
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds

/-!
# Functoriality and exact interpolation for Calderón's upper complex method

Compatible continuous linear endpoint maps `T₀ : X₀ →L[ℂ] Y₀` and `T₁ : X₁ →L[ℂ] Y₁` induce
`UpperComplexMethodSpace.map θ T₀ T₁ h : [X₀, X₁]^θ →L[ℂ] [Y₀, Y₁]^θ` lying over the sum-space lift
`x₀ + x₁ ↦ T₀ x₀ + T₁ x₁` (`UpperComplexMethodSpace.toSum_map`).

When `Y₀` and `Y₁` are complete, Calderón's upper method is an exact interpolation functor of
exponent `θ` (Bergh–Löfström, Theorem 4.1.4): `‖map θ T₀ T₁ h u‖ ≤ M₀ ^ (1 - θ) * M₁ ^ θ * ‖u‖`
(`UpperComplexMethodSpace.norm_map_le`), proved by integrating the exponential gauge weight
`scaleFactor M₀ M₁` against `deriv H` by parts via `Complex.wedgeIntegral`. Functoriality also gives
retracts (`UpperComplexMethodSpace.leftInverse_map`,
`UpperComplexMethodSpace.norm_le_mul_norm_map_of_leftInverse`), endpoint continuous linear
equivalences (`UpperComplexMethodSpace.mapEquiv`), and completeness-free contractivity/isometry
(`UpperComplexMethodSpace.norm_map_le_of_norm_le`, `UpperComplexMethodSpace.norm_mapEquiv`).

## References

* A.-P. Calderón, *Intermediate spaces and interpolation, the complex method*, Studia Math. 24
  (1964), 113–190, §§5–6.
* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Springer, 1976, §4.1.
* M. Cwikel, *Lecture notes on duality and interpolation spaces*, arXiv:0803.3558 (2008), §2.4.
-/

public noncomputable section

open Asymptotics Bornology Complex Complex.HadamardThreeLines Filter MeasureTheory Set Topology
open TauCeti.Complex.HadamardThreeLines
open scoped BoundedContinuousFunction Interval NNReal

namespace TauCeti.CompatibleCouple

variable {X₀ X₁ V Y₀ Y₁ W : Type*}
  [NormedAddCommGroup X₀] [NormedSpace ℂ X₀] [NormedAddCommGroup X₁] [NormedSpace ℂ X₁]
  [AddCommGroup V] [Module ℂ V] [TopologicalSpace V] [ContinuousAdd V] [T1Space V]
  {C : CompatibleCouple ℂ X₀ X₁ V}
  [NormedAddCommGroup Y₀] [NormedSpace ℂ Y₀] [NormedAddCommGroup Y₁] [NormedSpace ℂ Y₁]
  [AddCommGroup W] [Module ℂ W] [TopologicalSpace W] [ContinuousAdd W] [T1Space W]
  {D : CompatibleCouple ℂ Y₀ Y₁ W} {θ : ℝ}

/-! ### Induced map on upper boundary traces and functoriality -/

section Map

variable (T₀ : X₀ →L[ℂ] Y₀) (T₁ : X₁ →L[ℂ] Y₁)
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
  (((T₀.compLeftContinuousBounded _).prodMap (T₁.compLeftContinuousBounded _)).domRestrict
    C.upperStripTraces).codRestrict D.upperStripTraces fun g =>
      mem_upperStripTraces_iff.2 ⟨_, (C.isUpperStripFunction_upperStripFunction g).map T₀ T₁ h⟩

@[simp] theorem coe_upperStripTracesMap_fst (g : C.upperStripTraces) :
    (upperStripTracesMap T₀ T₁ h g).val.1 = T₀.compLeftContinuousBounded _ g.val.1 := (rfl)

@[simp] theorem coe_upperStripTracesMap_snd (g : C.upperStripTraces) :
    (upperStripTracesMap T₀ T₁ h g).val.2 = T₁.compLeftContinuousBounded _ g.val.2 := (rfl)

theorem upperStripTracesMap_apply_fst (g : C.upperStripTraces) (p : offDiag (univ : Set ℝ)) :
    (upperStripTracesMap T₀ T₁ h g).val.1 p = T₀ (g.val.1 p) := by simp

theorem upperStripTracesMap_apply_snd (g : C.upperStripTraces) (p : offDiag (univ : Set ℝ)) :
    (upperStripTracesMap T₀ T₁ h g).val.2 p = T₁ (g.val.2 p) := by simp

theorem isUpperStripFunction_upperStripTracesMap (g : C.upperStripTraces) :
    D.IsUpperStripFunction
      (fun z => C.sumLift (D.fstToSum.comp T₀) (D.sndToSum.comp T₁) h (C.upperStripFunction g z))
      (upperStripTracesMap T₀ T₁ h g) := by
  have := (C.isUpperStripFunction_upperStripFunction g).map T₀ T₁ h
  rwa [← coe_upperStripTracesMap_fst T₀ T₁ h g, ← coe_upperStripTracesMap_snd T₀ T₁ h g,
    Prod.mk.eta] at this

theorem upperStripFunction_upperStripTracesMap (g : C.upperStripTraces) (z : ℂ) :
    D.upperStripFunction (upperStripTracesMap T₀ T₁ h g) z =
      C.sumLift (D.fstToSum.comp T₀) (D.sndToSum.comp T₁) h (C.upperStripFunction g z) := by
  by_cases hz : z ∈ verticalClosedStrip 0 1
  · simpa using upperStripFunction_eq (isUpperStripFunction_upperStripTracesMap T₀ T₁ h g) hz
  · simp [D.upperStripFunction_apply_of_notMem _ hz, C.upperStripFunction_apply_of_notMem _ hz]

theorem upperStripTracesMap_id
    (h : ∀ x : C.inter, C.fstToSum (ContinuousLinearMap.id ℂ X₀ (C.interFst x)) =
      C.sndToSum (ContinuousLinearMap.id ℂ X₁ (C.interSnd x))) :
    upperStripTracesMap (ContinuousLinearMap.id ℂ X₀) (ContinuousLinearMap.id ℂ X₁) h =
      ContinuousLinearMap.id ℂ C.upperStripTraces := by
  ext g : 1
  refine Subtype.ext <| Prod.ext ?_ ?_ <;> exact BoundedContinuousFunction.ext fun _ => by simp

theorem norm_upperStripTracesMap_fst_le {M₀ : ℝ} (hM₀ : 0 ≤ M₀) (h₀ : ∀ x, ‖T₀ x‖ ≤ M₀ * ‖x‖)
    (g : C.upperStripTraces) : ‖(upperStripTracesMap T₀ T₁ h g).val.1‖ ≤ M₀ * ‖g‖ := by
  rw [coe_upperStripTracesMap_fst]
  exact (T₀.norm_compLeftContinuousBounded_apply_le _).trans
    (mul_le_mul (T₀.opNorm_le_bound hM₀ h₀) (norm_fst_le g.val) (norm_nonneg _) hM₀)

theorem norm_upperStripTracesMap_snd_le {M₁ : ℝ} (hM₁ : 0 ≤ M₁) (h₁ : ∀ x, ‖T₁ x‖ ≤ M₁ * ‖x‖)
    (g : C.upperStripTraces) : ‖(upperStripTracesMap T₀ T₁ h g).val.2‖ ≤ M₁ * ‖g‖ := by
  rw [coe_upperStripTracesMap_snd]
  exact (T₁.norm_compLeftContinuousBounded_apply_le _).trans
    (mul_le_mul (T₁.opNorm_le_bound hM₁ h₁) (norm_snd_le g.val) (norm_nonneg _) hM₁)

theorem norm_upperStripTracesMap_le {M₀ M₁ : ℝ} (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁)
    (h₀ : ∀ x, ‖T₀ x‖ ≤ M₀ * ‖x‖) (h₁ : ∀ x, ‖T₁ x‖ ≤ M₁ * ‖x‖) (g : C.upperStripTraces) :
    ‖upperStripTracesMap T₀ T₁ h g‖ ≤ max M₀ M₁ * ‖g‖ := by
  rw [← Submodule.norm_coe]
  exact norm_prod_le_iff.2
    ⟨(norm_upperStripTracesMap_fst_le T₀ T₁ h hM₀ h₀ g).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg g)),
      (norm_upperStripTracesMap_snd_le T₀ T₁ h hM₁ h₁ g).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg g))⟩

theorem opNorm_upperStripTracesMap_le {M₀ M₁ : ℝ} (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁)
    (h₀ : ∀ x, ‖T₀ x‖ ≤ M₀ * ‖x‖) (h₁ : ∀ x, ‖T₁ x‖ ≤ M₁ * ‖x‖) :
    ‖upperStripTracesMap T₀ T₁ h‖ ≤ max M₀ M₁ :=
  ContinuousLinearMap.opNorm_le_bound _ (hM₀.trans (le_max_left _ _))
    (norm_upperStripTracesMap_le T₀ T₁ h hM₀ hM₁ h₀ h₁)

/-- Complex derivative evaluation commutes with `upperStripTracesMap`. -/
theorem upperStripDerivEval_upperStripTracesMap (z : ℂ) (g : C.upperStripTraces) :
    D.upperStripDerivEval z (upperStripTracesMap T₀ T₁ h g) =
      C.sumLift (D.fstToSum.comp T₀) (D.sndToSum.comp T₁) h (C.upperStripDerivEval z g) := by
  by_cases hz : z ∈ verticalStrip 0 1
  · rw [upperStripDerivEval_eq_deriv hz (isUpperStripFunction_upperStripTracesMap T₀ T₁ h g),
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
    (hsy.intervalIntegrable t₀ t), smul_add]; abel

private theorem ibpCurve_add_const {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (M₀ M₁ c : ℝ) {y : ℝ → E} (hy_cont : Continuous y) (v : E) (t : ℝ) :
    ibpCurve M₀ M₁ c (fun u => y u + v) t = ibpCurve M₀ M₁ c y t + scaleFactor M₀ M₁ c • v := by
  have hs : Continuous fun u : ℝ => scaleFactor M₀ M₁ (c + u * I) :=
    (differentiable_scaleFactor M₀ M₁).continuous.comp (by fun_prop)
  have hsplit : (∫ u in (0 : ℝ)..t,
        scaleFactor M₀ M₁ (c + u * I) • y u + scaleFactor M₀ M₁ (c + u * I) • v) =
      (∫ u in (0 : ℝ)..t, scaleFactor M₀ M₁ (c + u * I) • y u) +
        ∫ u in (0 : ℝ)..t, scaleFactor M₀ M₁ (c + u * I) • v :=
    intervalIntegral.integral_add ((hs.smul hy_cont).intervalIntegrable _ _)
      ((hs.smul continuous_const).intervalIntegrable _ _)
  have hconst : ((Real.log M₀ - Real.log M₁ : ℂ) * I) •
      (∫ u in (0 : ℝ)..t, scaleFactor M₀ M₁ (c + u * I) • v) =
        scaleFactor M₀ M₁ (c + t * I) • v - scaleFactor M₀ M₁ c • v := by
    rw [intervalIntegral.integral_smul_const, ← mul_smul, ← intervalIntegral.integral_const_mul,
      integral_mul_scaleFactor_add_mul_I]
    simp [sub_smul]
  simp only [ibpCurve, smul_add, hsplit, hconst]
  abel

private theorem ibpCurve_add_const_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (M₀ M₁ c : ℝ) {y : ℝ → E} (hy_cont : Continuous y) (v : E) (t t₀ : ℝ) :
    ibpCurve M₀ M₁ c (fun u => y u + v) t - ibpCurve M₀ M₁ c (fun u => y u + v) t₀ =
      ibpCurve M₀ M₁ c y t - ibpCurve M₀ M₁ c y t₀ := by
  simp only [ibpCurve_add_const M₀ M₁ c hy_cont v]
  abel

private theorem map_ibpCurve {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (M₀ M₁ c : ℝ) (ι : E →L[ℂ] F) {y : ℝ → E} (hy_cont : Continuous y) (t : ℝ) :
    ibpCurve M₀ M₁ c (ι ∘ y) t = ι (ibpCurve M₀ M₁ c y t) := by
  have hsy : Continuous fun u : ℝ => scaleFactor M₀ M₁ (c + u * I) • y u :=
    ((differentiable_scaleFactor M₀ M₁).continuous.comp (by fun_prop)).smul hy_cont
  dsimp only [ibpCurve, Function.comp_apply]; simp_rw [← map_smul]
  rw [ι.intervalIntegral_comp_comm (hsy.intervalIntegrable _ _), ← map_smul, ← map_sub]

/-- One-step quadratic-remainder bound on increments of `ibpCurve`. -/
private theorem norm_ibpCurve_sub_le_quad {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {M₀ M₁ c M : ℝ} (hM : 0 < M) {L : ℝ≥0}
    (hs_norm : ∀ t : ℝ, ‖scaleFactor M₀ M₁ (c + t * I)‖ = M⁻¹) {y : ℝ → E}
    (hy_lip : ∀ t t₀ : ℝ, ‖y t - y t₀‖ ≤ M * L * |t - t₀|) (t t₀ : ℝ) :
    ‖ibpCurve M₀ M₁ c y t - ibpCurve M₀ M₁ c y t₀‖ ≤
      (L : ℝ) * |t - t₀| + ‖(Real.log M₀ - Real.log M₁ : ℂ)‖ * L * |t - t₀| ^ 2 := by
  have hy_cont : Continuous y := (LipschitzWith.of_dist_le' fun u v => by
    simpa [dist_eq_norm, Real.dist_eq] using hy_lip u v).continuous
  have hy₀ : Continuous fun u => y u - y t₀ := hy_cont.sub continuous_const
  have hrem : ibpCurve M₀ M₁ c y t - ibpCurve M₀ M₁ c y t₀ =
      scaleFactor M₀ M₁ (c + t * I) • (y t - y t₀) -
        ((Real.log M₀ - Real.log M₁ : ℂ) * I) •
          ∫ u in t₀..t, scaleFactor M₀ M₁ (c + u * I) • (y u - y t₀) := by
    have hshift := ibpCurve_add_const_sub M₀ M₁ c hy₀ (y t₀) t t₀
    simp only [sub_add_cancel] at hshift
    simpa [hshift] using ibpCurve_sub M₀ M₁ c hy₀ t t₀
  have h1 : ‖scaleFactor M₀ M₁ (c + t * I) • (y t - y t₀)‖ ≤ (L : ℝ) * |t - t₀| := by
    rw [norm_smul, hs_norm t, inv_mul_le_iff₀ hM]; exact (hy_lip t t₀).trans_eq (mul_assoc _ _ _)
  have hint_le : ‖∫ u in t₀..t, scaleFactor M₀ M₁ (c + u * I) • (y u - y t₀)‖ ≤
      (L : ℝ) * |t - t₀| * |t - t₀| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun u hu => by
      rw [norm_smul, hs_norm u, inv_mul_le_iff₀ hM]
      exact ((hy_lip u t₀).trans (mul_le_mul_of_nonneg_left
        (abs_sub_left_of_mem_uIcc (uIoc_subset_uIcc hu)) (by positivity))).trans_eq
        (mul_assoc _ _ _)
  refine hrem ▸ (norm_sub_le _ _).trans (add_le_add h1 ?_)
  rw [norm_smul, norm_mul, norm_I, mul_one]
  exact (mul_le_mul_of_nonneg_left hint_le (norm_nonneg _)).trans_eq (by ring)

/-- `N`-step subdivision upgrades `norm_ibpCurve_sub_le_quad` to exact `L`-Lipschitz continuity. -/
private theorem lipschitzWith_ibpCurve {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {M₀ M₁ c M : ℝ} (hM : 0 < M) {L : ℝ≥0}
    (hs_norm : ∀ t : ℝ, ‖scaleFactor M₀ M₁ (c + t * I)‖ = M⁻¹) {y : ℝ → E}
    (hy_lip : ∀ t t₀ : ℝ, ‖y t - y t₀‖ ≤ M * L * |t - t₀|) :
    LipschitzWith L (ibpCurve M₀ M₁ c y) := by
  let a : ℂ := Real.log M₀ - Real.log M₁; let k := ibpCurve M₀ M₁ c y
  refine LipschitzWith.of_dist_le_mul fun t t₀ => ?_
  rw [dist_eq_norm, Real.dist_eq]; refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨N, hN⟩ := exists_nat_gt (‖a‖ * L * |t - t₀| ^ 2 / ε)
  have hNpos : 0 < (N : ℝ) := (div_nonneg (by positivity) hε.le).trans_lt hN
  let p : ℕ → ℝ := fun m => t₀ + (m : ℝ) / N * (t - t₀)
  have hdiff (j : ℕ) : |p (j + 1) - p j| = |t - t₀| / N := by
    have hstep : p (j + 1) - p j = (t - t₀) / N := by dsimp [p]; push_cast; ring
    rw [hstep, abs_div, abs_of_pos hNpos]
  have hpN : p N = t := by simp [p, div_self hNpos.ne']
  have hp0 : p 0 = t₀ := by simp [p]
  have hsum_norm : ‖k t - k t₀‖ ≤ (L : ℝ) * |t - t₀| + ‖a‖ * L * |t - t₀| ^ 2 / N := by
    conv_lhs => rw [← hpN, ← hp0, ← Finset.sum_range_sub (fun j => k (p j)) N]
    refine ((norm_sum_le _ _).trans (Finset.sum_le_sum
      (g := fun _ => (L : ℝ) * (|t - t₀| / N) + ‖a‖ * L * (|t - t₀| / N) ^ 2)
      fun j _ => ?_)).trans_eq ?_
    · simpa [k, a, hdiff j] using norm_ibpCurve_sub_le_quad hM hs_norm hy_lip (p (j + 1)) (p j)
    · simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, div_pow]; field_simp [hNpos.ne']
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
private theorem ibpStripFunction_sub_eq {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {θ M₀ M₁ : ℝ} (c : ℝ) {H : ℂ → F} (hdH : DiffContOnCl ℂ H (verticalStrip 0 1))
    (hθ : (θ : ℂ) ∈ verticalClosedStrip 0 1) (ι : E →L[ℂ] F) (hc : c ∈ Icc 0 1)
    {y : ℝ → E} (hy_cont : Continuous y) (hH_eq : ∀ u : ℝ, ι (y u) = H (c + u * I) - H c)
    (t t₀ : ℝ) :
    ibpStripFunction θ M₀ M₁ H (c + t * I) - ibpStripFunction θ M₀ M₁ H (c + t₀ * I) =
      ι (ibpCurve M₀ M₁ c y t - ibpCurve M₀ M₁ c y t₀) := by
  have hH_line : (fun u : ℝ => H (c + u * I)) = fun u => (ι ∘ y) u + H c :=
    funext fun u => sub_eq_iff_eq_add.1 (hH_eq u).symm
  have hiy_cont : Continuous (ι ∘ y) := ι.continuous.comp hy_cont
  have hHc_cont : Continuous fun u : ℝ => H (c + u * I) := hH_line ▸ hiy_cont.add continuous_const
  have hf : DiffContOnCl ℂ (fun w => scaleFactor M₀ M₁ w • H w) (verticalStrip 0 1) :=
    (differentiable_scaleFactor M₀ M₁).diffContOnCl.smul hdH
  have hwedge : wedgeIntegral θ (c + t * I) (fun w => scaleFactor M₀ M₁ w • H w) -
      wedgeIntegral θ (c + t₀ * I) (fun w => scaleFactor M₀ M₁ w • H w) =
      I • ∫ u in t₀..t, scaleFactor M₀ M₁ (c + u * I) • H (c + u * I) := by
    rw [hf.wedgeIntegral_sub_wedgeIntegral_eq_of_mem_verticalClosedStrip zero_lt_one hθ
      (by simpa using hc) (by simpa using hc)]; simp [wedgeIntegral]
  have hibp : ibpStripFunction θ M₀ M₁ H (c + t * I) - ibpStripFunction θ M₀ M₁ H (c + t₀ * I) =
      ibpCurve M₀ M₁ c (fun u => H (c + u * I)) t -
        ibpCurve M₀ M₁ c (fun u => H (c + u * I)) t₀ := by
    rw [ibpCurve_sub M₀ M₁ c hHc_cont]
    simp only [ibpStripFunction, sub_eq_iff_eq_add.1 hwedge, smul_add, smul_smul]
    abel
  rw [hibp, hH_line, ibpCurve_add_const_sub M₀ M₁ c hiy_cont]
  simp [map_ibpCurve M₀ M₁ c ι hy_cont]

namespace UpperComplexMethodSpace

variable (θ) in
/-- The continuous linear map `[X₀, X₁]^θ →L[ℂ] [Y₀, Y₁]^θ` induced by continuous linear maps
`T₀ : X₀ →L[ℂ] Y₀` and `T₁ : X₁ →L[ℂ] Y₁` agreeing on `X₀ ∩ X₁`. -/
def map : C.UpperComplexMethodSpace θ →L[ℂ] D.UpperComplexMethodSpace θ :=
  lift ((mk θ).comp (upperStripTracesMap T₀ T₁ h)) fun g hg => by
    rw [ContinuousLinearMap.comp_apply, ← map_zero (mk (C := D) θ), mk_eq_mk_iff,
      upperStripDerivEval_upperStripTracesMap, hg, map_zero, map_zero]

@[simp] theorem map_mk (g : C.upperStripTraces) :
    map θ T₀ T₁ h (mk θ g) = mk θ (upperStripTracesMap T₀ T₁ h g) := by simp [map]

/-- The induced map lies over `x₀ + x₁ ↦ T₀ x₀ + T₁ x₁` on the sum spaces. -/
@[simp] theorem toSum_map (u : C.UpperComplexMethodSpace θ) :
    toSum (map θ T₀ T₁ h u) = C.sumLift (D.fstToSum.comp T₀) (D.sndToSum.comp T₁) h (toSum u) := by
  obtain ⟨g, rfl⟩ := mk_surjective u
  rw [map_mk, toSum_mk, toSum_mk, upperStripDerivEval_upperStripTracesMap]

theorem map_id
    (h : ∀ x : C.inter, C.fstToSum (ContinuousLinearMap.id ℂ X₀ (C.interFst x)) =
      C.sndToSum (ContinuousLinearMap.id ℂ X₁ (C.interSnd x))) :
    map θ (ContinuousLinearMap.id ℂ X₀) (ContinuousLinearMap.id ℂ X₁) h =
      ContinuousLinearMap.id ℂ (C.UpperComplexMethodSpace θ) :=
  ContinuousLinearMap.ext fun u => by
    obtain ⟨g, rfl⟩ := mk_surjective u; simp [upperStripTracesMap_id]

end UpperComplexMethodSpace

section Comp

variable {Z₀ Z₁ U : Type*}
  [NormedAddCommGroup Z₀] [NormedSpace ℂ Z₀] [NormedAddCommGroup Z₁] [NormedSpace ℂ Z₁]
  [AddCommGroup U] [Module ℂ U] [TopologicalSpace U] [ContinuousAdd U] [T1Space U]
  {E : CompatibleCouple ℂ Z₀ Z₁ U} (S₀ : Y₀ →L[ℂ] Z₀) (S₁ : Y₁ →L[ℂ] Z₁)
  (hS : ∀ x : D.inter, E.fstToSum (S₀ (D.interFst x)) = E.sndToSum (S₁ (D.interSnd x)))
  (hST : ∀ x : C.inter,
    E.fstToSum (S₀.comp T₀ (C.interFst x)) = E.sndToSum (S₁.comp T₁ (C.interSnd x)))

theorem upperStripTracesMap_comp :
    upperStripTracesMap (S₀.comp T₀) (S₁.comp T₁) hST =
      (upperStripTracesMap S₀ S₁ hS).comp (upperStripTracesMap T₀ T₁ h) := by
  ext g : 1
  refine Subtype.ext <| Prod.ext ?_ ?_ <;> exact BoundedContinuousFunction.ext fun _ => by simp

theorem UpperComplexMethodSpace.map_comp :
    UpperComplexMethodSpace.map θ (S₀.comp T₀) (S₁.comp T₁) hST =
      (UpperComplexMethodSpace.map θ S₀ S₁ hS).comp (UpperComplexMethodSpace.map θ T₀ T₁ h) :=
  ContinuousLinearMap.ext fun u => by
    obtain ⟨g, rfl⟩ := UpperComplexMethodSpace.mk_surjective u
    rw [ContinuousLinearMap.comp_apply, UpperComplexMethodSpace.map_mk,
      UpperComplexMethodSpace.map_mk, UpperComplexMethodSpace.map_mk,
      upperStripTracesMap_comp T₀ T₁ h S₀ S₁ hS hST, ContinuousLinearMap.comp_apply]

end Comp

namespace UpperComplexMethodSpace

/-- `UpperComplexMethodSpace.map` commutes with the inclusions of the intersections. -/
theorem map_ofInter {x : C.inter} {y : D.inter} (hy : D.interFst y = T₀ (C.interFst x)) :
    map θ T₀ T₁ h (ofInter θ x) = ofInter θ y := by
  by_cases hθ : θ ∈ Ioo 0 1
  · ext; rw [toSum_map, toSum_ofInter hθ, toSum_ofInter hθ, hy]; exact C.sumLift_fstToSum _ _ h _
  · simp [eq_zero_of_notMem hθ]

theorem opNorm_map_le_max {M₀ M₁ : ℝ} (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁)
    (h₀ : ∀ x, ‖T₀ x‖ ≤ M₀ * ‖x‖) (h₁ : ∀ x, ‖T₁ x‖ ≤ M₁ * ‖x‖) :
    ‖map θ T₀ T₁ h‖ ≤ max M₀ M₁ := by
  rw [map, norm_lift]
  exact (norm_mk_comp_le _).trans (opNorm_upperStripTracesMap_le T₀ T₁ h hM₀ hM₁ h₀ h₁)

/-- Without completeness hypotheses, `UpperComplexMethodSpace.map` is bounded by `max M₀ M₁`. -/
theorem norm_map_le_max {M₀ M₁ : ℝ} (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁)
    (h₀ : ∀ x, ‖T₀ x‖ ≤ M₀ * ‖x‖) (h₁ : ∀ x, ‖T₁ x‖ ≤ M₁ * ‖x‖)
    (u : C.UpperComplexMethodSpace θ) : ‖map θ T₀ T₁ h u‖ ≤ max M₀ M₁ * ‖u‖ :=
  (map θ T₀ T₁ h).le_of_opNorm_le (opNorm_map_le_max T₀ T₁ h hM₀ hM₁ h₀ h₁) u

/-- Contractive endpoint maps induce a contractive map on `[X₀, X₁]^θ`, without completeness
assumptions. -/
theorem norm_map_le_of_norm_le (h₀ : ∀ x, ‖T₀ x‖ ≤ ‖x‖) (h₁ : ∀ x, ‖T₁ x‖ ≤ ‖x‖)
    (u : C.UpperComplexMethodSpace θ) : ‖map θ T₀ T₁ h u‖ ≤ ‖u‖ := by
  simpa using norm_map_le_max T₀ T₁ h zero_le_one zero_le_one
    (fun x => by simpa using h₀ x) (fun x => by simpa using h₁ x) u

/-! ### Exact interpolation of exponent `θ` (Bergh–Löfström Theorem 4.1.4) -/

/-- Finite-order exponential growth of `ibpStripFunction` on the open strip. -/
private theorem exists_isBigO_ibpStripFunction_exp_rpow (hθ : θ ∈ Ioo 0 1) (M₀ M₁ : ℝ)
    (qY : D.upperStripTraces) :
    ∃ A B : ℝ, ibpStripFunction θ M₀ M₁ (D.upperStripFunction qY)
      =O[cobounded ℂ ⊓ 𝓟 (verticalStrip 0 1)] fun w => Real.exp (B * ‖w‖ ^ A) := by
  let a : ℂ := Real.log M₀ - Real.log M₁
  let s := scaleFactor M₀ M₁; let H := D.upperStripFunction qY
  set S := Real.exp (|Real.log M₀| + |Real.log M₁|)
  have hθ_norm : ‖(θ : ℂ)‖ ≤ 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hθ.1.le] using hθ.2.le
  refine ⟨2, S * ‖qY‖ + ‖a‖ * (12 * S * ‖qY‖) + 1, IsBigO.of_norm_eventuallyLE ?_⟩
  filter_upwards [(tendsto_norm_cobounded_atTop.eventually (eventually_ge_atTop 1)).filter_mono
    inf_le_left, (eventually_mem_principal (verticalStrip 0 1)).filter_mono inf_le_right]
    with z hz1 hz
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
  let qY := upperStripTracesMap T₀ T₁ h g; let H := D.upperStripFunction qY
  have hH : D.IsUpperStripFunction H qY := D.isUpperStripFunction_upperStripFunction qY
  have hf : DiffContOnCl ℂ (fun w => scaleFactor M₀ M₁ w • H w) (verticalStrip 0 1) :=
    (differentiable_scaleFactor M₀ M₁).diffContOnCl.smul hH.diffContOnCl
  have hdK : DiffContOnCl ℂ (ibpStripFunction θ M₀ M₁ H) (verticalStrip 0 1) :=
    hf.sub ((hf.diffContOnCl_wedgeIntegral_verticalStrip zero_lt_one hθ_cl).const_smul
      (Real.log M₀ - Real.log M₁ : ℂ))
  have hderivK : toSum (scaleFactor M₀ M₁ θ • map θ T₀ T₁ h (mk θ g)) =
      deriv (ibpStripFunction θ M₀ M₁ H) θ := by
    have hKθ : HasDerivAt (ibpStripFunction θ M₀ M₁ H) (scaleFactor M₀ M₁ θ • deriv H θ) θ := by
      unfold ibpStripFunction
      exact (((hasDerivAt_scaleFactor M₀ M₁ θ).fun_smul
          (hH.differentiableAt hθ_open).hasDerivAt).fun_sub
        ((hf.hasDerivAt_wedgeIntegral_verticalStrip hθ_cl hθ_open).fun_const_smul _)).congr_deriv
        (by rw [smul_smul]; abel)
    rw [hKθ.deriv, map_smul, map_mk, toSum_mk, D.upperStripDerivEval_apply hθ_open]
  have hlip₀ := lipschitzWith_ibpCurve (M₀ := M₀) (M₁ := M₁) (c := 0) hM₀ (L := ‖g‖₊)
    (fun t => by simpa using norm_scaleFactor_mul_I (M₁ := M₁) hM₀ t) fun t t₀ =>
      (hH.norm_pinnedCurve_fst_sub_le t t₀).trans (mul_le_mul_of_nonneg_right
        (norm_upperStripTracesMap_fst_le T₀ T₁ h hM₀.le h₀ g) (abs_nonneg _))
  have hlip₁ := lipschitzWith_ibpCurve (M₀ := M₀) (M₁ := M₁) (c := 1) hM₁ (L := ‖g‖₊)
    (fun t => by simpa using norm_scaleFactor_one_add_mul_I (M₀ := M₀) hM₁ t) fun t t₀ =>
      (hH.norm_pinnedCurve_snd_sub_le t t₀).trans (mul_le_mul_of_nonneg_right
        (norm_upperStripTracesMap_snd_le T₀ T₁ h hM₁.le h₁ g) (abs_nonneg _))
  simpa using norm_le_of_lipschitz hdK (exists_isBigO_ibpStripFunction_exp_rpow hθ M₀ M₁ qY)
    hlip₀ hlip₁
    (fun t t₀ => by
      simpa using ibpStripFunction_sub_eq 0 hH.diffContOnCl hθ_cl D.fstToSum ⟨le_rfl, zero_le_one⟩
        hH.lipschitzWith_pinnedCurve_fst.continuous
        (fun u => by simpa using hH.fstToSum_pinnedCurve u) t t₀)
    (fun t t₀ => by
      simpa using ibpStripFunction_sub_eq 1 hH.diffContOnCl hθ_cl D.sndToSum ⟨zero_le_one, le_rfl⟩
        hH.lipschitzWith_pinnedCurve_snd.continuous hH.sndToSum_pinnedCurve t t₀) hderivK

private theorem norm_map_le_of_pos [CompleteSpace Y₀] [CompleteSpace Y₁] (hθ : θ ∈ Ioo 0 1)
    {M₀ M₁ : ℝ} (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
    (h₀ : ∀ x, ‖T₀ x‖ ≤ M₀ * ‖x‖) (h₁ : ∀ x, ‖T₁ x‖ ≤ M₁ * ‖x‖)
    (u : C.UpperComplexMethodSpace θ) : ‖map θ T₀ T₁ h u‖ ≤ M₀ ^ (1 - θ) * M₁ ^ θ * ‖u‖ := by
  let S : C.UpperComplexMethodSpace θ →L[ℂ] D.UpperComplexMethodSpace θ :=
    scaleFactor M₀ M₁ θ • map θ T₀ T₁ h
  have hS : ‖S‖ ≤ 1 := by
    rw [← norm_comp_mk]
    exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun g => by
      simpa [S] using norm_scaleFactor_smul_map_mk_le T₀ T₁ h hθ hM₀ hM₁ h₀ h₁ g
  calc ‖map θ T₀ T₁ h u‖
      = M₀ ^ (1 - θ) * M₁ ^ θ * ‖S u‖ := by
        symm; dsimp only [S]
        rw [smul_apply, norm_smul, ← mul_assoc (M₀ ^ (1 - θ) * M₁ ^ θ),
          mul_comm (M₀ ^ (1 - θ) * M₁ ^ θ), norm_scaleFactor_mul_rpow hM₀ hM₁, one_mul]
    _ ≤ M₀ ^ (1 - θ) * M₁ ^ θ * ‖u‖ :=
        mul_le_mul_of_nonneg_left (by simpa using S.le_of_opNorm_le hS u) (by positivity)

/-- **Bergh–Löfström Theorem 4.1.4 (exact interpolation for Calderón's upper method).** When `Y₀`
and `Y₁` are complete, if `‖T₀ x‖ ≤ M₀ * ‖x‖` and `‖T₁ x‖ ≤ M₁ * ‖x‖` with `M₀, M₁ ≥ 0`, then the
induced map `[X₀, X₁]^θ → [Y₀, Y₁]^θ` satisfies
`‖map θ T₀ T₁ h u‖ ≤ M₀ ^ (1 - θ) * M₁ ^ θ * ‖u‖`. -/
theorem norm_map_le [CompleteSpace Y₀] [CompleteSpace Y₁] {M₀ M₁ : ℝ}
    (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁) (h₀ : ∀ x, ‖T₀ x‖ ≤ M₀ * ‖x‖) (h₁ : ∀ x, ‖T₁ x‖ ≤ M₁ * ‖x‖)
    (u : C.UpperComplexMethodSpace θ) : ‖map θ T₀ T₁ h u‖ ≤ M₀ ^ (1 - θ) * M₁ ^ θ * ‖u‖ := by
  by_cases hθ : θ ∈ Ioo 0 1
  · exact le_rpow_mul_rpow_mul_of_forall_pos ⟨hθ.1.le, hθ.2.le⟩ fun _ hε =>
      norm_map_le_of_pos T₀ T₁ h hθ (by positivity) (by positivity)
        (fun x => (h₀ x).trans (by gcongr; linarith))
        (fun x => (h₁ x).trans (by gcongr; linarith)) u
  · simp [eq_zero_of_notMem hθ u]

/-- Operator-norm form of `UpperComplexMethodSpace.norm_map_le`. -/
theorem opNorm_map_le [CompleteSpace Y₀] [CompleteSpace Y₁] {M₀ M₁ : ℝ}
    (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁) (h₀ : ∀ x, ‖T₀ x‖ ≤ M₀ * ‖x‖) (h₁ : ∀ x, ‖T₁ x‖ ≤ M₁ * ‖x‖) :
    ‖map θ T₀ T₁ h‖ ≤ M₀ ^ (1 - θ) * M₁ ^ θ :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) (norm_map_le T₀ T₁ h hM₀ hM₁ h₀ h₁)

/-- Exact interpolation of exponent `θ` in terms of endpoint operator norms:
`‖map θ T₀ T₁ h‖ ≤ ‖T₀‖ ^ (1 - θ) * ‖T₁‖ ^ θ`. -/
theorem opNorm_map_le_opNorm [CompleteSpace Y₀] [CompleteSpace Y₁] :
    ‖map θ T₀ T₁ h‖ ≤ ‖T₀‖ ^ (1 - θ) * ‖T₁‖ ^ θ :=
  opNorm_map_le T₀ T₁ h (norm_nonneg _) (norm_nonneg _) T₀.le_opNorm T₁.le_opNorm

end UpperComplexMethodSpace

end Map

/-! ### Retracts and isomorphisms of couples -/

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
    (hPI₀ : Function.LeftInverse P₀ I₀) (hPI₁ : Function.LeftInverse P₁ I₁) {N₀ N₁ : ℝ}
    (hN₀ : 0 ≤ N₀) (hN₁ : 0 ≤ N₁) (h₀ : ∀ y, ‖P₀ y‖ ≤ N₀ * ‖y‖) (h₁ : ∀ y, ‖P₁ y‖ ≤ N₁ * ‖y‖)
    (u : C.UpperComplexMethodSpace θ) : ‖u‖ ≤ N₀ ^ (1 - θ) * N₁ ^ θ * ‖map θ I₀ I₁ hI u‖ := by
  conv_lhs => rw [← leftInverse_map I₀ I₁ hI P₀ P₁ hP hPI₀ hPI₁ u]
  exact norm_map_le P₀ P₁ hP hN₀ hN₁ h₀ h₁ _

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
  ContinuousLinearEquiv.ofContinuousLinearMap (map θ e₀ e₁ h) (map θ e₀.symm e₁.symm hsymm)
    (ContinuousLinearMap.ext fun v ↦
      leftInverse_map _ _ hsymm _ _ h (fun _ ↦ e₀.apply_symm_apply _)
        (fun _ ↦ e₁.apply_symm_apply _) v)
    (ContinuousLinearMap.ext fun u ↦
      leftInverse_map _ _ h _ _ hsymm (fun _ ↦ e₀.symm_apply_apply _)
        (fun _ ↦ e₁.symm_apply_apply _) u)

theorem mapEquiv_apply (u : C.UpperComplexMethodSpace θ) :
    mapEquiv θ e₀ e₁ h hsymm u = map θ e₀ e₁ h u := (rfl)

theorem mapEquiv_symm_apply (v : D.UpperComplexMethodSpace θ) :
    (mapEquiv θ e₀ e₁ h hsymm).symm v = map θ e₀.symm e₁.symm hsymm v := (rfl)

@[simp] theorem toSum_mapEquiv (u : C.UpperComplexMethodSpace θ) :
    toSum (mapEquiv θ e₀ e₁ h hsymm u) =
      C.sumLift (D.fstToSum.comp (e₀ : X₀ →L[ℂ] Y₀)) (D.sndToSum.comp (e₁ : X₁ →L[ℂ] Y₁)) h
        (toSum u) := toSum_map _ _ h u

@[simp] theorem toSum_mapEquiv_symm (v : D.UpperComplexMethodSpace θ) :
    toSum ((mapEquiv θ e₀ e₁ h hsymm).symm v) =
      D.sumLift (C.fstToSum.comp (e₀.symm : Y₀ →L[ℂ] X₀))
        (C.sndToSum.comp (e₁.symm : Y₁ →L[ℂ] X₁)) hsymm (toSum v) := toSum_map _ _ hsymm v

/-- Isometric endpoint equivalences induce an isometry `[X₀, X₁]^θ ≃ [Y₀, Y₁]^θ`, without
completeness assumptions. -/
theorem norm_mapEquiv (h₀ : ∀ x, ‖e₀ x‖ = ‖x‖) (h₁ : ∀ x, ‖e₁ x‖ = ‖x‖)
    (u : C.UpperComplexMethodSpace θ) : ‖mapEquiv θ e₀ e₁ h hsymm u‖ = ‖u‖ := by
  refine le_antisymm (norm_map_le_of_norm_le _ _ h (fun x => (h₀ x).le) (fun x => (h₁ x).le) u) ?_
  conv_lhs => rw [← (mapEquiv θ e₀ e₁ h hsymm).symm_apply_apply u, mapEquiv_symm_apply]
  refine norm_map_le_of_norm_le _ _ hsymm (fun y => ?_) (fun y => ?_) _
  · rw [ContinuousLinearEquiv.coe_coe, ← h₀ (e₀.symm y), ContinuousLinearEquiv.apply_symm_apply]
  · rw [ContinuousLinearEquiv.coe_coe, ← h₁ (e₁.symm y), ContinuousLinearEquiv.apply_symm_apply]

end Equiv

end UpperComplexMethodSpace

end TauCeti.CompatibleCouple
