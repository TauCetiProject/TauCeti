/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Interpolation.ComplexMethod.Upper.Basic
import TauCeti.Analysis.Complex.VerticalStrip

/-!
# Functoriality and exact interpolation for Calderón's upper complex method

Continuous linear maps `T₀ : X₀ →L[ℂ] Y₀` and `T₁ : X₁ →L[ℂ] Y₁` between the endpoints of two
compatible couples that agree on the intersection induce a continuous linear map
`UpperComplexMethodSpace.map θ T₀ T₁ h : [X₀, X₁]^θ →L[ℂ] [Y₀, Y₁]^θ` lying over the sum-space lift
`x₀ + x₁ ↦ T₀ x₀ + T₁ x₁` (`UpperComplexMethodSpace.toSum_map`).

When the target endpoints `Y₀` and `Y₁` are complete, Calderón's upper method is an exact
interpolation functor of exponent `θ` (Bergh–Löfström, Theorem 4.1.2): if `‖T₀ x‖ ≤ M₀ * ‖x‖` and
`‖T₁ x‖ ≤ M₁ * ‖x‖` with `M₀, M₁ ≥ 0`, then for `0 < θ < 1`,
`‖map θ T₀ T₁ h u‖ ≤ M₀ ^ (1 - θ) * M₁ ^ θ * ‖u‖` (`UpperComplexMethodSpace.norm_map_le`).
Notice that unlike `[X₀, X₁]_θ`, multiplying an upper strip function `H` pointwise by the analytic
weight `M₀ ^ (z - 1) * M₁ ^ (-z)` alters its complex derivative at `θ`; the exact bound integrates
that weight against `deriv H` by parts via `Complex.wedgeIntegral`.

For contractions (`M₀ = M₁ = 1`), the induced map is contractive without completeness assumptions
(`UpperComplexMethodSpace.norm_map_le_of_norm_le`), yielding retract stability and isometric
invariance under endpoint isomorphisms (`UpperComplexMethodSpace.mapEquiv`,
`UpperComplexMethodSpace.norm_mapEquiv`), following the interface of
`TauCeti.Analysis.Normed.Interpolation.ComplexMethod.Basic`.

## References

* A.-P. Calderón, *Intermediate spaces and interpolation, the complex method*, Studia Math. 24
  (1964), 113–190, §§5–6.
* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Grundlehren 223,
  Springer, 1976, §4.1 (Theorem 4.1.2).
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
    refine ⟨‖S‖ * max K 0, fun z hz => ?_⟩
    calc ‖S (G z)‖ ≤ ‖S‖ * ‖G z‖ := S.le_opNorm (G z)
      _ ≤ ‖S‖ * (K * (1 + |z.im|)) := mul_le_mul_of_nonneg_left (hK z hz) (norm_nonneg S)
      _ ≤ ‖S‖ * max K 0 * (1 + |z.im|) := by rw [mul_assoc]; gcongr; exact le_max_left K 0
  sub_mul_I hne := by
    rw [← map_sub, hG.sub_mul_I hne, map_smul]
    exact congrArg (_ • ·) (C.sumLift_fstToSum _ _ h _)
  sub_one_add_mul_I hne := by
    rw [← map_sub, hG.sub_one_add_mul_I hne, map_smul]
    exact congrArg (_ • ·) (C.sumLift_sndToSum _ _ h _)

private theorem norm_compLeftContinuousBounded_le {α E F : Type*} [TopologicalSpace α]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    (T : E →L[ℂ] F) {M : ℝ} (hM : 0 ≤ M) (hT : ∀ x, ‖T x‖ ≤ M * ‖x‖) (f : α →ᵇ E) :
    ‖T.compLeftContinuousBounded α f‖ ≤ M * ‖f‖ :=
  (BoundedContinuousFunction.norm_le (mul_nonneg hM (norm_nonneg f))).2 fun p =>
    (hT _).trans (mul_le_mul_of_nonneg_left (f.norm_coe_le_norm p) hM)

/-- The map of upper boundary difference quotients `(q₀, q₁) ↦ (T₀ ∘ q₀, T₁ ∘ q₁)` induced by
compatible endpoint maps `T₀` and `T₁`. -/
def upperStripTracesMap : C.upperStripTraces →L[ℂ] D.upperStripTraces :=
  LinearMap.mkContinuous
    { toFun g := ⟨(T₀.compLeftContinuousBounded _ g.1.1, T₁.compLeftContinuousBounded _ g.1.2),
        mem_upperStripTraces_iff.2 ⟨_, (C.isUpperStripFunction_upperStripFunction g).map T₀ T₁ h⟩⟩
      map_add' _ _ := Subtype.ext <| Prod.ext
        (BoundedContinuousFunction.ext fun _ => by simp)
        (BoundedContinuousFunction.ext fun _ => by simp)
      map_smul' _ _ := Subtype.ext <| Prod.ext
        (BoundedContinuousFunction.ext fun _ => by simp)
        (BoundedContinuousFunction.ext fun _ => by simp) }
    (max ‖T₀‖ ‖T₁‖) fun g =>
      norm_prod_le_iff.2
        ⟨(norm_compLeftContinuousBounded_le T₀ (norm_nonneg _) T₀.le_opNorm _).trans
            (mul_le_mul (le_max_left _ _) (norm_fst_le g.1) (norm_nonneg _)
              (le_trans (norm_nonneg T₀) (le_max_left _ _))),
          (norm_compLeftContinuousBounded_le T₁ (norm_nonneg _) T₁.le_opNorm _).trans
            (mul_le_mul (le_max_right _ _) (norm_snd_le g.1) (norm_nonneg _)
              (le_trans (norm_nonneg T₀) (le_max_left _ _)))⟩

@[simp]
theorem upperStripTracesMap_apply_fst (g : C.upperStripTraces) (p : offDiag (univ : Set ℝ)) :
    (upperStripTracesMap T₀ T₁ h g).1.1 p = T₀ (g.1.1 p) := (rfl)

@[simp]
theorem upperStripTracesMap_apply_snd (g : C.upperStripTraces) (p : offDiag (univ : Set ℝ)) :
    (upperStripTracesMap T₀ T₁ h g).1.2 p = T₁ (g.1.2 p) := (rfl)

theorem norm_upperStripTracesMap_fst_le {M₀ : ℝ} (hM₀ : 0 ≤ M₀) (h₀ : ∀ x, ‖T₀ x‖ ≤ M₀ * ‖x‖)
    (g : C.upperStripTraces) : ‖(upperStripTracesMap T₀ T₁ h g).1.1‖ ≤ M₀ * ‖g‖ :=
  (norm_compLeftContinuousBounded_le T₀ hM₀ h₀ _).trans
    (mul_le_mul_of_nonneg_left (norm_fst_le g.1) hM₀)

theorem norm_upperStripTracesMap_snd_le {M₁ : ℝ} (hM₁ : 0 ≤ M₁) (h₁ : ∀ x, ‖T₁ x‖ ≤ M₁ * ‖x‖)
    (g : C.upperStripTraces) : ‖(upperStripTracesMap T₀ T₁ h g).1.2‖ ≤ M₁ * ‖g‖ :=
  (norm_compLeftContinuousBounded_le T₁ hM₁ h₁ _).trans
    (mul_le_mul_of_nonneg_left (norm_snd_le g.1) hM₁)

/-- Complex derivative evaluation commutes with `upperStripTracesMap`. -/
theorem upperStripDerivEval_upperStripTracesMap (z : ℂ) (g : C.upperStripTraces) :
    D.upperStripDerivEval z (upperStripTracesMap T₀ T₁ h g) =
      C.sumLift (D.fstToSum.comp T₀) (D.sndToSum.comp T₁) h (C.upperStripDerivEval z g) := by
  let S := C.sumLift (D.fstToSum.comp T₀) (D.sndToSum.comp T₁) h
  by_cases hz : z ∈ verticalStrip 0 1
  · rw [upperStripDerivEval_eq_deriv hz
        ((C.isUpperStripFunction_upperStripFunction g).map T₀ T₁ h),
      C.upperStripDerivEval_apply hz]
    exact (S.hasFDerivAt.comp_hasDerivAt z
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
  have hadj : (∫ u in (0 : ℝ)..t, scaleFactor M₀ M₁ (c + u * I) • y u) -
      ∫ u in (0 : ℝ)..t₀, scaleFactor M₀ M₁ (c + u * I) • y u =
      ∫ u in t₀..t, scaleFactor M₀ M₁ (c + u * I) • y u := by
    rw [sub_eq_iff_eq_add',
      intervalIntegral.integral_add_adjacent_intervals (hsy.intervalIntegrable _ _)
        (hsy.intervalIntegrable _ _)]
  dsimp only [ibpCurve]; rw [← hadj, smul_sub]; abel

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
  have hconst_int : (a * I) • (∫ u in t₀..t, s (c + u * I) • y t₀) =
      (s (c + t * I) - s (c + t₀ * I)) • y t₀ := by
    rw [intervalIntegral.integral_smul_const, ← smul_assoc, smul_eq_mul,
      ← intervalIntegral.integral_const_mul, integral_deriv_scaleFactor_add_mul_I]
  have hrem : ibpCurve M₀ M₁ c y t - ibpCurve M₀ M₁ c y t₀ = s (c + t * I) • (y t - y t₀) -
      (a * I) • ∫ u in t₀..t, s (c + u * I) • (y u - y t₀) := by
    have hdiff_int : (∫ u in t₀..t, s (c + u * I) • (y u - y t₀)) =
        (∫ u in t₀..t, s (c + u * I) • y u) - ∫ u in t₀..t, s (c + u * I) • y t₀ := by
      simp_rw [smul_sub]
      exact intervalIntegral.integral_sub ((hs_cont.smul hy_cont).intervalIntegrable _ _)
        ((hs_cont.smul continuous_const).intervalIntegrable _ _)
    rw [ibpCurve_sub M₀ M₁ c hy_cont, hdiff_int, smul_sub, smul_sub, hconst_int, sub_smul]
    dsimp [a, s]; abel
  have h1 : ‖s (c + t * I) • (y t - y t₀)‖ ≤ (L : ℝ) * |t - t₀| := by
    rw [norm_smul, hs_norm t, inv_mul_le_iff₀ hM]; exact (hy_lip t t₀).trans_eq (mul_assoc _ _ _)
  have h2 : ‖(a * I) • ∫ u in t₀..t, s (c + u * I) • (y u - y t₀)‖ ≤ ‖a‖ * L * |t - t₀| ^ 2 := by
    rw [norm_smul, norm_mul, norm_I, mul_one]
    have hint_le : ‖∫ u in t₀..t, s (c + u * I) • (y u - y t₀)‖ ≤
        ((L : ℝ) * |t - t₀|) * |t - t₀| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const fun u hu => ?_
      have hu_le : |u - t₀| ≤ |t - t₀| := by
        rcases mem_uIcc.1 (uIoc_subset_uIcc hu) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
          exact abs_le.2
            ⟨by linarith [le_abs_self (t - t₀), neg_abs_le (t - t₀), abs_nonneg (t - t₀)],
              by linarith [le_abs_self (t - t₀), neg_abs_le (t - t₀), abs_nonneg (t - t₀)]⟩
      rw [norm_smul, hs_norm u, inv_mul_le_iff₀ hM]
      exact ((hy_lip u t₀).trans (mul_le_mul_of_nonneg_left hu_le
        (mul_nonneg hM.le L.coe_nonneg))).trans_eq (mul_assoc _ _ _)
    exact (mul_le_mul_of_nonneg_left hint_le (norm_nonneg a)).trans_eq (by ring)
  exact hrem ▸ (norm_sub_le _ _).trans (add_le_add h1 h2)

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
  have hNpos : 0 < (N : ℝ) := lt_of_le_of_lt (div_nonneg (by positivity) hε.le) hN
  let p : ℕ → ℝ := fun m => t₀ + (m : ℝ) / N * (t - t₀)
  have hdiff (j : ℕ) : |p (j + 1) - p j| = |t - t₀| / N := by
    have : p (j + 1) - p j = (t - t₀) / N := by dsimp [p]; push_cast; ring
    rw [this, abs_div, abs_of_pos hNpos]
  have hsum_norm : ‖k t - k t₀‖ ≤ (L : ℝ) * |t - t₀| + ‖a‖ * L * |t - t₀| ^ 2 / N := by
    have hpN : p N = t := by simp [p, div_self hNpos.ne']
    have hp0 : p 0 = t₀ := by simp [p]
    conv_lhs => rw [← hpN, ← hp0, ← Finset.sum_range_sub (fun j => k (p j)) N]
    calc ‖∑ j ∈ Finset.range N, (k (p (j + 1)) - k (p j))‖
        ≤ ∑ j ∈ Finset.range N, ‖k (p (j + 1)) - k (p j)‖ := norm_sum_le _ _
      _ ≤ ∑ _j ∈ Finset.range N,
            ((L : ℝ) * (|t - t₀| / N) + ‖a‖ * L * (|t - t₀| / N) ^ 2) :=
          Finset.sum_le_sum fun j _ => by
            simpa [k, a, hdiff j] using
              norm_ibpCurve_sub_le_quad hM hs_norm hy_cont hy_lip (p (j + 1)) (p j)
      _ = (L : ℝ) * |t - t₀| + ‖a‖ * L * |t - t₀| ^ 2 / N := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, div_pow]
          field_simp [hNpos.ne']
  have hrem_lt : ‖a‖ * L * |t - t₀| ^ 2 / N < ε := by
    rw [div_lt_iff₀ hNpos]; linarith [(div_lt_iff₀ hε).1 hN, mul_comm ε (N : ℝ)]
  linarith

/-- Sum-space boundary increment identity for the integrated-by-parts strip function. -/
private theorem wedgeIntegral_ibp_sub_eq [CompleteSpace Y₀] [CompleteSpace Y₁]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {M₀ M₁ c : ℝ} {H : ℂ → D.SumSpace}
    (hdH : DiffContOnCl ℂ H (verticalStrip 0 1)) (hθ : (θ : ℂ) ∈ verticalClosedStrip 0 1)
    (ι : E →L[ℂ] D.SumSpace) (hc : c ∈ Icc 0 1) {y : ℝ → E} (hy_cont : Continuous y)
    {u₀ : D.SumSpace} (hH_eq : ∀ t : ℝ, H (c + t * I) = ι (y t) + u₀) (t t₀ : ℝ) :
    let a : ℂ := Real.log M₀ - Real.log M₁
    let s := scaleFactor M₀ M₁
    (s (c + t * I) • H (c + t * I) - a • wedgeIntegral θ (c + t * I) (fun w => s w • H w)) -
      (s (c + t₀ * I) • H (c + t₀ * I) - a • wedgeIntegral θ (c + t₀ * I) (fun w => s w • H w)) =
      ι (ibpCurve M₀ M₁ c y t - ibpCurve M₀ M₁ c y t₀) := by
  intro a s
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
        (s (c + t * I) - s (c + t₀ * I)) • u₀ := by
    have hi₁ : IntervalIntegrable (fun u : ℝ => ι (s (c + u * I) • y u))
        MeasureTheory.volume t₀ t :=
      (ι.continuous.comp hsy_cont).intervalIntegrable _ _
    have hi₂ : IntervalIntegrable (fun u : ℝ => s (c + u * I) • u₀) MeasureTheory.volume t₀ t :=
      (hs_cont.smul continuous_const).intervalIntegrable _ _
    simp_rw [hH_eq, smul_add, ← map_smul]
    rw [intervalIntegral.integral_add hi₁ hi₂,
      ι.intervalIntegral_comp_comm (hsy_cont.intervalIntegrable _ _),
      intervalIntegral.integral_smul_const, smul_add, ← map_smul, ← smul_assoc, smul_eq_mul,
      ← intervalIntegral.integral_const_mul, integral_deriv_scaleFactor_add_mul_I]
  rw [sub_sub_sub_comm, ← smul_sub, hwedge, smul_smul, hint_split, hH_eq t, hH_eq t₀,
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
    map θ T₀ T₁ h (mk θ g) = mk θ (upperStripTracesMap T₀ T₁ h g) := by
  simp [map]

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
  ext
  rw [toSum_map, toSum_ofInter hθ, toSum_ofInter hθ, hy]
  exact C.sumLift_fstToSum _ _ h _

/-- Without completeness hypotheses, `UpperComplexMethodSpace.map` is bounded by `max M₀ M₁`. -/
theorem norm_map_le_max {M₀ M₁ : ℝ} (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁)
    (h₀ : ∀ x, ‖T₀ x‖ ≤ M₀ * ‖x‖) (h₁ : ∀ x, ‖T₁ x‖ ≤ M₁ * ‖x‖)
    (u : C.UpperComplexMethodSpace θ) :
    ‖map θ T₀ T₁ h u‖ ≤ max M₀ M₁ * ‖u‖ := by
  set M := max M₀ M₁
  have hM : 0 ≤ M := le_trans hM₀ (le_max_left _ _)
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨g, rfl, hg⟩ := norm_lt_iff.1
    (lt_add_of_pos_right ‖u‖ (div_pos hε (by linarith : 0 < M + 1)))
  have htrace : ‖upperStripTracesMap T₀ T₁ h g‖ ≤ M * ‖g‖ :=
    max_le
      ((norm_upperStripTracesMap_fst_le T₀ T₁ h hM₀ h₀ g).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg g)))
      ((norm_upperStripTracesMap_snd_le T₀ T₁ h hM₁ h₁ g).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg g)))
  calc ‖map θ T₀ T₁ h (mk θ g)‖ = ‖mk θ (upperStripTracesMap T₀ T₁ h g)‖ := by rw [map_mk]
    _ ≤ M * ‖g‖ := (norm_mk_le _).trans htrace
    _ ≤ M * (‖mk θ g‖ + ε / (M + 1)) := mul_le_mul_of_nonneg_left hg.le hM
    _ ≤ M * ‖mk θ g‖ + (M + 1) * (ε / (M + 1)) := by rw [mul_add]; gcongr; linarith
    _ = M * ‖mk θ g‖ + ε := by rw [mul_div_cancel₀ _ (by linarith : M + 1 ≠ 0)]

/-- Contractive endpoint maps induce a contractive map on `[X₀, X₁]^θ`, without completeness
assumptions. -/
theorem norm_map_le_of_norm_le (h₀ : ∀ x, ‖T₀ x‖ ≤ ‖x‖) (h₁ : ∀ x, ‖T₁ x‖ ≤ ‖x‖)
    (u : C.UpperComplexMethodSpace θ) : ‖map θ T₀ T₁ h u‖ ≤ ‖u‖ := by
  simpa using norm_map_le_max T₀ T₁ h zero_le_one zero_le_one
    (fun x => by simpa using h₀ x) (fun x => by simpa using h₁ x) u

/-! ### Exact interpolation of exponent `θ` (Bergh–Löfström Theorem 4.1.2) -/

private theorem norm_wedgeIntegral_le_of_linear {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℂ → E} {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hf : ∀ {w}, w ∈ verticalClosedStrip 0 1 → ‖f w‖ ≤ C₀ * ‖w‖)
    {θ : ℝ} (hθ : θ ∈ Icc 0 1) {z : ℂ}
    (hz : z ∈ verticalClosedStrip 0 1) (hz1 : 1 ≤ ‖z‖) :
    ‖wedgeIntegral θ z f‖ ≤ 3 * C₀ * ‖z‖ ^ 2 := by
  obtain ⟨hz0, hz1'⟩ := hz
  have hre : ‖∫ x in θ..z.re, f x‖ ≤ C₀ := by
    refine (intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_).trans
      (mul_le_of_le_one_right hC₀ (abs_le.2 ⟨by linarith [hθ.2], by linarith [hθ.1]⟩))
    have hx_mem : x ∈ Icc 0 1 :=
      ordConnected_Icc.uIcc_subset hθ ⟨hz0, hz1'⟩ (uIoc_subset_uIcc hx)
    exact (hf (by simpa using hx_mem)).trans (mul_le_of_le_one_right hC₀
      (by simp [Complex.norm_real, abs_of_nonneg hx_mem.1, hx_mem.2]))
  have him : ‖I • ∫ y in (0 : ℝ)..z.im, f (z.re + y * I)‖ ≤ 2 * C₀ * ‖z‖ ^ 2 := by
    rw [norm_smul, norm_I, one_mul]
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := 2 * C₀ * ‖z‖) fun y hy => ?_
      ).trans ((mul_le_mul_of_nonneg_left (by simpa using abs_im_le_norm z : |z.im - 0| ≤ ‖z‖)
        (by positivity)).trans_eq (by ring))
    have hy_abs : |y| ≤ |z.im| := by
      rcases mem_uIcc.1 (uIoc_subset_uIcc hy) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
        exact abs_le.2 ⟨by linarith [le_abs_self z.im, neg_abs_le z.im, abs_nonneg z.im],
          by linarith [le_abs_self z.im, neg_abs_le z.im, abs_nonneg z.im]⟩
    have hy_norm : ‖(z.re : ℂ) + y * I‖ ≤ 2 * ‖z‖ := by
      have hle := norm_le_abs_re_add_abs_im ((z.re : ℂ) + y * I)
      simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
        add_zero, add_im, mul_im, zero_add] at hle
      have hre_abs : |z.re| ≤ 1 := abs_le.2 ⟨by linarith, hz1'⟩
      linarith [abs_im_le_norm z]
    calc ‖f ((z.re : ℂ) + y * I)‖
        ≤ C₀ * ‖(z.re : ℂ) + y * I‖ := hf (by simp [hz0, hz1'])
      _ ≤ C₀ * (2 * ‖z‖) := mul_le_mul_of_nonneg_left hy_norm hC₀
      _ = 2 * C₀ * ‖z‖ := by ring
  have hz_sq : 1 ≤ ‖z‖ ^ 2 := by nlinarith
  simp only [wedgeIntegral, ofReal_re, ofReal_im, ofReal_zero, zero_mul, add_zero]
  calc ‖(∫ x in θ..z.re, f x) + I • ∫ y in (0 : ℝ)..z.im, f (z.re + y * I)‖
      ≤ C₀ + 2 * C₀ * ‖z‖ ^ 2 := (norm_add_le _ _).trans (add_le_add hre him)
    _ ≤ C₀ * ‖z‖ ^ 2 + 2 * C₀ * ‖z‖ ^ 2 := add_le_add (le_mul_of_one_le_right hC₀ hz_sq) le_rfl
    _ = 3 * C₀ * ‖z‖ ^ 2 := by ring

/-- Quadratic-exponential growth of the integrated-by-parts strip function on the open strip. -/
private theorem isBigO_exp_sq_ibp (hθ : θ ∈ Ioo 0 1) (M₀ M₁ : ℝ) (qY : D.upperStripTraces) :
    ∃ A B : ℝ,
      (fun z => scaleFactor M₀ M₁ z • D.upperStripFunction qY z -
        (Real.log M₀ - Real.log M₁ : ℂ) •
          wedgeIntegral θ z (fun w => scaleFactor M₀ M₁ w • D.upperStripFunction qY w))
        =O[cobounded ℂ ⊓ 𝓟 (verticalStrip 0 1)] fun w => Real.exp (B * ‖w‖ ^ A) := by
  let a : ℂ := Real.log M₀ - Real.log M₁
  let s := scaleFactor M₀ M₁
  let H := D.upperStripFunction qY
  set S := Real.exp (|Real.log M₀| + |Real.log M₁|)
  set B := S * ‖qY‖ + ‖a‖ * (3 * S * ‖qY‖) + 1
  refine ⟨2, B, IsBigO.of_norm_eventuallyLE ?_⟩
  filter_upwards [(tendsto_norm_cobounded_atTop.eventually (eventually_ge_atTop 1)).filter_mono
      inf_le_left,
    (eventually_mem_principal (verticalStrip 0 1)).filter_mono inf_le_right] with z hz1 hz
  have hz_cl := verticalStrip_subset_verticalClosedStrip 0 1 hz
  have hsH {w : ℂ} (hw : w ∈ verticalClosedStrip 0 1) : ‖s w • H w‖ ≤ S * ‖qY‖ * ‖w‖ := by
    rw [norm_smul]; exact (mul_le_mul (norm_scaleFactor_le hw) (D.norm_upperStripFunction_le qY w)
      (norm_nonneg _) (by positivity)).trans_eq (mul_assoc _ _ _).symm
  have hw : ‖wedgeIntegral θ z (fun w => s w • H w)‖ ≤ 3 * S * ‖qY‖ * ‖z‖ ^ 2 :=
    (norm_wedgeIntegral_le_of_linear (f := fun w => s w • H w) (by positivity) hsH
      ⟨hθ.1.le, hθ.2.le⟩ hz_cl hz1).trans_eq (by ring)
  have h1 : ‖s z • H z‖ ≤ S * ‖qY‖ * ‖z‖ ^ 2 :=
    (hsH hz_cl).trans (mul_le_mul_of_nonneg_left (by nlinarith) (by positivity))
  have h2 : ‖a • wedgeIntegral θ z (fun w => s w • H w)‖ ≤ ‖a‖ * (3 * S * ‖qY‖) * ‖z‖ ^ 2 := by
    rw [norm_smul, mul_assoc]; exact mul_le_mul_of_nonneg_left hw (norm_nonneg a)
  rw [Real.rpow_two]
  exact (((norm_sub_le _ _).trans (add_le_add h1 h2)).trans
    (by dsimp [B]; nlinarith [sq_nonneg ‖z‖])).trans
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
  let K : ℂ → D.SumSpace := fun z => s z • H z - a • wedgeIntegral θ z (fun w => s w • H w)
  have hf : DiffContOnCl ℂ (fun w => s w • H w) (verticalStrip 0 1) :=
    (differentiable_scaleFactor M₀ M₁).diffContOnCl.smul hH.diffContOnCl
  have hdK : DiffContOnCl ℂ K (verticalStrip 0 1) :=
    hf.sub ((hf.diffContOnCl_wedgeIntegral_verticalStrip zero_lt_one hθ_cl).const_smul a)
  have hderivK : toSum (s θ • map θ T₀ T₁ h (mk θ g)) = deriv K θ := by
    have hKθ : HasDerivAt K (s θ • deriv H θ) θ := by
      convert ((hasDerivAt_scaleFactor M₀ M₁ θ).smul (hH.differentiableAt hθ_open).hasDerivAt).sub
        ((hf.hasDerivAt_wedgeIntegral_verticalStrip zero_lt_one hθ_cl hθ_open).const_smul a) using 1
      rw [smul_smul]; abel
    rw [hKθ.deriv, map_smul, map_mk, toSum_mk, D.upperStripDerivEval_apply hθ_open]
  have hqY₀ := norm_upperStripTracesMap_fst_le T₀ T₁ h hM₀.le h₀ g
  have hqY₁ := norm_upperStripTracesMap_snd_le T₀ T₁ h hM₁.le h₁ g
  have hlip₀ := lipschitzWith_ibpCurve (M₀ := M₀) (M₁ := M₁) (c := 0) hM₀ (L := ‖g‖₊)
    (fun t => by simpa using norm_scaleFactor_mul_I (M₁ := M₁) hM₀ t)
    hH.lipschitzWith_fstBoundary.continuous
    (fun t t₀ => (hH.norm_fstBoundary_sub_le t t₀).trans
      (mul_le_mul_of_nonneg_right hqY₀ (abs_nonneg _)))
  have hlip₁ := lipschitzWith_ibpCurve (M₀ := M₀) (M₁ := M₁) (c := 1) hM₁ (L := ‖g‖₊)
    (fun t => by simpa using norm_scaleFactor_one_add_mul_I (M₀ := M₀) hM₁ t)
    hH.lipschitzWith_sndBoundary.continuous
    (fun t t₀ => (hH.norm_sndBoundary_sub_le t t₀).trans
      (mul_le_mul_of_nonneg_right hqY₁ (abs_nonneg _)))
  simpa using norm_le_of_lipschitz hθ hdK (isBigO_exp_sq_ibp hθ M₀ M₁ qY) hlip₀ hlip₁
    (fun t t₀ => by
      simpa [K] using wedgeIntegral_ibp_sub_eq (M₀ := M₀) (M₁ := M₁) (c := 0) hH.diffContOnCl hθ_cl
        D.fstToSum ⟨le_rfl, zero_le_one⟩ hH.lipschitzWith_fstBoundary.continuous
        (u₀ := 0) (fun u => by simpa [H] using (hH.fstToSum_fstBoundary u).symm) t t₀)
    (fun t t₀ => by
      simpa [K] using wedgeIntegral_ibp_sub_eq (M₀ := M₀) (M₁ := M₁) (c := 1) hH.diffContOnCl hθ_cl
        D.sndToSum ⟨zero_le_one, le_rfl⟩ hH.lipschitzWith_sndBoundary.continuous (u₀ := H 1)
        (fun u => by
          have := hH.sndToSum_sndBoundary u
          simp only [ofReal_one] at ⊢
          exact (eq_sub_iff_add_eq.1 this).symm) t t₀)
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

/-- **Bergh–Löfström Theorem 4.1.2 (exact interpolation for Calderón's upper method).** When `Y₀`
and `Y₁` are complete, if `‖T₀ x‖ ≤ M₀ * ‖x‖` and `‖T₁ x‖ ≤ M₁ * ‖x‖` with `M₀, M₁ ≥ 0`, then for
`0 < θ < 1` the induced map `[X₀, X₁]^θ → [Y₀, Y₁]^θ` satisfies
`‖map θ T₀ T₁ h u‖ ≤ M₀ ^ (1 - θ) * M₁ ^ θ * ‖u‖`. -/
theorem norm_map_le [CompleteSpace Y₀] [CompleteSpace Y₁] (hθ : θ ∈ Ioo 0 1) {M₀ M₁ : ℝ}
    (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁) (h₀ : ∀ x, ‖T₀ x‖ ≤ M₀ * ‖x‖) (h₁ : ∀ x, ‖T₁ x‖ ≤ M₁ * ‖x‖)
    (u : C.UpperComplexMethodSpace θ) :
    ‖map θ T₀ T₁ h u‖ ≤ M₀ ^ (1 - θ) * M₁ ^ θ * ‖u‖ := by
  have hle (ε : ℝ) (hε : 0 < ε) :
      ‖map θ T₀ T₁ h u‖ ≤ (M₀ + ε) ^ (1 - θ) * (M₁ + ε) ^ θ * ‖u‖ :=
    norm_map_le_of_pos T₀ T₁ h hθ (by positivity) (by positivity)
      (fun x => (h₀ x).trans (by gcongr; linarith))
      (fun x => (h₁ x).trans (by gcongr; linarith)) u
  have hcont : Continuous fun ε : ℝ => (M₀ + ε) ^ (1 - θ) * (M₁ + ε) ^ θ * ‖u‖ :=
    (((continuous_const.add continuous_id).rpow_const fun _ => Or.inr (sub_nonneg.2 hθ.2.le)).mul
      ((continuous_const.add continuous_id).rpow_const fun _ => Or.inr hθ.1.le)).mul
        continuous_const
  have hlim := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  simp only [add_zero] at hlim
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall hle)

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
