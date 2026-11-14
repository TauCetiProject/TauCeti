/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Interpolation.ComplexMethod.Upper.StripFunction
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Calderón's upper complex interpolation space

For a compatible couple `(X₀, X₁)` of complex normed spaces and `0 < θ < 1`, Calderón's *upper*
complex interpolation space `[X₀, X₁]^θ` consists of the complex derivatives `deriv G θ` of upper
strip functions `G` (`CompatibleCouple.IsUpperStripFunction`), normed by the infimum of the
boundary difference-quotient bounds `max ‖q₀‖ ‖q₁‖` over all `G` with `deriv G θ = u`.

Whereas the lower space `[X₀, X₁]_θ` (`CompatibleCouple.ComplexMethodSpace`) uses bounded strip
functions whose boundary traces vanish at infinity, the upper space allows antiderivatives with
Lipschitz boundary curves and serves as the target of Calderón's duality theorem
`([X₀, X₁]_θ)* = [X₀*, X₁*]^θ` on regular couples.

Following the quotient-of-traces architecture of
`TauCeti.Analysis.Normed.Interpolation.ComplexMethod.Basic`, we realise the space of upper strip
functions modulo constants by their boundary difference quotients:

* `CompatibleCouple.upperStripTraces`: the submodule of
  `(offDiag univ →ᵇ X₀) × (offDiag univ →ᵇ X₁)` consisting of boundary difference quotients of
  upper strip functions, closed and complete when `X₀` and `X₁` are complete
  (`CompatibleCouple.isClosed_upperStripTraces`);
* `CompatibleCouple.upperStripFunction g`: the canonical upper strip function with boundary
  difference quotients `g` normalized by `G 0 = 0`, and `CompatibleCouple.upperStripDerivEval z`,
  the continuous linear evaluation `g ↦ deriv G z` of norm at most one on `0 < re z < 1`;
* `CompatibleCouple.UpperComplexMethodSpace θ`: the quotient of `upperStripTraces` by the kernel
  of `upperStripDerivEval θ`, a Banach space when `X₀` and `X₁` are complete, with contractive
  injective inclusion `UpperComplexMethodSpace.toSum` into `X₀ + X₁`;
* `UpperComplexMethodSpace.ofInter` and `UpperComplexMethodSpace.norm_refl`: contractive inclusion
  of `X₀ ∩ X₁` via `z ↦ z • x` without completeness assumptions, and isometric identification of
  `[X, X]^θ` with `X`.

Functoriality, exact interpolation of exponent `θ` (Bergh–Löfström, Theorem 4.1.2), retracts, and
endpoint isomorphisms are proved in
`TauCeti.Analysis.Normed.Interpolation.ComplexMethod.Upper.Map`.

## References

* A.-P. Calderón, *Intermediate spaces and interpolation, the complex method*, Studia Math. 24
  (1964), 113–190, §§5–6.
* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Grundlehren 223,
  Springer, 1976, §4.1 and §4.2.
* M. Cwikel, *Lecture notes on duality and interpolation spaces*, arXiv:0803.3558 (2008), §2.4.
-/

public noncomputable section

open Asymptotics Bornology Complex Complex.HadamardThreeLines Filter Set Topology
open scoped BoundedContinuousFunction NNReal

namespace TauCeti

open Complex.HadamardThreeLines

namespace CompatibleCouple

variable {X₀ X₁ V : Type*}
  [NormedAddCommGroup X₀] [NormedSpace ℂ X₀] [NormedAddCommGroup X₁] [NormedSpace ℂ X₁]
  [AddCommGroup V] [Module ℂ V] [TopologicalSpace V] [ContinuousAdd V] [T1Space V]
  (C : CompatibleCouple ℂ X₀ X₁ V)

/-! ### The space of upper boundary traces -/

/-- The boundary difference quotients `(q₀, q₁)` of upper strip functions of `(X₀, X₁)`, a
submodule of `(offDiag univ →ᵇ X₀) × (offDiag univ →ᵇ X₁)` normed by `max ‖q₀‖ ‖q₁‖`. -/
def upperStripTraces :
    Submodule ℂ ((offDiag (univ : Set ℝ) →ᵇ X₀) × (offDiag (univ : Set ℝ) →ᵇ X₁)) where
  carrier := {q | ∃ G, C.IsUpperStripFunction G q}
  add_mem' := fun ⟨G, hG⟩ ⟨H, hH⟩ => ⟨G + H, hG.add hH⟩
  zero_mem' := ⟨0, IsUpperStripFunction.zero⟩
  smul_mem' c _ := fun ⟨G, hG⟩ => ⟨c • G, hG.const_smul c⟩

variable {C} in
theorem mem_upperStripTraces_iff
    {q : (offDiag (univ : Set ℝ) →ᵇ X₀) × (offDiag (univ : Set ℝ) →ᵇ X₁)} :
    q ∈ C.upperStripTraces ↔ ∃ G, C.IsUpperStripFunction G q :=
  Iff.rfl

/-- The canonical upper strip function with boundary difference quotients `g`, normalized by
`G 0 = 0` on the closed strip and extended by zero outside `verticalClosedStrip 0 1`. -/
def upperStripFunction (g : C.upperStripTraces) : ℂ → C.SumSpace :=
  (verticalClosedStrip 0 1).indicator fun z =>
    (mem_upperStripTraces_iff.1 g.2).choose z - (mem_upperStripTraces_iff.1 g.2).choose 0

theorem isUpperStripFunction_upperStripFunction (g : C.upperStripTraces) :
    C.IsUpperStripFunction (C.upperStripFunction g) g := by
  refine ((mem_upperStripTraces_iff.1 g.2).choose_spec.sub_const
    ((mem_upperStripTraces_iff.1 g.2).choose 0)).congr fun z hz => ?_
  simp [upperStripFunction, indicator_of_mem hz]

@[simp]
theorem upperStripFunction_apply_zero (g : C.upperStripTraces) :
    C.upperStripFunction g 0 = 0 := by
  simp [upperStripFunction]

variable {C} in
theorem upperStripFunction_eq {g : C.upperStripTraces} {G : ℂ → C.SumSpace}
    (hG : C.IsUpperStripFunction G g) {z : ℂ} (hz : z ∈ verticalClosedStrip 0 1) :
    C.upperStripFunction g z = G z - G 0 := by
  simpa using (C.isUpperStripFunction_upperStripFunction g).eqOn_sub_apply_zero hG hz

variable {C} in
theorem deriv_upperStripFunction_eq {g : C.upperStripTraces} {G : ℂ → C.SumSpace}
    (hG : C.IsUpperStripFunction G g) {z : ℂ} (hz : z ∈ verticalStrip 0 1) :
    deriv (C.upperStripFunction g) z = deriv G z :=
  (C.isUpperStripFunction_upperStripFunction g).deriv_eq hG hz

@[simp]
theorem upperStripFunction_eq_zero (g : C.upperStripTraces) {z : ℂ}
    (hz : z ∉ verticalClosedStrip 0 1) : C.upperStripFunction g z = 0 :=
  indicator_of_notMem hz _

@[simp]
theorem upperStripFunction_zero : C.upperStripFunction 0 = 0 := by
  ext z
  by_cases hz : z ∈ verticalClosedStrip 0 1
  · simpa using upperStripFunction_eq (g := 0) IsUpperStripFunction.zero hz
  · exact C.upperStripFunction_eq_zero _ hz

@[simp]
theorem upperStripFunction_add (g h : C.upperStripTraces) :
    C.upperStripFunction (g + h) = C.upperStripFunction g + C.upperStripFunction h := by
  ext z
  by_cases hz : z ∈ verticalClosedStrip 0 1
  · simpa using upperStripFunction_eq (g := g + h)
      ((C.isUpperStripFunction_upperStripFunction g).add
        (C.isUpperStripFunction_upperStripFunction h)) hz
  · simp [C.upperStripFunction_eq_zero _ hz]

@[simp]
theorem upperStripFunction_smul (c : ℂ) (g : C.upperStripTraces) :
    C.upperStripFunction (c • g) = c • C.upperStripFunction g := by
  ext z
  by_cases hz : z ∈ verticalClosedStrip 0 1
  · simpa [smul_sub] using upperStripFunction_eq (g := c • g)
      ((C.isUpperStripFunction_upperStripFunction g).const_smul c) hz
  · simp [C.upperStripFunction_eq_zero _ hz]

theorem norm_upperStripFunction_le (g : C.upperStripTraces) (z : ℂ) :
    ‖C.upperStripFunction g z‖ ≤ ‖g‖ * ‖z‖ := by
  by_cases hz : z ∈ verticalClosedStrip 0 1
  · simpa using (C.isUpperStripFunction_upperStripFunction g).norm_sub_apply_zero_le hz
  · rw [C.upperStripFunction_eq_zero g hz, norm_zero]
    positivity

/-- Complex derivative evaluation `g ↦ deriv G z` on `upperStripTraces` for `z ∈ verticalStrip 0 1`
(extended by zero outside the open strip), a continuous linear map of norm at most one. -/
def upperStripDerivEval (z : ℂ) : C.upperStripTraces →L[ℂ] C.SumSpace :=
  open Classical in
  if hz : z ∈ verticalStrip 0 1 then
    LinearMap.mkContinuous
      { toFun g := deriv (C.upperStripFunction g) z
        map_add' g h := by
          rw [upperStripFunction_add]
          exact deriv_add ((C.isUpperStripFunction_upperStripFunction g).differentiableAt hz)
            ((C.isUpperStripFunction_upperStripFunction h).differentiableAt hz)
        map_smul' c g := by
          rw [upperStripFunction_smul, RingHom.id_apply]
          exact deriv_const_smul c
            ((C.isUpperStripFunction_upperStripFunction g).differentiableAt hz) }
      1 fun g => by simpa using (C.isUpperStripFunction_upperStripFunction g).norm_deriv_le hz
  else 0

theorem upperStripDerivEval_apply {z : ℂ} (hz : z ∈ verticalStrip 0 1) (g : C.upperStripTraces) :
    C.upperStripDerivEval z g = deriv (C.upperStripFunction g) z := by
  simp [upperStripDerivEval, hz]

variable {C} in
theorem upperStripDerivEval_eq_deriv {z : ℂ} (hz : z ∈ verticalStrip 0 1) {g : C.upperStripTraces}
    {G : ℂ → C.SumSpace} (hG : C.IsUpperStripFunction G g) :
    C.upperStripDerivEval z g = deriv G z := by
  rw [C.upperStripDerivEval_apply hz, deriv_upperStripFunction_eq hG hz]

@[simp]
theorem upperStripDerivEval_eq_zero {z : ℂ} (hz : z ∉ verticalStrip 0 1) :
    C.upperStripDerivEval z = 0 := by
  simp [upperStripDerivEval, hz]

theorem norm_upperStripDerivEval_le (z : ℂ) : ‖C.upperStripDerivEval z‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun g => ?_
  by_cases hz : z ∈ verticalStrip 0 1
  · rw [C.upperStripDerivEval_apply hz, one_mul]
    exact (C.isUpperStripFunction_upperStripFunction g).norm_deriv_le hz
  · simp [C.upperStripDerivEval_eq_zero hz]

private theorem tendstoLocallyUniformlyOn_upperStripFunction [CompleteSpace X₀] [CompleteSpace X₁]
    {u : ℕ → C.upperStripTraces}
    {q : (offDiag (univ : Set ℝ) →ᵇ X₀) × (offDiag (univ : Set ℝ) →ᵇ X₁)}
    (hlim : Tendsto (fun n => (u n).1) atTop (𝓝 q)) :
    TendstoLocallyUniformlyOn (fun n => C.upperStripFunction (u n))
      (fun z => limUnder atTop fun n => C.upperStripFunction (u n) z)
      atTop (verticalClosedStrip 0 1) := by
  have hdist (n m : ℕ) {z : ℂ} (hz : z ∈ verticalClosedStrip 0 1) :
      ‖C.upperStripFunction (u n) z - C.upperStripFunction (u m) z‖ ≤
        ‖(u n).1 - (u m).1‖ * ‖z‖ := by
    simpa using ((C.isUpperStripFunction_upperStripFunction (u n)).sub
      (C.isUpperStripFunction_upperStripFunction (u m))).norm_sub_apply_zero_le hz
  have hlimz {z : ℂ} (hz : z ∈ verticalClosedStrip 0 1) :
      Tendsto (fun n => C.upperStripFunction (u n) z) atTop
        (𝓝 (limUnder atTop fun n => C.upperStripFunction (u n) z)) := by
    refine (Metric.cauchySeq_iff'.2 fun ε hε => ?_).tendsto_limUnder
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.1 hlim.cauchySeq (ε / (‖z‖ + 1)) (by positivity)
    refine ⟨N, fun n hn => ?_⟩
    rw [dist_eq_norm]
    calc ‖C.upperStripFunction (u n) z - C.upperStripFunction (u N) z‖
        ≤ ‖(u n).1 - (u N).1‖ * (‖z‖ + 1) :=
          (hdist n N hz).trans
            (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) (norm_nonneg _))
      _ < ε / (‖z‖ + 1) * (‖z‖ + 1) :=
          mul_lt_mul_of_pos_right (by simpa [dist_eq_norm] using hN n hn) (by positivity)
      _ = ε := div_mul_cancel₀ ε (by positivity)
  rw [Metric.tendstoLocallyUniformlyOn_iff]
  intro ε hε z₀ _
  refine ⟨verticalClosedStrip 0 1 ∩ Metric.ball z₀ 1,
    inter_mem_nhdsWithin _ (Metric.ball_mem_nhds z₀ zero_lt_one), ?_⟩
  have hq : Tendsto (fun n => ‖(u n).1 - q‖) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1 hlim
  filter_upwards [hq.eventually (gt_mem_nhds (div_pos hε (by positivity : 0 < ‖z₀‖ + 1)))]
    with n hn z ⟨hz, hzball⟩
  have hznorm : ‖z‖ ≤ ‖z₀‖ + 1 := by
    have := norm_sub_norm_le z z₀
    have hzb : ‖z - z₀‖ < 1 := by simpa [dist_eq_norm] using hzball
    linarith
  rw [dist_eq_norm, norm_sub_rev]
  have hlim_sub := le_of_tendsto_of_tendsto' (tendsto_const_nhds.sub (hlimz hz)).norm
    ((tendsto_const_nhds.sub hlim).norm.mul_const ‖z‖) fun m => hdist n m hz
  calc ‖C.upperStripFunction (u n) z - limUnder atTop fun m => C.upperStripFunction (u m) z‖
      ≤ ‖(u n).1 - q‖ * (‖z₀‖ + 1) :=
        hlim_sub.trans (mul_le_mul_of_nonneg_left hznorm (norm_nonneg _))
    _ < ε / (‖z₀‖ + 1) * (‖z₀‖ + 1) := mul_lt_mul_of_pos_right hn (by positivity)
    _ = ε := div_mul_cancel₀ ε (by positivity)

/-- When `X₀` and `X₁` are complete, `upperStripTraces` is a closed subspace of
`(offDiag univ →ᵇ X₀) × (offDiag univ →ᵇ X₁)`. -/
theorem isClosed_upperStripTraces [CompleteSpace X₀] [CompleteSpace X₁] :
    IsClosed (C.upperStripTraces :
      Set ((offDiag (univ : Set ℝ) →ᵇ X₀) × (offDiag (univ : Set ℝ) →ᵇ X₁))) := by
  refine IsSeqClosed.isClosed fun {u q} hu hlim => ?_
  let v : ℕ → C.upperStripTraces := fun n => ⟨u n, hu n⟩
  have hG (n : ℕ) : C.IsUpperStripFunction (C.upperStripFunction (v n)) (u n) :=
    C.isUpperStripFunction_upperStripFunction (v n)
  have hloc := C.tendstoLocallyUniformlyOn_upperStripFunction (u := v) hlim
  have hlimz {z : ℂ} (hz : z ∈ verticalClosedStrip 0 1) := hloc.tendsto_at hz
  refine ⟨_, ⟨⟨(hloc.mono (verticalStrip_subset_verticalClosedStrip 0 1)).differentiableOn
      (.of_forall fun n => (hG n).diffContOnCl.differentiableOn) (isOpen_verticalStrip 0 1),
    closure_verticalStrip zero_lt_one ▸ hloc.continuousOn
      (.of_forall fun n => (hG n).diffContOnCl.continuousOn_verticalClosedStrip zero_lt_one)⟩,
    ⟨‖q‖, fun w hw => ?_⟩, fun {t s} h => ?_, fun {t s} h => ?_⟩⟩
  · have hGw := le_of_tendsto_of_tendsto' (hlimz hw).norm (hlim.norm.mul_const ‖w‖) fun n => by
      simpa using (hG n).norm_sub_apply_zero_le hw
    have hre : |w.re| ≤ 1 := abs_le.2 ⟨by linarith [hw.1], hw.2⟩
    exact hGw.trans (mul_le_mul_of_nonneg_left
      ((norm_le_abs_re_add_abs_im w).trans (add_le_add_left hre _)) (norm_nonneg q))
  · set p : offDiag (univ : Set ℝ) := ⟨(t, s), ⟨trivial, trivial, h⟩⟩
    have hp : Tendsto (fun n => (u n).1 p) atTop (𝓝 (q.1 p)) := by
      simpa [Function.comp_def] using
        ((BoundedContinuousFunction.evalCLM ℂ p).continuous.tendsto _).comp
          ((continuous_fst.tendsto q).comp hlim)
    refine tendsto_nhds_unique ((hlimz (by simp)).sub (hlimz (by simp))) ?_
    simp_rw [(hG _).sub_mul_I h]
    exact ((continuous_const_smul (t - s : ℂ)).tendsto _).comp
      ((C.fstToSum.continuous.tendsto _).comp hp)
  · set p : offDiag (univ : Set ℝ) := ⟨(t, s), ⟨trivial, trivial, h⟩⟩
    have hp : Tendsto (fun n => (u n).2 p) atTop (𝓝 (q.2 p)) := by
      simpa [Function.comp_def] using
        ((BoundedContinuousFunction.evalCLM ℂ p).continuous.tendsto _).comp
          ((continuous_snd.tendsto q).comp hlim)
    refine tendsto_nhds_unique ((hlimz (by simp)).sub (hlimz (by simp))) ?_
    simp_rw [(hG _).sub_one_add_mul_I h]
    exact ((continuous_const_smul (t - s : ℂ)).tendsto _).comp
      ((C.sndToSum.continuous.tendsto _).comp hp)

instance [CompleteSpace X₀] [CompleteSpace X₁] : CompleteSpace C.upperStripTraces :=
  C.isClosed_upperStripTraces.completeSpace_coe

instance (z : ℂ) : IsClosed ((C.upperStripDerivEval z).ker : Set C.upperStripTraces) :=
  (C.upperStripDerivEval z).isClosed_ker

/-! ### Calderón's upper complex interpolation space -/

/-- Calderón's upper complex interpolation space `[X₀, X₁]^θ`, for `0 < θ < 1`: the quotient of
`upperStripTraces` by the kernel of `upperStripDerivEval θ`, with quotient norm
`‖u‖^[θ] = inf {‖q‖ | deriv G θ = u for an upper strip function G with difference quotients q}`
(`UpperComplexMethodSpace.norm_lt_iff`). It is a Banach space when `X₀` and `X₁` are complete, and
embeds contractively and injectively into the sum space via `UpperComplexMethodSpace.toSum`. For
`θ ∉ Ioo 0 1`, `upperStripDerivEval θ = 0`, so the space is zero
(`UpperComplexMethodSpace.eq_zero_of_notMem`). -/
def UpperComplexMethodSpace (θ : ℝ) : Type _ :=
  C.upperStripTraces ⧸ (C.upperStripDerivEval θ).ker

namespace UpperComplexMethodSpace

variable {C} {θ : ℝ}

instance : NormedAddCommGroup (C.UpperComplexMethodSpace θ) :=
  inferInstanceAs (NormedAddCommGroup (C.upperStripTraces ⧸ (C.upperStripDerivEval θ).ker))

instance : NormedSpace ℂ (C.UpperComplexMethodSpace θ) :=
  inferInstanceAs (NormedSpace ℂ (C.upperStripTraces ⧸ (C.upperStripDerivEval θ).ker))

instance [CompleteSpace X₀] [CompleteSpace X₁] : CompleteSpace (C.UpperComplexMethodSpace θ) :=
  inferInstanceAs (CompleteSpace (C.upperStripTraces ⧸ (C.upperStripDerivEval θ).ker))

variable (θ) in
/-- The class in `[X₀, X₁]^θ` of the upper strip function with boundary difference quotients `g`. -/
def mk : C.upperStripTraces →L[ℂ] C.UpperComplexMethodSpace θ :=
  (C.upperStripDerivEval θ).ker.mkQL

theorem mk_surjective :
    Function.Surjective (mk θ : C.upperStripTraces → C.UpperComplexMethodSpace θ) :=
  Submodule.mkQ_surjective _

theorem mk_eq_mk_iff {g h : C.upperStripTraces} :
    mk θ g = mk θ h ↔ C.upperStripDerivEval θ g = C.upperStripDerivEval θ h := by
  rw [← sub_eq_zero, ← map_sub, ← sub_eq_zero (a := C.upperStripDerivEval θ g), ← map_sub]
  exact Submodule.Quotient.mk_eq_zero _

/-- The quotient norm of `[X₀, X₁]^θ`: `‖u‖ < r` if and only if `u` is represented by boundary
difference quotients of norm strictly less than `r`. -/
theorem norm_lt_iff {u : C.UpperComplexMethodSpace θ} {r : ℝ} :
    ‖u‖ < r ↔ ∃ g, mk θ g = u ∧ ‖g‖ < r :=
  QuotientAddGroup.norm_lt_iff

theorem norm_mk_le (g : C.upperStripTraces) : ‖mk θ g‖ ≤ ‖g‖ :=
  Submodule.Quotient.norm_mk_le _ g

section Lift

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]

/-- A continuous linear map on `upperStripTraces` descends to `[X₀, X₁]^θ` when it vanishes on
traces whose derivative at `θ` is zero. -/
def lift (A : C.upperStripTraces →L[ℂ] E) (hA : ∀ g, C.upperStripDerivEval θ g = 0 → A g = 0) :
    C.UpperComplexMethodSpace θ →L[ℂ] E :=
  (C.upperStripDerivEval θ).ker.liftQL A hA

@[simp]
theorem lift_mk (A : C.upperStripTraces →L[ℂ] E)
    (hA : ∀ g, C.upperStripDerivEval θ g = 0 → A g = 0) (g : C.upperStripTraces) :
    lift A hA (mk θ g) = A g :=
  (rfl)

theorem lift_unique (A : C.upperStripTraces →L[ℂ] E)
    (hA : ∀ g, C.upperStripDerivEval θ g = 0 → A g = 0)
    {T : C.UpperComplexMethodSpace θ →L[ℂ] E} (hT : ∀ g, T (mk θ g) = A g) :
    T = lift A hA := by
  ext u
  obtain ⟨g, rfl⟩ := mk_surjective u
  simpa using hT g

end Lift

/-- The contractive injective inclusion `[X₀, X₁]^θ → X₀ + X₁`, sending `G` to `deriv G θ`. -/
def toSum : C.UpperComplexMethodSpace θ →L[ℂ] C.SumSpace :=
  (C.upperStripDerivEval θ).ker.liftQL (C.upperStripDerivEval θ) le_rfl

@[simp]
theorem toSum_mk (g : C.upperStripTraces) : toSum (mk θ g) = C.upperStripDerivEval θ g :=
  (rfl)

theorem toSum_injective :
    Function.Injective (toSum : C.UpperComplexMethodSpace θ → C.SumSpace) := by
  intro u v huv
  obtain ⟨g, rfl⟩ := mk_surjective u
  obtain ⟨h, rfl⟩ := mk_surjective v
  exact mk_eq_mk_iff.2 (by simpa using huv)

/-- Elements of `[X₀, X₁]^θ` are determined by their images in the sum space. -/
@[ext]
theorem ext {u v : C.UpperComplexMethodSpace θ} (h : toSum u = toSum v) : u = v :=
  toSum_injective h

/-- For `θ` outside `(0, 1)`, the space `[X₀, X₁]^θ` is zero. -/
theorem eq_zero_of_notMem (hθ : θ ∉ Ioo 0 1) (u : C.UpperComplexMethodSpace θ) : u = 0 := by
  ext
  obtain ⟨g, rfl⟩ := mk_surjective u
  rw [toSum_mk, C.upperStripDerivEval_eq_zero (by simpa using hθ), map_zero, zero_apply]

/-- The inclusion of `[X₀, X₁]^θ` into the sum space does not increase norms. -/
theorem norm_toSum_le (u : C.UpperComplexMethodSpace θ) : ‖toSum u‖ ≤ ‖u‖ := by
  refine le_of_forall_gt fun r hr => ?_
  obtain ⟨g, rfl, hg⟩ := norm_lt_iff.1 hr
  rw [toSum_mk]
  exact ((C.upperStripDerivEval θ).le_of_opNorm_le
    (C.norm_upperStripDerivEval_le θ) g).trans_lt (by simpa using hg)

theorem opNorm_toSum_le : ‖(toSum : C.UpperComplexMethodSpace θ →L[ℂ] C.SumSpace)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u => by simpa using norm_toSum_le u

/-- For `0 < θ < 1`, an element of the sum space lies in `[X₀, X₁]^θ` if and only if it is the
derivative at `θ` of an upper strip function. -/
theorem exists_toSum_eq_iff (hθ : θ ∈ Ioo 0 1) {u : C.SumSpace} :
    (∃ v : C.UpperComplexMethodSpace θ, toSum v = u) ↔
      ∃ G q, C.IsUpperStripFunction G q ∧ deriv G θ = u := by
  have hθ' : (θ : ℂ) ∈ verticalStrip 0 1 := by simpa using hθ
  constructor
  · rintro ⟨v, rfl⟩
    obtain ⟨g, rfl⟩ := mk_surjective v
    exact ⟨_, g, C.isUpperStripFunction_upperStripFunction g,
      (C.upperStripDerivEval_apply hθ' g).symm⟩
  · rintro ⟨G, q, hG, rfl⟩
    exact ⟨mk θ ⟨q, G, hG⟩, upperStripDerivEval_eq_deriv hθ' hG⟩

/-- For `0 < θ < 1`, an upper strip function `G` with boundary difference quotients `q` and
`deriv G θ = toSum u` bounds `‖u‖` by `‖q‖`. -/
theorem norm_le_of_toSum_eq (hθ : θ ∈ Ioo 0 1) {u : C.UpperComplexMethodSpace θ}
    {G : ℂ → C.SumSpace}
    {q : (offDiag (univ : Set ℝ) →ᵇ X₀) × (offDiag (univ : Set ℝ) →ᵇ X₁)}
    (hG : C.IsUpperStripFunction G q) (hu : toSum u = deriv G θ) : ‖u‖ ≤ ‖q‖ := by
  have hθ' : (θ : ℂ) ∈ verticalStrip 0 1 := by simpa using hθ
  have : u = mk θ ⟨q, G, hG⟩ := ext <| by
    rw [hu, toSum_mk, upperStripDerivEval_eq_deriv hθ' hG]
  exact this ▸ norm_mk_le _

/-- Norm bound in `[X₀, X₁]^θ` from Lipschitz boundary curves `g₀ : ℝ → X₀`, `g₁ : ℝ → X₁` of `G`
and finite-order strip growth. -/
theorem norm_le_of_lipschitz (hθ : θ ∈ Ioo 0 1) {u : C.UpperComplexMethodSpace θ}
    {G : ℂ → C.SumSpace} (hd : DiffContOnCl ℂ G (verticalStrip 0 1))
    (hgrowth : ∃ A B : ℝ, G =O[cobounded ℂ ⊓ 𝓟 (verticalStrip 0 1)]
      fun w => Real.exp (B * ‖w‖ ^ A))
    {g₀ : ℝ → X₀} {g₁ : ℝ → X₁} {K₀ K₁ : ℝ≥0}
    (hg₀ : LipschitzWith K₀ g₀) (hg₁ : LipschitzWith K₁ g₁)
    (h₀ : ∀ t s : ℝ, G (t * I) - G (s * I) = C.fstToSum (g₀ t - g₀ s))
    (h₁ : ∀ t s : ℝ, G (1 + t * I) - G (1 + s * I) = C.sndToSum (g₁ t - g₁ s))
    (hu : toSum u = deriv G θ) : ‖u‖ ≤ max (K₀ : ℝ) K₁ :=
  (norm_le_of_toSum_eq hθ (IsUpperStripFunction.of_lipschitz hd hgrowth hg₀ hg₁ h₀ h₁) hu).trans
    (max_le_max (norm_offDiagSlope_le hg₀) (norm_offDiagSlope_le hg₁))

end UpperComplexMethodSpace

/-! ### Inclusion of the intersection and the diagonal couple -/

section Inter

private def linearUpperTrace (x : C.inter) :
    (offDiag (univ : Set ℝ) →ᵇ X₀) × (offDiag (univ : Set ℝ) →ᵇ X₁) :=
  (BoundedContinuousFunction.const _ (I • C.interFst x),
    BoundedContinuousFunction.const _ (I • C.interSnd x))

private theorem isUpperStripFunction_linear (x : C.inter) :
    C.IsUpperStripFunction (fun z => z • C.fstToSum (C.interFst x)) (C.linearUpperTrace x) where
  diffContOnCl := (differentiable_id.smul_const _).diffContOnCl
  exists_norm_le := ⟨‖C.fstToSum (C.interFst x)‖, fun z hz => by
    have hre : |z.re| ≤ 1 := abs_le.2 ⟨by linarith [hz.1], hz.2⟩
    have hznorm : ‖z‖ ≤ 1 + |z.im| := (norm_le_abs_re_add_abs_im z).trans (add_le_add_left hre _)
    rw [norm_smul, mul_comm]
    exact mul_le_mul_of_nonneg_left hznorm (norm_nonneg _)⟩
  sub_mul_I _ := by
    simp only [linearUpperTrace, BoundedContinuousFunction.const_apply, map_smul]
    rw [← sub_smul, ← smul_assoc, smul_eq_mul]; congr 1; ring
  sub_one_add_mul_I _ := by
    simp only [linearUpperTrace, BoundedContinuousFunction.const_apply, ← C.fstToSum_interFst x,
      map_smul]
    rw [← sub_smul, ← smul_assoc, smul_eq_mul]; congr 1; ring

omit [ContinuousAdd V] [T1Space V] in
private theorem norm_linearUpperTrace_le (x : C.inter) : ‖C.linearUpperTrace x‖ ≤ ‖x‖ := by
  refine norm_prod_le_iff.2
    ⟨(BoundedContinuousFunction.norm_const_le _).trans ?_,
      (BoundedContinuousFunction.norm_const_le _).trans ?_⟩
  · simpa [norm_smul] using C.norm_interFst_le x
  · simpa [norm_smul] using C.norm_interSnd_le x

private def linearUpperTraceMap : C.inter →L[ℂ] C.upperStripTraces :=
  LinearMap.mkContinuous
    { toFun x := ⟨C.linearUpperTrace x, _, C.isUpperStripFunction_linear x⟩
      map_add' x y := Subtype.ext <| Prod.ext
        (BoundedContinuousFunction.ext fun _ => by simp [linearUpperTrace, smul_add])
        (BoundedContinuousFunction.ext fun _ => by simp [linearUpperTrace, smul_add])
      map_smul' c x := Subtype.ext <| Prod.ext
        (BoundedContinuousFunction.ext fun _ => by simp [linearUpperTrace, smul_comm I c])
        (BoundedContinuousFunction.ext fun _ => by simp [linearUpperTrace, smul_comm I c]) }
    1 fun x => by simpa using C.norm_linearUpperTrace_le x

namespace UpperComplexMethodSpace

variable {C}

variable (θ : ℝ) in
/-- The contractive inclusion `X₀ ∩ X₁ → [X₀, X₁]^θ`, sending `x` to the class of `z ↦ z • x`.
No completeness assumption on the endpoints is needed. -/
def ofInter : C.inter →L[ℂ] C.UpperComplexMethodSpace θ :=
  (mk θ).comp C.linearUpperTraceMap

@[simp]
theorem toSum_ofInter {θ : ℝ} (hθ : θ ∈ Ioo 0 1) (x : C.inter) :
    toSum (ofInter θ x) = C.fstToSum (C.interFst x) := by
  have hθ' : (θ : ℂ) ∈ verticalStrip 0 1 := by simpa using hθ
  rw [ofInter, ContinuousLinearMap.comp_apply, toSum_mk,
    upperStripDerivEval_eq_deriv hθ' (C.isUpperStripFunction_linear x)]
  simpa using ((hasDerivAt_id (θ : ℂ)).smul_const (C.fstToSum (C.interFst x))).deriv

/-- The intersection embeds into `[X₀, X₁]^θ` without increasing norms:
`‖ofInter θ x‖ ≤ max ‖x‖_{X₀} ‖x‖_{X₁}`. -/
theorem norm_ofInter_le (θ : ℝ) (x : C.inter) : ‖ofInter θ x‖ ≤ ‖x‖ :=
  (norm_mk_le _).trans (C.norm_linearUpperTrace_le x)

theorem opNorm_ofInter_le (θ : ℝ) :
    ‖(ofInter θ : C.inter →L[ℂ] C.UpperComplexMethodSpace θ)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by simpa using norm_ofInter_le θ x

/-- For the diagonal couple `(X, X)`, the upper complex method recovers the norm of `X` for every
`0 < θ < 1` (and is zero outside `(0, 1)`). -/
theorem norm_refl {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] {θ : ℝ}
    (u : (refl ℂ X).UpperComplexMethodSpace θ) : ‖u‖ = ‖toSum u‖ := by
  by_cases hθ : θ ∈ Ioo 0 1
  · refine le_antisymm ?_ (norm_toSum_le u)
    set x := (refl ℂ X).sumSpaceEmbed (toSum u)
    have hx : (x, x) ∈ (refl ℂ X).inter := by simp
    have hu : ofInter θ ⟨(x, x), hx⟩ = u := by ext; simp [toSum_ofInter hθ, x]
    calc ‖u‖ = ‖ofInter θ ⟨(x, x), hx⟩‖ := by rw [hu]
      _ ≤ ‖(⟨(x, x), hx⟩ : (refl ℂ X).inter)‖ := norm_ofInter_le θ _
      _ = ‖toSum u‖ := by simp [x, norm_refl_sumSpaceEmbed]
  · simp [eq_zero_of_notMem hθ u]

end UpperComplexMethodSpace

end Inter

end CompatibleCouple

end TauCeti
