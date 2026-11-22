/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Integral
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Probability.Independence.Basic
public import TauCeti.MeasureTheory.Integral.Exp.Matrix
import TauCeti.Analysis.Matrix.Eigenvalues.OperatorNorm
import TauCeti.Analysis.Matrix.MeasurableSpace
import TauCeti.Analysis.Matrix.Order
import TauCeti.Analysis.Matrix.Trace.Basic
import TauCeti.Analysis.Normed.Algebra.Basic
import TauCeti.MeasureTheory.Integral.Matrix
import TauCeti.MeasureTheory.Integral.PosSemidef
import TauCeti.Probability.Independence.Basic

/-!
# Matrix Laplace transform method

Tropp's matrix Laplace transform method for sums of independent random matrices over any `RCLike`
field `𝕜` (`ℝ` or `ℂ`). Expectations are written entrywise as
`Matrix.of fun i j ↦ ∫ ω, X ω i j ∂P`, coinciding with the Bochner integral under the `ℓ²` operator
norm for integrable matrix-valued functions (such as the exponentials of bounded-above measurable
matrices treated here). Combining Lieb's concavity
(`Matrix.IsHermitian.concaveOn_re_trace_exp_add_cfc_log`) with Jensen's inequality on
`exp X + ε • 1` and passing `ε → 0⁺` yields the single-step Lieb–Jensen bound under a one-sided
scalar Loewner upper bound, subadditivity of the matrix CGF, and master upper and lower eigenvalue

## Main results

* `Matrix.IsHermitian.integral_re_trace_exp_add_le`: the single-step Lieb–Jensen inequality.
* `ProbabilityTheory.iIndepFun.integral_re_trace_exp_add_sum_le`: subadditivity of the matrix CGF
  for independent random matrices bounded above in Loewner order (Tropp 2012, Lemma 3.4).
* `ProbabilityTheory.iIndepFun.measureReal_sSup_spectrum_sum_ge_le` and
  `ProbabilityTheory.iIndepFun.measureReal_sInf_spectrum_sum_le_le`: master Laplace-transform upper
  and lower eigenvalue tail bounds (Tropp 2012, Theorem 3.6).

## References

* J. A. Tropp, *User-friendly tail bounds for sums of random matrices*, Found. Comput. Math. 12
  (2012), 389–434, §3.
-/

public section

open MeasureTheory ProbabilityTheory Matrix Filter
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Topology

namespace Matrix

variable {Ω 𝕜 n : Type*} [MeasurableSpace Ω] {P : Measure Ω} [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜] [Fintype n] [DecidableEq n]

/-! ### Single-step Lieb–Jensen inequality -/

/-- **Single-step Lieb–Jensen inequality** (Tropp 2012, Corollary 3.3). For a fixed Hermitian
matrix `H` and a random matrix `X` satisfying an a.e. scalar Loewner upper bound `X ≤ M • 1`,
`E[Re Tr exp (H + X)] ≤ Re Tr exp (H + log E[exp X])`. -/
theorem IsHermitian.integral_re_trace_exp_add_le [IsProbabilityMeasure P]
    {H : Matrix n n 𝕜} (hH : H.IsHermitian) {X : Ω → Matrix n n 𝕜}
    (hmeas : AEMeasurable X P) {M : ℝ} (hupper : ∀ᵐ ω ∂P, X ω ≤ M • (1 : Matrix n n 𝕜)) :
    ∫ ω, RCLike.re (NormedSpace.exp (H + X ω)).trace ∂P ≤
      RCLike.re (NormedSpace.exp (H + cfc Real.log
        (Matrix.of fun i j ↦ ∫ ω, (NormedSpace.exp (X ω)) i j ∂P))).trace := by
  classical
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  let : NormedAlgebra ℚ (Matrix n n 𝕜) := TauCeti.normedAlgebraRatOfReal
  let g : Matrix n n 𝕜 → ℝ := fun A ↦ RCLike.re (NormedSpace.exp (H + cfc Real.log A)).trace
  let Y : Ω → Matrix n n 𝕜 := fun ω ↦ NormedSpace.exp (X ω)
  have hY_meas : AEMeasurable Y P :=
    (NormedSpace.exp_continuous (𝔸 := Matrix n n 𝕜)).measurable.comp_aemeasurable hmeas
  have hY_int : Integrable Y P := TauCeti.integrable_exp_of_ae_le_smul_one hmeas hupper
  have hY_bounds : ∀ᵐ ω ∂P, (Y ω).PosDef ∧ Y ω ≤ Real.exp M • (1 : Matrix n n 𝕜) :=
    hupper.mono fun _ hU ↦ ⟨(TauCeti.isHermitian_of_le_smul_one hU).posDef_exp,
      TauCeti.exp_le_exp_smul_one hU⟩
  have hg_cont : ContinuousOn g {A : Matrix n n 𝕜 | A.PosDef} :=
    TauCeti.continuous_re_trace.comp_continuousOn <|
      (NormedSpace.exp_continuous (𝔸 := Matrix n n 𝕜)).comp_continuousOn <|
        continuousOn_const.add (Matrix.contDiffOn_cfc_log (𝕜 := 𝕜) (n := n) (k := 0)).continuousOn
  have hg_aesm (ε : ℝ) (hε0 : 0 < ε) :
      AEStronglyMeasurable (fun ω ↦ g (Y ω + ε • (1 : Matrix n n 𝕜))) P := by
    let S : Set (Matrix n n 𝕜) := Set.Ici (ε • (1 : Matrix n n 𝕜))
    have hS_sub : S ⊆ {A : Matrix n n 𝕜 | A.PosDef} :=
      fun _ hA ↦ (PosDef.one.smul hε0).of_le hA
    have hp_meas : Measurable (S.piecewise g 0) :=
      (hg_cont.mono hS_sub).measurable_piecewise continuousOn_const isClosed_Ici.measurableSet
    have hYε_meas : AEMeasurable (fun ω ↦ Y ω + ε • (1 : Matrix n n 𝕜)) P :=
      (continuous_id.add continuous_const).measurable.comp_aemeasurable hY_meas
    refine (hp_meas.comp_aemeasurable hYε_meas).aestronglyMeasurable.congr ?_
    refine hY_bounds.mono fun ω ⟨hP, _⟩ ↦ Set.piecewise_eq_of_mem S g 0 ?_
    simpa [S] using add_le_add_right hP.posSemidef.nonneg (ε • (1 : Matrix n n 𝕜))
  have hg_bound (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
      ∀ᵐ ω ∂P, ‖g (Y ω + ε • (1 : Matrix n n 𝕜))‖ ≤
        (Fintype.card n : ℝ) * Real.exp (‖H‖ + Real.log (Real.exp M + 1)) := by
    refine hY_bounds.mono fun ω ⟨hP, hU⟩ ↦ ?_
    have hYε_pos : (Y ω + ε • (1 : Matrix n n 𝕜)).PosDef :=
      hP.add_posSemidef (PosDef.one.smul hε0).posSemidef
    have h1 : H ≤ ‖H‖ • (1 : Matrix n n 𝕜) := hH.le_smul_one_of_l2_opNorm_le le_rfl
    have hYε_le : Y ω + ε • (1 : Matrix n n 𝕜) ≤ (Real.exp M + 1) • (1 : Matrix n n 𝕜) := by
      have hε_le : ε • (1 : Matrix n n 𝕜) ≤ (1 : ℝ) • (1 : Matrix n n 𝕜) :=
        smul_le_smul_of_nonneg_right hε1.le zero_le_one
      exact (add_le_add hU hε_le).trans_eq (add_smul _ _ _).symm
    have hexp_pos : 0 < Real.exp M + 1 := by positivity
    have hherm_c : (Real.log (Real.exp M + 1) • (1 : Matrix n n 𝕜)).IsHermitian :=
      Matrix.isHermitian_one.smul (IsSelfAdjoint.all _)
    have hexp_c : NormedSpace.exp (Real.log (Real.exp M + 1) • (1 : Matrix n n 𝕜)) =
        (Real.exp M + 1) • (1 : Matrix n n 𝕜) := by
      rw [← Algebra.algebraMap_eq_smul_one, ← Algebra.algebraMap_eq_smul_one,
        ← NormedSpace.algebraMap_exp_comm, ← Real.exp_eq_exp_ℝ, Real.exp_log hexp_pos]
    have hlog_U : cfc Real.log (Y ω + ε • (1 : Matrix n n 𝕜)) ≤
        Real.log (Real.exp M + 1) • (1 : Matrix n n 𝕜) := by
      have hcmp := hYε_pos.cfc_log_le_cfc_log
        (B := NormedSpace.exp (Real.log (Real.exp M + 1) • (1 : Matrix n n 𝕜)))
        (hexp_c.symm ▸ hYε_le)
      rwa [hherm_c.cfc_log_exp] at hcmp
    have hlog_le : H + cfc Real.log (Y ω + ε • (1 : Matrix n n 𝕜)) ≤
        (‖H‖ + Real.log (Real.exp M + 1)) • (1 : Matrix n n 𝕜) :=
      (add_le_add h1 hlog_U).trans_eq (add_smul _ _ _).symm
    have h_nn : 0 ≤ g (Y ω + ε • (1 : Matrix n n 𝕜)) :=
      (hH.add (cfc_predicate Real.log
        (Y ω + ε • (1 : Matrix n n 𝕜))).isHermitian).re_trace_exp_nonneg
    rw [Real.norm_of_nonneg h_nn]
    exact TauCeti.re_trace_exp_le_card_mul_exp hlog_le
  have hstep (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
      ∫ ω, g (Y ω + ε • (1 : Matrix n n 𝕜)) ∂P ≤
        g ((Matrix.of fun i j ↦ ∫ ω, Y ω i j ∂P) + ε • (1 : Matrix n n 𝕜)) := by
    let S : Set (Matrix n n 𝕜) := Set.Ici (ε • (1 : Matrix n n 𝕜))
    have hS_sub : S ⊆ {A : Matrix n n 𝕜 | A.PosDef} :=
      fun _ hA ↦ (PosDef.one.smul hε0).of_le hA
    have hS_conv : Convex ℝ S := fun _ h₁ _ h₂ _ _ ha hb hab ↦ by
      simpa [S, ← add_smul, hab] using add_le_add
        (smul_le_smul_of_nonneg_left (Set.mem_Ici.1 h₁) ha)
        (smul_le_smul_of_nonneg_left (Set.mem_Ici.1 h₂) hb)
    have hYε_mem : ∀ᵐ ω ∂P, Y ω + ε • (1 : Matrix n n 𝕜) ∈ S :=
      hY_bounds.mono fun _ ⟨hP, _⟩ ↦
        by simpa [S] using add_le_add_right hP.posSemidef.nonneg (ε • (1 : Matrix n n 𝕜))
    have hjensen := (hH.concaveOn_re_trace_exp_add_cfc_log.subset hS_sub hS_conv).le_map_integral
      (hg_cont.mono hS_sub) isClosed_Ici hYε_mem (hY_int.add (integrable_const _))
      (Integrable.of_bound (hg_aesm ε hε0) _ (hg_bound ε hε0 hε1))
    have hYε_int_eq : ∫ ω, Y ω + ε • (1 : Matrix n n 𝕜) ∂P =
        (Matrix.of fun i j ↦ ∫ ω, Y ω i j ∂P) + ε • (1 : Matrix n n 𝕜) := by
      rw [integral_add hY_int (integrable_const _), integral_const, probReal_univ, one_smul,
        TauCeti.integral_l2Op_matrix_eq_of hY_int]
    rwa [hYε_int_eq] at hjensen
  have htend_g {A : Matrix n n 𝕜} (hA : A.PosDef) :
      Tendsto (fun ε : ℝ ↦ g (A + ε • (1 : Matrix n n 𝕜))) (𝓝[>] 0) (𝓝 (g A)) := by
    have hmap : Tendsto (fun ε : ℝ ↦ A + ε • (1 : Matrix n n 𝕜))
        (𝓝[>] 0) (𝓝[{B : Matrix n n 𝕜 | B.PosDef}] A) :=
      tendsto_nhdsWithin_iff.2 ⟨((continuous_const.add (continuous_id.smul continuous_const) :
          Continuous fun ε : ℝ ↦ A + ε • (1 : Matrix n n 𝕜)).tendsto' 0 A (by simp)).mono_left
          nhdsWithin_le_nhds,
        eventually_mem_nhdsWithin.mono fun ε hε ↦
          hA.add_posSemidef (PosDef.one.smul hε).posSemidef⟩
    exact (hg_cont A hA).tendsto.comp hmap
  have hRHS := htend_g (TauCeti.posDef_integral_exp hmeas hupper)
  have hLHS : Tendsto (fun ε : ℝ ↦ ∫ ω, g (Y ω + ε • (1 : Matrix n n 𝕜)) ∂P)
      (𝓝[>] 0) (𝓝 (∫ ω, RCLike.re (NormedSpace.exp (H + X ω)).trace ∂P)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun _ ↦ (Fintype.card n : ℝ) * Real.exp (‖H‖ + Real.log (Real.exp M + 1))) ?_ ?_
      (integrable_const _) ?_
    · filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with ε ⟨hε0, _⟩ using hg_aesm ε hε0
    · filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with ε ⟨hε0, hε1⟩ using hg_bound ε hε0 hε1
    · filter_upwards [hupper] with ω hU
      have hX_herm := TauCeti.isHermitian_of_le_smul_one hU
      have hg_eq : g (Y ω) = RCLike.re (NormedSpace.exp (H + X ω)).trace := by
        simp only [g, Y, hX_herm.cfc_log_exp]
      rw [← hg_eq]
      exact htend_g hX_herm.posDef_exp
  exact le_of_tendsto_of_tendsto hLHS hRHS <|
    eventually_of_mem (Ioo_mem_nhdsGT zero_lt_one) fun ε ⟨hε0, hε1⟩ ↦ hstep ε hε0 hε1

end Matrix

/-! ### Subadditivity of matrix CGF and master Laplace tail bounds -/

namespace ProbabilityTheory

variable {Ω 𝕜 n ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [RCLike 𝕜] [Fintype n] [DecidableEq n] [MeasurableSpace 𝕜] [BorelSpace 𝕜]

/-- One conditioning step of Tropp's subadditivity argument for two independent random matrices
`S` and `X` bounded above in Loewner order. -/
private theorem IndepFun.integral_re_trace_exp_add_add_le [IsProbabilityMeasure P]
    {S X : Ω → Matrix n n 𝕜} (hind : IndepFun S X P)
    (hS_meas : AEMeasurable S P) (hX_meas : AEMeasurable X P)
    {MS MX : ℝ} (hS_upper : ∀ᵐ ω ∂P, S ω ≤ MS • (1 : Matrix n n 𝕜))
    (hX_upper : ∀ᵐ ω ∂P, X ω ≤ MX • (1 : Matrix n n 𝕜))
    {H : Matrix n n 𝕜} (hH : H.IsHermitian) :
    ∫ ω, RCLike.re (NormedSpace.exp (H + S ω + X ω)).trace ∂P ≤
      ∫ ω, RCLike.re (NormedSpace.exp ((H + cfc Real.log
        (Matrix.of fun i j ↦ ∫ ω', (NormedSpace.exp (X ω')) i j ∂P)) + S ω)).trace ∂P := by
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  let : NormedAlgebra ℚ (Matrix n n 𝕜) := TauCeti.normedAlgebraRatOfReal
  let φ : Matrix n n 𝕜 × Matrix n n 𝕜 → ℝ :=
    fun p ↦ RCLike.re (NormedSpace.exp (H + p.1 + p.2)).trace
  have hφ_cont : Continuous φ :=
    TauCeti.continuous_re_trace.comp <| (NormedSpace.exp_continuous (𝔸 := Matrix n n 𝕜)).comp <|
      (continuous_const.add continuous_fst).add continuous_snd
  have hH_le : H ≤ ‖H‖ • (1 : Matrix n n 𝕜) := hH.le_smul_one_of_l2_opNorm_le le_rfl
  have hmap_prod := hind.map_prod_eq_prod_map_map hS_meas hX_meas
  have hφ_int_prod : Integrable φ ((P.map S).prod (P.map X)) :=
    hmap_prod ▸ (integrable_map_measure hφ_cont.aestronglyMeasurable (hS_meas.prodMk hX_meas)).2 <|
      TauCeti.integrable_re_trace_exp_of_ae_le_smul_one
        (((continuous_const.add continuous_fst).add continuous_snd).measurable.comp_aemeasurable
          (hS_meas.prodMk hX_meas))
        (M := ‖H‖ + MS + MX)
        ((hS_upper.and hX_upper).mono fun _ ⟨h1, h2⟩ ↦
          ((add_le_add (add_le_add hH_le h1) h2).trans_eq
            (by simp only [add_smul])))
  have hS_upper_map : ∀ᵐ A ∂(P.map S), A ≤ MS • (1 : Matrix n n 𝕜) :=
    (ae_map_iff hS_meas isClosed_Iic.measurableSet).2 hS_upper
  have hX_upper_map : ∀ᵐ B ∂(P.map X), B ≤ MX • (1 : Matrix n n 𝕜) :=
    (ae_map_iff hX_meas isClosed_Iic.measurableSet).2 hX_upper
  have hexp_map : (Matrix.of fun i j ↦ ∫ B, (NormedSpace.exp B) i j ∂(P.map X)) =
      Matrix.of fun i j ↦ ∫ ω, (NormedSpace.exp (X ω)) i j ∂P := by
    ext i j
    exact integral_map hX_meas ((continuous_apply j).comp ((continuous_apply i).comp
      (NormedSpace.exp_continuous (𝔸 := Matrix n n 𝕜)))).aestronglyMeasurable
  let L : Matrix n n 𝕜 := cfc Real.log (Matrix.of fun i j ↦ ∫ ω, (NormedSpace.exp (X ω)) i j ∂P)
  have hinner : ∀ᵐ A ∂(P.map S),
      (∫ B, φ (A, B) ∂(P.map X)) ≤ RCLike.re (NormedSpace.exp ((H + L) + A)).trace :=
    hS_upper_map.mono fun A hA ↦ by
      have hstep := (hH.add (TauCeti.isHermitian_of_le_smul_one hA)).integral_re_trace_exp_add_le
        (P := P.map X) aemeasurable_id hX_upper_map
      simp only [id_eq] at hstep
      rwa [hexp_map, add_right_comm H A L] at hstep
  have hrhs_cont : Continuous fun A : Matrix n n 𝕜 ↦
      RCLike.re (NormedSpace.exp ((H + L) + A)).trace :=
    TauCeti.continuous_re_trace.comp <| (NormedSpace.exp_continuous (𝔸 := Matrix n n 𝕜)).comp <|
      continuous_const.add continuous_id
  have hL : L.IsHermitian := IsSelfAdjoint.isHermitian (cfc_predicate Real.log _)
  have hHL_le : H + L ≤ ‖H + L‖ • (1 : Matrix n n 𝕜) :=
    (hH.add hL).le_smul_one_of_l2_opNorm_le le_rfl
  have hrhs_int := TauCeti.integrable_re_trace_exp_of_ae_le_smul_one
    (P := P.map S) (Z := fun A ↦ (H + L) + A)
    (continuous_const.add continuous_id).measurable.aemeasurable
    (M := ‖H + L‖ + MS)
    (hS_upper_map.mono fun _ hA ↦ (add_le_add hHL_le hA).trans_eq (add_smul _ _ _).symm)
  rw [← integral_map (hS_meas.prodMk hX_meas) hφ_cont.aestronglyMeasurable, hmap_prod,
    integral_prod φ hφ_int_prod, ← integral_map hS_meas hrhs_cont.aestronglyMeasurable]
  exact integral_mono_ae hφ_int_prod.integral_prod_left hrhs_int hinner

/-- **Subadditivity of the matrix cumulant generating function** (Tropp 2012, Lemma 3.4). For
independent random matrices `X k` (`k ∈ s`) bounded above in Loewner order and a fixed Hermitian
matrix `H`,
`E[Re Tr exp (H + ∑ k ∈ s, X k)] ≤ Re Tr exp (H + ∑ k ∈ s, log E[exp (X k)])`. -/
theorem iIndepFun.integral_re_trace_exp_add_sum_le [IsProbabilityMeasure P]
    {s : Finset ι} {X : ι → Ω → Matrix n n 𝕜}
    (hindep : iIndepFun X P)
    (hmeas : ∀ k ∈ s, AEMeasurable (X k) P)
    (hupper : ∀ k ∈ s, ∃ M : ℝ, ∀ᵐ ω ∂P, X k ω ≤ M • (1 : Matrix n n 𝕜))
    {H : Matrix n n 𝕜} (hH : H.IsHermitian) :
    ∫ ω, RCLike.re (NormedSpace.exp (H + ∑ k ∈ s, X k ω)).trace ∂P ≤
      RCLike.re (NormedSpace.exp (H + ∑ k ∈ s, cfc Real.log
        (Matrix.of fun i j ↦ ∫ ω, (NormedSpace.exp (X k ω)) i j ∂P))).trace := by
  classical
  induction s using Finset.induction_on generalizing H with
  | empty => simp
  | insert a t ha ih =>
    have hmeas_t := fun k hk ↦ hmeas k (Finset.mem_insert_of_mem hk)
    have hupper_t := fun k hk ↦ hupper k (Finset.mem_insert_of_mem hk)
    obtain ⟨Ma, hMa⟩ := hupper a (Finset.mem_insert_self a t)
    choose M hM using hupper_t
    have hMS : ∀ᵐ ω ∂P, ∑ k ∈ t, X k ω ≤ (∑ k ∈ t.attach, M k.val k.property) •
        (1 : Matrix n n 𝕜) := by
      refine ((eventually_all_finset t.attach).2 fun k _ ↦ hM k.val k.property).mono fun ω hω ↦ ?_
      rw [Finset.sum_smul, ← Finset.sum_attach t (fun k ↦ X k ω)]
      exact Finset.sum_le_sum fun k hk ↦ hω k hk
    simp_rw [Finset.sum_insert ha, ← add_assoc, add_right_comm H (X a _)]
    have hsum_fn : (fun ω ↦ ∑ k ∈ t, X k ω) = ∑ k ∈ t, X k :=
      funext fun ω ↦ (Finset.sum_apply ω t X).symm
    have hind : IndepFun (fun ω ↦ ∑ k ∈ t, X k ω) (X a) P :=
      hsum_fn ▸ hindep.indepFun_finsetSum_of_notMem₀_on ha hmeas_t
        (hmeas a (Finset.mem_insert_self a t))
    refine (hind.integral_re_trace_exp_add_add_le
      (Finset.aemeasurable_fun_sum t hmeas_t) (hmeas a (Finset.mem_insert_self a t))
      hMS hMa hH).trans ?_
    exact ih hmeas_t (fun k hk ↦ hupper k (Finset.mem_insert_of_mem hk))
      (hH.add <| IsSelfAdjoint.isHermitian (cfc_predicate Real.log _))

/-- **Master matrix Laplace-transform upper tail bound** (Tropp 2012, Theorem 3.6). For independent
random matrices `X k` (`k ∈ s`) bounded above in Loewner order on a nonempty index type `n` and any
`θ > 0`,
`P {λ_max (∑ k ∈ s, X k) ≥ t} ≤ exp (-θ t) * Re Tr exp (∑ k ∈ s, log E[exp (θ X k)])`. -/
theorem iIndepFun.measureReal_sSup_spectrum_sum_ge_le [IsProbabilityMeasure P] [Nonempty n]
    {s : Finset ι} {X : ι → Ω → Matrix n n 𝕜}
    (hindep : iIndepFun X P)
    (hmeas : ∀ k ∈ s, AEMeasurable (X k) P)
    (hupper : ∀ k ∈ s, ∃ M : ℝ, ∀ᵐ ω ∂P, X k ω ≤ M • (1 : Matrix n n 𝕜))
    {θ t : ℝ} (hθ : 0 < θ) :
    P.real {ω | t ≤ sSup (spectrum ℝ (∑ k ∈ s, X k ω))} ≤
      Real.exp (-θ * t) * RCLike.re (NormedSpace.exp (∑ k ∈ s, cfc Real.log
        (Matrix.of fun i j ↦ ∫ ω, (NormedSpace.exp (θ • X k ω)) i j ∂P))).trace := by
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  let : NormedAlgebra ℚ (Matrix n n 𝕜) := TauCeti.normedAlgebraRatOfReal
  let Y : ι → Ω → Matrix n n 𝕜 := fun k ω ↦ θ • X k ω
  have hY_meas := fun k hk ↦ (continuous_const_smul θ).measurable.comp_aemeasurable (hmeas k hk)
  have hY_upper : ∀ k ∈ s, ∃ M : ℝ, ∀ᵐ ω ∂P, Y k ω ≤ M • (1 : Matrix n n 𝕜) := fun k hk ↦
    let ⟨M, hM⟩ := hupper k hk
    ⟨θ * M, hM.mono fun _ h ↦ (smul_le_smul_of_nonneg_left h hθ.le).trans_eq (smul_smul _ _ _)⟩
  have hY_herm : ∀ k ∈ s, ∀ᵐ ω ∂P, (Y k ω).IsHermitian := fun k hk ↦
    let ⟨_, hM⟩ := hY_upper k hk
    hM.mono fun _ h ↦ TauCeti.isHermitian_of_le_smul_one h
  have hsum_herm := TauCeti.ae_isHermitian_finsetSum hY_herm
  obtain ⟨MY, hMY⟩ : ∃ MY : ℝ, ∀ᵐ ω ∂P, ∑ k ∈ s, Y k ω ≤ MY • (1 : Matrix n n 𝕜) := by
    classical
    choose M hM using hY_upper
    refine ⟨∑ k ∈ s.attach, M k.val k.property,
      ((eventually_all_finset s.attach).2 fun k _ ↦ hM k.val k.property).mono fun ω hω ↦ ?_⟩
    rw [Finset.sum_smul, ← Finset.sum_attach s (fun k ↦ Y k ω)]
    exact Finset.sum_le_sum fun k hk ↦ hω k hk
  have hsub : {ω | t ≤ sSup (spectrum ℝ (∑ k ∈ s, X k ω))} ≤ᵐ[P]
      {ω | Real.exp (θ * t) ≤ RCLike.re (NormedSpace.exp (∑ k ∈ s, Y k ω)).trace} :=
    hsum_herm.mono fun ω hω hge ↦ by
      have h1 := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hge hθ.le)
      have hsum_Y : ∑ k ∈ s, Y k ω = θ • ∑ k ∈ s, X k ω := by simp [Y, Finset.smul_sum]
      rw [← TauCeti.sSup_spectrum_real_smul_of_nonneg _ hθ.le, ← hsum_Y] at h1
      exact h1.trans hω.exp_sSup_spectrum_real_le_re_trace_exp
  have hcgf := (hindep.comp (fun _ A ↦ θ • A) fun _ ↦
      (continuous_const_smul θ).measurable).integral_re_trace_exp_add_sum_le
    hY_meas hY_upper isHermitian_zero
  simp only [Function.comp_apply, zero_add] at hcgf
  rw [neg_mul, Real.exp_neg, inv_mul_eq_div, le_div_iff₀' (Real.exp_pos _)]
  exact (mul_le_mul_of_nonneg_left (ENNReal.toReal_mono (measure_ne_top P _) (measure_mono_ae hsub))
    (Real.exp_pos _).le).trans <|
      (mul_meas_ge_le_integral_of_nonneg (hsum_herm.mono fun _ h ↦ h.re_trace_exp_nonneg)
        (TauCeti.integrable_re_trace_exp_of_ae_le_smul_one
          (Finset.aemeasurable_fun_sum s hY_meas) hMY)
        (Real.exp (θ * t))).trans hcgf

/-- **Master matrix Laplace-transform lower tail bound** (Tropp 2012, Theorem 3.6). For independent
random matrices `X k` (`k ∈ s`) bounded below in Loewner order on a nonempty index type `n` and any
`θ > 0`,
`P {λ_min (∑ k ∈ s, X k) ≤ t} ≤ exp (θ t) * Re Tr exp (∑ k ∈ s, log E[exp (-θ X k)])`. -/
theorem iIndepFun.measureReal_sInf_spectrum_sum_le_le [IsProbabilityMeasure P] [Nonempty n]
    {s : Finset ι} {X : ι → Ω → Matrix n n 𝕜}
    (hindep : iIndepFun X P)
    (hmeas : ∀ k ∈ s, AEMeasurable (X k) P)
    (hlower : ∀ k ∈ s, ∃ M : ℝ, ∀ᵐ ω ∂P, M • (1 : Matrix n n 𝕜) ≤ X k ω)
    {θ t : ℝ} (hθ : 0 < θ) :
    P.real {ω | sInf (spectrum ℝ (∑ k ∈ s, X k ω)) ≤ t} ≤
      Real.exp (θ * t) * RCLike.re (NormedSpace.exp (∑ k ∈ s, cfc Real.log
        (Matrix.of fun i j ↦ ∫ ω, (NormedSpace.exp ((-θ) • X k ω)) i j ∂P))).trace := by
  have h := (hindep.comp (fun _ A ↦ -A) fun _ ↦
      continuous_neg.measurable).measureReal_sSup_spectrum_sum_ge_le
    (fun k hk ↦ continuous_neg.measurable.comp_aemeasurable (hmeas k hk))
    (fun k hk ↦ by
      obtain ⟨M, hM⟩ := hlower k hk
      exact ⟨-M, hM.mono fun _ h ↦ by simpa [neg_smul] using neg_le_neg h⟩)
    (t := -t) hθ
  simp only [Function.comp_apply] at h
  have hevent_eq : {ω | -t ≤ sSup (spectrum ℝ (∑ k ∈ s, -X k ω))} =
      {ω | sInf (spectrum ℝ (∑ k ∈ s, X k ω)) ≤ t} := by
    ext ω
    simp [Finset.sum_neg_distrib, TauCeti.sSup_spectrum_real_neg]
  rw [hevent_eq] at h
  simpa [neg_smul, smul_neg] using h

end ProbabilityTheory
