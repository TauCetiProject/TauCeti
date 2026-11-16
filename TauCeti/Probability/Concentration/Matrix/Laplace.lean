/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Probability.Independence.Basic
public import TauCeti.Analysis.Matrix.Exponential.TraceInequalities
import TauCeti.Analysis.Matrix.Eigenvalues.OperatorNorm
import TauCeti.Analysis.Matrix.Order
import TauCeti.Analysis.Normed.Algebra.Basic

/-!
# Matrix Laplace transform method

Tropp's matrix Laplace transform method for sums of independent random Hermitian matrices over any
`RCLike` field `𝕜` (`ℝ` or `ℂ`). Expectations are written entrywise as
`Matrix.of fun i j ↦ ∫ ω, X ω i j ∂P`, coinciding with the Bochner integral under the `ℓ²` operator
norm. Combining Lieb's concavity (`Matrix.IsHermitian.concaveOn_re_trace_exp_add_cfc_log`) with
Jensen's inequality yields the single-step Lieb–Jensen bound, subadditivity of the matrix CGF, and
master upper and lower eigenvalue tail inequalities.

## Main results

* `Matrix.isHermitian_of_integral`, `Matrix.posSemidef_of_integral`,
  `Matrix.of_integral_le_of_integral_of_ae_le`: preservation of Hermitianness, positive
  semidefiniteness, and the Loewner order under entrywise expectation.
* `Matrix.integral_re_trace_exp_add_le`: the single-step Lieb–Jensen inequality.
* `ProbabilityTheory.iIndepFun.integral_re_trace_exp_add_sum_le`: subadditivity of the matrix CGF
  for independent random Hermitian matrices (Tropp 2012, Theorem 3.6).
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

section Expectation

variable {Ω 𝕜 n : Type*} [MeasurableSpace Ω] {P : Measure Ω} [RCLike 𝕜]

/-! ### Entrywise expectation and the Loewner order -/

/-- Entrywise expectation preserves the Hermitian property. -/
theorem isHermitian_of_integral {F : Ω → Matrix n n 𝕜}
    (hF : ∀ᵐ ω ∂P, (F ω).IsHermitian) :
    (Matrix.of fun i j ↦ ∫ ω, F ω i j ∂P).IsHermitian := by
  ext i j
  simp only [conjTranspose_apply, of_apply, RCLike.star_def, ← integral_conj]
  refine integral_congr_ae (hF.mono fun ω hω ↦ ?_)
  simpa [conjTranspose_apply, RCLike.star_def] using congrFun (congrFun hω i) j

/-- Entrywise expectation preserves positive semidefiniteness. -/
theorem posSemidef_of_integral [Finite n] {F : Ω → Matrix n n 𝕜}
    (hF : ∀ᵐ ω ∂P, (F ω).PosSemidef)
    (hint : ∀ i j, Integrable (fun ω ↦ F ω i j) P) :
    (Matrix.of fun i j ↦ ∫ ω, F ω i j ∂P).PosSemidef := by
  have := Fintype.ofFinite n
  refine posSemidef_iff_dotProduct_mulVec.2
    ⟨isHermitian_of_integral (hF.mono fun _ h ↦ h.1), fun x ↦ ?_⟩
  have hterm (i j : n) : Integrable (fun ω ↦ star x i * (F ω i j * x j)) P :=
    ((hint i j).mul_const (x j)).const_mul (star x i)
  have hquad_int : Integrable (fun ω ↦ star x ⬝ᵥ F ω *ᵥ x) P := by
    simp only [dotProduct, mulVec, Finset.mul_sum]
    exact integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hterm i j
  rw [show star x ⬝ᵥ (Matrix.of fun i j ↦ ∫ ω, F ω i j ∂P) *ᵥ x =
      ∫ ω, star x ⬝ᵥ F ω *ᵥ x ∂P by
    simp only [dotProduct, mulVec, of_apply, Finset.mul_sum]
    rw [integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hterm i j]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [integral_finsetSum _ fun j _ ↦ hterm i j]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [integral_const_mul, integral_mul_const],
    RCLike.nonneg_iff]
  have hnonneg := hF.mono fun _ h ↦ RCLike.nonneg_iff.1 ((posSemidef_iff_dotProduct_mulVec.1 h).2 x)
  exact ⟨by rw [← RCLike.reCLM_apply, ← RCLike.reCLM.integral_comp_comm hquad_int]
            exact integral_nonneg_of_ae (hnonneg.mono fun _ h ↦ h.1),
         by rw [← RCLike.imCLM_apply, ← RCLike.imCLM.integral_comp_comm hquad_int]
            exact (integral_congr_ae (hnonneg.mono fun _ h ↦ h.2)).trans (integral_zero _ _)⟩

/-- Entrywise expectation is monotone in the Loewner order. -/
theorem of_integral_le_of_integral_of_ae_le [Finite n] {F G : Ω → Matrix n n 𝕜}
    (hle : ∀ᵐ ω ∂P, F ω ≤ G ω)
    (hF : ∀ i j, Integrable (fun ω ↦ F ω i j) P)
    (hG : ∀ i j, Integrable (fun ω ↦ G ω i j) P) :
    (Matrix.of fun i j ↦ ∫ ω, F ω i j ∂P) ≤ (Matrix.of fun i j ↦ ∫ ω, G ω i j ∂P) := by
  rw [le_iff, show (Matrix.of fun i j ↦ ∫ ω, G ω i j ∂P) -
      (Matrix.of fun i j ↦ ∫ ω, F ω i j ∂P) = Matrix.of fun i j ↦ ∫ ω, (G ω - F ω) i j ∂P by
    ext i j; simp [integral_sub (hG i j) (hF i j)]]
  exact posSemidef_of_integral (hle.mono fun _ h ↦ le_iff.1 h) fun i j ↦ (hG i j).sub (hF i j)

/-- Entrywise integrability of an a.e. operator-norm bounded measurable random matrix. -/
theorem integrable_apply_of_ae_l2_opNorm_le [IsFiniteMeasure P]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] {m : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    {F : Ω → Matrix m n 𝕜} (hmeas : AEMeasurable F P) {M : ℝ} (hbdd : ∀ᵐ ω ∂P, ‖F ω‖ ≤ M)
    (i : m) (j : n) :
    Integrable (fun ω ↦ F ω i j) P :=
  Integrable.of_bound (Matrix.measurable_apply.comp_aemeasurable hmeas).aestronglyMeasurable
    M (hbdd.mono fun ω hω ↦ (Matrix.norm_apply_le_l2_opNorm (F ω) i j).trans hω)

end Expectation

section LiebJensen

variable {Ω 𝕜 n : Type*} [MeasurableSpace Ω] {P : Measure Ω} [RCLike 𝕜]

private theorem posDef_of_smul_one_le [DecidableEq n] {A : Matrix n n 𝕜} {c : ℝ} (hc : 0 < c)
    (hle : c • (1 : Matrix n n 𝕜) ≤ A) : A.PosDef := by
  rw [show A = c • (1 : Matrix n n 𝕜) + (A - c • (1 : Matrix n n 𝕜)) by abel]
  exact ((PosDef.one (n := n) (R := 𝕜)).smul hc).add_posSemidef (le_iff.1 hle)

private theorem continuous_re_trace [Fintype n] :
    Continuous fun Z : Matrix n n 𝕜 ↦ RCLike.re Z.trace :=
  (RCLike.reCLM.comp ((traceLinearMap n 𝕜 𝕜).restrictScalars ℝ).toContinuousLinearMap).continuous

variable [MeasurableSpace 𝕜] [BorelSpace 𝕜] [Fintype n] [DecidableEq n]

private theorem integrable_re_trace_exp [IsFiniteMeasure P] {Z : Ω → Matrix n n 𝕜}
    (hmeas : AEMeasurable Z P) (hherm : ∀ᵐ ω ∂P, (Z ω).IsHermitian)
    {M : ℝ} (hbdd : ∀ᵐ ω ∂P, ‖Z ω‖ ≤ M) :
    Integrable (fun ω ↦ RCLike.re (NormedSpace.exp (Z ω)).trace) P := by
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  let : NormedAlgebra ℚ (Matrix n n 𝕜) := TauCeti.normedAlgebraRatOfReal
  have hcont := continuous_re_trace.comp (NormedSpace.exp_continuous (𝔸 := Matrix n n 𝕜))
  refine Integrable.of_bound (hcont.measurable.comp_aemeasurable hmeas).aestronglyMeasurable
    ((Fintype.card n : ℝ) * Real.exp M) ((hherm.and hbdd).mono fun ω ⟨h1, h2⟩ ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg h1.re_trace_exp_nonneg]
  exact h1.re_trace_exp_le_card_mul_exp (h1.le_smul_one_of_l2_opNorm_le h2)

/-- The entrywise expectation of `exp X` for an a.e. bounded random Hermitian matrix `X` is
positive definite. -/
theorem posDef_of_integral_exp [IsProbabilityMeasure P] {X : Ω → Matrix n n 𝕜}
    (hmeas : AEMeasurable X P) (hherm : ∀ᵐ ω ∂P, (X ω).IsHermitian)
    {M : ℝ} (hbdd : ∀ᵐ ω ∂P, ‖X ω‖ ≤ M) :
    (Matrix.of fun i j ↦ ∫ ω, (NormedSpace.exp (X ω)) i j ∂P).PosDef := by
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  let : NormedAlgebra ℚ (Matrix n n 𝕜) := TauCeti.normedAlgebraRatOfReal
  refine posDef_of_smul_one_le (Real.exp_pos (-M)) ?_
  rw [show Real.exp (-M) • (1 : Matrix n n 𝕜) =
      Matrix.of fun i j ↦ ∫ _ω, (Real.exp (-M) • (1 : Matrix n n 𝕜)) i j ∂P by ext i j; simp]
  exact of_integral_le_of_integral_of_ae_le
    ((hherm.and hbdd).mono fun _ ⟨h1, h2⟩ ↦ (h1.smul_one_le_exp_and_le_smul_one h2).1)
    (fun _ _ ↦ integrable_const _)
    (integrable_apply_of_ae_l2_opNorm_le
      ((NormedSpace.exp_continuous (𝔸 := Matrix n n 𝕜)).measurable.comp_aemeasurable hmeas)
      ((hherm.and hbdd).mono fun _ ⟨h1, h2⟩ ↦ h1.l2_opNorm_exp_le h2))

/-! ### Single-step Lieb–Jensen inequality -/

/-- **Single-step Lieb–Jensen inequality** (Tropp 2012, Corollary 3.3). For a fixed Hermitian
matrix `H` and an a.e. bounded random Hermitian matrix `X`,
`E[Re Tr exp (H + X)] ≤ Re Tr exp (H + log E[exp X])`. -/
theorem integral_re_trace_exp_add_le [IsProbabilityMeasure P]
    {H : Matrix n n 𝕜} (hH : H.IsHermitian) {X : Ω → Matrix n n 𝕜}
    (hmeas : AEMeasurable X P) (hherm : ∀ᵐ ω ∂P, (X ω).IsHermitian)
    {M : ℝ} (hbdd : ∀ᵐ ω ∂P, ‖X ω‖ ≤ M) :
    ∫ ω, RCLike.re (NormedSpace.exp (H + X ω)).trace ∂P ≤
      RCLike.re (NormedSpace.exp (H + cfc Real.log
        (Matrix.of fun i j ↦ ∫ ω, (NormedSpace.exp (X ω)) i j ∂P))).trace := by
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  let : NormedAlgebra ℚ (Matrix n n 𝕜) := TauCeti.normedAlgebraRatOfReal
  let S : Set (Matrix n n 𝕜) := Set.Ici (Real.exp (-M) • (1 : Matrix n n 𝕜))
  let g : Matrix n n 𝕜 → ℝ := fun A ↦ RCLike.re (NormedSpace.exp (H + cfc Real.log A)).trace
  let Y : Ω → Matrix n n 𝕜 := fun ω ↦ NormedSpace.exp (X ω)
  have hS_sub : S ⊆ {A : Matrix n n 𝕜 | A.PosDef} :=
    fun _ hA ↦ posDef_of_smul_one_le (Real.exp_pos (-M)) hA
  have hS_conv : Convex ℝ S := fun _ h₁ _ h₂ _ _ ha hb hab ↦ by
    simpa [S, ← add_smul, hab] using add_le_add
      (smul_le_smul_of_nonneg_left (Set.mem_Ici.1 h₁) ha)
      (smul_le_smul_of_nonneg_left (Set.mem_Ici.1 h₂) hb)
  have hg_cont : ContinuousOn g S :=
    (continuous_re_trace.comp_continuousOn <|
      (NormedSpace.exp_continuous (𝔸 := Matrix n n 𝕜)).comp_continuousOn <|
        continuousOn_const.add
          (Matrix.contDiffOn_cfc_log (𝕜 := 𝕜) (n := n) (k := 0)).continuousOn).mono hS_sub
  have hY_int : Integrable Y P := Integrable.of_bound
    ((NormedSpace.exp_continuous (𝔸 := Matrix n n 𝕜)).measurable.comp_aemeasurable
      hmeas).aestronglyMeasurable
    (Real.exp M) ((hherm.and hbdd).mono fun _ ⟨h1, h2⟩ ↦ h1.l2_opNorm_exp_le h2)
  have hfg_eq : (fun ω ↦ g (Y ω)) =ᵐ[P] fun ω ↦ RCLike.re (NormedSpace.exp (H + X ω)).trace :=
    hherm.mono fun ω hω ↦ by simp only [g, Y, hω.cfc_log_exp]
  have hHX_int := integrable_re_trace_exp
    ((continuous_const.add continuous_id).measurable.comp_aemeasurable hmeas)
    (hherm.mono fun _ h ↦ hH.add h)
    (hbdd.mono fun _ h ↦ (norm_add_le _ _).trans (add_le_add le_rfl h))
  have hY_eq : ∫ ω, Y ω ∂P = Matrix.of fun i j ↦ ∫ ω, Y ω i j ∂P := by
    ext i j
    let ev : Matrix n n 𝕜 →L[ℝ] 𝕜 :=
      ((Matrix.entryLinearMap 𝕜 𝕜 i j).restrictScalars ℝ).toContinuousLinearMap
    simpa [ev] using (ev.integral_comp_comm hY_int).symm
  have hjensen := (hH.concaveOn_re_trace_exp_add_cfc_log.subset hS_sub hS_conv).le_map_integral
    hg_cont isClosed_Ici
    ((hherm.and hbdd).mono fun _ ⟨h1, h2⟩ ↦ (h1.smul_one_le_exp_and_le_smul_one h2).1)
    hY_int (hHX_int.congr hfg_eq.symm)
  rwa [integral_congr_ae hfg_eq, hY_eq] at hjensen

end LiebJensen

end Matrix

/-! ### Subadditivity of matrix CGF and master Laplace tail bounds -/

namespace ProbabilityTheory

section IndepSum

variable {Ω 𝕜 n ι : Type*} [MeasurableSpace Ω] {P : Measure Ω} [RCLike 𝕜]

private theorem ae_isHermitian_finsetSum {s : Finset ι} {X : ι → Ω → Matrix n n 𝕜}
    (hherm : ∀ k ∈ s, ∀ᵐ ω ∂P, (X k ω).IsHermitian) :
    ∀ᵐ ω ∂P, (∑ k ∈ s, X k ω).IsHermitian :=
  ((ae_ball_iff s.countable_toSet).2 hherm).mono fun _ hω ↦
    Finset.sum_induction _ _ (fun _ _ h₁ h₂ ↦ h₁.add h₂) isHermitian_zero hω

variable [MeasurableSpace 𝕜] [BorelSpace 𝕜]

private theorem measurableAdd₂_matrix : MeasurableAdd₂ (Matrix n n 𝕜) :=
  ⟨Matrix.measurable_iff.2 fun _ _ ↦
    (Matrix.measurable_apply.comp measurable_fst).add
      (Matrix.measurable_apply.comp measurable_snd)⟩

private theorem measurableSet_isHermitian [Countable n] :
    MeasurableSet {A : Matrix n n 𝕜 | A.IsHermitian} :=
  (isClosed_eq (show Continuous fun A : Matrix n n 𝕜 ↦ Aᴴ from
    continuous_pi fun i ↦ continuous_pi fun j ↦
      continuous_star.comp ((continuous_apply i).comp (continuous_apply j)))
    continuous_id).measurableSet

private theorem iIndepFun.indepFun_finsetSum_of_notMem_on [DecidableEq ι] {s : Finset ι} {a : ι}
    {X : ι → Ω → Matrix n n 𝕜} (hindep : iIndepFun X P) (ha : a ∉ s)
    (hmeas : ∀ k ∈ insert a s, AEMeasurable (X k) P) :
    IndepFun (fun ω ↦ ∑ k ∈ s, X k ω) (X a) P := by
  have : MeasurableAdd₂ (Matrix n n 𝕜) := measurableAdd₂_matrix
  let t : Finset ↥(insert a s) := s.attach.map
    ⟨fun k ↦ ⟨k.1, Finset.mem_insert_of_mem k.2⟩,
      fun _ _ h ↦ Subtype.ext (by simpa using congrArg Subtype.val h)⟩
  have ha' : (⟨a, Finset.mem_insert_self a s⟩ : ↥(insert a s)) ∉ t := by
    simp only [t, Finset.mem_map, Finset.mem_attach, true_and, Subtype.ext_iff, not_exists]
    exact fun k hk ↦ ha (hk ▸ k.2)
  have h := (hindep.precomp Subtype.val_injective).indepFun_finsetSum_of_notMem₀
    (fun k : ↥(insert a s) ↦ hmeas k.1 k.2) ha'
  rwa [show (∑ k ∈ t, fun ω ↦ X k.1 ω) = fun ω ↦ ∑ k ∈ s, X k ω by
    funext ω; simp only [Finset.sum_apply, t, Finset.sum_map]
    exact Finset.sum_attach s fun k ↦ X k ω] at h

end IndepSum

variable {Ω 𝕜 n ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [RCLike 𝕜] [Fintype n] [DecidableEq n]

private theorem exists_ae_norm_finsetSum_le {s : Finset ι} {X : ι → Ω → Matrix n n 𝕜}
    (hbdd : ∀ k ∈ s, ∃ M : ℝ, ∀ᵐ ω ∂P, ‖X k ω‖ ≤ M) :
    ∃ M : ℝ, ∀ᵐ ω ∂P, ‖∑ k ∈ s, X k ω‖ ≤ M := by
  choose M hM using hbdd
  refine ⟨∑ k ∈ s.attach, M k.1 k.2, (ae_all_iff.2 fun k : ↥s ↦ hM k.1 k.2).mono fun ω hω ↦ ?_⟩
  refine (norm_sum_le s fun k ↦ X k ω).trans ?_
  rw [← Finset.sum_attach s (fun k ↦ ‖X k ω‖)]
  exact Finset.sum_le_sum fun k _ ↦ hω k

variable [MeasurableSpace 𝕜] [BorelSpace 𝕜]

/-- One conditioning step of Tropp's subadditivity argument for two independent bounded random
Hermitian matrices `S` and `X`. -/
private theorem IndepFun.integral_re_trace_exp_add_add_le [IsProbabilityMeasure P]
    {S X : Ω → Matrix n n 𝕜} (hind : IndepFun S X P)
    (hS_meas : AEMeasurable S P) (hX_meas : AEMeasurable X P)
    (hS_herm : ∀ᵐ ω ∂P, (S ω).IsHermitian) (hX_herm : ∀ᵐ ω ∂P, (X ω).IsHermitian)
    {MS MX : ℝ} (hS_bdd : ∀ᵐ ω ∂P, ‖S ω‖ ≤ MS) (hX_bdd : ∀ᵐ ω ∂P, ‖X ω‖ ≤ MX)
    {H : Matrix n n 𝕜} (hH : H.IsHermitian) :
    ∫ ω, RCLike.re (NormedSpace.exp (H + S ω + X ω)).trace ∂P ≤
      ∫ ω, RCLike.re (NormedSpace.exp ((H + cfc Real.log
        (Matrix.of fun i j ↦ ∫ ω', (NormedSpace.exp (X ω')) i j ∂P)) + S ω)).trace ∂P := by
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  let : NormedAlgebra ℚ (Matrix n n 𝕜) := TauCeti.normedAlgebraRatOfReal
  let φ : Matrix n n 𝕜 × Matrix n n 𝕜 → ℝ :=
    fun p ↦ RCLike.re (NormedSpace.exp (H + p.1 + p.2)).trace
  have hφ_cont : Continuous φ :=
    Matrix.continuous_re_trace.comp <| (NormedSpace.exp_continuous (𝔸 := Matrix n n 𝕜)).comp <|
      (continuous_const.add continuous_fst).add continuous_snd
  have hmap_prod := hind.map_prod_eq_prod_map_map hS_meas hX_meas
  have hφ_int_prod : Integrable φ ((P.map S).prod (P.map X)) :=
    hmap_prod ▸ (integrable_map_measure hφ_cont.aestronglyMeasurable (hS_meas.prodMk hX_meas)).2 <|
      Matrix.integrable_re_trace_exp
        (((continuous_const.add continuous_fst).add continuous_snd).measurable.comp_aemeasurable
          (hS_meas.prodMk hX_meas))
        ((hS_herm.and hX_herm).mono fun _ ⟨h1, h2⟩ ↦ (hH.add h1).add h2)
        ((hS_bdd.and hX_bdd).mono fun _ ⟨h3, h4⟩ ↦
          (norm_add_le _ _).trans <| add_le_add ((norm_add_le _ _).trans (add_le_add le_rfl h3)) h4)
  have hS_herm_map := (ae_map_iff hS_meas measurableSet_isHermitian).2 hS_herm
  have hS_bdd_map :=
    (ae_map_iff hS_meas (isClosed_le continuous_norm continuous_const).measurableSet).2 hS_bdd
  have hexp_map : (Matrix.of fun i j ↦ ∫ B, (NormedSpace.exp B) i j ∂(P.map X)) =
      Matrix.of fun i j ↦ ∫ ω, (NormedSpace.exp (X ω)) i j ∂P := by
    ext i j
    exact integral_map hX_meas ((continuous_apply j).comp ((continuous_apply i).comp
      (NormedSpace.exp_continuous (𝔸 := Matrix n n 𝕜)))).aestronglyMeasurable
  let L : Matrix n n 𝕜 := cfc Real.log (Matrix.of fun i j ↦ ∫ ω, (NormedSpace.exp (X ω)) i j ∂P)
  have hinner : ∀ᵐ A ∂(P.map S),
      (∫ B, φ (A, B) ∂(P.map X)) ≤ RCLike.re (NormedSpace.exp ((H + L) + A)).trace :=
    hS_herm_map.mono fun A hA ↦ by
      have hstep := Matrix.integral_re_trace_exp_add_le (P := P.map X) (hH.add hA) aemeasurable_id
        ((ae_map_iff hX_meas measurableSet_isHermitian).2 hX_herm)
        ((ae_map_iff hX_meas (isClosed_le continuous_norm continuous_const).measurableSet).2 hX_bdd)
      simp only [id_eq] at hstep
      rwa [hexp_map, add_right_comm H A L] at hstep
  have hrhs_cont : Continuous fun A : Matrix n n 𝕜 ↦
      RCLike.re (NormedSpace.exp ((H + L) + A)).trace :=
    Matrix.continuous_re_trace.comp <| (NormedSpace.exp_continuous (𝔸 := Matrix n n 𝕜)).comp <|
      continuous_const.add continuous_id
  have hL_herm : L.IsHermitian := IsSelfAdjoint.isHermitian (cfc_predicate Real.log _)
  have hrhs_int : Integrable (fun A ↦ RCLike.re (NormedSpace.exp ((H + L) + A)).trace) (P.map S) :=
    Matrix.integrable_re_trace_exp (continuous_const.add continuous_id).measurable.aemeasurable
      (hS_herm_map.mono fun _ h ↦ (hH.add hL_herm).add h)
      (hS_bdd_map.mono fun _ h ↦ (norm_add_le _ _).trans (add_le_add le_rfl h))
  calc
    ∫ ω, RCLike.re (NormedSpace.exp (H + S ω + X ω)).trace ∂P
        = ∫ A, (∫ B, φ (A, B) ∂(P.map X)) ∂(P.map S) := by
          rw [← integral_map (hS_meas.prodMk hX_meas) hφ_cont.aestronglyMeasurable,
            hmap_prod, integral_prod φ hφ_int_prod]
    _ ≤ ∫ A, RCLike.re (NormedSpace.exp ((H + L) + A)).trace ∂(P.map S) :=
        integral_mono_ae hφ_int_prod.integral_prod_left hrhs_int hinner
    _ = ∫ ω, RCLike.re (NormedSpace.exp ((H + L) + S ω)).trace ∂P :=
        integral_map hS_meas hrhs_cont.aestronglyMeasurable

/-- **Subadditivity of the matrix cumulant generating function** (Tropp 2012, Theorem 3.6). For
independent a.e. bounded random Hermitian matrices `X k` (`k ∈ s`) and a fixed Hermitian matrix
`H`,
`E[Re Tr exp (H + ∑ k ∈ s, X k)] ≤ Re Tr exp (H + ∑ k ∈ s, log E[exp (X k)])`. -/
theorem iIndepFun.integral_re_trace_exp_add_sum_le [IsProbabilityMeasure P]
    {s : Finset ι} {X : ι → Ω → Matrix n n 𝕜}
    (hindep : iIndepFun X P)
    (hmeas : ∀ k ∈ s, AEMeasurable (X k) P)
    (hherm : ∀ k ∈ s, ∀ᵐ ω ∂P, (X k ω).IsHermitian)
    (hbdd : ∀ k ∈ s, ∃ M : ℝ, ∀ᵐ ω ∂P, ‖X k ω‖ ≤ M)
    {H : Matrix n n 𝕜} (hH : H.IsHermitian) :
    ∫ ω, RCLike.re (NormedSpace.exp (H + ∑ k ∈ s, X k ω)).trace ∂P ≤
      RCLike.re (NormedSpace.exp (H + ∑ k ∈ s, cfc Real.log
        (Matrix.of fun i j ↦ ∫ ω, (NormedSpace.exp (X k ω)) i j ∂P))).trace := by
  classical
  have : MeasurableAdd₂ (Matrix n n 𝕜) := measurableAdd₂_matrix
  induction s using Finset.induction_on generalizing H with
  | empty => simp
  | insert a t ha ih =>
    have hmeas_t := fun k hk ↦ hmeas k (Finset.mem_insert_of_mem hk)
    have hherm_t := fun k hk ↦ hherm k (Finset.mem_insert_of_mem hk)
    have hbdd_t := fun k hk ↦ hbdd k (Finset.mem_insert_of_mem hk)
    obtain ⟨Ma, hMa⟩ := hbdd a (Finset.mem_insert_self a t)
    obtain ⟨MS, hMS⟩ := exists_ae_norm_finsetSum_le hbdd_t
    simp_rw [Finset.sum_insert ha, ← add_assoc, add_right_comm H (X a _)]
    have h1 := (hindep.indepFun_finsetSum_of_notMem_on ha hmeas).integral_re_trace_exp_add_add_le
      (Finset.aemeasurable_fun_sum t hmeas_t) (hmeas a (Finset.mem_insert_self a t))
      (ae_isHermitian_finsetSum hherm_t) (hherm a (Finset.mem_insert_self a t)) hMS hMa hH
    have h2 := ih hmeas_t hherm_t hbdd_t
      (hH.add (IsSelfAdjoint.isHermitian (cfc_predicate Real.log
        (Matrix.of fun i j ↦ ∫ ω, (NormedSpace.exp (X a ω)) i j ∂P))))
    exact h1.trans h2

/-- **Master matrix Laplace-transform upper tail bound** (Tropp 2012, Theorem 3.6). For independent
a.e. bounded random Hermitian matrices `X k` (`k ∈ s`) on a nonempty index type `n` and any `θ > 0`,
`P {λ_max (∑ k ∈ s, X k) ≥ t} ≤ exp (-θ t) * Re Tr exp (∑ k ∈ s, log E[exp (θ X k)])`. -/
theorem iIndepFun.measureReal_sSup_spectrum_sum_ge_le [IsProbabilityMeasure P] [Nonempty n]
    {s : Finset ι} {X : ι → Ω → Matrix n n 𝕜}
    (hindep : iIndepFun X P)
    (hmeas : ∀ k ∈ s, AEMeasurable (X k) P)
    (hherm : ∀ k ∈ s, ∀ᵐ ω ∂P, (X k ω).IsHermitian)
    (hbdd : ∀ k ∈ s, ∃ M : ℝ, ∀ᵐ ω ∂P, ‖X k ω‖ ≤ M)
    {θ t : ℝ} (hθ : 0 < θ) :
    P.real {ω | t ≤ sSup (spectrum ℝ (∑ k ∈ s, X k ω))} ≤
      Real.exp (-θ * t) * RCLike.re (NormedSpace.exp (∑ k ∈ s, cfc Real.log
        (Matrix.of fun i j ↦ ∫ ω, (NormedSpace.exp (θ • X k ω)) i j ∂P))).trace := by
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  let : NormedAlgebra ℚ (Matrix n n 𝕜) := TauCeti.normedAlgebraRatOfReal
  have : MeasurableAdd₂ (Matrix n n 𝕜) := measurableAdd₂_matrix
  let Y : ι → Ω → Matrix n n 𝕜 := fun k ω ↦ θ • X k ω
  have hY_meas := fun k hk ↦ (continuous_const_smul θ).measurable.comp_aemeasurable (hmeas k hk)
  have hY_herm : ∀ k ∈ s, ∀ᵐ ω ∂P, (Y k ω).IsHermitian :=
    fun k hk ↦ (hherm k hk).mono fun _ h ↦ h.smul (IsSelfAdjoint.all θ)
  have hY_bdd : ∀ k ∈ s, ∃ M : ℝ, ∀ᵐ ω ∂P, ‖Y k ω‖ ≤ M := fun k hk ↦ by
    obtain ⟨M, hM⟩ := hbdd k hk
    exact ⟨θ * M, hM.mono fun _ h ↦ by
      simpa only [Y, norm_smul, Real.norm_of_nonneg hθ.le] using mul_le_mul_of_nonneg_left h hθ.le⟩
  have hsum_herm := ae_isHermitian_finsetSum hY_herm
  obtain ⟨MY, hMY⟩ := exists_ae_norm_finsetSum_le hY_bdd
  have hsub : {ω | t ≤ sSup (spectrum ℝ (∑ k ∈ s, X k ω))} ≤ᵐ[P]
      {ω | Real.exp (θ * t) ≤ RCLike.re (NormedSpace.exp (∑ k ∈ s, Y k ω)).trace} :=
    hsum_herm.mono fun ω hω hge ↦ by
      have h1 := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hge hθ.le)
      rw [← Matrix.sSup_spectrum_real_smul_of_nonneg _ hθ.le,
        ← show ∑ k ∈ s, Y k ω = θ • ∑ k ∈ s, X k ω by simp [Y, Finset.smul_sum]] at h1
      exact h1.trans hω.exp_sSup_spectrum_real_le_re_trace_exp
  have hcgf := (hindep.comp (fun _ A ↦ θ • A) fun _ ↦
      (continuous_const_smul θ).measurable).integral_re_trace_exp_add_sum_le
    hY_meas hY_herm hY_bdd isHermitian_zero
  simp only [Function.comp_apply, zero_add] at hcgf
  rw [neg_mul, Real.exp_neg, inv_mul_eq_div, le_div_iff₀' (Real.exp_pos _)]
  exact (mul_le_mul_of_nonneg_left (ENNReal.toReal_mono (measure_ne_top P _) (measure_mono_ae hsub))
    (Real.exp_pos _).le).trans <|
      (mul_meas_ge_le_integral_of_nonneg (hsum_herm.mono fun _ h ↦ h.re_trace_exp_nonneg)
        (Matrix.integrable_re_trace_exp (Finset.aemeasurable_fun_sum s hY_meas) hsum_herm hMY)
        (Real.exp (θ * t))).trans hcgf

/-- **Master matrix Laplace-transform lower tail bound** (Tropp 2012, Theorem 3.6). For independent
a.e. bounded random Hermitian matrices `X k` (`k ∈ s`) on a nonempty index type `n` and any `θ > 0`,
`P {λ_min (∑ k ∈ s, X k) ≤ t} ≤ exp (θ t) * Re Tr exp (∑ k ∈ s, log E[exp (-θ X k)])`. -/
theorem iIndepFun.measureReal_sInf_spectrum_sum_le_le [IsProbabilityMeasure P] [Nonempty n]
    {s : Finset ι} {X : ι → Ω → Matrix n n 𝕜}
    (hindep : iIndepFun X P)
    (hmeas : ∀ k ∈ s, AEMeasurable (X k) P)
    (hherm : ∀ k ∈ s, ∀ᵐ ω ∂P, (X k ω).IsHermitian)
    (hbdd : ∀ k ∈ s, ∃ M : ℝ, ∀ᵐ ω ∂P, ‖X k ω‖ ≤ M)
    {θ t : ℝ} (hθ : 0 < θ) :
    P.real {ω | sInf (spectrum ℝ (∑ k ∈ s, X k ω)) ≤ t} ≤
      Real.exp (θ * t) * RCLike.re (NormedSpace.exp (∑ k ∈ s, cfc Real.log
        (Matrix.of fun i j ↦ ∫ ω, (NormedSpace.exp ((-θ) • X k ω)) i j ∂P))).trace := by
  have h := (hindep.comp (fun _ A ↦ -A) fun _ ↦
      continuous_neg.measurable).measureReal_sSup_spectrum_sum_ge_le
    (fun k hk ↦ continuous_neg.measurable.comp_aemeasurable (hmeas k hk))
    (fun k hk ↦ (hherm k hk).mono fun _ h ↦ h.neg)
    (fun k hk ↦ by obtain ⟨M, hM⟩ := hbdd k hk; exact ⟨M, hM.mono fun _ h ↦ by simpa using h⟩)
    (t := -t) hθ
  simp only [Function.comp_apply] at h
  rw [show {ω | -t ≤ sSup (spectrum ℝ (∑ k ∈ s, -X k ω))} =
      {ω | sInf (spectrum ℝ (∑ k ∈ s, X k ω)) ≤ t} by
    ext ω; simp [Finset.sum_neg_distrib, Matrix.sSup_spectrum_real_neg]] at h
  simpa [neg_smul, smul_neg] using h

end ProbabilityTheory
