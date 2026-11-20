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
import TauCeti.Analysis.Matrix.MeasurableSpace
import TauCeti.Analysis.Matrix.Order
import TauCeti.Analysis.Normed.Algebra.Basic
import TauCeti.MeasureTheory.Integral.PosSemidef
import TauCeti.Probability.Independence.Basic

/-!
# Matrix Laplace transform method

Tropp's matrix Laplace transform method for sums of independent random Hermitian matrices over any
`RCLike` field `𝕜` (`ℝ` or `ℂ`). Expectations are written entrywise as
`Matrix.of fun i j ↦ ∫ ω, X ω i j ∂P`, coinciding with the Bochner integral under the `ℓ²` operator
norm. Combining Lieb's concavity (`Matrix.IsHermitian.concaveOn_re_trace_exp_add_cfc_log`) with
Jensen's inequality yields the single-step Lieb–Jensen bound, subadditivity of the matrix CGF, and
master upper and lower eigenvalue tail inequalities.

## Main results

* `Matrix.isHermitian_integral_of_ae_isHermitian`, `Matrix.integral_le_integral_of_ae_le`:
  preservation of Hermitianness and the Loewner order under entrywise expectation.
* `Matrix.integral_add_eq_add_integral`, `Matrix.integral_smul_eq_smul_integral`,
  `Matrix.integral_const_add_smul`: linearity of entrywise expectation.
* `Matrix.posDef_integral_exp`: positive definiteness of `E[exp X]`.
* `Matrix.integral_re_trace_exp_add_le`: the single-step Lieb–Jensen inequality.
* `ProbabilityTheory.ae_isHermitian_finsetSum`, `ProbabilityTheory.ae_posSemidef_finsetSum`:
  finite sums of a.e. Hermitian or positive semidefinite random matrices preserve those properties.
* `ProbabilityTheory.iIndepFun.integral_re_trace_exp_add_sum_le`: subadditivity of the matrix CGF
  for independent random Hermitian matrices (Tropp 2012, Lemma 3.4).
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
theorem isHermitian_integral_of_ae_isHermitian {F : Ω → Matrix n n 𝕜}
    (hF : ∀ᵐ ω ∂P, (F ω).IsHermitian) :
    (Matrix.of fun i j ↦ ∫ ω, F ω i j ∂P).IsHermitian := by
  ext i j
  simp only [conjTranspose_apply, of_apply, RCLike.star_def, ← integral_conj]
  refine integral_congr_ae (hF.mono fun ω hω ↦ ?_)
  simpa [conjTranspose_apply, RCLike.star_def] using congrFun (congrFun hω i) j

/-- Entrywise expectation is monotone in the Loewner order. -/
theorem integral_le_integral_of_ae_le [Finite n] {F G : Ω → Matrix n n 𝕜}
    (hle : ∀ᵐ ω ∂P, F ω ≤ G ω)
    (hF : ∀ i j, Integrable (fun ω ↦ F ω i j) P)
    (hG : ∀ i j, Integrable (fun ω ↦ G ω i j) P) :
    (Matrix.of fun i j ↦ ∫ ω, F ω i j ∂P) ≤ (Matrix.of fun i j ↦ ∫ ω, G ω i j ∂P) := by
  rw [le_iff, show (Matrix.of fun i j ↦ ∫ ω, G ω i j ∂P) -
      (Matrix.of fun i j ↦ ∫ ω, F ω i j ∂P) = Matrix.of fun i j ↦ ∫ ω, (G ω - F ω) i j ∂P by
    ext i j; simp [integral_sub (hG i j) (hF i j)]]
  exact TauCeti.posSemidef_integral (hle.mono fun _ h ↦ le_iff.1 h)
    fun i j ↦ (hG i j).sub (hF i j)

/-- Entrywise expectation of a pointwise sum of random matrices is the sum of their entrywise
expectations. -/
theorem integral_add_eq_add_integral {m E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F G : Ω → Matrix m n E} (hF : ∀ i j, Integrable (fun ω ↦ F ω i j) P)
    (hG : ∀ i j, Integrable (fun ω ↦ G ω i j) P) :
    (Matrix.of fun i j ↦ ∫ ω, (F ω + G ω) i j ∂P) =
      (Matrix.of fun i j ↦ ∫ ω, F ω i j ∂P) + (Matrix.of fun i j ↦ ∫ ω, G ω i j ∂P) := by
  ext i j; simp only [of_apply, Matrix.add_apply, integral_add (hF i j) (hG i j)]

/-- Entrywise expectation commutes with real scalar multiplication. -/
theorem integral_smul_eq_smul_integral {m E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℝ) (F : Ω → Matrix m n E) :
    (Matrix.of fun i j ↦ ∫ ω, (c • F ω) i j ∂P) =
      c • (Matrix.of fun i j ↦ ∫ ω, F ω i j ∂P) := by
  ext i j; simp only [of_apply, Matrix.smul_apply, integral_smul]

/-- Under a probability measure, the entrywise expectation of `A + c • F` is `A + c • E[F]`. -/
theorem integral_const_add_smul [IsProbabilityMeasure P] {m E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (A : Matrix m n E) (c : ℝ) {F : Ω → Matrix m n E}
    (hF : ∀ i j, Integrable (fun ω ↦ F ω i j) P) :
    (Matrix.of fun i j ↦ ∫ ω, (A + c • F ω) i j ∂P) =
      A + c • (Matrix.of fun i j ↦ ∫ ω, F ω i j ∂P) := by
  rw [integral_add_eq_add_integral (F := fun _ ↦ A) (G := fun ω ↦ c • F ω)
      (fun _ _ ↦ integrable_const _) (fun i j ↦ (hF i j).smul c),
    integral_smul_eq_smul_integral]
  congr 1; ext i j; simp only [of_apply, integral_const, probReal_univ, one_smul]

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
  [MeasurableSpace 𝕜] [BorelSpace 𝕜] [Fintype n] [DecidableEq n]

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
theorem posDef_integral_exp [IsProbabilityMeasure P] {X : Ω → Matrix n n 𝕜}
    (hmeas : AEMeasurable X P) (hherm : ∀ᵐ ω ∂P, (X ω).IsHermitian)
    {M : ℝ} (hbdd : ∀ᵐ ω ∂P, ‖X ω‖ ≤ M) :
    (Matrix.of fun i j ↦ ∫ ω, (NormedSpace.exp (X ω)) i j ∂P).PosDef := by
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  let : NormedAlgebra ℚ (Matrix n n 𝕜) := TauCeti.normedAlgebraRatOfReal
  refine ((PosDef.one (n := n) (R := 𝕜)).smul (Real.exp_pos (-M))).of_le ?_
  rw [show Real.exp (-M) • (1 : Matrix n n 𝕜) =
      Matrix.of fun i j ↦ ∫ _ω, (Real.exp (-M) • (1 : Matrix n n 𝕜)) i j ∂P by ext i j; simp]
  exact integral_le_integral_of_ae_le
    ((hherm.and hbdd).mono fun _ ⟨h1, h2⟩ ↦ (h1.smul_one_le_exp_and_le_smul_one h2).1)
    (fun _ _ ↦ integrable_const _)
    (integrable_apply_of_ae_l2_opNorm_le
      ((NormedSpace.exp_continuous (𝔸 := Matrix n n 𝕜)).measurable.comp_aemeasurable hmeas)
      (hbdd.mono fun _ h ↦ Matrix.l2_opNorm_exp_le h))

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
    fun _ hA ↦ ((PosDef.one (n := n) (R := 𝕜)).smul (Real.exp_pos (-M))).of_le hA
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
    (Real.exp M) (hbdd.mono fun _ h ↦ Matrix.l2_opNorm_exp_le h)
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

section FinsetSum

variable {Ω n ι R : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- A finite sum of a.e. Hermitian random matrices is a.e. Hermitian. -/
theorem ae_isHermitian_finsetSum [AddCommMonoid R] [StarAddMonoid R]
    {s : Finset ι} {X : ι → Ω → Matrix n n R}
    (hherm : ∀ k ∈ s, ∀ᵐ ω ∂P, (X k ω).IsHermitian) :
    ∀ᵐ ω ∂P, (∑ k ∈ s, X k ω).IsHermitian :=
  (Filter.eventually_all_finset s).2 hherm |>.mono fun _ hω ↦
    (isSelfAdjoint_sum s fun k hk ↦ (hω k hk).isSelfAdjoint).isHermitian

/-- A finite sum of a.e. positive semidefinite random matrices is a.e. positive semidefinite. -/
theorem ae_posSemidef_finsetSum [Ring R] [PartialOrder R] [StarRing R] [AddLeftMono R]
    {s : Finset ι} {X : ι → Ω → Matrix n n R}
    (hpsd : ∀ k ∈ s, ∀ᵐ ω ∂P, (X k ω).PosSemidef) :
    ∀ᵐ ω ∂P, (∑ k ∈ s, X k ω).PosSemidef :=
  (Filter.eventually_all_finset s).2 hpsd |>.mono fun _ hω ↦ Matrix.posSemidef_sum s hω

end FinsetSum

variable {Ω 𝕜 n ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [RCLike 𝕜] [Fintype n] [DecidableEq n] [MeasurableSpace 𝕜] [BorelSpace 𝕜]

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
  have hS_herm_map :=
    (ae_map_iff hS_meas Matrix.isClosed_setOfPred_isHermitian.measurableSet).2 hS_herm
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
        ((ae_map_iff hX_meas Matrix.isClosed_setOfPred_isHermitian.measurableSet).2 hX_herm)
        ((ae_map_iff hX_meas (isClosed_le continuous_norm continuous_const).measurableSet).2 hX_bdd)
      simp only [id_eq] at hstep; rwa [hexp_map, add_right_comm H A L] at hstep
  have hrhs_cont : Continuous fun A : Matrix n n 𝕜 ↦
      RCLike.re (NormedSpace.exp ((H + L) + A)).trace :=
    Matrix.continuous_re_trace.comp <| (NormedSpace.exp_continuous (𝔸 := Matrix n n 𝕜)).comp <|
      continuous_const.add continuous_id
  have hL : L.IsHermitian := IsSelfAdjoint.isHermitian (cfc_predicate Real.log _)
  have hrhs_int := Matrix.integrable_re_trace_exp (P := P.map S) (Z := fun A ↦ (H + L) + A)
    (continuous_const.add continuous_id).measurable.aemeasurable
    (hS_herm_map.mono fun _ h ↦ (hH.add hL).add h)
    (hS_bdd_map.mono fun _ h ↦ (norm_add_le _ _).trans (add_le_add le_rfl h))
  rw [← integral_map (hS_meas.prodMk hX_meas) hφ_cont.aestronglyMeasurable, hmap_prod,
    integral_prod φ hφ_int_prod, ← integral_map hS_meas hrhs_cont.aestronglyMeasurable]
  exact integral_mono_ae hφ_int_prod.integral_prod_left hrhs_int hinner

/-- **Subadditivity of the matrix cumulant generating function** (Tropp 2012, Lemma 3.4). For
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
  induction s using Finset.induction_on generalizing H with
  | empty => simp
  | insert a t ha ih =>
    have hmeas_t := fun k hk ↦ hmeas k (Finset.mem_insert_of_mem hk)
    have hherm_t := fun k hk ↦ hherm k (Finset.mem_insert_of_mem hk)
    have hbdd_t := fun k hk ↦ hbdd k (Finset.mem_insert_of_mem hk)
    obtain ⟨Ma, hMa⟩ := hbdd a (Finset.mem_insert_self a t)
    obtain ⟨MS, hMS⟩ := Filter.isBoundedUnder_le_sum (f := ae P) (u := fun k ω ↦ ‖X k ω‖) t
      fun k hk ↦ let ⟨M, hM⟩ := hbdd_t k hk; ⟨M, Filter.eventually_map.2 hM⟩
    simp_rw [Finset.sum_insert ha, ← add_assoc, add_right_comm H (X a _)]
    have hind : IndepFun (fun ω ↦ ∑ k ∈ t, X k ω) (X a) P :=
      (funext fun ω ↦ Finset.sum_apply ω t X) ▸
        hindep.indepFun_finsetSum_of_notMem₀_on ha hmeas_t (hmeas a (Finset.mem_insert_self a t))
    refine (hind.integral_re_trace_exp_add_add_le
      (Finset.aemeasurable_fun_sum t hmeas_t) (hmeas a (Finset.mem_insert_self a t))
      (ae_isHermitian_finsetSum hherm_t) (hherm a (Finset.mem_insert_self a t))
      ((Filter.eventually_map.1 hMS).mono fun _ hω ↦
        (norm_sum_le t _).trans (by simpa only [Finset.sum_apply] using hω)) hMa hH).trans ?_
    exact ih hmeas_t hherm_t hbdd_t
      (hH.add <| IsSelfAdjoint.isHermitian (cfc_predicate Real.log _))

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
  let Y : ι → Ω → Matrix n n 𝕜 := fun k ω ↦ θ • X k ω
  have hY_meas := fun k hk ↦ (continuous_const_smul θ).measurable.comp_aemeasurable (hmeas k hk)
  have hY_herm : ∀ k ∈ s, ∀ᵐ ω ∂P, (Y k ω).IsHermitian :=
    fun k hk ↦ (hherm k hk).mono fun _ h ↦ h.smul (IsSelfAdjoint.all θ)
  have hY_bdd : ∀ k ∈ s, ∃ M : ℝ, ∀ᵐ ω ∂P, ‖Y k ω‖ ≤ M := fun k hk ↦
    let ⟨M, hM⟩ := hbdd k hk
    ⟨θ * M, hM.mono fun _ h ↦ by
      simpa only [Y, norm_smul, Real.norm_of_nonneg hθ.le] using mul_le_mul_of_nonneg_left h hθ.le⟩
  have hsum_herm := ae_isHermitian_finsetSum hY_herm
  obtain ⟨MY, hMY⟩ := Filter.isBoundedUnder_le_sum (f := ae P) (u := fun k ω ↦ ‖Y k ω‖) s
    fun k hk ↦ let ⟨M, hM⟩ := hY_bdd k hk; ⟨M, Filter.eventually_map.2 hM⟩
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
        (Matrix.integrable_re_trace_exp (Finset.aemeasurable_fun_sum s hY_meas) hsum_herm
          ((Filter.eventually_map.1 hMY).mono fun _ hω ↦
            (norm_sum_le s _).trans (by simpa only [Finset.sum_apply] using hω)))
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
