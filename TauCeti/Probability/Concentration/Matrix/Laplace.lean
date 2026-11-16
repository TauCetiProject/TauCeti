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

This file develops Tropp's matrix Laplace transform method for sums of independent random Hermitian
matrices over any `RCLike` field `𝕜` (`ℝ` or `ℂ`).

For a random matrix `X : Ω → Matrix n n 𝕜`, we write its expectation entrywise as
`Matrix.of fun i j ↦ ∫ ω, X ω i j ∂P`, which requires no ambient `NormedSpace ℝ` instance in
theorem signatures and coincides with the Bochner integral under the `ℓ²` operator norm.

Combining Lieb's concavity theorem (`Matrix.IsHermitian.concaveOn_re_trace_exp_add_cfc_log`) with
Jensen's inequality for probability integrals (`ConcaveOn.le_map_integral`) yields the single-step
Lieb–Jensen inequality: for a fixed Hermitian matrix `H` and an a.e. bounded random Hermitian matrix
`X`,
`E[Re Tr exp (H + X)] ≤ Re Tr exp (H + log E[exp X])`.
Iterating this bound along an independent family gives Tropp's subadditivity of the matrix
cumulant generating function and master tail inequalities for the largest and smallest eigenvalues
of a sum of independent Hermitian random matrices.

## Main results

* `Matrix.isHermitian_of_integral`, `Matrix.posSemidef_of_integral`,
  `Matrix.of_integral_le_of_integral_of_ae_le`: preservation of Hermitianness, positive
  semidefiniteness, and the Loewner order under entrywise expectation.
* `Matrix.integral_re_trace_exp_add_le`: the single-step Lieb–Jensen inequality.
* `ProbabilityTheory.iIndepFun.integral_re_trace_exp_add_sum_le`: subadditivity of the matrix
  cumulant generating function for independent random Hermitian matrices (Tropp 2012, Theorem 3.6).
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
  have h := congrFun (congrFun hω i) j
  simpa [conjTranspose_apply, RCLike.star_def] using h

/-- Entrywise expectation preserves positive semidefiniteness. -/
theorem posSemidef_of_integral [Finite n] {F : Ω → Matrix n n 𝕜}
    (hF : ∀ᵐ ω ∂P, (F ω).PosSemidef)
    (hint : ∀ i j, Integrable (fun ω ↦ F ω i j) P) :
    (Matrix.of fun i j ↦ ∫ ω, F ω i j ∂P).PosSemidef := by
  have := Fintype.ofFinite n
  refine posSemidef_iff_dotProduct_mulVec.2
    ⟨isHermitian_of_integral (hF.mono fun _ h ↦ h.1), fun x ↦ ?_⟩
  have hquad : star x ⬝ᵥ (Matrix.of fun i j ↦ ∫ ω, F ω i j ∂P) *ᵥ x =
      ∫ ω, star x ⬝ᵥ F ω *ᵥ x ∂P := by
    simp only [dotProduct, mulVec, of_apply, Finset.mul_sum]
    rw [integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦
      ((hint i j).mul_const (x j)).const_mul (star x i)]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [integral_finsetSum _ fun j _ ↦ ((hint i j).mul_const (x j)).const_mul (star x i)]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [integral_const_mul, integral_mul_const]
  rw [hquad, RCLike.nonneg_iff]
  have hre : 0 ≤ᵐ[P] fun ω ↦ RCLike.re (star x ⬝ᵥ F ω *ᵥ x) :=
    hF.mono fun ω hω ↦ (RCLike.nonneg_iff.1 ((posSemidef_iff_dotProduct_mulVec.1 hω).2 x)).1
  have him : (fun ω ↦ RCLike.im (star x ⬝ᵥ F ω *ᵥ x)) =ᵐ[P] fun _ ↦ (0 : ℝ) :=
    hF.mono fun ω hω ↦ (RCLike.nonneg_iff.1 ((posSemidef_iff_dotProduct_mulVec.1 hω).2 x)).2
  have hquad_int : Integrable (fun ω ↦ star x ⬝ᵥ F ω *ᵥ x) P := by
    simp only [dotProduct, mulVec, Finset.mul_sum]
    exact integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦
      ((hint i j).mul_const (x j)).const_mul (star x i)
  refine ⟨?_, ?_⟩
  · rw [← RCLike.reCLM_apply, ← RCLike.reCLM.integral_comp_comm hquad_int]
    exact integral_nonneg_of_ae hre
  · rw [← RCLike.imCLM_apply, ← RCLike.imCLM.integral_comp_comm hquad_int]
    simpa only [RCLike.imCLM_apply] using (integral_congr_ae him).trans (integral_zero _ _)

/-- Entrywise expectation is monotone in the Loewner order. -/
theorem of_integral_le_of_integral_of_ae_le [Finite n] {F G : Ω → Matrix n n 𝕜}
    (hle : ∀ᵐ ω ∂P, F ω ≤ G ω)
    (hF : ∀ i j, Integrable (fun ω ↦ F ω i j) P)
    (hG : ∀ i j, Integrable (fun ω ↦ G ω i j) P) :
    (Matrix.of fun i j ↦ ∫ ω, F ω i j ∂P) ≤ (Matrix.of fun i j ↦ ∫ ω, G ω i j ∂P) := by
  rw [le_iff]
  have hsub : (Matrix.of fun i j ↦ ∫ ω, G ω i j ∂P) - (Matrix.of fun i j ↦ ∫ ω, F ω i j ∂P) =
      Matrix.of fun i j ↦ ∫ ω, (G ω - F ω) i j ∂P := by
    ext i j
    simp [integral_sub (hG i j) (hF i j)]
  rw [hsub]
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

variable {Ω 𝕜 n : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜] [Fintype n] [DecidableEq n]

/-- The entrywise expectation of `exp X` for an a.e. bounded random Hermitian matrix `X` is
positive definite. -/
theorem posDef_of_integral_exp [IsProbabilityMeasure P] {X : Ω → Matrix n n 𝕜}
    (hmeas : AEMeasurable X P) (hherm : ∀ᵐ ω ∂P, (X ω).IsHermitian)
    {M : ℝ} (hbdd : ∀ᵐ ω ∂P, ‖X ω‖ ≤ M) :
    (Matrix.of fun i j ↦ ∫ ω, (NormedSpace.exp (X ω)) i j ∂P).PosDef := by
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  let : NormedAlgebra ℚ (Matrix n n 𝕜) := TauCeti.normedAlgebraRatOfReal
  have hexp_meas : AEMeasurable (fun ω ↦ NormedSpace.exp (X ω)) P :=
    (NormedSpace.exp_continuous (𝔸 := Matrix n n 𝕜)).measurable.comp_aemeasurable hmeas
  have hexp_bdd : ∀ᵐ ω ∂P, ‖NormedSpace.exp (X ω)‖ ≤ Real.exp M :=
    (hherm.and hbdd).mono fun ω ⟨h1, h2⟩ ↦ h1.l2_opNorm_exp_le h2
  have hexp_int : ∀ i j, Integrable (fun ω ↦ (NormedSpace.exp (X ω)) i j) P :=
    integrable_apply_of_ae_l2_opNorm_le hexp_meas hexp_bdd
  have hlo : Real.exp (-M) • (1 : Matrix n n 𝕜) ≤
      Matrix.of fun i j ↦ ∫ ω, (NormedSpace.exp (X ω)) i j ∂P := by
    have hconst : Real.exp (-M) • (1 : Matrix n n 𝕜) =
        Matrix.of fun i j ↦ ∫ _ω, (Real.exp (-M) • (1 : Matrix n n 𝕜)) i j ∂P := by
      ext i j; simp
    rw [hconst]
    exact of_integral_le_of_integral_of_ae_le
      ((hherm.and hbdd).mono fun ω ⟨h1, h2⟩ ↦ (h1.smul_one_le_exp_and_le_smul_one h2).1)
      (fun i j ↦ integrable_const _) hexp_int
  have hdiff : ((Matrix.of fun i j ↦ ∫ ω, (NormedSpace.exp (X ω)) i j ∂P) -
      Real.exp (-M) • (1 : Matrix n n 𝕜)).PosSemidef := le_iff.1 hlo
  have hadd : Real.exp (-M) • (1 : Matrix n n 𝕜) +
      ((Matrix.of fun i j ↦ ∫ ω, (NormedSpace.exp (X ω)) i j ∂P) -
        Real.exp (-M) • (1 : Matrix n n 𝕜)) =
      Matrix.of fun i j ↦ ∫ ω, (NormedSpace.exp (X ω)) i j ∂P := by abel
  rw [← hadd]
  exact ((PosDef.one (n := n) (R := 𝕜)).smul (Real.exp_pos (-M))).add_posSemidef hdiff

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
  have hS_sub : S ⊆ {A : Matrix n n 𝕜 | A.PosDef} := fun A hA ↦ by
    have hdiff : (A - Real.exp (-M) • (1 : Matrix n n 𝕜)).PosSemidef := le_iff.1 hA
    have hadd : Real.exp (-M) • (1 : Matrix n n 𝕜) + (A - Real.exp (-M) • (1 : Matrix n n 𝕜)) = A :=
      by abel
    rw [Set.mem_ofPred_eq, ← hadd]
    exact ((PosDef.one (n := n) (R := 𝕜)).smul (Real.exp_pos (-M))).add_posSemidef hdiff
  have hS_conv : Convex ℝ S := by
    intro A₁ hA₁ A₂ hA₂ a b ha hb hab
    have h1 : a • (Real.exp (-M) • (1 : Matrix n n 𝕜)) ≤ a • A₁ :=
      smul_le_smul_of_nonneg_left hA₁ ha
    have h2 : b • (Real.exp (-M) • (1 : Matrix n n 𝕜)) ≤ b • A₂ :=
      smul_le_smul_of_nonneg_left hA₂ hb
    have hsum := add_le_add h1 h2
    rwa [← add_smul, hab, one_smul] at hsum
  have hg_conc : ConcaveOn ℝ S g :=
    hH.concaveOn_re_trace_exp_add_cfc_log.subset hS_sub hS_conv
  have hg_cont : ContinuousOn g S := by
    have hlog : ContinuousOn (cfc Real.log : Matrix n n 𝕜 → Matrix n n 𝕜) {A | A.PosDef} :=
      (Matrix.contDiffOn_cfc_log (𝕜 := 𝕜) (n := n) (k := 0)).continuousOn
    have htr : Continuous fun Z : Matrix n n 𝕜 ↦ RCLike.re Z.trace :=
      (RCLike.reCLM.comp
        ((traceLinearMap n 𝕜 𝕜).restrictScalars ℝ).toContinuousLinearMap).continuous
    have hcomp : ContinuousOn g {A | A.PosDef} :=
      htr.comp_continuousOn <| (NormedSpace.exp_continuous (𝔸 := Matrix n n 𝕜)).comp_continuousOn <|
        continuousOn_const.add hlog
    exact hcomp.mono hS_sub
  have hS_closed : IsClosed S := isClosed_Ici
  have hY_meas : AEMeasurable Y P :=
    (NormedSpace.exp_continuous (𝔸 := Matrix n n 𝕜)).measurable.comp_aemeasurable hmeas
  have hY_mem : ∀ᵐ ω ∂P, Y ω ∈ S :=
    (hherm.and hbdd).mono fun ω ⟨h1, h2⟩ ↦ (h1.smul_one_le_exp_and_le_smul_one h2).1
  have hY_int : Integrable Y P :=
    Integrable.of_bound hY_meas.aestronglyMeasurable (Real.exp M)
      ((hherm.and hbdd).mono fun ω ⟨h1, h2⟩ ↦ h1.l2_opNorm_exp_le h2)
  have hfg_eq : (fun ω ↦ g (Y ω)) =ᵐ[P] fun ω ↦ RCLike.re (NormedSpace.exp (H + X ω)).trace :=
    hherm.mono fun ω hω ↦ by simp only [g, Y, hω.cfc_log_exp]
  have hHX_meas : AEMeasurable (fun ω ↦ RCLike.re (NormedSpace.exp (H + X ω)).trace) P := by
    have hcont : Continuous fun Z : Matrix n n 𝕜 ↦
        RCLike.re (NormedSpace.exp (H + Z)).trace := by
      have htr : Continuous fun Z : Matrix n n 𝕜 ↦ RCLike.re Z.trace :=
        (RCLike.reCLM.comp
          ((traceLinearMap n 𝕜 𝕜).restrictScalars ℝ).toContinuousLinearMap).continuous
      exact htr.comp ((NormedSpace.exp_continuous (𝔸 := Matrix n n 𝕜)).comp
        (continuous_const.add continuous_id))
    exact hcont.measurable.comp_aemeasurable hmeas
  have hHX_int : Integrable (fun ω ↦ RCLike.re (NormedSpace.exp (H + X ω)).trace) P := by
    refine Integrable.of_bound hHX_meas.aestronglyMeasurable
      ((Fintype.card n : ℝ) * Real.exp (‖H‖ + M)) ((hherm.and hbdd).mono fun ω ⟨h1, h2⟩ ↦ ?_)
    have hsum_herm : (H + X ω).IsHermitian := hH.add h1
    rw [Real.norm_eq_abs, abs_of_nonneg hsum_herm.re_trace_exp_nonneg]
    exact hsum_herm.re_trace_exp_le_card_mul_exp
      (hsum_herm.le_smul_one_of_l2_opNorm_le ((norm_add_le H (X ω)).trans (add_le_add le_rfl h2)))
  have hfg_int : Integrable (g ∘ Y) P := hHX_int.congr hfg_eq.symm
  have hY_eq : ∫ ω, Y ω ∂P = Matrix.of fun i j ↦ ∫ ω, Y ω i j ∂P := by
    ext i j
    let ev : Matrix n n 𝕜 →L[ℝ] 𝕜 :=
      ((Matrix.entryLinearMap 𝕜 𝕜 i j).restrictScalars ℝ).toContinuousLinearMap
    simpa [ev] using (ev.integral_comp_comm hY_int).symm
  have hjensen := hg_conc.le_map_integral hg_cont hS_closed hY_mem hY_int hfg_int
  rw [integral_congr_ae hfg_eq, hY_eq] at hjensen
  exact hjensen

end LiebJensen

end Matrix

/-! ### Subadditivity of matrix CGF and master Laplace tail bounds -/

namespace ProbabilityTheory

section IndepSum

variable {Ω 𝕜 n ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]

/-- Matrix addition is jointly measurable with respect to the entrywise measurable space. -/
private theorem measurableAdd₂_matrix : MeasurableAdd₂ (Matrix n n 𝕜) :=
  ⟨Matrix.measurable_iff.2 fun _ _ ↦
    (Matrix.measurable_apply.comp measurable_fst).add
      (Matrix.measurable_apply.comp measurable_snd)⟩

/-- The set of Hermitian matrices is Borel measurable. -/
private theorem measurableSet_isHermitian [Countable n] :
    MeasurableSet {A : Matrix n n 𝕜 | A.IsHermitian} := by
  have heq : {A : Matrix n n 𝕜 | A.IsHermitian} =
      ⋂ i : n, ⋂ j : n, {A : Matrix n n 𝕜 | star (A j i) = A i j} := by
    ext A
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Matrix.IsHermitian]
    exact ⟨fun h i j ↦ congrFun (congrFun h i) j, fun h ↦ Matrix.ext fun i j ↦ h i j⟩
  rw [heq]
  exact MeasurableSet.iInter fun i ↦ MeasurableSet.iInter fun j ↦
    measurableSet_eq_fun (continuous_star.measurable.comp Matrix.measurable_apply)
      Matrix.measurable_apply

/-- Restricting an independent family to a finite set `insert a s` (`a ∉ s`) yields independence of
the partial sum over `s` from the `a`-th term, assuming a.e. measurability only on `insert a s`. -/
private theorem iIndepFun.indepFun_finsetSum_of_notMem_on [DecidableEq ι] {s : Finset ι} {a : ι}
    {X : ι → Ω → Matrix n n 𝕜} (hindep : iIndepFun X P) (ha : a ∉ s)
    (hmeas : ∀ k ∈ insert a s, AEMeasurable (X k) P) :
    IndepFun (fun ω ↦ ∑ k ∈ s, X k ω) (X a) P := by
  have : MeasurableAdd₂ (Matrix n n 𝕜) := measurableAdd₂_matrix
  let s' : Finset ι := insert a s
  let Y : ↥s' → Ω → Matrix n n 𝕜 := fun k ↦ X k.1
  have hY_indep : iIndepFun Y P := hindep.precomp Subtype.val_injective
  have hY_meas : ∀ k : ↥s', AEMeasurable (Y k) P := fun k ↦ hmeas k.1 k.2
  let t : Finset ↥s' := s.attach.map
    ⟨fun k ↦ ⟨k.1, Finset.mem_insert_of_mem k.2⟩,
      fun k₁ k₂ h ↦ Subtype.ext (by simpa using congrArg Subtype.val h)⟩
  let a' : ↥s' := ⟨a, Finset.mem_insert_self a s⟩
  have ha' : a' ∉ t := by
    simp only [t, Finset.mem_map, Finset.mem_attach, true_and, Subtype.ext_iff, a', not_exists]
    intro k hk
    exact ha (hk ▸ k.2)
  have h := hY_indep.indepFun_finsetSum_of_notMem₀ hY_meas ha'
  have hsum : (∑ k ∈ t, Y k) = fun ω ↦ ∑ k ∈ s, X k ω := by
    funext ω
    simp only [Finset.sum_apply, t, Finset.sum_map, Y]
    exact Finset.sum_attach s (fun k ↦ X k ω)
  rwa [hsum] at h

end IndepSum

variable {Ω 𝕜 n ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜] [Fintype n] [DecidableEq n]

/-- The closed `ℓ²` operator-norm ball `{A | ‖A‖ ≤ M}` is Borel measurable. -/
private theorem measurableSet_l2_opNorm_le (M : ℝ) :
    MeasurableSet {A : Matrix n n 𝕜 | ‖A‖ ≤ M} :=
  (isClosed_le continuous_norm continuous_const).measurableSet

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
  have htr_cont : Continuous fun Z : Matrix n n 𝕜 ↦ RCLike.re Z.trace :=
    (RCLike.reCLM.comp ((traceLinearMap n 𝕜 𝕜).restrictScalars ℝ).toContinuousLinearMap).continuous
  have hφ_cont : Continuous φ :=
    htr_cont.comp <| (NormedSpace.exp_continuous (𝔸 := Matrix n n 𝕜)).comp <|
      (continuous_const.add continuous_fst).add continuous_snd
  have hφ_int_P : Integrable (fun ω ↦ φ (S ω, X ω)) P := by
    refine Integrable.of_bound
      (hφ_cont.measurable.comp_aemeasurable (hS_meas.prodMk hX_meas)).aestronglyMeasurable
      ((Fintype.card n : ℝ) * Real.exp (‖H‖ + MS + MX))
      (((hS_herm.and hX_herm).and (hS_bdd.and hX_bdd)).mono fun ω ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ ↦ ?_)
    have hHsum : (H + S ω + X ω).IsHermitian := (hH.add h1).add h2
    rw [Real.norm_eq_abs, abs_of_nonneg hHsum.re_trace_exp_nonneg]
    exact hHsum.re_trace_exp_le_card_mul_exp <|
      hHsum.le_smul_one_of_l2_opNorm_le <|
        (norm_add_le _ _).trans <| add_le_add ((norm_add_le _ _).trans (add_le_add le_rfl h3)) h4
  have hmap_prod : P.map (fun ω ↦ (S ω, X ω)) = (P.map S).prod (P.map X) :=
    hind.map_prod_eq_prod_map_map hS_meas hX_meas
  have hφ_int_prod : Integrable φ ((P.map S).prod (P.map X)) := by
    rw [← hmap_prod]
    exact (integrable_map_measure hφ_cont.aestronglyMeasurable (hS_meas.prodMk hX_meas)).2 hφ_int_P
  have hX_herm_map : ∀ᵐ B ∂(P.map X), B.IsHermitian :=
    (ae_map_iff hX_meas measurableSet_isHermitian).2 hX_herm
  have hX_bdd_map : ∀ᵐ B ∂(P.map X), ‖B‖ ≤ MX :=
    (ae_map_iff hX_meas (measurableSet_l2_opNorm_le MX)).2 hX_bdd
  have hS_herm_map : ∀ᵐ A ∂(P.map S), A.IsHermitian :=
    (ae_map_iff hS_meas measurableSet_isHermitian).2 hS_herm
  have hS_bdd_map : ∀ᵐ A ∂(P.map S), ‖A‖ ≤ MS :=
    (ae_map_iff hS_meas (measurableSet_l2_opNorm_le MS)).2 hS_bdd
  have hexp_map : (Matrix.of fun i j ↦ ∫ B, (NormedSpace.exp B) i j ∂(P.map X)) =
      Matrix.of fun i j ↦ ∫ ω, (NormedSpace.exp (X ω)) i j ∂P := by
    ext i j
    have hcont : Continuous fun B : Matrix n n 𝕜 ↦ (NormedSpace.exp B) i j :=
      (continuous_apply j).comp ((continuous_apply i).comp
        (NormedSpace.exp_continuous (𝔸 := Matrix n n 𝕜)))
    exact integral_map hX_meas hcont.aestronglyMeasurable
  let L : Matrix n n 𝕜 :=
    cfc Real.log (Matrix.of fun i j ↦ ∫ ω, (NormedSpace.exp (X ω)) i j ∂P)
  have hL_herm : L.IsHermitian :=
    IsSelfAdjoint.isHermitian (cfc_predicate Real.log
      (Matrix.of fun i j ↦ ∫ ω, (NormedSpace.exp (X ω)) i j ∂P))
  have hinner : ∀ᵐ A ∂(P.map S),
      (∫ B, φ (A, B) ∂(P.map X)) ≤ RCLike.re (NormedSpace.exp ((H + L) + A)).trace := by
    refine hS_herm_map.mono fun A hA ↦ ?_
    have hstep := Matrix.integral_re_trace_exp_add_le (P := P.map X)
      (hH.add hA) aemeasurable_id hX_herm_map hX_bdd_map
    simp only [id_eq] at hstep
    rw [hexp_map, add_right_comm H A L] at hstep
    exact hstep
  have hrhs_cont : Continuous fun A : Matrix n n 𝕜 ↦
      RCLike.re (NormedSpace.exp ((H + L) + A)).trace :=
    htr_cont.comp <| (NormedSpace.exp_continuous (𝔸 := Matrix n n 𝕜)).comp <|
      continuous_const.add continuous_id
  have hrhs_int :
      Integrable (fun A ↦ RCLike.re (NormedSpace.exp ((H + L) + A)).trace) (P.map S) := by
    refine Integrable.of_bound hrhs_cont.aestronglyMeasurable
      ((Fintype.card n : ℝ) * Real.exp (‖H + L‖ + MS))
      ((hS_herm_map.and hS_bdd_map).mono fun A ⟨hA1, hA2⟩ ↦ ?_)
    have hsum : ((H + L) + A).IsHermitian := (hH.add hL_herm).add hA1
    rw [Real.norm_eq_abs, abs_of_nonneg hsum.re_trace_exp_nonneg]
    exact hsum.re_trace_exp_le_card_mul_exp <|
      hsum.le_smul_one_of_l2_opNorm_le ((norm_add_le _ _).trans (add_le_add le_rfl hA2))
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
    have hmeas_t : ∀ k ∈ t, AEMeasurable (X k) P := fun k hk ↦ hmeas k (Finset.mem_insert_of_mem hk)
    have hherm_t : ∀ k ∈ t, ∀ᵐ ω ∂P, (X k ω).IsHermitian :=
      fun k hk ↦ hherm k (Finset.mem_insert_of_mem hk)
    have hbdd_t : ∀ k ∈ t, ∃ M : ℝ, ∀ᵐ ω ∂P, ‖X k ω‖ ≤ M :=
      fun k hk ↦ hbdd k (Finset.mem_insert_of_mem hk)
    obtain ⟨Ma, hMa⟩ := hbdd a (Finset.mem_insert_self a t)
    let S : Ω → Matrix n n 𝕜 := fun ω ↦ ∑ k ∈ t, X k ω
    have hS_meas : AEMeasurable S P := Finset.aemeasurable_fun_sum t fun k hk ↦ hmeas_t k hk
    have hS_herm : ∀ᵐ ω ∂P, (S ω).IsHermitian := by
      have hall : ∀ᵐ ω ∂P, ∀ k ∈ t, (X k ω).IsHermitian :=
        (ae_ball_iff t.countable_toSet).2 hherm_t
      exact hall.mono fun ω hω ↦
        Finset.sum_induction _ _ (fun _ _ h₁ h₂ ↦ h₁.add h₂) isHermitian_zero hω
    obtain ⟨MS, hMS⟩ : ∃ MS : ℝ, ∀ᵐ ω ∂P, ‖S ω‖ ≤ MS := by
      choose M hM using hbdd_t
      refine ⟨∑ k ∈ t.attach, M k.1 k.2, ?_⟩
      have hall : ∀ᵐ ω ∂P, ∀ k : ↥t, ‖X k.1 ω‖ ≤ M k.1 k.2 :=
        ae_all_iff.2 fun k ↦ hM k.1 k.2
      refine hall.mono fun ω hω ↦ (norm_sum_le t fun k ↦ X k ω).trans ?_
      rw [← Finset.sum_attach t (fun k ↦ ‖X k ω‖)]
      exact Finset.sum_le_sum fun k _ ↦ hω k
    have hind : IndepFun S (X a) P := hindep.indepFun_finsetSum_of_notMem_on ha hmeas
    let La : Matrix n n 𝕜 :=
      cfc Real.log (Matrix.of fun i j ↦ ∫ ω, (NormedSpace.exp (X a ω)) i j ∂P)
    have hLa_herm : La.IsHermitian :=
      IsSelfAdjoint.isHermitian (cfc_predicate Real.log
        (Matrix.of fun i j ↦ ∫ ω, (NormedSpace.exp (X a ω)) i j ∂P))
    have harg (ω : Ω) : H + ∑ k ∈ insert a t, X k ω = H + S ω + X a ω := by
      rw [Finset.sum_insert ha, ← add_assoc, add_right_comm H (X a ω) (S ω)]
    simp_rw [harg]
    have h1 := hind.integral_re_trace_exp_add_add_le hS_meas
      (hmeas a (Finset.mem_insert_self a t)) hS_herm (hherm a (Finset.mem_insert_self a t))
      hMS hMa hH
    have h2 := ih hmeas_t hherm_t hbdd_t (hH.add hLa_herm)
    exact (h1.trans h2).trans_eq (by rw [Finset.sum_insert ha, add_assoc])

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
  have hY_indep : iIndepFun Y P :=
    hindep.comp (fun _ A ↦ θ • A) fun _ ↦ (continuous_const_smul θ).measurable
  have hY_meas : ∀ k ∈ s, AEMeasurable (Y k) P :=
    fun k hk ↦ (continuous_const_smul θ).measurable.comp_aemeasurable (hmeas k hk)
  have hY_herm : ∀ k ∈ s, ∀ᵐ ω ∂P, (Y k ω).IsHermitian :=
    fun k hk ↦ (hherm k hk).mono fun _ h ↦ h.smul (IsSelfAdjoint.all θ)
  have hY_bdd : ∀ k ∈ s, ∃ M : ℝ, ∀ᵐ ω ∂P, ‖Y k ω‖ ≤ M := by
    intro k hk
    obtain ⟨M, hM⟩ := hbdd k hk
    refine ⟨θ * M, hM.mono fun ω hω ↦ ?_⟩
    dsimp only [Y]
    rw [norm_smul, Real.norm_of_nonneg hθ.le]
    exact mul_le_mul_of_nonneg_left hω hθ.le
  let f : Ω → ℝ := fun ω ↦ RCLike.re (NormedSpace.exp (∑ k ∈ s, Y k ω)).trace
  have hsum_herm : ∀ᵐ ω ∂P, (∑ k ∈ s, Y k ω).IsHermitian := by
    have hall : ∀ᵐ ω ∂P, ∀ k ∈ s, (Y k ω).IsHermitian :=
      (ae_ball_iff s.countable_toSet).2 hY_herm
    exact hall.mono fun ω hω ↦
      Finset.sum_induction _ _ (fun _ _ h₁ h₂ ↦ h₁.add h₂) isHermitian_zero hω
  have hf_nonneg : 0 ≤ᵐ[P] f := hsum_herm.mono fun _ h ↦ h.re_trace_exp_nonneg
  have hf_int : Integrable f P := by
    choose M hM using hY_bdd
    have hall : ∀ᵐ ω ∂P, ∀ k : ↥s, ‖Y k.1 ω‖ ≤ M k.1 k.2 := ae_all_iff.2 fun k ↦ hM k.1 k.2
    have htr_cont : Continuous fun Z : Matrix n n 𝕜 ↦ RCLike.re (NormedSpace.exp Z).trace :=
      (RCLike.reCLM.comp
        ((traceLinearMap n 𝕜 𝕜).restrictScalars ℝ).toContinuousLinearMap).continuous.comp
        (NormedSpace.exp_continuous (𝔸 := Matrix n n 𝕜))
    have hsum_meas : AEMeasurable (fun ω ↦ ∑ k ∈ s, Y k ω) P :=
      Finset.aemeasurable_fun_sum s hY_meas
    refine Integrable.of_bound
      (htr_cont.measurable.comp_aemeasurable hsum_meas).aestronglyMeasurable
      ((Fintype.card n : ℝ) * Real.exp (∑ k ∈ s.attach, M k.1 k.2))
      ((hsum_herm.and hall).mono fun ω ⟨h1, h2⟩ ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg h1.re_trace_exp_nonneg]
    refine h1.re_trace_exp_le_card_mul_exp (h1.le_smul_one_of_l2_opNorm_le ?_)
    refine (norm_sum_le s fun k ↦ Y k ω).trans ?_
    rw [← Finset.sum_attach s (fun k ↦ ‖Y k ω‖)]
    exact Finset.sum_le_sum fun k _ ↦ h2 k
  -- On the Hermitian locus, `t ≤ λ_max(∑ X k)` implies `exp (θ t) ≤ Re Tr exp (∑ θ X k)`.
  have hsub : {ω | t ≤ sSup (spectrum ℝ (∑ k ∈ s, X k ω))} ≤ᵐ[P]
      {ω | Real.exp (θ * t) ≤ f ω} := by
    refine hsum_herm.mono fun ω hω hge ↦ ?_
    have hsmul : ∑ k ∈ s, Y k ω = θ • ∑ k ∈ s, X k ω := by
      simp [Y, Finset.smul_sum]
    calc
      Real.exp (θ * t) ≤ Real.exp (θ * sSup (spectrum ℝ (∑ k ∈ s, X k ω))) :=
        Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hge hθ.le)
      _ = Real.exp (sSup (spectrum ℝ (∑ k ∈ s, Y k ω))) := by
        rw [hsmul, Matrix.sSup_spectrum_real_smul_of_nonneg _ hθ.le]
      _ ≤ f ω := hω.exp_sSup_spectrum_real_le_re_trace_exp
  have hmeas_le : P.real {ω | t ≤ sSup (spectrum ℝ (∑ k ∈ s, X k ω))} ≤
      P.real {ω | Real.exp (θ * t) ≤ f ω} :=
    ENNReal.toReal_mono (measure_ne_top P _) (measure_mono_ae hsub)
  have hmarkov := mul_meas_ge_le_integral_of_nonneg hf_nonneg hf_int (Real.exp (θ * t))
  have hcgf := hY_indep.integral_re_trace_exp_add_sum_le hY_meas hY_herm hY_bdd isHermitian_zero
  simp only [zero_add] at hcgf
  have hmul : Real.exp (θ * t) * P.real {ω | t ≤ sSup (spectrum ℝ (∑ k ∈ s, X k ω))} ≤
      RCLike.re (NormedSpace.exp (∑ k ∈ s, cfc Real.log
        (Matrix.of fun i j ↦ ∫ ω, (NormedSpace.exp (θ • X k ω)) i j ∂P))).trace :=
    (mul_le_mul_of_nonneg_left hmeas_le (Real.exp_pos _).le).trans (hmarkov.trans hcgf)
  rw [neg_mul, Real.exp_neg, inv_mul_eq_div, le_div_iff₀' (Real.exp_pos _)]
  exact hmul

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
  have hneg_indep : iIndepFun (fun k ω ↦ -X k ω) P :=
    hindep.comp (fun _ A ↦ -A) fun _ ↦ continuous_neg.measurable
  have hneg_meas : ∀ k ∈ s, AEMeasurable (fun ω ↦ -X k ω) P :=
    fun k hk ↦ continuous_neg.measurable.comp_aemeasurable (hmeas k hk)
  have hneg_herm : ∀ k ∈ s, ∀ᵐ ω ∂P, (-X k ω).IsHermitian :=
    fun k hk ↦ (hherm k hk).mono fun _ h ↦ h.neg
  have hneg_bdd : ∀ k ∈ s, ∃ M : ℝ, ∀ᵐ ω ∂P, ‖-X k ω‖ ≤ M := by
    intro k hk
    obtain ⟨M, hM⟩ := hbdd k hk
    exact ⟨M, hM.mono fun _ h ↦ by simpa using h⟩
  have h := hneg_indep.measureReal_sSup_spectrum_sum_ge_le hneg_meas hneg_herm hneg_bdd
    (t := -t) hθ
  have hset : {ω | -t ≤ sSup (spectrum ℝ (∑ k ∈ s, -X k ω))} =
      {ω | sInf (spectrum ℝ (∑ k ∈ s, X k ω)) ≤ t} := by
    ext ω
    simp [Finset.sum_neg_distrib, Matrix.sSup_spectrum_real_neg]
  rw [hset] at h
  simpa [neg_smul, smul_neg] using h

end ProbabilityTheory
