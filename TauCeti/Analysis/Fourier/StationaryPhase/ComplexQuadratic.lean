/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.Normed
public import TauCeti.Analysis.Fourier.StationaryPhase.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import TauCeti.Analysis.Normed.Algebra.SquareRoot
import TauCeti.LinearAlgebra.BilinearForm.Basic
import TauCeti.LinearAlgebra.BilinearForm.Diagonalization
import TauCeti.LinearAlgebra.Complex.Determinant
import TauCeti.LinearAlgebra.Matrix.BilinearForm
import TauCeti.LinearAlgebra.Matrix.ToLinearEquiv
import TauCeti.Topology.Instances.Matrix

/-! # Normalization of complex quadratic phases -/

public section

open Filter LinearMap Matrix Metric Set Topology

namespace TauCeti

open scoped Matrix.Norms.Operator

private theorem analyticOnNhd_complex_sqrtNearOne {A : Type*} [NormedRing A]
    [NormedAlgebra ℂ A] [CompleteSpace A] :
    AnalyticOnNhd ℂ (sqrtNearOne A) (Metric.ball 1 1) := by
  intro x hx
  rw [Metric.mem_ball, dist_eq_norm] at hx
  let a : ℂ := ((2⁻¹ : ℝ) : ℂ)
  have hsum := ((binomialSeries A a).hasFPowerSeriesOnBall
    (zero_lt_one.trans_le (binomialSeries_radius_ge_one_of_normedRing a))).analyticAt_of_mem
      (mem_eball_binomialSeries_radius hx a)
  have hsub : AnalyticAt ℂ (fun z : A ↦ z - 1) x := analyticAt_id.sub analyticAt_const
  have he (z : A) : (binomialSeries A a).sum (z - 1) = sqrtNearOne A z := by
    rw [binomialSeries_sum_eq_tsum, sqrtNearOne_eq_tsum]
    simp only [a, ← Complex.ofReal_choose, RCLike.real_smul_eq_coe_smul (K := ℂ)]
    rfl
  exact (hsum.comp_of_eq hsub rfl).congr (Filter.Eventually.of_forall he)

private theorem sqrtNearOne_matrix_congr {n : ℕ} {A H : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsSymm) (hdet : IsUnit A.det) (hH : H.IsSymm) (hclose : ‖A⁻¹ * H - 1‖ < 1) :
    (sqrtNearOne _ (A⁻¹ * H))ᵀ * A * sqrtNearOne _ (A⁻¹ * H) = H := by
  let adj : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ := fun R ↦ A⁻¹ * Rᵀ * A
  let X := A⁻¹ * H - 1
  have hadj : Continuous adj :=
    (continuous_const.mul continuous_id.matrix_transpose).mul continuous_const
  have hm (P Q : Matrix (Fin n) (Fin n) ℂ) : adj (P * Q) = adj Q * adj P := by
    simp only [adj, transpose_mul, Matrix.mul_assoc, A.mul_nonsing_inv_cancel_left _ hdet]
  have h₁ : adj 1 = 1 := by simp [adj, A.nonsing_inv_mul hdet]
  have hX : adj X = X := by
    simp only [X, adj, transpose_sub, transpose_one, transpose_mul, transpose_nonsing_inv,
      hA.eq, hH.eq, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul,
      Matrix.mul_assoc, A.nonsing_inv_mul hdet]
  have hpow (j : ℕ) : adj (X ^ j) = X ^ j := by
    induction j with
    | zero => simpa only [pow_zero] using h₁
    | succ j ih =>
      rw [pow_succ, hm, hX, ih, ← pow_succ']
      exact pow_succ X j
  let T := sqrtNearOne _ (A⁻¹ * H)
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    { toFun := adj
      map_add' := fun P Q ↦ by simp [adj, Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c P ↦ by simp [adj] }
  have hsum : HasSum (fun j ↦ Ring.choose (2⁻¹ : ℝ) j • X ^ j) (adj T) := by
    have hT : HasSum (fun j ↦ Ring.choose (2⁻¹ : ℝ) j • X ^ j) T :=
      hasSum_sqrtNearOne hclose
    have h := hT.map L hadj
    have hL (j : ℕ) : L (X ^ j) = X ^ j := hpow j
    change HasSum (fun j ↦ Ring.choose (2⁻¹ : ℝ) j • X ^ j) (L T)
    simpa only [Function.comp_def, map_smul, hL] using h
  have hfix : adj T = T := hsum.unique (hasSum_sqrtNearOne hclose)
  have hAT : Tᵀ * A = A * T := by
    simpa only [adj, ← Matrix.mul_assoc, A.mul_nonsing_inv hdet, Matrix.one_mul] using
      congrArg (fun S ↦ A * S) hfix
  change Tᵀ * A * T = H
  rw [hAT, Matrix.mul_assoc, show T * T = A⁻¹ * H from mul_self_sqrtNearOne hclose,
    A.mul_nonsing_inv_cancel_left H hdet]

/-- An analytic family of quadratic forms with nonsingular value at zero can be reduced to
that value by a bounded analytic map with identity derivative. The radius and bound are uniform
for a bounded family of forms whose values at zero lie in a fixed compact nonsingular set. -/
theorem exists_bounded_analytic_quadratic_chart {n : ℕ} {K : Set (Matrix (Fin n) (Fin n) ℂ)}
    (hK : IsCompact K) (hKdet : ∀ H ∈ K, H.det ≠ 0) {r : ℝ} (hr : 0 < r) (M : ℝ) :
    ∃ R A : ℝ, 0 < R ∧ R ≤ r ∧ 0 ≤ A ∧
      ∀ (B : (Fin n → ℂ) → Matrix (Fin n) (Fin n) ℂ),
        AnalyticOnNhd ℂ B (Metric.ball 0 r) → (∀ x ∈ Metric.ball 0 r, ‖B x‖ ≤ M) →
        B 0 ∈ K → (∀ x ∈ Metric.ball 0 r, (B x).IsSymm) →
        ∃ f : (Fin n → ℂ) → (Fin n → ℂ), AnalyticOnNhd ℂ f (Metric.ball 0 R) ∧
          (∀ x ∈ Metric.ball 0 R, ‖f x‖ ≤ A) ∧ f 0 = 0 ∧
          fderiv ℂ f 0 = ContinuousLinearMap.id ℂ _ ∧
          ∀ x ∈ Metric.ball 0 R, (B x).toBilin' x x = (B 0).toBilin' (f x) (f x) := by
  let E := Fin n → ℂ
  let Mat := Matrix (Fin n) (Fin n) ℂ
  obtain ⟨T, hT⟩ := hK.bddAbove_image (f := fun H ↦ ‖(H : Mat)⁻¹‖)
    (fun H hH ↦ (continuous_id.continuousAt.matrix_inv (hKdet H hH)).norm.continuousWithinAt)
  obtain ⟨C, -, hC⟩ := exists_norm_iteratedFDeriv_le_of_analyticOnNhd_ball
    (E := E) (F := Mat) 1 (c := 0) (show r / 2 < r by linarith)
  let D := max 1 T * max 1 (C * M)
  have hD : 0 < D := mul_pos (zero_lt_one.trans_le (le_max_left ..))
    (zero_lt_one.trans_le (le_max_left ..))
  have hfun : ∀ᶠ z in 𝓝 (1 : Mat), ‖sqrtNearOne Mat z‖ < ‖(1 : Mat)‖ + 1 := by
    apply continuousAt_sqrtNearOne.norm.eventually_lt continuousAt_const
    simp
  obtain ⟨ε, hε, hεB⟩ := Metric.mem_nhds_iff.1 hfun
  let R := min (r / 2) (min 1 ε / D)
  have hR : 0 < R := lt_min (by positivity) (div_pos (lt_min one_pos hε) hD)
  have hRr : R ≤ r := (min_le_left ..).trans (by linarith)
  have hsub : Metric.ball (0 : E) R ⊆ Metric.ball 0 r := Metric.ball_subset_ball hRr
  refine ⟨R, (‖(1 : Mat)‖ + 1) * R, hR, hRr, by positivity, fun B hB hb hK₀ hsym ↦ ?_⟩
  let H := B 0
  have hunit := isUnit_iff_ne_zero.mpr (hKdet H hK₀)
  let Z := fun x ↦ H⁻¹ * B x
  have hZ (x : E) (hx : x ∈ Metric.ball 0 R) : ‖Z x - 1‖ < min 1 ε := by
    have hz : Z x - 1 = H⁻¹ * (B x - B 0) := by
      rw [Matrix.mul_sub, H.nonsing_inv_mul hunit]
    have hBdiff : ‖B x - B 0‖ ≤ max 1 (C * M) * ‖x‖ := by
      simpa only [sub_zero] using (convex_ball (0 : E) R).norm_image_sub_le_of_norm_fderiv_le
        (fun y hy ↦ (hB y (hsub hy)).differentiableAt)
        (fun y hy ↦ by
          rw [← norm_iteratedFDeriv_one (𝕜 := ℂ)]
          exact (hC B M hB hb y
            (Metric.ball_subset_closedBall (Metric.ball_subset_ball (min_le_left ..) hy))).trans
              (le_max_right ..)) (Metric.mem_ball_self hR) hx
    rw [hz]
    calc
      _ ≤ ‖H⁻¹‖ * ‖B x - B 0‖ := norm_mul_le ..
      _ ≤ max 1 T * (max 1 (C * M) * ‖x‖) := by
        gcongr
        exact (hT (mem_image_of_mem (fun H : Mat ↦ ‖H⁻¹‖) hK₀)).trans (le_max_right ..)
      _ = D * ‖x‖ := by dsimp only [D]; ring
      _ < _ := by
        have hlt := (mem_ball_zero_iff.1 hx).trans_le (min_le_right ..)
        simpa only [mul_comm D] using (lt_div_iff₀ hD).1 hlt
  let Q := fun x ↦ sqrtNearOne Mat (Z x)
  have hQ : AnalyticOnNhd ℂ Q (Metric.ball 0 R) := fun x hx ↦
    (analyticOnNhd_complex_sqrtNearOne _ (by
      rw [Metric.mem_ball, dist_eq_norm]
      exact (hZ x hx).trans_le (min_le_left ..))).comp
        (analyticAt_const.mul (hB x (hsub hx)))
  have hQ0 : Q 0 = 1 := by simp [Q, Z, show H⁻¹ * B 0 = 1 from H.nonsing_inv_mul hunit]
  let Aop := ((Matrix.toLin' (R := ℂ) (m := Fin n) (n := Fin n)).trans
    (LinearMap.toContinuousLinearMap (𝕜 := ℂ) (E := E) (F' := E))).toContinuousLinearEquiv
  let f (x : E) := Aop (Q x) x
  have hF : AnalyticOnNhd ℂ f (Metric.ball 0 R) :=
    (show DifferentiableOn ℂ f (Metric.ball 0 R) from fun x hx ↦
      ((Aop.toContinuousLinearMap.differentiableAt.comp x (hQ x hx).differentiableAt).clm_apply
        differentiableAt_id).differentiableWithinAt).analyticOnNhd_of_finiteDimensional
        Metric.isOpen_ball
  have ha (x : E) : f x = (Q x).toLin' x := rfl
  refine ⟨f, hF, ?_, by simp [f], ?_, ?_⟩
  · intro x hx
    have hmem : Z x ∈ Metric.ball 1 ε := by
      rw [Metric.mem_ball, dist_eq_norm]
      exact (hZ x hx).trans_le (min_le_right ..)
    rw [ha, Matrix.toLin'_apply']
    exact (linfty_opNorm_mulVec _ _).trans
      (mul_le_mul (hεB hmem).le (mem_ball_zero_iff.1 hx).le
        (norm_nonneg _) (by positivity))
  · have h := (Aop.toContinuousLinearMap.differentiableAt.comp 0
      (hQ 0 (Metric.mem_ball_self hR)).differentiableAt).hasFDerivAt.clm_apply
        (hasFDerivAt_id (𝕜 := ℂ) (0 : E))
    have he := h.fderiv
    change fderiv ℂ f 0 = _ at he
    rw [he]
    ext x i
    simp only [ContinuousLinearMap.comp_apply, id_eq, map_zero, add_zero,
      Function.comp_apply, hQ0]
    change (Matrix.toLin' (1 : Mat) x) i = x i
    change ((1 : Mat) *ᵥ x) i = x i
    rw [Matrix.one_mulVec]
  · intro x hx
    have hcon := sqrtNearOne_matrix_congr (hsym 0 (Metric.mem_ball_self hr)) hunit
      (hsym x (hsub hx)) ((hZ x hx).trans_le (min_le_left ..))
    rw [ha, ← LinearMap.BilinForm.comp_apply, Matrix.toBilin'_comp, hcon]

/-- A nonsingular complex symmetric form is a sum of squares in suitable coordinates.
The modulus of its determinant is the real Jacobian of the change of coordinates. -/
theorem exists_complex_quadratic_normalization {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ}
    (hH : H.IsSymm) (hdet : H.det ≠ 0) :
    ∃ L : (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ),
      (∀ x, H.toBilin' x x = ∑ i, (L x i) ^ 2) ∧
      LinearMap.det (L.toLinearMap.restrictScalars ℝ) = ‖H.det‖ := by
  let B := H.toBilin'
  have hb : B.IsSymm := Matrix.isSymm_toBilin'_iff_isSymm.mpr hH
  have hd : B.Nondegenerate := BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mpr hdet
  let D := (1 : Matrix (Fin n) (Fin n) ℂ).toBilin'
  have hds : D.IsSymm := Matrix.isSymm_toBilin'_iff_isSymm.mpr (by simp)
  have hdd : D.Nondegenerate := BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mpr (by simp)
  have halt {Q : LinearMap.BilinForm ℂ (Fin n → ℂ)} (hq : Q.IsSymm) :
      Q.IsAlt → Q = 0 :=
    TauCeti.BilinForm.eq_zero_of_isSymm_of_isAlt
      (fun _ _ h ↦ mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) h) hq
  obtain ⟨e⟩ := hb.equivalent_of_finrank_eq IsAlgClosed.isSquare hd (halt hb)
    hds hdd (halt hds) rfl
  let L := e.toLinearEquiv
  have hcomp : D.comp
      L.toLinearMap L.toLinearMap = B := by
    exact LinearMap.ext₂ fun x y ↦ e.map_app' x y
  refine ⟨L, fun x ↦ ?_, ?_⟩
  · change B x x = _
    rw [← hcomp]
    simp [D, Matrix.toBilin'_apply', dotProduct, pow_two]
  · have h := BilinForm.det_toMatrix_comp (Pi.basisFun ℂ (Fin n)) (Pi.basisFun ℂ (Fin n))
      D L.toLinearMap
    rw [hcomp] at h
    have hh : ((BilinForm.toMatrix (Pi.basisFun ℂ (Fin n))) B) = H := by
      rw [BilinForm.toMatrix_basisFun, show B = H.toBilin' by rfl, BilinForm.toMatrix'_toBilin']
    have hD : ((BilinForm.toMatrix (Pi.basisFun ℂ (Fin n))) D) = 1 := by
      rw [BilinForm.toMatrix_basisFun,
        show D = (1 : Matrix (Fin n) (Fin n) ℂ).toBilin' by rfl, BilinForm.toMatrix'_toBilin']
    rw [hh, hD, Matrix.det_one, mul_one, LinearMap.det_toMatrix] at h
    rw [LinearMap.det_restrictScalars_eq_normSq, Complex.normSq_eq_norm_sq]
    simpa only [norm_pow] using (congrArg norm h).symm

open scoped Matrix.Norms.Operator in
private theorem eventually_complex_symmetric_congr {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsSymm) (hdet : IsUnit A.det) :
    ∃ R : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ,
      ContinuousAt R A ∧ R A = 1 ∧
        ∀ᶠ H in 𝓝 A, H.IsSymm → (R H)ᵀ * A * R H = H := by
  let adj : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ := fun R ↦ A⁻¹ * Rᵀ * A
  have hadj : Continuous adj :=
    (continuous_const.mul continuous_id.matrix_transpose).mul continuous_const
  have hadj_mul (R S : Matrix (Fin n) (Fin n) ℂ) : adj (R * S) = adj S * adj R := by
    simp only [adj, transpose_mul, Matrix.mul_assoc, A.mul_nonsing_inv_cancel_left _ hdet]
  have hadj_C {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsSymm) :
      adj (A⁻¹ * H) = A⁻¹ * H := by
    simp only [adj, transpose_mul, transpose_nonsing_inv, hA.eq, hH.eq]
    simp [Matrix.mul_assoc, A.nonsing_inv_mul hdet]
  let C : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ := fun H ↦ A⁻¹ * H
  have hC : Continuous C := continuous_const.mul continuous_id
  have hC₁ : C A = 1 := A.nonsing_inv_mul hdet
  let R := sqrtNearOne (Matrix (Fin n) (Fin n) ℂ) ∘ C
  have hca : Tendsto C (𝓝 A) (𝓝 1) := hC₁ ▸ hC.tendsto A
  refine ⟨R, continuousAt_sqrtNearOne.comp_of_eq hC.continuousAt hC₁,
    by simp [R, hC₁, sqrtNearOne_one], ?_⟩
  filter_upwards [hca.eventually eventually_mul_self_sqrtNearOne,
    hca.eventually (eventually_sqrtNearOne_fixed hadj.continuousAt hadj_mul)] with H hsq hfixed
  intro hH
  have hs : adj (R H) = R H := hfixed (hadj_C hH)
  have hAR : (R H)ᵀ * A = A * R H := by
    have h := congrArg (fun S ↦ A * S) hs
    simpa only [adj, ← Matrix.mul_assoc, A.mul_nonsing_inv hdet, Matrix.one_mul] using h
  rw [hAR, Matrix.mul_assoc, show R H * R H = A⁻¹ * H from hsq,
    A.mul_nonsing_inv_cancel_left H hdet]

private theorem eventually_exists_bounded_complex_quadratic_normalization
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsSymm) (hdet : A.det ≠ 0) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ H in 𝓝 A, H.IsSymm →
      ∃ L : (Fin n → ℂ) ≃L[ℂ] (Fin n → ℂ),
        ‖L.toContinuousLinearMap‖ ≤ M ∧ ‖L.symm.toContinuousLinearMap‖ ≤ M ∧
        (∀ x, H.toBilin' x x = ∑ i, (L x i) ^ 2) ∧
        LinearMap.det (L.toLinearEquiv.toLinearMap.restrictScalars ℝ) = ‖H.det‖ := by
  obtain ⟨L₀, hL₀, hdet₀⟩ := exists_complex_quadratic_normalization hA hdet
  obtain ⟨R, hR, hR₁, hcongr⟩ := eventually_complex_symmetric_congr hA (isUnit_iff_ne_zero.mpr hdet)
  let toCLM := (Matrix.toLin' (R := ℂ) (m := Fin n) (n := Fin n)).trans
    (LinearMap.toContinuousLinearMap (𝕜 := ℂ) (E := Fin n → ℂ) (F' := Fin n → ℂ))
  have hc : Continuous toCLM := toCLM.toLinearMap.continuous_of_finiteDimensional
  have hbd : ∀ᶠ B in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), ‖toCLM B‖ < ‖toCLM 1‖ + 1 :=
    hc.continuousAt.norm.eventually_lt (continuousAt_const (x := (1 : Matrix (Fin n) (Fin n) ℂ)))
      (by linarith)
  have hRinv : ContinuousAt (fun H ↦ (R H)⁻¹) A :=
    hR.matrix_inv (by rw [hR₁, Matrix.det_one]; exact one_ne_zero)
  have ht : Tendsto R (𝓝 A) (𝓝 1) := hR₁ ▸ hR
  have hti : Tendsto (fun H ↦ (R H)⁻¹) (𝓝 A) (𝓝 1) := by
    change Tendsto (fun H ↦ (R H)⁻¹) (𝓝 A) (𝓝 ((R A)⁻¹)) at hRinv
    simpa only [hR₁, inv_one] using hRinv
  have hu : ∀ᶠ H in 𝓝 A, IsUnit (R H).det := by
    refine ht.eventually (p := fun B ↦ IsUnit (Matrix.det B)) ?_
    have hd : ContinuousAt (fun B : Matrix (Fin n) (Fin n) ℂ ↦ B.det) 1 :=
      continuous_id.matrix_det.continuousAt
    filter_upwards [hd.eventually_ne (by simp : Matrix.det (1 : Matrix (Fin n) (Fin n) ℂ) ≠ 0)]
      with B hB using isUnit_iff_ne_zero.mpr hB
  let e₀ := L₀.toContinuousLinearEquiv
  let M := max ‖e₀.toContinuousLinearMap‖ ‖e₀.symm.toContinuousLinearMap‖ * (‖toCLM 1‖ + 1)
  refine ⟨M, mul_nonneg ((norm_nonneg _).trans (le_max_left ..)) (by positivity), ?_⟩
  filter_upwards [hcongr, ht.eventually hbd, hti.eventually hbd, hu] with H hcon hb hbi hu
  intro hH
  let e := ((R H).toLinearEquiv (Pi.basisFun ℂ (Fin n)) hu).toContinuousLinearEquiv
  let L := e.trans e₀
  have he : e.toContinuousLinearMap = toCLM (R H) := by
    apply ContinuousLinearMap.ext
    intro x
    exact (R H).toLinearEquiv_basisFun_apply hu x
  have hei : e.symm.toContinuousLinearMap = toCLM (R H)⁻¹ := by
    apply ContinuousLinearMap.ext
    intro x
    exact (R H).toLinearEquiv_basisFun_symm_apply hu x
  refine ⟨L, ?_, ?_, ?_, ?_⟩
  · refine (ContinuousLinearMap.opNorm_comp_le e₀.toContinuousLinearMap
      e.toContinuousLinearMap).trans ?_
    rw [he]
    exact mul_le_mul (le_max_left ..) hb.le (norm_nonneg _)
      ((norm_nonneg _).trans (le_max_left ..))
  · refine (ContinuousLinearMap.opNorm_comp_le e.symm.toContinuousLinearMap
      e₀.symm.toContinuousLinearMap).trans ?_
    rw [hei, mul_comm]
    exact mul_le_mul (le_max_right ..) hbi.le (norm_nonneg _)
      ((norm_nonneg _).trans (le_max_right ..))
  · intro x
    have hbil : A.toBilin'.comp (R H).toLin' (R H).toLin' = H.toBilin' := by
      rw [Matrix.toBilin'_comp, hcon hH]
    rw [← hbil]
    change A.toBilin' ((R H).toLin' x) ((R H).toLin' x) = ∑ i, (L x i) ^ 2
    rw [hL₀]
    rfl
  · have hedet : LinearMap.det e.toLinearEquiv.toLinearMap = (R H).det := by
      rw [← LinearMap.det_toMatrix' e.toLinearEquiv.toLinearMap]
      exact congrArg Matrix.det (LinearMap.toMatrix'_toLin' _)
    have hcomp :
        L.toLinearEquiv.toLinearMap.restrictScalars ℝ =
          (L₀.toLinearMap.restrictScalars ℝ).comp (e.toLinearEquiv.toLinearMap.restrictScalars ℝ) :=
      rfl
    have hd := congrArg (fun B : Matrix (Fin n) (Fin n) ℂ ↦ ‖B.det‖) (hcon hH)
    simp only [Matrix.det_mul, Matrix.det_transpose, norm_mul] at hd
    rw [hcomp, LinearMap.det_comp, hdet₀, LinearMap.det_restrictScalars_eq_normSq,
      hedet, Complex.normSq_eq_norm_sq, ← hd]
    ring

/-- On a compact family of nonsingular complex symmetric forms, the coordinates and their
inverses can be chosen with uniformly bounded norms. -/
theorem exists_bounded_complex_quadratic_normalization {n : ℕ}
    {K : Set (Matrix (Fin n) (Fin n) ℂ)} (hK : IsCompact K)
    (hKs : ∀ H ∈ K, H.IsSymm) (hKd : ∀ H ∈ K, H.det ≠ 0) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ H ∈ K, ∃ L : (Fin n → ℂ) ≃L[ℂ] (Fin n → ℂ),
      ‖L.toContinuousLinearMap‖ ≤ M ∧ ‖L.symm.toContinuousLinearMap‖ ≤ M ∧
      (∀ x, H.toBilin' x x = ∑ i, (L x i) ^ 2) ∧
      LinearMap.det (L.toLinearEquiv.toLinearMap.restrictScalars ℝ) = ‖H.det‖ := by
  classical
  choose M hM hloc using fun H hH ↦
    eventually_exists_bounded_complex_quadratic_normalization (hKs H hH) (hKd H hH)
  obtain ⟨T, hT⟩ := hK.elim_nhds_subcover' _ hloc
  refine ⟨∑ H ∈ T, M H H.property, Finset.sum_nonneg fun H _ ↦ hM H H.property, ?_⟩
  intro H hH
  obtain ⟨A, hAT, hAH⟩ := mem_iUnion₂.1 (hT hH)
  obtain ⟨L, hL, hLi, hq, hj⟩ := hAH (hKs H hH)
  have hle := Finset.single_le_sum (f := fun B : K ↦ M B B.property)
    (fun B _ ↦ hM B B.property) hAT
  exact ⟨L, hL.trans hle, hLi.trans hle, hq, hj⟩

end TauCeti
