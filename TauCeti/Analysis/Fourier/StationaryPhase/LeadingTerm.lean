/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.StationaryPhase.Basic
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Fourier.StationaryPhase.AwayFromCritical
import TauCeti.Analysis.Fourier.StationaryPhase.ComplexQuadratic
import TauCeti.Analysis.Fourier.StationaryPhase.HolomorphicChart
import TauCeti.Analysis.Fourier.StationaryPhase.HolomorphicCoordinates
import TauCeti.Analysis.Fourier.StationaryPhase.QuadraticIntegral
import TauCeti.Analysis.Fourier.StationaryPhase.Transport

/-! # Stationary phase for holomorphic phases -/

public section

open Complex MeasureTheory Metric Set
open scoped ContDiff Matrix.Norms.Operator

namespace TauCeti

universe u

private noncomputable def oscillatoryKernel (s : ℝ) (y : ℝ) := exp (I * ((y / s : ℝ) : ℂ))

private theorem oscillatoryKernel_add (s y z : ℝ) :
    oscillatoryKernel s (y + z) = oscillatoryKernel s y * oscillatoryKernel s z := by
  simp only [oscillatoryKernel, add_div, ofReal_add, mul_add, exp_add]

private theorem hessian_norm_lower {n : ℕ} {d : ℝ}
    {H : Matrix (Fin n) (Fin n) ℂ} (hne : H.det ≠ 0) (hi : ‖H.det⁻¹‖ ≤ d) :
    d⁻¹ ≤ ‖H.det‖ := by
  rw [norm_inv] at hi
  simpa only [inv_inv] using inv_anti₀ (inv_pos.mpr (norm_pos_iff.mpr hne)) hi

private theorem exists_amplitude_decomposition {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (N : ℕ) {r ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ / 32 ≤ r) :
    ∃ J : ℝ, 0 ≤ J ∧ ∀ (V : Type u) [NormedAddCommGroup V] [NormedSpace ℝ V]
      (a : E → V) (S : ℝ), ContDiff ℝ N a →
      (∀ x ∉ closedBall 0 r, a x = 0) →
      (∀ j ≤ N, ∀ x, ‖iteratedFDeriv ℝ j a x‖ ≤ S) →
      ∃ a₀ a₁ : E → V, a = a₀ + a₁ ∧ a₀ 0 = a 0 ∧
        ContDiff ℝ N a₀ ∧ ContDiff ℝ N a₁ ∧
        (∀ x ∉ closedBall 0 (ρ / 32), a₀ x = 0) ∧
        (∀ x ∉ closedBall 0 r \ ball 0 (ρ / 64), a₁ x = 0) ∧
        (∀ j ≤ N, ∀ x, ‖iteratedFDeriv ℝ j a₀ x‖ ≤ J * S) ∧
        (∀ j ≤ N, ∀ x, ‖iteratedFDeriv ℝ j a₁ x‖ ≤ (1 + J) * S) := by
  obtain ⟨χ, U, hU, hχ, hχs, hχ1, hχb⟩ := exists_bounded_smooth_cutoff (E := E)
    N (show ρ / 64 < ρ / 32 by linarith)
  let J := 2 ^ N * U
  refine ⟨J, by positivity, fun V _ _ a S ha has hab ↦ ?_⟩
  let a₀ (x : E) := χ x • a x
  let a₁ := a - a₀
  have hχN : ContDiff ℝ N χ := hχ.of_le (by simp)
  have ha₀ : ContDiff ℝ N a₀ := hχN.smul ha
  have ha₀s (x : E) (hx : x ∉ closedBall 0 (ρ / 32)) : a₀ x = 0 := by
    have hχx : χ x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h ↦ hx (ball_subset_closedBall (hχs h)))
    simp [a₀, hχx]
  have ha₀b (j : ℕ) (hj : j ≤ N) (x : E) : ‖iteratedFDeriv ℝ j a₀ x‖ ≤ J * S :=
    norm_iteratedFDeriv_smul_le_of_uniform_bounds isOpen_univ (mem_univ x)
      hχN.contDiffOn ha.contDiffOn (fun i hi ↦ hχb i hi x) (fun i hi ↦ hab i hi x) j hj
  refine ⟨a₀, a₁, by simp [a₁], ?_, ha₀, ha.sub ha₀, ha₀s, ?_, ha₀b, ?_⟩
  · have hχ0 := (hχ1 0 (mem_closedBall_self (by positivity))).eq_of_nhds
    simp [a₀, hχ0]
  · intro x hx
    by_cases hxr : x ∈ closedBall 0 r
    · have hxb : x ∈ ball 0 (ρ / 64) := by
        by_contra h
        exact hx ⟨hxr, h⟩
      have hχx := (hχ1 x (ball_subset_closedBall hxb)).eq_of_nhds
      simp [a₁, a₀, hχx]
    · have ha₀x := ha₀s x (fun h ↦ hxr (closedBall_subset_closedBall hρr h))
      rw [show a₁ x = a x - a₀ x from rfl, has x hxr, ha₀x, sub_zero]
  · intro j hj x
    dsimp [a₁]
    rw [iteratedFDeriv_sub (ha.of_le (by exact_mod_cast hj))
      (ha₀.of_le (by exact_mod_cast hj))]
    exact (norm_sub_le _ _).trans ((add_le_add (hab j hj x) (ha₀b j hj x)).trans_eq (by ring))

private theorem integrable_smul_of_eqOn_compact {E V : Type*}
    [TopologicalSpace E] [R1Space E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [IsFiniteMeasureOnCompacts μ]
    [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] {K : Set E} (hK : IsCompact K)
    {p p' : E → ℂ} (hp' : Continuous p') (hp : EqOn p p' K) {a : E → V} (ha : Continuous a)
    (has : ∀ x ∉ K, a x = 0) : Integrable (fun x ↦ p x • a x) μ := by
  have h : (fun x ↦ p x • a x) = fun x ↦ p' x • a x := by
    funext x
    by_cases hx : x ∈ K
    · rw [hp hx]
    · simp [has x hx]
  rw [h]
  refine (hp'.smul ha).integrable_of_hasCompactSupport ?_
  apply HasCompactSupport.of_support_subset_isCompact hK
  intro x hx
  exact by_contra fun h ↦ hx (by simp [has x h])

private theorem exists_imaginary_phase_extension (n N : ℕ) {r Λ d : ℝ}
    (hr : 0 < r) (hΛ : 0 < Λ) :
    ∃ P : ℝ, ∀ g : (Fin n → ℂ) → ℂ,
      AnalyticOnNhd ℂ g (ball 0 (2 * r)) →
      (∀ x ∈ ball 0 (2 * r), ‖g x‖ ≤ Λ) →
      (∀ x ∈ closedBall 0 r, ‖x‖ ≤ Λ * ‖fun k : Fin n ↦ fderiv ℂ g x (Pi.single k 1)‖) →
      ∃ φ : (Fin n → ℂ) → ℝ, ContDiff ℝ (N + 1 : ℕ) φ ∧
        EqOn φ (fun x ↦ (g x).im) (closedBall 0 r) ∧
        (∀ j ≤ N, ∀ x, ‖iteratedFDeriv ℝ (j + 1) φ x‖ ≤ P) ∧
        ∀ x ∈ closedBall 0 r \ ball 0 d, d / (2 * Λ) ≤ ‖fderiv ℝ φ x‖ := by
  let E := Fin n → ℂ
  obtain ⟨P, -, hext⟩ := exists_contDiff_extension_of_analyticOnNhd_ball (E := E) (F := ℂ)
    (N + 1) (show r < 2 * r by linarith) Λ
  refine ⟨P, fun g hg hgb hgrad ↦ ?_⟩
  obtain ⟨g', hg', hg'eq, hg'b⟩ := hext g hg hgb
  let φ := imCLM ∘ g'
  refine ⟨φ, imCLM.contDiff.comp hg', fun x hx ↦ ?_, ?_, ?_⟩
  · exact congrArg im (hg'eq x hx).eq_of_nhds
  · intro j hj x
    refine (imCLM.norm_iteratedFDeriv_comp_left hg'.contDiffAt
      (by exact_mod_cast Nat.succ_le_succ hj)).trans ?_
    rw [imCLM_norm, one_mul]
    exact hg'b _ (Nat.succ_le_succ hj) x
  · intro x hx
    have hxg := closedBall_subset_ball (show r < 2 * r by linarith) hx.1
    have hgl := norm_le_mul_norm_fderiv_re_of_norm_le_gradient (x₀ := 0)
      (c := -I) (neg_ne_zero.mpr I_ne_zero) (hg x hxg).differentiableAt hΛ.le
      (by simpa only [sub_zero] using hgrad x hx.1)
    have heq : φ =ᶠ[nhds x] fun y ↦ (-I * g y).re := by
      filter_upwards [hg'eq x hx.1] with y hy
      change g' y = g y at hy
      simp [φ, hy, neg_mul]
    rw [← heq.fderiv_eq, sub_zero, norm_neg, norm_I, div_one] at hgl
    have hdist : d ≤ ‖x‖ := by simpa only [mem_ball, dist_zero_right, not_lt] using hx.2
    exact (div_le_iff₀ (by positivity : 0 < 2 * Λ)).2
      (by simpa only [mul_comm (2 * Λ)] using hdist.trans hgl)

private theorem norm_sub_le_of_det_smul {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {J : ℝ} (hJ : 0 < J) {D S B : ℝ} {x y : V} (hD : J⁻¹ ≤ D) (hS : 0 ≤ S)
    (h : ‖J • x - B • y‖ ≤ S) : ‖x - (B / J) • y‖ ≤ D * S := by
  have hmul : J • (x - (B / J) • y) = J • x - B • y := by
    rw [smul_sub, smul_smul, mul_div_cancel₀ _ hJ.ne']
  rw [← hmul, norm_smul, Real.norm_of_nonneg hJ.le] at h
  have hh := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hJ.le)
  rw [← mul_assoc, inv_mul_cancel₀ hJ.ne', one_mul] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right hD hS)

private theorem exists_norm_integral_stationaryPhase_centered (n : ℕ) (hn : 1 ≤ n)
    {r Λ : ℝ} (hr : 0 < r) (hΛ : 0 < Λ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : (Fin n → ℂ) → ℂ,
      DifferentiableOn ℂ g (ball 0 (2 * r)) →
      (∀ x ∈ ball 0 (2 * r), ‖g x‖ ≤ Λ) → fderiv ℂ g 0 = 0 →
      (∀ x ∈ closedBall 0 r, ‖x‖ ≤ Λ * ‖fun k : Fin n ↦ fderiv ℂ g x (Pi.single k 1)‖) →
      ∀ (V : Type u) [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
        (a : (Fin n → ℂ) → V) (S : ℝ), ContDiff ℝ (2 * n + 2 : ℕ) a →
        (∀ x ∉ closedBall 0 r, a x = 0) →
        (∀ j ≤ 2 * n + 2, ∀ x, ‖iteratedFDeriv ℝ j a x‖ ≤ S) →
        let H := Matrix.of fun i j : Fin n ↦
          iteratedFDeriv ℂ 2 g 0 ![Pi.single i 1, Pi.single j 1]
        H.det ≠ 0 ∧ ∀ s : ℝ, s ≠ 0 →
          ‖(∫ x, oscillatoryKernel s (g x).im • a x) -
            oscillatoryKernel s (g 0).im •
              (((2 * Real.pi * |s|) ^ n / ‖H.det‖ : ℝ) • a 0)‖ ≤
            C * S * |s| ^ (n + 1) := by
  let E := Fin n → ℂ
  let : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  let Mat := Matrix (Fin n) (Fin n) ℂ
  let N := n + 3
  have hN : N ≤ 2 * n + 2 := by dsimp [N]; omega
  let d : ℝ := n.factorial * Λ ^ n
  have hd : 0 < d := by positivity
  obtain ⟨M, -, hm⟩ := exists_bounded_analytic_taylor_matrix n hr Λ
  let K : Set Mat := closedBall 0 M ∩ {H | d⁻¹ ≤ ‖H.det‖} ∩ {H | H.IsSymm}
  have hK : IsCompact K := by
    apply IsCompact.inter_right
    · exact (isCompact_closedBall _ _).inter_right
        (isClosed_le continuous_const (continuous_id.matrix_det.norm))
    · exact isClosed_eq continuous_id.matrix_transpose continuous_id
  have hKs : ∀ H ∈ K, Matrix.IsSymm H := fun _ h ↦ h.2
  have hKd : ∀ H ∈ K, Matrix.det H ≠ 0 := fun H h ↦
    norm_pos_iff.mp ((inv_pos.mpr hd).trans_le h.1.2)
  obtain ⟨A, -, hq⟩ := exists_bounded_complex_quadratic_normalization hK hKs hKd
  obtain ⟨R, B, hR, hRr, -, hqchart⟩ := exists_bounded_analytic_quadratic_chart hK hKd hr M
  obtain ⟨ρ, hρ, hρR, hinvchart⟩ := exists_bounded_analytic_inverse_chart (E := E) hR B
  have hρr : ρ < r := hρR.trans_le hRr
  have hsubr : ρ / 32 ≤ r := by linarith [hρr]
  obtain ⟨T, hT, htransport⟩ := exists_bounded_transported_amplitude.{u} n N hρ
  obtain ⟨Q, hQ⟩ := exists_norm_integral_sum_sq_sub_le.{u} n (ρ / 8) A
  obtain ⟨J, hJ, hcut⟩ := exists_amplitude_decomposition.{u} (E := E) (2 * n + 2) hρ hsubr
  let F := closedBall (0 : E) r \ ball 0 (ρ / 64)
  have hF : IsCompact F := (isCompact_closedBall _ _).diff isOpen_ball
  let δ := (ρ / 64) / (2 * Λ)
  have hδ : 0 < δ := by positivity
  obtain ⟨P, hext⟩ := exists_imaginary_phase_extension n (n + 1) (d := ρ / 64) hr hΛ
  obtain ⟨W, hW, haway⟩ :=
    exists_norm_integral_oscillation_le_of_fderiv_lower.{u} (ν := volume) F hF (n + 1) hδ P
  refine ⟨max 0 Q * T * J * d + W * (1 + J), by positivity, ?_⟩
  intro g hg hgb hcrit hgrad V _ _ _ a S ha has hab H
  have hS : 0 ≤ S := (norm_nonneg _).trans (hab 0 (Nat.zero_le _) 0)
  have hgan : AnalyticOnNhd ℂ g (ball 0 (2 * r)) :=
    hg.analyticOnNhd_of_finiteDimensional isOpen_ball
  obtain ⟨hHd, hHi⟩ := det_hessian_ne_zero_and_norm_inv_le_of_norm_le_gradient hr hg hcrit
    (fun x hx ↦ by simpa only [sub_zero] using hgrad x hx)
  have hHlower : d⁻¹ ≤ ‖H.det‖ := hessian_norm_lower hHd hHi
  obtain ⟨D, hD, hDb, hD0, hDs, hDt⟩ := hm g hgan hgb
  have h0r : (0 : E) ∈ ball 0 r := mem_ball_self hr
  have hDK : D 0 ∈ K :=
    ⟨⟨by simpa only [mem_closedBall, dist_zero_right] using hDb 0 h0r,
      by rw [hD0]; exact hHlower⟩, hDs 0 h0r⟩
  change D 0 = H at hD0
  have hHK : H ∈ K := hD0 ▸ hDK
  obtain ⟨L, hL, hLi, hLq, hLj⟩ := hq H hHK
  obtain ⟨f, hf, hfb, hf0, hfder, hfeq⟩ := hqchart D hD hDb hDK hDs
  obtain ⟨e, he, hes, het, hean, heb, hen, heder⟩ := hinvchart f hf hfb hf0 hfder
  have hphase (x : E) (hx : x ∈ ball 0 ρ) :
      g x = g 0 + (2⁻¹ : ℂ) * ∑ i, (L (e x) i) ^ 2 := by
    have hxR := ball_subset_ball hρR.le hx
    rw [hDt x (ball_subset_ball hRr hxR), hcrit, zero_apply, add_zero,
      hfeq x hxR, hD0, hLq, he]
  obtain ⟨a₀, a₁, haeq, ha₀0, ha₀, ha₁, ha₀s, ha₁s, ha₀b, ha₁b⟩ :=
    hcut V a S ha has hab
  obtain ⟨b, hb, hb0, hbs, hbb, htr⟩ := htransport e hes het (by rw [he, hf0]) hean heb
    (by simpa only [he] using hen) heder V a₀ (J * S)
    (ha₀.of_le (by exact_mod_cast hN)) ha₀s (fun j hj ↦ ha₀b j (hj.trans hN))
  obtain ⟨φ, hφ, hφeq, hφb, hφlo⟩ := hext g hgan hgb hgrad
  refine ⟨hHd, fun s hs ↦ ?_⟩
  let p (x : E) := oscillatoryKernel s (g x).im
  let p' (x : E) := oscillatoryKernel s (φ x)
  let k := p 0
  let q (x : E) := exp (I * ((((-I / 2) * ∑ i, (L x i) ^ 2).re / s : ℝ) : ℂ))
  have hk : ‖k‖ = 1 := norm_exp_I_mul_ofReal _
  have hp (x : E) (hx : x ∈ closedBall 0 r) : p x = p' x := by
    exact congrArg (oscillatoryKernel s) (hφeq hx).symm
  have hqeq (x : E) (hx : x ∈ ball 0 ρ) : p x = k * q (e x) := by
    have hh (w : ℂ) : ((2⁻¹ : ℂ) * w).im = ((-I / 2) * w).re := by
      rw [show -I / 2 * w = -I * (2⁻¹ * w) by ring, neg_mul, neg_re, I_mul_re, neg_neg]
    unfold p
    rw [hphase x hx, add_im, oscillatoryKernel_add, hh]
    rfl
  have hi₀ : (∫ x, p x • a₀ x) = k • ∫ x, q x • b x := by
    rw [htr p (fun x ↦ k * q x) hqeq]
    simp only [mul_smul, integral_smul]
    rfl
  have he₁ : (fun x ↦ p x • a₁ x) = fun x ↦ p' x • a₁ x := by
    funext x
    by_cases hx : x ∈ closedBall 0 r
    · rw [hp x hx]
    · simp [ha₁s x (fun h ↦ hx h.1)]
  have hi₁ : ‖∫ x, p x • a₁ x‖ ≤ W * ((1 + J) * S) * |s| ^ (n + 1) := by
    rw [he₁]
    exact haway φ hφ hφlo (fun j hj x _ ↦ hφb j hj x) V a₁ ((1 + J) * S)
      (mul_nonneg (add_nonneg zero_le_one hJ) hS)
      (ha₁.of_le (by exact_mod_cast (show n + 1 ≤ 2 * n + 2 by omega))) ha₁s
      (fun j hj x _ ↦ ha₁b j (by omega) x) s hs
  have hp' : Continuous p' := by
    unfold p' oscillatoryKernel
    fun_prop
  have hfun (a' : E → V) (ha' : Continuous a') (hsa' : ∀ x ∉ closedBall 0 r, a' x = 0) :
      Integrable (fun x ↦ p x • a' x) :=
    integrable_smul_of_eqOn_compact (isCompact_closedBall _ _) hp' (fun x h ↦ hp x h) ha' hsa'
  have hsplit : (∫ x, p x • a x) = (∫ x, p x • a₀ x) + ∫ x, p x • a₁ x := by
    have heqa : (fun x ↦ p x • a x) = (fun x ↦ p x • a₀ x) + (fun x ↦ p x • a₁ x) := by
      funext x
      rw [congrFun haeq x]
      exact smul_add _ _ _
    rw [heqa]
    change (∫ x, p x • a₀ x + p x • a₁ x) = _
    rw [integral_add]
    · exact hfun a₀ ha₀.continuous fun x hx ↦ ha₀s x
        (fun h ↦ hx (closedBall_subset_closedBall hsubr h))
    · exact hfun a₁ ha₁.continuous fun x hx ↦ ha₁s x (fun h ↦ hx h.1)
  let lead := (((2 * Real.pi * |s|) ^ n / ‖H.det‖ : ℝ) • a 0)
  have hqerr' : ‖(∫ x, q x • b x) - lead‖ ≤
      max 0 Q * T * J * d * S * |s| ^ (n + 1) := by
    have h := hQ L hL hLi V b (T * (J * S)) hb hbs hbb s hs
    rw [hLj, hb0, ha₀0] at h
    have hbound : ‖H.det‖⁻¹ ≤ d := by simpa only [norm_inv] using hHi
    have h' := norm_sub_le_of_det_smul (norm_pos_iff.mpr hHd) hbound
      (show 0 ≤ max 0 Q * (T * (J * S)) * |s| ^ (n + 1) by positivity)
      (h.trans (by gcongr; exact le_max_right ..))
    exact h'.trans_eq (by ring)
  change ‖(∫ x, p x • a x) - k • lead‖ ≤ _
  rw [hsplit, hi₀, add_sub_right_comm, ← smul_sub]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, hk, one_mul]
  exact (add_le_add hqerr' hi₁).trans_eq (by ring)

private theorem norm_det_hessian_translate_smul {n : ℕ} {g : (Fin n → ℂ) → ℂ}
    {x₀ : Fin n → ℂ} (hg : ContDiffAt ℂ 2 g x₀) {c : ℂ} (hc : ‖c‖ = 1) :
    ‖(Matrix.of fun i j : Fin n ↦
      iteratedFDeriv ℂ 2 (c • fun x ↦ g (x₀ + x)) 0 ![Pi.single i 1, Pi.single j 1]).det‖ =
    ‖(Matrix.of fun i j : Fin n ↦
      iteratedFDeriv ℂ 2 g x₀ ![Pi.single i 1, Pi.single j 1]).det‖ := by
  let H := Matrix.of fun i j : Fin n ↦
    iteratedFDeriv ℂ 2 g x₀ ![Pi.single i 1, Pi.single j 1]
  have hg' : ContDiffAt ℂ 2 (fun x ↦ g (x₀ + x)) 0 := by
    apply ContDiffAt.comp 0 (f := fun x ↦ x₀ + x)
    · simpa only [add_zero] using hg
    · exact (contDiff_const.add contDiff_id).contDiffAt
  have hmat : (Matrix.of fun i j : Fin n ↦
      iteratedFDeriv ℂ 2 (c • fun x ↦ g (x₀ + x)) 0 ![Pi.single i 1, Pi.single j 1]) = c • H := by
    ext i j
    change iteratedFDeriv ℂ 2 (c • fun x ↦ g (x₀ + x)) 0 _ = c • iteratedFDeriv ℂ 2 g x₀ _
    rw [iteratedFDeriv_const_smul_apply hg', smul_apply, iteratedFDeriv_comp_add_left, add_zero]
  rw [hmat, Matrix.det_smul, Complex.norm_mul, norm_pow, hc, one_pow, one_mul]

private theorem norm_stationaryPhase_rescale {V : Type u} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (n : ℕ) {b τ : ℝ} (hb : 0 < b) (D C S : ℝ) (q : ℂ) (X Y : V)
    (h : ‖X - q • (((2 * Real.pi * (τ / b)) ^ n / D : ℝ) • Y)‖ ≤
      C * S * (τ / b) ^ (n + 1)) :
    ‖((b / (2 * Real.pi)) ^ n : ℝ) • X - (q * ((τ ^ n / D : ℝ) : ℂ)) • Y‖ ≤
      ((b / (2 * Real.pi)) ^ n * C / b ^ (n + 1)) * S * τ ^ (n + 1) := by
  let weight := (b / (2 * Real.pi)) ^ n
  have hw : 0 ≤ weight := by positivity
  have hscale : weight * (2 * Real.pi * (τ / b)) ^ n = τ ^ n := by
    dsimp [weight]
    rw [← mul_pow]
    congr 1
    field_simp [Real.pi_ne_zero, hb.ne']
  have hlead :
      weight • (q • (((2 * Real.pi * (τ / b)) ^ n / D : ℝ) • Y)) =
        (q * ((τ ^ n / D : ℝ) : ℂ)) • Y := by
    rw [smul_comm weight, smul_smul, ← mul_div_assoc, hscale, mul_smul]
    exact congrArg (fun v : V ↦ q • v) (RCLike.real_smul_eq_coe_smul (K := ℂ) (τ ^ n / D) Y)
  calc
    _ = weight * ‖X - q • (((2 * Real.pi * (τ / b)) ^ n / D : ℝ) • Y)‖ := by
      rw [← hlead, ← smul_sub, norm_smul, Real.norm_of_nonneg hw]
    _ ≤ weight * (C * S * (τ / b) ^ (n + 1)) := mul_le_mul_of_nonneg_left h hw
    _ = _ := by rw [div_pow]; ring

/-- The uniform leading term for a holomorphic phase with an isolated critical point.
The measure is Lebesgue measure on the complex coordinates, multiplied by
`(‖β‖ / (2 * Real.pi)) ^ n`. -/
theorem stationaryPhase_leadingTerm (n : ℕ) {β : ℂ} (hβ : β ≠ 0) {r Λ : ℝ} (hr : 0 < r)
    (hΛ : 0 < Λ) :
    ∃ C : ℝ, ∀ (x₀ : Fin n → ℂ) (g : (Fin n → ℂ) → ℂ),
      DifferentiableOn ℂ g (Metric.ball x₀ (2 * r)) →
      (∀ x ∈ Metric.ball x₀ (2 * r), ‖g x‖ ≤ Λ) →
      fderiv ℂ g x₀ = 0 →
      (∀ x ∈ Metric.closedBall x₀ r,
        ‖x - x₀‖ ≤ Λ * ‖fun k : Fin n ↦ fderiv ℂ g x (Pi.single k 1)‖) →
      ∀ (V : Type u) [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
        (a : (Fin n → ℂ) → V) (S : ℝ),
        ContDiff ℝ (2 * n + 2) a →
        (∀ x, x ∉ Metric.closedBall x₀ r → a x = 0) →
        (∀ j ≤ 2 * n + 2, ∀ x, ‖iteratedFDeriv ℝ j a x‖ ≤ S) →
        (Matrix.of fun i j : Fin n ↦
            iteratedFDeriv ℂ 2 g x₀ ![Pi.single i 1, Pi.single j 1]).det ≠ 0 ∧
        ∀ t : ℂ, t ≠ 0 →
          ‖((‖β‖ / (2 * Real.pi)) ^ n : ℝ) •
                (∫ x, Complex.exp (Complex.I * ((β * (g x / t)).re : ℂ)) • a x) -
              (Complex.exp (Complex.I * ((β * (g x₀ / t)).re : ℂ)) *
                ((‖t‖ ^ n / ‖(Matrix.of fun i j : Fin n ↦
                    iteratedFDeriv ℂ 2 g x₀ ![Pi.single i 1, Pi.single j 1]).det‖ : ℝ) : ℂ)) •
                a x₀‖ ≤ C * S * ‖t‖ ^ (n + 1) := by
  cases n with
  | zero =>
    refine ⟨0, fun x₀ g _ _ _ _ V _ _ _ a S _ _ _ ↦ ⟨by simp, fun t _ ↦ ?_⟩⟩
    rw [Measure.volume_pi_eq_dirac x₀, integral_dirac, Matrix.det_isEmpty]
    simp
  | succ m =>
    let n := m + 1
    let E := Fin n → ℂ
    obtain ⟨C, -, hc⟩ :=
      exists_norm_integral_stationaryPhase_centered.{u} n (by dsimp [n]; omega) hr hΛ
    let weight := (‖β‖ / (2 * Real.pi)) ^ n
    have hβp := norm_pos_iff.2 hβ
    refine ⟨weight * C / ‖β‖ ^ (n + 1), ?_⟩
    intro x₀ g hg hgb hcrit hgrad V _ _ _ a S ha has hab
    let H := Matrix.of fun i j : Fin n ↦
      iteratedFDeriv ℂ 2 g x₀ ![Pi.single i 1, Pi.single j 1]
    obtain ⟨hHd, -⟩ := det_hessian_ne_zero_and_norm_inv_le_of_norm_le_gradient hr hg hcrit hgrad
    refine ⟨hHd, fun t ht ↦ ?_⟩
    let s := ‖t‖ / ‖β‖
    have htpos := norm_pos_iff.2 ht
    have hs : 0 < s := div_pos htpos hβp
    let c := (I * β / t) * (s : ℂ)
    have hcn : ‖c‖ = 1 := by
      dsimp [c]
      rw [Complex.norm_mul, norm_div, Complex.norm_mul, norm_I, one_mul, norm_real,
        Real.norm_of_nonneg hs.le]
      dsimp [s]
      field_simp
    let tr (x : E) := x₀ + x
    let G : E → ℂ := c • (g ∘ tr)
    let a' := a ∘ tr
    have htr (x : E) : dist (tr x) x₀ = dist x 0 := by
      simp [tr, dist_eq_norm, add_comm x₀]
    have hgb' (x : E) (hx : x ∈ ball 0 (2 * r)) : tr x ∈ ball x₀ (2 * r) := by
      rwa [mem_ball, htr]
    have hgc : DifferentiableOn ℂ G (ball 0 (2 * r)) :=
      (hg.comp ((differentiable_const x₀).add differentiable_id).differentiableOn hgb').const_smul c
    have hder (x : E) : fderiv ℂ G x = c • fderiv ℂ g (tr x) := by
      rw [fderiv_const_smul_field]
      change c • fderiv ℂ (fun y ↦ g (x₀ + y)) x = _
      rw [fderiv_comp_add_left]
    have hG0 : fderiv ℂ G 0 = 0 := by
      rw [hder, show tr 0 = x₀ by simp [tr], hcrit]
      exact smul_zero (A := E →L[ℂ] ℂ) c
    have hGg (x : E) (hx : x ∈ closedBall 0 r) :
        ‖x‖ ≤ Λ * ‖fun k : Fin n ↦ fderiv ℂ G x (Pi.single k 1)‖ := by
      have hx' : tr x ∈ closedBall x₀ r := by rwa [mem_closedBall, htr]
      rw [hder]
      have hf : (fun k : Fin n ↦ (c • fderiv ℂ g (tr x)) (Pi.single k 1)) =
          c • (fun k : Fin n ↦ fderiv ℂ g (tr x) (Pi.single k 1)) := by
        ext k
        simp
      rw [hf, norm_smul, hcn, one_mul]
      simpa [tr, add_comm x₀] using hgrad (tr x) hx'
    have ha' : ContDiff ℝ (2 * n + 2 : ℕ) a' := ha.comp (contDiff_const.add contDiff_id)
    have has' (x : E) (hx : x ∉ closedBall 0 r) : a' x = 0 := has _ (by rwa [mem_closedBall, htr])
    have hab' (j : ℕ) (hj : j ≤ 2 * n + 2) (x : E) : ‖iteratedFDeriv ℝ j a' x‖ ≤ S := by
      change ‖iteratedFDeriv ℝ j (fun y ↦ a (x₀ + y)) x‖ ≤ _
      rw [iteratedFDeriv_comp_add_left]
      exact hab j hj _
    let H' := Matrix.of fun i j : Fin n ↦
      iteratedFDeriv ℂ 2 G 0 ![Pi.single i 1, Pi.single j 1]
    have hHn : ‖H'.det‖ = ‖H.det‖ := norm_det_hessian_translate_smul
      ((hg.analyticOnNhd_of_finiteDimensional isOpen_ball x₀
        (mem_ball_self (by positivity))).contDiffAt) hcn
    have hGb (x : E) (hx : x ∈ ball 0 (2 * r)) : ‖G x‖ ≤ Λ := by
      change ‖c • g (tr x)‖ ≤ Λ
      rw [norm_smul, hcn, one_mul]
      exact hgb _ (hgb' x hx)
    obtain ⟨-, hest⟩ := hc G hgc hGb hG0 hGg V a' S ha' has' hab'
    have h := hest s hs.ne'
    have habs : |s| = s := abs_of_pos hs
    let p (x : E) := exp (I * ((β * (g x / t)).re : ℂ))
    have hp (x : E) : oscillatoryKernel s (G x).im = p (tr x) := by
      have he : G x = (I * (β * (g (tr x) / t))) * (s : ℂ) := by
        change (I * β / t * (s : ℂ)) * g (tr x) = _
        ring
      unfold oscillatoryKernel p
      rw [he, mul_im, ofReal_im, ofReal_re, mul_zero, zero_add,
        I_mul_im, mul_div_cancel_right₀ _ hs.ne']
    simp only [hp, habs] at h
    change ‖(∫ x, p (tr x) • a' x) -
        p (tr 0) • (((2 * Real.pi * s) ^ n / ‖H'.det‖ : ℝ) • a' 0)‖ ≤
      C * S * s ^ (n + 1) at h
    rw [hHn] at h
    have hi : (∫ x, p (tr x) • a' x) = ∫ x, p x • a x :=
      integral_add_left_eq_self (fun x ↦ p x • a x) x₀
    rw [hi, show tr 0 = x₀ by simp [tr], show a' 0 = a x₀ by simp [a', tr]] at h
    exact norm_stationaryPhase_rescale n hβp ‖H.det‖ C S (p x₀) _ _ h

end TauCeti
