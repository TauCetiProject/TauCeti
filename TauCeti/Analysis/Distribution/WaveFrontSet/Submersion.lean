/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Submersion
public import TauCeti.Analysis.Distribution.WaveFrontSet.Basic
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import TauCeti.Analysis.Calculus.FDeriv.Equiv
import TauCeti.Analysis.Distribution.WaveFrontSet.ChangeOfVariables
import TauCeti.Analysis.Distribution.WaveFrontSet.EllipticRegularity
import TauCeti.Analysis.Distribution.WaveFrontSet.Localization
import TauCeti.Analysis.InnerProductSpace.LinearCoord
import TauCeti.MeasureTheory.Measure.Haar.Disintegration

/-!
# The wave front set of a pullback along a submersion

Let `f : E → E'` be a submersion between open subsets `Ω ⊆ E` and `Ω' ⊆ E'` of finite-dimensional
real inner product spaces: `f` is smooth on `Ω`, maps `Ω` into `Ω'`, and has surjective derivative
at every point of `Ω`. Every complex distribution `T` on `Ω'` then pulls back to a distribution
`f^* T` on `Ω` (`Distribution.compCLMOfSubmersion`). This file proves that the wave front set pulls
back along `f` with the transpose of its derivative (Hörmander I, Theorem 8.2.4):

`WF(f^* T) = {(x, Df(x)ᵀ η) | x ∈ Ω, (f x, η) ∈ WF(T)}`

(`Distribution.waveFrontSet_compCLMOfSubmersion`). Unlike the pullback along a general smooth map,
no condition on `WF(T)` is needed, since `Df(x)ᵀ` is injective
(`ContinuousLinearMap.adjoint_injective_iff_denseRange`) and so `Df(x)ᵀ η ≠ 0` for every
`η ≠ 0`. For a change of variables this is
`Distribution.waveFrontSet_compCLMOfOpenPartialHomeomorph`; for the projection `(x, y) ↦ x` of a
product it is the wave front set of `T ⊗ 1`
(`Distribution.waveFrontSet_transportCLM_tensorProduct_ofFun_const`).

## The argument

Near a point `x`, the local normal form of a submersion writes `f = A ∘ Θ` with `A = Df(x)` and
`Θ` a change of variables (`ContDiffOn.exists_openPartialHomeomorph_eqOn_fderiv_comp`). Since the
pullback is functorial (`Distribution.compCLMOfSubmersion_comp`) and local
(`Distribution.restrictCLM_compCLMOfSubmersion`), near `x` the distribution `f^* T` is the pullback
along `Θ` of `A^* T`, and the wave front set transforms along `Θ` by
`Distribution.isMicrolocallySmoothAt_compCLMOfOpenPartialHomeomorph_iff`. This leaves the case of
a surjective linear map `A`. Write `x = s (A x) + P x` with `P` a projection onto `ker A` and `s` a
linear section of `A` (`ContinuousLinearMap.linearSection_add_linearCoord_snd`). Then:

* `∂_k (A^* T) = 0` for `k ∈ ker A` (`Distribution.lineDerivOp_compCLMOfSubmersion_eq_zero`).
  Microlocal elliptic regularity for `∂_k` shows that `A^* T` is microlocally smooth in every
  direction `ξ` with `⟪k, ξ⟫ ≠ 0`, that is, off the range `(ker A)ᗮ` of `Aᵀ`.
* For a cutoff `φ x = φ₁ (A x) ρ (P x)`, Fubini's theorem in the coordinates `(A x, P x)` factors
  the localized Fourier transform of `A^* T` at `ζ` as that of `T` with cutoff `φ₁` at `sᵀ ζ`,
  times the Fourier transform of `ρ` on `ker A` and a constant comparing the Haar measures. Along
  the range of `Aᵀ`, where `sᵀ Aᵀ η = η` and the Fourier transform of `ρ` is its positive integral,
  rapid decay of either side gives rapid decay of the other.

## Main results

* `Distribution.isMicrolocallySmoothAt_compCLMOfSubmersion_iff`: `f^* T` is microlocally smooth at
  `(x, ξ)`, `ξ ≠ 0`, exactly when `T` is microlocally smooth at `(f x, η)` for every `η` with
  `Df(x)ᵀ η = ξ`.
* `Distribution.waveFrontSet_compCLMOfSubmersion`: the wave front set of `f^* T`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, Theorem 8.2.4 and Theorem 8.3.1.
* C. Brouder, N. V. Dang, F. Hélein, *Continuity of the fundamental operations on distributions
  having a specified wave front set*, arXiv:1409.7662v2, Proposition 5.1.
-/

public section

noncomputable section

open Complex Filter Function Metric Set TopologicalSpace TestFunction MeasureTheory LineDeriv
open scoped Distributions Topology RealInnerProductSpace ContDiff InnerProduct

namespace Distribution

variable {E E' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
  {Ω : Opens E} {Ω' : Opens E'}

/-! ### Pullback along a surjective linear map -/

section Linear

variable {A : E →L[ℝ] E'} (hA : Function.Surjective A)

/-- A cutoff `φ x' = φ₁ (A x') ρ (P x')` adapted to the coordinates `x' ↦ (A x', P x')`, equal to
`1` at `x`, with `φ₁` supported in a given neighbourhood of `A x` and `φ` in a given neighbourhood
of `x`, where `ρ` is a bump function on `ker A`. -/
private theorem exists_coord_cutoff (hAΩ : MapsTo A Ω Ω') {x : E} (hx : x ∈ Ω) {W : Set E'}
    (hW : W ∈ 𝓝 (A x)) {U : Set E} (hU : U ∈ 𝓝 x) :
    ∃ (φ₁ : 𝓓(Ω', ℂ)) (ρ : ContDiffBump (A.linearCoord hA x).2) (φ : 𝓓(Ω, ℂ)), tsupport φ₁ ⊆ W ∧
      φ₁ (A x) = 1 ∧ tsupport φ ⊆ U ∧ φ x = 1 ∧
        ∀ x', φ x' = φ₁ (A x') * ρ (A.linearCoord hA x').2 := by
  set L := A.linearCoord hA
  -- A radius `r` with `L⁻¹ (ball (L x) r) ⊆ Ω ∩ U`.
  obtain ⟨r, hr, hrΩ⟩ : ∃ r > 0, ball (L x) r ⊆ L.symm ⁻¹' (Ω ∩ U) :=
    Metric.mem_nhds_iff.1 ((L.symm.continuous.continuousAt (x := L x)).preimage_mem_nhds
      (by rw [L.symm_apply_apply]; exact inter_mem (Ω.isOpen.mem_nhds hx) hU))
  obtain ⟨φ₁, hφ₁s, hφ₁x⟩ := exists_tsupport_subset_apply_eq (Ω := Ω') (n := ⊤)
    (inter_mem (inter_mem hW (ball_mem_nhds _ (half_pos hr))) (Ω'.isOpen.mem_nhds (hAΩ hx)))
    inter_subset_right (1 : ℂ)
  let ρ : ContDiffBump (L x).2 := ⟨r / 4, r / 2, by positivity, by linarith⟩
  -- The product cutoff is supported in the compact set `S ⊆ Ω ∩ U`.
  set S := L.symm '' (closedBall (A x) (r / 2) ×ˢ closedBall (L x).2 (r / 2))
  have hS : IsCompact S :=
    ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)).image L.symm.continuous
  have hSΩ : S ⊆ Ω ∩ U := by
    rintro _ ⟨p, ⟨hp₁, hp₂⟩, rfl⟩
    refine hrΩ (mem_ball.2 (lt_of_le_of_lt ?_ (half_lt_self hr)))
    rw [Prod.dist_eq, ContinuousLinearMap.linearCoord_apply_fst]
    exact max_le (mem_closedBall.1 hp₁) (mem_closedBall.1 hp₂)
  have hsupp : support (fun x' ↦ φ₁ (A x') * (ρ (L x').2 : ℂ)) ⊆ S := by
    intro x' hx'
    refine ⟨L x', ⟨?_, ?_⟩, L.symm_apply_apply x'⟩
    · have h := ((hφ₁s (subset_tsupport _ (left_ne_zero_of_mul hx'))).1).2
      rw [ContinuousLinearMap.linearCoord_apply_fst]
      exact ball_subset_closedBall h
    · have h := right_ne_zero_of_mul hx'
      rw [Complex.ofReal_ne_zero, ← mem_support, ρ.support_eq] at h
      exact ball_subset_closedBall h
  have htsupp := closure_minimal hsupp hS.isClosed
  let φ : 𝓓(Ω, ℂ) := ⟨fun x' ↦ φ₁ (A x') * (ρ (L x').2 : ℂ),
    (φ₁.contDiff.comp A.contDiff).mul (Complex.ofRealCLM.contDiff.comp
      (ρ.contDiff.comp L.contDiff.snd)), .of_isClosed_subset hS (isClosed_tsupport _) htsupp,
    htsupp.trans (hSΩ.trans inter_subset_left)⟩
  have hφ (x' : E) : φ x' = φ₁ (A x') * ρ (L x').2 := congrFun TestFunction.coe_mk x'
  refine ⟨φ₁, ρ, φ, hφ₁s.trans (inter_subset_left.trans inter_subset_left), hφ₁x,
    htsupp.trans (hSΩ.trans inter_subset_right), ?_, hφ⟩
  rw [hφ, hφ₁x, ρ.one_of_mem_closedBall (mem_closedBall_self (by positivity))]
  simp

variable [MeasurableSpace E] [BorelSpace E] [MeasurableSpace E'] [BorelSpace E']
  (μ : Measure E) [μ.IsAddHaarMeasure] (ν : Measure E') [ν.IsAddHaarMeasure]

variable (hf : ContDiffOn ℝ ∞ A Ω) (hAΩ : MapsTo A Ω Ω')
  (hsurj : ∀ x ∈ Ω, Function.Surjective (fderiv ℝ A x))

/-- The pullback along a linear map `A` is microlocally smooth in every direction `ξ` that is not
orthogonal to `ker A`, that is, outside the range of `Aᵀ`. -/
private theorem isMicrolocallySmoothAt_compCLMOfSubmersion_of_inner_ne_zero (T : 𝓓'(Ω', ℂ))
    {x ξ k : E} (hx : x ∈ Ω) (hk : A k = 0) (hkξ : ⟪k, ξ⟫ ≠ 0) :
    (compCLMOfSubmersion μ ν A hf hAΩ hsurj T).IsMicrolocallySmoothAt x ξ := by
  -- `∂_k` is elliptic at `ξ` and kills the pullback.
  refine IsMicrolocallySmoothAt.of_sum_smul_iteratedLineDerivOp (s := {()}) (c := fun _ ↦ 1)
    (k := fun _ ↦ 1) (m := fun _ ↦ ![k]) (M := 1) (by simp) ?_ ?_
  · simp only [Finset.sum_singleton, one_smul, iteratedLineDerivOp_one, Matrix.cons_val_fin_one,
      lineDerivOp_compCLMOfSubmersion_eq_zero μ ν hf hAΩ hsurj T hk]
    exact isMicrolocallySmoothAt_of_notMem_dsupport hx (by simp) ξ
  · simpa [TauCeti.constCoeffPrincipalSymbol_def] using hkξ

/-- **The localized Fourier transform of a linear pullback.** For a cutoff
`φ x = φ₁ (A x) ρ (P x)` adapted to the coordinates `x ↦ (A x, P x)`, the localized Fourier
transform of `A^* T` at `ζ` is that of `T` with cutoff `φ₁` at `sᵀ ζ`, where `s` is the section
`linearSection` of `A`, times the Fourier transform of `ρ` on `ker A` at `ζ` and the constant
`linearScale` comparing the Haar measures. -/
private theorem localFourier_compCLMOfSubmersion_eq (T : 𝓓'(Ω', ℂ)) (φ₁ : 𝓓(Ω', ℂ))
    (ρ : (A : E →ₗ[ℝ] E').ker → ℂ) {φ : 𝓓(Ω, ℂ)}
    (hφ : ∀ x, φ x = φ₁ (A x) * ρ (A.linearCoord hA x).2) (ζ : E) :
    (compCLMOfSubmersion μ ν A hf hAΩ hsurj T).localFourier φ ζ =
      ((A.linearScale hA μ ν : ℝ) *
        ∫ k, ρ k * TauCeti.fourierAtom ζ (k : E) ∂Measure.addHaar) *
      T.localFourier φ₁ (((A.linearSection hA)†) ζ) := by
  rw [localFourier_def, localFourier_def, ← smul_eq_mul, ← map_smul]
  refine complexPairing_compCLMOfSubmersion μ ν hf hAΩ hsurj T fun g _ _ _ ↦ ?_
  set η := ((A.linearSection hA)†) ζ
  -- In the coordinates `(A x, P x)` the integrand is a product.
  have hprod (x : E) : φ x * TauCeti.fourierAtom ζ x * (g (A x) : ℂ) =
      (φ₁ (A.linearCoord hA x).1 * TauCeti.fourierAtom η (A.linearCoord hA x).1 *
          g (A.linearCoord hA x).1) *
        (ρ (A.linearCoord hA x).2 * TauCeti.fourierAtom ζ ((A.linearCoord hA x).2 : E)) := by
    simp only [ContinuousLinearMap.linearCoord_apply_fst, hφ, TauCeti.fourierAtom_eq_fourierChar,
      A.inner_eq_inner_linearCoord hA x ζ, neg_add, AddChar.map_add_eq_mul, Circle.coe_mul, η]
    ring
  simp only [FunLike.coe_smul, Pi.smul_apply, bilinLeftCLM_apply,
    ContinuousLinearMap.mul_apply', smul_eq_mul, hprod]
  symm
  refine (A.integral_mul_linearCoord hA μ ν (fun y ↦ φ₁ y * TauCeti.fourierAtom η y * g y)
    (fun k ↦ ρ k * TauCeti.fourierAtom ζ (k : E))).trans ?_
  simp only [Complex.real_smul, mul_assoc, integral_const_mul]
  ring

include hA in
/-- The pullback along a surjective linear map `A` is microlocally smooth at `(x, Aᵀ η)` if `T`
is microlocally smooth at `(A x, η)`. -/
private theorem isMicrolocallySmoothAt_compCLMOfSubmersion_adjoint (T : 𝓓'(Ω', ℂ)) {x : E}
    (hx : x ∈ Ω) {η : E'} (hη : η ≠ 0) (h : T.IsMicrolocallySmoothAt (A x) η) :
    (compCLMOfSubmersion μ ν A hf hAΩ hsurj T).IsMicrolocallySmoothAt x ((A†) η) := by
  obtain ⟨W, hW, Γ, hΓo, hηΓ, hΓc, hdecay⟩ := h.exists_nhds_cone
  obtain ⟨φ₁, ρ, φ, hφ₁W, -, -, hφx, hφ⟩ := exists_coord_cutoff hA hAΩ hx hW univ_mem
  set s := A.linearSection hA
  -- The frequencies `ζ` with `sᵀ ζ ∈ Γ` and `‖ζ‖ < M ‖sᵀ ζ‖` form an open cone around `Aᵀ η`.
  have hsA : (s†) ((A†) η) = η := A.adjoint_linearSection_adjoint_apply hA η
  set M := ‖(A†) η‖ / ‖η‖ + 1
  refine isMicrolocallySmoothAt_iff.2 ⟨φ, by simp [hφx], {ζ | (s†) ζ ∈ Γ ∧ ‖ζ‖ < M * ‖(s†) ζ‖},
    (hΓo.preimage (s†).continuous).inter (isOpen_lt continuous_norm (by fun_prop)), ⟨by
      rwa [mem_ofPred_eq, hsA], ?_⟩, fun t ht ζ hζ ↦ ⟨?_, ?_⟩, fun N ↦ ?_⟩
  · rw [hsA, add_mul, div_mul_cancel₀ _ (norm_ne_zero_iff.2 hη), one_mul]
    exact lt_add_of_pos_right _ (norm_pos_iff.2 hη)
  · rw [map_smul]
    exact hΓc t ht _ hζ.1
  · rw [map_smul, norm_smul, norm_smul, Real.norm_of_nonneg ht.le, mul_left_comm]
    exact mul_lt_mul_of_pos_left hζ.2 ht
  -- The decay of `T` with cutoff `φ₁` transfers through the product formula.
  obtain ⟨C, hC⟩ := hdecay φ₁ hφ₁W N
  set c := (A.linearScale hA μ ν : ℝ)
  set R := ∫ k, ρ k ∂Measure.addHaar
  refine ⟨max 1 M ^ N * (c * R * C), fun ζ hζ ↦ ?_⟩
  rw [localFourier_compCLMOfSubmersion_eq hA μ ν hf hAΩ hsurj T φ₁ (fun k ↦ (ρ k : ℂ)) hφ ζ]
  have hR : ‖∫ k, (ρ k : ℂ) * TauCeti.fourierAtom ζ (k : E) ∂Measure.addHaar‖ ≤ R := by
    refine (norm_integral_le_integral_norm _).trans_eq (integral_congr_ae
      (Eventually.of_forall fun k ↦ ?_))
    simp only [norm_mul, TauCeti.norm_fourierAtom, mul_one, Complex.norm_real,
      Real.norm_of_nonneg (ρ.nonneg' k)]
  have hc : 0 ≤ c := NNReal.coe_nonneg _
  have hR0 : 0 ≤ R := integral_nonneg ρ.nonneg'
  have hζ' : 1 + ‖ζ‖ ≤ max 1 M * (1 + ‖(s†) ζ‖) := by
    nlinarith [hζ.2, le_max_left 1 M, le_max_right 1 M, norm_nonneg ((s†) ζ)]
  calc (1 + ‖ζ‖) ^ N * ‖(c * ∫ k, (ρ k : ℂ) * TauCeti.fourierAtom ζ (k : E)
          ∂Measure.addHaar) * T.localFourier φ₁ ((s†) ζ)‖
      ≤ (max 1 M * (1 + ‖(s†) ζ‖)) ^ N * ((c * R) * ‖T.localFourier φ₁ ((s†) ζ)‖) := by
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hc]
        gcongr
    _ = max 1 M ^ N * (c * R) * ((1 + ‖(s†) ζ‖) ^ N * ‖T.localFourier φ₁ ((s†) ζ)‖) := by
        rw [mul_pow]
        ring
    _ ≤ max 1 M ^ N * (c * R) * C := by
        gcongr
        exact hC _ hζ.1
    _ = max 1 M ^ N * (c * R * C) := by ring

include hA in
/-- Conversely, `T` is microlocally smooth at `(A x, η)` if its pullback along a surjective linear
map `A` is microlocally smooth at `(x, Aᵀ η)`. -/
private theorem IsMicrolocallySmoothAt.of_compCLMOfSubmersion_adjoint (T : 𝓓'(Ω', ℂ)) {x : E}
    (hx : x ∈ Ω) {η : E'}
    (h : (compCLMOfSubmersion μ ν A hf hAΩ hsurj T).IsMicrolocallySmoothAt x ((A†) η)) :
    T.IsMicrolocallySmoothAt (A x) η := by
  obtain ⟨U, hU, Γ, hΓo, hηΓ, hΓc, hdecay⟩ := h.exists_nhds_cone
  obtain ⟨φ₁, ρ, φ, -, hφ₁x, hφU, -, hφ⟩ := exists_coord_cutoff hA hAΩ hx univ_mem hU
  set s := A.linearSection hA
  have hsA (η' : E') : (s†) ((A†) η') = η' := A.adjoint_linearSection_adjoint_apply hA η'
  refine isMicrolocallySmoothAt_iff.2 ⟨φ₁, by simp [hφ₁x], (A†) ⁻¹' Γ,
    hΓo.preimage (A†).continuous, hηΓ, fun t ht η' hη' ↦ by simpa using hΓc t ht _ hη',
    fun N ↦ ?_⟩
  obtain ⟨C, hC⟩ := hdecay φ hφU N
  -- Along `Aᵀ η'` the Fourier transform of `ρ` is its integral, since `ker A ⟂ range Aᵀ`.
  set c := (A.linearScale hA μ ν : ℝ)
  set R := ∫ k, ρ k ∂Measure.addHaar
  have hcR : 0 < c * R := mul_pos (NNReal.coe_pos.2 (A.linearScale_pos hA μ ν))
    (ρ.integral_pos)
  refine ⟨max 1 ‖s†‖ ^ N * C / (c * R), fun η' hη' ↦ ?_⟩
  have hF := localFourier_compCLMOfSubmersion_eq hA μ ν hf hAΩ hsurj T φ₁ (fun k ↦ (ρ k : ℂ)) hφ
    ((A†) η')
  have hRη : ∫ k, (ρ k : ℂ) * TauCeti.fourierAtom ((A†) η') (k : E) ∂Measure.addHaar = R := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Eventually.of_forall fun k ↦ ?_)
    simp [ContinuousLinearMap.adjoint_inner_right]
  rw [hRη, hsA, ← Complex.ofReal_mul] at hF
  have hη'le : 1 + ‖η'‖ ≤ max 1 ‖s†‖ * (1 + ‖(A†) η'‖) := by
    have h := (s†).le_opNorm ((A†) η')
    rw [hsA] at h
    nlinarith [le_max_left 1 ‖s†‖, le_max_right 1 ‖s†‖, norm_nonneg ((A†) η')]
  rw [le_div_iff₀ hcR]
  calc (1 + ‖η'‖) ^ N * ‖T.localFourier φ₁ η'‖ * (c * R)
      = (1 + ‖η'‖) ^ N * ‖((c * R : ℝ) : ℂ) * T.localFourier φ₁ η'‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hcR.le]
        ring
    _ ≤ (max 1 ‖s†‖ * (1 + ‖(A†) η'‖)) ^ N * ‖((c * R : ℝ) : ℂ) * T.localFourier φ₁ η'‖ := by
        gcongr
    _ = max 1 ‖s†‖ ^ N * ((1 + ‖(A†) η'‖) ^ N *
          ‖(compCLMOfSubmersion μ ν A hf hAΩ hsurj T).localFourier φ ((A†) η')‖) := by
        rw [hF, mul_pow, mul_assoc]
    _ ≤ max 1 ‖s†‖ ^ N * C := by
        gcongr
        exact hC _ hη'

include hA in
/-- **The wave front set of a pullback along a surjective linear map, pointwise.** The pullback
`A^* T` is microlocally smooth at `(x, ξ)`, `ξ ≠ 0`, exactly when `T` is microlocally smooth at
`(A x, η)` for every `η` with `Aᵀ η = ξ`. -/
private theorem isMicrolocallySmoothAt_compCLMOfSubmersion_linear_iff (T : 𝓓'(Ω', ℂ)) {x ξ : E}
    (hx : x ∈ Ω) (hξ : ξ ≠ 0) :
    (compCLMOfSubmersion μ ν A hf hAΩ hsurj T).IsMicrolocallySmoothAt x ξ ↔
      ∀ η, (A†) η = ξ → T.IsMicrolocallySmoothAt (A x) η := by
  refine ⟨fun h η hη ↦ ?_, fun h ↦ ?_⟩
  · subst hη
    exact IsMicrolocallySmoothAt.of_compCLMOfSubmersion_adjoint hA μ ν hf hAΩ hsurj T hx h
  by_cases hξA : ∃ η, (A†) η = ξ
  · obtain ⟨η, rfl⟩ := hξA
    exact isMicrolocallySmoothAt_compCLMOfSubmersion_adjoint hA μ ν hf hAΩ hsurj T hx
      (fun h0 ↦ hξ (by simp [h0])) (h η rfl)
  · -- Off the range of `Aᵀ`, which is `(ker A)ᗮ`, some `k ∈ ker A` has `⟪k, ξ⟫ ≠ 0`.
    obtain ⟨k, hk, hkξ⟩ : ∃ k, A k = 0 ∧ ⟪k, ξ⟫ ≠ 0 := by
      by_contra! hcon
      have hmem : ξ ∈ (A.ker)ᗮ := (Submodule.mem_orthogonal _ _).2 fun k hk ↦ hcon k hk
      rw [A.orthogonal_ker,
        (A†).range.isClosed_of_finiteDimensional.submodule_topologicalClosure_eq] at hmem
      exact hξA hmem
    exact isMicrolocallySmoothAt_compCLMOfSubmersion_of_inner_ne_zero μ ν hf hAΩ hsurj T hx hk
      hkξ

end Linear

/-! ### Pullback along a submersion -/

section Submersion

variable [MeasurableSpace E] [BorelSpace E] [MeasurableSpace E'] [BorelSpace E']
  (μ : Measure E) [μ.IsAddHaarMeasure] (ν : Measure E') [ν.IsAddHaarMeasure]
  {f : E → E'} (hf : ContDiffOn ℝ ∞ f Ω) (hfΩ : MapsTo f Ω Ω')
  (hsurj : ∀ x ∈ Ω, Function.Surjective (fderiv ℝ f x))

/-- Where `f = A ∘ Θ` for a change of variables `Θ` and a linear map `A`, the pullback `f^* T` is
the pullback along `Θ` of `A^* T`. -/
private theorem restrictCLM_compCLMOfSubmersion_eq (T : 𝓓'(Ω', ℂ))
    {Θ : OpenPartialHomeomorph E E} (hΘ : ContDiffOn ℝ ∞ Θ Θ.source)
    (hΘ' : ContDiffOn ℝ ∞ Θ.symm Θ.target) {U V : Opens E} (hU : (U : Set E) = Θ.source)
    (hUΩ : U ≤ Ω) (hΘUV : MapsTo Θ U V) {A : E →L[ℝ] E'} (hfΘ : EqOn f (A ∘ Θ) U)
    {hAV : MapsTo A V Ω'} {hAsurj : ∀ z ∈ V, Function.Surjective (fderiv ℝ A z)} :
    (restrictCLM (compCLMOfSubmersion μ ν f hf hfΩ hsurj T) : 𝓓'(U, ℂ)) =
      compCLMOfOpenPartialHomeomorph Θ hΘ hΘ' hU.subset hΘUV
        (compCLMOfSubmersion μ ν A A.contDiff.contDiffOn hAV hAsurj T) := by
  have hΘsurj : ∀ z ∈ U, Function.Surjective (fderiv ℝ Θ z) := fun z hz ↦
    (Θ.isInvertible_fderiv_of_contDiffOn hΘ hΘ' (by simp) (hU ▸ hz)).surjective
  have hAΘ : ContDiffOn ℝ ∞ (A ∘ Θ) U := A.contDiff.comp_contDiffOn (hU ▸ hΘ)
  have hAΘΩ : MapsTo (A ∘ Θ) U Ω' := fun z hz ↦ by
    rw [← hfΘ hz]
    exact hfΩ (hUΩ hz)
  have hAΘsurj : ∀ z ∈ U, Function.Surjective (fderiv ℝ (A ∘ Θ) z) := fun z hz ↦ by
    rw [← (hfΘ.eventuallyEq_of_mem (U.isOpen.mem_nhds hz)).fderiv_eq]
    exact hsurj z (hUΩ hz)
  rw [restrictCLM_compCLMOfSubmersion μ ν hf hfΩ hsurj hUΩ,
    compCLMOfSubmersion_congr μ ν hAΘ hAΘΩ hAΘsurj hfΘ.symm,
    compCLMOfSubmersion_comp μ μ (hU ▸ hΘ) hΘUV hΘsurj ν A.contDiff.contDiffOn hAV hAsurj,
    compCLMOfSubmersion_eq_compCLMOfOpenPartialHomeomorph]

/-- **The wave front set of a pullback along a submersion, pointwise** (Hörmander I,
Theorem 8.2.4). The pullback `f^* T` is microlocally smooth at `(x, ξ)`, `ξ ≠ 0`, exactly when
`T` is microlocally smooth at `(f x, η)` for every `η` with `Df(x)ᵀ η = ξ`. Since `Df(x)ᵀ` is
injective, there is at most one such `η`. -/
theorem isMicrolocallySmoothAt_compCLMOfSubmersion_iff (T : 𝓓'(Ω', ℂ)) {x ξ : E} (hx : x ∈ Ω)
    (hξ : ξ ≠ 0) :
    (compCLMOfSubmersion μ ν f hf hfΩ hsurj T).IsMicrolocallySmoothAt x ξ ↔
      ∀ η, ((fderiv ℝ f x)†) η = ξ → T.IsMicrolocallySmoothAt (f x) η := by
  -- Near `x`, `f = A ∘ Θ` with `A = Df(x)` and `Θ` a change of variables.
  obtain ⟨Θ, hxΘ, hΘΩ, hΘ, hΘ', hfΘ⟩ := hf.exists_openPartialHomeomorph_eqOn_fderiv_comp
    Ω.isOpen hx (by simp) (LinearMap.range_eq_top.2 (hsurj x hx)) (.of_finiteDimensional _)
  have hAsurj : Function.Surjective (fderiv ℝ f x) := hsurj x hx
  obtain ⟨A, hA⟩ : ∃ A, fderiv ℝ f x = A := ⟨_, rfl⟩
  rw [hA] at hfΘ hAsurj
  let U : Opens E := ⟨Θ.source, Θ.open_source⟩
  let V : Opens E := ⟨Θ.target, Θ.open_target⟩
  have hUΩ : U ≤ Ω := by simpa [U, ← SetLike.coe_subset_coe] using hΘΩ
  have hxU : x ∈ U := by simpa [U] using hxΘ
  have hΘUV : MapsTo Θ U V := fun z hz ↦ by simpa [V] using Θ.map_source (by simpa [U] using hz)
  obtain ⟨hd, hds⟩ := Θ.differentiableAt_and_differentiableAt_symm_of_contDiffOn hΘ hΘ' (by simp)
    hxΘ
  have hAV : MapsTo A V Ω' := fun z hz ↦ by
    have h := hfΘ (Θ.map_target hz)
    simp only [comp_apply, Θ.right_inv hz] at h
    rw [← h]
    exact hfΩ (hΘΩ (Θ.map_target hz))
  have hAsurj' : ∀ z ∈ V, Function.Surjective (fderiv ℝ A z) := fun _ _ ↦ by
    rw [A.fderiv]
    exact hAsurj
  -- On `U`, `f^* T` is the pullback along `Θ` of `A^* T`, and microlocal smoothness transforms
  -- along `Θ` and along `A`.
  rw [← isMicrolocallySmoothAt_restrictCLM_iff hUΩ hxU,
    restrictCLM_compCLMOfSubmersion_eq μ ν hf hfΩ hsurj T hΘ hΘ' (U := U) rfl hUΩ hΘUV hfΘ
      (hAV := hAV) (hAsurj := hAsurj'),
    isMicrolocallySmoothAt_compCLMOfOpenPartialHomeomorph_iff (hUΩ := hΘUV) hxU,
    isMicrolocallySmoothAt_compCLMOfSubmersion_linear_iff hAsurj μ ν _ hAV _ T
      (Θ.map_source hxΘ) fun h0 ↦ hξ (by
        rw [← Θ.adjoint_fderiv_apply_adjoint_fderiv_symm_apply hxΘ hd hds ξ, h0, map_zero])]
  -- `f x = A (Θ x)` and `Df(x) = A ∘ DΘ(x)`.
  rw [show f x = A (Θ x) from hfΘ hxΘ,
    (hfΘ.eventuallyEq_of_mem (Θ.open_source.mem_nhds hxΘ)).fderiv_eq, A.fderiv_comp_left hd]
  exact forall_congr' fun η ↦ imp_congr_left
    (Θ.adjoint_apply_eq_adjoint_fderiv_symm_apply_iff hxΘ hd hds A η ξ)

/-- **The wave front set of a pullback along a submersion** (Hörmander I, Theorem 8.2.4): the
covectors of `WF(f^* T)` are exactly the `(x, Df(x)ᵀ η)` with `x ∈ Ω` and `(f x, η) ∈ WF(T)`.
No condition on `WF(T)` is needed, since `Df(x)ᵀ η ≠ 0` for every `η ≠ 0`. -/
theorem waveFrontSet_compCLMOfSubmersion (T : 𝓓'(Ω', ℂ)) :
    (compCLMOfSubmersion μ ν f hf hfΩ hsurj T).waveFrontSet =
      {p | p.1 ∈ Ω ∧ ∃ η, (f p.1, η) ∈ T.waveFrontSet ∧ ((fderiv ℝ f p.1)†) η = p.2} := by
  ext ⟨x, ξ⟩
  simp only [mem_waveFrontSet_iff, mem_ofPred_eq]
  constructor
  · rintro ⟨hx, hξ, hT⟩
    rw [isMicrolocallySmoothAt_compCLMOfSubmersion_iff μ ν hf hfΩ hsurj T hx hξ] at hT
    simp only [not_forall] at hT
    obtain ⟨η, hη, hTη⟩ := hT
    refine ⟨hx, η, ⟨hfΩ hx, ?_, hTη⟩, hη⟩
    rintro rfl
    exact hξ (by rw [← hη, map_zero])
  · rintro ⟨hx, η, ⟨-, hη0, hTη⟩, rfl⟩
    -- `Df(x)ᵀ` is injective, since `Df(x)` is surjective.
    have hinj : ((fderiv ℝ f x)†) η ≠ 0 :=
      (map_ne_zero_iff _
        (ContinuousLinearMap.adjoint_injective_iff_denseRange.2 (hsurj x hx).denseRange)).2 hη0
    refine ⟨hx, hinj, fun h ↦ hTη ?_⟩
    exact (isMicrolocallySmoothAt_compCLMOfSubmersion_iff μ ν hf hfΩ hsurj T hx hinj).1 h η rfl

end Submersion

end Distribution
