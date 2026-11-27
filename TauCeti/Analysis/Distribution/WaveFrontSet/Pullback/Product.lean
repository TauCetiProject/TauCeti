/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.WaveFrontSet.Pullback.SmoothMap
public import TauCeti.Analysis.Distribution.WaveFrontSet.Product
public import TauCeti.Analysis.Distribution.WaveFrontSet.TensorProduct
import TauCeti.Analysis.Distribution.TestFunction.Prod
import TauCeti.Analysis.Distribution.TestFunction.Schwartz
import TauCeti.Analysis.Distribution.WaveFrontSet.Sobolev.Tempered
import TauCeti.Analysis.Fourier.Continuous
import TauCeti.Analysis.Fourier.Prod
import TauCeti.Analysis.Fourier.Mollifier
import TauCeti.Analysis.InnerProductSpace.ProdL2

/-!
# The product of distributions as a pullback along the diagonal

Let `S` and `T` be complex distributions on an open set `Ω` of a finite-dimensional real inner
product space `E`. Their tensor product `S ⊗ T` (`Distribution.tensorProduct`), moved to the
Euclidean product `WithLp 2 (E × E)` by `Distribution.transportCLM`, is a distribution of two
variables. Restricting it to the diagonal `x ↦ (x, x)` is the product `S T` in the same variable
(Hörmander I, Theorem 8.2.10 and the remark after it).

The diagonal map is the continuous linear map `WithLp.diagL2`, whose transpose sends `(ξ, η)` to
`ξ + η` (`WithLp.adjoint_diagL2_apply`), so its normal set consists of the covectors
`((x, x), (ξ, -ξ))` with `ξ ≠ 0`. By the wave front bound for tensor products, such a covector lies
in `WF(S ⊗ T)` only if `(x, ξ) ∈ WF(S)` and `(x, -ξ) ∈ WF(T)`. So Hörmander's condition for the
product, that no covector of `WF(S)` is opposite to a covector of `WF(T)` at the same point, makes
the wave front set of `S ⊗ T` miss the normal set of the diagonal
(`Distribution.adjoint_fderiv_diagonal_apply_ne_zero`), and `S ⊗ T` has a pullback along the
diagonal (`Distribution.pullback`). This pullback is the product
(`Distribution.pullback_diagonal_transportCLM_tensorProduct_eq_product`):

`Δ^* (S ⊗ T) = S T`.

## The argument

Both sides are local, so it suffices to compare them on test functions `ψ` supported where a cutoff
`χ` is one, with `S` and `T` without opposite covectors over the support of `χ`. There the product
is `∫ S (χ e_η) T (ψ e_(-η)) dη` (`Distribution.cutoffProduct_apply_eq_integral`), with
`e_η x = 𝐞 (-⟪x, η⟫)`.

The pullback is the limit of `(S ⊗ T) (g_♯ (ψ ⊗ ρ))` as the normalized bumps `ρ` concentrate at
`0`, where `g (x, y) = (x, x) + y` and `g_♯` integrates over the fibres of `g`
(`Distribution.tendsto_pullbackInl`). The inverse Fourier transform of `g_♯ (ψ ⊗ ρ)` at `ζ` is
`𝓕⁻ ψ (ζ.1 + ζ.2) 𝓕⁻ ρ (ζ)`. Testing `S ⊗ T` against it through Fourier inversion
(`Distribution.apply_eq_integral_fourierInv_mul_localFourier`), with the product cutoff
`χ (x) χ (y)` whose localized Fourier transform splits
(`Distribution.localFourier_transportCLM_tensorProduct`), gives

`(S ⊗ T) (g_♯ (ψ ⊗ ρ)) = ∫ 𝓕⁻ ψ (ζ.1 + ζ.2) 𝓕⁻ ρ (ζ) S (χ e_ζ.1) T (χ e_ζ.2) dζ`.

As `ρ` concentrates, `𝓕⁻ ρ` tends to one and stays bounded by one
(`ContDiffBump.tendsto_fourier_normed`, `ContDiffBump.norm_fourier_normed_le`); the condition on
opposite covectors makes the integrand without this factor integrable
(`Distribution.NoOppositeCovectorsOn.integrable_mul_localFourier_mul_localFourier`), so dominated
convergence applies. Integrating the limit first in `ζ.2` gives `T (ψ e_(-ζ.1))` by Fourier
inversion again, hence the product integral above.

## Main declarations

* `Distribution.adjoint_fderiv_diagonal_apply_ne_zero`: under Hörmander's condition the wave front
  set of `S ⊗ T` misses the normal set of the diagonal.
* `Distribution.pullback_diagonal_transportCLM_tensorProduct_eq_product`: the pullback of
  `S ⊗ T` along the diagonal is the product `S T`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, Theorem 8.2.10 and the remark following it (the product as the restriction of
  the tensor product to the diagonal).
* C. Brouder, N. V. Dang, F. Hélein, *Continuity of the fundamental operations on distributions
  having a specified wave front set*, Studia Math. 232 (2016), arXiv:1409.7662v2, §6 (products
  as pullbacks of tensor products by the diagonal).
-/

public section

noncomputable section

open Complex Filter Function MeasureTheory Metric Set TopologicalSpace TestFunction WithLp TauCeti
open scoped Distributions Topology FourierTransform RealInnerProductSpace ContDiff SchwartzMap

namespace Distribution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Ω : Opens E}

/-! ### The diagonal is admissible -/

variable {V : Opens (E × E)} {W : Opens (WithLp 2 (E × E))} {S T : 𝓓'(Ω, ℂ)}
  (hV : (V : Set (E × E)) = (Ω : Set E) ×ˢ (Ω : Set E))
  (hW : MapsTo (prodContinuousLinearEquiv 2 ℝ E E) W V)

/-- **The diagonal is admissible for `S ⊗ T`.** If at every point no covector of the wave front set
of `S` is opposite to a covector of the wave front set of `T`, then no covector of the wave front
set of `S ⊗ T` over the diagonal lies in the normal set of the diagonal map `x ↦ (x, x)`: these are
the covectors `((x, x), (ξ, -ξ))`, and `((x, x), (ξ, η)) ∈ WF(S ⊗ T)` with `ξ ≠ 0` and `η ≠ 0`
forces `(x, ξ) ∈ WF(S)` and `(x, η) ∈ WF(T)`. -/
theorem adjoint_fderiv_diagonal_apply_ne_zero (h : ∀ x, NoOppositeCovectorsOn S T {x}) :
    ∀ x ∈ Ω, ∀ η, (toLp 2 (x, x), η) ∈ (transportCLM (prodContinuousLinearEquiv 2 ℝ E E) hW
        (S.tensorProduct T hV.subset)).waveFrontSet →
      (fderiv ℝ (fun x : E ↦ toLp 2 (x, x)) x).adjoint η ≠ 0 := by
  intro x _ η hη h0
  rw [← coe_diagL2 ℝ E, (diagL2 ℝ E).fderiv, adjoint_diagL2_apply] at h0
  have hη0 : η ≠ 0 := (mem_waveFrontSet_iff.1 hη).2.1
  have hsnd : η.snd = -η.fst := eq_neg_of_add_eq_zero_right h0
  have hfst : η.fst ≠ 0 := fun hf ↦ hη0 (ofLp_injective 2 (by ext <;> simp [hf, hsnd]))
  obtain ⟨h₁, h₂⟩ := waveFrontSet_transportCLM_tensorProduct_subset S T hV hW hη
  simp only [toLp_fst, toLp_snd, mem_union, mem_prod, mem_singleton_iff] at h₁ h₂
  rcases h₁ with h₁ | ⟨-, h₁⟩
  · rcases h₂ with h₂ | ⟨-, h₂⟩
    · exact noOppositeCovectorsOn_singleton_iff.1 (h x) η.fst h₁ (hsnd ▸ h₂)
    · exact hfst (by simpa [hsnd] using h₂)
  · exact hfst h₁

/-! ### The fibre integral of `ψ ⊗ ρ` along `(x, y) ↦ (x, x) + y` -/

variable [MeasurableSpace E] [BorelSpace E]

/-- **The Fourier transform of `g_♯ (ψ ⊗ ρ)`.** For `g (x, y) = (x, x) + y`, the inverse Fourier
transform of the fibre integral of `(x, y) ↦ ψ x ρ y` along `g` is
`ζ ↦ 𝓕⁻ ψ (ζ.1 + ζ.2) 𝓕⁻ ρ (ζ)`. -/
private theorem fourierInv_fiberIntegralCLM_addSnd_diagonal
    (hf : ContDiffOn ℝ ∞ (fun x : E ↦ toLp 2 (x, x)) Ω) (ψ : 𝓓(Ω, ℝ))
    {ρ : WithLp 2 (E × E) → ℝ} {F : 𝓓(addSndDomain hf.continuousOn W, ℝ)}
    (hF : ∀ p, F p = ψ p.fst * ρ p.snd) (ζ : WithLp 2 (E × E)) :
    𝓕⁻ (fun z ↦ (fiberIntegralCLM volume volume (addSnd fun x : E ↦ toLp 2 (x, x))
        (contDiffOn_addSnd hf) (mapsTo_addSnd _)
        (surjective_fderiv_addSnd _ (hf.differentiableOn (by simp))) F z : ℂ)) ζ =
      𝓕⁻ (fun x ↦ (ψ x : ℂ)) (ζ.fst + ζ.snd) * 𝓕⁻ (fun y ↦ (ρ y : ℂ)) ζ := by
  set g : WithLp 2 (E × E) → ℂ := fun z ↦ (𝐞 ⟪z, ζ⟫ : ℂ)
  have hg : Continuous g := by fun_prop
  -- On `E × (E × E)` the integrand is the inverse Fourier kernel at `(ζ.1 + ζ.2, ζ)` against
  -- `(x, y) ↦ ψ x ρ y`.
  have hin (p : WithLp 2 (E × WithLp 2 (E × E))) :
      F p • g (addSnd (fun x : E ↦ toLp 2 (x, x)) p) =
        𝐞 ⟪p, toLp 2 (ζ.fst + ζ.snd, ζ)⟫ • ((ψ p.fst : ℂ) * (ρ p.snd : ℂ)) := by
    have h : ⟪toLp 2 (p.fst, p.fst) + p.snd, ζ⟫ = ⟪p, toLp 2 (ζ.fst + ζ.snd, ζ)⟫ := by
      simp only [inner_add_left, inner_add_right, prod_inner_apply, ofLp_fst, ofLp_snd]
    simp only [g, addSnd_apply, h, hF, Complex.real_smul, Complex.ofReal_mul, Circle.smul_def,
      smul_eq_mul]
    ring
  rw [Real.fourierInv_eq]
  set Φ := fiberIntegralCLM volume volume (addSnd fun x : E ↦ toLp 2 (x, x))
    (contDiffOn_addSnd hf) (mapsTo_addSnd _)
    (surjective_fderiv_addSnd _ (hf.differentiableOn (by simp))) F
  have hL : ∫ z, 𝐞 ⟪z, ζ⟫ • ((Φ z : ℝ) : ℂ) = ∫ z, Φ z • g z := by
    refine integral_congr_ae (ae_of_all _ fun z ↦ ?_)
    simp [g, Circle.smul_def, Complex.real_smul, mul_comm]
  rw [hL, integral_fiberIntegralCLM_smul volume volume _ _ _ F hg.continuousOn]
  simp_rw [hin]
  rw [← Real.fourierInv_eq (fun p : WithLp 2 (E × WithLp 2 (E × E)) ↦
      (ψ p.fst : ℂ) * (ρ p.snd : ℂ)), Real.fourierInv_eq_fourier_neg,
    Real.fourier_prod_mul (fun x ↦ (ψ x : ℂ)) (fun y ↦ (ρ y : ℂ)), Real.fourierInv_eq_fourier_neg,
    Real.fourierInv_eq_fourier_neg]
  simp

/-! ### The limit integral -/

/-- **The limit integral is the product integral.** Let `χ` be a real cutoff, one on the support
of a real test function `ψ`, over whose support `S` and `T` have no opposite covectors. Then
`ζ ↦ 𝓕⁻ ψ (ζ.1 + ζ.2) S (χ e_ζ.1) T (χ e_ζ.2)` is integrable on `WithLp 2 (E × E)`, and its integral
is `∫ S (χ e_η) T (ψ e_(-η)) dη`. -/
private theorem integrable_and_integral_fourierInv_mul_localFourier_mul_localFourier
    {ψ χ : 𝓓(Ω, ℝ)}
    (h : NoOppositeCovectorsOn S T (tsupport (postcompCLM (𝕜 := ℝ) ofRealCLM χ)))
    (hχψ : ∀ x ∈ tsupport ψ, χ x = 1) :
    Integrable (fun ζ : WithLp 2 (E × E) ↦ 𝓕⁻ (fun x ↦ (ψ x : ℂ)) (ζ.fst + ζ.snd) *
        (S.localFourier (postcompCLM (𝕜 := ℝ) ofRealCLM χ) ζ.fst *
          T.localFourier (postcompCLM (𝕜 := ℝ) ofRealCLM χ) ζ.snd)) ∧
      ∫ ζ : WithLp 2 (E × E), 𝓕⁻ (fun x ↦ (ψ x : ℂ)) (ζ.fst + ζ.snd) *
          (S.localFourier (postcompCLM (𝕜 := ℝ) ofRealCLM χ) ζ.fst *
            T.localFourier (postcompCLM (𝕜 := ℝ) ofRealCLM χ) ζ.snd) =
        ∫ η, S.localFourier (postcompCLM (𝕜 := ℝ) ofRealCLM χ) η *
          T.localFourier (postcompCLM (𝕜 := ℝ) ofRealCLM ψ) (-η) := by
  set χc : 𝓓(Ω, ℂ) := postcompCLM (𝕜 := ℝ) ofRealCLM χ
  set a : 𝓢(E, ℂ) := toSchwartzMapCLM ℝ (postcompCLM (𝕜 := ℝ) ofRealCLM ψ)
  set b : E → ℂ := 𝓕⁻ (fun x ↦ (ψ x : ℂ))
  set K : E × E → ℂ := fun q ↦ b (q.1 + q.2) * (S.localFourier χc q.1 * T.localFourier χc q.2)
  -- `K` is the integrable function of `NoOppositeCovectorsOn.integrable_mul_localFourier_mul_
  -- localFourier` after the measure preserving change of variables `(ζ, η) ↦ (ζ + η, ζ)`.
  have hK : Integrable K (volume.prod volume) := by
    have hH := h.integrable_mul_localFourier_mul_localFourier subset_rfl (𝓕⁻ a)
    rw [fourierInv_toSchwartzMapCLM_postcompCLM_ofRealCLM] at hH
    have hmp : MeasurePreserving (fun q : E × E ↦ (q.1 + q.2, q.1)) (volume.prod volume)
        (volume.prod volume) :=
      (Measure.measurePreserving_swap).comp (measurePreserving_prod_add volume volume)
    refine ((hmp.integrable_comp hH.aestronglyMeasurable).2 hH).congr
      (ae_of_all _ fun q ↦ ?_)
    simp [K, b]
  have hmpL := volume_preserving_symm_measurableEquiv_toLp_prod E E
  refine ⟨?_, ?_⟩
  · have hK' := (hmpL.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2
      (by rwa [Measure.volume_eq_prod])
    simpa [K, Function.comp_def] using hK'
  · rw [← hmpL.symm.integral_comp']
    simp only [MeasurableEquiv.symm_symm, MeasurableEquiv.coe_toLp, toLp_fst, toLp_snd]
    rw [Measure.volume_eq_prod, integral_prod K hK]
    refine integral_congr_ae (ae_of_all _ fun ζ ↦ ?_)
    -- Integrating first in `ζ.2`: `∫ 𝓕⁻ ψ (ζ.1 + ν) T (χ e_ν) dν = T (ψ e_(-ζ.1))`.
    have hinner : ∫ ν, b (ζ + ν) * T.localFourier χc ν = T.localFourier
        (postcompCLM (𝕜 := ℝ) ofRealCLM ψ) (-ζ) := by
      rw [← integral_fourierInv_mul_localFourier_add T χc a (φa := postcompCLM (𝕜 := ℝ)
        ofRealCLM ψ) (fun x ↦ ?_) (-ζ), fourierInv_toSchwartzMapCLM_postcompCLM_ofRealCLM,
        ← integral_add_left_eq_self (μ := volume)
          (fun ν ↦ 𝓕⁻ (fun x ↦ (ψ x : ℂ)) ν * T.localFourier χc (-ζ + ν)) ζ]
      · simp [b]
      · by_cases hx : x ∈ tsupport ψ
        · simp [a, χc, hχψ x hx]
        · simp [a, image_eq_zero_of_notMem_tsupport hx]
    simp only [K, ← hinner, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun ν ↦ ?_)
    ring

/-! ### The pullback along the diagonal near a point -/

/-- For normalized bumps `ρ_n` shrinking to `0`, the fibre integrals of `ψ ⊗ ρ_n` along
`(x, y) ↦ (x, x) + y` are eventually supported in the set of points both of whose coordinates lie
where a cutoff `χ`, equal to one near the support of `ψ`, is one. -/
private theorem eventually_forall_mem_tsupport_fiberIntegralCLM
    (hf : ContDiffOn ℝ ∞ (fun x : E ↦ toLp 2 (x, x)) Ω) {ψ χ : 𝓓(Ω, ℝ)}
    (hχ : ∀ᶠ x in 𝓝ˢ (tsupport ψ), χ x = 1) {σ : ℕ → ContDiffBump (0 : WithLp 2 (E × E))}
    (hσ : Tendsto (fun n ↦ (σ n).rOut) atTop (𝓝 0))
    {F : ℕ → 𝓓(addSndDomain hf.continuousOn W, ℝ)}
    (hF : ∀ n p, F n p = ψ p.fst * (σ n).normed volume p.snd) :
    ∀ᶠ n in atTop, ∀ z ∈ tsupport (fiberIntegralCLM volume volume
      (addSnd fun x : E ↦ toLp 2 (x, x)) (contDiffOn_addSnd hf) (mapsTo_addSnd _)
      (surjective_fderiv_addSnd _ (hf.differentiableOn (by simp))) (F n)),
        χ z.fst = 1 ∧ χ z.snd = 1 := by
  obtain ⟨N, hN, hψN, hχN⟩ := mem_nhdsSet_iff_exists.1 hχ
  obtain ⟨δ, hδ, hthick⟩ := ψ.hasCompactSupport.isCompact.exists_thickening_subset_open hN hψN
  filter_upwards [hσ.eventually (gt_mem_nhds hδ)] with n hn z hz
  obtain ⟨p, hp, rfl⟩ := tsupport_fiberIntegralCLM_subset volume volume _ _ _ (F n) hz
  -- A point of the support of `ψ ⊗ ρ_n` lies over the support of `ψ`, within `rOut` of `E × {0}`.
  have hpC : p.fst ∈ tsupport ψ ∧ ‖p.snd‖ ≤ (σ n).rOut := by
    refine closure_minimal (fun q hq ↦ ?_) ((isClosed_tsupport _).preimage
      (WithLp.continuous_fst _ _ _) |>.inter (isClosed_le
        (continuous_norm.comp (WithLp.continuous_snd _ _ _)) continuous_const)) hp
    rw [mem_support, hF] at hq
    refine ⟨subset_tsupport _ (left_ne_zero_of_mul hq), le_of_lt ?_⟩
    have hq' : q.snd ∈ support ((σ n).normed volume) := right_ne_zero_of_mul hq
    rw [(σ n).support_normed_eq] at hq'
    simpa using hq'
  have hmem (v : E) (hv : ‖v‖ ≤ ‖p.snd‖) : χ (p.fst + v) = 1 :=
    hχN (hthick (mem_thickening_iff.2 ⟨p.fst, hpC.1, by
      simpa using hv.trans_lt (hpC.2.trans_lt hn)⟩))
  simp only [addSnd_apply, WithLp.add_fst, WithLp.add_snd, toLp_fst, toLp_snd]
  exact ⟨hmem _ (WithLp.norm_fst_le _ p.snd), hmem _ (WithLp.norm_snd_le _ p.snd)⟩

/-- **The pullback along the diagonal, tested near a point.** Let `χ` be a real cutoff equal to one
near the support of a real test function `ψ`, over whose support `S` and `T` have no opposite
covectors, and such that `(x, y) ↦ χ x χ y` is a test function on `W`. Then the pullback of `S ⊗ T`
along the diagonal, at `ψ`, is `∫ S (χ e_η) T (ψ e_(-η)) dη`. -/
private theorem pullback_diagonal_apply_eq_integral (hST : ∀ x, NoOppositeCovectorsOn S T {x})
    (hΔ : MapsTo (fun x : E ↦ toLp 2 (x, x)) Ω W)
    {ψ χ : 𝓓(Ω, ℝ)}
    (h : NoOppositeCovectorsOn S T (tsupport (postcompCLM (𝕜 := ℝ) ofRealCLM χ)))
    (hχ : ∀ᶠ x in 𝓝ˢ (tsupport ψ), χ x = 1) {κ : 𝓓(W, ℂ)}
    (hκ : ∀ q, κ q = postcompCLM (𝕜 := ℝ) ofRealCLM χ q.fst *
      postcompCLM (𝕜 := ℝ) ofRealCLM χ q.snd) :
    (transportCLM (prodContinuousLinearEquiv 2 ℝ E E) hW
        (S.tensorProduct T hV.subset)).pullback (fun x : E ↦ toLp 2 (x, x))
        (contDiff_toLp_diag ℝ E).contDiffOn hΔ
        (adjoint_fderiv_diagonal_apply_ne_zero hV hW hST) ψ =
      ∫ η, S.localFourier (postcompCLM (𝕜 := ℝ) ofRealCLM χ) η *
        T.localFourier (postcompCLM (𝕜 := ℝ) ofRealCLM ψ) (-η) := by
  have hf : ContDiffOn ℝ ∞ (fun x : E ↦ toLp 2 (x, x)) Ω :=
    (contDiff_toLp_diag ℝ E).contDiffOn
  have hN := adjoint_fderiv_diagonal_apply_ne_zero hV hW hST
  set U := transportCLM (prodContinuousLinearEquiv 2 ℝ E E) hW (S.tensorProduct T hV.subset)
  set χc : 𝓓(Ω, ℂ) := postcompCLM (𝕜 := ℝ) ofRealCLM χ
  set G : WithLp 2 (E × E) → ℂ := fun ζ ↦ 𝓕⁻ (fun x ↦ (ψ x : ℂ)) (ζ.fst + ζ.snd) *
    (S.localFourier χc ζ.fst * T.localFourier χc ζ.snd)
  obtain ⟨hGint, hGeq⟩ := integrable_and_integral_fourierInv_mul_localFourier_mul_localFourier
    (S := S) (T := T) h fun x hx ↦ hχ.self_of_nhdsSet x hx
  -- Tensor products `ψ ⊗ ρ_n` with normalized bumps `ρ_n` shrinking to `0`.
  have hU := mapsTo_inl_addSndDomain hf.continuousOn hΔ
  obtain ⟨σ, F, hσ0, -, hF⟩ := exists_seq_tensor_mollifier hU ψ
  have hT := notMem_waveFrontSet_addSndPullback hf hN
  have h₁ := tendsto_pullbackInl (addSndPullback hf U) hU hT ψ (l := atTop)
    (ρ := fun n ↦ (σ n).normed volume) (r := fun n ↦ (σ n).rOut) (M := 1) (f := F)
    (Eventually.of_forall fun n ↦ by
      simp_rw [abs_of_nonneg ((σ n).nonneg_normed _), (σ n).integral_normed, le_refl])
    (by simp_rw [ContDiffBump.integral_normed, tendsto_const_nhds])
    (Eventually.of_forall fun n ↦ by
      simpa only [(σ n).support_normed_eq] using ball_subset_closedBall)
    hσ0 (Eventually.of_forall hF)
  rw [pullback_eq_pullbackInl hf hΔ hN rfl hT, ← hGeq]
  refine tendsto_nhds_unique h₁ ?_
  -- Eventually the bumps are so small that the fibre integrals are supported where `κ = 1`.
  have hev : ∀ᶠ n in atTop, addSndPullback hf U (F n) =
      ∫ ζ, G ζ * 𝓕⁻ (fun y ↦ ((σ n).normed volume y : ℂ)) ζ := by
    filter_upwards [eventually_forall_mem_tsupport_fiberIntegralCLM hf hχ hσ0 hF] with n hn
    rw [addSndPullback_apply, apply_eq_integral_fourierInv_mul_localFourier U (φ := κ)
      fun z hz ↦ ?_]
    · refine integral_congr_ae (ae_of_all _ fun ζ ↦ ?_)
      dsimp only
      rw [fourierInv_fiberIntegralCLM_addSnd_diagonal hf ψ (hF n),
        localFourier_transportCLM_tensorProduct S T hV hW hκ]
      simp only [G]
      ring
    · obtain ⟨h1, h2⟩ := hn z hz
      simp [hκ, χc, h1, h2]
  refine Tendsto.congr' (EventuallyEq.symm hev) ?_
  refine tendsto_integral_of_dominated_convergence (fun ζ ↦ ‖G ζ‖) (fun n ↦ ?_) hGint.norm
    (fun n ↦ ae_of_all _ fun ζ ↦ ?_) (ae_of_all _ fun ζ ↦ ?_)
  · exact hGint.aestronglyMeasurable.mul
      (((σ n).integrable_normed (μ := volume)).ofReal.continuous_fourierInv.aestronglyMeasurable)
  · rw [norm_mul, Real.fourierInv_eq_fourier_neg]
    exact mul_le_of_le_one_right (norm_nonneg _) ((σ n).norm_fourier_normed_le (-ζ))
  · have hlim := (ContDiffBump.tendsto_fourier_normed hσ0 (-ζ)).const_mul (G ζ)
    rw [mul_one] at hlim
    exact hlim.congr fun n ↦ by rw [Real.fourierInv_eq_fourier_neg]

/-! ### The product as a pullback -/

/-- **The product of distributions is the pullback of their tensor product along the diagonal**
(Hörmander I, Theorem 8.2.10). If at every point no covector of the wave front set of `S` is
opposite to a covector of the wave front set of `T`, then the tensor product `S ⊗ T`, moved to the
Euclidean product `WithLp 2 (E × E)`, has a pullback along the diagonal `x ↦ (x, x)`
(`Distribution.adjoint_fderiv_diagonal_apply_ne_zero`), and this pullback is the product `S T`. -/
theorem pullback_diagonal_transportCLM_tensorProduct_eq_product
    (h : ∀ x, NoOppositeCovectorsOn S T {x})
    (hΔ : MapsTo (fun x : E ↦ toLp 2 (x, x)) Ω W) :
    (transportCLM (prodContinuousLinearEquiv 2 ℝ E E) hW
        (S.tensorProduct T hV.subset)).pullback (fun x : E ↦ toLp 2 (x, x))
        (contDiff_toLp_diag ℝ E).contDiffOn hΔ
        (adjoint_fderiv_diagonal_apply_ne_zero hV hW h) =
      S.product T h := by
  refine (eq_product_iff h).2 fun x₀ hx₀ ↦ ?_
  obtain ⟨φ, hφ, U₀, hU₀, hxU₀, hφU₀, -⟩ := (eq_product_iff h).1 rfl x₀ hx₀
  -- Near `(x₀, x₀)`, products of cutoffs supported in `B₁` and `B₂` are test functions on `W`.
  obtain ⟨B₁, hB₁, B₂, hB₂, hprod⟩ := exists_nhds_prod_cutoff (Ω := Ω) (O := Ω) (hΔ hx₀)
  simp only [toLp_fst, toLp_snd] at hB₁ hB₂
  have hU' : IsOpen (U₀ ∩ interior (B₁ ∩ B₂)) := hU₀.inter isOpen_interior
  refine ⟨φ, hφ, U₀ ∩ interior (B₁ ∩ B₂), hU',
    ⟨hxU₀, mem_interior_iff_mem_nhds.2 (inter_mem hB₁ hB₂)⟩, hφU₀.mono inter_subset_left,
    fun ψ hψ ↦ ?_⟩
  -- A real cutoff `χ`, one near the support of `ψ` and supported where `φ = 1` and in `B₁ ∩ B₂`.
  obtain ⟨χ, -, hχψ, hχU⟩ := exists_cutoff_tsupport_subset ψ.hasCompactSupport.isCompact
    (hU'.inter Ω.isOpen) (subset_inter hψ ψ.tsupport_subset) inter_subset_right
  have hχc : tsupport (postcompCLM (𝕜 := ℝ) ofRealCLM χ) ⊆ tsupport χ :=
    tsupport_comp_subset (g := ofRealCLM) (by simp) χ
  have hχB (x : E) (hx : x ∈ tsupport (postcompCLM (𝕜 := ℝ) ofRealCLM χ)) : x ∈ B₁ ∩ B₂ :=
    interior_subset (hχU (hχc hx)).1.2
  obtain ⟨κ, hκ, -⟩ := hprod _ _ (fun x hx ↦ (hχB x hx).1) fun x hx ↦ (hχB x hx).2
  have hφχ (x : E) (hx : x ∈ tsupport χ) : φ x = 1 := hφU₀ (hχU hx).1.1
  rw [pullback_diagonal_apply_eq_integral hV hW h hΔ (hφ.mono fun x hx ↦ subset_tsupport _
      (by simp [hφχ x (hχc hx)] : φ x ≠ 0)) hχψ hκ,
    cutoffProduct_apply_eq_integral hφ hφχ fun x hx ↦ hχψ.self_of_nhdsSet x hx]

end Distribution
