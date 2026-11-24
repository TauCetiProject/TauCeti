/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.WaveFrontSet.Localization
import Mathlib.Analysis.LocallyConvex.Barrelled
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import TauCeti.Algebra.Module.ZLattice.Scaling
import TauCeti.Algebra.Module.ZLattice.Summable
import TauCeti.Analysis.Calculus.BumpFunction.Convolution
import TauCeti.Analysis.Distribution.TestFunction.Frechet
import TauCeti.Analysis.Distribution.TestFunction.LinearEquiv
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.Distribution.TestFunction.Prod
import TauCeti.Analysis.Fourier.Decay
import TauCeti.Analysis.Fourier.Mollifier
import TauCeti.Analysis.Fourier.Prod
import TauCeti.Analysis.Normed.Lp.ProdLp
import TauCeti.Analysis.Normed.Module.Cone

/-!
# Pulling a distribution back to `E × {0}`

Let `T` be a complex distribution on an open set `W` of the Euclidean product `WithLp 2 (E × D)` of
finite-dimensional real inner product spaces, and let `U` be an open set of `E` with
`U × {0} ⊆ W`. The inclusion `ι : x ↦ (x, 0)` has transpose `ιᵀ (ξ, η) = ξ`, so its normal set
consists of the covectors `((x, 0), (0, η))` with `η ≠ 0`, conormal to `E × {0}`. If none of them
over `U` lies in the wave front set of `T`, then `T` has a pullback `ι^* T` to `U`
(Hörmander I, Theorem 8.2.4): the distribution `Distribution.pullbackInl` with

`(ι^* T) ψ = lim T ((x, y) ↦ ψ x ρ y)`,

the limit being taken as `ρ` runs through smooth functions supported in balls about `0 ∈ D` of
radii tending to zero, with integrals tending to one and bounded integrals of `|ρ|`, for instance
smooth nonnegative functions of integral one (`Distribution.tendsto_pullbackInl`). The limit does
not depend on these functions. For a function `F` continuous on `W` which satisfies the hypothesis
on the wave front set, for instance a smooth one, the pullback is the restriction `x ↦ F (x, 0)`
(`Distribution.pullbackInl_ofFun`), and it is linear in `T`. Without the hypothesis
the limit need not exist: the surface measure `T = 1 ⊗ δ₀` of `E × {0}` has its conormal set as wave
front set, and `T (ψ ⊗ ρ) = (∫ ψ) ρ 0` is unbounded as `ρ` concentrates at `0` when `∫ ψ ≠ 0`.

Every injective linear map is such an inclusion after a linear change of coordinates. In
particular, after the change `(x, y) ↦ (x, y - x)` the diagonal of `E × E` becomes `E × {0}`, and
pulling back the tensor product `S ⊗ T` along it is how the product of two distributions with no
opposite wave front covectors over a common point is defined (Hörmander I, Theorem 8.2.10).

## Main declarations

* `Distribution.pullbackInl`: the pullback of `T` along `x ↦ (x, 0)`, under the hypothesis that no
  conormal covector of `E × {0}` over `U` lies in the wave front set of `T`.
* `Distribution.tendsto_pullbackInl`: its values are the limits of `T (ψ ⊗ ρ)` as `ρ` concentrates
  at `0`; `Distribution.exists_seq_tensor_mollifier` supplies such a sequence `ψ ⊗ ρ_n` of test
  functions.
* `Distribution.pullbackInl_ofFun`: for a continuous function satisfying the hypothesis it is the
  restriction to `E × {0}`.
* `Distribution.pullbackInl_add`, `Distribution.pullbackInl_smul`,
  `Distribution.pullbackInl_smul_of_ne_zero`, `Distribution.pullbackInl_zero`,
  `Distribution.pullbackInl_neg`, `Distribution.pullbackInl_sub`: linearity in `T`.

## Implementation notes

Fix a test function `ψ`, and a cutoff `χ` equal to one near `tsupport ψ × {0}`. Expanding
`ψ ⊗ ρ` in a Fourier series along a lattice adapted to `tsupport χ`
(`Distribution.hasSum_fourier_ofReal_mul_localFourier`) gives

`T (ψ ⊗ ρ) = ∑ m, c 𝓕 ψ (m.fst) 𝓕 ρ (m.snd) T (χ e_(-m))`.

As `ρ` concentrates at `0`, the factors `𝓕 ρ (m.snd)` stay bounded by `∫ |ρ|` and tend to one
(`Real.tendsto_fourier_of_support_subset`). The
hypothesis on the wave front set makes `T (χ e_(-m))` decay rapidly on a cone around the conormal
directions `{0} × D`, while off that cone `‖m‖` is comparable to `‖m.fst‖`, where `𝓕 ψ` decays
rapidly. So the summands are dominated by a summable sequence, and by dominated convergence
`T (ψ ⊗ ρ)` tends to the lattice sum without the factors `𝓕 ρ (m.snd)`.

For the test functions supported in a fixed compact set `K`, the maps `ψ ↦ T (ψ ⊗ ρ_n)` for a
sequence of bumps `ρ_n` are continuous linear maps on the Fréchet space `𝓓_K`, so their pointwise
limit is continuous by the Banach–Steinhaus theorem (`continuousLinearMapOfTendsto`), and
`TestFunction.limitCLM` assembles these limits into a distribution on `U`.

For a continuous function `F`, Fubini's theorem writes `∫ (ψ ⊗ ρ_n) F` as the convolution
`(ρ_n ⋆ g) (0)` of the function `g y = ∫ ψ (x) F (x, -y) dx`, which is continuous near `0`, so it
tends to `g 0 = ∫ ψ (x) F (x, 0) dx` (`ContDiffBump.tendsto_integral_shrinking_normed_smul`).

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, Theorem 8.2.4 (pullback of distributions whose wave front set avoids the normal
  set) and Theorem 8.2.10 (products of distributions).
* C. Brouder, N. V. Dang, F. Hélein, *Continuity of the fundamental operations on distributions
  having a specified wave front set*, arXiv:1409.7662v2, Proposition 5.1.
-/

public section

noncomputable section

open Complex Filter Function Metric Set TopologicalSpace TestFunction MeasureTheory WithLp
open scoped Distributions Topology FourierTransform RealInnerProductSpace ContDiff Real

namespace Distribution

variable {E D : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D]
  {U : Opens E} {W : Opens (WithLp 2 (E × D))}

/-! ### Neighbourhoods of `E × {0}` and decay in the conormal directions -/

/-- **Decay in the conormal directions.** If no covector `((x, 0), (0, η))` with `x ∈ K` and
`η ≠ 0` lies in the wave front set of `T`, there are an open set `G` containing `K × {0}` and a
constant `c > 0` such that every cutoff supported in `G` has localized Fourier transform rapidly
decreasing on the cone `‖ζ.fst‖ < c ‖ζ.snd‖` around the conormal directions `{0} × D`. -/
private theorem exists_isOpen_forall_decay (T : 𝓓'(W, ℂ)) {K : Set E} (hK : IsCompact K)
    (hKW : ∀ x ∈ K, toLp 2 (x, (0 : D)) ∈ W)
    (h : ∀ x ∈ K, ∀ η : D, η ≠ 0 → (toLp 2 (x, (0 : D)), toLp 2 ((0 : E), η)) ∉ T.waveFrontSet) :
    ∃ G : Set (WithLp 2 (E × D)), IsOpen G ∧ (∀ x ∈ K, toLp 2 (x, (0 : D)) ∈ G) ∧
      ∃ c > 0, ∀ χ : 𝓓(W, ℂ), tsupport χ ⊆ G → ∀ N : ℕ, ∃ C, ∀ ζ : WithLp 2 (E × D),
        ‖ζ.fst‖ < c * ‖ζ.snd‖ → (1 + ‖ζ‖) ^ N * ‖T.localFourier χ ζ‖ ≤ C := by
  classical
  set ι₁ : E → WithLp 2 (E × D) := fun x ↦ toLp 2 (x, 0)
  set ι₂ : D → WithLp 2 (E × D) := fun b ↦ toLp 2 (0, b)
  have hι₁ : Continuous ι₁ := (prodContinuousLinearEquiv 2 ℝ E D).symm.continuous.comp
    (continuous_id.prodMk continuous_const)
  have hι₂ : Continuous ι₂ := (prodContinuousLinearEquiv 2 ℝ E D).symm.continuous.comp
    (continuous_const.prodMk continuous_id)
  have hι₂smul (t : ℝ) (b : D) : ι₂ (t • b) = t • ι₂ b := by
    simp only [ι₂, ← toLp_smul, Prod.smul_mk, smul_zero]
  -- The hypothesis is microlocal smoothness at the conormal covectors over `K`.
  have hsmooth (η : sphere (0 : D) 1) : ∀ p ∈ ι₁ '' K, T.IsMicrolocallySmoothAt p (ι₂ η) := by
    rintro _ ⟨x, hx, rfl⟩
    by_contra hns
    have hη : ι₂ η ≠ 0 := fun h0 ↦ ne_zero_of_mem_unit_sphere η (by
      simpa [ι₂] using congrArg WithLp.snd h0)
    exact h x hx η (ne_zero_of_mem_unit_sphere η) (mem_waveFrontSet_iff.2 ⟨hKW x hx, hη, hns⟩)
  choose G' hG' hKG' Γ hΓ hηΓ hcone hdecay using fun η : sphere (0 : D) 1 ↦
    exists_isOpen_cone_forall_decay_of_isCompact (hK.image hι₁) (hsmooth η)
  -- Finitely many of the cones cover the conormal directions.
  obtain ⟨t, ht⟩ := TauCeti.exists_finset_compl_singleton_subset_biUnion (E := D)
    (Γ := fun η ↦ ι₂ ⁻¹' Γ η) (fun η ↦ (hΓ η).preimage hι₂) (fun η ↦ hηΓ η)
    fun η s hs b hb ↦ by simpa [Set.mem_preimage, hι₂smul] using hcone η s hs _ hb
  obtain ⟨c, hc, hcΓ⟩ := ((isOpen_biUnion fun η _ ↦ hΓ η).preimage
    (prod_continuous_toLp 2 E D)).exists_pos_setOf_norm_fst_lt_subset
    (fun s hs q hq ↦ by
      obtain ⟨η, hηt, hqη⟩ := mem_iUnion₂.1 hq
      exact mem_iUnion₂.2 ⟨η, hηt, by simpa using hcone η s hs _ hqη⟩)
    fun b hb ↦ by
      obtain ⟨η, hηt, hbη⟩ := mem_iUnion₂.1 (ht hb)
      exact mem_iUnion₂.2 ⟨η, hηt, hbη⟩
  refine ⟨⋂ η ∈ t, G' η, isOpen_biInter_finset fun η _ ↦ hG' η,
    fun x hx ↦ mem_iInter₂.2 fun η _ ↦ hKG' η (mem_image_of_mem _ hx), c, hc,
    fun χ hχ N ↦ ?_⟩
  have hpiece (η : sphere (0 : D) 1) (hη : η ∈ t) :
      ∃ C, ∀ ζ ∈ Γ η, (1 + ‖ζ‖) ^ N * ‖T.localFourier χ ζ‖ ≤ C :=
    hdecay η χ ((hχ.trans (biInter_subset_of_mem hη)).trans subset_union_left) N
  choose! C hC using hpiece
  refine ⟨∑ η ∈ t, |C η|, fun ζ hζ ↦ ?_⟩
  have hζ' := hcΓ (a := ofLp ζ) (by simpa using hζ)
  rw [mem_preimage, toLp_ofLp] at hζ'
  obtain ⟨η, hηt, hζΓ⟩ := mem_iUnion₂.1 hζ'
  calc (1 + ‖ζ‖) ^ N * ‖T.localFourier χ ζ‖ ≤ C η := hC η hηt ζ hζΓ
    _ ≤ |C η| := le_abs_self _
    _ ≤ ∑ η ∈ t, |C η| :=
      Finset.single_le_sum (f := fun η ↦ |C η|) (fun _ _ ↦ abs_nonneg _) hηt

/-! ### The limit of `T (ψ ⊗ ρ)` as `ρ` concentrates at `0` -/

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ D] in
/-- If `g` decays rapidly and the localized Fourier transform of `T` with cutoff `χ` decays rapidly
on the cone `‖ζ.fst‖ < c ‖ζ.snd‖`, then `ζ ↦ g ζ.fst * T (χ e_(-ζ))` decays rapidly: off the cone
`‖ζ‖` is comparable to `‖ζ.fst‖`, and the localized Fourier transform grows at most polynomially. -/
private theorem exists_decay_mul_localFourier_neg (T : 𝓓'(W, ℂ)) {χ : 𝓓(W, ℂ)} {c : ℝ}
    (hc : 0 < c) (hdecay : ∀ N : ℕ, ∃ C, ∀ ζ : WithLp 2 (E × D),
      ‖ζ.fst‖ < c * ‖ζ.snd‖ → (1 + ‖ζ‖) ^ N * ‖T.localFourier χ ζ‖ ≤ C)
    {g : E → ℂ} (hg : ∀ N : ℕ, ∃ C, ∀ a, (1 + ‖a‖) ^ N * ‖g a‖ ≤ C) (N : ℕ) :
    ∃ C, ∀ ζ : WithLp 2 (E × D), (1 + ‖ζ‖) ^ N * ‖g ζ.fst * T.localFourier χ (-ζ)‖ ≤ C := by
  obtain ⟨C₀, k, hC₀⟩ := exists_norm_localFourier_le T χ
  have hC₀' : 0 ≤ C₀ := by simpa using (norm_nonneg _).trans (hC₀ 0)
  obtain ⟨C₁, hC₁⟩ := hdecay N
  obtain ⟨C₂, hC₂⟩ := hg 0
  obtain ⟨C₃, hC₃⟩ := hg (N + k)
  have hC₂' (a : E) : ‖g a‖ ≤ C₂ := by simpa using hC₂ a
  set A := 1 + c⁻¹
  have hA : 1 ≤ A := le_add_of_nonneg_right (inv_nonneg.2 hc.le)
  refine ⟨max (C₂ * C₁) (C₀ * A ^ (N + k) * C₃), fun ζ ↦ ?_⟩
  rw [norm_mul, mul_left_comm]
  by_cases hζ : ‖ζ.fst‖ < c * ‖ζ.snd‖
  · -- On the cone, the localized Fourier transform decays.
    have h := hC₁ (-ζ) (by simpa using hζ)
    rw [norm_neg] at h
    exact (mul_le_mul (hC₂' _) h (by positivity) ((norm_nonneg _).trans (hC₂' 0))).trans
      (le_max_left _ _)
  · -- Off the cone, `1 + ‖ζ‖ ≤ A (1 + ‖ζ.fst‖)`.
    have hsnd : ‖ζ.snd‖ ≤ c⁻¹ * ‖ζ.fst‖ := by
      rw [le_inv_mul_iff₀ hc]
      exact not_lt.1 hζ
    have hle : 1 + ‖ζ‖ ≤ A * (1 + ‖ζ.fst‖) := by
      have := prod_norm_le_norm_fst_add_norm_snd ζ
      nlinarith [norm_nonneg ζ.fst]
    calc ‖g ζ.fst‖ * ((1 + ‖ζ‖) ^ N * ‖T.localFourier χ (-ζ)‖)
        ≤ ‖g ζ.fst‖ * ((1 + ‖ζ‖) ^ N * (C₀ * (1 + ‖ζ‖) ^ k)) := by
          gcongr
          simpa using hC₀ (-ζ)
      _ = C₀ * ((1 + ‖ζ‖) ^ (N + k) * ‖g ζ.fst‖) := by ring
      _ ≤ C₀ * ((A * (1 + ‖ζ.fst‖)) ^ (N + k) * ‖g ζ.fst‖) := by gcongr
      _ = C₀ * A ^ (N + k) * ((1 + ‖ζ.fst‖) ^ (N + k) * ‖g ζ.fst‖) := by rw [mul_pow]; ring
      _ ≤ C₀ * A ^ (N + k) * C₃ := by gcongr; exact hC₃ _
      _ ≤ _ := le_max_right _ _

/-- **The core convergence.** Let `χ = 1` on `tsupport ψ × closedBall 0 δ`, let the localized
Fourier transform of `T` with cutoff `χ` decay rapidly on a cone `‖ζ.fst‖ < c ‖ζ.snd‖`, and let
`L` be a lattice separating `tsupport χ` from its translates. If test functions `f i` are
`ψ ⊗ ρ i` for functions `ρ i` with `∫ |ρ i| ≤ M` and `∫ ρ i → 1`, supported in balls of radii
`r i → 0`, then `T (f i)` converges to the lattice sum
`∑ m, (covolume L)⁻¹ 𝓕 ψ (m.fst) T (χ e_(-m))`. -/
private theorem tendsto_apply_tsum [MeasurableSpace E] [BorelSpace E] [MeasurableSpace D]
    [BorelSpace D] (T : 𝓓'(W, ℂ)) {ψ : 𝓓(U, ℝ)} {χ : 𝓓(W, ℂ)}
    {δ : ℝ} (hδ : 0 < δ) (hχ : ∀ x ∈ tsupport ψ, ∀ y : D, ‖y‖ ≤ δ → χ (toLp 2 (x, y)) = 1)
    (L : Submodule ℤ (WithLp 2 (E × D))) [DiscreteTopology L] [IsZLattice ℝ L]
    (hL : ∀ p ∈ tsupport χ, ∀ ℓ ∈ L, p + ℓ ∈ tsupport χ → ℓ = 0) {c : ℝ} (hc : 0 < c)
    (hdecay : ∀ N : ℕ, ∃ C, ∀ ζ : WithLp 2 (E × D),
      ‖ζ.fst‖ < c * ‖ζ.snd‖ → (1 + ‖ζ‖) ^ N * ‖T.localFourier χ ζ‖ ≤ C)
    {ι : Type*} {l : Filter ι} {ρ : ι → D → ℝ} {r : ι → ℝ} {M : ℝ} {f : ι → 𝓓(W, ℝ)}
    (hρM : ∀ᶠ i in l, ∫ y, |ρ i y| ≤ M) (hρ1 : Tendsto (fun i ↦ ∫ y, ρ i y) l (𝓝 1))
    (hρr : ∀ᶠ i in l, support (ρ i) ⊆ closedBall 0 (r i)) (hr : Tendsto r l (𝓝 0))
    (hf : ∀ᶠ i in l, ∀ p, f i p = ψ p.fst * ρ i p.snd) :
    Tendsto (fun i ↦ T (f i)) l (𝓝 (∑' m : ZLattice.dual L, (ZLattice.covolume L : ℂ)⁻¹ *
      𝓕 (fun x ↦ (ψ x : ℂ)) (m : WithLp 2 (E × D)).fst * T.localFourier χ (-m))) := by
  set a : ℂ := (ZLattice.covolume L : ℂ)⁻¹
  set Ψ : E → ℂ := 𝓕 fun x ↦ (ψ x : ℂ)
  -- The limiting summands decay rapidly, hence are summable over the dual lattice.
  have hsum : Summable fun m : ZLattice.dual L ↦ ‖a * Ψ (m : WithLp 2 (E × D)).fst *
      T.localFourier χ (-m)‖ := by
    have h := ZLattice.summable_one_add_norm_pow_mul_norm_of_decay (ZLattice.dual L)
      (f := fun ζ : WithLp 2 (E × D) ↦ a * (Ψ ζ.fst * T.localFourier χ (-ζ))) (fun N ↦ by
        obtain ⟨C, hC⟩ := exists_decay_mul_localFourier_neg T hc hdecay
          (fun N ↦ TauCeti.exists_one_add_norm_pow_mul_norm_fourier_le
            (ofRealCLM.contDiff.comp ψ.contDiff)
            (ψ.hasCompactSupport.comp_left (g := ((↑) : ℝ → ℂ)) ofReal_zero) N) N
        exact ⟨‖a‖ * C, fun ζ ↦ by
          rw [norm_mul, mul_left_comm]
          exact mul_le_mul_of_nonneg_left (hC ζ) (norm_nonneg _)⟩) 0
    simpa [mul_assoc] using h
  -- Eventually `T (f i)` is the lattice sum with the extra factor `𝓕 (ρ i) (m.snd)`.
  have heq : ∀ᶠ i in l, ∑' m : ZLattice.dual L, a * Ψ (m : WithLp 2 (E × D)).fst *
      𝓕 (fun y ↦ (ρ i y : ℂ)) (m : WithLp 2 (E × D)).snd * T.localFourier χ (-m) = T (f i) := by
    filter_upwards [hρr, hf, hr.eventually (gt_mem_nhds hδ)] with i hri hfi hrδ
    have hfun : (fun p ↦ (f i p : ℂ)) = fun p : WithLp 2 (E × D) ↦
        (ψ p.fst : ℂ) * (ρ i p.snd : ℂ) := funext fun p ↦ by simp [hfi]
    refine ((hasSum_fourier_ofReal_mul_localFourier T χ L hL (φ := f i)
      fun p hp ↦ ?_).congr_fun fun m ↦ ?_).tsum_eq
    · have hp' : ψ p.fst ≠ 0 ∧ ρ i p.snd ≠ 0 := by simpa [hfi] using hp
      have hy : ‖p.snd‖ ≤ δ := by
        have := hri hp'.2
        rw [mem_closedBall, dist_zero_right] at this
        linarith
      have h := hχ p.fst (subset_tsupport _ hp'.1) p.snd hy
      rwa [← ofLp_fst, ← ofLp_snd, Prod.mk.eta, toLp_ofLp] at h
    · rw [hfun, Real.fourier_prod_mul (fun x ↦ (ψ x : ℂ)) (fun y ↦ (ρ i y : ℂ)), mul_assoc a]
  -- The factors `𝓕 (ρ i) (m.snd)` are bounded by `M` and tend to one.
  have hlim (b : D) : Tendsto (fun i ↦ 𝓕 (fun y ↦ (ρ i y : ℂ)) b) l (𝓝 1) :=
    Real.tendsto_fourier_of_support_subset (hρr.mono fun i hi y hy ↦ hi (by simpa using hy)) hr
      (hρM.mono fun i hi ↦ by simpa only [Complex.norm_real, Real.norm_eq_abs] using hi)
      (by simpa only [integral_complex_ofReal, ofReal_one, Function.comp_def] using
        (Complex.continuous_ofReal.tendsto 1).comp hρ1) b
  refine Tendsto.congr' heq ?_
  refine tendsto_tsum_of_dominated_convergence (hsum.mul_right M) (fun m ↦ ?_) ?_
  · simpa using ((hlim _).const_mul (a * Ψ (m : WithLp 2 (E × D)).fst)).mul_const
      (T.localFourier χ (-m))
  · filter_upwards [hρM] with i hi m
    have h : ‖𝓕 (fun y ↦ (ρ i y : ℂ)) (m : WithLp 2 (E × D)).snd‖ ≤ M :=
      (Real.norm_fourier_le_integral_norm _ _).trans
        (by simpa only [Complex.norm_real, Real.norm_eq_abs] using hi)
    simp only [norm_mul]
    nlinarith [mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤
      ‖a‖ * ‖Ψ (m : WithLp 2 (E × D)).fst‖ * ‖T.localFourier χ (-m)‖)]

/-- Around `K × {0}`, for a compact set `K` over which `T` has no conormal wave front covectors,
there is a cutoff `χ` equal to one on `K × closedBall 0 δ` whose localized Fourier transform
decays rapidly on a cone `‖ζ.fst‖ < c ‖ζ.snd‖`. -/
private theorem exists_cutoff_decay (T : 𝓓'(W, ℂ)) {K : Set E} (hK : IsCompact K)
    (hKW : ∀ x ∈ K, toLp 2 (x, (0 : D)) ∈ W)
    (h : ∀ x ∈ K, ∀ η : D, η ≠ 0 → (toLp 2 (x, (0 : D)), toLp 2 ((0 : E), η)) ∉ T.waveFrontSet) :
    ∃ δ > 0, ∃ χ : 𝓓(W, ℂ), (∀ x ∈ K, ∀ y : D, ‖y‖ ≤ δ → χ (toLp 2 (x, y)) = 1) ∧
      ∃ c > 0, ∀ N : ℕ, ∃ C, ∀ ζ : WithLp 2 (E × D),
        ‖ζ.fst‖ < c * ‖ζ.snd‖ → (1 + ‖ζ‖) ^ N * ‖T.localFourier χ ζ‖ ≤ C := by
  obtain ⟨G, hG, hKG, c, hc, hdecay⟩ := exists_isOpen_forall_decay T hK hKW h
  obtain ⟨δ, hδ, htube⟩ :=
    hK.exists_pos_forall_toLp_mem (hG.inter W.isOpen) fun x hx ↦ ⟨hKG x hx, hKW x hx⟩
  -- A real cutoff equal to one near `K × closedBall 0 (δ / 2)`, supported in `G ∩ W`.
  set B : Set (WithLp 2 (E × D)) := toLp 2 '' (K ×ˢ closedBall (0 : D) (δ / 2))
  have hB : IsCompact B := (hK.prod (isCompact_closedBall _ _)).image (prod_continuous_toLp 2 E D)
  have hBG : B ⊆ G ∩ W := by
    rintro _ ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩
    refine htube x hx x y (by simpa using hδ) ?_
    rw [mem_closedBall, dist_zero_right] at hy
    linarith
  obtain ⟨χ, -, hχ1, hχG⟩ := exists_cutoff_tsupport_subset (Ω := W) (n := ⊤) hB
    (hG.inter W.isOpen) hBG inter_subset_right
  refine ⟨δ / 2, half_pos hδ, postcompCLM (𝕜 := ℝ) ofRealCLM χ, fun x hx y hy ↦ ?_, c, hc,
    fun N ↦ hdecay _ ?_ N⟩
  · have h1 : χ (toLp 2 (x, y)) = 1 :=
      hχ1.self_of_nhdsSet _ ⟨(x, y), ⟨hx, by simpa using hy⟩, rfl⟩
    simp [h1]
  · rw [postcompCLM_apply]
    exact (tsupport_comp_subset (map_zero ofRealCLM) χ).trans (hχG.trans inter_subset_left)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [InnerProductSpace ℝ D]
  [FiniteDimensional ℝ D] in
/-- The radius of a tube around `K × {0}` inside `W`. -/
private def tubeRadius (hU : MapsTo (fun x ↦ toLp 2 (x, (0 : D))) (U : Set E) W) (K : Compacts E)
    (hK : (K : Set E) ⊆ U) : ℝ :=
  (K.isCompact.exists_pos_forall_toLp_mem W.isOpen fun _ hx ↦ hU (hK hx)).choose

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [InnerProductSpace ℝ D]
  [FiniteDimensional ℝ D] in
private theorem tubeRadius_pos (hU : MapsTo (fun x ↦ toLp 2 (x, (0 : D))) (U : Set E) W)
    (K : Compacts E) (hK : (K : Set E) ⊆ U) : 0 < tubeRadius hU K hK :=
  (K.isCompact.exists_pos_forall_toLp_mem W.isOpen fun _ hx ↦ hU (hK hx)).choose_spec.1

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [InnerProductSpace ℝ D]
  [FiniteDimensional ℝ D] in
/-- The tube of radius `tubeRadius` around `K × {0}` lies in `W`. -/
private theorem toLp_mem_of_lt_tubeRadius
    (hU : MapsTo (fun x ↦ toLp 2 (x, (0 : D))) (U : Set E) W) (K : Compacts E)
    (hK : (K : Set E) ⊆ U) {x x' : E} (hx : x ∈ (K : Set E)) {y : D}
    (hx' : dist x' x < tubeRadius hU K hK) (hy : ‖y‖ < tubeRadius hU K hK) :
    toLp 2 (x', y) ∈ W :=
  (K.isCompact.exists_pos_forall_toLp_mem W.isOpen fun _ hx ↦ hU (hK hx)).choose_spec.2
    x hx x' y hx' hy

/-- The normalized bump `ρ_n` of the shrinking sequence `ContDiffBump.shrinking (δ / 2)`, of
integral one and supported in the closed ball of radius `δ / (2 (n + 1))`, as a test function on
the open ball of radius `δ`. It is normalized for the Lebesgue measure of the Borel σ-algebra. -/
private def mollifier {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    𝓓((⟨ball (0 : D) δ, isOpen_ball⟩ : Opens D), ℝ) :=
  letI : MeasurableSpace D := borel D
  haveI : BorelSpace D := ⟨rfl⟩
  { toFun := (ContDiffBump.shrinking (c := (0 : D)) (half_pos hδ) n).normed volume
    contDiff' := (ContDiffBump.shrinking (half_pos hδ) n).contDiff_normed
    hasCompactSupport' := (ContDiffBump.shrinking (half_pos hδ) n).hasCompactSupport_normed
    tsupport_subset' := by
      rw [ContDiffBump.tsupport_normed_eq, ContDiffBump.rOut_shrinking]
      refine closedBall_subset_ball ((div_le_self (half_pos hδ).le ?_).trans_lt (half_lt_self hδ))
      linarith [n.cast_nonneg (α := ℝ)] }

private theorem mollifier_apply [MeasurableSpace D] [BorelSpace D] {δ : ℝ} (hδ : 0 < δ) (n : ℕ)
    (y : D) :
    mollifier hδ n y = (ContDiffBump.shrinking (c := (0 : D)) (half_pos hδ) n).normed volume y := by
  -- `mollifier` is built with the instance `borel D`. Once the ambient instance is replaced by
  -- `borel D`, both sides use the same `volume`, as the `BorelSpace` proofs are propositions.
  obtain rfl := BorelSpace.measurable_eq (α := D)
  rfl

/-- The mollified tensor products `φ ↦ ((x, y) ↦ φ x ρ_n y)` of the test functions supported in a
compact `K ⊆ U`, as continuous linear maps into the test functions on `W`. -/
private def tensorCLM (hU : MapsTo (fun x ↦ toLp 2 (x, (0 : D))) (U : Set E) W) (K : Compacts E)
    (hK : (K : Set E) ⊆ U) (n : ℕ) : 𝓓_{K}(E, ℝ) →L[ℝ] 𝓓(W, ℝ) :=
  let δ := tubeRadius hU K hK
  let Ω : Opens E := ⟨thickening δ K, isOpen_thickening⟩
  let O : Opens D := ⟨ball 0 δ, isOpen_ball⟩
  let V : Opens (E × D) := ⟨(Ω : Set E) ×ˢ (O : Set D), Ω.isOpen.prod O.isOpen⟩
  have hKΩ : (K : Set E) ⊆ Ω := self_subset_thickening (tubeRadius_pos hU K hK) _
  have hVW : MapsTo (prodContinuousLinearEquiv 2 ℝ E D).symm (V : Set (E × D)) W := by
    rintro ⟨x', y⟩ ⟨hx', hy⟩
    obtain ⟨x, hx, hxx'⟩ := mem_thickening_iff.1 hx'
    exact toLp_mem_of_lt_tubeRadius hU K hK hx hxx' (by simpa [O, δ] using hy)
  (prodContinuousLinearEquiv 2 ℝ E D).symm.transportTestFunction hVW ∘L
    (prodSMulCLM (F := ℝ) (mollifier (tubeRadius_pos hU K hK) n) (V := V) subset_rfl ∘L
      ofSupportedInCLM ℝ hKΩ)

omit [FiniteDimensional ℝ E] in
/-- The values `(φ ⊗ ρ_n) (x, y) = φ x ρ_n y` of the mollified tensor products. -/
private theorem tensorCLM_apply [MeasurableSpace D] [BorelSpace D]
    (hU : MapsTo (fun x ↦ toLp 2 (x, (0 : D))) (U : Set E) W)
    (K : Compacts E) (hK : (K : Set E) ⊆ U) (n : ℕ) (φ : 𝓓_{K}(E, ℝ)) (p : WithLp 2 (E × D)) :
    tensorCLM hU K hK n φ p = φ p.fst *
      (ContDiffBump.shrinking (c := (0 : D)) (half_pos (tubeRadius_pos hU K hK)) n).normed
        volume p.snd := by
  simp only [tensorCLM, ContinuousLinearMap.comp_apply]
  -- `erw`: the two evaluation lemmas match only after unfolding the instances on the product
  -- spaces that `tensorCLM` builds its open sets in.
  erw [ContinuousLinearEquiv.transportTestFunction_apply, prodSMulCLM_apply]
  simp [mollifier_apply, mul_comm]

omit [FiniteDimensional ℝ E] in
/-- The normalized bumps `ρ_n` of `ContDiffBump.shrinking R` have `∫ |ρ_n| = 1` and `∫ ρ_n = 1`,
and are supported in the closed balls of radii `R / (n + 1) → 0`. -/
private theorem shrinking_normed_properties [MeasurableSpace D] [BorelSpace D] {R : ℝ}
    (hR : 0 < R) :
    (∀ᶠ n in atTop, ∫ y, |(ContDiffBump.shrinking (c := (0 : D)) hR n).normed volume y| ≤ 1) ∧
      Tendsto (fun n ↦ ∫ y, (ContDiffBump.shrinking (c := (0 : D)) hR n).normed volume y) atTop
        (𝓝 1) ∧
      (∀ᶠ n in atTop, support ((ContDiffBump.shrinking (c := (0 : D)) hR n).normed volume) ⊆
        closedBall 0 (ContDiffBump.shrinking (c := (0 : D)) hR n).rOut) ∧
      Tendsto (fun n ↦ (ContDiffBump.shrinking (c := (0 : D)) hR n).rOut) atTop (𝓝 0) :=
  ⟨Eventually.of_forall fun n ↦ by
      simp_rw [abs_of_nonneg ((ContDiffBump.shrinking hR n).nonneg_normed _),
        (ContDiffBump.shrinking hR n).integral_normed, le_rfl],
    tendsto_const_nhds.congr fun n ↦ (ContDiffBump.shrinking hR n).integral_normed.symm,
    Eventually.of_forall fun n ↦ by
      rw [(ContDiffBump.shrinking hR n).support_normed_eq]
      exact ball_subset_closedBall,
    ContDiffBump.tendsto_rOut_shrinking hR⟩

/-- The candidate value of the pullback at `ψ`: the limit of `T (ψ ⊗ ρ_n)` for the normalized
bumps `ρ_n`. -/
private def pullbackInlValue (T : 𝓓'(W, ℂ))
    (hU : MapsTo (fun x ↦ toLp 2 (x, (0 : D))) (U : Set E) W) (ψ : 𝓓(U, ℝ)) : ℂ :=
  limUnder atTop fun n ↦ T (tensorCLM hU ⟨tsupport ψ, ψ.hasCompactSupport⟩ ψ.tsupport_subset n
    (ContDiffMapSupportedIn.of_support_subset ψ.contDiff (subset_tsupport _)))

/-- `T (ψ ⊗ ρ i)` converges to the candidate value for every family of functions `ρ i` with
bounded `∫ |ρ i|` and `∫ ρ i → 1`, supported in balls of radii tending to zero. -/
private theorem tendsto_pullbackInlValue [MeasurableSpace D] [BorelSpace D] (T : 𝓓'(W, ℂ))
    (hU : MapsTo (fun x ↦ toLp 2 (x, (0 : D))) (U : Set E) W)
    (h : ∀ x ∈ U, ∀ η : D, η ≠ 0 →
      (toLp 2 (x, (0 : D)), toLp 2 ((0 : E), η)) ∉ T.waveFrontSet) (ψ : 𝓓(U, ℝ))
    {ι : Type*} {l : Filter ι} {ρ : ι → D → ℝ} {r : ι → ℝ} {M : ℝ} {f : ι → 𝓓(W, ℝ)}
    (hρM : ∀ᶠ i in l, ∫ y, |ρ i y| ≤ M) (hρ1 : Tendsto (fun i ↦ ∫ y, ρ i y) l (𝓝 1))
    (hρr : ∀ᶠ i in l, support (ρ i) ⊆ closedBall 0 (r i)) (hr : Tendsto r l (𝓝 0))
    (hf : ∀ᶠ i in l, ∀ p, f i p = ψ p.fst * ρ i p.snd) :
    Tendsto (fun i ↦ T (f i)) l (𝓝 (pullbackInlValue T hU ψ)) := by
  borelize E
  obtain ⟨δ, hδ, χ, hχ, c, hc, hdecay⟩ := exists_cutoff_decay T ψ.hasCompactSupport.isCompact
    (fun x hx ↦ hU (ψ.tsupport_subset hx)) fun x hx ↦ h x (ψ.tsupport_subset hx)
  obtain ⟨L, _, _, hL⟩ :=
    ZLattice.exists_forall_add_mem_eq_zero_of_isBounded χ.hasCompactSupport.isCompact.isBounded
  -- Both the given family and the normalized bumps converge to the same lattice sum.
  have hK := tubeRadius_pos hU ⟨tsupport ψ, ψ.hasCompactSupport⟩ ψ.tsupport_subset
  obtain ⟨hM, h1, hsupp, hlim⟩ := shrinking_normed_properties (D := D) (half_pos hK)
  have hcan := tendsto_apply_tsum T hδ hχ L hL hc hdecay hM h1 hsupp hlim
    (f := fun n ↦ tensorCLM hU ⟨tsupport ψ, ψ.hasCompactSupport⟩ ψ.tsupport_subset n
      (ContDiffMapSupportedIn.of_support_subset ψ.contDiff (subset_tsupport _)))
    (Eventually.of_forall fun n p ↦ by
      rw [tensorCLM_apply, ContDiffMapSupportedIn.coe_of_support_subset])
  rw [pullbackInlValue, hcan.limUnder_eq]
  exact tendsto_apply_tsum T hδ hχ L hL hc hdecay hρM hρ1 hρr hr hf

/-- `T (φ ⊗ ρ_n)` tends to the candidate value at `φ` for the normalized bumps `ρ_n`. -/
private theorem tendsto_apply_tensorCLM (T : 𝓓'(W, ℂ))
    (hU : MapsTo (fun x ↦ toLp 2 (x, (0 : D))) (U : Set E) W)
    (h : ∀ x ∈ U, ∀ η : D, η ≠ 0 →
      (toLp 2 (x, (0 : D)), toLp 2 ((0 : E), η)) ∉ T.waveFrontSet) (K : Compacts E)
    (hK : (K : Set E) ⊆ U) (φ : 𝓓_{K}(E, ℝ)) :
    Tendsto (fun n ↦ T (tensorCLM hU K hK n φ)) atTop
      (𝓝 (pullbackInlValue T hU (ofSupportedIn hK φ))) := by
  borelize D
  obtain ⟨hM, h1, hsupp, hlim⟩ :=
    shrinking_normed_properties (D := D) (half_pos (tubeRadius_pos hU K hK))
  exact tendsto_pullbackInlValue T hU h _ hM h1 hsupp hlim
    (Eventually.of_forall fun n p ↦ by
      rw [coe_ofSupportedIn]
      exact tensorCLM_apply hU K hK n φ p)

/-- **The pullback to `E × {0}`.** Let `T` be a distribution on an open set `W` of the Euclidean
product `WithLp 2 (E × D)`, and `U` an open set of `E` with `U × {0} ⊆ W`. Suppose that no
covector `((x, 0), (0, η))` with `x ∈ U` and `η ≠ 0`, conormal to `E × {0}`, lies in the wave
front set of `T`. Then `T` has a pullback along the inclusion `x ↦ (x, 0)`: the distribution on `U`
whose value at `ψ` is the limit of `T (ψ ⊗ ρ)` as the smooth functions `ρ`, of integral tending to
one and bounded `∫ |ρ|`, concentrate at `0 ∈ D` (`Distribution.tendsto_pullbackInl`). For a
continuous function satisfying the wave front hypothesis it is the restriction to `E × {0}`
(`Distribution.pullbackInl_ofFun`). -/
def pullbackInl (T : 𝓓'(W, ℂ)) (hU : MapsTo (fun x ↦ toLp 2 (x, (0 : D))) (U : Set E) W)
    (h : ∀ x ∈ U, ∀ η : D, η ≠ 0 →
      (toLp 2 (x, (0 : D)), toLp 2 ((0 : E), η)) ∉ T.waveFrontSet) : 𝓓'(U, ℂ) :=
  TestFunction.limitCLM ℝ (pullbackInlValue T hU)
    (fun K hK ↦ continuousLinearMapOfTendsto (fun n ↦ (T : 𝓓(W, ℝ) →L[ℝ] ℂ) ∘L tensorCLM hU K hK n)
      (f := fun φ ↦ pullbackInlValue T hU (ofSupportedIn hK φ))
      (tendsto_pi_nhds.2 (tendsto_apply_tensorCLM T hU h K hK)))
    fun _ _ _ ↦ rfl

private theorem pullbackInl_apply (T : 𝓓'(W, ℂ))
    (hU : MapsTo (fun x ↦ toLp 2 (x, (0 : D))) (U : Set E) W)
    (h : ∀ x ∈ U, ∀ η : D, η ≠ 0 →
      (toLp 2 (x, (0 : D)), toLp 2 ((0 : E), η)) ∉ T.waveFrontSet) (ψ : 𝓓(U, ℝ)) :
    T.pullbackInl hU h ψ = pullbackInlValue T hU ψ :=
  rfl

/-- **Characterization of the pullback to `E × {0}`.** If `f i` are the test functions
`(x, y) ↦ ψ x ρ i y` for functions `ρ i` with `∫ |ρ i| ≤ M` and `∫ ρ i → 1`, supported in the
closed balls of radii `r i → 0`, then `T (f i)` tends to the pullback of `T` evaluated at `ψ`. -/
theorem tendsto_pullbackInl [MeasurableSpace D] [BorelSpace D] (T : 𝓓'(W, ℂ))
    (hU : MapsTo (fun x ↦ toLp 2 (x, (0 : D))) (U : Set E) W)
    (h : ∀ x ∈ U, ∀ η : D, η ≠ 0 →
      (toLp 2 (x, (0 : D)), toLp 2 ((0 : E), η)) ∉ T.waveFrontSet) (ψ : 𝓓(U, ℝ))
    {ι : Type*} {l : Filter ι} {ρ : ι → D → ℝ} {r : ι → ℝ} {M : ℝ} {f : ι → 𝓓(W, ℝ)}
    (hρM : ∀ᶠ i in l, ∫ y, |ρ i y| ≤ M) (hρ1 : Tendsto (fun i ↦ ∫ y, ρ i y) l (𝓝 1))
    (hρr : ∀ᶠ i in l, support (ρ i) ⊆ closedBall 0 (r i)) (hr : Tendsto r l (𝓝 0))
    (hf : ∀ᶠ i in l, ∀ p, f i p = ψ p.fst * ρ i p.snd) :
    Tendsto (fun i ↦ T (f i)) l (𝓝 (T.pullbackInl hU h ψ)) := by
  rw [pullbackInl_apply]
  exact tendsto_pullbackInlValue T hU h ψ hρM hρ1 hρr hr hf

/-! ### Linearity and agreement with the restriction of continuous functions -/

/-- `T (ψ ⊗ ρ_n)` tends to the pullback of `T` at `ψ` for the normalized bumps `ρ_n`. -/
private theorem tendsto_apply_tensorCLM_pullbackInl (T : 𝓓'(W, ℂ))
    (hU : MapsTo (fun x ↦ toLp 2 (x, (0 : D))) (U : Set E) W)
    (h : ∀ x ∈ U, ∀ η : D, η ≠ 0 →
      (toLp 2 (x, (0 : D)), toLp 2 ((0 : E), η)) ∉ T.waveFrontSet) (ψ : 𝓓(U, ℝ)) :
    Tendsto (fun n ↦ T (tensorCLM hU ⟨tsupport ψ, ψ.hasCompactSupport⟩ ψ.tsupport_subset n
      (ContDiffMapSupportedIn.of_support_subset ψ.contDiff (subset_tsupport _)))) atTop
      (𝓝 (T.pullbackInl hU h ψ)) :=
  tendsto_apply_tensorCLM T hU h _ ψ.tsupport_subset _

omit [FiniteDimensional ℝ E] in
/-- Every test function `ψ` on `U` has a sequence of test functions `(x, y) ↦ ψ x ρ_n y` on `W`
as in `Distribution.tendsto_pullbackInl`, for smooth nonnegative functions `ρ_n` of integral one
supported in the closed balls of radii `r n → 0`. -/
theorem exists_seq_tensor_mollifier [MeasurableSpace D] [BorelSpace D]
    (hU : MapsTo (fun x ↦ toLp 2 (x, (0 : D))) (U : Set E) W) (ψ : 𝓓(U, ℝ)) :
    ∃ (ρ : ℕ → D → ℝ) (r : ℕ → ℝ) (f : ℕ → 𝓓(W, ℝ)), (∀ n, ContDiff ℝ ∞ (ρ n)) ∧
      (∀ n y, 0 ≤ ρ n y) ∧ (∀ n, ∫ y, ρ n y = 1) ∧
      (∀ n, support (ρ n) ⊆ closedBall 0 (r n)) ∧ Tendsto r atTop (𝓝 0) ∧
      ∀ n p, f n p = ψ p.fst * ρ n p.snd := by
  set K : Compacts E := ⟨tsupport ψ, ψ.hasCompactSupport⟩
  have hR := half_pos (tubeRadius_pos hU K ψ.tsupport_subset)
  refine ⟨fun n ↦ (ContDiffBump.shrinking (c := (0 : D)) hR n).normed volume,
    fun n ↦ (ContDiffBump.shrinking (c := (0 : D)) hR n).rOut,
    fun n ↦ tensorCLM hU K ψ.tsupport_subset n
      (ContDiffMapSupportedIn.of_support_subset ψ.contDiff (subset_tsupport _)),
    fun n ↦ (ContDiffBump.shrinking hR n).contDiff_normed,
    fun n ↦ (ContDiffBump.shrinking hR n).nonneg_normed,
    fun n ↦ (ContDiffBump.shrinking hR n).integral_normed, fun n ↦ ?_,
    ContDiffBump.tendsto_rOut_shrinking hR, fun n p ↦ ?_⟩
  · rw [(ContDiffBump.shrinking hR n).support_normed_eq]
    exact ball_subset_closedBall
  · rw [tensorCLM_apply, ContDiffMapSupportedIn.coe_of_support_subset]

/-- **Additivity of the pullback in the distribution.** -/
theorem pullbackInl_add (hU : MapsTo (fun x ↦ toLp 2 (x, (0 : D))) (U : Set E) W)
    {T S : 𝓓'(W, ℂ)}
    (hT : ∀ x ∈ U, ∀ η : D, η ≠ 0 →
      (toLp 2 (x, (0 : D)), toLp 2 ((0 : E), η)) ∉ T.waveFrontSet)
    (hS : ∀ x ∈ U, ∀ η : D, η ≠ 0 →
      (toLp 2 (x, (0 : D)), toLp 2 ((0 : E), η)) ∉ S.waveFrontSet) :
    (T + S).pullbackInl hU (fun x hx η hη hm ↦
      (waveFrontSet_add_subset T S hm).elim (hT x hx η hη) (hS x hx η hη)) =
      T.pullbackInl hU hT + S.pullbackInl hU hS := by
  ext ψ
  refine tendsto_nhds_unique (tendsto_apply_tensorCLM_pullbackInl _ hU _ ψ) ?_
  simpa using (tendsto_apply_tensorCLM_pullbackInl T hU hT ψ).add
    (tendsto_apply_tensorCLM_pullbackInl S hU hS ψ)

/-- **Homogeneity of the pullback in the distribution.** -/
theorem pullbackInl_smul (hU : MapsTo (fun x ↦ toLp 2 (x, (0 : D))) (U : Set E) W) (c : ℂ)
    {T : 𝓓'(W, ℂ)}
    (hT : ∀ x ∈ U, ∀ η : D, η ≠ 0 →
      (toLp 2 (x, (0 : D)), toLp 2 ((0 : E), η)) ∉ T.waveFrontSet) :
    (c • T).pullbackInl hU (fun x hx η hη hm ↦ hT x hx η hη (waveFrontSet_smul_subset c T hm)) =
      c • T.pullbackInl hU hT := by
  ext ψ
  refine tendsto_nhds_unique (tendsto_apply_tensorCLM_pullbackInl _ hU _ ψ) ?_
  simpa using (tendsto_apply_tensorCLM_pullbackInl T hU hT ψ).const_smul c

/-- **Homogeneity of the pullback in the distribution**, for a nonzero scalar `c`, with the
hypothesis on the wave front set stated for `c • T`. -/
@[simp]
theorem pullbackInl_smul_of_ne_zero (hU : MapsTo (fun x ↦ toLp 2 (x, (0 : D))) (U : Set E) W)
    {c : ℂ} (hc : c ≠ 0) {T : 𝓓'(W, ℂ)}
    (h : ∀ x ∈ U, ∀ η : D, η ≠ 0 →
      (toLp 2 (x, (0 : D)), toLp 2 ((0 : E), η)) ∉ (c • T).waveFrontSet) :
    (c • T).pullbackInl hU h = c • T.pullbackInl hU (fun x hx η hη hm ↦
      h x hx η hη ((waveFrontSet_smul hc T).symm.subset hm)) :=
  pullbackInl_smul hU c _

/-- The pullback of the zero distribution is zero. -/
@[simp]
theorem pullbackInl_zero (hU : MapsTo (fun x ↦ toLp 2 (x, (0 : D))) (U : Set E) W) :
    (0 : 𝓓'(W, ℂ)).pullbackInl hU (fun _ _ _ _ hm ↦ notMem_empty _ (waveFrontSet_zero.subset hm)) =
      0 := by
  ext ψ
  exact tendsto_nhds_unique (tendsto_apply_tensorCLM_pullbackInl _ hU _ ψ) (by simp)

/-- The pullback commutes with negation of the distribution. -/
@[simp]
theorem pullbackInl_neg (hU : MapsTo (fun x ↦ toLp 2 (x, (0 : D))) (U : Set E) W)
    {T : 𝓓'(W, ℂ)}
    (h : ∀ x ∈ U, ∀ η : D, η ≠ 0 →
      (toLp 2 (x, (0 : D)), toLp 2 ((0 : E), η)) ∉ (-T).waveFrontSet) :
    (-T).pullbackInl hU h =
      -T.pullbackInl hU (fun x hx η hη hm ↦ h x hx η hη ((waveFrontSet_neg T).symm.subset hm)) := by
  ext ψ
  refine tendsto_nhds_unique (tendsto_apply_tensorCLM_pullbackInl _ hU _ ψ) ?_
  simpa using (tendsto_apply_tensorCLM_pullbackInl T hU _ ψ).neg

/-- The pullback commutes with subtraction of distributions. -/
theorem pullbackInl_sub (hU : MapsTo (fun x ↦ toLp 2 (x, (0 : D))) (U : Set E) W)
    {T S : 𝓓'(W, ℂ)}
    (hT : ∀ x ∈ U, ∀ η : D, η ≠ 0 →
      (toLp 2 (x, (0 : D)), toLp 2 ((0 : E), η)) ∉ T.waveFrontSet)
    (hS : ∀ x ∈ U, ∀ η : D, η ≠ 0 →
      (toLp 2 (x, (0 : D)), toLp 2 ((0 : E), η)) ∉ S.waveFrontSet) :
    (T - S).pullbackInl hU (fun x hx η hη hm ↦
      (waveFrontSet_sub_subset T S hm).elim (hT x hx η hη) (hS x hx η hη)) =
      T.pullbackInl hU hT - S.pullbackInl hU hS := by
  ext ψ
  refine tendsto_nhds_unique (tendsto_apply_tensorCLM_pullbackInl _ hU _ ψ) ?_
  simpa using (tendsto_apply_tensorCLM_pullbackInl T hU hT ψ).sub
    (tendsto_apply_tensorCLM_pullbackInl S hU hS ψ)

/-- **Agreement with the restriction of continuous functions.** For a function `F` continuous on
`W` whose wave front set has no covectors conormal to `E × {0}` over `U`, the pullback of `F` to
`E × {0}` is the function `x ↦ F (x, 0)`. This applies in particular to every smooth `F`, whose
wave front set is empty (`Distribution.waveFrontSet_ofFun_eq_empty`). -/
theorem pullbackInl_ofFun [MeasurableSpace E] [BorelSpace E] [MeasurableSpace D] [BorelSpace D]
    (hU : MapsTo (fun x ↦ toLp 2 (x, (0 : D))) (U : Set E) W)
    {F : WithLp 2 (E × D) → ℂ} (hF : ContinuousOn F W)
    (h : ∀ x ∈ U, ∀ η : D, η ≠ 0 →
      (toLp 2 (x, (0 : D)), toLp 2 ((0 : E), η)) ∉ (ofFun W F volume ⊤).waveFrontSet) :
    (ofFun W F volume ⊤).pullbackInl hU h = ofFun U (fun x ↦ F (toLp 2 (x, (0 : D)))) volume ⊤ := by
  have hι : Continuous fun x : E ↦ toLp 2 (x, (0 : D)) :=
    (prod_continuous_toLp 2 E D).comp (continuous_id.prodMk continuous_const)
  ext ψ
  set K : Compacts E := ⟨tsupport ψ, ψ.hasCompactSupport⟩
  have hδ := tubeRadius_pos hU K ψ.tsupport_subset
  refine tendsto_nhds_unique (tendsto_apply_tensorCLM_pullbackInl _ hU h ψ) ?_
  have hFU : ContinuousOn (fun x ↦ F (toLp 2 (x, (0 : D)))) U := hF.comp hι.continuousOn hU
  rw [ofFun_apply (hFU.locallyIntegrableOn U.isOpen.measurableSet)]
  simp_rw [ofFun_apply (hF.locallyIntegrableOn W.isOpen.measurableSet)]
  -- `H (x, y) = ψ x • F (x, y)` is continuous on the tube `E × ball 0 δ`.
  set H : E × D → ℂ := fun q ↦ ψ q.1 • F (toLp 2 q)
  have hH : ContinuousOn H (univ ×ˢ ball (0 : D) (tubeRadius hU K ψ.tsupport_subset)) := by
    rintro ⟨x, y⟩ ⟨-, hy⟩
    refine ContinuousAt.continuousWithinAt ?_
    by_cases hx : x ∈ tsupport ψ
    · have hW : toLp 2 (x, y) ∈ W := toLp_mem_of_lt_tubeRadius hU K ψ.tsupport_subset hx
        (by simpa using hδ) (by simpa using hy)
      exact (ψ.continuous.comp continuous_fst).continuousAt.smul
        ((hF.continuousAt (W.isOpen.mem_nhds hW)).comp (prod_continuous_toLp 2 E D).continuousAt)
    · refine (continuousAt_const : ContinuousAt (fun _ : E × D ↦ (0 : ℂ)) (x, y)).congr ?_
      filter_upwards [continuous_fst.continuousAt.eventually
        (notMem_tsupport_iff_eventuallyEq.1 hx)] with q hq
      simp [H, hq]
  refine (ContDiffBump.tendsto_integral_shrinking_normed_smul (μ := volume) (ν := volume)
    ψ.hasCompactSupport.isCompact
    (fun x y hx ↦ by simp [H, image_eq_zero_of_notMem_tsupport hx]) hδ hH).congr fun n ↦ ?_
  rw [← (WithLp.volume_preserving_symm_measurableEquiv_toLp_prod E D).symm.integral_comp']
  refine integral_congr_ae (Eventually.of_forall fun q ↦ ?_)
  simp [H, tensorCLM_apply, mul_comm, mul_assoc]

end Distribution
