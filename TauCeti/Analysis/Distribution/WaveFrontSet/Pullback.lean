/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.WaveFrontSet.Basic
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.LocallyConvex.Barrelled
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import TauCeti.Algebra.Module.ZLattice.Scaling
import TauCeti.Algebra.Module.ZLattice.Summable
import TauCeti.Analysis.Distribution.TestFunction.Frechet
import TauCeti.Analysis.Distribution.TestFunction.LinearEquiv
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.Distribution.TestFunction.Prod
import TauCeti.Analysis.Distribution.WaveFrontSet.Localization
import TauCeti.Analysis.Distribution.WaveFrontSet.SingularSupport
import TauCeti.Analysis.Fourier.Decay
import TauCeti.Analysis.Fourier.Mollifier
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

the limit being taken as `ρ` runs through nonnegative functions of integral one supported in
balls about `0 ∈ D` of radii tending to zero (`Distribution.tendsto_pullbackInl`). The limit does
not depend on these functions. For a function `F` continuous on `W` the pullback is the restriction
`x ↦ F (x, 0)` (`Distribution.pullbackInl_ofFun`), and it is linear in `T`. Without the hypothesis
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
  at `0`.
* `Distribution.pullbackInl_ofFun`: for a continuous function it is the restriction to `E × {0}`.
* `Distribution.pullbackInl_add`, `Distribution.pullbackInl_smul`: linearity in `T`.

## Implementation notes

Fix a test function `ψ`, and a cutoff `χ` equal to one near `tsupport ψ × {0}`. Expanding
`ψ ⊗ ρ` in a Fourier series along a lattice adapted to `tsupport χ`
(`Distribution.hasSum_fourier_mul_localFourier`) gives

`T (ψ ⊗ ρ) = ∑ m, c 𝓕 ψ (m.fst) 𝓕 ρ (m.snd) T (χ e_(-m))`.

As `ρ` concentrates at `0`, the factors `𝓕 ρ (m.snd)` stay bounded by one and tend to one. The
hypothesis on the wave front set makes `T (χ e_(-m))` decay rapidly on a cone around the conormal
directions `{0} × D`, while off that cone `‖m‖` is comparable to `‖m.fst‖`, where `𝓕 ψ` decays
rapidly. So the summands are dominated by a summable sequence, and by dominated convergence
`T (ψ ⊗ ρ)` tends to the lattice sum without the factors `𝓕 ρ (m.snd)`.

For the test functions supported in a fixed compact set `K`, the maps `ψ ↦ T (ψ ⊗ ρ_n)` for a
sequence of bumps `ρ_n` are continuous linear maps on the Fréchet space `𝓓_K`, so their pointwise
limit is continuous by the Banach–Steinhaus theorem (`continuousLinearMapOfTendsto`), and
`TestFunction.limitCLM` assembles these limits into a distribution on `U`.

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
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D]
  [MeasurableSpace D] [BorelSpace D] {U : Opens E} {W : Opens (WithLp 2 (E × D))}

/-! ### Neighbourhoods of `E × {0}` and decay in the conormal directions -/

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ D]
  [MeasurableSpace D] [BorelSpace D] in
/-- An open set containing `K × {0}` for a compact set `K` contains a tube
`{(x', y) | dist x' x < δ, ‖y‖ < δ}` around it. -/
private theorem exists_pos_tube {G : Set (WithLp 2 (E × D))} (hG : IsOpen G) {K : Set E}
    (hK : IsCompact K) (hKG : ∀ x ∈ K, toLp 2 (x, (0 : D)) ∈ G) :
    ∃ δ > 0, ∀ x ∈ K, ∀ (x' : E) (y : D), dist x' x < δ → ‖y‖ < δ → toLp 2 (x', y) ∈ G := by
  have hc : Continuous fun x : E ↦ toLp 2 (x, (0 : D)) :=
    (prodContinuousLinearEquiv 2 ℝ E D).symm.continuous.comp (continuous_id.prodMk continuous_const)
  obtain ⟨ε, hε, hεG⟩ := (hK.image hc).exists_cthickening_subset_open hG
    (image_subset_iff.2 hKG)
  refine ⟨ε / 2, half_pos hε, fun x hx x' y hx' hy ↦ hεG ?_⟩
  refine mem_cthickening_of_dist_le _ _ _ _ (mem_image_of_mem _ hx) ?_
  rw [dist_eq_norm, ← toLp_sub, Prod.mk_sub_mk, sub_zero]
  refine (prod_norm_le_norm_fst_add_norm_snd _).trans ?_
  rw [toLp_fst, toLp_snd, ← dist_eq_norm]
  linarith

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace D]
  [BorelSpace D] in
/-- An open cone of `WithLp 2 (E × D)` containing the nonzero vectors of `{0} × D` contains a
cone `‖ζ.fst‖ < c ‖ζ.snd‖` around them, by compactness of the unit sphere of `D`. -/
private theorem exists_pos_cone_subset {Γ : Set (WithLp 2 (E × D))} (hΓ : IsOpen Γ)
    (hcone : ∀ t : ℝ, 0 < t → ∀ ζ ∈ Γ, t • ζ ∈ Γ)
    (hD : ∀ b : D, b ≠ 0 → toLp 2 ((0 : E), b) ∈ Γ) :
    ∃ c > 0, ∀ ζ : WithLp 2 (E × D), ‖ζ.fst‖ < c * ‖ζ.snd‖ → ζ ∈ Γ := by
  set ι₂ : D → WithLp 2 (E × D) := fun b ↦ toLp 2 (0, b)
  have hι₂ : Continuous ι₂ := (prodContinuousLinearEquiv 2 ℝ E D).symm.continuous.comp
    (continuous_const.prodMk continuous_id)
  obtain ⟨c, hc, hcΓ⟩ := ((isCompact_sphere (0 : D) 1).image hι₂).exists_cthickening_subset_open
    hΓ (image_subset_iff.2 fun b hb ↦ hD b (ne_zero_of_mem_unit_sphere ⟨b, hb⟩))
  refine ⟨c, hc, fun ζ hζ ↦ ?_⟩
  -- Rescaled to a unit second component, `ζ` lies within `c` of a conormal direction.
  have hs : 0 < ‖ζ.snd‖ := by
    by_contra h0
    have h0' : ‖ζ.snd‖ = 0 := le_antisymm (not_lt.1 h0) (norm_nonneg _)
    rw [h0', mul_zero] at hζ
    exact (norm_nonneg _).not_gt hζ
  set s := ‖ζ.snd‖
  have hmem : s⁻¹ • ζ ∈ Γ := by
    refine hcΓ (mem_cthickening_of_dist_le _ (ι₂ (s⁻¹ • ζ.snd)) _ _
      (mem_image_of_mem _ ?_) ?_)
    · simp [norm_smul, inv_mul_cancel₀ hs.ne', s]
    · rw [dist_eq_norm, prod_norm_eq_norm_fst_of_snd_eq_zero (by simp [ι₂])]
      simp only [ι₂, sub_fst, smul_fst, toLp_fst, sub_zero, norm_smul, norm_inv]
      rw [Real.norm_of_nonneg hs.le, inv_mul_le_iff₀ hs]
      linarith
  simpa [smul_smul, mul_inv_cancel₀ hs.ne'] using hcone s hs _ hmem

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace D] [BorelSpace D] in
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
  obtain ⟨c, hc, hcΓ⟩ := exists_pos_cone_subset (isOpen_biUnion fun η _ ↦ hΓ η)
    (fun s hs ζ hζ ↦ by
      obtain ⟨η, hηt, hζη⟩ := mem_iUnion₂.1 hζ
      exact mem_iUnion₂.2 ⟨η, hηt, hcone η s hs ζ hζη⟩)
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
  obtain ⟨η, hηt, hζΓ⟩ := mem_iUnion₂.1 (hcΓ ζ hζ)
  calc (1 + ‖ζ‖) ^ N * ‖T.localFourier χ ζ‖ ≤ C η := hC η hηt ζ hζΓ
    _ ≤ |C η| := le_abs_self _
    _ ≤ ∑ η ∈ t, |C η| :=
      Finset.single_le_sum (f := fun η ↦ |C η|) (fun _ _ ↦ abs_nonneg _) hηt

/-! ### The limit of `T (ψ ⊗ ρ)` as `ρ` concentrates at `0` -/

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ D]
  [MeasurableSpace D] [BorelSpace D] in
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
`ψ ⊗ ρ i` for nonnegative `ρ i` of integral one supported in balls of radii `r i → 0`, then
`T (f i)` converges to the lattice sum `∑ m, (covolume L)⁻¹ 𝓕 ψ (m.fst) T (χ e_(-m))`. -/
private theorem tendsto_apply_tsum (T : 𝓓'(W, ℂ)) {ψ : 𝓓(U, ℝ)} {χ : 𝓓(W, ℂ)}
    {δ : ℝ} (hδ : 0 < δ) (hχ : ∀ x ∈ tsupport ψ, ∀ y : D, ‖y‖ ≤ δ → χ (toLp 2 (x, y)) = 1)
    (L : Submodule ℤ (WithLp 2 (E × D))) [DiscreteTopology L] [IsZLattice ℝ L]
    (hL : ∀ p ∈ tsupport χ, ∀ ℓ ∈ L, p + ℓ ∈ tsupport χ → ℓ = 0) {c : ℝ} (hc : 0 < c)
    (hdecay : ∀ N : ℕ, ∃ C, ∀ ζ : WithLp 2 (E × D),
      ‖ζ.fst‖ < c * ‖ζ.snd‖ → (1 + ‖ζ‖) ^ N * ‖T.localFourier χ ζ‖ ≤ C)
    {ι : Type*} {l : Filter ι} {ρ : ι → D → ℝ} {r : ι → ℝ} {f : ι → 𝓓(W, ℝ)}
    (hρ0 : ∀ᶠ i in l, ∀ y, 0 ≤ ρ i y) (hρ1 : ∀ᶠ i in l, ∫ y, ρ i y = 1)
    (hρr : ∀ᶠ i in l, support (ρ i) ⊆ closedBall 0 (r i)) (hr : Tendsto r l (𝓝 0))
    (hf : ∀ᶠ i in l, ∀ p, f i p = ψ p.fst * ρ i p.snd) :
    Tendsto (fun i ↦ T (f i)) l (𝓝 (∑' m : ZLattice.dual L, (ZLattice.covolume L : ℂ)⁻¹ *
      𝓕 (fun x ↦ (ψ x : ℂ)) (m : WithLp 2 (E × D)).fst * T.localFourier χ (-m))) := by
  set a : ℂ := (ZLattice.covolume L : ℂ)⁻¹
  set Ψ : E → ℂ := 𝓕 fun x ↦ (ψ x : ℂ)
  have hψc : ContDiff ℝ ∞ fun x ↦ (ψ x : ℂ) := ofRealCLM.contDiff.comp ψ.contDiff
  -- The limiting summands decay rapidly, hence are summable over the dual lattice.
  have hsum : Summable fun m : ZLattice.dual L ↦ ‖a * Ψ (m : WithLp 2 (E × D)).fst *
      T.localFourier χ (-m)‖ := by
    have h := ZLattice.summable_one_add_norm_pow_mul_norm_of_decay (ZLattice.dual L)
      (f := fun ζ : WithLp 2 (E × D) ↦ a * (Ψ ζ.fst * T.localFourier χ (-ζ))) (fun N ↦ by
        obtain ⟨C, hC⟩ := exists_decay_mul_localFourier_neg T hc hdecay
          (fun N ↦ TauCeti.exists_one_add_norm_pow_mul_norm_fourier_le hψc
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
        (ψ p.fst : ℂ) * (ρ i p.snd : ℂ) := by
      ext p
      simp [hfi]
    refine HasSum.tsum_eq ?_
    convert hasSum_fourier_mul_localFourier T χ L hL (φ := f i) (fun p hp ↦ ?_) using 2 with m
    · have h := Real.fourier_prod_mul (fun x ↦ (ψ x : ℂ)) (fun y ↦ (ρ i y : ℂ))
        (m : WithLp 2 (E × D))
      rw [hfun, h, mul_assoc a]
    · have hp' : ψ p.fst ≠ 0 ∧ ρ i p.snd ≠ 0 := by simpa [hfi] using hp
      have hy : ‖p.snd‖ ≤ δ := by
        have := hri hp'.2
        rw [mem_closedBall, dist_zero_right] at this
        linarith
      have h := hχ p.fst (subset_tsupport _ hp'.1) p.snd hy
      rwa [← ofLp_fst, ← ofLp_snd, Prod.mk.eta, toLp_ofLp] at h
  refine Tendsto.congr' heq ?_
  refine tendsto_tsum_of_dominated_convergence hsum (fun m ↦ ?_) ?_
  · simpa using ((Real.tendsto_fourier_ofReal_one hρ0 hρ1 hρr hr _).const_mul
      (a * Ψ (m : WithLp 2 (E × D)).fst)).mul_const (T.localFourier χ (-m))
  · filter_upwards [hρ0, hρ1] with i h0 h1 m
    have h := Real.norm_fourier_ofReal_le_one h0 h1 (m : WithLp 2 (E × D)).snd
    simp only [norm_mul]
    calc ‖a‖ * ‖Ψ (m : WithLp 2 (E × D)).fst‖ *
          ‖𝓕 (fun y ↦ (ρ i y : ℂ)) (m : WithLp 2 (E × D)).snd‖ * ‖T.localFourier χ (-m)‖
        ≤ ‖a‖ * ‖Ψ (m : WithLp 2 (E × D)).fst‖ * 1 * ‖T.localFourier χ (-m)‖ := by gcongr
      _ = _ := by rw [mul_one]

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace D] [BorelSpace D] in
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
    exists_pos_tube (hG.inter W.isOpen) hK fun x hx ↦ ⟨hKG x hx, hKW x hx⟩
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
  · refine (tsupport_comp_subset (g := ((↑) : ℝ → ℂ)) ofReal_zero _).trans
      (hχG.trans inter_subset_left)


omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ D]
  [MeasurableSpace D] [BorelSpace D] in
/-- If `U × {0}` lies in `W`, every compact `K ⊆ U` has a tube around `K × {0}` inside `W`. -/
private theorem exists_pos_tube_of_mapsTo (hU : MapsTo (fun x ↦ toLp 2 (x, (0 : D))) (U : Set E) W)
    (K : Compacts E) (hK : (K : Set E) ⊆ U) :
    ∃ δ > 0, ∀ x ∈ (K : Set E), ∀ (x' : E) (y : D), dist x' x < δ → ‖y‖ < δ →
      toLp 2 (x', y) ∈ W :=
  exists_pos_tube W.isOpen K.isCompact fun _ hx ↦ hU (hK hx)

/-- The radius of a tube around `K × {0}` inside `W`. -/
private def tubeRadius (hU : MapsTo (fun x ↦ toLp 2 (x, (0 : D))) (U : Set E) W) (K : Compacts E)
    (hK : (K : Set E) ⊆ U) : ℝ :=
  (exists_pos_tube_of_mapsTo hU K hK).choose

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ D]
  [MeasurableSpace D] [BorelSpace D] in
private theorem tubeRadius_pos (hU : MapsTo (fun x ↦ toLp 2 (x, (0 : D))) (U : Set E) W)
    (K : Compacts E) (hK : (K : Set E) ⊆ U) : 0 < tubeRadius hU K hK :=
  (exists_pos_tube_of_mapsTo hU K hK).choose_spec.1

/-- The bump function about `0 ∈ D` with outer radius `δ / (n + 2)`. -/
private def bump {δ : ℝ} (hδ : 0 < δ) (n : ℕ) : ContDiffBump (0 : D) where
  rIn := δ / (2 * (n + 2))
  rOut := δ / (n + 2)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    apply div_lt_div_of_pos_left hδ (by positivity)
    linarith

/-- The normalized bump `ρ_n` of integral one supported in the closed ball of radius
`δ / (n + 2)`, as a test function on the open ball of radius `δ`. -/
private def mollifier {δ : ℝ} (hδ : 0 < δ) (n : ℕ) : 𝓓((⟨ball (0 : D) δ, isOpen_ball⟩ : Opens D), ℝ)
    where
  toFun := (bump hδ n).normed volume
  contDiff' := (bump hδ n).contDiff_normed
  hasCompactSupport' := (bump hδ n).hasCompactSupport_normed
  tsupport_subset' := by
    rw [(bump hδ n).tsupport_normed_eq]
    exact closedBall_subset_ball (div_lt_self hδ (by linarith))

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
    exact (exists_pos_tube_of_mapsTo hU K hK).choose_spec.2 x hx x' y hxx'
      (by simpa [O, δ, tubeRadius] using hy)
  (prodContinuousLinearEquiv 2 ℝ E D).symm.transportTestFunction hVW ∘L
    (prodSMulCLM (F := ℝ) (mollifier (tubeRadius_pos hU K hK) n) (V := V) subset_rfl ∘L
      ofSupportedInCLM ℝ hKΩ)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The values `(φ ⊗ ρ_n) (x, y) = φ x ρ_n y` of the mollified tensor products. -/
private theorem tensorCLM_apply (hU : MapsTo (fun x ↦ toLp 2 (x, (0 : D))) (U : Set E) W)
    (K : Compacts E) (hK : (K : Set E) ⊆ U) (n : ℕ) (φ : 𝓓_{K}(E, ℝ)) (p : WithLp 2 (E × D)) :
    tensorCLM hU K hK n φ p = φ p.fst * (bump (tubeRadius_pos hU K hK) n).normed volume p.snd := by
  simp only [tensorCLM, ContinuousLinearMap.comp_apply]
  -- `erw`: the two evaluation lemmas match only after unfolding the instances on the product
  -- spaces that `tensorCLM` builds its open sets in.
  erw [ContinuousLinearEquiv.transportTestFunction_apply, prodSMulCLM_apply]
  rw [smul_eq_mul, mul_comm]
  rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The normalized bumps `ρ_n` are nonnegative of integral one, supported in the closed balls of
radii `δ / (n + 2) → 0`. -/
private theorem bump_normed_properties {δ : ℝ} (hδ : 0 < δ) :
    (∀ᶠ n in atTop, ∀ y, 0 ≤ (bump (D := D) hδ n).normed volume y) ∧
      (∀ᶠ n in atTop, ∫ y, (bump (D := D) hδ n).normed volume y = 1) ∧
      (∀ᶠ n in atTop, support ((bump (D := D) hδ n).normed volume) ⊆
        closedBall 0 (δ / ((n : ℝ) + 2))) ∧
      Tendsto (fun n : ℕ ↦ δ / ((n : ℝ) + 2)) atTop (𝓝 0) :=
  ⟨Eventually.of_forall fun n ↦ (bump hδ n).nonneg_normed,
    Eventually.of_forall fun n ↦ (bump hδ n).integral_normed,
    Eventually.of_forall fun n ↦ by
      rw [(bump hδ n).support_normed_eq]
      exact ball_subset_closedBall,
    tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)⟩

/-- The candidate value of the pullback at `ψ`: the limit of `T (ψ ⊗ ρ_n)` for the normalized
bumps `ρ_n`. -/
private def pullbackInlValue (T : 𝓓'(W, ℂ))
    (hU : MapsTo (fun x ↦ toLp 2 (x, (0 : D))) (U : Set E) W) (ψ : 𝓓(U, ℝ)) : ℂ :=
  limUnder atTop fun n ↦ T (tensorCLM hU ⟨tsupport ψ, ψ.hasCompactSupport⟩ ψ.tsupport_subset n
    (ContDiffMapSupportedIn.of_support_subset ψ.contDiff (subset_tsupport _)))

/-- `T (ψ ⊗ ρ i)` converges to the candidate value for every family of nonnegative `ρ i` of
integral one supported in balls of radii tending to zero. -/
private theorem tendsto_pullbackInlValue (T : 𝓓'(W, ℂ))
    (hU : MapsTo (fun x ↦ toLp 2 (x, (0 : D))) (U : Set E) W)
    (h : ∀ x ∈ U, ∀ η : D, η ≠ 0 →
      (toLp 2 (x, (0 : D)), toLp 2 ((0 : E), η)) ∉ T.waveFrontSet) (ψ : 𝓓(U, ℝ))
    {ι : Type*} {l : Filter ι} {ρ : ι → D → ℝ} {r : ι → ℝ} {f : ι → 𝓓(W, ℝ)}
    (hρ0 : ∀ᶠ i in l, ∀ y, 0 ≤ ρ i y) (hρ1 : ∀ᶠ i in l, ∫ y, ρ i y = 1)
    (hρr : ∀ᶠ i in l, support (ρ i) ⊆ closedBall 0 (r i)) (hr : Tendsto r l (𝓝 0))
    (hf : ∀ᶠ i in l, ∀ p, f i p = ψ p.fst * ρ i p.snd) :
    Tendsto (fun i ↦ T (f i)) l (𝓝 (pullbackInlValue T hU ψ)) := by
  obtain ⟨δ, hδ, χ, hχ, c, hc, hdecay⟩ := exists_cutoff_decay T ψ.hasCompactSupport.isCompact
    (fun x hx ↦ hU (ψ.tsupport_subset hx)) fun x hx ↦ h x (ψ.tsupport_subset hx)
  obtain ⟨L, _, _, hL⟩ :=
    ZLattice.exists_forall_add_mem_eq_zero_of_isBounded χ.hasCompactSupport.isCompact.isBounded
  -- Both the given family and the normalized bumps converge to the same lattice sum.
  have hK := tubeRadius_pos hU ⟨tsupport ψ, ψ.hasCompactSupport⟩ ψ.tsupport_subset
  obtain ⟨h0, h1, hsupp, hlim⟩ := bump_normed_properties (D := D) hK
  have hcan := tendsto_apply_tsum T hδ hχ L hL hc hdecay h0 h1 hsupp hlim
    (f := fun n ↦ tensorCLM hU ⟨tsupport ψ, ψ.hasCompactSupport⟩ ψ.tsupport_subset n
      (ContDiffMapSupportedIn.of_support_subset ψ.contDiff (subset_tsupport _)))
    (Eventually.of_forall fun n p ↦ by
      rw [tensorCLM_apply, ContDiffMapSupportedIn.coe_of_support_subset])
  rw [pullbackInlValue, hcan.limUnder_eq]
  exact tendsto_apply_tsum T hδ hχ L hL hc hdecay hρ0 hρ1 hρr hr hf

/-- **The pullback to `E × {0}`.** Let `T` be a distribution on an open set `W` of the Euclidean
product `WithLp 2 (E × D)`, and `U` an open set of `E` with `U × {0} ⊆ W`. Suppose that no
covector `((x, 0), (0, η))` with `x ∈ U` and `η ≠ 0`, conormal to `E × {0}`, lies in the wave
front set of `T`. Then `T` has a pullback along the inclusion `x ↦ (x, 0)`: the distribution on `U`
whose value at `ψ` is the limit of `T (ψ ⊗ ρ)` as `ρ` runs through nonnegative functions of
integral one concentrating at `0 ∈ D` (`Distribution.tendsto_pullbackInl`). For a continuous
function it is the restriction to `E × {0}` (`Distribution.pullbackInl_ofFun`). -/
def pullbackInl (T : 𝓓'(W, ℂ)) (hU : MapsTo (fun x ↦ toLp 2 (x, (0 : D))) (U : Set E) W)
    (h : ∀ x ∈ U, ∀ η : D, η ≠ 0 →
      (toLp 2 (x, (0 : D)), toLp 2 ((0 : E), η)) ∉ T.waveFrontSet) : 𝓓'(U, ℂ) :=
  TestFunction.limitCLM ℝ (pullbackInlValue T hU)
    (fun K hK ↦ continuousLinearMapOfTendsto (fun n ↦ (T : 𝓓(W, ℝ) →L[ℝ] ℂ) ∘L tensorCLM hU K hK n)
      (f := fun φ ↦ pullbackInlValue T hU (ofSupportedIn hK φ)) (tendsto_pi_nhds.2 fun φ ↦ by
        obtain ⟨h0, h1, hsupp, hlim⟩ := bump_normed_properties (D := D) (tubeRadius_pos hU K hK)
        exact tendsto_pullbackInlValue T hU h _ h0 h1 hsupp hlim
          (Eventually.of_forall fun n p ↦ by
            rw [coe_ofSupportedIn]
            exact tensorCLM_apply hU K hK n φ p)))
    fun _ _ _ ↦ rfl

private theorem pullbackInl_apply (T : 𝓓'(W, ℂ))
    (hU : MapsTo (fun x ↦ toLp 2 (x, (0 : D))) (U : Set E) W)
    (h : ∀ x ∈ U, ∀ η : D, η ≠ 0 →
      (toLp 2 (x, (0 : D)), toLp 2 ((0 : E), η)) ∉ T.waveFrontSet) (ψ : 𝓓(U, ℝ)) :
    T.pullbackInl hU h ψ = pullbackInlValue T hU ψ :=
  rfl

/-- **Characterization of the pullback to `E × {0}`.** If `f i` are the test functions
`(x, y) ↦ ψ x ρ i y` for nonnegative functions `ρ i` of integral one supported in the closed balls
of radii `r i → 0`, then `T (f i)` tends to the pullback of `T` evaluated at `ψ`. -/
theorem tendsto_pullbackInl (T : 𝓓'(W, ℂ))
    (hU : MapsTo (fun x ↦ toLp 2 (x, (0 : D))) (U : Set E) W)
    (h : ∀ x ∈ U, ∀ η : D, η ≠ 0 →
      (toLp 2 (x, (0 : D)), toLp 2 ((0 : E), η)) ∉ T.waveFrontSet) (ψ : 𝓓(U, ℝ))
    {ι : Type*} {l : Filter ι} {ρ : ι → D → ℝ} {r : ι → ℝ} {f : ι → 𝓓(W, ℝ)}
    (hρ0 : ∀ᶠ i in l, ∀ y, 0 ≤ ρ i y) (hρ1 : ∀ᶠ i in l, ∫ y, ρ i y = 1)
    (hρr : ∀ᶠ i in l, support (ρ i) ⊆ closedBall 0 (r i)) (hr : Tendsto r l (𝓝 0))
    (hf : ∀ᶠ i in l, ∀ p, f i p = ψ p.fst * ρ i p.snd) :
    Tendsto (fun i ↦ T (f i)) l (𝓝 (T.pullbackInl hU h ψ)) := by
  rw [pullbackInl_apply]
  exact tendsto_pullbackInlValue T hU h ψ hρ0 hρ1 hρr hr hf

/-! ### Linearity and agreement with the restriction of continuous functions -/

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Every test function `ψ` on `U` has a family `ψ ⊗ ρ_n` as in `tendsto_pullbackInl`, with
continuous `ρ_n`, supported in a tube `tsupport ψ × closedBall 0 δ` inside `W`. -/
private theorem exists_family (hU : MapsTo (fun x ↦ toLp 2 (x, (0 : D))) (U : Set E) W)
    (ψ : 𝓓(U, ℝ)) :
    ∃ (ρ : ℕ → D → ℝ) (r : ℕ → ℝ) (f : ℕ → 𝓓(W, ℝ)), (∀ᶠ n in atTop, ∀ y, 0 ≤ ρ n y) ∧
      (∀ᶠ n in atTop, ∫ y, ρ n y = 1) ∧
      (∀ᶠ n in atTop, support (ρ n) ⊆ closedBall 0 (r n)) ∧ Tendsto r atTop (𝓝 0) ∧
      (∀ᶠ n in atTop, ∀ p, f n p = ψ p.fst * ρ n p.snd) ∧ (∀ n, Continuous (ρ n)) ∧
      ∃ δ > 0, (∀ n, r n ≤ δ) ∧ ∀ x ∈ tsupport ψ, ∀ y : D, ‖y‖ ≤ δ → toLp 2 (x, y) ∈ W := by
  set K : Compacts E := ⟨tsupport ψ, ψ.hasCompactSupport⟩
  have hδ := tubeRadius_pos hU K ψ.tsupport_subset
  obtain ⟨h0, h1, hsupp, hlim⟩ := bump_normed_properties (D := D) hδ
  refine ⟨fun n ↦ (bump hδ n).normed volume, _, fun n ↦ tensorCLM hU K ψ.tsupport_subset n
    (ContDiffMapSupportedIn.of_support_subset ψ.contDiff (subset_tsupport _)), h0, h1, hsupp,
    hlim, Eventually.of_forall fun n p ↦ by
      rw [tensorCLM_apply, ContDiffMapSupportedIn.coe_of_support_subset],
    fun n ↦ (bump hδ n).continuous_normed, tubeRadius hU K ψ.tsupport_subset / 2, half_pos hδ,
    fun n ↦ div_le_div_of_nonneg_left hδ.le two_pos (by linarith [n.cast_nonneg (α := ℝ)]),
    fun x hx y hy ↦ (exists_pos_tube_of_mapsTo hU K ψ.tsupport_subset).choose_spec.2 x hx x y
      (by rw [dist_self]; exact hδ) (by unfold tubeRadius at hy hδ; linarith)⟩

/-- **Linearity of the pullback in the distribution.** -/
theorem pullbackInl_add (hU : MapsTo (fun x ↦ toLp 2 (x, (0 : D))) (U : Set E) W)
    {T S : 𝓓'(W, ℂ)}
    (hT : ∀ x ∈ U, ∀ η : D, η ≠ 0 →
      (toLp 2 (x, (0 : D)), toLp 2 ((0 : E), η)) ∉ T.waveFrontSet)
    (hS : ∀ x ∈ U, ∀ η : D, η ≠ 0 →
      (toLp 2 (x, (0 : D)), toLp 2 ((0 : E), η)) ∉ S.waveFrontSet)
    (hTS : ∀ x ∈ U, ∀ η : D, η ≠ 0 →
      (toLp 2 (x, (0 : D)), toLp 2 ((0 : E), η)) ∉ (T + S).waveFrontSet) :
    (T + S).pullbackInl hU hTS = T.pullbackInl hU hT + S.pullbackInl hU hS := by
  ext ψ
  obtain ⟨ρ, r, f, h0, h1, hsupp, hr, hf, -⟩ := exists_family hU ψ
  refine tendsto_nhds_unique (tendsto_pullbackInl _ hU hTS ψ h0 h1 hsupp hr hf) ?_
  simpa using (tendsto_pullbackInl T hU hT ψ h0 h1 hsupp hr hf).add
    (tendsto_pullbackInl S hU hS ψ h0 h1 hsupp hr hf)

/-- **Homogeneity of the pullback in the distribution.** -/
theorem pullbackInl_smul (hU : MapsTo (fun x ↦ toLp 2 (x, (0 : D))) (U : Set E) W) (c : ℂ)
    {T : 𝓓'(W, ℂ)}
    (hT : ∀ x ∈ U, ∀ η : D, η ≠ 0 →
      (toLp 2 (x, (0 : D)), toLp 2 ((0 : E), η)) ∉ T.waveFrontSet)
    (hcT : ∀ x ∈ U, ∀ η : D, η ≠ 0 →
      (toLp 2 (x, (0 : D)), toLp 2 ((0 : E), η)) ∉ (c • T).waveFrontSet) :
    (c • T).pullbackInl hU hcT = c • T.pullbackInl hU hT := by
  ext ψ
  obtain ⟨ρ, r, f, h0, h1, hsupp, hr, hf, -⟩ := exists_family hU ψ
  refine tendsto_nhds_unique (tendsto_pullbackInl _ hU hcT ψ h0 h1 hsupp hr hf) ?_
  simpa using (tendsto_pullbackInl T hU hT ψ h0 h1 hsupp hr hf).const_smul c

/-- On the product `E × D`, a function `(x, y) ↦ (ψ x ρ y) • g (x, y)` with `g` continuous on
`tsupport ψ × closedBall 0 δ` and `ρ` continuous, supported in `closedBall 0 δ`, is integrable. -/
private theorem integrable_mul_smul {ψ : E → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
    {ρ : D → ℝ} (hρ : Continuous ρ) {δ : ℝ} (hρδ : support ρ ⊆ closedBall 0 δ) {g : E × D → ℂ}
    (hg : ContinuousOn g (tsupport ψ ×ˢ closedBall 0 δ)) :
    Integrable fun q : E × D ↦ (ψ q.1 * ρ q.2) • g q := by
  refine (((hψ.comp continuous_fst).mul (hρ.comp continuous_snd)).continuousOn.smul hg
    |>.integrableOn_compact (hψc.isCompact.prod (isCompact_closedBall _ _)))
    |>.integrable_of_forall_notMem_eq_zero fun q hq ↦ ?_
  by_contra hne
  have hne' : (ψ q.1 * ρ q.2) • g q ≠ 0 := hne
  have hq' : ψ q.1 ≠ 0 ∧ ρ q.2 ≠ 0 := by
    simpa using left_ne_zero_of_smul hne'
  exact hq ⟨subset_tsupport _ hq'.1, hρδ hq'.2⟩

/-- **One step of the approximate identity.** Suppose `F (x, y)` varies by at most `ε` over
distances at most `η` on `S = tsupport ψ × closedBall 0 δ`. If `ρ` is a nonnegative continuous
function of integral one supported in `closedBall 0 r` with `r ≤ η` and `r ≤ δ`, then
`∫ (ψ ⊗ ρ) • F` is within `ε ∫ |ψ|` of `∫ ψ x • F (x, 0) dx`. -/
private theorem norm_integral_smul_sub_le {F : WithLp 2 (E × D) → ℂ} {ψ : E → ℝ}
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) {δ η ε r : ℝ}
    (hF : ContinuousOn F (toLp 2 '' (tsupport ψ ×ˢ closedBall (0 : D) δ)))
    (huc : ∀ x ∈ tsupport ψ ×ˢ closedBall (0 : D) δ, ∀ y ∈ tsupport ψ ×ˢ closedBall (0 : D) δ,
      dist x y ≤ η → dist (F (toLp 2 x)) (F (toLp 2 y)) ≤ ε)
    {ρ : D → ℝ} (hρ : Continuous ρ) (h0 : ∀ y, 0 ≤ ρ y) (h1 : ∫ y, ρ y = 1)
    (hsupp : support ρ ⊆ closedBall 0 r) (hrη : r ≤ η) (hrδ : r ≤ δ) :
    ‖(∫ q : E × D, (ψ q.1 * ρ q.2) • F (toLp 2 q)) - ∫ x, ψ x • F (toLp 2 (x, 0))‖ ≤
      ε * ∫ x, |ψ x| := by
  set S : Set (E × D) := tsupport ψ ×ˢ closedBall 0 δ
  have hr : 0 ≤ r := by
    by_contra hneg
    have hρ0 : ρ = 0 := by
      ext y
      by_contra hy
      have h := hsupp hy
      rw [mem_closedBall, dist_zero_right] at h
      linarith [norm_nonneg y]
    simp [hρ0] at h1
  have hρδ : support ρ ⊆ closedBall 0 δ := hsupp.trans (closedBall_subset_closedBall hrδ)
  have hS0 (q : E × D) (hq : q ∈ S) : (q.1, (0 : D)) ∈ S := ⟨hq.1, by simpa using hr.trans hrδ⟩
  have hG : ContinuousOn (fun q : E × D ↦ F (toLp 2 q)) S :=
    hF.comp (prod_continuous_toLp 2 E D).continuousOn (mapsTo_image _ _)
  have hG0 : ContinuousOn (fun q : E × D ↦ F (toLp 2 (q.1, 0))) S :=
    hF.comp ((prod_continuous_toLp 2 E D).comp
      (continuous_fst.prodMk continuous_const)).continuousOn fun q hq ↦ ⟨(q.1, 0), hS0 q hq, rfl⟩
  -- `∫ ψ x • F (x, 0) dx` is `∫ (ψ ⊗ ρ) • F (x, 0)`, since `ρ` has integral one.
  have hB : ∫ x, ψ x • F (toLp 2 (x, 0)) =
      ∫ q : E × D, (ψ q.1 * ρ q.2) • F (toLp 2 (q.1, 0)) := by
    have h : (fun q : E × D ↦ (ψ q.1 * ρ q.2) • F (toLp 2 (q.1, 0))) =
        fun q ↦ ψ q.1 • F (toLp 2 (q.1, 0)) * (ρ q.2 : ℂ) := by
      ext q
      simp only [Complex.real_smul, ofReal_mul]
      ring
    rw [h, Measure.volume_eq_prod, integral_prod_mul (fun x ↦ ψ x • F (toLp 2 (x, 0)))
      (fun y ↦ (ρ y : ℂ)), integral_complex_ofReal, h1, ofReal_one, mul_one]
  have hsub := integral_sub (integrable_mul_smul hψ hψc hρ hρδ hG)
    (integrable_mul_smul hψ hψc hρ hρδ hG0)
  rw [hB, ← hsub]
  -- Pointwise, the difference is at most `ε |ψ x| ρ y`.
  have hbound (q : E × D) : ‖(ψ q.1 * ρ q.2) • F (toLp 2 q) -
      (ψ q.1 * ρ q.2) • F (toLp 2 (q.1, 0))‖ ≤ ε * (|ψ q.1| * ρ q.2) := by
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (h0 q.2), mul_comm ε]
    by_cases hq : ψ q.1 * ρ q.2 = 0
    · rcases mul_eq_zero.1 hq with h | h <;> simp [h]
    have hq' := mul_ne_zero_iff.1 hq
    have hqS : q ∈ S := ⟨subset_tsupport _ hq'.1, hρδ hq'.2⟩
    have hd := huc q hqS (q.1, 0) (hS0 q hqS) (by
      rw [Prod.dist_eq, dist_self, dist_zero_right]
      exact max_le (hr.trans hrη) ((by simpa using hsupp hq'.2 : ‖q.2‖ ≤ r).trans hrη))
    exact mul_le_mul_of_nonneg_left (by rwa [← dist_eq_norm]) (mul_nonneg (abs_nonneg _) (h0 _))
  have hρint : Integrable ρ := Integrable.of_integral_ne_zero (by rw [h1]; exact one_ne_zero)
  refine (norm_integral_le_of_norm_le (((hψ.abs.integrable_of_hasCompactSupport hψc.abs).mul_prod
    hρint).const_mul ε) (Eventually.of_forall hbound)).trans_eq ?_
  rw [integral_const_mul, integral_prod_mul (fun x ↦ |ψ x|) (fun y ↦ ρ y), h1, mul_one]

/-- **The approximate identity in the normal variable.** If `F` is continuous on
`tsupport ψ × closedBall 0 δ`, then `∫ (ψ ⊗ ρ_n) • F → ∫ ψ(x) F(x, 0) dx` for nonnegative
continuous `ρ_n` of integral one supported in balls of radii `r_n → 0`. -/
private theorem tendsto_integral_smul_of_tensor {F : WithLp 2 (E × D) → ℂ} {ψ : E → ℝ}
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) {δ : ℝ} (hδ : 0 < δ)
    (hF : ContinuousOn F (toLp 2 '' (tsupport ψ ×ˢ closedBall (0 : D) δ)))
    {ρ : ℕ → D → ℝ} {r : ℕ → ℝ} {f : ℕ → WithLp 2 (E × D) → ℝ}
    (h0 : ∀ᶠ n in atTop, ∀ y, 0 ≤ ρ n y) (h1 : ∀ᶠ n in atTop, ∫ y, ρ n y = 1)
    (hsupp : ∀ᶠ n in atTop, support (ρ n) ⊆ closedBall 0 (r n)) (hr : Tendsto r atTop (𝓝 0))
    (hf : ∀ᶠ n in atTop, ∀ p, f n p = ψ p.fst * ρ n p.snd) (hρc : ∀ n, Continuous (ρ n)) :
    Tendsto (fun n ↦ ∫ p, f n p • F p) atTop (𝓝 (∫ x, ψ x • F (toLp 2 (x, 0)))) := by
  have hS : IsCompact (tsupport ψ ×ˢ closedBall (0 : D) δ) :=
    hψc.isCompact.prod (isCompact_closedBall _ _)
  have hM : 0 ≤ ∫ x, |ψ x| := integral_nonneg fun _ ↦ abs_nonneg _
  rw [Metric.tendsto_nhds]
  intro ε hε
  -- Uniform continuity of `F` near `tsupport ψ × {0}` with tolerance `ε' = ε / (2 (∫ |ψ| + 1))`.
  set ε' := ε / (2 * ((∫ x, |ψ x|) + 1))
  obtain ⟨η, hη, huc⟩ := Metric.uniformContinuousOn_iff_le.1
    (hS.uniformContinuousOn_of_continuous
      (hF.comp (prod_continuous_toLp 2 E D).continuousOn (mapsTo_image _ _))) ε' (by positivity)
  filter_upwards [h0, h1, hsupp, hf, hr.eventually (gt_mem_nhds (lt_min hη hδ))]
    with n h0n h1n hsn hfn hrn
  have hA : ∫ p, f n p • F p = ∫ q : E × D, (ψ q.1 * ρ n q.2) • F (toLp 2 q) := by
    rw [← (WithLp.volume_preserving_symm_measurableEquiv_toLp_prod E D).symm.integral_comp']
    simp [hfn]
  rw [dist_eq_norm, hA]
  refine (norm_integral_smul_sub_le hψ hψc hF huc (hρc n) h0n h1n hsn
    ((le_of_lt hrn).trans (min_le_left _ _)) ((le_of_lt hrn).trans (min_le_right _ _))).trans_lt ?_
  calc ε' * ∫ x, |ψ x| = ε / 2 * ((∫ x, |ψ x|) / ((∫ x, |ψ x|) + 1)) := by
        simp only [ε']; field_simp
    _ ≤ ε / 2 * 1 := by gcongr; exact div_le_one_of_le₀ (by linarith) (by linarith)
    _ < ε := by linarith

/-- **Agreement with the restriction of continuous functions.** For a function `F` continuous on
`W`, the pullback of `F` to `E × {0}` is the function `x ↦ F (x, 0)`. This applies in particular
to every smooth `F`, whose wave front set is empty (`Distribution.waveFrontSet_ofFun_eq_empty`). -/
theorem pullbackInl_ofFun (hU : MapsTo (fun x ↦ toLp 2 (x, (0 : D))) (U : Set E) W)
    {F : WithLp 2 (E × D) → ℂ} (hF : ContinuousOn F W)
    (h : ∀ x ∈ U, ∀ η : D, η ≠ 0 →
      (toLp 2 (x, (0 : D)), toLp 2 ((0 : E), η)) ∉ (ofFun W F volume ⊤).waveFrontSet) :
    (ofFun W F volume ⊤).pullbackInl hU h = ofFun U (fun x ↦ F (toLp 2 (x, (0 : D)))) volume ⊤ := by
  have hι : Continuous fun x : E ↦ toLp 2 (x, (0 : D)) :=
    (prod_continuous_toLp 2 E D).comp (continuous_id.prodMk continuous_const)
  ext ψ
  obtain ⟨ρ, r, f, h0, h1, hsupp, hr, hf, hρc, δ, hδ, -, htube⟩ := exists_family hU ψ
  refine tendsto_nhds_unique (tendsto_pullbackInl _ hU h ψ h0 h1 hsupp hr hf) ?_
  have hFU : ContinuousOn (fun x ↦ F (toLp 2 (x, (0 : D)))) U := hF.comp hι.continuousOn hU
  rw [ofFun_apply (hFU.locallyIntegrableOn U.isOpen.measurableSet)]
  simp_rw [ofFun_apply (hF.locallyIntegrableOn W.isOpen.measurableSet)]
  refine tendsto_integral_smul_of_tensor ψ.continuous ψ.hasCompactSupport hδ
    (hF.mono ?_) h0 h1 hsupp hr hf hρc
  rintro _ ⟨q, ⟨hq₁, hq₂⟩, rfl⟩
  exact htube q.1 hq₁ q.2 (by simpa using hq₂)

end Distribution
