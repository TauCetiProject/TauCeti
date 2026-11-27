/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import TauCeti.Analysis.Calculus.BumpFunction.Convolution
public import TauCeti.Analysis.Distribution.WaveFrontSet.Localization
import Mathlib.Analysis.LocallyConvex.Barrelled
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import TauCeti.Algebra.Module.ZLattice.Scaling
import TauCeti.Algebra.Module.ZLattice.Summable
import TauCeti.Analysis.Distribution.TestFunction.FourierAtom
import TauCeti.Analysis.Distribution.TestFunction.Frechet
import TauCeti.Analysis.Distribution.TestFunction.LinearEquiv
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.Distribution.TestFunction.Prod
import TauCeti.Analysis.Fourier.Continuous
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

The wave front set of the pullback lies in the image of that of `T` over `E × {0}` under the
transpose `ιᵀ`:

`WF(ι^* T) ⊆ {(x, ξ) | ∃ η, ((x, 0), (ξ, η)) ∈ WF(T)}`

(`Distribution.waveFrontSet_pullbackInl_subset`).

Every injective linear map is such an inclusion after a linear change of coordinates. In
particular, after the change `(x, y) ↦ (x, y - x)` the diagonal of `E × E` becomes `E × {0}`, and
pulling back the tensor product `S ⊗ T` along it is how the product of two distributions with no
opposite wave front covectors over a common point is defined (Hörmander I, Theorem 8.2.10).

## Main declarations

* `Distribution.pullbackInl`: the pullback of `T` along `x ↦ (x, 0)`, under the hypothesis that no
  conormal covector of `E × {0}` over `U` lies in the wave front set of `T`.
* `Distribution.tendsto_pullbackInl`: its values are the limits of `T (ψ ⊗ ρ)` as `ρ` concentrates
  at `0`; `Distribution.exists_seq_tensor_mollifier` supplies such a sequence `ψ ⊗ ρ_n` of test
  functions, built as `TestFunction.tensorBump`.
* `Distribution.pullbackInl_ofFun`: for a continuous function satisfying the hypothesis it is the
  restriction to `E × {0}`.
* `TauCeti.pullbackInlCone Γ`: the cone `ιᵀ Γ = {(x, ξ) | ∃ η, ((x, 0), (ξ, η)) ∈ Γ}`, monotone in
  `Γ` (`TauCeti.pullbackInlCone_mono`).
* `Distribution.isMicrolocallySmoothAt_pullbackInl`, `Distribution.waveFrontSet_pullbackInl_subset`:
  the wave front set of the pullback lies in the image `ιᵀ WF(T)` of that of `T` under `ιᵀ`.
* `Distribution.waveFrontSet_pullbackInl_subset_pullbackInlCone`: so it lies in `ιᵀ Γ` when the
  wave front set of `T` lies in `Γ`.
* `Distribution.localFourier_pullbackInl_eq_tsum`: the localized Fourier transform of the pullback
  as a lattice series of localized Fourier transforms of `T`, for a cutoff `χ` equal to one near
  the support of the cutoff of the pullback, as supplied by
  `TestFunction.exists_cutoff_eq_one_prod_closedBall`.
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

For the wave front set, let `T` be microlocally smooth at every `((x₀, 0), (ξ₀, η))`. Together with
the conormal directions, these covectors form the closed cone `V` of the `ζ` with `ζ.fst` on the ray
through `ξ₀`, so the localized Fourier transform of `T` with a cutoff `χ` near `(x₀, 0)` decays
rapidly on an open cone `Γ ⊇ V \ {0}`. Applying the lattice series to the modulated cutoff `φ e_ξ`,
whose Fourier transform is `𝓕 φ (· + ξ)`, writes the localized Fourier transform of `ι^* T` at `ξ`
as `∑ m, c 𝓕 φ (ξ + m.fst) T (χ e_(-m))`. For `ξ` in a small cone `Γ'` around `ξ₀` and
`-m ∉ Γ`, `‖ξ + m.fst‖ ≥ c' (‖ξ‖ + ‖m‖)` (`IsOpen.exists_cone_mul_add_le_norm_apply_sub`), so
every summand decays rapidly in `ξ` and `m` jointly
(`TauCeti.exists_one_add_norm_pow_mul_one_add_norm_pow_mul_norm_mul_le`).

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

namespace TestFunction

variable {E D : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D]
  {U : Opens E} {W : Opens (WithLp 2 (E × D))}

/-! ### The tensor product of a test function with a normalized bump -/

/-- The product `ψ(x) ρ(y)` of a test function `ψ` with the normalized bump `ρ` of `σ` vanishes off
`supp ψ × closedBall 0 (rOut σ)`. -/
theorem mul_normed_eq_zero_of_notMem [MeasurableSpace D] [BorelSpace D] (ψ : 𝓓(U, ℝ))
    (σ : ContDiffBump (0 : D)) {x : E} {y : D}
    (h : (x, y) ∉ tsupport ψ ×ˢ closedBall (0 : D) σ.rOut) :
    ψ x * σ.normed volume y = 0 := by
  by_cases hx : x ∈ tsupport ψ
  · rw [notMem_support.1 fun hy ↦ h ⟨hx, ball_subset_closedBall
      ((σ.support_normed_eq (μ := volume)).subset hy)⟩, mul_zero]
  · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]

/-- The product of the support of a test function `ψ` with a closed ball about `0`, as a subset of
`WithLp 2 (E × D)`, is compact. -/
theorem isCompact_image_toLp_tsupport_prod_closedBall (ψ : 𝓓(U, ℝ)) (r : ℝ) :
    IsCompact (toLp 2 '' (tsupport ψ ×ˢ closedBall (0 : D) r)) :=
  (ψ.hasCompactSupport.isCompact.prod (isCompact_closedBall _ _)).image
    (prod_continuous_toLp 2 E D)

/-- **The tensor product of a test function with a normalized bump.** The test function
`(x, y) ↦ ψ(x) ρ(y)` on an open set `W` of `E × D` containing `supp ψ × closedBall 0 (rOut σ)`,
for the normalized bump `ρ` of `σ`. -/
def tensorBump [MeasurableSpace D] [BorelSpace D] (ψ : 𝓓(U, ℝ)) (σ : ContDiffBump (0 : D))
    (hW : ∀ x ∈ tsupport ψ, ∀ y ∈ closedBall (0 : D) σ.rOut, toLp 2 (x, y) ∈ W) : 𝓓(W, ℝ) where
  toFun p := ψ p.fst * σ.normed volume p.snd
  contDiff' := (ψ.contDiff.comp (fstL 2 ℝ E D).contDiff).mul
    (σ.contDiff_normed.comp (sndL 2 ℝ E D).contDiff)
  hasCompactSupport' :=
    HasCompactSupport.intro (isCompact_image_toLp_tsupport_prod_closedBall ψ σ.rOut)
    fun _ hp ↦ mul_normed_eq_zero_of_notMem ψ σ (mt (mem_image_of_mem (toLp 2)) hp)
  tsupport_subset' := (closure_minimal (support_subset_iff'.2 fun _ hp ↦
    mul_normed_eq_zero_of_notMem ψ σ (mt (mem_image_of_mem (toLp 2)) hp))
      (isCompact_image_toLp_tsupport_prod_closedBall ψ σ.rOut).isClosed).trans <| by
    rintro _ ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩
    exact hW x hx y hy

/-- The values `(ψ ⊗ ρ) (x, y) = ψ x ρ y` of `TestFunction.tensorBump`. -/
@[simp]
theorem tensorBump_apply [MeasurableSpace D] [BorelSpace D] (ψ : 𝓓(U, ℝ))
    (σ : ContDiffBump (0 : D))
    (hW : ∀ x ∈ tsupport ψ, ∀ y ∈ closedBall (0 : D) σ.rOut, toLp 2 (x, y) ∈ W)
    (p : WithLp 2 (E × D)) :
    tensorBump ψ σ hW p = ψ p.fst * σ.normed volume p.snd :=
  (rfl)

variable [FiniteDimensional ℝ E] in
/-- Around `K × {0}`, for a compact set `K` with `K × {0} ⊆ G ∩ W`, there is a cutoff `χ` supported
in `G`, equal to one on `K × closedBall 0 δ` for some `δ > 0`. -/
theorem exists_cutoff_eq_one_prod_closedBall {K : Set E} (hK : IsCompact K)
    {G : Set (WithLp 2 (E × D))} (hG : IsOpen G) (hKG : ∀ x ∈ K, toLp 2 (x, (0 : D)) ∈ G ∩ W) :
    ∃ δ > 0, ∃ χ : 𝓓(W, ℂ), (∀ x ∈ K, ∀ y : D, ‖y‖ ≤ δ → χ (toLp 2 (x, y)) = 1) ∧
      tsupport χ ⊆ G := by
  obtain ⟨δ, hδ, htube⟩ := hK.exists_pos_forall_toLp_mem (hG.inter W.isOpen) hKG
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
  refine ⟨δ / 2, half_pos hδ, postcompCLM (𝕜 := ℝ) ofRealCLM χ, fun x hx y hy ↦ ?_, ?_⟩
  · have h1 : χ (toLp 2 (x, y)) = 1 :=
      hχ1.self_of_nhdsSet _ ⟨(x, y), ⟨hx, by simpa using hy⟩, rfl⟩
    simp [h1]
  · rw [postcompCLM_apply]
    exact (tsupport_comp_subset (map_zero ofRealCLM) χ).trans (hχG.trans inter_subset_left)

/-- The test function `ψ ⊗ σ` is supported in `supp ψ × closedBall 0 (rOut σ)`. -/
theorem tsupport_tensorBump_subset [MeasurableSpace D] [BorelSpace D] (ψ : 𝓓(U, ℝ))
    (σ : ContDiffBump (0 : D))
    (hW : ∀ x ∈ tsupport ψ, ∀ y ∈ closedBall (0 : D) σ.rOut, toLp 2 (x, y) ∈ W) :
    tsupport (tensorBump ψ σ hW) ⊆ toLp 2 '' (tsupport ψ ×ˢ closedBall (0 : D) σ.rOut) :=
  closure_minimal (support_subset_iff'.2 fun _ hp ↦
    mul_normed_eq_zero_of_notMem ψ σ (mt (mem_image_of_mem (toLp 2)) hp))
    (isCompact_image_toLp_tsupport_prod_closedBall ψ σ.rOut).isClosed

/-- **Integrals against `ψ ⊗ ρ_n` concentrate on `E × {0}`.** Let `ρ_n` be the normalized bumps of
`ContDiffBump.shrinking (r / 2)`. If `G` is continuous at the points `(x, y)` with `x ∈ supp ψ` and
`‖y‖ < r`, then `∫ (ψ ⊗ ρ_n) • G → ∫ ψ x • G (x, 0) dx`. -/
theorem tendsto_integral_tensorBump_smul [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] [MeasurableSpace D] [BorelSpace D] {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [CompleteSpace V] (ψ : 𝓓(U, ℝ)) {r : ℝ} (hr : 0 < r)
    (hW : ∀ n, ∀ x ∈ tsupport ψ,
      ∀ y ∈ closedBall (0 : D) (ContDiffBump.shrinking (c := (0 : D)) (half_pos hr) n).rOut,
      toLp 2 (x, y) ∈ W)
    {G : WithLp 2 (E × D) → V}
    (hG : ∀ x ∈ tsupport ψ, ∀ y : D, ‖y‖ < r → ContinuousAt G (toLp 2 (x, y))) :
    Tendsto (fun n ↦ ∫ p, tensorBump ψ _ (hW n) p • G p) atTop
      (𝓝 (∫ x, ψ x • G (toLp 2 (x, 0)))) := by
  -- `H (x, y) = ψ x • G (x, y)` is continuous on `E × ball 0 r`.
  set H : E × D → V := fun q ↦ ψ q.1 • G (toLp 2 q)
  have hH : ContinuousOn H (univ ×ˢ ball (0 : D) r) := by
    rintro ⟨x, y⟩ ⟨-, hy⟩
    refine ContinuousAt.continuousWithinAt ?_
    by_cases hx : x ∈ tsupport ψ
    · exact (ψ.continuous.comp continuous_fst).continuousAt.smul
        (ContinuousAt.comp (f := fun q : E × D ↦ toLp 2 q)
          (hG x hx y (mem_ball_zero_iff.1 hy)) (prod_continuous_toLp 2 E D).continuousAt)
    · refine (continuousAt_const : ContinuousAt (fun _ : E × D ↦ (0 : V)) (x, y)).congr ?_
      filter_upwards [continuous_fst.continuousAt.eventually
        (notMem_tsupport_iff_eventuallyEq.1 hx)] with q hq
      simp [H, hq]
  refine (ContDiffBump.tendsto_integral_shrinking_normed_smul (μ := volume) (ν := volume)
    ψ.hasCompactSupport.isCompact (fun x y hx ↦ by simp [H, image_eq_zero_of_notMem_tsupport hx])
    hr hH).congr fun n ↦ ?_
  rw [← (volume_preserving_symm_measurableEquiv_toLp_prod E D).symm.integral_comp',
    Measure.volume_eq_prod]
  refine integral_congr_ae (Eventually.of_forall fun q ↦ ?_)
  simp only [MeasurableEquiv.symm_symm, MeasurableEquiv.coe_toLp, tensorBump_apply, toLp_fst,
    toLp_snd, H, mul_comm, mul_smul]

end TestFunction

namespace TauCeti

section Cone

variable {E D : Type*} [Zero D]

/-- The cone `ιᵀ Γ = {(x, ξ) | ∃ η, ((x, 0), (ξ, η)) ∈ Γ}`: the part of `Γ` over `E × {0}`, moved
by the transpose `(ξ, η) ↦ ξ` of the inclusion `ι : x ↦ (x, 0)`. The wave front set of the
pullback along `ι` of a distribution with wave front set in `Γ` lies in it. -/
def pullbackInlCone (Γ : Set (WithLp 2 (E × D) × WithLp 2 (E × D))) : Set (E × E) :=
  {p | ∃ η : D, (toLp 2 (p.1, (0 : D)), toLp 2 (p.2, η)) ∈ Γ}

@[simp]
theorem mem_pullbackInlCone {Γ : Set (WithLp 2 (E × D) × WithLp 2 (E × D))} {p : E × E} :
    p ∈ pullbackInlCone Γ ↔ ∃ η : D, (toLp 2 (p.1, (0 : D)), toLp 2 (p.2, η)) ∈ Γ :=
  Iff.rfl

/-- The cone `ιᵀ Γ` is monotone in `Γ`. -/
@[gcongr]
theorem pullbackInlCone_mono {Γ Γ' : Set (WithLp 2 (E × D) × WithLp 2 (E × D))} (h : Γ ⊆ Γ') :
    pullbackInlCone Γ ⊆ pullbackInlCone Γ' :=
  fun _ ⟨η, hη⟩ ↦ ⟨η, h hη⟩

end Cone

end TauCeti

namespace Distribution

variable {E D : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D]
  {U : Opens E} {W : Opens (WithLp 2 (E × D))}

/-! ### Neighbourhoods of `E × {0}` and decay in the conormal directions -/

omit [FiniteDimensional ℝ E] in
/-- An open cone of `E × D` containing the nonzero conormal vectors `(0, b)` contains a cone
`‖ζ.fst‖ < c ‖ζ.snd‖` around them. -/
private theorem exists_pos_forall_norm_fst_lt_imp_mem {Γ : Set (WithLp 2 (E × D))}
    (hΓ : IsOpen Γ) (hcone : ∀ t : ℝ, 0 < t → ∀ ζ ∈ Γ, t • ζ ∈ Γ)
    (hD : ∀ b : D, b ≠ 0 → toLp 2 ((0 : E), b) ∈ Γ) :
    ∃ c > 0, ∀ ζ : WithLp 2 (E × D), ‖ζ.fst‖ < c * ‖ζ.snd‖ → ζ ∈ Γ := by
  obtain ⟨c, hc, hcΓ⟩ :=
    (hΓ.preimage (prod_continuous_toLp 2 E D)).exists_pos_setOf_norm_fst_lt_subset
      (fun t ht q hq ↦ by simpa using hcone t ht _ hq) hD
  refine ⟨c, hc, fun ζ hζ ↦ ?_⟩
  simpa using hcΓ (a := ofLp ζ) (by simpa using hζ)

/-! ### The limit of `T (ψ ⊗ ρ)` as `ρ` concentrates at `0` -/

/-- The summands `(covolume L)⁻¹ 𝓕 ψ (m.fst) T (χ e_(-m))` of the lattice series for the pullback
decay rapidly, hence are summable over the dual lattice. -/
private theorem summable_norm_fourier_mul_localFourier_neg [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace D] [BorelSpace D] (T : 𝓓'(W, ℂ)) {χ : 𝓓(W, ℂ)}
    (L : Submodule ℤ (WithLp 2 (E × D))) [DiscreteTopology L] [IsZLattice ℝ L] {c : ℝ}
    (hc : 0 < c) (hdecay : ∀ N : ℕ, ∃ C, ∀ ζ : WithLp 2 (E × D),
      ‖ζ.fst‖ < c * ‖ζ.snd‖ → (1 + ‖ζ‖) ^ N * ‖T.localFourier χ ζ‖ ≤ C) (ψ : 𝓓(U, ℝ)) :
    Summable fun m : ZLattice.dual L ↦ ‖(ZLattice.covolume L : ℂ)⁻¹ *
      𝓕 (fun x ↦ (ψ x : ℂ)) (m : WithLp 2 (E × D)).fst * T.localFourier χ (-m)‖ := by
  set a : ℂ := (ZLattice.covolume L : ℂ)⁻¹
  set Ψ : E → ℂ := 𝓕 fun x ↦ (ψ x : ℂ)
  -- Off the cone `‖ζ.fst‖ < c ‖ζ.snd‖`, `‖ζ‖` is comparable to `‖ζ.fst‖`.
  have hsep : ∀ ξ ∈ ({0} : Set E), ∀ ζ ∉ {ζ : WithLp 2 (E × D) | ‖ζ.fst‖ < c * ‖ζ.snd‖},
      c / (1 + c) * (‖ξ‖ + ‖ζ‖) ≤ ‖(-fstL 2 ℝ E D) ζ - ξ‖ := by
    rintro _ rfl ζ hζ
    rw [mem_ofPred_eq, not_lt] at hζ
    have h : c / (1 + c) * ‖ζ‖ ≤ ‖ζ.fst‖ := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left (prod_norm_le_norm_fst_add_norm_snd ζ) hc.le]
    simpa using h
  have h := ZLattice.summable_one_add_norm_pow_mul_norm_of_decay (ZLattice.dual L)
    (f := fun ζ : WithLp 2 (E × D) ↦ a * (Ψ ζ.fst * T.localFourier χ (-ζ)))
    (fun N ↦ by
      obtain ⟨C, hC⟩ := TauCeti.exists_one_add_norm_pow_mul_one_add_norm_pow_mul_norm_mul_le
        (-fstL 2 ℝ E D) (div_pos hc (by positivity)) hsep (g := Ψ)
        (F := fun ζ ↦ T.localFourier χ (-ζ))
        (TauCeti.exists_one_add_norm_pow_mul_norm_fourier_le (ofRealCLM.contDiff.comp ψ.contDiff)
          (ψ.hasCompactSupport.comp_left (g := ((↑) : ℝ → ℂ)) ofReal_zero))
        ((exists_norm_localFourier_le T χ).imp fun _ ⟨k, hk⟩ ↦ ⟨k, fun ζ ↦ by
          simpa using hk (-ζ)⟩)
        (fun N ↦ (hdecay N).imp fun _ hC ζ hζ ↦ by simpa using hC (-ζ) (by simpa using hζ)) N
      exact ⟨‖a‖ * C, fun ζ ↦ by
        have hζ : (1 + ‖ζ‖) ^ N * ‖Ψ ζ.fst * T.localFourier χ (-ζ)‖ ≤ C := by
          simpa using hC 0 rfl ζ
        rw [norm_mul, mul_left_comm]
        exact mul_le_mul_of_nonneg_left hζ (norm_nonneg _)⟩) 0
  simpa [mul_assoc] using h

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
  have hsum := summable_norm_fourier_mul_localFourier_neg T L hc hdecay ψ
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

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ D] in
/-- If `T` has no wave front covectors `((x, 0), (0, η))` in the conormal directions, it is
microlocally smooth at `(x, 0)` in every nonzero direction `ζ` with `ζ.fst = 0`. -/
private theorem isMicrolocallySmoothAt_of_fst_eq_zero (T : 𝓓'(W, ℂ)) {x : E}
    (hx : toLp 2 (x, (0 : D)) ∈ W)
    (h : ∀ η : D, η ≠ 0 → (toLp 2 (x, (0 : D)), toLp 2 ((0 : E), η)) ∉ T.waveFrontSet)
    {ζ : WithLp 2 (E × D)} (hζ0 : ζ ≠ 0) (hζ : ζ.fst = 0) :
    T.IsMicrolocallySmoothAt (toLp 2 (x, 0)) ζ := by
  have hζeq : toLp 2 ((0 : E), ζ.snd) = ζ := by
    rw [← hζ, ← ofLp_fst, ← ofLp_snd, Prod.mk.eta, toLp_ofLp]
  have hsnd : ζ.snd ≠ 0 := fun h0 ↦ hζ0 (by rw [← hζeq, h0, Prod.mk_zero_zero, toLp_zero])
  by_contra hns
  have hmem := mem_waveFrontSet_iff.2 ⟨hx, hζ0, hns⟩
  rw [← hζeq] at hmem
  exact h ζ.snd hsnd hmem

/-- Around `K × {0}`, for a compact set `K` over which `T` has no conormal wave front covectors,
there is a cutoff `χ` equal to one on `K × closedBall 0 δ` whose localized Fourier transform
decays rapidly on a cone `‖ζ.fst‖ < c ‖ζ.snd‖`. -/
private theorem exists_cutoff_decay (T : 𝓓'(W, ℂ)) {K : Set E} (hK : IsCompact K)
    (hKW : ∀ x ∈ K, toLp 2 (x, (0 : D)) ∈ W)
    (h : ∀ x ∈ K, ∀ η : D, η ≠ 0 → (toLp 2 (x, (0 : D)), toLp 2 ((0 : E), η)) ∉ T.waveFrontSet) :
    ∃ δ > 0, ∃ χ : 𝓓(W, ℂ), (∀ x ∈ K, ∀ y : D, ‖y‖ ≤ δ → χ (toLp 2 (x, y)) = 1) ∧
      ∃ c > 0, ∀ N : ℕ, ∃ C, ∀ ζ : WithLp 2 (E × D),
        ‖ζ.fst‖ < c * ‖ζ.snd‖ → (1 + ‖ζ‖) ^ N * ‖T.localFourier χ ζ‖ ≤ C := by
  have hι : Continuous fun x : E ↦ toLp 2 (x, (0 : D)) :=
    (prod_continuous_toLp 2 E D).comp (continuous_id.prodMk continuous_const)
  -- The hypothesis is microlocal smoothness over `K × {0}` in the closed cone `{0} × D`.
  obtain ⟨G, hG, hKG, Γ, hΓ, hVΓ, hcone, hdecay⟩ :=
    exists_isOpen_cone_forall_decay_of_isClosed_cone (T := T) (hK.image hι)
      (V := {ζ : WithLp 2 (E × D) | ζ.fst = 0}) (isClosed_eq (by fun_prop) continuous_const)
      (fun t _ ζ hζ ↦ by simp_all) (by
        rintro _ ⟨x, hx, rfl⟩ ζ hζ hζ0
        exact isMicrolocallySmoothAt_of_fst_eq_zero T (hKW x hx) (h x hx) hζ0 hζ)
  obtain ⟨c, hc, hcΓ⟩ := exists_pos_forall_norm_fst_lt_imp_mem hΓ hcone fun b hb ↦
    hVΓ _ (by simp) fun h0 ↦ hb (by simpa using congrArg WithLp.snd h0)
  obtain ⟨δ, hδ, χ, hχ1, hχG⟩ :=
    exists_cutoff_eq_one_prod_closedBall hK hG fun x hx ↦ ⟨hKG ⟨x, hx, rfl⟩, hKW x hx⟩
  exact ⟨δ, hδ, χ, hχ1, c, hc, fun N ↦ (hdecay χ (hχG.trans subset_union_left) N).imp
    fun _ hC ζ hζ ↦ hC ζ (hcΓ ζ hζ)⟩

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
  (prodContinuousLinearEquiv 2 ℝ E D).symm.transportTestFunction ℝ hVW ∘L
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

/-- **The pullback to `E × {0}` as a limit over bumps.** If `σ i` are bumps centred at `0` whose
outer radii tend to zero, and `f i` are the test functions `(x, y) ↦ ψ x σ_i y` for the normalized
bumps (for instance `TestFunction.tensorBump`), then `T (f i)` tends to the pullback of `T`
evaluated at `ψ`. -/
theorem tendsto_pullbackInl_bump [MeasurableSpace D] [BorelSpace D] (T : 𝓓'(W, ℂ))
    (hU : MapsTo (fun x ↦ toLp 2 (x, (0 : D))) (U : Set E) W)
    (h : ∀ x ∈ U, ∀ η : D, η ≠ 0 →
      (toLp 2 (x, (0 : D)), toLp 2 ((0 : E), η)) ∉ T.waveFrontSet) (ψ : 𝓓(U, ℝ))
    {ι : Type*} {l : Filter ι} {σ : ι → ContDiffBump (0 : D)}
    (hσ : Tendsto (fun i ↦ (σ i).rOut) l (𝓝 0)) {f : ι → 𝓓(W, ℝ)}
    (hf : ∀ᶠ i in l, ∀ p, f i p = ψ p.fst * (σ i).normed volume p.snd) :
    Tendsto (fun i ↦ T (f i)) l (𝓝 (T.pullbackInl hU h ψ)) :=
  tendsto_pullbackInl T hU h ψ (ρ := fun i ↦ (σ i).normed volume) (M := 1)
    (Eventually.of_forall fun i ↦ by
      simp_rw [abs_of_nonneg ((σ i).nonneg_normed _), (σ i).integral_normed, le_refl])
    (by simp_rw [ContDiffBump.integral_normed, tendsto_const_nhds])
    (Eventually.of_forall fun i ↦ by
      simpa only [(σ i).support_normed_eq] using ball_subset_closedBall)
    hσ hf

/-- **The pullback to `E × {0}` as a limit over products of bumps.** Let `D₁ × D₂` be a product of
finite-dimensional spaces. If `ρ i` and `σ i` are bumps centred at `0` in `D₁` and `D₂` whose outer
radii tend to zero, and `f i` are the test functions `(x, (y, z)) ↦ ψ x ρ_i y σ_i z` for the
normalized bumps, then `T (f i)` tends to the pullback of `T` evaluated at `ψ`. -/
theorem tendsto_pullbackInl_prod_bump {D₁ D₂ : Type*} [NormedAddCommGroup D₁]
    [InnerProductSpace ℝ D₁] [FiniteDimensional ℝ D₁] [MeasurableSpace D₁] [BorelSpace D₁]
    [NormedAddCommGroup D₂] [InnerProductSpace ℝ D₂] [FiniteDimensional ℝ D₂] [MeasurableSpace D₂]
    [BorelSpace D₂] {W : Opens (WithLp 2 (E × WithLp 2 (D₁ × D₂)))} (T : 𝓓'(W, ℂ))
    (hU : MapsTo (fun x ↦ toLp 2 (x, (0 : WithLp 2 (D₁ × D₂)))) (U : Set E) W)
    (h : ∀ x ∈ U, ∀ η : WithLp 2 (D₁ × D₂), η ≠ 0 →
      (toLp 2 (x, (0 : WithLp 2 (D₁ × D₂))), toLp 2 ((0 : E), η)) ∉ T.waveFrontSet)
    (ψ : 𝓓(U, ℝ)) {ι : Type*} {l : Filter ι} {ρ : ι → ContDiffBump (0 : D₁)}
    {σ : ι → ContDiffBump (0 : D₂)} (hr : Tendsto (fun i ↦ (ρ i).rOut + (σ i).rOut) l (𝓝 0))
    {f : ι → 𝓓(W, ℝ)} (hf : ∀ᶠ i in l, ∀ p,
      f i p = ψ p.fst * ((ρ i).normed volume p.snd.fst * (σ i).normed volume p.snd.snd)) :
    Tendsto (fun i ↦ T (f i)) l (𝓝 (T.pullbackInl hU h ψ)) := by
  -- The products `ρ_i ⊗ σ_i` are nonnegative of integral one, supported in the closed balls of
  -- radii `rOut (ρ i) + rOut (σ i)`.
  have hprod (i : ι) :
      ∫ d : WithLp 2 (D₁ × D₂), (ρ i).normed volume d.fst * (σ i).normed volume d.snd = 1 := by
    rw [← (volume_preserving_symm_measurableEquiv_toLp_prod D₁ D₂).symm.integral_comp']
    simp only [MeasurableEquiv.symm_symm, MeasurableEquiv.coe_toLp, toLp_fst, toLp_snd]
    rw [Measure.volume_eq_prod, integral_prod_mul, ContDiffBump.integral_normed,
      ContDiffBump.integral_normed, one_mul]
  refine tendsto_pullbackInl T hU h ψ
    (ρ := fun i d ↦ (ρ i).normed volume d.fst * (σ i).normed volume d.snd) (M := 1)
    (Eventually.of_forall fun i ↦ ?_) (by simp_rw [hprod, tendsto_const_nhds])
    (Eventually.of_forall fun i d hd ↦ ?_) hr hf
  · exact ((integral_congr_ae (Eventually.of_forall fun d ↦ abs_of_nonneg
      (mul_nonneg ((ρ i).nonneg_normed _) ((σ i).nonneg_normed _)))).trans (hprod i)).le
  · rw [mem_support, mul_ne_zero_iff] at hd
    have h₁ : d.fst ∈ ball (0 : D₁) (ρ i).rOut := by
      rw [← (ρ i).support_normed_eq (μ := volume)]
      exact hd.1
    have h₂ : d.snd ∈ ball (0 : D₂) (σ i).rOut := by
      rw [← (σ i).support_normed_eq (μ := volume)]
      exact hd.2
    rw [mem_ball_zero_iff] at h₁ h₂
    exact mem_closedBall_zero_iff.2
      ((WithLp.prod_norm_le_norm_fst_add_norm_snd d).trans (add_le_add h₁.le h₂.le))

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
as in `Distribution.tendsto_pullbackInl`, where `ρ_n` is the normalized bump function of a bump
`σ_n` centred at `0`: a smooth nonnegative function of integral one supported in the closed ball of
radius `rOut (σ_n)`. These radii tend to zero, and the product of `supp ψ` with each of these closed
balls lies in `W`. -/
theorem exists_seq_tensor_mollifier [MeasurableSpace D] [BorelSpace D]
    (hU : MapsTo (fun x ↦ toLp 2 (x, (0 : D))) (U : Set E) W) (ψ : 𝓓(U, ℝ)) :
    ∃ (σ : ℕ → ContDiffBump (0 : D)) (f : ℕ → 𝓓(W, ℝ)),
      Tendsto (fun n ↦ (σ n).rOut) atTop (𝓝 0) ∧
      (∀ n, ∀ x ∈ tsupport ψ, ∀ y ∈ closedBall (0 : D) (σ n).rOut, toLp 2 (x, y) ∈ W) ∧
      ∀ n p, f n p = ψ p.fst * (σ n).normed volume p.snd := by
  set K : Compacts E := ⟨tsupport ψ, ψ.hasCompactSupport⟩
  have hδ := tubeRadius_pos hU K ψ.tsupport_subset
  have hW (n : ℕ) : ∀ x ∈ tsupport ψ,
      ∀ y ∈ closedBall (0 : D) (ContDiffBump.shrinking (c := (0 : D)) (half_pos hδ) n).rOut,
      toLp 2 (x, y) ∈ W := fun x hx y hy ↦
    toLp_mem_of_lt_tubeRadius hU K ψ.tsupport_subset hx (by simpa using hδ) <|
      (mem_closedBall_zero_iff.1 hy).trans_lt
        ((ContDiffBump.rOut_shrinking_le (half_pos hδ) n).trans_lt (half_lt_self hδ))
  exact ⟨fun n ↦ ContDiffBump.shrinking (half_pos hδ) n, fun n ↦ tensorBump ψ _ (hW n),
    ContDiffBump.tendsto_rOut_shrinking (half_pos hδ), hW, fun n ↦ tensorBump_apply ψ _ (hW n)⟩

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

/-! ### The wave front set of the pullback -/

/-- **The pullback as a lattice series.** For a real test function `ψ` on `U` and a cutoff `χ`
equal to one on `tsupport ψ × closedBall 0 δ` whose localized Fourier transform decays rapidly on a
cone `‖ζ.fst‖ < c ‖ζ.snd‖`, the pullback of `T` at `ψ` is the lattice series
`∑ m, (covolume L)⁻¹ 𝓕 ψ (m.fst) T (χ e_(-m))`. -/
private theorem pullbackInl_apply_eq_tsum [MeasurableSpace E] [BorelSpace E] [MeasurableSpace D]
    [BorelSpace D] (T : 𝓓'(W, ℂ)) (hU : MapsTo (fun x ↦ toLp 2 (x, (0 : D))) (U : Set E) W)
    (h : ∀ x ∈ U, ∀ η : D, η ≠ 0 →
      (toLp 2 (x, (0 : D)), toLp 2 ((0 : E), η)) ∉ T.waveFrontSet) {ψ : 𝓓(U, ℝ)} {χ : 𝓓(W, ℂ)}
    {δ : ℝ} (hδ : 0 < δ) (hχ : ∀ x ∈ tsupport ψ, ∀ y : D, ‖y‖ ≤ δ → χ (toLp 2 (x, y)) = 1)
    (L : Submodule ℤ (WithLp 2 (E × D))) [DiscreteTopology L] [IsZLattice ℝ L]
    (hL : ∀ p ∈ tsupport χ, ∀ ℓ ∈ L, p + ℓ ∈ tsupport χ → ℓ = 0) {c : ℝ} (hc : 0 < c)
    (hdecay : ∀ N : ℕ, ∃ C, ∀ ζ : WithLp 2 (E × D),
      ‖ζ.fst‖ < c * ‖ζ.snd‖ → (1 + ‖ζ‖) ^ N * ‖T.localFourier χ ζ‖ ≤ C) :
    T.pullbackInl hU h ψ = ∑' m : ZLattice.dual L, (ZLattice.covolume L : ℂ)⁻¹ *
      𝓕 (fun x ↦ (ψ x : ℂ)) (m : WithLp 2 (E × D)).fst * T.localFourier χ (-m) := by
  obtain ⟨σ, f, hr, -, hf⟩ := exists_seq_tensor_mollifier hU ψ
  set ρ : ℕ → D → ℝ := fun n ↦ (σ n).normed volume
  have hM : ∀ᶠ n in atTop, ∫ y, |ρ n y| ≤ 1 := Eventually.of_forall fun n ↦ by
    simp_rw [ρ, abs_of_nonneg ((σ n).nonneg_normed _), (σ n).integral_normed, le_rfl]
  have h1 : Tendsto (fun n ↦ ∫ y, ρ n y) atTop (𝓝 1) := by
    simp_rw [ρ, ContDiffBump.integral_normed, tendsto_const_nhds]
  have hρr (n : ℕ) : support (ρ n) ⊆ closedBall 0 (σ n).rOut := by
    simpa only [ρ, (σ n).support_normed_eq] using ball_subset_closedBall
  exact tendsto_nhds_unique
    (tendsto_pullbackInl T hU h ψ hM h1 (Eventually.of_forall hρr) hr (Eventually.of_forall hf))
    (tendsto_apply_tsum T hδ hχ L hL hc hdecay hM h1 (Eventually.of_forall hρr) hr
      (Eventually.of_forall hf))

/-- `Distribution.pullbackInl_apply_eq_tsum` for a complex test function `ψ`, through its real and
imaginary parts. -/
private theorem complexPairing_pullbackInl_eq_tsum [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace D] [BorelSpace D] (T : 𝓓'(W, ℂ))
    (hU : MapsTo (fun x ↦ toLp 2 (x, (0 : D))) (U : Set E) W)
    (h : ∀ x ∈ U, ∀ η : D, η ≠ 0 →
      (toLp 2 (x, (0 : D)), toLp 2 ((0 : E), η)) ∉ T.waveFrontSet) {ψ : 𝓓(U, ℂ)} {χ : 𝓓(W, ℂ)}
    {δ : ℝ} (hδ : 0 < δ) (hχ : ∀ x ∈ tsupport ψ, ∀ y : D, ‖y‖ ≤ δ → χ (toLp 2 (x, y)) = 1)
    (L : Submodule ℤ (WithLp 2 (E × D))) [DiscreteTopology L] [IsZLattice ℝ L]
    (hL : ∀ p ∈ tsupport χ, ∀ ℓ ∈ L, p + ℓ ∈ tsupport χ → ℓ = 0) {c : ℝ} (hc : 0 < c)
    (hdecay : ∀ N : ℕ, ∃ C, ∀ ζ : WithLp 2 (E × D),
      ‖ζ.fst‖ < c * ‖ζ.snd‖ → (1 + ‖ζ‖) ^ N * ‖T.localFourier χ ζ‖ ≤ C) :
    (T.pullbackInl hU h).complexPairing ψ = ∑' m : ZLattice.dual L,
      (ZLattice.covolume L : ℂ)⁻¹ * 𝓕 (ψ : E → ℂ) (m : WithLp 2 (E × D)).fst *
        T.localFourier χ (-m) := by
  set ψr : 𝓓(U, ℝ) := postcompCLM (𝕜 := ℝ) reCLM ψ
  set ψi : 𝓓(U, ℝ) := postcompCLM (𝕜 := ℝ) imCLM ψ
  have hsupp (g : ℂ →L[ℝ] ℝ) (x : E) (hx : x ∈ tsupport (postcompCLM (𝕜 := ℝ) g ψ)) :
      x ∈ tsupport ψ := by
    rw [postcompCLM_apply] at hx
    exact tsupport_comp_subset (map_zero g) ψ hx
  have hint (φ : 𝓓(U, ℝ)) : Integrable fun x ↦ (φ x : ℂ) :=
    (continuous_ofReal.comp φ.continuous).integrable_of_hasCompactSupport
      (φ.hasCompactSupport.comp_left ofReal_zero)
  -- `ψ = ψr + I ψi`, so `𝓕 ψ = 𝓕 ψr + I 𝓕 ψi`.
  have hF : 𝓕 (ψ : E → ℂ) = 𝓕 (fun x ↦ (ψr x : ℂ)) + I • 𝓕 (fun x ↦ (ψi x : ℂ)) := by
    have hfun : (ψ : E → ℂ) = (fun x ↦ (ψr x : ℂ)) + I • fun x ↦ (ψi x : ℂ) := by
      ext x
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, ψr, ψi, postcompCLM_apply,
        Function.comp_apply, reCLM_apply, imCLM_apply]
      rw [mul_comm]
      exact (re_add_im _).symm
    rw [hfun, (hint ψr).fourier_add ((hint ψi).smul I),
      Real.fourier_const_smul]
  have hr := (summable_norm_fourier_mul_localFourier_neg T L hc hdecay ψr).of_norm
  have hi := (summable_norm_fourier_mul_localFourier_neg T L hc hdecay ψi).of_norm
  rw [complexPairing_apply,
    pullbackInl_apply_eq_tsum T hU h hδ (fun x hx ↦ hχ x (hsupp reCLM x hx)) L hL hc hdecay,
    pullbackInl_apply_eq_tsum T hU h hδ (fun x hx ↦ hχ x (hsupp imCLM x hx)) L hL hc hdecay]
  refine ((hr.hasSum.add (hi.hasSum.mul_left I)).congr_fun fun m ↦ ?_).tsum_eq.symm
  simp only [hF, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- **The localized Fourier transform of the pullback as a lattice series.** Let `χ` be equal to
one on `tsupport φ × closedBall 0 δ`, let the translates of `tsupport χ` by the lattice `L` meet it
only for the translation `0`, and let the localized Fourier transform of `T` with cutoff `χ` decay
rapidly on the cone `‖ζ.fst‖ < c ‖ζ.snd‖`. Then

`ι^* T (φ e_ξ) = ∑ m ∈ L*, (covolume L)⁻¹ 𝓕 φ (ξ + m.fst) T (χ e_(-m))`. -/
theorem localFourier_pullbackInl_eq_tsum [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace D] [BorelSpace D] (T : 𝓓'(W, ℂ))
    (hU : MapsTo (fun x ↦ toLp 2 (x, (0 : D))) (U : Set E) W)
    (h : ∀ x ∈ U, ∀ η : D, η ≠ 0 →
      (toLp 2 (x, (0 : D)), toLp 2 ((0 : E), η)) ∉ T.waveFrontSet) {φ : 𝓓(U, ℂ)} {χ : 𝓓(W, ℂ)}
    {δ : ℝ} (hδ : 0 < δ) (hχ : ∀ x ∈ tsupport φ, ∀ y : D, ‖y‖ ≤ δ → χ (toLp 2 (x, y)) = 1)
    (L : Submodule ℤ (WithLp 2 (E × D))) [DiscreteTopology L] [IsZLattice ℝ L]
    (hL : ∀ p ∈ tsupport χ, ∀ ℓ ∈ L, p + ℓ ∈ tsupport χ → ℓ = 0) {c : ℝ} (hc : 0 < c)
    (hdecay : ∀ N : ℕ, ∃ C, ∀ ζ : WithLp 2 (E × D),
      ‖ζ.fst‖ < c * ‖ζ.snd‖ → (1 + ‖ζ‖) ^ N * ‖T.localFourier χ ζ‖ ≤ C) (ξ : E) :
    (T.pullbackInl hU h).localFourier φ ξ = ∑' m : ZLattice.dual L,
      (ZLattice.covolume L : ℂ)⁻¹ * (𝓕 (φ : E → ℂ) (ξ + (m : WithLp 2 (E × D)).fst) *
        T.localFourier χ (-m)) := by
  rw [localFourier_def, complexPairing_pullbackInl_eq_tsum T hU h hδ ?_ L hL hc hdecay]
  · congr 1 with m
    rw [TestFunction.fourier_bilinLeftCLM_fourierAtom, add_comm, mul_assoc]
  · intro x hx y hy
    refine hχ x ?_ y hy
    simp only [bilinLeftCLM_apply, ContinuousLinearMap.mul_apply'] at hx
    exact tsupport_mul_subset_left hx

/-- **Rapid decay of the localized Fourier transform of the pullback.** Let `χ` be equal to one on
`tsupport φ × closedBall 0 δ`, with localized Fourier transform rapidly decreasing on an open set
`Γ` containing the cone `‖ζ.fst‖ < c ‖ζ.snd‖`. If the first components of the covectors outside
`Γ` stay away from a set `Γ'` of frequencies, then the localized Fourier transform of the pullback
with cutoff `φ` decays rapidly on `Γ'`. -/
private theorem exists_decay_localFourier_pullbackInl [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace D] [BorelSpace D] (T : 𝓓'(W, ℂ))
    (hU : MapsTo (fun x ↦ toLp 2 (x, (0 : D))) (U : Set E) W)
    (h : ∀ x ∈ U, ∀ η : D, η ≠ 0 →
      (toLp 2 (x, (0 : D)), toLp 2 ((0 : E), η)) ∉ T.waveFrontSet) {φ : 𝓓(U, ℂ)} {χ : 𝓓(W, ℂ)}
    {δ : ℝ} (hδ : 0 < δ) (hχ : ∀ x ∈ tsupport φ, ∀ y : D, ‖y‖ ≤ δ → χ (toLp 2 (x, y)) = 1)
    {Γ : Set (WithLp 2 (E × D))} {c : ℝ} (hc : 0 < c)
    (hcΓ : ∀ ζ : WithLp 2 (E × D), ‖ζ.fst‖ < c * ‖ζ.snd‖ → ζ ∈ Γ)
    (hdecay : ∀ N : ℕ, ∃ C, ∀ ζ ∈ Γ, (1 + ‖ζ‖) ^ N * ‖T.localFourier χ ζ‖ ≤ C) {Γ' : Set E}
    {c' : ℝ} (hc' : 0 < c') (hsep : ∀ ξ ∈ Γ', ∀ ζ ∉ Γ, c' * (‖ξ‖ + ‖ζ‖) ≤ ‖fstL 2 ℝ E D ζ - ξ‖)
    (N : ℕ) : ∃ C, ∀ ξ ∈ Γ', (1 + ‖ξ‖) ^ N * ‖(T.pullbackInl hU h).localFourier φ ξ‖ ≤ C := by
  obtain ⟨L, _, _, hL⟩ :=
    ZLattice.exists_forall_add_mem_eq_zero_of_isBounded χ.hasCompactSupport.isCompact.isBounded
  set q := Module.finrank ℤ (ZLattice.dual L) + 1
  have hsum := ZLattice.summable_one_add_norm_pow_inv (ZLattice.dual L) (r := q) (by omega)
  -- The summands `𝓕 φ (ξ + m.fst) T (χ e_(-m))` of the lattice series decay jointly in `ξ ∈ Γ'`
  -- and `m`.
  obtain ⟨C, hC⟩ := TauCeti.exists_one_add_norm_pow_mul_one_add_norm_pow_mul_norm_mul_le
    (fstL 2 ℝ E D) hc' hsep
    (fun N ↦ TauCeti.exists_one_add_norm_pow_mul_norm_fourier_le φ.contDiff φ.hasCompactSupport N)
    (exists_norm_localFourier_le T χ) hdecay (N + q)
  set a : ℂ := (ZLattice.covolume L : ℂ)⁻¹
  refine ⟨‖a‖ * C * ∑' m : ZLattice.dual L, ((1 + ‖(m : WithLp 2 (E × D))‖) ^ q)⁻¹,
    fun ξ hξ ↦ ?_⟩
  have hterm (m : ZLattice.dual L) :
      ‖a * (𝓕 (φ : E → ℂ) (ξ + (m : WithLp 2 (E × D)).fst) * T.localFourier χ (-m))‖ ≤
        ‖a‖ * C * ((1 + ‖ξ‖) ^ N)⁻¹ * ((1 + ‖(m : WithLp 2 (E × D))‖) ^ q)⁻¹ := by
    set P := ‖𝓕 (φ : E → ℂ) (ξ + (m : WithLp 2 (E × D)).fst) * T.localFourier χ (-m)‖
    have h1 : (1 + ‖ξ‖) ^ (N + q) * ((1 + ‖(m : WithLp 2 (E × D))‖) ^ (N + q) * P) ≤ C := by
      simpa [P] using hC ξ hξ (-(m : WithLp 2 (E × D)))
    have hle : (1 + ‖ξ‖) ^ N * ((1 + ‖(m : WithLp 2 (E × D))‖) ^ q * P) ≤ C :=
      le_trans (by gcongr <;> first | exact le_add_of_nonneg_right (norm_nonneg _) | omega) h1
    rw [norm_mul, mul_assoc ‖a‖, mul_assoc ‖a‖]
    gcongr
    rw [mul_assoc, ← mul_inv, le_mul_inv_iff₀ (by positivity)]
    linarith [hle]
  have hle := tsum_of_norm_bounded (hsum.hasSum.mul_left (‖a‖ * C * ((1 + ‖ξ‖) ^ N)⁻¹)) hterm
  have hX : (1 + ‖ξ‖) ^ N ≠ 0 := by positivity
  rw [localFourier_pullbackInl_eq_tsum T hU h hδ hχ L hL hc
    (fun N ↦ (hdecay N).imp fun _ hC ζ hζ ↦ hC ζ (hcΓ ζ hζ))]
  calc (1 + ‖ξ‖) ^ N * ‖∑' m : ZLattice.dual L,
        a * (𝓕 (φ : E → ℂ) (ξ + (m : WithLp 2 (E × D)).fst) * T.localFourier χ (-m))‖
      ≤ (1 + ‖ξ‖) ^ N * (‖a‖ * C * ((1 + ‖ξ‖) ^ N)⁻¹ *
          ∑' m : ZLattice.dual L, ((1 + ‖(m : WithLp 2 (E × D))‖) ^ q)⁻¹) := by gcongr
    _ = _ := by field_simp

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ D] in
/-- If `T` is microlocally smooth at the covectors `((x₀, 0), (ξ₀, η))` for every `η`, and has no
wave front set in the conormal directions `((x₀, 0), (0, η))`, then it is microlocally smooth at
`(x₀, 0)` in every nonzero direction whose first component lies on the ray through `ξ₀`. -/
private theorem isMicrolocallySmoothAt_of_fst_eq_smul (T : 𝓓'(W, ℂ)) {x₀ ξ₀ : E}
    (hx₀ : toLp 2 (x₀, (0 : D)) ∈ W) (h : ∀ η : D, η ≠ 0 →
      (toLp 2 (x₀, (0 : D)), toLp 2 ((0 : E), η)) ∉ T.waveFrontSet)
    (hT : ∀ η : D, T.IsMicrolocallySmoothAt (toLp 2 (x₀, 0)) (toLp 2 (ξ₀, η)))
    {ζ : WithLp 2 (E × D)} (hζ0 : ζ ≠ 0) {s : ℝ} (hs : 0 ≤ s) (hsζ : s • ξ₀ = ζ.fst) :
    T.IsMicrolocallySmoothAt (toLp 2 (x₀, 0)) ζ := by
  rcases hs.eq_or_lt with rfl | hs
  · -- A conormal direction.
    rw [zero_smul] at hsζ
    exact isMicrolocallySmoothAt_of_fst_eq_zero T hx₀ h hζ0 hsζ.symm
  · -- `ζ = s (ξ₀, s⁻¹ ζ.snd)` with `s > 0`, and microlocal smoothness is conic.
    have hζs : s • toLp 2 (ξ₀, s⁻¹ • ζ.snd) = ζ := by
      rw [← toLp_smul, Prod.smul_mk, smul_smul, mul_inv_cancel₀ hs.ne', one_smul, hsζ, ← ofLp_fst,
        ← ofLp_snd, Prod.mk.eta, toLp_ofLp]
    rw [← hζs, isMicrolocallySmoothAt_smul_iff hs]
    exact hT _

/-- **The wave front set of the pullback to `E × {0}`, pointwise** (Hörmander I, Theorem 8.2.4).
Let `ξ₀ ≠ 0`. If `T` is microlocally smooth at the covectors `((x₀, 0), (ξ₀, η))` for every
`η ∈ D`, that is, at every covector over `(x₀, 0)` which the transpose `(ξ, η) ↦ ξ` of the
inclusion sends to `ξ₀`, then the pullback of `T` to `E × {0}` is microlocally smooth at
`(x₀, ξ₀)`. -/
theorem isMicrolocallySmoothAt_pullbackInl (T : 𝓓'(W, ℂ))
    (hU : MapsTo (fun x ↦ toLp 2 (x, (0 : D))) (U : Set E) W)
    (h : ∀ x ∈ U, ∀ η : D, η ≠ 0 →
      (toLp 2 (x, (0 : D)), toLp 2 ((0 : E), η)) ∉ T.waveFrontSet) {x₀ ξ₀ : E} (hx₀ : x₀ ∈ U)
    (hξ₀ : ξ₀ ≠ 0) (hT : ∀ η : D, T.IsMicrolocallySmoothAt (toLp 2 (x₀, 0)) (toLp 2 (ξ₀, η))) :
    (T.pullbackInl hU h).IsMicrolocallySmoothAt x₀ ξ₀ := by
  borelize E D
  -- `T` decays at `(x₀, 0)` on an open cone `Γ` around the closed cone `V` of the covectors whose
  -- first component lies on the ray through `ξ₀`, which contains the conormal directions.
  set V : Set (WithLp 2 (E × D)) := WithLp.fst ⁻¹' ((fun s : ℝ ↦ s • ξ₀) '' Ici 0)
  obtain ⟨G, hG, hp₀G, Γ, hΓ, hVΓ, hcone, hdecay⟩ :=
    exists_isOpen_cone_forall_decay_of_isClosed_cone (T := T) (V := V) isCompact_singleton
      ((isClosedMap_smul_left ξ₀ _ isClosed_Ici).preimage (by fun_prop))
      (fun t ht ζ ⟨s, hs, hsζ⟩ ↦ ⟨t * s, mul_nonneg ht.le hs, by simp [← hsζ, smul_smul]⟩)
      fun p hp ζ ⟨s, hs, hsζ⟩ hζ0 ↦ (mem_singleton_iff.1 hp) ▸
        isMicrolocallySmoothAt_of_fst_eq_smul T (hU hx₀) (h x₀ hx₀) hT hζ0 hs hsζ
  obtain ⟨c, hc, hcΓ⟩ := exists_pos_forall_norm_fst_lt_imp_mem hΓ hcone fun b hb ↦
    hVΓ _ ⟨0, le_rfl, by simp⟩ fun h0 ↦ hb (by simpa using congrArg WithLp.snd h0)
  -- Off `Γ`, the first component of a covector stays away from a cone `Γ'` around `ξ₀`.
  obtain ⟨Γ', hΓ', hξ₀Γ', hcone', c', hc', hsep⟩ :=
    hΓ.exists_cone_mul_add_le_norm_apply_sub hcone (fstL 2 ℝ E D) hξ₀
      fun ζ hζ s hs hζs ↦ hVΓ ζ ⟨s, hs, hζs.symm⟩ hζ
  -- A cutoff `φ` near `x₀` and a cutoff `χ` supported in `G`, equal to one on
  -- `tsupport φ × closedBall 0 δ`.
  obtain ⟨r, hr, htube⟩ := isCompact_singleton.exists_pos_forall_toLp_mem (hG.inter W.isOpen)
    fun x hx ↦ by
      rw [mem_singleton_iff.1 hx]
      exact ⟨hp₀G (mem_singleton _), hU hx₀⟩
  obtain ⟨δ, hδ, χ, hχ1, hχG⟩ :=
    exists_cutoff_eq_one_prod_closedBall (isCompact_closedBall x₀ (r / 2)) hG fun x hx ↦
      htube x₀ rfl x 0 ((mem_closedBall.1 hx).trans_lt (half_lt_self hr)) (by simpa using hr)
  obtain ⟨φ, -, hφ1, hφ⟩ := exists_cutoff_tsupport_subset (Ω := U) (n := ⊤)
    (isCompact_singleton (x := x₀)) (isOpen_ball.inter U.isOpen)
    (singleton_subset_iff.2 ⟨mem_ball_self (half_pos hr), hx₀⟩) inter_subset_right
  have hφK : tsupport (postcompCLM (𝕜 := ℝ) ofRealCLM φ) ⊆ closedBall x₀ (r / 2) := by
    rw [postcompCLM_apply]
    exact ((tsupport_comp_subset (map_zero ofRealCLM) φ).trans hφ).trans
      (inter_subset_left.trans ball_subset_closedBall)
  refine isMicrolocallySmoothAt_iff.2 ⟨postcompCLM (𝕜 := ℝ) ofRealCLM φ,
    by simp [postcompCLM_apply, hφ1.self_of_nhdsSet x₀ rfl], Γ', hΓ', hξ₀Γ', hcone',
    exists_decay_localFourier_pullbackInl T hU h hδ (fun x hx ↦ hχ1 x (hφK hx)) hc hcΓ
      (hdecay χ (hχG.trans subset_union_left)) hc' hsep⟩

/-- **The wave front set of the pullback to `E × {0}`** (Hörmander I, Theorem 8.2.4). The
transpose of the inclusion `ι : x ↦ (x, 0)` is `ιᵀ (ξ, η) = ξ`, and the wave front set of the
pullback `ι^* T` lies in the image of the wave front set of `T` over `E × {0}` under `ιᵀ`:

`WF(ι^* T) ⊆ {(x, ξ) | ∃ η, ((x, 0), (ξ, η)) ∈ WF(T)}`. -/
theorem waveFrontSet_pullbackInl_subset (T : 𝓓'(W, ℂ))
    (hU : MapsTo (fun x ↦ toLp 2 (x, (0 : D))) (U : Set E) W)
    (h : ∀ x ∈ U, ∀ η : D, η ≠ 0 →
      (toLp 2 (x, (0 : D)), toLp 2 ((0 : E), η)) ∉ T.waveFrontSet) :
    (T.pullbackInl hU h).waveFrontSet ⊆ TauCeti.pullbackInlCone T.waveFrontSet := by
  rintro ⟨x, ξ⟩ hxξ
  obtain ⟨hx, hξ, hns⟩ := mem_waveFrontSet_iff.1 hxξ
  by_contra hmem
  refine hns (isMicrolocallySmoothAt_pullbackInl T hU h hx hξ fun η ↦ ?_)
  by_contra hns'
  refine hmem ⟨η, mem_waveFrontSet_iff.2 ⟨hU hx, fun h0 ↦ hξ ?_, hns'⟩⟩
  simpa using congrArg WithLp.fst h0

/-- The wave front set of the pullback to `E × {0}` of a distribution with wave front set in `Γ`
lies in the cone `ιᵀ Γ`. -/
theorem waveFrontSet_pullbackInl_subset_pullbackInlCone
    {Γ : Set (WithLp 2 (E × D) × WithLp 2 (E × D))}
    (hU : MapsTo (fun x ↦ toLp 2 (x, (0 : D))) (U : Set E) W) {T : 𝓓'(W, ℂ)}
    (h : ∀ x ∈ U, ∀ η : D, η ≠ 0 →
      (toLp 2 (x, (0 : D)), toLp 2 ((0 : E), η)) ∉ T.waveFrontSet)
    (hT : T.waveFrontSet ⊆ Γ) : (T.pullbackInl hU h).waveFrontSet ⊆ TauCeti.pullbackInlCone Γ :=
  (waveFrontSet_pullbackInl_subset T hU h).trans (TauCeti.pullbackInlCone_mono hT)

end Distribution
