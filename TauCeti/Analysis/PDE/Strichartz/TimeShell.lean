/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Strichartz.TTStar
import TauCeti.Analysis.PDE.Strichartz.Localized
import Mathlib.Data.Int.Log
import TauCeti.MeasureTheory.Function.L2Space
import TauCeti.MeasureTheory.Function.Lp.Integral.Functional
import TauCeti.MeasureTheory.Measure.Lebesgue.Basic
import TauCeti.MeasureTheory.Measure.Prod

/-!
# The `TT*` pairings on dyadic time shells

Let `U(t) : H → L²(X, μ)`, `t ∈ ℝ`, be bounded operators from a Hilbert space into an `L²` space,
such as the Schrödinger propagator `exp(itΔ)`. The `TT*` argument of
`TauCeti/Analysis/PDE/Strichartz/TTStar.lean` reduces Strichartz estimates to the bilinear form

`T(F, G) = ∫∫ ⟪U(s)* F(s), U(t)* G(t)⟫ ds dt`

of time-dependent `F, G : ℝ → L²(X, μ)`, and bounds it by the Hardy–Littlewood–Sobolev inequality
in time. At the endpoint `q = 2` of the admissible exponents that inequality fails, and Keel and
Tao instead decompose `T` according to the size of `|s - t|`. This file supplies that
decomposition and the bounds for its pieces at the three exponent pairs from which the endpoint
argument starts.

The **dyadic time shell** `timeShell ρ` is the set of pairs `(s, t)` with `ρ ≤ |s - t| < 2ρ`. For
`ρ = 2ʲ`, `j ∈ ℤ`, the shells are disjoint and cover the pairs of distinct times
(`TauCeti.pairwise_disjoint_timeShell_zpow`, `TauCeti.iUnion_timeShell_zpow`); since the diagonal
is a null set, the integral of an integrable function on `ℝ × ℝ` is the sum of its integrals over
the shells (`TauCeti.hasSum_setIntegral_timeShell`). The restriction of `T` to a shell is bounded
in three ways, all in mixed norms `L²_t L^a_x`:

* **At equal exponents** (`TauCeti.setLIntegral_timeShell_enorm_inner_adjoint_le`): if the time
  pairings decay like `‖U(s) U(t)* g‖_r ≤ A |s - t| ^ (-γ) ‖g‖_{r'}`, `γ ≥ 0`, then the integral of
  `|⟪U(s)* F(s), U(t)* G(t)⟫|` over the shell is at most `4 A ρ ^ (1 - γ) ‖F‖_{L² L^{r'}}
  ‖G‖_{L² L^{r'}}`. On the shell the pairing decay is at least `ρ ^ (-γ)`, and the sections of
  the shell are windows of length `2ρ`, so the sliding-window decay bound
  `TauCeti.lintegral_setLIntegral_sub_preimage_enorm_inner_adjoint_le` does the time integral.
  With the dispersive estimate, `r = ∞` and `γ = σ`, this is the bound at the pair `(∞, ∞)`.
* **With an energy factor** (`TauCeti.enorm_setIntegral_timeShell_inner_adjoint_le` and
  `TauCeti.enorm_setIntegral_timeShell_inner_adjoint_le'`): if `‖U(t)‖ ≤ M` and the dual estimate
  `‖∫ U(t)* G(t) dt‖ ≤ K ‖G‖_{L^p L^r}` holds with a time exponent `p ≤ 2`, then the restriction
  of `T` to the shell is at most `M K (2ρ) ^ (1/p) ‖F‖_{L² L²} ‖G‖_{L² L^r}`, and symmetrically
  with the roles of `F` and `G` exchanged. For each `s` the integral over the section
  `ρ ≤ |s - t| < 2ρ`, which has length `2ρ`, is `⟪U(s)* F(s), ∫ U(t)* G(t) dt⟫` over that
  section; the energy bound controls the first factor, the dual estimate and Hölder's inequality
  in time on the section the second. This is the sliding-window energy bound
  `TauCeti.enorm_integral_inner_setIntegral_sub_preimage_adjoint_le` for these sections. With the
  non-endpoint dual Strichartz estimate at a pair `(q, a)`, `p = q'`, these are the bounds at the
  pairs `(2, a)` and `(a, 2)`.

For a decay rate `σ > 1`, the endpoint `(r, r)`, `1/r = 1/2 - 1/(2σ)`, lies inside the triangle
spanned by `(∞, ∞)`, `(2, a)` and `(a, 2)` in the plane of inverse exponents when `a` is close to
the endpoint. The powers of `ρ` in the three bounds are the values at these three points of an
affine function of the inverse exponents, which vanishes at the endpoint. Keel and Tao's argument
combines the three bounds and sums them over the dyadic shells.

The shells here are symmetric in `s` and `t`, so they decompose the whole form `T`; the retarded
form, over `s < t`, is the restriction to the half plane.

## Main declarations

* `TauCeti.timeShell`: the dyadic time shell `ρ ≤ |s - t| < 2ρ`.
* `TauCeti.hasSum_setIntegral_timeShell`: the decomposition of a double integral over the
  shells `ρ = 2ʲ`.
* `TauCeti.setIntegral_timeShell_inner_eq_conj`: the shell pairings are conjugate symmetric.
* `TauCeti.enorm_inner_integral_le_tsum`: the pairing of two time integrals is at most the sum of
  the absolute values of its shell pieces.
* `TauCeti.setLIntegral_timeShell_enorm_inner_adjoint_le`: the bound at equal exponents.
* `TauCeti.enorm_setIntegral_timeShell_inner_adjoint_le`,
  `TauCeti.enorm_setIntegral_timeShell_inner_adjoint_le'`: the bounds with an energy factor.

## References

* M. Keel and T. Tao, *Endpoint Strichartz estimates*, Amer. J. Math. 120 (1998), 955–980.
* T. Tao, *Nonlinear Dispersive Equations: Local and Global Analysis*, CBMS Regional Conference
  Series in Mathematics 106, AMS, 2006, Section 2.3.
-/

public section

open MeasureTheory Metric Set
open scoped ENNReal NNReal InnerProductSpace InnerProduct

namespace TauCeti

/-- The **dyadic time shell** `{(s, t) | ρ ≤ |s - t| < 2 ρ}` of pairs of times at distance
comparable to `ρ`. For `ρ = 2ʲ`, `j ∈ ℤ`, these shells partition the pairs of distinct times. -/
def timeShell (ρ : ℝ) : Set (ℝ × ℝ) := {p | ρ ≤ dist p.1 p.2 ∧ dist p.1 p.2 < 2 * ρ}

@[simp]
theorem mem_timeShell {ρ : ℝ} {p : ℝ × ℝ} :
    p ∈ timeShell ρ ↔ ρ ≤ dist p.1 p.2 ∧ dist p.1 p.2 < 2 * ρ := Iff.rfl

/-- The section of the dyadic time shell at a first time `s` is the set of `t` with
`ρ ≤ |s - t| < 2ρ`. -/
theorem mk_preimage_timeShell_right (ρ s : ℝ) :
    Prod.mk s ⁻¹' timeShell ρ = ball s (2 * ρ) \ ball s ρ := by
  ext t
  simp [dist_comm t s, and_comm]

/-- The section of the dyadic time shell at a second time `t` is the set of `s` with
`ρ ≤ |s - t| < 2ρ`. -/
theorem mk_preimage_timeShell_left (ρ t : ℝ) :
    (fun s ↦ (s, t)) ⁻¹' timeShell ρ = ball t (2 * ρ) \ ball t ρ := by
  ext s
  simp [and_comm]

/-- On the line through `(s, t)` with first time `s`, the indicator of the dyadic time shell is
the indicator of its section `ρ ≤ |s - t| < 2ρ`. -/
theorem indicator_timeShell_mk_right {M : Type*} [Zero M] (ρ s t : ℝ) (φ : ℝ × ℝ → M) :
    (timeShell ρ).indicator φ (s, t) =
      (ball s (2 * ρ) \ ball s ρ).indicator (fun t ↦ φ (s, t)) t := by
  rw [← mk_preimage_timeShell_right]
  exact (indicator_comp_right (Prod.mk s)).symm

/-- On the line through `(s, t)` with second time `t`, the indicator of the dyadic time shell is
the indicator of its section `ρ ≤ |s - t| < 2ρ`. -/
theorem indicator_timeShell_mk_left {M : Type*} [Zero M] (ρ s t : ℝ) (φ : ℝ × ℝ → M) :
    (timeShell ρ).indicator φ (s, t) =
      (ball t (2 * ρ) \ ball t ρ).indicator (fun s ↦ φ (s, t)) s := by
  rw [← mk_preimage_timeShell_left]
  exact (indicator_comp_right fun s ↦ (s, t)).symm

/-- The two times of a pair in a dyadic time shell are distinct. -/
theorem ne_of_mem_timeShell {ρ : ℝ} {p : ℝ × ℝ} (hp : p ∈ timeShell ρ) : p.1 ≠ p.2 :=
  dist_pos.1 (by linarith [hp.1, hp.2])

theorem measurableSet_timeShell (ρ : ℝ) : MeasurableSet (timeShell ρ) :=
  (measurableSet_le measurable_const measurable_dist).inter
    (measurableSet_lt measurable_dist measurable_const)

/-- The dyadic time shell is symmetric in `s` and `t`. -/
theorem swap_mem_timeShell {ρ : ℝ} {p : ℝ × ℝ} : p.swap ∈ timeShell ρ ↔ p ∈ timeShell ρ := by
  simp [dist_comm p.1 p.2]

/-- The dyadic time shell of a nonpositive radius is empty. -/
@[simp]
theorem timeShell_eq_empty_of_nonpos {ρ : ℝ} (hρ : ρ ≤ 0) : timeShell ρ = ∅ := by
  ext p
  simp only [mem_timeShell, mem_empty_iff_false, iff_false, not_and, not_lt]
  intro h
  linarith [dist_nonneg (x := p.1) (y := p.2)]

/-- The dyadic time shells `ρ = 2ʲ`, `j ∈ ℤ`, are pairwise disjoint. -/
theorem pairwise_disjoint_timeShell_zpow :
    Pairwise (Function.onFun Disjoint fun j : ℤ ↦ timeShell ((2 : ℝ) ^ j)) := by
  refine (pairwise_disjoint_on _).2 fun i j hij ↦ ?_
  rw [Set.disjoint_left]
  rintro p ⟨-, hi⟩ ⟨hj, -⟩
  have h : (2 : ℝ) ^ (i + 1) ≤ 2 ^ j := zpow_le_zpow_right₀ one_le_two (by omega)
  rw [zpow_add_one₀ two_ne_zero] at h
  linarith

/-- The dyadic time shells `ρ = 2ʲ`, `j ∈ ℤ`, cover exactly the pairs of distinct times. -/
theorem iUnion_timeShell_zpow : ⋃ j : ℤ, timeShell ((2 : ℝ) ^ j) = {p | p.1 ≠ p.2} := by
  ext p
  simp only [mem_iUnion, mem_ofPred_eq]
  constructor
  · rintro ⟨j, hj⟩
    exact ne_of_mem_timeShell hj
  · intro h
    have hd : 0 < dist p.1 p.2 := dist_pos.2 h
    refine ⟨Int.log 2 (dist p.1 p.2), mem_timeShell.2 ⟨?_, ?_⟩⟩
    · exact_mod_cast Int.zpow_log_le_self (b := 2) one_lt_two hd
    · have := Int.lt_zpow_succ_log_self (b := 2) one_lt_two (dist p.1 p.2)
      rw [zpow_add_one₀ (by norm_num)] at this
      push_cast at this
      linarith

/-- **The dyadic decomposition of a double time integral.** For an integrable function `f` on
`ℝ × ℝ`, the integrals of `f` over the dyadic time shells `2ʲ ≤ |s - t| < 2ʲ⁺¹`, `j ∈ ℤ`, sum to
the integral of `f`. -/
theorem hasSum_setIntegral_timeShell {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ × ℝ → E} (hf : Integrable f (volume.prod volume)) :
    HasSum (fun j : ℤ ↦ ∫ p in timeShell ((2 : ℝ) ^ j), f p ∂(volume.prod volume))
      (∫ p, f p ∂(volume.prod volume)) := by
  have h := hasSum_integral_iUnion (fun j ↦ measurableSet_timeShell _)
    pairwise_disjoint_timeShell_zpow hf.integrableOn
  -- The diagonal is a null set.
  have hdiag : ∀ᵐ p : ℝ × ℝ ∂(volume.prod volume), p ∈ {p : ℝ × ℝ | p.1 ≠ p.2} :=
    ae_iff.2 (measure_mono_null (fun p hp ↦ (not_not.1 hp).symm)
      (Measure.prod_graph_eq_zero measurable_id))
  rwa [iUnion_timeShell_zpow, Measure.restrict_eq_self_of_ae_mem hdiag] at h

/-- The pairing of two time-dependent vectors over a dyadic time shell is conjugate symmetric:
exchanging the two arguments conjugates it, since the shell is symmetric in `s` and `t`. -/
theorem setIntegral_timeShell_inner_eq_conj {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V]
    [InnerProductSpace 𝕜 V] (ρ : ℝ) (f g : ℝ → V) :
    ∫ z in timeShell ρ, ⟪f z.1, g z.2⟫_𝕜 ∂(volume.prod volume) =
      starRingEnd 𝕜 (∫ z in timeShell ρ, ⟪g z.1, f z.2⟫_𝕜 ∂(volume.prod volume)) := by
  have hswap : Prod.swap ⁻¹' timeShell ρ = timeShell ρ := ext fun _ ↦ swap_mem_timeShell
  rw [← integral_conj]
  conv_rhs => rw [← Measure.measurePreserving_swap.setIntegral_preimage_emb
    MeasurableEquiv.prodComm.measurableEmbedding _ (timeShell ρ), hswap]
  simp only [Prod.fst_swap, Prod.snd_swap, inner_conj_symm]

/-- The pairing of two time integrals is at most the sum over the dyadic time shells of the
absolute values of its pieces. -/
theorem enorm_inner_integral_le_tsum {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V]
    [InnerProductSpace 𝕜 V] [CompleteSpace V] [NormedSpace ℝ V] {f g : ℝ → V} (hf : Integrable f)
    (hg : Integrable g) :
    ‖⟪∫ s, f s, ∫ t, g t⟫_𝕜‖ₑ ≤
      ∑' j : ℤ, ‖∫ z in timeShell ((2 : ℝ) ^ j), ⟪f z.1, g z.2⟫_𝕜 ∂(volume.prod volume)‖ₑ := by
  have hφ : Integrable (fun z : ℝ × ℝ ↦ ⟪f z.1, g z.2⟫_𝕜) (volume.prod volume) :=
    hf.op_fst_snd (op := fun u v ↦ ⟪u, v⟫_𝕜) continuous_inner
      ⟨1, fun u v ↦ by simpa using norm_inner_le_norm u v⟩ hg
  have heq : ⟪∫ s, f s, ∫ t, g t⟫_𝕜 = ∫ z, ⟪f z.1, g z.2⟫_𝕜 ∂(volume.prod volume) := by
    rw [integral_prod _ hφ]
    simp_rw [integral_inner hg]
    rw [← inner_conj_symm, ← integral_inner hf, ← integral_conj]
    simp_rw [inner_conj_symm]
  rw [heq, ← (hasSum_setIntegral_timeShell hφ).tsum_eq]
  exact eNorm_tsum_le_tsum_eNorm

variable {𝕜 X E H : Type*} [RCLike 𝕜] {mX : MeasurableSpace X} {μ : Measure X}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- The section of the dyadic time shell at a time `t` is the translate by `t` of the shell
`ρ ≤ |w| < 2ρ` around `0`. -/
private theorem ball_sdiff_ball_eq_preimage (ρ t : ℝ) :
    ball t (2 * ρ) \ ball t ρ = (fun s ↦ s - t) ⁻¹' (ball 0 (2 * ρ) \ ball 0 ρ) := by
  ext s
  simp only [mem_sdiff, mem_ball, mem_preimage, dist_zero_right, Real.norm_eq_abs, Real.dist_eq]

/-- **The time pairings on a dyadic shell, at equal exponents.** Let `U(t) : H → L²(X, μ)` be
bounded operators whose time pairings decay from `L^{r'}` to `L^r` like `|s - t| ^ (-γ)`,
`‖U(s) U(t)* g‖_r ≤ A |s - t| ^ (-γ) ‖g‖_{r'}` for `s ≠ t`, with `γ ≥ 0`. Then on the dyadic time
shell `ρ ≤ |s - t| < 2ρ`,

`∫∫_{ρ ≤ |s - t| < 2ρ} |⟪U(s)* F(s), U(t)* G(t)⟫| ds dt ≤
  4 A ρ ^ (1 - γ) ‖F‖_{L² L^{r'}} ‖G‖_{L² L^{r'}}`.

With the dispersive estimate, `r = ∞` and `γ = σ`, this is the bound of Keel and Tao at the
exponent pair `(∞, ∞)`. -/
theorem setLIntegral_timeShell_enorm_inner_adjoint_le {r r' : ℝ≥0∞} [r'.HolderConjugate r]
    {γ : ℝ} (hγ : 0 ≤ γ) (ρ : ℝ) {U : ℝ → H →L[𝕜] Lp E 2 μ} {A : ℝ≥0∞}
    (hU : ∀ s t, s ≠ t → ∀ g : Lp E 2 μ,
      eLpNorm (U s (((U t)†) g)) r μ ≤ A * ‖s - t‖ₑ ^ (-γ) * eLpNorm g r' μ)
    {F G : ℝ → Lp E 2 μ} (hF : AEStronglyMeasurable F) (hG : AEStronglyMeasurable G) :
    ∫⁻ z in timeShell ρ, ‖⟪((U z.1)†) (F z.1), ((U z.2)†) (G z.2)⟫_𝕜‖ₑ ∂(volume.prod volume) ≤
      4 * A * ENNReal.ofReal ρ ^ (1 - γ) * eLpNorm (fun s ↦ eLpNorm (F s) r' μ) 2 *
        eLpNorm (fun t ↦ eLpNorm (G t) r' μ) 2 := by
  rcases le_or_gt ρ 0 with hρ | hρ
  · simp [timeShell_eq_empty_of_nonpos hρ]
  set W := ball (0 : ℝ) (2 * ρ) \ ball 0 ρ
  have hW : MeasurableSet W := measurableSet_ball.diff measurableSet_ball
  have hWρ (w : ℝ) (hw : w ∈ W) : ρ ≤ |w| :=
    not_lt.1 (by simpa only [mem_ball, dist_zero_right, Real.norm_eq_abs] using hw.2)
  have hvol : volume W = 2 * ENNReal.ofReal ρ := by
    rw [volume_ball_two_mul_sdiff_ball, ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat]
  have hpow : ENNReal.ofReal ρ ^ (1 - γ) = ENNReal.ofReal ρ * ENNReal.ofReal ρ ^ (-γ) := by
    rw [sub_eq_add_neg, ENNReal.rpow_add _ _ (ENNReal.ofReal_pos.2 hρ).ne'
      ENNReal.ofReal_ne_top, ENNReal.rpow_one]
  -- The section of the shell at a first time `s` is the window `t - s ∈ W`. Exchanging the two
  -- arguments of the pairing, which preserves its absolute value, gives the sliding-window bound
  -- with `F` and `G` exchanged.
  have hsec : ∫⁻ z in timeShell ρ, ‖⟪((U z.1)†) (F z.1), ((U z.2)†) (G z.2)⟫_𝕜‖ₑ
      ∂(volume.prod volume) ≤
        ∫⁻ s, ∫⁻ t in (fun t ↦ t - s) ⁻¹' W, ‖⟪((U t)†) (G t), ((U s)†) (F s)⟫_𝕜‖ₑ := by
    rw [← lintegral_indicator (measurableSet_timeShell ρ)]
    refine (lintegral_prod_le _).trans_eq (lintegral_congr fun s ↦ ?_)
    rw [← ball_sdiff_ball_eq_preimage,
      ← lintegral_indicator (measurableSet_ball.diff measurableSet_ball)]
    refine lintegral_congr fun t ↦ ?_
    rw [indicator_timeShell_mk_right]
    congr 1
    funext t
    rw [← inner_conj_symm, RCLike.eNorm_conj]
  have h2 := lintegral_setLIntegral_sub_preimage_enorm_inner_adjoint_le (r := r) (F := G)
    (G := F) hγ hρ hU hW hWρ hG hF
  refine (hsec.trans h2).trans ?_
  rw [hvol, hpow]
  generalize eLpNorm (fun s ↦ eLpNorm (F s) r' μ) 2 = x
  generalize eLpNorm (fun t ↦ eLpNorm (G t) r' μ) 2 = y
  calc A * ENNReal.ofReal ρ ^ (-γ) * (2 * ENNReal.ofReal ρ) * y * x
      = 2 * (A * (ENNReal.ofReal ρ * ENNReal.ofReal ρ ^ (-γ)) * x * y) := by ring
    _ ≤ 4 * (A * (ENNReal.ofReal ρ * ENNReal.ofReal ρ ^ (-γ)) * x * y) := by
        gcongr
        norm_num
    _ = 4 * A * (ENNReal.ofReal ρ * ENNReal.ofReal ρ ^ (-γ)) * x * y := by ring

variable [NormedSpace ℝ H]

/-- Integrating first in the first time `s`, the pairing of `f` and `g` over the dyadic time shell
is the integral over `t` of the pairing of `g(t)` with the integral of `f` over the section
`ρ ≤ |s - t| < 2ρ`. -/
private theorem setIntegral_timeShell_inner_eq {ρ : ℝ} {f g : ℝ → H} (hf : Integrable f)
    (hg : Integrable g) :
    ∫ z in timeShell ρ, ⟪f z.1, g z.2⟫_𝕜 ∂(volume.prod volume) =
      ∫ t, ⟪∫ s in (fun s ↦ s - t) ⁻¹' (ball 0 (2 * ρ) \ ball 0 ρ), f s, g t⟫_𝕜 := by
  have hφ : Integrable (fun z : ℝ × ℝ ↦ ⟪f z.1, g z.2⟫_𝕜) (volume.prod volume) :=
    hf.op_fst_snd (op := fun u v ↦ ⟪u, v⟫_𝕜) continuous_inner
      ⟨1, fun u v ↦ by simpa using norm_inner_le_norm u v⟩ hg
  rw [← integral_indicator (measurableSet_timeShell ρ),
    integral_prod_symm _ (hφ.indicator (measurableSet_timeShell ρ))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t ↦ ?_)
  dsimp only
  rw [← integral_inner_left hf.integrableOn, ← ball_sdiff_ball_eq_preimage,
    ← integral_indicator (measurableSet_ball.diff measurableSet_ball)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun s ↦ ?_)
  exact indicator_timeShell_mk_left ρ s t _

/-- **The time pairings on a dyadic shell, with an energy factor.** Let `U(t) : H → L²(X, μ)` be
bounded operators, `‖U(t)‖ ≤ M`, satisfying a dual estimate with a time exponent `p ≤ 2`,
`‖∫ U(t)* G(t) dt‖ ≤ K ‖G‖_{L^p L^r}`. Then on the dyadic time shell `ρ ≤ |s - t| < 2ρ`,

`|∫∫_{ρ ≤ |s - t| < 2ρ} ⟪U(s)* F(s), U(t)* G(t)⟫ ds dt| ≤
  M K (2ρ) ^ (1/p) ‖F‖_{L² L²} ‖G‖_{L² L^r}`.

With the non-endpoint dual Strichartz estimate at a pair `(q, a)`, `p = q'`, this is the bound
of Keel and Tao at the exponent pair `(2, a)`. -/
theorem enorm_setIntegral_timeShell_inner_adjoint_le {p r : ℝ≥0∞} (hp : p ≤ 2) (ρ : ℝ)
    {U : ℝ → H →L[𝕜] Lp E 2 μ} {M K : ℝ≥0∞} (hM : ∀ t, ‖U t‖ₑ ≤ M)
    (hK : ∀ G' : ℝ → Lp E 2 μ, AEStronglyMeasurable G' → Integrable (fun t ↦ ((U t)†) (G' t)) →
      ‖∫ t, ((U t)†) (G' t)‖ₑ ≤ K * eLpNorm (fun t ↦ eLpNorm (G' t) r μ) p)
    {F G : ℝ → Lp E 2 μ} (hF : AEStronglyMeasurable F) (hG : AEStronglyMeasurable G)
    (hUF : Integrable fun s ↦ ((U s)†) (F s)) (hUG : Integrable fun t ↦ ((U t)†) (G t)) :
    ‖∫ z in timeShell ρ, ⟪((U z.1)†) (F z.1), ((U z.2)†) (G z.2)⟫_𝕜 ∂(volume.prod volume)‖ₑ ≤
      M * K * ENNReal.ofReal (2 * ρ) ^ p.toReal⁻¹ * eLpNorm (fun s ↦ eLpNorm (F s) 2 μ) 2 *
        eLpNorm (fun t ↦ eLpNorm (G t) r μ) 2 := by
  rw [setIntegral_timeShell_inner_eq_conj ρ (fun s ↦ ((U s)†) (F s)) fun t ↦ ((U t)†) (G t),
    RCLike.eNorm_conj, setIntegral_timeShell_inner_eq hUG hUF]
  refine (enorm_integral_inner_setIntegral_sub_preimage_adjoint_le hp hM hK
    (measurableSet_ball.diff measurableSet_ball) hG hF).trans_eq ?_
  simp only [volume_ball_two_mul_sdiff_ball, Lp.eNorm_def]
  ring

/-- **The time pairings on a dyadic shell, with an energy factor on the second argument.** This
is `TauCeti.enorm_setIntegral_timeShell_inner_adjoint_le` with the roles of `F` and `G` exchanged:
if `‖U(t)‖ ≤ M` and `‖∫ U(s)* F(s) ds‖ ≤ K ‖F‖_{L^p L^r}` with `p ≤ 2`, then

`|∫∫_{ρ ≤ |s - t| < 2ρ} ⟪U(s)* F(s), U(t)* G(t)⟫ ds dt| ≤
  M K (2ρ) ^ (1/p) ‖F‖_{L² L^r} ‖G‖_{L² L²}`.

For the non-endpoint dual Strichartz estimate at a pair `(q, a)`, `p = q'`, this is the bound of
Keel and Tao at the exponent pair `(a, 2)`. -/
theorem enorm_setIntegral_timeShell_inner_adjoint_le' {p r : ℝ≥0∞} (hp : p ≤ 2) (ρ : ℝ)
    {U : ℝ → H →L[𝕜] Lp E 2 μ} {M K : ℝ≥0∞} (hM : ∀ t, ‖U t‖ₑ ≤ M)
    (hK : ∀ F' : ℝ → Lp E 2 μ, AEStronglyMeasurable F' → Integrable (fun s ↦ ((U s)†) (F' s)) →
      ‖∫ s, ((U s)†) (F' s)‖ₑ ≤ K * eLpNorm (fun s ↦ eLpNorm (F' s) r μ) p)
    {F G : ℝ → Lp E 2 μ} (hF : AEStronglyMeasurable F) (hG : AEStronglyMeasurable G)
    (hUF : Integrable fun s ↦ ((U s)†) (F s)) (hUG : Integrable fun t ↦ ((U t)†) (G t)) :
    ‖∫ z in timeShell ρ, ⟪((U z.1)†) (F z.1), ((U z.2)†) (G z.2)⟫_𝕜 ∂(volume.prod volume)‖ₑ ≤
      M * K * ENNReal.ofReal (2 * ρ) ^ p.toReal⁻¹ * eLpNorm (fun s ↦ eLpNorm (F s) r μ) 2 *
        eLpNorm (fun t ↦ eLpNorm (G t) 2 μ) 2 := by
  rw [setIntegral_timeShell_inner_eq hUF hUG]
  refine (enorm_integral_inner_setIntegral_sub_preimage_adjoint_le hp hM hK
    (measurableSet_ball.diff measurableSet_ball) hF hG).trans_eq ?_
  simp only [volume_ball_two_mul_sdiff_ball, Lp.eNorm_def]

end TauCeti
