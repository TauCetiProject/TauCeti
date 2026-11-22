/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Strichartz.TTStar
import Mathlib.Data.Int.Log
import TauCeti.MeasureTheory.Function.Lp.Integral.Functional
import TauCeti.MeasureTheory.Integral.SchurTest
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
  ‖G‖_{L² L^{r'}}`. On the shell the pairing decay is at least `ρ ^ (-γ)`, and Schur's test for
  the kernel `1_{|s - t| < 2ρ}`, whose rows and columns have length `4ρ`, does the time integral.
  With the dispersive estimate, `r = ∞` and `γ = σ`, this is the bound at the pair `(∞, ∞)`.
* **With an energy factor** (`TauCeti.enorm_setIntegral_timeShell_inner_adjoint_le` and
  `TauCeti.enorm_setIntegral_timeShell_inner_adjoint_le'`): if `‖U(t)‖ ≤ M` and the dual estimate
  `‖∫ U(t)* G(t) dt‖ ≤ K ‖G‖_{L^p L^r}` holds with a time exponent `p ≤ 2`, then the restriction
  of `T` to the shell is at most `M K (2ρ) ^ (1/p) ‖F‖_{L² L²} ‖G‖_{L² L^r}`, and symmetrically
  with the roles of `F` and `G` exchanged. For each `s` the integral over the section
  `ρ ≤ |s - t| < 2ρ`, which has length `2ρ`, is `⟪U(s)* F(s), ∫ U(t)* G(t) dt⟫` over that
  section; the energy bound controls the first factor, the dual estimate and Hölder's inequality
  in time on the section the second. With the non-endpoint dual Strichartz estimate at a pair
  `(q, a)`, `p = q'`, these are the bounds at the pairs `(2, a)` and `(a, 2)`.

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

/-- On the dyadic time shell, the pairing decay `‖U(s) U(t)* g‖_r ≤ A |s - t| ^ (-γ) ‖g‖_{r'}`
bounds `|⟪U(s)* F(s), U(t)* G(t)⟫|` by `A ρ ^ (-γ) ‖F(s)‖_{r'} 1_{|s - t| < 2ρ} ‖G(t)‖_{r'}`. -/
private theorem indicator_timeShell_enorm_inner_adjoint_le {r r' : ℝ≥0∞} [r'.HolderConjugate r]
    {γ ρ : ℝ} (hγ : 0 ≤ γ) {U : ℝ → H →L[𝕜] Lp E 2 μ} {A : ℝ≥0∞}
    (hU : ∀ s t, s ≠ t → ∀ g : Lp E 2 μ,
      eLpNorm (U s (((U t)†) g)) r μ ≤ A * ‖s - t‖ₑ ^ (-γ) * eLpNorm g r' μ)
    (F G : ℝ → Lp E 2 μ) (z : ℝ × ℝ) :
    (timeShell ρ).indicator (fun z ↦ ‖⟪((U z.1)†) (F z.1), ((U z.2)†) (G z.2)⟫_𝕜‖ₑ) z ≤
      A * ENNReal.ofReal ρ ^ (-γ) * (eLpNorm (F z.1) r' μ *
        ((ball z.1 (2 * ρ)).indicator (1 : ℝ → ℝ≥0∞) z.2 * eLpNorm (G z.2) r' μ)) := by
  by_cases hz : z ∈ timeShell ρ
  · rw [indicator_of_mem hz, indicator_of_mem (by rw [mem_ball, dist_comm]; exact hz.2),
      Pi.one_apply, one_mul]
    have hdist : ENNReal.ofReal ρ ≤ ‖z.1 - z.2‖ₑ := by
      rw [← eDist_eq_eNorm_sub, edist_dist]
      exact ENNReal.ofReal_le_ofReal hz.1
    calc _ ≤ A * ‖z.1 - z.2‖ₑ ^ (-γ) * eLpNorm (F z.1) r' μ * eLpNorm (G z.2) r' μ :=
          enorm_inner_adjoint_le hU (ne_of_mem_timeShell hz) _ _
      _ ≤ A * ENNReal.ofReal ρ ^ (-γ) * eLpNorm (F z.1) r' μ * eLpNorm (G z.2) r' μ := by
          gcongr A * ?_ * _ * _
          rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
          exact ENNReal.inv_le_inv.2 (ENNReal.rpow_le_rpow hdist hγ)
      _ = _ := by ring
  · rw [indicator_of_notMem hz]
    exact bot_le

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
  set a := fun s ↦ eLpNorm (F s) r' μ
  set b := fun t ↦ eLpNorm (G t) r' μ
  have ha : AEMeasurable a := hF.aemeasurable_eLpNorm_Lp .rfl r'
  have hb : AEMeasurable b := hG.aemeasurable_eLpNorm_Lp .rfl r'
  set c := A * ENNReal.ofReal ρ ^ (-γ)
  set k : ℝ → ℝ → ℝ≥0∞ := fun s t ↦ (ball s (2 * ρ)).indicator 1 t
  have hinner (s : ℝ) : AEMeasurable fun t ↦ a s * (k s t * b t) :=
    aemeasurable_const.mul ((measurable_one.indicator measurableSet_ball).aemeasurable.mul hb)
  have hprod : AEMeasurable (fun z : ℝ × ℝ ↦ a z.1 * (k z.1 z.2 * b z.2))
      (volume.prod volume) :=
    ha.comp_fst.mul ((measurable_uncurry_indicator_ball (2 * ρ)).aemeasurable.mul hb.comp_snd)
  have hk : AEMeasurable (fun s ↦ ∫⁻ t, a s * (k s t * b t)) := hprod.lintegral_prod_right'
  have h4 : ENNReal.ofReal (2 * (2 * ρ)) = 4 * ENNReal.ofReal ρ := by
    rw [← mul_assoc, ENNReal.ofReal_mul (by norm_num)]
    norm_num
  have hpow : ENNReal.ofReal ρ ^ (1 - γ) = ENNReal.ofReal ρ * ENNReal.ofReal ρ ^ (-γ) := by
    rw [sub_eq_add_neg, ENNReal.rpow_add _ _ (ENNReal.ofReal_pos.2 hρ).ne'
      ENNReal.ofReal_ne_top, ENNReal.rpow_one]
  calc ∫⁻ z in timeShell ρ, ‖⟪((U z.1)†) (F z.1), ((U z.2)†) (G z.2)⟫_𝕜‖ₑ ∂(volume.prod volume)
      ≤ ∫⁻ z, c * (a z.1 * (k z.1 z.2 * b z.2)) ∂(volume.prod volume) := by
        rw [← lintegral_indicator (measurableSet_timeShell ρ)]
        exact lintegral_mono (indicator_timeShell_enorm_inner_adjoint_le hγ hU F G)
    _ ≤ ∫⁻ s, ∫⁻ t, c * (a s * (k s t * b t)) := lintegral_prod_le _
    _ = c * ∫⁻ s, ∫⁻ t, a s * (k s t * b t) := by
        rw [← lintegral_const_mul'' _ hk]
        exact lintegral_congr fun s ↦ lintegral_const_mul'' _ (hinner s)
    _ ≤ c * (ENNReal.ofReal (2 * (2 * ρ)) * eLpNorm a 2 * eLpNorm b 2) := by
        gcongr
        exact lintegral_lintegral_mul_indicator_ball_mul_le ha hb (2 * ρ)
    _ = _ := by
        rw [h4, hpow]
        ring

/-- The `L²` norm of a function into `ℝ≥0∞` is the square root of the integral of its square. -/
private theorem eLpNorm_two_eq {f : ℝ → ℝ≥0∞} (hf : AEMeasurable f) :
    eLpNorm f 2 = (∫⁻ x, f x ^ (2 : ℝ)) ^ (2⁻¹ : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal two_ne_zero ENNReal.ofNat_ne_top
    hf.aestronglyMeasurable]
  simp

/-- The square of the `L²` norm of `b` on the section `ρ ≤ |s - t| < 2ρ` at `s` is the integral
of `b²` over the section of the dyadic time shell. -/
private theorem eLpNorm_indicator_ball_diff_eq {ρ : ℝ} {b : ℝ → ℝ≥0∞} (hb : AEMeasurable b)
    (s : ℝ) : eLpNorm ((ball s (2 * ρ) \ ball s ρ).indicator b) 2 =
      (∫⁻ t, (timeShell ρ).indicator (fun z ↦ b z.2 ^ (2 : ℝ)) (s, t)) ^ (2⁻¹ : ℝ) := by
  rw [eLpNorm_two_eq (hb.indicator (measurableSet_ball.diff measurableSet_ball))]
  congr 1
  refine lintegral_congr fun t ↦ ?_
  rw [indicator_timeShell_mk_right]
  by_cases ht : t ∈ ball s (2 * ρ) \ ball s ρ <;> simp [ht]

private theorem aemeasurable_uncurry_indicator_timeShell (ρ : ℝ) {b : ℝ → ℝ≥0∞}
    (hb : AEMeasurable b) :
    AEMeasurable (Function.uncurry fun s t ↦
      (timeShell ρ).indicator (fun z ↦ b z.2 ^ (2 : ℝ)) (s, t)) (volume.prod volume) :=
  (hb.comp_snd.pow_const _).indicator (measurableSet_timeShell ρ)

/-- The `L²` norms of `b` on the sections `ρ ≤ |s - t| < 2ρ` depend measurably on `s`. -/
private theorem aemeasurable_eLpNorm_indicator_ball_diff (ρ : ℝ) {b : ℝ → ℝ≥0∞}
    (hb : AEMeasurable b) :
    AEMeasurable fun s ↦ eLpNorm ((ball s (2 * ρ) \ ball s ρ).indicator b) 2 := by
  simp_rw [eLpNorm_indicator_ball_diff_eq hb]
  exact (aemeasurable_uncurry_indicator_timeShell ρ hb).lintegral_prod_right'.pow_const _

/-- The `L²` norm in `s` of the `L²` norms of `b` on the sections `ρ ≤ |s - t| < 2ρ` is
`(2ρ) ^ (1/2) ‖b‖₂`. -/
private theorem eLpNorm_eLpNorm_indicator_ball_diff (ρ : ℝ) {b : ℝ → ℝ≥0∞}
    (hb : AEMeasurable b) :
    eLpNorm (fun s ↦ eLpNorm ((ball s (2 * ρ) \ ball s ρ).indicator b) 2) 2 =
      ENNReal.ofReal (2 * ρ) ^ (2⁻¹ : ℝ) * eLpNorm b 2 := by
  -- Integrating the squared sections over `s` gives `2ρ ∫ b²`, by Tonelli's theorem.
  have hcol (t : ℝ) : ∫⁻ s, (timeShell ρ).indicator (fun z ↦ b z.2 ^ (2 : ℝ)) (s, t) =
      b t ^ (2 : ℝ) * ENNReal.ofReal (2 * ρ) := by
    have : (fun s ↦ (timeShell ρ).indicator (fun z ↦ b z.2 ^ (2 : ℝ)) (s, t)) =
        (ball t (2 * ρ) \ ball t ρ).indicator fun _ ↦ b t ^ (2 : ℝ) := by
      ext s
      exact indicator_timeShell_mk_left ρ s t _
    rw [this, lintegral_indicator_const (measurableSet_ball.diff measurableSet_ball),
      volume_ball_two_mul_sdiff_ball]
  have hsq (x : ℝ≥0∞) : (x ^ (2⁻¹ : ℝ)) ^ (2 : ℝ) = x := by
    rw [← ENNReal.rpow_mul]
    norm_num
  rw [eLpNorm_two_eq (aemeasurable_eLpNorm_indicator_ball_diff ρ hb), eLpNorm_two_eq hb]
  simp_rw [eLpNorm_indicator_ball_diff_eq hb, hsq]
  rw [lintegral_lintegral_swap (aemeasurable_uncurry_indicator_timeShell ρ hb)]
  simp_rw [hcol]
  rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
    mul_comm]

/-- Cutting a family `G` off to a set of times commutes with applying `U(t)*`. -/
private theorem adjoint_indicator_eq {U : ℝ → H →L[𝕜] Lp E 2 μ} (G : ℝ → Lp E 2 μ) (S : Set ℝ) :
    (fun t ↦ ((U t)†) (S.indicator G t)) = S.indicator fun t ↦ ((U t)†) (G t) := by
  ext t
  by_cases ht : t ∈ S <;> simp [ht]

variable [NormedSpace ℝ H]

/-- For each `s`, the integral over `t` of the time pairing restricted to the dyadic time shell is
the pairing of `U(s)* F(s)` with the integral of `U(t)* G(t)` over the section
`ρ ≤ |s - t| < 2ρ`. -/
private theorem integral_indicator_timeShell_inner_eq {ρ : ℝ} {U : ℝ → H →L[𝕜] Lp E 2 μ}
    (F G : ℝ → Lp E 2 μ) (hUG : Integrable fun t ↦ ((U t)†) (G t)) (s : ℝ) :
    ∫ t, (timeShell ρ).indicator (fun z ↦ ⟪((U z.1)†) (F z.1), ((U z.2)†) (G z.2)⟫_𝕜) (s, t) =
      ⟪((U s)†) (F s), ∫ t, ((U t)†) ((ball s (2 * ρ) \ ball s ρ).indicator G t)⟫_𝕜 := by
  have h : (fun t ↦ (timeShell ρ).indicator
      (fun z ↦ ⟪((U z.1)†) (F z.1), ((U z.2)†) (G z.2)⟫_𝕜) (s, t)) =
        fun t ↦ ⟪((U s)†) (F s), ((U t)†) ((ball s (2 * ρ) \ ball s ρ).indicator G t)⟫_𝕜 := by
    ext t
    rw [indicator_timeShell_mk_right]
    by_cases ht : t ∈ ball s (2 * ρ) \ ball s ρ <;> simp [ht]
  rw [h, integral_inner]
  rw [adjoint_indicator_eq]
  exact hUG.indicator (measurableSet_ball.diff measurableSet_ball)

/-- The dual estimate `‖∫ U(t)* G(t) dt‖ ≤ K ‖G‖_{L^p L^r}`, `p ≤ 2`, applied on the section
`ρ ≤ |s - t| < 2ρ` of length `2ρ`, together with Hölder's inequality in time on the section. -/
private theorem enorm_integral_adjoint_indicator_ball_diff_le {p r : ℝ≥0∞} (hp : p ≤ 2) {ρ : ℝ}
    {U : ℝ → H →L[𝕜] Lp E 2 μ} {K : ℝ≥0∞}
    (hK : ∀ G' : ℝ → Lp E 2 μ, AEStronglyMeasurable G' → Integrable (fun t ↦ ((U t)†) (G' t)) →
      ‖∫ t, ((U t)†) (G' t)‖ₑ ≤ K * eLpNorm (fun t ↦ eLpNorm (G' t) r μ) p)
    {G : ℝ → Lp E 2 μ} (hG : AEStronglyMeasurable G) (hUG : Integrable fun t ↦ ((U t)†) (G t))
    (s : ℝ) :
    ‖∫ t, ((U t)†) ((ball s (2 * ρ) \ ball s ρ).indicator G t)‖ₑ ≤
      K * (eLpNorm ((ball s (2 * ρ) \ ball s ρ).indicator fun t ↦ eLpNorm (G t) r μ) 2 *
        ENNReal.ofReal (2 * ρ) ^ (1 / p.toReal - 1 / (2 : ℝ≥0∞).toReal)) := by
  set S := ball s (2 * ρ) \ ball s ρ
  have hS : MeasurableSet S := measurableSet_ball.diff measurableSet_ball
  have hb : AEMeasurable fun t ↦ eLpNorm (G t) r μ := hG.aemeasurable_eLpNorm_Lp .rfl r
  refine (hK _ (hG.indicator hS) (by rw [adjoint_indicator_eq]; exact hUG.indicator hS)).trans ?_
  gcongr
  have hb' : (fun t ↦ eLpNorm ((S.indicator G t : Lp E 2 μ) : X → E) r μ) =
      S.indicator fun t ↦ eLpNorm (G t) r μ := by
    ext t
    by_cases ht : t ∈ S
    · simp [ht]
    · rw [indicator_of_notMem ht, indicator_of_notMem ht,
        eLpNorm_congr_ae (Lp.coeFn_zero _ _ _), eLpNorm_zero]
  rw [hb', eLpNorm_indicator_eq_eLpNorm_restrict (μ := volume) hS.nullMeasurableSet,
    eLpNorm_indicator_eq_eLpNorm_restrict (μ := volume) hS.nullMeasurableSet]
  have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp (hb.restrict (s := S)).aestronglyMeasurable
  rwa [Measure.restrict_apply_univ, volume_ball_two_mul_sdiff_ball] at h

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
  rcases le_or_gt ρ 0 with hρ | hρ
  · simp [timeShell_eq_empty_of_nonpos hρ]
  set a := fun s ↦ eLpNorm (F s) 2 μ
  set b := fun t ↦ eLpNorm (G t) r μ
  have ha : AEMeasurable a := hF.aemeasurable_eLpNorm_Lp .rfl 2
  have hb : AEMeasurable b := hG.aemeasurable_eLpNorm_Lp .rfl r
  set g := fun s ↦ eLpNorm ((ball s (2 * ρ) \ ball s ρ).indicator b) 2
  have hg : AEMeasurable g := aemeasurable_eLpNorm_indicator_ball_diff ρ hb
  set c := ENNReal.ofReal (2 * ρ) ^ (1 / p.toReal - 1 / (2 : ℝ≥0∞).toReal)
  have hφ : Integrable (fun z : ℝ × ℝ ↦ ⟪((U z.1)†) (F z.1), ((U z.2)†) (G z.2)⟫_𝕜)
      (volume.prod volume) :=
    hUF.op_fst_snd (op := fun u v ↦ ⟪u, v⟫_𝕜) continuous_inner
      ⟨1, fun u v ↦ by simpa using norm_inner_le_norm u v⟩ hUG
  -- The energy bound for `U(s)* F(s)`, and the dual estimate for the integral over the section.
  have hpt (s : ℝ) : ‖∫ t, (timeShell ρ).indicator
      (fun z ↦ ⟪((U z.1)†) (F z.1), ((U z.2)†) (G z.2)⟫_𝕜) (s, t)‖ₑ ≤ M * K * c * (a s * g s) := by
    rw [integral_indicator_timeShell_inner_eq F G hUG]
    refine (eNorm_inner_le_eNorm _ _).trans ?_
    have hx : ‖((U s)†) (F s)‖ₑ ≤ M * a s := by
      refine (((U s)†).le_opENorm _).trans ?_
      rw [ContinuousLinearMap.adjoint.eNorm_map, Lp.eNorm_def]
      gcongr
      exact hM s
    calc _ ≤ M * a s * (K * (g s * c)) := by
          gcongr
          exact enorm_integral_adjoint_indicator_ball_diff_le hp hK hG hUG s
      _ = _ := by ring
  have hpow : c * ENNReal.ofReal (2 * ρ) ^ (2⁻¹ : ℝ) = ENNReal.ofReal (2 * ρ) ^ p.toReal⁻¹ := by
    rw [← ENNReal.rpow_add _ _ (ENNReal.ofReal_pos.2 (by positivity)).ne' ENNReal.ofReal_ne_top]
    norm_num
  -- Fubini, then Hölder's inequality in `s`.
  calc ‖∫ z in timeShell ρ, ⟪((U z.1)†) (F z.1), ((U z.2)†) (G z.2)⟫_𝕜 ∂(volume.prod volume)‖ₑ
      = ‖∫ s, ∫ t, (timeShell ρ).indicator
          (fun z ↦ ⟪((U z.1)†) (F z.1), ((U z.2)†) (G z.2)⟫_𝕜) (s, t)‖ₑ := by
        rw [← integral_indicator (measurableSet_timeShell ρ),
          integral_prod _ (hφ.indicator (measurableSet_timeShell ρ))]
    _ ≤ ∫⁻ s, M * K * c * (a s * g s) :=
        (eNorm_integral_le_lintegral_eNorm _).trans (lintegral_mono hpt)
    _ = M * K * c * ∫⁻ s, a s * g s := lintegral_const_mul'' _ (ha.mul hg)
    _ ≤ M * K * c * (eLpNorm a 2 * eLpNorm g 2) := by
        gcongr
        have h := eLpNorm_le_eLpNorm_mul_eLpNorm_ennreal (p := 2) (q := 2) (r := 1)
          ha.aestronglyMeasurable hg.aestronglyMeasurable
        rwa [eLpNorm_one_eq_lintegral_eNorm (ha.mul hg).aestronglyMeasurable] at h
    _ = _ := by
        rw [eLpNorm_eLpNorm_indicator_ball_diff ρ hb, ← hpow]
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
  rw [setIntegral_timeShell_inner_eq_conj ρ (fun s ↦ ((U s)†) (F s)) fun t ↦ ((U t)†) (G t),
    RCLike.eNorm_conj]
  refine (enorm_setIntegral_timeShell_inner_adjoint_le hp ρ hM hK hG hF hUG hUF).trans_eq ?_
  ring

end TauCeti
