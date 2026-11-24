/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Asymptotics.Bleistein.UniformBound
import TauCeti.Order.Monotone.Basic

/-!
# Uniform remainder bound in Bleistein's method for `C¹` phases

After Bleistein's canonical change of variables (`TauCeti.bleisteinW`), a Laplace-type integral
`I(α, x) = ∫ t in s, (exp (-x * p t) * t ^ (λ - 1)) • q t` with an interior or coalescing
critical point `α` and an algebraic endpoint singularity `t ^ (λ - 1)` at `t = 0` takes the
canonical form

  `exp (-x * p 0) • ∫ w in (0, ∞), (exp (-x * (w ^ 2 / 2 - a * w)) * w ^ (λ - 1)) • f w`

when the upper canonical limit is `κ = ∞` (DLMF 2.3.29), where `a = bleisteinA p α` and
`f = bleisteinAmplitude p q λ α s`. Expanding `f` around `w = a`,

  `f w = ∑ j < N, (w - a) ^ j • φ j + R_N w`,    `‖R_N w‖ ≤ C * |w - a| ^ N`,

and applying `TauCeti.norm_bleistein_remainder_le` yields the uniform error bound
`C * x ^ (-(N + λ) / 2) * bleisteinG λ N (a * √x)` (DLMF 2.3.32), uniformly across any parameter
family on which `C` is chosen independent of `α`.

The results of `TauCeti.Analysis.Asymptotics.Bleistein.UniformBound` assume a `C²` phase whose
only critical point on an order-connected domain is `α`. Here the phase `p` is only assumed `C¹`
on an open set `I` with `0 < deriv (deriv p) α`, strictly decreasing up to `α` and strictly
increasing from `α` onward, and free of critical points on the integration domain `s` other than
`α`; the amplitude `q` is assumed continuous on `s`, which makes the transformed amplitude
continuous and hence measurable.

## Main results

* `TauCeti.integrableOn_bleistein_of_taylor_bound`,
  `TauCeti.norm_exp_smul_integral_bleistein_sub_le_of_taylor_bound`: convergence and explicit
  uniform remainder bound for `I(α, x)` on a domain `s` with `bleisteinW p α '' s = (0, ∞)`.
* `TauCeti.integrableOn_bleistein_Ioo_of_taylor_bound`,
  `TauCeti.norm_exp_smul_integral_bleistein_Ioo_sub_le_of_taylor_bound`,
  `TauCeti.integrableOn_bleistein_Ioi_of_taylor_bound`,
  `TauCeti.norm_exp_smul_integral_bleistein_Ioi_sub_le_of_taylor_bound`: the same on `(0, k)` and
  `(0, ∞)` when `p t → ∞` at the upper endpoint.

## References

* N. Bleistein, Uniform asymptotic expansions of integrals with stationary point near algebraic
  singularity, *Comm. Pure Appl. Math.* 19 (1966), 353–370.
* N. Bleistein and R. A. Handelsman, *Asymptotic Expansions of Integrals*, Holt, Rinehart and
  Winston, 1975; reprinted Dover, 1986. Chapter 9, §4.
* F. W. J. Olver, *Asymptotics and Special Functions*, Academic Press, 1974; reprinted
  A K Peters, 1997. Chapter 9, §6.
* NIST *Digital Library of Mathematical Functions*, §2.3(v), formulas 2.3.29–2.3.33,
  <https://dlmf.nist.gov/2.3#v>.
-/

public section

open Filter MeasureTheory Set
open scoped Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Shared change-of-variables setup deriving openness and positivity of `s`, phase lower bounds,
positivity and injectivity of `bleisteinW p α`, positivity of its derivative, and continuity of
`bleisteinAmplitude` on `(0, ∞)`. -/
private theorem bleistein_changeOfVariables_setup
    {lam : ℝ} {p : ℝ → ℝ} {q : ℝ → E} {I s : Set ℝ} {α : ℝ}
    (hI : IsOpen I) (hsI : s ⊆ I) (hα : α ∈ I) (h0 : 0 ∈ I) (hp : ContDiffOn ℝ 1 p I)
    (hanti : StrictAntiOn p (I ∩ Iic α)) (hmono : StrictMonoOn p (I ∩ Ici α))
    (hp''_pos : 0 < deriv (deriv p) α) (hreg : ∀ t ∈ s, t ≠ α → deriv p t ≠ 0)
    (hq : ContinuousOn q s) (himg : bleisteinW p α '' s = Ioi 0) :
    IsOpen s ∧ s ⊆ Ioi 0 ∧ p α ≤ p 0 ∧ (∀ t ∈ s, p α ≤ p t) ∧
      (∀ t ∈ s, 0 < bleisteinW p α t) ∧ InjOn (bleisteinW p α) s ∧
      (∀ t ∈ s, 0 < deriv (bleisteinW p α) t) ∧
      ContinuousOn (bleisteinAmplitude p q lam α s) (Ioi 0) := by
  have hw_mono := strictMonoOn_bleisteinW hα hanti hmono
  have hs_eq : s = I ∩ Ioi 0 := by
    ext t
    constructor
    · intro ht
      have hwt : 0 < bleisteinW p α t := by
        have hmem : bleisteinW p α t ∈ bleisteinW p α '' s := ⟨t, ht, rfl⟩
        rwa [himg] at hmem
      rw [← bleisteinW_zero p α] at hwt
      exact ⟨hsI ht, (hw_mono.lt_iff_lt h0 (hsI ht)).mp hwt⟩
    · rintro ⟨htI, ht0⟩
      have hwt : bleisteinW p α t ∈ bleisteinW p α '' s := by
        rw [himg, mem_Ioi, ← bleisteinW_zero p α]
        exact hw_mono h0 htI ht0
      rcases hwt with ⟨t', ht', heq⟩
      exact hw_mono.injOn (hsI ht') htI heq ▸ ht'
  have hs : IsOpen s := hs_eq ▸ hI.inter isOpen_Ioi
  have hs0 : s ⊆ Ioi 0 := hs_eq ▸ inter_subset_right
  have hw_c1 := contDiffOn_bleisteinW hI hα hp
    (fun _ ht hne => lt_of_strictAntiOn_strictMonoOn hα hanti hmono ht hne) hp''_pos
  have hinj : InjOn (bleisteinW p α) s := hw_mono.injOn.mono hsI
  have hw_pos : ∀ t ∈ s, 0 < bleisteinW p α t := fun t ht =>
    bleisteinW_pos hα h0 hanti hmono (hsI ht) (hs0 ht)
  have hdpos : ∀ t ∈ s, 0 < deriv (bleisteinW p α) t := fun t ht =>
    deriv_bleisteinW_pos_of_differentiableOn hI hα (hp.differentiableOn one_ne_zero) hanti hmono
      hp''_pos (hsI ht) (hreg t ht)
  have hf_cont : ContinuousOn (bleisteinAmplitude p q lam α s) (Ioi 0) :=
    himg ▸ continuousOn_bleisteinAmplitude_of_injOn hs hs0 (hw_c1.mono hsI) hinj hw_pos
      (fun t ht => (hdpos t ht).ne') hq
  have hmin : ∀ t ∈ I, p α ≤ p t :=
    fun _ ht => le_of_antitoneOn_monotoneOn hα hanti.antitoneOn hmono.monotoneOn ht
  exact ⟨hs, hs0, hmin 0 h0, fun t ht => hmin t (hsI ht), hw_pos, hinj, hdpos, hf_cont⟩

/-- Convergence (Bochner integrability, hence absolute convergence) of the original integral
`I(α, x) = ∫ t in s, (exp (-x * p t) * t ^ (λ - 1)) • q t` for a `C¹` phase `p` when
`bleisteinW p α '' s = (0, ∞)` and the transformed amplitude satisfies a Taylor remainder bound. -/
theorem integrableOn_bleistein_of_taylor_bound
    {lam C x : ℝ} {N : ℕ} {p : ℝ → ℝ} {q : ℝ → E} {phi : ℕ → E} {I s : Set ℝ} {α : ℝ}
    (hlam : 0 < lam) (hx : 0 < x) (hI : IsOpen I) (hsI : s ⊆ I) (hα : α ∈ I) (h0 : 0 ∈ I)
    (hp : ContDiffOn ℝ 1 p I) (hanti : StrictAntiOn p (I ∩ Iic α))
    (hmono : StrictMonoOn p (I ∩ Ici α)) (hp''_pos : 0 < deriv (deriv p) α)
    (hreg : ∀ t ∈ s, t ≠ α → deriv p t ≠ 0) (hq : ContinuousOn q s)
    (himg : bleisteinW p α '' s = Ioi 0)
    (hf : ∀ w > 0, ‖bleisteinAmplitude p q lam α s w -
        ∑ j ∈ Finset.range N, (w - bleisteinA p α) ^ j • phi j‖ ≤
      C * |w - bleisteinA p α| ^ N) :
    IntegrableOn (fun t => (Real.exp (-x * p t) * t ^ (lam - 1)) • q t) s := by
  obtain ⟨hs, hs0, h0_min, hmin, hw_pos, hinj, hdpos, hf_cont⟩ :=
    bleistein_changeOfVariables_setup hI hsI hα h0 hp hanti hmono hp''_pos hreg hq himg
  rw [← integrableOn_bleistein_iff_of_deriv_pos hs.measurableSet hs0 h0_min hmin hw_pos hinj
    hdpos, himg]
  exact integrableOn_bleistein_transformed hlam hx
    (hf_cont.aestronglyMeasurable measurableSet_Ioi) hf

/-- **Uniform Bleistein expansion with explicit remainder** (DLMF 2.3.32, `κ = ∞`) for a `C¹`
phase `p`, on a domain `s ⊆ I` mapped onto `(0, ∞)` by `bleisteinW p α`. -/
theorem norm_exp_smul_integral_bleistein_sub_le_of_taylor_bound [CompleteSpace E]
    {lam C x : ℝ} {N : ℕ} {p : ℝ → ℝ} {q : ℝ → E} {phi : ℕ → E} {I s : Set ℝ} {α : ℝ}
    (hlam : 0 < lam) (hx : 0 < x) (hI : IsOpen I) (hsI : s ⊆ I) (hα : α ∈ I) (h0 : 0 ∈ I)
    (hp : ContDiffOn ℝ 1 p I) (hanti : StrictAntiOn p (I ∩ Iic α))
    (hmono : StrictMonoOn p (I ∩ Ici α)) (hp''_pos : 0 < deriv (deriv p) α)
    (hreg : ∀ t ∈ s, t ≠ α → deriv p t ≠ 0) (hq : ContinuousOn q s)
    (himg : bleisteinW p α '' s = Ioi 0)
    (hf : ∀ w > 0, ‖bleisteinAmplitude p q lam α s w -
        ∑ j ∈ Finset.range N, (w - bleisteinA p α) ^ j • phi j‖ ≤
      C * |w - bleisteinA p α| ^ N) :
    ‖Real.exp (x * p 0) • (∫ t in s, (Real.exp (-x * p t) * t ^ (lam - 1)) • q t) -
        x ^ (-lam / 2) • ∑ j ∈ Finset.range N,
          (bleisteinF lam j (bleisteinA p α * Real.sqrt x) * x ^ (-(j : ℝ) / 2)) • phi j‖ ≤
      C * x ^ (-((N : ℝ) + lam) / 2) * bleisteinG lam N (bleisteinA p α * Real.sqrt x) := by
  obtain ⟨hs, hs0, h0_min, hmin, hw_pos, hinj, hdpos, hf_cont⟩ :=
    bleistein_changeOfVariables_setup hI hsI hα h0 hp hanti hmono hp''_pos hreg hq himg
  rw [exp_smul_integral_bleistein_eq hs.measurableSet hs0 h0_min hmin hw_pos hinj hdpos, himg]
  exact norm_bleistein_remainder_le hlam hx (hf_cont.aestronglyMeasurable measurableSet_Ioi) hf

/-- Convergence (Bochner integrability) of `I(α, x)` on `(0, k)` for a `C¹` phase `p` with
`p t → ∞` as `t → k⁻`. -/
theorem integrableOn_bleistein_Ioo_of_taylor_bound
    {lam C x k : ℝ} {N : ℕ} {p : ℝ → ℝ} {q : ℝ → E} {phi : ℕ → E} {I : Set ℝ} {α : ℝ}
    (hk : 0 < k) (hlam : 0 < lam) (hx : 0 < x) (hI : IsOpen I) (hsub : Ico 0 k ⊆ I) (hα : α ∈ I)
    (hp : ContDiffOn ℝ 1 p I) (hanti : StrictAntiOn p (I ∩ Iic α))
    (hmono : StrictMonoOn p (I ∩ Ici α)) (hp''_pos : 0 < deriv (deriv p) α)
    (hreg : ∀ t ∈ Ioo 0 k, t ≠ α → deriv p t ≠ 0)
    (hlim : Tendsto p (𝓝[<] k) atTop) (hq : ContinuousOn q (Ioo 0 k))
    (hf : ∀ w > 0, ‖bleisteinAmplitude p q lam α (Ioo 0 k) w -
        ∑ j ∈ Finset.range N, (w - bleisteinA p α) ^ j • phi j‖ ≤
      C * |w - bleisteinA p α| ^ N) :
    IntegrableOn (fun t => (Real.exp (-x * p t) * t ^ (lam - 1)) • q t) (Ioo 0 k) :=
  integrableOn_bleistein_of_taylor_bound hlam hx hI (Ioo_subset_Ico_self.trans hsub) hα
    (hsub (left_mem_Ico.mpr hk)) hp hanti hmono hp''_pos hreg hq
    (image_bleisteinW_Ioo_of_tendsto_atTop hk hsub hα (hp.continuousOn.mono hsub) hanti hmono
      (tendsto_bleisteinW_nhdsLT_atTop_of_strictAntiOn hk hsub hanti hlim)) hf

/-- **Uniform Bleistein expansion on `(0, k)`** (DLMF 2.3.32) for a `C¹` phase `p` with `p t → ∞`
as `t → k⁻`. -/
theorem norm_exp_smul_integral_bleistein_Ioo_sub_le_of_taylor_bound [CompleteSpace E]
    {lam C x k : ℝ} {N : ℕ} {p : ℝ → ℝ} {q : ℝ → E} {phi : ℕ → E} {I : Set ℝ} {α : ℝ}
    (hk : 0 < k) (hlam : 0 < lam) (hx : 0 < x) (hI : IsOpen I) (hsub : Ico 0 k ⊆ I) (hα : α ∈ I)
    (hp : ContDiffOn ℝ 1 p I) (hanti : StrictAntiOn p (I ∩ Iic α))
    (hmono : StrictMonoOn p (I ∩ Ici α)) (hp''_pos : 0 < deriv (deriv p) α)
    (hreg : ∀ t ∈ Ioo 0 k, t ≠ α → deriv p t ≠ 0)
    (hlim : Tendsto p (𝓝[<] k) atTop) (hq : ContinuousOn q (Ioo 0 k))
    (hf : ∀ w > 0, ‖bleisteinAmplitude p q lam α (Ioo 0 k) w -
        ∑ j ∈ Finset.range N, (w - bleisteinA p α) ^ j • phi j‖ ≤
      C * |w - bleisteinA p α| ^ N) :
    ‖Real.exp (x * p 0) • (∫ t in Ioo 0 k, (Real.exp (-x * p t) * t ^ (lam - 1)) • q t) -
        x ^ (-lam / 2) • ∑ j ∈ Finset.range N,
          (bleisteinF lam j (bleisteinA p α * Real.sqrt x) * x ^ (-(j : ℝ) / 2)) • phi j‖ ≤
      C * x ^ (-((N : ℝ) + lam) / 2) * bleisteinG lam N (bleisteinA p α * Real.sqrt x) :=
  norm_exp_smul_integral_bleistein_sub_le_of_taylor_bound hlam hx hI
    (Ioo_subset_Ico_self.trans hsub) hα (hsub (left_mem_Ico.mpr hk)) hp hanti hmono hp''_pos hreg
    hq (image_bleisteinW_Ioo_of_tendsto_atTop hk hsub hα (hp.continuousOn.mono hsub) hanti hmono
      (tendsto_bleisteinW_nhdsLT_atTop_of_strictAntiOn hk hsub hanti hlim)) hf

/-- Convergence (Bochner integrability) of `I(α, x)` on `(0, ∞)` for a `C¹` phase `p` with
`p t → ∞` as `t → ∞`. -/
theorem integrableOn_bleistein_Ioi_of_taylor_bound
    {lam C x : ℝ} {N : ℕ} {p : ℝ → ℝ} {q : ℝ → E} {phi : ℕ → E} {I : Set ℝ} {α : ℝ}
    (hlam : 0 < lam) (hx : 0 < x) (hI : IsOpen I) (hsub : Ici 0 ⊆ I) (hα : α ∈ I)
    (hp : ContDiffOn ℝ 1 p I) (hanti : StrictAntiOn p (I ∩ Iic α))
    (hmono : StrictMonoOn p (I ∩ Ici α)) (hp''_pos : 0 < deriv (deriv p) α)
    (hreg : ∀ t ∈ Ioi 0, t ≠ α → deriv p t ≠ 0)
    (hlim : Tendsto p atTop atTop) (hq : ContinuousOn q (Ioi 0))
    (hf : ∀ w > 0, ‖bleisteinAmplitude p q lam α (Ioi 0) w -
        ∑ j ∈ Finset.range N, (w - bleisteinA p α) ^ j • phi j‖ ≤
      C * |w - bleisteinA p α| ^ N) :
    IntegrableOn (fun t => (Real.exp (-x * p t) * t ^ (lam - 1)) • q t) (Ioi 0) :=
  integrableOn_bleistein_of_taylor_bound hlam hx hI (Ioi_subset_Ici_self.trans hsub) hα
    (hsub self_mem_Ici) hp hanti hmono hp''_pos hreg hq
    (image_bleisteinW_Ioi_of_tendsto_atTop hsub hα (hp.continuousOn.mono hsub) hanti hmono
      (tendsto_bleisteinW_atTop_of_tendsto_atTop (eventually_gt_atTop α) hlim)) hf

/-- **Uniform Bleistein expansion on `(0, ∞)`** (DLMF 2.3.32) for a `C¹` phase `p` with `p t → ∞`
as `t → ∞`. -/
theorem norm_exp_smul_integral_bleistein_Ioi_sub_le_of_taylor_bound [CompleteSpace E]
    {lam C x : ℝ} {N : ℕ} {p : ℝ → ℝ} {q : ℝ → E} {phi : ℕ → E} {I : Set ℝ} {α : ℝ}
    (hlam : 0 < lam) (hx : 0 < x) (hI : IsOpen I) (hsub : Ici 0 ⊆ I) (hα : α ∈ I)
    (hp : ContDiffOn ℝ 1 p I) (hanti : StrictAntiOn p (I ∩ Iic α))
    (hmono : StrictMonoOn p (I ∩ Ici α)) (hp''_pos : 0 < deriv (deriv p) α)
    (hreg : ∀ t ∈ Ioi 0, t ≠ α → deriv p t ≠ 0)
    (hlim : Tendsto p atTop atTop) (hq : ContinuousOn q (Ioi 0))
    (hf : ∀ w > 0, ‖bleisteinAmplitude p q lam α (Ioi 0) w -
        ∑ j ∈ Finset.range N, (w - bleisteinA p α) ^ j • phi j‖ ≤
      C * |w - bleisteinA p α| ^ N) :
    ‖Real.exp (x * p 0) • (∫ t in Ioi (0 : ℝ), (Real.exp (-x * p t) * t ^ (lam - 1)) • q t) -
        x ^ (-lam / 2) • ∑ j ∈ Finset.range N,
          (bleisteinF lam j (bleisteinA p α * Real.sqrt x) * x ^ (-(j : ℝ) / 2)) • phi j‖ ≤
      C * x ^ (-((N : ℝ) + lam) / 2) * bleisteinG lam N (bleisteinA p α * Real.sqrt x) :=
  norm_exp_smul_integral_bleistein_sub_le_of_taylor_bound hlam hx hI
    (Ioi_subset_Ici_self.trans hsub) hα (hsub self_mem_Ici) hp hanti hmono hp''_pos hreg hq
    (image_bleisteinW_Ioi_of_tendsto_atTop hsub hα (hp.continuousOn.mono hsub) hanti hmono
      (tendsto_bleisteinW_atTop_of_tendsto_atTop (eventually_gt_atTop α) hlim)) hf

end TauCeti
