/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.TaylorSeries
import TauCeti.Analysis.Calculus.IteratedDeriv.Basic
import TauCeti.Analysis.Calculus.IteratedDeriv.Leibniz

/-!
# Iterated derivatives of holomorphic functions of one complex variable

This file records that every iterated derivative of a complex differentiable function
`g : ℂ → E` is again complex differentiable (`Differentiable.iteratedDeriv`), the iterated form of
Mathlib's `Differentiable.deriv`. If the `(e + 1)`-th derivative of an entire function `h`
vanishes, so does the `e`-th derivative of `dslope h ζ`
(`Differentiable.iteratedDeriv_dslope_eq_zero`): dividing a polynomial by a linear factor lowers its
degree. It also computes the norms of the real iterated derivatives
of the powers `z ^ m` (`TauCeti.Complex.norm_iteratedFDeriv_pow`).

On an open set `U`, the iterated derivatives over any field below `ℂ`, such as `ℝ`, of a map
holomorphic on `U` are the restrictions of scalars of its complex iterated derivatives
(`DifferentiableOn.iteratedFDeriv_eq_restrictScalars`). Weierstrass's theorem upgrades locally
uniform convergence of holomorphic maps on `U` to locally uniform convergence of all iterated
derivatives (`TendstoLocallyUniformlyOn.iteratedDeriv`), and hence of all real iterated derivatives
(`TendstoLocallyUniformlyOn.iteratedFDeriv`).

For a family `f t` of maps holomorphic on `U`, depending on a real variable `t` with derivative
`f' t` in `t`, Weierstrass's theorem applied to the difference quotients `t⁻¹ (f t - f 0)` shows
that `f' 0` is again holomorphic on `U` and that the complex derivatives of `f t` are
differentiable in `t` at `0`, with derivatives those of `f' 0`, provided `f' t` is within `C |t|`
of `f' 0` uniformly on `U` (`TauCeti.differentiableOn_of_hasDerivAt_of_norm_sub_le`,
`TauCeti.hasDerivAt_iteratedDeriv_of_norm_sub_le`). No joint regularity in `t` and the complex
variable is assumed.
-/

public section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- An iterated derivative of a complex differentiable function `g : ℂ → E` is complex
differentiable. This is the iterated form of `Differentiable.deriv`. -/
theorem Differentiable.iteratedDeriv {g : ℂ → E} (hg : Differentiable ℂ g) (k : ℕ) :
    Differentiable ℂ (iteratedDeriv k g) :=
  (hg.contDiff (n := ⊤)).differentiable_iteratedDeriv k (by simp)

/-- **Dividing out a root lowers the degree.** If the `(e + 1)`-th derivative of an entire
function `h : ℂ → E` vanishes, that is, if `h` is a polynomial of degree at most `e`, then the
`e`-th derivative of `dslope h ζ` vanishes: `dslope h ζ` is a polynomial of degree less than `e`.
-/
theorem Differentiable.iteratedDeriv_dslope_eq_zero {h : ℂ → E} (hh : Differentiable ℂ h)
    {e : ℕ} (he : _root_.iteratedDeriv (e + 1) h = 0) (ζ : ℂ) :
    _root_.iteratedDeriv e (dslope h ζ) = 0 := by
  have hD : Differentiable ℂ (dslope h ζ) := fun z ↦ ((hh.analyticAt z).dslope ζ).differentiableAt
  -- The Taylor coefficients of `dslope h ζ` at `ζ` of order at least `e` are those of `h` of order
  -- at least `e + 1`, which vanish.
  have hcoeff (k : ℕ) : _root_.iteratedDeriv (k + e) (dslope h ζ) ζ = 0 := by
    have hshift := TauCeti.inv_factorial_smul_iteratedDeriv_pow_sub_smul 1 (k + e)
      ((hD.contDiff (n := ⊤)).contDiffAt.of_le le_top) (a := ζ)
    have hfun : (fun z ↦ (z - ζ) ^ 1 • dslope h ζ z) = fun z ↦ -h ζ + h z := by
      ext z
      rw [pow_one, sub_smul_dslope, neg_add_eq_sub]
    rw [hfun, iteratedDeriv_const_add (by omega), show 1 + (k + e) = k + (e + 1) by omega,
      ← TauCeti.iteratedDeriv_iteratedDeriv, he] at hshift
    simpa [Nat.factorial_ne_zero] using hshift.symm
  ext z
  rw [← Complex.taylorSeries_eq_of_entire (hD.iteratedDeriv e) ζ z]
  simp [TauCeti.iteratedDeriv_iteratedDeriv, hcoeff]

/-- On an open set `U`, the `k`-th iterated derivative over a field `𝕜` below `ℂ` of a map
holomorphic on `U` is the restriction of scalars of its complex `k`-th iterated derivative, which
is the multilinear map `(v₁, …, v_k) ↦ v₁ ⋯ v_k • iteratedDeriv k f z`. -/
theorem DifferentiableOn.iteratedFDeriv_eq_restrictScalars (𝕜 : Type*)
    [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℂ] [NormedSpace 𝕜 E] [IsScalarTower 𝕜 ℂ E]
    {f : ℂ → E} {U : Set ℂ} (hf : DifferentiableOn ℂ f U) (hU : IsOpen U) (k : ℕ) {z : ℂ}
    (hz : z ∈ U) :
    iteratedFDeriv 𝕜 k f z =
      (ContinuousMultilinearMap.piFieldEquiv ℂ (Fin k) E (iteratedDeriv k f z)).restrictScalars
        𝕜 := by
  rw [← ((hf.contDiffOn (n := k) hU).contDiffAt (hU.mem_nhds hz)).restrictScalars_iteratedFDeriv,
    iteratedFDeriv_eq_equiv_comp]
  rfl

/-- **Weierstrass's theorem for iterated derivatives.** If holomorphic maps `F n` converge to `f`
locally uniformly on an open set `U ⊆ ℂ`, then so do their iterated derivatives. This is the
iterated form of Mathlib's `TendstoLocallyUniformlyOn.deriv`. -/
theorem TendstoLocallyUniformlyOn.iteratedDeriv {ι : Type*} {l : Filter ι} {F : ι → ℂ → E}
    {f : ℂ → E} {U : Set ℂ} (hf : TendstoLocallyUniformlyOn F f l U)
    (hF : ∀ᶠ n in l, DifferentiableOn ℂ (F n) U) (hU : IsOpen U) (k : ℕ) :
    TendstoLocallyUniformlyOn (fun n => iteratedDeriv k (F n)) (iteratedDeriv k f) l U := by
  induction k generalizing F f with
  | zero => simpa using hf
  | succ k ih =>
    simp only [iteratedDeriv_succ']
    exact ih (hf.deriv hF hU) (hF.mono fun n hn => hn.deriv hU)

/-- **Weierstrass's theorem for real iterated derivatives.** If holomorphic maps `F n` converge
to `f` locally uniformly on an open set `U ⊆ ℂ`, then so do their iterated derivatives over any
field `𝕜` below `ℂ`; for `𝕜 = ℝ`, the convergence is `C^∞` on compact subsets of `U`. -/
theorem TendstoLocallyUniformlyOn.iteratedFDeriv (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    [NormedAlgebra 𝕜 ℂ] [NormedSpace 𝕜 E] [IsScalarTower 𝕜 ℂ E] {ι : Type*} {l : Filter ι}
    {F : ι → ℂ → E} {f : ℂ → E} {U : Set ℂ} (hf : TendstoLocallyUniformlyOn F f l U)
    (hF : ∀ᶠ n in l, DifferentiableOn ℂ (F n) U) (hU : IsOpen U) (k : ℕ) :
    TendstoLocallyUniformlyOn (fun n => iteratedFDeriv 𝕜 k (F n)) (iteratedFDeriv 𝕜 k f) l U := by
  rcases l.eq_or_neBot with rfl | _
  · exact fun _ _ _ _ => ⟨Set.univ, Filter.univ_mem, Filter.eventually_bot⟩
  have hT : UniformContinuous fun x : E =>
      (ContinuousMultilinearMap.piFieldEquiv ℂ (Fin k) E x).restrictScalars 𝕜 :=
    ((ContinuousMultilinearMap.restrictScalarsₗᵢ 𝕜).isometry.comp
      (ContinuousMultilinearMap.piFieldEquiv ℂ (Fin k) E).isometry).uniformContinuous
  have hf' := hf.differentiableOn hF hU
  refine ((hT.comp_tendstoLocallyUniformlyOn (hf.iteratedDeriv hF hU k)).congr_inseparable
    (hF.mono fun n hn z hz => .of_eq ?_)).congr_right fun z hz => ?_
  · exact (hn.iteratedFDeriv_eq_restrictScalars 𝕜 hU k hz).symm
  · exact (hf'.iteratedFDeriv_eq_restrictScalars 𝕜 hU k hz).symm

namespace TauCeti

/-! ### Holomorphic families depending on a real variable -/

section RealVariable

open Filter Metric Topology

variable {f f' : ℝ → ℂ → E} {U : Set ℂ} {δ C : ℝ}

omit [CompleteSpace E] in
/-- The difference quotient of `t ↦ f t r` at `0` is within `C |t|` of `f' 0 r` when the
derivative `f' s r` of `s ↦ f s r` is within `C |s|` of `f' 0 r` on a ball containing `t`. -/
private theorem norm_slope_sub_le {r : ℂ}
    (hf : ∀ t ∈ ball (0 : ℝ) δ, HasDerivAt (f · r) (f' t r) t)
    (hC : ∀ t ∈ ball (0 : ℝ) δ, ‖f' t r - f' 0 r‖ ≤ C * |t|) {t : ℝ} (ht : t ∈ ball (0 : ℝ) δ)
    (ht0 : t ≠ 0) : ‖slope (f · r) 0 t - f' 0 r‖ ≤ C * |t| := by
  have hseg : Set.uIcc 0 t ⊆ ball (0 : ℝ) δ := by
    rw [← segment_eq_uIcc]
    exact (convex_ball 0 δ).segment_subset (mem_ball_self (pos_of_mem_ball ht)) ht
  -- `s ↦ f s r - s f' 0 r` has derivative `f' s r - f' 0 r`, of norm at most `C |t|` on `[0, t]`
  have key := (convex_uIcc (0 : ℝ) t).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun s ↦ f s r - s • f' 0 r) (f' := fun s ↦ f' s r - f' 0 r) (C := C * |t|)
    (fun s hs ↦ (((hf s (hseg hs)).sub ((hasDerivAt_id s).smul_const (f' 0 r))).congr_deriv
      (by simp)).hasDerivWithinAt)
    (fun s hs ↦ (hC s (hseg hs)).trans (mul_le_mul_of_nonneg_left
      (by simpa using Set.abs_sub_left_of_mem_uIcc hs)
      (nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (hC t ht)) (abs_pos.2 ht0))))
    Set.left_mem_uIcc Set.right_mem_uIcc
  have hslope : slope (f · r) 0 t - f' 0 r =
      t⁻¹ • ((f t r - t • f' 0 r) - (f 0 r - (0 : ℝ) • f' 0 r)) := by
    rw [slope_def_module, sub_zero, zero_smul, sub_zero, sub_right_comm,
      smul_sub _ (f t r - f 0 r), smul_smul, inv_mul_cancel₀ ht0, one_smul]
  rw [hslope, norm_smul, Real.norm_eq_abs, abs_inv]
  calc |t|⁻¹ * ‖(f t r - t • f' 0 r) - (f 0 r - (0 : ℝ) • f' 0 r)‖
      ≤ |t|⁻¹ * (C * |t| * ‖t - 0‖) := by gcongr
    _ = C * |t| := by
      rw [sub_zero, Real.norm_eq_abs]
      field_simp [abs_pos.2 ht0]

omit [CompleteSpace E] in
/-- Let `f t r` depend on a real variable `t` with derivative `f' t r`, and let `f' t r` be within
`C |t|` of `f' 0 r` near `t = 0`, uniformly in `r ∈ U`. Then the difference quotients
`t⁻¹ (f t r - f 0 r)` converge to `f' 0 r` uniformly in `r ∈ U` as `t → 0`. -/
theorem tendstoUniformlyOn_slope_of_norm_sub_le (hδ : 0 < δ)
    (hf : ∀ r ∈ U, ∀ t ∈ ball (0 : ℝ) δ, HasDerivAt (f · r) (f' t r) t)
    (hC : ∀ r ∈ U, ∀ t ∈ ball (0 : ℝ) δ, ‖f' t r - f' 0 r‖ ≤ C * |t|) :
    TendstoUniformlyOn (fun t r ↦ slope (f · r) 0 t) (f' 0) (𝓝[≠] 0) U := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hsmall : ∀ᶠ t in 𝓝 (0 : ℝ), |C| * |t| < ε :=
    ((continuous_const.mul continuous_abs).tendsto' (0 : ℝ) 0 (by simp)).eventually
      (gt_mem_nhds hε)
  filter_upwards [nhdsWithin_le_nhds (ball_mem_nhds 0 hδ), nhdsWithin_le_nhds hsmall,
    self_mem_nhdsWithin] with t ht htε ht0 r hr
  rw [dist_comm, dist_eq_norm]
  exact (norm_slope_sub_le (hf r hr) (hC r hr) ht ht0).trans_lt
    ((mul_le_mul_of_nonneg_right (le_abs_self C) (abs_nonneg t)).trans_lt htε)

omit [CompleteSpace E] in
/-- The difference quotients `r ↦ t⁻¹ (f t r - f 0 r)` of a family of maps holomorphic on `U` are
holomorphic on `U`. -/
private theorem eventually_differentiableOn_slope (hδ : 0 < δ)
    (hF : ∀ t ∈ ball (0 : ℝ) δ, DifferentiableOn ℂ (f t) U) :
    ∀ᶠ t in 𝓝[≠] (0 : ℝ), DifferentiableOn ℂ (fun r ↦ slope (f · r) 0 t) U := by
  filter_upwards [nhdsWithin_le_nhds (ball_mem_nhds 0 hδ)] with t ht
  simp only [slope_def_module, sub_zero]
  exact ((hF t ht).sub (hF 0 (mem_ball_self hδ))).const_smul t⁻¹

/-- **Differentiating a holomorphic family in a real variable.** Let `f t` be holomorphic on an
open set `U ⊆ ℂ` for every real `t` near `0`, and let `t ↦ f t r` have derivative `f' t r`, with
`‖f' t r - f' 0 r‖ ≤ C |t|` near `t = 0`, uniformly in `r ∈ U`. Then the derivative `f' 0` at
`t = 0` is holomorphic on `U`. -/
theorem differentiableOn_of_hasDerivAt_of_norm_sub_le (hU : IsOpen U) (hδ : 0 < δ)
    (hF : ∀ t ∈ ball (0 : ℝ) δ, DifferentiableOn ℂ (f t) U)
    (hf : ∀ r ∈ U, ∀ t ∈ ball (0 : ℝ) δ, HasDerivAt (f · r) (f' t r) t)
    (hC : ∀ r ∈ U, ∀ t ∈ ball (0 : ℝ) δ, ‖f' t r - f' 0 r‖ ≤ C * |t|) :
    DifferentiableOn ℂ (f' 0) U :=
  (tendstoUniformlyOn_slope_of_norm_sub_le hδ hf hC).tendstoLocallyUniformlyOn.differentiableOn
    (eventually_differentiableOn_slope hδ hF) hU

/-- **The real and the complex derivatives of a holomorphic family commute.** Under the
hypotheses of `TauCeti.differentiableOn_of_hasDerivAt_of_norm_sub_le`, for every `k` and `r ∈ U`
the `k`-th complex derivative `∂_r^k f t r` has derivative `∂_r^k f' 0 r` in `t` at `t = 0`. -/
theorem hasDerivAt_iteratedDeriv_of_norm_sub_le (hU : IsOpen U) (hδ : 0 < δ)
    (hF : ∀ t ∈ ball (0 : ℝ) δ, DifferentiableOn ℂ (f t) U)
    (hf : ∀ r ∈ U, ∀ t ∈ ball (0 : ℝ) δ, HasDerivAt (f · r) (f' t r) t)
    (hC : ∀ r ∈ U, ∀ t ∈ ball (0 : ℝ) δ, ‖f' t r - f' 0 r‖ ≤ C * |t|) (k : ℕ) {r : ℂ}
    (hr : r ∈ U) :
    HasDerivAt (fun t ↦ iteratedDeriv k (f t) r) (iteratedDeriv k (f' 0) r) 0 := by
  rw [hasDerivAt_iff_tendsto_slope]
  -- by Weierstrass's theorem, the derivatives of the difference quotients converge
  have hT := (tendstoUniformlyOn_slope_of_norm_sub_le hδ hf hC).tendstoLocallyUniformlyOn
  refine ((hT.iteratedDeriv (eventually_differentiableOn_slope hδ hF) hU k).tendsto_at hr).congr' ?_
  filter_upwards [nhdsWithin_le_nhds (ball_mem_nhds 0 hδ)] with t ht
  have hc (s : ℝ) (hs : s ∈ ball (0 : ℝ) δ) : ContDiffAt ℂ k (f s) r :=
    ((hF s hs).contDiffOn hU).contDiffAt (hU.mem_nhds hr)
  simp only [slope_def_module, sub_zero]
  rw [iteratedDeriv_fun_const_smul_field, iteratedDeriv_fun_sub (hc t ht) (hc 0 (mem_ball_self hδ))]

end RealVariable

end TauCeti

namespace TauCeti.Complex

/-- The real iterated derivatives of `z ^ m` have the norms of the complex ones:
`‖D^k (z ^ m)‖ = m (m - 1) ⋯ (m - k + 1) ‖z‖ ^ (m - k)`. -/
theorem norm_iteratedFDeriv_pow (k m : ℕ) (z : ℂ) :
    ‖iteratedFDeriv ℝ k (fun w : ℂ => w ^ m) z‖ = m.descFactorial k * ‖z‖ ^ (m - k) := by
  have h : ContDiffAt ℂ k (fun w : ℂ => w ^ m) z := by fun_prop
  rw [← h.restrictScalars_iteratedFDeriv (𝕜 := ℝ), Function.comp_apply,
    ContinuousMultilinearMap.norm_restrictScalars, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    iteratedDeriv_pow, norm_mul, norm_pow, Complex.norm_natCast]

end TauCeti.Complex
