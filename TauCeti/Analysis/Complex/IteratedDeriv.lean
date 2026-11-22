/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Normed.Group.FunctionSeries
import TauCeti.Analysis.Calculus.IteratedDeriv.Basic
import TauCeti.Analysis.Calculus.IteratedDeriv.Leibniz

/-!
# Iterated derivatives of holomorphic functions and series of one complex variable

This file records that every iterated derivative of a complex differentiable function
`g : ℂ → E` is again complex differentiable (`Differentiable.iteratedDeriv`,
`DifferentiableOn.iteratedDeriv`), the iterated form of Mathlib's `Differentiable.deriv`. If the
`(e + 1)`-th derivative of an entire function `h` vanishes, so does the `e`-th derivative of
`dslope h ζ` (`Differentiable.iteratedDeriv_dslope_eq_zero`): dividing a polynomial by a linear
factor lowers its degree. It also computes the norms of the real iterated derivatives
of the powers `z ^ m` (`TauCeti.Complex.norm_iteratedFDeriv_pow`).

On an open set `U`, the iterated derivatives over any field below `ℂ`, such as `ℝ`, of a map
holomorphic on `U` are the restrictions of scalars of its complex iterated derivatives
(`DifferentiableOn.iteratedFDeriv_eq_restrictScalars`). Weierstrass's theorem upgrades locally
uniform convergence of holomorphic maps on `U` to locally uniform convergence of all iterated
derivatives (`TendstoLocallyUniformlyOn.iteratedDeriv`), and hence of all real iterated derivatives
(`TendstoLocallyUniformlyOn.iteratedFDeriv`). It also records the resulting Weierstrass M-test
formulas for differentiating holomorphic series (`Complex.hasDerivAt_tsum_of_summable_norm`,
`Complex.hasSum_iteratedDeriv_of_summable_norm`).
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

/-- An iterated derivative of a complex differentiable function `g : ℂ → E` on an open set `U ⊆ ℂ`
is again complex differentiable on `U`. -/
theorem DifferentiableOn.iteratedDeriv {g : ℂ → E} {U : Set ℂ} (hg : DifferentiableOn ℂ g U)
    (hU : IsOpen U) (k : ℕ) : DifferentiableOn ℂ (iteratedDeriv k g) U := by
  rw [iteratedDeriv_eq_iterate]
  exact ((hg.analyticOnNhd hU).iterated_deriv k).differentiableOn

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

namespace Complex

/-- If holomorphic functions `F i` on an open set `U ⊆ ℂ` satisfy a uniform summable norm bound
`‖F i w‖ ≤ u i`, then their sum has derivative `∑' i, deriv (F i) z` at every `z ∈ U`. -/
theorem hasDerivAt_tsum_of_summable_norm {ι : Type*} {F : ι → ℂ → E} {U : Set ℂ} {u : ι → ℝ}
    (hu : Summable u) (hF : ∀ i, DifferentiableOn ℂ (F i) U) (hU : IsOpen U)
    (hF_le : ∀ i, ∀ w ∈ U, ‖F i w‖ ≤ u i) {z : ℂ} (hz : z ∈ U) :
    HasDerivAt (fun w => ∑' i, F i w) (∑' i, deriv (F i) z) z := by
  have hd := ((Complex.differentiableOn_tsum_of_summable_norm hu hF hU hF_le).differentiableAt
    (hU.mem_nhds hz)).hasDerivAt
  rwa [← (Complex.hasSum_deriv_of_summable_norm hu hF hU hF_le hz).tsum_eq] at hd

/-- If holomorphic functions `F i` on an open set `U ⊆ ℂ` satisfy a uniform summable norm bound
`‖F i w‖ ≤ u i`, then for every `k : ℕ` and `z ∈ U`, the `k`-th iterated derivatives
`iteratedDeriv k (F i) z` sum to `iteratedDeriv k (fun w => ∑' i, F i w) z`. -/
theorem hasSum_iteratedDeriv_of_summable_norm {ι : Type*} {F : ι → ℂ → E} {U : Set ℂ}
    {u : ι → ℝ} (hu : Summable u) (hF : ∀ i, DifferentiableOn ℂ (F i) U) (hU : IsOpen U)
    (hF_le : ∀ i, ∀ w ∈ U, ‖F i w‖ ≤ u i) (k : ℕ) {z : ℂ} (hz : z ∈ U) :
    HasSum (fun i => iteratedDeriv k (F i) z) (iteratedDeriv k (fun w => ∑' i, F i w) z) := by
  rw [HasSum]
  have hc := (tendstoUniformlyOn_tsum hu hF_le).tendstoLocallyUniformlyOn
  refine ((hc.iteratedDeriv (Filter.Eventually.of_forall fun s =>
    DifferentiableOn.fun_sum fun i _ => hF i) hU k).tendsto_at hz).congr fun s => ?_
  exact iteratedDeriv_fun_sum fun i _ => ((hF i).analyticOnNhd hU z hz).contDiffAt

end Complex

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
