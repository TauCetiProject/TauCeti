/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Iterated derivatives of holomorphic functions of one complex variable

This file records that every iterated derivative of a complex differentiable function
`g : ℂ → E` is again complex differentiable (`Differentiable.iteratedDeriv`), the iterated form of
Mathlib's `Differentiable.deriv`. For an entire `f : ℂ → ℂ`, the iterated derivatives of the real
function `x ↦ Re f(x)` on the real line are the real parts of the complex ones
(`Differentiable.iteratedDeriv_re_comp_ofReal`). It also computes the norms of the real iterated
derivatives of the powers `z ^ m` (`TauCeti.Complex.norm_iteratedFDeriv_pow`).

On an open set `U`, the iterated derivatives over any field below `ℂ`, such as `ℝ`, of a map
holomorphic on `U` are the restrictions of scalars of its complex iterated derivatives
(`DifferentiableOn.iteratedFDeriv_eq_restrictScalars`). Weierstrass's theorem upgrades locally
uniform convergence of holomorphic maps on `U` to locally uniform convergence of all iterated
derivatives (`TendstoLocallyUniformlyOn.iteratedDeriv`), and hence of all real iterated derivatives
(`TendstoLocallyUniformlyOn.iteratedFDeriv`).
-/

public section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- An iterated derivative of a complex differentiable function `g : ℂ → E` is complex
differentiable. This is the iterated form of `Differentiable.deriv`. -/
theorem Differentiable.iteratedDeriv {g : ℂ → E} (hg : Differentiable ℂ g) (k : ℕ) :
    Differentiable ℂ (iteratedDeriv k g) :=
  (hg.contDiff (n := ⊤)).differentiable_iteratedDeriv k (by simp)

/-- **Iterated derivatives on the real line.** For an entire function `f : ℂ → ℂ`, the `k`-th
derivative of the real function `x ↦ Re f(x)` is the real part of the complex `k`-th derivative
of `f` at `x`. -/
theorem Differentiable.iteratedDeriv_re_comp_ofReal {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (k : ℕ) :
    _root_.iteratedDeriv k (fun x : ℝ => (f x).re) =
      fun x : ℝ => (_root_.iteratedDeriv k f x).re := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ, ih, iteratedDeriv_succ]
    exact funext fun x => ((hf.iteratedDeriv k x).hasDerivAt.real_of_complex).deriv

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
