/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5, OpenAI GPT-6
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearPMap.Yosida.Basic
public import Mathlib.Data.PNat.Basic
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.CStarAlgebra.Exponential
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Uniform convergence of Yosida exponential approximants

The exponential orbits of the symmetric Yosida approximations of a self-adjoint
partial operator form a Cauchy family uniformly for time in any bounded interval.
The proof first uses the **Duhamel estimate**

`‖exp (t • Bₘ) ψ - exp (t • Bₙ) ψ‖ ≤ |t| ‖(Bₘ - Bₙ) ψ‖`

for *commuting* skew-adjoint `Bₘ`, `Bₙ`, together with convergence of the
approximations on the domain. Density and unitarity extend the uniform bound
to every vector. No limit group is constructed in this module.

## Sources

That a bounded skew-adjoint operator exponentiates to a strongly continuous
one-parameter unitary group, and that this is the bounded case of Stone's theorem,
is standard (Reed--Simon, *Methods of Modern Mathematical Physics I*).  No source
is followed for the presentation.

## Provenance

* **Original repository:** Spectra, commit `8dbaaf6728d1342ae16acf79fd7eef7c59b37e63`.
* **Original module:** `Spectra/YosidaHille/Approximation/Commutation.lean`
  (`norm_expBounded_pairwise_le` and its supporting commutation lemmas).
* **Original authors / copyright / licence:** Copyright (c) 2026 Spectra
  Formalization Project; `Authors: Adam Bornemann`; Apache 2.0.
* **Extraction class:** *adapted.*  The proof architecture — differentiate
  `s ↦ exp((t-s)Bₙ) exp(sBₘ) ψ`, recognise the derivative as
  `exp((t-s)Bₙ) exp(sBₘ) (Bₘ - Bₙ) ψ`, integrate, and bound the integrand by
  unitarity — is Spectra's, and is the classical Duhamel argument.
* **Semantic differences from the donor:**
  1. Stated over Mathlib's `NormedSpace.exp` rather than Spectra's hand-rolled
     `expBounded` power series.  Spectra proves the two agree
     (`expBounded_eq_exp`), so nothing is lost; what *is* saved is the 576 lines
     of `ExpBounded/{Helpers,Adjoint,Unitary}` establishing summability, the
     group law and unitarity, all of which Mathlib already has.
  2. Unitarity comes from `selfAdjoint.expUnitary`, and the derivative from
     `hasDerivAt_exp_smul_const` — Mathlib's derivative of `t ↦ exp (t • x)` in a
     *non-commutative* algebra.
-/

public section

namespace TauCeti

open Complex NormedSpace Filter Topology
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The exponential of a bounded operator scaled by a real time. -/
private noncomputable def expTime (B : H →L[ℂ] H) (t : ℝ) : H →L[ℂ] H :=
  exp (t • B)

@[simp] private theorem expTime_zero (B : H →L[ℂ] H) : expTime B 0 = 1 := by
  simp [expTime]

/-- `t ↦ exp (t • B)` has derivative `exp (t • B) * B`. -/
private theorem hasDerivAt_expTime (B : H →L[ℂ] H) (t : ℝ) :
    HasDerivAt (expTime B) (expTime B t * B) t :=
  hasDerivAt_exp_smul_const (𝕂 := ℝ) B t

/-- Commuting operators have commuting exponentials. -/
private theorem commute_expTime_of_commute {B C : H →L[ℂ] H} (h : Commute B C) (t : ℝ) :
    Commute C (expTime B t) :=
  ((h.symm.smul_right t)).exp_right

/-! ### Unitarity -/

omit [CompleteSpace H] in
/-- `t • (I • S) = I • ((t : ℂ) • S)`: the real and complex scalings agree. -/
private theorem real_smul_I_smul (S : H →L[ℂ] H) (t : ℝ) :
    t • (I • S) = I • ((t : ℂ) • S) := by
  rw [smul_comm]
  congr 1

/-- For self-adjoint `S`, `exp (t • (I • S))` is unitary, hence norm-preserving. -/
private theorem norm_expTime_I_smul (S : H →L[ℂ] H) (hS : IsSelfAdjoint S) (t : ℝ) (ψ : H) :
    ‖expTime (I • S) t ψ‖ = ‖ψ‖ := by
  have hsa : ((t : ℂ) • S) ∈ selfAdjoint (H →L[ℂ] H) := by
    rw [selfAdjoint.mem_iff, star_smul, hS.star_eq, Complex.star_def, Complex.conj_ofReal]
  have hval : expTime (I • S) t = (selfAdjoint.expUnitary ⟨(t : ℂ) • S, hsa⟩ : H →L[ℂ] H) := by
    rw [expTime, real_smul_I_smul]
    rfl
  have hstar : (ContinuousLinearMap.adjoint (expTime (I • S) t)) * expTime (I • S) t = 1 := by
    rw [hval]
    have := Unitary.coe_star_mul_self (selfAdjoint.expUnitary ⟨(t : ℂ) • S, hsa⟩)
    rwa [ContinuousLinearMap.star_eq_adjoint] at this
  have hinner : ⟪expTime (I • S) t ψ, expTime (I • S) t ψ⟫_ℂ = ⟪ψ, ψ⟫_ℂ := by
    calc ⟪expTime (I • S) t ψ, expTime (I • S) t ψ⟫_ℂ
        = ⟪(ContinuousLinearMap.adjoint (expTime (I • S) t)) (expTime (I • S) t ψ), ψ⟫_ℂ := by
          rw [ContinuousLinearMap.adjoint_inner_left]
      _ = ⟪((ContinuousLinearMap.adjoint (expTime (I • S) t)) * expTime (I • S) t) ψ, ψ⟫_ℂ := rfl
      _ = ⟪ψ, ψ⟫_ℂ := by rw [hstar]; rfl
  -- take real parts: `re ⟪x, x⟫ = ‖x‖ ^ 2`
  have h1 : ‖expTime (I • S) t ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
    rw [← @inner_self_eq_norm_sq ℂ, ← @inner_self_eq_norm_sq ℂ, hinner]
  have h2 := congrArg Real.sqrt h1
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h2

/-! ### The Duhamel estimate -/

/-- `s ↦ exp((t-s) • Bₙ)` differentiates to `-(exp((t-s) • Bₙ) * Bₙ)`. -/
private theorem hasDerivAt_expTime_sub (B : H →L[ℂ] H) (t s : ℝ) :
    HasDerivAt (fun s : ℝ => expTime B (t - s)) (-(expTime B (t - s) * B)) s := by
  have h2 : HasDerivAt (fun s : ℝ => t - s) (-1) s := by
    simpa using (hasDerivAt_id s).const_sub t
  simpa [Function.comp_def] using (hasDerivAt_expTime B (t - s)).scomp s h2

/-- `s ↦ exp(s • B) ψ` differentiates to `(exp(s • B) * B) ψ`. -/
private theorem hasDerivAt_expTime_apply (B : H →L[ℂ] H) (ψ : H) (s : ℝ) :
    HasDerivAt (fun s : ℝ => expTime B s ψ) ((expTime B s * B) ψ) s := by
  have h := ((ContinuousLinearMap.apply ℂ H ψ).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s
    (hasDerivAt_expTime B s)
  exact HasDerivAt.congr_deriv h rfl

/-- **The Duhamel estimate.**  For commuting skew-adjoint generators the two
unitary flows differ by at most `|t|` times the difference of the generators. -/
private theorem norm_expTime_sub_expTime_le {Sm Sn : H →L[ℂ] H}
    (hm : IsSelfAdjoint Sm) (hn : IsSelfAdjoint Sn) (hcomm : Commute Sm Sn)
    (t : ℝ) (ψ : H) :
    ‖expTime (I • Sm) t ψ - expTime (I • Sn) t ψ‖
      ≤ |t| * ‖(I • Sm - I • Sn) ψ‖ := by
  set Bm : H →L[ℂ] H := I • Sm with hBm
  set Bn : H →L[ℂ] H := I • Sn with hBn
  have hBcomm : Commute Bm Bn := (hcomm.smul_left I).smul_right I
  -- the derivative of the interpolating path
  have hderiv : ∀ s : ℝ, HasDerivAt
      (fun s => expTime Bn (t - s) (expTime Bm s ψ))
      (expTime Bn (t - s) (expTime Bm s ((Bm - Bn) ψ))) s := by
    intro s
    have hf := hasDerivAt_expTime_sub Bn t s
    have hu := hasDerivAt_expTime_apply Bm ψ s
    -- `Bn` commutes with `exp(s • Bm)`
    have hcEn : Commute Bn (expTime Bm s) := commute_expTime_of_commute hBcomm s
    have hswap : Bn (expTime Bm s ψ) = expTime Bm s (Bn ψ) := by
      have h := congrArg (fun T : H →L[ℂ] H => T ψ) hcEn
      simpa using h
    have hval : expTime Bn (t - s) (expTime Bm s ((Bm - Bn) ψ))
        = (-(expTime Bn (t - s) * Bn)) (expTime Bm s ψ)
          + expTime Bn (t - s) ((expTime Bm s * Bm) ψ) := by
      have hsub : expTime Bm s ((Bm - Bn) ψ)
          = (expTime Bm s * Bm) ψ - Bn (expTime Bm s ψ) := by
        rw [hswap]
        simp only [sub_apply, map_sub]
        rfl
      rw [hsub, map_sub]
      simp only [neg_apply]
      abel
    -- `clm_apply` differentiates in `ℝ`, so the ℂ-linear operators must have their
    -- scalars restricted first
    have hf' := (ContinuousLinearMap.restrictScalarsL ℂ H H ℝ ℝ).hasFDerivAt.comp_hasDerivAt s hf
    rw [hval]
    simpa using HasDerivAt.clm_apply hf' hu
  -- continuity of the derivative, for integrability
  have hcont : Continuous
      (fun s : ℝ => expTime Bn (t - s) (expTime Bm s ((Bm - Bn) ψ))) := by
    have cBn : Continuous (fun τ : ℝ => expTime Bn τ) :=
      Differentiable.continuous fun τ => (hasDerivAt_expTime Bn τ).differentiableAt
    have cBm : Continuous (fun τ : ℝ => expTime Bm τ) :=
      Differentiable.continuous fun τ => (hasDerivAt_expTime Bm τ).differentiableAt
    exact (cBn.comp (continuous_const.sub continuous_id)).clm_apply
      (cBm.clm_apply continuous_const)
  -- fundamental theorem of calculus
  have hftc : (∫ s in (0 : ℝ)..t, expTime Bn (t - s) (expTime Bm s ((Bm - Bn) ψ)))
      = expTime Bm t ψ - expTime Bn t ψ := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun s => expTime Bn (t - s) (expTime Bm s ψ))
      (fun s _ => hderiv s) (hcont.intervalIntegrable 0 t)
    simpa using h
  -- the integrand has constant norm, by unitarity of both flows
  have hnorm : ∀ s : ℝ,
      ‖expTime Bn (t - s) (expTime Bm s ((Bm - Bn) ψ))‖ = ‖(Bm - Bn) ψ‖ := by
    intro s
    rw [hBn, norm_expTime_I_smul Sn hn, hBm, norm_expTime_I_smul Sm hm]
  calc ‖expTime Bm t ψ - expTime Bn t ψ‖
      = ‖∫ s in (0 : ℝ)..t, expTime Bn (t - s) (expTime Bm s ((Bm - Bn) ψ))‖ := by rw [hftc]
    _ ≤ ‖(Bm - Bn) ψ‖ * |t - 0| := by
        refine intervalIntegral.norm_integral_le_of_norm_le_const fun s _ => ?_
        exact le_of_eq (hnorm s)
    _ = |t| * ‖(Bm - Bn) ψ‖ := by rw [sub_zero, mul_comm]

variable {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)

private noncomputable def yosidaFlow (A : H →ₗ.[ℂ] H) (n : ℕ+) (t : ℝ) : H →L[ℂ] H :=
  expTime (I • A.symmetricYosidaApproximation (n : ℝ)) t

private theorem yosidaFlow_norm (hA : IsSelfAdjoint A) (n : ℕ+) (t : ℝ) (x : H) :
    ‖yosidaFlow A n t x‖ = ‖x‖ := by
  exact norm_expTime_I_smul _ (hA.isSelfAdjoint_symmetricYosidaApproximation (n : ℝ)) t x

private theorem yosidaFlow_difference (hA : IsSelfAdjoint A) (m n : ℕ+) (t : ℝ) (x : H) :
    ‖yosidaFlow A m t x - yosidaFlow A n t x‖ ≤
      |t| * ‖A.symmetricYosidaApproximation (m : ℝ) x -
        A.symmetricYosidaApproximation (n : ℝ) x‖ := by
  have h := norm_expTime_sub_expTime_le (hA.isSelfAdjoint_symmetricYosidaApproximation (m : ℝ))
    (hA.isSelfAdjoint_symmetricYosidaApproximation (n : ℝ))
    (hA.commute_symmetricYosidaApproximation (m : ℝ) (n : ℝ)) t x
  simpa only [yosidaFlow, sub_apply, smul_apply, ← smul_sub, norm_smul, norm_I, one_mul] using h

/-- Symmetric Yosida exponential orbits are uniformly Cauchy on bounded time intervals. -/
theorem _root_.IsSelfAdjoint.yosida_exponential_uniform_cauchy
    (hA : IsSelfAdjoint A) (x : H) (R : ℝ) (ε : ℝ)
    (hε : 0 < ε) : ∃ N : ℕ+, ∀ m ≥ N, ∀ n ≥ N, ∀ t : ℝ, |t| ≤ R →
      ‖NormedSpace.exp (t • (I • A.symmetricYosidaApproximation (m : ℝ))) x -
        NormedSpace.exp (t • (I • A.symmetricYosidaApproximation (n : ℝ))) x‖ < ε := by
  let K := max R 0 + 1
  have hK : 0 < K := by dsimp [K]; positivity
  have hdense : Dense (A.domain : Set H) := hA.dense_domain
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp
    (hdense.closure_eq ▸ Set.mem_univ x) (ε / 3) (by positivity)
  have hconv := ((hA.tendsto_symmetricYosidaApproximation_apply ⟨y, hy⟩).mono_left
    atTop_le_cocompact).comp (tendsto_natCast_atTop_atTop.comp tendsto_PNat_val_atTop_atTop)
  have hc := hconv.cauchySeq
  rw [Metric.cauchySeq_iff] at hc
  obtain ⟨N, hN⟩ := hc (ε / (3 * K)) (by positivity)
  refine ⟨N, fun m hm n hn t ht => ?_⟩
  have hmn := hN m hm n hn
  rw [dist_eq_norm] at hmn
  have hbound : |t| ≤ K := le_trans ht (le_trans (le_max_left R 0) (by dsimp [K]; linarith))
  have hmid : ‖yosidaFlow A m t y - yosidaFlow A n t y‖ < ε / 3 := by
    calc
      ‖yosidaFlow A m t y - yosidaFlow A n t y‖ ≤
          |t| * ‖A.symmetricYosidaApproximation (m : ℝ) y -
            A.symmetricYosidaApproximation (n : ℝ) y‖ := yosidaFlow_difference hA m n t y
      _ ≤ K * ‖A.symmetricYosidaApproximation (m : ℝ) y -
            A.symmetricYosidaApproximation (n : ℝ) y‖ :=
        mul_le_mul_of_nonneg_right hbound (norm_nonneg _)
      _ < K * (ε / (3 * K)) := mul_lt_mul_of_pos_left hmn hK
      _ = ε / 3 := by field_simp
  have hleft : dist (yosidaFlow A m t x) (yosidaFlow A m t y) = dist x y := by
    rw [dist_eq_norm, dist_eq_norm, ← ContinuousLinearMap.map_sub, yosidaFlow_norm hA]
  have hright : dist (yosidaFlow A n t y) (yosidaFlow A n t x) = dist y x := by
    rw [dist_eq_norm, dist_eq_norm, ← ContinuousLinearMap.map_sub, yosidaFlow_norm hA]
  change ‖yosidaFlow A m t x - yosidaFlow A n t x‖ < ε
  rw [← dist_eq_norm]
  calc
    dist (yosidaFlow A m t x) (yosidaFlow A n t x) ≤
        dist (yosidaFlow A m t x) (yosidaFlow A m t y) +
        dist (yosidaFlow A m t y) (yosidaFlow A n t y) +
        dist (yosidaFlow A n t y) (yosidaFlow A n t x) := dist_triangle4 _ _ _ _
    _ = dist x y + ‖yosidaFlow A m t y - yosidaFlow A n t y‖ + dist y x := by
      rw [hleft, hright]
      simp only [dist_eq_norm]
    _ < ε / 3 + ε / 3 + ε / 3 := by
      rw [dist_comm y x]
      linarith
    _ = ε := by ring

end TauCeti
