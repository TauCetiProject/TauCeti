/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Analytic.Order
public import TauCeti.Analysis.Calculus.IteratedDeriv.Basic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import TauCeti.Analysis.Analytic.Constructions
import TauCeti.Topology.Algebra.Module.Equiv.Pi

/-!
# Analyticity of iterated slice derivatives

Mathlib proves that the `n`-fold iterate `deriv^[n] f` of an analytic function `f : 𝕜 → F` into a
complete normed space is analytic (`AnalyticAt.iterated_deriv`). This file proves the parametric
two-variable versions: if `f : E × 𝕜 → F` is jointly analytic at `p`, then
`(q : E × 𝕜) ↦ iteratedDeriv n (fun y ↦ f (q.1, y)) q.2` is jointly analytic at `p`
(`AnalyticAt.iteratedDeriv_snd`), its vertical Taylor coefficient
`x ↦ iteratedDeriv n (fun y ↦ f (x, y)) p.2` is analytic at `p.1`
(`AnalyticAt.curry_left_iteratedDeriv_snd`), and the first partial derivatives in the second and
first scalar variables are jointly analytic at `p` (`AnalyticAt.deriv_snd`, `AnalyticAt.deriv_fst`).

For `TauCeti.iteratedDerivInr k f` (defined in `TauCeti.Analysis.Calculus.IteratedDeriv.Basic` as
the `k`-th iterated derivative in the `Sum.inr` coordinate of `σ ⊕ τ → 𝕜` with `τ` unique), this
file proves that it preserves analyticity (`AnalyticAt.iteratedDerivInr`,
`AnalyticOnNhd.iteratedDerivInr`) and characterizes the analytic order of vertical slices
(`AnalyticAt.analyticOrderAt_sumElim_eq_nat_iff`).
-/

public section

open Filter Metric Topology

namespace AnalyticAt

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

/-- If `f : E × 𝕜 → F` is jointly analytic at `p` and `F` is complete, then the `n`-th iterated
derivative in the second variable `(q : E × 𝕜) ↦ iteratedDeriv n (fun y ↦ f (q.1, y)) q.2` is
jointly analytic at `p`. -/
theorem iteratedDeriv_snd {f : E × 𝕜 → F} {p : E × 𝕜} (hf : AnalyticAt 𝕜 f p) :
    ∀ n : ℕ, AnalyticAt 𝕜 (fun q : E × 𝕜 ↦ iteratedDeriv n (fun y ↦ f (q.1, y)) q.2) p
  | 0 => by simpa only [iteratedDeriv_zero] using hf
  | n + 1 => by
    set f' : E × 𝕜 → F := fun q ↦ fderiv 𝕜 f q (0, 1)
    have hf' : AnalyticAt 𝕜 f' p :=
      ((ContinuousLinearMap.apply 𝕜 F ((0 : E), (1 : 𝕜))).analyticAt _).comp hf.fderiv
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 (isOpen_analyticAt 𝕜 f) p hf
    refine (hf'.iteratedDeriv_snd n).congr ?_
    filter_upwards [ball_mem_nhds p (half_pos hr)] with q hq
    have hq_lt : dist q p < r := (mem_ball.1 hq).trans (half_lt_self hr)
    have hderiv_eq : (fun y ↦ f' (q.1, y)) =ᶠ[𝓝 q.2] deriv (fun y ↦ f (q.1, y)) := by
      have hy_open : {y : 𝕜 | (q.1, y) ∈ ball p r} ∈ 𝓝 q.2 :=
        ((continuous_const.prodMk continuous_id).tendsto q.2).eventually
          (isOpen_ball.mem_nhds (mem_ball.2 hq_lt))
      filter_upwards [hy_open] with y hy
      exact (((hball hy).differentiableAt.hasFDerivAt.comp_hasDerivAt y
        ((hasDerivAt_const y q.1).prodMk (hasDerivAt_id y))).deriv).symm
    rw [iteratedDeriv_succ']
    exact hderiv_eq.iteratedDeriv_eq n

/-- If `f : E × 𝕜 → F` is jointly analytic at `p` and `F` is complete, then
`x ↦ iteratedDeriv n (fun y ↦ f (x, y)) p.2` is analytic at `p.1`. -/
theorem curry_left_iteratedDeriv_snd {f : E × 𝕜 → F} {p : E × 𝕜} (hf : AnalyticAt 𝕜 f p) (n : ℕ) :
    AnalyticAt 𝕜 (fun x : E ↦ iteratedDeriv n (fun y ↦ f (x, y)) p.2) p.1 :=
  (hf.iteratedDeriv_snd n).curry_left

/-- If `f : E × 𝕜 → F` is jointly analytic at `p` and `F` is complete, then its partial derivative
in the second variable `(q : E × 𝕜) ↦ deriv (fun y ↦ f (q.1, y)) q.2` is jointly analytic at
`p`. -/
theorem deriv_snd {f : E × 𝕜 → F} {p : E × 𝕜} (hf : AnalyticAt 𝕜 f p) :
    AnalyticAt 𝕜 (fun q : E × 𝕜 ↦ deriv (fun y ↦ f (q.1, y)) q.2) p := by
  simpa only [iteratedDeriv_one] using hf.iteratedDeriv_snd 1

/-- If `f : 𝕜 × E → F` is jointly analytic at `p` and `F` is complete, then its partial derivative
in the first variable `(q : 𝕜 × E) ↦ deriv (fun x ↦ f (x, q.2)) q.1` is jointly analytic at
`p`. -/
theorem deriv_fst {f : 𝕜 × E → F} {p : 𝕜 × E} (hf : AnalyticAt 𝕜 f p) :
    AnalyticAt 𝕜 (fun q : 𝕜 × E ↦ deriv (fun x ↦ f (x, q.2)) q.1) p := by
  have hswap : AnalyticAt 𝕜 (fun r : E × 𝕜 ↦ f (r.2, r.1)) (p.2, p.1) :=
    hf.comp_of_eq (analyticAt_snd.prod analyticAt_fst) rfl
  exact hswap.deriv_snd.comp_of_eq (analyticAt_snd.prod analyticAt_fst) rfl

end AnalyticAt

section IteratedDerivInr

variable {𝕜 σ τ F : Type*} [NontriviallyNormedField 𝕜] [Fintype σ] [Unique τ]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- If `f : (σ ⊕ τ → 𝕜) → F` is analytic at `z` and `F` is complete, with `σ` finite and `τ`
unique, then `TauCeti.iteratedDerivInr k f` is analytic at `z`. -/
theorem AnalyticAt.iteratedDerivInr [CompleteSpace F] {f : (σ ⊕ τ → 𝕜) → F} {z : σ ⊕ τ → 𝕜}
    (hf : AnalyticAt 𝕜 f z) (k : ℕ) :
    AnalyticAt 𝕜 (TauCeti.iteratedDerivInr k f) z := by
  let e := ContinuousLinearEquiv.piProdEquivPiSumUnique 𝕜 σ τ 𝕜
  have hfe : AnalyticAt 𝕜 (f ∘ e) (e.symm z) :=
    hf.comp_of_eq (e.analyticAt _) (e.apply_symm_apply z)
  have hcomp : AnalyticAt 𝕜
      (fun y : σ ⊕ τ → 𝕜 ↦ iteratedDeriv k (fun w ↦ (f ∘ e) ((e.symm y).1, w)) (e.symm y).2) z :=
    (hfe.iteratedDeriv_snd k).comp (e.symm.analyticAt z)
  refine hcomp.congr (.of_forall fun y ↦ ?_)
  simp [TauCeti.iteratedDerivInr_apply, e]

/-- If `f : (σ ⊕ τ → 𝕜) → F` is analytic on `s` and `F` is complete, with `σ` finite and `τ`
unique, then `TauCeti.iteratedDerivInr k f` is analytic on `s`. -/
theorem AnalyticOnNhd.iteratedDerivInr [CompleteSpace F] {f : (σ ⊕ τ → 𝕜) → F}
    {s : Set (σ ⊕ τ → 𝕜)} (hf : AnalyticOnNhd 𝕜 f s) (k : ℕ) :
    AnalyticOnNhd 𝕜 (TauCeti.iteratedDerivInr k f) s :=
  fun z hz ↦ (hf z hz).iteratedDerivInr k

/-- For `f : (σ ⊕ τ → 𝕜) → F` analytic at `Sum.elim x (fun _ ↦ w)`, with `σ` finite, `τ` unique,
`CharZero 𝕜`, and `F` complete, the analytic order of the vertical slice
`ζ ↦ f (Sum.elim x (fun _ ↦ ζ))` at `w` equals `n` if and only if the first `n` derivatives in the
`Sum.inr` coordinate vanish at `Sum.elim x (fun _ ↦ w)` and the `n`-th does not. -/
theorem AnalyticAt.analyticOrderAt_sumElim_eq_nat_iff [CharZero 𝕜] [CompleteSpace F]
    {f : (σ ⊕ τ → 𝕜) → F} {x : σ → 𝕜} {w : 𝕜}
    (hf : AnalyticAt 𝕜 f (Sum.elim x (fun _ ↦ w))) (n : ℕ) :
    analyticOrderAt (fun ζ ↦ f (Sum.elim x (fun _ ↦ ζ))) w = n ↔
      (∀ k < n, TauCeti.iteratedDerivInr k f (Sum.elim x (fun _ ↦ w)) = 0) ∧
        TauCeti.iteratedDerivInr n f (Sum.elim x (fun _ ↦ w)) ≠ 0 := by
  have hslice : AnalyticAt 𝕜 (fun ζ ↦ f (Sum.elim x (fun _ ↦ ζ))) w :=
    hf.comp_of_eq (TauCeti.analyticAt_sumElim_const x w) rfl
  rw [analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero hslice]
  simp

end IteratedDerivInr
