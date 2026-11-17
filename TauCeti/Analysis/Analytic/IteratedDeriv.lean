/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import TauCeti.Analysis.Analytic.Constructions
import TauCeti.Topology.Algebra.Module.Equiv.Pi

/-!
# Analyticity of iterated vertical slice derivatives

Mathlib proves that the `n`-fold iterate `deriv^[n] f` of an analytic function `f : 𝕜 → F` into a
complete normed space is analytic (`AnalyticAt.iterated_deriv`). This file proves the parametric
two-variable version for `iteratedDeriv`: if `f : E × 𝕜 → F` is jointly analytic at `p`, then
`(q : E × 𝕜) ↦ iteratedDeriv n (fun y ↦ f (q.1, y)) q.2` is jointly analytic at `p`
(`AnalyticAt.iteratedDeriv_snd`), and in particular the vertical Taylor coefficient
`x ↦ iteratedDeriv n (fun y ↦ f (x, y)) p.2` is analytic at `p.1`
(`AnalyticAt.curry_left_iteratedDeriv_snd`).

In `σ ⊕ τ → 𝕜` coordinates with `τ` unique, `TauCeti.iteratedDerivInr k f` packages the `k`-th
iterated derivative in the `Sum.inr` coordinate. It satisfies the Fréchet-derivative step
`DifferentiableAt.iteratedDerivInr_succ_eq_fderiv`, preserves analyticity
(`AnalyticAt.iteratedDerivInr`, `AnalyticOnNhd.iteratedDerivInr`), and characterizes the analytic
order of vertical slices (`AnalyticAt.analyticOrderAt_sumElim_eq_nat_iff`).
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

end AnalyticAt

namespace TauCeti

variable {𝕜 σ τ F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The `k`-th iterated derivative of a constant-across-coordinates family `ζ ↦ fun _ : α ↦ g ζ`
is the constant family of `k`-th iterated derivatives. -/
theorem iteratedDeriv_const_pi {α : Type*} [Fintype α] (k : ℕ) (g : 𝕜 → F) (w : 𝕜) :
    iteratedDeriv k (fun ζ (_ : α) ↦ g ζ) w = fun _ ↦ iteratedDeriv k g w := by
  by_cases hα : Nonempty α
  · induction k generalizing w with
    | zero => rfl
    | succ k ih =>
      rw [iteratedDeriv_succ, iteratedDeriv_succ]
      have hfun : iteratedDeriv k (fun ζ (_ : α) ↦ g ζ) = fun ζ (_ : α) ↦ iteratedDeriv k g ζ :=
        funext ih
      rw [hfun]
      by_cases hd : DifferentiableAt 𝕜 (iteratedDeriv k g) w
      · exact (hasDerivAt_pi.mpr fun _ ↦ hd.hasDerivAt).deriv
      · have hd' : ¬ DifferentiableAt 𝕜 (fun ζ (_ : α) ↦ iteratedDeriv k g ζ) w := fun h ↦
          hd ((differentiableAt_pi.mp h) (Classical.arbitrary α))
        rw [deriv_zero_of_not_differentiableAt hd, deriv_zero_of_not_differentiableAt hd']
        rfl
  · funext a
    exact (hα ⟨a⟩).elim

/-- The `k`-th iterated derivative of `f : (σ ⊕ τ → 𝕜) → F` in the distinguished coordinate indexed
by the unique type `τ`. -/
noncomputable def iteratedDerivInr [Unique τ] (k : ℕ) (f : (σ ⊕ τ → 𝕜) → F)
    (z : σ ⊕ τ → 𝕜) : F :=
  iteratedDeriv k (fun w ↦ f (Sum.elim (z ∘ Sum.inl) (fun _ ↦ w))) (z (.inr default))

/-- The `0`-th iterated derivative in the `Sum.inr` coordinate is the function itself. -/
@[simp]
theorem iteratedDerivInr_zero [Unique τ] (f : (σ ⊕ τ → 𝕜) → F) :
    iteratedDerivInr 0 f = f := by
  funext z
  simp only [iteratedDerivInr, iteratedDeriv_zero]
  congr 1
  funext j
  rcases j with i | t
  · rfl
  · simp [Unique.eq_default t]

/-- Evaluating `iteratedDerivInr k f` at `Sum.elim x (fun _ ↦ w)` gives the `k`-th iterated
derivative of the vertical slice `ζ ↦ f (Sum.elim x (fun _ ↦ ζ))` at `w`. -/
@[simp]
theorem iteratedDerivInr_sumElim [Unique τ] (k : ℕ) (f : (σ ⊕ τ → 𝕜) → F)
    (x : σ → 𝕜) (w : 𝕜) :
    iteratedDerivInr k f (Sum.elim x (fun _ ↦ w)) =
      iteratedDeriv k (fun ζ ↦ f (Sum.elim x (fun _ ↦ ζ))) w := by
  simp only [iteratedDerivInr, Sum.elim_comp_inl, Sum.elim_inr]

/-- Differentiating a constant-across-coordinates family `y ↦ fun _ : α ↦ f y` in the `Sum.inr`
coordinate commutes with forming the constant tuple. -/
theorem iteratedDerivInr_const_pi {α : Type*} [Fintype α] [Unique τ] (k : ℕ)
    (f : (σ ⊕ τ → 𝕜) → F) (z : σ ⊕ τ → 𝕜) :
    iteratedDerivInr k (fun y (_ : α) ↦ f y) z = fun _ ↦ iteratedDerivInr k f z :=
  iteratedDeriv_const_pi k _ _

end TauCeti

section IteratedDerivInr

variable {𝕜 σ τ F : Type*} [NontriviallyNormedField 𝕜] [Unique τ]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- If `TauCeti.iteratedDerivInr k f` is differentiable at `z`, then its `(k + 1)`-th derivative in
the `Sum.inr` coordinate equals its Fréchet derivative at `z` in the unit `Sum.inr` direction
`Sum.elim 0 (fun _ ↦ 1)`. -/
theorem DifferentiableAt.iteratedDerivInr_succ_eq_fderiv [Finite σ] {f : (σ ⊕ τ → 𝕜) → F} {k : ℕ}
    {z : σ ⊕ τ → 𝕜} (hf : DifferentiableAt 𝕜 (TauCeti.iteratedDerivInr k f) z) :
    TauCeti.iteratedDerivInr (k + 1) f z =
      fderiv 𝕜 (TauCeti.iteratedDerivInr k f) z (Sum.elim 0 (fun _ ↦ 1)) := by
  let _ := Fintype.ofFinite σ
  let v : σ ⊕ τ → 𝕜 := Sum.elim 0 (fun _ ↦ 1)
  let φ : 𝕜 → (σ ⊕ τ → 𝕜) := fun w ↦ z + (w - z (.inr default)) • v
  have hφ_eq (w : 𝕜) : φ w = Sum.elim (z ∘ Sum.inl) (fun _ ↦ w) := by
    ext (i | t)
    · simp [φ, v]
    · simp [φ, v, Unique.eq_default t]
  have hφ_deriv : HasDerivAt φ v (z (.inr default)) := by
    simpa [φ] using
      (((hasDerivAt_id (z (.inr default))).sub_const (z (.inr default))).smul_const v).const_add z
  have hφz : φ (z (.inr default)) = z := by simp [φ]
  have hGφ := hφz ▸ hf.hasFDerivAt
  have hstep : TauCeti.iteratedDerivInr (k + 1) f z =
      deriv (fun w ↦ TauCeti.iteratedDerivInr k f (φ w)) (z (.inr default)) := by
    simp only [TauCeti.iteratedDerivInr, hφ_eq, Sum.elim_comp_inl, Sum.elim_inr, iteratedDeriv_succ]
  rw [hstep]
  simpa [hφz, Function.comp_def] using (hGφ.comp_hasDerivAt (z (.inr default)) hφ_deriv).deriv

variable [Fintype σ]

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
  simp [TauCeti.iteratedDerivInr, e]

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
