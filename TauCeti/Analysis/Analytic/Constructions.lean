/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Constructions

/-!
# Analytic constructions: products, slices, and finite sums

Mathlib's `AnalyticAt.curry_right` says that a function analytic at `p` on a product has an
analytic slice `y ↦ f (p.1, y)` at `p.2`. Since the analytic locus is open, the same holds for the
slices `y ↦ f (x, y)` with `x` near `p.1` (`AnalyticAt.eventually_analyticAt_curry_right`).

Concatenating two finite families of vectors, `p ↦ Sum.elim p.1 p.2`, is analytic
(`TauCeti.analyticAt_sumElim`, `TauCeti.analyticOnNhd_sumElim`), as are concatenating a family with
a constant family (`TauCeti.analyticAt_sumElim_const`), reindexing coordinates along a map
(`TauCeti.analyticAt_comp_right`), splitting a family on `ι ⊕ ι'`
(`TauCeti.analyticAt_prod_comp_inl_inr`, `TauCeti.analyticAt_prod_comp_inl_apply_inr`), and taking
slices `t ↦ f (Sum.elim x (fun _ ↦ t))` (`AnalyticAt.comp_sumElim_const`,
`TauCeti.analyticOnNhd_comp_sumElim_const`).

Finite sums of functions admitting power series on a common ball admit the summed power series on
that ball (`Finset.hasFPowerSeriesOnBall_sum`, `Finset.hasFPowerSeriesWithinOnBall_sum`).
-/

public section

open Filter Topology

section Products

variable {𝕜 E E' F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] [CompleteSpace F]

/-- The slices `y ↦ f (x, y)` of a function analytic at `p` are analytic at `p.2` for every `x`
near `p.1`. -/
theorem AnalyticAt.eventually_analyticAt_curry_right {f : E × E' → F} {p : E × E'}
    (hf : AnalyticAt 𝕜 f p) : ∀ᶠ x in 𝓝 p.1, AnalyticAt 𝕜 (fun y ↦ f (x, y)) p.2 :=
  ((continuous_id.prodMk continuous_const).tendsto p.1).eventually hf.eventually_analyticAt
    |>.mono fun _ hx ↦ hx.curry_right

namespace TauCeti

/-- Concatenating two finite families of vectors, `p ↦ Sum.elim p.1 p.2`, is analytic. -/
theorem analyticAt_sumElim {ι ι' : Type*} [Fintype ι] [Fintype ι'] {p : (ι → E) × (ι' → E)} :
    AnalyticAt 𝕜 (fun p : (ι → E) × (ι' → E) ↦ Sum.elim p.1 p.2) p := by
  refine analyticAt_pi_iff.2 fun i ↦ ?_
  cases i with
  | inl i => exact (analyticAt_pi_iff.1 analyticAt_fst) i
  | inr i => exact (analyticAt_pi_iff.1 analyticAt_snd) i

/-- Concatenating two finite families of vectors, `p ↦ Sum.elim p.1 p.2`, is analytic. -/
theorem analyticOnNhd_sumElim {ι ι' : Type*} [Fintype ι] [Fintype ι']
    {s : Set ((ι → E) × (ι' → E))} :
    AnalyticOnNhd 𝕜 (fun p : (ι → E) × (ι' → E) ↦ Sum.elim p.1 p.2) s :=
  fun _ _ ↦ analyticAt_sumElim

/-- Concatenating a finite family of vectors with a constant family,
`p ↦ Sum.elim p.1 (fun _ ↦ p.2)`, is analytic. -/
theorem analyticAt_sumElim_const {ι ι' : Type*} [Fintype ι] [Fintype ι'] {p : (ι → E) × E} :
    AnalyticAt 𝕜 (fun p : (ι → E) × E ↦ Sum.elim p.1 fun _ : ι' ↦ p.2) p :=
  analyticAt_sumElim.comp₂ analyticAt_fst (analyticAt_pi_iff.2 fun _ ↦ analyticAt_snd)

/-- Reindexing coordinates along a map `e : ι → ι'`, sending `y : ι' → E` to `y ∘ e`, is
analytic. -/
theorem analyticAt_comp_right {ι ι' : Type*} [Fintype ι] [Fintype ι'] (e : ι → ι')
    {y : ι' → E} : AnalyticAt 𝕜 (fun y : ι' → E ↦ y ∘ e) y :=
  analyticAt_pi_iff.2 fun i ↦ (analyticAt_pi_iff.1 analyticAt_id) (e i)

/-- Splitting a family on a disjoint union `p : ι ⊕ ι' → E` into `(p ∘ Sum.inl, p ∘ Sum.inr)` is
analytic. -/
theorem analyticAt_prod_comp_inl_inr {ι ι' : Type*} [Fintype ι] [Fintype ι'] {p : ι ⊕ ι' → E} :
    AnalyticAt 𝕜 (fun p : ι ⊕ ι' → E ↦ (p ∘ Sum.inl, p ∘ Sum.inr)) p :=
  (analyticAt_comp_right Sum.inl).prod (analyticAt_comp_right Sum.inr)

/-- Splitting a family `p : ι ⊕ ι' → E` into `(p ∘ Sum.inl, p (Sum.inr j))` is analytic. -/
theorem analyticAt_prod_comp_inl_apply_inr {ι ι' : Type*} [Fintype ι] [Fintype ι'] (j : ι')
    {p : ι ⊕ ι' → E} :
    AnalyticAt 𝕜 (fun p : ι ⊕ ι' → E ↦ (p ∘ Sum.inl, p (.inr j))) p :=
  (analyticAt_fst.prod ((analyticAt_pi_iff.1 analyticAt_snd) j)).comp analyticAt_prod_comp_inl_inr

omit [CompleteSpace F] in
/-- If `f : (ι ⊕ ι' → E) → F` is analytic at `Sum.elim x (fun _ ↦ t₀)`, then its slice
`t ↦ f (Sum.elim x (fun _ ↦ t))` is analytic at `t₀`. -/
theorem _root_.AnalyticAt.comp_sumElim_const {ι ι' : Type*} [Fintype ι] [Fintype ι']
    {f : (ι ⊕ ι' → E) → F} {x : ι → E} {t₀ : E}
    (hf : AnalyticAt 𝕜 f (Sum.elim x fun _ ↦ t₀)) :
    AnalyticAt 𝕜 (fun t ↦ f (Sum.elim x fun _ ↦ t)) t₀ :=
  hf.fun_comp_of_eq (analyticAt_sumElim_const.comp (analyticAt_const.prod analyticAt_id)) rfl

omit [CompleteSpace F] in
/-- If `f : (ι ⊕ ι' → E) → F` is analytic at `Sum.elim x (fun _ ↦ t)` for every `t ∈ s`, then its
slice `t ↦ f (Sum.elim x (fun _ ↦ t))` is analytic on `s`. -/
theorem analyticOnNhd_comp_sumElim_const {ι ι' : Type*} [Fintype ι] [Fintype ι']
    {f : (ι ⊕ ι' → E) → F} {x : ι → E} {s : Set E}
    (hf : ∀ t ∈ s, AnalyticAt 𝕜 f (Sum.elim x fun _ ↦ t)) :
    AnalyticOnNhd 𝕜 (fun t ↦ f (Sum.elim x fun _ ↦ t)) s :=
  fun t ht ↦ (hf t ht).comp_sumElim_const

end TauCeti

end Products

section FinsetSum

open scoped ENNReal

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Finite sums of functions admitting power series on a common ball within `s` admit the summed
power series on the same ball. -/
@[to_fun Finset.hasFPowerSeriesWithinOnBall_fun_sum]
theorem Finset.hasFPowerSeriesWithinOnBall_sum {ι : Type*} {f : ι → E → F}
    {p : ι → FormalMultilinearSeries 𝕜 E F} {s : Set E} {x : E} {r : ℝ≥0∞}
    (I : Finset ι) (hr : 0 < r)
    (h : ∀ i ∈ I, HasFPowerSeriesWithinOnBall (f i) (p i) s x r) :
    HasFPowerSeriesWithinOnBall (∑ i ∈ I, f i) (∑ i ∈ I, p i) s x r := by
  classical
  induction I using Finset.induction with
  | empty => exact ⟨by simp, hr, fun _ _ ↦ hasSum_zero⟩
  | insert a I haI ih =>
    rw [Finset.sum_insert haI, Finset.sum_insert haI]
    exact (h a (Finset.mem_insert_self a I)).add
      (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi))

/-- Finite sums of functions admitting power series on a common ball admit the summed power series
on the same ball. -/
@[to_fun Finset.hasFPowerSeriesOnBall_fun_sum]
theorem Finset.hasFPowerSeriesOnBall_sum {ι : Type*} {f : ι → E → F}
    {p : ι → FormalMultilinearSeries 𝕜 E F} {x : E} {r : ℝ≥0∞}
    (I : Finset ι) (hr : 0 < r)
    (h : ∀ i ∈ I, HasFPowerSeriesOnBall (f i) (p i) x r) :
    HasFPowerSeriesOnBall (∑ i ∈ I, f i) (∑ i ∈ I, p i) x r := by
  simp_rw [← hasFPowerSeriesWithinOnBall_univ] at h ⊢
  exact I.hasFPowerSeriesWithinOnBall_sum hr h

end FinsetSum
