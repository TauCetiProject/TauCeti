/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj
public import TauCeti.Probability.DenoisingDiffusion.NoiseKernel

/-!
# The forward noising chain of a denoising diffusion model

A noise schedule `β : ℕ → ℝ` assigns to each step `t ≥ 1` a noise level `β t ∈ [0, 1]`. The
forward chain of a denoising diffusion model starts from a law `μ₀` on `EuclideanSpace ℝ ι` and
moves from the state at time `n` to the state at time `n + 1` by the noising kernel
`noiseKernel (1 - β (n + 1))`. Its path law up to a horizon `T` is built with Mathlib's
`ProbabilityTheory.Kernel.partialTraj`, on paths indexed by `Finset.Iic T`.

Since composing noising kernels multiplies their signal levels, the state at time `t` given the
initial state `x₀` is `noiseKernel (alphaBar β t) x₀`, where `alphaBar β t` is the product of the
signal levels `1 - β s` for `1 ≤ s ≤ t`. This file proves this closed form, both for the
marginals of the path law and for the joint law of the initial and the time-`t` states.

## Main definitions

* `TauCeti.Probability.alphaBar`: the cumulative signal level `∏_{s=1}^t (1 - β s)`.
* `TauCeti.Probability.pathEval`: evaluation of a path indexed by `Finset.Iic n` at a time `i ≤ n`.
* `TauCeti.Probability.forwardStep`: the step kernel of the forward chain on paths.
* `TauCeti.Probability.forwardPath`: the law of the forward chain on paths up to time `T`.
* `TauCeti.Probability.forwardMarginal`: the law `noiseKernel (alphaBar β t) ∘ₘ μ₀`.

## Main results

* `TauCeti.Probability.forwardPath_map_eval`: the time-`t` marginal of the path law is
  `forwardMarginal μ₀ β t`.
* `TauCeti.Probability.forwardPath_map_eval_zero_eval`: the joint law of the states at times `0`
  and `t` is `μ₀ ⊗ₘ noiseKernel (alphaBar β t)`.
* `TauCeti.Probability.forwardPath_map_eval_zero`: for every `β`, the path law starts from `μ₀`.
* `TauCeti.Probability.forwardMarginal_succ`: the marginals satisfy the forward recursion.
* `TauCeti.Probability.forwardMarginal_stdGaussian`: the standard Gaussian law is stationary.

## References

* J. Ho, A. Jain and P. Abbeel, *Denoising diffusion probabilistic models*, NeurIPS 2020,
  equations (2) and (4).
-/

public section

open MeasureTheory ProbabilityTheory Finset

namespace TauCeti.Probability

/-! ### Cumulative signal levels -/

section AlphaBar

variable {β : ℕ → ℝ}

/-- The cumulative signal level `alphaBar β t = ∏_{s=1}^t (1 - β s)` of a noise schedule `β`. -/
noncomputable def alphaBar (β : ℕ → ℝ) (t : ℕ) : ℝ :=
  ∏ s ∈ Icc 1 t, (1 - β s)

/-- Unfolding lemma for `alphaBar`. -/
theorem alphaBar_def (β : ℕ → ℝ) (t : ℕ) : alphaBar β t = ∏ s ∈ Icc 1 t, (1 - β s) := (rfl)

/-- With no step taken the signal level is `1`. -/
@[simp]
theorem alphaBar_zero (β : ℕ → ℝ) : alphaBar β 0 = 1 := by
  simp [alphaBar]

/-- Each step multiplies the cumulative signal level by the signal level `1 - β (t + 1)`. -/
theorem alphaBar_succ (β : ℕ → ℝ) (t : ℕ) :
    alphaBar β (t + 1) = alphaBar β t * (1 - β (t + 1)) := by
  rw [alphaBar, prod_Icc_succ_top (by lia), ← alphaBar]

/-- For noise levels at most `1` the cumulative signal level is nonnegative. -/
theorem alphaBar_nonneg (hβ : ∀ s, 1 ≤ s → β s ≤ 1) (t : ℕ) : 0 ≤ alphaBar β t :=
  prod_nonneg fun s hs ↦ sub_nonneg.2 (hβ s (mem_Icc.1 hs).1)

/-- For noise levels below `1` the cumulative signal level is positive. -/
theorem alphaBar_pos (hβ : ∀ s, 1 ≤ s → β s < 1) (t : ℕ) : 0 < alphaBar β t :=
  prod_pos fun s hs ↦ sub_pos.2 (hβ s (mem_Icc.1 hs).1)

/-- For noise levels in `[0, 1]` the cumulative signal level is at most `1`. -/
theorem alphaBar_le_one (hβ : ∀ s, 1 ≤ s → 0 ≤ β s ∧ β s ≤ 1) (t : ℕ) : alphaBar β t ≤ 1 :=
  prod_le_one₀ (fun s hs ↦ sub_nonneg.2 (hβ s (mem_Icc.1 hs).1).2)
    fun s hs ↦ sub_le_self _ (hβ s (mem_Icc.1 hs).1).1

/-- For a schedule with noise levels in `[0, 1]` the cumulative signal level decreases. -/
theorem alphaBar_antitone (hβ : ∀ s, 1 ≤ s → 0 ≤ β s ∧ β s ≤ 1) : Antitone (alphaBar β) :=
  antitone_nat_of_succ_le fun t ↦ by
    rw [alphaBar_succ]
    exact mul_le_of_le_one_right (alphaBar_nonneg (fun s hs ↦ (hβ s hs).2) t)
      (sub_le_self _ (hβ (t + 1) (by lia)).1)

/-- For noise levels in `[0, 1]`, a step `t ≥ 1` with positive noise level brings the cumulative
signal level below `1`. -/
theorem alphaBar_lt_one (hβ : ∀ s, 1 ≤ s → 0 ≤ β s ∧ β s ≤ 1) {t : ℕ} (ht : 1 ≤ t)
    (hβt : 0 < β t) : alphaBar β t < 1 := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le' ht
  rw [alphaBar_succ]
  have h₁ := alphaBar_le_one hβ t
  have hb := (hβ (t + 1) (by lia)).2
  nlinarith

end AlphaBar

/-! ### Paths and the forward chain -/

/-- Evaluation at time `i ≤ n` of a path indexed by the times `Finset.Iic n`. -/
def pathEval {α : Type*} {n : ℕ} (i : ℕ) (hi : i ≤ n) (x : Iic n → α) : α :=
  x ⟨i, mem_Iic.2 hi⟩

/-- Unfolding lemma for `pathEval`. -/
@[simp]
theorem pathEval_apply {α : Type*} {n : ℕ} (i : ℕ) (hi : i ≤ n) (x : Iic n → α) :
    pathEval i hi x = x ⟨i, mem_Iic.2 hi⟩ := (rfl)

/-- Evaluation of a path at a fixed time is measurable. -/
@[fun_prop]
theorem measurable_pathEval {α : Type*} [MeasurableSpace α] {n : ℕ} (i : ℕ) (hi : i ≤ n) :
    Measurable (pathEval (α := α) i hi) :=
  measurable_pi_apply _

variable {ι : Type*} [Fintype ι]

/-- The step kernel of the forward chain from time `n` to time `n + 1`: it noises the state at
time `n` with signal level `1 - β (n + 1)`. -/
noncomputable def forwardStep (β : ℕ → ℝ) (n : ℕ) :
    Kernel (Iic n → EuclideanSpace ℝ ι) (EuclideanSpace ℝ ι) :=
  (noiseKernel (1 - β (n + 1))).comap (pathEval n le_rfl) (measurable_pathEval n le_rfl)

/-- Unfolding lemma for `forwardStep`. -/
theorem forwardStep_def (β : ℕ → ℝ) (n : ℕ) :
    forwardStep (ι := ι) β n =
      (noiseKernel (1 - β (n + 1))).comap (pathEval n le_rfl) (measurable_pathEval n le_rfl) :=
  (rfl)

/-- The forward step at a path noises the state at its last time. -/
@[simp]
theorem forwardStep_apply (β : ℕ → ℝ) (n : ℕ) (x : Iic n → EuclideanSpace ℝ ι) :
    forwardStep β n x = noiseKernel (1 - β (n + 1)) (pathEval n le_rfl x) :=
  (rfl)

instance (β : ℕ → ℝ) (n : ℕ) : IsMarkovKernel (forwardStep (ι := ι) β n) := by
  rw [forwardStep_def]
  infer_instance

/-- The law of the forward chain on paths up to time `T`, started from the law `μ₀`: the initial
state is drawn from `μ₀`, and the state at time `n + 1` from `noiseKernel (1 - β (n + 1))` at the
state at time `n`. -/
noncomputable def forwardPath (μ₀ : Measure (EuclideanSpace ℝ ι)) (β : ℕ → ℝ) (T : ℕ) :
    Measure (Iic T → EuclideanSpace ℝ ι) :=
  Kernel.partialTraj (X := fun _ ↦ EuclideanSpace ℝ ι) (forwardStep β) 0 T ∘ₘ
    μ₀.map (fun x (_ : Iic 0) ↦ x)

/-- Unfolding lemma for `forwardPath`. -/
theorem forwardPath_def (μ₀ : Measure (EuclideanSpace ℝ ι)) (β : ℕ → ℝ) (T : ℕ) :
    forwardPath μ₀ β T =
      Kernel.partialTraj (X := fun _ ↦ EuclideanSpace ℝ ι) (forwardStep β) 0 T ∘ₘ
        μ₀.map (fun x (_ : Iic 0) ↦ x) :=
  (rfl)

instance (μ₀ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ₀] (β : ℕ → ℝ) (T : ℕ) :
    IsProbabilityMeasure (forwardPath μ₀ β T) := by
  rw [forwardPath_def]
  infer_instance

/-- The law `noiseKernel (alphaBar β t) ∘ₘ μ₀` of the state at time `t` of the forward chain
started from `μ₀` (`forwardPath_map_eval`). -/
noncomputable def forwardMarginal (μ₀ : Measure (EuclideanSpace ℝ ι)) (β : ℕ → ℝ) (t : ℕ) :
    Measure (EuclideanSpace ℝ ι) :=
  noiseKernel (alphaBar β t) ∘ₘ μ₀

/-- Unfolding lemma for `forwardMarginal`. -/
theorem forwardMarginal_def (μ₀ : Measure (EuclideanSpace ℝ ι)) (β : ℕ → ℝ) (t : ℕ) :
    forwardMarginal μ₀ β t = noiseKernel (alphaBar β t) ∘ₘ μ₀ :=
  (rfl)

instance (μ₀ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ₀] (β : ℕ → ℝ) (t : ℕ) :
    IsProbabilityMeasure (forwardMarginal μ₀ β t) := by
  rw [forwardMarginal_def]
  infer_instance

/-- At time `0` the forward chain has not moved. -/
@[simp]
theorem forwardMarginal_zero (μ₀ : Measure (EuclideanSpace ℝ ι)) (β : ℕ → ℝ) :
    forwardMarginal μ₀ β 0 = μ₀ := by
  rw [forwardMarginal_def, alphaBar_zero, noiseKernel_one, Measure.id_comp]

/-- The forward recursion for the marginals of the forward chain: the law at time `t + 1` is the
law at time `t` noised with signal level `1 - β (t + 1)`. -/
theorem forwardMarginal_succ (μ₀ : Measure (EuclideanSpace ℝ ι)) {β : ℕ → ℝ}
    (hβ : ∀ s, 1 ≤ s → 0 ≤ β s ∧ β s ≤ 1) (t : ℕ) :
    forwardMarginal μ₀ β (t + 1) = noiseKernel (1 - β (t + 1)) ∘ₘ forwardMarginal μ₀ β t := by
  have hb := hβ (t + 1) (by lia)
  rw [forwardMarginal_def, forwardMarginal_def, Measure.comp_assoc,
    noiseKernel_comp (alphaBar_le_one hβ t) (sub_nonneg.2 hb.2) (sub_le_self _ hb.1),
    alphaBar_succ]

/-- The standard Gaussian law is stationary for the forward chain. -/
theorem forwardMarginal_stdGaussian {β : ℕ → ℝ} (hβ : ∀ s, 1 ≤ s → 0 ≤ β s ∧ β s ≤ 1) (t : ℕ) :
    forwardMarginal (stdGaussian (EuclideanSpace ℝ ι)) β t = stdGaussian (EuclideanSpace ℝ ι) :=
  stdGaussian_bind_noiseKernel (alphaBar_nonneg (fun s hs ↦ (hβ s hs).2) t)
    (alphaBar_le_one hβ t)

/-! ### Marginals of the path law -/

/-- The state at time `t ≤ T` of a trajectory up to time `T` only depends on the trajectory up to
time `t`. -/
private theorem partialTraj_forwardStep_map_eval_of_le (β : ℕ → ℝ) {T t : ℕ} (ht : t ≤ T) :
    (Kernel.partialTraj (X := fun _ ↦ EuclideanSpace ℝ ι) (forwardStep β) 0 T).map
        (pathEval t ht) =
      (Kernel.partialTraj (X := fun _ ↦ EuclideanSpace ℝ ι) (forwardStep β) 0 t).map
        (pathEval t le_rfl) := by
  rw [← Kernel.partialTraj_map_frestrictLe₂ 0 ht]
  -- `pathEval t ht` is `pathEval t le_rfl ∘ frestrictLe₂ ht` by unfolding both sides.
  exact Kernel.map_comp_right _
    (Preorder.measurable_frestrictLe₂ (X := fun _ ↦ EuclideanSpace ℝ ι) ht)
    (measurable_pathEval (α := EuclideanSpace ℝ ι) t le_rfl)

/-- A path started at `y` keeps `y 0` as its initial state. -/
private theorem partialTraj_forwardStep_map_eval_zero (β : ℕ → ℝ) (T : ℕ) :
    (Kernel.partialTraj (X := fun _ ↦ EuclideanSpace ℝ ι) (forwardStep β) 0 T).map
        (pathEval 0 (Nat.zero_le T)) =
      Kernel.deterministic (pathEval 0 le_rfl) (measurable_pathEval 0 le_rfl) := by
  rw [partialTraj_forwardStep_map_eval_of_le, Kernel.partialTraj_self, Kernel.id_map]

/-- Started at a path `y` of length one, the forward chain is at time `t` distributed as
`noiseKernel (alphaBar β t) (y 0)`. -/
private theorem partialTraj_forwardStep_map_eval {β : ℕ → ℝ}
    (hβ : ∀ s, 1 ≤ s → 0 ≤ β s ∧ β s ≤ 1) {T t : ℕ} (ht : t ≤ T) :
    (Kernel.partialTraj (X := fun _ ↦ EuclideanSpace ℝ ι) (forwardStep β) 0 T).map
        (pathEval t ht) =
      (noiseKernel (alphaBar β t)).comap (pathEval 0 le_rfl) (measurable_pathEval 0 le_rfl) := by
  rw [partialTraj_forwardStep_map_eval_of_le]
  clear ht T
  induction t with
  | zero =>
    rw [Kernel.partialTraj_self, Kernel.id_map, alphaBar_zero, noiseKernel_one, Kernel.id_comap]
  | succ t ih =>
    have hb := hβ (t + 1) (by lia)
    -- Mathlib's `map_partialTraj_succ_self`, with its evaluation map written as `pathEval`.
    have hstep : (Kernel.partialTraj (X := fun _ ↦ EuclideanSpace ℝ ι) (forwardStep β) t
        (t + 1)).map (pathEval (t + 1) le_rfl) = forwardStep β t :=
      Kernel.map_partialTraj_succ_self t
    -- One more step composes the last noising kernel with the `t`-step kernel.
    rw [Kernel.partialTraj_succ_eq_comp (Nat.zero_le t), Kernel.map_comp, hstep, forwardStep_def,
      ← Kernel.comp_map _ _ (by fun_prop), ih,
      ← Kernel.comp_deterministic_eq_comap, ← Kernel.comp_deterministic_eq_comap,
      ← Kernel.comp_assoc,
      noiseKernel_comp (alphaBar_le_one hβ t) (sub_nonneg.2 hb.2) (sub_le_self _ hb.1),
      alphaBar_succ]

/-- Pushing the forward path law along `f` integrates the pushed-forward trajectory kernel,
started at the constant path, against `μ₀`. -/
private theorem forwardPath_map_eq_bind (μ₀ : Measure (EuclideanSpace ℝ ι)) (β : ℕ → ℝ) (T : ℕ)
    {γ : Type*} [MeasurableSpace γ] {f : (Iic T → EuclideanSpace ℝ ι) → γ} (hf : Measurable f)
    (κ : Kernel (EuclideanSpace ℝ ι) γ)
    (hκ : (Kernel.partialTraj (X := fun _ ↦ EuclideanSpace ℝ ι) (forwardStep β) 0 T).map f =
      κ.comap (pathEval 0 le_rfl) (measurable_pathEval 0 le_rfl)) :
    (forwardPath μ₀ β T).map f = κ ∘ₘ μ₀ := by
  rw [forwardPath_def, Measure.map_comp _ _ hf, hκ, Kernel.coe_comap,
    Measure.bind_map (by fun_prop) (by fun_prop)]
  -- The constant path at `x` evaluates to `x` at time `0`, by unfolding `pathEval`.
  rfl

/-- For every sequence `β`, the forward path law starts from the initial law `μ₀`. -/
@[simp]
theorem forwardPath_map_eval_zero (μ₀ : Measure (EuclideanSpace ℝ ι)) (β : ℕ → ℝ) (T : ℕ) :
    (forwardPath μ₀ β T).map (pathEval 0 (Nat.zero_le T)) = μ₀ := by
  rw [forwardPath_map_eq_bind μ₀ β T (by fun_prop) Kernel.id
    (by rw [partialTraj_forwardStep_map_eval_zero, Kernel.id_comap]), Measure.id_comp]

/-- **The marginals of the forward chain.** For a noise schedule with levels in `[0, 1]`, the state
at time `t ≤ T` of the forward chain started from `μ₀` has law
`forwardMarginal μ₀ β t = noiseKernel (alphaBar β t) ∘ₘ μ₀`. -/
theorem forwardPath_map_eval (μ₀ : Measure (EuclideanSpace ℝ ι)) {β : ℕ → ℝ}
    (hβ : ∀ s, 1 ≤ s → 0 ≤ β s ∧ β s ≤ 1) {T t : ℕ} (ht : t ≤ T) :
    (forwardPath μ₀ β T).map (pathEval t ht) = forwardMarginal μ₀ β t :=
  forwardPath_map_eq_bind μ₀ β T (by fun_prop) _ (partialTraj_forwardStep_map_eval hβ ht)

/-- **The `t`-step transition of the forward chain.** For a noise schedule with levels in `[0, 1]`,
the joint law of the states at times `0` and `t ≤ T` of the forward chain started from `μ₀` is
`μ₀ ⊗ₘ noiseKernel (alphaBar β t)`: given the initial state `x₀`, the state at time `t` has law
`noiseKernel (alphaBar β t) x₀`. -/
theorem forwardPath_map_eval_zero_eval (μ₀ : Measure (EuclideanSpace ℝ ι)) [SFinite μ₀]
    {β : ℕ → ℝ} (hβ : ∀ s, 1 ≤ s → 0 ≤ β s ∧ β s ≤ 1) {T t : ℕ} (ht : t ≤ T) :
    (forwardPath μ₀ β T).map (fun x ↦ (pathEval 0 (Nat.zero_le T) x, pathEval t ht x)) =
      μ₀ ⊗ₘ noiseKernel (alphaBar β t) := by
  rw [Measure.compProd_eq_comp_prod]
  refine forwardPath_map_eq_bind μ₀ β T (by fun_prop) _ ?_
  ext1 y
  set P := Kernel.partialTraj (X := fun _ ↦ EuclideanSpace ℝ ι) (forwardStep β) 0 T y with hP
  -- Under `P` the initial state is almost surely `y 0`.
  have h0 : P.map (pathEval 0 (Nat.zero_le T)) = Measure.dirac (pathEval 0 le_rfl y) := by
    rw [hP, ← Kernel.map_apply _ (by fun_prop), partialTraj_forwardStep_map_eval_zero,
      Kernel.deterministic_apply]
  have hae : ∀ᵐ x ∂P, pathEval 0 (Nat.zero_le T) x = pathEval 0 le_rfl y := by
    refine ae_of_ae_map (p := fun z ↦ z = pathEval 0 le_rfl y)
      (measurable_pathEval (α := EuclideanSpace ℝ ι) 0 (Nat.zero_le T)).aemeasurable ?_
    rw [h0, ae_dirac_eq]
    exact Filter.eventually_pure.2 rfl
  have ht' : P.map (pathEval t ht) = noiseKernel (alphaBar β t) (pathEval 0 le_rfl y) := by
    rw [hP, ← Kernel.map_apply _ (by fun_prop), partialTraj_forwardStep_map_eval hβ ht,
      Kernel.comap_apply]
  rw [Kernel.map_apply _ (by fun_prop), Kernel.comap_apply, Kernel.prod_apply, Kernel.id_apply,
    Measure.dirac_prod, ← ht', Measure.map_map (by fun_prop) (by fun_prop)]
  exact Measure.map_congr (hae.mono fun x hx ↦ by simp only [Function.comp_apply, hx])

end TauCeti.Probability
