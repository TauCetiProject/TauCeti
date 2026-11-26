/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.MarkovChain.MarkovProperty

/-!
# Finite-time cylinder probabilities of a homogeneous chain

The path law `markovChainLaw ν κ` is characterized by its consecutive prefix laws. This file
computes its laws at arbitrary finite sets of times `t 0 ≤ t 1 ≤ … ≤ t k`, which need not be
consecutive: between two observed times, the chain moves by the kernel power `κ ^ d` over the
gap `d`.

The input is the `k`-step Markov property of `TauCeti.Probability.MarkovChain.MarkovProperty`:
`MeasureTheory.Measure.markovChainLaw_map_prefix_eval_add_eq_compProd` (the joint law of the prefix
`(X 0, …, X n)` and of `X (n + k)`) and its event form
`MeasureTheory.Measure.markovChainLaw_inter_preimage_eval_add`. Taking for the history event a
cylinder `{X (t 0) ∈ A 0, …, X (t j) ∈ A j}` with `t j ≤ n` and measurable sets `A i` reduces each
cylinder probability to an integral over a cylinder with one fewer time. This file proves:

* `MeasureTheory.Measure.markovChainLaw_map_pair_add`: the pair `(X n, X (n + k))` has law
  `((κ ^ n) ∘ₘ ν) ⊗ₘ κ ^ k`.
* `MeasureTheory.Measure.markovChainLaw_map_comp_init_last_eq_compProd`: for nondecreasing times
  `t : Fin (k + 2) → ℕ`, the law of `(X (t 0), …, X (t (k + 1)))` is obtained from the law of its
  first `k + 1` coordinates by one `κ ^ (t (k + 1) - t k)`-step out of the last one. Together with
  the time-`n` marginals this determines every finite-dimensional law of the chain.
* `MeasureTheory.Measure.markovChainLaw_setOf_forall_apply_eq`: with measurable singletons, the
  product formula

  ```text
  ℙ(X (t 0) = w 0, …, X (t k) = w k)
    = ((κ ^ t 0) ∘ₘ ν) {w 0} * ∏ i, (κ ^ (t (i + 1) - t i)) (w i) {w (i + 1)},
  ```

  for every initial measure `ν`.

The forms for a process on an arbitrary measure space whose path has law `markovChainLaw ν κ` are
`ProbabilityTheory.HasLaw.pair_add_markovChainLaw` and
`ProbabilityTheory.HasLaw.measure_setOf_forall_eq_markovChainLaw`.

## References

* J. R. Norris, *Markov Chains*, Cambridge University Press, 1997, §1.1, Theorem 1.1.3, for
  multi-step transition probabilities and the finite-dimensional distributions of a chain.
-/

public section

open MeasureTheory ProbabilityTheory

namespace TauCeti.Probability

variable {α : Type*} [MeasurableSpace α] (ν : Measure α) (κ : Kernel α α) [IsMarkovKernel κ]

/-- **The `k`-step transition law of the chain.** The joint law of the states at times `n` and
`n + k` is the time-`n` law extended by the `k`-step kernel `κ ^ k`. -/
theorem _root_.MeasureTheory.Measure.markovChainLaw_map_pair_add [SFinite ν] (n k : ℕ) :
    (markovChainLaw ν κ).map (fun x => (x n, x (n + k))) =
      ((κ ^ n : Kernel α α) ∘ₘ ν) ⊗ₘ (κ ^ k : Kernel α α) := by
  have hlast : Measurable fun w : Fin (n + 1) → α => w (Fin.last n) :=
    measurable_pi_apply (Fin.last n)
  have hprod : Measurable
      fun x : ℕ → α => ((fun i : Fin (n + 1) => x i.val), x (n + k)) := by fun_prop
  calc (markovChainLaw ν κ).map (fun x => (x n, x (n + k)))
      = ((markovChainLaw ν κ).map
          fun x => ((fun i : Fin (n + 1) => x i.val), x (n + k))).map
          (Prod.map (fun w : Fin (n + 1) → α => w (Fin.last n)) id) := by
        rw [Measure.map_map (hlast.prodMap measurable_id) hprod]
        -- Both maps send `x` to `(x n, x (n + k))`, the right one written as a composite.
        rfl
    _ = ((markovChainLaw ν κ).map fun x (i : Fin (n + 1)) => x i.val).map
          (fun w : Fin (n + 1) → α => w (Fin.last n)) ⊗ₘ (κ ^ k : Kernel α α) := by
        rw [Measure.markovChainLaw_map_prefix_eval_add_eq_compProd,
          Measure.map_prodMap_compProd_comap _ _ hlast]
    _ = _ := by
        rw [Measure.map_map hlast (by fun_prop), ← Measure.markovChainLaw_map_eval]
        -- The last coordinate of the prefix `(x 0, …, x n)` is `x n`.
        rfl

/-- **The finite-dimensional laws of the chain at arbitrary times.** For nondecreasing times
`t 0 ≤ … ≤ t (k + 1)`, the joint law of `(X (t 0), …, X (t k))` and of `X (t (k + 1))` is the law
of the first `k + 1` observations extended by the kernel `κ ^ (t (k + 1) - t k)` of the last gap,
out of the last of them. With `MeasureTheory.Measure.markovChainLaw_map_eval` for the first
observation, this recursion determines the law of the chain at every finite set of times. -/
theorem _root_.MeasureTheory.Measure.markovChainLaw_map_comp_init_last_eq_compProd [SFinite ν]
    {k : ℕ} {t : Fin (k + 2) → ℕ} (ht : Monotone t) :
    (markovChainLaw ν κ).map
        (fun x => ((fun i : Fin (k + 1) => x (t i.castSucc)), x (t (Fin.last (k + 1))))) =
      ((markovChainLaw ν κ).map fun x (i : Fin (k + 1)) => x (t i.castSucc)) ⊗ₘ
        (κ ^ (t (Fin.last (k + 1)) - t (Fin.last k).castSucc)).comap
          (fun w : Fin (k + 1) → α => w (Fin.last k)) (measurable_pi_apply _) := by
  set n := t (Fin.last k).castSucc
  set d := t (Fin.last (k + 1)) - n
  have hle : ∀ i : Fin (k + 1), t i.castSucc < n + 1 := fun i =>
    Nat.lt_succ_of_le (ht (Fin.castSucc_le_castSucc_iff.2 (Fin.le_last i)))
  have hnd : n + d = t (Fin.last (k + 1)) :=
    Nat.add_sub_cancel' (ht (Fin.le_last _))
  -- Subsample the prefix `(X 0, …, X n)` at the first `k + 1` observation times.
  let f : (Fin (n + 1) → α) → (Fin (k + 1) → α) := fun w i => w ⟨t i.castSucc, hle i⟩
  have hf : Measurable f := by fun_prop
  have hpre : Measurable fun x : ℕ → α => fun i : Fin (n + 1) => x i.val := by fun_prop
  have hkern : (κ ^ d).comap (fun w : Fin (n + 1) → α => w (Fin.last n)) (measurable_pi_apply _) =
      ((κ ^ d).comap (fun w : Fin (k + 1) → α => w (Fin.last k)) (measurable_pi_apply _)).comap
        f hf := by
    ext w s _
    simp only [Kernel.comap_apply, f]
    -- `Fin.last n` is `⟨t (Fin.last k).castSucc, _⟩` by definition of `n`.
    rfl
  have hobs : (fun x : ℕ → α => ((fun i : Fin (k + 1) => x (t i.castSucc)),
      x (t (Fin.last (k + 1))))) =
      Prod.map f id ∘ fun x => ((fun i : Fin (n + 1) => x i.val), x (n + d)) := by
    funext x
    simp only [Function.comp_apply, Prod.map, f, hnd, id]
  rw [hobs, ← Measure.map_map (hf.prodMap measurable_id) (hpre.prodMk (measurable_pi_apply _)),
    Measure.markovChainLaw_map_prefix_eval_add_eq_compProd, hkern,
    Measure.map_prodMap_compProd_comap _ _ hf, Measure.map_map hf hpre]
  -- Subsampling the prefix at the observation times reads off `x (t i)` for `i ≤ k`.
  rfl

/-- The cylinder product formula for an s-finite initial measure. -/
private theorem markovChainLaw_setOf_forall_apply_eq_of_sFinite [SFinite ν]
    [MeasurableSingletonClass α] (k : ℕ) {t : Fin (k + 1) → ℕ} (ht : Monotone t)
    (w : Fin (k + 1) → α) :
    markovChainLaw ν κ {x | ∀ i, x (t i) = w i} =
      ((κ ^ t 0 : Kernel α α) ∘ₘ ν) {w 0} *
        ∏ i : Fin k, (κ ^ (t i.succ - t i.castSucc)) (w i.castSucc) {w i.succ} := by
  induction k with
  | zero =>
    have hset : {x : ℕ → α | ∀ i : Fin 1, x (t i) = w i} = {x | x (t 0) = w 0} := by
      ext x
      simp [Fin.forall_fin_one]
    rw [hset, Measure.markovChainLaw_setOf_apply_eq_comp]
    simp
  | succ k ih =>
    set n := t (Fin.last k).castSucc
    have hle : ∀ i : Fin (k + 1), t i.castSucc ≤ n := fun i =>
      ht (Fin.castSucc_le_castSucc_iff.2 (Fin.le_last i))
    have hnd : n + (t (Fin.last (k + 1)) - n) = t (Fin.last (k + 1)) :=
      Nat.add_sub_cancel' (ht (Fin.le_last _))
    set B := {x : ℕ → α | ∀ i : Fin (k + 1), x (t i.castSucc) = w i.castSucc}
    -- The first `k + 1` observations form an event of the history through time `n`.
    have hB : MeasurableSet[Filtration.piLE n] B := by
      rw [Filtration.piLE_eq_comap_prefix]
      refine ⟨⋂ i : Fin (k + 1), (fun u : Fin (n + 1) → α =>
        u ⟨t i.castSucc, Nat.lt_succ_of_le (hle i)⟩) ⁻¹' {w i.castSucc},
        MeasurableSet.iInter fun i => measurable_pi_apply _ (measurableSet_singleton _), ?_⟩
      ext x
      simp [B]
    have hset : {x : ℕ → α | ∀ i, x (t i) = w i} =
        B ∩ (fun x => x (n + (t (Fin.last (k + 1)) - n))) ⁻¹' {w (Fin.last (k + 1))} := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
        hnd, B]
      exact ⟨fun h => ⟨fun i => h _, h _⟩, fun h i => Fin.lastCases h.2 h.1 i⟩
    -- The induction hypothesis computes the mass of `B`, the cylinder at the first `k + 1` times.
    have hB' := ih (ht.comp Fin.strictMono_castSucc.monotone) (w ∘ Fin.castSucc)
    simp only [Function.comp_apply] at hB'
    -- On `B` the integrand is the constant transition weight out of `w k`.
    rw [hset, Measure.markovChainLaw_inter_preimage_eval_add ν κ n _ hB
        (measurableSet_singleton _),
      setLIntegral_congr_fun (Filtration.piLE.le n _ hB) (fun x hx => by rw [hx (Fin.last k)]),
      setLIntegral_const, hB', Fin.prod_univ_castSucc]
    simp only [Fin.castSucc_zero, Fin.succ_last, Fin.succ_castSucc, n]
    ring

/-- **Cylinder probabilities of the chain.** On a state space with measurable singletons, for
nondecreasing times `t 0 ≤ … ≤ t k`, the probability that the chain visits `w 0, …, w k` at those
times is the time-`t 0` weight of `w 0` times the product of the multi-step transition weights
over the gaps. This holds for every initial measure `ν`. -/
theorem _root_.MeasureTheory.Measure.markovChainLaw_setOf_forall_apply_eq
    [MeasurableSingletonClass α] (k : ℕ) {t : Fin (k + 1) → ℕ} (ht : Monotone t)
    (w : Fin (k + 1) → α) :
    markovChainLaw ν κ {x | ∀ i, x (t i) = w i} =
      ((κ ^ t 0 : Kernel α α) ∘ₘ ν) {w 0} *
        ∏ i : Fin k, (κ ^ (t i.succ - t i.castSucc)) (w i.castSucc) {w i.succ} := by
  have hS : MeasurableSet {x : ℕ → α | ∀ i, x (t i) = w i} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun i => measurable_pi_apply _ (measurableSet_singleton _)
  -- Integrate the formula for the chains started at fixed states against `ν`.
  rw [Measure.markovChainLaw_eq_comp, Measure.bind_apply hS (Kernel.aemeasurable _),
    Measure.bind_apply (measurableSet_singleton _) (Kernel.aemeasurable _),
    ← lintegral_mul_const _ (Kernel.measurable_coe _ (measurableSet_singleton _))]
  refine lintegral_congr fun x => ?_
  rw [Kernel.markovChainKernel_apply, markovChainLaw_setOf_forall_apply_eq_of_sFinite _ κ k ht w,
    Measure.dirac_bind (Kernel.measurable _)]

section Process

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → α}

/-- **The `k`-step transition law of a Markov chain.** If the path of `X` has law
`markovChainLaw ν κ`, then the pair `(X n, X (n + k))` has law `((κ ^ n) ∘ₘ ν) ⊗ₘ κ ^ k`. -/
theorem _root_.ProbabilityTheory.HasLaw.pair_add_markovChainLaw [SFinite ν]
    (h : HasLaw (fun ω n => X n ω) (markovChainLaw ν κ) μ) (n k : ℕ) :
    HasLaw (fun ω => (X n ω, X (n + k) ω))
      (((κ ^ n : Kernel α α) ∘ₘ ν) ⊗ₘ (κ ^ k : Kernel α α)) μ := by
  rw [← Measure.markovChainLaw_map_pair_add]
  exact (hasLaw_map
    ((measurable_pi_apply n).prodMk (measurable_pi_apply (n + k))).aemeasurable).comp h

/-- **Cylinder probabilities of a Markov chain.** If the path of `X` has law
`markovChainLaw ν κ` on a state space with measurable singletons, then for nondecreasing times
`t 0 ≤ … ≤ t k` the probability that `X` visits `w 0, …, w k` at those times is given by the
product formula of `MeasureTheory.Measure.markovChainLaw_setOf_forall_apply_eq`. -/
theorem _root_.ProbabilityTheory.HasLaw.measure_setOf_forall_eq_markovChainLaw
    [MeasurableSingletonClass α] (h : HasLaw (fun ω n => X n ω) (markovChainLaw ν κ) μ) (k : ℕ)
    {t : Fin (k + 1) → ℕ} (ht : Monotone t) (w : Fin (k + 1) → α) :
    μ {ω | ∀ i, X (t i) ω = w i} =
      ((κ ^ t 0 : Kernel α α) ∘ₘ ν) {w 0} *
        ∏ i : Fin k, (κ ^ (t i.succ - t i.castSucc)) (w i.castSucc) {w i.succ} := by
  have hS : MeasurableSet {x : ℕ → α | ∀ i, x (t i) = w i} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun i => measurable_pi_apply _ (measurableSet_singleton _)
  rw [← Measure.markovChainLaw_setOf_forall_apply_eq ν κ k ht w, ← h.map_eq,
    Measure.map_apply₀ h.aemeasurable hS.nullMeasurableSet]
  -- The preimage of the path cylinder under the path map is the cylinder event of `X`.
  rfl

end Process

end TauCeti.Probability
