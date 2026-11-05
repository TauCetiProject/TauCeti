/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Process.MarkovChain
public import TauCeti.Probability.Kernel.Randomization
public import TauCeti.MeasureTheory.Group.Convolution.Power
public import Mathlib.Probability.Independence.Basic

/-!
# Additive random walks as Markov chains

For an s-finite increment law `μ`, `Measure.additiveWalk μ` adds a fresh increment
with law `μ` to the current state.
Partial sums of independent increments with common law `μ` have the corresponding
Markov-chain path law, on any measurable sample space. No cancellation, topology,
or countability of the state space is needed.

This identifies the discrete skeleton of a counting process from its increment laws,
rather than merely identifying its separate one-time marginals.

See J. R. Norris, *Markov Chains*, Cambridge University Press (1997), §1.1, for
random walks viewed as homogeneous Markov chains.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MeasureTheory.Measure

variable {α : Type*} [MeasurableSpace α] [AddMonoid α] [MeasurableAdd₂ α]

/-- The transition kernel that adds an independent increment with s-finite law `μ`. -/
def additiveWalk (μ : Measure α) : Kernel α α :=
  (Kernel.id ×ₖ Kernel.const α μ).map (fun p => p.1 + p.2)

/-- The transition measure from `a` is the increment law translated by `a`. -/
@[simp] theorem additiveWalk_apply (μ : Measure α) [SFinite μ] (a : α) :
    additiveWalk μ a = μ.map (fun b => a + b) := by
  rw [additiveWalk, Kernel.map_apply _ (by fun_prop), Kernel.prod_apply, Kernel.id_apply,
    Kernel.const_apply,
    Measure.dirac_prod, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

instance (μ : Measure α) : IsSFiniteKernel (additiveWalk μ) := by
  unfold additiveWalk
  infer_instance

instance (μ : Measure α) [IsProbabilityMeasure μ] : IsMarkovKernel (additiveWalk μ) :=
  ⟨fun a => by rw [additiveWalk_apply]; infer_instance⟩

/-- Evaluating a random-walk transition is evaluating the increment law on a preimage. -/
theorem additiveWalk_apply' (μ : Measure α) [SFinite μ] (a : α) {s : Set α} (hs : MeasurableSet s) :
    additiveWalk μ a s = μ ((fun b => a + b) ⁻¹' s) := by
  rw [additiveWalk_apply, Measure.map_apply (by fun_prop) hs]

/-- The zero increment gives the identity transition. -/
@[simp] theorem additiveWalk_dirac_zero : additiveWalk (Measure.dirac (0 : α)) = Kernel.id := by
  ext a : 1
  simp [Kernel.id_apply, Measure.map_dirac' (by fun_prop : Measurable (fun b : α => a + b))]

/-- Integrating a test function against a random-walk step translates its argument. -/
theorem lintegral_additiveWalk (μ : Measure α) [SFinite μ] (a : α)
    {f : α → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ b, f b ∂additiveWalk μ a = ∫⁻ b, f (a + b) ∂μ := by
  rw [additiveWalk_apply, MeasureTheory.lintegral_map hf (by fun_prop)]

/-- Successive independent increments combine by convolution of their laws. -/
theorem additiveWalk_comp (μ ν : Measure α) [SFinite μ] [SFinite ν] :
    additiveWalk ν ∘ₖ additiveWalk μ = additiveWalk (μ ∗ ν) := by
  ext a : 1
  apply Measure.ext_of_lintegral
  intro f hf
  rw [Kernel.comp_apply, Measure.lintegral_bind (Kernel.aemeasurable _) hf.aemeasurable]
  simp_rw [lintegral_additiveWalk _ _ hf]
  rw [lintegral_additiveWalk μ a (by fun_prop), Measure.lintegral_conv (by fun_prop)]
  simp only [add_assoc]

/-- Kernel powers of a random walk use convolution powers of the increment law. -/
theorem additiveWalk_pow (μ : Measure α) [SFinite μ] (n : ℕ) :
    additiveWalk μ ^ n = additiveWalk (μ.convolutionPower n) := by
  induction n with
  | zero => rw [Measure.convolutionPower_zero, additiveWalk_dirac_zero]; rfl
  | succ n ih =>
    rw [Kernel.pow_add, pow_one, ih, additiveWalk_comp, Measure.convolutionPower_succ']

/-- A walk with natural-valued increments cannot decrease its state; its singleton
transition weights are shifted increment masses. -/
theorem additiveWalk_apply_singleton (μ : Measure ℕ) [SFinite μ] (i j : ℕ) :
    additiveWalk μ i {j} = if i ≤ j then μ {j - i} else 0 := by
  rw [additiveWalk_apply' _ _ (measurableSet_singleton _)]
  by_cases hij : i ≤ j
  · have hpre : (fun k : ℕ => i + k) ⁻¹' {j} = {j - i} := by
      ext k
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      omega
    simp [hpre, hij]
  · have hpre : (fun k : ℕ => i + k) ⁻¹' {j} = ∅ := by
      ext k
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false]
      exact iff_false_intro (fun h => hij (by omega))
    simp [hpre, hij]

end MeasureTheory.Measure

namespace TauCeti.Probability

variable {α Ω : Type*} [MeasurableSpace α] [AddCommMonoid α] [MeasurableAdd₂ α]
  [MeasurableSpace Ω] {P : Measure Ω} {U : ℕ → Ω → α} {μ : Measure α}
  [IsProbabilityMeasure μ]

/-- Partial sums of independent increments with common law `μ`, starting at `a`, have
Markov-chain path law with initial law `δ_a` and transition kernel `μ.additiveWalk`. -/
theorem hasLaw_markovChainLaw_partialSums (hU : ∀ n, Measurable (U n))
    (hindep : iIndepFun U P) (hlaw : ∀ n, HasLaw (U n) μ P) (a : α) :
    HasLaw (fun ω n => a + ∑ j ∈ Finset.range n, U j ω)
      (markovChainLaw (Measure.dirac a) μ.additiveWalk) P := by
  have := hindep.isProbabilityMeasure
  let X (ω : Ω) (n : ℕ) := a + ∑ j ∈ Finset.range n, U j ω
  have hX : Measurable X := by fun_prop
  refine ⟨hX.aemeasurable, Measure.eq_markovChainLaw _ _ ?_ ?_⟩
  · rw [Measure.map_map (by fun_prop) hX]
    simp [X, Function.comp_def]
  · intro n
    let W (ω : Ω) (i : Fin (n + 1)) := X ω i
    have hW : Measurable W := by fun_prop
    -- The entire state prefix is a measurable function of increments strictly before `n`.
    let F (v : Set.Iio n → α) (i : Fin (n + 1)) :=
      a + ∑ j : Fin i.val, v ⟨j.val, lt_of_lt_of_le j.isLt (Nat.le_of_lt_succ i.isLt)⟩
    have hF : Measurable F := by fun_prop
    have hprefix (ω : Ω) : F (fun j => U j ω) = W ω := by
      ext i
      dsimp only [F, W, X]
      rw [← Fin.sum_univ_eq_sum_range]
    have hdis : Disjoint (Set.Iio n) ({n} : Set ℕ) := by
      simp only [Set.disjoint_left, Set.mem_Iio, Set.mem_singleton_iff]
      omega
    have hi := (hindep.indepFun_set (Set.Iio n) {n} hdis hU).comp
      hF (measurable_pi_apply ⟨n, rfl⟩)
    have hi' : IndepFun W (U n) P := by
      simpa only [Function.comp_def, hprefix] using hi
    let η := μ.additiveWalk.comap
      (fun w : Fin (n + 1) → α => w (Fin.last n)) (measurable_pi_apply _)
    let step (w : Fin (n + 1) → α) (u : α) := w (Fin.last n) + u
    have hstep := η.map_prod_eq_compProd_of_map (μ := P.map W) μ step (by fun_prop)
      (fun w => by simp [η, step, Kernel.comap_apply])
    have hpair := hi'.map_prod_eq_prod_map_map hW.aemeasurable (hU n).aemeasurable
    rw [(hlaw n).map_eq] at hpair
    calc
      _ = P.map (fun ω => (W ω, step (W ω) (U n ω))) := by
        rw [Measure.map_map (by fun_prop) hX]
        congr 1
        funext ω
        simp [W, X, step, Finset.sum_range_succ, add_assoc]
      _ = ((P.map W).prod μ).map (fun p => (p.1, step p.1 p.2)) := by
        rw [← hpair, Measure.map_map (by fun_prop) (hW.prodMk (hU n))]
        rfl
      _ = (P.map W) ⊗ₘ η := hstep
      _ = _ := by
        rw [Measure.map_map (by fun_prop) hX]
        rfl

end TauCeti.Probability
