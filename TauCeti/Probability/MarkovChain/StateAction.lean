/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Process.MarkovChain
public import TauCeti.Probability.Kernel.Composition.MeasureCompProd

/-!
# The state process of a chain driven by a stationary randomized control

Let `τ : Kernel (α × β) α` give the law of the next state from a state and an action, and let
`ρ : Kernel α β` choose an action at random from the current state. Alternating the two gives a
Markov chain on state-action pairs: from `(s, a)` the next state `s'` is drawn from `τ (s, a)`,
and then the next action from `ρ s'`. Its transition kernel is `τ ⊗ₖ ρ.comap Prod.snd _`.

The states alone form a Markov chain, whose kernel `(ρ ⊗ₖ τ).snd` averages `τ (s, ·)` over the
actions drawn from `ρ s`. This is not an instance of the lumping criterion
`MeasureTheory.Measure.markovChainLaw_map_comp`: the law of the next state depends on the current
action and not only on the current state. The point is that, given the states up to time `n`,
the action at time `n` is drawn from `ρ` at the state at time `n`, once the earlier actions are
integrated out.

This is how a stationary randomized policy of a Markov decision process turns its trajectory law
into a Markov chain on the states.

## Main statements

* `MeasureTheory.Measure.markovChainLaw_compProd_map_prefix` — given the states up to time `n`,
  the action at time `n` has law `ρ` at the state at time `n`.
* `MeasureTheory.Measure.markovChainLaw_compProd_map_fst` — the states form the Markov chain of
  `(ρ ⊗ₖ τ).snd`, started from the initial law of the states.
* `MeasureTheory.Measure.markovChainLaw_compProd_map_eval` — the state-action pair at time `n`
  has law `(((ρ ⊗ₖ τ).snd ^ n) ∘ₘ ν) ⊗ₘ ρ`.

## References

* M. L. Puterman, *Markov decision processes: discrete stochastic dynamic programming*, Wiley
  (1994), §2.1.6 and §5.3.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti.Probability

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  (ν : Measure α) (τ : Kernel (α × β) α) (ρ : Kernel α β) [IsMarkovKernel τ] [IsMarkovKernel ρ]

/-- The law of the chain of state-action pairs that draws the next state from `τ` and then the
next action from `ρ` at that state, started from `ν ⊗ₘ ρ`. -/
private abbrev stateActionLaw : Measure (ℕ → α × β) :=
  markovChainLaw (ν ⊗ₘ ρ) (τ ⊗ₖ ρ.comap Prod.snd measurable_snd)

/-- Under `stateActionLaw`, given the states up to time `n`, the action at time `n` has law `ρ` at
the state at time `n`: the induction hypothesis of `markovChainLaw_compProd_map_prefix`. -/
private def ActionGivenStates (n : ℕ) : Prop :=
  (stateActionLaw ν τ ρ).map (fun x ↦ ((fun i : Fin (n + 1) ↦ (x i).1), (x n).2)) =
    ((stateActionLaw ν τ ρ).map fun x (i : Fin (n + 1)) ↦ (x i).1) ⊗ₘ
      ρ.comap (fun w : Fin (n + 1) → α ↦ w (Fin.last n)) (measurable_pi_apply _)

/-- If, given the states up to time `n`, the action at time `n` has law `ρ` at the state at time
`n`, then forgetting the actions in the one-step extension of the state-action prefix by `τ`
leaves the state prefix extended by `(ρ ⊗ₖ τ).snd`. -/
private theorem map_prefix_fst_succ (n : ℕ) (hA : ActionGivenStates ν τ ρ n) :
    (((stateActionLaw ν τ ρ).map fun x (i : Fin (n + 1)) ↦ x i) ⊗ₘ
        τ.comap (fun z : Fin (n + 1) → α × β ↦ z (Fin.last n)) (measurable_pi_apply _)).map
        (Prod.map (fun z i ↦ (z i).1) id) =
      ((stateActionLaw ν τ ρ).map fun x (i : Fin (n + 1)) ↦ (x i).1) ⊗ₘ
        (ρ ⊗ₖ τ).snd.comap (fun w : Fin (n + 1) → α ↦ w (Fin.last n)) (measurable_pi_apply _) := by
  unfold ActionGivenStates stateActionLaw at *
  set μ := markovChainLaw (ν ⊗ₘ ρ) (τ ⊗ₖ ρ.comap Prod.snd measurable_snd)
  have hlast : Measurable fun w : Fin (n + 1) → α ↦ w (Fin.last n) := measurable_pi_apply _
  have hF : Measurable fun (z : Fin (n + 1) → α × β) (i : Fin (n + 1)) ↦ (z i).1 := by fun_prop
  have hg : Measurable fun z : Fin (n + 1) → α × β ↦ (z (Fin.last n)).2 := by fun_prop
  -- The kernel `τ` at the last pair only sees the last state and the last action.
  have hτ : τ.comap (fun z : Fin (n + 1) → α × β ↦ z (Fin.last n)) (measurable_pi_apply _) =
      (τ.comap (Prod.map (fun w : Fin (n + 1) → α ↦ w (Fin.last n)) id)
        (hlast.prodMap measurable_id)).comap
        (fun z ↦ ((fun i ↦ (z i).1), (z (Fin.last n)).2)) (hF.prodMk hg) := by
    ext z : 1
    simp [Kernel.comap_apply]
  have hprefix : (μ.map fun x (i : Fin (n + 1)) ↦ x i).map
      (fun z ↦ ((fun i ↦ (z i).1), (z (Fin.last n)).2)) =
        μ.map (fun x ↦ ((fun i : Fin (n + 1) ↦ (x i).1), (x n).2)) := by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    simp only [Function.comp_def, Fin.val_last]
  have hprefixF : (μ.map fun x (i : Fin (n + 1)) ↦ x i).map
      (fun (z : Fin (n + 1) → α × β) (i : Fin (n + 1)) ↦ (z i).1) =
        μ.map fun x (i : Fin (n + 1)) ↦ (x i).1 := by
    rw [Measure.map_map hF (by fun_prop)]
    rfl
  rw [hτ, Measure.map_prodMap_compProd_comap_prodMk _ hF hg
    (ρ.comap (fun w : Fin (n + 1) → α ↦ w (Fin.last n)) hlast) _ (by rw [hprefix, hprefixF, hA]),
    hprefixF, ← Kernel.comap_compProd, Kernel.snd_comap]

/-- The law of the states up to time `n + 1` is the law of the states up to time `n` and the state
at time `n + 1`, read as one prefix. -/
private theorem map_prefix_fst_snoc (μ : Measure (ℕ → α × β)) (n : ℕ) :
    (μ.map fun x ↦ ((fun i : Fin (n + 1) ↦ (x i).1), (x (n + 1)).1)).map
        (fun p ↦ (Fin.snoc p.1 p.2 : Fin (n + 2) → α)) =
      μ.map fun x (i : Fin (n + 2)) ↦ (x i).1 := by
  rw [Measure.map_map (MeasureTheory.measurable_finSnoc (n + 1)) (by fun_prop)]
  congr 1
  funext x
  exact (congrFun (prefix_succ_eq_finSnoc_comp (n + 1)) fun k ↦ (x k).1).symm

/-- If, given the states up to time `n`, the action at time `n` has law `ρ` at the state at time
`n`, then, given the same states, the state at time `n + 1` has law `(ρ ⊗ₖ τ).snd` at the state
at time `n`. -/
private theorem map_prefix_fst_succ_eq_compProd (n : ℕ) (hA : ActionGivenStates ν τ ρ n) :
    (stateActionLaw ν τ ρ).map (fun x ↦ ((fun i : Fin (n + 1) ↦ (x i).1), (x (n + 1)).1)) =
      ((stateActionLaw ν τ ρ).map fun x (i : Fin (n + 1)) ↦ (x i).1) ⊗ₘ
        (ρ ⊗ₖ τ).snd.comap (fun w : Fin (n + 1) → α ↦ w (Fin.last n)) (measurable_pi_apply _) := by
  unfold stateActionLaw
  set μ := markovChainLaw (ν ⊗ₘ ρ) (τ ⊗ₖ ρ.comap Prod.snd measurable_snd)
  have hlast : Measurable fun z : Fin (n + 1) → α × β ↦ z (Fin.last n) := measurable_pi_apply _
  calc μ.map (fun x ↦ ((fun i : Fin (n + 1) ↦ (x i).1), (x (n + 1)).1))
      = ((μ.map fun x ↦ ((fun i : Fin (n + 1) ↦ x i), x (n + 1))).map
          (Prod.map id Prod.fst)).map (Prod.map (fun z i ↦ (z i).1) id) := by
        rw [Measure.map_map (by fun_prop) (by fun_prop),
          Measure.map_map (by fun_prop) (by fun_prop)]
        rfl
    _ = (((μ.map fun x (i : Fin (n + 1)) ↦ x i) ⊗ₘ
          τ.comap (fun z : Fin (n + 1) → α × β ↦ z (Fin.last n)) hlast).map
            (Prod.map (fun z i ↦ (z i).1) id)) := by
        rw [markovChainLaw_map_prefix_succ_eq_compProd,
          ← Measure.compProd_comap_map _ _ _ measurable_fst, ← Kernel.fst_eq,
          Kernel.fst_compProd]
    _ = _ := map_prefix_fst_succ ν τ ρ n hA

/-- The inductive step: if the action at time `n` has law `ρ` at the state at time `n` given the
states up to time `n`, then the same holds at time `n + 1`. -/
private theorem map_prefix_succ_eq_compProd (n : ℕ) (hA : ActionGivenStates ν τ ρ n) :
    ActionGivenStates ν τ ρ (n + 1) := by
  unfold ActionGivenStates stateActionLaw
  set μ := markovChainLaw (ν ⊗ₘ ρ) (τ ⊗ₖ ρ.comap Prod.snd measurable_snd)
  have hlast : Measurable fun z : Fin (n + 1) → α × β ↦ z (Fin.last n) := measurable_pi_apply _
  have hF : Measurable fun (z : Fin (n + 1) → α × β) (i : Fin (n + 1)) ↦ (z i).1 := by fun_prop
  have hsnoc := MeasureTheory.measurable_finSnoc (α := α) (n + 1)
  -- After the state at time `n + 1` is drawn, the action is drawn from `ρ` at that state.
  have hK : (τ ⊗ₖ ρ.comap Prod.snd measurable_snd).comap
      (fun z : Fin (n + 1) → α × β ↦ z (Fin.last n)) hlast =
        τ.comap (fun z : Fin (n + 1) → α × β ↦ z (Fin.last n)) hlast ⊗ₖ
          (ρ.comap (Prod.snd : (Fin (n + 1) → α) × α → α) measurable_snd).comap
            (Prod.map (fun z i ↦ (z i).1) id) (hF.prodMap measurable_id) := by
    rw [Kernel.comap_compProd, ← Kernel.comap_comp_right]
    -- Both pullbacks of `ρ` read the second component, `fun p ↦ p.2`.
    rfl
  have hρ : (ρ.comap (fun w : Fin (n + 2) → α ↦ w (Fin.last (n + 1))) (measurable_pi_apply _)).comap
      (fun p : (Fin (n + 1) → α) × α ↦ (Fin.snoc p.1 p.2 : Fin (n + 2) → α)) hsnoc =
        ρ.comap (Prod.snd : (Fin (n + 1) → α) × α → α) measurable_snd := by
    ext p : 1
    simp [Kernel.comap_apply]
  calc μ.map (fun x ↦ ((fun i : Fin (n + 2) ↦ (x i).1), (x (n + 1)).2))
      = (((μ.map fun x (i : Fin (n + 1)) ↦ x i) ⊗ₘ
          (τ ⊗ₖ ρ.comap Prod.snd measurable_snd).comap
            (fun z : Fin (n + 1) → α × β ↦ z (Fin.last n)) hlast).map
          (fun p ↦ (Fin.snoc (fun i ↦ (p.1 i).1) p.2.1, p.2.2))) := by
        rw [← markovChainLaw_map_prefix_succ_eq_compProd, Measure.map_map (by fun_prop)
          (by fun_prop)]
        congr 1
        funext x
        refine Prod.ext (funext fun i ↦ ?_) rfl
        refine Fin.lastCases ?_ (fun j ↦ ?_) i <;> simp
    _ = ((((μ.map fun x (i : Fin (n + 1)) ↦ x i) ⊗ₘ
          τ.comap (fun z : Fin (n + 1) → α × β ↦ z (Fin.last n)) hlast) ⊗ₘ
            (ρ.comap (Prod.snd : (Fin (n + 1) → α) × α → α) measurable_snd).comap
              (Prod.map (fun z i ↦ (z i).1) id) (hF.prodMap measurable_id)).map
          (Prod.map (Prod.map (fun z i ↦ (z i).1) id) id)).map
          (Prod.map (fun p ↦ (Fin.snoc p.1 p.2 : Fin (n + 2) → α)) id) := by
        rw [hK, ← Measure.compProd_assoc', Measure.map_map (by fun_prop) (by fun_prop),
          Measure.map_map (by fun_prop) (by fun_prop)]
        refine congrArg (fun h ↦ Measure.map h _) (funext fun ⟨⟨z, s⟩, a⟩ ↦ ?_)
        simp [MeasurableEquiv.prodAssoc]
    _ = ((μ.map fun x ↦ ((fun i : Fin (n + 1) ↦ (x i).1), (x (n + 1)).1)) ⊗ₘ
          ρ.comap (Prod.snd : (Fin (n + 1) → α) × α → α) measurable_snd).map
          (Prod.map (fun p ↦ (Fin.snoc p.1 p.2 : Fin (n + 2) → α)) id) := by
        rw [Measure.map_prodMap_compProd_comap _ _ (hF.prodMap measurable_id),
          map_prefix_fst_succ ν τ ρ n hA, map_prefix_fst_succ_eq_compProd ν τ ρ n hA]
    _ = _ := by
        rw [← hρ, Measure.map_prodMap_compProd_comap _ _ hsnoc, ← map_prefix_fst_snoc]

/-- The initial state-action pair has law `ν ⊗ₘ ρ`, so the initial action has law `ρ` at the
initial state. -/
private theorem map_prefix_zero_eq_compProd [SFinite ν] : ActionGivenStates ν τ ρ 0 := by
  unfold ActionGivenStates stateActionLaw
  set μ := markovChainLaw (ν ⊗ₘ ρ) (τ ⊗ₖ ρ.comap Prod.snd measurable_snd)
  have hc : Measurable fun (a : α) (_ : Fin 1) ↦ a := measurable_pi_iff.2 fun _ ↦ measurable_id
  have h₀ : μ.map (fun x ↦ x 0) = ν ⊗ₘ ρ := markovChainLaw_map_eval_zero _ _
  have hstates : μ.map (fun x (i : Fin 1) ↦ (x i).1) = ν.map fun (a : α) (_ : Fin 1) ↦ a := by
    rw [← Measure.fst_compProd ν ρ, ← h₀, Measure.fst, Measure.map_map measurable_fst
      (measurable_pi_apply 0), Measure.map_map hc (by fun_prop)]
    congr 1
    funext x i
    simp [Fin.fin_one_eq_zero i]
  have hρ : (ρ.comap (fun w : Fin 1 → α ↦ w (Fin.last 0)) (measurable_pi_apply _)).comap
      (fun (a : α) (_ : Fin 1) ↦ a) hc = ρ := by
    ext a : 1
    simp [Kernel.comap_apply]
  rw [hstates, ← Measure.map_prodMap_compProd_comap _ _ hc, hρ, ← h₀,
    Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext x
  refine Prod.ext (funext fun i ↦ ?_) rfl
  simp [Fin.fin_one_eq_zero i]

/-- **The action given the states.** Under the chain of state-action pairs that draws the next
state from `τ` and then the next action from `ρ` at that state, the joint law of the states up to
time `n` and of the action at time `n` is the law of the states extended by `ρ` at the state at
time `n`. That is, given the states up to time `n`, the action at time `n` has law `ρ` at the
current state, once the earlier actions are integrated out. -/
theorem _root_.MeasureTheory.Measure.markovChainLaw_compProd_map_prefix [SFinite ν]
    (n : ℕ) :
    (markovChainLaw (ν ⊗ₘ ρ) (τ ⊗ₖ ρ.comap Prod.snd measurable_snd)).map
        (fun x ↦ ((fun i : Fin (n + 1) ↦ (x i).1), (x n).2)) =
      ((markovChainLaw (ν ⊗ₘ ρ) (τ ⊗ₖ ρ.comap Prod.snd measurable_snd)).map
          fun x (i : Fin (n + 1)) ↦ (x i).1) ⊗ₘ
        ρ.comap (fun w : Fin (n + 1) → α ↦ w (Fin.last n)) (measurable_pi_apply _) := by
  induction n with
  | zero => exact map_prefix_zero_eq_compProd ν τ ρ
  | succ n ih => exact map_prefix_succ_eq_compProd ν τ ρ n ih

/-- **The states of a chain driven by a stationary randomized control form a Markov chain.**
Under the chain of state-action pairs that draws the next state from `τ` and then the next action
from `ρ` at that state, started from `ν ⊗ₘ ρ`, the states form the Markov chain of
`(ρ ⊗ₖ τ).snd` started from `ν`. Its transition from `s` draws an action from `ρ s` and then the
next state from `τ` at `s` and that action. -/
@[simp]
theorem _root_.MeasureTheory.Measure.markovChainLaw_compProd_map_fst [IsFiniteMeasure ν] :
    (markovChainLaw (ν ⊗ₘ ρ) (τ ⊗ₖ ρ.comap Prod.snd measurable_snd)).map
        (fun x n ↦ (x n).1) = markovChainLaw ν (ρ ⊗ₖ τ).snd := by
  refine Measure.eq_markovChainLaw ν _ ?_ fun n ↦ ?_
  · calc _ = ((markovChainLaw (ν ⊗ₘ ρ) (τ ⊗ₖ ρ.comap Prod.snd measurable_snd)).map
            fun x ↦ x 0).map Prod.fst := by
          rw [Measure.map_map measurable_fst (measurable_pi_apply 0),
            Measure.map_map (measurable_pi_apply 0) (by fun_prop)]
          rfl
      _ = ν := by
          rw [markovChainLaw_map_eval_zero]
          exact Measure.fst_compProd ν ρ
  · rw [Measure.map_map (by fun_prop) (by fun_prop), Measure.map_map (by fun_prop) (by fun_prop)]
    exact map_prefix_fst_succ_eq_compProd ν τ ρ n
      (Measure.markovChainLaw_compProd_map_prefix ν τ ρ n)

/-- **The state-action pair at time `n`.** Under the chain of state-action pairs that draws the
next state from `τ` and then the next action from `ρ` at that state, started from `ν ⊗ₘ ρ`, the
pair at time `n` has law `(((ρ ⊗ₖ τ).snd ^ n) ∘ₘ ν) ⊗ₘ ρ`: the state follows `n` steps of the
averaged kernel, and the action is drawn from `ρ` at that state. -/
theorem _root_.MeasureTheory.Measure.markovChainLaw_compProd_map_eval [IsFiniteMeasure ν]
    (n : ℕ) :
    (markovChainLaw (ν ⊗ₘ ρ) (τ ⊗ₖ ρ.comap Prod.snd measurable_snd)).map (fun x ↦ x n) =
      (((ρ ⊗ₖ τ).snd ^ n) ∘ₘ ν) ⊗ₘ ρ := by
  set μ := markovChainLaw (ν ⊗ₘ ρ) (τ ⊗ₖ ρ.comap Prod.snd measurable_snd)
  have hlast : Measurable fun w : Fin (n + 1) → α ↦ w (Fin.last n) := measurable_pi_apply _
  have hstate : (μ.map fun x (i : Fin (n + 1)) ↦ (x i).1).map (fun w ↦ w (Fin.last n)) =
      ((ρ ⊗ₖ τ).snd ^ n) ∘ₘ ν := by
    rw [← Measure.markovChainLaw_map_eval, ← Measure.markovChainLaw_compProd_map_fst,
      Measure.map_map hlast (by fun_prop), Measure.map_map (measurable_pi_apply n) (by fun_prop)]
    simp only [μ, Function.comp_def, Fin.val_last]
  calc μ.map (fun x ↦ x n)
      = (μ.map fun x ↦ ((fun i : Fin (n + 1) ↦ (x i).1), (x n).2)).map
          (Prod.map (fun w ↦ w (Fin.last n)) id) := by
        rw [Measure.map_map (by fun_prop) (by fun_prop)]
        simp only [Function.comp_def, Prod.map_apply, Fin.val_last, id_eq]
    _ = (((ρ ⊗ₖ τ).snd ^ n) ∘ₘ ν) ⊗ₘ ρ := by
        rw [Measure.markovChainLaw_compProd_map_prefix,
          Measure.map_prodMap_compProd_comap _ _ hlast, hstate]

end TauCeti.Probability
