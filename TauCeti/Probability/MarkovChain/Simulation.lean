/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Process.MarkovChain
public import TauCeti.Probability.Kernel.Randomization
public import Mathlib.Probability.Independence.InfinitePi

/-!
# Markov chains driven by independent noise

`randomizedChain g f u` starts at `g (u 0)` and updates its state using `f` and the next
noise coordinate. If the coordinates of `u` are independent with law `ρ`, `g` samples the
initial law, and `f x` samples the transition law from `x`, the whole path has law
`markovChainLaw`. The result applies on any probability space and to any measurable state
space admitting such samplers.

For nonempty standard Borel state spaces, Mathlib's kernel randomization theorem supplies
the samplers from uniform noise on the closed unit interval. Thus the existence result
includes finite and countably infinite state spaces, with no positivity requirement on
individual transition weights. The uniform representation is an existence result, with
no prescribed enumeration or inverse-cdf endpoint convention.

The proof uses the existing prefix-recursion uniqueness theorem for `markovChainLaw` and
`Kernel.map_prod_eq_compProd_of_map` for a single randomized transition.

## References

* J. R. Norris, *Markov Chains* (1997), §1.1, for constructing a chain from independent noise.
* O. Kallenberg, *Foundations of Modern Probability*, 3rd ed., Lemma 4.22, for the uniform
  representation of kernels, supplied by Mathlib.
-/

public section

open MeasureTheory ProbabilityTheory Function
open scoped unitInterval

namespace TauCeti.Probability

variable {α ξ Ω : Type*}

/-- The trajectory obtained by sampling the initial state from noise coordinate zero and
then applying `f` to the current state and each fresh noise coordinate. -/
def randomizedChain (g : ξ → α) (f : α → ξ → α) (u : ℕ → ξ) : ℕ → α
  | 0 => g (u 0)
  | n + 1 => f (randomizedChain g f u n) (u (n + 1))

/-- The initial state uses the zeroth noise coordinate. -/
@[simp]
theorem randomizedChain_zero (g : ξ → α) (f : α → ξ → α) (u : ℕ → ξ) :
    randomizedChain g f u 0 = g (u 0) := (rfl)

/-- Each transition uses the next noise coordinate. -/
@[simp]
theorem randomizedChain_succ (g : ξ → α) (f : α → ξ → α) (u : ℕ → ξ) (n : ℕ) :
    randomizedChain g f u (n + 1) = f (randomizedChain g f u n) (u (n + 1)) := (rfl)

/-- The state at time `n` depends only on noise coordinates through `n`. -/
theorem randomizedChain_congr (g : ξ → α) (f : α → ξ → α) {u v : ℕ → ξ} {n : ℕ}
    (h : ∀ i ≤ n, u i = v i) : randomizedChain g f u n = randomizedChain g f v n := by
  induction n with
  | zero => simp [h 0 le_rfl]
  | succ n ih =>
    simp only [randomizedChain_succ, h (n + 1) le_rfl,
      ih (fun i hi => h i (hi.trans (Nat.le_succ n)))]

variable [MeasurableSpace α] [MeasurableSpace ξ] [MeasurableSpace Ω]

/-- A measurable initial sampler and a jointly measurable update give a measurable path map. -/
@[fun_prop]
theorem measurable_randomizedChain {g : ξ → α} {f : α → ξ → α}
    (hg : Measurable g) (hf : Measurable (uncurry f)) : Measurable (randomizedChain g f) := by
  apply measurable_pi_iff.mpr
  intro n
  induction n with
  | zero => exact hg.comp (measurable_pi_apply 0)
  | succ n ih => exact hf.comp (ih.prodMk (measurable_pi_apply (n + 1)))

private theorem indepFun_randomizedChain_prefix {g : ξ → α} {f : α → ξ → α}
    (hg : Measurable g) (hf : Measurable (uncurry f)) {U : ℕ → Ω → ξ} {P : Measure Ω}
    (hU : ∀ i, Measurable (U i)) (hindep : iIndepFun U P) (n : ℕ) :
    IndepFun (fun ω (i : Fin (n + 1)) => randomizedChain g f (fun j => U j ω) i)
      (U (n + 1)) P := by
  -- Extend a finite noise prefix arbitrarily; causality makes its remaining coordinates irrelevant.
  let extend (v : Set.Iic n → ξ) (j : ℕ) : ξ :=
    if h : j ≤ n then v ⟨j, h⟩ else v ⟨0, Nat.zero_le n⟩
  have hext : Measurable extend := by
    apply measurable_pi_iff.mpr
    intro j
    by_cases h : j ≤ n <;> simp only [extend, h, ↓reduceDIte] <;> fun_prop
  let F (v : Set.Iic n → ξ) (i : Fin (n + 1)) := randomizedChain g f (extend v) i
  have hF : Measurable F := by
    exact measurable_pi_iff.mpr fun i =>
      ((measurable_pi_apply (i : ℕ)).comp (measurable_randomizedChain hg hf)).comp hext
  have h := hindep.indepFun_set (Set.Iic n) {n + 1}
    (by simp only [Set.disjoint_left, Set.mem_Iic, Set.mem_singleton_iff]; omega) hU
  have h' := h.comp hF (measurable_pi_apply ⟨n + 1, rfl⟩)
  convert h' using 1
  · funext ω i
    apply randomizedChain_congr
    intro j hj
    simp [extend, hj.trans (Nat.le_of_lt_succ i.isLt)]
  · rfl

/-- Independent noises with a common law, passed through initial and transition samplers,
produce the entire Markov-chain path law. The sample space need not be canonical. -/
theorem hasLaw_randomizedChain {g : ξ → α} {f : α → ξ → α}
    (hg : Measurable g) (hf : Measurable (uncurry f))
    {U : ℕ → Ω → ξ} {P : Measure Ω} (hU : ∀ i, Measurable (U i))
    (hindep : iIndepFun U P) {ρ : Measure ξ}
    (hlaw : ∀ i, HasLaw (U i) ρ P)
    (ν : Measure α) (κ : Kernel α α) [IsMarkovKernel κ]
    (hg_map : ρ.map g = ν) (hf_map : ∀ x, ρ.map (f x) = κ x) :
    HasLaw (fun ω => randomizedChain g f (fun i => U i ω)) (markovChainLaw ν κ) P := by
  have := hindep.isProbabilityMeasure
  have : IsProbabilityMeasure ρ := (hlaw 0).isProbabilityMeasure_iff.mp inferInstance
  have : IsProbabilityMeasure ν := hg_map ▸ inferInstanceAs (IsProbabilityMeasure (ρ.map g))
  let X (ω : Ω) := randomizedChain g f (fun i => U i ω)
  have hX : Measurable X := (measurable_randomizedChain hg hf).comp (by fun_prop)
  refine ⟨hX.aemeasurable, Measure.eq_markovChainLaw ν κ ?_ ?_⟩
  · rw [Measure.map_map (by fun_prop) hX]
    rw [← hg_map, ← (hlaw 0).map_eq, Measure.map_map hg (hU 0)]
    rfl
  · intro n
    let W (ω : Ω) (i : Fin (n + 1)) := X ω i
    have hW : Measurable W := by fun_prop
    let η := κ.comap (fun w : Fin (n + 1) → α => w (Fin.last n))
      (measurable_pi_apply (Fin.last n))
    let F (w : Fin (n + 1) → α) (u : ξ) := f (w (Fin.last n)) u
    have hF : Measurable (uncurry F) := by fun_prop
    have hstep := η.map_prod_eq_compProd_of_map (μ := P.map W) ρ F hF
      (fun w => hf_map (w (Fin.last n)))
    have hpair := (indepFun_randomizedChain_prefix hg hf hU hindep n).map_prod_eq_prod_map_map
      hW.aemeasurable (hU (n + 1)).aemeasurable
    rw [(hlaw (n + 1)).map_eq] at hpair
    calc
      _ = P.map (fun ω => (W ω, F (W ω) (U (n + 1) ω))) := by
        rw [Measure.map_map (by fun_prop) hX]
        rfl
      _ = ((P.map W).prod ρ).map (fun p => (p.1, F p.1 p.2)) := by
        rw [← hpair, Measure.map_map (by fun_prop) (hW.prodMk (hU (n + 1)))]
        rfl
      _ = (P.map W) ⊗ₘ η := hstep
      _ = _ := by
        rw [Measure.map_map (by fun_prop) hX]
        rfl

/-- Every Markov kernel on a nonempty standard Borel space admits jointly measurable uniform
samplers whose recursive simulation has its Markov-chain law, for every initial probability law. -/
theorem exists_uniform_randomizedChain [StandardBorelSpace α] [Nonempty α]
    (ν : Measure α) [IsProbabilityMeasure ν] (κ : Kernel α α) [IsMarkovKernel κ] :
    ∃ (g : unitInterval → α) (f : α → unitInterval → α),
      Measurable g ∧ Measurable (uncurry f) ∧
      (volume : Measure unitInterval).map g = ν ∧
      (∀ x, (volume : Measure unitInterval).map (f x) = κ x) ∧
      HasLaw (randomizedChain g f) (markovChainLaw ν κ)
        (Measure.infinitePi fun _ : ℕ => (volume : Measure unitInterval)) := by
  obtain ⟨g, hg, hg_map⟩ := ν.exists_measurable_map_eq
  obtain ⟨f, hf, hf_map⟩ := κ.exists_measurable_map_eq_unitInterval
  refine ⟨g, f, hg, hf, hg_map, hf_map, ?_⟩
  exact hasLaw_randomizedChain hg hf (fun i => measurable_pi_apply i)
    (iIndepFun_infinitePi (X := fun _ x => x) fun _ => measurable_id)
    (fun i => ⟨(measurable_pi_apply i).aemeasurable, Measure.infinitePi_map_eval _ i⟩)
    ν κ hg_map hf_map

end TauCeti.Probability
