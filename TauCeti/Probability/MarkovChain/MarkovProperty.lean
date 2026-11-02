/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Process.MarkovChain
public import TauCeti.Probability.Process.PathLaw.ProcessShift
public import TauCeti.Probability.Process.PathLaw.Filtration

/-!
# The Markov property of a homogeneous chain at a fixed time

Let `X` be the coordinate process on path space `ℕ → α` under the path law
`markovChainLaw ν κ`, and write `ℙₓ = markovChainLaw (dirac x) κ` for the law of the chain started
at `x`. The *Markov property at time `n`* says that, conditionally on the history `X 0, …, X n`,
the future path `(X (n + k))ₖ = (shift α)^[n] X` is a chain with law `ℙ_{X n}`.

This file proves it in the following forms.

* As a joint law (`MeasureTheory.Measure.markovChainLaw_map_prefix_shift_iterate_eq_compProd`):
  the pair formed by the prefix `(X 0, …, X n)` and the future path has law
  `prefixLaw ⊗ₘ (u ↦ ℙ_{u n})`. This is the strongest form, and the one transported to processes
  on arbitrary probability spaces (`ProbabilityTheory.HasLaw.prefix_processShift_markovChainLaw`).
* As an identity of conditional expectations with respect to the natural filtration
  `MeasureTheory.Filtration.piLE` of path space: for an integrable test function `f`,
  `𝔼[f ∘ (shift α)^[n] | X 0, …, X n] = ∫ f dℙ_{X n}` almost surely
  (`MeasureTheory.Measure.condExp_shift_iterate_markovChainLaw`), and for an event `B` of path
  space, `ℙ[(shift α)^[n] X ∈ B | X 0, …, X n] = ℙ_{X n}(B)` almost surely
  (`MeasureTheory.Measure.condExp_indicator_shift_iterate_markovChainLaw`).
* Without conditioning, the future path is again a chain, started from the time-`n` law:
  `(markovChainLaw ν κ).map (shift α)^[n] = markovChainLaw ((κ ^ n) ∘ₘ ν) κ`
  (`MeasureTheory.Measure.markovChainLaw_map_shift_iterate`). On an event `{(X 0, …, X n) ∈ A}` of
  the history, the future path has the law of the chain started from the law of `X n` restricted
  to that event (`MeasureTheory.Measure.markovChainLaw_restrict_map_shift_iterate`).

The proof restricts the path law to an event of the history and identifies the law of the future
path on it by the uniqueness theorem `MeasureTheory.Measure.eq_markovChainLaw`: the prefix
recursion of the future follows from the one-step Markov property
`markovChainLaw_map_prefix_succ_eq_compProd` at the later times `n + m`.

## References

* J. R. Norris, *Markov Chains*, Cambridge University Press, 1997, Theorem 1.1.2.
* Olav Kallenberg, *Foundations of Modern Probability*, 2nd edition, Springer, 2002, Proposition
  8.2.
-/

public section

open MeasureTheory ProbabilityTheory

namespace TauCeti.Probability

variable {α : Type*} [MeasurableSpace α] (ν : Measure α) (κ : Kernel α α) [IsMarkovKernel κ]

/-- **The future path on an event of the history.** Restricted to an event `{(X 0, …, X n) ∈ A}`,
the law of the future path `(shift α)^[n] X` is the path law of the chain whose initial measure is
the law of `X n` restricted to the same event. -/
theorem _root_.MeasureTheory.Measure.markovChainLaw_restrict_map_shift_iterate [IsFiniteMeasure ν]
    (n : ℕ) {A : Set (Fin (n + 1) → α)} (hA : MeasurableSet A) :
    ((markovChainLaw ν κ).restrict ((fun x (i : Fin (n + 1)) => x i.1) ⁻¹' A)).map
        (shift α)^[n] =
      markovChainLaw (((markovChainLaw ν κ).restrict
        ((fun x (i : Fin (n + 1)) => x i.1) ⁻¹' A)).map fun x => x n) κ := by
  set P := markovChainLaw ν κ
  set H := (fun (x : ℕ → α) (i : Fin (n + 1)) => x i.1) ⁻¹' A
  refine Measure.eq_markovChainLaw _ κ ?_ fun m => ?_
  · rw [Measure.map_map (measurable_pi_apply 0) (measurable_shift_iterate n)]
    congr 1
    funext x
    simp
  -- The prefix recursion of the future path at step `m` is the Markov property of the chain at
  -- time `n + m`, restricted to the event `H` and read off the coordinates `n, …, n + m`.
  let π : (Fin (n + m + 1) → α) → (Fin (n + 1) → α) := fun w i => w (Fin.castLE (by omega) i)
  let ρ : (Fin (n + m + 1) → α) → (Fin (m + 1) → α) := fun w i => w ⟨i + n, by omega⟩
  have hπ : Measurable π := by fun_prop
  have hρ : Measurable ρ := by fun_prop
  have hπA : MeasurableSet (π ⁻¹' A) := hA.preimage hπ
  have hpre : Measurable fun x : ℕ → α => fun i : Fin (n + m + 1) => x i.1 := by fun_prop
  have hpair : Measurable fun x : ℕ → α => ((fun i : Fin (n + m + 1) => x i.1), x (n + m + 1)) :=
    by fun_prop
  have hH : H = (fun x : ℕ → α => fun i : Fin (n + m + 1) => x i.1) ⁻¹' (π ⁻¹' A) := by
    ext x; simp [H, π]
  have hκ : κ.comap (fun w : Fin (n + m + 1) → α => w (Fin.last (n + m)))
        (measurable_pi_apply _) =
      (κ.comap (fun v : Fin (m + 1) → α => v (Fin.last m)) (measurable_pi_apply _)).comap ρ hρ := by
    ext1 w
    simp only [Kernel.comap_apply, ρ]
    congr 2
    ext
    simp [Nat.add_comm]
  have hL : (P.restrict H).map (fun x => ((fun i : Fin (m + 1) => (shift α)^[n] x i.1),
        (shift α)^[n] x (m + 1))) =
      ((P.map fun x => ((fun i : Fin (n + m + 1) => x i.1), x (n + m + 1))).restrict
        ((π ⁻¹' A) ×ˢ Set.univ)).map (Prod.map ρ id) := by
    rw [Measure.restrict_map hpair (hπA.prod .univ), Measure.map_map (by fun_prop) hpair]
    have hfib : (fun x : ℕ → α => ((fun i : Fin (n + m + 1) => x i.1), x (n + m + 1))) ⁻¹'
        ((π ⁻¹' A) ×ˢ Set.univ) = H := by
      rw [hH]; ext x; simp
    rw [hfib]
    congr 1
    funext x
    simp only [Function.comp_apply, Prod.map_apply, id_eq, shift_iterate_apply, ρ]
    congr 2
    omega
  have hR : (P.restrict H).map (fun x (i : Fin (m + 1)) => (shift α)^[n] x i.1) =
      ((P.map fun x (i : Fin (n + m + 1)) => x i.1).restrict (π ⁻¹' A)).map ρ := by
    rw [Measure.restrict_map hpre hπA, Measure.map_map hρ hpre, ← hH]
    congr 1
    funext x i
    simp [ρ]
  rw [Measure.map_map (by fun_prop) (measurable_shift_iterate n),
    Measure.map_map (by fun_prop) (measurable_shift_iterate n)]
  simp only [Function.comp_def]
  rw [hL, hR, markovChainLaw_map_prefix_succ_eq_compProd, ← Measure.compProd_restrict_left _ _ hπA,
    hκ, Measure.map_prodMap_compProd_comap]

/-- **The future path is a chain started from the time-`n` law.** For a finite initial measure,
the path `(X (n + k))ₖ` seen from time `n` has law `markovChainLaw ((κ ^ n) ∘ₘ ν) κ`. -/
theorem _root_.MeasureTheory.Measure.markovChainLaw_map_shift_iterate [IsFiniteMeasure ν]
    (n : ℕ) :
    (markovChainLaw ν κ).map (shift α)^[n] = markovChainLaw ((κ ^ n : Kernel α α) ∘ₘ ν) κ := by
  simpa [Measure.markovChainLaw_map_eval] using
    Measure.markovChainLaw_restrict_map_shift_iterate ν κ n MeasurableSet.univ

/-- **The Markov property at time `n`, as a joint law.** Under `markovChainLaw ν κ`, the prefix
`(X 0, …, X n)` and the future path `(X (n + k))ₖ` have joint law the prefix law composed with the
kernel `u ↦ ℙ_{u n}` sending a prefix to the law of the chain started at its last state. -/
theorem _root_.MeasureTheory.Measure.markovChainLaw_map_prefix_shift_iterate_eq_compProd
    [IsFiniteMeasure ν] (n : ℕ) :
    (markovChainLaw ν κ).map (fun x => ((fun i : Fin (n + 1) => x i.1), (shift α)^[n] x)) =
      ((markovChainLaw ν κ).map fun x (i : Fin (n + 1)) => x i.1) ⊗ₘ
        κ.markovChainKernel.comap (fun w : Fin (n + 1) → α => w (Fin.last n))
          (measurable_pi_apply _) := by
  refine Measure.ext_prod fun {A B} hA hB => ?_
  have hpre : Measurable fun x : ℕ → α => fun i : Fin (n + 1) => x i.1 := by fun_prop
  have hfib : (fun x => ((fun i : Fin (n + 1) => x i.1), (shift α)^[n] x)) ⁻¹' (A ×ˢ B) =
      (shift α)^[n] ⁻¹' B ∩ (fun x (i : Fin (n + 1)) => x i.1) ⁻¹' A := by
    ext x; simp [and_comm]
  rw [Measure.map_apply (hpre.prodMk (measurable_shift_iterate n)) (hA.prod hB),
    Measure.compProd_apply_prod hA hB, setLIntegral_map hA (Kernel.measurable_coe _ hB) hpre, hfib,
    ← Measure.restrict_apply (hB.preimage (measurable_shift_iterate n)),
    ← Measure.map_apply (measurable_shift_iterate n) hB,
    Measure.markovChainLaw_restrict_map_shift_iterate ν κ n hA, Measure.markovChainLaw_eq_comp,
    Measure.bind_apply hB (Kernel.aemeasurable _),
    lintegral_map (Kernel.measurable_coe _ hB) (measurable_pi_apply n)]
  simp [Kernel.comap_apply]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **The Markov property at time `n`, for test functions.** For a finite initial measure and a
function `f` of paths that is integrable for the law `markovChainLaw ((κ ^ n) ∘ₘ ν) κ` of the future
path, the conditional expectation of `f ((shift α)^[n] X)` given the history `X 0, …, X n` is
`∫ f dℙ_{X n}`. -/
theorem _root_.MeasureTheory.Measure.condExp_shift_iterate_markovChainLaw [IsFiniteMeasure ν]
    (n : ℕ) {f : (ℕ → α) → E} (hf : Integrable f (markovChainLaw ((κ ^ n : Kernel α α) ∘ₘ ν) κ)) :
    (markovChainLaw ν κ)[fun x => f ((shift α)^[n] x) | Filtration.piLE n] =ᵐ[markovChainLaw ν κ]
      fun x => ∫ y, f y ∂markovChainLaw (Measure.dirac (x n)) κ := by
  set P := markovChainLaw ν κ
  set K := κ.markovChainKernel.comap (fun w : Fin (n + 1) → α => w (Fin.last n))
    (measurable_pi_apply _)
  have hpre : Measurable fun x : ℕ → α => fun i : Fin (n + 1) => x i.1 := by fun_prop
  have hF : Measurable fun x : ℕ → α => ((fun i : Fin (n + 1) => x i.1), (shift α)^[n] x) :=
    hpre.prodMk (measurable_shift_iterate n)
  have hjoint := Measure.markovChainLaw_map_prefix_shift_iterate_eq_compProd ν κ n
  -- The future path has law `K ∘ₘ (law of the history)`, the second marginal of the joint law.
  have hshift : P.map (shift α)^[n] = markovChainLaw ((κ ^ n : Kernel α α) ∘ₘ ν) κ :=
    Measure.markovChainLaw_map_shift_iterate ν κ n
  have hcomp : K ∘ₘ (P.map fun x (i : Fin (n + 1)) => x i.1) =
      markovChainLaw ((κ ^ n : Kernel α α) ∘ₘ ν) κ := by
    rw [← Measure.snd_compProd, ← hjoint,
      Measure.snd_map_prodMk hpre (measurable_shift_iterate n), hshift]
  have hfP : Integrable (fun x => f ((shift α)^[n] x)) P := by
    rw [← hshift] at hf
    exact (integrable_map_measure hf.1 (measurable_shift_iterate n).aemeasurable).1 hf
  have hfF : Integrable (fun p : (Fin (n + 1) → α) × (ℕ → α) => f p.2)
      ((P.map fun x (i : Fin (n + 1)) => x i.1) ⊗ₘ K) := by
    rw [Measure.integrable_compProd_snd_iff (hcomp ▸ hf.1), hcomp]
    exact hf
  have hg : Integrable (fun u => ∫ y, f y ∂K u) (P.map fun x (i : Fin (n + 1)) => x i.1) :=
    hfF.integral_compProd
  have hgP : Integrable (fun x : ℕ → α => ∫ y, f y ∂K (fun i : Fin (n + 1) => x i.1)) P :=
    (integrable_map_measure hg.1 hpre.aemeasurable).1 hg
  have hKx : ∀ x : ℕ → α,
      K (fun i : Fin (n + 1) => x i.1) = markovChainLaw (Measure.dirac (x n)) κ :=
    fun x => by simp [K, Kernel.comap_apply]
  simp_rw [← hKx]
  refine (ae_eq_condExp_of_forall_setIntegral_eq (Filtration.le _ n) hfP
    (fun s _ _ => hgP.integrableOn) ?_ ?_).symm <;> rw [Filtration.piLE_eq_comap_prefix]
  · rintro - ⟨A, hA, rfl⟩ -
    have hfib : (fun x => ((fun i : Fin (n + 1) => x i.1), (shift α)^[n] x)) ⁻¹'
        (A ×ˢ Set.univ) = (fun x (i : Fin (n + 1)) => x i.1) ⁻¹' A := by
      ext x; simp
    have hfFm : AEStronglyMeasurable (fun p : (Fin (n + 1) → α) × (ℕ → α) => f p.2)
        (P.map fun x => ((fun i : Fin (n + 1) => x i.1), (shift α)^[n] x)) := by
      rw [hjoint]; exact hfF.1
    rw [← setIntegral_map hA hg.1 hpre.aemeasurable, ← hfib,
      ← setIntegral_map (hA.prod .univ) hfFm hF.aemeasurable, hjoint,
      Measure.setIntegral_compProd hA .univ hfF.integrableOn]
    simp
  · exact hg.1.comp_ae_measurable' hpre.aemeasurable

/-- **The Markov property at time `n`, for events.** For a finite initial measure and a measurable
set `B` of paths, the conditional probability that the future path `(X (n + k))ₖ` lies in `B` given
the history `X 0, …, X n` is `ℙ_{X n}(B)`. -/
theorem _root_.MeasureTheory.Measure.condExp_indicator_shift_iterate_markovChainLaw
    [IsFiniteMeasure ν] (n : ℕ) {B : Set (ℕ → α)} (hB : MeasurableSet B) :
    (markovChainLaw ν κ)[((shift α)^[n] ⁻¹' B).indicator 1 | Filtration.piLE n]
      =ᵐ[markovChainLaw ν κ] fun x => (markovChainLaw (Measure.dirac (x n)) κ).real B := by
  have : IsFiniteMeasure (markovChainLaw ((κ ^ n : Kernel α α) ∘ₘ ν) κ) := by
    rw [← Measure.markovChainLaw_map_shift_iterate]; infer_instance
  have h := Measure.condExp_shift_iterate_markovChainLaw ν κ n
    (f := B.indicator (1 : (ℕ → α) → ℝ)) ((integrable_const (1 : ℝ)).indicator hB)
  simp_rw [integral_indicator_one hB] at h
  exact h

section Process

variable {ν κ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → α}

/-- **The Markov property at time `n` for a process with the law of a chain.** If the path of `X`
has law `markovChainLaw ν κ`, then the history `(X 0, …, X n)` and the future path
`processShift X n` have joint law `prefixLaw μ X (n + 1) ⊗ₘ (u ↦ ℙ_{u n})`. -/
theorem _root_.ProbabilityTheory.HasLaw.prefix_processShift_markovChainLaw [IsFiniteMeasure ν]
    (h : HasLaw (fun ω n => X n ω) (markovChainLaw ν κ) μ) (n : ℕ) :
    HasLaw (fun ω => ((fun i : Fin (n + 1) => X i ω), processShift X n ω))
      (prefixLaw μ X (n + 1) ⊗ₘ κ.markovChainKernel.comap
        (fun w : Fin (n + 1) → α => w (Fin.last n)) (measurable_pi_apply _)) μ := by
  have hpre : prefixLaw μ X (n + 1) =
      (markovChainLaw ν κ).map fun x (i : Fin (n + 1)) => x i.1 := by
    rw [← map_prefixProj_pathLaw μ h.aemeasurable, pathLaw_def, h.map_eq]
    -- `prefixProj α (n + 1)` is by definition the prefix map `fun x i => x i.1`.
    rfl
  have hF : (fun ω => ((fun i : Fin (n + 1) => X i ω), processShift X n ω)) =
      (fun x : ℕ → α => ((fun i : Fin (n + 1) => x i.1), (shift α)^[n] x)) ∘
        fun ω n => X n ω := by
    rw [processShift_eq_shift_iterate]
    -- Both sides are the same function, the right one written as a composite.
    rfl
  rw [hpre, ← Measure.markovChainLaw_map_prefix_shift_iterate_eq_compProd, hF]
  exact (hasLaw_map ((by fun_prop : Measurable fun x : ℕ → α => fun i : Fin (n + 1) => x i.1).prodMk
    (measurable_shift_iterate n)).aemeasurable).comp h

end Process

end TauCeti.Probability
