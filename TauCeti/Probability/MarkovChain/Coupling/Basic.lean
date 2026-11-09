/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.TotalVariation.Basic
public import TauCeti.MeasureTheory.OptimalTransport.Coupling
public import TauCeti.Probability.MarkovChain.MarkovProperty

/-!
# Markovian couplings and the meeting-time coupling inequality

A *Markovian coupling* of a transition kernel `κ` on `α` with itself is a transition kernel `η` on
`α × α` such that every `η (a, b)` is a coupling of `κ a` and `κ b`, in the sense of
`TauCeti.IsCoupling`. The independent product `κ ∥ₖ κ` is the basic example. Run the chain of `η`
from an initial coupling `ρ` of two laws `ν` and `ν'`, and write `ω n = (X n, Y n)` for its path.
Then `X` is a `κ`-chain started from `ν` and `Y` is a `κ`-chain started from `ν'`.

The *meeting-time coupling* follows `X` until the first time `X` and `Y` meet and follows `Y` from
then on: `spliceAtMeeting ω n` is `Y n` if `X k = Y k` for some `k ≤ n`, and `X n` otherwise. Since
both coordinates move according to `κ` and they agree at the switching time, the spliced path is
again a `κ`-chain started from `ν`. Comparing it with `Y` at time `n` gives the **coupling
inequality**

```text
tvDist ((κ ^ n) ∘ₘ ν) ((κ ^ n) ∘ₘ ν') ≤ 2 * ℙ(X k ≠ Y k for every k ≤ n).
```

The factor two comes from Mathlib's normalization of `MeasureTheory.tvDist`, under which the
distance between probability measures lies in `[0, 2]`. This inequality reduces convergence to
equilibrium to the almost sure meeting of two independent copies of the chain.

The coordinate laws are instances of a general fact
(`MeasureTheory.Measure.markovChainLaw_map_comp`): if the law of `f` under every transition `η s`
is `κ (f s)`, then the image of an `η`-chain under `f` is a `κ`-chain. No countability is
assumed on the state space; the meeting events only need a measurable diagonal
(`MeasurableEq α`).

## Main definitions

* `TauCeti.Probability.spliceAtMeeting ω`: the path following the first coordinate of `ω` until
  the coordinates first agree, and the second coordinate from then on.

## Main statements

* `MeasureTheory.Measure.markovChainLaw_map_fst_of_isCoupling`,
  `MeasureTheory.Measure.markovChainLaw_map_snd_of_isCoupling`: each coordinate of a Markovian
  coupling is a chain.
* `MeasureTheory.Measure.markovChainLaw_map_spliceAtMeeting`: the meeting-time coupling has the
  law of the first coordinate.
* `ProbabilityTheory.Kernel.tvDist_pow_comp_le_of_isCoupling`: the coupling inequality for a
  Markovian coupling.
* `ProbabilityTheory.Kernel.tvDist_pow_comp_le_parallelComp`: the coupling inequality for two
  independent copies of the chain.

## References

* J. R. Norris, *Markov Chains*, Cambridge University Press (1997), §1.8, proof of Theorem 1.8.3.
* T. Lindvall, *Lectures on the Coupling Method*, Wiley (1992), Chapter II.
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace TauCeti.Probability

variable {α : Type*}

/-- The *meeting-time splice* of a path `ω = (X, Y)` in `α × α`: at time `n` it is `Y n` if the
coordinates have met by time `n` (`X k = Y k` for some `k ≤ n`), and `X n` otherwise. Under a
Markovian coupling it is again a chain with the law of `X`
(`MeasureTheory.Measure.markovChainLaw_map_spliceAtMeeting`). -/
noncomputable def spliceAtMeeting (ω : ℕ → α × α) (n : ℕ) : α :=
  open Classical in if ∃ k ≤ n, (ω k).1 = (ω k).2 then (ω n).2 else (ω n).1

/-- Once the coordinates have met, the splice is the second coordinate. -/
@[simp]
theorem spliceAtMeeting_of_exists {ω : ℕ → α × α} {n : ℕ} (h : ∃ k ≤ n, (ω k).1 = (ω k).2) :
    spliceAtMeeting ω n = (ω n).2 := by
  simp [spliceAtMeeting, h]

/-- Before the coordinates meet, the splice is the first coordinate. -/
@[simp]
theorem spliceAtMeeting_of_forall_ne {ω : ℕ → α × α} {n : ℕ} (h : ∀ k ≤ n, (ω k).1 ≠ (ω k).2) :
    spliceAtMeeting ω n = (ω n).1 := by
  have : ¬∃ k ≤ n, (ω k).1 = (ω k).2 := by simpa using h
  simp [spliceAtMeeting, this]

/-- Before the coordinates have met by time `n`, the splice at `n + 1` is the first coordinate,
also when they meet at time `n + 1`. -/
@[simp]
theorem spliceAtMeeting_succ_of_forall_ne {ω : ℕ → α × α} {n : ℕ}
    (h : ∀ k ≤ n, (ω k).1 ≠ (ω k).2) : spliceAtMeeting ω (n + 1) = (ω (n + 1)).1 := by
  by_cases hm : (ω (n + 1)).1 = (ω (n + 1)).2
  · rw [spliceAtMeeting_of_exists ⟨n + 1, le_rfl, hm⟩, hm]
  · refine spliceAtMeeting_of_forall_ne fun k hk => ?_
    rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hk) with hk | rfl
    · exact h k (Nat.lt_succ_iff.1 hk)
    · exact hm

/-- At time zero the splice is the first coordinate, whether or not the coordinates agree. -/
@[simp]
theorem spliceAtMeeting_zero (ω : ℕ → α × α) : spliceAtMeeting ω 0 = (ω 0).1 := by
  by_cases h : (ω 0).1 = (ω 0).2
  · rw [spliceAtMeeting_of_exists ⟨0, le_rfl, h⟩, h]
  · exact spliceAtMeeting_of_forall_ne fun k hk => by rwa [Nat.le_zero.1 hk]

variable [MeasurableSpace α] [MeasurableEq α]

/-- Having met by time `n` is an event of the history up to time `n`. -/
theorem measurableSet_piLE_exists_le_fst_eq_snd (n : ℕ) :
    MeasurableSet[Filtration.piLE n] {ω : ℕ → α × α | ∃ k ≤ n, (ω k).1 = (ω k).2} := by
  have hset : {ω : ℕ → α × α | ∃ k ≤ n, (ω k).1 = (ω k).2} =
      ⋃ k ∈ Finset.Iic n, (fun ω : ℕ → α × α => ω k) ⁻¹' {p | p.1 = p.2} := by
    ext ω
    simp
  rw [hset]
  refine Finset.measurableSet_biUnion _ fun k hk => ?_
  exact (measurableSet_eq_fun measurable_fst measurable_snd).preimage
    ((Filtration.adapted_piLE k).mono (Filtration.piLE.mono (Finset.mem_Iic.1 hk)) le_rfl)

/-- The meeting-time splice is adapted to the natural filtration of path space. -/
theorem adapted_spliceAtMeeting :
    Adapted (Filtration.piLE (X := fun _ : ℕ => α × α)) fun n ω => spliceAtMeeting ω n := by
  intro n
  simp only [spliceAtMeeting]
  exact Measurable.ite (measurableSet_piLE_exists_le_fst_eq_snd n)
    (measurable_snd.comp (Filtration.adapted_piLE n))
    (measurable_fst.comp (Filtration.adapted_piLE n))

/-- The meeting-time splice is a measurable map of paths. -/
theorem measurable_spliceAtMeeting : Measurable (spliceAtMeeting (α := α)) :=
  measurable_pi_iff.2 fun n => (adapted_spliceAtMeeting n).mono (Filtration.le _ n) le_rfl

end TauCeti.Probability

namespace MeasureTheory.Measure

open TauCeti TauCeti.Probability

variable {α : Type*} [MeasurableSpace α] {β : Type*} [MeasurableSpace β]
  {κ : Kernel α α} {κ' : Kernel β β} {η : Kernel (α × β) (α × β)} [IsMarkovKernel η]

/-- **The first coordinate of a Markovian coupling is a chain.** If every transition `η p` couples
`κ p.1` and `κ' p.2`, the first coordinates of the chain of `η` form the chain of `κ` started from
the first marginal of the initial law. -/
theorem markovChainLaw_map_fst_of_isCoupling [IsMarkovKernel κ] (ρ : Measure (α × β))
    [IsFiniteMeasure ρ]
    (hη : ∀ p, IsCoupling (η p) (κ p.1) (κ' p.2)) :
    (markovChainLaw ρ η).map (fun ω n => (ω n).1) = markovChainLaw ρ.fst κ :=
  markovChainLaw_map_comp ρ η κ measurable_fst fun p => (hη p).fst_eq

/-- **The second coordinate of a Markovian coupling is a chain.** If every transition `η p` couples
`κ p.1` and `κ' p.2`, the second coordinates of the chain of `η` form the chain of `κ'` started
from the second marginal of the initial law. -/
theorem markovChainLaw_map_snd_of_isCoupling [IsMarkovKernel κ'] (ρ : Measure (α × β))
    [IsFiniteMeasure ρ]
    (hη : ∀ p, IsCoupling (η p) (κ p.1) (κ' p.2)) :
    (markovChainLaw ρ η).map (fun ω n => (ω n).2) = markovChainLaw ρ.snd κ' :=
  markovChainLaw_map_comp ρ η κ' measurable_snd fun p => (hη p).snd_eq

/-- **The meeting-time coupling.** Let every transition `η p` couple `κ p.1` and `κ p.2`. Under the
chain of `η` started from `ρ`, the path that follows the first coordinate until the coordinates
first meet and the second coordinate from then on is the chain of `κ` started from the first
marginal of `ρ`. -/
theorem markovChainLaw_map_spliceAtMeeting [MeasurableEq α] [IsMarkovKernel κ]
    (ρ : Measure (α × α))
    [IsFiniteMeasure ρ] {η : Kernel (α × α) (α × α)} [IsMarkovKernel η]
    (hη : ∀ p, IsCoupling (η p) (κ p.1) (κ p.2)) :
    (markovChainLaw ρ η).map spliceAtMeeting = markovChainLaw ρ.fst κ := by
  set P := markovChainLaw ρ η
  set Z : ℕ → (ℕ → α × α) → α := fun n ω => spliceAtMeeting ω n
  have hZ : ∀ n, Measurable (Z n) := fun n =>
    (adapted_spliceAtMeeting n).mono (Filtration.le _ n) le_rfl
  refine ((hasLaw_markovChainLaw_iff ρ.fst κ (X := Z) fun n => (hZ n).aemeasurable).2
    ⟨?_, fun n => ?_⟩).map_eq
  · have h0 : Z 0 = Prod.fst ∘ fun ω : ℕ → α × α => ω 0 := funext spliceAtMeeting_zero
    rw [h0, ← Measure.map_map measurable_fst (measurable_pi_apply 0),
      markovChainLaw_map_eval_zero, Measure.fst]
  refine Measure.ext_prod fun {A C} hA hC => ?_
  -- The history event `B = {(Z 0, …, Z n) ∈ A}` splits along the event `M` of having met by
  -- time `n`. On `M` the next step of the splice is the second coordinate, off `M` the first.
  set M := {ω : ℕ → α × α | ∃ k ≤ n, (ω k).1 = (ω k).2}
  set B := (fun ω (i : Fin (n + 1)) => Z i ω) ⁻¹' A
  have hpre : Measurable[Filtration.piLE n] fun ω (i : Fin (n + 1)) => Z i ω :=
    @Measurable.of_eval _ _ _ (Filtration.piLE n) _ _ fun i =>
      (adapted_spliceAtMeeting i.1).mono (Filtration.piLE.mono (Nat.lt_succ_iff.1 i.2)) le_rfl
  have hBn : MeasurableSet[Filtration.piLE n] B := hpre hA
  have hMn : MeasurableSet[Filtration.piLE n] M := measurableSet_piLE_exists_le_fst_eq_snd n
  have hB : MeasurableSet B := Filtration.le _ n _ hBn
  have hM : MeasurableSet M := Filtration.le _ n _ hMn
  have hfib : (fun ω => ((fun i : Fin (n + 1) => Z i ω), Z (n + 1) ω)) ⁻¹' (A ×ˢ C) =
      B ∩ Z (n + 1) ⁻¹' C := rfl
  have hin : B ∩ Z (n + 1) ⁻¹' C ∩ M =
      B ∩ M ∩ (fun ω : ℕ → α × α => ω (n + 1)) ⁻¹' (Prod.snd ⁻¹' C) := by
    ext ω
    simp only [mem_inter_iff, mem_preimage]
    constructor
    · rintro ⟨⟨hb, hc⟩, hm⟩
      refine ⟨⟨hb, hm⟩, ?_⟩
      rwa [← spliceAtMeeting_of_exists (Exists.imp (fun k hk => ⟨hk.1.trans n.le_succ, hk.2⟩) hm)]
    · rintro ⟨⟨hb, hm⟩, hc⟩
      refine ⟨⟨hb, ?_⟩, hm⟩
      rwa [← spliceAtMeeting_of_exists
        (Exists.imp (fun k hk => ⟨hk.1.trans n.le_succ, hk.2⟩) hm)] at hc
  have hout : (B ∩ Z (n + 1) ⁻¹' C) \ M =
      (B \ M) ∩ (fun ω : ℕ → α × α => ω (n + 1)) ⁻¹' (Prod.fst ⁻¹' C) := by
    ext ω
    simp only [mem_inter_iff, mem_sdiff, mem_preimage]
    constructor
    · rintro ⟨⟨hb, hc⟩, hm⟩
      have hne : ∀ k ≤ n, (ω k).1 ≠ (ω k).2 := fun k hk he => hm ⟨k, hk, he⟩
      refine ⟨⟨hb, hm⟩, ?_⟩
      rwa [← spliceAtMeeting_succ_of_forall_ne hne]
    · rintro ⟨⟨hb, hm⟩, hc⟩
      have hne : ∀ k ≤ n, (ω k).1 ≠ (ω k).2 := fun k hk he => hm ⟨k, hk, he⟩
      refine ⟨⟨hb, ?_⟩, hm⟩
      rwa [← spliceAtMeeting_succ_of_forall_ne hne] at hc
  rw [prefixLaw_compProd_apply_prod κ hZ n hA hC, Measure.map_apply
    ((measurable_pi_iff.2 fun i => hZ i.1).prodMk (hZ _)) (hA.prod hC), hfib,
    ← measure_inter_add_sdiff _ hM, hin, hout,
    markovChainLaw_inter_preimage_eval_succ ρ η n (hBn.inter hMn) (measurable_snd hC),
    markovChainLaw_inter_preimage_eval_succ ρ η n (hBn.diff hMn) (measurable_fst hC),
    ← lintegral_inter_add_sdiff (fun ω => κ (Z n ω) C) B hM]
  congr 1
  · refine setLIntegral_congr_fun (hB.inter hM) fun ω hω => ?_
    rw [← Measure.snd_apply hC, (hη _).snd_eq]
    exact congrArg (κ · C) (spliceAtMeeting_of_exists hω.2).symm
  · refine setLIntegral_congr_fun (hB.diff hM) fun ω hω => ?_
    rw [← Measure.fst_apply hC, (hη _).fst_eq]
    exact congrArg (κ · C)
      (spliceAtMeeting_of_forall_ne fun k hk he => hω.2 ⟨k, hk, he⟩).symm

end MeasureTheory.Measure

namespace ProbabilityTheory.Kernel

open TauCeti TauCeti.Probability

variable {α : Type*} [MeasurableSpace α] [MeasurableEq α]

/-- **The coupling inequality, in `ℝ≥0∞`.** Let every transition `η p` couple `κ p.1` and `κ p.2`
and let `ρ` couple `ν` and `ν'`. Then the total variation distance between the laws at time `n` of
the chains of `κ` started from `ν` and from `ν'` is at most twice the probability that the two
coordinates of the chain of `η` started from `ρ` have not met by time `n`. -/
theorem etvDist_pow_comp_le_of_isCoupling (κ : Kernel α α) [IsMarkovKernel κ]
    {η : Kernel (α × α) (α × α)} [IsMarkovKernel η] (hη : ∀ p, IsCoupling (η p) (κ p.1) (κ p.2))
    {ρ : Measure (α × α)} [IsFiniteMeasure ρ] {ν ν' : Measure α} (hρ : IsCoupling ρ ν ν')
    (n : ℕ) :
    etvDist ((κ ^ n : Kernel α α) ∘ₘ ν) ((κ ^ n : Kernel α α) ∘ₘ ν') ≤
      2 * markovChainLaw ρ η {ω | ∀ k ≤ n, (ω k).1 ≠ (ω k).2} := by
  set P := markovChainLaw ρ η
  have hν : ρ.fst = ν := hρ.fst_eq
  have hν' : ρ.snd = ν' := hρ.snd_eq
  subst hν hν'
  -- The time-`n` laws are those of the splice and of the second coordinate.
  have hZ : P.map (fun ω => spliceAtMeeting ω n) = (κ ^ n : Kernel α α) ∘ₘ ρ.fst := by
    rw [← Measure.markovChainLaw_map_eval, ← Measure.markovChainLaw_map_spliceAtMeeting ρ hη,
      Measure.map_map (measurable_pi_apply n) measurable_spliceAtMeeting]
    rfl
  have hY : P.map (fun ω => (ω n).2) = (κ ^ n : Kernel α α) ∘ₘ ρ.snd := by
    rw [← Measure.markovChainLaw_map_eval, ← Measure.markovChainLaw_map_snd_of_isCoupling ρ hη,
      Measure.map_map (measurable_pi_apply n) (by fun_prop)]
    rfl
  have hZm : Measurable fun ω : ℕ → α × α => spliceAtMeeting ω n :=
    (measurable_pi_apply n).comp measurable_spliceAtMeeting
  have hYm : Measurable fun ω : ℕ → α × α => (ω n).2 := by fun_prop
  have hM : MeasurableSet {ω : ℕ → α × α | ∃ k ≤ n, (ω k).1 = (ω k).2} :=
    Filtration.le _ n _ (measurableSet_piLE_exists_le_fst_eq_snd n)
  have hcompl : {ω : ℕ → α × α | ∃ k ≤ n, (ω k).1 = (ω k).2}ᶜ =
      {ω | ∀ k ≤ n, (ω k).1 ≠ (ω k).2} := by
    ext ω
    simp
  have hmass : P.map (fun ω => spliceAtMeeting ω n) univ = P.map (fun ω => (ω n).2) univ := by
    rw [Measure.map_apply hZm .univ, Measure.map_apply hYm .univ, preimage_univ, preimage_univ]
  rw [← hZ, ← hY, etvDist_le_two_mul_iff hmass]
  intro A hA
  -- Off the event of not having met, the splice at time `n` is the second coordinate.
  rw [Measure.map_apply hZm hA, Measure.map_apply hYm hA, ← hcompl]
  calc P ((fun ω => spliceAtMeeting ω n) ⁻¹' A)
      ≤ P ((fun ω => spliceAtMeeting ω n) ⁻¹' A ∩ {ω | ∃ k ≤ n, (ω k).1 = (ω k).2}) +
          P ({ω | ∃ k ≤ n, (ω k).1 = (ω k).2}ᶜ) := by
        rw [← measure_inter_add_sdiff _ hM, sdiff_eq]
        gcongr
        exact inter_subset_right
    _ ≤ P ((fun ω : ℕ → α × α => (ω n).2) ⁻¹' A) +
          P ({ω | ∃ k ≤ n, (ω k).1 = (ω k).2}ᶜ) := by
        gcongr
        rintro ω ⟨hω, hm⟩
        simpa [mem_preimage, spliceAtMeeting_of_exists hm] using hω

/-- **The coupling inequality.** Let every transition `η p` couple `κ p.1` and `κ p.2` and let `ρ`
couple `ν` and `ν'`. Then the total variation distance between the laws at time `n` of the chains
of `κ` started from `ν` and from `ν'` is at most twice the probability that the two coordinates of
the chain of `η` started from `ρ` have not met by time `n`. -/
theorem tvDist_pow_comp_le_of_isCoupling (κ : Kernel α α) [IsMarkovKernel κ]
    {η : Kernel (α × α) (α × α)} [IsMarkovKernel η] (hη : ∀ p, IsCoupling (η p) (κ p.1) (κ p.2))
    {ρ : Measure (α × α)} [IsFiniteMeasure ρ] {ν ν' : Measure α} (hρ : IsCoupling ρ ν ν')
    (n : ℕ) :
    tvDist ((κ ^ n : Kernel α α) ∘ₘ ν) ((κ ^ n : Kernel α α) ∘ₘ ν') ≤
      2 * (markovChainLaw ρ η).real {ω | ∀ k ≤ n, (ω k).1 ≠ (ω k).2} := by
  rw [tvDist, measureReal_def, ← ENNReal.toReal_ofNat 2, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (by finiteness) (etvDist_pow_comp_le_of_isCoupling κ hη hρ n)

/-- **The coupling inequality for independent copies.** For probability measures `ν` and `ν'`,
the total variation distance between the laws at time `n` of the chains of `κ` started from `ν`
and from `ν'` is at most twice the probability that two independent copies of the chain, started
from `ν` and `ν'`, have not met by time `n`. -/
theorem tvDist_pow_comp_le_parallelComp (κ : Kernel α α) [IsMarkovKernel κ] (ν ν' : Measure α)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ν'] (n : ℕ) :
    tvDist ((κ ^ n : Kernel α α) ∘ₘ ν) ((κ ^ n : Kernel α α) ∘ₘ ν') ≤
      2 * (markovChainLaw (ν.prod ν') (κ ∥ₖ κ)).real {ω | ∀ k ≤ n, (ω k).1 ≠ (ω k).2} := by
  have hη : ∀ p : α × α, IsCoupling ((κ ∥ₖ κ) p) (κ p.1) (κ p.2) := fun p => by
    rw [parallelComp_apply]
    exact isCoupling_prod _ _
  exact tvDist_pow_comp_le_of_isCoupling κ hη (isCoupling_prod ν ν') n

end ProbabilityTheory.Kernel
