/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Kernel.IonescuTulcea.Traj
public import TauCeti.Probability.Kernel.Composition.MeasureCompProd
public import TauCeti.Probability.Process.PathLaw.FiniteMarginals

/-!
# The path law of a homogeneous Markov chain

Given an initial law `ν` on a state space `α` and a transition kernel `κ : Kernel α α`, this file
builds the law `markovChainLaw ν κ` of the associated homogeneous Markov chain as a measure on path
space `ℕ → α`, and computes its finite-dimensional laws.

The construction is Mathlib's Ionescu–Tulcea measure `ProbabilityTheory.Kernel.trajMeasure` for the
time-indexed homogeneous kernel family that reads the current state off the trajectory so far and
steps by the fixed transition kernel `κ`. Two facts identify the resulting measure
(`eq_markovChainLaw`): its time-zero marginal is `ν`, and it has the Markov property
`markovChainLaw_map_prefix_succ_eq_compProd`, which recursively determines the law of a prefix of
length `n + 1` from the law of a prefix of length `n`. On a state space with measurable singletons
that recursion unwinds to the familiar product formula
`markovChainLaw_map_prefix_apply_singleton`,

```text
ℙ(X₀ = w 0, …, X n = w n) = ν {w 0} * ∏ i, κ (w i) {w (i + 1)},
```

which is the defining property of a Markov chain, and the form in which the finite path masses are
consumed downstream.

Started from a fixed state `x`, the chain has law `κ.markovChainKernel x`. This path-law kernel
depends measurably on `x`, its time-`n` marginals are the kernel powers `κ ^ n`, and integrating it
against an arbitrary initial law `ν` gives `markovChainLaw ν κ`; in particular the time-`n` law of
the chain is `(κ ^ n) ∘ₘ ν`.

## Main definitions

* `TauCeti.Probability.markovChainLaw` — the path law of the homogeneous Markov chain with initial
  law `ν` and transition kernel `κ`.
* `ProbabilityTheory.Kernel.markovChainKernel` — the path-law kernel
  `x ↦ markovChainLaw (dirac x) κ`, the law of the chain as a measurable function of its starting
  state.

## Main results

* `TauCeti.Probability.markovChainLaw_map_eval_zero` — the chain starts from `ν`.
* `MeasureTheory.Measure.markovChainLaw_eq_comp` — the path law with initial law `ν` is the path-law
  kernel integrated against `ν`.
* `MeasureTheory.Measure.markovChainLaw_map_eval` — the state at time `n` has law `(κ ^ n) ∘ₘ ν`;
  `ProbabilityTheory.Kernel.markovChainKernel_map_eval` is the kernel form.
* `TauCeti.Probability.markovChainLaw_map_prefix_succ_eq_compProd` — the Markov property: the joint
  law of a prefix and of the next state is the prefix law extended by one `κ`-step from its last
  coordinate.
* `TauCeti.Probability.markovChainLaw_map_pair_succ`,
  `TauCeti.Probability.markovChainLaw_map_eval_succ` — the two-coordinate form of the Markov
  property and the forward recursion for the one-dimensional marginals.
* `TauCeti.Probability.markovChainLaw_map_prefix_apply_singleton` — on a state space with
  measurable singletons, the mass of a finite path is the initial weight times the product of the
  transition weights; `MeasureTheory.Measure.markovChainLaw_prefixLaw_singleton` is the same formula
  for the prefix laws of the coordinate process.
* `MeasureTheory.Measure.eq_markovChainLaw` — the path law is the only measure on path space with
  initial law `ν` satisfying the Markov recursion for its prefix laws.

## References

* J. R. Norris, *Markov Chains*, Cambridge University Press, 1997, §1.1, for the time-`n` marginals
  as the initial law propagated by the `n`-step transition kernel.
* Olav Kallenberg, *Foundations of Modern Probability*, 2nd edition, Springer, 2002, Chapter 7,
  for the path law of a Markov chain with a given initial law and transition kernel.
-/

public section

noncomputable section

open Finset MeasureTheory Preorder ProbabilityTheory

open scoped ENNReal

namespace TauCeti

namespace Probability

variable {α : Type*} [MeasurableSpace α]

/-- Reading a trajectory indexed by the times `≤ n` as a tuple of length `n + 1`.

This is the change of index that connects Mathlib's Ionescu–Tulcea API, which restricts a path to
`Finset.Iic n`, with the `Fin`-indexed prefix laws used downstream. -/
private def iicEquivFin (α : Type*) [MeasurableSpace α] (n : ℕ) :
    ((_ : ↥(Iic n)) → α) ≃ᵐ (Fin (n + 1) → α) :=
  (MeasurableEquiv.piCongrLeft (fun _ : ↥(Iic n) => α)
    ((Iic n).orderIsoOfFin (k := n + 1) (by simp))).symm

private theorem coe_orderIsoIic_apply (n : ℕ) (i : Fin (n + 1)) :
    (((Iic n).orderIsoOfFin (k := n + 1) (by simp) i : ↥(Iic n)) : ℕ) = i := by
  rw [Finset.coe_orderIsoOfFin_apply]
  symm
  exact congrFun (Finset.orderEmbOfFin_unique (by simp)
    (fun j => mem_Iic.2 (Nat.le_of_lt_succ j.2)) Fin.val_strictMono) i

@[simp]
private theorem iicEquivFin_apply (n : ℕ) (u : (_ : ↥(Iic n)) → α) (i : Fin (n + 1)) :
    iicEquivFin α n u i = u ⟨i.1, mem_Iic.2 (Nat.lt_succ_iff.1 i.2)⟩ :=
  by
    -- `piCongrLeft` acts by precomposition, so its coercion reduces definitionally to this value.
    change u ((Iic n).orderIsoOfFin (k := n + 1) (by simp) i) = _
    congr 1
    ext
    exact coe_orderIsoIic_apply n i

@[simp]
private theorem iicEquivFin_symm_apply (n : ℕ) (w : Fin (n + 1) → α) (j : ↥(Iic n)) :
    (iicEquivFin α n).symm w j = w ⟨j.1, Nat.lt_succ_iff.2 (mem_Iic.1 j.2)⟩ :=
  by
    simp only [iicEquivFin, MeasurableEquiv.symm_symm]
    rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
    simp only [eq_rec_constant]
    congr 1
    ext
    -- The subtype coercion exposes the value component of the inverse order isomorphism.
    change (((Iic n).orderIsoOfFin (k := n + 1) (by simp)).symm j : Fin (n + 1)).1 = j.1
    have h := coe_orderIsoIic_apply n
      (((Iic n).orderIsoOfFin (k := n + 1) (by simp)).symm j)
    simpa using h.symm

/-- The kernel family driving the Ionescu–Tulcea construction of a homogeneous chain: from a
trajectory up to time `n`, step by `κ` out of the state occupied at time `n`. -/
private def markovStep (κ : Kernel α α) (n : ℕ) : Kernel ((_ : ↥(Iic n)) → α) α :=
  κ.comap (fun u => u ⟨n, mem_Iic.2 le_rfl⟩) (measurable_pi_apply _)

private instance (κ : Kernel α α) [IsMarkovKernel κ] (n : ℕ) : IsMarkovKernel (markovStep κ n) :=
  inferInstanceAs (IsMarkovKernel (κ.comap _ _))

/-- **The path law of a homogeneous Markov chain** with initial law `ν` and transition kernel `κ`:
the Ionescu–Tulcea measure of the time-indexed homogeneous family `markovStep κ` induced by the
fixed transition kernel `κ`. -/
def markovChainLaw (ν : Measure α) (κ : Kernel α α) [IsMarkovKernel κ] : Measure (ℕ → α) :=
  Kernel.trajMeasure (X := fun _ => α) ν (markovStep κ)

variable (ν : Measure α) (κ : Kernel α α) [IsMarkovKernel κ]

instance [IsProbabilityMeasure ν] : IsProbabilityMeasure (markovChainLaw ν κ) :=
  inferInstanceAs (IsProbabilityMeasure (Kernel.trajMeasure _ _))

instance [IsFiniteMeasure ν] : IsFiniteMeasure (markovChainLaw ν κ) :=
  inferInstanceAs (IsFiniteMeasure (Kernel.traj _ 0 ∘ₘ _))

instance [SFinite ν] : SFinite (markovChainLaw ν κ) :=
  inferInstanceAs (SFinite (Kernel.traj _ 0 ∘ₘ _))

/-- **The path-law kernel of a homogeneous Markov chain**: the kernel sending a state `x` to the law
`markovChainLaw (Measure.dirac x) κ` of the chain started at `x` (`markovChainKernel_apply`). Being
a kernel, it records that this law depends measurably on the starting state, and every path law of
the chain is its mixture over the initial law (`markovChainLaw_eq_comp`). -/
def _root_.ProbabilityTheory.Kernel.markovChainKernel : Kernel α (ℕ → α) :=
  (Kernel.traj (markovStep κ) 0).comap (MeasurableEquiv.piUnique fun _ : ↥(Iic (0 : ℕ)) => α).symm
    (MeasurableEquiv.measurable _)

instance : IsMarkovKernel κ.markovChainKernel :=
  inferInstanceAs (IsMarkovKernel (Kernel.comap _ _ _))

/-- **The path law is a mixture of the laws started at fixed states**: the path law with initial
law `ν` is the path-law kernel integrated against `ν`. This holds for every initial measure `ν`. -/
theorem _root_.MeasureTheory.Measure.markovChainLaw_eq_comp :
    markovChainLaw ν κ = κ.markovChainKernel ∘ₘ ν := by
  rw [markovChainLaw, Kernel.trajMeasure,
    Measure.bind_map (MeasurableEquiv.measurable _).aemeasurable (Kernel.aemeasurable _),
    Kernel.markovChainKernel, Kernel.coe_comap, Function.comp_def]

/-- The path-law kernel evaluated at a state `x` is the law of the chain started at `x`. -/
@[simp]
theorem _root_.ProbabilityTheory.Kernel.markovChainKernel_apply (x : α) :
    κ.markovChainKernel x = markovChainLaw (Measure.dirac x) κ := by
  rw [Measure.markovChainLaw_eq_comp, Measure.dirac_bind (Kernel.measurable _)]

/-- **The law of the chain depends measurably on its starting state.** -/
theorem _root_.ProbabilityTheory.Kernel.measurable_markovChainLaw_dirac :
    Measurable fun x => markovChainLaw (Measure.dirac x) κ := by
  have h : (fun x => markovChainLaw (Measure.dirac x) κ) = κ.markovChainKernel :=
    funext fun x => (κ.markovChainKernel_apply x).symm
  rw [h]
  exact κ.markovChainKernel.measurable

/-- The trajectory of the chain restricted to time `0` is the initial law, transported along the
canonical identification of `(_ : ↥(Iic 0)) → α` with `α`. -/
private theorem markovChainLaw_map_frestrictLe_zero :
    (markovChainLaw ν κ).map (frestrictLe 0) =
      ν.map (MeasurableEquiv.piUnique fun _ : ↥(Iic (0 : ℕ)) => α).symm := by
  rw [markovChainLaw, Kernel.trajMeasure,
    Measure.map_comp _ _ (measurable_frestrictLe _), Kernel.traj_map_frestrictLe,
    Kernel.partialTraj_self, Measure.id_comp]

/-- **The chain starts from its initial law.** -/
@[simp]
theorem markovChainLaw_map_eval_zero :
    (markovChainLaw ν κ).map (fun x => x 0) = ν := by
  have hcomp : (fun x : ℕ → α => x 0)
      = (fun u : ((_ : ↥(Iic (0 : ℕ))) → α) => u ⟨0, mem_Iic.2 le_rfl⟩) ∘ frestrictLe 0 := rfl
  have hid : (fun u : ((_ : ↥(Iic (0 : ℕ))) → α) => u ⟨0, mem_Iic.2 le_rfl⟩) ∘
      (MeasurableEquiv.piUnique fun _ : ↥(Iic (0 : ℕ)) => α).symm = id := by
    funext a
    simp [MeasurableEquiv.piUnique, Equiv.piUnique, uniqueElim_const]
  calc (markovChainLaw ν κ).map (fun x => x 0)
      = ((markovChainLaw ν κ).map (frestrictLe 0)).map
          (fun u : ((_ : ↥(Iic (0 : ℕ))) → α) => u ⟨0, mem_Iic.2 le_rfl⟩) := by
        rw [Measure.map_map (μ := markovChainLaw ν κ) (f := frestrictLe 0)
          (g := fun u : ((_ : ↥(Iic (0 : ℕ))) → α) => u ⟨0, mem_Iic.2 le_rfl⟩)
          (by fun_prop) (measurable_frestrictLe 0), hcomp]
    _ = ν := by
        rw [markovChainLaw_map_frestrictLe_zero,
          Measure.map_map (μ := ν)
            (f := ⇑(MeasurableEquiv.piUnique fun _ : ↥(Iic (0 : ℕ)) => α).symm)
            (g := fun u : ((_ : ↥(Iic (0 : ℕ))) → α) => u ⟨0, mem_Iic.2 le_rfl⟩)
            (by fun_prop) (MeasurableEquiv.measurable _), hid, Measure.map_id]

/-- **The Markov property of the chain.** The joint law of the length-`n + 1` prefix
`(X 0, …, X n)` and of the next state `X (n + 1)` is the prefix law extended by one `κ`-step out of
the last coordinate of the prefix. Together with `markovChainLaw_map_eval_zero` this determines all
the finite-dimensional laws of the chain. -/
theorem markovChainLaw_map_prefix_succ_eq_compProd [SFinite ν] (n : ℕ) :
    (markovChainLaw ν κ).map (fun x => ((fun i : Fin (n + 1) => x i.1), x (n + 1)))
      = ((markovChainLaw ν κ).map fun x (i : Fin (n + 1)) => x i.1) ⊗ₘ
        κ.comap (fun w : Fin (n + 1) → α => w (Fin.last n))
          (measurable_pi_apply (Fin.last n)) := by
  have he : Measurable (iicEquivFin α n) := (iicEquivFin α n).measurable
  have hmap : Measurable (Prod.map (iicEquivFin α n) (id : α → α)) := he.prodMap measurable_id
  have hpair : Measurable fun x : ℕ → α => (frestrictLe n x, x (n + 1)) := by fun_prop
  have hstep : markovStep κ n
      = (κ.comap (fun w : Fin (n + 1) → α => w (Fin.last n))
          (measurable_pi_apply (Fin.last n))).comap (iicEquivFin α n) he := by
    ext u s _
    simp [markovStep, Kernel.comap_apply, iicEquivFin_apply]
  have key : ((markovChainLaw ν κ).map (frestrictLe n)) ⊗ₘ markovStep κ n
      = (markovChainLaw ν κ).map (fun x => (frestrictLe n x, x (n + 1))) := by
    rw [Measure.compProd_eq_comp_prod, markovChainLaw, Kernel.trajMeasure,
      Measure.map_comp _ _ (measurable_frestrictLe n), Kernel.traj_map_frestrictLe,
      Measure.comp_assoc, Measure.map_comp _ _ hpair]
    congr with x₀ : 1
    rw [Kernel.comp_apply, ← Measure.compProd_eq_comp_prod, Kernel.map_apply _ hpair,
      Kernel.partialTraj_compProd_eq_map_traj zero_le]
  calc (markovChainLaw ν κ).map (fun x => ((fun i : Fin (n + 1) => x i.1), x (n + 1)))
      = ((markovChainLaw ν κ).map (fun x => (frestrictLe n x, x (n + 1)))).map
          (Prod.map (iicEquivFin α n) id) := by
        rw [Measure.map_map hmap hpair]
        congr 1
        funext x
        apply Prod.ext
        · funext i
          simp [frestrictLe, iicEquivFin_apply]
        · rfl
    _ = (((markovChainLaw ν κ).map (frestrictLe n)) ⊗ₘ markovStep κ n).map
          (Prod.map (iicEquivFin α n) id) := by rw [key]
    _ = ((markovChainLaw ν κ).map (frestrictLe n)).map (iicEquivFin α n) ⊗ₘ
          κ.comap (fun w : Fin (n + 1) → α => w (Fin.last n))
            (measurable_pi_apply (Fin.last n)) := by
        rw [hstep]; exact TauCeti.Measure.map_prodMap_compProd_comap _ _ he
    _ = _ := by
        rw [Measure.map_map he (measurable_frestrictLe n)]
        congr 2
        funext x i
        exact iicEquivFin_apply n (frestrictLe n x) i

/-- **The one-step transition law of the chain.** The joint law of the states at times `n` and
`n + 1` is the time-`n` law extended by `κ`; this is the Markov property read off two coordinates
rather than a whole prefix. -/
theorem markovChainLaw_map_pair_succ [IsProbabilityMeasure ν] (n : ℕ) :
    (markovChainLaw ν κ).map (fun x => (x n, x (n + 1)))
      = ((markovChainLaw ν κ).map fun x => x n) ⊗ₘ κ := by
  have hlast : Measurable fun w : Fin (n + 1) → α => w (Fin.last n) :=
    measurable_pi_apply (Fin.last n)
  have hmap : Measurable
      (Prod.map (fun w : Fin (n + 1) → α => w (Fin.last n)) (id : α → α)) :=
    hlast.prodMap measurable_id
  have hprod : Measurable
      fun x : ℕ → α => ((fun i : Fin (n + 1) => x i.1), x (n + 1)) := by fun_prop
  calc (markovChainLaw ν κ).map (fun x => (x n, x (n + 1)))
      = ((markovChainLaw ν κ).map
          fun x => ((fun i : Fin (n + 1) => x i.1), x (n + 1))).map
          (Prod.map (fun w : Fin (n + 1) → α => w (Fin.last n)) id) := by
        rw [Measure.map_map hmap hprod]; rfl
    _ = (((markovChainLaw ν κ).map fun x (i : Fin (n + 1)) => x i.1) ⊗ₘ
          κ.comap (fun w : Fin (n + 1) → α => w (Fin.last n)) hlast).map
          (Prod.map (fun w : Fin (n + 1) → α => w (Fin.last n)) id) := by
        rw [markovChainLaw_map_prefix_succ_eq_compProd]
    _ = ((markovChainLaw ν κ).map fun x (i : Fin (n + 1)) => x i.1).map
          (fun w : Fin (n + 1) → α => w (Fin.last n)) ⊗ₘ κ :=
        TauCeti.Measure.map_prodMap_compProd_comap _ _ hlast
    _ = _ := by rw [Measure.map_map hlast (by fun_prop)]; rfl

/-- **The time-`n` laws of the chain satisfy the forward recursion**: the law at time `n + 1` is the
law at time `n` pushed through the transition kernel. With `markovChainLaw_map_eval_zero` this
identifies every one-dimensional marginal of the chain. -/
@[simp]
theorem markovChainLaw_map_eval_succ [IsProbabilityMeasure ν] (n : ℕ) :
    (markovChainLaw ν κ).map (fun x => x (n + 1))
      = κ ∘ₘ ((markovChainLaw ν κ).map fun x => x n) := by
  rw [← Measure.snd_compProd, ← markovChainLaw_map_pair_succ, Measure.snd_map_prodMk₀]
  exacts [(measurable_pi_apply n).aemeasurable, (measurable_pi_apply (n + 1)).aemeasurable]

/-- **The time-`n` marginals of the path-law kernel are the kernel powers**: started at `x`, the
chain is at time `n` distributed as `(κ ^ n) x`. -/
@[simp]
theorem _root_.ProbabilityTheory.Kernel.markovChainKernel_map_eval (n : ℕ) :
    κ.markovChainKernel.map (fun w => w n) = κ ^ n := by
  ext1 x
  rw [Kernel.map_apply _ (measurable_pi_apply n), Kernel.markovChainKernel_apply]
  induction n with
  | zero =>
    rw [markovChainLaw_map_eval_zero, pow_zero]
    -- The unit of the monoid of kernels `Kernel α α` is `Kernel.id`, which has no rewrite lemma.
    exact (Kernel.id_apply x).symm
  | succ n ih =>
    rw [markovChainLaw_map_eval_succ, ih, add_comm, Kernel.pow_add, pow_one, Kernel.comp_apply]

/-- **The time-`n` marginal of the chain**: the state at time `n` has law `(κ ^ n) ∘ₘ ν`, the
initial law propagated by the `n`-step transition kernel. This holds for every initial measure
`ν`. -/
theorem _root_.MeasureTheory.Measure.markovChainLaw_map_eval (n : ℕ) :
    (markovChainLaw ν κ).map (fun w => w n) = (κ ^ n) ∘ₘ ν := by
  rw [Measure.markovChainLaw_eq_comp, Measure.map_comp _ _ (measurable_pi_apply n),
    Kernel.markovChainKernel_map_eval]

/-- **The finite path masses of the chain.** On a state space with measurable singletons the mass a
homogeneous Markov chain gives to a finite path is the initial weight of its first state times the
product of the transition weights along it. This is the defining product form of the
finite-dimensional laws of a Markov chain. -/
theorem markovChainLaw_map_prefix_apply_singleton [IsProbabilityMeasure ν]
    [MeasurableSingletonClass α] (n : ℕ) (w : Fin (n + 1) → α) :
    ((markovChainLaw ν κ).map fun x (i : Fin (n + 1)) => x i.1) {w}
      = ν {w 0} * ∏ i : Fin n, κ (w i.castSucc) {w i.succ} := by
  induction n with
  | zero =>
    have hc : (fun (x : ℕ → α) (i : Fin 1) => x i.1)
        = (fun (a : α) (_ : Fin 1) => a) ∘ (fun x : ℕ → α => x 0) := by
      funext x i
      simp
    have hpre : (fun (a : α) (_ : Fin 1) => a) ⁻¹' {w} = {w 0} := by
      ext a
      simp only [Set.mem_preimage, Set.mem_singleton_iff, funext_iff]
      exact ⟨fun h => h 0, fun h i => by rw [h, Subsingleton.elim (0 : Fin 1) i]⟩
    rw [hc, ← Measure.map_map (by fun_prop) (by fun_prop), markovChainLaw_map_eval_zero,
      Measure.map_apply (by fun_prop) (measurableSet_singleton w), hpre]
    simp
  | succ n ih =>
    have hprod : Measurable
        fun x : ℕ → α => ((fun i : Fin (n + 1) => x i.1), x (n + 1)) := by fun_prop
    have hpre : (fun (x : ℕ → α) (i : Fin (n + 2)) => x i.1) ⁻¹' {w}
        = (fun x : ℕ → α => ((fun i : Fin (n + 1) => x i.1), x (n + 1))) ⁻¹'
          {(Fin.init w, w (Fin.last (n + 1)))} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq, funext_iff]
      refine ⟨fun h => ⟨fun i => h i.castSucc, h (Fin.last (n + 1))⟩, fun h i => ?_⟩
      refine Fin.lastCases ?_ (fun j => ?_) i
      · exact h.2
      · exact h.1 j
    rw [Measure.map_apply (by fun_prop) (measurableSet_singleton w), hpre,
      ← Measure.map_apply hprod (measurableSet_singleton _),
      markovChainLaw_map_prefix_succ_eq_compProd, Measure.compProd_apply
        (measurableSet_singleton _)]
    have hint : ∀ v : Fin (n + 1) → α,
        (κ.comap (fun y : Fin (n + 1) → α => y (Fin.last n))
            (measurable_pi_apply (Fin.last n))) v
          (Prod.mk v ⁻¹' ({(Fin.init w, w (Fin.last (n + 1)))} :
            Set ((Fin (n + 1) → α) × α)))
        = Set.indicator {Fin.init w}
            (fun _ => κ (w (Fin.last n).castSucc) {w (Fin.last (n + 1))}) v := by
      intro v
      by_cases hv : v = Fin.init w
      · subst hv
        have hfibre : (Prod.mk (Fin.init w) ⁻¹'
            ({(Fin.init w, w (Fin.last (n + 1)))} : Set ((Fin (n + 1) → α) × α)))
            = {w (Fin.last (n + 1))} := by
          ext c; simp
        rw [hfibre, Kernel.comap_apply]
        simp [Fin.init]
      · have hfibre : (Prod.mk v ⁻¹'
            ({(Fin.init w, w (Fin.last (n + 1)))} : Set ((Fin (n + 1) → α) × α))) = ∅ := by
          ext c; simp [hv]
        rw [hfibre]
        simp [hv]
    rw [lintegral_congr hint, lintegral_indicator (measurableSet_singleton _),
      setLIntegral_const, ih (Fin.init w), Fin.prod_univ_castSucc]
    have hsucc : (Fin.last n).succ = Fin.last (n + 1) := Fin.succ_last n
    simp only [Fin.init, Fin.castSucc_zero, hsucc, Fin.succ_castSucc]
    ring

/-- **The finite path masses of the chain, as prefix laws.** The product formula
`markovChainLaw_map_prefix_apply_singleton`, restated for the prefix laws of the coordinate process;
this is the form consumed by statements about the finite path laws of a process. -/
theorem _root_.MeasureTheory.Measure.markovChainLaw_prefixLaw_singleton
    [IsProbabilityMeasure ν] [MeasurableSingletonClass α]
    (n : ℕ) (w : Fin (n + 1) → α) :
    prefixLaw (markovChainLaw ν κ) (fun i x => x i) (n + 1) {w}
      = ν {w 0} * ∏ i : Fin n, κ (w i.castSucc) {w i.succ} := by
  rw [prefixLaw_def, blockLaw_def]
  exact markovChainLaw_map_prefix_apply_singleton ν κ n w

/-- **Uniqueness of the path law.** A measure on path space whose time-zero marginal is `ν` and
whose prefix laws satisfy the Markov recursion of `markovChainLaw_map_prefix_succ_eq_compProd` is
the path law `markovChainLaw ν κ`. -/
theorem _root_.MeasureTheory.Measure.eq_markovChainLaw [IsFiniteMeasure ν]
    {μ : Measure (ℕ → α)}
    (h₀ : μ.map (fun x => x 0) = ν)
    (hstep : ∀ n, μ.map (fun x => ((fun i : Fin (n + 1) => x i.1), x (n + 1)))
      = (μ.map fun x (i : Fin (n + 1)) => x i.1) ⊗ₘ
        κ.comap (fun w : Fin (n + 1) → α => w (Fin.last n))
          (measurable_pi_apply (Fin.last n))) :
    μ = markovChainLaw ν κ := by
  -- The laws of the prefixes `(X 0, …, X n)` agree, by induction on `n`.
  have hpre : ∀ n : ℕ, μ.map (fun x (i : Fin (n + 1)) => x i.1)
      = (markovChainLaw ν κ).map (fun x (i : Fin (n + 1)) => x i.1) := by
    intro n
    induction n with
    | zero =>
      have hc : (fun (x : ℕ → α) (i : Fin 1) => x i.1)
          = (fun (a : α) (_ : Fin 1) => a) ∘ (fun x : ℕ → α => x 0) := by
        funext x i
        simp [Fin.fin_one_eq_zero i]
      rw [hc, ← Measure.map_map (by fun_prop) (by fun_prop),
        ← Measure.map_map (by fun_prop) (by fun_prop), h₀, markovChainLaw_map_eval_zero]
    | succ n ih =>
      have hc : (fun (x : ℕ → α) (i : Fin (n + 2)) => x i.1)
          = (fun p : (Fin (n + 1) → α) × α => Fin.snoc p.1 p.2) ∘
            (fun x : ℕ → α => ((fun i : Fin (n + 1) => x i.1), x (n + 1))) := by
        funext x i
        refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
      have hsnoc : Measurable
          fun p : (Fin (n + 1) → α) × α => (Fin.snoc p.1 p.2 : Fin (n + 2) → α) :=
        measurable_pi_iff.2 fun i => Fin.lastCases (by simp only [Fin.snoc_last]; fun_prop)
          (fun j => by simp only [Fin.snoc_castSucc]; fun_prop) i
      rw [hc, ← Measure.map_map hsnoc (by fun_prop), ← Measure.map_map hsnoc (by fun_prop), hstep,
        ih, markovChainLaw_map_prefix_succ_eq_compProd]
  -- Every prefix law is a pushforward of one of these, so finite-marginal uniqueness applies.
  refine (measure_eq_of_prefixProj_map_eq fun n => ?_).symm
  have hc : prefixProj α n = (fun (w : Fin (n + 1) → α) (i : Fin n) => w i.castSucc) ∘
      (fun x (i : Fin (n + 1)) => x i.1) := by
    funext x i
    simp
  rw [hc, ← Measure.map_map (by fun_prop) (by fun_prop),
    ← Measure.map_map (by fun_prop) (by fun_prop), hpre]

end Probability

end TauCeti

end

end
