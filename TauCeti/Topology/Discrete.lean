/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Order

/-!
# Maps and convergence in discrete spaces

A continuous map into a discrete space is locally constant, and this file records three
consequences. Pointwise continuous families of equivalences into a discrete space have continuous
inverse evaluation, whatever the topology of their source (`TauCeti.continuous_equiv_symm_apply`).
This supplies continuity of inverse permutation evaluation in
`TauCeti.WreathProduct.continuous_right_inv` and
inverse coset translation in `Subgroup.continuous_inv_smul_const`. A continuous map lifts along any
surjection onto a discrete space (`TauCeti.exists_continuous_lift`), and an injection into a
discrete space reflects continuity (`TauCeti.continuous_of_injective_comp`); these give
surjectivity and the descent of cocycle conditions for continuous cochains of discrete modules
in `TauCeti/RepresentationTheory/Homological/ContCohomology/ShortExact.lean`.

A family eventually contained in a subset and converging to one of its points witnesses
nondiscreteness when it is frequently unequal to that point (`Filter.Tendsto.not_isDiscrete`).
This criterion uses only the target topology and applies to ranges of homomorphisms whose
nonidentity values accumulate at the identity.
-/

public section

namespace TauCeti

/-- Inverse evaluation of a family of equivalences into a discrete space is continuous if every
forward evaluation is continuous, whatever the topology on the source of the equivalences. -/
theorem continuous_equiv_symm_apply {α β γ : Type*} [TopologicalSpace α] [TopologicalSpace β]
    [TopologicalSpace γ] [DiscreteTopology γ] {f : α → β ≃ γ}
    (hf : ∀ c, Continuous fun a => f a c) (b : γ) :
    Continuous fun a => (f a).symm b := by
  apply IsLocallyConstant.continuous
  rw [IsLocallyConstant.iff_isOpen_fiber]
  intro c
  simpa only [Set.preimage, Set.mem_singleton_iff, Equiv.symm_apply_eq, eq_comm (a := b)] using
    (isOpen_discrete ({b} : Set γ)).preimage (hf c)

/-- **A continuous map lifts along any surjection onto a discrete space.** A continuous map into
the discrete `C` is locally constant, so composing it with any set-theoretic section of `p` is
continuous again. -/
theorem exists_continuous_lift {X B C : Type*} [TopologicalSpace X] [TopologicalSpace B]
    [TopologicalSpace C] [DiscreteTopology C] {p : B → C} (hp : Function.Surjective p)
    {f : X → C} (hf : Continuous f) : ∃ e : X → B, Continuous e ∧ ∀ x, p (e x) = f x :=
  ⟨fun x => Function.surjInv hp (f x),
    (continuous_of_discreteTopology (f := Function.surjInv hp)).comp hf,
    fun x => Function.surjInv_eq hp (f x)⟩

/-- **An injective map into a discrete space reflects continuity.** Continuity into the discrete
`B` is local constancy, local constancy descends along an injection, and a locally constant map is
continuous. -/
theorem continuous_of_injective_comp {X A B : Type*} [TopologicalSpace X] [TopologicalSpace A]
    [TopologicalSpace B] [DiscreteTopology B] {f : A → B} (hf : Function.Injective f) {a : X → A}
    (h : Continuous fun x => f (a x)) : Continuous a :=
  (IsLocallyConstant.desc a f ((IsLocallyConstant.iff_continuous _).2 h) hf).continuous

end TauCeti

open Topology

namespace Filter

/-- A subset containing the limit of an eventually contained family is nondiscrete if the family
is frequently different from the limit. -/
theorem Tendsto.not_isDiscrete {X Y : Type*} [TopologicalSpace Y] {f : X → Y} {l : Filter X}
    {a : Y} {s : Set Y} (hf : Tendsto f l (𝓝 a)) (ha : a ∈ s)
    (hs : ∀ᶠ x in l, f x ∈ s) (hne : ∃ᶠ x in l, f x ≠ a) : ¬ IsDiscrete s := by
  intro hD
  have heq := tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hf hs
  rw [nhdsWithin_of_mem_discrete hD ha, tendsto_pure] at heq
  exact hne (heq.mono fun _ h hne ↦ hne h)

end Filter
