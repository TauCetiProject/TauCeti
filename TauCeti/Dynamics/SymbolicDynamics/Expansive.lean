/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Topology.MetricSpace.PiNat
public import TauCeti.Dynamics.Expansive
public import TauCeti.Dynamics.SymbolicDynamics.Shift
public import TauCeti.Dynamics.SymbolicDynamics.Subshift
public import TauCeti.Topology.UniformSpace.DiscreteUniformity

/-!
# Shifts are expansive

Over an alphabet with the discrete uniformity, configurations whose translates all agree at a
fixed finite set of coordinates meeting every orbit are equal. Hence:

* every subshift `X : TauCeti.Subshift Γ I S` whose index set `I` has a finite set of coordinates
  meeting every `Γ`-orbit is an expansive `Γ`-action (`TauCeti.Subshift.isExpansiveAction`); in
  particular every subshift of `Γ → S` with `Γ` acting on itself, such as the two-sided full shift
  and its subshifts for `Γ = Multiplicative ℤ`, is expansive
  (`TauCeti.Subshift.isExpansiveAction_self`);
* the one-sided full shift on `ℕ → α` is expansive as the `ℕ`-action of its iterates
  (`TauCeti.isExpansiveAction_iterateMulAct_shift_nat`), and so is its restriction to every
  shift-invariant subset (`TauCeti.IsExpansiveAction.subMulAction`);
* for the metric `dist x y = (1/2)^n`, where `n` is the first coordinate at which `x` and `y`
  differ (Mathlib's `PiNat.metricSpace`), the one-sided full shift over a discrete alphabet is
  positively expansive with constant `3/4` (`TauCeti.isPositivelyExpansive_shift_piNat`).
-/

public section

namespace TauCeti

open Set Filter SymbolicDynamics.FullShift
open scoped Uniformity

namespace Subshift

variable {Γ I S : Type*} [Group Γ] [MulAction Γ I] [UniformSpace S] [DiscreteUniformity S]

/-- A subshift is an expansive action as soon as a finite set `F` of coordinates meets every orbit
of `Γ` on the index set: the entourage "agree on `F`" witnesses expansiveness, since distinct
configurations have translates that differ somewhere on `F`. -/
theorem isExpansiveAction (X : Subshift Γ I S) {F : Set I} (hF : F.Finite)
    (hFI : ∀ i : I, ∃ g : Γ, g • i ∈ F) : IsExpansiveAction Γ X := by
  rw [isExpansiveAction_iff]
  have hU : {p : (I → S) × (I → S) | ∀ i ∈ F, p.1 i = p.2 i} ∈ 𝓤 (I → S) :=
    Pi.hasBasis_uniformity_of_discreteUniformity.mem_of_mem hF
  refine ⟨{p : X × X | ∀ i ∈ F, p.1.val i = p.2.val i}, uniformContinuous_subtypeVal hU,
    fun x y hxy ↦ Subtype.ext (funext fun j ↦ ?_)⟩
  obtain ⟨g, hg⟩ := hFI j
  have := hxy g _ hg
  simpa [smul_apply] using this

/-- A subshift of `Γ → S`, with `Γ` acting on itself by left multiplication, is an expansive
action: configurations whose translates agree at the identity coordinate are equal. -/
theorem isExpansiveAction_self (X : Subshift Γ Γ S) : IsExpansiveAction Γ X :=
  X.isExpansiveAction (finite_singleton 1) fun i ↦ ⟨i⁻¹, by simp⟩

end Subshift

variable {α : Type*}

/-- The one-sided full shift on `ℕ → α` over an alphabet with the discrete uniformity is expansive
as the `ℕ`-action of its iterates: sequences whose shifts all agree at the coordinate `0` are
equal. -/
theorem isExpansiveAction_iterateMulAct_shift_nat [UniformSpace α] [DiscreteUniformity α] :
    IsExpansiveAction (IterateMulAct (shift (1 : ℕ) : (ℕ → α) → ℕ → α)) (ℕ → α) := by
  rw [isExpansiveAction_iff]
  refine ⟨{p | ∀ i ∈ ({0} : Set ℕ), p.1 i = p.2 i},
    Pi.hasBasis_uniformity_of_discreteUniformity.mem_of_mem (finite_singleton 0),
    fun x y hxy ↦ funext fun n ↦ ?_⟩
  have := hxy ⟨n⟩ 0 rfl
  simpa [IterateMulAct.mk_smul, shift_iterate] using this

/-- For the metric `dist x y = (1/2)^n` on `ℕ → α`, where `n` is the first coordinate at which `x`
and `y` differ, the one-sided full shift over a discrete alphabet is positively expansive with
constant `3/4`. -/
theorem isPositivelyExpansive_shift_piNat [TopologicalSpace α] [DiscreteTopology α] :
    letI := PiNat.metricSpace (E := fun _ : ℕ ↦ α)
    IsPositivelyExpansive (shift (1 : ℕ) : (ℕ → α) → ℕ → α) (3 / 4) := by
  let := PiNat.metricSpace (E := fun _ : ℕ ↦ α)
  refine isPositivelyExpansive_iff.2 fun x y hxy ↦ ?_
  refine ⟨PiNat.firstDiff x y, ?_⟩
  have hne : (shift (1 : ℕ))^[PiNat.firstDiff x y] x 0 ≠
      (shift (1 : ℕ))^[PiNat.firstDiff x y] y 0 := by
    simpa [shift_iterate] using PiNat.apply_firstDiff_ne hxy
  have hne' : (shift (1 : ℕ))^[PiNat.firstDiff x y] x ≠ (shift (1 : ℕ))^[PiNat.firstDiff x y] y :=
    fun h ↦ hne (congrFun h 0)
  rw [PiNat.dist_eq_of_ne hne',
    Nat.eq_zero_of_not_pos fun h ↦ hne (PiNat.apply_eq_of_lt_firstDiff h)]
  norm_num

end TauCeti
