/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.Order.Lattice

/-!
# Measurability of finite infima and suprema, and of a maximizing index

Mathlib's `Mathlib.MeasureTheory.Order.Lattice` proves `Finset.measurable_sup'` for a nonempty
finite supremum in the function lattice `δ → α`, but omits the dual nonempty finite infimum lemma
`Finset.measurable_inf'` and the general pointwise forms `fun x ↦ s.inf' hs fun i ↦ f i x` and
`fun x ↦ s.sup' hs fun i ↦ f i x`. This file supplies those `fun_prop` lemmas under the minimal
semilattice measurability classes `MeasurableInf₂` and `MeasurableSup₂`.

With a bottom element, the pointwise supremum `x ↦ s.sup (f · x)` of a possibly empty finite
family is measurable (`Finset.measurable_sup_apply`). For a linear order, the last index `m < N`
attaining `max_{m < N} fₘ(x)` can be chosen measurably in `x`
(`TauCeti.exists_measurable_finsetSup_eq`).
-/

public section

open MeasureTheory

namespace Finset

section SemilatticeInf

variable {δ α : Type*} [MeasurableSpace δ] [MeasurableSpace α] [SemilatticeInf α]
  [MeasurableInf₂ α]

/-- The infimum of a nonempty finite family of measurable functions is measurable. -/
@[fun_prop]
theorem measurable_inf' {ι : Type*} {s : Finset ι} (hs : s.Nonempty) {f : ι → δ → α}
    (hf : ∀ i ∈ s, Measurable (f i)) : Measurable (s.inf' hs f) :=
  s.inf'_induction hs _ (fun _f hf _g hg ↦ hf.inf hg) fun i hi ↦ hf i hi

/-- The pointwise infimum of a nonempty finite family of measurable functions is measurable. -/
@[fun_prop]
theorem measurable_inf'' {ι : Type*} {s : Finset ι} (hs : s.Nonempty) {f : ι → δ → α}
    (hf : ∀ i ∈ s, Measurable (f i)) :
    Measurable fun x ↦ s.inf' hs fun i ↦ f i x := by
  convert s.measurable_inf' hs hf using 1
  ext x
  simp

end SemilatticeInf

section SemilatticeSup

variable {δ α : Type*} [MeasurableSpace δ] [MeasurableSpace α] [SemilatticeSup α]
  [MeasurableSup₂ α]

/-- The pointwise supremum of a nonempty finite family of measurable functions is measurable. -/
@[fun_prop]
theorem measurable_sup'' {ι : Type*} {s : Finset ι} (hs : s.Nonempty) {f : ι → δ → α}
    (hf : ∀ i ∈ s, Measurable (f i)) :
    Measurable fun x ↦ s.sup' hs fun i ↦ f i x := by
  convert s.measurable_sup' hs hf using 1
  ext x
  simp

/-- The pointwise supremum `x ↦ s.sup (f · x)` of finitely many measurable functions is
measurable. Unlike `Finset.measurable_sup''`, the index set may be empty. -/
theorem measurable_sup_apply [OrderBot α] {ι : Type*} (s : Finset ι) {f : ι → δ → α}
    (hf : ∀ i ∈ s, Measurable (f i)) : Measurable fun x ↦ s.sup (f · x) := by
  convert Finset.sup_induction (p := Measurable) (s := s) (f := f) measurable_const
    (fun _ h₁ _ h₂ ↦ h₁.sup h₂) hf using 1
  ext x
  simp

end SemilatticeSup

end Finset

namespace TauCeti

variable {δ α : Type*} [MeasurableSpace δ] [MeasurableSpace α]

/-- **A measurable maximizing index.** For measurable `fₘ : δ → α` with values in a linear order,
the last index `m < N` attaining the maximum `max_{m < N} fₘ(x)` depends measurably on `x`. It is
chosen by `Nat.findGreatest`, so it is at most `N`, and it attains the maximum wherever the maximum
is not `⊥`. -/
theorem exists_measurable_finsetSup_eq [LinearOrder α] [OrderBot α] [MeasurableSup₂ α]
    [MeasurableEq α] {f : ℕ → δ → α} (hf : ∀ m, Measurable (f m)) (N : ℕ) :
    ∃ ψ : δ → ℕ, Measurable ψ ∧ (∀ x, ψ x ≤ N) ∧
      ∀ x, (Finset.range N).sup (f · x) ≠ ⊥ → f (ψ x) x = (Finset.range N).sup (f · x) := by
  refine ⟨fun x ↦ Nat.findGreatest (fun m ↦ m < N ∧ f m x = (Finset.range N).sup (f · x)) N,
    measurable_findGreatest fun m _ ↦ (MeasurableSet.const _).inter
      (measurableSet_eq_fun (hf m) ((Finset.range N).measurable_sup_apply fun m _ ↦ hf m)),
    fun x ↦ Nat.findGreatest_le N, fun x hx ↦ ?_⟩
  have hN : (Finset.range N).Nonempty :=
    Finset.nonempty_range_iff.2 fun hN ↦ hx (by simp [hN])
  obtain ⟨m, hm, hmφ⟩ := Finset.exists_mem_eq_sup _ hN (f · x)
  exact (Nat.findGreatest_spec (P := fun m ↦ m < N ∧ f m x = (Finset.range N).sup (f · x))
    (Finset.mem_range.1 hm).le ⟨Finset.mem_range.1 hm, hmφ.symm⟩).2

end TauCeti
