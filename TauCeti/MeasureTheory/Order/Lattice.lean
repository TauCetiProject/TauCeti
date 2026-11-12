/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.Order.Lattice

/-!
# Measurability of finite suprema and of a maximizing index

The pointwise supremum `x ↦ s.sup (f · x)` of finitely many measurable functions is measurable
(`TauCeti.measurable_finsetSup`). This is the `Finset.sup` form of Mathlib's
`Finset.measurable_sup''`, which needs a nonempty index set. For a linear order, the last index
`m < N` attaining `max_{m < N} fₘ(x)` can be chosen measurably in `x`
(`TauCeti.exists_measurable_finsetSup_eq`).
-/

public section

namespace TauCeti

variable {δ α ι : Type*} [MeasurableSpace δ] [MeasurableSpace α]

/-- The pointwise supremum `x ↦ s.sup (f · x)` of finitely many measurable functions is
measurable. -/
theorem measurable_finsetSup [SemilatticeSup α] [OrderBot α] [MeasurableSup₂ α] (s : Finset ι)
    {f : ι → δ → α} (hf : ∀ i ∈ s, Measurable (f i)) : Measurable fun x ↦ s.sup (f · x) := by
  convert Finset.sup_induction (p := Measurable) (s := s) (f := f) measurable_const
    (fun _ h₁ _ h₂ ↦ h₁.sup h₂) hf using 1
  ext x
  simp

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
      (measurableSet_eq_fun (hf m) (measurable_finsetSup _ fun m _ ↦ hf m)),
    fun x ↦ Nat.findGreatest_le N, fun x hx ↦ ?_⟩
  have hN : (Finset.range N).Nonempty :=
    Finset.nonempty_range_iff.2 fun hN ↦ hx (by simp [hN])
  obtain ⟨m, hm, hmφ⟩ := Finset.exists_mem_eq_sup _ hN (f · x)
  exact (Nat.findGreatest_spec (P := fun m ↦ m < N ∧ f m x = (Finset.range N).sup (f · x))
    (Finset.mem_range.1 hm).le ⟨Finset.mem_range.1 hm, hmφ.symm⟩).2

end TauCeti
