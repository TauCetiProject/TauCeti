/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.Form

/-!
# Independence of the Kostant form from toral lattice generators

For a commuting Cartan family `h`, the Kostant form contains the binomial coefficients of every
vector in its integer span. Consequently replacing `h` by any other family with the same integer
span leaves the integral form unchanged. In particular, choosing a different integer basis of
the cocharacter lattice does not change the form. This uses the full toral lattice, not just the
span of the simple coroots, and does not require a splitting off of central toral directions.

The argument uses the binomial-ring Chu–Vandermonde identity and the integral negation formula.
No root relations or integral Poincaré–Birkhoff–Witt theorem are required.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.ringChoose_mem_kostantForm_of_mem_span`:
  binomial coefficients in the entire toral lattice belong to the form.
* `TauCeti.UniversalEnvelopingAlgebra.kostantForm_eq_of_cartan_span_eq`:
  invariance under replacement of commuting toral lattice generators.
* `TauCeti.UniversalEnvelopingAlgebra.kostantForm_eq_of_cartan_basis`:
  independence of the chosen integer basis of a toral lattice.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, II.1, for the toral part of the
  integral enveloping algebra.
* B. Kostant, *Groups over Z*, in *Algebraic Groups and Discontinuous Subgroups* (1966),
  for the integral form.
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

open Set

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]
variable {ι κ κ' : Type*}

attribute [local instance] TauCeti.moduleNNRat
attribute [local instance 100] LieRing.ofAssociativeRing

/-- The Kostant form attached to a commuting Cartan family contains the binomial coefficients of
all integer linear combinations of that family. -/
theorem ringChoose_mem_kostantForm_of_mem_span (e : ι → L) (h : κ → L)
    (hcomm : ∀ i j, ⁅h i, h j⁆ = 0) {x : L}
    (hx : x ∈ Submodule.span ℤ (range h)) (n : ℕ) :
    Ring.choose (_root_.UniversalEnvelopingAlgebra.ι ℚ x) n ∈ kostantForm e h := by
  let f := (_root_.UniversalEnvelopingAlgebra.ι ℚ (L := L)).toLinearMap.restrictScalars ℤ
  have hf : f x ∈ Submodule.span ℤ (f '' range h) := by
    rw [← Submodule.map_span]
    exact Submodule.mem_map_of_mem hx
  apply Ring.choose_mem_of_mem_span (kostantForm e h) (s := f '' range h) ?_ ?_ hf n
  · rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩ _ ⟨_, ⟨j, rfl⟩, rfl⟩
    exact commute_of_lie_eq_zero (AlgHom.id ℚ _) (hcomm i j)
  · rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩ n
    exact ringChoose_mem_kostantForm e h i n

/-- Replacing a Cartan family by vectors in the integer span of a commuting Cartan family can
only shrink the Kostant integral form. -/
theorem kostantForm_le_of_cartan_span_le (e : ι → L) (h : κ → L) (h' : κ' → L)
    (hcomm : ∀ i j, ⁅h' i, h' j⁆ = 0)
    (hle : Submodule.span ℤ (range h) ≤ Submodule.span ℤ (range h')) :
    kostantForm e h ≤ kostantForm e h' := by
  rw [kostantForm_le_iff]
  exact ⟨dividedPower_mem_kostantForm e h', fun i n ↦
    ringChoose_mem_kostantForm_of_mem_span e h' hcomm
      (hle (Submodule.subset_span (mem_range_self i))) n⟩

/-- Two commuting Cartan families with the same integer span define the same Kostant integral
form, with the root-vector family held fixed. -/
theorem kostantForm_eq_of_cartan_span_eq (e : ι → L) (h : κ → L) (h' : κ' → L)
    (hcomm : ∀ i j, ⁅h i, h j⁆ = 0)
    (heq : Submodule.span ℤ (range h) = Submodule.span ℤ (range h')) :
    kostantForm e h = kostantForm e h' := by
  have hspan : ∀ x ∈ Submodule.span ℤ (range h),
      ∀ y ∈ Submodule.span ℤ (range h), ⁅x, y⁆ = 0 := by
    intro x hx y hy
    induction hx, hy using Submodule.span_induction₂ with
    | mem_mem x y hx hy =>
      obtain ⟨i, rfl⟩ := hx
      obtain ⟨j, rfl⟩ := hy
      exact hcomm i j
    | zero_left => simp
    | zero_right => simp
    | add_left _ _ _ _ _ _ ih₁ ih₂ => simp [add_lie, ih₁, ih₂]
    | add_right _ _ _ _ _ _ ih₁ ih₂ => simp [lie_add, ih₁, ih₂]
    | smul_left _ _ _ _ _ ih => simp [ih]
    | smul_right _ _ _ _ _ ih => simp [ih]
  have hcomm' : ∀ i j, ⁅h' i, h' j⁆ = 0 := fun i j ↦
    hspan _ (heq.ge (Submodule.subset_span (mem_range_self i)))
      _ (heq.ge (Submodule.subset_span (mem_range_self j)))
  exact le_antisymm (kostantForm_le_of_cartan_span_le e h h' hcomm' heq.le)
    (kostantForm_le_of_cartan_span_le e h' h hcomm heq.ge)

/-- The Kostant integral form is independent of the chosen integer basis of a commuting toral
lattice, including lattices with central toral directions and the zero lattice. -/
theorem kostantForm_eq_of_cartan_basis (e : ι → L) (Y : Submodule ℤ L)
    (hcomm : ∀ x ∈ Y, ∀ y ∈ Y, ⁅x, y⁆ = 0)
    (b : Module.Basis κ ℤ Y) (b' : Module.Basis κ' ℤ Y) :
    kostantForm e (fun i ↦ (b i : L)) = kostantForm e (fun i ↦ (b' i : L)) := by
  apply kostantForm_eq_of_cartan_span_eq e _ _
    (fun i j ↦ hcomm _ (b i).property _ (b j).property)
  simpa only [Submodule.map_span, ← Set.range_comp, Function.comp_def,
    Submodule.subtype_apply] using
    congrArg (Submodule.map Y.subtype) (b.span_eq.trans b'.span_eq.symm)

end TauCeti.UniversalEnvelopingAlgebra
