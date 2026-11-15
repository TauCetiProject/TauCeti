/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Torus.Basic

/-!
# Root weights in the lattice of representation weights

A nonzero root operator on a lattice with a weight basis has a nonzero matrix entry. If its
root weight is `α`, that entry joins a weight `μ` to the weight `μ + α`. Consequently `α` is a
difference of two representation weights, and belongs to their integral span. This is the
lattice inclusion needed to regard roots as characters of the torus of a represented group.

The results do not require faithfulness of the whole representation: nonvanishing of the
particular root operator suffices. A rational spanning hypothesis on the lattice lets one
check nonvanishing in the ambient representation instead.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 27.
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]
variable {ι κ η : Type*} {V : Type*} [AddCommGroup V] [Module ℚ V]
variable (e : ι → L) (h : κ → L)
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] End ℚ V)
variable (M : AddSubgroup V)
variable (hM : ∀ u ∈ kostantForm e h, ∀ v ∈ M, ρ u v ∈ M)
variable (b : Basis η ℤ M) (wt : η → κ → ℤ)

/-- A nonzero root operator has a nonzero weight-basis entry, joining a weight `μ` to `μ + α`.
In particular its root weight is a difference of representation weights. -/
theorem exists_weight_eq_add_of_kostantRootOperator_ne_zero
    (hwt : ∀ x, IsCartanWeightVector h ρ (wt x) (b x : V)) (i : ι) {α : κ → ℤ}
    (hα : ∀ j, ⁅h j, e i⁆ = (α j : ℚ) • e i)
    (hne : kostantRootOperator e h ρ M hM i ≠ 0) :
    ∃ x y, b.repr (kostantRootOperator e h ρ M hM i (b x)) y ≠ 0 ∧
      wt y = wt x + α := by
  classical
  have hx : ∃ x, kostantRootOperator e h ρ M hM i (b x) ≠ 0 := by
    by_contra! hx
    exact hne (b.ext fun x => by simpa using hx x)
  obtain ⟨x, hx⟩ := hx
  have hy : ∃ y, b.repr (kostantRootOperator e h ρ M hM i (b x)) y ≠ 0 := by
    by_contra! hy
    apply hx
    apply b.repr.injective
    ext y
    simpa using hy y
  obtain ⟨y, hy⟩ := hy
  refine ⟨x, y, hy, ?_⟩
  by_contra hneWeight
  exact hy (repr_eq_zero_of_isCartanWeightVector h ρ M b wt hwt
    (isCartanWeightVector_coe_kostantRootOperator e h ρ M hM i hα (hwt x)) hneWeight)

include hM in
/-- The weight of a nonzero represented root vector belongs to the integral span of the
weights of a rationally spanning stable lattice. No finite-generation hypothesis is needed. -/
theorem rootWeight_mem_span_of_representation_ne_zero
    (hspan : Submodule.span ℚ (M : Set V) = ⊤)
    (hwt : ∀ x, IsCartanWeightVector h ρ (wt x) (b x : V)) (i : ι) {α : κ → ℤ}
    (hα : ∀ j, ⁅h j, e i⁆ = (α j : ℚ) • e i)
    (hne : ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)) ≠ 0) :
    α ∈ Submodule.span ℤ (Set.range wt) := by
  have hop : kostantRootOperator e h ρ M hM i ≠ 0 := by
    intro hz
    apply hne
    refine (Submodule.linearMap_eq_zero_iff_of_span_eq_top _ hspan).mpr fun m => ?_
    have hm := congrArg (fun f : End ℤ M => (f ⟨m, m.property⟩ : V)) hz
    simpa only [coe_kostantRootOperator_apply, LinearMap.zero_apply, ZeroMemClass.coe_zero] using hm
  obtain ⟨x, y, _, hxy⟩ :=
    exists_weight_eq_add_of_kostantRootOperator_ne_zero e h ρ M hM b wt hwt i hα hop
  have hdiff : α = wt y - wt x := by rw [hxy]; abel
  rw [hdiff]
  exact Submodule.sub_mem _ (Submodule.subset_span ⟨y, rfl⟩)
    (Submodule.subset_span ⟨x, rfl⟩)

end TauCeti.UniversalEnvelopingAlgebra
