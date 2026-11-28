/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.Defs

/-!
# Maximal invariants

A function `M : α → β` is a *maximal invariant* of an action of `G` on `α` if it is invariant,
`M (g • x) = M x`, and separates orbits: `M x = M y` only when `y = g • x` for some `g`. This is
the reduction by invariance of testing theory: an invariant test is a function of a maximal
invariant (Ferguson, *Mathematical Statistics: A Decision Theoretic Approach*, §5.6).

Inverting a family of invariant tests gives an invariant confidence set; the duality of tests and
confidence sets used there is `TauCeti.hasConfidenceCoverage_iff_forall_hasTestLevel` in
`TauCeti.Statistics.Experiments.ConfidenceSets`.

## Main definitions

* `MulAction.IsMaximalInvariant G M`: `M` is invariant under `G` and separates `G`-orbits.

## Main results

* `MulAction.IsMaximalInvariant.factorsThrough_iff`: a function factors through a maximal
  invariant `M` (`Function.FactorsThrough`) if and only if it is invariant (Ferguson, §5.6, Thm 1).
* `MulAction.isMaximalInvariant_mk`: the projection to the orbit quotient is a maximal invariant.

The scale-group example of Ferguson, §5.6, Example 2 is in
`TauCeti.Statistics.Experiments.Invariance`.

The factorization theorem is adapted from `CKSD.invariant_iff_factors_through_maximal_invariant`
in lean-CKSD's `CKSD/Inference/InvariantTesting.lean`.

## References

* T. S. Ferguson, *Mathematical Statistics: A Decision Theoretic Approach*, Academic Press, 1967,
  §5.6, pp. 244–246.
-/

public section

namespace MulAction

variable {G α β γ : Type*}

/-- A function `M : α → β` is a **maximal invariant** of the action of `G` on `α` if it is
invariant under `G` and takes equal values only on points of the same orbit. -/
structure IsMaximalInvariant (G : Type*) [SMul G α] (M : α → β) : Prop where
  /-- A maximal invariant is invariant. -/
  apply_smul (g : G) (x : α) : M (g • x) = M x
  /-- A maximal invariant separates orbits. -/
  exists_smul_eq ⦃x y : α⦄ : M x = M y → ∃ g : G, g • x = y

section SMul

variable [SMul G α] {M : α → β}

/-- `M` is a maximal invariant if and only if `M x = M y` holds exactly when `y = g • x` for some
`g`. -/
theorem isMaximalInvariant_iff :
    IsMaximalInvariant G M ↔ ∀ x y, M x = M y ↔ ∃ g : G, g • x = y where
  mp h x y := ⟨(h.exists_smul_eq ·), by rintro ⟨g, rfl⟩; exact (h.apply_smul g x).symm⟩
  mpr h := ⟨fun g x ↦ ((h x (g • x)).2 ⟨g, rfl⟩).symm, fun x y ↦ (h x y).1⟩

/-- A maximal invariant takes equal values exactly on points of the same orbit. -/
theorem IsMaximalInvariant.apply_eq_apply_iff (hM : IsMaximalInvariant G M) {x y : α} :
    M x = M y ↔ ∃ g : G, g • x = y :=
  isMaximalInvariant_iff.1 hM x y

/-- A function factors through a maximal invariant `M` if and only if it is invariant. -/
theorem IsMaximalInvariant.factorsThrough_iff (hM : IsMaximalInvariant G M) (f : α → γ) :
    f.FactorsThrough M ↔ ∀ (g : G) (x : α), f (g • x) = f x where
  mp hf g x := hf (hM.apply_smul g x)
  mpr hf x y hxy := by
    obtain ⟨g, rfl⟩ := hM.exists_smul_eq hxy
    exact (hf g x).symm

end SMul

/-- The projection of `α` onto its orbit quotient is a maximal invariant. -/
theorem isMaximalInvariant_mk [Group G] [MulAction G α] :
    IsMaximalInvariant G (Quotient.mk (orbitRel G α)) where
  apply_smul g x := Quotient.sound (mem_orbit x g)
  exists_smul_eq _ _ hxy := mem_orbit_iff.1 (orbitRel_apply.1 (Quotient.exact hxy.symm))

end MulAction
