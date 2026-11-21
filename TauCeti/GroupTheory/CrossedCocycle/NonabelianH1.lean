/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.CrossedCocycle.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Nonabelian.Basic

/-!
# Crossed cocycles of a discrete group and nonabelian first cohomology

Let a group `Γ` act on a group `H` through `α : Γ →* MulAut H`, and suppose this action is also
recorded as a `MulDistribMulAction Γ H` agreeing with `α`. When `Γ` is discrete, the continuity
condition in `TauCeti.NonabelianH1.Cocycle Γ H` is automatic, whatever the topology on `H`, so its
cocycles are exactly the crossed cocycles `TauCeti.CrossedCocycle α`. Under this identification
the cohomology relation of `TauCeti.NonabelianH1` is gauge equivalence: `f ≈ f'` exactly when
`f'` is the gauge of `f` by some `h : H`. The cohomologous cocycle `g ↦ a⁻¹ * f g * g • a` of
`TauCeti.NonabelianH1` is the gauge by `a⁻¹`. Hence `TauCeti.NonabelianH1 Γ H` is the set of
gauge orbits of crossed cocycles.

## Main definitions

* `TauCeti.CrossedCocycle.nonabelianCocycleEquiv`: crossed cocycles of a discrete group are the
  cocycles of `TauCeti.NonabelianH1`.

## Main results

* `TauCeti.CrossedCocycle.nonabelianCocycleEquiv_equiv_iff`: the cohomology relation corresponds
  to gauge equivalence.
* `TauCeti.CrossedCocycle.nonabelianH1_mk_eq_mk_iff`: two crossed cocycles have the same class in
  `TauCeti.NonabelianH1 Γ H` exactly when they are gauge equivalent.
-/

public section

namespace TauCeti

namespace CrossedCocycle

variable {Γ H : Type*} [Group Γ] [Group H] [TopologicalSpace Γ] [DiscreteTopology Γ]
  [TopologicalSpace H] [MulDistribMulAction Γ H] {α : Γ →* MulAut H}
  (hα : ∀ γ x, α γ x = γ • x)

/-- Crossed cocycles of a discrete group `Γ` for `α` are the cocycles of `TauCeti.NonabelianH1`
for an action `•` agreeing with `α`. -/
def nonabelianCocycleEquiv : CrossedCocycle α ≃ NonabelianH1.Cocycle Γ H where
  toFun c := ⟨c, continuous_of_discreteTopology, fun γ δ ↦ by rw [c.apply_mul, hα]⟩
  invFun f := ⟨f, fun γ δ ↦ by rw [f.apply_mul, hα]⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem nonabelianCocycleEquiv_apply (c : CrossedCocycle α) (γ : Γ) :
    nonabelianCocycleEquiv hα c γ = c γ :=
  (rfl)

@[simp]
theorem nonabelianCocycleEquiv_symm_apply (f : NonabelianH1.Cocycle Γ H) (γ : Γ) :
    (nonabelianCocycleEquiv hα).symm f γ = f γ :=
  (rfl)

/-- The cohomology relation of `TauCeti.NonabelianH1` is gauge equivalence of crossed
cocycles. -/
theorem nonabelianCocycleEquiv_equiv_iff {c c' : CrossedCocycle α} :
    nonabelianCocycleEquiv hα c ≈ nonabelianCocycleEquiv hα c' ↔ ∃ h : H, h • c = c' := by
  rw [NonabelianH1.Cocycle.equiv_iff]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a⁻¹, ext fun γ ↦ by simpa [hα] using (ha γ).symm⟩
  · rintro ⟨h, rfl⟩
    exact ⟨h⁻¹, fun γ ↦ by simp [hα]⟩

/-- Two crossed cocycles have the same class in `TauCeti.NonabelianH1 Γ H` exactly when they are
gauge equivalent. -/
theorem nonabelianH1_mk_eq_mk_iff {c c' : CrossedCocycle α} :
    NonabelianH1.mk (nonabelianCocycleEquiv hα c) = NonabelianH1.mk (nonabelianCocycleEquiv hα c')
      ↔ ∃ h : H, h • c = c' := by
  rw [NonabelianH1.mk_eq_mk_iff, ← NonabelianH1.Cocycle.equiv_iff,
    nonabelianCocycleEquiv_equiv_iff]

end CrossedCocycle

end TauCeti
