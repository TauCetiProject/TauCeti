/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.CrossedCocycle.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Nonabelian.Basic

/-!
# Continuous crossed cocycles and nonabelian first cohomology

Let a topological group `Γ` act on a topological group `H` through `α : Γ →* MulAut H`, and
suppose this action is also recorded as a `MulDistribMulAction Γ H` agreeing with `α`. The
cocycles of `TauCeti.NonabelianH1.Cocycle Γ H` are exactly the continuous crossed cocycles
`TauCeti.CrossedCocycle α`, and under this identification the cohomology relation of
`TauCeti.NonabelianH1` is gauge equivalence: `f ≈ f'` exactly when `f'` is the gauge of `f` by some
`h : H`. The cohomologous cocycle `g ↦ a⁻¹ * f g * g • a` of `TauCeti.NonabelianH1` is the gauge
by `a⁻¹`. Hence `TauCeti.NonabelianH1 Γ H` is the set of gauge orbits of continuous crossed
cocycles.

When `Γ` is discrete every crossed cocycle is continuous, whatever the topology on `H`, so all
crossed cocycles are cocycles of `TauCeti.NonabelianH1`.

## Main definitions

* `TauCeti.CrossedCocycle.continuousNonabelianCocycleEquiv`: continuous crossed cocycles are the
  cocycles of `TauCeti.NonabelianH1`.
* `TauCeti.CrossedCocycle.nonabelianCocycleEquiv`: crossed cocycles of a discrete group are the
  cocycles of `TauCeti.NonabelianH1`.

## Main results

* `TauCeti.CrossedCocycle.continuousNonabelianCocycleEquiv_equiv_iff` and
  `TauCeti.CrossedCocycle.nonabelianCocycleEquiv_equiv_iff`: the cohomology relation corresponds
  to gauge equivalence; with `TauCeti.NonabelianH1.mk_eq_mk_iff`, two crossed cocycles have the
  same class in `TauCeti.NonabelianH1 Γ H` exactly when they are gauge equivalent.
-/

public section

namespace TauCeti

namespace CrossedCocycle

variable {Γ H : Type*} [Group Γ] [Group H] [TopologicalSpace Γ] [TopologicalSpace H]
  [MulDistribMulAction Γ H] {α : Γ →* MulAut H} (hα : ∀ γ x, α γ x = γ • x)

/-- Continuous crossed cocycles of `Γ` for `α` are the cocycles of `TauCeti.NonabelianH1` for an
action `•` agreeing with `α`. -/
def continuousNonabelianCocycleEquiv :
    {c : CrossedCocycle α // Continuous c} ≃ NonabelianH1.Cocycle Γ H where
  toFun c := ⟨c.val, c.property, fun γ δ ↦ by rw [c.val.apply_mul, hα]⟩
  invFun f := ⟨f.toCrossedCocycle hα, by simpa using f.continuous⟩
  left_inv c := Subtype.ext <| ext fun _ ↦ by simp
  right_inv f := NonabelianH1.Cocycle.ext fun _ ↦ by simp

@[simp]
theorem continuousNonabelianCocycleEquiv_apply (c : {c : CrossedCocycle α // Continuous c})
    (γ : Γ) : continuousNonabelianCocycleEquiv hα c γ = c.val γ :=
  (rfl)

@[simp]
theorem coe_continuousNonabelianCocycleEquiv_symm_apply (f : NonabelianH1.Cocycle Γ H) :
    ((continuousNonabelianCocycleEquiv hα).symm f : CrossedCocycle α) = f.toCrossedCocycle hα :=
  (rfl)

/-- The cohomology relation of `TauCeti.NonabelianH1` is gauge equivalence of continuous crossed
cocycles. -/
theorem continuousNonabelianCocycleEquiv_equiv_iff
    {c c' : {c : CrossedCocycle α // Continuous c}} :
    continuousNonabelianCocycleEquiv hα c ≈ continuousNonabelianCocycleEquiv hα c' ↔
      ∃ h : H, h • c.val = c'.val := by
  rw [NonabelianH1.Cocycle.equiv_iff]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a⁻¹, ext fun γ ↦ by simpa [hα] using (ha γ).symm⟩
  · rintro ⟨h, hc⟩
    exact ⟨h⁻¹, fun γ ↦ by simp [← hc, hα]⟩

variable [DiscreteTopology Γ]

/-- Crossed cocycles of a discrete group `Γ` for `α` are the cocycles of `TauCeti.NonabelianH1`
for an action `•` agreeing with `α`: continuity is automatic. -/
def nonabelianCocycleEquiv : CrossedCocycle α ≃ NonabelianH1.Cocycle Γ H :=
  (Equiv.subtypeUnivEquiv fun _ ↦ continuous_of_discreteTopology).symm.trans
    (continuousNonabelianCocycleEquiv hα)

@[simp]
theorem nonabelianCocycleEquiv_apply (c : CrossedCocycle α) (γ : Γ) :
    nonabelianCocycleEquiv hα c γ = c γ :=
  (rfl)

@[simp]
theorem nonabelianCocycleEquiv_symm_apply (f : NonabelianH1.Cocycle Γ H) :
    (nonabelianCocycleEquiv hα).symm f = f.toCrossedCocycle hα :=
  (rfl)

/-- The cohomology relation of `TauCeti.NonabelianH1` is gauge equivalence of crossed
cocycles. -/
theorem nonabelianCocycleEquiv_equiv_iff {c c' : CrossedCocycle α} :
    nonabelianCocycleEquiv hα c ≈ nonabelianCocycleEquiv hα c' ↔ ∃ h : H, h • c = c' :=
  continuousNonabelianCocycleEquiv_equiv_iff hα

end CrossedCocycle

end TauCeti
