/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.Topology.Algebra.Group.Defs
public import TauCeti.GroupTheory.CrossedCocycle.Basic

/-!
# Continuity of crossed cocycles

The continuous crossed cocycles are the subtype cut out by continuity of the underlying map.
Restriction along a continuous homomorphism and continuous equivariant change of coefficients
preserve this subtype. When every action orbit map on the coefficient group is continuous,
the subtype is stable under gauge and inherits the gauge action.
-/

public section

namespace TauCeti.CrossedCocycle

variable {Γ H : Type*} [Monoid Γ] [Group H] [TopologicalSpace Γ] [TopologicalSpace H]
  {α : Γ →* MulAut H} {c : CrossedCocycle α}

/-- Restriction along a continuous homomorphism preserves continuity. -/
theorem continuous_comap {Δ : Type*} [Monoid Δ] [TopologicalSpace Δ] {f : Δ →* Γ}
    (hc : Continuous c) (hf : Continuous f) : Continuous (c.comap f) := by
  convert hc.comp hf using 1
  exact funext (comap_apply c f)

/-- Continuous equivariant change of coefficients preserves continuity. -/
theorem continuous_map {K : Type*} [Group K] [TopologicalSpace K] {β : Γ →* MulAut K}
    {u : H →* K} (hu : ∀ γ x, u (α γ x) = β γ (u x))
    (hc : Continuous c) (hu' : Continuous u) : Continuous (c.map u hu) := by
  convert hu'.comp hc using 1
  exact funext (map_apply u hu c)

section Gauge

variable [IsTopologicalGroup H]

/-- Gauge by `h` preserves continuity when the action orbit map of `h` is continuous. -/
theorem continuous_smul {h : H} (hc : Continuous c) (hh : Continuous fun γ ↦ α γ h) :
    Continuous (h • c) := by
  rw [funext (smul_apply h c)]
  exact (hc.const_mul h).mul hh.inv

/-- Continuous crossed cocycles as a subaction for gauge, with the inherited gauge action. -/
def continuousSubMulAction (α : Γ →* MulAut H)
    (hα : ∀ h : H, Continuous fun γ ↦ α γ h) : SubMulAction H (CrossedCocycle α) where
  carrier := {c | Continuous c}
  smul_mem' h {_} hc := continuous_smul hc (hα h)

@[simp]
theorem mem_continuousSubMulAction (hα : ∀ h : H, Continuous fun γ ↦ α γ h) :
    c ∈ continuousSubMulAction α hα ↔ Continuous c :=
  Iff.rfl

end Gauge

end TauCeti.CrossedCocycle
