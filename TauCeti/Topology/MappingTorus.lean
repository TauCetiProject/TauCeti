/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Instances.AddCircle.Real
public import Mathlib.Topology.Constructions
public import Mathlib.GroupTheory.GroupAction.Defs

/-!
# Mapping tori and fibering over the circle

For a homeomorphism `φ : F ≃ₜ F`, the mapping torus identifies `(φ x, t + 1)` with
`(x, t)`. The quotient model below is deliberately topological: manifold charts and
the local-triviality theorem are separate geometric input. `FibersOverCircle` records
the data needed to state that a space is a mapping torus, while retaining the fibre and
monodromy rather than hiding them in an existential proposition.

The quotient projection to `UnitAddCircle` records the circle coordinate of each orbit.

The construction follows the standard mapping-torus model, e.g. Hatcher,
*Algebraic Topology*, Section 2.2.
-/

universe u

public section

open Topology

namespace TauCeti

variable {F : Type*} [TopologicalSpace F]

namespace MappingTorus

private theorem zpow_apply_add (φ : F ≃ₜ F) (m n : ℤ) (x : F) :
    (φ ^ (m + n)) x = (φ ^ m) ((φ ^ n) x) := by
  rw [zpow_add, Homeomorph.mul_apply]

/-- The integer action translating the real coordinate and applying monodromy. -/
def vadd (φ : F ≃ₜ F) (n : ℤ) (p : F × ℝ) : F × ℝ :=
  ((φ ^ n) p.1, p.2 + n)

/-- The additive action whose orbits form the mapping torus. -/
@[instance_reducible]
def action (φ : F ≃ₜ F) : AddAction ℤ (F × ℝ) where
  vadd := vadd φ
  zero_vadd p := by
    change vadd φ 0 p = p
    dsimp [vadd]
    simp
  add_vadd m n p := by
    change vadd φ (m + n) p = vadd φ m (vadd φ n p)
    dsimp [vadd]
    apply Prod.ext
    · rw [zpow_add, Homeomorph.mul_apply]
    · push_cast
      ring_nf

/-- The setoid of orbits of the integer monodromy action. -/
def quotientSetoid (φ : F ≃ₜ F) : Setoid (F × ℝ) :=
  @AddAction.orbitRel ℤ (F × ℝ) inferInstance (action φ)

end MappingTorus

/-- The topological mapping torus of a self-homeomorphism. -/
abbrev MappingTorus (φ : F ≃ₜ F) := Quotient (MappingTorus.quotientSetoid φ)

namespace MappingTorus

/-- The quotient map from the cylinder used to construct the mapping torus. -/
def mk (φ : F ≃ₜ F) (x : F) (t : ℝ) : MappingTorus φ :=
  @Quotient.mk' (F × ℝ) (MappingTorus.quotientSetoid φ) (x, t)

@[simp]
theorem mk_eq (φ : F ≃ₜ F) (x y : F) (s t : ℝ) :
    mk φ x s = mk φ y t ↔
      @AddAction.orbitRel ℤ (F × ℝ) inferInstance (MappingTorus.action φ) (x, s) (y, t) := by
  exact Quotient.eq'

/-- Shifting along the integer action does not change a mapping-torus point. -/
@[simp]
theorem mk_add_int (φ : F ≃ₜ F) (x : F) (t : ℝ) (n : ℤ) :
    mk φ ((φ ^ n) x) (t + n) = mk φ x t := by
  let _ : AddAction ℤ (F × ℝ) := MappingTorus.action φ
  change (⟦((φ ^ n) x, t + n)⟧ : Quotient (MappingTorus.quotientSetoid φ)) = ⟦(x, t)⟧
  apply Quotient.sound
  exact ⟨n, rfl⟩

/-- The canonical projection of a mapping torus to the circle. -/
def proj (φ : F ≃ₜ F) : MappingTorus φ → UnitAddCircle :=
  letI := MappingTorus.action φ
  Quotient.lift (fun z : F × ℝ ↦ (z.2 : UnitAddCircle)) (by
    intro a b h
    obtain ⟨n, rfl⟩ := (show a ∈ AddAction.orbit ℤ b from h)
    change ((b.2 + (n : ℝ) : ℝ) : UnitAddCircle) = (b.2 : UnitAddCircle)
    rw [AddCircle.coe_add]
    simp)

@[simp]
theorem proj_mk (φ : F ≃ₜ F) (x : F) (t : ℝ) :
    proj φ (mk φ x t) = (t : UnitAddCircle) := by
  unfold proj mk
  apply Quotient.lift_mk

/-- The quotient map from the cylinder into the mapping torus is continuous. -/
theorem continuous_mk (φ : F ≃ₜ F) :
    Continuous (fun p : F × ℝ ↦ mk φ p.1 p.2) := by
  change Continuous (@Quotient.mk' (F × ℝ) (MappingTorus.quotientSetoid φ))
  exact isQuotientMap_quotient_mk'.continuous

/-- The canonical projection from a mapping torus to the additive circle is continuous. -/
theorem continuous_proj (φ : F ≃ₜ F) : Continuous (proj φ) := by
  unfold proj
  let _ : AddAction ℤ (F × ℝ) := MappingTorus.action φ
  simpa using
    ((isQuotientMap_quotient_mk' (s := MappingTorus.quotientSetoid φ)).continuous_iff.mpr
      ((AddCircle.continuous_mk' (1 : ℝ)).comp continuous_snd))

end MappingTorus

/-- A mapping-torus presentation of a topological space, including its fibre and monodromy. -/
structure MappingTorusPresentation (M : Type u) [TopologicalSpace M] where
  /-- The fibre type. -/
  Fiber : Type u
  /-- The topology carried by the fibre. -/
  fiberTopology : TopologicalSpace Fiber
  /-- The monodromy homeomorphism around the circle. -/
  monodromy : @Homeomorph Fiber Fiber fiberTopology fiberTopology
  /-- A homeomorphism from the presented space to the mapping torus. -/
  equivalence : @Homeomorph M (@MappingTorus Fiber fiberTopology monodromy)
      (by infer_instance) instTopologicalSpaceQuotient

/-- A space fibres over the circle when it is homeomorphic to a mapping torus. -/
def FibersOverCircle (M : Type u) [TopologicalSpace M] : Prop :=
  Nonempty (MappingTorusPresentation M)

/-- The mapping torus has its canonical presentation. -/
def MappingTorus.presentation (φ : F ≃ₜ F) :
    MappingTorusPresentation (MappingTorus φ) where
  Fiber := F
  fiberTopology := inferInstance
  monodromy := φ
  equivalence := Homeomorph.refl _

/-- The mapping torus carries its canonical fibering-over-the-circle presentation. -/
theorem fibersOverCircle_mappingTorus (φ : F ≃ₜ F) :
    FibersOverCircle (MappingTorus φ) :=
  ⟨MappingTorus.presentation φ⟩

/-- A homeomorphism transports a fibering-over-the-circle presentation. -/
theorem FibersOverCircle.ofHomeomorph {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    (h : M ≃ₜ N) (hN : FibersOverCircle N) : FibersOverCircle M := by
  obtain ⟨p⟩ := hN
  let _ := p.fiberTopology
  let e : N ≃ₜ @MappingTorus p.Fiber p.fiberTopology p.monodromy := p.equivalence
  refine ⟨{ Fiber := p.Fiber
            fiberTopology := p.fiberTopology
            monodromy := p.monodromy
            equivalence := ?_ }⟩
  exact h.trans e

end TauCeti
