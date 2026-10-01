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
public import TauCeti.Topology.Instances.AddCircle.Defs

/-!
# Mapping tori and fibering over the circle

For a homeomorphism `φ : F ≃ₜ F`, the mapping torus identifies `(φ x, t + 1)` with
`(x, t)`. The quotient model below is deliberately topological: manifold charts and
the local-triviality theorem are separate geometric input. `MappingTorusPresentation`
stores the fibre and monodromy, while `FibersOverCircle` asserts that such a presentation
exists.

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

/-- The integer action translating the real coordinate and applying monodromy. -/
def vadd (φ : F ≃ₜ F) (n : ℤ) (p : F × ℝ) : F × ℝ :=
  ((φ ^ n) p.1, p.2 + n)

/-- The additive action whose orbits form the mapping torus. -/
@[instance_reducible]
def action (φ : F ≃ₜ F) : AddAction ℤ (F × ℝ) where
  vadd := vadd φ
  zero_vadd p := by
    -- Unfold the action field to expose the concrete `vadd` operation.
    change vadd φ 0 p = p
    dsimp [vadd]
    simp
  add_vadd m n p := by
    -- Unfold the action field to expose the concrete `vadd` operation.
    change vadd φ (m + n) p = vadd φ m (vadd φ n p)
    dsimp [vadd]
    apply Prod.ext
    · rw [zpow_add, Homeomorph.mul_apply]
    · push_cast
      ring_nf

end MappingTorus

/-- The topological mapping torus of a self-homeomorphism. -/
abbrev MappingTorus (φ : F ≃ₜ F) :=
  @AddAction.orbitRel.Quotient ℤ (F × ℝ) inferInstance (MappingTorus.action φ)

namespace MappingTorus

/-- The quotient map from the cylinder used to construct the mapping torus. -/
def mk (φ : F ≃ₜ F) (x : F) (t : ℝ) : MappingTorus φ :=
  @Quotient.mk'' (F × ℝ)
    (@AddAction.orbitRel ℤ (F × ℝ) inferInstance (MappingTorus.action φ)) (x, t)

/-- The quotient identifies (φ ^ n) x at height t + n with x at height t. -/
@[simp]
theorem mk_vadd (φ : F ≃ₜ F) (n : ℤ) (x : F) (t : ℝ) :
    mk φ ((φ ^ n) x) (t + n) = mk φ x t := by
  let _ : AddAction ℤ (F × ℝ) := MappingTorus.action φ
  unfold mk
  apply Quotient.sound
  exact AddAction.orbitRel_apply.mpr ⟨n, rfl⟩

/-- Two cylinder points represent the same mapping-torus point exactly when they differ
by an integer translate in the monodromy orbit and the corresponding height translate. -/
theorem mk_eq_iff (φ : F ≃ₜ F) {x y : F} {t s : ℝ} :
    mk φ x t = mk φ y s ↔ ∃ n : ℤ, (φ ^ n) y = x ∧ s + n = t := by
  let _ : AddAction ℤ (F × ℝ) := MappingTorus.action φ
  unfold mk
  rw [Quotient.eq, AddAction.orbitRel_apply, AddAction.mem_orbit_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_, ?_⟩
    · exact congrArg Prod.fst hn
    · exact congrArg Prod.snd hn
  · rintro ⟨n, hxy, hts⟩
    exact ⟨n, Prod.ext hxy hts⟩

/-- The canonical projection of a mapping torus to the circle. -/
def proj (φ : F ≃ₜ F) : MappingTorus φ → UnitAddCircle :=
  letI := MappingTorus.action φ
  Quotient.lift (fun z : F × ℝ ↦ (z.2 : UnitAddCircle)) (by
    intro a b h
    obtain ⟨n, rfl⟩ := AddAction.mem_orbit_iff.mp h
    -- The action orbit witness must be unfolded to expose its real coordinate.
    change ((b.2 + (n : ℝ) : ℝ) : UnitAddCircle) = (b.2 : UnitAddCircle)
    rw [AddCircle.coe_add]
    simp)

@[simp]
theorem proj_mk (φ : F ≃ₜ F) (x : F) (t : ℝ) :
    proj φ (mk φ x t) = (t : UnitAddCircle) := by
  unfold proj mk
  apply Quotient.lift_mk

/-- The canonical projection from a mapping torus to the additive circle is continuous. -/
theorem continuous_proj (φ : F ≃ₜ F) : Continuous (proj φ) := by
  unfold proj
  let _ : AddAction ℤ (F × ℝ) := MappingTorus.action φ
  simpa using
    ((isQuotientMap_quotient_mk' (s := AddAction.orbitRel ℤ (F × ℝ))).continuous_iff.mpr
      ((AddCircle.continuous_mk' (1 : ℝ)).comp continuous_snd))

/-- The projection from the mapping torus of a nonempty space onto the circle is surjective. -/
theorem proj_surjective [Nonempty F] (φ : F ≃ₜ F) : Function.Surjective (proj φ) := by
  intro θ
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective θ
  exact ⟨mk φ (Classical.arbitrary F) t, proj_mk φ _ t⟩

end MappingTorus

/-- A mapping-torus presentation of a topological space, including its fibre and monodromy. -/
structure MappingTorusPresentation (M : Type u) [TopologicalSpace M] where
  /-- The fibre type. -/
  Fiber : Type u
  /-- The fibre is nonempty. -/
  nonemptyFiber : Nonempty Fiber
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
def MappingTorus.presentation [Nonempty F] (φ : F ≃ₜ F) :
    MappingTorusPresentation (MappingTorus φ) where
  Fiber := F
  nonemptyFiber := inferInstance
  fiberTopology := inferInstance
  monodromy := φ
  equivalence := Homeomorph.refl _

/-- The mapping torus carries its canonical fibering-over-the-circle presentation. -/
theorem fibersOverCircle_mappingTorus [Nonempty F] (φ : F ≃ₜ F) :
    FibersOverCircle (MappingTorus φ) :=
  ⟨MappingTorus.presentation φ⟩

/-- A homeomorphism transports a fibering-over-the-circle presentation. -/
theorem _root_.Homeomorph.fibersOverCircle {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    (h : M ≃ₜ N) (hN : FibersOverCircle N) : FibersOverCircle M := by
  obtain ⟨p⟩ := hN
  let _ := p.fiberTopology
  let e : N ≃ₜ @MappingTorus p.Fiber p.fiberTopology p.monodromy := p.equivalence
  refine ⟨{ Fiber := p.Fiber
            nonemptyFiber := p.nonemptyFiber
            fiberTopology := p.fiberTopology
            monodromy := p.monodromy
            equivalence := ?_ }⟩
  exact h.trans e

/-- A space that fibers over the circle is infinite, since it maps onto the circle. -/
theorem FibersOverCircle.infinite {M : Type u} [TopologicalSpace M] (h : FibersOverCircle M) :
    Infinite M := by
  obtain ⟨p⟩ := h
  let _ := p.fiberTopology
  have := p.nonemptyFiber
  exact .of_surjective _ ((MappingTorus.proj_surjective p.monodromy).comp p.equivalence.surjective)

end TauCeti
