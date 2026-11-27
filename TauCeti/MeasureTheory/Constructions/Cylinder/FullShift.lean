/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.SymbolicDynamics.Basic
public import Mathlib.MeasureTheory.Constructions.Cylinders
public import Mathlib.Probability.ProductMeasure

/-!
# Cylinder sets of the full shift as measurable sets

Mathlib's cylinder set `SymbolicDynamics.FullShift.cylinder U x = {y : y = x on U}`, for a finite
set `U` of indices, is the cylinder event `MeasureTheory.cylinder U {x|_U}` of a single pattern.
This file records that cylinder sets are measurable when the alphabet has measurable singletons,
that the intersection of two cylinder sets is a cylinder set on the union of their supports, and
that the cylinder sets, and those of a fixed configuration, form π-systems. Under a product of
probability measures `μ i` on the coordinates, the cylinder set of `x` on `U` has measure
`∏ i ∈ U, μ i {x i}`; for a constant family `μ i = p` this is the Bernoulli measure of a cylinder.

## Main results

* `SymbolicDynamics.FullShift.cylinder_eq_cylinder_singleton`
* `SymbolicDynamics.FullShift.measurableSet_cylinder`
* `SymbolicDynamics.FullShift.cylinder_inter_cylinder`
* `SymbolicDynamics.FullShift.isPiSystem_cylinder`
* `SymbolicDynamics.FullShift.isPiSystem_cylinder_fixed`
* `SymbolicDynamics.FullShift.infinitePi_cylinder`
-/

public section

open MeasureTheory Set

namespace SymbolicDynamics.FullShift

variable {G A : Type*}

/-- A cylinder set is the cylinder event, in the sense of `MeasureTheory.cylinder`, of the single
pattern `x|_U`. -/
theorem cylinder_eq_cylinder_singleton (U : Finset G) (x : G → A) :
    FullShift.cylinder U x = MeasureTheory.cylinder (α := fun _ : G => A) U {U.restrict x} := by
  ext y
  simp [FullShift.mem_cylinder, funext_iff]

/-- Cylinder sets are measurable. -/
theorem measurableSet_cylinder [MeasurableSpace A] [MeasurableSingletonClass A] (U : Finset G)
    (x : G → A) : MeasurableSet (FullShift.cylinder U x) := by
  rw [cylinder_eq_cylinder_singleton]
  exact MeasurableSet.cylinder _ (measurableSet_singleton _)

/-- The intersection of two cylinder sets is the cylinder set, on the union of their supports, of
any configuration that lies in both. -/
theorem cylinder_inter_cylinder [DecidableEq G] {U V : Finset G} {x y z : G → A}
    (hzx : ∀ i ∈ U, z i = x i) (hzy : ∀ i ∈ V, z i = y i) :
    FullShift.cylinder U x ∩ FullShift.cylinder V y = FullShift.cylinder (U ∪ V) z := by
  ext w
  simp only [mem_inter_iff, FullShift.mem_cylinder, Finset.mem_union]
  constructor
  · rintro ⟨hwx, hwy⟩ j (hj | hj)
    · rw [hwx j hj, hzx j hj]
    · rw [hwy j hj, hzy j hj]
  · intro hw
    exact ⟨fun j hj => (hw j (Or.inl hj)).trans (hzx j hj),
      fun j hj => (hw j (Or.inr hj)).trans (hzy j hj)⟩

/-- The cylinder set of a configuration on a union is the intersection of its cylinder sets. -/
theorem cylinder_union [DecidableEq G] (U V : Finset G) (x : G → A) :
    FullShift.cylinder (U ∪ V) x = FullShift.cylinder U x ∩ FullShift.cylinder V x :=
  (cylinder_inter_cylinder (fun _ _ => rfl) fun _ _ => rfl).symm

/-- The cylinder sets form a π-system. -/
theorem isPiSystem_cylinder :
    IsPiSystem {C : Set (G → A) | ∃ (U : Finset G) (x : G → A), C = FullShift.cylinder U x} := by
  classical
  rintro _ ⟨U, x, rfl⟩ _ ⟨V, y, rfl⟩ ⟨z, hzx, hzy⟩
  exact ⟨U ∪ V, z, cylinder_inter_cylinder hzx hzy⟩

/-- The cylinder sets of a fixed configuration form a π-system. -/
theorem isPiSystem_cylinder_fixed (x : G → A) :
    IsPiSystem {C : Set (G → A) | ∃ U : Finset G, C = FullShift.cylinder U x} := by
  classical
  rintro _ ⟨U, rfl⟩ _ ⟨V, rfl⟩ -
  exact ⟨U ∪ V, (cylinder_union U V x).symm⟩

/-- **Measure of a cylinder set.** Under the product `Measure.infinitePi μ` of probability measures,
the cylinder set of configurations agreeing with `x` on a finite set `U` of coordinates has measure
`∏ i ∈ U, μ i {x i}`. For `μ = fun _ ↦ p` this is the Bernoulli measure of a cylinder. -/
theorem infinitePi_cylinder [MeasurableSpace A] [MeasurableSingletonClass A] (μ : G → Measure A)
    [∀ i, IsProbabilityMeasure (μ i)] (U : Finset G) (x : G → A) :
    Measure.infinitePi μ (FullShift.cylinder U x) = ∏ i ∈ U, μ i {x i} := by
  rw [cylinder_eq_set_pi]
  exact Measure.infinitePi_pi _ fun i _ ↦ measurableSet_singleton (x i)

end SymbolicDynamics.FullShift
