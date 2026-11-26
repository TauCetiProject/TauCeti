/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.Sets.Opens
import Mathlib.Algebra.GroupWithZero.Units.Lemmas

/-!
# Algebraic operations on continuous maps

The algebra map `R →+* C(X, A)` into continuous maps valued in a topological `R`-algebra sends `r`
to the constant map `ContinuousMap.const X (algebraMap R A r)`
(`ContinuousMap.algebraMap_eq_const`).

When a bundled continuous map `f : C(X, M₀)` into a topological monoid with zero is a unit,
evaluating `f⁻¹ʳ` at `x : X` agrees with `(f x)⁻¹ʳ` (`ContinuousMap.ringInverse_apply`). Without
`IsUnit f`, `f⁻¹ʳ` vanishes globally even at points where `f x` is individually invertible.

For a continuous map `f : s → X` on a subset `s` of a topological additive group, the
*displacement* `ContinuousMap.displacement f` is the continuous map `z ↦ z - f z`, whose zeros are
the fixed points of `f` (`ContinuousMap.preimage_displacement_zero`).
-/

public section

open Set TopologicalSpace
open scoped Ring

namespace ContinuousMap

/-- The algebra map `R →+* C(X, A)` sends `r` to the constant continuous map with value
`algebraMap R A r`. -/
theorem algebraMap_eq_const {X R A : Type*} [TopologicalSpace X] [CommSemiring R]
    [TopologicalSpace A] [Semiring A] [Algebra R A] [IsTopologicalSemiring A] (r : R) :
    algebraMap R C(X, A) r = const X (algebraMap R A r) :=
  (rfl)

/-- Evaluating `f⁻¹ʳ` at a point `x` gives `(f x)⁻¹ʳ` whenever `f : C(X, M₀)` is a unit. -/
theorem ringInverse_apply {X M₀ : Type*} [TopologicalSpace X] [MonoidWithZero M₀]
    [TopologicalSpace M₀] [ContinuousMul M₀] {f : C(X, M₀)} (hf : IsUnit f) (x : X) :
    f⁻¹ʳ x = (f x)⁻¹ʳ :=
  hf.map_ringInverse ((Pi.evalMonoidHom (fun _ ↦ M₀) x).comp coeFnMonoidHom)

section Displacement

variable {X S : Type*} [TopologicalSpace X] [AddGroup X] [IsTopologicalAddGroup X] [SetLike S X]
  {s : S}

/-- The **displacement** of a continuous map `f : s → X` on a subset `s` of a topological additive
group: the map `z ↦ z - f z`, whose zeros are the fixed points of `f`
(`ContinuousMap.preimage_displacement_zero`). -/
def displacement (f : C(s, X)) : C(s, X) :=
  subtypeVal (s : Set X) - f

/-- The displacement of `f` sends `z` to `z - f z`. -/
@[simp]
theorem displacement_apply (f : C(s, X)) (z : s) : f.displacement z = z - f z :=
  (rfl)

/-- The zeros of the displacement `z ↦ z - f z` are the fixed points of `f`. -/
theorem preimage_displacement_zero (f : C(s, X)) : f.displacement ⁻¹' {0} = {z | f z = z} := by
  ext z
  rw [mem_preimage, mem_singleton_iff, displacement_apply, sub_eq_zero, mem_ofPred_eq]
  exact eq_comm

/-- The displacement of the restriction of `f : U → X` to an open subset `V ⊆ U` is the
restriction of the displacement of `f`. -/
@[simp]
theorem displacement_comp_inclusion {U V : Opens X} (hVU : V ≤ U) (f : C(U, X)) :
    (f.comp (inclusion hVU)).displacement = f.displacement.comp (inclusion hVU) := by
  ext z
  simp [inclusion]

end Displacement

end ContinuousMap
