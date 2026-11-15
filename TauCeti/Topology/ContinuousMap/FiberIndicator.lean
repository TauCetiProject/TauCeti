/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.ContinuousMap.LocallyConstant
public import Mathlib.Topology.UniformSpace.ProdApproximation

/-!
# Continuous fibre indicators

A continuous map to a discrete space has continuous fibre indicators. These functions pull back
under composition and vanish on empty fibres. Integer-valued decompositions into finite sums of
separated products transport to any topological commutative ring, which allows the same
decomposition to be used with different coefficient rings.
-/

public noncomputable section

namespace ContinuousMap

variable {X A B R : Type*} [TopologicalSpace X] [TopologicalSpace A] [TopologicalSpace B]

section

variable [TopologicalSpace R] [Zero R] [One R]

/-- The continuous characteristic function of a fibre of a map to a discrete space. -/
def fiberIndicator [DiscreteTopology A] (q : C(X, A)) (a : A) : C(X, R) :=
  by
    classical
    exact (ContinuousMap.equivFnOfDiscrete.symm (Pi.single a 1)).comp q

@[simp]
theorem fiberIndicator_apply [DiscreteTopology A] [DecidableEq A]
    (q : C(X, A)) (a : A) (x : X) :
    q.fiberIndicator (R := R) a x = if q x = a then 1 else 0 := by
  classical
  simp [fiberIndicator, Pi.single_apply]

/-- The fibre indicators of `q` pull back to the fibre indicators of `q ∘ φ`. -/
@[simp]
theorem fiberIndicator_comp [DiscreteTopology A] (q : C(X, A)) (φ : C(B, X)) (a : A) :
    (q.fiberIndicator (R := R) a).comp φ = (q.comp φ).fiberIndicator a := by
  classical
  ext x
  simp

/-- The indicator of an empty fibre vanishes. -/
theorem fiberIndicator_eq_zero_of_notMem_range [DiscreteTopology A] {q : C(X, A)} {a : A}
    (ha : a ∉ Set.range q) : q.fiberIndicator (R := R) a = 0 := by
  classical
  ext x
  have hx : q x ≠ a := fun h ↦ ha ⟨x, h⟩
  simp [fiberIndicator_apply, hx]

end

/-- Transport an integer fibre-indicator decomposition into any topological commutative ring. -/
theorem fiberIndicator_comp_eq_sum_intCast [DiscreteTopology A] [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] (q : C(X, A)) (m : C(X × X, X))
    (a : A) {n : ℕ} (g h : Fin n → C(X, ℤ))
    (hgh : ∀ x y, (q.comp m).fiberIndicator (R := ℤ) a (x, y) = ∑ i, g i x * h i y) :
    (q.fiberIndicator (R := R) a).comp m =
      ∑ i, (intCastLocallyConstant (R := R) (g i) : C(X, R)).prodMul
        (intCastLocallyConstant (R := R) (h i)) := by
  classical
  ext p
  have hp := congrArg (Int.castRingHom R) (hgh p.1 p.2)
  simpa [fiberIndicator_apply] using hp

end ContinuousMap
