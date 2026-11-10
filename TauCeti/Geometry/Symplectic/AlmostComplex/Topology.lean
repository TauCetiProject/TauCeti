/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.AlmostComplex
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import TauCeti.Topology.Algebra.Module.BilinearForm

import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# The topology on linear complex structures

The complex structures of a finite-dimensional real normed space carry the topology induced by
the operator norm of their endomorphisms. Since all norms on a finite-dimensional space are
equivalent, it does not depend on the choice of the norm of `V`.

## Main declarations

* The instance `TopologicalSpace (TauCeti.AlmostComplexStructure V)`: the topology induced from
  the operator norm on `V →L[ℝ] V`.
* `TauCeti.AlmostComplexStructure.isEmbedding_toContinuousLinearMap`: sending a complex
  structure to its continuous endomorphism is a topological embedding.
* `TauCeti.AlmostComplexStructure.continuous_iff`: continuity of maps into the complex
  structures is continuity of their endomorphisms in the operator norm.
* `TauCeti.AlmostComplexStructure.toContinuousLinearMap_mul_self`: in the operator-norm algebra a
  complex structure squares to `-1`.
* `TauCeti.SymplecticForm.Tames.eventually_of_continuousAt`: tameness is an open condition along
  families that are continuous in the operator norm.
-/

public noncomputable section

open Filter Topology

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

namespace AlmostComplexStructure

/-- The topology on the complex structures of a finite-dimensional real normed space induced by
the operator norm of their endomorphisms. Since all norms on a finite-dimensional space are
equivalent, it does not depend on the choice of the norm of `V`. -/
instance : TopologicalSpace (AlmostComplexStructure V) :=
  .induced (fun J ↦ LinearMap.toContinuousLinearMap J.toLinearMap) inferInstance

/-- Sending a complex structure to its endomorphism is a topological embedding into the
continuous endomorphisms. -/
theorem isEmbedding_toContinuousLinearMap :
    IsEmbedding fun J : AlmostComplexStructure V ↦ LinearMap.toContinuousLinearMap J.toLinearMap :=
  ⟨⟨rfl⟩, LinearMap.toContinuousLinearMap.injective.comp toLinearMap_injective⟩

/-- A map into the complex structures is continuous exactly when its endomorphisms are
continuous in the operator norm. -/
theorem continuous_iff {X : Type*} [TopologicalSpace X] {f : X → AlmostComplexStructure V} :
    Continuous f ↔ Continuous fun x ↦ LinearMap.toContinuousLinearMap (f x).toLinearMap :=
  isEmbedding_toContinuousLinearMap.continuous_iff

/-- In the operator-norm algebra, an almost complex structure squares to `-1`. -/
@[simp]
theorem toContinuousLinearMap_mul_self (J : AlmostComplexStructure V) :
    LinearMap.toContinuousLinearMap J.toLinearMap * LinearMap.toContinuousLinearMap J.toLinearMap =
      -1 := by
  ext v
  simp

end AlmostComplexStructure

namespace SymplecticForm

/-- Tameness is an open condition: if a family of complex structures is continuous at `x` in
the operator-norm topology and `ω`-tame there, it is `ω`-tame near `x`. -/
theorem Tames.eventually_of_continuousAt {X : Type*} [TopologicalSpace X] {ω : SymplecticForm V}
    {J : X → AlmostComplexStructure V} {x : X}
    (hJ : ContinuousAt (fun y => LinearMap.toContinuousLinearMap (J y).toLinearMap) x)
    (h : ω.Tames (J x)) : ∀ᶠ y in 𝓝 x, ω.Tames (J y) := by
  let ωc := ω.toBilinForm.toContinuousBilinearMap
  -- The forms `ω(·, A ·)` depend continuously on the operator `A`, and positivity is open.
  have hc : Continuous fun A : V →L[ℝ] V => (ContinuousLinearMap.compL ℝ V V ℝ).flip A ∘L ωc := by
    fun_prop
  have hA : ∀ᶠ A in 𝓝 (LinearMap.toContinuousLinearMap (J x).toLinearMap),
      ∀ v, v ≠ 0 → 0 < ((ContinuousLinearMap.compL ℝ V V ℝ).flip A ∘L ωc) v v :=
    hc.continuousAt.preimage_mem_nhds (isOpen_setOf_forall_bilinear_apply_self_pos.mem_nhds
      fun v hv => by simpa [ωc] using h v hv)
  filter_upwards [hJ.eventually hA] with y hy v hv
  simpa [ωc] using hy v hv

end SymplecticForm

end TauCeti
