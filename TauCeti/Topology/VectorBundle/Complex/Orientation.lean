/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Orientation
public import TauCeti.Topology.VectorBundle.Complex.Structure
public import TauCeti.Topology.VectorBundle.Orientation.Basic

import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
import Mathlib.Topology.VectorBundle.FiniteDimensional
import TauCeti.Analysis.Normed.Module.Alternating.Tame
import TauCeti.Geometry.Symplectic.ExistsCompatible

/-!
# The complex orientation of a complex vector bundle

A continuous complex structure `J` on a real vector bundle `V` with finite-dimensional model fibre
(`TauCeti.Bundle.ContinuousComplexStructure`) orients each fibre `V b` by the complex orientation
of `J b` (`TauCeti.AlmostComplexStructure.orientation`), in which the `J b`-adapted bases
`(v₁, J v₁, …, vₙ, J vₙ)` are positive. These fibre orientations form an orientation of the
bundle, the **complex orientation** `TauCeti.Bundle.ContinuousComplexStructure.orientation`.

Local constancy needs no derivative of `J`, only its continuity. Read in the trivialization of `V`
at `b`, `J` is a continuous family `J.coord b x` of endomorphisms of the model fibre `F`, and it
carries the complex orientation of `J x` to that of `J.coord b x`
(`TauCeti.AlmostComplexStructure.map_orientation`). A symplectic form on `F` taming `J.coord b b`
still tames `J.coord b x` for `x` near `b`, since taming a fixed form is an open condition on the
endomorphism (`TauCeti.isOpen_setOf_forall_endomorphism_pos`), and every form taming `J.coord b x`
induces its complex orientation (`TauCeti.AlmostComplexStructure.orientation_eq_of_tames`).

## Main definitions

* `TauCeti.Bundle.ContinuousComplexStructure.orientation`: the complex orientation of `V`.

## Main results

* `TauCeti.Bundle.ContinuousComplexStructure.orientation_apply`: its orientation of the fibre over
  `b` is the complex orientation of `J b`.
* `TauCeti.Bundle.ContinuousComplexStructure.transport_almostComplexStructureAt_apply`: read in the
  trivialization of `V` at `b₀`, the complex structure `J b` is `J.coord b₀ b`.

## References

* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Chapter 4 (almost complex structures and the orientations they induce).
-/

public section

open Bundle Filter Module
open scoped Topology

namespace TauCeti.Bundle.ContinuousComplexStructure

variable {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : B → Type*} [∀ b, AddCommGroup (V b)] [∀ b, Module ℝ (V b)] [∀ b, TopologicalSpace (V b)]
  [∀ b, IsTopologicalAddGroup (V b)] [∀ b, ContinuousSMul ℝ (V b)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  (J : ContinuousComplexStructure F V) {k : ℕ} (hk : finrank ℝ F = k)

omit [FiniteDimensional ℝ F] in
/-- Read in the trivialization of `V` at `b₀`, the complex structure `J b` is `J.coord b₀ b`. -/
theorem transport_almostComplexStructureAt_apply {b₀ b : B}
    (hb : b ∈ (trivializationAt F V b₀).baseSet) (w : F) :
    (J.almostComplexStructureAt b).transport ((trivializationAt F V b₀).linearEquivAt ℝ b hb) w =
      J.coord b₀ b w := by
  -- On the base set, the trivialization's linear equivalence is its continuous linear map.
  have he (v : V b) : (trivializationAt F V b₀).linearEquivAt ℝ b hb v =
      (trivializationAt F V b₀).continuousLinearMapAt ℝ b v :=
    ((trivializationAt F V b₀).continuousLinearMapAt_apply_of_mem (R := ℝ) hb v).symm
  obtain ⟨v, rfl⟩ := ((trivializationAt F V b₀).linearEquivAt ℝ b hb).surjective w
  rw [AlmostComplexStructure.transport_apply, LinearEquiv.symm_apply_apply,
    almostComplexStructureAt_apply, he, he, coord_apply J hb]

/-- The fibre complex orientations are locally constant in the preferred trivializations of `V`. -/
private theorem eventually_mapOrientation_orientation_eq (b : B) :
    ∀ᶠ x in 𝓝 b, ∀ hx : x ∈ (trivializationAt F V b).baseSet,
      haveI := VectorBundle.finiteDimensional ℝ F V x
      haveI := VectorBundle.finiteDimensional ℝ F V b
      (trivializationAt F V b).mapOrientation (Fin k) hx
          ((J.almostComplexStructureAt x).orientation
            ((VectorBundle.finrank_eq ℝ F V x).trans hk)) =
        (trivializationAt F V b).mapOrientation (Fin k)
          (FiberBundle.mem_baseSet_trivializationAt' b)
          ((J.almostComplexStructureAt b).orientation
            ((VectorBundle.finrank_eq ℝ F V b).trans hk)) := by
  have (x : B) : FiniteDimensional ℝ (V x) := VectorBundle.finiteDimensional ℝ F V x
  set e := trivializationAt F V b
  have hb : b ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' b
  -- A symplectic form on `F` taming `J` read at `x` induces the orientation at `x`.
  have hmap {x : B} (hx : x ∈ e.baseSet) (τ : SymplecticForm F)
      (hτ : ∀ u ≠ 0, 0 < τ u (J.coord b x u)) :
      e.mapOrientation (Fin k) hx
        ((J.almostComplexStructureAt x).orientation ((VectorBundle.finrank_eq ℝ F V x).trans hk)) =
          τ.orientation hk := by
    rw [Trivialization.mapOrientation_apply, AlmostComplexStructure.map_orientation
      (AlmostComplexStructure.isComplexLinearMap_transport _ _)
      ((VectorBundle.finrank_eq ℝ F V x).trans hk)]
    refine AlmostComplexStructure.orientation_eq_of_tames (fun u hu ↦ ?_) _
    rw [transport_almostComplexStructureAt_apply]
    exact hτ u hu
  -- A form taming `J` read at `b` still tames it nearby.
  obtain ⟨τ, hτ⟩ := ((J.almostComplexStructureAt b).transport (e.linearEquivAt ℝ b hb)).exists_tames
  have hτb : ∀ u ≠ 0, 0 < τ u (J.coord b b u) := fun u hu ↦ by
    rw [← transport_almostComplexStructureAt_apply J hb]
    exact hτ u hu
  have hc : ContinuousAt (J.coord b) b :=
    (J.continuousOn_coord b).continuousAt (e.open_baseSet.mem_nhds hb)
  filter_upwards [hc.eventually_mem ((isOpen_setOf_forall_endomorphism_pos
    (LinearMap.toContinuousBilinearMap τ.toBilinForm)).mem_nhds (by simpa using hτb))]
    with x hx hxe
  rw [hmap hxe τ (by simpa using hx), hmap hb τ hτb]

/-- The **complex orientation** of a real vector bundle `V` with a continuous complex structure
`J`: on the fibre over `b` it is the complex orientation of `J b`, in which the `J b`-adapted bases
`(v₁, J v₁, …, vₙ, J vₙ)` are positive. -/
noncomputable def orientation : VectorBundleOrientation F V (Fin k) :=
  ⟨fun b ↦ haveI := VectorBundle.finiteDimensional ℝ F V b
    (J.almostComplexStructureAt b).orientation ((VectorBundle.finrank_eq ℝ F V b).trans hk),
    J.eventually_mapOrientation_orientation_eq hk⟩

/-- The complex orientation of `V` orients the fibre over `b` by the complex orientation of
`J b`. -/
theorem orientation_apply (b : B) (hb : finrank ℝ (V b) = k) :
    haveI := VectorBundle.finiteDimensional ℝ F V b
    J.orientation hk b = (J.almostComplexStructureAt b).orientation hb :=
  (rfl)

end TauCeti.Bundle.ContinuousComplexStructure
