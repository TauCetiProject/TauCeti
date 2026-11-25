/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Billiard.ClosedCylinder
public import TauCeti.Dynamics.Billiard.Measure
public import TauCeti.Dynamics.NonwanderingSet

/-!
# The billiard map has no wandering points

Let `χ` be a twice differentiable arclength parametrization of the boundary of a strictly convex
billiard table (`TauCeti.StrictConvexBilliardTable`). The billiard map `T` of the open cylinder
`AddCircle L × (-1, 1)` preserves an area of full support, so by Poincaré recurrence
(`TauCeti.StrictConvexBilliardTable.exists_mem_iterate_billiardMap_mem`) every nonempty open set of
states contains a state returning to it: every state is non-wandering
(`TauCeti.StrictConvexBilliardTable.nonwanderingSet_billiardMap`).

The extension `T'` of `T` to the closed cylinder `AddCircle L × [-1, 1]`
(`TauCeti.StrictConvexBilliardTable.closedBilliardMap`) restricts to `T` on the open cylinder,
which is dense in the closed one, so every point of the closed cylinder is non-wandering for `T'`
(`TauCeti.StrictConvexBilliardTable.nonwanderingSet_closedBilliardMap`); the points of the two
boundary circles are moreover fixed by `T'`.
-/

public section

open Function Set Filter Topology Module

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fact (finrank ℝ E = 2)]

namespace StrictConvexBilliardTable

variable {o : Orientation ℝ E (Fin 2)} {χ : StrictConvexBilliardTable o}

/-- **Every state of a convex billiard is non-wandering.** If the arclength parametrization `χ`
is twice differentiable, the non-wandering set of the billiard map of the open cylinder is the
whole cylinder. -/
theorem nonwanderingSet_billiardMap (hχ : Differentiable ℝ (deriv χ)) :
    nonwanderingSet χ.billiardMap = univ := by
  refine eq_univ_of_forall fun x => mem_nonwanderingSet_iff_forall_isOpen.2 fun U hU hx => ?_
  obtain ⟨y, hy, m, hm, hmy⟩ := exists_mem_iterate_billiardMap_mem hχ hU ⟨x, hx⟩
  exact ⟨m, Nat.pos_of_ne_zero hm, _, mem_image_of_mem _ hy, hmy⟩

/-- The inclusion of the open cylinder `AddCircle L × (-1, 1)` in the closed cylinder
`AddCircle L × [-1, 1]`. -/
@[expose] def cylinderInclusion (χ : StrictConvexBilliardTable o) :
    AddCircle χ.period × Ioo (-1 : ℝ) 1 → AddCircle χ.period × Icc (-1 : ℝ) 1 :=
  Prod.map id (inclusion Ioo_subset_Icc_self)

/-- The inclusion of the open cylinder keeps the angle and the tangential component. -/
theorem cylinderInclusion_apply (x : AddCircle χ.period × Ioo (-1 : ℝ) 1) :
    χ.cylinderInclusion x = (x.1, inclusion Ioo_subset_Icc_self x.2) :=
  rfl

/-- The inclusion of the open cylinder in the closed cylinder is continuous. -/
theorem continuous_cylinderInclusion : Continuous χ.cylinderInclusion :=
  continuous_id.prodMap (continuous_inclusion Ioo_subset_Icc_self)

/-- The open cylinder is dense in the closed cylinder. -/
theorem denseRange_cylinderInclusion : DenseRange χ.cylinderInclusion := by
  have h : DenseRange (inclusion (Ioo_subset_Icc_self : Ioo (-1 : ℝ) 1 ⊆ Icc (-1) 1)) := by
    rw [DenseRange, dense_iff_closure_eq, eq_univ_iff_forall]
    intro v
    have hv : Subtype.val '' {x : Icc (-1 : ℝ) 1 | (x : ℝ) ∈ Ioo (-1) 1} = Ioo (-1) 1 := by
      ext y
      exact ⟨fun ⟨_, hx, hxy⟩ => hxy ▸ hx, fun hy => ⟨⟨y, Ioo_subset_Icc_self hy⟩, hy, rfl⟩⟩
    rw [range_inclusion, closure_subtype]
    change (v : ℝ) ∈ closure (Subtype.val '' {x : Icc (-1 : ℝ) 1 | (x : ℝ) ∈ Ioo (-1) 1})
    rw [hv, closure_Ioo (by norm_num)]
    exact v.property
  exact denseRange_id.prodMap h

/-- The extended billiard map restricts to the billiard map on the open cylinder, for every
number of iterations. -/
theorem iterate_closedBilliardMap_cylinderInclusion (n : ℕ)
    (x : AddCircle χ.period × Ioo (-1 : ℝ) 1) :
    χ.closedBilliardMap^[n] (χ.cylinderInclusion x) = χ.cylinderInclusion (χ.billiardMap^[n] x) :=
  ((Semiconj.iterate_right (f := χ.cylinderInclusion)
    (fun x => (χ.closedBilliardMap_inclusion x).symm) n x)).symm

/-- **Every point of the closed cylinder is non-wandering.** If the arclength parametrization `χ`
is twice differentiable, the non-wandering set of the billiard map extended to the closed cylinder
is the whole closed cylinder. -/
theorem nonwanderingSet_closedBilliardMap (hχ : Differentiable ℝ (deriv χ)) :
    nonwanderingSet χ.closedBilliardMap = univ := by
  refine χ.denseRange_cylinderInclusion.nonwanderingSet_eq_univ ?_
  rintro _ ⟨x, rfl⟩
  refine mem_nonwanderingSet_iff_exists_iterate_mem.2 fun U hU => ?_
  have hx : χ.cylinderInclusion ⁻¹' U ∈ 𝓝 x := χ.continuous_cylinderInclusion.continuousAt hU
  obtain ⟨n, hn, y, hy, hny⟩ :=
    mem_nonwanderingSet_iff_exists_iterate_mem.1 ((nonwanderingSet_billiardMap hχ).symm ▸
      mem_univ x) _ hx
  exact ⟨n, hn, _, hy, by rwa [iterate_closedBilliardMap_cylinderInclusion]⟩

end StrictConvexBilliardTable

end TauCeti
