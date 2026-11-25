/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Billiard.Inverse
public import Mathlib.Topology.Algebra.Group.Quotient
import TauCeti.Dynamics.Billiard.Continuous
import TauCeti.Topology.Constructions.SumProd
import TauCeti.Topology.Instances.AddCircle.Coe
import TauCeti.Topology.Order.Interval

/-!
# The billiard map is a homeomorphism

Let `χ` be an arclength parametrization of the boundary of a strictly convex billiard table
(`TauCeti.StrictConvexBilliardTable`), with period `L`, and let `B(s, v) = (t, w)` be its
next-collision map on the strip `ℝ × (-1, 1)`, which is continuous there
(`TauCeti.StrictConvexBilliardTable.continuousOn_nextCollision`). Its inverse is
`τ⁻¹ ∘ ι ∘ B ∘ ι`, with `ι(s, v) = (s, -v)` and `τ(s, v) = (s + L, v)`, so `B` is a homeomorphism
of the strip (`TauCeti.StrictConvexBilliardTable.nextCollisionHomeomorph`), and the billiard map `β`
it induces on the space of collision states `AddCircle L × (-1, 1)` is a homeomorphism
(`TauCeti.StrictConvexBilliardTable.billiardHomeomorph`).

## Main results

* `TauCeti.StrictConvexBilliardTable.continuous_nextCollisionEquiv`,
  `TauCeti.StrictConvexBilliardTable.continuous_nextCollisionEquiv_symm`,
  `TauCeti.StrictConvexBilliardTable.nextCollisionHomeomorph`: the next-collision map is a
  homeomorphism of the strip.
* `TauCeti.StrictConvexBilliardTable.billiardHomeomorph`: the billiard map is a homeomorphism of
  `AddCircle L × (-1, 1)`.

## References

* Ana Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 5.2 (the billiard map of a convex table).
* Serge Tabachnikov, *Geometry and Billiards*, Student Mathematical Library 30, American
  Mathematical Society, 2005, Chapter 3 (the billiard ball map).
-/

public section

noncomputable section

open Set

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fact (Module.finrank ℝ E = 2)]

namespace StrictConvexBilliardTable

variable {o : Orientation ℝ E (Fin 2)} (χ : StrictConvexBilliardTable o)

/-! ### The next-collision map and the billiard map are homeomorphisms -/

/-- The next-collision map is continuous as a bijection of the strip. -/
theorem continuous_nextCollisionEquiv : Continuous χ.nextCollisionEquiv := by
  convert χ.continuousOn_nextCollision.continuous_restrict_univ_prod
    fun x ↦ χ.nextCollision_snd_mem_Ioo x.2.property using 1
  funext x
  ext <;> simp

/-- The inverse `τ⁻¹ ∘ ι ∘ B ∘ ι` of the next-collision map is continuous. -/
theorem continuous_nextCollisionEquiv_symm : Continuous χ.nextCollisionEquiv.symm := by
  convert ((continuous_fst.sub (continuous_const (y := χ.period))).prodMk
    ((continuous_neg_Ioo (1 : ℝ)).comp continuous_snd)).comp
      (χ.continuous_nextCollisionEquiv.comp
        (continuous_fst.prodMk ((continuous_neg_Ioo (1 : ℝ)).comp continuous_snd))) using 1
  funext x
  ext <;> simp

/-- The next-collision map is a homeomorphism of the strip `ℝ × (-1, 1)`. -/
def nextCollisionHomeomorph : ℝ × Ioo (-1 : ℝ) 1 ≃ₜ ℝ × Ioo (-1 : ℝ) 1 where
  toEquiv := χ.nextCollisionEquiv
  continuous_toFun := χ.continuous_nextCollisionEquiv
  continuous_invFun := χ.continuous_nextCollisionEquiv_symm

@[simp]
theorem nextCollisionHomeomorph_toEquiv :
    χ.nextCollisionHomeomorph.toEquiv = χ.nextCollisionEquiv := by
  rfl

@[simp]
theorem coe_nextCollisionHomeomorph : ⇑χ.nextCollisionHomeomorph = χ.nextCollisionEquiv := by
  rfl

@[simp]
theorem coe_nextCollisionHomeomorph_symm :
    ⇑χ.nextCollisionHomeomorph.symm = χ.nextCollisionEquiv.symm := by
  rfl

/-- The billiard map of `AddCircle L × (-1, 1)` is continuous. -/
theorem continuous_billiardMap : Continuous χ.billiardMap :=
  AddCircle.continuous_prod_of_lift χ.continuous_nextCollisionEquiv fun s v ↦ by simp

/-- The inverse `ι ∘ β ∘ ι` of the billiard map is continuous. -/
theorem continuous_billiardMap_symm : Continuous χ.billiardMap.symm := by
  convert (continuous_id.prodMap (continuous_neg_Ioo (1 : ℝ))).comp
    (χ.continuous_billiardMap.comp (continuous_id.prodMap (continuous_neg_Ioo (1 : ℝ)))) using 1
  funext ⟨θ, v⟩
  induction θ using QuotientAddGroup.induction_on with | H s => ?_
  ext <;> simp

/-- The billiard map is a homeomorphism of the space of collision states
`AddCircle L × (-1, 1)`. -/
def billiardHomeomorph :
    AddCircle χ.period × Ioo (-1 : ℝ) 1 ≃ₜ AddCircle χ.period × Ioo (-1 : ℝ) 1 where
  toEquiv := χ.billiardMap
  continuous_toFun := χ.continuous_billiardMap
  continuous_invFun := χ.continuous_billiardMap_symm

@[simp]
theorem billiardHomeomorph_toEquiv : χ.billiardHomeomorph.toEquiv = χ.billiardMap := by
  rfl

@[simp]
theorem coe_billiardHomeomorph : ⇑χ.billiardHomeomorph = χ.billiardMap := by
  rfl

@[simp]
theorem coe_billiardHomeomorph_symm : ⇑χ.billiardHomeomorph.symm = χ.billiardMap.symm := by
  rfl
end StrictConvexBilliardTable

end TauCeti
