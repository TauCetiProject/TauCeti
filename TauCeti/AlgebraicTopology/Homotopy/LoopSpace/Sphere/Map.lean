/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.MappingSpace.HomotopyGroup
public import TauCeti.Topology.Homotopy.HomotopyGroup.IteratedLoopSpace.Basic
public import TauCeti.Topology.MappingSpace.Fibration
public import TauCeti.Topology.MappingSpace.Sphere.Basic

/-!
# Homotopy groups of mapping spaces out of spheres

Let `Sᵏ ⊆ ℝᵏ⁺¹` be the unit sphere, `k ≥ 1`, with a basepoint `s₀`. For every space `Q`, evaluation
`Map(Sᵏ, Q) → Q` at `s₀` is a Hurewicz fibration
(`TauCeti.isHurewiczFibration_mappingSpaceEval_sphere`) with fibre over `x` the based maps
`Map_*(Sᵏ, Q)`, a copy of the `k`-fold loop space `Ωᵏ_x Q`, and the constant maps are a section.
So its exact homotopy sequence splits (`TauCeti.injective_homotopyGroupMap_basedMap_val`,
`TauCeti.mem_range_homotopyGroupMap_basedMap_val_iff`): for `m ≥ 0` there are split short exact
sequences of groups

`1 → π_{m+1+k}(Q, x) → π_{m+1}(Map(Sᵏ, Q), x) → π_{m+1}(Q, x) → 1`,

at the constant map at `x`. The first map is the inclusion of the based maps after the shift
`π_{m+1}(Map_*(Sᵏ, Q)) ≅ π_{m+1}(Ωᵏ Q) ≅ π_{m+1+k}(Q, x)`
(`TauCeti.basedMapSphereHomotopyGroupMulEquiv`), the second is evaluation, and the splitting is
given by the constant maps (`TauCeti.mapHom_mappingSpaceEval_comp_mapHom_const`). For `k = 1` this
is the free-loop sequence of `TauCeti.AlgebraicTopology.Homotopy.LoopSpace.FreeLoop`, on a
different model of the circle; for `k = 2` it is the evaluation sequence of `Map(S², Q) → Q`, with
fibre the double loop space `Ω²Q`.

## Main declarations

* `TauCeti.basedMapSphereHomotopyGroupMulEquiv`: the shift
  `π_{m+1}(Map_*(Sᵏ, Q)) ≅ π_{m+1+k}(Q, x)` on the based-map fibre.
* `TauCeti.sphereMapHomotopyGroupHom`: the injection `π_{m+1+k}(Q, x) → π_{m+1}(Map(Sᵏ, Q), x)`,
  with `TauCeti.injective_sphereMapHomotopyGroupHom` and `TauCeti.range_sphereMapHomotopyGroupHom`,
  split by `TauCeti.mapHom_mappingSpaceEval_comp_mapHom_const`.

## References

* G. W. Whitehead, *Elements of Homotopy Theory*, GTM 61, Springer, 1978, Chapters I and IV.8.
* A. Hatcher, *Algebraic Topology*, Section 4.2, the long exact sequence of a fibration.
-/

public section

noncomputable section

open Metric Topology

universe u

namespace TauCeti

open BasedTopologicalSpace

variable (k : ℕ) {Q : Type u} [TopologicalSpace Q] (x : Q)
  (s₀ : sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1)

/-! ### The based-map fibre -/

/-- **The based-map fibre computes the shifted homotopy groups.** For `k ≥ 1`, the shift
`π_{m+1}(Map_*(Sᵏ, Q)) ≅ π_{m+1+k}(Q, x)` at the constant map: the based maps are the `k`-fold loop
space (`TauCeti.BasedTopologicalSpace.basedMapSphereHomeomorphIteratedLoopSpace`), whose homotopy
groups are those of `Q` shifted by `k`
(`TauCeti.BasedTopologicalSpace.piIteratedLoopSpaceMulEquiv`). -/
def basedMapSphereHomotopyGroupMulEquiv [NeZero k] (m : ℕ) :
    π_ (m + 1) (BasedMap (sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) Q s₀ x)
        ⟨ContinuousMap.const _ x, ContinuousMap.const_apply x s₀⟩ ≃*
      π_ (m + 1 + k) Q x :=
  (HomotopyGroup.homeomorphMulEquivOfEq
    (basedMapSphereHomeomorphIteratedLoopSpace k ⟨Q, x⟩ s₀)
    (basedMapSphereHomeomorphIteratedLoopSpace_const k ⟨Q, x⟩ s₀)).trans
    (piIteratedLoopSpaceMulEquiv k ⟨Q, x⟩ m)

/-- The shift on the based maps is the map induced by
`TauCeti.BasedTopologicalSpace.basedMapSphereHomeomorphIteratedLoopSpace`, followed by the shift
`TauCeti.BasedTopologicalSpace.piIteratedLoopSpaceMulEquiv` of the iterated loop space. -/
@[simp]
theorem basedMapSphereHomotopyGroupMulEquiv_apply [NeZero k] (m : ℕ)
    (a : π_ (m + 1) (BasedMap (sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) Q s₀ x)
      ⟨ContinuousMap.const _ x, ContinuousMap.const_apply x s₀⟩) :
    basedMapSphereHomotopyGroupMulEquiv k x s₀ m a =
      piIteratedLoopSpaceMulEquiv k ⟨Q, x⟩ m
        (HomotopyGroup.map
          ⟨basedMapSphereHomeomorphIteratedLoopSpace k ⟨Q, x⟩ s₀,
            (basedMapSphereHomeomorphIteratedLoopSpace k ⟨Q, x⟩ s₀).continuous⟩
          (basedMapSphereHomeomorphIteratedLoopSpace_const k ⟨Q, x⟩ s₀)
          a) := by
  rw [basedMapSphereHomotopyGroupMulEquiv, MulEquiv.trans_apply,
    HomotopyGroup.homeomorphMulEquivOfEq_apply]

/-! ### All maps -/

/-- The injection `π_{m+1+k}(Q, x) → π_{m+1}(Map(Sᵏ, Q), x)` at the constant map: the inverse of
the shift `TauCeti.basedMapSphereHomotopyGroupMulEquiv`, followed by the inclusion of the based
maps (`TauCeti.basedMapHomotopyGroupHom`). -/
def sphereMapHomotopyGroupHom [NeZero k] (m : ℕ) :
    π_ (m + 1 + k) Q x →*
      π_ (m + 1) C(sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1, Q) (ContinuousMap.const _ x) :=
  basedMapHomotopyGroupHom (basedMapSphereHomotopyGroupMulEquiv k x s₀ m)

/-- On the shift of a class of based maps, `TauCeti.sphereMapHomotopyGroupHom` is the map induced
by the inclusion of the based maps. Not `@[simp]`: the simp normal form unfolds the shift through
`TauCeti.basedMapSphereHomotopyGroupMulEquiv_apply`. -/
theorem sphereMapHomotopyGroupHom_basedMapSphereHomotopyGroupMulEquiv [NeZero k] (m : ℕ)
    (a : π_ (m + 1) (BasedMap (sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) Q s₀ x)
      ⟨ContinuousMap.const _ x, ContinuousMap.const_apply x s₀⟩) :
    sphereMapHomotopyGroupHom k x s₀ m (basedMapSphereHomotopyGroupMulEquiv k x s₀ m a) =
      HomotopyGroup.map ⟨Subtype.val, continuous_subtype_val⟩ rfl a :=
  basedMapHomotopyGroupHom_apply_mulEquiv _ a

/-- The injection `π_{m+1+k}(Q, x) → π_{m+1}(Map(Sᵏ, Q), x)` is injective. -/
theorem injective_sphereMapHomotopyGroupHom [NeZero k] (m : ℕ) :
    Function.Injective (sphereMapHomotopyGroupHom k x s₀ m) :=
  injective_basedMapHomotopyGroupHom
    (isHurewiczFibration_mappingSpaceEval_sphere.{0} k s₀).mem_serreFibrations _

/-- **Exactness of the sphere-map sequence.** The image of
`π_{m+1+k}(Q, x) → π_{m+1}(Map(Sᵏ, Q), x)` is the kernel of evaluation
`π_{m+1}(Map(Sᵏ, Q), x) → π_{m+1}(Q, x)`. -/
theorem range_sphereMapHomotopyGroupHom [NeZero k] (m : ℕ) :
    (sphereMapHomotopyGroupHom k x s₀ m).range =
      (HomotopyGroup.mapHom (N := Fin (m + 1)) (mappingSpaceEval (X := Q) s₀)
        (leftInverse_mappingSpaceEval_const s₀ x)).ker :=
  range_basedMapHomotopyGroupHom
    (isHurewiczFibration_mappingSpaceEval_sphere.{0} k s₀).mem_serreFibrations _

end TauCeti
