/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.AffineE8.Basic
public import TauCeti.RepresentationTheory.Quiver.Zigzag.ADE.Basic

/-!
# The affine `E₈` quiver and zigzag graph

The inward-oriented representation quiver for affine `E₈` and the arm-indexed graph used for
its zigzag algebra are two labelings of the same `T₂,₃,₆` diagram. This file gives the explicit
graph isomorphism between them and identifies the affine node in those labels.
-/

public section

namespace TauCeti

/-- The arm-coordinate labels on the affine `E₈` quiver, in the numbering of
`zigzagAffineE8Graph`: the centre is `0`, and the short, medium, and long arms are numbered
outwards. -/
def affineE8VertexEquiv : Quiver.AffineE8 ≃ Fin 9 where
  toFun
    | .center => 0
    | .short => 1
    | .medium4 => 2
    | .medium2 => 3
    | .long5 => 4
    | .long4 => 5
    | .long3 => 6
    | .long2 => 7
    | .long1 => 8
  invFun
    | 0 => .center
    | 1 => .short
    | 2 => .medium4
    | 3 => .medium2
    | 4 => .long5
    | 5 => .long4
    | 6 => .long3
    | 7 => .long2
    | 8 => .long1
  left_inv v := by cases v <;> rfl
  right_inv i := by fin_cases i <;> rfl

/-- The centre has affine `E₈` graph label `0`. -/
@[simp] theorem affineE8VertexEquiv_center :
    affineE8VertexEquiv Quiver.AffineE8.center = 0 := (rfl)

/-- The short-arm vertex has affine `E₈` graph label `1`. -/
@[simp] theorem affineE8VertexEquiv_short :
    affineE8VertexEquiv Quiver.AffineE8.short = 1 := (rfl)

/-- The outer medium-arm vertex has affine `E₈` graph label `2`. -/
@[simp] theorem affineE8VertexEquiv_medium4 :
    affineE8VertexEquiv Quiver.AffineE8.medium4 = 2 := (rfl)

/-- The inner medium-arm vertex has affine `E₈` graph label `3`. -/
@[simp] theorem affineE8VertexEquiv_medium2 :
    affineE8VertexEquiv Quiver.AffineE8.medium2 = 3 := (rfl)

/-- The outer long-arm vertex has affine `E₈` graph label `4`. -/
@[simp] theorem affineE8VertexEquiv_long5 :
    affineE8VertexEquiv Quiver.AffineE8.long5 = 4 := (rfl)

/-- The next long-arm vertex has affine `E₈` graph label `5`. -/
@[simp] theorem affineE8VertexEquiv_long4 :
    affineE8VertexEquiv Quiver.AffineE8.long4 = 5 := (rfl)

/-- The middle long-arm vertex has affine `E₈` graph label `6`. -/
@[simp] theorem affineE8VertexEquiv_long3 :
    affineE8VertexEquiv Quiver.AffineE8.long3 = 6 := (rfl)

/-- The next long-arm vertex has affine `E₈` graph label `7`. -/
@[simp] theorem affineE8VertexEquiv_long2 :
    affineE8VertexEquiv Quiver.AffineE8.long2 = 7 := (rfl)

/-- The endpoint of the long arm has affine `E₈` graph label `8`. -/
@[simp] theorem affineE8VertexEquiv_long1 :
    affineE8VertexEquiv Quiver.AffineE8.long1 = 8 := (rfl)

/-- Graph label `0` is sent back to the centre. -/
@[simp] theorem affineE8VertexEquiv_symm_zero :
    affineE8VertexEquiv.symm 0 = Quiver.AffineE8.center := (rfl)

/-- Graph label `1` is sent back to the short-arm vertex. -/
@[simp] theorem affineE8VertexEquiv_symm_one :
    affineE8VertexEquiv.symm 1 = Quiver.AffineE8.short := (rfl)

/-- Graph label `2` is sent back to the outer medium-arm vertex. -/
@[simp] theorem affineE8VertexEquiv_symm_two :
    affineE8VertexEquiv.symm 2 = Quiver.AffineE8.medium4 := (rfl)

/-- Graph label `3` is sent back to the inner medium-arm vertex. -/
@[simp] theorem affineE8VertexEquiv_symm_three :
    affineE8VertexEquiv.symm 3 = Quiver.AffineE8.medium2 := (rfl)

/-- Graph label `4` is sent back to the outer long-arm vertex. -/
@[simp] theorem affineE8VertexEquiv_symm_four :
    affineE8VertexEquiv.symm 4 = Quiver.AffineE8.long5 := (rfl)

/-- Graph label `5` is sent back to the next long-arm vertex. -/
@[simp] theorem affineE8VertexEquiv_symm_five :
    affineE8VertexEquiv.symm 5 = Quiver.AffineE8.long4 := (rfl)

/-- Graph label `6` is sent back to the middle long-arm vertex. -/
@[simp] theorem affineE8VertexEquiv_symm_six :
    affineE8VertexEquiv.symm 6 = Quiver.AffineE8.long3 := (rfl)

/-- Graph label `7` is sent back to the next long-arm vertex. -/
@[simp] theorem affineE8VertexEquiv_symm_seven :
    affineE8VertexEquiv.symm 7 = Quiver.AffineE8.long2 := (rfl)

/-- Graph label `8` is sent back to the endpoint of the long arm. -/
@[simp] theorem affineE8VertexEquiv_symm_eight :
    affineE8VertexEquiv.symm 8 = Quiver.AffineE8.long1 := (rfl)

/-- The explicit relabelling identifies the underlying graph of the inward affine `E₈` quiver
with the affine `E₈` graph used for its zigzag algebra. -/
def affineE8UnderlyingGraphIso :
    Quiver.underlyingGraph Quiver.AffineE8 ≃g zigzagAffineE8Graph where
  toEquiv := affineE8VertexEquiv
  map_rel_iff' := by
    classical
    intro v w
    rw [zigzagAffineE8Graph_adj, Quiver.underlyingGraph_adj]
    cases v <;> cases w
    all_goals
      simp only [Equiv.coe_fn_mk, affineE8VertexEquiv]
    all_goals norm_num
    all_goals
      first
      | exact Or.inl ⟨Quiver.AffineE8.Arrow.short⟩
      | exact Or.inr ⟨Quiver.AffineE8.Arrow.short⟩
      | exact Or.inl ⟨Quiver.AffineE8.Arrow.medium2⟩
      | exact Or.inr ⟨Quiver.AffineE8.Arrow.medium2⟩
      | exact Or.inl ⟨Quiver.AffineE8.Arrow.medium4⟩
      | exact Or.inr ⟨Quiver.AffineE8.Arrow.medium4⟩
      | exact Or.inl ⟨Quiver.AffineE8.Arrow.long1⟩
      | exact Or.inr ⟨Quiver.AffineE8.Arrow.long1⟩
      | exact Or.inl ⟨Quiver.AffineE8.Arrow.long2⟩
      | exact Or.inr ⟨Quiver.AffineE8.Arrow.long2⟩
      | exact Or.inl ⟨Quiver.AffineE8.Arrow.long3⟩
      | exact Or.inr ⟨Quiver.AffineE8.Arrow.long3⟩
      | exact Or.inl ⟨Quiver.AffineE8.Arrow.long4⟩
      | exact Or.inr ⟨Quiver.AffineE8.Arrow.long4⟩
      | exact Or.inl ⟨Quiver.AffineE8.Arrow.long5⟩
      | exact Or.inr ⟨Quiver.AffineE8.Arrow.long5⟩
      | constructor <;> exact ⟨fun e => by cases e⟩

/-- The graph isomorphism acts on vertices by the explicit arm-coordinate equivalence. -/
@[simp]
theorem affineE8UnderlyingGraphIso_apply (v : Quiver.AffineE8) :
    affineE8UnderlyingGraphIso v = affineE8VertexEquiv v := (rfl)

/-- The affine node is the endpoint of the arm of length five in the representation-quiver
labeling. -/
theorem affineE8VertexEquiv_long1_affineNode :
    affineE8VertexEquiv Quiver.AffineE8.long1 =
      Fin.cast (by rfl) AffineDynkinType.E8.affineNode := by
  apply Fin.ext
  rw [Fin.val_cast, AffineDynkinType.affineNode_E8]
  rfl

end TauCeti
