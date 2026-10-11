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
@[expose]
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
      | exact Or.inl (show Nonempty (Quiver.AffineE8.short ⟶ Quiver.AffineE8.center)
          from ⟨Quiver.AffineE8.Arrow.short⟩)
      | exact Or.inr (show Nonempty (Quiver.AffineE8.short ⟶ Quiver.AffineE8.center)
          from ⟨Quiver.AffineE8.Arrow.short⟩)
      | exact Or.inl (show Nonempty (Quiver.AffineE8.medium2 ⟶ Quiver.AffineE8.medium4)
          from ⟨Quiver.AffineE8.Arrow.medium2⟩)
      | exact Or.inr (show Nonempty (Quiver.AffineE8.medium2 ⟶ Quiver.AffineE8.medium4)
          from ⟨Quiver.AffineE8.Arrow.medium2⟩)
      | exact Or.inl (show Nonempty (Quiver.AffineE8.medium4 ⟶ Quiver.AffineE8.center)
          from ⟨Quiver.AffineE8.Arrow.medium4⟩)
      | exact Or.inr (show Nonempty (Quiver.AffineE8.medium4 ⟶ Quiver.AffineE8.center)
          from ⟨Quiver.AffineE8.Arrow.medium4⟩)
      | exact Or.inl (show Nonempty (Quiver.AffineE8.long1 ⟶ Quiver.AffineE8.long2)
          from ⟨Quiver.AffineE8.Arrow.long1⟩)
      | exact Or.inr (show Nonempty (Quiver.AffineE8.long1 ⟶ Quiver.AffineE8.long2)
          from ⟨Quiver.AffineE8.Arrow.long1⟩)
      | exact Or.inl (show Nonempty (Quiver.AffineE8.long2 ⟶ Quiver.AffineE8.long3)
          from ⟨Quiver.AffineE8.Arrow.long2⟩)
      | exact Or.inr (show Nonempty (Quiver.AffineE8.long2 ⟶ Quiver.AffineE8.long3)
          from ⟨Quiver.AffineE8.Arrow.long2⟩)
      | exact Or.inl (show Nonempty (Quiver.AffineE8.long3 ⟶ Quiver.AffineE8.long4)
          from ⟨Quiver.AffineE8.Arrow.long3⟩)
      | exact Or.inr (show Nonempty (Quiver.AffineE8.long3 ⟶ Quiver.AffineE8.long4)
          from ⟨Quiver.AffineE8.Arrow.long3⟩)
      | exact Or.inl (show Nonempty (Quiver.AffineE8.long4 ⟶ Quiver.AffineE8.long5)
          from ⟨Quiver.AffineE8.Arrow.long4⟩)
      | exact Or.inr (show Nonempty (Quiver.AffineE8.long4 ⟶ Quiver.AffineE8.long5)
          from ⟨Quiver.AffineE8.Arrow.long4⟩)
      | exact Or.inl (show Nonempty (Quiver.AffineE8.long5 ⟶ Quiver.AffineE8.center)
          from ⟨Quiver.AffineE8.Arrow.long5⟩)
      | exact Or.inr (show Nonempty (Quiver.AffineE8.long5 ⟶ Quiver.AffineE8.center)
          from ⟨Quiver.AffineE8.Arrow.long5⟩)
      | constructor <;> exact ⟨fun e => by cases e⟩

/-- The graph isomorphism acts on vertices by the explicit arm-coordinate equivalence. -/
@[simp]
theorem affineE8UnderlyingGraphIso_apply (v : Quiver.AffineE8) :
    affineE8UnderlyingGraphIso v = affineE8VertexEquiv v := (rfl)

/-- The trivalent vertex of the affine `E₈` quiver has zigzag graph label `0`. -/
@[simp]
theorem affineE8UnderlyingGraphIso_center :
    affineE8VertexEquiv Quiver.AffineE8.center = 0 := rfl

/-- The affine node is the endpoint of the arm of length five in the representation-quiver
labeling. -/
@[simp]
theorem affineE8UnderlyingGraphIso_long1 :
    affineE8VertexEquiv Quiver.AffineE8.long1 =
      Fin.cast (show AffineDynkinType.E8.nodes = 9 by rfl)
        AffineDynkinType.E8.affineNode := by
  apply Fin.ext
  rw [Fin.val_cast, AffineDynkinType.affineNode_E8]
  rfl

end TauCeti
