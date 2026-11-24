/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
public import Mathlib.Topology.Homotopy.Product

/-!
# Pointwise products of paths, up to homotopy

A path `γ` in `X` from `a₁` to `a₂` and a path `δ` in `Y` from `b₁` to `b₂` give the path
`t ↦ (γ t, δ t)` in `X × Y` (`Path.prod`). It moves in both coordinates at once, and it is
homotopic to the path that first moves in `X` and then in `Y`
(`Path.Homotopic.prod_refl_trans_refl_prod`), and to the path that first moves in `Y` and then in
`X` (`Path.Homotopic.refl_prod_trans_prod_refl`): the square `I × I` can be crossed along its
diagonal or along two adjacent sides, either way round.

Composing with a continuous multiplication `X × X → X`, the same holds for the pointwise product
`t ↦ γ t * δ t` of two paths in `X` (`Path.mul`). When `X` has a two-sided unit `1`, multiplying
a path pointwise by the constant path at `1` does not change it. Hence if `γ` ends at `1` and `δ`
starts at `1`, their pointwise product is homotopic to `γ` followed by `δ`
(`Path.Homotopic.cast_mul_trans`), and if `δ` ends at `1` and `γ` starts at `1`, it is homotopic
to `δ` followed by `γ` (`Path.Homotopic.cast_mul_trans_swap`). For two loops at `1` the pointwise
product is therefore homotopic to their concatenation in either order. This compares the
pointwise product of loops in a topological group, or more generally in a topological space with
a continuous multiplication and a two-sided unit, with the group law of the fundamental group,
which is concatenation of loops.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.C, Exercise 5.
-/

public section

open scoped unitInterval

namespace Path

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

namespace Homotopic

variable {a₁ a₂ : X} {b₁ b₂ : Y}

/-- A path in a product that moves both coordinates at once is homotopic to the path that first
moves the first coordinate and then the second. -/
theorem prod_refl_trans_refl_prod (γ : Path a₁ a₂) (δ : Path b₁ b₂) :
    ((γ.prod (Path.refl b₁)).trans ((Path.refl a₂).prod δ)).Homotopic (γ.prod δ) := by
  rw [trans_prod_eq_prod_trans]
  exact ⟨prodHomotopy (Homotopy.transRefl γ) (Homotopy.reflTrans δ)⟩

/-- A path in a product that moves both coordinates at once is homotopic to the path that first
moves the second coordinate and then the first. -/
theorem refl_prod_trans_prod_refl (γ : Path a₁ a₂) (δ : Path b₁ b₂) :
    (((Path.refl a₁).prod δ).trans (γ.prod (Path.refl b₂))).Homotopic (γ.prod δ) := by
  rw [trans_prod_eq_prod_trans]
  exact ⟨prodHomotopy (Homotopy.reflTrans γ) (Homotopy.transRefl δ)⟩

end Homotopic

section Mul

variable [Mul X] [ContinuousMul X] {a₁ b₁ a₂ b₂ : X}

namespace Homotopic

/-- The pointwise product of two paths is homotopic to the path that first multiplies the first
path by the starting point of the second, and then multiplies the endpoint of the first by the
second path. -/
@[to_additive /-- The pointwise sum of two paths is homotopic to the path that first adds the
starting point of the second path to the first path, and then adds the second path to the endpoint
of the first. -/]
theorem mul_refl_trans_refl_mul (γ : Path a₁ b₁) (δ : Path a₂ b₂) :
    ((γ.mul (Path.refl a₂)).trans ((Path.refl b₁).mul δ)).Homotopic (γ.mul δ) := by
  simpa only [Path.mul, map_trans] using
    (prod_refl_trans_refl_prod γ δ).map ⟨fun x : X × X ↦ x.1 * x.2, continuous_mul⟩

/-- The pointwise product of two paths is homotopic to the path that first multiplies the
starting point of the first path by the second path, and then multiplies the first path by the
endpoint of the second. -/
@[to_additive /-- The pointwise sum of two paths is homotopic to the path that first adds the
second path to the starting point of the first, and then adds the endpoint of the second path to
the first path. -/]
theorem refl_mul_trans_mul_refl (γ : Path a₁ b₁) (δ : Path a₂ b₂) :
    (((Path.refl a₁).mul δ).trans (γ.mul (Path.refl b₂))).Homotopic (γ.mul δ) := by
  simpa only [Path.mul, map_trans] using
    (refl_prod_trans_prod_refl γ δ).map ⟨fun x : X × X ↦ x.1 * x.2, continuous_mul⟩

end Homotopic

end Mul

section MulOneClass

variable {M : Type*} [TopologicalSpace M] [MulOneClass M] [ContinuousMul M] {a b c : M}

namespace Homotopic

/-- **The pointwise product of paths through `1` is their concatenation.** If `γ` ends at `1`
and `δ` starts at `1`, the pointwise product `t ↦ γ t * δ t`, a path from `a * 1 = a` to
`1 * c = c`, is homotopic to `γ` followed by `δ`. -/
@[to_additive /-- **The pointwise sum of paths through `0` is their concatenation.** If `γ` ends
at `0` and `δ` starts at `0`, the pointwise sum `t ↦ γ t + δ t`, a path from `a + 0 = a` to
`0 + c = c`, is homotopic to `γ` followed by `δ`. -/]
theorem cast_mul_trans (γ : Path a 1) (δ : Path 1 c) :
    ((γ.mul δ).cast (mul_one a).symm (one_mul c).symm).Homotopic (γ.trans δ) := by
  have h : ((γ.mul (Path.refl 1)).trans ((Path.refl 1).mul δ)).cast (mul_one a).symm
      (one_mul c).symm = γ.trans δ := by
    ext t
    simp [trans_apply]
  rw [← h]
  exact ((mul_refl_trans_refl_mul γ δ).pathCast _ _).symm

/-- **The pointwise product of paths through `1`, in the other order.** If `γ` starts at `1`
and `δ` ends at `1`, the pointwise product `t ↦ γ t * δ t`, a path from `1 * a = a` to
`b * 1 = b`, is homotopic to `δ` followed by `γ`. -/
@[to_additive /-- **The pointwise sum of paths through `0`, in the other order.** If `γ` starts
at `0` and `δ` ends at `0`, the pointwise sum `t ↦ γ t + δ t`, a path from `0 + a = a` to
`b + 0 = b`, is homotopic to `δ` followed by `γ`. -/]
theorem cast_mul_trans_swap (γ : Path 1 b) (δ : Path a 1) :
    ((γ.mul δ).cast (one_mul a).symm (mul_one b).symm).Homotopic (δ.trans γ) := by
  have h : (((Path.refl 1).mul δ).trans (γ.mul (Path.refl 1))).cast (one_mul a).symm
      (mul_one b).symm = δ.trans γ := by
    ext t
    simp [trans_apply]
  rw [← h]
  exact ((refl_mul_trans_mul_refl γ δ).pathCast _ _).symm

end Homotopic

end MulOneClass

end Path
