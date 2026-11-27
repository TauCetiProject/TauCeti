/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Path

/-!
# Images of paths

Mathlib's `Path.map'` transports a path along a map that is only continuous on the range of the
path, and records the coercion of the image path only for its continuous special case
`Path.map` (`Path.map_coe`). This file supplies the corresponding statement for `Path.map'`.

It also records that a map carrying two composable paths onto two composable paths carries their
concatenation onto the concatenation of the images (`Path.comp_trans_eq_of_comp_eq`); unlike
`Path.map_trans`, the map need not be continuous. Continuous multiplicative maps preserve
pointwise path products, with endpoint transports, both for arbitrary paths and for loops at `1`.

## Main declarations

* `Path.map'_coe` -- the image path `γ.map' h` is the composite `f ∘ γ`.
* `Path.comp_trans_eq_of_comp_eq` -- if `f ∘ Γ = γ` and `f ∘ Γ' = γ'`, then
  `f ∘ Γ.trans Γ' = γ.trans γ'`.
* `Path.map_mul` -- mapping a pointwise product gives the pointwise product of the image paths.
* `Path.cast_map_cast_mul` -- the based-loop form for a map preserving the unit.
-/

public section

namespace Path

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x y : X}

/-- The image of a path along a map continuous on its range is the composite path. -/
@[simp, grind =]
theorem map'_coe (γ : Path x y) {f : X → Y} (h : ContinuousOn f (Set.range γ)) :
    ⇑(γ.map' h) = f ∘ γ :=
  rfl

/-- If `f` carries the path `Γ` onto `γ` and `Γ'` onto `γ'`, it carries the concatenation
`Γ.trans Γ'` onto `γ.trans γ'`. -/
theorem comp_trans_eq_of_comp_eq {z : X} {a b c : Y} {f : X → Y} {Γ : Path x y} {Γ' : Path y z}
    {γ : Path a b} {γ' : Path b c} (h : f ∘ Γ = γ) (h' : f ∘ Γ' = γ') :
    f ∘ Γ.trans Γ' = γ.trans γ' := by
  funext t
  simp only [Function.comp_apply, trans_apply, apply_dite f, ← h, ← h']

/-- A continuous multiplicative map preserves pointwise path products, after transporting the
endpoints along the multiplicativity equalities. -/
@[to_additive /-- A continuous additive map preserves pointwise path sums, after transporting the
endpoints along the additivity equalities. -/]
theorem map_mul [Mul X] [ContinuousMul X] [Mul Y] [ContinuousMul Y]
    {a₁ b₁ a₂ b₂ : X} (γ : Path a₁ b₁) (δ : Path a₂ b₂) {f : X → Y}
    (hf : Continuous f) (hmul : ∀ a b, f (a * b) = f a * f b) :
    (γ.mul δ).map hf = ((γ.map hf).mul (δ.map hf)).cast (hmul a₁ a₂) (hmul b₁ b₂) := by
  ext t
  simp [hmul]

/-- A unit-preserving continuous multiplicative map preserves pointwise products of loops based
at the unit, including the transports back to the unit. -/
@[to_additive /-- A zero-preserving continuous additive map preserves pointwise sums of loops
based at zero, including the transports back to zero. -/]
theorem cast_map_cast_mul [MulOneClass X] [ContinuousMul X] [MulOneClass Y] [ContinuousMul Y]
    (γ δ : Path (1 : X) 1) {f : X → Y} (hf : Continuous f) (h₁ : f 1 = 1)
    (hmul : ∀ a b, f (a * b) = f a * f b) :
    (((γ.mul δ).cast (mul_one 1).symm (mul_one 1).symm).map hf).cast h₁.symm h₁.symm =
      (((γ.map hf).cast h₁.symm h₁.symm).mul ((δ.map hf).cast h₁.symm h₁.symm)).cast
        (mul_one 1).symm (mul_one 1).symm := by
  ext t
  simpa only [cast_coe, map_coe, Function.comp_apply, Path.mul_apply] using
    DFunLike.congr_fun (γ.map_mul δ hf hmul) t

end Path

end
