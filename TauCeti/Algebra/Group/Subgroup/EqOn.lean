/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Subgroup.Map

/-!
# Maps agreeing on a subgroup

Two homomorphisms that agree on a subgroup `H` have the same image of `H`. If an endomorphism `f`
of a group agrees on a subgroup `K` with the inner automorphism by `c`, then on each conjugate
`w K w⁻¹` it agrees with the inner automorphism by `f(w) c w⁻¹`, because
`f(w k w⁻¹) = f(w) (c k c⁻¹) f(w)⁻¹` for `k ∈ K`. So an endomorphism that agrees with an inner
automorphism on `K` does so on every conjugate of `K`, and carries it to a conjugate of itself.

## Main results

* `Subgroup.map_eq_map_of_eqOn`: homomorphisms agreeing on `H` have the same image of `H`.
* `Set.EqOn.map_conj`: agreement with an inner automorphism on `K` passes to the conjugates of `K`.
-/

public section

variable {G N : Type*} [Group G] [Group N]

/-- Two homomorphisms that agree on a subgroup `H` have the same image of `H`. -/
theorem Subgroup.map_eq_map_of_eqOn {f g : G →* N} {H : Subgroup G} (h : Set.EqOn f g H) :
    H.map f = H.map g :=
  SetLike.coe_injective (by simpa only [Subgroup.coe_map] using h.image_eq)

/-- If an endomorphism `f` agrees on a subgroup `K` with the inner automorphism by `c`, then on the
conjugate `w K w⁻¹` it agrees with the inner automorphism by `f(w) c w⁻¹`. -/
theorem Set.EqOn.map_conj {F : Type*} [FunLike F G G] [MonoidHomClass F G G] {f : F} {c : G}
    {K : Subgroup G} (h : Set.EqOn f (MulAut.conj c) K) (w : G) :
    Set.EqOn f (MulAut.conj (f w * c * w⁻¹)) (K.map (MulAut.conj w : G →* G)) := by
  rintro _ ⟨k, hk, rfl⟩
  simp [MulAut.conj_apply, h hk, mul_assoc]
