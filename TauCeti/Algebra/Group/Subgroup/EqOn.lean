/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Subgroup.Map
import TauCeti.GroupTheory.ConjugationTransfer

/-!
# Maps agreeing on a subgroup

Two monoid homomorphisms that agree on a submonoid `S` have the same image of `S`; in particular
two group homomorphisms that agree on a subgroup `H` have the same image of `H`. If an
endomorphism `f` of a group agrees on a set `s` with the inner automorphism by `c`, then on each
conjugate `w s w⁻¹` it agrees with the inner automorphism by `f(w) c w⁻¹`, because
`f(w k w⁻¹) = f(w) (c k c⁻¹) f(w)⁻¹` for `k ∈ s`. So an endomorphism that agrees with an inner
automorphism on a subgroup `K` does so on every conjugate of `K`, and carries it to a conjugate of
itself.

## Main results

* `Set.EqOn.submonoid_map_eq`, `Set.EqOn.subgroup_map_eq`: homomorphisms agreeing on `S` or `H`
  have the same image of it.
* `Set.EqOn.map_conj`: agreement with an inner automorphism on `s` passes to the conjugates of `s`.
-/

public section

/-- Two monoid homomorphisms that agree on a submonoid `S` have the same image of `S`. -/
theorem Set.EqOn.submonoid_map_eq {M N F F' : Type*} [MulOneClass M] [MulOneClass N]
    [FunLike F M N] [MonoidHomClass F M N] [FunLike F' M N] [MonoidHomClass F' M N] {f : F}
    {g : F'} {S : Submonoid M} (h : Set.EqOn f g S) : S.map f = S.map g :=
  SetLike.coe_injective (by simpa only [Submonoid.coe_map] using h.image_eq)

variable {G N : Type*} [Group G] [Group N]

/-- Two homomorphisms that agree on a subgroup `H` have the same image of `H`. -/
theorem Set.EqOn.subgroup_map_eq {F F' : Type*} [FunLike F G N] [MonoidHomClass F G N]
    [FunLike F' G N] [MonoidHomClass F' G N] {f : F} {g : F'} {H : Subgroup G}
    (h : Set.EqOn f g H) : H.map (f : G →* N) = H.map (g : G →* N) := by
  refine Subgroup.toSubmonoid_injective ?_
  rw [Subgroup.map_toSubmonoid, Subgroup.map_toSubmonoid]
  exact Set.EqOn.submonoid_map_eq (f := (f : G →* N)) (g := (g : G →* N)) h

/-- If an endomorphism `f` agrees on a set `s` with the inner automorphism by `c`, then on the
conjugate `w s w⁻¹` it agrees with the inner automorphism by `f(w) c w⁻¹`. -/
theorem Set.EqOn.map_conj {F : Type*} [FunLike F G G] [MonoidHomClass F G G] {f : F} {c : G}
    {s : Set G} (h : Set.EqOn f (MulAut.conj c) s) (w : G) :
    Set.EqOn f (MulAut.conj (f w * c * w⁻¹)) (MulAut.conj w '' s) := by
  rintro _ ⟨k, hk, rfl⟩
  have hw := TauCeti.map_conj_eq_conj_of_map_eq_conj f id (q := w) (c := c⁻¹) rfl
    (by simpa [MulAut.conj_apply] using h hk)
  simpa [MulAut.conj_apply, mul_assoc] using hw
