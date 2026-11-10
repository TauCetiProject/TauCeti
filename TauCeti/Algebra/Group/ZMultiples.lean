/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Lemmas

/-!
# `ℤ`-multiples of a non-torsion element

For an element `p` of an additive group that is not of finite additive order, the subgroup
`zmultiples p` of its `ℤ`-multiples is infinite cyclic: `n ↦ n • p` is an isomorphism
`ℤ ≃+ zmultiples p`. This generalizes Mathlib's `AddSubgroup.zmultiplesEquivInt`, which needs
the ambient group to be torsion-free. A homomorphism into a torsion-free additive group is
injective on `zmultiples p` whenever it is nonzero at `p`. If `n ↦ n • g` identifies `ℤ` with a
group `H`, then any element that an additive endomorphism of `H` sends to `g` is `g` up to a unit
of `ℤ`.

## Main declarations

* `TauCeti.intEquivZMultiples`: the isomorphism `ℤ ≃+ zmultiples p` for a non-torsion `p`.
* `AddMonoidHom.comp_zmultiples_subtype_injective`: injectivity on a cyclic subgroup when
  its generator has nonzero image in a torsion-free group.
* `AddMonoidHom.exists_eq_units_smul_of_map_eq`: in an infinite cyclic group with generator `g`,
  an element sent to `g` by an additive endomorphism is a unit multiple of `g`.
-/

public section

namespace TauCeti

open AddSubgroup

variable {G : Type*} [AddGroup G] {p : G}

/-- For an element `p` of infinite additive order, the subgroup `zmultiples p` is infinite
cyclic, identified with `ℤ` by `n ↦ n • p`. -/
noncomputable def intEquivZMultiples (hp : ¬ IsOfFinAddOrder p) : ℤ ≃+ zmultiples p :=
  (AddMonoidHom.ofInjective (f := zmultiplesHom G p)
    (injective_zsmul_iff_not_isOfFinAddOrder.2 hp)).trans
    (AddEquiv.addSubgroupCongr (range_zmultiplesHom p))

@[simp]
theorem intEquivZMultiples_apply (hp : ¬ IsOfFinAddOrder p) (n : ℤ) :
    (intEquivZMultiples hp n : G) = n • p :=
  (rfl)

@[simp]
theorem intEquivZMultiples_symm_mk_zsmul (hp : ¬ IsOfFinAddOrder p) (n : ℤ) :
    (intEquivZMultiples hp).symm ⟨n • p, zsmul_mem_zmultiples p n⟩ = n :=
  (intEquivZMultiples hp).symm_apply_eq.2 (Subtype.ext (by simp))

@[simp]
theorem intEquivZMultiples_symm_zsmul (hp : ¬ IsOfFinAddOrder p) (a : zmultiples p) :
    (intEquivZMultiples hp).symm a • p = (a : G) := by
  rw [← intEquivZMultiples_apply hp, AddEquiv.apply_symm_apply]

end TauCeti

namespace AddMonoidHom

/-- A homomorphism into a torsion-free additive group is injective on the subgroup generated
by any element with nonzero image. The source group need not be torsion-free. -/
theorem comp_zmultiples_subtype_injective {A B : Type*} [AddGroup A] [AddGroup B]
    [IsAddTorsionFree B] (f : A →+ B) {a : A} (ha : f a ≠ 0) :
    Function.Injective (f.comp (AddSubgroup.zmultiples a).subtype) := by
  rintro ⟨_, m, rfl⟩ ⟨_, n, rfl⟩ h
  obtain rfl : m = n := IsAddTorsionFree.zsmul_left_injective ha (by simpa using h)
  rfl

/-- If `k ↦ k • g` identifies `ℤ` with `H` and an additive endomorphism of `H` sends `x` to `g`,
then `g` is a unit multiple of `x`. -/
theorem exists_eq_units_smul_of_map_eq {H : Type*} [AddCommGroup H] (f : H →+ H) {g x : H}
    (hg : Function.Bijective fun k : ℤ ↦ k • g) (hx : f x = g) :
    ∃ ε : ℤˣ, g = (ε : ℤ) • x := by
  -- Write `x = m • g` and `f g = j • g`. Then `g = f x = (m * j) • g`, so `m * j = 1`.
  obtain ⟨m, rfl⟩ := hg.2 x
  obtain ⟨j, hj⟩ := hg.2 (f g)
  have hmj : m * j = 1 := hg.1 <| by
    simp only [mul_smul, hj, ← map_zsmul, hx, one_smul]
  exact ⟨Units.mkOfMulEqOne j m (by rw [mul_comm, hmj]), by simp [smul_smul, mul_comm j m, hmj]⟩

end AddMonoidHom
