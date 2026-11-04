/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# `ℤ`-multiples of a non-torsion element

For an element `p` of an additive group that is not of finite additive order, the subgroup
`zmultiples p` of its `ℤ`-multiples is infinite cyclic: `n ↦ n • p` is an isomorphism
`ℤ ≃+ zmultiples p`. This applies Mathlib's `intEquivOfZMultiplesEqTop` to the subgroup
`zmultiples p` itself. A homomorphism into a torsion-free additive group is injective on
`zmultiples p` whenever it is nonzero at `p`.

## Main declarations

* `TauCeti.intEquivZMultiples`: the isomorphism `ℤ ≃+ zmultiples p` for a non-torsion `p`.
* `AddMonoidHom.comp_zmultiples_subtype_injective`: injectivity on a cyclic subgroup when
  its generator has nonzero image in a torsion-free group.
-/

public section

namespace TauCeti

open AddSubgroup

variable {G : Type*} [AddGroup G] {p : G}

/-- For an element `p` of infinite additive order, the subgroup `zmultiples p` is infinite
cyclic, identified with `ℤ` by `n ↦ n • p`. -/
noncomputable def intEquivZMultiples (hp : ¬ IsOfFinAddOrder p) : ℤ ≃+ zmultiples p :=
  let q : zmultiples p := ⟨p, mem_zmultiples_iff.2 ⟨1, by simp⟩⟩
  haveI : Infinite (zmultiples p) := infinite_zmultiples.2 hp
  intEquivOfZMultiplesEqTop q <| by
    ext x
    constructor
    · intro _
      trivial
    · intro _
      obtain ⟨n, hn⟩ := mem_zmultiples_iff.1 x.2
      exact mem_zmultiples_iff.2 ⟨n, by ext; exact hn⟩

@[simp]
theorem intEquivZMultiples_apply (hp : ¬ IsOfFinAddOrder p) (n : ℤ) :
    (intEquivZMultiples hp n : G) = n • p :=
  by simp [intEquivZMultiples]

@[simp]
theorem intEquivZMultiples_symm_mk_zsmul (hp : ¬ IsOfFinAddOrder p) (n : ℤ) :
    (intEquivZMultiples hp).symm
      ⟨n • p, mem_zmultiples_iff.2 ⟨n, rfl⟩⟩ = n := by
  have h : intEquivZMultiples hp n = ⟨n • p, mem_zmultiples_iff.2 ⟨n, rfl⟩⟩ := by
    ext
    simp
  rw [← h]
  simp

theorem intEquivZMultiples_symm_zsmul (hp : ¬ IsOfFinAddOrder p) (a : zmultiples p) :
    ((intEquivZMultiples hp).symm a) • p = (a : G) := by
  rw [← intEquivZMultiples_apply hp ((intEquivZMultiples hp).symm a)]
  simp

end TauCeti

namespace AddMonoidHom

/-- A homomorphism into a torsion-free additive group is injective on the subgroup generated
by any element with nonzero image. The source group need not be torsion-free. -/
theorem comp_zmultiples_subtype_injective {A B : Type*} [AddGroup A] [AddGroup B]
    [IsAddTorsionFree B] (f : A →+ B) {a : A} (ha : f a ≠ 0) :
    Function.Injective (f.comp (AddSubgroup.zmultiples a).subtype) := by
  intro x y hxy
  obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.1 x.property
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.1 y.property
  have hmn : m = n := IsAddTorsionFree.zsmul_left_injective ha (by
    simpa only [comp_apply, AddSubgroup.subtype_apply, ← hm, ← hn, map_zsmul] using hxy)
  exact Subtype.ext (hm.symm.trans (hmn ▸ hn))

end AddMonoidHom
