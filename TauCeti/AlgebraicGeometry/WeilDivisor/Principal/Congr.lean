/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.Principal.Basic

/-!
# Transporting divisor class groups along a reindexing of points

Let `S` be an order system on points `X` with functions `G`, and `T` an order system on points
`Y` with functions `H`. An equivalence `e : X ≃ Y` reindexes Weil divisors by
`Finsupp.domCongr e`. Suppose that, for an additive equivalence `φ : G ≃+ H`, reindexing carries
the principal divisor of every `g : G` to the principal divisor of `φ g`. Then reindexing carries
the principal divisors of `S` onto those of `T`, so it descends to an isomorphism of divisor class
groups `S.ClassGroup ≃+ T.ClassGroup`. If weights `v` on `X` and `w` on `Y` correspond under `e`,
the isomorphism preserves weighted degrees and restricts to an isomorphism of the degree-zero
parts `S.picZero v ≃+ T.picZero w`.

This is the mechanism for comparing divisor class groups of two models of one curve: for
instance, the codimension-one points of a curve and the places of its function field, or the
places of two isomorphic function fields.

## Main declarations

* `WeilDivisor.OrderSystem.classGroupCongr`: the induced isomorphism of divisor class groups;
* `WeilDivisor.OrderSystem.picZeroCongr`: its restriction to the degree-zero parts.
-/

public section

namespace TauCeti

namespace AlgebraicGeometry

namespace WeilDivisor

variable {X Y : Type*}

namespace OrderSystem

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H] {S : OrderSystem X G}
  {T : OrderSystem Y H} (e : X ≃ Y) (φ : G ≃+ H)
  (h : ∀ g, Finsupp.domCongr e (S.principalDivisor g) = T.principalDivisor (φ g))

include h in
/-- Reindexing along `e` carries the principal divisors of `S` onto those of `T`, when it carries
the principal divisor of each `g` to that of `φ g`. -/
lemma map_domCongr_principalSubgroup :
    S.principalSubgroup.map (Finsupp.domCongr e : WeilDivisor X ≃+ WeilDivisor Y).toAddMonoidHom =
      T.principalSubgroup := by
  ext D
  simp only [AddSubgroup.mem_map, mem_principalSubgroup, AddEquiv.coe_toAddMonoidHom]
  constructor
  · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
    exact ⟨φ g, (h g).symm⟩
  · rintro ⟨g, rfl⟩
    exact ⟨_, ⟨φ.symm g, rfl⟩, by rw [h, φ.apply_symm_apply]⟩

/-- **Transport of divisor class groups.** If reindexing Weil divisors along `e : X ≃ Y` carries
the principal divisor of every `g` to the principal divisor of `φ g`, it induces an isomorphism
`S.ClassGroup ≃+ T.ClassGroup`. -/
noncomputable def classGroupCongr : S.ClassGroup ≃+ T.ClassGroup :=
  QuotientAddGroup.congr _ _ (Finsupp.domCongr e) (map_domCongr_principalSubgroup e φ h)

/-- `classGroupCongr` sends the class of `D` to the class of its reindexing. -/
@[simp]
lemma classGroupCongr_divisorClass (D : WeilDivisor X) :
    classGroupCongr e φ h (S.divisorClass D) = T.divisorClass (Finsupp.domCongr e D) := by
  rw [divisorClass_eq_mk', divisorClass_eq_mk']
  -- `QuotientAddGroup.congr` acts on a class by applying the equivalence to a representative;
  -- Mathlib states this only for multiplicative quotients (`QuotientGroup.congr_mk`).
  rfl

/-- The inverse of `classGroupCongr` sends the class of `D` to the class of its reindexing along
`e.symm`. -/
@[simp]
lemma classGroupCongr_symm_divisorClass (D : WeilDivisor Y) :
    (classGroupCongr e φ h).symm (T.divisorClass D) =
      S.divisorClass ((Finsupp.domCongr e).symm D) := by
  rw [divisorClass_eq_mk', divisorClass_eq_mk']
  -- As above, the inverse of `QuotientAddGroup.congr` applies the inverse equivalence to a
  -- representative (`QuotientGroup.congr_symm` in the multiplicative setting).
  rfl

variable {v : X → ℤ} {w : Y → ℤ} (hv : S.IsWeightedDegreeZero v) (hw : T.IsWeightedDegreeZero w)
  (hvw : ∀ x, w (e x) = v x)

include hvw in
/-- `classGroupCongr` preserves the weighted degree of divisor classes, for weights that
correspond under `e`. -/
lemma weightedDegreeClass_classGroupCongr (c : S.ClassGroup) :
    weightedDegreeClass w hw (classGroupCongr e φ h c) = weightedDegreeClass v hv c := by
  obtain ⟨D, rfl⟩ := S.divisorClass_surjective c
  rw [classGroupCongr_divisorClass, weightedDegreeClass_divisorClass,
    weightedDegreeClass_divisorClass, Finsupp.domCongr_apply, Finsupp.equivMapDomain_eq_mapDomain,
    ← pushforward_apply, weightedDegree_pushforward]
  exact congrArg (weightedDegree · D) (funext hvw)

include hvw in
/-- `classGroupCongr` carries the degree-zero part of `S` onto that of `T`. -/
lemma map_picZero_classGroupCongr :
    (picZero v hv).map (classGroupCongr e φ h).toAddMonoidHom = picZero w hw := by
  ext c
  rw [AddSubgroup.mem_map_equiv, mem_picZero, mem_picZero, ← weightedDegreeClass_classGroupCongr
    e φ h hv hw hvw, AddEquiv.apply_symm_apply]

/-- **Transport of the degree-zero part of the class group.** The isomorphism `classGroupCongr`
restricts to an isomorphism `S.picZero v ≃+ T.picZero w` for weights that correspond under `e`. -/
noncomputable def picZeroCongr : picZero v hv ≃+ picZero w hw :=
  ((classGroupCongr e φ h).addSubgroupMap _).trans
    (AddEquiv.addSubgroupCongr (map_picZero_classGroupCongr e φ h hv hw hvw))

/-- `picZeroCongr` is the restriction of `classGroupCongr`. -/
@[simp]
lemma coe_picZeroCongr_apply (c : picZero v hv) :
    (picZeroCongr e φ h hv hw hvw c : T.ClassGroup) = classGroupCongr e φ h c :=
  (rfl)

/-- The inverse of `picZeroCongr` is the restriction of the inverse of `classGroupCongr`. -/
@[simp]
lemma coe_picZeroCongr_symm_apply (c : picZero w hw) :
    ((picZeroCongr e φ h hv hw hvw).symm c : S.ClassGroup) = (classGroupCongr e φ h).symm c :=
  (rfl)

end OrderSystem

end WeilDivisor

end AlgebraicGeometry

end TauCeti
