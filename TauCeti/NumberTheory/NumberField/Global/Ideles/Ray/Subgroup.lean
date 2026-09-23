/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Ideles.Congruence

/-!
# Ray subgroups of the idele class group

Let `K` be a number field and `𝔪` a modulus.  The ray subgroup `raySubgroup 𝔪` is the
image in the idele class group of the ideles satisfying the finite and infinite congruence
conditions imposed by `𝔪`.  Thus an idele class belongs to the ray subgroup precisely when it
has a representative in `ideleCongruenceSubgroup 𝔪`.

The quotient map from ideles to idele classes is open.  Since the idele congruence subgroup is
open, its image is open as well.  The ray subgroups are antitone in the modulus: increasing the
finite exponents or adding real places imposes stronger conditions and gives a smaller subgroup.

The pullback of `raySubgroup 𝔪` to the idele group is the join of the idele congruence subgroup
and the principal ideles.  This is the form used to identify the kernel of the homomorphism from
idele classes to ray classes.

## Main definitions

* `TauCeti.GlobalNumberFields.raySubgroup`: the image of an idele congruence subgroup in the
  idele class group.

## Main results

* `TauCeti.GlobalNumberFields.mem_raySubgroup_iff`: membership through a congruence-idele
  representative.
* `TauCeti.GlobalNumberFields.mk_mem_raySubgroup_iff`: a class represented by an idele belongs
  precisely when that idele is in the join of the congruence subgroup and the principal ideles.
* `TauCeti.GlobalNumberFields.raySubgroup_antitone`: ray subgroups decrease when the modulus
  grows.
* `TauCeti.GlobalNumberFields.isOpen_raySubgroup`: every ray subgroup is open.

## References

* J. W. S. Cassels and A. Fröhlich, eds., *Algebraic Number Theory*, Chapter II, §17.
* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1.
-/

public section
noncomputable section

open IsDedekindDomain NumberField
open scoped NumberField

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-- **The ray subgroup of the idele class group**: the image of the ideles satisfying the
congruence conditions of `𝔪` under the quotient by the principal ideles. -/
def raySubgroup (𝔪 : Modulus K) : Subgroup (IdeleClassGroup (𝓞 K) K) :=
  Subgroup.map (QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 K) K))
    (ideleCongruenceSubgroup 𝔪)

/-- **Membership in a ray subgroup is represented by a congruence idele.** -/
theorem mem_raySubgroup_iff {𝔪 : Modulus K} {c : IdeleClassGroup (𝓞 K) K} :
    c ∈ raySubgroup 𝔪 ↔
      ∃ x : IdeleGroup (𝓞 K) K, x ∈ ideleCongruenceSubgroup 𝔪 ∧
        QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 K) K) x = c := by
  rw [raySubgroup, Subgroup.mem_map]

/-- **The pullback of a ray subgroup to the ideles.**  An idele represents a class in
`raySubgroup 𝔪` exactly when it belongs to the join of the congruence subgroup and the principal
ideles. -/
@[simp] theorem comap_raySubgroup (𝔪 : Modulus K) :
    (raySubgroup 𝔪).comap
        (QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 K) K)) =
      ideleCongruenceSubgroup 𝔪 ⊔ IdeleGroup.principalSubgroup (𝓞 K) K := by
  rw [raySubgroup, Subgroup.comap_map_eq, QuotientGroup.ker_mk']

/-- **Membership of an idele representative in a ray subgroup.**  The class of an idele lies in
`raySubgroup 𝔪` exactly when the idele differs from a congruence idele by a principal idele. -/
@[simp] theorem mk_mem_raySubgroup_iff {𝔪 : Modulus K} {x : IdeleGroup (𝓞 K) K} :
    (x : IdeleClassGroup (𝓞 K) K) ∈ raySubgroup 𝔪 ↔
      x ∈ ideleCongruenceSubgroup 𝔪 ⊔ IdeleGroup.principalSubgroup (𝓞 K) K := by
  rw [← QuotientGroup.mk'_apply, ← Subgroup.mem_comap, comap_raySubgroup]

/-- **Ray subgroups decrease when the modulus grows.** -/
theorem raySubgroup_antitone {𝔪 𝔫 : Modulus K} (h : 𝔪 ∣ 𝔫) :
    raySubgroup 𝔫 ≤ raySubgroup 𝔪 := by
  rw [raySubgroup, raySubgroup]
  exact Subgroup.map_mono (ideleCongruenceSubgroup_antitone h)

/-- **Every ray subgroup is open in the idele class group.** -/
theorem isOpen_raySubgroup (𝔪 : Modulus K) :
    IsOpen (raySubgroup 𝔪 : Set (IdeleClassGroup (𝓞 K) K)) := by
  rw [raySubgroup, Subgroup.coe_map, QuotientGroup.coe_mk']
  exact QuotientGroup.isOpenMap_coe _ (isOpen_ideleCongruenceSubgroup 𝔪)

end TauCeti.GlobalNumberFields
