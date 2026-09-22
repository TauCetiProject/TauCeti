/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Ideles.Congruence

/-!
# Ray subgroups of the idele class group

Let `K` be a number field and `𝔪` a modulus.  The ray subgroup `RaySubgroup 𝔪` is the
image in the idele class group of the ideles satisfying the finite and infinite congruence
conditions imposed by `𝔪`.  Thus an idele class belongs to the ray subgroup precisely when it
has a representative in `ideleCongruenceSubgroup 𝔪`.

The quotient map from ideles to idele classes is open.  Since the idele congruence subgroup is
open, its image is open as well.  The ray subgroups are antitone in the modulus: increasing the
finite exponents or adding real places imposes stronger conditions and gives a smaller subgroup.

The pullback of `RaySubgroup 𝔪` to the idele group is the join of the idele congruence subgroup
and the principal ideles.  This is the form used to identify the kernel of the homomorphism from
idele classes to ray classes.

## Main definitions

* `TauCeti.GlobalNumberFields.RaySubgroup`: the image of an idele congruence subgroup in the
  idele class group.

## Main results

* `TauCeti.GlobalNumberFields.mem_RaySubgroup_iff`: membership through a congruence-idele
  representative.
* `TauCeti.GlobalNumberFields.mk_mem_RaySubgroup_iff`: a class represented by an idele belongs
  precisely when that idele is in the join of the congruence subgroup and the principal ideles.
* `TauCeti.GlobalNumberFields.RaySubgroup_antitone`: ray subgroups decrease when the modulus
  grows.
* `TauCeti.GlobalNumberFields.isOpen_RaySubgroup`: every ray subgroup is open.

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
def RaySubgroup (𝔪 : Modulus K) : Subgroup (IdeleClassGroup (𝓞 K) K) :=
  Subgroup.map (QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 K) K))
    (ideleCongruenceSubgroup 𝔪)

/-- A ray subgroup is the image of the corresponding idele congruence subgroup. -/
theorem RaySubgroup_eq_map (𝔪 : Modulus K) :
    RaySubgroup 𝔪 =
      Subgroup.map (QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 K) K))
        (ideleCongruenceSubgroup 𝔪) :=
  (rfl)

/-- **Membership in a ray subgroup is represented by a congruence idele.** -/
theorem mem_RaySubgroup_iff {𝔪 : Modulus K} {c : IdeleClassGroup (𝓞 K) K} :
    c ∈ RaySubgroup 𝔪 ↔
      ∃ x : IdeleGroup (𝓞 K) K, x ∈ ideleCongruenceSubgroup 𝔪 ∧
        QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 K) K) x = c := by
  rw [RaySubgroup_eq_map, Subgroup.mem_map]

/-- **The pullback of a ray subgroup to the ideles.**  An idele represents a class in
`RaySubgroup 𝔪` exactly when it belongs to the join of the congruence subgroup and the principal
ideles. -/
theorem comap_RaySubgroup (𝔪 : Modulus K) :
    (RaySubgroup 𝔪).comap
        (QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 K) K)) =
      ideleCongruenceSubgroup 𝔪 ⊔ IdeleGroup.principalSubgroup (𝓞 K) K := by
  rw [RaySubgroup_eq_map, Subgroup.comap_map_eq, QuotientGroup.ker_mk']

/-- **Membership of an idele representative in a ray subgroup.**  The class of an idele lies in
`RaySubgroup 𝔪` exactly when the idele differs from a congruence idele by a principal idele. -/
@[simp] theorem mk_mem_RaySubgroup_iff {𝔪 : Modulus K} {x : IdeleGroup (𝓞 K) K} :
    QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 K) K) x ∈ RaySubgroup 𝔪 ↔
      x ∈ ideleCongruenceSubgroup 𝔪 ⊔ IdeleGroup.principalSubgroup (𝓞 K) K := by
  rw [← Subgroup.mem_comap, comap_RaySubgroup]

/-- **Ray subgroups decrease when the modulus grows.** -/
theorem RaySubgroup_antitone {𝔪 𝔫 : Modulus K} (h : 𝔪 ∣ 𝔫) :
    RaySubgroup 𝔫 ≤ RaySubgroup 𝔪 := by
  rw [RaySubgroup_eq_map, RaySubgroup_eq_map]
  exact Subgroup.map_mono (ideleCongruenceSubgroup_antitone h)

/-- **Every ray subgroup is open in the idele class group.** -/
theorem isOpen_RaySubgroup (𝔪 : Modulus K) :
    IsOpen (RaySubgroup 𝔪 : Set (IdeleClassGroup (𝓞 K) K)) := by
  rw [RaySubgroup_eq_map, Subgroup.coe_map, QuotientGroup.coe_mk']
  exact QuotientGroup.isOpenMap_coe _ (isOpen_ideleCongruenceSubgroup 𝔪)

end TauCeti.GlobalNumberFields
