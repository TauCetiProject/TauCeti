/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.ClassNumber
public import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.One
public import TauCeti.NumberTheory.NumberField.Global.Ideles.Ray.ClassQuotient

import Mathlib.Topology.Algebra.OpenSubgroup
import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Compact
import TauCeti.NumberTheory.NumberField.Global.Ideles.IdentityComponent

/-!
# Ray class groups as finite quotients of the norm-one idele class group

Let `K` be a number field, `C_K` its idele class group and `C_K¹ = IdeleClassGroup.normOne K` the
norm-one idele class group.  For a modulus `𝔪`, the ray class map
`rayClassQuotient 𝔪 : C_K → Cl_𝔪` is surjective with kernel the open ray subgroup `U_𝔪`.

This file shows that the ray class map is already surjective on `C_K¹`: the ray subgroup contains
the identity component of `C_K`, whose idele class norms exhaust `ℝ>0`, so `U_𝔪 · C_K¹ = C_K`.
Hence

`C_K¹ / (U_𝔪 ∩ C_K¹) ≃* Cl_𝔪`,

and since `U_𝔪 ∩ C_K¹` is an open subgroup of the compact group `C_K¹`, it has finite index.  This
is the adelic route to the finiteness of the ray class groups, and in particular of the ideal class
group: at the trivial modulus, the class number of `K` is the index of `U_1 ∩ C_K¹` in `C_K¹`.

The compactness of `C_K¹` (`IdeleClassGroup.isCompact_normOne`) is itself proved from the
finiteness of the class group and Dirichlet's unit theorem, so the statements here are agreement
results between the idelic and the ideal-theoretic descriptions, not an independent proof of
finiteness.

## Main results

* `TauCeti.GlobalNumberFields.IdeleClassGroup.raySubgroup_sup_normOne`: every idele class is the
  product of an element of the ray subgroup and a norm-one idele class.
* `TauCeti.GlobalNumberFields.IdeleClassGroup.rayClassQuotient_domRestrict_normOne_surjective`:
  the ray class map is surjective on the norm-one idele class group.
* `TauCeti.GlobalNumberFields.IdeleClassGroup.isFiniteRelIndex_raySubgroup_normOne`: the ray
  subgroup has finite index in the norm-one idele class group, by compactness.
* `TauCeti.GlobalNumberFields.IdeleClassGroup.normOneQuotientEquivRayClassGroup`: the ray class
  group is the quotient of the norm-one idele class group by its intersection with the ray
  subgroup.
* `TauCeti.GlobalNumberFields.IdeleClassGroup.relIndex_raySubgroup_normOne` and
  `TauCeti.GlobalNumberFields.IdeleClassGroup.index_raySubgroup`: the order of the ray class group
  is the index of the ray subgroup, in `C_K¹` and in `C_K`.
* `TauCeti.GlobalNumberFields.IdeleClassGroup.classNumber_eq_relIndex_raySubgroup_normOne`: the
  class number is the index of the ray subgroup of the trivial modulus in `C_K¹`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1, Theorem 1.6 and its proof.
* J. W. S. Cassels and A. Fröhlich, eds., *Algebraic Number Theory*, Chapter II, §16.
-/

public section

open NumberField

namespace TauCeti.GlobalNumberFields.IdeleClassGroup

variable {K : Type*} [Field K] [NumberField K]

/-- Every idele class differs from a norm-one idele class by an element of the ray subgroup,
namely an element of the identity component with the same idele class norm. -/
private theorem _root_.IdeleClassGroup.exists_mem_raySubgroup_inv_mul_mem_normOne (𝔪 : Modulus K)
    (c : IdeleClassGroup (𝓞 K) K) : ∃ d ∈ raySubgroup 𝔪, d⁻¹ * c ∈ normOne K := by
  obtain ⟨d, hd, hdc⟩ :=
    exists_mem_connectedComponentOfOne_ideleClassNorm_eq (K := K) (ideleClassNorm c)
  refine ⟨d, connectedComponentOfOne_le_raySubgroup 𝔪 hd, ?_⟩
  rw [mem_normOne_iff, map_mul, map_inv, hdc, inv_mul_cancel]

/-- **Every idele class is a ray-subgroup element times a norm-one idele class.**  The ray
subgroup contains the identity component of the idele class group, on which the idele class norm
takes every positive real value. -/
theorem raySubgroup_sup_normOne (𝔪 : Modulus K) : raySubgroup 𝔪 ⊔ normOne K = ⊤ := by
  refine eq_top_iff.mpr fun c _ ↦ ?_
  obtain ⟨d, hd, hdc⟩ := IdeleClassGroup.exists_mem_raySubgroup_inv_mul_mem_normOne 𝔪 c
  rw [← mul_inv_cancel_left d c]
  exact Subgroup.mul_mem_sup hd hdc

/-- **The ray class map is surjective on the norm-one idele class group.** -/
theorem rayClassQuotient_domRestrict_normOne_surjective (𝔪 : Modulus K) :
    Function.Surjective ((rayClassQuotient 𝔪).domRestrict (normOne K)) := by
  intro x
  obtain ⟨c, rfl⟩ := rayClassQuotient_surjective 𝔪 x
  obtain ⟨d, hd, hdc⟩ := IdeleClassGroup.exists_mem_raySubgroup_inv_mul_mem_normOne 𝔪 c
  rw [← ker_rayClassQuotient, MonoidHom.mem_ker] at hd
  exact ⟨⟨d⁻¹ * c, hdc⟩, by rw [MonoidHom.domRestrict_apply, map_mul, map_inv, hd, inv_one,
    one_mul]⟩

/-- **The ray subgroup has finite index in the norm-one idele class group**: its intersection with
`C_K¹` is an open subgroup of the compact group `C_K¹`. -/
instance isFiniteRelIndex_raySubgroup_normOne (𝔪 : Modulus K) :
    (raySubgroup 𝔪).IsFiniteRelIndex (normOne K) := by
  rw [Subgroup.isFiniteRelIndex_iff_finiteIndex]
  have := Subgroup.quotient_finite_of_isOpen ((raySubgroup 𝔪).subgroupOf (normOne K))
    ((isOpen_raySubgroup 𝔪).preimage continuous_subtype_val)
  exact Subgroup.finiteIndex_of_finite_quotient

/-- **The ray class group is a quotient of the norm-one idele class group**: the ray class map
identifies `C_K¹ / (U_𝔪 ∩ C_K¹)` with the ray class group of `𝔪`. -/
noncomputable def normOneQuotientEquivRayClassGroup (𝔪 : Modulus K) :
    normOne K ⧸ (raySubgroup 𝔪).subgroupOf (normOne K) ≃* RayClassGroup 𝔪 :=
  (QuotientGroup.quotientMulEquivOfEq
    (by rw [MonoidHom.ker_domRestrict, ker_rayClassQuotient])).trans
    (QuotientGroup.quotientKerEquivOfSurjective _
      (rayClassQuotient_domRestrict_normOne_surjective 𝔪))

/-- The identification of `C_K¹ / (U_𝔪 ∩ C_K¹)` with the ray class group sends the class of a
norm-one idele class to its ray class. -/
@[simp]
theorem normOneQuotientEquivRayClassGroup_mk (𝔪 : Modulus K) (c : normOne K) :
    normOneQuotientEquivRayClassGroup 𝔪 (c : normOne K ⧸ (raySubgroup 𝔪).subgroupOf (normOne K)) =
      rayClassQuotient 𝔪 c := by
  rw [normOneQuotientEquivRayClassGroup, MulEquiv.trans_apply,
    QuotientGroup.quotientMulEquivOfEq_mk, QuotientGroup.quotientKerEquivOfSurjective,
    QuotientGroup.quotientKerEquivOfRightInverse_apply, QuotientGroup.kerLift_mk,
    MonoidHom.domRestrict_apply]

/-- The order of the ray class group is the index of the ray subgroup in the norm-one idele class
group. -/
theorem relIndex_raySubgroup_normOne (𝔪 : Modulus K) :
    (raySubgroup 𝔪).relIndex (normOne K) = Nat.card (RayClassGroup 𝔪) :=
  Nat.card_congr (normOneQuotientEquivRayClassGroup 𝔪).toEquiv

/-- The order of the ray class group is the index of the ray subgroup in the idele class group. -/
theorem index_raySubgroup (𝔪 : Modulus K) :
    (raySubgroup 𝔪).index = Nat.card (RayClassGroup 𝔪) := by
  rw [← relIndex_raySubgroup_normOne, ← Subgroup.relIndex_top_right, ← raySubgroup_sup_normOne 𝔪,
    Subgroup.relIndex_sup_left (normOne K) (raySubgroup 𝔪)]

variable (K) in
/-- **The class number is an idelic index**: it is the index in the norm-one idele class group of
the ray subgroup of the trivial modulus, which is finite by compactness of `C_K¹`. -/
theorem classNumber_eq_relIndex_raySubgroup_normOne :
    classNumber K = (raySubgroup (Modulus.one K)).relIndex (normOne K) := by
  rw [relIndex_raySubgroup_normOne, classNumber, ← Nat.card_eq_fintype_card,
    Nat.card_congr (oneEquivClassGroup (K := K)).toEquiv]

end TauCeti.GlobalNumberFields.IdeleClassGroup
