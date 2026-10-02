/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.One
public import TauCeti.NumberTheory.NumberField.Global.Ideles.Ray.Subgroup
public import TauCeti.Topology.Algebra.Group.Connected

import Mathlib.Topology.Algebra.ClopenNhdofOne
import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Compact
import TauCeti.NumberTheory.NumberField.Global.Ideles.Ray.OpenSubgroup

/-!
# The identity component of the idele class group

Let `K` be a number field and let `D_K = Subgroup.connectedComponentOfOne C_K` be the connected
component of the identity in the idele class group `C_K`.  This file shows that `D_K` is exactly
the part of `C_K` that no ray class group sees, and that the quotient `C_K / D_K` is a profinite
group.

* Every ray subgroup is open, hence contains `D_K`.
* The ideles concentrated at one infinite place with positive real components lie in `D_K`, and
  their idele norms exhaust `ℝ>0`.  Hence `C_K = C_K¹ · D_K`, and `C_K / D_K` is a continuous
  image of the compact norm-one idele class group `C_K¹`.
* `D_K` is a closed normal subgroup, so `C_K / D_K` is Hausdorff, and the quotient of a
  topological group by its identity component is totally disconnected.  Together with
  compactness, these instances make `C_K / D_K` a profinite group (`ProfiniteGrp.of` applies).
* Since the open subgroups of the profinite group `C_K / D_K` separate its points, and every open
  subgroup of `C_K` contains a ray subgroup, `D_K` is the intersection of all ray subgroups.

## Main results

* `TauCeti.GlobalNumberFields.connectedComponentOfOne_le_raySubgroup`: the identity component
  lies in every ray subgroup.
* `TauCeti.GlobalNumberFields.IdeleClassGroup.exists_mem_connectedComponentOfOne_ideleClassNorm_eq`:
  every positive real number is the idele class norm of an element of the identity component.
* `TauCeti.GlobalNumberFields.IdeleClassGroup.compactSpace_quotient_connectedComponentOfOne`:
  the quotient of `C_K` by its identity component is compact.
* `TauCeti.GlobalNumberFields.iInf_raySubgroup`: the intersection of all ray subgroups is the
  identity component.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter IX.
-/

public section

open IsDedekindDomain NumberField NumberField.InfinitePlace
open scoped NumberField NNReal

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-- **The identity component of the idele class group lies in every ray subgroup**: a ray
subgroup is open, hence also closed. -/
theorem connectedComponentOfOne_le_raySubgroup (𝔪 : Modulus K) :
    Subgroup.connectedComponentOfOne (IdeleClassGroup (𝓞 K) K) ≤ raySubgroup 𝔪 :=
  Subgroup.connectedComponentOfOne_le_of_isOpen (isOpen_raySubgroup 𝔪)

namespace IdeleClassGroup

/-- **The idele class norm is surjective on the identity component**: every positive real number
is the idele class norm of an element of the identity component of the idele class group, namely
of an idele concentrated at one infinite place with positive real component. -/
theorem exists_mem_connectedComponentOfOne_ideleClassNorm_eq (t : ℝ≥0ˣ) :
    ∃ d ∈ Subgroup.connectedComponentOfOne (IdeleClassGroup (𝓞 K) K), ideleClassNorm d = t := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace K))
  -- An element `x` of normalized absolute value `√t`; its square `x * x` has absolute value `t`
  -- and is positive at a real place.
  obtain ⟨x, hx⟩ := exists_infiniteCompletionNormalizedAbsValue_eq w
    (Real.sqrt_nonneg ((t : ℝ≥0) : ℝ))
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero, eq_comm, Real.sqrt_eq_zero (t : ℝ≥0).coe_nonneg] at hx
    exact t.ne_zero (NNReal.coe_eq_zero.mp hx)
  let u : w.Completionˣ := Units.mk0 (x * x) (mul_ne_zero hx0 hx0)
  refine ⟨(IdeleGroup.ofCompletion (𝓞 K) K w u : IdeleClassGroup (𝓞 K) K), ?_, ?_⟩
  · refine Subgroup.map_connectedComponentOfOne_le (f := QuotientGroup.mk' _)
      QuotientGroup.continuous_mk ⟨_, ofCompletion_mem_connectedComponentOfOne w u fun hw ↦ ?_, rfl⟩
    rw [Units.val_mk0, map_mul]
    exact mul_self_pos.mpr ((map_ne_zero _).mpr hx0)
  · refine Units.ext (NNReal.eq ?_)
    rw [ideleClassNorm_mk, coe_ideleNorm_ofCompletion, Units.val_mk0, map_mul, hx,
      Real.mul_self_sqrt (t : ℝ≥0).coe_nonneg]

variable (K)

/-- **The quotient of the idele class group by its identity component is compact**: every class
is represented by an idele class of norm one, after dividing by an element of the identity
component of the same norm, so the quotient is the image of the compact norm-one idele class
group.  With the instances `QuotientGroup.instT3Space` and
`QuotientGroup.totallyDisconnectedSpace_connectedComponentOfOne`, this makes the quotient a
profinite group. -/
instance compactSpace_quotient_connectedComponentOfOne :
    CompactSpace (IdeleClassGroup (𝓞 K) K ⧸
      Subgroup.connectedComponentOfOne (IdeleClassGroup (𝓞 K) K)) := by
  set D := Subgroup.connectedComponentOfOne (IdeleClassGroup (𝓞 K) K)
  have himage : QuotientGroup.mk' D '' (normOne K : Set (IdeleClassGroup (𝓞 K) K)) =
      Set.univ := by
    refine Set.eq_univ_of_forall fun q ↦ ?_
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective D q
    obtain ⟨d, hd, hdc⟩ := exists_mem_connectedComponentOfOne_ideleClassNorm_eq (K := K)
      (ideleClassNorm c)
    refine ⟨c * d⁻¹, ?_, ?_⟩
    · rw [SetLike.mem_coe, mem_normOne_iff, map_mul, map_inv, hdc, mul_inv_cancel]
    · rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, eq_comm, QuotientGroup.eq,
        inv_mul_cancel_left]
      exact D.inv_mem hd
  refine ⟨?_⟩
  rw [← himage]
  exact (isCompact_normOne K).image QuotientGroup.continuous_mk

end IdeleClassGroup

/-- **The identity component of the idele class group is the intersection of the ray
subgroups.**  An idele class outside the identity component is separated from it by an open
subgroup of the profinite group `C_K / D_K`, whose preimage is an open subgroup of `C_K` and so
contains a ray subgroup. -/
theorem iInf_raySubgroup :
    ⨅ 𝔪 : Modulus K, raySubgroup 𝔪 =
      Subgroup.connectedComponentOfOne (IdeleClassGroup (𝓞 K) K) := by
  set D := Subgroup.connectedComponentOfOne (IdeleClassGroup (𝓞 K) K)
  refine le_antisymm (fun c hc ↦ ?_) (le_iInf connectedComponentOfOne_le_raySubgroup)
  by_contra hcD
  have hne : (1 : IdeleClassGroup (𝓞 K) K ⧸ D) ∈ ({(c : IdeleClassGroup (𝓞 K) K ⧸ D)}ᶜ) :=
    Set.mem_compl_singleton_iff.mpr fun h ↦ hcD ((QuotientGroup.eq_one_iff c).mp h.symm)
  obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    isOpen_compl_singleton hne
  obtain ⟨𝔪, h𝔪⟩ := exists_raySubgroup_le_of_isOpen (H.toSubgroup.comap (QuotientGroup.mk' D))
    (H.isOpen.preimage QuotientGroup.continuous_mk)
  exact hH (h𝔪 (Subgroup.mem_iInf.mp hc 𝔪)) rfl

end TauCeti.GlobalNumberFields
