/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.ClassModule.Extension
import TauCeti.Topology.Algebra.Group.TopologicalAbelianization.Lift

/-!
# Finite quotients of a pro-`p` class-module extension

Let `V` be a subgroup of a topological group `G`, and `U` an open normal subgroup of finite index.
If the image of `V` in `G/U` is an abelian `p`-group, the quotient map kills the kernel of
`V → Vᵃᵇ(p)`. When `V` is normal, `G/U` is therefore a quotient of the class-module extension
`G / ker(V → Vᵃᵇ(p))`. This permits a generating family of that extension to be read in the
finite quotient.

## References

* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, 2nd ed.,
  proof of (7.4.1).
-/

public section

namespace TauCeti

open scoped IsMulCommutative

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A finite quotient in which the image of `V` is an abelian `p`-group kills the kernel
of `V → Vᵃᵇ(p)`. For normal `V`, this is the inclusion needed by `QuotientGroup.mapOfLE`
to factor the quotient through the pro-`p` class-module extension. -/
theorem abelianizationProPExtensionKernel_le_of_isPGroup_map (p : ℕ)
    (V : Subgroup G) (U : OpenNormalSubgroup G) [U.toSubgroup.FiniteIndex]
    (hpro : IsPGroup p (V.map (QuotientGroup.mk' U.toSubgroup)))
    (hcomm : ⁅V, V⁆ ≤ U.toSubgroup) :
    abelianizationProPExtensionKernel p G V ≤ U.toSubgroup := by
  let q := QuotientGroup.mk' U.toSubgroup
  let H := V.map q
  have hHcomm : ⁅H, H⁆ = ⊥ := by
    rw [← Subgroup.map_commutator]
    exact (Subgroup.map_eq_bot_iff _).mpr (by simpa [q] using hcomm)
  let _ : IsMulCommutative H := Subgroup.commutator_self_eq_bot_iff.mp hHcomm
  let f : V →* H := q.subgroupMap V
  have hf : Continuous f :=
    (QuotientGroup.continuous_mk.comp continuous_subtype_val).subtype_mk _
  let fc : V →ₜ* H := ⟨f, hf⟩
  let a := TopologicalAbelianization.lift fc
  have hHpro : IsProP p H := isProP_iff_isPGroup.mpr hpro
  let b := maximalProPQuotient.lift hHpro a.toMonoidHom a.continuous
  intro x hx
  obtain ⟨hv, hzero⟩ := (mem_abelianizationProPExtensionKernel_iff p G V x).mp hx
  have hb : b (abelianizationProPMk p G V ⟨x, hv⟩) = f ⟨x, hv⟩ := by
    rw [abelianizationProPMk_apply, maximalProPQuotient.mk_apply]
    simp only [b, maximalProPQuotient.lift_mk]
    exact TopologicalAbelianization.lift_mk fc _
  rw [hzero, map_one] at hb
  exact (QuotientGroup.eq_one_iff x).mp (congrArg Subtype.val hb.symm)

end TauCeti
