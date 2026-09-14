/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.PGroup
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Basic

/-!
# Products of pro-p groups

The product of two pro-`p` groups is pro-`p`. Given an open normal subgroup `U` of a product,
its preimages under the two coordinate inclusions give open normal subgroups `V` and `W` of the
factors. The product `V × W` lies in `U`, so the quotient by `U` is a quotient of
`(G × H) ⧸ (V × W)`, which is a `p`-group.

## Main result

* `IsProP.prod`: a product of two pro-`p` groups is pro-`p`.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 2.2.
-/

public section

namespace TauCeti

universe u v

namespace IsProP

variable {p : ℕ}
variable {G : Type u} [Group G] [TopologicalSpace G]
variable {H : Type v} [Group H] [TopologicalSpace H]

/-- A product of two pro-`p` groups, with the product topology, is pro-`p`. -/
theorem prod (hG : IsProP p G) (hH : IsProP p H) : IsProP p (G × H) := by
  rw [isProP_iff]
  intro U
  let iG : G →ₜ* (G × H) := ContinuousMonoidHom.inl G H
  let iH : H →ₜ* (G × H) := ContinuousMonoidHom.inr G H
  let V := OpenNormalSubgroup.comap U iG.toMonoidHom iG.continuous
  let W := OpenNormalSubgroup.comap U iH.toMonoidHom iH.continuous
  let _ : V.toSubgroup.Normal := V.isNormal'
  let _ : W.toSubgroup.Normal := W.isNormal'
  have hVW : V.toSubgroup.prod W.toSubgroup ≤ U.toSubgroup := by
    rintro ⟨g, h⟩ gh
    rw [Subgroup.mem_prod] at gh
    have hg : (g, 1) ∈ U := by
      have : iG g ∈ U := OpenNormalSubgroup.mem_comap.mp gh.1
      simpa [iG] using this
    have hh : (1, h) ∈ U := by
      have : iH h ∈ U := OpenNormalSubgroup.mem_comap.mp gh.2
      simpa [iH] using this
    change (g, h) ∈ U
    rw [show (g, h) = (g, 1) * (1, h) by simp]
    exact U.toSubgroup.mul_mem hg hh
  have hProd : IsPGroup p ((G × H) ⧸ (V.toSubgroup.prod W.toSubgroup)) :=
    ((isProP_iff.mp hG V).prod (isProP_iff.mp hH W)).of_equiv
      (QuotientGroup.prodMulEquiv V.toSubgroup W.toSubgroup).symm
  let q : (G × H) ⧸ (V.toSubgroup.prod W.toSubgroup) →* (G × H) ⧸ U.toSubgroup :=
    QuotientGroup.map _ _ (MonoidHom.id (G × H)) (by simpa using hVW)
  apply hProd.of_surjective q
  exact QuotientGroup.map_surjective_of_surjective _ _ (MonoidHom.id (G × H))
    (QuotientGroup.mk'_surjective U.toSubgroup) (by simpa using hVW)

end IsProP

end TauCeti
