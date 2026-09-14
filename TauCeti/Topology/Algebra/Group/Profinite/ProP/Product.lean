/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.PGroup
public import TauCeti.GroupTheory.QuotientGroup.Map
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Basic

/-!
# Products of pro-p groups

The product of two pro-`p` groups is pro-`p`. Given an open normal subgroup `U` of a product,
its preimages under the two coordinate inclusions give open normal subgroups `V` and `W` of the
factors. The product `V × W` lies in `U`, so the quotient by `U` is a quotient of
`(G × H) ⧸ (V × W)`, which is a `p`-group. For a finite product `∀ i, G i`, the preimages `V i`
under the coordinate inclusions play the same role: the kernel of the map to `∀ i, G i ⧸ V i`
lies in `U`, and that map embeds its quotient into a finite product of `p`-groups.

## Main results

* `IsProP.prod`: a product of two pro-`p` groups is pro-`p`.
* `IsProP.pi`: a product of finitely many pro-`p` groups is pro-`p`.

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
  let V := OpenNormalSubgroup.comap U (ContinuousMonoidHom.inl G H).toMonoidHom
    (ContinuousMonoidHom.inl G H).continuous
  let W := OpenNormalSubgroup.comap U (ContinuousMonoidHom.inr G H).toMonoidHom
    (ContinuousMonoidHom.inr G H).continuous
  let _ : V.toSubgroup.Normal := V.isNormal'
  let _ : W.toSubgroup.Normal := W.isNormal'
  have hVW : V.toSubgroup.prod W.toSubgroup ≤ U.toSubgroup :=
    Subgroup.prod_le_iff.mpr ⟨Subgroup.map_le_iff_le_comap.mpr fun g hg ↦ by simpa [V] using hg,
      Subgroup.map_le_iff_le_comap.mpr fun h hh ↦ by simpa [W] using hh⟩
  have hProd : IsPGroup p ((G × H) ⧸ (V.toSubgroup.prod W.toSubgroup)) :=
    ((isProP_iff.mp hG V).prod (isProP_iff.mp hH W)).of_equiv
      (QuotientGroup.prodMulEquiv V.toSubgroup W.toSubgroup).symm
  exact hProd.of_surjective (QuotientGroup.mapOfLE hVW) (QuotientGroup.mapOfLE_surjective hVW)

/-- A product of finitely many pro-`p` groups, with the product topology, is pro-`p`. -/
theorem pi {ι : Type*} [Finite ι] {G : ι → Type*} [∀ i, Group (G i)]
    [∀ i, TopologicalSpace (G i)] (hG : ∀ i, IsProP p (G i)) : IsProP p (∀ i, G i) := by
  classical
  rw [isProP_iff]
  intro U
  let V i := OpenNormalSubgroup.comap U (MonoidHom.mulSingle G i) (continuous_mulSingle i)
  let _ (i : ι) : (V i).toSubgroup.Normal := (V i).isNormal'
  let f : (∀ i, G i) →* ∀ i, G i ⧸ (V i).toSubgroup :=
    MonoidHom.pi fun i ↦ (QuotientGroup.mk' (V i).toSubgroup).comp (Pi.evalMonoidHom G i)
  have hfU : f.ker ≤ U.toSubgroup := fun x hx ↦
    Subgroup.pi_mem_of_mulSingle_mem x fun i ↦ by
      have hxi : (x i : G i ⧸ (V i).toSubgroup) = 1 := by
        simpa [f] using congrFun (MonoidHom.mem_ker.mp hx) i
      exact OpenNormalSubgroup.mem_comap.mp ((QuotientGroup.eq_one_iff (x i)).mp hxi)
  have hker : IsPGroup p ((∀ i, G i) ⧸ f.ker) :=
    (IsPGroup.pi fun i ↦ isProP_iff.mp (hG i) (V i)).of_injective (QuotientGroup.kerLift f)
      (QuotientGroup.kerLift_injective f)
  exact hker.of_surjective (QuotientGroup.mapOfLE hfU) (QuotientGroup.mapOfLE_surjective hfU)

end IsProP

end TauCeti
