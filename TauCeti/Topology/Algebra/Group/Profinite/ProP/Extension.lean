/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupExtension.Defs
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Basic

/-!
# Pro-`p` groups are closed under extensions

Let `f : E →* G` be a quotient map from a group with continuous multiplication. If `G` is pro-`p`
and the kernel of `f` is pro-`p` in the subspace topology, then `E` is pro-`p`
(`TauCeti.IsProP.of_ker_isProP`). The algebraic input is that an extension of a `p`-group by a
`p`-group is a `p`-group, `IsPGroup.comap_of_ker_isPGroup`. The topological input is that a
quotient group homomorphism is an open map, so the image of an open normal subgroup `U ≤ E` is an
open normal subgroup `f(U) ≤ G`; this exhibits `E ⧸ U` as an extension of the `p`-group
`G ⧸ f(U)` by a quotient of the kernel.

For an extension `1 → M → E → G → 1` whose inclusion is continuous and whose projection is a
quotient map, this says that `E` is pro-`p` as soon as `M` and `G` are (`GroupExtension.isProP`).
The quotient-map hypothesis holds for any continuous surjection from a compact group onto a
Hausdorff group. This makes the universal property of a free pro-`p` group available for lifting
generators through such an extension.

## Main results

* `TauCeti.IsProP.of_ker_isProP`: a group with continuous multiplication mapping onto a pro-`p`
  group by a quotient map with pro-`p` kernel is pro-`p`.
* `GroupExtension.isProP`: the total group of an extension of a pro-`p` group by a pro-`p` group is
  pro-`p`.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, 2nd ed., Section 2.2.
-/

public section

namespace TauCeti

variable {p : ℕ}

namespace IsProP

variable {E : Type*} [Group E] [TopologicalSpace E] [ContinuousMul E]
  {G : Type*} [Group G] [TopologicalSpace G]

/-- **Pro-`p` is closed under extensions.** A group `E` with continuous multiplication is pro-`p`
when it maps onto a pro-`p` group by a quotient map whose kernel is pro-`p` in the subspace
topology. -/
theorem of_ker_isProP (hG : IsProP p G) {f : E →* G} (hf : Topology.IsQuotientMap f)
    (hker : IsProP p f.ker) : IsProP p E := by
  rw [isProP_iff]
  intro U
  -- A quotient group homomorphism is open, so the image of `U` is an open normal subgroup.
  have hopen : IsOpenMap f := (MonoidHom.isOpenQuotientMap_of_isQuotientMap hf).isOpenMap
  let V : OpenNormalSubgroup G :=
    { toSubgroup := U.toSubgroup.map f
      isOpen' := hopen _ U.isOpen'
      isNormal' := U.isNormal'.map f hf.surjective }
  have _ : V.toSubgroup.Normal := V.isNormal'
  have hUV : U.toSubgroup ≤ V.toSubgroup.comap f := fun x hx ↦ Subgroup.mem_map_of_mem f hx
  -- The kernel of the induced map `E ⧸ U → G ⧸ f(U)` is the image of `ker f`, a `p`-group.
  have hφ : IsPGroup p (QuotientGroup.map U.toSubgroup V.toSubgroup f hUV).ker := by
    rw [QuotientGroup.ker_map, Subgroup.comap_map_eq, Subgroup.map_sup,
      QuotientGroup.map_mk'_self, bot_sup_eq]
    exact hker.isPGroup_map_mk' U
  -- `E ⧸ U` is the preimage of the `p`-group `G ⧸ f(U)`, so it is a `p`-group.
  have h := ((isProP_iff.mp hG V).to_subgroup ⊤).comap_of_ker_isPGroup _ hφ
  rw [Subgroup.comap_top] at h
  exact h.of_equiv Subgroup.topEquiv

end IsProP

variable {M : Type*} [Group M] [TopologicalSpace M]
  {E : Type*} [Group E] [TopologicalSpace E] [ContinuousMul E]
  {G : Type*} [Group G] [TopologicalSpace G]

/-- The total group of an extension `1 → M → E → G → 1` with continuous multiplication,
continuous inclusion, and quotient projection is pro-`p` when `M` and `G` are. -/
theorem _root_.GroupExtension.isProP (S : GroupExtension M E G) (hinl : Continuous S.inl)
    (hrh : Topology.IsQuotientMap S.rightHom) (hM : IsProP p M) (hG : IsProP p G) : IsProP p E := by
  refine hG.of_ker_isProP hrh ?_
  rw [← S.range_inl_eq_ker_rightHom]
  exact hM.of_surjective S.inl.rangeRestrict (continuous_induced_rng.mpr hinl)
    S.inl.rangeRestrict_surjective

end TauCeti
