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

The class of pro-`p` groups is stable under products: if each factor is pro-`p`, then so is
their product with the product topology. Together with stability under continuous surjective
images from `ProP.Basic`, this is part of the basic closure API for `IsProP`, and lets new pro-`p`
groups be assembled from known factors without re-examining their open normal subgroups. The
result is stated both for binary products `G × H` and for indexed products `∀ i, G i`, the two
product forms used in practice.

The index type of `IsProP.pi` is arbitrary, so the closure covers infinite products as well as
finite ones. That generality is what makes it applicable to inverse limits, which are carved out
of a product over an index category that need not be finite.

## Main results

* `IsProP.prod`: a product of two pro-`p` groups is pro-`p`.
* `IsProP.pi`: a product of pro-`p` groups is pro-`p`.

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
  -- Pull `U` back along the coordinate inclusions to open normal subgroups `V` and `W`. Then
  -- `V × W ≤ U`, so `(G × H) ⧸ U` is a quotient of the `p`-group `(G × H) ⧸ (V × W)`.
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

/-- A product of pro-`p` groups, with the product topology, is pro-`p`. Specialising to a finite
index type gives stability under finite products. -/
theorem pi {ι : Type*} {G : ι → Type*} [∀ i, Group (G i)]
    [∀ i, TopologicalSpace (G i)] (hG : ∀ i, IsProP p (G i)) : IsProP p (∀ i, G i) := by
  -- Pull `U` back along each coordinate inclusion to `V i`, and take a basic box inside `U`
  -- around `1`, constraining only the coordinates in a finite set `I`. The kernel of the map to
  -- `∀ i : I, G i ⧸ V i` lies in `U`, and its quotient embeds in a finite product of `p`-groups.
  classical
  rw [isProP_iff]
  intro U
  obtain ⟨I, s, hs, hsU⟩ := isOpen_pi_iff.mp U.toOpenSubgroup.isOpen 1 U.toSubgroup.one_mem
  let V i := OpenNormalSubgroup.comap U (MonoidHom.mulSingle G i) (continuous_mulSingle i)
  let _ (i : ι) : (V i).toSubgroup.Normal := (V i).isNormal'
  let f : (∀ i, G i) →* ∀ i : I, G i ⧸ (V i).toSubgroup :=
    MonoidHom.pi fun i ↦ (QuotientGroup.mk' (V i).toSubgroup).comp (Pi.evalMonoidHom G i)
  have hfU : f.ker ≤ U.toSubgroup := by
    intro x hx
    have hxV : ∀ i ∈ I, Pi.mulSingle i (x i) ∈ U.toSubgroup := fun i hi ↦ by
      have hxi : (x i : G i ⧸ (V i).toSubgroup) = 1 := by
        simpa [f] using congrFun (MonoidHom.mem_ker.mp hx) ⟨i, hi⟩
      exact OpenNormalSubgroup.mem_comap.mp ((QuotientGroup.eq_one_iff (x i)).mp hxi)
    -- Split `x` into the part supported on `I`, a finite product of `Pi.mulSingle`s lying in
    -- `U`, times the complementary part, which lies in the box.
    have hsplit : x = (fun i ↦ if i ∈ I then x i else 1) * fun i ↦ if i ∈ I then 1 else x i := by
      funext i
      by_cases hi : i ∈ I <;> simp [hi]
    rw [hsplit]
    exact mul_mem (Submonoid.pi_mem_of_mulSingle_mem_aux I _ (fun i hi ↦ by simp [hi])
        fun i hi ↦ by simpa [hi] using hxV i hi)
      (hsU fun i hi ↦ by simpa [Finset.mem_coe.mp hi] using (hs i (Finset.mem_coe.mp hi)).2)
  have hker : IsPGroup p ((∀ i, G i) ⧸ f.ker) :=
    (IsPGroup.pi fun i : I ↦ isProP_iff.mp (hG i) (V i)).of_injective (QuotientGroup.kerLift f)
      (QuotientGroup.kerLift_injective f)
  exact hker.of_surjective (QuotientGroup.mapOfLE hfU) (QuotientGroup.mapOfLE_surjective hfU)

end IsProP

end TauCeti
