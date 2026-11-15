/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.QuotientGroup.Basic
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.TitsSystem
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Torus.Weyl
import TauCeti.GroupTheory.TitsSystem.Parabolic.Normalizer

/-!
# The Weyl quotient of a Chevalley datum

Over any field `K`, the kernel of `D.weylProjection K : D.weylSubgroup K →* W` is the actual
character-lattice torus `((D.torusPoints K).range).subgroupOf (D.weylSubgroup K)`, so `N(K) / T(K)`
and the Weyl groups of both `D.titsSystem K` and `D.elementaryTitsSystem K` are canonically
isomorphic to the root-datum Weyl group `(t.simplyConnectedRootDatum ht).weylGroup`, carrying the
Tits simple reflections onto the simple reflections `ofIdx`.

Any Weyl-subgroup element `g` in the kernel fixes every root in the Weyl group, hence normalizes
`U(K)` and `T(K)` and therefore normalizes `B(K)`. Because the distinguished subgroup `B` of a Tits
system is self-normalizing (`TauCeti.TitsSystem.normalizer_subgroupB`), `g` lies in
`B(K) ∩ N(K) = T(K)`.

## Main definitions

* `TauCeti.DynkinType.ChevalleyDatum.weylSubgroupQuotientEquiv`: the isomorphism
  `D.weylSubgroup K ⧸ ((D.torusPoints K).range).subgroupOf (D.weylSubgroup K) ≃* W`.
* `TauCeti.DynkinType.ChevalleyDatum.titsSystemWeylGroupEquiv`: the isomorphism from the Weyl group
  of `D.titsSystem K` to `(t.simplyConnectedRootDatum ht).weylGroup`.
* `TauCeti.DynkinType.ChevalleyDatum.elementaryTitsSystemWeylGroupEquiv`: the isomorphism from the
  Weyl group of `D.elementaryTitsSystem K` to `(t.simplyConnectedRootDatum ht).weylGroup`.

## Main results

* `TauCeti.DynkinType.ChevalleyDatum.weylProjection_eq_one_iff_mem_range_torusPoints` and
  `TauCeti.DynkinType.ChevalleyDatum.ker_weylProjection`: the kernel of `D.weylProjection K` is the
  actual torus.
* `TauCeti.DynkinType.ChevalleyDatum.image_titsSystemWeylGroupEquiv_simple` and
  `TauCeti.DynkinType.ChevalleyDatum.image_elementaryTitsSystemWeylGroupEquiv_simple`: both
  isomorphisms send the Tits simple reflections onto the pinned simple reflections.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 27 and Theorem 4.
* R. W. Carter, *Simple Groups of Lie Type*, §8.2.
-/

public section

namespace TauCeti.DynkinType.ChevalleyDatum

universe v

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)
variable (K : Type v) [Field K]

private theorem map_borelSubgroup_conj_of_weylProjection_eq_one {g : D.weylSubgroup K}
    (hproj : D.weylProjection K g = 1) :
    (D.borelSubgroup K).map (MulAut.conj (g : D.points K)).toMonoidHom = D.borelSubgroup K := by
  have hpos : (D.positivePoints K).map (MulAut.conj (g : D.points K)).toMonoidHom =
      D.positivePoints K := by
    rw [D.positivePoints_eq_iSup K, D.map_iSup_rootSubgroupPoints_conj K g, hproj, map_one]
    simp [Set.image_id]
  have htor : ((D.torusPoints K).range).map (MulAut.conj (g : D.points K)).toMonoidHom =
      (D.torusPoints K).range := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp
        (D.weylSubgroup_le_normalizer_range_torusPoints K g.2) x).mp hx
    · intro x hx
      refine ⟨(g : D.points K)⁻¹ * x * (g : D.points K), ?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp
          (D.weylSubgroup_le_normalizer_range_torusPoints K g⁻¹.2) x).mp hx
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
  rw [D.borelSubgroup_def, Subgroup.map_sup, hpos, htor]

/-- An element of `D.weylSubgroup K` projects to `1` in the Weyl group if and only if it belongs to
the actual character-lattice torus. -/
theorem weylProjection_eq_one_iff_mem_range_torusPoints (g : D.weylSubgroup K) :
    D.weylProjection K g = 1 ↔ (g : D.points K) ∈ (D.torusPoints K).range := by
  constructor
  · intro hproj
    have hconj := D.map_borelSubgroup_conj_of_weylProjection_eq_one K hproj
    let gE : D.extendedElementarySubgroup K :=
      ⟨(g : D.points K), D.weylSubgroup_le_extendedElementarySubgroup K g.2⟩
    have hnorm : gE ∈ Subgroup.normalizer ((D.titsSystem K).subgroupB : Set _) := by
      rw [Subgroup.mem_normalizer_iff]
      intro b
      simp only [D.titsSystem_subgroupB, Subgroup.mem_subgroupOf, Subgroup.coe_mul,
        Subgroup.coe_inv]
      constructor
      · intro hb
        rw [← hconj]
        exact ⟨b.val, hb, rfl⟩
      · intro hb
        rw [← hconj] at hb
        obtain ⟨x, hx, heq⟩ := hb
        have hxb : x = b.val := (MulAut.conj (g : D.points K)).injective heq
        rwa [← hxb]
    rw [(D.titsSystem K).normalizer_subgroupB, D.titsSystem_subgroupB] at hnorm
    have hinf : (g : D.points K) ∈ D.borelSubgroup K ⊓ D.weylSubgroup K :=
      ⟨Subgroup.mem_subgroupOf.mp hnorm, g.2⟩
    rwa [D.borelSubgroup_inf_weylSubgroup_eq_range_torusPoints K] at hinf
  · rintro ⟨s, hs⟩
    have hg : g = ⟨D.torusPoints K s, D.torusPoints_mem_weylSubgroup K s⟩ :=
      Subtype.ext hs.symm
    rw [hg, D.weylProjection_torusPoints]

/-- The kernel of `D.weylProjection K` is the actual torus inside `D.weylSubgroup K`. -/
@[simp]
theorem ker_weylProjection :
    (D.weylProjection K).ker = ((D.torusPoints K).range).subgroupOf (D.weylSubgroup K) := by
  ext g
  exact D.weylProjection_eq_one_iff_mem_range_torusPoints K g

/-- **The Weyl quotient isomorphism** `N(K) / T(K) ≃* W` induced by `D.weylProjection K`. -/
noncomputable def weylSubgroupQuotientEquiv :
    D.weylSubgroup K ⧸ ((D.torusPoints K).range).subgroupOf (D.weylSubgroup K) ≃*
      (t.simplyConnectedRootDatum ht).weylGroup :=
  (QuotientGroup.quotientMulEquivOfEq (D.ker_weylProjection K).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (D.weylProjection K)
      (D.weylProjection_surjective K))

/-- `D.weylSubgroupQuotientEquiv K` acts on cosets via `D.weylProjection K`. -/
@[simp]
theorem weylSubgroupQuotientEquiv_mk (g : D.weylSubgroup K) :
    D.weylSubgroupQuotientEquiv K (QuotientGroup.mk g) = D.weylProjection K g := by
  simp [weylSubgroupQuotientEquiv, QuotientGroup.quotientKerEquivOfSurjective]

private noncomputable def titsWeylProjection :
    (D.titsSystem K).subgroupN →* (t.simplyConnectedRootDatum ht).weylGroup :=
  (D.weylProjection K).comp (D.titsSystemSubgroupNEquiv K).toMonoidHom

private theorem titsWeylProjection_surjective :
    Function.Surjective (D.titsWeylProjection K) :=
  (D.weylProjection_surjective K).comp (D.titsSystemSubgroupNEquiv K).surjective

private theorem ker_titsWeylProjection :
    (D.titsWeylProjection K).ker = (D.titsSystem K).intersection := by
  ext n
  have hnW : ((n : D.extendedElementarySubgroup K) : D.points K) ∈ D.weylSubgroup K := by
    rw [← D.coe_titsSystemSubgroupNEquiv]
    exact (D.titsSystemSubgroupNEquiv K n).2
  simp only [MonoidHom.mem_ker, titsWeylProjection, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, D.weylProjection_eq_one_iff_mem_range_torusPoints K,
    D.coe_titsSystemSubgroupNEquiv, ← D.borelSubgroup_inf_weylSubgroup_eq_range_torusPoints K,
    Subgroup.mem_inf, D.titsSystem_subgroupB, Subgroup.mem_subgroupOf]
  exact ⟨fun h => h.1, fun h => ⟨h, hnW⟩⟩

/-- **The Weyl group of `D.titsSystem K` is canonically isomorphic to the root-datum Weyl group.**
-/
noncomputable def titsSystemWeylGroupEquiv :
    (D.titsSystem K).WeylGroup ≃* (t.simplyConnectedRootDatum ht).weylGroup :=
  (QuotientGroup.quotientMulEquivOfEq (D.ker_titsWeylProjection K).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (D.titsWeylProjection K)
      (D.titsWeylProjection_surjective K))

/-- `D.titsSystemWeylGroupEquiv K` sends the class of `n` to its Weyl projection. -/
@[simp]
theorem titsSystemWeylGroupEquiv_mk (n : (D.titsSystem K).subgroupN) :
    D.titsSystemWeylGroupEquiv K (QuotientGroup.mk n) =
      D.weylProjection K (D.titsSystemSubgroupNEquiv K n) := by
  simp [titsSystemWeylGroupEquiv, QuotientGroup.quotientKerEquivOfSurjective]
  simp [titsWeylProjection]

/-- `D.titsSystemWeylGroupEquiv K` maps the `i`-th Tits simple reflection to the `i`-th simple
reflection of the root datum. -/
@[simp]
theorem titsSystemWeylGroupEquiv_titsSystemSimple (i : Fin t.rank) :
    D.titsSystemWeylGroupEquiv K (D.titsSystemSimple K i) =
      RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht) (t.simpleIndex ht i) := by
  rw [← D.titsSystemSubgroupNEquiv_symm_simpleWeylLift K i, D.titsSystemWeylGroupEquiv_mk,
    MulEquiv.apply_symm_apply, D.weylProjection_simpleWeylLift]

/-- `D.titsSystemWeylGroupEquiv K` carries the simple reflections of `D.titsSystem K` onto the
pinned simple reflections of the root datum. -/
theorem image_titsSystemWeylGroupEquiv_simple :
    D.titsSystemWeylGroupEquiv K '' (D.titsSystem K).simple =
      Set.range fun i : Fin t.rank =>
        RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht) (t.simpleIndex ht i) := by
  rw [D.titsSystem_simple K, ← Set.range_comp]
  ext w
  simp only [Set.mem_range, Function.comp_apply, D.titsSystemWeylGroupEquiv_titsSystemSimple]

/-- **The Weyl group of `D.elementaryTitsSystem K` is canonically isomorphic to the root-datum Weyl
group.** -/
noncomputable def elementaryTitsSystemWeylGroupEquiv :
    (D.elementaryTitsSystem K).WeylGroup ≃* (t.simplyConnectedRootDatum ht).weylGroup :=
  (D.elementaryToExtendedWeylGroupEquiv K).trans (D.titsSystemWeylGroupEquiv K)

/-- `D.elementaryTitsSystemWeylGroupEquiv K` factors through
`D.elementaryToExtendedWeylGroupEquiv K` and `D.titsSystemWeylGroupEquiv K`. -/
theorem elementaryTitsSystemWeylGroupEquiv_apply (w : (D.elementaryTitsSystem K).WeylGroup) :
    D.elementaryTitsSystemWeylGroupEquiv K w =
      D.titsSystemWeylGroupEquiv K (D.elementaryToExtendedWeylGroupEquiv K w) := by
  rfl

/-- `D.elementaryTitsSystemWeylGroupEquiv K` sends the class of `n` to its Weyl projection. -/
@[simp]
theorem elementaryTitsSystemWeylGroupEquiv_mk (n : (D.elementaryTitsSystem K).subgroupN) :
    D.elementaryTitsSystemWeylGroupEquiv K (QuotientGroup.mk n) =
      D.weylProjection K (D.elementaryTitsSystemSubgroupNToWeylSubgroup K n) := by
  simp [elementaryTitsSystemWeylGroupEquiv_apply]

/-- `D.elementaryTitsSystemWeylGroupEquiv K` carries the simple reflections of
`D.elementaryTitsSystem K` onto the pinned simple reflections of the root datum. -/
theorem image_elementaryTitsSystemWeylGroupEquiv_simple :
    D.elementaryTitsSystemWeylGroupEquiv K '' (D.elementaryTitsSystem K).simple =
      Set.range fun i : Fin t.rank =>
        RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht) (t.simpleIndex ht i) := by
  rw [D.elementaryTitsSystem_simple K, elementaryTitsSystemWeylGroupEquiv,
    MulEquiv.coe_trans, Set.image_comp,
    (D.elementaryToExtendedWeylGroupEquiv K).surjective.image_preimage,
    D.image_titsSystemWeylGroupEquiv_simple]

end TauCeti.DynkinType.ChevalleyDatum
