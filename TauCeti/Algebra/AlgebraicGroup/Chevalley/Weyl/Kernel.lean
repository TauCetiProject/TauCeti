/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Borel
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Torus.Weyl
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Braid.Coxeter
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Coroot
import TauCeti.Algebra.AlgebraicGroup.Chevalley.RankOne
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Weyl.Root
import TauCeti.GroupTheory.Coxeter.Basic
import TauCeti.LinearAlgebra.RootSystem.Coxeter.Presentation
import TauCeti.LinearAlgebra.RootSystem.Inversions.StrongExchange
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Coxeter
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Rational
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Reduced

/-!
# The kernel of the Chevalley Weyl projection

For a Chevalley datum `D` and a field `k`, let `N = D.weylSubgroup k` be the subgroup generated
by the actual torus `T = T_D(k)` and the pinned simple Weyl representatives `nᵢ = nᵢ(1)`. The
Weyl projection `N → W` onto the Weyl group of the simply connected root datum is surjective and
kills `T`. This file proves that its kernel is exactly `T`, so that `N / T ≅ W` by `nᵢ ↦ sᵢ`, and
that `N ∩ B = T` for the Borel-type subgroup `B`. Both hold over every field, finite or not.

The kernel is computed through the Coxeter presentation of `W`. In `N / T` the images of the
`nᵢ` are involutions, since `nᵢ² = hᵢ(-1)` is a torus point, and they satisfy the braid relations
of `TauCeti.DynkinType.coxeterMatrix` by `ChevalleyDatum.weylWord_braidWord_eq`. Hence the
Coxeter group of the pinned base maps onto `N / T`. Composed with the projection, this is the
canonical map onto `W`, which is injective by Tits' theorem `TauCeti.weylCoxeterHom_injective`.
The projection is therefore injective on `N / T`.

For `N ∩ B`, an element of both conjugates every positive root subgroup to the root subgroup of
the image root, inside `B`. A negative root element of `B` is trivial, so its Weyl projection
keeps every positive root positive and is the identity by `TauCeti.eq_one_of_mapsTo_posRoots`.
The kernel theorem then places it in `T`. As a consequence, `B ∩ N` is normal in `N`, the
corresponding axiom of a Tits system with these subgroups.

## Main results

* `TauCeti.DynkinType.ChevalleyDatum.ker_weylProjection`: the kernel of the Weyl projection is
  the actual torus.
* `TauCeti.DynkinType.ChevalleyDatum.weylQuotientEquiv` and
  `TauCeti.DynkinType.ChevalleyDatum.weylQuotientEquiv_mk`: `N / T ≅ W`, induced by the Weyl
  projection, so that the class of `nᵢ` goes to the simple reflection `sᵢ`
  (`TauCeti.DynkinType.ChevalleyDatum.weylProjection_weylElement`).
* `TauCeti.DynkinType.ChevalleyDatum.weylSubgroup_inf_borelSubgroup`: `N ∩ B = T`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3.
* R. W. Carter, *Simple Groups of Lie Type*, §7.2 and §8.1.
* J. Tits, *Normalisateurs de tores I. Groupes de Coxeter étendus*, J. Algebra **4** (1966),
  96--116.
-/

public section

namespace TauCeti.DynkinType.ChevalleyDatum

universe v

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)
variable (k : Type v) [Field k]

/-- The pinned simple Weyl representative `nᵢ = nᵢ(1)`, as an element of the Weyl subgroup. -/
private noncomputable def weylRep (i : Fin t.rank) : D.weylSubgroup k :=
  ⟨D.weylElement (t.simpleIndex ht i) k 1, D.weylElement_mem_weylSubgroup k i⟩

/-- The simple Weyl representative, as a point. -/
@[simp]
private theorem coe_weylRep (i : Fin t.rank) :
    (D.weylRep k i : D.points k) = D.weylElement (t.simpleIndex ht i) k 1 :=
  rfl

/-- The square of a simple Weyl representative is a torus point. -/
private theorem weylRep_mul_self_mem (i : Fin t.rank) :
    D.weylRep k i * D.weylRep k i ∈ (D.torusPoints k).range.subgroupOf (D.weylSubgroup k) := by
  rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, coe_weylRep, D.weylElement_mul_self,
    D.simpleCorootPoints_eq_torusPoints]
  exact ⟨_, rfl⟩

/-- The images of the simple Weyl representatives in `N / T`, indexed by the support of the
pinned base. -/
private noncomputable def coxeterGen (i : (t.simplyConnectedBase ht).support) :
    D.weylSubgroup k ⧸ (D.torusPoints k).range.subgroupOf (D.weylSubgroup k) :=
  QuotientGroup.mk (D.weylRep k ((t.simpleSupportEquivSimplyConnectedBase ht).symm i))

/-- In `N / T` the simple Weyl representatives satisfy the Coxeter relations of the pinned base. -/
private theorem isLiftable_coxeterGen :
    (coxeterMatrixOfBase (t.simplyConnectedRootDatum ht) (t.simplyConnectedBase ht)).IsLiftable
      (D.coxeterGen k) := by
  intro i j
  rw [coxeterMatrixOfBase_simplyConnectedBase, CoxeterMatrix.reindex_apply]
  let q : Fin t.rank → D.weylSubgroup k ⧸ (D.torusPoints k).range.subgroupOf (D.weylSubgroup k) :=
    fun a => QuotientGroup.mk (D.weylRep k a)
  have hq (a : Fin t.rank) : q a * q a = 1 := by
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
    exact D.weylRep_mul_self_mem k a
  have hbraid (a b : Fin t.rank) :
      ((CoxeterSystem.alternatingWord a b (t.coxeterMatrix a b)).map q).prod =
        ((CoxeterSystem.alternatingWord b a (t.coxeterMatrix a b)).map q).prod := by
    have hmk (l : List (Fin t.rank)) :
        (l.map q).prod = QuotientGroup.mk (l.map (D.weylRep k)).prod := by
      rw [← QuotientGroup.mk'_apply, map_list_prod, List.map_map]
      simp only [q, Function.comp_def, QuotientGroup.mk'_apply]
    rw [hmk, hmk]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.val_list_prod, List.map_map]
    have h := D.weylWord_braidWord_eq a b k
    rw [CoxeterSystem.braidWord, CoxeterSystem.braidWord, t.coxeterMatrix.symmetric b a] at h
    simpa [Function.comp_def, coe_weylRep] using h
  exact TauCeti.pow_eq_one_of_prod_map_alternatingWord_eq q (hq _) (hq _) _ (hbraid _ _)

/-- The Coxeter group of the pinned base maps to `N / T`, sending each generator to the class of
the corresponding simple Weyl representative. -/
private noncomputable def coxeterLift :
    (coxeterMatrixOfBase (t.simplyConnectedRootDatum ht) (t.simplyConnectedBase ht)).Group →*
      D.weylSubgroup k ⧸ (D.torusPoints k).range.subgroupOf (D.weylSubgroup k) :=
  (coxeterMatrixOfBase (t.simplyConnectedRootDatum ht)
    (t.simplyConnectedBase ht)).toCoxeterSystem.lift ⟨D.coxeterGen k, D.isLiftable_coxeterGen k⟩

/-- The Coxeter lift sends each Coxeter generator to the class of its Weyl representative. -/
private theorem coxeterLift_simple (i : (t.simplyConnectedBase ht).support) :
    D.coxeterLift k ((coxeterMatrixOfBase (t.simplyConnectedRootDatum ht)
      (t.simplyConnectedBase ht)).simple i) = D.coxeterGen k i := by
  rw [← CoxeterMatrix.toCoxeterSystem_simple]
  exact CoxeterSystem.lift_apply_simple _ (D.isLiftable_coxeterGen k) i

/-- Every class in `N / T` is the image of an element of the Coxeter group: `N` is generated by
`T` and the simple Weyl representatives. -/
private theorem coxeterLift_surjective : Function.Surjective (D.coxeterLift k) := by
  let H : Subgroup (D.points k) :=
    ((D.coxeterLift k).range.comap (QuotientGroup.mk' _)).map (D.weylSubgroup k).subtype
  have hle : D.weylSubgroup k ≤ H := by
    rw [weylSubgroup_def, Subgroup.closure_le]
    rintro _ (⟨s, rfl⟩ | ⟨i, rfl⟩)
    · refine ⟨⟨_, D.torusPoints_mem_weylSubgroup k s⟩, ?_, rfl⟩
      refine ⟨1, ?_⟩
      rw [map_one, eq_comm, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact ⟨s, rfl⟩
    · refine ⟨D.weylRep k i, ⟨(coxeterMatrixOfBase (t.simplyConnectedRootDatum ht)
        (t.simplyConnectedBase ht)).toCoxeterSystem.simple
          (t.simpleSupportEquivSimplyConnectedBase ht i), ?_⟩, rfl⟩
      rw [CoxeterMatrix.toCoxeterSystem_simple, coxeterLift_simple, coxeterGen,
        Equiv.symm_apply_apply, QuotientGroup.mk'_apply]
  intro x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨g', hg', heq⟩ := hle g.property
  rw [show g' = g from Subtype.ext heq] at hg'
  exact hg'

/-- The Weyl projection, descended to `N / T`. -/
private noncomputable def quotientWeylProjection :
    D.weylSubgroup k ⧸ (D.torusPoints k).range.subgroupOf (D.weylSubgroup k) →*
      (t.simplyConnectedRootDatum ht).weylGroup :=
  QuotientGroup.lift _ (D.weylProjection k) (by
    rintro ⟨_, _⟩ ⟨s, rfl⟩
    exact D.weylProjection_torusPoints k s)

/-- The descended Weyl projection of a class is the Weyl projection of its representatives. -/
private theorem quotientWeylProjection_mk (g : D.weylSubgroup k) :
    D.quotientWeylProjection k (QuotientGroup.mk g) = D.weylProjection k g :=
  QuotientGroup.lift_mk _ _ g

/-- Composed with the descended Weyl projection, the Coxeter lift is the canonical map from the
Coxeter group to the Weyl group. -/
private theorem quotientWeylProjection_comp_coxeterLift :
    (D.quotientWeylProjection k).comp (D.coxeterLift k) =
      weylCoxeterHom (t.simplyConnectedRootDatum ht) (t.simplyConnectedBase ht) := by
  apply (coxeterMatrixOfBase (t.simplyConnectedRootDatum ht)
    (t.simplyConnectedBase ht)).toCoxeterSystem.ext_simple
  intro i
  rw [MonoidHom.comp_apply, CoxeterMatrix.toCoxeterSystem_simple, coxeterLift_simple,
    weylCoxeterHom_apply_simple, coxeterGen, quotientWeylProjection_mk]
  simp only [weylRep]
  rw [weylProjection_weylElement, ← coe_simpleSupportEquivSimplyConnectedBase,
    Equiv.apply_symm_apply]

/-- The descended Weyl projection is injective, by Tits' theorem. -/
private theorem quotientWeylProjection_injective :
    Function.Injective (D.quotientWeylProjection k) := by
  have := t.isReduced_simplyConnectedRootDatum ht
  rw [injective_iff_map_eq_one]
  intro x hx
  obtain ⟨c, rfl⟩ := D.coxeterLift_surjective k x
  have hc : weylCoxeterHom (t.simplyConnectedRootDatum ht) (t.simplyConnectedBase ht) c = 1 := by
    rw [← D.quotientWeylProjection_comp_coxeterLift k]
    exact hx
  rw [(weylCoxeterHom_injective (t.simplyConnectedRootDatum ht) (t.simplyConnectedBase ht)).eq_iff'
    (map_one _)] at hc
  rw [hc, map_one]

/-- **The kernel of the Weyl projection is the actual torus.** Over every field, a point of the
subgroup `N` generated by the actual torus and the simple Weyl representatives projects to the
identity of the Weyl group exactly when it is a torus point. -/
theorem ker_weylProjection :
    (D.weylProjection k).ker = (D.torusPoints k).range.subgroupOf (D.weylSubgroup k) := by
  ext g
  rw [MonoidHom.mem_ker, ← QuotientGroup.eq_one_iff, ← D.quotientWeylProjection_mk k,
    (D.quotientWeylProjection_injective k).eq_iff' (map_one _)]

/-- A point of `N` has trivial Weyl projection exactly when it is a torus point. -/
theorem weylProjection_eq_one_iff_mem_range_torusPoints (g : D.weylSubgroup k) :
    D.weylProjection k g = 1 ↔ (g : D.points k) ∈ (D.torusPoints k).range := by
  rw [← MonoidHom.mem_ker, ker_weylProjection, Subgroup.mem_subgroupOf]

/-- **The Weyl group of a Chevalley datum over a field.** The quotient of `N` by the actual
torus is the Weyl group of the simply connected root datum, the class of each simple Weyl
representative `nᵢ` going to the simple reflection `sᵢ`. -/
noncomputable def weylQuotientEquiv :
    D.weylSubgroup k ⧸ (D.torusPoints k).range.subgroupOf (D.weylSubgroup k) ≃*
      (t.simplyConnectedRootDatum ht).weylGroup :=
  (QuotientGroup.quotientMulEquivOfEq (D.ker_weylProjection k).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (D.weylProjection_surjective k))

/-- The equivalence `N / T ≅ W` sends the class of a point of `N` to its Weyl projection. -/
@[simp]
theorem weylQuotientEquiv_mk (g : D.weylSubgroup k) :
    D.weylQuotientEquiv k (QuotientGroup.mk g) = D.weylProjection k g := by
  simp [weylQuotientEquiv, QuotientGroup.quotientKerEquivOfSurjective]

/-- A point of `N ∩ B` has Weyl projection keeping every positive root positive. -/
private theorem mapsTo_weylProjection_posRoots (g : D.weylSubgroup k)
    (hg : (g : D.points k) ∈ D.borelSubgroup k) :
    Set.MapsTo ((t.simplyConnectedRootDatum ht).weylGroupToPerm (D.weylProjection k g))
      (posRoots (t.rationalRootSystem ht) (t.rationalBase ht))
      (posRoots (t.rationalRootSystem ht) (t.rationalBase ht)) := by
  intro γ hγ
  obtain ⟨c, hc⟩ := D.exists_unit_conj_rootSubgroupPoints k g γ
  refine ((posRoots_union_negRoots _ _).symm.subset (Set.mem_univ _)).resolve_right ?_
  intro hneg
  have hmem : MulAut.conj (g : D.points k) (D.rootSubgroupPoints γ k (Multiplicative.ofAdd 1)) ∈
      D.borelSubgroup k :=
    (D.borelSubgroup k).mul_mem ((D.borelSubgroup k).mul_mem hg
      (D.positivePoints_le_borelSubgroup k (D.rootSubgroupPoints_mem_positivePoints k hγ _)))
      ((D.borelSubgroup k).inv_mem hg)
  rw [hc, D.rootSubgroupPoints_mem_borelSubgroup_iff_of_mem_negRoots k hneg, ← hc,
    map_eq_one_iff _ (MulAut.conj _).injective] at hmem
  exact D.rootSubgroupPoints_ofAdd_one_ne_one k γ hmem

/-- **The Weyl subgroup meets the Borel-type subgroup in the actual torus.** Over every field,
`N ∩ B = T`. -/
@[simp]
theorem weylSubgroup_inf_borelSubgroup :
    D.weylSubgroup k ⊓ D.borelSubgroup k = (D.torusPoints k).range := by
  apply le_antisymm
  · rintro g ⟨hN, hB⟩
    have hw : D.weylProjection k ⟨g, hN⟩ = 1 := by
      have := t.isReduced_simplyConnectedRootDatum ht
      apply eq_one_of_mapsTo_posRoots (b := t.simplyConnectedBase ht)
      rw [← t.posRoots_rationalRootSystem ht]
      exact D.mapsTo_weylProjection_posRoots k ⟨g, hN⟩ hB
    exact (D.weylProjection_eq_one_iff_mem_range_torusPoints k ⟨g, hN⟩).mp hw
  · rintro _ ⟨s, rfl⟩
    exact ⟨D.torusPoints_mem_weylSubgroup k s, D.range_torusPoints_le_borelSubgroup k ⟨s, rfl⟩⟩

/-- `B ∩ N` is normal in `N`: it is the actual torus, which `N` normalizes. This is the normality
axiom of a Tits system with these subgroups. -/
instance normal_borelSubgroup_subgroupOf_weylSubgroup :
    ((D.borelSubgroup k).subgroupOf (D.weylSubgroup k)).Normal := by
  rw [← Subgroup.inf_subgroupOf_left, D.weylSubgroup_inf_borelSubgroup k]
  infer_instance

end TauCeti.DynkinType.ChevalleyDatum
