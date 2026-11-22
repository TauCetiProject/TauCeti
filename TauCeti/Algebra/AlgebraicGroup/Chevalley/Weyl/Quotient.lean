/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Torus.Weyl
import TauCeti.Algebra.AlgebraicGroup.Chevalley.RankOne
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Braid.Coxeter
import TauCeti.LinearAlgebra.RootSystem.Coxeter.Presentation
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Coxeter

/-!
# The Weyl quotient of Chevalley data

For every Chevalley datum of every valid Dynkin type (including `G₂`) over a nontrivial commutative
ring, the quotient of `weylSubgroup` by its actual character-lattice torus is the Weyl group of
the pinned root datum (`ChevalleyDatum.weylQuotientMulEquiv`). The equivalence sends the class of
each pinned simple Weyl representative to its simple reflection and commutes with ring homomorphisms
(`ChevalleyDatum.weylQuotientMulEquiv_map`). Over a field, the kernel of the native Weyl projection
is exactly that torus (`ChevalleyDatum.ker_weylProjection` and
`ChevalleyDatum.weylProjection_eq_one_iff_mem_range_torusPoints`).

The argument uses the native rank-one square identity (`nᵢ(1)² = hᵢ(-1)`) and the Coxeter braid
relations `ChevalleyDatum.weylWord_braidWord_eq` in `D.points A`. Modulo the torus, the pinned
representatives satisfy the Coxeter presentation; the induced map back from the Weyl group is
surjective by generation and injective by reduction to a residue field. Over fields its inverse
agrees with the native Weyl projection. No point-generation theorem, Bruhat decomposition,
infinitude assumption, or surjectivity of the full-weight torus parametrization is needed. In
particular, the result applies to adjoint data and finite fields.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemmas 19 and 22, and Chapter 6.
* R. W. Carter, *Simple Groups of Lie Type*, §§6.4 and 7.2.
-/

public section

namespace TauCeti.DynkinType.ChevalleyDatum

noncomputable section

attribute [local instance] isReduced_simplyConnectedRootDatum

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)
variable (A : Type*) [CommRing A]

local notation "N" => D.weylSubgroup A
local notation "H" => Subgroup.subgroupOf (MonoidHom.range (D.torusPoints A)) N
local notation "Q" => N ⧸ H

private def simpleLift (i : Fin t.rank) : N :=
  ⟨D.weylElement (t.simpleIndex ht i) A 1, D.weylElement_mem_weylSubgroup A i⟩

private def simpleClass (i : Fin t.rank) : Q :=
  QuotientGroup.mk (D.simpleLift A i)

private theorem simpleClass_mul_self (i : Fin t.rank) :
    D.simpleClass A i * D.simpleClass A i = 1 := by
  rw [simpleClass, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf, MonoidHom.mem_range]
  simp only [Subgroup.coe_mul, simpleLift]
  exact ⟨D.simpleCorootParameter i A (-1),
    (D.simpleCorootPoints_eq_torusPoints i A (-1)).symm.trans
      (D.weylElement_mul_self i A).symm⟩

private theorem simpleClass_prod_eq (l l' : List (Fin t.rank))
    (h : (l.map (fun i => D.weylElement (t.simpleIndex ht i) A 1)).prod =
      (l'.map (fun i => D.weylElement (t.simpleIndex ht i) A 1)).prod) :
    (l.map (D.simpleClass A)).prod = (l'.map (D.simpleClass A)).prod := by
  have h' : (l.map (D.simpleLift A)).prod = (l'.map (D.simpleLift A)).prod := by
    apply Subtype.ext
    simpa only [Subgroup.val_list_prod, List.map_map, simpleLift, Function.comp_def] using h
  unfold simpleClass
  simpa only [map_list_prod, List.map_map, Function.comp_def, QuotientGroup.mk'_apply]
    using congrArg (QuotientGroup.mk' H) h'

private theorem simpleClass_liftable :
    (coxeterMatrixOfBase (t.simplyConnectedRootDatum ht) (t.simplyConnectedBase ht)).IsLiftable
      (fun i => D.simpleClass A ((t.simpleSupportEquivSimplyConnectedBase ht).symm i)) := by
  intro a b
  let e := t.simpleSupportEquivSimplyConnectedBase ht
  obtain ⟨i, rfl⟩ := e.surjective a
  obtain ⟨j, rfl⟩ := e.surjective b
  simp only [e, Equiv.symm_apply_apply,
    t.coxeterMatrixOfBase_simplyConnectedBase_apply ht i j]
  have hbraid :
      ((CoxeterSystem.alternatingWord i j (t.coxeterMatrix i j)).map
          (fun k => D.weylElement (t.simpleIndex ht k) A 1)).prod =
        ((CoxeterSystem.alternatingWord j i (t.coxeterMatrix i j)).map
          (fun k => D.weylElement (t.simpleIndex ht k) A 1)).prod := by
    have h := D.weylWord_braidWord_eq i j A
    simpa only [CoxeterSystem.braidWord, t.coxeterMatrix.symmetric j i] using h
  exact TauCeti.pow_eq_one_of_prod_map_alternatingWord_eq (D.simpleClass A)
    (D.simpleClass_mul_self A i) (D.simpleClass_mul_self A j) (t.coxeterMatrix i j)
    (D.simpleClass_prod_eq A _ _ hbraid)

private def quotientSection :
    (t.simplyConnectedRootDatum ht).weylGroup →* Q :=
  (weylCoxeterSystem (t.simplyConnectedRootDatum ht) (t.simplyConnectedBase ht)).lift
    ⟨_, D.simpleClass_liftable A⟩

private theorem quotientSection_simple (i : Fin t.rank) :
    D.quotientSection A
        (RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht) (t.simpleIndex ht i)) =
      D.simpleClass A i := by
  have h := (weylCoxeterSystem (t.simplyConnectedRootDatum ht)
    (t.simplyConnectedBase ht)).lift_apply_simple (D.simpleClass_liftable A)
      (t.simpleSupportEquivSimplyConnectedBase ht i)
  simpa only [quotientSection, weylCoxeterSystem_simple,
    coe_simpleSupportEquivSimplyConnectedBase_apply, Equiv.symm_apply_apply] using h

private theorem closure_weylSubgroup_generators :
    Subgroup.closure ((D.weylSubgroup A).subtype ⁻¹'
      (Set.range (D.torusPoints A) ∪
        Set.range (fun i => D.weylElement (t.simpleIndex ht i) A 1))) = ⊤ := by
  rw [D.weylSubgroup_def]
  exact Subgroup.closure_preimage_eq_top _

private theorem mk_torusPoints (s : Fin t.rank → Aˣ)
    (hx : D.torusPoints A s ∈ N) :
    (QuotientGroup.mk ⟨D.torusPoints A s, hx⟩ : Q) = 1 := by
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, MonoidHom.mem_range]
  exact ⟨s, rfl⟩

private theorem quotientSection_surjective :
    Function.Surjective (D.quotientSection A) := by
  have hrange : (D.quotientSection A).range.comap (QuotientGroup.mk' H) = ⊤ := by
    apply top_unique
    rw [← D.closure_weylSubgroup_generators A, Subgroup.closure_le]
    rintro ⟨x, hx⟩ (⟨s, rfl⟩ | ⟨i, rfl⟩)
    · rw [SetLike.mem_coe, Subgroup.mem_comap, QuotientGroup.mk'_apply,
        D.mk_torusPoints A s hx, MonoidHom.mem_range]
      exact ⟨1, map_one _⟩
    · rw [SetLike.mem_coe, Subgroup.mem_comap, QuotientGroup.mk'_apply,
        MonoidHom.mem_range]
      exact ⟨_, D.quotientSection_simple A i⟩
  intro q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective H q
  have hg : g ∈ (D.quotientSection A).range.comap (QuotientGroup.mk' H) := by
    rw [hrange]
    trivial
  rw [Subgroup.mem_comap, MonoidHom.mem_range] at hg
  exact hg

private theorem torusPoints_subgroupOf_le_comap_weylSubgroupMap
    {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) :
    Subgroup.subgroupOf (MonoidHom.range (D.torusPoints A)) (D.weylSubgroup A) ≤
      (Subgroup.subgroupOf (MonoidHom.range (D.torusPoints B)) (D.weylSubgroup B)).comap
        (D.weylSubgroupMap A f) := by
  rintro x ⟨s, hs⟩
  have hx : x = ⟨D.torusPoints A s, D.torusPoints_mem_weylSubgroup A s⟩ := Subtype.ext hs.symm
  rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, hx, D.weylSubgroupMap_torusPoints]
  exact ⟨_, rfl⟩

private def quotientMap {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) :
    D.weylSubgroup A ⧸
        Subgroup.subgroupOf (MonoidHom.range (D.torusPoints A)) (D.weylSubgroup A) →*
      D.weylSubgroup B ⧸
        Subgroup.subgroupOf (MonoidHom.range (D.torusPoints B)) (D.weylSubgroup B) :=
  QuotientGroup.map _ _ (D.weylSubgroupMap A f)
    (D.torusPoints_subgroupOf_le_comap_weylSubgroupMap f)

private theorem quotientMap_comp_quotientSection
    {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) :
    (D.quotientMap f).comp (D.quotientSection A) = D.quotientSection B := by
  apply (weylCoxeterSystem (t.simplyConnectedRootDatum ht)
    (t.simplyConnectedBase ht)).ext_simple
  intro a
  obtain ⟨i, rfl⟩ := (t.simpleSupportEquivSimplyConnectedBase ht).surjective a
  simp only [MonoidHom.comp_apply, weylCoxeterSystem_simple,
    coe_simpleSupportEquivSimplyConnectedBase_apply, D.quotientSection_simple,
    simpleClass, quotientMap, QuotientGroup.map_mk, simpleLift, D.weylSubgroupMap_weylElement]

private def fieldQuotientProjection (K : Type*) [Field K] :
    D.weylSubgroup K ⧸
        Subgroup.subgroupOf (MonoidHom.range (D.torusPoints K)) (D.weylSubgroup K) →*
      (t.simplyConnectedRootDatum ht).weylGroup :=
  QuotientGroup.lift _ (D.weylProjection K) (by
    rintro x ⟨s, hs⟩
    have hx : x = ⟨D.torusPoints K s, D.torusPoints_mem_weylSubgroup K s⟩ := Subtype.ext hs.symm
    rw [MonoidHom.mem_ker, hx, D.weylProjection_torusPoints])

private theorem fieldQuotientProjection_comp_quotientSection (K : Type*) [Field K] :
    (D.fieldQuotientProjection K).comp (D.quotientSection K) = MonoidHom.id _ := by
  apply (weylCoxeterSystem (t.simplyConnectedRootDatum ht)
    (t.simplyConnectedBase ht)).ext_simple
  intro a
  obtain ⟨i, rfl⟩ := (t.simpleSupportEquivSimplyConnectedBase ht).surjective a
  simp only [MonoidHom.comp_apply, MonoidHom.id_apply, weylCoxeterSystem_simple,
    coe_simpleSupportEquivSimplyConnectedBase_apply, D.quotientSection_simple,
    simpleClass, fieldQuotientProjection, QuotientGroup.lift_mk', simpleLift,
    D.weylProjection_weylElement]

private theorem quotientSection_injective [Nontrivial A] :
    Function.Injective (D.quotientSection A) := by
  -- A residue field detects the Weyl word, without requiring a projection over rings.
  obtain ⟨M, hM⟩ := Ideal.exists_maximal A
  let : M.IsMaximal := hM
  let := Ideal.Quotient.field M
  have hp : ((D.fieldQuotientProjection (A ⧸ M)).comp
        (D.quotientMap (Ideal.Quotient.mk M))).comp (D.quotientSection A) = MonoidHom.id _ := by
    rw [MonoidHom.comp_assoc, D.quotientMap_comp_quotientSection,
      D.fieldQuotientProjection_comp_quotientSection]
  exact Function.LeftInverse.injective
      (g := (D.fieldQuotientProjection (A ⧸ M)).comp (D.quotientMap (Ideal.Quotient.mk M)))
      fun w => by
    simpa only [MonoidHom.comp_apply, MonoidHom.id_apply] using DFunLike.congr_fun hp w

/-- The quotient of a Chevalley datum's Weyl subgroup by its actual torus is the Weyl
group of the pinned root datum, over every nontrivial commutative ring and every valid Dynkin
type (including `G₂`). -/
def weylQuotientMulEquiv [Nontrivial A] :
    Q ≃* (t.simplyConnectedRootDatum ht).weylGroup :=
  (MulEquiv.ofBijective (D.quotientSection A)
    ⟨D.quotientSection_injective A, D.quotientSection_surjective A⟩).symm

private theorem weylQuotientMulEquiv_symm_apply [Nontrivial A]
    (w : (t.simplyConnectedRootDatum ht).weylGroup) :
    (D.weylQuotientMulEquiv A).symm w = D.quotientSection A w := by
  rw [weylQuotientMulEquiv, MulEquiv.symm_symm]
  exact MulEquiv.ofBijective_apply _ _ _

/-- The inverse Weyl quotient equivalence sends a pinned simple reflection to the class
of its pinned Weyl representative. -/
@[simp↓]
theorem weylQuotientMulEquiv_symm_ofIdx [Nontrivial A]
    (i : Fin t.rank) :
    (D.weylQuotientMulEquiv A).symm
        (RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht) (t.simpleIndex ht i)) =
      QuotientGroup.mk
        ⟨D.weylElement (t.simpleIndex ht i) A 1, D.weylElement_mem_weylSubgroup A i⟩ := by
  rw [D.weylQuotientMulEquiv_symm_apply, D.quotientSection_simple, simpleClass,
    simpleLift]

/-- The Weyl quotient equivalence sends the class of a pinned simple Weyl representative
to its simple reflection. -/
@[simp↓]
theorem weylQuotientMulEquiv_mk_weylElement [Nontrivial A]
    (i : Fin t.rank) :
    D.weylQuotientMulEquiv A
        (QuotientGroup.mk
          ⟨D.weylElement (t.simpleIndex ht i) A 1, D.weylElement_mem_weylSubgroup A i⟩) =
      RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht) (t.simpleIndex ht i) := by
  apply (D.weylQuotientMulEquiv A).eq_symm_apply.mp
  exact (D.weylQuotientMulEquiv_symm_ofIdx A i).symm

/-- The Weyl quotient equivalence sends the class of an actual torus point to `1`. -/
@[simp]
theorem weylQuotientMulEquiv_mk_torusPoints [Nontrivial A] (s : Fin t.rank → Aˣ) :
    D.weylQuotientMulEquiv A
        (QuotientGroup.mk ⟨D.torusPoints A s, D.torusPoints_mem_weylSubgroup A s⟩) = 1 := by
  rw [D.mk_torusPoints A s (D.torusPoints_mem_weylSubgroup A s), map_one]

/-- The canonical Weyl-quotient isomorphism commutes with every ring homomorphism between
nontrivial commutative rings. -/
theorem weylQuotientMulEquiv_map {A : Type*} {B : Type*}
    [CommRing A] [Nontrivial A] [CommRing B] [Nontrivial B]
    (f : A →+* B) (g : D.weylSubgroup A) :
    D.weylQuotientMulEquiv B (QuotientGroup.mk (D.weylSubgroupMap A f g)) =
      D.weylQuotientMulEquiv A (QuotientGroup.mk g) := by
  have hw := DFunLike.congr_fun (D.quotientMap_comp_quotientSection f)
    (D.weylQuotientMulEquiv A (QuotientGroup.mk g))
  have hsecA : D.quotientSection A (D.weylQuotientMulEquiv A (QuotientGroup.mk g)) =
      QuotientGroup.mk g := by
    rw [← D.weylQuotientMulEquiv_symm_apply, MulEquiv.symm_apply_apply]
  have hsecB : D.quotientSection B (D.weylQuotientMulEquiv A (QuotientGroup.mk g)) =
      QuotientGroup.mk (D.weylSubgroupMap A f g) := by
    simpa only [MonoidHom.comp_apply, hsecA, quotientMap, QuotientGroup.map_mk] using hw.symm
  apply (D.weylQuotientMulEquiv B).symm.injective
  rw [MulEquiv.symm_apply_apply, D.weylQuotientMulEquiv_symm_apply, hsecB]

/-- On a product of a Weyl word and an actual torus point, `D.weylQuotientMulEquiv A` evaluates
to the Weyl-group element spelled by the word. -/
theorem weylQuotientMulEquiv_list_prod_mul_torusPoints [Nontrivial A]
    (l : List (Fin t.rank)) (s : Fin t.rank → Aˣ) :
    D.weylQuotientMulEquiv A
        (QuotientGroup.mk
          ⟨(l.map fun i => D.weylElement (t.simpleIndex ht i) A 1).prod * D.torusPoints A s,
            mul_mem (D.list_prod_map_weylElement_mem_weylSubgroup A l)
              (D.torusPoints_mem_weylSubgroup A s)⟩) =
      t.geckWeylWordProd ht l := by
  have hsub :
      (⟨(l.map fun i => D.weylElement (t.simpleIndex ht i) A 1).prod * D.torusPoints A s,
          mul_mem (D.list_prod_map_weylElement_mem_weylSubgroup A l)
            (D.torusPoints_mem_weylSubgroup A s)⟩ : N) =
        (l.map (D.simpleLift A)).prod *
          ⟨D.torusPoints A s, D.torusPoints_mem_weylSubgroup A s⟩ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.val_list_prod, List.map_map, Function.comp_def,
      simpleLift]
  rw [hsub, QuotientGroup.mk_mul, map_mul, D.weylQuotientMulEquiv_mk_torusPoints A s, mul_one,
    ← QuotientGroup.mk'_apply, map_list_prod (QuotientGroup.mk' H),
    map_list_prod (D.weylQuotientMulEquiv A), List.map_map, List.map_map]
  simp only [Function.comp_def, QuotientGroup.mk'_apply, simpleLift,
    D.weylQuotientMulEquiv_mk_weylElement]
  clear hsub
  induction l with
  | nil => simp
  | cons i l ih => simp [ih]

end

noncomputable section

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)
variable (K : Type*) [Field K]

local notation "Nₖ" => D.weylSubgroup K
local notation "Hₖ" => Subgroup.subgroupOf (MonoidHom.range (D.torusPoints K)) Nₖ

private theorem quotientSection_comp_fieldQuotientProjection :
    (D.quotientSection K).comp (D.fieldQuotientProjection K) = MonoidHom.id _ :=
  MonoidHom.ext fun q =>
    (Function.LeftInverse.rightInverse_of_surjective
      (fun w => by
        simpa only [MonoidHom.comp_apply, MonoidHom.id_apply] using
          DFunLike.congr_fun (D.fieldQuotientProjection_comp_quotientSection K) w)
      (D.quotientSection_surjective K)) q

/-- The inverse Weyl quotient equivalence sends a Weyl projection to its quotient class. -/
@[simp]
theorem weylQuotientMulEquiv_symm_weylProjection (g : Nₖ) :
    (D.weylQuotientMulEquiv K).symm (D.weylProjection K g) =
      QuotientGroup.mk g := by
  rw [D.weylQuotientMulEquiv_symm_apply]
  have hg : D.weylProjection K g = D.fieldQuotientProjection K (QuotientGroup.mk g) := by
    simp only [fieldQuotientProjection, QuotientGroup.lift_mk]
  rw [hg, ← MonoidHom.comp_apply, D.quotientSection_comp_fieldQuotientProjection K,
    MonoidHom.id_apply]

/-- The Weyl quotient equivalence is induced by the native Weyl projection. -/
@[simp]
theorem weylQuotientMulEquiv_mk (g : Nₖ) :
    D.weylQuotientMulEquiv K (QuotientGroup.mk g) = D.weylProjection K g := by
  apply (D.weylQuotientMulEquiv K).eq_symm_apply.mp
  exact (D.weylQuotientMulEquiv_symm_weylProjection K g).symm

/-- Over every field, the Weyl projection has kernel exactly the actual torus,
regarded as a subgroup of the subgroup generated by the torus and Weyl representatives. -/
@[simp]
theorem ker_weylProjection :
    (D.weylProjection K).ker = Hₖ := by
  have hcomp :
      (D.weylQuotientMulEquiv K).toMonoidHom.comp (QuotientGroup.mk' Hₖ) =
        D.weylProjection K :=
    MonoidHom.ext fun g => D.weylQuotientMulEquiv_mk K g
  rw [← hcomp, MonoidHom.ker_comp_of_injective _ _ (D.weylQuotientMulEquiv K).injective,
    QuotientGroup.ker_mk']

/-- A point of `N` has trivial Weyl projection exactly when it is a torus point. -/
theorem weylProjection_eq_one_iff_mem_range_torusPoints (g : Nₖ) :
    D.weylProjection K g = 1 ↔ (g : D.points K) ∈ (D.torusPoints K).range := by
  rw [← MonoidHom.mem_ker, ker_weylProjection, Subgroup.mem_subgroupOf]

/-- On a product of a Weyl word and an actual torus point, `D.weylProjection K` evaluates to the
Weyl-group element spelled by the word. -/
theorem weylProjection_list_prod_mul_torusPoints (l : List (Fin t.rank))
    (s : Fin t.rank → Kˣ) :
    D.weylProjection K
      ⟨(l.map fun i => D.weylElement (t.simpleIndex ht i) K 1).prod * D.torusPoints K s,
        mul_mem (D.list_prod_map_weylElement_mem_weylSubgroup K l)
          (D.torusPoints_mem_weylSubgroup K s)⟩ =
      t.geckWeylWordProd ht l := by
  rw [← D.weylQuotientMulEquiv_mk, D.weylQuotientMulEquiv_list_prod_mul_torusPoints K l s]

end

end TauCeti.DynkinType.ChevalleyDatum
