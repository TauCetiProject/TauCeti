/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Bruhat.Generation
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Torus.Weyl
public import TauCeti.GroupTheory.TitsSystem.Basic
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Positive.Blocks
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Positive.Parabolic
import TauCeti.Algebra.AlgebraicGroup.Chevalley.RankOne
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Weyl.Root
import TauCeti.GroupTheory.QuotientGroup.KerEquiv
import TauCeti.GroupTheory.TitsSystem.Bruhat.Uniqueness
import TauCeti.GroupTheory.TitsSystem.Parabolic.Normalizer
import TauCeti.LinearAlgebra.Matrix.Diagonal
import TauCeti.LinearAlgebra.RootSystem.Inversions.StrongExchange

/-!
# The Tits system, Weyl quotient, and Bruhat decomposition of a Chevalley datum

Over an arbitrary field `K` (finite or infinite, of any characteristic), the extended
elementary subgroup `E(K)` of any Chevalley datum `D` carries a Tits system `(B(K), N(K))`
whose distinguished subgroups are `D.borelSubgroup K` and `D.weylSubgroup K`, with simple
reflections represented by the pinned simple Weyl elements `nᵢ(1)`.

The intersection `B(K) ∩ N(K)` equals the actual character-lattice torus `T(K)`: an element
of `B(K) ∩ N(K)` preserves the positive roots under its Weyl projection, hence projects to
`1`, and its positive factor commutes with the represented full-weight torus after extension
to `AlgebraicClosure K`, forcing it to preserve every weight space and therefore to be `1`.

The Tits multiplication axiom `B nᵢ B w B ⊆ B (nᵢ w) B ∪ B w B` combines the all-type
punctured-positive factorization of `B(K)` with the root action of `N(K)` and the rank-one
Bruhat collection theorem `ChevalleyDatum.mem_sup_simpleRootPair_torus_iff`. From the
resulting `TauCeti.TitsSystem` on `E(K)`, self-normalization of `B(K)` identifies the kernel
of `D.weylProjection K` with `T(K)`, yielding the Weyl quotient isomorphism
`N(K) / T(K) ≃* W` and the disjoint Bruhat decomposition `E(K) = ⨆ w ∈ W, B(K) n_w B(K)`
indexed directly by the Weyl group of `DynkinType.simplyConnectedRootDatum`.

Neither point generation of the ambient group scheme nor the refined unipotent normal form
inside each Bruhat cell is asserted here.

## Main definitions

* `ChevalleyDatum.titsSystem`: the Tits system `(B(K), N(K))` on
  `D.extendedElementarySubgroup K` over any field `K`.
* `ChevalleyDatum.weylSubgroupQuotientEquivWeylGroup`: the isomorphism `N(K) / T(K) ≃* W`
  induced by `D.weylProjection K`.
* `ChevalleyDatum.titsSystemWeylGroupEquiv`: the isomorphism identifying the Weyl quotient
  of `D.titsSystem K` with the root datum's Weyl group.
* `ChevalleyDatum.bruhatCell`: the Bruhat cell `B(K) n_w B(K)` inside `D.points K`, indexed
  directly by `w ∈ W`.

## Main results

* `ChevalleyDatum.mem_borelSubgroup_iff_exists_mul_torusPoints_mul_rootSubgroupPoints`:
  simple-root factorization of `B(A)` over every commutative ring `A`.
* `ChevalleyDatum.borelSubgroup_inf_weylSubgroup`: `B(K) ∩ N(K) = T(K)` over every field `K`.
* `ChevalleyDatum.normalizer_borelSubgroup_inf_extendedElementarySubgroup`: `B(K)` is
  self-normalizing in `E(K)`.
* `ChevalleyDatum.ker_weylProjection`: the kernel of `D.weylProjection K` is the actual
  torus `T(K)`.
* `ChevalleyDatum.iUnion_bruhatCell`, `ChevalleyDatum.disjoint_bruhatCell_iff`, and
  `ChevalleyDatum.existsUnique_mem_bruhatCell`: the Bruhat decomposition of `E(K)` into
  pairwise disjoint cells indexed by `W`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Theorem 4 and Lemma 25.
* R. W. Carter, *Simple Groups of Lie Type*, §§7.2 and 8.2–8.3.
-/

public section

open scoped Pointwise
open Multiplicative TauCeti.UniversalEnvelopingAlgebra

namespace TauCeti.DynkinType.ChevalleyDatum

universe v

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

/-! ## Simple-root factorization of the Borel-type subgroup -/

private theorem iSup_posRoots_diff_singleton_le_positivePoints
    (A : Type v) [CommRing A] (i : Fin t.rank) :
    (⨆ γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht) \ {t.simpleIndex ht i},
      (D.rootSubgroupPoints γ A).range : Subgroup (D.points A)) ≤ D.positivePoints A := by
  refine iSup₂_le fun γ hγ => ?_
  rintro _ ⟨a, rfl⟩
  exact D.rootSubgroupPoints_mem_positivePoints A hγ.1 a

/-- Over every commutative ring, every element of the Borel-type subgroup factors as a
punctured-positive element, followed by a point of the actual torus, followed by an element
of the chosen positive simple root subgroup. No uniqueness of these factors is asserted. -/
theorem mem_borelSubgroup_iff_exists_mul_torusPoints_mul_rootSubgroupPoints
    (A : Type v) [CommRing A] (i : Fin t.rank) (g : D.points A) :
    g ∈ D.borelSubgroup A ↔
      ∃ v ∈ (⨆ γ ∈
        posRoots (t.rationalRootSystem ht) (t.rationalBase ht) \ {t.simpleIndex ht i},
        (D.rootSubgroupPoints γ A).range : Subgroup (D.points A)),
        ∃ s : Fin t.rank → Aˣ, ∃ u : Multiplicative A,
          g = v * D.torusPoints A s * D.rootSubgroupPoints (t.simpleIndex ht i) A u := by
  constructor
  · intro hg
    obtain ⟨p, hp, s, rfl⟩ := (D.mem_borelSubgroup_iff A).mp hg
    obtain ⟨v, hv, u, rfl⟩ := (D.mem_positivePoints_iff_exists_mul_rootSubgroupPoints A i p).mp hp
    have hconj := D.torusPoints_conj_rootSubgroupPoints (t.simpleIndex ht i) A s⁻¹ (toAdd u)
    rw [map_inv, inv_inv, ofAdd_toAdd] at hconj
    refine ⟨v, hv, s, ofAdd ((torusCharacter s⁻¹ (D.coordinateRoot (t.simpleIndex ht i)) : A) *
      toAdd u), ?_⟩
    rw [← hconj]
    group
  · rintro ⟨v, hv, s, u, rfl⟩
    exact (D.borelSubgroup A).mul_mem
      ((D.borelSubgroup A).mul_mem
        (D.positivePoints_le_borelSubgroup A
          (D.iSup_posRoots_diff_singleton_le_positivePoints A i hv))
        (D.range_torusPoints_le_borelSubgroup A ⟨s, rfl⟩))
      (D.positivePoints_le_borelSubgroup A
        (D.rootSubgroupPoints_mem_positivePoints A (simpleIndex_mem_posRoots i) u))

/-! ## Intersection of the Borel and Weyl subgroups -/

variable (K : Type v) [Field K]

/-- An element of `B(K) ∩ N(K)` keeps every positive root positive under its Weyl projection,
so its Weyl projection is trivial. -/
private theorem weylProjection_eq_one_of_mem_borelSubgroup
    {g : D.weylSubgroup K} (hg : (g : D.points K) ∈ D.borelSubgroup K) :
    D.weylProjection K g = 1 := by
  let _ := t.isReduced_simplyConnectedRootDatum ht
  apply TauCeti.eq_one_of_mapsTo_posRoots
    (P := t.simplyConnectedRootDatum ht) (b := t.simplyConnectedBase ht)
  intro γ hγ
  by_contra hnotpos
  have hneg : (t.simplyConnectedRootDatum ht).weylGroupToPerm (D.weylProjection K g) γ ∈
      negRoots (t.rationalRootSystem ht) (t.rationalBase ht) := by
    simp only [mem_negRoots, RootPairing.Base.isPos_iff, height_rationalBase]
    exact fun hp => hnotpos ((mem_posRoots _ _ _).mpr ((RootPairing.Base.isPos_iff _).mpr hp))
  have hγ_rat : γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht) := by
    rwa [posRoots_rationalRootSystem]
  let x := D.rootSubgroupPoints γ K (ofAdd 1)
  have hx_conj_B : MulAut.conj (g : D.points K) x ∈ D.borelSubgroup K :=
    D.positivePoints_le_borelSubgroup K <|
      (Subgroup.mem_normalizer_iff.mp (D.borelSubgroup_le_normalizer_positivePoints K hg) x).mp
        (D.rootSubgroupPoints_mem_positivePoints K hγ_rat (ofAdd 1))
  have hx_conj_range : MulAut.conj (g : D.points K) x ∈
      (D.rootSubgroupPoints
        ((t.simplyConnectedRootDatum ht).weylGroupToPerm (D.weylProjection K g) γ) K).range := by
    rw [← D.map_range_rootSubgroupPoints_conj K g γ]
    exact Subgroup.mem_map_of_mem _ ⟨ofAdd 1, rfl⟩
  obtain ⟨u, hu⟩ := hx_conj_range
  have hu_one : D.rootSubgroupPoints
      ((t.simplyConnectedRootDatum ht).weylGroupToPerm (D.weylProjection K g) γ) K u = 1 :=
    (D.rootSubgroupPoints_mem_borelSubgroup_iff_of_mem_negRoots K hneg u).mp (hu.symm ▸ hx_conj_B)
  have hx_one : x = 1 :=
    (MulAut.conj (g : D.points K)).injective (by rw [← hu, hu_one, map_one])
  exact D.rootSubgroupPoints_ofAdd_one_ne_one K γ hx_one

/-- A positive point in `N(K)` with trivial Weyl projection commutes with the full-weight
torus over `AlgebraicClosure K`, hence preserves every weight space and must equal `1`. -/
private theorem eq_one_of_mem_positivePoints_of_weylProjection_eq_one
    {u : D.weylSubgroup K} (hu : (u : D.points K) ∈ D.positivePoints K)
    (hw : D.weylProjection K u = 1) : (u : D.points K) = 1 := by
  let φ := (D.pointsPresentation K).map (D.pointsPresentation (AlgebraicClosure K))
    (algebraMap K (AlgebraicClosure K))
  let u' : D.points (AlgebraicClosure K) := φ (u : D.points K)
  have hcoe : (u' : Matrix.GeneralLinearGroup (Fin D.dim) (AlgebraicClosure K)) =
      Matrix.GeneralLinearGroup.map (algebraMap K (AlgebraicClosure K))
        ((u : D.points K) : Matrix.GeneralLinearGroup (Fin D.dim) K) :=
    (D.pointsPresentation K).coe_map (D.pointsPresentation (AlgebraicClosure K))
      (algebraMap K (AlgebraicClosure K)) (u : D.points K)
  have hu'_pos : u' ∈ D.positivePoints (AlgebraicClosure K) :=
    D.map_positivePoints_le (algebraMap K (AlgebraicClosure K)) ⟨(u : D.points K), hu, rfl⟩
  have hcomm (s : Fin t.rank → (AlgebraicClosure K)ˣ) :
      Commute (Matrix.diagonal (fun j => (torusCharacter s (D.weight j) : AlgebraicClosure K)))
        ((u' : Matrix.GeneralLinearGroup (Fin D.dim) (AlgebraicClosure K)) :
          Matrix (Fin D.dim) (Fin D.dim) (AlgebraicClosure K)) := by
    have hconj := (D.weylProjection_eq_iff K u 1).mp hw s
    simp only [map_one, MulAut.one_apply, mul_inv_eq_iff_eq_mul] at hconj
    rw [← hcoe] at hconj
    have hmat := congrArg Units.val hconj
    rw [Commute, SemiconjBy]
    simpa only [Units.val_mul, diagGL_coe] using hmat.symm
  have hu'_one : u' = 1 := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    by_cases hij : D.weight i = D.weight j
    · simpa only [Subgroup.coe_one, Units.val_one] using
        D.coe_apply_eq_one_apply_of_mem_positivePoints_of_weight_eq (AlgebraicClosure K)
          hu'_pos hij
    · obtain ⟨s, hs⟩ := exists_torusCharacter_ne (K := AlgebraicClosure K) hij
      have hne : i ≠ j := fun heq => hij (congrArg D.weight heq)
      have hzero := apply_eq_zero_of_commute_diagonal (hcomm s) (Units.val_injective.ne hs)
      simpa only [Subgroup.coe_one, Units.val_one, Matrix.one_apply, hne, ↓reduceIte] using hzero
  apply Subtype.ext
  apply Matrix.GeneralLinearGroup.map_injective (algebraMap K (AlgebraicClosure K)).injective
  rw [← hcoe, congrArg Subtype.val hu'_one, Subgroup.coe_one, Subgroup.coe_one, map_one]

/-- Over every field (finite or infinite, of any characteristic), the intersection of the
Borel-type subgroup and the Weyl subgroup is the actual character-lattice torus. -/
@[simp]
theorem borelSubgroup_inf_weylSubgroup :
    D.borelSubgroup K ⊓ D.weylSubgroup K = (D.torusPoints K).range := by
  apply le_antisymm
  · rintro g ⟨hgB, hgN⟩
    have hgw : D.weylProjection K ⟨g, hgN⟩ = 1 :=
      D.weylProjection_eq_one_of_mem_borelSubgroup K hgB
    obtain ⟨u, huU, s, hsg⟩ := (D.mem_borelSubgroup_iff K).mp hgB
    have hu_eq : u = g * (D.torusPoints K s)⁻¹ := by
      rw [← hsg, mul_inv_cancel_right]
    have huN : u ∈ D.weylSubgroup K := by
      rw [hu_eq]
      exact (D.weylSubgroup K).mul_mem hgN
        ((D.weylSubgroup K).inv_mem (D.torusPoints_mem_weylSubgroup K s))
    have hu_sub : (⟨u, huN⟩ : D.weylSubgroup K) =
        ⟨g, hgN⟩ * ⟨D.torusPoints K s, D.torusPoints_mem_weylSubgroup K s⟩⁻¹ :=
      Subtype.ext hu_eq
    have huw : D.weylProjection K ⟨u, huN⟩ = 1 := by
      rw [hu_sub, map_mul, map_inv, hgw, D.weylProjection_torusPoints, inv_one, mul_one]
    have hu_one : u = 1 :=
      D.eq_one_of_mem_positivePoints_of_weylProjection_eq_one K (u := ⟨u, huN⟩) huU huw
    exact ⟨s, by rw [← hsg, hu_one, one_mul]⟩
  · refine le_inf (D.range_torusPoints_le_borelSubgroup K) ?_
    rintro _ ⟨s, rfl⟩
    exact D.torusPoints_mem_weylSubgroup K s

/-! ## The Tits multiplication axiom and the Tits system on `E(K)` -/

/-- When `w⁻¹(αᵢ)` is positive, moving a positive simple root element past `w` lands directly
in the adjacent Bruhat double coset `B (nᵢ w) B`. -/
private theorem weylElement_mul_rootSubgroup_mul_mem_doubleCoset_of_pos
    (i : Fin t.rank) (w : D.weylSubgroup K) (u : Multiplicative K)
    (hpos : (t.simplyConnectedRootDatum ht).weylGroupToPerm (D.weylProjection K w)⁻¹
        (t.simpleIndex ht i) ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht)) :
    D.weylElement (t.simpleIndex ht i) K 1 *
        D.rootSubgroupPoints (t.simpleIndex ht i) K u * (w : D.points K) ∈
      DoubleCoset.doubleCoset (D.weylElement (t.simpleIndex ht i) K 1 * (w : D.points K))
        (D.borelSubgroup K) (D.borelSubgroup K) := by
  have hconj_range : MulAut.conj ((w⁻¹ : D.weylSubgroup K) : D.points K)
        (D.rootSubgroupPoints (t.simpleIndex ht i) K u) ∈
      (D.rootSubgroupPoints
        ((t.simplyConnectedRootDatum ht).weylGroupToPerm (D.weylProjection K w⁻¹)
          (t.simpleIndex ht i)) K).range := by
    rw [← D.map_range_rootSubgroupPoints_conj K w⁻¹ (t.simpleIndex ht i)]
    exact Subgroup.mem_map_of_mem _ ⟨u, rfl⟩
  rw [map_inv] at hconj_range
  obtain ⟨u', hu'⟩ := hconj_range
  have hb : MulAut.conj ((w⁻¹ : D.weylSubgroup K) : D.points K)
      (D.rootSubgroupPoints (t.simpleIndex ht i) K u) ∈ D.borelSubgroup K := by
    rw [← hu']
    exact D.positivePoints_le_borelSubgroup K (D.rootSubgroupPoints_mem_positivePoints K hpos u')
  refine DoubleCoset.mem_doubleCoset.mpr
    ⟨1, (D.borelSubgroup K).one_mem,
      MulAut.conj ((w⁻¹ : D.weylSubgroup K) : D.points K)
        (D.rootSubgroupPoints (t.simpleIndex ht i) K u),
      hb, ?_⟩
  simp only [one_mul, MulAut.conj_apply, Subgroup.coe_inv]
  group

private theorem weylGroupToPerm_inv_weylElement_mul_mem_posRoots
    (i : Fin t.rank) (w : D.weylSubgroup K)
    (hnotpos : (t.simplyConnectedRootDatum ht).weylGroupToPerm (D.weylProjection K w)⁻¹
        (t.simpleIndex ht i) ∉ posRoots (t.rationalRootSystem ht) (t.rationalBase ht)) :
    (t.simplyConnectedRootDatum ht).weylGroupToPerm
        (D.weylProjection K
          (⟨D.weylElement (t.simpleIndex ht i) K 1,
            D.weylElement_mem_weylSubgroup K i⟩ * w))⁻¹
        (t.simpleIndex ht i) ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht) := by
  have hsi : (RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht)
      (t.simpleIndex ht i))⁻¹ =
      RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht) (t.simpleIndex ht i) :=
    inv_eq_of_mul_eq_one_right (RootPairing.weylGroup.ofIdx_mul_self _ _)
  have hw' : (D.weylProjection K
      (⟨D.weylElement (t.simpleIndex ht i) K 1,
        D.weylElement_mem_weylSubgroup K i⟩ * w))⁻¹ =
      (D.weylProjection K w)⁻¹ *
        RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht) (t.simpleIndex ht i) := by
    simp only [map_mul, mul_inv_rev, D.weylProjection_weylElement, hsi]
  rw [hw', RootPairing.weylGroupToPerm_mul_ofIdx_apply]
  let _ := (t.simplyConnectedRootDatum ht).indexNeg
  rw [← RootPairing.indexNeg_neg, RootPairing.weylGroupToPerm_neg,
    posRoots_rationalRootSystem, mem_posRoots, RootPairing.Base.IsPos.neg_iff_not]
  intro hp
  exact hnotpos (by rw [posRoots_rationalRootSystem, mem_posRoots]; exact hp)

private theorem weylElement_conj_rootSubgroupPoints_mem_sup
    (i : Fin t.rank) (u : Multiplicative K) :
    D.weylElement (t.simpleIndex ht i) K 1 *
        D.rootSubgroupPoints (t.simpleIndex ht i) K u *
        (D.weylElement (t.simpleIndex ht i) K 1)⁻¹ ∈
      Subgroup.closure
        (Set.range (D.rootSubgroupPoints (t.simpleIndex ht i) K) ∪
          Set.range (D.rootSubgroupPoints ((t.simplyConnectedRootDatum ht).reflectionPerm
            (t.simpleIndex ht i) (t.simpleIndex ht i)) K)) ⊔ (D.torusPoints K).range := by
  apply Subgroup.mem_sup_left
  apply Subgroup.subset_closure
  refine Or.inr ⟨ofAdd (((t.chevalleyWeylSign ht (t.simpleIndex ht i)
    (t.simpleIndex ht i) : ℤ) : K) * toAdd u), ?_⟩
  simpa only [ofAdd_toAdd] using
    (D.weylElement_conj_rootSubgroupPoints i (t.simpleIndex ht i) K (toAdd u)).symm

/-- For every simple root `αᵢ`, root element `xᵢ(u)`, and Weyl lift `w`, the product
`nᵢ xᵢ(u) w` lies in `B (nᵢ w) B ∪ B w B`. -/
private theorem weylElement_mul_rootSubgroup_mul_mem_union_doubleCoset
    (i : Fin t.rank) (w : D.weylSubgroup K) (u : Multiplicative K) :
    D.weylElement (t.simpleIndex ht i) K 1 *
        D.rootSubgroupPoints (t.simpleIndex ht i) K u * (w : D.points K) ∈
      DoubleCoset.doubleCoset (D.weylElement (t.simpleIndex ht i) K 1 * (w : D.points K))
          (D.borelSubgroup K) (D.borelSubgroup K) ∪
        DoubleCoset.doubleCoset (w : D.points K)
          (D.borelSubgroup K) (D.borelSubgroup K) := by
  by_cases hpos : (t.simplyConnectedRootDatum ht).weylGroupToPerm (D.weylProjection K w)⁻¹
      (t.simpleIndex ht i) ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht)
  · exact Or.inl (D.weylElement_mul_rootSubgroup_mul_mem_doubleCoset_of_pos K i w u hpos)
  · -- When `w⁻¹(αᵢ)` is negative, rewrite `nᵢ xᵢ(u) nᵢ⁻¹` by rank-one Bruhat collection,
    -- then apply the positive case to `w' = nᵢ w`.
    let n := D.weylElement (t.simpleIndex ht i) K 1
    let nN : D.weylSubgroup K := ⟨n, D.weylElement_mem_weylSubgroup K i⟩
    let w' : D.weylSubgroup K := nN * w
    have hpos' := D.weylGroupToPerm_inv_weylElement_mul_mem_posRoots K i w hpos
    let y := n * D.rootSubgroupPoints (t.simpleIndex ht i) K u * n⁻¹
    rcases (D.mem_sup_simpleRootPair_torus_iff i K y).mp
        (D.weylElement_conj_rootSubgroupPoints_mem_sup K i u) with
      ⟨a, s, hy⟩ | ⟨a, b, s, hy⟩
    · refine Or.inl (DoubleCoset.mem_doubleCoset.mpr ⟨y, ?_, 1, (D.borelSubgroup K).one_mem, ?_⟩)
      · rw [hy]
        exact (D.borelSubgroup K).mul_mem
          (D.positivePoints_le_borelSubgroup K
            (D.rootSubgroupPoints_mem_positivePoints K (simpleIndex_mem_posRoots i) _))
          (D.range_torusPoints_le_borelSubgroup K ⟨s, rfl⟩)
      · simp only [y, n, mul_one]
        group
    · have hconj_s := D.torusPoints_conj_rootSubgroupPoints (t.simpleIndex ht i) K s⁻¹ b
      rw [map_inv, inv_inv] at hconj_s
      let u' := ofAdd ((torusCharacter s⁻¹ (D.coordinateRoot (t.simpleIndex ht i)) : K) * b)
      obtain ⟨b₁, hb₁, b₂, hb₂, hcell_eq⟩ := DoubleCoset.mem_doubleCoset.mp
        (D.weylElement_mul_rootSubgroup_mul_mem_doubleCoset_of_pos K i w' u' hpos')
      have hxa : D.rootSubgroupPoints (t.simpleIndex ht i) K (ofAdd a) ∈ D.borelSubgroup K :=
        D.positivePoints_le_borelSubgroup K
          (D.rootSubgroupPoints_mem_positivePoints K (simpleIndex_mem_posRoots i) _)
      have ht₁ : n * D.torusPoints K s * n⁻¹ ∈ D.borelSubgroup K :=
        D.range_torusPoints_le_borelSubgroup K <|
          (Subgroup.mem_normalizer_iff.mp
            (D.weylElement_mem_normalizer_range_torusPoints i K) (D.torusPoints K s)).mp ⟨s, rfl⟩
      have hnn : n * n ∈ D.borelSubgroup K := by
        dsimp only [n]
        rw [D.weylElement_mul_self i K, D.simpleCorootPoints_eq_torusPoints]
        exact D.range_torusPoints_le_borelSubgroup K ⟨_, rfl⟩
      refine Or.inr (DoubleCoset.mem_doubleCoset.mpr
        ⟨D.rootSubgroupPoints (t.simpleIndex ht i) K (ofAdd a) *
            (n * D.torusPoints K s * n⁻¹) * b₁ * (n * n),
          (D.borelSubgroup K).mul_mem
            ((D.borelSubgroup K).mul_mem ((D.borelSubgroup K).mul_mem hxa ht₁) hb₁) hnn,
          b₂, hb₂, ?_⟩)
      have hcomm_x : D.rootSubgroupPoints (t.simpleIndex ht i) K (ofAdd b) * D.torusPoints K s =
          D.torusPoints K s * D.rootSubgroupPoints (t.simpleIndex ht i) K u' := by
        dsimp only [u']
        rw [← hconj_s]
        group
      calc
        D.weylElement (t.simpleIndex ht i) K 1 *
            D.rootSubgroupPoints (t.simpleIndex ht i) K u * (w : D.points K)
            = y * (w' : D.points K) := by
              simp only [y, w', nN, n, Subgroup.coe_mul]
              group
        _ = D.rootSubgroupPoints (t.simpleIndex ht i) K (ofAdd a) * n *
              (D.rootSubgroupPoints (t.simpleIndex ht i) K (ofAdd b) * D.torusPoints K s) *
              (w' : D.points K) := by
              rw [hy]; dsimp only [n]; group
        _ = D.rootSubgroupPoints (t.simpleIndex ht i) K (ofAdd a) * n *
              (D.torusPoints K s * D.rootSubgroupPoints (t.simpleIndex ht i) K u') *
              (w' : D.points K) := by
              rw [hcomm_x]
        _ = D.rootSubgroupPoints (t.simpleIndex ht i) K (ofAdd a) *
              (n * D.torusPoints K s * n⁻¹) *
              (n * D.rootSubgroupPoints (t.simpleIndex ht i) K u' * (w' : D.points K)) := by
              group
        _ = D.rootSubgroupPoints (t.simpleIndex ht i) K (ofAdd a) *
              (n * D.torusPoints K s * n⁻¹) *
              (b₁ * (n * (w' : D.points K)) * b₂) := by
              dsimp only [n]; rw [hcell_eq]
        _ = D.rootSubgroupPoints (t.simpleIndex ht i) K (ofAdd a) *
              (n * D.torusPoints K s * n⁻¹) * b₁ * (n * n) * (w : D.points K) * b₂ := by
              simp only [w', nN, Subgroup.coe_mul]
              group

/-- Point-level Tits multiplication law `B nᵢ B · B w B ⊆ B (nᵢ w) B ∪ B w B` in `D.points K`. -/
private theorem mul_doubleCoset_subset_points (i : Fin t.rank) (w : D.weylSubgroup K) :
    DoubleCoset.doubleCoset (D.weylElement (t.simpleIndex ht i) K 1)
          (D.borelSubgroup K) (D.borelSubgroup K) *
        DoubleCoset.doubleCoset (w : D.points K)
          (D.borelSubgroup K) (D.borelSubgroup K) ⊆
      DoubleCoset.doubleCoset (D.weylElement (t.simpleIndex ht i) K 1 * (w : D.points K))
          (D.borelSubgroup K) (D.borelSubgroup K) ∪
        DoubleCoset.doubleCoset (w : D.points K)
          (D.borelSubgroup K) (D.borelSubgroup K) := by
  rintro _ ⟨x, hx, y, hy, rfl⟩
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hx
  obtain ⟨b₃, hb₃, b₄, hb₄, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hy
  let n := D.weylElement (t.simpleIndex ht i) K 1
  obtain ⟨v, hv, s, u, hfac⟩ :=
    (D.mem_borelSubgroup_iff_exists_mul_torusPoints_mul_rootSubgroupPoints K i (b₂ * b₃)).mp
      ((D.borelSubgroup K).mul_mem hb₂ hb₃)
  have hv'_pos : n * v * n⁻¹ ∈ D.positivePoints K :=
    D.iSup_posRoots_diff_singleton_le_positivePoints K i <|
      (Subgroup.mem_normalizer_iff.mp
        (D.weylElement_mem_normalizer_positivePoints_diff_singleton K i 1) v).mp hv
  have ht' : n * D.torusPoints K s * n⁻¹ ∈ D.borelSubgroup K :=
    D.range_torusPoints_le_borelSubgroup K <|
      (Subgroup.mem_normalizer_iff.mp
        (D.weylElement_mem_normalizer_range_torusPoints i K) (D.torusPoints K s)).mp ⟨s, rfl⟩
  have hleft : b₁ * (n * v * n⁻¹) * (n * D.torusPoints K s * n⁻¹) ∈ D.borelSubgroup K :=
    (D.borelSubgroup K).mul_mem
      ((D.borelSubgroup K).mul_mem hb₁ (D.positivePoints_le_borelSubgroup K hv'_pos)) ht'
  have hrew : b₁ * D.weylElement (t.simpleIndex ht i) K 1 * b₂ * (b₃ * (w : D.points K) * b₄) =
      (b₁ * (n * v * n⁻¹) * (n * D.torusPoints K s * n⁻¹)) *
        (D.weylElement (t.simpleIndex ht i) K 1 *
          D.rootSubgroupPoints (t.simpleIndex ht i) K u * (w : D.points K)) * b₄ := by
    calc
      b₁ * D.weylElement (t.simpleIndex ht i) K 1 * b₂ * (b₃ * (w : D.points K) * b₄)
          = b₁ * n * (b₂ * b₃) * (w : D.points K) * b₄ := by dsimp only [n]; group
      _ = b₁ * n * (v * D.torusPoints K s * D.rootSubgroupPoints (t.simpleIndex ht i) K u) *
            (w : D.points K) * b₄ := by rw [hfac]
      _ = _ := by dsimp only [n]; group
  dsimp only
  rw [hrew]
  rcases D.weylElement_mul_rootSubgroup_mul_mem_union_doubleCoset K i w u with h | h
  · left
    obtain ⟨c₁, hc₁, c₂, hc₂, heq⟩ := DoubleCoset.mem_doubleCoset.mp h
    rw [heq]
    exact DoubleCoset.mem_doubleCoset.mpr
      ⟨_, (D.borelSubgroup K).mul_mem hleft hc₁, _, (D.borelSubgroup K).mul_mem hc₂ hb₄, by group⟩
  · right
    obtain ⟨c₁, hc₁, c₂, hc₂, heq⟩ := DoubleCoset.mem_doubleCoset.mp h
    rw [heq]
    exact DoubleCoset.mem_doubleCoset.mpr
      ⟨_, (D.borelSubgroup K).mul_mem hleft hc₁, _, (D.borelSubgroup K).mul_mem hc₂ hb₄, by group⟩

private theorem mem_doubleCoset_borel_subgroupOf_iff
    {g h : D.extendedElementarySubgroup K} :
    g ∈ DoubleCoset.doubleCoset h
        ((D.borelSubgroup K).subgroupOf (D.extendedElementarySubgroup K))
        ((D.borelSubgroup K).subgroupOf (D.extendedElementarySubgroup K)) ↔
      (g : D.points K) ∈ DoubleCoset.doubleCoset (h : D.points K)
        (D.borelSubgroup K) (D.borelSubgroup K) := by
  constructor
  · intro hg
    obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hg
    exact DoubleCoset.mem_doubleCoset.mpr ⟨b₁, hb₁, b₂, hb₂, rfl⟩
  · intro hg
    obtain ⟨b₁, hb₁, b₂, hb₂, heq⟩ := DoubleCoset.mem_doubleCoset.mp hg
    refine DoubleCoset.mem_doubleCoset.mpr
      ⟨⟨b₁, D.borelSubgroup_le_extendedElementarySubgroup K hb₁⟩, hb₁,
        ⟨b₂, D.borelSubgroup_le_extendedElementarySubgroup K hb₂⟩, hb₂, Subtype.ext heq⟩

private theorem normal_borelSubgroup_subgroupOf_weylSubgroup :
    (((D.borelSubgroup K).subgroupOf (D.extendedElementarySubgroup K)).subgroupOf
      ((D.weylSubgroup K).subgroupOf (D.extendedElementarySubgroup K))).Normal := by
  let eN := Subgroup.subgroupOfEquivOfLe (D.weylSubgroup_le_extendedElementarySubgroup K)
  have heq :
      ((D.borelSubgroup K).subgroupOf (D.extendedElementarySubgroup K)).subgroupOf
          ((D.weylSubgroup K).subgroupOf (D.extendedElementarySubgroup K)) =
        (((D.torusPoints K).range).subgroupOf (D.weylSubgroup K)).comap eN.toMonoidHom := by
    ext n
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom]
    have heN : ((eN n : D.weylSubgroup K) : D.points K) = (n : D.points K) := rfl
    rw [heN, ← D.borelSubgroup_inf_weylSubgroup K]
    exact ⟨fun h => ⟨h, n.2⟩, fun h => h.1⟩
  rw [heq]
  exact Subgroup.Normal.comap inferInstance eN.toMonoidHom

/-- The pinned simple Weyl representative `nᵢ(1)` regarded in `N(K) ≤ E(K)`. -/
private noncomputable def simpleWeylInSubgroupN (i : Fin t.rank) :
    ((D.weylSubgroup K).subgroupOf (D.extendedElementarySubgroup K)) :=
  ⟨⟨D.weylElement (t.simpleIndex ht i) K 1,
      D.weylSubgroup_le_extendedElementarySubgroup K (D.weylElement_mem_weylSubgroup K i)⟩,
    D.weylElement_mem_weylSubgroup K i⟩

private theorem closure_simpleWeylInSubgroupN_eq_top :
    let _ := D.normal_borelSubgroup_subgroupOf_weylSubgroup K
    Subgroup.closure (Set.range fun i : Fin t.rank =>
        (QuotientGroup.mk (D.simpleWeylInSubgroupN K i) :
          ((D.weylSubgroup K).subgroupOf (D.extendedElementarySubgroup K)) ⧸
            ((D.borelSubgroup K).subgroupOf (D.extendedElementarySubgroup K)).subgroupOf
              ((D.weylSubgroup K).subgroupOf (D.extendedElementarySubgroup K)))) = ⊤ := by
  let _ := D.normal_borelSubgroup_subgroupOf_weylSubgroup K
  rw [Subgroup.eq_top_iff']
  intro q
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨g, hg, hgn⟩ : ∃ g ∈ D.weylSubgroup K, (n : D.points K) = g :=
    ⟨(n : D.points K), n.2, rfl⟩
  rw [D.weylSubgroup_def K] at hg
  induction hg using Subgroup.closure_induction generalizing n with
  | mem g hg =>
    rcases hg with ⟨s, rfl⟩ | ⟨i, rfl⟩
    · have h1 : (QuotientGroup.mk n : _ ⧸
          ((D.borelSubgroup K).subgroupOf (D.extendedElementarySubgroup K)).subgroupOf
            ((D.weylSubgroup K).subgroupOf (D.extendedElementarySubgroup K))) = 1 :=
        (QuotientGroup.eq_one_iff n).mpr <| by
          rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, hgn]
          exact D.range_torusPoints_le_borelSubgroup K ⟨s, rfl⟩
      rw [h1]
      exact Subgroup.one_mem _
    · have hn_eq : n = D.simpleWeylInSubgroupN K i := Subtype.ext (Subtype.ext hgn)
      rw [hn_eq]
      exact Subgroup.subset_closure ⟨i, rfl⟩
  | one =>
    have hn_eq : n = 1 := Subtype.ext (Subtype.ext hgn)
    rw [hn_eq, QuotientGroup.mk_one]
    exact Subgroup.one_mem _
  | mul g₁ g₂ hg₁ hg₂ ih₁ ih₂ =>
    have hg₁' : g₁ ∈ D.weylSubgroup K := by rw [D.weylSubgroup_def K]; exact hg₁
    have hg₂' : g₂ ∈ D.weylSubgroup K := by rw [D.weylSubgroup_def K]; exact hg₂
    let n₁ : (D.weylSubgroup K).subgroupOf (D.extendedElementarySubgroup K) :=
      ⟨⟨g₁, D.weylSubgroup_le_extendedElementarySubgroup K hg₁'⟩, hg₁'⟩
    let n₂ : (D.weylSubgroup K).subgroupOf (D.extendedElementarySubgroup K) :=
      ⟨⟨g₂, D.weylSubgroup_le_extendedElementarySubgroup K hg₂'⟩, hg₂'⟩
    have hn_eq : n = n₁ * n₂ := Subtype.ext (Subtype.ext hgn)
    rw [hn_eq, QuotientGroup.mk_mul]
    exact Subgroup.mul_mem _ (ih₁ n₁ rfl) (ih₂ n₂ rfl)
  | inv g hg ih =>
    have hg' : g ∈ D.weylSubgroup K := by rw [D.weylSubgroup_def K]; exact hg
    let n₁ : (D.weylSubgroup K).subgroupOf (D.extendedElementarySubgroup K) :=
      ⟨⟨g, D.weylSubgroup_le_extendedElementarySubgroup K hg'⟩, hg'⟩
    have hn_eq : n = n₁⁻¹ := Subtype.ext (Subtype.ext hgn)
    rw [hn_eq, QuotientGroup.mk_inv]
    exact Subgroup.inv_mem _ (ih n₁ rfl)

/-- **The Tits system on the extended elementary subgroup `E(K)`** of any Chevalley datum
over any field `K`, with distinguished subgroups `B(K) = D.borelSubgroup K`,
`N(K) = D.weylSubgroup K`, and simple reflections represented by the pinned Weyl elements
`nᵢ(1)`. -/
noncomputable def titsSystem : TitsSystem (D.extendedElementarySubgroup K) where
  subgroupB := (D.borelSubgroup K).subgroupOf (D.extendedElementarySubgroup K)
  subgroupN := (D.weylSubgroup K).subgroupOf (D.extendedElementarySubgroup K)
  closure_subgroupB_union_subgroupN := by
    rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
    apply Subgroup.map_injective (D.extendedElementarySubgroup K).subtype_injective
    rw [Subgroup.map_sup,
      Subgroup.map_subgroupOf_eq_of_le (D.borelSubgroup_le_extendedElementarySubgroup K),
      Subgroup.map_subgroupOf_eq_of_le (D.weylSubgroup_le_extendedElementarySubgroup K),
      D.borelSubgroup_sup_weylSubgroup K, Subgroup.map_top, Subgroup.range_subtype]
  intersection_normal := D.normal_borelSubgroup_subgroupOf_weylSubgroup K
  simple :=
    letI := D.normal_borelSubgroup_subgroupOf_weylSubgroup K
    Set.range fun i : Fin t.rank => QuotientGroup.mk (D.simpleWeylInSubgroupN K i)
  closure_simple := D.closure_simpleWeylInSubgroupN_eq_top K
  exists_simpleRep_mul_self_mem s hs := by
    let _ := D.normal_borelSubgroup_subgroupOf_weylSubgroup K
    obtain ⟨i, rfl⟩ := hs
    refine ⟨D.simpleWeylInSubgroupN K i, rfl, ?_⟩
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, simpleWeylInSubgroupN]
    rw [D.weylElement_mul_self, D.simpleCorootPoints_eq_torusPoints]
    exact D.range_torusPoints_le_borelSubgroup K ⟨_, rfl⟩
  mul_doubleCoset_subset s hs := by
    let _ := D.normal_borelSubgroup_subgroupOf_weylSubgroup K
    obtain ⟨i, rfl⟩ := hs
    refine ⟨D.simpleWeylInSubgroupN K i, rfl, fun w => ?_⟩
    rintro _ ⟨x, hx, y, hy, rfl⟩
    have hxy := D.mul_doubleCoset_subset_points K i ⟨(w : D.points K), w.2⟩
      ⟨(x : D.points K), (D.mem_doubleCoset_borel_subgroupOf_iff K).mp hx,
        (y : D.points K), (D.mem_doubleCoset_borel_subgroupOf_iff K).mp hy, rfl⟩
    rcases hxy with h | h
    · exact Or.inl ((D.mem_doubleCoset_borel_subgroupOf_iff K).mpr h)
    · exact Or.inr ((D.mem_doubleCoset_borel_subgroupOf_iff K).mpr h)
  exists_conj_not_mem s hs := by
    let _ := D.normal_borelSubgroup_subgroupOf_weylSubgroup K
    obtain ⟨i, rfl⟩ := hs
    obtain ⟨b, hb⟩ := D.exists_weylElement_conj_notMem_borelSubgroup K i
    exact ⟨D.simpleWeylInSubgroupN K i, rfl,
      ⟨⟨b.1, D.borelSubgroup_le_extendedElementarySubgroup K b.2⟩, b.2⟩, hb⟩

/-- The distinguished subgroup `B` of `D.titsSystem K` is `D.borelSubgroup K` inside `E(K)`. -/
@[simp]
theorem titsSystem_subgroupB :
    (D.titsSystem K).subgroupB =
      (D.borelSubgroup K).subgroupOf (D.extendedElementarySubgroup K) :=
  (rfl)

/-- The distinguished subgroup `N` of `D.titsSystem K` is `D.weylSubgroup K` inside `E(K)`. -/
@[simp]
theorem titsSystem_subgroupN :
    (D.titsSystem K).subgroupN =
      (D.weylSubgroup K).subgroupOf (D.extendedElementarySubgroup K) :=
  (rfl)

/-- Membership in the intersection `B ∩ N` of `D.titsSystem K` is membership in the actual
torus `T(K)`. -/
theorem mem_titsSystem_intersection_iff (n : (D.titsSystem K).subgroupN) :
    n ∈ (D.titsSystem K).intersection ↔ (n : D.points K) ∈ (D.torusPoints K).range := by
  rw [TitsSystem.intersection, Subgroup.mem_subgroupOf, titsSystem_subgroupB,
    Subgroup.mem_subgroupOf, ← D.borelSubgroup_inf_weylSubgroup K]
  exact ⟨fun h => ⟨h, (D.titsSystem_subgroupN K).le n.2⟩, fun h => h.1⟩

/-- The simple reflections of `D.titsSystem K` are the classes of the pinned simple Weyl
representatives `nᵢ(1)`. -/
theorem mem_titsSystem_simple_iff (s : (D.titsSystem K).WeylGroup) :
    s ∈ (D.titsSystem K).simple ↔
      ∃ i : Fin t.rank,
        (QuotientGroup.mk
          (⟨⟨D.weylElement (t.simpleIndex ht i) K 1,
              D.weylSubgroup_le_extendedElementarySubgroup K (D.weylElement_mem_weylSubgroup K i)⟩,
            (D.titsSystem_subgroupN K).ge
              (D.weylElement_mem_weylSubgroup K i)⟩ : (D.titsSystem K).subgroupN) :
          (D.titsSystem K).WeylGroup) = s :=
  Iff.rfl

/-- Inside `E(K)`, the Borel-type subgroup is self-normalizing over every field `K`. -/
@[simp]
theorem normalizer_borelSubgroup_inf_extendedElementarySubgroup :
    Subgroup.normalizer (D.borelSubgroup K : Set (D.points K)) ⊓
        D.extendedElementarySubgroup K = D.borelSubgroup K := by
  apply le_antisymm
  · rintro g ⟨hgNorm, hgE⟩
    let gE : D.extendedElementarySubgroup K := ⟨g, hgE⟩
    have hg' : gE ∈ Subgroup.normalizer ((D.titsSystem K).subgroupB :
        Set (D.extendedElementarySubgroup K)) := by
      rw [Subgroup.mem_normalizer_iff]
      intro b
      simpa only [titsSystem_subgroupB, Subgroup.mem_subgroupOf,
        Subgroup.coe_mul, Subgroup.coe_inv] using
        Subgroup.mem_normalizer_iff.mp hgNorm (b : D.points K)
    rw [(D.titsSystem K).normalizer_subgroupB] at hg'
    exact hg'
  · exact le_inf (D.borelSubgroup K).le_normalizer (D.borelSubgroup_le_extendedElementarySubgroup K)

/-! ## The Weyl quotient isomorphism `N(K) / T(K) ≃* W` -/

/-- Over every field `K`, the kernel of the Weyl projection is the actual character-lattice
torus `T(K)`. -/
@[simp]
theorem ker_weylProjection :
    (D.weylProjection K).ker = ((D.torusPoints K).range).subgroupOf (D.weylSubgroup K) := by
  apply le_antisymm
  · intro n hn
    have hproj : D.weylProjection K n = 1 := hn
    have hmapU : (D.positivePoints K).map (MulAut.conj (n : D.points K)).toMonoidHom =
        D.positivePoints K := by
      rw [D.positivePoints_eq_iSup K, D.map_iSup_rootSubgroupPoints_conj K n, hproj, map_one,
        Equiv.Perm.coe_one, Set.image_id]
    have hmapT : ((D.torusPoints K).range).map (MulAut.conj (n : D.points K)).toMonoidHom =
        (D.torusPoints K).range := by
      ext x
      rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
      have hinv := (D.weylSubgroup K).inv_mem n.2
      simpa only [inv_inv] using (Subgroup.mem_normalizer_iff.mp
        (D.weylSubgroup_le_normalizer_range_torusPoints K hinv) x).symm
    have hmapB : (D.borelSubgroup K).map (MulAut.conj (n : D.points K)).toMonoidHom =
        D.borelSubgroup K := by
      rw [D.borelSubgroup_def K, Subgroup.map_sup, hmapU, hmapT]
    have hn_norm :
        (n : D.points K) ∈ Subgroup.normalizer (D.borelSubgroup K : Set (D.points K)) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      have hx := Subgroup.mem_map_iff_mem (f := (MulAut.conj (n : D.points K)).toMonoidHom)
        (MulAut.conj (n : D.points K)).injective (K := D.borelSubgroup K) (x := x)
      rw [hmapB] at hx
      exact hx.symm
    have hnB : (n : D.points K) ∈ D.borelSubgroup K := by
      rw [← D.normalizer_borelSubgroup_inf_extendedElementarySubgroup K]
      exact ⟨hn_norm, D.weylSubgroup_le_extendedElementarySubgroup K n.2⟩
    rw [Subgroup.mem_subgroupOf, ← D.borelSubgroup_inf_weylSubgroup K]
    exact ⟨hnB, n.2⟩
  · rintro n ⟨s, hs⟩
    rw [MonoidHom.mem_ker]
    have hn : n = ⟨D.torusPoints K s, D.torusPoints_mem_weylSubgroup K s⟩ := Subtype.ext hs.symm
    rw [hn, D.weylProjection_torusPoints]

/-- **The Weyl quotient isomorphism `N(K) / T(K) ≃* W`**, induced by `D.weylProjection K`
over every field `K`. -/
noncomputable def weylSubgroupQuotientEquivWeylGroup :
    D.weylSubgroup K ⧸ ((D.torusPoints K).range).subgroupOf (D.weylSubgroup K) ≃*
      (t.simplyConnectedRootDatum ht).weylGroup :=
  (QuotientGroup.quotientMulEquivOfEq (D.ker_weylProjection K).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (D.weylProjection K)
      (D.weylProjection_surjective K))

/-- On cosets, `weylSubgroupQuotientEquivWeylGroup` evaluates via `D.weylProjection K`. -/
@[simp]
theorem weylSubgroupQuotientEquivWeylGroup_mk (n : D.weylSubgroup K) :
    D.weylSubgroupQuotientEquivWeylGroup K (QuotientGroup.mk n) = D.weylProjection K n := by
  simp only [weylSubgroupQuotientEquivWeylGroup, MulEquiv.trans_apply,
    QuotientGroup.quotientMulEquivOfEq_mk,
    TauCeti.QuotientGroup.quotientKerEquivOfSurjective_apply_mk]

/-- Canonical identification of `(D.titsSystem K).subgroupN` with `D.weylSubgroup K`. -/
private noncomputable def titsSystemSubgroupNEquiv :
    (D.titsSystem K).subgroupN ≃* D.weylSubgroup K :=
  (MulEquiv.subgroupCongr (D.titsSystem_subgroupN K)).trans
    (Subgroup.subgroupOfEquivOfLe (D.weylSubgroup_le_extendedElementarySubgroup K))

private theorem titsSystemSubgroupNEquiv_apply (n : (D.titsSystem K).subgroupN) :
    D.titsSystemSubgroupNEquiv K n =
      ⟨(n : D.points K), (D.titsSystem_subgroupN K).le n.2⟩ :=
  rfl

/-- The Weyl projection read on the `subgroupN` carrier of `D.titsSystem K`. -/
private noncomputable def titsSystemWeylProjection :
    (D.titsSystem K).subgroupN →* (t.simplyConnectedRootDatum ht).weylGroup :=
  (D.weylProjection K).comp (D.titsSystemSubgroupNEquiv K).toMonoidHom

private theorem ker_titsSystemWeylProjection :
    (D.titsSystemWeylProjection K).ker = (D.titsSystem K).intersection := by
  ext n
  rw [MonoidHom.mem_ker, titsSystemWeylProjection, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, D.titsSystemSubgroupNEquiv_apply K, ← MonoidHom.mem_ker,
    D.ker_weylProjection K, Subgroup.mem_subgroupOf, D.mem_titsSystem_intersection_iff K]

private theorem titsSystemWeylProjection_surjective :
    Function.Surjective (D.titsSystemWeylProjection K) :=
  (D.weylProjection_surjective K).comp (D.titsSystemSubgroupNEquiv K).surjective

/-- Identification of the Weyl quotient of `D.titsSystem K` with the Weyl group of
`DynkinType.simplyConnectedRootDatum`, over every field `K`. -/
noncomputable def titsSystemWeylGroupEquiv :
    (D.titsSystem K).WeylGroup ≃* (t.simplyConnectedRootDatum ht).weylGroup :=
  (QuotientGroup.quotientMulEquivOfEq (D.ker_titsSystemWeylProjection K).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (D.titsSystemWeylProjection K)
      (D.titsSystemWeylProjection_surjective K))

/-- On cosets of `(D.titsSystem K).subgroupN`, `titsSystemWeylGroupEquiv` evaluates via
`D.weylProjection K`. -/
@[simp]
theorem titsSystemWeylGroupEquiv_mk (n : (D.titsSystem K).subgroupN) :
    D.titsSystemWeylGroupEquiv K (QuotientGroup.mk n) =
      D.weylProjection K ⟨(n : D.points K), (D.titsSystem_subgroupN K).le n.2⟩ := by
  rw [titsSystemWeylGroupEquiv, MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk,
    TauCeti.QuotientGroup.quotientKerEquivOfSurjective_apply_mk, titsSystemWeylProjection,
    MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, titsSystemSubgroupNEquiv_apply]

/-- `titsSystemWeylGroupEquiv` matches the simple reflections of `D.titsSystem K` with the
Bourbaki-numbered simple reflections of the root datum's Weyl group. -/
theorem image_titsSystemWeylGroupEquiv_simple :
    D.titsSystemWeylGroupEquiv K '' (D.titsSystem K).simple =
      Set.range fun i : Fin t.rank =>
        RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht) (t.simpleIndex ht i) := by
  ext w
  constructor
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨i, rfl⟩ := (D.mem_titsSystem_simple_iff K s).mp hs
    exact ⟨i, by rw [D.titsSystemWeylGroupEquiv_mk, D.weylProjection_weylElement]⟩
  · rintro ⟨i, rfl⟩
    refine ⟨QuotientGroup.mk
        ⟨⟨D.weylElement (t.simpleIndex ht i) K 1,
            D.weylSubgroup_le_extendedElementarySubgroup K (D.weylElement_mem_weylSubgroup K i)⟩,
          (D.titsSystem_subgroupN K).ge (D.weylElement_mem_weylSubgroup K i)⟩,
      (D.mem_titsSystem_simple_iff K _).mpr ⟨i, rfl⟩, ?_⟩
    rw [D.titsSystemWeylGroupEquiv_mk]
    exact D.weylProjection_weylElement K i

/-! ## Bruhat decomposition of `E(K)` indexed by `W` -/

/-- The Bruhat cell `B(K) n_w B(K)` in `D.points K`, indexed directly by an element `w` of
the root datum's Weyl group. -/
noncomputable def bruhatCell (w : (t.simplyConnectedRootDatum ht).weylGroup) :
    Set (D.points K) :=
  Subtype.val '' (D.titsSystem K).bruhatCell ((D.titsSystemWeylGroupEquiv K).symm w)

/-- The Bruhat cell at the projection of a Weyl lift `n ∈ N(K)` is the double coset
`B(K) n B(K)`. -/
theorem bruhatCell_weylProjection (n : D.weylSubgroup K) :
    D.bruhatCell K (D.weylProjection K n) =
      DoubleCoset.doubleCoset (n : D.points K) (D.borelSubgroup K) (D.borelSubgroup K) := by
  let nN : (D.titsSystem K).subgroupN :=
    ⟨⟨n.1, D.weylSubgroup_le_extendedElementarySubgroup K n.2⟩,
      (D.titsSystem_subgroupN K).ge n.2⟩
  have hsymm : (D.titsSystemWeylGroupEquiv K).symm (D.weylProjection K n) =
      QuotientGroup.mk nN := by
    apply (D.titsSystemWeylGroupEquiv K).injective
    rw [MulEquiv.apply_symm_apply, D.titsSystemWeylGroupEquiv_mk]
  ext g
  constructor
  · rintro ⟨gE, hgE, rfl⟩
    rw [hsymm, (D.titsSystem K).bruhatCell_mk, D.titsSystem_subgroupB K] at hgE
    exact (D.mem_doubleCoset_borel_subgroupOf_iff K).mp hgE
  · intro hg
    obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hg
    have hgE : b₁ * (n : D.points K) * b₂ ∈ D.extendedElementarySubgroup K :=
      (D.extendedElementarySubgroup K).mul_mem
        ((D.extendedElementarySubgroup K).mul_mem
          (D.borelSubgroup_le_extendedElementarySubgroup K hb₁)
          (D.weylSubgroup_le_extendedElementarySubgroup K n.2))
        (D.borelSubgroup_le_extendedElementarySubgroup K hb₂)
    refine ⟨⟨_, hgE⟩, ?_, rfl⟩
    rw [hsymm, (D.titsSystem K).bruhatCell_mk, D.titsSystem_subgroupB K,
      D.mem_doubleCoset_borel_subgroupOf_iff K]
    exact DoubleCoset.mem_doubleCoset.mpr ⟨b₁, hb₁, b₂, hb₂, rfl⟩

/-- The Bruhat cell at the identity of the Weyl group is `B(K)`. -/
@[simp]
theorem bruhatCell_one :
    D.bruhatCell K 1 = (D.borelSubgroup K : Set (D.points K)) := by
  have h := D.bruhatCell_weylProjection K 1
  rw [map_one, Subgroup.coe_one, doubleCoset_one_self] at h
  exact h

/-- Every Weyl-indexed Bruhat cell is nonempty. -/
theorem bruhatCell_nonempty (w : (t.simplyConnectedRootDatum ht).weylGroup) :
    (D.bruhatCell K w).Nonempty := by
  obtain ⟨n, rfl⟩ := D.weylProjection_surjective K w
  rw [D.bruhatCell_weylProjection K n]
  exact ⟨n, DoubleCoset.mem_doubleCoset_self _ _ _⟩

/-- Membership in `D.bruhatCell K w` is membership in `B(K) n B(K)` for some (equivalently
any) lift `n ∈ N(K)` of `w`. -/
theorem mem_bruhatCell_iff {g : D.points K}
    {w : (t.simplyConnectedRootDatum ht).weylGroup} :
    g ∈ D.bruhatCell K w ↔
      ∃ n : D.weylSubgroup K, D.weylProjection K n = w ∧
        g ∈ DoubleCoset.doubleCoset (n : D.points K) (D.borelSubgroup K) (D.borelSubgroup K) := by
  obtain ⟨n, rfl⟩ := D.weylProjection_surjective K w
  constructor
  · intro hg
    exact ⟨n, rfl, (D.bruhatCell_weylProjection K n ▸ hg)⟩
  · rintro ⟨m, hm, hg⟩
    rwa [← hm, D.bruhatCell_weylProjection K m]

/-- Every Bruhat cell lies in the extended elementary subgroup `E(K)`. -/
theorem bruhatCell_subset_extendedElementarySubgroup
    (w : (t.simplyConnectedRootDatum ht).weylGroup) :
    D.bruhatCell K w ⊆ (D.extendedElementarySubgroup K : Set (D.points K)) := by
  rintro _ ⟨gE, _, rfl⟩
  exact gE.2

/-- The Bruhat cells cover exactly the extended elementary subgroup `E(K)`. -/
@[simp]
theorem iUnion_bruhatCell :
    (⋃ w : (t.simplyConnectedRootDatum ht).weylGroup, D.bruhatCell K w) =
      (D.extendedElementarySubgroup K : Set (D.points K)) := by
  ext g
  simp only [Set.mem_iUnion, SetLike.mem_coe]
  constructor
  · rintro ⟨w, hg⟩
    exact D.bruhatCell_subset_extendedElementarySubgroup K w hg
  · intro hg
    obtain ⟨q, hq, _⟩ := (D.titsSystem K).existsUnique_mem_bruhatCell ⟨g, hg⟩
    refine ⟨D.titsSystemWeylGroupEquiv K q, ⟨g, hg⟩, ?_, rfl⟩
    simpa only [MulEquiv.symm_apply_apply] using hq

/-- Distinct Weyl elements index distinct Bruhat cells in `D.points K`. -/
theorem bruhatCell_injective : Function.Injective (D.bruhatCell K) := by
  intro w v h
  apply (D.titsSystemWeylGroupEquiv K).symm.injective
  apply (D.titsSystem K).bruhatCell_injective
  exact Set.image_injective.mpr Subtype.val_injective h

/-- Equality of Bruhat cells in `D.points K` is equality of their Weyl indices. -/
@[simp]
theorem bruhatCell_inj {w v : (t.simplyConnectedRootDatum ht).weylGroup} :
    D.bruhatCell K w = D.bruhatCell K v ↔ w = v :=
  (D.bruhatCell_injective K).eq_iff

/-- Two Bruhat cells in `D.points K` are disjoint exactly when their Weyl indices differ. -/
@[simp]
theorem disjoint_bruhatCell_iff {w v : (t.simplyConnectedRootDatum ht).weylGroup} :
    Disjoint (D.bruhatCell K w) (D.bruhatCell K v) ↔ w ≠ v := by
  rw [bruhatCell, bruhatCell, Set.disjoint_image_iff Subtype.val_injective,
    (D.titsSystem K).disjoint_bruhatCell_iff,
    (D.titsSystemWeylGroupEquiv K).symm.injective.ne_iff]

/-- **Bruhat decomposition of `E(K)`:** over every field `K`, every element of the extended
elementary subgroup belongs to a unique Weyl-indexed Bruhat cell `B(K) n_w B(K)`. -/
theorem existsUnique_mem_bruhatCell {g : D.points K}
    (hg : g ∈ D.extendedElementarySubgroup K) :
    ∃! w : (t.simplyConnectedRootDatum ht).weylGroup, g ∈ D.bruhatCell K w := by
  obtain ⟨q, hq, huniq⟩ := (D.titsSystem K).existsUnique_mem_bruhatCell ⟨g, hg⟩
  refine ⟨D.titsSystemWeylGroupEquiv K q,
    ⟨⟨g, hg⟩, by simpa only [MulEquiv.symm_apply_apply] using hq, rfl⟩, ?_⟩
  rintro w ⟨gE, hgE, hgE_val⟩
  have hgE_eq : gE = ⟨g, hg⟩ := Subtype.ext hgE_val
  subst gE
  exact (D.titsSystemWeylGroupEquiv K).symm.injective
    ((huniq _ hgE).trans (MulEquiv.symm_apply_apply _ _).symm)

end TauCeti.DynkinType.ChevalleyDatum
