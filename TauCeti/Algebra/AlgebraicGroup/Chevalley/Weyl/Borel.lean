/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Borel
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Elementary
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Torus.Weyl
import TauCeti.Algebra.AlgebraicGroup.Chevalley.BigCell.Triangular
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Positive.Blocks
import TauCeti.Algebra.AlgebraicGroup.Chevalley.RankOne
import TauCeti.LinearAlgebra.Matrix.Diagonal

/-!
# Word factorization of the Weyl subgroup and its intersection with the Borel subgroup

For a Chevalley datum `D` over any commutative ring `A`, the pinned simple Weyl representatives
satisfy `nᵢ(1)² = αᵢ∨(-1) ∈ T_D(A)` and normalize the actual torus `T_D(A)`. Consequently every
element of `D.weylSubgroup A` decomposes as a positive word in the pinned simple Weyl
representatives followed by an actual torus point. Moreover, the join of `D.borelSubgroup A` and
`D.weylSubgroup A` is the extended elementary subgroup `D.extendedElementarySubgroup A`.

Over any field `K`, combining this word decomposition with weight-space block unitriangularity of
`D.positivePoints K` and the Weyl-word block `LDU` criterion shows that `D.positivePoints K`
intersects `D.weylSubgroup K` trivially: the block `LDU` test forces the Weyl projection to be `1`,
so off-block matrix entries vanish by torus character separation over `AlgebraicClosure K` while
diagonal weight blocks equal the identity by block unitriangularity. Decomposing elements of
`D.borelSubgroup K` as positive times torus factors then yields the exact intersection
`D.borelSubgroup K ⊓ D.weylSubgroup K = (D.torusPoints K).range`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemmas 22 and 27, and Chapter 5,
  Theorem 7.
* R. W. Carter, *Simple Groups of Lie Type*, §§7.2 and 8.2.
-/

public section

open Multiplicative
open TauCeti.UniversalEnvelopingAlgebra

namespace TauCeti.DynkinType.ChevalleyDatum

universe v

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

section CommRing

variable (A : Type v) [CommRing A]

/-- Every product of pinned simple Weyl representatives belongs to `D.weylSubgroup A`. -/
theorem list_prod_map_weylElement_mem_weylSubgroup (l : List (Fin t.rank)) :
    (l.map fun i => D.weylElement (t.simpleIndex ht i) A 1).prod ∈ D.weylSubgroup A := by
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
  exact D.weylElement_mem_weylSubgroup A i

/-- Every element of `D.weylSubgroup A` is a positive word in the pinned simple Weyl
representatives followed by a point of the actual torus, over every commutative ring. -/
theorem mem_weylSubgroup_iff_exists_list_prod_mul_torusPoints {g : D.points A} :
    g ∈ D.weylSubgroup A ↔
      ∃ (l : List (Fin t.rank)) (s : Fin t.rank → Aˣ),
        (l.map fun i => D.weylElement (t.simpleIndex ht i) A 1).prod *
          D.torusPoints A s = g := by
  let r : Fin t.rank → D.points A := fun i => D.weylElement (t.simpleIndex ht i) A 1
  have htorus_mul (s₀ : Fin t.rank → Aˣ) (l : List (Fin t.rank)) (s : Fin t.rank → Aˣ) :
      ∃ s' : Fin t.rank → Aˣ,
        D.torusPoints A s₀ * ((l.map r).prod * D.torusPoints A s) =
          (l.map r).prod * D.torusPoints A s' := by
    have hnorm := D.weylSubgroup_le_normalizer_range_torusPoints A
      (inv_mem (D.list_prod_map_weylElement_mem_weylSubgroup A l))
    obtain ⟨s₁, hs₁⟩ := (Subgroup.mem_normalizer_iff.mp hnorm (D.torusPoints A s₀)).mp
      ⟨s₀, rfl⟩
    refine ⟨s₁ * s, ?_⟩
    have hcomm : D.torusPoints A s₀ * (l.map r).prod = (l.map r).prod * D.torusPoints A s₁ := by
      rw [hs₁]
      dsimp only [r]
      group
    rw [← mul_assoc, hcomm, mul_assoc, (D.torusPoints A).map_mul]
  constructor
  · intro hg
    rw [D.weylSubgroup_def] at hg
    induction hg using Subgroup.closure_induction_left with
    | one =>
      exact ⟨[], 1, by simp⟩
    | mul_left x hx y _ ih =>
      obtain ⟨l, s, rfl⟩ := ih
      rcases hx with ⟨s₀, rfl⟩ | ⟨i, rfl⟩
      · obtain ⟨s', hs'⟩ := htorus_mul s₀ l s
        exact ⟨l, s', hs'.symm⟩
      · exact ⟨i :: l, s, by simp [mul_assoc]⟩
    | inv_mul_cancel x hx y _ ih =>
      obtain ⟨l, s, rfl⟩ := ih
      rcases hx with ⟨s₀, rfl⟩ | ⟨i, rfl⟩
      · rw [← map_inv]
        obtain ⟨s', hs'⟩ := htorus_mul s₀⁻¹ l s
        exact ⟨l, s', hs'.symm⟩
      · have hri_inv : (r i)⁻¹ =
            r i * D.torusPoints A (D.simpleCorootParameter i A (-1))⁻¹ := by
          apply inv_eq_of_mul_eq_one_right
          rw [← mul_assoc, D.weylElement_mul_self i A, D.simpleCorootPoints_eq_torusPoints,
            ← (D.torusPoints A).map_mul, mul_inv_cancel, map_one]
        rw [hri_inv, mul_assoc]
        obtain ⟨s', hs'⟩ := htorus_mul (D.simpleCorootParameter i A (-1))⁻¹ l s
        refine ⟨i :: l, s', ?_⟩
        dsimp only [r] at hs' ⊢
        simp only [List.map_cons, List.prod_cons, mul_assoc]
        rw [← hs']
  · rintro ⟨l, s, rfl⟩
    exact mul_mem (D.list_prod_map_weylElement_mem_weylSubgroup A l)
      (D.torusPoints_mem_weylSubgroup A s)

/-- The Borel-type subgroup is contained in the extended elementary subgroup over every
commutative ring. -/
theorem borelSubgroup_le_extendedElementarySubgroup :
    D.borelSubgroup A ≤ D.extendedElementarySubgroup A := by
  rw [D.borelSubgroup_le_iff]
  refine ⟨fun γ _ u => D.elementarySubgroup_le_extendedElementarySubgroup A
    (D.rootSubgroupPoints_mem_elementarySubgroup A γ u),
    D.torusPoints_mem_extendedElementarySubgroup A⟩

/-- The Weyl subgroup is contained in the extended elementary subgroup over every commutative
ring. -/
theorem weylSubgroup_le_extendedElementarySubgroup :
    D.weylSubgroup A ≤ D.extendedElementarySubgroup A := by
  rw [D.weylSubgroup_def, Subgroup.closure_le]
  rintro g (⟨s, rfl⟩ | ⟨i, rfl⟩)
  · exact D.torusPoints_mem_extendedElementarySubgroup A s
  · dsimp only
    apply D.elementarySubgroup_le_extendedElementarySubgroup A
    rw [D.weylElement_def]
    exact mul_mem (mul_mem (D.rootSubgroupPoints_mem_elementarySubgroup A _ _)
      (D.rootSubgroupPoints_mem_elementarySubgroup A _ _))
      (D.rootSubgroupPoints_mem_elementarySubgroup A _ _)

/-- The Borel-type subgroup and the Weyl subgroup together generate the extended elementary
subgroup over every commutative ring. -/
@[simp]
theorem borelSubgroup_sup_weylSubgroup_eq_extendedElementarySubgroup :
    D.borelSubgroup A ⊔ D.weylSubgroup A = D.extendedElementarySubgroup A := by
  apply le_antisymm
  · exact sup_le (D.borelSubgroup_le_extendedElementarySubgroup A)
      (D.weylSubgroup_le_extendedElementarySubgroup A)
  · rw [D.extendedElementarySubgroup_def]
    refine sup_le ?_ ((D.range_torusPoints_le_borelSubgroup A).trans le_sup_left)
    rw [D.elementarySubgroup_eq_closure_simpleRootPair, Subgroup.closure_le]
    rintro g hg
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hg
    rcases hi with ⟨u, rfl⟩ | ⟨u, rfl⟩
    · exact Subgroup.mem_sup_left (D.positivePoints_le_borelSubgroup A
        (D.rootSubgroupPoints_mem_positivePoints A (simpleIndex_mem_posRoots i) u))
    · let ε : ℤˣ := t.chevalleyWeylSign ht (t.simpleIndex ht i) (t.simpleIndex ht i)
      have hε : ((ε : ℤ) : A) * ((ε : ℤ) : A) = 1 := by
        rcases Int.units_eq_one_or ε with h | h <;> simp [h]
      have hconj := D.weylElement_conj_rootSubgroupPoints i (t.simpleIndex ht i) A
        (((ε : ℤ) : A) * toAdd u)
      have hu : D.rootSubgroupPoints ((t.simplyConnectedRootDatum ht).reflectionPerm
          (t.simpleIndex ht i) (t.simpleIndex ht i)) A u =
          D.weylElement (t.simpleIndex ht i) A 1 *
            D.rootSubgroupPoints (t.simpleIndex ht i) A
              (ofAdd (((ε : ℤ) : A) * toAdd u)) *
            (D.weylElement (t.simpleIndex ht i) A 1)⁻¹ := by
        rw [hconj, ← mul_assoc, hε, one_mul, ofAdd_toAdd]
      rw [hu]
      exact mul_mem
        (mul_mem (Subgroup.mem_sup_right (D.weylElement_mem_weylSubgroup A i))
          (Subgroup.mem_sup_left (D.positivePoints_le_borelSubgroup A
            (D.rootSubgroupPoints_mem_positivePoints A (simpleIndex_mem_posRoots i) _))))
        (inv_mem (Subgroup.mem_sup_right (D.weylElement_mem_weylSubgroup A i)))

end CommRing

section Field

variable (K : Type v) [Field K]

/-- On a product of a Weyl word and an actual torus point, `D.weylProjection K` evaluates to the
Weyl-group element spelled by the word. -/
theorem weylProjection_list_prod_mul_torusPoints (l : List (Fin t.rank))
    (s : Fin t.rank → Kˣ) :
    D.weylProjection K
      ⟨(l.map fun i => D.weylElement (t.simpleIndex ht i) K 1).prod * D.torusPoints K s,
        mul_mem (D.list_prod_map_weylElement_mem_weylSubgroup K l)
          (D.torusPoints_mem_weylSubgroup K s)⟩ =
      t.geckWeylWordProd ht l := by
  have hword (m : List (Fin t.rank)) :
      D.weylProjection K ⟨(m.map fun i => D.weylElement (t.simpleIndex ht i) K 1).prod,
        D.list_prod_map_weylElement_mem_weylSubgroup K m⟩ =
        t.geckWeylWordProd ht m := by
    induction m with
    | nil =>
      have hone :
          (⟨([].map fun i => D.weylElement (t.simpleIndex ht i) K 1).prod,
            D.list_prod_map_weylElement_mem_weylSubgroup K []⟩ : D.weylSubgroup K) = 1 := by
        ext
        simp only [List.map_nil, List.prod_nil, Subgroup.coe_one]
      rw [hone, map_one, geckWeylWordProd_nil]
    | cons i m ih =>
      have hsplit : (⟨((i :: m).map fun j => D.weylElement (t.simpleIndex ht j) K 1).prod,
          D.list_prod_map_weylElement_mem_weylSubgroup K (i :: m)⟩ : D.weylSubgroup K) =
          ⟨D.weylElement (t.simpleIndex ht i) K 1, D.weylElement_mem_weylSubgroup K i⟩ *
            ⟨(m.map fun j => D.weylElement (t.simpleIndex ht j) K 1).prod,
              D.list_prod_map_weylElement_mem_weylSubgroup K m⟩ := by
        ext
        simp only [List.map_cons, List.prod_cons, Subgroup.coe_mul]
      rw [hsplit, map_mul, D.weylProjection_weylElement K i, ih, geckWeylWordProd_cons]
  have hmul : (⟨(l.map fun i => D.weylElement (t.simpleIndex ht i) K 1).prod *
      D.torusPoints K s,
      mul_mem (D.list_prod_map_weylElement_mem_weylSubgroup K l)
        (D.torusPoints_mem_weylSubgroup K s)⟩ : D.weylSubgroup K) =
      ⟨(l.map fun i => D.weylElement (t.simpleIndex ht i) K 1).prod,
        D.list_prod_map_weylElement_mem_weylSubgroup K l⟩ *
        ⟨D.torusPoints K s, D.torusPoints_mem_weylSubgroup K s⟩ := rfl
  rw [hmul, map_mul, hword l, D.weylProjection_torusPoints K s, mul_one]

private theorem eq_one_of_mem_positivePoints_of_weylProjection_eq_one
    {u : D.points K} (huP : u ∈ D.positivePoints K) (huW : u ∈ D.weylSubgroup K)
    (hproj : D.weylProjection K ⟨u, huW⟩ = 1) : u = 1 := by
  -- Block unitriangularity handles equal-weight blocks; torus-character separation over the
  -- algebraic closure forces distinct-weight entries to vanish.
  have hbu := D.blockUnitriangular_orderedWeightBlock_of_mem_positivePoints huP
  apply Subtype.ext
  apply Units.ext
  ext i j
  by_cases hwt : D.weight i = D.weight j
  · exact hbu.apply_of_eq
      ((orderedWeightBlock_eq_iff (t.weightDegree ht) D.weight).mpr hwt)
  · have hij : i ≠ j := fun h => hwt (congrArg D.weight h)
    rw [Subgroup.coe_one, Units.val_one, Matrix.one_apply_ne hij]
    apply (algebraMap K (AlgebraicClosure K)).injective
    rw [map_zero]
    have hne_char :
        weightChar (AlgebraicClosure K) (D.weight i) ≠
          weightChar (AlgebraicClosure K) (D.weight j) :=
      fun h => hwt (weightChar_injective h)
    have hexists : ∃ s'' : Fin t.rank → (AlgebraicClosure K)ˣ,
        torusCharacter s'' (D.weight i) ≠ torusCharacter s'' (D.weight j) := by
      by_contra hforall
      push Not at hforall
      exact hne_char (MonoidHom.ext fun s'' => by simpa only [weightChar_apply] using hforall s'')
    obtain ⟨s'', hs''⟩ := hexists
    have hconj := (D.weylProjection_eq_iff K ⟨u, huW⟩ 1).mp hproj s''
    rw [map_one, MulAut.one_apply, mul_inv_eq_iff_eq_mul] at hconj
    have hcomm : Commute
        (Matrix.diagonal fun k => (torusCharacter s'' (D.weight k) : AlgebraicClosure K))
        ((Matrix.GeneralLinearGroup.map (algebraMap K (AlgebraicClosure K))
          ((u : D.points K) : Matrix.GeneralLinearGroup (Fin D.dim) K) :
          Matrix.GeneralLinearGroup (Fin D.dim) (AlgebraicClosure K)) :
          Matrix (Fin D.dim) (Fin D.dim) (AlgebraicClosure K)) := by
      rw [Commute, SemiconjBy]
      have hmat := congrArg Units.val hconj.symm
      simpa only [Units.val_mul, diagGL_coe] using hmat
    simpa only [Matrix.GeneralLinearGroup.map_apply] using
      apply_eq_zero_of_commute_diagonal hcomm (fun h => hs'' (Units.ext h))

/-- Over a field, the positive point subgroup intersects the Weyl subgroup trivially. -/
@[simp]
theorem positivePoints_inf_weylSubgroup_eq_bot :
    D.positivePoints K ⊓ D.weylSubgroup K = ⊥ := by
  refine eq_bot_iff.mpr ?_
  intro u hu
  rw [Subgroup.mem_inf] at hu
  obtain ⟨huP, huW⟩ := hu
  rw [Subgroup.mem_bot]
  obtain ⟨l, s, hls⟩ := (D.mem_weylSubgroup_iff_exists_list_prod_mul_torusPoints K).mp huW
  let wprod : D.points K := (l.map fun i => D.weylElement (t.simpleIndex ht i) K 1).prod
  -- Conjugate the positive factor across the torus point so the Weyl word has block LDU form.
  let u' : D.points K := D.torusPoints K s * u * (D.torusPoints K s)⁻¹
  have hu'P : u' ∈ D.positivePoints K :=
    (Subgroup.mem_normalizer_iff.mp
      (D.range_torusPoints_le_normalizer_positivePoints K ⟨s, rfl⟩) u).mp huP
  have hwprod' : wprod = D.torusPoints K s⁻¹ * u' := by
    have hwprod : wprod = u * (D.torusPoints K s)⁻¹ := eq_mul_inv_of_mul_eq hls
    rw [hwprod, (D.torusPoints K).map_inv]
    dsimp only [u']
    group
  have hword_one : t.geckWeylWordProd ht l = 1 := by
    rw [← D.exists_blockLDU_weylWord_iff l K D.weightBlockEquiv]
    have hfun : (fun j => D.weightBlockEquiv ⟨D.weight j, Set.mem_range_self j⟩) =
        orderedWeightBlock (t.weightDegree ht) D.weight :=
      funext D.weightBlockEquiv_weight
    let Nmat : Matrix (Fin D.dim) (Fin D.dim) K :=
      ((D.torusPoints K s⁻¹ : Matrix.GeneralLinearGroup (Fin D.dim) K) :
        Matrix (Fin D.dim) (Fin D.dim) K)
    let Umat : Matrix (Fin D.dim) (Fin D.dim) K :=
      ((u' : Matrix.GeneralLinearGroup (Fin D.dim) K) :
        Matrix (Fin D.dim) (Fin D.dim) K)
    have hNdiag : Nmat =
        Matrix.diagonal (fun j => (torusCharacter s⁻¹ (D.coordinateWeight j) : K)) := by
      simp only [Nmat, D.coe_torusPoints, kostantTorusMatrix_apply, diagGL_coe]
    refine ⟨1, Nmat, Umat, Matrix.blockUnitriangular_one, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hNdiag]
      exact Matrix.blockTriangular_diagonal _
    · rw [hNdiag]
      exact Matrix.blockTriangular_diagonal _
    · rw [hfun]
      exact D.blockUnitriangular_orderedWeightBlock_of_mem_positivePoints hu'P
    · exact (Matrix.isUnit_iff_isUnit_det Nmat).mp
        (D.torusPoints K s⁻¹ : Matrix.GeneralLinearGroup (Fin D.dim) K).isUnit
    · rw [one_mul]
      simpa only [wprod, Nmat, Umat, Subgroup.coe_mul, Units.val_mul] using
        congrArg (fun x : D.points K =>
          ((x : Matrix.GeneralLinearGroup (Fin D.dim) K) :
            Matrix (Fin D.dim) (Fin D.dim) K)) hwprod'
  have hproj : D.weylProjection K ⟨u, huW⟩ = 1 := by
    have hsub : (⟨u, huW⟩ : D.weylSubgroup K) =
        ⟨(l.map fun i => D.weylElement (t.simpleIndex ht i) K 1).prod * D.torusPoints K s,
          mul_mem (D.list_prod_map_weylElement_mem_weylSubgroup K l)
            (D.torusPoints_mem_weylSubgroup K s)⟩ :=
      Subtype.ext hls.symm
    rw [hsub, D.weylProjection_list_prod_mul_torusPoints K l s, hword_one]
  exact D.eq_one_of_mem_positivePoints_of_weylProjection_eq_one K huP huW hproj

/-- Over any field, the intersection of the Borel-type subgroup and the Weyl subgroup of a
Chevalley datum is precisely the image of its actual torus. -/
@[simp]
theorem borelSubgroup_inf_weylSubgroup_eq_range_torusPoints :
    D.borelSubgroup K ⊓ D.weylSubgroup K = (D.torusPoints K).range := by
  apply le_antisymm
  · intro g hg
    rw [Subgroup.mem_inf] at hg
    obtain ⟨hgB, hgW⟩ := hg
    obtain ⟨u, huP, s, rfl⟩ := (D.mem_borelSubgroup_iff K).mp hgB
    have huW : u ∈ D.weylSubgroup K := by
      have hts : D.torusPoints K s ∈ D.weylSubgroup K := D.torusPoints_mem_weylSubgroup K s
      simpa only [mul_inv_cancel_right] using mul_mem hgW (inv_mem hts)
    have hu1 : u = 1 := by
      have hmem : u ∈ D.positivePoints K ⊓ D.weylSubgroup K :=
        Subgroup.mem_inf.mpr ⟨huP, huW⟩
      rwa [D.positivePoints_inf_weylSubgroup_eq_bot K, Subgroup.mem_bot] at hmem
    rw [hu1, one_mul]
    exact ⟨s, rfl⟩
  · refine le_inf (D.range_torusPoints_le_borelSubgroup K) ?_
    rintro _ ⟨s, rfl⟩
    exact D.torusPoints_mem_weylSubgroup K s

/-- Over any field, the intersection of the Weyl subgroup and the Borel-type subgroup of a
Chevalley datum is precisely the image of its actual torus. -/
@[simp]
theorem weylSubgroup_inf_borelSubgroup_eq_range_torusPoints :
    D.weylSubgroup K ⊓ D.borelSubgroup K = (D.torusPoints K).range := by
  rw [inf_comm, D.borelSubgroup_inf_weylSubgroup_eq_range_torusPoints K]

end Field

end TauCeti.DynkinType.ChevalleyDatum
