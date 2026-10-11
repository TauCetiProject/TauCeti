/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.FundamentalGroup.VanKampen.Basic
public import TauCeti.AlgebraicTopology.UniversalCover.Circle.FundamentalGroup
public import TauCeti.GroupTheory.CoprodI
public import TauCeti.Topology.WedgeSum
public import TauCeti.Topology.Circle.Punctured

import TauCeti.AlgebraicTopology.FundamentalGroup.HomotopyEquiv
import TauCeti.Topology.Homotopy.HomotopyEquiv

/-!
# The fundamental group of a wedge sum

Let `(X i, x i)` be path-connected pointed spaces, each base point `x i` having an open
neighbourhood `V i` which deformation retracts onto `x i` (relative to `x i`).  Then the
fundamental group of the wedge sum `⋁ᵢ X i` is the free product of the groups `π₁(X i, x i)`: the
homomorphism `TauCeti.WedgeSum.fundamentalGroupLift` out of the free product, induced by the
inclusions of the summands, is an isomorphism.

This is the Seifert--van Kampen theorem for the family of open sets
`U i = X i ∨ ⋁_{j ≠ i} V j` (`TauCeti.vanKampenWideEquiv`): any two of them meet in
`C = ⋁ⱼ V j`, which contracts onto the wedge point, and each `U i` deformation retracts onto
`X i` by contracting the other neighbourhoods `V j`.

For a family of circles `Circle` based at `1`, where `Circle ∖ {-1}` contracts onto `1` along
the chords to `1`, the free product is a free product of copies of `ℤ`, so the fundamental group
of a wedge of circles indexed by `ι` is the free group on `ι`
(`TauCeti.WedgeSum.circleFundamentalGroupMulEquiv`), the generator `i` being the loop going once
counterclockwise around the `i`-th circle.

## Main declarations

* `TauCeti.WedgeSum.fundamentalGroupLift`: the homomorphism `∗ᵢ π₁(X i, x i) →* π₁(⋁ᵢ X i)`
  induced by the inclusions of the summands.
* `TauCeti.WedgeSum.fundamentalGroupLift_bijective` and
  `TauCeti.WedgeSum.fundamentalGroupMulEquiv`: **the fundamental group of a wedge sum is the free
  product of the fundamental groups of the summands.**
* `TauCeti.WedgeSum.circleFundamentalGroupMulEquiv` and
  `TauCeti.WedgeSum.circleFundamentalGroupMulEquiv_expLoop`: **the fundamental group of a wedge
  of circles is free on the circles**, with the loop around the `i`-th circle sent to the
  generator `i`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 1.2, Example 1.21: the fundamental group of a wedge sum, and of a wedge of circles.
-/

public section

noncomputable section

namespace TauCeti

namespace WedgeSum

open Set Topology ContinuousMap unitInterval Monoid

universe u v

variable {ι : Type u} {X : ι → Type v} [∀ i, TopologicalSpace (X i)] {x : ∀ i, X i}

/-- The homomorphism from the free product of the fundamental groups of the summands to the
fundamental group of the wedge sum, induced on each factor by the inclusion of the summand. -/
def fundamentalGroupLift (x : ∀ i, X i) :
    CoprodI (fun i => FundamentalGroup (X i) (x i)) →* FundamentalGroup (WedgeSum x) (base x) :=
  CoprodI.lift fun i => FundamentalGroup.mapOfEq (incl x i) (incl_apply_self i)

@[simp]
lemma fundamentalGroupLift_of {i : ι} (g : FundamentalGroup (X i) (x i)) :
    fundamentalGroupLift x (CoprodI.of g) =
      FundamentalGroup.mapOfEq (incl x i) (incl_apply_self i) g := by
  simp [fundamentalGroupLift]

/-! ### The open cover of the wedge sum

Fix open neighbourhoods `V i ∋ x i` with deformation retractions `H i` onto the base points. The
open set `U i` of the cover is the wedge sum of the sets `nbhd V i j`, which are `X i` for `j = i`
and `V j` otherwise. -/

section Cover

variable (V : ∀ i, Set (X i)) (hxV : ∀ i, x i ∈ V i)
  (H : ∀ i, (ContinuousMap.id (V i)).HomotopyRel (.const (V i) ⟨x i, hxV i⟩) {⟨x i, hxV i⟩})

/-- The summands of the `i`-th open set of the cover: all of `X i`, and `V j` for `j ≠ i`. -/
private def nbhd (i : ι) (j : ι) : Set (X j) :=
  {z | j = i ∨ z ∈ V j}

omit [∀ i, TopologicalSpace (X i)] in
private lemma base_mem_nbhd {V : ∀ i, Set (X i)} (hxV : ∀ i, x i ∈ V i) (i j : ι) :
    x j ∈ nbhd V i j :=
  .inr (hxV j)

omit [∀ i, TopologicalSpace (X i)] in
private lemma mem_nbhd_self (i : ι) (z : X i) : z ∈ nbhd V i i :=
  .inl rfl

private lemma isOpen_nbhd (hVo : ∀ i, IsOpen (V i)) (i j : ι) : IsOpen (nbhd V i j) := by
  by_cases hj : j = i
  · convert isOpen_univ
    ext z
    simp [nbhd, hj]
  · convert hVo j using 1
    ext z
    simp [nbhd, hj]

/-- The wedge of the neighbourhoods `V j` lies in each open set of the cover. -/
private lemma range_subtypeVal_subset (i : ι) :
    range (subtypeVal hxV) ⊆ range (subtypeVal (base_mem_nbhd hxV i)) := by
  rintro _ ⟨w, rfl⟩
  induction w using ind with
  | base =>
    rw [subtypeVal_base]
    exact base_mem_range_subtypeVal _
  | incl j a =>
    rw [subtypeVal_incl]
    exact (incl_mem_range_subtypeVal_iff _).2 (Or.inr a.2)

/-- Two distinct open sets of the cover meet in the wedge of the neighbourhoods `V j`. -/
private lemma range_inter_range_subset {i j : ι} (hij : i ≠ j) :
    range (subtypeVal (base_mem_nbhd hxV i)) ∩ range (subtypeVal (base_mem_nbhd hxV j)) ⊆
      range (subtypeVal hxV) := by
  intro w ⟨hwi, hwj⟩
  induction w using ind with
  | base => exact base_mem_range_subtypeVal hxV
  | incl k z =>
    rw [incl_mem_range_subtypeVal_iff] at hwi hwj ⊢
    rcases hwi with rfl | hz
    · exact hwj.resolve_left hij
    · exact hz

/-- The deformation retractions of the neighbourhoods fix the base points. -/
@[simp]
private lemma homotopy_base (i : ι) (t : I) : H i (t, ⟨x i, hxV i⟩) = ⟨x i, hxV i⟩ :=
  (H i).eq_fst t rfl

/-- The contraction of the wedge sum of the neighbourhoods `V i` onto the wedge point. -/
private def contraction :
    Homotopy (ContinuousMap.id (WedgeSum fun i => (⟨x i, hxV i⟩ : V i)))
      (.const _ (base _)) where
  toContinuousMap := liftProd (fun i => (incl _ i).comp (H i).toContinuousMap)
    (.const _ (base _)) fun i t => by
      simp only [ContinuousMap.comp_apply, HomotopyWith.coe_toContinuousMap,
        ContinuousMap.const_apply]
      rw [homotopy_base]
      exact incl_apply_self i
  map_zero_left w := by
    induction w using ind with
    | base => simp [ContinuousMap.toFun_eq_coe]
    | incl i a => simp [ContinuousMap.toFun_eq_coe]
  map_one_left w := by
    induction w using ind with
    | base => simp [ContinuousMap.toFun_eq_coe]
    | incl i a => simp [ContinuousMap.toFun_eq_coe]

/-- The deformation retraction of the wedge sum of the sets `nbhd V i j` onto `X i`: it fixes
`X i` and contracts each `V j`, `j ≠ i`, onto the base point. -/
private def retraction (i : ι) :
    Homotopy (ContinuousMap.id (WedgeSum fun j => (⟨x j, base_mem_nbhd hxV i j⟩ : nbhd V i j)))
      (((incl _ i).comp ⟨fun z => ⟨z, mem_nbhd_self V i z⟩, by fun_prop⟩).comp
        ((proj x i).comp (subtypeVal (base_mem_nbhd hxV i)))) := by
  classical
  refine
    { toContinuousMap := liftProd
        (fun j => if hj : j = i then (incl _ j).comp ContinuousMap.snd else
          (incl _ j).comp ⟨fun p => ⟨H j (p.1, ⟨p.2, p.2.2.resolve_left hj⟩), .inr (H j _).2⟩,
            by fun_prop⟩)
        (.const _ (base _)) fun j t => ?_
      map_zero_left := fun w => ?_
      map_one_left := fun w => ?_ }
  · split_ifs with hj
    · simp
    · simp
  · induction w using ind with
    | base => simp [ContinuousMap.toFun_eq_coe]
    | incl j a =>
      simp only [ContinuousMap.toFun_eq_coe, liftProd_incl]
      split_ifs with hj <;> simp
  · induction w using ind with
    | base => simp [ContinuousMap.toFun_eq_coe]
    | incl j a =>
      simp only [ContinuousMap.toFun_eq_coe, liftProd_incl]
      by_cases hj : j = i
      · subst hj
        simp
      · simp [hj, proj_incl_of_ne hj]

/-- The homotopy equivalence of `X i` with the wedge sum of the sets `nbhd V i j`, given by the
inclusion of the `i`-th summand. -/
private def nbhdHomotopyEquiv (i : ι) :
    X i ≃ₕ WedgeSum fun j => (⟨x j, base_mem_nbhd hxV i j⟩ : nbhd V i j) where
  toFun := (incl _ i).comp ⟨fun z => ⟨z, mem_nbhd_self V i z⟩, by fun_prop⟩
  invFun := (proj x i).comp (subtypeVal (base_mem_nbhd hxV i))
  left_inv := by
    have h : ((proj x i).comp (subtypeVal (base_mem_nbhd hxV i))).comp
        ((incl _ i).comp ⟨fun z => ⟨z, mem_nbhd_self V i z⟩, by fun_prop⟩) =
          ContinuousMap.id (X i) := by
      ext z
      simp
    rw [h]
  right_inv := ⟨(retraction V hxV H i).symm⟩

end Cover

/-- Over the empty family both groups are trivial: the free product has no factors and the wedge
sum is a point. -/
private lemma fundamentalGroupLift_bijective_of_isEmpty [IsEmpty ι] :
    Function.Bijective (fundamentalGroupLift x) := by
  have : Subsingleton (CoprodI fun i => FundamentalGroup (X i) (x i)) := by
    have h (c : CoprodI fun i => FundamentalGroup (X i) (x i)) : c = 1 := by
      induction c using CoprodI.induction_on with
      | one => rfl
      | of m => exact isEmptyElim (α := ι) ‹_›
      | mul _ _ ha hb => rw [ha, hb, mul_one]
    exact ⟨fun a b => (h a).trans (h b).symm⟩
  exact ⟨Function.injective_of_subsingleton _, fun _ => ⟨1, Subsingleton.elim _ _⟩⟩

section FreeProduct

variable [∀ i, PathConnectedSpace (X i)]
  (hV : ∀ i, ∃ V : Set (X i), IsOpen V ∧ ∃ hx : x i ∈ V,
    Nonempty ((ContinuousMap.id V).HomotopyRel (.const V ⟨x i, hx⟩) {⟨x i, hx⟩}))

include hV in
/-- **The fundamental group of a wedge sum is the free product of the fundamental groups of the
summands.**  If every summand `X i` is path connected and its base point `x i` has an open
neighbourhood `V` which deformation retracts onto `x i`, then the homomorphism from the free
product of the groups `π₁(X i, x i)` to `π₁(⋁ᵢ X i)` induced by the inclusions of the summands is
bijective. -/
theorem fundamentalGroupLift_bijective :
    Function.Bijective (fundamentalGroupLift x) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact fundamentalGroupLift_bijective_of_isEmpty
  choose V hVo hxV hH using hV
  let H i := (hH i).some
  -- The open cover: `U i` is `X i` wedged with the `V j`, and two of them meet in `C = ⋁ⱼ V j`.
  let U (i : ι) : Set (WedgeSum x) := range (subtypeVal (base_mem_nbhd hxV i))
  let C : Set (WedgeSum x) := range (subtypeVal hxV)
  have hUo (i : ι) : IsOpen (U i) :=
    (isOpenEmbedding_subtypeVal _ (isOpen_nbhd V hVo i)).isOpen_range
  have hx : base x ∈ C := base_mem_range_subtypeVal hxV
  have hCU (i : ι) : C ⊆ U i := range_subtypeVal_subset V hxV i
  have hUC : Pairwise fun i j => U i ∩ U j ⊆ C := fun _ _ hij => range_inter_range_subset V hxV hij
  have hU (w : WedgeSum x) : ∃ i, U i ∈ 𝓝 w := by
    induction w using ind with
    | base => exact ⟨hι.some, (hUo _).mem_nhds (hCU _ hx)⟩
    | incl i z =>
      exact ⟨i, (hUo i).mem_nhds ((incl_mem_range_subtypeVal_iff _).2 (mem_nbhd_self V i z))⟩
  -- `C` is contractible, and `X i` is homotopy equivalent to `U i` by the inclusion.
  have hC : IsSimplyConnected C := by
    have : ContractibleSpace (WedgeSum fun i => (⟨x i, hxV i⟩ : V i)) :=
      (contractible_iff_id_nullhomotopic _).2 ⟨_, ⟨contraction V hxV H⟩⟩
    have : ContractibleSpace C :=
      (isOpenEmbedding_subtypeVal hxV hVo).isEmbedding.toHomeomorph.symm.contractibleSpace
    exact SimplyConnectedSpace.ofContractible C
  let e (i : ι) : X i ≃ₕ U i := (nbhdHomotopyEquiv V hxV H i).trans
    (isOpenEmbedding_subtypeVal _ (isOpen_nbhd V hVo i)).isEmbedding.toHomeomorph.toHomotopyEquiv
  have he (i : ι) (z : X i) : ((e i).toFun z : WedgeSum x) = incl x i z := by
    simp [e, nbhdHomotopyEquiv, ContinuousMap.HomotopyEquiv.trans, Homeomorph.toHomotopyEquiv]
  have hUp (i : ι) : IsPathConnected (U i) :=
    isPathConnected_iff_pathConnectedSpace.2 (e i).pathConnectedSpace
  have heb (i : ι) : (e i).toFun (x i) = ⟨base x, hCU i hx⟩ := Subtype.ext (by rw [he]; simp)
  let ψ (i : ι) := FundamentalGroup.mapOfEq (e i).toFun (heb i)
  have hψ (i : ι) : Function.Bijective (ψ i) :=
    (CategoryTheory.eqToIso (congrArg FundamentalGroupoid.mk (heb i))).conj.bijective.comp
      ((e i).fundamentalGroup_map_bijective (x i))
  -- `fundamentalGroupLift` is the van Kampen isomorphism after the isomorphisms `ψ i`.
  have hfac : fundamentalGroupLift x = (vanKampenWideEquiv hU hUp hC hCU hUC hx).toMonoidHom.comp
      (MulEquiv.coprodICongr fun i => MulEquiv.ofBijective (ψ i) (hψ i)).toMonoidHom := by
    refine CoprodI.ext_hom _ _ fun i => MonoidHom.ext fun g => ?_
    induction g using Path.Homotopic.Quotient.ind with | mk γ =>
    simp only [MonoidHom.comp_apply, fundamentalGroupLift_of, MulEquiv.coe_toMonoidHom,
      MulEquiv.coprodICongr_apply_of, MulEquiv.ofBijective_apply, vanKampenWideEquiv_apply,
      vanKampenWideLift_of, ψ, FundamentalGroup.mapOfEq_apply, FundamentalGroup.map_apply]
    simp only [← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_cast]
    congr 1
    ext t
    exact (he i (γ t)).symm
  rw [hfac]
  exact (vanKampenWideEquiv hU hUp hC hCU hUC hx).bijective.comp
    (MulEquiv.coprodICongr fun i => MulEquiv.ofBijective (ψ i) (hψ i)).bijective

/-- **The fundamental group of a wedge sum is the free product of the fundamental groups of the
summands**, under the hypotheses of `TauCeti.WedgeSum.fundamentalGroupLift_bijective`.  Its
underlying homomorphism is `TauCeti.WedgeSum.fundamentalGroupLift`. -/
def fundamentalGroupMulEquiv :
    CoprodI (fun i => FundamentalGroup (X i) (x i)) ≃* FundamentalGroup (WedgeSum x) (base x) :=
  MulEquiv.ofBijective _ (fundamentalGroupLift_bijective hV)

@[simp]
lemma fundamentalGroupMulEquiv_apply (g : CoprodI fun i => FundamentalGroup (X i) (x i)) :
    fundamentalGroupMulEquiv hV g = fundamentalGroupLift x g :=
  (rfl)

/-- The inverse of `TauCeti.WedgeSum.fundamentalGroupMulEquiv` sends the image of a loop in the
`i`-th summand to the corresponding element of the `i`-th factor of the free product. -/
@[simp]
lemma fundamentalGroupMulEquiv_symm_mapOfEq {i : ι} (g : FundamentalGroup (X i) (x i)) :
    (fundamentalGroupMulEquiv hV).symm (FundamentalGroup.mapOfEq (incl x i) (incl_apply_self i) g) =
      CoprodI.of (M := fun i => FundamentalGroup (X i) (x i)) g :=
  (MulEquiv.symm_apply_eq _).2 (fundamentalGroupLift_of g).symm

end FreeProduct

/-! ### A wedge of circles -/

section Circle

/-- **The fundamental group of a wedge of circles is the free group on the circles.**  The
generator `i` of the free group corresponds to the loop going once counterclockwise around the
`i`-th circle (`TauCeti.WedgeSum.circleFundamentalGroupMulEquiv_expLoop`). -/
def circleFundamentalGroupMulEquiv (ι : Type u) :
    FundamentalGroup (WedgeSum fun _ : ι => (1 : Circle)) (base _) ≃* FreeGroup ι :=
  (fundamentalGroupMulEquiv fun _ => ⟨{z : Circle | z ≠ -1}, isOpen_ne,
    (Circle.neg_ne_self 1).symm, ⟨circleChordHomotopy⟩⟩).symm.trans
    ((MulEquiv.coprodICongr fun _ =>
      (Circle.fundamentalGroupMulEquiv 1).trans FreeGroup.mulEquivIntOfUnique.symm).trans
      freeGroupEquivCoprodI.symm)

/-- The loop going once counterclockwise around the `i`-th circle of a wedge of circles is the
generator `i` of the free group. -/
@[simp]
theorem circleFundamentalGroupMulEquiv_expLoop (i : ι) :
    circleFundamentalGroupMulEquiv ι
        (FundamentalGroup.mapOfEq (incl _ i) (incl_apply_self i)
          (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk Circle.expLoop))) =
      FreeGroup.of i := by
  have h : FreeGroup.mulEquivIntOfUnique.symm (Multiplicative.ofAdd (1 : ℤ)) = FreeGroup.of () :=
    (MulEquiv.symm_apply_eq _).2 (by simp [FreeGroup.mulEquivIntOfUnique,
      FreeGroup.equivIntOfUnique])
  simp [circleFundamentalGroupMulEquiv, h]

end Circle

end WedgeSum

end TauCeti
