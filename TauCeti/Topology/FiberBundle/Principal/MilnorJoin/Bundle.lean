/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ClassifyingSpace.Basic
public import TauCeti.Topology.FiberBundle.Principal.Basic
public import TauCeti.Topology.FiberBundle.Principal.MilnorJoin.Basic
public import TauCeti.Topology.PartitionOfUnity.Shrink
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.Separation.Hausdorff
import TauCeti.Topology.Algebra.GroupAction.Quotient
import TauCeti.Topology.Order.Lattice

/-!
# The strong-topology Milnor classifying space and universal principal bundle

For a topological group `G`, this file defines `TauCeti.MilnorClassifyingSpace G` as the orbit
quotient of `TauCeti.MilnorTotalSpace G` by the free right `G`-action (`MulAction Gᵐᵒᵖ`), constructs
Milnor's numerable partition of unity subordinate to `V_i = {b | 0 < t_i(b)}` via finite-support
tail control of `maxBaseWeight G`, equips the projection with normalized local sections and
principal `G`-bundle charts `milnorTrivialization G i`, and proves Hausdorffness when `T2Space G`.

## Main definitions and results

* `TauCeti.MilnorClassifyingSpace`, `milnorClassifyingSpaceBasepoint`: orbit quotient of
  `MilnorTotalSpace G`.
* `TauCeti.MilnorClassifyingSpace.baseWeight`, `baseCoordSet`, `maxBaseWeight`,
  `TauCeti.milnorPartitionOfUnity`, `isSubordinate_milnorPartitionOfUnity`: descended weights `t_i`,
  open cover `V_i`, continuous supremum `m = ⨆ i, t_i`, and subordinate partition of unity.
* `TauCeti.MilnorClassifyingSpace.localSection`, `TauCeti.MilnorBundleFiber`,
  `TauCeti.milnorTrivialization`, `coordChange_milnorTrivialization`,
  `instPrincipalBundleMilnorBundleFiber`, `instT2SpaceMilnorClassifyingSpace`,
  `weakToMilnorClassifyingSpace`, `MonoidHom.milnorClassifyingSpaceMap`.

## References

* J. Milnor, *Construction of universal bundles, II*, Ann. of Math. (2) 63 (1956), 430–436, §§2–3.
* T. tom Dieck, *Algebraic Topology*, EMS Textbooks in Mathematics, 2008, §14.4.3.
-/

public section

noncomputable section

open Bundle Filter Function MulOpposite Set Topology

universe u v w

namespace TauCeti

section OrbitQuotient

variable (G : Type u) [Group G]

/-- Milnor's classifying space `B_join(G)` with the quotient of the strong coordinate topology on
`MilnorTotalSpace G` by the free right action of `G` (`MulAction Gᵐᵒᵖ`). -/
abbrev MilnorClassifyingSpace : Type u :=
  MulAction.orbitRel.Quotient Gᵐᵒᵖ (MilnorTotalSpace G)

/-- The distinguished base point of `MilnorClassifyingSpace G`. -/
def milnorClassifyingSpaceBasepoint : MilnorClassifyingSpace G :=
  Quotient.mk'' (MilnorTotalSpace.basepoint G)

instance instInhabitedMilnorClassifyingSpace : Inhabited (MilnorClassifyingSpace G) :=
  ⟨milnorClassifyingSpaceBasepoint G⟩

end OrbitQuotient

/-! ### Descended weights, coordinate cover, and numerable partition of unity -/

namespace MilnorClassifyingSpace

section BaseWeights

variable (G : Type u) [Group G] [TopologicalSpace G]

/-- The `i`-th barycentric weight descended to a continuous map `MilnorClassifyingSpace G → ℝ`. -/
def baseWeight (i : ℕ) : C(MilnorClassifyingSpace G, ℝ) where
  toFun := MulAction.orbitRelQuotientLift (MilnorTotalSpace.weight i)
    fun g p ↦ MilnorTotalSpace.weight_smul g i p
  continuous_toFun :=
    continuous_orbitRelQuotientLift_iff.mpr (MilnorTotalSpace.continuous_weight i)

@[simp] theorem baseWeight_mk' (i : ℕ) (p : MilnorTotalSpace G) :
    baseWeight G i (Quotient.mk'' p) = MilnorTotalSpace.weight i p :=
  MulAction.orbitRelQuotientLift_mk p

/-- The `i`-th coordinate open set `V_i = {b | 0 < t_i(b)}` in `MilnorClassifyingSpace G`. -/
def baseCoordSet (i : ℕ) : Set (MilnorClassifyingSpace G) := {b | 0 < baseWeight G i b}

variable {G}

@[simp] theorem mem_baseCoordSet_iff {i : ℕ} {b : MilnorClassifyingSpace G} :
    b ∈ baseCoordSet G i ↔ 0 < baseWeight G i b := Iff.rfl
theorem mk'_mem_baseCoordSet_iff {i : ℕ} {p : MilnorTotalSpace G} :
    (Quotient.mk'' p : MilnorClassifyingSpace G) ∈ baseCoordSet G i ↔
      p ∈ MilnorTotalSpace.coordSet G i := by
  simp [mem_baseCoordSet_iff]
@[simp] theorem preimage_baseCoordSet (G : Type u) [Group G] [TopologicalSpace G] (i : ℕ) :
    (Quotient.mk'' : MilnorTotalSpace G → MilnorClassifyingSpace G) ⁻¹' baseCoordSet G i =
      MilnorTotalSpace.coordSet G i := by
  ext; simp
theorem image_coordSet_eq_baseCoordSet (G : Type u) [Group G] [TopologicalSpace G] (i : ℕ) :
    (Quotient.mk'' : MilnorTotalSpace G → MilnorClassifyingSpace G) ''
      MilnorTotalSpace.coordSet G i = baseCoordSet G i := by
  rw [← preimage_baseCoordSet, Quotient.mk_surjective.image_preimage]
theorem isOpen_baseCoordSet (G : Type u) [Group G] [TopologicalSpace G] (i : ℕ) :
    IsOpen (baseCoordSet G i) := isOpen_lt continuous_const (baseWeight G i).continuous

theorem baseWeight_nonneg (i : ℕ) (b : MilnorClassifyingSpace G) : 0 ≤ baseWeight G i b := by
  obtain ⟨p, rfl⟩ := Quotient.mk_surjective b
  simpa using MilnorTotalSpace.weight_nonneg i p
theorem baseWeight_le_one (i : ℕ) (b : MilnorClassifyingSpace G) : baseWeight G i b ≤ 1 := by
  obtain ⟨p, rfl⟩ := Quotient.mk_surjective b
  simpa using MilnorTotalSpace.weight_le_one i p
theorem finite_support_baseWeight (b : MilnorClassifyingSpace G) :
    (support fun i ↦ baseWeight G i b).Finite := by
  obtain ⟨p, rfl⟩ := Quotient.mk_surjective b
  simpa using MilnorTotalSpace.finite_support_weight p
theorem hasSum_baseWeight (b : MilnorClassifyingSpace G) : HasSum (fun i ↦ baseWeight G i b) 1 := by
  obtain ⟨p, rfl⟩ := Quotient.mk_surjective b
  simpa using MilnorTotalSpace.hasSum_weight p
@[simp] theorem tsum_baseWeight (b : MilnorClassifyingSpace G) : ∑' i, baseWeight G i b = 1 :=
  (hasSum_baseWeight b).tsum_eq
theorem exists_mem_baseCoordSet (b : MilnorClassifyingSpace G) : ∃ i, b ∈ baseCoordSet G i := by
  obtain ⟨p, rfl⟩ := Quotient.mk_surjective b
  simpa [mem_baseCoordSet_iff] using MilnorTotalSpace.exists_weight_pos p
@[simp] theorem iUnion_baseCoordSet (G : Type u) [Group G] [TopologicalSpace G] :
    ⋃ i, baseCoordSet G i = univ :=
  eq_univ_of_forall fun b ↦ mem_iUnion.mpr (exists_mem_baseCoordSet b)

private theorem baseWeight_eq_zero_of_notMem {b : MilnorClassifyingSpace G} {i : ℕ}
    (hi : i ∉ (finite_support_baseWeight b).toFinset) : baseWeight G i b = 0 :=
  not_not.mp fun hne ↦ hi ((finite_support_baseWeight b).mem_toFinset.mpr hne)

private theorem sum_toFinset_support_baseWeight (b : MilnorClassifyingSpace G) :
    ∑ i ∈ (finite_support_baseWeight b).toFinset, baseWeight G i b = 1 :=
  (tsum_eq_sum fun _ ↦ baseWeight_eq_zero_of_notMem).symm.trans (tsum_baseWeight b)

/-- Finite-support tail bound: for `j ∉ I`, `baseWeight G j b ≤ 1 - ∑ i ∈ I, baseWeight G i b`. -/
theorem baseWeight_le_one_sub_sum {b : MilnorClassifyingSpace G} {I : Finset ℕ} {j : ℕ}
    (hj : j ∉ I) : baseWeight G j b ≤ 1 - ∑ i ∈ I, baseWeight G i b := by
  have hle := sum_le_hasSum (insert j I) (fun k _ ↦ baseWeight_nonneg k b) (hasSum_baseWeight b)
  rw [Finset.sum_insert hj] at hle
  linarith

private def maxBaseWeightFun (G : Type u) [Group G] [TopologicalSpace G]
    (b : MilnorClassifyingSpace G) : ℝ := ⨆ i : ℕ, baseWeight G i b

private theorem le_maxBaseWeightFun (i : ℕ) (b : MilnorClassifyingSpace G) :
    baseWeight G i b ≤ maxBaseWeightFun G b :=
  le_ciSup ⟨1, forall_mem_range.2 fun j ↦ baseWeight_le_one j b⟩ i

private theorem continuous_maxBaseWeightFun (G : Type u) [Group G] [TopologicalSpace G] :
    Continuous (maxBaseWeightFun G) := by
  refine TauCeti.continuous_ciSup_of_eventually_le (fun i ↦ (baseWeight G i).continuous)
    (fun b ↦ ⟨1, forall_mem_range.2 fun j ↦ baseWeight_le_one j b⟩) baseWeight_nonneg fun b₀ ↦ ?_
  let I := (finite_support_baseWeight b₀).toFinset
  obtain ⟨i₀, hi₀⟩ := exists_mem_baseCoordSet b₀
  have hm₀ : 0 < maxBaseWeightFun G b₀ := hi₀.trans_le (le_maxBaseWeightFun i₀ b₀)
  have hcont_sup : Continuous fun x : MilnorClassifyingSpace G ↦ ⨆ i : I, baseWeight G i.val x :=
    TauCeti.continuous_ciSup_of_finite fun i : I ↦ (baseWeight G i.val).continuous
  have hcont_sum : Continuous fun x : MilnorClassifyingSpace G ↦ ∑ i ∈ I, baseWeight G i x := by
    fun_prop
  have hsup₀ : maxBaseWeightFun G b₀ = ⨆ i : I, baseWeight G i.val b₀ :=
    TauCeti.ciSup_eq_ciSup_of_notMem_le
      ⟨1, forall_mem_range.2 fun j ↦ baseWeight_le_one j b₀⟩ (fun i ↦ baseWeight_nonneg i b₀)
      fun _ hj ↦ (baseWeight_eq_zero_of_notMem hj).symm ▸
        Real.iSup_nonneg fun i ↦ baseWeight_nonneg i.val b₀
  have hW : ({x | 1 - maxBaseWeightFun G b₀ / 3 < ∑ i ∈ I, baseWeight G i x} ∩
      {x | maxBaseWeightFun G b₀ / 2 < ⨆ i : I, baseWeight G i.val x}) ∈ 𝓝 b₀ :=
    ((isOpen_lt continuous_const hcont_sum).inter (isOpen_lt continuous_const hcont_sup)).mem_nhds
      ⟨by have := sum_toFinset_support_baseWeight b₀; dsimp; linarith,
       by dsimp; rw [← hsup₀]; linarith⟩
  exact ⟨I, eventually_of_mem hW fun x ⟨hx1, hx2⟩ j hj ↦ by
    have := baseWeight_le_one_sub_sum (b := x) hj; dsimp at hx1 hx2; linarith⟩

/-- Pointwise maximum weight `m(b) = ⨆ i, baseWeight G i b` as a continuous function. -/
def maxBaseWeight (G : Type u) [Group G] [TopologicalSpace G] : C(MilnorClassifyingSpace G, ℝ) :=
  ⟨maxBaseWeightFun G, continuous_maxBaseWeightFun G⟩

@[simp] theorem maxBaseWeight_apply (b : MilnorClassifyingSpace G) :
    maxBaseWeight G b = ⨆ i : ℕ, baseWeight G i b := (rfl)
theorem le_maxBaseWeight (i : ℕ) (b : MilnorClassifyingSpace G) :
    baseWeight G i b ≤ maxBaseWeight G b := le_maxBaseWeightFun i b
theorem maxBaseWeight_pos (b : MilnorClassifyingSpace G) : 0 < maxBaseWeight G b :=
  let ⟨i₀, hi₀⟩ := exists_mem_baseCoordSet b
  hi₀.trans_le (le_maxBaseWeight i₀ b)

private theorem locallyFinite_support_halfMaxTrunc_baseWeight
    (G : Type u) [Group G] [TopologicalSpace G] :
    LocallyFinite fun i ↦ support
      (PartitionOfUnity.halfMaxTrunc (baseWeight G) (maxBaseWeight G) i) := fun b₀ ↦ by
  let I := (finite_support_baseWeight b₀).toFinset
  have hm₀ := maxBaseWeight_pos b₀
  have hcont_sum : Continuous fun x : MilnorClassifyingSpace G ↦ ∑ i ∈ I, baseWeight G i x := by
    fun_prop
  have hW : ({x | 1 - maxBaseWeight G b₀ / 4 < ∑ i ∈ I, baseWeight G i x} ∩
      {x | maxBaseWeight G b₀ / 2 < maxBaseWeight G x}) ∈ 𝓝 b₀ :=
    ((isOpen_lt continuous_const hcont_sum).inter
      (isOpen_lt continuous_const (maxBaseWeight G).continuous)).mem_nhds
      ⟨by have := sum_toFinset_support_baseWeight b₀; dsimp; linarith, by dsimp; linarith⟩
  refine ⟨_, hW, I.finite_toSet.subset fun j ⟨x, hx_supp, hx1, hx2⟩ ↦ ?_⟩
  rw [Finset.mem_coe]; by_contra hj
  have htail := baseWeight_le_one_sub_sum (b := x) hj
  dsimp at hx1 hx2
  rw [Function.mem_support, PartitionOfUnity.halfMaxTrunc_apply] at hx_supp
  exact hx_supp (max_eq_left (by linarith))

end BaseWeights

end MilnorClassifyingSpace

/-- **Milnor's subordinate partition of unity** on `MilnorClassifyingSpace G`. -/
def milnorPartitionOfUnity (G : Type u) [Group G] [TopologicalSpace G] :
    PartitionOfUnity ℕ (MilnorClassifyingSpace G) :=
  PartitionOfUnity.shrinkOfMax (MilnorClassifyingSpace.baseWeight G)
    (MilnorClassifyingSpace.maxBaseWeight G)
    (MilnorClassifyingSpace.locallyFinite_support_halfMaxTrunc_baseWeight G)
    fun b ↦ exists_lt_of_lt_ciSup (half_lt_self (MilnorClassifyingSpace.maxBaseWeight_pos b))

/-- Milnor's partition of unity on `MilnorClassifyingSpace G` is subordinate to the open cover
`MilnorClassifyingSpace.baseCoordSet G` of positive-weight coordinate sets. -/
theorem isSubordinate_milnorPartitionOfUnity (G : Type u) [Group G] [TopologicalSpace G] :
    (milnorPartitionOfUnity G).IsSubordinate (MilnorClassifyingSpace.baseCoordSet G) :=
  PartitionOfUnity.isSubordinate_shrinkOfMax MilnorClassifyingSpace.maxBaseWeight_pos
    fun i b hb ↦ (MilnorClassifyingSpace.baseWeight_nonneg i b).lt_of_ne' hb

/-! ### Local sections, Hausdorffness, and principal bundle structure -/

namespace MilnorClassifyingSpace

section LocalSections

private def normalize (G : Type u) [Group G] (i : ℕ) (p : MilnorTotalSpace G) :
    MilnorTotalSpace G := by
  classical
  exact if p ∈ MilnorTotalSpace.coordSet G i then op (MilnorTotalSpace.label i p)⁻¹ • p
    else MilnorTotalSpace.basepoint G

private theorem normalize_of_mem {G : Type u} [Group G] {i : ℕ} {p : MilnorTotalSpace G}
    (hp : p ∈ MilnorTotalSpace.coordSet G i) :
    normalize G i p = op (MilnorTotalSpace.label i p)⁻¹ • p := by simp [normalize, hp]

private theorem normalize_smul {G : Type u} [Group G] (i : ℕ) (g : Gᵐᵒᵖ)
    (p : MilnorTotalSpace G) : normalize G i (g • p) = normalize G i p := by
  by_cases hp : p ∈ MilnorTotalSpace.coordSet G i
  · have hgp : op g.unop • p ∈ MilnorTotalSpace.coordSet G i := by simpa using hp
    rw [← op_unop g, normalize_of_mem hgp, normalize_of_mem hp,
      MilnorTotalSpace.label_op_smul g.unop hp, mul_inv_rev,
      _root_.op_smul_op_smul, mul_inv_cancel_left]
  · have hgp : g • p ∉ MilnorTotalSpace.coordSet G i :=
      mt (MilnorTotalSpace.smul_mem_coordSet_iff g).mp hp
    simp [normalize, hp, hgp]

private theorem label_normalize {G : Type u} [Group G] {i : ℕ} {p : MilnorTotalSpace G}
    (hp : p ∈ MilnorTotalSpace.coordSet G i) :
    MilnorTotalSpace.label i (normalize G i p) = 1 := by
  rw [normalize_of_mem hp, MilnorTotalSpace.label_op_smul _ hp, mul_inv_cancel]

private theorem smul_normalize {G : Type u} [Group G] {i : ℕ} {p : MilnorTotalSpace G}
    (hp : p ∈ MilnorTotalSpace.coordSet G i) :
    op (MilnorTotalSpace.label i p) • normalize G i p = p := by
  rw [normalize_of_mem hp, _root_.op_smul_op_smul, inv_mul_cancel, op_one, one_smul]

private def localSectionAux (G : Type u) [Group G] (i : ℕ) :
    MilnorClassifyingSpace G → MilnorTotalSpace G :=
  MulAction.orbitRelQuotientLift (normalize G i) (normalize_smul i)

private theorem localSectionAux_mk' {G : Type u} [Group G] (i : ℕ) (p : MilnorTotalSpace G) :
    localSectionAux G i (Quotient.mk'' p) = normalize G i p :=
  MulAction.orbitRelQuotientLift_mk p

variable {G : Type u} [Group G] [TopologicalSpace G]

private theorem mk'_localSectionAux {i : ℕ} {b : MilnorClassifyingSpace G}
    (hb : b ∈ baseCoordSet G i) :
    (Quotient.mk'' (localSectionAux G i b) : MilnorClassifyingSpace G) = b := by
  obtain ⟨p, rfl⟩ := Quotient.mk_surjective b
  rw [localSectionAux_mk', normalize_of_mem (mk'_mem_baseCoordSet_iff.mp hb)]
  exact MulAction.orbitRel.Quotient.quotient_smul_eq

private theorem localSectionAux_mem_coordSet {i : ℕ} {b : MilnorClassifyingSpace G}
    (hb : b ∈ baseCoordSet G i) : localSectionAux G i b ∈ MilnorTotalSpace.coordSet G i := by
  rwa [← mk'_mem_baseCoordSet_iff, mk'_localSectionAux hb]

private theorem weight_localSectionAux (j : ℕ) {i : ℕ} {b : MilnorClassifyingSpace G}
    (hb : b ∈ baseCoordSet G i) :
    MilnorTotalSpace.weight j (localSectionAux G i b) = baseWeight G j b := by
  rw [← baseWeight_mk' G j, mk'_localSectionAux hb]

private theorem label_localSectionAux {i : ℕ} {b : MilnorClassifyingSpace G}
    (hb : b ∈ baseCoordSet G i) : MilnorTotalSpace.label i (localSectionAux G i b) = 1 := by
  obtain ⟨p, rfl⟩ := Quotient.mk_surjective b
  rw [localSectionAux_mk']
  exact label_normalize (mk'_mem_baseCoordSet_iff.mp hb)

private theorem continuousOn_localSectionAux (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (i : ℕ) :
    ContinuousOn (localSectionAux G i) (baseCoordSet G i) := by
  rw [continuousOn_iff_continuous_domRestrict,
    ((MulAction.isOpenQuotientMap_quotientMk (Γ := Gᵐᵒᵖ) (T := MilnorTotalSpace G)).restrictPreimage
      (baseCoordSet G i)).isQuotientMap.continuous_iff]
  have hnorm : ContinuousOn (normalize G i)
      ((Quotient.mk'' : MilnorTotalSpace G → MilnorClassifyingSpace G) ⁻¹' baseCoordSet G i) := by
    rw [preimage_baseCoordSet]
    exact (((continuous_op.comp continuous_inv).continuousOn.comp
      (MilnorTotalSpace.continuousOn_label i) (mapsTo_univ _ _)).smul continuousOn_id).congr
      fun _ hp ↦ normalize_of_mem hp
  exact (continuousOn_iff_continuous_domRestrict.mp hnorm).congr fun p ↦
    (localSectionAux_mk' i p.val).symm

/-- Local section `s_i : V_i → MilnorTotalSpace G` normalized by `label i (s_i b) = 1`. -/
def localSection (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (i : ℕ) :
    C(baseCoordSet G i, MilnorTotalSpace G) :=
  ⟨(baseCoordSet G i).domRestrict (localSectionAux G i),
    continuousOn_iff_continuous_domRestrict.mp (continuousOn_localSectionAux G i)⟩

@[simp] theorem mk'_localSection [IsTopologicalGroup G] (i : ℕ) (b : baseCoordSet G i) :
    (Quotient.mk'' (localSection G i b) : MilnorClassifyingSpace G) = b.val :=
  mk'_localSectionAux b.property
theorem localSection_mem_coordSet [IsTopologicalGroup G] (i : ℕ) (b : baseCoordSet G i) :
    localSection G i b ∈ MilnorTotalSpace.coordSet G i := localSectionAux_mem_coordSet b.property
@[simp] theorem weight_localSection [IsTopologicalGroup G] (j i : ℕ) (b : baseCoordSet G i) :
    MilnorTotalSpace.weight j (localSection G i b) = baseWeight G j b.val :=
  weight_localSectionAux j b.property
@[simp] theorem label_localSection [IsTopologicalGroup G] (i : ℕ) (b : baseCoordSet G i) :
    MilnorTotalSpace.label i (localSection G i b) = 1 := label_localSectionAux b.property
@[simp] theorem localSection_mk' [IsTopologicalGroup G] {i : ℕ} {p : MilnorTotalSpace G}
    (hp : p ∈ MilnorTotalSpace.coordSet G i) :
    localSection G i ⟨Quotient.mk'' p, mk'_mem_baseCoordSet_iff.mpr hp⟩ =
      op (MilnorTotalSpace.label i p)⁻¹ • p := by
  simpa [localSection, localSectionAux_mk'] using normalize_of_mem hp
theorem smul_localSection_mk' [IsTopologicalGroup G] {i : ℕ} {p : MilnorTotalSpace G}
    (hp : p ∈ MilnorTotalSpace.coordSet G i) :
    op (MilnorTotalSpace.label i p) •
      localSection G i ⟨Quotient.mk'' p, mk'_mem_baseCoordSet_iff.mpr hp⟩ = p := by
  simpa [localSection, localSectionAux_mk'] using smul_normalize hp

end LocalSections

end MilnorClassifyingSpace

instance instT2SpaceMilnorClassifyingSpace (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] : T2Space (MilnorClassifyingSpace G) :=
  t2Space_iff_disjoint_nhds.mpr fun b₁ b₂ hb ↦ by
    by_cases hw : ∀ j,
        MilnorClassifyingSpace.baseWeight G j b₁ = MilnorClassifyingSpace.baseWeight G j b₂
    · obtain ⟨i, hb₁i⟩ := MilnorClassifyingSpace.exists_mem_baseCoordSet b₁
      have hb₂i : b₂ ∈ MilnorClassifyingSpace.baseCoordSet G i := by
        rwa [MilnorClassifyingSpace.mem_baseCoordSet_iff, ← hw i]
      have hs_ne : MilnorClassifyingSpace.localSectionAux G i b₁ ≠
          MilnorClassifyingSpace.localSectionAux G i b₂ := fun h ↦ hb <| by
        rw [← MilnorClassifyingSpace.mk'_localSectionAux hb₁i,
          ← MilnorClassifyingSpace.mk'_localSectionAux hb₂i]
        exact congrArg (Quotient.mk'' : MilnorTotalSpace G → MilnorClassifyingSpace G) h
      exact ((MilnorClassifyingSpace.continuousOn_localSectionAux G i).continuousAt
        ((MilnorClassifyingSpace.isOpen_baseCoordSet G i).mem_nhds hb₁i)).tendsto.disjoint
        (disjoint_nhds_nhds.mpr hs_ne)
        ((MilnorClassifyingSpace.continuousOn_localSectionAux G i).continuousAt
          ((MilnorClassifyingSpace.isOpen_baseCoordSet G i).mem_nhds hb₂i)).tendsto
    · obtain ⟨j, hj⟩ := not_forall.mp hw
      exact (MilnorClassifyingSpace.baseWeight G j).continuous.continuousAt.tendsto.disjoint
        (disjoint_nhds_nhds.mpr hj)
        (MilnorClassifyingSpace.baseWeight G j).continuous.continuousAt.tendsto

/-! ### Bundle fibre family and principal bundle charts -/

section PrincipalBundle

/-- The fibre over `b : MilnorClassifyingSpace G` of Milnor's universal bundle, realized as the
orbit `b.orbit` under the free right action of `G`. -/
abbrev MilnorBundleFiber (G : Type u) [Group G] (b : MilnorClassifyingSpace G) : Type u :=
  MulAction.orbitRel.Quotient.orbit (G := Gᵐᵒᵖ) (α := MilnorTotalSpace G) b

namespace MilnorBundleFiber

section Group

variable {G : Type u} [Group G]

instance instNonempty (b : MilnorClassifyingSpace G) : Nonempty (MilnorBundleFiber G b) :=
  (MulAction.orbitRel.Quotient.nonempty_orbit b).to_subtype

/-- Canonical equivalence identifying `TotalSpace G (MilnorBundleFiber G)` with
`MilnorTotalSpace G`. -/
@[expose] def totalSpaceEquiv (G : Type u) [Group G] :
    TotalSpace G (MilnorBundleFiber G) ≃ MilnorTotalSpace G :=
  (⟨fun x ↦ ⟨x.proj, x.snd⟩, fun x ↦ ⟨x.1, x.2⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩ :
      TotalSpace G (MilnorBundleFiber G) ≃
        Σ ω : MulAction.orbitRel.Quotient Gᵐᵒᵖ (MilnorTotalSpace G), ω.orbit).trans
    (MulAction.selfEquivSigmaOrbits' Gᵐᵒᵖ (MilnorTotalSpace G)).symm

@[simp] theorem totalSpaceEquiv_apply (x : TotalSpace G (MilnorBundleFiber G)) :
    totalSpaceEquiv G x = x.snd.val := (rfl)
@[simp] theorem totalSpaceEquiv_symm_apply (p : MilnorTotalSpace G) :
    (totalSpaceEquiv G).symm p =
      ⟨Quotient.mk'' p, ⟨p, MulAction.orbitRel.Quotient.mem_orbit.mpr rfl⟩⟩ :=
  (rfl)
@[simp] theorem snd_val_totalSpaceEquiv_symm (p : MilnorTotalSpace G) :
    ((totalSpaceEquiv G).symm p).snd.val = p := (rfl)
theorem mk'_comp_totalSpaceEquiv (x : TotalSpace G (MilnorBundleFiber G)) :
    (Quotient.mk'' (totalSpaceEquiv G x) : MilnorClassifyingSpace G) = x.proj :=
  MulAction.orbitRel.Quotient.mem_orbit.mp x.snd.property

end Group

section Topology

variable (G : Type u) [Group G] [TopologicalSpace G]

instance instTopologicalSpaceTotalSpace :
    TopologicalSpace (TotalSpace G (MilnorBundleFiber G)) :=
  .induced (totalSpaceEquiv G) inferInstance

/-- Homeomorphism identifying `TotalSpace G (MilnorBundleFiber G)` with `MilnorTotalSpace G`. -/
@[expose] def totalSpaceHomeomorph : TotalSpace G (MilnorBundleFiber G) ≃ₜ MilnorTotalSpace G :=
  (totalSpaceEquiv G).toHomeomorphOfIsInducing ⟨rfl⟩

@[simp] theorem coe_totalSpaceHomeomorph : ⇑(totalSpaceHomeomorph G) = totalSpaceEquiv G := (rfl)
@[simp] theorem coe_totalSpaceHomeomorph_symm :
    ⇑(totalSpaceHomeomorph G).symm = (totalSpaceEquiv G).symm := (rfl)

theorem continuous_proj : Continuous (π G (MilnorBundleFiber G)) := by
  have heq : π G (MilnorBundleFiber G) = Quotient.mk'' ∘ totalSpaceHomeomorph G :=
    funext fun x ↦ (mk'_comp_totalSpaceEquiv x).symm
  exact heq ▸ (continuous_quotient_mk' (s := MulAction.orbitRel Gᵐᵒᵖ (MilnorTotalSpace G))).comp
    (totalSpaceHomeomorph G).continuous

end Topology

end MilnorBundleFiber

section Charts

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Principal `G`-bundle trivialization of `MilnorBundleFiber G` over `baseCoordSet G i`, sending
`p` to `(p.proj, label i p.2.val)` with inverse `(b, g) ↦ s_i(b) · g`. -/
def milnorTrivialization (i : ℕ) : Trivialization G (π G (MilnorBundleFiber G)) where
  toFun p := (p.proj, MilnorTotalSpace.label i p.snd.val)
  invFun x := (MilnorBundleFiber.totalSpaceEquiv G).symm
    (op x.2 • MilnorClassifyingSpace.localSectionAux G i x.1)
  source := π G (MilnorBundleFiber G) ⁻¹' MilnorClassifyingSpace.baseCoordSet G i
  target := MilnorClassifyingSpace.baseCoordSet G i ×ˢ univ
  map_source' _ hp := ⟨hp, mem_univ _⟩
  map_target' x hx := by
    have hproj :
        (Quotient.mk'' (op x.2 • MilnorClassifyingSpace.localSectionAux G i x.1) :
            MilnorClassifyingSpace G) = x.1 :=
      (MulAction.orbitRel.Quotient.quotient_smul_eq (g := op x.2)
        (a := MilnorClassifyingSpace.localSectionAux G i x.1)).trans
        (MilnorClassifyingSpace.mk'_localSectionAux hx.1)
    simpa only [mem_preimage, MilnorBundleFiber.totalSpaceEquiv_symm_apply, hproj] using hx.1
  left_inv' := fun p hp ↦ (MilnorBundleFiber.totalSpaceEquiv G).injective <| by
    have hp_proj : (Quotient.mk'' p.snd.val : MilnorClassifyingSpace G) = p.proj :=
      MulAction.orbitRel.Quotient.mem_orbit.mp p.snd.property
    have hq : p.snd.val ∈ MilnorTotalSpace.coordSet G i :=
      MilnorClassifyingSpace.mk'_mem_baseCoordSet_iff.mp (hp_proj.symm ▸ hp)
    have hsec : MilnorClassifyingSpace.localSectionAux G i p.proj =
        MilnorClassifyingSpace.normalize G i p.snd.val :=
      (congrArg (MilnorClassifyingSpace.localSectionAux G i) hp_proj).symm.trans
        (MilnorClassifyingSpace.localSectionAux_mk' i p.snd.val)
    dsimp only
    rw [Equiv.apply_symm_apply, hsec, MilnorClassifyingSpace.smul_normalize hq,
      MilnorBundleFiber.totalSpaceEquiv_apply]
  right_inv' := fun ⟨b, g⟩ hx ↦ Prod.ext
    (by simp only [MilnorBundleFiber.totalSpaceEquiv_symm_apply]
        exact (MulAction.orbitRel.Quotient.quotient_smul_eq (g := op g)
          (a := MilnorClassifyingSpace.localSectionAux G i b)).trans
          (MilnorClassifyingSpace.mk'_localSectionAux hx.1))
    (by dsimp only
        rw [MilnorBundleFiber.snd_val_totalSpaceEquiv_symm,
          MilnorTotalSpace.label_op_smul g
            (MilnorClassifyingSpace.localSectionAux_mem_coordSet hx.1),
          MilnorClassifyingSpace.label_localSectionAux hx.1, one_mul])
  open_source := (MilnorClassifyingSpace.isOpen_baseCoordSet G i).preimage
    (MilnorBundleFiber.continuous_proj G)
  open_target := (MilnorClassifyingSpace.isOpen_baseCoordSet G i).prod isOpen_univ
  continuousOn_toFun :=
    (MilnorBundleFiber.continuous_proj G).continuousOn.prodMk <|
      (MilnorTotalSpace.continuousOn_label i).comp
        (MilnorBundleFiber.totalSpaceHomeomorph G).continuous.continuousOn fun p hp ↦
          MilnorClassifyingSpace.mk'_mem_baseCoordSet_iff.mp <| by
            have hp_proj : (Quotient.mk'' p.snd.val : MilnorClassifyingSpace G) = p.proj :=
              MulAction.orbitRel.Quotient.mem_orbit.mp p.snd.property
            rwa [hp_proj]
  continuousOn_invFun :=
    (MilnorBundleFiber.totalSpaceHomeomorph G).symm.continuous.comp_continuousOn <|
      (continuous_op.comp continuous_snd).continuousOn.smul
        ((MilnorClassifyingSpace.continuousOn_localSectionAux G i).comp
          continuous_fst.continuousOn fun _ hx ↦ hx.1)
  baseSet := MilnorClassifyingSpace.baseCoordSet G i
  open_baseSet := MilnorClassifyingSpace.isOpen_baseCoordSet G i
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

@[simp] theorem baseSet_milnorTrivialization (i : ℕ) :
    (milnorTrivialization G i).baseSet = MilnorClassifyingSpace.baseCoordSet G i := (rfl)
@[simp] theorem milnorTrivialization_apply (i : ℕ) (p : TotalSpace G (MilnorBundleFiber G)) :
    milnorTrivialization G i p = (p.proj, MilnorTotalSpace.label i p.snd.val) := (rfl)

variable {G} in
@[simp] theorem milnorTrivialization_symm_apply {i : ℕ} {b : MilnorClassifyingSpace G}
    (hb : b ∈ MilnorClassifyingSpace.baseCoordSet G i) (g : G) :
    (milnorTrivialization G i).toOpenPartialHomeomorph.symm (b, g) =
      (MilnorBundleFiber.totalSpaceEquiv G).symm
        (op g • MilnorClassifyingSpace.localSection G i ⟨b, hb⟩) := (rfl)

instance isEquivariant_milnorTrivialization (i : ℕ) :
    (milnorTrivialization G i).IsEquivariant where
  snd_apply_smul _ hb p g := MilnorTotalSpace.label_op_smul g
    (MilnorClassifyingSpace.mk'_mem_baseCoordSet_iff.mp <| by
      have hp : (Quotient.mk'' p.val : MilnorClassifyingSpace G) = _ :=
        MulAction.orbitRel.Quotient.mem_orbit.mp p.property
      rwa [hp])

/-- **Noncommutative transition cocycle of Milnor's principal bundle charts.** -/
theorem coordChange_milnorTrivialization {i j : ℕ} {p : MilnorTotalSpace G}
    (hpi : p ∈ MilnorTotalSpace.coordSet G i) (hpj : p ∈ MilnorTotalSpace.coordSet G j) (g : G) :
    (milnorTrivialization G i).coordChange (milnorTrivialization G j)
      (Quotient.mk'' p) g =
      MilnorTotalSpace.label j p * (MilnorTotalSpace.label i p)⁻¹ * g := by
  rw [Trivialization.coordChange,
    milnorTrivialization_symm_apply (MilnorClassifyingSpace.mk'_mem_baseCoordSet_iff.mpr hpi),
    milnorTrivialization_apply, MilnorBundleFiber.snd_val_totalSpaceEquiv_symm,
    MilnorClassifyingSpace.localSection_mk' hpi, _root_.op_smul_op_smul,
    MilnorTotalSpace.label_op_smul _ hpj, mul_assoc]

instance instFiberBundleMilnorBundleFiber : FiberBundle G (MilnorBundleFiber G) where
  totalSpaceMk_isInducing' _ :=
    (MilnorBundleFiber.totalSpaceHomeomorph G).isInducing.of_comp_iff.mp IsInducing.subtypeVal
  trivializationAtlas' := range (milnorTrivialization G)
  trivializationAt' b := milnorTrivialization G
    (MilnorClassifyingSpace.exists_mem_baseCoordSet b).choose
  mem_baseSet_trivializationAt' b := by
    rw [baseSet_milnorTrivialization]
    exact (MilnorClassifyingSpace.exists_mem_baseCoordSet b).choose_spec
  trivialization_mem_atlas' _ := ⟨_, rfl⟩

instance memTrivializationAtlas_milnorTrivialization (i : ℕ) :
    MemTrivializationAtlas (milnorTrivialization G i) := ⟨⟨i, rfl⟩⟩

instance instPrincipalBundleMilnorBundleFiber : PrincipalBundle G (MilnorBundleFiber G) where
  isEquivariant_trivialization' _ ht := by obtain ⟨_, rfl⟩ := ht.out; infer_instance

theorem MilnorBundleFiber.division_eq {i : ℕ} {b : MilnorClassifyingSpace G}
    (hb : b ∈ MilnorClassifyingSpace.baseCoordSet G i) (p q : MilnorBundleFiber G b) :
    PrincipalBundle.division G p q =
      (MilnorTotalSpace.label i p.val)⁻¹ * MilnorTotalSpace.label i q.val :=
  PrincipalBundle.division_eq_of_mem_baseSet (e := milnorTrivialization G i) hb p q

end Charts

end PrincipalBundle

/-! ### Comparison from the weak simplicial classifying space and functoriality -/

section Comparison

/-- Continuous comparison map `classifyingSpace G → MilnorClassifyingSpace G` induced by
`weakToMilnorTotalSpace G`. -/
def weakToMilnorClassifyingSpace (G : Type u) [Group G] [TopologicalSpace G] :
    C(classifyingSpace G, MilnorClassifyingSpace G) :=
  classifyingSpaceLift
    ⟨Quotient.mk'' ∘ weakToMilnorTotalSpace G,
      continuous_quotient_mk'.comp (weakToMilnorTotalSpace G).continuous⟩
    fun g x ↦ by
      rw [ContinuousMap.coe_mk, Function.comp_apply, weakToMilnorTotalSpace_smul]
      exact MulAction.orbitRel.Quotient.quotient_smul_eq

@[simp] theorem weakToMilnorClassifyingSpace_mk' {G : Type u} [Group G] [TopologicalSpace G]
    (x : universalGSpace G) :
    weakToMilnorClassifyingSpace G (classifyingSpaceProj G x) =
      Quotient.mk'' (weakToMilnorTotalSpace G x) :=
  classifyingSpaceLift_apply _ _ x

@[simp] theorem weakToMilnorClassifyingSpace_basepoint (G : Type u) [Group G] [TopologicalSpace G] :
    weakToMilnorClassifyingSpace G (classifyingSpaceBasepoint G) =
      milnorClassifyingSpaceBasepoint G := by
  rw [← classifyingSpaceProj_universalGSpaceBasepoint, weakToMilnorClassifyingSpace_mk',
    weakToMilnorTotalSpace_basepoint]
  rfl

end Comparison

end TauCeti

namespace MonoidHom

open TauCeti MulOpposite

variable {G : Type u} {H : Type v} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]

private def milnorTotalSpaceMulActionHom (φ : G →* H) (hφ : Continuous φ) :
    MilnorTotalSpace G →ₑ[fun g : Gᵐᵒᵖ ↦ MulOpposite.op (φ g.unop)] MilnorTotalSpace H where
  toFun := φ.milnorTotalSpaceMap hφ
  map_smul' g p := by simpa using milnorTotalSpaceMap_op_smul φ hφ g.unop p

private theorem milnorTotalSpaceMulActionHom_apply (φ : G →* H) (hφ : Continuous φ)
    (p : MilnorTotalSpace G) :
    φ.milnorTotalSpaceMulActionHom hφ p = φ.milnorTotalSpaceMap hφ p :=
  rfl

/-- A continuous group homomorphism `φ : G →* H` induces a continuous map
`MilnorClassifyingSpace G → MilnorClassifyingSpace H`. -/
def milnorClassifyingSpaceMap (φ : G →* H) (hφ : Continuous φ) :
    C(MilnorClassifyingSpace G, MilnorClassifyingSpace H) where
  toFun := (φ.milnorTotalSpaceMulActionHom hφ).orbitRelQuotientMap
  continuous_toFun := by
    have hq : IsQuotientMap (Quotient.mk (MulAction.orbitRel Gᵐᵒᵖ (MilnorTotalSpace G))) :=
      isQuotientMap_quot_mk
    rw [hq.continuous_iff, MulActionHom.orbitRelQuotientMap_comp_mk]
    exact continuous_quot_mk.comp (φ.milnorTotalSpaceMap hφ).continuous

@[simp] theorem milnorClassifyingSpaceMap_mk' (φ : G →* H) (hφ : Continuous φ)
    (p : MilnorTotalSpace G) :
    φ.milnorClassifyingSpaceMap hφ (Quotient.mk'' p) =
      Quotient.mk'' (φ.milnorTotalSpaceMap hφ p) :=
  (φ.milnorTotalSpaceMulActionHom hφ).orbitRelQuotientMap_mk p
@[simp] theorem milnorClassifyingSpaceMap_basepoint (φ : G →* H) (hφ : Continuous φ) :
    φ.milnorClassifyingSpaceMap hφ (milnorClassifyingSpaceBasepoint G) =
      milnorClassifyingSpaceBasepoint H := by
  rw [milnorClassifyingSpaceBasepoint, milnorClassifyingSpaceMap_mk', milnorTotalSpaceMap_basepoint]
  rfl
@[simp] theorem milnorClassifyingSpaceMap_id :
    (MonoidHom.id G).milnorClassifyingSpaceMap continuous_id =
      ContinuousMap.id (MilnorClassifyingSpace G) :=
  ContinuousMap.coe_injective <| by
    have h : (MonoidHom.id G).milnorTotalSpaceMulActionHom continuous_id =
        MulActionHom.id Gᵐᵒᵖ :=
      MulActionHom.ext fun p ↦ by
        rw [milnorTotalSpaceMulActionHom_apply, milnorTotalSpaceMap_id]; rfl
    exact (congrArg MulActionHom.orbitRelQuotientMap h).trans MulActionHom.orbitRelQuotientMap_id
@[simp] theorem milnorClassifyingSpaceMap_comp {K : Type w} [Group K] [TopologicalSpace K]
    (ψ : H →* K) (hψ : Continuous ψ) (φ : G →* H) (hφ : Continuous φ) :
    (ψ.comp φ).milnorClassifyingSpaceMap (hψ.comp hφ) =
      (ψ.milnorClassifyingSpaceMap hψ).comp (φ.milnorClassifyingSpaceMap hφ) :=
  ContinuousMap.coe_injective <| by
    let : _root_.CompTriple (fun g : Gᵐᵒᵖ ↦ MulOpposite.op (φ g.unop))
        (fun h : Hᵐᵒᵖ ↦ MulOpposite.op (ψ h.unop))
        (fun g : Gᵐᵒᵖ ↦ MulOpposite.op ((ψ.comp φ) g.unop)) := ⟨rfl⟩
    have h : (ψ.comp φ).milnorTotalSpaceMulActionHom (hψ.comp hφ) =
        (ψ.milnorTotalSpaceMulActionHom hψ).comp (φ.milnorTotalSpaceMulActionHom hφ) :=
      MulActionHom.ext fun p ↦ by
        rw [MulActionHom.comp_apply, milnorTotalSpaceMulActionHom_apply,
          milnorTotalSpaceMulActionHom_apply, milnorTotalSpaceMulActionHom_apply,
          milnorTotalSpaceMap_comp, ContinuousMap.comp_apply]
    exact (congrArg MulActionHom.orbitRelQuotientMap h).trans
      (MulActionHom.orbitRelQuotientMap_comp _ _)

end MonoidHom
