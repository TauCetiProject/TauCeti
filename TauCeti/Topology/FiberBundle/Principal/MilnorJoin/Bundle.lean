/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.FiberBundle.Principal.Basic
public import TauCeti.Topology.FiberBundle.Principal.MilnorJoin.Basic
public import TauCeti.Topology.PartitionOfUnity.Shrink
import Mathlib.Topology.LocalAtTarget
import TauCeti.Topology.Algebra.GroupAction.Quotient

/-!
# The strong-topology Milnor numerable principal bundle

For a topological group `G`, this file defines the base space `TauCeti.MilnorClassifyingSpace G`
as the orbit quotient of `TauCeti.MilnorTotalSpace G` by the free right `G`-action
(`MulAction Gᵐᵒᵖ`), and constructs the numerable principal `G`-bundle `TauCeti.MilnorBundleFiber G`
over a partition-of-unity-subordinate coordinate cover (whose total space is weakly contractible).

Specifically, this module constructs Milnor's numerable partition of unity
`TauCeti.milnorPartitionOfUnity` subordinate to the coordinate cover
`MilnorClassifyingSpace.baseCoordSet G`, equips the projection with normalized local sections
and principal `G`-bundle charts `TauCeti.milnorTrivialization G i` forming the bundle atlas,
computes the transition cocycle and division element, and establishes path-connectedness and
Hausdorffness (for a Hausdorff topological group `G`, i.e. `[IsTopologicalGroup G] [T2Space G]`)
of the base space.

## Main definitions and results

* `TauCeti.MilnorClassifyingSpace`, `TauCeti.milnorClassifyingSpaceProj`,
  `milnorClassifyingSpaceBasepoint`, `instPathConnectedSpaceMilnorClassifyingSpace`,
  `isOpenQuotientMap_milnorClassifyingSpaceProj`: orbit quotient of `MilnorTotalSpace G`.
* `TauCeti.MilnorClassifyingSpace.baseWeight`, `baseCoordSet`, `maxBaseWeight`,
  `TauCeti.milnorPartitionOfUnity`, `milnorPartitionOfUnity_apply`,
  `milnorPartitionOfUnity_pos_iff`, `isSubordinate_milnorPartitionOfUnity`: descended weights `t_i`,
  open cover `V_i`, continuous supremum `m = ⨆ i, t_i`, and subordinate partition of unity.
* `TauCeti.MilnorClassifyingSpace.localSection`, `TauCeti.MilnorBundleFiber`,
  `TauCeti.milnorTrivialization`, `coordChange_milnorTrivialization`,
  `instPrincipalBundleMilnorBundleFiber`, `MilnorBundleFiber.division_eq`,
  `instT2SpaceMilnorClassifyingSpace`, `ContinuousMonoidHom.milnorClassifyingSpaceMap`:
  atlas of principal `G`-bundle trivializations, Hausdorff base space, and group-homomorphism
  functoriality.

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

/-- The orbit projection from `MilnorTotalSpace G` to `MilnorClassifyingSpace G`. -/
def milnorClassifyingSpaceProj : MilnorTotalSpace G → MilnorClassifyingSpace G :=
  Quotient.mk''

/-- `milnorClassifyingSpaceProj G` is the orbit quotient map `Quotient.mk''`. -/
theorem milnorClassifyingSpaceProj_def {G : Type u} [Group G] (p : MilnorTotalSpace G) :
    milnorClassifyingSpaceProj G p = Quotient.mk'' p :=
  (rfl)

/-- The distinguished base point of `MilnorClassifyingSpace G`. -/
def milnorClassifyingSpaceBasepoint : MilnorClassifyingSpace G :=
  milnorClassifyingSpaceProj G (MilnorTotalSpace.basepoint G)

/-- The base point of `MilnorClassifyingSpace G` is the orbit of
`MilnorTotalSpace.basepoint G`. -/
@[simp] theorem milnorClassifyingSpaceProj_basepoint :
    milnorClassifyingSpaceProj G (MilnorTotalSpace.basepoint G) =
      milnorClassifyingSpaceBasepoint G :=
  (rfl)

instance instInhabitedMilnorClassifyingSpace : Inhabited (MilnorClassifyingSpace G) :=
  ⟨milnorClassifyingSpaceBasepoint G⟩

/-- The orbit projection `milnorClassifyingSpaceProj G` is an open quotient map. -/
theorem isOpenQuotientMap_milnorClassifyingSpaceProj [TopologicalSpace G] [ContinuousMul G] :
    IsOpenQuotientMap (milnorClassifyingSpaceProj G) :=
  MulAction.isOpenQuotientMap_quotientMk

/-- The orbit projection `milnorClassifyingSpaceProj G` is a quotient map. -/
theorem isQuotientMap_milnorClassifyingSpaceProj [TopologicalSpace G] :
    IsQuotientMap (milnorClassifyingSpaceProj G) :=
  isQuotientMap_quotient_mk'

/-- The orbit projection `milnorClassifyingSpaceProj G` is continuous. -/
@[fun_prop, continuity]
theorem continuous_milnorClassifyingSpaceProj [TopologicalSpace G] :
    Continuous (milnorClassifyingSpaceProj G) :=
  (isQuotientMap_milnorClassifyingSpaceProj G).continuous

/-- Every point of `MilnorClassifyingSpace G` is the orbit of a point of `MilnorTotalSpace G`. -/
theorem milnorClassifyingSpaceProj_surjective :
    Function.Surjective (milnorClassifyingSpaceProj G) :=
  Quotient.mk_surjective

/-- Two points of `MilnorTotalSpace G` have the same image in `MilnorClassifyingSpace G` iff they
lie in the same `Gᵐᵒᵖ`-orbit. -/
theorem milnorClassifyingSpaceProj_eq_iff {G : Type u} [Group G] {p q : MilnorTotalSpace G} :
    milnorClassifyingSpaceProj G p = milnorClassifyingSpaceProj G q ↔
      p ∈ MulAction.orbit Gᵐᵒᵖ q :=
  Quotient.eq''.trans MulAction.orbitRel_apply

/-- Right translation does not change the image in `MilnorClassifyingSpace G`. -/
@[simp] theorem milnorClassifyingSpaceProj_smul {G : Type u} [Group G] (g : Gᵐᵒᵖ)
    (p : MilnorTotalSpace G) :
    milnorClassifyingSpaceProj G (g • p) = milnorClassifyingSpaceProj G p :=
  milnorClassifyingSpaceProj_eq_iff.mpr (MulAction.mem_orbit p g)

/-- `MilnorClassifyingSpace G` is path-connected as the quotient of the path-connected space
`MilnorTotalSpace G`. -/
instance instPathConnectedSpaceMilnorClassifyingSpace [TopologicalSpace G] :
    PathConnectedSpace (MilnorClassifyingSpace G) :=
  (milnorClassifyingSpaceProj_surjective G).pathConnectedSpace
    (continuous_milnorClassifyingSpaceProj G)

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

@[simp] theorem baseWeight_proj (i : ℕ) (p : MilnorTotalSpace G) :
    baseWeight G i (milnorClassifyingSpaceProj G p) = MilnorTotalSpace.weight i p :=
  MulAction.orbitRelQuotientLift_mk p

/-- The `i`-th coordinate open set `V_i = {b | 0 < t_i(b)}` in `MilnorClassifyingSpace G`. -/
def baseCoordSet (i : ℕ) : Set (MilnorClassifyingSpace G) := {b | 0 < baseWeight G i b}

variable {G}

@[simp] theorem mem_baseCoordSet_iff {i : ℕ} {b : MilnorClassifyingSpace G} :
    b ∈ baseCoordSet G i ↔ 0 < baseWeight G i b := Iff.rfl
theorem proj_mem_baseCoordSet_iff {i : ℕ} {p : MilnorTotalSpace G} :
    milnorClassifyingSpaceProj G p ∈ baseCoordSet G i ↔ p ∈ MilnorTotalSpace.coordSet G i := by
  simp [mem_baseCoordSet_iff]
@[simp] theorem preimage_baseCoordSet (G : Type u) [Group G] [TopologicalSpace G] (i : ℕ) :
    milnorClassifyingSpaceProj G ⁻¹' baseCoordSet G i = MilnorTotalSpace.coordSet G i := by
  ext; simp
theorem image_coordSet_eq_baseCoordSet (G : Type u) [Group G] [TopologicalSpace G] (i : ℕ) :
    milnorClassifyingSpaceProj G '' MilnorTotalSpace.coordSet G i = baseCoordSet G i := by
  rw [← preimage_baseCoordSet, (milnorClassifyingSpaceProj_surjective G).image_preimage]
theorem isOpen_baseCoordSet (G : Type u) [Group G] [TopologicalSpace G] (i : ℕ) :
    IsOpen (baseCoordSet G i) := isOpen_lt continuous_const (baseWeight G i).continuous

theorem baseWeight_nonneg (i : ℕ) (b : MilnorClassifyingSpace G) : 0 ≤ baseWeight G i b := by
  obtain ⟨p, rfl⟩ := milnorClassifyingSpaceProj_surjective G b
  simpa using MilnorTotalSpace.weight_nonneg i p
theorem baseWeight_le_one (i : ℕ) (b : MilnorClassifyingSpace G) : baseWeight G i b ≤ 1 := by
  obtain ⟨p, rfl⟩ := milnorClassifyingSpaceProj_surjective G b
  simpa using MilnorTotalSpace.weight_le_one i p
theorem finite_support_baseWeight (b : MilnorClassifyingSpace G) :
    (support fun i ↦ baseWeight G i b).Finite := by
  obtain ⟨p, rfl⟩ := milnorClassifyingSpaceProj_surjective G b
  simpa using MilnorTotalSpace.finite_support_weight p
theorem hasSum_baseWeight (b : MilnorClassifyingSpace G) : HasSum (fun i ↦ baseWeight G i b) 1 := by
  obtain ⟨p, rfl⟩ := milnorClassifyingSpaceProj_surjective G b
  simpa using MilnorTotalSpace.hasSum_weight p
@[simp] theorem tsum_baseWeight (b : MilnorClassifyingSpace G) : ∑' i, baseWeight G i b = 1 :=
  (hasSum_baseWeight b).tsum_eq
theorem exists_mem_baseCoordSet (b : MilnorClassifyingSpace G) : ∃ i, b ∈ baseCoordSet G i := by
  obtain ⟨p, rfl⟩ := milnorClassifyingSpaceProj_surjective G b
  simpa [mem_baseCoordSet_iff] using MilnorTotalSpace.exists_weight_pos p
@[simp] theorem iUnion_baseCoordSet (G : Type u) [Group G] [TopologicalSpace G] :
    ⋃ i, baseCoordSet G i = univ :=
  eq_univ_of_forall fun b ↦ mem_iUnion.mpr (exists_mem_baseCoordSet b)

/-- Pointwise maximum weight `m(b) = ⨆ i, baseWeight G i b` as a continuous function. -/
def maxBaseWeight (G : Type u) [Group G] [TopologicalSpace G] : C(MilnorClassifyingSpace G, ℝ) :=
  ⟨fun b ↦ ⨆ i : ℕ, baseWeight G i b,
    continuous_ciSup_of_hasSum_one (baseWeight G)
      (fun i b ↦ baseWeight_nonneg i b) hasSum_baseWeight⟩

@[simp] theorem maxBaseWeight_apply (b : MilnorClassifyingSpace G) :
    maxBaseWeight G b = ⨆ i : ℕ, baseWeight G i b := (rfl)
theorem le_maxBaseWeight (i : ℕ) (b : MilnorClassifyingSpace G) :
    baseWeight G i b ≤ maxBaseWeight G b :=
  le_ciSup ⟨1, forall_mem_range.2 fun j ↦ baseWeight_le_one j b⟩ i
theorem maxBaseWeight_pos (b : MilnorClassifyingSpace G) : 0 < maxBaseWeight G b :=
  let ⟨i₀, hi₀⟩ := exists_mem_baseCoordSet b
  hi₀.trans_le (le_maxBaseWeight i₀ b)

end BaseWeights

end MilnorClassifyingSpace

/-- **Milnor's subordinate partition of unity** on `MilnorClassifyingSpace G`. -/
def milnorPartitionOfUnity (G : Type u) [Group G] [TopologicalSpace G] :
    PartitionOfUnity ℕ (MilnorClassifyingSpace G) :=
  PartitionOfUnity.shrinkOfThreshold (MilnorClassifyingSpace.baseWeight G)
    (MilnorClassifyingSpace.maxBaseWeight G)
    (locallyFinite_support_halfThresholdTrunc_of_hasSum_one
      (MilnorClassifyingSpace.baseWeight G)
      (fun i b ↦ MilnorClassifyingSpace.baseWeight_nonneg i b)
      MilnorClassifyingSpace.hasSum_baseWeight
      MilnorClassifyingSpace.maxBaseWeight_apply)
    fun b ↦ exists_lt_of_lt_ciSup (half_lt_self (MilnorClassifyingSpace.maxBaseWeight_pos b))

/-- Pointwise formula for the `i`-th weight of `milnorPartitionOfUnity G` at `b`. -/
theorem milnorPartitionOfUnity_apply (G : Type u) [Group G] [TopologicalSpace G]
    (i : ℕ) (b : MilnorClassifyingSpace G) :
    milnorPartitionOfUnity G i b =
      max 0 (MilnorClassifyingSpace.baseWeight G i b -
        MilnorClassifyingSpace.maxBaseWeight G b / 2) /
        ∑ᶠ k, max 0 (MilnorClassifyingSpace.baseWeight G k b -
          MilnorClassifyingSpace.maxBaseWeight G b / 2) :=
  PartitionOfUnity.shrinkOfThreshold_apply _ _ _ _ i b

/-- The `i`-th weight of `milnorPartitionOfUnity G` is positive at `b` iff
`maxBaseWeight G b / 2 < baseWeight G i b`. -/
@[simp] theorem milnorPartitionOfUnity_pos_iff (G : Type u) [Group G] [TopologicalSpace G]
    {i : ℕ} {b : MilnorClassifyingSpace G} :
    0 < milnorPartitionOfUnity G i b ↔
      MilnorClassifyingSpace.maxBaseWeight G b / 2 < MilnorClassifyingSpace.baseWeight G i b :=
  PartitionOfUnity.shrinkOfThreshold_pos_iff

/-- Milnor's partition of unity on `MilnorClassifyingSpace G` is subordinate to the open cover
`MilnorClassifyingSpace.baseCoordSet G` of positive-weight coordinate sets. -/
theorem isSubordinate_milnorPartitionOfUnity (G : Type u) [Group G] [TopologicalSpace G] :
    (milnorPartitionOfUnity G).IsSubordinate (MilnorClassifyingSpace.baseCoordSet G) :=
  PartitionOfUnity.isSubordinate_shrinkOfThreshold MilnorClassifyingSpace.maxBaseWeight_pos
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

private theorem localSectionAux_proj {G : Type u} [Group G] (i : ℕ) (p : MilnorTotalSpace G) :
    localSectionAux G i (milnorClassifyingSpaceProj G p) = normalize G i p :=
  MulAction.orbitRelQuotientLift_mk p

variable {G : Type u} [Group G] [TopologicalSpace G]

private theorem proj_localSectionAux {i : ℕ} {b : MilnorClassifyingSpace G}
    (hb : b ∈ baseCoordSet G i) :
    milnorClassifyingSpaceProj G (localSectionAux G i b) = b := by
  obtain ⟨p, rfl⟩ := milnorClassifyingSpaceProj_surjective G b
  rw [localSectionAux_proj, normalize_of_mem (proj_mem_baseCoordSet_iff.mp hb)]
  exact milnorClassifyingSpaceProj_smul _ p

private theorem localSectionAux_mem_coordSet {i : ℕ} {b : MilnorClassifyingSpace G}
    (hb : b ∈ baseCoordSet G i) : localSectionAux G i b ∈ MilnorTotalSpace.coordSet G i := by
  rwa [← proj_mem_baseCoordSet_iff, proj_localSectionAux hb]

private theorem weight_localSectionAux (j : ℕ) {i : ℕ} {b : MilnorClassifyingSpace G}
    (hb : b ∈ baseCoordSet G i) :
    MilnorTotalSpace.weight j (localSectionAux G i b) = baseWeight G j b := by
  rw [← baseWeight_proj G j, proj_localSectionAux hb]

private theorem label_localSectionAux {i : ℕ} {b : MilnorClassifyingSpace G}
    (hb : b ∈ baseCoordSet G i) : MilnorTotalSpace.label i (localSectionAux G i b) = 1 := by
  obtain ⟨p, rfl⟩ := milnorClassifyingSpaceProj_surjective G b
  rw [localSectionAux_proj]
  exact label_normalize (proj_mem_baseCoordSet_iff.mp hb)

private theorem continuousOn_localSectionAux (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (i : ℕ) :
    ContinuousOn (localSectionAux G i) (baseCoordSet G i) := by
  rw [continuousOn_iff_continuous_domRestrict,
    ((isOpenQuotientMap_milnorClassifyingSpaceProj G).restrictPreimage
      (baseCoordSet G i)).isQuotientMap.continuous_iff]
  have hnorm : ContinuousOn (normalize G i)
      (milnorClassifyingSpaceProj G ⁻¹' baseCoordSet G i) := by
    rw [preimage_baseCoordSet]
    exact (((continuous_op.comp continuous_inv).continuousOn.comp
      (MilnorTotalSpace.continuousOn_label i) (mapsTo_univ _ _)).smul continuousOn_id).congr
      fun _ hp ↦ normalize_of_mem hp
  exact (continuousOn_iff_continuous_domRestrict.mp hnorm).congr fun p ↦
    (localSectionAux_proj i p.val).symm

/-- Local section `s_i : V_i → MilnorTotalSpace G` normalized by `label i (s_i b) = 1`. -/
def localSection (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (i : ℕ) :
    C(baseCoordSet G i, MilnorTotalSpace G) :=
  ⟨(baseCoordSet G i).domRestrict (localSectionAux G i),
    continuousOn_iff_continuous_domRestrict.mp (continuousOn_localSectionAux G i)⟩

@[simp] theorem proj_localSection [IsTopologicalGroup G] (i : ℕ) (b : baseCoordSet G i) :
    milnorClassifyingSpaceProj G (localSection G i b) = b.val :=
  proj_localSectionAux b.property
theorem localSection_mem_coordSet [IsTopologicalGroup G] (i : ℕ) (b : baseCoordSet G i) :
    localSection G i b ∈ MilnorTotalSpace.coordSet G i := localSectionAux_mem_coordSet b.property
@[simp] theorem weight_localSection [IsTopologicalGroup G] (j i : ℕ) (b : baseCoordSet G i) :
    MilnorTotalSpace.weight j (localSection G i b) = baseWeight G j b.val :=
  weight_localSectionAux j b.property
@[simp] theorem label_localSection [IsTopologicalGroup G] (i : ℕ) (b : baseCoordSet G i) :
    MilnorTotalSpace.label i (localSection G i b) = 1 := label_localSectionAux b.property
@[simp] theorem localSection_proj [IsTopologicalGroup G] {i : ℕ} {p : MilnorTotalSpace G}
    (hp : p ∈ MilnorTotalSpace.coordSet G i) :
    localSection G i ⟨milnorClassifyingSpaceProj G p, proj_mem_baseCoordSet_iff.mpr hp⟩ =
      op (MilnorTotalSpace.label i p)⁻¹ • p := by
  simpa [localSection, localSectionAux_proj] using normalize_of_mem hp
theorem smul_localSection_proj [IsTopologicalGroup G] {i : ℕ} {p : MilnorTotalSpace G}
    (hp : p ∈ MilnorTotalSpace.coordSet G i) :
    op (MilnorTotalSpace.label i p) •
      localSection G i ⟨milnorClassifyingSpaceProj G p, proj_mem_baseCoordSet_iff.mpr hp⟩ = p := by
  simpa [localSection, localSectionAux_proj] using smul_normalize hp

end LocalSections

end MilnorClassifyingSpace

/-- `MilnorClassifyingSpace G` is Hausdorff whenever `G` is a Hausdorff topological group
(`[IsTopologicalGroup G] [T2Space G]`). -/
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
        rw [← MilnorClassifyingSpace.proj_localSectionAux hb₁i,
          ← MilnorClassifyingSpace.proj_localSectionAux hb₂i]
        exact congrArg (milnorClassifyingSpaceProj G) h
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

/-- The fibre over `b : MilnorClassifyingSpace G` of Milnor's numerable principal `G`-bundle
(over a partition-of-unity-subordinate cover, with weakly contractible total space), realized as
the orbit `b.orbit` under the free right action of `G`. -/
abbrev MilnorBundleFiber (G : Type u) [Group G] (b : MilnorClassifyingSpace G) : Type u :=
  MulAction.orbitRel.Quotient.orbit (G := Gᵐᵒᵖ) (α := MilnorTotalSpace G) b

namespace MilnorBundleFiber

section Group

variable {G : Type u} [Group G]

instance instNonempty (b : MilnorClassifyingSpace G) : Nonempty (MilnorBundleFiber G b) :=
  (MulAction.orbitRel.Quotient.nonempty_orbit b).to_subtype

/-- Canonical equivalence identifying `TotalSpace G (MilnorBundleFiber G)` with
`MilnorTotalSpace G`. -/
def totalSpaceEquiv (G : Type u) [Group G] :
    TotalSpace G (MilnorBundleFiber G) ≃ MilnorTotalSpace G where
  toFun x := x.snd.val
  invFun p := ⟨milnorClassifyingSpaceProj G p,
    ⟨p, MulAction.orbitRel.Quotient.mem_orbit.mpr (milnorClassifyingSpaceProj_def p).symm⟩⟩
  left_inv := fun ⟨b, ⟨p, hp⟩⟩ ↦ by
    obtain rfl : milnorClassifyingSpaceProj G p = b :=
      (milnorClassifyingSpaceProj_def p).trans (MulAction.orbitRel.Quotient.mem_orbit.mp hp)
    rfl
  right_inv _ := rfl

@[simp] theorem totalSpaceEquiv_apply (x : TotalSpace G (MilnorBundleFiber G)) :
    totalSpaceEquiv G x = x.snd.val := (rfl)
@[simp] theorem totalSpaceEquiv_symm_apply (p : MilnorTotalSpace G) :
    (totalSpaceEquiv G).symm p =
      ⟨milnorClassifyingSpaceProj G p,
        ⟨p, MulAction.orbitRel.Quotient.mem_orbit.mpr (milnorClassifyingSpaceProj_def p).symm⟩⟩ :=
  (rfl)
@[simp] theorem snd_val_totalSpaceEquiv_symm (p : MilnorTotalSpace G) :
    ((totalSpaceEquiv G).symm p).snd.val = p := (rfl)
theorem proj_totalSpaceEquiv_apply (x : TotalSpace G (MilnorBundleFiber G)) :
    milnorClassifyingSpaceProj G (totalSpaceEquiv G x) = x.proj :=
  (milnorClassifyingSpaceProj_def _).trans (MulAction.orbitRel.Quotient.mem_orbit.mp x.snd.property)

end Group

section Topology

variable (G : Type u) [Group G] [TopologicalSpace G]

/-- The topology on `TotalSpace G (MilnorBundleFiber G)` induced along `totalSpaceEquiv G` from
the strong coordinate topology on `MilnorTotalSpace G`. -/
instance instTopologicalSpaceTotalSpace :
    TopologicalSpace (TotalSpace G (MilnorBundleFiber G)) :=
  .induced (totalSpaceEquiv G) inferInstance

/-- Homeomorphism identifying `TotalSpace G (MilnorBundleFiber G)` with `MilnorTotalSpace G`. -/
def totalSpaceHomeomorph : TotalSpace G (MilnorBundleFiber G) ≃ₜ MilnorTotalSpace G :=
  (totalSpaceEquiv G).toHomeomorphOfIsInducing ⟨rfl⟩

@[simp] theorem coe_totalSpaceHomeomorph : ⇑(totalSpaceHomeomorph G) = totalSpaceEquiv G := (rfl)
@[simp] theorem coe_totalSpaceHomeomorph_symm :
    ⇑(totalSpaceHomeomorph G).symm = (totalSpaceEquiv G).symm := (rfl)

/-- Under `totalSpaceHomeomorph G`, the bundle projection `π G (MilnorBundleFiber G)` is the
strong-coordinate orbit quotient `milnorClassifyingSpaceProj G`, and hence is continuous. -/
theorem continuous_proj : Continuous (π G (MilnorBundleFiber G)) := by
  have heq : π G (MilnorBundleFiber G) = milnorClassifyingSpaceProj G ∘ totalSpaceHomeomorph G :=
    funext fun x ↦ (proj_totalSpaceEquiv_apply x).symm
  exact heq ▸ (continuous_milnorClassifyingSpaceProj G).comp (totalSpaceHomeomorph G).continuous

/-- A point in the fibre over `b` lies in the `i`-th total-space coordinate open set iff `b`
lies in `baseCoordSet G i`. -/
theorem val_mem_coordSet_iff {G : Type u} [Group G] [TopologicalSpace G]
    {b : MilnorClassifyingSpace G} (p : MilnorBundleFiber G b) {i : ℕ} :
    p.val ∈ MilnorTotalSpace.coordSet G i ↔ b ∈ MilnorClassifyingSpace.baseCoordSet G i := by
  rw [← MilnorClassifyingSpace.proj_mem_baseCoordSet_iff, milnorClassifyingSpaceProj_def,
    MulAction.orbitRel.Quotient.mem_orbit.mp p.property]

end Topology

end MilnorBundleFiber

section Charts

variable (G : Type u) [Group G] [TopologicalSpace G]

private theorem proj_totalSpaceEquiv_symm_smul_localSectionAux {i : ℕ}
    {b : MilnorClassifyingSpace G} (hb : b ∈ MilnorClassifyingSpace.baseCoordSet G i) (g : G) :
    ((MilnorBundleFiber.totalSpaceEquiv G).symm
        (op g • MilnorClassifyingSpace.localSectionAux G i b)).proj = b := by
  rw [← MilnorBundleFiber.proj_totalSpaceEquiv_apply, Equiv.apply_symm_apply,
    milnorClassifyingSpaceProj_smul]
  exact MilnorClassifyingSpace.proj_localSectionAux hb

variable [IsTopologicalGroup G]

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
    simpa only [mem_preimage, proj_totalSpaceEquiv_symm_smul_localSectionAux G hx.1] using hx.1
  left_inv' := fun p hp ↦ (MilnorBundleFiber.totalSpaceEquiv G).injective <| by
    have hq : p.snd.val ∈ MilnorTotalSpace.coordSet G i :=
      (MilnorBundleFiber.val_mem_coordSet_iff p.snd).mpr hp
    have hsec : MilnorClassifyingSpace.localSectionAux G i p.proj =
        MilnorClassifyingSpace.normalize G i p.snd.val :=
      (congrArg (MilnorClassifyingSpace.localSectionAux G i)
        (MilnorBundleFiber.proj_totalSpaceEquiv_apply p)).symm.trans <| by
        rw [MilnorBundleFiber.totalSpaceEquiv_apply, MilnorClassifyingSpace.localSectionAux_proj]
    dsimp only
    rw [Equiv.apply_symm_apply, hsec, MilnorClassifyingSpace.smul_normalize hq,
      MilnorBundleFiber.totalSpaceEquiv_apply]
  right_inv' := fun ⟨b, g⟩ hx ↦ Prod.ext
    (proj_totalSpaceEquiv_symm_smul_localSectionAux G hx.1 g)
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
          (MilnorBundleFiber.val_mem_coordSet_iff p.snd).mpr hp
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
  snd_apply_smul _ hb p g :=
    MilnorTotalSpace.label_op_smul g ((MilnorBundleFiber.val_mem_coordSet_iff p).mpr hb)

/-- **Noncommutative transition cocycle of Milnor's principal bundle charts.** -/
theorem coordChange_milnorTrivialization {i j : ℕ} {p : MilnorTotalSpace G}
    (hpi : p ∈ MilnorTotalSpace.coordSet G i) (hpj : p ∈ MilnorTotalSpace.coordSet G j) (g : G) :
    (milnorTrivialization G i).coordChange (milnorTrivialization G j)
      (milnorClassifyingSpaceProj G p) g =
      MilnorTotalSpace.label j p * (MilnorTotalSpace.label i p)⁻¹ * g := by
  have hbi : milnorClassifyingSpaceProj G p ∈ (milnorTrivialization G i).baseSet :=
    MilnorClassifyingSpace.proj_mem_baseCoordSet_iff.mpr hpi
  have hbj : milnorClassifyingSpaceProj G p ∈ (milnorTrivialization G j).baseSet :=
    MilnorClassifyingSpace.proj_mem_baseCoordSet_iff.mpr hpj
  let s := MilnorClassifyingSpace.localSection G i ⟨milnorClassifyingSpaceProj G p, hbi⟩
  have hproj : ((MilnorBundleFiber.totalSpaceEquiv G).symm s).proj =
      milnorClassifyingSpaceProj G p :=
    MilnorClassifyingSpace.proj_localSection i ⟨milnorClassifyingSpaceProj G p, hbi⟩
  have hsec := (milnorTrivialization G i).coordChange_apply_snd (milnorTrivialization G j)
    (p := (MilnorBundleFiber.totalSpaceEquiv G).symm s) (hproj ▸ hbi)
  rw [hproj, milnorTrivialization_apply, milnorTrivialization_apply] at hsec
  dsimp only [s] at hsec
  rw [MilnorBundleFiber.snd_val_totalSpaceEquiv_symm, MilnorClassifyingSpace.label_localSection,
    MilnorClassifyingSpace.localSection_proj hpi, MilnorTotalSpace.label_op_smul _ hpj] at hsec
  rw [(milnorTrivialization G i).coordChange_eq_mul (milnorTrivialization G j) hbi hbj g, hsec]

/-- Coordinate-chart `FiberBundle` instance on `MilnorBundleFiber G` whose atlas is generated by
`milnorTrivialization G i` over the cover `MilnorClassifyingSpace.baseCoordSet G`. -/
instance instFiberBundleMilnorBundleFiber : FiberBundle G (MilnorBundleFiber G) where
  totalSpaceMk_isInducing' b := by
    have hcomp : ⇑(MilnorBundleFiber.totalSpaceHomeomorph G) ∘ TotalSpace.mk b = Subtype.val :=
      funext fun x ↦ by simp
    exact (MilnorBundleFiber.totalSpaceHomeomorph G).isInducing.of_comp_iff.mp
      (hcomp ▸ IsInducing.subtypeVal)
  trivializationAtlas' := range (milnorTrivialization G)
  trivializationAt' b := milnorTrivialization G
    (MilnorClassifyingSpace.exists_mem_baseCoordSet b).choose
  mem_baseSet_trivializationAt' b := by
    rw [baseSet_milnorTrivialization]
    exact (MilnorClassifyingSpace.exists_mem_baseCoordSet b).choose_spec
  trivialization_mem_atlas' _ := ⟨_, rfl⟩

/-- Every coordinate trivialization `milnorTrivialization G i` belongs to the bundle atlas of
`MilnorBundleFiber G`. -/
instance memTrivializationAtlas_milnorTrivialization (i : ℕ) :
    MemTrivializationAtlas (milnorTrivialization G i) := ⟨⟨i, rfl⟩⟩

/-- `MilnorBundleFiber G` is a principal `G`-bundle over `MilnorClassifyingSpace G`, equivariant
with respect to the coordinate-chart atlas `milnorTrivialization G`. -/
instance instPrincipalBundleMilnorBundleFiber : PrincipalBundle G (MilnorBundleFiber G) where
  isEquivariant_trivialization' _ ht := by obtain ⟨_, rfl⟩ := ht.out; infer_instance

/-- Explicit chart formula for the principal-bundle division element over `baseCoordSet G i`:
`division p q = (label i p.val)⁻¹ * label i q.val`. -/
theorem MilnorBundleFiber.division_eq {i : ℕ} {b : MilnorClassifyingSpace G}
    (hb : b ∈ MilnorClassifyingSpace.baseCoordSet G i) (p q : MilnorBundleFiber G b) :
    PrincipalBundle.division G p q =
      (MilnorTotalSpace.label i p.val)⁻¹ * MilnorTotalSpace.label i q.val :=
  PrincipalBundle.division_eq_of_mem_baseSet (e := milnorTrivialization G i) hb p q

end Charts

end PrincipalBundle

end TauCeti

/-! ### Functoriality on classifying spaces -/

namespace ContinuousMonoidHom

open TauCeti MulOpposite

variable {G : Type u} {H : Type v} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]

private def milnorTotalSpaceMulActionHom (φ : G →ₜ* H) :
    MilnorTotalSpace G →ₑ[fun g : Gᵐᵒᵖ ↦ MulOpposite.op (φ g.unop)] MilnorTotalSpace H where
  toFun := MilnorTotalSpace.map (φ : C(G, H))
  map_smul' g p := by simpa using MilnorTotalSpace.map_op_smul φ g.unop p

private theorem milnorTotalSpaceMulActionHom_apply (φ : G →ₜ* H) (p : MilnorTotalSpace G) :
    φ.milnorTotalSpaceMulActionHom p = MilnorTotalSpace.map (φ : C(G, H)) p :=
  rfl

/-- A continuous group homomorphism `φ : G →ₜ* H` induces a continuous map
`MilnorClassifyingSpace G → MilnorClassifyingSpace H`. -/
def milnorClassifyingSpaceMap (φ : G →ₜ* H) :
    C(MilnorClassifyingSpace G, MilnorClassifyingSpace H) where
  toFun := φ.milnorTotalSpaceMulActionHom.orbitRelQuotientMap
  continuous_toFun := by
    rw [(isQuotientMap_milnorClassifyingSpaceProj G).continuous_iff]
    have hcomp : φ.milnorTotalSpaceMulActionHom.orbitRelQuotientMap ∘ milnorClassifyingSpaceProj G =
        milnorClassifyingSpaceProj H ∘ MilnorTotalSpace.map (φ : C(G, H)) :=
      funext fun p ↦ φ.milnorTotalSpaceMulActionHom.orbitRelQuotientMap_mk p
    exact hcomp ▸ (continuous_milnorClassifyingSpaceProj H).comp
      (MilnorTotalSpace.map (φ : C(G, H))).continuous

@[simp] theorem milnorClassifyingSpaceMap_proj (φ : G →ₜ* H) (p : MilnorTotalSpace G) :
    φ.milnorClassifyingSpaceMap (milnorClassifyingSpaceProj G p) =
      milnorClassifyingSpaceProj H (MilnorTotalSpace.map (φ : C(G, H)) p) :=
  φ.milnorTotalSpaceMulActionHom.orbitRelQuotientMap_mk p

@[simp] theorem milnorClassifyingSpaceMap_basepoint (φ : G →ₜ* H) :
    φ.milnorClassifyingSpaceMap (milnorClassifyingSpaceBasepoint G) =
      milnorClassifyingSpaceBasepoint H := by
  rw [← milnorClassifyingSpaceProj_basepoint, milnorClassifyingSpaceMap_proj,
    MilnorTotalSpace.map_basepoint, milnorClassifyingSpaceProj_basepoint]

@[simp] theorem milnorClassifyingSpaceMap_id :
    (ContinuousMonoidHom.id G).milnorClassifyingSpaceMap =
      ContinuousMap.id (MilnorClassifyingSpace G) :=
  ContinuousMap.coe_injective <| by
    have h : (ContinuousMonoidHom.id G).milnorTotalSpaceMulActionHom =
        MulActionHom.id Gᵐᵒᵖ :=
      MulActionHom.ext fun p ↦ by
        rw [milnorTotalSpaceMulActionHom_apply]
        exact congrArg (· p) (MilnorTotalSpace.map_id G)
    exact (congrArg MulActionHom.orbitRelQuotientMap h).trans MulActionHom.orbitRelQuotientMap_id

@[simp] theorem milnorClassifyingSpaceMap_comp {K : Type w} [Group K] [TopologicalSpace K]
    (ψ : H →ₜ* K) (φ : G →ₜ* H) :
    (ψ.comp φ).milnorClassifyingSpaceMap =
      ψ.milnorClassifyingSpaceMap.comp φ.milnorClassifyingSpaceMap :=
  ContinuousMap.coe_injective <| by
    let : _root_.CompTriple (fun g : Gᵐᵒᵖ ↦ MulOpposite.op (φ g.unop))
        (fun h : Hᵐᵒᵖ ↦ MulOpposite.op (ψ h.unop))
        (fun g : Gᵐᵒᵖ ↦ MulOpposite.op ((ψ.comp φ) g.unop)) := ⟨rfl⟩
    have h : (ψ.comp φ).milnorTotalSpaceMulActionHom =
        ψ.milnorTotalSpaceMulActionHom.comp φ.milnorTotalSpaceMulActionHom :=
      MulActionHom.ext fun p ↦ by
        rw [MulActionHom.comp_apply, milnorTotalSpaceMulActionHom_apply,
          milnorTotalSpaceMulActionHom_apply, milnorTotalSpaceMulActionHom_apply]
        exact congrArg (· p)
          (MilnorTotalSpace.map_comp (ψ : C(H, K)) (φ : C(G, H)))
    exact (congrArg MulActionHom.orbitRelQuotientMap h).trans
      (MulActionHom.orbitRelQuotientMap_comp _ _)

end ContinuousMonoidHom
