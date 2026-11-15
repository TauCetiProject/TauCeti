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
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.Separation.Hausdorff
import TauCeti.Topology.Order.Lattice

/-!
# The strong-topology Milnor classifying space and universal principal bundle

For a topological group `G`, this file constructs Milnor's strong-coordinate classifying space
`TauCeti.MilnorClassifyingSpace G` as the orbit quotient of `TauCeti.MilnorTotalSpace G` by the free
right action of `G` (`MulAction Gᵐᵒᵖ`), equips the projection with its principal `G`-bundle charts
over the open coordinate cover `V_i = {b | 0 < t_i(b)}`, proves Hausdorffness when `G` is
Hausdorff, and constructs Milnor's numerable partition of unity subordinate to `(V_i)_{i ∈ ℕ}`.

Specifically:
* When multiplication on `G` is continuous, right translation on `MilnorTotalSpace G` is a
  homeomorphism, so the orbit projection `milnorClassifyingSpaceProj G` is an open quotient map
  (`TauCeti.isOpenQuotientMap_milnorClassifyingSpaceProj`).
* Each barycentric weight `weight i` is `G`-invariant and descends to a continuous function
  `TauCeti.MilnorClassifyingSpace.baseWeight G i : C(MilnorClassifyingSpace G, ℝ)`. Even though the
  family `(baseWeight G i)` is only pointwise finite rather than locally finite, its pointwise
  supremum `maxBaseWeight G b = ⨆ i, baseWeight G i b` is positive and continuous by finite-support
  tail control: near `b₀`, the finite support `I` of `baseWeight G · b₀` captures more than
  `1 - m(b₀) / 3` of the total mass `1`, forcing all outside weights below `m(b₀) / 3`. Truncating
  below `m / 2` yields a locally finite positive family `truncatedBaseWeight G i` whose
  normalization (`PartitionOfUnity.ofExistsPos`) is a partition of unity
  `TauCeti.milnorPartitionOfUnity G` with closed supports inside `baseCoordSet G i`
  (`TauCeti.isSubordinate_milnorPartitionOfUnity`).
* When `G` is a topological group (`[IsTopologicalGroup G]`), normalizing the `i`-th vertex label to
  `1` via `p ↦ p · g_i(p)⁻¹` descends along the open quotient restriction `U_i → V_i` to a
  continuous local section `TauCeti.MilnorClassifyingSpace.localSection G i`. Presenting the orbit
  fibres as the bundle family `TauCeti.MilnorBundleFiber G` gives equivariant trivializations
  `TauCeti.milnorTrivialization G i` over `baseCoordSet G i` with noncommutative transition cocycle
  `c_{ij}(pG) = g_j(p) * g_i(p)⁻¹` (`TauCeti.coordChange_milnorTrivialization`), assembling into
  `FiberBundle G (MilnorBundleFiber G)` and `PrincipalBundle G (MilnorBundleFiber G)`.
* When `G` is also Hausdorff (`[T2Space G]`), `MilnorClassifyingSpace G` is Hausdorff
  (`TauCeti.instT2SpaceMilnorClassifyingSpace`), separated either by `baseWeight G i` or on a common
  chart overlap `V_i ∩ V_j` by the continuous normalized-label invariants
  `b ↦ label j (localSection G i b)`.
* Label inversion (`TauCeti.weakToMilnorTotalSpace`) descends to a continuous comparison map
  `TauCeti.weakToMilnorClassifyingSpace : C(classifyingSpace G, MilnorClassifyingSpace G)` from the
  weak simplicial classifying space, and continuous group homomorphisms act functorially on
  `MilnorClassifyingSpace` (`MonoidHom.milnorClassifyingSpaceMap`).

## Main definitions

* `TauCeti.MilnorClassifyingSpace`, `TauCeti.milnorClassifyingSpaceProj`,
  `TauCeti.milnorClassifyingSpaceBasepoint`, `TauCeti.milnorClassifyingSpaceLift`: the strong
  coordinate classifying space, orbit map, base point, and quotient descent.
* `TauCeti.MilnorClassifyingSpace.baseWeight`, `TauCeti.MilnorClassifyingSpace.baseCoordSet`:
  descended weights `t_i` and open coordinate cover `V_i`.
* `TauCeti.milnorPartitionOfUnity`: partition of unity subordinate to `baseCoordSet G`.
* `TauCeti.MilnorBundleFiber`, `TauCeti.milnorTrivialization`: fibre family and principal bundle
  charts of `MilnorTotalSpace G → MilnorClassifyingSpace G`.
* `TauCeti.weakToMilnorClassifyingSpace`, `MonoidHom.milnorClassifyingSpaceMap`: comparison from the
  weak simplicial classifying space and functoriality in continuous group homomorphisms.

## Main results

* `TauCeti.isOpenQuotientMap_milnorClassifyingSpaceProj`: the orbit map is an open quotient map.
* `TauCeti.isSubordinate_milnorPartitionOfUnity`: `milnorPartitionOfUnity G` has closed supports
  subordinate to `baseCoordSet G`.
* `TauCeti.instFiberBundleMilnorBundleFiber`, `TauCeti.instPrincipalBundleMilnorBundleFiber`:
  `MilnorBundleFiber G` is a principal `G`-bundle over `MilnorClassifyingSpace G`.
* `TauCeti.coordChange_milnorTrivialization`: overlap formula `g_j(p) * g_i(p)⁻¹ * g`.
* `TauCeti.instT2SpaceMilnorClassifyingSpace`: `MilnorClassifyingSpace G` is `T₂` when `G` is `T₂`.

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
def MilnorClassifyingSpace : Type u :=
  MulAction.orbitRel.Quotient Gᵐᵒᵖ (MilnorTotalSpace G)

/-- The orbit projection `MilnorTotalSpace G → MilnorClassifyingSpace G`. -/
def milnorClassifyingSpaceProj : MilnorTotalSpace G → MilnorClassifyingSpace G :=
  Quotient.mk (MulAction.orbitRel Gᵐᵒᵖ (MilnorTotalSpace G))

/-- The distinguished base point of `MilnorClassifyingSpace G`, image of
`MilnorTotalSpace.basepoint`. -/
def milnorClassifyingSpaceBasepoint : MilnorClassifyingSpace G :=
  milnorClassifyingSpaceProj G (MilnorTotalSpace.basepoint G)

instance instInhabitedMilnorClassifyingSpace : Inhabited (MilnorClassifyingSpace G) :=
  ⟨milnorClassifyingSpaceBasepoint G⟩

@[simp]
theorem milnorClassifyingSpaceProj_basepoint :
    milnorClassifyingSpaceProj G (MilnorTotalSpace.basepoint G) =
      milnorClassifyingSpaceBasepoint G :=
  (rfl)

/-- Every point of `MilnorClassifyingSpace G` is the orbit of a point of `MilnorTotalSpace G`. -/
theorem milnorClassifyingSpaceProj_surjective :
    Surjective (milnorClassifyingSpaceProj G) :=
  Quot.mk_surjective

variable {G}

/-- Two points of `MilnorTotalSpace G` project to the same point of `MilnorClassifyingSpace G` if
and only if they lie in the same right `G`-orbit. -/
theorem milnorClassifyingSpaceProj_eq_iff {p q : MilnorTotalSpace G} :
    milnorClassifyingSpaceProj G p = milnorClassifyingSpaceProj G q ↔
      p ∈ MulAction.orbit Gᵐᵒᵖ q :=
  Quotient.eq''.trans MulAction.orbitRel_apply

@[simp]
theorem milnorClassifyingSpaceProj_smul (g : Gᵐᵒᵖ) (p : MilnorTotalSpace G) :
    milnorClassifyingSpaceProj G (g • p) = milnorClassifyingSpaceProj G p :=
  milnorClassifyingSpaceProj_eq_iff.mpr (MulAction.mem_orbit p g)

/-- Two points of `MilnorTotalSpace G` have the same image in `MilnorClassifyingSpace G` if and only
if a unique `g : G` carries the second to the first on the right (`op g • q = p`). -/
theorem milnorClassifyingSpaceProj_eq_iff_existsUnique {p q : MilnorTotalSpace G} :
    milnorClassifyingSpaceProj G p = milnorClassifyingSpaceProj G q ↔
      ∃! g : G, op g • q = p := by
  rw [milnorClassifyingSpaceProj_eq_iff, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨g.unop, by simpa using hg, fun g' hg' ↦ ?_⟩
    exact congrArg unop (IsCancelSMul.right_cancel (op g') g q (hg'.trans hg.symm))
  · rintro ⟨g, hg, -⟩
    exact ⟨op g, hg⟩

/-- The fibre of `milnorClassifyingSpaceProj G` through `p` is the right `G`-orbit of `p`. -/
theorem preimage_milnorClassifyingSpaceProj_singleton (p : MilnorTotalSpace G) :
    milnorClassifyingSpaceProj G ⁻¹' {milnorClassifyingSpaceProj G p} =
      MulAction.orbit Gᵐᵒᵖ p :=
  Set.ext fun _ ↦ milnorClassifyingSpaceProj_eq_iff

variable (G) [TopologicalSpace G]

/-- `MilnorClassifyingSpace G` carries the quotient topology induced from the strong coordinate
topology on `MilnorTotalSpace G`. -/
instance instTopologicalSpaceMilnorClassifyingSpace :
    TopologicalSpace (MilnorClassifyingSpace G) :=
  inferInstanceAs (TopologicalSpace (MulAction.orbitRel.Quotient Gᵐᵒᵖ (MilnorTotalSpace G)))

/-- The orbit projection `milnorClassifyingSpaceProj G` is a quotient map. -/
theorem isQuotientMap_milnorClassifyingSpaceProj :
    IsQuotientMap (milnorClassifyingSpaceProj G) :=
  isQuotientMap_quotient_mk'

/-- The orbit projection `milnorClassifyingSpaceProj G` is continuous. -/
@[fun_prop, continuity]
theorem continuous_milnorClassifyingSpaceProj :
    Continuous (milnorClassifyingSpaceProj G) :=
  (isQuotientMap_milnorClassifyingSpaceProj G).continuous

/-- **The orbit projection `MilnorTotalSpace G → MilnorClassifyingSpace G` is an open quotient
map** whenever multiplication on `G` is continuous. -/
theorem isOpenQuotientMap_milnorClassifyingSpaceProj [ContinuousMul G] :
    IsOpenQuotientMap (milnorClassifyingSpaceProj G) :=
  MulAction.isOpenQuotientMap_quotientMk

/-- When multiplication on `G` is continuous, `milnorClassifyingSpaceProj G` is an open map. -/
theorem isOpenMap_milnorClassifyingSpaceProj [ContinuousMul G] :
    IsOpenMap (milnorClassifyingSpaceProj G) :=
  (isOpenQuotientMap_milnorClassifyingSpaceProj G).isOpenMap

variable {G}

/-- A continuous `Gᵐᵒᵖ`-invariant map out of `MilnorTotalSpace G` descends to a continuous map out
of `MilnorClassifyingSpace G`. -/
def milnorClassifyingSpaceLift {X : Type*} [TopologicalSpace X]
    (f : C(MilnorTotalSpace G, X))
    (hf : ∀ (g : Gᵐᵒᵖ) (p : MilnorTotalSpace G), f (g • p) = f p) :
    C(MilnorClassifyingSpace G, X) where
  toFun := Quotient.lift f fun _ _ h ↦ by
    obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp h)
    exact hf g _
  continuous_toFun := continuous_quot_lift _ f.continuous

@[simp]
theorem milnorClassifyingSpaceLift_apply {X : Type*} [TopologicalSpace X]
    (f : C(MilnorTotalSpace G, X))
    (hf : ∀ (g : Gᵐᵒᵖ) (p : MilnorTotalSpace G), f (g • p) = f p)
    (p : MilnorTotalSpace G) :
    milnorClassifyingSpaceLift f hf (milnorClassifyingSpaceProj G p) = f p :=
  (rfl)

/-- Two continuous maps out of `MilnorClassifyingSpace G` agree once they agree after precomposition
with `milnorClassifyingSpaceProj G`. -/
theorem milnorClassifyingSpace_continuousMap_ext {X : Type*} [TopologicalSpace X]
    {φ ψ : C(MilnorClassifyingSpace G, X)}
    (h : ∀ p : MilnorTotalSpace G,
      φ (milnorClassifyingSpaceProj G p) = ψ (milnorClassifyingSpaceProj G p)) :
    φ = ψ :=
  ContinuousMap.ext ((milnorClassifyingSpaceProj_surjective G).forall.mpr h)

/-- When `G` is a trivial group (`Subsingleton G`), the orbit map is a homeomorphism
`MilnorTotalSpace G ≃ₜ MilnorClassifyingSpace G`. -/
def milnorClassifyingSpaceHomeomorphOfSubsingleton (G : Type u) [Group G] [TopologicalSpace G]
    [Subsingleton G] : MilnorTotalSpace G ≃ₜ MilnorClassifyingSpace G where
  toFun := milnorClassifyingSpaceProj G
  invFun := milnorClassifyingSpaceLift (ContinuousMap.id _) fun g p ↦ by
    rw [Subsingleton.elim g 1, one_smul]
  left_inv _ := rfl
  right_inv := Quotient.ind fun _ ↦ rfl
  continuous_toFun := continuous_milnorClassifyingSpaceProj G
  continuous_invFun := (milnorClassifyingSpaceLift _ _).continuous

end OrbitQuotient

/-! ### Descended weights, coordinate cover, and numerable partition of unity -/

namespace MilnorClassifyingSpace

section BaseWeights

variable (G : Type u) [Group G] [TopologicalSpace G]

/-- The `i`-th barycentric weight descended to a continuous map `MilnorClassifyingSpace G → ℝ`. -/
def baseWeight (i : ℕ) : C(MilnorClassifyingSpace G, ℝ) :=
  milnorClassifyingSpaceLift ⟨MilnorTotalSpace.weight i, MilnorTotalSpace.continuous_weight i⟩
    fun g p ↦ MilnorTotalSpace.weight_smul g i p

@[simp]
theorem baseWeight_proj (i : ℕ) (p : MilnorTotalSpace G) :
    baseWeight G i (milnorClassifyingSpaceProj G p) = MilnorTotalSpace.weight i p :=
  (rfl)

/-- The `i`-th coordinate open set `V_i = {b | 0 < t_i(b)}` in `MilnorClassifyingSpace G`. -/
def baseCoordSet (i : ℕ) : Set (MilnorClassifyingSpace G) :=
  {b | 0 < baseWeight G i b}

variable {G}

@[simp]
theorem mem_baseCoordSet_iff {i : ℕ} {b : MilnorClassifyingSpace G} :
    b ∈ baseCoordSet G i ↔ 0 < baseWeight G i b :=
  Iff.rfl

theorem proj_mem_baseCoordSet_iff {i : ℕ} {p : MilnorTotalSpace G} :
    milnorClassifyingSpaceProj G p ∈ baseCoordSet G i ↔ p ∈ MilnorTotalSpace.coordSet G i := by
  simp [mem_baseCoordSet_iff]

@[simp]
theorem preimage_baseCoordSet (G : Type u) [Group G] [TopologicalSpace G] (i : ℕ) :
    milnorClassifyingSpaceProj G ⁻¹' baseCoordSet G i = MilnorTotalSpace.coordSet G i := by
  ext p
  simp

/-- `baseCoordSet G i` is the image of `MilnorTotalSpace.coordSet G i` under the orbit map. -/
theorem image_coordSet_eq_baseCoordSet (G : Type u) [Group G] [TopologicalSpace G] (i : ℕ) :
    milnorClassifyingSpaceProj G '' MilnorTotalSpace.coordSet G i = baseCoordSet G i := by
  rw [← preimage_baseCoordSet,
    (milnorClassifyingSpaceProj_surjective G).image_preimage]

/-- Each coordinate chart base `baseCoordSet G i` is open in `MilnorClassifyingSpace G`. -/
theorem isOpen_baseCoordSet (G : Type u) [Group G] [TopologicalSpace G] (i : ℕ) :
    IsOpen (baseCoordSet G i) :=
  isOpen_lt continuous_const (baseWeight G i).continuous

theorem baseWeight_nonneg (i : ℕ) (b : MilnorClassifyingSpace G) : 0 ≤ baseWeight G i b :=
  Quotient.inductionOn b fun p ↦ MilnorTotalSpace.weight_nonneg i p

theorem baseWeight_le_one (i : ℕ) (b : MilnorClassifyingSpace G) : baseWeight G i b ≤ 1 :=
  Quotient.inductionOn b fun p ↦ MilnorTotalSpace.weight_le_one i p

theorem finite_support_baseWeight (b : MilnorClassifyingSpace G) :
    (support fun i ↦ baseWeight G i b).Finite :=
  Quotient.inductionOn b fun p ↦ MilnorTotalSpace.finite_support_weight p

theorem hasSum_baseWeight (b : MilnorClassifyingSpace G) :
    HasSum (fun i ↦ baseWeight G i b) 1 :=
  Quotient.inductionOn b fun p ↦ MilnorTotalSpace.hasSum_weight p

@[simp]
theorem tsum_baseWeight (b : MilnorClassifyingSpace G) : ∑' i, baseWeight G i b = 1 :=
  (hasSum_baseWeight b).tsum_eq

theorem exists_mem_baseCoordSet (b : MilnorClassifyingSpace G) :
    ∃ i, b ∈ baseCoordSet G i :=
  Quotient.inductionOn b fun p ↦ MilnorTotalSpace.exists_weight_pos p

/-- The open sets `baseCoordSet G i` cover `MilnorClassifyingSpace G`. -/
@[simp]
theorem iUnion_baseCoordSet (G : Type u) [Group G] [TopologicalSpace G] :
    ⋃ i, baseCoordSet G i = univ :=
  eq_univ_of_forall fun b ↦ mem_iUnion.mpr (exists_mem_baseCoordSet b)

private theorem sum_toFinset_support_baseWeight (b : MilnorClassifyingSpace G) :
    ∑ i ∈ (finite_support_baseWeight b).toFinset, baseWeight G i b = 1 :=
  (hasSum_sum_of_ne_finset_zero fun _ hi ↦
    not_not.mp fun hne ↦ hi ((finite_support_baseWeight b).mem_toFinset.mpr hne)).unique
    (hasSum_baseWeight b)

/-- Finite-support tail bound: for any finite index set `I` and any `j ∉ I`, the `j`-th weight at
`b` is bounded by the tail mass `1 - ∑ i ∈ I, baseWeight G i b`. -/
theorem baseWeight_le_one_sub_sum {b : MilnorClassifyingSpace G} {I : Finset ℕ} {j : ℕ}
    (hj : j ∉ I) : baseWeight G j b ≤ 1 - ∑ i ∈ I, baseWeight G i b := by
  let S : Finset ℕ := insert j I ∪ (finite_support_baseWeight b).toFinset
  have hle : ∑ i ∈ insert j I, baseWeight G i b ≤ ∑ i ∈ S, baseWeight G i b :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
      fun k _ _ ↦ baseWeight_nonneg k b
  have hS : ∑ i ∈ S, baseWeight G i b = 1 := by
    rw [← Finset.sum_subset Finset.subset_union_right fun k _ hk ↦
      not_not.mp fun hne ↦ hk ((finite_support_baseWeight b).mem_toFinset.mpr hne)]
    exact sum_toFinset_support_baseWeight b
  rw [Finset.sum_insert hj, hS] at hle
  linarith

private def maxBaseWeightFun (G : Type u) [Group G] [TopologicalSpace G]
    (b : MilnorClassifyingSpace G) : ℝ :=
  ⨆ i : ℕ, baseWeight G i b

private theorem bddAbove_range_baseWeight (b : MilnorClassifyingSpace G) :
    BddAbove (range fun i ↦ baseWeight G i b) :=
  ⟨1, forall_mem_range.2 fun i ↦ baseWeight_le_one i b⟩

private theorem le_maxBaseWeightFun (i : ℕ) (b : MilnorClassifyingSpace G) :
    baseWeight G i b ≤ maxBaseWeightFun G b :=
  le_ciSup (bddAbove_range_baseWeight b) i

private theorem maxBaseWeightFun_nonneg (b : MilnorClassifyingSpace G) :
    0 ≤ maxBaseWeightFun G b :=
  Real.iSup_nonneg fun i ↦ baseWeight_nonneg i b

private theorem maxBaseWeightFun_eq_ciSup_finset {J : Finset ℕ} {x : MilnorClassifyingSpace G}
    (hJ : ∀ j, j ∉ J → baseWeight G j x ≤ ⨆ i : J, baseWeight G i x) :
    maxBaseWeightFun G x = ⨆ i : J, baseWeight G i x := by
  have hnn : 0 ≤ ⨆ i : J, baseWeight G i x := Real.iSup_nonneg fun i ↦ baseWeight_nonneg i.1 x
  refine le_antisymm (Real.iSup_le (fun j ↦ ?_) hnn)
    (Real.iSup_le (fun i : J ↦ le_maxBaseWeightFun i.1 x) (maxBaseWeightFun_nonneg x))
  by_cases hj : j ∈ J
  · exact le_ciSup (finite_range (fun i : J ↦ baseWeight G i.1 x)).bddAbove ⟨j, hj⟩
  · exact hJ j hj

private theorem exists_eq_maxBaseWeightFun_and_pos (b : MilnorClassifyingSpace G) :
    ∃ i, baseWeight G i b = maxBaseWeightFun G b ∧ 0 < maxBaseWeightFun G b := by
  let I : Finset ℕ := (finite_support_baseWeight b).toFinset
  obtain ⟨i₀, hi₀⟩ := exists_mem_baseCoordSet b
  have hI : maxBaseWeightFun G b = ⨆ i : I, baseWeight G i.1 b := by
    refine maxBaseWeightFun_eq_ciSup_finset fun j hj ↦ ?_
    have hj0 : baseWeight G j b = 0 :=
      not_not.mp fun hne ↦ hj ((finite_support_baseWeight b).mem_toFinset.mpr hne)
    rw [hj0]
    exact Real.iSup_nonneg fun i : I ↦ baseWeight_nonneg i.1 b
  have : Nonempty I := ⟨⟨i₀, (finite_support_baseWeight b).mem_toFinset.mpr hi₀.ne'⟩⟩
  obtain ⟨⟨i, _⟩, hi⟩ := exists_eq_ciSup_of_finite (f := fun j : I ↦ baseWeight G j.1 b)
  exact ⟨i, hi.trans hI.symm, hi₀.trans_le (le_maxBaseWeightFun i₀ b)⟩

private theorem continuous_maxBaseWeightFun (G : Type u) [Group G] [TopologicalSpace G] :
    Continuous (maxBaseWeightFun G) := by
  refine continuous_iff_continuousAt.mpr fun b₀ ↦ ?_
  let I : Finset ℕ := (finite_support_baseWeight b₀).toFinset
  obtain ⟨_, -, hm₀⟩ := exists_eq_maxBaseWeightFun_and_pos b₀
  have hI_eq : ⨆ i : I, baseWeight G i.1 b₀ = maxBaseWeightFun G b₀ := by
    symm
    refine maxBaseWeightFun_eq_ciSup_finset fun j hj ↦ ?_
    have hj0 : baseWeight G j b₀ = 0 :=
      not_not.mp fun hne ↦ hj ((finite_support_baseWeight b₀).mem_toFinset.mpr hne)
    rw [hj0]
    exact Real.iSup_nonneg fun i : I ↦ baseWeight_nonneg i.1 b₀
  have hcont_sup : Continuous fun x : MilnorClassifyingSpace G ↦ ⨆ i : I, baseWeight G i.1 x :=
    TauCeti.continuous_ciSup_of_finite fun i : I ↦ (baseWeight G i.1).continuous
  have hcont_sum : Continuous fun x : MilnorClassifyingSpace G ↦ ∑ i ∈ I, baseWeight G i x := by
    fun_prop
  let W : Set (MilnorClassifyingSpace G) :=
    {x | 1 - maxBaseWeightFun G b₀ / 3 < ∑ i ∈ I, baseWeight G i x} ∩
      {x | maxBaseWeightFun G b₀ / 2 < ⨆ i : I, baseWeight G i.1 x}
  have hW_open : IsOpen W :=
    (isOpen_lt continuous_const hcont_sum).inter (isOpen_lt continuous_const hcont_sup)
  have hb₀W : b₀ ∈ W := by
    refine ⟨?_, ?_⟩
    · rw [mem_ofPred_eq]
      have hsum : ∑ i ∈ I, baseWeight G i b₀ = 1 := sum_toFinset_support_baseWeight b₀
      linarith
    · simp only [mem_ofPred_eq, hI_eq]
      linarith
  refine hcont_sup.continuousAt.congr
    (eventuallyEq_of_mem (hW_open.mem_nhds hb₀W) fun x hx ↦ ?_)
  symm
  refine maxBaseWeightFun_eq_ciSup_finset fun j hj ↦ ?_
  have htail := baseWeight_le_one_sub_sum (b := x) hj
  have hx1 : 1 - maxBaseWeightFun G b₀ / 3 < ∑ i ∈ I, baseWeight G i x := hx.1
  have hx2 : maxBaseWeightFun G b₀ / 2 < ⨆ i : I, baseWeight G i.1 x := hx.2
  linarith

/-- Pointwise maximum weight `m(b) = ⨆ i, baseWeight G i b` as a continuous function on
`MilnorClassifyingSpace G`, proved continuous by finite-support tail control. -/
def maxBaseWeight (G : Type u) [Group G] [TopologicalSpace G] :
    C(MilnorClassifyingSpace G, ℝ) :=
  ⟨maxBaseWeightFun G, continuous_maxBaseWeightFun G⟩

@[simp]
theorem maxBaseWeight_apply (b : MilnorClassifyingSpace G) :
    maxBaseWeight G b = ⨆ i : ℕ, baseWeight G i b :=
  (rfl)

theorem le_maxBaseWeight (i : ℕ) (b : MilnorClassifyingSpace G) :
    baseWeight G i b ≤ maxBaseWeight G b :=
  le_maxBaseWeightFun i b

theorem maxBaseWeight_pos (b : MilnorClassifyingSpace G) : 0 < maxBaseWeight G b :=
  (exists_eq_maxBaseWeightFun_and_pos b).choose_spec.2

theorem exists_baseWeight_eq_maxBaseWeight (b : MilnorClassifyingSpace G) :
    ∃ i, baseWeight G i b = maxBaseWeight G b :=
  ⟨(exists_eq_maxBaseWeightFun_and_pos b).choose,
    (exists_eq_maxBaseWeightFun_and_pos b).choose_spec.1⟩

/-- Milnor's truncated weight `ψ_i(b) = max(t_i(b) - m(b) / 2, 0)`. -/
def truncatedBaseWeight (G : Type u) [Group G] [TopologicalSpace G] (i : ℕ) :
    C(MilnorClassifyingSpace G, ℝ) :=
  ⟨fun b ↦ max (baseWeight G i b - maxBaseWeight G b / 2) 0,
    ((baseWeight G i).continuous.sub ((maxBaseWeight G).continuous.div_const 2)).max
      continuous_const⟩

@[simp]
theorem truncatedBaseWeight_apply (i : ℕ) (b : MilnorClassifyingSpace G) :
    truncatedBaseWeight G i b = max (baseWeight G i b - maxBaseWeight G b / 2) 0 :=
  (rfl)

theorem truncatedBaseWeight_nonneg (i : ℕ) (b : MilnorClassifyingSpace G) :
    0 ≤ truncatedBaseWeight G i b :=
  le_max_right _ _

theorem exists_truncatedBaseWeight_pos (b : MilnorClassifyingSpace G) :
    ∃ i, 0 < truncatedBaseWeight G i b := by
  obtain ⟨i, hi⟩ := exists_baseWeight_eq_maxBaseWeight b
  have hm : 0 < maxBaseWeight G b := maxBaseWeight_pos b
  exact ⟨i, lt_max_of_lt_left (by rw [hi]; linarith)⟩

/-- The supports of `truncatedBaseWeight G i` are locally finite on `MilnorClassifyingSpace G`. -/
theorem locallyFinite_support_truncatedBaseWeight (G : Type u) [Group G] [TopologicalSpace G] :
    LocallyFinite fun i ↦ support (truncatedBaseWeight G i) := by
  intro b₀
  let I : Finset ℕ := (finite_support_baseWeight b₀).toFinset
  have hm₀ : 0 < maxBaseWeight G b₀ := maxBaseWeight_pos b₀
  have hcont_sum : Continuous fun x : MilnorClassifyingSpace G ↦ ∑ i ∈ I, baseWeight G i x := by
    fun_prop
  let W : Set (MilnorClassifyingSpace G) :=
    {x | 1 - maxBaseWeight G b₀ / 4 < ∑ i ∈ I, baseWeight G i x} ∩
      {x | maxBaseWeight G b₀ / 2 < maxBaseWeight G x}
  have hW_open : IsOpen W :=
    (isOpen_lt continuous_const hcont_sum).inter
      (isOpen_lt continuous_const (maxBaseWeight G).continuous)
  have hb₀W : b₀ ∈ W := by
    refine ⟨?_, ?_⟩
    · rw [mem_ofPred_eq]
      have hsum : ∑ i ∈ I, baseWeight G i b₀ = 1 := sum_toFinset_support_baseWeight b₀
      linarith
    · simp only [mem_ofPred_eq]
      linarith
  refine ⟨W, hW_open.mem_nhds hb₀W, I.finite_toSet.subset fun j ⟨x, hx_supp, hxW⟩ ↦ ?_⟩
  rw [Finset.mem_coe]
  by_contra hj
  have htail := baseWeight_le_one_sub_sum (b := x) hj
  have hx1 : 1 - maxBaseWeight G b₀ / 4 < ∑ i ∈ I, baseWeight G i x := hxW.1
  have hx2 : maxBaseWeight G b₀ / 2 < maxBaseWeight G x := hxW.2
  have hle : baseWeight G j x - maxBaseWeight G x / 2 ≤ 0 := by linarith
  exact hx_supp (max_eq_right hle)

/-- Every closed support `tsupport (truncatedBaseWeight G i)` lies inside `baseCoordSet G i`. -/
theorem tsupport_truncatedBaseWeight_subset_baseCoordSet (i : ℕ) :
    tsupport (truncatedBaseWeight G i) ⊆ baseCoordSet G i := by
  intro b hb
  have hclosed :
      IsClosed {x : MilnorClassifyingSpace G | maxBaseWeight G x / 2 ≤ baseWeight G i x} :=
    isClosed_le ((maxBaseWeight G).continuous.div_const 2) (baseWeight G i).continuous
  have hle : maxBaseWeight G b / 2 ≤ baseWeight G i b := by
    refine closure_minimal (fun x hx ↦ ?_) hclosed hb
    rw [mem_ofPred_eq]
    have hpos : 0 < truncatedBaseWeight G i x :=
      lt_of_le_of_ne (truncatedBaseWeight_nonneg i x) (Ne.symm hx)
    rcases lt_max_iff.mp hpos with h | h
    · linarith
    · exact absurd h (lt_irrefl 0)
  exact (half_pos (maxBaseWeight_pos b)).trans_le hle

end BaseWeights

end MilnorClassifyingSpace

/-- **Milnor's subordinate partition of unity** on `MilnorClassifyingSpace G`, normalizing the
locally finite truncated weights `ψ_i = max(t_i - m / 2, 0)`. -/
def milnorPartitionOfUnity (G : Type u) [Group G] [TopologicalSpace G] :
    PartitionOfUnity ℕ (MilnorClassifyingSpace G) :=
  PartitionOfUnity.ofExistsPos (MilnorClassifyingSpace.truncatedBaseWeight G)
    (MilnorClassifyingSpace.locallyFinite_support_truncatedBaseWeight G)
    MilnorClassifyingSpace.truncatedBaseWeight_nonneg
    MilnorClassifyingSpace.exists_truncatedBaseWeight_pos

/-- `milnorPartitionOfUnity G` is subordinate (in the closed-support sense) to the coordinate open
cover `MilnorClassifyingSpace.baseCoordSet G`. -/
theorem isSubordinate_milnorPartitionOfUnity (G : Type u) [Group G] [TopologicalSpace G] :
    (milnorPartitionOfUnity G).IsSubordinate (MilnorClassifyingSpace.baseCoordSet G) := fun i ↦ by
  rw [milnorPartitionOfUnity, PartitionOfUnity.tsupport_ofExistsPos]
  exact MilnorClassifyingSpace.tsupport_truncatedBaseWeight_subset_baseCoordSet i

/-! ### Local sections, Hausdorffness, and principal bundle structure -/

namespace MilnorClassifyingSpace

section LocalSections

section Algebraic

variable (G : Type u) [Group G]

/-- Pointwise label normalization at index `i`: sends `p ∈ coordSet G i` to `p · g_i(p)⁻¹` (so that
its `i`-th vertex label is `1`) and sends points outside `coordSet G i` to `basepoint G`. This total
definition is globally `Gᵐᵒᵖ`-invariant on `MilnorTotalSpace G`. -/
private def normalize (i : ℕ) (p : MilnorTotalSpace G) : MilnorTotalSpace G := by
  classical
  exact if p ∈ MilnorTotalSpace.coordSet G i then
    op (MilnorTotalSpace.label i p)⁻¹ • p
  else
    MilnorTotalSpace.basepoint G

variable {G}

private theorem normalize_of_mem {i : ℕ} {p : MilnorTotalSpace G}
    (hp : p ∈ MilnorTotalSpace.coordSet G i) :
    normalize G i p = op (MilnorTotalSpace.label i p)⁻¹ • p := by
  simp [normalize, hp]

private theorem normalize_smul (i : ℕ) (g : Gᵐᵒᵖ) (p : MilnorTotalSpace G) :
    normalize G i (g • p) = normalize G i p := by
  by_cases hp : p ∈ MilnorTotalSpace.coordSet G i
  · have hgp : op g.unop • p ∈ MilnorTotalSpace.coordSet G i := by simpa using hp
    rw [← op_unop g, normalize_of_mem hgp, normalize_of_mem hp,
      MilnorTotalSpace.label_op_smul g.unop hp, mul_inv_rev,
      MilnorTotalSpace.op_smul_op_smul, mul_inv_cancel_left]
  · have hgp : g • p ∉ MilnorTotalSpace.coordSet G i := by simpa using hp
    simp [normalize, hp, hgp]

private theorem label_normalize {i : ℕ} {p : MilnorTotalSpace G}
    (hp : p ∈ MilnorTotalSpace.coordSet G i) :
    MilnorTotalSpace.label i (normalize G i p) = 1 := by
  rw [normalize_of_mem hp, MilnorTotalSpace.label_op_smul _ hp, mul_inv_cancel]

private theorem smul_normalize {i : ℕ} {p : MilnorTotalSpace G}
    (hp : p ∈ MilnorTotalSpace.coordSet G i) :
    op (MilnorTotalSpace.label i p) • normalize G i p = p := by
  rw [normalize_of_mem hp, MilnorTotalSpace.op_smul_op_smul, inv_mul_cancel, op_one, one_smul]

/-- Total auxiliary descent of `normalize G i` to `MilnorClassifyingSpace G`, continuous on
`baseCoordSet G i`. -/
private def localSectionAux (G : Type u) [Group G] (i : ℕ) :
    MilnorClassifyingSpace G → MilnorTotalSpace G :=
  Quotient.lift (normalize G i) fun _ _ h ↦ by
    obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp h)
    exact normalize_smul i g _

private theorem localSectionAux_proj (i : ℕ) (p : MilnorTotalSpace G) :
    localSectionAux G i (milnorClassifyingSpaceProj G p) = normalize G i p :=
  (rfl)

end Algebraic

section Topological

variable {G : Type u} [Group G] [TopologicalSpace G]

private theorem proj_localSectionAux {i : ℕ} {b : MilnorClassifyingSpace G}
    (hb : b ∈ baseCoordSet G i) :
    milnorClassifyingSpaceProj G (localSectionAux G i b) = b := by
  obtain ⟨p, rfl⟩ := milnorClassifyingSpaceProj_surjective G b
  rw [localSectionAux_proj, normalize_of_mem (proj_mem_baseCoordSet_iff.mp hb),
    milnorClassifyingSpaceProj_smul]

private theorem localSectionAux_mem_coordSet {i : ℕ} {b : MilnorClassifyingSpace G}
    (hb : b ∈ baseCoordSet G i) :
    localSectionAux G i b ∈ MilnorTotalSpace.coordSet G i := by
  rw [← proj_mem_baseCoordSet_iff, proj_localSectionAux hb]
  exact hb

private theorem weight_localSectionAux (j : ℕ) {i : ℕ} {b : MilnorClassifyingSpace G}
    (hb : b ∈ baseCoordSet G i) :
    MilnorTotalSpace.weight j (localSectionAux G i b) = baseWeight G j b := by
  rw [← baseWeight_proj G j, proj_localSectionAux hb]

private theorem label_localSectionAux {i : ℕ} {b : MilnorClassifyingSpace G}
    (hb : b ∈ baseCoordSet G i) :
    MilnorTotalSpace.label i (localSectionAux G i b) = 1 := by
  obtain ⟨p, rfl⟩ := milnorClassifyingSpaceProj_surjective G b
  exact label_normalize (proj_mem_baseCoordSet_iff.mp hb)

private theorem continuousOn_normalize (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (i : ℕ) :
    ContinuousOn (normalize G i) (MilnorTotalSpace.coordSet G i) := by
  refine (((continuous_op.comp continuous_inv).continuousOn.comp
    (MilnorTotalSpace.continuousOn_label i) (mapsTo_univ _ _)).smul continuousOn_id).congr ?_
  intro p hp
  exact normalize_of_mem hp

/-- Continuity of `localSectionAux G i` on `baseCoordSet G i`, descended along the open quotient
restriction `coordSet G i → baseCoordSet G i`. -/
private theorem continuousOn_localSectionAux (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (i : ℕ) :
    ContinuousOn (localSectionAux G i) (baseCoordSet G i) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hq : IsOpenQuotientMap
      ((baseCoordSet G i).restrictPreimage (milnorClassifyingSpaceProj G)) :=
    (isOpenQuotientMap_milnorClassifyingSpaceProj G).restrictPreimage (baseCoordSet G i)
  rw [hq.isQuotientMap.continuous_iff]
  have hnorm : ContinuousOn (normalize G i)
      (milnorClassifyingSpaceProj G ⁻¹' baseCoordSet G i) := by
    rw [preimage_baseCoordSet]
    exact continuousOn_normalize G i
  exact continuousOn_iff_continuous_domRestrict.mp hnorm

/-- Continuous local section `s_i : V_i → MilnorTotalSpace G` over `baseCoordSet G i` normalized by
`label i (s_i b) = 1`. -/
def localSection (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (i : ℕ) :
    C(baseCoordSet G i, MilnorTotalSpace G) :=
  ⟨(baseCoordSet G i).domRestrict (localSectionAux G i),
    continuousOn_iff_continuous_domRestrict.mp (continuousOn_localSectionAux G i)⟩

@[simp]
theorem proj_localSection [IsTopologicalGroup G] (i : ℕ) (b : baseCoordSet G i) :
    milnorClassifyingSpaceProj G (localSection G i b) = b.1 :=
  proj_localSectionAux b.2

theorem localSection_mem_coordSet [IsTopologicalGroup G] (i : ℕ) (b : baseCoordSet G i) :
    localSection G i b ∈ MilnorTotalSpace.coordSet G i :=
  localSectionAux_mem_coordSet b.2

@[simp]
theorem weight_localSection [IsTopologicalGroup G] (j i : ℕ) (b : baseCoordSet G i) :
    MilnorTotalSpace.weight j (localSection G i b) = baseWeight G j b.1 :=
  weight_localSectionAux j b.2

@[simp]
theorem label_localSection [IsTopologicalGroup G] (i : ℕ) (b : baseCoordSet G i) :
    MilnorTotalSpace.label i (localSection G i b) = 1 :=
  label_localSectionAux b.2

@[simp]
theorem localSection_mk_proj [IsTopologicalGroup G] {i : ℕ} {p : MilnorTotalSpace G}
    (hp : p ∈ MilnorTotalSpace.coordSet G i) :
    localSection G i ⟨milnorClassifyingSpaceProj G p, proj_mem_baseCoordSet_iff.mpr hp⟩ =
      op (MilnorTotalSpace.label i p)⁻¹ • p :=
  normalize_of_mem hp

theorem smul_localSection_mk_proj [IsTopologicalGroup G] {i : ℕ} {p : MilnorTotalSpace G}
    (hp : p ∈ MilnorTotalSpace.coordSet G i) :
    op (MilnorTotalSpace.label i p) •
      localSection G i ⟨milnorClassifyingSpaceProj G p, proj_mem_baseCoordSet_iff.mpr hp⟩ = p :=
  smul_normalize hp

end Topological

end LocalSections

end MilnorClassifyingSpace

/-- **Hausdorffness of `MilnorClassifyingSpace G` for Hausdorff topological groups**, proved by
descended-weight separation together with normalized-label separation
`b ↦ label j (localSection G i ⟨b, hb⟩)` on chart overlaps
`baseCoordSet G i ∩ baseCoordSet G j`. -/
instance instT2SpaceMilnorClassifyingSpace (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] : T2Space (MilnorClassifyingSpace G) := by
  refine ⟨fun b₁ b₂ hb ↦ ?_⟩
  by_cases hw : ∀ j,
      MilnorClassifyingSpace.baseWeight G j b₁ = MilnorClassifyingSpace.baseWeight G j b₂
  · obtain ⟨i, hb₁i⟩ := MilnorClassifyingSpace.exists_mem_baseCoordSet b₁
    have hb₂i : b₂ ∈ MilnorClassifyingSpace.baseCoordSet G i := by
      rw [MilnorClassifyingSpace.mem_baseCoordSet_iff, ← hw i]
      exact hb₁i
    set s₁ := MilnorClassifyingSpace.localSectionAux G i b₁
    set s₂ := MilnorClassifyingSpace.localSectionAux G i b₂
    have hs_ne : s₁ ≠ s₂ := fun h ↦ hb <| by
      rw [← MilnorClassifyingSpace.proj_localSectionAux hb₁i,
        ← MilnorClassifyingSpace.proj_localSectionAux hb₂i]
      exact congrArg (milnorClassifyingSpaceProj G) h
    have hsw : ∀ j, MilnorTotalSpace.weight j s₁ = MilnorTotalSpace.weight j s₂ := fun j ↦ by
      rw [MilnorClassifyingSpace.weight_localSectionAux j hb₁i,
        MilnorClassifyingSpace.weight_localSectionAux j hb₂i, hw j]
    have hsl : ∃ j, s₁ ∈ MilnorTotalSpace.coordSet G j ∧
        MilnorTotalSpace.label j s₁ ≠ MilnorTotalSpace.label j s₂ := by
      by_contra! h
      exact hs_ne (MilnorTotalSpace.ext_coord hsw h)
    obtain ⟨j, hs₁j, hlj⟩ := hsl
    have hb₁j : b₁ ∈ MilnorClassifyingSpace.baseCoordSet G j := by
      rw [MilnorClassifyingSpace.mem_baseCoordSet_iff,
        ← MilnorClassifyingSpace.weight_localSectionAux j hb₁i]
      exact MilnorTotalSpace.mem_coordSet_iff.mp hs₁j
    have hb₂j : b₂ ∈ MilnorClassifyingSpace.baseCoordSet G j := by
      rw [MilnorClassifyingSpace.mem_baseCoordSet_iff, ← hw j]
      exact hb₁j
    let W : Set (MilnorClassifyingSpace G) :=
      MilnorClassifyingSpace.baseCoordSet G i ∩ MilnorClassifyingSpace.baseCoordSet G j
    have hW_open : IsOpen W :=
      (MilnorClassifyingSpace.isOpen_baseCoordSet G i).inter
        (MilnorClassifyingSpace.isOpen_baseCoordSet G j)
    have hf : ContinuousOn (fun b ↦
        MilnorTotalSpace.label j (MilnorClassifyingSpace.localSectionAux G i b)) W := by
      refine (MilnorTotalSpace.continuousOn_label j).comp
        ((MilnorClassifyingSpace.continuousOn_localSectionAux G i).mono inter_subset_left) ?_
      intro b hbW
      rw [MilnorTotalSpace.mem_coordSet_iff,
        MilnorClassifyingSpace.weight_localSectionAux j hbW.1]
      exact hbW.2
    obtain ⟨U, V, hU, hV, hU₁, hV₂, hdisj⟩ := t2_separation hlj
    obtain ⟨U', hU', hU'eq⟩ := continuousOn_iff'.mp hf U hU
    obtain ⟨V', hV', hV'eq⟩ := continuousOn_iff'.mp hf V hV
    refine ⟨U' ∩ W, V' ∩ W, hU'.inter hW_open, hV'.inter hW_open, ?_, ?_, ?_⟩
    · rw [← hU'eq]
      exact ⟨hU₁, hb₁i, hb₁j⟩
    · rw [← hV'eq]
      exact ⟨hV₂, hb₂i, hb₂j⟩
    · rw [← hU'eq, ← hV'eq]
      exact Disjoint.mono inter_subset_left inter_subset_left (hdisj.preimage _)
  · push Not at hw
    obtain ⟨j, hj⟩ := hw
    obtain ⟨U, V, hU, hV, hU₁, hV₂, hdisj⟩ := t2_separation hj
    exact ⟨MilnorClassifyingSpace.baseWeight G j ⁻¹' U,
      MilnorClassifyingSpace.baseWeight G j ⁻¹' V,
      hU.preimage (MilnorClassifyingSpace.baseWeight G j).continuous,
      hV.preimage (MilnorClassifyingSpace.baseWeight G j).continuous,
      hU₁, hV₂, hdisj.preimage _⟩

/-! ### Bundle fibre family and principal bundle charts -/

section PrincipalBundle

/-- The fibre over `b : MilnorClassifyingSpace G` of Milnor's universal bundle, consisting of points
of `MilnorTotalSpace G` whose orbit is `b`. -/
@[ext]
structure MilnorBundleFiber (G : Type u) [Group G] (b : MilnorClassifyingSpace G) where
  /-- Regard a point of `MilnorTotalSpace G` over `b` as a point of `MilnorBundleFiber G b`. -/
  mk ::
  /-- The underlying point of `MilnorTotalSpace G`. -/
  val : MilnorTotalSpace G
  /-- The underlying point projects to `b`. -/
  proj_eq : milnorClassifyingSpaceProj G val = b

namespace MilnorBundleFiber

section Group

variable {G : Type u} [Group G]

instance instNonempty (b : MilnorClassifyingSpace G) : Nonempty (MilnorBundleFiber G b) :=
  ⟨⟨Quotient.out b, Quotient.out_eq b⟩⟩

/-- Right action of `G` (`MulAction Gᵐᵒᵖ`) on each fibre `MilnorBundleFiber G b`. -/
instance instMulActionOp (b : MilnorClassifyingSpace G) :
    MulAction Gᵐᵒᵖ (MilnorBundleFiber G b) where
  smul g p := ⟨g • p.val, (milnorClassifyingSpaceProj_smul g p.val).trans p.proj_eq⟩
  one_smul p := MilnorBundleFiber.ext (one_smul _ p.val)
  mul_smul g h p := MilnorBundleFiber.ext (mul_smul g h p.val)

@[simp]
theorem val_smul {b : MilnorClassifyingSpace G} (g : Gᵐᵒᵖ) (p : MilnorBundleFiber G b) :
    (g • p).val = g • p.val :=
  (rfl)

/-- Canonical equivalence identifying `TotalSpace G (MilnorBundleFiber G)` with
`MilnorTotalSpace G`. -/
def totalSpaceEquiv (G : Type u) [Group G] :
    TotalSpace G (MilnorBundleFiber G) ≃ MilnorTotalSpace G where
  toFun x := x.2.val
  invFun p := ⟨milnorClassifyingSpaceProj G p, ⟨p, rfl⟩⟩
  left_inv x := by
    rcases x with ⟨b, ⟨p, rfl⟩⟩
    rfl
  right_inv _ := rfl

@[simp]
theorem totalSpaceEquiv_apply (x : TotalSpace G (MilnorBundleFiber G)) :
    totalSpaceEquiv G x = x.2.val :=
  (rfl)

@[simp]
theorem totalSpaceEquiv_symm_apply (p : MilnorTotalSpace G) :
    (totalSpaceEquiv G).symm p = ⟨milnorClassifyingSpaceProj G p, ⟨p, rfl⟩⟩ :=
  (rfl)

@[simp]
theorem snd_val_totalSpaceEquiv_symm (p : MilnorTotalSpace G) :
    ((totalSpaceEquiv G).symm p).2.val = p :=
  (rfl)

@[simp]
theorem proj_val {b : MilnorClassifyingSpace G} (p : MilnorBundleFiber G b) :
    milnorClassifyingSpaceProj G p.val = b :=
  p.proj_eq

theorem proj_comp_totalSpaceEquiv (x : TotalSpace G (MilnorBundleFiber G)) :
    milnorClassifyingSpaceProj G (totalSpaceEquiv G x) = x.proj :=
  x.2.proj_eq

end Group

section Topology

variable (G : Type u) [Group G] [TopologicalSpace G]

/-- Topology on `TotalSpace G (MilnorBundleFiber G)` induced from `MilnorTotalSpace G` via
`totalSpaceEquiv G`. -/
instance instTopologicalSpaceTotalSpace :
    TopologicalSpace (TotalSpace G (MilnorBundleFiber G)) :=
  .induced (totalSpaceEquiv G) inferInstance

/-- Subspace topology on each fibre `MilnorBundleFiber G b`. -/
instance instTopologicalSpace (b : MilnorClassifyingSpace G) :
    TopologicalSpace (MilnorBundleFiber G b) :=
  .induced (TotalSpace.mk' G b) inferInstance

/-- Homeomorphism identifying `TotalSpace G (MilnorBundleFiber G)` with `MilnorTotalSpace G`. -/
def totalSpaceHomeomorph : TotalSpace G (MilnorBundleFiber G) ≃ₜ MilnorTotalSpace G :=
  (totalSpaceEquiv G).toHomeomorphOfIsInducing ⟨rfl⟩

@[simp]
theorem coe_totalSpaceHomeomorph :
    ⇑(totalSpaceHomeomorph G) = totalSpaceEquiv G :=
  (rfl)

@[simp]
theorem coe_totalSpaceHomeomorph_symm :
    ⇑(totalSpaceHomeomorph G).symm = (totalSpaceEquiv G).symm :=
  (rfl)

theorem continuous_proj : Continuous (π G (MilnorBundleFiber G)) := by
  have heq : π G (MilnorBundleFiber G) =
      milnorClassifyingSpaceProj G ∘ totalSpaceHomeomorph G := by
    ext x
    exact (proj_comp_totalSpaceEquiv x).symm
  rw [heq]
  exact (continuous_milnorClassifyingSpaceProj G).comp (totalSpaceHomeomorph G).continuous

end Topology

end MilnorBundleFiber

section Charts

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Principal `G`-bundle trivialization of `MilnorBundleFiber G` over `baseCoordSet G i`, sending
`p` to `(p.proj, label i p.2.val)` with inverse `(b, g) ↦ s_i(b) · g`. -/
def milnorTrivialization (i : ℕ) :
    Trivialization G (π G (MilnorBundleFiber G)) where
  toFun p := (p.proj, MilnorTotalSpace.label i p.2.val)
  invFun x := (MilnorBundleFiber.totalSpaceEquiv G).symm
    (op x.2 • MilnorClassifyingSpace.localSectionAux G i x.1)
  source := π G (MilnorBundleFiber G) ⁻¹' MilnorClassifyingSpace.baseCoordSet G i
  target := MilnorClassifyingSpace.baseCoordSet G i ×ˢ univ
  map_source' _ hp := ⟨hp, mem_univ _⟩
  map_target' x hx := by
    change milnorClassifyingSpaceProj G
      (op x.2 • MilnorClassifyingSpace.localSectionAux G i x.1) ∈
      MilnorClassifyingSpace.baseCoordSet G i
    rw [milnorClassifyingSpaceProj_smul, MilnorClassifyingSpace.proj_localSectionAux hx.1]
    exact hx.1
  left_inv' p hp := by
    rcases p with ⟨b, ⟨q, rfl⟩⟩
    have hq : q ∈ MilnorTotalSpace.coordSet G i :=
      MilnorClassifyingSpace.proj_mem_baseCoordSet_iff.mp hp
    simp [MilnorClassifyingSpace.localSectionAux_proj, MilnorClassifyingSpace.smul_normalize hq]
  right_inv' x hx := by
    rcases x with ⟨b, g⟩
    have hb : b ∈ MilnorClassifyingSpace.baseCoordSet G i := hx.1
    have hs : MilnorClassifyingSpace.localSectionAux G i b ∈ MilnorTotalSpace.coordSet G i :=
      MilnorClassifyingSpace.localSectionAux_mem_coordSet hb
    ext
    · change milnorClassifyingSpaceProj G
        (op g • MilnorClassifyingSpace.localSectionAux G i b) = b
      rw [milnorClassifyingSpaceProj_smul, MilnorClassifyingSpace.proj_localSectionAux hb]
    · change MilnorTotalSpace.label i
        (op g • MilnorClassifyingSpace.localSectionAux G i b) = g
      rw [MilnorTotalSpace.label_op_smul g hs, MilnorClassifyingSpace.label_localSectionAux hb,
        one_mul]
  open_source := (MilnorClassifyingSpace.isOpen_baseCoordSet G i).preimage
    (MilnorBundleFiber.continuous_proj G)
  open_target := (MilnorClassifyingSpace.isOpen_baseCoordSet G i).prod isOpen_univ
  continuousOn_toFun :=
    (MilnorBundleFiber.continuous_proj G).continuousOn.prodMk <|
      (MilnorTotalSpace.continuousOn_label i).comp
        (MilnorBundleFiber.totalSpaceHomeomorph G).continuous.continuousOn fun p hp ↦ by
          rw [← MilnorClassifyingSpace.proj_mem_baseCoordSet_iff, p.2.proj_eq]
          exact hp
  continuousOn_invFun :=
    (MilnorBundleFiber.totalSpaceHomeomorph G).symm.continuous.comp_continuousOn <|
      ((continuous_op.comp continuous_snd).continuousOn.smul
        ((MilnorClassifyingSpace.continuousOn_localSectionAux G i).comp
          continuous_fst.continuousOn fun _ hx ↦ hx.1))
  baseSet := MilnorClassifyingSpace.baseCoordSet G i
  open_baseSet := MilnorClassifyingSpace.isOpen_baseCoordSet G i
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

@[simp]
theorem baseSet_milnorTrivialization (i : ℕ) :
    (milnorTrivialization G i).baseSet = MilnorClassifyingSpace.baseCoordSet G i :=
  (rfl)

@[simp]
theorem milnorTrivialization_apply (i : ℕ) (p : TotalSpace G (MilnorBundleFiber G)) :
    milnorTrivialization G i p = (p.proj, MilnorTotalSpace.label i p.2.val) :=
  (rfl)

variable {G} in
@[simp]
theorem milnorTrivialization_symm_apply {i : ℕ} {b : MilnorClassifyingSpace G}
    (hb : b ∈ MilnorClassifyingSpace.baseCoordSet G i) (g : G) :
    (milnorTrivialization G i).toOpenPartialHomeomorph.symm (b, g) =
      (MilnorBundleFiber.totalSpaceEquiv G).symm
        (op g • MilnorClassifyingSpace.localSection G i ⟨b, hb⟩) :=
  (rfl)

/-- Every chart `milnorTrivialization G i` is right-equivariant. -/
instance isEquivariant_milnorTrivialization (i : ℕ) :
    (milnorTrivialization G i).IsEquivariant where
  snd_apply_smul b hb p g := by
    have hp : p.val ∈ MilnorTotalSpace.coordSet G i := by
      rw [← MilnorClassifyingSpace.proj_mem_baseCoordSet_iff, p.proj_eq]
      exact hb
    rw [milnorTrivialization_apply, milnorTrivialization_apply, MilnorBundleFiber.val_smul]
    exact MilnorTotalSpace.label_op_smul g hp

/-- **Noncommutative transition cocycle of Milnor's principal bundle charts.** On the overlap
`p ∈ coordSet G i ∩ coordSet G j` over `b = milnorClassifyingSpaceProj G p`, changing coordinates
from chart `i` to chart `j` multiplies on the left by `label j p * (label i p)⁻¹`. -/
theorem coordChange_milnorTrivialization {i j : ℕ} {p : MilnorTotalSpace G}
    (hpi : p ∈ MilnorTotalSpace.coordSet G i) (hpj : p ∈ MilnorTotalSpace.coordSet G j) (g : G) :
    (milnorTrivialization G i).coordChange (milnorTrivialization G j)
      (milnorClassifyingSpaceProj G p) g =
      MilnorTotalSpace.label j p * (MilnorTotalSpace.label i p)⁻¹ * g := by
  rw [Trivialization.coordChange,
    milnorTrivialization_symm_apply (MilnorClassifyingSpace.proj_mem_baseCoordSet_iff.mpr hpi),
    milnorTrivialization_apply, MilnorBundleFiber.snd_val_totalSpaceEquiv_symm,
    MilnorClassifyingSpace.localSection_mk_proj hpi, MilnorTotalSpace.op_smul_op_smul,
    MilnorTotalSpace.label_op_smul _ hpj, mul_assoc]

/-- Fibre bundle structure on `MilnorBundleFiber G` with atlas
`{milnorTrivialization G i | i : ℕ}`. -/
instance instFiberBundleMilnorBundleFiber : FiberBundle G (MilnorBundleFiber G) where
  totalSpaceMk_isInducing' _ := ⟨rfl⟩
  trivializationAtlas' := range (milnorTrivialization G)
  trivializationAt' b := milnorTrivialization G
    (MilnorClassifyingSpace.exists_mem_baseCoordSet b).choose
  mem_baseSet_trivializationAt' b := by
    rw [baseSet_milnorTrivialization]
    exact (MilnorClassifyingSpace.exists_mem_baseCoordSet b).choose_spec
  trivialization_mem_atlas' b := ⟨_, rfl⟩

instance memTrivializationAtlas_milnorTrivialization (i : ℕ) :
    MemTrivializationAtlas (milnorTrivialization G i) :=
  ⟨⟨i, rfl⟩⟩

/-- **Milnor's countable join is a principal `G`-bundle** over `MilnorClassifyingSpace G`. -/
instance instPrincipalBundleMilnorBundleFiber : PrincipalBundle G (MilnorBundleFiber G) where
  isEquivariant_trivialization' _ ht := by
    obtain ⟨i, rfl⟩ := ht.out
    infer_instance

/-- Over `b ∈ baseCoordSet G i`, the principal-bundle division map on `MilnorBundleFiber G b` reads
`(label i p.val)⁻¹ * label i q.val`. -/
theorem MilnorBundleFiber.division_eq {i : ℕ} {b : MilnorClassifyingSpace G}
    (hb : b ∈ MilnorClassifyingSpace.baseCoordSet G i) (p q : MilnorBundleFiber G b) :
    PrincipalBundle.division G p q =
      (MilnorTotalSpace.label i p.val)⁻¹ * MilnorTotalSpace.label i q.val :=
  PrincipalBundle.division_eq_of_mem_baseSet (e := milnorTrivialization G i) hb p q

end Charts

end PrincipalBundle

/-! ### Comparison from the weak simplicial classifying space and functoriality -/

section Comparison

/-- Continuous comparison map `classifyingSpace G → MilnorClassifyingSpace G` from the weak
simplicial classifying space to the strong-coordinate classifying space, induced by
`weakToMilnorTotalSpace G`. -/
def weakToMilnorClassifyingSpace (G : Type u) [Group G] [TopologicalSpace G] :
    C(classifyingSpace G, MilnorClassifyingSpace G) :=
  classifyingSpaceLift
    ((⟨milnorClassifyingSpaceProj G, continuous_milnorClassifyingSpaceProj G⟩ :
      C(MilnorTotalSpace G, MilnorClassifyingSpace G)).comp (weakToMilnorTotalSpace G))
    fun g x ↦ by
      simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, weakToMilnorTotalSpace_smul,
        milnorClassifyingSpaceProj_smul]

@[simp]
theorem weakToMilnorClassifyingSpace_proj {G : Type u} [Group G] [TopologicalSpace G]
    (x : universalGSpace G) :
    weakToMilnorClassifyingSpace G (classifyingSpaceProj G x) =
      milnorClassifyingSpaceProj G (weakToMilnorTotalSpace G x) := by
  simp [weakToMilnorClassifyingSpace]

@[simp]
theorem weakToMilnorClassifyingSpace_basepoint (G : Type u) [Group G] [TopologicalSpace G] :
    weakToMilnorClassifyingSpace G (classifyingSpaceBasepoint G) =
      milnorClassifyingSpaceBasepoint G := by
  rw [← classifyingSpaceProj_universalGSpaceBasepoint, weakToMilnorClassifyingSpace_proj,
    weakToMilnorTotalSpace_basepoint, milnorClassifyingSpaceProj_basepoint]

end Comparison

end TauCeti

namespace MonoidHom

open TauCeti MulOpposite

variable {G : Type u} {H : Type v} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]

/-- A continuous group homomorphism `φ : G →* H` induces a continuous map
`MilnorClassifyingSpace G → MilnorClassifyingSpace H` intertwining the orbit projections with
`φ.milnorTotalSpaceMap hφ`. -/
def milnorClassifyingSpaceMap (φ : G →* H) (hφ : Continuous φ) :
    C(MilnorClassifyingSpace G, MilnorClassifyingSpace H) :=
  milnorClassifyingSpaceLift
    ((⟨milnorClassifyingSpaceProj H, continuous_milnorClassifyingSpaceProj H⟩ :
      C(MilnorTotalSpace H, MilnorClassifyingSpace H)).comp (φ.milnorTotalSpaceMap hφ))
    fun g p ↦ by
      rw [ContinuousMap.comp_apply, ContinuousMap.coe_mk, ← op_unop g,
        milnorTotalSpaceMap_op_smul, milnorClassifyingSpaceProj_smul]
      rfl

@[simp]
theorem milnorClassifyingSpaceMap_proj (φ : G →* H) (hφ : Continuous φ)
    (p : MilnorTotalSpace G) :
    φ.milnorClassifyingSpaceMap hφ (milnorClassifyingSpaceProj G p) =
      milnorClassifyingSpaceProj H (φ.milnorTotalSpaceMap hφ p) :=
  (rfl)

@[simp]
theorem milnorClassifyingSpaceMap_basepoint (φ : G →* H) (hφ : Continuous φ) :
    φ.milnorClassifyingSpaceMap hφ (milnorClassifyingSpaceBasepoint G) =
      milnorClassifyingSpaceBasepoint H := by
  rw [← milnorClassifyingSpaceProj_basepoint, milnorClassifyingSpaceMap_proj,
    milnorTotalSpaceMap_basepoint, milnorClassifyingSpaceProj_basepoint]

@[simp]
theorem milnorClassifyingSpaceMap_id :
    (MonoidHom.id G).milnorClassifyingSpaceMap continuous_id =
      ContinuousMap.id (MilnorClassifyingSpace G) :=
  milnorClassifyingSpace_continuousMap_ext fun p ↦ by simp

@[simp]
theorem milnorClassifyingSpaceMap_comp {K : Type w} [Group K] [TopologicalSpace K]
    (ψ : H →* K) (hψ : Continuous ψ) (φ : G →* H) (hφ : Continuous φ) :
    (ψ.comp φ).milnorClassifyingSpaceMap (hψ.comp hφ) =
      (ψ.milnorClassifyingSpaceMap hψ).comp (φ.milnorClassifyingSpaceMap hφ) :=
  milnorClassifyingSpace_continuousMap_ext fun p ↦ by
    rw [ContinuousMap.comp_apply, milnorClassifyingSpaceMap_proj, milnorClassifyingSpaceMap_proj,
      milnorClassifyingSpaceMap_proj, milnorTotalSpaceMap_comp, ContinuousMap.comp_apply]

end MonoidHom
