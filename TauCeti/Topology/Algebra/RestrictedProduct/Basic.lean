/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
public import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Integral subgroups of restricted products

This file packages the everywhere-integral part of a restricted product of groups equipped
with topologies.  The reference family used to form the restricted product and a second family of
subgroups are kept separate, so changing the integral model at finitely many indices is
represented without changing the ambient restricted product.  The resulting openness and
compactness statements are the point-set input for maps and decompositions of restricted
products.

It also names the restricted product of a family of groups relative to a family of reference
subgroups, and its product with a distinguished factor carrying no integrality condition. These
are the shapes in which restricted products appear when a family of local groups is assembled
into an adelic one: the finite adelic points, and the full adelic points with the archimedean
factor set apart.

Every construction and theorem here is also stated for additive groups (`integralAddSubgroup`,
`RestrictedProductAddGroup`, `CompactOpenAddSubgroups`, …).

The eventual comparison results are adapted from the FLT project
(`ImperialCollegeLondon/FLT`, file `TopologicalSpace.lean`, source commit
`bc2fe8ff7396469a16c2a6d51d6117f5825d93a0`, FLT PR #1088, Apache 2.0), whose source file
credits Matthew Jasper, Kevin Buzzard, Bhavik Mehta, Ruben Van de Velde, Bryan Wang Peng Jun,
and Pietro Monticone.

## References

* N. Bourbaki, *General Topology*.
* A. Weil, *Basic Number Theory*.
-/

public section

open Filter
open scoped RestrictedProduct

namespace RestrictedProduct

/-- The coercion homomorphism from a restricted product to the full product acts as the
coercion. -/
@[to_additive (attr := simp)]
theorem coeMonoidHom_apply {ι : Type*} {R : ι → Type*} {S : ι → Type*}
    [∀ i, SetLike (S i) (R i)] {B : ∀ i, S i} {𝓕 : Filter ι} [∀ i, Monoid (R i)]
    [∀ i, SubmonoidClass (S i) (R i)] (x : Πʳ i, [R i, B i]_[𝓕]) :
    coeMonoidHom x = ⇑x :=
  rfl

end RestrictedProduct

namespace TauCeti

universe u v w

variable {ι : Type u} {G : ι → Type v}
variable [∀ i, Group (G i)]

/-- The restricted product of the family `G` relative to the reference subgroups `U`: the
elements of `Π i, G i` whose coordinates lie in `U i` for all but finitely many `i`. -/
@[to_additive /-- The restricted product of the family of additive groups `G` relative to the
reference subgroups `U`: the elements of `Π i, G i` whose coordinates lie in `U i` for all but
finitely many `i`. -/]
abbrev RestrictedProductGroup (U : ∀ i, Subgroup (G i)) :=
  Πʳ i, [G i, (U i : Set (G i))]

/-- A restricted product together with a distinguished factor `H` carrying **no** integrality
condition. -/
@[to_additive /-- A restricted product of additive groups together with a distinguished factor
`H` carrying **no** integrality condition. -/]
abbrev RestrictedProductGroupWithFactor (H : Type w) (U : ∀ i, Subgroup (G i)) :=
  H × RestrictedProductGroup U

/-- The subgroup of a restricted product cut out by a second family of subgroups. -/
@[to_additive /-- The additive subgroup of a restricted product cut out by a second family of
additive subgroups. -/]
def integralSubgroupOf (U V : ∀ i, Subgroup (G i)) :
    Subgroup (Πʳ i, [G i, (U i : Set (G i))]) :=
  (Subgroup.pi Set.univ V).comap RestrictedProduct.coeMonoidHom

/-- Membership means that every coordinate belongs to the corresponding subgroup `V i`. -/
@[to_additive (attr := simp)]
theorem mem_integralSubgroupOf (U V : ∀ i, Subgroup (G i))
    (x : Πʳ i, [G i, (U i : Set (G i))]) :
    x ∈ integralSubgroupOf U V ↔ ∀ i, x i ∈ V i := by
  simp [integralSubgroupOf, Subgroup.mem_pi]

/-- The subgroup whose coordinates lie in the reference subgroup at every index. -/
@[to_additive /-- The additive subgroup whose coordinates lie in the reference subgroup at every
index. -/]
def integralSubgroup (U : ∀ i, Subgroup (G i)) :
    Subgroup (Πʳ i, [G i, (U i : Set (G i))]) :=
  integralSubgroupOf U U

/-- Membership means that every coordinate belongs to the reference subgroup `U i`. -/
@[to_additive (attr := simp)]
theorem mem_integralSubgroup (U : ∀ i, Subgroup (G i))
    (x : Πʳ i, [G i, (U i : Set (G i))]) :
    x ∈ integralSubgroup U ↔ ∀ i, x i ∈ U i := by
  simp [integralSubgroup, mem_integralSubgroupOf]

/-- Cutting the reference family out by itself gives the everywhere-integral subgroup. This is the
definition of `integralSubgroup`; it is not a `simp` lemma, since `simp [integralSubgroup]` would
then loop. -/
@[to_additive]
theorem integralSubgroupOf_self (U : ∀ i, Subgroup (G i)) :
    integralSubgroupOf U U = integralSubgroup U :=
  (rfl)

/-- Inside a fixed restricted product, the subgroup cut out by a family `V` is contained in the
one cut out by `V'` exactly when `V i ≤ V' i` at every index: the single-coordinate elements
detect every `V i`. -/
@[to_additive]
theorem integralSubgroupOf_le_integralSubgroupOf_iff (U V V' : ∀ i, Subgroup (G i)) :
    integralSubgroupOf U V ≤ integralSubgroupOf U V' ↔ ∀ i, V i ≤ V' i := by
  classical
  refine ⟨fun h i g hg ↦ ?_, fun h x hx ↦ ?_⟩
  · have hx : RestrictedProduct.mulSingle U i g ∈ integralSubgroupOf U V := by
      refine (mem_integralSubgroupOf U V _).mpr fun j ↦ ?_
      rcases eq_or_ne j i with rfl | hj
      · rwa [RestrictedProduct.mulSingle_eq_same]
      · rw [RestrictedProduct.mulSingle_eq_of_ne _ _ hj]
        exact one_mem _
    simpa using (mem_integralSubgroupOf U V' _).mp (h hx) i
  · rw [mem_integralSubgroupOf] at hx ⊢
    exact fun i ↦ h i (hx i)

/-- The subgroup cut out by a family `V` lies in the everywhere-integral subgroup exactly when
`V i ≤ U i` at every index. -/
@[to_additive]
theorem integralSubgroupOf_le_integralSubgroup_iff (U V : ∀ i, Subgroup (G i)) :
    integralSubgroupOf U V ≤ integralSubgroup U ↔ ∀ i, V i ≤ U i :=
  integralSubgroupOf_le_integralSubgroupOf_iff U V U

variable [∀ i, TopologicalSpace (G i)]

/-- Openness when every `V i` is open and the reference subgroup `U i` lies in `V i` at all but
finitely many indices. -/
@[to_additive]
theorem isOpen_integralSubgroupOf_of_eventually_le (U V : ∀ i, Subgroup (G i))
    (hV : ∀ i, IsOpen (V i : Set (G i))) (hUV : ∀ᶠ i in cofinite, U i ≤ V i) :
    IsOpen (integralSubgroupOf U V : Set (Πʳ i, [G i, (U i : Set (G i))])) := by
  simp_rw +instances [RestrictedProduct.topologicalSpace_eq_iSup cofinite, isOpen_iSup_iff,
    isOpen_coinduced]
  intro T hT
  -- For a point of the restricted product relative to `𝓟 T`, membership in `V i` is automatic
  -- at the indices of `{i | U i ≤ V i} ∩ T`; only finitely many conditions remain.
  have hfin : ({i | U i ≤ V i} ∩ T)ᶜ.Finite := mem_cofinite.mp (hUV.and (le_principal_iff.mp hT))
  convert (isOpen_set_pi hfin fun i _ ↦ hV i).preimage RestrictedProduct.continuous_coe using 1
  ext y
  simp only [Set.mem_preimage, SetLike.mem_coe, mem_integralSubgroupOf, Set.mem_pi]
  refine ⟨fun h i _ ↦ h i, fun h i ↦ ?_⟩
  by_cases hi : i ∈ {i | U i ≤ V i} ∩ T
  · exact hi.1 (y.2 hi.2)
  · exact h i hi

/-- Compactness when every `V i` is compact and lies in the reference subgroup `U i` at all but
finitely many indices. -/
@[to_additive]
theorem isCompact_integralSubgroupOf_of_eventually_le (U V : ∀ i, Subgroup (G i))
    (hV : ∀ i, IsCompact (V i : Set (G i))) (hVU : ∀ᶠ i in cofinite, V i ≤ U i) :
    IsCompact (integralSubgroupOf U V : Set (Πʳ i, [G i, (U i : Set (G i))])) := by
  -- Realize the subgroup as the image of a compact set in the restricted product relative to
  -- `𝓟 S`, where `S` is the cofinite set of indices with `V i ≤ U i`.
  let S : Set ι := {i | V i ≤ U i}
  have hS : cofinite ≤ 𝓟 S := le_principal_iff.mpr hVU
  let Q : Set (∀ i, G i) := Set.univ.pi fun i ↦ (V i : Set (G i))
  have hK : IsCompact (((↑) : Πʳ i, [G i, (U i : Set (G i))]_[𝓟 S] → ∀ i, G i) ⁻¹' Q) := by
    refine RestrictedProduct.isEmbedding_coe_of_principal.isCompact_preimage'
      (isCompact_univ_pi hV) ?_
    rw [RestrictedProduct.range_coe_principal]
    exact fun x hx i hi ↦ hi (hx i trivial)
  convert hK.image (RestrictedProduct.continuous_inclusion hS) using 1
  ext x
  simp only [SetLike.mem_coe, mem_integralSubgroupOf]
  refine ⟨fun hx ↦ ⟨⟨x, fun i hi ↦ hi (hx i)⟩, fun i _ ↦ hx i, rfl⟩, ?_⟩
  rintro ⟨y, hy, rfl⟩
  exact fun i ↦ hy i trivial

/-- Openness of the everywhere-integral subgroup from coordinatewise openness. -/
@[to_additive]
theorem isOpen_integralSubgroup (U : ∀ i, Subgroup (G i))
    (hU : ∀ i, IsOpen (U i : Set (G i))) :
    IsOpen (integralSubgroup U : Set (Πʳ i, [G i, (U i : Set (G i))])) := by
  rw [← integralSubgroupOf_self]
  exact isOpen_integralSubgroupOf_of_eventually_le U U hU (.of_forall fun _ ↦ le_rfl)

/-- Compactness of the everywhere-integral subgroup needs only coordinatewise compactness. -/
@[to_additive]
theorem isCompact_integralSubgroup (U : ∀ i, Subgroup (G i))
    (hK : ∀ i, IsCompact (U i : Set (G i))) :
    IsCompact (integralSubgroup U : Set (Πʳ i, [G i, (U i : Set (G i))])) := by
  rw [← integralSubgroupOf_self]
  exact isCompact_integralSubgroupOf_of_eventually_le U U hK (.of_forall fun _ ↦ le_rfl)

/-- A family of compact open additive subgroups, one in each factor. -/
structure CompactOpenAddSubgroups (G : ι → Type v) [∀ i, AddGroup (G i)]
    [∀ i, TopologicalSpace (G i)] where
  /-- The compact open additive subgroup chosen in each factor. -/
  addSubgroup : ∀ i, OpenAddSubgroup (G i)
  /-- Compactness of the chosen additive subgroup in each factor. -/
  isCompact_addSubgroup : ∀ i, IsCompact (addSubgroup i : Set (G i))

/-- A family of compact open subgroups, one in each factor. -/
@[to_additive CompactOpenAddSubgroups]
structure CompactOpenSubgroups (G : ι → Type v) [∀ i, Group (G i)]
    [∀ i, TopologicalSpace (G i)] where
  /-- The compact open subgroup chosen in each factor. -/
  subgroup : ∀ i, OpenSubgroup (G i)
  /-- Compactness of the chosen subgroup in each factor. -/
  isCompact_subgroup : ∀ i, IsCompact (subgroup i : Set (G i))

@[to_additive (attr := ext)]
theorem CompactOpenSubgroups.ext {K L : CompactOpenSubgroups G}
    (h : K.subgroup = L.subgroup) : K = L := by
  cases K
  cases L
  cases h
  rfl

end TauCeti
