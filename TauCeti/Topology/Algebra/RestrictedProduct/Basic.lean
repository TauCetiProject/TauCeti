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

namespace TauCeti

open Filter
open scoped RestrictedProduct

universe u v

variable {ι : Type u} {G : ι → Type v}
variable [∀ i, Group (G i)]

/-- The subgroup of a restricted product cut out by a second family of subgroups. -/
def integralSubgroupOf (U V : ∀ i, Subgroup (G i)) :
    Subgroup (Πʳ i, [G i, (U i : Set (G i))]) :=
  (Subgroup.pi Set.univ V).comap RestrictedProduct.coeMonoidHom

/-- Membership means that every coordinate belongs to the corresponding subgroup `V i`. -/
@[simp]
theorem mem_integralSubgroupOf (U V : ∀ i, Subgroup (G i))
    (x : Πʳ i, [G i, (U i : Set (G i))]) :
    x ∈ integralSubgroupOf U V ↔ ∀ i, x i ∈ V i := by
  rw [integralSubgroupOf, Subgroup.mem_comap, Subgroup.mem_pi]
  simp [RestrictedProduct.coeMonoidHom]

/-- The subgroup whose coordinates lie in the reference subgroup at every index. -/
def integralSubgroup (U : ∀ i, Subgroup (G i)) :
    Subgroup (Πʳ i, [G i, (U i : Set (G i))]) :=
  integralSubgroupOf U U

/-- Membership means that every coordinate belongs to the reference subgroup `U i`. -/
@[simp]
theorem mem_integralSubgroup (U : ∀ i, Subgroup (G i))
    (x : Πʳ i, [G i, (U i : Set (G i))]) :
    x ∈ integralSubgroup U ↔ ∀ i, x i ∈ U i := by
  simp [integralSubgroup, mem_integralSubgroupOf]

variable [∀ i, TopologicalSpace (G i)]

/-- Openness when the second family agrees with the reference family eventually. -/
theorem isOpen_forall_mem_of_eventually_eq (U V : ∀ i, Subgroup (G i))
    (hV : ∀ i, IsOpen (V i : Set (G i)))
    (hUV : ∀ᶠ i in cofinite, U i = V i) :
    IsOpen (integralSubgroupOf U V : Set (Πʳ i, [G i, (U i : Set (G i))])) := by
  classical
  let S : Set ι := {i | U i = V i}
  have hS : cofinite ≤ 𝓟 S := le_principal_iff.mpr hUV
  have hopenU : IsOpen {x : Πʳ i, [G i, (U i : Set (G i))] |
      ∀ i, i ∈ S → x i ∈ U i} := by
    simp_rw +instances [RestrictedProduct.topologicalSpace_eq_iSup cofinite,
      isOpen_iSup_iff, isOpen_coinduced]
    intro T hT
    have hfinite : (S \ T).Finite :=
      (mem_cofinite.mp (le_principal_iff.mp hT)).subset fun i hi ↦ hi.2
    have hopen : IsOpen ((S \ T : Set ι).pi fun i ↦ (V i : Set (G i))) :=
      isOpen_set_pi hfinite (fun i _ ↦ hV i)
    convert hopen.preimage RestrictedProduct.continuous_coe using 1
    ext x
    constructor
    · intro hx i hi
      have hi' : U i = V i := hi.1
      change x i ∈ V i
      rw [← hi']
      exact hx i hi.1
    · intro hx i hi
      by_cases hiT : i ∈ T
      · exact x.2 hiT
      · have hi' : U i = V i := hi
        change x i ∈ U i
        rw [hi']
        exact hx i ⟨hi, hiT⟩
  have hopenV : IsOpen ((Sᶜ : Set ι).pi fun i ↦ (V i : Set (G i)) :
      Set (∀ i, G i)) :=
    isOpen_set_pi (mem_cofinite.mp hUV) (fun i _ ↦ hV i)
  have hopen := hopenU.inter (hopenV.preimage RestrictedProduct.continuous_coe)
  convert hopen using 1
  ext x
  constructor
  · intro hx
    have hx' := (mem_integralSubgroupOf U V x).mp hx
    constructor
    · exact fun i hi ↦ hi ▸ hx' i
    · exact fun i hi ↦ hx' i
  · rintro ⟨hxS, hxSc⟩
    apply (mem_integralSubgroupOf U V x).mpr
    intro i
    by_cases hi : i ∈ S
    · exact hi ▸ hxS i hi
    · exact hxSc i hi

/-- Compactness when the second family is eventually contained in the reference family. -/
theorem isCompact_forall_mem_of_eventually_subset (U V : ∀ i, Subgroup (G i))
    (hV : ∀ i, IsCompact (V i : Set (G i)))
    (hUV : ∀ᶠ i in cofinite, (V i : Set (G i)) ⊆ (U i : Set (G i))) :
    IsCompact (integralSubgroupOf U V : Set (Πʳ i, [G i, (U i : Set (G i))])) := by
  classical
  let S : Set ι := {i | (V i : Set (G i)) ⊆ (U i : Set (G i))}
  have hS : cofinite ≤ 𝓟 S := le_principal_iff.mpr hUV
  let Q : Set (∀ i, G i) := Set.univ.pi fun i ↦ (V i : Set (G i))
  have hQ : IsCompact Q := isCompact_univ_pi hV
  have hQrange : Q ⊆ Set.range
      ((↑) : (Πʳ i, [G i, (U i : Set (G i))]_[𝓟 S]) → (∀ i : ι, G i)) := by
    rw [RestrictedProduct.range_coe_principal]
    intro x hx i hi
    exact hi (hx i trivial)
  have hK : IsCompact (((↑) :
      (Πʳ i, [G i, (U i : Set (G i))]_[𝓟 S]) → (∀ i : ι, G i)) ⁻¹' Q) :=
    (RestrictedProduct.isEmbedding_coe_of_principal (S := S)).isCompact_preimage' hQ hQrange
  have himage :
      (integralSubgroupOf U V : Set (Πʳ i, [G i, (U i : Set (G i))])) =
        RestrictedProduct.inclusion (fun i ↦ G i) (fun i ↦ (U i : Set (G i))) hS ''
          (((↑) : (Πʳ i, [G i, (U i : Set (G i))]_[𝓟 S]) → (∀ i : ι, G i)) ⁻¹' Q) := by
    ext x
    constructor
    · intro hx
      have hx' := (mem_integralSubgroupOf U V x).mp hx
      refine ⟨⟨x, ?_⟩, ?_, rfl⟩
      · exact fun i hi ↦ hi (hx' i)
      · exact fun i _ ↦ hx' i
    · rintro ⟨y, hy, rfl⟩
      apply (mem_integralSubgroupOf U V _).mpr
      exact fun i ↦ hy i trivial
  rw [himage]
  exact hK.image (RestrictedProduct.continuous_inclusion hS)

/-- Openness of the everywhere-integral subgroup from coordinatewise openness. -/
theorem isOpen_integralSubgroup (U : ∀ i, Subgroup (G i))
    (hU : ∀ i, IsOpen (U i : Set (G i))) :
    IsOpen (integralSubgroup U : Set (Πʳ i, [G i, (U i : Set (G i))])) := by
  simpa [integralSubgroup] using
    isOpen_forall_mem_of_eventually_eq U U hU (.of_forall fun _ ↦ rfl)

/-- Compactness of the everywhere-integral subgroup needs only coordinatewise compactness. -/
theorem isCompact_integralSubgroup (U : ∀ i, Subgroup (G i))
    (hK : ∀ i, IsCompact (U i : Set (G i))) :
    IsCompact (integralSubgroup U : Set (Πʳ i, [G i, (U i : Set (G i))])) := by
  simpa [integralSubgroup] using
    isCompact_forall_mem_of_eventually_subset U U hK (.of_forall fun _ ↦ subset_rfl)

/-- A family of compact open subgroups, one in each factor. -/
structure CompactOpenSubgroups (G : ι → Type v) [∀ i, Group (G i)]
    [∀ i, TopologicalSpace (G i)] where
  /-- The compact open subgroup chosen in each factor. -/
  subgroup : ∀ i, OpenSubgroup (G i)
  /-- Compactness of the chosen subgroup in each factor. -/
  isCompact_subgroup : ∀ i, IsCompact (subgroup i : Set (G i))

@[ext]
theorem CompactOpenSubgroups.ext {K L : CompactOpenSubgroups G}
    (h : K.subgroup = L.subgroup) : K = L := by
  cases K
  cases L
  cases h
  rfl

end TauCeti
