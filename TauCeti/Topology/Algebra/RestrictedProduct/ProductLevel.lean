/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.RestrictedProduct.Basic
public import TauCeti.Topology.Algebra.RestrictedProduct.Principal
import TauCeti.Topology.Algebra.RestrictedProduct.ContinuousRng
import TauCeti.Topology.Algebra.RestrictedProduct.TopologicalSpace

/-!
# Product levels in restricted products

Every compact open subgroup of a restricted product of Hausdorff topological groups contains,
and is contained in, a product of compact open local subgroups equal to the reference subgroups
outside finitely many indices. The inner factors are the inverse images along single-coordinate
inclusions; the outer factors are the coordinate images. Thus these choices require neither
commutativity nor a local basis of compact open subgroups as an extra hypothesis.

Compactness makes integrality uniform outside a finite set. Openness supplies the reverse
inclusion at almost every coordinate. A closed subgroup containing every single-coordinate
part of a point contains that point, by convergence of finite truncations. These facts give
both product comparisons and allow compact adelic levels to be compared with local levels.

## References

* A. Borel, *Some finiteness properties of adele groups over number fields*, §1.7, p. 8.
-/

public section

open Filter Topology
open scoped RestrictedProduct

namespace TauCeti

variable {ι : Type*} {G : ι → Type*} [∀ i, Group (G i)]
  [∀ i, TopologicalSpace (G i)] {B : ∀ i, Subgroup (G i)}

/-- A compact subset of a restricted product lies in one principal level: all its points are
integral outside the same finite set. -/
theorem exists_subset_levelOpenSubgroup_of_isCompact
    (hB : ∀ i, IsOpen (B i : Set (G i))) {C : Set (Πʳ i, [G i, B i])} (hC : IsCompact C) :
    ∃ S : Finset ι, C ⊆ levelOpenSubgroup B S (fun i _ ↦ hB i) := by
  classical
  refine hC.elim_directed_cover (fun S : Finset ι ↦
    (levelOpenSubgroup B S (fun i _ ↦ hB i) : Set (Πʳ i, [G i, B i])))
    (fun S ↦ (levelOpenSubgroup B S _).isOpen) ?_ ?_
  · intro x _
    obtain ⟨S, _, hx⟩ := exists_superset_mem_levelOpenSubgroup B ∅ (fun i _ ↦ hB i) x
    exact Set.mem_iUnion.mpr ⟨S, hx⟩
  · intro S T
    exact ⟨S ∪ T, levelOpenSubgroup_mono B Finset.subset_union_left _ _,
      levelOpenSubgroup_mono B Finset.subset_union_right _ _⟩

/-- For a compact subset, every coordinate is integral at almost every index, uniformly in the
point of that subset. -/
theorem eventually_forall_mem_of_isCompact
    (hB : ∀ i, IsOpen (B i : Set (G i))) {C : Set (Πʳ i, [G i, B i])} (hC : IsCompact C) :
    ∀ᶠ i in cofinite, ∀ x ∈ C, x i ∈ B i := by
  obtain ⟨S, hS⟩ := exists_subset_levelOpenSubgroup_of_isCompact hB hC
  filter_upwards [S.finite_toSet.compl_mem_cofinite] with i hi x hx
  exact (mem_levelOpenSubgroup B S _ x).mp (hS hx) i hi

end TauCeti

namespace Subgroup

open TauCeti

variable {ι : Type*} {G : ι → Type*} [∀ i, Group (G i)]
  [∀ i, TopologicalSpace (G i)] {B : ∀ i, Subgroup (G i)}

/-- A closed subgroup of a restricted product contains a point if it contains that point's
single-coordinate parts. -/
theorem mem_of_forall_mulSingle_mem [DecidableEq ι]
    (U : Subgroup (Πʳ i, [G i, B i])) (hU : IsClosed (U : Set (Πʳ i, [G i, B i])))
    {x : Πʳ i, [G i, B i]} (hx : ∀ i, RestrictedProduct.mulSingle B i (x i) ∈ U) : x ∈ U := by
  let f (S : Finset ι) : Πʳ i, [G i, B i] :=
    ⟨fun i ↦ if i ∈ S then x i else 1,
      Filter.Eventually.mono S.finite_toSet.compl_mem_cofinite fun i hi ↦ by
        dsimp only
        split_ifs with hiS
        · exact (hi hiS).elim
        · exact (B i).one_mem⟩
  have hf (S : Finset ι) : f S ∈ U := by
    induction S using Finset.induction_on with
    | empty =>
      have heq : f ∅ = 1 := by ext i; simp [f]
      rw [heq]
      exact U.one_mem
    | @insert i S hi ih =>
      have heq : f (insert i S) = RestrictedProduct.mulSingle B i (x i) * f S := by
        ext j
        rw [RestrictedProduct.mul_apply]
        by_cases hji : j = i
        · subst j
          simp [f, hi]
        · simp [f, hji, RestrictedProduct.mulSingle_eq_of_ne _ _ hji]
      rw [heq]
      exact U.mul_mem (hx i) ih
  have ht : Tendsto f atTop (𝓝 x) := by
    refine (tendsto_restrictedProduct_iff_of_eventually_mem
      (le_principal_iff.mpr x.eventually) (.of_forall fun S i hi ↦ ?_)).mpr ?_
    · dsimp [f]
      split_ifs
      exacts [hi, (B i).one_mem]
    · intro i
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop ({i} : Finset ι)] with S hS
      simp [f, hS (Finset.mem_singleton_self i)]
  exact hU.mem_of_tendsto ht (.of_forall hf)

/-- Openness of a subgroup forces it to contain the reference subgroup supported at one index
for all but finitely many indices. -/
theorem eventually_le_comap_mulSingle [DecidableEq ι]
    (U : Subgroup (Πʳ i, [G i, B i])) (hU : IsOpen (U : Set (Πʳ i, [G i, B i]))) :
    ∀ᶠ i in cofinite, B i ≤ U.comap (RestrictedProduct.mulSingleMonoidHom B i) := by
  classical
  let g (i : ι) : B i :=
    if h : ∃ a : B i, RestrictedProduct.mulSingle B i a ∉ U then h.choose else 1
  have ht := tendsto_restrictedProduct_mulSingle_cofinite B (fun i ↦ (g i).property)
  have hmem := ht.eventually (hU.mem_nhds U.one_mem)
  filter_upwards [hmem] with i hi a ha
  by_contra hnot
  have hex : ∃ a : B i, RestrictedProduct.mulSingle B i a ∉ U := ⟨⟨a, ha⟩, hnot⟩
  have hbad : RestrictedProduct.mulSingle B i (g i) ∉ U := by
    simpa only [g, dite_eq_left hex] using hex.choose_spec
  exact hbad hi

/-- For a compact open subgroup, both its single-coordinate inverse images and its coordinate
images agree with the reference subgroups at almost every index. -/
theorem eventually_comap_mulSingle_eq_and_map_eval_eq [DecidableEq ι]
    (U : Subgroup (Πʳ i, [G i, B i])) (hU : IsOpen (U : Set (Πʳ i, [G i, B i])))
    (hUc : IsCompact (U : Set (Πʳ i, [G i, B i]))) (hB : ∀ i, IsOpen (B i : Set (G i))) :
    ∀ᶠ i in cofinite,
      U.comap (RestrictedProduct.mulSingleMonoidHom B i) = B i ∧
      U.map (RestrictedProduct.evalMonoidHom G i) = B i := by
  filter_upwards [U.eventually_le_comap_mulSingle hU,
    eventually_forall_mem_of_isCompact hB hUc] with i hle hmem
  have hmap : U.map (RestrictedProduct.evalMonoidHom G i) ≤ B i := by
    rintro g ⟨x, hx, rfl⟩
    exact hmem x hx
  have hcomap : U.comap (RestrictedProduct.mulSingleMonoidHom B i) ≤
      U.map (RestrictedProduct.evalMonoidHom G i) := by
    intro g hg
    exact ⟨RestrictedProduct.mulSingle B i g, hg, by simp⟩
  exact ⟨le_antisymm (hcomap.trans hmap) hle, le_antisymm hmap (hle.trans hcomap)⟩

end Subgroup

namespace TauCeti

variable {ι : Type*} {G : ι → Type*} [∀ i, Group (G i)]
  [∀ i, TopologicalSpace (G i)] [∀ i, T2Space (G i)]
  {B : ∀ i, Subgroup (G i)}

/-- Every compact open subgroup contains a compact open product level, with local factors equal
to the reference subgroups outside a finite set. The factors are its inverse images under the
single-coordinate inclusions. -/
theorem exists_compactOpen_product_le (hB : ∀ i, IsOpen (B i : Set (G i)))
    (U : OpenSubgroup (Πʳ i, [G i, B i])) (hU : IsCompact (U : Set (Πʳ i, [G i, B i]))) :
    ∃ V : ∀ i, Subgroup (G i),
      (∀ i, IsOpen (V i : Set (G i))) ∧ (∀ i, IsCompact (V i : Set (G i))) ∧
      (∀ᶠ i in cofinite, V i = B i) ∧ integralSubgroupOf B V ≤ U.toSubgroup := by
  classical
  refine ⟨fun i ↦ U.toSubgroup.comap (RestrictedProduct.mulSingleMonoidHom B i),
    fun i ↦ U.isOpen.preimage (continuous_restrictedProduct_mulSingle B i),
    fun i ↦ (isClosedEmbedding_restrictedProduct_mulSingle B i).isCompact_preimage hU,
    ?_, ?_⟩
  · exact (U.toSubgroup.eventually_comap_mulSingle_eq_and_map_eval_eq U.isOpen hU hB).mono
      fun _ hi ↦ hi.1
  · intro x hx
    exact U.toSubgroup.mem_of_forall_mulSingle_mem hU.isClosed
      ((mem_integralSubgroupOf B _ x).mp hx)

omit [∀ i, T2Space (G i)] in
/-- Every compact open subgroup is contained in a compact open product level, with local factors
equal to the reference subgroups outside a finite set. The factors are its coordinate images. -/
theorem exists_compactOpen_product_ge (hB : ∀ i, IsOpen (B i : Set (G i)))
    (U : OpenSubgroup (Πʳ i, [G i, B i])) (hU : IsCompact (U : Set (Πʳ i, [G i, B i]))) :
    ∃ V : ∀ i, Subgroup (G i),
      (∀ i, IsOpen (V i : Set (G i))) ∧ (∀ i, IsCompact (V i : Set (G i))) ∧
      (∀ᶠ i in cofinite, V i = B i) ∧ U.toSubgroup ≤ integralSubgroupOf B V := by
  classical
  refine ⟨fun i ↦ U.toSubgroup.map (RestrictedProduct.evalMonoidHom G i),
    fun i ↦ by
      rw [Subgroup.coe_map]
      have he : (RestrictedProduct.evalMonoidHom G i : (Πʳ j, [G j, B j]) → G i) =
          fun x ↦ x i := funext fun x ↦ RestrictedProduct.evalMonoidHom_apply G x i
      rw [he]
      exact isOpenMap_restrictedProduct_eval i _ U.isOpen,
    fun i ↦ hU.image (RestrictedProduct.continuous_eval i), ?_, ?_⟩
  · exact (U.toSubgroup.eventually_comap_mulSingle_eq_and_map_eval_eq U.isOpen hU hB).mono
      fun _ hi ↦ hi.2
  · intro x hx
    exact (mem_integralSubgroupOf B _ x).mpr fun i ↦ ⟨x, hx, rfl⟩

end TauCeti
