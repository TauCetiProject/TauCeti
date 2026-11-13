/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.LinearAlgebra.RootSystem.Hom
public import Mathlib.LinearAlgebra.RootSystem.Irreducible
public import Mathlib.LinearAlgebra.RootSystem.RootPositive

/-!
# Irreducible components of a root pairing

Join two distinct roots when they are not orthogonal. The connected components of this graph are
the **irreducible components** of the root pairing, and the span of the roots in a component is its
**component space**. The definitions use neither a base nor any finiteness, so the resulting
partition of the roots is intrinsic, and any equivalence of root pairings carries it to the
corresponding partition.

Roots in different components are orthogonal. This makes the component spaces of a root system
independent, with sum the whole space, puts each root in exactly one of them when `2 ≠ 0`, shows
that the reflection at any root preserves each of them, and, over a domain with `2 ≠ 0`, makes them
orthogonal under every invariant form. Over a field in which `2` is invertible it follows that a
root system is irreducible exactly when its graph is connected.

## Main definitions

* `RootPairing.nonorthogonalGraph`: the graph on the roots joining non-orthogonal pairs.
* `RootPairing.Component`: the connected components of this graph.
* `RootPairing.componentSpace`, `RootPairing.corootComponentSpace`: the spans of the roots and of
  the coroots in a component.
* `RootPairing.Equiv.nonorthogonalGraphIso`: the graph isomorphism induced by an equivalence.

## Main results

* `RootPairing.isInternal_componentSpace`: a root system is the internal direct sum of its component
  spaces.
* `RootPairing.root_mem_componentSpace_iff`: when `2 ≠ 0`, a root lies in exactly the component
  space of its own component.
* `RootPairing.componentSpace_mem_invtSubmodule`: component spaces are invariant under reflections.
* `RootPairing.InvariantForm.apply_eq_zero_of_mem_componentSpace`: over a domain with `2 ≠ 0`,
  different component spaces are orthogonal under every invariant form.
* `RootPairing.Equiv.map_componentSpace`, `RootPairing.Equiv.map_corootComponentSpace`: an
  equivalence carries component spaces to component spaces, and likewise for coroots.
* `RootPairing.isIrreducible_iff_connected_nonorthogonalGraph`: irreducibility is connectedness of
  the graph.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4-6*, Ch. VI §1, no. 2.
* J. S. Milne, *Algebraic Groups*, Cambridge University Press (2017), Appendix C, C.23 and C.55.
-/

public section

open Module.End (invtSubmodule)
open Submodule (span span_le subset_span)

namespace RootPairing

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N)

/-- The **non-orthogonality graph** of a root pairing: two distinct roots are joined when they are
not orthogonal. When `2 ≠ 0`, a root is joined to its negative whenever that is a different
root. -/
def nonorthogonalGraph : SimpleGraph ι :=
  SimpleGraph.fromRel fun i j ↦ ¬ P.IsOrthogonal i j

@[simp]
theorem nonorthogonalGraph_adj {i j : ι} :
    P.nonorthogonalGraph.Adj i j ↔ i ≠ j ∧ ¬ P.IsOrthogonal i j := by
  rw [nonorthogonalGraph, SimpleGraph.fromRel_adj, P.isOrthogonal_symm (i := j) (j := i)]
  tauto

/-- The **irreducible components** of a root pairing: the connected components of its
non-orthogonality graph. -/
abbrev Component : Type _ := P.nonorthogonalGraph.ConnectedComponent

/-- The irreducible component containing a given root. -/
abbrev componentOf (i : ι) : P.Component := P.nonorthogonalGraph.connectedComponentMk i

/-- The **component space** of an irreducible component: the span of its roots. -/
def componentSpace (C : P.Component) : Submodule R M := span R (P.root '' C.supp)

/-- The span of the coroots of an irreducible component. -/
def corootComponentSpace (C : P.Component) : Submodule R N := span R (P.coroot '' C.supp)

theorem componentSpace_def (C : P.Component) : P.componentSpace C = span R (P.root '' C.supp) :=
  (rfl)

theorem corootComponentSpace_def (C : P.Component) :
    P.corootComponentSpace C = span R (P.coroot '' C.supp) :=
  (rfl)

variable {P}

/-- Roots indexed, along an injective map, by vertices in different components of the pulled-back
non-orthogonality graph are orthogonal. -/
theorem isOrthogonal_of_connectedComponentMk_comap_ne {V : Type*} {f : V → ι}
    (hf : Function.Injective f) {u v : V}
    (h : (P.nonorthogonalGraph.comap f).connectedComponentMk u ≠
      (P.nonorthogonalGraph.comap f).connectedComponentMk v) :
    P.IsOrthogonal (f u) (f v) := by
  by_contra huv
  have hne : u ≠ v := by
    rintro rfl
    exact h rfl
  refine h (SimpleGraph.ConnectedComponent.sound (SimpleGraph.Adj.reachable ?_))
  exact SimpleGraph.comap_adj.mpr (P.nonorthogonalGraph_adj.mpr ⟨hf.ne hne, huv⟩)

/-- Roots in different irreducible components are orthogonal. -/
theorem isOrthogonal_of_componentOf_ne {i j : ι} (h : P.componentOf i ≠ P.componentOf j) :
    P.IsOrthogonal i j :=
  isOrthogonal_of_connectedComponentMk_comap_ne Function.injective_id h

/-- Roots with a nonzero pairing lie in the same irreducible component. -/
theorem componentOf_eq_of_pairing_ne_zero {i j : ι} (h : P.pairing i j ≠ 0) :
    P.componentOf i = P.componentOf j := by
  by_contra hij
  exact h (isOrthogonal_of_componentOf_ne hij).1

/-- A reflection permutes the roots of each irreducible component. -/
@[simp]
theorem componentOf_reflectionPerm (i j : ι) :
    P.componentOf (P.reflectionPerm i j) = P.componentOf j := by
  by_cases h : P.pairing j i = 0
  · rw [P.reflectionPerm_eq_of_pairing_eq_zero h]
  · rw [componentOf_eq_of_pairing_ne_zero h, componentOf_eq_of_pairing_ne_zero (j := i)]
    rwa [← P.pairing_reflectionPerm, P.pairing_reflectionPerm_self_right, neg_ne_zero]

theorem root_mem_componentSpace_of_mem_supp {C : P.Component} {i : ι} (hi : i ∈ C.supp) :
    P.root i ∈ P.componentSpace C :=
  subset_span ⟨i, hi, rfl⟩

theorem coroot_mem_corootComponentSpace_of_mem_supp {C : P.Component} {i : ι} (hi : i ∈ C.supp) :
    P.coroot i ∈ P.corootComponentSpace C :=
  subset_span ⟨i, hi, rfl⟩

theorem root_mem_componentSpace (i : ι) : P.root i ∈ P.componentSpace (P.componentOf i) :=
  root_mem_componentSpace_of_mem_supp rfl

theorem coroot_mem_corootComponentSpace (i : ι) :
    P.coroot i ∈ P.corootComponentSpace (P.componentOf i) :=
  coroot_mem_corootComponentSpace_of_mem_supp rfl

/-- A coroot outside an irreducible component kills its component space. -/
theorem coroot'_eq_zero_of_mem_componentSpace {C : P.Component} {j : ι} (hj : P.componentOf j ≠ C)
    {x : M} (hx : x ∈ P.componentSpace C) : P.coroot' j x = 0 := by
  have hle : P.componentSpace C ≤ LinearMap.ker (P.coroot' j) := by
    refine span_le.mpr ?_
    rintro _ ⟨i, rfl, rfl⟩
    exact (isOrthogonal_of_componentOf_ne (Ne.symm hj)).1
  exact hle hx

/-- A root outside an irreducible component kills its coroot space. -/
theorem root'_eq_zero_of_mem_corootComponentSpace {C : P.Component} {j : ι}
    (hj : P.componentOf j ≠ C) {y : N} (hy : y ∈ P.corootComponentSpace C) : P.root' j y = 0 := by
  have hle : P.corootComponentSpace C ≤ LinearMap.ker (P.root' j) := by
    refine span_le.mpr ?_
    rintro _ ⟨i, rfl, rfl⟩
    exact (isOrthogonal_of_componentOf_ne hj).1
  exact hle hy

/-- **The component spaces of a root system are independent.** A vector in one of them and in the
sum of the others is killed by every coroot, since each coroot lies outside one of the two. -/
theorem iSupIndep_componentSpace [P.IsRootSystem] : iSupIndep P.componentSpace := by
  refine fun C ↦ Submodule.disjoint_def.mpr fun x hx hx' ↦ ?_
  refine P.eq_zero_iff_forall_coroot'_eq_zero.mpr fun j ↦ ?_
  by_cases hj : P.componentOf j = C
  · have hle : ⨆ D, ⨆ (_ : D ≠ C), P.componentSpace D ≤ LinearMap.ker (P.coroot' j) :=
      iSup₂_le fun D hD _ hy ↦ coroot'_eq_zero_of_mem_componentSpace (hj.trans_ne hD.symm) hy
    exact hle hx'
  · exact coroot'_eq_zero_of_mem_componentSpace hj hx

/-- The component spaces together span the same submodule as all the roots. -/
theorem iSup_componentSpace : ⨆ C, P.componentSpace C = P.rootSpan R := by
  refine le_antisymm (iSup_le fun C ↦ Submodule.span_mono (Set.image_subset_range _ _)) ?_
  refine span_le.mpr ?_
  rintro _ ⟨i, rfl⟩
  exact (le_iSup P.componentSpace (P.componentOf i)) (root_mem_componentSpace i)

/-- **A root system is the internal direct sum of its component spaces.** -/
theorem isInternal_componentSpace [DecidableEq P.Component] [P.IsRootSystem] :
    DirectSum.IsInternal P.componentSpace :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top iSupIndep_componentSpace
    (iSup_componentSpace.trans IsRootSystem.span_root_eq_top)

/-- **Each root lies in exactly one component space**: that of its own component. -/
@[simp]
theorem root_mem_componentSpace_iff [NeZero (2 : R)] {i : ι} {C : P.Component} :
    P.root i ∈ P.componentSpace C ↔ P.componentOf i = C := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ root_mem_componentSpace i⟩
  by_contra hi
  have := coroot'_eq_zero_of_mem_componentSpace hi h
  rw [root_coroot'_eq_pairing, pairing_same] at this
  exact two_ne_zero this

/-- Each coroot lies in exactly one coroot component space: that of its own component. -/
@[simp]
theorem coroot_mem_corootComponentSpace_iff [NeZero (2 : R)] {i : ι} {C : P.Component} :
    P.coroot i ∈ P.corootComponentSpace C ↔ P.componentOf i = C := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ coroot_mem_corootComponentSpace i⟩
  by_contra hi
  have := root'_eq_zero_of_mem_corootComponentSpace hi h
  rw [root'_coroot_eq_pairing, pairing_same] at this
  exact two_ne_zero this

/-- **Component spaces are invariant under every reflection.** The reflection at a root of the
component preserves its span; the reflection at any other root fixes it pointwise. -/
theorem componentSpace_mem_invtSubmodule (C : P.Component) (i : ι) :
    P.componentSpace C ∈ invtSubmodule (P.reflection i) := by
  by_cases hi : P.componentOf i = C
  · exact Submodule.mem_invtSubmodule_reflection_of_mem _ _ (hi ▸ root_mem_componentSpace i)
  · refine (Module.End.mem_invtSubmodule _).mpr fun x hx ↦ ?_
    rw [Submodule.mem_comap, LinearEquiv.coe_coe, reflection_apply,
      coroot'_eq_zero_of_mem_componentSpace hi hx, zero_smul, sub_zero]
    exact hx

/-- **Different component spaces are orthogonal under every invariant form.** -/
theorem InvariantForm.apply_eq_zero_of_mem_componentSpace [IsDomain R] [NeZero (2 : R)]
    (B : P.InvariantForm) {C D : P.Component} (hCD : C ≠ D) {x y : M}
    (hx : x ∈ P.componentSpace C) (hy : y ∈ P.componentSpace D) : B.form x y = 0 := by
  have hle : Submodule.map₂ B.form (P.componentSpace C) (P.componentSpace D) ≤ ⊥ := by
    rw [componentSpace_def, componentSpace_def, Submodule.map₂_span_span, span_le,
      Set.image2_subset_iff]
    rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
    refine (B.apply_root_root_zero_iff i j).mpr (isOrthogonal_of_componentOf_ne ?_).1
    exact ((C.mem_supp_iff i).mp hi).trans_ne (hCD.trans_eq ((D.mem_supp_iff j).mp hj).symm)
  exact (Submodule.mem_bot R).mp (hle (Submodule.apply_mem_map₂ _ hx hy))

/-! ### Transport along equivalences -/

section Equiv

variable {ι₂ M₂ N₂ : Type*} [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
  {Q : RootPairing ι₂ R M₂ N₂}

/-- An equivalence of root pairings is an isomorphism of non-orthogonality graphs, along its
bijection of root indices. -/
def Equiv.nonorthogonalGraphIso (e : P.Equiv Q) : P.nonorthogonalGraph ≃g Q.nonorthogonalGraph where
  toEquiv := e.indexEquiv
  map_rel_iff' {i j} := by
    simp only [nonorthogonalGraph_adj, IsOrthogonal, e.toHom.pairing,
      e.indexEquiv.apply_eq_iff_eq, ne_eq]

@[simp]
theorem Equiv.nonorthogonalGraphIso_apply (e : P.Equiv Q) (i : ι) :
    e.nonorthogonalGraphIso i = e.indexEquiv i :=
  (rfl)

/-- The bijection of irreducible components induced by an equivalence of root pairings. -/
def Equiv.componentEquiv (e : P.Equiv Q) : P.Component ≃ Q.Component :=
  e.nonorthogonalGraphIso.connectedComponentEquiv

@[simp]
theorem Equiv.componentEquiv_componentOf (e : P.Equiv Q) (i : ι) :
    e.componentEquiv (P.componentOf i) = Q.componentOf (e.indexEquiv i) :=
  (rfl)

@[simp]
theorem Equiv.componentEquiv_symm_componentOf (e : P.Equiv Q) (i : ι₂) :
    e.componentEquiv.symm (Q.componentOf i) = P.componentOf (e.indexEquiv.symm i) :=
  e.componentEquiv.symm_apply_eq.mpr (by simp)

theorem Equiv.indexEquiv_mem_supp_iff (e : P.Equiv Q) {C : P.Component} {i : ι} :
    e.indexEquiv i ∈ (e.componentEquiv C).supp ↔ i ∈ C.supp := by
  simp only [SimpleGraph.ConnectedComponent.mem_supp_iff, ← e.componentEquiv_componentOf,
    e.componentEquiv.apply_eq_iff_eq]

/-- **An equivalence of root pairings carries component spaces to component spaces.** -/
theorem Equiv.map_componentSpace (e : P.Equiv Q) (C : P.Component) :
    (P.componentSpace C).map e.weightEquiv.toLinearMap = Q.componentSpace (e.componentEquiv C) := by
  rw [componentSpace_def, componentSpace_def, Submodule.map_span]
  congr 1
  ext x
  simp only [Set.mem_image, LinearEquiv.coe_coe, exists_exists_and_eq_and]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨e.indexEquiv i, e.indexEquiv_mem_supp_iff.mpr hi,
      (Hom.root_weightMap_apply P Q i e.toHom).symm⟩
  · rintro ⟨i, hi, rfl⟩
    refine ⟨e.indexEquiv.symm i, ?_, ?_⟩
    · exact e.indexEquiv_mem_supp_iff.mp (by simpa using hi)
    · simpa using Hom.root_weightMap_apply P Q (e.indexEquiv.symm i) e.toHom

/-- An equivalence of root pairings carries coroot component spaces to coroot component spaces. -/
theorem Equiv.map_corootComponentSpace (e : P.Equiv Q) (C : P.Component) :
    (Q.corootComponentSpace (e.componentEquiv C)).map e.coweightEquiv.toLinearMap =
      P.corootComponentSpace C := by
  rw [corootComponentSpace_def, corootComponentSpace_def, Submodule.map_span]
  congr 1
  ext x
  simp only [Set.mem_image, LinearEquiv.coe_coe, exists_exists_and_eq_and, coweightEquiv_apply]
  constructor
  · rintro ⟨i, hi, rfl⟩
    refine ⟨e.indexEquiv.symm i, ?_, ?_⟩
    · exact e.indexEquiv_mem_supp_iff.mp (by simpa using hi)
    · exact (Hom.coroot_coweightMap_apply P Q i e.toHom).symm
  · rintro ⟨i, hi, rfl⟩
    exact ⟨e.indexEquiv i, e.indexEquiv_mem_supp_iff.mpr hi,
      by simpa using Hom.coroot_coweightMap_apply P Q (e.indexEquiv i) e.toHom⟩

end Equiv

/-! ### Irreducibility -/

section Field

variable {K : Type*} [Field K] [NeZero (2 : K)] [Module K M] [Module K N]
  {P : RootPairing ι K M N}

/-- **A root system is irreducible exactly when its non-orthogonality graph is connected.**

The empty root system lives on the zero module, so it is not irreducible, and its graph is not
connected because it has no vertices. -/
theorem isIrreducible_iff_connected_nonorthogonalGraph [P.IsRootSystem] :
    P.IsIrreducible ↔ P.nonorthogonalGraph.Connected := by
  constructor
  · intro hP
    have hne : Nonempty ι := by
      by_contra! hι
      have := hP.nontrivial
      obtain ⟨x, hx⟩ := exists_ne (0 : M)
      have htop : x ∈ span K (Set.range P.root) := by
        rw [IsRootSystem.span_root_eq_top]
        exact Submodule.mem_top
      rw [Set.range_eq_empty, Submodule.span_empty, Submodule.mem_bot] at htop
      exact hx htop
    refine { preconnected := fun i j ↦ ?_, nonempty := hne }
    have htop : P.componentSpace (P.componentOf i) = ⊤ :=
      IsIrreducible.eq_top_of_invtSubmodule_reflection _
        (componentSpace_mem_invtSubmodule _) fun hbot ↦ P.ne_zero i (by
          simpa [hbot] using root_mem_componentSpace (P := P) i)
    have hj : P.root j ∈ P.componentSpace (P.componentOf i) := htop ▸ Submodule.mem_top
    exact (SimpleGraph.ConnectedComponent.exact (root_mem_componentSpace_iff.mp hj)).symm
  · intro hc
    obtain ⟨i⟩ := hc.nonempty
    have : Nontrivial M := ⟨P.root i, 0, P.ne_zero i⟩
    refine IsIrreducible.mk' P fun q hinv hq ↦
      P.eq_top_of_mem_invtSubmodule_of_forall_eq_univ q hq hinv fun Φ hΦ hroot hker ↦ ?_
    obtain ⟨j, hj⟩ := hΦ
    -- `Φ` is stable under adjacency: outside `Φ`, a coroot kills `q` and so the roots of `Φ`.
    have step {j k : ι} (hadj : P.nonorthogonalGraph.Adj j k) (hj : j ∈ Φ) : k ∈ Φ := by
      by_contra hk
      have hzero : P.pairing j k = 0 := by
        have := hker k hk (hroot ⟨j, hj, rfl⟩)
        rwa [LinearMap.mem_ker, root_coroot'_eq_pairing] at this
      exact (P.nonorthogonalGraph_adj.mp hadj).2 ⟨hzero, P.pairing_eq_zero_iff'.mp hzero⟩
    refine Set.eq_univ_of_forall fun k ↦ ?_
    obtain ⟨w⟩ := hc.preconnected j k
    induction w with
    | nil => exact hj
    | cons hadj _ ih => exact ih (step hadj hj)

end Field

end RootPairing
