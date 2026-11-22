/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.FixedSubmodule
public import TauCeti.LinearAlgebra.RootSystem.Component.Aut
public import TauCeti.LinearAlgebra.RootSystem.OrbitSum.Basic
import TauCeti.Algebra.DirectSum.Internal
import TauCeti.Dynamics.PeriodicPts.Basic
import TauCeti.GroupTheory.Perm.Basic
import TauCeti.GroupTheory.Perm.Cycle.Enumeration

/-!
# Component cycles, return automorphisms, and diagonal orbit-sum transport

For an automorphism `σ` of a root pairing `P` and an irreducible component `C` of cycle length
`c = Function.minimalPeriod σ.componentEquiv C`, `σ ^ c` restricts over a field to the **return
automorphism** `P.componentReturnAut σ C` on `P.componentPairing C`. Summing `σ`-iterates gives the
linear isomorphism `P.componentCycleDiag σ C` onto `P.componentCycleFixedSubmodule σ C`,
transporting orbit sums (`coe_componentCycleDiag_orbitSum`, `componentCycleFoldedIndicesEquiv`),
root spans (`mem_rootSpan_componentCycleDiag_iff`), and direct-sum/product decompositions
(`isInternal_componentCycleFixedSubmodule`, `componentCycleFixedPiEquiv`).

## References

* J. R. Stembridge, *Folding by automorphisms* (2008); N. Bourbaki, *Lie Groups and Lie Algebras*,
  Ch. VI §1, no. 2; G. Lusztig, *Introduction to Quantum Groups* (1993), §14.1.
-/

public section

open Finset Function TauCeti
open _root_.Equiv (Perm)
open _root_.Equiv.Perm (SameCycle)
open scoped DirectSum

namespace RootPairing

/-! ### Component cycles and cycle spaces over a commutative ring -/

section CommRing

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) (σ : P.Aut) (C : P.Component) {D : P.Component}

section FiniteComponent

variable [Finite P.Component]

/-- The **component cycle** of `C` under `σ`: the finset of components on the `σ`-cycle of `C`. -/
noncomputable def componentCycle : Finset P.Component :=
  (Set.toFinite {D | SameCycle σ.componentEquiv C D}).toFinset

variable {P σ C} in
@[simp] theorem mem_componentCycle :
    D ∈ P.componentCycle σ C ↔ SameCycle σ.componentEquiv C D := by simp [componentCycle]

theorem self_mem_componentCycle : C ∈ P.componentCycle σ C :=
  mem_componentCycle.mpr (SameCycle.refl _ _)

theorem card_componentCycle : #(P.componentCycle σ C) = minimalPeriod σ.componentEquiv C := by
  rw [componentCycle, ← Set.ncard_eq_toFinset_card, Perm.ncard_setOf_sameCycle]

theorem card_componentCycle_pos : 0 < #(P.componentCycle σ C) :=
  Finset.card_pos.mpr ⟨C, P.self_mem_componentCycle σ C⟩

theorem minimalPeriod_componentEquiv_pos : 0 < minimalPeriod σ.componentEquiv C :=
  P.card_componentCycle σ C ▸ P.card_componentCycle_pos σ C

variable {P σ C} in
theorem componentCycle_eq_of_mem (h : D ∈ P.componentCycle σ C) :
    P.componentCycle σ D = P.componentCycle σ C := by
  ext E; simp only [mem_componentCycle] at h ⊢; exact ⟨h.trans, h.symm.trans⟩

@[simp] theorem componentCycle_componentEquiv :
    P.componentCycle σ (σ.componentEquiv C) = P.componentCycle σ C :=
  componentCycle_eq_of_mem (mem_componentCycle.mpr ⟨1, by simp⟩)

@[simp] theorem componentCycle_one : P.componentCycle 1 C = {C} := by ext D; simp [eq_comm]

end FiniteComponent

theorem componentEquiv_pow_minimalPeriod :
    (σ ^ minimalPeriod σ.componentEquiv C).componentEquiv C = C := by
  rw [σ.componentEquiv_pow, Perm.coe_pow]; exact isPeriodicPt_minimalPeriod σ.componentEquiv C

theorem minimalPeriod_componentEquiv_pow_apply (k : ℕ) :
    minimalPeriod σ.componentEquiv ((σ ^ k).componentEquiv C) =
      minimalPeriod σ.componentEquiv C :=
  (SameCycle.minimalPeriod_eq ⟨(k : ℤ), by simp [σ.componentEquiv_pow]⟩).symm

/-- The **component-cycle space** of `C` under `σ`: supremum of `P.componentSpace D` on its
`σ`-cycle. -/
def componentCycleSpace : Submodule R M :=
  ⨆ D, ⨆ (_ : SameCycle σ.componentEquiv C D), P.componentSpace D

variable {P σ C} in
theorem componentSpace_le_componentCycleSpace (h : SameCycle σ.componentEquiv C D) :
    P.componentSpace D ≤ P.componentCycleSpace σ C := le_iSup₂_of_le D h le_rfl

theorem self_componentSpace_le_componentCycleSpace :
    P.componentSpace C ≤ P.componentCycleSpace σ C :=
  P.componentSpace_le_componentCycleSpace (SameCycle.refl _ _)

variable {P σ C} in
theorem componentCycleSpace_eq_of_sameCycle (h : SameCycle σ.componentEquiv C D) :
    P.componentCycleSpace σ C = P.componentCycleSpace σ D :=
  le_antisymm
    (iSup₂_le fun _ hCE ↦ P.componentSpace_le_componentCycleSpace (h.symm.trans hCE))
    (iSup₂_le fun _ hDE ↦ P.componentSpace_le_componentCycleSpace (h.trans hDE))

@[simp] theorem componentCycleSpace_componentEquiv :
    P.componentCycleSpace σ (σ.componentEquiv C) = P.componentCycleSpace σ C :=
  (P.componentCycleSpace_eq_of_sameCycle ⟨(1 : ℤ), by simp⟩).symm

@[simp] theorem componentCycleSpace_one : P.componentCycleSpace 1 C = P.componentSpace C :=
  le_antisymm (iSup₂_le fun D hD ↦ (by simpa using hD : C = D) ▸ le_rfl)
    (P.self_componentSpace_le_componentCycleSpace 1 C)

theorem componentCycleSpace_eq_biSup_componentCycle [Finite P.Component] :
    P.componentCycleSpace σ C = ⨆ D ∈ P.componentCycle σ C, P.componentSpace D := by
  simp only [componentCycleSpace, mem_componentCycle]

/-- The component-cycle space is mapped onto itself by `σ.weightMap`. -/
@[simp] theorem map_componentCycleSpace :
    (P.componentCycleSpace σ C).map σ.weightMap = P.componentCycleSpace σ C := by
  have hle (τ : P.Aut) (hτ : ∀ D, SameCycle σ.componentEquiv C D →
      SameCycle σ.componentEquiv C (τ.componentEquiv D)) :
      (P.componentCycleSpace σ C).map τ.weightMap ≤ P.componentCycleSpace σ C := by
    simp only [componentCycleSpace, Submodule.map_iSup]
    exact iSup₂_le fun D hD ↦ Submodule.map_le_iff_le_comap.mpr fun _ hx ↦
      P.componentSpace_le_componentCycleSpace (hτ D hD) (τ.weightMap_mem_componentSpace hx)
  refine le_antisymm (hle σ fun _ ↦ Perm.sameCycle_apply_right.mpr) ?_
  have hcomp : σ.weightMap.comp (σ⁻¹).weightMap = LinearMap.id := by
    ext x; simp [← Equiv.weightEquiv_apply, Equiv.weightEquiv_inv]
  simpa only [← Submodule.map_comp, hcomp, Submodule.map_id] using
    Submodule.map_mono (f := σ.weightMap) (hle σ⁻¹ fun _ hD ↦ by
      rw [σ.componentEquiv_inv, Perm.inv_def]; exact Perm.sameCycle_symm_apply_right.mpr hD)

/-- Distinct exponents below the minimal period produce distinct components along the cycle. -/
theorem pow_componentEquiv_ne_of_ne_lt {r s : ℕ}
    (hr : r < minimalPeriod σ.componentEquiv C) (hs : s < minimalPeriod σ.componentEquiv C)
    (hrs : r ≠ s) : (σ.componentEquiv ^ r) C ≠ (σ.componentEquiv ^ s) C := fun hEq ↦ hrs <| by
  rw [Perm.coe_pow, Perm.coe_pow] at hEq
  exact (iterate_eq_iterate_iff_of_lt_minimalPeriod hr hs).mp hEq

/-- The submodule of `σ`-fixed weights lying in the component-cycle space of `C`. -/
def componentCycleFixedSubmodule : Submodule R (LinearMap.fixedSubmodule σ.weightMap) :=
  (P.componentCycleSpace σ C).comap (LinearMap.fixedSubmodule σ.weightMap).subtype

section ImplicitCycle

variable {P σ C}

/-- Two components on the same `σ`-cycle have the same cycle-fixed submodule. -/
theorem componentCycleFixedSubmodule_eq_of_sameCycle (h : SameCycle σ.componentEquiv C D) :
    P.componentCycleFixedSubmodule σ C = P.componentCycleFixedSubmodule σ D := by
  rw [componentCycleFixedSubmodule, componentCycleFixedSubmodule,
    P.componentCycleSpace_eq_of_sameCycle h]

theorem weightMap_mem_componentCycleSpace {x : M} (hx : x ∈ P.componentCycleSpace σ C) :
    σ.weightMap x ∈ P.componentCycleSpace σ C :=
  P.map_componentCycleSpace σ C ▸ Submodule.mem_map_of_mem hx

theorem pow_weightMap_mem_componentCycleSpace {x : M} (hx : x ∈ P.componentCycleSpace σ C)
    (n : ℕ) : (σ.weightMap ^ n) x ∈ P.componentCycleSpace σ C := by
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    rw [pow_succ', Module.End.mul_eq_comp, LinearMap.comp_apply]
    exact P.weightMap_mem_componentCycleSpace ih

private theorem pow_weightMap_mem_componentSpace {u : M} (hu : u ∈ P.componentSpace C) (r : ℕ) :
    (σ.weightMap ^ r) u ∈ P.componentSpace ((σ.componentEquiv ^ r) C) := by
  rw [← σ.weightMap_pow, ← σ.componentEquiv_pow]; exact (σ ^ r).weightMap_mem_componentSpace hu

@[simp] theorem mem_componentCycleFixedSubmodule {y : LinearMap.fixedSubmodule σ.weightMap} :
    y ∈ P.componentCycleFixedSubmodule σ C ↔ (y : M) ∈ P.componentCycleSpace σ C := Iff.rfl

end ImplicitCycle

/-! #### Cycle independence, projections, and direct-sum decomposition -/

section RootSystem

variable [P.IsRootSystem]

variable {P σ C} in
/-- A vector lies in the component-cycle space of `C` iff its projections onto all components
outside the `σ`-cycle of `C` vanish. -/
theorem mem_componentCycleSpace_iff {x : M} :
    x ∈ P.componentCycleSpace σ C ↔
      ∀ D, ¬SameCycle σ.componentEquiv C D → P.componentProj D x = 0 := by
  refine ⟨fun hx D hD ↦ LinearMap.mem_ker.mp ((iSup₂_le fun _ hCE _ hy ↦ LinearMap.mem_ker.mpr
    (P.componentProj_apply_of_ne (fun (hED : _ = D) ↦ hD (hED ▸ hCE)) hy) :
      P.componentCycleSpace σ C ≤ LinearMap.ker (P.componentProj D)) hx), fun h ↦ ?_⟩
  classical
  let _ := P.isInternal_componentSpace.chooseDecomposition
  rw [← DirectSum.sum_support_decompose P.componentSpace x]
  refine Submodule.sum_mem _ fun D hD ↦
    P.componentSpace_le_componentCycleSpace ?_ (DirectSum.decompose P.componentSpace x D).property
  by_contra hnc
  exact DFinsupp.mem_support_iff.mp hD
    ((P.decompose_componentSpace_eq_componentProj D x).trans (h D hnc))

variable {P σ C} in
theorem componentProj_eq_zero_of_not_sameCycle {x : M} (hx : x ∈ P.componentCycleSpace σ C)
    (hD : ¬SameCycle σ.componentEquiv C D) : P.componentProj D x = 0 :=
  P.mem_componentCycleSpace_iff.mp hx _ hD

omit [P.IsRootSystem] in
private theorem componentCycleSpace_out_eq_iSup
    (O : Quotient (SameCycle.setoid σ.componentEquiv)) :
    P.componentCycleSpace σ O.out =
      ⨆ D : P.Component, ⨆ (_ : (⟦D⟧ : Quotient (SameCycle.setoid σ.componentEquiv)) = O),
        P.componentSpace D := by
  simp only [componentCycleSpace, Perm.sameCycle_out_iff σ.componentEquiv]

/-- **The weight space is the internal direct sum of its component-cycle spaces.** -/
theorem isInternal_componentCycleSpace
    [DecidableEq (Quotient (SameCycle.setoid σ.componentEquiv))] :
    DirectSum.IsInternal fun O : Quotient (SameCycle.setoid σ.componentEquiv) ↦
      P.componentCycleSpace σ O.out := by
  classical
  simpa only [← componentCycleSpace_out_eq_iSup] using
    P.isInternal_componentSpace.iSup_fiber (Quotient.mk (SameCycle.setoid σ.componentEquiv))

/-- **The component-cycle spaces of distinct cycles are independent.** -/
theorem iSupIndep_componentCycleSpace :
    iSupIndep fun O : Quotient (SameCycle.setoid σ.componentEquiv) ↦
      P.componentCycleSpace σ O.out :=
  have _ := Classical.decEq (Quotient (SameCycle.setoid σ.componentEquiv))
  (P.isInternal_componentCycleSpace σ).submodule_iSupIndep

@[simp] theorem iSup_componentCycleSpace :
    (⨆ O : Quotient (SameCycle.setoid σ.componentEquiv), P.componentCycleSpace σ O.out) = ⊤ :=
  have _ := Classical.decEq (Quotient (SameCycle.setoid σ.componentEquiv))
  (P.isInternal_componentCycleSpace σ).submodule_iSup_eq_top

/-- **The fixed space `LinearMap.fixedSubmodule σ.weightMap` is the internal direct sum of the
cycle-fixed submodules.** -/
theorem isInternal_componentCycleFixedSubmodule
    [DecidableEq (Quotient (SameCycle.setoid σ.componentEquiv))] :
    DirectSum.IsInternal fun O : Quotient (SameCycle.setoid σ.componentEquiv) ↦
      P.componentCycleFixedSubmodule σ O.out :=
  (P.isInternal_componentCycleSpace σ).fixedSubmodule_comap σ.weightMap
    fun O ↦ (P.map_componentCycleSpace σ O.out).le

theorem iSupIndep_componentCycleFixedSubmodule :
    iSupIndep fun O : Quotient (SameCycle.setoid σ.componentEquiv) ↦
      P.componentCycleFixedSubmodule σ O.out :=
  haveI := Classical.decEq (Quotient (SameCycle.setoid σ.componentEquiv))
  (P.isInternal_componentCycleFixedSubmodule σ).submodule_iSupIndep

/-- The `C`-projection of any `σ`-fixed weight is fixed by the return iterate `σ ^ c`. -/
theorem pow_minimalPeriod_weightMap_componentProj {x : M} (hσx : σ.weightMap x = x) :
    (σ.weightMap ^ minimalPeriod σ.componentEquiv C) (P.componentProj C x) =
      P.componentProj C x := by
  rw [← σ.coe_componentProj_pow_weightMap _ C x,
    LinearMap.pow_apply_of_mem_fixedSubmodule σ.weightMap
      (LinearMap.mem_fixedSubmodule_iff.mpr hσx),
    ← σ.componentEquiv_pow, P.componentEquiv_pow_minimalPeriod σ C]

section FiniteComp

variable {P σ C} [Finite P.Component]

theorem sum_componentCycle_componentProj_of_mem_componentCycleSpace {x : M}
    (hx : x ∈ P.componentCycleSpace σ C) :
    ∑ D ∈ P.componentCycle σ C, (P.componentProj D x : M) = x := by
  cases nonempty_fintype P.Component
  conv_rhs => rw [← P.sum_componentProj x]
  refine Finset.sum_subset (Finset.subset_univ _) fun D _ hD ↦ ?_
  simp [P.componentProj_eq_zero_of_not_sameCycle hx (mt mem_componentCycle.mpr hD)]

theorem sum_range_componentProj_of_mem_componentCycleSpace {x : M}
    (hx : x ∈ P.componentCycleSpace σ C) :
    ∑ r ∈ range (minimalPeriod σ.componentEquiv C),
        (P.componentProj ((σ.componentEquiv ^ r) C) x : M) = x := by
  classical
  cases nonempty_fintype P.Component
  rw [Perm.sum_range_minimalPeriod σ.componentEquiv (fun D ↦ (P.componentProj D x : M)) C]
  conv_rhs => rw [← P.sum_componentCycle_componentProj_of_mem_componentCycleSpace hx]
  exact Finset.sum_congr (by ext D; simp [mem_componentCycle]) fun _ _ ↦ rfl

/-- **Left-inverse identity for the diagonal cycle sum.** -/
theorem componentProj_sum_range_pow_weightMap {u : M} (hu : u ∈ P.componentSpace C) :
    P.componentProj C (∑ r ∈ range (minimalPeriod σ.componentEquiv C), (σ.weightMap ^ r) u) =
      ⟨u, hu⟩ := by
  rw [map_sum, Finset.sum_eq_single 0]
  · simpa using P.componentProj_apply_of_mem hu
  · intro r hr hr0
    have hne : (σ.componentEquiv ^ r) C ≠ C := by
      simpa using P.pow_componentEquiv_ne_of_ne_lt σ C (Finset.mem_range.mp hr)
        (P.minimalPeriod_componentEquiv_pos σ C) hr0
    exact P.componentProj_apply_of_ne hne (P.pow_weightMap_mem_componentSpace hu r)
  · exact fun h0 ↦ absurd (Finset.mem_range.mpr (P.minimalPeriod_componentEquiv_pos σ C)) h0

/-- **Right-inverse identity for the diagonal cycle sum.** -/
theorem sum_range_pow_weightMap_componentProj {x : M} (hx : x ∈ P.componentCycleSpace σ C)
    (hσx : σ.weightMap x = x) :
    ∑ r ∈ range (minimalPeriod σ.componentEquiv C), (σ.weightMap ^ r) (P.componentProj C x) =
      x := by
  conv_rhs => rw [← P.sum_range_componentProj_of_mem_componentCycleSpace hx]
  exact Finset.sum_congr rfl fun r _ ↦ by
    rw [← σ.coe_componentProj_pow_weightMap r C x,
      LinearMap.pow_apply_of_mem_fixedSubmodule σ.weightMap
        (LinearMap.mem_fixedSubmodule_iff.mpr hσx) r]

end FiniteComp

end RootSystem

/-! #### Orbit-period factorization and folded indices on a component cycle -/

/-- **Orbit-period factorization.** -/
theorem minimalPeriod_indexEquiv_eq_mul (i : ι) :
    minimalPeriod σ.indexEquiv i =
      minimalPeriod σ.componentEquiv (P.componentOf i) *
        minimalPeriod (σ.indexEquiv ^ minimalPeriod σ.componentEquiv (P.componentOf i)) i := by
  have hsemi : Semiconj P.componentOf σ.indexEquiv σ.componentEquiv :=
    fun j ↦ (σ.componentEquiv_componentOf j).symm
  simpa only [Perm.coe_pow] using hsemi.minimalPeriod_eq_mul_iterate i

section FiniteRoots

variable [Finite ι]

/-- The set of `σ`-orbit sums of roots whose component lies in the `σ`-cycle of `C`. -/
noncomputable def componentCycleFoldedIndices : Set M :=
  {x | ∃ j : ι, SameCycle σ.componentEquiv C (P.componentOf j) ∧ P.orbitSum σ j = x}

variable {P σ C} in
theorem mem_componentCycleFoldedIndices {x : M} :
    x ∈ P.componentCycleFoldedIndices σ C ↔
      ∃ j : ι, SameCycle σ.componentEquiv C (P.componentOf j) ∧ P.orbitSum σ j = x := Iff.rfl

variable {P σ C} in
/-- Two components on the same `σ`-cycle have the same set of cycle-folded indices. -/
theorem componentCycleFoldedIndices_eq_of_sameCycle (h : SameCycle σ.componentEquiv C D) :
    P.componentCycleFoldedIndices σ C = P.componentCycleFoldedIndices σ D := by
  ext x
  simp only [mem_componentCycleFoldedIndices]
  exact ⟨fun ⟨j, hj, hx⟩ ↦ ⟨j, h.symm.trans hj, hx⟩, fun ⟨j, hj, hx⟩ ↦ ⟨j, h.trans hj, hx⟩⟩

variable {P σ C} in
theorem orbitSum_mem_componentCycleFoldedIndices_of_mem_supp (i : C.supp) :
    P.orbitSum σ (i : ι) ∈ P.componentCycleFoldedIndices σ C :=
  ⟨i, by
    have hi : P.componentOf (i : ι) = C := (C.mem_supp_iff (i : ι)).mp i.property
    rw [hi], rfl⟩

/-- Every folded vector on the `σ`-cycle of `C` is the `σ`-orbit sum of a root in `C.supp`. -/
theorem componentCycleFoldedIndices_eq_range_supp :
    P.componentCycleFoldedIndices σ C = Set.range fun i : C.supp ↦ P.orbitSum σ (i : ι) := by
  ext x
  refine ⟨?_, fun ⟨i, hi⟩ ↦ hi ▸ P.orbitSum_mem_componentCycleFoldedIndices_of_mem_supp i⟩
  rintro ⟨j, hj, rfl⟩
  obtain ⟨k, hk⟩ := hj.symm.exists_nat_pow_eq
  have hk' : P.componentOf ((σ.indexEquiv ^ k) j) = C := by
    rw [← σ.indexEquiv_pow, ← (σ ^ k).componentEquiv_componentOf, σ.componentEquiv_pow, hk]
  exact ⟨⟨(σ.indexEquiv ^ k) j, hk'⟩,
    P.orbitSum_eq_of_mem (P.mem_orbitIndices_iff_exists_pow.mpr ⟨k, rfl⟩)⟩

theorem componentCycleFoldedIndices_subset_foldedIndices :
    P.componentCycleFoldedIndices σ C ⊆ P.foldedIndices σ :=
  fun _ ⟨j, _, h⟩ ↦ h ▸ P.orbitSum_mem_foldedIndices σ j

theorem componentCycleFoldedIndices_subset_componentCycleSpace :
    P.componentCycleFoldedIndices σ C ⊆ P.componentCycleSpace σ C := by
  rintro _ ⟨j, hj, rfl⟩
  rw [P.orbitSum_def]
  refine Submodule.sum_mem _ fun k hk ↦ ?_
  obtain ⟨r, rfl⟩ := P.mem_orbitIndices_iff_exists_pow.mp hk
  have hcomp : SameCycle σ.componentEquiv C (P.componentOf ((σ.indexEquiv ^ r) j)) := by
    rw [← σ.indexEquiv_pow, ← (σ ^ r).componentEquiv_componentOf, σ.componentEquiv_pow]
    exact hj.trans ⟨(r : ℤ), by simp⟩
  exact P.componentSpace_le_componentCycleSpace hcomp (P.root_mem_componentSpace _)

/-- **The folded indices of `σ` are the union of the cycle-folded indices over all cycles.** -/
theorem iUnion_componentCycleFoldedIndices :
    (⋃ O : Quotient (SameCycle.setoid σ.componentEquiv),
      P.componentCycleFoldedIndices σ O.out) = P.foldedIndices σ :=
  Set.Subset.antisymm
    (Set.iUnion_subset fun O ↦ P.componentCycleFoldedIndices_subset_foldedIndices σ O.out)
    fun _ hx ↦ let ⟨j, hj⟩ := P.mem_foldedIndices.mp hx
      Set.mem_iUnion.mpr ⟨⟦P.componentOf j⟧, j,
        (Perm.sameCycle_out_iff σ.componentEquiv).mpr rfl, hj⟩

variable {P σ} in
/-- **Distinct component cycles contribute disjoint folded sets** when `0 ∉ P.foldedIndices σ`. -/
theorem pairwise_disjoint_componentCycleFoldedIndices [P.IsRootSystem]
    (h0 : 0 ∉ P.foldedIndices σ) :
    Pairwise fun O₁ O₂ : Quotient (SameCycle.setoid σ.componentEquiv) ↦
      Disjoint (P.componentCycleFoldedIndices σ O₁.out)
        (P.componentCycleFoldedIndices σ O₂.out) :=
  fun _ _ hO ↦ Set.disjoint_left.mpr fun x hx₁ hx₂ ↦
    h0 ((Submodule.disjoint_def.mp ((P.iSupIndep_componentCycleSpace σ).pairwiseDisjoint hO) x
      (P.componentCycleFoldedIndices_subset_componentCycleSpace σ _ hx₁)
      (P.componentCycleFoldedIndices_subset_componentCycleSpace σ _ hx₂)) ▸
        P.componentCycleFoldedIndices_subset_foldedIndices σ _ hx₁)

variable {P σ} in
/-- Distinct component cycles contribute disjoint folded sets for a base-preserving `σ`. -/
theorem pairwise_disjoint_componentCycleFoldedIndices_of_base [CharZero R] [P.IsRootSystem]
    {b : P.Base} (hσ : ∀ j ∈ b.support, σ.indexEquiv j ∈ b.support) :
    Pairwise fun O₁ O₂ : Quotient (SameCycle.setoid σ.componentEquiv) ↦
      Disjoint (P.componentCycleFoldedIndices σ O₁.out)
        (P.componentCycleFoldedIndices σ O₂.out) :=
  P.pairwise_disjoint_componentCycleFoldedIndices (P.zero_notMem_foldedIndices hσ)

end FiniteRoots

end CommRing

/-! ### Return automorphism and diagonal transport over a field -/

section Field

variable {ι K M N : Type*} [Field K] [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]

section Finite

variable (P : RootPairing ι K M N) [Finite ι] [P.IsRootSystem] (σ : P.Aut) (C : P.Component)

/-- **The return automorphism of `C`**, restricting `σ ^ c` to `P.componentPairing C`. -/
noncomputable def componentReturnAut : (P.componentPairing C).Aut :=
  (σ ^ minimalPeriod σ.componentEquiv C).restrictComponentAut C
    (P.componentEquiv_pow_minimalPeriod σ C)

@[simp] theorem coe_componentReturnAut_weightMap (u : P.componentSpace C) :
    ((P.componentReturnAut σ C).weightMap u : M) =
      (σ.weightMap ^ minimalPeriod σ.componentEquiv C) u := by simp [componentReturnAut]

@[simp] theorem coe_componentReturnAut_coweightMap (v : P.corootComponentSpace C) :
    ((P.componentReturnAut σ C).coweightMap v : N) =
      (σ ^ minimalPeriod σ.componentEquiv C).coweightMap v := by simp [componentReturnAut]

@[simp] theorem coe_componentReturnAut_indexEquiv (i : C.supp) :
    ((P.componentReturnAut σ C).indexEquiv i : ι) =
      (σ.indexEquiv ^ minimalPeriod σ.componentEquiv C) i := by simp [componentReturnAut]

@[simp] theorem coe_componentReturnAut_indexEquiv_pow (k : ℕ) (i : C.supp) :
    (((P.componentReturnAut σ C).indexEquiv ^ k) i : ι) =
      ((σ.indexEquiv ^ minimalPeriod σ.componentEquiv C) ^ k) i :=
  Semiconj.perm_pow_right (fun j ↦ P.coe_componentReturnAut_indexEquiv σ C j) k i

variable {P σ C} in
/-- When `σ` fixes `C`, the return automorphism is the component restriction of `σ` (`c = 1`). -/
theorem componentReturnAut_of_componentEquiv_eq (hC : σ.componentEquiv C = C) :
    P.componentReturnAut σ C = σ.restrictComponentAut C hC :=
  Equiv.restrictComponentAut_congr (by rw [minimalPeriod_eq_one_iff_isFixedPt.mpr hC, pow_one]) _ hC

@[simp] theorem componentReturnAut_one : P.componentReturnAut 1 C = 1 := by
  rw [componentReturnAut_of_componentEquiv_eq (by simp), Equiv.restrictComponentAut_one]

/-- **Restriction of `P.componentProj C` to `σ`-fixed weights** into the return fixed space. -/
noncomputable def componentCycleFixedProj :
    LinearMap.fixedSubmodule σ.weightMap →ₗ[K]
      LinearMap.fixedSubmodule (P.componentReturnAut σ C).weightMap where
  toFun y := ⟨P.componentProj C (y : M), LinearMap.mem_fixedSubmodule_iff.mpr <| Subtype.ext <| by
    rw [P.coe_componentReturnAut_weightMap]
    exact P.pow_minimalPeriod_weightMap_componentProj σ C
      (LinearMap.mem_fixedSubmodule_iff.mp y.property)⟩
  map_add' x y := Subtype.ext (map_add (P.componentProj C) (x : M) (y : M))
  map_smul' r x := Subtype.ext (map_smul (P.componentProj C) r (x : M))

@[simp] theorem val_componentCycleFixedProj_apply (y : LinearMap.fixedSubmodule σ.weightMap) :
    (P.componentCycleFixedProj σ C y : P.componentSpace C) = P.componentProj C (y : M) := (rfl)

theorem coe_componentCycleFixedProj_apply (y : LinearMap.fixedSubmodule σ.weightMap) :
    ((P.componentCycleFixedProj σ C y : P.componentSpace C) : M) =
      P.componentProj C (y : M) := (rfl)

private theorem sum_range_pow_weightMap_mem_fixedSubmodule
    (u : LinearMap.fixedSubmodule (P.componentReturnAut σ C).weightMap) :
    ∑ r ∈ range (minimalPeriod σ.componentEquiv C), (σ.weightMap ^ r) (u : M) ∈
      LinearMap.fixedSubmodule σ.weightMap :=
  LinearMap.sum_range_pow_apply_mem_fixedSubmodule <|
    (P.coe_componentReturnAut_weightMap σ C u.val).symm.trans
      (congrArg Subtype.val (LinearMap.mem_fixedSubmodule_iff.mp u.property))

/-- **Diagonal transport `u ↦ ∑ r ∈ range c, (σ.weightMap ^ r) u`** from the return fixed space
onto `P.componentCycleFixedSubmodule σ C`, with inverse `P.componentCycleFixedProj σ C`. -/
noncomputable def componentCycleDiag :
    LinearMap.fixedSubmodule (P.componentReturnAut σ C).weightMap ≃ₗ[K]
      P.componentCycleFixedSubmodule σ C where
  toFun u := ⟨⟨∑ r ∈ range (minimalPeriod σ.componentEquiv C), (σ.weightMap ^ r) (u : M),
      P.sum_range_pow_weightMap_mem_fixedSubmodule σ C u⟩, by
    rw [P.mem_componentCycleFixedSubmodule, Submodule.coe_mk]
    exact Submodule.sum_mem _ fun r _ ↦ P.pow_weightMap_mem_componentCycleSpace
      (P.self_componentSpace_le_componentCycleSpace σ C u.val.property) r⟩
  map_add' _ _ := Subtype.ext <| Subtype.ext <| by simp [Finset.sum_add_distrib]
  map_smul' _ _ := Subtype.ext <| Subtype.ext <| by simp [Finset.smul_sum]
  invFun y := P.componentCycleFixedProj σ C y.val
  left_inv u := Subtype.ext (P.componentProj_sum_range_pow_weightMap u.val.property)
  right_inv y := Subtype.ext <| Subtype.ext <|
    P.sum_range_pow_weightMap_componentProj y.property
      (LinearMap.mem_fixedSubmodule_iff.mp y.val.property)

@[simp] theorem componentCycleDiag_symm_apply (y : P.componentCycleFixedSubmodule σ C) :
    (P.componentCycleDiag σ C).symm y = P.componentCycleFixedProj σ C y.val := (rfl)

section DiagApply

variable (u : LinearMap.fixedSubmodule (P.componentReturnAut σ C).weightMap)

theorem coe_componentCycleDiag_apply :
    ((P.componentCycleDiag σ C u : LinearMap.fixedSubmodule σ.weightMap) : M) =
      ∑ r ∈ range (minimalPeriod σ.componentEquiv C), (σ.weightMap ^ r) (u : M) := (rfl)

@[simp] theorem componentProj_componentCycleDiag :
    P.componentProj C ((P.componentCycleDiag σ C u : LinearMap.fixedSubmodule σ.weightMap) : M) =
      (u : P.componentSpace C) :=
  P.componentProj_sum_range_pow_weightMap u.val.property

@[simp] theorem componentCycleFixedProj_componentCycleDiag :
    P.componentCycleFixedProj σ C (P.componentCycleDiag σ C u) = u :=
  (P.componentCycleDiag σ C).symm_apply_apply u

end DiagApply

section ImplicitDiag

variable {P σ C}

theorem componentCycleDiag_componentCycleFixedProj_of_mem
    {y : LinearMap.fixedSubmodule σ.weightMap} (hy : y ∈ P.componentCycleFixedSubmodule σ C) :
    P.componentCycleDiag σ C (P.componentCycleFixedProj σ C y) = ⟨y, hy⟩ :=
  (P.componentCycleDiag σ C).apply_symm_apply ⟨y, hy⟩

theorem componentCycleFixedProj_eq_zero_of_not_sameCycle {D : P.Component}
    (hCD : ¬SameCycle σ.componentEquiv D C) {y : LinearMap.fixedSubmodule σ.weightMap}
    (hy : y ∈ P.componentCycleFixedSubmodule σ D) :
    P.componentCycleFixedProj σ C y = 0 :=
  Subtype.ext (P.componentProj_eq_zero_of_not_sameCycle hy hCD)

/-- When `σ` fixes `C` (`c = 1`), `componentCycleDiag` acts as the identity on ambient vectors. -/
theorem coe_componentCycleDiag_of_componentEquiv_eq (hC : σ.componentEquiv C = C)
    (u : LinearMap.fixedSubmodule (P.componentReturnAut σ C).weightMap) :
    ((P.componentCycleDiag σ C u : LinearMap.fixedSubmodule σ.weightMap) : M) = (u : M) := by
  rw [P.coe_componentCycleDiag_apply, minimalPeriod_eq_one_iff_isFixedPt.mpr hC,
    Finset.sum_range_one, pow_zero, Module.End.one_eq_id, LinearMap.id_apply]

end ImplicitDiag

/-! ### Orbit sizes and distinct orbit-sum transport -/

theorem minimalPeriod_componentReturnAut_indexEquiv (i : C.supp) :
    minimalPeriod (P.componentReturnAut σ C).indexEquiv i =
      minimalPeriod (σ.indexEquiv ^ minimalPeriod σ.componentEquiv C) (i : ι) :=
  Semiconj.minimalPeriod_eq (fb := ⇑(σ.indexEquiv ^ minimalPeriod σ.componentEquiv C))
    (fun j ↦ P.coe_componentReturnAut_indexEquiv σ C j) Subtype.val_injective i

/-- **Minimal period factorization via the return automorphism.** -/
theorem minimalPeriod_indexEquiv_eq_mul_componentReturnAut (i : C.supp) :
    minimalPeriod σ.indexEquiv (i : ι) =
      minimalPeriod σ.componentEquiv C * minimalPeriod (P.componentReturnAut σ C).indexEquiv i := by
  have hi : P.componentOf (i : ι) = C := (C.mem_supp_iff (i : ι)).mp i.property
  rw [P.minimalPeriod_indexEquiv_eq_mul σ (i : ι), hi,
    P.minimalPeriod_componentReturnAut_indexEquiv σ C i]

/-- **Orbit-size factorization** via the return automorphism on `P.componentPairing C`. -/
theorem card_orbitIndices_eq_mul_componentReturnAut (i : C.supp) :
    #(P.orbitIndices σ (i : ι)) =
      minimalPeriod σ.componentEquiv C *
        #((P.componentPairing C).orbitIndices (P.componentReturnAut σ C) i) := by
  rw [P.card_orbitIndices, (P.componentPairing C).card_orbitIndices,
    P.minimalPeriod_indexEquiv_eq_mul_componentReturnAut]

/-- The return orbit sum of `i : C.supp` packaged in the return fixed submodule. -/
noncomputable def componentReturnOrbitSumFixed (i : C.supp) :
    LinearMap.fixedSubmodule (P.componentReturnAut σ C).weightMap :=
  ⟨(P.componentPairing C).orbitSum (P.componentReturnAut σ C) i,
    (P.componentPairing C).orbitSum_mem_fixedSubmodule (P.componentReturnAut σ C) i⟩

@[simp] theorem coe_componentReturnOrbitSumFixed (i : C.supp) :
    (P.componentReturnOrbitSumFixed σ C i : P.componentSpace C) =
      (P.componentPairing C).orbitSum (P.componentReturnAut σ C) i := (rfl)

/-- **Diagonal transport carries return orbit sums to ambient orbit sums.** -/
@[simp] theorem coe_componentCycleDiag_orbitSum (i : C.supp) :
    ((P.componentCycleDiag σ C (P.componentReturnOrbitSumFixed σ C i) :
        LinearMap.fixedSubmodule σ.weightMap) : M) = P.orbitSum σ (i : ι) := by
  rw [P.coe_componentCycleDiag_apply]
  set c := minimalPeriod σ.componentEquiv C
  have hret : ((P.componentReturnOrbitSumFixed σ C i : P.componentSpace C) : M) =
      ∑ q ∈ range (minimalPeriod (P.componentReturnAut σ C).indexEquiv i),
        P.root ((σ.indexEquiv ^ (c * q)) (i : ι)) := by
    rw [coe_componentReturnOrbitSumFixed, (P.componentPairing C).orbitSum_eq_sum_range,
      Submodule.coe_sum]
    exact Finset.sum_congr rfl fun q _ ↦ by
      rw [P.coe_componentPairing_root, P.coe_componentReturnAut_indexEquiv_pow, ← pow_mul]
  rw [hret]
  have hstep r q : (σ.weightMap ^ r) (P.root ((σ.indexEquiv ^ (c * q)) (i : ι))) =
      P.root ((σ.indexEquiv ^ (c * q + r)) (i : ι)) := by
    rw [← σ.weightMap_pow, Hom.root_weightMap_apply P P _ (σ ^ r).toHom, σ.indexEquiv_pow,
      Nat.add_comm, pow_add, Perm.mul_apply]
  simp_rw [map_sum, hstep]
  rw [Finset.sum_comm, ← Finset.sum_range_mul_eq_sum_sum (fun l ↦ P.root ((σ.indexEquiv ^ l) i)),
    ← P.minimalPeriod_indexEquiv_eq_mul_componentReturnAut σ C i, ← P.orbitSum_eq_sum_range]

/-- Two roots in `C.supp` have equal ambient orbit sums iff they have equal return orbit sums. -/
theorem orbitSum_eq_iff_componentReturnAut (i j : C.supp) :
    P.orbitSum σ (i : ι) = P.orbitSum σ (j : ι) ↔
      (P.componentPairing C).orbitSum (P.componentReturnAut σ C) i =
        (P.componentPairing C).orbitSum (P.componentReturnAut σ C) j := by
  rw [← P.coe_componentCycleDiag_orbitSum σ C i, ← P.coe_componentCycleDiag_orbitSum σ C j]
  exact ⟨fun h ↦ congrArg Subtype.val ((P.componentCycleDiag σ C).injective
      (Subtype.ext (Subtype.ext h))),
    fun h ↦ congrArg (fun u ↦ ((P.componentCycleDiag σ C u : _) : M)) (Subtype.ext h)⟩

/-- **Bijection of distinct folded root vectors on a component cycle.** -/
noncomputable def componentCycleFoldedIndicesEquiv :
    (P.componentPairing C).foldedIndices (P.componentReturnAut σ C) ≃
      P.componentCycleFoldedIndices σ C where
  toFun v := ⟨((P.componentCycleDiag σ C
      ⟨v.val, (P.componentPairing C).foldedIndices_subset_fixedSubmodule
        (P.componentReturnAut σ C) v.property⟩ :
        LinearMap.fixedSubmodule σ.weightMap) : M), by
    obtain ⟨i, hi⟩ := (P.componentPairing C).mem_foldedIndices.mp v.property
    have hEq : (⟨v.val, (P.componentPairing C).foldedIndices_subset_fixedSubmodule
          (P.componentReturnAut σ C) v.property⟩ :
        LinearMap.fixedSubmodule (P.componentReturnAut σ C).weightMap) =
        P.componentReturnOrbitSumFixed σ C i := Subtype.ext hi.symm
    rw [hEq, P.coe_componentCycleDiag_orbitSum]
    exact P.orbitSum_mem_componentCycleFoldedIndices_of_mem_supp i⟩
  invFun w := ⟨P.componentProj C w.val, by
    obtain ⟨i, hi⟩ : w.val ∈ Set.range fun i : C.supp ↦ P.orbitSum σ (i : ι) :=
      P.componentCycleFoldedIndices_eq_range_supp σ C ▸ w.property
    dsimp only at hi
    refine (P.componentPairing C).mem_foldedIndices.mpr ⟨i, ?_⟩
    rw [← hi, ← P.coe_componentCycleDiag_orbitSum σ C i, P.componentProj_componentCycleDiag,
      P.coe_componentReturnOrbitSumFixed]⟩
  left_inv v := Subtype.ext (P.componentProj_sum_range_pow_weightMap v.val.property)
  right_inv w := Subtype.ext <| by
    obtain ⟨i, hi⟩ : w.val ∈ Set.range fun i : C.supp ↦ P.orbitSum σ (i : ι) :=
      P.componentCycleFoldedIndices_eq_range_supp σ C ▸ w.property
    dsimp only at hi
    exact P.sum_range_pow_weightMap_componentProj
      (P.componentCycleFoldedIndices_subset_componentCycleSpace σ C w.property)
      (hi ▸ P.weightMap_orbitSum_self σ (i : ι))

@[simp] theorem coe_componentCycleFoldedIndicesEquiv_apply
    (v : (P.componentPairing C).foldedIndices (P.componentReturnAut σ C)) :
    (P.componentCycleFoldedIndicesEquiv σ C v : M) =
      ((P.componentCycleDiag σ C ⟨v.val,
        (P.componentPairing C).foldedIndices_subset_fixedSubmodule
          (P.componentReturnAut σ C) v.property⟩ :
          LinearMap.fixedSubmodule σ.weightMap) : M) := (rfl)

theorem coe_componentCycleFoldedIndicesEquiv_apply_eq_sum
    (v : (P.componentPairing C).foldedIndices (P.componentReturnAut σ C)) :
    (P.componentCycleFoldedIndicesEquiv σ C v : M) =
      ∑ r ∈ range (minimalPeriod σ.componentEquiv C), (σ.weightMap ^ r) (v.val : M) := (rfl)

@[simp] theorem coe_componentCycleFoldedIndicesEquiv_symm_apply
    (w : P.componentCycleFoldedIndices σ C) :
    ((P.componentCycleFoldedIndicesEquiv σ C).symm w : P.componentSpace C) =
      P.componentProj C w.val := (rfl)

/-! ### Independence of the starting component and product assembly across cycles -/

/-- **Changing the starting component conjugates the return automorphism.** -/
theorem autCongr_componentReturnAut_pow (k : ℕ) :
    ((σ ^ k).componentPairingEquiv C).autCongr (P.componentReturnAut σ C) =
      P.componentReturnAut σ ((σ ^ k).componentEquiv C) := by
  rw [componentReturnAut, (σ ^ k).autCongr_restrictComponentAut, componentReturnAut]
  refine Equiv.restrictComponentAut_congr ?_ _ _
  rw [Equiv.autCongr_apply, P.minimalPeriod_componentEquiv_pow_apply σ C k, ← Equiv.comp_assoc,
    ← Equiv.mul_eq_comp (σ ^ k), (Commute.pow_pow_self σ k _).eq, Equiv.mul_eq_comp,
    Equiv.comp_assoc, Equiv.self_comp_symm, Equiv.id_comp]

/-- Shift of return fixed vectors from `C` to `(σ ^ k).componentEquiv C` via `σ.weightMap ^ k`. -/
noncomputable def componentReturnFixedShift (k : ℕ) :
    LinearMap.fixedSubmodule (P.componentReturnAut σ C).weightMap ≃ₗ[K]
      LinearMap.fixedSubmodule (P.componentReturnAut σ ((σ ^ k).componentEquiv C)).weightMap :=
  (((σ ^ k).componentPairingEquiv C).weightEquiv).fixedSubmoduleCongr <| by
    ext u
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      Equiv.weightEquiv_apply, Equiv.coe_componentPairingEquiv_weightMap_apply,
      coe_componentReturnAut_weightMap, minimalPeriod_componentEquiv_pow_apply, σ.weightMap_pow]
    rw [← LinearMap.comp_apply, ← Module.End.mul_eq_comp,
      (Commute.pow_pow_self σ.weightMap k _).eq, Module.End.mul_eq_comp, LinearMap.comp_apply]

@[simp] theorem coe_componentReturnFixedShift_apply (k : ℕ)
    (u : LinearMap.fixedSubmodule (P.componentReturnAut σ C).weightMap) :
    ((P.componentReturnFixedShift σ C k u : P.componentSpace ((σ ^ k).componentEquiv C)) : M) =
      (σ.weightMap ^ k) (u : M) := by
  simp [componentReturnFixedShift]

/-- Projecting a `σ`-fixed weight to `(σ ^ k).componentEquiv C` shifts its `C`-projection. -/
theorem componentCycleFixedProj_pow (k : ℕ) (y : LinearMap.fixedSubmodule σ.weightMap) :
    P.componentCycleFixedProj σ ((σ ^ k).componentEquiv C) y =
      P.componentReturnFixedShift σ C k (P.componentCycleFixedProj σ C y) :=
  Subtype.ext <| Subtype.ext <| by
    rw [P.coe_componentReturnFixedShift_apply, P.coe_componentCycleFixedProj_apply,
      P.coe_componentCycleFixedProj_apply, σ.componentEquiv_pow,
      ← σ.coe_componentProj_pow_weightMap k C (y : M),
      LinearMap.pow_apply_of_mem_fixedSubmodule σ.weightMap y.property k]

/-- **Independence of the starting component** for `componentCycleDiag`. -/
theorem coe_componentCycleDiag_componentReturnFixedShift (k : ℕ)
    (u : LinearMap.fixedSubmodule (P.componentReturnAut σ C).weightMap) :
    ((P.componentCycleDiag σ ((σ ^ k).componentEquiv C)
        (P.componentReturnFixedShift σ C k u) : LinearMap.fixedSubmodule σ.weightMap) : M) =
      ((P.componentCycleDiag σ C u : LinearMap.fixedSubmodule σ.weightMap) : M) := by
  set y : LinearMap.fixedSubmodule σ.weightMap := (P.componentCycleDiag σ C u).val
  have hy : y ∈ P.componentCycleFixedSubmodule σ ((σ ^ k).componentEquiv C) := by
    rw [mem_componentCycleFixedSubmodule, ← P.componentCycleSpace_eq_of_sameCycle
      (⟨(k : ℤ), by simp [σ.componentEquiv_pow]⟩ : SameCycle σ.componentEquiv C _)]
    exact (P.componentCycleDiag σ C u).property
  have hproj : P.componentReturnFixedShift σ C k u =
      P.componentCycleFixedProj σ ((σ ^ k).componentEquiv C) y := by
    rw [P.componentCycleFixedProj_pow σ C k y, P.componentCycleFixedProj_componentCycleDiag]
  rw [hproj, P.componentCycleDiag_componentCycleFixedProj_of_mem hy]

/-- **Product decomposition of the full `σ`-fixed weight space across all component cycles.** -/
noncomputable def componentCycleFixedPiEquiv :
    LinearMap.fixedSubmodule σ.weightMap ≃ₗ[K]
      ∀ O : Quotient (SameCycle.setoid σ.componentEquiv),
        LinearMap.fixedSubmodule (P.componentReturnAut σ O.out).weightMap := by
  haveI := Fintype.ofFinite (Quotient (SameCycle.setoid σ.componentEquiv))
  exact
    { toFun y O := P.componentCycleFixedProj σ O.out y
      map_add' x y := funext fun O ↦ map_add (P.componentCycleFixedProj σ O.out) x y
      map_smul' r x := funext fun O ↦ map_smul (P.componentCycleFixedProj σ O.out) r x
      invFun f := ∑ O, (P.componentCycleDiag σ O.out (f O)).val
      left_inv y := Subtype.ext <| by
        cases nonempty_fintype P.Component
        simp only [Submodule.coe_sum, coe_componentCycleDiag_apply,
          coe_componentCycleFixedProj_apply]
        simp_rw [← σ.coe_componentProj_pow_weightMap _ _ (y : M),
          LinearMap.pow_apply_of_mem_fixedSubmodule σ.weightMap y.property]
        rw [Perm.sum_quotient_sameCycle_sum_range σ.componentEquiv
          (fun D ↦ (P.componentProj D (y : M) : M))]
        exact P.sum_componentProj (y : M)
      right_inv f := funext fun O ↦ by
        dsimp only; rw [map_sum, Finset.sum_eq_single O (fun O' _ hO' ↦
          P.componentCycleFixedProj_eq_zero_of_not_sameCycle
            (fun hsc ↦ hO' (by rw [← (Perm.sameCycle_out_iff σ.componentEquiv).mp hsc,
              Quotient.out_eq])) (P.componentCycleDiag σ O'.out (f O')).property) (by simp)]
        exact P.componentCycleFixedProj_componentCycleDiag σ O.out (f O) }

@[simp] theorem componentCycleFixedPiEquiv_apply (y : LinearMap.fixedSubmodule σ.weightMap)
    (O : Quotient (SameCycle.setoid σ.componentEquiv)) :
    P.componentCycleFixedPiEquiv σ y O = P.componentCycleFixedProj σ O.out y := (rfl)

theorem coe_componentCycleFixedPiEquiv_symm_apply
    [Fintype (Quotient (SameCycle.setoid σ.componentEquiv))]
    (f : ∀ O : Quotient (SameCycle.setoid σ.componentEquiv),
      LinearMap.fixedSubmodule (P.componentReturnAut σ O.out).weightMap) :
    ((P.componentCycleFixedPiEquiv σ).symm f : M) =
      ∑ O, ((P.componentCycleDiag σ O.out (f O) : LinearMap.fixedSubmodule σ.weightMap) : M) := by
  obtain rfl : ‹Fintype (Quotient (SameCycle.setoid σ.componentEquiv))› =
      Fintype.ofFinite _ := Subsingleton.elim _ _
  simp [componentCycleFixedPiEquiv]

end Finite

section

variable (P : RootPairing ι K M N) [Finite ι] [P.IsRootSystem]

/-- An additive submonoid invariant under `σ.weightMap` and `P.componentProj C` is preserved by
`componentCycleDiag`. -/
theorem mem_addSubmonoid_componentCycleDiag_iff (A : AddSubmonoid M) {σ : P.Aut}
    (hstep : ∀ {x}, x ∈ A → σ.weightMap x ∈ A) (C : P.Component)
    (hproj : ∀ {x}, x ∈ A → (P.componentProj C x : M) ∈ A)
    (u : LinearMap.fixedSubmodule (P.componentReturnAut σ C).weightMap) :
    ((P.componentCycleDiag σ C u : LinearMap.fixedSubmodule σ.weightMap) : M) ∈ A ↔
      (u : M) ∈ A := by
  have hpow (r : ℕ) {x : M} (hx : x ∈ A) : (σ.weightMap ^ r) x ∈ A := by
    induction r with
    | zero => simpa using hx
    | succ r ih => rw [pow_succ', Module.End.mul_eq_comp, LinearMap.comp_apply]; exact hstep ih
  refine ⟨fun hD ↦ ?_, fun hu ↦ ?_⟩
  · have h := hproj hD; rwa [P.componentProj_componentCycleDiag] at h
  · rw [P.coe_componentCycleDiag_apply]; exact AddSubmonoid.sum_mem _ fun r _ ↦ hpow r hu

/-- **Root-lattice preservation under `componentCycleDiag`** for any compatible scalar ring `S`. -/
theorem mem_rootSpan_componentCycleDiag_iff (S : Type*) [CommRing S] [Module S M]
    [LinearMap.CompatibleSMul M M S K] (σ : P.Aut) (C : P.Component)
    (u : LinearMap.fixedSubmodule (P.componentReturnAut σ C).weightMap) :
    ((P.componentCycleDiag σ C u : LinearMap.fixedSubmodule σ.weightMap) : M) ∈ P.rootSpan S ↔
      (u : M) ∈ P.rootSpan S :=
  P.mem_addSubmonoid_componentCycleDiag_iff (P.rootSpan S).toAddSubmonoid
    (fun {x} hx ↦ (Submodule.span_le.mpr (Set.range_subset_iff.mpr fun j ↦ by
      rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.restrictScalars_apply,
        Hom.root_weightMap_apply P P j σ.toHom]
      exact (P.rootSpanMem S _).property) :
        P.rootSpan S ≤ (P.rootSpan S).comap (σ.weightMap.restrictScalars S)) hx)
    C (fun hx ↦ P.componentProj_mem_rootSpan S C hx) u

end

end Field

end RootPairing
