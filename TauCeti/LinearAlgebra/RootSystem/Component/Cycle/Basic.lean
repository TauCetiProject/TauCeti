/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.FixedSubmodule
public import TauCeti.LinearAlgebra.RootSystem.Component.Base
public import TauCeti.LinearAlgebra.RootSystem.OrbitSum.Basic
import TauCeti.Algebra.DirectSum.Internal
import TauCeti.Dynamics.PeriodicPts.Basic
import TauCeti.GroupTheory.Perm.Basic
import TauCeti.GroupTheory.Perm.Cycle.Enumeration
import TauCeti.LinearAlgebra.FixedSubmodule.DirectSum

/-!
# Component cycles of a root-pairing automorphism and their return maps

An automorphism `σ` of a finite root system `P` over a field permutes its irreducible components
(`RootPairing.Equiv.componentEquiv`). Let `C` be a component and `c` the length of its cycle
`C, σC, …, σᶜ⁻¹C`, the minimal period of `C`. Then `σᶜ` maps `C` to itself and restricts, by
`RootPairing.Equiv.componentPairingEquiv`, to an automorphism `τ` of the component pairing of `C`,
the **return map** `RootPairing.Equiv.componentReturn σ C`.

The cycle sum `D x = ∑_{r < c} σʳ x` (`RootPairing.Equiv.componentCycleSum`) carries `τ`-fixed
vectors of the component space of `C` to `σ`-fixed vectors (`RootPairing.Equiv.componentCycleMap`),
transports orbit sums (`RootPairing.Equiv.componentCycleSum_orbitSum`), and induces an internal
direct-sum decomposition `RootPairing.isInternal_componentCycleFixedSubmodule` across cycles.
See `TauCeti.LinearAlgebra.RootSystem.Component.Cycle.Diag` for the diagonal isomorphism
`RootPairing.componentCycleDiag` and the cycle-wise product decomposition.

## Main definitions

* `RootPairing.componentCycle`: the finset of components on the `σ`-cycle of `C`.
* `RootPairing.componentCycleSpace`, `RootPairing.componentCycleFixedSubmodule`: the span of the
  component spaces on the `σ`-cycle of `C` and its `σ`-fixed submodule.
* `RootPairing.Equiv.componentCycleSum`, `RootPairing.Equiv.componentCycleMap`: the cycle sum on
  weights and on fixed vectors.
* `RootPairing.Equiv.componentReturn`: the return map of a component under an automorphism.
* `RootPairing.componentCycleFoldedIndices`: folded root vectors on a component cycle.

## References

* J. R. Stembridge, *Folding by automorphisms*, note of 20 August 2008, p. 1.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4-6*, Ch. VI §1, no. 2.
* G. Lusztig, *Introduction to Quantum Groups* (1993), §14.1.
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

section CyclePeriod

variable {P : RootPairing ι R M N} (σ : P.Aut) (C : P.Component)

namespace Equiv

/-- The power `σᶜ`, for `c` the length of the cycle of `C`, maps `C` to itself. -/
theorem componentEquiv_pow_minimalPeriod :
    (σ ^ minimalPeriod σ.componentEquiv C).componentEquiv C = C := by
  rw [componentEquiv_pow, Equiv.Perm.coe_pow]
  exact isPeriodicPt_minimalPeriod _ _

/-- The cycle of a component has positive length. -/
theorem minimalPeriod_componentEquiv_pos [Finite P.Component] :
    0 < minimalPeriod σ.componentEquiv C :=
  minimalPeriod_pos_of_mem_periodicPts (σ.componentEquiv.injective.mem_periodicPts C)

/-- The components `σʳC`, `r` below the length of the cycle of `C`, are distinct. -/
theorem componentEquiv_pow_injOn :
    (Set.Iio (minimalPeriod σ.componentEquiv C)).InjOn fun r ↦ (σ ^ r).componentEquiv C := by
  simpa only [componentEquiv_pow, Equiv.Perm.coe_pow] using iterate_injOn_Iio_minimalPeriod

end Equiv

end CyclePeriod

section CycleLemmas

variable (P : RootPairing ι R M N) (σ : P.Aut) (C : P.Component) {D : P.Component}

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

variable {P σ C} in
theorem componentCycle_eq_of_mem (h : D ∈ P.componentCycle σ C) :
    P.componentCycle σ D = P.componentCycle σ C := by
  ext E; simp only [mem_componentCycle] at h ⊢; exact ⟨h.trans, h.symm.trans⟩

@[simp] theorem componentCycle_componentEquiv :
    P.componentCycle σ (σ.componentEquiv C) = P.componentCycle σ C :=
  componentCycle_eq_of_mem (mem_componentCycle.mpr ⟨1, by simp⟩)

@[simp] theorem componentCycle_one : P.componentCycle 1 C = {C} := by ext D; simp [eq_comm]

end FiniteComponent

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
  rw [pow_apply_eq_iterate]
  exact Set.MapsTo.iterate (fun _ h ↦ P.weightMap_mem_componentCycleSpace h) n hx

@[simp] theorem mem_componentCycleFixedSubmodule {y : LinearMap.fixedSubmodule σ.weightMap} :
    y ∈ P.componentCycleFixedSubmodule σ C ↔ (y : M) ∈ P.componentCycleSpace σ C := Iff.rfl

end ImplicitCycle

end CycleLemmas

/-! ### The cycle sum -/

section CycleSum

variable {P : RootPairing ι R M N}

namespace Equiv

variable (σ : P.Aut) (C : P.Component)

/-- The **cycle sum** of the component `C` under `σ`: the linear map `x ↦ ∑_{r < c} σʳ x`, where
`c` is the length of the cycle of `C` under the permutation of the components induced by `σ`. -/
noncomputable def componentCycleSum : M →ₗ[R] M :=
  ∑ r ∈ range (minimalPeriod σ.componentEquiv C), (σ ^ r).toHom.weightMap

theorem componentCycleSum_apply (x : M) :
    σ.componentCycleSum C x =
      ∑ r ∈ range (minimalPeriod σ.componentEquiv C), (σ ^ r).toHom.weightMap x := by
  rw [componentCycleSum, LinearMap.sum_apply]

variable {σ C}

/-- The cycle sum of a vector fixed by `σᶜ` is fixed by `σ`. -/
theorem componentCycleSum_mem_fixedSubmodule {x : M}
    (hx : (σ ^ minimalPeriod σ.componentEquiv C).toHom.weightMap x = x) :
    σ.componentCycleSum C x ∈ LinearMap.fixedSubmodule σ.weightMap := by
  rw [componentCycleSum_apply]
  simp_rw [σ.weightMap_pow] at hx ⊢
  exact LinearMap.sum_range_pow_apply_mem_fixedSubmodule hx

end Equiv

end CycleSum

/-! #### Cycle independence, projections, and direct-sum decomposition -/

section RootSystem

variable (P : RootPairing ι R M N) (σ : P.Aut) (C : P.Component) [P.IsRootSystem]

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
    ← σ.componentEquiv_pow, σ.componentEquiv_pow_minimalPeriod C]

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
  have hpos := Equiv.minimalPeriod_componentEquiv_pos σ C
  rw [map_sum, Finset.sum_eq_single_of_mem 0 (mem_range.mpr hpos)]
  · simp [P.componentProj_apply_of_mem hu]
  · intro r hr hr0
    refine P.componentProj_apply_of_ne (fun h ↦ hr0 ?_)
      (σ.pow_weightMap_mem_componentSpace hu r)
    exact σ.componentEquiv_pow_injOn C (mem_range.mp hr) hpos
      (by simpa [σ.componentEquiv_pow] using h)

/-- **Projection inverts the cycle sum on the component.** The projection onto the component space
of `C` of the cycle sum of a vector of that component space is the vector itself. -/
theorem Equiv.componentProj_componentCycleSum {x : M} (hx : x ∈ P.componentSpace C) :
    P.componentProj C (σ.componentCycleSum C x) = ⟨x, hx⟩ := by
  simpa [Equiv.componentCycleSum_apply, σ.weightMap_pow] using
    P.componentProj_sum_range_pow_weightMap hx

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

section FoldedIndices

variable (P : RootPairing ι R M N) (σ : P.Aut) (C : P.Component) {D : P.Component}

/-- `P.componentOf` semiconjugates `σ.indexEquiv` to `σ.componentEquiv`. -/
theorem semiconj_componentOf : Semiconj P.componentOf σ.indexEquiv σ.componentEquiv :=
  fun j ↦ (σ.componentEquiv_componentOf j).symm

/-- **Orbit-period factorization.** -/
theorem minimalPeriod_indexEquiv_eq_mul (i : ι) :
    minimalPeriod σ.indexEquiv i =
      minimalPeriod σ.componentEquiv (P.componentOf i) *
        minimalPeriod (σ.indexEquiv ^ minimalPeriod σ.componentEquiv (P.componentOf i)) i := by
  simpa only [Perm.coe_pow] using (P.semiconj_componentOf σ).minimalPeriod_eq_mul_iterate i

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
  ⟨i, by have hi : P.componentOf (i : ι) = C := (C.mem_supp_iff _).mp i.property; rw [hi], rfl⟩

/-- Every folded vector on the `σ`-cycle of `C` is the `σ`-orbit sum of a root in `C.supp`. -/
theorem componentCycleFoldedIndices_eq_range_supp :
    P.componentCycleFoldedIndices σ C = Set.range fun i : C.supp ↦ P.orbitSum σ (i : ι) := by
  ext x
  refine ⟨?_, fun ⟨i, hi⟩ ↦ hi ▸ P.orbitSum_mem_componentCycleFoldedIndices_of_mem_supp i⟩
  rintro ⟨j, hj, rfl⟩
  obtain ⟨k, hk⟩ := hj.symm.exists_nat_pow_eq
  have hk' : P.componentOf ((σ.indexEquiv ^ k) j) = C :=
    ((P.semiconj_componentOf σ).perm_pow_right k j).trans hk
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
  exact P.componentSpace_le_componentCycleSpace
    (((P.semiconj_componentOf σ).perm_pow_right r j).symm ▸ hj.trans ⟨(r : ℤ), by simp⟩)
    (P.root_mem_componentSpace _)

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

end FoldedIndices

end CommRing

/-! ### The return map of a component cycle and diagonal transport over a field -/

section Field

variable {ι K M N : Type*} [Field K] [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]

section ReturnMap

variable {P : RootPairing ι K M N} [Finite ι] [P.IsRootSystem]

namespace Equiv

variable (σ : P.Aut) (C : P.Component)

/-- The **return map** of the component `C` under `σ`: the restriction to the component pairing of
`C` of `σᶜ`, where `c` is the length of the cycle of `C` under the permutation of the components
induced by `σ`. -/
noncomputable def componentReturn : (P.componentPairing C).Aut :=
  (σ ^ minimalPeriod σ.componentEquiv C).componentPairingEquiv C
    (componentEquiv_pow_minimalPeriod σ C)

theorem componentReturn_def :
    σ.componentReturn C =
      (σ ^ minimalPeriod σ.componentEquiv C).componentPairingEquiv C
        (componentEquiv_pow_minimalPeriod σ C) := by
  rw [componentReturn]

@[simp]
theorem coe_componentReturn_weightMap_apply (x : P.componentSpace C) :
    ((σ.componentReturn C).toHom.weightMap x : M) =
      (σ ^ minimalPeriod σ.componentEquiv C).toHom.weightMap x :=
  coe_componentPairingEquiv_weightMap_apply _ C _ x

@[simp]
theorem coe_componentReturn_coweightMap_apply (y : P.corootComponentSpace C) :
    ((σ.componentReturn C).toHom.coweightMap y : N) =
      (σ ^ minimalPeriod σ.componentEquiv C).toHom.coweightMap y :=
  coe_componentPairingEquiv_coweightMap_apply _ C _ y

@[simp]
theorem coe_componentReturn_indexEquiv_apply (i : C.supp) :
    ((σ.componentReturn C).indexEquiv i : ι) =
      (σ.indexEquiv ^ minimalPeriod σ.componentEquiv C) i := by
  rw [componentReturn, coe_componentPairingEquiv_indexEquiv_apply, indexEquiv_pow]

@[simp]
theorem coe_componentReturn_indexEquiv_symm_apply (i : C.supp) :
    ((σ.componentReturn C).indexEquiv.symm i : ι) =
      (σ.indexEquiv ^ minimalPeriod σ.componentEquiv C).symm (i : ι) := by
  rw [componentReturn, coe_componentPairingEquiv_indexEquiv_symm_apply, indexEquiv_pow]

/-- The `k`-th power of the return map moves a root of `C` by `σᶜᵏ`. -/
theorem coe_componentReturn_indexEquiv_pow_apply (k : ℕ) (i : C.supp) :
    (((σ.componentReturn C).indexEquiv ^ k) i : ι) =
      (σ.indexEquiv ^ (minimalPeriod σ.componentEquiv C * k)) i := by
  rw [pow_mul, Equiv.Perm.coe_pow, Equiv.Perm.coe_pow (σ.indexEquiv ^ _)]
  exact Semiconj.iterate_right (fun j ↦ coe_componentReturn_indexEquiv_apply σ C j) k i

variable {σ C} in
/-- When `σ` fixes `C`, the return map is the component restriction of `σ` (`c = 1`). -/
theorem componentReturn_of_componentEquiv_eq (hC : σ.componentEquiv C = C) :
    σ.componentReturn C = σ.componentPairingEquiv C hC :=
  Equiv.componentPairingEquiv_congr
    (by rw [minimalPeriod_eq_one_iff_isFixedPt.mpr hC, pow_one]) _ hC

@[simp]
theorem componentReturn_one : (1 : P.Aut).componentReturn C = 1 := by
  rw [componentReturn_of_componentEquiv_eq (by simp), Equiv.componentPairingEquiv_one]

/-- The members of the orbit of a root of `C` under the return map are the iterates `σᶜᵏ` of that
root. -/
theorem mem_orbitIndices_componentReturn_iff {i j : C.supp} :
    j ∈ (P.componentPairing C).orbitIndices (σ.componentReturn C) i ↔
      ∃ k : ℕ, (σ.indexEquiv ^ (minimalPeriod σ.componentEquiv C * k)) i = j := by
  rw [mem_orbitIndices_iff_exists_pow]
  exact exists_congr fun k ↦ by rw [← Subtype.coe_inj, coe_componentReturn_indexEquiv_pow_apply]

/-! #### Orbits and orbit sums along a component cycle -/

/-- The images under `σʳ`, `r` below the length of the cycle of `C`, of the orbit of a root of `C`
under the return map are pairwise disjoint: they lie in the distinct components `σʳC`. -/
theorem pairwiseDisjoint_map_orbitIndices_componentReturn (i : C.supp) :
    (range (minimalPeriod σ.componentEquiv C) : Set ℕ).PairwiseDisjoint fun r ↦
      (((P.componentPairing C).orbitIndices (σ.componentReturn C) i).map
        (Embedding.subtype _)).map (σ ^ r).indexEquiv.toEmbedding := by
  intro r hr s hs hrs
  refine disjoint_left.mpr fun j hjr hjs ↦ hrs ?_
  simp only [mem_map, Embedding.coe_subtype, _root_.Equiv.coe_toEmbedding] at hjr hjs
  obtain ⟨_, ⟨t, -, rfl⟩, rfl⟩ := hjr
  obtain ⟨_, ⟨t', -, rfl⟩, ht'⟩ := hjs
  have hmem {u : C.supp} {n : ℕ} : (σ ^ n).indexEquiv u ∈ ((σ ^ n).componentEquiv C).supp :=
    (σ ^ n).indexEquiv_mem_supp_iff.mpr u.prop
  refine componentEquiv_pow_injOn σ C (mem_range.mp hr) (mem_range.mp hs) ?_
  dsimp only
  rw [← (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mp (hmem (u := t) (n := r)), ← ht',
    (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mp (hmem (u := t') (n := s))]

/-- **The `σ`-orbit of a root of `C` is the union of the `σʳ`-images of its orbit under the return
map**, for `r` below the length of the cycle of `C`; the union is disjoint by
`RootPairing.Equiv.pairwiseDisjoint_map_orbitIndices_componentReturn`. -/
theorem orbitIndices_eq_biUnion [DecidableEq ι] (i : C.supp) :
    P.orbitIndices σ i = (range (minimalPeriod σ.componentEquiv C)).biUnion fun r ↦
      (((P.componentPairing C).orbitIndices (σ.componentReturn C) i).map
        (Embedding.subtype _)).map (σ ^ r).indexEquiv.toEmbedding := by
  ext j
  simp only [mem_biUnion, mem_range, mem_map, Embedding.coe_subtype,
    _root_.Equiv.coe_toEmbedding, indexEquiv_pow, mem_orbitIndices_iff_exists_pow]
  constructor
  · rintro ⟨n, rfl⟩
    refine ⟨n % minimalPeriod σ.componentEquiv C,
      Nat.mod_lt _ (minimalPeriod_componentEquiv_pos σ C), _,
      ⟨_, ⟨n / minimalPeriod σ.componentEquiv C, rfl⟩, rfl⟩, ?_⟩
    rw [coe_componentReturn_indexEquiv_pow_apply, ← Equiv.Perm.mul_apply, ← pow_add,
      Nat.mod_add_div]
  · rintro ⟨r, -, _, ⟨_, ⟨k, rfl⟩, rfl⟩, rfl⟩
    exact ⟨r + minimalPeriod σ.componentEquiv C * k, by
      rw [coe_componentReturn_indexEquiv_pow_apply, pow_add, Equiv.Perm.mul_apply]⟩

/-- **Orbit sizes along a component cycle.** The `σ`-orbit of a root of `C` has `c` times as many
members as its orbit under the return map, where `c` is the length of the cycle of `C`. -/
theorem card_orbitIndices_eq_mul (i : C.supp) :
    #(P.orbitIndices σ i) = minimalPeriod σ.componentEquiv C *
      #((P.componentPairing C).orbitIndices (σ.componentReturn C) i) := by
  classical
  rw [orbitIndices_eq_biUnion,
    card_biUnion (pairwiseDisjoint_map_orbitIndices_componentReturn σ C i)]
  simp

/-- **The cycle sum carries orbit sums of the return map to orbit sums of `σ`.** For a root of `C`,
the cycle sum of its orbit sum under the return map is its orbit sum under `σ`. -/
theorem componentCycleSum_orbitSum (i : C.supp) :
    σ.componentCycleSum C ((P.componentPairing C).orbitSum (σ.componentReturn C) i) =
      P.orbitSum σ i := by
  classical
  rw [orbitSum_def P σ, orbitIndices_eq_biUnion,
    sum_biUnion (pairwiseDisjoint_map_orbitIndices_componentReturn σ C i), componentCycleSum_apply]
  refine sum_congr rfl fun r _ ↦ ?_
  rw [sum_map, sum_map, orbitSum_def, Submodule.coe_sum, map_sum]
  refine sum_congr rfl fun t _ ↦ ?_
  rw [coe_componentPairing_root]
  exact Hom.root_weightMap_apply P P t (σ ^ r).toHom

/-- The cycle sum of a vector fixed by `σ` projected onto the component space of `C` is the sum of
the projections of that vector onto the component spaces `σʳC` of the cycle of `C`. -/
theorem componentCycleSum_componentProj {x : M} (hx : x ∈ LinearMap.fixedSubmodule σ.weightMap) :
    σ.componentCycleSum C (P.componentProj C x) =
      ∑ r ∈ range (minimalPeriod σ.componentEquiv C),
        (P.componentProj ((σ ^ r).componentEquiv C) x : M) := by
  rw [componentCycleSum_apply]
  refine sum_congr rfl fun r _ ↦ ?_
  rw [← coe_componentPairingEquiv_weightMap_apply (σ ^ r) C rfl,
    componentPairingEquiv_weightMap_componentProj, weightMap_pow,
    LinearMap.pow_apply_of_mem_fixedSubmodule _ hx]

/-- The projection onto the component space of `C` of a vector fixed by `σ` is fixed by the return
map of `C`. -/
theorem componentProj_mem_fixedSubmodule_componentReturn {x : M}
    (hx : x ∈ LinearMap.fixedSubmodule σ.weightMap) :
    P.componentProj C x ∈ LinearMap.fixedSubmodule (σ.componentReturn C).toHom.weightMap := by
  rw [LinearMap.mem_fixedSubmodule_iff, componentReturn,
    componentPairingEquiv_weightMap_componentProj, weightMap_pow,
    LinearMap.pow_apply_of_mem_fixedSubmodule _ hx]

/-! #### The cycle sum on fixed vectors -/

/-- The **cycle sum on fixed vectors**: the cycle sum `x ↦ ∑_{r < c} σʳ x` of the component `C`,
`c` the length of its cycle, as a linear map from the vectors of the component space of `C` fixed
by the return map to the vectors fixed by `σ`. -/
noncomputable def componentCycleMap :
    LinearMap.fixedSubmodule (σ.componentReturn C).toHom.weightMap →ₗ[K]
      LinearMap.fixedSubmodule σ.toHom.weightMap :=
  ((σ.componentCycleSum C).comp ((P.componentSpace C).subtype.comp
    (LinearMap.fixedSubmodule _).subtype)).codRestrict _ fun u ↦
      componentCycleSum_mem_fixedSubmodule <| by
        simpa using congrArg Subtype.val (LinearMap.mem_fixedSubmodule_iff.mp u.prop)

@[simp]
theorem coe_componentCycleMap_apply
    (u : LinearMap.fixedSubmodule (σ.componentReturn C).toHom.weightMap) :
    (σ.componentCycleMap C u : M) = σ.componentCycleSum C (u : P.componentSpace C) :=
  (rfl)

/-- The cycle sum on fixed vectors carries the orbit sum of a root of `C` under the return map to
its orbit sum under `σ`. -/
theorem componentCycleMap_orbitSum (i : C.supp) :
    σ.componentCycleMap C ⟨_, (P.componentPairing C).orbitSum_mem_fixedSubmodule _ i⟩ =
      ⟨_, P.orbitSum_mem_fixedSubmodule σ i⟩ :=
  Subtype.ext (componentCycleSum_orbitSum σ C i)

/-- Projection onto the component space of `C` is a left inverse of the cycle sum on fixed
vectors. -/
theorem componentProj_componentCycleMap
    (u : LinearMap.fixedSubmodule (σ.componentReturn C).toHom.weightMap) :
    P.componentProj C (σ.componentCycleMap C u) = u :=
  componentProj_componentCycleSum (u : P.componentSpace C).prop

/-- The cycle sum on fixed vectors is injective. -/
theorem componentCycleMap_injective : Injective (σ.componentCycleMap C) :=
  fun u v h ↦ Subtype.ext <| by
    rw [← componentProj_componentCycleMap σ C u, h, componentProj_componentCycleMap]

end Equiv

end ReturnMap

end Field

namespace Base

variable {ι K M N : Type*} [Field K] [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  {P : RootPairing ι K M N} [Finite ι] [P.IsRootSystem]
  (b : P.Base) {σ : P.Aut} {C : P.Component}

/-- **The return map is based.** The return map of a component under an automorphism permuting the
simple roots of `b` permutes the simple roots of the base of the component. -/
theorem indexEquiv_componentReturn_mem_support
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support) {i : C.supp}
    (hi : i ∈ (b.componentBase C).support) :
    (σ.componentReturn C).indexEquiv i ∈ (b.componentBase C).support := by
  rw [mem_support_componentBase] at hi ⊢
  rw [Equiv.coe_componentReturn_indexEquiv_apply]
  exact (P.mem_support_iff_of_mem_orbitIndices hσ
    (mem_orbitIndices_iff_exists_pow.mpr ⟨_, rfl⟩)).mpr hi

end Base

end RootPairing
