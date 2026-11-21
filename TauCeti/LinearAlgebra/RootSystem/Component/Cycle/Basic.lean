/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.FixedSubmodule
public import TauCeti.LinearAlgebra.RootSystem.Component.Aut
public import TauCeti.LinearAlgebra.RootSystem.Component.InvariantForm
public import TauCeti.LinearAlgebra.RootSystem.OrbitSum.Basic
import TauCeti.GroupTheory.Perm.Basic
import TauCeti.GroupTheory.Perm.Cycle.Enumeration
import TauCeti.LinearAlgebra.RootSystem.HomInvariance
import TauCeti.LinearAlgebra.RootSystem.InvariantForm.Hom

/-!
# Component cycles, return automorphisms, and diagonal orbit-sum transport

For an automorphism `σ` of a root pairing `P` and an irreducible component `C` of cycle length
`c = Function.minimalPeriod σ.componentEquiv C`, `σ ^ c` restricts over a field to the **return
automorphism** `P.componentReturnAut σ C` on `P.componentPairing C`. Summing `σ`-iterates gives the
linear isomorphism `P.componentCycleDiag σ C` onto `P.componentCycleFixedSubmodule σ C`,
transporting orbit sums (`coe_componentCycleDiag_orbitSum`, `componentCycleFoldedIndicesEquiv`),
direct-sum/product decompositions (`isInternal_componentCycleFixedSubmodule`,
`componentCycleFixedPiEquiv`), and `σ`-invariant bilinear forms scaled by `c`
(`rootForm_componentCycleDiag`, `InvariantForm.form_componentCycleDiag`,
`rootForm_eq_sum_componentCycleFixedProj`).

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

private theorem pow_componentEquiv_ne_of_ne_lt {r s : ℕ}
    (hr : r < minimalPeriod σ.componentEquiv C) (hs : s < minimalPeriod σ.componentEquiv C)
    (hrs : r ≠ s) : (σ.componentEquiv ^ r) C ≠ (σ.componentEquiv ^ s) C := fun hEq ↦ hrs <| by
  rw [Perm.coe_pow, Perm.coe_pow] at hEq
  exact (iterate_eq_iterate_iff_of_lt_minimalPeriod hr hs).mp hEq

/-- The submodule of `σ`-fixed weights lying in the component-cycle space of `C`. -/
def componentCycleFixedSubmodule : Submodule R (LinearMap.fixedSubmodule σ.weightMap) :=
  (P.componentCycleSpace σ C).comap (LinearMap.fixedSubmodule σ.weightMap).subtype

section ImplicitCycle

variable {P σ C}

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
theorem componentProj_eq_zero_of_not_sameCycle {x : M} (hx : x ∈ P.componentCycleSpace σ C)
    (hD : ¬SameCycle σ.componentEquiv C D) : P.componentProj D x = 0 :=
  LinearMap.mem_ker.mp ((iSup₂_le fun _ hCE _ hy ↦ LinearMap.mem_ker.mpr
    (P.componentProj_apply_of_ne (fun (hED : _ = D) ↦ hD (hED ▸ hCE)) hy) :
      P.componentCycleSpace σ C ≤ LinearMap.ker (P.componentProj D)) hx)

/-- **The component-cycle spaces of distinct cycles are independent.** -/
theorem iSupIndep_componentCycleSpace :
    iSupIndep fun O : Quotient (SameCycle.setoid σ.componentEquiv) ↦
      P.componentCycleSpace σ O.out :=
  iSupIndep_def.mpr fun O ↦ by
    have hL : P.componentCycleSpace σ O.out =
        ⨆ D ∈ {D : P.Component | (⟦D⟧ : Quotient _) = O}, P.componentSpace D := by
      simp only [componentCycleSpace, Set.mem_ofPred_eq, Perm.sameCycle_out_iff σ.componentEquiv]
    have hR : (⨆ O' ≠ O, P.componentCycleSpace σ O'.out) ≤
        ⨆ D ∈ {D : P.Component | (⟦D⟧ : Quotient _) ≠ O}, P.componentSpace D :=
      iSup₂_le fun _ hO' ↦ iSup₂_le fun D hD ↦ le_iSup₂_of_le D
        (by rwa [Set.mem_ofPred_eq, (Perm.sameCycle_out_iff σ.componentEquiv).mp hD]) le_rfl
    rw [hL]
    exact Disjoint.mono_right hR (P.iSupIndep_componentSpace.disjoint_biSup_biSup
      (Set.disjoint_left.mpr fun _ h1 h2 ↦ h2 h1))

@[simp] theorem iSup_componentCycleSpace :
    (⨆ O : Quotient (SameCycle.setoid σ.componentEquiv), P.componentCycleSpace σ O.out) = ⊤ :=
  eq_top_iff.mpr ((P.iSup_componentSpace.trans IsRootSystem.span_root_eq_top).symm.trans_le
    (iSup_le fun C ↦ le_iSup_of_le ⟦C⟧ (P.componentSpace_le_componentCycleSpace
      ((Perm.sameCycle_out_iff σ.componentEquiv).mpr rfl))))

/-- **The weight space is the internal direct sum of its component-cycle spaces.** -/
theorem isInternal_componentCycleSpace
    [DecidableEq (Quotient (SameCycle.setoid σ.componentEquiv))] :
    DirectSum.IsInternal fun O : Quotient (SameCycle.setoid σ.componentEquiv) ↦
      P.componentCycleSpace σ O.out :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (P.iSupIndep_componentCycleSpace σ) (P.iSup_componentCycleSpace σ)

theorem iSupIndep_componentCycleFixedSubmodule :
    iSupIndep fun O : Quotient (SameCycle.setoid σ.componentEquiv) ↦
      P.componentCycleFixedSubmodule σ O.out :=
  iSupIndep_def.mpr fun O ↦ Submodule.disjoint_def.mpr fun y hy₁ hy₂ ↦ by
    have hmap : (⨆ O' ≠ O, P.componentCycleFixedSubmodule σ O'.out).map
        (LinearMap.fixedSubmodule σ.weightMap).subtype ≤
          ⨆ O' ≠ O, P.componentCycleSpace σ O'.out := by
      simp only [Submodule.map_iSup]
      exact iSup₂_le fun O' hO' ↦ le_iSup₂_of_le O' hO' (Submodule.map_comap_le _ _)
    exact Subtype.ext ((Submodule.disjoint_def.mp
      (iSupIndep_def.mp (P.iSupIndep_componentCycleSpace σ) O)) (y : M) hy₁
        (hmap (Submodule.mem_map_of_mem hy₂)))

/-- **The fixed space `LinearMap.fixedSubmodule σ.weightMap` is the internal direct sum of the
cycle-fixed submodules.** -/
theorem isInternal_componentCycleFixedSubmodule
    [DecidableEq (Quotient (SameCycle.setoid σ.componentEquiv))] :
    DirectSum.IsInternal fun O : Quotient (SameCycle.setoid σ.componentEquiv) ↦
      P.componentCycleFixedSubmodule σ O.out := by
  refine DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (P.iSupIndep_componentCycleFixedSubmodule σ) (eq_top_iff.mpr fun y _ ↦ ?_)
  classical
  have his := P.isInternal_componentCycleSpace σ
  obtain ⟨f, hf⟩ := his.2 (y : M)
  have hf_sum : ∑ O ∈ f.support, (f O : M) = (y : M) := by
    rw [← hf, DirectSum.coeAddMonoidHom_eq_dfinsuppSum, DFinsupp.sum]
  let g : ⨁ O : Quotient (SameCycle.setoid σ.componentEquiv), P.componentCycleSpace σ O.out :=
    ∑ O ∈ f.support, DirectSum.of (fun O ↦ ↥(P.componentCycleSpace σ O.out)) O
      ⟨σ.weightMap (f O), P.weightMap_mem_componentCycleSpace (f O).property⟩
  have hfg : g = f := his.1 <| by
    simp only [g, map_sum, DirectSum.coeAddMonoidHom_of]
    rw [← map_sum, hf_sum, LinearMap.mem_fixedSubmodule_iff.mp y.property, ← hf]
  have hfixed O (hO : O ∈ f.support) : (f O : M) ∈ LinearMap.fixedSubmodule σ.weightMap := by
    rw [LinearMap.mem_fixedSubmodule_iff]
    have hgO : (g O : M) = σ.weightMap (f O) := by
      rw [DirectSum.sum_apply, Submodule.coe_sum, Finset.sum_eq_single O
        (fun O' _ hO' ↦ by rw [DirectSum.of_eq_of_ne _ _ _ hO'.symm, Submodule.coe_zero])
        (fun h ↦ absurd hO h), DirectSum.of_eq_same]
    exact hgO.symm.trans (congrArg Subtype.val (by rw [hfg]))
  have hsum : y = ∑ O ∈ f.support.attach,
      (⟨(f O.val : M), hfixed O.val O.property⟩ : LinearMap.fixedSubmodule σ.weightMap) :=
    Subtype.ext (by rw [Submodule.coe_sum, Finset.sum_attach f.support fun O ↦ (f O : M), hf_sum])
  exact hsum ▸ Submodule.sum_mem _ fun O _ ↦ Submodule.mem_iSup_of_mem O.val (f O.val).property

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
  set c := minimalPeriod σ.componentEquiv (P.componentOf i)
  have hsemi : Semiconj P.componentOf σ.indexEquiv σ.componentEquiv :=
    fun j ↦ (σ.componentEquiv_componentOf j).symm
  have hcdvd : c ∣ minimalPeriod σ.indexEquiv i :=
    ((isPeriodicPt_minimalPeriod σ.indexEquiv i).map hsemi).minimalPeriod_dvd
  rcases eq_or_ne c 0 with hc | hc
  · rw [hc, zero_mul]; exact zero_dvd_iff.mp (hc ▸ hcdvd)
  · rw [Perm.coe_pow, minimalPeriod_iterate_eq_div_gcd hc, Nat.gcd_eq_right hcdvd,
      Nat.mul_div_cancel' hcdvd]

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

/-! #### Empty root systems -/

section Empty

variable [IsEmpty ι]

theorem subsingleton_fixedSubmodule_of_isEmpty [P.IsRootSystem] :
    Subsingleton (LinearMap.fixedSubmodule σ.weightMap) := by
  have : Subsingleton M := subsingleton_iff_forall_eq 0 |>.mpr fun x ↦
    (Submodule.mem_bot R).mp <| by
      have hx : x ∈ (⊤ : Submodule R M) := Submodule.mem_top
      rwa [← IsRootSystem.span_root_eq_top (P := P), Set.range_eq_empty, Submodule.span_empty] at hx
  infer_instance

end Empty

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

theorem coe_componentReturnAut_weightEquiv (u : P.componentSpace C) :
    ((P.componentReturnAut σ C).weightEquiv u : M) =
      (σ.weightMap ^ minimalPeriod σ.componentEquiv C) u := by simp [componentReturnAut]

@[simp] theorem coe_componentReturnAut_coweightMap (v : P.corootComponentSpace C) :
    ((P.componentReturnAut σ C).coweightMap v : N) =
      (σ ^ minimalPeriod σ.componentEquiv C).coweightMap v := by simp [componentReturnAut]

@[simp] theorem coe_componentReturnAut_indexEquiv (i : C.supp) :
    ((P.componentReturnAut σ C).indexEquiv i : ι) =
      (σ.indexEquiv ^ minimalPeriod σ.componentEquiv C) i := by simp [componentReturnAut]

@[simp] theorem coe_componentReturnAut_indexEquiv_pow (k : ℕ) (i : C.supp) :
    (((P.componentReturnAut σ C).indexEquiv ^ k) i : ι) =
      ((σ.indexEquiv ^ minimalPeriod σ.componentEquiv C) ^ k) i := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', pow_succ', Perm.mul_apply, Perm.mul_apply, coe_componentReturnAut_indexEquiv, ih]

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
      LinearMap.fixedSubmodule σ.weightMap := by
  rw [LinearMap.mem_fixedSubmodule_iff, map_sum]
  set c := minimalPeriod σ.componentEquiv C
  have hret : (σ.weightMap ^ c) (u : M) = (u : M) :=
    (P.coe_componentReturnAut_weightMap σ C u.val).symm.trans
      (congrArg Subtype.val (LinearMap.mem_fixedSubmodule_iff.mp u.property))
  simp_rw [← LinearMap.comp_apply (f := σ.weightMap), ← Module.End.mul_eq_comp, ← pow_succ']
  refine add_right_cancel (b := (u : M)) ?_
  simpa only [pow_zero, Module.End.one_eq_id, LinearMap.id_apply, hret] using
    (Finset.sum_range_succ' (fun r ↦ (σ.weightMap ^ r) (u : M)) c).symm.trans
      (Finset.sum_range_succ (fun r ↦ (σ.weightMap ^ r) (u : M)) c)

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
  minimalPeriod_eq_minimalPeriod_iff.mpr fun n ↦ by
    simp only [IsPeriodicPt, IsFixedPt, ← Perm.coe_pow, Subtype.ext_iff,
      P.coe_componentReturnAut_indexEquiv_pow]

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

private theorem mem_fixedSubmodule_of_mem_componentFoldedIndices {v : P.componentSpace C}
    (hv : v ∈ (P.componentPairing C).foldedIndices (P.componentReturnAut σ C)) :
    v ∈ LinearMap.fixedSubmodule (P.componentReturnAut σ C).weightMap :=
  let ⟨i, hi⟩ := (P.componentPairing C).mem_foldedIndices.mp hv
  hi ▸ (P.componentPairing C).orbitSum_mem_fixedSubmodule _ i

/-- **Bijection of distinct folded root vectors on a component cycle.** -/
noncomputable def componentCycleFoldedIndicesEquiv :
    (P.componentPairing C).foldedIndices (P.componentReturnAut σ C) ≃
      P.componentCycleFoldedIndices σ C where
  toFun v := ⟨((P.componentCycleDiag σ C
      ⟨v.val, P.mem_fixedSubmodule_of_mem_componentFoldedIndices σ C v.property⟩ :
        LinearMap.fixedSubmodule σ.weightMap) : M), by
    obtain ⟨i, hi⟩ := (P.componentPairing C).mem_foldedIndices.mp v.property
    have hEq : (⟨v.val, P.mem_fixedSubmodule_of_mem_componentFoldedIndices σ C v.property⟩ :
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
      ∑ r ∈ range (minimalPeriod σ.componentEquiv C), (σ.weightMap ^ r) (v.val : M) := (rfl)

@[simp] theorem coe_componentCycleFoldedIndicesEquiv_symm_apply
    (w : P.componentCycleFoldedIndices σ C) :
    ((P.componentCycleFoldedIndicesEquiv σ C).symm w : P.componentSpace C) =
      P.componentProj C w.val := (rfl)

/-! ### Scaling of invariant bilinear forms under `componentCycleDiag` -/

private theorem bilinear_componentCycleDiag (B : M →ₗ[K] M →ₗ[K] K)
    (hB : ∀ x y, B (σ.weightMap x) (σ.weightMap y) = B x y)
    (horth : ∀ {D E : P.Component}, D ≠ E → ∀ {x y : M},
      x ∈ P.componentSpace D → y ∈ P.componentSpace E → B x y = 0)
    (u v : LinearMap.fixedSubmodule (P.componentReturnAut σ C).weightMap) :
    B ((P.componentCycleDiag σ C u : LinearMap.fixedSubmodule σ.weightMap) : M)
        ((P.componentCycleDiag σ C v : LinearMap.fixedSubmodule σ.weightMap) : M) =
      (minimalPeriod σ.componentEquiv C : K) * B (u : M) (v : M) := by
  have hpow (r : ℕ) (x y : M) : B ((σ.weightMap ^ r) x) ((σ.weightMap ^ r) y) = B x y := by
    induction r with
    | zero => rfl
    | succ r ih =>
      rw [pow_succ', Module.End.mul_eq_comp, LinearMap.comp_apply, LinearMap.comp_apply, hB, ih]
  rw [P.coe_componentCycleDiag_apply, P.coe_componentCycleDiag_apply]
  simp only [map_sum, LinearMap.sum_apply]
  rw [Finset.sum_congr rfl fun s hs ↦ by
    rw [Finset.sum_eq_single s (fun r hr hrs ↦ horth (P.pow_componentEquiv_ne_of_ne_lt σ C
      (Finset.mem_range.mp hr) (Finset.mem_range.mp hs) hrs)
      (P.pow_weightMap_mem_componentSpace u.val.property r)
      (P.pow_weightMap_mem_componentSpace v.val.property s))
      (fun h ↦ absurd hs h), hpow s],
    Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **Scaling of a `σ`-invariant `B : P.InvariantForm` along `componentCycleDiag`** (`2 ≠ 0`). -/
theorem InvariantForm.form_componentCycleDiag [NeZero (2 : K)] (B : P.InvariantForm) {σ : P.Aut}
    (hB : ∀ x y, B.form (σ.weightMap x) (σ.weightMap y) = B.form x y) (C : P.Component)
    (u v : LinearMap.fixedSubmodule (P.componentReturnAut σ C).weightMap) :
    B.form ((P.componentCycleDiag σ C u : LinearMap.fixedSubmodule σ.weightMap) : M)
        ((P.componentCycleDiag σ C v : LinearMap.fixedSubmodule σ.weightMap) : M) =
      (minimalPeriod σ.componentEquiv C : K) * (B.restrictComponent C).form u.val v.val := by
  rw [B.restrictComponent_form_apply]; exact P.bilinear_componentCycleDiag σ C B.form hB
    (fun h _ _ hx hy ↦ B.apply_eq_zero_of_mem_componentSpace h hx hy) u v

/-- **Cartan ratios for a `σ`-invariant `B : P.InvariantForm` are preserved** when the cycle length
is nonzero in `K`. -/
theorem InvariantForm.cartanRatio_componentCycleDiag [NeZero (2 : K)] (B : P.InvariantForm)
    {σ : P.Aut} (hB : ∀ x y, B.form (σ.weightMap x) (σ.weightMap y) = B.form x y)
    (C : P.Component) (hc : (minimalPeriod σ.componentEquiv C : K) ≠ 0)
    (u v : LinearMap.fixedSubmodule (P.componentReturnAut σ C).weightMap) :
    2 * B.form ((P.componentCycleDiag σ C u : LinearMap.fixedSubmodule σ.weightMap) : M)
          ((P.componentCycleDiag σ C v : LinearMap.fixedSubmodule σ.weightMap) : M) /
        B.form ((P.componentCycleDiag σ C v : LinearMap.fixedSubmodule σ.weightMap) : M)
          ((P.componentCycleDiag σ C v : LinearMap.fixedSubmodule σ.weightMap) : M) =
      2 * (B.restrictComponent C).form u.val v.val / (B.restrictComponent C).form v.val v.val := by
  rw [B.form_componentCycleDiag P hB C, B.form_componentCycleDiag P hB C, mul_left_comm (2 : K),
    mul_div_mul_left _ _ hc]

/-! ### Independence of the starting component and product assembly across cycles -/

/-- **Changing the starting component conjugates the return automorphism.** -/
theorem autCongr_componentReturnAut_pow (k : ℕ) :
    ((σ ^ k).restrictComponent C).autCongr (P.componentReturnAut σ C) =
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
  (((σ ^ k).restrictComponent C).weightEquiv).fixedSubmoduleCongr <| by
    ext u
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      Equiv.coe_restrictComponent_weightEquiv, coe_componentReturnAut_weightMap,
      minimalPeriod_componentEquiv_pow_apply, σ.weightMap_pow]
    rw [← LinearMap.comp_apply, ← Module.End.mul_eq_comp, (Commute.pow_pow_self σ.weightMap k _).eq,
      Module.End.mul_eq_comp, LinearMap.comp_apply]

@[simp] theorem coe_componentReturnFixedShift_apply (k : ℕ)
    (u : LinearMap.fixedSubmodule (P.componentReturnAut σ C).weightMap) :
    ((P.componentReturnFixedShift σ C k u : P.componentSpace ((σ ^ k).componentEquiv C)) : M) =
      (σ.weightMap ^ k) (u : M) := by simp [componentReturnFixedShift]

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

/-! ### Scaling and orthogonal decomposition of the canonical `RootForm` -/

section RootForm

variable (P : RootPairing ι K M N) [Fintype ι] [P.IsRootSystem] (σ : P.Aut) (C : P.Component)

/-- **Scaling of `P.RootForm` along `componentCycleDiag`** (without needing `2 ≠ 0`). -/
theorem rootForm_componentCycleDiag [Fintype C.supp]
    (u v : LinearMap.fixedSubmodule (P.componentReturnAut σ C).weightMap) :
    P.RootForm ((P.componentCycleDiag σ C u : LinearMap.fixedSubmodule σ.weightMap) : M)
        ((P.componentCycleDiag σ C v : LinearMap.fixedSubmodule σ.weightMap) : M) =
      (minimalPeriod σ.componentEquiv C : K) * (P.componentPairing C).RootForm u.val v.val := by
  rw [P.bilinear_componentCycleDiag σ C P.RootForm (fun x y ↦ σ.toHom.rootForm_weightMap x y)
    (fun h _ _ hx hy ↦ P.rootForm_apply_eq_zero_of_mem_componentSpace h hx hy) u v,
    P.rootForm_componentPairing C]; rfl

/-- **Cartan ratios for `P.RootForm` are preserved by `componentCycleDiag`** when the cycle
length is nonzero in `K`. -/
theorem rootForm_cartanRatio_componentCycleDiag [Fintype C.supp]
    (hc : (minimalPeriod σ.componentEquiv C : K) ≠ 0)
    (u v : LinearMap.fixedSubmodule (P.componentReturnAut σ C).weightMap) :
    2 * P.RootForm ((P.componentCycleDiag σ C u : LinearMap.fixedSubmodule σ.weightMap) : M)
          ((P.componentCycleDiag σ C v : LinearMap.fixedSubmodule σ.weightMap) : M) /
        P.RootForm ((P.componentCycleDiag σ C v : LinearMap.fixedSubmodule σ.weightMap) : M)
          ((P.componentCycleDiag σ C v : LinearMap.fixedSubmodule σ.weightMap) : M) =
      2 * (P.componentPairing C).RootForm u.val v.val /
        (P.componentPairing C).RootForm v.val v.val := by
  rw [P.rootForm_componentCycleDiag σ C, P.rootForm_componentCycleDiag σ C, mul_left_comm (2 : K),
    mul_div_mul_left _ _ hc]

/-- **Orthogonal decomposition of `P.RootForm` on `σ`-fixed weights across component cycles.** -/
theorem rootForm_eq_sum_componentCycleFixedProj
    [Fintype (Quotient (SameCycle.setoid σ.componentEquiv))]
    [∀ O : Quotient (SameCycle.setoid σ.componentEquiv), Fintype O.out.supp]
    (x y : LinearMap.fixedSubmodule σ.weightMap) :
    P.RootForm (x : M) (y : M) =
      ∑ O : Quotient (SameCycle.setoid σ.componentEquiv),
        (minimalPeriod σ.componentEquiv O.out : K) *
          (P.componentPairing O.out).RootForm
            (P.componentCycleFixedProj σ O.out x).val
            (P.componentCycleFixedProj σ O.out y).val := by
  conv_lhs =>
    rw [← (P.componentCycleFixedPiEquiv σ).symm_apply_apply x,
      ← (P.componentCycleFixedPiEquiv σ).symm_apply_apply y]
  rw [P.coe_componentCycleFixedPiEquiv_symm_apply, P.coe_componentCycleFixedPiEquiv_symm_apply]
  simp only [map_sum, LinearMap.sum_apply, componentCycleFixedPiEquiv_apply]
  refine Finset.sum_congr rfl fun O _ ↦ ?_
  rw [Finset.sum_eq_single O (fun O' _ hO' ↦ by
    rw [P.coe_componentCycleDiag_apply, P.coe_componentCycleDiag_apply]
    simp only [map_sum, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun s _ ↦ Finset.sum_eq_zero fun r _ ↦ ?_
    have hne : (σ.componentEquiv ^ r) O'.out ≠ (σ.componentEquiv ^ s) O.out := fun hEq ↦ hO' <| by
      have hsc : SameCycle σ.componentEquiv O'.out O.out :=
        SameCycle.trans (y := (σ.componentEquiv ^ r) O'.out) ⟨(r : ℤ), by simp⟩
          (SameCycle.symm ⟨(s : ℤ), by simp [hEq]⟩)
      rw [← (Perm.sameCycle_out_iff σ.componentEquiv).mp hsc, Quotient.out_eq]
    exact P.rootForm_apply_eq_zero_of_mem_componentSpace hne
      (P.pow_weightMap_mem_componentSpace (P.componentCycleFixedProj σ O'.out x).val.property r)
      (P.pow_weightMap_mem_componentSpace (P.componentCycleFixedProj σ O.out y).val.property s))
    (by simp)]
  exact P.rootForm_componentCycleDiag σ O.out _ _

end RootForm

end Field

end RootPairing
