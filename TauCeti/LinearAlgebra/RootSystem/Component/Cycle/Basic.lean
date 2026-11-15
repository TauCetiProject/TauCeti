/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.FixedSubmodule
public import TauCeti.LinearAlgebra.RootSystem.Component.Aut
public import TauCeti.LinearAlgebra.RootSystem.Component.InvariantForm
public import TauCeti.LinearAlgebra.RootSystem.OrbitSum
import TauCeti.GroupTheory.Perm.Basic
import TauCeti.GroupTheory.Perm.Cycle.Enumeration
import TauCeti.LinearAlgebra.RootSystem.HomInvariance
import TauCeti.LinearAlgebra.RootSystem.InvariantForm.Hom

/-!
# Component cycles, return automorphisms, and diagonal orbit-sum transport

An automorphism `σ` of a root pairing `P` permutes the irreducible components via
`σ.componentEquiv` (`TauCeti.LinearAlgebra.RootSystem.Component.Aut`). For a component `C` whose
`σ`-cycle has length `c = Function.minimalPeriod σ.componentEquiv C`, the iterate `σ ^ c` fixes `C`
and restricts over a field to the **return automorphism**
`RootPairing.componentReturnAut P σ C : (P.componentPairing C).Aut` on the irreducible component
pairing `P.componentPairing C`.

On a root system, the weight space decomposes into the `σ`-stable **component-cycle spaces**
`P.componentCycleSpace σ O.out` indexed by the component cycles
`O : Quotient (Equiv.Perm.SameCycle.setoid σ.componentEquiv)`, and likewise the fixed space
`LinearMap.fixedSubmodule σ.weightMap` is the internal direct sum of the cycle-fixed submodules
`P.componentCycleFixedSubmodule σ O.out`. On a single component cycle of length `c`, summing
the iterates `u, σ u, …, σ ^ (c - 1) u` gives a linear isomorphism
`RootPairing.componentCycleDiag P σ C` from the return fixed space
`LinearMap.fixedSubmodule (P.componentReturnAut σ C).weightMap` onto
`P.componentCycleFixedSubmodule σ C`, whose inverse is the ambient component projection
`RootPairing.componentCycleFixedProj P σ C`.

Under `componentCycleDiag`, folding a component cycle of length `c` under `σ` reduces to folding the
single irreducible component `C` under its return automorphism `τ = σ ^ c`:
* Each `σ`-orbit of root indices meeting `C` has cardinality `c` times the cardinality of its
  `τ`-orbit in `C.supp` (`RootPairing.card_orbitIndices_eq_mul_componentReturnAut`), and
  `componentCycleDiag` carries each `τ`-orbit sum in `P.componentPairing C` to the ambient `σ`-orbit
  sum in `P` (`RootPairing.coe_componentCycleDiag_orbitSum`), inducing a bijection between the
  distinct folded root vectors (`RootPairing.componentCycleFoldedIndicesEquiv`).
* Both the canonical root form `P.RootForm` and every `σ`-invariant `B : P.InvariantForm` (for
  `2 ≠ 0`) scale uniformly by `c` along `componentCycleDiag`
  (`RootPairing.rootForm_componentCycleDiag`,
  `RootPairing.InvariantForm.form_componentCycleDiag`), so in characteristic zero all Cartan ratios
  `2 B(u, v) / B(v, v)` are preserved unchanged.
* Replacing `C` by another component `(σ ^ k).componentEquiv C` on the same cycle conjugates the
  return automorphism along `(σ ^ k).restrictComponent C` and leaves `componentCycleDiag` unchanged
  on ambient vectors (`RootPairing.coe_componentCycleDiag_componentReturnFixedShift`). Assembling
  all cycles yields the product decomposition `RootPairing.componentCycleFixedPiEquiv` of the full
  fixed space and the partition of `P.foldedIndices σ`.

Interaction with bases, simple-orbit coordinates, the positive root cone, and the root lattice is
developed in `TauCeti.LinearAlgebra.RootSystem.Component.Cycle.Base`.

## Main definitions

* `RootPairing.componentCycle`: the finset of irreducible components in the `σ`-cycle of `C`.
* `RootPairing.componentCycleSpace`: the `σ`-stable submodule spanned by the component spaces on the
  `σ`-cycle of `C`.
* `RootPairing.componentCycleFixedSubmodule`: the submodule of
  `LinearMap.fixedSubmodule σ.weightMap` consisting of fixed vectors lying in
  `P.componentCycleSpace σ C`.
* `RootPairing.componentReturnAut`: the return automorphism `(σ ^ c).restrictComponentAut C _` of
  `P.componentPairing C`, where `c = Function.minimalPeriod σ.componentEquiv C`.
* `RootPairing.componentCycleFixedProj`, `RootPairing.componentCycleDiag`: projection onto `C` and
  diagonal sum `u ↦ ∑ r ∈ range c, (σ.weightMap ^ r) u` as inverse maps between the return fixed
  space and the cycle fixed space.
* `RootPairing.componentCycleFoldedIndices`, `RootPairing.componentCycleFoldedIndicesEquiv`: the
  orbit sums of roots in the `σ`-cycle of `C`, and their bijection with the folded indices of
  `P.componentReturnAut σ C` via `componentCycleDiag`.
* `RootPairing.componentReturnFixedShift`: transport of return fixed vectors along `σ ^ k` to
  another component in the same cycle.
* `RootPairing.componentCycleFixedPiEquiv`: decomposition of `LinearMap.fixedSubmodule σ.weightMap`
  into the product of the return fixed spaces over all component cycles.

## Main results

* `RootPairing.isInternal_componentCycleSpace`,
  `RootPairing.isInternal_componentCycleFixedSubmodule`: internal direct-sum decompositions of `M`
  and `LinearMap.fixedSubmodule σ.weightMap` over component cycles.
* `RootPairing.card_orbitIndices_eq_mul_componentReturnAut`,
  `RootPairing.coe_componentCycleDiag_orbitSum`: orbit-size factorization and orbit-sum transport
  along `componentCycleDiag`.
* `RootPairing.rootForm_componentCycleDiag`, `RootPairing.InvariantForm.form_componentCycleDiag`,
  `RootPairing.rootForm_cartanRatio_componentCycleDiag`,
  `RootPairing.InvariantForm.cartanRatio_componentCycleDiag`: scaling by `c` of invariant bilinear
  forms and invariance of Cartan ratios.
* `RootPairing.autCongr_componentReturnAut_pow`,
  `RootPairing.coe_componentCycleDiag_componentReturnFixedShift`: independence of the starting
  component in the cycle.
* `RootPairing.iUnion_componentCycleFoldedIndices`,
  `RootPairing.pairwise_disjoint_componentCycleFoldedIndices`: partition of `P.foldedIndices σ`
  across component cycles.

## References

* J. R. Stembridge, *Folding by automorphisms*, note of 20 August 2008.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4-6*, Ch. VI §1, no. 2.
* G. Lusztig, *Introduction to Quantum Groups*, Birkhäuser (1993), §14.1.
-/

public section

open Finset Function TauCeti
open scoped DirectSum

namespace RootPairing

/-! ### Component cycles and cycle spaces over a commutative ring -/

section CommRing

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) (σ : P.Aut) (C : P.Component) {D : P.Component}

/-- The **component cycle** of an irreducible component `C` under an automorphism `σ`: the finite
set of irreducible components on the same cycle of `σ.componentEquiv` as `C`. -/
noncomputable def componentCycle [Finite P.Component] : Finset P.Component :=
  (Set.toFinite {D | _root_.Equiv.Perm.SameCycle σ.componentEquiv C D}).toFinset

variable {P σ C}

@[simp]
theorem mem_componentCycle [Finite P.Component] :
    D ∈ P.componentCycle σ C ↔ _root_.Equiv.Perm.SameCycle σ.componentEquiv C D := by
  simp [componentCycle]

variable (P σ C) in
theorem self_mem_componentCycle [Finite P.Component] : C ∈ P.componentCycle σ C :=
  mem_componentCycle.mpr (_root_.Equiv.Perm.SameCycle.refl _ _)

variable (P σ C) in
theorem card_componentCycle [Finite P.Component] :
    #(P.componentCycle σ C) = minimalPeriod σ.componentEquiv C := by
  rw [componentCycle, ← Set.ncard_eq_toFinset_card, _root_.Equiv.Perm.ncard_setOf_sameCycle]

variable (P σ C) in
theorem card_componentCycle_pos [Finite P.Component] : 0 < #(P.componentCycle σ C) :=
  Finset.card_pos.mpr ⟨C, P.self_mem_componentCycle σ C⟩

variable (P σ C) in
theorem minimalPeriod_componentEquiv_pos [Finite P.Component] :
    0 < minimalPeriod σ.componentEquiv C := by
  rw [← P.card_componentCycle σ C]
  exact P.card_componentCycle_pos σ C

theorem componentCycle_eq_of_mem [Finite P.Component] (h : D ∈ P.componentCycle σ C) :
    P.componentCycle σ D = P.componentCycle σ C := by
  ext E
  simp only [mem_componentCycle] at h ⊢
  exact ⟨h.trans, h.symm.trans⟩

variable (P σ C) in
@[simp]
theorem componentCycle_componentEquiv [Finite P.Component] :
    P.componentCycle σ (σ.componentEquiv C) = P.componentCycle σ C :=
  componentCycle_eq_of_mem (mem_componentCycle.mpr ⟨1, by simp⟩)

variable (P C) in
@[simp]
theorem componentCycle_one [Finite P.Component] : P.componentCycle 1 C = {C} := by
  ext D
  simp [eq_comm]

variable (P σ C) in
theorem componentEquiv_pow_minimalPeriod :
    (σ ^ minimalPeriod σ.componentEquiv C).componentEquiv C = C := by
  rw [σ.componentEquiv_pow, _root_.Equiv.Perm.coe_pow]
  exact isPeriodicPt_minimalPeriod σ.componentEquiv C

variable (P σ C) in
theorem minimalPeriod_componentEquiv_pow_apply (k : ℕ) :
    minimalPeriod σ.componentEquiv ((σ ^ k).componentEquiv C) =
      minimalPeriod σ.componentEquiv C :=
  (_root_.Equiv.Perm.SameCycle.minimalPeriod_eq ⟨(k : ℤ), by simp [σ.componentEquiv_pow]⟩).symm

variable (P σ C) in
/-- The **component-cycle space** of `C` under `σ`: the supremum of the component spaces
`P.componentSpace D` over all components `D` in the `σ`-cycle of `C`. -/
def componentCycleSpace : Submodule R M :=
  ⨆ D, ⨆ (_ : _root_.Equiv.Perm.SameCycle σ.componentEquiv C D), P.componentSpace D

theorem componentSpace_le_componentCycleSpace
    (h : _root_.Equiv.Perm.SameCycle σ.componentEquiv C D) :
    P.componentSpace D ≤ P.componentCycleSpace σ C :=
  le_iSup₂_of_le D h le_rfl

variable (P σ C) in
theorem self_componentSpace_le_componentCycleSpace :
    P.componentSpace C ≤ P.componentCycleSpace σ C :=
  P.componentSpace_le_componentCycleSpace (_root_.Equiv.Perm.SameCycle.refl _ _)

theorem componentCycleSpace_eq_of_sameCycle
    (h : _root_.Equiv.Perm.SameCycle σ.componentEquiv C D) :
    P.componentCycleSpace σ C = P.componentCycleSpace σ D :=
  le_antisymm
    (iSup₂_le fun _ hCE ↦ P.componentSpace_le_componentCycleSpace (h.symm.trans hCE))
    (iSup₂_le fun _ hDE ↦ P.componentSpace_le_componentCycleSpace (h.trans hDE))

variable (P σ C) in
@[simp]
theorem componentCycleSpace_componentEquiv :
    P.componentCycleSpace σ (σ.componentEquiv C) = P.componentCycleSpace σ C :=
  (P.componentCycleSpace_eq_of_sameCycle ⟨(1 : ℤ), by simp⟩).symm

variable (P C) in
@[simp]
theorem componentCycleSpace_one : P.componentCycleSpace 1 C = P.componentSpace C := by
  refine le_antisymm (iSup₂_le fun D hD ↦ ?_) (P.self_componentSpace_le_componentCycleSpace 1 C)
  obtain rfl : C = D := by simpa using hD
  exact le_rfl

variable (P σ C) in
theorem componentCycleSpace_eq_biSup_componentCycle [Finite P.Component] :
    P.componentCycleSpace σ C = ⨆ D ∈ P.componentCycle σ C, P.componentSpace D := by
  simp only [componentCycleSpace, mem_componentCycle]

variable (P σ C) in
/-- The component-cycle space is mapped onto itself by `σ.weightMap`. -/
@[simp]
theorem map_componentCycleSpace :
    (P.componentCycleSpace σ C).map σ.weightMap = P.componentCycleSpace σ C := by
  have hle (τ : P.Aut)
      (hτ : ∀ D, _root_.Equiv.Perm.SameCycle σ.componentEquiv C D →
        _root_.Equiv.Perm.SameCycle σ.componentEquiv C (τ.componentEquiv D)) :
      (P.componentCycleSpace σ C).map τ.weightMap ≤ P.componentCycleSpace σ C := by
    rw [componentCycleSpace, Submodule.map_iSup]
    refine iSup_le fun D ↦ ?_
    rw [Submodule.map_iSup]
    refine iSup_le fun hD ↦ Submodule.map_le_iff_le_comap.mpr fun x hx ↦ ?_
    exact P.componentSpace_le_componentCycleSpace (hτ D hD) (τ.weightMap_mem_componentSpace hx)
  refine le_antisymm (hle σ fun D hD ↦ _root_.Equiv.Perm.sameCycle_apply_right.mpr hD) ?_
  calc
    P.componentCycleSpace σ C =
        ((P.componentCycleSpace σ C).map (σ⁻¹).weightMap).map σ.weightMap := by
      rw [← Submodule.map_comp]
      have hcomp : σ.weightMap.comp (σ⁻¹).weightMap = LinearMap.id := by
        ext x
        simp [← Equiv.weightEquiv_apply, Equiv.weightEquiv_inv]
      simp [hcomp]
    _ ≤ (P.componentCycleSpace σ C).map σ.weightMap :=
      Submodule.map_mono (hle σ⁻¹ fun D hD ↦ by
        rw [σ.componentEquiv_inv, _root_.Equiv.Perm.inv_def]
        exact _root_.Equiv.Perm.sameCycle_symm_apply_right.mpr hD)

theorem weightMap_mem_componentCycleSpace {x : M} (hx : x ∈ P.componentCycleSpace σ C) :
    σ.weightMap x ∈ P.componentCycleSpace σ C := by
  rw [← P.map_componentCycleSpace σ C]
  exact Submodule.mem_map_of_mem hx

theorem pow_weightMap_mem_componentCycleSpace {x : M} (hx : x ∈ P.componentCycleSpace σ C)
    (n : ℕ) : (σ.weightMap ^ n) x ∈ P.componentCycleSpace σ C := by
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    rw [pow_succ', Module.End.mul_eq_comp, LinearMap.comp_apply]
    exact P.weightMap_mem_componentCycleSpace ih

private theorem pow_weightMap_mem_componentSpace {u : M} (hu : u ∈ P.componentSpace C) (r : ℕ) :
    (σ.weightMap ^ r) u ∈ P.componentSpace ((σ.componentEquiv ^ r) C) := by
  rw [← σ.weightMap_pow, ← σ.componentEquiv_pow]
  exact (σ ^ r).weightMap_mem_componentSpace hu

variable (P σ C) in
/-- The submodule of `σ`-fixed weights lying in the component-cycle space of `C`. -/
def componentCycleFixedSubmodule : Submodule R (LinearMap.fixedSubmodule σ.weightMap) :=
  (P.componentCycleSpace σ C).comap (LinearMap.fixedSubmodule σ.weightMap).subtype

@[simp]
theorem mem_componentCycleFixedSubmodule {y : LinearMap.fixedSubmodule σ.weightMap} :
    y ∈ P.componentCycleFixedSubmodule σ C ↔ (y : M) ∈ P.componentCycleSpace σ C :=
  Iff.rfl

/-! #### Cycle independence, projections, and direct-sum decomposition -/

section RootSystem

variable [P.IsRootSystem]

theorem componentProj_eq_zero_of_not_sameCycle {x : M}
    (hx : x ∈ P.componentCycleSpace σ C)
    (hD : ¬_root_.Equiv.Perm.SameCycle σ.componentEquiv C D) :
    P.componentProj D x = 0 := by
  have hle : P.componentCycleSpace σ C ≤ LinearMap.ker (P.componentProj D) :=
    iSup₂_le fun E hCE y hy ↦ LinearMap.mem_ker.mpr
      (P.componentProj_apply_of_ne (fun (hED : E = D) ↦ hD (hED ▸ hCE)) hy)
  exact LinearMap.mem_ker.mp (hle hx)

variable (P σ) in
/-- **The component-cycle spaces of distinct cycles are independent.** -/
theorem iSupIndep_componentCycleSpace :
    iSupIndep fun O : Quotient (_root_.Equiv.Perm.SameCycle.setoid σ.componentEquiv) ↦
      P.componentCycleSpace σ O.out := by
  rw [iSupIndep_def]
  intro O
  have hL : P.componentCycleSpace σ O.out =
      ⨆ D ∈ {D : P.Component | (⟦D⟧ : Quotient _) = O}, P.componentSpace D := by
    simp only [componentCycleSpace, Set.mem_ofPred_eq,
      _root_.Equiv.Perm.sameCycle_out_iff σ.componentEquiv]
  have hR : (⨆ O' ≠ O, P.componentCycleSpace σ O'.out) ≤
      ⨆ D ∈ {D : P.Component | (⟦D⟧ : Quotient _) ≠ O}, P.componentSpace D :=
    iSup₂_le fun O' hO' ↦ iSup₂_le fun D hD ↦ le_iSup₂_of_le D
      (by rwa [Set.mem_ofPred_eq,
        (_root_.Equiv.Perm.sameCycle_out_iff σ.componentEquiv).mp hD]) le_rfl
  rw [hL]
  exact Disjoint.mono_right hR (P.iSupIndep_componentSpace.disjoint_biSup_biSup
    (Set.disjoint_left.mpr fun _ h1 h2 ↦ h2 h1))

variable (P σ) in
@[simp]
theorem iSup_componentCycleSpace :
    (⨆ O : Quotient (_root_.Equiv.Perm.SameCycle.setoid σ.componentEquiv),
      P.componentCycleSpace σ O.out) = ⊤ :=
  eq_top_iff.mpr ((P.iSup_componentSpace.trans IsRootSystem.span_root_eq_top).symm.trans_le
    (iSup_le fun C ↦ le_iSup_of_le ⟦C⟧ (P.componentSpace_le_componentCycleSpace
      ((_root_.Equiv.Perm.sameCycle_out_iff σ.componentEquiv).mpr rfl))))

variable (P σ) in
/-- **The weight space of a root system is the internal direct sum of its component-cycle
spaces.** -/
theorem isInternal_componentCycleSpace
    [DecidableEq (Quotient (_root_.Equiv.Perm.SameCycle.setoid σ.componentEquiv))] :
    DirectSum.IsInternal fun O : Quotient (_root_.Equiv.Perm.SameCycle.setoid σ.componentEquiv) ↦
      P.componentCycleSpace σ O.out :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (P.iSupIndep_componentCycleSpace σ) (P.iSup_componentCycleSpace σ)

variable (P σ) in
theorem iSupIndep_componentCycleFixedSubmodule :
    iSupIndep fun O : Quotient (_root_.Equiv.Perm.SameCycle.setoid σ.componentEquiv) ↦
      P.componentCycleFixedSubmodule σ O.out := by
  rw [iSupIndep_def]
  intro O
  rw [Submodule.disjoint_def]
  intro y hy₁ hy₂
  have hmap : (⨆ O' ≠ O, P.componentCycleFixedSubmodule σ O'.out).map
      (LinearMap.fixedSubmodule σ.weightMap).subtype ≤
      ⨆ O' ≠ O, P.componentCycleSpace σ O'.out := by
    rw [Submodule.map_iSup]
    refine iSup_le fun O' ↦ ?_
    rw [Submodule.map_iSup]
    exact iSup_le fun hO' ↦ le_iSup₂_of_le O' hO' (Submodule.map_comap_le _ _)
  have hmem : (y : M) ∈ ⨆ O' ≠ O, P.componentCycleSpace σ O'.out :=
    hmap (Submodule.mem_map_of_mem hy₂)
  exact Subtype.ext ((Submodule.disjoint_def.mp
    (iSupIndep_def.mp (P.iSupIndep_componentCycleSpace σ) O)) (y : M) hy₁ hmem)

variable (P σ) in
/-- **The fixed space `LinearMap.fixedSubmodule σ.weightMap` is the internal direct sum of the
cycle-fixed submodules**, without any finiteness hypothesis on the root index type. -/
theorem isInternal_componentCycleFixedSubmodule
    [DecidableEq (Quotient (_root_.Equiv.Perm.SameCycle.setoid σ.componentEquiv))] :
    DirectSum.IsInternal fun O : Quotient (_root_.Equiv.Perm.SameCycle.setoid σ.componentEquiv) ↦
      P.componentCycleFixedSubmodule σ O.out := by
  refine DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (P.iSupIndep_componentCycleFixedSubmodule σ) (eq_top_iff.mpr fun y _ ↦ ?_)
  classical
  have his := P.isInternal_componentCycleSpace σ
  obtain ⟨f, hf⟩ := his.2 (y : M)
  have hf_sum : ∑ O ∈ f.support, (f O : M) = (y : M) := by
    rw [← hf, DirectSum.coeAddMonoidHom_eq_dfinsuppSum, DFinsupp.sum]
  let g : ⨁ O : Quotient (_root_.Equiv.Perm.SameCycle.setoid σ.componentEquiv),
      P.componentCycleSpace σ O.out :=
    ∑ O ∈ f.support, DirectSum.of (fun O ↦ ↥(P.componentCycleSpace σ O.out)) O
      ⟨σ.weightMap (f O), P.weightMap_mem_componentCycleSpace (f O).2⟩
  have hfg : g = f := his.1 (by
    dsimp only [g]
    rw [map_sum]
    simp only [DirectSum.coeAddMonoidHom_of]
    rw [← map_sum, hf_sum, LinearMap.mem_fixedSubmodule_iff.mp y.2, ← hf])
  have hfixed (O) (hO : O ∈ f.support) : (f O : M) ∈ LinearMap.fixedSubmodule σ.weightMap := by
    rw [LinearMap.mem_fixedSubmodule_iff]
    have happ : (g O : M) = (f O : M) := congrArg Subtype.val (by rw [hfg])
    have hgO : (g O : M) = σ.weightMap (f O) := by
      dsimp only [g]
      rw [DirectSum.sum_apply, Submodule.coe_sum, Finset.sum_eq_single O]
      · rw [DirectSum.of_eq_same]
      · intro O' _ hO'
        rw [DirectSum.of_eq_of_ne _ _ _ hO'.symm, Submodule.coe_zero]
      · exact fun h ↦ absurd hO h
    exact hgO.symm.trans happ
  have hsum : y = ∑ O ∈ f.support.attach,
      (⟨(f O.1 : M), hfixed O.1 O.2⟩ : LinearMap.fixedSubmodule σ.weightMap) :=
    Subtype.ext (by rw [Submodule.coe_sum, Finset.sum_attach f.support fun O ↦ (f O : M), hf_sum])
  rw [hsum]
  exact Submodule.sum_mem _ fun O _ ↦ Submodule.mem_iSup_of_mem O.1 (f O.1).2

theorem sum_componentCycle_componentProj_of_mem_componentCycleSpace [Finite P.Component] {x : M}
    (hx : x ∈ P.componentCycleSpace σ C) :
    ∑ D ∈ P.componentCycle σ C, (P.componentProj D x : M) = x := by
  cases nonempty_fintype P.Component
  conv_rhs => rw [← P.sum_componentProj x]
  refine Finset.sum_subset (Finset.subset_univ _) fun D _ hD ↦ ?_
  rw [P.componentProj_eq_zero_of_not_sameCycle hx (mt mem_componentCycle.mpr hD),
    Submodule.coe_zero]

theorem sum_range_componentProj_of_mem_componentCycleSpace [Finite P.Component] {x : M}
    (hx : x ∈ P.componentCycleSpace σ C) :
    ∑ r ∈ range (minimalPeriod σ.componentEquiv C),
        (P.componentProj ((σ.componentEquiv ^ r) C) x : M) = x := by
  classical
  cases nonempty_fintype P.Component
  rw [_root_.Equiv.Perm.sum_range_minimalPeriod σ.componentEquiv
    (fun D ↦ (P.componentProj D x : M)) C]
  conv_rhs => rw [← P.sum_componentCycle_componentProj_of_mem_componentCycleSpace hx]
  refine Finset.sum_congr ?_ fun _ _ ↦ rfl
  ext D
  simp [mem_componentCycle]

/-- **Left-inverse identity for the diagonal cycle sum.** For any `u` in `P.componentSpace C`,
summing `(σ.weightMap ^ r) u` over `r < minimalPeriod σ.componentEquiv C` and projecting back to `C`
recovers `u`. -/
theorem componentProj_sum_range_pow_weightMap [Finite P.Component] {u : M}
    (hu : u ∈ P.componentSpace C) :
    P.componentProj C (∑ r ∈ range (minimalPeriod σ.componentEquiv C), (σ.weightMap ^ r) u) =
      ⟨u, hu⟩ := by
  rw [map_sum, Finset.sum_eq_single 0]
  · simpa using P.componentProj_apply_of_mem hu
  · intro r hr hr0
    have hrlt : r < minimalPeriod σ.componentEquiv C := Finset.mem_range.mp hr
    have hne : (σ.componentEquiv ^ r) C ≠ C := fun hEq ↦ hr0 (by
      rw [_root_.Equiv.Perm.coe_pow] at hEq
      exact (iterate_eq_iterate_iff_of_lt_minimalPeriod hrlt
        (P.minimalPeriod_componentEquiv_pos σ C)).mp hEq)
    exact P.componentProj_apply_of_ne hne (P.pow_weightMap_mem_componentSpace hu r)
  · intro h0
    exact absurd (Finset.mem_range.mpr (P.minimalPeriod_componentEquiv_pos σ C)) h0

/-- **Right-inverse identity for the diagonal cycle sum.** Any `σ`-fixed vector `x` in the
component-cycle space of `C` is the sum of the `σ`-iterates of its `C`-projection. -/
theorem sum_range_pow_weightMap_componentProj [Finite P.Component] {x : M}
    (hx : x ∈ P.componentCycleSpace σ C) (hσx : σ.weightMap x = x) :
    ∑ r ∈ range (minimalPeriod σ.componentEquiv C), (σ.weightMap ^ r) (P.componentProj C x) =
      x := by
  have hfix : x ∈ LinearMap.fixedSubmodule σ.weightMap :=
    LinearMap.mem_fixedSubmodule_iff.mpr hσx
  calc
    ∑ r ∈ range (minimalPeriod σ.componentEquiv C), (σ.weightMap ^ r) (P.componentProj C x) =
        ∑ r ∈ range (minimalPeriod σ.componentEquiv C),
          (P.componentProj ((σ.componentEquiv ^ r) C) x : M) := by
      refine Finset.sum_congr rfl fun r _ ↦ ?_
      rw [← σ.coe_componentProj_pow_weightMap r C x,
        LinearMap.pow_apply_of_mem_fixedSubmodule σ.weightMap hfix r]
    _ = x := P.sum_range_componentProj_of_mem_componentCycleSpace hx

variable (P σ C) in
/-- The `C`-projection of any `σ`-fixed weight is fixed by the return iterate `σ ^ c`. -/
theorem pow_minimalPeriod_weightMap_componentProj {x : M} (hσx : σ.weightMap x = x) :
    (σ.weightMap ^ minimalPeriod σ.componentEquiv C) (P.componentProj C x) =
      P.componentProj C x := by
  have hfix : x ∈ LinearMap.fixedSubmodule σ.weightMap :=
    LinearMap.mem_fixedSubmodule_iff.mpr hσx
  rw [← σ.coe_componentProj_pow_weightMap _ C x,
    LinearMap.pow_apply_of_mem_fixedSubmodule σ.weightMap hfix,
    ← σ.componentEquiv_pow, P.componentEquiv_pow_minimalPeriod σ C]

end RootSystem

/-! #### Orbit-period factorization and folded indices on a component cycle -/

variable (P σ) in
/-- **Orbit-period factorization.** The minimal period of a root index `i` under `σ.indexEquiv` is
the length `c` of the `σ`-cycle of `P.componentOf i` times the minimal period of `i` under
`σ.indexEquiv ^ c`. -/
theorem minimalPeriod_indexEquiv_eq_mul (i : ι) :
    minimalPeriod σ.indexEquiv i =
      minimalPeriod σ.componentEquiv (P.componentOf i) *
        minimalPeriod (σ.indexEquiv ^ minimalPeriod σ.componentEquiv (P.componentOf i)) i := by
  set c := minimalPeriod σ.componentEquiv (P.componentOf i)
  set m := minimalPeriod σ.indexEquiv i
  set d := minimalPeriod (σ.indexEquiv ^ c) i
  have hm_fix : (σ.indexEquiv ^ m) i = i := by
    rw [_root_.Equiv.Perm.coe_pow]
    exact isPeriodicPt_minimalPeriod σ.indexEquiv i
  have hc_per : IsPeriodicPt σ.componentEquiv m (P.componentOf i) := by
    have h : (⇑σ.componentEquiv)^[m] (P.componentOf i) = P.componentOf i := by
      rw [← _root_.Equiv.Perm.coe_pow, ← σ.componentEquiv_pow,
        (σ ^ m).componentEquiv_componentOf, σ.indexEquiv_pow, hm_fix]
    exact h
  obtain ⟨q, hm⟩ := hc_per.minimalPeriod_dvd
  have hd_dvd_q : d ∣ q := by
    have h : (⇑(σ.indexEquiv ^ c))^[q] i = i := by
      rw [← _root_.Equiv.Perm.coe_pow, ← pow_mul, ← hm, hm_fix]
    exact IsPeriodicPt.minimalPeriod_dvd h
  have hm_dvd_cd : m ∣ c * d := by
    have h : (⇑σ.indexEquiv)^[c * d] i = i := by
      rw [← _root_.Equiv.Perm.coe_pow, pow_mul, _root_.Equiv.Perm.coe_pow]
      exact isPeriodicPt_minimalPeriod (σ.indexEquiv ^ c) i
    exact IsPeriodicPt.minimalPeriod_dvd h
  exact Nat.dvd_antisymm hm_dvd_cd (hm ▸ Nat.mul_dvd_mul_left c hd_dvd_q)

section FiniteRoots

variable [Finite ι]

variable (P σ C) in
/-- The set of `σ`-orbit sums of roots whose irreducible component lies in the `σ`-cycle of `C`. -/
noncomputable def componentCycleFoldedIndices : Set M :=
  {x | ∃ j : ι, _root_.Equiv.Perm.SameCycle σ.componentEquiv C (P.componentOf j) ∧
    P.orbitSum σ j = x}

theorem mem_componentCycleFoldedIndices {x : M} :
    x ∈ P.componentCycleFoldedIndices σ C ↔
      ∃ j : ι, _root_.Equiv.Perm.SameCycle σ.componentEquiv C (P.componentOf j) ∧
        P.orbitSum σ j = x :=
  Iff.rfl

theorem orbitSum_mem_componentCycleFoldedIndices_of_mem_supp (i : C.supp) :
    P.orbitSum σ (i : ι) ∈ P.componentCycleFoldedIndices σ C := by
  have hi : P.componentOf (i : ι) = C := i.2
  exact ⟨i, by rw [hi], rfl⟩

variable (P σ C) in
/-- Every folded vector attached to the component cycle of `C` is the `σ`-orbit sum of a root in
`C.supp` itself. -/
theorem componentCycleFoldedIndices_eq_range_supp :
    P.componentCycleFoldedIndices σ C = Set.range fun i : C.supp ↦ P.orbitSum σ (i : ι) := by
  ext x
  refine ⟨?_, ?_⟩
  · rintro ⟨j, hj, rfl⟩
    obtain ⟨k, hk⟩ := hj.symm.exists_nat_pow_eq
    have hk' : P.componentOf ((σ.indexEquiv ^ k) j) = C := by
      rw [← σ.indexEquiv_pow, ← (σ ^ k).componentEquiv_componentOf, σ.componentEquiv_pow, hk]
    refine ⟨⟨(σ.indexEquiv ^ k) j, hk'⟩, ?_⟩
    exact P.orbitSum_eq_of_mem (P.mem_orbitIndices_iff_exists_pow.mpr ⟨k, rfl⟩)
  · rintro ⟨i, rfl⟩
    exact P.orbitSum_mem_componentCycleFoldedIndices_of_mem_supp i

variable (P σ C) in
theorem componentCycleFoldedIndices_subset_foldedIndices :
    P.componentCycleFoldedIndices σ C ⊆ P.foldedIndices σ := by
  rintro _ ⟨j, -, rfl⟩
  exact P.orbitSum_mem_foldedIndices σ j

variable (P σ C) in
theorem componentCycleFoldedIndices_subset_componentCycleSpace :
    P.componentCycleFoldedIndices σ C ⊆ P.componentCycleSpace σ C := by
  rintro _ ⟨j, hj, rfl⟩
  rw [P.orbitSum_def]
  refine Submodule.sum_mem _ fun k hk ↦ ?_
  obtain ⟨r, rfl⟩ := P.mem_orbitIndices_iff_exists_pow.mp hk
  have hcomp : _root_.Equiv.Perm.SameCycle σ.componentEquiv C
      (P.componentOf ((σ.indexEquiv ^ r) j)) := by
    rw [← σ.indexEquiv_pow, ← (σ ^ r).componentEquiv_componentOf, σ.componentEquiv_pow]
    exact hj.trans ⟨(r : ℤ), by simp⟩
  exact P.componentSpace_le_componentCycleSpace hcomp (P.root_mem_componentSpace _)

variable (P σ) in
/-- **The folded indices of `σ` are the union of the cycle-folded indices over all component
cycles** (including when `ι` is empty). -/
theorem iUnion_componentCycleFoldedIndices :
    (⋃ O : Quotient (_root_.Equiv.Perm.SameCycle.setoid σ.componentEquiv),
      P.componentCycleFoldedIndices σ O.out) = P.foldedIndices σ := by
  refine Set.Subset.antisymm
    (Set.iUnion_subset fun O ↦ P.componentCycleFoldedIndices_subset_foldedIndices σ O.out) ?_
  intro x hx
  obtain ⟨j, rfl⟩ := P.mem_foldedIndices.mp hx
  exact Set.mem_iUnion.mpr ⟨⟦P.componentOf j⟧, j,
    (_root_.Equiv.Perm.sameCycle_out_iff σ.componentEquiv).mpr rfl, rfl⟩

/-- **Distinct component cycles contribute disjoint sets of folded vectors** whenever `0` is not an
orbit sum of `σ`. -/
theorem pairwise_disjoint_componentCycleFoldedIndices [P.IsRootSystem]
    (h0 : 0 ∉ P.foldedIndices σ) :
    Pairwise fun O₁ O₂ : Quotient (_root_.Equiv.Perm.SameCycle.setoid σ.componentEquiv) ↦
      Disjoint (P.componentCycleFoldedIndices σ O₁.out)
        (P.componentCycleFoldedIndices σ O₂.out) := by
  intro O₁ O₂ hO
  rw [Set.disjoint_left]
  intro x hx₁ hx₂
  have hdisj := (P.iSupIndep_componentCycleSpace σ).pairwiseDisjoint hO
  have hx0 : x = 0 := (Submodule.disjoint_def.mp hdisj) x
    (P.componentCycleFoldedIndices_subset_componentCycleSpace σ O₁.out hx₁)
    (P.componentCycleFoldedIndices_subset_componentCycleSpace σ O₂.out hx₂)
  exact h0 (hx0 ▸ P.componentCycleFoldedIndices_subset_foldedIndices σ O₁.out hx₁)

/-- For a base-preserving automorphism in characteristic zero, distinct component cycles contribute
pairwise disjoint sets of folded vectors. -/
theorem pairwise_disjoint_componentCycleFoldedIndices_of_base [CharZero R] [P.IsRootSystem]
    {b : P.Base} (hσ : ∀ j ∈ b.support, σ.indexEquiv j ∈ b.support) :
    Pairwise fun O₁ O₂ : Quotient (_root_.Equiv.Perm.SameCycle.setoid σ.componentEquiv) ↦
      Disjoint (P.componentCycleFoldedIndices σ O₁.out)
        (P.componentCycleFoldedIndices σ O₂.out) :=
  P.pairwise_disjoint_componentCycleFoldedIndices (P.zero_notMem_foldedIndices hσ)

end FiniteRoots

/-! #### Empty root systems and canonical root-form orthogonality -/

section Empty

variable [IsEmpty ι]

/-- An empty root index type has an empty type of irreducible components. -/
instance isEmpty_component : IsEmpty P.Component :=
  ⟨fun C ↦ C.exists_rep.elim (IsEmpty.elim ‹IsEmpty ι›)⟩

variable (P σ) in
@[simp]
theorem foldedIndices_eq_empty : P.foldedIndices σ = ∅ := by
  ext x
  simp

variable (P σ) in
theorem subsingleton_fixedSubmodule_of_isEmpty [P.IsRootSystem] :
    Subsingleton (LinearMap.fixedSubmodule σ.weightMap) := by
  have hzero (x : M) : x = 0 := by
    have hx : x ∈ (⊤ : Submodule R M) := Submodule.mem_top
    rw [← IsRootSystem.span_root_eq_top (P := P), Set.range_eq_empty, Submodule.span_empty] at hx
    exact (Submodule.mem_bot R).mp hx
  have : Subsingleton M := ⟨fun x y ↦ (hzero x).trans (hzero y).symm⟩
  infer_instance

end Empty

/-- Different component spaces are orthogonal under `P.RootForm` over any commutative ring, without
needing `2 ≠ 0`. -/
theorem rootForm_apply_eq_zero_of_mem_componentSpace [Fintype ι] {C D : P.Component}
    (hCD : C ≠ D) {x y : M} (hx : x ∈ P.componentSpace C) (hy : y ∈ P.componentSpace D) :
    P.RootForm x y = 0 := by
  rw [P.rootForm_apply_apply]
  refine Finset.sum_eq_zero fun k _ ↦ ?_
  by_cases hk : P.componentOf k = C
  · rw [P.coroot'_eq_zero_of_mem_componentSpace (hk ▸ hCD) hy, mul_zero]
  · rw [P.coroot'_eq_zero_of_mem_componentSpace hk hx, zero_mul]

end CommRing

/-! ### Return automorphism and diagonal transport over a field -/

section Field

variable {ι K M N : Type*} [Field K] [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]

section Finite

variable (P : RootPairing ι K M N) [Finite ι] [P.IsRootSystem] (σ : P.Aut) (C : P.Component)

/-- **The return automorphism of a component.** If `C` has cycle length
`c = Function.minimalPeriod σ.componentEquiv C`, then `σ ^ c` fixes `C` and restricts to an
automorphism of the irreducible component pairing `P.componentPairing C`. -/
noncomputable def componentReturnAut : (P.componentPairing C).Aut :=
  (σ ^ minimalPeriod σ.componentEquiv C).restrictComponentAut C
    (P.componentEquiv_pow_minimalPeriod σ C)

@[simp]
theorem coe_componentReturnAut_weightMap (u : P.componentSpace C) :
    ((P.componentReturnAut σ C).weightMap u : M) =
      (σ.weightMap ^ minimalPeriod σ.componentEquiv C) u := by
  simp [componentReturnAut]

theorem coe_componentReturnAut_weightEquiv (u : P.componentSpace C) :
    ((P.componentReturnAut σ C).weightEquiv u : M) =
      (σ.weightMap ^ minimalPeriod σ.componentEquiv C) u := by
  simp [componentReturnAut]

@[simp]
theorem coe_componentReturnAut_coweightMap (v : P.corootComponentSpace C) :
    ((P.componentReturnAut σ C).coweightMap v : N) =
      (σ ^ minimalPeriod σ.componentEquiv C).coweightMap v := by
  simp [componentReturnAut]

@[simp]
theorem coe_componentReturnAut_indexEquiv (i : C.supp) :
    ((P.componentReturnAut σ C).indexEquiv i : ι) =
      (σ.indexEquiv ^ minimalPeriod σ.componentEquiv C) i := by
  simp [componentReturnAut]

@[simp]
theorem coe_componentReturnAut_indexEquiv_pow (k : ℕ) (i : C.supp) :
    (((P.componentReturnAut σ C).indexEquiv ^ k) i : ι) =
      ((σ.indexEquiv ^ minimalPeriod σ.componentEquiv C) ^ k) i := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', pow_succ', _root_.Equiv.Perm.mul_apply, _root_.Equiv.Perm.mul_apply,
      coe_componentReturnAut_indexEquiv, ih]

variable {P σ C} in
/-- When `σ` fixes the component `C`, the return automorphism is simply the component restriction
of `σ` itself (`c = 1`). -/
theorem componentReturnAut_of_componentEquiv_eq (hC : σ.componentEquiv C = C) :
    P.componentReturnAut σ C = σ.restrictComponentAut C hC := by
  have hc : minimalPeriod σ.componentEquiv C = 1 :=
    minimalPeriod_eq_one_iff_isFixedPt.mpr hC
  exact Equiv.restrictComponentAut_congr (by rw [hc, pow_one]) _ hC

@[simp]
theorem componentReturnAut_one : P.componentReturnAut 1 C = 1 := by
  rw [componentReturnAut_of_componentEquiv_eq (by simp), Equiv.restrictComponentAut_one]

/-- **Restriction of `P.componentProj C` to `σ`-fixed weights**, landing in the fixed space of the
return automorphism `P.componentReturnAut σ C`. -/
noncomputable def componentCycleFixedProj :
    LinearMap.fixedSubmodule σ.weightMap →ₗ[K]
      LinearMap.fixedSubmodule (P.componentReturnAut σ C).weightMap where
  toFun y := ⟨P.componentProj C (y : M), LinearMap.mem_fixedSubmodule_iff.mpr <| Subtype.ext <| by
    rw [P.coe_componentReturnAut_weightMap]
    exact P.pow_minimalPeriod_weightMap_componentProj σ C
      (LinearMap.mem_fixedSubmodule_iff.mp y.2)⟩
  map_add' x y := Subtype.ext (map_add (P.componentProj C) (x : M) (y : M))
  map_smul' r x := Subtype.ext (map_smul (P.componentProj C) r (x : M))

@[simp]
theorem val_componentCycleFixedProj_apply (y : LinearMap.fixedSubmodule σ.weightMap) :
    (P.componentCycleFixedProj σ C y : P.componentSpace C) = P.componentProj C (y : M) :=
  (rfl)

theorem coe_componentCycleFixedProj_apply (y : LinearMap.fixedSubmodule σ.weightMap) :
    ((P.componentCycleFixedProj σ C y : P.componentSpace C) : M) = P.componentProj C (y : M) :=
  (rfl)

private theorem sum_range_pow_weightMap_mem_fixedSubmodule
    (u : LinearMap.fixedSubmodule (P.componentReturnAut σ C).weightMap) :
    ∑ r ∈ range (minimalPeriod σ.componentEquiv C), (σ.weightMap ^ r) (u : M) ∈
      LinearMap.fixedSubmodule σ.weightMap := by
  rw [LinearMap.mem_fixedSubmodule_iff, map_sum]
  set c := minimalPeriod σ.componentEquiv C
  have hret : (σ.weightMap ^ c) (u : M) = (u : M) := by
    rw [← P.coe_componentReturnAut_weightMap σ C u.1]
    exact congrArg Subtype.val (LinearMap.mem_fixedSubmodule_iff.mp u.2)
  have hstep (r : ℕ) :
      σ.weightMap ((σ.weightMap ^ r) (u : M)) = (σ.weightMap ^ (r + 1)) (u : M) := by
    rw [pow_succ', Module.End.mul_eq_comp, LinearMap.comp_apply]
  simp_rw [hstep]
  refine add_right_cancel (b := (u : M)) ?_
  have h1 := (Finset.sum_range_succ' (fun r ↦ (σ.weightMap ^ r) (u : M)) c).symm
  have h2 := Finset.sum_range_succ (fun r ↦ (σ.weightMap ^ r) (u : M)) c
  simpa only [pow_zero, Module.End.one_eq_id, LinearMap.id_apply, hret] using h1.trans h2

/-- **Diagonal transport from the return fixed space to the cycle fixed space.** Sending a return
fixed vector `u ∈ V_C^(σ ^ c)` to `∑ r ∈ range c, (σ.weightMap ^ r) u` is a `K`-linear isomorphism
onto `P.componentCycleFixedSubmodule σ C`, with inverse given by `P.componentCycleFixedProj σ C`. -/
noncomputable def componentCycleDiag :
    LinearMap.fixedSubmodule (P.componentReturnAut σ C).weightMap ≃ₗ[K]
      P.componentCycleFixedSubmodule σ C where
  toFun u := ⟨⟨∑ r ∈ range (minimalPeriod σ.componentEquiv C), (σ.weightMap ^ r) (u : M),
      P.sum_range_pow_weightMap_mem_fixedSubmodule σ C u⟩, by
    rw [mem_componentCycleFixedSubmodule]
    dsimp only
    exact Submodule.sum_mem (P.componentCycleSpace σ C) fun r _ ↦
      P.pow_weightMap_mem_componentCycleSpace
        (P.self_componentSpace_le_componentCycleSpace σ C u.1.2) r⟩
  map_add' u v := Subtype.ext <| Subtype.ext <| by
    simp [Finset.sum_add_distrib]
  map_smul' a u := Subtype.ext <| Subtype.ext <| by
    simp [Finset.smul_sum]
  invFun y := P.componentCycleFixedProj σ C y.1
  left_inv u := Subtype.ext (P.componentProj_sum_range_pow_weightMap u.1.2)
  right_inv y := Subtype.ext <| Subtype.ext <|
    P.sum_range_pow_weightMap_componentProj y.2 (LinearMap.mem_fixedSubmodule_iff.mp y.1.2)

theorem coe_componentCycleDiag_apply
    (u : LinearMap.fixedSubmodule (P.componentReturnAut σ C).weightMap) :
    ((P.componentCycleDiag σ C u : LinearMap.fixedSubmodule σ.weightMap) : M) =
      ∑ r ∈ range (minimalPeriod σ.componentEquiv C), (σ.weightMap ^ r) (u : M) :=
  (rfl)

@[simp]
theorem componentCycleDiag_symm_apply (y : P.componentCycleFixedSubmodule σ C) :
    (P.componentCycleDiag σ C).symm y = P.componentCycleFixedProj σ C y.1 :=
  (rfl)

@[simp]
theorem componentProj_componentCycleDiag
    (u : LinearMap.fixedSubmodule (P.componentReturnAut σ C).weightMap) :
    P.componentProj C ((P.componentCycleDiag σ C u : LinearMap.fixedSubmodule σ.weightMap) : M) =
      (u : P.componentSpace C) :=
  P.componentProj_sum_range_pow_weightMap u.1.2

@[simp]
theorem componentCycleFixedProj_componentCycleDiag
    (u : LinearMap.fixedSubmodule (P.componentReturnAut σ C).weightMap) :
    P.componentCycleFixedProj σ C (P.componentCycleDiag σ C u) = u :=
  (P.componentCycleDiag σ C).symm_apply_apply u

variable {P σ C} in
theorem componentCycleDiag_componentCycleFixedProj_of_mem {y : LinearMap.fixedSubmodule σ.weightMap}
    (hy : y ∈ P.componentCycleFixedSubmodule σ C) :
    P.componentCycleDiag σ C (P.componentCycleFixedProj σ C y) = ⟨y, hy⟩ :=
  (P.componentCycleDiag σ C).apply_symm_apply ⟨y, hy⟩

variable {P σ C} in
theorem componentCycleFixedProj_eq_zero_of_not_sameCycle {D : P.Component}
    (hCD : ¬_root_.Equiv.Perm.SameCycle σ.componentEquiv D C)
    {y : LinearMap.fixedSubmodule σ.weightMap} (hy : y ∈ P.componentCycleFixedSubmodule σ D) :
    P.componentCycleFixedProj σ C y = 0 :=
  Subtype.ext (P.componentProj_eq_zero_of_not_sameCycle hy hCD)

variable {P σ C} in
/-- When `σ` fixes `C` (`c = 1`), `componentCycleDiag` acts as the identity on ambient vectors. -/
theorem coe_componentCycleDiag_of_componentEquiv_eq (hC : σ.componentEquiv C = C)
    (u : LinearMap.fixedSubmodule (P.componentReturnAut σ C).weightMap) :
    ((P.componentCycleDiag σ C u : LinearMap.fixedSubmodule σ.weightMap) : M) = (u : M) := by
  rw [P.coe_componentCycleDiag_apply, minimalPeriod_eq_one_iff_isFixedPt.mpr hC,
    Finset.sum_range_one, pow_zero, Module.End.one_eq_id, LinearMap.id_apply]

/-! ### Orbit sizes and distinct orbit-sum transport -/

theorem minimalPeriod_componentReturnAut_indexEquiv (i : C.supp) :
    minimalPeriod (P.componentReturnAut σ C).indexEquiv i =
      minimalPeriod (σ.indexEquiv ^ minimalPeriod σ.componentEquiv C) (i : ι) := by
  set c := minimalPeriod σ.componentEquiv C
  set d₁ := minimalPeriod (P.componentReturnAut σ C).indexEquiv i
  set d₂ := minimalPeriod (σ.indexEquiv ^ c) (i : ι)
  refine Nat.dvd_antisymm ?_ ?_
  · have h : (⇑(P.componentReturnAut σ C).indexEquiv)^[d₂] i = i := by
      rw [← _root_.Equiv.Perm.coe_pow]
      apply Subtype.ext
      rw [P.coe_componentReturnAut_indexEquiv_pow, _root_.Equiv.Perm.coe_pow]
      exact isPeriodicPt_minimalPeriod (σ.indexEquiv ^ c) (i : ι)
    exact IsPeriodicPt.minimalPeriod_dvd h
  · have h : (⇑(σ.indexEquiv ^ c))^[d₁] (i : ι) = (i : ι) := by
      rw [← _root_.Equiv.Perm.coe_pow, ← P.coe_componentReturnAut_indexEquiv_pow,
        _root_.Equiv.Perm.coe_pow, isPeriodicPt_minimalPeriod]
    exact IsPeriodicPt.minimalPeriod_dvd h

/-- **Minimal period factorization via the return automorphism.** For `i : C.supp`, the period of
`i` under `σ.indexEquiv` is the cycle length of `C` times the period of `i` under
`(P.componentReturnAut σ C).indexEquiv`. -/
theorem minimalPeriod_indexEquiv_eq_mul_componentReturnAut (i : C.supp) :
    minimalPeriod σ.indexEquiv (i : ι) =
      minimalPeriod σ.componentEquiv C *
        minimalPeriod (P.componentReturnAut σ C).indexEquiv i := by
  have hi : P.componentOf (i : ι) = C := i.2
  rw [P.minimalPeriod_indexEquiv_eq_mul σ (i : ι), hi,
    P.minimalPeriod_componentReturnAut_indexEquiv σ C i]

/-- **Orbit-size factorization.** The `σ`-orbit of `i : C.supp` has cardinality `c` times the
cardinality of its return orbit in `P.componentPairing C`. -/
theorem card_orbitIndices_eq_mul_componentReturnAut (i : C.supp) :
    #(P.orbitIndices σ (i : ι)) =
      minimalPeriod σ.componentEquiv C *
        #((P.componentPairing C).orbitIndices (P.componentReturnAut σ C) i) := by
  rw [P.card_orbitIndices, (P.componentPairing C).card_orbitIndices,
    P.minimalPeriod_indexEquiv_eq_mul_componentReturnAut]

/-- The `τ`-orbit sum of `i : C.supp` in `P.componentPairing C`, packaged as an element of the
return fixed submodule. -/
noncomputable def componentReturnOrbitSumFixed (i : C.supp) :
    LinearMap.fixedSubmodule (P.componentReturnAut σ C).weightMap :=
  ⟨(P.componentPairing C).orbitSum (P.componentReturnAut σ C) i,
    (P.componentPairing C).orbitSum_mem_fixedSubmodule (P.componentReturnAut σ C) i⟩

@[simp]
theorem coe_componentReturnOrbitSumFixed (i : C.supp) :
    (P.componentReturnOrbitSumFixed σ C i : P.componentSpace C) =
      (P.componentPairing C).orbitSum (P.componentReturnAut σ C) i :=
  (rfl)

/-- **Diagonal transport carries return orbit sums to ambient orbit sums.** -/
@[simp]
theorem coe_componentCycleDiag_orbitSum (i : C.supp) :
    ((P.componentCycleDiag σ C (P.componentReturnOrbitSumFixed σ C i) :
        LinearMap.fixedSubmodule σ.weightMap) : M) =
      P.orbitSum σ (i : ι) := by
  rw [P.coe_componentCycleDiag_apply]
  set c := minimalPeriod σ.componentEquiv C
  set τ := P.componentReturnAut σ C
  set d := minimalPeriod τ.indexEquiv i
  have hret : ((P.componentReturnOrbitSumFixed σ C i : P.componentSpace C) : M) =
      ∑ q ∈ range d, P.root ((σ.indexEquiv ^ (c * q)) (i : ι)) := by
    rw [coe_componentReturnOrbitSumFixed, (P.componentPairing C).orbitSum_eq_sum_range,
      Submodule.coe_sum]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    rw [P.coe_componentPairing_root, P.coe_componentReturnAut_indexEquiv_pow, ← pow_mul]
  rw [hret]
  have hstep (r q : ℕ) :
      (σ.weightMap ^ r) (P.root ((σ.indexEquiv ^ (c * q)) (i : ι))) =
        P.root ((σ.indexEquiv ^ (c * q + r)) (i : ι)) := by
    rw [← σ.weightMap_pow, Hom.root_weightMap_apply P P _ (σ ^ r).toHom, σ.indexEquiv_pow,
      Nat.add_comm, pow_add, _root_.Equiv.Perm.mul_apply]
  simp_rw [map_sum, hstep]
  rw [Finset.sum_comm,
    ← Finset.sum_range_mul_eq_sum_sum (fun l ↦ P.root ((σ.indexEquiv ^ l) (i : ι))) c d,
    ← P.minimalPeriod_indexEquiv_eq_mul_componentReturnAut σ C i, ← P.orbitSum_eq_sum_range]

/-- Two roots in `C.supp` have the same ambient `σ`-orbit sum in `M` if and only if they have the
same return orbit sum in `P.componentPairing C`. -/
theorem orbitSum_eq_iff_componentReturnAut (i j : C.supp) :
    P.orbitSum σ (i : ι) = P.orbitSum σ (j : ι) ↔
      (P.componentPairing C).orbitSum (P.componentReturnAut σ C) i =
        (P.componentPairing C).orbitSum (P.componentReturnAut σ C) j := by
  rw [← P.coe_componentCycleDiag_orbitSum σ C i, ← P.coe_componentCycleDiag_orbitSum σ C j]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have hEq : P.componentReturnOrbitSumFixed σ C i = P.componentReturnOrbitSumFixed σ C j :=
      (P.componentCycleDiag σ C).injective (Subtype.ext (Subtype.ext h))
    exact congrArg Subtype.val hEq
  · exact congrArg (fun u ↦ ((P.componentCycleDiag σ C u : _) : M)) (Subtype.ext h)

private theorem mem_fixedSubmodule_of_mem_componentFoldedIndices
    {v : P.componentSpace C}
    (hv : v ∈ (P.componentPairing C).foldedIndices (P.componentReturnAut σ C)) :
    v ∈ LinearMap.fixedSubmodule (P.componentReturnAut σ C).weightMap := by
  obtain ⟨i, rfl⟩ := (P.componentPairing C).mem_foldedIndices.mp hv
  exact (P.componentPairing C).orbitSum_mem_fixedSubmodule _ i

/-- **Bijection of distinct folded root vectors on a component cycle.** `P.componentCycleDiag σ C`
maps the folded indices of `(P.componentPairing C, P.componentReturnAut σ C)` bijectively onto
`P.componentCycleFoldedIndices σ C`. -/
noncomputable def componentCycleFoldedIndicesEquiv :
    (P.componentPairing C).foldedIndices (P.componentReturnAut σ C) ≃
      P.componentCycleFoldedIndices σ C where
  toFun v := ⟨((P.componentCycleDiag σ C
      ⟨v.1, P.mem_fixedSubmodule_of_mem_componentFoldedIndices σ C v.2⟩ :
        LinearMap.fixedSubmodule σ.weightMap) : M), by
    obtain ⟨i, hi⟩ := (P.componentPairing C).mem_foldedIndices.mp v.2
    have hEq : (⟨v.1, P.mem_fixedSubmodule_of_mem_componentFoldedIndices σ C v.2⟩ :
        LinearMap.fixedSubmodule (P.componentReturnAut σ C).weightMap) =
        P.componentReturnOrbitSumFixed σ C i := Subtype.ext hi.symm
    rw [hEq, P.coe_componentCycleDiag_orbitSum]
    exact P.orbitSum_mem_componentCycleFoldedIndices_of_mem_supp i⟩
  invFun w := ⟨P.componentProj C w.1, by
    have hw : w.1 ∈ Set.range fun i : C.supp ↦ P.orbitSum σ (i : ι) :=
      P.componentCycleFoldedIndices_eq_range_supp σ C ▸ w.2
    obtain ⟨i, hi⟩ := hw
    dsimp only at hi
    refine (P.componentPairing C).mem_foldedIndices.mpr ⟨i, ?_⟩
    rw [← hi, ← P.coe_componentCycleDiag_orbitSum σ C i, P.componentProj_componentCycleDiag,
      P.coe_componentReturnOrbitSumFixed]⟩
  left_inv v := Subtype.ext <| by
    dsimp only
    rw [P.coe_componentCycleDiag_apply]
    exact P.componentProj_sum_range_pow_weightMap v.1.2
  right_inv w := Subtype.ext <| by
    dsimp only
    rw [P.coe_componentCycleDiag_apply]
    have hw_range : w.1 ∈ Set.range fun i : C.supp ↦ P.orbitSum σ (i : ι) :=
      P.componentCycleFoldedIndices_eq_range_supp σ C ▸ w.2
    obtain ⟨i, hi⟩ := hw_range
    dsimp only at hi
    have hw : σ.weightMap w.1 = w.1 := by
      rw [← hi]
      exact P.weightMap_orbitSum_self σ (i : ι)
    exact P.sum_range_pow_weightMap_componentProj
      (P.componentCycleFoldedIndices_subset_componentCycleSpace σ C w.2) hw

@[simp]
theorem coe_componentCycleFoldedIndicesEquiv_apply
    (v : (P.componentPairing C).foldedIndices (P.componentReturnAut σ C)) :
    (P.componentCycleFoldedIndicesEquiv σ C v : M) =
      ∑ r ∈ range (minimalPeriod σ.componentEquiv C), (σ.weightMap ^ r) (v.1 : M) :=
  (rfl)

@[simp]
theorem coe_componentCycleFoldedIndicesEquiv_symm_apply (w : P.componentCycleFoldedIndices σ C) :
    ((P.componentCycleFoldedIndicesEquiv σ C).symm w : P.componentSpace C) =
      P.componentProj C w.1 :=
  (rfl)

/-! ### Scaling of invariant bilinear forms under `componentCycleDiag` -/

/-- **Scaling of any `σ`-invariant `B : P.InvariantForm` along `componentCycleDiag`** when
`2 ≠ 0`. -/
theorem InvariantForm.form_componentCycleDiag [NeZero (2 : K)] (B : P.InvariantForm) {σ : P.Aut}
    (hB : ∀ x y, B.form (σ.weightMap x) (σ.weightMap y) = B.form x y) (C : P.Component)
    (u v : LinearMap.fixedSubmodule (P.componentReturnAut σ C).weightMap) :
    B.form ((P.componentCycleDiag σ C u : LinearMap.fixedSubmodule σ.weightMap) : M)
        ((P.componentCycleDiag σ C v : LinearMap.fixedSubmodule σ.weightMap) : M) =
      (minimalPeriod σ.componentEquiv C : K) * (B.restrictComponent C).form u.1 v.1 := by
  have hpow (r : ℕ) (x y : M) :
      B.form ((σ.weightMap ^ r) x) ((σ.weightMap ^ r) y) = B.form x y := by
    induction r with
    | zero => rfl
    | succ r ih =>
      rw [pow_succ', Module.End.mul_eq_comp, LinearMap.comp_apply, LinearMap.comp_apply, hB, ih]
  set c := minimalPeriod σ.componentEquiv C
  rw [P.coe_componentCycleDiag_apply, P.coe_componentCycleDiag_apply]
  simp only [map_sum, LinearMap.sum_apply]
  have hdiag : ∀ s ∈ range c,
      (∑ r ∈ range c, B.form ((σ.weightMap ^ r) (u : M)) ((σ.weightMap ^ s) (v : M))) =
        (B.restrictComponent C).form u.1 v.1 := by
    intro s hs
    rw [Finset.sum_eq_single s]
    · rw [hpow s (u : M) (v : M), B.restrictComponent_form_apply]
    · intro r hr hrs
      have hne : (σ.componentEquiv ^ r) C ≠ (σ.componentEquiv ^ s) C := fun hEq ↦ hrs (by
        rw [_root_.Equiv.Perm.coe_pow, _root_.Equiv.Perm.coe_pow] at hEq
        exact (iterate_eq_iterate_iff_of_lt_minimalPeriod
          (Finset.mem_range.mp hr) (Finset.mem_range.mp hs)).mp hEq)
      exact B.apply_eq_zero_of_mem_componentSpace hne
        (P.pow_weightMap_mem_componentSpace u.1.2 r)
        (P.pow_weightMap_mem_componentSpace v.1.2 s)
    · exact fun h ↦ absurd hs h
  rw [Finset.sum_congr rfl hdiag, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **Cartan ratios for any `σ`-invariant `B : P.InvariantForm` are preserved unchanged by
`componentCycleDiag`** in characteristic zero. -/
theorem InvariantForm.cartanRatio_componentCycleDiag [CharZero K] (B : P.InvariantForm)
    {σ : P.Aut} (hB : ∀ x y, B.form (σ.weightMap x) (σ.weightMap y) = B.form x y)
    (C : P.Component) (u v : LinearMap.fixedSubmodule (P.componentReturnAut σ C).weightMap) :
    2 * B.form ((P.componentCycleDiag σ C u : LinearMap.fixedSubmodule σ.weightMap) : M)
          ((P.componentCycleDiag σ C v : LinearMap.fixedSubmodule σ.weightMap) : M) /
        B.form ((P.componentCycleDiag σ C v : LinearMap.fixedSubmodule σ.weightMap) : M)
          ((P.componentCycleDiag σ C v : LinearMap.fixedSubmodule σ.weightMap) : M) =
      2 * (B.restrictComponent C).form u.1 v.1 /
        (B.restrictComponent C).form v.1 v.1 := by
  have hc : (minimalPeriod σ.componentEquiv C : K) ≠ 0 :=
    Nat.cast_ne_zero.mpr (P.minimalPeriod_componentEquiv_pos σ C).ne'
  rw [B.form_componentCycleDiag P hB C, B.form_componentCycleDiag P hB C,
    mul_left_comm (2 : K), mul_div_mul_left _ _ hc]

/-! ### Independence of the starting component and product assembly across cycles -/

/-- **Changing the starting component conjugates the return automorphism.** Moving from `C` to
`(σ ^ k).componentEquiv C` along `(σ ^ k).restrictComponent C` conjugates
`P.componentReturnAut σ C` to `P.componentReturnAut σ ((σ ^ k).componentEquiv C)`. -/
theorem autCongr_componentReturnAut_pow (k : ℕ) :
    ((σ ^ k).restrictComponent C).autCongr (P.componentReturnAut σ C) =
      P.componentReturnAut σ ((σ ^ k).componentEquiv C) := by
  rw [componentReturnAut, (σ ^ k).autCongr_restrictComponentAut, componentReturnAut]
  refine Equiv.restrictComponentAut_congr ?_ _ _
  have hmul (a b : P.Aut) : Equiv.comp a b = a * b := (rfl)
  have hinv (a : P.Aut) : Equiv.symm P P a = a⁻¹ := (rfl)
  rw [P.minimalPeriod_componentEquiv_pow_apply σ C k, Equiv.autCongr_apply, hinv, hmul, hmul,
    ← mul_assoc, (Commute.pow_pow_self σ k _).eq, mul_assoc, mul_inv_cancel, mul_one]

/-- Transport of return fixed vectors from `C` to `(σ ^ k).componentEquiv C` by
`σ.weightMap ^ k`. -/
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

@[simp]
theorem coe_componentReturnFixedShift_apply (k : ℕ)
    (u : LinearMap.fixedSubmodule (P.componentReturnAut σ C).weightMap) :
    ((P.componentReturnFixedShift σ C k u :
        P.componentSpace ((σ ^ k).componentEquiv C)) : M) =
      (σ.weightMap ^ k) (u : M) := by
  simp [componentReturnFixedShift]

/-- Projecting a `σ`-fixed weight to `(σ ^ k).componentEquiv C` shifts its `C`-projection by
`σ.weightMap ^ k`. -/
theorem componentCycleFixedProj_pow (k : ℕ) (y : LinearMap.fixedSubmodule σ.weightMap) :
    P.componentCycleFixedProj σ ((σ ^ k).componentEquiv C) y =
      P.componentReturnFixedShift σ C k (P.componentCycleFixedProj σ C y) := by
  apply Subtype.ext
  apply Subtype.ext
  rw [P.coe_componentReturnFixedShift_apply, P.coe_componentCycleFixedProj_apply,
    P.coe_componentCycleFixedProj_apply, σ.componentEquiv_pow,
    ← σ.coe_componentProj_pow_weightMap k C (y : M),
    LinearMap.pow_apply_of_mem_fixedSubmodule σ.weightMap y.2 k]

/-- **Independence of the starting component.** Shifting `u` along `σ ^ k` to
`(σ ^ k).componentEquiv C` and applying `componentCycleDiag` produces the exact same ambient
`σ`-fixed vector as applying `componentCycleDiag` at `C`. -/
theorem coe_componentCycleDiag_componentReturnFixedShift (k : ℕ)
    (u : LinearMap.fixedSubmodule (P.componentReturnAut σ C).weightMap) :
    ((P.componentCycleDiag σ ((σ ^ k).componentEquiv C)
        (P.componentReturnFixedShift σ C k u) : LinearMap.fixedSubmodule σ.weightMap) : M) =
      ((P.componentCycleDiag σ C u : LinearMap.fixedSubmodule σ.weightMap) : M) := by
  set y : LinearMap.fixedSubmodule σ.weightMap := (P.componentCycleDiag σ C u).1
  have hy : y ∈ P.componentCycleFixedSubmodule σ ((σ ^ k).componentEquiv C) := by
    rw [mem_componentCycleFixedSubmodule]
    have hsc : _root_.Equiv.Perm.SameCycle σ.componentEquiv C ((σ ^ k).componentEquiv C) :=
      ⟨(k : ℤ), by simp [σ.componentEquiv_pow]⟩
    rw [← P.componentCycleSpace_eq_of_sameCycle hsc]
    exact (P.componentCycleDiag σ C u).2
  have hproj : P.componentReturnFixedShift σ C k u =
      P.componentCycleFixedProj σ ((σ ^ k).componentEquiv C) y := by
    rw [P.componentCycleFixedProj_pow σ C k y, P.componentCycleFixedProj_componentCycleDiag]
  rw [hproj, P.componentCycleDiag_componentCycleFixedProj_of_mem hy]

/-- **Product decomposition of the full `σ`-fixed weight space across all component cycles.** -/
noncomputable def componentCycleFixedPiEquiv :
    LinearMap.fixedSubmodule σ.weightMap ≃ₗ[K]
      ∀ O : Quotient (_root_.Equiv.Perm.SameCycle.setoid σ.componentEquiv),
        LinearMap.fixedSubmodule (P.componentReturnAut σ O.out).weightMap := by
  haveI := Fintype.ofFinite (Quotient (_root_.Equiv.Perm.SameCycle.setoid σ.componentEquiv))
  exact
    { toFun y O := P.componentCycleFixedProj σ O.out y
      map_add' x y := funext fun O ↦ map_add (P.componentCycleFixedProj σ O.out) x y
      map_smul' r x := funext fun O ↦ map_smul (P.componentCycleFixedProj σ O.out) r x
      invFun f := ∑ O, (P.componentCycleDiag σ O.out (f O)).1
      left_inv y := Subtype.ext <| by
        cases nonempty_fintype P.Component
        simp only [Submodule.coe_sum, coe_componentCycleDiag_apply,
          coe_componentCycleFixedProj_apply]
        have hterm (O : Quotient (_root_.Equiv.Perm.SameCycle.setoid σ.componentEquiv)) (r : ℕ) :
            (σ.weightMap ^ r) (P.componentProj O.out (y : M)) =
              (P.componentProj ((σ.componentEquiv ^ r) O.out) (y : M) : M) := by
          rw [← σ.coe_componentProj_pow_weightMap r O.out (y : M),
            LinearMap.pow_apply_of_mem_fixedSubmodule σ.weightMap y.2 r]
        simp_rw [hterm]
        rw [_root_.Equiv.Perm.sum_quotient_sameCycle_sum_range σ.componentEquiv
          (fun D ↦ (P.componentProj D (y : M) : M))]
        exact P.sum_componentProj (y : M)
      right_inv f := funext fun O ↦ by
        dsimp only
        rw [map_sum, Finset.sum_eq_single O]
        · exact P.componentCycleFixedProj_componentCycleDiag σ O.out (f O)
        · intro O' _ hO'
          have hnot : ¬_root_.Equiv.Perm.SameCycle σ.componentEquiv O'.out O.out := fun hsc ↦
            hO' (by
              rw [← (_root_.Equiv.Perm.sameCycle_out_iff σ.componentEquiv).mp hsc,
                Quotient.out_eq])
          exact P.componentCycleFixedProj_eq_zero_of_not_sameCycle hnot
            (P.componentCycleDiag σ O'.out (f O')).2
        · exact fun h ↦ absurd (Finset.mem_univ O) h }

@[simp]
theorem componentCycleFixedPiEquiv_apply (y : LinearMap.fixedSubmodule σ.weightMap)
    (O : Quotient (_root_.Equiv.Perm.SameCycle.setoid σ.componentEquiv)) :
    P.componentCycleFixedPiEquiv σ y O = P.componentCycleFixedProj σ O.out y :=
  (rfl)

theorem coe_componentCycleFixedPiEquiv_symm_apply
    [Fintype (Quotient (_root_.Equiv.Perm.SameCycle.setoid σ.componentEquiv))]
    (f : ∀ O : Quotient (_root_.Equiv.Perm.SameCycle.setoid σ.componentEquiv),
      LinearMap.fixedSubmodule (P.componentReturnAut σ O.out).weightMap) :
    ((P.componentCycleFixedPiEquiv σ).symm f : M) =
      ∑ O, ((P.componentCycleDiag σ O.out (f O) : LinearMap.fixedSubmodule σ.weightMap) : M) := by
  obtain rfl : ‹Fintype (Quotient (_root_.Equiv.Perm.SameCycle.setoid σ.componentEquiv))› =
      Fintype.ofFinite _ := Subsingleton.elim _ _
  simp [componentCycleFixedPiEquiv]

end Finite

/-! ### Scaling and orthogonal decomposition of the canonical `RootForm` -/

section RootForm

variable (P : RootPairing ι K M N) [Fintype ι] [P.IsRootSystem] (σ : P.Aut) (C : P.Component)

/-- **Scaling of `P.RootForm` along `componentCycleDiag`.** Without needing `2 ≠ 0`, `P.RootForm`
multiplies by the cycle length `c = Function.minimalPeriod σ.componentEquiv C` under
`componentCycleDiag`. -/
theorem rootForm_componentCycleDiag [Fintype C.supp]
    (u v : LinearMap.fixedSubmodule (P.componentReturnAut σ C).weightMap) :
    P.RootForm ((P.componentCycleDiag σ C u : LinearMap.fixedSubmodule σ.weightMap) : M)
        ((P.componentCycleDiag σ C v : LinearMap.fixedSubmodule σ.weightMap) : M) =
      (minimalPeriod σ.componentEquiv C : K) * (P.componentPairing C).RootForm u.1 v.1 := by
  set c := minimalPeriod σ.componentEquiv C
  rw [P.coe_componentCycleDiag_apply, P.coe_componentCycleDiag_apply]
  simp only [map_sum, LinearMap.sum_apply]
  have hdiag : ∀ s ∈ range c,
      (∑ r ∈ range c, P.RootForm ((σ.weightMap ^ r) (u : M)) ((σ.weightMap ^ s) (v : M))) =
        (P.componentPairing C).RootForm u.1 v.1 := by
    intro s hs
    rw [Finset.sum_eq_single s]
    · rw [← σ.weightMap_pow, (σ ^ s).toHom.rootForm_weightMap, P.rootForm_componentPairing C]
      rfl
    · intro r hr hrs
      have hne : (σ.componentEquiv ^ r) C ≠ (σ.componentEquiv ^ s) C := fun hEq ↦ hrs (by
        rw [_root_.Equiv.Perm.coe_pow, _root_.Equiv.Perm.coe_pow] at hEq
        exact (iterate_eq_iterate_iff_of_lt_minimalPeriod
          (Finset.mem_range.mp hr) (Finset.mem_range.mp hs)).mp hEq)
      exact P.rootForm_apply_eq_zero_of_mem_componentSpace hne
        (P.pow_weightMap_mem_componentSpace u.1.2 r)
        (P.pow_weightMap_mem_componentSpace v.1.2 s)
    · exact fun h ↦ absurd hs h
  rw [Finset.sum_congr rfl hdiag, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **Cartan ratios for `P.RootForm` are preserved unchanged by `componentCycleDiag`** in
characteristic zero. -/
theorem rootForm_cartanRatio_componentCycleDiag [CharZero K] [Fintype C.supp]
    (u v : LinearMap.fixedSubmodule (P.componentReturnAut σ C).weightMap) :
    2 * P.RootForm ((P.componentCycleDiag σ C u : LinearMap.fixedSubmodule σ.weightMap) : M)
          ((P.componentCycleDiag σ C v : LinearMap.fixedSubmodule σ.weightMap) : M) /
        P.RootForm ((P.componentCycleDiag σ C v : LinearMap.fixedSubmodule σ.weightMap) : M)
          ((P.componentCycleDiag σ C v : LinearMap.fixedSubmodule σ.weightMap) : M) =
      2 * (P.componentPairing C).RootForm u.1 v.1 /
        (P.componentPairing C).RootForm v.1 v.1 := by
  have hc : (minimalPeriod σ.componentEquiv C : K) ≠ 0 :=
    Nat.cast_ne_zero.mpr (P.minimalPeriod_componentEquiv_pos σ C).ne'
  rw [P.rootForm_componentCycleDiag σ C, P.rootForm_componentCycleDiag σ C,
    mul_left_comm (2 : K), mul_div_mul_left _ _ hc]

/-- **Orthogonal decomposition of `P.RootForm` on `σ`-fixed weights across component cycles.** -/
theorem rootForm_eq_sum_componentCycleFixedProj
    [Fintype (Quotient (_root_.Equiv.Perm.SameCycle.setoid σ.componentEquiv))]
    [∀ O : Quotient (_root_.Equiv.Perm.SameCycle.setoid σ.componentEquiv), Fintype O.out.supp]
    (x y : LinearMap.fixedSubmodule σ.weightMap) :
    P.RootForm (x : M) (y : M) =
      ∑ O : Quotient (_root_.Equiv.Perm.SameCycle.setoid σ.componentEquiv),
        (minimalPeriod σ.componentEquiv O.out : K) *
          (P.componentPairing O.out).RootForm
            (P.componentCycleFixedProj σ O.out x).1
            (P.componentCycleFixedProj σ O.out y).1 := by
  have hx := (P.componentCycleFixedPiEquiv σ).symm_apply_apply x
  have hy := (P.componentCycleFixedPiEquiv σ).symm_apply_apply y
  conv_lhs => rw [← hx, ← hy]
  rw [P.coe_componentCycleFixedPiEquiv_symm_apply, P.coe_componentCycleFixedPiEquiv_symm_apply]
  simp only [map_sum, LinearMap.sum_apply, componentCycleFixedPiEquiv_apply]
  refine Finset.sum_congr rfl fun O _ ↦ ?_
  rw [Finset.sum_eq_single O]
  · exact P.rootForm_componentCycleDiag σ O.out _ _
  · intro O' _ hO'
    rw [P.coe_componentCycleDiag_apply, P.coe_componentCycleDiag_apply]
    simp only [map_sum, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun s _ ↦ Finset.sum_eq_zero fun r _ ↦ ?_
    have hne : (σ.componentEquiv ^ r) O'.out ≠ (σ.componentEquiv ^ s) O.out := fun hEq ↦ hO' (by
      have hsc₁ : _root_.Equiv.Perm.SameCycle σ.componentEquiv O'.out
          ((σ.componentEquiv ^ r) O'.out) := ⟨(r : ℤ), by simp⟩
      have hsc₂ : _root_.Equiv.Perm.SameCycle σ.componentEquiv O.out
          ((σ.componentEquiv ^ s) O.out) := ⟨(s : ℤ), by simp⟩
      have hsc : _root_.Equiv.Perm.SameCycle σ.componentEquiv O'.out O.out :=
        hsc₁.trans (hEq ▸ hsc₂.symm)
      rw [← (_root_.Equiv.Perm.sameCycle_out_iff σ.componentEquiv).mp hsc, Quotient.out_eq])
    exact P.rootForm_apply_eq_zero_of_mem_componentSpace hne
      (P.pow_weightMap_mem_componentSpace (P.componentCycleFixedProj σ O'.out x).1.2 r)
      (P.pow_weightMap_mem_componentSpace (P.componentCycleFixedProj σ O.out y).1.2 s)
  · exact fun h ↦ absurd (Finset.mem_univ O) h

end RootForm

end Field

end RootPairing
