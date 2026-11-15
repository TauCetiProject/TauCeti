/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.FixedSubmodule.Permutation
public import TauCeti.LinearAlgebra.RootSystem.Component.Cycle.Basic
import TauCeti.GroupTheory.Perm.Basic
import TauCeti.LinearAlgebra.RootSystem.HomInvariance

/-!
# Bases, simple-orbit coordinates, and positive cones on component cycles

When an automorphism `σ` of a root system `P` preserves a base `b`, the diagonal isomorphism
`RootPairing.componentCycleDiag P σ C` between the return fixed space
`LinearMap.fixedSubmodule (P.componentReturnAut σ C).weightMap` and the cycle fixed space
`P.componentCycleFixedSubmodule σ C` transports simple-root coordinates, orbit-sum bases, the
positive root cone, and the root lattice without distortion:

* Component projections `P.componentProj C` preserve simple-root coordinates inside `C`, kill
  simple-root coordinates outside `C`, and map both `TauCeti.posRootCone P b` and `P.rootSpan S`
  into themselves (`RootPairing.componentProj_mem_posRootCone`,
  `RootPairing.componentProj_mem_rootSpan`).
* Under `componentCycleDiag`, membership in `TauCeti.posRootCone P b` and in `P.rootSpan S` (in
  particular the integral root lattice `P.rootSpan ℤ`) is preserved iff-wise
  (`RootPairing.mem_posRootCone_componentCycleDiag_iff`,
  `RootPairing.mem_rootSpan_componentCycleDiag_iff`).
* Over any commutative ring `R`, the simple roots of `b` in `C` and in the `σ`-cycle of `C` form
  `R`-bases `RootPairing.Base.componentWeightBasis` and
  `RootPairing.Base.componentCycleWeightBasis` of `P.componentSpace C` and
  `P.componentCycleSpace σ C`, and their `σ`-orbit sums form an `R`-basis
  `RootPairing.Base.componentCycleSimpleOrbitBasis` of `P.componentCycleFixedSubmodule σ C`. Over a
  field `K`, taking `(σ ^ c)`-orbit sums produces the matching `K`-basis
  `RootPairing.Base.componentReturnSimpleOrbitBasis` of the return fixed space, carried onto
  `componentCycleSimpleOrbitBasis` along `RootPairing.Base.componentCycleSimpleOrbitEquiv` by
  `componentCycleDiag` (`RootPairing.Base.componentCycleDiag_componentReturnSimpleOrbitBasis`,
  `RootPairing.Base.componentCycleSimpleOrbitBasis_repr_componentCycleDiag`).

## Main definitions

* `RootPairing.Base.componentWeightBasis`, `RootPairing.Base.componentCycleWeightBasis`: the simple
  roots of `b` lying in `C` and in the `σ`-cycle of `C`, as `R`-bases of `P.componentSpace C` and
  `P.componentCycleSpace σ C`.
* `RootPairing.Base.componentReturnSupportPerm`, `RootPairing.Base.componentCycleSupportPerm`: the
  permutations induced by `σ ^ c` and `σ` on the simple roots in `C` and in the `σ`-cycle of `C`.
* `RootPairing.Base.componentCycleSimpleOrbitEquiv`: the bijection between `(σ ^ c)`-orbits of
  simple roots in `C` and `σ`-orbits of simple roots in the `σ`-cycle of `C`.
* `RootPairing.Base.componentCycleSimpleOrbitBasis`,
  `RootPairing.Base.componentReturnSimpleOrbitBasis`: the simple-orbit bases of the cycle fixed
  space (over `R`) and the return fixed space (over `K`).

## Main results

* `RootPairing.componentProj_mem_posRootCone`, `RootPairing.componentProj_mem_rootSpan`: component
  projections preserve `posRootCone P b` and `P.rootSpan S`.
* `RootPairing.mem_posRootCone_componentCycleDiag_iff`,
  `RootPairing.mem_rootSpan_componentCycleDiag_iff`: cone and root-lattice invariance under
  `componentCycleDiag`.
* `RootPairing.orbitSum_mem_posRootCone_iff_isPos`: in characteristic zero, an orbit sum lies in
  `posRootCone P b` iff the root is positive.
* `RootPairing.Base.componentCycleDiag_componentReturnSimpleOrbitBasis`,
  `RootPairing.Base.componentCycleSimpleOrbitBasis_repr_componentCycleDiag`: basis and coordinate
  transport along `componentCycleDiag`.
* `RootPairing.Base.mem_posRootCone_iff_forall_componentReturnSimpleOrbitBasis_repr`: cone
  membership on the return fixed space in terms of `ℕ`-valued simple-orbit coordinates.

## References

* J. R. Stembridge, *Folding by automorphisms*, note of 20 August 2008.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4-6*, Ch. VI §1, no. 7.
-/

public section

open Finset Function TauCeti

namespace RootPairing

/-! ### Simple-root coordinates and cone / root-span projections -/

section CommRing

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N)

private theorem root_mem_posRootCone_of_mem_support (b : P.Base) {j : ι} (hj : j ∈ b.support) :
    P.root j ∈ posRootCone P b := by
  classical
  exact (mem_posRootCone P b).mpr ⟨fun k ↦ if k = j then 1 else 0, by simp [hj]⟩

/-- In characteristic zero, for a base-preserving automorphism `σ`, an orbit sum `P.orbitSum σ i`
lies in `posRootCone P b` if and only if `i` is a positive root. -/
theorem orbitSum_mem_posRootCone_iff_isPos [Finite ι] [CharZero R] {σ : P.Aut} {b : P.Base}
    (hσ : ∀ j ∈ b.support, σ.indexEquiv j ∈ b.support) (i : ι) :
    P.orbitSum σ i ∈ posRootCone P b ↔ b.IsPos i := by
  refine ⟨fun hcone ↦ ?_, P.orbitSum_mem_posRootCone hσ⟩
  by_contra hni
  have hneg : b.IsPos (P.reflectionPerm i i) :=
    (isPos_reflectionPerm_self_iff_mem_negRoots P b i).mpr ((mem_negRoots P b i).mpr hni)
  have hneg_cone : -P.orbitSum σ i ∈ posRootCone P b := by
    rw [← P.orbitSum_reflectionPerm_self]
    exact P.orbitSum_mem_posRootCone hσ hneg
  exact P.orbitSum_ne_zero hσ i
    ((isPointed_posRootCone P b).eq_zero_of_mem_of_neg_mem hcone hneg_cone)

section IsRootSystem

variable [P.IsRootSystem]

private theorem coe_componentProj_root_of_eq {C : P.Component} {j : ι}
    (hj : P.componentOf j = C) :
    (P.componentProj C (P.root j) : M) = P.root j := by
  subst hj
  exact congrArg Subtype.val (P.componentProj_root_self j)

private theorem toWeightBasis_repr_componentProj_aux (b : P.Base) (C : P.Component) (x : M)
    (i : b.support) :
    b.toWeightBasis.repr (P.componentProj C x : M) i =
      open Classical in if P.componentOf (i : ι) = C then b.toWeightBasis.repr x i else 0 := by
  classical
  conv_lhs => rw [← b.toWeightBasis.sum_repr x]
  simp only [b.toWeightBasis_apply, map_sum, map_smul, Submodule.coe_sum,
    Submodule.coe_smul_of_tower, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · by_cases hi : P.componentOf (i : ι) = C
    · rw [P.coe_componentProj_root_of_eq hi, ← b.toWeightBasis_apply]
      simp [hi]
    · rw [P.componentProj_root_of_ne hi]
      simp [hi]
  · intro j _ hji
    by_cases hj : P.componentOf (j : ι) = C
    · rw [P.coe_componentProj_root_of_eq hj, ← b.toWeightBasis_apply]
      simp [Finsupp.single_eq_of_ne (Ne.symm hji)]
    · rw [P.componentProj_root_of_ne hj]
      simp
  · exact fun h ↦ absurd (Finset.mem_univ i) h

theorem toWeightBasis_repr_componentProj_of_eq (b : P.Base) {C : P.Component} {i : b.support}
    (hi : P.componentOf (i : ι) = C) (x : M) :
    b.toWeightBasis.repr (P.componentProj C x : M) i = b.toWeightBasis.repr x i := by
  rw [P.toWeightBasis_repr_componentProj_aux]
  simp [hi]

theorem toWeightBasis_repr_componentProj_of_ne (b : P.Base) {C : P.Component} {i : b.support}
    (hi : P.componentOf (i : ι) ≠ C) (x : M) :
    b.toWeightBasis.repr (P.componentProj C x : M) i = 0 := by
  rw [P.toWeightBasis_repr_componentProj_aux]
  simp [hi]

variable {P} in
/-- A vector in `P.componentSpace C` has zero coordinates along simple roots outside `C`. -/
theorem toWeightBasis_repr_eq_zero_of_mem_componentSpace (b : P.Base) {C : P.Component} {x : M}
    (hx : x ∈ P.componentSpace C) {i : b.support} (hi : P.componentOf (i : ι) ≠ C) :
    b.toWeightBasis.repr x i = 0 := by
  have hproj : (P.componentProj C x : M) = x :=
    congrArg Subtype.val (P.componentProj_apply_of_mem hx)
  rw [← hproj, P.toWeightBasis_repr_componentProj_of_ne b hi]

variable {P} in
/-- A vector in `P.componentCycleSpace σ C` has zero coordinates along simple roots outside the
`σ`-cycle of `C`. -/
theorem toWeightBasis_repr_eq_zero_of_mem_componentCycleSpace (b : P.Base) {σ : P.Aut}
    {C : P.Component} {x : M} (hx : x ∈ P.componentCycleSpace σ C) {i : b.support}
    (hi : ¬_root_.Equiv.Perm.SameCycle σ.componentEquiv C (P.componentOf (i : ι))) :
    b.toWeightBasis.repr x i = 0 := by
  rw [← P.toWeightBasis_repr_componentProj_of_eq b rfl x,
    P.componentProj_eq_zero_of_not_sameCycle hx hi, Submodule.coe_zero, map_zero,
    Finsupp.zero_apply]

/-- Component projections preserve the positive root cone of any base. -/
theorem componentProj_mem_posRootCone (b : P.Base) (C : P.Component) {x : M}
    (hx : x ∈ posRootCone P b) :
    (P.componentProj C x : M) ∈ posRootCone P b := by
  obtain ⟨f, rfl⟩ := (mem_posRootCone P b).mp hx
  rw [map_sum, Submodule.coe_sum]
  refine AddSubmonoid.sum_mem _ fun j hj ↦ ?_
  rw [map_nsmul, Submodule.coe_smul_of_tower]
  by_cases hjC : P.componentOf j = C
  · rw [P.coe_componentProj_root_of_eq hjC]
    exact AddSubmonoid.nsmul_mem _ (P.root_mem_posRootCone_of_mem_support b hj) _
  · rw [P.componentProj_root_of_ne hjC, Submodule.coe_zero, smul_zero]
    exact AddSubmonoid.zero_mem _

/-- Component projections preserve the `S`-span of the roots for every compatible scalar
commutative ring `S` (including `S = ℤ`, `S = ℚ`, and `S = R`). -/
theorem componentProj_mem_rootSpan (S : Type*) [CommRing S] [Module S M]
    [LinearMap.CompatibleSMul M M S R] (C : P.Component) {x : M} (hx : x ∈ P.rootSpan S) :
    (P.componentProj C x : M) ∈ P.rootSpan S := by
  let projS : M →ₗ[S] M := ((P.componentSpace C).subtype ∘ₗ P.componentProj C).restrictScalars S
  have hle : P.rootSpan S ≤ (P.rootSpan S).comap projS := by
    refine Submodule.span_le.mpr (Set.range_subset_iff.mpr fun j ↦ ?_)
    rw [SetLike.mem_coe, Submodule.mem_comap]
    by_cases hjC : P.componentOf j = C
    · simpa [projS, P.coe_componentProj_root_of_eq hjC] using (P.rootSpanMem S j).property
    · simp [projS, P.componentProj_root_of_ne hjC]
  exact hle hx

end IsRootSystem

end CommRing

/-! ### Cone, root-lattice, and positivity transport under `componentCycleDiag` -/

section Field

variable {ι K M N : Type*} [Field K] [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  (P : RootPairing ι K M N) [Finite ι] [P.IsRootSystem]

/-- **Cone preservation under `componentCycleDiag`.** For a base-preserving automorphism `σ`, a
return fixed vector lies in `posRootCone P b` if and only if its diagonal image does. -/
theorem mem_posRootCone_componentCycleDiag_iff {σ : P.Aut} {b : P.Base}
    (hσ : ∀ j ∈ b.support, σ.indexEquiv j ∈ b.support) (C : P.Component)
    (u : LinearMap.fixedSubmodule (P.componentReturnAut σ C).weightMap) :
    ((P.componentCycleDiag σ C u : LinearMap.fixedSubmodule σ.weightMap) : M) ∈ posRootCone P b ↔
      (u : M) ∈ posRootCone P b := by
  have hstep {x : M} (hx : x ∈ posRootCone P b) : σ.weightMap x ∈ posRootCone P b := by
    obtain ⟨f, rfl⟩ := (mem_posRootCone P b).mp hx
    rw [map_sum]
    refine AddSubmonoid.sum_mem _ fun j hj ↦ ?_
    rw [map_nsmul, Hom.root_weightMap_apply P P j σ.toHom]
    exact AddSubmonoid.nsmul_mem _ (P.root_mem_posRootCone_of_mem_support b (hσ j hj)) _
  have hpow (r : ℕ) {x : M} (hx : x ∈ posRootCone P b) :
      (σ.weightMap ^ r) x ∈ posRootCone P b := by
    induction r with
    | zero => simpa using hx
    | succ r ih =>
      rw [pow_succ', Module.End.mul_eq_comp, LinearMap.comp_apply]
      exact hstep ih
  refine ⟨fun hD ↦ ?_, fun hu ↦ ?_⟩
  · have hproj := P.componentProj_mem_posRootCone b C hD
    rwa [P.componentProj_componentCycleDiag] at hproj
  · rw [P.coe_componentCycleDiag_apply]
    exact AddSubmonoid.sum_mem _ fun r _ ↦ hpow r hu

/-- **Root-lattice preservation under `componentCycleDiag`.** For every compatible scalar
commutative ring `S` (in particular `S = ℤ`), a return fixed vector lies in `P.rootSpan S` if and
only if its diagonal image does. -/
theorem mem_rootSpan_componentCycleDiag_iff (S : Type*) [CommRing S] [Module S M]
    [LinearMap.CompatibleSMul M M S K] (σ : P.Aut) (C : P.Component)
    (u : LinearMap.fixedSubmodule (P.componentReturnAut σ C).weightMap) :
    ((P.componentCycleDiag σ C u : LinearMap.fixedSubmodule σ.weightMap) : M) ∈ P.rootSpan S ↔
      (u : M) ∈ P.rootSpan S := by
  have hstep {x : M} (hx : x ∈ P.rootSpan S) : σ.weightMap x ∈ P.rootSpan S := by
    have hle : P.rootSpan S ≤ (P.rootSpan S).comap (σ.weightMap.restrictScalars S) := by
      refine Submodule.span_le.mpr (Set.range_subset_iff.mpr fun j ↦ ?_)
      rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.restrictScalars_apply,
        Hom.root_weightMap_apply P P j σ.toHom]
      exact (P.rootSpanMem S _).property
    exact hle hx
  have hpow (r : ℕ) {x : M} (hx : x ∈ P.rootSpan S) : (σ.weightMap ^ r) x ∈ P.rootSpan S := by
    induction r with
    | zero => simpa using hx
    | succ r ih =>
      rw [pow_succ', Module.End.mul_eq_comp, LinearMap.comp_apply]
      exact hstep ih
  refine ⟨fun hD ↦ ?_, fun hu ↦ ?_⟩
  · have hproj := P.componentProj_mem_rootSpan S C hD
    rwa [P.componentProj_componentCycleDiag] at hproj
  · rw [P.coe_componentCycleDiag_apply]
    exact Submodule.sum_mem _ fun r _ ↦ hpow r hu

end Field

/-! ### Simple-orbit bases on the return fixed space and cycle fixed space -/

namespace Base

section SupportPerm

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} (b : P.Base)

private theorem pow_indexEquiv_mem_support {σ : P.Aut}
    (hb : ∀ i, i ∈ b.support ↔ σ.indexEquiv i ∈ b.support) :
    ∀ n {z : ι}, z ∈ b.support → (σ.indexEquiv ^ n) z ∈ b.support
  | 0, _, hz => hz
  | n + 1, _, hz => by
    rw [pow_succ', _root_.Equiv.Perm.mul_apply]
    exact (hb _).mp (pow_indexEquiv_mem_support hb n hz)

private theorem coe_supportEquiv_pow {σ : P.Aut}
    (hb : ∀ i, i ∈ b.support ↔ σ.indexEquiv i ∈ b.support) :
    ∀ n (j : b.support), (((σ.supportEquiv hb ^ n) j : b.support) : ι) = (σ.indexEquiv ^ n) (j : ι)
  | 0, _ => rfl
  | n + 1, j => by
    rw [pow_succ', pow_succ', _root_.Equiv.Perm.mul_apply, _root_.Equiv.Perm.mul_apply,
      σ.coe_supportEquiv_apply, coe_supportEquiv_pow hb n j]

/-- The permutation of the simple roots in `C` induced by the return automorphism `σ ^ c` when `σ`
permutes `b.support`. -/
noncomputable def componentReturnSupportPerm (σ : P.Aut)
    (hb : ∀ i, i ∈ b.support ↔ σ.indexEquiv i ∈ b.support) (C : P.Component) :
    _root_.Equiv.Perm {i : b.support // P.componentOf (i : ι) = C} where
  toFun i := ⟨(σ.supportEquiv hb ^ minimalPeriod σ.componentEquiv C) i.1, by
    rw [coe_supportEquiv_pow b hb, ← σ.indexEquiv_pow, ← (σ ^ _).componentEquiv_componentOf, i.2,
      P.componentEquiv_pow_minimalPeriod]⟩
  invFun i := ⟨(σ.supportEquiv hb ^ minimalPeriod σ.componentEquiv C).symm i.1, by
    set c := minimalPeriod σ.componentEquiv C
    have hj : (σ ^ c).indexEquiv (((σ.supportEquiv hb ^ c).symm i.1 : b.support) : ι) =
        (i.1 : ι) := by
      rw [σ.indexEquiv_pow, ← coe_supportEquiv_pow b hb c ((σ.supportEquiv hb ^ c).symm i.1),
        _root_.Equiv.apply_symm_apply]
    apply (σ ^ c).componentEquiv.injective
    rw [(σ ^ c).componentEquiv_componentOf, hj, i.2, P.componentEquiv_pow_minimalPeriod]⟩
  left_inv i := Subtype.ext (_root_.Equiv.symm_apply_apply _ _)
  right_inv i := Subtype.ext (_root_.Equiv.apply_symm_apply _ _)

@[simp]
theorem coe_componentReturnSupportPerm_apply (σ : P.Aut)
    (hb : ∀ i, i ∈ b.support ↔ σ.indexEquiv i ∈ b.support) (C : P.Component)
    (i : {i : b.support // P.componentOf (i : ι) = C}) :
    ((b.componentReturnSupportPerm σ hb C i).1 : ι) =
      (σ.indexEquiv ^ minimalPeriod σ.componentEquiv C) (i.1 : ι) :=
  coe_supportEquiv_pow b hb _ i.1

@[simp]
theorem coe_componentReturnSupportPerm_pow (σ : P.Aut)
    (hb : ∀ i, i ∈ b.support ↔ σ.indexEquiv i ∈ b.support) (C : P.Component) (k : ℕ)
    (i : {i : b.support // P.componentOf (i : ι) = C}) :
    (((b.componentReturnSupportPerm σ hb C ^ k) i).1 : ι) =
      ((σ.indexEquiv ^ minimalPeriod σ.componentEquiv C) ^ k) (i.1 : ι) := by
  induction k with
  | zero => rfl
  | succ k ih => simp [pow_succ', ih]

/-- The permutation of the simple roots in the `σ`-cycle of `C` induced by `σ` when `σ` permutes
`b.support`. -/
noncomputable def componentCycleSupportPerm (σ : P.Aut)
    (hb : ∀ i, i ∈ b.support ↔ σ.indexEquiv i ∈ b.support) (C : P.Component) :
    _root_.Equiv.Perm {i : b.support //
      _root_.Equiv.Perm.SameCycle σ.componentEquiv C (P.componentOf (i : ι))} where
  toFun i := ⟨σ.supportEquiv hb i.1, by
    rw [σ.coe_supportEquiv_apply, ← σ.componentEquiv_componentOf]
    exact _root_.Equiv.Perm.sameCycle_apply_right.mpr i.2⟩
  invFun i := ⟨(σ.supportEquiv hb).symm i.1, by
    rw [σ.coe_supportEquiv_symm_apply]
    have hcomp : P.componentOf (σ.indexEquiv.symm (i.1 : ι)) =
        σ.componentEquiv.symm (P.componentOf (i.1 : ι)) :=
      σ.componentEquiv.injective (by
        rw [_root_.Equiv.apply_symm_apply, σ.componentEquiv_componentOf,
          _root_.Equiv.apply_symm_apply])
    rw [hcomp]
    exact _root_.Equiv.Perm.sameCycle_symm_apply_right.mpr i.2⟩
  left_inv i := Subtype.ext (_root_.Equiv.symm_apply_apply _ _)
  right_inv i := Subtype.ext (_root_.Equiv.apply_symm_apply _ _)

@[simp]
theorem coe_componentCycleSupportPerm_apply (σ : P.Aut)
    (hb : ∀ i, i ∈ b.support ↔ σ.indexEquiv i ∈ b.support) (C : P.Component)
    (i : {i : b.support //
      _root_.Equiv.Perm.SameCycle σ.componentEquiv C (P.componentOf (i : ι))}) :
    ((b.componentCycleSupportPerm σ hb C i).1 : ι) = σ.indexEquiv (i.1 : ι) :=
  σ.coe_supportEquiv_apply hb i.1

@[simp]
theorem coe_componentCycleSupportPerm_pow (σ : P.Aut)
    (hb : ∀ i, i ∈ b.support ↔ σ.indexEquiv i ∈ b.support) (C : P.Component) (k : ℕ)
    (i : {i : b.support //
      _root_.Equiv.Perm.SameCycle σ.componentEquiv C (P.componentOf (i : ι))}) :
    (((b.componentCycleSupportPerm σ hb C ^ k) i).1 : ι) = (σ.indexEquiv ^ k) (i.1 : ι) := by
  induction k with
  | zero => rfl
  | succ k ih => simp [pow_succ', ih]

private theorem sameCycle_componentReturnSupportPerm_iff (σ : P.Aut)
    (hb : ∀ i, i ∈ b.support ↔ σ.indexEquiv i ∈ b.support) (C : P.Component)
    (i j : {i : b.support // P.componentOf (i : ι) = C}) :
    _root_.Equiv.Perm.SameCycle (b.componentReturnSupportPerm σ hb C) i j ↔
      _root_.Equiv.Perm.SameCycle (b.componentCycleSupportPerm σ hb C)
        ⟨i.1, by rw [i.2]⟩
        ⟨j.1, by rw [j.2]⟩ := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨k, rfl⟩ := h.exists_nat_pow_eq
    refine ⟨(minimalPeriod σ.componentEquiv C * k : ℕ), ?_⟩
    ext
    rw [zpow_natCast]
    dsimp only
    rw [b.coe_componentCycleSupportPerm_pow, b.coe_componentReturnSupportPerm_pow, ← pow_mul]
  · obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
    have hk_val : (σ.indexEquiv ^ k) (i.1 : ι) = (j.1 : ι) := by
      simpa using congrArg (fun x ↦ (x.1 : ι)) hk
    have hc_per : IsPeriodicPt σ.componentEquiv k C := by
      have hfix : (⇑σ.componentEquiv)^[k] C = C := by
        conv_lhs => rw [← i.2]
        rw [← _root_.Equiv.Perm.coe_pow, ← σ.componentEquiv_pow,
          (σ ^ k).componentEquiv_componentOf, σ.indexEquiv_pow, hk_val, j.2]
      exact hfix
    obtain ⟨q, rfl⟩ := hc_per.minimalPeriod_dvd
    refine ⟨(q : ℕ), ?_⟩
    ext
    rw [zpow_natCast, b.coe_componentReturnSupportPerm_pow, ← pow_mul, hk_val]

/-- **Bijection between simple-root `(σ ^ c)`-orbits in `C` and simple-root `σ`-orbits in the
component cycle of `C`.** -/
noncomputable def componentCycleSimpleOrbitEquiv (σ : P.Aut)
    (hb : ∀ i, i ∈ b.support ↔ σ.indexEquiv i ∈ b.support) (C : P.Component) :
    Quotient (_root_.Equiv.Perm.SameCycle.setoid (b.componentReturnSupportPerm σ hb C)) ≃
      Quotient (_root_.Equiv.Perm.SameCycle.setoid (b.componentCycleSupportPerm σ hb C)) := by
  let incl : {i : b.support // P.componentOf (i : ι) = C} →
      {i : b.support // _root_.Equiv.Perm.SameCycle σ.componentEquiv C (P.componentOf (i : ι))} :=
    fun i ↦ ⟨i.1, by rw [i.2]⟩
  have hsemi : Function.Semiconj (fun x ↦ P.componentOf (x.1 : ι))
      (b.componentCycleSupportPerm σ hb C) σ.componentEquiv := fun x ↦ by
    dsimp only
    rw [b.coe_componentCycleSupportPerm_apply, ← σ.componentEquiv_componentOf]
  refine _root_.Equiv.ofBijective
    (Quotient.lift (fun i ↦ ⟦incl i⟧) fun i j hij ↦
      Quotient.sound ((b.sameCycle_componentReturnSupportPerm_iff σ hb C i j).mp hij))
    ⟨fun o₁ o₂ h ↦ ?_, fun O ↦ ?_⟩
  · induction o₁ using Quotient.ind with | _ i => ?_
    induction o₂ using Quotient.ind with | _ j => ?_
    exact Quotient.sound
      ((b.sameCycle_componentReturnSupportPerm_iff σ hb C i j).mpr (Quotient.exact h))
  · induction O using Quotient.ind with | _ j => ?_
    obtain ⟨k, hk⟩ := j.2.symm
    let i₀ : {i : b.support // P.componentOf (i : ι) = C} :=
      ⟨((b.componentCycleSupportPerm σ hb C ^ k) j).1, (hsemi.perm_zpow_right k j).trans hk⟩
    exact ⟨⟦i₀⟧, Quotient.sound (_root_.Equiv.Perm.SameCycle.symm ⟨k, Subtype.ext rfl⟩)⟩

end SupportPerm

private noncomputable local instance fintypeSupportComponent
    {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} (b : P.Base) (C : P.Component) :
    Fintype {i : b.support // P.componentOf (i : ι) = C} :=
  Fintype.ofFinite _

private noncomputable local instance fintypeSupportComponentCycle
    {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} (b : P.Base) (σ : P.Aut) (C : P.Component) :
    Fintype {i : b.support //
      _root_.Equiv.Perm.SameCycle σ.componentEquiv C (P.componentOf (i : ι))} :=
  Fintype.ofFinite _

section CycleBasis

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsRootSystem] (b : P.Base)

/-- The simple roots of `b` lying in the component `C` form an `R`-basis of `P.componentSpace C`. -/
noncomputable def componentWeightBasis (C : P.Component) :
    Module.Basis {i : b.support // P.componentOf (i : ι) = C} R (P.componentSpace C) :=
  Module.Basis.ofEquivFun
    { toFun x i := b.toWeightBasis.repr (x : M) i.1
      map_add' x y := funext fun i ↦ by simp
      map_smul' r x := funext fun i ↦ by simp
      invFun f := ∑ i, f i • (⟨P.root (i.1 : ι),
        P.root_mem_componentSpace_of_mem_supp ((C.mem_supp_iff _).mpr i.2)⟩ : P.componentSpace C)
      left_inv x := Subtype.ext <| by
        classical
        simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower]
        conv_rhs => rw [← b.toWeightBasis.sum_repr (x : M)]
        simp only [b.toWeightBasis_apply]
        rw [← Finset.sum_subtype
          (Finset.univ.filter fun j : b.support ↦ P.componentOf (j : ι) = C)
          (fun _ ↦ by simp)
          (fun j : b.support ↦ b.toWeightBasis.repr (x : M) j • P.root (j : ι))]
        refine Finset.sum_subset (Finset.subset_univ _) fun j _ hj ↦ ?_
        have hj' : P.componentOf (j : ι) ≠ C := by simpa using hj
        rw [P.toWeightBasis_repr_eq_zero_of_mem_componentSpace b x.2 hj', zero_smul]
      right_inv f := funext fun i ↦ by
        classical
        simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower, map_sum, map_smul,
          Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
        rw [Finset.sum_eq_single i]
        · rw [← b.toWeightBasis_apply, Module.Basis.repr_self, Finsupp.single_eq_same, mul_one]
        · intro j _ hji
          have hne : j.1 ≠ i.1 := fun h ↦ hji (Subtype.ext h)
          rw [← b.toWeightBasis_apply, Module.Basis.repr_self, Finsupp.single_eq_of_ne' hne,
            mul_zero]
        · exact fun h ↦ absurd (Finset.mem_univ i) h }

@[simp]
theorem componentWeightBasis_repr_apply (C : P.Component) (x : P.componentSpace C)
    (i : {i : b.support // P.componentOf (i : ι) = C}) :
    (b.componentWeightBasis C).repr x i = b.toWeightBasis.repr (x : M) i.1 :=
  (rfl)

@[simp]
theorem coe_componentWeightBasis_apply (C : P.Component)
    (i : {i : b.support // P.componentOf (i : ι) = C}) :
    (b.componentWeightBasis C i : M) = P.root (i.1 : ι) := by
  classical
  rw [componentWeightBasis, Module.Basis.coe_ofEquivFun]
  dsimp only [LinearEquiv.coe_symm_mk]
  simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    rw [Pi.single_eq_of_ne hji, zero_smul]
  · exact fun h ↦ absurd (Finset.mem_univ i) h

/-- The simple roots of `b` lying in the `σ`-cycle of `C` form an `R`-basis of
`P.componentCycleSpace σ C`. -/
noncomputable def componentCycleWeightBasis (σ : P.Aut) (C : P.Component) :
    Module.Basis
      {i : b.support // _root_.Equiv.Perm.SameCycle σ.componentEquiv C (P.componentOf (i : ι))} R
      (P.componentCycleSpace σ C) :=
  Module.Basis.ofEquivFun
    { toFun x i := b.toWeightBasis.repr (x : M) i.1
      map_add' x y := funext fun i ↦ by simp
      map_smul' r x := funext fun i ↦ by simp
      invFun f := ∑ i, f i • ⟨P.root (i.1 : ι),
        P.componentSpace_le_componentCycleSpace i.2 (P.root_mem_componentSpace _)⟩
      left_inv x := Subtype.ext <| by
        classical
        simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower]
        conv_rhs => rw [← b.toWeightBasis.sum_repr (x : M)]
        simp only [b.toWeightBasis_apply]
        rw [← Finset.sum_subtype (Finset.univ.filter fun j : b.support ↦
          _root_.Equiv.Perm.SameCycle σ.componentEquiv C (P.componentOf (j : ι)))
          (fun _ ↦ by simp)
          (fun j : b.support ↦ b.toWeightBasis.repr (x : M) j • P.root (j : ι))]
        refine Finset.sum_subset (Finset.subset_univ _) fun j _ hj ↦ ?_
        have hj' : ¬_root_.Equiv.Perm.SameCycle σ.componentEquiv C (P.componentOf (j : ι)) := by
          simpa using hj
        rw [P.toWeightBasis_repr_eq_zero_of_mem_componentCycleSpace b x.2 hj', zero_smul]
      right_inv f := funext fun i ↦ by
        classical
        simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower, map_sum, map_smul,
          Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
        rw [Finset.sum_eq_single i]
        · rw [← b.toWeightBasis_apply, Module.Basis.repr_self, Finsupp.single_eq_same, mul_one]
        · intro j _ hji
          have hne : j.1 ≠ i.1 := fun h ↦ hji (Subtype.ext h)
          rw [← b.toWeightBasis_apply, Module.Basis.repr_self, Finsupp.single_eq_of_ne' hne,
            mul_zero]
        · exact fun h ↦ absurd (Finset.mem_univ i) h }

@[simp]
theorem componentCycleWeightBasis_repr_apply (σ : P.Aut) (C : P.Component)
    (x : P.componentCycleSpace σ C)
    (i : {i : b.support //
      _root_.Equiv.Perm.SameCycle σ.componentEquiv C (P.componentOf (i : ι))}) :
    (b.componentCycleWeightBasis σ C).repr x i = b.toWeightBasis.repr (x : M) i.1 :=
  (rfl)

@[simp]
theorem coe_componentCycleWeightBasis_apply (σ : P.Aut) (C : P.Component)
    (i : {i : b.support //
      _root_.Equiv.Perm.SameCycle σ.componentEquiv C (P.componentOf (i : ι))}) :
    (b.componentCycleWeightBasis σ C i : M) = P.root (i.1 : ι) := by
  classical
  rw [componentCycleWeightBasis, Module.Basis.coe_ofEquivFun]
  dsimp only [LinearEquiv.coe_symm_mk]
  simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    rw [Pi.single_eq_of_ne hji, zero_smul]
  · exact fun h ↦ absurd (Finset.mem_univ i) h

/-- Helper building the orbit-sum basis of `e.toLinearMap.fixedSubmodule` whenever a linear
automorphism `e : U ≃ₗ[R] U` permutes a finite basis `B : Module.Basis J R U` along `π`. -/
private noncomputable def basisPermFixedBasis {J U : Type*} [Fintype J] [AddCommGroup U]
    [Module R U] (B : Module.Basis J R U) (e : U ≃ₗ[R] U) (π : _root_.Equiv.Perm J)
    (he : ∀ j, e (B j) = B (π j)) :
    Module.Basis (Quotient (_root_.Equiv.Perm.SameCycle.setoid π)) R e.toLinearMap.fixedSubmodule :=
  have hint : B.equivFun.toLinearMap ∘ₗ e.symm.toLinearMap =
      (LinearEquiv.funCongrLeft R R π).toLinearMap ∘ₗ B.equivFun.toLinearMap :=
    B.ext fun k ↦ funext fun j ↦ by
      have hsymm : e.symm (B k) = B (π.symm k) :=
        e.injective (by rw [e.apply_symm_apply, he, π.apply_symm_apply])
      classical
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
        Module.Basis.equivFun_apply, hsymm, LinearEquiv.funCongrLeft_apply,
        LinearMap.funLeft_apply, Module.Basis.repr_self, Finsupp.single_apply]
      exact if_congr π.symm_apply_eq rfl rfl
  (_root_.Equiv.Perm.permutationFixedBasis (R := R) π).map
    ((B.equivFun.fixedSubmoduleCongr hint).symm.trans
      (LinearEquiv.ofEq _ _ (LinearEquiv.fixedSubmodule_symm_eq e)))

private theorem basisPermFixedBasis_repr {J U : Type*} [Fintype J] [AddCommGroup U] [Module R U]
    (B : Module.Basis J R U) (e : U ≃ₗ[R] U) (π : _root_.Equiv.Perm J)
    (he : ∀ j, e (B j) = B (π j)) (u : e.toLinearMap.fixedSubmodule) (j : J) :
    (basisPermFixedBasis B e π he).repr u ⟦j⟧ = B.repr u.1 j := by
  simp [basisPermFixedBasis]

private theorem coe_basisPermFixedBasis_apply {J U : Type*} [Fintype J]
    [AddCommGroup U] [Module R U] (B : Module.Basis J R U) (e : U ≃ₗ[R] U)
    (π : _root_.Equiv.Perm J) (he : ∀ j, e (B j) = B (π j))
    [DecidableEq (Quotient (_root_.Equiv.Perm.SameCycle.setoid π))]
    (o : Quotient (_root_.Equiv.Perm.SameCycle.setoid π)) :
    (basisPermFixedBasis B e π he o : U) =
      ∑ j ∈ Finset.univ.filter (fun j ↦ (⟦j⟧ : Quotient _) = o), B j := by
  classical
  apply B.equivFun.injective
  ext j
  simp only [basisPermFixedBasis, Module.Basis.map_apply, LinearEquiv.trans_apply,
    LinearEquiv.coe_ofEq_apply, LinearEquiv.fixedSubmoduleCongr_symm_apply,
    LinearEquiv.apply_symm_apply, _root_.Equiv.Perm.permutationFixedBasis_apply,
    map_sum, Finset.sum_apply, Module.Basis.equivFun_apply, Module.Basis.repr_self]
  by_cases hj : (⟦j⟧ : Quotient _) = o
  · simp only [hj, ↓reduceIte]
    rw [Finset.sum_eq_single j]
    · exact Finsupp.single_eq_same.symm
    · intro c _ hcj
      exact Finsupp.single_eq_of_ne' hcj
    · intro hnot
      exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩) hnot
  · simp only [hj, ↓reduceIte]
    refine (Finset.sum_eq_zero fun c hc ↦ ?_).symm
    have hcj : c ≠ j := fun h ↦ hj (h ▸ (Finset.mem_filter.mp hc).2)
    exact Finsupp.single_eq_of_ne' hcj

/-- **The simple-orbit `R`-basis of the cycle fixed space**
`P.componentCycleFixedSubmodule σ C`. -/
noncomputable def componentCycleSimpleOrbitBasis (σ : P.Aut)
    (hb : ∀ i, i ∈ b.support ↔ σ.indexEquiv i ∈ b.support) (C : P.Component) :
    Module.Basis
      (Quotient (_root_.Equiv.Perm.SameCycle.setoid (b.componentCycleSupportPerm σ hb C))) R
      (P.componentCycleFixedSubmodule σ C) :=
  let eCyc : P.componentCycleSpace σ C ≃ₗ[R] P.componentCycleSpace σ C :=
    σ.weightEquiv.ofSubmodules _ _
      (by rw [LinearMap.ext σ.weightEquiv_apply]; exact P.map_componentCycleSpace σ C)
  let eFix : eCyc.toLinearMap.fixedSubmodule ≃ₗ[R] P.componentCycleFixedSubmodule σ C :=
    { toFun z := ⟨⟨(z.1 : M), LinearMap.mem_fixedSubmodule_iff.mpr
        (congrArg Subtype.val (LinearMap.mem_fixedSubmodule_iff.mp z.2))⟩,
          P.mem_componentCycleFixedSubmodule.mpr z.1.2⟩
      invFun y := ⟨⟨(y.1 : M), P.mem_componentCycleFixedSubmodule.mp y.2⟩,
        LinearMap.mem_fixedSubmodule_iff.mpr
          (Subtype.ext (LinearMap.mem_fixedSubmodule_iff.mp y.1.2))⟩
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  (basisPermFixedBasis (b.componentCycleWeightBasis σ C) eCyc
    (b.componentCycleSupportPerm σ hb C) fun i ↦ Subtype.ext <| by
      dsimp only [eCyc]
      rw [LinearEquiv.ofSubmodules_apply, Equiv.weightEquiv_apply,
        b.coe_componentCycleWeightBasis_apply, b.coe_componentCycleWeightBasis_apply,
        b.coe_componentCycleSupportPerm_apply, Hom.root_weightMap_apply P P _ σ.toHom]).map eFix

@[simp]
theorem componentCycleSimpleOrbitBasis_repr (σ : P.Aut)
    (hb : ∀ i, i ∈ b.support ↔ σ.indexEquiv i ∈ b.support) (C : P.Component)
    (y : P.componentCycleFixedSubmodule σ C)
    (i : {i : b.support //
      _root_.Equiv.Perm.SameCycle σ.componentEquiv C (P.componentOf (i : ι))}) :
    (b.componentCycleSimpleOrbitBasis σ hb C).repr y ⟦i⟧ =
      b.toWeightBasis.repr (y.1 : M) i.1 := by
  simpa [componentCycleSimpleOrbitBasis] using
    basisPermFixedBasis_repr (b.componentCycleWeightBasis σ C) _ _ _ _ i

/-- Each vector of `componentCycleSimpleOrbitBasis` is the ambient `σ`-orbit sum of its simple-root
representative. -/
theorem coe_componentCycleSimpleOrbitBasis_apply [Finite ι] (σ : P.Aut)
    (hb : ∀ i, i ∈ b.support ↔ σ.indexEquiv i ∈ b.support) (C : P.Component)
    (O : Quotient (_root_.Equiv.Perm.SameCycle.setoid (b.componentCycleSupportPerm σ hb C))) :
    ((b.componentCycleSimpleOrbitBasis σ hb C O : LinearMap.fixedSubmodule σ.weightMap) : M) =
      P.orbitSum σ (O.out.1 : ι) := by
  classical
  have hcoe : ((b.componentCycleSimpleOrbitBasis σ hb C O :
      LinearMap.fixedSubmodule σ.weightMap) : M) =
      ∑ j ∈ Finset.univ.filter (fun j ↦ (⟦j⟧ : Quotient _) = O), P.root (j.1 : ι) := by
    simp only [componentCycleSimpleOrbitBasis, Module.Basis.map_apply, LinearEquiv.coe_mk,
      LinearMap.coe_mk, AddHom.coe_mk, coe_basisPermFixedBasis_apply, Submodule.coe_sum,
      b.coe_componentCycleWeightBasis_apply]
  rw [hcoe, P.orbitSum_def]
  refine Finset.sum_nbij'
    (fun j ↦ (j.1 : ι))
    (fun k ↦ if hk : k ∈ b.support then
      if hC : _root_.Equiv.Perm.SameCycle σ.componentEquiv C (P.componentOf k) then
        ⟨⟨k, hk⟩, hC⟩ else O.out else O.out)
    (fun j hj ↦ ?_) (fun k hk ↦ ?_)
    (fun j _ ↦ by simp [j.1.2, j.2]) (fun k hk ↦ ?_) (fun _ _ ↦ rfl)
  · have hsc : (b.componentCycleSupportPerm σ hb C).SameCycle O.out j :=
      Quotient.exact ((Quotient.out_eq O).trans (Finset.mem_filter.mp hj).2.symm)
    obtain ⟨r, rfl⟩ := hsc.exists_nat_pow_eq
    exact P.mem_orbitIndices_iff_exists_pow.mpr
      ⟨r, (b.coe_componentCycleSupportPerm_pow σ hb C r O.out).symm⟩
  · obtain ⟨r, rfl⟩ := P.mem_orbitIndices_iff_exists_pow.mp hk
    have hmem_b := pow_indexEquiv_mem_support b hb r O.out.1.2
    have hC : _root_.Equiv.Perm.SameCycle σ.componentEquiv C
        (P.componentOf ((σ.indexEquiv ^ r) (O.out.1 : ι))) := by
      rw [← σ.indexEquiv_pow, ← (σ ^ r).componentEquiv_componentOf, σ.componentEquiv_pow]
      exact O.out.2.trans ⟨(r : ℤ), by simp⟩
    simp only [hmem_b, hC, ↓reduceDIte]
    have hsc : (b.componentCycleSupportPerm σ hb C).SameCycle O.out ⟨⟨_, hmem_b⟩, hC⟩ := by
      refine ⟨(r : ℤ), Subtype.ext <| Subtype.ext ?_⟩
      rw [zpow_natCast, b.coe_componentCycleSupportPerm_pow]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Quotient.sound hsc.symm).trans
      (Quotient.out_eq O)⟩
  · obtain ⟨r, rfl⟩ := P.mem_orbitIndices_iff_exists_pow.mp hk
    have hmem_b := pow_indexEquiv_mem_support b hb r O.out.1.2
    have hC : _root_.Equiv.Perm.SameCycle σ.componentEquiv C
        (P.componentOf ((σ.indexEquiv ^ r) (O.out.1 : ι))) := by
      rw [← σ.indexEquiv_pow, ← (σ ^ r).componentEquiv_componentOf, σ.componentEquiv_pow]
      exact O.out.2.trans ⟨(r : ℤ), by simp⟩
    simp only [hmem_b, hC, ↓reduceDIte]

end CycleBasis

section ReturnSimpleOrbitBasis

variable {ι K M N : Type*} [Field K] [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  {P : RootPairing ι K M N} [Finite ι] [P.IsRootSystem] (b : P.Base)

/-- **The simple-orbit `K`-basis of the return fixed space**
`LinearMap.fixedSubmodule (P.componentReturnAut σ C).weightMap`. -/
noncomputable def componentReturnSimpleOrbitBasis (σ : P.Aut)
    (hb : ∀ i, i ∈ b.support ↔ σ.indexEquiv i ∈ b.support) (C : P.Component) :
    Module.Basis
      (Quotient (_root_.Equiv.Perm.SameCycle.setoid (b.componentReturnSupportPerm σ hb C))) K
      (LinearMap.fixedSubmodule (P.componentReturnAut σ C).weightMap) :=
  (basisPermFixedBasis (b.componentWeightBasis C) (P.componentReturnAut σ C).weightEquiv
    (b.componentReturnSupportPerm σ hb C) fun i ↦ Subtype.ext <| by
      rw [P.coe_componentReturnAut_weightEquiv, b.coe_componentWeightBasis_apply,
        b.coe_componentWeightBasis_apply, b.coe_componentReturnSupportPerm_apply,
        ← σ.weightMap_pow, ← σ.indexEquiv_pow, Hom.root_weightMap_apply P P _ (σ ^ _).toHom]).map
    (LinearEquiv.ofEq _ _
      (congrArg LinearMap.fixedSubmodule
        (LinearMap.ext (P.componentReturnAut σ C).weightEquiv_apply)))

@[simp]
theorem componentReturnSimpleOrbitBasis_repr (σ : P.Aut)
    (hb : ∀ i, i ∈ b.support ↔ σ.indexEquiv i ∈ b.support) (C : P.Component)
    (u : LinearMap.fixedSubmodule (P.componentReturnAut σ C).weightMap)
    (i : {i : b.support // P.componentOf (i : ι) = C}) :
    (b.componentReturnSimpleOrbitBasis σ hb C).repr u ⟦i⟧ =
      b.toWeightBasis.repr (u : M) i.1 := by
  rw [componentReturnSimpleOrbitBasis, Module.Basis.map_repr, LinearEquiv.trans_apply,
    basisPermFixedBasis_repr]
  rfl

/-- Each vector of `componentReturnSimpleOrbitBasis` is the return orbit sum of its simple-root
representative in `P.componentPairing C`. -/
theorem coe_componentReturnSimpleOrbitBasis_apply (σ : P.Aut)
    (hb : ∀ i, i ∈ b.support ↔ σ.indexEquiv i ∈ b.support) (C : P.Component)
    (o : Quotient (_root_.Equiv.Perm.SameCycle.setoid (b.componentReturnSupportPerm σ hb C))) :
    ((b.componentReturnSimpleOrbitBasis σ hb C o :
        LinearMap.fixedSubmodule (P.componentReturnAut σ C).weightMap) : P.componentSpace C) =
      (P.componentPairing C).orbitSum (P.componentReturnAut σ C)
        ⟨o.out.1, (C.mem_supp_iff _).mpr o.out.2⟩ := by
  classical
  have hcoe : ((b.componentReturnSimpleOrbitBasis σ hb C o :
      LinearMap.fixedSubmodule (P.componentReturnAut σ C).weightMap) : P.componentSpace C) =
      ∑ j ∈ Finset.univ.filter (fun j ↦ (⟦j⟧ : Quotient _) = o), b.componentWeightBasis C j := by
    rw [componentReturnSimpleOrbitBasis, Module.Basis.map_apply, LinearEquiv.coe_ofEq_apply,
      coe_basisPermFixedBasis_apply]
  rw [hcoe]
  apply Subtype.ext
  simp only [Submodule.coe_sum, b.coe_componentWeightBasis_apply,
    (P.componentPairing C).orbitSum_def, P.coe_componentPairing_root]
  refine Finset.sum_nbij'
    (fun j ↦ (⟨j.1, (C.mem_supp_iff _).mpr j.2⟩ : C.supp))
    (fun k ↦ if hk : (k : ι) ∈ b.support then ⟨⟨k, hk⟩, (C.mem_supp_iff _).mp k.2⟩ else o.out)
    (fun j hj ↦ ?_) (fun k hk ↦ ?_)
    (fun j _ ↦ by simp) (fun k hk ↦ ?_) (fun _ _ ↦ rfl)
  · have hsc : (b.componentReturnSupportPerm σ hb C).SameCycle o.out j :=
      Quotient.exact ((Quotient.out_eq o).trans (Finset.mem_filter.mp hj).2.symm)
    obtain ⟨r, rfl⟩ := hsc.exists_nat_pow_eq
    refine (P.componentPairing C).mem_orbitIndices_iff_exists_pow.mpr ⟨r, Subtype.ext ?_⟩
    rw [P.coe_componentReturnAut_indexEquiv_pow, b.coe_componentReturnSupportPerm_pow]
  · obtain ⟨r, rfl⟩ := (P.componentPairing C).mem_orbitIndices_iff_exists_pow.mp hk
    have hmem_b : (((P.componentReturnAut σ C).indexEquiv ^ r)
        ⟨o.out.1, (C.mem_supp_iff _).mpr o.out.2⟩ : ι) ∈ b.support := by
      rw [P.coe_componentReturnAut_indexEquiv_pow, ← pow_mul]
      exact pow_indexEquiv_mem_support b hb _ o.out.1.2
    simp only [hmem_b, ↓reduceDIte]
    have hsc : (b.componentReturnSupportPerm σ hb C).SameCycle o.out
        ⟨⟨_, hmem_b⟩, (C.mem_supp_iff _).mp (((P.componentReturnAut σ C).indexEquiv ^ r)
          ⟨o.out.1, (C.mem_supp_iff _).mpr o.out.2⟩).2⟩ := by
      refine ⟨(r : ℤ), Subtype.ext <| Subtype.ext ?_⟩
      dsimp only
      rw [zpow_natCast, b.coe_componentReturnSupportPerm_pow,
        P.coe_componentReturnAut_indexEquiv_pow]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Quotient.sound hsc.symm).trans
      (Quotient.out_eq o)⟩
  · obtain ⟨r, rfl⟩ := (P.componentPairing C).mem_orbitIndices_iff_exists_pow.mp hk
    have hmem_b : (((P.componentReturnAut σ C).indexEquiv ^ r)
        ⟨o.out.1, (C.mem_supp_iff _).mpr o.out.2⟩ : ι) ∈ b.support := by
      rw [P.coe_componentReturnAut_indexEquiv_pow, ← pow_mul]
      exact pow_indexEquiv_mem_support b hb _ o.out.1.2
    simp only [hmem_b, ↓reduceDIte, Subtype.coe_eta]

/-- **Diagonal transport carries the return simple-orbit basis onto the cycle simple-orbit
basis.** -/
@[simp]
theorem componentCycleDiag_componentReturnSimpleOrbitBasis (σ : P.Aut)
    (hb : ∀ i, i ∈ b.support ↔ σ.indexEquiv i ∈ b.support) (C : P.Component)
    (o : Quotient (_root_.Equiv.Perm.SameCycle.setoid (b.componentReturnSupportPerm σ hb C))) :
    P.componentCycleDiag σ C (b.componentReturnSimpleOrbitBasis σ hb C o) =
      b.componentCycleSimpleOrbitBasis σ hb C (b.componentCycleSimpleOrbitEquiv σ hb C o) := by
  apply Subtype.ext
  apply Subtype.ext
  have hret : b.componentReturnSimpleOrbitBasis σ hb C o =
      P.componentReturnOrbitSumFixed σ C ⟨o.out.1, (C.mem_supp_iff _).mpr o.out.2⟩ :=
    Subtype.ext
      ((b.coe_componentReturnSimpleOrbitBasis_apply σ hb C o).trans
        (P.coe_componentReturnOrbitSumFixed σ C _).symm)
  rw [hret, P.coe_componentCycleDiag_orbitSum, b.coe_componentCycleSimpleOrbitBasis_apply]
  have heq : b.componentCycleSimpleOrbitEquiv σ hb C o =
      ⟦⟨o.out.1, by rw [o.out.2]⟩⟧ := by
    conv_lhs => rw [← Quotient.out_eq o]
    rfl
  have hsc : _root_.Equiv.Perm.SameCycle (b.componentCycleSupportPerm σ hb C)
      (b.componentCycleSimpleOrbitEquiv σ hb C o).out
      ⟨o.out.1, by rw [o.out.2]⟩ :=
    Quotient.exact ((Quotient.out_eq _).trans heq)
  obtain ⟨k, hk⟩ := hsc.exists_nat_pow_eq
  have hk' : (σ.indexEquiv ^ k) ((b.componentCycleSimpleOrbitEquiv σ hb C o).out.1 : ι) =
      (o.out.1 : ι) := by
    simpa using congrArg (fun x ↦ (x.1 : ι)) hk
  dsimp only
  exact P.orbitSum_eq_of_mem (P.mem_orbitIndices_iff_exists_pow.mpr ⟨k, hk'⟩)

/-- **Simple-orbit coordinates are preserved unchanged by `componentCycleDiag`.** -/
@[simp]
theorem componentCycleSimpleOrbitBasis_repr_componentCycleDiag (σ : P.Aut)
    (hb : ∀ i, i ∈ b.support ↔ σ.indexEquiv i ∈ b.support) (C : P.Component)
    (u : LinearMap.fixedSubmodule (P.componentReturnAut σ C).weightMap)
    (o : Quotient (_root_.Equiv.Perm.SameCycle.setoid (b.componentReturnSupportPerm σ hb C))) :
    (b.componentCycleSimpleOrbitBasis σ hb C).repr (P.componentCycleDiag σ C u)
        (b.componentCycleSimpleOrbitEquiv σ hb C o) =
      (b.componentReturnSimpleOrbitBasis σ hb C).repr u o := by
  have := Fintype.ofFinite
    (Quotient (_root_.Equiv.Perm.SameCycle.setoid (b.componentReturnSupportPerm σ hb C)))
  conv_lhs => rw [← (b.componentReturnSimpleOrbitBasis σ hb C).sum_repr u]
  simp only [map_sum, map_smul, componentCycleDiag_componentReturnSimpleOrbitBasis,
    Module.Basis.repr_self, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single o]
  · simp
  · intro o' _ ho'
    have hne : b.componentCycleSimpleOrbitEquiv σ hb C o ≠
        b.componentCycleSimpleOrbitEquiv σ hb C o' :=
      (b.componentCycleSimpleOrbitEquiv σ hb C).injective.ne ho'.symm
    simp [Finsupp.single_eq_of_ne hne]
  · exact fun h ↦ absurd (Finset.mem_univ o) h

/-- A return fixed vector lies in `posRootCone P b` if and only if all of its coordinates in
`b.componentReturnSimpleOrbitBasis σ hb C` come from `ℕ`. -/
theorem mem_posRootCone_iff_forall_componentReturnSimpleOrbitBasis_repr (σ : P.Aut)
    (hb : ∀ i, i ∈ b.support ↔ σ.indexEquiv i ∈ b.support) (C : P.Component)
    (u : LinearMap.fixedSubmodule (P.componentReturnAut σ C).weightMap) :
    (u : M) ∈ posRootCone P b ↔
      ∀ o, ∃ n : ℕ, (b.componentReturnSimpleOrbitBasis σ hb C).repr u o = (n : K) := by
  have := Fintype.ofFinite
    (Quotient (_root_.Equiv.Perm.SameCycle.setoid (b.componentReturnSupportPerm σ hb C)))
  refine ⟨fun hu o ↦ ?_, fun h ↦ ?_⟩
  · classical
    obtain ⟨f, hf⟩ := (mem_posRootCone P b).mp hu
    refine ⟨f o.out.1, ?_⟩
    have hrepr : (b.componentReturnSimpleOrbitBasis σ hb C).repr u o =
        b.toWeightBasis.repr (u : M) o.out.1 := by
      conv_lhs => rw [← Quotient.out_eq o]
      exact b.componentReturnSimpleOrbitBasis_repr σ hb C u o.out
    rw [hrepr, hf, ← Finset.sum_coe_sort b.support]
    simp only [← Nat.cast_smul_eq_nsmul K, ← b.toWeightBasis_apply, map_sum, map_smul,
      Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul, Module.Basis.repr_self]
    rw [Finset.sum_eq_single o.out.1]
    · simp
    · intro j _ hj
      rw [Finsupp.single_eq_of_ne' hj, mul_zero]
    · exact fun hnot ↦ absurd (Finset.mem_univ _) hnot
  · choose n hn using h
    have hsum : u = ∑ o, n o • b.componentReturnSimpleOrbitBasis σ hb C o := by
      conv_lhs => rw [← (b.componentReturnSimpleOrbitBasis σ hb C).sum_repr u]
      exact Finset.sum_congr rfl fun o _ ↦ by rw [hn o, Nat.cast_smul_eq_nsmul]
    have hcoe : (u : M) =
        ∑ o, n o • ((b.componentReturnSimpleOrbitBasis σ hb C o :
          LinearMap.fixedSubmodule (P.componentReturnAut σ C).weightMap) : M) := by
      rw [hsum]
      simp
    rw [hcoe]
    refine AddSubmonoid.sum_mem _ fun o _ ↦ AddSubmonoid.nsmul_mem _ ?_ _
    have hvec : ((b.componentReturnSimpleOrbitBasis σ hb C o :
        LinearMap.fixedSubmodule (P.componentReturnAut σ C).weightMap) : M) =
        ((P.componentPairing C).orbitSum (P.componentReturnAut σ C)
          ⟨o.out.1, (C.mem_supp_iff _).mpr o.out.2⟩ : M) :=
      congrArg Subtype.val (b.coe_componentReturnSimpleOrbitBasis_apply σ hb C o)
    rw [hvec, (P.componentPairing C).orbitSum_def, Submodule.coe_sum]
    refine AddSubmonoid.sum_mem _ fun k hk ↦ ?_
    obtain ⟨r, rfl⟩ := (P.componentPairing C).mem_orbitIndices_iff_exists_pow.mp hk
    rw [P.coe_componentPairing_root, P.coe_componentReturnAut_indexEquiv_pow, ← pow_mul]
    exact P.root_mem_posRootCone_of_mem_support b (pow_indexEquiv_mem_support b hb _ o.out.1.2)

end ReturnSimpleOrbitBasis

end Base

end RootPairing
