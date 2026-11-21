/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.FixedSubmodule.Permutation
public import TauCeti.LinearAlgebra.RootSystem.Component.Cycle.Basic
import TauCeti.GroupTheory.Perm.Basic
import TauCeti.GroupTheory.Perm.Cycle.Enumeration
import TauCeti.LinearAlgebra.RootSystem.HomInvariance

/-!
# Bases, simple-orbit coordinates, and positive cones on component cycles

When an automorphism `σ` of a root system `P` preserves a base `b`, `P.componentCycleDiag σ C`
transports simple-root coordinates, orbit-sum bases (`Base.componentWeightBasis`,
`Base.componentCycleWeightBasis`, `Base.componentReturnSimpleOrbitBasis`,
`Base.componentCycleSimpleOrbitBasis`, `Base.componentCycleSimpleOrbitEquiv`), the positive root
cone (`componentProj_mem_posRootCone`, `mem_posRootCone_componentCycleDiag_iff`,
`orbitSum_mem_posRootCone_iff_isPos`,
`Base.mem_posRootCone_iff_forall_componentReturnSimpleOrbitBasis_repr`), and the root lattice
(`componentProj_mem_rootSpan`, `mem_rootSpan_componentCycleDiag_iff`) without distortion.

## References

* J. R. Stembridge, *Folding by automorphisms* (2008); N. Bourbaki, *Lie Groups and Lie Algebras*,
  Ch. VI §1, no. 7.
-/

public section

open Finset Function TauCeti
open _root_.Equiv (Perm)
open _root_.Equiv.Perm (SameCycle)

namespace RootPairing

/-! ### Simple-root coordinates and cone / root-span projections -/

section CommRing

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N)

private theorem root_mem_posRootCone_of_mem_support (b : P.Base) {j : ι} (hj : j ∈ b.support) :
    P.root j ∈ posRootCone P b := by
  classical
  exact (mem_posRootCone P b).mpr ⟨fun k ↦ if k = j then 1 else 0, by simp [hj]⟩

/-- In char. zero, for a base-preserving `σ`, `P.orbitSum σ i ∈ posRootCone P b ↔ b.IsPos i`. -/
theorem orbitSum_mem_posRootCone_iff_isPos [Finite ι] [CharZero R] {σ : P.Aut} {b : P.Base}
    (hσ : ∀ j ∈ b.support, σ.indexEquiv j ∈ b.support) (i : ι) :
    P.orbitSum σ i ∈ posRootCone P b ↔ b.IsPos i := by
  refine ⟨fun hcone ↦ ?_, P.orbitSum_mem_posRootCone hσ⟩
  by_contra hni
  have hneg : b.IsPos (P.reflectionPerm i i) :=
    (isPos_reflectionPerm_self_iff_mem_negRoots P b i).mpr ((mem_negRoots P b i).mpr hni)
  have hneg_cone : -P.orbitSum σ i ∈ posRootCone P b := by
    rw [← P.orbitSum_reflectionPerm_self]; exact P.orbitSum_mem_posRootCone hσ hneg
  exact P.orbitSum_ne_zero hσ i
    ((isPointed_posRootCone P b).eq_zero_of_mem_of_neg_mem hcone hneg_cone)

section IsRootSystem

variable [P.IsRootSystem]

private theorem coe_componentProj_root_of_eq {C : P.Component} {j : ι}
    (hj : P.componentOf j = C) : (P.componentProj C (P.root j) : M) = P.root j := by
  subst hj; exact congrArg Subtype.val (P.componentProj_root_self j)

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
    · rw [P.coe_componentProj_root_of_eq hi, ← b.toWeightBasis_apply]; simp [hi]
    · rw [P.componentProj_root_of_ne hi]; simp [hi]
  · intro j _ hji
    by_cases hj : P.componentOf (j : ι) = C
    · rw [P.coe_componentProj_root_of_eq hj, ← b.toWeightBasis_apply]
      simp [Finsupp.single_eq_of_ne (Ne.symm hji)]
    · rw [P.componentProj_root_of_ne hj]; simp
  · simp

theorem toWeightBasis_repr_componentProj_of_eq (b : P.Base) {C : P.Component} {i : b.support}
    (hi : P.componentOf (i : ι) = C) (x : M) :
    b.toWeightBasis.repr (P.componentProj C x : M) i = b.toWeightBasis.repr x i := by
  rw [P.toWeightBasis_repr_componentProj_aux]; simp [hi]

theorem toWeightBasis_repr_componentProj_of_ne (b : P.Base) {C : P.Component} {i : b.support}
    (hi : P.componentOf (i : ι) ≠ C) (x : M) :
    b.toWeightBasis.repr (P.componentProj C x : M) i = 0 := by
  rw [P.toWeightBasis_repr_componentProj_aux]; simp [hi]

variable {P} in
/-- A vector in `P.componentSpace C` has zero coordinates along simple roots outside `C`. -/
theorem toWeightBasis_repr_eq_zero_of_mem_componentSpace (b : P.Base) {C : P.Component} {x : M}
    (hx : x ∈ P.componentSpace C) {i : b.support} (hi : P.componentOf (i : ι) ≠ C) :
    b.toWeightBasis.repr x i = 0 := by
  have hproj : (P.componentProj C x : M) = x :=
    congrArg Subtype.val (P.componentProj_apply_of_mem hx)
  rw [← hproj, P.toWeightBasis_repr_componentProj_of_ne b hi]

variable {P} in
/-- A vector in `P.componentCycleSpace σ C` vanishes on simple roots outside the cycle of `C`. -/
theorem toWeightBasis_repr_eq_zero_of_mem_componentCycleSpace (b : P.Base) {σ : P.Aut}
    {C : P.Component} {x : M} (hx : x ∈ P.componentCycleSpace σ C) {i : b.support}
    (hi : ¬SameCycle σ.componentEquiv C (P.componentOf (i : ι))) :
    b.toWeightBasis.repr x i = 0 := by
  rw [← P.toWeightBasis_repr_componentProj_of_eq b rfl x,
    P.componentProj_eq_zero_of_not_sameCycle hx hi, Submodule.coe_zero, map_zero,
    Finsupp.zero_apply]

/-- Component projections preserve the positive root cone of any base. -/
theorem componentProj_mem_posRootCone (b : P.Base) (C : P.Component) {x : M}
    (hx : x ∈ posRootCone P b) : (P.componentProj C x : M) ∈ posRootCone P b := by
  obtain ⟨f, rfl⟩ := (mem_posRootCone P b).mp hx
  rw [map_sum, Submodule.coe_sum]
  refine AddSubmonoid.sum_mem _ fun j hj ↦ ?_
  rw [map_nsmul, Submodule.coe_smul_of_tower]
  by_cases hjC : P.componentOf j = C
  · rw [P.coe_componentProj_root_of_eq hjC]
    exact AddSubmonoid.nsmul_mem _ (P.root_mem_posRootCone_of_mem_support b hj) _
  · simp [P.componentProj_root_of_ne hjC]

/-- Component projections preserve `P.rootSpan S` for every compatible scalar ring `S`. -/
theorem componentProj_mem_rootSpan (S : Type*) [CommRing S] [Module S M]
    [LinearMap.CompatibleSMul M M S R] (C : P.Component) {x : M} (hx : x ∈ P.rootSpan S) :
    (P.componentProj C x : M) ∈ P.rootSpan S := by
  let projS : M →ₗ[S] M := ((P.componentSpace C).subtype ∘ₗ P.componentProj C).restrictScalars S
  refine (Submodule.span_le.mpr (Set.range_subset_iff.mpr fun j ↦ ?_) :
      P.rootSpan S ≤ (P.rootSpan S).comap projS) hx
  rw [SetLike.mem_coe, Submodule.mem_comap]
  by_cases hjC : P.componentOf j = C
  · simpa [projS, P.coe_componentProj_root_of_eq hjC] using (P.rootSpanMem S j).property
  · simp [projS, P.componentProj_root_of_ne hjC]

end IsRootSystem

end CommRing

/-! ### Cone, root-lattice, and positivity transport under `componentCycleDiag` -/

section Field

variable {ι K M N : Type*} [Field K] [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  (P : RootPairing ι K M N) [Finite ι] [P.IsRootSystem]

private theorem mem_addSubmonoid_componentCycleDiag_iff (A : AddSubmonoid M) {σ : P.Aut}
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

/-- **Cone preservation under `componentCycleDiag`** for a base-preserving automorphism `σ`. -/
theorem mem_posRootCone_componentCycleDiag_iff {σ : P.Aut} {b : P.Base}
    (hσ : ∀ j ∈ b.support, σ.indexEquiv j ∈ b.support) (C : P.Component)
    (u : LinearMap.fixedSubmodule (P.componentReturnAut σ C).weightMap) :
    ((P.componentCycleDiag σ C u : LinearMap.fixedSubmodule σ.weightMap) : M) ∈ posRootCone P b ↔
      (u : M) ∈ posRootCone P b :=
  P.mem_addSubmonoid_componentCycleDiag_iff (posRootCone P b)
    (fun {x} hx ↦ by
      obtain ⟨f, rfl⟩ := (mem_posRootCone P b).mp hx
      rw [map_sum]
      refine AddSubmonoid.sum_mem _ fun j hj ↦ ?_
      rw [map_nsmul, Hom.root_weightMap_apply P P j σ.toHom]
      exact AddSubmonoid.nsmul_mem _ (P.root_mem_posRootCone_of_mem_support b (hσ j hj)) _)
    C (fun hx ↦ P.componentProj_mem_posRootCone b C hx) u

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

end Field

/-! ### Simple-orbit bases on the return fixed space and cycle fixed space -/

namespace Base

section SupportPerm

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} (b : P.Base)

private theorem coe_supportEquiv_pow {σ : P.Aut}
    (hb : ∀ i, i ∈ b.support ↔ σ.indexEquiv i ∈ b.support) :
    ∀ n (j : b.support), (((σ.supportEquiv hb ^ n) j : b.support) : ι) = (σ.indexEquiv ^ n) (j : ι)
  | 0, _ => rfl
  | n + 1, j => by
    rw [pow_succ', pow_succ', Perm.mul_apply, Perm.mul_apply, σ.coe_supportEquiv_apply,
      coe_supportEquiv_pow hb n j]

variable (σ : P.Aut) (hb : ∀ i, i ∈ b.support ↔ σ.indexEquiv i ∈ b.support) (C : P.Component)

/-- The permutation of simple roots in `C` induced by the return iterate `σ ^ c`. -/
noncomputable def componentReturnSupportPerm :
    Perm {i : b.support // P.componentOf (i : ι) = C} where
  toFun i := ⟨(σ.supportEquiv hb ^ minimalPeriod σ.componentEquiv C) i.1, by
    rw [coe_supportEquiv_pow b hb, ← σ.indexEquiv_pow, ← (σ ^ _).componentEquiv_componentOf, i.2,
      P.componentEquiv_pow_minimalPeriod]⟩
  invFun i := ⟨(σ.supportEquiv hb ^ minimalPeriod σ.componentEquiv C).symm i.1, by
    set c := minimalPeriod σ.componentEquiv C
    apply (σ ^ c).componentEquiv.injective
    rw [(σ ^ c).componentEquiv_componentOf, σ.indexEquiv_pow, ← coe_supportEquiv_pow b hb,
      _root_.Equiv.apply_symm_apply, i.2, P.componentEquiv_pow_minimalPeriod]⟩
  left_inv i := Subtype.ext (_root_.Equiv.symm_apply_apply _ _)
  right_inv i := Subtype.ext (_root_.Equiv.apply_symm_apply _ _)

@[simp] theorem coe_componentReturnSupportPerm_apply
    (i : {i : b.support // P.componentOf (i : ι) = C}) :
    ((b.componentReturnSupportPerm σ hb C i).1 : ι) =
      (σ.indexEquiv ^ minimalPeriod σ.componentEquiv C) (i.1 : ι) :=
  coe_supportEquiv_pow b hb _ i.1

@[simp] theorem coe_componentReturnSupportPerm_pow (k : ℕ)
    (i : {i : b.support // P.componentOf (i : ι) = C}) :
    (((b.componentReturnSupportPerm σ hb C ^ k) i).1 : ι) =
      ((σ.indexEquiv ^ minimalPeriod σ.componentEquiv C) ^ k) (i.1 : ι) := by
  induction k with | zero => rfl | succ k ih => simp [pow_succ', ih]

/-- The permutation of simple roots in the `σ`-cycle of `C` induced by `σ`. -/
noncomputable def componentCycleSupportPerm :
    Perm {i : b.support // SameCycle σ.componentEquiv C (P.componentOf (i : ι))} where
  toFun i := ⟨σ.supportEquiv hb i.1, by
    rw [σ.coe_supportEquiv_apply, ← σ.componentEquiv_componentOf]
    exact Perm.sameCycle_apply_right.mpr i.2⟩
  invFun i := ⟨(σ.supportEquiv hb).symm i.1, by
    rw [σ.coe_supportEquiv_symm_apply, ← σ.componentEquiv_symm_componentOf]
    exact Perm.sameCycle_symm_apply_right.mpr i.2⟩
  left_inv i := Subtype.ext (_root_.Equiv.symm_apply_apply _ _)
  right_inv i := Subtype.ext (_root_.Equiv.apply_symm_apply _ _)

@[simp] theorem coe_componentCycleSupportPerm_apply
    (i : {i : b.support // SameCycle σ.componentEquiv C (P.componentOf (i : ι))}) :
    ((b.componentCycleSupportPerm σ hb C i).1 : ι) = σ.indexEquiv (i.1 : ι) :=
  σ.coe_supportEquiv_apply hb i.1

@[simp] theorem coe_componentCycleSupportPerm_pow (k : ℕ)
    (i : {i : b.support // SameCycle σ.componentEquiv C (P.componentOf (i : ι))}) :
    (((b.componentCycleSupportPerm σ hb C ^ k) i).1 : ι) = (σ.indexEquiv ^ k) (i.1 : ι) := by
  induction k with | zero => rfl | succ k ih => simp [pow_succ', ih]

private theorem sameCycle_componentReturnSupportPerm_iff
    (i j : {i : b.support // P.componentOf (i : ι) = C}) :
    SameCycle (b.componentReturnSupportPerm σ hb C) i j ↔
      SameCycle (b.componentCycleSupportPerm σ hb C) ⟨i.1, by rw [i.2]⟩ ⟨j.1, by rw [j.2]⟩ := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨k, rfl⟩ := h.exists_nat_pow_eq
    refine ⟨(minimalPeriod σ.componentEquiv C * k : ℕ), Subtype.ext <| Subtype.ext ?_⟩
    rw [zpow_natCast, b.coe_componentCycleSupportPerm_pow, b.coe_componentReturnSupportPerm_pow,
      ← pow_mul]
  · obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
    have hk_val : (σ.indexEquiv ^ k) (i.1 : ι) = (j.1 : ι) := by
      simpa using congrArg (fun x ↦ (x.1 : ι)) hk
    have hc_per : IsPeriodicPt σ.componentEquiv k C := by
      rw [IsPeriodicPt, IsFixedPt]
      conv_lhs => rw [← i.2]
      rw [← Perm.coe_pow, ← σ.componentEquiv_pow, (σ ^ k).componentEquiv_componentOf,
        σ.indexEquiv_pow, hk_val, j.2]
    obtain ⟨q, rfl⟩ := hc_per.minimalPeriod_dvd
    refine ⟨(q : ℕ), Subtype.ext <| Subtype.ext ?_⟩
    rw [zpow_natCast, b.coe_componentReturnSupportPerm_pow, ← pow_mul, hk_val]

/-- **Bijection between simple-root `(σ ^ c)`-orbits in `C` and `σ`-orbits in its cycle.** -/
noncomputable def componentCycleSimpleOrbitEquiv :
    Quotient (SameCycle.setoid (b.componentReturnSupportPerm σ hb C)) ≃
      Quotient (SameCycle.setoid (b.componentCycleSupportPerm σ hb C)) :=
  have hsemi : Semiconj (fun x ↦ P.componentOf (x.1 : ι))
      (b.componentCycleSupportPerm σ hb C) σ.componentEquiv := fun x ↦ by
    dsimp only; rw [b.coe_componentCycleSupportPerm_apply, ← σ.componentEquiv_componentOf]
  _root_.Equiv.ofBijective
    (Quotient.lift (fun i ↦ ⟦⟨i.1, by rw [i.2]⟩⟧) fun i j hij ↦
      Quotient.sound ((b.sameCycle_componentReturnSupportPerm_iff σ hb C i j).mp hij))
    ⟨fun o₁ o₂ h ↦ by
      induction o₁ using Quotient.ind with | _ i =>
      induction o₂ using Quotient.ind with | _ j =>
      exact Quotient.sound
        ((b.sameCycle_componentReturnSupportPerm_iff σ hb C i j).mpr (Quotient.exact h)),
    fun O ↦ by
      induction O using Quotient.ind with | _ j =>
      obtain ⟨k, hk⟩ := j.2.symm
      let i₀ : {i : b.support // P.componentOf (i : ι) = C} :=
        ⟨((b.componentCycleSupportPerm σ hb C ^ k) j).1, (hsemi.perm_zpow_right k j).trans hk⟩
      exact ⟨⟦i₀⟧, Quotient.sound (SameCycle.symm ⟨k, Subtype.ext rfl⟩)⟩⟩

/-- The orbit correspondence sends the cycle of a simple root in `C` to its `σ`-cycle. -/
@[simp] theorem componentCycleSimpleOrbitEquiv_mk
    (i : {i : b.support // P.componentOf (i : ι) = C}) :
    b.componentCycleSimpleOrbitEquiv σ hb C ⟦i⟧ = ⟦⟨i.1, by rw [i.2]⟩⟧ := (rfl)

end SupportPerm

private noncomputable local instance fintypeSupportComponent {ι R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] {P : RootPairing ι R M N}
    (b : P.Base) (C : P.Component) :
    Fintype {i : b.support // P.componentOf (i : ι) = C} := Fintype.ofFinite _

private noncomputable local instance fintypeSupportComponentCycle {ι R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] {P : RootPairing ι R M N}
    (b : P.Base) (σ : P.Aut) (C : P.Component) :
    Fintype {i : b.support // SameCycle σ.componentEquiv C (P.componentOf (i : ι))} :=
  Fintype.ofFinite _

section CycleBasis

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsRootSystem] (b : P.Base)

section SubWeightBasis

variable (p : b.support → Prop) (U : Submodule R M)
  (hmem : ∀ i : {i : b.support // p i}, P.root (i.1 : ι) ∈ U)
  (hzero : ∀ {x : M} {i : b.support}, x ∈ U → ¬p i → b.toWeightBasis.repr x i = 0)

private noncomputable def subWeightBasis : Module.Basis {i : b.support // p i} R U := by
  classical
  haveI : Fintype {i : b.support // p i} := Fintype.ofFinite _
  exact Module.Basis.ofEquivFun
    { toFun x i := b.toWeightBasis.repr (x : M) i.1
      map_add' _ _ := funext fun _ ↦ by simp
      map_smul' _ _ := funext fun _ ↦ by simp
      invFun f := ∑ i, f i • (⟨P.root (i.1 : ι), hmem i⟩ : U)
      left_inv x := Subtype.ext <| by
        simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower]
        conv_rhs => rw [← b.toWeightBasis.sum_repr (x : M)]
        simp only [b.toWeightBasis_apply]
        rw [← Finset.sum_subtype (Finset.univ.filter p) (fun _ ↦ by simp)
          (fun j : b.support ↦ b.toWeightBasis.repr (x : M) j • P.root (j : ι))]
        refine Finset.sum_subset (Finset.subset_univ _) fun j _ hj ↦ ?_
        rw [hzero x.2 (by simpa using hj), zero_smul]
      right_inv f := funext fun i ↦ by
        simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower, map_sum, map_smul,
          Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
        rw [Finset.sum_eq_single i
          (fun j _ hji ↦ by rw [← b.toWeightBasis_apply, Module.Basis.repr_self,
            Finsupp.single_eq_of_ne' (fun h ↦ hji (Subtype.ext h)), mul_zero]) (by simp),
          ← b.toWeightBasis_apply, Module.Basis.repr_self, Finsupp.single_eq_same, mul_one] }

private theorem subWeightBasis_repr_apply (x : U) (i : {i : b.support // p i}) :
    (b.subWeightBasis p U hmem hzero).repr x i = b.toWeightBasis.repr (x : M) i.1 := by
  simp [subWeightBasis]

private theorem coe_subWeightBasis_apply (i : {i : b.support // p i}) :
    (b.subWeightBasis p U hmem hzero i : M) = P.root (i.1 : ι) := by
  classical
  rw [subWeightBasis, Module.Basis.coe_ofEquivFun]
  dsimp only [LinearEquiv.coe_symm_mk]
  simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower]
  rw [Finset.sum_eq_single i (fun j _ hji ↦ by rw [Pi.single_eq_of_ne hji, zero_smul]) (by simp)]
  simp

end SubWeightBasis

/-- The simple roots of `b` lying in `C` form an `R`-basis of `P.componentSpace C`. -/
noncomputable def componentWeightBasis (C : P.Component) :
    Module.Basis {i : b.support // P.componentOf (i : ι) = C} R (P.componentSpace C) :=
  b.subWeightBasis (fun i : b.support ↦ P.componentOf (i : ι) = C) (P.componentSpace C)
    (fun i ↦ P.root_mem_componentSpace_of_mem_supp ((C.mem_supp_iff _).mpr i.2))
    (fun hx hi ↦ P.toWeightBasis_repr_eq_zero_of_mem_componentSpace b hx hi)

@[simp] theorem componentWeightBasis_repr_apply (C : P.Component) (x : P.componentSpace C)
    (i : {i : b.support // P.componentOf (i : ι) = C}) :
    (b.componentWeightBasis C).repr x i = b.toWeightBasis.repr (x : M) i.1 :=
  b.subWeightBasis_repr_apply _ _ _ _ x i

@[simp] theorem coe_componentWeightBasis_apply (C : P.Component)
    (i : {i : b.support // P.componentOf (i : ι) = C}) :
    (b.componentWeightBasis C i : M) = P.root (i.1 : ι) :=
  b.coe_subWeightBasis_apply _ _ _ _ i

/-- The simple roots of `b` in the `σ`-cycle of `C` form an `R`-basis of
`P.componentCycleSpace σ C`. -/
noncomputable def componentCycleWeightBasis (σ : P.Aut) (C : P.Component) :
    Module.Basis {i : b.support // SameCycle σ.componentEquiv C (P.componentOf (i : ι))} R
      (P.componentCycleSpace σ C) :=
  b.subWeightBasis (fun i : b.support ↦ SameCycle σ.componentEquiv C (P.componentOf (i : ι)))
    (P.componentCycleSpace σ C)
    (fun i ↦ P.componentSpace_le_componentCycleSpace i.2 (P.root_mem_componentSpace _))
    (fun hx hi ↦ P.toWeightBasis_repr_eq_zero_of_mem_componentCycleSpace b hx hi)

@[simp] theorem componentCycleWeightBasis_repr_apply (σ : P.Aut) (C : P.Component)
    (x : P.componentCycleSpace σ C)
    (i : {i : b.support // SameCycle σ.componentEquiv C (P.componentOf (i : ι))}) :
    (b.componentCycleWeightBasis σ C).repr x i = b.toWeightBasis.repr (x : M) i.1 :=
  b.subWeightBasis_repr_apply _ _ _ _ x i

@[simp] theorem coe_componentCycleWeightBasis_apply (σ : P.Aut) (C : P.Component)
    (i : {i : b.support // SameCycle σ.componentEquiv C (P.componentOf (i : ι))}) :
    (b.componentCycleWeightBasis σ C i : M) = P.root (i.1 : ι) :=
  b.coe_subWeightBasis_apply _ _ _ _ i

section CycleOrbit

variable (σ : P.Aut) (hb : ∀ i, i ∈ b.support ↔ σ.indexEquiv i ∈ b.support) (C : P.Component)

/-- **The simple-orbit `R`-basis of the cycle fixed space**
`P.componentCycleFixedSubmodule σ C`. -/
noncomputable def componentCycleSimpleOrbitBasis :
    Module.Basis (Quotient (SameCycle.setoid (b.componentCycleSupportPerm σ hb C))) R
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
      left_inv _ := rfl, right_inv _ := rfl, map_add' _ _ := rfl, map_smul' _ _ := rfl }
  (Perm.basisPermFixedBasis (b.componentCycleWeightBasis σ C) eCyc
    (b.componentCycleSupportPerm σ hb C) fun i ↦ Subtype.ext <| by
      dsimp only [eCyc]
      rw [LinearEquiv.ofSubmodules_apply, Equiv.weightEquiv_apply,
        b.coe_componentCycleWeightBasis_apply, b.coe_componentCycleWeightBasis_apply,
        b.coe_componentCycleSupportPerm_apply, Hom.root_weightMap_apply P P _ σ.toHom]).map eFix

@[simp] theorem componentCycleSimpleOrbitBasis_repr (y : P.componentCycleFixedSubmodule σ C)
    (i : {i : b.support // SameCycle σ.componentEquiv C (P.componentOf (i : ι))}) :
    (b.componentCycleSimpleOrbitBasis σ hb C).repr y ⟦i⟧ =
      b.toWeightBasis.repr (y.1 : M) i.1 := by
  simp [componentCycleSimpleOrbitBasis]

/-- Each vector of `componentCycleSimpleOrbitBasis` is the `σ`-orbit sum of its representative. -/
theorem coe_componentCycleSimpleOrbitBasis_apply [Finite ι]
    (O : Quotient (SameCycle.setoid (b.componentCycleSupportPerm σ hb C))) :
    ((b.componentCycleSimpleOrbitBasis σ hb C O : LinearMap.fixedSubmodule σ.weightMap) : M) =
      P.orbitSum σ (O.out.1 : ι) := by
  classical
  simp only [componentCycleSimpleOrbitBasis, Module.Basis.map_apply, LinearEquiv.coe_mk,
    LinearMap.coe_mk, AddHom.coe_mk, Perm.coe_basisPermFixedBasis_apply, Submodule.coe_sum,
    b.coe_componentCycleWeightBasis_apply, P.orbitSum_eq_sum_range]
  exact Perm.sum_filter_quotient_eq_sum_range (b.componentCycleSupportPerm σ hb C)
    (fun j ↦ (j.1 : ι)) (Subtype.val_injective.comp Subtype.val_injective) σ.indexEquiv
    (fun j ↦ b.coe_componentCycleSupportPerm_apply σ hb C j) P.root O

end CycleOrbit

end CycleBasis

section ReturnSimpleOrbitBasis

variable {ι K M N : Type*} [Field K] [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  {P : RootPairing ι K M N} [Finite ι] [P.IsRootSystem] (b : P.Base)
  (σ : P.Aut) (hb : ∀ i, i ∈ b.support ↔ σ.indexEquiv i ∈ b.support) (C : P.Component)

/-- **The simple-orbit `K`-basis of the return fixed space**
`LinearMap.fixedSubmodule (P.componentReturnAut σ C).weightMap`. -/
noncomputable def componentReturnSimpleOrbitBasis :
    Module.Basis (Quotient (SameCycle.setoid (b.componentReturnSupportPerm σ hb C))) K
      (LinearMap.fixedSubmodule (P.componentReturnAut σ C).weightMap) :=
  (Perm.basisPermFixedBasis (b.componentWeightBasis C) (P.componentReturnAut σ C).weightEquiv
    (b.componentReturnSupportPerm σ hb C) fun i ↦ Subtype.ext <| by
      rw [P.coe_componentReturnAut_weightEquiv, b.coe_componentWeightBasis_apply,
        b.coe_componentWeightBasis_apply, b.coe_componentReturnSupportPerm_apply,
        ← σ.weightMap_pow, ← σ.indexEquiv_pow, Hom.root_weightMap_apply P P _ (σ ^ _).toHom]).map
    (LinearEquiv.ofEq _ _
      (congrArg LinearMap.fixedSubmodule
        (LinearMap.ext (P.componentReturnAut σ C).weightEquiv_apply)))

@[simp] theorem componentReturnSimpleOrbitBasis_repr
    (u : LinearMap.fixedSubmodule (P.componentReturnAut σ C).weightMap)
    (i : {i : b.support // P.componentOf (i : ι) = C}) :
    (b.componentReturnSimpleOrbitBasis σ hb C).repr u ⟦i⟧ =
      b.toWeightBasis.repr (u : M) i.1 := by
  rw [componentReturnSimpleOrbitBasis, Module.Basis.map_repr, LinearEquiv.trans_apply,
    Perm.basisPermFixedBasis_repr, componentWeightBasis_repr_apply]; rfl

/-- Each vector of `componentReturnSimpleOrbitBasis` is its representative's return orbit sum. -/
theorem coe_componentReturnSimpleOrbitBasis_apply
    (o : Quotient (SameCycle.setoid (b.componentReturnSupportPerm σ hb C))) :
    ((b.componentReturnSimpleOrbitBasis σ hb C o :
        LinearMap.fixedSubmodule (P.componentReturnAut σ C).weightMap) : P.componentSpace C) =
      (P.componentPairing C).orbitSum (P.componentReturnAut σ C)
        ⟨o.out.1, (C.mem_supp_iff _).mpr o.out.2⟩ := by
  classical
  apply Subtype.ext
  simp only [componentReturnSimpleOrbitBasis, Module.Basis.map_apply, LinearEquiv.coe_ofEq_apply,
    Perm.coe_basisPermFixedBasis_apply, Submodule.coe_sum, b.coe_componentWeightBasis_apply,
    (P.componentPairing C).orbitSum_eq_sum_range]
  refine (Perm.sum_filter_quotient_eq_sum_range (b.componentReturnSupportPerm σ hb C)
    (fun j ↦ (⟨j.1, (C.mem_supp_iff _).mpr j.2⟩ : C.supp))
    (fun _ _ h ↦ Subtype.ext (Subtype.ext (congrArg (Subtype.val : C.supp → ι) h)))
    (P.componentReturnAut σ C).indexEquiv
    (fun j ↦ Subtype.ext (by
      rw [b.coe_componentReturnSupportPerm_apply, P.coe_componentReturnAut_indexEquiv]))
    (fun k ↦ P.root (k : ι)) o).trans ?_
  exact Finset.sum_congr rfl fun r _ ↦ (P.coe_componentPairing_root C _).symm

/-- **Diagonal transport carries the return simple-orbit basis to the cycle simple-orbit basis.** -/
@[simp] theorem componentCycleDiag_componentReturnSimpleOrbitBasis
    (o : Quotient (SameCycle.setoid (b.componentReturnSupportPerm σ hb C))) :
    P.componentCycleDiag σ C (b.componentReturnSimpleOrbitBasis σ hb C o) =
      b.componentCycleSimpleOrbitBasis σ hb C (b.componentCycleSimpleOrbitEquiv σ hb C o) := by
  apply Subtype.ext; apply Subtype.ext
  have hret : b.componentReturnSimpleOrbitBasis σ hb C o =
      P.componentReturnOrbitSumFixed σ C ⟨o.out.1, (C.mem_supp_iff _).mpr o.out.2⟩ :=
    Subtype.ext ((b.coe_componentReturnSimpleOrbitBasis_apply σ hb C o).trans
      (P.coe_componentReturnOrbitSumFixed σ C _).symm)
  rw [hret, P.coe_componentCycleDiag_orbitSum, b.coe_componentCycleSimpleOrbitBasis_apply]
  have heq : b.componentCycleSimpleOrbitEquiv σ hb C o = ⟦⟨o.out.1, by rw [o.out.2]⟩⟧ := by
    conv_lhs => rw [← Quotient.out_eq o, b.componentCycleSimpleOrbitEquiv_mk]
  obtain ⟨k, hk⟩ := (Quotient.exact ((Quotient.out_eq _).trans heq) :
    SameCycle (b.componentCycleSupportPerm σ hb C) (b.componentCycleSimpleOrbitEquiv σ hb C o).out
      ⟨o.out.1, by rw [o.out.2]⟩).exists_nat_pow_eq
  exact P.orbitSum_eq_of_mem (P.mem_orbitIndices_iff_exists_pow.mpr ⟨k, by
    simpa using congrArg (fun x ↦ (x.1 : ι)) hk⟩)

/-- **Simple-orbit coordinates are preserved unchanged by `componentCycleDiag`.** -/
@[simp] theorem componentCycleSimpleOrbitBasis_repr_componentCycleDiag
    (u : LinearMap.fixedSubmodule (P.componentReturnAut σ C).weightMap)
    (o : Quotient (SameCycle.setoid (b.componentReturnSupportPerm σ hb C))) :
    (b.componentCycleSimpleOrbitBasis σ hb C).repr (P.componentCycleDiag σ C u)
        (b.componentCycleSimpleOrbitEquiv σ hb C o) =
      (b.componentReturnSimpleOrbitBasis σ hb C).repr u o := by
  induction o using Quotient.ind with | _ i =>
  rw [b.componentCycleSimpleOrbitEquiv_mk, b.componentCycleSimpleOrbitBasis_repr,
    b.componentReturnSimpleOrbitBasis_repr, ← P.toWeightBasis_repr_componentProj_of_eq b i.2,
    P.componentProj_componentCycleDiag]

/-- A return fixed vector lies in `posRootCone P b` iff its return simple-orbit coordinates lie in
`ℕ`. -/
theorem mem_posRootCone_iff_forall_componentReturnSimpleOrbitBasis_repr
    (u : LinearMap.fixedSubmodule (P.componentReturnAut σ C).weightMap) :
    (u : M) ∈ posRootCone P b ↔
      ∀ o, ∃ n : ℕ, (b.componentReturnSimpleOrbitBasis σ hb C).repr u o = (n : K) := by
  have := Fintype.ofFinite (Quotient (SameCycle.setoid (b.componentReturnSupportPerm σ hb C)))
  refine ⟨fun hu o ↦ ?_, fun h ↦ ?_⟩
  · classical
    obtain ⟨f, hf⟩ := (mem_posRootCone P b).mp hu
    refine ⟨f o.out.1, ?_⟩
    conv_lhs => rw [← Quotient.out_eq o]
    rw [b.componentReturnSimpleOrbitBasis_repr, hf, ← Finset.sum_coe_sort b.support]
    simp only [← Nat.cast_smul_eq_nsmul K, ← b.toWeightBasis_apply, map_sum, map_smul,
      Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul, Module.Basis.repr_self]
    rw [Finset.sum_eq_single o.out.1 (fun _ _ hj ↦ by rw [Finsupp.single_eq_of_ne' hj, mul_zero])
      (by simp)]
    simp
  · classical
    choose n hn using h
    have hsum : u = ∑ o, n o • b.componentReturnSimpleOrbitBasis σ hb C o := by
      conv_lhs => rw [← (b.componentReturnSimpleOrbitBasis σ hb C).sum_repr u]
      exact Finset.sum_congr rfl fun o _ ↦ by rw [hn o, Nat.cast_smul_eq_nsmul]
    rw [hsum, Submodule.coe_sum, Submodule.coe_sum]
    refine AddSubmonoid.sum_mem _ fun o _ ↦ ?_
    rw [Submodule.coe_smul_of_tower, Submodule.coe_smul_of_tower]
    refine AddSubmonoid.nsmul_mem _ ?_ _
    rw [componentReturnSimpleOrbitBasis, Module.Basis.map_apply, LinearEquiv.coe_ofEq_apply,
      Perm.coe_basisPermFixedBasis_apply, Submodule.coe_sum]
    exact AddSubmonoid.sum_mem _ fun j _ ↦ by
      rw [b.coe_componentWeightBasis_apply]; exact P.root_mem_posRootCone_of_mem_support b j.1.2

end ReturnSimpleOrbitBasis

end Base

end RootPairing
