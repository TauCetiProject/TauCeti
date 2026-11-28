/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Component.Base
public import TauCeti.LinearAlgebra.RootSystem.Component.Cycle.Diag
public import TauCeti.LinearAlgebra.RootSystem.OrbitSum.Realization
import TauCeti.GroupTheory.Perm.Cycle.Enumeration
import TauCeti.GroupTheory.Perm.Semiconj

/-!
# Bases, simple-orbit coordinates, and positive cones on component cycles

When an automorphism `σ` of a root system `P` stabilizes the support of a base `b`,
`P.componentCycleDiag σ C` transports simple-root coordinates, orbit-sum bases
(`Base.componentCycleWeightBasis`, `Base.componentReturnSimpleOrbitBasis`,
`Base.componentCycleSimpleOrbitBasis`, `Base.componentCycleSimpleOrbitEquiv`,
`Base.componentCycleSigmaSimpleOrbitEquiv`, `Base.componentReturnBaseOrbitEquiv`), and the
positive root cone (`mem_posRootCone_componentCycleDiag_iff`,
`Base.mem_posRootCone_iff_forall_componentReturnSimpleOrbitBasis_repr`) without distortion.

## References

* J. R. Stembridge, *Folding by automorphisms* (2008); N. Bourbaki, *Lie Groups and Lie Algebras*,
  Ch. VI §1, no. 7.
-/

public section

open Finset Function TauCeti
open _root_.Equiv (Perm)
open _root_.Equiv.Perm (SameCycle)

namespace RootPairing

/-! ### Simple-root coordinates on component cycles -/

section CommRing

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) [P.IsRootSystem]

variable {P} in
/-- A vector in `P.componentCycleSpace σ C` vanishes on simple roots outside the cycle of `C`. -/
theorem toWeightBasis_repr_eq_zero_of_mem_componentCycleSpace (b : P.Base) {σ : P.Aut}
    {C : P.Component} {x : M} (hx : x ∈ P.componentCycleSpace σ C) {i : b.support}
    (hi : ¬SameCycle σ.componentEquiv C (P.componentOf (i : ι))) :
    b.toWeightBasis.repr x i = 0 := by
  rw [← P.toWeightBasis_repr_componentProj_of_eq b rfl x,
    P.componentProj_eq_zero_of_not_sameCycle hx hi, Submodule.coe_zero, map_zero,
    Finsupp.zero_apply]

variable {P} in
/-- Distinct component cycles contribute disjoint folded sets for a base-preserving `σ`. -/
theorem pairwise_disjoint_componentCycleFoldedIndices_of_base [Finite ι] [CharZero R]
    {σ : P.Aut} {b : P.Base} (hσ : ∀ j ∈ b.support, σ.indexEquiv j ∈ b.support) :
    Pairwise fun O₁ O₂ : Quotient (SameCycle.setoid σ.componentEquiv) ↦
      Disjoint (P.componentCycleFoldedIndices σ O₁.out)
        (P.componentCycleFoldedIndices σ O₂.out) :=
  P.pairwise_disjoint_componentCycleFoldedIndices (P.zero_notMem_foldedIndices hσ)

end CommRing

/-! ### Cone and positivity transport under `componentCycleDiag` -/

section Field

variable {ι K M N : Type*} [Field K] [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  (P : RootPairing ι K M N) [Finite ι] [P.IsRootSystem]

/-- **Cone preservation under `componentCycleDiag`** for a base-preserving automorphism `σ`. -/
theorem mem_posRootCone_componentCycleDiag_iff {σ : P.Aut} {b : P.Base}
    (hσ : ∀ j ∈ b.support, σ.indexEquiv j ∈ b.support) (C : P.Component)
    (u : LinearMap.fixedSubmodule (σ.componentReturn C).toHom.weightMap) :
    ((P.componentCycleDiag σ C u : LinearMap.fixedSubmodule σ.weightMap) : M) ∈ posRootCone P b ↔
      (u : M) ∈ posRootCone P b :=
  P.mem_addSubmonoid_componentCycleDiag_iff (posRootCone P b)
    (fun {x} hx ↦ by
      obtain ⟨f, rfl⟩ := (mem_posRootCone P b).mp hx
      rw [map_sum]
      refine AddSubmonoid.sum_mem _ fun j hj ↦ ?_
      rw [map_nsmul, Hom.root_weightMap_apply P P j σ.toHom]
      exact AddSubmonoid.nsmul_mem _ (root_mem_posRootCone_of_mem_support P b (hσ j hj)) _)
    C (fun hx ↦ P.componentProj_mem_posRootCone b C hx) u

end Field

/-! ### Simple-orbit bases on the return fixed space and cycle fixed space -/

namespace Base

section SupportPerm

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} (b : P.Base)
  (σ : P.Aut) (hσ : ∀ j ∈ b.support, σ.indexEquiv j ∈ b.support) (C : P.Component)

private theorem componentOf_supportPerm_pow_minimalPeriod_eq_iff (i : b.support) :
    P.componentOf ((b.supportPerm hσ ^ minimalPeriod σ.componentEquiv C) i : ι) = C ↔
      P.componentOf (i : ι) = C := by
  rw [b.coe_supportPerm_pow hσ, (P.semiconj_componentOf σ).perm_pow_right,
    ← σ.componentEquiv_pow]
  nth_rw 2 [← σ.componentEquiv_pow_minimalPeriod (C := C)]
  exact (σ ^ minimalPeriod σ.componentEquiv C).componentEquiv.injective.eq_iff

/-- The permutation of simple roots in `C` induced by the return iterate `σ ^ c`. -/
noncomputable def componentReturnSupportPerm :
    Perm {i : b.support // P.componentOf (i : ι) = C} :=
  (b.supportPerm hσ ^ minimalPeriod σ.componentEquiv C).subtypePerm
    (b.componentOf_supportPerm_pow_minimalPeriod_eq_iff σ hσ C)

@[simp] theorem coe_componentReturnSupportPerm_apply
    (i : {i : b.support // P.componentOf (i : ι) = C}) :
    ((b.componentReturnSupportPerm σ hσ C i).val : ι) =
      (σ.indexEquiv ^ minimalPeriod σ.componentEquiv C) (i.val : ι) :=
  b.coe_supportPerm_pow hσ _ i.val

@[simp] theorem coe_componentReturnSupportPerm_symm_apply
    (i : {i : b.support // P.componentOf (i : ι) = C}) :
    (((b.componentReturnSupportPerm σ hσ C).symm i).val : ι) =
      (σ.indexEquiv ^ minimalPeriod σ.componentEquiv C).symm (i.val : ι) :=
  (σ.indexEquiv ^ minimalPeriod σ.componentEquiv C).eq_symm_apply.mpr <| by
    rw [← b.coe_componentReturnSupportPerm_apply σ hσ C, _root_.Equiv.apply_symm_apply]

@[simp] theorem coe_componentReturnSupportPerm_pow (k : ℕ)
    (i : {i : b.support // P.componentOf (i : ι) = C}) :
    (((b.componentReturnSupportPerm σ hσ C ^ k) i).val : ι) =
      ((σ.indexEquiv ^ minimalPeriod σ.componentEquiv C) ^ k) (i.val : ι) :=
  Semiconj.perm_pow_right (g := fun x : {i : b.support // P.componentOf (i : ι) = C} ↦ (x.val : ι))
    (fun j ↦ b.coe_componentReturnSupportPerm_apply σ hσ C j) k i

private theorem sameCycle_componentOf_supportPerm_iff (i : b.support) :
    SameCycle σ.componentEquiv C (P.componentOf (b.supportPerm hσ i : ι)) ↔
      SameCycle σ.componentEquiv C (P.componentOf (i : ι)) := by
  rw [b.coe_supportPerm_apply, ← σ.componentEquiv_componentOf]
  exact Perm.sameCycle_apply_right

/-- The permutation of simple roots in the `σ`-cycle of `C` induced by `σ`. -/
noncomputable def componentCycleSupportPerm :
    Perm {i : b.support // SameCycle σ.componentEquiv C (P.componentOf (i : ι))} :=
  (b.supportPerm hσ).subtypePerm (b.sameCycle_componentOf_supportPerm_iff σ hσ C)

@[simp] theorem coe_componentCycleSupportPerm_apply
    (i : {i : b.support // SameCycle σ.componentEquiv C (P.componentOf (i : ι))}) :
    ((b.componentCycleSupportPerm σ hσ C i).val : ι) = σ.indexEquiv (i.val : ι) :=
  b.coe_supportPerm_apply hσ i.val

@[simp] theorem coe_componentCycleSupportPerm_symm_apply
    (i : {i : b.support // SameCycle σ.componentEquiv C (P.componentOf (i : ι))}) :
    (((b.componentCycleSupportPerm σ hσ C).symm i).val : ι) = σ.indexEquiv.symm (i.val : ι) :=
  b.coe_supportPerm_symm_apply hσ i.val

@[simp] theorem coe_componentCycleSupportPerm_pow (k : ℕ)
    (i : {i : b.support // SameCycle σ.componentEquiv C (P.componentOf (i : ι))}) :
    (((b.componentCycleSupportPerm σ hσ C ^ k) i).val : ι) = (σ.indexEquiv ^ k) (i.val : ι) :=
  Semiconj.perm_pow_right
    (g := fun x : {i : b.support // SameCycle σ.componentEquiv C (P.componentOf (i : ι))} ↦
      (x.val : ι))
    (fun j ↦ b.coe_componentCycleSupportPerm_apply σ hσ C j) k i

private theorem semiconj_componentCycleSupportPerm :
    Semiconj (fun x : {i : b.support // SameCycle σ.componentEquiv C (P.componentOf (i : ι))} ↦
      P.componentOf (x.val : ι)) (b.componentCycleSupportPerm σ hσ C) σ.componentEquiv :=
  fun x ↦ by dsimp only; rw [b.coe_componentCycleSupportPerm_apply, ← σ.componentEquiv_componentOf]

private theorem sameCycle_componentReturnSupportPerm_iff
    (i j : {i : b.support // P.componentOf (i : ι) = C}) :
    SameCycle (b.componentReturnSupportPerm σ hσ C) i j ↔
      SameCycle (b.componentCycleSupportPerm σ hσ C) ⟨i.val, by rw [i.property]⟩
        ⟨j.val, by rw [j.property]⟩ := by
  let ιC : {i : b.support // P.componentOf (i : ι) = C} →
      {i : b.support // SameCycle σ.componentEquiv C (P.componentOf (i : ι))} :=
    fun k ↦ ⟨k.val, by rw [k.property]⟩
  have hιC : Semiconj ιC (b.componentReturnSupportPerm σ hσ C)
      ⇑(b.componentCycleSupportPerm σ hσ C ^ minimalPeriod σ.componentEquiv C) := fun k ↦
    Subtype.ext <| Subtype.ext <| by
      rw [b.coe_componentCycleSupportPerm_pow, b.coe_componentReturnSupportPerm_apply]
  have hset := Set.ext_iff.mp
    ((b.semiconj_componentCycleSupportPerm σ hσ C).setOf_sameCycle_and_eq (ιC i)) (ιC j)
  simp only [Set.mem_ofPred_eq, ιC, i.property, j.property, and_true] at hset
  exact (hιC.sameCycle_iff fun _ _ h ↦ Subtype.ext (congrArg (fun k ↦ k.val) h)).symm.trans
    hset.symm

/-- **Bijection between simple-root `(σ ^ c)`-orbits in `C` and `σ`-orbits in its cycle.** -/
noncomputable def componentCycleSimpleOrbitEquiv :
    Quotient (SameCycle.setoid (b.componentReturnSupportPerm σ hσ C)) ≃
      Quotient (SameCycle.setoid (b.componentCycleSupportPerm σ hσ C)) :=
  _root_.Equiv.ofBijective
    (Quotient.lift (fun i ↦ ⟦⟨i.val, by rw [i.property]⟩⟧) fun i j hij ↦
      Quotient.sound ((b.sameCycle_componentReturnSupportPerm_iff σ hσ C i j).mp hij))
    ⟨fun o₁ o₂ h ↦ by
      induction o₁ using Quotient.ind with | _ i =>
      induction o₂ using Quotient.ind with | _ j =>
      exact Quotient.sound
        ((b.sameCycle_componentReturnSupportPerm_iff σ hσ C i j).mpr (Quotient.exact h)),
    fun O ↦ by
      induction O using Quotient.ind with | _ j =>
      obtain ⟨k, hk⟩ := j.property.symm
      let i₀ : {i : b.support // P.componentOf (i : ι) = C} :=
        ⟨((b.componentCycleSupportPerm σ hσ C ^ k) j).val,
          ((b.semiconj_componentCycleSupportPerm σ hσ C).perm_zpow_right k j).trans hk⟩
      exact ⟨⟦i₀⟧, Quotient.sound (SameCycle.symm ⟨k, Subtype.ext rfl⟩)⟩⟩

/-- The orbit correspondence sends the cycle of a simple root in `C` to its `σ`-cycle. -/
@[simp] theorem componentCycleSimpleOrbitEquiv_mk
    (i : {i : b.support // P.componentOf (i : ι) = C}) :
    b.componentCycleSimpleOrbitEquiv σ hσ C ⟦i⟧ = ⟦⟨i.val, by rw [i.property]⟩⟧ := (rfl)

omit C in
/-- **Sigma-orbit bijection**: grouping `(σ ^ c)`-simple-root orbits by `σ`-component cycles
bijects with `σ`-orbits on the full simple-root support `b.support`. -/
noncomputable def componentCycleSigmaSimpleOrbitEquiv :
    (Σ O : Quotient (SameCycle.setoid σ.componentEquiv),
      Quotient (SameCycle.setoid (b.componentCycleSupportPerm σ hσ O.out))) ≃
      Quotient (SameCycle.setoid (b.supportPerm hσ)) :=
  let hval (D : P.Component) :
      Semiconj (fun i : {i : b.support // SameCycle σ.componentEquiv D (P.componentOf (i : ι))} ↦
        i.val) (b.componentCycleSupportPerm σ hσ D) (b.supportPerm hσ) := fun _ ↦ rfl
  let f : (Σ O : Quotient (SameCycle.setoid σ.componentEquiv),
      Quotient (SameCycle.setoid (b.componentCycleSupportPerm σ hσ O.out))) →
      Quotient (SameCycle.setoid (b.supportPerm hσ)) :=
    fun p ↦ Quotient.lift (fun i ↦ (⟦i.val⟧ : Quotient (SameCycle.setoid (b.supportPerm hσ))))
      (fun _ _ hij ↦ Quotient.sound (((hval p.1.out).sameCycle_iff Subtype.val_injective).mpr hij))
      p.2
  _root_.Equiv.ofBijective f
    ⟨fun ⟨O₁, o₁⟩ ⟨O₂, o₂⟩ h ↦ by
      induction o₁ using Quotient.ind with | _ i =>
      induction o₂ using Quotient.ind with | _ j =>
      have hij : SameCycle (b.supportPerm hσ) i.val j.val := Quotient.exact h
      obtain ⟨k, hk⟩ := hij.exists_nat_pow_eq
      have hcomp : SameCycle σ.componentEquiv (P.componentOf (i.val : ι))
          (P.componentOf (j.val : ι)) := by
        refine ⟨(k : ℤ), ?_⟩
        have h' := congrArg (fun x : b.support ↦ P.componentOf (x : ι)) hk
        rw [b.coe_supportPerm_pow hσ, (P.semiconj_componentOf σ).perm_pow_right] at h'
        rwa [zpow_natCast]
      have hO : O₁ = O₂ :=
        ((Perm.sameCycle_out_iff σ.componentEquiv).mp
          (i.property.trans (hcomp.trans j.property.symm))).symm.trans (Quotient.out_eq O₂)
      subst hO
      exact congrArg (Sigma.mk O₁) (Quotient.sound
        (((hval O₁.out).sameCycle_iff Subtype.val_injective).mp hij)),
    fun q ↦ by
      induction q using Quotient.ind with | _ i =>
      let O : Quotient (SameCycle.setoid σ.componentEquiv) := ⟦P.componentOf (i : ι)⟧
      have hi : SameCycle σ.componentEquiv O.out (P.componentOf (i : ι)) :=
        (Perm.sameCycle_out_iff σ.componentEquiv).mpr rfl
      exact ⟨⟨O, ⟦⟨i, hi⟩⟧⟩, rfl⟩⟩

omit C in
/-- `componentCycleSigmaSimpleOrbitEquiv` sends the cycle orbit of a simple root to its ambient
`σ`-orbit in `b.support`. -/
@[simp] theorem componentCycleSigmaSimpleOrbitEquiv_mk
    (O : Quotient (SameCycle.setoid σ.componentEquiv))
    (i : {i : b.support // SameCycle σ.componentEquiv O.out (P.componentOf (i : ι))}) :
    b.componentCycleSigmaSimpleOrbitEquiv σ hσ ⟨O, ⟦i⟧⟩ = ⟦i.val⟧ := (rfl)

end SupportPerm

section CycleBasis

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsRootSystem] (b : P.Base)

/-- The simple roots of `b` in the `σ`-cycle of `C` form an `R`-basis of
`P.componentCycleSpace σ C`. -/
noncomputable def componentCycleWeightBasis (σ : P.Aut) (C : P.Component) :
    Module.Basis {i : b.support // SameCycle σ.componentEquiv C (P.componentOf (i : ι))} R
      (P.componentCycleSpace σ C) :=
  b.toWeightBasis.restrict
    {i : b.support | SameCycle σ.componentEquiv C (P.componentOf (i : ι))}
    (P.componentCycleSpace σ C)
    (fun i hi ↦ by
      rw [b.toWeightBasis_apply]
      exact P.componentSpace_le_componentCycleSpace hi (P.root_mem_componentSpace _))
    (fun hx hi ↦ P.toWeightBasis_repr_eq_zero_of_mem_componentCycleSpace b hx hi)

@[simp] theorem componentCycleWeightBasis_repr_apply (σ : P.Aut) (C : P.Component)
    (x : P.componentCycleSpace σ C)
    (i : {i : b.support // SameCycle σ.componentEquiv C (P.componentOf (i : ι))}) :
    (b.componentCycleWeightBasis σ C).repr x i = b.toWeightBasis.repr (x : M) i.val := by
  rw [componentCycleWeightBasis, Module.Basis.restrict_repr]

@[simp] theorem coe_componentCycleWeightBasis_apply (σ : P.Aut) (C : P.Component)
    (i : {i : b.support // SameCycle σ.componentEquiv C (P.componentOf (i : ι))}) :
    (b.componentCycleWeightBasis σ C i : M) = P.root (i.val : ι) := by
  rw [componentCycleWeightBasis, Module.Basis.coe_restrict, b.toWeightBasis_apply]

section CycleOrbit

private noncomputable def cycleWeightEquiv (σ : P.Aut) (C : P.Component) :
    P.componentCycleSpace σ C ≃ₗ[R] P.componentCycleSpace σ C :=
  σ.weightEquiv.ofSubmodules _ _
    (by rw [LinearMap.ext σ.weightEquiv_apply]; exact P.map_componentCycleSpace σ C)

omit [P.IsRootSystem] in
@[simp] private theorem coe_cycleWeightEquiv_apply (σ : P.Aut) (C : P.Component)
    (x : P.componentCycleSpace σ C) :
    (cycleWeightEquiv (P := P) σ C x : M) = σ.weightMap x := by
  rw [cycleWeightEquiv, LinearEquiv.ofSubmodules_apply, Equiv.weightEquiv_apply]

private noncomputable def componentCycleFixedEquiv (σ : P.Aut) (C : P.Component) :
    (cycleWeightEquiv (P := P) σ C).toLinearMap.fixedSubmodule ≃ₗ[R]
      P.componentCycleFixedSubmodule σ C where
  toFun z := ⟨⟨(z.val : M), LinearMap.mem_fixedSubmodule_iff.mpr <| by
    simpa using congrArg Subtype.val (LinearMap.mem_fixedSubmodule_iff.mp z.property)⟩,
    P.mem_componentCycleFixedSubmodule.mpr z.val.property⟩
  invFun y := ⟨⟨(y.val : M), P.mem_componentCycleFixedSubmodule.mp y.property⟩,
    LinearMap.mem_fixedSubmodule_iff.mpr <| Subtype.ext <| by
      simpa using LinearMap.mem_fixedSubmodule_iff.mp y.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [P.IsRootSystem] in
@[simp] private theorem coe_componentCycleFixedEquiv_apply (σ : P.Aut) (C : P.Component)
    (z : (cycleWeightEquiv (P := P) σ C).toLinearMap.fixedSubmodule) :
    ((componentCycleFixedEquiv (P := P) σ C z : LinearMap.fixedSubmodule σ.weightMap) : M) =
      (z.val : M) := (rfl)

omit [P.IsRootSystem] in
@[simp] private theorem coe_componentCycleFixedEquiv_symm_apply (σ : P.Aut) (C : P.Component)
    (y : P.componentCycleFixedSubmodule σ C) :
    (((componentCycleFixedEquiv (P := P) σ C).symm y).val : M) = (y.val : M) := (rfl)

variable (σ : P.Aut) (hσ : ∀ j ∈ b.support, σ.indexEquiv j ∈ b.support) (C : P.Component)

/-- **The simple-orbit `R`-basis of the cycle fixed space**
`P.componentCycleFixedSubmodule σ C`. -/
noncomputable def componentCycleSimpleOrbitBasis :
    Module.Basis (Quotient (SameCycle.setoid (b.componentCycleSupportPerm σ hσ C))) R
      (P.componentCycleFixedSubmodule σ C) :=
  letI := Fintype.ofFinite {i : b.support // SameCycle σ.componentEquiv C (P.componentOf (i : ι))}
  (Perm.basisPermFixedBasis (b.componentCycleWeightBasis σ C) (cycleWeightEquiv (P := P) σ C)
    (b.componentCycleSupportPerm σ hσ C) fun i ↦ Subtype.ext <| by
      rw [coe_cycleWeightEquiv_apply, b.coe_componentCycleWeightBasis_apply,
        b.coe_componentCycleWeightBasis_apply, b.coe_componentCycleSupportPerm_apply,
        Hom.root_weightMap_apply P P _ σ.toHom]).map (componentCycleFixedEquiv (P := P) σ C)

@[simp] theorem componentCycleSimpleOrbitBasis_repr (y : P.componentCycleFixedSubmodule σ C)
    (i : {i : b.support // SameCycle σ.componentEquiv C (P.componentOf (i : ι))}) :
    (b.componentCycleSimpleOrbitBasis σ hσ C).repr y ⟦i⟧ =
      b.toWeightBasis.repr (y.val : M) i.val := by simp [componentCycleSimpleOrbitBasis]

open Classical in
/-- Each vector of `componentCycleSimpleOrbitBasis` is the sum of the simple roots in its
`σ`-orbit. -/
theorem coe_componentCycleSimpleOrbitBasis_eq_sum
    [Fintype {i : b.support // SameCycle σ.componentEquiv C (P.componentOf (i : ι))}]
    (O : Quotient (SameCycle.setoid (b.componentCycleSupportPerm σ hσ C))) :
    ((b.componentCycleSimpleOrbitBasis σ hσ C O : LinearMap.fixedSubmodule σ.weightMap) : M) =
      ∑ j ∈ Finset.univ.filter (fun j ↦ (⟦j⟧ : Quotient _) = O), P.root (j.val : ι) := by
  let := Fintype.ofFinite
    {i : b.support // SameCycle σ.componentEquiv C (P.componentOf (i : ι))}
  rw [componentCycleSimpleOrbitBasis, Module.Basis.map_apply,
    coe_componentCycleFixedEquiv_apply, Perm.coe_basisPermFixedBasis_apply, Submodule.coe_sum]
  exact Finset.sum_congr (by ext; simp) fun j _ ↦ b.coe_componentCycleWeightBasis_apply σ C j

/-- Each vector of `componentCycleSimpleOrbitBasis` is the `σ`-orbit sum of its representative. -/
theorem coe_componentCycleSimpleOrbitBasis_apply [Finite ι]
    (O : Quotient (SameCycle.setoid (b.componentCycleSupportPerm σ hσ C))) :
    ((b.componentCycleSimpleOrbitBasis σ hσ C O : LinearMap.fixedSubmodule σ.weightMap) : M) =
      P.orbitSum σ (O.out.val : ι) := by
  classical
  let := Fintype.ofFinite
    {i : b.support // SameCycle σ.componentEquiv C (P.componentOf (i : ι))}
  rw [b.coe_componentCycleSimpleOrbitBasis_eq_sum, P.orbitSum_eq_sum_range]
  convert Perm.sum_filter_quotient_eq_sum_range (b.componentCycleSupportPerm σ hσ C)
    (fun j ↦ (j.val : ι)) (Subtype.val_injective.comp Subtype.val_injective) σ.indexEquiv
    (fun j ↦ b.coe_componentCycleSupportPerm_apply σ hσ C j) P.root O

end CycleOrbit

end CycleBasis

section ReturnSimpleOrbitBasis

variable {ι K M N : Type*} [Field K] [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  {P : RootPairing ι K M N} [Finite ι] [P.IsRootSystem] (b : P.Base)

/-- **The return map is based.** The return map of a component under an automorphism permuting the
simple roots of `b` permutes the simple roots of the base of the component. -/
theorem indexEquiv_componentReturn_mem_support {σ : P.Aut} {C : P.Component}
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support) {i : C.supp}
    (hi : i ∈ (b.componentBase C).support) :
    (σ.componentReturn C).indexEquiv i ∈ (b.componentBase C).support := by
  rw [mem_support_componentBase] at hi ⊢
  rw [Equiv.coe_componentReturn_indexEquiv_apply]
  exact (P.mem_support_iff_of_mem_orbitIndices hσ
    (mem_orbitIndices_iff_exists_pow.mpr ⟨_, rfl⟩)).mpr hi

variable (σ : P.Aut) (hσ : ∀ j ∈ b.support, σ.indexEquiv j ∈ b.support) (C : P.Component)

include hσ in
/-- A base-preserving automorphism induces a return map on `C` that stabilizes the simple roots of
`b.componentBase C`. -/
theorem mem_support_componentReturn_indexEquiv_iff (i : C.supp) :
    (σ.componentReturn C).indexEquiv i ∈ (b.componentBase C).support ↔
      i ∈ (b.componentBase C).support :=
  (b.componentBase C).mem_support_indexEquiv_iff
    (fun _ hj ↦ b.indexEquiv_componentReturn_mem_support hσ hj) i

/-- `componentReturnSupportEquiv` conjugates `componentReturnSupportPerm` to the support
permutation of `σ.componentReturn C` on `b.componentBase C`. -/
theorem componentReturnSupportEquiv_supportPerm :
    (b.componentBase C).supportPerm
        (fun _ hj ↦ b.indexEquiv_componentReturn_mem_support hσ hj) =
      (b.componentReturnSupportEquiv C).permCongr (b.componentReturnSupportPerm σ hσ C) := by
  ext j; simp [Equiv.coe_componentReturn_indexEquiv_apply]

/-- Bijection between `(σ ^ c)`-simple-root orbits in `C` and simple-root orbits of
`σ.componentReturn C` on `b.componentBase C`. -/
noncomputable def componentReturnBaseOrbitEquiv :
    Quotient (SameCycle.setoid (b.componentReturnSupportPerm σ hσ C)) ≃
      Quotient (SameCycle.setoid ((b.componentBase C).supportPerm
        (fun _ hj ↦ b.indexEquiv_componentReturn_mem_support hσ hj))) :=
  _root_.Equiv.sameCycleQuotientCongr (b.componentReturnSupportEquiv C)
    (b.componentReturnSupportEquiv_supportPerm σ hσ C)

@[simp] theorem componentReturnBaseOrbitEquiv_mk
    (i : {i : b.support // P.componentOf (i : ι) = C}) :
    b.componentReturnBaseOrbitEquiv σ hσ C ⟦i⟧ = ⟦b.componentReturnSupportEquiv C i⟧ := by
  simp [componentReturnBaseOrbitEquiv]

private noncomputable def componentReturnFixedEquiv :
    (σ.componentReturn C).weightEquiv.toLinearMap.fixedSubmodule ≃ₗ[K]
      LinearMap.fixedSubmodule (σ.componentReturn C).toHom.weightMap :=
  LinearEquiv.ofEq _ _
    (congrArg LinearMap.fixedSubmodule (LinearMap.ext (σ.componentReturn C).weightEquiv_apply))

@[simp] private theorem coe_componentReturnFixedEquiv_apply
    (z : (σ.componentReturn C).weightEquiv.toLinearMap.fixedSubmodule) :
    (componentReturnFixedEquiv (P := P) σ C z : P.componentSpace C) = z.val := (rfl)

@[simp] private theorem coe_componentReturnFixedEquiv_symm_apply
    (u : LinearMap.fixedSubmodule (σ.componentReturn C).toHom.weightMap) :
    ((componentReturnFixedEquiv (P := P) σ C).symm u).val = u.val := (rfl)

/-- **The simple-orbit `K`-basis of the return fixed space**
`LinearMap.fixedSubmodule (σ.componentReturn C).toHom.weightMap`. -/
noncomputable def componentReturnSimpleOrbitBasis :
    Module.Basis (Quotient (SameCycle.setoid (b.componentReturnSupportPerm σ hσ C))) K
      (LinearMap.fixedSubmodule (σ.componentReturn C).toHom.weightMap) :=
  letI := Fintype.ofFinite {i : b.support // P.componentOf (i : ι) = C}
  (Perm.basisPermFixedBasis (b.componentWeightBasis C) (σ.componentReturn C).weightEquiv
    (b.componentReturnSupportPerm σ hσ C) fun i ↦ Subtype.ext <| by
      rw [Equiv.weightEquiv_apply, Equiv.coe_componentReturn_weightMap_apply,
        b.coe_componentWeightBasis_apply, b.coe_componentWeightBasis_apply,
        b.coe_componentReturnSupportPerm_apply, ← σ.indexEquiv_pow,
        Hom.root_weightMap_apply P P _ (σ ^ _).toHom]).map
    (componentReturnFixedEquiv (P := P) σ C)

@[simp] theorem componentReturnSimpleOrbitBasis_repr
    (u : LinearMap.fixedSubmodule (σ.componentReturn C).toHom.weightMap)
    (i : {i : b.support // P.componentOf (i : ι) = C}) :
    (b.componentReturnSimpleOrbitBasis σ hσ C).repr u ⟦i⟧ =
      b.toWeightBasis.repr (u : M) i.val := by simp [componentReturnSimpleOrbitBasis]

open Classical in
/-- Each vector of `componentReturnSimpleOrbitBasis` is the sum of the simple roots in its
`(σ ^ c)`-orbit. -/
theorem coe_componentReturnSimpleOrbitBasis_eq_sum
    [Fintype {i : b.support // P.componentOf (i : ι) = C}]
    (o : Quotient (SameCycle.setoid (b.componentReturnSupportPerm σ hσ C))) :
    ((b.componentReturnSimpleOrbitBasis σ hσ C o :
        LinearMap.fixedSubmodule (σ.componentReturn C).toHom.weightMap) : M) =
      ∑ j ∈ Finset.univ.filter (fun j ↦ (⟦j⟧ : Quotient _) = o), P.root (j.val : ι) := by
  let := Fintype.ofFinite {i : b.support // P.componentOf (i : ι) = C}
  rw [componentReturnSimpleOrbitBasis, Module.Basis.map_apply,
    coe_componentReturnFixedEquiv_apply, Perm.coe_basisPermFixedBasis_apply, Submodule.coe_sum]
  exact Finset.sum_congr (by ext; simp) fun j _ ↦ b.coe_componentWeightBasis_apply C j

/-- Each vector of `componentReturnSimpleOrbitBasis` is its representative's return orbit sum. -/
theorem coe_componentReturnSimpleOrbitBasis_apply
    (o : Quotient (SameCycle.setoid (b.componentReturnSupportPerm σ hσ C))) :
    ((b.componentReturnSimpleOrbitBasis σ hσ C o :
        LinearMap.fixedSubmodule (σ.componentReturn C).toHom.weightMap) : P.componentSpace C) =
      (P.componentPairing C).orbitSum (σ.componentReturn C)
        ⟨o.out.val, (C.mem_supp_iff _).mpr o.out.property⟩ := by
  classical
  let := Fintype.ofFinite {i : b.support // P.componentOf (i : ι) = C}
  apply Subtype.ext
  rw [b.coe_componentReturnSimpleOrbitBasis_eq_sum, (P.componentPairing C).orbitSum_eq_sum_range,
    Submodule.coe_sum]
  refine (Eq.trans (by
    convert Perm.sum_filter_quotient_eq_sum_range (b.componentReturnSupportPerm σ hσ C)
      (fun j ↦ (⟨j.val, (C.mem_supp_iff _).mpr j.property⟩ : C.supp))
      (fun _ _ h ↦ Subtype.ext (Subtype.ext (congrArg (Subtype.val : C.supp → ι) h)))
      (σ.componentReturn C).indexEquiv
      (fun j ↦ Subtype.ext (by
        rw [b.coe_componentReturnSupportPerm_apply, Equiv.coe_componentReturn_indexEquiv_apply]))
      (fun k ↦ P.root (k : ι)) o) ?_)
  exact Finset.sum_congr rfl fun r _ ↦ (P.coe_componentPairing_root C _).symm

/-- **Simple-orbit coordinates are preserved unchanged by `componentCycleDiag`.** -/
@[simp] theorem componentCycleSimpleOrbitBasis_repr_componentCycleDiag
    (u : LinearMap.fixedSubmodule (σ.componentReturn C).toHom.weightMap)
    (o : Quotient (SameCycle.setoid (b.componentReturnSupportPerm σ hσ C))) :
    (b.componentCycleSimpleOrbitBasis σ hσ C).repr (P.componentCycleDiag σ C u)
        (b.componentCycleSimpleOrbitEquiv σ hσ C o) =
      (b.componentReturnSimpleOrbitBasis σ hσ C).repr u o := by
  induction o using Quotient.ind with | _ i =>
  rw [b.componentCycleSimpleOrbitEquiv_mk, b.componentCycleSimpleOrbitBasis_repr,
    b.componentReturnSimpleOrbitBasis_repr, ← P.toWeightBasis_repr_componentProj_of_eq b i.property,
    P.componentProj_componentCycleDiag]

/-- **Diagonal transport carries the return simple-orbit basis to the cycle simple-orbit basis.** -/
@[simp] theorem componentCycleDiag_componentReturnSimpleOrbitBasis
    (o : Quotient (SameCycle.setoid (b.componentReturnSupportPerm σ hσ C))) :
    P.componentCycleDiag σ C (b.componentReturnSimpleOrbitBasis σ hσ C o) =
      b.componentCycleSimpleOrbitBasis σ hσ C (b.componentCycleSimpleOrbitEquiv σ hσ C o) := by
  apply (b.componentCycleSimpleOrbitBasis σ hσ C).repr.injective; ext O
  obtain ⟨o', rfl⟩ := (b.componentCycleSimpleOrbitEquiv σ hσ C).surjective O
  classical
  rw [b.componentCycleSimpleOrbitBasis_repr_componentCycleDiag, Module.Basis.repr_self,
    Module.Basis.repr_self, Finsupp.single_apply, Finsupp.single_apply]
  simp only [(b.componentCycleSimpleOrbitEquiv σ hσ C).apply_eq_iff_eq]

/-- `componentReturnSimpleOrbitBasis` agrees with `(b.componentBase C).fixedSubmoduleBasis` via
`b.componentReturnBaseOrbitEquiv`. -/
theorem componentReturnSimpleOrbitBasis_eq_fixedSubmoduleBasis
    (o : Quotient (SameCycle.setoid (b.componentReturnSupportPerm σ hσ C))) :
    b.componentReturnSimpleOrbitBasis σ hσ C o =
      (b.componentBase C).fixedSubmoduleBasis
        (fun _ hj ↦ b.indexEquiv_componentReturn_mem_support hσ hj)
        (b.componentReturnBaseOrbitEquiv σ hσ C o) := by
  induction o using Quotient.ind with | _ i =>
  apply Subtype.ext
  rw [b.componentReturnBaseOrbitEquiv_mk,
    (b.componentBase C).coe_fixedSubmoduleBasis_mk _ (b.componentReturnSupportEquiv C i),
    b.coe_componentReturnSimpleOrbitBasis_apply]
  have hsc : SameCycle (b.componentReturnSupportPerm σ hσ C)
      i (Quotient.mk (SameCycle.setoid (b.componentReturnSupportPerm σ hσ C)) i).out :=
    ((Perm.sameCycle_out_iff (b.componentReturnSupportPerm σ hσ C)).mpr rfl).symm
  obtain ⟨k, hk⟩ := hsc.exists_nat_pow_eq
  refine (P.componentPairing C).orbitSum_eq_of_mem
    ((P.componentPairing C).mem_orbitIndices_iff_exists_pow.mpr ⟨k, Subtype.ext ?_⟩)
  rw [Equiv.coe_componentReturn_indexEquiv_pow_apply, pow_mul]
  simpa [b.coe_componentReturnSupportPerm_pow] using congrArg (fun x ↦ (x.val : ι)) hk

omit C in
/-- Each vector of `componentCycleSimpleOrbitBasis` agrees in `M` with `b.fixedSubmoduleBasis`
via `componentCycleSigmaSimpleOrbitEquiv`. -/
theorem coe_componentCycleSimpleOrbitBasis_eq_fixedSubmoduleBasis
    (O : Quotient (SameCycle.setoid σ.componentEquiv))
    (o : Quotient (SameCycle.setoid (b.componentCycleSupportPerm σ hσ O.out))) :
    ((b.componentCycleSimpleOrbitBasis σ hσ O.out o : LinearMap.fixedSubmodule σ.weightMap) : M) =
      ((b.fixedSubmoduleBasis hσ (b.componentCycleSigmaSimpleOrbitEquiv σ hσ ⟨O, o⟩) :
          LinearMap.fixedSubmodule σ.weightMap) : M) := by
  induction o using Quotient.ind with | _ i =>
  rw [b.componentCycleSigmaSimpleOrbitEquiv_mk, b.coe_fixedSubmoduleBasis_mk hσ i.val,
    b.coe_componentCycleSimpleOrbitBasis_apply]
  have hsc : SameCycle (b.componentCycleSupportPerm σ hσ O.out)
      i (Quotient.mk (SameCycle.setoid (b.componentCycleSupportPerm σ hσ O.out)) i).out :=
    ((Perm.sameCycle_out_iff (b.componentCycleSupportPerm σ hσ O.out)).mpr rfl).symm
  obtain ⟨k, hk⟩ := hsc.exists_nat_pow_eq
  exact P.orbitSum_eq_of_mem (P.mem_orbitIndices_iff_exists_pow.mpr ⟨k, by
    simpa [b.coe_componentCycleSupportPerm_pow] using congrArg (fun x ↦ (x.val : ι)) hk⟩)

/-- A return fixed vector lies in `posRootCone P b` iff its return simple-orbit coordinates lie in
`ℕ`. -/
theorem mem_posRootCone_iff_forall_componentReturnSimpleOrbitBasis_repr
    (u : LinearMap.fixedSubmodule (σ.componentReturn C).toHom.weightMap) :
    (u : M) ∈ posRootCone P b ↔
      ∀ o, ∃ n : ℕ, (b.componentReturnSimpleOrbitBasis σ hσ C).repr u o = (n : K) := by
  have := Fintype.ofFinite (Quotient (SameCycle.setoid (b.componentReturnSupportPerm σ hσ C)))
  refine ⟨fun hu o ↦ ?_, fun h ↦ ?_⟩
  · classical
    obtain ⟨f, hf⟩ := (mem_posRootCone P b).mp hu
    refine ⟨f o.out.val, ?_⟩
    conv_lhs => rw [← Quotient.out_eq o]
    rw [b.componentReturnSimpleOrbitBasis_repr, hf, ← Finset.sum_coe_sort b.support]
    simp only [← Nat.cast_smul_eq_nsmul K, ← b.toWeightBasis_apply, map_sum, map_smul,
      Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul, Module.Basis.repr_self]
    rw [Finset.sum_eq_single o.out.val
      (fun _ _ hj ↦ by rw [Finsupp.single_eq_of_ne' hj, mul_zero]) (by simp)]
    simp
  · classical
    let := Fintype.ofFinite {i : b.support // P.componentOf (i : ι) = C}
    choose n hn using h
    have hsum : u = ∑ o, n o • b.componentReturnSimpleOrbitBasis σ hσ C o := by
      conv_lhs => rw [← (b.componentReturnSimpleOrbitBasis σ hσ C).sum_repr u]
      exact Finset.sum_congr rfl fun o _ ↦ by rw [hn o, Nat.cast_smul_eq_nsmul]
    rw [hsum, Submodule.coe_sum, Submodule.coe_sum]
    refine AddSubmonoid.sum_mem _ fun o _ ↦ AddSubmonoid.nsmul_mem _ ?_ _
    rw [b.coe_componentReturnSimpleOrbitBasis_eq_sum]
    exact AddSubmonoid.sum_mem _ fun j _ ↦ root_mem_posRootCone_of_mem_support P b j.val.property

end ReturnSimpleOrbitBasis

end Base

end RootPairing
