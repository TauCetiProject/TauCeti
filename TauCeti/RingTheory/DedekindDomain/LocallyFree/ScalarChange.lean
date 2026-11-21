/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DedekindDomain.LocallyFree.ClassGroup
public import TauCeti.LinearAlgebra.TensorProduct.Balanced.CentralBaseChange

/-!
# Extension of locally free lattices

Extension of scalars along a morphism `Λ →ₐ[A] Γ` of algebras over a Dedekind domain preserves
local freeness and its rank, provided `Γ` is finite over `A`. At each prime, balanced extension
commutes with central completion, and extending a completed free basis gives a free basis of the
same rank over the completed destination algebra.

Consequently scalar extension sends the locally free class group into that of the destination.
This gives the class-group map for an overorder and identifies its kernel with the kernel group.

## References

* A. Fröhlich, *Arithmetic and Galois module structure for tame extensions*, Appendix VI,
  Proposition 2, and Appendix VII, Proposition 1.
-/

public section

open scoped TensorProduct

attribute [local instance low] TauCeti.CentralBaseChange.module
  TauCeti.BalancedExtension.moduleBase

namespace TauCeti.LocallyFree

variable {A : Type*} [CommRing A] [IsDedekindDomain A] {K : Type*} [Field K] [Algebra A K]
  [IsFractionRing A K] {Λ Γ : Type*} [Ring Λ] [Ring Γ] [Algebra A Λ] [Algebra A Γ]
  {M : Type*} [AddCommGroup M] [Module A M] [Module Λ M] [IsScalarTower A Λ M] {n : ℕ}

/-- Extension along a morphism of algebras finite over the central Dedekind base preserves
locally free lattices and their rank. Only the destination algebra needs to be finite. -/
theorem IsLocallyFreeOfRank.extendScalars [Module.Finite A Γ]
    (h : IsLocallyFreeOfRank A K Λ M n) (f : Λ →ₐ[A] Γ)
    [Module A (BalancedExtension (RingHomClass.toRingHom f) M)]
    [IsScalarTower A Γ (BalancedExtension (RingHomClass.toRingHom f) M)] :
    IsLocallyFreeOfRank A K Γ (BalancedExtension (RingHomClass.toRingHom f) M) n where
  finite := by
    have := h.finite
    have := Module.Finite.of_restrictScalars_finite A Λ M
    exact Module.Finite.trans Γ (BalancedExtension (RingHomClass.toRingHom f) M)
  nonempty_linearEquiv v := by
    let S := v.adicCompletionIntegers K
    let g := (RingHomClass.toRingHom (Algebra.TensorProduct.map (AlgHom.id A S) f))
    exact ⟨(BalancedExtension.baseChangeEquiv A S Λ M f).symm.trans <|
      (BalancedExtension.congr g (h.nonempty_linearEquiv v).some).trans <|
        (BalancedExtension.congr g (CentralBaseChange.piRight A S Λ (Fin n))).trans <|
          (BalancedExtension.piScalarRight g (Fin n)).trans
            (CentralBaseChange.piRight A S Γ (Fin n)).symm⟩

section ClassGroup

universe u

variable {Λ Γ : Type u} [Ring Λ] [Ring Γ] [Algebra A Λ] [Algebra A Γ]
  [Module.Finite A Γ] (f : Λ →ₐ[A] Γ)

/-- Scalar extension sends the locally free class subgroup into the destination subgroup. -/
theorem classGroupK0Map_mem_classGroup (x : classGroup A K Λ) :
    classGroupK0Map A K (RingHomClass.toRingHom f) x ∈ classGroup A K Γ := by
  classical
  by_cases hA : IsField A
  · have hx : x = 0 := Subtype.ext (by simpa [classGroup_eq_bot K Λ hA] using x.property)
    simp [hx]
  have hle : classGroup A K Λ ≤ (classGroup A K Γ).comap
      (SplitK0.map.{u, u} (RingHomClass.toRingHom f).finiteProjectiveModulesExtendScalars) := by
    rw [classGroup_le_iff hA]
    intro M _ _ _ _ _ _ n h
    rw [AddSubgroup.mem_comap]
    have hmap := classGroupK0Map_classOf (RingHomClass.toRingHom f) hA h
    rw [classGroupK0Map_apply] at hmap
    rw [hmap]
    exact classOf_mem_classGroup hA (h.extendScalars f)
  simpa only [classGroupK0Map_apply, AddSubgroup.mem_comap] using hle x.property

variable (A K) in
/-- Extension of scalars on locally free class groups, for a morphism of algebras whose
destination is finite over the central Dedekind base. This includes inclusions of orders. -/
noncomputable def classGroupMap : classGroup A K Λ →+ classGroup A K Γ :=
  (classGroupK0Map A K (RingHomClass.toRingHom f)).codRestrict (classGroup A K Γ)
    (classGroupK0Map_mem_classGroup f)

/-- The class-group map agrees with scalar extension in ambient projective `K₀`. -/
@[simp]
theorem coe_classGroupMap (x : classGroup A K Λ) :
    (classGroupMap A K f x : SplitK0.{u} (finiteProjectiveModules Γ).FullSubcategory) =
      classGroupK0Map A K (RingHomClass.toRingHom f) x := (rfl)

variable {M : Type u} [AddCommGroup M] [Module A M] [Module Λ M] [IsScalarTower A Λ M]
  [Module.Finite Λ M] [Module.Projective Λ M] {n : ℕ}

/-- Extension of scalars sends the reduced class of `M` to the reduced class of `Γ ⊗_Λ M`. -/
theorem classGroupMap_classOf (hA : ¬IsField A) (h : IsLocallyFreeOfRank A K Λ M n) :
    classGroupMap A K f ⟨FiniteProjectiveModules.classOf Λ M n, classOf_mem_classGroup hA h⟩ =
      ⟨FiniteProjectiveModules.classOf Γ (BalancedExtension (RingHomClass.toRingHom f) M) n,
        classOf_mem_classGroup hA (h.extendScalars f)⟩ :=
  Subtype.ext (classGroupK0Map_classOf (RingHomClass.toRingHom f) hA h)

/-- The kernel of the subgroup-valued scalar map is the kernel group, as computed in `K₀`. -/
@[simp]
theorem ker_classGroupMap :
    (classGroupMap A K f).ker = kernelGroup A K (RingHomClass.toRingHom f) := by
  ext x
  simp only [AddMonoidHom.mem_ker, ← ZeroMemClass.coe_eq_zero,
    coe_classGroupMap, mem_kernelGroup_iff, classGroupK0Map_apply]

end ClassGroup

end TauCeti.LocallyFree
