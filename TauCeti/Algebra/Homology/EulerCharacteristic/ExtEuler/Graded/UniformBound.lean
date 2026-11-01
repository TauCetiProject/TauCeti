/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Graded.FiniteLength

/-!
# Uniform graded Ext bounds from simple modules

A cohomological bound on graded Ext can be uniform both in internal degree and in the pair of
objects. For finite modules it suffices to test such a bound on simple modules. For an exhaustive
family of graded simples up to shift, it suffices to test the chosen representatives: arbitrary
internal shifts do not change a cohomological bound.

In particular, pointwise graded Euler-admissibility on a finite exhaustive family gives one
cohomological bound for all finite graded modules. Finiteness of internal support remains a
separate condition; it is not asserted by the uniform-bound predicate.

## References

* Charles A. Weibel, *An Introduction to Homological Algebra*, Sections 2.4--2.7 and Chapter 4.
* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, Section 2.3.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

universe w v u uk uA

section Uniform

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C] {e : C ≌ C}

/-- One cohomological bound for all pairs in `P × Q` and all internal degrees. This does not
require finite-dimensional Ext or finite internal support. -/
structure IsGradedExtBoundedOn (e : C ≌ C) (P Q : ObjectProperty C) (N : ℕ) : Prop where
  /-- Every selected pair has the same cohomological bound. -/
  isGradedExtBoundedBy ⦃X Y : C⦄ (hX : P X) (hY : Q Y) :
    IsGradedExtBoundedBy.{w} e X Y N

/-- A uniform bound restricts to smaller object properties and may be raised. -/
theorem IsGradedExtBoundedOn.mono {P P' Q Q' : ObjectProperty C} {N M : ℕ}
    (h : IsGradedExtBoundedOn.{w} e P Q N) (hP : P' ≤ P) (hQ : Q' ≤ Q) (hNM : N ≤ M) :
    IsGradedExtBoundedOn.{w} e P' Q' M :=
  ⟨fun _ _ hX hY ↦ (h.isGradedExtBoundedBy (hP _ hX) (hQ _ hY)).mono hNM⟩

/-- A uniform cohomological bound and pointwise finite internal support give graded
Euler-admissibility. -/
theorem IsGradedExtBoundedOn.isGradedEulerAdmissibleOn
    {k : Type*} [Field k] [Linear k C] {P Q : ObjectProperty C} {N : ℕ}
    (h : IsGradedExtBoundedOn.{w} e P Q N)
    (hfin : ∀ ⦃X Y : C⦄, P X → Q Y → IsGradedExtInternallyFinite.{w} k e X Y) :
    IsGradedEulerAdmissibleOn.{w} (k := k) (e := e) P Q :=
  ⟨fun _ _ hX hY ↦ ⟨hfin hX hY, (h.isGradedExtBoundedBy hX hY).isGradedExtBounded⟩⟩

end Uniform

variable {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A}

section Simple

variable [HasExt.{w} (GradedModuleCat.{v} 𝒜)]

/-- A fixed bound against all finite-dimensional simple graded sources bounds every
finite-dimensional graded source, without increasing the bound. -/
theorem isGradedExtBoundedBy_of_finite_of_forall_simple
    (e : GradedModuleCat.{v} 𝒜 ≌ GradedModuleCat.{v} 𝒜)
    (Y : GradedModuleCat.{v} 𝒜) (N : ℕ)
    (h : ∀ S : GradedModuleCat.{v} 𝒜, Module.Finite k S → Simple S →
      IsGradedExtBoundedBy.{w} e S Y N)
    (X : GradedModuleCat.{v} 𝒜) [Module.Finite k X] :
    IsGradedExtBoundedBy.{w} e X Y N := by
  classical
  induction hn : Module.finrank k X using Nat.strong_induction_on generalizing X with
  | _ n ih =>
    by_cases hX : IsZero X
    · exact ⟨fun n _ j ↦ subsingleton_ext_of_isZero_left hX _ n⟩
    by_cases hs : Simple X
    · exact h X inferInstance hs
    obtain ⟨Z, i, hi, hZ, hQ, _, hdimZ, hdimQ⟩ :=
      X.exists_mono_cokernel_finrank_lt hX hs
    have : Module.Finite k Z := hZ
    have : Module.Finite k (GradedModuleCat.cokernelObj i) := hQ
    simpa only [max_self] using (ih _ (hn ▸ hdimZ) Z rfl).of_shortExact₂'
      (GradedModuleCat.shortExact_cokernelπ i)
      (ih _ (hn ▸ hdimQ) (GradedModuleCat.cokernelObj i) rfl)

/-- A fixed bound against all finite-dimensional simple graded targets bounds every
finite-dimensional graded target, without increasing the bound. -/
theorem isGradedExtBoundedBy_of_finite_of_forall_simple_right
    (e : GradedModuleCat.{v} 𝒜 ≌ GradedModuleCat.{v} 𝒜)
    (X : GradedModuleCat.{v} 𝒜) (N : ℕ)
    (h : ∀ T : GradedModuleCat.{v} 𝒜, Module.Finite k T → Simple T →
      IsGradedExtBoundedBy.{w} e X T N)
    (Y : GradedModuleCat.{v} 𝒜) [Module.Finite k Y] :
    IsGradedExtBoundedBy.{w} e X Y N := by
  classical
  induction hn : Module.finrank k Y using Nat.strong_induction_on generalizing Y with
  | _ n ih =>
    by_cases hY : IsZero Y
    · exact ⟨fun n _ j ↦ subsingleton_ext_of_isZero_right X ((e ^ j).functor.map_isZero hY) n⟩
    by_cases hs : Simple Y
    · exact h Y inferInstance hs
    obtain ⟨Z, i, hi, hZ, hQ, _, hdimZ, hdimQ⟩ :=
      Y.exists_mono_cokernel_finrank_lt hY hs
    have : Module.Finite k Z := hZ
    have : Module.Finite k (GradedModuleCat.cokernelObj i) := hQ
    simpa only [max_self] using (ih _ (hn ▸ hdimZ) Z rfl).of_shortExact₂
      (GradedModuleCat.shortExact_cokernelπ i)
      (ih _ (hn ▸ hdimQ) (GradedModuleCat.cokernelObj i) rfl)

end Simple

section Exhaustive

variable {I : Type*} [Module.Finite k A] [HasExt.{w} (GradedModuleCat.{uA} 𝒜)]

/-- A uniform cohomological bound on finite graded modules is detected on any exhaustive
family of graded simples up to shift, with the very same bound. -/
theorem isGradedExtBoundedOn_gradedFiniteModules_iff
    {S : I → (gradedFiniteModules 𝒜).FullSubcategory}
    (hS : IsExhaustiveGradedSimpleFamily S) (N : ℕ) :
    IsGradedExtBoundedOn.{w} (GradedModuleCat.shift 𝒜)
        (gradedFiniteModules 𝒜) (gradedFiniteModules 𝒜) N ↔
      ∀ i j, IsGradedExtBoundedBy.{w} (GradedModuleCat.shift 𝒜) (S i).obj (S j).obj N := by
  refine ⟨fun h i j ↦ h.isGradedExtBoundedBy (S i).property (S j).property, fun h ↦ ?_⟩
  have hshift (T : GradedModuleCat.{uA} 𝒜) [Module.Finite k T] (hT : Simple T) :
      ∃ i d, Nonempty (T ≅ (S i).obj.shiftObj d) :=
    (isExhaustiveGradedSimpleFamily_iff S).1 hS
      ⟨T, gradedFiniteModules_iff.2 (Module.Finite.of_restrictScalars_finite k A T)⟩ hT
  refine ⟨fun X Y hX hY ↦ ?_⟩
  have : Module.Finite A X := gradedFiniteModules_iff.1 hX
  have : Module.Finite A Y := gradedFiniteModules_iff.1 hY
  have : Module.Finite k X := Module.Finite.trans A X
  have : Module.Finite k Y := Module.Finite.trans A Y
  refine isGradedExtBoundedBy_of_finite_of_forall_simple _ Y N (fun T _ hT ↦ ?_) X
  obtain ⟨i, d, ⟨φ⟩⟩ := hshift T hT
  refine IsGradedExtBoundedBy.of_iso (IsGradedExtBoundedBy.shiftObj ?_ d) φ.symm (Iso.refl Y)
  refine isGradedExtBoundedBy_of_finite_of_forall_simple_right _ _ N (fun T' _ hT' ↦ ?_) Y
  obtain ⟨j, d', ⟨φ'⟩⟩ := hshift T' hT'
  exact ((h i j).shiftObjTarget d').of_iso (Iso.refl _) φ'.symm

/-- Pointwise eventual graded Ext-vanishing on a finite exhaustive family of simples supplies
one cohomological bound for every pair of finite graded modules and every internal degree. -/
theorem exists_isGradedExtBoundedOn_of_forall_simple [Finite I]
    {S : I → (gradedFiniteModules 𝒜).FullSubcategory}
    (hS : IsExhaustiveGradedSimpleFamily S)
    (h : ∀ i j, IsGradedExtBounded.{w} (GradedModuleCat.shift 𝒜) (S i).obj (S j).obj) :
    ∃ N, IsGradedExtBoundedOn.{w} (GradedModuleCat.shift 𝒜)
      (gradedFiniteModules 𝒜) (gradedFiniteModules 𝒜) N := by
  obtain ⟨N, hN⟩ := exists_forall_isGradedExtBoundedBy
    (X := fun p : I × I ↦ (S p.1).obj) (Y := fun p : I × I ↦ (S p.2).obj)
    (fun p ↦ h p.1 p.2)
  exact ⟨N, (isGradedExtBoundedOn_gradedFiniteModules_iff hS N).2 (fun i j ↦ hN (i, j))⟩

end Exhaustive

end TauCeti
