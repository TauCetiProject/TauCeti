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
  refine X.finite_induction (fun M ↦ IsGradedExtBoundedBy.{w} e M Y N)
    (fun _ hM ↦ ⟨fun n _ _ ↦ subsingleton_ext_of_isZero_left hM _ n⟩) h ?_
  intro S _ _ hS h₁ h₃
  simpa only [max_self] using h₁.of_shortExact₂' hS h₃

/-- A fixed bound against all finite-dimensional simple graded targets bounds every
finite-dimensional graded target, without increasing the bound. -/
theorem isGradedExtBoundedBy_of_finite_of_forall_simple_right
    (e : GradedModuleCat.{v} 𝒜 ≌ GradedModuleCat.{v} 𝒜)
    (X : GradedModuleCat.{v} 𝒜) (N : ℕ)
    (h : ∀ T : GradedModuleCat.{v} 𝒜, Module.Finite k T → Simple T →
      IsGradedExtBoundedBy.{w} e X T N)
    (Y : GradedModuleCat.{v} 𝒜) [Module.Finite k Y] :
    IsGradedExtBoundedBy.{w} e X Y N := by
  refine Y.finite_induction (fun M ↦ IsGradedExtBoundedBy.{w} e X M N)
    (fun _ hM ↦ ⟨fun n _ j ↦ subsingleton_ext_of_isZero_right X
      ((e ^ j).functor.map_isZero hM) n⟩) h ?_
  intro S _ _ hS h₁ h₃
  simpa only [max_self] using h₁.of_shortExact₂ hS h₃

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
  refine ⟨fun X Y hX hY ↦ hS.prop_on_pairs
    (fun X Y ↦ IsGradedExtBoundedBy.{w} (GradedModuleCat.shift 𝒜) X Y N)
    (fun h i j ↦ h.of_iso i j) (fun h d ↦ h.shiftObj d)
    (fun h d ↦ h.shiftObjTarget d) ?_ ?_ h hX hY⟩
  · intro Y h X hX
    have := hX
    exact isGradedExtBoundedBy_of_finite_of_forall_simple _ Y N h X
  · intro X h Y hY
    have := hY
    exact isGradedExtBoundedBy_of_finite_of_forall_simple_right _ X N h Y

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
