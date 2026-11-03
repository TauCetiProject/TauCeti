/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.RingTheory.HopkinsLevitzki
public import TauCeti.Algebra.Category.ModuleCat.FiniteLength
public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Basic

/-!
# Uniform Ext bounds from simple modules

A fixed vanishing bound for Ext propagates through a composition series without increasing.
Consequently, over an Artinian ring a uniform bound on pairs of finitely generated modules is
equivalent to the same bound on pairs of simple modules. This is a uniform assertion, unlike
pointwise eventual vanishing, and requires no finiteness of the Ext groups themselves.

## References

* Charles A. Weibel, *An Introduction to Homological Algebra*, Sections 2.4--2.7 and Chapter 4.
-/

public section

namespace ModuleCat

open TauCeti CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat

universe u

variable {R : Type u} [Ring R]

/-- A common bound against all simple sources bounds Ext from any finite-length source,
without increasing the bound. -/
theorem isExtBoundedBy_of_isFiniteLength (Y : ModuleCat.{u} R) (N : ℕ)
    (h : ∀ S : ModuleCat.{u} R, IsSimpleModule R S → IsExtBoundedBy.{u} S Y N)
    (X : ModuleCat.{u} R) (hX : IsFiniteLength R X) : IsExtBoundedBy.{u} X Y N := by
  refine X.prop_of_isFiniteLength hX (fun M ↦ IsExtBoundedBy.{u} M Y N)
    (fun M hM ↦ ⟨fun n _ ↦ subsingleton_ext_of_isZero_left hM Y n⟩) h ?_
  intro S hS h₁ h₃
  simpa only [max_self] using h₁.of_shortExact₂' hS h₃

/-- A common bound against all simple targets bounds Ext into any finite-length target,
without increasing the bound. -/
theorem isExtBoundedBy_of_isFiniteLength_right (X : ModuleCat.{u} R) (N : ℕ)
    (h : ∀ T : ModuleCat.{u} R, IsSimpleModule R T → IsExtBoundedBy.{u} X T N)
    (Y : ModuleCat.{u} R) (hY : IsFiniteLength R Y) : IsExtBoundedBy.{u} X Y N := by
  refine Y.prop_of_isFiniteLength hY (fun M ↦ IsExtBoundedBy.{u} X M N)
    (fun M hM ↦ ⟨fun n _ ↦ subsingleton_ext_of_isZero_right X hM n⟩) h ?_
  intro S hS h₁ h₃
  simpa only [max_self] using h₁.of_shortExact₂ hS h₃

end ModuleCat

namespace TauCeti

open CategoryTheory

open scoped ModuleCat

universe u

variable {R : Type u} [Ring R] [IsArtinianRing R]

/-- Over an Artinian ring, a uniform Ext bound on finitely generated modules is detected on
simple pairs. No finite-dimensionality of Ext is assumed or concluded. -/
theorem isExtBoundedOn_isFG_iff_forall_isSimpleModule (N : ℕ) :
    IsExtBoundedOn.{u} (ModuleCat.isFG R) (ModuleCat.isFG R) N ↔
      ∀ S T : ModuleCat.{u} R, IsSimpleModule R S → IsSimpleModule R T →
        IsExtBoundedBy.{u} S T N := by
  refine ⟨fun h S T hS hT ↦ ?_, fun h ↦ ⟨fun X Y hX hY ↦ ?_⟩⟩
  · have := hS
    have := hT
    exact h.isExtBoundedBy ((ModuleCat.isFG_iff S).2 inferInstance)
      ((ModuleCat.isFG_iff T).2 inferInstance)
  · have : Module.Finite R X := (ModuleCat.isFG_iff X).1 hX
    have : Module.Finite R Y := (ModuleCat.isFG_iff Y).1 hY
    have hlenX : IsFiniteLength R X :=
      isFiniteLength_iff_isNoetherian_isArtinian.2 ⟨inferInstance, inferInstance⟩
    have hlenY : IsFiniteLength R Y :=
      isFiniteLength_iff_isNoetherian_isArtinian.2 ⟨inferInstance, inferInstance⟩
    exact Y.isExtBoundedBy_of_isFiniteLength N (fun S hS ↦
      S.isExtBoundedBy_of_isFiniteLength_right N (fun T hT ↦ h S T hS hT) Y hlenY) X hlenX

end TauCeti
