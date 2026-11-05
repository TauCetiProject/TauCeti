/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.FiniteLength
public import TauCeti.Algebra.Category.GradedModuleCat.SimpleFamily
public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Graded.Shift

/-!
# Graded Euler-admissibility from simple modules

For a fixed target, graded Euler-admissibility of finite-dimensional sources can be tested on
simple graded modules, and dually for a fixed source it can be tested on simple targets. Both
internal finiteness and eventual cohomological vanishing propagate through graded composition
series. The algebra need not itself be finite-dimensional for these two criteria.

Together with the shift-admissibility results in
`TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Graded.Shift`, they let an exhaustive family
of simples up to shift supply the finiteness data for a q-Euler form: over a finite-dimensional
graded algebra, every pair of finite graded modules is graded Euler-admissible exactly when every
pair of members of the family is.

## Main results

* `TauCeti.isGradedEulerAdmissible_of_finite_of_forall_simple` and
  `TauCeti.isSlicewiseEulerAdmissible_of_finite_of_forall_simple`: graded and slicewise
  admissibility against a fixed target can be tested on finite-dimensional simple sources.
* `TauCeti.isGradedEulerAdmissible_of_finite_of_forall_simple_right` and
  `TauCeti.isSlicewiseEulerAdmissible_of_finite_of_forall_simple_right`: graded and slicewise
  admissibility from a fixed source can be tested on finite-dimensional simple targets.
* `TauCeti.isGradedEulerAdmissibleOn_gradedFiniteModules_iff`: every pair of finite graded modules
  is graded Euler-admissible exactly when every pair drawn from an exhaustive family of graded
  simples is.

## References

* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, Section 2.3.
* Charles A. Weibel, *An Introduction to Homological Algebra*, Sections 2.4--2.7.

The composition-series inductions use `GradedModuleCat.finite_induction`; the extension
steps use `IsGradedEulerAdmissible.of_shortExact₂'` and `IsGradedEulerAdmissible.of_shortExact₂`.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe w uk uA v

variable {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A}

section Simple

variable [HasExt.{w} (GradedModuleCat.{v} 𝒜)]

/-- Admissibility against every finite-dimensional simple source implies admissibility against
all finite-dimensional graded sources, for any chosen internal-shift autoequivalence. -/
theorem isGradedEulerAdmissible_of_finite_of_forall_simple
    (e : GradedModuleCat.{v} 𝒜 ≌ GradedModuleCat.{v} 𝒜) (Y : GradedModuleCat.{v} 𝒜)
    (h : ∀ S : GradedModuleCat.{v} 𝒜, Module.Finite k S → Simple S →
      IsGradedEulerAdmissible.{w} k e S Y)
    (X : GradedModuleCat.{v} 𝒜) [Module.Finite k X] :
    IsGradedEulerAdmissible.{w} k e X Y := by
  exact X.finite_induction (fun M ↦ IsGradedEulerAdmissible.{w} k e M Y)
    (fun _ hM ↦ IsGradedEulerAdmissible.of_isZero_left k e hM) h
    (fun hS h₁ h₃ ↦ h₁.of_shortExact₂' hS h₃)

/-- Admissibility from a fixed source against every finite-dimensional simple target implies
admissibility against all finite-dimensional graded targets, for any chosen internal-shift
autoequivalence. This is the target counterpart of
`TauCeti.isGradedEulerAdmissible_of_finite_of_forall_simple`. -/
theorem isGradedEulerAdmissible_of_finite_of_forall_simple_right
    (e : GradedModuleCat.{v} 𝒜 ≌ GradedModuleCat.{v} 𝒜) (X : GradedModuleCat.{v} 𝒜)
    (h : ∀ T : GradedModuleCat.{v} 𝒜, Module.Finite k T → Simple T →
      IsGradedEulerAdmissible.{w} k e X T)
    (Y : GradedModuleCat.{v} 𝒜) [Module.Finite k Y] :
    IsGradedEulerAdmissible.{w} k e X Y := by
  exact Y.finite_induction (fun M ↦ IsGradedEulerAdmissible.{w} k e X M)
    (fun _ hM ↦ IsGradedEulerAdmissible.of_isZero_right k e hM) h
    (fun hS h₁ h₃ ↦ h₁.of_shortExact₂ hS h₃)

/-- Slicewise Euler-admissibility against every finite-dimensional simple source implies slicewise
Euler-admissibility against all finite-dimensional graded sources, for any chosen internal-shift
autoequivalence. -/
theorem isSlicewiseEulerAdmissible_of_finite_of_forall_simple
    (e : GradedModuleCat.{v} 𝒜 ≌ GradedModuleCat.{v} 𝒜) (Y : GradedModuleCat.{v} 𝒜)
    (h : ∀ S : GradedModuleCat.{v} 𝒜, Module.Finite k S → Simple S →
      IsSlicewiseEulerAdmissible.{w} k e S Y)
    (X : GradedModuleCat.{v} 𝒜) [Module.Finite k X] :
    IsSlicewiseEulerAdmissible.{w} k e X Y :=
  X.finite_induction (fun M ↦ IsSlicewiseEulerAdmissible.{w} k e M Y)
    (fun _ hM ↦ IsSlicewiseEulerAdmissible.of_isZero_left k e hM) h
    (fun hS h₁ h₃ ↦ h₁.of_shortExact₂' hS h₃)

/-- Slicewise Euler-admissibility from a fixed source against every finite-dimensional simple
target implies slicewise Euler-admissibility against all finite-dimensional graded targets, for any
chosen internal-shift autoequivalence. This is the target counterpart of
`TauCeti.isSlicewiseEulerAdmissible_of_finite_of_forall_simple`. -/
theorem isSlicewiseEulerAdmissible_of_finite_of_forall_simple_right
    (e : GradedModuleCat.{v} 𝒜 ≌ GradedModuleCat.{v} 𝒜) (X : GradedModuleCat.{v} 𝒜)
    (h : ∀ T : GradedModuleCat.{v} 𝒜, Module.Finite k T → Simple T →
      IsSlicewiseEulerAdmissible.{w} k e X T)
    (Y : GradedModuleCat.{v} 𝒜) [Module.Finite k Y] :
    IsSlicewiseEulerAdmissible.{w} k e X Y :=
  Y.finite_induction (fun M ↦ IsSlicewiseEulerAdmissible.{w} k e X M)
    (fun _ hM ↦ IsSlicewiseEulerAdmissible.of_isZero_right k e hM) h
    (fun hS h₁ h₃ ↦ h₁.of_shortExact₂ hS h₃)

end Simple

/-! ### Exhaustive families of graded simples -/

section Exhaustive

variable {I : Type*} [Module.Finite k A] [HasExt.{w} (GradedModuleCat.{uA} 𝒜)]

/-- **Graded Euler-admissibility of finite graded modules is decided on simples.** Over a
finite-dimensional graded algebra, let `S` be an exhaustive family of graded simples up to
internal shift. Every pair of finite graded modules is graded Euler-admissible exactly when every
pair `(S i, S j)` is. -/
theorem isGradedEulerAdmissibleOn_gradedFiniteModules_iff
    {S : I → (gradedFiniteModules 𝒜).FullSubcategory} (hS : IsExhaustiveGradedSimpleFamily S) :
    IsGradedEulerAdmissibleOn.{w} (k := k) (e := GradedModuleCat.shift 𝒜)
        (gradedFiniteModules 𝒜) (gradedFiniteModules 𝒜) ↔
      ∀ i j, IsGradedEulerAdmissible.{w} k (GradedModuleCat.shift 𝒜) (S i).obj (S j).obj := by
  refine ⟨fun h i j ↦ h.isGradedEulerAdmissible (S i).property (S j).property, fun h ↦ ?_⟩
  refine ⟨fun X Y hX hY ↦ hS.prop_on_pairs
    (IsGradedEulerAdmissible.{w} k (GradedModuleCat.shift 𝒜))
    (fun h i j ↦ h.of_iso k i j) (fun h d ↦ h.shiftObj d)
    (fun h d ↦ h.shiftObjTarget d) ?_ ?_ h hX hY⟩
  · intro Y h X hX
    have := hX
    exact isGradedEulerAdmissible_of_finite_of_forall_simple _ Y h X
  · intro X h Y hY
    have := hY
    exact isGradedEulerAdmissible_of_finite_of_forall_simple_right _ X h Y

end Exhaustive

end TauCeti
