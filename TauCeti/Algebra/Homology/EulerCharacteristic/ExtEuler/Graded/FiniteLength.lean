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

* `TauCeti.isGradedEulerAdmissible_of_finite_of_forall_simple`: admissibility against a fixed
  target can be tested on finite-dimensional simple sources.
* `TauCeti.isGradedEulerAdmissible_of_finite_of_forall_simple_right`: admissibility from a fixed
  source can be tested on finite-dimensional simple targets.
* `TauCeti.isGradedEulerAdmissibleOn_gradedFiniteModules_iff`: every pair of finite graded modules
  is graded Euler-admissible exactly when every pair drawn from an exhaustive family of graded
  simples is.

## References

* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, Section 2.3.
* Charles A. Weibel, *An Introduction to Homological Algebra*, Sections 2.4--2.7.

The dimension inductions use `GradedModuleCat.exists_mono_cokernel_finrank_lt`; the extension
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
  classical
  induction hn : Module.finrank k X using Nat.strong_induction_on generalizing X with
  | _ n ih =>
    by_cases hX : IsZero X
    · exact IsGradedEulerAdmissible.of_isZero_left k e hX
    by_cases hs : Simple X
    · exact h X inferInstance hs
    obtain ⟨Z, i, hi, hZ, hQ, _, hdimZ, hdimQ⟩ :=
      X.exists_mono_cokernel_finrank_lt hX hs
    have : Module.Finite k Z := hZ
    have : Module.Finite k (GradedModuleCat.cokernelObj i) := hQ
    exact (ih _ (hn ▸ hdimZ) Z rfl).of_shortExact₂' (GradedModuleCat.shortExact_cokernelπ i)
      (ih _ (hn ▸ hdimQ) (GradedModuleCat.cokernelObj i) rfl)

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
  classical
  induction hn : Module.finrank k Y using Nat.strong_induction_on generalizing Y with
  | _ n ih =>
    by_cases hY : IsZero Y
    · exact IsGradedEulerAdmissible.of_isZero_right k e hY
    by_cases hs : Simple Y
    · exact h Y inferInstance hs
    obtain ⟨Z, i, hi, hZ, hQ, _, hdimZ, hdimQ⟩ := Y.exists_mono_cokernel_finrank_lt hY hs
    have : Module.Finite k Z := hZ
    have : Module.Finite k (GradedModuleCat.cokernelObj i) := hQ
    exact (ih _ (hn ▸ hdimZ) Z rfl).of_shortExact₂ (GradedModuleCat.shortExact_cokernelπ i)
      (ih _ (hn ▸ hdimQ) (GradedModuleCat.cokernelObj i) rfl)

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
  -- A simple finite graded module is a shift of a member of `S`.
  have hshift (T : GradedModuleCat.{uA} 𝒜) [Module.Finite k T] (hT : Simple T) :
      ∃ i d, Nonempty (T ≅ (S i).obj.shiftObj d) :=
    (isExhaustiveGradedSimpleFamily_iff S).1 hS
      ⟨T, gradedFiniteModules_iff.2 (Module.Finite.of_restrictScalars_finite k A T)⟩ hT
  refine ⟨fun X Y hX hY ↦ ?_⟩
  have : Module.Finite A X := gradedFiniteModules_iff.1 hX
  have : Module.Finite A Y := gradedFiniteModules_iff.1 hY
  have : Module.Finite k X := Module.Finite.trans A X
  have : Module.Finite k Y := Module.Finite.trans A Y
  -- Reduce the source to a shifted simple `(S i){d}`, then the target to a shifted `(S j){d'}`.
  refine isGradedEulerAdmissible_of_finite_of_forall_simple _ Y (fun T _ hT ↦ ?_) X
  obtain ⟨i, d, ⟨φ⟩⟩ := hshift T hT
  refine IsGradedEulerAdmissible.of_iso k (IsGradedEulerAdmissible.shiftObj ?_ d) φ.symm
    (Iso.refl Y)
  refine isGradedEulerAdmissible_of_finite_of_forall_simple_right _ _ (fun T' _ hT' ↦ ?_) Y
  obtain ⟨j, d', ⟨φ'⟩⟩ := hshift T' hT'
  exact ((h i j).shiftObjTarget d').of_iso k (Iso.refl _) φ'.symm

end Exhaustive

end TauCeti
