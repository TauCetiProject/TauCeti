/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Algebra.HolomorphicFunctionalCalculus.Basic
import Mathlib.Analysis.Calculus.DSlope

/-!
# Spectral mapping theorem for the holomorphic functional calculus

Let `a` be an element of a complex Banach algebra `A`. This file proves the spectral mapping
theorem `spectrum ℂ (holomorphicCalculus a g) = spectrum ℂ g` for every holomorphic germ `g` near
`spectrum ℂ a` (including the zero algebra, where both sides are empty), together with its
represented, open-domain, and unit-characterization corollaries.

## Main results

* `TauCeti.spectrum_holomorphicCalculus`: `spectrum ℂ (holomorphicCalculus a g) = spectrum ℂ g`.
* `TauCeti.spectrum_holomorphicCalculus_ofFun`, `TauCeti.spectrum_holomorphicCalculusOn`, and
  `TauCeti.spectrum_holomorphicCalculusOn_of`: represented and open-domain spectral mapping forms.
* `TauCeti.isUnit_holomorphicCalculus_iff`, `TauCeti.isUnit_holomorphicCalculus_ofFun_iff`, and
  `TauCeti.isUnit_holomorphicCalculusOn_iff`: invertibility of `f(a)` is equivalent to `f` not
  vanishing on `spectrum ℂ a`.

## References

* H. G. Dales, *Banach Algebras and Automatic Continuity*, §2.4, Theorem 2.4.4 and Corollary 2.4.5.
* J. B. Conway, *A Course in Functional Analysis*, second edition, VII.4, Theorem 4.10.
-/

public noncomputable section

open Complex Filter Set TopologicalSpace

namespace TauCeti

open HolomorphicFunctions

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- **Spectral mapping theorem for the holomorphic germ calculus.** For every Banach-algebra
element `a` and every holomorphic germ `g` near `spectrum ℂ a`,
`spectrum ℂ (holomorphicCalculus a g) = spectrum ℂ g` (including in the zero algebra). -/
@[simp]
theorem spectrum_holomorphicCalculus (a : A) (g : holomorphicGerms (spectrum ℂ a)) :
    spectrum ℂ (holomorphicCalculus a g) = spectrum ℂ g := by
  refine Subset.antisymm (AlgHom.spectrum_apply_subset (holomorphicCalculus a) g) ?_
  obtain ⟨f, hf, rfl⟩ := holomorphicGerms.exists_ofFun_eq g
  rw [holomorphicGerms.spectrum_ofFun]
  rintro _ ⟨z₀, hz₀, rfl⟩
  let u := algebraMap ℂ (holomorphicGerms (spectrum ℂ a)) z₀ -
    holomorphicGerms.ofFun id analyticOnNhd_id
  let q := holomorphicGerms.ofFun (dslope f z₀) (hf.dslope z₀)
  have hfac : u * q =
      algebraMap ℂ (holomorphicGerms (spectrum ℂ a)) (f z₀) - holomorphicGerms.ofFun f hf := by
    simp only [u, q]
    rw [← holomorphicGerms.ofFun_const z₀, ← holomorphicGerms.ofFun_sub,
      ← holomorphicGerms.ofFun_mul, ← holomorphicGerms.ofFun_const (f z₀),
      ← holomorphicGerms.ofFun_sub, holomorphicGerms.ofFun_eq_iff]
    refine Eventually.of_forall fun z ↦ ?_
    have hd := sub_smul_dslope f z₀ z
    rw [smul_eq_mul] at hd
    simp only [Pi.mul_apply, Pi.sub_apply, id_eq]
    linear_combination -hd
  have hcomm : Commute (holomorphicCalculus a u) (holomorphicCalculus a q) :=
    (Commute.all u q).map (holomorphicCalculus a)
  have hu : holomorphicCalculus a u = algebraMap ℂ A z₀ - a := by
    simp [u]
  have hmap : holomorphicCalculus a u * holomorphicCalculus a q =
      algebraMap ℂ A (f z₀) - holomorphicCalculus a (holomorphicGerms.ofFun f hf) := by
    rw [← map_mul, hfac, map_sub, AlgHom.commutes]
  rw [spectrum.mem_iff, ← hmap]
  intro hunit
  exact spectrum.mem_iff.mp hz₀ (hu ▸ (hcomm.isUnit_mul_iff.mp hunit).1)

/-- **Spectral mapping theorem (represented germ form).** If `f` is analytic on a neighbourhood of
`spectrum ℂ a`, then `spectrum ℂ (f(a)) = f '' spectrum ℂ a`. -/
theorem spectrum_holomorphicCalculus_ofFun (a : A) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (spectrum ℂ a)) :
    spectrum ℂ (holomorphicCalculus a (holomorphicGerms.ofFun f hf)) = f '' spectrum ℂ a := by
  rw [spectrum_holomorphicCalculus, holomorphicGerms.spectrum_ofFun]

/-- **Spectral mapping theorem (open-domain form).** For `f : holomorphicFunctions U` with
`spectrum ℂ a ⊆ U`, `spectrum ℂ (holomorphicCalculusOn a U ha f) = extend f '' spectrum ℂ a`. -/
theorem spectrum_holomorphicCalculusOn (a : A) (U : Opens ℂ) (ha : spectrum ℂ a ⊆ U)
    (f : holomorphicFunctions U) :
    spectrum ℂ (holomorphicCalculusOn a U ha f) = extend f '' spectrum ℂ a := by
  rw [← holomorphicCalculus_toGerm, spectrum_holomorphicCalculus, toGerm_apply,
    holomorphicGerms.spectrum_ofFun]

/-- **Spectral mapping theorem (ambient differentiable representative).** For `f` differentiable on
an open neighbourhood `U` of `spectrum ℂ a`,
`spectrum ℂ (holomorphicCalculusOn a U ha (of U f hf)) = f '' spectrum ℂ a`. -/
theorem spectrum_holomorphicCalculusOn_of (a : A) (U : Opens ℂ) (ha : spectrum ℂ a ⊆ U)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f U) :
    spectrum ℂ (holomorphicCalculusOn a U ha (of U f hf)) = f '' spectrum ℂ a := by
  rw [← holomorphicCalculus_toGerm, toGerm_of, spectrum_holomorphicCalculus_ofFun]

/-- A holomorphic germ evaluates to a unit at `a` if and only if the germ is a unit
(equivalently, it does not vanish on `spectrum ℂ a`). -/
@[simp]
theorem isUnit_holomorphicCalculus_iff (a : A) (g : holomorphicGerms (spectrum ℂ a)) :
    IsUnit (holomorphicCalculus a g) ↔ IsUnit g := by
  rw [← spectrum.zero_notMem_iff (R := ℂ), spectrum_holomorphicCalculus,
    spectrum.zero_notMem_iff]

/-- A represented holomorphic germ evaluates to a unit at `a` if and only if its representative
does not vanish on `spectrum ℂ a`. -/
theorem isUnit_holomorphicCalculus_ofFun_iff (a : A) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (spectrum ℂ a)) :
    IsUnit (holomorphicCalculus a (holomorphicGerms.ofFun f hf)) ↔
      ∀ z ∈ spectrum ℂ a, f z ≠ 0 := by
  rw [isUnit_holomorphicCalculus_iff, holomorphicGerms.isUnit_iff]
  simp

/-- On an open neighbourhood `U` of `spectrum ℂ a`, `holomorphicCalculusOn a U ha f` is a unit if
and only if `f` does not vanish on `spectrum ℂ a`. -/
theorem isUnit_holomorphicCalculusOn_iff (a : A) (U : Opens ℂ) (ha : spectrum ℂ a ⊆ U)
    (f : holomorphicFunctions U) :
    IsUnit (holomorphicCalculusOn a U ha f) ↔ ∀ z ∈ spectrum ℂ a, extend f z ≠ 0 := by
  rw [← holomorphicCalculus_toGerm, toGerm_apply, isUnit_holomorphicCalculus_ofFun_iff]

end TauCeti
