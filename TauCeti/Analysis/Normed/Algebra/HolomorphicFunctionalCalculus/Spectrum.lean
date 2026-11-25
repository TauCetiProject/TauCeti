/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Algebra.Spectrum
public import TauCeti.Analysis.Normed.Algebra.HolomorphicFunctionalCalculus.Basic

/-!
# Units and spectra under the holomorphic calculus

For an element `a` of a complex Banach algebra, the holomorphic germ calculus
`holomorphicCalculus a` reflects units: `f(a)` is invertible exactly when the germ `f` has no
zero on the spectrum of `a`. Consequently the calculus commutes with `Ring.inverse` and satisfies
the spectral mapping theorem `σ(f(a)) = f(σ(a))`. Related reciprocal
(`TauCeti.holomorphicCalculus_ofFun_inv`), quotient (`TauCeti.holomorphicCalculus_ofFun_div`), and
rational (`TauCeti.holomorphicCalculus_div_polynomial`) evaluation formulas live in `Basic.lean`,
following from the algebraic inverse-germ and quotient formulas
`AlgHom.map_holomorphicGermsOfFun_inv` and `AlgHom.map_holomorphicGermsOfFun_div`.

The key step is that a germ vanishing at `λ ∈ σ(a)` factors as `(z - λ) h(z)`, so that
`f(a) = (a - λ) h(a) = h(a) (a - λ)` cannot be invertible. The zero algebra, where the spectrum
and the germ algebra are trivial, is included.

## Main results

* `TauCeti.isUnit_holomorphicCalculus_iff`, `TauCeti.isUnit_holomorphicCalculus_ofFun_iff`, and
  `TauCeti.isUnit_holomorphicCalculusOn_iff`: `f(a)` is invertible exactly when `f` has no zero on
  the spectrum of `a`.
* `TauCeti.holomorphicCalculus_ringInverse`: the holomorphic calculus commutes with `Ring.inverse`.
* `TauCeti.spectrum_holomorphicCalculus`, `TauCeti.spectrum_holomorphicCalculus_ofFun`,
  `TauCeti.spectrum_holomorphicCalculusOn`, and `TauCeti.spectrum_holomorphicCalculusOn_of`: the
  spectral mapping theorem for germs, represented germs, and functions on an open neighbourhood.

## References

* H. G. Dales, *Banach Algebras and Automatic Continuity*, Theorem 2.4.4.
* J. B. Conway, *A Course in Functional Analysis*, second edition, VII.4.
-/

public noncomputable section

open Set TopologicalSpace

namespace TauCeti

open HolomorphicFunctions

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- The holomorphic calculus reflects units: if `f(a)` is invertible, then the germ `f` has no
zero on the spectrum of `a`. -/
instance isLocalHom_holomorphicCalculus (a : A) : IsLocalHom (holomorphicCalculus a) :=
  AlgHom.isLocalHom_of_map_holomorphicGermsOfFun_id (holomorphicCalculus a)
    (holomorphicCalculus_id a)

/-- `f(a)` is invertible exactly when the germ `f` has no zero on the spectrum of `a`. -/
theorem isUnit_holomorphicCalculus_iff (a : A) (g : holomorphicGerms (spectrum ℂ a)) :
    IsUnit (holomorphicCalculus a g) ↔ ∀ (x : ℂ) (hx : x ∈ spectrum ℂ a),
      holomorphicGerms.eval x hx g ≠ 0 := by
  rw [isUnit_map_iff, holomorphicGerms.isUnit_iff]

/-- The holomorphic calculus commutes with `Ring.inverse`; both sides vanish when the germ has a
zero on the spectrum. -/
@[simp]
theorem holomorphicCalculus_ringInverse (a : A) (g : holomorphicGerms (spectrum ℂ a)) :
    holomorphicCalculus a (Ring.inverse g) = Ring.inverse (holomorphicCalculus a g) :=
  map_ringInverse _ g

/-- **Spectral mapping theorem** for the holomorphic calculus: the spectrum of `f(a)` is the
spectrum of the germ `f`, that is, the set of values of `f` on the spectrum of `a`
(`holomorphicGerms.spectrum_eq`). This includes the zero algebra, where both sides are empty. -/
theorem spectrum_holomorphicCalculus (a : A) (g : holomorphicGerms (spectrum ℂ a)) :
    spectrum ℂ (holomorphicCalculus a g) = spectrum ℂ g :=
  AlgHom.spectrum_apply_eq _ g

/-- **Spectral mapping theorem** for a holomorphic representative: `σ(f(a)) = f(σ(a))`. -/
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

/-- A represented holomorphic germ evaluates to a unit at `a` if and only if its representative
does not vanish on `spectrum ℂ a`. -/
theorem isUnit_holomorphicCalculus_ofFun_iff (a : A) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (spectrum ℂ a)) :
    IsUnit (holomorphicCalculus a (holomorphicGerms.ofFun f hf)) ↔
      ∀ z ∈ spectrum ℂ a, f z ≠ 0 := by
  rw [isUnit_map_iff, holomorphicGerms.isUnit_iff]
  simp

/-- On an open neighbourhood `U` of `spectrum ℂ a`, `holomorphicCalculusOn a U ha f` is a unit if
and only if `f` does not vanish on `spectrum ℂ a`. -/
theorem isUnit_holomorphicCalculusOn_iff (a : A) (U : Opens ℂ) (ha : spectrum ℂ a ⊆ U)
    (f : holomorphicFunctions U) :
    IsUnit (holomorphicCalculusOn a U ha f) ↔ ∀ z ∈ spectrum ℂ a, extend f z ≠ 0 := by
  rw [← holomorphicCalculus_toGerm, toGerm_apply, isUnit_holomorphicCalculus_ofFun_iff]

end TauCeti
