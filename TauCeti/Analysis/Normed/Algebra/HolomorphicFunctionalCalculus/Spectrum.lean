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
zero on the spectrum of `a`. Consequently the calculus commutes with `Ring.inverse`, it sends
quotients to products with inverses and so agrees with rational functions whose poles lie off the
spectrum, it sends `(μ - z)⁻¹` to the resolvent at `μ`, and it satisfies the spectral mapping
theorem `σ(f(a)) = f(σ(a))`.

The key step is that a germ vanishing at `λ ∈ σ(a)` factors as `(z - λ) h(z)`, so that
`f(a) = (a - λ) h(a) = h(a) (a - λ)` cannot be invertible. The zero algebra, where the spectrum
and the germ algebra are trivial, is included.

## Main results

* `TauCeti.isUnit_holomorphicCalculus_iff`, `TauCeti.isUnit_holomorphicCalculus_ofFun_iff`, and
  `TauCeti.isUnit_holomorphicCalculusOn_iff`: `f(a)` is invertible exactly when `f` has no zero on
  the spectrum of `a`.
* `TauCeti.spectrum_holomorphicCalculus`, `TauCeti.spectrum_holomorphicCalculus_ofFun`,
  `TauCeti.spectrum_holomorphicCalculusOn`, and `TauCeti.spectrum_holomorphicCalculusOn_of`: the
  spectral mapping theorem for germs, represented germs, and functions on an open neighbourhood.
* `TauCeti.holomorphicCalculus_ofFun_div` and `TauCeti.holomorphicCalculus_polynomial_div`:
  quotients are sent to quotients, so the calculus agrees with rational functions.

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
instance isLocalHom_holomorphicCalculus (a : A) : IsLocalHom (holomorphicCalculus a) where
  map_nonunit g hg := by
    refine (holomorphicGerms.isUnit_iff g).mpr fun x hx hgx ↦ ?_
    obtain ⟨h, rfl⟩ := (holomorphicGerms.dvd_iff_eval_eq_zero hx g).mpr hgx
    have hc : Commute (holomorphicCalculus a
        (holomorphicGerms.ofFun id analyticOnNhd_id - algebraMap ℂ _ x))
        (holomorphicCalculus a h) := (Commute.all _ _).map _
    rw [map_mul, hc.isUnit_mul_iff, map_sub, holomorphicCalculus_id, AlgHom.commutes] at hg
    exact spectrum.mem_iff.mp hx (by simpa using hg.1.neg)

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

/-- The calculus sends the reciprocal of a function without zeros on the spectrum to the inverse
of its value. -/
theorem holomorphicCalculus_ofFun_inv (a : A) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (spectrum ℂ a)) (hne : ∀ x ∈ spectrum ℂ a, f x ≠ 0) :
    holomorphicCalculus a (holomorphicGerms.ofFun (fun z ↦ (f z)⁻¹) (hf.inv hne)) =
      Ring.inverse (holomorphicCalculus a (holomorphicGerms.ofFun f hf)) := by
  rw [holomorphicGerms.ofFun_inv hf hne, holomorphicCalculus_ringInverse]

/-- The calculus sends a quotient by a function with no zero on the spectrum to the product with
the inverse of the denominator's value. -/
theorem holomorphicCalculus_ofFun_div (a : A) {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (spectrum ℂ a)) (hg : AnalyticOnNhd ℂ g (spectrum ℂ a))
    (hne : ∀ z ∈ spectrum ℂ a, g z ≠ 0) :
    holomorphicCalculus a (holomorphicGerms.ofFun (fun z ↦ f z / g z) (hf.div hg hne)) =
      holomorphicCalculus a (holomorphicGerms.ofFun f hf) *
        Ring.inverse (holomorphicCalculus a (holomorphicGerms.ofFun g hg)) := by
  have h : holomorphicGerms.ofFun (fun z ↦ f z / g z) (hf.div hg hne) =
      holomorphicGerms.ofFun f hf * holomorphicGerms.ofFun (fun z ↦ (g z)⁻¹) (hg.inv hne) := by
    rw [← holomorphicGerms.ofFun_mul, holomorphicGerms.ofFun_eq_iff]
    exact .of_forall fun z ↦ div_eq_mul_inv _ _
  rw [h, map_mul, holomorphicCalculus_ofFun_inv a _ hg hne]

/-- The calculus agrees with rational functions whose poles lie off the spectrum. -/
theorem holomorphicCalculus_polynomial_div (a : A) (p q : Polynomial ℂ)
    (hq : ∀ x ∈ spectrum ℂ a, q.eval x ≠ 0) :
    holomorphicCalculus a (holomorphicGerms.ofFun (fun z ↦ p.eval z / q.eval z)
      (((AnalyticOnNhd.eval_polynomial p).mono (subset_univ _)).div
        ((AnalyticOnNhd.eval_polynomial q).mono (subset_univ _)) hq)) =
      Polynomial.aeval a p * Ring.inverse (Polynomial.aeval a q) := by
  rw [holomorphicCalculus_ofFun_div a ((AnalyticOnNhd.eval_polynomial p).mono (subset_univ _))
    ((AnalyticOnNhd.eval_polynomial q).mono (subset_univ _)) hq,
    holomorphicCalculus_polynomial, holomorphicCalculus_polynomial]

/-- The calculus sends `z ↦ (μ - z)⁻¹` to the resolvent of `a` at a point `μ` off the
spectrum. -/
theorem holomorphicCalculus_inv_sub (a : A) {μ : ℂ} (hμ : μ ∉ spectrum ℂ a) :
    holomorphicCalculus a (holomorphicGerms.ofFun (fun z ↦ (μ - z)⁻¹)
      ((analyticOnNhd_const.sub analyticOnNhd_id).inv fun x hx ↦
        sub_ne_zero.mpr (ne_of_mem_of_not_mem hx hμ).symm)) = resolvent a μ := by
  have hf := (AnalyticOnNhd.eval_polynomial (𝕜 := ℂ) (Polynomial.C μ - Polynomial.X)).mono
    (subset_univ (spectrum ℂ a))
  have hne : ∀ x ∈ spectrum ℂ a, (Polynomial.C μ - Polynomial.X).eval x ≠ 0 := fun x hx ↦ by
    simpa [sub_eq_zero] using (ne_of_mem_of_not_mem hx hμ).symm
  have h := holomorphicCalculus_ofFun_inv a _ hf hne
  rw [holomorphicCalculus_polynomial] at h
  simpa only [Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X, map_sub,
    Polynomial.aeval_C, Polynomial.aeval_X, resolvent] using h

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
