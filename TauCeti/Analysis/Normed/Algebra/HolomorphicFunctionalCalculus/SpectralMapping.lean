/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Algebra.Spectrum
public import TauCeti.Analysis.Normed.Algebra.HolomorphicFunctionalCalculus.Basic

/-!
# The spectral mapping theorem for the holomorphic calculus

For an element `a` of a complex Banach algebra and a germ `f` holomorphic near its spectrum,
the holomorphic calculus value `f(a)` is invertible exactly when `f` has no zero on the
spectrum of `a`. Equivalently, `holomorphicCalculus a` is a local homomorphism, so it
preserves spectra:

`σ(f(a)) = f(σ(a))`.

The nontrivial inclusion comes from the factorization `f(z) - f(x) = (z - x) g(z)` with
`g = dslope f x` holomorphic: if `x ∈ σ(a)` and `f(a) - f(x)` were invertible, then the
commuting factor `a - x` would be invertible too. The same statement is given for the
calculus on an open neighbourhood of the spectrum.

Since the calculus reflects units, it commutes with `Ring.inverse`. Consequently a quotient
of germs is sent to the quotient of values, and in particular a rational function with no
pole on the spectrum is evaluated by the usual rational expression in `a`.

## Main results

* `TauCeti.isLocalHom_holomorphicCalculus`: the germ calculus reflects units.
* `TauCeti.spectrum_holomorphicCalculus_ofFun`: the spectral mapping theorem.
* `TauCeti.spectrum_holomorphicCalculusOn`: the spectral mapping theorem on an open domain.
* `TauCeti.holomorphicCalculus_ofFun_div`: quotients are sent to quotients.
* `TauCeti.holomorphicCalculus_div_polynomial`: agreement with rational functions.

## References

* H. G. Dales, *Banach Algebras and Automatic Continuity*, Theorem 2.4.4.
* J. B. Conway, *A Course in Functional Analysis*, second edition, VII.4.10.
-/

public section

open Set TopologicalSpace
open scoped Ring

namespace TauCeti

open HolomorphicFunctions

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- The holomorphic calculus reflects units: if `f(a)` is invertible, then the germ `f` has
no zero on the spectrum of `a`. -/
instance isLocalHom_holomorphicCalculus (a : A) : IsLocalHom (holomorphicCalculus a) where
  map_nonunit g hg := by
    obtain ⟨f, hf, rfl⟩ := holomorphicGerms.exists_ofFun_eq g
    refine (holomorphicGerms.isUnit_iff _).mpr fun x hx hfx => spectrum.mem_iff.mp hx ?_
    rw [holomorphicGerms.eval_ofFun] at hfx
    -- Divide out the zero at `x`: `f = (z - x) · dslope f x` near the spectrum.
    have hd : AnalyticOnNhd ℂ (dslope f x) (spectrum ℂ a) := fun z hz => (hf z hz).dslope x
    have hl : AnalyticOnNhd ℂ (fun z => z - x) (spectrum ℂ a) :=
      analyticOnNhd_id.sub analyticOnNhd_const
    have hfac : holomorphicGerms.ofFun f hf =
        holomorphicGerms.ofFun (fun z => z - x) hl * holomorphicGerms.ofFun (dslope f x) hd := by
      rw [← holomorphicGerms.ofFun_mul, holomorphicGerms.ofFun_eq_iff]
      refine Filter.Eventually.of_forall fun z => ?_
      simpa [hfx] using (sub_smul_dslope f x z).symm
    have hlin : holomorphicCalculus a (holomorphicGerms.ofFun (fun z => z - x) hl) =
        a - algebraMap ℂ A x := by
      convert holomorphicCalculus_polynomial a (Polynomial.X - Polynomial.C x) using 3 <;>
        simp
    rw [hfac, map_mul] at hg
    have hx' := (((Commute.all _ _).map (holomorphicCalculus a)).isUnit_mul_iff.mp hg).1
    rw [hlin] at hx'
    exact IsUnit.sub_iff.mp hx'

/-- **Spectral mapping theorem** for the holomorphic germ calculus: `σ(f(a)) = f(σ(a))`. -/
theorem spectrum_holomorphicCalculus_ofFun (a : A) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (spectrum ℂ a)) :
    spectrum ℂ (holomorphicCalculus a (holomorphicGerms.ofFun f hf)) = f '' spectrum ℂ a := by
  rw [AlgHom.spectrum_apply_eq, holomorphicGerms.spectrum_ofFun]

/-- The spectral mapping theorem for the calculus on an open neighbourhood `U` of the
spectrum: the spectrum of `f(a)` is the image of the spectrum of `a` under `f`. -/
theorem spectrum_holomorphicCalculusOn (a : A) (U : Opens ℂ) (ha : spectrum ℂ a ⊆ U)
    (f : holomorphicFunctions U) :
    spectrum ℂ (holomorphicCalculusOn a U ha f) = extend f '' spectrum ℂ a := by
  rw [← holomorphicCalculus_toGerm,
    toGerm_eq_ofFun ha f (extend f) (analyticOnNhd_extend ha f)
      (fun z => (extend_apply f z).symm),
    spectrum_holomorphicCalculus_ofFun]

/-- The holomorphic calculus sends a quotient by a function with no zero on the spectrum to
the product with the inverse of the denominator's value. -/
theorem holomorphicCalculus_ofFun_div (a : A) {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (spectrum ℂ a)) (hg : AnalyticOnNhd ℂ g (spectrum ℂ a))
    (hne : ∀ z ∈ spectrum ℂ a, g z ≠ 0) :
    holomorphicCalculus a (holomorphicGerms.ofFun (fun z => f z / g z) (hf.div hg hne)) =
      holomorphicCalculus a (holomorphicGerms.ofFun f hf) *
        (holomorphicCalculus a (holomorphicGerms.ofFun g hg))⁻¹ʳ := by
  have hdiv : holomorphicGerms.ofFun (fun z => f z / g z) (hf.div hg hne) =
      holomorphicGerms.ofFun f hf * holomorphicGerms.ofFun (fun z => (g z)⁻¹) (hg.inv hne) := by
    rw [← holomorphicGerms.ofFun_mul, holomorphicGerms.ofFun_eq_iff]
    exact Filter.Eventually.of_forall fun z => div_eq_mul_inv (f z) (g z)
  rw [hdiv, map_mul, holomorphicGerms.ofFun_inv hg hne, map_ringInverse]

/-- The holomorphic calculus agrees with rational functions whose poles lie off the
spectrum: `(p / q)(a) = p(a) q(a)⁻¹`. -/
theorem holomorphicCalculus_div_polynomial (a : A) (p q : Polynomial ℂ)
    (hq : ∀ z ∈ spectrum ℂ a, q.eval z ≠ 0) :
    holomorphicCalculus a (holomorphicGerms.ofFun (fun z => p.eval z / q.eval z)
      (((AnalyticOnNhd.eval_polynomial p).mono (subset_univ _)).div
        ((AnalyticOnNhd.eval_polynomial q).mono (subset_univ _)) hq)) =
      Polynomial.aeval a p * (Polynomial.aeval a q)⁻¹ʳ := by
  rw [holomorphicCalculus_ofFun_div a ((AnalyticOnNhd.eval_polynomial p).mono (subset_univ _))
    ((AnalyticOnNhd.eval_polynomial q).mono (subset_univ _)) hq,
    holomorphicCalculus_polynomial, holomorphicCalculus_polynomial]

end TauCeti
