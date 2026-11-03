/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.DedekindZeta.Basic
public import TauCeti.NumberTheory.NumberField.Quadratic.DedekindZeta
import TauCeti.NumberTheory.LSeries.CompletedRiemannZeta

/-!
# The quadratic factorization of the continued Dedekind zeta function

Let `K` be a quadratic number field of discriminant `D`, and let `χ_D` be the primitive quadratic
Dirichlet character of conductor `|D|` (`TauCeti.Multiquadratic.fundamentalDiscriminantChar`),
regarded as a complex character. On the half-plane `Re s > 1` of absolute convergence the
Dedekind zeta function factors as `ζ_K(s) = ζ(s) L(s, χ_D)`
(`TauCeti.NumberField.dedekindZeta_eq_riemannZeta_mul_LFunction`), an identity of Dirichlet
coefficients. The right side is meromorphic on the whole plane and analytic away from `s = 1`:
`ζ` is meromorphic (`TauCeti.meromorphic_riemannZeta`) and analytic off `s = 1`, and `L(s, χ_D)`
is entire because `χ_D` is not the trivial character. So the product is a meromorphic
continuation of `ζ_K`, and the factorization holds for the continued Dedekind zeta function
`TauCeti.LFunctions.dedekindZetaC K`.

Both sides have a pole at `s = 1`, where the values of the total functions carry no meaning, so
the factorization of the continued function is stated as an equality of punctured germs at every
point of the plane and as an equality of values away from `s = 1`.

## Main results

* `TauCeti.LFunctions.dedekindZetaC_eventuallyEq_riemannZeta_mul_LFunction`: the continued
  Dedekind zeta function of a quadratic field has the punctured germ of `ζ(s) L(s, χ_D)` at every
  point.
* `TauCeti.LFunctions.dedekindZetaC_eq_riemannZeta_mul_LFunction`:
  `dedekindZetaC K s = ζ(s) L(s, χ_D)` for every `s ≠ 1`.

## References

* H. Davenport, *Multiplicative Number Theory*, Chapter 6.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §5.
-/

public section

open Filter Module NumberField TauCeti.Multiquadratic
open scoped Topology

namespace TauCeti.LFunctions

variable {K : Type*} [Field K] [NumberField K] (hK : finrank ℚ K = 2)
include hK

/-- The product `ζ(s) L(s, χ_D)` is analytic away from `s = 1`. -/
private theorem analyticAt_riemannZeta_mul_LFunction {s : ℂ} (hs : s ≠ 1) :
    AnalyticAt ℂ (fun z ↦ riemannZeta z * DirichletCharacter.LFunction
      ((fundamentalDiscriminantChar (discr K) (isFundamentalDiscr_discr hK)).ringHomComp
        (Int.castRingHom ℂ)) z) s :=
  (analyticOn_riemannZeta s hs).mul ((DirichletCharacter.differentiable_LFunction
    (ringHomComp_fundamentalDiscriminantChar_discr_ne_one hK)).analyticAt s)

/-- The product `ζ(s) L(s, χ_D)` is meromorphic on the plane. -/
private theorem meromorphic_riemannZeta_mul_LFunction :
    Meromorphic fun z ↦ riemannZeta z * DirichletCharacter.LFunction
      ((fundamentalDiscriminantChar (discr K) (isFundamentalDiscr_discr hK)).ringHomComp
        (Int.castRingHom ℂ)) z := fun z ↦
  (meromorphic_riemannZeta z).mul ((DirichletCharacter.differentiable_LFunction
    (ringHomComp_fundamentalDiscriminantChar_discr_ne_one hK)).analyticAt z).meromorphicAt

/-- The product `ζ(s) L(s, χ_D)` is analytic on the half-plane `Re s > 1`. -/
private theorem analyticOnNhd_riemannZeta_mul_LFunction :
    AnalyticOnNhd ℂ (fun z ↦ riemannZeta z * DirichletCharacter.LFunction
      ((fundamentalDiscriminantChar (discr K) (isFundamentalDiscr_discr hK)).ringHomComp
        (Int.castRingHom ℂ)) z) {s | 1 < s.re} := fun s hs ↦
  analyticAt_riemannZeta_mul_LFunction hK fun h ↦ by simp [h] at hs

/-- The product `ζ(s) L(s, χ_D)` agrees with `ζ_K` on the half-plane `Re s > 1`. -/
private theorem eqOn_riemannZeta_mul_LFunction :
    Set.EqOn (fun z ↦ riemannZeta z * DirichletCharacter.LFunction
      ((fundamentalDiscriminantChar (discr K) (isFundamentalDiscr_discr hK)).ringHomComp
        (Int.castRingHom ℂ)) z) (dedekindZeta K) {s | 1 < s.re} := fun _ hs ↦
  (NumberField.dedekindZeta_eq_riemannZeta_mul_LFunction hK hs).symm

/-- **The quadratic factorization of the continued Dedekind zeta function, as germs.** If `K` is
a quadratic field of discriminant `D`, then at every point of the plane, including the pole
`s = 1`, the continued Dedekind zeta function has the punctured germ of `ζ(s) L(s, χ_D)`, where
`χ_D` is the complex quadratic character of `D`. -/
theorem dedekindZetaC_eventuallyEq_riemannZeta_mul_LFunction (s : ℂ) :
    dedekindZetaC K =ᶠ[𝓝[≠] s] fun z ↦ riemannZeta z * DirichletCharacter.LFunction
      ((fundamentalDiscriminantChar (discr K) (isFundamentalDiscr_discr hK)).ringHomComp
        (Int.castRingHom ℂ)) z := by
  rw [dedekindZetaC_def]
  exact meromorphicContinuation_eventuallyEq (meromorphic_riemannZeta_mul_LFunction hK)
    (analyticOnNhd_riemannZeta_mul_LFunction hK) (eqOn_riemannZeta_mul_LFunction hK) s

/-- **The quadratic factorization of the continued Dedekind zeta function.** If `K` is a
quadratic field of discriminant `D`, then `dedekindZetaC K s = ζ(s) L(s, χ_D)` at every `s ≠ 1`,
where `χ_D` is the complex quadratic character of `D`. At `s = 1` both sides have a pole, and
`dedekindZetaC_eventuallyEq_riemannZeta_mul_LFunction` compares their germs there. -/
theorem dedekindZetaC_eq_riemannZeta_mul_LFunction {s : ℂ} (hs : s ≠ 1) :
    dedekindZetaC K s = riemannZeta s * DirichletCharacter.LFunction
      ((fundamentalDiscriminantChar (discr K) (isFundamentalDiscr_discr hK)).ringHomComp
        (Int.castRingHom ℂ)) s := by
  rw [dedekindZetaC_def]
  exact meromorphicContinuation_apply (meromorphic_riemannZeta_mul_LFunction hK)
    (analyticOnNhd_riemannZeta_mul_LFunction hK) (eqOn_riemannZeta_mul_LFunction hK)
    (analyticAt_riemannZeta_mul_LFunction hK hs)

end TauCeti.LFunctions
