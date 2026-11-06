/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.RingTheory.Unramified.Locus
public import TauCeti.RingTheory.Polynomial.CyclicInvariants.Basic

/-!
# Differentials of the cyclic normal-coordinate quotient

Let `ζ` be a primitive `e`-th root of unity in a domain `R`, with `e > 0`. The fixed
subalgebra `A` of `R[X]` under `X ↦ ζ X` is `R[X^e]`, as constructed by
`Polynomial.cyclicInvariantsEquiv`. Its relative cotangent module is

`Ω[R[X]⁄A] ≃ R[X] / (e X^(e-1))`.

The equivalence sends `dX` to `1` and `df` to the class of the ordinary derivative of
`f`. In particular its annihilator is exactly `(e X^(e-1))`, not merely an ideal
contained in it. This computes the scheme-theoretic ramification multiplicity of the
normal-coordinate power map. The coefficient ring may itself contain the coordinates
along a reflecting hyperplane. No invertibility assumption on `e` is imposed.

## References

* R. Kane, *Reflection Groups and Invariant Theory*, Springer (2001), §18.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Cambridge (1990), §3.5.

The construction uses Mathlib's universal derivation and `Polynomial.mkDerivationEquiv`,
and the power-substitution presentation `Polynomial.cyclicInvariantsEquiv`.
-/

public section

noncomputable section

namespace Polynomial

variable {R : Type*} [CommRing R] {e : ℕ} {ζ : R}

local notation "A" => (AlgHom.equalizer (aeval (C ζ * X)) (AlgHom.id R R[X]))

private theorem cyclic_D_apply (p : R[X]) :
    KaehlerDifferential.D A R[X] p = derivative p • KaehlerDifferential.D A R[X] X := by
  have h := congrArg (fun d : Derivation R R[X] Ω[R[X]⁄A] ↦ d p)
    ((mkDerivationEquiv R).apply_symm_apply
      ((KaehlerDifferential.D A R[X]).restrictScalars R))
  simpa only [mkDerivationEquiv_apply, mkDerivationEquiv_symm_apply,
    mkDerivation_apply, Derivation.restrictScalars_apply] using h.symm

variable [IsDomain R]

private theorem differential_relation (he : 0 < e) (hζ : IsPrimitiveRoot ζ e) :
    ((e : R[X]) * X ^ (e - 1)) • KaehlerDifferential.D A R[X] X = 0 := by
  let a : A := cyclicInvariantsEquiv he hζ X
  have ha : (a : R[X]) = X ^ e := by simp [a]
  have h := (KaehlerDifferential.D A R[X]).map_algebraMap a
  rw [Subalgebra.algebraMap_apply, ha, cyclic_D_apply, derivative_X_pow] at h
  exact h

private def quotientDerivative (he : 0 < e) (hζ : IsPrimitiveRoot ζ e) :
    Derivation A R[X] (R[X] ⧸ Ideal.span {((e : R[X]) * X ^ (e - 1))}) := by
  let I : Ideal R[X] := Ideal.span {((e : R[X]) * X ^ (e - 1))}
  let D : Derivation R R[X] (R[X] ⧸ I) := I.mkQ.compDer derivative'
  have hzero (a : A) : D a = 0 := by
    have hmem : derivative (a : R[X]) ∈ I := by
      rw [derivative_of_comp_C_mul_X_eq_self (a : R[X]) he hζ a.2]
      exact I.mul_mem_left _ (Ideal.subset_span rfl)
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  exact
    { toFun := D
      map_add' := D.map_add
      map_smul' := fun a p ↦ by
        simp only [Algebra.smul_def, D.leibniz, Subalgebra.algebraMap_apply,
          RingHom.id_apply, hzero, smul_zero, add_zero]
        exact (IsScalarTower.algebraMap_smul R[X] a (D p)).symm
      map_one_eq_zero' := D.map_one_eq_zero
      leibniz' := D.leibniz }

private theorem quotientDerivative_apply (he : 0 < e) (hζ : IsPrimitiveRoot ζ e)
    (p : R[X]) :
    quotientDerivative he hζ p =
      Ideal.Quotient.mk (Ideal.span {((e : R[X]) * X ^ (e - 1))}) (derivative p) :=
  (rfl)

private def differentialFromQuotient (he : 0 < e) (hζ : IsPrimitiveRoot ζ e) :
    (R[X] ⧸ Ideal.span {((e : R[X]) * X ^ (e - 1))}) →ₗ[R[X]] Ω[R[X]⁄A] := by
  let L : R[X] →ₗ[R[X]] Ω[R[X]⁄A] :=
    LinearMap.toSpanSingleton R[X] _ (KaehlerDifferential.D A R[X] X)
  exact Submodule.liftQSpanSingleton ((e : R[X]) * X ^ (e - 1)) L
    (differential_relation he hζ)

private theorem differentialFromQuotient_mk (he : 0 < e) (hζ : IsPrimitiveRoot ζ e)
    (p : R[X]) :
    differentialFromQuotient he hζ
        (Ideal.Quotient.mk (Ideal.span {((e : R[X]) * X ^ (e - 1))}) p) =
      p • KaehlerDifferential.D A R[X] X :=
  (rfl)

/-- The relative cotangent module of the cyclic normal-coordinate quotient is the quotient
by `e X^(e-1)`. The class of `1` corresponds to the differential of the normal coordinate. -/
def cyclicInvariantsDifferentialEquiv (he : 0 < e) (hζ : IsPrimitiveRoot ζ e) :
    Ω[R[X]⁄A] ≃ₗ[R[X]] R[X] ⧸ Ideal.span {((e : R[X]) * X ^ (e - 1))} := by
  let F := (quotientDerivative he hζ).liftKaehlerDifferential
  let H := differentialFromQuotient he hζ
  refine LinearEquiv.ofLinearMap F H ?_ ?_
  · apply LinearMap.ext
    intro p
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective p
    simp only [LinearMap.comp_apply, LinearMap.id_apply, F, H,
      differentialFromQuotient_mk, map_smul,
      Derivation.liftKaehlerDifferential_comp_D, quotientDerivative_apply,
      derivative_X, map_one]
    exact (Algebra.algebraMap_eq_smul_one p).symm
  · apply Derivation.liftKaehlerDifferential_unique
    ext p
    simp only [Derivation.coe_comp, Derivation.coeFn_coe, LinearMap.restrictScalars_apply,
      LinearMap.comp_apply, LinearMap.id_apply, F,
      Derivation.liftKaehlerDifferential_comp_D, quotientDerivative_apply, H,
      differentialFromQuotient_mk]
    exact (cyclic_D_apply p).symm

/-- Under the cotangent presentation, the universal differential is the ordinary derivative
modulo the normal ramification factor. -/
@[simp]
theorem cyclicInvariantsDifferentialEquiv_D (he : 0 < e) (hζ : IsPrimitiveRoot ζ e)
    (p : R[X]) :
    cyclicInvariantsDifferentialEquiv he hζ (KaehlerDifferential.D A R[X] p) =
      Ideal.Quotient.mk (Ideal.span {((e : R[X]) * X ^ (e - 1))}) (derivative p) :=
  (quotientDerivative he hζ).liftKaehlerDifferential_comp_D p

/-- The inverse cotangent presentation sends a polynomial class to its multiple of `dX`. -/
@[simp]
theorem cyclicInvariantsDifferentialEquiv_symm_mk (he : 0 < e) (hζ : IsPrimitiveRoot ζ e)
    (p : R[X]) :
    (cyclicInvariantsDifferentialEquiv he hζ).symm
        (Ideal.Quotient.mk (Ideal.span {((e : R[X]) * X ^ (e - 1))}) p) =
      p • KaehlerDifferential.D A R[X] X :=
  (rfl)

/-- The annihilator of the relative differentials is exactly the ideal generated by the
derivative of the normal-coordinate power map. -/
theorem annihilator_cyclicInvariantsDifferential (he : 0 < e) (hζ : IsPrimitiveRoot ζ e) :
    Module.annihilator R[X] Ω[R[X]⁄A] = Ideal.span {((e : R[X]) * X ^ (e - 1))} := by
  rw [(cyclicInvariantsDifferentialEquiv he hζ).annihilator_eq,
    Ideal.annihilator_quotient]

/-- The cyclic normal-coordinate quotient is unramified precisely where the derivative
`e X^(e-1)` is invertible. This also records any ramification coming from the coefficient
ring when `e` is not a unit. -/
theorem unramifiedLocus_cyclicInvariants (he : 0 < e) (hζ : IsPrimitiveRoot ζ e) :
    Algebra.unramifiedLocus A R[X] =
      (PrimeSpectrum.basicOpen ((e : R[X]) * X ^ (e - 1)) : Set (PrimeSpectrum R[X])) := by
  rw [Algebra.unramifiedLocus_eq_compl_support,
    (cyclicInvariantsDifferentialEquiv he hζ).support_eq, Module.support_eq_zeroLocus,
    Ideal.annihilator_quotient, PrimeSpectrum.zeroLocus_span,
    PrimeSpectrum.basicOpen_eq_zeroLocus_compl]

/-- If the stabilizer order is a unit, the normal-coordinate ramification ideal is
`(X^(e-1))`, with its exact multiplicity. -/
theorem annihilator_cyclicInvariantsDifferential_of_isUnit (he : 0 < e)
    (hζ : IsPrimitiveRoot ζ e) (hu : IsUnit (e : R)) :
    Module.annihilator R[X] Ω[R[X]⁄A] = Ideal.span {X ^ (e - 1)} := by
  rw [annihilator_cyclicInvariantsDifferential he hζ]
  exact Ideal.span_singleton_mul_left_unit (by simpa using hu.map (C : R →+* R[X])) _

/-- For a nontrivial cyclic normal-coordinate quotient of invertible order, the
unramified locus is exactly the complement of the reflecting hyperplane. -/
theorem unramifiedLocus_cyclicInvariants_of_isUnit (he : 1 < e)
    (hζ : IsPrimitiveRoot ζ e) (hu : IsUnit (e : R)) :
    Algebra.unramifiedLocus A R[X] =
      (PrimeSpectrum.basicOpen (X : R[X]) : Set (PrimeSpectrum R[X])) := by
  have hu' : IsUnit (e : R[X]) := by simpa using hu.map (C : R →+* R[X])
  rw [unramifiedLocus_cyclicInvariants (by omega) hζ,
    PrimeSpectrum.basicOpen_mul, PrimeSpectrum.basicOpen_pow _ _ (by omega)]
  ext p
  simp [p.asIdeal.notMem_of_isUnit hu']

end Polynomial
