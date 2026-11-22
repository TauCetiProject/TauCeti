/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
public import TauCeti.RingTheory.SplitAlgebra.Descent

import Mathlib.RingTheory.Flat.Localization

/-!
# Trace splittings and the direct summand theorem over `ℚ`

Let `R` be an integrally closed domain with fraction field `K`, and let `L` be a field extension of
`K` of degree `d`. The trace of an element of `L` integral over `R` is integral over `R` and lies
in `K`, hence lies in `R`. So if `d` is a unit of `R`, the divided trace `d⁻¹ • Tr_{L/K}`
restricts to an `R`-linear map from any integral `R`-algebra `S` mapping to `L` back to `R`, and it
takes `1` to `d⁻¹ • d = 1`: it splits `S` over `R`.

Over a ring containing `ℚ` every positive degree is a unit. Choosing a prime of a finite
injective algebra `S` lying over the zero ideal and taking `L` to be the fraction field of the
quotient gives the direct summand theorem in this case: every finite `R`-algebra with injective
structure map is split over an integrally closed domain `R` containing `ℚ`. Since splitting of
finitely presented algebras is detected at maximal ideals, the same holds over every ring
containing `ℚ` whose localizations at maximal ideals are integrally closed domains, for finitely
presented algebras.

## Main results

* `TauCeti.exists_splitting_algebraMap_eq_trace`: for an integral `R`-algebra `S`, an
  `R`-algebra map `f : S → L` and `[L : K]` a unit of `R`, the divided trace
  `x ↦ [L : K]⁻¹ * Tr_{L/K} (f x)` takes values in `R` and splits `S` over `R`.
* `TauCeti.SplitAlgebra.of_isUnit_finrank`: the splitting statement alone.
* `TauCeti.SplitAlgebra.of_injective_of_algebraRat`: over an integrally closed domain containing
  `ℚ`, every finite algebra with injective structure map is split.
* `TauCeti.SplitAlgebra.of_injective_of_algebraRat_of_localization`: the same over a ring
  containing `ℚ` whose localizations at maximal ideals are integrally closed domains, for
  algebras finitely presented as modules.

## References

* Y. André, *La conjecture du facteur direct*, Publ. Math. IHÉS 127 (2018), §0.2.
* B. Bhatt, *Derived splinters in positive characteristic*, Compos. Math. 148 (2012),
  Example 1.1.
-/

public section

open Module

namespace TauCeti

section Trace

variable {R K L S : Type*} [CommRing R] [IsIntegrallyClosed R] [Field K] [Algebra R K]
  [IsFractionRing R K] [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  [Ring S] [Algebra R S] [Algebra.IsIntegral R S]

/-- The divided trace splits integral algebras over an integrally closed domain. Let `R` be an
integrally closed domain with fraction field `K`, let `L` be an extension of `K` whose degree
`[L : K]` is a unit of `R`, and let `f : S → L` be an `R`-algebra map from an integral
`R`-algebra `S`. Then `x ↦ [L : K]⁻¹ * Tr_{L/K} (f x)` takes values in `R`, and as an `R`-linear
map `S → R` it takes `1` to `1`. -/
theorem exists_splitting_algebraMap_eq_trace (f : S →ₐ[R] L) (hd : IsUnit (finrank K L : R)) :
    ∃ ρ : S →ₗ[R] R, ρ 1 = 1 ∧
      ∀ x, algebraMap R K (ρ x) = (finrank K L : K)⁻¹ * Algebra.trace K L (f x) := by
  have hdK : (finrank K L : K) ≠ 0 := by
    simpa using (hd.map (algebraMap R K)).ne_zero
  have : FiniteDimensional K L :=
    Module.finite_of_finrank_pos (Nat.pos_of_ne_zero fun h ↦ hdK (by simp [h]))
  -- `f` lands in the integral closure of `R` in `L`, where Mathlib restricts the trace to `R`.
  let g : S →ₐ[R] integralClosure R L :=
    f.codRestrict _ fun x ↦ (Algebra.IsIntegral.isIntegral x).map f
  let ρ : S →ₗ[R] R :=
    (hd.unit⁻¹ : Rˣ).val • (Algebra.intTraceAux R K L (integralClosure R L) ∘ₗ g.toLinearMap)
  have hu : algebraMap R K (hd.unit⁻¹ : Rˣ).val = (finrank K L : K)⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← map_natCast (algebraMap R K), ← map_mul, hd.val_inv_mul, map_one]
  have hρ (x : S) :
      algebraMap R K (ρ x) = (finrank K L : K)⁻¹ * Algebra.trace K L (f x) := by
    simp only [ρ, LinearMap.smul_apply, LinearMap.comp_apply, smul_eq_mul, map_mul, hu,
      Algebra.map_intTraceAux]
    rfl
  refine ⟨ρ, IsFractionRing.injective R K ?_, hρ⟩
  rw [hρ, map_one f, map_one (algebraMap R K), ← map_one (algebraMap K L),
    Algebra.trace_algebraMap, nsmul_eq_mul, mul_one, inv_mul_cancel₀ hdK]

/-- An integral algebra `S` over an integrally closed domain `R` is split as soon as it maps to a
field extension `L` of the fraction field `K` of `R` whose degree `[L : K]` is a unit of `R`. -/
theorem SplitAlgebra.of_isUnit_finrank (f : S →ₐ[R] L) (hd : IsUnit (finrank K L : R)) :
    SplitAlgebra R S := by
  obtain ⟨ρ, hρ, -⟩ := exists_splitting_algebraMap_eq_trace f hd
  exact .of_map_one ρ hρ

end Trace

section Rat

/-- The direct summand theorem over an integrally closed domain containing `ℚ`: every finite
`R`-algebra `S` whose structure map is injective is split over `R`. -/
theorem SplitAlgebra.of_injective_of_algebraRat {R S : Type*} [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] [Algebra ℚ R] [CommRing S] [Algebra R S] [Module.Finite R S]
    (h : Function.Injective (algebraMap R S)) : SplitAlgebra R S := by
  -- A prime `q` of `S` over `0` gives a domain `S ⧸ q` finite over `R` and containing `R`; the
  -- divided trace of its fraction field over that of `R` splits `S`.
  obtain ⟨q, -, hq, hqR⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (⊥ : Ideal R)
    (⊥ : Ideal S) fun x hx ↦ (injective_iff_map_eq_zero _).1 h x ((Ideal.mem_under R _).1 hx)
  have hinj : Function.Injective (algebraMap R (S ⧸ q)) := by
    refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
    rw [← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq_zero_iff_mem,
      ← Ideal.mem_under, hqR] at hx
    exact Ideal.mem_bot.1 hx
  have : IsTorsionFree R (S ⧸ q) := isTorsionFree_iff_algebraMap_injective.2 hinj
  let := FractionRing.liftAlgebra R (FractionRing (S ⧸ q))
  have hpos : 0 < finrank (FractionRing R) (FractionRing (S ⧸ q)) := Module.finrank_pos
  refine SplitAlgebra.of_isUnit_finrank (K := FractionRing R)
    ((IsScalarTower.toAlgHom R (S ⧸ q) (FractionRing (S ⧸ q))).comp (Ideal.Quotient.mkₐ R q)) ?_
  rw [← map_natCast (algebraMap ℚ R)]
  exact (IsUnit.mk0 _ (Nat.cast_ne_zero.2 hpos.ne')).map _

/-- The direct summand theorem over a ring `R` containing `ℚ` whose localizations at maximal
ideals are integrally closed domains (for instance an integrally closed domain containing `ℚ`):
every `R`-algebra `S` finitely presented as an `R`-module whose structure map is injective is split
over `R`. -/
theorem SplitAlgebra.of_injective_of_algebraRat_of_localization {R S : Type*} [CommRing R]
    [Algebra ℚ R] [CommRing S] [Algebra R S] [Module.FinitePresentation R S]
    (hR : ∀ (m : Ideal R) [m.IsMaximal], IsDomain (Localization.AtPrime m) ∧
      IsIntegrallyClosed (Localization.AtPrime m))
    (h : Function.Injective (algebraMap R S)) : SplitAlgebra R S := by
  -- Splitting is detected at the maximal ideals, where the localized algebra is still finite and
  -- injective by flatness of localization.
  refine splitAlgebra_iff_localized_maximal.2 fun m _ ↦ ?_
  obtain ⟨_, _⟩ := hR m
  let : Algebra ℚ (Localization.AtPrime m) :=
    ((algebraMap R (Localization.AtPrime m)).comp (algebraMap ℚ R)).toAlgebra
  exact SplitAlgebra.of_injective_of_algebraRat
    (Algebra.TensorProduct.includeLeft_injective (S := Localization.AtPrime m) h)

end Rat

end TauCeti
