/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.IdeleClass.SIdeles
public import TauCeti.RingTheory.DedekindDomain.SInteger.Unit
public import TauCeti.NumberTheory.ClassFieldTheory.Global.PlacePermutation.Basic

/-!
# The Galois-equivariant valuation of S-units

For an extension of number fields `L/K`, valuation sends an `S`-unit of `L` to an
integer-valued function on the primes of `L` above `S`. This file constructs that map as a
morphism of integral Galois representations. The equivariance is the local identity that the
valuation of a Galois translate at the translated prime equals the original valuation.
The map is the finite-place input to the comparison between the `S`-units and the place
permutation lattice in the Herbrand-quotient calculation for idele classes.

The underlying valuation and its finite-index image are `Set.unitValuation` and
`TauCeti.finiteIndex_range_unitValuation`. See J. S. Milne, *Class Field Theory*, Chapter VII, §3.
-/

public noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField MonoidAlgebra
open scoped NumberField Pointwise

namespace TauCeti.ClassFieldTheory

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L]

/-- The valuation of a Galois translate at the translated prime is the original valuation. -/
theorem valuationOfNeZero_smul_primesAbove (S : Set (HeightOneSpectrum (𝓞 K)))
    (σ : L ≃ₐ[K] L) (w : ↥(primesAbove (𝓞 K) (𝓞 L) S)) (u : Lˣ) :
    (σ • w).1.valuationOfNeZero (σ • u) = w.1.valuationOfNeZero u := by
  apply WithZero.coe_injective
  rw [valuationOfNeZero_eq, valuationOfNeZero_eq]
  simpa only [AlgEquiv.smul_units_def, Units.coe_map, MonoidHom.coe_ofClass] using
    valuation_apply_eq_of_asIdeal_eq_smul σ
      (asIdeal_smul_primesAbove_ringOfIntegers K L S σ w) (u : L)

/-- The valuation tuple of an `S`-unit, written additively as a vector in the free module on
the primes above `S`. -/
def sUnitsValuation (S : Finset (HeightOneSpectrum (𝓞 K))) :
    sUnitsRep L (↑S : Set _) ⟶
      Rep.ofMulAction ℤ (L ≃ₐ[K] L) ↥(primesAbove (𝓞 K) (𝓞 L) ↑S) := by
  classical
  letI := (primesAbove_finite (𝓞 K) (𝓞 L) S.finite_toSet).to_subtype
  let e : Additive (↥(primesAbove (𝓞 K) (𝓞 L) ↑S) → Multiplicative ℤ) ≃ₗ[ℤ]
      (↥(primesAbove (𝓞 K) (𝓞 L) ↑S) → ℤ) :=
    (MulEquiv.funMultiplicative _ ℤ).symm.toAdditiveLeft.toIntLinearEquiv
  let v := (Set.unitValuation (primesAbove (𝓞 K) (𝓞 L) ↑S) L).toAdditive.toIntLinearMap
  let q := (Finsupp.linearEquivFunOnFinite ℤ ℤ
    ↥(primesAbove (𝓞 K) (𝓞 L) ↑S)).symm.toLinearMap
  let r : (↥(primesAbove (𝓞 K) (𝓞 L) ↑S) →₀ ℤ) →ₗ[ℤ]
      MonoidAlgebra ℤ ↥(primesAbove (𝓞 K) (𝓞 L) ↑S) :=
    (MonoidAlgebra.coeffLinearEquiv ℤ).symm.toLinearMap
  let f := r ∘ₗ q ∘ₗ e.toLinearMap ∘ₗ v
  exact Rep.ofHom ⟨f, by
    intro σ
    ext u w
    simp only [LinearMap.comp_apply, Representation.coeff_ofMulAction]
    -- The four linear equivalences defining `f` reduce its coefficients to `unitValuation`.
    change Multiplicative.toAdd
        (Set.unitValuation (primesAbove (𝓞 K) (𝓞 L) ↑S) L (σ • u.toMul) w) =
      Multiplicative.toAdd
        (Set.unitValuation (primesAbove (𝓞 K) (𝓞 L) ↑S) L u.toMul (σ⁻¹ • w))
    have h := valuationOfNeZero_smul_primesAbove (↑S : Set _) σ (σ⁻¹ • w) u.toMul
    simpa only [Set.unitValuation_apply, smul_inv_smul,
      GlobalNumberFields.coe_smul_unit_primesAbove] using congrArg Multiplicative.toAdd h⟩

/-- The coefficient of the `S`-unit valuation vector at a prime is its additive valuation. -/
@[simp]
theorem coeff_sUnitsValuation (S : Finset (HeightOneSpectrum (𝓞 K)))
    (u : Additive ((primesAbove (𝓞 K) (𝓞 L) ↑S).unit L))
    (w : ↥(primesAbove (𝓞 K) (𝓞 L) ↑S)) :
    (dsimp% only ((sUnitsValuation (K := K) (L := L) S).hom u)).coeff w =
      Multiplicative.toAdd (Set.unitValuation (primesAbove (𝓞 K) (𝓞 L) ↑S) L u.toMul w) :=
  (rfl)

end TauCeti.ClassFieldTheory
