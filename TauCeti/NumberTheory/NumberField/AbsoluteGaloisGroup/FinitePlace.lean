/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.AbsoluteValue.Place
public import TauCeti.Analysis.AbsoluteValue.ValuationSubring
public import TauCeti.NumberTheory.NumberField.AbsoluteGaloisGroup.ValuationSubring

import Mathlib.RingTheory.Ideal.GoingUp
import TauCeti.NumberTheory.NumberField.PlacesOver.ValuationSubring

/-!
# Finite places of `F^alg` and maximal ideals of the algebraic integers

Let `F` be a number field, `F^alg = AlgebraicClosure F`, `G_F = Field.absoluteGaloisGroup F` and
`O` the integral closure of `𝓞 F` in `F^alg`. A finite place `w` of `F^alg` (an
`AbsoluteValue.Place` with `IsNonarchimedean w.val`) cuts out the maximal ideal
`Q_w = {x ∈ O | w x < 1}` of `O`. This file proves that `w ↦ Q_w` is a `G_F`-equivariant bijection
from the finite places of `F^alg` onto the maximal ideals of `O`
(`TauCeti.GaloisRep.finitePlaceEquivMaximalIdeal`), and that the valuation subring `A_w` of `w` is
centred at `Q_w`, so that `A_w` is the localization `O_{Q_w}`
(`ValuationSubring.IsCenteredAt.eq_valuationSubringAtPrime`).

The bijection is the composite of two others. Finite places of `F^alg` are the valuation subrings
of `F^alg` other than `F^alg` (`AbsoluteValue.Place.finitePlaceEquivValuationSubring`, since
`F^alg` is algebraic over `ℚ`), and valuation subrings of `F^alg` are primes of `O` through their
centres (`TauCeti.GaloisRep.valuationSubringEquivPrimeSpectrum`); under the latter the proper
valuation subrings are the nonzero primes, which are the maximal ideals of `O`.

## Main results

* `TauCeti.GaloisRep.finitePlaceEquivMaximalIdeal`: finite places of `F^alg` are maximal ideals of
  `O`, with `x ∈ Q_w ↔ w x < 1` (`TauCeti.GaloisRep.mem_finitePlaceEquivMaximalIdeal_iff`).
* `TauCeti.GaloisRep.isCenteredAt_finitePlaceEquivMaximalIdeal`: `A_w` is centred at `Q_w`.
* `TauCeti.GaloisRep.valuationSubring_finitePlaceEquivMaximalIdeal_symm_apply`: the place
  corresponding to a maximal ideal `Q` has valuation subring `O_Q`.
* `TauCeti.GaloisRep.finitePlaceEquivMaximalIdeal_smul`: the bijection is `G_F`-equivariant.

## References

* J. Neukirch, *Algebraic Number Theory*, Springer, 1999, Chapter II, §§3, 8 and 9.
-/

public section

open AbsoluteValue NumberField Pointwise

namespace TauCeti.GaloisRep

variable (F : Type*) [Field F] [NumberField F]

/-- `F^alg` is algebraic over `ℚ`. -/
instance instIsAlgebraicRatAlgebraicClosure : Algebra.IsAlgebraic ℚ (AlgebraicClosure F) :=
  Algebra.IsAlgebraic.trans ℚ F (AlgebraicClosure F)

variable {F}

/-- The centre `Q_w` on `O` of the valuation subring of a finite place `w` of `F^alg`. -/
private noncomputable abbrev centre
    (w : {w : Place (AlgebraicClosure F) // IsNonarchimedean w.val}) :
    Ideal (integralClosure (𝓞 F) (AlgebraicClosure F)) :=
  (valuationSubringEquivPrimeSpectrum F (w.val.val.valuationSubring w.property)).asIdeal

private theorem mem_centre_iff (w : {w : Place (AlgebraicClosure F) // IsNonarchimedean w.val})
    (b : integralClosure (𝓞 F) (AlgebraicClosure F)) :
    b ∈ centre w ↔ w.val.val (b : AlgebraicClosure F) < 1 := by
  rw [centre, asIdeal_valuationSubringEquivPrimeSpectrum_apply, Valuation.mem_centerIdeal,
    ← ValuationSubring.mem_nonunits_iff, mem_nonunits_valuationSubring_iff,
    Subalgebra.algebraMap_apply]

/-- The centre of a finite place on `O` is a maximal ideal. -/
private theorem isMaximal_centre (w : {w : Place (AlgebraicClosure F) // IsNonarchimedean w.val}) :
    (centre w).IsMaximal := by
  obtain ⟨p, _, hp⟩ := w.val.isNonarchimedean_iff.mp w.property
  have hpQ : (p : integralClosure (𝓞 F) (AlgebraicClosure F)) ∈ centre w := by
    rw [mem_centre_iff]
    simpa using Place.apply_natCast_lt_one_of_under_eq_padic hp
  have hp0 : (p : integralClosure (𝓞 F) (AlgebraicClosure F)) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hunder : (centre w).under (𝓞 F) ≠ ⊥ :=
    Ideal.under_ne_bot_of_integral_mem hp0 hpQ (Algebra.IsIntegral.isIntegral _)
  have := Ideal.IsPrime.isMaximal (Ideal.IsPrime.under (𝓞 F) (centre w)) hunder
  exact Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := 𝓞 F) _ this

variable (F) in
/-- **Finite places of `F^alg` are maximal ideals of `O`.** The map `w ↦ Q_w = {x ∈ O | w x < 1}`
is a bijection from the finite places of `F^alg` onto the maximal ideals of the integral closure
`O` of `𝓞 F` in `F^alg`. -/
noncomputable def finitePlaceEquivMaximalIdeal :
    {w : Place (AlgebraicClosure F) // IsNonarchimedean w.val} ≃
      {Q : Ideal (integralClosure (𝓞 F) (AlgebraicClosure F)) // Q.IsMaximal} :=
  .ofBijective (fun w ↦ ⟨centre w, isMaximal_centre w⟩) <| by
    refine ⟨fun v w h ↦ Subtype.ext <| Place.eq_of_valuationSubring_eq v.property w.property <|
      (valuationSubringEquivPrimeSpectrum F).injective <| PrimeSpectrum.ext <|
        congrArg Subtype.val h, fun Q ↦ ?_⟩
    have := Q.property.isPrime
    set A := (valuationSubringEquivPrimeSpectrum F).symm ⟨Q.val, this⟩ with hA
    have hc : A.IsCenteredAt Q.val := by
      rw [hA, valuationSubringEquivPrimeSpectrum_symm_apply]
      exact Ideal.isCenteredAt_valuationSubringAtPrime
    -- `Q` is nonzero since `O` is not a field, so its localization `A` is proper
    have hQ : Q.val ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField Q.property
      ((Algebra.IsIntegral.isField_iff_isField
        (FaithfulSMul.algebraMap_injective (𝓞 F) _)).not.mp (RingOfIntegers.not_isField F))
    obtain ⟨w, hw, hwA⟩ := Place.exists_valuationSubring_eq <|
      hc.ne_top_of_ne_bot (FaithfulSMul.algebraMap_injective _ _) hQ
    refine ⟨⟨w, hw⟩, Subtype.ext ?_⟩
    dsimp only [centre]
    rw [hwA, hA, Equiv.apply_symm_apply]

/-- `Q_w` is the centre on `O` of the valuation subring of `w`. -/
theorem coe_finitePlaceEquivMaximalIdeal_apply
    (w : {w : Place (AlgebraicClosure F) // IsNonarchimedean w.val}) :
    (finitePlaceEquivMaximalIdeal F w).val =
      (valuationSubringEquivPrimeSpectrum F (w.val.val.valuationSubring w.property)).asIdeal :=
  (rfl)

/-- `Q_w` consists of the elements `x` of `O` with `w x < 1`. -/
@[simp]
theorem mem_finitePlaceEquivMaximalIdeal_iff
    (w : {w : Place (AlgebraicClosure F) // IsNonarchimedean w.val})
    (b : integralClosure (𝓞 F) (AlgebraicClosure F)) :
    b ∈ (finitePlaceEquivMaximalIdeal F w).val ↔ w.val.val (b : AlgebraicClosure F) < 1 :=
  mem_centre_iff w b

/-- **The valuation subring of a finite place is centred at `Q_w`**, so it is the localization
`O_{Q_w}` (`ValuationSubring.IsCenteredAt.eq_valuationSubringAtPrime`). -/
theorem isCenteredAt_finitePlaceEquivMaximalIdeal
    (w : {w : Place (AlgebraicClosure F) // IsNonarchimedean w.val}) :
    (w.val.val.valuationSubring w.property).IsCenteredAt
      (finitePlaceEquivMaximalIdeal F w).val := by
  rw [coe_finitePlaceEquivMaximalIdeal_apply, asIdeal_valuationSubringEquivPrimeSpectrum_apply]
  exact ValuationSubring.isCenteredAt_centerIdeal _ _

/-- The finite place corresponding to a maximal ideal `Q` of `O` has valuation subring `O_Q`. -/
@[simp]
theorem valuationSubring_finitePlaceEquivMaximalIdeal_symm_apply
    (Q : {Q : Ideal (integralClosure (𝓞 F) (AlgebraicClosure F)) // Q.IsMaximal}) :
    ((finitePlaceEquivMaximalIdeal F).symm Q).val.val.valuationSubring
        ((finitePlaceEquivMaximalIdeal F).symm Q).property =
      (valuationSubringEquivPrimeSpectrum F).symm ⟨Q.val, Q.property.isPrime⟩ := by
  rw [Equiv.eq_symm_apply, PrimeSpectrum.ext_iff, ← coe_finitePlaceEquivMaximalIdeal_apply,
    Equiv.apply_symm_apply]

/-- **The bijection is `G_F`-equivariant**: `Q_{σ • w} = σ • Q_w`. -/
theorem finitePlaceEquivMaximalIdeal_smul (σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F)
    (w : {w : Place (AlgebraicClosure F) // IsNonarchimedean w.val}) :
    (finitePlaceEquivMaximalIdeal F
        ⟨σ • w.val, by rw [Place.val_smul, isNonarchimedean_smul_iff]; exact w.property⟩).val =
      σ • (finitePlaceEquivMaximalIdeal F w).val := by
  ext b
  rw [mem_finitePlaceEquivMaximalIdeal_iff, Ideal.mem_pointwise_smul_iff_inv_smul_mem,
    mem_finitePlaceEquivMaximalIdeal_iff, Place.val_smul, AbsoluteValue.smul_apply,
    integralClosure.coe_smul]

end TauCeti.GaloisRep
