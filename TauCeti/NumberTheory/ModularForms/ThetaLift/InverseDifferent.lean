/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.CMField.AdeleStar
public import Mathlib.RingTheory.DedekindDomain.Different
import TauCeti.NumberTheory.ModularForms.ThetaLift.WeilIdele

/-!
# The inverse different of the finite Weil idele

When the different has generator `δ * x`, the idele `α` obtained by selecting the inverse of
`x` at the primes containing `β` satisfies `(-1/δ) α (conj α) Ô = 𝔇⁻¹ Ô`. This supplies the
fractional-ideal identity in the Weil data for the lattice vacuum.

The normalization is that of `New.Parameters.v_weilData_j_mul_alpha_mul_star` in
`New/Derivatives/Field/WeilData.lean` of [lsernau/grh-lean](https://github.com/lsernau/grh-lean)
(revision `72fead1`).
-/

public section

open IsDedekindDomain IsDedekindDomain.FiniteAdeleRing NumberField NumberField.IsCMField
open scoped NumberField.AdeleRing nonZeroDivisors

namespace TauCeti

open Classical in
/-- Suppose `δ * x` generates the absolute different, the ideal `(x)` is invariant under
conjugation, and `β` and its conjugate are coprime and cover the primes dividing `x`. The
finite Weil idele selected by `β` gives the inverse different after multiplying by its
conjugate and by `-δ⁻¹`. Its inverse is integral, and `x` clears its denominators. -/
theorem exists_weilFiniteIdele_inverseDifferent {E : Type*}
    [Field E] [NumberField E] [IsCMField E] {β x δ : 𝓞 E}
    (hβ : IsCoprime β (RingOfIntegers.mapRingEquiv (complexConj E).toRingEquiv β))
    (hx : Associated (RingOfIntegers.mapRingEquiv (complexConj E).toRingEquiv x) x)
    (hsupport : β * RingOfIntegers.mapRingEquiv (complexConj E).toRingEquiv β ∈
      (Ideal.span {x}).radical)
    (hD : differentIdeal ℤ (𝓞 E) = Ideal.span {δ * x}) :
    ∃ α : 𝔸ᶠ[E]ˣ,
      (∀ v : HeightOneSpectrum (𝓞 E), (α : 𝔸ᶠ[E]) v =
        if β ∈ v.asIdeal then ((x : E)⁻¹ : v.adicCompletion E) else 1) ∧
      (↑(α⁻¹) : 𝔸ᶠ[E]) ∈ integralAdeles (𝓞 E) E ∧
      algebraMap (𝓞 E) 𝔸ᶠ[E] x * (α : 𝔸ᶠ[E]) ∈ integralAdeles (𝓞 E) E ∧
      FractionalIdeal.spanSingleton (𝓞 E)⁰ (-(δ : E)⁻¹) *
        (toFractionalIdeal (α * star α) : FractionalIdeal (𝓞 E)⁰ E) =
        FractionalIdeal.dual ℤ ℚ 1 := by
  obtain ⟨α, hα, hαinv, hαmul, hval⟩ :=
    (complexConj E).toRingEquiv.exists_weilFiniteIdele hβ hx hsupport (dvd_refl x)
  refine ⟨α, hα, hαinv, hαmul, ?_⟩
  have hD' : FractionalIdeal.spanSingleton (𝓞 E)⁰ ((δ : E) * x) =
      (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E))⁻¹ := by
    have h := coeIdeal_differentIdeal (B := 𝓞 E) ℤ ℚ E
    rw [hD, FractionalIdeal.coeIdeal_span_singleton, map_mul] at h
    exact h
  have hx₀ : (x : E) ≠ 0 := by
    intro h
    apply FractionalIdeal.dual_ne_zero ℤ ℚ (one_ne_zero : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0)
    simpa [h] using (congrArg Inv.inv hD').symm
  -- The local valuation calculation identifies the fractional ideal of `α * star α`.
  let u := unitEmbedding (𝓞 E) E (Units.mk0 (x : E) hx₀)
  have htriv : toFractionalIdeal (α * star α * u) = 1 := by
    refine toFractionalIdeal_eq_one_iff.mpr fun v ↦ adicOrd_eq_zero_iff.mpr ?_
    simpa only [u, Units.val_mul, Units.coe_star, unitEmbedding_apply, Units.val_mk0,
      ← finiteAdeleConj_apply, finiteAdeleConj_def,
      ← IsScalarTower.algebraMap_apply (𝓞 E) E] using hval v
  have hI : toFractionalIdeal (α * star α) = (toFractionalIdeal u)⁻¹ := by
    rw [map_mul, ← eq_inv_iff_mul_eq_one] at htriv
    exact htriv
  rw [hI]
  dsimp only [u]
  rw [toFractionalIdeal_unitEmbedding, Units.val_inv_eq_inv_val,
    coe_toPrincipalIdeal, Units.val_mk0, FractionalIdeal.spanSingleton_inv,
    ← map_mul, neg_mul, ← mul_inv]
  have hsign : FractionalIdeal.spanSingleton (𝓞 E)⁰ (-1 : E) = 1 := by
    have h := FractionalIdeal.coeIdeal_span_singleton (S := (𝓞 E)⁰) (P := E) (-1 : 𝓞 E)
    simpa [Ideal.span_singleton_neg] using h.symm
  rw [← neg_one_mul, map_mul, hsign, one_mul, ← FractionalIdeal.spanSingleton_inv]
  simpa using congrArg Inv.inv hD'

end TauCeti
