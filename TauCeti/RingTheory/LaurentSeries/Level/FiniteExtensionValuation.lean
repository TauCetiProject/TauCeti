/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.LaurentSeries.Level.Valuation
public import TauCeti.RingTheory.LaurentSeries.Puiseux.FiniteExtension
public import TauCeti.RingTheory.RamificationInertia.Bijective

/-!
# Valuation integers of finite Laurent extensions

For an algebraically closed field `K` of characteristic zero, a finite extension `L` of
`K⸨t⸩` of degree `e` is isomorphic to the ramified level `K⸨u⸩`, with `u ^ e = t`.
The normalized `u`-adic valuation transported to `L` is independent of this isomorphism:
two choices differ by a Kummer automorphism, which rescales coefficients by units and
therefore preserves the valuation.

This file constructs that valuation, describes its integers through any level isomorphism,
and identifies its residue field with `K`. The valuation integers form a discrete valuation
ring with ramification index `e` over the base integer ring. The residue of an integer is
the constant coefficient of its Laurent expansion in `u`; this coefficient too is independent
of the chosen isomorphism. No topology on `K` is used.

The finite-extension classification and the Kummer description are supplied by
`Level.algEquivOfFinrankEq` and `Level.kummer_surjective`; the integer-ring and residue-field
computations on a level are those of `Level.Valuation`.
-/

public section

open IsLocalRing Module
open scoped LaurentSeries WithZero

namespace TauCeti.LaurentSeries.Level

section FiniteExtension

variable {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
  {L : Type*} [Field L] [Algebra K⸨X⸩ L] {e : ℕ+}

/-- The normalized discrete valuation on an extension of `K⸨t⸩` of degree `e`, transported
from its ramified level. A level uniformizer has value `exp (-1)`, so the base parameter has
value `exp (-e)`. The valuation is independent of the chosen level isomorphism. -/
noncomputable def valuationOfFinrankEq (h : finrank K⸨X⸩ L = e) : Valuation L ℤᵐ⁰ :=
  (valuation K e).comap (algEquivOfFinrankEq h).toRingHom

/-- The valuation of a finite extension is computed through any isomorphism with its level. -/
theorem valuationOfFinrankEq_apply (h : finrank K⸨X⸩ L = e)
    (φ : L ≃ₐ[K⸨X⸩] Level K e) (x : L) :
    valuationOfFinrankEq h x = valuation K e (φ x) :=
  valuation_apply_eq_of_algEquiv _ φ x

/-- The normalized valuation is natural under isomorphisms of finite Laurent extensions. -/
@[simp]
theorem valuationOfFinrankEq_algEquiv_apply {L' : Type*} [Field L'] [Algebra K⸨X⸩ L']
    (h : finrank K⸨X⸩ L = e) (h' : finrank K⸨X⸩ L' = e) (ψ : L ≃ₐ[K⸨X⸩] L') (x : L) :
    valuationOfFinrankEq h' (ψ x) = valuationOfFinrankEq h x := by
  rw [valuationOfFinrankEq_apply h' (ψ.symm.trans (algEquivOfFinrankEq h)),
    valuationOfFinrankEq_apply h (algEquivOfFinrankEq h), AlgEquiv.trans_apply,
    AlgEquiv.symm_apply_apply]

/-- On the base field the normalized extension valuation is the `e`-th power of the original
Laurent valuation. -/
@[simp]
theorem valuationOfFinrankEq_algebraMap (h : finrank K⸨X⸩ L = e) (f : K⸨X⸩) :
    valuationOfFinrankEq h (Algebra.algebraMap K⸨X⸩ L f) = Valued.v f ^ (e : ℕ) := by
  rw [valuationOfFinrankEq_apply h (algEquivOfFinrankEq h), AlgEquiv.commutes,
    valuation_algebraMap]

/-- The normalized valuation extends the base valuation, with the normalization allowed by
`Valuation.HasExtension`. -/
instance hasExtension_valuationOfFinrankEq (h : finrank K⸨X⸩ L = e) :
    (Valued.v : Valuation K⸨X⸩ ℤᵐ⁰).HasExtension (valuationOfFinrankEq h) where
  val_isEquiv_comap := by
    rw [Valuation.isEquiv_iff_val_le_one]
    intro f
    simp [pow_le_one_iff_of_nonneg zero_le e.ne_zero]

/-- The normalized discrete valuation on a finite extension is surjective. -/
theorem valuationOfFinrankEq_surjective (h : finrank K⸨X⸩ L = e) :
    Function.Surjective (valuationOfFinrankEq h) := by
  intro γ
  obtain ⟨x, hx⟩ := valuation_surjective K e γ
  exact ⟨(algEquivOfFinrankEq h).symm x, by
    simpa [valuationOfFinrankEq_apply h (algEquivOfFinrankEq h)] using hx⟩

/-- The valuation integers of a finite Laurent extension form a discrete valuation ring. -/
instance (h : finrank K⸨X⸩ L = e) :
    IsDiscreteValuationRing (valuationOfFinrankEq h).valuationSubring :=
  Valuation.valuationSubring_isDiscreteValuationRing_of_surjective _
    (valuationOfFinrankEq_surjective h)

/-- An element of a finite extension is an integer exactly when its level expansion is a
power series. -/
theorem mem_valuationOfFinrankEq_valuationSubring_iff (h : finrank K⸨X⸩ L = e)
    (φ : L ≃ₐ[K⸨X⸩] Level K e) (x : L) :
    x ∈ (valuationOfFinrankEq h).valuationSubring ↔
      ringEquivLaurentSeries K e (φ x) ∈ _root_.LaurentSeries.powerSeries_as_subring K := by
  rw [ringEquivLaurentSeries_mem_powerSeries_as_subring_iff,
    Valuation.mem_valuationSubring_iff, Valuation.mem_valuationSubring_iff,
    valuationOfFinrankEq_apply h φ]

/-- A level isomorphism restricts to an isomorphism of the valuation integer rings over the
base integer ring. -/
noncomputable def valuationSubringEquivOfFinrankEq (h : finrank K⸨X⸩ L = e)
    (φ : L ≃ₐ[K⸨X⸩] Level K e) :
    (valuationOfFinrankEq h).valuationSubring ≃ₐ[
      (Valued.v : Valuation K⸨X⸩ ℤᵐ⁰).valuationSubring] (valuation K e).valuationSubring :=
  AlgEquiv.ofRingEquiv
    (f := φ.toRingEquiv.restrict _ _ fun x ↦ by
      simp [Valuation.mem_valuationSubring_iff, valuationOfFinrankEq_apply h φ])
    fun a ↦ Subtype.ext (φ.commutes a)

/-- The restricted integer-ring isomorphism acts by the original level isomorphism. -/
@[simp]
theorem coe_valuationSubringEquivOfFinrankEq (h : finrank K⸨X⸩ L = e)
    (φ : L ≃ₐ[K⸨X⸩] Level K e) (x : (valuationOfFinrankEq h).valuationSubring) :
    (valuationSubringEquivOfFinrankEq h φ x : Level K e) = φ x :=
  (rfl)

/-- The inverse integer-ring isomorphism acts by the inverse level isomorphism. -/
@[simp]
theorem coe_valuationSubringEquivOfFinrankEq_symm (h : finrank K⸨X⸩ L = e)
    (φ : L ≃ₐ[K⸨X⸩] Level K e) (x : (valuation K e).valuationSubring) :
    ((valuationSubringEquivOfFinrankEq h φ).symm x : L) = φ.symm x :=
  (rfl)

/-- The residue field of a finite Laurent extension is the coefficient field `K`. -/
noncomputable def residueFieldEquivOfFinrankEq (h : finrank K⸨X⸩ L = e) :
    ResidueField (valuationOfFinrankEq h).valuationSubring ≃+* K :=
  (ResidueField.mapEquiv
    (valuationSubringEquivOfFinrankEq h (algEquivOfFinrankEq h)).toRingEquiv).trans
    (residueFieldEquiv K e)

/-- The residue of an integer is the constant coefficient of its chosen level expansion. -/
@[simp]
theorem residueFieldEquivOfFinrankEq_residue (h : finrank K⸨X⸩ L = e)
    (x : (valuationOfFinrankEq h).valuationSubring) :
    residueFieldEquivOfFinrankEq h (residue _ x) =
      (ringEquivLaurentSeries K e (algEquivOfFinrankEq h x)).coeff 0 := by
  simp [residueFieldEquivOfFinrankEq]

/-- In any level expansion, the residue of an integer is its constant coefficient. -/
theorem residueFieldEquivOfFinrankEq_residue_eq_coeff (h : finrank K⸨X⸩ L = e)
    (φ : L ≃ₐ[K⸨X⸩] Level K e) (x : (valuationOfFinrankEq h).valuationSubring) :
    residueFieldEquivOfFinrankEq h (residue _ x) =
      (ringEquivLaurentSeries K e (φ x)).coeff 0 := by
  rw [residueFieldEquivOfFinrankEq_residue]
  exact coeff_zero_apply_eq_of_algEquiv _ φ x

/-- The ramification index of an extension of degree `e` is `e`, with respect to the
normalized discrete valuation. -/
theorem ramificationIdx_valuationOfFinrankEq (h : finrank K⸨X⸩ L = e) :
    (maximalIdeal (valuationOfFinrankEq h).valuationSubring).ramificationIdx
      (Valued.v : Valuation K⸨X⸩ ℤᵐ⁰).valuationSubring = e := by
  let φ := valuationSubringEquivOfFinrankEq h (algEquivOfFinrankEq h)
  have he := Ideal.ramificationIdx_map_algEquiv φ
    (maximalIdeal (valuationOfFinrankEq h).valuationSubring)
  have hm : (maximalIdeal (valuationOfFinrankEq h).valuationSubring).map φ =
      maximalIdeal (valuation K e).valuationSubring := by
    simpa only [Ideal.map, AlgEquiv.coe_toRingEquiv] using
      IsLocalRing.map_ringEquiv_maximalIdeal φ.toRingEquiv
  rw [hm] at he
  exact he.symm.trans (ramificationIdx_maximalIdeal K e)

end FiniteExtension

end TauCeti.LaurentSeries.Level
