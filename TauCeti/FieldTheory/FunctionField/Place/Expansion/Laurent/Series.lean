/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Expansion.Completion
public import TauCeti.RingTheory.LaurentSeries.Basic

/-!
# Laurent-series expansions at rational places

The completion of a function field at a rational place is isomorphic to the Laurent-series field
over the constant field.  The isomorphism is the fraction-field extension of the uniformizer
expansion of the completed valuation ring, so it sends a chosen uniformizer to `X` and restricts
to the previously constructed power-series expansion on integral elements.

This supplies the local Laurent coefficients used to define residues of differentials.  Keeping
the construction as the canonical fraction-field extension makes its behaviour on quotients and
on the valuation ring available without choosing numerator-denominator presentations.

## Main results

* `TauCeti.Place.completionEquivLaurentSeries`: the completed local field is `k((X))`.
* `TauCeti.Place.completionEquivLaurentSeries_apply_integer`: the equivalence restricts to the
  power-series expansion on the completed valuation ring.
* `TauCeti.Place.completionEquivLaurentSeries_uniformizer`: a chosen uniformizer maps to `X`.
* `TauCeti.Place.completionLaurentCoeff_ext_iff`: Laurent coefficients determine a completed
  element.
* `TauCeti.Place.completionResidue_completionEquivLaurentSeries_symm_derivative`:
  completed residues kill formal derivatives.

## Reference

H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Section IV.2.
-/

public section

open scoped LaurentSeries WithZero

namespace TauCeti.Place

variable {k F : Type*} [Field k] [Field F] [Algebra k F]
variable (P : Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1)

/-- **Laurent-series expansion at a rational place.**  A chosen uniformizer identifies the
completion of the local function field with the Laurent-series field over the constants.  This is
the fraction-field extension of `TauCeti.Place.completionIntegersEquivPowerSeries`. -/
noncomputable def completionEquivLaurentSeries : P.Completion ≃ₐ[k] LaurentSeries k :=
  IsFractionRing.algEquivOfAlgEquiv (P.completionIntegersEquivPowerSeries hP ht)

/-- Laurent-series expansion restricts to power-series expansion on the completed valuation
ring. -/
@[simp]
theorem completionEquivLaurentSeries_apply_integer (x : P.completionPlace.integers) :
    P.completionEquivLaurentSeries hP ht (x : P.Completion) =
      (P.completionIntegersEquivPowerSeries hP ht x : LaurentSeries k) := by
  rw [completionEquivLaurentSeries]
  exact IsFractionRing.algEquivOfAlgEquiv_algebraMap _ x

/-- The inverse Laurent-series expansion restricts to the inverse power-series expansion. -/
@[simp]
theorem completionEquivLaurentSeries_symm_apply_powerSeries (f : PowerSeries k) :
    (P.completionEquivLaurentSeries hP ht).symm (f : LaurentSeries k) =
      ((P.completionIntegersEquivPowerSeries hP ht).symm f : P.Completion) := by
  apply (P.completionEquivLaurentSeries hP ht).injective
  rw [AlgEquiv.apply_symm_apply, P.completionEquivLaurentSeries_apply_integer]
  simp

/-- A completed function is integral exactly when its Laurent expansion comes from a power
series. -/
@[simp]
theorem exists_powerSeries_eq_completionEquivLaurentSeries_iff_mem_integers
    (z : P.Completion) :
    (∃ f : PowerSeries k, (f : LaurentSeries k) = P.completionEquivLaurentSeries hP ht z) ↔
      z ∈ P.completionPlace.integers := by
  constructor
  · rintro ⟨f, hf⟩
    have hz : z =
        ((P.completionIntegersEquivPowerSeries hP ht).symm f : P.Completion) := by
      apply (P.completionEquivLaurentSeries hP ht).injective
      rw [hf.symm, P.completionEquivLaurentSeries_apply_integer, AlgEquiv.apply_symm_apply]
    rw [hz]
    exact Subtype.property _
  · intro hz
    exact ⟨P.completionIntegersEquivPowerSeries hP ht ⟨z, hz⟩,
      (P.completionEquivLaurentSeries_apply_integer hP ht ⟨z, hz⟩).symm⟩

/-- The chosen uniformizer maps to the Laurent-series variable. -/
@[simp]
theorem completionEquivLaurentSeries_uniformizer :
    P.completionEquivLaurentSeries hP ht (P.completionEmbedding t) =
      ((PowerSeries.X : PowerSeries k) : LaurentSeries k) := by
  let t₀ : P.integers := ⟨t, P.mem_integers_iff_ord_nonneg.mpr (by omega)⟩
  let tᵢ : P.completionPlace.integers := P.completionIntegersEmbedding t₀
  rw [← show (tᵢ : P.Completion) = P.completionEmbedding t by
      exact P.completionIntegersEmbedding_apply t₀,
    P.completionEquivLaurentSeries_apply_integer]
  exact congrArg ((↑) : PowerSeries k → LaurentSeries k)
    (P.completionIntegersEquivPowerSeries_uniformizer hP ht)

/-- Laurent-series expansion preserves the normalized valuation.  Thus the power of `X` at the
first nonzero Laurent coefficient is the order at the original place. -/
@[simp]
theorem valuation_completionEquivLaurentSeries (x : P.Completion) :
    Valued.v (P.completionEquivLaurentSeries hP ht x) = P.completionPlace.valuation x := by
  let e := P.completionEquivLaurentSeries hP ht
  let w : Valuation (LaurentSeries k) ℤᵐ⁰ := Valued.v
  have hequiv : P.completionPlace.valuation.IsEquiv
      (w.comap e.toRingHom) := by
    apply Valuation.isEquiv_of_val_le_one
    intro z
    rw [Valuation.comap_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      LaurentSeries.val_le_one_iff_eq_coe]
    exact P.completionPlace.mem_integers_iff.symm.trans
      (P.exists_powerSeries_eq_completionEquivLaurentSeries_iff_mem_integers hP ht z).symm
  have hsurj : Function.Surjective
      (w.comap e.toRingHom) := by
    intro γ
    obtain ⟨y, hy⟩ := LaurentSeries.valuation_surjective k γ
    refine ⟨e.symm y, ?_⟩
    simpa [Valuation.comap_apply, e] using hy
  have hvaluation := Valuation.eq_of_isEquiv_of_surjective
    P.completionPlace.valuation_surjective hsurj hequiv
  exact DFunLike.congr_fun hvaluation.symm x

/-- Laurent-series expansion preserves the additive order, including its conventional junk value
`0` at the zero element. -/
@[simp]
theorem ord_completionEquivLaurentSeries (x : P.Completion) :
    Valuation.ord (show Valuation (LaurentSeries k) ℤᵐ⁰ from Valued.v)
        (P.completionEquivLaurentSeries hP ht x) =
      P.completionPlace.ord x := by
  rw [Valuation.ord_def, ord_def, P.valuation_completionEquivLaurentSeries hP ht]

/-! ### Completed Laurent coefficients and residues -/

/-- The `n`-th Laurent coefficient on the completed local field, with respect to the uniformizer
`t`. -/
noncomputable def completionLaurentCoeff (n : ℤ) : P.Completion →ₗ[k] k :=
  -- `toLinearMap` targets `Algebra.toModule`, but `coeff.linearMap` expects
  -- `HahnSeries.instModule`; these are not definitionally equal. This scalar bridge
  -- supplies the coefficientwise module structure without changing the public maps.
  (HahnSeries.coeff.linearMap n).comp
    ({ toFun := (P.completionEquivLaurentSeries hP ht).toAlgHom
       map_add' := (P.completionEquivLaurentSeries hP ht).toAlgHom.map_add
       map_smul' := fun c z => by
         rw [Algebra.smul_def, map_mul, AlgHom.commutes, HahnSeries.algebraMap_apply',
           PowerSeries.algebraMap_eq, HahnSeries.ofPowerSeries_C, HahnSeries.C_mul_eq_smul,
           RingHom.id_apply] } : P.Completion →ₗ[k] LaurentSeries k)

/-- The completed Laurent coefficient is the corresponding coefficient of the Laurent-series
expansion. -/
@[simp]
theorem completionLaurentCoeff_apply (n : ℤ) (z : P.Completion) :
    P.completionLaurentCoeff hP ht n z =
      (P.completionEquivLaurentSeries hP ht z).coeff n :=
  (rfl)

/-- Elements of the completed local field are equal exactly when all their Laurent coefficients
are equal. -/
theorem completionLaurentCoeff_ext_iff {x y : P.Completion} :
    x = y ↔ ∀ n : ℤ,
      P.completionLaurentCoeff hP ht n x = P.completionLaurentCoeff hP ht n y := by
  constructor
  · rintro rfl n
    rfl
  · intro h
    apply (P.completionEquivLaurentSeries hP ht).injective
    apply HahnSeries.ext
    funext n
    simpa only [completionLaurentCoeff_apply] using h n

/-- The coefficient of a Laurent monomial is zero away from its exponent. -/
theorem completionLaurentCoeff_completionEquivLaurentSeries_symm_single (m n : ℤ) (c : k) :
    P.completionLaurentCoeff hP ht n
        ((P.completionEquivLaurentSeries hP ht).symm (HahnSeries.single m c)) =
      if n = m then c else 0 := by
  simp [completionLaurentCoeff_apply, HahnSeries.coeff_single]

/-- The negative Laurent coefficients of an integral element of the completed local field
vanish. -/
theorem completionLaurentCoeff_coe_integer_eq_zero (z : P.completionPlace.integers)
    {n : ℤ} (hn : n < 0) :
    P.completionLaurentCoeff hP ht n (z : P.Completion) = 0 := by
  rw [completionLaurentCoeff_apply]
  apply LaurentSeries.coeff_zero_of_lt_valuation k (D := 0) _ hn
  rw [valuation_completionEquivLaurentSeries]
  simpa using P.completionPlace.mem_integers_iff.mp z.2

/-- The completed residue with respect to `t`, given by the coefficient of exponent `-1`. -/
noncomputable def completionResidue : P.Completion →ₗ[k] k :=
  P.completionLaurentCoeff hP ht (-1)

/-- The completed residue is the coefficient of exponent `-1`. -/
@[simp]
theorem completionResidue_apply (z : P.Completion) :
    P.completionResidue hP ht z =
      (P.completionEquivLaurentSeries hP ht z).coeff (-1) :=
  (rfl)

/-- The completed residue vanishes on the completed valuation ring. -/
theorem completionResidue_coe_integer_eq_zero
    (z : P.completionPlace.integers) :
    P.completionResidue hP ht (z : P.Completion) = 0 :=
  P.completionLaurentCoeff_coe_integer_eq_zero hP ht z (by omega)

/-- The coefficient of `X⁻¹` in the formal derivative of a Laurent series is zero.  Equivalently,
the local residue kills formal derivatives. -/
theorem completionResidue_completionEquivLaurentSeries_symm_derivative (f : LaurentSeries k) :
    P.completionResidue hP ht
        ((P.completionEquivLaurentSeries hP ht).symm (LaurentSeries.derivative k f)) = 0 := by
  simp [completionResidue_apply, LaurentSeries.derivative_apply]

end TauCeti.Place
