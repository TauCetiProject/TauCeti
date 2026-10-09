/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Expansion.Completion
public import TauCeti.RingTheory.LaurentSeries

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

end TauCeti.Place
