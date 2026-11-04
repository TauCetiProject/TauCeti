/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Graded.Poincare.Basic
public import Mathlib.RingTheory.PowerSeries.Trunc

/-!
# Unbounded bigraded Ext Poincaré power series

The cohomological variable of an Ext Poincaré series is a formal power-series variable.
Only the internal support in each cohomological degree needs to be finite: the coefficient
of `tⁿ` is the Laurent polynomial with coefficient `dim_k Extⁿ(X,Y{j})` at `qʲ`.
In particular, this construction applies when the cohomological support is infinite.

Truncating this power series recovers the coefficients of the finite bigraded series.
The power series is a polynomial exactly when Ext has a uniform cohomological vanishing
bound. Its diagonal support is equivalent to off-diagonal Ext vanishing, without such a
bound. The internal exponent here is `j`; applying `LaurentPolynomial.invert` coefficientwise
gives the target-shift convention `q⁻ʲ` used for Euler characteristics.

This construction uses `TauCeti.gradedDimension` for each internal slice and Mathlib's
`PowerSeries.mk` and `PowerSeries.trunc`. It defines no infinite Euler characteristic or
evaluation of the cohomological variable at `-1`.

## References

* A. Beilinson, V. Ginzburg and W. Soergel, *Koszul duality patterns in representation theory*,
  Sections 1.2 and 2.11, for bigraded Ext and Poincaré series.
-/

public section

open scoped DirectSum

namespace TauCeti

open CategoryTheory CategoryTheory.Abelian

universe w v u t

variable {C : Type u} [Category.{v} C] [Abelian C]
  {k : Type t} [Field k] [Linear k C] [HasExt.{w} C]
  {e : C ≌ C} {X Y : C}

variable (k e) in
/-- The full bigraded Ext Poincaré series, as a formal power series in cohomological degree
with Laurent-polynomial internal coefficients. No cohomological bound is required. -/
noncomputable def bigradedExtPoincarePowerSeries
    (h : IsGradedExtInternallyFinite.{w} k e X Y) : PowerSeries (LaurentPolynomial ℤ) :=
  PowerSeries.mk fun n ↦ gradedDimension k (GradedExt.{w} e X Y n) (h.finiteLaurentSupport n)

/-- The coefficient of `tⁿ` is the graded dimension of the internal Ext family in degree `n`. -/
@[simp]
theorem coeff_bigradedExtPoincarePowerSeries
    (h : IsGradedExtInternallyFinite.{w} k e X Y) (n : ℕ) :
    PowerSeries.coeff n (bigradedExtPoincarePowerSeries k e h) =
      gradedDimension k (GradedExt.{w} e X Y n) (h.finiteLaurentSupport n) := by
  simp [bigradedExtPoincarePowerSeries]

/-- The coefficient in bidegree `(n,j)` is the actual finite dimension of `Extⁿ(X,Y{j})`. -/
theorem coeff_coeff_bigradedExtPoincarePowerSeries
    (h : IsGradedExtInternallyFinite.{w} k e X Y) (n : ℕ) (j : ℤ) :
    (PowerSeries.coeff n (bigradedExtPoincarePowerSeries k e h)).coeff j =
      Module.finrank k (GradedExt.{w} e X Y n j) := by
  simp

/-- Truncation in the cohomological variable recovers every coefficient of the existing
finite bigraded Ext Poincaré series, including the zero coefficients beyond the truncation. -/
theorem coeff_coeff_trunc_bigradedExtPoincarePowerSeries
    (h : IsGradedExtInternallyFinite.{w} k e X Y) (b n : ℕ) (j : ℤ) :
    ((PowerSeries.trunc b (bigradedExtPoincarePowerSeries k e h)).coeff n).coeff j =
      (bigradedExtPoincareSeries k e h b).coeff ((n : ℤ), j) := by
  rw [PowerSeries.coeff_trunc, coeff_bigradedExtPoincareSeries]
  split_ifs <;> simp_all

/-- A cohomological vanishing bound makes the full Poincaré series equal to its polynomial
truncation. The internal variable retains its Laurent-polynomial coefficients. -/
theorem bigradedExtPoincarePowerSeries_eq_coe_trunc
    (h : IsGradedExtInternallyFinite.{w} k e X Y) {b : ℕ}
    (hb : IsGradedExtBoundedBy.{w} e X Y b) :
    bigradedExtPoincarePowerSeries k e h =
      (PowerSeries.trunc b (bigradedExtPoincarePowerSeries k e h) :
        PowerSeries (LaurentPolynomial ℤ)) := by
  apply PowerSeries.ext
  intro n
  rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
  split_ifs with hn
  · rfl
  · rw [coeff_bigradedExtPoincarePowerSeries, gradedDimension_eq_zero_iff]
    exact fun j ↦ hb.subsingleton (Nat.le_of_not_gt hn) j

/-- The full Poincaré series comes from a polynomial exactly when the Ext groups vanish
uniformly in internal degree above some cohomological bound. -/
theorem exists_polynomial_bigradedExtPoincarePowerSeries_iff
    (h : IsGradedExtInternallyFinite.{w} k e X Y) :
    (∃ p : Polynomial (LaurentPolynomial ℤ),
      (p : PowerSeries (LaurentPolynomial ℤ)) = bigradedExtPoincarePowerSeries k e h) ↔
        IsGradedExtBounded.{w} e X Y := by
  constructor
  · rintro ⟨p, hp⟩
    refine ⟨p.natDegree + 1, ⟨fun n hn j ↦ ?_⟩⟩
    have hc : PowerSeries.coeff n (bigradedExtPoincarePowerSeries k e h) = 0 := by
      rw [← hp, Polynomial.coeff_coe]
      exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    rw [coeff_bigradedExtPoincarePowerSeries, gradedDimension_eq_zero_iff] at hc
    exact hc j
  · rintro ⟨b, hb⟩
    exact ⟨_, (bigradedExtPoincarePowerSeries_eq_coe_trunc h hb).symm⟩

/-- Diagonal support of the full series is equivalent to off-diagonal Ext vanishing.
Finite internal support supplies finite-dimensionality; no cohomological bound is used. -/
theorem diagonal_bigradedExtPoincarePowerSeries_iff
    (h : IsGradedExtInternallyFinite.{w} k e X Y) :
    (∀ (n : ℕ) (j : ℤ), (n : ℤ) ≠ j →
      (PowerSeries.coeff n (bigradedExtPoincarePowerSeries k e h)).coeff j = 0) ↔
        ∀ (n : ℕ) (j : ℤ), (n : ℤ) ≠ j →
          Subsingleton (GradedExt.{w} e X Y n j) := by
  constructor
  · intro hdiag n j hnj
    let _ := (h.finiteLaurentSupport n).finiteDimensional j
    rw [← Module.finrank_zero_iff (R := k)]
    exact_mod_cast (by simpa using hdiag n j hnj :
      (Module.finrank k (GradedExt.{w} e X Y n j) : ℤ) = 0)
  · intro hoff n j hnj
    let _ := hoff n j hnj
    simp [Module.finrank_zero_of_subsingleton]

/-- Forgetting the internal degree by setting `q = 1` gives the ordinary formal Poincaré
series of the total Ext dimensions. The cohomological variable remains formal. -/
theorem map_laurentEval_one_bigradedExtPoincarePowerSeries
    (h : IsGradedExtInternallyFinite.{w} k e X Y) :
    PowerSeries.map (laurentEval (1 : ℤˣ)).toRingHom
      (bigradedExtPoincarePowerSeries k e h) =
        PowerSeries.mk fun n ↦ (Module.finrank k (⨁ j, GradedExt.{w} e X Y n j) : ℤ) := by
  apply PowerSeries.ext
  intro n
  simp

/-- The coefficient of `tⁿ` in the internally specialized series is the total finite
dimension of the internal Ext pieces in cohomological degree `n`. -/
theorem coeff_map_laurentEval_one_bigradedExtPoincarePowerSeries
    (h : IsGradedExtInternallyFinite.{w} k e X Y) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.map (laurentEval (1 : ℤˣ)).toRingHom
      (bigradedExtPoincarePowerSeries k e h)) =
        Module.finrank k (⨁ j, GradedExt.{w} e X Y n j) := by
  simp

/-- The formal substitution `t ↦ -t` introduces the alternating signs needed for the
Cartan–Poincaré comparison, without summing infinitely many cohomological dimensions. -/
theorem rescale_neg_one_map_laurentEval_one_bigradedExtPoincarePowerSeries
    (h : IsGradedExtInternallyFinite.{w} k e X Y) :
    PowerSeries.rescale (-1 : ℤ) (PowerSeries.map (laurentEval (1 : ℤˣ)).toRingHom
      (bigradedExtPoincarePowerSeries k e h)) =
        PowerSeries.mk fun n ↦
          (-1 : ℤ) ^ n * Module.finrank k (⨁ j, GradedExt.{w} e X Y n j) := by
  rw [map_laurentEval_one_bigradedExtPoincarePowerSeries, PowerSeries.rescale_mk]

/-- For a diagonally supported series, forgetting internal degree retains exactly the
diagonal Ext dimensions. This identifies the ordinary formal Poincaré series with the
diagonal series without introducing a separate construction. -/
theorem map_laurentEval_one_bigradedExtPoincarePowerSeries_of_diagonal
    (h : IsGradedExtInternallyFinite.{w} k e X Y)
    (hdiag : ∀ (n : ℕ) (j : ℤ), (n : ℤ) ≠ j →
      (PowerSeries.coeff n (bigradedExtPoincarePowerSeries k e h)).coeff j = 0) :
    PowerSeries.map (laurentEval (1 : ℤˣ)).toRingHom
      (bigradedExtPoincarePowerSeries k e h) =
        PowerSeries.mk fun n ↦ (Module.finrank k (GradedExt.{w} e X Y n n) : ℤ) := by
  have hoff := (diagonal_bigradedExtPoincarePowerSeries_iff h).1 hdiag
  apply PowerSeries.ext
  intro n
  rw [PowerSeries.coeff_map, coeff_bigradedExtPoincarePowerSeries,
    gradedDimension_eq_sum _ {(n : ℤ)} (fun j hj ↦
      hoff n j (Ne.symm (Finset.notMem_singleton.mp hj)))]
  simp

/-- The full bigraded Ext Poincaré matrix of an arbitrary family of objects, with no common
cohomological vanishing bound and no finiteness requirement on the indexing type. -/
noncomputable def bigradedExtPoincarePowerSeriesMatrix {I : Type*} (S : I → C)
    (h : ∀ i j, IsGradedExtInternallyFinite.{w} k e (S i) (S j)) :
    Matrix I I (PowerSeries (LaurentPolynomial ℤ)) :=
  fun i j ↦ bigradedExtPoincarePowerSeries k e (h i j)

/-- An entry of the full power-series matrix is the series of the corresponding pair. -/
@[simp]
theorem bigradedExtPoincarePowerSeriesMatrix_apply {I : Type*} (S : I → C)
    (h : ∀ i j, IsGradedExtInternallyFinite.{w} k e (S i) (S j)) (i j : I) :
    bigradedExtPoincarePowerSeriesMatrix S h i j =
      bigradedExtPoincarePowerSeries k e (h i j) := (rfl)

end TauCeti
