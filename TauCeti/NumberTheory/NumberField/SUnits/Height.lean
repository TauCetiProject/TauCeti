/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Height.FiniteOrder
public import TauCeti.NumberTheory.Height.SInteger
public import TauCeti.NumberTheory.NumberField.Global.Places.Height
public import TauCeti.NumberTheory.NumberField.SUnits.LogEmbedding

/-!
# Heights of S-units and the kernel of the S-logarithmic embedding

Let `S` be a finite set of finite places of a number field `K`. The `S`-logarithmic embedding
`TauCeti.NumberField.SUnit.logEmbedding S` records the weighted logarithms of an `S`-unit at the
infinite places other than Mathlib's distinguished place `w₀`, and its logarithms at the places
of `S`. The vector of all weighted logarithms of an `S`-unit, over `S` and every infinite place,
has `ℓ¹` norm twice the logarithmic height, and the product formula recovers the omitted
coordinate at `w₀` as minus the sum of the kept ones. Hence

`2 * logHeight₁ x = ∑ i, |logEmbedding S x i| + |∑ i, logEmbedding S x i|`,

which compares the height of an `S`-unit with the `ℓ¹` and supremum norms of its image.

As a consequence the kernel of the `S`-logarithmic embedding is the torsion subgroup of the
`S`-units: an `S`-unit with vanishing image has height zero, and by Kronecker's theorem an element
of height zero is a root of unity. This is the `S`-analogue of Mathlib's
`NumberField.Units.dirichletUnitTheorem.logEmbedding_ker`. By the first isomorphism theorem, the
`S`-logarithmic embedding is therefore injective on the quotient of the `S`-units by torsion.

## Main results

* `TauCeti.NumberField.SUnit.two_mul_logHeight₁_eq_sum_abs_logEmbedding`: the height of an
  `S`-unit in terms of its `S`-logarithmic embedding.
* `TauCeti.NumberField.SUnit.sum_abs_logEmbedding_le_two_mul_logHeight₁` and
  `TauCeti.NumberField.SUnit.logHeight₁_le_sum_abs_logEmbedding`: the two-sided `ℓ¹` comparison.
* `TauCeti.NumberField.SUnit.norm_logEmbedding_le_logHeight₁` and
  `TauCeti.NumberField.SUnit.logHeight₁_le_mul_norm_logEmbedding`: the supremum-norm comparison.
* `TauCeti.NumberField.SUnit.logHeight₁_eq_zero_iff`: an `S`-unit has height zero exactly when it
  is torsion.
* `TauCeti.NumberField.SUnit.logEmbedding_eq_zero_iff` and
  `TauCeti.NumberField.SUnit.logEmbedding_ker`: the kernel of the `S`-logarithmic embedding is
  the torsion subgroup of the `S`-units.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press, 2006,
  §1.5 (Kronecker's theorem 1.5.9 and the `S`-unit theorem 1.5.13).
* Y. Bugeaud and K. Győry, *Bounds for the solutions of unit equations*, Acta Arith. **74**
  (1996), 67–80, §3, formula (12).
-/

public section

open Finset Height IsDedekindDomain NumberField NumberField.InfinitePlace
  NumberField.Units.dirichletUnitTheorem

namespace TauCeti.NumberField.SUnit

variable {K : Type*} [Field K] [NumberField K]

/-! ### Height zero and torsion -/

section Torsion

variable {S : Set (HeightOneSpectrum (𝓞 K))}

/-- An `S`-unit has multiplicative height one exactly when it is torsion. -/
@[simp]
theorem mulHeight₁_eq_one_iff (x : S.unit K) :
    mulHeight₁ ((x : Kˣ) : K) = 1 ↔ x ∈ CommGroup.torsion (S.unit K) := by
  rw [Height.mulHeight₁_eq_one_iff, or_iff_right (x : Kˣ).ne_zero, CommGroup.mem_torsion,
    Units.isOfFinOrder_val]
  exact Submonoid.isOfFinOrder_coe

/-- An `S`-unit has logarithmic height zero exactly when it is torsion. -/
@[simp]
theorem logHeight₁_eq_zero_iff (x : S.unit K) :
    logHeight₁ ((x : Kˣ) : K) = 0 ↔ x ∈ CommGroup.torsion (S.unit K) := by
  rw [Height.logHeight₁_eq_zero_iff, or_iff_right (x : Kˣ).ne_zero, CommGroup.mem_torsion,
    Units.isOfFinOrder_val]
  exact Submonoid.isOfFinOrder_coe

end Torsion

/-! ### The height in `S`-logarithmic coordinates -/

section Height

variable (S : Finset (HeightOneSpectrum (𝓞 K)))

open Classical in
/-- Twice the logarithmic height of an `S`-unit is the `ℓ¹` norm of its `S`-logarithmic
embedding plus the absolute value of the omitted coordinate, which is the absolute value of the
sum of the kept coordinates. -/
theorem two_mul_logHeight₁_eq_sum_abs_logEmbedding
    (x : (S : Set (HeightOneSpectrum (𝓞 K))).unit K) :
    2 * logHeight₁ ((x : Kˣ) : K) =
      ∑ i, |logEmbedding S (Additive.ofMul x) i| +
        |∑ i, logEmbedding S (Additive.ofMul x) i| := by
  have hS (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S) :
      HeightOneSpectrum.adicAbv K v ((x : Kˣ) : K) = 1 := by
    rw [← FinitePlace.norm_embedding, ← FinitePlace.mk_apply]
    exact (Set.mem_unit_iff_finitePlace _ _).mp x.2 v (by simpa using hv)
  rw [GlobalNumberFields.two_mul_logHeight₁_eq_sum_abs_log_adicAbv_add_sum_mult_mul_abs_log S hS,
    sum_logEmbedding, Fintype.sum_sum_type,
    Fintype.sum_eq_add_sum_subtype_ne (fun w : InfinitePlace K ↦ w.mult * |Real.log (w _)|) w₀,
    ← Finset.sum_coe_sort S]
  simp only [logEmbedding_apply_inl, logEmbedding_apply_inr, abs_mul, abs_neg, Nat.abs_cast,
    FinitePlace.mk_apply, FinitePlace.norm_embedding]
  ring

open Classical in
/-- The `ℓ¹` norm of the `S`-logarithmic embedding of an `S`-unit is at most twice its
logarithmic height. -/
theorem sum_abs_logEmbedding_le_two_mul_logHeight₁
    (x : (S : Set (HeightOneSpectrum (𝓞 K))).unit K) :
    ∑ i, |logEmbedding S (Additive.ofMul x) i| ≤ 2 * logHeight₁ ((x : Kˣ) : K) := by
  rw [two_mul_logHeight₁_eq_sum_abs_logEmbedding]
  exact le_add_of_nonneg_right (abs_nonneg _)

open Classical in
/-- The logarithmic height of an `S`-unit is at most the `ℓ¹` norm of its `S`-logarithmic
embedding. -/
theorem logHeight₁_le_sum_abs_logEmbedding (x : (S : Set (HeightOneSpectrum (𝓞 K))).unit K) :
    logHeight₁ ((x : Kˣ) : K) ≤ ∑ i, |logEmbedding S (Additive.ofMul x) i| := by
  have h := two_mul_logHeight₁_eq_sum_abs_logEmbedding S x
  have := Finset.abs_sum_le_sum_abs (fun i ↦ logEmbedding S (Additive.ofMul x) i) univ
  linarith

open Classical in
/-- The supremum norm of the `S`-logarithmic embedding of an `S`-unit is at most its logarithmic
height. -/
theorem norm_logEmbedding_le_logHeight₁ (x : (S : Set (HeightOneSpectrum (𝓞 K))).unit K) :
    ‖logEmbedding S (Additive.ofMul x)‖ ≤ logHeight₁ ((x : Kˣ) : K) := by
  refine (pi_norm_le_iff_of_nonneg (zero_le_logHeight₁ _)).mpr fun i ↦ ?_
  rw [Real.norm_eq_abs]
  cases i with
  | inl w =>
    rw [logEmbedding_apply_inl, ← Real.log_pow, ← GlobalNumberFields.normalizedAbsValue_inr]
    exact GlobalNumberFields.abs_log_normalizedAbsValue_le_logHeight₁ _ _
  | inr v =>
    rw [logEmbedding_apply_inr, FinitePlace.mk_apply, FinitePlace.norm_embedding,
      ← GlobalNumberFields.normalizedAbsValue_inl]
    exact GlobalNumberFields.abs_log_normalizedAbsValue_le_logHeight₁ _ _

open Classical in
/-- The logarithmic height of an `S`-unit is at most `rank K + #S`, the dimension of the
`S`-logarithmic space, times the supremum norm of its `S`-logarithmic embedding. -/
theorem logHeight₁_le_mul_norm_logEmbedding (x : (S : Set (HeightOneSpectrum (𝓞 K))).unit K) :
    logHeight₁ ((x : Kˣ) : K) ≤
      (NumberField.Units.rank K + #S) * ‖logEmbedding S (Additive.ofMul x)‖ := by
  have hcard : Fintype.card ({w : InfinitePlace K // w ≠ w₀} ⊕ S) =
      NumberField.Units.rank K + #S := by
    simp [NumberField.Units.rank]
  refine (logHeight₁_le_sum_abs_logEmbedding S x).trans ?_
  calc ∑ i, |logEmbedding S (Additive.ofMul x) i|
      ≤ Fintype.card ({w : InfinitePlace K // w ≠ w₀} ⊕ S) •
          ‖logEmbedding S (Additive.ofMul x)‖ :=
        Finset.sum_le_card_nsmul _ _ _ fun i _ ↦ by
          simpa only [Real.norm_eq_abs] using norm_le_pi_norm (logEmbedding S _) i
    _ = (NumberField.Units.rank K + #S) * ‖logEmbedding S (Additive.ofMul x)‖ := by
        rw [hcard, nsmul_eq_mul, Nat.cast_add]

/-! ### The kernel -/

/-- The logarithmic height of an `S`-unit vanishes exactly when its `S`-logarithmic embedding
does. -/
theorem logHeight₁_eq_zero_iff_logEmbedding_eq_zero
    (x : (S : Set (HeightOneSpectrum (𝓞 K))).unit K) :
    logHeight₁ ((x : Kˣ) : K) = 0 ↔ logEmbedding S (Additive.ofMul x) = 0 := by
  classical
  refine ⟨fun h ↦ norm_le_zero_iff.mp ((norm_logEmbedding_le_logHeight₁ S x).trans_eq h),
    fun h ↦ ?_⟩
  refine le_antisymm ?_ (zero_le_logHeight₁ _)
  simpa [h] using logHeight₁_le_mul_norm_logEmbedding S x

/-- An `S`-unit lies in the kernel of the `S`-logarithmic embedding exactly when it is torsion.
This is the `S`-analogue of `NumberField.Units.dirichletUnitTheorem.logEmbedding_eq_zero_iff`. -/
theorem logEmbedding_eq_zero_iff {x : (S : Set (HeightOneSpectrum (𝓞 K))).unit K} :
    logEmbedding S (Additive.ofMul x) = 0 ↔
      x ∈ CommGroup.torsion ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) := by
  rw [← logHeight₁_eq_zero_iff_logEmbedding_eq_zero, logHeight₁_eq_zero_iff]

/-- The kernel of the `S`-logarithmic embedding is the torsion subgroup of the `S`-units. This is
the `S`-analogue of `NumberField.Units.dirichletUnitTheorem.logEmbedding_ker`. -/
theorem logEmbedding_ker :
    (logEmbedding S).ker =
      (CommGroup.torsion ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)).toAddSubgroup := by
  ext x
  rw [AddMonoidHom.mem_ker, ← ofMul_toMul x, logEmbedding_eq_zero_iff]
  simp

end Height

end TauCeti.NumberField.SUnit
