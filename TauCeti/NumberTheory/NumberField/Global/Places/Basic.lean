/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.ProductFormula
public import TauCeti.Algebra.BigOperators.Finprod

import TauCeti.NumberTheory.NumberField.FinitePlace

/-!
# Places of a number field and their normalized absolute values

Mathlib indexes the two kinds of place of a number field `K` by two unrelated types: the finite
places by `IsDedekindDomain.HeightOneSpectrum (𝓞 K)` and the infinite places by
`NumberField.InfinitePlace K`.  Both carry an absolute value, but with different normalizations,
and the product formula `NumberField.prod_abs_eq_one` is stated as a product over the finite
places times a product over the infinite places.

This file introduces the single indexing type `TauCeti.GlobalNumberFields.Place K` for all places
of `K`, together with the normalized absolute value `‖·‖_v` attached to a place `v`, and states
the product formula as one `finprod` over that type.

The normalization is the one that makes the product formula hold with all exponents equal to one:

* at a finite place `v`, `‖x‖_v` is the `v`-adic absolute value `NumberField.HeightOneSpectrum.
  adicAbv`, that is `(N v) ^ (-v x)`;
* at a real place `w`, `‖x‖_w = |x|` computed through the real embedding;
* at a complex place `w`, `‖x‖_w = |x| ^ 2` computed through either complex embedding.

Because of the square at the complex places, `‖·‖_v` is not an `AbsoluteValue` — it does not
satisfy the triangle inequality there — so it is bundled as a `MonoidWithZeroHom`.  This is the
standard normalization: `‖·‖_v` is the module of the local field at `v`, which is what the idele
norm and the product formula require.

Heights in Diophantine approximation instead use the degree-normalized absolute value
`TauCeti.GlobalNumberFields.normAbs`, written `|·|_v`, the `[K : ℚ]`-th root of `‖·‖_v`, whose
products over the places give absolute heights.

## Main definitions

* `TauCeti.GlobalNumberFields.Place`: the places of `K`, finite and infinite together.
* `TauCeti.GlobalNumberFields.normalizedAbsValue`: the normalized absolute value at a place.
* `TauCeti.GlobalNumberFields.normAbs`: its `[K : ℚ]`-th root, the degree-normalized absolute value.

## Main results

* `TauCeti.GlobalNumberFields.forall_normalizedAbsValue_inl_le_one_iff`: an element of `K` is an
  algebraic integer exactly when its normalized absolute value is at most `1` at every finite
  place.
* `TauCeti.GlobalNumberFields.hasFiniteMulSupport_normalizedAbsValue`: a nonzero element of `K`
  has normalized absolute value `1` at all but finitely many places.
* `TauCeti.GlobalNumberFields.finprod_normalizedAbsValue_eq_one`: the product formula, as a single
  product over all places of `K`; `TauCeti.GlobalNumberFields.finprod_normAbs_eq_one` is its
  degree-normalized form.
* `TauCeti.GlobalNumberFields.hasFiniteMulSupport_iSup_normalizedAbsValue`: a nonzero tuple has
  largest normalized absolute value `1` at all but finitely many places.

## References

* J. W. S. Cassels and A. Fröhlich, eds., *Algebraic Number Theory*, Chapter II.
* J. Neukirch, *Algebraic Number Theory*, Chapter III.
* J.-H. Evertse and R. G. Ferretti, *A further improvement of the quantitative Subspace
  Theorem*, Ann. of Math. 177 (2013), §1.1 (for `normAbs`).
-/

public section

open Function IsDedekindDomain NumberField
open scoped NNReal NumberField

namespace TauCeti.GlobalNumberFields

variable (K : Type*) [Field K] [NumberField K]

/-- A place of a number field `K`: either a finite place, indexed by a height one prime of `𝓞 K`,
or an infinite place.  This is an abbreviation for the disjoint union of Mathlib's two indexing
types; it is the uniform vocabulary in which statements ranging over *all* places of `K` (the
product formula, the restricted product defining the adeles, the idele norm) are phrased. -/
abbrev Place : Type _ := HeightOneSpectrum (𝓞 K) ⊕ InfinitePlace K

variable {K}

/-- The normalized absolute value at a place of a number field: the `v`-adic absolute value at a
finite place `v`, and `w x ^ w.mult` at an infinite place `w`, so that a real place contributes
`|x|` and a complex place contributes `|x| ^ 2`.

At a complex place this is not subadditive, so it is bundled as a `MonoidWithZeroHom` rather than
as an `AbsoluteValue`. -/
noncomputable def normalizedAbsValue : Place K → K →*₀ ℝ
  | .inl v => (NumberField.HeightOneSpectrum.adicAbv K v).toMonoidWithZeroHom
  | .inr w =>
    { toFun x := w x ^ w.mult
      map_zero' := by simp [zero_pow InfinitePlace.mult_ne_zero]
      map_one' := by simp
      map_mul' x y := by simp [mul_pow] }

@[simp]
theorem normalizedAbsValue_inl (v : HeightOneSpectrum (𝓞 K)) (x : K) :
    normalizedAbsValue (Sum.inl v) x = NumberField.HeightOneSpectrum.adicAbv K v x := (rfl)

@[simp]
theorem normalizedAbsValue_inr (w : InfinitePlace K) (x : K) :
    normalizedAbsValue (Sum.inr w) x = w x ^ w.mult := (rfl)

/-- At a real place the normalized absolute value is the absolute value itself. -/
theorem normalizedAbsValue_inr_of_isReal {w : InfinitePlace K} (hw : w.IsReal) (x : K) :
    normalizedAbsValue (Sum.inr w) x = w x := by
  simp [hw.mult_eq_one]

/-- At a complex place the normalized absolute value is the *square* of the absolute value. -/
theorem normalizedAbsValue_inr_of_isComplex {w : InfinitePlace K} (hw : w.IsComplex) (x : K) :
    normalizedAbsValue (Sum.inr w) x = w x ^ 2 := by
  simp [hw.mult_eq_two]

/-- The normalized absolute value at an infinite place, computed through a complex embedding
defining the place. -/
theorem normalizedAbsValue_inr_eq_norm_embedding (w : InfinitePlace K) (x : K) :
    normalizedAbsValue (Sum.inr w) x = ‖w.embedding x‖ ^ w.mult := by
  rw [normalizedAbsValue_inr, InfinitePlace.norm_embedding_eq]

/-- The normalized absolute value at a finite place `v` is the norm in the `v`-adic completion. -/
theorem normalizedAbsValue_inl_eq_norm_coe (v : HeightOneSpectrum (𝓞 K)) (x : K) :
    normalizedAbsValue (Sum.inl v) x = ‖(x : v.adicCompletion K)‖ := by
  rw [normalizedAbsValue_inl, ← FinitePlace.norm_embedding, FinitePlace.embedding_apply]

theorem normalizedAbsValue_nonneg (v : Place K) (x : K) : 0 ≤ normalizedAbsValue v x := by
  cases v with
  | inl v => exact (NumberField.HeightOneSpectrum.adicAbv K v).nonneg x
  | inr w => exact pow_nonneg (apply_nonneg w x) _

theorem normalizedAbsValue_eq_zero (v : Place K) {x : K} :
    normalizedAbsValue v x = 0 ↔ x = 0 :=
  map_eq_zero _

theorem normalizedAbsValue_pos (v : Place K) {x : K} (hx : x ≠ 0) :
    0 < normalizedAbsValue v x :=
  (normalizedAbsValue_nonneg v x).lt_of_ne fun h ↦ hx ((normalizedAbsValue_eq_zero v).mp h.symm)

section Integers

variable (v : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K)

/-- An algebraic integer has normalized absolute value at most `1` at every finite place. -/
theorem normalizedAbsValue_inl_algebraMap_le_one :
    normalizedAbsValue (Sum.inl v) (algebraMap (𝓞 K) K x) ≤ 1 := by
  rw [normalizedAbsValue_inl, ← FinitePlace.norm_embedding]
  exact FinitePlace.norm_le_one K v x

/-- An algebraic integer has normalized absolute value exactly `1` at a finite place precisely
when it avoids the corresponding prime. -/
theorem normalizedAbsValue_inl_algebraMap_eq_one_iff :
    normalizedAbsValue (Sum.inl v) (algebraMap (𝓞 K) K x) = 1 ↔ x ∉ v.asIdeal := by
  rw [normalizedAbsValue_inl, ← FinitePlace.norm_embedding]
  exact FinitePlace.norm_eq_one_iff_notMem K v x

/-- At a finite place, having normalized absolute value at most `1` is having `v`-adic valuation
at most `1`. -/
theorem normalizedAbsValue_inl_le_one_iff (y : K) :
    normalizedAbsValue (Sum.inl v) y ≤ 1 ↔ v.valuation K y ≤ 1 := by
  simpa only [normalizedAbsValue_inl, FinitePlace.mk_apply, FinitePlace.norm_embedding]
    using FinitePlace.mk_apply_le_one_iff v y

/-- An element of a number field is an algebraic integer exactly when its normalized absolute
value is at most `1` at every finite place. -/
theorem forall_normalizedAbsValue_inl_le_one_iff (y : K) :
    (∀ v : HeightOneSpectrum (𝓞 K), normalizedAbsValue (Sum.inl v) y ≤ 1) ↔
      y ∈ (algebraMap (𝓞 K) K).range := by
  refine ⟨fun h ↦ IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one K y
    fun v ↦ (normalizedAbsValue_inl_le_one_iff v y).mp (h v), ?_⟩
  rintro ⟨z, rfl⟩ v
  exact normalizedAbsValue_inl_algebraMap_le_one v z

open Ideal in
/-- The normalized absolute value of a nonzero algebraic integer at a finite place, explicitly:
the ideal norm of the prime, raised to minus the multiplicity of that prime in the principal ideal
generated by the integer. -/
theorem normalizedAbsValue_inl_algebraMap_eq_absNorm_zpow (hx : x ≠ 0) :
    normalizedAbsValue (Sum.inl v) (algebraMap (𝓞 K) K x) =
      (absNorm v.asIdeal : ℝ) ^ (-(multiplicity v.asIdeal (span {x}) : ℤ)) := by
  have h := FinitePlace.apply_mul_absNorm_pow_eq_one (FinitePlace.mk v) hx
  rw [FinitePlace.maximalIdeal_mk, FinitePlace.mk_apply, FinitePlace.norm_embedding] at h
  rw [normalizedAbsValue_inl, zpow_neg, zpow_natCast]
  exact eq_inv_of_mul_eq_one_left h

end Integers

variable {x : K}

/-- A nonzero element of a number field lies outside all but finitely many height one primes,
so its `v`-adic absolute values are almost all `1`. -/
theorem hasFiniteMulSupport_adicAbv (hx : x ≠ 0) :
    HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 K) ↦
      NumberField.HeightOneSpectrum.adicAbv K v x := by
  refine Set.Finite.subset
    (Set.Finite.image FinitePlace.maximalIdeal (FinitePlace.hasFiniteMulSupport hx)) ?_
  intro v hv
  refine ⟨FinitePlace.mk v, ?_, FinitePlace.maximalIdeal_mk v⟩
  simpa [FinitePlace.mk_apply, FinitePlace.norm_embedding] using hv

/-- A nonzero element of a number field has normalized absolute value `1` at all but finitely
many places. -/
theorem hasFiniteMulSupport_normalizedAbsValue (hx : x ≠ 0) :
    HasFiniteMulSupport fun v : Place K ↦ normalizedAbsValue v x :=
  hasFiniteMulSupport_sum_type (hasFiniteMulSupport_adicAbv hx) (Set.toFinite _)

/-- The finite part of the product formula, indexed by the height one primes of `𝓞 K`. -/
theorem finprod_normalizedAbsValue_inl (hx : x ≠ 0) :
    ∏ᶠ v : HeightOneSpectrum (𝓞 K), normalizedAbsValue (Sum.inl v) x =
      |(Algebra.norm ℚ) x|⁻¹ := by
  have h (v : HeightOneSpectrum (𝓞 K)) : normalizedAbsValue (Sum.inl v) x =
      (FinitePlace.equivHeightOneSpectrum.symm v) x := by
    rw [normalizedAbsValue_inl, FinitePlace.equivHeightOneSpectrum_symm_apply,
      FinitePlace.norm_embedding]
  rw [finprod_congr h,
    finprod_comp_equiv (FinitePlace.equivHeightOneSpectrum (K := K)).symm
      (f := fun w : FinitePlace K ↦ w x),
    FinitePlace.prod_eq_inv_abs_norm hx]

/-- **The product formula** for a number field, as a single product over all of its places, finite
and infinite, of the normalized absolute values. -/
theorem finprod_normalizedAbsValue_eq_one (hx : x ≠ 0) :
    ∏ᶠ v : Place K, normalizedAbsValue v x = 1 := by
  rw [finprod_sum_type _ (hasFiniteMulSupport_adicAbv hx) (Set.toFinite _),
    finprod_normalizedAbsValue_inl hx, finprod_eq_prod_of_fintype]
  simp only [normalizedAbsValue_inr]
  rw [InfinitePlace.prod_eq_abs_norm]
  have h0 : |(Algebra.norm ℚ) x| ≠ 0 := by simpa [Algebra.norm_eq_zero_iff] using hx
  rw [← Rat.cast_mul, inv_mul_cancel₀ h0, Rat.cast_one]

/-- A tuple of elements of a number field which is not identically zero has, at all but finitely
many places, largest normalized absolute value `1`. -/
theorem hasFiniteMulSupport_iSup_normalizedAbsValue {ι : Type*} [Finite ι] {y : ι → K}
    (hy : y ≠ 0) : HasFiniteMulSupport fun v : Place K ↦ ⨆ i, normalizedAbsValue v (y i) := by
  refine hasFiniteMulSupport_sum_type ?_ (Set.toFinite _)
  convert (FinitePlace.hasFiniteMulSupport_iSup hy).comp_of_injective
    FinitePlace.equivHeightOneSpectrum.symm.injective
  ext v
  simp [FinitePlace.equivHeightOneSpectrum_symm_apply, FinitePlace.norm_embedding]

/-! ### The degree-normalized absolute value -/

/-- The degree-normalized absolute value `|x|_v = normalizedAbsValue v x ^ (1 / [K : ℚ])` at a
place `v` of a number field `K`. At an infinite place `w` it is `w x ^ (mult w / [K : ℚ])`
(`normAbs_inr`), and at a finite place it is the `[K : ℚ]`-th root of the `v`-adic absolute value
(`normAbs_inl`).

This is the normalization of Evertse–Ferretti, in which the product of the local factors of a
height is the absolute height: it does not change when `K` is replaced by a finite extension. -/
noncomputable def normAbs (v : Place K) : K →*₀ ℝ where
  toFun x := normalizedAbsValue v x ^ ((1 : ℝ) / Module.finrank ℚ K)
  map_zero' := by
    rw [map_zero, Real.zero_rpow]
    exact one_div_ne_zero (Nat.cast_ne_zero.mpr Module.finrank_pos.ne')
  map_one' := by simp
  map_mul' x y := by
    rw [map_mul, Real.mul_rpow (normalizedAbsValue_nonneg v x) (normalizedAbsValue_nonneg v y)]

theorem normAbs_apply (v : Place K) (x : K) :
    normAbs v x = normalizedAbsValue v x ^ ((1 : ℝ) / Module.finrank ℚ K) := (rfl)

/-- At a finite place `v`, the degree-normalized absolute value is the `[K : ℚ]`-th root of the
`v`-adic absolute value. -/
@[simp]
theorem normAbs_inl (v : HeightOneSpectrum (𝓞 K)) (x : K) :
    normAbs (Sum.inl v) x =
      NumberField.HeightOneSpectrum.adicAbv K v x ^ ((1 : ℝ) / Module.finrank ℚ K) := (rfl)

/-- At an infinite place `w`, the degree-normalized absolute value is `w x ^ (mult w / [K : ℚ])`.
-/
@[simp]
theorem normAbs_inr (w : InfinitePlace K) (x : K) :
    normAbs (Sum.inr w) x = w x ^ ((w.mult : ℝ) / Module.finrank ℚ K) := by
  rw [normAbs_apply, normalizedAbsValue_inr, ← Real.rpow_natCast,
    ← Real.rpow_mul (apply_nonneg w x), mul_one_div]

theorem normAbs_nonneg (v : Place K) (x : K) : 0 ≤ normAbs v x :=
  Real.rpow_nonneg (normalizedAbsValue_nonneg v x) _

theorem normAbs_pos (v : Place K) {x : K} (hx : x ≠ 0) : 0 < normAbs v x :=
  Real.rpow_pos_of_pos (normalizedAbsValue_pos v hx) _

/-- The `[K : ℚ]`-th power of the degree-normalized absolute value is the normalized absolute
value. -/
theorem normAbs_pow_finrank (v : Place K) (x : K) :
    normAbs v x ^ Module.finrank ℚ K = normalizedAbsValue v x := by
  rw [normAbs_apply, one_div,
    Real.rpow_inv_natCast_pow (normalizedAbsValue_nonneg v x) Module.finrank_pos.ne']

/-- The `[K : ℚ]`-th power of the largest degree-normalized absolute value of a finite tuple is
its largest normalized absolute value. -/
theorem iSup_normAbs_pow_finrank {ι : Type*} [Finite ι] (v : Place K) (y : ι → K) :
    (⨆ i, normAbs v (y i)) ^ Module.finrank ℚ K = ⨆ i, normalizedAbsValue v (y i) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp [Module.finrank_pos.ne']
  · rw [Finite.map_iSup_of_monotoneOn (pow_left_monotoneOn (M₀ := ℝ)) fun i ↦
      Set.mem_Ici.mpr (normAbs_nonneg v (y i))]
    simp_rw [normAbs_pow_finrank]

/-- A tuple of elements of a number field which is not identically zero has, at all but finitely
many places, largest degree-normalized absolute value `1`. -/
theorem hasFiniteMulSupport_iSup_normAbs {ι : Type*} [Finite ι] {y : ι → K} (hy : y ≠ 0) :
    HasFiniteMulSupport fun v : Place K ↦ ⨆ i, normAbs v (y i) := by
  refine (hasFiniteMulSupport_iSup_normalizedAbsValue hy).of_eq_one_iff fun v ↦ ?_
  rw [← iSup_normAbs_pow_finrank, pow_eq_one_iff_of_nonneg
    (Real.iSup_nonneg fun i ↦ normAbs_nonneg v (y i)) Module.finrank_pos.ne']

/-- A nonzero element of a number field has degree-normalized absolute value `1` at all but
finitely many places. -/
theorem hasFiniteMulSupport_normAbs (hx : x ≠ 0) :
    HasFiniteMulSupport fun v : Place K ↦ normAbs v x :=
  (hasFiniteMulSupport_normalizedAbsValue hx).subset fun v hv h ↦
    hv (by beta_reduce at h ⊢; rw [normAbs_apply, h, Real.one_rpow])

/-- **The product formula** for the degree-normalized absolute values of a number field. -/
theorem finprod_normAbs_eq_one (hx : x ≠ 0) : ∏ᶠ v : Place K, normAbs v x = 1 := by
  rw [← pow_eq_one_iff_of_nonneg (finprod_nonneg fun v ↦ normAbs_nonneg v x)
    (Module.finrank_pos (R := ℚ) (M := K)).ne', finprod_pow (hasFiniteMulSupport_normAbs hx)]
  simp_rw [normAbs_pow_finrank]
  exact finprod_normalizedAbsValue_eq_one hx

end TauCeti.GlobalNumberFields
