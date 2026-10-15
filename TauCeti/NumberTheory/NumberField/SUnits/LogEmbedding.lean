/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Places.Basic
public import TauCeti.NumberTheory.NumberField.SUnits.Basic
public import TauCeti.NumberTheory.NumberField.Units.LogEmbedding

/-!
# The logarithmic embedding of S-units

For a finite set `S` of finite places of a number field, the logarithmic embedding sends an
`S`-unit to its weighted logarithms at all infinite places except Mathlib's distinguished place,
together with its logarithms at the places in `S`. The product formula recovers the omitted
infinite coordinate as minus the sum of these coordinates.

Ordinary units map to the usual Dirichlet logarithmic embedding in the infinite coordinates and
to zero in the finite coordinates. These facts are the coordinate foundation for the
`S`-logarithmic lattice and its regulator.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Theorem 1.5.13.
-/

public noncomputable section

open Finset IsDedekindDomain NumberField NumberField.InfinitePlace
  NumberField.Units.dirichletUnitTheorem

namespace TauCeti.NumberField.SUnit

variable {K : Type*} [Field K] [NumberField K]

/-- The logarithmic space for the `S`-units, with the coordinate at the distinguished infinite
place omitted. -/
abbrev logSpace (S : Finset (HeightOneSpectrum (𝓞 K))) :=
  ({w : InfinitePlace K // w ≠ w₀} ⊕ S) → ℝ

/-- The logarithmic embedding of the `S`-units. Its infinite coordinates are weighted by the
place multiplicity, while its finite coordinates use the normalized finite-place absolute
values. -/
def logEmbedding (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Additive ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) →+ logSpace S where
  toFun x := Sum.elim
    (fun w ↦ w.1.mult * Real.log (w.1 (x.toMul : Kˣ)))
    (fun v ↦ Real.log (FinitePlace.mk v.1 (x.toMul : Kˣ)))
  map_zero' := by
    classical
    ext i
    cases i <;> simp
  map_add' x y := by
    classical
    ext i
    cases i <;> simp [Real.log_mul, mul_add]

@[simp]
theorem logEmbedding_apply_inl (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x : (S : Set (HeightOneSpectrum (𝓞 K))).unit K)
    (w : {w : InfinitePlace K // w ≠ w₀}) :
    logEmbedding S (Additive.ofMul x) (Sum.inl w) =
      w.1.mult * Real.log (w.1 (x : Kˣ)) :=
  (rfl)

@[simp]
theorem logEmbedding_apply_inr (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x : (S : Set (HeightOneSpectrum (𝓞 K))).unit K) (v : S) :
    logEmbedding S (Additive.ofMul x) (Sum.inr v) =
      Real.log (FinitePlace.mk v.1 (x : Kˣ)) :=
  (rfl)

private theorem normalizedAbsValue_inl_eq_one_of_notMem
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x : (S : Set (HeightOneSpectrum (𝓞 K))).unit K)
    {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ S) :
    GlobalNumberFields.normalizedAbsValue (Sum.inl v) ((x : Kˣ) : K) = 1 := by
  have hvone : v.valuation K ((x : Kˣ) : K) = 1 :=
    Set.unit_valuation_eq_one (S : Set (HeightOneSpectrum (𝓞 K))) K x hv
  rw [GlobalNumberFields.normalizedAbsValue_inl, HeightOneSpectrum.adicAbv_def, hvone]
  simp

/-- The product formula for an `S`-unit, with the finite contribution restricted to `S`. -/
theorem sum_mult_mul_log_add_sum_log_finitePlace
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x : (S : Set (HeightOneSpectrum (𝓞 K))).unit K) :
    (∑ w : InfinitePlace K, w.mult * Real.log (w ((x : Kˣ) : K))) +
        ∑ v : S, Real.log (FinitePlace.mk v.1 ((x : Kˣ) : K)) = 0 := by
  classical
  have hx : ((x : Kˣ) : K) ≠ 0 := (x : Kˣ).ne_zero
  have hsupp : Function.mulSupport
      (fun v : HeightOneSpectrum (𝓞 K) ↦
        GlobalNumberFields.normalizedAbsValue (Sum.inl v) ((x : Kˣ) : K)) ⊆ S := by
    intro v hv
    by_contra hvS
    exact hv (normalizedAbsValue_inl_eq_one_of_notMem S x hvS)
  have hfinite (v : HeightOneSpectrum (𝓞 K)) :
      GlobalNumberFields.normalizedAbsValue (Sum.inl v) ((x : Kˣ) : K) =
        FinitePlace.mk v ((x : Kˣ) : K) := by
    rw [GlobalNumberFields.normalizedAbsValue_inl, FinitePlace.mk_apply,
      FinitePlace.norm_embedding]
  have hfinprod :
      ∏ᶠ v : HeightOneSpectrum (𝓞 K),
          GlobalNumberFields.normalizedAbsValue (Sum.inl v) ((x : Kˣ) : K) =
        ∏ v : S, FinitePlace.mk v.1 ((x : Kˣ) : K) := by
    rw [finprod_eq_prod_of_mulSupport_subset _ hsupp]
    rw [← Finset.prod_coe_sort]
    exact Fintype.prod_congr _ _ fun v ↦ hfinite v.1
  have hnorm : |(Algebra.norm ℚ) ((x : Kˣ) : K)| ≠ 0 := by
    simp [Algebra.norm_eq_zero_iff, hx]
  have hprod :
      (∏ v : S, FinitePlace.mk v.1 ((x : Kˣ) : K)) *
          ∏ w : InfinitePlace K, w ((x : Kˣ) : K) ^ w.mult = 1 := by
    rw [← hfinprod, GlobalNumberFields.finprod_normalizedAbsValue_inl hx,
      InfinitePlace.prod_eq_abs_norm, ← Rat.cast_mul, inv_mul_cancel₀ hnorm, Rat.cast_one]
  have hposFinite (v : S) : 0 < FinitePlace.mk v.1 ((x : Kˣ) : K) :=
    FinitePlace.pos_iff.mpr hx
  have hposInfinite (w : InfinitePlace K) : 0 < w ((x : Kˣ) : K) :=
    InfinitePlace.pos_iff.mpr hx
  have hlog := congrArg Real.log hprod
  rw [Real.log_mul (Finset.prod_ne_zero_iff.mpr fun v _ ↦ (hposFinite v).ne')
      (Finset.prod_ne_zero_iff.mpr fun w _ ↦ (pow_pos (hposInfinite w) _).ne'),
    Real.log_prod (fun v _ ↦ (hposFinite v).ne'),
    Real.log_prod (fun w _ ↦ (pow_pos (hposInfinite w) _).ne'),
    Real.log_one] at hlog
  simpa only [Real.log_pow, Nat.cast_ofNat, Finset.sum_const_zero, add_zero,
    mul_comm, add_comm] using hlog

open Classical in
/-- The sum of the `S`-logarithmic coordinates is the negative of the omitted infinite-place
coordinate. -/
theorem sum_logEmbedding (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x : (S : Set (HeightOneSpectrum (𝓞 K))).unit K) :
    ∑ i, logEmbedding S (Additive.ofMul x) i =
      -(w₀ (K := K)).mult * Real.log ((w₀ (K := K)) ((x : Kˣ) : K)) := by
  rw [Fintype.sum_sum_type]
  simp_rw [logEmbedding_apply_inl, logEmbedding_apply_inr]
  have h := sum_mult_mul_log_add_sum_log_finitePlace S x
  rw [Fintype.sum_eq_add_sum_subtype_ne _ (w₀ (K := K))] at h
  linarith

/-- On ordinary units, the `S`-logarithmic embedding is the usual logarithmic embedding in the
infinite coordinates and zero in the finite coordinates. -/
@[simp]
theorem logEmbedding_unitOfUnits (S : Finset (HeightOneSpectrum (𝓞 K))) (u : (𝓞 K)ˣ) :
    logEmbedding S (Additive.ofMul
      (unitOfUnits (S : Set (HeightOneSpectrum (𝓞 K))) u)) =
      Sum.elim (NumberField.Units.logEmbedding K (Additive.ofMul u)) 0 := by
  classical
  ext i
  cases i with
  | inl w =>
      simp only [Sum.elim_inl]
      rw [logEmbedding_apply_inl,
        NumberField.Units.dirichletUnitTheorem.logEmbedding_component]
      rw [val_unitOfUnits]
  | inr v =>
      simp only [logEmbedding_apply_inr, Sum.elim_inr, Pi.zero_apply]
      rw [val_unitOfUnits,
        FinitePlace.mk_apply,
        (FinitePlace.norm_eq_one_iff_notMem K v.1 (u : 𝓞 K)).mpr
          (v.1.asIdeal.notMem_of_isUnit u.isUnit), Real.log_one]

end TauCeti.NumberField.SUnit
