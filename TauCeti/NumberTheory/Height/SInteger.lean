/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Height.NumberField
public import TauCeti.NumberTheory.NumberField.FinitePlace
public import TauCeti.RingTheory.DedekindDomain.SInteger.Basic
public import TauCeti.RingTheory.DedekindDomain.SInteger.Unit

import Mathlib.Algebra.FiniteSupport.Basic

/-!
# Heights of S-integers

The height of an S-integer is supported on the primes in S and the infinite places.
This file translates membership in Mathlib's S-integers and S-units into finite-place
absolute values, proves the resulting multiplicative and logarithmic height identities,
and shows that the multiplicative identity characterizes nonzero S-integers.
The set S may be arbitrary; finset versions give ordinary products and sums.

Adapted from Ralf Stephan's `ArithmeticHeights/SUnit.lean` in `rwst/Subspace-Theorems`,
commit `e443c2479e19f7665b31d8e94e2317c8ced1ca06` (Apache 2.0), using Mathlib's height API.
The mathematical reference is Bombieri and Gubler, *Heights in Diophantine Geometry*,
Cambridge University Press (2006), §1.5.10.
-/

public section

open Function Height IsDedekindDomain Real

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- **An `S`-integer is an element whose absolute values at the finite places outside `S` are at
most `1`.** -/
theorem _root_.Set.mem_integer_iff_finitePlace (S : Set (HeightOneSpectrum (𝓞 K))) (x : K) :
    x ∈ S.integer K ↔ ∀ v ∉ S, FinitePlace.mk v x ≤ 1 :=
  (Set.mem_integer_iff K S).trans <|
    forall₂_congr fun v _ ↦ (FinitePlace.mk_apply_le_one_iff v x).symm

/-- **An `S`-unit is an element of `Kˣ` whose absolute values at the finite places outside `S` are
all `1`.** -/
theorem _root_.Set.mem_unit_iff_finitePlace (S : Set (HeightOneSpectrum (𝓞 K))) (x : Kˣ) :
    x ∈ S.unit K ↔ ∀ v ∉ S, FinitePlace.mk v (x : K) = 1 :=
  (Set.mem_unit_iff S K).trans <|
    forall₂_congr fun v _ ↦ (FinitePlace.mk_apply_eq_one_iff v (x : K)).symm

section Height

variable (S : Set (HeightOneSpectrum (𝓞 K)))

/-- The local factor of an `S`-integer is trivial at every finite place outside `S`. -/
private theorem max_mk_apply_one_eq_one {x : K} (hx : x ∈ S.integer K)
    {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ S) : max (FinitePlace.mk v x) 1 = 1 :=
  max_eq_right ((Set.mem_integer_iff_finitePlace S x).mp hx v hv)

/-- **The height of an `S`-integer is carried by the infinite places and the places of `S`.**
The `S`-unit case of this is Bombieri–Gubler 1.5.10; the hypothesis the proof uses is only that
`x` is an `S`-integer. -/
theorem mulHeight₁_eq_of_mem_integer {x : K} (hx : x ∈ S.integer K) :
    mulHeight₁ x
      = (∏ w : InfinitePlace K, max (w x) 1 ^ w.mult)
        * ∏ᶠ v ∈ S, max (FinitePlace.mk v x) 1 := by
  rw [NumberField.mulHeight₁_eq]
  congr 1
  rw [← finprod_comp_equiv (FinitePlace.equivHeightOneSpectrum (K := K)).symm]
  simp only [FinitePlace.equivHeightOneSpectrum_symm_apply, ← FinitePlace.mk_apply]
  rw [← finprod_mem_univ]
  refine finprod_mem_inter_mulSupport_eq' _ Set.univ S fun v hv ↦ ?_
  simp only [Set.mem_univ, true_iff]
  by_contra hvS
  exact hv (max_mk_apply_one_eq_one S hx hvS)

/-- The logarithmic form of `NumberField.mulHeight₁_eq_of_mem_integer`. -/
theorem logHeight₁_eq_of_mem_integer {x : K} (hx : x ∈ S.integer K) :
    logHeight₁ x
      = (∑ w : InfinitePlace K, w.mult * log⁺ (w x))
        + ∑ᶠ v ∈ S, log⁺ (FinitePlace.mk v x) := by
  rw [NumberField.logHeight₁_eq]
  congr 1
  rw [← finsum_comp_equiv (FinitePlace.equivHeightOneSpectrum (K := K)).symm]
  simp only [FinitePlace.equivHeightOneSpectrum_symm_apply, ← FinitePlace.mk_apply]
  rw [← finsum_mem_univ]
  refine finsum_mem_inter_support_eq' _ Set.univ S fun v hv ↦ ?_
  simp only [Set.mem_univ, true_iff]
  by_contra hvS
  refine hv ?_
  exact (posLog_eq_zero_iff _).mpr (by
    rw [abs_of_nonneg (apply_nonneg _ _)]
    exact (Set.mem_integer_iff_finitePlace S x).mp hx v hvS)

/-- **The height of an `S`-unit**, the statement of Bombieri–Gubler 1.5.10. -/
theorem mulHeight₁_eq_of_mem_unit {x : Kˣ} (hx : x ∈ S.unit K) :
    mulHeight₁ (x : K)
      = (∏ w : InfinitePlace K, max (w (x : K)) 1 ^ w.mult)
        * ∏ᶠ v ∈ S, max (FinitePlace.mk v (x : K)) 1 :=
  mulHeight₁_eq_of_mem_integer S ((Set.mem_integer_iff K S).mpr
    fun v hv ↦ ((Set.mem_unit_iff S K).mp hx v hv).le)

/-- The logarithmic form of `NumberField.mulHeight₁_eq_of_mem_unit`. -/
theorem logHeight₁_eq_of_mem_unit {x : Kˣ} (hx : x ∈ S.unit K) :
    logHeight₁ (x : K)
      = (∑ w : InfinitePlace K, w.mult * log⁺ (w (x : K)))
        + ∑ᶠ v ∈ S, log⁺ (FinitePlace.mk v (x : K)) :=
  logHeight₁_eq_of_mem_integer S ((Set.mem_integer_iff K S).mpr
    fun v hv ↦ ((Set.mem_unit_iff S K).mp hx v hv).le)

end Height

/-- The height of an `S`-integer when `S` is a finite set of primes. -/
theorem mulHeight₁_eq_prod_of_mem_integer (S : Finset (HeightOneSpectrum (𝓞 K))) {x : K}
    (hx : x ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K) :
    mulHeight₁ x
      = (∏ w : InfinitePlace K, max (w x) 1 ^ w.mult)
        * ∏ v ∈ S, max (FinitePlace.mk v x) 1 := by
  rw [mulHeight₁_eq_of_mem_integer _ hx, finprod_mem_coe_finset]

/-- The logarithmic height of an `S`-integer when `S` is a finite set of primes. -/
theorem logHeight₁_eq_sum_of_mem_integer (S : Finset (HeightOneSpectrum (𝓞 K))) {x : K}
    (hx : x ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K) :
    logHeight₁ x = (∑ w : InfinitePlace K, w.mult * log⁺ (w x))
      + ∑ v ∈ S, log⁺ (FinitePlace.mk v x) := by
  rw [logHeight₁_eq_of_mem_integer _ hx, finsum_mem_coe_finset]

/-!
### The identity characterizes the `S`-integers
-/

/-- **The display of `NumberField.mulHeight₁_eq_of_mem_integer` characterizes the `S`-integers.**
Every local factor is at least `1`, so a finite place outside `S` at which `x` has absolute value
greater than `1` makes the full finite product strictly larger than its part over `S`. -/
theorem mulHeight₁_eq_iff_mem_integer (S : Set (HeightOneSpectrum (𝓞 K))) {x : K} (hx : x ≠ 0) :
    mulHeight₁ x
        = (∏ w : InfinitePlace K, max (w x) 1 ^ w.mult)
          * ∏ᶠ v ∈ S, max (FinitePlace.mk v x) 1
      ↔ x ∈ S.integer K := by
  refine ⟨fun h ↦ (S.mem_integer_iff_finitePlace x).mpr fun v hv ↦ ?_,
    mulHeight₁_eq_of_mem_integer S⟩
  have hone : ∀ w : HeightOneSpectrum (𝓞 K), (1 : ℝ) ≤ max (FinitePlace.mk w x) 1 :=
    fun w ↦ le_max_right _ _
  have hfin : HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 K) ↦
      max (FinitePlace.mk v x) 1 := by
    have hf : HasFiniteMulSupport fun w : FinitePlace K ↦ w x :=
      FinitePlace.hasFiniteMulSupport hx
    simpa only [Pi.one_apply,
      FinitePlace.equivHeightOneSpectrum_symm_apply, ← FinitePlace.mk_apply] using
      (hf.max (hasFiniteMulSupport_fun_one)).fun_comp_of_injective
        (FinitePlace.equivHeightOneSpectrum (K := K)).symm.injective
  have harch : (∏ w : InfinitePlace K, max (w x) 1 ^ w.mult) ≠ 0 :=
    (Finset.prod_pos fun w _ ↦ pow_pos (lt_of_lt_of_le zero_lt_one (le_max_right _ _)) _).ne'
  -- the full finite product coincides with its part over `S`
  have hall : ∏ᶠ w : HeightOneSpectrum (𝓞 K), max (FinitePlace.mk w x) 1
      = ∏ᶠ w ∈ S, max (FinitePlace.mk w x) 1 := by
    rw [NumberField.mulHeight₁_eq] at h
    replace h := mul_left_cancel₀ harch h
    rw [← finprod_comp_equiv (FinitePlace.equivHeightOneSpectrum (K := K)).symm] at h
    simpa only [FinitePlace.equivHeightOneSpectrum_symm_apply, ← FinitePlace.mk_apply] using h
  -- so the part outside `S` is trivial
  have hsplit := finprod_mem_inter_mul_sdiff'
    (f := fun w : HeightOneSpectrum (𝓞 K) ↦ max (FinitePlace.mk w x) 1) (s := Set.univ) S
    (by rw [Set.univ_inter]; exact hfin)
  rw [Set.univ_inter, ← Set.compl_eq_univ_sdiff, finprod_mem_univ, hall] at hsplit
  have hSpos : (0 : ℝ) < ∏ᶠ w ∈ S, max (FinitePlace.mk w x) 1 :=
    lt_of_lt_of_le zero_lt_one (one_le_finprod fun w ↦ one_le_finprod fun _ ↦ hone w)
  have hcompl : ∏ᶠ w ∈ Sᶜ, max (FinitePlace.mk w x) 1 = 1 :=
    mul_left_cancel₀ hSpos.ne' (by rw [mul_one]; exact hsplit)
  -- and then so is the single factor at `v`
  have hsing := finprod_mem_inter_mul_sdiff'
    (f := fun w : HeightOneSpectrum (𝓞 K) ↦ max (FinitePlace.mk w x) 1) (s := Sᶜ) {v}
    (hfin.subset Set.inter_subset_right)
  rw [Set.inter_eq_self_of_subset_right (Set.singleton_subset_iff.mpr hv), finprod_mem_singleton,
    hcompl] at hsing
  have hrest : (1 : ℝ) ≤ ∏ᶠ w ∈ (Sᶜ \ {v} : Set (HeightOneSpectrum (𝓞 K))),
      max (FinitePlace.mk w x) 1 :=
    one_le_finprod fun w ↦ one_le_finprod fun _ ↦ hone w
  have key := mul_le_mul_of_nonneg_left hrest (le_trans zero_le_one (hone v))
  rw [mul_one, hsing] at key
  exact le_of_max_le_left key

end NumberField
