/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Units
public import TauCeti.NumberTheory.Cyclotomic.Stickelberger.Smoothing

import TauCeti.Algebra.Order.Floor.Div
import TauCeti.Data.ZMod.Count
import TauCeti.Data.ZMod.MulCastHom

/-!
# The distribution relation of the Stickelberger elements of Jacobi sums

For a modulus `N ≥ 1`, a natural number `b` and a residue `y : ZMod N` with least nonnegative
representative `y₀ = y.val`, write

`θ_{N,b}(y) = ⌊b y₀ / N⌋ - ⌊b (-y)₀ / N⌋`,

the floors being natural-number quotients. The element `∑_t θ_{N,b}(t) [t⁻¹]` of
`ℤ[(ZMod N)ˣ]` is `(1 - [-1]) s_{N,b}`, where `s_{N,b}` is the positively smoothed Stickelberger
element `TauCeti.smoothedStickelberger N b`; it is the Stickelberger element attached to the
Jacobi sums. This file proves that these elements form a distribution along the reductions
`ZMod (q * M) → ZMod M` for primes `q ∤ M`.

* Over a whole fibre, for `b` prime to `n`, the sum of `θ_{nM,b}` over the `n` residues modulo
  `n M` that reduce to `x` is `θ_{M,b}(x)`: the constant `∑_{j<n} ⌊b j / n⌋` that each of the
  two floors acquires (`Nat.sum_range_add_mul_div`) cancels in the difference.
* Over the units, for a prime `q` dividing neither `b` nor `M` and a unit `t` modulo `M`, the
  sum of `θ_{qM,b}` over the units modulo `q M` that reduce to `t` is
  `θ_{M,b}(t) - θ_{M,b}(q⁻¹ t)`: exactly one residue of the fibre is not a unit
  (`ZMod.filter_castHom_eq_and_not_isUnit`), and it contributes `θ_{M,b}(q⁻¹ t)`.
* In the group ring, the push-forward of `(1 - [-1]) s_{qM,b}` along `ZMod.unitsMap` is
  `(1 - [q⁻¹]) (1 - [-1]) s_{M,b}`.

## Main results

* `TauCeti.coeff_one_sub_single_neg_one_mul_smoothedStickelberger`: the coefficient of
  `(1 - [-1]) s_{N,b}` at `[c]` is `θ_{N,b}(c⁻¹)`.
* `TauCeti.sum_filter_castHom_div_sub_div`: the distribution relation over whole fibres.
* `TauCeti.sum_filter_unitsMap_div_sub_div`: the distribution relation over units.
* `TauCeti.mapDomainRingHom_unitsMap_one_sub_single_mul_smoothedStickelberger`: the
  distribution relation in the group ring, for `b` prime to `q`.
* `TauCeti.mapDomainRingHom_unitsMap_one_sub_single_mul_smoothedStickelberger_of_lt`: the same
  for `b < q`.

## References

* The statement of the distribution relation is that of the formal proof of the Riemann
  hypothesis for Dirichlet `L`-functions,
  https://github.com/leanprover-community/riemann-hypothesis, lemma `UpperTheory.V.ML.thDist`,
  for the coefficients `UpperTheory.V.ML.th`.
* L. C. Washington, *Introduction to Cyclotomic Fields*, §6.2 and §12.1 (distributions).
* S. Lang, *Cyclotomic Fields I and II*, Chapter 1, §1 (the Bernoulli distribution).
-/

public section

open Finset MonoidAlgebra

namespace TauCeti

open ZMod

/-- **The distribution relation over whole fibres.** For `b` prime to `n` and `x : ZMod M`,
the sum of `θ_{nM,b}(y) = ⌊b y₀ / (n M)⌋ - ⌊b (-y)₀ / (n M)⌋` over the residues `y` modulo `n M`
reducing to `x` is `θ_{M,b}(x) = ⌊b x₀ / M⌋ - ⌊b (-x)₀ / M⌋`, where `z₀ = z.val` is the least
nonnegative representative and the floors are natural-number quotients. -/
theorem sum_filter_castHom_div_sub_div {n M b : ℕ} [NeZero n] [NeZero M] (hb : b.Coprime n)
    (x : ZMod M) :
    ∑ y : ZMod (n * M) with castHom (dvd_mul_left M n) (ZMod M) y = x,
        (((b * y.val / (n * M) : ℕ) : ℤ) - (b * (-y).val / (n * M) : ℕ)) =
      ((b * x.val / M : ℕ) : ℤ) - (b * (-x).val / M : ℕ) := by
  have hM : 0 < M := NeZero.pos M
  -- Each floor sums over a fibre to its value at the base plus `∑_{j<n} ⌊b j / n⌋`.
  have key (x' : ZMod M) :
      ∑ y : ZMod (n * M) with castHom (dvd_mul_left M n) (ZMod M) y = x', b * y.val / (n * M) =
        b * x'.val / M + ∑ j ∈ range n, b * j / n := by
    rw [sum_val_filter_castHom_eq_sum_range x' (fun k ↦ b * k / (n * M)),
      ← Nat.sum_range_add_mul_div (NeZero.ne n) hb]
    refine sum_congr rfl fun j _ ↦ ?_
    rw [mul_comm n M, ← Nat.div_div_eq_div_mul, mul_add, mul_left_comm, Nat.add_mul_div_left _ _ hM]
  have hneg : ∑ y : ZMod (n * M) with castHom (dvd_mul_left M n) (ZMod M) y = x,
      b * (-y).val / (n * M) =
        ∑ y : ZMod (n * M) with castHom (dvd_mul_left M n) (ZMod M) y = -x, b * y.val / (n * M) :=
    sum_nbij' Neg.neg Neg.neg
      (fun y hy ↦ by simpa only [mem_filter, mem_univ, true_and, map_neg, neg_inj] using hy)
      (fun y hy ↦ by
        simpa only [mem_filter, mem_univ, true_and, map_neg, neg_eq_iff_eq_neg] using hy)
      (fun y _ ↦ neg_neg y) (fun y _ ↦ neg_neg y) (fun _ _ ↦ rfl)
  rw [sum_sub_distrib, ← Nat.cast_sum, ← Nat.cast_sum, hneg, key, key]
  push_cast
  ring

/-- **The distribution relation over units.** Let `q` be a prime dividing neither `b` nor `M`,
and `t` a unit modulo `M`. The sum of `θ_{qM,b}(t') = ⌊b t'₀ / (q M)⌋ - ⌊b (-t')₀ / (q M)⌋`
over the units `t'` modulo `q M` reducing to `t` is `θ_{M,b}(t) - θ_{M,b}(q⁻¹ t)`, where
`z₀ = z.val` is the least nonnegative representative, the floors are natural-number quotients
and `q⁻¹` is the inverse of `q` in `ZMod M`. -/
theorem sum_filter_unitsMap_div_sub_div {q M b : ℕ} [Fact q.Prime] [NeZero M]
    (hqM : q.Coprime M) (hb : b.Coprime q) (t : (ZMod M)ˣ) :
    ∑ t' : (ZMod (q * M))ˣ with unitsMap (dvd_mul_left M q) t' = t,
        (((b * (t' : ZMod (q * M)).val / (q * M) : ℕ) : ℤ) -
          (b * (-(t' : ZMod (q * M))).val / (q * M) : ℕ)) =
      (((b * (t : ZMod M).val / M : ℕ) : ℤ) - (b * (-(t : ZMod M)).val / M : ℕ)) -
        (((b * ((q : ZMod M)⁻¹ * t).val / M : ℕ) : ℤ) -
          (b * (-((q : ZMod M)⁻¹ * t)).val / M : ℕ)) := by
  have hq : q.Prime := Fact.out
  set θ : ZMod (q * M) → ℤ := fun y ↦
    ((b * y.val / (q * M) : ℕ) : ℤ) - (b * (-y).val / (q * M) : ℕ) with hθ
  set F : Finset (ZMod (q * M)) := {y | castHom (dvd_mul_left M q) (ZMod M) y = t} with hF
  -- The sum over units is the sum over the units of the fibre `F`.
  have hunits : ∑ t' : (ZMod (q * M))ˣ with unitsMap (dvd_mul_left M q) t' = t,
      θ t' = ∑ y ∈ F with IsUnit y, θ y := by
    refine sum_bij (fun t' _ ↦ (t' : ZMod (q * M))) (fun t' ht' ↦ ?_)
      (fun _ _ _ _ h ↦ Units.ext h) (fun y hy ↦ ?_) (fun _ _ ↦ rfl)
    · simp only [mem_filter, mem_univ, true_and, hF] at ht' ⊢
      exact ⟨by rw [← ht', unitsMap_val, castHom_apply], t'.isUnit⟩
    · simp only [mem_filter, mem_univ, true_and, hF] at hy ⊢
      refine ⟨hy.2.unit, Units.ext ?_, rfl⟩
      rw [unitsMap_val, IsUnit.unit_spec, ← castHom_apply (h := dvd_mul_left M q)]
      exact hy.1
  -- The non-units of the fibre contribute `θ_{M,b}(q⁻¹ t)`.
  have hN : ∑ y ∈ F with ¬IsUnit y, θ y =
      ((b * ((q : ZMod M)⁻¹ * t).val / M : ℕ) : ℤ) -
        (b * (-((q : ZMod M)⁻¹ * t)).val / M : ℕ) := by
    -- The only non-unit of the fibre is `q (q⁻¹ t)₀`.
    have hval (a : ZMod M) : (mulCastHom q (mul_comm M q) a).val = q * a.val := by
      rw [mulCastHom_apply, cast_eq_val, ← Nat.cast_mul, mul_comm a.val,
        val_natCast_mul_val (mul_comm q M)]
    rw [hF, filter_filter, filter_castHom_eq_and_not_isUnit q (mul_comm M q) hqM t,
      sum_singleton, hθ]
    simp only [← map_neg, hval, mul_left_comm b q, Nat.mul_div_mul_left _ _ hq.pos]
  have hfull := sum_filter_castHom_div_sub_div hb (t : ZMod M)
  rw [← sum_filter_add_sum_filter_not _ IsUnit] at hfull
  rw [hunits, ← hfull, hN, add_sub_cancel_right]

/-- The coefficient of `(1 - [-1]) s_{m,b}` at `[c]` is
`θ_{m,b}(c⁻¹) = ⌊b (c⁻¹)₀ / m⌋ - ⌊b (-c⁻¹)₀ / m⌋`, where `s_{m,b}` is
`smoothedStickelberger m b`, `z₀ = z.val` is the least nonnegative representative and the floors
are natural-number quotients. -/
@[simp]
theorem coeff_one_sub_single_neg_one_mul_smoothedStickelberger (m : ℕ) [NeZero m] (b : ℕ)
    (c : (ZMod m)ˣ) :
    ((1 - single (-1) 1) * smoothedStickelberger m b).coeff c =
      ((b * ((c⁻¹ : (ZMod m)ˣ) : ZMod m).val / m : ℕ) : ℤ) -
        (b * (-((c⁻¹ : (ZMod m)ˣ) : ZMod m)).val / m : ℕ) := by
  simp [sub_mul, coeff_single_mul_apply]

/-- `(1 - [-1]) s_{m,b}` is the sum of `θ_{m,b}(a) [a⁻¹]` over the units `a` modulo `m`. -/
private theorem one_sub_single_neg_one_mul_smoothedStickelberger_eq_sum (m : ℕ) [NeZero m]
    (b : ℕ) :
    (1 - single (-1) 1) * smoothedStickelberger m b =
      ∑ a : (ZMod m)ˣ, single a⁻¹ (((b * (a : ZMod m).val / m : ℕ) : ℤ) -
        (b * (-(a : ZMod m)).val / m : ℕ)) := by
  ext c
  rw [coeff_one_sub_single_neg_one_mul_smoothedStickelberger]
  simp [coeff_sum, coeff_single, Finsupp.single_apply, inv_eq_iff_eq_inv]

/-- **The distribution relation of the Stickelberger elements of Jacobi sums.** Let `q` be a
prime dividing neither `b` nor `M`. The push-forward along the reduction
`ZMod.unitsMap : (ZMod (q * M))ˣ → (ZMod M)ˣ` of `(1 - [-1]) s_{qM,b}` is
`(1 - [q⁻¹]) (1 - [-1]) s_{M,b}`, where `s_{N,b}` is `smoothedStickelberger N b` and `q⁻¹` is the
inverse of the unit `q` of `ZMod M`. In coefficients this is
`sum_filter_unitsMap_div_sub_div`. -/
theorem mapDomainRingHom_unitsMap_one_sub_single_mul_smoothedStickelberger {q M b : ℕ}
    [Fact q.Prime] [NeZero M] (hqM : q.Coprime M) (hb : b.Coprime q) :
    mapDomainRingHom ℤ (ZMod.unitsMap (dvd_mul_left M q))
        ((1 - single (-1) 1) * smoothedStickelberger (q * M) b) =
      (1 - single (ZMod.unitOfCoprime q hqM)⁻¹ 1) *
        ((1 - single (-1) 1) * smoothedStickelberger M b) := by
  ext c
  -- The coefficient at `[c]` of the right side is `θ_{M,b}(c⁻¹) - θ_{M,b}(q⁻¹ c⁻¹)`.
  have hu : (((ZMod.unitOfCoprime q hqM * c)⁻¹ : (ZMod M)ˣ) : ZMod M) =
      (q : ZMod M)⁻¹ * ((c⁻¹ : (ZMod M)ˣ) : ZMod M) := by
    rw [mul_inv_rev, Units.val_mul, ← ZMod.inv_coe_unit, ← ZMod.inv_coe_unit,
      ZMod.coe_unitOfCoprime, mul_comm]
  have hR : ((1 - single (ZMod.unitOfCoprime q hqM)⁻¹ 1) *
      ((1 - single (-1) 1) * smoothedStickelberger M b)).coeff c =
        (((b * ((c⁻¹ : (ZMod M)ˣ) : ZMod M).val / M : ℕ) : ℤ) -
          (b * (-((c⁻¹ : (ZMod M)ˣ) : ZMod M)).val / M : ℕ)) -
        (((b * ((q : ZMod M)⁻¹ * ((c⁻¹ : (ZMod M)ˣ) : ZMod M)).val / M : ℕ) : ℤ) -
          (b * (-((q : ZMod M)⁻¹ * ((c⁻¹ : (ZMod M)ˣ) : ZMod M))).val / M : ℕ)) := by
    rw [sub_mul, one_mul, coeff_sub, Finsupp.sub_apply, coeff_single_mul_apply, inv_inv, one_mul]
    simp only [coeff_one_sub_single_neg_one_mul_smoothedStickelberger, hu]
  -- On the left, `[a⁻¹]` lands on `[c]` exactly when `a` reduces to `c⁻¹`.
  have hL : (mapDomainRingHom ℤ (ZMod.unitsMap (dvd_mul_left M q))
      ((1 - single (-1) 1) * smoothedStickelberger (q * M) b)).coeff c =
        ∑ a : (ZMod (q * M))ˣ with ZMod.unitsMap (dvd_mul_left M q) a = c⁻¹,
          (((b * (a : ZMod (q * M)).val / (q * M) : ℕ) : ℤ) -
            (b * (-(a : ZMod (q * M))).val / (q * M) : ℕ)) := by
    rw [one_sub_single_neg_one_mul_smoothedStickelberger_eq_sum, map_sum, coeff_sum,
      Finset.sum_apply', sum_filter]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    simp only [mapDomainRingHom_apply, mapDomain_single, coeff_single, Finsupp.single_apply,
      map_inv, inv_eq_iff_eq_inv]
  rw [hL, hR, sum_filter_unitsMap_div_sub_div hqM hb c⁻¹]

/-- **The distribution relation of the Stickelberger elements of Jacobi sums, for `b < q`.** For a
prime `q ∤ M` and a natural number `b < q`, the push-forward along `ZMod.unitsMap` of
`(1 - [-1]) s_{qM,b}` is `(1 - [q⁻¹]) (1 - [-1]) s_{M,b}`; see
`mapDomainRingHom_unitsMap_one_sub_single_mul_smoothedStickelberger`. -/
theorem mapDomainRingHom_unitsMap_one_sub_single_mul_smoothedStickelberger_of_lt {q M b : ℕ}
    [Fact q.Prime] [NeZero M] (hqM : q.Coprime M) (hb : b < q) :
    mapDomainRingHom ℤ (ZMod.unitsMap (dvd_mul_left M q))
        ((1 - single (-1) 1) * smoothedStickelberger (q * M) b) =
      (1 - single (ZMod.unitOfCoprime q hqM)⁻¹ 1) *
        ((1 - single (-1) 1) * smoothedStickelberger M b) := by
  rcases Nat.eq_zero_or_pos b with rfl | hb0
  · simp
  exact mapDomainRingHom_unitsMap_one_sub_single_mul_smoothedStickelberger hqM
    ((Fact.out : q.Prime).coprime_iff_not_dvd.2 (Nat.not_dvd_of_pos_of_lt hb0 hb)).symm

end TauCeti
