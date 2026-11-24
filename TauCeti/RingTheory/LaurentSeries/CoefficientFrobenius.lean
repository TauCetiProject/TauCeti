/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.Perfect
public import Mathlib.LinearAlgebra.Dimension.Finite
public import TauCeti.RingTheory.LaurentSeries.Basic

/-!
# Coefficient Frobenius and difference equations on Laurent series

The arithmetic `p^f`-Frobenius on `k((X))` acts on coefficients and fixes `X`.
When `k` is algebraically closed and `f > 0`, every nonzero scalar twisted
polynomial in this Frobenius is surjective. After normalization by powers of
`X`, one solves each successive power-series coefficient by taking a root
of a nonconstant polynomial over `k`. This is the coefficient lifting
argument for difference equations over a discretely valued field.

On any finite-dimensional Laurent-series vector space with semilinear
endomorphism `Φ` for this Frobenius, the operator `Φ - 1` is surjective.
A dependence among the iterates of a vector reduces its preimage to a
scalar equation, and a finite sum of iterates telescopes.

## References

* K. S. Kedlaya, *A p-adic local monodromy theorem*, Ann. of Math. 160 (2004),
  Proposition 3.17, for the use of reduction to a polynomial over the residue field.
-/

public section

open scoped PowerSeries LaurentSeries
open Finset Function HahnSeries

namespace LaurentSeries

variable (p : ℕ) {k : Type*}

/-- Apply the `p^f`-power automorphism to each coefficient of a Laurent series. -/
noncomputable def coefficientFrobenius [CommSemiring k] [ExpChar k p] [PerfectRing k p] (f : ℕ) :
    k⸨X⸩ ≃+* k⸨X⸩ :=
  { toFun := mapRingHom (iterateFrobeniusEquiv k p f).toRingHom
    invFun := mapRingHom (iterateFrobeniusEquiv k p f).symm.toRingHom
    map_add' := map_add _
    map_mul' := map_mul _
    left_inv := fun x => by
      ext j
      rw [coeff_mapRingHom, coeff_mapRingHom]
      exact (iterateFrobeniusEquiv k p f).symm_apply_apply _
    right_inv := fun x => by
      ext j
      rw [coeff_mapRingHom, coeff_mapRingHom]
      exact (iterateFrobeniusEquiv k p f).apply_symm_apply _ }

variable [CommSemiring k] [ExpChar k p] [PerfectRing k p]

/-- The coefficient of a Laurent series is raised to `p^f` by coefficient Frobenius. -/
@[simp]
theorem coeff_coefficientFrobenius (f : ℕ) (x : k⸨X⸩) (j : ℤ) :
    (coefficientFrobenius p f x).coeff j = x.coeff j ^ p ^ f :=
  coeff_mapRingHom _ _ _

/-- Coefficient Frobenius acts on a monomial without changing its exponent. -/
@[simp]
theorem coefficientFrobenius_single (f : ℕ) (j : ℤ) (a : k) :
    coefficientFrobenius p f (single j a) = single j (a ^ p ^ f) :=
  mapRingHom_single _ _ _

/-- Coefficient Frobenius restricts to coefficientwise Frobenius on power series. -/
@[simp]
theorem coefficientFrobenius_coe (f : ℕ) (x : k⟦X⟧) :
    coefficientFrobenius p f (x : k⸨X⸩) = (PowerSeries.map (iterateFrobenius k p f) x : k⸨X⸩) :=
  (mapRingHom_apply _ _).trans (map_ofPowerSeries _ _)

/-- The zeroth coefficient Frobenius is the identity. -/
@[simp]
theorem coefficientFrobenius_zero :
    coefficientFrobenius (k := k) p 0 = RingEquiv.refl k⸨X⸩ := by
  ext x j
  simp

/-- Composing coefficient Frobenius maps adds their iteration exponents. -/
theorem coefficientFrobenius_add_apply (f g : ℕ) (x : k⸨X⸩) :
    coefficientFrobenius p (f + g) x = coefficientFrobenius p f (coefficientFrobenius p g x) := by
  ext j
  simpa only [coeff_coefficientFrobenius, iterateFrobenius_def] using
    iterateFrobenius_add_apply k p f g (x.coeff j)

/-- Iterating coefficient Frobenius multiplies its exponent index by the number of iterations. -/
theorem coefficientFrobenius_iterate (f n : ℕ) :
    (coefficientFrobenius (k := k) p f)^[n] = coefficientFrobenius p (f * n) := by
  induction n with
  | zero => simp [Function.iterate_zero]
  | succ n ih =>
    funext x
    rw [iterate_succ_apply, ih, Nat.mul_succ, coefficientFrobenius_add_apply]

end LaurentSeries

namespace LaurentSeries

open Polynomial

variable {p : ℕ} {k : Type*} [Field k] [Fact p.Prime] [CharP k p] [IsAlgClosed k]

private theorem exists_powerSeries_sum_mul_frobenius_eq (s : Finset ℕ) (a : ℕ → k⟦X⟧)
    {f : ℕ} (hf : 0 < f) (ha : ∃ i ∈ s, PowerSeries.constantCoeff (a i) ≠ 0) (b : k⟦X⟧) :
    ∃ x : k⟦X⟧, ∑ i ∈ s, a i * PowerSeries.map (iterateFrobenius k p (f * i)) x = b := by
  classical
  let q := p ^ f
  have hq : 1 < q := one_lt_pow₀ (Fact.out : p.Prime).one_lt hf.ne'
  -- The constant coefficients give the same nonconstant polynomial at every lifting step.
  let lead (x : k) := ∑ i ∈ s, PowerSeries.constantCoeff (a i) * x ^ (q ^ i)
  have hlead : Surjective lead := by
    let P : k[X] := ∑ i ∈ s, monomial (q ^ i) (PowerSeries.constantCoeff (a i))
    obtain ⟨i, hi, hai⟩ := ha
    have he (j : ℕ) : q ^ j = q ^ i ↔ j = i := (Nat.pow_right_injective hq).eq_iff
    have hcoeff : P.coeff (q ^ i) = PowerSeries.constantCoeff (a i) := by
      simp only [P, finsetSum_coeff, coeff_monomial_apply, he]
      simp [hi]
    have hdegree : P.natDegree ≠ 0 := by
      intro h
      have hlt : P.natDegree < q ^ i := h.symm ▸ pow_pos (by omega) _
      exact hai (hcoeff.symm.trans (coeff_eq_zero_of_natDegree_lt hlt))
    simpa only [lead, P, eval_finsetSum, eval_monomial] using IsAlgClosed.eval_surjective hdegree
  let lower (n : ℕ) (c : ℕ → k) : k :=
    ∑ i ∈ s, ∑ j ∈ range n, PowerSeries.coeff (n - j) (a i) * c j ^ (q ^ i)
  let solve (n : ℕ) (c : ℕ → k) := surjInv hlead (PowerSeries.coeff n b - lower n c)
  let step (n : ℕ) (prev : ∀ j < n, k) : k :=
    solve n (fun j => if h : j < n then prev j h else 0)
  let c : ℕ → k := fun n => Nat.strongRecOn n step
  have hc (n : ℕ) : ∑ i ∈ s, PowerSeries.constantCoeff (a i) * c n ^ (q ^ i) =
      PowerSeries.coeff n b - lower n c := by
    rw [show c n = solve n (fun j => if j < n then c j else 0) from Nat.strongRecOn_eq step n]
    have h : lower n (fun j => if j < n then c j else 0) = lower n c := by
      refine sum_congr rfl fun i _ => sum_congr rfl fun j hj => ?_
      simp [mem_range.mp hj]
    simpa only [solve, h] using
      rightInverse_surjInv hlead (PowerSeries.coeff n b - lower n c)
  refine ⟨PowerSeries.mk c, PowerSeries.ext fun n => ?_⟩
  have hmul (i : ℕ) :
      PowerSeries.coeff n (a i * PowerSeries.map (iterateFrobenius k p (f * i))
          (PowerSeries.mk c)) =
        (∑ j ∈ range n, PowerSeries.coeff (n - j) (a i) * c j ^ (q ^ i)) +
          PowerSeries.constantCoeff (a i) * c n ^ (q ^ i) := by
    rw [mul_comm, PowerSeries.coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk, sum_range_succ]
    simp [PowerSeries.coeff_zero_eq_constantCoeff, iterateFrobenius_def, q, pow_mul, mul_comm]
  simp only [map_sum, hmul, sum_add_distrib, hc, lower]
  abel

/-- A nonzero scalar twisted polynomial in positive coefficient Frobenius is surjective on
Laurent series over an algebraically closed field. Each index in `s` denotes an iterate
of the same coefficient automorphism. -/
theorem surjective_sum_mul_coefficientFrobenius {f : ℕ} (hf : 0 < f) {s : Finset ℕ}
    (a : ℕ → k⸨X⸩) (ha : ∃ i ∈ s, a i ≠ 0) :
    Surjective (fun x : k⸨X⸩ => ∑ i ∈ s, a i * coefficientFrobenius p (f * i) x) := by
  classical
  intro b
  obtain ⟨j, hj, hmin⟩ := (s.filter fun i => a i ≠ 0).exists_min_image
    (fun i => (a i).order) (by
      obtain ⟨i, hi, hi₀⟩ := ha
      exact ⟨i, mem_filter.mpr ⟨hi, hi₀⟩⟩)
  let m := (a j).order
  -- Dividing all operator coefficients by the same monomial gives a nonzero reduction.
  let aSeries (i : ℕ) := PowerSeries.X ^ ((a i).order - m).toNat * (a i).powerSeriesPart
  have haSeries_coe (i : ℕ) (hi : i ∈ s) :
      (aSeries i : k⸨X⸩) = single (-m) 1 * a i := by
    rcases eq_or_ne (a i) 0 with hzero | hne
    · simp [aSeries, hzero]
    have hle := hmin i (mem_filter.mpr ⟨hi, hne⟩)
    have hadd : (((a i).order - m).toNat : ℤ) + -(a i).order = -m := by omega
    simp only [aSeries, PowerSeries.coe_mul, ofPowerSeries_X_pow, ofPowerSeries_powerSeriesPart]
    rw [← mul_assoc, single_mul_single, one_mul, hadd]
  have hj' := mem_filter.mp hj
  have hAj : PowerSeries.constantCoeff (aSeries j) ≠ 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff, ← coeff_coe_powerSeries, haSeries_coe _ hj'.1,
      coeff_single_mul, one_mul, Int.natCast_zero, zero_sub, neg_neg]
    exact coeff_order_eq_zero.not.mpr hj'.2
  obtain ⟨x, hx⟩ := exists_powerSeries_sum_mul_frobenius_eq (p := p) s aSeries hf
    ⟨j, hj'.1, hAj⟩ b.powerSeriesPart
  refine ⟨single (b.order - m) 1 * (x : k⸨X⸩), ?_⟩
  apply mul_left_cancel₀ (a := (single (-b.order) 1 : k⸨X⸩)) (by simp)
  rw [← ofPowerSeries_powerSeriesPart b, ← hx, map_sum]
  rw [mul_sum]
  refine sum_congr rfl fun i hi => ?_
  have hadd : -b.order + (b.order - m) = -m := by omega
  rw [map_mul, coefficientFrobenius_single, one_pow, mul_left_comm (a i), ← mul_assoc,
    single_mul_single, one_mul, hadd, ← mul_assoc, ← haSeries_coe i hi, coefficientFrobenius_coe]
  exact (map_mul (ofPowerSeries ℤ k) _ _).symm

end LaurentSeries

namespace LaurentSeries

variable {k : Type*} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] [IsAlgClosed k]
  {f : ℕ} {V : Type*} [AddCommGroup V] [Module k⸨X⸩ V]

local notation "σ" => coefficientFrobenius (k := k) p f

private theorem frobenius_iterate_smul (Φ : V →ₛₗ[(σ).toRingHom] V)
    (n : ℕ) (a : k⸨X⸩) (v : V) : Φ^[n] (a • v) = σ^[n] a • Φ^[n] v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iterate_succ_apply' Φ, ih, map_smulₛₗ, iterate_succ_apply' σ, iterate_succ_apply' Φ]
    rfl

private theorem frobenius_sub_sum_iterates (Φ : V →ₛₗ[(σ).toRingHom] V) (n : ℕ) (v : V) :
    Φ (∑ j ∈ range n, Φ^[j] v) - ∑ j ∈ range n, Φ^[j] v = Φ^[n] v - v := by
  rw [map_sum, ← sum_sub_distrib]
  simp_rw [← iterate_succ_apply' Φ]
  exact sum_range_sub (fun j => Φ^[j] v) n

/-- On a finite-dimensional Laurent-series vector space over an algebraically closed field,
the difference `Φ - 1` for positive coefficient Frobenius is surjective. -/
theorem surjective_sub_id_of_semilinear [Module.Finite k⸨X⸩ V] (hf : 0 < f)
    (Φ : V →ₛₗ[(σ).toRingHom] V) : Surjective (fun x => Φ x - x) := by
  classical
  intro v
  -- The first `finrank + 1` iterates of the target vector satisfy a nonzero relation.
  let n := Module.finrank k⸨X⸩ V
  let u (i : Fin (n + 1)) := Φ^[n - i.val] v
  have hu : ¬ LinearIndependent k⸨X⸩ u := by
    intro h
    simpa [n] using h.fintype_card_le_finrank
  obtain ⟨a, ha, i₀, hi₀⟩ := Fintype.not_linearIndependent_iff.mp hu
  -- Untwist each relation coefficient by the corresponding Frobenius power.
  let c (i : Fin (n + 1)) := (σ).symm^[n - i.val] (a i)
  have hinverse : LeftInverse σ (σ).symm := (σ).apply_symm_apply
  have hinv (i : Fin (n + 1)) : σ^[n - i.val] (c i) = a i := hinverse.iterate _ _
  let d (i : ℕ) := if hi : i < n + 1 then c ⟨i, hi⟩ else 0
  have hd : ∃ i ∈ range (n + 1), d i ≠ 0 := by
    refine ⟨i₀, mem_range.mpr i₀.isLt, ?_⟩
    simp only [d, i₀.isLt, dite_true, Fin.eta]
    intro hi
    apply hi₀
    rw [← hinv i₀, hi]
    exact iterate_fixed (map_zero σ) _
  obtain ⟨z, hz⟩ := surjective_sum_mul_coefficientFrobenius (p := p) hf d hd (-1)
  let w (i : Fin (n + 1)) := (c i * σ^[i.val] z) • v
  have hsum : ∑ i, w i = -v := by
    have hz' : (∑ i : Fin (n + 1), c i * σ^[i.val] z) = -1 := by
      rw [sum_fin_eq_sum_range]
      refine (sum_congr rfl fun i hi => ?_).trans hz
      have hil : i < n + 1 := mem_range.mp hi
      simp only [d, dite_eq_left hil, coefficientFrobenius_iterate]
    simp only [w, ← sum_smul, hz', neg_one_smul]
  have hiter (i : Fin (n + 1)) :
      Φ^[n - i.val] (w i) = σ^[n] z • (a i • u i) := by
    rw [frobenius_iterate_smul p, iterate_map_mul, hinv, ← iterate_add_apply,
      Nat.sub_add_cancel (by omega : i.val ≤ n), smul_smul, mul_comm]
  -- The iterated terms sum to zero, and their starting terms sum to `-v`.
  refine ⟨∑ i : Fin (n + 1), ∑ j ∈ range (n - i.val), Φ^[j] (w i), ?_⟩
  dsimp only
  rw [map_sum, ← sum_sub_distrib]
  simp_rw [frobenius_sub_sum_iterates p, hiter]
  rw [sum_sub_distrib, ← smul_sum, ha, smul_zero, hsum, zero_sub, neg_neg]

end LaurentSeries
