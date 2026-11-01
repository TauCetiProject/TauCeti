/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.Data.Int.DivMod
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Mathlib.Analysis.Normed.Field.Basic
import TauCeti.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.Ring

/-!
# Coefficients of quasi-periodic Tate theta series

Comparing Laurent coefficients in `f(qw) = c⁻¹ w⁻ᵈ f(w)` gives
`a(n + d) = c qⁿ a(n)`. For positive `d` and units `q, c`, restriction to the
indices `0, …, d - 1` is a linear equivalence from the solutions of this recurrence to `Rᵈ`.
The inverse is explicit: along the residue class `r` it multiplies the initial coefficient
by `cᵏ q^(rk + d k(k-1)/2)`. In particular, the coefficient space has rank `d`
over any nontrivial commutative ring, including in positive characteristic.

The degree-two case compares products of two translated theta functions with the first Tate
coordinate, and the degree-three case compares products of three translated theta functions
with lines in Tate coordinates. Over a complete normed field with `‖q‖ < 1`, the Laurent series
of every solution of positive degree converges at every unit, by the ratio test along each
residue class. Uniqueness of analytic Laurent expansions is not asserted.

## Main declarations

* `TauCeti.tateThetaCoefficients`: the submodule of bilateral coefficient sequences
  satisfying the recurrence.
* `TauCeti.tateThetaCoefficientsEquiv`: restriction to the first `d` coefficients,
  with an explicit inverse.
* `TauCeti.finrank_tateThetaCoefficients`: its rank over a nontrivial commutative ring.
* `TauCeti.hasSum_tateThetaCoefficients_mul`: transport of a convergent Laurent sum
  from `u` to `qu`.
* `TauCeti.summable_tateThetaCoefficients`: the Laurent series of a solution converges at
  every unit.

## References

* J. Tate, *A review of non-Archimedean elliptic functions* (1995).
* P. Roquette, *Analytic theory of elliptic functions over local fields* (1970).
-/

public section

namespace TauCeti

variable {R : Type*} [CommRing R]

/-- The Laurent coefficient recurrence for `f(qw) = c⁻¹ w⁻ᵈ f(w)`.
The parameter `d` is allowed to vanish here; the finite-coordinate equivalence requires
it to be positive. -/
def tateThetaCoefficients (q c : Rˣ) (d : ℕ) : Submodule R (ℤ → R) where
  carrier := {a | ∀ n, a (n + d) = ↑(c * q ^ n) * a n}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb n
    simp only [Pi.add_apply, ha n, hb n, mul_add]
  smul_mem' := by
    intro s a ha n
    simp only [Pi.smul_apply, smul_eq_mul, ha n]
    ring

/-- Membership is precisely the quasi-periodic coefficient recurrence. -/
@[simp]
theorem mem_tateThetaCoefficients_iff (q c : Rˣ) (d : ℕ) (a : ℤ → R) :
    a ∈ tateThetaCoefficients q c d ↔ ∀ n, a (n + d) = ↑(c * q ^ n) * a n :=
  Iff.rfl

private def thetaWeight (q c : Rˣ) (d : ℕ) (r k : ℤ) : Rˣ :=
  c ^ k * q ^ (r * k + d * (k * (k - 1) / 2))

private theorem thetaWeight_zero (q c : Rˣ) (d : ℕ) (r : ℤ) :
    thetaWeight q c d r 0 = 1 := by
  simp [thetaWeight]

private theorem thetaWeight_succ (q c : Rˣ) (d : ℕ) (r k : ℤ) :
    thetaWeight q c d r (k + 1) = (c * q ^ (r + d * k)) * thetaWeight q c d r k := by
  have htri : (k + 1) * (k + 1 - 1) / 2 = k * (k - 1) / 2 + k := by
    have : (k + 1) * (k + 1 - 1) = k * (k - 1) + 2 * k := by ring
    omega
  simp only [thetaWeight, htri]
  have hexponent : r * (k + 1) + (d : ℤ) * (k * (k - 1) / 2 + k) =
      (r + d * k) + (r * k + d * (k * (k - 1) / 2)) := by ring
  rw [hexponent, zpow_add, zpow_add]
  simp only [zpow_one]
  ac_rfl

private theorem theta_coeff_shift (q c : Rˣ) (d : ℕ)
    (a : tateThetaCoefficients q c d) (r k : ℤ) :
    a.val (r + d * k) = ↑(thetaWeight q c d r k) * a.val r := by
  induction k using Int.induction_on with
  | zero => simp [thetaWeight_zero]
  | succ k ih =>
    have hindex : r + (d : ℤ) * ((k : ℤ) + 1) = (r + d * k) + d := by ring
    rw [hindex, a.property, ih, thetaWeight_succ]
    simp [mul_assoc]
  | pred k ih =>
    have h := a.property (r + d * (-(k : ℤ) - 1))
    have hindex : r + (d : ℤ) * (-(k : ℤ) - 1) + d = r + d * -(k : ℤ) := by ring
    rw [hindex, ih] at h
    have hw := thetaWeight_succ q c d r (-(k : ℤ) - 1)
    simp only [sub_add_cancel] at hw
    rw [hw, Units.val_mul, mul_assoc] at h
    exact (Units.mul_right_inj (c * q ^ (r + d * (-(k : ℤ) - 1)))).mp h.symm

private def thetaResidue (d : ℕ) (hd : 0 < d) (n : ℤ) : Fin d :=
  ⟨(n % d).toNat, by
    have hp : (0 : ℤ) < d := by exact_mod_cast hd
    exact_mod_cast (Int.toNat_lt (Int.emod_nonneg n (ne_of_gt hp))).mpr
      (Int.emod_lt_of_pos n hp)⟩

private theorem thetaResidue_val (d : ℕ) (hd : 0 < d) (n : ℤ) :
    ((thetaResidue d hd n).val : ℤ) = n % d := by
  exact Int.toNat_of_nonneg (Int.emod_nonneg n (by omega))

private def thetaExtend (q c : Rˣ) (d : ℕ) (hd : 0 < d) (v : Fin d → R) (n : ℤ) : R :=
  ↑(thetaWeight q c d (n % d) (n / d)) * v (thetaResidue d hd n)

private theorem thetaExtend_mem (q c : Rˣ) (d : ℕ) (hd : 0 < d) (v : Fin d → R) :
    thetaExtend q c d hd v ∈ tateThetaCoefficients q c d := by
  intro n
  have hr : (n + d) % (d : ℤ) = n % d := by simp
  have hk : (n + d) / (d : ℤ) = n / d + 1 := by
    rw [Int.add_ediv_of_dvd_right (dvd_refl (d : ℤ)), Int.ediv_self (by omega)]
  have hi : thetaResidue d hd (n + d) = thetaResidue d hd n := by
    apply Fin.ext
    simp only [thetaResidue, hr]
  simp only [thetaExtend, hr, hk, hi, thetaWeight_succ, Units.val_mul]
  rw [Int.emod_add_mul_ediv n (d : ℤ)]
  simp [mul_assoc]

/-- Restriction of a quasi-periodic coefficient sequence to `0, …, d - 1`.
Every initial vector has a unique extension to all integer indices. -/
def tateThetaCoefficientsEquiv (q c : Rˣ) (d : ℕ) (hd : 0 < d) :
    tateThetaCoefficients q c d ≃ₗ[R] (Fin d → R) where
  toFun a i := a.val i
  invFun v := ⟨thetaExtend q c d hd v, thetaExtend_mem q c d hd v⟩
  left_inv a := by
    apply Subtype.ext
    funext n
    have h := theta_coeff_shift q c d a (n % d) (n / d)
    rw [Int.emod_add_mul_ediv n (d : ℤ)] at h
    simpa only [thetaExtend, thetaResidue_val] using h.symm
  right_inv v := by
    funext i
    have hr : (i : ℤ) % d = i := Int.emod_eq_of_lt (by omega) (by exact_mod_cast i.isLt)
    have hk : (i : ℤ) / d = 0 := Int.ediv_eq_zero_of_lt (by omega)
      (by exact_mod_cast i.isLt)
    have hi : thetaResidue d hd i = i := by
      apply Fin.ext
      simp [thetaResidue, hr]
    simp [thetaExtend, hr, hk, hi, thetaWeight_zero]
  map_add' a b := by ext i; rfl
  map_smul' s a := by ext i; rfl

/-- The finite-coordinate equivalence reads off the indicated coefficient. -/
@[simp]
theorem tateThetaCoefficientsEquiv_apply (q c : Rˣ) (d : ℕ) (hd : 0 < d)
    (a : tateThetaCoefficients q c d) (i : Fin d) :
    tateThetaCoefficientsEquiv q c d hd a i = a.val i := (rfl)

/-- Extending an initial vector preserves its initial coefficients. -/
@[simp]
theorem tateThetaCoefficientsEquiv_symm_apply_coe (q c : Rˣ) (d : ℕ) (hd : 0 < d)
    (v : Fin d → R) (i : Fin d) :
    ((tateThetaCoefficientsEquiv q c d hd).symm v).val i = v i := by
  exact congrFun ((tateThetaCoefficientsEquiv q c d hd).apply_symm_apply v) i

/-- The unique extension along each residue class, including negative indices. -/
theorem tateThetaCoefficientsEquiv_symm_apply (q c : Rˣ) (d : ℕ) (hd : 0 < d)
    (v : Fin d → R) (i : Fin d) (k : ℤ) :
    ((tateThetaCoefficientsEquiv q c d hd).symm v).val (i + d * k) =
      ↑(c ^ k * q ^ ((i : ℤ) * k + d * (k * (k - 1) / 2))) * v i := by
  have h := theta_coeff_shift q c d ((tateThetaCoefficientsEquiv q c d hd).symm v) i k
  simpa only [thetaWeight, tateThetaCoefficientsEquiv_symm_apply_coe] using h

/-- A positive-degree quasi-periodic coefficient space is finitely generated. -/
instance (q c : Rˣ) (d : ℕ) [NeZero d] :
    Module.Finite R (tateThetaCoefficients q c d) :=
  Module.Finite.equiv (tateThetaCoefficientsEquiv q c d
    (Nat.pos_of_ne_zero (NeZero.ne d))).symm

/-- Over a nontrivial commutative ring, the quasi-periodic Laurent coefficient space has
rank equal to its positive degree. -/
@[simp]
theorem finrank_tateThetaCoefficients [Nontrivial R] (q c : Rˣ)
    (d : ℕ) (hd : 0 < d) : Module.finrank R (tateThetaCoefficients q c d) = d := by
  rw [(tateThetaCoefficientsEquiv q c d hd).finrank_eq]
  simp

/-- A convergent bilateral Laurent series with the coefficient recurrence satisfies
`f(qu) = c⁻¹ u⁻ᵈ f(u)`. Convergence at `qu` follows from convergence at `u`.
No completeness or separation hypothesis is needed for this identity of sums. -/
theorem hasSum_tateThetaCoefficients_mul [TopologicalSpace R] [IsTopologicalRing R]
    (q c : Rˣ) (d : ℕ) (a : tateThetaCoefficients q c d) (u : Rˣ) {s : R}
    (hs : HasSum (fun n : ℤ ↦ a.val n * ↑(u ^ n)) s) :
    HasSum (fun n : ℤ ↦ a.val n * ↑((q * u) ^ n))
      (↑(c⁻¹ * u ^ (-(d : ℤ))) * s) := by
  have hshift := (Equiv.addRight (d : ℤ)).hasSum_iff.mpr hs
  have h := hshift.mul_left (↑(c⁻¹ * u ^ (-(d : ℤ))) : R)
  convert h using 1
  funext n
  simp only [Function.comp_apply, Equiv.coe_addRight]
  rw [a.property]
  simp only [mul_zpow, zpow_add, Units.val_mul]
  symm
  calc
    _ = ↑(c⁻¹ * c) * ↑(u ^ (-(d : ℤ)) * u ^ (d : ℤ)) *
        (a.val n * (↑(q ^ n) * ↑(u ^ n))) := by simp only [Units.val_mul]; ring
    _ = _ := by simp

section Convergence

variable {K : Type*} [NormedField K]

/-- Along a residue class, the coefficient recurrence multiplies consecutive terms of the
Laurent series by `c q^(r + d k) uᵈ`. -/
private theorem tateThetaCoefficients_term_add_one (q c : Kˣ) (d : ℕ)
    (a : tateThetaCoefficients q c d) (u : Kˣ) (r k : ℤ) :
    a.val (r + d * (k + 1)) * ↑(u ^ (r + d * (k + 1))) =
      ↑(c * q ^ (r + d * k) * u ^ (d : ℤ)) * (a.val (r + d * k) * ↑(u ^ (r + d * k))) := by
  have hidx : r + (d : ℤ) * (k + 1) = (r + d * k) + d := by ring
  rw [hidx, a.property, zpow_add u (r + d * k) d]
  simp only [Units.val_mul]
  ring

private theorem norm_tateThetaCoefficients_factor (q c : Kˣ) (d : ℕ) (u : Kˣ) (r k : ℤ) :
    ‖((c * q ^ (r + d * k) * u ^ (d : ℤ) : Kˣ) : K)‖ =
      ‖(c : K)‖ * ‖(q : K)‖ ^ r * ‖(u : K)‖ ^ d * (‖(q : K)‖ ^ d) ^ k := by
  have hq : ‖(q : K)‖ ≠ 0 := norm_ne_zero_iff.mpr q.ne_zero
  simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, norm_mul, norm_zpow, zpow_natCast,
    zpow_add₀ hq, zpow_mul, Units.val_pow_eq_pow_val, norm_pow]
  ring

/-- **Quasi-periodic coefficient sequences are entire.** Over a complete normed field, for
`‖q‖ < 1` and positive degree, the Laurent series of a solution of the coefficient recurrence
converges at every unit. -/
theorem summable_tateThetaCoefficients [CompleteSpace K] (q c : Kˣ) (hq : ‖(q : K)‖ < 1)
    {d : ℕ} (hd : 0 < d) (a : tateThetaCoefficients q c d) (u : Kˣ) :
    Summable (fun n : ℤ ↦ a.val n * ↑(u ^ n)) := by
  have hρ₀ : 0 ≤ ‖(q : K)‖ ^ d := by positivity
  have hρ : ‖(q : K)‖ ^ d < 1 := pow_lt_one₀ (norm_nonneg _) hq hd.ne'
  -- Each residue class `r + dℤ` is summable by the ratio test in both directions.
  have hclass (r : ℤ) : Summable (fun k : ℤ ↦ a.val (r + d * k) * ↑(u ^ (r + d * k))) := by
    have hA : 0 < ‖(c : K)‖ * ‖(q : K)‖ ^ r * ‖(u : K)‖ ^ d := by
      have := norm_pos_iff.mpr c.ne_zero
      have := norm_pos_iff.mpr q.ne_zero
      have := norm_pos_iff.mpr u.ne_zero
      positivity
    have hρ' : 0 < ‖(q : K)‖ ^ d := pow_pos (norm_pos_iff.mpr q.ne_zero) d
    refine Summable.of_nat_of_neg_add_one ?_ ?_
    · refine summable_of_norm_succ_le_mul_pow
        (C := ‖(c : K)‖ * ‖(q : K)‖ ^ r * ‖(u : K)‖ ^ d) hρ₀ hρ fun k ↦ le_of_eq ?_
      rw [Nat.cast_succ, tateThetaCoefficients_term_add_one, norm_mul,
        norm_tateThetaCoefficients_factor, zpow_natCast]
    · refine summable_of_norm_succ_le_mul_pow
        (C := (‖(c : K)‖ * ‖(q : K)‖ ^ r * ‖(u : K)‖ ^ d)⁻¹ * (‖(q : K)‖ ^ d) ^ 2)
        hρ₀ hρ fun k ↦ le_of_eq ?_
      have hstep := congrArg norm
        (tateThetaCoefficients_term_add_one q c d a u r (-((k : ℤ) + 2)))
      have hk : -((k : ℤ) + 2) + 1 = -((k : ℤ) + 1) := by ring
      rw [hk] at hstep
      simp only [norm_mul, norm_tateThetaCoefficients_factor] at hstep
      have hk' : -(((k + 1 : ℕ) : ℤ) + 1) = -((k : ℤ) + 2) := by push_cast; ring
      rw [hk']
      simp only [norm_mul]
      rw [hstep, zpow_neg, show (k : ℤ) + 2 = ((k + 2 : ℕ) : ℤ) by push_cast; ring,
        zpow_natCast, pow_add]
      field_simp
  -- Split the Laurent series into its `d` residue classes.
  have hsplit : (fun n : ℤ ↦ a.val n * ↑(u ^ n)) = fun n : ℤ ↦
      ∑ r ∈ Finset.range d, if (n % (d : ℤ)).toNat = r then a.val n * ↑(u ^ n) else 0 := by
    funext n
    have hmem : (n % (d : ℤ)).toNat ∈ Finset.range d := by
      rw [Finset.mem_range]
      have := Int.emod_lt_of_pos n (by exact_mod_cast hd : (0 : ℤ) < d)
      have := Int.emod_nonneg n (by exact_mod_cast hd.ne' : (d : ℤ) ≠ 0)
      omega
    simp [Finset.sum_ite_eq, hmem]
  rw [hsplit]
  refine summable_sum fun r hr ↦ ?_
  have hr' : r < d := Finset.mem_range.mp hr
  have hinj : Function.Injective (fun k : ℤ ↦ (r : ℤ) + d * k) := fun k l h ↦ by
    simpa [hd.ne'] using h
  refine (hinj.summable_iff fun n hn ↦ ?_).mp ?_
  · simp only [ite_eq_right_iff]
    intro hnr
    refine absurd ⟨n / d, ?_⟩ hn
    have := Int.emod_add_mul_ediv n d
    have := Int.emod_nonneg n (by exact_mod_cast hd.ne' : (d : ℤ) ≠ 0)
    simp only
    omega
  · convert hclass r using 2 with k
    have : ((r : ℤ) + d * k) % d = r := by
      rw [Int.add_mul_emod_self_left]
      exact Int.emod_eq_of_lt (by omega) (by exact_mod_cast hr')
    simp [this]

end Convergence

end TauCeti

end
