/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.Topology.MetricSpace.Ultra.Basic
import TauCeti.RingTheory.MvPowerSeries.GaussNorm
import TauCeti.RingTheory.MvPowerSeries.MonomialSelection
import TauCeti.RingTheory.MvPowerSeries.Rename
import TauCeti.RingTheory.PowerSeries.Substitution

/-!
# Maximum derivative norms in a formal parameter

For a formal parameter `t(z)` over an ultrametric seminormed ring, the largest norm of the
`n`-th derivative at zero of an integral series in `t(z)` is attained by a power of `t`.
If addition of the `z` variables is given by an integral power series in the two `t`
variables, these maxima are submultiplicative.

## References

* N. M. Katz, *Divisibilities, congruences, and Cartier duality* (1981), pp. 667–678.
* The maximum and its submultiplicativity correspond to `New.CMLattice.maxDerivNorm` and
  `New.CMLattice.maxDerivNorm_add_le` in `grh/src/New/Derivatives/Sharpness/OneCurve.lean` of
  [grh-lean](https://github.com/lsernau/grh-lean), revision `72fead1`.
-/

public section

open Finset
open scoped Nat

namespace PowerSeries

variable {R : Type*} [SeminormedCommRing R]

/-- The largest norm of the `n`-th derivative at zero among powers `t^j` with `j ≤ n`.
Over an ultrametric ring with `‖1‖ = 1`, when `t` has zero constant coefficient, this is also
the largest such norm among all series in `t` with integral coefficients. -/
noncomputable def maxDerivNorm (t : R⟦X⟧) (n : ℕ) : ℝ :=
  (range (n + 1)).sup' (nonempty_range_add_one) fun j ↦ ‖(n ! : R) * coeff n (t ^ j)‖

/-- Each power in the finite maximum contributes a lower bound. -/
theorem norm_factorial_mul_coeff_pow_le_maxDerivNorm (t : R⟦X⟧) {n j : ℕ} (hj : j ≤ n) :
    ‖(n ! : R) * coeff n (t ^ j)‖ ≤ t.maxDerivNorm n :=
  le_sup' (fun j ↦ ‖(n ! : R) * coeff n (t ^ j)‖) (mem_range_succ_iff.mpr hj)

/-- Some power `t^j` with `j ≤ n` realizes the maximum. -/
theorem exists_maxDerivNorm_eq (t : R⟦X⟧) (n : ℕ) :
    ∃ j ≤ n, t.maxDerivNorm n = ‖(n ! : R) * coeff n (t ^ j)‖ := by
  obtain ⟨j, hj, he⟩ := exists_mem_eq_sup' nonempty_range_add_one
    (fun j ↦ ‖(n ! : R) * coeff n (t ^ j)‖)
  exact ⟨j, mem_range_succ_iff.mp hj, he⟩

/-- The maximum derivative norm is nonnegative, including when all the derivatives vanish. -/
theorem maxDerivNorm_nonneg (t : R⟦X⟧) (n : ℕ) : 0 ≤ t.maxDerivNorm n :=
  (norm_nonneg _).trans (t.norm_factorial_mul_coeff_pow_le_maxDerivNorm n.zero_le)

/-- The maximum in degree zero is one. -/
@[simp] theorem maxDerivNorm_zero [NormOneClass R] (t : R⟦X⟧) : t.maxDerivNorm 0 = 1 := by
  obtain ⟨j, hj, he⟩ := t.exists_maxDerivNorm_eq 0
  simpa [Nat.eq_zero_of_le_zero hj] using he

/-- An integral series in `t` cannot have a larger `n`-th derivative norm than the maximum
over powers of `t`. Only coefficients of the outer series through degree `n` are needed. -/
theorem norm_factorial_mul_coeff_subst_le_maxDerivNorm [IsUltrametricDist R]
    (t : R⟦X⟧) (ht : t.constantCoeff = 0) (g : R⟦X⟧) (n : ℕ)
    (hg : ∀ j ≤ n, ‖coeff j g‖ ≤ 1) :
    ‖(n ! : R) * coeff n (g.subst t)‖ ≤ t.maxDerivNorm n := by
  rw [coeff_subst_eq_sum_range g ht, Finset.mul_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (t.maxDerivNorm_nonneg n)
    fun j hj ↦ ?_
  rw [Algebra.smul_def, Algebra.algebraMap_self_apply, mul_left_comm]
  exact (norm_mul_le _ _).trans <| (mul_le_of_le_one_left (norm_nonneg _)
    (hg j (mem_range_succ_iff.mp hj))).trans
    (t.norm_factorial_mul_coeff_pow_le_maxDerivNorm (mem_range_succ_iff.mp hj))

/-- An upper bound for all integral substitutions is precisely an upper bound for the
maximum derivative norm. -/
theorem maxDerivNorm_le_iff [IsUltrametricDist R] [NormOneClass R]
    (t : R⟦X⟧) (ht : t.constantCoeff = 0) (n : ℕ) (B : ℝ) :
    t.maxDerivNorm n ≤ B ↔ ∀ g : R⟦X⟧, (∀ j, ‖coeff j g‖ ≤ 1) →
      ‖(n ! : R) * coeff n (g.subst t)‖ ≤ B := by
  refine ⟨fun h g hg ↦ (t.norm_factorial_mul_coeff_subst_le_maxDerivNorm ht g n
    (fun j _ ↦ hg j)).trans h, fun h ↦ ?_⟩
  obtain ⟨j, _, hj⟩ := t.exists_maxDerivNorm_eq n
  have hsub : HasSubst t := .of_constantCoeff_zero' ht
  rw [hj, ← subst_X (R := R) hsub, ← subst_pow hsub]
  exact h (X ^ j) fun i ↦ by rw [coeff_X_pow]; split_ifs <;> simp

private theorem norm_factorials_mul_coeff_subst_le [IsUltrametricDist R]
    (t : R⟦X⟧) (ht : t.constantCoeff = 0) (G : MvPowerSeries (Fin 2) R)
    (hG : ∀ e, ‖MvPowerSeries.coeff e G‖ ≤ 1) (m n : ℕ) :
    let d := Finsupp.single (0 : Fin 2) m + Finsupp.single 1 n
    let a := fun i : Fin 2 ↦ t.subst (MvPowerSeries.X i)
    ‖((m ! : R) * (n ! : R)) * MvPowerSeries.coeff d (G.subst a)‖ ≤
      t.maxDerivNorm m * t.maxDerivNorm n := by
  dsimp only
  let d := Finsupp.single (0 : Fin 2) m + Finsupp.single 1 n
  let a (i : Fin 2) : MvPowerSeries (Fin 2) R := t.subst (MvPowerSeries.X i)
  have ha₀ (i : Fin 2) : MvPowerSeries.constantCoeff (a i) = 0 := by
    rw [constantCoeff_subst_of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i), ht, map_zero]
  have ha := MvPowerSeries.hasSubst_of_constantCoeff_zero ha₀
  let c : R := (m ! : R) * (n ! : R)
  obtain ⟨e, _, he⟩ := MvPowerSeries.exists_monomial_norm_coeff_subst_mul_le
    ha ha₀ G (MvPowerSeries.C c) d (fun k _ ↦ hG k)
  have he' : ‖c * MvPowerSeries.coeff d (G.subst a)‖ ≤
      ‖c * MvPowerSeries.coeff d (a 0 ^ e 0 * a 1 ^ e 1)‖ := by
    simpa [MvPowerSeries.substAlgHom_apply, MvPowerSeries.coeff_mul_C, mul_comm c,
      Finsupp.prod_fintype, Fin.prod_univ_two] using he
  let emb (i : Fin 2) : Unit ↪ Fin 2 := ⟨fun _ ↦ i, fun _ _ _ ↦ Subsingleton.elim _ _⟩
  have hrename (i : Fin 2) : a i ^ e i = MvPowerSeries.rename (emb i) (t ^ e i) := by
    rw [MvPowerSeries.rename_eq_subst]
    -- The constant renaming of `Unit` substitutes its sole variable by `X i`.
    exact (subst_pow (HasSubst.X (S := R) i) t (e i)).symm
  have hcoef : MvPowerSeries.coeff d (a 0 ^ e 0 * a 1 ^ e 1) =
      coeff m (t ^ e 0) * coeff n (t ^ e 1) := by
    rw [hrename 0, hrename 1]
    have h₀ : emb 0 () = 0 := rfl
    have h₁ : emb 1 () = 1 := rfl
    simpa only [d, Finsupp.embDomain_single, h₀, h₁, coeff_coeToMvPowerSeries] using
      MvPowerSeries.coeff_embDomain_add_embDomain_rename_mul_rename
        (e₁ := emb 0) (e₂ := emb 1) (t ^ e 0) (t ^ e 1)
        (fun _ _ ↦ Fin.zero_ne_one) (Finsupp.single () m) (Finsupp.single () n)
  have hb (k j : ℕ) : ‖(k ! : R) * coeff k (t ^ j)‖ ≤ t.maxDerivNorm k := by
    obtain hj | hj := le_or_gt j k
    · exact t.norm_factorial_mul_coeff_pow_le_maxDerivNorm hj
    · rw [coeff_of_lt_order k ((Nat.cast_lt.mpr hj).trans_le
        (le_order_pow_of_constantCoeff_eq_zero j ht)), mul_zero, norm_zero]
      exact t.maxDerivNorm_nonneg k
  refine he'.trans ?_
  dsimp only [c]
  rw [hcoef, mul_mul_mul_comm]
  exact norm_mul_le_of_le (hb m (e 0)) (hb n (e 1))

/-- If `t(z₀ + z₁)` is an integral series in `t(z₀)` and `t(z₁)`, its maximum derivative
norms are submultiplicative. In particular, the integral law can be the formal group law
in the parameter `t`. -/
theorem maxDerivNorm_add_le [IsUltrametricDist R]
    (t : R⟦X⟧) (ht : t.constantCoeff = 0) (G : MvPowerSeries (Fin 2) R)
    (hG : ∀ e, ‖MvPowerSeries.coeff e G‖ ≤ 1)
    (hadd : t.subst (MvPowerSeries.X (R := R) (0 : Fin 2) + MvPowerSeries.X (1 : Fin 2)) =
      G.subst (fun i ↦ t.subst (MvPowerSeries.X i))) (m n : ℕ) :
    t.maxDerivNorm (m + n) ≤ t.maxDerivNorm m * t.maxDerivNorm n := by
  obtain ⟨j, _, hj⟩ := t.exists_maxDerivNorm_eq (m + n)
  rcases j with _ | j
  · by_cases h : m + n = 0
    · obtain ⟨rfl, rfl⟩ := Nat.add_eq_zero_iff.mp h
      have hnorm := norm_mul_le (1 : R) 1
      simpa [hj] using hnorm
    · rw [hj, pow_zero, coeff_one, ite_eq_right h, mul_zero, norm_zero]
      exact mul_nonneg (t.maxDerivNorm_nonneg m) (t.maxDerivNorm_nonneg n)
  let d := Finsupp.single (0 : Fin 2) m + Finsupp.single 1 n
  let a (i : Fin 2) : MvPowerSeries (Fin 2) R := t.subst (MvPowerSeries.X i)
  have ha₀ (i : Fin 2) : MvPowerSeries.constantCoeff (a i) = 0 := by
    rw [constantCoeff_subst_of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i), ht, map_zero]
  have heq :
      (t ^ (j + 1)).subst (MvPowerSeries.X (R := R) (0 : Fin 2) + MvPowerSeries.X (1 : Fin 2)) =
        (G ^ (j + 1)).subst a := by
    rw [subst_pow (.of_constantCoeff_zero (by simp)), hadd,
      MvPowerSeries.subst_pow (MvPowerSeries.hasSubst_of_constantCoeff_zero ha₀)]
  have hm : d 0 = m := by simp [d, Finsupp.single_eq_of_ne Fin.zero_ne_one]
  have hn : d 1 = n := by simp [d, Finsupp.single_eq_of_ne (Ne.symm Fin.zero_ne_one)]
  have hcoeff := congrArg (fun f ↦ MvPowerSeries.coeff d f) heq
  simp only [coeff_subst_X_zero_add_X_one, hm, hn] at hcoeff
  have hfact : ((m + n)! : R) = ((m + n).choose m : R) * (m ! : R) * (n ! : R) := by
    have h := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right m n)
    rw [Nat.add_sub_cancel_left] at h
    simpa only [Nat.cast_mul] using congrArg (fun k : ℕ ↦ (k : R)) h.symm
  rw [hj, hfact]
  calc
    _ = ‖((m ! : R) * (n ! : R)) * MvPowerSeries.coeff d ((G ^ (j + 1)).subst a)‖ := by
      rw [← hcoeff]
      congr 1
      ring
    _ ≤ _ := norm_factorials_mul_coeff_subst_le t ht (G ^ (j + 1)) (fun e ↦
      MvPowerSeries.norm_coeff_pow_le_of_degree_le le_rfl (fun b _ ↦ hG b)
        (Nat.succ_ne_zero j) le_rfl) m n

end PowerSeries
