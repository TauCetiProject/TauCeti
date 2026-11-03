/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.VanDerPut.Basic
public import TauCeti.NumberTheory.Padics.QuotientTower

/-!
# Finite van der Put expansions

A continuous function on `ℤ_p` is constant on residue classes modulo `p ^ h` exactly when its
van der Put coefficients vanish at every index `n ≥ p ^ h`. At that level its expansion is the
finite sum over `n < p ^ h`. Consequently locally constant functions are exactly the continuous
functions with finitely supported van der Put coefficients.

These statements need only a Hausdorff target with an additive commutative group structure.
No norm, completeness, scalar action, or continuity of addition on the target is needed. The
finite expansion follows from the telescoping identity and continuity along p-adic truncations.

## References

* W. H. Schikhof, *Ultrametric Calculus*, Cambridge University Press, 1984, §62.
* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §I.3.
-/

public section

open Filter Topology

namespace PadicInt

variable {p : ℕ} [hp : Fact p.Prime] {E : Type*} [AddCommGroup E] [TopologicalSpace E]

/-- If all van der Put coefficients beyond level `h` vanish, the expansion is the finite sum
of the terms indexed by `n < p ^ h`. -/
theorem sum_vanDerPutTerm_eq_of_vanDerPutCoeff_eq_zero [T2Space E]
    (f : C(ℤ_[p], E)) (h : ℕ) (hf : ∀ n, p ^ h ≤ n → vanDerPutCoeff f n = 0)
    (x : ℤ_[p]) :
    ∑ n ∈ Finset.range (p ^ h), vanDerPutTerm (vanDerPutCoeff f n) n x = f x := by
  have heq : ∀ᶠ k in atTop,
      f (x.appr k) = ∑ n ∈ Finset.range (p ^ h), vanDerPutTerm (vanDerPutCoeff f n) n x := by
    filter_upwards [eventually_ge_atTop h] with k hk
    rw [← sum_vanDerPutTerm_vanDerPutCoeff_apply f x k]
    symm
    exact Finset.sum_subset (Finset.range_mono (Nat.pow_le_pow_right hp.out.pos hk))
      fun n _ hn ↦ by simp [hf n (Nat.le_of_not_gt (by simpa using hn))]
  exact tendsto_nhds_unique tendsto_const_nhds
    ((f.continuous.continuousAt.tendsto.comp (tendsto_appr x)).congr' heq)

/-- A continuous function is constant on the residue classes modulo `p ^ h` exactly when its
van der Put coefficients vanish at every index `n ≥ p ^ h`. At `h = 0`, this says that only the
constant term can remain. -/
theorem vanDerPutCoeff_eq_zero_iff_eq_appr [T2Space E] (f : C(ℤ_[p], E)) (h : ℕ) :
    (∀ n, p ^ h ≤ n → vanDerPutCoeff f n = 0) ↔ ∀ x, f (x.appr h) = f x := by
  constructor
  · intro hf x
    rw [← sum_vanDerPutTerm_vanDerPutCoeff_apply f x h]
    exact sum_vanDerPutTerm_eq_of_vanDerPutCoeff_eq_zero f h hf x
  · intro hf n hn
    have hn0 : n ≠ 0 := (pow_pos hp.out.pos h).trans_le hn |>.ne'
    have hlog : h ≤ Nat.log p n := (Nat.le_log_iff_pow_le hp.out.one_lt hn0).mpr hn
    rw [vanDerPutCoeff_of_ne_zero f hn0, ← hf n, ← hf (n % p ^ Nat.log p n : ℕ)]
    simp only [appr_natCast, Nat.mod_mod_of_dvd _ (pow_dvd_pow p hlog), sub_self]

/-- A continuous function on `ℤ_p` is locally constant exactly when its van der Put coefficients
have finite support. This includes the zero function and arbitrary Hausdorff additive targets. -/
theorem isLocallyConstant_iff_finite_support_vanDerPutCoeff [T2Space E] (f : C(ℤ_[p], E)) :
    IsLocallyConstant f ↔ (Function.support (vanDerPutCoeff f)).Finite := by
  constructor
  · intro hf
    obtain ⟨h, g, hg⟩ := (TauCeti.FiniteQuotientTower.padicTower p).exists_comp_q_eq
      (hf.comp_continuous continuous_toAdd)
    have hfactor (x : ℤ_[p]) :
        g (Multiplicative.ofAdd (toZModPow h x)) = f x := by
      simpa only [Function.comp_apply, TauCeti.FiniteQuotientTower.padicTower_q_ofAdd,
        toAdd_ofAdd] using congrFun hg (Multiplicative.ofAdd x)
    have htrunc : ∀ x : ℤ_[p], f (x.appr h) = f x := by
      intro x
      rw [← hfactor, map_natCast, ← toZModPow_eq_natCast_appr, hfactor]
    exact (Finset.finite_toSet (Finset.range (p ^ h))).subset fun n hn ↦ by
      exact Finset.mem_range.mpr (lt_of_not_ge fun hle ↦ hn
        ((vanDerPutCoeff_eq_zero_iff_eq_appr f h).mpr htrunc n hle))
  · intro hf
    obtain ⟨N, hN⟩ := hf.bddAbove
    have hcoeff : ∀ n, p ^ (N + 1) ≤ n → vanDerPutCoeff f n = 0 := by
      intro n hn
      by_contra hne
      have := hN hne
      have := Nat.lt_pow_self hp.out.one_lt (n := N + 1)
      omega
    have htrunc := (vanDerPutCoeff_eq_zero_iff_eq_appr f (N + 1)).mp hcoeff
    have hloc : IsLocallyConstant (fun x : ℤ_[p] ↦ f (x.appr (N + 1))) :=
      ((IsLocallyConstant.iff_continuous _).mpr (continuous_appr (N + 1))).comp
        (fun n : ℕ ↦ f n)
    exact (funext htrunc) ▸ hloc

end PadicInt
