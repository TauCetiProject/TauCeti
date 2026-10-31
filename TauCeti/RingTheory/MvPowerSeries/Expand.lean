/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Quotient
public import Mathlib.RingTheory.MvPowerSeries.Expand
public import Mathlib.RingTheory.MvPowerSeries.Restricted
public import TauCeti.Data.Nat.ModEq
-- Proof-only: divisibility by a constant is coefficientwise divisibility.
import TauCeti.RingTheory.MvPowerSeries.Dvd

/-!
# Expanding multivariate power series

This file records general facts about Mathlib's expansion `f(X) ↦ f(X^p)` of multivariate power
series. Substituting `X i ↦ X i ^ p` multiplies every exponent by `p`, so the weight of `p • μ`
at the polyradii `r` is the weight of `μ` at `r ^ p`, and `f(X^p)` is restricted at `r` exactly
when `f` is restricted at `r ^ p`. In finitely many variables, the coefficient at `p • μ + ν` of
a sum `∑ X^ν' g_ν'(X^p)` over the exponents `ν'` with `ν' i < p` is the coefficient at `μ` of
`g_ν`; this is the formal uniqueness of the decomposition along the expansion.

Expansion by `p ^ i` is the integral shadow of the Frobenius: if `φ` is a ring endomorphism with
`φ(a) ≡ a ^ (p ^ i)` modulo `p`, then `ψ ^ (p ^ i) ≡ (φ ψ)(X ^ (p ^ i))` modulo `p` for every power
series `ψ`, where `φ ψ` applies `φ` to the coefficients. Modulo `p` this is Mathlib's
`MvPowerSeries.map_iterateFrobenius_expand`. Such congruences drive integrality arguments for
power series defined by functional equations, as in Hazewinkel's functional equation lemma.

## Main results

* `MvPowerSeries.prod_pow_nsmul`: the weight of `p • μ` at `r` is the weight of `μ` at `r ^ p`.
* `MvPowerSeries.isRestricted_expand_iff`: `f(X^p)` is restricted at `r` exactly when `f` is
  restricted at `r ^ p`.
* `MvPowerSeries.IsRestricted.coeff_nsmul_add`: restrictedness of an expansion component.
* `MvPowerSeries.coeff_sum_monomial_mul_expand`: the coefficients of `∑ X^ν g_ν(X^p)`.
* `MvPowerSeries.natCast_dvd_pow_sub_expand_map`: if `φ(a) ≡ a ^ (p ^ i)` modulo the prime `p`,
  then `p` divides `ψ ^ (p ^ i) - (φ ψ)(X ^ (p ^ i))`.
-/

public section

namespace MvPowerSeries

open Filter

variable {σ : Type*} (p : ℕ)

/-- The weight at the polyradii `r` of the exponent `p • μ` is the weight of `μ` at the polyradii
`t = r ^ p`. -/
theorem prod_pow_nsmul {M : Type*} [CommMonoid M] {r t : σ → M} (ht : ∀ i, r i ^ p = t i)
    (μ : σ →₀ ℕ) : (p • μ).prod (r · ^ ·) = μ.prod (t · ^ ·) := by
  rw [Finsupp.prod_of_support_subset _ Finsupp.support_smul _ fun i _ ↦ pow_zero (r i)]
  exact Finset.prod_congr rfl fun i _ ↦ by simp [pow_mul, ht]

variable (hp : p ≠ 0)

include hp in
/-- **Restrictedness of an expansion.** The series `f(X^p)` is restricted at the polyradii `r`
exactly when `f` is restricted at the polyradii `r ^ p`. -/
theorem isRestricted_expand_iff {R : Type*} [NormedCommRing R] {r t : σ → ℝ}
    (ht : ∀ i, r i ^ p = t i) {f : MvPowerSeries σ R} :
    IsRestricted r (expand p hp f) ↔ IsRestricted t f := by
  have he : Function.Injective (p • · : (σ →₀ ℕ) → σ →₀ ℕ) := nsmul_right_injective hp
  have hcomp : (fun μ : σ →₀ ℕ ↦ ‖coeff μ f‖ * μ.prod (t · ^ ·)) =
      (fun α ↦ ‖coeff α (expand p hp f)‖ * α.prod (r · ^ ·)) ∘ (p • ·) := by
    funext μ
    simp [coeff_expand_smul, prod_pow_nsmul p ht]
  unfold IsRestricted
  rw [hcomp]
  refine ⟨fun h ↦ h.comp he.tendsto_cofinite, fun h U hU ↦ ?_⟩
  -- the weighted coefficients of `f(X^p)` vanish away from the exponents `p • μ`
  have hfin : {μ | ‖coeff (p • μ) (expand p hp f)‖ * (p • μ).prod (r · ^ ·) ∉ U}.Finite := h hU
  refine (hfin.image (p • ·)).subset fun α hα ↦ ?_
  by_cases hα0 : coeff α (expand p hp f) = 0
  · exact absurd (by simpa [hα0] using mem_of_mem_nhds hU) hα
  · obtain ⟨μ, -, rfl⟩ := support_expand_subset p hp f (a := α) hα0
    exact ⟨μ, hα, rfl⟩

/-- Extracting the coefficients in an arithmetic progression of exponents preserves
restrictedness, with the polyradii raised to the common step. -/
theorem IsRestricted.coeff_nsmul_add {R : Type*} [NormedRing R] {r t : σ → ℝ}
    [∀ i, Fact (0 < r i)] {p : ℕ} {f : MvPowerSeries σ R} (hf : IsRestricted r f)
    (hp : p ≠ 0) (ht : ∀ i, r i ^ p = t i) (ν : σ →₀ ℕ) :
    IsRestricted t (fun μ ↦ coeff (p • μ + ν) f : MvPowerSeries σ R) := by
  have hi : Function.Injective fun μ : σ →₀ ℕ ↦ p • μ + ν :=
    (add_left_injective ν).comp (nsmul_right_injective hp)
  have hpos : 0 < ν.prod (r · ^ ·) := Finset.prod_pos fun i _ ↦ pow_pos Fact.out _
  have h := (hf.comp hi.tendsto_cofinite).const_mul (ν.prod (r · ^ ·))⁻¹
  rw [mul_zero] at h
  refine h.congr fun μ ↦ ?_
  have hc : coeff μ (fun μ ↦ coeff (p • μ + ν) f : MvPowerSeries σ R) =
      coeff (p • μ + ν) f := coeff_apply _ μ
  rw [hc, Function.comp_apply,
    Finsupp.prod_add_index' (fun _ ↦ pow_zero _) (fun _ _ _ ↦ pow_add _ _ _),
    prod_pow_nsmul p ht]
  field_simp [hpos.ne']

/-- The coefficient at `p • μ + ν` of a sum `∑ X^ν' g_ν'(X^p)` over the exponents `ν'` with
`ν' i < p` is the coefficient at `μ` of `g_ν`. -/
theorem coeff_sum_monomial_mul_expand {R : Type*} [CommRing R] [Fintype σ] [DecidableEq σ]
    (g : (σ → Fin p) → MvPowerSeries σ R) (μ : σ →₀ ℕ) (ν : σ → Fin p) :
    coeff (p • μ + Finsupp.equivFunOnFinite.symm (Fin.val ∘ ν))
        (∑ ν', monomial (Finsupp.equivFunOnFinite.symm (Fin.val ∘ ν')) 1 *
          expand p hp (g ν')) = coeff μ (g ν) := by
  classical
  rw [map_sum, Finset.sum_eq_single ν]
  · simp [coeff_monomial_mul]
  · intro ν' _ hν'
    rw [coeff_monomial_mul]
    split_ifs with hle
    · obtain ⟨i, hi⟩ := Function.ne_iff.mp hν'
      rw [one_mul]
      refine coeff_expand_of_not_dvd p hp (g ν') (i := i) ?_
      have hle' := hle i
      simp only [Finsupp.coe_tsub, Finsupp.coe_add, Finsupp.coe_smul,
        Finsupp.coe_equivFunOnFinite_symm, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
        Function.comp_apply, smul_eq_mul] at hle' ⊢
      exact Nat.not_dvd_mul_add_sub (ν i).isLt (ν' i).isLt (fun h ↦ hi (Fin.ext h.symm)) hle'
    · rfl
  · simp

/-- **The Frobenius congruence for power series.** Let `p` be a prime and `φ` a ring endomorphism
of `A` with `φ(a) ≡ a ^ (p ^ i)` modulo `p` for all `a`. Then `p` divides
`ψ ^ (p ^ i) - (φ ψ)(X ^ (p ^ i))` for every power series `ψ` over `A`, where `φ ψ` applies `φ` to
the coefficients of `ψ`. -/
theorem natCast_dvd_pow_sub_expand_map {A : Type*} [CommRing A] {p : ℕ} [Fact p.Prime] (i : ℕ)
    {φ : A →+* A} (hφ : ∀ a, (p : A) ∣ φ a - a ^ p ^ i) (ψ : MvPowerSeries σ A) :
    (p : MvPowerSeries σ A) ∣ ψ ^ p ^ i - expand (p ^ i) (NeZero.ne _) (map φ ψ) := by
  set I := Ideal.span {(p : A)}
  rw [← map_natCast (C (σ := σ) (R := A)), C_dvd_iff_dvd_coeff]
  intro d
  -- reduce the coefficients modulo `p`, where `φ` becomes the `i`-th power of the Frobenius
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem, ← coeff_map, map_sub, map_pow,
    map_expand, map_map]
  refine (congrArg (coeff d) (sub_eq_zero.mpr ?_)).trans (map_zero _)
  by_cases hI : (p : A) ∈ nonunits A
  · have : CharP (A ⧸ I) p := CharP.quotient A p hI
    have hc : (Ideal.Quotient.mk I).comp φ =
        (iterateFrobenius (A ⧸ I) p i).comp (Ideal.Quotient.mk I) := by
      ext a
      simp only [RingHom.comp_apply, iterateFrobenius_def, ← map_pow]
      rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
      exact hφ a
    rw [hc, ← map_map, ← map_expand, map_iterateFrobenius_expand _ (NeZero.ne p)]
  · have : Subsingleton (A ⧸ I) := by
      rw [Ideal.Quotient.subsingleton_iff, Ideal.span_singleton_eq_top]
      simpa [nonunits] using hI
    exact ext fun _ ↦ Subsingleton.elim _ _

end MvPowerSeries
