/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import TauCeti.RingTheory.AdicCompletion.Pi

/-!
# Newton's method over an adically complete ring

Let `R` be a commutative ring and `π ∈ R` an element for which `R` is `π`-adically complete
(`IsAdicComplete (Ideal.span {π}) R`). Let `A : (ι → R) → (ι → R)` be a map on a finite free
module, `M` a square matrix over `R` whose determinant is a unit, and `u₀` a point with
`A u₀ ≡ 0 mod π`. Suppose `M` is a *uniform linearisation* of `A` on the residue class of `u₀`:
for every `k ≥ 1` and all `u, u'` in that class with `u' ≡ u mod π^k`,

  `A u' ≡ A u + M (u' - u)  mod π^(k+1)`.

Then `A` has exactly one zero in the residue class of `u₀`
(`TauCeti.IsAdicComplete.existsUnique_eq_zero_of_isUnit_det`).

This is a multivariable form of Hensel's lemma with an integral linearisation. No polynomiality of
`A` is assumed: the linearisation hypothesis plays the role of the derivative, and the unit
determinant of `M` that of the nonvanishing of the Jacobian modulo `π`. Mathlib's
`Mathlib.NumberTheory.Padics.Hensel` is the one-variable polynomial case over `ℤ_p`. The theorem
supplies the canonical character of a Demushkin group: its values on the generators are the zero of
the map recording the values of the crossed homomorphisms on the relator.

## Main results

* `TauCeti.IsAdicComplete.existsUnique_eq_zero_of_isUnit_det`: Newton's method, the existence and
  uniqueness of the zero.
-/

public section

namespace TauCeti

open Matrix

variable {R : Type*} {ι : Type*} [CommRing R] (π : R) [IsAdicComplete (Ideal.span {π}) R]
  [Fintype ι] [DecidableEq ι]

/-- **Newton's method over a `π`-adically complete ring.** Let `A : (ι → R) → (ι → R)`, let `M` be
a matrix with unit determinant, and let `u₀` satisfy `A u₀ ≡ 0 mod π`. If `M` linearises `A`
uniformly on the residue class of `u₀`, in the sense that `A u' ≡ A u + M (u' - u) mod π^(k+1)`
whenever `u, u'` lie in that class and `u' ≡ u mod π^k` with `k ≥ 1`, then `A` has exactly one zero
in the residue class of `u₀`. -/
theorem IsAdicComplete.existsUnique_eq_zero_of_isUnit_det (A : (ι → R) → (ι → R))
    {M : Matrix ι ι R} (hM : IsUnit M.det) (u₀ : ι → R) (h₀ : ∀ i, π ∣ A u₀ i)
    (hA : ∀ u u' : ι → R, (∀ i, π ∣ u i - u₀ i) → (∀ i, π ∣ u' i - u₀ i) →
      ∀ k : ℕ, 1 ≤ k → (∀ i, π ^ k ∣ u' i - u i) →
        ∀ i, π ^ (k + 1) ∣ A u' i - A u i - (M *ᵥ (u' - u)) i) :
    ∃! u : ι → R, (∀ i, π ∣ u i - u₀ i) ∧ A u = 0 := by
  -- A matrix preserves coordinatewise divisibility.
  have hmulVec : ∀ (N : Matrix ι ι R) (v : ι → R) (d : R), (∀ i, d ∣ v i) → ∀ i, d ∣ (N *ᵥ v) i :=
    fun N v d hv i ↦ Finset.dvd_sum fun j _ ↦ (hv j).mul_left _
  -- The Newton step and its defining property.
  set T : (ι → R) → (ι → R) := fun u ↦ u - M⁻¹ *ᵥ A u with hTdef
  have hT : ∀ u, M *ᵥ (T u - u) = -A u := fun u ↦ by
    rw [hTdef]
    simp only [sub_sub_cancel_left, Matrix.mulVec_neg, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ hM, Matrix.one_mulVec]
  -- The Newton iterates, and the invariant they satisfy: they stay in the residue class of `u₀`
  -- and `A` vanishes on the `k`-th iterate modulo `π ^ (k + 1)`.
  set u : ℕ → ι → R := fun k ↦ T^[k] u₀ with hudef
  have hu_succ : ∀ k, u (k + 1) = T (u k) := fun k ↦ Function.iterate_succ_apply' T k u₀
  have hstep : ∀ k, (∀ i, π ^ (k + 1) ∣ A (u k) i) → ∀ i, π ^ (k + 1) ∣ u (k + 1) i - u k i :=
    fun k hk i ↦ by
      rw [hu_succ, hTdef]
      simp only [Pi.sub_apply, sub_sub_cancel_left, dvd_neg]
      exact hmulVec _ _ _ hk i
  have key : ∀ k, (∀ i, π ∣ u k i - u₀ i) ∧ ∀ i, π ^ (k + 1) ∣ A (u k) i := by
    intro k
    induction k with
    | zero =>
      refine ⟨fun i ↦ by simp [hudef], fun i ↦ ?_⟩
      simpa [hudef] using h₀ i
    | succ k ih =>
      have hclass : ∀ i, π ∣ u (k + 1) i - u₀ i := fun i ↦ by
        have h1 := (dvd_pow_self π (Nat.succ_ne_zero k)).trans (hstep k ih.2 i)
        have h2 := ih.1 i
        simpa only [sub_add_sub_cancel] using dvd_add h1 h2
      refine ⟨hclass, fun i ↦ ?_⟩
      have h1 := hA (u k) (u (k + 1)) ih.1 hclass (k + 1) (by omega) (hstep k ih.2) i
      rw [hu_succ, hT, Pi.neg_apply, sub_neg_eq_add, sub_add_cancel] at h1
      rwa [hu_succ]
  -- Consecutive iterates are congruent modulo `π ^ (k + 1)`, so the sequence is Cauchy.
  have hconsec : ∀ k i, π ^ (k + 1) ∣ u (k + 1) i - u k i := fun k ↦ hstep k (key k).2
  have hcauchy : ∀ {m n : ℕ}, m ≤ n →
      u m ≡ u n [SMOD ((Ideal.span {π}) ^ m • ⊤ : Submodule R (ι → R))] := by
    intro m n hmn
    rw [SModEq.sub_mem, mem_span_singleton_pow_smul_top_iff]
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      intro i
      have h1 := (pow_dvd_pow π (by omega : m ≤ n + 1)).trans (hconsec n i)
      simpa only [Pi.sub_apply, sub_sub_sub_cancel_right] using dvd_sub (ih i) h1
  obtain ⟨L, hL⟩ := IsPrecomplete.prec inferInstance hcauchy
  have hL' : ∀ k i, π ^ k ∣ L i - u k i := fun k i ↦ by
    have := (mem_span_singleton_pow_smul_top_iff π _ k).1 (SModEq.sub_mem.1 (hL k)) i
    rw [Pi.sub_apply] at this
    exact (dvd_neg.2 this).trans (by rw [neg_sub])
  have hLclass : ∀ i, π ∣ L i - u₀ i := fun i ↦ by
    have h1 : π ∣ L i - u 1 i := by simpa only [pow_one] using hL' 1 i
    simpa only [sub_add_sub_cancel] using dvd_add h1 ((key 1).1 i)
  -- `A L` vanishes modulo every power of `π`, hence vanishes.
  have hAL : A L = 0 := by
    refine IsHausdorff.haus (I := Ideal.span {π}) inferInstance _ fun k ↦ ?_
    rw [SModEq.zero, mem_span_singleton_pow_smul_top_iff]
    intro i
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    have h1 := hA (u k) L (key k).1 hLclass k hk (hL' k) i
    have h2 := (pow_dvd_pow π (Nat.le_succ k)).trans ((key k).2 i)
    have h3 := hmulVec M (L - u k) (π ^ k) (fun j ↦ by simpa using hL' k j) i
    have h4 := (pow_dvd_pow π (Nat.le_succ k)).trans h1
    simpa only [sub_add_cancel] using dvd_add (dvd_add h4 h3) h2
  refine ⟨L, ⟨hLclass, hAL⟩, fun v ⟨hv, hAv⟩ ↦ ?_⟩
  -- Uniqueness: two zeros in the residue class agree modulo every power of `π`.
  have hdiff : ∀ k i, π ^ k ∣ v i - L i := by
    intro k
    induction k with
    | zero => exact fun i ↦ by simp
    | succ k ih =>
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · intro i
        simpa only [zero_add, pow_one, sub_sub_sub_cancel_right] using dvd_sub (hv i) (hLclass i)
      have h1 := hA L v hLclass hv k hk ih
      simp only [hAL, hAv, Pi.zero_apply, sub_self, zero_sub, dvd_neg] at h1
      have h2 := hmulVec M⁻¹ _ _ h1
      rwa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hM, Matrix.one_mulVec] at h2
  funext i
  refine sub_eq_zero.1 (IsHausdorff.haus (I := Ideal.span {π}) inferInstance _ fun k ↦ ?_)
  rw [SModEq.zero, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  obtain ⟨c, hc⟩ := hdiff k i
  exact ⟨c, Submodule.mem_top, by rw [smul_eq_mul, hc]⟩

end TauCeti
