/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import TauCeti.Algebra.Polynomial.Identities
public import TauCeti.LinearAlgebra.Matrix.Divisibility
public import TauCeti.LinearAlgebra.Matrix.Nonsingular.Basic
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

The quantitative form allows a Jacobian that is only invertible up to `π ^ k`. Suppose `π` is a
non-zero-divisor, `J` is a linearisation of `A` on the class `t + π ^ (k + 1) R^ι` that gains
`k + 1` powers of `π` (`A x' ≡ A x + J (x' - x) mod π^(n + k + 1)` when `x' ≡ x mod π^n`,
`n ≥ k + 1`), and some integral matrix `M` satisfies `M * J = π ^ k • 1`. If
`A t ≡ 0 mod π ^ (2k + 1)`, then `A` has exactly one zero `u ≡ t mod π ^ (k + 1)`, and
`A t ≡ 0 mod π ^ e` forces `u ≡ t mod π ^ (e - k)`. For a polynomial in one
variable this is the classical form `|f(t)| < |f'(t)|²` of Hensel's lemma. Unlike the case
`k = 0`, the quantitative form needs `π` to be a non-zero-divisor: over `ℤ/8ℤ`, with `π = 2`,
the map `x ↦ 2x` has `J = 2`, `M = 1`, `k = 1` and the two zeros `0` and `4` congruent modulo
`4`.

## Main results

* `TauCeti.IsAdicComplete.existsUnique_eq_zero_of_isUnit_det`: Newton's method, the existence and
  uniqueness of the zero.
* `TauCeti.IsAdicComplete.existsUnique_eq_zero_of_mul_eq_pow_smul`: the quantitative form, with a
  Jacobian invertible up to `π ^ k`.
* `TauCeti.pow_dvd_sub_of_eq_zero_of_mul_eq_pow_smul`: the error bound `u ≡ t mod π ^ (e - k)`.
* `TauCeti.IsAdicComplete.existsUnique_eval_eq_zero_of_dvd_pow` and
  `TauCeti.pow_dvd_sub_of_eval_eq_zero_of_dvd_pow`: Hensel's lemma for a polynomial `f` with
  `f(t) ≡ 0 mod π ^ (2k + 1)` and `f'(t) ∣ π ^ k`, and its error bound.

## References

* [R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces*], proof of
  Proposition 1.7.1.
* [O. Gabber and L. Ramero, *Almost ring theory*], Lemma 5.4.8.
-/

public section

namespace TauCeti

open Matrix

variable {R : Type*} {ι : Type*} [CommRing R] (π : R) [Fintype ι] [DecidableEq ι]

section Complete

variable [IsAdicComplete (Ideal.span {π}) R]

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
      exact dvd_mulVec_apply hk _ i
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
    have h3 := dvd_mulVec_apply (v := L - u k) (fun j ↦ by simpa using hL' k j) M i
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
      have h2 := dvd_mulVec_apply h1 M⁻¹
      rwa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hM, Matrix.one_mulVec] at h2
  funext i
  refine sub_eq_zero.1 (IsHausdorff.haus (I := Ideal.span {π}) inferInstance _ fun k ↦ ?_)
  rw [SModEq.zero, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  obtain ⟨c, hc⟩ := hdiff k i
  exact ⟨c, Submodule.mem_top, by rw [smul_eq_mul, hc]⟩

end Complete

section Quantitative

variable {π}

/-- The step behind the quantitative Newton method: let `J` linearise `A` on the class
`t + π ^ (k + 1) R^ι`, gaining `k + 1` powers of `π`, and let `M * J = π ^ k • 1`. If two points of
the class agree modulo `π ^ n`, `n ≥ k + 1`, and their values agree modulo `π ^ (n + k + 1)`, then
the points agree modulo `π ^ (n + 1)`. -/
private theorem pow_succ_dvd_sub_of_pow_dvd (hπ : IsLeftRegular π) {A : (ι → R) → (ι → R)}
    {J M : Matrix ι ι R} {k : ℕ} (hMJ : M * J = π ^ k • (1 : Matrix ι ι R)) {t : ι → R}
    (hA : ∀ x x' : ι → R, (∀ i, π ^ (k + 1) ∣ x i - t i) → (∀ i, π ^ (k + 1) ∣ x' i - t i) →
      ∀ n : ℕ, k + 1 ≤ n → (∀ i, π ^ n ∣ x' i - x i) →
        ∀ i, π ^ (n + k + 1) ∣ A x' i - A x i - (J *ᵥ (x' - x)) i)
    {x x' : ι → R} (hx : ∀ i, π ^ (k + 1) ∣ x i - t i) (hx' : ∀ i, π ^ (k + 1) ∣ x' i - t i)
    {n : ℕ} (hn : k + 1 ≤ n) (hxx' : ∀ i, π ^ n ∣ x' i - x i)
    (hAxx' : ∀ i, π ^ (n + k + 1) ∣ A x' i - A x i) (i : ι) : π ^ (n + 1) ∣ x' i - x i := by
  -- `π ^ (n + k + 1)` divides `J (x' - x)`, hence `M J (x' - x) = π ^ k (x' - x)`.
  have hJ (j : ι) : π ^ (n + k + 1) ∣ (J *ᵥ (x' - x)) j := by
    simpa using dvd_sub (hAxx' j) (hA x x' hx hx' n hn hxx' j)
  have hMJv := dvd_mulVec_apply hJ M i
  simp only [Matrix.mulVec_mulVec, hMJ, Matrix.smul_mulVec, Matrix.one_mulVec, Pi.smul_apply,
    smul_eq_mul] at hMJv
  exact (hπ.pow k).dvd_cancel_left.mp (by rwa [← pow_add, show k + (n + 1) = n + k + 1 by omega])

/-- **Error bound for the quantitative Newton method.** Let `π` be a non-zero-divisor, let `J`
linearise `A` on the class `t + π ^ (k + 1) R^ι`, gaining `k + 1` powers of `π`, and let
`M * J = π ^ k • 1`. If `A t ≡ 0 mod π ^ e`, then every zero `u` of `A` in the class satisfies
`u ≡ t mod π ^ (e - k)`. This is only new information when `e ≥ 2k + 2`. No completeness is
needed. -/
theorem pow_dvd_sub_of_eq_zero_of_mul_eq_pow_smul (hπ : IsLeftRegular π)
    (A : (ι → R) → (ι → R)) {J M : Matrix ι ι R} {k : ℕ}
    (hMJ : M * J = π ^ k • (1 : Matrix ι ι R)) (t : ι → R)
    (hA : ∀ x x' : ι → R, (∀ i, π ^ (k + 1) ∣ x i - t i) → (∀ i, π ^ (k + 1) ∣ x' i - t i) →
      ∀ n : ℕ, k + 1 ≤ n → (∀ i, π ^ n ∣ x' i - x i) →
        ∀ i, π ^ (n + k + 1) ∣ A x' i - A x i - (J *ᵥ (x' - x)) i)
    {e : ℕ} (ht : ∀ i, π ^ e ∣ A t i) {u : ι → R}
    (hu : ∀ i, π ^ (k + 1) ∣ u i - t i) (hAu : A u = 0) (i : ι) : π ^ (e - k) ∣ u i - t i := by
  suffices ∀ n, k + 1 ≤ n → n ≤ e - k → ∀ i, π ^ n ∣ u i - t i by
    rcases le_total (e - k) (k + 1) with he | he
    · exact (pow_dvd_pow π he).trans (hu i)
    · exact this _ he le_rfl i
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact fun _ ↦ hu
  | succ n hn ih =>
    refine fun hne ↦ pow_succ_dvd_sub_of_pow_dvd hπ hMJ hA (by simp) hu hn (ih (by omega))
      fun j ↦ ?_
    simpa [hAu] using (pow_dvd_pow π (by omega : n + k + 1 ≤ e)).trans (ht j)

/-- Over a `π`-adically Hausdorff ring, `A` has at most one zero in the class
`t + π ^ (k + 1) R^ι`, under the hypotheses of the quantitative Newton method. -/
private theorem eq_of_eq_zero_of_mul_eq_pow_smul [IsHausdorff (Ideal.span {π}) R]
    (hπ : IsLeftRegular π) {A : (ι → R) → (ι → R)} {J M : Matrix ι ι R} {k : ℕ}
    (hMJ : M * J = π ^ k • (1 : Matrix ι ι R)) {t : ι → R}
    (hA : ∀ x x' : ι → R, (∀ i, π ^ (k + 1) ∣ x i - t i) → (∀ i, π ^ (k + 1) ∣ x' i - t i) →
      ∀ n : ℕ, k + 1 ≤ n → (∀ i, π ^ n ∣ x' i - x i) →
        ∀ i, π ^ (n + k + 1) ∣ A x' i - A x i - (J *ᵥ (x' - x)) i)
    {u u' : ι → R} (hu : ∀ i, π ^ (k + 1) ∣ u i - t i) (hu' : ∀ i, π ^ (k + 1) ∣ u' i - t i)
    (hAu : A u = 0) (hAu' : A u' = 0) : u' = u := by
  have key (n : ℕ) (hn : k + 1 ≤ n) (i : ι) : π ^ n ∣ u' i - u i := by
    induction n, hn using Nat.le_induction generalizing i with
    | base => simpa using dvd_sub (hu' i) (hu i)
    | succ n hn ih =>
      exact pow_succ_dvd_sub_of_pow_dvd hπ hMJ hA hu hu' hn ih (by simp [hAu, hAu']) i
  refine sub_eq_zero.mp (eq_zero_of_forall_pow_dvd π fun n i ↦ ?_)
  exact (pow_dvd_pow π (le_max_left n (k + 1))).trans (key _ (le_max_right n (k + 1)) i)

/-- **Newton's method with a Jacobian invertible up to `π ^ k`.** Let `R` be `π`-adically complete
with `π` a non-zero-divisor, and let `J` linearise `A` on the class `t + π ^ (k + 1) R^ι`, gaining
`k + 1` powers of `π`: `A x' ≡ A x + J (x' - x) mod π ^ (n + k + 1)` whenever `x, x'` lie in the
class and `x' ≡ x mod π ^ n` with `n ≥ k + 1`. If `M * J = π ^ k • 1` for some matrix `M` and
`A t ≡ 0 mod π ^ (2k + 1)`, then `A` has exactly one zero congruent to `t` modulo `π ^ (k + 1)`. -/
theorem IsAdicComplete.existsUnique_eq_zero_of_mul_eq_pow_smul
    [IsAdicComplete (Ideal.span {π}) R] (hπ : IsLeftRegular π) (A : (ι → R) → (ι → R))
    {J M : Matrix ι ι R} {k : ℕ} (hMJ : M * J = π ^ k • (1 : Matrix ι ι R)) (t : ι → R)
    (ht : ∀ i, π ^ (2 * k + 1) ∣ A t i)
    (hA : ∀ x x' : ι → R, (∀ i, π ^ (k + 1) ∣ x i - t i) → (∀ i, π ^ (k + 1) ∣ x' i - t i) →
      ∀ n : ℕ, k + 1 ≤ n → (∀ i, π ^ n ∣ x' i - x i) →
        ∀ i, π ^ (n + k + 1) ∣ A x' i - A x i - (J *ᵥ (x' - x)) i) :
    ∃! u : ι → R, (∀ i, π ^ (k + 1) ∣ u i - t i) ∧ A u = 0 := by
  -- Rescale: on `v`, the point `x v = t + π ^ (k + 1) v` of the class, `M A (x v)` is divisible by
  -- `π ^ (2k + 1)`, and the quotient `G v` is linearised by the identity matrix.
  set x : (ι → R) → (ι → R) := fun v ↦ t + π ^ (k + 1) • v with hx
  have hxt (v : ι → R) (i : ι) : π ^ (k + 1) ∣ x v i - t i := by simp [hx]
  have hxsub (v v' : ι → R) : x v' - x v = π ^ (k + 1) • (v' - v) := by
    simp only [hx, smul_sub]
    abel
  have hxsub' (v v' : ι → R) (j : ι) : x v' j - x v j = π ^ (k + 1) * (v' j - v j) := by
    simpa using congrFun (hxsub v v') j
  have hkey (v v' : ι → R) :
      M *ᵥ (A (x v') - A (x v) - J *ᵥ (x v' - x v)) =
        M *ᵥ A (x v') - M *ᵥ A (x v) - π ^ (2 * k + 1) • (v' - v) := by
    simp only [Matrix.mulVec_sub, Matrix.mulVec_mulVec, hMJ, Matrix.smul_mulVec, Matrix.one_mulVec,
      hxsub, smul_smul, ← pow_add]
    rw [show k + (k + 1) = 2 * k + 1 by omega]
  have hx0 : x 0 = t := by simp [hx]
  have hdiv (v : ι → R) (i : ι) : π ^ (2 * k + 1) ∣ (M *ᵥ A (x v)) i := by
    have h1 := dvd_mulVec_apply (v := A (x v) - A (x 0) - J *ᵥ (x v - x 0))
      (hA (x 0) (x v) (hxt 0) (hxt v) (k + 1) le_rfl fun j ↦ by simp [hxsub']) M i
    rw [hkey, hx0] at h1
    have h2 := (pow_dvd_pow π (by omega : 2 * k + 1 ≤ k + 1 + k + 1)).trans h1
    have h3 := dvd_mulVec_apply ht M i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_zero] at h2
    convert dvd_add (dvd_add h2 h3) (dvd_mul_right (π ^ (2 * k + 1)) (v i)) using 1
    ring
  choose G hG using hdiv
  have hGlin (v v' : ι → R) (n : ℕ) (hvv' : ∀ i, π ^ n ∣ v' i - v i) (i : ι) :
      π ^ (n + 1) ∣ G v' i - G v i - (v' i - v i) := by
    have h1 := dvd_mulVec_apply (v := A (x v') - A (x v) - J *ᵥ (x v' - x v))
      (hA (x v) (x v') (hxt v) (hxt v') (n + k + 1) (by omega) fun j ↦ by
        rw [hxsub', add_assoc, pow_add, mul_comm]
        exact mul_dvd_mul_left _ (hvv' j)) M i
    simp only [hkey, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hG, ← mul_sub] at h1
    rw [show n + k + 1 + k + 1 = 2 * k + 1 + (n + 1) by omega, pow_add] at h1
    exact (hπ.pow _).dvd_cancel_left.mp h1
  -- Newton's method with a unit Jacobian produces a zero of `G`, hence one of `M A`.
  obtain ⟨w, ⟨-, hw⟩, -⟩ := IsAdicComplete.existsUnique_eq_zero_of_isUnit_det π G
    (M := 1) (by simp) (-G 0) (fun i ↦ by simpa using hGlin 0 (-G 0) 0 (by simp) i)
    fun v v' _ _ n _ hvv' i ↦ by simpa using hGlin v v' n hvv' i
  have hMA : M *ᵥ A (x w) = 0 := funext fun i ↦ by rw [hG, hw, Pi.zero_apply, mul_zero]
  -- `M * J = π ^ k • 1` makes `M` injective, so `M A (x w) = 0` forces `A (x w) = 0`.
  have hAw : A (x w) = 0 := Matrix.mulVec_injective_of_mul_eq_smul_one (hπ.pow k) hMJ
    (by rw [hMA, Matrix.mulVec_zero])
  exact ⟨x w, ⟨hxt w, hAw⟩, fun u ⟨hu, hAu⟩ ↦
    eq_of_eq_zero_of_mul_eq_pow_smul hπ hMJ hA (hxt w) hu hAw hAu⟩

end Quantitative

section Polynomial

open Polynomial

variable {π} {f : R[X]} {k : ℕ} {t : R}

/-- Taylor's estimate for a polynomial, restated for its evaluation map on `Unit`-indexed coordinate
families and the `1 × 1` Jacobian `f'(t)`: the linearisation hypothesis of the quantitative Newton
method. -/
private theorem pow_dvd_evalUnit_sub (x x' : Unit → R) (hx : ∀ i, π ^ (k + 1) ∣ x i - t)
    (n : ℕ) (hn : k + 1 ≤ n) (hxx' : ∀ i, π ^ n ∣ x' i - x i) (i : Unit) :
    π ^ (n + k + 1) ∣ f.eval (x' i) - f.eval (x i) -
      ((Matrix.of fun _ _ ↦ f.derivative.eval t : Matrix Unit Unit R) *ᵥ (x' - x)) i := by
  have h := f.mul_dvd_eval_sub_eval_sub_mul (hx i) (pow_dvd_pow π hn) (hxx' i)
  rw [← pow_add, show k + 1 + n = n + k + 1 by omega] at h
  simpa [Matrix.mulVec, dotProduct] using h

/-- The scalar matrix of a `Unit`-indexed Jacobian `f'(t)` with a cofactor `m`. -/
private theorem of_mul_of_eq_pow_smul {m : R} (hm : π ^ k = f.derivative.eval t * m) :
    (Matrix.of fun _ _ ↦ m : Matrix Unit Unit R) * Matrix.of (fun _ _ ↦ f.derivative.eval t) =
      π ^ k • (1 : Matrix Unit Unit R) := by
  ext
  simp [Matrix.mul_apply, hm, mul_comm]

/-- **Error bound in Hensel's lemma.** Let `π` be a non-zero-divisor and `f'(t) ∣ π ^ k`. If
`f(t) ≡ 0 mod π ^ e`, then every root `u` of `f` with `u ≡ t mod π ^ (k + 1)` satisfies
`u ≡ t mod π ^ (e - k)`. -/
theorem pow_dvd_sub_of_eval_eq_zero_of_dvd_pow (hπ : IsLeftRegular π)
    (hd : f.derivative.eval t ∣ π ^ k) {e : ℕ} (ht : π ^ e ∣ f.eval t)
    {u : R} (hu : π ^ (k + 1) ∣ u - t) (hfu : f.eval u = 0) : π ^ (e - k) ∣ u - t := by
  obtain ⟨m, hm⟩ := hd
  exact pow_dvd_sub_of_eq_zero_of_mul_eq_pow_smul hπ (fun x i ↦ f.eval (x i))
    (of_mul_of_eq_pow_smul hm) (fun _ ↦ t)
    (fun x x' hx _ n hn hxx' ↦ pow_dvd_evalUnit_sub x x' hx n hn hxx') (fun _ ↦ ht)
    (u := fun _ ↦ u) (fun _ ↦ hu) (funext fun _ ↦ hfu) ()

/-- **Hensel's lemma with a derivative dividing `π ^ k`.** Let `R` be `π`-adically complete with
`π` a non-zero-divisor, and let `f` be a polynomial with `f'(t) ∣ π ^ k` and
`f(t) ≡ 0 mod π ^ (2k + 1)`. Then `f` has exactly one root congruent to `t` modulo `π ^ (k + 1)`.
-/
theorem IsAdicComplete.existsUnique_eval_eq_zero_of_dvd_pow [IsAdicComplete (Ideal.span {π}) R]
    (hπ : IsLeftRegular π) (hd : f.derivative.eval t ∣ π ^ k)
    (ht : π ^ (2 * k + 1) ∣ f.eval t) : ∃! u : R, π ^ (k + 1) ∣ u - t ∧ f.eval u = 0 := by
  obtain ⟨m, hm⟩ := hd
  obtain ⟨u, ⟨hu, hfu⟩, huniq⟩ := IsAdicComplete.existsUnique_eq_zero_of_mul_eq_pow_smul hπ
    (fun x i ↦ f.eval (x i)) (of_mul_of_eq_pow_smul hm) (fun _ ↦ t) (fun _ ↦ ht)
    fun x x' hx _ n hn hxx' ↦ pow_dvd_evalUnit_sub x x' hx n hn hxx'
  exact ⟨u (), ⟨hu (), congrFun hfu ()⟩, fun y ⟨hy, hfy⟩ ↦
    congrFun (huniq (fun _ ↦ y) ⟨fun _ ↦ hy, funext fun _ ↦ hfy⟩) ()⟩

end Polynomial

end TauCeti
