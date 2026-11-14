/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
public import TauCeti.RingTheory.MvPolynomial.Finrank
public import TauCeti.RingTheory.MvPolynomial.Homogeneous

/-!
# Harmonic polynomials and the Fischer decomposition

For finitely many variables `X₁, …, Xₙ`, the Laplacian of a polynomial is `Δ p = ∑ᵢ ∂²p/∂Xᵢ²`
and `r² = ∑ᵢ Xᵢ²` is the polynomial giving the squared Euclidean norm. A polynomial is harmonic
when its Laplacian vanishes. This file develops the finite algebra of harmonic homogeneous
polynomials that underlies spherical harmonics: over `ℝ`, a harmonic homogeneous polynomial of
degree `d` in `n` variables restricts to an eigenfunction of the Laplacian of the unit sphere
`S^(n-1)`, with eigenvalue `d(d + n - 2)`. That restriction is not treated here.

Writing `P_d` for the homogeneous polynomials of degree `d` and `H_d ⊆ P_d` for the harmonic
ones, the Laplacian maps `P_d` to `P_(d-2)`, and for `q ∈ P_e` the product rule and Euler's
identity give

`Δ (r² q) = r² Δ q + (2n + 4e) q`,

and hence, for `h ∈ H_l`, `Δ (r^(2(k+1)) h) = 2(k+1)(2l + n + 2k) r^(2k) h`.
With at least one variable and coefficients in which multiplication by a positive integer is
injective, the operator `q ↦ Δ (r² q)` has trivial kernel (`Δ (r² q) = 0 → q = 0`), so a harmonic
polynomial divisible by `r²` is zero. Over a field of characteristic zero it is injective, hence
bijective on `P_e`, which yields the
**Fischer decomposition**

`P_(e+2) = H_(e+2) ⊕ r² P_e`,

and the dimension formula `dim H_(e+2) = dim P_(e+2) - dim P_e`. Since every polynomial of degree
at most one is harmonic, `H_d = P_d` for `d ≤ 1`. Iterating the decomposition writes every
homogeneous polynomial as a sum of harmonic ones multiplied by powers of `r²`.

The Laplacian is defined as a linear map on polynomials rather than through the analytic
notation class `Laplacian`, so that this file stays purely algebraic.

## Main definitions

* `MvPolynomial.laplacian`: the Laplacian `∑ᵢ ∂²/∂Xᵢ²` on polynomials in finitely many variables.
* `MvPolynomial.normSq`: the polynomial `r² = ∑ᵢ Xᵢ²`.
* `MvPolynomial.harmonicSubmodule σ R d`: the harmonic homogeneous polynomials of degree `d`.
* `MvPolynomial.fischerEquiv σ K d`: the linear equivalence
  `(Π k : Fin (d / 2 + 1), H_(d - 2k)) ≃ₗ[K] P_d` given by the iterated Fischer decomposition.

## Main results

* `MvPolynomial.laplacian_mul`: the product rule `Δ (p q) = Δ p q + 2 ∑ᵢ ∂ᵢp ∂ᵢq + p Δ q`.
* `MvPolynomial.map_laplacian`, `MvPolynomial.map_normSq`, and
  `MvPolynomial.map_mem_harmonicSubmodule`: ring homomorphisms commute with `Δ` and preserve `r²`
  and `H_d`.
* `MvPolynomial.IsHomogeneous.laplacian`: the Laplacian lowers the degree by two.
* `MvPolynomial.laplacian_normSq_mul`: `Δ (r² q) = r² Δ q + (2n + 4e) q` for `q ∈ P_e`.
* `MvPolynomial.laplacian_normSq_pow_mul`: `Δ (r^(2(k+1)) h) = 2(k+1)(2l + n + 2k) r^(2k) h`
  for `h ∈ H_l`.
* `MvPolynomial.eq_zero_of_laplacian_normSq_mul_eq_zero`,
  `MvPolynomial.eq_zero_of_normSq_mul_eq_zero`, and `MvPolynomial.exists_laplacian_normSq_mul_eq`:
  with at least one variable, `Δ (r² q) = 0 → q = 0` and `r² q = 0 → q = 0` (under
  `HasUniqueDiv R`), and `q ↦ Δ (r² q)` is bijective on `P_e` over a field of characteristic zero.
* `MvPolynomial.harmonicSubmodule_sup_map_mulLeft_normSq` and
  `MvPolynomial.disjoint_ker_laplacian_range_mulLeft_normSq`: the Fischer decomposition
  `P_(e+2) = H_(e+2) ⊕ r² P_e`.
* `MvPolynomial.homogeneousSubmodule_eq_iSup_map_mulLeft_normSq_pow`,
  `MvPolynomial.sum_normSq_pow_mul_eq_zero_iff`, `MvPolynomial.eq_of_sum_normSq_pow_mul_eq`, and
  `MvPolynomial.existsUnique_sum_normSq_pow_mul_eq`: existence and uniqueness of the iterated
  Fischer decomposition `p = ∑_{k ≤ d/2} r^(2k) h_k` with `h_k ∈ H_(d-2k)`.
* `MvPolynomial.finrank_harmonicSubmodule_add_finrank`,
  `MvPolynomial.finrank_harmonicSubmodule_add_two`,
  `MvPolynomial.finrank_harmonicSubmodule_of_le_one`,
  `MvPolynomial.finrank_harmonicSubmodule`, and
  `MvPolynomial.finrank_harmonicSubmodule_eq_choose_sub`: the dimension of `H_d`, in terms of
  multichoose numbers and binomial coefficients `C(m + d, d) - C(m + d - 2, d - 2)`.

## References

* S. Axler, P. Bourdon and W. Ramey, *Harmonic Function Theory*, 2nd ed., Springer GTM 137
  (2001), Chapter 5 (harmonic polynomials and the decomposition of homogeneous polynomials).
* E. M. Stein and G. Weiss, *Introduction to Fourier Analysis on Euclidean Spaces*, Princeton
  University Press (1971), Chapter IV, Section 2 (spherical harmonics).
-/

public section

namespace MvPolynomial

variable {σ R : Type*} [CommSemiring R]

section Laplacian

variable [Fintype σ]

/-- The **Laplacian** `Δ p = ∑ᵢ ∂²p/∂Xᵢ²` of a polynomial in finitely many variables. -/
noncomputable def laplacian : MvPolynomial σ R →ₗ[R] MvPolynomial σ R :=
  ∑ i, (pderiv i).toLinearMap ∘ₗ (pderiv i).toLinearMap

theorem laplacian_apply (p : MvPolynomial σ R) :
    laplacian p = ∑ i, pderiv i (pderiv i p) := by
  simp [laplacian]

@[simp]
theorem laplacian_C (a : R) : laplacian (C a : MvPolynomial σ R) = 0 := by
  simp [laplacian_apply]

/-- The **product rule** for the Laplacian: `Δ (p q) = Δ p q + 2 ∑ᵢ ∂ᵢp ∂ᵢq + p Δ q`. -/
theorem laplacian_mul (p q : MvPolynomial σ R) :
    laplacian (p * q) =
      laplacian p * q + 2 * ∑ i, pderiv i p * pderiv i q + p * laplacian q := by
  simp only [laplacian_apply, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [pderiv_mul, map_add]
  ring

/-- The Laplacian lowers the degree of a homogeneous polynomial by two. -/
protected theorem IsHomogeneous.laplacian {p : MvPolynomial σ R} {n : ℕ}
    (hp : p.IsHomogeneous n) : (laplacian p).IsHomogeneous (n - 2) := by
  rw [laplacian_apply]
  exact IsHomogeneous.sum _ _ _ fun i _ ↦ by simpa [Nat.sub_sub] using hp.pderiv.pderiv

/-- A homogeneous polynomial of degree at most one is harmonic. -/
theorem IsHomogeneous.laplacian_eq_zero_of_le_one {p : MvPolynomial σ R} {n : ℕ}
    (hp : p.IsHomogeneous n) (hn : n ≤ 1) : laplacian p = 0 := by
  rw [laplacian_apply]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  have h : (pderiv i p).IsHomogeneous 0 := by simpa [Nat.sub_eq_zero_of_le hn] using hp.pderiv
  rw [← totalDegree_zero_iff_isHomogeneous, totalDegree_eq_zero_iff_eq_C] at h
  rw [h, pderiv_C]

@[simp]
theorem laplacian_X (j : σ) : laplacian (X j : MvPolynomial σ R) = 0 :=
  (isHomogeneous_X R j).laplacian_eq_zero_of_le_one le_rfl

/-- Mapping coefficients along a ring homomorphism commutes with the polynomial Laplacian. -/
theorem map_laplacian {S : Type*} [CommSemiring S] (f : R →+* S) (p : MvPolynomial σ R) :
    map f (laplacian p) = laplacian (map f p) := by
  simp [laplacian_apply, pderiv_map]

end Laplacian

section NormSq

variable (σ R)

/-- The polynomial `r² = ∑ᵢ Xᵢ²` giving the squared Euclidean norm. -/
noncomputable def normSq [Fintype σ] : MvPolynomial σ R :=
  ∑ i, X i ^ 2

variable [Fintype σ]

theorem normSq_def : normSq σ R = ∑ i, X i ^ 2 := by
  rw [normSq]

@[simp]
theorem eval_normSq (x : σ → R) : eval x (normSq σ R) = ∑ i, x i ^ 2 := by
  simp [normSq_def]

variable {σ R} in
@[simp]
theorem map_normSq {S : Type*} [CommSemiring S] (f : R →+* S) :
    map f (normSq σ R) = normSq σ S := by
  simp [normSq_def]

theorem isHomogeneous_normSq : (normSq σ R).IsHomogeneous 2 :=
  IsHomogeneous.sum _ _ _ fun i _ ↦ (isHomogeneous_X R i).pow 2

/-- With no variables, `r² = 0`. -/
@[simp]
theorem normSq_eq_zero_of_isEmpty [IsEmpty σ] : normSq σ R = 0 := by
  simp [normSq_def]

/-- `normSq` is a nonzero polynomial as soon as there is a variable. -/
theorem normSq_ne_zero [Nontrivial R] [Nonempty σ] : normSq σ R ≠ 0 := by
  classical
  obtain ⟨i⟩ := ‹Nonempty σ›
  intro h
  have := congrArg (eval (Pi.single i 1)) h
  simp only [normSq, map_sum, map_pow, eval_X, map_zero] at this
  rw [Finset.sum_eq_single i (fun j _ hj ↦ by simp [hj]) (by simp)] at this
  simp at this

variable {σ}

@[simp]
theorem pderiv_normSq (i : σ) : pderiv i (normSq σ R) = 2 * X i := by
  classical
  simp [normSq, pderiv_X, Pi.single_apply]

@[simp]
theorem laplacian_normSq : laplacian (normSq σ R) = 2 * (Fintype.card σ : MvPolynomial σ R) := by
  have h2 (i : σ) : pderiv i (2 : MvPolynomial σ R) = 0 := by
    simpa using (pderiv i).map_natCast 2
  simp [laplacian_apply, h2, mul_comm]

variable {R}

/-- **The Laplacian of `r² q`**: for `q` homogeneous of degree `e` in `n` variables,
`Δ (r² q) = r² Δ q + (2n + 4e) q`. -/
theorem laplacian_normSq_mul {q : MvPolynomial σ R} {e : ℕ} (hq : q.IsHomogeneous e) :
    laplacian (normSq σ R * q) =
      normSq σ R * laplacian q + (2 * Fintype.card σ + 4 * e) • q := by
  have euler := hq.sum_X_mul_pderiv
  rw [laplacian_mul, laplacian_normSq]
  simp only [pderiv_normSq, mul_assoc, ← Finset.mul_sum, euler]
  simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  ring

/-- **The Laplacian of `r^(2(k+1)) h`**: for `h` harmonic and homogeneous of degree `l` in `n`
variables, `Δ (r^(2(k+1)) h) = 2(k+1)(2l + n + 2k) r^(2k) h`. -/
theorem laplacian_normSq_pow_mul {h : MvPolynomial σ R} {l : ℕ} (hh : h.IsHomogeneous l)
    (hΔ : laplacian h = 0) (k : ℕ) :
    laplacian (normSq σ R ^ (k + 1) * h) =
      (2 * (k + 1) * (2 * l + Fintype.card σ + 2 * k)) • (normSq σ R ^ k * h) := by
  induction k with
  | zero =>
    rw [zero_add, pow_one, laplacian_normSq_mul hh, hΔ]
    simp only [pow_zero, one_mul, nsmul_eq_mul]
    push_cast
    ring
  | succ k ih =>
    have hdeg : (normSq σ R ^ (k + 1) * h).IsHomogeneous (2 * (k + 1) + l) :=
      ((isHomogeneous_normSq σ R).pow (k + 1)).mul hh
    rw [pow_succ', mul_assoc, laplacian_normSq_mul hdeg, ih]
    simp only [nsmul_eq_mul]
    push_cast
    ring

end NormSq

section Harmonic

variable (σ R) [Fintype σ]

/-- The **harmonic homogeneous polynomials** of degree `d`: the homogeneous polynomials of degree
`d` whose Laplacian vanishes. -/
noncomputable def harmonicSubmodule (d : ℕ) : Submodule R (MvPolynomial σ R) :=
  homogeneousSubmodule σ R d ⊓ LinearMap.ker laplacian

variable {σ R}

@[simp]
theorem mem_harmonicSubmodule_iff {d : ℕ} {p : MvPolynomial σ R} :
    p ∈ harmonicSubmodule σ R d ↔ p.IsHomogeneous d ∧ laplacian p = 0 :=
  Iff.rfl

theorem harmonicSubmodule_le_homogeneousSubmodule (d : ℕ) :
    harmonicSubmodule σ R d ≤ homogeneousSubmodule σ R d :=
  inf_le_left

/-- Mapping coefficients along a ring homomorphism preserves harmonic homogeneous polynomials. -/
theorem map_mem_harmonicSubmodule {S : Type*} [CommSemiring S] (f : R →+* S) {d : ℕ}
    {p : MvPolynomial σ R} (hp : p ∈ harmonicSubmodule σ R d) :
    map f p ∈ harmonicSubmodule σ S d := by
  rw [mem_harmonicSubmodule_iff] at hp ⊢
  refine ⟨fun m hm ↦ hp.1 fun h0 ↦ hm (by rw [coeff_map, h0, map_zero]), ?_⟩
  rw [← map_laplacian, hp.2, map_zero]

/-- With no variables, every harmonic polynomial of positive degree is zero. -/
@[simp]
theorem harmonicSubmodule_succ_eq_bot_of_isEmpty [IsEmpty σ] (n : ℕ) :
    harmonicSubmodule σ R (n + 1) = ⊥ := by
  simp [harmonicSubmodule]

/-- In degree at most one every homogeneous polynomial is harmonic. -/
theorem harmonicSubmodule_eq_of_le_one {d : ℕ} (hd : d ≤ 1) :
    harmonicSubmodule σ R d = homogeneousSubmodule σ R d :=
  inf_eq_left.2 fun _ hp ↦ IsHomogeneous.laplacian_eq_zero_of_le_one hp hd

/-- **The dimension of the harmonic polynomials** of degree `d ≤ 1` in `n` variables is
`n.multichoose d`, the dimension of all homogeneous polynomials of degree `d`. -/
theorem finrank_harmonicSubmodule_of_le_one [StrongRankCondition R] {d : ℕ} (hd : d ≤ 1) :
    Module.finrank R (harmonicSubmodule σ R d) = (Fintype.card σ).multichoose d := by
  rw [harmonicSubmodule_eq_of_le_one hd, TauCeti.finrank_homogeneousSubmodule_eq_multichoose]

end Harmonic

section Injective

variable [Fintype σ] [HasUniqueDiv R]

/-- If `Δ (r² q) + m q = 0` for `q` homogeneous and `m` a natural number, then `q = 0`: the
operator `q ↦ Δ (r² q)` has no eigenvalue `-m`. -/
private theorem eq_zero_of_laplacian_normSq_mul_add_nsmul_eq_zero [Nonempty σ] {e : ℕ} :
    ∀ {q : MvPolynomial σ R} {m : ℕ}, q.IsHomogeneous e →
      laplacian (normSq σ R * q) + m • q = 0 → q = 0 := by
  induction e using Nat.strong_induction_on with
  | _ e ih =>
  intro q m hq h
  rw [laplacian_normSq_mul hq, add_assoc, ← add_smul] at h
  set N := 2 * Fintype.card σ + 4 * e + m
  have hN : N ≠ 0 := by
    have : 0 < Fintype.card σ := Fintype.card_pos
    omega
  -- Once `Δ q = 0`, the equation reads `N q = 0`.
  suffices hΔ : laplacian q = 0 by
    rw [hΔ, mul_zero, zero_add] at h
    ext d
    exact nsmul_right_injective hN <| by
      simpa [-nsmul_eq_mul] using congrArg (fun p ↦ p.coeff d) h
  rcases lt_or_ge e 2 with he | he
  · exact hq.laplacian_eq_zero_of_le_one (by omega)
  -- Applying `Δ` gives `Δ (r² Δ q) + N Δ q = 0`, an equation of the same shape in degree `e - 2`.
  exact @ih (e - 2) (by omega) _ N hq.laplacian <| by
    simpa only [map_add, map_nsmul, map_zero] using congrArg laplacian h

/-- **Trivial kernel of `q ↦ Δ (r² q)`**: with at least one variable and coefficients in which
multiplication by a positive integer is injective (for instance a field of characteristic zero),
if `Δ (r² q) = 0`, then `q = 0`. When `R` is a ring this gives injectivity. -/
theorem eq_zero_of_laplacian_normSq_mul_eq_zero [Nonempty σ] {q : MvPolynomial σ R}
    (h : laplacian (normSq σ R * q) = 0) : q = 0 := by
  -- The operator preserves the degree, so it vanishes on each homogeneous component of `q`.
  have ht (i : ℕ) : (laplacian (normSq σ R * homogeneousComponent i q)).IsHomogeneous i := by
    simpa [add_comm] using
      ((isHomogeneous_normSq σ R).mul (homogeneousComponent_isHomogeneous i q)).laplacian
  have hc (d : ℕ) : homogeneousComponent d q = 0 := by
    have hd : laplacian (normSq σ R * homogeneousComponent d q) = 0 := by
      have := congrArg (homogeneousComponent d) h
      conv_lhs at this => rw [← sum_homogeneousComponent q]
      simp only [Finset.mul_sum, map_sum] at this
      rw [Finset.sum_eq_single d (fun i _ hi ↦ by
          rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).2 (ht i))]
          simp [Ne.symm hi]) (fun hd ↦ by
          rw [homogeneousComponent_eq_zero d q (by simpa using hd)]; simp),
        homogeneousComponent_eq_self (ht d)] at this
      simpa using this
    exact eq_zero_of_laplacian_normSq_mul_add_nsmul_eq_zero (m := 0)
      (homogeneousComponent_isHomogeneous d q) (by simpa using hd)
  rw [← sum_homogeneousComponent q]
  exact Finset.sum_eq_zero fun d _ ↦ hc d

/-- With at least one variable and unique division by positive integers, `r² = ∑ᵢ Xᵢ²` is a
non-zero-divisor: if `r² q = 0`, then `q = 0`. -/
theorem eq_zero_of_normSq_mul_eq_zero [Nonempty σ] {q : MvPolynomial σ R}
    (h : normSq σ R * q = 0) : q = 0 :=
  eq_zero_of_laplacian_normSq_mul_eq_zero (by rw [h, map_zero])

/-- **The Fischer decomposition**, disjointness: a harmonic polynomial divisible by `r²` is
zero. -/
theorem disjoint_ker_laplacian_range_mulLeft_normSq :
    Disjoint (LinearMap.ker (laplacian : MvPolynomial σ R →ₗ[R] MvPolynomial σ R))
      (LinearMap.range (LinearMap.mulLeft R (normSq σ R))) := by
  rcases isEmpty_or_nonempty σ with hσ | hσ
  · simp
  rw [Submodule.disjoint_def]
  rintro _ hΔ ⟨q, rfl⟩
  rw [LinearMap.mulLeft_apply, eq_zero_of_laplacian_normSq_mul_eq_zero hΔ, mul_zero]

/-- **Linear independence of the iterated Fischer summands**: with at least one variable over a
commutative ring with `HasUniqueDiv`, if `h_k ∈ H_(d - 2k)` for `0 ≤ k ≤ d / 2` satisfy
`∑_{k ≤ d/2} r^(2k) h_k = 0`, then every `h_k` is zero. With no variables this fails: `r² = 0`, so
for `d = 2` the component `h₁ ∈ H_0` is unconstrained. -/
theorem sum_normSq_pow_mul_eq_zero_iff {R : Type*} [CommRing R] [HasUniqueDiv R] [Nonempty σ]
    {d : ℕ} {h : ℕ → MvPolynomial σ R}
    (hh : ∀ k ≤ d / 2, h k ∈ harmonicSubmodule σ R (d - 2 * k)) :
    ∑ k ∈ Finset.Iic (d / 2), normSq σ R ^ k * h k = 0 ↔ ∀ k ≤ d / 2, h k = 0 := by
  refine ⟨?_, fun hz ↦ Finset.sum_eq_zero fun k hk ↦ by rw [hz k (Finset.mem_Iic.1 hk), mul_zero]⟩
  induction d using Nat.strong_induction_on generalizing h with
  | _ d ih =>
  have hrange (m : ℕ) : Finset.Iic m = Finset.range (m + 1) := by
    ext k; simp
  rcases lt_or_ge d 2 with hd | hd
  · rw [Nat.div_eq_of_lt hd, hrange]
    intro h0 k hk
    have hk0 : k = 0 := by have := Nat.div_eq_of_lt hd; omega
    subst hk0
    simpa using h0
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 2 := ⟨d - 2, by omega⟩
  rw [Nat.add_div_right e two_pos, hrange, Finset.sum_range_succ']
  simp only [pow_zero, one_mul, pow_succ', mul_assoc, ← Finset.mul_sum, ← hrange]
  intro hsum
  have hh0 : h 0 = 0 := by
    have hmem : h 0 ∈ LinearMap.ker laplacian ⊓
        LinearMap.range (LinearMap.mulLeft R (normSq σ R)) :=
      ⟨(hh 0 (by omega)).2, -∑ x ∈ Finset.Iic (e / 2), normSq σ R ^ x * h (x + 1), by
        rw [LinearMap.mulLeft_apply, mul_neg, neg_eq_iff_add_eq_zero]
        exact hsum⟩
    rwa [disjoint_ker_laplacian_range_mulLeft_normSq.eq_bot, Submodule.mem_bot] at hmem
  rw [hh0, add_zero] at hsum
  have htail := (ih e (by omega) (h := fun j ↦ h (j + 1)) fun j hj ↦ by
    simpa [show e + 2 - 2 * (j + 1) = e - 2 * j by omega] using
      hh (j + 1) (by rw [Nat.add_div_right e two_pos]; omega))
    (eq_zero_of_normSq_mul_eq_zero hsum)
  intro k hk
  rcases k with _ | j
  · exact hh0
  · exact htail j (by omega)

/-- **Uniqueness of the iterated Fischer decomposition**: with at least one variable over a
commutative ring with `HasUniqueDiv`, the harmonic components `h_k ∈ H_(d - 2k)` (`0 ≤ k ≤ d / 2`)
in `p = ∑_{k ≤ d/2} r^(2k) h_k` are uniquely determined by `p`. -/
theorem eq_of_sum_normSq_pow_mul_eq {R : Type*} [CommRing R] [HasUniqueDiv R] [Nonempty σ]
    {d : ℕ} {h h' : ℕ → MvPolynomial σ R}
    (hh : ∀ k ≤ d / 2, h k ∈ harmonicSubmodule σ R (d - 2 * k))
    (hh' : ∀ k ≤ d / 2, h' k ∈ harmonicSubmodule σ R (d - 2 * k))
    (heq : ∑ k ∈ Finset.Iic (d / 2), normSq σ R ^ k * h k =
      ∑ k ∈ Finset.Iic (d / 2), normSq σ R ^ k * h' k) :
    ∀ k ≤ d / 2, h k = h' k := by
  have hzero : ∑ k ∈ Finset.Iic (d / 2), normSq σ R ^ k * (h k - h' k) = 0 := by
    simp_rw [mul_sub, Finset.sum_sub_distrib, heq, sub_self]
  intro k hk
  exact sub_eq_zero.1 <|
    (sum_normSq_pow_mul_eq_zero_iff fun j hj ↦ Submodule.sub_mem _ (hh j hj) (hh' j hj)).1
      hzero k hk

end Injective

section Fischer

variable {K : Type*} [Field K] [Fintype σ]

instance (d : ℕ) : FiniteDimensional K (harmonicSubmodule σ K d) :=
  Submodule.finiteDimensional_of_le (harmonicSubmodule_le_homogeneousSubmodule d)

variable [CharZero K] [Nonempty σ]

/-- **Surjectivity of `q ↦ Δ (r² q)`**: over a field of characteristic zero and with at least one
variable, every homogeneous polynomial `p` of degree `e` is `Δ (r² q)` for a homogeneous
polynomial `q` of degree `e`. -/
theorem exists_laplacian_normSq_mul_eq {p : MvPolynomial σ K} {e : ℕ} (hp : p.IsHomogeneous e) :
    ∃ q : MvPolynomial σ K, q.IsHomogeneous e ∧ laplacian (normSq σ K * q) = p := by
  -- The operator `q ↦ Δ (r² q)` on the finite-dimensional space of homogeneous polynomials of
  -- degree `e` is injective, hence surjective.
  let T : Module.End K (homogeneousSubmodule σ K e) :=
    (laplacian ∘ₗ LinearMap.mulLeft K (normSq σ K)).restrict fun q hq ↦ by
      simpa using ((isHomogeneous_normSq σ K).mul hq).laplacian
  have hT : Function.Injective T := by
    refine (injective_iff_map_eq_zero T).2 fun q hq ↦ Subtype.ext ?_
    exact eq_zero_of_laplacian_normSq_mul_eq_zero (congrArg Subtype.val hq)
  obtain ⟨q, hq⟩ := LinearMap.injective_iff_surjective.1 hT ⟨p, hp⟩
  exact ⟨q, q.2, congrArg Subtype.val hq⟩

omit [Nonempty σ] in
/-- **The Fischer decomposition**: every homogeneous polynomial of degree `e + 2` is the sum of a
harmonic one and `r²` times a homogeneous polynomial of degree `e`. The sum is direct by
`MvPolynomial.disjoint_ker_laplacian_range_mulLeft_normSq`. -/
theorem harmonicSubmodule_sup_map_mulLeft_normSq (e : ℕ) :
    harmonicSubmodule σ K (e + 2) ⊔
        (homogeneousSubmodule σ K e).map (LinearMap.mulLeft K (normSq σ K)) =
      homogeneousSubmodule σ K (e + 2) := by
  rcases isEmpty_or_nonempty σ with hσ | hσ
  · simp
  refine le_antisymm (sup_le (harmonicSubmodule_le_homogeneousSubmodule _) ?_) fun p hp ↦ ?_
  · rintro _ ⟨q, hq, rfl⟩
    simpa [add_comm] using (isHomogeneous_normSq σ K).mul hq
  obtain ⟨q, hq, hΔ⟩ := exists_laplacian_normSq_mul_eq (by simpa using hp.laplacian)
  have hrq : (normSq σ K * q).IsHomogeneous (e + 2) := by
    simpa [add_comm] using (isHomogeneous_normSq σ K).mul hq
  refine Submodule.mem_sup.2 ⟨p - normSq σ K * q, ⟨?_, ?_⟩, normSq σ K * q, ⟨q, hq, rfl⟩,
    sub_add_cancel p _⟩
  · exact Submodule.sub_mem _ hp hrq
  · simp [hΔ]

omit [Nonempty σ] in
/-- **The harmonic decomposition**: every homogeneous polynomial of degree `d` is a sum
`∑_{k ≤ d/2} r^(2k) h_k` with each `h_k` harmonic and homogeneous of degree `d - 2k`. -/
theorem homogeneousSubmodule_eq_iSup_map_mulLeft_normSq_pow (d : ℕ) :
    homogeneousSubmodule σ K d =
      ⨆ k ≤ d / 2,
        (harmonicSubmodule σ K (d - 2 * k)).map (LinearMap.mulLeft K (normSq σ K ^ k)) := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  rcases lt_or_ge d 2 with hd | hd
  · simp [Nat.div_eq_of_lt hd, harmonicSubmodule_eq_of_le_one (show d ≤ 1 by omega)]
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 2 := ⟨d - 2, by omega⟩
  rw [Nat.add_div_right e two_pos, Nat.iSup_le_succ', ← harmonicSubmodule_sup_map_mulLeft_normSq e,
    ih e (by omega)]
  simp_rw [Submodule.map_iSup, ← Submodule.map_comp, ← LinearMap.mulLeft_mul, ← pow_succ',
    show ∀ k, e + 2 - 2 * (k + 1) = e - 2 * k by omega]
  simp

private noncomputable def fischerLinearMap (σ K : Type*) [Field K] [Fintype σ] (d : ℕ) :
    (Π k : Fin (d / 2 + 1), harmonicSubmodule σ K (d - 2 * k)) →ₗ[K]
      homogeneousSubmodule σ K d where
  toFun h := ⟨∑ k : Fin (d / 2 + 1), normSq σ K ^ (k : ℕ) * (h k : MvPolynomial σ K), by
    refine IsHomogeneous.sum _ _ _ fun k _ ↦ ?_
    have hk : 2 * (k : ℕ) + (d - 2 * (k : ℕ)) = d := by omega
    simpa only [hk] using ((isHomogeneous_normSq σ K).pow (k : ℕ)).mul (h k).2.1⟩
  map_add' g h := Subtype.ext <| by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c h := Subtype.ext <| by simp [Finset.smul_sum]

/-- **The iterated Fischer decomposition as a linear equivalence**: over a field of characteristic
zero and with at least one variable, `(h_k)_{k ≤ d/2} ↦ ∑_{k ≤ d/2} r^(2k) h_k` is a linear
isomorphism from `∏_{k ≤ d/2} H_(d - 2k)` onto `P_d`. -/
noncomputable def fischerEquiv (σ K : Type*) [Field K] [CharZero K] [Fintype σ] [Nonempty σ]
    (d : ℕ) :
    (Π k : Fin (d / 2 + 1), harmonicSubmodule σ K (d - 2 * k)) ≃ₗ[K]
      homogeneousSubmodule σ K d :=
  LinearEquiv.ofBijective (fischerLinearMap σ K d) ⟨by
    refine (injective_iff_map_eq_zero _).2 fun h hh ↦ funext fun k ↦ Subtype.ext ?_
    let h' : ℕ → MvPolynomial σ K := fun j ↦
      if hj : j ≤ d / 2 then (h ⟨j, Nat.lt_succ_of_le hj⟩ : _) else 0
    have hsum : ∑ j ∈ Finset.Iic (d / 2), normSq σ K ^ j * h' j = 0 := by
      have hrange : Finset.Iic (d / 2) = Finset.range (d / 2 + 1) := by ext j; simp
      rw [hrange, ← Fin.sum_univ_eq_sum_range]
      refine Eq.trans (Finset.sum_congr rfl fun j _ ↦ ?_) (congrArg Subtype.val hh)
      simp only [h', dite_eq_left (Nat.le_of_lt_succ j.isLt)]
    have hzero := (sum_normSq_pow_mul_eq_zero_iff (h := h') fun j hj ↦ by
      simp only [h', dite_eq_left hj]
      exact (h ⟨j, Nat.lt_succ_of_le hj⟩).2).1 hsum k (Nat.le_of_lt_succ k.isLt)
    simpa [h', dite_eq_left (Nat.le_of_lt_succ k.isLt)] using hzero, by
    classical
    rw [← LinearMap.range_eq_top, eq_top_iff]
    intro p _
    have hp : (p : MvPolynomial σ K) ∈
        ⨆ k ≤ d / 2, (harmonicSubmodule σ K (d - 2 * k)).map
          (LinearMap.mulLeft K (normSq σ K ^ k)) := by
      rw [← homogeneousSubmodule_eq_iSup_map_mulLeft_normSq_pow]; exact p.2
    suffices hle : ⨆ k ≤ d / 2, (harmonicSubmodule σ K (d - 2 * k)).map
        (LinearMap.mulLeft K (normSq σ K ^ k)) ≤
        (LinearMap.range (fischerLinearMap σ K d)).map (homogeneousSubmodule σ K d).subtype by
      rcases hle hp with ⟨q, hq, hqp⟩
      exact Subtype.ext hqp ▸ hq
    refine iSup₂_le fun k hk ↦ ?_
    rintro _ ⟨q, hq, rfl⟩
    let k₀ : Fin (d / 2 + 1) := ⟨k, Nat.lt_succ_of_le hk⟩
    refine ⟨fischerLinearMap σ K d (Pi.single k₀ ⟨q, hq⟩), ⟨_, rfl⟩, ?_⟩
    exact Eq.trans (Finset.sum_eq_single k₀ (fun j _ hj ↦ by simp [Pi.single_eq_of_ne hj])
      fun hk₀ ↦ (hk₀ (Finset.mem_univ k₀)).elim) (by simp [k₀])⟩

@[simp]
theorem coe_fischerEquiv_apply (d : ℕ)
    (h : Π k : Fin (d / 2 + 1), harmonicSubmodule σ K (d - 2 * k)) :
    (fischerEquiv σ K d h : MvPolynomial σ K) =
      ∑ k : Fin (d / 2 + 1), normSq σ K ^ (k : ℕ) * (h k : MvPolynomial σ K) :=
  (rfl)

/-- Every homogeneous polynomial of degree `d` over a field of characteristic zero (with at least
one variable) decomposes uniquely as `∑_{k ≤ d/2} r^(2k) h_k` with `h_k ∈ H_(d - 2k)`. -/
theorem existsUnique_sum_normSq_pow_mul_eq {d : ℕ} {p : MvPolynomial σ K}
    (hp : p.IsHomogeneous d) :
    ∃! h : Π k : Fin (d / 2 + 1), harmonicSubmodule σ K (d - 2 * k),
      ∑ k : Fin (d / 2 + 1), normSq σ K ^ (k : ℕ) * (h k : MvPolynomial σ K) = p := by
  simpa only [Subtype.ext_iff, coe_fischerEquiv_apply] using
    (fischerEquiv σ K d).bijective.existsUnique ⟨p, hp⟩

/-- **The dimension of the harmonic polynomials**: `dim H_(e+2) + dim P_e = dim P_(e+2)`. -/
theorem finrank_harmonicSubmodule_add_finrank (e : ℕ) :
    Module.finrank K (harmonicSubmodule σ K (e + 2)) +
        Module.finrank K (homogeneousSubmodule σ K e) =
      Module.finrank K (homogeneousSubmodule σ K (e + 2)) := by
  have hinj : Function.Injective (LinearMap.mulLeft K (normSq σ K)) :=
    mul_right_injective₀ (normSq_ne_zero σ K)
  have h := Submodule.finrank_sup_add_finrank_inf_eq (harmonicSubmodule σ K (e + 2))
    ((homogeneousSubmodule σ K e).map (LinearMap.mulLeft K (normSq σ K)))
  have hdisj : Disjoint (harmonicSubmodule σ K (e + 2))
      ((homogeneousSubmodule σ K e).map (LinearMap.mulLeft K (normSq σ K))) :=
    (disjoint_ker_laplacian_range_mulLeft_normSq.mono_left inf_le_right).mono_right
      LinearMap.map_le_range
  rwa [harmonicSubmodule_sup_map_mulLeft_normSq, hdisj.eq_bot, finrank_bot,
    add_zero, ← (Submodule.equivMapOfInjective _ hinj _).finrank_eq, eq_comm] at h

omit [Nonempty σ] in
/-- **The dimension of the harmonic polynomials** of degree `e + 2` in `n` variables is
`n.multichoose (e + 2) - n.multichoose e`, that is `C(n + e + 1, e + 2) - C(n + e - 1, e)` for
`n ≥ 1`. With no variables both sides are `0`; for `e = 0` the right side is then `0 - 1`, which
is `0` by truncated subtraction in `ℕ`. -/
theorem finrank_harmonicSubmodule_add_two (e : ℕ) :
    Module.finrank K (harmonicSubmodule σ K (e + 2)) =
      (Fintype.card σ).multichoose (e + 2) - (Fintype.card σ).multichoose e := by
  rcases isEmpty_or_nonempty σ with hσ | hσ
  · simp
  have h := finrank_harmonicSubmodule_add_finrank (σ := σ) (K := K) e
  rw [TauCeti.finrank_homogeneousSubmodule_eq_multichoose,
    TauCeti.finrank_homogeneousSubmodule_eq_multichoose] at h
  omega

omit [Nonempty σ] in
/-- **The dimension of the harmonic polynomials** of any degree `d` in `n` variables is
`n.multichoose d - (if 2 ≤ d then n.multichoose (d - 2) else 0)`. -/
theorem finrank_harmonicSubmodule (d : ℕ) :
    Module.finrank K (harmonicSubmodule σ K d) =
      (Fintype.card σ).multichoose d -
        if 2 ≤ d then (Fintype.card σ).multichoose (d - 2) else 0 := by
  split_ifs with hd
  · obtain ⟨e, rfl⟩ : ∃ e, d = e + 2 := ⟨d - 2, by omega⟩
    simpa using finrank_harmonicSubmodule_add_two (σ := σ) (K := K) e
  · rw [Nat.sub_zero, finrank_harmonicSubmodule_of_le_one (by omega)]

omit [Nonempty σ] in
/-- **Binomial dimension of the harmonic polynomials**: in `m + 1` variables (`m ≥ 0`), the space
`H_d` of harmonic homogeneous polynomials of degree `d` over a field of characteristic zero has
dimension `C(m + d, d) - C(m + d - 2, d - 2)`, where the subtracted term is `0` for `d < 2`. -/
theorem finrank_harmonicSubmodule_eq_choose_sub {m : ℕ} (hσ : Fintype.card σ = m + 1) (d : ℕ) :
    Module.finrank K (harmonicSubmodule σ K d) =
      (m + d).choose d - if 2 ≤ d then (m + d - 2).choose (d - 2) else 0 := by
  rw [finrank_harmonicSubmodule, hσ]
  split_ifs with hd
  · obtain ⟨e, rfl⟩ : ∃ e, d = e + 2 := ⟨d - 2, by omega⟩
    simp [Nat.multichoose_eq, show m + 1 + (e + 1) = m + (e + 2) by omega,
      show m + (e + 2) - 2 = m + e by omega]
  · simp [Nat.multichoose_eq]

end Fischer

end MvPolynomial
