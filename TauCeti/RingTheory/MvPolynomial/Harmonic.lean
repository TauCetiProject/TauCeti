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

## Main results

* `MvPolynomial.laplacian_mul`: the product rule `Δ (p q) = Δ p q + 2 ∑ᵢ ∂ᵢp ∂ᵢq + p Δ q`.
* `MvPolynomial.IsHomogeneous.laplacian`: the Laplacian lowers the degree by two.
* `MvPolynomial.laplacian_normSq_mul`: `Δ (r² q) = r² Δ q + (2n + 4e) q` for `q ∈ P_e`.
* `MvPolynomial.laplacian_normSq_pow_mul`: `Δ (r^(2(k+1)) h) = 2(k+1)(2l + n + 2k) r^(2k) h`
  for `h ∈ H_l`.
* `MvPolynomial.eq_zero_of_laplacian_normSq_mul_eq_zero` and
  `MvPolynomial.exists_laplacian_normSq_mul_eq`: with at least one variable, `Δ (r² q) = 0 → q = 0`
  (under `HasUniqueDiv R`), and `q ↦ Δ (r² q)` is bijective on `P_e` over a field of
  characteristic zero.
* `MvPolynomial.harmonicSubmodule_sup_map_mulLeft_normSq` and
  `MvPolynomial.disjoint_ker_laplacian_range_mulLeft_normSq`: the Fischer decomposition
  `P_(e+2) = H_(e+2) ⊕ r² P_e`.
* `MvPolynomial.homogeneousSubmodule_eq_iSup_map_mulLeft_normSq_pow`: iterating, every
  homogeneous polynomial of degree `d` is a sum `∑_{k ≤ d/2} r^(2k) h_k` with `h_k ∈ H_(d-2k)`.
* `MvPolynomial.finrank_harmonicSubmodule_add_finrank`,
  `MvPolynomial.finrank_harmonicSubmodule_add_two` and
  `MvPolynomial.finrank_harmonicSubmodule_of_le_one`: the dimension of `H_d`, in terms of the
  multichoose numbers `dim P_d = n.multichoose d`.

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

end Fischer

end MvPolynomial
