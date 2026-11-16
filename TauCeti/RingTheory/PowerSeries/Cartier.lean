/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Expand
import TauCeti.Data.Nat.Carry
import TauCeti.RingTheory.PowerSeries.Derivative
import TauCeti.RingTheory.PowerSeries.Expand

/-!
# Cartier operators on power series

The Cartier operator of modulus `q` and index `r` selects coefficients at the indices
`q * n + r`. It is linear in the series. For an actual residue `r < q`, it commutes with
multiplication by an expanded series, and the expanded Cartier components reconstruct the
original series. The Cartier components of a product are sums of products of components whose
residues add up to the given residue, shifted by `X` when the residues carry; for modulus `2`
this is the product formula for even and odd parts. Rescaling the variable by `a` rescales each
Cartier component, so the odd part of `F(-X) F(X)` vanishes. Over a finite field, expansion by its
cardinality is the Frobenius power, so these identities give the usual Cartier identities used
in residue averaging. Since the `j`-th iterate of that expansion is the `q ^ j`-th power map
(`FiniteField.PowerSeries.expand_card_pow_apply`),
for a set `T` of series stable under the Cartier operators of modulus `q = |K|`, the powers
`h ^ q ^ j` with `h ∈ T` lie in the `K[X]`-span of the powers `g ^ q ^ m` with `g ∈ T` whenever
`j ≤ m`; this is the linear-algebra step of the proof of Christol's theorem.
A series whose coefficients vanish away from the multiples of the modulus is the expansion of
its residue-zero Cartier component; in prime characteristic this applies to a series with zero
derivative.

The definition and finite-field multiplication identity follow Section 3, definition and
Proposition 4, of Rowland–Stipulanti–Yassawi, *An elementary proof of Bridy's theorem*
(<https://arxiv.org/html/2308.10977v2>). The substitution identities use Mathlib's
`PowerSeries.expand`; the finite-field specializations use
`FiniteField.PowerSeries.expand_card`.
-/

public section

namespace PowerSeries

section Semiring

variable (R : Type*) [Semiring R]

/-- The Cartier operator selects the coefficients at `q * n + r`. It is defined for every
index `r`; the multiplication identities require `r < q`. -/
noncomputable def cartier (q r : ℕ) : PowerSeries R →ₗ[R] PowerSeries R where
  toFun F := mk fun n ↦ F.coeff (q * n + r)
  map_add' F G := by ext n; simp
  map_smul' a F := by ext n; simp

variable {R}

/-- The defining coefficient equation of a Cartier operator. -/
@[simp]
theorem coeff_cartier (q r n : ℕ) (F : PowerSeries R) :
    (cartier R q r F).coeff n = F.coeff (q * n + r) := by
  simp [cartier]

/-- The constant coefficient of a Cartier component is the coefficient at its index. -/
@[simp]
theorem constantCoeff_cartier (q r : ℕ) (F : PowerSeries R) :
    constantCoeff (cartier R q r F) = F.coeff r := by
  simp [← coeff_zero_eq_constantCoeff_apply]

/-- The residue-zero Cartier operator of modulus one is the identity. -/
@[simp]
theorem cartier_one_zero : cartier R 1 0 = LinearMap.id := by
  ext F n
  simp

/-- At nonzero modulus, the Cartier components of `1` vanish except at residue zero. This
holds even when `r` lies outside the residue range. -/
@[simp]
theorem cartier_one (q r : ℕ) (hq : q ≠ 0) :
    cartier R q r 1 = if r = 0 then 1 else 0 := by
  ext n
  by_cases hr : r = 0 <;> simp [hr, coeff_one, hq]

/-- On a monomial, a Cartier operator keeps precisely its residue class. -/
@[simp]
theorem cartier_monomial (q r m : ℕ) (hr : r < q) (a : R) :
    cartier R q r (monomial m a) =
      if m % q = r then monomial (m / q) a else 0 := by
  ext n
  have hq' : 0 < q := Nat.lt_of_le_of_lt (Nat.zero_le r) hr
  have hn : q * n + r = m ↔ m % q = r ∧ n = m / q := by
    constructor
    · rintro rfl
      simp [Nat.add_mod, Nat.mod_eq_of_lt hr, Nat.mul_add_div hq', Nat.div_eq_of_lt hr]
    · rintro ⟨hm, rfl⟩
      simpa [hm, Nat.add_comm] using Nat.mod_add_div m q
  simp only [coeff_cartier, coeff_monomial, hn]
  split_ifs <;> simp_all [coeff_monomial]

/-- At nonzero modulus, a Cartier operator sends a polynomial to a polynomial whose degree is at
most the original degree divided by the modulus. This holds for every index `r`. -/
theorem exists_cartier_coe_polynomial_eq (q r : ℕ) (hq : q ≠ 0) (P : Polynomial R) :
    ∃ P' : Polynomial R, P'.natDegree ≤ P.natDegree / q ∧ cartier R q r (P : R⟦X⟧) = P' := by
  classical
  refine ⟨∑ n ∈ Finset.range (P.natDegree / q + 1), Polynomial.monomial n (P.coeff (q * n + r)),
    Polynomial.natDegree_sum_le_of_forall_le _ _ fun n hn ↦
      (Polynomial.natDegree_monomial_le _).trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)),
    ?_⟩
  ext n
  simp only [coeff_cartier, Polynomial.coeff_coe, Polynomial.finsetSum_coeff,
    Polynomial.coeff_monomial_apply, Finset.sum_ite_eq', Finset.mem_range]
  split_ifs with hn
  · rfl
  · refine Polynomial.coeff_eq_zero_of_natDegree_lt ?_
    have hlt : P.natDegree / q < n := by omega
    have := (Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero hq)).mp hlt
    nlinarith

/-- **Cartier components of a product.** At an actual residue `r`, the Cartier component of
`F * G` collects the products of the components of `F` and `G` whose residues add up to `r`
modulo `q`, shifted by `X` when the residues carry past `q`. -/
theorem cartier_mul (q r : ℕ) (hr : r < q) (F G : PowerSeries R) :
    cartier R q r (F * G) = ∑ a ∈ Finset.range q, ∑ b ∈ Finset.range q,
      if (a + b) % q = r then X ^ ((a + b) / q) * (cartier R q a F * cartier R q b G)
      else 0 := by
  classical
  have hq : 0 < q := Nat.zero_lt_of_lt hr
  ext n
  rw [coeff_cartier, coeff_mul, ← Finset.sum_fiberwise_of_maps_to
    (g := fun p : ℕ × ℕ ↦ (p.1 % q, p.2 % q)) (t := Finset.range q ×ˢ Finset.range q)
    fun p _ ↦ Finset.mem_product.2 ⟨Finset.mem_range.2 (Nat.mod_lt _ hq),
      Finset.mem_range.2 (Nat.mod_lt _ hq)⟩, Finset.sum_product, map_sum]
  refine Finset.sum_congr rfl fun a ha ↦ ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun b hb ↦ ?_
  rw [Finset.mem_range] at ha hb
  have key : ∀ p ∈ {p ∈ Finset.antidiagonal (q * n + r) | (p.1 % q, p.2 % q) = (a, b)},
      (a + b) % q = r ∧ p.1 / q + p.2 / q + (a + b) / q = n := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_antidiagonal, Prod.mk.injEq] at hp
    rw [← hp.2.1, ← hp.2.2, ← Nat.add_mod, ← Nat.add_div_eq_div_add_div_add_mod_add_mod_div, hp.1]
    simp [Nat.mod_eq_of_lt hr, Nat.mul_add_div hq, Nat.div_eq_of_lt hr]
  split_ifs with hab
  · rw [coeff_X_pow_mul']
    split_ifs with hc
    · rw [coeff_mul]
      refine Finset.sum_nbij' (fun p ↦ (p.1 / q, p.2 / q)) (fun p ↦ (q * p.1 + a, q * p.2 + b))
        (fun p hp ↦ ?_) (fun p hp ↦ ?_) (fun p hp ↦ ?_) (fun p _ ↦ ?_) (fun p hp ↦ ?_)
      · have := (key p hp).2
        rw [Finset.mem_antidiagonal]
        omega
      · rw [Finset.mem_antidiagonal] at hp
        have h3 := Nat.div_add_mod (a + b) q
        -- `omega` cannot multiply by the variable modulus `q`, so the quotient identity is
        -- multiplied by `q` here and distributed before the linear arithmetic below.
        have h : q * (p.1 + p.2 + (a + b) / q) = q * n := by
          rw [show p.1 + p.2 + (a + b) / q = n by omega]
        rw [hab] at h3
        rw [mul_add, mul_add] at h
        simp [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
        omega
      · simp only [Finset.mem_filter, Prod.mk.injEq] at hp
        have h1 := Nat.div_add_mod p.1 q
        have h2 := Nat.div_add_mod p.2 q
        rw [hp.2.1] at h1
        rw [hp.2.2] at h2
        ext <;> simp <;> omega
      · simp [Nat.mul_add_div hq, Nat.div_eq_of_lt ha, Nat.div_eq_of_lt hb]
      · simp only [Finset.mem_filter, Prod.mk.injEq] at hp
        rw [coeff_cartier, coeff_cartier, ← hp.2.1, ← hp.2.2, Nat.div_add_mod, Nat.div_add_mod]
    · exact Finset.sum_eq_zero fun p hp ↦
        (hc ((key p hp).2 ▸ Nat.le_add_left _ _)).elim
  · exact Finset.sum_eq_zero fun p hp ↦ (hab (key p hp).1).elim

/-- The even part of a product: writing `F(X) = F₀(X²) + X F₁(X²)` and similarly for `G`, the
even part of `F * G` is `F₀ G₀ + X F₁ G₁`. -/
theorem cartier_two_zero_mul (F G : PowerSeries R) :
    cartier R 2 0 (F * G) =
      cartier R 2 0 F * cartier R 2 0 G + X * (cartier R 2 1 F * cartier R 2 1 G) := by
  simp [cartier_mul 2 0 two_pos, Finset.sum_range_succ]

/-- The odd part of a product: writing `F(X) = F₀(X²) + X F₁(X²)` and similarly for `G`, the
odd part of `F * G` is `F₀ G₁ + F₁ G₀`. -/
theorem cartier_two_one_mul (F G : PowerSeries R) :
    cartier R 2 1 (F * G) =
      cartier R 2 0 F * cartier R 2 1 G + cartier R 2 1 F * cartier R 2 0 G := by
  simp [cartier_mul 2 1 one_lt_two, Finset.sum_range_succ]

end Semiring

section CommSemiring

variable {R : Type*} [CommSemiring R]

/-- Rescaling the variable by `a` multiplies the Cartier component of modulus `q` and index `r`
by `a ^ r` and rescales it by `a ^ q`. -/
theorem cartier_rescale (q r : ℕ) (a : R) (F : PowerSeries R) :
    cartier R q r (rescale a F) = a ^ r • rescale (a ^ q) (cartier R q r F) := by
  ext n
  simp only [coeff_cartier, coeff_rescale, coeff_smul, smul_eq_mul]
  ring

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R]

/-- Multiplication by an expanded series passes through a Cartier operator at an actual
residue. -/
theorem cartier_expand_mul (q r : ℕ) (hq : q ≠ 0) (hr : r < q)
    (F G : PowerSeries R) :
    cartier R q r (expand q hq F * G) = F * cartier R q r G := by
  classical
  ext n
  rw [coeff_cartier, coeff_mul, coeff_mul]
  symm
  refine Finset.sum_bij_ne_zero
    (fun ij _ _ ↦ (q * ij.1, q * ij.2 + r)) ?_ ?_ ?_ ?_
  · intro ij hij _
    rw [Finset.mem_antidiagonal] at hij ⊢
    nlinarith [hij]
  · intro ij _ _ kl _ _ heq
    obtain ⟨h₁, h₂⟩ := Prod.mk.inj heq
    apply Prod.ext <;> nlinarith
  · intro ij hij hne
    have hi : q ∣ ij.1 := by
      by_contra hi
      simp [coeff_expand_of_not_dvd q hq F hi] at hne
    obtain ⟨i, hi⟩ := hi
    have heq := Finset.mem_antidiagonal.mp hij
    have hin : i ≤ n := by nlinarith
    have hj : ij.2 = q * (n - i) + r := by
      have := Nat.sub_add_cancel hin
      nlinarith
    refine ⟨(i, n - i), Finset.mem_antidiagonal.mpr (Nat.add_sub_of_le hin), ?_, ?_⟩
    · simpa [hi, hj, coeff_cartier] using hne
    · exact Prod.ext hi.symm hj.symm
  · intro ij _ _
    simp [coeff_cartier]

/-- Every series is the sum of its expanded Cartier components, one for each residue. -/
theorem sum_X_pow_mul_expand_cartier (q : ℕ) (hq : q ≠ 0) (F : PowerSeries R) :
    F = ∑ r ∈ Finset.range q, X ^ r * expand q hq (cartier R q r F) := by
  classical
  ext n
  rw [map_sum]
  have hq' := Nat.pos_of_ne_zero hq
  symm
  rw [Finset.sum_eq_single (n % q)]
  · have hle := Nat.mod_le n q
    rw [coeff_X_pow_mul', ite_eq_left hle]
    have hn : n - n % q = q * (n / q) := by
      have := Nat.mod_add_div n q
      omega
    rw [hn, coeff_expand_mul, coeff_cartier]
    simpa [Nat.add_comm] using congrArg (fun k ↦ F.coeff k) (Nat.mod_add_div n q)
  · intro r hr hne
    rw [coeff_X_pow_mul']
    split_ifs with hle
    · have hnd : ¬ q ∣ n - r := by
        intro hd
        have hmod : n % q = r := by
          obtain ⟨i, hi⟩ := hd
          have hn : n = q * i + r := by omega
          rw [hn, Nat.add_mod]
          simp [Nat.mod_eq_of_lt (Finset.mem_range.mp hr)]
        exact hne hmod.symm
      exact coeff_expand_of_not_dvd q hq _ hnd
    · rfl
  · intro hnot
    exact (hnot (Finset.mem_range.mpr (Nat.mod_lt n hq'))).elim

/-- The even part of `F(-X)` is the even part of `F`, evaluated at `X`. -/
@[simp]
theorem cartier_two_zero_rescale_neg_one (F : PowerSeries R) :
    cartier R 2 0 (rescale (-1) F) = cartier R 2 0 F := by
  simp [cartier_rescale]

/-- The odd part of `F(-X)` is minus the odd part of `F`. -/
@[simp]
theorem cartier_two_one_rescale_neg_one (F : PowerSeries R) :
    cartier R 2 1 (rescale (-1) F) = -cartier R 2 1 F := by
  simp [cartier_rescale]

/-- The product `F(-X) F(X)` is even: its odd part vanishes. -/
@[simp]
theorem cartier_two_one_rescale_neg_one_mul_self (F : PowerSeries R) :
    cartier R 2 1 (rescale (-1) F * F) = 0 := by
  rw [cartier_two_one_mul, cartier_two_zero_rescale_neg_one, cartier_two_one_rescale_neg_one]
  ring

/-- A series whose coefficients vanish away from the multiples of `q` is the expansion of its
residue-zero Cartier component. -/
theorem expand_cartier_zero_of_coeff_eq_zero (q : ℕ) (hq : q ≠ 0) {F : PowerSeries R}
    (hF : ∀ n, ¬ q ∣ n → F.coeff n = 0) : expand q hq (cartier R q 0 F) = F := by
  ext n
  by_cases hn : q ∣ n
  · obtain ⟨m, rfl⟩ := hn
    simp
  · rw [coeff_expand_of_not_dvd _ _ _ hn, hF n hn]

end CommRing

section Characteristic

variable {R : Type*} [CommRing R] {p : ℕ} [Fact p.Prime] [CharP R p]

/-- The residue-zero Cartier component recovers a series with zero derivative by expansion
in prime characteristic. -/
theorem expand_cartier_of_derivative_eq_zero {f : PowerSeries R}
    (hf : derivative f = 0) : expand p (Fact.out : p.Prime).ne_zero (cartier R p 0 f) = f :=
  expand_cartier_zero_of_coeff_eq_zero _ _ fun _ hn ↦ coeff_eq_zero_of_derivative_eq_zero hf hn

end Characteristic

section FiniteField

variable {K : Type*} [Field K] [Fintype K]

/-- Over a finite field, multiplication by a cardinality power passes through a Cartier
operator at an actual residue. -/
theorem cartier_pow_card_mul (r : ℕ) (hr : r < Fintype.card K) (F G : PowerSeries K) :
    cartier K (Fintype.card K) r (F ^ Fintype.card K * G) =
      F * cartier K (Fintype.card K) r G := by
  rw [← FiniteField.PowerSeries.expand_card]
  exact cartier_expand_mul _ _ Fintype.card_ne_zero hr F G

/-- Over a finite field, a series is the sum of the cardinality powers of its Cartier
components multiplied by the corresponding powers of `X`. -/
theorem eq_sum_X_pow_mul_cartier_pow (F : PowerSeries K) :
    F = ∑ r ∈ Finset.range (Fintype.card K),
      X ^ r * (cartier K (Fintype.card K) r F) ^ Fintype.card K := by
  simpa only [FiniteField.PowerSeries.expand_card] using
    sum_X_pow_mul_expand_cartier (Fintype.card K) Fintype.card_ne_zero F

/-- Over a finite field `K` with `q` elements, let `T` be a set of power series that is stable under
the Cartier operators `cartier K q r` with `r < q`. For `h ∈ T` and `j ≤ m`, the power `h ^ q ^ j`
lies in the `K[X]`-span of the powers `g ^ q ^ m` with `g ∈ T`. -/
theorem pow_card_pow_mem_span_of_cartier_stable {T : Set (PowerSeries K)}
    (hTq : ∀ h ∈ T, ∀ r < Fintype.card K, cartier K (Fintype.card K) r h ∈ T) {h : PowerSeries K}
    (hh : h ∈ T) {j m : ℕ} (hjm : j ≤ m) :
    h ^ Fintype.card K ^ j ∈ Submodule.span (Polynomial K) ((· ^ Fintype.card K ^ m) '' T) := by
  set q := Fintype.card K
  -- The `q ^ j`-th power map is the `j`-th iterate of the `K`-algebra endomorphism `expand q`.
  set F : PowerSeries K →ₐ[K] PowerSeries K := expand q Fintype.card_ne_zero
  have hFj (j : ℕ) (h : PowerSeries K) : (F ^ j) h = h ^ q ^ j :=
    FiniteField.PowerSeries.expand_card_pow_apply j h
  -- The spans `M j` of the powers `h ^ q ^ j` with `h ∈ T` increase with `j`.
  set M : ℕ → Submodule (Polynomial K) (PowerSeries K) := fun j ↦
    Submodule.span (Polynomial K) ((· ^ q ^ j) '' T)
  have hM : Monotone M := by
    refine monotone_nat_of_le_succ fun j ↦ Submodule.span_le.mpr ?_
    rintro _ ⟨h, hh, rfl⟩
    -- Apply the `q ^ j`-th power map to `h = ∑_{r < q} X ^ r * (Λ_r h) ^ q`.
    have hsum := congrArg (F ^ j) (eq_sum_X_pow_mul_cartier_pow h)
    rw [hFj, map_sum] at hsum
    -- The membership goal is stated for the image function applied to `h`.
    change h ^ q ^ j ∈ M (j + 1)
    rw [hsum]
    refine Submodule.sum_mem _ fun r hr ↦ ?_
    have hterm : (F ^ j) (X ^ r * cartier K q r h ^ q) =
        ((Polynomial.X : Polynomial K) ^ (q ^ j * r)) • cartier K q r h ^ q ^ (j + 1) := by
      simp only [hFj, Algebra.smul_def, algebraMap_apply', Algebra.algebraMap_self,
        Polynomial.coe_pow, Polynomial.coe_X, map_id, id_eq]
      ring
    rw [hterm]
    exact Submodule.smul_mem _ _ <|
      Submodule.subset_span ⟨_, hTq h hh r (Finset.mem_range.mp hr), rfl⟩
  exact hM hjm (Submodule.subset_span ⟨h, hh, rfl⟩)

end FiniteField

/-! The small examples also check the residue restriction in the multiplication identities. -/

example : cartier (ZMod 3) 3 1 (monomial 7 (1 : ZMod 3)) = monomial 2 1 ∧
    cartier (ZMod 3) 3 0 (monomial 7 (1 : ZMod 3)) = 0 := by
  constructor <;> simp [cartier_monomial]

example (F : PowerSeries ℤ) : cartier ℤ 1 0 F = F := by simp

example (F : PowerSeries (ZMod 3)) : cartier (ZMod 3) 3 0 (F ^ 3) = F := by
  simpa using cartier_pow_card_mul (K := ZMod 3) 0 (by decide) F 1

example : cartier ℤ 1 1 (expand 1 one_ne_zero (X : PowerSeries ℤ) * 1) = 1 ∧
    (X : PowerSeries ℤ) * cartier ℤ 1 1 1 = 0 := by
  constructor
  · ext n
    simp [coeff_X, coeff_one]
  · simp

example : cartier (ZMod 3) 3 3 ((X : PowerSeries (ZMod 3)) ^ 3 * 1) = 1 ∧
    (X : PowerSeries (ZMod 3)) * cartier (ZMod 3) 3 3 1 = 0 := by
  constructor
  · ext n
    simp [coeff_X_pow, coeff_one]
  · simp

end PowerSeries
