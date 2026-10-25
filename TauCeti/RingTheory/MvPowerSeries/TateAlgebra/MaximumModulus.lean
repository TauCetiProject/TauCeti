/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Eval
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

import Mathlib.Algebra.Field.GeomSum
import TauCeti.Analysis.Normed.Group.NullFamily

/-!
# Maximum modulus for Tate algebras at roots of unity

Let `f = ∑ₜ fₜ Xᵗ` be a restricted power series in `k` variables at unit polyradius over an
ultrametric normed ring `R`, and let `φ : R → S` be an isometric ring homomorphism into a complete
ultrametric normed field. Suppose that `S` contains a primitive `m`-th root of unity `ζ`, where
`‖m‖ = 1` in `S` and `m` exceeds every exponent of every coefficient `fₜ` with `‖fₜ‖ = ‖f‖`.
Then `f` attains its Gauss norm at a point of `S ^ k` whose coordinates are powers of `ζ`.

The proof is discrete Fourier inversion. Let `t₀` be an exponent with `‖fₜ₀‖ = ‖f‖`. Averaging
the values `f(ζʲ)` against the characters `ζ^(-⟨j, t₀⟩)` over `j ∈ (ℤ ⧸ m) ^ k` gives
`m ^ k ∑_{t ≡ t₀} φ(fₜ)`, the sum over the exponents congruent to `t₀` modulo `m`. By the choice of
`m` the term at `t₀` is the only one of norm `‖f‖`, so this sum has norm `‖f‖`, and since
`‖m‖ = 1` the ultrametric inequality forces `‖f(ζʲ)‖ ≥ ‖f‖` for some `j`. The reverse inequality
holds at every point of the closed unit polydisc.

The condition `‖m‖ = 1` excludes multiples of the residue characteristic, so that the reductions of
the `m`-th roots of unity are distinct. Points with coordinates in `R` do not suffice in general:
over `ℚ_p` the polynomial `X ^ p - X` has Gauss norm one but takes values of norm at most `p⁻¹` on
`ℤ_p`.

## Main results

* `MvPowerSeries.exists_norm_restrictedEval₂_eq_norm`: a restricted series attains its Gauss norm
  at a point whose coordinates are `m`-th roots of unity.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §5.1.4.
-/

public section

namespace MvPowerSeries

/-- The sum of the powers `(ζ ^ e) ^ a` over `a < m` of a primitive `m`-th root of unity is `m` if
`m` divides `e`, and zero otherwise. -/
private theorem sum_pow_pow_eq {F : Type*} [Field F] {ζ : F} {m : ℕ} (hζ : IsPrimitiveRoot ζ m)
    (e : ℕ) :
    ∑ a : Fin m, (ζ ^ e) ^ (a : ℕ) = if m ∣ e then (m : F) else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun a ↦ (ζ ^ e) ^ a)]
  split_ifs with h
  · simp [(hζ.pow_eq_one_iff_dvd e).mpr h]
  · have h1 : ζ ^ e ≠ 1 := fun h' ↦ h ((hζ.pow_eq_one_iff_dvd e).mp h')
    rw [geom_sum_eq h1, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow, sub_self,
      zero_div]

/-- **Orthogonality of characters.** Averaging the monomial `c ∏ᵢ (ζ ^ jᵢ) ^ tᵢ` against the
character `j ↦ ζ ^ (-⟨j, t₀⟩)` over `j ∈ {0, …, m - 1} ^ k` gives `c m ^ k` if `t ≡ t₀` modulo
`m`, and zero otherwise. The character is written with the natural exponents `(m - 1) t₀ᵢ`. -/
private theorem sum_mul_monomial_eq {F : Type*} [Field F] {k m : ℕ} {ζ : F}
    (hζ : IsPrimitiveRoot ζ m) (t₀ t : Fin k → ℕ) (c : F) :
    ∑ j : Fin k → Fin m, (∏ i, ζ ^ ((j i : ℕ) * ((m - 1) * t₀ i))) *
        (c * ∏ i, (ζ ^ (j i : ℕ)) ^ t i) =
      c * ∏ i, if m ∣ (m - 1) * t₀ i + t i then (m : F) else 0 := by
  classical
  simp only [← sum_pow_pow_eq hζ, Fintype.prod_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [mul_left_comm, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [← pow_mul, ← pow_mul, ← pow_add]
  ring_nf

/-- Two residues `a, b < m` with `m ∣ (m - 1) a + b` are equal, since `(m - 1) a ≡ -a` modulo
`m`. -/
private theorem eq_of_dvd_sub_one_mul_add {m a b : ℕ} (ha : a < m) (hb : b < m)
    (h : m ∣ (m - 1) * a + b) : b = a := by
  obtain ⟨q, hq⟩ := h
  have hab : m * a + b = m * q + a := by
    rw [← hq, add_right_comm, ← add_one_mul, Nat.sub_add_cancel (by omega)]
  have := congrArg (· % m) hab
  simpa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using this

variable {k : ℕ} {R S : Type*} [NormedCommRing R] [IsUltrametricDist R]
  [NormedField S] [IsUltrametricDist S] [CompleteSpace S] (φ : R →+* S)

/-- **Discrete Fourier inversion for restricted series.** Averaging the values `f(ζʲ)` against
the character `j ↦ ζ ^ (-⟨j, t₀⟩)` over `j ∈ {0, …, m - 1} ^ k` is the sum of `m ^ k φ(fₜ)` over
the exponents `t ≡ t₀` modulo `m`. -/
private theorem hasSum_sum_mul_restrictedEval₂ (hφ : ∀ r, ‖φ r‖ ≤ ‖r‖) {m : ℕ} {ζ : S}
    (hζ : IsPrimitiveRoot ζ m) (hx : ∀ (j : Fin k → Fin m) i, ‖ζ ^ (j i : ℕ)‖ ≤ 1)
    (f : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) (t₀ : Fin k →₀ ℕ) :
    HasSum (fun t ↦ φ (coeff t (f : MvPowerSeries (Fin k) R)) *
        ∏ i, if m ∣ (m - 1) * t₀ i + t i then (m : S) else 0)
      (∑ j : Fin k → Fin m, (∏ i, ζ ^ ((j i : ℕ) * ((m - 1) * t₀ i))) *
        restrictedEval₂ φ (fun i ↦ ζ ^ (j i : ℕ)) hφ (hx j) f) := by
  convert hasSum_sum fun j (_ : j ∈ Finset.univ) ↦
    (hasSum_restrictedEval₂ φ _ hφ (hx j) f).mul_left
      (∏ i, ζ ^ ((j i : ℕ) * ((m - 1) * t₀ i))) using 1
  funext t
  simp only [TauCeti.Huber.weightedEvalTerm_def]
  exact (sum_mul_monomial_eq hζ t₀ t _).symm

/-- **Maximum modulus at roots of unity.** Let `φ : R → S` be an isometric ring homomorphism into
a complete ultrametric normed field containing a primitive `m`-th root of unity `ζ`, where
`‖m‖ = 1` in `S` and `m` exceeds every exponent of every coefficient of `f` of norm `‖f‖`. Then
there is a point `x` of the closed unit polydisc of `S ^ k`, with coordinates powers of `ζ`, at
which `‖f(x)‖ = ‖f‖`. -/
theorem exists_norm_restrictedEval₂_eq_norm (hφ : ∀ r, ‖φ r‖ = ‖r‖) {m : ℕ} {ζ : S}
    (hζ : IsPrimitiveRoot ζ m) (hm : ‖(m : S)‖ = 1)
    (f : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1))
    (hfm : ∀ t, ‖coeff t (f : MvPowerSeries (Fin k) R)‖ = ‖f‖ → ∀ i, t i < m) :
    ∃ (x : Fin k → S) (hx : ∀ i, ‖x i‖ ≤ 1), (∀ i, ∃ a < m, x i = ζ ^ a) ∧
      ‖restrictedEval₂ φ x (fun r ↦ (hφ r).le) hx f‖ = ‖f‖ := by
  classical
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hm
  have hζ1 : ‖ζ‖ = 1 :=
    (pow_eq_one_iff_of_nonneg (norm_nonneg ζ) hm0).mp
      (by rw [← norm_pow, hζ.pow_eq_one, norm_one])
  have hζa (a : ℕ) : ‖ζ ^ a‖ = 1 := by rw [norm_pow, hζ1, one_pow]
  -- The point `ζʲ` attached to `j ∈ {0, …, m - 1} ^ k`.
  let x (j : Fin k → Fin m) : Fin k → S := fun i ↦ ζ ^ (j i : ℕ)
  have hx (j : Fin k → Fin m) (i : Fin k) : ‖x j i‖ ≤ 1 := (hζa _).le
  let ev (j : Fin k → Fin m) := restrictedEval₂ φ (x j) (fun r ↦ (hφ r).le) (hx j) f
  suffices H : ∃ j, ‖f‖ ≤ ‖ev j‖ by
    obtain ⟨j, hj⟩ := H
    exact ⟨x j, hx j, fun i ↦ ⟨j i, (j i).2, rfl⟩,
      le_antisymm (norm_restrictedEval₂_le _ _ _ _ f) hj⟩
  rcases eq_or_ne f 0 with rfl | hf
  · have : Nonempty (Fin k → Fin m) := ⟨fun _ ↦ ⟨0, Nat.pos_of_ne_zero hm0⟩⟩
    exact ⟨Classical.arbitrary _, by simp⟩
  -- A dominant exponent `t₀`.
  obtain ⟨t₀, ht₀⟩ := exists_achievesGaussNorm f
  have h1 (t : Fin k →₀ ℕ) : (t.prod fun _ _ ↦ (1 : ℝ)) = 1 := by simp [Finsupp.prod]
  simp only [AchievesGaussNorm, one_pow, h1, mul_one] at ht₀
  rw [← norm_eq_gaussNorm] at ht₀
  -- The character `j ↦ ζ ^ (-⟨j, t₀⟩)`, written with natural exponents.
  let w (j : Fin k → Fin m) : S := ∏ i, ζ ^ ((j i : ℕ) * ((m - 1) * t₀ i))
  have hw (j : Fin k → Fin m) : ‖w j‖ = 1 := by
    simp only [w, norm_prod, hζa, Finset.prod_const_one]
  -- Averaging the values `f(ζʲ)` against the character isolates the coefficients at the exponents
  -- congruent to `t₀` modulo `m`; among them only `t₀` has norm `‖f‖`.
  let g (t : Fin k →₀ ℕ) : S := φ (coeff t (f : MvPowerSeries (Fin k) R)) *
    ∏ i, if m ∣ (m - 1) * t₀ i + t i then (m : S) else 0
  have hsum : HasSum g (∑ j, w j * ev j) := hasSum_sum_mul_restrictedEval₂ φ _ hζ hx f t₀
  have hgt₀ : ‖g t₀‖ = ‖f‖ := by
    have hdvd (i : Fin k) : m ∣ (m - 1) * t₀ i + t₀ i :=
      ⟨t₀ i, by rw [← add_one_mul, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hm0)]⟩
    simp [g, hdvd, hφ, hm, ht₀]
  have hg (t : Fin k →₀ ℕ) (ht : t ≠ t₀) : ‖g t‖ < ‖g t₀‖ := by
    rw [hgt₀]
    rcases (norm_coeff_mul_prod_le f t).lt_or_eq with hlt | heq
    · -- Each factor of the product has norm at most one.
      simp only [one_pow, h1, mul_one] at hlt
      refine lt_of_le_of_lt ?_ hlt
      rw [norm_mul, hφ, norm_prod]
      refine mul_le_of_le_one_right (norm_nonneg _) <|
        Finset.prod_le_one₀ (fun _ _ ↦ norm_nonneg _) fun i _ ↦ ?_
      split_ifs <;> simp [hm]
    -- A second dominant exponent is not congruent to `t₀`, so its term vanishes.
    simp only [one_pow, h1, mul_one] at heq
    obtain ⟨i, hi⟩ : ∃ i, t i ≠ t₀ i := by
      by_contra! h
      exact ht (Finsupp.ext h)
    have hzero : g t = 0 := by
      refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ i) ?_)
      rw [ite_eq_right_iff]
      exact fun h ↦ absurd (eq_of_dvd_sub_one_mul_add (hfm t₀ ht₀ i) (hfm t heq i) h) hi
    simpa [hzero] using hf
  have htotal : ‖∑ j, w j * ev j‖ = ‖f‖ := (hsum.norm_eq_of_forall_norm_lt t₀ hg).trans hgt₀
  -- Some term of the average has norm at least `‖f‖`.
  have : Nonempty (Fin k → Fin m) := ⟨fun _ ↦ ⟨0, Nat.pos_of_ne_zero hm0⟩⟩
  obtain ⟨j, -, hj⟩ := IsUltrametricDist.exists_norm_finsetSum_le Finset.univ
    fun j ↦ w j * ev j
  refine ⟨j, ?_⟩
  rwa [htotal, norm_mul, hw, one_mul] at hj

end MvPowerSeries
