/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
public import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula

/-!
# Level-one modular forms of weight divisible by `4` are polynomials in `E₄` and `Δ`

A level-one modular form `f` of weight `k` with `4 ∣ k` is a combination

`f = ∑_{4 a + 12 b = k} c (a, b) • E₄ ^ a * Δ ^ b`

with uniquely determined coefficients `c (a, b) ∈ ℂ`. In other words, the part
`⨁_{4 ∣ k} M_k(SL(2, ℤ))` of the graded ring of level-one modular forms is `ℂ[E₄, Δ]`. This is the
shape in which the theta series of an even unimodular lattice, whose weight is divisible by `4`,
is identified inside the graded ring.

Existence is proved by induction on the weight, as in Mathlib's proof that `E₄` and `E₆` generate
the graded ring (`ModularForm.evalE₄E₆_surjective`), but with `E₄ ^ (k / 4)` in place of a general
monomial in `E₄` and `E₆`. Subtracting the constant term of `f` times `E₄ ^ (k / 4)` leaves a cusp
form, which is `Δ` times a form of weight `k - 12` (`CuspForm.discriminantEquiv`); the case of
weight `k - 12` is the induction hypothesis.

Uniqueness holds in every weight, and is the linear independence of the functions
`E₄ ^ a * Δ ^ b` with `4 a + 12 b = k`: in a vanishing combination, divide by the smallest power
`Δ ^ b₀` that occurs, which is legitimate because `Δ` has no zeros on `ℍ`. As `im τ → ∞`, `E₄`
tends to `1` and `Δ` to `0`, so the quotient tends to the coefficient of the unique pair
`(a₀, b₀)` of weight `k`, which therefore vanishes.

## Main statements

* `ModularForm.linearIndepOn_E₄_pow_mul_discriminant_pow`: the functions `E₄ ^ a * Δ ^ b` with
  `4 a + 12 b = k` are linearly independent.
* `ModularForm.existsUnique_finsupp_E₄_discriminant`: a level-one modular form of weight `k` with
  `4 ∣ k` is a unique combination of the `E₄ ^ a * Δ ^ b` with `4 a + 12 b = k`.

## References

* J.-P. Serre, *A Course in Arithmetic*, Ch. VII, §3.2.
-/

public section

open UpperHalfPlane Filter Topology EisensteinSeries
open scoped MatrixGroups

namespace ModularForm

/-- As `im τ → ∞`, `E₄ τ ^ a * Δ τ ^ b` tends to `1` if `b = 0` and to `0` otherwise. -/
private theorem tendsto_E₄_pow_mul_discriminant_pow (a b : ℕ) :
    Tendsto (fun τ : ℍ ↦ E₄ τ ^ a * discriminant τ ^ b) atImInfty
      (𝓝 (if b = 0 then 1 else 0)) := by
  have hΔ : Tendsto discriminant atImInfty (𝓝 0) := discriminant_isZeroAtImInfty
  simpa [zero_pow_eq] using ((tendsto_E_atImInfty (k := 4)).pow a).mul (hΔ.pow b)

/-- A combination of the `E₄ τ ^ a * Δ τ ^ b` over pairs `(a, b)` of a single weight
`4 a + 12 b = k` that vanishes at every `τ` has zero coefficients. -/
private theorem eq_zero_of_forall_linearCombination_eq_zero {k : ℤ} {l : ℕ × ℕ →₀ ℂ}
    (hl : ∀ ab ∈ l.support, 4 * (ab.1 : ℤ) + 12 * ab.2 = k)
    (h : ∀ τ : ℍ, Finsupp.linearCombination ℂ
      (fun ab : ℕ × ℕ ↦ E₄ τ ^ ab.1 * discriminant τ ^ ab.2) l = 0) :
    l = 0 := by
  by_contra hne
  -- `b₀` is the smallest power of `Δ` occurring in `l`, attained at the pair `(a₀, b₀)`.
  have hs : (l.support.image Prod.snd).Nonempty :=
    (Finsupp.support_nonempty_iff.2 hne).image _
  obtain ⟨⟨a₀, b₀⟩, h₀, hb₀⟩ := Finset.mem_image.1 ((l.support.image Prod.snd).min'_mem hs)
  have hle (ab : ℕ × ℕ) (hab : ab ∈ l.support) : b₀ ≤ ab.2 := by
    rw [show b₀ = _ from hb₀]
    exact Finset.min'_le _ _ (Finset.mem_image_of_mem _ hab)
  -- Dividing the combination by `Δ ^ b₀` gives a function `T` that vanishes identically.
  let T : ℍ → ℂ := fun τ ↦
    ∑ ab ∈ l.support, l ab * (E₄ τ ^ ab.1 * discriminant τ ^ (ab.2 - b₀))
  have hT (τ : ℍ) : T τ = 0 := by
    have hτ : discriminant τ ^ b₀ * T τ = 0 := by
      rw [← h τ, Finsupp.linearCombination_apply, Finsupp.sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun ab hab ↦ ?_
      rw [smul_eq_mul, ← pow_mul_pow_sub _ (hle ab hab)]
      ring
    exact (mul_eq_zero.1 hτ).resolve_left (pow_ne_zero _ (discriminant_ne_zero τ))
  -- At `i∞` the function `T` tends to the coefficient of `(a₀, b₀)`, which therefore vanishes.
  have hlim : Tendsto T atImInfty
      (𝓝 (∑ ab ∈ l.support, l ab * if ab.2 - b₀ = 0 then 1 else 0)) :=
    tendsto_finsetSum _ fun ab _ ↦ (tendsto_E₄_pow_mul_discriminant_pow _ _).const_mul _
  have hsum := tendsto_nhds_unique (tendsto_const_nhds.congr fun τ ↦ (hT τ).symm) hlim
  rw [Finset.sum_eq_single (a₀, b₀) (fun ab hab hne ↦ ?_) (fun h ↦ absurd h₀ h)] at hsum
  · exact Finsupp.mem_support_iff.1 h₀ (by simpa using hsum.symm)
  · -- Any other pair of the same weight has a larger power of `Δ`.
    have hb : ab.2 ≠ b₀ := fun hb ↦ hne <| Prod.ext (by
      have h₁ := hl ab hab
      have h₂ := hl _ h₀
      dsimp only at h₂ ⊢
      omega) hb
    have : ab.2 - b₀ ≠ 0 := by have := hle ab hab; omega
    simp [this]

/-- The functions `E₄ ^ a * Δ ^ b` with `4 a + 12 b = k`, the products of a single weight `k`,
are linearly independent over `ℂ`. -/
theorem linearIndepOn_E₄_pow_mul_discriminant_pow (k : ℤ) :
    LinearIndepOn ℂ (fun ab : ℕ × ℕ ↦ fun τ : ℍ ↦ E₄ τ ^ ab.1 * discriminant τ ^ ab.2)
      {ab | 4 * (ab.1 : ℤ) + 12 * ab.2 = k} := by
  refine linearIndepOn_iff.2 fun l hl h ↦ eq_zero_of_forall_linearCombination_eq_zero
    (fun ab hab ↦ hl hab) fun τ ↦ ?_
  have := congrFun h τ
  simpa [Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_apply] using this

/-- Every level-one modular form of weight `k` with `4 ∣ k` is a combination of the
`E₄ ^ a * Δ ^ b` with `4 a + 12 b = k`. -/
private theorem exists_finsupp_E₄_discriminant {k : ℤ} (f : ModularForm 𝒮ℒ k) (hk : 4 ∣ k) :
    ∃ c : ℕ × ℕ →₀ ℂ, (∀ ab ∈ c.support, 4 * (ab.1 : ℤ) + 12 * ab.2 = k) ∧
      ∀ τ : ℍ, f τ = Finsupp.linearCombination ℂ
        (fun ab : ℕ × ℕ ↦ E₄ τ ^ ab.1 * discriminant τ ^ ab.2) c := by
  induction k using Int.strongRec (m := 0) with
  | lt k hk0 =>
    refine ⟨0, by simp, fun τ ↦ ?_⟩
    simp [rank_zero_iff_forall_zero.mp (levelOne_neg_weight_rank_zero hk0) f]
  | ge k hk0 ih =>
    obtain ⟨n, rfl⟩ := hk
    lift n to ℕ using by omega
    -- Subtracting the constant term of `f` times `E₄ ^ n` leaves a cusp form `g`, and `g` is `Δ`
    -- times the form `g / Δ` of weight `4 n - 12`.
    let m : ModularForm 𝒮ℒ (4 * n) := mcast (by ring) (E₄.pow n)
    have hE : PowerSeries.constantCoeff (qExpansion 1 E₄) = 1 := by
      simpa using E_qExpansion_coeff_zero (k := 4) _ ⟨2, rfl⟩
    have hm : (qExpansion 1 m).coeff 0 = 1 := by
      rw [ModularForm.qExpansion_mcast, ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]
      simp [hE]
    obtain ⟨g, hg⟩ := sub_smul_isCuspForm f m hm
    obtain ⟨c, hc, hgc⟩ :=
      ih (4 * n - 12) (by omega) (CuspForm.discriminantEquiv g) ⟨(n : ℤ) - 3, by ring⟩
    refine ⟨.single (n, 0) ((qExpansion 1 f).coeff 0) +
      c.mapDomain fun ab ↦ (ab.1, ab.2 + 1), fun ab hab ↦ ?_, fun τ ↦ ?_⟩
    · rcases Finset.mem_union.1 (Finsupp.support_add hab) with hab | hab
      · rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hab)]
        simp
      · obtain ⟨ab', hab', rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hab)
        push_cast
        linarith [hc ab' hab']
    · have hgτ : g τ = f τ - (qExpansion 1 f).coeff 0 * E₄ τ ^ n := by
        simpa [m] using congr($hg τ)
      have hf : f τ = (qExpansion 1 f).coeff 0 * E₄ τ ^ n +
          discriminant τ * CuspForm.discriminantEquiv g τ := by
        rw [discriminant_mul_discriminantEquiv_apply, hgτ, add_sub_cancel]
      rw [hf, hgc, map_add, Finsupp.linearCombination_single, Finsupp.linearCombination_mapDomain]
      simp only [smul_eq_mul, pow_zero, mul_one, Function.comp_def,
        Finsupp.linearCombination_apply, Finsupp.sum, Finset.mul_sum, pow_succ]
      exact congrArg _ (Finset.sum_congr rfl fun _ _ ↦ by ring)

/-- **Level-one forms of weight divisible by `4` are polynomials in `E₄` and `Δ`.** A level-one
modular form `f` of weight `k` with `4 ∣ k` is
`f = ∑_{4 a + 12 b = k} c (a, b) • E₄ ^ a * Δ ^ b` for a unique finitely supported family of
coefficients `c (a, b) ∈ ℂ`. -/
theorem existsUnique_finsupp_E₄_discriminant {k : ℤ} (f : ModularForm 𝒮ℒ k) (hk : 4 ∣ k) :
    ∃! c : ℕ × ℕ →₀ ℂ, (∀ ab ∈ c.support, 4 * (ab.1 : ℤ) + 12 * ab.2 = k) ∧
      ⇑f = fun τ ↦ c.sum fun ab z ↦ z * E₄ τ ^ ab.1 * discriminant τ ^ ab.2 := by
  have hsum (c : ℕ × ℕ →₀ ℂ) (τ : ℍ) :
      (c.sum fun ab z ↦ z * E₄ τ ^ ab.1 * discriminant τ ^ ab.2) =
        Finsupp.linearCombination ℂ (fun ab : ℕ × ℕ ↦ E₄ τ ^ ab.1 * discriminant τ ^ ab.2) c := by
    simp [Finsupp.linearCombination_apply, mul_assoc]
  obtain ⟨c, hc, hfc⟩ := exists_finsupp_E₄_discriminant f hk
  refine ⟨c, ⟨hc, funext fun τ ↦ by rw [hfc, hsum]⟩, fun c' ⟨hc', hfc'⟩ ↦ ?_⟩
  -- Two such families differ by a vanishing combination of pairs of weight `k`.
  refine sub_eq_zero.1 (eq_zero_of_forall_linearCombination_eq_zero (k := k) (fun ab hab ↦ ?_)
    fun τ ↦ ?_)
  · rcases Finset.mem_union.1 (Finsupp.support_sub hab) with hab | hab
    exacts [hc' ab hab, hc ab hab]
  · rw [map_sub, ← hsum, ← hfc τ, ← congrFun hfc' τ, sub_self]

end ModularForm
