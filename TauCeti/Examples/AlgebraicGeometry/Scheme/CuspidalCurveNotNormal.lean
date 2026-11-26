/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.Algebra.Polynomial.Expand
public import TauCeti.AlgebraicGeometry.Scheme.Normal

/-!
# The curve `y² + (x + c)ⁿ = 0` is not normal for odd `n ≥ 3`

Normality is not preserved under inseparable extension of the ground field: for `k = 𝔽_p(t)` with
`p` odd, the curve `C : x^p + y² + t = 0` becomes, over `k' = k(t^{1/p})` and with
`u = x + t^{1/p}`, the integral curve `u^p + y² = 0`, which is not normal at `u = y = 0`. This file
proves the non-normality.

Over a domain `K`, put `A = K[x, y]/(y² + (x + c)ⁿ)` for `c ∈ K` and odd `n`, as
`AdjoinRoot (poly c n)` over `K[x]`. The parametrization `s ↦ (x, y) = (-s² - c, sⁿ)` is an
injective ring homomorphism `A → K[s]` (`param_injective`): every element of `A` is
`r₀(x) + r₁(x) y`, whose image `r₀(-s² - c) + r₁(-s² - c) sⁿ` splits into even and odd powers of
`s`. So `A` is a domain (`isDomain`). The element `y / (x + c)^((n-1)/2)` of the fraction field
squares to `-(x + c)`, so it is integral over `A`; it lies in `A` only if `s` lies in the image of
the parametrization, which has no `s¹` term once `n ≥ 3`. Hence `A` is not integrally closed
(`not_isIntegrallyClosed`) and `Spec A` is not normal (`not_isNormalScheme`). In characteristic
`p` with `c^p = t`, `(x + c)^p = x^p + t`, which gives the curve `x^p + y² + t = 0`
(`not_isNormalScheme_of_charP`).
-/

public section

open AlgebraicGeometry Polynomial TauCeti.AlgebraicGeometry

universe u

namespace TauCeti.CuspidalCurveExample

variable {K : Type u} [CommRing K]

/-- The polynomial `Y² + (X + c)ⁿ` over `K[X]`, whose quotient is the coordinate ring of the
plane curve `y² + (x + c)ⁿ = 0`. -/
noncomputable def poly (c : K) (n : ℕ) : K[X][X] := X ^ 2 + C ((X + C c) ^ n)

theorem poly_def (c : K) (n : ℕ) : poly c n = X ^ 2 + C ((X + C c) ^ n) := (rfl)

theorem degree_poly [Nontrivial K] (c : K) (n : ℕ) : (poly c n).degree = 2 :=
  degree_X_pow_add_C two_pos _

theorem monic_poly (c : K) (n : ℕ) : (poly c n).Monic :=
  monic_X_pow_add_C _ two_ne_zero

/-- The polynomial substituted for `x` by the parametrization: `-s² - c`. -/
noncomputable abbrev paramX (c : K) : K[X] := -X ^ 2 - C c

private theorem comp_paramX_eq_expand (q : K[X]) (c : K) :
    q.comp (paramX c) = expand K 2 (q.comp (-X - C c)) := by
  rw [expand_eq_comp_X_pow, comp_assoc]
  simp

private theorem coeff_comp_paramX_of_odd (q : K[X]) (c : K) {k : ℕ} (hk : Odd k) :
    (q.comp (paramX c)).coeff k = 0 := by
  rw [comp_paramX_eq_expand, coeff_expand two_pos]
  simp [hk.not_two_dvd_nat]

private theorem eq_zero_of_comp_paramX_eq_zero {q : K[X]} {c : K} (h : q.comp (paramX c) = 0) :
    q = 0 := by
  rw [comp_paramX_eq_expand, expand_eq_zero two_pos] at h
  have : q = (q.comp (-X - C c)).comp (-X - C c) := by
    rw [comp_assoc]
    simp
  rw [this, h, zero_comp]

private theorem coeff_comp_paramX_mul_X_pow_of_even (q : K[X]) (c : K) {n k : ℕ} (hn : Odd n)
    (hk : Even k) : (q.comp (paramX c) * X ^ n).coeff k = 0 := by
  rw [coeff_mul_X_pow']
  split_ifs with h
  · exact coeff_comp_paramX_of_odd q c (Nat.Even.sub_odd h hk hn)
  · rfl

private theorem X_add_C_comp_paramX (c : K) :
    (X + C c : K[X]).comp (paramX c) = C (-1) * X ^ 2 := by
  simp [paramX]

/-- The parametrization `s ↦ (x, y) = (-s² - c, sⁿ)` of the curve `y² + (x + c)ⁿ = 0`, for odd
`n`. -/
noncomputable def param (c : K) {n : ℕ} (hn : Odd n) : AdjoinRoot (poly c n) →+* K[X] :=
  AdjoinRoot.lift (aeval (paramX c)).toRingHom (X ^ n) <| by
    simp [poly_def, paramX, eval₂_pow, hn.neg_pow, ← pow_mul, mul_comm]

variable (c : K) {n : ℕ}

@[simp]
theorem param_of (hn : Odd n) (r : K[X]) : param c hn (AdjoinRoot.of _ r) = r.comp (paramX c) := by
  simp [param, comp_eq_aeval]

@[simp]
theorem param_root (hn : Odd n) : param c hn (AdjoinRoot.root _) = X ^ n := by
  simp [param]

/-- Every element of `K[x, y]/(y² + (x + c)ⁿ)` is `r₀(x) + r₁(x) y`. -/
theorem exists_eq_add_mul_root (a : AdjoinRoot (poly c n)) :
    ∃ r₀ r₁ : K[X], a = AdjoinRoot.of _ r₀ + AdjoinRoot.of _ r₁ * AdjoinRoot.root _ := by
  obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective a
  cases subsingleton_or_nontrivial K
  · exact ⟨0, 0, by rw [Subsingleton.elim g 0]; simp⟩
  have hd : (g %ₘ poly c n).degree ≤ 1 := by
    have := degree_modByMonic_lt g (monic_poly c n)
    rw [degree_poly] at this
    exact Order.le_of_lt_succ this
  refine ⟨(g %ₘ poly c n).coeff 0, (g %ₘ poly c n).coeff 1, ?_⟩
  rw [← AdjoinRoot.mk_leftInverse (monic_poly c n) (AdjoinRoot.mk _ g),
    AdjoinRoot.modByMonicHom_mk]
  conv_lhs => rw [eq_X_add_C_of_degree_le_one hd]
  simp [add_comm]

/-- The parametrization `s ↦ (-s² - c, sⁿ)` is injective for odd `n`, over any commutative
ring `K`. -/
theorem param_injective (hn : Odd n) : Function.Injective (param c hn) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨r₀, r₁, rfl⟩ := exists_eq_add_mul_root c a
  simp only [map_add, map_mul, param_of, param_root] at ha
  have h₀ : r₀.comp (paramX c) = 0 := by
    ext k
    rcases Nat.even_or_odd k with hk | hk
    · simpa [coeff_comp_paramX_mul_X_pow_of_even r₁ c hn hk] using congrArg (fun f ↦ f.coeff k) ha
    · simpa using coeff_comp_paramX_of_odd r₀ c hk
  have h₁ : r₁.comp (paramX c) = 0 := by
    rw [h₀, zero_add] at ha
    exact (monic_X_pow n).mul_left_eq_zero_iff.mp ha
  simp [eq_zero_of_comp_paramX_eq_zero h₀, eq_zero_of_comp_paramX_eq_zero h₁]

/-- The coordinate ring of `y² + (x + c)ⁿ = 0` is a domain for odd `n`, over a domain
`K`. -/
theorem isDomain [IsDomain K] (hn : Odd n) : IsDomain (AdjoinRoot (poly c n)) :=
  (param_injective c hn).isDomain _

/-- The image of the parametrization has no `s¹` term once `n ≥ 3`. -/
theorem coeff_param_one (hn : Odd n) (h3 : 3 ≤ n) (a : AdjoinRoot (poly c n)) :
    (param c hn a).coeff 1 = 0 := by
  obtain ⟨r₀, r₁, rfl⟩ := exists_eq_add_mul_root c a
  simp only [map_add, map_mul, param_of, param_root, coeff_add, coeff_mul_X_pow',
    coeff_comp_paramX_of_odd r₀ c odd_one]
  simp [show ¬ n ≤ 1 by omega]

/-- In `K[x, y]/(y² + (x + c)ⁿ)`, `y² = -(x + c)ⁿ`. -/
theorem root_sq : AdjoinRoot.root (poly c n) ^ 2 = -AdjoinRoot.of _ (X + C c) ^ n := by
  have h := AdjoinRoot.eval₂_root (poly c n)
  simp only [poly_def, eval₂_add, eval₂_X_pow, eval₂_C] at h
  rw [← map_pow]
  exact eq_neg_of_add_eq_zero_left h

/-- Over a domain `K`, the coordinate ring of `y² + (x + c)ⁿ = 0` is not integrally closed for
odd `n ≥ 3`: the element `y / (x + c)^((n-1)/2)` of its fraction field is a square root of
`-(x + c)`. -/
theorem not_isIntegrallyClosed [IsDomain K] (hn : Odd n) (h3 : 3 ≤ n) :
    ¬ IsIntegrallyClosed (AdjoinRoot (poly c n)) := by
  intro hic
  have := isDomain c hn
  -- `have` rather than `obtain`, so that `hn` stays available for `param c hn`.
  have ⟨m, hm⟩ := hn
  set u := AdjoinRoot.of (poly c n) (X + C c)
  let F := FractionRing (AdjoinRoot (poly c n))
  have hu : u ≠ 0 := fun h ↦ by
    have := congrArg (fun z ↦ (param c hn z).coeff 2) h
    simp [u] at this
  have hu' : algebraMap _ F u ≠ 0 := by
    rwa [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective _ F)]
  have hint : IsIntegral (AdjoinRoot (poly c n))
      (algebraMap _ F (AdjoinRoot.root (poly c n)) / algebraMap _ F u ^ m) := by
    refine ⟨X ^ 2 + C u, monic_X_pow_add_C _ two_ne_zero, ?_⟩
    simp only [eval₂_add, eval₂_X_pow, eval₂_C, div_pow, ← map_pow, root_sq]
    simp only [map_neg, map_pow, hm]
    field_simp
    ring
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  have hay : a * u ^ m = AdjoinRoot.root _ :=
    IsFractionRing.injective _ F <| by
      rw [map_mul, ha, map_pow, div_mul_cancel₀ _ (pow_ne_zero _ hu')]
  have := congrArg (fun z ↦ (param c hn z).coeff n) hay
  simp only [u, map_mul, map_pow, param_of, param_root, X_add_C_comp_paramX] at this
  simp only [mul_pow, ← C_pow, ← pow_mul, mul_left_comm _ (C _), coeff_C_mul] at this
  simp [hm, coeff_mul_X_pow', coeff_param_one c hn h3] at this

/-- The curve `y² + (x + c)ⁿ = 0` over a domain is not normal for odd `n ≥ 3`. -/
theorem not_isNormalScheme [IsDomain K] (hn : Odd n) (h3 : 3 ≤ n) :
    ¬ IsNormalScheme (Spec (.of (AdjoinRoot (poly c n)))) := by
  have := isDomain c hn
  rw [isNormalScheme_Spec_iff]
  exact not_isIntegrallyClosed c hn h3

/-- Over a domain `K` of odd prime characteristic `p` in which `t` is a `p`-th power, as it is over
`k' = k(t^{1/p})` for `k = 𝔽_p(t)`, the curve `x^p + y² + t = 0` is not normal. -/
theorem not_isNormalScheme_of_charP [IsDomain K] (p : ℕ) [hp : Fact p.Prime] [CharP K p]
    (hp2 : p ≠ 2) {t : K} (ht : ∃ c, c ^ p = t) :
    ¬ IsNormalScheme (Spec (.of (AdjoinRoot (X ^ 2 + C (X ^ p + C t) : K[X][X])))) := by
  obtain ⟨c, rfl⟩ := ht
  have h : (X ^ 2 + C (X ^ p + C (c ^ p)) : K[X][X]) = poly c p := by
    simp [poly_def, add_pow_char, C_pow]
  rw [h]
  exact not_isNormalScheme c (hp.out.odd_of_ne_two hp2) (by have := hp.out.two_le; omega)

end TauCeti.CuspidalCurveExample
