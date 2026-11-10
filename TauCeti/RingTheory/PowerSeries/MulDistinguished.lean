/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Monoid.MulUnit
public import TauCeti.RingTheory.PowerSeries.GaussNorm
import TauCeti.Analysis.Normed.Ring.MulUnit

/-!
# Multiplicatively distinguished power series

A power series `g` is *multiplicatively distinguished of degree `s`* at the radius `c` when it is
distinguished of degree `s` in the sense of `TauCeti.PowerSeries.IsDistinguished` and its
coefficient in degree `s` is a multiplicative unit (`TauCeti.IsNormMulUnit`): an invertible
element by which left multiplication scales every norm exactly.

This is the divisor hypothesis of Weierstrass division and preparation over an ultrametric
Banach ring whose norm need not be multiplicative, such as a coefficient ring with nilpotents.
Its basic consequence is the multiplication estimate: multiplying a restricted series `q` by such
a `g` on the left loses no norm, `‖g * q‖ = ‖g‖ * ‖q‖`, and if `q` is distinguished of degree
`k` then `g * q` is distinguished of degree `s + k`. No multiplicativity of the norm of `R` is
assumed. When the norm of `R` is multiplicative, the extra condition says only that the
distinguished coefficient is a unit.

Norm-preserving coefficient homomorphisms preserve distinguishedness, lowest dominant degrees
and multiplicative distinguishedness, so these divisor hypotheses survive isometric coefficient
extension.

## Main definitions

* `TauCeti.PowerSeries.IsMulDistinguished`: `g` is distinguished of degree `s` at `c`, and its
  coefficient in degree `s` is a multiplicative unit.

## Main results

* `PowerSeries.gaussNorm_map_of_norm_eq`: a norm-preserving coefficient homomorphism
  preserves the Gauss norm.
* `TauCeti.PowerSeries.isMulDistinguished_iff_isUnit`: over a ring with multiplicative norm, a
  series is multiplicatively distinguished exactly when it is distinguished with invertible
  distinguished coefficient.
* `TauCeti.PowerSeries.IsMulDistinguished.isDistinguished_mul`: left multiplication by a
  multiplicatively distinguished series of degree `s` raises distinguished degrees by `s`.
* `TauCeti.PowerSeries.IsMulDistinguished.gaussNorm_mul`: left multiplication by a
  multiplicatively distinguished series multiplies the Gauss norm of a restricted series by the
  Gauss norm of the divisor.
* `TauCeti.PowerSeries.gaussNorm_X_sub_C_mul`: in particular `‖(X - a) * q‖ = c * ‖q‖` at the
  radius `c` when `‖a‖ ≤ c`.
* `TauCeti.PowerSeries.isMulDistinguished_monomial` and
  `TauCeti.PowerSeries.isMulDistinguished_X_sub_C`: monomials with multiplicative-unit
  coefficient, and `X - b` for `b` in the closed disc of radius `c`.
* `TauCeti.PowerSeries.isMulDistinguished_iff_gaussNorm_eq`: a monic polynomial of degree `s` is
  multiplicatively distinguished of degree `s` at `c` exactly when its Gauss norm is `c ^ s`.

## References

* F. Martin, *Overconvergent subanalytic subsets in the framework of Berkovich spaces*,
  J. Eur. Math. Soc. 18 (2016), Definitions 1.20 and 1.24, Lemma 1.26 and Corollary 1.28.
-/

public section

namespace TauCeti.PowerSeries

section SeminormedRing

variable {R : Type*} [SeminormedRing R] {c : ℝ} {s k : ℕ} {g q : PowerSeries R}

variable {S : Type*} [SeminormedRing S] in
/-- A norm-preserving coefficient homomorphism preserves the Gauss norm at every radius. -/
theorem _root_.PowerSeries.gaussNorm_map_of_norm_eq (φ : R →+* S) (hφ : ∀ a, ‖φ a‖ = ‖a‖)
    (g : PowerSeries R) (c : ℝ) : (PowerSeries.map φ g).gaussNorm norm c = g.gaussNorm norm c := by
  simp only [PowerSeries.gaussNorm_eq, PowerSeries.coeff_map, hφ]

variable {S : Type*} [SeminormedRing S] in
/-- A norm-preserving coefficient homomorphism preserves distinguishedness, with the same
radius and degree. Neither completeness nor surjectivity is required. -/
theorem IsDistinguished.map (hf : IsDistinguished c s g) (φ : R →+* S)
    (hφ : ∀ a, ‖φ a‖ = ‖a‖) : IsDistinguished c s (PowerSeries.map φ g) := by
  have hn := g.gaussNorm_map_of_norm_eq φ hφ c
  exact ⟨by simpa only [PowerSeries.coeff_map, hφ, hn] using hf.norm_coeff_mul_pow_eq,
    fun n hn' ↦ by simpa only [PowerSeries.coeff_map, hφ, hn] using
      hf.norm_coeff_mul_pow_lt n hn'⟩

variable {S : Type*} [SeminormedRing S] in
/-- A norm-preserving coefficient homomorphism preserves the lowest dominant degree, at the same
radius. Neither completeness nor surjectivity is required. -/
theorem IsLowestDominant.map (hf : IsLowestDominant c s g) (φ : R →+* S)
    (hφ : ∀ a, ‖φ a‖ = ‖a‖) : IsLowestDominant c s (PowerSeries.map φ g) := by
  have hn := g.gaussNorm_map_of_norm_eq φ hφ c
  exact ⟨hn ▸ hf.gaussNorm_pos,
    by simpa only [PowerSeries.coeff_map, hφ, hn] using hf.norm_coeff_mul_pow_eq,
    fun n hn' ↦ by simpa only [PowerSeries.coeff_map, hφ, hn] using
      hf.norm_coeff_mul_pow_lt n hn'⟩

variable (c s g) in
/-- `g` is **multiplicatively distinguished of degree `s`** at the radius `c` when it is
distinguished of degree `s` at `c` and its coefficient in degree `s` is a multiplicative unit.

The first condition says that the Gauss norm of `g` at `c` is attained in degree `s` and that
every later weighted coefficient norm is strictly smaller; earlier coefficients may tie. The
second makes left multiplication by `g` lose no norm, without any multiplicativity assumption on
the norm of the coefficient ring. -/
structure IsMulDistinguished : Prop extends IsDistinguished c s g where
  /-- The coefficient in the distinguished degree is a multiplicative unit. -/
  isNormMulUnit_coeff : IsNormMulUnit (g.coeff s)

/-- A series is multiplicatively distinguished exactly when it is distinguished and its
coefficient in the distinguished degree is a multiplicative unit. -/
theorem isMulDistinguished_iff :
    IsMulDistinguished c s g ↔ IsDistinguished c s g ∧ IsNormMulUnit (g.coeff s) :=
  ⟨fun h ↦ ⟨h.toIsDistinguished, h.isNormMulUnit_coeff⟩, fun h ↦ ⟨h.1, h.2⟩⟩

/-- Over a ring with multiplicative norm, a series is multiplicatively distinguished exactly when
it is distinguished and its coefficient in the distinguished degree is a unit. -/
theorem isMulDistinguished_iff_isUnit [NormMulClass R] :
    IsMulDistinguished c s g ↔ IsDistinguished c s g ∧ IsUnit (g.coeff s) := by
  rw [isMulDistinguished_iff, isNormMulUnit_iff_isUnit]

/-- The coefficient ring of a multiplicatively distinguished series is nontrivial. -/
theorem IsMulDistinguished.nontrivial (hg : IsMulDistinguished c s g) : Nontrivial R :=
  nontrivial_of_ne _ _ hg.coeff_ne_zero

/-- The truncation of a multiplicatively distinguished series just past its distinguished degree
is again multiplicatively distinguished of that degree. -/
theorem IsMulDistinguished.trunc (hg : IsMulDistinguished c s g) :
    IsMulDistinguished c s ((g.trunc (s + 1) : Polynomial R) : PowerSeries R) := by
  refine ⟨hg.toIsDistinguished.trunc, ?_⟩
  rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc, ite_eq_left (Nat.lt_succ_self s)]
  exact hg.isNormMulUnit_coeff

/-- A linear polynomial `X - b` whose root lies in the closed disc of radius `c > 0` is
multiplicatively distinguished of degree `1` at `c`, over a norm-one ring. The constant term may
have the same weighted norm as the leading one. -/
theorem isMulDistinguished_X_sub_C [NormOneClass R] (hc : 0 < c) {b : R} (hb : ‖b‖ ≤ c) :
    IsMulDistinguished c 1 (PowerSeries.X - PowerSeries.C b) :=
  ⟨isDistinguished_X_sub_C hc hb, by simp⟩

variable [IsUltrametricDist R]

/-- **Distinguished degrees under multiplication by a multiplicatively distinguished series.**
If `g` is multiplicatively distinguished of degree `s` and `q` is distinguished of degree `k` at
a positive radius, then `g * q` is distinguished of degree `s + k`. -/
theorem IsMulDistinguished.isDistinguished_mul (hg : IsMulDistinguished c s g)
    (hq : IsDistinguished c k q) (hc : 0 < c) : IsDistinguished c (s + k) (g * q) :=
  hg.toIsDistinguished.mul hq hc (hg.isNormMulUnit_coeff.norm_mul _)

end SeminormedRing

section SeminormedCommRing

variable {R : Type*} [SeminormedCommRing R] {c : ℝ} {s : ℕ} {g : PowerSeries R}

/-- Right multiplication by the distinguished coefficient scales norms exactly. -/
theorem IsMulDistinguished.norm_mul_coeff (hg : IsMulDistinguished c s g) (x : R) :
    ‖x * g.coeff s‖ = ‖x‖ * ‖g.coeff s‖ := by
  rw [mul_comm x, hg.isNormMulUnit_coeff.norm_mul, mul_comm]

end SeminormedCommRing

section NormedRing

variable {R : Type*} [NormedRing R] {c : ℝ} {s : ℕ} {g q : PowerSeries R}

/-- The norm of the coefficient ring of a multiplicatively distinguished series takes the value
`1` at `1`, since the distinguished coefficient is a nonzero multiplicative unit. -/
theorem IsMulDistinguished.normOneClass (hg : IsMulDistinguished c s g) : NormOneClass R :=
  have := hg.nontrivial
  ⟨hg.isNormMulUnit_coeff.norm_one⟩

variable {S : Type*} [SeminormedRing S] in
/-- A norm-preserving coefficient homomorphism preserves multiplicative distinguishedness,
even without a multiplicative coefficient norm or a surjectivity hypothesis. -/
theorem IsMulDistinguished.map (hf : IsMulDistinguished c s g) (φ : R →+* S)
    (hφ : ∀ a, ‖φ a‖ = ‖a‖) : IsMulDistinguished c s (PowerSeries.map φ g) := by
  have : NormOneClass R := hf.normOneClass
  refine ⟨hf.toIsDistinguished.map φ hφ, ?_⟩
  rw [PowerSeries.coeff_map]
  exact hf.isNormMulUnit_coeff.map φ.toMonoidHom hφ

/-- A monomial whose coefficient is a multiplicative unit is multiplicatively distinguished of
its degree at a positive radius, over a nontrivial ring. -/
theorem isMulDistinguished_monomial [Nontrivial R] (hc : 0 < c) {a : R} (ha : IsNormMulUnit a)
    (n : ℕ) : IsMulDistinguished c n (PowerSeries.monomial n a) :=
  ⟨isDistinguished_monomial hc ha.isUnit.ne_zero n, by
    rwa [PowerSeries.coeff_monomial_same]⟩

/-- **Weierstrass polynomials at a radius.** A monic polynomial of degree `s` is
multiplicatively distinguished of degree `s` at a positive radius `c` exactly when its Gauss
norm at `c` is `c ^ s`, the weighted norm of its leading term. This is the normalisation of the
polynomial factor in Weierstrass preparation. Lower coefficients may tie with the leading one, as
for `X - 1` at the radius `1`. -/
theorem isMulDistinguished_iff_gaussNorm_eq (hc : 0 < c) {p : Polynomial R}
    (hp : p.IsMonicOfDegree s) :
    IsMulDistinguished c s (p : PowerSeries R) ↔ (p : PowerSeries R).gaussNorm norm c = c ^ s := by
  have hs := hp.coeff_coe_self
  have hb := hasGaussNorm_of_isRestricted (isRestricted_polynomial (c := c) p)
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have := h.normOneClass
    rw [← h.norm_coeff_mul_pow_eq, hs, norm_one, one_mul]
  · have hcs : 0 < c ^ s := pow_pos hc s
    have hle : ‖(1 : R)‖ * c ^ s ≤ c ^ s := by
      simpa [hs, h] using PowerSeries.le_gaussNorm norm c (p : PowerSeries R) hb s
    have hnt : Nontrivial R := by
      refine not_subsingleton_iff_nontrivial.mp fun hsub ↦ ?_
      have h0 : (p : PowerSeries R).gaussNorm norm c = 0 := by
        simp [PowerSeries.gaussNorm_eq, Subsingleton.elim _ (0 : R)]
      exact hcs.ne (h0.symm.trans h)
    have hpos : 0 < ‖(1 : R)‖ := norm_pos_iff.2 one_ne_zero
    have hmul : ‖(1 : R)‖ ≤ ‖(1 : R)‖ * ‖(1 : R)‖ := by simpa using norm_mul_le (1 : R) 1
    have : NormOneClass R :=
      ⟨le_antisymm ((mul_le_iff_le_one_left hcs).1 hle) (by nlinarith)⟩
    refine ⟨isDistinguished_of_isMonicOfDegree hc hp fun k _ ↦ ?_,
      by rw [hs]; exact isNormMulUnit_one⟩
    rw [← h, ← Polynomial.coeff_coe]
    exact PowerSeries.le_gaussNorm norm c _ hb k

variable [IsUltrametricDist R]

/-- **The multiplication estimate.** Left multiplication by a multiplicatively distinguished
series multiplies the Gauss norm of a restricted series by the Gauss norm of the divisor, at
a positive radius:

```text
‖g * q‖ = ‖g‖ * ‖q‖.
```

No multiplicativity of the norm of the coefficient ring is assumed. -/
theorem IsMulDistinguished.gaussNorm_mul (hg : IsMulDistinguished c s g) (hc : 0 < c)
    (hq : q.IsRestricted c) :
    (g * q).gaussNorm norm c = g.gaussNorm norm c * q.gaussNorm norm c := by
  rcases eq_or_ne q 0 with rfl | hq0
  · simp [PowerSeries.gaussNorm_zero norm c (norm_zero : ‖(0 : R)‖ = 0)]
  obtain ⟨k, hk⟩ := exists_isDistinguished hc hq hq0
  exact hg.toIsDistinguished.gaussNorm_mul hk hc (hg.isNormMulUnit_coeff.norm_mul _)

/-- Multiplying a restricted series by `X - a`, for `a` in the closed disc of radius `c > 0`,
multiplies its Gauss norm at `c` by `c`. No normalisation `‖1‖ = 1` of the coefficient ring is
needed. -/
theorem gaussNorm_X_sub_C_mul (hc : 0 < c) {a : R} (ha : ‖a‖ ≤ c)
    (hq : q.IsRestricted c) :
    ((PowerSeries.X - PowerSeries.C a) * q).gaussNorm norm c = c * q.gaussNorm norm c := by
  rcases eq_or_ne q 0 with rfl | hq0
  · simp [PowerSeries.gaussNorm_zero norm c (norm_zero : ‖(0 : R)‖ = 0)]
  obtain ⟨k, hk⟩ := exists_isDistinguished hc hq hq0
  have hqle (m : ℕ) : ‖q.coeff m‖ * c ^ m ≤ q.gaussNorm norm c :=
    PowerSeries.le_gaussNorm norm c q hk.hasGaussNorm m
  -- the coefficients of the product
  have hcoeff (m : ℕ) : ((PowerSeries.X - PowerSeries.C a) * q).coeff (m + 1) =
      q.coeff m - a * q.coeff (m + 1) := by
    rw [sub_mul, map_sub, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_C_mul]
  have hcoeff0 : ((PowerSeries.X - PowerSeries.C a) * q).coeff 0 = -(a * q.coeff 0) := by
    rw [sub_mul, map_sub, PowerSeries.coeff_zero_X_mul, PowerSeries.coeff_C_mul, zero_sub]
  -- the cross term is dominated by `c` times the weighted norm one degree up
  have hcross (m : ℕ) : ‖a * q.coeff m‖ * c ^ m ≤ c * (‖q.coeff m‖ * c ^ m) := by
    calc ‖a * q.coeff m‖ * c ^ m ≤ (‖a‖ * ‖q.coeff m‖) * c ^ m :=
          mul_le_mul_of_nonneg_right (norm_mul_le _ _) (pow_nonneg hc.le m)
      _ ≤ (c * ‖q.coeff m‖) * c ^ m :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ha (norm_nonneg _))
            (pow_nonneg hc.le m)
      _ = c * (‖q.coeff m‖ * c ^ m) := by ring
  have hupper (m : ℕ) : ‖((PowerSeries.X - PowerSeries.C a) * q).coeff m‖ * c ^ m ≤
      c * q.gaussNorm norm c := by
    rcases m with _ | m
    · rw [hcoeff0, norm_neg]
      exact (hcross 0).trans (mul_le_mul_of_nonneg_left (hqle 0) hc.le)
    · rw [hcoeff]
      have hsub : ‖q.coeff m - a * q.coeff (m + 1)‖ ≤ max ‖q.coeff m‖ ‖a * q.coeff (m + 1)‖ := by
        simpa [sub_eq_add_neg] using IsUltrametricDist.norm_add_le_max (q.coeff m)
          (-(a * q.coeff (m + 1)))
      refine (mul_le_mul_of_nonneg_right hsub (pow_nonneg hc.le (m + 1))).trans ?_
      rw [max_mul_of_nonneg _ _ (by positivity)]
      refine max_le ?_ ((hcross (m + 1)).trans (mul_le_mul_of_nonneg_left (hqle _) hc.le))
      calc ‖q.coeff m‖ * c ^ (m + 1) = c * (‖q.coeff m‖ * c ^ m) := by ring
        _ ≤ c * q.gaussNorm norm c := mul_le_mul_of_nonneg_left (hqle m) hc.le
  have hlower : c * q.gaussNorm norm c ≤
      ‖((PowerSeries.X - PowerSeries.C a) * q).coeff (k + 1)‖ * c ^ (k + 1) := by
    have hlt : ‖a * q.coeff (k + 1)‖ * c ^ (k + 1) < ‖q.coeff k‖ * c ^ (k + 1) := by
      calc ‖a * q.coeff (k + 1)‖ * c ^ (k + 1) ≤ c * (‖q.coeff (k + 1)‖ * c ^ (k + 1)) :=
            hcross _
        _ < c * q.gaussNorm norm c :=
            mul_lt_mul_of_pos_left (hk.norm_coeff_mul_pow_lt _ (Nat.lt_succ_self k)) hc
        _ = ‖q.coeff k‖ * c ^ (k + 1) := by
            rw [← hk.norm_coeff_mul_pow_eq, pow_succ]; ring
    have hq' : ‖q.coeff k‖ ≤ ‖((PowerSeries.X - PowerSeries.C a) * q).coeff (k + 1)‖ := by
      by_contra hcon
      rw [not_le, hcoeff] at hcon
      have hle := IsUltrametricDist.norm_add_le_max (q.coeff k - a * q.coeff (k + 1))
        (a * q.coeff (k + 1))
      rw [sub_add_cancel] at hle
      have hlt' : ‖a * q.coeff (k + 1)‖ < ‖q.coeff k‖ :=
        lt_of_mul_lt_mul_right hlt (pow_nonneg hc.le _)
      exact absurd hle (not_le.mpr (max_lt hcon hlt'))
    calc c * q.gaussNorm norm c = ‖q.coeff k‖ * c ^ (k + 1) := by
          rw [← hk.norm_coeff_mul_pow_eq, pow_succ]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hq' (pow_nonneg hc.le _)
  have hb : ((PowerSeries.X - PowerSeries.C a) * q).HasGaussNorm norm c :=
    ⟨_, Set.forall_mem_range.mpr hupper⟩
  exact le_antisymm ((PowerSeries.gaussNorm_eq _ _ _).trans_le (ciSup_le hupper))
    (hlower.trans (PowerSeries.le_gaussNorm norm c _ hb _))

end NormedRing

end TauCeti.PowerSeries
