/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Iterate
public import TauCeti.RingTheory.PowerSeries.Weierstrass.Division

/-!
# Weierstrass division in several variables over Banach rings

Let `R` be an ultrametric normed commutative ring and let `c : Option σ → ℝ` be positive
polyradii. Separating the variable `X none` identifies restricted series in `Option σ` at `c`
with univariate series restricted at the radius `c none` whose coefficients are restricted series
in `σ` at the polyradii `c ∘ some` (`TauCeti.Huber.restrictedOptionEquiv`), and this
identification preserves the Gauss norms. Weierstrass division by a series `g` in the separated
variable is one-variable Weierstrass division over that coefficient ring.

The divisor hypothesis is that the iterated series of `g` is multiplicatively distinguished of
degree `s` at the radius `c none` (`TauCeti.PowerSeries.IsMulDistinguished`): its Gauss norm is
attained in degree `s`, every later weighted coefficient norm `‖aₙ‖ * c none ^ n` is strictly
smaller (earlier ones may tie), and the coefficient in degree `s`, a restricted series in the
remaining variables, is a multiplicative unit of the ring of such series. A remainder is a series
of degree less than `s` in `X none`: every monomial in which `X none` occurs with exponent at
least `s` has coefficient zero. Its coefficients in the
remaining variables are arbitrary restricted series.

Over a complete coefficient ring every restricted series `f` then has a unique decomposition
`f = g * q + r` with `q` restricted and `r` a remainder, and

```text
‖g * q + r‖ = max (‖g‖ * ‖q‖) ‖r‖
```

for the Gauss norms at `c`, so that `‖q‖ ≤ ‖f‖ / ‖g‖` and `‖r‖ ≤ ‖f‖`. The norm of `R` need not
be multiplicative, and `R` may have nilpotents.

## Main results

* `TauCeti.MvPowerSeries.norm_mul_add_eq_max_of_isMulDistinguished`: the norm identity.
* `TauCeti.MvPowerSeries.eq_and_eq_of_mul_add_eq_mul_add_of_isMulDistinguished`: the quotient and
  the remainder are unique.
* `TauCeti.MvPowerSeries.exists_mul_add_eq_of_isMulDistinguished` and
  `TauCeti.MvPowerSeries.existsUnique_mul_add_eq_of_isMulDistinguished`: over a complete
  ultrametric normed commutative ring, every restricted series has a unique Weierstrass division,
  with quotient and remainder bounded by the dividend.

## References

* F. Martin, *Overconvergent subanalytic subsets in the framework of Berkovich spaces*,
  J. Eur. Math. Soc. 18 (2016), Proposition 1.27 and the remark following Corollary 1.28, for
  division by a multiplicatively distinguished series over a Banach ring and its several-variable
  form.
* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §5.2.1, Theorem 2, for the unit-radius
  case over a complete nonarchimedean field.
-/

public section

namespace TauCeti.MvPowerSeries

open _root_.MvPowerSeries
open TauCeti.Huber (restrictedOptionEquiv forall_coeff_restrictedOptionEquiv_eq_zero_iff
  norm_restrictedOptionEquiv)

variable {σ R : Type*} [NormedCommRing R] [IsUltrametricDist R] {c : Option σ → ℝ}
  [∀ i, Fact (0 < c i)] {s : ℕ}

local notation "Inner" => IsRestricted.subring (R := R) (fun i : σ ↦ c (some i))
local notation "Flat" => IsRestricted.subring (R := R) c

/-- The underlying series of the iterated series of `g * q + r`. -/
private theorem coe_restrictedOptionEquiv_mul_add (g q r : Flat) :
    (restrictedOptionEquiv (g * q + r) : PowerSeries Inner) =
      (restrictedOptionEquiv g : PowerSeries Inner) * (restrictedOptionEquiv q) +
        (restrictedOptionEquiv r) := by
  rw [map_add, map_mul, Subring.coe_add, Subring.coe_mul]

/-- A series whose iterated series is multiplicatively distinguished has positive Gauss norm. -/
theorem norm_pos_of_isMulDistinguished {g : Flat}
    (hg : PowerSeries.IsMulDistinguished (c none) s
      (restrictedOptionEquiv g : PowerSeries Inner)) :
    0 < ‖g‖ := by
  rw [← norm_restrictedOptionEquiv, PowerSeries.norm_eq_gaussNorm]
  exact hg.gaussNorm_pos

/-- **The Weierstrass division estimate in several variables.** Over an ultrametric normed
commutative ring, let the iterated series of `g` in the separated variable `X none` be
multiplicatively distinguished of degree `s`. If `r` has degree less than `s` in `X none`, then

```text
‖g * q + r‖ = max (‖g‖ * ‖q‖) ‖r‖
```

for the Gauss norms at the polyradii `c`. The norm of the coefficient ring need not be
multiplicative. -/
theorem norm_mul_add_eq_max_of_isMulDistinguished {g : Flat}
    (hg : PowerSeries.IsMulDistinguished (c none) s
      (restrictedOptionEquiv g : PowerSeries Inner))
    (q : Flat) {r : Flat}
    (hr : ∀ t : Option σ →₀ ℕ, s ≤ t none → coeff t (r : MvPowerSeries (Option σ) R) = 0) :
    ‖g * q + r‖ = max (‖g‖ * ‖q‖) ‖r‖ := by
  simp only [← norm_restrictedOptionEquiv (f := g * q + r), ← norm_restrictedOptionEquiv (f := g),
    ← norm_restrictedOptionEquiv (f := q), ← norm_restrictedOptionEquiv (f := r),
    PowerSeries.norm_eq_gaussNorm, coe_restrictedOptionEquiv_mul_add]
  exact hg.gaussNorm_mul_add_eq_max Fact.out (restrictedOptionEquiv q).2
    ((forall_coeff_restrictedOptionEquiv_eq_zero_iff _ s).mpr hr)

/-- **Uniqueness in several-variable Weierstrass division.** Over an ultrametric normed
commutative ring, let the iterated series of `g` in the separated variable `X none` be
multiplicatively distinguished of degree `s`. A restricted series has at most one decomposition
`g * q + r` with `q` restricted and `r` of degree less than `s` in `X none`. -/
theorem eq_and_eq_of_mul_add_eq_mul_add_of_isMulDistinguished {g : Flat}
    (hg : PowerSeries.IsMulDistinguished (c none) s
      (restrictedOptionEquiv g : PowerSeries Inner))
    {q q' r r' : Flat}
    (hr : ∀ t : Option σ →₀ ℕ, s ≤ t none → coeff t (r : MvPowerSeries (Option σ) R) = 0)
    (hr' : ∀ t : Option σ →₀ ℕ, s ≤ t none → coeff t (r' : MvPowerSeries (Option σ) R) = 0)
    (h : g * q + r = g * q' + r') :
    q = q' ∧ r = r' := by
  have h' := congrArg (fun x : Flat ↦ (restrictedOptionEquiv x : PowerSeries Inner)) h
  simp only [coe_restrictedOptionEquiv_mul_add] at h'
  obtain ⟨hq, hr⟩ := hg.eq_and_eq_of_mul_add_eq_mul_add Fact.out (restrictedOptionEquiv q).2
    (restrictedOptionEquiv q').2 ((forall_coeff_restrictedOptionEquiv_eq_zero_iff _ s).mpr hr)
    ((forall_coeff_restrictedOptionEquiv_eq_zero_iff _ s).mpr hr') h'
  exact ⟨restrictedOptionEquiv.injective (Subtype.ext hq),
    restrictedOptionEquiv.injective (Subtype.ext hr)⟩

/-- **Weierstrass division in several variables over a Banach ring** (Martin, Proposition 1.27,
iterated). Over a complete ultrametric normed commutative ring, let the iterated series of a
restricted series `g` in the separated variable `X none` be multiplicatively distinguished of
degree `s` at the radius `c none`. Then every restricted series `f` decomposes as

```text
f = g * q + r,    q restricted,    r of degree less than s in X none,
```

with `‖q‖ ≤ ‖f‖ / ‖g‖` and `‖r‖ ≤ ‖f‖` for the Gauss norms at `c`. The norm of the coefficient ring
need not be multiplicative. The decomposition is unique by
`TauCeti.MvPowerSeries.eq_and_eq_of_mul_add_eq_mul_add_of_isMulDistinguished`. -/
theorem exists_mul_add_eq_of_isMulDistinguished [CompleteSpace R] {g : Flat}
    (hg : PowerSeries.IsMulDistinguished (c none) s
      (restrictedOptionEquiv g : PowerSeries Inner))
    (f : Flat) :
    ∃ q r : Flat,
      (∀ t : Option σ →₀ ℕ, s ≤ t none → coeff t (r : MvPowerSeries (Option σ) R) = 0) ∧
      g * q + r = f ∧ ‖q‖ ≤ ‖f‖ / ‖g‖ ∧ ‖r‖ ≤ ‖f‖ := by
  obtain ⟨q', r', hq', hr', hqr⟩ :=
    hg.exists_mul_add_eq Fact.out (restrictedOptionEquiv g).2 (restrictedOptionEquiv f).2
  set q : Flat := restrictedOptionEquiv.symm ⟨q', hq'⟩
  set r : Flat := restrictedOptionEquiv.symm
    ⟨r', TauCeti.PowerSeries.isRestricted_of_forall_coeff_eq_zero hr'⟩
  have hr : ∀ t : Option σ →₀ ℕ, s ≤ t none → coeff t (r : MvPowerSeries (Option σ) R) = 0 :=
    (forall_coeff_restrictedOptionEquiv_eq_zero_iff r s).mp (by simpa [r] using hr')
  have hf : g * q + r = f := restrictedOptionEquiv.injective <| Subtype.ext <| by
    rw [coe_restrictedOptionEquiv_mul_add]
    simpa [q, r] using hqr
  have hnorm := norm_mul_add_eq_max_of_isMulDistinguished hg q hr
  rw [hf] at hnorm
  refine ⟨q, r, hr, hf, ?_, hnorm ▸ le_max_right _ _⟩
  rw [le_div_iff₀ (norm_pos_of_isMulDistinguished hg), mul_comm, hnorm]
  exact le_max_left _ _

/-- **Weierstrass division in several variables over a Banach ring**, in its unique-existence
form: over a complete ultrametric normed commutative ring, if the iterated series of `g` in the
separated variable `X none` is multiplicatively distinguished of degree `s`, every restricted
series `f` is `g * q + r` for exactly one pair of restricted series `q` and `r` with `r` of
degree less than `s` in `X none`. -/
theorem existsUnique_mul_add_eq_of_isMulDistinguished [CompleteSpace R] {g : Flat}
    (hg : PowerSeries.IsMulDistinguished (c none) s
      (restrictedOptionEquiv g : PowerSeries Inner))
    (f : Flat) :
    ∃! p : Flat × Flat,
      (∀ t : Option σ →₀ ℕ, s ≤ t none → coeff t (p.2 : MvPowerSeries (Option σ) R) = 0) ∧
      g * p.1 + p.2 = f := by
  obtain ⟨q, r, hr, hqr, -⟩ := exists_mul_add_eq_of_isMulDistinguished hg f
  refine ⟨(q, r), ⟨hr, hqr⟩, fun p ⟨hp, hpf⟩ ↦ ?_⟩
  obtain ⟨e1, e2⟩ :=
    eq_and_eq_of_mul_add_eq_mul_add_of_isMulDistinguished hg hp hr (hpf.trans hqr.symm)
  exact Prod.ext e1 e2

end TauCeti.MvPowerSeries
