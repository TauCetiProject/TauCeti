/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.TateAlgebra
public import TauCeti.RingTheory.PowerSeries.Weierstrass.Division

/-!
# The Weierstrass quotient and remainder as linear maps

Let `R` be a complete ultrametric normed commutative ring, `c > 0` a radius, and `g` a series
restricted at `c` which is multiplicatively distinguished of degree `s`
(`TauCeti.PowerSeries.IsMulDistinguished`). Weierstrass division by `g`
(`TauCeti.PowerSeries.IsMulDistinguished.existsUnique_mul_add_eq`) writes every series `f`
restricted at `c` uniquely as

```text
f = g * q + r,    q restricted at c,    r a polynomial of degree less than s.
```

This file names the quotient `q` and the remainder `r` as functions of `f`, for fixed `g`. By
uniqueness they are `R`-linear, so they are recorded as linear maps

```text
weierstrassDiv : R⟨c⁻¹X⟩ →ₗ[R] R⟨c⁻¹X⟩,   weierstrassMod : R⟨c⁻¹X⟩ →ₗ[R] R[X]
```

on the ring `PowerSeries.IsRestricted.subring c` of series restricted at `c`. They are
characterised by the division identity and the degree bound on the remainder, they send `g * q`
to `(q, 0)` and a polynomial of degree less than `s` to `(0, p)`, and the remainder vanishes
exactly on the multiples of `g`. The Gauss norm at `c` satisfies

```text
‖f‖ = max (‖g‖ * ‖weierstrassDiv f‖) ‖weierstrassMod f‖,
```

so for the Gauss norm the quotient map is bounded by `‖g‖⁻¹` and the remainder map by `1`; in
particular the
quotient map is continuous for the Gauss-norm topology. The norm of `R` need not be
multiplicative, and `R` may have nilpotents.

## Main definitions

* `TauCeti.PowerSeries.IsMulDistinguished.weierstrassDiv`: the Weierstrass quotient by `g`.
* `TauCeti.PowerSeries.IsMulDistinguished.weierstrassMod`: the Weierstrass remainder by `g`, a
  polynomial of degree less than `s`.

## Main results

* `TauCeti.PowerSeries.IsMulDistinguished.mul_weierstrassDiv_add_weierstrassMod` and
  `TauCeti.PowerSeries.IsMulDistinguished.degree_weierstrassMod_lt`: the division identity.
* `TauCeti.PowerSeries.IsMulDistinguished.weierstrassDiv_eq_and_weierstrassMod_eq_iff`: any
  decomposition `g * q + r` with `deg r < s` is the Weierstrass division.
* `TauCeti.PowerSeries.IsMulDistinguished.weierstrassMod_eq_zero_iff_dvd`: the remainder vanishes
  exactly on multiples of `g`.
* `TauCeti.PowerSeries.IsMulDistinguished.gaussNorm_eq_max`,
  `TauCeti.PowerSeries.IsMulDistinguished.gaussNorm_weierstrassDiv_le` and
  `TauCeti.PowerSeries.IsMulDistinguished.gaussNorm_weierstrassMod_le`: the norm identity and the
  bounds `‖q‖ ≤ ‖f‖ / ‖g‖` and `‖r‖ ≤ ‖f‖`.
* `TauCeti.PowerSeries.IsMulDistinguished.continuous_weierstrassDiv`: the quotient map is
  continuous.

## References

* F. Martin, *Overconvergent subanalytic subsets in the framework of Berkovich spaces*,
  J. Eur. Math. Soc. 18 (2016), Proposition 1.27, for division by a multiplicatively distinguished
  series over a Banach ring and its norm estimates.
* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §5.2.1, Theorem 2, for the field case.

The names and the shape of the characterising lemmas follow Mathlib's `PowerSeries.weierstrassDiv`
and `PowerSeries.weierstrassMod`, the quotient and remainder of the ideal-adic Weierstrass division
over a complete local ring; that is a different division theorem, for a different notion of
divisor.
-/

public section

namespace TauCeti.PowerSeries.IsMulDistinguished

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] {c : ℝ} {s : ℕ}
  {g : PowerSeries.IsRestricted.subring (R := R) c}

/-- Uniqueness of Weierstrass division, read in the restricted subring with a polynomial
remainder. -/
private theorem eq_and_eq_of_mul_add_polynomialToRestricted_eq
    (hg : IsMulDistinguished c s (g : PowerSeries R)) (hc : 0 < c)
    {q q' : PowerSeries.IsRestricted.subring (R := R) c} {r r' : Polynomial R}
    (hr : r.degree < s) (hr' : r'.degree < s)
    (h : g * q + polynomialToRestricted c r = g * q' + polynomialToRestricted c r') :
    q = q' ∧ r = r' := by
  have h' : (g : PowerSeries R) * q + r = (g : PowerSeries R) * q' + r' := by
    simpa using congrArg Subtype.val h
  have hz : ∀ {p : Polynomial R}, p.degree < s → ∀ m, s ≤ m → (p : PowerSeries R).coeff m = 0 :=
    fun hp m hm ↦ by
      rw [Polynomial.coeff_coe]
      exact Polynomial.coeff_eq_zero_of_degree_lt (hp.trans_le (by exact_mod_cast hm))
  obtain ⟨hq, hr⟩ := hg.eq_and_eq_of_mul_add_eq_mul_add hc q.2 q'.2 (hz hr) (hz hr') h'
  exact ⟨Subtype.ext hq, Polynomial.coe_inj.mp hr⟩

variable [CompleteSpace R]

/-- Existence of Weierstrass division, read in the restricted subring with a polynomial
remainder. -/
private theorem exists_mul_add_polynomialToRestricted_eq
    (hg : IsMulDistinguished c s (g : PowerSeries R)) (hc : 0 < c)
    (f : PowerSeries.IsRestricted.subring (R := R) c) :
    ∃ p : PowerSeries.IsRestricted.subring (R := R) c × Polynomial R,
      p.2.degree < s ∧ g * p.1 + polynomialToRestricted c p.2 = f := by
  obtain ⟨q, r, hq, hr, hqr⟩ := hg.exists_mul_add_eq hc g.2 f.2
  refine ⟨(⟨q, hq⟩, PowerSeries.trunc s r), PowerSeries.degree_trunc_lt r s, ?_⟩
  rw [polynomialToRestricted_trunc_eq_of_coeff_eq_zero
    ⟨r, isRestricted_of_forall_coeff_eq_zero hr⟩ hr]
  exact Subtype.ext hqr

/-- The Weierstrass quotient and remainder of `f`, chosen by existence of division. -/
private noncomputable def divModFun (hg : IsMulDistinguished c s (g : PowerSeries R))
    (hc : 0 < c) (f : PowerSeries.IsRestricted.subring (R := R) c) :
    PowerSeries.IsRestricted.subring (R := R) c × Polynomial R :=
  (exists_mul_add_polynomialToRestricted_eq hg hc f).choose

private theorem divModFun_spec (hg : IsMulDistinguished c s (g : PowerSeries R)) (hc : 0 < c)
    (f : PowerSeries.IsRestricted.subring (R := R) c) :
    (divModFun hg hc f).2.degree < s ∧
      g * (divModFun hg hc f).1 + polynomialToRestricted c (divModFun hg hc f).2 = f :=
  (exists_mul_add_polynomialToRestricted_eq hg hc f).choose_spec

private theorem divModFun_eq (hg : IsMulDistinguished c s (g : PowerSeries R)) (hc : 0 < c)
    {f : PowerSeries.IsRestricted.subring (R := R) c}
    {p : PowerSeries.IsRestricted.subring (R := R) c × Polynomial R}
    (hr : p.2.degree < s) (h : g * p.1 + polynomialToRestricted c p.2 = f) :
    divModFun hg hc f = p := by
  obtain ⟨hr', h'⟩ := divModFun_spec hg hc f
  obtain ⟨e1, e2⟩ :=
    eq_and_eq_of_mul_add_polynomialToRestricted_eq hg hc hr' hr (h'.trans h.symm)
  exact Prod.ext e1 e2

/-- The Weierstrass quotient and remainder together, as an `R`-linear map. Linearity is forced by
uniqueness of the division. -/
private noncomputable def divMod (hg : IsMulDistinguished c s (g : PowerSeries R)) (hc : 0 < c) :
    PowerSeries.IsRestricted.subring (R := R) c →ₗ[R]
      PowerSeries.IsRestricted.subring (R := R) c × Polynomial R where
  toFun := divModFun hg hc
  map_add' f f' := by
    obtain ⟨hr, h⟩ := divModFun_spec hg hc f
    obtain ⟨hr', h'⟩ := divModFun_spec hg hc f'
    refine divModFun_eq hg hc ?_ ?_
    · exact (Polynomial.degree_add_le _ _).trans_lt (max_lt hr hr')
    · rw [Prod.snd_add, Prod.fst_add, map_add]
      linear_combination h + h'
  map_smul' a f := by
    obtain ⟨hr, h⟩ := divModFun_spec hg hc f
    refine divModFun_eq hg hc ?_ ?_
    · exact (Polynomial.degree_smul_le a _).trans_lt hr
    · rw [Prod.smul_snd, Prod.smul_fst, map_smul, mul_smul_comm, ← smul_add, h, RingHom.id_apply]

/-- **The Weierstrass quotient** by a restricted series `g` multiplicatively distinguished of
degree `s` at a radius `c > 0`, over a complete ultrametric normed commutative ring: the
restricted series `q` in the unique decomposition `f = g * q + r` with `r` a polynomial of degree
less than `s`. It is `R`-linear in `f`. -/
noncomputable def weierstrassDiv (hg : IsMulDistinguished c s (g : PowerSeries R)) (hc : 0 < c) :
    PowerSeries.IsRestricted.subring (R := R) c →ₗ[R]
      PowerSeries.IsRestricted.subring (R := R) c :=
  LinearMap.fst R _ _ ∘ₗ divMod hg hc

/-- **The Weierstrass remainder** by a restricted series `g` multiplicatively distinguished of
degree `s` at a radius `c > 0`, over a complete ultrametric normed commutative ring: the
polynomial `r` of degree less than `s` in the unique decomposition `f = g * q + r` with `q`
restricted. It is `R`-linear in `f`. -/
noncomputable def weierstrassMod (hg : IsMulDistinguished c s (g : PowerSeries R)) (hc : 0 < c) :
    PowerSeries.IsRestricted.subring (R := R) c →ₗ[R] Polynomial R :=
  LinearMap.snd R _ _ ∘ₗ divMod hg hc

variable (hg : IsMulDistinguished c s (g : PowerSeries R)) (hc : 0 < c)

/-- The Weierstrass remainder has degree less than the distinguished degree. -/
theorem degree_weierstrassMod_lt (f : PowerSeries.IsRestricted.subring (R := R) c) :
    (hg.weierstrassMod hc f).degree < s :=
  (divModFun_spec hg hc f).1

/-- **The Weierstrass division identity**: `f = g * q + r` for the Weierstrass quotient `q` and
remainder `r` of `f`. -/
theorem mul_weierstrassDiv_add_weierstrassMod
    (f : PowerSeries.IsRestricted.subring (R := R) c) :
    g * hg.weierstrassDiv hc f + polynomialToRestricted c (hg.weierstrassMod hc f) = f :=
  (divModFun_spec hg hc f).2

/-- **Uniqueness of the Weierstrass quotient and remainder.** A decomposition `g * q + r` of `f`
with `r` a polynomial of degree less than `s` is the Weierstrass division of `f`. -/
theorem weierstrassDiv_eq_and_weierstrassMod_eq_iff
    {f q : PowerSeries.IsRestricted.subring (R := R) c} {r : Polynomial R} (hr : r.degree < s) :
    hg.weierstrassDiv hc f = q ∧ hg.weierstrassMod hc f = r ↔
      g * q + polynomialToRestricted c r = f := by
  refine ⟨fun ⟨hq, hr'⟩ ↦ ?_, fun h ↦ ?_⟩
  · rw [← hq, ← hr']
    exact hg.mul_weierstrassDiv_add_weierstrassMod hc f
  · have := divModFun_eq hg hc (p := (q, r)) hr h
    exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩

/-- The Weierstrass quotient of `g * q + r`, with `r` a polynomial of degree less than `s`,
is `q`. -/
theorem weierstrassDiv_eq_of_mul_add_eq
    {f q : PowerSeries.IsRestricted.subring (R := R) c} {r : Polynomial R} (hr : r.degree < s)
    (h : g * q + polynomialToRestricted c r = f) : hg.weierstrassDiv hc f = q :=
  ((hg.weierstrassDiv_eq_and_weierstrassMod_eq_iff hc hr).mpr h).1

/-- The Weierstrass remainder of `g * q + r`, with `r` a polynomial of degree less than `s`,
is `r`. -/
theorem weierstrassMod_eq_of_mul_add_eq
    {f q : PowerSeries.IsRestricted.subring (R := R) c} {r : Polynomial R} (hr : r.degree < s)
    (h : g * q + polynomialToRestricted c r = f) : hg.weierstrassMod hc f = r :=
  ((hg.weierstrassDiv_eq_and_weierstrassMod_eq_iff hc hr).mpr h).2

/-- Dividing a multiple `g * q` by `g` returns `q`. -/
@[simp]
theorem weierstrassDiv_mul_cancel_left (q : PowerSeries.IsRestricted.subring (R := R) c) :
    hg.weierstrassDiv hc (g * q) = q :=
  hg.weierstrassDiv_eq_of_mul_add_eq hc (q := q)
    (by rw [Polynomial.degree_zero]; exact WithBot.bot_lt_coe s) (by simp)

/-- A multiple `g * q` has Weierstrass remainder zero. -/
@[simp]
theorem weierstrassMod_mul_eq_zero (q : PowerSeries.IsRestricted.subring (R := R) c) :
    hg.weierstrassMod hc (g * q) = 0 :=
  hg.weierstrassMod_eq_of_mul_add_eq hc (q := q)
    (by rw [Polynomial.degree_zero]; exact WithBot.bot_lt_coe s) (by simp)

/-- A polynomial of degree less than `s` has Weierstrass quotient zero. -/
@[simp]
theorem weierstrassDiv_polynomialToRestricted_of_degree_lt {p : Polynomial R}
    (hp : p.degree < s) : hg.weierstrassDiv hc (polynomialToRestricted c p) = 0 :=
  hg.weierstrassDiv_eq_of_mul_add_eq hc (q := 0) hp (by simp)

/-- A polynomial of degree less than `s` is its own Weierstrass remainder. -/
@[simp]
theorem weierstrassMod_polynomialToRestricted_of_degree_lt {p : Polynomial R}
    (hp : p.degree < s) : hg.weierstrassMod hc (polynomialToRestricted c p) = p :=
  hg.weierstrassMod_eq_of_mul_add_eq hc (q := 0) hp (by simp)

/-- The Weierstrass remainder of `f` vanishes exactly when `g` divides `f` in the ring of
restricted series. -/
theorem weierstrassMod_eq_zero_iff_dvd {f : PowerSeries.IsRestricted.subring (R := R) c} :
    hg.weierstrassMod hc f = 0 ↔ g ∣ f := by
  refine ⟨fun h ↦ ⟨hg.weierstrassDiv hc f, ?_⟩,
    fun ⟨q, hq⟩ ↦ hq ▸ hg.weierstrassMod_mul_eq_zero hc q⟩
  have := hg.mul_weierstrassDiv_add_weierstrassMod hc f
  rw [h, map_zero, add_zero] at this
  exact this.symm

/-- In distinguished degree zero every Weierstrass remainder is zero. -/
@[simp]
theorem weierstrassMod_eq_zero (hg : IsMulDistinguished c 0 (g : PowerSeries R))
    (f : PowerSeries.IsRestricted.subring (R := R) c) : hg.weierstrassMod hc f = 0 := by
  have := hg.degree_weierstrassMod_lt hc f
  rw [Nat.cast_zero, Nat.WithBot.lt_zero_iff] at this
  exact Polynomial.degree_eq_bot.mp this

/-- **The Weierstrass norm identity.** The Gauss norm of `f` at `c` is the larger of
`‖g‖ * ‖q‖` and `‖r‖`, for its Weierstrass quotient `q` and remainder `r`. -/
theorem gaussNorm_eq_max (f : PowerSeries.IsRestricted.subring (R := R) c) :
    (f : PowerSeries R).gaussNorm norm c =
      max ((g : PowerSeries R).gaussNorm norm c *
          (hg.weierstrassDiv hc f : PowerSeries R).gaussNorm norm c)
        ((hg.weierstrassMod hc f : PowerSeries R).gaussNorm norm c) := by
  conv_lhs => rw [← hg.mul_weierstrassDiv_add_weierstrassMod hc f]
  simpa using hg.gaussNorm_mul_add_eq_max hc (hg.weierstrassDiv hc f).2 fun m hm ↦ by
    rw [Polynomial.coeff_coe]
    exact Polynomial.coeff_eq_zero_of_degree_lt
      ((hg.degree_weierstrassMod_lt hc f).trans_le (by exact_mod_cast hm))

/-- **The Weierstrass quotient bound** `‖q‖ ≤ ‖f‖ / ‖g‖`, for the Gauss norm at `c`. -/
theorem gaussNorm_weierstrassDiv_le (f : PowerSeries.IsRestricted.subring (R := R) c) :
    (hg.weierstrassDiv hc f : PowerSeries R).gaussNorm norm c ≤
      (f : PowerSeries R).gaussNorm norm c / (g : PowerSeries R).gaussNorm norm c := by
  rw [le_div_iff₀ hg.gaussNorm_pos, mul_comm, hg.gaussNorm_eq_max hc f]
  exact le_max_left _ _

/-- **The Weierstrass remainder bound** `‖r‖ ≤ ‖f‖`, for the Gauss norm at `c`. -/
theorem gaussNorm_weierstrassMod_le (f : PowerSeries.IsRestricted.subring (R := R) c) :
    (hg.weierstrassMod hc f : PowerSeries R).gaussNorm norm c ≤
      (f : PowerSeries R).gaussNorm norm c := by
  rw [hg.gaussNorm_eq_max hc f]
  exact le_max_right _ _

/-- The Weierstrass quotient map is continuous for the Gauss-norm topology at `c`: it is bounded
by `‖g‖⁻¹`. -/
theorem continuous_weierstrassDiv [Fact (0 < c)] :
    Continuous (hg.weierstrassDiv (Fact.out : 0 < c)) :=
  AddMonoidHomClass.continuous_of_bound _ ‖g‖⁻¹ fun f ↦ by
    rw [norm_eq_gaussNorm, norm_eq_gaussNorm, norm_eq_gaussNorm, inv_mul_eq_div]
    exact hg.gaussNorm_weierstrassDiv_le Fact.out f

end TauCeti.PowerSeries.IsMulDistinguished
