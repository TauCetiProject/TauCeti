/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NewtonPolygon.Mul
public import TauCeti.RingTheory.Polynomial.Factors

/-!
# Irreducibility of pure polynomials with integral valuations

Let `v` be a real additive valuation taking integer values on nonzero elements, for example a
discrete valuation normalised at a uniformiser. A polynomial is *pure* of slope `q` when every
finite slope of its Newton polygon equals `q`. Its endpoints have integer heights, so `q` times
its horizontal length is an integer; for rational `q` the denominator of `q` divides that
length, by `Polynomial.den_dvd_card_newtonSlopes`.

The slopes of a factor of a nonzero polynomial are among the slopes of the polynomial, by
`Polynomial.newtonSlopes_le_of_dvd`. Hence every factor of a pure polynomial is pure of
the same slope, and if the polynomial has a nonzero constant coefficient the denominator of the
slope divides the degree of every factor. Over a field this gives the Newton polygon
irreducibility criterion: a polynomial with nonzero constant coefficient whose finite slopes all
equal `a / d`, where `d > 0` is its degree and `a` is coprime to `d`, is irreducible. More
generally a pure polynomial of degree `d` with nonzero constant coefficient whose slope has
denominator `e` has at most `d / e` irreducible factors, counted with multiplicity. Purity alone
does not imply irreducibility, nor does a polygon with a single segment.

An Eisenstein polynomial of degree `d` is pure of slope `-1 / d`, by
`Polynomial.newtonSlopes_eq_replicate_of_eisenstein`, and `-1` is coprime to `d`, so the
criterion recovers the Eisenstein criterion over the field. Mathlib's
`Polynomial.irreducible_of_eisenstein_criterion` is the corresponding statement over a ring for
a prime ideal, for primitive polynomials.

## Main results

* `Polynomial.den_dvd_natDegree_of_dvd`: the denominator of the slope of a pure polynomial with
  nonzero constant coefficient divides the degree of each of its factors.
* `Polynomial.irreducible_of_forall_mem_newtonSlopes_eq`: a pure polynomial with nonzero constant
  coefficient whose degree is the denominator of its slope is irreducible, with the coprime
  numerator form `Polynomial.irreducible_of_forall_mem_newtonSlopes_eq_div`.
* `Polynomial.card_normalizedFactors_mul_den_le_natDegree`: a pure polynomial of degree `d` with
  nonzero constant coefficient whose slope has denominator `e` has at most `d / e` irreducible
  factors, counted with multiplicity.
* `Polynomial.irreducible_of_eisenstein`: the Eisenstein criterion over a field with a valuation
  taking integer values on nonzero elements, as a consequence of the Newton polygon
  irreducibility criterion.

## References

* J. Neukirch, *Algebraic Number Theory*, Grundlehren 322, Springer, 1999, Chapter II §6, for
  Newton polygons over discretely valued fields, and Proposition 6.3 and its corollary for
  Eisenstein polynomials.
* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, second edition,
  Graduate Texts in Mathematics 58, Springer, 1984, Chapter IV §3.
-/

public section

namespace Polynomial

section Ring

variable {R : Type*} [Ring R] {v : AddValuation R (WithTop ℝ)}

/-- If the valuation takes integer values on nonzero elements and `f` has nonzero constant
coefficient and every finite slope equal to the rational number `q`, then the denominator of
`q` divides the degree of every factor of `f`. -/
theorem den_dvd_natDegree_of_dvd (hint : ∀ x, x ≠ 0 → ∃ n : ℤ, v x = ((n : ℝ) : WithTop ℝ))
    {f g : R[X]} (hf : f.coeff 0 ≠ 0) {q : ℚ} (hq : ∀ m ∈ f.newtonSlopes v, m = q)
    (hgf : g ∣ f) : q.den ∣ g.natDegree := by
  have hv := AddValuation.eq_zero_of_eq_top_of_forall_ne_zero hint
  have hf₀ : f ≠ 0 := by
    rintro rfl
    exact hf (coeff_zero 0)
  have hle := newtonSlopes_le_of_dvd hv hf₀ hgf
  have hdvd := den_dvd_card_newtonSlopes hint fun m hm => hq m (Multiset.subset_of_le hle hm)
  obtain ⟨h, rfl⟩ := hgf
  have hg : g.coeff 0 ≠ 0 := by
    intro hg
    exact hf (by rw [mul_coeff_zero, hg, zero_mul])
  rwa [card_newtonSlopes g v hv, natTrailingDegree_eq_zero_of_constantCoeff_ne_zero hg,
    Nat.sub_zero] at hdvd

end Ring

section Field

variable {K : Type*} [Field K] {v : AddValuation K (WithTop ℝ)}

/-- **Newton polygon irreducibility criterion.** If the valuation takes integer values on
nonzero elements, a polynomial `f` with nonzero constant coefficient whose finite slopes all
equal a rational number `q`, and whose degree is the denominator of `q`, is irreducible. -/
theorem irreducible_of_forall_mem_newtonSlopes_eq
    (hint : ∀ x, x ≠ 0 → ∃ n : ℤ, v x = ((n : ℝ) : WithTop ℝ)) {f : K[X]} (hf : f.coeff 0 ≠ 0)
    {q : ℚ} (hq : ∀ m ∈ f.newtonSlopes v, m = q) (hden : q.den = f.natDegree) :
    Irreducible f := by
  have hdeg : 0 < f.natDegree := hden ▸ q.den_pos
  refine (irreducible_iff_lt_natDegree_lt (ne_zero_of_natDegree_gt hdeg)
    fun hu => hdeg.ne' (natDegree_eq_zero_of_isUnit hu)).mpr fun g _ hg hgf => ?_
  obtain ⟨k, hk⟩ := den_dvd_natDegree_of_dvd hint hf hq hgf
  rw [Finset.mem_Ioc, hk, hden] at hg
  rcases k with _ | k
  · simp at hg
  · nlinarith [Nat.div_mul_le_self f.natDegree 2]

/-- **Newton polygon irreducibility criterion**, coprime form. If the valuation takes integer
values on nonzero elements, a polynomial `f` of degree `d > 0` with nonzero constant coefficient
whose finite slopes all equal `a / d`, for an integer `a` coprime to `d`, is irreducible. -/
theorem irreducible_of_forall_mem_newtonSlopes_eq_div
    (hint : ∀ x, x ≠ 0 → ∃ n : ℤ, v x = ((n : ℝ) : WithTop ℝ)) {f : K[X]} (hf : f.coeff 0 ≠ 0)
    (hdeg : 0 < f.natDegree) {a : ℤ} (hcop : a.natAbs.Coprime f.natDegree)
    (ha : ∀ m ∈ f.newtonSlopes v, m = a / f.natDegree) : Irreducible f := by
  have hden : ((a : ℚ) / ((f.natDegree : ℤ) : ℚ)).den = f.natDegree := by
    have := Rat.den_div_eq_of_coprime (a := a) (b := f.natDegree) (by exact_mod_cast hdeg)
      (by simpa using hcop)
    exact_mod_cast this
  refine irreducible_of_forall_mem_newtonSlopes_eq hint hf (fun m hm => ?_) hden
  rw [ha m hm]
  norm_num

open UniqueFactorizationMonoid in
/-- If the valuation takes integer values on nonzero elements, a polynomial `f` of degree `d`
with nonzero constant coefficient whose finite slopes all equal a rational number with
denominator `e` has at most `d / e` irreducible factors, counted with multiplicity: each
irreducible factor has degree a positive multiple of `e`. -/
theorem card_normalizedFactors_mul_den_le_natDegree [DecidableEq K]
    (hint : ∀ x, x ≠ 0 → ∃ n : ℤ, v x = ((n : ℝ) : WithTop ℝ)) {f : K[X]} (hf : f.coeff 0 ≠ 0)
    {q : ℚ} (hq : ∀ m ∈ f.newtonSlopes v, m = q) :
    (normalizedFactors f).card * q.den ≤ f.natDegree := by
  rw [← sum_natDegree_normalizedFactors f, ← smul_eq_mul, ← Multiset.sum_replicate,
    ← Multiset.map_const']
  refine Multiset.sum_map_le_sum_map _ _ fun p hp => Nat.le_of_dvd ?_ ?_
  · exact (irreducible_of_normalized_factor p hp).natDegree_pos
  · exact den_dvd_natDegree_of_dvd hint hf hq (dvd_of_mem_normalizedFactors hp)

/-- **Eisenstein criterion.** If the valuation takes integer values on nonzero elements, a
polynomial whose leading coefficient has valuation zero, whose constant coefficient has
valuation one, and whose other coefficients below the degree have valuation at least one, is
irreducible. This is the Newton polygon irreducibility criterion for the single slope `-1 / d`. -/
theorem irreducible_of_eisenstein (hint : ∀ x, x ≠ 0 → ∃ n : ℤ, v x = ((n : ℝ) : WithTop ℝ))
    {f : K[X]} (hlead : v f.leadingCoeff = 0) (h0 : v (f.coeff 0) = 1)
    (hmem : ∀ n, 0 < n → n < f.natDegree → 1 ≤ v (f.coeff n)) : Irreducible f := by
  have hc0 : f.coeff 0 ≠ 0 := fun h => by simp [h] at h0
  have hd : 0 < f.natDegree := Nat.pos_of_ne_zero fun hd => by
    rw [leadingCoeff, hd, h0] at hlead
    exact one_ne_zero hlead
  refine irreducible_of_forall_mem_newtonSlopes_eq_div hint hc0 hd (a := -1) (by simp)
    fun m hm => ?_
  rw [newtonSlopes_eq_replicate_of_eisenstein hlead h0 hmem] at hm
  rw [Multiset.eq_of_mem_replicate hm]
  push_cast
  ring

end Field

end Polynomial
