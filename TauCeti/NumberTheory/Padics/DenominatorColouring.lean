/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Data.Rat.Encodable
public import TauCeti.NumberTheory.Padics.PadicValRat
public import TauCeti.Order.CountableDenseLinearOrder

/-!
# Colouring the rationals by the `p`-adic valuation of the denominator

Fix a prime `p` and colour each rational number `r` by `multiplicity p r.den`, the exponent of `p`
in its reduced denominator (equal to `padicValNat p r.den`, by `Nat.padicValNat_def`). For
`p = 2`: `3/4` has colour `2`, `5` and `0` have colour `0`, `-1/6` has colour `1`.

Every colour class is dense in `ℚ`: the rationals whose denominator is prime to `p` are dense,
as `z / (p + 1) ^ N` shows, and adding `1 / p ^ m` to such a rational gives one of colour `m`.
Hence the coloured form of Cantor's isomorphism theorem applies to `ℚ` with this colouring and
any permutation of it: every permutation `σ` of the colours is realised by an order automorphism
`π` of `ℚ`, in the sense that `π r` has colour `σ` of the colour of `r`.

With `p = 2`, the colour of a rational number is a vertex of a countable structure on `ℕ`, and a
finite sequence of rationals names a tuple of vertices. Relabelling the vertices by a permutation
`σ` of `ℕ` then lifts to an order automorphism of `ℚ` acting entrywise on such sequences, which is
how isomorphic countable structures yield isomorphic coloured linear orders (Friedman–Stanley).

## Main results

* `Rat.exists_multiplicity_den_eq_btwn`: between any two rationals there is one of each colour.
* `Rat.exists_orderIso_multiplicity_den_eq`: every permutation of the colours is induced by an
  order automorphism of `ℚ`.

## References

* H. Friedman and L. Stanley, *A Borel reducibility theory for classes of countable structures*,
  J. Symbolic Logic 54 (1989), §2.
* A. Montalbán, *Computable structure theory: within the arithmetic*, the proof of Lemma VI.18.
-/

public section

namespace Rat

variable {p : ℕ} [hp : Fact p.Prime]

/-- Between any two rationals there is one whose denominator is prime to `p`, of the form
`z / (p + 1) ^ N`. -/
private theorem exists_multiplicity_den_eq_zero_btwn {a b : ℚ} (hab : a < b) :
    ∃ r, a < r ∧ r < b ∧ multiplicity p r.den = 0 := by
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (b - a)⁻¹
    (by exact_mod_cast Nat.succ_lt_succ hp.out.pos : (1 : ℚ) < ((p + 1 : ℕ) : ℚ))
  obtain ⟨z, hz₁, hz₂⟩ := exists_div_btwn (n := (p + 1) ^ N) hab (by exact_mod_cast hN)
  refine ⟨z / ((p + 1) ^ N : ℕ), hz₁, hz₂, multiplicity_eq_zero_of_not_dvd fun hdvd ↦ ?_⟩
  -- the denominator divides `(p + 1) ^ N`, which `p` does not divide
  have hden : ((z / ((p + 1) ^ N : ℕ) : ℚ).den : ℤ) ∣ ((p + 1) ^ N : ℕ) := by
    simpa [Rat.divInt_eq_div] using Rat.den_dvd z ((p + 1) ^ N : ℕ)
  have hp1 : p ∣ p + 1 :=
    hp.out.dvd_of_dvd_pow (hdvd.trans (Int.natCast_dvd_natCast.1 hden))
  exact hp.out.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right dvd_rfl).1 hp1))

/-- **Density of the colour classes.** Between any two rationals there is one whose denominator
has exactly `m` factors of `p`. -/
theorem exists_multiplicity_den_eq_btwn (m : ℕ) {a b : ℚ} (hab : a < b) :
    ∃ r, a < r ∧ r < b ∧ multiplicity p r.den = m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact exists_multiplicity_den_eq_zero_btwn hab
  -- shift a rational with denominator prime to `p` by `1 / p ^ m`
  set s : ℚ := ((p ^ m : ℕ) : ℚ)⁻¹
  have hs : multiplicity p s.den = m := by
    rw [Rat.inv_natCast_den_of_pos (pow_pos hp.out.pos m)]
    exact Nat.multiplicity_prime_pow m
  obtain ⟨t, ht₁, ht₂, ht⟩ :=
    exists_multiplicity_den_eq_zero_btwn (p := p) (sub_lt_sub_right hab s)
  refine ⟨t + s, by linarith, by linarith, ?_⟩
  rw [multiplicity_den_add_of_lt (by omega), hs]

/-- **The coloured Cantor theorem for `ℚ`.** Colouring each rational by the multiplicity of `p` in
its denominator, every permutation `σ` of the colours is induced by an order automorphism `π` of
`ℚ`: the colour of `π r` is `σ` of the colour of `r`. -/
theorem exists_orderIso_multiplicity_den_eq (σ : Equiv.Perm ℕ) :
    ∃ π : ℚ ≃o ℚ, ∀ r, multiplicity p (π r).den = σ (multiplicity p r.den) := by
  obtain ⟨π, hπ⟩ := Order.exists_orderIso_comp_eq_of_dense
    (c := fun r : ℚ ↦ σ (multiplicity p r.den)) (d := fun r : ℚ ↦ multiplicity p r.den)
    (fun i _ _ hab ↦ (exists_multiplicity_den_eq_btwn (p := p) (σ.symm i) hab).imp fun _ hr ↦
      ⟨hr.1, hr.2.1, by simp [hr.2.2]⟩)
    (fun i _ _ hab ↦ exists_multiplicity_den_eq_btwn i hab)
  exact ⟨π, congrFun hπ⟩

end Rat
