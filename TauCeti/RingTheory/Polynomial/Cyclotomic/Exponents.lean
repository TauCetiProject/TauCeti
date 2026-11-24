/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import TauCeti.RingTheory.Polynomial.Roots

/-!
# Exponents of roots of unity in polynomial factorizations

Suppose a rational polynomial splits as a product of linear factors with roots `ζ ^ e i`,
where `ζ` is a primitive `h`-th root of unity and `e i < h`. If the polynomial has any
primitive `h`-th root, then every residue coprime to `h` occurs among the `e i`.

The rationality hypothesis matters: a polynomial over a larger field can have just one
primitive root without having its cyclotomic conjugates. No simplicity of the roots is
assumed, so repeated exponents are permitted. This is the arithmetic step that turns
integral characteristic polynomials into constraints on their lists of eigenvalue exponents.

Rationality also makes such a factorization independent of the primitive root: a rational
polynomial equal to `∏ i, (X - ζ ^ e i)` is equal to `∏ i, (X - ξ ^ e i)` for every primitive
`h`-th root of unity `ξ` (`IsPrimitiveRoot.map_eq_prod_of_map_eq_prod`). Each coefficient of the
product is a rational polynomial expression in `ζ`, and agreeing with a rational number at `ζ` it
does so at every root of the cyclotomic polynomial, the minimal polynomial of `ζ`.

The ambient ring can be any domain that is a rational algebra. The proof uses Mathlib's
`IsPrimitiveRoot.minpoly_eq_cyclotomic_of_irreducible` and irreducibility of cyclotomic
polynomials over the rationals.

Over a field, if instead the roots `ζ ^ e i` are stable under inversion with multiplicity, as
for the eigenvalues of a linear map conjugate to its inverse, and no `e i` is divisible by `h`,
then the residues `e i % h` pair off as `a` and `h - a`, so they add up to `h / 2` per factor
(`IsPrimitiveRoot.two_mul_sum_mod_eq_mul_card`).
-/

public section

open Polynomial

namespace IsPrimitiveRoot

section Rational

variable {K ι : Type*} [CommRing K] [IsDomain K] [Algebra ℚ K] [Fintype ι]

/-- If a rational polynomial factors with roots `ζ ^ e i`, with all `e i < h`, and has a
primitive `h`-th root, every residue less than `h` and coprime to `h` occurs in `e`.
The primitive root already known to be a root need not be `ζ` itself. -/
theorem exists_eq_of_isRoot_of_map_eq_prod {h : ℕ} {ζ ξ : K}
    (hζ : IsPrimitiveRoot ζ h) (hξ : IsPrimitiveRoot ξ h) {p : ℚ[X]}
    (hp : (p.map (algebraMap ℚ K)).IsRoot ξ) {e : ι → ℕ}
    (he : ∀ i, e i < h)
    (hprod : p.map (algebraMap ℚ K) = ∏ i, (X - C (ζ ^ e i)))
    {a : ℕ} (ha : a < h) (hcop : a.Coprime h) : ∃ i, e i = a := by
  classical
  have hh : 0 < h := Nat.zero_lt_of_lt ha
  have : NeZero (h : ℚ) := ⟨Nat.cast_ne_zero.mpr hh.ne'⟩
  have hdiv : cyclotomic h ℚ ∣ p := by
    rw [hξ.minpoly_eq_cyclotomic_of_irreducible (cyclotomic.irreducible_rat hh)]
    exact minpoly.dvd ℚ ξ (by simpa only [aeval_def, eval₂_eq_eval_map, IsRoot.def] using hp)
  have hroot : (p.map (algebraMap ℚ K)).IsRoot (ζ ^ a) := by
    obtain ⟨q, rfl⟩ := hdiv
    rw [Polynomial.map_mul, map_cyclotomic]
    have hcy : (cyclotomic h K).IsRoot (ζ ^ a) :=
      (hζ.pow_of_coprime a hcop).isRoot_cyclotomic hh
    rw [IsRoot.def, eval_mul, hcy.eq_zero, zero_mul]
  rw [hprod, IsRoot.def, eval_prod] at hroot
  obtain ⟨i, -, hi⟩ := Finset.prod_eq_zero_iff.mp hroot
  have hi' : ζ ^ a = ζ ^ e i := sub_eq_zero.mp (by simpa using hi)
  exact ⟨i, (hζ.pow_inj ha (he i) hi').symm⟩

/-- **A rational factorization into powers of a primitive root does not depend on the root.** If a
rational polynomial factors as `∏ i, (X - ζ ^ e i)` for a primitive `h`-th root of unity `ζ`, then
it factors as `∏ i, (X - ξ ^ e i)` for every primitive `h`-th root of unity `ξ`. The exponents are
unrestricted and may repeat. -/
theorem map_eq_prod_of_map_eq_prod {h : ℕ} (hh : 0 < h) {ζ ξ : K}
    (hζ : IsPrimitiveRoot ζ h) (hξ : IsPrimitiveRoot ξ h) {p : ℚ[X]} {e : ι → ℕ}
    (hprod : p.map (algebraMap ℚ K) = ∏ i, (X - C (ζ ^ e i))) :
    p.map (algebraMap ℚ K) = ∏ i, (X - C (ξ ^ e i)) := by
  have : NeZero (h : ℚ) := ⟨Nat.cast_ne_zero.mpr hh.ne'⟩
  -- The same product with the root replaced by a variable, whose coefficients lie in `ℚ[X]`.
  let F : ℚ[X][X] := ∏ i, (X - C (X ^ e i))
  have hF (μ : K) : F.map (aeval μ).toRingHom = ∏ i, (X - C (μ ^ e i)) := by
    simp [F, Polynomial.map_prod]
  -- Each coefficient of `F`, minus the matching coefficient of `p`, vanishes at `ζ`, so it is
  -- divisible by the minimal polynomial of `ζ`, the cyclotomic polynomial, which also kills `ξ`.
  ext j
  have hj := congr(($hprod).coeff j)
  rw [← hF ζ, coeff_map, coeff_map] at hj
  rw [← hF ξ, coeff_map, coeff_map]
  obtain ⟨q, hq⟩ : cyclotomic h ℚ ∣ F.coeff j - C (p.coeff j) := by
    rw [hζ.minpoly_eq_cyclotomic_of_irreducible (cyclotomic.irreducible_rat hh)]
    exact minpoly.dvd ℚ ζ (by simpa [sub_eq_zero] using hj.symm)
  have hcy : aeval ξ (cyclotomic h ℚ) = 0 := by
    rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]
    exact (hξ.isRoot_cyclotomic hh).eq_zero
  have hξq := congr(aeval ξ $hq)
  rw [map_mul, hcy, zero_mul, map_sub, aeval_C, sub_eq_zero] at hξq
  simpa using hξq.symm

end Rational

section Field

variable {K ι : Type*} [Field K] [Fintype ι]

/-- If the roots `ζ ^ e i` of `∏ i, (X - ζ ^ e i)`, for a primitive `h`-th root of unity `ζ`,
are stable under inversion with multiplicity, and no `e i` is divisible by `h`, then the residues
`e i % h` add up to `h / 2` per factor: they pair off as `a` and `h - a`. -/
theorem two_mul_sum_mod_eq_mul_card {h : ℕ} [NeZero h] {ζ : K} (hζ : IsPrimitiveRoot ζ h)
    {e : ι → ℕ} (he : ∀ i, ¬ h ∣ e i)
    (hprod : ∏ i, (X - C (ζ ^ e i)) = ∏ i, (X - C (ζ⁻¹ ^ e i))) :
    2 * ∑ i, e i % h = h * Fintype.card ι := by
  classical
  -- Read the exponents as residues: `a ↦ ζ ^ a.val` is injective on `ZMod h`.
  let f : ZMod h → K := fun a ↦ ζ ^ a.val
  have hf : Function.Injective f := fun a a' haa' ↦
    ZMod.val_injective h (hζ.pow_inj a.val_lt a'.val_lt haa')
  have hfe (n : ℕ) : f n = ζ ^ n := by
    conv_rhs => rw [← Nat.mod_add_div n h, pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]
    rw [← ZMod.val_natCast]
  have hfneg (n : ℕ) : f (-(n : ZMod h)) = ζ⁻¹ ^ n := by
    have hdvd : h ∣ (-(n : ZMod h)).val + n := (ZMod.natCast_eq_zero_iff _ _).mp (by simp)
    rw [inv_pow]
    exact eq_inv_of_mul_eq_one_left (by rw [← pow_add]; exact (hζ.pow_eq_one_iff_dvd _).mpr hdvd)
  -- Comparing roots, the residues `e i` are stable under negation, with multiplicity.
  have hs : (Finset.univ.val.map fun i ↦ -(e i : ZMod h)) =
      Finset.univ.val.map fun i ↦ (e i : ZMod h) := by
    refine Multiset.map_injective hf ?_
    simpa only [Multiset.map_map, Function.comp_def, hfe, hfneg, roots_prod_X_sub_C_map] using
      (congrArg Polynomial.roots hprod).symm
  have hsum : ∑ i, (-(e i : ZMod h)).val = ∑ i, e i % h := by
    simpa only [Multiset.map_map, Function.comp_def, ZMod.val_natCast,
      ← Finset.sum_eq_multiset_sum] using congrArg (fun t ↦ (t.map ZMod.val).sum) hs
  -- Each residue `a` is paired with `h - a`.
  have hneg (i : ι) : (-(e i : ZMod h)).val = h - e i % h := by
    rw [ZMod.neg_val, ite_eq_right (by rw [ZMod.natCast_eq_zero_iff]; exact he i), ZMod.val_natCast]
  calc 2 * ∑ i, e i % h = ∑ i, e i % h + ∑ i, (-(e i : ZMod h)).val := by rw [hsum, two_mul]
    _ = ∑ _i : ι, h := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      have := Nat.mod_lt (e i) (Nat.pos_of_neZero h)
      rw [hneg]
      omega
    _ = h * Fintype.card ι := by simp [mul_comm]

end Field

end IsPrimitiveRoot
