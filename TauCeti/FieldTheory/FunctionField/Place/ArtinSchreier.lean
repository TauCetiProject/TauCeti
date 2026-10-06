/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Perfect
public import TauCeti.FieldTheory.FunctionField.Place.Filtration
public import TauCeti.RingTheory.Valuation.Discrete.PowerSubSelf

/-!
# Reduced Artin–Schreier representatives at a place

In characteristic `p`, a function `u` defines the same Artin–Schreier extension as
`u - (w ^ p - w)`. At a place with perfect residue field, such a representative can be
chosen integral or with pole order prime to `p`. This is the local input for computing
ramification and the different of Artin–Schreier extensions.

`exists_ord_sub_pow_sub_self_gt_of_dvd_ord` cancels a leading pole term whose order is
divisible by the exponent, by lifting a root of its residue. Iteration gives
`exists_reduced_artinSchreier_representative`. The one-step result only needs surjectivity
of the power map on the residue field; the iteration uses additivity of Frobenius.
Neither result requires completeness, an exact constant field, or a function-field hypothesis.

A prime-to-`p` pole cannot be improved by any Artin–Schreier substitution, even with an
imperfect residue field.
`TauCeti.ne_pow_sub_self_of_exists_reduced_artinSchreier_pole` proves that a class with such a
representative is nontrivial.
`TauCeti.ord_sub_pow_sub_self_le_of_ord_neg_of_not_dvd` records this maximality,
and `TauCeti.ord_reduced_artinSchreier_representative_eq` gives uniqueness.
The integral alternative includes the zero representative, so no statement
uses the junk value `ord_P 0 = 0` as a positive order of vanishing.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Proposition 3.7.8.
-/

public section

namespace TauCeti.Place

variable {k F : Type*} [Field k] [Field F] [Algebra k F] (P : Place k F)

/-- A pole of order divisible by `n > 1` can be improved by a substitution
`u ↦ u - (w ^ n - w)` if the `n`-th power map of the residue field is surjective.
This cancellation step does not need a characteristic hypothesis. -/
theorem exists_ord_sub_pow_sub_self_gt_of_dvd_ord {n : ℕ} (hn : 1 < n)
    (hpow : Function.Surjective fun a : P.ResidueField ↦ a ^ n) {u : F}
    (hu : P.ord u < 0) (hdiv : (n : ℤ) ∣ P.ord u) :
    ∃ w : F, P.ord u < P.ord (u - (w ^ n - w)) := by
  obtain ⟨q, hq⟩ := hdiv
  have hn' : (1 : ℤ) < n := by exact_mod_cast hn
  have hqneg : q < 0 := by nlinarith
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu
  -- Normalize the leading term to a unit and lift an n-th root of its residue.
  obtain ⟨s, hs0, hs⟩ := P.exists_ne_zero_ord_eq (-q)
  have hnorm : P.ord (u * s ^ n) = 0 := by
    rw [P.ord_mul hu0 (pow_ne_zero _ hs0), P.ord_pow, hs, hq]
    ring
  let b : P.integers := ⟨u * s ^ n, P.mem_integers_iff_ord_nonneg.mpr hnorm.ge⟩
  obtain ⟨a₀, ha₀⟩ := hpow (IsLocalRing.residue P.integers b)
  obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective (R := P.integers) a₀
  have hres : IsLocalRing.residue P.integers b =
      IsLocalRing.residue P.integers (a ^ n) := by
    rw [map_pow, ha]
    exact ha₀.symm
  have hcancel : u * s ^ n - (a : F) ^ n ∈ P.filtration 1 := by
    simpa only [b, SubmonoidClass.coe_pow] using
      P.residue_eq_iff_sub_mem_filtration_one.mp hres
  have hsinv : s⁻¹ ^ n ∈ P.filtration (P.ord u) := by
    rw [P.mem_filtration_iff_le_ord (pow_ne_zero _ (inv_ne_zero hs0)),
      P.ord_pow, P.ord_inv, hs, hq]
    simp
  -- Undo the normalization. The filtration also handles a vanishing remainder.
  have hfirst : u - ((a : F) / s) ^ n ∈ P.filtration (P.ord u + 1) := by
    have h := P.mul_mem_filtration hcancel hsinv
    have heq : (u * s ^ n - (a : F) ^ n) * s⁻¹ ^ n =
        u - ((a : F) / s) ^ n := by
      rw [div_pow, inv_pow]
      field_simp
    simpa only [heq, add_comm] using h
  -- The linear correction has strictly higher order than the original pole.
  have hsecond : (a : F) / s ∈ P.filtration (P.ord u + 1) := by
    have haint := P.mem_filtration_zero_iff.mpr a.2
    have hsint : s⁻¹ ∈ P.filtration q := by
      rw [P.mem_filtration_iff_le_ord (inv_ne_zero hs0), P.ord_inv, hs]
      omega
    have h := P.mul_mem_filtration haint hsint
    apply P.filtration_antitone (b := q)
    · rw [hq]
      nlinarith
    · simpa [div_eq_mul_inv] using h
  refine ⟨(a : F) / s, ?_⟩
  have hmem : u - (((a : F) / s) ^ n - (a : F) / s) ∈
      P.filtration (P.ord u + 1) := by
    rw [sub_sub_eq_add_sub]
    simpa only [add_sub_right_comm] using Submodule.add_mem _ hfirst hsecond
  rcases eq_or_ne (u - (((a : F) / s) ^ n - (a : F) / s)) 0 with hzero | hzero
  · simpa [hzero] using hu
  · have := (P.mem_filtration_iff_le_ord hzero).mp hmem
    omega

/-- Over a perfect residue field in characteristic `p`, every Artin–Schreier class has
an integral representative or a representative with negative order not divisible by `p`.
The substitution lies in `F` itself; no completion is used. -/
theorem exists_reduced_artinSchreier_representative (p : ℕ) [Fact p.Prime] [CharP F p]
    [PerfectField P.ResidueField] (u : F) :
    ∃ w : F, u - (w ^ p - w) ∈ P.integers ∨
      (P.ord (u - (w ^ p - w)) < 0 ∧ ¬(p : ℤ) ∣ P.ord (u - (w ^ p - w))) := by
  have : CharP P.integers p :=
    (ValuationSubring.subtype P.integers).charP (Subtype.val_injective) p
  have : CharP P.ResidueField p := by
    apply (CharP.charP_iff_prime_eq_zero Fact.out).mpr
    rw [← map_natCast (IsLocalRing.residue P.integers), CharP.cast_eq_zero, map_zero]
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  -- Each cancellation decreases the nonnegative pole order; corrections add by Frobenius.
  induction h : (-P.ord u).toNat using Nat.strong_induction_on generalizing u with
  | h n ih =>
    by_cases hint : u ∈ P.integers
    · exact ⟨0, by simpa [hp0] using Or.inl hint⟩
    have hu : P.ord u < 0 := by
      rw [P.mem_integers_iff_ord_nonneg] at hint
      omega
    by_cases hdiv : (p : ℤ) ∣ P.ord u
    · obtain ⟨w, hw⟩ := P.exists_ord_sub_pow_sub_self_gt_of_dvd_ord
        (Fact.out : p.Prime).one_lt (surjective_frobenius P.ResidueField p) hu hdiv
      have hlt : (-P.ord (u - (w ^ p - w))).toNat < n := by omega
      obtain ⟨z, hz⟩ := ih _ hlt (u - (w ^ p - w)) rfl
      refine ⟨w + z, ?_⟩
      have heq : u - ((w + z) ^ p - (w + z)) =
          (u - (w ^ p - w)) - (z ^ p - z) := by
        rw [add_pow_char]
        ring
      rwa [heq]
    · exact ⟨0, by simpa [hp0] using Or.inr ⟨hu, hdiv⟩⟩

end TauCeti.Place
