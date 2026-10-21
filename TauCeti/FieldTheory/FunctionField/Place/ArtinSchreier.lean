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

Over an imperfect residue field the reduction can fail.
`ord_sub_pow_le_of_forall_pow_ne_residue` shows that if the leading coefficient of `u` is not an
`n`-th power in the residue field, then no `y ^ n` agrees with `u` beyond the leading order of `u`.
So when `n` divides the pole order of `u`,
`not_exists_reduced_artinSchreier_representative_of_forall_pow_ne_residue` rules out every
reduced representative. At a place of degree one,
`not_exists_reduced_artinSchreier_representative_of_degree_eq_one` gives the explicit
obstruction `a / t ^ n` for a constant `a` that is not an `n`-th power in `k`. Thus the
perfectness hypothesis of `exists_reduced_artinSchreier_representative` cannot be dropped.

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

/-- Suppose the leading coefficient of `u`, read in the residue field after multiplying by
`s ^ n`, is not an `n`-th power. Then no `n`-th power `y ^ n` agrees with `u` beyond the
leading order of `u`. This complements the cancellation step
`exists_ord_sub_pow_sub_self_gt_of_dvd_ord`, which removes a leading term whose residue is an
`n`-th power. -/
theorem ord_sub_pow_le_of_forall_pow_ne_residue {n : ℕ} (hn : n ≠ 0) {u s : F}
    (hs : u * s ^ n ∈ P.integers)
    (hres : ∀ c : P.ResidueField, c ^ n ≠ IsLocalRing.residue P.integers ⟨u * s ^ n, hs⟩)
    (y : F) : P.ord (u - y ^ n) ≤ P.ord u := by
  by_contra! hlt
  have hus0 : u * s ^ n ≠ 0 := by
    intro h
    apply hres 0
    have h0 : (⟨u * s ^ n, hs⟩ : P.integers) = 0 := Subtype.ext h
    rw [zero_pow hn, h0, map_zero]
  have hu0 : u ≠ 0 := left_ne_zero_of_mul hus0
  have hsn0 : s ^ n ≠ 0 := right_ne_zero_of_mul hus0
  -- Multiplying `u - y ^ n` by `s ^ n` lands in the maximal ideal.
  have hdiff : u - y ^ n ∈ P.filtration (P.ord u + 1) := by
    rcases eq_or_ne (u - y ^ n) 0 with h | h
    · rw [h]
      exact zero_mem _
    · rw [P.mem_filtration_iff_le_ord h]
      omega
  have hord : 0 ≤ P.ord u + P.ord (s ^ n) := by
    rw [← P.ord_mul hu0 hsn0]
    exact P.mem_integers_iff_ord_nonneg.mp hs
  have hmem : (y * s) ^ n - u * s ^ n ∈ P.filtration 1 := by
    have h := P.mul_mem_filtration hdiff (P.mem_filtration_ord (s ^ n))
    rw [show (u - y ^ n) * s ^ n = -((y * s) ^ n - u * s ^ n) by ring, neg_mem_iff] at h
    exact P.filtration_antitone (by omega) h
  -- Hence `y * s` is integral, and its residue is an `n`-th root of the leading coefficient.
  have hys : y * s ∈ P.integers := by
    have hpow : (y * s) ^ n ∈ P.integers := by
      rw [← sub_add_cancel ((y * s) ^ n) (u * s ^ n)]
      exact add_mem (P.mem_filtration_zero_iff.mp (P.filtration_antitone zero_le_one hmem)) hs
    rw [P.mem_integers_iff_ord_nonneg, P.ord_pow] at hpow
    rw [P.mem_integers_iff_ord_nonneg]
    have : (0 : ℤ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    nlinarith
  apply hres (IsLocalRing.residue P.integers ⟨y * s, hys⟩)
  rw [← map_pow, P.residue_eq_iff_sub_mem_filtration_one]
  simpa using hmem

/-- **Reduction fails over an imperfect residue field.** Let `n > 1` divide the negative order
of `u`, and suppose the leading coefficient of `u`, read in the residue field after multiplying
by `s ^ n`, is not an `n`-th power. Then `u` has no reduced representative for the map
`w ↦ w ^ n - w`: no `u - (w ^ n - w)` is integral or has a pole of order prime to `n`.
For `n = p` in characteristic `p` this is the Artin–Schreier map, and this shows that
`exists_reduced_artinSchreier_representative` needs its perfect residue field. -/
theorem not_exists_reduced_artinSchreier_representative_of_forall_pow_ne_residue {n : ℕ}
    (hn : 1 < n) {u s : F} (hu : P.ord u < 0) (hdvd : (n : ℤ) ∣ P.ord u)
    (hs : u * s ^ n ∈ P.integers)
    (hres : ∀ c : P.ResidueField, c ^ n ≠ IsLocalRing.residue P.integers ⟨u * s ^ n, hs⟩) :
    ¬∃ w : F, u - (w ^ n - w) ∈ P.integers ∨
      (P.ord (u - (w ^ n - w)) < 0 ∧ ¬(n : ℤ) ∣ P.ord (u - (w ^ n - w))) := by
  rintro ⟨w, hw⟩
  obtain ⟨hneg, hdvd'⟩ := ord_sub_pow_sub_self_neg_and_dvd (v := P.valuation) hn
    (by rwa [ord_valuation]) (by rwa [ord_valuation])
    (by simpa only [ord_valuation] using
      P.ord_sub_pow_le_of_forall_pow_ne_residue (by omega) hs hres) w
  rw [ord_valuation] at hneg hdvd'
  rcases hw with hint | ⟨-, hndvd⟩
  · rw [P.mem_integers_iff_ord_nonneg] at hint
    exact hneg.not_ge hint
  · exact hndvd hdvd'

/-- **The explicit obstruction at a place of degree one.** If `a ∈ k` is not an `n`-th power
for some `n > 1`, and `t` vanishes at a place `P` of degree one, then `a / t ^ n` has no
reduced representative for the map `w ↦ w ^ n - w` at `P`. For `k = 𝔽_p(a)` and `n = p`, this
is the imperfect-residue counterexample to reducing Artin–Schreier representatives. -/
theorem not_exists_reduced_artinSchreier_representative_of_degree_eq_one (hP : P.degree = 1)
    {n : ℕ} (hn : 1 < n) {a : k} (ha : ∀ c : k, c ^ n ≠ a) {t : F} (ht : 0 < P.ord t) :
    ¬∃ w : F, algebraMap k F a / t ^ n - (w ^ n - w) ∈ P.integers ∨
      (P.ord (algebraMap k F a / t ^ n - (w ^ n - w)) < 0 ∧
        ¬(n : ℤ) ∣ P.ord (algebraMap k F a / t ^ n - (w ^ n - w))) := by
  have ha0 : algebraMap k F a ≠ 0 := by
    rw [map_ne_zero]
    rintro rfl
    exact ha 0 (zero_pow (by omega))
  have ht0 : t ≠ 0 := by
    rintro rfl
    simp at ht
  have hord : P.ord (algebraMap k F a / t ^ n) = n * -P.ord t := by
    rw [P.ord_div ha0 (pow_ne_zero _ ht0), P.ord_algebraMap, P.ord_pow]
    ring
  have hmul : algebraMap k F a / t ^ n * t ^ n = algebraMap k F a :=
    div_mul_cancel₀ _ (pow_ne_zero _ ht0)
  have hs : algebraMap k F a / t ^ n * t ^ n ∈ P.integers := by
    rw [hmul]
    exact P.algebraMap_mem_integers a
  refine P.not_exists_reduced_artinSchreier_representative_of_forall_pow_ne_residue hn
    (s := t) (by rw [hord]; nlinarith) ⟨-P.ord t, hord⟩
    hs ?_
  -- The leading coefficient is the residue of the constant `a`.
  intro c hc
  obtain ⟨c, rfl⟩ := (P.degree_eq_one_iff_algebraMap_surjective).mp hP c
  have hres : IsLocalRing.residue P.integers ⟨algebraMap k F a / t ^ n * t ^ n, hs⟩ =
      algebraMap k P.ResidueField a := by
    rw [P.algebraMap_residueField]
    congr 1
    exact Subtype.ext hmul
  rw [hres, ← map_pow] at hc
  exact ha c ((algebraMap k P.ResidueField).injective hc)

end TauCeti.Place
