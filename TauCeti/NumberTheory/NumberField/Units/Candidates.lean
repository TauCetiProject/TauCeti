/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Units.Regulator
import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Mathlib.Topology.Algebra.Polynomial
import TauCeti.Algebra.Polynomial.Card.BoundedCoeff
import TauCeti.NumberTheory.NumberField.Index.PowerBasis
import TauCeti.NumberTheory.NumberField.Minpoly
import TauCeti.NumberTheory.NumberField.Units.PrimeDegree

/-!
# Candidate minimal polynomials for units in rank one

Let `K` be a number field of unit rank one and degree `n`. A unit `v` generating `K` over `ℚ`
whose value at a real infinite place lies between `1` and `B` has all its other conjugates of
absolute value at most `1`, so its minimal polynomial over `ℤ` is a monic polynomial of degree
`n` with constant coefficient `±1` whose coefficient of `X ^ (n - k)` is at most
`C(n-1, k-1) B + C(n-1, k)` in absolute value. `unitCandidates K B` is the finite set of all such
polynomials; the minimal polynomial of every generating unit in the interval belongs to it, and
at prime degree every unit in the interval generates `K`.

In degree `2` the candidates are `X² + mX ± 1` with `|m| ≤ B + 1`; in degree `3` they are
`X³ + aX² + bX ± 1` with `|a| ≤ B + 2` and `|b| ≤ 2B + 1`. The enumeration is intentionally an
overapproximation: a later root test and field test eliminate candidates that cannot be units
in the given field.

## Main results

* `TauCeti.NumberField.Units.unitCandidates`: the finite set of candidate minimal polynomials,
  characterised by `TauCeti.NumberField.Units.mem_unitCandidates_iff`.
* `TauCeti.NumberField.Units.minpoly_mem_unitCandidates`: completeness of the candidate set at
  unit rank one and prime degree.

## References

* H. Cohen, *A Course in Computational Algebraic Number Theory*, §5.7.
-/

public section

open Polynomial NumberField NumberField.InfinitePlace NumberField.Units TauCeti.NumberField
open scoped NumberField

namespace TauCeti.NumberField.Units

variable (K : Type*) [Field K] [NumberField K]

/-- The set of monic integer polynomials of degree `[K : ℚ]` with constant coefficient `±1`
and the coefficient bounds of `unitCandidates` is finite. -/
private theorem finite_setOf_unitCandidate (B : ℝ) :
    {f : ℤ[X] | f.Monic ∧ f.natDegree = Module.finrank ℚ K ∧ (f.coeff 0 = 1 ∨ f.coeff 0 = -1) ∧
      ∀ k, 0 < k → k < Module.finrank ℚ K →
        |(f.coeff (Module.finrank ℚ K - k) : ℝ)| ≤
          (Module.finrank ℚ K - 1).choose (k - 1) * B +
            (Module.finrank ℚ K - 1).choose k}.Finite := by
  set n := Module.finrank ℚ K
  -- A uniform bound on every coefficient.
  set M : ℕ := ⌈(2 : ℝ) ^ (n - 1) * (|B| + 1)⌉₊
  have hM1 : (1 : ℝ) ≤ 2 ^ (n - 1) * (|B| + 1) :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ one_le_two) (by linarith [abs_nonneg B])
  refine (TauCeti.Polynomial.finite_setOf_natDegree_le_abs_intCoeff_le n M).subset ?_
  rintro f ⟨hmonic, hdeg, h0, hk⟩
  refine ⟨hdeg.le, fun i => ?_⟩
  suffices h : |(f.coeff i : ℝ)| ≤ 2 ^ (n - 1) * (|B| + 1) by
    have hM : |(f.coeff i : ℝ)| ≤ (M : ℝ) := h.trans (Nat.le_ceil _)
    exact_mod_cast hM
  rcases lt_trichotomy i n with hi | rfl | hi
  · rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rcases h0 with h0 | h0 <;> rw [h0] <;> simpa using hM1
    · have := hk (n - i) (Nat.sub_pos_of_lt hi) (by omega)
      rw [Nat.sub_sub_self hi.le] at this
      refine this.trans ?_
      have hc1 : ((n - 1).choose (n - i - 1) : ℝ) ≤ 2 ^ (n - 1) := by
        exact_mod_cast Nat.choose_le_two_pow _ _
      have hc2 : ((n - 1).choose (n - i) : ℝ) ≤ 2 ^ (n - 1) := by
        exact_mod_cast Nat.choose_le_two_pow _ _
      have hB : B ≤ |B| := le_abs_self B
      have hB0 : 0 ≤ |B| := abs_nonneg B
      have h2 : (0 : ℝ) ≤ 2 ^ (n - 1) := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hB (Nat.cast_nonneg ((n - 1).choose (n - i - 1)))]
  · have h1 : f.coeff n = 1 := by rw [← hdeg]; exact hmonic.coeff_natDegree
    rw [h1]
    simpa using hM1
  · rw [coeff_eq_zero_of_natDegree_lt (hdeg ▸ hi)]
    simpa using zero_le_one.trans hM1

/-- The finite list of monic integer polynomials of degree `n = [K : ℚ]` with constant
coefficient `±1` whose coefficient of `X ^ (n - k)`, for `0 < k < n`, is at most
`C(n-1, k-1) B + C(n-1, k)` in absolute value. -/
noncomputable def unitCandidates (B : ℝ) : Finset ℤ[X] :=
  (finite_setOf_unitCandidate K B).toFinset

variable {K}

/-- Membership in the candidate list is exactly monicity, field degree, constant coefficient
`±1`, and the binomial coefficient bounds. -/
@[simp]
theorem mem_unitCandidates_iff (f : ℤ[X]) (B : ℝ) :
    f ∈ unitCandidates K B ↔
      f.Monic ∧ f.natDegree = Module.finrank ℚ K ∧ (f.coeff 0 = 1 ∨ f.coeff 0 = -1) ∧
        ∀ k, 0 < k → k < Module.finrank ℚ K →
          |(f.coeff (Module.finrank ℚ K - k) : ℝ)| ≤
            (Module.finrank ℚ K - 1).choose (k - 1) * B + (Module.finrank ℚ K - 1).choose k :=
  Set.Finite.mem_toFinset _

/-- Every unit generating `K` over `ℚ` whose value at a real infinite place lies in `(1, B]`
has its minimal polynomial in `unitCandidates K B` when the unit rank is one. -/
theorem minpoly_mem_unitCandidates_of_adjoin_eq_top (hr : rank K = 1)
    {w : InfinitePlace K} (hw : w.IsReal) (v : (𝓞 K)ˣ)
    (hgen : Algebra.adjoin ℚ {((v : 𝓞 K) : K)} = ⊤) {B : ℝ}
    (hlo : 1 < w.embedding_of_isReal hw (v : K))
    (hhi : w.embedding_of_isReal hw (v : K) ≤ B) :
    minpoly ℤ (v : 𝓞 K) ∈ unitCandidates K B := by
  classical
  set n := Module.finrank ℚ K with hn
  have hwv : w v = w.embedding_of_isReal hw v := by
    rw [← norm_embedding_of_isReal hw, Real.norm_eq_abs, abs_of_pos (zero_lt_one.trans hlo)]
  have hw1 : 1 < w v := hwv ▸ hlo
  have hwB : w v ≤ B := hwv ▸ hhi
  let θ : IntegralPrimitiveElement K := ⟨v, hgen⟩
  have hintQ : IsIntegral ℚ (v : K) := IsIntegral.of_finite ℚ _
  -- The minimal polynomial over `ℚ` is the one over `ℤ`, and has degree `n`.
  have hQ : minpoly ℚ (v : K) = (minpoly ℤ (v : 𝓞 K)).map (algebraMap ℤ ℚ) :=
    RingOfIntegers.minpoly_rat_coe (v : 𝓞 K)
  have hdegQ : (minpoly ℚ (v : K)).natDegree = n := by
    have h := θ.powerBasis.natDegree_minpoly
    rwa [IntegralPrimitiveElement.powerBasis_gen, ← θ.powerBasis.finrank] at h
  have hdeg : (minpoly ℤ (v : 𝓞 K)).natDegree = n := by
    rw [← hdegQ, hQ, natDegree_map_eq_of_injective (algebraMap ℤ ℚ).injective_int]
  refine (mem_unitCandidates_iff _ B).mpr ⟨minpoly.monic (v : 𝓞 K).isIntegral, hdeg,
    coeff_zero_minpoly_eq_one_or_neg_one v, fun k hk hkn => ?_⟩
  -- Work over `ℂ`, where the minimal polynomial is the product over the embeddings.
  set p : ℂ[X] := (minpoly ℚ (v : K)).map (algebraMap ℚ ℂ) with hpdef
  have hpmonic : p.Monic := (minpoly.monic hintQ).map _
  have hp0 : p ≠ 0 := hpmonic.ne_zero
  have hroots : ∀ z, z ∈ p.roots ↔ ∃ φ : K →+* ℂ, φ v = z := fun z => by
    rw [mem_roots hp0, IsRoot.def, hpdef, eval_map, ← aeval_def]
    have h := Set.ext_iff.mp (Embeddings.range_eval_eq_rootSet_minpoly K ℂ (v : K)) z
    rw [Set.mem_range, mem_rootSet_of_ne (minpoly.ne_zero hintQ)] at h
    exact h.symm
  have hpcard : p.roots.card = n := by
    rw [← (IsAlgClosed.splits p).natDegree_eq_card_roots, hpdef,
      natDegree_map_eq_of_injective (algebraMap ℚ ℂ).injective, hdegQ]
  have hnodup : p.roots.Nodup := nodup_roots ((minpoly.irreducible hintQ).separable.map)
  -- The real root, and the factor it accounts for.
  set r : ℂ := embedding w v
  have hr_root : r ∈ p.roots := (hroots r).mpr ⟨embedding w, rfl⟩
  have hr_norm : ‖r‖ = w v := norm_embedding_eq w _
  set s : Multiset ℂ := p.roots.erase r with hs
  set q : ℂ[X] := (s.map fun a => X - C a).prod with hq
  have hpq : p = (X - C r) * q := by
    have h : p = ((r ::ₘ s).map fun a => X - C a).prod := by
      rw [hs, Multiset.cons_erase hr_root, prod_multiset_X_sub_C_of_monic_of_roots_card_eq hpmonic
        (by rw [hpcard, hpdef, natDegree_map_eq_of_injective (algebraMap ℚ ℂ).injective, hdegQ])]
    rw [h, Multiset.map_cons, Multiset.prod_cons]
  have hqmonic : q.Monic := monic_multiset_prod_of_monic _ _ fun a _ => monic_X_sub_C a
  have hqroots : q.roots = s := roots_multiset_prod_X_sub_C s
  have hqsplits : q.Splits := Splits.multisetProd fun f hf => by
    obtain ⟨a, -, rfl⟩ := Multiset.mem_map.mp hf
    exact Splits.X_sub_C a
  have hqdeg : q.natDegree = n - 1 := by
    rw [hqsplits.natDegree_eq_card_roots, hqroots, hs, Multiset.card_erase_of_mem hr_root, hpcard,
      Nat.pred_eq_sub_one]
  -- The other roots are the values of `v` at the other embeddings, of absolute value `< 1`.
  have hqbound : ∀ z ∈ q.roots, ‖z‖ ≤ 1 := by
    intro z hz
    rw [hqroots, hs, hnodup.mem_erase_iff] at hz
    obtain ⟨φ, rfl⟩ := (hroots z).mp hz.2
    have hne : InfinitePlace.mk φ ≠ w := by
      intro hφ
      rw [← mk_embedding w, mk_eq_iff] at hφ
      rcases hφ with hφ | hφ
      · exact hz.1 (DFunLike.congr_fun hφ _)
      · have hreal : ComplexEmbedding.conjugate (embedding w) = embedding w :=
          ComplexEmbedding.isReal_iff.mp (isReal_iff.mp hw)
        have hφ' : φ = embedding w := by
          rw [← ComplexEmbedding.involutive_conjugate K φ, hφ, hreal]
        exact hz.1 (DFunLike.congr_fun hφ' _)
    exact (lt_one_of_rank_eq_one_of_ne_of_one_lt hr hne hw1).le
  have hqcoeff : ∀ j, ‖q.coeff j‖ ≤ (n - 1).choose j := fun j => by
    have h := coeff_le_of_roots_le (f := RingHom.id ℂ) (B := 1) j hqmonic
      (by rwa [map_id]) (by rwa [map_id])
    rwa [map_id, one_pow, one_mul, hqdeg] at h
  -- Assemble the bound on the coefficient of `X ^ (n - k)`.
  have hcoeff : ((minpoly ℤ (v : 𝓞 K)).coeff (n - k) : ℂ) = p.coeff (n - k) := by
    rw [hpdef, hQ, Polynomial.map_map, coeff_map, ← IsScalarTower.algebraMap_eq, eq_intCast]
  have hsplit : p.coeff (n - k) = q.coeff (n - k - 1) - r * q.coeff (n - k) := by
    obtain ⟨a, ha⟩ : ∃ a, n - k = a + 1 := ⟨n - k - 1, by omega⟩
    rw [hpq, ha, Nat.add_sub_cancel, coeff_X_sub_C_mul]
  have hidx1 : n - k - 1 = n - 1 - k := by omega
  have hidx2 : n - k = n - 1 - (k - 1) := by omega
  have hsym1 : (n - 1).choose (n - k - 1) = (n - 1).choose k := by
    rw [hidx1, Nat.choose_symm (Nat.le_sub_one_of_lt hkn)]
  have hsym2 : (n - 1).choose (n - k) = (n - 1).choose (k - 1) := by
    rw [hidx2, Nat.choose_symm (Nat.sub_le_sub_right hkn.le 1)]
  have hfinal : ‖p.coeff (n - k)‖ ≤ (n - 1).choose (k - 1) * B + (n - 1).choose k := by
    rw [hsplit]
    calc ‖q.coeff (n - k - 1) - r * q.coeff (n - k)‖
        ≤ ‖q.coeff (n - k - 1)‖ + ‖r‖ * ‖q.coeff (n - k)‖ := by
          rw [← norm_mul]; exact norm_sub_le _ _
      _ ≤ (n - 1).choose k + B * (n - 1).choose (k - 1) := by
          refine add_le_add (by rw [← hsym1]; exact hqcoeff _) (mul_le_mul (hr_norm ▸ hwB)
            (by rw [← hsym2]; exact hqcoeff _) (norm_nonneg _) (by linarith))
      _ = (n - 1).choose (k - 1) * B + (n - 1).choose k := by ring
  rw [← Complex.norm_intCast, hcoeff]
  exact hfinal

/-- Every unit whose value at a real infinite place lies in `(1, B]` has its minimal polynomial
in `unitCandidates K B` when the unit rank is one and the field degree is prime. -/
theorem minpoly_mem_unitCandidates (hr : rank K = 1)
    (hp : Nat.Prime (Module.finrank ℚ K)) {w : InfinitePlace K} (hw : w.IsReal)
    (v : (𝓞 K)ˣ) {B : ℝ}
    (hlo : 1 < w.embedding_of_isReal hw (v : K))
    (hhi : w.embedding_of_isReal hw (v : K) ≤ B) :
    minpoly ℤ (v : 𝓞 K) ∈ unitCandidates K B := by
  have hnot : v ∉ torsion K := by
    intro hv
    have hvone := (NumberField.Units.mem_torsion (x := v)).mp hv w
    have hval : w v = w.embedding_of_isReal hw (v : K) := by
      rw [← InfinitePlace.norm_embedding_of_isReal hw, Real.norm_eq_abs,
        abs_of_pos (lt_trans zero_lt_one hlo)]
    exact (ne_of_gt hlo) (hval ▸ hvone)
  exact minpoly_mem_unitCandidates_of_adjoin_eq_top hr hw v
    (adjoin_eq_top_of_finrank_prime hp hnot) hlo hhi

end TauCeti.NumberField.Units
