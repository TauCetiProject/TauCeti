/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# An effective count of ideals of bounded norm

In a number field `F` of degree `n`, the number of nonzero integral ideals of norm at most
`X` is at most `X² · 2ⁿ`. A nonzero ideal is encoded injectively as an `n`-tuple of positive
naturals with product `≤ absNorm I` (distributing, for each rational prime `p`, the value
`p^{vₚ}` of the `i`-th prime above `p` into the `i`-th coordinate); the valuations of the
tuple recover the ideal, and there are at most `X²·2ⁿ` such tuples.

Mathlib's `Ideal.finite_setOf_absNorm_le` already gives finiteness (and `Ideal/Asymptotics`
the sharp asymptotic `~ ρ·X`); the contribution here is the explicit elementary bound, the
input to the effective class-number estimate.

## Main results

* `TauCeti.NumberField.prodLeTuples_ncard_le`: at most `X²·2ⁿ` positive `n`-tuples of
  product `≤ X`.
* `TauCeti.NumberField.card_ideal_absNorm_le`: at most `X²·2^[F:ℚ]` nonzero ideals of norm
  `≤ X`.

## Provenance

Migrated from
[kim-em/erdos-unit-distance](https://github.com/kim-em/erdos-unit-distance), the
formalization of L. Alpöge's disproof of the uniform-constant Erdős unit-distance
conjecture, where this Rankin-style count fed the class-number bound.
-/

attribute [local instance] Classical.propDecidable

namespace TauCeti.NumberField

/-- The set of `n`-tuples of positive naturals with real product at most `X`. -/
def prodLeTuples (n : ℕ) (X : ℝ) : Set (Fin n → ℕ) :=
  {d : Fin n → ℕ | (∀ i, 0 < d i) ∧ (∏ i, (d i : ℝ)) ≤ X}

/-- The tuple set is finite: every coordinate lies in `[1, ⌊X⌋]`. -/
theorem prodLeTuples_finite (n : ℕ) (X : ℝ) : (prodLeTuples n X).Finite := by
  apply Set.Finite.subset (Set.finite_Icc (1 : Fin n → ℕ) (fun _ => ⌊X⌋₊))
  rintro d ⟨hpos, hprod⟩
  refine ⟨fun i => hpos i, fun i => Nat.le_floor ?_⟩
  exact le_trans (mod_cast Finset.single_le_prod' (fun a _ => hpos a) (Finset.mem_univ i)) hprod

/-- `∑_{j=1}^{N} 1/j² ≤ 2`, from the Basel sum `π²/6 < 2`. -/
theorem sum_one_div_sq_le_two (N : ℕ) :
    ∑ j ∈ Finset.Icc 1 N, (1 : ℝ) / (j : ℝ) ^ 2 ≤ 2 := by
  have hconv : ∑ j ∈ Finset.Icc 1 N, (1 : ℝ) / (j : ℝ) ^ 2 ≤ Real.pi ^ 2 / 6 := by
    simpa using sum_le_hasSum (Finset.Icc 1 N) (fun n _ => by positivity)
      (by simpa using hasSum_zeta_two)
  have hpi : Real.pi < 3.4 := by pi_upper_bound [7 / 5]
  nlinarith [hconv, Real.pi_pos, hpi]

/-
[elementary] The number of `n`-tuples of positive naturals with product at
most `X` is at most `X² · 2ⁿ`.  Proof by induction on `n`: split off the last
coordinate `j ∈ {1,…,⌊X⌋}`, bound the rest by `(X/j)² · 2ⁿ` via the inductive
hypothesis, and sum using `sum_one_div_sq_le_two`.
-/
theorem prodLeTuples_ncard_le (n : ℕ) {X : ℝ} (hX : 1 ≤ X) :
    ((prodLeTuples n X).ncard : ℝ) ≤ X ^ 2 * 2 ^ n := by
  induction n generalizing X with
  | zero =>
      have huniv : prodLeTuples 0 X = Set.univ := by
        ext d; simp [prodLeTuples, Subsingleton.elim d 0, hX]
      rw [huniv, Set.ncard_univ, Nat.card_unique, pow_zero, Nat.cast_one, mul_one]
      nlinarith [hX, sq_nonneg (X - 1)]
  | succ n ih =>
      -- Decompose by the last coordinate `j ∈ {1,…,⌊X⌋}`.
      have h_def : prodLeTuples (n + 1) X = ⋃ j ∈ Finset.Icc 1 ⌊X⌋₊,
          (fun e => Fin.snoc e j) '' (prodLeTuples n (X / j)) := by
        ext d; simp only [prodLeTuples, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_image,
          Finset.mem_Icc]
        constructor <;> intro h
        · refine ⟨d (Fin.last n), ⟨h.1 _, Nat.le_floor ?_⟩, Fin.init d, ⟨?_, ?_⟩,
            Fin.snoc_init_self d⟩
          · refine le_trans ?_ h.2
            rw [Fin.prod_univ_castSucc]
            exact le_mul_of_one_le_left (Nat.cast_nonneg _)
              (mod_cast Finset.one_le_prod' fun i _ => h.1 _)
          · exact fun i => h.1 _
          · rw [le_div_iff₀ (mod_cast h.1 (Fin.last n))]
            rw [Fin.prod_univ_castSucc] at h
            simpa [Fin.init] using h.2
        · obtain ⟨j, ⟨hj1, hjX⟩, e, ⟨hepos, heprod⟩, rfl⟩ := h
          have hj0 : (0 : ℝ) < j := by exact_mod_cast (show 0 < j from hj1)
          refine ⟨fun i => ?_, ?_⟩
          · refine Fin.lastCases ?_ (fun i => ?_) i
            · rw [Fin.snoc_last]; exact hj1
            · rw [Fin.snoc_castSucc]; exact hepos i
          · rw [Fin.prod_univ_castSucc, Fin.snoc_last]
            simp only [Fin.snoc_castSucc]
            rw [le_div_iff₀ hj0] at heprod
            linarith [heprod]
      -- The biUnion's count is at most the sum of the parts' counts.
      have key : ∀ s : Finset ℕ, (⋃ j ∈ s, (fun e : Fin n → ℕ => (Fin.snoc e j : Fin (n + 1) → ℕ))
          '' (prodLeTuples n (X / j))).ncard ≤ ∑ j ∈ s, (prodLeTuples n (X / j)).ncard := by
        intro s
        induction s using Finset.induction with
        | empty => simp
        | insert a s ha ih2 =>
            rw [Finset.set_biUnion_insert, Finset.sum_insert ha]
            refine (Set.ncard_union_le _ _).trans (add_le_add ?_ ih2)
            exact Set.ncard_image_le (prodLeTuples_finite _ _)
      have h_ind : (prodLeTuples (n + 1) X).ncard ≤
          ∑ j ∈ Finset.Icc 1 ⌊X⌋₊, (prodLeTuples n (X / j)).ncard := by
        rw [h_def]; exact key _
      refine le_trans (Nat.cast_le.mpr h_ind) ?_
      push_cast
      refine le_trans (Finset.sum_le_sum fun i hi => ih ?_) ?_
      · rw [le_div_iff₀ (by exact_mod_cast (Finset.mem_Icc.mp hi).1)]
        simpa using le_trans (mod_cast (Finset.mem_Icc.mp hi).2) (Nat.floor_le (by linarith))
      · have h_sum : ∑ j ∈ Finset.Icc 1 ⌊X⌋₊, (X / (j : ℝ)) ^ 2 * 2 ^ n
            = X ^ 2 * 2 ^ n * ∑ j ∈ Finset.Icc 1 ⌊X⌋₊, (1 / (j : ℝ)) ^ 2 := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
        rw [h_sum, pow_succ]
        calc X ^ 2 * 2 ^ n * ∑ j ∈ Finset.Icc 1 ⌊X⌋₊, (1 / (j : ℝ)) ^ 2
            ≤ X ^ 2 * 2 ^ n * 2 :=
              mul_le_mul_of_nonneg_left (by simpa using sum_one_div_sq_le_two ⌊X⌋₊)
                (by positivity)
          _ = X ^ 2 * (2 ^ n * 2) := by ring

/-! ### Encoding ideals as tuples (for the Rankin-style ideal count)

We encode a nonzero ideal `I` of `𝓞 F` as an `n`-tuple of positive naturals
(`n = [F:ℚ]`) whose product is at most `absNorm I`, injectively.  For a nonzero
prime `P`, `ratBelow P` is the rational prime below `P` and `primeCoord P` is the
index of `P` among the (at most `n`) primes above that rational prime.  The
`i`-th coordinate of the encoding multiplies `(ratBelow P) ^ (mult of P in I)`
over all prime factors `P` of `I` with `primeCoord P = i`. -/
section RankinCount

open _root_.NumberField Ideal IsDedekindDomain UniqueFactorizationMonoid

noncomputable section

variable (F : Type) [Field F] [NumberField F]

/-- The rational prime below a prime ideal `P` of `𝓞 F`. -/
def ratBelow (P : Ideal (𝓞 F)) : ℕ := Ideal.absNorm (Ideal.under ℤ P)

/-- The coordinate (index in `Fin [F:ℚ]`) assigned to a prime ideal `P`: its
position in the list of primes above the rational prime below `P`. -/
def primeCoord (P : Ideal (𝓞 F)) : ℕ :=
  (IsDedekindDomain.primesOverFinset (Ideal.under ℤ P) (𝓞 F)).toList.idxOf P

/-- The `i`-th coordinate of the tuple encoding the ideal `I`. -/
def encodeIdeal (I : Ideal (𝓞 F)) (i : Fin (Module.finrank ℚ F)) : ℕ :=
  ∏ P ∈ (normalizedFactors I).toFinset.filter (fun P => primeCoord F P = i.val),
    (ratBelow F P) ^ ((normalizedFactors I).count P)

/-
[foundational] `P` belongs to the finite set of primes above the rational
prime below it.
-/
theorem mem_primesOverFinset_under {P : Ideal (𝓞 F)} (hP : P.IsPrime) (hP0 : P ≠ ⊥) :
    P ∈ IsDedekindDomain.primesOverFinset (Ideal.under ℤ P) (𝓞 F) := by
  -- Since P is a prime ideal in O_F, we have that P is maximal in O_F.
  have hP_max : P.IsMaximal := Ideal.IsPrime.isMaximal hP hP0
  rw [ IsDedekindDomain.mem_primesOverFinset_iff ];
  · constructor;
    · exact hP;
    · constructor;
      rfl;
  · exact Ideal.under_ne_bot (A := ℤ) hP0

/-
[foundational] The coordinate of a nonzero prime ideal is `< [F:ℚ]`.
-/
theorem primeCoord_lt {P : Ideal (𝓞 F)} (hP : P.IsPrime) (hP0 : P ≠ ⊥) :
    primeCoord F P < Module.finrank ℚ F := by
  have hmax : (Ideal.under ℤ P).IsMaximal :=
    Ideal.IsPrime.isMaximal (IsPrime.under ℤ P) (Ideal.under_ne_bot (A := ℤ) hP0)
  calc primeCoord F P
      < (IsDedekindDomain.primesOverFinset (Ideal.under ℤ P) (𝓞 F)).toList.length := by
        rw [primeCoord]
        exact List.idxOf_lt_length_iff.mpr
          (Finset.mem_toList.mpr (mem_primesOverFinset_under F hP hP0))
    _ = (IsDedekindDomain.primesOverFinset (Ideal.under ℤ P) (𝓞 F)).card := Finset.length_toList _
    _ ≤ Module.finrank ℚ F :=
        Ideal.card_primesOverFinset_le_finrank (𝓞 F) ℚ F (Ideal.under_ne_bot (A := ℤ) hP0)

/-
[foundational] `ratBelow` injectivity: equal `ratBelow` means the primes lie
over the same rational prime, hence have the same `IsDedekindDomain.primesOverFinset`.
-/
omit [NumberField F] in
theorem under_eq_of_ratBelow_eq {P Q : Ideal (𝓞 F)} (hP : P.IsPrime) (hP0 : P ≠ ⊥)
    (hQ : Q.IsPrime) (hQ0 : Q ≠ ⊥) (hr : ratBelow F P = ratBelow F Q) :
    Ideal.under ℤ P = Ideal.under ℤ Q := by
  have hr' : Ideal.absNorm (Ideal.under ℤ P) = Ideal.absNorm (Ideal.under ℤ Q) := hr
  have hr'' : ∀ {J : Ideal ℤ}, J ≠ ⊥ → J.IsPrime → J = Ideal.span {(Ideal.absNorm J : ℤ)} := by
    simp_all +decide
  haveI := hP; haveI := hQ
  rw [hr'' (Ideal.under_ne_bot (A := ℤ) hP0) (IsPrime.under ℤ P),
    hr'' (Ideal.under_ne_bot (A := ℤ) hQ0) (IsPrime.under ℤ Q), hr']

/-
[foundational] Two nonzero primes over the same rational prime with the same
coordinate are equal.
-/
theorem prime_eq_of_coord_eq {P Q : Ideal (𝓞 F)} (hP : P.IsPrime) (hP0 : P ≠ ⊥)
    (hQ : Q.IsPrime) (hQ0 : Q ≠ ⊥) (hr : ratBelow F P = ratBelow F Q)
    (hc : primeCoord F P = primeCoord F Q) : P = Q := by
  have hUeq : Ideal.under ℤ P = Ideal.under ℤ Q := under_eq_of_ratBelow_eq F hP hP0 hQ hQ0 hr
  set l := (IsDedekindDomain.primesOverFinset (Ideal.under ℤ P) (𝓞 F)).toList with hl
  have hPl : P ∈ l := Finset.mem_toList.mpr (mem_primesOverFinset_under F hP hP0)
  have hQl : Q ∈ l := by
    rw [hl, hUeq]
    exact Finset.mem_toList.mpr (mem_primesOverFinset_under F hQ hQ0)
  have hidx : l.idxOf P = l.idxOf Q := by
    have hQ' : l.idxOf Q = primeCoord F Q := by rw [primeCoord, hl, hUeq]
    rw [show l.idxOf P = primeCoord F P from rfl, hQ', hc]
  have hgen : ∀ {m : List (Ideal (𝓞 F))}, ∀ {x y : Ideal (𝓞 F)}, x ∈ m → y ∈ m →
      m.idxOf x = m.idxOf y → x = y := by
    intro m x y hx hy hxy
    induction m <;> simp_all +decide [List.idxOf_cons]
    grind
  exact hgen hPl hQl hidx

/-
The factors in `normalizedFactors I` are nonzero primes.
-/
theorem isPrime_of_mem_normalizedFactors {I P : Ideal (𝓞 F)} (hI : I ≠ ⊥)
    (hP : P ∈ normalizedFactors I) : P.IsPrime ∧ P ≠ ⊥ := by
  grind +suggestions

/-
[foundational] Each coordinate of the encoding of a nonzero ideal is positive.
-/
theorem encodeIdeal_pos {I : Ideal (𝓞 F)} (hI : I ≠ ⊥)
    (i : Fin (Module.finrank ℚ F)) : 0 < encodeIdeal F I i := by
  refine Finset.prod_pos fun P hP => ?_
  rw [Finset.mem_filter, Multiset.mem_toFinset] at hP
  have hPp := isPrime_of_mem_normalizedFactors F hI hP.1
  haveI := hPp.1
  haveI : NeZero P := ⟨hPp.2⟩
  exact pow_pos (by simpa [ratBelow] using (Nat.absNorm_under_prime P).pos) _

/-
Regrouping: the product of all coordinates is the product over all prime
factors of `(ratBelow P) ^ (mult of P)`.
-/
theorem prod_encodeIdeal_eq {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) :
    ∏ i, encodeIdeal F I i =
      ∏ P ∈ (normalizedFactors I).toFinset,
        (ratBelow F P) ^ ((normalizedFactors I).count P) := by
  have h_sum : ∏ i : Fin (Module.finrank ℚ F), encodeIdeal F I i =
      ∏ P ∈ (normalizedFactors I).toFinset, ∏ i : Fin (Module.finrank ℚ F),
        if primeCoord F P = i.val then (ratBelow F P) ^ ((normalizedFactors I).count P) else 1 := by
    rw [Finset.prod_comm, Finset.prod_congr rfl]
    unfold encodeIdeal
    simp +decide [Finset.prod_ite]
  rw [h_sum]
  refine Finset.prod_congr rfl fun P hP => ?_
  have hPp := isPrime_of_mem_normalizedFactors F hI (Multiset.mem_toFinset.mp hP)
  rw [Finset.prod_eq_single ⟨primeCoord F P, primeCoord_lt F hPp.1 hPp.2⟩] <;> aesop

/-
The product of the encoding coordinates is at most `absNorm I`.
-/
theorem prod_encodeIdeal_le_absNorm {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) :
    ∏ i, encodeIdeal F I i ≤ Ideal.absNorm I := by
  rw [prod_encodeIdeal_eq F hI]
  have h_prod_le : ∏ P ∈ (normalizedFactors I).toFinset,
      (Ideal.absNorm P) ^ ((normalizedFactors I).count P) ≤ Ideal.absNorm I := by
    have h_prod_le : ∏ P ∈ (normalizedFactors I).toFinset,
          (Ideal.absNorm P) ^ ((normalizedFactors I).count P)
        = Ideal.absNorm (∏ P ∈ (normalizedFactors I).toFinset,
          P ^ ((normalizedFactors I).count P)) := by
      induction (normalizedFactors I).toFinset using Finset.induction <;>
        simp_all +decide [Finset.prod_insert]
    convert h_prod_le.le using 2;
    convert ( Ideal.prod_normalizedFactors_eq_self hI ) |> Eq.symm;
    rw [ Finset.prod_multiset_count ];
  refine le_trans ?_ h_prod_le
  gcongr with Q hQ
  have hQp := isPrime_of_mem_normalizedFactors F hI (Multiset.mem_toFinset.mp hQ)
  exact Nat.le_of_dvd (Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hQp.2))
    (by simpa [ratBelow] using Int.absNorm_under_dvd_absNorm Q)

/-
Recovery: the multiplicity of a prime `P` in `I` is the `ratBelow P`-adic
valuation of the `primeCoord P` coordinate of the encoding.
-/
theorem count_eq_padicValNat {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) {P : Ideal (𝓞 F)}
    (hP : P.IsPrime) (hP0 : P ≠ ⊥) :
    (normalizedFactors I).count P =
      padicValNat (ratBelow F P)
        (encodeIdeal F I ⟨primeCoord F P, primeCoord_lt F hP hP0⟩) := by
  classical
  haveI := hP
  haveI : NeZero P := ⟨hP0⟩
  have hpp : (ratBelow F P).Prime := by simpa [ratBelow] using Nat.absNorm_under_prime P
  have hfact : ∀ Q ∈ (normalizedFactors I).toFinset.filter
      (fun Q => primeCoord F Q = primeCoord F P),
      (ratBelow F Q) ^ ((normalizedFactors I).count Q) ≠ 0 := by
    intro Q hQ
    rw [Finset.mem_filter, Multiset.mem_toFinset] at hQ
    have hQp := isPrime_of_mem_normalizedFactors F hI hQ.1
    haveI := hQp.1
    haveI : NeZero Q := ⟨hQp.2⟩
    exact pow_ne_zero _ (by simpa [ratBelow] using (Nat.absNorm_under_prime Q).pos.ne')
  rw [eq_comm, ← Nat.factorization_def _ hpp]
  simp only [encodeIdeal]
  rw [Nat.factorization_prod hfact]
  rw [Finset.sum_apply']
  rw [Finset.sum_eq_single P]
  · rw [hpp.factorization_pow, Finsupp.single_apply]
    simp
  · intro Q hQ hQP
    rw [Finset.mem_filter, Multiset.mem_toFinset] at hQ
    have hQp := isPrime_of_mem_normalizedFactors F hI hQ.1
    have hrb : ratBelow F Q ≠ ratBelow F P := fun h =>
      hQP (prime_eq_of_coord_eq F hQp.1 hQp.2 hP hP0 h hQ.2)
    haveI := hQp.1
    haveI : NeZero Q := ⟨hQp.2⟩
    have hQbelow : (ratBelow F Q).Prime := by simpa [ratBelow] using Nat.absNorm_under_prime Q
    rw [hQbelow.factorization_pow, Finsupp.single_apply]
    simp [hrb]
  · intro hPnot
    rw [Finset.mem_filter, Multiset.mem_toFinset] at hPnot
    rw [not_and] at hPnot
    have hPmem : P ∉ normalizedFactors I := fun hmem => (hPnot hmem) rfl
    rw [Multiset.count_eq_zero_of_notMem hPmem]
    simp

/-
[foundational] The encoding is injective on nonzero ideals.
-/
theorem encodeIdeal_injOn :
    Set.InjOn (encodeIdeal F) {I : Ideal (𝓞 F) | I ≠ ⊥} := by
  intro I hI J hJ h_eq
  -- The multiplicity of every nonzero prime is recovered from the encoding, so it agrees.
  have hcount : ∀ {P : Ideal (𝓞 F)}, P.IsPrime → P ≠ ⊥ →
      (normalizedFactors I).count P = (normalizedFactors J).count P := by
    intro P hPp hP0
    rw [count_eq_padicValNat F hI hPp hP0, count_eq_padicValNat F hJ hPp hP0, h_eq]
  -- Hence the factor multisets agree, hence the ideals.
  have hms : normalizedFactors I = normalizedFactors J := by
    refine Multiset.ext.mpr fun P => ?_
    by_cases hmem : P ∈ normalizedFactors I ∨ P ∈ normalizedFactors J
    · obtain hP | hP := hmem
      · obtain ⟨hPp, hP0⟩ := isPrime_of_mem_normalizedFactors F hI hP
        exact hcount hPp hP0
      · obtain ⟨hPp, hP0⟩ := isPrime_of_mem_normalizedFactors F hJ hP
        exact hcount hPp hP0
    · rw [not_or] at hmem
      rw [Multiset.count_eq_zero_of_notMem hmem.1, Multiset.count_eq_zero_of_notMem hmem.2]
  rw [← Ideal.prod_normalizedFactors_eq_self hI, ← Ideal.prod_normalizedFactors_eq_self hJ, hms]

end

end RankinCount

open _root_.NumberField in
/-- [hard] Injection from nonzero integral ideals of norm `≤ X` into the
`n`-tuples of positive naturals with product `≤ X` (`n = [F:ℚ]`).  Each ideal
`I = ∏_𝔭 𝔭^{v_𝔭}` is encoded by distributing, for every rational prime `p`,
the exponent `v_{𝔭_i}(I)` of the `i`-th prime above `p` into `f(𝔭_i)`
coordinates as the value `p^{v_{𝔭_i}(I)}`; since `∑_{𝔭∣p} e_𝔭 f_𝔭 = [F:ℚ]`
there are at most `n` coordinates used per prime and the resulting tuple has
product `absNorm I`.  The map is injective because the `p`-adic valuations of
the tuple recover all `v_𝔭(I)`, hence `I`. -/
theorem ideal_ncard_le_prodLeTuples_ncard (F : Type) [Field F] [NumberField F]
    {X : ℝ} :
    {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ X}.ncard ≤
      (prodLeTuples (Module.finrank ℚ F) X).ncard := by
  classical
  refine Set.ncard_le_ncard_of_injOn (encodeIdeal F) ?_ ?_ (prodLeTuples_finite _ _)
  · rintro I ⟨hI0, hIX⟩
    refine ⟨fun i => encodeIdeal_pos F hI0 i, ?_⟩
    calc (∏ i, (encodeIdeal F I i : ℝ))
        = ((∏ i, encodeIdeal F I i : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (Ideal.absNorm I : ℝ) := by exact_mod_cast prod_encodeIdeal_le_absNorm F hI0
      _ ≤ X := hIX
  · intro I hI J hJ h
    exact encodeIdeal_injOn F hI.1 hJ.1 h

open _root_.NumberField in
/-- [HARD] **Rankin-style ideal count.**  In any number field `F` of degree
`n`, the number of nonzero integral ideals of norm at most `X` is at most
`X² · 2^n`.  Sketch: `∑_{N𝔞 ≤ X} 1 ≤ X² ∑_{𝔞} N𝔞⁻²`, and by unique
factorization into primes (with at most `n` primes above each rational `p`,
each of norm `≥ p`), `∑_𝔞 N𝔞⁻² ≤ ∏_{p ≤ X} (1 - p⁻²)⁻ⁿ ≤ ζ(2)ⁿ ≤ 2ⁿ`,
restricting to ideals supported above primes `≤ X`.  This is the main
genuinely-new counting argument needed from the algebraic side. -/
theorem card_ideal_absNorm_le (F : Type) [Field F] [NumberField F]
    {X : ℝ} (hX : 1 ≤ X) :
    {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ X}.Finite ∧
      (({I : Ideal (𝓞 F) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ X}.ncard : ℝ)) ≤
        X ^ 2 * 2 ^ Module.finrank ℚ F := by
  refine ⟨?_, ?_⟩
  · apply Set.Finite.subset (Ideal.finite_setOf_absNorm_le ⌊X⌋₊)
    rintro I ⟨-, hI⟩
    exact Nat.le_floor hI
  · calc ((({I : Ideal (𝓞 F) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ X}).ncard : ℝ))
        ≤ ((prodLeTuples (Module.finrank ℚ F) X).ncard : ℝ) := by
          exact_mod_cast ideal_ncard_le_prodLeTuples_ncard F (X := X)
      _ ≤ X ^ 2 * 2 ^ Module.finrank ℚ F := prodLeTuples_ncard_le _ hX

end TauCeti.NumberField
