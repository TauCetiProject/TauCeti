/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.FreeProbability.Cumulant.S.Basic
import TauCeti.Algebra.BigOperators.Finset.Range
import TauCeti.Data.Finset.Sort
import TauCeti.RingTheory.PowerSeries.Substitution

/-!
# The S-series of a product of free elements

Let `φ : A →ₗ[R] R` be a normalised linear functional on an algebra over a commutative ring, and
let `a` and `b` lie in two different members of a freely independent family of subalgebras. If the
means `φ a` and `φ b` are units, then so is `φ (a b) = φ a φ b`, and the formal S-series are
multiplicative:

`S_{ab}(z) = S_a(z) S_b(z)`.

No traciality of `φ` is needed. Along the way, the moments of `a b` and `b a` agree,
`φ ((a b)ⁿ) = φ ((b a)ⁿ)`, again without a trace.

The proof expands the moments of the alternating words `a b a b ⋯` by the moment–cumulant formula
according to the part through the first position. Mixed free cumulants vanish, so that part only
contains positions of `a`, and the words between its consecutive positions, and after its last
one, begin with `b`. Writing `M_{ab}` for the moment series of `a b`, `C_a` for the free cumulant
series and `R_a` for the R-series of `a`, and

`P(z) = ∑_{m ≥ 0} φ ((b a)ᵐ b) zᵐ` and `Q(z) = ∑_{m ≥ 0} φ ((a b)ᵐ a) zᵐ`,

this gives the functional equations

`M_{ab}(z) = C_a(z P(z))` and `Q(z) = R_a(z P(z)) M_{ba}(z)`,

together with the same equations with `a` and `b` exchanged. With `u = z P` and `v = z Q` they
give `u v = z (M_{ba} - 1) M_{ab} = z (M_{ab} - 1) M_{ba}`, whence `M_{ab} = M_{ba}`. Substituting
the compositional inverse of `Ψ = M_{ab} - 1` turns `u` and `v` into the compositional inverses
`z S_a` and `z S_b` of `C_a - 1` and `C_b - 1`, and `u v = z Ψ (1 + Ψ)` into
`z² S_a S_b = z (1 + z) Ψ⁻¹ = z² S_{ab}`.

## Main results

* `TauCeti.IsFreelyIndependent.momentSeries_mul_comm` and
  `TauCeti.IsFreelyIndependentElements.momentSeries_mul_comm` — `M_{ab} = M_{ba}` for free `a`
  and `b`.
* `TauCeti.IsFreelyIndependent.isUnit_apply_mul_of_ne` and
  `TauCeti.IsFreelyIndependentElements.isUnit_apply_mul_of_ne` — `φ (a b)` is a unit for free `a`
  and `b` with unit means, over a semiring.
* `TauCeti.IsFreelyIndependent.sSeries_mul` and
  `TauCeti.IsFreelyIndependentElements.sSeries_mul` — `S_{ab} = S_a S_b` for free `a` and `b`
  with unit means.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Lecture 18
  (the multiplicativity of the S-transform).
* D. V. Voiculescu, *Multiplication of certain non-commuting random variables*,
  J. Operator Theory 18 (1987), 223–235.
-/

public section

open Finset PowerSeries

namespace TauCeti

variable {R A ι : Type*} [CommRing R]

/-! ### Alternating words -/

/-- The alternating word `a, b, a, b, …`: the letter at an even position is `a`, and the letter
at an odd position is `b`. -/
private def altWord {M : Type*} (a b : M) (n : ℕ) : M := if Even n then a else b

private theorem altWord_add_two_mul {M : Type*} (a b : M) (k n : ℕ) :
    altWord a b (k + 2 * n) = altWord a b k := by
  simp [altWord, Nat.even_add]

/-- The product of the alternating word along `k, k + 1, …, k + 2n - 1`. -/
private theorem prod_range'_two_mul {M : Type*} [Monoid M] (a b : M) (k n : ℕ) :
    ((List.range' k (2 * n)).map (altWord a b)).prod =
      (altWord a b k * altWord a b (k + 1)) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 2 by ring, ← List.range'_append, List.map_append,
      List.prod_append, ih, pow_succ]
    simp [List.range'_succ, altWord_add_two_mul, add_right_comm k (2 * n) 1]

/-- The product of the alternating word along `k, k + 1, …, k + 2n`. -/
private theorem prod_range'_two_mul_add_one {M : Type*} [Monoid M] (a b : M) (k n : ℕ) :
    ((List.range' k (2 * n + 1)).map (altWord a b)).prod =
      (altWord a b k * altWord a b (k + 1)) ^ n * altWord a b k := by
  rw [← List.range'_append, List.map_append, List.prod_append, prod_range'_two_mul]
  simp [altWord_add_two_mul]

section Semiring

variable [Semiring A] [Algebra R A] {φ : A →ₗ[R] R}

/-- The free cumulants of the alternating word along sets containing both an even and an odd
position vanish. -/
private def MixedVanish (φ : A →ₗ[R] R) (a b : A) : Prop :=
  ∀ ⦃s : Finset ℕ⦄ ⦃x y : ℕ⦄, x ∈ s → y ∈ s → Even x → ¬Even y →
    freeCumulant φ (altWord a b) s = 0

/-- If `a ∈ B i` and `b ∈ B j` for `i ≠ j`, with `B` freely independent, then the mixed free
cumulants of the alternating word vanish. -/
private theorem mixedVanish {B : ι → Subalgebra R A} (h : IsFreelyIndependent φ B)
    (hφ : φ 1 = 1) {i j : ι} (hij : i ≠ j) {a b : A} (ha : a ∈ B i) (hb : b ∈ B j) :
    MixedVanish φ a b := fun _ _ _ hx hy hxe hyo => by
  refine h.freeCumulant_eq_zero hφ (ℓ := fun n => if Even n then i else j) (fun n _ => ?_) hx hy
    (by simpa [hxe, hyo] using hij)
  unfold altWord
  split_ifs
  exacts [ha, hb]

/-! ### The functional equations -/

/-- The weight of the part through the first position: the coefficient of `g` at its size if all
its positions are even, and `0` otherwise. -/
private noncomputable def evenPartWeight (g : R⟦X⟧) (B : Finset ℕ) : R :=
  if ∀ y ∈ B, Even y then coeff #B g else 0

/-- The sum over the noncrossing partitions of `t` in which the part through `0` has the weight
`evenPartWeight g` and every other part has the free cumulant of the alternating word along it
as its weight. -/
private noncomputable def firstPartSum (φ : A →ₗ[R] R) (a b : A) (g : R⟦X⟧) (t : Finset ℕ) :
    R :=
  ∑ P : NoncrossingPartition t,
    evenPartWeight g (P.1.part 0) * ∏ B ∈ P.1.parts with 0 ∉ B, freeCumulant φ (altWord a b) B

/-- Extending a part by a position `y` outside it shifts its weight, or kills it if `y` is
odd. -/
private theorem evenPartWeight_insert (g : R⟦X⟧) {B : Finset ℕ} {y : ℕ} (hy : y ∉ B) :
    evenPartWeight g (insert y B) =
      if Even y then evenPartWeight (mk fun p => coeff (p + 1) g) B else 0 := by
  by_cases hye : Even y <;> simp [evenPartWeight, hye, card_insert_of_notMem hy]

/-- On the empty set of positions, the sum is the constant coefficient of `g`. -/
private theorem firstPartSum_empty (φ : A →ₗ[R] R) (a b : A) (g : R⟦X⟧) :
    firstPartSum φ a b g ∅ = coeff 0 g := by
  rw [firstPartSum, Fintype.sum_unique, Finpartition.parts_eq_empty_iff.2 rfl, filter_empty,
    prod_empty, mul_one, (default : NoncrossingPartition (∅ : Finset ℕ)).1.part_eq_empty.2
      (notMem_empty 0)]
  simp [evenPartWeight]

/-- The recursion by the last position `y` of the part through `0`: the positions before `y`
carry a partition whose part through `0` is extended by `y`, and the positions after `y` carry an
arbitrary noncrossing partition, whose total weight is a moment of the alternating word. -/
private theorem firstPartSum_range_succ (hφ : φ 1 = 1) (a b : A) (g : R⟦X⟧) (L : ℕ) :
    firstPartSum φ a b g (range (L + 1)) =
      ∑ y ∈ range (L + 1), if Even y then
        firstPartSum φ a b (mk fun p => coeff (p + 1) g) (range y) *
          φ (((List.range' (y + 1) (L - y)).map (altWord a b)).prod) else 0 := by
  have hs : (range (L + 1)).Nonempty := ⟨0, by simp⟩
  have hmin : (range (L + 1)).min' hs = 0 :=
    le_antisymm (min'_le _ 0 (by simp)) (Nat.zero_le _)
  have h := NoncrossingPartition.sum_mul_prod_eq_sum_mul_sum hs (evenPartWeight g)
    (freeCumulant φ (altWord a b))
  rw [hmin] at h
  rw [firstPartSum, h]
  refine sum_congr rfl fun y hy => ?_
  have hyL := mem_range.1 hy
  have hlt : {z ∈ range (L + 1) | z < y} = range y := by
    ext z
    simp only [mem_filter, mem_range]
    omega
  have hgt : {z ∈ range (L + 1) | y < z} = Ico (y + 1) (L + 1) := by
    ext z
    simp only [mem_filter, mem_range, mem_Ico]
    omega
  rw [hlt, hgt]
  -- The positions after `y` contribute the moment of the alternating word along them.
  have htail : ∑ P : NoncrossingPartition (Ico (y + 1) (L + 1)),
      ∏ B ∈ P.1.parts, freeCumulant φ (altWord a b) B =
        φ (((List.range' (y + 1) (L - y)).map (altWord a b)).prod) := by
    obtain hne | hemp := (Ico (y + 1) (L + 1)).eq_empty_or_nonempty
    · obtain rfl : y = L := by
        rw [Ico_eq_empty_iff] at hne
        omega
      rw [Ico_self, Fintype.sum_unique, Finpartition.parts_eq_empty_iff.2 rfl, prod_empty,
        Nat.sub_self]
      simp [hφ]
    · rw [← apply_prod_eq_sum_prod_freeCumulant φ (altWord a b) hemp, Nat.sort_Ico,
        Nat.add_sub_add_right]
  rw [htail]
  -- The part through `0` extended by `y` has a shifted weight, or none if `y` is odd.
  have hins (P : NoncrossingPartition (range y)) :
      evenPartWeight g (insert y (P.1.part 0)) =
        if Even y then evenPartWeight (mk fun p => coeff (p + 1) g) (P.1.part 0) else 0 :=
    evenPartWeight_insert g fun hy' => by simpa using P.1.part_subset 0 hy'
  simp_rw [hins]
  split_ifs
  · rfl
  · simp

/-- On `0, …, 2n - 1`, the weighted sum is the `n`-th coefficient of `g(z P(z))`, where
`P(z) = ∑_{m ≥ 0} φ ((b a)ᵐ b) zᵐ`. -/
private theorem firstPartSum_range_two_mul (hφ : φ 1 = 1) (a b : A) (g : R⟦X⟧) (n : ℕ) :
    firstPartSum φ a b g (range (2 * n)) =
      coeff n (g.subst (X * mk fun m => φ ((b * a) ^ m * b))) := by
  induction n using Nat.strong_induction_on generalizing g with
  | _ n ih =>
  obtain _ | k := n
  · rw [mul_zero, range_zero, firstPartSum_empty, coeff_zero_eq_constantCoeff_apply,
      coeff_zero_eq_constantCoeff_apply]
    exact (constantCoeff_subst_of_constantCoeff_zero (S := R)
      (by simp [← constantCoeff_eq]) g).symm
  -- Only even last positions `y = 2j` of the part through `0` contribute; the positions after
  -- `y` carry the word `(b a)^(k - j) b`.
  rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, firstPartSum_range_succ hφ, sum_range_succ,
    sum_range_two_mul_add_one]
  simp only [even_two_mul, Nat.not_even_two_mul_add_one, ↓reduceIte, sum_const_zero, add_zero]
  rw [coeff_succ_subst_X_mul, mul_comm (PowerSeries.mk _), coeff_mul,
    Nat.sum_antidiagonal_eq_sum_range_succ fun i j => coeff i _ * coeff j _]
  refine sum_congr rfl fun j hj => ?_
  have hjk := mem_range.1 hj
  rw [ih j (by omega), show 2 * k + 1 - 2 * j = 2 * (k - j) + 1 by omega,
    prod_range'_two_mul_add_one]
  simp [altWord, Nat.even_add_one]

/-- On `0, …, 2n`, the weighted sum is the `n`-th coefficient of `g₁(z P(z)) M_{ba}(z)`, where
`g₁ = (g - g(0)) / z` and `P(z) = ∑_{m ≥ 0} φ ((b a)ᵐ b) zᵐ`. -/
private theorem firstPartSum_range_two_mul_add_one (hφ : φ 1 = 1) (a b : A) (g : R⟦X⟧)
    (n : ℕ) :
    firstPartSum φ a b g (range (2 * n + 1)) =
      coeff n ((mk fun p => coeff (p + 1) g).subst (X * mk fun m => φ ((b * a) ^ m * b)) *
        momentSeries φ (b * a)) := by
  -- Only even last positions `y = 2j` of the part through `0` contribute; the positions after
  -- `y` carry the word `(b a)^(n - j)`.
  rw [firstPartSum_range_succ hφ, sum_range_two_mul_add_one]
  simp only [even_two_mul, Nat.not_even_two_mul_add_one, ↓reduceIte, sum_const_zero, add_zero]
  rw [coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ fun i j => coeff i _ * coeff j _]
  refine sum_congr rfl fun j hj => ?_
  have hjn := mem_range.1 hj
  rw [firstPartSum_range_two_mul hφ, show 2 * n - 2 * j = 2 * (n - j) by omega,
    prod_range'_two_mul, coeff_momentSeries]
  simp [altWord, Nat.even_add_one]

/-- If mixed free cumulants vanish, the moment of the alternating word along `0, …, L - 1` is the
weighted sum for the free cumulant series of `a`: the part through `0` contains only positions of
`a`. -/
private theorem apply_prod_range_eq_firstPartSum (hφ : φ 1 = 1) {a b : A}
    (hmix : MixedVanish φ a b) (L : ℕ) :
    φ (((List.range L).map (altWord a b)).prod) =
      firstPartSum φ a b (freeCumulantSeries φ a) (range L) := by
  rcases L.eq_zero_or_pos with rfl | hL
  · simp [firstPartSum_empty, hφ]
  have h0L : 0 ∈ range L := mem_range.2 hL
  rw [← sort_range, apply_prod_eq_sum_prod_freeCumulant φ _ ⟨0, h0L⟩, firstPartSum]
  refine sum_congr rfl fun P _ => ?_
  rw [P.1.prod_parts_eq_mul_prod_filter_notMem h0L]
  congr 1
  unfold evenPartWeight
  split_ifs with he
  · rw [freeCumulant_congr φ (b := fun _ => a) fun y hy => by simp [altWord, he y hy],
      freeCumulant_const_eq_coeff_freeCumulantSeries]
  · push Not at he
    obtain ⟨y, hy, hyo⟩ := he
    exact hmix (P.1.mem_part h0L) hy (by decide) hyo

/-- *The first functional equation*: `M_{ab}(z) = C_a(z P(z))` with
`P(z) = ∑_{m ≥ 0} φ ((b a)ᵐ b) zᵐ`. -/
private theorem momentSeries_mul_eq_subst (hφ : φ 1 = 1) {a b : A} (hmix : MixedVanish φ a b) :
    momentSeries φ (a * b) =
      (freeCumulantSeries φ a).subst (X * mk fun m => φ ((b * a) ^ m * b)) := by
  ext n
  rw [coeff_momentSeries, ← firstPartSum_range_two_mul hφ,
    ← apply_prod_range_eq_firstPartSum hφ hmix, List.range_eq_range', prod_range'_two_mul]
  simp [altWord]

/-- When mixed free cumulants vanish, the first mixed moment factorises:
`φ (a b) = φ a φ b`. -/
private theorem apply_mul_of_mixedVanish (hφ : φ 1 = 1) {a b : A} (hmix : MixedVanish φ a b) :
    φ (a * b) = φ a * φ b := by
  have h := congrArg (coeff 1) (momentSeries_mul_eq_subst hφ hmix)
  rw [coeff_momentSeries, pow_one, coeff_one_subst (by simp), coeff_one_freeCumulantSeries] at h
  simpa using h

/-- *The second functional equation*: `Q(z) = R_a(z P(z)) M_{ba}(z)` with
`P(z) = ∑_{m ≥ 0} φ ((b a)ᵐ b) zᵐ` and `Q(z) = ∑_{m ≥ 0} φ ((a b)ᵐ a) zᵐ`. -/
private theorem mk_apply_mul_pow_mul_eq (hφ : φ 1 = 1) {a b : A} (hmix : MixedVanish φ a b) :
    (mk fun m => φ ((a * b) ^ m * a)) =
      (rSeries φ a).subst (X * mk fun m => φ ((b * a) ^ m * b)) * momentSeries φ (b * a) := by
  have hr : (mk fun p => coeff (p + 1) (freeCumulantSeries φ a)) = rSeries φ a := by
    ext p
    rw [coeff_mk, coeff_succ_freeCumulantSeries]
  ext n
  rw [coeff_mk, ← hr, ← firstPartSum_range_two_mul_add_one hφ,
    ← apply_prod_range_eq_firstPartSum hφ hmix, List.range_eq_range',
    prod_range'_two_mul_add_one]
  simp [altWord]

/-- With `u = z P` and `v = z Q`, the functional equations give `u v = z M_{ab} (M_{ba} - 1)`. -/
private theorem X_mul_mul_X_mul_eq (hφ : φ 1 = 1) {a b : A} (hba : MixedVanish φ b a) :
    (X * mk fun m => φ ((b * a) ^ m * b)) * (X * mk fun m => φ ((a * b) ^ m * a)) =
      X * momentSeries φ (a * b) * (momentSeries φ (b * a) - 1) := by
  set v : R⟦X⟧ := X * mk fun m => φ ((a * b) ^ m * a)
  have hv : HasSubst v := .of_constantCoeff_zero' (by simp [v])
  have hC : momentSeries φ (b * a) - 1 = v * (rSeries φ b).subst v := by
    rw [momentSeries_mul_eq_subst hφ hba, freeCumulantSeries_eq_one_add_X_mul_rSeries,
      subst_add hv, subst_mul hv, subst_X hv, subst_one, add_sub_cancel_left]
  rw [hC, mk_apply_mul_pow_mul_eq hφ hba]
  ring

/-- The moment series of `a b` and `b a` agree when mixed cumulants vanish in both orders. -/
private theorem momentSeries_mul_comm_of_mixedVanish (hφ : φ 1 = 1) {a b : A}
    (hab : MixedVanish φ a b) (hba : MixedVanish φ b a) :
    momentSeries φ (a * b) = momentSeries φ (b * a) := by
  have h := (X_mul_mul_X_mul_eq hφ hba).symm.trans
    ((mul_comm _ _).trans (X_mul_mul_X_mul_eq hφ hab))
  rw [mul_assoc, mul_assoc] at h
  linear_combination -X_mul_injective h

/-- `S_{ab} = S_a S_b` when mixed cumulants vanish in both orders. -/
private theorem sSeries_mul_of_mixedVanish (hφ : φ 1 = 1) {a b : A} (hab : MixedVanish φ a b)
    (hba : MixedVanish φ b a) (ha : IsUnit (φ a)) (hb : IsUnit (φ b))
    (hab' : IsUnit (φ (a * b))) :
    sSeries φ (a * b) hab' = sSeries φ a ha * sSeries φ b hb := by
  have hcomm := momentSeries_mul_comm_of_mixedVanish hφ hab hba
  set u : R⟦X⟧ := X * mk fun m => φ ((b * a) ^ m * b)
  set v : R⟦X⟧ := X * mk fun m => φ ((a * b) ^ m * a)
  have hu : HasSubst u := .of_constantCoeff_zero' (by simp [u])
  have hv : HasSubst v := .of_constantCoeff_zero' (by simp [v])
  -- Substitute the compositional inverse `w` of `Ψ = M_{ab} - 1`.
  have hψ : constantCoeff (momentSeries φ (a * b) - 1) = 0 := by simp [hφ]
  have hψ' := isUnit_coeff_one_momentSeries_sub_one φ (a * b) hab'
  set w := (momentSeries φ (a * b) - 1).substInvOfIsUnit hψ'
  have hw : HasSubst w := .substInvOfIsUnit _ _
  have hψw : (momentSeries φ (a * b) - 1).subst w = X :=
    subst_substInvOfIsUnit_right _ hψ hψ'
  have hMw : (momentSeries φ (a * b)).subst w = 1 + X := by
    rw [← sub_add_cancel (momentSeries φ (a * b)) 1, subst_add hw, hψw, subst_one, add_comm]
  -- The substituted series `u(w)` and `v(w)` are the compositional inverses of `C_a - 1` and
  -- `C_b - 1`, that is, `z S_a` and `z S_b`.
  have hsub {c : A} {t : R⟦X⟧} (ht : HasSubst t) (hc : IsUnit (φ c))
      (hct : momentSeries φ (a * b) = (freeCumulantSeries φ c).subst t) :
      t.subst w = X * sSeries φ c hc := by
    rw [X_mul_sSeries_eq_substInvOfIsUnit c hφ hc]
    refine (freeCumulantSeries φ c - 1).eq_substInvOfIsUnit_of_subst_eq_X (by simp) _
      (by simpa [coe_substAlgHom] using ht.comp hw) ?_
    rw [← subst_comp_subst_apply ht hw, subst_sub ht, subst_one, ← hct, hψw]
  have hSa := hsub hu ha (momentSeries_mul_eq_subst hφ hab)
  have hSb := hsub hv hb (hcomm.trans (momentSeries_mul_eq_subst hφ hba))
  -- Substituting `w` into `u v = z M_{ab} (M_{ab} - 1)` gives `z² S_a S_b = z (1 + z) w`, and
  -- `z S_{ab} = (1 + z) w`.
  have e : u * v = X * momentSeries φ (a * b) * (momentSeries φ (a * b) - 1) := by
    simp only [u, v]
    rw [X_mul_mul_X_mul_eq hφ hba, ← hcomm]
  have h := congrArg (subst w) e
  rw [subst_mul hw u v, hSa, hSb, subst_mul hw, subst_mul hw X, subst_X hw, hMw, hψw] at h
  apply X_mul_injective
  apply X_mul_injective
  dsimp only
  rw [X_mul_sSeries]
  linear_combination -h

/-! ### Products of free elements -/

/-- *The moments of `a b` and `b a` agree for free elements*: if `a ∈ B i` and `b ∈ B j` for
`i ≠ j`, with `B` freely independent for a normalised `φ`, then `φ ((a b)ⁿ) = φ ((b a)ⁿ)` for
every `n`. No traciality of `φ` is needed. -/
theorem IsFreelyIndependent.momentSeries_mul_comm {B : ι → Subalgebra R A}
    (h : IsFreelyIndependent φ B) (hφ : φ 1 = 1) {i j : ι} (hij : i ≠ j) {a b : A}
    (ha : a ∈ B i) (hb : b ∈ B j) :
    momentSeries φ (a * b) = momentSeries φ (b * a) :=
  momentSeries_mul_comm_of_mixedVanish hφ (mixedVanish h hφ hij ha hb)
    (mixedVanish h hφ hij.symm hb ha)

/-- *The moments of `c i * c j` and `c j * c i` agree for free elements*: if `c i` and `c j`, for
`i ≠ j`, belong to a freely independent family for a normalised `φ`, then
`φ ((c i * c j)ⁿ) = φ ((c j * c i)ⁿ)` for every `n`. -/
theorem IsFreelyIndependentElements.momentSeries_mul_comm {c : ι → A}
    (h : IsFreelyIndependentElements φ c) (hφ : φ 1 = 1) {i j : ι} (hij : i ≠ j) :
    momentSeries φ (c i * c j) = momentSeries φ (c j * c i) :=
  (isFreelyIndependentElements_iff.mp h).momentSeries_mul_comm hφ hij
    (Algebra.self_mem_adjoin_singleton R _) (Algebra.self_mem_adjoin_singleton R _)

/-- The mean of a product of free elements with unit means is a unit: if `a ∈ B i` and `b ∈ B j`
for `i ≠ j`, with `B` freely independent for a normalised `φ`, and `φ a` and `φ b` are units, then
so is `φ (a b) = φ a φ b`. Unlike `IsFreelyIndependent.apply_mul_of_ne`, this holds over a
semiring `A`. -/
theorem IsFreelyIndependent.isUnit_apply_mul_of_ne {B : ι → Subalgebra R A}
    (h : IsFreelyIndependent φ B) (hφ : φ 1 = 1) {i j : ι} (hij : i ≠ j) {a b : A}
    (ha : a ∈ B i) (hb : b ∈ B j) (hua : IsUnit (φ a)) (hub : IsUnit (φ b)) :
    IsUnit (φ (a * b)) := by
  rw [apply_mul_of_mixedVanish hφ (mixedVanish h hφ hij ha hb)]
  exact hua.mul hub

/-- The mean of a product of two free elements with unit means is a unit: if `c i` and `c j`, for
`i ≠ j`, belong to a freely independent family for a normalised `φ` and `φ (c i)` and `φ (c j)`
are units, then so is `φ (c i * c j)`. -/
theorem IsFreelyIndependentElements.isUnit_apply_mul_of_ne {c : ι → A}
    (h : IsFreelyIndependentElements φ c) (hφ : φ 1 = 1) {i j : ι} (hij : i ≠ j)
    (hua : IsUnit (φ (c i))) (hub : IsUnit (φ (c j))) : IsUnit (φ (c i * c j)) :=
  (isFreelyIndependentElements_iff.mp h).isUnit_apply_mul_of_ne hφ hij
    (Algebra.self_mem_adjoin_singleton R _) (Algebra.self_mem_adjoin_singleton R _) hua hub

/-- *Multiplicativity of the S-series*: if `a ∈ B i` and `b ∈ B j` for `i ≠ j`, with `B` freely
independent for a normalised `φ`, and the means `φ a` and `φ b` are units, then
`S_{ab} = S_a S_b`. The mean `φ (a b) = φ a φ b` of `a b` is then a unit too. No traciality of
`φ` is needed. -/
theorem IsFreelyIndependent.sSeries_mul {B : ι → Subalgebra R A}
    (h : IsFreelyIndependent φ B) (hφ : φ 1 = 1) {i j : ι} (hij : i ≠ j) {a b : A}
    (ha : a ∈ B i) (hb : b ∈ B j) (hua : IsUnit (φ a)) (hub : IsUnit (φ b)) :
    sSeries φ (a * b) (h.isUnit_apply_mul_of_ne hφ hij ha hb hua hub) =
      sSeries φ a hua * sSeries φ b hub :=
  sSeries_mul_of_mixedVanish hφ (mixedVanish h hφ hij ha hb) (mixedVanish h hφ hij.symm hb ha)
    hua hub _

/-- *Multiplicativity of the S-series*: if `c i` and `c j`, for `i ≠ j`, belong to a freely
independent family for a normalised `φ` and have unit means, then the S-series of `c i * c j` is
the product of the S-series of `c i` and of `c j`. -/
theorem IsFreelyIndependentElements.sSeries_mul {c : ι → A}
    (h : IsFreelyIndependentElements φ c) (hφ : φ 1 = 1) {i j : ι} (hij : i ≠ j)
    (hua : IsUnit (φ (c i))) (hub : IsUnit (φ (c j))) :
    sSeries φ (c i * c j) (h.isUnit_apply_mul_of_ne hφ hij hua hub) =
      sSeries φ (c i) hua * sSeries φ (c j) hub :=
  (isFreelyIndependentElements_iff.mp h).sSeries_mul hφ hij
    (Algebra.self_mem_adjoin_singleton R _) (Algebra.self_mem_adjoin_singleton R _) hua hub

end Semiring

end TauCeti
