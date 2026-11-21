/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.PowerSeries.Expand
public import Mathlib.RingTheory.PowerSeries.Substitution
public import TauCeti.RingTheory.PowerSeries.Cartier

import Mathlib.Algebra.CharP.Lemmas
import TauCeti.RingTheory.PowerSeries.AdicComplete
import TauCeti.RingTheory.PowerSeries.Dvd

/-!
# The Frobenius power basis of a power series ring

For a prime `p` and a commutative ring `R`, the Frobenius substitution
`φ f = f ((1 + X) ^ p - 1)` is an `R`-algebra endomorphism of `R⟦X⟧`. Through `φ` the power
series ring becomes an algebra over itself, `a • f = φ a * f`; this is not the ordinary
self-module structure. When `R` is `p`-adically complete and `p` is a nonzerodivisor of `R`,
for instance over `ℤ_[p]` or over the integers of a finite unramified extension of `ℚ_[p]`,
this algebra is free of rank `p` with basis `1, 1 + X, …, (1 + X) ^ (p - 1)`: every series has a
unique expansion

  `f = ∑ i < p, (1 + X) ^ i * φ (a i)`.

This is the finite free algebra whose determinant norm and trace are Coleman's norm and trace
operators on `R⟦X⟧`.

The proof reduces modulo `p`. Over any commutative ring `S`, the series `(1 + X) ^ i` with
`i < q` form a basis of `S⟦X⟧` over itself through the expansion `f ↦ f (X ^ q)`; this follows
from the Cartier decomposition `F = ∑ r < q, X ^ r * F_r (X ^ q)` by the binomial change of basis
between `X ^ r` and `(1 + X) ^ i`. Modulo `p`, the binomial theorem turns `φ` into the expansion
by `p`. Existence of coordinates modulo every power of `p` follows by successive approximation,
and the approximations converge since `R⟦X⟧` is complete for the ideal of series whose constant
coefficient lies in `pR` (`PowerSeries.isAdicComplete_comap_constantCoeff`). Uniqueness uses that
`p` is a nonzerodivisor, and Hausdorffness for the same ideal.

## Main definitions

* `PowerSeries.frobeniusSubst R p`: the substitution `f ↦ f ((1 + X) ^ p - 1)`.
* `PowerSeries.frobeniusAlgebra R p`: `R⟦X⟧` as an algebra over itself through `φ`.
* `PowerSeries.frobeniusAssembly R p`: the `R`-linear map `a ↦ ∑ i, (1 + X) ^ i * φ (a i)`.
* `PowerSeries.frobeniusBasis R p`: the basis `(1 + X) ^ i`, `i < p`, of `R⟦X⟧` over itself
  through `φ`.

## Main results

* `PowerSeries.exists_sum_one_add_X_pow_mul_expand`,
  `PowerSeries.eq_zero_of_sum_one_add_X_pow_mul_expand_eq_zero`: over any commutative ring, every
  series is uniquely `∑ i < q, (1 + X) ^ i * b i (X ^ q)`.
* `PowerSeries.frobeniusSubst_eq_expand`: if `p = 0` in `S`, then `φ` is the expansion by `p`.
* `PowerSeries.frobeniusAssembly_injective`, `PowerSeries.frobeniusAssembly_surjective`: the
  Frobenius coordinates exist when `R` is `p`-adically complete, and are unique when `R` is
  `p`-adically Hausdorff and `p` is a nonzerodivisor.
* `PowerSeries.frobeniusAssembly_frobeniusBasis_repr`: the coordinates of `f` in the Frobenius
  basis assemble to `f`.
* `PowerSeries.finrank_frobeniusAlgebra`: `R⟦X⟧` has rank `p` over itself through `φ`.

## References

* R. F. Coleman, *Division values in local fields*, Invent. Math. 53 (1979), 91–116, §2.
* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*, Essential Number
  Theory 4 (2025), Lemma 10.8.
-/

public section

namespace PowerSeries

/-! ### Expanded coordinates over an arbitrary ring -/

section Expand

variable {S : Type*} [CommRing S]

/-- Every Cartier component of modulus `q` of a power `(1 + X) ^ i` with `i < q` is a constant
binomial coefficient. -/
theorem cartier_one_add_X_pow {q i : ℕ} (j : ℕ) (hi : i < q) :
    cartier S q j ((1 + X) ^ i) = C (i.choose j : S) := by
  ext n
  rw [coeff_cartier, coeff_C, ← Polynomial.coe_one, ← Polynomial.coe_X, ← Polynomial.coe_add,
    ← Polynomial.coe_pow, Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [Nat.choose_eq_zero_of_lt (by nlinarith)]
    simp [hn.ne']

/-- The Cartier component of index `j` of `(1 + X) ^ i * g (X ^ q)`, for `i < q`, is the binomial
coefficient times `g`. -/
theorem cartier_one_add_X_pow_mul_expand {q i j : ℕ} (hq : q ≠ 0) (hi : i < q) (hj : j < q)
    (g : S⟦X⟧) :
    cartier S q j ((1 + X) ^ i * expand q hq g) = C (i.choose j : S) * g := by
  rw [mul_comm, cartier_expand_mul q j hq hj, cartier_one_add_X_pow j hi, mul_comm]

/-- A power of `X` below `q` is a combination of the powers `(1 + X) ^ i`, `i < q`, with
binomial coefficients. -/
theorem X_pow_eq_sum_one_add_X_pow {q r : ℕ} (hr : r < q) :
    (X : S⟦X⟧) ^ r =
      ∑ i : Fin q, C ((-1) ^ (r - i) * (r.choose i : S)) * (1 + X) ^ (i : ℕ) := by
  have h : (X : S⟦X⟧) ^ r = ((1 + X) + (-1)) ^ r := by ring
  rw [h, add_pow, Fin.sum_univ_eq_sum_range
    (fun i ↦ C ((-1) ^ (r - i) * (r.choose i : S)) * (1 + X) ^ i)]
  rw [← Finset.sum_range_add_sum_Ico _ (show r + 1 ≤ q by omega)]
  rw [Finset.sum_eq_zero (s := Finset.Ico _ _) fun i hi ↦ by
    rw [Nat.choose_eq_zero_of_lt (by simp at hi; omega)]; simp, add_zero]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [map_mul, map_pow, map_neg, map_one, map_natCast]
  ring

/-- **Existence of expanded coordinates.** Over any commutative ring, every power series is
`∑ i < q, (1 + X) ^ i * b i (X ^ q)` for some series `b i`. -/
theorem exists_sum_one_add_X_pow_mul_expand (q : ℕ) (hq : q ≠ 0) (g : S⟦X⟧) :
    ∃ b : Fin q → S⟦X⟧, ∑ i : Fin q, (1 + X) ^ (i : ℕ) * expand q hq (b i) = g := by
  refine ⟨fun i ↦ ∑ r ∈ Finset.range q,
    C ((-1) ^ (r - i) * (r.choose i : S)) * cartier S q r g, ?_⟩
  conv_rhs => rw [sum_X_pow_mul_expand_cartier q hq g]
  simp_rw [map_sum, Finset.mul_sum, map_mul, expand_C]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r hr ↦ ?_
  rw [X_pow_eq_sum_one_add_X_pow (Finset.mem_range.mp hr), Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [map_mul]
  ring

/-- The Cartier components of an expanded combination: the component of index `j < q` of
`∑ i < q, (1 + X) ^ i * b i (X ^ q)` is `∑ i, choose i j * b i`. -/
theorem cartier_sum_one_add_X_pow_mul_expand {q j : ℕ} (hq : q ≠ 0) (hj : j < q)
    (b : Fin q → S⟦X⟧) :
    cartier S q j (∑ i : Fin q, (1 + X) ^ (i : ℕ) * expand q hq (b i)) =
      ∑ i : Fin q, C ((i : ℕ).choose j : S) * b i := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ cartier_one_add_X_pow_mul_expand hq i.isLt hj (b i)

/-- **Uniqueness of expanded coordinates.** Over any commutative ring, if
`∑ i < q, (1 + X) ^ i * b i (X ^ q) = 0`, then every `b i` vanishes. -/
theorem eq_zero_of_sum_one_add_X_pow_mul_expand_eq_zero {q : ℕ} (hq : q ≠ 0)
    {b : Fin q → S⟦X⟧} (hb : ∑ i : Fin q, (1 + X) ^ (i : ℕ) * expand q hq (b i) = 0) : b = 0 := by
  have hc (j : Fin q) : ∑ i : Fin q, C ((i : ℕ).choose j : S) * b i = 0 := by
    rw [← cartier_sum_one_add_X_pow_mul_expand hq j.isLt, hb, map_zero]
  -- Downward induction: the component of index `j` sees `b j` and the `b i` with `i > j`.
  suffices h : ∀ k, ∀ j : Fin q, q ≤ j + k → b j = 0 from
    funext fun j ↦ h q j (by omega)
  intro k
  induction k with
  | zero => exact fun j hj ↦ absurd j.isLt (by omega)
  | succ k ih =>
    intro j hj
    rw [← hc j, Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
      · rw [Nat.choose_eq_zero_of_lt h]; simp
      · rw [ih i (by omega), mul_zero]
    · simp

end Expand

/-! ### The Frobenius substitution -/

variable {R : Type*} [CommRing R] (p : ℕ)

private theorem constantCoeff_one_add_X_pow_sub_one :
    constantCoeff ((1 + X : R⟦X⟧) ^ p - 1) = 0 := by
  simp

/-- The series `(1 + X) ^ p - 1` has zero constant coefficient, so it can be substituted. -/
theorem hasSubst_one_add_X_pow_sub_one : HasSubst ((1 + X : R⟦X⟧) ^ p - 1) :=
  HasSubst.of_constantCoeff_zero' (constantCoeff_one_add_X_pow_sub_one p)

variable (R) in
/-- The Frobenius substitution `f ↦ f ((1 + X) ^ p - 1)` on `R⟦X⟧`. It fixes coefficients. -/
noncomputable def frobeniusSubst : R⟦X⟧ →ₐ[R] R⟦X⟧ :=
  substAlgHom (hasSubst_one_add_X_pow_sub_one (R := R) p)

theorem frobeniusSubst_apply (f : R⟦X⟧) :
    frobeniusSubst R p f = f.subst ((1 + X : R⟦X⟧) ^ p - 1) :=
  congrFun (coe_substAlgHom (hasSubst_one_add_X_pow_sub_one p)) f

@[simp]
theorem frobeniusSubst_X : frobeniusSubst R p X = (1 + X) ^ p - 1 :=
  substAlgHom_X _

@[simp]
theorem frobeniusSubst_C (c : R) : frobeniusSubst R p (C c) = C c :=
  (frobeniusSubst R p).commutes c

theorem frobeniusSubst_one_add_X : frobeniusSubst R p (1 + X) = (1 + X) ^ p := by
  simp

@[simp]
theorem constantCoeff_frobeniusSubst (f : R⟦X⟧) :
    constantCoeff (frobeniusSubst R p f) = constantCoeff f := by
  rw [frobeniusSubst_apply]
  exact (constantCoeff_subst_of_constantCoeff_zero (S := R)
    (constantCoeff_one_add_X_pow_sub_one p) f).trans (Algebra.algebraMap_self_apply _)

/-- The Frobenius substitution commutes with change of coefficients. -/
theorem map_frobeniusSubst {S : Type*} [CommRing S] (h : R →+* S) (f : R⟦X⟧) :
    map h (frobeniusSubst R p f) = frobeniusSubst S p (map h f) := by
  rw [frobeniusSubst_apply, frobeniusSubst_apply]
  have : map h ((1 + X : R⟦X⟧) ^ p - 1) = (1 + X) ^ p - 1 := by simp
  exact (map_subst (hasSubst_one_add_X_pow_sub_one p) f).trans (congrArg (subst · (map h f)) this)

/-- If `p = 0` in `S`, the Frobenius substitution is the expansion `f ↦ f (X ^ p)`. -/
theorem frobeniusSubst_eq_expand [hp : Fact p.Prime] {S : Type*} [CommRing S]
    (hpS : (p : S) = 0) (f : S⟦X⟧) :
    frobeniusSubst S p f = expand p hp.out.ne_zero f := by
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp.out (X : S⟦X⟧) 1
  have hp' : (p : S⟦X⟧) = 0 := by rw [← map_natCast (C (R := S)), hpS, map_zero]
  rw [frobeniusSubst_apply, expand_apply, add_comm, hr, hp']
  simp

/-! ### The Frobenius scalar algebra -/

variable (R) in
/-- The power series ring as an algebra over itself through the Frobenius substitution:
`a • f = φ a * f`. This is not an instance: it differs from the ordinary self-module
structure, and is passed explicitly. -/
@[instance_reducible]
noncomputable def frobeniusAlgebra : Algebra R⟦X⟧ R⟦X⟧ :=
  (frobeniusSubst R p).toRingHom.toAlgebra

theorem algebraMap_frobeniusAlgebra :
    @algebraMap R⟦X⟧ R⟦X⟧ _ _ (frobeniusAlgebra R p) = (frobeniusSubst R p).toRingHom :=
  (rfl)

theorem frobeniusAlgebra_smul (a f : R⟦X⟧) :
    @HSMul.hSMul _ _ _ (@instHSMul _ _ (frobeniusAlgebra R p).toSMul) a f =
      frobeniusSubst R p a * f :=
  (rfl)

/-! ### Frobenius coordinates -/

variable (R) in
/-- The Frobenius coordinate assembly `a ↦ ∑ i < p, (1 + X) ^ i * φ (a i)`. -/
noncomputable def frobeniusAssembly : (Fin p → R⟦X⟧) →ₗ[R] R⟦X⟧ where
  toFun a := ∑ i : Fin p, (1 + X) ^ (i : ℕ) * frobeniusSubst R p (a i)
  map_add' a b := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c a := by simp [Finset.smul_sum]

theorem frobeniusAssembly_apply (a : Fin p → R⟦X⟧) :
    frobeniusAssembly R p a = ∑ i : Fin p, (1 + X) ^ (i : ℕ) * frobeniusSubst R p (a i) :=
  (rfl)

@[simp]
theorem frobeniusAssembly_single (i : Fin p) (a : R⟦X⟧) :
    frobeniusAssembly R p (Pi.single i a) = (1 + X) ^ (i : ℕ) * frobeniusSubst R p a := by
  classical
  rw [frobeniusAssembly_apply, Finset.sum_eq_single i (fun j _ hj ↦ by simp [hj]) (by simp)]
  simp

/-- The assembly is linear over the Frobenius scalars: multiplying every coordinate by `a`
multiplies the assembled series by `φ a`. -/
theorem frobeniusAssembly_mul (a : R⟦X⟧) (v : Fin p → R⟦X⟧) :
    frobeniusAssembly R p (fun i ↦ a * v i) = frobeniusSubst R p a * frobeniusAssembly R p v := by
  simp only [frobeniusAssembly_apply, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

/-! ### Reduction modulo `p` -/

/-- Divisibility by `p` in `R⟦X⟧` is coefficientwise divisibility, detected by reduction modulo
`p`. -/
private theorem natCast_dvd_iff_map_eq_zero {f : R⟦X⟧} :
    (p : R⟦X⟧) ∣ f ↔ map (Ideal.Quotient.mk (Ideal.span {(p : R)})) f = 0 := by
  rw [← map_natCast C, C_dvd_iff_dvd_coeff, PowerSeries.ext_iff]
  simp [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]

/-- Reduction modulo `p` of the Frobenius assembly is the expanded assembly. -/
private theorem map_frobeniusAssembly [Fact p.Prime] (a : Fin p → R⟦X⟧) :
    map (Ideal.Quotient.mk (Ideal.span {(p : R)})) (frobeniusAssembly R p a) =
      ∑ i : Fin p, (1 + X) ^ (i : ℕ) *
        expand p (Fact.out : p.Prime).ne_zero (map (Ideal.Quotient.mk _) (a i)) := by
  have hp : (p : R ⧸ Ideal.span {(p : R)}) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton_self _
  simp [frobeniusAssembly_apply, map_frobeniusSubst, frobeniusSubst_eq_expand p hp]

/-- **Coordinates modulo `p`.** Every series is a Frobenius assembly up to a multiple of `p`. -/
theorem exists_frobeniusAssembly_add_natCast_mul [Fact p.Prime] (f : R⟦X⟧) :
    ∃ a h, f = frobeniusAssembly R p a + p * h := by
  obtain ⟨b, hb⟩ := exists_sum_one_add_X_pow_mul_expand p (Fact.out : p.Prime).ne_zero
    (map (Ideal.Quotient.mk (Ideal.span {(p : R)})) f)
  choose a ha using fun i ↦ map_surjective _ Ideal.Quotient.mk_surjective (b i)
  obtain ⟨h, hh⟩ := (natCast_dvd_iff_map_eq_zero p).mpr
    (show map (Ideal.Quotient.mk _) (f - frobeniusAssembly R p a) = 0 by
      rw [map_sub, map_frobeniusAssembly, ← hb]; simp [ha])
  exact ⟨a, h, by rw [← hh]; ring⟩

/-- **Reflection of divisibility by `p`.** If `p` divides a Frobenius assembly, it divides every
coordinate. -/
theorem natCast_dvd_of_natCast_dvd_frobeniusAssembly [Fact p.Prime] {a : Fin p → R⟦X⟧}
    (ha : (p : R⟦X⟧) ∣ frobeniusAssembly R p a) (i : Fin p) : (p : R⟦X⟧) ∣ a i := by
  rw [natCast_dvd_iff_map_eq_zero, map_frobeniusAssembly] at ha
  rw [natCast_dvd_iff_map_eq_zero]
  exact congrFun (eq_zero_of_sum_one_add_X_pow_mul_expand_eq_zero _ ha) i

/-! ### Exact coordinates -/

/-- The ideal of series whose constant coefficient lies in `pR`. -/
local notation "𝔍" => Ideal.comap (constantCoeff (R := R)) (Ideal.span {(p : R)})

private theorem natCast_mem : (p : R⟦X⟧) ∈ 𝔍 := by
  simp

/-- The Frobenius assembly preserves the powers of the ideal of series with constant coefficient
in `pR`. -/
private theorem frobeniusAssembly_mem_pow {n : ℕ} {a : Fin p → R⟦X⟧} (ha : ∀ i, a i ∈ 𝔍 ^ n) :
    frobeniusAssembly R p a ∈ 𝔍 ^ n := by
  have hle : Ideal.map (frobeniusSubst R p) 𝔍 ≤ 𝔍 :=
    Ideal.map_le_iff_le_comap.mpr fun f hf ↦ by simpa using hf
  rw [frobeniusAssembly_apply]
  refine Ideal.sum_mem _ fun i _ ↦ Ideal.mul_mem_left _ _ ?_
  have := Ideal.mem_map_of_mem (frobeniusSubst R p) (ha i)
  rw [Ideal.map_pow] at this
  exact Ideal.pow_right_mono hle n this

/-- **Uniqueness of Frobenius coordinates.** If `R` is `p`-adically Hausdorff and `p` is a
nonzerodivisor of `R`, the Frobenius assembly is injective. -/
theorem frobeniusAssembly_injective [Fact p.Prime] [IsHausdorff (Ideal.span {(p : R)}) R]
    (hp : IsSMulRegular R (p : R)) : Function.Injective (frobeniusAssembly R p) := by
  have hreg {g : R⟦X⟧} (hg : (p : R⟦X⟧) * g = 0) : g = 0 := ext fun n ↦ hp <| by
    have := congrArg (coeff n) hg
    rwa [← map_natCast C, coeff_C_mul, map_zero, ← mul_zero (p : R)] at this
  -- Every coordinate of a vanishing assembly is divisible by every power of `p`.
  have hdvd (r : ℕ) : ∀ a, frobeniusAssembly R p a = 0 → ∀ i, (p : R⟦X⟧) ^ r ∣ a i := by
    induction r with
    | zero => simp
    | succ r ih =>
      intro a ha i
      choose b hb using natCast_dvd_of_natCast_dvd_frobeniusAssembly p (ha ▸ dvd_zero _)
      have hb' : a = fun i ↦ (p : R⟦X⟧) * b i := funext hb
      rw [hb', frobeniusAssembly_mul, map_natCast] at ha
      obtain ⟨c, hc⟩ := ih b (hreg (by simpa using ha)) i
      exact ⟨c, by rw [hb i, hc]; ring⟩
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro a ha
  funext i
  refine (isHausdorff_comap_constantCoeff (Ideal.span {(p : R)})).haus _ fun n ↦ ?_
  obtain ⟨c, hc⟩ := hdvd n a ha i
  simpa [SModEq.zero, hc] using Ideal.mul_mem_right c _ (Ideal.pow_mem_pow (natCast_mem p) n)

/-- **Existence of Frobenius coordinates.** If `R` is `p`-adically complete, the Frobenius
assembly is surjective. -/
theorem frobeniusAssembly_surjective [Fact p.Prime] [IsAdicComplete (Ideal.span {(p : R)}) R] :
    Function.Surjective (frobeniusAssembly R p) := by
  intro f
  choose A H hAH using exists_frobeniusAssembly_add_natCast_mul (R := R) p
  have hmem {n : ℕ} (x : R⟦X⟧) : (p : R⟦X⟧) ^ n * x ∈ 𝔍 ^ n :=
    Ideal.mul_mem_right x _ (Ideal.pow_mem_pow (natCast_mem p) n)
  -- Successive approximations `s r`, with `f = Ξ (s r) + p ^ r * H^[r] f`.
  let s (r : ℕ) : Fin p → R⟦X⟧ := ∑ k ∈ Finset.range r, p ^ k • A (H^[k] f)
  have hsucc (r : ℕ) : s (r + 1) = s r + p ^ r • A (H^[r] f) := Finset.sum_range_succ _ _
  have hs (r : ℕ) : f = frobeniusAssembly R p (s r) + p ^ r * H^[r] f := by
    induction r with
    | zero => simp [s]
    | succ r ih =>
      conv_lhs => rw [ih, hAH (H^[r] f)]
      rw [hsucc, map_add, map_nsmul, nsmul_eq_mul, Nat.cast_pow, Function.iterate_succ_apply']
      ring
  -- The approximations converge coordinatewise, by precompleteness.
  have hcauchy {m n : ℕ} (hmn : m ≤ n) (i : Fin p) : s n i - s m i ∈ 𝔍 ^ m := by
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      rw [hsucc, Pi.add_apply, add_sub_right_comm, Pi.smul_apply, nsmul_eq_mul, Nat.cast_pow]
      exact add_mem ih (Ideal.pow_le_pow_right hmn (hmem _))
  choose L hL using fun i ↦ (isPrecomplete_comap_constantCoeff (Ideal.span {(p : R)})).prec
    (f := fun n ↦ s n i) fun hmn ↦ by
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← neg_mem_iff, neg_sub]
      exact hcauchy hmn i
  have := isHausdorff_comap_constantCoeff (Ideal.span {(p : R)})
  refine ⟨L, (IsHausdorff.eq_iff_smodEq (I := 𝔍)).mpr fun n ↦ ?_⟩
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
  have hL' : frobeniusAssembly R p (s n - L) ∈ 𝔍 ^ n := frobeniusAssembly_mem_pow p fun i ↦ by
    have := hL i n
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at this
    exact this
  have : frobeniusAssembly R p L - f = -(frobeniusAssembly R p (s n - L) + p ^ n * H^[n] f) := by
    conv_lhs => rw [hs n]
    rw [map_sub]
    ring
  rw [this, neg_mem_iff]
  exact add_mem hL' (hmem _)

/-- **Frobenius coordinates.** If `R` is `p`-adically complete and `p` is a nonzerodivisor of `R`,
every series is uniquely `∑ i < p, (1 + X) ^ i * φ (a i)`. -/
theorem frobeniusAssembly_bijective [Fact p.Prime] [IsAdicComplete (Ideal.span {(p : R)}) R]
    (hp : IsSMulRegular R (p : R)) : Function.Bijective (frobeniusAssembly R p) :=
  ⟨frobeniusAssembly_injective p hp, frobeniusAssembly_surjective p⟩

/-! ### The Frobenius power basis -/

section Basis

variable [Fact p.Prime] [IsAdicComplete (Ideal.span {(p : R)}) R]

variable (R) in
/-- **The Frobenius power basis.** If `R` is `p`-adically complete and `p` is a nonzerodivisor of
`R`, the series `(1 + X) ^ i`, `i < p`, form a basis of `R⟦X⟧` as an algebra over itself through
the Frobenius substitution `f ↦ f ((1 + X) ^ p - 1)`. The module structure is passed explicitly,
since it differs from the ordinary self-module structure. -/
noncomputable def frobeniusBasis (hp : IsSMulRegular R (p : R)) :
    @Module.Basis (Fin p) R⟦X⟧ R⟦X⟧ _ _ (frobeniusAlgebra R p).toModule :=
  @Module.Basis.mk _ _ _ _ _ (frobeniusAlgebra R p).toModule (fun i : Fin p ↦ (1 + X) ^ (i : ℕ))
    ((@Fintype.linearIndependent_iff _ _ _ _ _ (frobeniusAlgebra R p).toModule _ _).mpr
      fun g hg ↦ by
        have h0 : frobeniusAssembly R p g = 0 := by
          rw [← hg, frobeniusAssembly_apply]
          exact Finset.sum_congr rfl fun i _ ↦ by rw [frobeniusAlgebra_smul, mul_comm]
        exact congrFun (frobeniusAssembly_injective p hp (h0.trans (map_zero _).symm)))
    fun f _ ↦ (@Submodule.mem_span_range_iff_exists_fun _ _ _ _ _ _
      (frobeniusAlgebra R p).toModule _ _).mpr <| by
        obtain ⟨a, rfl⟩ := frobeniusAssembly_surjective p f
        exact ⟨a, Finset.sum_congr rfl fun i _ ↦ by rw [frobeniusAlgebra_smul, mul_comm]⟩

variable (hp : IsSMulRegular R (p : R))

@[simp]
theorem frobeniusBasis_apply (i : Fin p) : frobeniusBasis R p hp i = (1 + X) ^ (i : ℕ) :=
  @Module.Basis.mk_apply _ _ _ _ _ (frobeniusAlgebra R p).toModule _ _ _ i

/-- Assembling coordinates is the inverse of the coordinate map of the Frobenius basis. -/
theorem frobeniusBasis_equivFun_symm_apply (a : Fin p → R⟦X⟧) :
    (@Module.Basis.equivFun _ _ _ _ _ (frobeniusAlgebra R p).toModule _
      (frobeniusBasis R p hp)).symm a = frobeniusAssembly R p a := by
  rw [@Module.Basis.equivFun_symm_apply _ _ _ _ _ (frobeniusAlgebra R p).toModule,
    frobeniusAssembly_apply]
  exact Finset.sum_congr rfl fun i _ ↦ by
    rw [frobeniusBasis_apply, frobeniusAlgebra_smul, mul_comm]

/-- Every series is the assembly of its coordinates `c` in the Frobenius basis:
`f = ∑ i < p, (1 + X) ^ i * φ (c i)`. -/
@[simp]
theorem frobeniusAssembly_frobeniusBasis_repr (f : R⟦X⟧) :
    frobeniusAssembly R p
      (@Module.Basis.repr _ _ _ _ _ (frobeniusAlgebra R p).toModule (frobeniusBasis R p hp) f) =
      f := by
  rw [← @Module.Basis.equivFun_apply _ _ _ _ _ (frobeniusAlgebra R p).toModule,
    ← frobeniusBasis_equivFun_symm_apply p hp, LinearEquiv.symm_apply_apply]

/-- The coordinates of an assembly in the Frobenius basis are the assembled coordinates. -/
@[simp]
theorem frobeniusBasis_repr_frobeniusAssembly (a : Fin p → R⟦X⟧) (i : Fin p) :
    @Module.Basis.repr _ _ _ _ _ (frobeniusAlgebra R p).toModule (frobeniusBasis R p hp)
      (frobeniusAssembly R p a) i = a i := by
  rw [← @Module.Basis.equivFun_apply _ _ _ _ _ (frobeniusAlgebra R p).toModule,
    ← frobeniusBasis_equivFun_symm_apply p hp, LinearEquiv.apply_symm_apply]

include hp in
/-- The power series ring has rank `p` over itself through the Frobenius substitution. -/
theorem finrank_frobeniusAlgebra [Nontrivial R] :
    @Module.finrank R⟦X⟧ R⟦X⟧ _ _ (frobeniusAlgebra R p).toModule = p := by
  rw [@Module.finrank_eq_card_basis _ _ _ _ (frobeniusAlgebra R p).toModule _ _ _
    (frobeniusBasis R p hp), Fintype.card_fin]

end Basis

/-! At `p = 2` the scalar `X` acts on `1` by `2 X + X ^ 2`, not by `X`. -/

example : frobeniusSubst ℤ 2 X = 2 * X + X ^ 2 := by
  rw [frobeniusSubst_X]
  ring

end PowerSeries
