/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.Polynomial.UniversalFactorizationRing
public import TauCeti.RingTheory.GradedAlgebra.MvPolynomial
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Alternant
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import TauCeti.Algebra.Polynomial.Taylor
import TauCeti.Algebra.Prime.Finset
import TauCeti.RingTheory.MvPolynomial.Prime
import TauCeti.RingTheory.MvPolynomial.Symmetric.Homogeneous
import TauCeti.RingTheory.MvPolynomial.WeightedHomogeneous
import TauCeti.RingTheory.Polynomial.Resultant.Discriminant
import TauCeti.RingTheory.Polynomial.Resultant.RootCoordinates
import TauCeti.RingTheory.Polynomial.Vieta

/-!
# The generic and depressed discriminants

The generic monic polynomial of degree `m`, `Polynomial.freeMonic R m`, has coefficients
`X 0, …, X (m - 1)` of natural weights `m, …, 1` (the coefficient of `X ^ i` has weight `m - i`).
Under the Vieta homomorphism sending `X i` to `(-1) ^ (m - i) * esymm (Fin m) R (m - i)`,
`Polynomial.freeMonic R m` maps to `∏ j : Fin m, (X - C (X j))`, whose discriminant is the square
of the Vandermonde alternant `∏_{i < j} (X j - X i)`. Since the Vieta homomorphism is injective,
this determines both the weighted degree `m * (m - 1)` of the generic discriminant (over any
commutative ring) and its irreducibility and primality (over any integral domain, respectively
unique factorization domain, in which `2 ≠ 0`, for `m ≥ 2`).

Setting the subleading coefficient to zero gives the generic depressed monic polynomial
`TauCeti.genericDepressed R m = X ^ m + ∑ i : Fin (m - 1), C (X i) * X ^ (m - (i + 2))`,
with weights `depressedWeight m i = i + 2`. Specializing `freeMonic` shows that its discriminant
`TauCeti.depressedDiscr R m` has weight `m * (m - 1)` over any commutative ring. Whenever `m` is
invertible in `R`, the Tschirnhaus shift `X ↦ X + a₁ / m` induces an `R`-algebra automorphism
`TauCeti.tschirnhausEquiv` of `MvPolynomial (Fin m) R` carrying `(freeMonic R m).discr` to the
variable-embedded `depressedDiscr R m`. Consequently, `depressedDiscr R m` is prime whenever
`2 ≠ 0` and `IsUnit (m : R)` over a unique factorization domain (in particular over a field of
characteristic zero), so localizing `MvPolynomial (Fin (m - 1)) R` away from `depressedDiscr R m`
has homogeneous unit degrees `m * (m - 1) ℤ` and shift class group `ZMod (m * (m - 1))`.

In degrees `2` and `3` the depressed discriminant is `-4 * X 0` and `-4 * X 0 ^ 3 - 27 * X 1 ^ 2`.
In particular, when `2 ≠ 0` and `3` is invertible in a unique factorization domain `R`,
`4 * X 0 ^ 3 + 27 * X 1 ^ 2` is prime of weight `12` for the weights `![4, 6]`, giving shift class
group `ZMod 12`.

## Main definitions

* `TauCeti.freeMonicWeight`: the weight `i ↦ m - i` on the coefficients of `Polynomial.freeMonic`.
* `TauCeti.vietaAlgHom`: the Vieta substitution `X i ↦ (-1) ^ (m - i) * esymm (Fin m) R (m - i)`.
* `TauCeti.genericDepressed`: the generic depressed monic polynomial of degree `m`.
* `TauCeti.depressedWeight`: the weight `i ↦ i + 2` on the coefficients of `genericDepressed`.
* `TauCeti.depressedDiscr`: the discriminant of `genericDepressed`.
* `TauCeti.depressedEmb`: the variable embedding `j ↦ m - 2 - j` from depressed to monic
  coefficients.
* `TauCeti.tschirnhausEquiv`: the Tschirnhaus automorphism eliminating the subleading coefficient
  when `IsUnit (m : R)`.
* `TauCeti.shiftClassGroupAwayDepressedDiscrEquiv`: the shift class group `ZMod (m * (m - 1))`
  after inverting `depressedDiscr R m`.
* `TauCeti.shiftClassGroupAwayWeierstrassEquiv`: the shift class group `ZMod 12` after inverting
  `4 * X 0 ^ 3 + 27 * X 1 ^ 2` with weights `![4, 6]`.

## Main results

* `TauCeti.discr_freeMonic_mem_weightedHomogeneousSubmodule`: `(Polynomial.freeMonic R m).discr`
  has weight `m * (m - 1)`.
* `TauCeti.irreducible_discr_freeMonic` and `TauCeti.prime_discr_freeMonic`: irreducibility and
  primality of `(Polynomial.freeMonic R m).discr` for `m ≥ 2` when `(2 : R) ≠ 0`.
* `TauCeti.depressedDiscr_mem`: `depressedDiscr R m` has weight `m * (m - 1)` for `depressedWeight`.
* `TauCeti.depressedDiscr_prime` and `TauCeti.depressedDiscr_prime_of_charZero`: primality of
  `depressedDiscr R m` for `m ≥ 2` when `(2 : R) ≠ 0` and `IsUnit (m : R)` (in particular over a
  field of characteristic zero).
* `TauCeti.homogeneousUnitDegrees_away_depressedDiscr`: the homogeneous unit degrees after
  inverting `depressedDiscr R m` are `AddSubgroup.zmultiples (m * (m - 1))`.
* `TauCeti.depressedDiscr_two` and `TauCeti.depressedDiscr_three`: explicit formulas in degrees
  `2` and `3`.
-/

public section

namespace TauCeti

open Finset MvPolynomial TauCeti.GradedAlgebra

attribute [local instance] MvPolynomial.WeightedHomogeneousSubmodule.gradedMonoid

/-! ### The Vieta homomorphism and the discriminant of `Polynomial.freeMonic` -/

section FreeMonic

/-- The natural weights on the coefficients of `Polynomial.freeMonic R m`: the coefficient `X i`
of `X ^ i` has weight `m - i`. -/
def freeMonicWeight (m : ℕ) : Fin m → ℤ := fun i ↦ (m : ℤ) - (i : ℕ)

/-- The weight assigned by `freeMonicWeight m` to `i : Fin m` is `m - i`. -/
@[simp]
theorem freeMonicWeight_apply (m : ℕ) (i : Fin m) : freeMonicWeight m i = (m : ℤ) - (i : ℕ) :=
  (rfl)

/-- The Vieta algebra homomorphism sending the `i`-th coefficient variable of `Polynomial.freeMonic`
to `(-1) ^ (m - i) * esymm (Fin m) R (m - i)`. -/
noncomputable def vietaAlgHom (R : Type*) [CommRing R] (m : ℕ) :
    MvPolynomial (Fin m) R →ₐ[R] MvPolynomial (Fin m) R :=
  aeval fun i : Fin m ↦
    (-1 : MvPolynomial (Fin m) R) ^ (m - (i : ℕ)) * esymm (Fin m) R (m - (i : ℕ))

/-- The action of `vietaAlgHom R m` on a variable `X i`. -/
@[simp]
theorem vietaAlgHom_X (R : Type*) [CommRing R] (m : ℕ) (i : Fin m) :
    vietaAlgHom R m (X i) =
      (-1 : MvPolynomial (Fin m) R) ^ (m - (i : ℕ)) * esymm (Fin m) R (m - (i : ℕ)) :=
  aeval_X _ i

/-- The Vieta homomorphism is injective over any commutative ring, since it is the elementary
symmetric substitution precomposed with a signed reversal of variables. -/
theorem vietaAlgHom_injective (R : Type*) [CommRing R] (m : ℕ) :
    Function.Injective (vietaAlgHom R m) := by
  let f : MvPolynomial (Fin m) R →ₐ[R] MvPolynomial (Fin m) R :=
    aeval fun i : Fin m ↦ (-1 : MvPolynomial (Fin m) R) ^ (m - (i : ℕ)) * X i.rev
  let g : MvPolynomial (Fin m) R →ₐ[R] MvPolynomial (Fin m) R :=
    aeval fun j : Fin m ↦ (-1 : MvPolynomial (Fin m) R) ^ ((j : ℕ) + 1) * X j.rev
  have hfg : f.comp g = AlgHom.id R _ := by
    refine algHom_ext fun j ↦ ?_
    have hj : (j : ℕ) + 1 + (m - (j.rev : ℕ)) = 2 * ((j : ℕ) + 1) := by
      simp only [Fin.val_rev]
      omega
    simp only [AlgHom.comp_apply, AlgHom.id_apply, f, g, aeval_X, map_mul, map_pow, map_neg,
      map_one, Fin.rev_rev, ← mul_assoc, ← pow_add]
    rw [hj, pow_mul]
    simp
  have hgf : g.comp f = AlgHom.id R _ := by
    refine algHom_ext fun i ↦ ?_
    have hi : m - (i : ℕ) + ((i.rev : ℕ) + 1) = 2 * (m - (i : ℕ)) := by
      simp only [Fin.val_rev]
      omega
    simp only [AlgHom.comp_apply, AlgHom.id_apply, f, g, aeval_X, map_mul, map_pow, map_neg,
      map_one, Fin.rev_rev, ← mul_assoc, ← pow_add]
    rw [hi, pow_mul]
    simp
  let e : MvPolynomial (Fin m) R ≃ₐ[R] MvPolynomial (Fin m) R := AlgEquiv.ofAlgHom f g hfg hgf
  have halg : vietaAlgHom R m =
      (symmetricSubalgebra (Fin m) R).val.comp ((esymmAlgHom (Fin m) R m).comp e.toAlgHom) := by
    refine algHom_ext fun i ↦ ?_
    simp [e, f, esymmAlgHom_apply]
    congr 2
    omega
  have hcoe : (vietaAlgHom R m : MvPolynomial (Fin m) R → MvPolynomial (Fin m) R) =
      Subtype.val ∘ esymmAlgHom (Fin m) R m ∘ e := congrArg DFunLike.coe halg
  rw [hcoe]
  exact Subtype.val_injective.comp ((esymmAlgHom_fin_injective R le_rfl).comp e.injective)

/-- Every polynomial in the image of `vietaAlgHom R m` is symmetric in the variables. -/
theorem rename_vietaAlgHom {R : Type*} [CommRing R] {m : ℕ} (τ : Equiv.Perm (Fin m))
    (p : MvPolynomial (Fin m) R) : rename τ (vietaAlgHom R m p) = vietaAlgHom R m p := by
  have h : (rename τ).comp (vietaAlgHom R m) = vietaAlgHom R m := by
    refine algHom_ext fun i ↦ ?_
    simp only [AlgHom.comp_apply, vietaAlgHom_X, map_mul, map_pow, map_neg, map_one]
    rw [esymm_isSymmetric (Fin m) R (m - (i : ℕ)) τ]
  exact AlgHom.congr_fun h p

/-- Mapping `Polynomial.freeMonic R m` along `vietaAlgHom R m` produces the split monic polynomial
`∏ j : Fin m, (X - C (X j))`. -/
theorem map_freeMonic_vietaAlgHom (R : Type*) [CommRing R] (m : ℕ) :
    (Polynomial.freeMonic R m).map (vietaAlgHom R m).toRingHom =
      ∏ j : Fin m, (Polynomial.X - Polynomial.C (X j)) := by
  nontriviality R
  have hmon : (∏ j : Fin m, (Polynomial.X - Polynomial.C (X j : MvPolynomial (Fin m) R))).Monic :=
    Polynomial.monic_prod_X_sub_C _ _
  have hdeg :
      (∏ j : Fin m, (Polynomial.X - Polynomial.C (X j : MvPolynomial (Fin m) R))).natDegree = m :=
    by simp [Polynomial.natDegree_finsetProd_X_sub_C_eq_card]
  refine AddMonoidAlgebra.ext (Finsupp.ext fun k ↦ ?_)
  rw [Polynomial.coeff_map, Polynomial.coeff_freeMonic]
  split_ifs with hlt heq
  · simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, vietaAlgHom_X]
    have hvieta := aeval_esymm_eq_coeff_prod_X_sub_C (R := R)
      (X : Fin m → MvPolynomial (Fin m) R) (k := m - k) (by simp)
    simp only [aeval_X_left, AlgHom.id_apply, Fintype.card_fin] at hvieta
    rw [hvieta, Nat.sub_sub_self hlt.le, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
    simp
  · have hlead :
        (∏ j : Fin m, (Polynomial.X - Polynomial.C (X j : MvPolynomial (Fin m) R))).coeff m = 1 :=
      by
        have h := hmon.leadingCoeff
        rw [Polynomial.leadingCoeff, hdeg] at h
        exact h
    rw [heq, map_one, hlead]
  · rw [map_zero, Polynomial.coeff_eq_zero_of_natDegree_lt]
    rw [hdeg]
    omega

/-- Applying `vietaAlgHom R m` to the discriminant of `Polynomial.freeMonic R m` yields the square
of the Vandermonde alternant. -/
theorem vietaAlgHom_discr_freeMonic (R : Type*) [CommRing R] (m : ℕ) :
    vietaAlgHom R m (Polynomial.freeMonic R m).discr =
      (alternant (Fin m) R (fun j ↦ (j : ℕ))) ^ 2 := by
  have h := (Polynomial.monic_freeMonic R m).discr_map (vietaAlgHom R m).toRingHom
  rw [map_freeMonic_vietaAlgHom, Polynomial.discr_prod_X_sub_C] at h
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h
  rw [← h, alternant_fin_val_eq_vandermonde, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  ring

/-- The discriminant of `Polynomial.freeMonic R m` is weighted homogeneous of weight `m * (m - 1)`
for `freeMonicWeight m`, over any commutative ring `R`. -/
theorem discr_freeMonic_mem_weightedHomogeneousSubmodule (R : Type*) [CommRing R] (m : ℕ) :
    (Polynomial.freeMonic R m).discr ∈
      weightedHomogeneousSubmodule R (freeMonicWeight m) ((m : ℤ) * (m - 1)) := by
  let wNat : Fin m → ℕ := fun i ↦ m - (i : ℕ)
  have hg : ∀ i : Fin m, (vietaAlgHom R m (X i)).IsHomogeneous (wNat i) := fun i ↦ by
    have hC : (-1 : MvPolynomial (Fin m) R) ^ (m - (i : ℕ)) =
        C ((-1 : R) ^ (m - (i : ℕ))) := by simp
    rw [vietaAlgHom_X, hC]
    exact (isHomogeneous_esymm (σ := Fin m) (R := R) (m - (i : ℕ))).C_mul _
  have hsum : 2 * ∑ j : Fin m, (j : ℕ) = m * (m - 1) := by
    rw [Fin.sum_univ_eq_sum_range (fun j ↦ j) m, mul_comm, Finset.sum_range_id_mul_two]
  have hhom : (vietaAlgHom R m (Polynomial.freeMonic R m).discr).IsHomogeneous (m * (m - 1)) := by
    rw [vietaAlgHom_discr_freeMonic, ← hsum, mul_comm]
    exact (isHomogeneous_alternant (R := R) (fun j : Fin m ↦ (j : ℕ))).pow 2
  have hnat : (Polynomial.freeMonic R m).discr.IsWeightedHomogeneous wNat (m * (m - 1)) :=
    isWeightedHomogeneous_of_isHomogeneous_aeval (w := wNat)
      (g := fun i : Fin m ↦ (-1 : MvPolynomial (Fin m) R) ^ (m - (i : ℕ)) *
        esymm (Fin m) R (m - (i : ℕ)))
      (fun i ↦ by simpa [vietaAlgHom_X] using hg i) (vietaAlgHom_injective R m) hhom
  intro d hd
  have hwd : Finsupp.weight wNat d = m * (m - 1) := hnat hd
  have hcast : Finsupp.weight (freeMonicWeight m) d = (Finsupp.weight wNat d : ℤ) := by
    simp only [Finsupp.weight_apply, Finsupp.sum, Nat.cast_sum, smul_eq_mul, Nat.cast_mul]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp [freeMonicWeight, wNat, Nat.cast_sub i.isLt.le]
  rw [hcast, hwd]
  rcases m with _ | m
  · simp
  · push_cast
    ring

/-- The Vandermonde alternant expressed as a single product over the finset of ordered pairs
`i < j`. -/
private theorem alternant_fin_val_eq_prod_pairs (R : Type*) [CommRing R] (m : ℕ) :
    alternant (Fin m) R (fun j ↦ (j : ℕ)) =
      ∏ p ∈ (univ : Finset (Fin m × Fin m)).filter (fun p ↦ p.1 < p.2), (X p.2 - X p.1) := by
  rw [alternant_fin_val_eq_vandermonde,
    ← Finset.prod_sigma
      (f := fun p : Σ _ : Fin m, Fin m ↦ (X p.2 - X p.1 : MvPolynomial (Fin m) R))]
  refine Finset.prod_bij (fun p _ ↦ (p.1, p.2)) ?_ ?_ ?_ ?_
  · intro p hp
    simp only [mem_sigma, mem_univ, mem_Ioi, true_and] at hp
    simp [hp]
  · intro p₁ _ p₂ _ h
    cases p₁
    cases p₂
    simpa using h
  · intro q hq
    simp only [mem_filter, mem_univ, true_and] at hq
    exact ⟨⟨q.1, q.2⟩, by simp [hq], rfl⟩
  · intro _ _
    rfl

/-- For any two strictly ordered pairs in `Fin m`, some permutation maps one to the other. -/
private theorem exists_perm_map_pair {m : ℕ} {p q : Fin m × Fin m} (hp : p.1 < p.2)
    (hq : q.1 < q.2) : ∃ τ : Equiv.Perm (Fin m), τ p.1 = q.1 ∧ τ p.2 = q.2 := by
  let τ₁ : Equiv.Perm (Fin m) := Equiv.swap p.1 q.1
  let τ : Equiv.Perm (Fin m) := Equiv.swap (τ₁ p.2) q.2 * τ₁
  refine ⟨τ, ?_, by simp [τ]⟩
  have hne : τ₁ p.2 ≠ q.1 := fun h ↦
    hp.ne' (τ₁.injective (h.trans (Equiv.swap_apply_left p.1 q.1).symm))
  simp [τ, τ₁, Equiv.swap_apply_of_ne_of_ne hne.symm hq.ne]

/-- Any symmetric divisor `vietaAlgHom R m f` of `(alternant ...)^2` over a domain is associated to
`alternant ^ c` for some `c ≤ 2`. -/
private theorem exists_associated_alternant_pow_of_dvd_discr {R : Type*} [CommRing R] [IsDomain R]
    {m : ℕ} (hm : 2 ≤ m) {f : MvPolynomial (Fin m) R}
    (hdvd : vietaAlgHom R m f ∣ vietaAlgHom R m (Polynomial.freeMonic R m).discr) :
    ∃ c ≤ 2, Associated (vietaAlgHom R m f) ((alternant (Fin m) R (fun j ↦ (j : ℕ))) ^ c) := by
  let pairs : Finset (Fin m × Fin m) := univ.filter fun p ↦ p.1 < p.2
  have halt : alternant (Fin m) R (fun j ↦ (j : ℕ)) = ∏ p ∈ pairs, (X p.2 - X p.1) :=
    alternant_fin_val_eq_prod_pairs R m
  rw [vietaAlgHom_discr_freeMonic, halt, ← Finset.prod_pow] at hdvd
  have hprime : ∀ p ∈ pairs, Prime (X p.2 - X p.1 : MvPolynomial (Fin m) R) := fun p hp ↦
    prime_X_sub_X (ne_of_lt (mem_filter.mp hp).2)
  obtain ⟨k, hk, hassoc⟩ := (dvd_finsetProd_prime_pow_iff hprime (fun _ ↦ 2)).mp hdvd
  -- By `S_m`-invariance of `vietaAlgHom R m f`, all ordered pairs carry the same exponent `k p`.
  have hk_le : ∀ p ∈ pairs, ∀ q ∈ pairs, k p ≤ k q := fun p hp q hq ↦ by
    obtain ⟨τ, hτ1, hτ2⟩ := exists_perm_map_pair (mem_filter.mp hp).2 (mem_filter.mp hq).2
    have hpow_dvd : (X q.2 - X q.1 : MvPolynomial (Fin m) R) ^ k p ∣
        ∏ r ∈ pairs, (X r.2 - X r.1) ^ k r := by
      have h1 : (X p.2 - X p.1 : MvPolynomial (Fin m) R) ^ k p ∣ vietaAlgHom R m f :=
        (Finset.dvd_prod_of_mem (fun r ↦ (X r.2 - X r.1) ^ k r) hp).trans hassoc.symm.dvd
      have h2 := map_dvd (rename (R := R) τ) h1
      rw [rename_vietaAlgHom, map_pow, map_sub, rename_X, rename_X, hτ1, hτ2] at h2
      exact h2.trans hassoc.dvd
    have hndvd : ∀ r ∈ pairs, r ≠ q →
        ¬ (X q.2 - X q.1 : MvPolynomial (Fin m) R) ∣ (X r.2 - X r.1) :=
      fun r hr hrq hdiv ↦ by
        have hr_lt : r.1 < r.2 := (mem_filter.mp hr).2
        have hq_lt : q.1 < q.2 := (mem_filter.mp hq).2
        have hna : ¬ Associated (X q.2 - X q.1 : MvPolynomial (Fin m) R) (X r.2 - X r.1) :=
          not_associated_X_sub_X
            (not_and_or.mp fun h ↦ hrq (Prod.ext h.1 h.2))
            (not_and_or.mp fun h ↦ lt_asymm hq_lt (h.2 ▸ h.1 ▸ hr_lt))
            hr_lt.ne
        exact hna ((hprime q hq).associated_of_dvd (hprime r hr) hdiv)
    exact ((hprime q hq).pow_dvd_finsetProd_pow_iff
      (p := fun r : Fin m × Fin m ↦ (X r.2 - X r.1 : MvPolynomial (Fin m) R))
      hq hndvd k).mp hpow_dvd
  let p₀ : Fin m × Fin m := (⟨0, by omega⟩, ⟨1, by omega⟩)
  have hp₀ : p₀ ∈ pairs := by simp [pairs, p₀]
  refine ⟨k p₀, hk p₀ hp₀, ?_⟩
  rw [halt, ← Finset.prod_pow]
  have hprod : ∏ p ∈ pairs, (X p.2 - X p.1 : MvPolynomial (Fin m) R) ^ k p =
      ∏ p ∈ pairs, (X p.2 - X p.1) ^ k p₀ :=
    Finset.prod_congr rfl fun p hp ↦ by
      rw [le_antisymm (hk_le p hp p₀ hp₀) (hk_le p₀ hp₀ p hp)]
  rwa [← hprod]

/-- Over a domain in which `2 ≠ 0`, a symmetric polynomial `vietaAlgHom R m f` cannot equal a
nonzero scalar multiple of the Vandermonde alternant for `m ≥ 2`. -/
private theorem not_vietaAlgHom_eq_alternant_mul_C {R : Type*} [CommRing R] [IsDomain R]
    (h2 : (2 : R) ≠ 0) {m : ℕ} (hm : 2 ≤ m) {f : MvPolynomial (Fin m) R} {r : R} (hr : r ≠ 0)
    (hu : alternant (Fin m) R (fun j ↦ (j : ℕ)) * C r = vietaAlgHom R m f) : False := by
  let i₀ : Fin m := ⟨0, by omega⟩
  let i₁ : Fin m := ⟨1, by omega⟩
  have hi01 : i₀ ≠ i₁ := by simp [i₀, i₁]
  have halt_ne : alternant (Fin m) R (fun j ↦ (j : ℕ)) ≠ 0 :=
    alternant_ne_zero_of_injective Fin.val_injective
  have hswap := congrArg (rename (R := R) (Equiv.swap i₀ i₁)) hu
  rw [rename_vietaAlgHom, map_mul, rename_alternant, Equiv.Perm.sign_swap hi01, rename_C,
    Units.smul_def, Units.val_neg, Units.val_one, neg_one_zsmul, neg_mul, ← hu] at hswap
  have hzero : C (2 * r) * alternant (Fin m) R (fun j ↦ (j : ℕ)) = 0 := by
    have hsum : alternant (Fin m) R (fun j ↦ (j : ℕ)) * C r +
        alternant (Fin m) R (fun j ↦ (j : ℕ)) * C r = 0 := by
      linear_combination -hswap
    have hrew : C (2 * r) * alternant (Fin m) R (fun j ↦ (j : ℕ)) =
        alternant (Fin m) R (fun j ↦ (j : ℕ)) * C r +
          alternant (Fin m) R (fun j ↦ (j : ℕ)) * C r := by
      rw [map_mul, map_ofNat]
      ring
    rw [hrew, hsum]
  rcases mul_eq_zero.mp hzero with hcr | halt0
  · exact mul_ne_zero h2 hr (C_eq_zero.mp hcr)
  · exact halt_ne halt0

/-- **Irreducibility of the generic discriminant.** Over any integral domain in which `2 ≠ 0`,
the discriminant of `Polynomial.freeMonic R m` is irreducible for every `m ≥ 2`. -/
theorem irreducible_discr_freeMonic {R : Type*} [CommRing R] [IsDomain R] (h2 : (2 : R) ≠ 0)
    {m : ℕ} (hm : 2 ≤ m) : Irreducible (Polynomial.freeMonic R m).discr := by
  let i₀ : Fin m := ⟨0, by omega⟩
  let i₁ : Fin m := ⟨1, by omega⟩
  have halt_ne : alternant (Fin m) R (fun j ↦ (j : ℕ)) ≠ 0 :=
    alternant_ne_zero_of_injective Fin.val_injective
  have hdiscr_ne : (Polynomial.freeMonic R m).discr ≠ 0 := fun h ↦ by
    have h0 := congrArg (vietaAlgHom R m) h
    rw [map_zero, vietaAlgHom_discr_freeMonic] at h0
    exact pow_ne_zero 2 halt_ne h0
  refine ⟨?_, fun f g hfg ↦ ?_⟩
  · -- `discr` is not a unit because its Vieta image vanishes at `0`.
    intro hu
    have hu' : IsUnit (vietaAlgHom R m (Polynomial.freeMonic R m).discr) := hu.map (vietaAlgHom R m)
    rw [vietaAlgHom_discr_freeMonic] at hu'
    have hi01_lt : i₀ < i₁ := by simp [i₀, i₁]
    have heval0 : eval (0 : Fin m → R) (alternant (Fin m) R (fun j ↦ (j : ℕ))) = 0 := by
      rw [alternant_fin_val_eq_vandermonde, map_prod]
      refine Finset.prod_eq_zero (mem_univ i₀) ?_
      rw [map_prod]
      refine Finset.prod_eq_zero (mem_Ioi.mpr hi01_lt) ?_
      simp
    have h0 : eval (0 : Fin m → R) ((alternant (Fin m) R (fun j ↦ (j : ℕ))) ^ 2) = 0 := by
      rw [map_pow, heval0, zero_pow two_ne_zero]
    exact (hu'.map (eval (0 : Fin m → R))).ne_zero h0
  · have hdiv : vietaAlgHom R m f ∣ vietaAlgHom R m (Polynomial.freeMonic R m).discr :=
      ⟨vietaAlgHom R m g, by rw [← map_mul, hfg]⟩
    obtain ⟨c, hc, hassoc⟩ := exists_associated_alternant_pow_of_dvd_discr hm hdiv
    obtain ⟨u, hu⟩ := hassoc.symm
    obtain ⟨r, hr, hru⟩ := (isUnit_iff_eq_C_of_isReduced (P := (u : MvPolynomial (Fin m) R))).mp
      u.isUnit
    rw [hru] at hu
    have hc_cases : c = 0 ∨ c = 1 ∨ c = 2 := by omega
    rcases hc_cases with rfl | rfl | rfl
    · left
      rw [pow_zero, one_mul] at hu
      have hf : f = C r := vietaAlgHom_injective R m (by rw [← hu, algHom_C, algebraMap_eq])
      exact hf ▸ hr.map C
    · exact (not_vietaAlgHom_eq_alternant_mul_C h2 hm hr.ne_zero (by simpa using hu)).elim
    · right
      have hCr : vietaAlgHom R m (C r) = C r := by rw [algHom_C, algebraMap_eq]
      rw [← vietaAlgHom_discr_freeMonic, ← hCr, ← map_mul] at hu
      have hf : f = (Polynomial.freeMonic R m).discr * C r := vietaAlgHom_injective R m hu.symm
      have hmul : (Polynomial.freeMonic R m).discr * (C r * g) =
          (Polynomial.freeMonic R m).discr * 1 := by
        rw [← mul_assoc, ← hf, ← hfg, mul_one]
      have hcg : C r * g = 1 := mul_left_cancel₀ hdiscr_ne hmul
      exact isUnit_iff_exists_inv.mpr ⟨C r, by rw [mul_comm, hcg]⟩

/-- **Primality of the generic discriminant.** Over any unique factorization domain in which
`2 ≠ 0`, the discriminant of `Polynomial.freeMonic R m` is prime for every `m ≥ 2`. -/
theorem prime_discr_freeMonic {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (h2 : (2 : R) ≠ 0) {m : ℕ} (hm : 2 ≤ m) : Prime (Polynomial.freeMonic R m).discr :=
  UniqueFactorizationMonoid.irreducible_iff_prime.mp (irreducible_discr_freeMonic h2 hm)

end FreeMonic

/-! ### The generic depressed polynomial, its discriminant, and the Tschirnhaus automorphism -/

section Depressed

/-- The generic depressed monic polynomial of degree `m`,
`X ^ m + a₂ * X ^ (m - 2) + ⋯ + aₘ`, where `X i` (`i : Fin (m - 1)`) represents `a_{i + 2}`. -/
noncomputable def genericDepressed (R : Type*) [CommSemiring R] (m : ℕ) :
    Polynomial (MvPolynomial (Fin (m - 1)) R) :=
  Polynomial.X ^ m +
    ∑ i : Fin (m - 1), Polynomial.C (X i) * Polynomial.X ^ (m - (i.val + 2))

/-- Explicit expansion of `genericDepressed R m` as a sum of monomials. -/
theorem genericDepressed_eq (R : Type*) [CommSemiring R] (m : ℕ) :
    genericDepressed R m =
      Polynomial.X ^ m +
        ∑ i : Fin (m - 1), Polynomial.C (X i) * Polynomial.X ^ (m - (i.val + 2)) :=
  (rfl)

/-- The weight of the variable `a_{i + 2}` (`X i`) in `genericDepressed R m` is `i + 2`. -/
def depressedWeight (m : ℕ) : Fin (m - 1) → ℤ := fun i ↦ (i.val : ℤ) + 2

/-- The weight assigned by `depressedWeight m` to `i : Fin (m - 1)` is `i + 2`. -/
@[simp]
theorem depressedWeight_apply (m : ℕ) (i : Fin (m - 1)) : depressedWeight m i = (i.val : ℤ) + 2 :=
  (rfl)

/-- The discriminant of the generic depressed monic polynomial of degree `m`. -/
noncomputable def depressedDiscr (R : Type*) [CommRing R] (m : ℕ) : MvPolynomial (Fin (m - 1)) R :=
  Polynomial.discr (genericDepressed R m)

/-- Unfolding lemma expressing `depressedDiscr R m` as the discriminant of
`genericDepressed R m`. -/
theorem depressedDiscr_eq (R : Type*) [CommRing R] (m : ℕ) :
    depressedDiscr R m = Polynomial.discr (genericDepressed R m) :=
  (rfl)

/-- The `k`-th coefficient of `genericDepressed R m` is `X (m - 2 - k)` for `k + 2 ≤ m`, `1` for
`k = m`, and `0` otherwise. -/
theorem coeff_genericDepressed (R : Type*) [CommSemiring R] (m k : ℕ) :
    (genericDepressed R m).coeff k =
      if h : k + 2 ≤ m then X ⟨m - 2 - k, by omega⟩ else if k = m then 1 else 0 := by
  simp only [genericDepressed, Polynomial.coeff_add, Polynomial.coeff_X_pow,
    Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, mul_ite, mul_one, mul_zero]
  by_cases hlt : k + 2 ≤ m
  · have hkm : k ≠ m := by omega
    rw [dite_eq_left hlt, ite_eq_right hkm, zero_add,
      Finset.sum_eq_single (⟨m - 2 - k, by omega⟩ : Fin (m - 1))]
    · rw [ite_eq_left (by dsimp; omega)]
    · intro i _ hne
      refine ite_eq_right fun heq' ↦ hne ?_
      ext
      dsimp
      omega
    · intro hmem
      exact (hmem (mem_univ _)).elim
  · rw [dite_eq_right hlt, Finset.sum_eq_zero fun i _ ↦ ite_eq_right (by omega), add_zero]

/-- Over a nontrivial semiring, `genericDepressed R m` has degree `m`. -/
@[simp]
theorem degree_genericDepressed (R : Type*) [CommSemiring R] [Nontrivial R] (m : ℕ) :
    (genericDepressed R m).degree = m :=
  Polynomial.degree_eq_of_le_of_coeff_ne_zero
    ((Polynomial.degree_le_iff_coeff_zero _ _).mpr fun k hk ↦ by
      have hgt : m < k := WithBot.coe_lt_coe.mp hk
      have hlt : ¬ k + 2 ≤ m := by omega
      simp [coeff_genericDepressed, hlt, hgt.ne'])
    (by simp [coeff_genericDepressed])

/-- Over a nontrivial semiring, `genericDepressed R m` has `natDegree` equal to `m`. -/
@[simp]
theorem natDegree_genericDepressed (R : Type*) [CommSemiring R] [Nontrivial R] (m : ℕ) :
    (genericDepressed R m).natDegree = m :=
  Polynomial.natDegree_eq_of_degree_eq_some (degree_genericDepressed R m)

/-- The generic depressed polynomial `genericDepressed R m` is monic over any commutative
semiring. -/
theorem monic_genericDepressed (R : Type*) [CommSemiring R] (m : ℕ) :
    (genericDepressed R m).Monic := by
  nontriviality R
  rw [Polynomial.Monic, Polynomial.leadingCoeff, natDegree_genericDepressed, coeff_genericDepressed]
  simp

/-- Forming `genericDepressed` commutes with base change along any ring homomorphism. -/
@[simp]
theorem map_map_genericDepressed {R S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S)
    (m : ℕ) : (genericDepressed R m).map (MvPolynomial.map f) = genericDepressed S m := by
  simp [genericDepressed, Polynomial.map_sum]

/-- Forming `depressedDiscr` commutes with base change along any ring homomorphism. -/
@[simp]
theorem map_depressedDiscr {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (m : ℕ) :
    MvPolynomial.map f (depressedDiscr R m) = depressedDiscr S m := by
  rw [depressedDiscr, depressedDiscr, ← (monic_genericDepressed R m).discr_map,
    map_map_genericDepressed]

/-- **Weighted homogeneity of the generic depressed discriminant.** Over any commutative ring,
`depressedDiscr R m` has weight `m * (m - 1)` for `depressedWeight m`. -/
theorem depressedDiscr_mem (R : Type*) [CommRing R] (m : ℕ) :
    depressedDiscr R m ∈
      weightedHomogeneousSubmodule R (depressedWeight m) ((m : ℤ) * (m - 1)) := by
  let g : Fin m → MvPolynomial (Fin (m - 1)) R :=
    fun i ↦ if h : (i : ℕ) + 2 ≤ m then X ⟨m - 2 - (i : ℕ), by omega⟩ else 0
  have hmap : (Polynomial.freeMonic R m).map (aeval g).toRingHom = genericDepressed R m := by
    refine AddMonoidAlgebra.ext (Finsupp.ext fun k ↦ ?_)
    rw [Polynomial.coeff_map, Polynomial.coeff_freeMonic, coeff_genericDepressed]
    by_cases hlt : k + 2 ≤ m
    · have hkm : k < m := by omega
      simp [g, hlt, hkm]
    · by_cases hlt' : k < m
      · have hne : k ≠ m := hlt'.ne
        simp [g, hlt, hlt', hne]
      · by_cases heq : k = m
        · subst heq
          simp
        · simp [hlt, hlt', heq]
  have hdiscr : aeval g (Polynomial.freeMonic R m).discr = depressedDiscr R m := by
    have h := (Polynomial.monic_freeMonic R m).discr_map (aeval g).toRingHom
    rw [hmap] at h
    exact h.symm
  have hg : ∀ i : Fin m, (g i).IsWeightedHomogeneous (depressedWeight m) (freeMonicWeight m i) := by
    intro i
    dsimp only [g]
    split_ifs with h
    · convert isWeightedHomogeneous_X R (depressedWeight m) ⟨m - 2 - (i : ℕ), by omega⟩
      simp only [depressedWeight, freeMonicWeight]
      omega
    · exact isWeightedHomogeneous_zero R (depressedWeight m) _
  rw [mem_weightedHomogeneousSubmodule, ← hdiscr]
  exact ((mem_weightedHomogeneousSubmodule ..).mp
    (discr_freeMonic_mem_weightedHomogeneousSubmodule R m)).aeval hg

/-- The embedding sending variable `j` of `genericDepressed R m` to the coefficient index
`m - 2 - j` of `Polynomial.freeMonic R m`. -/
def depressedEmb (m : ℕ) (hm : 2 ≤ m) : Fin (m - 1) → Fin m :=
  fun j ↦ ⟨m - 2 - j.val, by omega⟩

/-- The image of `j : Fin (m - 1)` under `depressedEmb m hm` is `⟨m - 2 - j, _⟩`. -/
@[simp]
theorem depressedEmb_apply (m : ℕ) (hm : 2 ≤ m) (j : Fin (m - 1)) :
    depressedEmb m hm j = ⟨m - 2 - j.val, by omega⟩ :=
  (rfl)

/-- The variable embedding `depressedEmb m hm` is injective. -/
theorem depressedEmb_injective (m : ℕ) (hm : 2 ≤ m) :
    Function.Injective (depressedEmb m hm) := fun j₁ j₂ h ↦ by
  ext
  have := congrArg Fin.val h
  dsimp [depressedEmb] at this
  omega

private theorem coeff_map_rename_genericDepressed (R : Type*) [CommRing R] {m : ℕ} (hm : 2 ≤ m)
    (k : ℕ) :
    ((genericDepressed R m).map (rename (depressedEmb m hm)).toRingHom).coeff k =
      if h : k + 2 ≤ m then X ⟨k, by omega⟩ else if k = m then 1 else 0 := by
  rw [Polynomial.coeff_map, coeff_genericDepressed]
  split_ifs with h1 h2
  · simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_X, depressedEmb]
    congr 1
    ext
    dsimp
    omega
  · simp
  · simp

/-- The depressed monic polynomial of degree `m` viewed inside `(MvPolynomial (Fin m) R)[X]`
via `depressedEmb`. -/
private noncomputable def embeddedDepressed (R : Type*) [CommRing R] {m : ℕ} (hm : 2 ≤ m) :
    Polynomial (MvPolynomial (Fin m) R) :=
  (genericDepressed R m).map (rename (depressedEmb m hm)).toRingHom

/-- The Tschirnhaus shift `c * X (m - 1)` where `m * c = 1`. -/
private noncomputable def tschirnhausShift (R : Type*) [CommRing R] {m : ℕ} (hm : 2 ≤ m)
    (hmR : IsUnit (m : R)) : MvPolynomial (Fin m) R :=
  C ((hmR.unit⁻¹ : Rˣ) : R) * X ⟨m - 1, by omega⟩

/-- The algebra endomorphism of `MvPolynomial (Fin m) R` taking the depressed coefficients to the
shifted coefficients of `Polynomial.freeMonic R m` while fixing `X (m - 1)`. -/
private noncomputable def tschirnhausToDepressed (R : Type*) [CommRing R] {m : ℕ} (hm : 2 ≤ m)
    (hmR : IsUnit (m : R)) : MvPolynomial (Fin m) R →ₐ[R] MvPolynomial (Fin m) R :=
  aeval fun i : Fin m ↦
    if (i : ℕ) + 2 ≤ m then
      ((Polynomial.freeMonic R m).comp
        (Polynomial.X - Polynomial.C (tschirnhausShift R hm hmR))).coeff i
    else X ⟨m - 1, by omega⟩

/-- The algebra endomorphism of `MvPolynomial (Fin m) R` taking the coefficients of
`Polynomial.freeMonic R m` to those of the shifted depressed polynomial while fixing `X (m - 1)`. -/
private noncomputable def tschirnhausFromDepressed (R : Type*) [CommRing R] {m : ℕ} (hm : 2 ≤ m)
    (hmR : IsUnit (m : R)) : MvPolynomial (Fin m) R →ₐ[R] MvPolynomial (Fin m) R :=
  aeval fun i : Fin m ↦
    if (i : ℕ) + 2 ≤ m then
      ((embeddedDepressed R hm).comp
        (Polynomial.X + Polynomial.C (tschirnhausShift R hm hmR))).coeff i
    else X ⟨m - 1, by omega⟩

private theorem natCast_mul_C_inv_eq_one {R : Type*} [CommRing R] {m : ℕ} (hmR : IsUnit (m : R)) :
    (m : MvPolynomial (Fin m) R) * C ((hmR.unit⁻¹ : Rˣ) : R) = 1 := by
  rw [← map_natCast C, ← map_mul, hmR.mul_val_inv, map_one]

private theorem map_embeddedDepressed_tschirnhausToDepressed (R : Type*) [CommRing R] {m : ℕ}
    (hm : 2 ≤ m) (hmR : IsUnit (m : R)) :
    (embeddedDepressed R hm).map (tschirnhausToDepressed R hm hmR).toRingHom =
      (Polynomial.freeMonic R m).comp
        (Polynomial.X - Polynomial.C (tschirnhausShift R hm hmR)) := by
  nontriviality R
  let s := tschirnhausShift R hm hmR
  let F := Polynomial.freeMonic R m
  have hF_deg : F.natDegree = m := Polynomial.natDegree_freeMonic R m
  have hF_mon : F.Monic := Polynomial.monic_freeMonic R m
  have hshift : F.comp (Polynomial.X - Polynomial.C s) = Polynomial.taylor (-s) F := by
    rw [Polynomial.taylor_apply, map_neg, sub_eq_add_neg]
  refine AddMonoidAlgebra.ext (Finsupp.ext fun k ↦ ?_)
  rw [Polynomial.coeff_map, embeddedDepressed, coeff_map_rename_genericDepressed R hm]
  by_cases h1 : k + 2 ≤ m
  · simp [tschirnhausToDepressed, h1]
  · rw [dite_eq_right h1]
    by_cases h2 : k = m
    · have hlead : (Polynomial.taylor (-s) F).coeff m = 1 := by
        have h := Polynomial.leadingCoeff_taylor (-s) F
        rw [Polynomial.leadingCoeff, Polynomial.natDegree_taylor, hF_deg, hF_mon.leadingCoeff] at h
        exact h
      rw [h2, ite_eq_left rfl, map_one, hshift, hlead]
    · rw [ite_eq_right h2, map_zero, hshift]
      by_cases hkm1 : k = m - 1
      · subst hkm1
        have hnext := Polynomial.nextCoeff_taylor F (-s)
        have hpos1 : 0 < (Polynomial.taylor (-s) F).natDegree := by
          rw [Polynomial.natDegree_taylor, hF_deg]
          omega
        rw [Polynomial.nextCoeff_of_natDegree_pos hpos1,
          Polynomial.nextCoeff_of_natDegree_pos (by rw [hF_deg]; omega),
          Polynomial.natDegree_taylor, hF_deg, hF_mon.leadingCoeff, mul_one,
          Polynomial.coeff_freeMonic, dite_eq_left (by omega)] at hnext
        rw [hnext]
        calc
          (0 : MvPolynomial (Fin m) R)
            = X ⟨m - 1, by omega⟩ - ((m : MvPolynomial (Fin m) R) * C ((hmR.unit⁻¹ : Rˣ) : R)) *
                X ⟨m - 1, by omega⟩ := by rw [natCast_mul_C_inv_eq_one hmR, one_mul, sub_self]
          _ = X ⟨m - 1, by omega⟩ + (m : MvPolynomial (Fin m) R) * -s := by
                dsimp [s, tschirnhausShift]
                ring
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
        rw [Polynomial.natDegree_taylor, hF_deg]
        omega

private theorem map_freeMonic_tschirnhausFromDepressed (R : Type*) [CommRing R] {m : ℕ}
    (hm : 2 ≤ m) (hmR : IsUnit (m : R)) :
    (Polynomial.freeMonic R m).map (tschirnhausFromDepressed R hm hmR).toRingHom =
      (embeddedDepressed R hm).comp (Polynomial.X + Polynomial.C (tschirnhausShift R hm hmR)) := by
  nontriviality R
  let s := tschirnhausShift R hm hmR
  let G := embeddedDepressed R hm
  have hG_mon : G.Monic := (monic_genericDepressed R m).map _
  have hG_deg : G.natDegree = m := by
    dsimp only [G, embeddedDepressed]
    rw [(monic_genericDepressed R m).natDegree_map]
    exact natDegree_genericDepressed R m
  have hshift : G.comp (Polynomial.X + Polynomial.C s) = Polynomial.taylor s G :=
    (Polynomial.taylor_apply s G).symm
  refine AddMonoidAlgebra.ext (Finsupp.ext fun k ↦ ?_)
  rw [Polynomial.coeff_map, Polynomial.coeff_freeMonic]
  by_cases h1 : k < m
  · rw [dite_eq_left h1]
    by_cases hlt : k + 2 ≤ m
    · simp [tschirnhausFromDepressed, hlt]
    · have hk : k = m - 1 := by omega
      subst hk
      have hnext := Polynomial.nextCoeff_taylor G s
      have hpos1 : 0 < (Polynomial.taylor s G).natDegree := by
        rw [Polynomial.natDegree_taylor, hG_deg]
        omega
      rw [Polynomial.nextCoeff_of_natDegree_pos hpos1,
        Polynomial.nextCoeff_of_natDegree_pos (by rw [hG_deg]; omega),
        Polynomial.natDegree_taylor, hG_deg, hG_mon.leadingCoeff, mul_one] at hnext
      have hGcoeff : G.coeff (m - 1) = 0 := by
        dsimp only [G, embeddedDepressed]
        rw [coeff_map_rename_genericDepressed R hm, dite_eq_right (by omega),
          ite_eq_right (by omega)]
      rw [hGcoeff, zero_add] at hnext
      have hnot : ¬ m - 1 + 2 ≤ m := by omega
      have hX : (tschirnhausFromDepressed R hm hmR).toRingHom (X ⟨m - 1, h1⟩) =
          X ⟨m - 1, h1⟩ := by
        simp [tschirnhausFromDepressed, hnot]
      rw [hshift, hnext, hX]
      calc
        (X ⟨m - 1, h1⟩ : MvPolynomial (Fin m) R)
          = ((m : MvPolynomial (Fin m) R) * C ((hmR.unit⁻¹ : Rˣ) : R)) *
              X ⟨m - 1, h1⟩ := by rw [natCast_mul_C_inv_eq_one hmR, one_mul]
        _ = (m : MvPolynomial (Fin m) R) * s := by
              dsimp [s, tschirnhausShift]
              ring
  · rw [dite_eq_right h1]
    by_cases h2 : k = m
    · have hlead : (Polynomial.taylor s G).coeff m = 1 := by
        have h := Polynomial.leadingCoeff_taylor s G
        rw [Polynomial.leadingCoeff, Polynomial.natDegree_taylor, hG_deg, hG_mon.leadingCoeff] at h
        exact h
      rw [h2, ite_eq_left rfl, map_one, hshift, hlead]
    · rw [ite_eq_right h2, map_zero, hshift, Polynomial.coeff_eq_zero_of_natDegree_lt]
      rw [Polynomial.natDegree_taylor, hG_deg]
      omega

/-- **The Tschirnhaus automorphism.** Whenever `m ≥ 2` is invertible in `R`, shifting the root
coordinate by `a₁ / m` defines an `R`-algebra automorphism of `MvPolynomial (Fin m) R` taking the
generic monic polynomial `Polynomial.freeMonic R m` to the shifted depressed polynomial
`G(X + a₁ / m)` and keeping the subleading coefficient variable `X ⟨m - 1, _⟩` fixed. -/
noncomputable def tschirnhausEquiv (R : Type*) [CommRing R] {m : ℕ} (hm : 2 ≤ m)
    (hmR : IsUnit (m : R)) : MvPolynomial (Fin m) R ≃ₐ[R] MvPolynomial (Fin m) R := by
  let φ := tschirnhausToDepressed R hm hmR
  let ψ := tschirnhausFromDepressed R hm hmR
  let s := tschirnhausShift R hm hmR
  have hnot : ¬ m - 1 + 2 ≤ m := by omega
  have hφs : φ s = s := by simp [φ, s, tschirnhausToDepressed, tschirnhausShift, hnot]
  have hψs : ψ s = s := by simp [ψ, s, tschirnhausFromDepressed, tschirnhausShift, hnot]
  have hφψ : φ.comp ψ = AlgHom.id R _ := by
    have hpoly :
        (Polynomial.freeMonic R m).map (φ.comp ψ).toRingHom = Polynomial.freeMonic R m := by
      have hring : (φ.comp ψ).toRingHom = φ.toRingHom.comp ψ.toRingHom := rfl
      rw [hring, ← Polynomial.map_map, map_freeMonic_tschirnhausFromDepressed R hm hmR,
        Polynomial.map_comp, map_embeddedDepressed_tschirnhausToDepressed R hm hmR,
        Polynomial.map_add, Polynomial.map_X, Polynomial.map_C]
      have hφs' : φ.toRingHom s = s := hφs
      rw [hφs', Polynomial.comp_assoc, Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp,
        add_sub_cancel_right, Polynomial.comp_X]
    refine algHom_ext fun i ↦ ?_
    have hi := congrArg (fun p ↦ p.coeff i) hpoly
    rw [Polynomial.coeff_map, Polynomial.coeff_freeMonic, dite_eq_left i.isLt] at hi
    exact hi
  have hψφ : ψ.comp φ = AlgHom.id R _ := by
    have hpoly : (embeddedDepressed R hm).map (ψ.comp φ).toRingHom = embeddedDepressed R hm := by
      have hring : (ψ.comp φ).toRingHom = ψ.toRingHom.comp φ.toRingHom := rfl
      rw [hring, ← Polynomial.map_map, map_embeddedDepressed_tschirnhausToDepressed R hm hmR,
        Polynomial.map_comp, map_freeMonic_tschirnhausFromDepressed R hm hmR,
        Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
      have hψs' : ψ.toRingHom s = s := hψs
      rw [hψs', Polynomial.comp_assoc, Polynomial.add_comp, Polynomial.X_comp, Polynomial.C_comp,
        sub_add_cancel, Polynomial.comp_X]
    refine algHom_ext fun i ↦ ?_
    by_cases hlt : (i : ℕ) + 2 ≤ m
    · have hi := congrArg (fun p ↦ p.coeff i) hpoly
      rw [Polynomial.coeff_map, embeddedDepressed, coeff_map_rename_genericDepressed R hm,
        dite_eq_left hlt] at hi
      exact hi
    · have hi : i = ⟨m - 1, by omega⟩ := Fin.ext (by dsimp; omega)
      rw [hi]
      simp [φ, ψ, tschirnhausToDepressed, tschirnhausFromDepressed, hnot]
  exact AlgEquiv.ofAlgHom ψ φ hψφ hφψ

/-- The Tschirnhaus automorphism fixes the subleading coefficient variable `X ⟨m - 1, _⟩`. -/
@[simp]
theorem tschirnhausEquiv_X_subleading (R : Type*) [CommRing R] {m : ℕ} (hm : 2 ≤ m)
    (hmR : IsUnit (m : R)) :
    tschirnhausEquiv R hm hmR (X ⟨m - 1, by omega⟩) = X ⟨m - 1, by omega⟩ := by
  have hnot : ¬ m - 1 + 2 ≤ m := by omega
  simp [tschirnhausEquiv, tschirnhausFromDepressed, hnot]

/-- Applying `tschirnhausEquiv` coefficientwise carries `Polynomial.freeMonic R m` to the shifted
embedded depressed polynomial. -/
theorem map_freeMonic_tschirnhausEquiv (R : Type*) [CommRing R] {m : ℕ} (hm : 2 ≤ m)
    (hmR : IsUnit (m : R)) :
    (Polynomial.freeMonic R m).map (tschirnhausEquiv R hm hmR).toAlgHom.toRingHom =
      ((genericDepressed R m).map (rename (depressedEmb m hm)).toRingHom).comp
        (Polynomial.X + Polynomial.C (C ((hmR.unit⁻¹ : Rˣ) : R) * X ⟨m - 1, by omega⟩)) :=
  map_freeMonic_tschirnhausFromDepressed R hm hmR

/-- The Tschirnhaus automorphism maps `(Polynomial.freeMonic R m).discr` to the embedded
`depressedDiscr R m`. -/
theorem tschirnhausEquiv_discr_freeMonic (R : Type*) [CommRing R] {m : ℕ} (hm : 2 ≤ m)
    (hmR : IsUnit (m : R)) :
    tschirnhausEquiv R hm hmR (Polynomial.freeMonic R m).discr =
      rename (depressedEmb m hm) (depressedDiscr R m) := by
  have h1 := (Polynomial.monic_freeMonic R m).discr_map
    (tschirnhausEquiv R hm hmR).toAlgHom.toRingHom
  have h2 := (monic_genericDepressed R m).discr_map (rename (depressedEmb m hm)).toRingHom
  rw [map_freeMonic_tschirnhausEquiv, Polynomial.discr_comp_X_add_C] at h1
  exact h1.symm.trans h2

/-- **Primality of the generic depressed discriminant.** Over any unique factorization domain in
which `2 ≠ 0` and `m` is invertible, `depressedDiscr R m` is prime for every `m ≥ 2`. -/
theorem depressedDiscr_prime {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (h2 : (2 : R) ≠ 0) {m : ℕ} (hmR : IsUnit (m : R)) (hm : 2 ≤ m) :
    Prime (depressedDiscr R m) := by
  rw [← prime_rename_iff_of_injective (depressedEmb_injective m hm),
    ← tschirnhausEquiv_discr_freeMonic R hm hmR]
  exact (MulEquiv.prime_iff (tschirnhausEquiv R hm hmR).toMulEquiv).mpr
    (prime_discr_freeMonic h2 hm)

/-- Over a field of characteristic zero, the generic depressed discriminant is prime for every
`m ≥ 2`. -/
theorem depressedDiscr_prime_of_charZero (K : Type*) [Field K] [CharZero K] (m : ℕ) (hm : 2 ≤ m) :
    Prime (depressedDiscr K m) :=
  depressedDiscr_prime (two_ne_zero) (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (by omega))) hm

/-! ### Graded localization consequences and low-degree formulas -/

/-- Inverting `depressedDiscr R m` in `MvPolynomial (Fin (m - 1)) R` with `depressedWeight m`
yields homogeneous unit degrees `m * (m - 1) ℤ`. -/
theorem homogeneousUnitDegrees_away_depressedDiscr {R : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] (h2 : (2 : R) ≠ 0) {m : ℕ} (hmR : IsUnit (m : R))
    (hm : 2 ≤ m) :
    homogeneousUnitDegrees
        (awayGrading (weightedHomogeneousSubmodule R (depressedWeight m)) (depressedDiscr_mem R m))
      = AddSubgroup.zmultiples ((m : ℤ) * (m - 1)) :=
  homogeneousUnitDegrees_away_prime (depressedWeight m) (depressedDiscr_mem R m)
    (depressedDiscr_prime h2 hmR hm)

/-- Inverting `depressedDiscr R m` in `MvPolynomial (Fin (m - 1)) R` with `depressedWeight m`
yields shift class group `ZMod (m * (m - 1))`. -/
noncomputable def shiftClassGroupAwayDepressedDiscrEquiv {R : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] (h2 : (2 : R) ≠ 0) {m : ℕ} (hmR : IsUnit (m : R))
    (hm : 2 ≤ m) :
    ShiftClassGroup
        (awayGrading (weightedHomogeneousSubmodule R (depressedWeight m)) (depressedDiscr_mem R m))
      ≃+ ZMod (m * (m - 1)) :=
  (shiftClassGroupAwayPrimeEquiv (depressedWeight m) (depressedDiscr_mem R m)
    (depressedDiscr_prime h2 hmR hm)).trans (ZMod.ringEquivCongr (by
      have h : ((m : ℤ) * (m - 1)) = ((m * (m - 1) : ℕ) : ℤ) := by
        rw [Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_one]
      rw [h, Int.natAbs_natCast])).toAddEquiv

/-- The identification of the shift class group after inverting `depressedDiscr R m` with
`ZMod (m * (m - 1))` sends the class of `d` to `d mod m * (m - 1)`. -/
@[simp]
theorem shiftClassGroupAwayDepressedDiscrEquiv_mk {R : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] (h2 : (2 : R) ≠ 0) {m : ℕ} (hmR : IsUnit (m : R))
    (hm : 2 ≤ m) (d : ℤ) :
    shiftClassGroupAwayDepressedDiscrEquiv h2 hmR hm d = d := by
  simp [shiftClassGroupAwayDepressedDiscrEquiv]

/-- In degree `2`, `depressedDiscr R 2 = -4 * X 0`. -/
theorem depressedDiscr_two (R : Type*) [CommRing R] : depressedDiscr R 2 = -4 * X 0 := by
  nontriviality R
  rw [depressedDiscr, Polynomial.discr_of_degree_eq_two (degree_genericDepressed R 2)]
  simp only [coeff_genericDepressed]
  norm_num

/-- In degree `3`, `depressedDiscr R 3 = -4 * X 0 ^ 3 - 27 * X 1 ^ 2`. -/
theorem depressedDiscr_three (R : Type*) [CommRing R] :
    depressedDiscr R 3 = -4 * X 0 ^ 3 - 27 * X 1 ^ 2 := by
  nontriviality R
  rw [depressedDiscr, Polynomial.discr_of_degree_eq_three (degree_genericDepressed R 3)]
  simp only [coeff_genericDepressed]
  norm_num

/-- The Weierstrass cubic discriminant `4 * X 0 ^ 3 + 27 * X 1 ^ 2` has weight `12` when the
variables have weights `4` and `6`. -/
theorem mem_weightedHomogeneousSubmodule_weierstrass (R : Type*) [CommRing R] :
    (4 * X 0 ^ 3 + 27 * X 1 ^ 2 : MvPolynomial (Fin 2) R) ∈
      weightedHomogeneousSubmodule R (![4, 6] : Fin 2 → ℤ) 12 := by
  have h0 : (4 * X 0 ^ 3 : MvPolynomial (Fin 2) R) ∈
      weightedHomogeneousSubmodule R (![4, 6] : Fin 2 → ℤ) 12 := by
    have hx : (X 0 : MvPolynomial (Fin 2) R).IsWeightedHomogeneous (![4, 6] : Fin 2 → ℤ) 4 :=
      isWeightedHomogeneous_X R _ 0
    simpa [← map_ofNat (C (σ := Fin 2) (R := R))] using (hx.pow 3).C_mul (4 : R)
  have h1 : (27 * X 1 ^ 2 : MvPolynomial (Fin 2) R) ∈
      weightedHomogeneousSubmodule R (![4, 6] : Fin 2 → ℤ) 12 := by
    have hx : (X 1 : MvPolynomial (Fin 2) R).IsWeightedHomogeneous (![4, 6] : Fin 2 → ℤ) 6 :=
      isWeightedHomogeneous_X R _ 1
    simpa [← map_ofNat (C (σ := Fin 2) (R := R))] using (hx.pow 2).C_mul (27 : R)
  exact add_mem h0 h1

/-- Over any unique factorization domain in which `2 ≠ 0` and `3` is invertible, the Weierstrass
discriminant `4 * X 0 ^ 3 + 27 * X 1 ^ 2` is prime. -/
theorem prime_four_mul_pow_three_add_twentyseven_mul_sq {R : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] (h2 : (2 : R) ≠ 0) (h3 : IsUnit (3 : R)) :
    Prime (4 * X 0 ^ 3 + 27 * X 1 ^ 2 : MvPolynomial (Fin 2) R) := by
  have h : (4 * X 0 ^ 3 + 27 * X 1 ^ 2 : MvPolynomial (Fin 2) R) = -depressedDiscr R 3 := by
    rw [depressedDiscr_three]
    ring
  rw [h]
  have hassoc : Associated (depressedDiscr R 3) (-depressedDiscr R 3) := ⟨-1, by simp⟩
  exact hassoc.prime_iff.mp
    (depressedDiscr_prime h2 (m := 3) (by norm_num; exact h3) (by norm_num))

/-- Inverting `4 * X 0 ^ 3 + 27 * X 1 ^ 2` in `R[a, b]` with weights `4, 6` (when `2 ≠ 0` and `3`
is invertible in a unique factorization domain `R`) yields shift class group `ZMod 12`. -/
noncomputable def shiftClassGroupAwayWeierstrassEquiv {R : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] (h2 : (2 : R) ≠ 0) (h3 : IsUnit (3 : R)) :
    ShiftClassGroup
        (awayGrading (weightedHomogeneousSubmodule R (![4, 6] : Fin 2 → ℤ))
          (mem_weightedHomogeneousSubmodule_weierstrass R)) ≃+ ZMod 12 :=
  shiftClassGroupAwayPrimeEquiv (![4, 6] : Fin 2 → ℤ)
    (mem_weightedHomogeneousSubmodule_weierstrass R)
    (prime_four_mul_pow_three_add_twentyseven_mul_sq h2 h3)

/-- The identification of the Weierstrass shift class group with `ZMod 12` sends the class of `d`
to `d mod 12`. -/
@[simp]
theorem shiftClassGroupAwayWeierstrassEquiv_mk {R : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] (h2 : (2 : R) ≠ 0) (h3 : IsUnit (3 : R)) (d : ℤ) :
    shiftClassGroupAwayWeierstrassEquiv h2 h3 d = d :=
  shiftClassGroupAwayPrimeEquiv_mk _ _ _ d

end Depressed

end TauCeti
