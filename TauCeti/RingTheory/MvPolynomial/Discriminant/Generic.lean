/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.UniversalFactorizationRing
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Alternant
public import TauCeti.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import TauCeti.RingTheory.MvPolynomial.Prime
import TauCeti.RingTheory.MvPolynomial.Symmetric.Homogeneous
import TauCeti.RingTheory.Polynomial.Resultant.Discriminant
import TauCeti.RingTheory.Polynomial.Resultant.RootCoordinates
import TauCeti.RingTheory.Polynomial.Vieta

/-!
# The generic discriminant

The generic monic polynomial of degree `m`, `Polynomial.freeMonic R m`, has coefficients
`X 0, …, X (m - 1)` of natural weights `m, …, 1` (the coefficient of `X ^ i` has weight `m - i`).
Under the Vieta homomorphism sending `X i` to `(-1) ^ (m - i) * esymm (Fin m) R (m - i)`,
`Polynomial.freeMonic R m` maps to `∏ j : Fin m, (X - C (X j))`, whose discriminant is the square
of the Vandermonde alternant `∏_{i < j} (X j - X i)`. Since the Vieta homomorphism is injective,
this determines both the weighted degree `m * (m - 1)` of the generic discriminant (over any
commutative ring) and its irreducibility and primality (over any integral domain in which
`2 ≠ 0`, for `m ≥ 2`).

## Main definitions

* `TauCeti.freeMonicWeight`: the weight `i ↦ m - i` on the coefficients of `Polynomial.freeMonic`.
* `TauCeti.vietaAlgHom`: the Vieta substitution `X i ↦ (-1) ^ (m - i) * esymm (Fin m) R (m - i)`.

## Main results

* `TauCeti.discr_freeMonic_mem_weightedHomogeneousSubmodule`: `(Polynomial.freeMonic R m).discr`
  has weight `m * (m - 1)`.
* `TauCeti.irreducible_discr_freeMonic` and `TauCeti.prime_discr_freeMonic`: irreducibility and
  primality of `(Polynomial.freeMonic R m).discr` for `m ≥ 2` when `(2 : R) ≠ 0`.
-/

public section

namespace TauCeti

open Finset MvPolynomial

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

private noncomputable def vietaSignRevEquiv (R : Type*) [CommRing R] (m : ℕ) :
    MvPolynomial (Fin m) R ≃ₐ[R] MvPolynomial (Fin m) R :=
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
  AlgEquiv.ofAlgHom f g hfg hgf

private theorem vietaAlgHom_eq_comp (R : Type*) [CommRing R] (m : ℕ) :
    vietaAlgHom R m =
      (symmetricSubalgebra (Fin m) R).val.comp
        ((esymmAlgHom (Fin m) R m).comp (vietaSignRevEquiv R m).toAlgHom) := by
  refine algHom_ext fun i ↦ ?_
  simp [vietaSignRevEquiv, esymmAlgHom_apply]
  congr 2
  omega

/-- The Vieta homomorphism is injective over any commutative ring, since it is the elementary
symmetric substitution precomposed with a signed reversal of variables. -/
theorem vietaAlgHom_injective (R : Type*) [CommRing R] (m : ℕ) :
    Function.Injective (vietaAlgHom R m) := by
  have hcoe : (vietaAlgHom R m : MvPolynomial (Fin m) R → MvPolynomial (Fin m) R) =
      Subtype.val ∘ esymmAlgHom (Fin m) R m ∘ vietaSignRevEquiv R m :=
    congrArg DFunLike.coe (vietaAlgHom_eq_comp R m)
  rw [hcoe]
  exact Subtype.val_injective.comp
    ((esymmAlgHom_fin_injective R le_rfl).comp (vietaSignRevEquiv R m).injective)

/-- Every symmetric polynomial in `MvPolynomial (Fin m) R` lies in the image of
`vietaAlgHom R m`. -/
private theorem exists_vietaAlgHom_eq_of_isSymmetric {R : Type*} [CommRing R] {m : ℕ}
    {q : MvPolynomial (Fin m) R} (hq : ∀ τ : Equiv.Perm (Fin m), rename τ q = q) :
    ∃ g : MvPolynomial (Fin m) R, vietaAlgHom R m g = q := by
  have hmem : q ∈ symmetricSubalgebra (Fin m) R := fun τ ↦ hq τ
  obtain ⟨g₀, hg₀⟩ := (esymmAlgHom_fin_bijective R m).surjective ⟨q, hmem⟩
  refine ⟨(vietaSignRevEquiv R m).symm g₀, ?_⟩
  have hcoe := AlgHom.congr_fun (vietaAlgHom_eq_comp R m) ((vietaSignRevEquiv R m).symm g₀)
  change vietaAlgHom R m ((vietaSignRevEquiv R m).symm g₀) =
    (esymmAlgHom (Fin m) R m ((vietaSignRevEquiv R m) ((vietaSignRevEquiv R m).symm g₀)) :
      MvPolynomial (Fin m) R) at hcoe
  rw [AlgEquiv.apply_symm_apply, hg₀] at hcoe
  exact hcoe

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

private theorem X_dvd_of_aeval_update_zero {σ R : Type*} [CommRing R] [DecidableEq σ] {j : σ}
    {p : MvPolynomial σ R}
    (h : aeval (Function.update (X : σ → MvPolynomial σ R) j 0) p = 0) : X j ∣ p := by
  rw [X_dvd_iff_modMonomial_eq_zero]
  set r : MvPolynomial σ R := p.modMonomial (Finsupp.single j 1)
  have hsum : X j * (p.divMonomial (Finsupp.single j 1)) + r = p :=
    divMonomial_add_modMonomial_single p j
  let φ : MvPolynomial σ R →ₐ[R] MvPolynomial σ R :=
    aeval (Function.update (X : σ → MvPolynomial σ R) j 0)
  have hφ_p : φ p = φ r := by
    have h1 := congrArg φ hsum
    simpa [φ] using h1.symm
  have hφ_r : φ r = r := by
    conv_lhs => rw [r.as_sum, map_sum]
    conv_rhs => rw [r.as_sum]
    refine Finset.sum_congr rfl fun d hd ↦ ?_
    have hd_j : d j = 0 := by
      by_contra hne
      have hle : Finsupp.single j 1 ≤ d :=
        Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hne)
      have hzero : r.coeff d = 0 := coeff_modMonomial_of_le p hle
      exact (mem_support_iff.mp hd) hzero
    rw [aeval_monomial, algebraMap_eq, monomial_eq]
    congr 1
    refine Finset.prod_congr rfl fun k hk ↦ ?_
    have hkj : k ≠ j := fun hkeq ↦ (Finsupp.mem_support_iff.mp hk) (hkeq ▸ hd_j)
    dsimp only
    rw [Function.update_of_ne hkj]
  rw [← hφ_r, ← hφ_p]
  exact h

private theorem X_sub_X_dvd_of_aeval_update {σ R : Type*} [CommRing R] [DecidableEq σ]
    {i j : σ} (hij : i ≠ j) {p : MvPolynomial σ R}
    (h : aeval (Function.update (X : σ → MvPolynomial σ R) j (X i)) p = 0) :
    X j - X i ∣ p := by
  let e := shearXEquiv R hij
  have hcomp : (aeval (Function.update (X : σ → MvPolynomial σ R) j 0)).comp e.toAlgHom =
      aeval (Function.update (X : σ → MvPolynomial σ R) j (X i)) := by
    ext k
    rcases eq_or_ne k j with rfl | hkj
    · simp [e, hij]
    · simp [e, hkj]
  have he0 : aeval (Function.update (X : σ → MvPolynomial σ R) j 0) (e p) = 0 := by
    simpa [AlgHom.comp_apply] using (AlgHom.congr_fun hcomp p).trans h
  have hdvd : X j ∣ e p := X_dvd_of_aeval_update_zero he0
  have hdvd' := map_dvd e.symm.toRingHom hdvd
  simpa [e] using hdvd'

private theorem prod_X_sub_X_dvd_of_forall_dvd {R : Type*} [CommRing R] [IsDomain R] {m : ℕ}
    (s : Finset (Fin m × Fin m)) (hs : ∀ p ∈ s, p.1 < p.2) {h : MvPolynomial (Fin m) R}
    (hdvd : ∀ p ∈ s, (X p.2 - X p.1 : MvPolynomial (Fin m) R) ∣ h) :
    (∏ p ∈ s, (X p.2 - X p.1 : MvPolynomial (Fin m) R)) ∣ h := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s has ih =>
    rw [Finset.prod_insert has]
    have ha_lt : a.1 < a.2 := hs a (Finset.mem_insert_self a s)
    have ha_prime : Prime (X a.2 - X a.1 : MvPolynomial (Fin m) R) := prime_X_sub_X ha_lt.ne
    obtain ⟨q, hq⟩ := ih (fun p hp ↦ hs p (Finset.mem_insert_of_mem hp))
      (fun p hp ↦ hdvd p (Finset.mem_insert_of_mem hp))
    have ha_dvd : (X a.2 - X a.1 : MvPolynomial (Fin m) R) ∣
        (∏ p ∈ s, (X p.2 - X p.1)) * q := hq ▸ hdvd a (Finset.mem_insert_self a s)
    rcases ha_prime.dvd_or_dvd ha_dvd with hprod | haq
    · obtain ⟨p, hp, hap⟩ := (ha_prime.dvd_finsetProd_iff _).mp hprod
      have hp_lt : p.1 < p.2 := hs p (Finset.mem_insert_of_mem hp)
      have hpa : p ≠ a := fun hpeq ↦ has (hpeq ▸ hp)
      have hna : ¬ Associated (X a.2 - X a.1 : MvPolynomial (Fin m) R) (X p.2 - X p.1) :=
        not_associated_X_sub_X
          (not_and_or.mp fun h ↦ hpa (Prod.ext h.1 h.2))
          (not_and_or.mp fun h ↦ lt_asymm ha_lt (h.2 ▸ h.1 ▸ hp_lt))
          hp_lt.ne
      exact (hna (ha_prime.associated_of_dvd (prime_X_sub_X hp_lt.ne) hap)).elim
    · obtain ⟨q', rfl⟩ := haq
      exact ⟨q', by rw [hq]; ring⟩

private theorem discr_freeMonic_dvd_of_X_sub_X_dvd_vieta {R : Type*} [CommRing R] [IsDomain R]
    (h2 : (2 : R) ≠ 0) {m : ℕ} (hm : 2 ≤ m) {f : MvPolynomial (Fin m) R}
    (hdvd : (X ⟨1, by omega⟩ - X ⟨0, by omega⟩ : MvPolynomial (Fin m) R) ∣ vietaAlgHom R m f) :
    (Polynomial.freeMonic R m).discr ∣ f := by
  let pairs : Finset (Fin m × Fin m) := univ.filter fun p ↦ p.1 < p.2
  have hpairs_lt : ∀ p ∈ pairs, p.1 < p.2 := fun p hp ↦ (mem_filter.mp hp).2
  have halt : alternant (Fin m) R (fun j ↦ (j : ℕ)) = ∏ p ∈ pairs, (X p.2 - X p.1) :=
    alternant_fin_val_eq_prod_pairs R m
  have halt_ne : alternant (Fin m) R (fun j ↦ (j : ℕ)) ≠ 0 :=
    alternant_ne_zero_of_injective Fin.val_injective
  have hdvd_pairs : ∀ p ∈ pairs, (X p.2 - X p.1 : MvPolynomial (Fin m) R) ∣ vietaAlgHom R m f := by
    intro p hp
    obtain ⟨τ, hτ1, hτ2⟩ := exists_perm_map_pair (p := (⟨0, by omega⟩, ⟨1, by omega⟩))
      (by simp) (hpairs_lt p hp)
    have h1 := map_dvd (rename (R := R) τ) hdvd
    rwa [rename_vietaAlgHom, map_sub, rename_X, rename_X, hτ1, hτ2] at h1
  obtain ⟨h, hh⟩ := halt ▸ prod_X_sub_X_dvd_of_forall_dvd pairs hpairs_lt hdvd_pairs
  have hh_pairs : ∀ p ∈ pairs, (X p.2 - X p.1 : MvPolynomial (Fin m) R) ∣ h := by
    intro p hp
    have hp_lt : p.1 < p.2 := hpairs_lt p hp
    let τ : Equiv.Perm (Fin m) := Equiv.swap p.1 p.2
    have hsym : rename (R := R) τ (vietaAlgHom R m f) = vietaAlgHom R m f :=
      rename_vietaAlgHom τ f
    rw [hh, map_mul, rename_alternant, Equiv.Perm.sign_swap hp_lt.ne, Units.smul_def,
      Units.val_neg, Units.val_one, neg_one_zsmul, neg_mul] at hsym
    have hneg : rename (R := R) τ h = -h := by
      have hmul : alternant (Fin m) R (fun j ↦ (j : ℕ)) * (rename (R := R) τ h) =
          alternant (Fin m) R (fun j ↦ (j : ℕ)) * (-h) := by
        rw [mul_neg]
        exact neg_eq_iff_eq_neg.mp hsym
      exact mul_left_cancel₀ halt_ne hmul
    let φ : MvPolynomial (Fin m) R →ₐ[R] MvPolynomial (Fin m) R :=
      aeval (Function.update (X : Fin m → MvPolynomial (Fin m) R) p.2 (X p.1))
    have hφτ : φ.comp (rename (R := R) τ) = φ := by
      refine algHom_ext fun k ↦ ?_
      simp only [AlgHom.comp_apply, rename_X, φ, τ]
      rcases eq_or_ne k p.1 with rfl | hk1
      · simp [Function.update_of_ne hp_lt.ne]
      · rcases eq_or_ne k p.2 with rfl | hk2
        · simp [Equiv.swap_apply_right, Function.update_of_ne hp_lt.ne]
        · simp [Equiv.swap_apply_of_ne_of_ne hk1 hk2, Function.update_of_ne hk2]
    have hφh : φ h = -φ h := by
      have h1 := congrArg φ hneg
      rw [map_neg] at h1
      simpa [AlgHom.comp_apply] using (AlgHom.congr_fun hφτ h).symm.trans h1
    have h2φ : C (2 : R) * φ h = 0 := by
      have hsum : φ h + φ h = 0 := by linear_combination hφh
      calc C (2 : R) * φ h = φ h + φ h := by rw [map_ofNat]; ring
      _ = 0 := hsum
    have hC2 : C (2 : R) ≠ (0 : MvPolynomial (Fin m) R) := by
      simpa using (C_injective (Fin m) R).ne h2
    have hφ0 : φ h = 0 := (mul_eq_zero.mp h2φ).resolve_left hC2
    exact X_sub_X_dvd_of_aeval_update hp_lt.ne hφ0
  obtain ⟨q, hq⟩ := halt ▸ prod_X_sub_X_dvd_of_forall_dvd pairs hpairs_lt hh_pairs
  have hvf : vietaAlgHom R m f = vietaAlgHom R m (Polynomial.freeMonic R m).discr * q := by
    rw [vietaAlgHom_discr_freeMonic, pow_two, mul_assoc, ← hq, ← hh]
  have hdiscr_ne : vietaAlgHom R m (Polynomial.freeMonic R m).discr ≠ 0 := by
    rw [vietaAlgHom_discr_freeMonic]
    exact pow_ne_zero 2 halt_ne
  have hq_sym : ∀ τ : Equiv.Perm (Fin m), rename τ q = q := fun τ ↦ by
    have h1 := congrArg (rename (R := R) τ) hvf
    rw [rename_vietaAlgHom, map_mul, rename_vietaAlgHom, hvf] at h1
    exact mul_left_cancel₀ hdiscr_ne h1.symm
  obtain ⟨g, hg⟩ := exists_vietaAlgHom_eq_of_isSymmetric hq_sym
  rw [← hg, ← map_mul] at hvf
  exact ⟨g, vietaAlgHom_injective R m hvf⟩

/-- **Primality of the generic discriminant.** Over any integral domain in which `2 ≠ 0`,
the discriminant of `Polynomial.freeMonic R m` is prime for every `m ≥ 2`. -/
theorem prime_discr_freeMonic {R : Type*} [CommRing R] [IsDomain R] (h2 : (2 : R) ≠ 0)
    {m : ℕ} (hm : 2 ≤ m) : Prime (Polynomial.freeMonic R m).discr := by
  let i₀ : Fin m := ⟨0, by omega⟩
  let i₁ : Fin m := ⟨1, by omega⟩
  have halt_ne : alternant (Fin m) R (fun j ↦ (j : ℕ)) ≠ 0 :=
    alternant_ne_zero_of_injective Fin.val_injective
  have hdiscr_ne : (Polynomial.freeMonic R m).discr ≠ 0 := fun h ↦ by
    have h0 := congrArg (vietaAlgHom R m) h
    rw [map_zero, vietaAlgHom_discr_freeMonic] at h0
    exact pow_ne_zero 2 halt_ne h0
  refine ⟨hdiscr_ne, ?_, fun f g hfg ↦ ?_⟩
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
  · have hp₀ : Prime (X i₁ - X i₀ : MvPolynomial (Fin m) R) := prime_X_sub_X (by simp [i₀, i₁])
    have hp₀_dvd_alt : (X i₁ - X i₀ : MvPolynomial (Fin m) R) ∣
        alternant (Fin m) R (fun j ↦ (j : ℕ)) := by
      rw [alternant_fin_val_eq_vandermonde]
      have hi01 : i₀ < i₁ := by simp [i₀, i₁]
      have h1 : (X i₁ - X i₀ : MvPolynomial (Fin m) R) ∣
          ∏ j ∈ Finset.Ioi i₀, (X j - X i₀) :=
        Finset.dvd_prod_of_mem (fun j ↦ (X j - X i₀ : MvPolynomial (Fin m) R))
          (Finset.mem_Ioi.mpr hi01)
      exact h1.trans (Finset.dvd_prod_of_mem
        (fun i : Fin m ↦ ∏ j ∈ Finset.Ioi i, (X j - X i : MvPolynomial (Fin m) R))
        (Finset.mem_univ i₀))
    have hp₀_dvd : (X i₁ - X i₀ : MvPolynomial (Fin m) R) ∣
        vietaAlgHom R m f * vietaAlgHom R m g := by
      have h1 := map_dvd (vietaAlgHom R m).toRingHom hfg
      rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, vietaAlgHom_discr_freeMonic, map_mul] at h1
      exact ((hp₀_dvd_alt.trans (dvd_pow_self _ two_ne_zero))).trans h1
    rcases hp₀.dvd_or_dvd hp₀_dvd with hf | hg
    · exact Or.inl (discr_freeMonic_dvd_of_X_sub_X_dvd_vieta h2 hm hf)
    · exact Or.inr (discr_freeMonic_dvd_of_X_sub_X_dvd_vieta h2 hm hg)

/-- **Irreducibility of the generic discriminant.** Over any integral domain in which `2 ≠ 0`,
the discriminant of `Polynomial.freeMonic R m` is irreducible for every `m ≥ 2`. -/
theorem irreducible_discr_freeMonic {R : Type*} [CommRing R] [IsDomain R] (h2 : (2 : R) ≠ 0)
    {m : ℕ} (hm : 2 ≤ m) : Irreducible (Polynomial.freeMonic R m).discr :=
  (prime_discr_freeMonic h2 hm).irreducible

end FreeMonic

end TauCeti
