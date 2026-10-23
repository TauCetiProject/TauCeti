/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DividedPowerAlgebra.UniversalLaw
public import TauCeti.RingTheory.PolynomialLaw.Coeff
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Multiset.Fintype
import TauCeti.Algebra.MvPolynomial.Monomial

/-!
# Roby representability

Composition with the universal law `γ_d` sends a linear map `Γ^d_R(M) → N` to a homogeneous
polynomial law of degree `d`. Roby's theorem says that this is a linear equivalence: every
homogeneous law of degree `d` from `M` to `N` is represented by a unique linear map on the
degree-`d` piece of the divided power algebra. No flatness or projectivity of `M` is assumed.

Uniqueness requires scalar-extended values, rather than just ground values. Evaluating at
`∑ X_j ⊗ m_j` and extracting a mixed coefficient recovers the value of the linear map on
`∏ dp R (k j) (m j)`. These products span the homogeneous piece, even for modules with torsion
and without inverting factorials.

The construction uses `DividedPowerAlgebra.gamma` and its coefficient formula. The underlying
divided power algebra and polynomial laws are the Mathlib formalizations by Antoine
Chambert-Loir and María Inés de Frutos-Fernández.

## Main declarations

* `DividedPowerAlgebra.homogeneousLawMap`: the linear comparison to homogeneous laws.
* `DividedPowerAlgebra.lid_rTensor_lcoeff_homogeneousLawMap`: recovery by mixed coefficients.
* `DividedPowerAlgebra.homogeneousLawMap_injective`: uniqueness of a representing linear map.
* `DividedPowerAlgebra.homogeneousLawMap_surjective`: existence of a representing linear map.
* `DividedPowerAlgebra.homogeneousLawEquiv`: Roby's theorem, the linear equivalence between
  linear maps `Γ^d_R(M) → N` and homogeneous laws `M → N` of degree `d`.
* `DividedPowerAlgebra.homogeneousLawEquiv_symm_apply_prod_dp`: the linear map representing `f`
  sends `∏ⱼ dp R kⱼ mⱼ` to the coefficient of `∏ⱼ Tⱼ ^ kⱼ` in `f (∑ⱼ Tⱼ ⊗ mⱼ)`.
* `DividedPowerAlgebra.homogeneousLawMap_comp` and
  `DividedPowerAlgebra.homogeneousLawMap_comp_mapHomogeneousSubmodule`: naturality in both modules.

## Implementation notes

For existence, a law `f` determines a linear map on the polynomial ring in the variables
`X (n, m)`, sending a monomial `∏ᵢ X (nᵢ, mᵢ)` to the coefficient of `∏ᵢ Tᵢ ^ nᵢ` in
`f (∑ᵢ Tᵢ ⊗ mᵢ)`. Comparing coefficients along substitutions of the variables `Tᵢ` shows that this
map respects the defining relations of `Γ_R(M)`, even after multiplication by any monomial, so it
descends to `Γ_R(M)`. Its restriction to the degree-`d` piece represents `f` when `f` is
homogeneous of degree `d`, since both laws then have the same coefficients.

## References

* [N. Roby, *Lois polynômes et lois formelles en théorie des modules* (1963),
  Théorème IV.1][Roby-1963]
-/

public section

noncomputable section

universe u

open TensorProduct

namespace DividedPowerAlgebra

variable {R : Type u} [CommSemiring R]
variable {M N P : Type*} [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module R N] [AddCommMonoid P] [Module R P]

variable (R M N) in
/-- Composition with the universal degree-`d` law, as a linear map into homogeneous laws.
Injectivity is `homogeneousLawMap_injective`; surjectivity is not asserted here. -/
def homogeneousLawMap (d : ℕ) :
    (homogeneousSubmodule (R := R) (M := M) d →ₗ[R] N) →ₗ[R]
      PolynomialLaw.homogeneousSubmodule R M N d where
  toFun f := ⟨f.toPolynomialLaw.comp (gamma R M d), by
    simpa using f.isHomogeneousOfDegree_toPolynomialLaw.comp
      (isHomogeneousOfDegree_gamma (R := R) (M := M) d)⟩
  map_add' f g := by
    apply Subtype.ext
    ext S _ _ x
    simp
  map_smul' r f := by
    apply Subtype.ext
    ext S _ _ x
    simp

/-- The law associated with `f` is its linear polynomial law composed with `γ_d`. -/
@[simp]
theorem coe_homogeneousLawMap_apply (d : ℕ)
    (f : homogeneousSubmodule (R := R) (M := M) d →ₗ[R] N) :
    (homogeneousLawMap R M N d f : M →ₚₗ[R] N) = f.toPolynomialLaw.comp (gamma R M d) :=
  (rfl)

/-- At any scalar algebra, the comparison is the base change of `f` applied to `γ_d`. -/
theorem homogeneousLawMap_toFun (d : ℕ)
    (f : homogeneousSubmodule (R := R) (M := M) d →ₗ[R] N)
    (S : Type*) [CommSemiring S] [Algebra R S] (x : S ⊗[R] M) :
    (homogeneousLawMap R M N d f : M →ₚₗ[R] N).toFun S x =
      f.baseChange S ((gamma R M d).toFun S x) := by
  simp

/-- The ground value of the associated law is `f` evaluated on the divided-power generator. -/
@[simp]
theorem ground_toPolynomialLaw_comp_gamma_apply (d : ℕ)
    (f : homogeneousSubmodule (R := R) (M := M) d →ₗ[R] N) (m : M) :
    (f.toPolynomialLaw.comp (gamma R M d)).ground m =
      f ⟨dp R d m, dp_mem_homogeneousSubmodule d m⟩ := by
  simp [PolynomialLaw.ground_apply, PolynomialLaw.toFun'_eq_toFun, gamma_toFun_tmul]

open MvPolynomial in
/-- Mixed coefficients of the associated law recover `f` on products of divided powers.
The hypothesis fixes the total degree of the monomial, with no factorial factors. -/
theorem lid_rTensor_lcoeff_homogeneousLawMap (d : ℕ)
    (f : homogeneousSubmodule (R := R) (M := M) d →ₗ[R] N)
    {ι : Type*} [Fintype ι] (m : ι → M) (k : ι →₀ ℕ) (hk : ∑ j, k j = d) :
    TensorProduct.lid R N ((lcoeff R k).rTensor N
      ((homogeneousLawMap R M N d f : M →ₚₗ[R] N).toFun (MvPolynomial ι R)
        (∑ j, X j ⊗ₜ[R] m j))) =
      f ⟨∏ j, dp R (k j) (m j), prod_dp_mem_homogeneousSubmodule_of_sum_eq m k hk⟩ := by
  have hgamma : TensorProduct.lid R _ ((lcoeff R k).rTensor _
      ((gamma R M d).toFun (MvPolynomial ι R) (∑ j, X j ⊗ₜ[R] m j))) =
      ⟨∏ j, dp R (k j) (m j), prod_dp_mem_homogeneousSubmodule_of_sum_eq m k hk⟩ := by
    apply Subtype.ext
    simpa only [hk, ite_true] using
      coe_lid_rTensor_lcoeff_gamma_toFun_sum_X_tmul (R := R) d m k
  rw [homogeneousLawMap_toFun, ← hgamma]
  generalize (gamma R M d).toFun (MvPolynomial ι R) (∑ j, X j ⊗ₜ[R] m j) = z
  induction z using TensorProduct.inductionOn with
  | tmul s y => simp
  | add x y hx hy => simp_all

/-- Composition with `γ_d` determines a linear map on the entire homogeneous piece.
Ground values alone need not determine it; the proof uses mixed coefficients over polynomial
scalar algebras. -/
theorem homogeneousLawMap_injective (d : ℕ) :
    Function.Injective (homogeneousLawMap R M N d) := by
  intro f g hfg
  have hprod {ι : Type} [Fintype ι] (m : ι → M) (k : ι →₀ ℕ)
      (hk : ∑ j, k j = d) :
      f ⟨∏ j, dp R (k j) (m j), prod_dp_mem_homogeneousSubmodule_of_sum_eq m k hk⟩ =
      g ⟨∏ j, dp R (k j) (m j), prod_dp_mem_homogeneousSubmodule_of_sum_eq m k hk⟩ := by
    rw [← lid_rTensor_lcoeff_homogeneousLawMap d f m k hk,
      ← lid_rTensor_lcoeff_homogeneousLawMap d g m k hk, hfg]
  apply homogeneousSubmodule_ext
  intro l hl
  let k : Fin l.length →₀ ℕ := Finsupp.equivFunOnFinite.symm fun j ↦ l[j.1].1
  have hk : ∑ j, k j = d := by
    simpa [k] using hl
  have hp := Fin.prod_univ_fun_getElem l (fun nm : ℕ × M ↦ dp R nm.1 nm.2)
  simpa only [k, Finsupp.coe_equivFunOnFinite_symm, hp] using
    hprod (fun j : Fin l.length ↦ l[j.1].2) k hk

/-- Postcomposition of the representing linear map agrees with postcomposition of its law. -/
theorem homogeneousLawMap_comp (d : ℕ)
    (f : homogeneousSubmodule (R := R) (M := M) d →ₗ[R] N) (g : N →ₗ[R] P) :
    (homogeneousLawMap R M P d (g.comp f) : M →ₚₗ[R] P) =
      g.toPolynomialLaw.comp (homogeneousLawMap R M N d f) := by
  simp [PolynomialLaw.comp_assoc]

/-- Precomposition on homogeneous pieces agrees with precomposition of polynomial laws. -/
theorem homogeneousLawMap_comp_mapHomogeneousSubmodule (d : ℕ) (f : M →ₗ[R] N)
    (g : homogeneousSubmodule (R := R) (M := N) d →ₗ[R] P) :
    (homogeneousLawMap R M P d (g.comp (mapHomogeneousSubmodule f d)) : M →ₚₗ[R] P) =
      (homogeneousLawMap R N P d g : N →ₚₗ[R] P).comp f.toPolynomialLaw := by
  simp only [coe_homogeneousLawMap_apply, LinearMap.toPolynomialLaw_comp,
    ← PolynomialLaw.comp_assoc, gamma_comp_toPolynomialLaw]

section Existence

open MvPolynomial PolynomialLaw

variable (f : M →ₚₗ[R] N)

/-- The coefficient of `f` attached to a finite family `p` of pairs `(nᵢ, mᵢ)`: the coefficient
of `∏ᵢ Xᵢ ^ nᵢ` in `f (∑ᵢ Xᵢ ⊗ mᵢ)`. -/
private def famCoeff {ι : Type*} [Fintype ι] (p : ι → ℕ × M) : N :=
  coeff R N (fun i ↦ (p i).2) f (Finsupp.equivFunOnFinite.symm fun i ↦ (p i).1)

/-- Coefficients are invariant under reindexing the family. -/
private theorem famCoeff_comp_equiv {ι κ : Type*} [Fintype ι] [Fintype κ] (e : κ ≃ ι)
    (p : ι → ℕ × M) : famCoeff f (p ∘ e) = famCoeff f p := by
  classical
  symm
  rw [famCoeff, coeff_eq_sum_of_sum_tmul_eq f (fun k ↦ (p (e k)).2) (fun k ↦ X (e k))
    (fun i ↦ (p i).2) (e.sum_comp fun i ↦ X i ⊗ₜ[R] (p i).2)]
  have h (l : κ →₀ ℕ) : (∏ k, (X (e k) : MvPolynomial ι R) ^ l k).coeff
      (Finsupp.equivFunOnFinite.symm fun i ↦ (p i).1) =
      if l = Finsupp.equivFunOnFinite.symm fun k ↦ (p (e k)).1 then 1 else 0 := by
    rw [Fintype.prod_equiv e _ (fun i ↦ (X i : MvPolynomial ι R) ^ l (e.symm i)) (by simp),
      coeff_prod_univ_X_pow]
    congr 1
    simp only [Finsupp.coe_equivFunOnFinite_symm, Finsupp.ext_iff, eq_iff_iff]
    exact ⟨fun h k ↦ by simpa using h (e k), fun h i ↦ by simpa using h (e.symm i)⟩
  simp only [h, ite_smul, _root_.one_smul, _root_.zero_smul, Finsupp.sum_ite_self_eq']
  simp only [famCoeff, Function.comp_apply]

/-- A pair with exponent zero does not contribute to a coefficient. -/
private theorem famCoeff_option_zero {ι : Type*} [Fintype ι] (a : M) (p : ι → ℕ × M) :
    famCoeff f (Option.elim' (0, a) p) = famCoeff f p := by
  classical
  symm
  rw [famCoeff, coeff_eq_sum_of_sum_tmul_eq f (fun o ↦ (Option.elim' (0, a) p o).2)
    (Option.elim' 0 X) (fun i ↦ (p i).2) (by simp [Fintype.sum_option])]
  have h (l : Option ι →₀ ℕ) :
      (∏ o, (Option.elim' 0 X o : MvPolynomial ι R) ^ l o).coeff
        (Finsupp.equivFunOnFinite.symm fun i ↦ (p i).1) =
      if l = Finsupp.equivFunOnFinite.symm fun o ↦ (Option.elim' (0, a) p o).1 then 1 else 0 := by
    rw [Fintype.prod_option]
    simp only [Option.elim'_none, Option.elim'_some]
    rcases Nat.eq_zero_or_pos (l none) with h0 | h0
    · rw [h0, pow_zero, one_mul, coeff_prod_univ_X_pow]
      congr 1
      simp [Finsupp.ext_iff, Option.forall, h0]
    · have hl : l ≠ Finsupp.equivFunOnFinite.symm fun o ↦ (Option.elim' (0, a) p o).1 := by
        rintro rfl
        simp at h0
      simp [zero_pow h0.ne', hl]
  simp only [h, ite_smul, _root_.one_smul, _root_.zero_smul, Finsupp.sum_ite_self_eq']
  rw [famCoeff]

/-- Scaling the vector of a pair by `r` scales the coefficient by `r ^ n`. -/
private theorem famCoeff_option_smul {ι : Type*} [Fintype ι] (n : ℕ) (r : R) (a : M)
    (p : ι → ℕ × M) :
    famCoeff f (Option.elim' (n, r • a) p) = r ^ n • famCoeff f (Option.elim' (n, a) p) := by
  classical
  let K : Option ι →₀ ℕ := Finsupp.equivFunOnFinite.symm fun o ↦ (Option.elim' (n, a) p o).1
  let s : Option ι → MvPolynomial (Option ι) R := Option.elim' (C r * X none) fun i ↦ X (some i)
  rw [famCoeff, coeff_eq_sum_of_sum_tmul_eq f (fun o ↦ (Option.elim' (n, a) p o).2) s
    (fun o ↦ (Option.elim' (n, r • a) p o).2)
    (by simp [s, Fintype.sum_option, ← smul_eq_C_mul, TensorProduct.smul_tmul])]
  have h (l : Option ι →₀ ℕ) : (∏ o, s o ^ l o).coeff K = if l = K then r ^ n else 0 := by
    rw [show ∏ o, s o ^ l o = C (r ^ l none) * ∏ o, (X o : MvPolynomial (Option ι) R) ^ l o by
      simp only [s, Fintype.prod_option, Option.elim'_none, Option.elim'_some, mul_pow, map_pow,
        mul_assoc], coeff_C_mul, coeff_prod_univ_X_pow]
    by_cases hl : l = K
    · subst hl
      simp [K]
    · rw [ite_eq_right_iff.mpr fun h ↦ absurd h hl, ite_eq_right_iff.mpr, mul_zero]
      exact fun h ↦ absurd (Finsupp.ext h) hl
  have hK : (Finsupp.equivFunOnFinite.symm fun o ↦ (Option.elim' (n, r • a) p o).1) = K := by
    ext o
    cases o <;> rfl
  simp only [hK, h, ite_smul, _root_.zero_smul]
  rw [Finsupp.sum_ite_eq', famCoeff]
  split_ifs with hmem
  · rfl
  · rw [Finsupp.notMem_support_iff.mp hmem, smul_zero]

/-- Two pairs with the same vector merge into one, with a binomial coefficient. -/
private theorem famCoeff_option_option_mul {ι : Type*} [Fintype ι] (x y : ℕ) (a : M)
    (p : ι → ℕ × M) :
    famCoeff f (Option.elim' (x, a) (Option.elim' (y, a) p)) =
      (x + y).choose x • famCoeff f (Option.elim' (x + y, a) p) := by
  classical
  let L : Option ι →₀ ℕ := Finsupp.equivFunOnFinite.symm fun o ↦ (Option.elim' (x + y, a) p o).1
  let s : Option ι → MvPolynomial (Option (Option ι)) R :=
    Option.elim' (X none + X (some none)) fun i ↦ X (some (some i))
  rw [famCoeff, coeff_eq_sum_of_sum_tmul_eq f (fun o ↦ (Option.elim' (x + y, a) p o).2) s
    (fun o ↦ (Option.elim' (x, a) (Option.elim' (y, a) p) o).2)
    (by simp [s, Fintype.sum_option, TensorProduct.add_tmul, add_assoc])]
  set K : Option (Option ι) →₀ ℕ := Finsupp.equivFunOnFinite.symm fun o ↦
    (Option.elim' (x, a) (Option.elim' (y, a) p) o).1
  have h (l : Option ι →₀ ℕ) :
      (∏ o, s o ^ l o).coeff K = if l = L then ((x + y).choose x : R) else 0 := by
    have hprod : ∏ o, s o ^ l o = ∑ q ∈ Finset.antidiagonal (l none), (l none).choose q.1 •
        ∏ o, (X o : MvPolynomial (Option (Option ι)) R) ^
          (Option.elim' q.1 (Option.elim' q.2 fun i ↦ l (some i)) o) := by
      rw [Fintype.prod_option]
      simp only [s, Option.elim'_none, Option.elim'_some]
      rw [(Commute.all _ _).add_pow', Finset.sum_mul]
      refine Finset.sum_congr rfl fun q _ ↦ ?_
      simp [Fintype.prod_option, mul_assoc]
    have hcond (q : ℕ × ℕ) : (∀ o, Option.elim' q.1 (Option.elim' q.2 fun i ↦ l (some i)) o =
        K o) ↔ q = (x, y) ∧ ∀ i, l (some i) = (p i).1 := by
      simp [K, Option.forall, Prod.ext_iff, and_assoc]
    have hns (c : ℕ) (P : MvPolynomial (Option (Option ι)) R) :
        (c • P).coeff K = c • P.coeff K := by
      simpa using map_nsmul (coeffAddMonoidHom K) c P
    rw [hprod, coeff_sum]
    simp only [hns, coeff_prod_univ_X_pow, hcond, ite_and, smul_ite, smul_zero]
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_antidiagonal, L, Finsupp.ext_iff, Option.forall,
      Finsupp.coe_equivFunOnFinite_symm, Option.elim'_none, Option.elim'_some, nsmul_eq_mul,
      mul_one]
    by_cases hxy : x + y = l none
    · simp [hxy, eq_comm]
    · simp [hxy, Ne.symm hxy]
  simp only [h, ite_smul, _root_.zero_smul]
  rw [Finsupp.sum_ite_eq', famCoeff]
  split_ifs with hmem
  · rw [Nat.cast_smul_eq_nsmul]
  · rw [Finsupp.notMem_support_iff.mp hmem, smul_zero]

/-- A pair whose vector is a sum splits into a sum over pairs, as in the divided-power
binomial formula. -/
private theorem famCoeff_option_add {ι : Type*} [Fintype ι] (n : ℕ) (a b : M)
    (p : ι → ℕ × M) :
    famCoeff f (Option.elim' (n, a + b) p) =
      ∑ q ∈ Finset.antidiagonal n,
        famCoeff f (Option.elim' (q.1, a) (Option.elim' (q.2, b) p)) := by
  classical
  let L (q : ℕ × ℕ) : Option (Option ι) →₀ ℕ := Finsupp.equivFunOnFinite.symm fun o ↦
    (Option.elim' (q.1, a) (Option.elim' (q.2, b) p) o).1
  let s : Option (Option ι) → MvPolynomial (Option ι) R :=
    Option.elim' (X none) (Option.elim' (X none) fun i ↦ X (some i))
  rw [famCoeff, coeff_eq_sum_of_sum_tmul_eq f
    (fun o ↦ (Option.elim' (0, a) (Option.elim' (0, b) p) o).2) s
    (fun o ↦ (Option.elim' (n, a + b) p o).2)
    (by simp [s, Fintype.sum_option, TensorProduct.tmul_add, add_assoc])]
  set K : Option ι →₀ ℕ := Finsupp.equivFunOnFinite.symm fun o ↦ (Option.elim' (n, a + b) p o).1
  have h (l : Option (Option ι) →₀ ℕ) (c : N) :
      (∏ o, s o ^ l o).coeff K • c = ∑ q ∈ Finset.antidiagonal n, if l = L q then c else 0 := by
    rw [show ∏ o, s o ^ l o = ∏ o, (X o : MvPolynomial (Option ι) R) ^
        (Option.elim' (l none + l (some none)) (fun i ↦ l (some (some i))) o) by
      simp [s, Fintype.prod_option, pow_add, mul_assoc], coeff_prod_univ_X_pow]
    have hL (q : ℕ × ℕ) : l = L q ↔
        q = (l none, l (some none)) ∧ ∀ i, l (some (some i)) = (p i).1 := by
      simp [L, Finsupp.ext_iff, Option.forall, Prod.ext_iff, eq_comm, and_assoc]
    simp only [hL, ite_and, Finset.sum_ite_eq', Finset.mem_antidiagonal]
    simp only [K, Option.forall, Finsupp.coe_equivFunOnFinite_symm, Option.elim'_none,
      Option.elim'_some]
    split_ifs <;> simp_all
  simp only [Finsupp.sum, h]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  have hv : (fun o ↦ (Option.elim' (0, a) (Option.elim' (0, b) p) o).2) =
      fun o ↦ (Option.elim' (q.1, a) (Option.elim' (q.2, b) p) o).2 := by
    funext o
    rcases o with _ | _ | _ <;> rfl
  rw [Finset.sum_ite_eq', Finsupp.if_mem_support, famCoeff, hv]

section Multiset

variable [DecidableEq M]

/-- The coefficient of `f` attached to a multiset of pairs `(n, m)`. -/
private def famMultiset (s : Multiset (ℕ × M)) : N :=
  famCoeff f fun x : s ↦ (x : ℕ × M)

private theorem famMultiset_cons (q : ℕ × M) (s : Multiset (ℕ × M)) :
    famMultiset f (q ::ₘ s) = famCoeff f (Option.elim' q fun x : s ↦ (x : ℕ × M)) := by
  rw [famMultiset, ← famCoeff_comp_equiv f (Multiset.consEquiv (v := q) (m := s)).symm]
  congr 1
  funext o
  cases o <;> rfl

private theorem famMultiset_cons_cons (q q' : ℕ × M) (s : Multiset (ℕ × M)) :
    famMultiset f (q ::ₘ q' ::ₘ s) =
      famCoeff f (Option.elim' q (Option.elim' q' fun x : s ↦ (x : ℕ × M))) := by
  rw [famMultiset_cons, ← famCoeff_comp_equiv f
    (Equiv.optionCongr (Multiset.consEquiv (v := q') (m := s)).symm)]
  congr 1
  funext o
  rcases o with _ | _ | _ <;> rfl

private theorem famMultiset_map_univ {ι : Type*} [Fintype ι] (p : ι → ℕ × M) :
    famMultiset f (Finset.univ.val.map p) = famCoeff f p := by
  classical
  have hinj : Function.Injective fun x : (Finset.univ.val : Multiset ι) ↦ (x : ι) := by
    intro x y hxy
    apply (Multiset.coeEmbedding _).injective
    have hx := x.2.2
    have hy := y.2.2
    simp only [Multiset.count_eq_one_of_mem Finset.univ.nodup (Finset.mem_univ _)] at hx hy
    simp only [Multiset.coeEmbedding_apply, Prod.mk.injEq]
    exact ⟨hxy, by lia⟩
  let U := Equiv.ofBijective _ ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨hinj, by simp [Multiset.card_coe]⟩)
  rw [famMultiset, ← famCoeff_comp_equiv f (Multiset.mapEquiv _ p), ← famCoeff_comp_equiv f U]
  congr 1
  funext x
  simp [U]

/-- The linear map on polynomials in the variables `X (n, m)` sending the monomial
`∏ X (nᵢ, mᵢ)` to the coefficient of `f` attached to the pairs `(nᵢ, mᵢ)`. -/
private def polyMap : MvPolynomial (ℕ × M) R →ₗ[R] N :=
  (basisMonomials (ℕ × M) R).constr R fun e ↦ famMultiset f (Finsupp.toMultiset e)

private theorem polyMap_monomial (e : ℕ × M →₀ ℕ) :
    polyMap f (monomial e 1) = famMultiset f (Finsupp.toMultiset e) := by
  simpa [polyMap] using (basisMonomials (ℕ × M) R).constr_basis R
    (fun e ↦ famMultiset f (Finsupp.toMultiset e)) e

private theorem polyMap_monomial_mul_X (e : ℕ × M →₀ ℕ) (q : ℕ × M) :
    polyMap f (monomial e 1 * X q) = famMultiset f (q ::ₘ Finsupp.toMultiset e) := by
  rw [X, monomial_mul_monomial, one_mul, polyMap_monomial, map_add, Finsupp.toMultiset_single,
    one_nsmul, Multiset.add_comm, Multiset.singleton_add]

private theorem polyMap_monomial_mul_X_mul_X (e : ℕ × M →₀ ℕ) (q q' : ℕ × M) :
    polyMap f (monomial e 1 * (X q * X q')) =
      famMultiset f (q ::ₘ q' ::ₘ Finsupp.toMultiset e) := by
  rw [mul_comm (X q), ← mul_assoc, X, monomial_mul_monomial, one_mul, polyMap_monomial_mul_X,
    map_add, Finsupp.toMultiset_single, one_nsmul, Multiset.add_comm, Multiset.singleton_add]

/-- The coefficient map respects each defining relation of `Γ_R(M)`, after multiplication by
any monomial. -/
private theorem polyMap_monomial_mul_of_rel {a b : MvPolynomial (ℕ × M) R}
    (h : Rel R M a b) (e : ℕ × M →₀ ℕ) :
    polyMap f (monomial e 1 * a) = polyMap f (monomial e 1 * b) := by
  cases h with
  | rfl_zero => rfl
  | zero =>
    rw [polyMap_monomial_mul_X, mul_one, polyMap_monomial, famMultiset_cons,
      famCoeff_option_zero, famMultiset]
  | smul =>
    rw [mul_smul_comm, map_smul, polyMap_monomial_mul_X, polyMap_monomial_mul_X,
      famMultiset_cons, famMultiset_cons, famCoeff_option_smul]
  | mul =>
    rw [mul_smul_comm, map_nsmul, polyMap_monomial_mul_X_mul_X, polyMap_monomial_mul_X,
      famMultiset_cons_cons, famMultiset_cons, famCoeff_option_option_mul]
  | add =>
    rw [Finset.mul_sum, map_sum, polyMap_monomial_mul_X, famMultiset_cons, famCoeff_option_add]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    rw [polyMap_monomial_mul_X_mul_X, famMultiset_cons_cons]

/-- The ring congruence identifying polynomials which `polyMap f` cannot distinguish after
multiplication by any polynomial. -/
private def polyCon : RingCon (MvPolynomial (ℕ × M) R) where
  r a b := ∀ t, polyMap f (t * a) = polyMap f (t * b)
  iseqv := ⟨fun _ _ ↦ rfl, fun h t ↦ (h t).symm, fun h h' t ↦ (h t).trans (h' t)⟩
  add' h h' t := by rw [mul_add, mul_add, map_add, map_add, h t, h' t]
  mul' {a b c d} h h' t := by
    calc polyMap f (t * (a * c)) = polyMap f (t * c * a) := by ring_nf
      _ = polyMap f (t * c * b) := h (t * c)
      _ = polyMap f (t * b * c) := by ring_nf
      _ = polyMap f (t * b * d) := h' (t * b)
      _ = polyMap f (t * (b * d)) := by ring_nf

private theorem ringCon_le_polyCon : ringCon R M ≤ polyCon f := by
  rw [ringCon, RingCon.ringConGen_le]
  intro a b h t
  induction t using MvPolynomial.induction_on' with
  | monomial e c =>
    rw [show monomial e c = c • monomial e 1 by rw [smul_monomial, smul_eq_mul, mul_one],
      smul_mul_assoc, smul_mul_assoc, map_smul, map_smul, polyMap_monomial_mul_of_rel f h]
  | add t t' ht ht' => rw [add_mul, add_mul, map_add, map_add, ht, ht']

/-- The linear map `Γ_R(M) → N` induced by the coefficients of `f`: it sends
`∏ᵢ dp R nᵢ mᵢ` to the coefficient of `∏ᵢ Xᵢ ^ nᵢ` in `f (∑ᵢ Xᵢ ⊗ mᵢ)`. -/
private def coeffLift : DividedPowerAlgebra R M →ₗ[R] N where
  toFun := Quotient.lift (s := (ringCon R M).toSetoid) (polyMap f) fun a b h ↦ by
    simpa using ringCon_le_polyCon f h 1
  map_add' x y := Quotient.inductionOn₂' x y fun a b ↦
    (congrArg (Quotient.lift (s := (ringCon R M).toSetoid) (polyMap f) _)
      (RingCon.coe_add (c := ringCon R M) a b).symm).trans (map_add (polyMap f) a b)
  map_smul' r x := Quotient.inductionOn' x fun a ↦
    (congrArg (Quotient.lift (s := (ringCon R M).toSetoid) (polyMap f) _)
      (RingCon.coe_smul (c := ringCon R M) r a).symm).trans (map_smul (polyMap f) r a)

private theorem coeffLift_mk (P : MvPolynomial (ℕ × M) R) :
    coeffLift f (P : DividedPowerAlgebra R M) = polyMap f P :=
  rfl

private theorem coeffLift_prod_dp {ι : Type*} [Fintype ι] (p : ι → ℕ × M) :
    coeffLift f (∏ i, dp R (p i).1 (p i).2) = famCoeff f p := by
  rw [show ∏ i, dp R (p i).1 (p i).2 =
      ((monomial (∑ i, Finsupp.single (p i) 1) 1 : MvPolynomial (ℕ × M) R) :
        DividedPowerAlgebra R M) by
    rw [monomial_sum_one]
    exact (map_prod (RingCon.mkₐ R (ringCon R M)) _ _).symm, coeffLift_mk, polyMap_monomial,
    map_sum]
  simp only [Finsupp.toMultiset_single, one_nsmul]
  rw [← famMultiset_map_univ, ← Multiset.sum_map_singleton (Finset.univ.val.map p),
    Multiset.map_map]
  rfl

end Multiset

/-- Every homogeneous polynomial law of degree `d` is represented by a linear map on `Γ^d_R(M)`:
the comparison `homogeneousLawMap` is surjective. -/
theorem homogeneousLawMap_surjective (d : ℕ) :
    Function.Surjective (homogeneousLawMap R M N d) := by
  classical
  rintro ⟨f, hf⟩
  refine ⟨coeffLift f ∘ₗ (homogeneousSubmodule (R := R) (M := M) d).subtype,
    Subtype.ext (ext_coeff fun n m ↦ Finsupp.ext fun k ↦ ?_)⟩
  by_cases hk : ∑ j, k j = d
  · rw [coeff_apply, lid_rTensor_lcoeff_homogeneousLawMap d _ m k hk, LinearMap.comp_apply,
      Submodule.subtype_apply, coeffLift_prod_dp f fun j ↦ (k j, m j), famCoeff]
    simp
  · rw [(mem_homogeneousSubmodule.mp (homogeneousLawMap R M N d _).2).coeff_eq_zero m hk,
      (mem_homogeneousSubmodule.mp hf).coeff_eq_zero m hk]

variable (R M N) in
/-- **Roby representability**: composition with the universal law `γ_d` is a linear equivalence
between linear maps `Γ^d_R(M) → N` and homogeneous polynomial laws `M → N` of degree `d`. -/
def homogeneousLawEquiv (d : ℕ) :
    (homogeneousSubmodule (R := R) (M := M) d →ₗ[R] N) ≃ₗ[R]
      PolynomialLaw.homogeneousSubmodule R M N d :=
  LinearEquiv.ofBijective (homogeneousLawMap R M N d)
    ⟨homogeneousLawMap_injective d, homogeneousLawMap_surjective d⟩

@[simp]
theorem homogeneousLawEquiv_apply (d : ℕ)
    (g : homogeneousSubmodule (R := R) (M := M) d →ₗ[R] N) :
    homogeneousLawEquiv R M N d g = homogeneousLawMap R M N d g :=
  (rfl)

/-- The linear map representing a homogeneous law `f` of degree `d` sends `∏ⱼ dp R kⱼ mⱼ`, with
`∑ⱼ kⱼ = d`, to the coefficient of `∏ⱼ Tⱼ ^ kⱼ` in `f (∑ⱼ Tⱼ ⊗ mⱼ)`. -/
theorem homogeneousLawEquiv_symm_apply_prod_dp (d : ℕ)
    (f : PolynomialLaw.homogeneousSubmodule R M N d) {ι : Type*} [Fintype ι] (m : ι → M)
    (k : ι →₀ ℕ) (hk : ∑ j, k j = d) :
    (homogeneousLawEquiv R M N d).symm f
        ⟨∏ j, dp R (k j) (m j), prod_dp_mem_homogeneousSubmodule_of_sum_eq m k hk⟩ =
      PolynomialLaw.coeff R N m (f : M →ₚₗ[R] N) k := by
  rw [PolynomialLaw.coeff_apply, ← lid_rTensor_lcoeff_homogeneousLawMap d _ m k hk,
    ← homogeneousLawEquiv_apply, LinearEquiv.apply_symm_apply]

/-- The linear map representing a homogeneous law `f` of degree `d` sends `dp R d m` to the
ground value `f m`. -/
@[simp]
theorem homogeneousLawEquiv_symm_apply_dp (d : ℕ)
    (f : PolynomialLaw.homogeneousSubmodule R M N d) (m : M) :
    (homogeneousLawEquiv R M N d).symm f ⟨dp R d m, dp_mem_homogeneousSubmodule d m⟩ =
      (f : M →ₚₗ[R] N).ground m := by
  conv_rhs => rw [← (homogeneousLawEquiv R M N d).apply_symm_apply f]
  rw [homogeneousLawEquiv_apply, coe_homogeneousLawMap_apply,
    ground_toPolynomialLaw_comp_gamma_apply]

end Existence

end DividedPowerAlgebra
