/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.RingTheory.Polynomial.UniversalFactorizationRing
public import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import Mathlib.Tactic.LinearCombination
import TauCeti.Algebra.Ring.Parity
import TauCeti.RingTheory.MvPolynomial.Rescale

/-!
# Vieta's formulas for indexed families of roots

Mathlib reads the coefficients of a product of linear factors off the elementary symmetric
functions of the multiset of its roots (`Multiset.prod_X_sub_C_coeff`). Here the roots are a
family `x : σ → S` indexed by a finite type and the elementary symmetric functions are the
values of `MvPolynomial.esymm`: the `k`-th elementary symmetric polynomial at `x` is `(-1) ^ k`
times the coefficient of `∏ i, (X - C (x i))` in degree `card σ - k`.

Over a domain, a monic polynomial whose degree is the size of a finite set `s` and whose
roots, with multiplicity, are the values of `x` on `s` is the product
`∏ i ∈ s, (X - C (x i))`. When `s` is all of a finite type `σ` this is the product above, so the
same formula computes its coefficients.

For the universal monic polynomial `Polynomial.freeMonic R m` over `MvPolynomial (Fin m) R`,
combining Vieta's formulas with the fundamental theorem of symmetric polynomials yields an
`R`-algebra isomorphism `MvPolynomial.vietaAlgEquiv` onto `symmetricSubalgebra (Fin m) R` (and an
injective `R`-algebra endomorphism `MvPolynomial.vietaAlgHom`) sending each coefficient variable
`X i` to `(-1) ^ (m - i) * esymm (Fin m) R (m - i)` and factoring `Polynomial.freeMonic R m` into
`∏ j, (X - C (X j))`.

## Main results

* `MvPolynomial.aeval_esymm_eq_coeff_prod_X_sub_C`: the elementary symmetric polynomials at `x`
  are the signed coefficients of `∏ i, (X - C (x i))`.
* `MvPolynomial.vietaAlgEquiv`, `MvPolynomial.vietaAlgHom`, `MvPolynomial.range_vietaAlgHom`,
  `MvPolynomial.mem_range_vietaAlgHom_iff`, `MvPolynomial.vietaAlgEquiv_X`,
  `MvPolynomial.vietaAlgEquiv_symm_esymm`: universal Vieta correspondence identifying
  `MvPolynomial (Fin m) R` with `symmetricSubalgebra (Fin m) R` and its forward and inverse
  generator rules.
* `MvPolynomial.map_vietaAlgHom_freeMonic`: `Polynomial.freeMonic R m` maps along
  `MvPolynomial.vietaAlgHom R m` to `∏ j, (X - C (X j))`.
* `MvPolynomial.isUnit_of_isUnit_vietaAlgHom`: `MvPolynomial.vietaAlgHom R m` reflects units.
* `Polynomial.eq_prod_X_sub_C_of_monic_of_roots_eq`: a monic polynomial whose roots are listed by
  `x` on a finite set `s` is the product of the linear factors `X - C (x i)` over `s`.

Evaluated at a point `v`, the product `P(v) = ∏_{w ∈ s} (v - w)` of a multiset `s` of `m` elements
is `vᵐ + ∑_{j=1}^{m} (-1)ʲ e_j(s) v^(m-j)`, and its derivative at a root `v ∈ s` is
`P'(v) = ∏_{w ∈ s ∖ v} (v - w)`. Two further identities hold at a root, the first being Euler's
identity `v P'(v) = m P(v) - ∑ (-1)ʲ j e_j(s) v^(m-j)` with `P(v) = 0`. They express a combination
of the coefficients of `P` with the weights `(-1)^(j-1) v^(m-j)` through `P'(v)`, which is how
first-order equations for the coefficients of `P` become equations for its simple roots.

* `Multiset.prod_map_sub_eq_pow_add_sum_esymm`: `∏_{w ∈ s} (v - w) = vᵐ + ∑ (-1)ʲ e_j(s) v^(m-j)`.
* `Multiset.prod_map_sub_eq_zero_iff`: over a domain, `v` is a root of `∏_{w ∈ s} (W - w)` exactly
  when `v ∈ s`.
* `Multiset.eq_zero_of_mem_of_forall_esymm_eq_zero`: over a reduced ring, a multiset whose
  elementary symmetric functions of positive degree vanish consists of zeros.
* `Multiset.prod_map_sub_erase_eq_sum_esymm`: the derivative at a root,
  `∏_{w ∈ s ∖ v} (v - w) = m v^(m-1) + ∑ (-1)ʲ (m - j) e_j(s) v^(m-j-1)`.
* `Multiset.prod_map_sub_erase_ne_zero`: it is nonzero at a simple root of a multiset over a
  domain.
* `Multiset.sum_mul_esymm_eq_mul_prod_map_sub_erase`:
  `∑ (-1)^(j-1) v^(m-j) j e_j(s) = v ∏_{w ∈ s ∖ v} (v - w)` at a root.
* `Multiset.sum_mul_sum_map_mul_esymm_erase`: for any weights `f`,
  `∑ (-1)^(j-1) v^(m-j) ∑_{w ∈ s} f(w) e_{j-1}(s ∖ w) = f(v) ∏_{w ∈ s ∖ v} (v - w)` at a root.
-/

public section

namespace MvPolynomial

variable {σ R S : Type*} [Fintype σ] [CommSemiring R] [CommRing S] [Algebra R S]

/-- **Vieta's formulas for an indexed family of roots**: the `k`-th elementary symmetric
polynomial, evaluated at `x : σ → S`, is `(-1) ^ k` times the coefficient of the monic polynomial
`∏ i, (X - C (x i))` in degree `card σ - k`. -/
theorem aeval_esymm_eq_coeff_prod_X_sub_C (x : σ → S) {k : ℕ} (hk : k ≤ Fintype.card σ) :
    aeval x (esymm σ R k) =
      (-1) ^ k * (∏ i, (Polynomial.X - Polynomial.C (x i))).coeff (Fintype.card σ - k) := by
  rw [aeval_esymm_eq_multiset_esymm, Finset.prod_eq_multiset_prod,
    ← Function.comp_def (fun t => Polynomial.X - Polynomial.C t) x, ← Multiset.map_map,
    Multiset.prod_X_sub_C_coeff _ (by simp)]
  simp [Nat.sub_sub_self hk]

/-- Vieta's `R`-algebra isomorphism from the universal coefficient ring `MvPolynomial (Fin m) R`
onto the symmetric polynomials in `m` root variables, sending `X i` (the degree-`i` coefficient)
to `(-1) ^ (m - i) * esymm (Fin m) R (m - i)`. -/
noncomputable def vietaAlgEquiv (R : Type*) [CommRing R] (m : ℕ) :
    MvPolynomial (Fin m) R ≃ₐ[R] symmetricSubalgebra (Fin m) R :=
  (renameEquiv R Fin.revPerm).trans
    ((rescaleEquiv (fun j : Fin m ↦ (-1 : Rˣ) ^ ((j : ℕ) + 1))).trans
      (esymmAlgEquiv (Fin m) R (Fintype.card_fin m)))

/-- The injective `R`-algebra homomorphism embedding `MvPolynomial (Fin m) R` into the root-variable
ring `MvPolynomial (Fin m) R` with image `symmetricSubalgebra (Fin m) R`. -/
noncomputable def vietaAlgHom (R : Type*) [CommRing R] (m : ℕ) :
    MvPolynomial (Fin m) R →ₐ[R] MvPolynomial (Fin m) R :=
  (symmetricSubalgebra (Fin m) R).val.comp (vietaAlgEquiv R m).toAlgHom

/-- Applying `MvPolynomial.vietaAlgHom` returns the underlying symmetric polynomial of
`MvPolynomial.vietaAlgEquiv`. -/
theorem vietaAlgHom_apply {R : Type*} [CommRing R] {m : ℕ} (p : MvPolynomial (Fin m) R) :
    vietaAlgHom R m p = (vietaAlgEquiv R m p : MvPolynomial (Fin m) R) := by
  rfl

/-- `MvPolynomial.vietaAlgHom` is injective. -/
theorem vietaAlgHom_injective (R : Type*) [CommRing R] (m : ℕ) :
    Function.Injective (vietaAlgHom R m) :=
  Subtype.val_injective.comp (vietaAlgEquiv R m).injective

/-- Every polynomial in the image of `MvPolynomial.vietaAlgHom` is symmetric. -/
theorem isSymmetric_vietaAlgHom {R : Type*} [CommRing R] {m : ℕ}
    (p : MvPolynomial (Fin m) R) : (vietaAlgHom R m p).IsSymmetric :=
  (vietaAlgEquiv R m p).property

/-- The range of `MvPolynomial.vietaAlgHom` is `symmetricSubalgebra (Fin m) R`. -/
@[simp]
theorem range_vietaAlgHom (R : Type*) [CommRing R] (m : ℕ) :
    (vietaAlgHom R m).range = symmetricSubalgebra (Fin m) R := by
  ext q
  simp only [AlgHom.mem_range, vietaAlgHom_apply, mem_symmetricSubalgebra]
  constructor
  · rintro ⟨p, rfl⟩
    exact (vietaAlgEquiv R m p).property
  · intro hq
    exact ⟨(vietaAlgEquiv R m).symm ⟨q, hq⟩, by simp⟩

/-- A polynomial in `MvPolynomial (Fin m) R` lies in the range of `MvPolynomial.vietaAlgHom` if
and only if it is symmetric. -/
theorem mem_range_vietaAlgHom_iff {R : Type*} [CommRing R] {m : ℕ}
    {q : MvPolynomial (Fin m) R} :
    q ∈ Set.range (vietaAlgHom R m) ↔ q.IsSymmetric := by
  rw [Set.mem_range, ← AlgHom.mem_range, range_vietaAlgHom, mem_symmetricSubalgebra]

/-- On variables, `MvPolynomial.vietaAlgHom` sends `X i` to the signed elementary symmetric
polynomial `(-1) ^ (m - i) * esymm (Fin m) R (m - i)`. -/
@[simp]
theorem vietaAlgHom_X {R : Type*} [CommRing R] {m : ℕ} (i : Fin m) :
    vietaAlgHom R m (X i) =
      (-1) ^ (m - (i : ℕ)) * esymm (Fin m) R (m - (i : ℕ)) := by
  have hrev : (i.rev : ℕ) + 1 = m - (i : ℕ) := by
    rw [Fin.val_rev]
    have := i.isLt
    omega
  calc vietaAlgHom R m (X i)
    _ = ((esymmAlgEquiv (Fin m) R (Fintype.card_fin m))
          ((rescaleEquiv (fun j : Fin m ↦ (-1 : Rˣ) ^ ((j : ℕ) + 1)))
            (renameEquiv R Fin.revPerm (X i))) : MvPolynomial (Fin m) R) := by
          rw [vietaAlgHom_apply, vietaAlgEquiv, AlgEquiv.trans_apply, AlgEquiv.trans_apply]
    _ = ((esymmAlgEquiv (Fin m) R (Fintype.card_fin m))
          (C ((-1 : R) ^ ((i.rev : ℕ) + 1)) * X i.rev) : MvPolynomial (Fin m) R) := by
          rw [renameEquiv_apply, rename_X, Fin.revPerm_apply, rescaleEquiv_apply, rescale_X,
            Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]
    _ = ((-1 : R) ^ ((i.rev : ℕ) + 1)) •
          ((esymmAlgEquiv (Fin m) R (Fintype.card_fin m)) (X i.rev) : MvPolynomial (Fin m) R) := by
          rw [C_eq_algebraMap, ← Algebra.smul_def, map_smul, SetLike.val_smul]
    _ = (-1) ^ (m - (i : ℕ)) * esymm (Fin m) R (m - (i : ℕ)) := by
          rw [esymmAlgEquiv_apply, esymmAlgHom_apply, aeval_X, hrev, Algebra.smul_def,
            map_pow, map_neg, map_one]

/-- On variables, `MvPolynomial.vietaAlgEquiv` sends `X i` to the signed elementary symmetric
polynomial `(-1) ^ (m - i) * esymm (Fin m) R (m - i)` in `symmetricSubalgebra (Fin m) R`. -/
@[simp]
theorem vietaAlgEquiv_X {R : Type*} [CommRing R] {m : ℕ} (i : Fin m) :
    vietaAlgEquiv R m (X i) =
      ⟨(-1) ^ (m - (i : ℕ)) * esymm (Fin m) R (m - (i : ℕ)), by
        rw [← vietaAlgHom_X]
        exact isSymmetric_vietaAlgHom (X i)⟩ :=
  Subtype.ext (vietaAlgHom_X i)

/-- The inverse of `MvPolynomial.vietaAlgEquiv` maps the elementary symmetric generator
`esymm (Fin m) R (j + 1)` to `(-1) ^ (j + 1) * X j.rev`. -/
@[simp]
theorem vietaAlgEquiv_symm_esymm {R : Type*} [CommRing R] {m : ℕ} (j : Fin m) :
    (vietaAlgEquiv R m).symm ⟨esymm (Fin m) R (j + 1), esymm_isSymmetric (Fin m) R _⟩ =
      (-1) ^ ((j : ℕ) + 1) * X j.rev := by
  rw [AlgEquiv.symm_apply_eq]
  apply Subtype.ext
  rw [← vietaAlgHom_apply, map_mul, map_pow, map_neg, map_one, vietaAlgHom_X, Fin.val_rev]
  have hj := j.isLt
  have hj' : m - (m - ((j : ℕ) + 1)) = (j : ℕ) + 1 := by omega
  rw [hj', ← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]

/-- Mapping `Polynomial.freeMonic R m` along `MvPolynomial.vietaAlgHom` factors it into linear
root factors `∏ j, (Polynomial.X - Polynomial.C (MvPolynomial.X j))`. -/
theorem map_vietaAlgHom_freeMonic (R : Type*) [CommRing R] (m : ℕ) :
    (Polynomial.freeMonic R m).map (vietaAlgHom R m).toRingHom =
      ∏ j : Fin m, (Polynomial.X - Polynomial.C (X j)) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact Subsingleton.elim _ _
  let P : Polynomial (MvPolynomial (Fin m) R) :=
    ∏ j : Fin m, (Polynomial.X - Polynomial.C (X j))
  have hmon : P.Monic :=
    Polynomial.monic_prod_of_monic Finset.univ _ fun j _ ↦ Polynomial.monic_X_sub_C _
  have hdeg : P.natDegree = m := by
    simp [P, Polynomial.natDegree_finsetProd_X_sub_C_eq_card]
  have hv_eq : vietaAlgHom R m = aeval (fun k : Fin m ↦ P.coeff k) := by
    refine algHom_ext fun k : Fin m ↦ ?_
    rw [aeval_X, vietaAlgHom_X]
    have hv := aeval_esymm_eq_coeff_prod_X_sub_C
      (R := R) (X : Fin m → MvPolynomial (Fin m) R) (k := m - k) (by simp)
    rw [aeval_X_left, AlgHom.id_apply, Fintype.card_fin, Nat.sub_sub_self k.isLt.le] at hv
    rw [hv, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
    simp [P]
  rw [hv_eq]
  exact congrArg Subtype.val
    ((mapEquivMonic R _ m).apply_symm_apply (.mk P hmon hdeg))

/-- `MvPolynomial.vietaAlgHom R m` reflects units. -/
theorem isUnit_of_isUnit_vietaAlgHom {R : Type*} [CommRing R] {m : ℕ}
    {b : MvPolynomial (Fin m) R} (hb : IsUnit (vietaAlgHom R m b)) : IsUnit b := by
  obtain ⟨c, hc⟩ := hb.exists_right_inv
  have hc_symm : c.IsSymmetric := by
    intro e
    have h1 : vietaAlgHom R m b * rename e c = 1 := by
      have h := congrArg (rename e) hc
      rw [map_mul, map_one, isSymmetric_vietaAlgHom b e] at h
      exact h
    calc rename e c = (c * vietaAlgHom R m b) * rename e c := by
          rw [mul_comm c, hc, one_mul]
      _ = c * (vietaAlgHom R m b * rename e c) := mul_assoc _ _ _
      _ = c := by rw [h1, mul_one]
  obtain ⟨d, hd⟩ := mem_range_vietaAlgHom_iff.mpr hc_symm
  have hbd : b * d = 1 := vietaAlgHom_injective R m (by rw [map_mul, map_one, hd, hc])
  exact IsUnit.of_mul_eq_one d hbd

end MvPolynomial

namespace Polynomial

variable {σ R : Type*} [CommRing R] [IsDomain R]

/-- A monic polynomial of degree `s.card` whose roots, with multiplicity, are listed by `x` on the
finite set `s` is the product of the linear factors `X - C (x i)` over `s`. -/
theorem eq_prod_X_sub_C_of_monic_of_roots_eq {f : R[X]} {s : Finset σ} {x : σ → R}
    (hf : f.Monic) (hdeg : f.natDegree = s.card) (hroots : f.roots = s.val.map x) :
    f = ∏ i ∈ s, (X - C (x i)) := by
  rw [← prod_multiset_X_sub_C_of_monic_of_roots_card_eq hf (by simp [hroots, hdeg]), hroots,
    Multiset.map_map, Function.comp_def, Finset.prod_map_val]

end Polynomial

namespace Multiset

variable {R : Type*} [CommRing R] {s : Multiset R} {v : R} {m : ℕ}

/-- A sum over `1 ≤ j ≤ m` as a sum over `0 ≤ i < m` of the shifted terms. -/
private theorem sum_Icc_one_eq_sum_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) (m : ℕ) :
    ∑ j ∈ Finset.Icc 1 m, f j = ∑ i ∈ Finset.range m, f (i + 1) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [add_comm]

/-- **Vieta's formula, evaluated.** `∏_{w ∈ s} (v - w) = ∑_{i=0}^{m} (-1)ⁱ eᵢ(s) v^(m-i)`, where
`m` is the cardinality of `s`. -/
theorem prod_map_sub_eq_sum_esymm (s : Multiset R) (v : R) :
    (s.map fun w ↦ v - w).prod =
      ∑ i ∈ Finset.range (card s + 1), (-1) ^ i * s.esymm i * v ^ (card s - i) := by
  have h := congrArg (Polynomial.eval v) (prod_X_sub_X_eq_sum_esymm s)
  simp only [Polynomial.eval_multiset_prod, map_map, Function.comp_def, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_neg, Polynomial.eval_one] at h
  rw [h]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- **Vieta's formula, evaluated**, with the leading term separated:
`∏_{w ∈ s} (v - w) = vᵐ + ∑_{j=1}^{m} (-1)ʲ e_j(s) v^(m-j)` for a multiset of `m` elements. -/
theorem prod_map_sub_eq_pow_add_sum_esymm (hs : card s = m) (v : R) :
    (s.map fun w ↦ v - w).prod =
      v ^ m + ∑ j ∈ Finset.Icc 1 m, (-1) ^ j * s.esymm j * v ^ (m - j) := by
  rw [prod_map_sub_eq_sum_esymm, hs, Finset.sum_range_succ', sum_Icc_one_eq_sum_range]
  simp [add_comm]

/-- Over a domain, `v` is a root of `∏_{w ∈ s} (W - w)` exactly when `v ∈ s`. -/
theorem prod_map_sub_eq_zero_iff [IsDomain R] : (s.map fun w ↦ v - w).prod = 0 ↔ v ∈ s := by
  simp [prod_eq_zero_iff, sub_eq_zero]

/-- Over a reduced ring, if the elementary symmetric functions of positive degree of `s` vanish,
then every element of `s` is `0`: it is a root of `∏_{w ∈ s} (W - w) = Wᵐ`. -/
theorem eq_zero_of_mem_of_forall_esymm_eq_zero [IsReduced R] (h : ∀ j, j ≠ 0 → s.esymm j = 0)
    (hv : v ∈ s) : v = 0 := by
  have hP := prod_map_sub_eq_pow_add_sum_esymm (s := s) rfl v
  rw [prod_eq_zero (mem_map.2 ⟨v, hv, sub_self v⟩), Finset.sum_eq_zero fun j hj ↦ by
    rw [h j (Nat.one_le_iff_ne_zero.1 (Finset.mem_Icc.1 hj).1), mul_zero, zero_mul],
    add_zero] at hP
  exact IsNilpotent.eq_zero ⟨_, hP.symm⟩

variable [DecidableEq R]

/-- **The derivative at a root.** If `v ∈ s` and `s` has `m` elements, the derivative
`m v^(m-1) + ∑_{j=1}^{m} (-1)ʲ (m - j) e_j(s) v^(m-j-1)` of `∏_{w ∈ s} (W - w)` at `W = v` is
`∏_{w ∈ s ∖ v} (v - w)`. -/
theorem prod_map_sub_erase_eq_sum_esymm (hs : card s = m) (hv : v ∈ s) :
    ((s.erase v).map fun w ↦ v - w).prod =
      m * v ^ (m - 1) +
        ∑ j ∈ Finset.Icc 1 m, (-1) ^ j * s.esymm j * ((m - j : ℕ) * v ^ (m - j - 1)) := by
  rw [← Polynomial.eval_multiset_prod_X_sub_C_derivative hv, prod_X_sub_X_eq_sum_esymm s, hs]
  simp only [Polynomial.derivative_sum, Polynomial.derivative_mul, Polynomial.derivative_pow,
    Polynomial.derivative_neg, Polynomial.derivative_one, Polynomial.derivative_C,
    Polynomial.derivative_X, Polynomial.eval_finsetSum, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_neg, Polynomial.eval_one, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_zero]
  rw [Finset.sum_range_succ', sum_Icc_one_eq_sum_range]
  rw [esymm_zero]
  rw [add_comm]
  congr 1
  · simp
  · exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- At a simple root `v` of `∏_{w ∈ s} (W - w)`, over a domain, the derivative
`∏_{w ∈ s ∖ v} (v - w)` is nonzero. -/
theorem prod_map_sub_erase_ne_zero [IsDomain R] (hv : s.count v = 1) :
    ((s.erase v).map fun w ↦ v - w).prod ≠ 0 := by
  have hnot : v ∉ s.erase v := by
    rw [← count_eq_zero, count_erase_self, hv]
  refine prod_ne_zero fun h ↦ ?_
  obtain ⟨w, hw, hw0⟩ := mem_map.1 h
  rw [sub_eq_zero] at hw0
  subst hw0
  exact hnot hw

/-- **Euler's identity at a root.** If `v ∈ s` and `s` has `m` elements, then
`∑_{j=1}^{m} (-1)^(j-1) v^(m-j) j e_j(s) = v ∏_{w ∈ s ∖ v} (v - w)`: at a zero `v` of
`P = ∏_{w ∈ s} (W - w)`, `v P'(v) = m P(v) - ∑ (-1)ʲ j e_j(s) v^(m-j)`. -/
theorem sum_mul_esymm_eq_mul_prod_map_sub_erase (hs : card s = m) (hv : v ∈ s) :
    ∑ j ∈ Finset.Icc 1 m, (-1) ^ (j - 1) * v ^ (m - j) * (j * s.esymm j) =
      v * ((s.erase v).map fun w ↦ v - w).prod := by
  have hP : v ^ m + ∑ j ∈ Finset.Icc 1 m, (-1) ^ j * s.esymm j * v ^ (m - j) = 0 := by
    rw [← prod_map_sub_eq_pow_add_sum_esymm hs]
    exact prod_eq_zero (mem_map.2 ⟨v, hv, sub_self v⟩)
  rw [prod_map_sub_erase_eq_sum_esymm hs hv, mul_add, Finset.mul_sum]
  -- `v · (m - j) v^(m-j-1) = (m - j) v^(m-j)`, and the terms with `m` are `m P(v) = 0`.
  have hterm : ∀ j ∈ Finset.Icc 1 m, v * ((-1) ^ j * s.esymm j * ((m - j : ℕ) * v ^ (m - j - 1))) =
      m * ((-1) ^ j * s.esymm j * v ^ (m - j)) -
        (-1) ^ (j - 1) * v ^ (m - j) * (j * s.esymm j) * (-1) := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    have hsign : ((-1 : R) ^ j) = (-1) ^ (j - 1) * (-1) := by
      rw [← pow_succ, Nat.sub_add_cancel hj.1]
    rcases Nat.lt_or_ge j m with hjm | hjm
    · have hpow : v * v ^ (m - j - 1) = v ^ (m - j) := by
        rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ m - j)]
      rw [Nat.cast_sub hj.2, hsign]
      linear_combination ((-1) ^ (j - 1) * (-1) * s.esymm j * (m - j)) * hpow
    · have hjm : j = m := le_antisymm hj.2 hjm
      subst hjm
      rw [Nat.sub_self, hsign]
      simp only [Nat.cast_zero, zero_mul, mul_zero, pow_zero]
      ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  have hm : (m : R) * v ^ (m - 1) * v = m * v ^ m := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · rw [mul_assoc, ← pow_succ, Nat.sub_add_cancel hm]
  linear_combination (-(m : R)) * hP - hm

/-- At a root `v ∈ s`, a weighted sum `∑_{w ∈ s} f(w) ∏_{u ∈ s ∖ w} (v - u)` of the Lagrange
products reduces to its terms with `w = v`: every other product contains the factor `v - v`. -/
theorem sum_map_mul_prod_map_sub_erase (f : R → R) (hv : v ∈ s) :
    (s.map fun w ↦ f w * ((s.erase w).map fun u ↦ v - u).prod).sum =
      f v * ((s.erase v).map fun u ↦ v - u).prod := by
  rw [← sum_map_erase hv, add_eq_left]
  refine sum_eq_zero fun x hx ↦ ?_
  obtain ⟨w, hw, rfl⟩ := mem_map.1 hx
  -- `v` still lies in `s ∖ w`: either `w ≠ v`, or `w = v` occurs twice in `s`.
  have hvw : v ∈ s.erase w := by
    by_cases h : w = v
    · subst h
      exact hw
    · exact (mem_erase_of_ne (Ne.symm h)).2 hv
  rw [prod_eq_zero (mem_map.2 ⟨v, hvw, sub_self v⟩), mul_zero]

/-- At a root `v ∈ s` of `∏_{w ∈ s} (W - w)`, with `s` of `m` elements, for any weights `f`,
`∑_{j=1}^{m} (-1)^(j-1) v^(m-j) ∑_{w ∈ s} f(w) e_{j-1}(s ∖ w) = f(v) ∏_{w ∈ s ∖ v} (v - w)`. -/
theorem sum_mul_sum_map_mul_esymm_erase (hs : card s = m) (hv : v ∈ s) (f : R → R) :
    ∑ j ∈ Finset.Icc 1 m, (-1) ^ (j - 1) * v ^ (m - j) *
        (s.map fun w ↦ f w * (s.erase w).esymm (j - 1)).sum =
      f v * ((s.erase v).map fun w ↦ v - w).prod := by
  have hm : 1 ≤ m := hs ▸ card_pos_iff_exists_mem.2 ⟨v, hv⟩
  rw [← sum_map_mul_prod_map_sub_erase f hv]
  simp_rw [← sum_map_mul_left]
  rw [← sum_map_sum]
  refine congrArg sum (map_congr rfl fun w hw ↦ ?_)
  have hcard : card (s.erase w) = m - 1 := by
    rw [card_erase_of_mem hw, hs, Nat.pred_eq_sub_one]
  rw [prod_map_sub_eq_sum_esymm, hcard, Nat.sub_add_cancel hm, Finset.mul_sum,
    sum_Icc_one_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Nat.add_sub_cancel, Nat.sub_sub, add_comm 1 i]
  ring

end Multiset
