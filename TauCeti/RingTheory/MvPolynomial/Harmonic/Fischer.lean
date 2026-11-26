/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Defs
public import TauCeti.RingTheory.MvPolynomial.Harmonic
public import TauCeti.RingTheory.MvPolynomial.LinearSubst

/-!
# The Fischer inner product on multivariate polynomials

For finitely many variables `Xᵢ` (`i ∈ σ`) and a commutative star-semiring `R`, the **Fischer**
(or Bombieri / apolar) Hermitian form on `MvPolynomial σ R` is

`⟨p, q⟩_F = ∑_m (∏_i (m i)!) * star (p.coeff m) * q.coeff m`.

It is conjugate-linear in the first argument and linear in the second, and it makes multiplication
by `X i` adjoint to the partial derivative `pderiv i`:

`⟨X i * p, q⟩_F = ⟨p, ∂ᵢ q⟩_F`.

Consequently, multiplication by the squared norm `r² = ∑ᵢ Xᵢ²` is adjoint to the polynomial
Laplacian `Δ = ∑ᵢ ∂ᵢ²` (`MvPolynomial.fischerInner_normSq_mul_left`), so harmonic polynomials are
orthogonal to all multiples of `r²`. Moreover, by induction on the first argument using the chain
rule `MvPolynomial.pderiv_linearSubst`, any unitary linear change of variables `M` with `M Mᴴ = 1`
preserves the form (`MvPolynomial.fischerInner_linearSubst_of_mul_conjTranspose_eq_one`).

Over `𝕜` with `[RCLike 𝕜]` (in particular `ℝ` or `ℂ`), the form is positive definite and yields an
`InnerProductSpace.Core 𝕜 (MvPolynomial σ 𝕜)` (`MvPolynomial.fischerInnerCore`). This core is not
installed as a global `InnerProductSpace` instance, because subspaces such as `harmonicSubmodule`
also carry other natural inner products (for example the `L²` inner product on the unit sphere).

## Main definitions

* `MvPolynomial.fischerInner`: the Fischer Hermitian form on `MvPolynomial σ R`.
* `MvPolynomial.fischerInnerCore`: the `InnerProductSpace.Core 𝕜 (MvPolynomial σ 𝕜)` induced by
  `fischerInner` for `[RCLike 𝕜]`.

## Main results

* `MvPolynomial.star_fischerInner`: conjugate symmetry `star ⟨p, q⟩_F = ⟨q, p⟩_F`.
* `MvPolynomial.fischerInner_X_mul_left` and `MvPolynomial.fischerInner_X_mul_right`:
  multiplication by `X i` is adjoint to `pderiv i`.
* `MvPolynomial.fischerInner_normSq_mul_left` and `MvPolynomial.fischerInner_normSq_mul_right`:
  multiplication by `normSq σ R` is adjoint to `laplacian`.
* `MvPolynomial.fischerInner_linearSubst_of_mul_conjTranspose_eq_one`: unitary invariance
  `⟨p ∘ M, q ∘ M⟩_F = ⟨p, q⟩_F` whenever `M Mᴴ = 1`.
* `MvPolynomial.re_fischerInner_self_nonneg` and `MvPolynomial.fischerInner_self_eq_zero_iff`:
  positivity and definiteness over `[RCLike 𝕜]`.

## References

* E. Fischer, *Über die Differentiationsprozesse der Algebra*, J. Reine Angew. Math. 148 (1917),
  1–78.
* S. Axler, P. Bourdon and W. Ramey, *Harmonic Function Theory*, 2nd ed., Springer GTM 137 (2001),
  Chapter 5 (the apolar inner product on polynomials).
-/

public section

open Matrix

namespace MvPolynomial

section CommSemiring

variable {σ R : Type*} [Fintype σ] [CommSemiring R] [StarRing R]

/-- The **Fischer** (or Bombieri / apolar) Hermitian form on `MvPolynomial σ R`:
`⟨p, q⟩_F = ∑_m (∏_i (m i)!) * star (p.coeff m) * q.coeff m`.
It is conjugate-linear in the first argument and linear in the second, making `X i * ·` adjoint
to `pderiv i` (`MvPolynomial.fischerInner_X_mul_left`) and `normSq σ R * ·` adjoint to `laplacian`
(`MvPolynomial.fischerInner_normSq_mul_left`). -/
noncomputable def fischerInner (p q : MvPolynomial σ R) : R :=
  ∑ m ∈ p.support, (∏ i, ((m i).factorial : R)) * star (p.coeff m) * q.coeff m

theorem fischerInner_def (p q : MvPolynomial σ R) :
    fischerInner p q =
      ∑ m ∈ p.support, (∏ i, ((m i).factorial : R)) * star (p.coeff m) * q.coeff m :=
  (rfl)

/-- The Fischer form can be summed over any finite set containing the support of the first
argument. -/
theorem fischerInner_eq_sum_of_support_subset {p q : MvPolynomial σ R} {s : Finset (σ →₀ ℕ)}
    (hs : p.support ⊆ s) :
    fischerInner p q =
      ∑ m ∈ s, (∏ i, ((m i).factorial : R)) * star (p.coeff m) * q.coeff m := by
  rw [fischerInner_def]
  refine Finset.sum_subset hs fun m _ hm ↦ ?_
  rw [notMem_support_iff.mp hm, star_zero, mul_zero, zero_mul]

/-- The Fischer form summed over the intersection of the supports of both arguments. -/
theorem fischerInner_eq_sum_inter [DecidableEq σ] (p q : MvPolynomial σ R) :
    fischerInner p q =
      ∑ m ∈ p.support ∩ q.support,
        (∏ i, ((m i).factorial : R)) * star (p.coeff m) * q.coeff m := by
  rw [fischerInner_def]
  refine (Finset.sum_subset Finset.inter_subset_left fun m hm hmq ↦ ?_).symm
  have hq : m ∉ q.support := fun h ↦ hmq (Finset.mem_inter.mpr ⟨hm, h⟩)
  rw [notMem_support_iff.mp hq, mul_zero]

@[simp]
theorem fischerInner_zero_left (q : MvPolynomial σ R) : fischerInner 0 q = 0 := by
  simp [fischerInner_def]

@[simp]
theorem fischerInner_zero_right (p : MvPolynomial σ R) : fischerInner p 0 = 0 := by
  simp [fischerInner_def]

theorem fischerInner_add_left (p₁ p₂ q : MvPolynomial σ R) :
    fischerInner (p₁ + p₂) q = fischerInner p₁ q + fischerInner p₂ q := by
  classical
  have hsub : (p₁ + p₂).support ⊆ p₁.support ∪ p₂.support := support_add
  rw [fischerInner_eq_sum_of_support_subset hsub,
    fischerInner_eq_sum_of_support_subset Finset.subset_union_left,
    fischerInner_eq_sum_of_support_subset Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, star_add]
  ring

theorem fischerInner_add_right (p q₁ q₂ : MvPolynomial σ R) :
    fischerInner p (q₁ + q₂) = fischerInner p q₁ + fischerInner p q₂ := by
  simp only [fischerInner_def, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, mul_add,
    Finset.sum_add_distrib]

theorem fischerInner_sum_left {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ R)
    (q : MvPolynomial σ R) :
    fischerInner (∑ i ∈ s, f i) q = ∑ i ∈ s, fischerInner (f i) q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, fischerInner_add_left, ih]

theorem fischerInner_sum_right {ι : Type*} (s : Finset ι) (p : MvPolynomial σ R)
    (g : ι → MvPolynomial σ R) :
    fischerInner p (∑ i ∈ s, g i) = ∑ i ∈ s, fischerInner p (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, fischerInner_add_right, ih]

theorem fischerInner_C_mul_left (a : R) (p q : MvPolynomial σ R) :
    fischerInner (C a * p) q = star a * fischerInner p q := by
  have hsub : (C a * p).support ⊆ p.support := by
    intro m hm
    rw [mem_support_iff, coeff_C_mul] at hm
    rw [mem_support_iff]
    exact right_ne_zero_of_mul hm
  rw [fischerInner_eq_sum_of_support_subset hsub, fischerInner_def, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  rw [coeff_C_mul, star_mul]
  ring

theorem fischerInner_C_mul_right (a : R) (p q : MvPolynomial σ R) :
    fischerInner p (C a * q) = a * fischerInner p q := by
  rw [fischerInner_def, fischerInner_def, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  rw [coeff_C_mul]
  ring

theorem fischerInner_smul_left (a : R) (p q : MvPolynomial σ R) :
    fischerInner (a • p) q = star a * fischerInner p q := by
  rw [smul_eq_C_mul, fischerInner_C_mul_left]

theorem fischerInner_smul_right (a : R) (p q : MvPolynomial σ R) :
    fischerInner p (a • q) = a * fischerInner p q := by
  rw [smul_eq_C_mul, fischerInner_C_mul_right]

/-- The Fischer form is conjugate-symmetric: `star ⟨p, q⟩_F = ⟨q, p⟩_F`. -/
theorem star_fischerInner (p q : MvPolynomial σ R) :
    star (fischerInner p q) = fischerInner q p := by
  classical
  rw [fischerInner_eq_sum_inter p q, fischerInner_eq_sum_inter q p, Finset.inter_comm, star_sum]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  simp only [star_mul, star_prod, star_natCast, star_star]
  ring

theorem fischerInner_monomial_left (m : σ →₀ ℕ) (a : R) (q : MvPolynomial σ R) :
    fischerInner (monomial m a) q = (∏ i, ((m i).factorial : R)) * star a * q.coeff m := by
  classical
  by_cases ha : a = 0
  · simp [ha]
  · simp [fischerInner_def, support_monomial, ha]

theorem fischerInner_monomial_right (p : MvPolynomial σ R) (m : σ →₀ ℕ) (b : R) :
    fischerInner p (monomial m b) = (∏ i, ((m i).factorial : R)) * star (p.coeff m) * b := by
  apply star_injective
  rw [star_fischerInner, fischerInner_monomial_left]
  simp only [star_mul, star_prod, star_natCast, star_star]
  ring

@[simp]
theorem fischerInner_monomial_monomial [DecidableEq σ] (m n : σ →₀ ℕ) (a b : R) :
    fischerInner (monomial m a) (monomial n b) =
      if m = n then (∏ i, ((m i).factorial : R)) * star a * b else 0 := by
  rw [fischerInner_monomial_left, coeff_monomial]
  by_cases h : m = n
  · subst h; simp
  · simp [h, Ne.symm h]

@[simp]
theorem fischerInner_C_left (a : R) (q : MvPolynomial σ R) :
    fischerInner (C a) q = star a * q.coeff 0 := by
  rw [← monomial_zero', fischerInner_monomial_left]
  simp

@[simp]
theorem fischerInner_C_right (p : MvPolynomial σ R) (b : R) :
    fischerInner p (C b) = star (p.coeff 0) * b := by
  rw [← monomial_zero', fischerInner_monomial_right]
  simp

/-- **Adjointness of multiplication and differentiation** (left):
`⟨X i * p, q⟩_F = ⟨p, ∂ᵢ q⟩_F`. -/
theorem fischerInner_X_mul_left (i : σ) (p q : MvPolynomial σ R) :
    fischerInner (X i * p) q = fischerInner p (pderiv i q) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p₁ p₂ hp₁ hp₂ =>
    rw [mul_add, fischerInner_add_left, fischerInner_add_left, hp₁, hp₂]
  | monomial m a =>
    have hX : X i * monomial m a = monomial (m + Finsupp.single i 1) a := by
      rw [X, monomial_mul_monomial, one_mul, add_comm]
    rw [hX, fischerInner_monomial_left, fischerInner_monomial_left, coeff_pderiv]
    have hprod :
        ∏ j, (((m + Finsupp.single i 1 : σ →₀ ℕ) j).factorial : R) =
          ((m i + 1 : ℕ) : R) * ∏ j, ((m j).factorial : R) := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
        ← Finset.mul_prod_erase _ (fun j ↦ ((m j).factorial : R)) (Finset.mem_univ i)]
      have hrest :
          ∏ j ∈ Finset.univ.erase i, (((m + Finsupp.single i 1 : σ →₀ ℕ) j).factorial : R) =
            ∏ j ∈ Finset.univ.erase i, ((m j).factorial : R) := by
        refine Finset.prod_congr rfl fun j hj ↦ ?_
        rw [Finsupp.add_apply, Finsupp.single_eq_of_ne (Finset.ne_of_mem_erase hj), add_zero]
      rw [hrest, Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorial_succ, Nat.cast_mul,
        mul_assoc]
    rw [hprod]
    push_cast
    ring

theorem fischerInner_mul_X_left (i : σ) (p q : MvPolynomial σ R) :
    fischerInner (p * X i) q = fischerInner p (pderiv i q) := by
  rw [mul_comm, fischerInner_X_mul_left]

/-- **Adjointness of multiplication and differentiation** (right):
`⟨p, X i * q⟩_F = ⟨∂ᵢ p, q⟩_F`. -/
theorem fischerInner_X_mul_right (i : σ) (p q : MvPolynomial σ R) :
    fischerInner p (X i * q) = fischerInner (pderiv i p) q := by
  apply star_injective
  rw [star_fischerInner, fischerInner_X_mul_left, star_fischerInner]

theorem fischerInner_mul_X_right (i : σ) (p q : MvPolynomial σ R) :
    fischerInner p (q * X i) = fischerInner (pderiv i p) q := by
  rw [mul_comm, fischerInner_X_mul_right]

/-- **Adjointness of `r²` and the Laplacian** (left):
`⟨r² * p, q⟩_F = ⟨p, Δ q⟩_F`. -/
theorem fischerInner_normSq_mul_left (p q : MvPolynomial σ R) :
    fischerInner (normSq σ R * p) q = fischerInner p (laplacian q) := by
  rw [normSq_def, Finset.sum_mul, fischerInner_sum_left, laplacian_apply, fischerInner_sum_right]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [sq, mul_assoc, fischerInner_X_mul_left, fischerInner_X_mul_left]

/-- **Adjointness of `r²` and the Laplacian** (right):
`⟨p, r² * q⟩_F = ⟨Δ p, q⟩_F`. -/
theorem fischerInner_normSq_mul_right (p q : MvPolynomial σ R) :
    fischerInner p (normSq σ R * q) = fischerInner (laplacian p) q := by
  apply star_injective
  rw [star_fischerInner, fischerInner_normSq_mul_left, star_fischerInner]

/-- **Unitary invariance of the Fischer form**: if `M * Mᴴ = 1`, then the linear change of
variables `linearSubst M` preserves `fischerInner`. -/
theorem fischerInner_linearSubst_of_mul_conjTranspose_eq_one [DecidableEq σ]
    {M : Matrix σ σ R} (hM : M * Mᴴ = 1) (p q : MvPolynomial σ R) :
    fischerInner (linearSubst M p) (linearSubst M q) = fischerInner p q := by
  have hMki (k i : σ) : ∑ j, M k j * star (M i j) = if k = i then 1 else 0 := by
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] using
      congrFun (congrFun hM k) i
  induction p using MvPolynomial.induction_on generalizing q with
  | C a =>
    simp [← constantCoeff_eq, ← eval_zero, eval_linearSubst]
  | add p₁ p₂ hp₁ hp₂ =>
    simp [map_add, fischerInner_add_left, hp₁, hp₂]
  | mul_X p i hp =>
    rw [map_mul, linearSubst_X, mul_comm, Finset.sum_mul, fischerInner_sum_left,
      fischerInner_mul_X_left]
    calc
      ∑ j, fischerInner (C (M i j) * X j * linearSubst M p) (linearSubst M q)
          = ∑ j, star (M i j) * fischerInner (linearSubst M p)
              (pderiv j (linearSubst M q)) := by
            refine Finset.sum_congr rfl fun j _ ↦ ?_
            rw [mul_assoc, fischerInner_C_mul_left, fischerInner_X_mul_left]
      _ = ∑ j, ∑ k, star (M i j) * M k j *
            fischerInner (linearSubst M p) (linearSubst M (pderiv k q)) := by
            refine Finset.sum_congr rfl fun j _ ↦ ?_
            rw [pderiv_linearSubst, fischerInner_sum_right, Finset.mul_sum]
            refine Finset.sum_congr rfl fun k _ ↦ ?_
            rw [fischerInner_C_mul_right, mul_assoc]
      _ = ∑ k, (∑ j, M k j * star (M i j)) * fischerInner p (pderiv k q) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun k _ ↦ ?_
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun j _ ↦ ?_
            rw [hp, mul_comm (star (M i j)) (M k j)]
      _ = fischerInner p (pderiv i q) := by
            simp [hMki]

end CommSemiring

section CommRing

variable {σ R : Type*} [Fintype σ] [CommRing R] [StarRing R]

theorem fischerInner_neg_left (p q : MvPolynomial σ R) :
    fischerInner (-p) q = -fischerInner p q := by
  simpa using fischerInner_smul_left (-1 : R) p q

theorem fischerInner_neg_right (p q : MvPolynomial σ R) :
    fischerInner p (-q) = -fischerInner p q := by
  simpa using fischerInner_smul_right (-1 : R) p q

theorem fischerInner_sub_left (p₁ p₂ q : MvPolynomial σ R) :
    fischerInner (p₁ - p₂) q = fischerInner p₁ q - fischerInner p₂ q := by
  rw [sub_eq_add_neg, fischerInner_add_left, fischerInner_neg_left, ← sub_eq_add_neg]

theorem fischerInner_sub_right (p q₁ q₂ : MvPolynomial σ R) :
    fischerInner p (q₁ - q₂) = fischerInner p q₁ - fischerInner p q₂ := by
  rw [sub_eq_add_neg, fischerInner_add_right, fischerInner_neg_right, ← sub_eq_add_neg]

end CommRing

section RCLike

variable {σ 𝕜 : Type*} [Fintype σ] [RCLike 𝕜]

/-- The real part of the diagonal Fischer form is the weighted sum of squared coefficient norms. -/
theorem re_fischerInner_self (p : MvPolynomial σ 𝕜) :
    RCLike.re (fischerInner p p) =
      ∑ m ∈ p.support, (∏ i, ((m i).factorial : ℝ)) * ‖p.coeff m‖ ^ 2 := by
  rw [fischerInner_def, map_sum]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  have hterm :
      (∏ i, ((m i).factorial : 𝕜)) * star (p.coeff m) * p.coeff m =
        RCLike.ofReal ((∏ i, ((m i).factorial : ℝ)) * ‖p.coeff m‖ ^ 2) := by
    rw [mul_assoc, RCLike.star_def, RCLike.conj_mul]
    simp
  rw [hterm, RCLike.ofReal_re]

/-- The Fischer form is positive semidefinite over `ℝ` or `ℂ`. -/
theorem re_fischerInner_self_nonneg (p : MvPolynomial σ 𝕜) :
    0 ≤ RCLike.re (fischerInner p p) := by
  rw [re_fischerInner_self]
  exact Finset.sum_nonneg fun m _ ↦
    mul_nonneg (Finset.prod_nonneg fun i _ ↦ Nat.cast_nonneg _) (sq_nonneg _)

/-- The Fischer form is positive definite over `ℝ` or `ℂ`: `⟨p, p⟩_F = 0` exactly when `p = 0`. -/
@[simp]
theorem fischerInner_self_eq_zero_iff (p : MvPolynomial σ 𝕜) :
    fischerInner p p = 0 ↔ p = 0 := by
  refine ⟨fun hp ↦ ?_, fun hp ↦ by simp [hp]⟩
  have hsum : ∑ m ∈ p.support, (∏ i, ((m i).factorial : ℝ)) * ‖p.coeff m‖ ^ 2 = 0 := by
    rw [← re_fischerInner_self, hp, map_zero]
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg fun m _ ↦
    mul_nonneg (Finset.prod_nonneg fun i _ ↦ Nat.cast_nonneg _) (sq_nonneg _)).mp hsum
  ext m
  by_cases hm : m ∈ p.support
  · have hpos : 0 < ∏ i, ((m i).factorial : ℝ) :=
      Finset.prod_pos fun i _ ↦ Nat.cast_pos.mpr (Nat.factorial_pos _)
    have hnorm : ‖p.coeff m‖ ^ 2 = 0 := (mul_eq_zero.mp (hzero m hm)).resolve_left hpos.ne'
    simpa [sq_eq_zero_iff] using hnorm
  · simp [notMem_support_iff.mp hm]

variable (σ 𝕜)

/-- The positive definite Fischer inner product core on `MvPolynomial σ 𝕜`. This core supplies the
normed and inner product space structures without installing a global norm instance on
`MvPolynomial σ 𝕜`. -/
@[instance_reducible]
noncomputable def fischerInnerCore : InnerProductSpace.Core 𝕜 (MvPolynomial σ 𝕜) where
  inner p q := fischerInner p q
  conj_inner_symm p q := by simpa [RCLike.star_def] using star_fischerInner q p
  re_inner_nonneg := re_fischerInner_self_nonneg
  add_left := fischerInner_add_left
  smul_left p q a := by simpa [RCLike.star_def] using fischerInner_smul_left a p q
  definite p := (fischerInner_self_eq_zero_iff p).mp

@[simp]
theorem fischerInnerCore_inner (p q : MvPolynomial σ 𝕜) :
    (fischerInnerCore σ 𝕜).inner p q = fischerInner p q :=
  (rfl)

end RCLike

end MvPolynomial
