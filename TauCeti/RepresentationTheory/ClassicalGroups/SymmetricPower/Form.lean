/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.UnitaryGroup
public import TauCeti.RingTheory.MvPolynomial.BinaryMonomial
public import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Algebra.MvPolynomial.Coeff
import Mathlib.Algebra.MvPolynomial.Funext
import TauCeti.RingTheory.MvPolynomial.Polarization

/-!
# The invariant Hermitian form on forms of degree `d`

Over `𝕜 = ℝ` or `ℂ`, the forms of degree `d` in the variables `X i`, `i ∈ σ`, carry the Hermitian
form `TauCeti.polynomialForm d` (the Bombieri–Weyl, or Kostlan, inner product) for which the
monomials are orthogonal and `X ^ α` has squared norm `1 / multinomial α`:

`⟨p, q⟩_d = ∑_{|α| = d} conj (p_α) q_α / multinomial α`.

It is conjugate-linear in the first variable. On all polynomials it only reads the coefficients
of degree `d`, so it is positive definite on the forms of degree `d` and vanishes on the other
homogeneous components. In two variables, with `x = X 0` and `y = X 1`, the binary monomials
`e_i^d = x ^ (d - i) * y ^ i` (`TauCeti.polynomialMonomial`) are orthogonal with
`⟨e_i^d, e_i^d⟩_d = 1 / choose d i`.

The weights are chosen so that `d`-th powers of linear forms are reproducing kernels: for the
linear form `ℓ_v = ∑ i, v i • X i`,

`⟨ℓ_v ^ d, q⟩_d = q (conj v)`

for every form `q` of degree `d`. Since these powers span the forms of degree `d`
(`TauCeti.MvPolynomial.span_sum_smul_X_pow_eq_homogeneousSubmodule`), and the substitution of
standard vectors `TauCeti.polynomialAction g` sends `ℓ_v` to `ℓ_{g v}`, the form is
**contravariant**: the adjoint of the substitution by any matrix `g` is the substitution by its
conjugate transpose. In particular the form is invariant under the unitary group `U(σ)`, so for
`σ = Fin 2` it is an invariant Hermitian form on the polynomial model of the representations of
`U(2)` and `SU(2)`.

## Main definitions

* `TauCeti.polynomialForm`: the invariant Hermitian form on forms of degree `d`.

## Main results

* `TauCeti.polynomialForm_monomial_monomial`, `TauCeti.polynomialForm_polynomialMonomial`: the
  monomials are orthogonal, with the weights above.
* `TauCeti.isSymm_polynomialForm`, `TauCeti.polynomialForm_self_pos`: the form is Hermitian and
  positive definite on the forms of degree `d`.
* `TauCeti.polynomialForm_sum_smul_X_pow`: the powers of linear forms are reproducing kernels.
* `TauCeti.polynomialForm_polynomialAction_left`: contravariance.
* `TauCeti.polynomialForm_polynomialAction_polynomialAction`: invariance under unitary matrices.

## References

* E. Kostlan, *On the distribution of roots of random polynomials*, in *From Topology to
  Computation: Proceedings of the Smalefest*, Springer (1993), 419–431.
* P. Bürgisser and F. Cucker, *Condition: The Geometry of Numerical Algorithms*, Grundlehren 349,
  Springer (2013), §16.1.
* P. Etingof, *Lie Groups and Lie Algebras*, arXiv:2201.09397v5, §11.4, p. 63: the polynomial
  model of the representations of `SL₂`.
-/

public section

open MvPolynomial Matrix
open scoped ComplexOrder

namespace TauCeti

variable {σ 𝕜 : Type*} [Fintype σ] [DecidableEq σ] [RCLike 𝕜]

/-- **The invariant Hermitian form on forms of degree `d`**:
`⟨p, q⟩_d = ∑_{|α| = d} conj (p_α) q_α / multinomial α`, conjugate-linear in `p`. It only reads
the coefficients of degree `d`. Its weights make the `d`-th powers of linear forms reproducing
kernels (`TauCeti.polynomialForm_sum_smul_X_pow`), which makes it invariant under unitary changes
of variables (`TauCeti.polynomialForm_polynomialAction_polynomialAction`). -/
noncomputable def polynomialForm (d : ℕ) : MvPolynomial σ 𝕜 →ₗ⋆[𝕜] MvPolynomial σ 𝕜 →ₗ[𝕜] 𝕜 :=
  LinearMap.mk₂'ₛₗ (starRingEnd 𝕜) (RingHom.id 𝕜)
    (fun p q ↦ ∑ α ∈ Finset.univ.finsuppAntidiag d, star (p.coeff α) * q.coeff α / α.multinomial)
    (fun p p' q ↦ by simp [Finset.sum_add_distrib, add_mul, add_div])
    (fun c p q ↦ by simp [Finset.mul_sum, mul_assoc, mul_div_assoc])
    (fun p q q' ↦ by simp [Finset.sum_add_distrib, mul_add, add_div])
    (fun c p q ↦ by simp [Finset.mul_sum, mul_left_comm, mul_div_assoc])

/-- The value of the invariant form, as a sum over the exponents of degree `d`. -/
theorem polynomialForm_apply (d : ℕ) (p q : MvPolynomial σ 𝕜) :
    polynomialForm d p q =
      ∑ α ∈ Finset.univ.finsuppAntidiag d, star (p.coeff α) * q.coeff α / α.multinomial :=
  (rfl)

/-- The monomials are orthogonal for the invariant form, and `X ^ α` has squared norm
`1 / multinomial α` when `α` has degree `d`. -/
@[simp]
theorem polynomialForm_monomial_monomial (d : ℕ) (α β : σ →₀ ℕ) (a b : 𝕜) :
    polynomialForm d (monomial α a) (monomial β b) =
      if α = β ∧ α.degree = d then star a * b / α.multinomial else 0 := by
  rw [polynomialForm_apply]
  by_cases hαβ : α = β
  · subst hαβ
    simp [coeff_monomial, apply_ite star, ite_mul, ite_div, Finset.sum_ite_eq,
      Finsupp.degree_eq_sum]
  · simp only [hαβ, false_and, ↓reduceIte]
    refine Finset.sum_eq_zero fun γ _ ↦ ?_
    by_cases hγ : α = γ
    · subst hγ
      simp [coeff_monomial, Ne.symm hαβ]
    · simp [coeff_monomial, hγ]

/-- The invariant form only reads the homogeneous component of degree `d` of its first
argument. -/
@[simp]
theorem polynomialForm_homogeneousComponent_left (d : ℕ) (p q : MvPolynomial σ 𝕜) :
    polynomialForm d (homogeneousComponent d p) q = polynomialForm d p q := by
  simp only [polynomialForm_apply, coeff_homogeneousComponent]
  exact Finset.sum_congr rfl fun α hα ↦ by simp_all [Finsupp.degree_eq_sum]

/-- The invariant form only reads the homogeneous component of degree `d` of its second
argument. -/
@[simp]
theorem polynomialForm_homogeneousComponent_right (d : ℕ) (p q : MvPolynomial σ 𝕜) :
    polynomialForm d p (homogeneousComponent d q) = polynomialForm d p q := by
  simp only [polynomialForm_apply, coeff_homogeneousComponent]
  exact Finset.sum_congr rfl fun α hα ↦ by simp_all [Finsupp.degree_eq_sum]

/-- The invariant form is Hermitian. -/
theorem isSymm_polynomialForm (d : ℕ) : (polynomialForm (σ := σ) (𝕜 := 𝕜) d).IsSymm where
  eq p q := by simp [polynomialForm_apply, mul_comm]

/-- The invariant form is positive semidefinite. -/
theorem polynomialForm_self_nonneg (d : ℕ) (p : MvPolynomial σ 𝕜) : 0 ≤ polynomialForm d p p := by
  rw [polynomialForm_apply]
  exact Finset.sum_nonneg fun α _ ↦ div_nonneg (star_mul_self_nonneg _) (Nat.cast_nonneg _)

/-- The invariant form is positive definite on the forms of degree `d`. -/
theorem polynomialForm_self_pos {d : ℕ} {p : MvPolynomial σ 𝕜} (hp : p.IsHomogeneous d)
    (h : p ≠ 0) : 0 < polynomialForm d p p := by
  obtain ⟨α, hα⟩ := exists_coeff_ne_zero h
  rw [polynomialForm_apply]
  refine Finset.sum_pos' (fun β _ ↦ div_nonneg (star_mul_self_nonneg _) (Nat.cast_nonneg _))
    ⟨α, ?_, div_pos ?_ ?_⟩
  · refine Finset.mem_finsuppAntidiag.mpr ⟨?_, Finset.subset_univ _⟩
    rw [← Finsupp.degree_eq_sum, Finsupp.degree_eq_weight_one]
    exact hp hα
  · rw [RCLike.star_def, RCLike.conj_mul]
    exact_mod_cast pow_pos (norm_pos_iff.mpr hα) 2
  · exact_mod_cast (Finsupp.multinomial_eq α ▸ Nat.multinomial_pos _ _)

/-- **The reproducing property** for forms of degree `d`: pairing with the `d`-th power of the
linear form `∑ i, v i • X i` evaluates at the conjugate point `star v`. -/
theorem polynomialForm_sum_smul_X_pow_of_isHomogeneous (v : σ → 𝕜) {d : ℕ}
    {q : MvPolynomial σ 𝕜} (hq : q.IsHomogeneous d) :
    polynomialForm d ((∑ i, v i • X i : MvPolynomial σ 𝕜) ^ d) q = eval (star v) q := by
  rw [polynomialForm_apply, ← aeval_eq_eval, hq.aeval_eq_sum_finsuppAntidiag]
  refine Finset.sum_congr rfl fun α hα ↦ ?_
  have hdeg : α.sum (fun _ m ↦ m) = d := by
    simpa [Finsupp.sum_fintype] using (Finset.mem_finsuppAntidiag.mp hα).1
  have hmult : (α.multinomial : 𝕜) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Finsupp.multinomial_eq α ▸ Nat.multinomial_pos _ _).ne'
  simp only [coeff_linearCombination_X_pow_of_fintype, hdeg, ↓reduceIte,
    Finsupp.prod_fintype _ _ fun i ↦ pow_zero (v i), star_mul', star_natCast, star_prod,
    star_pow, Pi.star_apply, Algebra.algebraMap_self, RingHom.id_apply]
  field_simp

/-- **The reproducing property**: pairing with the `d`-th power of the linear form
`∑ i, v i • X i` evaluates the homogeneous component of degree `d` at the conjugate point
`star v`. -/
theorem polynomialForm_sum_smul_X_pow (v : σ → 𝕜) (d : ℕ) (q : MvPolynomial σ 𝕜) :
    polynomialForm d ((∑ i, v i • X i : MvPolynomial σ 𝕜) ^ d) q =
      eval (star v) (homogeneousComponent d q) := by
  rw [← polynomialForm_homogeneousComponent_right,
    polynomialForm_sum_smul_X_pow_of_isHomogeneous v (homogeneousComponent_isHomogeneous d q)]

/-- **Contravariance of the invariant form.** The adjoint of the substitution of standard vectors
by a matrix `g` is the substitution by its conjugate transpose `gᴴ`. -/
theorem polynomialForm_polynomialAction_left (g : Matrix σ σ 𝕜) (d : ℕ)
    (p q : MvPolynomial σ 𝕜) :
    polynomialForm d (polynomialAction g p) q = polynomialForm d p (polynomialAction gᴴ q) := by
  have : Infinite 𝕜 := Infinite.of_injective _ (Nat.cast_injective (R := 𝕜))
  rw [← polynomialForm_homogeneousComponent_left, homogeneousComponent_polynomialAction,
    ← polynomialForm_homogeneousComponent_left d p]
  have hp : homogeneousComponent d p ∈ Submodule.span 𝕜
      ((fun v : σ → 𝕜 ↦ (∑ i, v i • X i : MvPolynomial σ 𝕜) ^ d) '' Set.univ) := by
    rw [MvPolynomial.span_sum_smul_X_pow_eq_homogeneousSubmodule _
      (fun r hr ↦ MvPolynomial.funext fun v ↦ by simpa using hr v trivial)]
    exact (mem_homogeneousSubmodule d _).mpr (homogeneousComponent_isHomogeneous d p)
  generalize homogeneousComponent d p = r at hp ⊢
  induction hp using Submodule.span_induction with
  | mem r hr =>
    obtain ⟨v, -, rfl⟩ := hr
    have hv : polynomialAction g (∑ i, v i • X i) = ∑ i, (g *ᵥ v) i • X i := by
      simpa only [smul_eq_C_mul] using polynomialAction_sum_C_mul_X g v
    rw [map_pow, hv, polynomialForm_sum_smul_X_pow, polynomialForm_sum_smul_X_pow,
      homogeneousComponent_polynomialAction, eval_polynomialAction, star_mulVec,
      mulVec_transpose]
  | zero => simp
  | add r s _ _ hr hs => simp [hr, hs]
  | smul c r _ hr => simp [hr]

/-- **Unitary invariance of the invariant form.** Substitution of standard vectors by a unitary
matrix preserves the invariant form. -/
theorem polynomialForm_polynomialAction_polynomialAction {g : Matrix σ σ 𝕜}
    (hg : g ∈ unitaryGroup σ 𝕜) (d : ℕ) (p q : MvPolynomial σ 𝕜) :
    polynomialForm d (polynomialAction g p) (polynomialAction g q) = polynomialForm d p q := by
  rw [polynomialForm_polynomialAction_left, ← polynomialAction_mul_apply, ← star_eq_conjTranspose,
    mem_unitaryGroup_iff'.mp hg, polynomialAction_one, AlgHom.id_apply]

/-! ### Binary forms -/

/-- The binary monomials `e_i^d = x ^ (d - i) * y ^ i` are orthogonal for the invariant form,
with `⟨e_i^d, e_i^d⟩_d = 1 / choose d i`. -/
@[simp]
theorem polynomialForm_polynomialMonomial (d i j : ℕ) :
    polynomialForm d (polynomialMonomial 𝕜 d i) (polynomialMonomial 𝕜 d j) =
      if i = j ∧ i ≤ d then ((d.choose i : 𝕜))⁻¹ else 0 := by
  by_cases hi : i ≤ d
  · by_cases hj : j ≤ d
    · have hiff : Finsupp.single (0 : Fin 2) (d - i) + Finsupp.single 1 i =
          Finsupp.single 0 (d - j) + Finsupp.single 1 j ↔ i = j :=
        ⟨fun h ↦ by simpa using DFunLike.congr_fun h 1, fun h ↦ h ▸ rfl⟩
      rw [polynomialMonomial_eq_monomial hi, polynomialMonomial_eq_monomial hj,
        polynomialForm_monomial_monomial]
      have hdeg : (Finsupp.single (0 : Fin 2) (d - i) + Finsupp.single 1 i).degree = d := by
        rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]
        simp [hi]
      have hmult : (Finsupp.single (0 : Fin 2) (d - i) + Finsupp.single 1 i).multinomial =
          d.choose i := by
        rw [Finsupp.multinomial_eq_of_support_subset (Finset.subset_univ _), Finset.univ_fin2,
          Nat.binomial_eq_choose Fin.zero_ne_one]
        simp [Nat.sub_add_cancel hi, Nat.choose_symm hi]
      simp only [hiff, hdeg, hi, and_true, hmult, star_one, mul_one,
        one_div]
    · have hij : i ≠ j := by omega
      simp [polynomialMonomial_of_lt (not_le.mp hj), hij]
  · simp [polynomialMonomial_of_lt (not_le.mp hi), hi]

end TauCeti
