/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import TauCeti.RingTheory.MvPolynomial.OrderAt
import Mathlib.Data.Finsupp.Weight
import TauCeti.RingTheory.MvPolynomial.Ideal

/-!
# First jets of multivariate polynomials

For a point `P : σ → R`, the *first jet* of a polynomial `f` at `P` is its value `f(P)` together
with its gradient `(∂ⱼ f (P))ⱼ`. These form the square-zero extension `R ⊕ (σ → R)`, whose
multiplication `(a, v) (b, w) = (a b, a w + b v)` is the Leibniz rule, so taking first jets is an
algebra homomorphism `TauCeti.jetAlgebra P : R[X] →ₐ[R] TrivSqZeroExt R (σ → R)`. It is algebra
evaluation at the point whose `j`-th coordinate is `P j + εⱼ`, the infinitesimals `εⱼ` having
pairwise products zero; the derivatives are Mathlib's `MvPolynomial.pderiv`, with no factorials,
so everything holds in every characteristic. A single directional derivative is read off from
evaluation at a dual-number point by `MvPolynomial.aeval_inl_add_inr`; the first jet records all
partial derivatives at once.

Over any commutative ring `R`, translating to the origin via `MvPolynomial.taylor P` identifies
the kernel of `jetAlgebra P` with `(ker (eval P))²` for every variable type `σ`
(`TauCeti.ker_jetAlgebra`). When `σ` is finite, `jetAlgebra P` is already surjective on
polynomials of total degree at most `1` (`TauCeti.exists_totalDegree_le_one_jetAlgebra_eq`,
`TauCeti.jetAlgebra_surjective`). Over a commutative ring, points differing by a unit in some
coordinate (in particular, distinct points over a field) have comaximal evaluation ideals and
squared evaluation ideals.

## Main definitions

* `TauCeti.jetAlgebra P`: the first jet at `P`, as an algebra homomorphism to
  `TrivSqZeroExt R (σ → R)`.

## Main results

* `TauCeti.fst_jetAlgebra`, `TauCeti.snd_jetAlgebra_apply`: the first jet consists of the value
  and the partial derivatives at `P`.
* `TauCeti.sub_sum_mem_ker_eval_sq`: the first-order Taylor expansion modulo `𝔪_P²`.
* `TauCeti.ker_eval_eq_map_taylor_neg`, `TauCeti.mem_pow_ker_eval_iff`: Taylor-shift
  characterization of point ideals and their powers.
* `TauCeti.exists_totalDegree_le_one_jetAlgebra_eq`, `TauCeti.jetAlgebra_surjective`,
  `TauCeti.ker_jetAlgebra`: surjectivity of the first jet and its kernel `𝔪_P²` in arbitrary
  characteristic and for arbitrary variable types.
* `TauCeti.isCoprime_ker_eval_of_exists_isUnit_sub`,
  `TauCeti.isCoprime_ker_eval_sq_of_exists_isUnit_sub`, `TauCeti.isCoprime_ker_eval`,
  `TauCeti.isCoprime_ker_eval_sq`: coprimality of evaluation ideals and their squares.

## References

* J.-M. Couveignes, *Enumerating number fields*, Ann. of Math. 192 (2020), 487–497, §3.
* M. C. Brambilla and G. Ottaviani, *On the Alexander–Hirschowitz theorem*,
  arXiv:math/0701409, §2, Proposition 2.1.
-/

public section

namespace TauCeti

open MvPolynomial TrivSqZeroExt

variable {σ : Type*}

section PointIdeal

variable {R : Type*} [CommRing R]

/-- `Xⱼ - Pⱼ` vanishes at `P`. -/
theorem X_sub_C_mem_ker_eval (P : σ → R) (j : σ) : X j - C (P j) ∈ RingHom.ker (eval P) := by
  simp [RingHom.mem_ker]

/-- The first-order part `∑ⱼ ∂ⱼ f (P) (Xⱼ - Pⱼ)` of the expansion of `f` at `P` after a polynomial
`p * Xᵢ`: it is `Pᵢ` times that of `p`, plus `p(P) (Xᵢ - Pᵢ)`. -/
private theorem sum_pderiv_mul_X [Fintype σ] (P : σ → R) (p : MvPolynomial σ R) (i : σ) :
    ∑ j, C (eval P (pderiv j (p * X i))) * (X j - C (P j)) =
      C (eval P p) * (X i - C (P i)) +
        C (P i) * ∑ j, C (eval P (pderiv j p)) * (X j - C (P j)) := by
  classical
  simp only [Derivation.leibniz, pderiv_X, smul_eq_mul, map_add, map_mul, eval_X, add_mul,
    Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  · rw [Fintype.sum_eq_single i fun j hj ↦ by simp [hj.symm]]
    simp
  · exact Finset.sum_congr rfl fun j _ ↦ by ring

/-- **First-order Taylor expansion.** A polynomial agrees with its first-order Taylor polynomial
`f(P) + ∑ⱼ ∂ⱼ f (P) (Xⱼ - Pⱼ)` at `P` modulo the square of the ideal of `P`. -/
theorem sub_sum_mem_ker_eval_sq [Fintype σ] (P : σ → R) (f : MvPolynomial σ R) :
    f - C (eval P f) - ∑ j, C (eval P (pderiv j f)) * (X j - C (P j)) ∈
      RingHom.ker (eval P) ^ 2 := by
  rw [sq]
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    convert add_mem hp hq using 1
    simp only [map_add, Finset.sum_add_distrib, add_mul]
    ring
  | mul_X p i hp =>
    -- The remainder for `p * Xᵢ` is the remainder for `p` times `Xᵢ`, plus the first-order part
    -- of `p` times `Xᵢ - Pᵢ`, which lies in `𝔪_P * 𝔪_P`.
    have key : p * X i - C (eval P (p * X i)) -
        ∑ j, C (eval P (pderiv j (p * X i))) * (X j - C (P j)) =
        (p - C (eval P p) - ∑ j, C (eval P (pderiv j p)) * (X j - C (P j))) * X i +
          (∑ j, C (eval P (pderiv j p)) * (X j - C (P j))) * (X i - C (P i)) := by
      rw [sum_pderiv_mul_X, eval_mul, eval_X, map_mul]
      ring
    rw [key]
    exact add_mem (Ideal.mul_mem_right _ _ hp) <| Ideal.mul_mem_mul
      (sum_mem fun j _ ↦ Ideal.mul_mem_left _ _ (X_sub_C_mem_ker_eval P j))
      (X_sub_C_mem_ker_eval P i)

/-- The evaluation ideal at `P` is the image of `idealOfVars σ R` under the inverse Taylor shift
`taylor (-P)`. -/
theorem ker_eval_eq_map_taylor_neg (P : σ → R) :
    RingHom.ker (eval P) = (idealOfVars σ R).map (taylor (-P)) := by
  rw [map_taylor_eq_comap_taylor_neg, neg_neg]
  ext f
  simp [← ker_constantCoeff, RingHom.mem_ker]

/-- A polynomial lies in `(RingHom.ker (eval P)) ^ k` if and only if its Taylor shift at `P` lies
in `(idealOfVars σ R) ^ k`. -/
theorem mem_pow_ker_eval_iff (P : σ → R) (k : ℕ) (f : MvPolynomial σ R) :
    f ∈ RingHom.ker (eval P) ^ k ↔ taylor P f ∈ idealOfVars σ R ^ k := by
  rw [ker_eval_eq_map_taylor_neg, ← Ideal.map_pow, map_taylor_eq_comap_taylor_neg, neg_neg,
    Ideal.mem_comap]

/-- If two points `P, Q : σ → R` differ by a unit in some coordinate, their evaluation ideals are
comaximal. -/
theorem isCoprime_ker_eval_of_exists_isUnit_sub {P Q : σ → R} (h : ∃ j, IsUnit (P j - Q j)) :
    IsCoprime (RingHom.ker (eval P)) (RingHom.ker (eval Q)) := by
  obtain ⟨j, u, hu⟩ := h
  rw [Ideal.isCoprime_iff_sup_eq]
  refine Ideal.eq_top_of_isUnit_mem _ (x := C (P j - Q j)) ?_ (hu ▸ u.isUnit.map C)
  have hsub : C (P j - Q j) = (X j - C (Q j)) - (X j - C (P j)) := by
    simp [map_sub]
  rw [hsub]
  exact Ideal.sub_mem _ (Ideal.mem_sup_right (X_sub_C_mem_ker_eval Q j))
    (Ideal.mem_sup_left (X_sub_C_mem_ker_eval P j))

/-- If two points `P, Q : σ → R` differ by a unit in some coordinate, the squares of their
evaluation ideals are comaximal. -/
theorem isCoprime_ker_eval_sq_of_exists_isUnit_sub {P Q : σ → R} (h : ∃ j, IsUnit (P j - Q j)) :
    IsCoprime (RingHom.ker (eval P) ^ 2) (RingHom.ker (eval Q) ^ 2) :=
  (isCoprime_ker_eval_of_exists_isUnit_sub h).pow

end PointIdeal

section Field

variable {k : Type*} [Field k]

/-- Over a field, the ideals of two distinct points are coprime. -/
theorem isCoprime_ker_eval {P Q : σ → k} (h : P ≠ Q) :
    IsCoprime (RingHom.ker (eval P)) (RingHom.ker (eval Q)) := by
  obtain ⟨j, hj⟩ := Function.ne_iff.1 h
  exact isCoprime_ker_eval_of_exists_isUnit_sub ⟨j, (sub_ne_zero.2 hj).isUnit⟩

/-- Over a field, the squares of the ideals of two distinct points are coprime. -/
theorem isCoprime_ker_eval_sq {P Q : σ → k} (h : P ≠ Q) :
    IsCoprime (RingHom.ker (eval P) ^ 2) (RingHom.ker (eval Q) ^ 2) :=
  (isCoprime_ker_eval h).pow

end Field

section JetAlgebra

variable {R : Type*} [CommSemiring R] [DecidableEq σ]

/-- The first jet of a polynomial at a point `P`: algebra evaluation at the point of
`TrivSqZeroExt R (σ → R)` whose `j`-th coordinate is `P j` plus the `j`-th infinitesimal
coordinate. Its value part is `f(P)` (`TauCeti.fst_jetAlgebra`) and its square-zero part is the
gradient `(∂ⱼ f (P))ⱼ` (`TauCeti.snd_jetAlgebra_apply`). -/
noncomputable def jetAlgebra (P : σ → R) : MvPolynomial σ R →ₐ[R] TrivSqZeroExt R (σ → R) :=
  aeval fun j ↦ inl (P j) + inr (Pi.single j 1)

theorem jetAlgebra_def (P : σ → R) :
    jetAlgebra P = aeval fun j ↦ inl (P j) + inr (Pi.single j 1) :=
  (rfl)

@[simp]
theorem jetAlgebra_X (P : σ → R) (j : σ) :
    jetAlgebra P (X j) = inl (P j) + inr (Pi.single j 1) :=
  aeval_X _ j

theorem jetAlgebra_C (P : σ → R) (a : R) : jetAlgebra P (C a) = inl a :=
  (jetAlgebra P).commutes a

/-- The value part of the first jet of `f` at `P` is `f(P)`. -/
@[simp]
theorem fst_jetAlgebra (P : σ → R) (f : MvPolynomial σ R) : (jetAlgebra P f).fst = eval P f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [algebraMap_eq_inl]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

/-- The square-zero part of the first jet of `f` at `P` is the gradient of `f` at `P`. -/
@[simp]
theorem snd_jetAlgebra_apply (P : σ → R) (f : MvPolynomial σ R) (j : σ) :
    (jetAlgebra P f).snd j = eval P (pderiv j f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [algebraMap_eq_inl]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    simp [hp, Pi.single_apply, Derivation.leibniz, pderiv_X, eq_comm (a := j)]
    split_ifs <;> simp

/-- The first jet of `f` at `P` is its value plus its gradient at `P`. -/
theorem jetAlgebra_apply (P : σ → R) (f : MvPolynomial σ R) :
    jetAlgebra P f = inl (eval P f) + inr fun j ↦ eval P (pderiv j f) := by
  ext <;> simp

/-- A polynomial has first jet zero at `P` exactly when its value and all its first partial
derivatives vanish at `P`. -/
theorem jetAlgebra_eq_zero_iff (P : σ → R) (f : MvPolynomial σ R) :
    jetAlgebra P f = 0 ↔ eval P f = 0 ∧ ∀ j, eval P (pderiv j f) = 0 := by
  simp [TrivSqZeroExt.ext_iff, funext_iff]

variable {R : Type*} [CommRing R]

/-- Translating `f` to the origin by `taylor P` turns the first jet at `P` into the first jet at
`0`. -/
@[simp]
theorem jetAlgebra_zero_taylor (P : σ → R) (f : MvPolynomial σ R) :
    jetAlgebra 0 (taylor P f) = jetAlgebra P f := by
  ext <;> simp [eval_zero]

/-- In finitely many variables over a commutative ring, every first-jet datum at `P` is realized by
a polynomial of total degree at most `1`. -/
theorem exists_totalDegree_le_one_jetAlgebra_eq [Finite σ] (P : σ → R)
    (x : TrivSqZeroExt R (σ → R)) :
    ∃ f : MvPolynomial σ R, f.totalDegree ≤ 1 ∧ jetAlgebra P f = x := by
  cases nonempty_fintype σ
  refine ⟨C x.fst + ∑ j, C (x.snd j) * (X j - C (P j)), ?_, ?_⟩
  · refine (totalDegree_add _ _).trans (max_le (by simp) ?_)
    refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun j _ ↦ ?_)
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add]
    exact (totalDegree_sub _ _).trans
      (max_le ((totalDegree_monomial_le (Finsupp.single j 1) (1 : R)).trans_eq (by simp))
        (by simp))
  · rw [jetAlgebra_apply]
    ext i
    · simp
    · simp [Pi.single_apply]

/-- Over a commutative ring, every value and gradient at a point is the first jet of a
polynomial: `a + ∑ⱼ vⱼ (Xⱼ - Pⱼ)` has value `a` and gradient `v` at `P`. -/
theorem jetAlgebra_surjective [Finite σ] (P : σ → R) : Function.Surjective (jetAlgebra P) :=
  fun x ↦ let ⟨f, _, hf⟩ := exists_totalDegree_le_one_jetAlgebra_eq P x; ⟨f, hf⟩

/-- The kernel of the first jet at `P` is the square of the ideal of `P`: a polynomial lies in
`𝔪_P²` exactly when its value and first partial derivatives vanish at `P`, in every characteristic
and for any variable type `σ`. -/
theorem ker_jetAlgebra (P : σ → R) :
    RingHom.ker (jetAlgebra P) = RingHom.ker (eval P) ^ 2 := by
  ext f
  rw [RingHom.mem_ker, jetAlgebra_eq_zero_iff, mem_pow_ker_eval_iff, mem_pow_idealOfVars_iff']
  constructor
  · rintro ⟨h0, h1⟩ e he
    have hdeg : e.degree = 0 ∨ e.degree = 1 := by omega
    rcases hdeg with hd | hd
    · rw [Finsupp.degree_eq_zero_iff] at hd
      rw [hd, ← constantCoeff_eq, constantCoeff_taylor, h0]
    · have he1 : e ∈ Set.range (fun a : σ ↦ Finsupp.single a 1) := by
        rw [Finsupp.range_single_one]
        exact hd
      obtain ⟨j, rfl⟩ := he1
      rw [coeff_single_one_taylor, h1 j]
  · intro h
    refine ⟨?_, fun j ↦ ?_⟩
    · simpa [← constantCoeff_eq, constantCoeff_taylor] using h 0 (by simp)
    · simpa [coeff_single_one_taylor] using h (Finsupp.single j 1) (by simp)

end JetAlgebra

end TauCeti
