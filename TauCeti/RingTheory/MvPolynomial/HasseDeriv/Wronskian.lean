/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharZero.Infinite
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import TauCeti.RingTheory.MvPolynomial.Kronecker
public import TauCeti.RingTheory.Polynomial.HasseWronskian

/-!
# Generalized Wronskians of multivariate polynomials

For a family `f : Fin m → MvPolynomial σ R` and a family of multi-indices `D : Fin m → σ →₀ ℕ`,
the *generalized Wronskian* `W_D(f)` is the determinant `det (∂^(D k) f_l)` of the `m × m`
matrix whose `(k, l)` entry is the `D k`-th Hasse derivative of `f_l`. The row family is
*admissible* when `|D k| ≤ k` for every `k`; admissibility is a hypothesis of the theorems, not
part of the definition. With the rows `D k = k eᵢ` and a family of polynomials in the single
variable `Xᵢ`, the generalized Wronskian is the one-variable Hasse Wronskian
`Polynomial.hasseWronskian`.

Over an integral domain a linearly dependent family has vanishing generalized Wronskians for every
row family. Over a field of characteristic zero the converse holds in the following form: a
linearly independent family has a nonzero generalized Wronskian with admissible rows. Generalized
Wronskians are the auxiliary determinants of Roth's lemma, which bounds the index of a polynomial
in several variables at a point; admissibility controls their degrees.

## Main definitions

* `MvPolynomial.genWronskian D f`: the determinant of the Hasse derivatives `∂^(D k) f_l`.

## Main results

* `MvPolynomial.map_genWronskian`, `MvPolynomial.eval_genWronskian`: generalized Wronskians
  commute with maps of coefficient rings and with evaluation.
* `MvPolynomial.genWronskian_single_toMvPolynomial`: in a single variable, with rows `k eᵢ`,
  the generalized Wronskian is the Hasse Wronskian.
* `MvPolynomial.genWronskian_eq_zero_of_not_linearIndependent`: over an integral domain,
  dependent families have vanishing generalized Wronskians.
* `MvPolynomial.det_hasseDeriv_sum_mul_toMvPolynomial`: for `P = ∑ₖ fₖ · gₖ(Xᵢ)` with the `fₖ`
  free of `Xᵢ` and rows `D k` that do not differentiate in `Xᵢ` (`D k i = 0` for every `k`), the
  determinant `det (∂^(D k + l eᵢ) P)` is the product of the generalized Wronskian of the `fₖ`
  and the Hasse Wronskian of the `gₖ`.
* `MvPolynomial.linearIndependent_iff_exists_genWronskian_ne_zero`: over a field of
  characteristic zero, a family is linearly independent if and only if some admissible generalized
  Wronskian is nonzero.

## Implementation notes

The nonvanishing direction reduces to one variable. The Kronecker substitution `Xₛ ↦ T ^ eₛ`,
for a weight `e` separating the exponents of the family, preserves linear independence, so the
image family has a nonzero Hasse Wronskian, which survives evaluation at some point `a`.
Translating `T` to `a + U` turns the substitution into `Xₛ ↦ (U + a) ^ eₛ - a ^ eₛ`, whose
images have no constant term. Hence the `k`-th Hasse derivative of an image, evaluated at `a`,
is a linear combination of Hasse derivatives `∂^ν f` of total order `|ν| ≤ k`, evaluated at
`(a ^ eₛ)ₛ`. Expanding the determinant multilinearly in its rows exhibits a nonzero admissible
generalized Wronskian.

## References

* L. Pottmeyer, *Diophantine Approximation*, lecture notes (version of 17 January 2022), §3.3:
  Definition 3.3.5, Theorem 3.3.7 and Lemma 3.3.9.
* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press
  (2006), Proposition 6.3.10, whose proof by Kronecker substitution is followed here.
* The proof plan (separating weights, translated substitution and multilinear expansion of the
  determinant) is adapted from Ralf Stephan's `DiophantineApproximation/GeneralizedWronskian.lean`
  in [`rwst/Subspace-Theorems`](https://github.com/rwst/Subspace-Theorems), commit
  `5cff93ceb4b69b2048473301411763febe96bb3f` (Apache 2.0).
-/

public section

noncomputable section

namespace MvPolynomial

open Matrix Finset Finsupp

variable {R S σ : Type*} [CommRing R] [CommRing S] {m : ℕ}

/-- The generalized Wronskian `W_D(f)` of a family `f : Fin m → MvPolynomial σ R` with respect to
the row family `D : Fin m → σ →₀ ℕ`: the determinant of the matrix whose `(k, l)` entry is the
Hasse derivative `∂^(D k) f_l`. The generalized Wronskian of the empty family is `1`. -/
def genWronskian (D : Fin m → σ →₀ ℕ) (f : Fin m → MvPolynomial σ R) : MvPolynomial σ R :=
  (of fun k l ↦ hasseDeriv (D k) (f l)).det

/-- The generalized Wronskian is the determinant of the matrix of Hasse derivatives
`∂^(D k) f_l`. -/
theorem genWronskian_def (D : Fin m → σ →₀ ℕ) (f : Fin m → MvPolynomial σ R) :
    genWronskian D f = (of fun k l ↦ hasseDeriv (D k) (f l)).det := by
  rw [genWronskian]

/-- The generalized Wronskian of the empty family is `1`. -/
@[simp]
theorem genWronskian_fin_zero (D : Fin 0 → σ →₀ ℕ) (f : Fin 0 → MvPolynomial σ R) :
    genWronskian D f = 1 := by
  rw [genWronskian_def, det_fin_zero]

/-- The generalized Wronskian of a single polynomial `f₀` is `∂^(D 0) f₀`; for the admissible row
`D 0 = 0` it is `f₀`. -/
@[simp]
theorem genWronskian_fin_one (D : Fin 1 → σ →₀ ℕ) (f : Fin 1 → MvPolynomial σ R) :
    genWronskian D f = hasseDeriv (D 0) (f 0) := by
  rw [genWronskian_def, det_fin_one, of_apply]

/-- Generalized Wronskians commute with maps of coefficient rings. -/
@[simp]
theorem map_genWronskian (g : R →+* S) (D : Fin m → σ →₀ ℕ) (f : Fin m → MvPolynomial σ R) :
    map g (genWronskian D f) = genWronskian D fun l ↦ map g (f l) := by
  rw [genWronskian_def, genWronskian_def, RingHom.map_det]
  congr 1
  ext1 k l
  simp [hasseDeriv_map]

/-- Evaluating a generalized Wronskian at `x` gives the determinant of the values of the Hasse
derivatives `∂^(D k) f_l` at `x`. -/
theorem eval_genWronskian (x : σ → R) (D : Fin m → σ →₀ ℕ) (f : Fin m → MvPolynomial σ R) :
    eval x (genWronskian D f) = (of fun k l ↦ eval x (hasseDeriv (D k) (f l))).det := by
  rw [genWronskian_def, RingHom.map_det]
  congr 1

/-- In the single variable `Xᵢ`, with rows `D k = k eᵢ`, the generalized Wronskian is the
one-variable Hasse Wronskian. -/
@[simp]
theorem genWronskian_single_toMvPolynomial (i : σ) (g : Fin m → Polynomial R) :
    genWronskian (fun k ↦ single i (k : ℕ)) (fun l ↦ (g l).toMvPolynomial i) =
      (Polynomial.hasseWronskian g).toMvPolynomial i := by
  rw [genWronskian_def, Polynomial.hasseWronskian_def, AlgHom.map_det]
  congr 1
  ext1 k l
  simp

/-- Over an integral domain, every generalized Wronskian of a linearly dependent family
vanishes. No row admissibility or characteristic assumption is needed. -/
theorem genWronskian_eq_zero_of_not_linearIndependent [IsDomain R] (D : Fin m → σ →₀ ℕ)
    {f : Fin m → MvPolynomial σ R} (hf : ¬LinearIndependent R f) : genWronskian D f = 0 := by
  obtain ⟨c, hc, l, hl⟩ := Fintype.not_linearIndependent_iff.mp hf
  rw [genWronskian_def, ← exists_mulVec_eq_zero_iff]
  refine ⟨fun l ↦ C (c l), fun h ↦ hl (C_injective σ R (by simpa using congr_fun h l)), ?_⟩
  ext1 k
  have hk : ∑ l, hasseDeriv (D k) (f l) * C (c l) = hasseDeriv (D k) (∑ l, c l • f l) := by
    rw [map_sum]
    refine sum_congr rfl fun l _ ↦ ?_
    rw [map_smul, smul_eq_C_mul, mul_comm]
  simpa [mulVec, dotProduct, hc] using hk

/-- **Separation of variables for generalized Wronskians** (Pottmeyer, Lemma 3.3.9). Let
`P = ∑ₖ fₖ · gₖ(Xᵢ)`, where no `fₖ` involves `Xᵢ`, and let the rows `D k` not differentiate in
`Xᵢ`. Then the determinant of the Hasse derivatives `∂^(D k + l eᵢ) P` is the product of the
generalized Wronskian `W_D(f)` and the Hasse Wronskian of the `gₖ`, placed in `Xᵢ`. -/
theorem det_hasseDeriv_sum_mul_toMvPolynomial {i : σ} {D : Fin m → σ →₀ ℕ} (hD : ∀ k, D k i = 0)
    {f : Fin m → MvPolynomial σ R} (hf : ∀ k, i ∉ (f k).vars) (g : Fin m → Polynomial R) :
    (of fun k l : Fin m ↦
        hasseDeriv (D k + single i (l : ℕ)) (∑ j, f j * (g j).toMvPolynomial i)).det =
      genWronskian D f * (Polynomial.hasseWronskian g).toMvPolynomial i := by
  have hM : (of fun k l : Fin m ↦
      hasseDeriv (D k + single i (l : ℕ)) (∑ j, f j * (g j).toMvPolynomial i)) =
        of (fun k j ↦ hasseDeriv (D k) (f j)) *
          (of fun (l : Fin m) j ↦ (Polynomial.hasseDeriv l (g j)).toMvPolynomial i)ᵀ := by
    ext1 k l
    simp [mul_apply, hasseDeriv_add_single_mul_toMvPolynomial (hD k) (hf _)]
  -- The second factor is the Hasse matrix of `g` mapped entrywise by `toMvPolynomial i`.
  have hg : (of fun (l : Fin m) j ↦ (Polynomial.hasseDeriv l (g j)).toMvPolynomial i) =
      (Polynomial.toMvPolynomial i).mapMatrix
        (of fun (l : Fin m) j ↦ Polynomial.hasseDeriv l (g j)) := by
    ext l j
    simp [AlgHom.mapMatrix_apply]
  rw [hM, hg, det_mul, det_transpose, ← AlgHom.map_det, genWronskian_def,
    Polynomial.hasseWronskian_def]

/-! ### The generalized Wronskian criterion -/

/-- Over a field of characteristic zero, a linearly independent family of polynomials has a
nonzero generalized Wronskian with admissible rows `|D k| ≤ k`. -/
theorem exists_genWronskian_ne_zero {K : Type*} [Field K] [CharZero K]
    {f : Fin m → MvPolynomial σ K} (hf : LinearIndependent K f) :
    ∃ D : Fin m → σ →₀ ℕ, (∀ k, (D k).degree ≤ k) ∧ genWronskian D f ≠ 0 := by
  classical
  -- Carry the family to one variable by a Kronecker substitution separating its exponents.
  obtain ⟨e, he⟩ := exists_injOn_weight (univ.biUnion fun l ↦ (f l).support)
  set g : Fin m → Polynomial K := fun l ↦ aeval (fun s ↦ (Polynomial.X : Polynomial K) ^ e s) (f l)
  have hg : LinearIndependent K g := linearIndependent_aeval_X_pow he
    (fun l ν hν ↦ mem_biUnion.mpr ⟨l, mem_univ l, hν⟩) hf
  -- Its Hasse Wronskian is nonzero, hence nonzero at some point `a`.
  obtain ⟨a, ha⟩ : ∃ a, (Polynomial.hasseWronskian g).eval a ≠ 0 := by
    by_contra! h
    exact Polynomial.hasseWronskian_ne_zero_of_linearIndependent hg
      (Polynomial.funext fun a ↦ by simp [h a])
  -- By the chain rule, row `k` of the evaluated Hasse Wronskian matrix is a combination of the
  -- vectors `v ν` of values of `∂^ν f_l`, over the exponents `ν` with `|ν| ≤ k`.
  set b : σ → K := fun s ↦ a ^ e s
  set c : Fin m → (σ →₀ ℕ) → K := fun k ν ↦
    (aeval (fun s ↦ (Polynomial.X + Polynomial.C a) ^ e s - Polynomial.C (a ^ e s))
      (monomial ν (1 : K))).coeff k
  set v : (σ →₀ ℕ) → Fin m → K := fun ν l ↦ eval b (hasseDeriv ν (f l))
  set T : Fin m → Finset (σ →₀ ℕ) := fun k ↦
    (univ.biUnion fun l ↦ (taylor b (f l)).support).filter fun ν ↦ ν.degree ≤ k
  have hrow (k : Fin m) :
      (fun l ↦ (Polynomial.hasseDeriv k (g l)).eval a) = ∑ ν ∈ T k, c k ν • v ν := by
    ext1 l
    rw [Finset.sum_apply, sum_filter_of_ne fun ν _ hν ↦ ?_]
    · exact eval_hasseDeriv_aeval_X_pow e a (f l) k fun ν hν ↦ mem_biUnion.mpr ⟨l, mem_univ l, hν⟩
    · by_contra hk
      exact hν (by
        rw [Pi.smul_apply, smul_eq_mul]
        exact mul_eq_zero_of_left (coeff_aeval_X_add_C_pow_sub_C_eq_zero e a ν (by omega)) _)
  -- Expanding the determinant multilinearly in its rows exhibits an admissible generalized
  -- Wronskian that does not vanish at `b`.
  have hdet : (Polynomial.hasseWronskian g).eval a =
      ∑ p ∈ Fintype.piFinset T, (∏ k, c k (p k)) * eval b (genWronskian p f) := by
    have hM : (Polynomial.evalRingHom a).mapMatrix
        (of fun k l : Fin m ↦ Polynomial.hasseDeriv k (g l)) =
          fun k ↦ ∑ ν ∈ T k, c k ν • v ν := by
      ext k l
      simpa using congr_fun (hrow k) l
    rw [Polynomial.hasseWronskian_def, ← Polynomial.coe_evalRingHom, RingHom.map_det, hM]
    simp only [Matrix.det]
    rw [← AlternatingMap.coe_multilinearMap, MultilinearMap.map_sum_finset]
    refine sum_congr rfl fun p _ ↦ ?_
    rw [MultilinearMap.map_smul_univ, smul_eq_mul, AlternatingMap.coe_multilinearMap,
      eval_genWronskian]
    -- Both sides evaluate `detRowAlternating` on the same rows; `Matrix.of` is the identity.
    simp only [Matrix.det]
    congr 2
  obtain ⟨p, hp, hpne⟩ := exists_ne_zero_of_sum_ne_zero (hdet ▸ ha)
  refine ⟨p, fun k ↦ (mem_filter.mp (Fintype.mem_piFinset.mp hp k)).2,
    fun h0 ↦ right_ne_zero_of_mul hpne (by rw [h0, map_zero])⟩

/-- **The generalized Wronskian criterion.** Over a field of characteristic zero, a family of
multivariate polynomials is linearly independent if and only if some generalized Wronskian with
admissible rows `|D k| ≤ k` is nonzero. -/
theorem linearIndependent_iff_exists_genWronskian_ne_zero {K : Type*} [Field K] [CharZero K]
    {f : Fin m → MvPolynomial σ K} :
    LinearIndependent K f ↔ ∃ D : Fin m → σ →₀ ℕ, (∀ k, (D k).degree ≤ k) ∧ genWronskian D f ≠ 0 :=
  ⟨exists_genWronskian_ne_zero, fun ⟨D, _, hD⟩ ↦
    by_contra fun h ↦ hD (genWronskian_eq_zero_of_not_linearIndependent D h)⟩

example : genWronskian ![0, Finsupp.single 0 1]
    ![X 0, X 1] = -(X 1 : MvPolynomial (Fin 2) ℚ) := by
  simp [genWronskian_def, det_fin_two, hasseDeriv_X, hasseDeriv_zero, Finsupp.single_eq_single_iff]

example : genWronskian ![0, Finsupp.single 0 1]
    ![1, X 0] = (1 : MvPolynomial (Fin 2) ℚ) := by
  simp [genWronskian_def, det_fin_two, hasseDeriv_X, hasseDeriv_zero, hasseDeriv_one]

end MvPolynomial
