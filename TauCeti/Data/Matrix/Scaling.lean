/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: the Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Topology.Instances.Matrix
public import TauCeti.Data.Matrix.BirkhoffContraction
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import TauCeti.Analysis.SpecialFunctions.Log.MulLog
import TauCeti.Data.Finset.Basic

/-!
# The entropy minimiser with prescribed marginals and the Sinkhorn–Knopp theorem

Let `ι` and `κ` be finite types, let `a : ι → ℝ` and `b : κ → ℝ` be the row and the column sums,
and let `S` be the set of the nonnegative matrices `P : ι × κ → ℝ` whose row sums are `a` and
whose column sums are `b`. Against a fixed matrix `K : ι × κ → ℝ`, the relative entropy of `P`
attains a minimum on `S` as soon as `S` is nonempty, and for strictly positive marginals of equal
total mass every minimiser has strictly positive entries.

For a strictly positive `K` the minimiser is a diagonal scaling `P i j = u i * K i j * v j` of `K`
by strictly positive factors. At a minimiser with positive entries the relative entropy is
differentiable along every direction that preserves the marginals, and its derivative vanishes
there; testing against the rectangle directions splits `log (P i j) - log (K i j)` into a function
of the row plus a function of the column. Conversely, Gibbs' inequality and the Pythagorean identity
`relEntropy Q K = relEntropy Q P + relEntropy P K` show that every such scaling with marginals `a`
and `b` is the minimiser. This gives the Sinkhorn–Knopp theorem for a strictly positive kernel:
strictly positive marginals of equal total mass are the row and column sums of a diagonal scaling
of `K`, the scaled matrix is unique, and its factors are unique up to one common scalar.

Nothing here uses the ordinal structure of the row and column types: the results are stated for
arbitrary finite `ι` and `κ`, and the diagonal scaling of a kernel between two enumerated finite
sets is the specialisation of `Matrix.IsDiagonalScaling` to `Fin n` and `Fin m`.

The relative entropy `Matrix.relEntropy P K` below is the formula
`∑ i, ∑ j, (P i j * log (P i j) - P i j * log (K i j))`; for a nonnegative `P` and a strictly
positive `K` it is the relative entropy of `P` against `K`. Existence and positivity of the
minimiser hold for every `K`; strict positivity of `K` is needed only to identify the minimiser with
a diagonal scaling of `K`. A kernel with zero entries constrains the support of a scaling and is
not treated here.

`Matrix.IsDiagonalScaling P K u v` records the shape of the minimiser:
`P i j = u i * K i j * v j` for row factors `u` and column factors `v`, that is a diagonal scaling
of `K`.

The marginals here are arbitrary vectors of equal total mass, not probability distributions, and
the matrices are real: this is the setting of a diagonal scaling of a kernel, where the scaled
matrix has total mass `∑ i, a i` and is compared against the real kernel `K`. A probability-valued
plan with `PMF` marginals is `TauCeti.TransportMatrix`.

## Main definitions

* `Matrix.HasMarginals P a b`: the row sums of `P` are `a` and its column sums are `b`.
* `Matrix.IsDiagonalScaling P K u v`: `P i j = u i * K i j * v j` for all `i` and `j`.
* `Matrix.relEntropy P K`: the sum over `i`, `j` of `P i j * (log (P i j) - log (K i j))`.

## Main results

* `Matrix.exists_relEntropy_minOn`: a minimiser of `Matrix.relEntropy` against `K` among the
  nonnegative matrices with row sums `a` and column sums `b` exists, as soon as there is one such
  matrix.
* `Matrix.exists_relEntropy_minOn_of_pos`: the same, for strictly positive marginals `a` and `b` of
  equal total mass.
* `Matrix.pos_of_relEntropy_minOn`: every such minimiser has strictly positive entries.
* `Matrix.HasMarginals.add_vecMulVec_of_sum_eq_zero`: the row and column sums of a matrix are
  preserved by an outer product of a row weight and a column weight, each of total sum `0`.
* `Matrix.relEntropy_nonneg` and `Matrix.relEntropy_eq_zero_iff`: Gibbs' inequality for matrices
  of equal total mass, with its equality case.
* `Matrix.hasDerivAt_relEntropy_add_smul` and
  `Matrix.sum_sum_mul_log_sub_log_eq_zero_of_relEntropy_minOn`: the derivative of the relative
  entropy along a direction, and the first-order condition at a positive minimiser.
* `Matrix.exists_isDiagonalScaling_of_relEntropy_minOn`: for a strictly positive `K`, every
  minimiser is a diagonal scaling of `K` by strictly positive factors;
  `Matrix.relEntropy_minOn_iff_exists_isDiagonalScaling` is the resulting characterisation.
* `Matrix.IsDiagonalScaling.relEntropy_eq_relEntropy_add`: the Pythagorean identity of the relative
  entropy at a diagonal scaling.
* `Matrix.exists_sinkhorn_scaling`: **the Sinkhorn–Knopp theorem** for a strictly positive kernel.
* `Matrix.IsDiagonalScaling.eq_of_hasMarginals` and
  `Matrix.IsDiagonalScaling.exists_eq_rescale_factors`: the scaled matrix is unique, and its
  factors are unique up to a common scalar.
* `Matrix.IsDiagonalScaling.apply_le_exp_hilbertProjectiveDist_mul`: two diagonal scalings of a
  strictly positive kernel with the same row sums agree entrywise up to the factor `exp d`, where
  `d` is the Hilbert projective distance between their column factors.

## References

* R. Sinkhorn and P. Knopp, *Concerning nonnegative matrices and doubly stochastic matrices*,
  Pacific J. Math. 21 (1967), 343--348.
* I. Csiszár, *I-divergence geometry of probability distributions and minimization problems*,
  Ann. Probab. 3 (1975), 146--158, for the Pythagorean identity of the relative entropy.
* G. Peyré and M. Cuturi, *Computational Optimal Transport*, Found. Trends Mach. Learn. 11 (2019),
  Proposition 4.3, for the characterisation of the entropic minimiser as a diagonal scaling.
-/
public section

open scoped BigOperators

namespace Matrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-! ### Marginals and diagonal scalings -/

/-- `P` has row sums `a` and column sums `b`, that is `(∑ j, P i j) = a i` and
`(∑ i, P i j) = b j` for all `i` and `j`.

This is the two sum equalities only. The nonnegativity of a matrix with these marginals is a
separate hypothesis, as it is in the results below. -/
def HasMarginals (P : Matrix ι κ ℝ) (a : ι → ℝ) (b : κ → ℝ) : Prop :=
  (∀ i, (∑ j, P i j) = a i) ∧ (∀ j, (∑ i, P i j) = b j)

@[simp] theorem hasMarginals_def (P : Matrix ι κ ℝ) (a : ι → ℝ) (b : κ → ℝ) :
    HasMarginals P a b ↔ (∀ i, (∑ j, P i j) = a i) ∧ (∀ j, (∑ i, P i j) = b j) := Iff.rfl

omit [Fintype ι] [Fintype κ] in
/-- `P` is the diagonal scaling of `K` by the row factors `u` and the column factors `v`, that is
`P i j = u i * K i j * v j` for all `i` and `j`. -/
def IsDiagonalScaling (P : Matrix ι κ ℝ) (K : Matrix ι κ ℝ)
    (u : ι → ℝ) (v : κ → ℝ) : Prop :=
  ∀ i j, P i j = u i * K i j * v j

omit [Fintype ι] [Fintype κ] in
@[simp] theorem isDiagonalScaling_def (P K : Matrix ι κ ℝ) (u : ι → ℝ) (v : κ → ℝ) :
    IsDiagonalScaling P K u v ↔ ∀ i j, P i j = u i * K i j * v j := Iff.rfl

/-- The row and column sums of a diagonal scaling are the row and column sums of its factors, so
the stated sums of `u i * K i j * v j` over the columns and over the rows transfer through
`IsDiagonalScaling` to `HasMarginals P a b`. -/
theorem IsDiagonalScaling.hasMarginals {P K : Matrix ι κ ℝ} {u : ι → ℝ} {v : κ → ℝ}
    (h : IsDiagonalScaling P K u v) (a : ι → ℝ) (b : κ → ℝ)
    (ha : ∀ i, (∑ j, u i * K i j * v j) = a i) (hb : ∀ j, (∑ i, u i * K i j * v j) = b j) :
    HasMarginals P a b := by
  have hP : P = fun i j => u i * K i j * v j := funext fun i => funext fun j => h i j
  constructor
  · intro i
    rw [hP]
    exact ha i
  · intro j
    rw [hP]
    exact hb j

omit [Fintype ι] [Fintype κ] in
/-- A diagonal scaling is not unique: rescaling the row factors by `r` and the column factors by
`r ⁻¹`, for a nonzero `r`, leaves the scaled matrix `P` unchanged. -/
theorem IsDiagonalScaling.rescale_factors {P K : Matrix ι κ ℝ} {u : ι → ℝ} {v : κ → ℝ}
    (h : IsDiagonalScaling P K u v) {r : ℝ} (hr : r ≠ 0) :
    IsDiagonalScaling P K (fun i => r * u i) (fun j => r⁻¹ * v j) := by
  have hrr : r * r⁻¹ = 1 := mul_inv_cancel₀ hr
  intro i j
  calc P i j = u i * K i j * v j := h i j
    _ = (u i * K i j * v j) * (r * r⁻¹) := by rw [hrr]; ring
    _ = r * u i * K i j * (r⁻¹ * v j) := by ring

omit [Fintype ι] [Fintype κ] in
/-- A diagonal scaling of a strictly positive `K` by strictly positive factors is strictly
positive. -/
theorem IsDiagonalScaling.pos {P K : Matrix ι κ ℝ} {u : ι → ℝ} {v : κ → ℝ}
    (h : IsDiagonalScaling P K u v) (hK : ∀ i j, 0 < K i j) (hu : ∀ i, 0 < u i)
    (hv : ∀ j, 0 < v j) (i : ι) (j : κ) : 0 < P i j := by
  rw [h i j]
  exact mul_pos (mul_pos (hu i) (hK i j)) (hv j)

omit [Fintype ι] [Fintype κ] in
/-- Transposing a diagonal scaling exchanges the roles of the row and the column factors: if `P` is
the diagonal scaling of `K` by `u` and `v`, then `Pᵀ` is the diagonal scaling of `Kᵀ` by `v` and
`u`. -/
theorem IsDiagonalScaling.transpose {P K : Matrix ι κ ℝ} {u : ι → ℝ} {v : κ → ℝ}
    (h : IsDiagonalScaling P K u v) : IsDiagonalScaling Pᵀ Kᵀ v u := fun j i => by
  rw [transpose_apply, transpose_apply, h i j]
  ring

/-! ### The relative entropy of a matrix against a kernel -/

/-- `Matrix.relEntropy P K` is the real number
`∑ i, ∑ j, (P i j * Real.log (P i j) - P i j * Real.log (K i j))`, with the convention
`0 * log 0 = 0`.

The formula is defined for arbitrary real matrices `P` and `K`. For a nonnegative `P` and a strictly
positive `K` it is the relative entropy of `P` against `K`; the nonnegativity of `P` and the
strict positivity of `K` are hypotheses of the results that use this interpretation, not part of
the definition.

Writing `A = ∑ i j, P i j` and `B = ∑ i j, K i j`, for a nonnegative `P` of positive total mass
and a strictly positive `K` it is `A` times the relative entropy of the probability distributions
`P i j / A` and `K i j / B`, up to the additive constant `A * (log A - log B)`. Two matrices of
equal total mass that differ by that constant are compared the same way by an optimisation against
`K`. -/
noncomputable def relEntropy (P K : Matrix ι κ ℝ) : ℝ :=
  ∑ i, ∑ j, (P i j * Real.log (P i j) - P i j * Real.log (K i j))

@[simp] theorem relEntropy_def (P K : Matrix ι κ ℝ) :
    relEntropy P K = ∑ i, ∑ j, (P i j * Real.log (P i j) - P i j * Real.log (K i j)) :=
  -- `(rfl)` rather than `rfl`: a bare `rfl` proof would demand that `relEntropy` be `@[expose]`,
  -- and this lemma is the supported unfolding interface instead.
  (rfl)

/-- The relative entropy against a fixed matrix is continuous in the matrix it is applied to. -/
theorem continuous_relEntropy (K : Matrix ι κ ℝ) : Continuous (relEntropy · K) := by
  unfold relEntropy
  fun_prop

/-! ### A minimiser of the relative entropy -/

/-- The relative entropy against `K` attains a minimum on the nonnegative matrices with row sums `a`
and column sums `b`, as soon as there is one such matrix.

The set of these matrices is closed, every entry of such a matrix is at most `∑ i, a i`, and the
relative entropy is continuous, so the minimum is attained on a closed subset of a compact box. -/
theorem exists_relEntropy_minOn (K : Matrix ι κ ℝ) (a : ι → ℝ) (b : κ → ℝ)
    (hfeas : ∃ P : Matrix ι κ ℝ, (∀ i j, 0 ≤ P i j) ∧ HasMarginals P a b) :
    ∃ P : Matrix ι κ ℝ, (∀ i j, 0 ≤ P i j) ∧ HasMarginals P a b ∧
      ∀ Q : Matrix ι κ ℝ, (∀ i j, 0 ≤ Q i j) → HasMarginals Q a b →
        relEntropy P K ≤ relEntropy Q K := by
  obtain ⟨Pfeas, hPfeas0, hPfeasa⟩ := hfeas
  set A : ℝ := ∑ i, a i with hA
  have hnonneg : IsClosed {P : Matrix ι κ ℝ | ∀ i j, 0 ≤ P i j} := by
    have key : {P : Matrix ι κ ℝ | ∀ i j, 0 ≤ P i j}
        = ⋂ i : ι, ⋂ j : κ, {P : Matrix ι κ ℝ | 0 ≤ P i j} := by
      ext P
      simp only [Set.mem_iInter, Set.mem_ofPred]
    rw [key]
    exact isClosed_iInter fun i : ι => isClosed_iInter fun j : κ =>
      isClosed_le (f := fun _ => (0 : ℝ)) (g := fun P : Matrix ι κ ℝ => P i j)
        continuous_const (by fun_prop)
  have hrows : IsClosed {P : Matrix ι κ ℝ | ∀ i : ι, (∑ j, P i j) = a i} := by
    have key : {P : Matrix ι κ ℝ | ∀ i : ι, (∑ j, P i j) = a i}
        = ⋂ i : ι, {P : Matrix ι κ ℝ | (∑ j, P i j) = a i} := by
      ext P
      simp only [Set.mem_iInter, Set.mem_ofPred]
    rw [key]
    exact isClosed_iInter fun i : ι =>
      isClosed_eq (f := fun P : Matrix ι κ ℝ => ∑ j, P i j) (g := fun _ => a i)
        (by fun_prop) continuous_const
  have hcols : IsClosed {P : Matrix ι κ ℝ | ∀ j : κ, (∑ i, P i j) = b j} := by
    have key : {P : Matrix ι κ ℝ | ∀ j : κ, (∑ i, P i j) = b j}
        = ⋂ j : κ, {P : Matrix ι κ ℝ | (∑ i, P i j) = b j} := by
      ext P
      simp only [Set.mem_iInter, Set.mem_ofPred]
    rw [key]
    exact isClosed_iInter fun j : κ =>
      isClosed_eq (f := fun P : Matrix ι κ ℝ => ∑ i, P i j) (g := fun _ => b j)
        (by fun_prop) continuous_const
  set S : Set (Matrix ι κ ℝ) :=
    {P | (∀ i j, 0 ≤ P i j) ∧ HasMarginals P a b} with hS
  have hclosed : IsClosed S := by
    rw [hS, Set.ofPred_and]
    exact hnonneg.inter (hrows.inter hcols)
  have hbound : ∀ P : Matrix ι κ ℝ, (∀ i j, 0 ≤ P i j) → HasMarginals P a b →
      ∀ i j, P i j ≤ A := by
    intro P hP0 hPa i j
    calc P i j ≤ ∑ k, P i k := Finset.single_le_sum (fun k _ => hP0 i k) (Finset.mem_univ j)
      _ = a i := hPa.1 i
      _ ≤ ∑ k, a k := Finset.single_le_sum
          (fun k _ => by rw [← hPa.1 k]; exact Finset.sum_nonneg fun l _ => hP0 k l)
          (Finset.mem_univ i)
      _ = A := hA.symm
  have hbox : IsCompact {P : Matrix ι κ ℝ | ∀ i j, P i j ∈ Set.Icc 0 A} :=
    IsCompact.matrix (isCompact_Icc (α := ℝ))
  have hcompact : IsCompact S :=
    IsCompact.of_isClosed_subset hbox hclosed
      fun P hP => fun i j => ⟨hP.1 i j, hbound P hP.1 hP.2 i j⟩
  obtain ⟨P, hPmem, hPmin⟩ := hcompact.exists_isMinOn (f := fun P => relEntropy P K)
    ⟨Pfeas, hPfeas0, hPfeasa⟩ (continuous_relEntropy K).continuousOn
  rw [hS, Set.mem_ofPred] at hPmem
  exact ⟨P, hPmem.1, hPmem.2, fun Q hQ0 hQa => (isMinOn_iff.mp hPmin) Q ⟨hQ0, hQa⟩⟩

/-- The relative entropy against `K` attains a minimum on the nonnegative matrices with row sums
`a` and column sums `b` whenever `a` and `b` are nonnegative and of equal total mass.

Such a matrix is always available: the product coupling `P i j = a i * b j / ∑ k, a k` has the
prescribed marginals when the total mass is positive, and when the total mass is zero both marginals
vanish identically, so the zero matrix has them. -/
theorem exists_relEntropy_minOn_of_nonneg (K : Matrix ι κ ℝ) (a : ι → ℝ) (b : κ → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j) (hmass : (∑ i, a i) = ∑ j, b j) :
    ∃ P : Matrix ι κ ℝ, (∀ i j, 0 ≤ P i j) ∧ HasMarginals P a b ∧
      ∀ Q : Matrix ι κ ℝ, (∀ i j, 0 ≤ Q i j) → HasMarginals Q a b →
        relEntropy P K ≤ relEntropy Q K := by
  have hfeas : ∃ P : Matrix ι κ ℝ, (∀ i j, 0 ≤ P i j) ∧ HasMarginals P a b := by
    by_cases hApos : 0 < ∑ i, a i
    · -- The product coupling of the two marginals.
      set A : ℝ := ∑ i, a i with hA
      have hA0 : A ≠ 0 := ne_of_gt hApos
      have hP₀ : (∀ i j, 0 ≤ (fun i j => a i * (b j * A⁻¹)) i j) ∧
          HasMarginals (fun i j => a i * (b j * A⁻¹)) a b := by
        constructor
        · intro i j
          exact mul_nonneg (ha i) (mul_nonneg (hb j) (inv_nonneg.mpr hApos.le))
        · constructor
          · intro i
            calc ∑ j, a i * (b j * A⁻¹) = a i * ∑ j, (b j * A⁻¹) := by rw [Finset.mul_sum]
              _ = a i * ((∑ j, b j) * A⁻¹) := by rw [← Finset.sum_mul]
              _ = a i * (A * A⁻¹) := by rw [← hmass]
              _ = a i := by rw [mul_inv_cancel₀ hA0, mul_one]
          · intro j
            calc ∑ i, a i * (b j * A⁻¹) = (∑ i, a i) * (b j * A⁻¹) := by rw [Finset.sum_mul]
              _ = A * (b j * A⁻¹) := by rw [hA]
              _ = b j * (A * A⁻¹) := by ring
              _ = b j := by rw [mul_inv_cancel₀ hA0, mul_one]
      exact ⟨fun i j => a i * (b j * A⁻¹), hP₀.1, hP₀.2⟩
    · -- A total mass of zero forces both marginals to vanish.
      have hA0 : (∑ i, a i) = 0 :=
        le_antisymm (not_lt.mp hApos) (Finset.sum_nonneg fun i _ => ha i)
      have hb0 : (∑ j, b j) = 0 := by rw [← hmass, hA0]
      have hzero : HasMarginals (0 : Matrix ι κ ℝ) a b := by
        constructor
        · intro i
          have hle : a i ≤ ∑ k, a k := Finset.single_le_sum (fun k _ => ha k) (Finset.mem_univ i)
          rw [hA0] at hle
          simp only [Matrix.zero_apply, Finset.sum_const_zero]
          exact (le_antisymm hle (ha i)).symm
        · intro j
          have hle : b j ≤ ∑ k, b k := Finset.single_le_sum (fun k _ => hb k) (Finset.mem_univ j)
          rw [hb0] at hle
          simp only [Matrix.zero_apply, Finset.sum_const_zero]
          exact (le_antisymm hle (hb j)).symm
      exact ⟨0, fun _ _ => by simp, hzero⟩
  obtain ⟨P, hP, hPa⟩ := hfeas
  exact exists_relEntropy_minOn K a b ⟨P, hP, hPa⟩

/-- For strictly positive marginals `a` and `b` of equal total mass, the relative entropy against
`K` attains a minimum on the nonnegative matrices with row sums `a` and column sums `b`.

This is the case of nonnegative marginals of `exists_relEntropy_minOn_of_nonneg`; it is stated
separately because strictly positive marginals are the setting of
`Matrix.exists_isDiagonalScaling_of_relEntropy_minOn`, which identifies the minimiser with a
diagonal scaling of `K`. -/
theorem exists_relEntropy_minOn_of_pos (K : Matrix ι κ ℝ) (a : ι → ℝ) (b : κ → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j) (hmass : (∑ i, a i) = ∑ j, b j) :
    ∃ P : Matrix ι κ ℝ, (∀ i j, 0 ≤ P i j) ∧ HasMarginals P a b ∧
      ∀ Q : Matrix ι κ ℝ, (∀ i j, 0 ≤ Q i j) → HasMarginals Q a b →
        relEntropy P K ≤ relEntropy Q K :=
  exists_relEntropy_minOn_of_nonneg K a b (fun i => (ha i).le) (fun j => (hb j).le) hmass

/-! ### Rectangle perturbations -/

/-- `subIndicator i i' x` is `1` at `i`, `-1` at `i'` and `0` elsewhere. It is the difference of
the two sparse vectors `Pi.single i 1` and `Pi.single i' 1`, and it is the weight of a perturbation
of the rows, or of the columns, of a matrix. -/
private def subIndicator {ι : Type*} [DecidableEq ι] (i i' : ι) : ι → ℝ :=
  Pi.single i 1 - Pi.single i' 1

/-- The value of the sparse vector `subIndicator i i' x` is the difference of the indicators of `i`
and `i'` at `x`. -/
private theorem subIndicator_apply {ι : Type*} [DecidableEq ι] (i i' x : ι) :
    subIndicator i i' x = (if x = i then (1 : ℝ) else 0) - if x = i' then 1 else 0 := by
  simp [subIndicator, Pi.single_apply]

/-- The sparse vector `subIndicator i i' x` is `1` at `i`, provided `i` and `i'` are distinct. -/
private theorem subIndicator_eq_one {ι : Type*} [DecidableEq ι] {i i' : ι} (h : i ≠ i') :
    subIndicator i i' i = 1 := by
  rw [subIndicator_apply, ite_eq_left rfl, ite_eq_right h, sub_zero]

/-- The sparse vector `subIndicator i i' x` is `-1` at `i'`, provided `i` and `i'` are distinct. -/
private theorem subIndicator_eq_neg_one {ι : Type*} [DecidableEq ι] {i i' : ι} (h : i ≠ i') :
    subIndicator i i' i' = -1 := by
  rw [subIndicator_apply, ite_eq_right (Ne.symm h), ite_eq_left rfl, zero_sub]

/-- The sum of the sparse vector `subIndicator i i' x` against a function `g` of `x` is the
difference of the values of `g` at `i` and `i'`. -/
private lemma sum_subIndicator_mul {ι : Type*} [Fintype ι] [DecidableEq ι] (i i' : ι) (g : ι → ℝ) :
    ∑ x, subIndicator i i' x * g x = g i - g i' := by
  calc (∑ x, subIndicator i i' x * g x)
      = (Pi.single i (1 : ℝ) : ι → ℝ) ⬝ᵥ g - (Pi.single i' (1 : ℝ) : ι → ℝ) ⬝ᵥ g := by
          -- The dot product of two vectors is by definition the sum of the products of their
          -- entries, so unfolding the two dot products gives the two sums of the left side.
          rw [dotProduct, dotProduct]
          simp only [subIndicator, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
    _ = g i - g i' := by
          rw [single_one_dotProduct i g, single_one_dotProduct i' g]

/-- The sum of the sparse vector `subIndicator i i' x` over `x` is `0`. -/
private lemma sum_subIndicator {ι : Type*} [Fintype ι] [DecidableEq ι] (i i' : ι) :
    ∑ x, subIndicator i i' x = 0 := by
  simpa using (sum_subIndicator_mul i i' fun _ => (1 : ℝ))

open scoped Classical in
/-- The double sum of `subIndicator i i' x * (subIndicator j j' y * g x y)` over `x` and `y` is the
alternating sum of the values of `g` at the four cells of the rectangle `i`, `i'` by `j`, `j'`. -/
private lemma sum_subIndicator_prod (g : ι → κ → ℝ) (i i' : ι) (j j' : κ) :
    (∑ x, ∑ y, subIndicator i i' x * (subIndicator j j' y * g x y))
      = g i j - g i j' - g i' j + g i' j' := by
  have key : ∀ x : ι, (∑ y, subIndicator j j' y * g x y) = g x j - g x j' :=
    fun _ => sum_subIndicator_mul j j' (g _)
  calc (∑ x, ∑ y, subIndicator i i' x * (subIndicator j j' y * g x y))
      = ∑ x, subIndicator i i' x * (∑ y, subIndicator j j' y * g x y) := by
        apply Fintype.sum_congr
        intro x
        rw [Finset.mul_sum]
    _ = ∑ x, subIndicator i i' x * (g x j - g x j') := by
        apply Fintype.sum_congr
        intro x
        rw [key x]
    _ = g i j - g i j' - g i' j + g i' j' := by
        rw [sum_subIndicator_mul i i' (fun x => g x j - g x j')]
        ring

omit [Fintype ι] [Fintype κ] in
open scoped Classical in
/-- The outer product of two differences of sparse vectors vanishes outside the four cells of the
rectangle `i`, `i'` by `j`, `j'`: a row or a column outside the rectangle carries the weight `0`. -/
private lemma subIndicator_mul_eq_zero (i i' : ι) (j j' : κ) (x : ι) (y : κ)
    (h1 : ¬(x = i ∧ y = j)) (h2 : ¬(x = i ∧ y = j')) (h3 : ¬(x = i' ∧ y = j))
    (h4 : ¬(x = i' ∧ y = j')) : subIndicator i i' x * subIndicator j j' y = 0 := by
  by_cases hx : x = i
  · have hy1 : y ≠ j := fun e => h1 ⟨hx, e⟩
    have hy2 : y ≠ j' := fun e => h2 ⟨hx, e⟩
    have h0 : subIndicator j j' y = 0 := by
      rw [subIndicator_apply, ite_eq_right hy1, ite_eq_right hy2, sub_zero]
    rw [h0, mul_zero]
  by_cases hx' : x = i'
  · have hy1 : y ≠ j := fun e => h3 ⟨hx', e⟩
    have hy2 : y ≠ j' := fun e => h4 ⟨hx', e⟩
    have h0 : subIndicator j j' y = 0 := by
      rw [subIndicator_apply, ite_eq_right hy1, ite_eq_right hy2, sub_zero]
    rw [h0, mul_zero]
  · have h0 : subIndicator i i' x = 0 := by
      rw [subIndicator_apply, ite_eq_right hx, ite_eq_right hx', sub_zero]
    rw [h0, zero_mul]

/-- Adding the outer product `Matrix.vecMulVec (t * r) c` of a row weight `r` and a column weight
`c`, both of total sum `0`, preserves the row sums and the column sums: the row of `x` gains
`t * r x * (∑ y, c y)` and the column of `y` gains `t * (∑ x, r x) * c y`, and both are zero. -/
theorem HasMarginals.add_vecMulVec_of_sum_eq_zero (a : ι → ℝ) (b : κ → ℝ) (P : Matrix ι κ ℝ)
    (hP : HasMarginals P a b) (r : ι → ℝ) (c : κ → ℝ) (hr : ∑ x, r x = 0)
    (hc : ∑ y, c y = 0) (t : ℝ) : HasMarginals (P + Matrix.vecMulVec (fun x => t * r x) c) a b := by
  -- The row sums of a matrix are its product with the constant-one vector by `Matrix.mulVec`, and
  -- its column sums the same product by `Matrix.vecMul`, so each half of the goal is the vanishing
  -- of the corresponding product of the added outer product.
  have hzero : Matrix.mulVec (Matrix.vecMulVec (fun x => t * r x) c) (fun _ => (1 : ℝ)) = 0 ∧
      Matrix.vecMul (fun _ => (1 : ℝ)) (Matrix.vecMulVec (fun x => t * r x) c) = 0 := by
    constructor
    · rw [Matrix.vecMulVec_mulVec]
      simp [dotProduct, hc]
    · rw [Matrix.vecMul_vecMulVec]
      simp [dotProduct, ← Finset.mul_sum, hr]
  have hrow : Matrix.mulVec (P + Matrix.vecMulVec (fun x => t * r x) c) (fun _ => (1 : ℝ)) = a := by
    rw [Matrix.add_mulVec, hzero.1, add_zero]
    funext x
    simpa only [Matrix.mulVec_apply_eq_sum, mul_one] using hP.1 x
  have hcol : Matrix.vecMul (fun _ => (1 : ℝ)) (P + Matrix.vecMulVec (fun x => t * r x) c) = b := by
    rw [Matrix.vecMul_add, hzero.2, add_zero]
    funext y
    simpa only [Matrix.vecMul_apply_eq_sum, one_mul] using hP.2 y
  constructor
  · intro x
    have h := congrFun hrow x
    simpa only [Matrix.mulVec_apply_eq_sum, mul_one] using h
  · intro y
    have h := congrFun hcol y
    simpa only [Matrix.vecMul_apply_eq_sum, one_mul] using h

omit [Fintype ι] [Fintype κ] in
open scoped Classical in
/-- A nonnegative matrix `P` perturbed by the outer product of `t * subIndicator i i'` and
`subIndicator j j'`, which moves `t` into the cell `(i, j)`, takes it from the cells `(i, j')` and
`(i', j)` and adds it at `(i', j')`, stays nonnegative as soon as `0 ≤ t ≤ P i j'` and
`0 ≤ t ≤ P i' j`, that is as soon as the two cells that give up mass keep a nonnegative value. -/
private lemma nonneg_add_subIndicator (P : Matrix ι κ ℝ) (i i' : ι) (j j' : κ)
    (hi'ne : i ≠ i') (hj'ne : j ≠ j') (t : ℝ) (ht0 : 0 ≤ t) (hty : t ≤ P i j')
    (htz : t ≤ P i' j) (hP : ∀ i j, 0 ≤ P i j) (u : ι) (v : κ) :
    0 ≤ P u v + t * (subIndicator i i' u * subIndicator j j' v) := by
  by_cases h1 : u = i ∧ v = j
  · rw [h1.1, h1.2, subIndicator_eq_one hi'ne, subIndicator_eq_one hj'ne, one_mul]
    linarith [hP i j]
  by_cases h2 : u = i ∧ v = j'
  · rw [h2.1, h2.2, subIndicator_eq_one hi'ne, subIndicator_eq_neg_one hj'ne, one_mul, mul_neg,
      mul_one]
    linarith [hP i j', hty]
  by_cases h3 : u = i' ∧ v = j
  · rw [h3.1, h3.2, subIndicator_eq_neg_one hi'ne, subIndicator_eq_one hj'ne, neg_one_mul,
      mul_neg, mul_one]
    linarith [hP i' j, htz]
  by_cases h4 : u = i' ∧ v = j'
  · rw [h4.1, h4.2, subIndicator_eq_neg_one hi'ne, subIndicator_eq_neg_one hj'ne, neg_one_mul,
      neg_neg, mul_one]
    linarith [hP i' j']
  have h0 : subIndicator i i' u * subIndicator j j' v = 0 :=
    subIndicator_mul_eq_zero i i' j j' u v h1 h2 h3 h4
  rw [h0, mul_zero, add_zero]
  exact hP u v

open scoped Classical in
/-- Moving `t` into the cell `(i, j)` of `P`, taking it from the cells `(i, j')` and `(i', j)`, and
adding it to the cell `(i', j')`, changes the relative entropy against `K` by the corresponding
change of `u * log u` at those four cells, minus `t` times the alternating sum of `Real.log (K _ _)`
over them. -/
private lemma relEntropy_add_subIndicator (K P : Matrix ι κ ℝ) (i i' : ι) (j j' : κ)
    (hi'ne : i ≠ i') (hj'ne : j ≠ j') (t : ℝ) :
    relEntropy (P + Matrix.vecMulVec (fun x => t * subIndicator i i' x) (subIndicator j j')) K
      - relEntropy P K
      = ((P i j + t) * Real.log (P i j + t) - P i j * Real.log (P i j)
        + (P i j' - t) * Real.log (P i j' - t) - P i j' * Real.log (P i j')
        + (P i' j - t) * Real.log (P i' j - t) - P i' j * Real.log (P i' j)
        + (P i' j' + t) * Real.log (P i' j' + t) - P i' j' * Real.log (P i' j'))
      - (Real.log (K i j) - Real.log (K i j') - Real.log (K i' j)
        + Real.log (K i' j')) * t := by
  set Q : Matrix ι κ ℝ := P + Matrix.vecMulVec (fun x => t * subIndicator i i' x)
    (subIndicator j j') with hQ
  have hQapply : ∀ x y,
      Q x y = P x y + (t * subIndicator i i' x) * subIndicator j j' y := by
    intro x y
    simp only [hQ, Matrix.add_apply, Matrix.vecMulVec_apply]
  -- The values at the four cells of the rectangle.
  have hQ1 : Q i j = P i j + t := by
    rw [hQapply, subIndicator_eq_one hi'ne, subIndicator_eq_one hj'ne]
    ring
  have hQ2 : Q i j' = P i j' - t := by
    rw [hQapply, subIndicator_eq_one hi'ne, subIndicator_eq_neg_one hj'ne]
    ring
  have hQ3 : Q i' j = P i' j - t := by
    rw [hQapply, subIndicator_eq_neg_one hi'ne, subIndicator_eq_one hj'ne]
    ring
  have hQ4 : Q i' j' = P i' j' + t := by
    rw [hQapply, subIndicator_eq_neg_one hi'ne, subIndicator_eq_neg_one hj'ne]
    ring
  -- Outside the four cells the perturbation vanishes, so the matrix `Q` agrees there with `P`.
  have hD : ∀ x y, ¬(x = i ∧ y = j) → ¬(x = i ∧ y = j') → ¬(x = i' ∧ y = j)
      → ¬(x = i' ∧ y = j') → subIndicator i i' x * subIndicator j j' y = 0 :=
    fun _ _ h1 h2 h3 h4 => subIndicator_mul_eq_zero i i' j j' _ _ h1 h2 h3 h4
  have hQ0 : ∀ x y, ¬(x = i ∧ y = j) → ¬(x = i ∧ y = j') → ¬(x = i' ∧ y = j)
      → ¬(x = i' ∧ y = j') → Q x y = P x y := by
    intro x y h1 h2 h3 h4
    have h0 : (t * subIndicator i i' x) * subIndicator j j' y = 0 := by
      calc (t * subIndicator i i' x) * subIndicator j j' y
          = t * (subIndicator i i' x * subIndicator j j' y) := by ring
        _ = 0 := by rw [hD x y h1 h2 h3 h4, mul_zero]
    rw [hQapply, h0, add_zero]
  -- The change of the two sums of `u * log u`, supported on the four cells.
  set φ : ι → κ → ℝ := fun x y => Q x y * Real.log (Q x y) - P x y * Real.log (P x y)
    with hφ
  have hφ0 : ∀ x y, ¬(x = i ∧ y = j) → ¬(x = i ∧ y = j') → ¬(x = i' ∧ y = j)
      → ¬(x = i' ∧ y = j') → φ x y = 0 := by
    intro x y h1 h2 h3 h4
    have h0 : Q x y = P x y := hQ0 x y h1 h2 h3 h4
    simp only [hφ, h0]
    ring
  have hφsum : (∑ x, ∑ y, φ x y) = φ i j + φ i j' + φ i' j + φ i' j' :=
    Finset.sum_eq_four φ i i' j j' hi'ne hj'ne hφ0
  -- The change of the two sums of `u * log (K u v)`, supported on the four cells as well.
  have hKsum : (∑ x, ∑ y, ((Q x y - P x y) * Real.log (K x y)))
      = (Real.log (K i j) - Real.log (K i j') - Real.log (K i' j)
        + Real.log (K i' j')) * t := by
    calc (∑ x, ∑ y, ((Q x y - P x y) * Real.log (K x y)))
        = ∑ x, ∑ y, (t * (subIndicator i i' x * subIndicator j j' y)) * Real.log (K x y) := by
          apply Fintype.sum_congr
          intro x
          apply Fintype.sum_congr
          intro y
          rw [hQapply]
          ring
      _ = ∑ x, ∑ y, subIndicator i i' x * (subIndicator j j' y * (t * Real.log (K x y))) := by
          apply Fintype.sum_congr
          intro x
          apply Fintype.sum_congr
          intro y
          ring
      _ = (Real.log (K i j) - Real.log (K i j') - Real.log (K i' j)
          + Real.log (K i' j')) * t := by
          rw [sum_subIndicator_prod (fun x y => t * Real.log (K x y)) i i' j j']
          ring
  calc relEntropy Q K - relEntropy P K
      = (∑ x, ∑ y, φ x y) - ∑ x, ∑ y, ((Q x y - P x y) * Real.log (K x y)) := by
        have key : ∀ x y, (Q x y * Real.log (Q x y) - Q x y * Real.log (K x y))
              - (P x y * Real.log (P x y) - P x y * Real.log (K x y))
            = φ x y - (Q x y - P x y) * Real.log (K x y) := by
          intro x y
          simp only [hφ]
          ring
        unfold relEntropy
        calc (∑ x, ∑ y, (Q x y * Real.log (Q x y) - Q x y * Real.log (K x y)))
              - ∑ x, ∑ y, (P x y * Real.log (P x y) - P x y * Real.log (K x y))
            = ∑ x, ∑ y, ((Q x y * Real.log (Q x y) - Q x y * Real.log (K x y))
                - (P x y * Real.log (P x y) - P x y * Real.log (K x y))) := by
              simp_rw [← Finset.sum_sub_distrib]
          _ = ∑ x, ∑ y, (φ x y - (Q x y - P x y) * Real.log (K x y)) := by
              apply Fintype.sum_congr
              intro x
              apply Fintype.sum_congr
              intro y
              exact key x y
          _ = (∑ x, ∑ y, φ x y) - ∑ x, ∑ y, ((Q x y - P x y) * Real.log (K x y)) := by
              simp_rw [← Finset.sum_sub_distrib]
      _ = φ i j + φ i j' + φ i' j + φ i' j'
        - (Real.log (K i j) - Real.log (K i j') - Real.log (K i' j)
          + Real.log (K i' j')) * t := by
        rw [hφsum, hKsum]
      _ = ((P i j + t) * Real.log (P i j + t) - P i j * Real.log (P i j)
        + (P i j' - t) * Real.log (P i j' - t) - P i j' * Real.log (P i j')
        + (P i' j - t) * Real.log (P i' j - t) - P i' j * Real.log (P i' j)
        + (P i' j' + t) * Real.log (P i' j' + t) - P i' j' * Real.log (P i' j'))
        - (Real.log (K i j) - Real.log (K i j') - Real.log (K i' j)
          + Real.log (K i' j')) * t := by
        simp only [hφ]
        rw [hQ1, hQ2, hQ3, hQ4]
        ring

/-- A minimiser of the relative entropy against `K` has no zero entry, for every matrix `K`: moving
a sufficiently small positive amount of mass into a zero entry, taken from one entry of the same
row and one entry of the same column, preserves the marginals and decreases the relative entropy.

There is no hypothesis on `K`: the argument below bounds the kernel contribution `t * L`, with
`L = log (K i j) - log (K i j') - log (K i' j) + log (K i' j')`, by an arbitrary constant. -/
theorem pos_of_relEntropy_minOn (K : Matrix ι κ ℝ) (a : ι → ℝ) (b : κ → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j) {P : Matrix ι κ ℝ} (hP : ∀ i j, 0 ≤ P i j)
    (hPa : HasMarginals P a b)
    (hmin : ∀ Q : Matrix ι κ ℝ, (∀ i j, 0 ≤ Q i j) → HasMarginals Q a b →
      relEntropy P K ≤ relEntropy Q K) :
    ∀ i j, 0 < P i j := by
  classical
  by_contra hzero
  push Not at hzero
  obtain ⟨i, j, hij⟩ := hzero
  have hij0 : P i j = 0 := le_antisymm hij (hP i j)
  -- The row of `i` and the column of `j` each contain a positive entry, because `a` and `b` are
  -- strictly positive.
  obtain ⟨j', hj'pos, hj'ne⟩ : ∃ j' : κ, 0 < P i j' ∧ j' ≠ j := by
    have key : ∃ y, 0 < P i y := by
      by_contra hcon
      push Not at hcon
      have h1 : (∑ y, P i y) ≤ 0 := Finset.sum_nonpos fun y _ => hcon y
      rw [hPa.1 i] at h1
      exact absurd h1 (not_le_of_gt (ha i))
    obtain ⟨j'', hj''⟩ := key
    have hj''ne : j'' ≠ j := by
      intro h
      rw [h] at hj''
      rw [hij0] at hj''
      exact absurd hj'' (lt_irrefl _)
    exact ⟨j'', hj'', hj''ne⟩
  obtain ⟨i', hi'pos, hi'ne⟩ : ∃ i' : ι, 0 < P i' j ∧ i' ≠ i := by
    have key : ∃ x, 0 < P x j := by
      by_contra hcon
      push Not at hcon
      have h1 : (∑ x, P x j) ≤ 0 := Finset.sum_nonpos fun x _ => hcon x
      rw [hPa.2 j] at h1
      exact absurd h1 (not_le_of_gt (hb j))
    obtain ⟨i'', hi''⟩ := key
    have hi''ne : i'' ≠ i := by
      intro h
      rw [h] at hi''
      rw [hij0] at hi''
      exact absurd hi'' (lt_irrefl _)
    exact ⟨i'', hi'', hi''ne⟩
  have hi'ne' : i ≠ i' := fun h => hi'ne h.symm
  have hj'ne' : j ≠ j' := fun h => hj'ne h.symm
  -- `y` and `z` are the two cells that give up mass, `q` is the cell that receives it.
  set y : ℝ := P i j' with hy
  set z : ℝ := P i' j with hz
  set q : ℝ := P i' j' with hq
  have hy0 : 0 < y := by rw [hy]; exact hj'pos
  have hz0 : 0 < z := by rw [hz]; exact hi'pos
  have hq0 : 0 ≤ q := by rw [hq]; exact hP i' j'
  -- For `0 < t` the perturbation `Q t = P + t * (subIndicator i i' ⊗ subIndicator j j')` moves `t`
  -- into the cell `(i, j)`, takes it from `(i, j')` and `(i', j)`, and adds it at `(i', j')`.
  set Q : ℝ → Matrix ι κ ℝ := fun t =>
    P + Matrix.vecMulVec (fun x => t * subIndicator i i' x) (subIndicator j j') with hQ
  have hQnonneg : ∀ t, 0 ≤ t → t ≤ min y z → ∀ u v, 0 ≤ Q t u v := by
    intro t ht htmin u v
    rw [hQ]
    simp only [Matrix.add_apply, Matrix.vecMulVec_apply]
    have hre : (t * subIndicator i i' u) * subIndicator j j' v
        = t * (subIndicator i i' u * subIndicator j j' v) := by ring
    rw [hre]
    exact nonneg_add_subIndicator P i i' j j' hi'ne' hj'ne' t ht
      (le_trans htmin (min_le_left _ _)) (le_trans htmin (min_le_right _ _)) hP u v
  have hQmarg : ∀ t, HasMarginals (Q t) a b := by
    intro t
    rw [hQ]
    exact HasMarginals.add_vecMulVec_of_sum_eq_zero a b P hPa (subIndicator i i')
      (subIndicator j j') (sum_subIndicator i i') (sum_subIndicator j j') t
  have hrelDiff (t : ℝ) :
      relEntropy (Q t) K - relEntropy P K
        = ((P i j + t) * Real.log (P i j + t) - P i j * Real.log (P i j)
          + (P i j' - t) * Real.log (P i j' - t) - P i j' * Real.log (P i j')
          + (P i' j - t) * Real.log (P i' j - t) - P i' j * Real.log (P i' j)
          + (P i' j' + t) * Real.log (P i' j' + t) - P i' j' * Real.log (P i' j'))
        - (Real.log (K i j) - Real.log (K i j') - Real.log (K i' j)
          + Real.log (K i' j')) * t := by
    rw [hQ]
    exact relEntropy_add_subIndicator K P i i' j j' hi'ne' hj'ne' t
  -- The step `t` is chosen so small that the gain at the receiving cell, `t * log t`, dominates the
  -- losses at the two donor cells, the gain at the fourth cell and the kernel term `t * L`.
  set L : ℝ := Real.log (K i j) - Real.log (K i j') - Real.log (K i' j) + Real.log (K i' j')
    with hL
  set C : ℝ := -Real.log y - Real.log z + Real.log (q + 1) + 2 * Real.log 2 - 1 - L with hC
  set t : ℝ := min (min (min y z) 1) (Real.exp (-(C + 1))) / 2 with ht
  have hminA : min (min (min y z) 1) (Real.exp (-(C + 1))) ≤ min (min y z) 1 := min_le_left _ _
  have hminy : min y z ≤ y := min_le_left _ _
  have hminz : min y z ≤ z := min_le_right _ _
  have hminE : min (min (min y z) 1) (Real.exp (-(C + 1))) ≤ Real.exp (-(C + 1)) :=
    min_le_right _ _
  have hX0 : 0 < min (min (min y z) 1) (Real.exp (-(C + 1))) := by
    exact lt_min (lt_min (lt_min hy0 hz0) (by norm_num)) (by positivity)
  have ht0 : 0 < t := by
    rw [ht]
    exact div_pos hX0 (by norm_num : (0 : ℝ) < 2)
  have hty : t ≤ y / 2 := by
    rw [ht]
    calc (min (min (min y z) 1) (Real.exp (-(C + 1)))) / 2
        ≤ (min (min y z) 1) / 2 := div_le_div_of_nonneg_right hminA (by norm_num)
      _ ≤ (min y z) / 2 := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
      _ ≤ y / 2 := div_le_div_of_nonneg_right hminy (by norm_num)
  have htz : t ≤ z / 2 := by
    rw [ht]
    calc (min (min (min y z) 1) (Real.exp (-(C + 1)))) / 2
        ≤ (min (min y z) 1) / 2 := div_le_div_of_nonneg_right hminA (by norm_num)
      _ ≤ (min y z) / 2 := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
      _ ≤ z / 2 := div_le_div_of_nonneg_right hminz (by norm_num)
  have ht1 : t ≤ 1 / 2 := by
    rw [ht]
    calc (min (min (min y z) 1) (Real.exp (-(C + 1)))) / 2
        ≤ (min (min y z) 1) / 2 := div_le_div_of_nonneg_right hminA (by norm_num)
      _ ≤ 1 / 2 := div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  have htE : t ≤ Real.exp (-(C + 1)) := by
    rw [ht]
    calc (min (min (min y z) 1) (Real.exp (-(C + 1)))) / 2
        ≤ Real.exp (-(C + 1)) / 2 := div_le_div_of_nonneg_right hminE (by norm_num)
      _ ≤ Real.exp (-(C + 1)) := div_le_self (by positivity) (by norm_num)
  have hqt0 : 0 < q + t := by linarith
  have hqt1 : 0 < q + 1 := by linarith
  have htmin : t ≤ min y z := le_min
    (le_trans hty (div_le_self hy0.le (by norm_num)))
    (le_trans htz (div_le_self hz0.le (by norm_num)))
  have hlogt : Real.log t ≤ -(C + 1) := by
    have h1 : Real.log t ≤ Real.log (Real.exp (-(C + 1))) := by
      exact Real.strictMonoOn_log.monotoneOn ht0 (Real.exp_pos _) htE
    rwa [Real.log_exp] at h1
  -- The supporting-line inequality bounds the loss at each of the two donor cells and the gain at
  -- the receiving cell.
  have hby : (y - t) * Real.log (y - t) - y * Real.log y
      ≤ -t * (Real.log y - Real.log 2 + 1) := Real.sub_mul_log_le ht0.le hty
  have hbz : (z - t) * Real.log (z - t) - z * Real.log z
      ≤ -t * (Real.log z - Real.log 2 + 1) := Real.sub_mul_log_le ht0.le htz
  have hbq : (q + t) * Real.log (q + t) - q * Real.log q ≤ t * (Real.log (q + 1) + 1) := by
    have hle := Real.mul_log_sub_mul_log_ge (q + t) q hqt0 hq0
    have h2 : Real.log (q + t) ≤ Real.log (q + 1) :=
      Real.strictMonoOn_log.monotoneOn hqt0 hqt1 (by linarith [ht1])
    have h3 := mul_le_mul_of_nonneg_left h2 ht0.le
    linarith
  -- The perturbed matrix is a competitor of `P`, and its relative entropy is strictly smaller.
  have hnonpos : relEntropy P K ≤ relEntropy (Q t) K := hmin _ (hQnonneg t ht0.le htmin) (hQmarg t)
  have hneg : relEntropy (Q t) K - relEntropy P K < 0 := by
    rw [hrelDiff t, hij0, ← hy, ← hz, ← hq]
    simp only [Real.log_zero, zero_mul, zero_add, sub_zero]
    have key1 : Real.log t + C < 0 := by
      linarith [hlogt, hC]
    have key2 : (Real.log t + C) * t < 0 := mul_neg_of_neg_of_pos key1 ht0
    linarith [hby, hbz, hbq, hL]
  linarith

/-! ### Linearity of the marginal constraints -/

/-- The row and column sums of a sum of two matrices are the sums of their row and column sums. -/
theorem HasMarginals.add {P Q : Matrix ι κ ℝ} {a a' : ι → ℝ} {b b' : κ → ℝ}
    (hP : HasMarginals P a b) (hQ : HasMarginals Q a' b') :
    HasMarginals (P + Q) (a + a') (b + b') :=
  ⟨fun i => by simp [Finset.sum_add_distrib, hP.1 i, hQ.1 i],
    fun j => by simp [Finset.sum_add_distrib, hP.2 j, hQ.2 j]⟩

/-- The row and column sums of a scalar multiple of a matrix are the same multiple of its row and
column sums. -/
theorem HasMarginals.smul {P : Matrix ι κ ℝ} {a : ι → ℝ} {b : κ → ℝ} (hP : HasMarginals P a b)
    (t : ℝ) : HasMarginals (t • P) (t • a) (t • b) :=
  ⟨fun i => by simp [← Finset.mul_sum, hP.1 i], fun j => by simp [← Finset.mul_sum, hP.2 j]⟩

/-- Summed against a matrix with row sums `a` and column sums `b`, a function `f i + g j` of the
row plus a function of the column gives `∑ i, a i * f i + ∑ j, b j * g j`: only the marginals of
the matrix enter. -/
theorem HasMarginals.sum_sum_mul_add {Q : Matrix ι κ ℝ} {a : ι → ℝ} {b : κ → ℝ}
    (hQ : HasMarginals Q a b) (f : ι → ℝ) (g : κ → ℝ) :
    ∑ i, ∑ j, Q i j * (f i + g j) = ∑ i, a i * f i + ∑ j, b j * g j := by
  simp only [mul_add, Finset.sum_add_distrib]
  congr 1
  · simp_rw [← Finset.sum_mul, hQ.1]
  · rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, hQ.2]

/-! ### Gibbs' inequality -/

/-- Gibbs' inequality in its quantitative form: the relative entropy of a nonnegative matrix `Q`
against a strictly positive matrix `P` of the same total mass dominates the squared Hellinger
distance `∑ i, ∑ j, (√(Q i j) - √(P i j)) ^ 2`. -/
theorem sum_sum_sq_sqrt_sub_sqrt_le_relEntropy {P Q : Matrix ι κ ℝ} (hQ : ∀ i j, 0 ≤ Q i j)
    (hP : ∀ i j, 0 < P i j) (hmass : ∑ i, ∑ j, Q i j = ∑ i, ∑ j, P i j) :
    ∑ i, ∑ j, (√(Q i j) - √(P i j)) ^ 2 ≤ relEntropy Q P := by
  -- Summed over the cells, the gap of the supporting line of `x ↦ x * log x` at `P i j` is the
  -- relative entropy, because the linear terms add up to the difference of the total masses.
  have hgap : relEntropy Q P = ∑ i, ∑ j, (Q i j * Real.log (Q i j) - P i j * Real.log (P i j)
      - (Q i j - P i j) * (Real.log (P i j) + 1)) := by
    have hlin : ∑ i, ∑ j, (Q i j - P i j) = 0 := by
      simp only [Finset.sum_sub_distrib, hmass, sub_self]
    rw [relEntropy_def, ← sub_zero (∑ i, ∑ j, _), ← hlin, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hgap]
  exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
    TauCeti.sq_sqrt_sub_sqrt_le_mul_log_sub_mul_log_sub (hP i j) (hQ i j)

/-- Gibbs' inequality: the relative entropy of a nonnegative matrix `Q` against a strictly positive
matrix `P` of the same total mass is nonnegative. -/
theorem relEntropy_nonneg {P Q : Matrix ι κ ℝ} (hQ : ∀ i j, 0 ≤ Q i j) (hP : ∀ i j, 0 < P i j)
    (hmass : ∑ i, ∑ j, Q i j = ∑ i, ∑ j, P i j) : 0 ≤ relEntropy Q P :=
  le_trans (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
    (sum_sum_sq_sqrt_sub_sqrt_le_relEntropy hQ hP hmass)

/-- The equality case of Gibbs' inequality: the relative entropy of a nonnegative matrix `Q` against
a strictly positive matrix `P` of the same total mass vanishes exactly when `Q = P`. -/
theorem relEntropy_eq_zero_iff {P Q : Matrix ι κ ℝ} (hQ : ∀ i j, 0 ≤ Q i j)
    (hP : ∀ i j, 0 < P i j) (hmass : ∑ i, ∑ j, Q i j = ∑ i, ∑ j, P i j) :
    relEntropy Q P = 0 ↔ Q = P := by
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  have hle := sum_sum_sq_sqrt_sub_sqrt_le_relEntropy hQ hP hmass
  rw [h] at hle
  have hrow : ∀ i, 0 ≤ ∑ j, (√(Q i j) - √(P i j)) ^ 2 :=
    fun i => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hrow i).mp
    (le_antisymm hle (Finset.sum_nonneg fun i _ => hrow i))
  ext i j
  have hij := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _).mp
    (hzero i (Finset.mem_univ i)) j (Finset.mem_univ j)
  rw [sq_eq_zero_iff, sub_eq_zero] at hij
  rw [← Real.sq_sqrt (hQ i j), ← Real.sq_sqrt (hP i j).le, hij]

/-! ### The first-order condition at a positive minimiser -/

/-- The relative entropy against `K` of the matrix `P + t • D` has derivative
`∑ i, ∑ j, D i j * (log (P i j) + 1 - log (K i j))` in `t` at `t = 0`, as soon as no entry of `P`
vanishes. -/
theorem hasDerivAt_relEntropy_add_smul (K P D : Matrix ι κ ℝ) (hP : ∀ i j, P i j ≠ 0) :
    HasDerivAt (fun t : ℝ => relEntropy (P + t • D) K)
      (∑ i, ∑ j, D i j * (Real.log (P i j) + 1 - Real.log (K i j))) 0 := by
  simp only [relEntropy_def, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  refine HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun j _ => ?_
  have hlin : HasDerivAt (fun t : ℝ => P i j + t * D i j) (D i j) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (D i j)).const_add (P i j)
  have hlog :
      HasDerivAt (fun x => x * Real.log x) (Real.log (P i j) + 1) (P i j + 0 * D i j) := by
    simpa using Real.hasDerivAt_mul_log (hP i j)
  refine ((hlog.comp 0 hlin).sub (hlin.mul_const (Real.log (K i j)))).congr_deriv ?_
  ring

/-- The first-order condition at a minimiser with positive entries: if `P` minimises the relative
entropy against `K` among the nonnegative matrices with row sums `a` and column sums `b`, and
every entry of `P` is positive, then the matrix `log (P i j) - log (K i j)` is orthogonal to every
direction `D` whose row and column sums vanish. -/
theorem sum_sum_mul_log_sub_log_eq_zero_of_relEntropy_minOn (K : Matrix ι κ ℝ) {a : ι → ℝ}
    {b : κ → ℝ} {P D : Matrix ι κ ℝ} (hP : ∀ i j, 0 < P i j) (hPa : HasMarginals P a b)
    (hmin : ∀ Q : Matrix ι κ ℝ, (∀ i j, 0 ≤ Q i j) → HasMarginals Q a b →
      relEntropy P K ≤ relEntropy Q K)
    (hD : HasMarginals D 0 0) :
    ∑ i, ∑ j, D i j * (Real.log (P i j) - Real.log (K i j)) = 0 := by
  -- For `t` near `0` the matrix `P + t • D` is still nonnegative and has the marginals of `P`, so
  -- `t = 0` is a local minimum of its relative entropy.
  have hloc : IsLocalMin (fun t : ℝ => relEntropy (P + t • D) K) 0 := by
    have hpos : ∀ᶠ t in nhds (0 : ℝ), ∀ i j, 0 < (P + t • D) i j := by
      simp only [Filter.eventually_all]
      intro i j
      have hc : Continuous fun t : ℝ => (P + t • D) i j := by
        simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
        fun_prop
      exact continuousAt_const.eventually_lt hc.continuousAt (by simpa using hP i j)
    refine hpos.mono fun t ht => ?_
    simpa using hmin _ (fun i j => (ht i j).le) (by simpa using hPa.add (hD.smul t))
  have hderiv := hloc.hasDerivAt_eq_zero
    (hasDerivAt_relEntropy_add_smul K P D fun i j => (hP i j).ne')
  -- The constant `1` in the derivative contributes `∑ i, ∑ j, D i j`, which vanishes.
  have hsum : ∑ i, ∑ j, D i j = 0 := by simp [hD.1]
  have hsplit : ∑ i, ∑ j, D i j * (Real.log (P i j) + 1 - Real.log (K i j))
      = ∑ i, ∑ j, D i j * (Real.log (P i j) - Real.log (K i j)) + ∑ i, ∑ j, D i j := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  linarith

/-! ### The minimiser is a diagonal scaling -/

/-- For a strictly positive kernel `K` and strictly positive marginals `a` and `b`, every minimiser
`P` of the relative entropy against `K` among the nonnegative matrices with row sums `a` and column
sums `b` is a diagonal scaling of `K` by strictly positive row and column factors. -/
theorem exists_isDiagonalScaling_of_relEntropy_minOn {K : Matrix ι κ ℝ} (hK : ∀ i j, 0 < K i j)
    {a : ι → ℝ} {b : κ → ℝ} (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j) {P : Matrix ι κ ℝ}
    (hP : ∀ i j, 0 ≤ P i j) (hPa : HasMarginals P a b)
    (hmin : ∀ Q : Matrix ι κ ℝ, (∀ i j, 0 ≤ Q i j) → HasMarginals Q a b →
      relEntropy P K ≤ relEntropy Q K) :
    ∃ (u : ι → ℝ) (v : κ → ℝ), (∀ i, 0 < u i) ∧ (∀ j, 0 < v j) ∧ IsDiagonalScaling P K u v := by
  classical
  have hPpos := pos_of_relEntropy_minOn K a b ha hb hP hPa hmin
  set H : ι → κ → ℝ := fun i j => Real.log (P i j) - Real.log (K i j) with hH
  -- Testing the first-order condition against the rectangle direction on `i`, `i'` by `j`, `j'`
  -- makes the alternating sum of `H` over the four cells vanish, so `H` is the sum of a function
  -- of the row and a function of the column.
  have hrect : ∀ i i' j j', H i j - H i j' - H i' j + H i' j' = 0 := by
    intro i i' j j'
    have hD : HasMarginals (Matrix.vecMulVec (subIndicator i i') (subIndicator j j')) 0 0 :=
      ⟨fun x => by simp [Matrix.vecMulVec_apply, ← Finset.mul_sum, sum_subIndicator],
        fun y => by simp [Matrix.vecMulVec_apply, ← Finset.sum_mul, sum_subIndicator]⟩
    rw [← sum_subIndicator_prod H i i' j j',
      ← sum_sum_mul_log_sub_log_eq_zero_of_relEntropy_minOn K hPpos hPa hmin hD]
    simp only [Matrix.vecMulVec_apply, hH, mul_assoc]
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i₀⟩⟩
  · exact ⟨1, 1, fun _ => one_pos, fun _ => one_pos, fun i => isEmptyElim i⟩
  rcases isEmpty_or_nonempty κ with hκ | ⟨⟨j₀⟩⟩
  · exact ⟨1, 1, fun _ => one_pos, fun _ => one_pos, fun _ j => isEmptyElim j⟩
  refine ⟨fun i => Real.exp (H i j₀), fun j => Real.exp (H i₀ j - H i₀ j₀),
    fun _ => Real.exp_pos _, fun _ => Real.exp_pos _, fun i j => ?_⟩
  have hHij : H i j = H i j₀ + (H i₀ j - H i₀ j₀) := by linarith [hrect i i₀ j j₀]
  calc P i j = Real.exp (H i j) * K i j := by
        rw [hH, Real.exp_sub, Real.exp_log (hPpos i j), Real.exp_log (hK i j),
          div_mul_cancel₀ _ (hK i j).ne']
    _ = Real.exp (H i j₀) * K i j * Real.exp (H i₀ j - H i₀ j₀) := by
        rw [hHij, Real.exp_add]
        ring

/-- **The Sinkhorn–Knopp theorem** for a strictly positive kernel: a strictly positive matrix `K`
and strictly positive row sums `a` and column sums `b` of equal total mass admit strictly positive
row factors `u` and column factors `v` such that the diagonal scaling `u i * K i j * v j` has row
sums `a` and column sums `b`.

The scaled matrix is the minimiser of the relative entropy against `K` with these marginals. -/
theorem exists_sinkhorn_scaling {K : Matrix ι κ ℝ} (hK : ∀ i j, 0 < K i j) {a : ι → ℝ}
    {b : κ → ℝ} (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j) (hmass : ∑ i, a i = ∑ j, b j) :
    ∃ (u : ι → ℝ) (v : κ → ℝ), (∀ i, 0 < u i) ∧ (∀ j, 0 < v j) ∧
      (∀ i, ∑ j, u i * K i j * v j = a i) ∧ ∀ j, ∑ i, u i * K i j * v j = b j := by
  obtain ⟨P, hP, hPa, hmin⟩ := exists_relEntropy_minOn_of_pos K a b ha hb hmass
  obtain ⟨u, v, hu, hv, hPuv⟩ :=
    exists_isDiagonalScaling_of_relEntropy_minOn hK ha hb hP hPa hmin
  refine ⟨u, v, hu, hv, fun i => ?_, fun j => ?_⟩
  · rw [← hPa.1 i]
    exact Finset.sum_congr rfl fun j _ => (hPuv i j).symm
  · rw [← hPa.2 j]
    exact Finset.sum_congr rfl fun i _ => (hPuv i j).symm

/-- The Pythagorean identity of the relative entropy at a diagonal scaling: if `K` and the scaling
factors have no zero entries, then for every matrix `Q` with the row and column sums of `P`,
`relEntropy Q K = relEntropy Q P + relEntropy P K`. -/
theorem IsDiagonalScaling.relEntropy_eq_relEntropy_add {P K : Matrix ι κ ℝ} {u : ι → ℝ}
    {v : κ → ℝ} (h : IsDiagonalScaling P K u v) (hK : ∀ i j, K i j ≠ 0) (hu : ∀ i, u i ≠ 0)
    (hv : ∀ j, v j ≠ 0) {a : ι → ℝ} {b : κ → ℝ} (hP : HasMarginals P a b) {Q : Matrix ι κ ℝ}
    (hQ : HasMarginals Q a b) :
    relEntropy Q K = relEntropy Q P + relEntropy P K := by
  have hlog : ∀ i j,
      Real.log (P i j) = Real.log (K i j) + (Real.log (u i) + Real.log (v j)) := by
    intro i j
    rw [h i j, Real.log_mul (mul_ne_zero (hu i) (hK i j)) (hv j),
      Real.log_mul (hu i) (hK i j)]
    ring
  have hQK : relEntropy Q K
      = relEntropy Q P + ∑ i, ∑ j, Q i j * (Real.log (u i) + Real.log (v j)) := by
    simp only [relEntropy_def, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hlog]
    ring
  have hPK : relEntropy P K = ∑ i, ∑ j, P i j * (Real.log (u i) + Real.log (v j)) := by
    simp only [relEntropy_def]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hlog]
    ring
  rw [hQK, hPK, hQ.sum_sum_mul_add, hP.sum_sum_mul_add]

/-- A diagonal scaling of a strictly positive `K` by strictly positive factors minimises the
relative entropy against `K` among the nonnegative matrices with its row and column sums. -/
theorem IsDiagonalScaling.relEntropy_le {P K : Matrix ι κ ℝ} {u : ι → ℝ} {v : κ → ℝ}
    (h : IsDiagonalScaling P K u v) (hK : ∀ i j, 0 < K i j) (hu : ∀ i, 0 < u i)
    (hv : ∀ j, 0 < v j) {a : ι → ℝ} {b : κ → ℝ} (hP : HasMarginals P a b) {Q : Matrix ι κ ℝ}
    (hQ0 : ∀ i j, 0 ≤ Q i j) (hQ : HasMarginals Q a b) :
    relEntropy P K ≤ relEntropy Q K := by
  have hPpos := h.pos hK hu hv
  have hmass : ∑ i, ∑ j, Q i j = ∑ i, ∑ j, P i j := by simp only [hQ.1, hP.1]
  rw [h.relEntropy_eq_relEntropy_add (fun i j => (hK i j).ne') (fun i => (hu i).ne')
    (fun j => (hv j).ne') hP hQ]
  linarith [relEntropy_nonneg hQ0 hPpos hmass]

/-- For a strictly positive kernel `K` and strictly positive marginals `a` and `b`, a nonnegative
matrix with row sums `a` and column sums `b` minimises the relative entropy against `K` among all
such matrices exactly when it is a diagonal scaling of `K` by strictly positive factors. -/
theorem relEntropy_minOn_iff_exists_isDiagonalScaling {K : Matrix ι κ ℝ} (hK : ∀ i j, 0 < K i j)
    {a : ι → ℝ} {b : κ → ℝ} (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j) {P : Matrix ι κ ℝ}
    (hP : ∀ i j, 0 ≤ P i j) (hPa : HasMarginals P a b) :
    (∀ Q : Matrix ι κ ℝ, (∀ i j, 0 ≤ Q i j) → HasMarginals Q a b →
      relEntropy P K ≤ relEntropy Q K) ↔
      ∃ (u : ι → ℝ) (v : κ → ℝ), (∀ i, 0 < u i) ∧ (∀ j, 0 < v j) ∧ IsDiagonalScaling P K u v :=
  ⟨exists_isDiagonalScaling_of_relEntropy_minOn hK ha hb hP hPa,
    fun ⟨_, _, hu, hv, h⟩ _ hQ0 hQ => h.relEntropy_le hK hu hv hPa hQ0 hQ⟩

/-- Two diagonal scalings of a strictly positive `K` by strictly positive factors that have the same
row and column sums are equal: the scaled matrix of the Sinkhorn–Knopp theorem is unique. -/
theorem IsDiagonalScaling.eq_of_hasMarginals {P P' K : Matrix ι κ ℝ} {u u' : ι → ℝ}
    {v v' : κ → ℝ} (h : IsDiagonalScaling P K u v) (h' : IsDiagonalScaling P' K u' v')
    (hK : ∀ i j, 0 < K i j) (hu : ∀ i, 0 < u i) (hv : ∀ j, 0 < v j) (hu' : ∀ i, 0 < u' i)
    (hv' : ∀ j, 0 < v' j) {a : ι → ℝ} {b : κ → ℝ} (hP : HasMarginals P a b)
    (hP' : HasMarginals P' a b) : P = P' := by
  have hPpos := h.pos hK hu hv
  have hP'pos := h'.pos hK hu' hv'
  have hmass : ∑ i, ∑ j, P' i j = ∑ i, ∑ j, P i j := by simp only [hP.1, hP'.1]
  -- Each scaling is the minimiser, so the two Pythagorean identities force both relative
  -- entropies between them to vanish.
  have e1 := h.relEntropy_eq_relEntropy_add (fun i j => (hK i j).ne')
    (fun i => (hu i).ne') (fun j => (hv j).ne') hP hP'
  have e2 := h'.relEntropy_eq_relEntropy_add (fun i j => (hK i j).ne')
    (fun i => (hu' i).ne') (fun j => (hv' j).ne') hP' hP
  have n1 := relEntropy_nonneg (fun i j => (hP'pos i j).le) hPpos hmass
  have n2 := relEntropy_nonneg (fun i j => (hPpos i j).le) hP'pos hmass.symm
  exact ((relEntropy_eq_zero_iff (fun i j => (hP'pos i j).le) hPpos hmass).mp (by linarith)).symm

omit [Fintype ι] [Fintype κ] in
/-- Up to a common scalar, the factors of a diagonal scaling of a kernel with no zero entry are
unique: if `P` is the diagonal scaling of `K` both by `u`, `v` and by `u'`, `v'`, with nonzero
`u'` and `v'`, then `u = r * u'` and `v = r⁻¹ * v'` for a nonzero scalar `r`. This is the converse
of `Matrix.IsDiagonalScaling.rescale_factors`. -/
theorem IsDiagonalScaling.exists_eq_rescale_factors [Nonempty ι] [Nonempty κ]
    {P K : Matrix ι κ ℝ} {u u' : ι → ℝ} {v v' : κ → ℝ} (h : IsDiagonalScaling P K u v)
    (h' : IsDiagonalScaling P K u' v') (hK : ∀ i j, K i j ≠ 0) (hu' : ∀ i, u' i ≠ 0)
    (hv' : ∀ j, v' j ≠ 0) :
    ∃ r : ℝ, r ≠ 0 ∧ (∀ i, u i = r * u' i) ∧ ∀ j, v j = r⁻¹ * v' j := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  obtain ⟨j₀⟩ := ‹Nonempty κ›
  -- Cancelling the entry of `K` identifies the two outer products of the factors.
  have huv : ∀ i j, u i * v j = u' i * v' j := fun i j =>
    mul_right_cancel₀ (hK i j) (by linear_combination (h' i j) - (h i j))
  have hu : ∀ i, u i ≠ 0 := fun i hi => mul_ne_zero (hu' i) (hv' j₀) (by rw [← huv, hi, zero_mul])
  have hv : ∀ j, v j ≠ 0 := fun j hj => mul_ne_zero (hu' i₀) (hv' j) (by rw [← huv, hj, mul_zero])
  refine ⟨u i₀ / u' i₀, div_ne_zero (hu i₀) (hu' i₀), fun i => ?_, fun j => ?_⟩
  · have hcross : u i * u' i₀ * v j₀ = u i₀ * u' i * v j₀ := by
      linear_combination u' i₀ * huv i j₀ - u' i * huv i₀ j₀
    rw [div_mul_eq_mul_div, eq_div_iff (hu' i₀)]
    exact mul_right_cancel₀ (hv j₀) hcross
  · rw [inv_div, div_mul_eq_mul_div, eq_div_iff (hu i₀)]
    linear_combination huv i₀ j

/-! ### Comparison of diagonal scalings with the same row sums -/

omit [Fintype ι] in
open Real TauCeti in
/-- Two diagonal scalings whose kernel is strictly positive in row `i`, with the same `i`-th row
sum, agree on that row up to the factor `exp d`, where `d` is the Hilbert projective distance
between their column factors: if `P` is the diagonal scaling of `K` by `u` and `v > 0`, with
`u i ≥ 0`, and `Q` that by `u'` and `v' > 0`, then
`P i j ≤ exp (hilbertProjectiveDist v v') * Q i j`. -/
theorem IsDiagonalScaling.apply_le_exp_hilbertProjectiveDist_mul {P Q K : Matrix ι κ ℝ}
    {u u' : ι → ℝ} {v v' : κ → ℝ} (hP : IsDiagonalScaling P K u v)
    (hQ : IsDiagonalScaling Q K u' v') {i : ι} (hK : ∀ j, 0 < K i j) (hu : 0 ≤ u i)
    (hv : ∀ j, 0 < v j) (hv' : ∀ j, 0 < v' j) (hrow : ∑ j, P i j = ∑ j, Q i j)
    (j : κ) : P i j ≤ exp (hilbertProjectiveDist v v') * Q i j := by
  rw [isDiagonalScaling_def] at hP hQ
  have : Nonempty κ := ⟨j⟩
  -- the extreme ratios `m ≤ v j / v' j ≤ M` of the column factors, attained at `j₂` and `j₁`
  obtain ⟨j₁, hj₁⟩ := Finite.exists_max fun j ↦ v j / v' j
  obtain ⟨j₂, hj₂⟩ := Finite.exists_min fun j ↦ v j / v' j
  have hM : 0 < v j₁ / v' j₁ := div_pos (hv j₁) (hv' j₁)
  have hm : 0 < v j₂ / v' j₂ := div_pos (hv j₂) (hv' j₂)
  have hupper : ∀ j, v j ≤ v j₁ / v' j₁ * v' j := fun j ↦ (div_le_iff₀ (hv' j)).1 (hj₁ j)
  have hlower : ∀ j, v j₂ / v' j₂ * v' j ≤ v j := fun j ↦ (le_div_iff₀ (hv' j)).1 (hj₂ j)
  -- `M / m ≤ exp d`
  have hMm : v j₁ / v' j₁ / (v j₂ / v' j₂) ≤ exp (hilbertProjectiveDist v v') := by
    rw [← exp_log (div_pos hM hm), div_div_div_eq]
    exact exp_le_exp.2 (log_le_hilbertProjectiveDist v v' j₁ j₂)
  -- the equal row sums give `u i * m ≤ u' i`
  have hrow' : u i * ∑ j, K i j * v j = u' i * ∑ j, K i j * v' j := by
    simpa only [hP i, hQ i, mul_assoc, ← Finset.mul_sum] using hrow
  have hum : u i * (v j₂ / v' j₂) ≤ u' i := by
    refine le_of_mul_le_mul_right ?_
      (Finset.sum_pos (fun j _ ↦ mul_pos (hK j) (hv' j)) Finset.univ_nonempty)
    calc u i * (v j₂ / v' j₂) * ∑ j, K i j * v' j
        = u i * ∑ j, K i j * (v j₂ / v' j₂ * v' j) := by
          rw [mul_assoc, Finset.mul_sum]
          exact congrArg (u i * ·) (Finset.sum_congr rfl fun j _ ↦ by ring)
      _ ≤ u i * ∑ j, K i j * v j :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ ↦
            mul_le_mul_of_nonneg_left (hlower j) (hK j).le) hu
      _ = u' i * ∑ j, K i j * v' j := hrow'
  have hQ0 : 0 ≤ Q i j := by
    rw [hQ i j]
    exact mul_nonneg (mul_nonneg ((mul_nonneg hu hm.le).trans hum) (hK j).le) (hv' j).le
  calc P i j = u i * K i j * v j := hP i j
    _ ≤ u i * K i j * (v j₁ / v' j₁ * v' j) :=
        mul_le_mul_of_nonneg_left (hupper j) (mul_nonneg hu (hK j).le)
    _ = u i * (v j₂ / v' j₂) * K i j * v' j * (v j₁ / v' j₁ / (v j₂ / v' j₂)) := by
        have := (hv j₂).ne'
        have := (hv' j₂).ne'
        field_simp
    _ ≤ u' i * K i j * v' j * (v j₁ / v' j₁ / (v j₂ / v' j₂)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hum (hK j).le) (hv' j).le) (div_pos hM hm).le
    _ = v j₁ / v' j₁ / (v j₂ / v' j₂) * Q i j := by rw [hQ i j]; ring
    _ ≤ exp (hilbertProjectiveDist v v') * Q i j := mul_le_mul_of_nonneg_right hMm hQ0

end Matrix
