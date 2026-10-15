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
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Dual.Lemmas
import TauCeti.Analysis.SpecialFunctions.Log.MulLog

/-!
# The entropy minimiser with prescribed marginals and the Sinkhorn–Knopp theorem

Let `ι` and `κ` be finite types, let `a : ι → ℝ` and `b : κ → ℝ` be the row and the column sums,
and let `S` be the set of the nonnegative matrices `P : ι × κ → ℝ` whose row sums are `a` and
whose column sums are `b`. Against a fixed matrix `K : ι × κ → ℝ`, the relative entropy of `P`
attains a minimum on `S` as soon as `S` is nonempty, and for strictly positive marginals of equal
total mass every minimiser has strictly positive entries.

On a convex set of nonnegative matrices, a minimiser of the relative entropy has the largest
support (Csiszár's support property), which gives the positivity above. For a nonnegative `K` the
minimiser among the matrices vanishing wherever `K` does is a diagonal scaling
`P i j = u i * K i j * v j` of `K` by strictly positive factors, as soon as some competitor has the
zero pattern of `K`. At such a minimiser the relative entropy is differentiable along every
direction that preserves the marginals and vanishes off the support of `P`, and its derivative
vanishes there; a matrix orthogonal to all these directions is a function of the row plus a function
of the column on that support, and this splits `log (P i j) - log (K i j)`. A strictly positive `K`
is the case without zero entries. Conversely, Gibbs' inequality and the Pythagorean identity
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
minimiser hold for every `K`; nonnegativity of `K` and a competitor with its zero pattern are
needed only to identify the minimiser with a diagonal scaling of `K`. The resulting scaling
criterion for a kernel with zero entries is in `TauCeti.Data.Matrix.Scaling.Support`.

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

* `Matrix.isCompact_setOf_nonneg_hasMarginals`: the nonnegative matrices with row sums `a` and
  column sums `b` form a compact set.
* `Matrix.hasMarginals_mul_mul_inv`: the product coupling `a i * (b j * (∑ k, a k)⁻¹)` has row
  sums `a` and column sums `b` when these have the same nonzero total mass.
* `Matrix.exists_relEntropy_minOn`: a minimiser of `Matrix.relEntropy` against `K` among the
  nonnegative matrices with row sums `a` and column sums `b` exists, as soon as there is one such
  matrix.
* `Matrix.exists_relEntropy_minOn_of_pos`: the same, for strictly positive marginals `a` and `b` of
  equal total mass.
* `Matrix.convex_setOf_nonneg_hasMarginals`: these matrices form a convex set.
* `Matrix.pos_of_isMinOn_relEntropy`: a minimiser of the relative entropy over a convex set is
  positive wherever some nonnegative member of the set is.
* `Matrix.pos_of_relEntropy_minOn`: every minimiser with strictly positive marginals has strictly
  positive entries; `Matrix.pos_of_relEntropy_minOn_support` is the version among the matrices
  vanishing wherever `K` does.
* `Matrix.HasMarginals.add_vecMulVec_of_sum_eq_zero`: the row and column sums of a matrix are
  preserved by an outer product of a row weight and a column weight, each of total sum `0`.
* `Matrix.relEntropy_nonneg` and `Matrix.relEntropy_eq_zero_iff`: Gibbs' inequality for matrices
  of equal total mass, with its equality case; `Matrix.relEntropy_nonneg_of_nonneg` allows a
  reference with zero entries, on which the other matrix vanishes.
* `Matrix.hasDerivAt_relEntropy_add_smul`,
  `Matrix.sum_sum_mul_log_sub_log_eq_zero_of_relEntropy_minOn_support` and
  `Matrix.sum_sum_mul_log_sub_log_eq_zero_of_relEntropy_minOn`: the derivative of the relative
  entropy along a direction, and the first-order condition at a minimiser on its own support and at
  a positive minimiser.
* `Matrix.exists_forall_mem_eq_add_iff`: on a set `s` of cells, a matrix is `f i + g j` exactly
  when it is orthogonal to every matrix vanishing off `s` with zero row and column sums.
* `Matrix.exists_isDiagonalScaling_of_relEntropy_minOn_support`: for a nonnegative `K`, if some
  competitor has the zero pattern of `K`, the minimiser among the matrices vanishing wherever `K`
  does is a diagonal scaling of `K` by strictly positive factors.
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
  Ann. Probab. 3 (1975), 146--158, for the Pythagorean identity of the relative entropy and the
  support of a relative-entropy minimiser.
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

/-- The nonnegative matrices with row sums `a` and column sums `b` form a compact set.

The set is closed, and every entry of such a matrix is at most `∑ i, a i`, so it is a closed subset
of a compact box. -/
theorem isCompact_setOf_nonneg_hasMarginals (a : ι → ℝ) (b : κ → ℝ) :
    IsCompact {P : Matrix ι κ ℝ | (∀ i j, 0 ≤ P i j) ∧ HasMarginals P a b} := by
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
  exact IsCompact.of_isClosed_subset hbox hclosed
    fun P hP => fun i j => ⟨hP.1 i j, hbound P hP.1 hP.2 i j⟩

/-- The relative entropy against `K` attains a minimum on the nonnegative matrices with row sums `a`
and column sums `b`, as soon as there is one such matrix.

The set of these matrices is compact by `Matrix.isCompact_setOf_nonneg_hasMarginals`, and the
relative entropy is continuous. -/
theorem exists_relEntropy_minOn (K : Matrix ι κ ℝ) (a : ι → ℝ) (b : κ → ℝ)
    (hfeas : ∃ P : Matrix ι κ ℝ, (∀ i j, 0 ≤ P i j) ∧ HasMarginals P a b) :
    ∃ P : Matrix ι κ ℝ, (∀ i j, 0 ≤ P i j) ∧ HasMarginals P a b ∧
      ∀ Q : Matrix ι κ ℝ, (∀ i j, 0 ≤ Q i j) → HasMarginals Q a b →
        relEntropy P K ≤ relEntropy Q K := by
  obtain ⟨P, ⟨hP0, hPa⟩, hPmin⟩ :=
    (isCompact_setOf_nonneg_hasMarginals a b).exists_isMinOn (f := fun P => relEntropy P K)
      hfeas (continuous_relEntropy K).continuousOn
  exact ⟨P, hP0, hPa, fun Q hQ0 hQa => (isMinOn_iff.mp hPmin) Q ⟨hQ0, hQa⟩⟩

/-- For row sums `a` and column sums `b` of the same nonzero total mass `A = ∑ i, a i`, the product
coupling `a i * (b j * A⁻¹)` has row sums `a` and column sums `b`. -/
theorem hasMarginals_mul_mul_inv {a : ι → ℝ} {b : κ → ℝ} (hmass : (∑ i, a i) = ∑ j, b j)
    (hA : (∑ i, a i) ≠ 0) : HasMarginals (fun i j => a i * (b j * (∑ k, a k)⁻¹)) a b := by
  constructor
  · intro i
    rw [← Finset.mul_sum, ← Finset.sum_mul, ← hmass, mul_inv_cancel₀ hA, mul_one]
  · intro j
    rw [← Finset.sum_mul, mul_left_comm, mul_inv_cancel₀ hA, mul_one]

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
      exact ⟨fun i j => a i * (b j * (∑ k, a k)⁻¹),
        fun i j => mul_nonneg (ha i) (mul_nonneg (hb j) (inv_nonneg.mpr hApos.le)),
        hasMarginals_mul_mul_inv hmass hApos.ne'⟩
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

/-! ### The minimiser has the largest support -/

/-- The nonnegative matrices with row sums `a` and column sums `b` form a convex set. -/
theorem convex_setOf_nonneg_hasMarginals (a : ι → ℝ) (b : κ → ℝ) :
    Convex ℝ {P : Matrix ι κ ℝ | (∀ i j, 0 ≤ P i j) ∧ HasMarginals P a b} := by
  rintro M ⟨hM0, hMa⟩ N ⟨hN0, hNa⟩ s t hs ht hst
  refine ⟨fun i j => ?_, ?_⟩
  · simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg hs (hM0 i j)) (mul_nonneg ht (hN0 i j))
  · simpa only [Convex.combo_self hst] using (hMa.smul s).add (hNa.smul t)

/-- A minimiser `P` of the relative entropy against `K` over a convex set `C` of matrices has the
largest support among the nonnegative members of `C`: if `P` and some `Q ∈ C` are nonnegative,
then every entry at which `Q` is positive is a positive entry of `P`. There is no hypothesis on
`K`. -/
theorem pos_of_isMinOn_relEntropy {K : Matrix ι κ ℝ} {C : Set (Matrix ι κ ℝ)} (hC : Convex ℝ C)
    {P Q : Matrix ι κ ℝ} (hP0 : ∀ i j, 0 ≤ P i j) (hQ0 : ∀ i j, 0 ≤ Q i j) (hPC : P ∈ C)
    (hmin : IsMinOn (relEntropy · K) C P) (hQC : Q ∈ C) {i : ι} {j : κ} (hQ : 0 < Q i j) :
    0 < P i j := by
  classical
  refine (hP0 i j).lt_of_ne fun hPij => ?_
  -- Moving from `P` towards `Q` by `t` changes `x * log x` at the entry `(i, j)` by
  -- `t * Q i j * log (t * Q i j)`, and at every other entry by at most `t` times the change from
  -- `P` to `Q`, by convexity. For small `t` the logarithm of `t` dominates, and the relative
  -- entropy decreases.
  set q : ℝ := Q i j with hq
  set A : ℝ := ∑ x, ∑ y, (Q x y * Real.log (Q x y) - P x y * Real.log (P x y))
    - ∑ x, ∑ y, (Q x y - P x y) * Real.log (K x y) with hA
  set t : ℝ := Real.exp (-(|A| + 1) / q) with ht
  have ht0 : 0 < t := Real.exp_pos _
  have ht1 : t ≤ 1 := Real.exp_le_one_iff.mpr
    (div_nonpos_of_nonpos_of_nonneg (by linarith [abs_nonneg A]) hQ.le)
  have hlogt : q * Real.log t = -(|A| + 1) := by
    rw [ht, Real.log_exp]
    field_simp
  set R : Matrix ι κ ℝ := (1 - t) • P + t • Q with hR
  have hRapply : ∀ x y, R x y = (1 - t) * P x y + t * Q x y := fun x y => by
    simp [hR]
  have hRC : R ∈ C := hC hPC hQC (by linarith) ht0.le (by ring)
  have hcell : ∀ x y, R x y * Real.log (R x y) - P x y * Real.log (P x y) ≤
      t * (Q x y * Real.log (Q x y) - P x y * Real.log (P x y))
        + if x = i ∧ y = j then t * (q * Real.log t) else 0 := by
    intro x y
    split_ifs with hxy
    · obtain ⟨rfl, rfl⟩ := hxy
      rw [hRapply, ← hPij, ← hq, mul_zero, zero_add, Real.log_mul ht0.ne' hQ.ne']
      simp only [zero_mul, sub_zero]
      exact le_of_eq (by ring)
    · have hconv := Real.convexOn_mul_log.2 (Set.mem_Ici.2 (hP0 x y))
        (Set.mem_Ici.2 (hQ0 x y)) (by linarith : 0 ≤ 1 - t) ht0.le (by ring)
      simp only [smul_eq_mul] at hconv
      rw [hRapply]
      linarith
  have hdiff : relEntropy R K - relEntropy P K ≤ t * (A + q * Real.log t) := by
    have hsplit : relEntropy R K - relEntropy P K
        = ∑ x, ∑ y, (R x y * Real.log (R x y) - P x y * Real.log (P x y))
          - t * ∑ x, ∑ y, (Q x y - P x y) * Real.log (K x y) := by
      simp only [relEntropy_def, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      rw [hRapply]
      ring
    have hsum := Finset.sum_le_sum fun x (_ : x ∈ Finset.univ) =>
      Finset.sum_le_sum fun y (_ : y ∈ Finset.univ) => hcell x y
    have hδ : ∀ c : ℝ, ∑ x, ∑ y, (if x = i ∧ y = j then c else 0) = c := fun c => by
      rw [Finset.sum_eq_single i (fun x _ hx => by simp [hx]) (by simp)]
      simp
    have hite : ∑ x, ∑ y, (t * (Q x y * Real.log (Q x y) - P x y * Real.log (P x y))
        + if x = i ∧ y = j then t * (q * Real.log t) else 0)
        = t * ∑ x, ∑ y, (Q x y * Real.log (Q x y) - P x y * Real.log (P x y))
          + t * (q * Real.log t) := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum, hδ]
    rw [hsplit, hA]
    linarith
  have hneg : t * (A + q * Real.log t) < 0 :=
    mul_neg_of_pos_of_neg ht0 (by rw [hlogt]; linarith [le_abs_self A])
  have hle : relEntropy P K ≤ relEntropy R K := isMinOn_iff.mp hmin R hRC
  linarith

/-- A minimiser of the relative entropy against `K` among the nonnegative matrices with strictly
positive row sums `a` and column sums `b` has no zero entry, for every matrix `K`: the product
coupling `a i * b j / ∑ k, a k` is a strictly positive competitor, so this is the case of
`Matrix.pos_of_isMinOn_relEntropy` for the convex set of these matrices. -/
theorem pos_of_relEntropy_minOn (K : Matrix ι κ ℝ) (a : ι → ℝ) (b : κ → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j) {P : Matrix ι κ ℝ} (hP : ∀ i j, 0 ≤ P i j)
    (hPa : HasMarginals P a b)
    (hmin : ∀ Q : Matrix ι κ ℝ, (∀ i j, 0 ≤ Q i j) → HasMarginals Q a b →
      relEntropy P K ≤ relEntropy Q K) :
    ∀ i j, 0 < P i j := by
  intro i j
  have hmass : (∑ i, a i) = ∑ j, b j := by
    simp_rw [← hPa.1, ← hPa.2]
    exact Finset.sum_comm
  have hA : 0 < ∑ k, a k := Finset.sum_pos (fun k _ => ha k) ⟨i, Finset.mem_univ i⟩
  have hQ0 : ∀ i j, 0 ≤ a i * (b j * (∑ k, a k)⁻¹) := fun i j =>
    (mul_pos (ha i) (mul_pos (hb j) (inv_pos.mpr hA))).le
  exact pos_of_isMinOn_relEntropy (convex_setOf_nonneg_hasMarginals a b) hP hQ0 ⟨hP, hPa⟩
    (isMinOn_iff.mpr fun M hM => hmin M hM.1 hM.2) ⟨hQ0, hasMarginals_mul_mul_inv hmass hA.ne'⟩
    (mul_pos (ha i) (mul_pos (hb j) (inv_pos.mpr hA)))

/-- A minimiser of the relative entropy against `K` among the nonnegative matrices with row sums
`a` and column sums `b` that vanish wherever `K` does is positive at every entry where some such
matrix is positive. -/
theorem pos_of_relEntropy_minOn_support {K : Matrix ι κ ℝ} {a : ι → ℝ} {b : κ → ℝ}
    {P Q : Matrix ι κ ℝ} (hP : ∀ i j, 0 ≤ P i j) (hPa : HasMarginals P a b)
    (hPK : ∀ i j, K i j = 0 → P i j = 0)
    (hmin : ∀ Q : Matrix ι κ ℝ, (∀ i j, 0 ≤ Q i j) → HasMarginals Q a b →
      (∀ i j, K i j = 0 → Q i j = 0) → relEntropy P K ≤ relEntropy Q K)
    (hQ : ∀ i j, 0 ≤ Q i j) (hQa : HasMarginals Q a b) (hQK : ∀ i j, K i j = 0 → Q i j = 0)
    {i : ι} {j : κ} (hQij : 0 < Q i j) : 0 < P i j := by
  have hC : Convex ℝ ({M : Matrix ι κ ℝ | (∀ i j, 0 ≤ M i j) ∧ HasMarginals M a b} ∩
      {M | ∀ i j, K i j = 0 → M i j = 0}) :=
    (convex_setOf_nonneg_hasMarginals a b).inter fun M hM N hN s t _ _ _ i j h => by
      simp [Set.mem_ofPred_eq.mp hM i j h, Set.mem_ofPred_eq.mp hN i j h]
  exact pos_of_isMinOn_relEntropy hC hP hQ ⟨⟨hP, hPa⟩, hPK⟩
    (isMinOn_iff.mpr fun M hM => hmin M hM.1.1 hM.1.2 hM.2) ⟨⟨hQ, hQa⟩, hQK⟩ hQij

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

/-- Gibbs' inequality against a reference with zero entries: the relative entropy of a nonnegative
matrix `Q` against a nonnegative matrix `P` of the same total mass is nonnegative, provided `Q`
vanishes wherever `P` does. -/
theorem relEntropy_nonneg_of_nonneg {P Q : Matrix ι κ ℝ} (hQ : ∀ i j, 0 ≤ Q i j)
    (hP : ∀ i j, 0 ≤ P i j) (hQP : ∀ i j, P i j = 0 → Q i j = 0)
    (hmass : ∑ i, ∑ j, Q i j = ∑ i, ∑ j, P i j) : 0 ≤ relEntropy Q P := by
  -- Each cell satisfies `Q - P ≤ Q * log Q - Q * log P`, and the left sides add up to `0`.
  have hcell : ∀ i j, Q i j - P i j ≤ Q i j * Real.log (Q i j) - Q i j * Real.log (P i j) := by
    intro i j
    rcases (hP i j).eq_or_lt with h | h
    · simp [hQP i j h.symm, ← h]
    · linarith [Real.mul_log_sub_mul_log_ge (P i j) (Q i j) h (hQ i j)]
  calc (0 : ℝ) = ∑ i, ∑ j, (Q i j - P i j) := by simp [Finset.sum_sub_distrib, hmass]
    _ ≤ relEntropy Q P := by
      rw [relEntropy_def]
      exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hcell i j

/-- Gibbs' inequality: the relative entropy of a nonnegative matrix `Q` against a strictly positive
matrix `P` of the same total mass is nonnegative. -/
theorem relEntropy_nonneg {P Q : Matrix ι κ ℝ} (hQ : ∀ i j, 0 ≤ Q i j) (hP : ∀ i j, 0 < P i j)
    (hmass : ∑ i, ∑ j, Q i j = ∑ i, ∑ j, P i j) : 0 ≤ relEntropy Q P :=
  relEntropy_nonneg_of_nonneg hQ (fun i j => (hP i j).le) (fun i j h => absurd h (hP i j).ne')
    hmass

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

/-! ### The first-order condition at a minimiser -/

/-- The relative entropy against `K` of the matrix `P + t • D` has derivative
`∑ i, ∑ j, D i j * (log (P i j) + 1 - log (K i j))` in `t` at `t = 0`, as soon as `D` vanishes
wherever `P` does. -/
theorem hasDerivAt_relEntropy_add_smul (K P D : Matrix ι κ ℝ)
    (hDP : ∀ i j, P i j = 0 → D i j = 0) :
    HasDerivAt (fun t : ℝ => relEntropy (P + t • D) K)
      (∑ i, ∑ j, D i j * (Real.log (P i j) + 1 - Real.log (K i j))) 0 := by
  simp only [relEntropy_def, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  refine HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun j _ => ?_
  by_cases hP : P i j = 0
  · -- On a zero entry of `P` the direction vanishes too, so the entry stays `0`.
    simpa [hP, hDP i j hP] using hasDerivAt_const (0 : ℝ) (0 : ℝ)
  have hlin : HasDerivAt (fun t : ℝ => P i j + t * D i j) (D i j) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (D i j)).const_add (P i j)
  have hlog :
      HasDerivAt (fun x => x * Real.log x) (Real.log (P i j) + 1) (P i j + 0 * D i j) := by
    simpa using Real.hasDerivAt_mul_log hP
  refine ((hlog.comp 0 hlin).sub (hlin.mul_const (Real.log (K i j)))).congr_deriv ?_
  ring

/-- The first-order condition at a minimiser on its own support: if `P` minimises the relative
entropy against `K` among the nonnegative matrices with row sums `a` and column sums `b` that
vanish wherever `P` does, then the matrix `log (P i j) - log (K i j)` is orthogonal to every
direction `D` whose row and column sums vanish and which vanishes wherever `P` does. -/
theorem sum_sum_mul_log_sub_log_eq_zero_of_relEntropy_minOn_support (K : Matrix ι κ ℝ)
    {a : ι → ℝ} {b : κ → ℝ} {P D : Matrix ι κ ℝ} (hP : ∀ i j, 0 ≤ P i j)
    (hPa : HasMarginals P a b)
    (hmin : ∀ Q : Matrix ι κ ℝ, (∀ i j, 0 ≤ Q i j) → HasMarginals Q a b →
      (∀ i j, P i j = 0 → Q i j = 0) → relEntropy P K ≤ relEntropy Q K)
    (hD : HasMarginals D 0 0) (hDP : ∀ i j, P i j = 0 → D i j = 0) :
    ∑ i, ∑ j, D i j * (Real.log (P i j) - Real.log (K i j)) = 0 := by
  -- For `t` near `0` the matrix `P + t • D` is still nonnegative, vanishes wherever `P` does and
  -- has the marginals of `P`, so `t = 0` is a local minimum of its relative entropy.
  have hzero : ∀ t : ℝ, ∀ i j, P i j = 0 → (P + t • D) i j = 0 := fun t i j h => by
    simp [h, hDP i j h]
  have hloc : IsLocalMin (fun t : ℝ => relEntropy (P + t • D) K) 0 := by
    have hpos : ∀ᶠ t in nhds (0 : ℝ), ∀ i j, 0 ≤ (P + t • D) i j := by
      simp only [Filter.eventually_all]
      intro i j
      rcases (hP i j).eq_or_lt with h | h
      · exact Filter.Eventually.of_forall fun t => (hzero t i j h.symm).ge
      have hc : Continuous fun t : ℝ => (P + t • D) i j := by
        simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
        fun_prop
      exact (continuousAt_const.eventually_lt hc.continuousAt (by simpa using h)).mono
        fun _ ht => ht.le
    refine hpos.mono fun t ht => ?_
    simpa using hmin _ ht (by simpa using hPa.add (hD.smul t)) (hzero t)
  have hderiv := hloc.hasDerivAt_eq_zero (hasDerivAt_relEntropy_add_smul K P D hDP)
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

/-- The first-order condition at a minimiser with positive entries: if `P` minimises the relative
entropy against `K` among the nonnegative matrices with row sums `a` and column sums `b`, and
every entry of `P` is positive, then the matrix `log (P i j) - log (K i j)` is orthogonal to every
direction `D` whose row and column sums vanish. -/
theorem sum_sum_mul_log_sub_log_eq_zero_of_relEntropy_minOn (K : Matrix ι κ ℝ) {a : ι → ℝ}
    {b : κ → ℝ} {P D : Matrix ι κ ℝ} (hP : ∀ i j, 0 < P i j) (hPa : HasMarginals P a b)
    (hmin : ∀ Q : Matrix ι κ ℝ, (∀ i j, 0 ≤ Q i j) → HasMarginals Q a b →
      relEntropy P K ≤ relEntropy Q K)
    (hD : HasMarginals D 0 0) :
    ∑ i, ∑ j, D i j * (Real.log (P i j) - Real.log (K i j)) = 0 :=
  sum_sum_mul_log_sub_log_eq_zero_of_relEntropy_minOn_support K (fun i j => (hP i j).le) hPa
    (fun Q hQ hQa _ => hmin Q hQ hQa) hD fun i j h => absurd h (hP i j).ne'

/-! ### Matrices orthogonal to the zero-marginal directions on a support -/

/-- On a set `s` of cells, a matrix `H` is the sum `f i + g j` of a function of the row and a
function of the column exactly when `∑ i, ∑ j, D i j * H i j = 0` for every matrix `D` that
vanishes off `s` and has zero row and column sums. -/
theorem exists_forall_mem_eq_add_iff (H : Matrix ι κ ℝ) (s : Set (ι × κ)) :
    (∃ (f : ι → ℝ) (g : κ → ℝ), ∀ i j, (i, j) ∈ s → H i j = f i + g j) ↔
      ∀ D : Matrix ι κ ℝ, (∀ i j, (i, j) ∉ s → D i j = 0) → HasMarginals D 0 0 →
        ∑ i, ∑ j, D i j * H i j = 0 := by
  classical
  constructor
  · rintro ⟨f, g, hfg⟩ D hDs hD
    calc ∑ i, ∑ j, D i j * H i j = ∑ i, ∑ j, D i j * (f i + g j) := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          by_cases h : (i, j) ∈ s
          · rw [hfg i j h]
          · rw [hDs i j h, zero_mul, zero_mul]
      _ = 0 := by simp [hD.sum_sum_mul_add f g]
  · intro hH
    -- The matrices equal to `f i + g j` on `s` and to `0` off `s` form the range of `T`, and `H`
    -- restricted to `s` lies in it because every functional killing that range kills `H`.
    let T : ((ι → ℝ) × (κ → ℝ)) →ₗ[ℝ] Matrix ι κ ℝ :=
      { toFun := fun fg => of fun i j => if (i, j) ∈ s then fg.1 i + fg.2 j else 0
        map_add' := fun x y => by
          ext i j
          simp only [of_apply, Prod.fst_add, Prod.snd_add, Pi.add_apply, Matrix.add_apply]
          split_ifs <;> ring
        map_smul' := fun c x => by
          ext i j
          simp only [of_apply, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
            RingHom.id_apply, Matrix.smul_apply]
          split_ifs <;> ring }
    have hT : ∀ fg i j, T fg i j = if (i, j) ∈ s then fg.1 i + fg.2 j else 0 :=
      fun _ _ _ => of_apply _ _ _
    -- A linear functional on matrices is the pairing with its values on the matrix units.
    have hφ : ∀ (φ : Module.Dual ℝ (Matrix ι κ ℝ)) (M : Matrix ι κ ℝ),
        φ M = ∑ i, ∑ j, M i j * φ (Matrix.single i j 1) := by
      intro φ M
      conv_lhs => rw [matrix_eq_sum_single M]
      simp only [map_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [← smul_eq_mul, ← map_smul, smul_single, smul_eq_mul, mul_one]
    have hmem : of (fun i j => if (i, j) ∈ s then H i j else 0) ∈ LinearMap.range T := by
      refine (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff (LinearMap.range T) _).mp
        fun φ hφT => ?_
      rw [Submodule.mem_dualAnnihilator] at hφT
      set D : Matrix ι κ ℝ := of fun i j => if (i, j) ∈ s then φ (Matrix.single i j 1) else 0
        with hD_def
      have hTD : ∀ fg : (ι → ℝ) × (κ → ℝ), ∑ i, ∑ j, D i j * (fg.1 i + fg.2 j) = 0 := by
        intro fg
        rw [← hφT (T fg) (LinearMap.mem_range_self T fg), hφ]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [hT, hD_def, of_apply]
        split_ifs <;> ring
      have hD : HasMarginals D 0 0 := by
        refine (hasMarginals_def _ _ _).2 ⟨fun i => ?_, fun j => ?_⟩
        · simpa [Pi.single_apply] using hTD (Pi.single i 1, 0)
        · simpa [Pi.single_apply] using hTD (0, Pi.single j 1)
      have hDs : ∀ i j, (i, j) ∉ s → D i j = 0 := fun i j h => by
        rw [hD_def, of_apply, ite_eq_right_iff.2 fun h' => absurd h' h]
      rw [hφ]
      refine Eq.trans ?_ (hH D hDs hD)
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hD_def, of_apply, of_apply]
      split_ifs <;> ring
    obtain ⟨fg, hfg⟩ := hmem
    refine ⟨fg.1, fg.2, fun i j hij => ?_⟩
    have h := congrFun (congrFun hfg i) j
    rw [hT, of_apply, ite_eq_left_iff.2 fun h' => absurd hij h',
      ite_eq_left_iff.2 fun h' => absurd hij h'] at h
    exact h.symm

/-! ### The minimiser is a diagonal scaling -/

/-- If some nonnegative matrix with row sums `a` and column sums `b` has the zero pattern of the
nonnegative kernel `K`, then every minimiser of the relative entropy against `K` among the
nonnegative matrices with these row and column sums that vanish wherever `K` does is a diagonal
scaling of `K` by strictly positive row and column factors. -/
theorem exists_isDiagonalScaling_of_relEntropy_minOn_support {K : Matrix ι κ ℝ}
    (hK : ∀ i j, 0 ≤ K i j) {a : ι → ℝ} {b : κ → ℝ} {P Q : Matrix ι κ ℝ}
    (hP : ∀ i j, 0 ≤ P i j) (hPa : HasMarginals P a b) (hPK : ∀ i j, K i j = 0 → P i j = 0)
    (hmin : ∀ Q : Matrix ι κ ℝ, (∀ i j, 0 ≤ Q i j) → HasMarginals Q a b →
      (∀ i j, K i j = 0 → Q i j = 0) → relEntropy P K ≤ relEntropy Q K)
    (hQ : ∀ i j, 0 ≤ Q i j) (hQa : HasMarginals Q a b) (hQK : ∀ i j, Q i j = 0 ↔ K i j = 0) :
    ∃ (u : ι → ℝ) (v : κ → ℝ), (∀ i, 0 < u i) ∧ (∀ j, 0 < v j) ∧ IsDiagonalScaling P K u v := by
  -- The minimiser has the zero pattern of `Q`, which is that of `K`.
  have hPpos : ∀ i j, K i j ≠ 0 → 0 < P i j := fun i j h =>
    pos_of_relEntropy_minOn_support hP hPa hPK hmin hQ hQa (fun i j h => (hQK i j).2 h)
      ((hQ i j).lt_of_ne fun h' => h ((hQK i j).1 h'.symm))
  have hPK' : ∀ i j, P i j = 0 ↔ K i j = 0 := fun i j =>
    ⟨fun h => by_contra fun hK0 => (hPpos i j hK0).ne' h, hPK i j⟩
  -- On the support of `K`, the first-order condition makes `log P - log K` a function of the row
  -- plus a function of the column.
  obtain ⟨f, g, hfg⟩ := (exists_forall_mem_eq_add_iff
    (fun i j => Real.log (P i j) - Real.log (K i j)) {x : ι × κ | K x.1 x.2 ≠ 0}).2 fun D hDs hD =>
      sum_sum_mul_log_sub_log_eq_zero_of_relEntropy_minOn_support K hP hPa
        (fun Q hQ hQa hQP => hmin Q hQ hQa fun i j h => hQP i j ((hPK' i j).2 h)) hD
        fun i j h => hDs i j fun hs => (Set.mem_ofPred.mp hs) ((hPK' i j).1 h)
  refine ⟨fun i => Real.exp (f i), fun j => Real.exp (g j), fun _ => Real.exp_pos _,
    fun _ => Real.exp_pos _, (isDiagonalScaling_def _ _ _ _).2 fun i j => ?_⟩
  by_cases hKij : K i j = 0
  · simp [hPK i j hKij, hKij]
  have hK' : 0 < K i j := (hK i j).lt_of_ne' hKij
  calc P i j = Real.exp (Real.log (P i j) - Real.log (K i j)) * K i j := by
        rw [Real.exp_sub, Real.exp_log (hPpos i j hKij), Real.exp_log hK',
          div_mul_cancel₀ _ hK'.ne']
    _ = Real.exp (f i) * K i j * Real.exp (g j) := by
        rw [hfg i j hKij, Real.exp_add]
        ring

/-- For a strictly positive kernel `K` and strictly positive marginals `a` and `b`, every minimiser
`P` of the relative entropy against `K` among the nonnegative matrices with row sums `a` and column
sums `b` is a diagonal scaling of `K` by strictly positive row and column factors.

This is the case of `Matrix.exists_isDiagonalScaling_of_relEntropy_minOn_support` in which `K` has
no zero entry: `P` itself has no zero entry by `Matrix.pos_of_relEntropy_minOn`. -/
theorem exists_isDiagonalScaling_of_relEntropy_minOn {K : Matrix ι κ ℝ} (hK : ∀ i j, 0 < K i j)
    {a : ι → ℝ} {b : κ → ℝ} (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j) {P : Matrix ι κ ℝ}
    (hP : ∀ i j, 0 ≤ P i j) (hPa : HasMarginals P a b)
    (hmin : ∀ Q : Matrix ι κ ℝ, (∀ i j, 0 ≤ Q i j) → HasMarginals Q a b →
      relEntropy P K ≤ relEntropy Q K) :
    ∃ (u : ι → ℝ) (v : κ → ℝ), (∀ i, 0 < u i) ∧ (∀ j, 0 < v j) ∧ IsDiagonalScaling P K u v := by
  have hPpos := pos_of_relEntropy_minOn K a b ha hb hP hPa hmin
  exact exists_isDiagonalScaling_of_relEntropy_minOn_support (fun i j => (hK i j).le) hP hPa
    (fun i j h => absurd h (hK i j).ne') (fun Q hQ hQa _ => hmin Q hQ hQa) hP hPa
    fun i j => ⟨fun h => absurd h (hPpos i j).ne', fun h => absurd h (hK i j).ne'⟩

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
