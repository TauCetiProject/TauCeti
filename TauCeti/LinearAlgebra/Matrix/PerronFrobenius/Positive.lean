/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Algebra.Spectrum
public import Mathlib.LinearAlgebra.Eigenspace.Matrix
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.Topology.Instances.Matrix

/-!
# The Perron–Frobenius theorem for positive matrices

A square real matrix all of whose entries are strictly positive has an eigenvector all of whose
entries are strictly positive, for a positive eigenvalue `r`, the **Perron root**. This eigenvector
is unique up to a scalar: every eigenvector for `r`, of any sign, is a multiple of it, and every
nonzero entrywise nonnegative eigenvector, for any eigenvalue, is a positive multiple of it.
Finally `r` is the spectral radius: every complex eigenvalue has modulus at most `r`.

The comparison arguments work over any linearly ordered field. Their heart is the Collatz–Wielandt
bound: if `A` is entrywise nonnegative and `A v = r v` with `v` strictly positive, then `t y ≤ A y`
for a nonzero nonnegative `y` forces `t ≤ r`. This bound, and with it the spectral radius
statement, needs only nonnegativity of `A` once a strictly positive eigenvector is given.
Existence is specific to `ℝ`: the Perron root is the largest `t` for which some point `x` of the
standard simplex satisfies `t x ≤ A x`, and the maximum exists by compactness.

These are the statements used to define the Frobenius–Perron dimension of a based ring: there one
applies them to the matrix of multiplication by the sum of all basis elements, which is strictly
positive, and uses the uniqueness of nonnegative eigenvectors to see that the other structure
matrices act on the Perron eigenvector by scalars.

## Main results

* `Matrix.mulVec_pos`: a strictly positive matrix sends a nonzero nonnegative vector to a strictly
  positive one.
* `Matrix.le_of_smul_le_mulVec`: the Collatz–Wielandt bound against a positive eigenvector.
* `Matrix.exists_eq_smul_of_mulVec_eq_smul`: for a strictly positive matrix, the eigenspace of a
  strictly positive eigenvector is spanned by it.
* `Matrix.eq_of_mulVec_eq_smul_of_nonneg` and `Matrix.exists_pos_eq_smul_of_mulVec_eq_smul`:
  a nonzero nonnegative eigenvector of a strictly positive matrix has the Perron root as
  eigenvalue, and is a positive multiple of the Perron eigenvector.
* `Matrix.exists_mulVec_eq_smul_of_pos`: a strictly positive real matrix has a strictly positive
  eigenvector with positive eigenvalue.
* `Matrix.norm_le_of_mulVec_eq_smul` and `Matrix.spectralRadius_eq_of_mulVec_eq_smul`: the
  eigenvalue of a strictly positive eigenvector of a nonnegative real matrix bounds the modulus of
  every complex eigenvalue, and is the spectral radius.

## References

* E. Seneta, *Non-negative Matrices and Markov Chains*, Springer (2006), Chapter 1.
* P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor Categories*, Mathematical Surveys and
  Monographs **205**, AMS (2015), Sections 3.2 (the Frobenius–Perron theorem) and 3.3
  (Frobenius–Perron dimensions).
-/

public section

open scoped Matrix

namespace Matrix

variable {n : Type*} [Fintype n]

section OrderedSemiring

variable {R : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R] {A : Matrix n n R}
  {x y : n → R}

/-- Multiplication by an entrywise nonnegative matrix is monotone. -/
theorem mulVec_mono (hA : ∀ i j, 0 ≤ A i j) (hxy : x ≤ y) : A *ᵥ x ≤ A *ᵥ y := fun i =>
  dotProduct_le_dotProduct_of_nonneg_left hxy (hA i)

/-- An entrywise nonnegative matrix sends nonnegative vectors to nonnegative vectors. -/
theorem mulVec_nonneg (hA : ∀ i j, 0 ≤ A i j) (hx : 0 ≤ x) : 0 ≤ A *ᵥ x := fun i =>
  dotProduct_nonneg_of_nonneg (hA i) hx

end OrderedSemiring

section StrictOrderedSemiring

variable {R : Type*} [Semiring R] [PartialOrder R] [IsStrictOrderedRing R] {A : Matrix n n R}
  {y : n → R}

/-- A strictly positive matrix sends a nonzero nonnegative vector to a vector all of whose entries
are strictly positive. -/
theorem mulVec_pos (hA : ∀ i j, 0 < A i j) (hy : 0 ≤ y) (hy0 : y ≠ 0) (i : n) :
    0 < (A *ᵥ y) i := by
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hy0
  exact Finset.sum_pos' (fun k _ => mul_nonneg (hA i k).le (hy k))
    ⟨j, Finset.mem_univ j, mul_pos (hA i j) ((hy j).lt_of_ne' hj)⟩

end StrictOrderedSemiring

section OrderedField

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {A : Matrix n n K}
  {v w y : n → K} {r μ t : K}

/-- **Collatz–Wielandt bound.** Let `A` be entrywise nonnegative with an eigenvector `v` all of
whose entries are strictly positive, for the eigenvalue `r`. If `t y ≤ A y` entrywise for some
nonzero nonnegative vector `y`, then `t ≤ r`. -/
theorem le_of_smul_le_mulVec (hA : ∀ i j, 0 ≤ A i j) (hv : ∀ i, 0 < v i)
    (hAv : A *ᵥ v = r • v) (hy : 0 ≤ y) (hy0 : y ≠ 0) (h : t • y ≤ A *ᵥ y) : t ≤ r := by
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hy0
  have : Nonempty n := ⟨j⟩
  -- Compare `y` with the smallest multiple `c • v` lying above it, at a coordinate `i` where
  -- the two agree.
  obtain ⟨i, hi⟩ := Finite.exists_max fun i => y i / v i
  set c := y i / v i
  have hyc : y ≤ c • v := fun k => by
    simpa [mul_comm] using (div_le_iff₀ (hv k)).1 (hi k)
  have hyi : y i = c * v i := (div_mul_cancel₀ _ (hv i).ne').symm
  have hc : 0 < c := (div_pos ((hy j).lt_of_ne' hj) (hv j)).trans_le (hi j)
  have key : t * y i ≤ r * y i :=
    calc t * y i = (t • y) i := by rw [Pi.smul_apply, smul_eq_mul]
      _ ≤ (A *ᵥ y) i := h i
      _ ≤ (A *ᵥ (c • v)) i := mulVec_mono hA hyc i
      _ = r * y i := by simp [mulVec_smul, hAv, hyi, mul_left_comm]
  exact le_of_mul_le_mul_right key (hyi ▸ mul_pos hc (hv i))

/-- A nonzero nonnegative eigenvector of a strictly positive matrix has all entries strictly
positive. -/
theorem pos_of_mulVec_eq_smul (hA : ∀ i j, 0 < A i j) (hw : 0 ≤ w) (hw0 : w ≠ 0)
    (hAw : A *ᵥ w = μ • w) (i : n) : 0 < w i := by
  have h : ∀ k, 0 < μ * w k := fun k => by
    simpa [hAw] using mulVec_pos hA hw hw0 k
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hw0
  exact pos_of_mul_pos_right (h i) (pos_of_mul_pos_left (h j) (hw j)).le

/-- For a strictly positive matrix, the eigenspace of an eigenvector `v` with strictly positive
entries is spanned by `v`: every eigenvector for the same eigenvalue, of any sign, is a multiple
of `v`. -/
theorem exists_eq_smul_of_mulVec_eq_smul (hA : ∀ i j, 0 < A i j) (hv : ∀ i, 0 < v i)
    (hAv : A *ᵥ v = r • v) (hAw : A *ᵥ w = r • w) : ∃ c : K, w = c • v := by
  cases isEmpty_or_nonempty n
  · exact ⟨0, Subsingleton.elim _ _⟩
  -- Subtract the largest multiple of `v` lying below `w`; the difference is a nonnegative
  -- eigenvector with a zero entry, hence zero.
  obtain ⟨i, hi⟩ := Finite.exists_min fun i => w i / v i
  set c := w i / v i
  refine ⟨c, ?_⟩
  have hx : 0 ≤ w - c • v := fun k => by
    simpa [mul_comm] using (le_div_iff₀ (hv k)).1 (hi k)
  have hxi : (w - c • v) i = 0 := by simp [c, div_mul_cancel₀ _ (hv i).ne']
  have hAx : A *ᵥ (w - c • v) = r • (w - c • v) := by
    rw [mulVec_sub, mulVec_smul, hAv, hAw, smul_sub, smul_comm]
  by_contra hne
  have := mulVec_pos hA hx (sub_ne_zero.2 hne) i
  simp [hAx, hxi] at this

/-- A nonzero nonnegative eigenvector of a strictly positive matrix has the same eigenvalue as any
eigenvector with strictly positive entries. -/
theorem eq_of_mulVec_eq_smul_of_nonneg (hA : ∀ i j, 0 < A i j) (hv : ∀ i, 0 < v i)
    (hAv : A *ᵥ v = r • v) (hw : 0 ≤ w) (hw0 : w ≠ 0) (hAw : A *ᵥ w = μ • w) : μ = r := by
  have hA' : ∀ i j, 0 ≤ A i j := fun i j => (hA i j).le
  refine le_antisymm (le_of_smul_le_mulVec hA' hv hAv hw hw0 hAw.ge) ?_
  have hv0 : v ≠ 0 := by
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hw0
    exact fun h => (hv j).ne' (congrFun h j)
  exact le_of_smul_le_mulVec hA' (pos_of_mulVec_eq_smul hA hw hw0 hAw) hAw
    (fun i => (hv i).le) hv0 hAv.ge

/-- A nonzero nonnegative eigenvector of a strictly positive matrix is a positive multiple of any
eigenvector with strictly positive entries, whatever eigenvalue it was taken for. -/
theorem exists_pos_eq_smul_of_mulVec_eq_smul (hA : ∀ i j, 0 < A i j) (hv : ∀ i, 0 < v i)
    (hAv : A *ᵥ v = r • v) (hw : 0 ≤ w) (hw0 : w ≠ 0) (hAw : A *ᵥ w = μ • w) :
    ∃ c : K, 0 < c ∧ w = c • v := by
  obtain rfl := eq_of_mulVec_eq_smul_of_nonneg hA hv hAv hw hw0 hAw
  obtain ⟨c, rfl⟩ := exists_eq_smul_of_mulVec_eq_smul hA hv hAv hAw
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hw0
  refine ⟨c, pos_of_mul_pos_left ?_ (hv j).le, rfl⟩
  simpa using pos_of_mulVec_eq_smul hA hw hw0 hAw j

/-- If `r x ≤ A x` for a nonzero nonnegative vector `x` and a strictly positive matrix `A`, but `x`
is not an eigenvector for `r`, then some probability vector `y` satisfies `(r + ε) y ≤ A y` for
some `ε > 0`: namely `A x`, rescaled. -/
private theorem exists_add_smul_le_mulVec {x : n → K} (hA : ∀ i j, 0 < A i j) (hx : 0 ≤ x)
    (hx0 : x ≠ 0) (hxr : r • x ≤ A *ᵥ x) (hne : A *ᵥ x ≠ r • x) :
    ∃ ε : K, 0 < ε ∧ ∃ y : n → K, 0 ≤ y ∧ ∑ i, y i = 1 ∧ (r + ε) • y ≤ A *ᵥ y := by
  obtain ⟨j₀, -⟩ := Function.ne_iff.1 hx0
  have : Nonempty n := ⟨j₀⟩
  have hAx := mulVec_pos hA hx hx0
  -- The defect `z = A x - r x` is nonnegative and nonzero, so `A z` is strictly positive, and
  -- `A (A x) = A z + r (A x)` beats `r (A x)` by a uniform proportion `ε` of `A x`.
  set z := A *ᵥ x - r • x
  have hAz := mulVec_pos hA (sub_nonneg.2 hxr) (sub_ne_zero.2 hne)
  obtain ⟨i, hi⟩ := Finite.exists_min fun i => (A *ᵥ z) i / (A *ᵥ x) i
  have hy : (r + (A *ᵥ z) i / (A *ᵥ x) i) • (A *ᵥ x) ≤ A *ᵥ (A *ᵥ x) := fun j => by
    have h₁ := (le_div_iff₀ (hAx j)).1 (hi j)
    have h₂ : A *ᵥ (A *ᵥ x) = A *ᵥ z + r • (A *ᵥ x) := by simp [z, mulVec_sub, mulVec_smul]
    simp only [h₂, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linarith
  set s := ∑ j, (A *ᵥ x) j
  have hs : 0 < s := Finset.sum_pos (fun j _ => hAx j) Finset.univ_nonempty
  refine ⟨_, div_pos (hAz i) (hAx i), s⁻¹ • A *ᵥ x,
    smul_nonneg (inv_nonneg.2 hs.le) fun j => (hAx j).le, by simp [← Finset.mul_sum, s, hs.ne'], ?_⟩
  rw [mulVec_smul, smul_comm]
  exact smul_le_smul_of_nonneg_left hy (inv_nonneg.2 hs.le)

end OrderedField

section Real

variable {A : Matrix n n ℝ} {v : n → ℝ} {r : ℝ}

/-- If `t x ≤ A x` for a probability vector `x` and a nonnegative matrix `A`, then `t` is at most
the sum of the entries of `A`. This bounds the set maximized in the existence proof. -/
private theorem le_sum_of_smul_le_mulVec (hA : ∀ i j, 0 ≤ A i j) {x : n → ℝ} {t : ℝ}
    (hx : 0 ≤ x) (hx1 : ∑ i, x i = 1) (h : t • x ≤ A *ᵥ x) : t ≤ ∑ i, ∑ j, A i j :=
  calc t = ∑ i, t * x i := by rw [← Finset.mul_sum, hx1, mul_one]
    _ ≤ ∑ i, (A *ᵥ x) i := Finset.sum_le_sum fun i _ => h i
    _ ≤ ∑ i, ∑ j, A i j := Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
        mul_le_of_le_one_right (hA i j)
          (hx1 ▸ Finset.single_le_sum (fun k _ => hx k) (Finset.mem_univ j))

/-- The pairs `(x, t)` with `x` a probability vector, `t ∈ [0, M]` and `t x ≤ A x` form a compact
set. When `M` is the sum of the entries of `A`, the Perron root is the largest `t` occurring in it.
-/
private theorem isCompact_setOf_smul_le_mulVec (A : Matrix n n ℝ) (M : ℝ) :
    IsCompact {p : (n → ℝ) × ℝ |
      0 ≤ p.1 ∧ ∑ i, p.1 i = 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ M ∧ p.2 • p.1 ≤ A *ᵥ p.1} := by
  refine (isCompact_Icc (a := ((0 : n → ℝ), (0 : ℝ))) (b := (1, M))).of_isClosed_subset ?_ ?_
  · simp only [Set.ofPred_and]
    refine (isClosed_le continuous_const continuous_fst).inter <|
      (isClosed_eq (by fun_prop) continuous_const).inter <|
      (isClosed_le continuous_const continuous_snd).inter <|
      (isClosed_le continuous_snd continuous_const).inter <|
      isClosed_le (continuous_snd.smul continuous_fst)
        (continuous_const.matrix_mulVec continuous_fst)
  · rintro ⟨x, t⟩ ⟨hx, hx1, ht, htM, -⟩
    exact ⟨⟨hx, ht⟩,
      fun j => (Finset.single_le_sum (fun k _ => hx k) (Finset.mem_univ j)).trans_eq hx1, htM⟩

/-- **Perron–Frobenius theorem for positive matrices**, existence: a real square matrix whose
entries are all strictly positive has an eigenvector whose entries are all strictly positive, for a
strictly positive eigenvalue.

This eigenvalue is the spectral radius (`Matrix.spectralRadius_eq_of_mulVec_eq_smul`), and the
eigenvector is unique up to a scalar (`Matrix.exists_eq_smul_of_mulVec_eq_smul`). -/
theorem exists_mulVec_eq_smul_of_pos [Nonempty n] (hA : ∀ i j, 0 < A i j) :
    ∃ r : ℝ, 0 < r ∧ ∃ v : n → ℝ, (∀ i, 0 < v i) ∧ A *ᵥ v = r • v := by
  classical
  have hA' : ∀ i j, 0 ≤ A i j := fun i j => (hA i j).le
  obtain ⟨i₀⟩ := ‹Nonempty n›
  -- Maximize `t` over the pairs `(x, t)` with `x` a probability vector and `t x ≤ A x`; the
  -- bound `t ≤ ∑ i, ∑ j, A i j` is automatic, and makes the set compact.
  have hne : {p : (n → ℝ) × ℝ | 0 ≤ p.1 ∧ ∑ i, p.1 i = 1 ∧ 0 ≤ p.2 ∧
      p.2 ≤ ∑ i, ∑ j, A i j ∧ p.2 • p.1 ≤ A *ᵥ p.1}.Nonempty := by
    refine ⟨(Pi.single i₀ 1, 0), Pi.single_nonneg.2 zero_le_one, by simp, le_rfl,
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hA' i j, ?_⟩
    simpa using mulVec_nonneg hA' (Pi.single_nonneg.2 zero_le_one)
  obtain ⟨⟨x, r⟩, ⟨hx, hx1, hr, -, hxr⟩, hmax⟩ :=
    (isCompact_setOf_smul_le_mulVec A _).exists_isMaxOn hne continuous_snd.continuousOn
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx1
  -- At the maximum, `x` is an eigenvector: otherwise some probability vector does strictly better.
  have heig : A *ᵥ x = r • x := by
    by_contra hne
    obtain ⟨ε, hε, y, hy, hy1, hyr⟩ := exists_add_smul_le_mulVec hA hx hx0 hxr hne
    have := isMaxOn_iff.1 hmax (y, r + ε)
      ⟨hy, hy1, by positivity, le_sum_of_smul_le_mulVec hA' hy hy1 hyr, hyr⟩
    linarith
  refine ⟨r, ?_, x, pos_of_mulVec_eq_smul hA hx hx0 heig, heig⟩
  have h := mulVec_pos hA hx hx0 i₀
  rw [heig] at h
  exact pos_of_mul_pos_left h (hx i₀)

/-- The eigenvalue `r` of an eigenvector with strictly positive entries of an entrywise
nonnegative real matrix bounds the modulus of every complex eigenvalue. -/
theorem norm_le_of_mulVec_eq_smul (hA : ∀ i j, 0 ≤ A i j) (hv : ∀ i, 0 < v i)
    (hAv : A *ᵥ v = r • v) {μ : ℂ} {z : n → ℂ} (hz : z ≠ 0)
    (hAz : A.map (↑) *ᵥ z = μ • z) : ‖μ‖ ≤ r := by
  refine le_of_smul_le_mulVec hA hv hAv (y := fun i => ‖z i‖) (fun i => norm_nonneg _) ?_ ?_
  · intro h
    exact hz (funext fun i => norm_eq_zero.1 (congrFun h i))
  · intro i
    calc ‖μ‖ * ‖z i‖ = ‖(A.map (↑) *ᵥ z) i‖ := by simp [hAz]
      _ ≤ ∑ j, ‖((A i j : ℝ) : ℂ) * z j‖ := norm_sum_le _ _
      _ = (A *ᵥ fun i => ‖z i‖) i := by
        simp [mulVec, dotProduct, Complex.norm_real, abs_of_nonneg (hA i _)]

/-- **Perron–Frobenius**: the eigenvalue `r` of an eigenvector with strictly positive entries of an
entrywise nonnegative real square matrix is the spectral radius of the matrix, viewed as a complex
matrix. Together with `Matrix.exists_mulVec_eq_smul_of_pos`, a strictly positive matrix has its
spectral radius as an eigenvalue, with an eigenvector whose entries are strictly positive. -/
theorem spectralRadius_eq_of_mulVec_eq_smul [Nonempty n] (hA : ∀ i j, 0 ≤ A i j)
    (hv : ∀ i, 0 < v i) (hAv : A *ᵥ v = r • v) :
    spectralRadius ℂ (A.map (↑) : Matrix n n ℂ) = ENNReal.ofReal r := by
  classical
  have hmem : ∀ μ : ℂ, μ ∈ spectrum ℂ (A.map (↑) : Matrix n n ℂ) ↔
      ∃ z : n → ℂ, z ≠ 0 ∧ A.map (↑) *ᵥ z = μ • z := by
    intro μ
    rw [← spectrum_toLin', ← Module.End.hasEigenvalue_iff_mem_spectrum]
    refine ⟨fun h => ?_, fun ⟨z, hz, hAz⟩ => ?_⟩
    · obtain ⟨z, hz⟩ := h.exists_hasEigenvector
      exact ⟨z, hz.2, by simpa using Module.End.mem_eigenspace_iff.1 hz.1⟩
    · exact Module.End.hasEigenvalue_of_hasEigenvector
        ⟨Module.End.mem_eigenspace_iff.2 (by simpa using hAz), hz⟩
  obtain ⟨i₀⟩ := ‹Nonempty n›
  have hr : 0 ≤ r := by
    have h := mulVec_nonneg hA (fun i => (hv i).le) i₀
    rw [hAv] at h
    exact nonneg_of_mul_nonneg_left h (hv i₀)
  rw [spectralRadius_eq_of_unital]
  refine le_antisymm (iSup₂_le fun μ hμ => ?_) ?_
  · obtain ⟨z, hz, hAz⟩ := (hmem μ).1 hμ
    rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm]
    exact ENNReal.ofReal_le_ofReal (norm_le_of_mulVec_eq_smul hA hv hAv hz hAz)
  · refine le_iSup₂_of_le (r : ℂ) ((hmem _).2 ⟨fun i => v i, ?_, ?_⟩) ?_
    · exact fun h => (hv i₀).ne' (by simpa using congrFun h i₀)
    · ext i
      simpa [mulVec, dotProduct] using congrArg Complex.ofReal (congrFun hAv i)
    · rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm, Complex.norm_real, Real.norm_of_nonneg hr]

end Real

end Matrix
