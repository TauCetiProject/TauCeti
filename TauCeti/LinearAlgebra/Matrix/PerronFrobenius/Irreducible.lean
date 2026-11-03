/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Eigenspace.Zero
public import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
public import TauCeti.LinearAlgebra.Matrix.PerronFrobenius.Positive

/-!
# The Perron–Frobenius theorem for irreducible matrices

A square real matrix `A` is irreducible (`Matrix.IsIrreducible`) when its entries are nonnegative
and the directed graph of its positive entries is strongly connected. For such a matrix some power
of `1 + A` is strictly positive, that is `1 + A` is primitive, and this reduces the theory to the
one for strictly positive matrices in `TauCeti.LinearAlgebra.Matrix.PerronFrobenius.Positive`.

The conclusions are those of the Perron–Frobenius theorem for irreducible matrices. `A` has an
eigenvector all of whose entries are strictly positive, for a strictly positive eigenvalue `r`,
the **Perron root**, which is the spectral radius of `A`
(`Matrix.spectralRadius_eq_of_mulVec_eq_smul`). Every nonzero nonnegative eigenvector of `A`, for
any eigenvalue, has strictly positive entries and is a positive multiple of the Perron eigenvector,
so its eigenvalue is `r`. The root `r` is simple: its eigenspace is spanned by the Perron
eigenvector, and its multiplicity as a root of the characteristic polynomial is one. Finally,
`r y ≤ A y` for a real vector `y` forces `A y = r y`.

The primitivity of `1 + A` and the positivity of nonnegative eigenvectors hold over any linearly
ordered commutative ring, such as `ℤ`. The other statements about a given positive eigenvector work
over any linearly ordered field. Existence, and the two statements that use a positive eigenvector
of the transpose (simplicity as a root of the characteristic polynomial, and the equality case
`r y ≤ A y`), are stated over `ℝ`.

## Main results

* `Matrix.IsIrreducible.isPrimitive_one_add`: if `A` is irreducible, then `1 + A` is primitive.
* `Matrix.IsIrreducible.exists_mulVec_eq_smul`: an irreducible real matrix has an eigenvector with
  strictly positive entries, for a strictly positive eigenvalue.
* `Matrix.IsIrreducible.exists_pos_eq_smul_of_mulVec_eq_smul`: a nonzero nonnegative eigenvector of
  an irreducible matrix is a positive multiple of any eigenvector with strictly positive entries.
* `Matrix.IsIrreducible.exists_eq_smul_of_mulVec_eq_smul`: the eigenspace of the Perron root is
  spanned by the Perron eigenvector.
* `Matrix.IsIrreducible.rootMultiplicity_charpoly_eq_one`: the Perron root is a simple root of the
  characteristic polynomial.
* `Matrix.IsIrreducible.mulVec_eq_smul_of_smul_le_mulVec`: if `r y ≤ A y`, then `A y = r y`.

## References

* E. Seneta, *Non-negative Matrices and Markov Chains*, Springer (2006), Chapter 1 (irreducible
  matrices, the reduction to `(1 + A) ^ k`, and the subinvariance theorem).
* P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor Categories*, Mathematical Surveys and
  Monographs **205**, AMS (2015), Section 3.2 (the Frobenius–Perron theorem).
-/

public section

open scoped Matrix

namespace Matrix

variable {n : Type*} [Fintype n]

section OrderedCommRing

variable {K : Type*} [CommRing K] [LinearOrder K] [IsStrictOrderedRing K] {A : Matrix n n K}
  {w : n → K} {μ : K}

/-- If `A` is irreducible, then `1 + A` is primitive: some power of `1 + A` has all its entries
strictly positive. -/
theorem IsIrreducible.isPrimitive_one_add [DecidableEq n] (hA : A.IsIrreducible) :
    (1 + A).IsPrimitive := by
  choose k hk0 hk using (isIrreducible_iff_exists_pow_pos hA.nonneg).1 hA
  -- A power `N` beyond every `k i j` works, since `(1 + A) ^ N` dominates a positive multiple of
  -- each `A ^ k i j` by the binomial theorem.
  obtain ⟨N, hN, hkN⟩ : ∃ N, 0 < N ∧ ∀ i j, k i j ≤ N :=
    ⟨(Finset.univ.sup fun p : n × n => k p.1 p.2) + 1, Nat.succ_pos _, fun i j =>
      (Finset.le_sup (f := fun p : n × n => k p.1 p.2) (Finset.mem_univ (i, j))).trans
        (Nat.le_succ _)⟩
  refine ⟨fun i j => add_nonneg ?_ (hA.nonneg i j), N, hN, fun i j => ?_⟩
  · rw [Matrix.one_apply]
    split_ifs <;> simp
  rw [add_comm, (Commute.one_right A).add_pow', Matrix.sum_apply]
  refine Finset.sum_pos' (fun p _ => ?_) ⟨(k i j, N - k i j), ?_, ?_⟩
  · simpa using nsmul_nonneg (pow_apply_nonneg hA.nonneg p.1 i j) _
  · simpa using Nat.add_sub_cancel' (hkN i j)
  · simpa using nsmul_pos (hk i j) (Nat.choose_pos (hkN i j)).ne'

/-- For an irreducible `A`, some power `(1 + A) ^ k` is strictly positive, and every eigenvector of
`A`, for an eigenvalue `t`, is an eigenvector of it for `(1 + t) ^ k`. This is how each statement
below is reduced to the strictly positive case. -/
private theorem IsIrreducible.exists_one_add_pow [DecidableEq n] (hA : A.IsIrreducible) :
    ∃ k : ℕ, (∀ i j, 0 < ((1 + A) ^ k) i j) ∧
      ∀ {u : n → K} {t : K}, A *ᵥ u = t • u → ((1 + A) ^ k) *ᵥ u = (1 + t) ^ k • u := by
  obtain ⟨-, k, -, hk⟩ := hA.isPrimitive_one_add
  exact ⟨k, hk, fun hu =>
    pow_mulVec_eq_pow_smul (by rw [add_mulVec, one_mulVec, hu, add_smul, one_smul]) k⟩

/-- A nonzero nonnegative eigenvector of an irreducible matrix has all its entries strictly
positive. -/
theorem IsIrreducible.pos_of_mulVec_eq_smul (hA : A.IsIrreducible) (hw : 0 ≤ w) (hw0 : w ≠ 0)
    (hAw : A *ᵥ w = μ • w) (i : n) : 0 < w i := by
  classical
  obtain ⟨k, hk, h⟩ := hA.exists_one_add_pow
  exact Matrix.pos_of_mulVec_eq_smul hk hw hw0 (h hAw) i

end OrderedCommRing

section OrderedField

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {A : Matrix n n K}
  {v w : n → K} {r μ : K}

/-- A nonzero nonnegative eigenvector of an irreducible matrix is a positive multiple of any
eigenvector with strictly positive entries, whatever eigenvalue it was taken for. -/
theorem IsIrreducible.exists_pos_eq_smul_of_mulVec_eq_smul (hA : A.IsIrreducible)
    (hv : ∀ i, 0 < v i) (hAv : A *ᵥ v = r • v) (hw : 0 ≤ w) (hw0 : w ≠ 0)
    (hAw : A *ᵥ w = μ • w) : ∃ c : K, 0 < c ∧ w = c • v := by
  classical
  obtain ⟨k, hk, h⟩ := hA.exists_one_add_pow
  exact Matrix.exists_pos_eq_smul_of_mulVec_eq_smul hk hv (h hAv) hw hw0 (h hAw)

/-- A nonzero nonnegative eigenvector of an irreducible matrix has the same eigenvalue as any
eigenvector with strictly positive entries. -/
theorem IsIrreducible.eq_of_mulVec_eq_smul_of_nonneg (hA : A.IsIrreducible) (hv : ∀ i, 0 < v i)
    (hAv : A *ᵥ v = r • v) (hw : 0 ≤ w) (hw0 : w ≠ 0) (hAw : A *ᵥ w = μ • w) : μ = r := by
  obtain ⟨c, hc, rfl⟩ := hA.exists_pos_eq_smul_of_mulVec_eq_smul hv hAv hw hw0 hAw
  obtain ⟨i, -⟩ := Function.ne_iff.1 hw0
  have h := congrFun hAw i
  rw [mulVec_smul, hAv] at h
  simp only [Pi.smul_apply, smul_eq_mul] at h
  exact (mul_right_cancel₀ (mul_pos hc (hv i)).ne' (by linear_combination h)).symm

/-- For an irreducible matrix, the eigenspace of an eigenvector `v` with strictly positive entries
is spanned by `v`: every eigenvector for the same eigenvalue, of any sign, is a multiple of `v`. -/
theorem IsIrreducible.exists_eq_smul_of_mulVec_eq_smul (hA : A.IsIrreducible) (hv : ∀ i, 0 < v i)
    (hAv : A *ᵥ v = r • v) (hAw : A *ᵥ w = r • w) : ∃ c : K, w = c • v := by
  classical
  obtain ⟨k, hk, h⟩ := hA.exists_one_add_pow
  exact Matrix.exists_eq_smul_of_mulVec_eq_smul hk hv (h hAv) (h hAw)

end OrderedField

section Real

variable {A : Matrix n n ℝ} {v y : n → ℝ} {r : ℝ}

/-- **Perron–Frobenius theorem for irreducible matrices**, existence: an irreducible real square
matrix has an eigenvector whose entries are all strictly positive, for a strictly positive
eigenvalue.

This eigenvalue is the spectral radius (`Matrix.spectralRadius_eq_of_mulVec_eq_smul`), its
eigenspace is spanned by the eigenvector (`Matrix.IsIrreducible.exists_eq_smul_of_mulVec_eq_smul`),
and it is a simple root of the characteristic polynomial
(`Matrix.IsIrreducible.rootMultiplicity_charpoly_eq_one`). -/
theorem IsIrreducible.exists_mulVec_eq_smul [Nonempty n] (hA : A.IsIrreducible) :
    ∃ r : ℝ, 0 < r ∧ ∃ v : n → ℝ, (∀ i, 0 < v i) ∧ A *ᵥ v = r • v := by
  classical
  obtain ⟨-, k, -, hk⟩ := hA.isPrimitive_one_add
  obtain ⟨s, -, v, hv, hBv⟩ := exists_mulVec_eq_smul_of_pos hk
  -- The vector `(1 + A) v` is again a positive eigenvector of `(1 + A) ^ k`, hence a positive
  -- multiple `c v` of `v`, and `A v = (c - 1) v`.
  set w := (1 + A) *ᵥ v
  have hvw : ∀ i, v i ≤ w i := fun i => by
    simpa [w, add_mulVec] using mulVec_nonneg hA.nonneg (fun j => (hv j).le) i
  have hw : 0 ≤ w := fun i => (hv i).le.trans (hvw i)
  obtain ⟨i₀⟩ := ‹Nonempty n›
  have hw0 : w ≠ 0 := fun h => (hv i₀).not_ge (by simpa [h] using hvw i₀)
  have hBw : ((1 + A) ^ k) *ᵥ w = s • w := by
    rw [mulVec_mulVec, ← pow_succ, pow_succ', ← mulVec_mulVec, hBv, mulVec_smul]
  obtain ⟨c, -, hc⟩ := Matrix.exists_pos_eq_smul_of_mulVec_eq_smul hk hv hBv hw hw0 hBw
  have hAv : A *ᵥ v = (c - 1) • v := by
    rw [sub_smul, one_smul, ← hc]
    simp [w, add_mulVec]
  refine ⟨c - 1, ?_, v, hv, hAv⟩
  -- The eigenvalue is nonnegative since `A v ≥ 0`; it is nonzero since otherwise `A v = 0` would
  -- force `A = 0`, which is not irreducible.
  have hr : 0 ≤ c - 1 := by
    have h := mulVec_nonneg hA.nonneg (fun j => (hv j).le) i₀
    rw [hAv] at h
    exact nonneg_of_mul_nonneg_left h (hv i₀)
  refine hr.lt_of_ne fun h0 => ?_
  have hA0 : A = 0 := by
    ext i j
    have hi := congrFun hAv i
    rw [← h0, zero_smul] at hi
    simp only [mulVec, dotProduct, Pi.zero_apply] at hi
    have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ =>
      mul_nonneg (hA.nonneg i j) (hv j).le).1 hi j (Finset.mem_univ j)
    simpa [(hv j).ne'] using this
  obtain ⟨m, hm0, hm⟩ := (isIrreducible_iff_exists_pow_pos hA.nonneg).1 hA i₀ i₀
  simp [hA0, zero_pow hm0.ne'] at hm

/-- An irreducible real matrix with a strictly positive eigenvector for `r` has a strictly positive
left eigenvector for the same `r`. -/
private theorem IsIrreducible.exists_vecMul_eq_smul [Nonempty n] (hA : A.IsIrreducible)
    (hv : ∀ i, 0 < v i) (hAv : A *ᵥ v = r • v) :
    ∃ u : n → ℝ, (∀ i, 0 < u i) ∧ u ᵥ* A = r • u := by
  obtain ⟨s, -, u, hu, hAu⟩ := hA.transpose.exists_mulVec_eq_smul
  rw [mulVec_transpose] at hAu
  refine ⟨u, hu, ?_⟩
  -- Pairing both eigenvector equations with the other vector shows `s = r`.
  have h := dotProduct_mulVec u A v
  rw [hAu, hAv, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul] at h
  have huv : 0 < u ⬝ᵥ v :=
    Finset.sum_pos (fun i _ => mul_pos (hu i) (hv i)) Finset.univ_nonempty
  rw [hAu, mul_right_cancel₀ huv.ne' h.symm]

/-- **Subinvariance**: if `A` is irreducible with a strictly positive eigenvector for `r`, and a
real vector `y` satisfies `r y ≤ A y` entrywise, then `y` is an eigenvector for `r`. -/
theorem IsIrreducible.mulVec_eq_smul_of_smul_le_mulVec (hA : A.IsIrreducible) (hv : ∀ i, 0 < v i)
    (hAv : A *ᵥ v = r • v) (hy : r • y ≤ A *ᵥ y) : A *ᵥ y = r • y := by
  cases isEmpty_or_nonempty n
  · exact funext isEmptyElim
  obtain ⟨u, hu, huA⟩ := hA.exists_vecMul_eq_smul hv hAv
  -- The defect `A y - r y` is nonnegative and orthogonal to the positive vector `u`.
  have h : u ⬝ᵥ (A *ᵥ y - r • y) = 0 := by
    rw [dotProduct_sub, dotProduct_mulVec, huA, dotProduct_smul, smul_dotProduct, sub_self]
  rw [← sub_eq_zero]
  ext i
  have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ =>
    mul_nonneg (hu j).le (sub_nonneg.2 (hy j))).1 h i (Finset.mem_univ i)
  simpa [(hu i).ne'] using this

/-- If `A` is irreducible with a strictly positive eigenvector for `r`, then no eigenvector for `r`
lies in the range of `A - r`: an eigenvector for `r` of the form `A x - r x` is zero. -/
private theorem IsIrreducible.mulVec_sub_smul_eq_zero (hA : A.IsIrreducible) (hv : ∀ i, 0 < v i)
    (hAv : A *ᵥ v = r • v) {x : n → ℝ} (hx : A *ᵥ (A *ᵥ x - r • x) = r • (A *ᵥ x - r • x)) :
    A *ᵥ x - r • x = 0 := by
  cases isEmpty_or_nonempty n
  · exact funext isEmptyElim
  obtain ⟨c, hc⟩ := hA.exists_eq_smul_of_mulVec_eq_smul hv hAv hx
  obtain ⟨u, hu, huA⟩ := hA.exists_vecMul_eq_smul hv hAv
  -- Pair with the positive left eigenvector `u`: it kills the range of `A - r`, but not `v`.
  have h : u ⬝ᵥ (A *ᵥ x - r • x) = 0 := by
    rw [dotProduct_sub, dotProduct_mulVec, huA, dotProduct_smul, smul_dotProduct, sub_self]
  have huv : 0 < u ⬝ᵥ v :=
    Finset.sum_pos (fun i _ => mul_pos (hu i) (hv i)) Finset.univ_nonempty
  rw [hc, dotProduct_smul, smul_eq_mul, mul_eq_zero] at h
  rw [hc, h.resolve_right huv.ne', zero_smul]

/-- **Perron–Frobenius**: the eigenvalue `r` of a strictly positive eigenvector of an irreducible
real matrix is a simple root of its characteristic polynomial. -/
theorem IsIrreducible.rootMultiplicity_charpoly_eq_one [DecidableEq n] [Nonempty n]
    (hA : A.IsIrreducible) (hv : ∀ i, 0 < v i) (hAv : A *ᵥ v = r • v) :
    A.charpoly.rootMultiplicity r = 1 := by
  obtain ⟨i₀⟩ := ‹Nonempty n›
  have hv0 : v ≠ 0 := fun h => (hv i₀).ne' (congrFun h i₀)
  have hsub (x : n → ℝ) : (toLin' A - r • 1) x = A *ᵥ x - r • x := by simp
  -- Every generalized eigenvector for `r` is an eigenvector, by `mulVec_sub_smul_eq_zero`.
  have hgen (k : ℕ) (x : n → ℝ) (hx : ((toLin' A - r • 1) ^ k) x = 0) :
      (toLin' A - r • 1) x = 0 := by
    induction k generalizing x with
    | zero => simp_all
    | succ k ih =>
      rw [pow_succ, _root_.mul_apply_eq_comp] at hx
      have h := ih _ hx
      rw [hsub, hsub, sub_eq_zero] at h
      rw [hsub]
      exact hA.mulVec_sub_smul_eq_zero hv hAv h
  have hspan : Module.End.maxGenEigenspace (toLin' A) r = ℝ ∙ v := by
    refine le_antisymm (fun x hx => ?_) ?_
    · obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 hx
      have h := hgen k x hk
      rw [hsub, sub_eq_zero] at h
      obtain ⟨c, rfl⟩ := hA.exists_eq_smul_of_mulVec_eq_smul hv hAv h
      exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self v)
    · refine (Submodule.span_singleton_le_iff_mem _ _).2
        (Module.End.eigenspace_le_maxGenEigenspace ?_)
      rw [Module.End.mem_eigenspace_iff, toLin'_apply, hAv]
  rw [← charpoly_toLin', ← LinearMap.finrank_maxGenEigenspace_eq, hspan,
    finrank_span_singleton hv0]

end Real

end Matrix
