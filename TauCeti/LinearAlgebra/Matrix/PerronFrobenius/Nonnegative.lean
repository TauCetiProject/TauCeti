/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.PerronFrobenius.Positive

/-!
# The Perron–Frobenius theorem for nonnegative matrices

An entrywise nonnegative real square matrix `A` has its spectral radius `r` as an eigenvalue, with
an eigenvector whose entries are nonnegative and not all zero. Moreover `r` dominates every `t`
satisfying `t y ≤ A y` entrywise for some nonzero nonnegative vector `y`, which is the lower half
of the Collatz–Wielandt formula.

Without positivity or irreducibility these statements cannot be sharpened: the eigenvector may have
zero entries, and other nonnegative eigenvectors may belong to smaller eigenvalues, as the diagonal
matrix with entries `1` and `2` shows; and it need not be unique up to scalars, as the identity
matrix of size two shows. For strictly positive
and for irreducible matrices see `TauCeti.LinearAlgebra.Matrix.PerronFrobenius.Positive` and
`TauCeti.LinearAlgebra.Matrix.PerronFrobenius.Irreducible`.

The proof is the classical continuity argument. For `ε > 0` the matrix `A + ε J`, where `J` has
all entries `1`, is strictly positive, so it has a Perron eigenvector `v_ε` in the standard simplex,
with eigenvalue `r_ε`. Since `A v_ε ≤ r_ε v_ε`, the Collatz–Wielandt bounds for `A` against the
strictly positive vector `v_ε` show that `r_ε` dominates every complex eigenvalue of `A` in modulus,
and every `t` as above. The standard simplex is compact, so along a sequence `ε → 0` the vectors
`v_ε` have a limit point `v`, at which the eigenvalues `r_ε` converge to some `r`; in the limit
`A v = r v`, and `r` keeps both domination properties, so it is the spectral radius.

## Main results

* `Matrix.exists_mulVec_eq_smul_of_nonneg`: an entrywise nonnegative real square matrix has a
  nonzero nonnegative eigenvector whose eigenvalue is its spectral radius.
* `Matrix.ofReal_le_spectralRadius_of_smul_le_mulVec`: if `t y ≤ A y` for a nonzero nonnegative
  vector `y`, then `t` is at most the spectral radius of `A`.

## References

* R. A. Horn, C. R. Johnson, *Matrix Analysis*, 2nd ed., Cambridge University Press (2013),
  Section 8.3 (Theorem 8.3.1 and its proof by approximation with positive matrices).
* E. Seneta, *Non-negative Matrices and Markov Chains*, Springer (2006), Chapter 1.
* P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor Categories*, Mathematical Surveys and
  Monographs **205**, AMS (2015), Section 3.2 (the Frobenius–Perron theorem).
-/

public section

open scoped Matrix Topology

open Convexity Filter

namespace Matrix

variable {n : Type*} [Fintype n] {A : Matrix n n ℝ}

/-- For `ε > 0`, the perturbation `A + ε J` of a nonnegative matrix `A`, where `J` has all entries
`1`, has a strictly positive eigenvector in the standard simplex. On such a vector `v` the matrix
`J` acts as the constant vector `1`, so the eigenvalue equation reads `A v + ε = r v`. -/
private theorem exists_mulVec_add_eq_smul [Nonempty n] (hA : ∀ i j, 0 ≤ A i j) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ r : ℝ, ∃ v : n → ℝ, (∀ i, 0 < v i) ∧ ∑ i, v i = 1 ∧ A *ᵥ v + (fun _ => ε) = r • v := by
  obtain ⟨r, -, w, hw, hBw⟩ := exists_mulVec_eq_smul_of_pos
    (A := A + of fun _ _ => ε) fun i j => by simpa using add_pos_of_nonneg_of_pos (hA i j) hε
  have hs : 0 < ∑ i, w i := Finset.sum_pos (fun i _ => hw i) Finset.univ_nonempty
  have hv1 : ∑ i, ((∑ i, w i)⁻¹ • w) i = 1 := by
    simp [← Finset.mul_sum, hs.ne']
  refine ⟨r, (∑ i, w i)⁻¹ • w, fun i => by simpa using mul_pos (inv_pos.2 hs) (hw i), hv1, ?_⟩
  have hB := congrArg ((∑ i, w i)⁻¹ • ·) hBw
  simp only [← mulVec_smul, smul_comm _ r] at hB
  rw [← hB, add_mulVec]
  congr 1
  ext i
  simpa [mulVec, dotProduct, ← Finset.mul_sum] using (congrArg (ε * ·) hv1).symm

/-- The limit of the Perron eigenvectors of the perturbations `A + ε J` as `ε → 0`, along a
subsequence: a nonnegative eigenvector `v` of `A` in the standard simplex, for an eigenvalue `r`
that is at least every `x` bounded by all the Collatz–Wielandt upper bounds `s`, those with
`A w ≤ s w` for some strictly positive `w`. -/
private theorem exists_mulVec_eq_smul_of_nonneg_aux [Nonempty n] (hA : ∀ i j, 0 ≤ A i j) :
    ∃ r : ℝ, ∃ v : n → ℝ, 0 ≤ v ∧ ∑ i, v i = 1 ∧ A *ᵥ v = r • v ∧
      ∀ x : ℝ, (∀ (w : n → ℝ) (s : ℝ), (∀ i, 0 < w i) → A *ᵥ w ≤ s • w → x ≤ s) → x ≤ r := by
  set ε : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1)
  have hε (m : ℕ) : 0 < ε m := by positivity
  choose r w hw hw1 heq using fun m => exists_mulVec_add_eq_smul hA (hε m)
  set S := Set.range fun s : StdSimplex ℝ n => ⇑s.weights
  have hmem (x : n → ℝ) : x ∈ S ↔ 0 ≤ x ∧ ∑ i, x i = 1 := by
    simp [S, StdSimplex.range_toFun_comp_weights, Pi.le_def]
  have hS : IsCompact S :=
    isCompact_range (StdSimplex.isEmbedding_toFun_comp_weights ℝ n).continuous
  obtain ⟨v, hvS, φ, hφ, hv⟩ :=
    hS.tendsto_subseq fun m => (hmem (w m)).2 ⟨fun i => (hw m i).le, hw1 m⟩
  obtain ⟨hv0, hv1⟩ := (hmem v).1 hvS
  have hεφ : Tendsto (ε ∘ φ) atTop (𝓝 0) :=
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hφ.tendsto_atTop
  -- Summing the eigenvalue equation over the simplex computes `r` from `w` and `ε`, so the
  -- eigenvalues converge along the subsequence as well.
  have hr (m : ℕ) : r m = ∑ i, (A *ᵥ w m) i + Fintype.card n * ε m := by
    have h := congrArg (fun u : n → ℝ => ∑ i, u i) (heq m)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum, hw1 m, mul_one] at h
    exact h.symm
  have hcont : Continuous fun u : n → ℝ => A *ᵥ u := continuous_const.matrix_mulVec continuous_id
  have hAw : Tendsto (fun m => A *ᵥ w (φ m)) atTop (𝓝 (A *ᵥ v)) := (hcont.tendsto v).comp hv
  set R := ∑ i, (A *ᵥ v) i
  have hrφ : Tendsto (r ∘ φ) atTop (𝓝 R) := by
    have hsum : Continuous fun u : n → ℝ => ∑ i, (A *ᵥ u) i :=
      continuous_finsetSum _ fun i _ => (continuous_apply i).comp hcont
    have h := ((hsum.tendsto v).comp hv).add (hεφ.const_mul (Fintype.card n : ℝ))
    rw [mul_zero, add_zero] at h
    exact h.congr fun m => (hr (φ m)).symm
  refine ⟨R, v, hv0, hv1, ?_, fun x hx => ge_of_tendsto' hrφ fun m => hx _ _ (hw (φ m)) ?_⟩
  · have hL : Tendsto (fun m => A *ᵥ w (φ m) + fun _ => ε (φ m)) atTop
        (𝓝 (A *ᵥ v + fun _ => 0)) :=
      hAw.add (tendsto_pi_nhds.2 fun _ => hεφ)
    have hR : Tendsto (fun m => r (φ m) • w (φ m)) atTop (𝓝 (R • v)) := hrφ.smul hv
    rw [funext fun m => heq (φ m)] at hL
    have h := tendsto_nhds_unique hL hR
    rwa [← Pi.zero_def, add_zero] at h
  · rw [Function.comp_apply, ← heq (φ m)]
    exact le_add_of_nonneg_right fun _ => (hε (φ m)).le

/-- The eigenvalue produced by `Matrix.exists_mulVec_eq_smul_of_nonneg_aux` is nonnegative and is
the spectral radius: it is an eigenvalue, and it dominates the modulus of every complex eigenvalue.
It still dominates every `x` bounded by all the Collatz–Wielandt upper bounds. -/
private theorem exists_spectralRadius_eq_aux [Nonempty n] (hA : ∀ i j, 0 ≤ A i j) :
    ∃ r : ℝ, 0 ≤ r ∧ spectralRadius ℂ (A.map (↑) : Matrix n n ℂ) = ENNReal.ofReal r ∧
      (∃ v : n → ℝ, 0 ≤ v ∧ v ≠ 0 ∧ A *ᵥ v = r • v) ∧
      ∀ x : ℝ, (∀ (w : n → ℝ) (s : ℝ), (∀ i, 0 < w i) → A *ᵥ w ≤ s • w → x ≤ s) → x ≤ r := by
  obtain ⟨r, v, hv, hv1, hAv, hmax⟩ := exists_mulVec_eq_smul_of_nonneg_aux hA
  have hv0 : v ≠ 0 := by
    rintro rfl
    simp at hv1
  have hr : 0 ≤ r := hmax 0 fun w s hw hAw =>
    le_of_smul_le_mulVec hA hw hAw hv hv0 (by simpa using mulVec_nonneg hA hv)
  refine ⟨r, hr, spectralRadius_eq_of_mulVec_eq_smul_of_forall_norm_le hr hv0 hAv ?_,
    ⟨v, hv, hv0, hAv⟩, hmax⟩
  exact fun μ z hz hAz => hmax _ fun w s hw hAw => norm_le_of_mulVec_le_smul hA hw hAw hz hAz

/-- **Perron–Frobenius theorem for nonnegative matrices**: an entrywise nonnegative real square
matrix has its spectral radius `r`, viewed as a complex matrix, as an eigenvalue, with an
eigenvector whose entries are nonnegative and not all zero.

Unlike the strictly positive and irreducible cases (`Matrix.exists_mulVec_eq_smul_of_pos` and
`Matrix.IsIrreducible.exists_mulVec_eq_smul`), the eigenvector may have zero entries and need not be
unique up to scalars, and `r` may be zero. -/
theorem exists_mulVec_eq_smul_of_nonneg [Nonempty n] (hA : ∀ i j, 0 ≤ A i j) :
    ∃ r : ℝ, 0 ≤ r ∧ spectralRadius ℂ (A.map (↑) : Matrix n n ℂ) = ENNReal.ofReal r ∧
      ∃ v : n → ℝ, 0 ≤ v ∧ v ≠ 0 ∧ A *ᵥ v = r • v :=
  let ⟨r, hr, hρ, hv, _⟩ := exists_spectralRadius_eq_aux hA
  ⟨r, hr, hρ, hv⟩

/-- **Collatz–Wielandt bound for nonnegative matrices.** If `t y ≤ A y` entrywise for an entrywise
nonnegative real square matrix `A` and a nonzero vector `y` with nonnegative entries, then `t` is at
most the spectral radius of `A`, viewed as a complex matrix. -/
theorem ofReal_le_spectralRadius_of_smul_le_mulVec (hA : ∀ i j, 0 ≤ A i j) {y : n → ℝ} {t : ℝ}
    (hy : 0 ≤ y) (hy0 : y ≠ 0) (h : t • y ≤ A *ᵥ y) :
    ENNReal.ofReal t ≤ spectralRadius ℂ (A.map (↑) : Matrix n n ℂ) := by
  obtain ⟨j, -⟩ := Function.ne_iff.1 hy0
  have : Nonempty n := ⟨j⟩
  obtain ⟨r, -, hρ, -, hmax⟩ := exists_spectralRadius_eq_aux hA
  rw [hρ]
  exact ENNReal.ofReal_le_ofReal <| hmax t fun w s hw hAw => le_of_smul_le_mulVec hA hw hAw hy hy0 h

end Matrix
