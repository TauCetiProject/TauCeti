/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import TauCeti.Analysis.InnerProductSpace.SchurHorn
public import TauCeti.Analysis.Matrix.EuclideanLin

/-!
# Diagonals of unitary orbits: the Schur–Horn theorem for matrices

For a real tuple `w`, the unitary orbit `{U diag(w) Uᴴ | U ∈ U(n)}` consists of the Hermitian
matrices with spectrum `w`. Under the pairing `⟨H, X⟩ = -i tr(H X)` between Hermitian matrices and
the Lie algebra `u(n)`, a diagonal element `X = i diag(θ)` of the Lie algebra of the diagonal
torus pairs with `H` to `∑ₖ θₖ Hₖₖ` (`Matrix.neg_I_mul_trace_mul_diagonal_I_mul`). So the moment
map of the diagonal torus on this orbit sends a matrix to its list of diagonal entries, and the
image of this moment map is the set of diagonals of the orbit. This file shows that it is the
*permutohedron* of `w`, the convex hull of the rearrangements `w ∘ σ`
(`Matrix.range_re_diag_unitary_mul_diagonal_mul_star`).

The entries of `U diag(w) Uᴴ` on the diagonal are `∑ᵢ |Uₖᵢ|² wᵢ`
(`Matrix.mul_diagonal_mul_star_apply_self`), and the matrix `(|Uₖᵢ|²)` of a unitary `U` is doubly
stochastic (`Matrix.of_norm_sq_mem_doublyStochastic`), so by Birkhoff's theorem the diagonal lies
in the permutohedron (Schur). Conversely (Horn), every point of the permutohedron is a diagonal of
the orbit: the rows of a unitary matrix form an orthonormal basis of `EuclideanSpace 𝕜 ι`, which
turns the operator form of Horn's theorem,
`LinearMap.IsSymmetric.exists_orthonormalBasis_re_inner_apply_self_eq_of_mem_convexHull`, into a
statement about unitary matrices. For a Hermitian matrix `A`, the spectral theorem puts `A` in
the orbit of the diagonal matrix of its eigenvalues, so the diagonals of the matrices `U A Uᴴ`
form the permutohedron of the eigenvalues of `A`
(`Matrix.IsHermitian.range_re_diag_unitary_mul_mul_star`). Repeated eigenvalues are allowed; they
give smaller orbits with the same description of the diagonals.

Two special cases are worked out.

* The orbit of `diag(c, 0, …, 0)` consists of the matrices `c v vᴴ` of rank at most one, for unit
  vectors `v` (`Matrix.mul_diagonal_single_mul_star`). When `c ≠ 0` it is a copy of the
  projective space of lines in `𝕜ⁿ`: `ℂℙⁿ⁻¹` for `𝕜 = ℂ` and `ℝℙⁿ⁻¹` for `𝕜 = ℝ`.
  Its diagonals form the simplex with vertices `c eᵢ`, the standard simplex scaled by `c`
  (`Matrix.range_re_diag_unitary_mul_diagonal_single_mul_star`).
* In size two, the explicit real symmetric matrix `!![d₁, b; b, d₂]` with
  `b = √((l₁ - d₁) (d₁ - l₂))` has characteristic polynomial `(X - l₁) (X - l₂)` whenever
  `l₂ ≤ d₁ ≤ l₁` and `d₁ + d₂ = l₁ + l₂`, so it realizes every diagonal majorized by a given pair
  of eigenvalues; conversely, these inequalities are forced
  (`Matrix.exists_isSymm_fin_two_charpoly_eq_iff`).

## Main results

* `Matrix.neg_I_mul_trace_mul_diagonal_I_mul`: the pairing `-i tr(H · i diag(θ))` is
  `∑ₖ θₖ Hₖₖ`, so the moment map of the diagonal torus reads off the diagonal.
* `Matrix.of_norm_sq_mem_doublyStochastic`: the squared moduli of the entries of a unitary matrix
  form a doubly stochastic matrix.
* `Matrix.re_diag_mul_diagonal_mul_star_mem_convexHull`: Schur's theorem, the diagonal of
  `U diag(w) Uᴴ` lies in the permutohedron of `w`.
* `Matrix.exists_mem_unitaryGroup_re_diag_mul_diagonal_mul_star_eq`: Horn's theorem, every point
  of the permutohedron of `w` is the diagonal of some `U diag(w) Uᴴ`.
* `Matrix.range_re_diag_unitary_mul_diagonal_mul_star`: the diagonals of the unitary orbit of
  `diag(w)` form exactly the permutohedron of `w`.
* `Matrix.IsHermitian.range_re_diag_unitary_mul_mul_star`: the same for the unitary orbit of a
  Hermitian matrix and the permutohedron of its eigenvalues.
* `Matrix.range_re_diag_unitary_mul_diagonal_single_mul_star`: the orbit of `diag(c, 0, …, 0)` has
  the simplex with vertices `c eᵢ` as its diagonals.
* `Matrix.exists_isSymm_fin_two_charpoly_eq_iff`: the `2 × 2` case, with an explicit matrix.

## References

* I. Schur, *Über eine Klasse von Mittelbildungen mit Anwendungen auf die
  Determinantentheorie*, Sitzungsber. Berl. Math. Ges. **22** (1923), 9–20.
* A. Horn, *Doubly stochastic matrices and the diagonal of a rotation matrix*, Amer. J. Math.
  **76** (1954), 620–630.
* M. F. Atiyah, *Convexity and commuting Hamiltonians*, Bull. London Math. Soc. **14** (1982),
  1–15, §1 (the Schur–Horn theorem as a moment-map convexity statement).
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer (2001), §27.
-/

public section

open scoped InnerProductSpace Matrix
open Polynomial TauCeti

namespace Matrix

variable {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι]

/-- **The diagonal torus reads off the diagonal.** Under the pairing `⟨H, X⟩ = -i tr(H X)`
between Hermitian matrices and `u(n)`, the element `X = i diag(θ)` of the Lie algebra of the
diagonal torus pairs with `H` to `∑ₖ θₖ Hₖₖ`. Hence the moment map of the diagonal torus on a
unitary orbit of Hermitian matrices sends a matrix to its diagonal. -/
theorem neg_I_mul_trace_mul_diagonal_I_mul (H : Matrix ι ι ℂ) (θ : ι → ℝ) :
    -Complex.I * (H * diagonal fun k ↦ Complex.I * θ k).trace = ∑ k, θ k * H k k := by
  simp only [trace, diag, mul_diagonal, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  linear_combination (-(θ k * H k k)) * Complex.I_mul_I

/-! ### Schur's theorem: diagonals lie in the permutohedron -/

/-- The diagonal entries of `U diag(w) Uᴴ` are the weighted sums `∑ᵢ |Uₖᵢ|² wᵢ` of `w`; when
`U` is unitary these are averages of `w`. -/
theorem mul_diagonal_mul_star_apply_self (U : Matrix ι ι 𝕜) (w : ι → ℝ) (k : ι) :
    (U * diagonal (fun i ↦ (w i : 𝕜)) * star U) k k = ((∑ i, ‖U k i‖ ^ 2 * w i : ℝ) : 𝕜) := by
  rw [Matrix.mul_apply]
  simp only [mul_diagonal, Matrix.star_apply, RCLike.star_def, RCLike.ofReal_sum,
    RCLike.ofReal_mul, RCLike.ofReal_pow]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← RCLike.mul_conj]
  ring

/-- The real parts of the diagonal entries of `U diag(w) Uᴴ` are the weighted sums
`∑ᵢ |Uₖᵢ|² wᵢ` of `w`; when `U` is unitary these are averages of `w`. -/
theorem re_mul_diagonal_mul_star_apply_self (U : Matrix ι ι 𝕜) (w : ι → ℝ) (k : ι) :
    RCLike.re ((U * diagonal (fun i ↦ (w i : 𝕜)) * star U) k k) = ∑ i, ‖U k i‖ ^ 2 * w i := by
  rw [mul_diagonal_mul_star_apply_self, RCLike.ofReal_re]

/-- **Unitary matrices are unistochastic.** The squared moduli `|Uₖᵢ|²` of the entries of a
unitary matrix form a doubly stochastic matrix. -/
theorem of_norm_sq_mem_doublyStochastic {U : Matrix ι ι 𝕜} (hU : U ∈ unitaryGroup ι 𝕜) :
    (of fun k i ↦ ‖U k i‖ ^ 2) ∈ doublyStochastic ℝ ι := by
  refine mem_doublyStochastic_iff_sum.2
    ⟨fun _ _ ↦ by rw [of_apply]; positivity, fun k ↦ ?_, fun i ↦ ?_⟩
  · have h := congr_fun₂ (mem_unitaryGroup_iff.1 hU) k k
    simp only [Matrix.mul_apply, Matrix.star_apply, RCLike.star_def, RCLike.mul_conj,
      one_apply_eq] at h
    simpa only [of_apply] using (by exact_mod_cast h : ∑ j, ‖U k j‖ ^ 2 = 1)
  · have h := congr_fun₂ (mem_unitaryGroup_iff'.1 hU) i i
    simp only [Matrix.mul_apply, Matrix.star_apply, RCLike.star_def, RCLike.conj_mul,
      one_apply_eq] at h
    simpa only [of_apply] using (by exact_mod_cast h : ∑ k, ‖U k i‖ ^ 2 = 1)

/-- **Schur's theorem.** For a unitary `U`, the diagonal of `U diag(w) Uᴴ` lies in the convex hull
of the rearrangements `w ∘ σ` of `w`. -/
theorem re_diag_mul_diagonal_mul_star_mem_convexHull {U : Matrix ι ι 𝕜}
    (hU : U ∈ unitaryGroup ι 𝕜) (w : ι → ℝ) :
    (fun k ↦ RCLike.re ((U * diagonal (fun i ↦ (w i : 𝕜)) * star U) k k)) ∈
      convexHull ℝ (Set.range fun σ : Equiv.Perm ι ↦ w ∘ σ) := by
  convert mulVec_mem_convexHull_range_comp_perm (of_norm_sq_mem_doublyStochastic hU) w using 1
  ext k
  simp [re_mul_diagonal_mul_star_apply_self, mulVec, dotProduct]

/-! ### Horn's theorem: every point of the permutohedron is a diagonal -/

/-- **Horn's theorem.** Every point `d` of the convex hull of the rearrangements of `w` is the
diagonal of `U diag(w) Uᴴ` for some unitary `U`. -/
theorem exists_mem_unitaryGroup_re_diag_mul_diagonal_mul_star_eq {w d : ι → ℝ}
    (hd : d ∈ convexHull ℝ (Set.range fun σ : Equiv.Perm ι ↦ w ∘ σ)) :
    ∃ U ∈ unitaryGroup ι 𝕜,
      ∀ k, RCLike.re ((U * diagonal (fun i ↦ (w i : 𝕜)) * star U) k k) = d k := by
  -- Work with the diagonal operator `T = diag(w)` and the operator form of the theorem, whose
  -- orthonormal bases are indexed by `Fin N`.
  set T : EuclideanSpace 𝕜 ι →ₗ[𝕜] EuclideanSpace 𝕜 ι := toEuclideanLin (diagonal fun i ↦ (w i : 𝕜))
  have hT : T.IsSymmetric :=
    isSymmetric_toEuclideanLin_iff.2 (isHermitian_diagonal_of_self_adjoint _ (by
      ext i; simp [Pi.star_apply, RCLike.star_def, RCLike.conj_ofReal]))
  have hn : Module.finrank 𝕜 (EuclideanSpace 𝕜 ι) = Fintype.card ι := finrank_euclideanSpace
  set eqv := Fintype.equivFin ι
  set ev := hT.eigenvalues hn
  -- The tuple `w`, read through `eqv`, is the diagonal of `T` in the standard basis, so it lies
  -- in the permutohedron of the eigenvalues of `T`; hence so does all of its permutohedron.
  have hw : w ∘ eqv.symm ∈ convexHull ℝ (Set.range fun σ : Equiv.Perm (Fin _) ↦ ev ∘ σ) := by
    convert hT.re_inner_apply_self_mem_convexHull_eigenvalues_comp_perm hn
      ((EuclideanSpace.basisFun ι 𝕜).reindex eqv) using 1
    ext k
    simp only [T, Function.comp_apply, OrthonormalBasis.reindex_apply,
      EuclideanSpace.basisFun_apply, re_inner_toEuclideanLin_diagonal_apply_self]
    rw [Finset.sum_eq_single (eqv.symm k) (fun i _ hi ↦ by simp [hi]) (by simp)]
    simp
  have hsub : convexHull ℝ (Set.range fun σ : Equiv.Perm (Fin _) ↦ (w ∘ eqv.symm) ∘ σ) ⊆
      convexHull ℝ (Set.range fun σ : Equiv.Perm (Fin _) ↦ ev ∘ σ) :=
    convexHull_min (Set.range_subset_iff.2 fun σ ↦ comp_perm_mem_convexHull_range_comp_perm hw σ)
      (convex_convexHull ℝ _)
  -- Reindexing by `eqv` carries the permutohedron of `w` onto that of `w ∘ eqv.symm`.
  have hd' : d ∘ eqv.symm ∈
      convexHull ℝ (Set.range fun σ : Equiv.Perm (Fin _) ↦ (w ∘ eqv.symm) ∘ σ) := by
    have himage : LinearMap.funLeft ℝ ℝ eqv.symm '' Set.range (fun σ : Equiv.Perm ι ↦ w ∘ σ) ⊆
        Set.range fun σ : Equiv.Perm (Fin _) ↦ (w ∘ eqv.symm) ∘ σ := by
      rintro _ ⟨_, ⟨σ, rfl⟩, rfl⟩
      exact ⟨eqv.permCongr σ, by ext; simp [Equiv.permCongr_apply]⟩
    refine convexHull_mono himage ?_
    rw [← LinearMap.image_convexHull]
    exact ⟨d, hd, rfl⟩
  obtain ⟨e, he⟩ :=
    hT.exists_orthonormalBasis_re_inner_apply_self_eq_of_mem_convexHull hn (hsub hd')
  obtain ⟨U, hU, hUe⟩ :=
    exists_mem_unitaryGroup_mul_mul_star_apply_self_eq_inner (diagonal fun i ↦ (w i : 𝕜))
      (e.reindex eqv.symm)
  refine ⟨U, hU, fun k ↦ ?_⟩
  rw [hUe k, inner_re_symm, OrthonormalBasis.reindex_apply, Equiv.symm_symm]
  simpa [T] using he (eqv k)

/-- **The Schur–Horn theorem.** The diagonals of the matrices `U diag(w) Uᴴ`, for `U` unitary,
form exactly the convex hull of the rearrangements of `w`. In the language of moment maps: the
image of the unitary orbit of `diag(w)` under the moment map of the diagonal torus is the
permutohedron of `w`. -/
theorem range_re_diag_unitary_mul_diagonal_mul_star (w : ι → ℝ) :
    (Set.range fun (U : unitaryGroup ι 𝕜) (k : ι) ↦
      RCLike.re ((U * diagonal (fun i ↦ (w i : 𝕜)) * star U : Matrix ι ι 𝕜) k k)) =
      convexHull ℝ (Set.range fun σ : Equiv.Perm ι ↦ w ∘ σ) := by
  ext d
  refine ⟨?_, fun hd ↦ ?_⟩
  · rintro ⟨U, rfl⟩
    exact re_diag_mul_diagonal_mul_star_mem_convexHull U.2 w
  · obtain ⟨U, hU, hUd⟩ := exists_mem_unitaryGroup_re_diag_mul_diagonal_mul_star_eq (𝕜 := 𝕜) hd
    exact ⟨⟨U, hU⟩, funext hUd⟩

/-- **The Schur–Horn theorem for a Hermitian matrix.** The diagonals of the matrices `U A Uᴴ`,
for `U` unitary, form exactly the convex hull of the rearrangements of the eigenvalues of the
Hermitian matrix `A`. -/
theorem IsHermitian.range_re_diag_unitary_mul_mul_star {A : Matrix ι ι 𝕜} (hA : A.IsHermitian) :
    (Set.range fun (U : unitaryGroup ι 𝕜) (k : ι) ↦
      RCLike.re ((U * A * star U : Matrix ι ι 𝕜) k k)) =
      convexHull ℝ (Set.range fun σ : Equiv.Perm ι ↦ hA.eigenvalues ∘ σ) := by
  rw [← range_re_diag_unitary_mul_diagonal_mul_star (𝕜 := 𝕜)]
  -- By the spectral theorem `A = V diag(λ) Vᴴ`, so `U A Uᴴ = (U V) diag(λ) (U V)ᴴ`, and
  -- `U ↦ U V` is a bijection of the unitary group.
  have hconj (U : unitaryGroup ι 𝕜) : (U * A * star U : Matrix ι ι 𝕜) =
      ((U * hA.eigenvectorUnitary : unitaryGroup ι 𝕜) : Matrix ι ι 𝕜) *
        diagonal (fun i ↦ (hA.eigenvalues i : 𝕜)) *
          star ((U * hA.eigenvectorUnitary : unitaryGroup ι 𝕜) : Matrix ι ι 𝕜) := by
    conv_lhs => rw [hA.spectral_theorem]
    simp [Unitary.conjStarAlgAut_apply, star_mul, mul_assoc, Function.comp_def]
  simp_rw [hconj]
  exact (Equiv.mulRight hA.eigenvectorUnitary).surjective.range_comp
    (fun (V : unitaryGroup ι 𝕜) (k : ι) ↦
      RCLike.re ((V * diagonal (fun i ↦ (hA.eigenvalues i : 𝕜)) * star V : Matrix ι ι 𝕜) k k))

/-! ### Orbits of rank at most one and the standard simplex -/

/-- The unitary orbit of `diag(0, …, c, …, 0)` consists of matrices of rank at most one: `U`
conjugates it to `c v vᴴ`, where `v` is the column of `U` at the position of `c`. -/
theorem mul_diagonal_single_mul_star (U : Matrix ι ι 𝕜) (i₀ : ι) (c : ℝ) :
    U * diagonal (fun i ↦ ((Pi.single i₀ c : ι → ℝ) i : 𝕜)) * star U =
      (c : 𝕜) • vecMulVec (fun k ↦ U k i₀) (star fun k ↦ U k i₀) := by
  ext k l
  rw [Matrix.mul_apply, Finset.sum_eq_single i₀ (fun i _ hi ↦ by simp [mul_diagonal, hi]) (by simp)]
  simp only [mul_diagonal, Pi.single_eq_same, Matrix.star_apply, Matrix.smul_apply,
    vecMulVec_apply, Pi.star_apply, smul_eq_mul]
  ring

/-- **The Schur–Horn theorem in rank at most one.** The diagonals of the unitary orbit of
`diag(0, …, c, …, 0)`, the matrices `c v vᴴ` for unit vectors `v`, form the simplex with vertices
`c eᵢ`, the standard simplex scaled by `c`. For `c ≠ 0` this orbit is the projective space of
lines in `𝕜ⁿ` (`ℂℙⁿ⁻¹` when `𝕜 = ℂ`), and the simplex is its moment image. -/
theorem range_re_diag_unitary_mul_diagonal_single_mul_star (i₀ : ι) (c : ℝ) :
    (Set.range fun (U : unitaryGroup ι 𝕜) (k : ι) ↦
      RCLike.re ((U * diagonal (fun i ↦ ((Pi.single i₀ c : ι → ℝ) i : 𝕜)) * star U :
        Matrix ι ι 𝕜) k k)) = convexHull ℝ (Set.range fun i ↦ Pi.single i c) := by
  rw [range_re_diag_unitary_mul_diagonal_mul_star]
  congr 1
  ext x
  simp only [Set.mem_range]
  refine ⟨fun ⟨σ, hσ⟩ ↦ ⟨σ.symm i₀, ?_⟩, fun ⟨i, hi⟩ ↦ ⟨Equiv.swap i₀ i, ?_⟩⟩
  · rw [← hσ]
    ext k
    simp [Pi.single_apply, Equiv.eq_symm_apply]
  · rw [← hi]
    ext k
    simp [Pi.single_apply, Equiv.swap_apply_eq_iff]

/-! ### The `2 × 2` case -/

/-- **The `2 × 2` Schur–Horn theorem.** For `l₂ ≤ l₁`, a real symmetric `2 × 2` matrix with
diagonal `(d₁, d₂)` and characteristic polynomial `(X - l₁) (X - l₂)` exists exactly when
`(d₁, d₂)` is majorized by `(l₁, l₂)`, that is, when `l₂ ≤ d₁ ≤ l₁` and `d₁ + d₂ = l₁ + l₂`. In
that case `!![d₁, b; b, d₂]` with `b = √((l₁ - d₁) (d₁ - l₂))` is such a matrix. -/
theorem exists_isSymm_fin_two_charpoly_eq_iff {l₁ l₂ d₁ d₂ : ℝ} (hl : l₂ ≤ l₁) :
    (∃ A : Matrix (Fin 2) (Fin 2) ℝ, A.IsSymm ∧ A 0 0 = d₁ ∧ A 1 1 = d₂ ∧
      A.charpoly = (X - C l₁) * (X - C l₂)) ↔ l₂ ≤ d₁ ∧ d₁ ≤ l₁ ∧ d₁ + d₂ = l₁ + l₂ := by
  have hpoly : (X - C l₁) * (X - C l₂) = X ^ 2 - C (l₁ + l₂) * X + C (l₁ * l₂) := by
    simp only [map_add, map_mul]
    ring
  refine ⟨fun ⟨A, hA, h₀, h₁, hχ⟩ ↦ ?_, fun ⟨h₁, h₂, hsum⟩ ↦ ?_⟩
  · -- Compare the coefficients of `X` and `1` in the two characteristic polynomials.
    rw [charpoly_fin_two, hpoly] at hχ
    have htr : A.trace = l₁ + l₂ := by
      linarith [show -A.trace = -l₂ + -l₁ by
        simpa using congr_arg (AddMonoidAlgebra.coeff · 1) hχ]
    have hdet : A.det = l₁ * l₂ := by
      simpa using congr_arg (AddMonoidAlgebra.coeff · 0) hχ
    have h₁₀ : A 1 0 = A 0 1 := hA.apply 0 1
    rw [trace_fin_two, h₀, h₁] at htr
    rw [det_fin_two, h₀, h₁, h₁₀] at hdet
    -- The off-diagonal entry satisfies `b² = (l₁ - d₁) (d₁ - l₂)`.
    have hb : (l₁ - d₁) * (d₁ - l₂) = A 0 1 ^ 2 := by
      have : d₂ = l₁ + l₂ - d₁ := by linarith
      subst this
      linear_combination hdet
    refine ⟨?_, ?_, htr⟩ <;> nlinarith [sq_nonneg (A 0 1)]
  · have hb : √((l₁ - d₁) * (d₁ - l₂)) * √((l₁ - d₁) * (d₁ - l₂)) = (l₁ - d₁) * (d₁ - l₂) :=
      Real.mul_self_sqrt (mul_nonneg (sub_nonneg.2 h₂) (sub_nonneg.2 h₁))
    refine ⟨!![d₁, √((l₁ - d₁) * (d₁ - l₂)); √((l₁ - d₁) * (d₁ - l₂)), d₂], ?_, rfl, rfl, ?_⟩
    · ext i j
      fin_cases i <;> fin_cases j <;> rfl
    · rw [charpoly_fin_two, trace_fin_two, det_fin_two, hpoly]
      simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one,
        hb]
      rw [hsum]
      congr 2
      linear_combination d₁ * hsum

end Matrix
