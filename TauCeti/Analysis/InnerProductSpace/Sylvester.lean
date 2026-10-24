/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.OpNormDefect
public import TauCeti.Analysis.InnerProductSpace.PointSpectrum

/-!
# The Sylvester operator: dimension-free bounds and the finite-dimensional equation

For bounded operators `A : E →L[𝕜] E` and `B : F →L[𝕜] F`, the *Sylvester operator*
`A.sylvester B` sends `X : F →L[𝕜] E` to `A ∘L X - X ∘L B`. The Sylvester equation
`A X - X B = C` is the linear equation through which spectral gaps control the motion of spectral
subspaces under perturbation (Davis–Kahan, Bhatia–Davis–McIntosh).

Quadratic-form separation bounds solutions in operator norm, in every dimension. If
`re ⟪A x, x⟫ ≥ α ‖x‖²` and `re ⟪B y, y⟫ ≥ β ‖y‖²`, then `(α + β) ‖X‖ ≤ ‖A X + X B‖`; this needs
neither symmetry, completeness nor finite dimension. Taking `α = β = δ > 0` gives the Lyapunov
bound `‖X‖ ≤ ‖A X + X B‖ / (2 δ)`. Replacing `B` by `-B` gives the separated Sylvester bound: if
the form of `A` is at least `c + g` and that of `B` at most `c`, then `g ‖X‖ ≤ ‖A X - X B‖`. The
reverse orientation follows in the same way. The proof evaluates the equation on unit vectors `v`
with `‖X v‖` close to `‖X‖`. For such `v`, the Cauchy–Schwarz inequality for the positive
semidefinite form `‖X‖² ⟪·, ·⟫ - ⟪X ·, X ·⟫`
(`ContinuousLinearMap.sq_opNorm_sq_mul_re_inner_sub_re_inner_le`) makes `re ⟪X (B v), X v⟫` close
to `‖X‖² re ⟪B v, v⟫`.

When `A` is symmetric, the equation diagonalises on eigenvectors: if `A u = α u` and `B v = β v`
with `α` real and `β : 𝕜`, then `⟪u, (A X - X B) v⟫ = (α - β) ⟪u, X v⟫`. Only `E` needs an
inner product for this identity. Dually, when `B` is symmetric, the rank-one operator formed from
eigenvectors of `A` and `B` has Sylvester eigenvalue `α - β`; here only `F` needs an inner product,
and `α : 𝕜` may be arbitrary. In finite dimension, choosing
orthonormal eigenbases `(uᵢ)` of `A` and `(vⱼ)` of `B` turns the equation into the scalar equations
`(αᵢ - βⱼ) Xᵢⱼ = Cᵢⱼ` on the matrix coefficients `Xᵢⱼ = ⟪uᵢ, X vⱼ⟫`. If no eigenvalue of `A` is an
eigenvalue of `B`, every `αᵢ - βⱼ` is nonzero, so the Sylvester operator is bijective and the
unique solution is obtained by dividing each coefficient of `C` by the corresponding eigenvalue
difference.

The spectral hypothesis is phrased as disjointness of the real point spectra
`Module.End.restrictedPointSpectrum A ⊤` and `Module.End.restrictedPointSpectrum B ⊤`. A positive
separation `Module.End.PointSpectraSeparated A ⊤ B ⊤ δ` with `0 < δ` supplies it through
`Module.End.PointSpectraSeparated.disjoint`.

## Main definitions

* `ContinuousLinearMap.sylvester A B`: the continuous linear map `X ↦ A ∘L X - X ∘L B` on
  `F →L[𝕜] E`.

## Main statements

* `OrthonormalBasis.sum_sum_inner_mul_inner_mul_inner`: the expansion
  `⟪x, T y⟫ = ∑ᵢ ∑ⱼ ⟪x, uᵢ⟫ ⟪uᵢ, T vⱼ⟫ ⟪vⱼ, y⟫` in orthonormal bases `(uᵢ)`, `(vⱼ)`.
* `OrthonormalBasis.sum_inner_smul_rankOne`: for orthonormal bases `(uᵢ)`, `(vⱼ)`, every operator
  `C` is the sum of `⟪uᵢ, C vⱼ⟫` times the rank-one operators `rankOne 𝕜 uᵢ vⱼ`.
* `ContinuousLinearMap.sub_smul_one_sylvester_sub_smul_one`: the Sylvester operator is unchanged
  when `A` and `B` are shifted by the same scalar.
* `ContinuousLinearMap.add_mul_norm_le_norm_comp_add_comp`: if the forms of `A` and `B` are
  bounded below by `α` and `β`, then `(α + β) ‖X‖ ≤ ‖A X + X B‖`.
* `ContinuousLinearMap.mul_norm_le_norm_sylvester_apply_of_le_re_inner_of_re_inner_le`,
  `ContinuousLinearMap.mul_norm_le_norm_sylvester_apply_of_re_inner_le_of_le_re_inner`: if the
  forms of `A` and `B` are separated by `g`, in either order, then `g ‖X‖ ≤ ‖A X - X B‖`.
* `ContinuousLinearMap.inner_sylvester_apply_of_apply_eq_smul`: for symmetric `A` and eigenvectors
  `A u = α u`, `B v = β v`, `⟪u, A.sylvester B X v⟫ = (α - β) ⟪u, X v⟫`.
* `ContinuousLinearMap.sylvester_rankOne_of_apply_eq_smul`: for symmetric `B` and eigenvectors
  `A u = α u`, `B v = β v`, the Sylvester operator acts on `rankOne 𝕜 u v` as the scalar `α - β`.
* `ContinuousLinearMap.inner_sylvester_apply_eigenvectorBasis`: the same identity on the matrix
  coefficients in ordered eigenbases.
* `ContinuousLinearMap.sylvester_injective`: in finite dimension, for symmetric `A` and `B` with
  disjoint point spectra, the Sylvester operator is injective.
* `ContinuousLinearMap.sylvester_sum_eigenvectorBasis`: under the same hypotheses, dividing the
  eigenbasis coefficients of `C` by the eigenvalue differences gives a solution of
  `A X - X B = C`.
* `ContinuousLinearMap.sylvester_bijective`, `ContinuousLinearMap.sylvester_apply_eq_iff`: the
  Sylvester operator is bijective, and that coefficient formula gives the unique solution.

## References

* J. J. Sylvester, *Sur l'équation en matrices `px = xq`*, C. R. Acad. Sci. Paris **99** (1884).
* R. Bhatia, *Matrix Analysis*, Graduate Texts in Mathematics 169, Springer (1997), §VII.2.
* R. Bhatia, C. Davis, A. McIntosh, *Perturbation of spectral subspaces and solution of linear
  operator equations*, Linear Algebra Appl. **52/53** (1983), 45–67.
-/

public section

open InnerProductSpace Module
open scoped InnerProductSpace

namespace OrthonormalBasis

variable {𝕜 E F ι κ : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [Fintype ι] [Fintype κ]

/-- **Expansion in rank-one operators.** For orthonormal bases `(uᵢ)` of `E` and `(vⱼ)` of `F`,
every `C : F →L[𝕜] E` is the sum of its matrix coefficients `⟪uᵢ, C vⱼ⟫` times the rank-one
operators `rankOne 𝕜 uᵢ vⱼ : x ↦ ⟪vⱼ, x⟫ uᵢ`. -/
theorem sum_inner_smul_rankOne (u : OrthonormalBasis ι 𝕜 E) (v : OrthonormalBasis κ 𝕜 F)
    (C : F →L[𝕜] E) : ∑ i, ∑ j, ⟪u i, C (v j)⟫_𝕜 • rankOne 𝕜 (u i) (v j) = C := by
  have hC : C = (∑ i, rankOne 𝕜 (u i) (u i)) ∘L C ∘L ∑ j, rankOne 𝕜 (v j) (v j) := by
    simp [sum_rankOne_eq_id]
  conv_rhs => rw [hC]
  simp only [ContinuousLinearMap.comp_finsetSum, comp_rankOne, sum_apply,
    rankOne_apply, map_sum, map_smul, smul_apply]
  exact Finset.sum_comm

/-- **Matrix coefficients of an inner product.** For orthonormal bases `(uᵢ)` of `E` and `(vⱼ)` of
`F`, `⟪x, T y⟫ = ∑ᵢ ∑ⱼ ⟪x, uᵢ⟫ ⟪uᵢ, T vⱼ⟫ ⟪vⱼ, y⟫` for every linear map `T : F →ₗ[𝕜] E`. -/
theorem sum_sum_inner_mul_inner_mul_inner (u : OrthonormalBasis ι 𝕜 E)
    (v : OrthonormalBasis κ 𝕜 F) (T : F →ₗ[𝕜] E) (x : E) (y : F) :
    ∑ i, ∑ j, ⟪x, u i⟫_𝕜 * ⟪u i, T (v j)⟫_𝕜 * ⟪v j, y⟫_𝕜 = ⟪x, T y⟫_𝕜 := by
  rw [← u.sum_inner_mul_inner x (T y)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  conv_rhs => rw [← v.sum_repr' y]
  simp only [map_sum, map_smul, inner_sum, inner_smul_right, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ ↦ by ring

end OrthonormalBasis

namespace ContinuousLinearMap

section Normed

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The *Sylvester operator* of `A : E →L[𝕜] E` and `B : F →L[𝕜] F`: the continuous linear map
`X ↦ A ∘L X - X ∘L B` on `F →L[𝕜] E`. Its equation `A.sylvester B X = C` is the Sylvester
equation `A X - X B = C`, and its kernel consists of the intertwiners `A X = X B`. -/
noncomputable def sylvester (A : E →L[𝕜] E) (B : F →L[𝕜] F) : (F →L[𝕜] E) →L[𝕜] F →L[𝕜] E :=
  compL 𝕜 F E E A - (compL 𝕜 F F E).flip B

@[simp]
theorem sylvester_apply (A : E →L[𝕜] E) (B : F →L[𝕜] F) (X : F →L[𝕜] E) :
    A.sylvester B X = A ∘L X - X ∘L B := by
  simp [sylvester]

/-- The Sylvester operator is unchanged when both operators are shifted by the same scalar:
`(A - c) X - X (B - c) = A X - X B`. -/
@[simp]
theorem sub_smul_one_sylvester_sub_smul_one (A : E →L[𝕜] E) (B : F →L[𝕜] F) (c : 𝕜) :
    (A - c • 1).sylvester (B - c • 1) = A.sylvester B := by
  ext X y
  simp [sub_comp, comp_sub]

end Normed

section Bounds

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  {A : E →L[𝕜] E} {B : F →L[𝕜] F}

/-- **The coercivity bound for `A X + X B`.** If the real parts of the quadratic forms of `A` and
`B` are bounded below by `α` and `β`, then `(α + β) ‖X‖ ≤ ‖A X + X B‖` for every bounded operator
`X`. Neither symmetry of `A` and `B`, completeness, nor finite dimension is assumed, and `α`, `β`
may have any sign. The codomain `E` may be seminormed. For `α = β = δ > 0` this is the Lyapunov
bound: every solution of `A X + X B = Y` satisfies `‖X‖ ≤ ‖Y‖ / (2 δ)`. -/
theorem add_mul_norm_le_norm_comp_add_comp {α β : ℝ}
    (hA : ∀ x, α * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜) (hB : ∀ y, β * ‖y‖ ^ 2 ≤ RCLike.re ⟪B y, y⟫_𝕜)
    (X : F →L[𝕜] E) : (α + β) * ‖X‖ ≤ ‖A ∘L X + X ∘L B‖ := by
  set Y := A ∘L X + X ∘L B
  rcases (norm_nonneg X).eq_or_lt with hX | hX
  · rw [← hX, mul_zero]
    exact norm_nonneg _
  -- For a unit vector `v`, the defect `‖X‖ - ‖X v‖` controls how far the inequality can fail.
  have key (v : F) (hv : ‖v‖ = 1) :
      α * ‖X v‖ ^ 2 + β * ‖X‖ ^ 2 - ‖Y‖ * ‖X v‖ ≤ ‖B‖ * ‖X‖ * √(‖X‖ ^ 2 - ‖X v‖ ^ 2) := by
    have hXv : ‖X v‖ ≤ ‖X‖ := by simpa [hv] using X.le_opNorm v
    have hBv : ‖B v‖ ≤ ‖B‖ := by simpa [hv] using B.le_opNorm v
    have hY : RCLike.re ⟪Y v, X v⟫_𝕜 ≤ ‖Y‖ * ‖X v‖ :=
      (re_inner_le_norm _ _).trans (by gcongr; simpa [hv] using Y.le_opNorm v)
    have hYv : RCLike.re ⟪Y v, X v⟫_𝕜 =
        RCLike.re ⟪A (X v), X v⟫_𝕜 + RCLike.re ⟪X (B v), X v⟫_𝕜 := by
      simp [Y, inner_add_left]
    have hCS := X.sq_opNorm_sq_mul_re_inner_sub_re_inner_le (B v) v
    rw [hv, one_pow, mul_one] at hCS
    have hD : ‖X‖ ^ 2 * RCLike.re ⟪B v, v⟫_𝕜 - RCLike.re ⟪X (B v), X v⟫_𝕜 ≤
        ‖B‖ * ‖X‖ * √(‖X‖ ^ 2 - ‖X v‖ ^ 2) := by
      rw [← Real.sqrt_sq (by positivity : 0 ≤ ‖B‖ * ‖X‖), ← Real.sqrt_mul (by positivity)]
      refine Real.le_sqrt_of_sq_le (hCS.trans (mul_le_mul_of_nonneg_right ?_ ?_))
      · have : ‖B v‖ ^ 2 ≤ ‖B‖ ^ 2 := by gcongr
        nlinarith [mul_le_mul_of_nonneg_left this (sq_nonneg ‖X‖), sq_nonneg ‖X (B v)‖]
      · nlinarith [norm_nonneg (X v)]
    have := hA (X v)
    have := hB v
    rw [hv] at this
    nlinarith
  -- `‖X‖` is a limit of values `‖X v‖` on the unit sphere, where `key` holds.
  set S := (fun v ↦ ‖X v‖) '' Metric.sphere (0 : F) 1
  have hSup : sSup S = ‖X‖ := X.sSup_sphere_eq_norm
  have hne : S.Nonempty := by
    refine Set.nonempty_iff_ne_empty.mpr fun h ↦ hX.ne ?_
    rw [← hSup, h, Real.sSup_empty]
  have hbdd : BddAbove S := by
    refine ⟨‖X‖, ?_⟩
    rintro - ⟨v, hv, rfl⟩
    simpa [mem_sphere_zero_iff_norm.1 hv] using X.le_opNorm v
  have hlim : ‖X‖ ∈ {r : ℝ | α * r ^ 2 + β * ‖X‖ ^ 2 - ‖Y‖ * r ≤
      ‖B‖ * ‖X‖ * √(‖X‖ ^ 2 - r ^ 2)} := by
    refine closure_minimal ?_ (isClosed_le (by fun_prop) (by fun_prop))
      (hSup ▸ csSup_mem_closure hne hbdd)
    rintro - ⟨v, hv, rfl⟩
    exact key v (mem_sphere_zero_iff_norm.1 hv)
  simp only [Set.mem_ofPred_eq, sub_self, Real.sqrt_zero, mul_zero] at hlim
  exact le_of_mul_le_mul_right (by linarith) hX

/-- **The separated Sylvester bound.** If the real part of the quadratic form of `A` is at least
`c + g` and that of `B` is at most `c`, then `g ‖X‖ ≤ ‖A X - X B‖` for every bounded operator `X`.
For `g > 0`, every solution of `A X - X B = Y` therefore satisfies `‖X‖ ≤ ‖Y‖ / g`. -/
theorem mul_norm_le_norm_sylvester_apply_of_le_re_inner_of_re_inner_le {c g : ℝ}
    (hA : ∀ x, (c + g) * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜)
    (hB : ∀ y, RCLike.re ⟪B y, y⟫_𝕜 ≤ c * ‖y‖ ^ 2) (X : F →L[𝕜] E) :
    g * ‖X‖ ≤ ‖A.sylvester B X‖ := by
  have hB' (y : F) : -c * ‖y‖ ^ 2 ≤ RCLike.re ⟪(-B) y, y⟫_𝕜 := by
    simpa [inner_neg_left] using hB y
  simpa [sub_eq_add_neg] using add_mul_norm_le_norm_comp_add_comp hA hB' X

/-- **The reverse separated Sylvester bound.** If the real part of the quadratic form of `A` is at
most `c` and that of `B` is at least `c + g`, then `g ‖X‖ ≤ ‖A X - X B‖` for every bounded operator
`X`. For `g > 0`, every solution of `A X - X B = Y` therefore satisfies `‖X‖ ≤ ‖Y‖ / g`. -/
theorem mul_norm_le_norm_sylvester_apply_of_re_inner_le_of_le_re_inner {c g : ℝ}
    (hA : ∀ x, RCLike.re ⟪A x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2)
    (hB : ∀ y, (c + g) * ‖y‖ ^ 2 ≤ RCLike.re ⟪B y, y⟫_𝕜) (X : F →L[𝕜] E) :
    g * ‖X‖ ≤ ‖A.sylvester B X‖ := by
  have hA' (x : E) : -c * ‖x‖ ^ 2 ≤ RCLike.re ⟪(-A) x, x⟫_𝕜 := by
    simpa [inner_neg_left] using hA x
  calc
    g * ‖X‖ ≤ ‖(-A) ∘L X + X ∘L B‖ := by
      simpa only [neg_add_cancel_left] using add_mul_norm_le_norm_comp_add_comp hA' hB X
    _ = ‖A.sylvester B X‖ := by
      rw [sylvester_apply, neg_comp, neg_add_eq_sub, norm_sub_rev]

end Bounds

section Eigenvectors

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]

/-- **The Sylvester equation on eigenvectors.** If `A` is symmetric, `A u = α u` and `B v = β v`
with `α` real and `β : 𝕜`, then the coefficient of `A X - X B` between `v` and `u` is `α - β`
times that of `X`. Only the space containing `u` needs an inner product. -/
theorem inner_sylvester_apply_of_apply_eq_smul [InnerProductSpace 𝕜 E] [NormedSpace 𝕜 F]
    {A : E →L[𝕜] E} {B : F →L[𝕜] F} (hA : (A : E →ₗ[𝕜] E).IsSymmetric)
    (X : F →L[𝕜] E) {α : ℝ} {β : 𝕜} {u : E} {v : F} (hu : A u = (α : 𝕜) • u)
    (hv : B v = β • v) :
    ⟪u, A.sylvester B X v⟫_𝕜 = ((α : 𝕜) - β) * ⟪u, X v⟫_𝕜 := by
  have hAu : ⟪u, A (X v)⟫_𝕜 = (α : 𝕜) * ⟪u, X v⟫_𝕜 := by
    rw [← hA.apply_clm u (X v), hu, inner_smul_left, RCLike.conj_ofReal]
  simp [hAu, hv, inner_sub_right, inner_smul_right, sub_mul]

/-- **The Sylvester operator on rank-one operators.** If `B` is symmetric, `A u = α u` and
`B v = β v` with `α : 𝕜` and `β` real, then the Sylvester operator acts on
`rankOne 𝕜 u v : x ↦ ⟪v, x⟫ u` as the scalar `α - β`. Only the space containing `v` needs an
inner product. -/
theorem sylvester_rankOne_of_apply_eq_smul [NormedSpace 𝕜 E] [InnerProductSpace 𝕜 F]
    {A : E →L[𝕜] E} {B : F →L[𝕜] F} (hB : (B : F →ₗ[𝕜] F).IsSymmetric) {α : 𝕜} {β : ℝ}
    {u : E} {v : F} (hu : A u = α • u) (hv : B v = (β : 𝕜) • v) :
    A.sylvester B (rankOne 𝕜 u v) = (α - (β : 𝕜)) • rankOne 𝕜 u v := by
  ext x
  have hBv : ⟪v, B x⟫_𝕜 = (β : 𝕜) * ⟪v, x⟫_𝕜 := by
    rw [← hB.apply_clm v x, hv, inner_smul_left, RCLike.conj_ofReal]
  simp [hu, hBv, smul_smul, sub_smul, mul_comm]

end Eigenvectors

section FiniteDimensional

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  {A : E →L[𝕜] E} {B : F →L[𝕜] F} [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] {n m : ℕ}

/-- **The Sylvester equation in eigenbases.** For symmetric `A` and `B` with ordered orthonormal
eigenbases `(uᵢ)`, `(vⱼ)` and eigenvalues `(αᵢ)`, `(βⱼ)`, the matrix coefficients of
`C = A X - X B` are `Cᵢⱼ = (αᵢ - βⱼ) Xᵢⱼ`, where `Xᵢⱼ = ⟪uᵢ, X vⱼ⟫`. -/
theorem inner_sylvester_apply_eigenvectorBasis (hA : (A : E →ₗ[𝕜] E).IsSymmetric)
    (hB : (B : F →ₗ[𝕜] F).IsSymmetric) (hn : finrank 𝕜 E = n) (hm : finrank 𝕜 F = m)
    (X : F →L[𝕜] E) (i : Fin n) (j : Fin m) :
    ⟪hA.eigenvectorBasis hn i, A.sylvester B X (hB.eigenvectorBasis hm j)⟫_𝕜 =
      ((hA.eigenvalues hn i - hB.eigenvalues hm j : ℝ) : 𝕜) *
        ⟪hA.eigenvectorBasis hn i, X (hB.eigenvectorBasis hm j)⟫_𝕜 := by
  simpa only [RCLike.ofReal_sub] using
    inner_sylvester_apply_of_apply_eq_smul hA X (hA.apply_eigenvectorBasis hn i)
      (hB.apply_eigenvectorBasis hm j)

/-- **Uniqueness for the Sylvester equation.** In finite dimension, if `A` and `B` are symmetric and
no real eigenvalue of `A` is an eigenvalue of `B`, the Sylvester operator `X ↦ A X - X B` is
injective. -/
theorem sylvester_injective (hA : (A : E →ₗ[𝕜] E).IsSymmetric) (hB : (B : F →ₗ[𝕜] F).IsSymmetric)
    (h : Disjoint (End.restrictedPointSpectrum (A : E →ₗ[𝕜] E) ⊤)
      (End.restrictedPointSpectrum (B : F →ₗ[𝕜] F) ⊤)) :
    Function.Injective (A.sylvester B) := by
  set u := hA.eigenvectorBasis rfl
  set v := hB.eigenvectorBasis rfl
  refine (injective_iff_map_eq_zero _).mpr fun X hX ↦ ?_
  -- Every eigenbasis coefficient of `X` vanishes, since its eigenvalue difference does not.
  have hcoeff (i j) : ⟪u i, X (v j)⟫_𝕜 = 0 := by
    have := inner_sylvester_apply_eigenvectorBasis hA hB rfl rfl X i j
    rw [hX, zero_apply, inner_zero_right, eq_comm, mul_eq_zero, RCLike.ofReal_eq_zero] at this
    exact this.resolve_left
      (sub_ne_zero.mpr (hA.eigenvalues_ne_eigenvalues_of_disjoint hB rfl rfl h i j))
  rw [← u.sum_inner_smul_rankOne v X]
  simp [hcoeff]

/-- **The canonical solution of the Sylvester equation.** In finite dimension, let `A` and `B` be
symmetric with ordered orthonormal eigenbases `(uᵢ)`, `(vⱼ)` and eigenvalues `(αᵢ)`, `(βⱼ)`, and
suppose no real eigenvalue of `A` is an eigenvalue of `B`. Then the operator whose coefficients are
`⟪uᵢ, C vⱼ⟫ / (αᵢ - βⱼ)`, namely the sum of `(αᵢ - βⱼ)⁻¹ ⟪uᵢ, C vⱼ⟫` times the rank-one operators
`rankOne 𝕜 uᵢ vⱼ : x ↦ ⟪vⱼ, x⟫ uᵢ`, solves `A X - X B = C`. -/
theorem sylvester_sum_eigenvectorBasis (hA : (A : E →ₗ[𝕜] E).IsSymmetric)
    (hB : (B : F →ₗ[𝕜] F).IsSymmetric) (hn : finrank 𝕜 E = n) (hm : finrank 𝕜 F = m)
    (h : Disjoint (End.restrictedPointSpectrum (A : E →ₗ[𝕜] E) ⊤)
      (End.restrictedPointSpectrum (B : F →ₗ[𝕜] F) ⊤)) (C : F →L[𝕜] E) :
    A.sylvester B (∑ i, ∑ j,
      ((((hA.eigenvalues hn i - hB.eigenvalues hm j)⁻¹ : ℝ) : 𝕜) *
          ⟪hA.eigenvectorBasis hn i, C (hB.eigenvectorBasis hm j)⟫_𝕜) •
        rankOne 𝕜 (hA.eigenvectorBasis hn i) (hB.eigenvectorBasis hm j)) = C := by
  conv_rhs => rw [← (hA.eigenvectorBasis hn).sum_inner_smul_rankOne (hB.eigenvectorBasis hm) C]
  simp only [map_sum, map_smul]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  have hij := sub_ne_zero.mpr (hA.eigenvalues_ne_eigenvalues_of_disjoint hB hn hm h i j)
  rw [sylvester_rankOne_of_apply_eq_smul hB (hA.apply_eigenvectorBasis hn i)
    (hB.apply_eigenvectorBasis hm j), ← RCLike.ofReal_sub, smul_smul, mul_right_comm,
    ← RCLike.ofReal_mul, inv_mul_cancel₀ hij, RCLike.ofReal_one, one_mul]

/-- **Bijectivity of the Sylvester operator.** In finite dimension, if `A` and `B` are symmetric
and no real eigenvalue of `A` is an eigenvalue of `B`, then for every `C` the Sylvester equation
`A X - X B = C` has exactly one solution. -/
theorem sylvester_bijective (hA : (A : E →ₗ[𝕜] E).IsSymmetric) (hB : (B : F →ₗ[𝕜] F).IsSymmetric)
    (h : Disjoint (End.restrictedPointSpectrum (A : E →ₗ[𝕜] E) ⊤)
      (End.restrictedPointSpectrum (B : F →ₗ[𝕜] F) ⊤)) :
    Function.Bijective (A.sylvester B) :=
  ⟨sylvester_injective hA hB h, fun C ↦ ⟨_, sylvester_sum_eigenvectorBasis hA hB rfl rfl h C⟩⟩

/-- **The solution of the Sylvester equation.** In finite dimension, if `A` and `B` are symmetric
and no real eigenvalue of `A` is an eigenvalue of `B`, then `X` solves `A X - X B = C` exactly when
its coefficients in ordered orthonormal eigenbases `(uᵢ)`, `(vⱼ)` of `A` and `B` are
`⟪uᵢ, C vⱼ⟫ / (αᵢ - βⱼ)`. -/
theorem sylvester_apply_eq_iff (hA : (A : E →ₗ[𝕜] E).IsSymmetric) (hB : (B : F →ₗ[𝕜] F).IsSymmetric)
    (hn : finrank 𝕜 E = n) (hm : finrank 𝕜 F = m)
    (h : Disjoint (End.restrictedPointSpectrum (A : E →ₗ[𝕜] E) ⊤)
      (End.restrictedPointSpectrum (B : F →ₗ[𝕜] F) ⊤)) {X C : F →L[𝕜] E} :
    A.sylvester B X = C ↔ X = ∑ i, ∑ j,
      ((((hA.eigenvalues hn i - hB.eigenvalues hm j)⁻¹ : ℝ) : 𝕜) *
          ⟪hA.eigenvectorBasis hn i, C (hB.eigenvectorBasis hm j)⟫_𝕜) •
        rankOne 𝕜 (hA.eigenvectorBasis hn i) (hB.eigenvectorBasis hm j) := by
  constructor
  · intro hX
    exact sylvester_injective hA hB h
      (hX.trans (sylvester_sum_eigenvectorBasis hA hB hn hm h C).symm)
  · rintro rfl
    exact sylvester_sum_eigenvectorBasis hA hB hn hm h C

end FiniteDimensional

end ContinuousLinearMap
