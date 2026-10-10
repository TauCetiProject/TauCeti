/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5, Claude Opus 4.8, Claude Opus 5
-/
module

/-
Staged for Tau Ceti, roadmap topic T02.  Mathlib is not the destination
(`ForTauCeti/README.md`); what follows is where this material would have gone on
the closed Mathlib track —
a proposed new file `Mathlib/Analysis/InnerProductSpace/NearIsometry.lean`.

Formalized by Claude Fable 5 (claude-fable-5[1m]); golf pass by Claude Opus 4.8
(claude-opus-4-8[1m]); redesigned around the polar factorization by Claude Opus 5
(claude-opus-5[1m]) per the `mathlib-quality` rules.
-/

public import TauCeti.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Spectrum

/-! # A near-isometry is close to a genuine isometry (via the polar factorization)

A linear map `M` on a finite-dimensional real inner product space whose quadratic form
`x ↦ ⟪M x, M x⟫` is uniformly `δ`-close to `x ↦ ⟪x, x⟫` (with `δ < 1`)
factors as `M = W ∘ S`
with `W` a linear isometry equivalence and `S` a square root of the Gram operator `Mᵀ ∘ M`
that moves no vector by more than `δ`.  In particular `M` lies within `δ` of the genuine
isometry `W`: `‖M x - W x‖ ≤ δ * ‖x‖`.

The factorization is the *polar decomposition* `M = W |M|`: `S = (Mᵀ M)^(1/2)` is built
directly from the orthonormal eigenbasis of the Gram operator
(`LinearMap.IsSymmetric.eigenvectorBasis`), and `W = M ∘ S⁻¹`.  So the proof uses neither the
continuous functional calculus nor a singular value decomposition.  This keeps the
finite-dimensional proof elementary and independent of the bounded-operator
functional-calculus route.

Exposing the factorization, rather than only the estimate, is what makes the constant sharp.
Because `W` is an isometry and `M x = W (S x)`,

  `‖M x - W x‖ = ‖W (S x) - W x‖ = ‖S x - x‖`,

so the operator estimate *is* the scalar estimate `|√μ - 1| ≤ |μ - 1| ≤ δ` on the
eigenvalues
`μ` of the Gram operator (`Real.abs_sqrt_sub_one_le_abs_sub_one`), with no loss.
Estimating instead through `M ∘ (1 - S⁻¹)` — the route that gives the constant `2 * δ` —
pays
an avoidable `‖M‖ ≤ √(1 + δ)` factor and needs `δ ≤ 1 / 2`.

## Main results

* `LinearMap.exists_linearIsometryEquiv_comp_polarFactor`: the polar factorization
  `M = W ∘ S` with `S ∘ S = Mᵀ ∘ M`, `S` symmetric, and
  `‖S x - x‖ ≤ δ * ‖x‖`.  This is the
  primary statement; the estimates below are corollaries of it.
* `LinearMap.exists_linearIsometryEquiv_norm_sub_apply_le` and
  `ContinuousLinearMap.exists_linearIsometryEquiv_norm_sub_apply_le`: the sharp
  near-isometry estimate `‖M x - W x‖ ≤ δ * ‖x‖`, under the pointwise quadratic-form
  hypothesis and the operator-norm hypothesis `‖Mᵀ M - 1‖ ≤ δ` respectively.
* `LinearMap.exists_linearIsometryEquiv_norm_sub_le` and
  `ContinuousLinearMap.exists_linearIsometryEquiv_norm_sub_le`: the historical
  statements, with the weaker constant `2 * δ` under `δ ≤ 1 / 2`.  Retained because they are
  the form quoted by the downstream paper development and by the challenge comparator; both
  are now one-line corollaries.

## Design note: why retain the finite-dimensional factorization

`ForTauCeti/Analysis/InnerProductSpace/Polar/Isometry.lean` defines the canonical bounded polar
isometry `ContinuousLinearMap.polarIsometryOfIsUnitModulus M = M ∘L Ring.inverse |M|` over an
arbitrary `RCLike` field and proves the same sharp estimate without a finite-dimensionality
assumption.  The theorem here is retained because its conclusion exposes the finite spectral
factorization data directly: it returns `W` and `S`, with `S ∘ S = Mᵀ ∘ M`, symmetry of `S`,
and the pointwise square-root estimate.  Downstream finite-dimensional arguments use those
witnesses, while callers that only need the canonical bounded factor can use `Polar/Isometry.lean`.

## Scalars: what is open, and what it would cost

The operator results here are stated over `ℝ`.  The `RCLike` form is open, and the
obstruction is bookkeeping rather than mathematics: the eigenbasis machinery
(`LinearMap.IsSymmetric.eigenvectorBasis`) already works over `RCLike`, so what has to be
redone is the real-inner-product arithmetic in the proofs below — the places where a real
inner product is used as a real number without a `RCLike.re`.

**This is a different situation from the entrywise operator-norm bound in
`ForTauCeti/Analysis/Matrix/EntrywiseOpNorm.lean`**, whose `RCLike` form needs a
re-derivation because `Matrix.toEuclideanLin` changes convention over `𝕜`.  Here the
statements are convention-free and only the proofs move.

## References

* N. J. Higham, *Functions of Matrices: Theory and Computation*, SIAM, 2008, Ch. 8
  (the unitary polar factor as the nearest isometry).

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `ForMathlib/Analysis/InnerProductSpace/NearIsometry.lean`
  at Davis--Kahan commit `fc38eb4`.
* Original declarations: `ForMathlib.Real.abs_one_sub_inv_sqrt_le` (moved to
  `ForTauCeti/Analysis/SpecialFunctions/Sqrt.lean`),
  `ForMathlib.LinearMap.exists_linearIsometryEquiv_norm_sub_le`, and
  `ContinuousLinearMap.exists_linearIsometryEquiv_norm_sub_le`
  (renamed here `ForMathlib.*` → `TauCeti.*`).
* Original authorship: formalized by Claude Fable 5 (`claude-fable-5[1m]`), golf
  pass by Claude Opus 4.8 (`claude-opus-4-8[1m]`); staged for Mathlib (no
  separate copyright line in the source header), released under Apache 2.0.
* Extraction class: **copied, then redesigned** per the signature-polish
  backlog — the existential now carries the polar
  factorization, the constant is sharp, and the scalar `Real.sqrt` lemmas were moved out.
* Spectra influence: **none** (imports only Mathlib and the Tau Ceti `Real.sqrt` staging
  module).
-/

public section

namespace TauCeti

open scoped RealInnerProductSpace InnerProductSpace
open Module (finrank)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section Diagonal

variable {d : ℕ}

/-- The operator that scales the `k`-th vector of an orthonormal basis by `c k`. -/
private noncomputable def diagonal (b : OrthonormalBasis (Fin d) ℝ E) (c : Fin d → ℝ) :
    E →ₗ[ℝ] E :=
  b.toBasis.constr ℝ fun j => c j • b j

private theorem diagonal_basis (b : OrthonormalBasis (Fin d) ℝ E) (c : Fin d → ℝ)
    (k : Fin d) :
    diagonal b c (b k) = c k • b k := by
  have := b.toBasis.constr_basis ℝ (fun j => c j • b j) k
  rwa [OrthonormalBasis.coe_toBasis] at this

/-- **Diagonals compose pointwise.**  `diagonal b f ∘ₗ diagonal b g` is the
diagonal of the pointwise product. -/
private theorem diagonal_comp_diagonal (b : OrthonormalBasis (Fin d) ℝ E)
    (f g : Fin d → ℝ) :
    diagonal b f ∘ₗ diagonal b g = diagonal b (fun k => f k * g k) := by
  refine b.toBasis.ext fun k => ?_
  simp only [OrthonormalBasis.coe_toBasis, LinearMap.comp_apply, diagonal_basis, map_smul,
    smul_smul, mul_comm]

/-- **A diagonal minus the identity is diagonal**, with factors `c k - 1`. -/
private theorem diagonal_sub_id (b : OrthonormalBasis (Fin d) ℝ E) (c : Fin d → ℝ) :
    diagonal b c - LinearMap.id = diagonal b fun k => c k - 1 := by
  refine b.toBasis.ext fun k => ?_
  simp only [OrthonormalBasis.coe_toBasis, LinearMap.sub_apply, LinearMap.id_apply,
    diagonal_basis, sub_smul, one_smul]

/-- A diagonal operator acts on basis coordinates by scalar multiplication. -/
private theorem repr_diagonal (b : OrthonormalBasis (Fin d) ℝ E) (c : Fin d → ℝ) (x : E)
    (k : Fin d) : b.repr (diagonal b c x) k = c k * b.repr x k := by
  have hx : diagonal b c x = ∑ j : Fin d, b.repr x j • (c j • b j) := by
    conv_lhs => rw [← b.sum_repr x, map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [map_smul, diagonal_basis]
  rw [b.repr_apply_apply, hx, inner_sum, Finset.sum_eq_single k]
  · rw [real_inner_smul_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
      b.orthonormal.norm_eq_one k, b.repr_apply_apply]
    ring
  · intro j _ hjk
    rw [real_inner_smul_right, real_inner_smul_right, b.inner_eq_zero hjk.symm]
    ring
  · intro hk; exact absurd (Finset.mem_univ k) hk

private theorem isSymmetric_diagonal (b : OrthonormalBasis (Fin d) ℝ E) (c : Fin d → ℝ) :
    (diagonal b c).IsSymmetric := by
  have key :
      ∀ u v : E, ⟪diagonal b c u, v⟫_ℝ =
        ∑ k : Fin d, c k * b.repr u k * b.repr v k := by
    intro u v
    conv_lhs => rw [← b.sum_repr v]
    rw [inner_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [real_inner_smul_right, real_inner_comm, ← b.repr_apply_apply, repr_diagonal]
    ring
  intro x y
  rw [key, real_inner_comm, key]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- A diagonal operator whose scaling factors are bounded by `δ` has operator norm at most
`δ`, by Parseval. -/
private theorem norm_diagonal_apply_le (b : OrthonormalBasis (Fin d) ℝ E) (c : Fin d → ℝ)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hc : ∀ k, |c k| ≤ δ) (x : E) :
    ‖diagonal b c x‖ ≤ δ * ‖x‖ := by
  have hpars : ∀ y : E, ∑ k : Fin d, b.repr y k ^ 2 = ‖y‖ ^ 2 := by
    intro y
    rw [← b.sum_sq_inner_right y]
    exact Finset.sum_congr rfl fun k _ => by rw [b.repr_apply_apply]
  have hbnd : ‖diagonal b c x‖ ^ 2 ≤ δ ^ 2 * ‖x‖ ^ 2 := by
    rw [← hpars (diagonal b c x), ← hpars x, Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [repr_diagonal, mul_pow]
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    have := hc k
    nlinarith [abs_nonneg (c k), abs_le.mp (hc k), sq_abs (c k)]
  nlinarith [hbnd, norm_nonneg (diagonal b c x), mul_nonneg hδ0 (norm_nonneg x),
    sq_nonneg (‖diagonal b c x‖ - δ * ‖x‖)]

/-- A diagonal operator whose scaling factors are all within `δ` of `1` moves no vector by
more than `δ`.

This is the operator form of the scalar estimate that makes the near-isometry constant sharp:
`diagonal b c - 1` is again diagonal, with factors `c k - 1`. -/
private theorem norm_diagonal_apply_sub_self_le (b : OrthonormalBasis (Fin d) ℝ E)
    (c : Fin d → ℝ) {δ : ℝ} (hδ0 : 0 ≤ δ) (hc : ∀ k, |c k - 1| ≤ δ) (x : E) :
    ‖diagonal b c x - x‖ ≤ δ * ‖x‖ := by
  have hsub := diagonal_sub_id b c
  have hx : diagonal b c x - x = diagonal b (fun k => c k - 1) x := by
    have := congrArg (fun T : E →ₗ[ℝ] E => T x) hsub
    simpa using this
  rw [hx]
  exact norm_diagonal_apply_le b _ hδ0 hc x

end Diagonal

section OrthonormalBasis

variable {d : ℕ}

/-- A linear map that preserves the inner products *between the vectors of an orthonormal
basis* preserves all inner products.  Bilinearity does the rest. -/
private theorem inner_map_eq_of_inner_basis (b : OrthonormalBasis (Fin d) ℝ E)
    {W : E →ₗ[ℝ] E}
    (hW : ∀ j k : Fin d, ⟪W (b j), W (b k)⟫_ℝ = ⟪b j, b k⟫_ℝ)
    (x y : E) :
    ⟪W x, W y⟫_ℝ = ⟪x, y⟫_ℝ := by
  conv_lhs => rw [← b.sum_repr x, ← b.sum_repr y]
  conv_rhs => rw [← b.sum_repr x, ← b.sum_repr y]
  simp only [map_sum, map_smul, sum_inner, inner_sum, real_inner_smul_left,
    real_inner_smul_right]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [hW k j]

end OrthonormalBasis

end TauCeti

-- The following theorems extend Mathlib's LinearMap and ContinuousLinearMap.
-- Their namespaces must be at the root for dot notation and the upstream lint.
open scoped RealInnerProductSpace InnerProductSpace
open Module (finrank)
open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

namespace LinearMap

omit [FiniteDimensional ℝ E] in
/-- A quadratic-form perturbation bound forces `0 ≤ δ`, as soon as some vector is nonzero.

Extracted from `exists_linearIsometryEquiv_comp_polarFactor`, where the sign of `δ` is needed
before any eigenvalue reasoning can start. -/
private theorem nonneg_of_quadraticFormBound [Nontrivial E] {M : E →ₗ[ℝ] E} {δ : ℝ}
    (hM : ∀ x : E, |⟪M x, M x⟫_ℝ - ⟪x, x⟫_ℝ| ≤ δ * ⟪x, x⟫_ℝ) : 0 ≤ δ := by
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  have hvpos : 0 < ⟪v, v⟫_ℝ := real_inner_self_pos.mpr hv
  have hmul : 0 ≤ δ * ⟪v, v⟫_ℝ :=
    le_trans (abs_nonneg (⟪M v, M v⟫_ℝ - ⟪v, v⟫_ℝ)) (hM v)
  exact nonneg_of_mul_nonneg_left hmul hvpos

/-- On an orthonormal eigenbasis of the Gram operator `Mᵀ ∘ M`, the images under `M` are
orthogonal and their squared norms are the eigenvalues.

This is why `W = M ∘ S⁻¹` is an isometry in `exists_linearIsometryEquiv_comp_polarFactor`:
rescaling `M (b k)` by `(√ μ k)⁻¹` turns this Gram matrix into the identity. -/
private theorem inner_map_eigenvectorBasis {M : E →ₗ[ℝ] E} {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ E) (μ : Fin d → ℝ)
    (hunit : ∀ k, ⟪b k, b k⟫_ℝ = 1)
    (hGbasis : ∀ k, (M.adjoint * M) (b k) = μ k • b k) (j k : Fin d) :
    ⟪M (b j), M (b k)⟫_ℝ = if j = k then μ j else 0 := by
  have hadj : ⟪M (b j), M (b k)⟫_ℝ = ⟪(M.adjoint * M) (b j), b k⟫_ℝ := by
    rw [Module.End.mul_apply, LinearMap.adjoint_inner_left]
  rw [hadj, hGbasis j, real_inner_smul_left]
  by_cases hjk : j = k
  · subst hjk; rw [hunit j, ite_eq_left rfl, mul_one]
  · rw [b.inner_eq_zero hjk, ite_eq_right hjk, mul_zero]

/-- Rescaling the eigenbasis images by `(√ μ k)⁻¹` turns the Gram matrix of `M` into the
identity: a map sending `b k` to `(√ μ k)⁻¹ • M (b k)` preserves the inner products *between
basis vectors*.

With `inner_map_eq_of_inner_basis` this is the whole reason `W = M ∘ S⁻¹` is an isometry in
`exists_linearIsometryEquiv_comp_polarFactor`. -/
private theorem inner_basis_of_smul_inv_sqrt {M W : E →ₗ[ℝ] E} {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ E) {μ : Fin d → ℝ} (hμpos : ∀ k, 0 < μ k)
    (hunit : ∀ k, ⟪b k, b k⟫_ℝ = 1)
    (hGbasis : ∀ k, (M.adjoint * M) (b k) = μ k • b k)
    (hWbasis : ∀ k, W (b k) = (Real.sqrt (μ k))⁻¹ • M (b k)) (j k : Fin d) :
    ⟪W (b j), W (b k)⟫_ℝ = ⟪b j, b k⟫_ℝ := by
  rw [hWbasis, hWbasis, real_inner_smul_left, real_inner_smul_right,
    inner_map_eigenvectorBasis b μ hunit hGbasis]
  by_cases hjk : j = k
  · subst hjk
    rw [ite_eq_left rfl, hunit j]
    have hsj : 0 < Real.sqrt (μ j) := Real.sqrt_pos.mpr (hμpos j)
    have hsqj : Real.sqrt (μ j) * Real.sqrt (μ j) = μ j :=
      Real.mul_self_sqrt (le_of_lt (hμpos j))
    field_simp
    exact (Real.sq_sqrt (le_of_lt (hμpos j))).symm
  · rw [ite_eq_right hjk, b.inner_eq_zero hjk, mul_zero, mul_zero]

/-- An eigenvalue of the Gram operator `Mᵀ ∘ M` at a **unit** eigenvector lies within
`δ` of `1`.

This is the quantitative heart of `exists_linearIsometryEquiv_comp_polarFactor`: the hypothesis
says `M` distorts every quadratic form by at most `δ`, and on an eigenvector that distortion *is*
`μ - 1`.  Positivity of the eigenvalues, and hence invertibility of the square root, follows from
this bound together with `δ < 1`. -/
private theorem abs_eigenvalue_sub_one_le {M : E →ₗ[ℝ] E} {δ : ℝ}
    (hM : ∀ x : E, |⟪M x, M x⟫_ℝ - ⟪x, x⟫_ℝ| ≤ δ * ⟪x, x⟫_ℝ)
    {v : E} (hv : ⟪v, v⟫_ℝ = 1) {lam : ℝ}
    (hGv : (M.adjoint * M) v = lam • v) : |lam - 1| ≤ δ := by
  have hquad : ⟪(M.adjoint * M) v, v⟫_ℝ = ⟪M v, M v⟫_ℝ := by
    rw [Module.End.mul_apply, LinearMap.adjoint_inner_left]
  have hlam : ⟪(M.adjoint * M) v, v⟫_ℝ = lam := by
    rw [hGv, real_inner_smul_left, hv, mul_one]
  have hb := hM v
  rwa [← hquad, hlam, hv, mul_one] at hb

/-- The Gram operator `Mᵀ M` of a near-isometry has an orthonormal eigenbasis whose eigenvalues
all lie within `δ` of `1` — hence are positive, since `δ < 1`.

This is the entire spectral input to `exists_linearIsometryEquiv_comp_polarFactor`: everything
after it is the construction of `S = (Mᵀ M)^(1/2)` and `W = M ∘ S⁻¹` from this data. -/
private theorem exists_orthonormalBasis_gram (M : E →ₗ[ℝ] E) {δ : ℝ} (hδ : δ < 1)
    (hM : ∀ x : E, |⟪M x, M x⟫_ℝ - ⟪x, x⟫_ℝ| ≤ δ * ⟪x, x⟫_ℝ)
    {d : ℕ} (hd : finrank ℝ E = d) :
    ∃ (b : OrthonormalBasis (Fin d) ℝ E) (μ : Fin d → ℝ),
      (∀ k, ⟪b k, b k⟫_ℝ = 1) ∧ (∀ k, (M.adjoint * M) (b k) = μ k • b k) ∧
        (∀ k, |μ k - 1| ≤ δ) ∧ ∀ k, 0 < μ k := by
  have hGsymm : (M.adjoint * M).IsSymmetric := LinearMap.isSymmetric_adjoint_mul_self M
  set b := hGsymm.eigenvectorBasis hd with hb
  set μ := hGsymm.eigenvalues hd with hμ
  have hunit : ∀ k : Fin d, ⟪b k, b k⟫_ℝ = 1 := fun k => by
    rw [real_inner_self_eq_norm_sq, b.orthonormal.norm_eq_one k]; ring
  have hGbasis : ∀ k : Fin d, (M.adjoint * M) (b k) = μ k • b k := by
    intro k
    rw [hb, hGsymm.apply_eigenvectorBasis, ← hb, ← hμ]
    simp
  have hμbound : ∀ k : Fin d, |μ k - 1| ≤ δ := fun k =>
    abs_eigenvalue_sub_one_le hM (hunit k) (hGbasis k)
  refine ⟨b, μ, hunit, hGbasis, hμbound, fun k => ?_⟩
  have hk := hμbound k
  rw [abs_le] at hk
  linarith

/-- A linear map of a *finite-dimensional* space that preserves inner products is a linear
isometry **equivalence**.

Preserving inner products gives an isometry, hence injectivity; finite dimension upgrades that
to surjectivity, which is the only place `exists_linearIsometryEquiv_comp_polarFactor` needs
`E` to be finite-dimensional beyond the eigenbasis. -/
private theorem exists_linearIsometryEquiv_coe_eq {W : E →ₗ[ℝ] E}
    (hW : ∀ x y : E, ⟪W x, W y⟫_ℝ = ⟪x, y⟫_ℝ) :
    ∃ U : E ≃ₗᵢ[ℝ] E, ∀ x, U x = W x := by
  have hcoe : ⇑(W.isometryOfInner hW) = ⇑W := W.coe_isometryOfInner hW
  have hsurj : Function.Surjective (W.isometryOfInner hW) := by
    rw [hcoe]
    exact LinearMap.injective_iff_surjective.mp (hcoe ▸ (W.isometryOfInner hW).injective)
  refine ⟨LinearIsometryEquiv.ofSurjective _ hsurj, fun x => ?_⟩
  rw [LinearIsometryEquiv.coe_ofSurjective, hcoe]

/-- **Polar factorization of a near-isometry.**  If the quadratic form of a linear map `M` on a
finite-dimensional real inner product space is uniformly `δ`-close to the identity quadratic
form (`|⟪M x, M x⟫ - ⟪x, x⟫| ≤ δ * ⟪x, x⟫`, with `δ < 1`), then `M` factors
as `M = W ∘ S`
where

* `W` is a linear isometry equivalence of `E`,
* `S` is the modulus of `M`: symmetric, with `S ∘ S = Mᵀ ∘ M`, and
* `S` moves no vector by more than `δ`: `‖S x - x‖ ≤ δ * ‖x‖`.

`S` is built from the orthonormal eigenbasis of the Gram operator `Mᵀ ∘ M`, rescaling the
`k`-th eigenvector by `√(μ k)`; `W = M ∘ S⁻¹` is an isometry because
`⟪M b_j, M b_k⟫ = μ_j δ_jk`
on that basis.  Since the two stated properties of `S` determine it (a symmetric square root of
`Mᵀ M` that is close to the identity is *the* positive square root), this statement exposes the
canonical polar factor rather than an arbitrary witness — see the module docstring for why the
real case is stated existentially at all.

The hypothesis `δ < 1` is exactly what is needed: it forces the eigenvalues `μ k ≥ 1 - δ` of
the Gram operator to be positive, so that `S` is invertible and `M` is bounded below. -/
theorem exists_linearIsometryEquiv_comp_polarFactor (M : E →ₗ[ℝ] E) {δ : ℝ} (hδ : δ < 1)
    (hM : ∀ x : E, |⟪M x, M x⟫_ℝ - ⟪x, x⟫_ℝ| ≤ δ * ⟪x, x⟫_ℝ) :
    ∃ (W : E ≃ₗᵢ[ℝ] E) (S : E →ₗ[ℝ] E),
      (∀ x : E, M x = W (S x)) ∧ S.IsSymmetric ∧ S ∘ₗ S = M.adjoint ∘ₗ M ∧
        ∀ x : E, ‖S x - x‖ ≤ δ * ‖x‖ := by
  -- Degenerate case: if `E` is a subsingleton every vector is `0`.
  rcases subsingleton_or_nontrivial E with hsub | hnt
  · refine ⟨LinearIsometryEquiv.refl ℝ E, LinearMap.id, fun x => ?_, fun x y => ?_,
      LinearMap.ext fun x => ?_, fun x => ?_⟩ <;>
      simp [Subsingleton.elim x (0 : E)]
  -- Main case: `E` is nontrivial.  Derive `δ ≥ 0` from a nonzero vector.
  have hδ0 : 0 ≤ δ := nonneg_of_quadraticFormBound hM
  obtain ⟨d, hd⟩ : ∃ d, finrank ℝ E = d := ⟨_, rfl⟩
  -- Sorted eigen-data of the Gram operator `Mᵀ M`, with every eigenvalue within `δ` of `1`.
  obtain ⟨b, μ, hunit, hGbasis, hμbound, hμpos⟩ := exists_orthonormalBasis_gram M hδ hM hd
  have hsqrtpos : ∀ k : Fin d, 0 < Real.sqrt (μ k) := fun k => Real.sqrt_pos.mpr (hμpos k)
  -- The modulus `S = G^(1/2)` and its inverse `R = G^(-1/2)`, diagonal in the eigenbasis.
  set S : E →ₗ[ℝ] E := diagonal b (fun k => Real.sqrt (μ k)) with hS
  set R : E →ₗ[ℝ] E := diagonal b (fun k => (Real.sqrt (μ k))⁻¹) with hR
  have hRS : ∀ x : E, R (S x) = x := by
    have : R ∘ₗ S = LinearMap.id := by
      rw [hS, hR, diagonal_comp_diagonal]
      refine b.toBasis.ext fun k => ?_
      rw [OrthonormalBasis.coe_toBasis, LinearMap.id_apply, diagonal_basis,
        inv_mul_cancel₀ (ne_of_gt (hsqrtpos k)), one_smul]
    intro x
    exact congrArg (fun T : E →ₗ[ℝ] E => T x) this
  -- `S` is a square root of the Gram operator.
  have hSS : S ∘ₗ S = M.adjoint ∘ₗ M := by
    rw [hS, diagonal_comp_diagonal]
    refine b.toBasis.ext fun k => ?_
    rw [OrthonormalBasis.coe_toBasis, diagonal_basis,
      Real.mul_self_sqrt (le_of_lt (hμpos k))]
    exact (hGbasis k).symm
  -- The candidate isometry `W₀ = M ∘ R`, which is orthonormal on the eigenbasis.
  set W₀ : E →ₗ[ℝ] E := M ∘ₗ R with hW
  have hWbasis : ∀ k : Fin d, W₀ (b k) = (Real.sqrt (μ k))⁻¹ • M (b k) := fun k => by
    rw [hW, LinearMap.comp_apply, hR, diagonal_basis, map_smul]
  have hWortho := inner_basis_of_smul_inv_sqrt b hμpos hunit hGbasis hWbasis
  -- `S` moves no vector by more than `δ`, since `|√(μ k) - 1| ≤ |μ k - 1| ≤ δ`.
  have hSest : ∀ x : E, ‖S x - x‖ ≤ δ * ‖x‖ := by
    intro x
    rw [hS]
    exact norm_diagonal_apply_sub_self_le b _ hδ0
      (fun k => (Real.abs_sqrt_sub_one_le_abs_sub_one).trans (hμbound k)) x
  -- Bundle `W₀` as a linear isometry equivalence and read off the factorization.
  obtain ⟨U, hU⟩ := exists_linearIsometryEquiv_coe_eq (inner_map_eq_of_inner_basis b hWortho)
  refine ⟨U, S, fun x => ?_, hS ▸ isSymmetric_diagonal b _, hSS, hSest⟩
  rw [hU, hW, LinearMap.comp_apply, hRS]

/-- **The sharp near-isometry estimate.**  If the quadratic form of a linear map `M` on a
finite-dimensional real inner product space is uniformly `δ`-close to the identity quadratic
form (with `δ < 1`), then `M` lies within `δ` — not `2 * δ` — of a genuine linear isometry
equivalence.

This is immediate from `exists_linearIsometryEquiv_comp_polarFactor`: `M x - W x` is the image
under the isometry `W` of `S x - x`. -/
theorem exists_linearIsometryEquiv_norm_sub_apply_le (M : E →ₗ[ℝ] E) {δ : ℝ} (hδ : δ < 1)
    (hM : ∀ x : E, |⟪M x, M x⟫_ℝ - ⟪x, x⟫_ℝ| ≤ δ * ⟪x, x⟫_ℝ) :
    ∃ W : E ≃ₗᵢ[ℝ] E, ∀ x : E, ‖M x - W x‖ ≤ δ * ‖x‖ := by
  obtain ⟨W, S, hMS, -, -, hSest⟩ := exists_linearIsometryEquiv_comp_polarFactor M hδ hM
  refine ⟨W, fun x => ?_⟩
  rw [hMS x, ← map_sub, W.norm_map]
  exact hSest x

/-- **Quantitative polar factor for a near-isometry**, historical form.

Superseded by `LinearMap.exists_linearIsometryEquiv_norm_sub_apply_le`, which gives the
sharp constant `δ` under the weaker hypothesis `δ < 1`.  This statement is retained because it
is the form quoted downstream (`Acharyya2025.PolarFactor`) and by the challenge comparator. -/
theorem exists_linearIsometryEquiv_norm_sub_le (M : E →ₗ[ℝ] E) {δ : ℝ} (hδ : δ ≤ 1 / 2)
    (hM : ∀ x : E, |⟪M x, M x⟫_ℝ - ⟪x, x⟫_ℝ| ≤ δ * ⟪x, x⟫_ℝ) :
    ∃ W : E ≃ₗᵢ[ℝ] E, ∀ x : E, ‖M x - W x‖ ≤ 2 * δ * ‖x‖ := by
  obtain ⟨W, hW⟩ := exists_linearIsometryEquiv_norm_sub_apply_le M (by linarith) hM
  refine ⟨W, fun x => (hW x).trans ?_⟩
  rcases subsingleton_or_nontrivial E with hsub | hnt
  · simp [Subsingleton.elim x (0 : E)]
  · have hδ0 : 0 ≤ δ := by
      obtain ⟨v, hv⟩ := exists_ne (0 : E)
      have hvpos : 0 < ⟪v, v⟫_ℝ := real_inner_self_pos.mpr hv
      exact nonneg_of_mul_nonneg_left
        (le_trans (abs_nonneg (⟪M v, M v⟫_ℝ - ⟪v, v⟫_ℝ)) (hM v)) hvpos
    have := norm_nonneg x
    nlinarith

end LinearMap

namespace ContinuousLinearMap

/-- The operator-norm hypothesis `‖Mᵀ M - 1‖ ≤ δ` implies the pointwise quadratic-form
hypothesis, by Cauchy--Schwarz. -/
private theorem abs_inner_sub_le_of_norm_adjoint_mul_self_sub_one_le (M : E →L[ℝ] E) {δ : ℝ}
    (hM : ‖ContinuousLinearMap.adjoint M * M - 1‖ ≤ δ) (x : E) :
    |⟪(M : E →ₗ[ℝ] E) x, (M : E →ₗ[ℝ] E) x⟫_ℝ - ⟪x, x⟫_ℝ| ≤
      δ * ⟪x, x⟫_ℝ := by
  have hid : ⟪(ContinuousLinearMap.adjoint M * M - 1) x, x⟫_ℝ
      = ⟪(M : E →ₗ[ℝ] E) x, (M : E →ₗ[ℝ] E) x⟫_ℝ - ⟪x, x⟫_ℝ := by
    rw [sub_apply, mul_apply_eq_comp, one_apply_eq_self, inner_sub_left,
      ContinuousLinearMap.adjoint_inner_left]
    simp
  rw [← hid]
  calc |⟪(ContinuousLinearMap.adjoint M * M - 1) x, x⟫_ℝ|
      ≤ ‖(ContinuousLinearMap.adjoint M * M - 1) x‖ * ‖x‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖ContinuousLinearMap.adjoint M * M - 1‖ * ‖x‖ * ‖x‖ :=
        mul_le_mul_of_nonneg_right
          ((ContinuousLinearMap.adjoint M * M - 1).le_opNorm x) (norm_nonneg x)
    _ ≤ δ * ‖x‖ * ‖x‖ := by gcongr
    _ = δ * ⟪x, x⟫_ℝ := by rw [real_inner_self_eq_norm_mul_norm]; ring

/-- **The sharp near-isometry estimate, operator-norm form.**  If a continuous linear map `M` on
a finite-dimensional real inner product space satisfies `‖Mᵀ M - 1‖ ≤ δ` with `δ < 1`,
then `M`
lies within `δ` of a genuine linear isometry equivalence.

See `ContinuousLinearMap.norm_sub_polarIsometryOfIsUnitModulus_le` in
`ForTauCeti/Analysis/InnerProductSpace/Polar/Isometry.lean` for the version over arbitrary
`RCLike` Hilbert spaces, which additionally names the isometry. -/
theorem exists_linearIsometryEquiv_norm_sub_apply_le (M : E →L[ℝ] E) {δ : ℝ} (hδ : δ < 1)
    (hM : ‖ContinuousLinearMap.adjoint M * M - 1‖ ≤ δ) :
    ∃ W : E ≃ₗᵢ[ℝ] E, ∀ x : E, ‖M x - W x‖ ≤ δ * ‖x‖ := by
  obtain ⟨W, hW⟩ :=
    LinearMap.exists_linearIsometryEquiv_norm_sub_apply_le (M : E →ₗ[ℝ] E) hδ
    (abs_inner_sub_le_of_norm_adjoint_mul_self_sub_one_le M hM)
  exact ⟨W, fun x => by simpa using hW x⟩

/-- **Quantitative polar factor, operator-norm form**, historical statement.

Superseded by `ContinuousLinearMap.exists_linearIsometryEquiv_norm_sub_apply_le`;
retained for the downstream paper development and the challenge comparator. -/
theorem exists_linearIsometryEquiv_norm_sub_le (M : E →L[ℝ] E) {δ : ℝ} (hδ : δ ≤ 1 / 2)
    (hM : ‖ContinuousLinearMap.adjoint M * M - 1‖ ≤ δ) :
    ∃ W : E ≃ₗᵢ[ℝ] E, ∀ x : E, ‖M x - W x‖ ≤ 2 * δ * ‖x‖ := by
  obtain ⟨W, hW⟩ := LinearMap.exists_linearIsometryEquiv_norm_sub_le (M : E →ₗ[ℝ] E) hδ
    (abs_inner_sub_le_of_norm_adjoint_mul_self_sub_one_le M hM)
  exact ⟨W, fun x => by simpa using hW x⟩

end ContinuousLinearMap

end
