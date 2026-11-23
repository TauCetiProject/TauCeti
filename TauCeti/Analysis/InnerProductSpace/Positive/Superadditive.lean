/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import TauCeti.Analysis.InnerProductSpace.SchurHorn
public import TauCeti.Analysis.InnerProductSpace.SingularValues

/-!
# Superadditivity of convex spectral sums of positive operators

Let `A` and `B` be positive endomorphisms of an `n`-dimensional real or complex inner product
space, with eigenvalues `αᵢ`, `βᵢ` and `γᵢ` for `A`, `B` and `A + B`. For a function `φ` convex on
`[0, ∞)` with `φ 0 ≤ 0`,

`∑ᵢ φ(αᵢ) + ∑ᵢ φ(βᵢ) ≤ ∑ᵢ φ(γᵢ)`,

that is `tr φ(A) + tr φ(B) ≤ tr φ(A + B)`, and the inequality reverses for `φ` concave on `[0, ∞)`
with `0 ≤ φ 0`. For `φ(t) = tʳ` these are McCarthy's inequalities
`tr Aʳ + tr Bʳ ≤ tr (A + B)ʳ` for `1 ≤ r` and `tr (A + B)ʳ ≤ tr Aʳ + tr Bʳ` for `0 ≤ r ≤ 1`; the
concave case is Rotfel'd's trace inequality. For `0 < r ≤ 1` the concave inequality is the
`r`-triangle inequality `‖A + B‖ᵣʳ ≤ ‖A‖ᵣʳ + ‖B‖ᵣʳ` of the Schatten quasi-norms on positive
operators, and for `1 ≤ r` the convex one is the reverse bound `‖A‖ᵣʳ + ‖B‖ᵣʳ ≤ ‖A + B‖ᵣʳ`.

## The argument

Put `V x = (√A x, √B x)`, a map from `E` to the `L²` product `E × E`. Its source Gram operator
`V† V` is `A + B`, while its target Gram operator `V V†` acts on the `2n`-dimensional product, and
its diagonal entries in the orthonormal basis `(vᵢ, 0)`, `(0, wⱼ)` built from eigenbases of `A`
and `B` are `‖√A vᵢ‖² = αᵢ` and `‖√B wⱼ‖² = βⱼ`. The Schur–Horn inequality in Karamata form
(`LinearMap.IsSymmetric.sum_map_re_inner_apply_self_le_sum_map_eigenvalues`) bounds the sum of
`φ` over these diagonal entries by its sum over the eigenvalues of `V V†`. Those are the squared
singular values of `V`: the eigenvalues `γᵢ` of `V† V = A + B`, followed by `n` zeros, each of
which contributes `φ 0 ≤ 0`.

## Main results

* `LinearMap.IsPositive.sum_map_eigenvalues_add_sum_map_eigenvalues_le_sum_map_eigenvalues_add`:
  the convex inequality.
* `LinearMap.IsPositive.sum_map_eigenvalues_add_le_sum_map_eigenvalues_add_sum_map_eigenvalues`:
  the concave inequality.

## References

* C. A. McCarthy, *cₚ*, Israel J. Math. **5** (1967), 249–271.
* S. Ju. Rotfel'd, *The singular numbers of the sum of completely continuous operators*,
  Topics in Mathematical Physics **3** (1969), 73–78.
* J.-C. Bourin and M. Uchiyama, *A matrix subadditivity inequality for f(A + B) and f(A) + f(B)*,
  Linear Algebra Appl. **423** (2007), 512–518.
-/

public section

open Module (finrank)
open scoped InnerProductSpace

namespace LinearMap.IsPositive

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {A B : E →ₗ[𝕜] E} {n : ℕ}

/-- The column map `x ↦ (√A x, √B x)` into the `L²` product, whose source Gram operator is
`A + B`. -/
private noncomputable def sqrtColumn (hA : A.IsPositive) (hB : B.IsPositive) :
    E →ₗ[𝕜] WithLp 2 (E × E) :=
  (WithLp.linearEquiv 2 𝕜 (E × E)).symm.toLinearMap ∘ₗ hA.sqrt.prod hB.sqrt

private theorem sqrtColumn_apply (hA : A.IsPositive) (hB : B.IsPositive) (x : E) :
    sqrtColumn hA hB x = WithLp.toLp 2 (hA.sqrt x, hB.sqrt x) :=
  (rfl)

/-- The adjoint of the column map is the row map `(x, y) ↦ √A x + √B y`. -/
private theorem adjoint_sqrtColumn_toLp (hA : A.IsPositive) (hB : B.IsPositive) (x y : E) :
    adjoint (sqrtColumn hA hB) (WithLp.toLp 2 (x, y)) = hA.sqrt x + hB.sqrt y := by
  refine ext_inner_right 𝕜 fun z ↦ ?_
  rw [adjoint_inner_left, sqrtColumn_apply, WithLp.prod_inner_apply, inner_add_left,
    hA.sqrt_isSymmetric, hB.sqrt_isSymmetric]

/-- The source Gram operator of the column map is `A + B`. -/
private theorem adjoint_sqrtColumn_comp_sqrtColumn (hA : A.IsPositive) (hB : B.IsPositive) :
    adjoint (sqrtColumn hA hB) ∘ₗ sqrtColumn hA hB = A + B := by
  ext x
  rw [comp_apply, sqrtColumn_apply, adjoint_sqrtColumn_toLp, ← comp_apply, ← comp_apply,
    hA.sqrt_sq, hB.sqrt_sq, LinearMap.add_apply]

/-- The diagonal entries of the target Gram operator of the column map are the quadratic forms
of `A` and `B`. -/
private theorem re_inner_sqrtColumn_comp_adjoint_apply_self (hA : A.IsPositive)
    (hB : B.IsPositive) (x y : E) :
    RCLike.re ⟪(sqrtColumn hA hB ∘ₗ adjoint (sqrtColumn hA hB)) (WithLp.toLp 2 (x, y)),
      WithLp.toLp 2 (x, y)⟫_𝕜 = ‖hA.sqrt x + hB.sqrt y‖ ^ 2 := by
  rw [comp_apply, ← adjoint_inner_right, adjoint_sqrtColumn_toLp, inner_self_eq_norm_sq]

/-- **Superadditivity of convex spectral sums** (McCarthy; Bourin–Uchiyama). For positive
operators `A` and `B` on an `n`-dimensional inner product space and a function `φ` convex on
`[0, ∞)` with `φ 0 ≤ 0`, `tr φ(A) + tr φ(B) ≤ tr φ(A + B)`, written as sums over the eigenvalues.
For `φ(t) = tʳ` with `1 ≤ r` this is McCarthy's inequality `tr Aʳ + tr Bʳ ≤ tr (A + B)ʳ`. -/
theorem sum_map_eigenvalues_add_sum_map_eigenvalues_le_sum_map_eigenvalues_add
    (hA : A.IsPositive) (hB : B.IsPositive) (hn : finrank 𝕜 E = n) {φ : ℝ → ℝ}
    (hφ : ConvexOn ℝ (Set.Ici 0) φ) (hφ0 : φ 0 ≤ 0) :
    ∑ i, φ (hA.isSymmetric.eigenvalues hn i) + ∑ i, φ (hB.isSymmetric.eigenvalues hn i) ≤
      ∑ i, φ ((hA.add hB).isSymmetric.eigenvalues hn i) := by
  set V := sqrtColumn hA hB
  set e := (hA.isSymmetric.eigenvectorBasis hn).prod (hB.isSymmetric.eigenvectorBasis hn)
  have hV := V.isSymmetric_self_comp_adjoint
  -- Schur–Horn for `V V†` in the basis `(vᵢ, 0)`, `(0, wⱼ)`.
  have key := hV.sum_map_re_inner_apply_self_le_sum_map_eigenvalues rfl e hφ
    fun i ↦ V.isPositive_self_comp_adjoint.nonneg_eigenvalues rfl i
  -- The diagonal entries are `‖√A vᵢ‖² = αᵢ` and `‖√B wⱼ‖² = βⱼ`.
  have hdiag : ∀ i, RCLike.re ⟪(V ∘ₗ adjoint V) (e i), e i⟫_𝕜 =
      Sum.elim (hA.isSymmetric.eigenvalues hn) (hB.isSymmetric.eigenvalues hn) i := by
    rintro (i | j) <;>
      simp only [e, OrthonormalBasis.prod_apply, Sum.elim_inl, Sum.elim_inr, Function.comp_apply,
        inl_apply, inr_apply, V, re_inner_sqrtColumn_comp_adjoint_apply_self, map_zero, add_zero,
        zero_add, norm_sqrt_eigenvectorBasis_sq]
  simp only [hdiag, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr] at key
  refine key.trans ?_
  -- The eigenvalues of `V V†` are the squared singular values of `V`: those of `V† V = A + B`,
  -- then zeros.
  have hnm : n ≤ finrank 𝕜 (WithLp 2 (E × E)) := by
    rw [Module.finrank_eq_card_basis e.toBasis]
    simp
  rw [Finset.sum_congr rfl fun i _ ↦ by
      rw [← V.sq_singularValues_eq_eigenvalues_self_comp_adjoint rfl i.isLt],
    Fin.sum_univ_eq_sum_range (fun i ↦ φ (V.singularValues i ^ 2)),
    ← Finset.sum_range_add_sum_Ico _ hnm, ← Fin.sum_univ_eq_sum_range]
  have htail :
      ∑ i ∈ Finset.Ico n (finrank 𝕜 (WithLp 2 (E × E))), φ (V.singularValues i ^ 2) ≤ 0 :=
    Finset.sum_nonpos fun i hi ↦ by
      rw [V.singularValues_of_finrank_le (hn.trans_le (Finset.mem_Ico.mp hi).1)]
      simpa using hφ0
  refine (add_le_of_nonpos_right htail).trans_eq (Finset.sum_congr rfl fun i _ ↦ ?_)
  rw [V.sq_singularValues_fin hn,
    LinearMap.IsSymmetric.eigenvalues_congr (adjoint_sqrtColumn_comp_sqrtColumn hA hB)]

/-- **Subadditivity of concave spectral sums** (Rotfel'd). For positive operators `A` and `B` on
an `n`-dimensional inner product space and a function `φ` concave on `[0, ∞)` with `0 ≤ φ 0`,
`tr φ(A + B) ≤ tr φ(A) + tr φ(B)`, written as sums over the eigenvalues. For `φ(t) = tʳ` with
`0 ≤ r ≤ 1` this is McCarthy's inequality `tr (A + B)ʳ ≤ tr Aʳ + tr Bʳ`. -/
theorem sum_map_eigenvalues_add_le_sum_map_eigenvalues_add_sum_map_eigenvalues
    (hA : A.IsPositive) (hB : B.IsPositive) (hn : finrank 𝕜 E = n) {φ : ℝ → ℝ}
    (hφ : ConcaveOn ℝ (Set.Ici 0) φ) (hφ0 : 0 ≤ φ 0) :
    ∑ i, φ ((hA.add hB).isSymmetric.eigenvalues hn i) ≤
      ∑ i, φ (hA.isSymmetric.eigenvalues hn i) + ∑ i, φ (hB.isSymmetric.eigenvalues hn i) := by
  have h :=
    hA.sum_map_eigenvalues_add_sum_map_eigenvalues_le_sum_map_eigenvalues_add hB hn hφ.neg
    (by simpa using hφ0)
  simp only [Pi.neg_apply, Finset.sum_neg_distrib] at h
  linarith

end LinearMap.IsPositive
