/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Group.NullFamily
public import TauCeti.Analysis.Normed.Operator.Surjective
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Matrix

/-!
# Triangular perturbations of the identity of `C₀(ℕ, E)`

Let `R` be a seminormed ring and `E` a complete ultrametric normed `R`-module with contractive
action. A matrix `A` over `R` with null columns and bounded entries defines a continuous linear
map `A.toZeroAtInftySMulCLM S` on the model space `C₀(ℕ, E)`, acting by `(A x) i = ∑ j, A i j • x j`
(output index first). This file shows that `A` is an *isometric automorphism* as soon as

* every entry has norm at most one,
* every diagonal entry is a unit `d` of `R` acting isometrically, `‖d • e‖ = ‖e‖` for all `e`, and
* the entries strictly below the diagonal have norm at most a constant `c < 1`.

The isometry needs only that each entry below the diagonal has norm `< 1`, and holds for an
arbitrary linearly ordered discrete index type: at the last coordinate where `x` attains its norm,
the diagonal term of `(A x) i` strictly dominates all the others. For surjectivity, write `A` as
its upper triangular part `U` plus a strictly lower triangular part of entries of norm at most
`c`. The columns of `U` are finite, so back substitution solves `U x = y` for every finitely
supported `y`; since `U` is an isometry its range is closed, hence `U` is onto. Then `U⁻¹ A` is
within `max c 0 < 1` of the identity, so it is onto by the contraction principle
(`TauCeti.surjective_of_norm_sub_apply_le`).

No torsion-freeness of `E` is needed. Under a contractive action, a unit `d` with `‖d‖ ≤ 1` and
`‖d⁻¹‖ ≤ 1`, such as a unit of `ℤ_p`, acts isometrically on every such module.
The map `Matrix.toZeroAtInftyCLM` on `C₀(ℕ, R)` itself, which multiplies by the entries on the
right, is the action of the matrix over the opposite ring `Rᵐᵒᵖ`
(`Matrix.toZeroAtInftySMulCLM_map_op`), so the same results hold for it, with the diagonal
condition `‖r * d‖ = ‖r‖` for all `r`.

A matrix all of whose columns are finite satisfies the null-column hypothesis through
`tendsto_nhds_of_eventually_eq`; the bidiagonal matrix `1 + ϖ S`, with `S` the shift and
`‖ϖ‖ < 1`, is an example. The null-column hypothesis does not follow from the bounds on the
entries: the matrix with constant entry `ϖ ≠ 0` below the diagonal has no null column.

## Main definitions

* `Matrix.toZeroAtInftySMulLinearIsometryEquiv`: the isometric automorphism of `C₀(ℕ, E)` defined
  by such a matrix.
* `Matrix.toZeroAtInftyLinearIsometryEquiv`: the isometric automorphism of `C₀(ℕ, R)` defined by
  such a matrix acting by right multiplication.

## Main results

* `Matrix.norm_toZeroAtInftySMulCLM_apply`, `Matrix.isometry_toZeroAtInftySMulCLM`: the map defined
  by a matrix with entries of norm at most one, isometrically acting diagonal and entries of norm
  `< 1` below the diagonal preserves norms.
* `Matrix.surjective_toZeroAtInftySMulCLM`: on `C₀(ℕ, E)` it is onto when moreover the diagonal
  entries are units and the entries below the diagonal are bounded by some `c < 1`.
* `Matrix.norm_toZeroAtInftyCLM_apply`, `Matrix.isometry_toZeroAtInftyCLM`,
  `Matrix.surjective_toZeroAtInftyCLM`: the same results for `C₀(ℕ, R)`.

## References

* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §I.4 (Amice's theorem on
  the basis of locally analytic functions).
* P. Schneider, *Nonarchimedean Functional Analysis*, Springer, 2002, §10.
-/

public section

open Filter Topology ZeroAtInftyContinuousMap
open scoped ZeroAtInfty

namespace Matrix

section Isometry

variable {I R E : Type*} [TopologicalSpace I] [DiscreteTopology I] [LinearOrder I]
  [SeminormedRing R] [NormedAddCommGroup E] [Module R E] [IsBoundedSMul R E]
  [IsUltrametricDist E] [CompleteSpace E]
  (S : Type*) [Semiring S] [Module S E] [ContinuousConstSMul S E] [SMulCommClass R S E]

/-- **Triangular isometries.** Let `A` be a matrix with null columns over a seminormed ring `R`
whose entries have norm at most one, whose diagonal entries `d` act isometrically on a complete
ultrametric normed `R`-module `E`, and whose entries strictly below the diagonal have norm less
than one. Then the map `C₀(I, E) → C₀(I, E)` defined by `A` preserves norms. -/
theorem norm_toZeroAtInftySMulCLM_apply (A : Matrix I I R)
    (hcol : ∀ j, Tendsto (fun i ↦ A i j) cofinite (𝓝 0)) (hle : ∀ i j, ‖A i j‖ ≤ 1)
    (hdiag : ∀ i (e : E), ‖A i i • e‖ = ‖e‖) (hlow : ∀ i j, j < i → ‖A i j‖ < 1)
    (x : C₀(I, E)) : ‖A.toZeroAtInftySMulCLM S hcol ⟨1, hle⟩ x‖ = ‖x‖ := by
  set T := A.toZeroAtInftySMulCLM (E := E) S hcol ⟨1, hle⟩
  refine le_antisymm ?_ ?_
  · simpa using A.norm_toZeroAtInftySMulCLM_apply_le S hcol ⟨1, hle⟩ zero_le_one hle x
  rcases (norm_nonneg x).eq_or_lt with hx | hx
  · exact hx ▸ norm_nonneg _
  -- Choose the last coordinate `i₀` at which `x` attains its norm.
  have hfin : {i | ‖x i‖ = ‖x‖}.Finite := by
    refine (eventually_cofinite.1 ?_).subset fun i (hi : ‖x i‖ = ‖x‖) ↦ hi.not_lt
    exact (tendsto_norm_zero.comp x.tendsto_cofinite).eventually_lt_const hx
  have hne : {i | ‖x i‖ = ‖x‖}.Nonempty := by
    have : Nonempty I := by
      by_contra h
      exact hx.ne' (le_antisymm ((norm_le le_rfl).2 fun i ↦ (h ⟨i⟩).elim) (norm_nonneg x))
    exact x.exists_norm_coe_eq_norm
  obtain ⟨i₀, hi₀ : ‖x i₀‖ = ‖x‖, hmax⟩ := Set.exists_max_image _ id hfin hne
  -- In the sum `(T x) i₀ = ∑ j, A i₀ j • x j`, the diagonal term strictly dominates.
  have hdom : ‖T x i₀‖ = ‖A i₀ i₀ • x i₀‖ := by
    have hsum := A.hasSum_toZeroAtInftySMulCLM_apply S hcol ⟨1, hle⟩ x i₀
    refine hsum.norm_eq_of_forall_norm_lt i₀ fun j hj ↦ ?_
    rw [hdiag, hi₀]
    refine (norm_smul_le _ _).trans_lt ?_
    rcases hj.lt_or_gt with hj | hj
    · exact (mul_le_mul_of_nonneg_left (x.norm_coe_le_norm j) (norm_nonneg _)).trans_lt
        (mul_lt_of_lt_one_left hx (hlow i₀ j hj))
    · have hxj : ‖x j‖ < ‖x‖ := (x.norm_coe_le_norm j).lt_of_ne fun h ↦ (hmax j h).not_gt hj
      exact (mul_le_of_le_one_left (norm_nonneg _) (hle i₀ j)).trans_lt hxj
  calc ‖x‖ = ‖T x i₀‖ := by rw [hdom, hdiag, hi₀]
    _ ≤ ‖T x‖ := (T x).norm_coe_le_norm i₀

/-- **Triangular isometries.** The map defined by a matrix as in
`norm_toZeroAtInftySMulCLM_apply` is an isometry. -/
theorem isometry_toZeroAtInftySMulCLM (A : Matrix I I R)
    (hcol : ∀ j, Tendsto (fun i ↦ A i j) cofinite (𝓝 0)) (hle : ∀ i j, ‖A i j‖ ≤ 1)
    (hdiag : ∀ i (e : E), ‖A i i • e‖ = ‖e‖) (hlow : ∀ i j, j < i → ‖A i j‖ < 1) :
    Isometry (A.toZeroAtInftySMulCLM (E := E) S hcol ⟨1, hle⟩) :=
  AddMonoidHomClass.isometry_of_norm _ (A.norm_toZeroAtInftySMulCLM_apply S hcol hle hdiag hlow)

end Isometry

section Surjective

variable {R E : Type*} [SeminormedRing R] [NormedAddCommGroup E] [Module R E] [IsBoundedSMul R E]
  [IsUltrametricDist E] [CompleteSpace E]
  (S : Type*) [Semiring S] [Module S E] [ContinuousConstSMul S E] [SMulCommClass R S E]

/-- Back substitution: for an upper triangular matrix with unit diagonal, every vector supported
on `{0, …, n - 1}` is in the range of the map defined by the matrix. -/
private theorem mem_range_toZeroAtInftySMulCLM_of_upper (A : Matrix ℕ ℕ R)
    (hcol : ∀ j, Tendsto (fun i ↦ A i j) cofinite (𝓝 0)) (hle : ∀ i j, ‖A i j‖ ≤ 1)
    (hunit : ∀ i, IsUnit (A i i)) (hupper : ∀ i j, j < i → A i j = 0) (n : ℕ) (y : C₀(ℕ, E))
    (hy : ∀ i, n ≤ i → y i = 0) :
    y ∈ Set.range (A.toZeroAtInftySMulCLM (E := E) S hcol ⟨1, hle⟩) := by
  induction n generalizing y with
  | zero => exact ⟨0, by ext i; simp [hy i (Nat.zero_le i)]⟩
  | succ n ih =>
    -- Clear the coordinate `n` of `y` with a multiple of the `n`-th column, which is supported
    -- on `{0, …, n}`.
    set e := (↑(hunit n).unit⁻¹ : R) • y n
    obtain ⟨x, hx⟩ := ih (y - A.toZeroAtInftySMulCLM S hcol ⟨1, hle⟩ (.single n e)) fun i hi ↦ by
      rcases hi.eq_or_lt with rfl | hi
      · simp [e, smul_smul]
      · simp [hy i hi, hupper i n hi]
    exact ⟨x + .single n e, by rw [map_add, hx, sub_add_cancel]⟩

/-- An upper triangular matrix with entries of norm at most one and isometrically acting units on
the diagonal defines a surjection of `C₀(ℕ, E)`. -/
private theorem surjective_toZeroAtInftySMulCLM_of_upper (A : Matrix ℕ ℕ R)
    (hcol : ∀ j, Tendsto (fun i ↦ A i j) cofinite (𝓝 0)) (hle : ∀ i j, ‖A i j‖ ≤ 1)
    (hunit : ∀ i, IsUnit (A i i)) (hdiag : ∀ i (e : E), ‖A i i • e‖ = ‖e‖)
    (hupper : ∀ i j, j < i → A i j = 0) :
    Function.Surjective (A.toZeroAtInftySMulCLM (E := E) S hcol ⟨1, hle⟩) := by
  -- The range is closed, being the image of an isometry, and contains the dense subspace of
  -- finitely supported vectors.
  have hclosed : IsClosed (Set.range (A.toZeroAtInftySMulCLM (E := E) S hcol ⟨1, hle⟩)) :=
    (A.isometry_toZeroAtInftySMulCLM S hcol hle hdiag fun i j h ↦ by
      simp [hupper i j h]).isClosedEmbedding.isClosed_range
  have hsub : {f : C₀(ℕ, E) | (Function.support f).Finite} ⊆
      Set.range (A.toZeroAtInftySMulCLM (E := E) S hcol ⟨1, hle⟩) := fun f hf ↦ by
    obtain ⟨N, hN⟩ := hf.bddAbove
    refine mem_range_toZeroAtInftySMulCLM_of_upper S A hcol hle hunit hupper (N + 1) f
      fun i hi ↦ ?_
    exact Function.notMem_support.1 fun h ↦ by have := hN h; omega
  rw [← Set.range_eq_univ, ← hclosed.closure_eq]
  exact (Dense.mono hsub dense_setOf_finite_support).closure_eq

/-- **Triangular perturbations are onto.** Let `A` be a matrix with null columns over a
seminormed ring `R`, whose entries have norm at most one, whose diagonal entries are units acting
isometrically on a complete ultrametric normed `R`-module `E`, and whose entries strictly below
the diagonal have norm at most `c < 1`. Then the map `C₀(ℕ, E) → C₀(ℕ, E)` defined by `A` is
surjective. -/
theorem surjective_toZeroAtInftySMulCLM (A : Matrix ℕ ℕ R)
    (hcol : ∀ j, Tendsto (fun i ↦ A i j) cofinite (𝓝 0)) (hle : ∀ i j, ‖A i j‖ ≤ 1)
    (hunit : ∀ i, IsUnit (A i i)) (hdiag : ∀ i (e : E), ‖A i i • e‖ = ‖e‖) {c : ℝ} (hc : c < 1)
    (hlow : ∀ i j, j < i → ‖A i j‖ ≤ c) :
    Function.Surjective (A.toZeroAtInftySMulCLM (E := E) S hcol ⟨1, hle⟩) := by
  set T := A.toZeroAtInftySMulCLM (E := E) S hcol ⟨1, hle⟩
  -- The upper triangular part `U` of `A` defines a bijective isometry.
  set U : Matrix ℕ ℕ R := fun i j ↦ if j < i then 0 else A i j
  have hUcol (j : ℕ) : Tendsto (fun i ↦ U i j) cofinite (𝓝 0) := by
    refine tendsto_nhds_of_eventually_eq ?_
    rw [Nat.cofinite_eq_atTop]
    exact (eventually_gt_atTop j).mono fun i hi ↦ by simp [U, hi]
  have hUle (i j : ℕ) : ‖U i j‖ ≤ 1 := by
    simp only [U]
    split_ifs <;> simp [hle]
  have hUupper (i j : ℕ) (h : j < i) : U i j = 0 := by simp [U, h]
  have hUdiag (i : ℕ) : U i i = A i i := by simp [U]
  set TU := U.toZeroAtInftySMulCLM (E := E) S hUcol ⟨1, hUle⟩
  have hTU_norm : ∀ x, ‖TU x‖ = ‖x‖ :=
    U.norm_toZeroAtInftySMulCLM_apply S hUcol hUle (by simpa [hUdiag] using hdiag)
      fun i j h ↦ by simp [hUupper i j h]
  let V : C₀(ℕ, E) ≃ₗ[S] C₀(ℕ, E) := .ofBijective TU.toLinearMap
    ⟨(AddMonoidHomClass.isometry_of_norm TU hTU_norm).injective,
      surjective_toZeroAtInftySMulCLM_of_upper S U hUcol hUle (by simpa [hUdiag] using hunit)
        (by simpa [hUdiag] using hdiag) hUupper⟩
  have hV (y : C₀(ℕ, E)) : ‖V.symm y‖ = ‖y‖ := by
    rw [← hTU_norm]
    exact congrArg norm (V.apply_symm_apply y)
  -- `A - U` is strictly lower triangular, with entries of norm at most `max c 0`.
  have hD (i j : ℕ) : ‖(A - U) i j‖ ≤ max c 0 := by
    rw [Matrix.sub_apply]
    by_cases h : j < i
    · simpa [U, h] using (hlow i j h).trans (le_max_left c 0)
    · simp [U, h]
  have hdiff (x : C₀(ℕ, E)) : ‖T x - TU x‖ ≤ max c 0 * ‖x‖ := by
    rw [← toZeroAtInftySMulCLM_sub_apply S A U
      (fun j ↦ by simpa using (hcol j).sub (hUcol j)) ⟨_, hD⟩ hcol ⟨1, hle⟩ hUcol ⟨1, hUle⟩]
    exact (A - U).norm_toZeroAtInftySMulCLM_apply_le S _ _ (le_max_right c 0) hD x
  -- So `U⁻¹ A` is within `max c 0 < 1` of the identity, hence onto.
  have hv : Function.Surjective (V.symm.toLinearMap ∘ₗ T.toLinearMap) := by
    refine TauCeti.surjective_of_norm_sub_apply_le (max_lt hc zero_lt_one) fun x ↦ ?_
    have hx : V.symm (TU x) = x := V.symm_apply_apply x
    calc ‖x - V.symm (T x)‖ = ‖V.symm (TU x - T x)‖ := by rw [map_sub, hx]
      _ = ‖T x - TU x‖ := by rw [hV, norm_sub_rev]
      _ ≤ max c 0 * ‖x‖ := hdiff x
  intro y
  obtain ⟨x, hx⟩ := hv (V.symm y)
  exact ⟨x, V.symm.injective hx⟩

/-- The isometric automorphism of `C₀(ℕ, E)` defined by a matrix with null columns, entries of
norm at most one, isometrically acting units on the diagonal and entries of norm at most `c < 1`
below the diagonal. -/
noncomputable def toZeroAtInftySMulLinearIsometryEquiv (A : Matrix ℕ ℕ R)
    (hcol : ∀ j, Tendsto (fun i ↦ A i j) cofinite (𝓝 0)) (hle : ∀ i j, ‖A i j‖ ≤ 1)
    (hunit : ∀ i, IsUnit (A i i)) (hdiag : ∀ i (e : E), ‖A i i • e‖ = ‖e‖) {c : ℝ} (hc : c < 1)
    (hlow : ∀ i j, j < i → ‖A i j‖ ≤ c) : C₀(ℕ, E) ≃ₗᵢ[S] C₀(ℕ, E) :=
  .ofSurjective ⟨(A.toZeroAtInftySMulCLM S hcol ⟨1, hle⟩).toLinearMap,
      A.norm_toZeroAtInftySMulCLM_apply S hcol hle hdiag fun i j h ↦ (hlow i j h).trans_lt hc⟩
    (A.surjective_toZeroAtInftySMulCLM S hcol hle hunit hdiag hc hlow)

/-- The automorphism `toZeroAtInftySMulLinearIsometryEquiv` is the map defined by the matrix. -/
@[simp]
theorem toZeroAtInftySMulLinearIsometryEquiv_apply (A : Matrix ℕ ℕ R)
    (hcol : ∀ j, Tendsto (fun i ↦ A i j) cofinite (𝓝 0)) (hle : ∀ i j, ‖A i j‖ ≤ 1)
    (hunit : ∀ i, IsUnit (A i i)) (hdiag : ∀ i (e : E), ‖A i i • e‖ = ‖e‖) {c : ℝ} (hc : c < 1)
    (hlow : ∀ i j, j < i → ‖A i j‖ ≤ c) (x : C₀(ℕ, E)) :
    A.toZeroAtInftySMulLinearIsometryEquiv S hcol hle hunit hdiag hc hlow x =
      A.toZeroAtInftySMulCLM S hcol ⟨1, hle⟩ x :=
  (rfl)

end Surjective

/-! ### Right multiplication on `C₀(ℕ, R)` -/

section Ring

variable {I R : Type*} [TopologicalSpace I] [DiscreteTopology I]
  [NormedRing R] [IsUltrametricDist R] [CompleteSpace R]

omit [TopologicalSpace I] [DiscreteTopology I] [IsUltrametricDist R] [CompleteSpace R] in
private theorem tendsto_map_op {A : Matrix I I R}
    (hcol : ∀ j, Tendsto (fun i ↦ A i j) cofinite (𝓝 0)) (j : I) :
    Tendsto (fun i ↦ A.map MulOpposite.op i j) cofinite (𝓝 0) := by
  simpa [Function.comp_def] using (MulOpposite.continuous_op.tendsto 0).comp (hcol j)

/-- **Triangular isometries.** Let `A` be a matrix with null columns over a complete
ultrametric normed ring whose entries have norm at most one, whose diagonal entries `d` satisfy
`‖r * d‖ = ‖r‖`, and whose entries strictly below the diagonal have norm less than one. Then the
map `C₀(I, R) → C₀(I, R)` defined by `A` preserves norms. -/
theorem norm_toZeroAtInftyCLM_apply [LinearOrder I] (A : Matrix I I R)
    (hcol : ∀ j, Tendsto (fun i ↦ A i j) cofinite (𝓝 0)) (hle : ∀ i j, ‖A i j‖ ≤ 1)
    (hdiag : ∀ i (r : R), ‖r * A i i‖ = ‖r‖) (hlow : ∀ i j, j < i → ‖A i j‖ < 1)
    (x : C₀(I, R)) : ‖A.toZeroAtInftyCLM hcol ⟨1, hle⟩ x‖ = ‖x‖ := by
  have hle' (i j : I) : ‖A.map MulOpposite.op i j‖ ≤ 1 := by
    simpa [MulOpposite.norm_op] using hle i j
  rw [← A.toZeroAtInftySMulCLM_map_op hcol ⟨1, hle⟩ (tendsto_map_op hcol) ⟨1, hle'⟩]
  exact (A.map MulOpposite.op).norm_toZeroAtInftySMulCLM_apply R (tendsto_map_op hcol) hle'
    (by simpa using hdiag) (by simpa [MulOpposite.norm_op] using hlow) x

/-- **Triangular isometries.** The map defined by a matrix as in `norm_toZeroAtInftyCLM_apply` is
an isometry. -/
theorem isometry_toZeroAtInftyCLM [LinearOrder I] (A : Matrix I I R)
    (hcol : ∀ j, Tendsto (fun i ↦ A i j) cofinite (𝓝 0)) (hle : ∀ i j, ‖A i j‖ ≤ 1)
    (hdiag : ∀ i (r : R), ‖r * A i i‖ = ‖r‖) (hlow : ∀ i j, j < i → ‖A i j‖ < 1) :
    Isometry (A.toZeroAtInftyCLM hcol ⟨1, hle⟩) :=
  AddMonoidHomClass.isometry_of_norm _ (A.norm_toZeroAtInftyCLM_apply hcol hle hdiag hlow)

/-- **Triangular perturbations are onto.** Let `A` be a matrix with null columns over a complete
ultrametric normed ring, whose entries have norm at most one, whose diagonal entries are
units `d` with `‖r * d‖ = ‖r‖`, and whose entries strictly below the diagonal have norm at most
`c < 1`. Then the map `C₀(ℕ, R) → C₀(ℕ, R)` defined by `A` is surjective. -/
theorem surjective_toZeroAtInftyCLM (A : Matrix ℕ ℕ R)
    (hcol : ∀ j, Tendsto (fun i ↦ A i j) cofinite (𝓝 0)) (hle : ∀ i j, ‖A i j‖ ≤ 1)
    (hunit : ∀ i, IsUnit (A i i)) (hdiag : ∀ i (r : R), ‖r * A i i‖ = ‖r‖) {c : ℝ} (hc : c < 1)
    (hlow : ∀ i j, j < i → ‖A i j‖ ≤ c) :
    Function.Surjective (A.toZeroAtInftyCLM hcol ⟨1, hle⟩) := by
  have hle' (i j : ℕ) : ‖A.map MulOpposite.op i j‖ ≤ 1 := by
    simpa [MulOpposite.norm_op] using hle i j
  rw [← A.toZeroAtInftySMulCLM_map_op hcol ⟨1, hle⟩ (tendsto_map_op hcol) ⟨1, hle'⟩]
  exact (A.map MulOpposite.op).surjective_toZeroAtInftySMulCLM R (tendsto_map_op hcol) hle'
    (by simpa using hunit) (by simpa using hdiag) hc (by simpa [MulOpposite.norm_op] using hlow)

/-- The isometric automorphism of `C₀(ℕ, R)` defined by a matrix with null columns, entries of
norm at most one, units `d` with `‖r * d‖ = ‖r‖` on the diagonal and entries of norm at most
`c < 1` below the diagonal. -/
noncomputable def toZeroAtInftyLinearIsometryEquiv (A : Matrix ℕ ℕ R)
    (hcol : ∀ j, Tendsto (fun i ↦ A i j) cofinite (𝓝 0)) (hle : ∀ i j, ‖A i j‖ ≤ 1)
    (hunit : ∀ i, IsUnit (A i i)) (hdiag : ∀ i (r : R), ‖r * A i i‖ = ‖r‖) {c : ℝ} (hc : c < 1)
    (hlow : ∀ i j, j < i → ‖A i j‖ ≤ c) : C₀(ℕ, R) ≃ₗᵢ[R] C₀(ℕ, R) :=
  .ofSurjective ⟨(A.toZeroAtInftyCLM hcol ⟨1, hle⟩).toLinearMap,
      A.norm_toZeroAtInftyCLM_apply hcol hle hdiag fun i j h ↦ (hlow i j h).trans_lt hc⟩
    (A.surjective_toZeroAtInftyCLM hcol hle hunit hdiag hc hlow)

/-- The automorphism `toZeroAtInftyLinearIsometryEquiv` is the map defined by the matrix. -/
@[simp]
theorem toZeroAtInftyLinearIsometryEquiv_apply (A : Matrix ℕ ℕ R)
    (hcol : ∀ j, Tendsto (fun i ↦ A i j) cofinite (𝓝 0)) (hle : ∀ i j, ‖A i j‖ ≤ 1)
    (hunit : ∀ i, IsUnit (A i i)) (hdiag : ∀ i (r : R), ‖r * A i i‖ = ‖r‖) {c : ℝ} (hc : c < 1)
    (hlow : ∀ i j, j < i → ‖A i j‖ ≤ c) (x : C₀(ℕ, R)) :
    A.toZeroAtInftyLinearIsometryEquiv hcol hle hunit hdiag hc hlow x =
      A.toZeroAtInftyCLM hcol ⟨1, hle⟩ x :=
  (rfl)

end Ring

section Examples

variable {R : Type*} [NormedRing R] [NormOneClass R] [IsUltrametricDist R] [CompleteSpace R]

/-- The bidiagonal matrix `1 + ϖ S`, with `S` the shift and `‖ϖ‖ < 1`, has finite columns and
defines an isometric automorphism of `C₀(ℕ, E)` for every complete ultrametric normed `R`-module
`E` with contractive action. -/
example {E : Type*} [NormedAddCommGroup E] [Module R E] [IsBoundedSMul R E] [IsUltrametricDist E]
    [CompleteSpace E] {ϖ : R} (hϖ : ‖ϖ‖ < 1) :
    let A : Matrix ℕ ℕ R := fun i j ↦ if i = j then 1 else if i = j + 1 then ϖ else 0
    ∃ (hcol : ∀ j, Tendsto (fun i ↦ A i j) cofinite (𝓝 0)) (hle : ∀ i j, ‖A i j‖ ≤ 1),
      Isometry (A.toZeroAtInftySMulCLM (E := E) ℕ hcol ⟨1, hle⟩) ∧
        Function.Surjective (A.toZeroAtInftySMulCLM (E := E) ℕ hcol ⟨1, hle⟩) := by
  intro A
  have hcol (j : ℕ) : Tendsto (fun i ↦ A i j) cofinite (𝓝 0) := by
    refine tendsto_nhds_of_eventually_eq ?_
    rw [Nat.cofinite_eq_atTop]
    refine (eventually_gt_atTop (j + 1)).mono fun i hi ↦ ?_
    have hij : i ≠ j := by omega
    simp [A, hi.ne', hij]
  have hle (i j : ℕ) : ‖A i j‖ ≤ 1 := by
    simp only [A]
    split_ifs <;> simp [hϖ.le]
  have hdiag (i : ℕ) (e : E) : ‖A i i • e‖ = ‖e‖ := by simp [A]
  have hlow (i j : ℕ) (h : j < i) : ‖A i j‖ ≤ ‖ϖ‖ := by
    simp only [A, h.ne', ↓reduceIte]
    split_ifs <;> simp
  exact ⟨hcol, hle,
    A.isometry_toZeroAtInftySMulCLM ℕ hcol hle hdiag fun i j h ↦ (hlow i j h).trans_lt hϖ,
    A.surjective_toZeroAtInftySMulCLM ℕ hcol hle (fun i ↦ by simp [A]) hdiag hϖ hlow⟩

/-- A matrix with the constant entry `ϖ ≠ 0` everywhere below the diagonal has no null column, so
it does not define a map of `C₀(ℕ, R)`. -/
example {ϖ : R} (hϖ : ϖ ≠ 0) (j : ℕ) :
    ¬Tendsto (fun i ↦ if j < i then ϖ else 0) cofinite (𝓝 0) := by
  intro h
  refine hϖ (tendsto_nhds_unique (tendsto_nhds_of_eventually_eq ?_) h)
  rw [Nat.cofinite_eq_atTop]
  exact (eventually_gt_atTop j).mono fun i hi ↦ by simp [hi]

end Examples

end Matrix
