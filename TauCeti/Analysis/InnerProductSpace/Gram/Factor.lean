/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Factoring a bounded operator through another one

Let `A : E →L[𝕜] G` and `T : E →L[𝕜] F` be bounded operators with a common source, where `G` is
a complete inner product space and `F` is a Banach space, and suppose `‖T x‖ ≤ C * ‖A x‖` for
every `x`. Then the rule `A x ↦ T x` is well defined and bounded on the range of `A`. It extends
by continuity to the closure `K` of that range, and by zero on `Kᗮ`. The result is the canonical
factor `T.factorThru A : G →L[𝕜] F`, satisfying `T.factorThru A ∘L A = T` and
`‖T.factorThru A‖ ≤ C`. It is the unique bounded operator `V` with `V ∘L A = T` that vanishes on
`(range A)ᗮ`. This is the elementary direction of Douglas's factorization lemma.

When `‖T x‖ = ‖A x‖` for every `x`, for instance when the Gram operators `A† A` and `T† T` agree,
the factor is isometric on `K`. It is then a contraction, and its adjoint carries `T` back to `A`:
`(T.factorThru A)† ∘L T = A`. Applied to a self-adjoint square root `A` of `T† T`, this is the
Gram-contraction factorization of `T`. Applied to the modulus `A = |T|`, the factor is the polar
partial isometry of `T`.

## Main declarations

* `ContinuousLinearMap.factorThru`: the canonical factor of `T` through `A`.
* `ContinuousLinearMap.factorThru_comp`: `T.factorThru A ∘L A = T` under a norm bound.
* `ContinuousLinearMap.eq_factorThru`: uniqueness of the factor vanishing on `(range A)ᗮ`.
* `ContinuousLinearMap.adjoint_factorThru_comp`: `(T.factorThru A)† ∘L T = A` when
  `‖T x‖ = ‖A x‖` for every `x`.
* `ContinuousLinearMap.adjoint_comp_self_eq_adjoint_comp_self_iff`: equal Gram operators are
  equivalent to equal pointwise norms.
* `ContinuousLinearMap.exists_contraction_of_gram_eq`: equal Gram operators `A† A = T† T` give a
  contraction `W` with contractive adjoint, `W ∘L A = T`, and `W† ∘L T = A`.

## References

* R. G. Douglas, *On majorization, factorization, and range inclusion of operators on Hilbert
  space*, Proc. Amer. Math. Soc. **17** (1966), 413–415.
-/

public section

noncomputable section

open scoped InnerProduct

namespace ContinuousLinearMap

section Factor

variable {𝕜 E F G : Type*} [RCLike 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]

/-- The operator `A`, with codomain restricted to the closure of its range. -/
private def toClosureRange (A : E →L[𝕜] G) : E →ₗ[𝕜] A.range.topologicalClosure :=
  (A : E →ₗ[𝕜] G).codRestrict _ fun x ↦ A.range.le_topologicalClosure ⟨x, rfl⟩

private theorem coe_toClosureRange_apply (A : E →L[𝕜] G) (x : E) :
    (toClosureRange A x : G) = A x :=
  rfl

private theorem denseRange_toClosureRange (A : E →L[𝕜] G) : DenseRange (toClosureRange A) := by
  have hdense := (denseRange_inclusion_iff (subset_closure : (A.range : Set G) ⊆ _)).2 le_rfl
  refine hdense.mono ?_
  rintro _ ⟨⟨_, x, rfl⟩, rfl⟩
  exact ⟨x, rfl⟩

variable [CompleteSpace G]

private theorem orthogonalProjectionOnto_apply_apply (A : E →L[𝕜] G) (x : E) :
    A.range.topologicalClosure.orthogonalProjectionOnto (A x) = toClosureRange A x :=
  Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (toClosureRange A x)

/-- The canonical factor of `T` through `A`. On the closure of the range of `A` it is the
continuous extension of the rule `A x ↦ T x`, and it vanishes on the orthogonal complement of
that range. It satisfies `T.factorThru A ∘L A = T` whenever `‖T x‖ ≤ C * ‖A x‖` for some `C`
and every `x` (`factorThru_comp`); without such a bound its value is unspecified. -/
def factorThru (T : E →L[𝕜] F) (A : E →L[𝕜] G) : G →L[𝕜] F :=
  (T : E →ₗ[𝕜] F).extendOfNorm (toClosureRange A) ∘L
    A.range.topologicalClosure.orthogonalProjectionOnto

variable {T : E →L[𝕜] F} {A : E →L[𝕜] G}

private theorem factorThru_apply_eq (y : G) :
    T.factorThru A y = (T : E →ₗ[𝕜] F).extendOfNorm (toClosureRange A)
      (A.range.topologicalClosure.orthogonalProjectionOnto y) :=
  rfl

/-- Under a norm bound, the factor sends `A x` to `T x`. -/
@[simp]
theorem factorThru_apply_apply (h : ∃ C, ∀ x, ‖T x‖ ≤ C * ‖A x‖) (x : E) :
    T.factorThru A (A x) = T x := by
  rw [factorThru_apply_eq, orthogonalProjectionOnto_apply_apply]
  exact LinearMap.extendOfNorm_eq (denseRange_toClosureRange A) h x

/-- Under a norm bound `‖T x‖ ≤ C * ‖A x‖`, the operator `T` factors through `A`. -/
theorem factorThru_comp (h : ∃ C, ∀ x, ‖T x‖ ≤ C * ‖A x‖) : T.factorThru A ∘L A = T := by
  ext x
  exact factorThru_apply_apply h x

/-- The factor vanishes on the orthogonal complement of the range of `A`. -/
@[simp]
theorem factorThru_apply_of_mem_orthogonal {y : G} (hy : y ∈ A.rangeᗮ) :
    T.factorThru A y = 0 := by
  rw [factorThru_apply_eq, Submodule.orthogonalProjectionOnto_eq_zero_iff.2
    (by rwa [Submodule.orthogonal_closure]), map_zero]

/-- A bound `‖T x‖ ≤ C * ‖A x‖` bounds the norm of the factor by `C`. -/
theorem norm_factorThru_le {C : ℝ} (hC : 0 ≤ C) (h : ∀ x, ‖T x‖ ≤ C * ‖A x‖) :
    ‖T.factorThru A‖ ≤ C := by
  calc ‖T.factorThru A‖
      ≤ ‖(T : E →ₗ[𝕜] F).extendOfNorm (toClosureRange A)‖ *
          ‖A.range.topologicalClosure.orthogonalProjectionOnto‖ := opNorm_comp_le _ _
    _ ≤ C * 1 := by
      gcongr
      · exact LinearMap.opNorm_extendOfNorm_le (denseRange_toClosureRange A) hC h
      · exact Submodule.orthogonalProjectionOnto_norm_le _
    _ = C := mul_one C

/-- A bounded operator `V` with `V ∘L A = T` that vanishes on the orthogonal complement of the
range of `A` is the canonical factor of `T` through `A`. -/
theorem eq_factorThru {V : G →L[𝕜] F} (hV : V ∘L A = T) (hV₀ : ∀ y ∈ A.rangeᗮ, V y = 0) :
    V = T.factorThru A := by
  have hbound : ∃ C, ∀ x, ‖T x‖ ≤ C * ‖A x‖ := ⟨‖V‖, fun x ↦ by
    simpa only [← hV, comp_apply] using V.le_opNorm (A x)⟩
  -- The two operators agree on the range of `A`, hence on its closure `K`, and both vanish
  -- on `Kᗮ = (range A)ᗮ`; these two subspaces span `G`.
  have hrange : Set.EqOn V (T.factorThru A) (A.range : Set G) := by
    rintro _ ⟨x, rfl⟩
    rw [coe_coe, factorThru_apply_apply hbound, ← hV, comp_apply]
  have hclosure := hrange.closure V.continuous (T.factorThru A).continuous
  ext y
  obtain ⟨u, hu, v, hv, rfl⟩ := A.range.topologicalClosure.exists_add_mem_mem_orthogonal y
  rw [Submodule.orthogonal_closure] at hv
  rw [map_add, map_add, hclosure (by rwa [← Submodule.topologicalClosure_coe]), hV₀ v hv,
    factorThru_apply_of_mem_orthogonal hv]

/-- If `‖T x‖ = ‖A x‖` for every `x`, the factor is isometric on the closure of the range
of `A`. -/
theorem norm_factorThru_apply (h : ∀ x, ‖T x‖ = ‖A x‖) {y : G}
    (hy : y ∈ A.range.topologicalClosure) : ‖T.factorThru A y‖ = ‖y‖ := by
  have hbound : ∃ C, ∀ x, ‖T x‖ ≤ C * ‖A x‖ := ⟨1, fun x ↦ by rw [one_mul, h x]⟩
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hy
  refine closure_minimal ?_ (isClosed_eq (T.factorThru A).continuous.norm continuous_norm) hy
  rintro _ ⟨x, rfl⟩
  rw [Set.mem_ofPred_eq, coe_coe, factorThru_apply_apply hbound, h x]

end Factor

section Adjoint

variable {𝕜 E F G : Type*} [RCLike 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
  {T : E →L[𝕜] F} {A : E →L[𝕜] G}

/-- If `‖T x‖ = ‖A x‖` for every `x`, the adjoint of the factor of `T` through `A` carries `T`
back to `A`. -/
theorem adjoint_factorThru_comp (h : ∀ x, ‖T x‖ = ‖A x‖) : (T.factorThru A)† ∘L T = A := by
  -- The extension of `A x ↦ T x` from the range of `A` to its closure is a linear isometry.
  let V := (T : E →ₗ[𝕜] F).extendOfIsometry (denseRange_toClosureRange A) h
  have hV (k) : (T : E →ₗ[𝕜] F).extendOfNorm (toClosureRange A) k = V k :=
    (LinearMap.extendOfIsometry_apply (T : E →ₗ[𝕜] F) (denseRange_toClosureRange A) h k).symm
  have hTx (x : E) : T x = V (toClosureRange A x) :=
    (LinearMap.extendOfIsometry_eq (T : E →ₗ[𝕜] F) (denseRange_toClosureRange A) h x).symm
  ext x
  refine ext_inner_right 𝕜 fun y ↦ ?_
  rw [comp_apply, adjoint_inner_left, factorThru_apply_eq, hV, hTx, LinearIsometry.inner_map_map,
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left, coe_toClosureRange_apply]

end Adjoint

section Gram

variable {𝕜 E F G : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]

/-- Two bounded operators with a common source have equal Gram operators exactly when they have
equal pointwise norms. The proof follows Mathlib's
`ContinuousLinearMap.isStarNormal_iff_norm_eq_adjoint`. -/
theorem adjoint_comp_self_eq_adjoint_comp_self_iff {T : E →L[𝕜] F} {A : E →L[𝕜] G} :
    A† ∘L A = T† ∘L T ↔ ∀ x, ‖A x‖ = ‖T x‖ := by
  have hsymm : ((A† ∘L A - T† ∘L T : E →L[𝕜] E) : E →ₗ[𝕜] E).IsSymmetric :=
    (isPositive_adjoint_comp_self A).isSymmetric.sub (isPositive_adjoint_comp_self T).isSymmetric
  rw [← sub_eq_zero, ← coe_inj, toLinearMap_zero, ← hsymm.inner_map_self_eq_zero]
  simp_rw [coe_coe, sub_apply, inner_sub_left, comp_apply, adjoint_inner_left,
    inner_self_eq_norm_sq_to_K, sub_eq_zero, ← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
  norm_cast

/-- **Gram-contraction factorization.** If `A† A = T† T`, then `T` factors as `W ∘L A` through
a contraction `W` with contractive adjoint, and `W†` carries `T` back to `A`. In particular this
applies to a self-adjoint `A : E →L[𝕜] E` with `A ∘L A = T† ∘L T`. -/
theorem exists_contraction_of_gram_eq {T : E →L[𝕜] F} {A : E →L[𝕜] G}
    (h : A† ∘L A = T† ∘L T) :
    ∃ W : G →L[𝕜] F, ‖W‖ ≤ 1 ∧ ‖W†‖ ≤ 1 ∧ W ∘L A = T ∧ W† ∘L T = A := by
  have hnorm (x : E) : ‖T x‖ = ‖A x‖ := (adjoint_comp_self_eq_adjoint_comp_self_iff.1 h x).symm
  have hle : ‖T.factorThru A‖ ≤ 1 :=
    norm_factorThru_le zero_le_one fun x ↦ by rw [one_mul, hnorm x]
  refine ⟨T.factorThru A, hle, by rwa [LinearIsometryEquiv.norm_map], ?_,
    adjoint_factorThru_comp hnorm⟩
  exact factorThru_comp ⟨1, fun x ↦ by rw [one_mul, hnorm x]⟩

end Gram

end ContinuousLinearMap
