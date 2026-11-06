/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.Adjoint
public import TauCeti.Analysis.Fredholm.CompactPerturbation
public import TauCeti.Analysis.InnerProductSpace.Variational.Fredholm

/-!
# The compatibility condition for Gårding forms

Let `B` be a bounded bilinear form on a real Hilbert space `V`, and let `J : V → H` be a compact
continuous linear map to a real inner-product space. Suppose `B` satisfies **Gårding's
inequality**

`C₀ ‖w‖² ≤ B(w, w) + β ‖J w‖²` for every `w`, with `C₀ > 0`.

The form need not be coercive and need not be symmetric. This file proves that the variational
problem `B(u, ·) = ℓ` is solvable for a continuous linear functional `ℓ` exactly when `ℓ`
vanishes on the **adjoint kernel** `{w | ∀ v, B(v, w) = 0}`
(`IsCompactOperator.exists_forall_apply_eq_iff_of_garding`). The kernel `{u | ∀ v, B(u, v) = 0}`
and the adjoint kernel are finite dimensional of the same dimension
(`IsCompactOperator.finrank_ker_flip_eq_finrank_ker_of_garding`), so if the homogeneous problem
has only the trivial solution then every problem `B(u, ·) = ℓ` has exactly one solution
(`IsCompactOperator.existsUnique_forall_apply_eq_of_garding`), although `B` need not be
coercive.

For elliptic boundary-value problems `V = H¹₀(Ω)`, `H = L²(Ω)`, `J` is the compact Rellich
inclusion, and this is the Fredholm alternative with its compatibility condition.

## The argument

By Gårding's inequality the shifted form `B_β = B + β ⟪J ·, J ·⟫` is coercive. Let `T` be the
operator representing `B` by the Fréchet–Riesz theorem, `⟪T u, v⟫ = B(u, v)`
(`InnerProductSpace.continuousLinearMapOfBilin`), and let `E` be the Lax–Milgram equivalence of
`B_β`. Then `T = E ∘ (1 - β K)`, where `K` is the compact operator representing
`⟪J ·, J ·⟫` relative to `B_β` (`IsCoercive.formPerturbationOperator`). By the Riesz–Schauder
theorem `1 - β K` is Fredholm of index zero, hence so is `T`. In particular `T` has closed range,
and a closed subspace of a Hilbert space is the orthogonal complement of its orthogonal
complement. The orthogonal complement of the range of `T` is exactly the adjoint kernel of `B`,
which gives the compatibility condition. The adjoint of `T` represents the transposed form
`B.flip`, and index zero says that the kernels of `T` and of its adjoint have the same dimension.

## Main declarations

* `InnerProductSpace.ker_continuousLinearMapOfBilin`: the Fréchet–Riesz operator of a form has the
  kernel of the form.
* `InnerProductSpace.adjoint_continuousLinearMapOfBilin`: its adjoint represents the transposed
  form.
* `IsCompactOperator.isFredholm_continuousLinearMapOfBilin_of_garding` and
  `IsCompactOperator.index_continuousLinearMapOfBilin_of_garding`: the operator of a Gårding form
  is Fredholm of index zero.
* `IsCompactOperator.exists_forall_apply_eq_iff_of_garding`: the compatibility condition.
* `IsCompactOperator.finiteDimensional_ker_of_garding` and
  `IsCompactOperator.finrank_ker_flip_eq_finrank_ker_of_garding`: the kernel and the adjoint
  kernel are finite dimensional of equal dimension.
* `IsCompactOperator.existsUnique_forall_apply_eq_of_garding`: unique solvability when the
  kernel is trivial.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Section 6.2.3, Theorem 4.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 5.3 and Theorem 8.6.
-/

public section

noncomputable section

open Module
open scoped InnerProductSpace

namespace InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- The Fréchet–Riesz operator of a bounded sesquilinear form has the same kernel as the form:
`u` lies in it exactly when `B(u, v) = 0` for every `v`. -/
@[simp]
theorem ker_continuousLinearMapOfBilin (B : E →L⋆[𝕜] E →L[𝕜] 𝕜) :
    (continuousLinearMapOfBilin B).ker = B.ker := by
  ext u
  simp [continuousLinearMapOfBilin]

/-- The adjoint of the Fréchet–Riesz operator of a real bilinear form represents the transposed
form. -/
@[simp]
theorem adjoint_continuousLinearMapOfBilin {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [CompleteSpace V] (B : V →L[ℝ] V →L[ℝ] ℝ) :
    ContinuousLinearMap.adjoint (continuousLinearMapOfBilin B) =
      continuousLinearMapOfBilin B.flip := by
  refine ((ContinuousLinearMap.eq_adjoint_iff _ _).mpr fun w v => ?_).symm
  rw [continuousLinearMapOfBilin_apply, real_inner_comm, continuousLinearMapOfBilin_apply,
    ContinuousLinearMap.flip_apply]

end InnerProductSpace

namespace IsCompactOperator

open InnerProductSpace

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]
  {B : V →L[ℝ] V →L[ℝ] ℝ} {J : V →L[ℝ] H} {C₀ β : ℝ}

omit [CompleteSpace V] in
/-- Gårding's inequality says exactly that the shift of `B` by `β ⟪J ·, J ·⟫` is coercive. Over
`ℝ` the conjugate-linear first slot of `ContinuousLinearMap.toSesqForm` is linear, which is what
the type ascription records. -/
private theorem isCoercive_add_smul_of_garding (hC₀ : 0 < C₀)
    (hB : ∀ w, C₀ * ‖w‖ ^ 2 ≤ B w w + β * ‖J w‖ ^ 2) :
    IsCoercive (B + β • ((ContinuousLinearMap.toSesqForm J).comp J : V →L[ℝ] V →L[ℝ] ℝ)) := by
  refine ⟨C₀, hC₀, fun w => ?_⟩
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSesqForm_apply_coe,
    innerSL_apply_apply, smul_eq_mul, real_inner_self_eq_norm_sq]
  nlinarith [hB w]

/-- The Fréchet–Riesz operator of a Gårding form factors as the Lax–Milgram equivalence of the
shifted coercive form after a compact perturbation of the identity. -/
private theorem continuousLinearMapOfBilin_eq_comp_of_garding (hC₀ : 0 < C₀)
    (hB : ∀ w, C₀ * ‖w‖ ^ 2 ≤ B w w + β * ‖J w‖ ^ 2) :
    continuousLinearMapOfBilin B =
      ((isCoercive_add_smul_of_garding hC₀ hB).continuousLinearEquivOfBilin :
          V →L[ℝ] V).comp
        (1 - β • (isCoercive_add_smul_of_garding hC₀ hB).formPerturbationOperator J) := by
  ext1 u
  apply ext_inner_right ℝ
  intro v
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    IsCoercive.continuousLinearEquivOfBilin_apply, continuousLinearMapOfBilin_apply]
  -- First evaluate the perturbation operator against the shifted form, then expand that form.
  simp only [sub_apply, one_apply_eq_self, smul_apply, map_sub, map_smul,
    IsCoercive.apply_formPerturbationOperator]
  simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSesqForm_apply_coe, innerSL_apply_apply, smul_eq_mul]
  ring

/-- **The operator of a Gårding form is Fredholm.** If `B` satisfies Gårding's inequality
`C₀ ‖w‖² ≤ B(w, w) + β ‖J w‖²` with `C₀ > 0` and `J` compact, then the Fréchet–Riesz operator
of `B` is Fredholm. -/
theorem isFredholm_continuousLinearMapOfBilin_of_garding (hJ : IsCompactOperator J)
    (hC₀ : 0 < C₀) (hB : ∀ w, C₀ * ‖w‖ ^ 2 ≤ B w w + β * ‖J w‖ ^ 2) :
    (continuousLinearMapOfBilin B).IsFredholm := by
  rw [continuousLinearMapOfBilin_eq_comp_of_garding hC₀ hB]
  exact ContinuousLinearMap.isFredholm_equiv_comp.mpr <| TauCeti.isFredholm_one_sub <|
    ((isCoercive_add_smul_of_garding hC₀ hB).isCompactOperator_formPerturbationOperator hJ).smul β

/-- **The operator of a Gårding form has index zero.** -/
theorem index_continuousLinearMapOfBilin_of_garding (hJ : IsCompactOperator J)
    (hC₀ : 0 < C₀) (hB : ∀ w, C₀ * ‖w‖ ^ 2 ≤ B w w + β * ‖J w‖ ^ 2) :
    (continuousLinearMapOfBilin B).index = 0 := by
  rw [continuousLinearMapOfBilin_eq_comp_of_garding hC₀ hB,
    ContinuousLinearMap.index_equiv_comp]
  exact ContinuousLinearMap.index_one_sub_eq_zero <|
    ((isCoercive_add_smul_of_garding hC₀ hB).isCompactOperator_formPerturbationOperator hJ).smul β

/-- **The compatibility condition for a Gårding form.** If `B` satisfies Gårding's inequality
`C₀ ‖w‖² ≤ B(w, w) + β ‖J w‖²` with `C₀ > 0` and `J` compact, then for a continuous linear
functional `ℓ` the problem `B(u, ·) = ℓ` has a solution exactly when `ℓ` vanishes on the adjoint
kernel `{w | ∀ v, B(v, w) = 0}`. -/
theorem exists_forall_apply_eq_iff_of_garding (hJ : IsCompactOperator J) (hC₀ : 0 < C₀)
    (hB : ∀ w, C₀ * ‖w‖ ^ 2 ≤ B w w + β * ‖J w‖ ^ 2) (ℓ : StrongDual ℝ V) :
    (∃ u, ∀ v, B u v = ℓ v) ↔ ∀ w, (∀ v, B v w = 0) → ℓ w = 0 := by
  refine ⟨fun ⟨u, hu⟩ w hw => (hu w).symm.trans (hw u), fun hℓ => ?_⟩
  set R := (continuousLinearMapOfBilin B).range
  have : CompleteSpace R :=
    (hJ.isFredholm_continuousLinearMapOfBilin_of_garding hC₀ hB).isClosed_range.completeSpace_coe
  -- The Fréchet–Riesz representative of `ℓ` is orthogonal to `Rᗮ`, the adjoint kernel.
  have hmem : (toDual ℝ V).symm ℓ ∈ R := by
    rw [← R.orthogonal_orthogonal, Submodule.mem_orthogonal]
    intro w hw
    rw [real_inner_comm, toDual_symm_apply]
    refine hℓ w fun v => ?_
    rw [← continuousLinearMapOfBilin_apply, real_inner_comm]
    exact (Submodule.mem_orthogonal' R w).mp hw _ ⟨v, rfl⟩
  obtain ⟨u, hu⟩ := hmem
  rw [ContinuousLinearMap.coe_coe] at hu
  refine ⟨u, fun v => ?_⟩
  rw [← continuousLinearMapOfBilin_apply, hu, toDual_symm_apply]

/-- **The kernel of a Gårding form is finite dimensional.** -/
theorem finiteDimensional_ker_of_garding (hJ : IsCompactOperator J) (hC₀ : 0 < C₀)
    (hB : ∀ w, C₀ * ‖w‖ ^ 2 ≤ B w w + β * ‖J w‖ ^ 2) :
    FiniteDimensional ℝ B.ker := by
  have := (hJ.isFredholm_continuousLinearMapOfBilin_of_garding hC₀ hB).finite_ker
  rwa [← ker_continuousLinearMapOfBilin]

/-- **The kernel and the adjoint kernel of a Gårding form have the same dimension.** For a
Gårding form `B`, the space `{w | ∀ v, B(v, w) = 0}` of solutions of the adjoint homogeneous
problem and the space `{u | ∀ v, B(u, v) = 0}` of solutions of the homogeneous problem have the
same finite dimension. For non-symmetric `B` the two spaces are in general different. -/
theorem finrank_ker_flip_eq_finrank_ker_of_garding (hJ : IsCompactOperator J) (hC₀ : 0 < C₀)
    (hB : ∀ w, C₀ * ‖w‖ ^ 2 ≤ B w w + β * ‖J w‖ ^ 2) :
    finrank ℝ B.flip.ker = finrank ℝ B.ker := by
  have hT := hJ.isFredholm_continuousLinearMapOfBilin_of_garding hC₀ hB
  have := hT.finite_ker
  have := hT.finite_coker
  have hindex := (continuousLinearMapOfBilin B).index_eq_finrank_sub
  rw [hJ.index_continuousLinearMapOfBilin_of_garding hC₀ hB, LinearEquiv.finrank_eq
    ((continuousLinearMapOfBilin B).cokerEquivKerAdjoint hT.isClosed_range).toLinearEquiv]
    at hindex
  rw [← ker_continuousLinearMapOfBilin B, ← ker_continuousLinearMapOfBilin B.flip,
    ← adjoint_continuousLinearMapOfBilin]
  omega

/-- **Unique solvability without coercivity.** If `B` satisfies Gårding's inequality and the
homogeneous problem `B(u, ·) = 0` has only the solution `u = 0`, then for every continuous linear
functional `ℓ` the problem `B(u, ·) = ℓ` has exactly one solution. -/
theorem existsUnique_forall_apply_eq_of_garding (hJ : IsCompactOperator J) (hC₀ : 0 < C₀)
    (hB : ∀ w, C₀ * ‖w‖ ^ 2 ≤ B w w + β * ‖J w‖ ^ 2) (hker : ∀ u, (∀ v, B u v = 0) → u = 0)
    (ℓ : StrongDual ℝ V) :
    ∃! u, ∀ v, B u v = ℓ v := by
  have hker' : B.ker = ⊥ :=
    (Submodule.eq_bot_iff _).mpr fun u hu => hker u fun v => by
      rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hu
      rw [hu, zero_apply]
  have := hJ.finiteDimensional_ker_of_garding (B := B.flip) hC₀ fun w => by simpa using hB w
  have hflip : B.flip.ker = ⊥ := by
    rw [← Submodule.finrank_eq_zero, hJ.finrank_ker_flip_eq_finrank_ker_of_garding hC₀ hB,
      hker', finrank_bot]
  obtain ⟨u, hu⟩ := (hJ.exists_forall_apply_eq_iff_of_garding hC₀ hB ℓ).mpr fun w hw => by
    have hw0 : w ∈ B.flip.ker := LinearMap.mem_ker.mpr <| ContinuousLinearMap.ext hw
    rw [hflip, Submodule.mem_bot] at hw0
    rw [hw0, map_zero]
  refine ⟨u, hu, fun y hy => sub_eq_zero.mp <| hker _ fun v => ?_⟩
  rw [map_sub, sub_apply, hy v, hu v, sub_self]

end IsCompactOperator
