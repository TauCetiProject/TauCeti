/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn

/-!
# Stability of surjectivity under small perturbations

An additive endomorphism of a complete normed group that is uniformly closer than `1` to the
identity is surjective, by the contraction mapping principle; the next two results reduce to it.

Surjectivity onto a finite-dimensional space is stable under small perturbations in the operator
norm: the surjective maps form an open subset of the space of continuous linear maps. The source
is an arbitrary seminormed space over a complete nontrivially normed field.

Surjectivity onto a complete normed group is stable under perturbations that are small relative
to the map itself. If `Q` is a surjective linear map from a module `D` over any semiring into a
complete normed group and `‖K z‖ ≤ θ * ‖Q z‖` for every `z` with `θ < 1`, then `Q + K` is
surjective: `K` factors as `S ∘ Q` with `S` additive and `‖S y‖ ≤ θ * ‖y‖`, and
`Q + K = (id + S) ∘ Q` with `id + S` within `θ` of the identity. No topology on `D` is needed,
which is what makes the statement usable for operators defined on the domain of an unbounded
operator.

Mathlib records the companion fact that a surjective continuous linear map between Banach spaces
is an open map, in `ContinuousLinearMap.isOpenMap`; the openness proved here is openness of the
locus of such maps inside `E →L[𝕜] F`, not of any one of them.

## Main results

* `TauCeti.surjective_of_norm_sub_apply_le`: an additive endomorphism of a complete normed
  group (for instance a linear map over any ring) uniformly closer than `1` to the identity is
  surjective.
* `TauCeti.isOpen_setOf_surjective`: surjectivity onto a finite-dimensional space is an open
  condition on continuous linear maps.
* `LinearMap.surjective_add_of_norm_le`: a surjective linear map into a complete normed group
  stays surjective under a perturbation bounded by `θ < 1` times the map.
* `ContinuousLinearMap.surjective_of_norm_sub_lt_inv_rightInverse`: a perturbation smaller than
  the reciprocal bound of a given bounded nonlinear right inverse stays surjective.
* `ContinuousLinearMap.surjective_coprod_toSpanSingleton_iff`: a continuous linear map extended
  by the line through a vector is surjective exactly when its range and the vector span the
  target.
-/

public section

open Function

namespace TauCeti

section ContractingPerturbation

variable {M F : Type*} [NormedAddCommGroup M] [CompleteSpace M] [FunLike F M M]
  [AddMonoidHomClass F M M]

/-- On a complete normed group, an additive endomorphism `v` with `‖x - v x‖ ≤ c * ‖x‖` for some
`c < 1` is surjective: `v s = y` for the fixed point `s` of the contraction `x ↦ x - v x + y`.
This applies in particular to linear and continuous linear endomorphisms over any ring. -/
theorem surjective_of_norm_sub_apply_le {v : F} {c : ℝ} (hc : c < 1)
    (h : ∀ x, ‖x - v x‖ ≤ c * ‖x‖) : Surjective v := by
  intro y
  have hf : ContractingWith (Real.toNNReal c) (fun x ↦ x - v x + y) :=
    ⟨Real.toNNReal_lt_one.mpr hc, LipschitzWith.of_dist_le' fun x z ↦ by
      simpa [dist_eq_norm, map_sub, sub_sub_sub_comm] using h (x - z)⟩
  have hs : _ - _ + y = _ := hf.fixedPoint_isFixedPt
  rw [sub_add_eq_add_sub, sub_eq_iff_eq_add, add_right_inj] at hs
  exact ⟨_, hs.symm⟩

end ContractingPerturbation

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- Surjectivity onto a finite-dimensional space is an open condition on continuous linear
maps. -/
theorem isOpen_setOf_surjective : IsOpen {A : E →L[𝕜] F | Surjective A} := by
  have : CompleteSpace F := FiniteDimensional.completeSpace 𝕜 F
  rw [Metric.isOpen_iff]
  rintro A (hA : Surjective A)
  obtain ⟨R, hAR⟩ := A.exists_rightInverse_of_surjective (A.range_eq_top_of_surjective hA)
  have hAR (y : F) : A (R y) = y := by simpa using DFunLike.congr_fun hAR y
  refine ⟨(‖R‖ + 1)⁻¹, by positivity, fun B hB ↦ ?_⟩
  rw [Metric.mem_ball, dist_eq_norm] at hB
  have hlt : ‖B - A‖ * ‖R‖ < 1 := calc
    ‖B - A‖ * ‖R‖ ≤ ‖B - A‖ * (‖R‖ + 1) := by gcongr; linarith
    _ < (‖R‖ + 1)⁻¹ * (‖R‖ + 1) := by gcongr
    _ = 1 := inv_mul_cancel₀ (by positivity)
  -- Since `A ∘ R = id`, the endomorphism `B ∘ R` of `F` is within `‖B - A‖ * ‖R‖ < 1` of the
  -- identity, hence onto.
  have hBR : Surjective (B.comp R) := surjective_of_norm_sub_apply_le hlt fun y ↦ calc
    ‖y - B.comp R y‖ = ‖(B - A) (R y)‖ := by
      rw [norm_sub_rev, ContinuousLinearMap.comp_apply, sub_apply, hAR]
    _ ≤ ‖B - A‖ * (‖R‖ * ‖y‖) := (B - A).le_opNorm_of_le (R.le_opNorm y)
    _ = ‖B - A‖ * ‖R‖ * ‖y‖ := (mul_assoc _ _ _).symm
  rw [ContinuousLinearMap.coe_comp] at hBR
  exact hBR.of_comp

end TauCeti

namespace LinearMap

variable {R D Y : Type*} [Semiring R] [AddCommGroup D] [Module R D]
  [NormedAddCommGroup Y] [Module R Y] [CompleteSpace Y]

/-- **Surjectivity is stable under relatively small perturbations.** If `Q : D →ₗ[R] Y` is a
surjective linear map into a complete normed group and `‖K z‖ ≤ θ * ‖Q z‖` for every `z`, with
`θ < 1`, then `Q + K` is surjective. Only additivity is used: the scalars `R` are an arbitrary
semiring, unrelated to the norm of `Y`, and `R = ℕ` covers additive homomorphisms. -/
theorem surjective_add_of_norm_le (Q K : D →ₗ[R] Y) (hQ : Surjective Q) {θ : ℝ} (hθ : θ < 1)
    (hK : ∀ z, ‖K z‖ ≤ θ * ‖Q z‖) : Surjective (Q + K) := by
  have hker : Q.toAddMonoidHom.ker ≤ K.toAddMonoidHom.ker := fun z hz ↦ by
    rw [AddMonoidHom.mem_ker, toAddMonoidHom_coe] at hz ⊢
    simpa [hz] using hK z
  -- `K` factors through `Q` as `S ∘ Q`, with `S` additive. (`liftOfSurjective` abbreviates
  -- `liftOfRightInverse` at `surjInv hQ`, hence the lemma used for `hS`.)
  let S : Y →+ Y := Q.toAddMonoidHom.liftOfSurjective hQ ⟨K.toAddMonoidHom, hker⟩
  have hS (z : D) : S (Q z) = K z :=
    Q.toAddMonoidHom.liftOfRightInverse_comp_apply _ _ ⟨K.toAddMonoidHom, hker⟩ z
  -- `Q + K = (id + S) ∘ Q`, and `id + S` is within `θ` of the identity, hence onto.
  have hQK : ⇑(Q + K) = ⇑(AddMonoidHom.id Y + S) ∘ ⇑Q := by
    ext z
    simp [hS]
  have hSY : Surjective ⇑(AddMonoidHom.id Y + S) :=
    TauCeti.surjective_of_norm_sub_apply_le hθ fun y ↦ by
      obtain ⟨z, rfl⟩ := hQ y
      simpa [hS] using hK z
  rw [hQK]
  exact hSY.comp hQ

end LinearMap

namespace ContinuousLinearMap

open Set

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- A perturbation smaller than the reciprocal bound of a nonlinear right inverse stays onto.
No complement to the kernel is needed. -/
theorem surjective_of_norm_sub_lt_inv_rightInverse [CompleteSpace E]
    (T S : E →L[𝕜] F) (R : T.NonlinearRightInverse)
    (h : ‖S - T‖ < (R.nnNorm : ℝ)⁻¹) : Function.Surjective S := by
  have ha : ApproximatesLinearOn (S : E → F) T univ ‖S - T‖₊ := by
    intro x _ y _
    have he : S x - S y - T (x - y) = (S - T) (x - y) := by
      simp only [map_sub, sub_apply]
      abel
    rw [he]
    exact (S - T).le_opNorm _
  have hnn : ‖S - T‖₊ < R.nnNorm⁻¹ := by exact_mod_cast h
  have hopen : IsOpen (Set.range S) := by
    simpa only [image_univ] using ha.open_image R isOpen_univ (Or.inr hnn)
  apply LinearMap.range_eq_top.1
  apply Submodule.eq_top_of_nonempty_interior'
  rw [LinearMap.coe_range, ContinuousLinearMap.coe_coe, hopen.interior_eq]
  exact ⟨0, 0, map_zero S⟩

/-- A continuous linear map and a vector together span the target exactly when the map extended
by the line through the vector is surjective. -/
theorem surjective_coprod_toSpanSingleton_iff {V : Type*} [NormedAddCommGroup V]
    [NormedSpace 𝕜 V] (L : V →L[𝕜] F) (v : F) :
    Function.Surjective (L.coprod (toSpanSingleton 𝕜 v)) ↔
      LinearMap.range (L : V →ₗ[𝕜] F) ⊔ (𝕜 ∙ v) = ⊤ := by
  rw [← coe_coe, ← LinearMap.range_eq_top, range_coprod, toLinearMap_toSpanSingleton,
    LinearMap.range_toSpanSingleton]

end ContinuousLinearMap
