/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import TauCeti.Analysis.Fredholm.Spectral.FractionalLinear
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Module
import TauCeti.Analysis.Calculus.ContinuousLinearMapInverse
import TauCeti.Analysis.Fredholm.Basic
import TauCeti.Analysis.Fredholm.CompactPerturbation
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-!
# Shifted resolvent transforms of self-adjoint operators on a common domain

Let `ι : D →L H` be an injective bounded operator from a Banach space `D` into a Hilbert space `H`,
and `A : D →L H` a bounded operator which is symmetric through `ι`: `⟪A x, ι y⟫ = ⟪ι x, A y⟫`.
The bounded operator `A` on the common domain `D` describes the unbounded operator
`ContinuousLinearMap.domainOperator ι A hι` on `H` with domain `range ι`; this is how a self-adjoint
unbounded operator, such as `-J ∂_t` on a Sobolev space of loops, is given by a bounded operator on
its domain with the graph norm. For a real shift `c ≠ 0` at which `c ι - A` is invertible, the
**shifted resolvent transform**

`τ_c A = c A (c ι - A)⁻¹ = c² ι (c ι - A)⁻¹ - c`

(`ContinuousLinearMap.shiftedResolventTransform`,
`ContinuousLinearMap.shiftedResolventTransform_eq_sub`) is a bounded operator on `H`. It is
self-adjoint (`ContinuousLinearMap.isSelfAdjoint_shiftedResolventTransform`), it is a nonzero
multiple of a compact perturbation of the identity when `ι` is compact, hence Fredholm
(`ContinuousLinearMap.isFredholm_shiftedResolventTransform`), and it depends continuously on `A`
(`ContinuousOn.shiftedResolventTransform`). An eigenvector `ι x` of the unbounded operator, with
`A x = λ ι x`, is an eigenvector of `τ_c A` with eigenvalue `c λ / (c - λ)`
(`ContinuousLinearMap.shiftedResolventTransform_apply_of_apply_eq_smul`). The full spectral
correspondence is proved here only for the eigenvalue `0`: at a shift `c ≠ 0` with `c ι - A`
invertible, the kernel of `τ_c A` is the image under `ι` of the kernel of `A`
(`ContinuousLinearMap.ker_shiftedResolventTransform`). The function `λ ↦ c λ / (c - λ)` fixes `0`
and has derivative `1` there. Along a real path `A` with derivative `A'` at `t₀`, the transforms
have derivative `c² ι R A' R` at `t₀`, for `R = (c ι - A t₀)⁻¹`
(`HasDerivAt.shiftedResolventTransform`).

The shift is a choice, and a single shift need not be admissible along a whole path. The transforms
at two shifts `c` and `c'` are related by the fractional linear function `x ↦ x / (1 + k x)`, for
`k = (c' - c) / (c c')`:

`τ_{c'} A (1 + k τ_c A) = τ_c A`

(`ContinuousLinearMap.shiftedResolventTransform_mul_one_add_smul`), where `1 + k τ_c A` is
invertible (`ContinuousLinearMap.isUnit_one_add_smul_shiftedResolventTransform`), because it is
`(c / c') (c' ι - A) (c ι - A)⁻¹`. Hence the spectral flow of the transformed path does not depend
on the shift (`TauCeti.spectralFlow_shiftedResolventTransform_eq`): this is
`TauCeti.spectralFlow_mul_ringInverse_one_add_smul` for the change of operator `x ↦ x / (1 + k x)`.
For `D = H` and `ι = 1`, the transform at `c` is itself such an image, `A (1 - A / c)⁻¹`
(`ContinuousLinearMap.shiftedResolventTransform_one_eq_mul_ringInverse`).

Transforms are natural under changes of trivialization: if isomorphisms `V : D ≃L D'` and
`U : H ≃L K` intertwine the embeddings, `ι' ∘ V = U ∘ ι`, then `c ι' - U A V⁻¹ = U (c ι - A) V⁻¹`,
so `c` is admissible for `U A V⁻¹` exactly when it is for `A`
(`ContinuousLinearMap.isInvertible_smul_sub_comp_comp_symm_iff`), and the transform of `U A V⁻¹`
with respect to `ι'` is `U (τ_c A) U⁻¹`
(`ContinuousLinearMap.shiftedResolventTransform_comp_comp_symm`).

## References

* J. Robbin and D. Salamon, *The spectral flow and the Maslov index*, Bull. London Math. Soc.
  **27** (1995), 1--33, Section 4.
* B. Booss-Bavnbek, M. Lesch and J. Phillips, *Unbounded Fredholm operators and spectral flow*,
  Canad. J. Math. **57** (2005), 225--250.
-/

public section

noncomputable section

open Filter Set Topology

namespace ContinuousLinearMap

variable {𝕜 D H : Type*} [RCLike 𝕜] [NormedAddCommGroup D] [NormedSpace 𝕜 D]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- The **shifted resolvent transform** `c A (c ι - A)⁻¹` at a real shift `c` of an operator
`A : D →L H` on the common domain `D`, embedded in `H` by `ι`. It is the junk value `0` when
`c ι - A` is not invertible. -/
def shiftedResolventTransform (ι A : D →L[𝕜] H) (c : ℝ) : H →L[𝕜] H :=
  (c : 𝕜) • (A ∘L ((c : 𝕜) • ι - A).inverse)

variable {ι A : D →L[𝕜] H} {c c' : ℝ}

/-- When `c ι - A` is invertible, its inverse sends `c ι x - A x` back to `x`. -/
private theorem inverse_smul_sub_apply (h : ((c : 𝕜) • ι - A).IsInvertible) (x : D) :
    ((c : 𝕜) • ι - A).inverse ((c : 𝕜) • ι x - A x) = x := by
  simpa only [sub_apply, smul_apply] using h.inverse_apply_self x

/-- Unfolds `ContinuousLinearMap.shiftedResolventTransform`. -/
theorem shiftedResolventTransform_def (ι A : D →L[𝕜] H) (c : ℝ) :
    ι.shiftedResolventTransform A c = (c : 𝕜) • (A ∘L ((c : 𝕜) • ι - A).inverse) :=
  (rfl)

/-- The shifted resolvent transform at a shift `c` with `c ι - A` not invertible is the junk
value `0`. -/
@[simp]
theorem shiftedResolventTransform_of_not_isInvertible (h : ¬((c : 𝕜) • ι - A).IsInvertible) :
    ι.shiftedResolventTransform A c = 0 := by
  rw [shiftedResolventTransform_def, inverse_of_not_isInvertible h, comp_zero, smul_zero]

/-- The shifted resolvent transform at a shift `c` with `c ι - A` invertible sends `(c ι - A) x`
to `c A x`. -/
theorem shiftedResolventTransform_apply_sub (h : ((c : 𝕜) • ι - A).IsInvertible) (x : D) :
    ι.shiftedResolventTransform A c ((c : 𝕜) • ι x - A x) = (c : 𝕜) • A x := by
  rw [shiftedResolventTransform_def, smul_apply, comp_apply, inverse_smul_sub_apply h]

/-- The shifted resolvent transform at a shift `c` with `c ι - A` invertible is
`c² ι (c ι - A)⁻¹ - c`. -/
theorem shiftedResolventTransform_eq_sub (h : ((c : 𝕜) • ι - A).IsInvertible) :
    ι.shiftedResolventTransform A c =
      (c : 𝕜) ^ 2 • (ι ∘L ((c : 𝕜) • ι - A).inverse) - (c : 𝕜) • 1 := by
  ext y
  obtain ⟨x, rfl⟩ := h.surjective y
  simp only [sub_apply, smul_apply, comp_apply, inverse_smul_sub_apply h,
    shiftedResolventTransform_apply_sub h,
    one_apply_eq_self]
  module

/-- An eigenvector `ι x` of the operator, with `A x = μ ι x`, is an eigenvector of the shifted
resolvent transform at a shift `c` with `c ι - A` invertible, with eigenvalue `c μ / (c - μ)`. When
`μ = c` the invertibility forces `x = 0`, so both sides vanish. -/
theorem shiftedResolventTransform_apply_of_apply_eq_smul (h : ((c : 𝕜) • ι - A).IsInvertible)
    {x : D} {μ : ℝ} (hx : A x = (μ : 𝕜) • ι x) :
    ι.shiftedResolventTransform A c (ι x) = ((c * μ / (c - μ) : ℝ) : 𝕜) • ι x := by
  rcases eq_or_ne μ c with rfl | hμ
  · obtain rfl : x = 0 := h.injective (by simp [hx])
    simp
  have hcμ : ((c - μ : ℝ) : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.2 (sub_ne_zero.2 hμ.symm)
  have hR : ((c : 𝕜) • ι - A).inverse (ι x) = ((c - μ : ℝ) : 𝕜)⁻¹ • x := by
    refine h.injective ?_
    rw [h.self_apply_inverse, map_smul, sub_apply, smul_apply, hx, ← sub_smul, smul_smul]
    push_cast
    rw [inv_mul_cancel₀ (by exact_mod_cast hcμ), one_smul]
  rw [shiftedResolventTransform_def, smul_apply, comp_apply, hR, map_smul, hx, smul_smul,
    smul_smul]
  congr 1
  push_cast at hcμ ⊢
  field_simp

/-- The shifted resolvent transform of an operator which is symmetric through `ι` is
self-adjoint. -/
theorem isSelfAdjoint_shiftedResolventTransform [CompleteSpace H]
    (hsymm : ∀ x y, ⟪A x, ι y⟫ = ⟪ι x, A y⟫) :
    IsSelfAdjoint (ι.shiftedResolventTransform A c) := by
  by_cases h : ((c : 𝕜) • ι - A).IsInvertible
  swap
  · rw [shiftedResolventTransform_of_not_isInvertible h]
    exact .zero _
  rw [isSelfAdjoint_iff_isSymmetric]
  intro y z
  obtain ⟨x, rfl⟩ := h.surjective y
  obtain ⟨w, rfl⟩ := h.surjective z
  simp only [coe_coe, sub_apply, smul_apply, shiftedResolventTransform_apply_sub h]
  simp only [inner_smul_left, inner_smul_right, inner_sub_left, inner_sub_right, hsymm,
    RCLike.conj_ofReal]
  ring

/-- When `ι` is compact, the shifted resolvent transform at a shift `c ≠ 0` with `c ι - A`
invertible is Fredholm: it is `-c` times a compact perturbation of the identity. -/
theorem isFredholm_shiftedResolventTransform [CompleteSpace H] (hι : IsCompactOperator ι)
    (hc : c ≠ 0) (h : ((c : 𝕜) • ι - A).IsInvertible) :
    (ι.shiftedResolventTransform A c).IsFredholm := by
  set R := ((c : 𝕜) • ι - A).inverse
  have hK : IsCompactOperator ((c : 𝕜) • (ι ∘L R)) := (hι.comp_clm R).smul _
  have hτ : ι.shiftedResolventTransform A c = (-(c : 𝕜)) • (1 - (c : 𝕜) • (ι ∘L R)) := by
    rw [shiftedResolventTransform_eq_sub h]
    module
  rw [hτ]
  exact (TauCeti.isFredholm_one_sub hK).smul (neg_ne_zero.2 (RCLike.ofReal_ne_zero.2 hc))

/-- At a shift `c ≠ 0` with `c ι - A` invertible, the kernel of the shifted resolvent transform is
the image under `ι` of the kernel of `A`: the transform sends `c ι x - A x` to `c A x`, which
vanishes exactly when `A x = 0`, and then `c ι x - A x = ι (c x)`. -/
theorem ker_shiftedResolventTransform (h : ((c : 𝕜) • ι - A).IsInvertible) (hc : c ≠ 0) :
    (ι.shiftedResolventTransform A c).ker = A.ker.map (ι : D →ₗ[𝕜] H) := by
  have hc𝕜 : (c : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.2 hc
  ext y
  obtain ⟨x, rfl⟩ := h.surjective y
  simp only [LinearMap.mem_ker, Submodule.mem_map, coe_coe, shiftedResolventTransform_apply_sub h,
    smul_eq_zero, hc𝕜, false_or, sub_apply, smul_apply]
  constructor
  · intro hx
    exact ⟨(c : 𝕜) • x, by simp [hx], by simp [hx]⟩
  · rintro ⟨z, hz, hzx⟩
    -- `c ι - A` sends both `x` and `c⁻¹ z` to `ι z`, so `x = c⁻¹ z` lies in the kernel of `A`.
    have hxz : x = (c : 𝕜)⁻¹ • z := h.injective <| by
      simp only [sub_apply, smul_apply, map_smul, hz, sub_zero, smul_smul,
        inv_mul_cancel₀ hc𝕜, one_smul] at hzx ⊢
      exact hzx.symm
    simp [hxz, hz]

/-- For shifts `c, c' ≠ 0` with `c ι - A` invertible, `1 + k τ_c A`, for `k = (c' - c) / (c c')`,
is `(c / c') (c' ι - A) (c ι - A)⁻¹`. -/
theorem one_add_smul_shiftedResolventTransform_eq (h : ((c : 𝕜) • ι - A).IsInvertible)
    (hc : c ≠ 0) (hc' : c' ≠ 0) :
    1 + (((c' - c) / (c * c') : ℝ) : 𝕜) • ι.shiftedResolventTransform A c =
      ((c / c' : ℝ) : 𝕜) • (((c' : 𝕜) • ι - A) ∘L ((c : 𝕜) • ι - A).inverse) := by
  ext y
  obtain ⟨x, rfl⟩ := h.surjective y
  simp only [add_apply, sub_apply, smul_apply, comp_apply, inverse_smul_sub_apply h,
    shiftedResolventTransform_apply_sub h, one_apply_eq_self]
  have hc𝕜 : (c : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.2 hc
  have hc'𝕜 : (c' : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.2 hc'
  match_scalars <;> field_simp
  ring

/-- **Change of shift.** For shifts `c, c' ≠ 0` with `c ι - A` and `c' ι - A` invertible, the
shifted resolvent transforms satisfy `τ_{c'} A (1 + k τ_c A) = τ_c A` for
`k = (c' - c) / (c c')`. -/
theorem shiftedResolventTransform_mul_one_add_smul (h : ((c : 𝕜) • ι - A).IsInvertible)
    (h' : ((c' : 𝕜) • ι - A).IsInvertible) (hc : c ≠ 0) (hc' : c' ≠ 0) :
    ι.shiftedResolventTransform A c' *
        (1 + (((c' - c) / (c * c') : ℝ) : 𝕜) • ι.shiftedResolventTransform A c) =
      ι.shiftedResolventTransform A c := by
  rw [one_add_smul_shiftedResolventTransform_eq h hc hc']
  ext y
  obtain ⟨x, rfl⟩ := h.surjective y
  rw [mul_apply_eq_comp]
  simp only [comp_apply, sub_apply, smul_apply, inverse_smul_sub_apply h, map_smul,
    shiftedResolventTransform_apply_sub h, shiftedResolventTransform_apply_sub h', smul_smul]
  congr 1
  have hc'𝕜 : (c' : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.2 hc'
  push_cast
  field_simp

/-- For a shift `c'` with `c' ι - A` invertible and any shift `c`, `1 + k τ_c A` is invertible
for `k = (c' - c) / (c c')`. -/
theorem isUnit_one_add_smul_shiftedResolventTransform (h' : ((c' : 𝕜) • ι - A).IsInvertible) :
    IsUnit (1 + (((c' - c) / (c * c') : ℝ) : 𝕜) • ι.shiftedResolventTransform A c) := by
  -- In the degenerate cases `k τ_c A = 0`.
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  rcases eq_or_ne c' 0 with rfl | hc'
  · simp
  by_cases h : ((c : 𝕜) • ι - A).IsInvertible
  swap
  · simp [h]
  rw [one_add_smul_shiftedResolventTransform_eq h hc hc', ← isInvertible_iff_isUnit,
    isInvertible_smul_iff (RCLike.ofReal_ne_zero.2 (div_ne_zero hc hc'))]
  exact h'.comp h.inverse

section Conjugation

variable {D' K : Type*} [NormedAddCommGroup D'] [NormedSpace 𝕜 D'] [NormedAddCommGroup K]
  [InnerProductSpace 𝕜 K] {ι' : D' →L[𝕜] K}

/-- If `V : D ≃L D'` and `U : H ≃L K` intertwine the embeddings, `ι' ∘ V = U ∘ ι`, then every
shift of the conjugated operator `U A V⁻¹` is the conjugate of the corresponding shift of `A`. -/
private theorem smul_sub_comp_comp_symm (U : H ≃L[𝕜] K) (V : D ≃L[𝕜] D')
    (h : ι' ∘L (V : D →L[𝕜] D') = (U : H →L[𝕜] K) ∘L ι) (A : D →L[𝕜] H) (c : 𝕜) :
    c • ι' - (U : H →L[𝕜] K) ∘L A ∘L (V.symm : D' →L[𝕜] D) =
      (U : H →L[𝕜] K) ∘L (c • ι - A) ∘L (V.symm : D' →L[𝕜] D) := by
  ext x
  have hx : ι' x = U (ι (V.symm x)) := by
    simpa using congr($h (V.symm x))
  simp [hx]

/-- **Admissible shifts under a change of trivialization.** If `V : D ≃L D'` and `U : H ≃L K`
intertwine the embeddings, `ι' ∘ V = U ∘ ι`, then a shift `c` is admissible for the conjugated
operator `U A V⁻¹`, that is `c ι' - U A V⁻¹` is invertible, exactly when it is admissible for
`A`. -/
theorem isInvertible_smul_sub_comp_comp_symm_iff (U : H ≃L[𝕜] K) (V : D ≃L[𝕜] D')
    (h : ι' ∘L (V : D →L[𝕜] D') = (U : H →L[𝕜] K) ∘L ι) (c : 𝕜) :
    (c • ι' - (U : H →L[𝕜] K) ∘L A ∘L (V.symm : D' →L[𝕜] D)).IsInvertible ↔
      (c • ι - A).IsInvertible := by
  rw [smul_sub_comp_comp_symm U V h, isInvertible_equiv_comp, isInvertible_comp_equiv]

/-- **Shifted resolvent transforms under a change of trivialization.** If `V : D ≃L D'` and
`U : H ≃L K` intertwine the embeddings, `ι' ∘ V = U ∘ ι`, then at every shift `c` the shifted
resolvent transform of the conjugated operator `U A V⁻¹` with respect to `ι'` is the conjugate
`U (τ_c A) U⁻¹` of the shifted resolvent transform of `A` with respect to `ι`. -/
theorem shiftedResolventTransform_comp_comp_symm (U : H ≃L[𝕜] K) (V : D ≃L[𝕜] D')
    (h : ι' ∘L (V : D →L[𝕜] D') = (U : H →L[𝕜] K) ∘L ι) (A : D →L[𝕜] H) (c : ℝ) :
    ι'.shiftedResolventTransform ((U : H →L[𝕜] K) ∘L A ∘L (V.symm : D' →L[𝕜] D)) c =
      (U : H →L[𝕜] K) ∘L ι.shiftedResolventTransform A c ∘L (U.symm : K →L[𝕜] H) := by
  rw [shiftedResolventTransform_def, shiftedResolventTransform_def, smul_sub_comp_comp_symm U V h,
    inverse_equiv_comp, inverse_comp_equiv]
  ext x
  simp

end Conjugation

section RealScalars

variable [Module ℝ (H →L[𝕜] H)] [IsScalarTower ℝ 𝕜 (H →L[𝕜] H)]

/-- On `D = H` with `ι = 1`, the shifted resolvent transform at a shift `c ≠ 0` with `c - A`
invertible is `A (1 - A / c)⁻¹`, the image of `A` under `x ↦ x / (1 - x / c)`. -/
theorem shiftedResolventTransform_one_eq_mul_ringInverse {A : H →L[𝕜] H} (hc : c ≠ 0)
    (h : ((c : 𝕜) • (1 : H →L[𝕜] H) - A).IsInvertible) :
    (1 : H →L[𝕜] H).shiftedResolventTransform A c = A * Ring.inverse (1 + (-c⁻¹) • A) := by
  refine (Ring.eq_mul_inverse_iff_mul_eq _ _ _ (isUnit_one_add_neg_inv_smul hc h)).2 ?_
  ext x
  rw [one_add_neg_inv_smul_eq hc, RCLike.algebraMap_eq_ofReal, mul_apply_eq_comp]
  simp only [smul_apply, sub_apply, map_smul, shiftedResolventTransform_apply_sub h, smul_smul,
    inv_mul_cancel₀ (RCLike.ofReal_ne_zero (K := 𝕜) |>.2 hc), one_smul]

end RealScalars

end ContinuousLinearMap

/-- The shifted resolvent transforms at a fixed shift `c` of a continuous family of operators on a
common complete domain, along which `c ι - A` stays invertible, form a continuous family. -/
theorem ContinuousOn.shiftedResolventTransform {𝕜 D H X : Type*} [RCLike 𝕜]
    [NormedAddCommGroup D] [NormedSpace 𝕜 D] [CompleteSpace D] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [TopologicalSpace X] {ι : D →L[𝕜] H} {A : X → D →L[𝕜] H} {s : Set X}
    {c : ℝ} (hA : ContinuousOn A s) (hinv : ∀ t ∈ s, ((c : 𝕜) • ι - A t).IsInvertible) :
    ContinuousOn (fun t ↦ ι.shiftedResolventTransform (A t) c) s := fun t ht ↦ by
  have hsub : ContinuousWithinAt (fun t ↦ (c : 𝕜) • ι - A t) s t :=
    continuousWithinAt_const.sub (hA t ht)
  have hR : ContinuousWithinAt (fun t ↦ ((c : 𝕜) • ι - A t).inverse) s t :=
    ContinuousAt.comp_continuousWithinAt (f := fun t ↦ (c : 𝕜) • ι - A t)
      ((hinv t ht).contDiffAt_map_inverse (n := 0)).continuousAt hsub
  have hcomp : ContinuousWithinAt (fun t ↦ A t ∘L ((c : 𝕜) • ι - A t).inverse) s t :=
    (hA t ht).clm_comp hR
  simp only [ContinuousLinearMap.shiftedResolventTransform_def]
  exact hcomp.const_smul (c : 𝕜)

/-- Over `ℝ` the coercion `RCLike.ofReal` is the identity, so at `𝕜 = ℝ` the shift
`(c : 𝕜) • ι - A` of the shifted resolvent transform is the real shift `c • ι - A`. -/
theorem ContinuousLinearMap.isInvertible_ofReal_smul_sub_iff {D H : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup H] [NormedSpace ℝ H] {ι A : D →L[ℝ] H} {c : ℝ} :
    ((RCLike.ofReal c : ℝ) • ι - A).IsInvertible ↔ (c • ι - A).IsInvertible := by
  rw [RCLike.ofReal_real_eq_id, id]

/-- **The derivative of the shifted resolvent transforms.** Let `A` be a path of operators on a
common Banach domain `D`, embedded in a real Hilbert space `H` by `ι`, with derivative `A'` at `t₀`,
and let `c ι - A t₀` be invertible. Then the shifted resolvent transforms at `c` have derivative
`c² ι R A' R` at `t₀`, for `R = (c ι - A t₀)⁻¹`: near `t₀` the transform is `c² ι (c ι - A t)⁻¹ - c`
(`ContinuousLinearMap.shiftedResolventTransform_eq_sub`). -/
theorem HasDerivAt.shiftedResolventTransform {D H : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [CompleteSpace D] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {ι : D →L[ℝ] H} {A : ℝ → D →L[ℝ] H} {A' : D →L[ℝ] H} {t₀ c : ℝ} (hA : HasDerivAt A A' t₀)
    (h : (c • ι - A t₀).IsInvertible) :
    HasDerivAt (fun t ↦ ι.shiftedResolventTransform (A t) c)
      (c ^ 2 • (ι ∘L (c • ι - A t₀).inverse ∘L A' ∘L (c • ι - A t₀).inverse)) t₀ := by
  have hsub : HasDerivAt (fun t ↦ c • ι - A t) (-A') t₀ := by
    have h := HasDerivAt.sub (hasDerivAt_const t₀ (c • ι)) hA
    rwa [zero_sub] at h
  have hR := HasDerivAt.clm_comp (hasDerivAt_const t₀ ι)
    (HasDerivAt.clm_inverse_of_completeSpace hsub h)
  have hinv : ∀ᶠ t in 𝓝 t₀, (c • ι - A t).IsInvertible :=
    (HasDerivAt.continuousAt hsub).eventually h.eventually_nhds
  refine HasDerivAt.congr_deriv (HasDerivAt.congr_of_eventuallyEq (HasDerivAt.sub_const
    (c • (1 : H →L[ℝ] H)) (HasDerivAt.const_smul (c ^ 2) hR)) ?_) ?_
  · filter_upwards [hinv] with t ht
    simpa only [RCLike.ofReal_real_eq_id, id_eq, Pi.smul_apply] using
      ι.shiftedResolventTransform_eq_sub (ContinuousLinearMap.isInvertible_ofReal_smul_sub_iff.2 ht)
  · simp

namespace TauCeti

variable {𝕜 D H : Type*} [RCLike 𝕜] [NormedAddCommGroup D] [NormedSpace 𝕜 D] [CompleteSpace D]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  [NormedAlgebra ℝ (H →L[𝕜] H)] [IsometricContinuousFunctionalCalculus ℝ (H →L[𝕜] H) IsSelfAdjoint]
  [IsScalarTower ℝ 𝕜 (H →L[𝕜] H)]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- **The spectral flow of the shifted resolvent transforms does not depend on the shift.** Let `ι`
be a compact embedding of a Banach space `D` into a Hilbert space `H`, and `A` a continuous path in
`D →L H` of operators symmetric through `ι`. For nonzero real shifts `c` and `c'` at which
`c ι - A t` and `c' ι - A t` are invertible for every `t ∈ [a, b]`, the paths of shifted resolvent
transforms at `c` and at `c'` have the same spectral flow. -/
theorem spectralFlow_shiftedResolventTransform_eq {ι : D →L[𝕜] H} {A : ℝ → D →L[𝕜] H}
    {a b c c' : ℝ} (hab : a ≤ b) (hι : IsCompactOperator ι) (hA : ContinuousOn A (Icc a b))
    (hsymm : ∀ t ∈ Icc a b, ∀ x y, ⟪A t x, ι y⟫ = ⟪ι x, A t y⟫) (hc : c ≠ 0) (hc' : c' ≠ 0)
    (hinv : ∀ t ∈ Icc a b, ((c : 𝕜) • ι - A t).IsInvertible)
    (hinv' : ∀ t ∈ Icc a b, ((c' : 𝕜) • ι - A t).IsInvertible) :
    spectralFlow (fun t ↦ ι.shiftedResolventTransform (A t) c') a b =
      spectralFlow (fun t ↦ ι.shiftedResolventTransform (A t) c) a b := by
  set k : ℝ := (c' - c) / (c * c')
  have heq : EqOn (fun t ↦ ι.shiftedResolventTransform (A t) c')
      (fun t ↦ ι.shiftedResolventTransform (A t) c *
        Ring.inverse (1 + k • ι.shiftedResolventTransform (A t) c)) (Icc a b) := fun t ht ↦ by
    simp only [RCLike.real_smul_eq_coe_smul (K := 𝕜) (E := H →L[𝕜] H)]
    exact (Ring.eq_mul_inverse_iff_mul_eq _ _ _
      (ι.isUnit_one_add_smul_shiftedResolventTransform (hinv' t ht))).2
      (ι.shiftedResolventTransform_mul_one_add_smul (hinv t ht) (hinv' t ht) hc hc')
  rw [spectralFlow_congr heq]
  exact spectralFlow_mul_ringInverse_one_add_smul hab (hA.shiftedResolventTransform hinv)
    (fun t ht ↦ ι.isSelfAdjoint_shiftedResolventTransform (hsymm t ht))
    (fun t ht ↦ ι.isFredholm_shiftedResolventTransform hι hc (hinv t ht))
    (fun t ht ↦ by
      rw [RCLike.real_smul_eq_coe_smul (K := 𝕜) (E := H →L[𝕜] H) k]
      exact ι.isUnit_one_add_smul_shiftedResolventTransform (hinv' t ht))

end TauCeti
