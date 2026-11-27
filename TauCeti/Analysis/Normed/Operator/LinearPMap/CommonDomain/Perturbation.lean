/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible
import Mathlib.Analysis.Real.Cardinality
import TauCeti.Analysis.Fredholm.CompactPerturbation
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Basic
import TauCeti.Analysis.Normed.Operator.Compact.Basic
import TauCeti.Analysis.Normed.Operator.Compact.Interpolation

/-!
# Relatively compact symmetric perturbations over a compactly embedded domain

Let `ι : D →L H` be a compact operator from a Banach space `D` into a Hilbert space `H`. A bounded
operator `A : D →L H` with an invertible shift `c₀ • ι - A` is how an unbounded operator on `H`
with domain `range ι` and compact resolvent is given by a bounded operator on its domain, such as
the asymptotic operator `J₀ ∂ₜ + S` of the Floer equation with `D = H¹` and `H = L²`. This file
shows that this property survives perturbations which are *bounded through `ι`* and keep the
operator symmetric: if `B : D →L H` is symmetric through `ι`, `⟪B x, ι y⟫ = ⟪ι x, B y⟫`, and
`‖(B - A) x‖ ≤ C ‖ι x‖` for all `x`, then some real shift `c • ι - B` is invertible
(`ContinuousLinearMap.exists_isInvertible_ofReal_smul_sub_of_norm_sub_apply_le`). In the Floer
setting, changing the zeroth-order term `S` is such a perturbation. By
`ContinuousLinearMap.eventually_isInvertible_ofReal_smul_sub` the admissible real shifts of `B`
are then dense.

The proof has two steps.

* **The Fredholm alternative.** `B - A` is dominated by the compact operator `ι`, hence compact,
  so every shift `c • ι - B = (c₀ • ι - A) + ((c - c₀) • ι - (B - A))` is a compact perturbation
  of an invertible operator. It is therefore Fredholm of index zero, and invertible as soon as it
  is injective.
* **Countably many real eigenvalues.** A real `c` at which `c • ι - B` is not injective is a real
  eigenvalue of the pencil, `B x = c • ι x` for some `x ≠ 0`
  (`ContinuousLinearMap.countable_setOf_exists_ne_zero_apply_eq_ofReal_smul`). Since `B` is
  symmetric through `ι`, eigenvectors for distinct real eigenvalues have orthogonal images under
  `ι`, and these images are nonzero when `ι` is injective on the kernel of `B`. Normalized, they
  form an orthonormal family in the range of `ι`, which is separable since `ι` is compact
  (`IsCompactOperator.isSeparable_range`), so the family is countable
  (`Orthonormal.countable_of_separableSpace`). So there are only countably many real eigenvalues,
  and some real `c` is not one of them.

No symmetry of `A` and no injectivity of `ι` are needed: a vector `x ≠ 0` with `ι x = 0` is not
killed by `c₀ • ι - A`, so `A x ≠ 0`, and `(B - A) x = 0`, so `B x ≠ 0`.

## Main results

* `ContinuousLinearMap.countable_setOf_exists_ne_zero_apply_eq_ofReal_smul`: an operator symmetric
  through a compact `ι` has countably many real eigenvalues, when `ι` is injective on its kernel.
* `ContinuousLinearMap.exists_isInvertible_ofReal_smul_sub_of_norm_sub_apply_le`: a symmetric
  perturbation bounded through `ι` of an operator with an invertible shift has an invertible real
  shift.

## References

* T. Kato, *Perturbation Theory for Linear Operators*, Springer, 1995, Chapter IV (relatively
  compact perturbations and operators with compact resolvent).
* J. Robbin and D. Salamon, *The spectral flow and the Maslov index*, Bull. London Math. Soc.
  **27** (1995), 1–33, Section 4 (paths of self-adjoint operators on a compactly embedded common
  domain).
-/

public section

open Function

namespace ContinuousLinearMap

variable {𝕜 D H : Type*} [RCLike 𝕜] [NormedAddCommGroup D] [NormedSpace 𝕜 D]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] {ι A B : D →L[𝕜] H}

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- Eigenvectors of an operator symmetric through `ι` for distinct real eigenvalues have orthogonal
images under `ι`. -/
private theorem inner_eq_zero_of_apply_eq_ofReal_smul
    (hsymm : ∀ x y, ⟪B x, ι y⟫ = ⟪ι x, B y⟫) {c d : ℝ} (hcd : c ≠ d) {x y : D}
    (hx : B x = (c : 𝕜) • ι x) (hy : B y = (d : 𝕜) • ι y) : ⟪ι x, ι y⟫ = 0 := by
  have h := hsymm x y
  rw [hx, hy, inner_smul_left, inner_smul_right, RCLike.conj_ofReal] at h
  have hne : (c : 𝕜) - d ≠ 0 := sub_ne_zero.2 (RCLike.ofReal_injective.ne hcd)
  exact (mul_eq_zero.1 (by rw [sub_mul]; exact sub_eq_zero.2 h)).resolve_left hne

/-- **Countably many real eigenvalues.** Let `ι` be compact and `B` symmetric through `ι`,
`⟪B x, ι y⟫ = ⟪ι x, B y⟫`, with `ι` injective on the kernel of `B`. Then the real `c` for which
`B x = c • ι x` has a solution `x ≠ 0` form a countable set. -/
theorem countable_setOf_exists_ne_zero_apply_eq_ofReal_smul (hι : IsCompactOperator ι)
    (hsymm : ∀ x y, ⟪B x, ι y⟫ = ⟪ι x, B y⟫)
    (hker : Injective ((ι : D →ₗ[𝕜] H) ∘ₗ B.ker.subtype)) :
    {c : ℝ | ∃ x, x ≠ 0 ∧ B x = (c : 𝕜) • ι x}.Countable := by
  set S := {c : ℝ | ∃ x, x ≠ 0 ∧ B x = (c : 𝕜) • ι x}
  choose x hx0 hxB using fun c : S ↦ c.property
  -- The images of the eigenvectors are nonzero.
  have hιx (c : S) : ι (x c) ≠ 0 := fun h ↦ hx0 c <| by
    have hB : x c ∈ B.ker := by
      rw [LinearMap.mem_ker, coe_coe, hxB, h, smul_zero]
    simpa using congrArg Subtype.val (hker (a₁ := ⟨x c, hB⟩) (a₂ := 0) (by simpa using h))
  -- Normalized, they form an orthonormal family in the range of `ι`.
  set w : S → H := fun c ↦ ((‖ι (x c)‖⁻¹ : ℝ) : 𝕜) • ι (x c)
  have hw : Orthonormal 𝕜 w := by
    refine ⟨fun c ↦ ?_, fun c d hcd ↦ ?_⟩
    · simp only [w, norm_smul, RCLike.norm_ofReal, abs_inv, abs_norm]
      exact inv_mul_cancel₀ (norm_ne_zero_iff.2 (hιx c))
    · simp only [w, inner_smul_left, inner_smul_right,
        inner_eq_zero_of_apply_eq_ofReal_smul hsymm (Subtype.coe_injective.ne hcd) (hxB c)
          (hxB d), mul_zero]
  have hmem (c : S) : w c ∈ LinearMap.range (ι : D →ₗ[𝕜] H) :=
    ⟨((‖ι (x c)‖⁻¹ : ℝ) : 𝕜) • x c, map_smul _ _ _⟩
  -- The range of `ι` is separable, so the family is countable.
  have : TopologicalSpace.SeparableSpace (LinearMap.range (ι : D →ₗ[𝕜] H)) := by
    have h := hι.isSeparable_range (f := (ι : D →ₗ[𝕜] H))
    rw [← LinearMap.coe_range] at h
    exact h.separableSpace
  exact Set.countable_coe_iff.1 ((hw.codRestrict _ hmem).countable_of_separableSpace)

variable [CompleteSpace D] [CompleteSpace H] {c₀ : 𝕜}

/-- **Relatively compact symmetric perturbations keep an invertible real shift.** Let `ι` be
compact and `A` an operator with an invertible shift `c₀ • ι - A`. If `B` is symmetric through `ι`,
`⟪B x, ι y⟫ = ⟪ι x, B y⟫`, and `B - A` is bounded through `ι`, `‖(B - A) x‖ ≤ C ‖ι x‖`, then some
real shift `c • ι - B` is invertible. -/
theorem exists_isInvertible_ofReal_smul_sub_of_norm_sub_apply_le (hι : IsCompactOperator ι)
    (h₀ : (c₀ • ι - A).IsInvertible) (hsymm : ∀ x y, ⟪B x, ι y⟫ = ⟪ι x, B y⟫) {C : ℝ}
    (hBA : ∀ x, ‖(B - A) x‖ ≤ C * ‖ι x‖) : ∃ c : ℝ, ((c : 𝕜) • ι - B).IsInvertible := by
  -- `B - A` is dominated by `ι`, hence compact.
  have hK : IsCompactOperator (B - A) :=
    hι.of_norm_le_mul_norm (T₀ := (ι : D →ₗ[𝕜] H)) (T := ((B - A : D →L[𝕜] H) : D →ₗ[𝕜] H)) hBA
  -- `ι` is injective on the kernel of `B`, where `B` agrees with `A` and `c₀ • ι - A` with `-A`.
  have hker : Injective ((ι : D →ₗ[𝕜] H) ∘ₗ B.ker.subtype) := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    rintro ⟨x, hx⟩ hιx
    replace hx : B x = 0 := LinearMap.mem_ker.1 hx
    replace hιx : ι x = 0 := by simpa using hιx
    have hAx : A x = 0 := by simpa [hιx, hx] using hBA x
    have : x = 0 := h₀.injective (by simp [hιx, hAx])
    simp [this]
  -- Some real `c` is not an eigenvalue, since there are only countably many.
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c ∉ {c : ℝ | ∃ x, x ≠ 0 ∧ B x = (c : 𝕜) • ι x} := by
    by_contra! h
    exact Set.not_countable_univ
      ((countable_setOf_exists_ne_zero_apply_eq_ofReal_smul hι hsymm hker).mono fun c _ ↦ h c)
  -- The shift at `c` is a compact perturbation of `c₀ • ι - A`, so Fredholm of index zero.
  have hdecomp : (c : 𝕜) • ι - B = (c₀ • ι - A) + (((c : 𝕜) - c₀) • ι - (B - A)) := by
    rw [sub_smul]
    abel
  have hcpt : IsCompactOperator ⇑(((c : 𝕜) - c₀) • ι - (B - A)) := (hι.smul _).sub hK
  have hF : ((c : 𝕜) • ι - B).IsFredholm := by
    rw [hdecomp]
    exact h₀.isFredholm.add_of_isCompactOperator hcpt
  have hindex : ((c : 𝕜) • ι - B).index = 0 := by
    rw [hdecomp, index_add_of_isCompactOperator h₀.isFredholm hcpt]
    exact index_eq_zero_of_bijective _ h₀.bijective
  refine ⟨c, hF.isInvertible_of_injective_of_index_eq_zero ?_ hindex⟩
  rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra hx0
  refine hc ⟨x, hx0, ?_⟩
  rw [sub_apply, sub_eq_zero, smul_apply] at hx
  exact hx.symm

end ContinuousLinearMap
