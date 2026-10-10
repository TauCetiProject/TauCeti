/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.SingularValues

/-!
# The Moore–Penrose inverse

For linear maps `A : E → F` and `B : F → E` between inner product spaces, `B` is a
*Moore–Penrose inverse* of `A` when the four Penrose conditions hold:

```text
A B A = A     B A B = B     A B is symmetric     B A is symmetric
```

Here symmetric means `LinearMap.IsSymmetric`, that is `⟪A B x, y⟫ = ⟪x, A B y⟫` for all `x` and
`y`, which makes sense without assuming that adjoints exist. When the spaces are
finite-dimensional, the last two conditions are the usual Penrose equations `(A B)† = A B` and
`(B A)† = B A`. The symmetric idempotents `A B` and `B A` are the orthogonal projections onto the
ranges of `A` and of `B`.
This file records the relation as the predicate `LinearMap.IsMoorePenroseInverse`, shows that it
determines `B` uniquely, that it is symmetric in `A` and `B`, and that it is compatible with
adjoints. For maps between finite-dimensional spaces, `LinearMap.moorePenroseInverse A` is the
singular-system construction

`A⁺ y = ∑ᵢ σᵢ⁻² ⟪A vᵢ, y⟫ vᵢ = ∑ᵢ σᵢ⁻¹ ⟪uᵢ, y⟫ vᵢ`,

where `(vᵢ) = A.rightSingularBasis` is the ordered orthonormal eigenbasis of `A† A`, `σᵢ` are the
singular values of `A`, and `uᵢ = σᵢ⁻¹ A vᵢ = A.leftSingularVector i` are the left singular
vectors. In words, `A⁺` inverts each nonzero singular
value and sends the zero ones to zero. Every Moore–Penrose inverse of `A` equals `A⁺`.

The relation reduces to familiar one-sided inverses in the injective, surjective, and invertible
cases: `A⁺ A = 1` for injective `A`, `A A⁺ = 1` for surjective `A`, and `A⁺ = A⁻¹` for a linear
equivalence.

## Main definitions

* `LinearMap.IsMoorePenroseInverse A B`: the four Penrose conditions.
* `LinearMap.moorePenroseInverse A`: the Moore–Penrose inverse of a map between
  finite-dimensional inner product spaces, built from its singular system.

## Main statements

* `LinearMap.IsMoorePenroseInverse.unique`: Moore–Penrose inverses are unique. This holds in
  arbitrary inner product spaces.
* `LinearMap.isMoorePenroseInverse_adjoint_iff`: `B` is a Moore–Penrose inverse of `A` if and
  only if `B†` is one of `A†`.
* `LinearMap.isMoorePenroseInverse_moorePenroseInverse`: the singular-system construction
  satisfies the Penrose equations.
* `LinearMap.isMoorePenroseInverse_iff_eq_moorePenroseInverse`: the Penrose equations
  characterize `A⁺`.

## References

* R. Penrose, *A generalized inverse for matrices*, Proc. Cambridge Philos. Soc. **51** (1955),
  406–413.
* A. Ben-Israel, T. N. E. Greville, *Generalized Inverses: Theory and Applications*, 2nd ed.,
  CMS Books in Mathematics, Springer (2003), Chapter 1.
-/

public section

open Module InnerProductSpace

namespace LinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

section Seminormed

variable [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [SeminormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- `IsMoorePenroseInverse A B` states that `B` is a Moore–Penrose inverse of `A`: the four
Penrose conditions hold, namely `A B A = A`, `B A B = B`, and the compositions `A B` and `B A`
are symmetric in the sense of `LinearMap.IsSymmetric`. In finite dimension the last two
conditions are the adjoint equations `(A B)† = A B` and `(B A)† = B A`. -/
structure IsMoorePenroseInverse (A : E →ₗ[𝕜] F) (B : F →ₗ[𝕜] E) : Prop where
  /-- `B` is a generalized inverse of `A`. -/
  comp_comp_self : A ∘ₗ B ∘ₗ A = A
  /-- `A` is a generalized inverse of `B`. -/
  comp_comp_self' : B ∘ₗ A ∘ₗ B = B
  /-- The idempotent `A B` onto the range of `A` is symmetric. -/
  isSymmetric_comp : (A ∘ₗ B).IsSymmetric
  /-- The idempotent `B A` onto the range of `B` is symmetric. -/
  isSymmetric_comp' : (B ∘ₗ A).IsSymmetric

namespace IsMoorePenroseInverse

variable {A : E →ₗ[𝕜] F} {B C : F →ₗ[𝕜] E}

/-- Pointwise form of `A B A = A`. -/
theorem apply_apply_apply (h : IsMoorePenroseInverse A B) (x : E) : A (B (A x)) = A x :=
  LinearMap.congr_fun h.comp_comp_self x

/-- Pointwise form of `B A B = B`. -/
theorem apply_apply_apply' (h : IsMoorePenroseInverse A B) (y : F) : B (A (B y)) = B y :=
  LinearMap.congr_fun h.comp_comp_self' y

/-- The Moore–Penrose relation is symmetric: if `B` is a Moore–Penrose inverse of `A`, then `A`
is a Moore–Penrose inverse of `B`. -/
protected theorem symm (h : IsMoorePenroseInverse A B) : IsMoorePenroseInverse B A :=
  ⟨h.comp_comp_self', h.comp_comp_self, h.isSymmetric_comp', h.isSymmetric_comp⟩

/-- If `A` is injective, a Moore–Penrose inverse of `A` is a left inverse. -/
theorem comp_eq_id_of_injective (h : IsMoorePenroseInverse A B) (hA : Function.Injective A) :
    B ∘ₗ A = .id :=
  LinearMap.ext fun x ↦ hA (h.apply_apply_apply x)

/-- If `A` is surjective, a Moore–Penrose inverse of `A` is a right inverse. -/
theorem comp_eq_id_of_surjective (h : IsMoorePenroseInverse A B) (hA : Function.Surjective A) :
    A ∘ₗ B = .id :=
  LinearMap.ext fun y ↦ by
    obtain ⟨x, rfl⟩ := hA y
    exact h.apply_apply_apply x

/-- A two-sided inverse is a Moore–Penrose inverse. -/
theorem of_comp_eq_id (hBA : B ∘ₗ A = .id) (hAB : A ∘ₗ B = .id) :
    IsMoorePenroseInverse A B where
  comp_comp_self := by rw [hBA, comp_id]
  comp_comp_self' := by rw [hAB, comp_id]
  isSymmetric_comp := hAB ▸ IsSymmetric.id
  isSymmetric_comp' := hBA ▸ IsSymmetric.id

end IsMoorePenroseInverse

/-- The Moore–Penrose relation is symmetric in its two arguments. -/
theorem isMoorePenroseInverse_comm {A : E →ₗ[𝕜] F} {B : F →ₗ[𝕜] E} :
    IsMoorePenroseInverse A B ↔ IsMoorePenroseInverse B A :=
  ⟨.symm, .symm⟩

/-- The zero map is its own Moore–Penrose inverse. -/
@[simp]
theorem isMoorePenroseInverse_zero : IsMoorePenroseInverse (0 : E →ₗ[𝕜] F) 0 :=
  ⟨by simp, by simp, by simp, by simp⟩

/-- A linear equivalence and its inverse are Moore–Penrose inverses of each other. -/
@[simp]
theorem _root_.LinearEquiv.isMoorePenroseInverse (e : E ≃ₗ[𝕜] F) :
    IsMoorePenroseInverse (e : E →ₗ[𝕜] F) e.symm :=
  .of_comp_eq_id e.symm_comp e.comp_symm

end Seminormed

variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

namespace IsMoorePenroseInverse

variable {A : E →ₗ[𝕜] F} {B C : F →ₗ[𝕜] E}

/-- **Uniqueness of the Moore–Penrose inverse.** A linear map between inner product spaces has
at most one Moore–Penrose inverse. -/
theorem unique (hB : IsMoorePenroseInverse A B) (hC : IsMoorePenroseInverse A C) : B = C := by
  -- The symmetric idempotents `A B` and `A C` absorb each other, so they agree.
  have hAB : A ∘ₗ B = A ∘ₗ C := LinearMap.ext fun x ↦ ext_inner_right 𝕜 fun y ↦ by
    calc ⟪A (B x), y⟫ = ⟪A (C (A (B x))), y⟫ := by rw [hC.apply_apply_apply]
      _ = ⟪x, A (B (A (C y)))⟫ :=
        (hC.isSymmetric_comp (A (B x)) y).trans (hB.isSymmetric_comp x (A (C y)))
      _ = ⟪A (C x), y⟫ := by rw [hB.apply_apply_apply]; exact (hC.isSymmetric_comp x y).symm
  -- Likewise for the symmetric idempotents `B A` and `C A`.
  have hBA : B ∘ₗ A = C ∘ₗ A := LinearMap.ext fun x ↦ ext_inner_right 𝕜 fun y ↦ by
    calc ⟪B (A x), y⟫ = ⟪B (A (C (A x))), y⟫ := by rw [hC.apply_apply_apply]
      _ = ⟪x, C (A (B (A y)))⟫ :=
        (hB.isSymmetric_comp' (C (A x)) y).trans (hC.isSymmetric_comp' x (B (A y)))
      _ = ⟪C (A x), y⟫ := by rw [hB.apply_apply_apply]; exact (hC.isSymmetric_comp' x y).symm
  refine LinearMap.ext fun y ↦ ?_
  rw [← hB.apply_apply_apply' y, ← hC.apply_apply_apply' y]
  exact (LinearMap.congr_fun hBA (B y)).trans (congrArg C (LinearMap.congr_fun hAB y))

/-- The Moore–Penrose relation is compatible with adjoints: if `B` is a Moore–Penrose inverse of
`A`, then `B†` is a Moore–Penrose inverse of `A†`. -/
protected theorem adjoint [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    (h : IsMoorePenroseInverse A B) : IsMoorePenroseInverse A.adjoint B.adjoint where
  comp_comp_self := by rw [← adjoint_comp, ← adjoint_comp, comp_assoc, h.comp_comp_self]
  comp_comp_self' := by rw [← adjoint_comp, ← adjoint_comp, comp_assoc, h.comp_comp_self']
  isSymmetric_comp := by
    rw [← adjoint_comp, h.isSymmetric_comp'.adjoint_eq]
    exact h.isSymmetric_comp'
  isSymmetric_comp' := by
    rw [← adjoint_comp, h.isSymmetric_comp.adjoint_eq]
    exact h.isSymmetric_comp

end IsMoorePenroseInverse

/-- `B` is a Moore–Penrose inverse of `A` if and only if `B†` is a Moore–Penrose inverse
of `A†`. -/
theorem isMoorePenroseInverse_adjoint_iff [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    {A : E →ₗ[𝕜] F} {B : F →ₗ[𝕜] E} :
    IsMoorePenroseInverse A.adjoint B.adjoint ↔ IsMoorePenroseInverse A B :=
  ⟨fun h ↦ by simpa using h.adjoint, .adjoint⟩

/-! ### The singular-system construction -/

section Construction

variable [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]

/-- The **Moore–Penrose inverse** of a linear map `A` between finite-dimensional inner product
spaces: `A⁺ y = ∑ᵢ σᵢ⁻² ⟪A vᵢ, y⟫ vᵢ`, where `(vᵢ)` is the right singular basis of `A`
(the ordered orthonormal eigenbasis of `A† A`) and `σᵢ` are the singular values of `A`. Indices
with `σᵢ = 0` contribute nothing. -/
noncomputable def moorePenroseInverse (A : E →ₗ[𝕜] F) : F →ₗ[𝕜] E :=
  ∑ i : Fin (finrank 𝕜 E), ((A.singularValues i ^ 2 : ℝ) : 𝕜)⁻¹ •
    (rankOne 𝕜 (A.rightSingularBasis i) (A (A.rightSingularBasis i))).toLinearMap

/-- The singular expansion of `A⁺ y`. -/
theorem moorePenroseInverse_apply (A : E →ₗ[𝕜] F) (y : F) :
    A.moorePenroseInverse y = ∑ i : Fin (finrank 𝕜 E), ((A.singularValues i ^ 2 : ℝ) : 𝕜)⁻¹ •
      ⟪A (A.rightSingularBasis i), y⟫ • A.rightSingularBasis i := by
  simp [moorePenroseInverse]

variable (A : E →ₗ[𝕜] F)

private theorem moorePenroseInverse_apply_apply (x : E) :
    A.moorePenroseInverse (A x) = ∑ i : Fin (finrank 𝕜 E),
      (((A.singularValues i ^ 2 : ℝ) : 𝕜)⁻¹ * ((A.singularValues i ^ 2 : ℝ) : 𝕜)) •
        ⟪A.rightSingularBasis i, x⟫ • A.rightSingularBasis i := by
  simp only [moorePenroseInverse_apply, inner_apply_rightSingularBasis, mul_smul]

/-- The singular-system construction `A⁺` is a Moore–Penrose inverse of `A`. -/
@[simp]
theorem isMoorePenroseInverse_moorePenroseInverse :
    IsMoorePenroseInverse A A.moorePenroseInverse where
  comp_comp_self := LinearMap.ext fun x ↦ by
    set v := A.rightSingularBasis
    conv_rhs => rw [← v.sum_repr' x]
    simp only [comp_apply, moorePenroseInverse_apply_apply, map_sum, map_smul]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [smul_comm, inv_mul_smul_apply_rightSingularBasis]
  comp_comp_self' := LinearMap.ext fun y ↦ by
    set v := A.rightSingularBasis
    rw [comp_apply, comp_apply, moorePenroseInverse_apply_apply, moorePenroseInverse_apply]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp_rw [← mul_smul]
    rw [v.orthonormal.inner_right_fintype, ← mul_assoc]
    generalize ((A.singularValues i ^ 2 : ℝ) : 𝕜) = c
    rcases eq_or_ne c 0 with rfl | hc
    · simp
    · rw [inv_mul_cancel₀ hc, one_mul]
  isSymmetric_comp := by
    have : A ∘ₗ A.moorePenroseInverse = ∑ i : Fin (finrank 𝕜 E),
        ((A.singularValues i ^ 2 : ℝ) : 𝕜)⁻¹ •
          (rankOne 𝕜 (A (A.rightSingularBasis i)) (A (A.rightSingularBasis i))).toLinearMap := by
      ext y
      simp [moorePenroseInverse_apply]
    rw [this]
    exact isSymmetric_sum _ fun i _ ↦ (isSymmetric_rankOne_self _).smul (by simp)
  isSymmetric_comp' := by
    have : A.moorePenroseInverse ∘ₗ A = ∑ i : Fin (finrank 𝕜 E),
        (((A.singularValues i ^ 2 : ℝ) : 𝕜)⁻¹ * ((A.singularValues i ^ 2 : ℝ) : 𝕜)) •
          (rankOne 𝕜 (A.rightSingularBasis i) (A.rightSingularBasis i)).toLinearMap := by
      ext x
      simp [moorePenroseInverse_apply_apply]
    rw [this]
    exact isSymmetric_sum _ fun i _ ↦ (isSymmetric_rankOne_self _).smul (by simp)

/-- **Characterization of the Moore–Penrose inverse.** A map satisfies the four Penrose
equations for `A` if and only if it is `A⁺`. -/
theorem isMoorePenroseInverse_iff_eq_moorePenroseInverse {B : F →ₗ[𝕜] E} :
    IsMoorePenroseInverse A B ↔ B = A.moorePenroseInverse :=
  ⟨fun h ↦ h.unique A.isMoorePenroseInverse_moorePenroseInverse,
    fun h ↦ h ▸ A.isMoorePenroseInverse_moorePenroseInverse⟩

/-- The Moore–Penrose inverse of an injective map is a left inverse. -/
theorem moorePenroseInverse_comp_of_injective (hA : Function.Injective A) :
    A.moorePenroseInverse ∘ₗ A = .id :=
  A.isMoorePenroseInverse_moorePenroseInverse.comp_eq_id_of_injective hA

/-- The Moore–Penrose inverse of a surjective map is a right inverse. -/
theorem comp_moorePenroseInverse_of_surjective (hA : Function.Surjective A) :
    A ∘ₗ A.moorePenroseInverse = .id :=
  A.isMoorePenroseInverse_moorePenroseInverse.comp_eq_id_of_surjective hA

/-- The Moore–Penrose inverse of a linear equivalence is its inverse. -/
@[simp]
theorem _root_.LinearEquiv.moorePenroseInverse_eq_symm (e : E ≃ₗ[𝕜] F) :
    (e : E →ₗ[𝕜] F).moorePenroseInverse = e.symm :=
  ((isMoorePenroseInverse_iff_eq_moorePenroseInverse _).mp e.isMoorePenroseInverse).symm

/-- The Moore–Penrose inverse is involutive: `(A⁺)⁺ = A`. -/
@[simp]
theorem moorePenroseInverse_moorePenroseInverse :
    A.moorePenroseInverse.moorePenroseInverse = A :=
  ((isMoorePenroseInverse_iff_eq_moorePenroseInverse _).mp
    A.isMoorePenroseInverse_moorePenroseInverse.symm).symm

/-- The Moore–Penrose inverse commutes with adjoints: `(A†)⁺ = (A⁺)†`. -/
@[simp]
theorem moorePenroseInverse_adjoint :
    A.adjoint.moorePenroseInverse = A.moorePenroseInverse.adjoint :=
  ((isMoorePenroseInverse_iff_eq_moorePenroseInverse _).mp
    A.isMoorePenroseInverse_moorePenroseInverse.adjoint).symm

/-- The Moore–Penrose inverse of the zero map is zero. -/
@[simp]
theorem moorePenroseInverse_zero : (0 : E →ₗ[𝕜] F).moorePenroseInverse = 0 :=
  ((isMoorePenroseInverse_iff_eq_moorePenroseInverse _).mp isMoorePenroseInverse_zero).symm

end Construction

end LinearMap
