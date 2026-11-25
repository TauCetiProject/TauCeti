/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.ContinuousFunctionalCalculus
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.AdjointComp
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.Resolvent
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import TauCeti.Analysis.InnerProductSpace.LinearPMap.Constructions
import TauCeti.LinearAlgebra.LinearPMap.Basic
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.RealAlgebra
import TauCeti.Topology.Algebra.Module.LinearPMap.Resolvent.Inverse

/-!
# Positive square roots of nonnegative self-adjoint partial linear maps

Let `A : E →ₗ.[𝕜] E` be a self-adjoint partial linear map on a Hilbert space `E` over `RCLike 𝕜`
whose quadratic form is nonnegative: `0 ≤ re ⟪A x, x⟫` for every `x : A.domain`. Every scalar in
the open left half-plane `re z < 0` then lies in the resolvent set of `A`; in particular `-1` is a
resolvent point, and `B = -R(-1, A) = (1 + A)⁻¹` is an injective bounded operator satisfying
`0 ≤ B ≤ 1` in the Loewner order.

Using the continuous functional calculus on `E →L[𝕜] E`, let `S = √B` and `C = √(1 - B)`. Since
`B` is injective, so is `S`; on `range S`, setting `A.sqrt (S z) = C z` defines a partial linear
map `A.sqrt : E →ₗ.[𝕜] E`, equivalently `C ∘ S⁻¹`. Geometrically `S² + C² = 1` with `S, C ≥ 0`
commuting, so `S + C` is bounded below by `1` and hence surjective, making `-1` a surjective shift
of the symmetric operator `A.sqrt`. This gives self-adjointness and dense domain of `A.sqrt`,
positivity of its quadratic form, the identity `(A.sqrt)† (A.sqrt) = A` on maximal domain, that
`A.domain` is a graph core for `A.sqrt`, and uniqueness among nonnegative self-adjoint partial
operators.

No complexification is needed at the unbounded level: the resolvent at `-1` and the real continuous
functional calculus from `TauCeti.Analysis.InnerProductSpace.ContinuousFunctionalCalculus` work
uniformly over every `RCLike 𝕜`.

## Main declarations

* `LinearPMap.sqrt`: the positive square root `A^(1/2)` of a nonnegative self-adjoint partial map.
* `IsSelfAdjoint.isSelfAdjoint_sqrt`, `IsSelfAdjoint.dense_sqrt_domain`,
  `IsSelfAdjoint.re_inner_sqrt_nonneg`: `A.sqrt` is self-adjoint, densely defined, and nonnegative.
* `IsSelfAdjoint.sqrt_adjointComp`: `(A.sqrt).adjointComp = A`.
* `IsSelfAdjoint.domain_le_sqrt_domain`, `IsSelfAdjoint.sqrt_hasCore_domain`: `A.domain` sits
  inside `A.sqrt.domain` as a graph core for `A.sqrt`.
* `IsSelfAdjoint.eq_sqrt`, `IsSelfAdjoint.eq_sqrt_iff`: uniqueness of the positive square root.
* `LinearPMap.sqrt_zero`, `ContinuousLinearMap.IsPositive.toPMap_top_sqrt`: compatibility with `0`
  and with bounded positive operators on `⊤`.

## References

* T. Kato, *Perturbation Theory for Linear Operators*, Springer (1995), §V.3.11.
* M. Reed, B. Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*, Academic
  Press (1980), §VIII.7.
* W. Rudin, *Functional Analysis*, 2nd ed., McGraw-Hill (1991), Theorem 13.31.
-/

public section

noncomputable section

open InnerProductSpace
open scoped LinearPMap NNReal

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

namespace LinearPMap

section Sqrt

variable [CompleteSpace E]

attribute [local instance] ContinuousLinearMap.realAlgebra ContinuousLinearMap.realIsScalarTower

/-- The bounded inverse `(1 + A)⁻¹ = -R(-1, A)` associated with a partial operator `A`. -/
private def sqrtB (A : E →ₗ.[𝕜] E) : E →L[𝕜] E := -A.resolvent (-1)

/-- The bounded positive operator `S = √((1 + A)⁻¹)`. -/
private def sqrtS (A : E →ₗ.[𝕜] E) : E →L[𝕜] E := CFC.sqrt (sqrtB A)

/-- The bounded positive operator `C = √(1 - (1 + A)⁻¹)`. -/
private def sqrtC (A : E →ₗ.[𝕜] E) : E →L[𝕜] E := CFC.sqrt (1 - sqrtB A)

/-- The **positive square root** `A^(1/2)` of a nonnegative self-adjoint partial linear map `A`,
defined as `C ∘ S⁻¹` where `B = -R(-1, A) = (1 + A)⁻¹`, `S = √B`, and `C = √(1 - B)`.

Off nonnegative self-adjoint operators its value is an unspecified partial linear map; all API
lemmas carry `IsSelfAdjoint A` and `∀ x : A.domain, 0 ≤ RCLike.re ⟪A x, (x : E)⟫`. -/
def sqrt (A : E →ₗ.[𝕜] E) : E →ₗ.[𝕜] E :=
  (sqrtC A : E →ₗ[𝕜] E).compPMap ((sqrtS A : E →ₗ[𝕜] E).toPMap ⊤).inverse

section Helpers

variable {A : E →ₗ.[𝕜] E}

private theorem neg_one_mem_resolventSet (hA : IsSelfAdjoint A)
    (hpos : ∀ x : A.domain, 0 ≤ RCLike.re ⟪A x, (x : E)⟫) : (-1 : 𝕜) ∈ A.resolventSet :=
  hA.mem_resolventSet_of_re_lt (γ := 0) (by simpa using hpos) (by simp)

private theorem sqrtB_mem_domain (hA : IsSelfAdjoint A)
    (hpos : ∀ x : A.domain, 0 ≤ RCLike.re ⟪A x, (x : E)⟫) (y : E) :
    sqrtB A y ∈ A.domain := by
  rw [sqrtB, _root_.neg_apply]
  exact A.domain.neg_mem (resolvent_mem_domain (neg_one_mem_resolventSet hA hpos) y)

private theorem add_apply_sqrtB (hA : IsSelfAdjoint A)
    (hpos : ∀ x : A.domain, 0 ≤ RCLike.re ⟪A x, (x : E)⟫) (y : E) :
    sqrtB A y + A ⟨sqrtB A y, sqrtB_mem_domain hA hpos y⟩ = y := by
  have h := smul_sub_apply_resolvent (neg_one_mem_resolventSet hA hpos) y
  have hdom : (⟨sqrtB A y, sqrtB_mem_domain hA hpos y⟩ : A.domain) =
      -⟨A.resolvent (-1) y, resolvent_mem_domain (neg_one_mem_resolventSet hA hpos) y⟩ :=
    Subtype.ext rfl
  rw [hdom, map_neg, sqrtB, _root_.neg_apply]
  simpa only [neg_one_smul, sub_eq_add_neg] using h

private theorem one_sub_sqrtB_apply (hA : IsSelfAdjoint A)
    (hpos : ∀ x : A.domain, 0 ≤ RCLike.re ⟪A x, (x : E)⟫) (y : E) :
    (1 - sqrtB A) y = A ⟨sqrtB A y, sqrtB_mem_domain hA hpos y⟩ := by
  rw [_root_.sub_apply, one_apply_eq_self]
  exact sub_eq_of_eq_add' (add_apply_sqrtB hA hpos y).symm

private theorem sqrtB_add_apply (hA : IsSelfAdjoint A)
    (hpos : ∀ x : A.domain, 0 ≤ RCLike.re ⟪A x, (x : E)⟫) (x : A.domain) :
    sqrtB A ((x : E) + A x) = (x : E) := by
  have h := resolvent_smul_sub_apply (neg_one_mem_resolventSet hA hpos) x
  have harg : (x : E) + A x = -((-1 : 𝕜) • (x : E) - A x) := by simp [add_comm]
  rw [sqrtB, _root_.neg_apply, harg, _root_.map_neg, h, neg_neg]

private theorem sqrtB_injective (hA : IsSelfAdjoint A)
    (hpos : ∀ x : A.domain, 0 ≤ RCLike.re ⟪A x, (x : E)⟫) :
    Function.Injective (sqrtB A) := by
  intro y₁ y₂ h
  have hsub : sqrtB A (y₁ - y₂) = 0 := by rw [_root_.map_sub, h, sub_self]
  have hid := add_apply_sqrtB hA hpos (y₁ - y₂)
  have hzero : (⟨sqrtB A (y₁ - y₂), sqrtB_mem_domain hA hpos (y₁ - y₂)⟩ : A.domain) = 0 :=
    Subtype.ext hsub
  rw [hzero, hsub, map_zero, add_zero] at hid
  exact sub_eq_zero.mp hid.symm

private theorem isSelfAdjoint_sqrtB (hA : IsSelfAdjoint A)
    (hpos : ∀ x : A.domain, 0 ≤ RCLike.re ⟪A x, (x : E)⟫) :
    IsSelfAdjoint (sqrtB A) :=
  (hA.isSelfAdjoint_resolvent (neg_one_mem_resolventSet hA hpos) (by simp)).neg

private theorem sqrtB_nonneg (hA : IsSelfAdjoint A)
    (hpos : ∀ x : A.domain, 0 ≤ RCLike.re ⟪A x, (x : E)⟫) : 0 ≤ sqrtB A := by
  rw [ContinuousLinearMap.nonneg_iff_isPositive, ContinuousLinearMap.isPositive_def]
  refine ⟨(isSelfAdjoint_sqrtB hA hpos).isSymmetric, fun y ↦ ?_⟩
  rw [ContinuousLinearMap.reApplyInnerSelf_apply]
  let u : A.domain := ⟨sqrtB A y, sqrtB_mem_domain hA hpos y⟩
  have hu : sqrtB A y = (u : E) := rfl
  have hy : y = (u : E) + A u := (add_apply_sqrtB hA hpos y).symm
  rw [hu, hy, inner_add_right, _root_.map_add, inner_re_symm (u : E) (A u)]
  exact add_nonneg inner_self_nonneg (hpos u)

private theorem one_sub_sqrtB_nonneg (hA : IsSelfAdjoint A)
    (hpos : ∀ x : A.domain, 0 ≤ RCLike.re ⟪A x, (x : E)⟫) : 0 ≤ 1 - sqrtB A := by
  rw [ContinuousLinearMap.nonneg_iff_isPositive, ContinuousLinearMap.isPositive_def]
  refine ⟨((IsSelfAdjoint.one (E →L[𝕜] E)).sub (isSelfAdjoint_sqrtB hA hpos)).isSymmetric,
    fun y ↦ ?_⟩
  rw [ContinuousLinearMap.reApplyInnerSelf_apply]
  let u : A.domain := ⟨sqrtB A y, sqrtB_mem_domain hA hpos y⟩
  have h1 : (1 - sqrtB A) y = A u := one_sub_sqrtB_apply hA hpos y
  have hy : y = (u : E) + A u := (add_apply_sqrtB hA hpos y).symm
  rw [h1, hy, inner_add_right, _root_.map_add]
  exact add_nonneg (hpos u) inner_self_nonneg

private theorem sqrtS_nonneg : 0 ≤ sqrtS A := CFC.sqrt_nonneg _

private theorem sqrtC_nonneg : 0 ≤ sqrtC A := CFC.sqrt_nonneg _

private theorem isPositive_sqrtS : (sqrtS A).IsPositive :=
  ContinuousLinearMap.nonneg_iff_isPositive.mp sqrtS_nonneg

private theorem isPositive_sqrtC : (sqrtC A).IsPositive :=
  ContinuousLinearMap.nonneg_iff_isPositive.mp sqrtC_nonneg

private theorem isSelfAdjoint_sqrtS : IsSelfAdjoint (sqrtS A) :=
  isPositive_sqrtS.isSelfAdjoint

private theorem isSelfAdjoint_sqrtC : IsSelfAdjoint (sqrtC A) :=
  isPositive_sqrtC.isSelfAdjoint

private theorem sqrtS_mul_self (hA : IsSelfAdjoint A)
    (hpos : ∀ x : A.domain, 0 ≤ RCLike.re ⟪A x, (x : E)⟫) :
    sqrtS A * sqrtS A = sqrtB A :=
  CFC.sqrt_mul_sqrt_self _ (sqrtB_nonneg hA hpos)

private theorem sqrtC_mul_self (hA : IsSelfAdjoint A)
    (hpos : ∀ x : A.domain, 0 ≤ RCLike.re ⟪A x, (x : E)⟫) :
    sqrtC A * sqrtC A = 1 - sqrtB A :=
  CFC.sqrt_mul_sqrt_self _ (one_sub_sqrtB_nonneg hA hpos)

private theorem commute_sqrtS_sqrtC : Commute (sqrtS A) (sqrtC A) := by
  have hB : Commute (sqrtB A) (1 - sqrtB A) :=
    (Commute.one_right (sqrtB A)).sub_right (Commute.refl _)
  have h1 : Commute (sqrtS A) (1 - sqrtB A) := hB.cfcₙ_nnreal NNReal.sqrt
  exact (h1.symm.cfcₙ_nnreal NNReal.sqrt).symm

private theorem sqrtS_injective (hA : IsSelfAdjoint A)
    (hpos : ∀ x : A.domain, 0 ≤ RCLike.re ⟪A x, (x : E)⟫) :
    Function.Injective (sqrtS A) := by
  intro y₁ y₂ h
  apply sqrtB_injective hA hpos
  have hmul := sqrtS_mul_self hA hpos
  calc sqrtB A y₁ = (sqrtS A * sqrtS A) y₁ := by rw [hmul]
    _ = sqrtS A (sqrtS A y₁) := rfl
    _ = sqrtS A (sqrtS A y₂) := by rw [h]
    _ = (sqrtS A * sqrtS A) y₂ := rfl
    _ = sqrtB A y₂ := by rw [hmul]

private theorem mem_sqrt_domain_iff {x : E} :
    x ∈ A.sqrt.domain ↔ ∃ z, sqrtS A z = x :=
  ContinuousLinearMap.mem_domain_inverse_toPMap_top_iff (sqrtS A)

private theorem sqrtS_mem_sqrt_domain (z : E) : sqrtS A z ∈ A.sqrt.domain :=
  ContinuousLinearMap.apply_mem_domain_inverse_toPMap_top (sqrtS A) z

private theorem sqrt_apply_sqrtS (hA : IsSelfAdjoint A)
    (hpos : ∀ x : A.domain, 0 ≤ RCLike.re ⟪A x, (x : E)⟫) (z : E) :
    A.sqrt ⟨sqrtS A z, sqrtS_mem_sqrt_domain z⟩ = sqrtC A z := by
  -- Unfold `A.sqrt` and `compPMap` simultaneously so the subtype membership proof aligns.
  change sqrtC A (((sqrtS A : E →ₗ[𝕜] E).toPMap ⊤).inverse
      ⟨sqrtS A z, ContinuousLinearMap.apply_mem_domain_inverse_toPMap_top (sqrtS A) z⟩) = sqrtC A z
  rw [ContinuousLinearMap.inverse_toPMap_top_apply (sqrtS A) (sqrtS_injective hA hpos)]

private theorem sqrt_apply_sqrtS_sqrtS (hA : IsSelfAdjoint A)
    (hpos : ∀ x : A.domain, 0 ≤ RCLike.re ⟪A x, (x : E)⟫) {u : A.sqrt.domain} {z : E}
    (hu : sqrtS A (sqrtS A z) = (u : E)) :
    A.sqrt u = sqrtS A (sqrtC A z) := by
  have hsub : u = ⟨sqrtS A (sqrtS A z), sqrtS_mem_sqrt_domain _⟩ := Subtype.ext hu.symm
  rw [hsub, sqrt_apply_sqrtS hA hpos, ← mul_apply_eq_comp,
    commute_sqrtS_sqrtC.symm.eq, mul_apply_eq_comp]

private theorem re_inner_sqrtC_sqrtS_nonneg (z : E) :
    0 ≤ RCLike.re ⟪sqrtC A z, sqrtS A z⟫ := by
  have hSC : 0 ≤ sqrtS A * sqrtC A :=
    Commute.mul_nonneg sqrtS_nonneg sqrtC_nonneg commute_sqrtS_sqrtC
  rw [← isPositive_sqrtS.inner_left_eq_inner_right, ← mul_apply_eq_comp]
  exact (ContinuousLinearMap.nonneg_iff_isPositive.mp hSC).re_inner_nonneg_left z

private theorem sqrt_isFormalAdjoint (hA : IsSelfAdjoint A)
    (hpos : ∀ x : A.domain, 0 ≤ RCLike.re ⟪A x, (x : E)⟫) :
    A.sqrt.IsFormalAdjoint A.sqrt := by
  intro x y
  obtain ⟨z₁, hz₁⟩ := mem_sqrt_domain_iff.mp x.property
  obtain ⟨z₂, hz₂⟩ := mem_sqrt_domain_iff.mp y.property
  have hx : x = ⟨sqrtS A z₁, sqrtS_mem_sqrt_domain z₁⟩ := Subtype.ext hz₁.symm
  have hy : y = ⟨sqrtS A z₂, sqrtS_mem_sqrt_domain z₂⟩ := Subtype.ext hz₂.symm
  rw [hx, hy, sqrt_apply_sqrtS hA hpos, sqrt_apply_sqrtS hA hpos]
  calc ⟪sqrtC A z₁, sqrtS A z₂⟫
      = ⟪sqrtS A (sqrtC A z₁), z₂⟫ := (isPositive_sqrtS.inner_left_eq_inner_right _ _).symm
    _ = ⟪(sqrtS A * sqrtC A) z₁, z₂⟫ := rfl
    _ = ⟪(sqrtC A * sqrtS A) z₁, z₂⟫ := by rw [commute_sqrtS_sqrtC.eq]
    _ = ⟪sqrtC A (sqrtS A z₁), z₂⟫ := rfl
    _ = ⟪sqrtS A z₁, sqrtC A z₂⟫ := isPositive_sqrtC.inner_left_eq_inner_right _ _

private theorem norm_le_sqrtS_add_sqrtC (hA : IsSelfAdjoint A)
    (hpos : ∀ x : A.domain, 0 ≤ RCLike.re ⟪A x, (x : E)⟫) (z : E) :
    ‖z‖ ≤ ‖(sqrtS A + sqrtC A) z‖ := by
  refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
  rw [_root_.add_apply, @norm_add_sq 𝕜]
  have hS : ‖sqrtS A z‖ ^ 2 = RCLike.re ⟪sqrtB A z, z⟫ := by
    rw [← inner_self_eq_norm_sq (𝕜 := 𝕜), ← isPositive_sqrtS.inner_left_eq_inner_right,
      ← mul_apply_eq_comp, sqrtS_mul_self hA hpos]
  have hC : ‖sqrtC A z‖ ^ 2 = RCLike.re ⟪(1 - sqrtB A) z, z⟫ := by
    rw [← inner_self_eq_norm_sq (𝕜 := 𝕜), ← isPositive_sqrtC.inner_left_eq_inner_right,
      ← mul_apply_eq_comp, sqrtC_mul_self hA hpos]
  have hsum : RCLike.re ⟪sqrtB A z, z⟫ + RCLike.re ⟪(1 - sqrtB A) z, z⟫ = ‖z‖ ^ 2 := by
    rw [← _root_.map_add, ← inner_add_left, ← _root_.add_apply, add_sub_cancel,
      one_apply_eq_self, inner_self_eq_norm_sq]
  have hcross : 0 ≤ RCLike.re ⟪sqrtS A z, sqrtC A z⟫ := by
    rw [inner_re_symm]
    exact re_inner_sqrtC_sqrtS_nonneg z
  linarith

private theorem surjective_neg_one_sub_sqrt (hA : IsSelfAdjoint A)
    (hpos : ∀ x : A.domain, 0 ≤ RCLike.re ⟪A x, (x : E)⟫) :
    Function.Surjective (fun x : A.sqrt.domain ↦ (-1 : 𝕜) • (x : E) - A.sqrt x) := by
  let U : E →L[𝕜] E := -(sqrtS A + sqrtC A)
  have hU_sa : IsSelfAdjoint ((U : E →ₗ[𝕜] E).toPMap ⊤) :=
    isSelfAdjoint_toPMap_top (isSelfAdjoint_sqrtS.add isSelfAdjoint_sqrtC).neg
  have hsurj : Function.Surjective U := by
    intro y
    obtain ⟨x, hx⟩ := hU_sa.smul_sub_surjective_of_norm_le (c := 0) zero_lt_one (fun x ↦ by
      have hUx : ((U : E →ₗ[𝕜] E).toPMap ⊤) x = U (x : E) := rfl
      rw [zero_smul, zero_sub, hUx, norm_neg, one_mul]
      simpa only [U, _root_.neg_apply, norm_neg] using norm_le_sqrtS_add_sqrtC hA hpos (x : E)) (-y)
    have hUx : ((U : E →ₗ[𝕜] E).toPMap ⊤) x = U (x : E) := rfl
    refine ⟨(x : E), ?_⟩
    simpa only [zero_smul, zero_sub, hUx, neg_eq_iff_eq_neg, neg_neg] using hx
  intro y
  obtain ⟨z, hz⟩ := hsurj y
  refine ⟨⟨sqrtS A z, sqrtS_mem_sqrt_domain z⟩, ?_⟩
  dsimp only
  rw [sqrt_apply_sqrtS hA hpos]
  simpa [U, neg_one_smul, sub_eq_add_neg, add_comm] using hz

end Helpers

/-- The positive square root of a nonnegative self-adjoint partial linear map is self-adjoint. -/
theorem _root_.IsSelfAdjoint.isSelfAdjoint_sqrt {A : E →ₗ.[𝕜] E} (hA : IsSelfAdjoint A)
    (hpos : ∀ x : A.domain, 0 ≤ RCLike.re ⟪A x, (x : E)⟫) :
    IsSelfAdjoint A.sqrt :=
  (sqrt_isFormalAdjoint hA hpos).isSelfAdjoint_of_surjective_smul_sub (by simp)
    (surjective_neg_one_sub_sqrt hA hpos)

/-- The domain of the positive square root of a nonnegative self-adjoint partial linear map is
dense. -/
theorem _root_.IsSelfAdjoint.dense_sqrt_domain {A : E →ₗ.[𝕜] E} (hA : IsSelfAdjoint A)
    (hpos : ∀ x : A.domain, 0 ≤ RCLike.re ⟪A x, (x : E)⟫) :
    Dense (A.sqrt.domain : Set E) :=
  (hA.isSelfAdjoint_sqrt hpos).dense_domain

/-- The positive square root of a nonnegative self-adjoint partial linear map has nonnegative
quadratic form. -/
theorem _root_.IsSelfAdjoint.re_inner_sqrt_nonneg {A : E →ₗ.[𝕜] E} (hA : IsSelfAdjoint A)
    (hpos : ∀ x : A.domain, 0 ≤ RCLike.re ⟪A x, (x : E)⟫) (x : A.sqrt.domain) :
    0 ≤ RCLike.re ⟪A.sqrt x, (x : E)⟫ := by
  obtain ⟨z, hz⟩ := mem_sqrt_domain_iff.mp x.property
  have hx : x = ⟨sqrtS A z, sqrtS_mem_sqrt_domain z⟩ := Subtype.ext hz.symm
  rw [hx, sqrt_apply_sqrtS hA hpos]
  exact re_inner_sqrtC_sqrtS_nonneg z

/-- The domain of a nonnegative self-adjoint partial linear map is contained in the domain of its
positive square root. -/
theorem _root_.IsSelfAdjoint.domain_le_sqrt_domain {A : E →ₗ.[𝕜] E} (hA : IsSelfAdjoint A)
    (hpos : ∀ x : A.domain, 0 ≤ RCLike.re ⟪A x, (x : E)⟫) :
    A.domain ≤ A.sqrt.domain := by
  intro x hx
  refine mem_sqrt_domain_iff.mpr ⟨sqrtS A (x + A ⟨x, hx⟩), ?_⟩
  rw [← mul_apply_eq_comp, sqrtS_mul_self hA hpos]
  exact sqrtB_add_apply hA hpos ⟨x, hx⟩

/-- Squaring `A.sqrt` via `adjointComp` recovers `A`: `(A.sqrt)† (A.sqrt) = A` on maximal domain. -/
theorem _root_.IsSelfAdjoint.sqrt_adjointComp {A : E →ₗ.[𝕜] E} (hA : IsSelfAdjoint A)
    (hpos : ∀ x : A.domain, 0 ≤ RCLike.re ⟪A x, (x : E)⟫) :
    A.sqrt.adjointComp = A := by
  have hsqrt := hA.isSelfAdjoint_sqrt hpos
  have hsqrt_adj : (A.sqrt)† = A.sqrt := isSelfAdjoint_def.mp hsqrt
  have hle : A ≤ A.sqrt.adjointComp := by
    refine ⟨fun x hx ↦ ?_, fun x y hxy ↦ ?_⟩
    · set z := x + A ⟨x, hx⟩
      have hxS : sqrtS A (sqrtS A z) = x := by
        rw [← mul_apply_eq_comp, sqrtS_mul_self hA hpos]
        exact sqrtB_add_apply hA hpos ⟨x, hx⟩
      have hx_dom : x ∈ A.sqrt.domain := hxS ▸ sqrtS_mem_sqrt_domain (sqrtS A z)
      refine mem_adjointComp_domain.mpr ⟨hx_dom, ?_⟩
      have hval : A.sqrt ⟨x, hx_dom⟩ = sqrtS A (sqrtC A z) :=
        sqrt_apply_sqrtS_sqrtS hA hpos hxS
      rw [hsqrt_adj, hval]
      exact sqrtS_mem_sqrt_domain (sqrtC A z)
    · set z := (x : E) + A x
      have hxB : sqrtB A z = (x : E) := sqrtB_add_apply hA hpos x
      have hxS : sqrtS A (sqrtS A z) = (x : E) := by
        rw [← mul_apply_eq_comp, sqrtS_mul_self hA hpos, hxB]
      have h1 : A.sqrt ⟨y, adjointComp_domain_le A.sqrt y.property⟩ = sqrtS A (sqrtC A z) :=
        sqrt_apply_sqrtS_sqrtS hA hpos (hxS.trans hxy)
      rw [adjointComp_apply]
      have h2 := LinearPMap.congr_fun hsqrt_adj
        (mem_adjointComp_domain.mp y.property).choose_spec
        (h1 ▸ sqrtS_mem_sqrt_domain (sqrtC A z))
      rw [h2]
      have hsub2 : (⟨A.sqrt ⟨y, adjointComp_domain_le A.sqrt y.property⟩,
          h1 ▸ sqrtS_mem_sqrt_domain (sqrtC A z)⟩ : A.sqrt.domain) =
          ⟨sqrtS A (sqrtC A z), sqrtS_mem_sqrt_domain _⟩ := Subtype.ext h1
      rw [hsub2, sqrt_apply_sqrtS hA hpos, ← mul_apply_eq_comp,
        sqrtC_mul_self hA hpos, _root_.sub_apply, one_apply_eq_self, hxB]
      exact (add_sub_cancel_left (x : E) (A x)).symm
  have hsq_sa := isSelfAdjoint_adjointComp A.sqrt hsqrt.isClosed hsqrt.dense_domain
  have hsq_pos := re_inner_adjointComp_nonneg A.sqrt
  exact (eq_of_le_of_mem_resolventSet hle (neg_one_mem_resolventSet hA hpos)
    (neg_one_mem_resolventSet hsq_sa hsq_pos)).symm

/-- For a nonnegative self-adjoint partial linear map `A`, `A.domain` is a graph core for
`A.sqrt`. -/
theorem _root_.IsSelfAdjoint.sqrt_hasCore_domain {A : E →ₗ.[𝕜] E} (hA : IsSelfAdjoint A)
    (hpos : ∀ x : A.domain, 0 ≤ RCLike.re ⟪A x, (x : E)⟫) :
    A.sqrt.HasCore A.domain := by
  have hcore := (hA.isSelfAdjoint_sqrt hpos).isClosed.hasCore_adjointComp_domain
  rwa [hA.sqrt_adjointComp hpos] at hcore

/-- Auxiliary bounded operator `z ↦ M (sqrtB A z)` used in the uniqueness proof for `A.sqrt`. -/
private def sqrtAuxCLM {A M : E →ₗ.[𝕜] E} (hA : IsSelfAdjoint A)
    (hpos : ∀ x : A.domain, 0 ≤ RCLike.re ⟪A x, (x : E)⟫) (hM : IsSelfAdjoint M)
    (hMsq : M.adjointComp = A) : E →L[𝕜] E :=
  have hdom : ∀ z : E, sqrtB A z ∈ M.domain := fun z ↦
    adjointComp_domain_le M (hMsq.symm ▸ sqrtB_mem_domain hA hpos z)
  LinearMap.mkContinuous
    { toFun := fun z ↦ M ⟨sqrtB A z, hdom z⟩
      map_add' := fun z₁ z₂ ↦ by
        have h : (⟨sqrtB A (z₁ + z₂), hdom _⟩ : M.domain) =
            ⟨sqrtB A z₁, hdom z₁⟩ + ⟨sqrtB A z₂, hdom z₂⟩ := Subtype.ext (_root_.map_add _ _ _)
        rw [h, map_add]
      map_smul' := fun c z ↦ by
        have h : (⟨sqrtB A (c • z), hdom _⟩ : M.domain) =
            c • ⟨sqrtB A z, hdom z⟩ := Subtype.ext (_root_.map_smul _ _ _)
        rw [h, map_smul, RingHom.id_apply] }
    1 fun z ↦ by
      rw [one_mul]
      dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
      refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
      let uA : A.domain := ⟨sqrtB A z, sqrtB_mem_domain hA hpos z⟩
      let uM : M.adjointComp.domain := ⟨sqrtB A z, hMsq.symm ▸ uA.property⟩
      have hnormM : ‖M ⟨sqrtB A z, hdom z⟩‖ ^ 2 = RCLike.re ⟪A uA, (uA : E)⟫ := by
        rw [← inner_self_eq_norm_sq (𝕜 := 𝕜), ← inner_adjointComp hM.dense_domain uM (hdom z),
          LinearPMap.congr_fun hMsq uM.property uA.property]
      have hz : z = (uA : E) + A uA := (add_apply_sqrtB hA hpos z).symm
      have hnormz : ‖z‖ ^ 2 =
          ‖(uA : E)‖ ^ 2 + 2 * RCLike.re ⟪A uA, (uA : E)⟫ + ‖A uA‖ ^ 2 := by
        conv_lhs => rw [hz]
        rw [@norm_add_sq 𝕜, inner_re_symm (uA : E) (A uA)]
      have h0 : 0 ≤ RCLike.re ⟪A uA, (uA : E)⟫ := hpos uA
      have h1 : 0 ≤ ‖(uA : E)‖ ^ 2 := sq_nonneg _
      have h2 : 0 ≤ ‖A uA‖ ^ 2 := sq_nonneg _
      linarith

private theorem sqrtAuxCLM_apply {A M : E →ₗ.[𝕜] E} (hA : IsSelfAdjoint A)
    (hpos : ∀ x : A.domain, 0 ≤ RCLike.re ⟪A x, (x : E)⟫) (hM : IsSelfAdjoint M)
    (hMsq : M.adjointComp = A) (z : E) :
    sqrtAuxCLM hA hpos hM hMsq z =
      M ⟨sqrtB A z, adjointComp_domain_le M (hMsq.symm ▸ sqrtB_mem_domain hA hpos z)⟩ :=
  rfl

private theorem sqrtAuxCLM_decomp {A M : E →ₗ.[𝕜] E} (hA : IsSelfAdjoint A)
    (hpos : ∀ x : A.domain, 0 ≤ RCLike.re ⟪A x, (x : E)⟫) (hM : IsSelfAdjoint M)
    (hMsq : M.adjointComp = A) (z : E) :
    ∃ (u v : M.domain), (u : E) = sqrtB A z ∧ (v : E) = sqrtAuxCLM hA hpos hM hMsq z ∧
      M u = (v : E) ∧ z = (u : E) + M v := by
  have hMadj : M† = M := isSelfAdjoint_def.mp hM
  have hMdom : M†.domain = M.domain := congrArg domain hMadj
  have huA : sqrtB A z ∈ A.domain := sqrtB_mem_domain hA hpos z
  have huMC : sqrtB A z ∈ M.adjointComp.domain := hMsq.symm ▸ huA
  let u : M.domain := ⟨sqrtB A z, adjointComp_domain_le M huMC⟩
  have hvM' : M u ∈ M†.domain := (mem_adjointComp_domain.mp huMC).choose_spec
  have hvM : M u ∈ M.domain := hMdom ▸ hvM'
  let v : M.domain := ⟨M u, hvM⟩
  refine ⟨u, v, rfl, rfl, rfl, ?_⟩
  have hMv : M v = A ⟨sqrtB A z, huA⟩ := by
    calc M v = M† ⟨M u, hvM'⟩ := (LinearPMap.congr_fun hMadj hvM' hvM).symm
      _ = M.adjointComp ⟨sqrtB A z, huMC⟩ := (adjointComp_apply M ⟨sqrtB A z, huMC⟩).symm
      _ = A ⟨sqrtB A z, huA⟩ := LinearPMap.congr_fun hMsq huMC huA
  rw [hMv]
  exact (add_apply_sqrtB hA hpos z).symm

private theorem sqrtAuxCLM_nonneg {A M : E →ₗ.[𝕜] E} (hA : IsSelfAdjoint A)
    (hpos : ∀ x : A.domain, 0 ≤ RCLike.re ⟪A x, (x : E)⟫) (hM : IsSelfAdjoint M)
    (hMpos : ∀ x : M.domain, 0 ≤ RCLike.re ⟪M x, (x : E)⟫) (hMsq : M.adjointComp = A) :
    0 ≤ sqrtAuxCLM hA hpos hM hMsq := by
  rw [ContinuousLinearMap.nonneg_iff_isPositive, ContinuousLinearMap.isPositive_def]
  refine ⟨fun z₁ z₂ ↦ ?_, fun z ↦ ?_⟩
  · obtain ⟨u₁, v₁, -, hv₁, hMu₁, hz₁⟩ := sqrtAuxCLM_decomp hA hpos hM hMsq z₁
    obtain ⟨u₂, v₂, -, hv₂, hMu₂, hz₂⟩ := sqrtAuxCLM_decomp hA hpos hM hMsq z₂
    rw [ContinuousLinearMap.coe_coe, ← hv₁, ← hv₂]
    calc ⟪(v₁ : E), z₂⟫
        = ⟪M u₁, (u₂ : E)⟫ + ⟪(v₁ : E), M v₂⟫ := by
            conv_lhs => rw [hz₂, ← hMu₁]
            rw [inner_add_right, hMu₁]
      _ = ⟪(u₁ : E), M u₂⟫ + ⟪M v₁, (v₂ : E)⟫ := by
            rw [hM.isFormalAdjoint u₁ u₂, ← hM.isFormalAdjoint v₁ v₂]
      _ = ⟪z₁, (v₂ : E)⟫ := by
            conv_rhs => rw [hz₁, ← hMu₂]
            rw [inner_add_left, hMu₂]
  · obtain ⟨u, v, -, hv, hMu, hz⟩ := sqrtAuxCLM_decomp hA hpos hM hMsq z
    rw [ContinuousLinearMap.reApplyInnerSelf_apply, ← hv, hz, inner_add_right, _root_.map_add]
    have h1 : ⟪(v : E), (u : E)⟫ = ⟪M u, (u : E)⟫ := by rw [hMu]
    have h2 : ⟪(v : E), M v⟫ = ⟪M v, (v : E)⟫ := (hM.isFormalAdjoint v v).symm
    rw [h1, h2]
    exact add_nonneg (hMpos u) (hMpos v)

private theorem sqrtAuxCLM_apply_eq_sqrtB_apply {A M : E →ₗ.[𝕜] E} (hA : IsSelfAdjoint A)
    (hpos : ∀ x : A.domain, 0 ≤ RCLike.re ⟪A x, (x : E)⟫) (hM : IsSelfAdjoint M)
    (hMsq : M.adjointComp = A) (w : M.domain) :
    sqrtAuxCLM hA hpos hM hMsq (w : E) = sqrtB A (M w) := by
  have hMadj : M† = M := isSelfAdjoint_def.mp hM
  have hMdom : M†.domain = M.domain := congrArg domain hMadj
  obtain ⟨u, v, -, hv, hMu, hw⟩ := sqrtAuxCLM_decomp hA hpos hM hMsq (w : E)
  have hMv_eq : M v = ((w - u : M.domain) : E) := eq_sub_of_add_eq' hw.symm
  have hMv_dom : M v ∈ M.domain := hMv_eq ▸ (w - u).property
  have hMv_adj : M v ∈ M†.domain := hMdom.symm ▸ hMv_dom
  have hvMC : (v : E) ∈ M.adjointComp.domain := mem_adjointComp_domain.mpr ⟨v.property, hMv_adj⟩
  have hvA : (v : E) ∈ A.domain := hMsq ▸ hvMC
  have hAv : A ⟨(v : E), hvA⟩ = M w - (v : E) := by
    have hsub : (⟨M v, hMv_dom⟩ : M.domain) = w - u := Subtype.ext hMv_eq
    calc A ⟨(v : E), hvA⟩
        = M.adjointComp ⟨(v : E), hvMC⟩ := LinearPMap.congr_fun hMsq.symm hvA hvMC
      _ = M† ⟨M v, (mem_adjointComp_domain.mp hvMC).choose_spec⟩ :=
          adjointComp_apply M ⟨(v : E), hvMC⟩
      _ = M ⟨M v, hMv_dom⟩ := LinearPMap.congr_fun hMadj _ hMv_dom
      _ = M (w - u) := by rw [hsub]
      _ = M w - (v : E) := by rw [map_sub, hMu]
  have hsum : (v : E) + A ⟨(v : E), hvA⟩ = M w := by rw [hAv, add_sub_cancel]
  rw [← hv, ← hsum]
  exact (sqrtB_add_apply hA hpos ⟨(v : E), hvA⟩).symm

private theorem sqrtAuxCLM_mul_self {A M : E →ₗ.[𝕜] E} (hA : IsSelfAdjoint A)
    (hpos : ∀ x : A.domain, 0 ≤ RCLike.re ⟪A x, (x : E)⟫) (hM : IsSelfAdjoint M)
    (hMsq : M.adjointComp = A) :
    sqrtAuxCLM hA hpos hM hMsq * sqrtAuxCLM hA hpos hM hMsq = sqrtB A * (1 - sqrtB A) := by
  ext z
  obtain ⟨u, v, hu, hv, -, hz⟩ := sqrtAuxCLM_decomp hA hpos hM hMsq z
  have hMv : M v = (1 - sqrtB A) z := by
    rw [_root_.sub_apply, one_apply_eq_self, ← hu]
    exact eq_sub_of_add_eq' hz.symm
  rw [mul_apply_eq_comp, ← hv, sqrtAuxCLM_apply_eq_sqrtB_apply hA hpos hM hMsq v,
    hMv, mul_apply_eq_comp]

/-- **Uniqueness of the positive square root.** Any nonnegative self-adjoint partial linear map `M`
satisfying `M.adjointComp = A` coincides with `A.sqrt`. -/
theorem _root_.IsSelfAdjoint.eq_sqrt {A M : E →ₗ.[𝕜] E} (hA : IsSelfAdjoint A)
    (hpos : ∀ x : A.domain, 0 ≤ RCLike.re ⟪A x, (x : E)⟫) (hM : IsSelfAdjoint M)
    (hMpos : ∀ x : M.domain, 0 ≤ RCLike.re ⟪M x, (x : E)⟫) (hMsq : M.adjointComp = A) :
    M = A.sqrt := by
  have hS := hA.isSelfAdjoint_sqrt hpos
  have hSpos := hA.re_inner_sqrt_nonneg hpos
  have hSsq := hA.sqrt_adjointComp hpos
  have hG : sqrtAuxCLM hA hpos hM hMsq = sqrtAuxCLM hA hpos hS hSsq :=
    (CFC.mul_self_eq_mul_self_iff _ _ (sqrtAuxCLM_nonneg hA hpos hM hMpos hMsq)
      (sqrtAuxCLM_nonneg hA hpos hS hSpos hSsq)).mp
      ((sqrtAuxCLM_mul_self hA hpos hM hMsq).trans (sqrtAuxCLM_mul_self hA hpos hS hSsq).symm)
  have hdomR : M.domRestrict A.domain = A.sqrt.domRestrict A.domain := by
    have hdomM : A.domain ≤ M.domain := hMsq ▸ adjointComp_domain_le M
    have hdomS : A.domain ≤ A.sqrt.domain := hA.domain_le_sqrt_domain hpos
    have hdomEq : (M.domRestrict A.domain).domain = (A.sqrt.domRestrict A.domain).domain := by
      rw [domRestrict_domain, domRestrict_domain, inf_of_le_left hdomM, inf_of_le_left hdomS]
    refine LinearPMap.ext hdomEq fun x hx₁ hx₂ ↦ ?_
    have hxA : x ∈ A.domain := hx₁.1
    let z : E := x + A ⟨x, hxA⟩
    have hBz : sqrtB A z = x := sqrtB_add_apply hA hpos ⟨x, hxA⟩
    have heval := congr($hG z)
    rw [sqrtAuxCLM_apply, sqrtAuxCLM_apply] at heval
    have hsubM : (⟨sqrtB A z, adjointComp_domain_le M
        (hMsq.symm ▸ sqrtB_mem_domain hA hpos z)⟩ : M.domain) = ⟨x, hx₁.2⟩ := Subtype.ext hBz
    have hsubS : (⟨sqrtB A z, adjointComp_domain_le A.sqrt
        (hSsq.symm ▸ sqrtB_mem_domain hA hpos z)⟩ : A.sqrt.domain) = ⟨x, hx₂.2⟩ := Subtype.ext hBz
    have h₁ : (M.domRestrict A.domain) ⟨x, hx₁⟩ = M ⟨x, hx₁.2⟩ := M.domRestrict_le.2 rfl
    have h₂ : (A.sqrt.domRestrict A.domain) ⟨x, hx₂⟩ = A.sqrt ⟨x, hx₂.2⟩ :=
      A.sqrt.domRestrict_le.2 rfl
    rw [h₁, h₂, ← hsubM, ← hsubS]
    exact heval
  have hcoreM : M.HasCore A.domain := hMsq ▸ hM.isClosed.hasCore_adjointComp_domain
  have hcoreS : A.sqrt.HasCore A.domain := hA.sqrt_hasCore_domain hpos
  rw [← hcoreM.closure_eq, hdomR, hcoreS.closure_eq]

/-- Characterization of `A.sqrt` as the unique nonnegative self-adjoint partial linear map whose
`adjointComp` is `A`. -/
theorem _root_.IsSelfAdjoint.eq_sqrt_iff {A M : E →ₗ.[𝕜] E} (hA : IsSelfAdjoint A)
    (hpos : ∀ x : A.domain, 0 ≤ RCLike.re ⟪A x, (x : E)⟫) :
    M = A.sqrt ↔
      IsSelfAdjoint M ∧ (∀ x : M.domain, 0 ≤ RCLike.re ⟪M x, (x : E)⟫) ∧ M.adjointComp = A := by
  refine ⟨?_, fun ⟨hM, hMpos, hMsq⟩ ↦ hA.eq_sqrt hpos hM hMpos hMsq⟩
  rintro rfl
  exact ⟨hA.isSelfAdjoint_sqrt hpos, hA.re_inner_sqrt_nonneg hpos, hA.sqrt_adjointComp hpos⟩

end Sqrt

end LinearPMap

namespace ContinuousLinearMap

variable [CompleteSpace E]

/-- Viewing a bounded positive operator `P` as a partial linear map on `⊤`, its unbounded positive
square root coincides with `CFC.sqrt P` on `⊤` (for any real algebra structure on `E →L[𝕜] E`
compatible with the `𝕜`-action). -/
theorem IsPositive.toPMap_top_sqrt [Algebra ℝ (E →L[𝕜] E)] [IsScalarTower ℝ 𝕜 (E →L[𝕜] E)]
    {P : E →L[𝕜] E} (hP : P.IsPositive) :
    ((P : E →ₗ[𝕜] E).toPMap ⊤).sqrt =
      ((CFC.sqrt P : E →L[𝕜] E) : E →ₗ[𝕜] E).toPMap ⊤ := by
  have hA : IsSelfAdjoint ((P : E →ₗ[𝕜] E).toPMap ⊤) :=
    LinearPMap.isSelfAdjoint_toPMap_top hP.isSelfAdjoint
  have hpos : ∀ x : ((P : E →ₗ[𝕜] E).toPMap ⊤).domain,
      0 ≤ RCLike.re ⟪((P : E →ₗ[𝕜] E).toPMap ⊤) x, (x : E)⟫ :=
    fun x ↦ hP.re_inner_nonneg_left (x : E)
  let Q : E →L[𝕜] E := CFC.sqrt P
  have hQ : Q.IsPositive := nonneg_iff_isPositive.mp (CFC.sqrt_nonneg P)
  refine ((hA.eq_sqrt_iff hpos).mpr ⟨LinearPMap.isSelfAdjoint_toPMap_top hQ.isSelfAdjoint,
    fun x ↦ hQ.re_inner_nonneg_left (x : E), ?_⟩).symm
  rw [Q.toPMap_top_adjointComp]
  have hQQ : Q.adjoint ∘L Q = P := by
    rw [hQ.isSelfAdjoint.adjoint_eq]
    exact CFC.sqrt_mul_sqrt_self P (nonneg_iff_isPositive.mpr hP)
  rw [hQQ]

end ContinuousLinearMap

namespace LinearPMap

variable [CompleteSpace E]

attribute [local instance] ContinuousLinearMap.realAlgebra ContinuousLinearMap.realIsScalarTower

/-- The positive square root of the zero partial linear map (on `⊤`) is zero. -/
@[simp]
theorem sqrt_zero : (0 : E →ₗ.[𝕜] E).sqrt = 0 := by
  have h0 : ((0 : E →L[𝕜] E) : E →ₗ[𝕜] E).toPMap ⊤ = (0 : E →ₗ.[𝕜] E) :=
    LinearPMap.ext rfl fun _ _ _ ↦ rfl
  have h := (ContinuousLinearMap.isPositive_zero (𝕜 := 𝕜) (E := E)).toPMap_top_sqrt
  rwa [CFC.sqrt_zero, h0] at h

end LinearPMap

