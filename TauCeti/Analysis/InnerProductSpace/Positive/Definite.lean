/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
import TauCeti.Analysis.InnerProductSpace.Positive.SquareRoot
import TauCeti.Analysis.InnerProductSpace.Reflection
import TauCeti.Analysis.Normed.Operator.ContinuousLinearEquiv

/-!
# A positive-definite form is the standard one in suitable coordinates

Let `S` be a symmetric operator on a finite-dimensional inner product space `V` whose associated
Hermitian form `⟪S v, w⟫` is positive definite. This file produces a linear automorphism of `V`
along which that form pulls back to the inner product `V` already carries:

`TauCeti.exists_continuousLinearEquiv_inner_map_map` gives `e : V ≃L[𝕜] V` with
`⟪S (e x), e y⟫ = ⟪x, y⟫` for all `x` and `y`.

Equivalently `e` is an isometry from `(V, ⟪·,·⟫)` onto `(V, ⟪S ·, ·⟫)`. One such `e` is the
inverse of the positive square root `√S` (`LinearMap.IsPositive.sqrt`), which is invertible because
the form is definite: `√S` is symmetric with `√S ∘ √S = S`, so `⟪S u, v⟫ = ⟪√S u, √S v⟫`.

A related factorization can be chosen compatibly with a prescribed direction `ν`:
`ContinuousLinearMap.exists_continuousLinearEquiv_comp_adjoint_eq_of_isSymmetric` factors a
positive-definite symmetric operator as `A = e e†`, so that `⟪A x, y⟫ = ⟪e† x, e† y⟫`, with
`e† ν` a positive real multiple of `ν`. Over the reals, composing with such an `e` turns the
second-order operator `u ↦ tr (A D²u)` into the Laplacian, since `D²(u ∘ e) = e† (D²u ∘ e) e`,
while `e⁻¹` maps each half-space `{⟪x, ν⟫ > a}` onto another half-space with the same normal. This
is how constant-coefficient elliptic equations on a half-space reduce to Poisson's equation on a
half-space.

## Main statements

* `TauCeti.exists_continuousLinearEquiv_inner_map_map`: a positive-definite symmetric operator's
  form becomes the standard inner product after a change of coordinates.
* `ContinuousLinearMap.exists_continuousLinearEquiv_comp_adjoint_eq_of_isSymmetric`: a
  positive-definite symmetric operator factors as `e e†`, with `e†` fixing the direction of a
  given vector.

Only the existence of `e` is exported, since `e` is determined only up to a unitary automorphism:
with `e`, every `e ∘ U` for a unitary `U` works as well. The operator is
taken continuous and the change of coordinates produced is a continuous linear equivalence; on a
finite-dimensional space that is no restriction either way, and it is the form the consumer both
supplies and wants.

The intended consumer is Weyl's unitarian trick: applied to the Gram operator of the Haar-averaged
inner product of a representation of a compact group, this is what turns the invariant form into
an honest unitary structure, in
`TauCeti/RepresentationTheory/Compact/UnitaryModel.lean`.
-/

public section

open RCLike
open scoped InnerProductSpace

namespace TauCeti

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [FiniteDimensional 𝕜 V]

/-- **A positive-definite form is standard in suitable coordinates.** If `S` is a symmetric
operator on a finite-dimensional inner product space whose form `⟪S ·, ·⟫` is positive definite,
then there is a continuous linear automorphism `e` with `⟪S (e x), e y⟫ = ⟪x, y⟫`.

One can take `e` to be the inverse of the positive square root `√S`
(`LinearMap.IsPositive.sqrt`), which is injective because the form is definite. -/
theorem exists_continuousLinearEquiv_inner_map_map (S : V →L[𝕜] V)
    (hsymm : (S : V →ₗ[𝕜] V).IsSymmetric) (hpos : ∀ v : V, v ≠ 0 → 0 < re ⟪S v, v⟫_𝕜) :
    ∃ e : V ≃L[𝕜] V, ∀ x y : V, ⟪S (e x), e y⟫_𝕜 = ⟪x, y⟫_𝕜 := by
  have hT : (S : V →ₗ[𝕜] V).IsPositive := ⟨hsymm, fun v ↦ by
    rcases eq_or_ne v 0 with rfl | hv
    · simp
    · exact (hpos v hv).le⟩
  set R := hT.sqrt
  -- The form is definite, so `S` is injective, and `R` has the same kernel as `S`.
  have hRinj : Function.Injective R := by
    rw [← LinearMap.ker_eq_bot, hT.ker_sqrt, LinearMap.ker_eq_bot']
    intro v hv
    by_contra hne
    rw [ContinuousLinearMap.coe_coe] at hv
    simpa [hv] using hpos v hne
  set Rc : V ≃L[𝕜] V := (LinearEquiv.ofInjectiveEndo R hRinj).toContinuousLinearEquiv
  have hRc : ∀ x, R (Rc.symm x) = x := fun x ↦ by
    rw [← LinearEquiv.coe_ofInjectiveEndo R hRinj, ← LinearEquiv.coe_toContinuousLinearEquiv',
      ContinuousLinearEquiv.apply_symm_apply]
  -- `R` is symmetric with `R ∘ R = S`, so `⟪S u, v⟫ = ⟪R u, R v⟫`.
  refine ⟨Rc.symm, fun x y ↦ ?_⟩
  rw [← ContinuousLinearMap.coe_coe, ← hT.sqrt_sq, LinearMap.comp_apply, hT.sqrt_isSymmetric,
    hRc, hRc]

/-- **Factoring a positive-definite operator through a prescribed direction.** Let `A` be a
symmetric operator on a finite-dimensional inner product space with `λ ‖ξ‖² ≤ re ⟪A ξ, ξ⟫` for
some `λ > 0`, and let `ν` be a vector. Then there is a continuous linear automorphism `e` with
`e e† = A`, whose adjoint maps `ν` to a positive real multiple of `ν`, and with
`‖e⁻¹ x‖ ≤ ‖x‖ / √λ`.

One can take `e = √A ∘ R`, where `√A` is the positive square root of `A` and `R` is the reflection
exchanging `ν` and the vector of the same length in the direction of `√A ν`. That reflection
exists over `ℂ` as well because `⟪ν, √A ν⟫` is real.

The `CompleteSpace V` argument is automatic for a finite-dimensional space; it is there so that the
adjoint `e†` of a continuous linear map can be formed, and instance search finds it over `ℝ`. -/
theorem _root_.ContinuousLinearMap.exists_continuousLinearEquiv_comp_adjoint_eq_of_isSymmetric
    [CompleteSpace V] (A : V →L[𝕜] V) (hA : (A : V →ₗ[𝕜] V).IsSymmetric) {lam : ℝ}
    (hlam : 0 < lam)
    (hpos : ∀ ξ : V, lam * ‖ξ‖ ^ 2 ≤ re ⟪A ξ, ξ⟫_𝕜) {ν : V} :
    ∃ e : V ≃L[𝕜] V, (e : V →L[𝕜] V) ∘L (e : V →L[𝕜] V).adjoint = A ∧
      (∃ c : ℝ, 0 < c ∧ (e : V →L[𝕜] V).adjoint ν = (c : 𝕜) • ν) ∧
      ∀ x : V, ‖e.symm x‖ ≤ (√lam)⁻¹ * ‖x‖ := by
  have hT : (A : V →ₗ[𝕜] V).IsPositive :=
    ⟨hA, fun x => (by positivity : 0 ≤ lam * ‖x‖ ^ 2).trans (hpos x)⟩
  set R := hT.sqrt
  -- `‖R x‖² = re ⟪A x, x⟫ ≥ λ ‖x‖²`, so `R` is injective.
  have hRn : ∀ x, lam * ‖x‖ ^ 2 ≤ ‖R x‖ ^ 2 := fun x => by
    rw [hT.norm_sqrt_apply_sq x]
    exact hpos x
  have hRinj : Function.Injective R := by
    refine (injective_iff_map_eq_zero R).2 fun x hx => ?_
    have h := hRn x
    rw [hx, norm_zero] at h
    have : ‖x‖ ^ 2 ≤ 0 := by nlinarith
    exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm this (sq_nonneg _)))
  set Rc : V ≃L[𝕜] V := (LinearEquiv.ofInjectiveEndo R hRinj).toContinuousLinearEquiv
  have hRν : ν ≠ 0 → R ν ≠ 0 := fun hν h => hν (hRinj (h.trans (map_zero R).symm))
  -- the reflection `O` carries `ν` to the direction of `R ν`, with the same norm
  set w : V := ((‖ν‖ / ‖R ν‖ : ℝ) : 𝕜) • R ν
  have hw : ‖ν‖ = ‖w‖ := by
    rcases eq_or_ne ν 0 with rfl | hν
    · simp [w]
    rw [norm_smul, RCLike.norm_ofReal, abs_of_nonneg (by positivity),
      div_mul_cancel₀ _ (norm_ne_zero_iff.2 (hRν hν))]
  -- `⟪ν, w⟫` is real, since `R` is symmetric and `w` is a real multiple of `R ν`
  have hνw : ⟪ν, w⟫_𝕜 = ⟪w, ν⟫_𝕜 := by
    rw [inner_smul_right, inner_smul_left, RCLike.conj_ofReal, hT.sqrt_isSymmetric]
  set O := (𝕜 ∙ (ν - w))ᗮ.reflection
  have hOν : O ν = w := Submodule.reflection_sub_of_inner_comm hw hνw
  have hOw : O w = ν := by rw [← hOν, Submodule.reflection_reflection]
  have hOO : ∀ x, O (O x) = x := Submodule.reflection_reflection _
  have hOinner : ∀ x y, ⟪O x, y⟫_𝕜 = ⟪x, O y⟫_𝕜 := fun x y => by
    rw [← O.inner_map_map x (O y), hOO]
  set e : V ≃L[𝕜] V := O.toContinuousLinearEquiv.trans Rc
  -- `Rc` is `R` bundled as an equivalence, so `e` is `R ∘ O` by construction
  have he : ∀ y, e y = R (O y) := fun y => rfl
  -- the adjoint of `e = R ∘ O` is `O ∘ R`
  have hadj : ∀ x, (e : V →L[𝕜] V).adjoint x = O (R x) := by
    intro x
    refine ext_inner_right 𝕜 fun y => ?_
    rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearEquiv.coe_coe, he,
      ← hT.sqrt_isSymmetric, hOinner]
  refine ⟨e, ?_, ?_, fun x => ?_⟩
  · ext x
    rw [ContinuousLinearMap.comp_apply, hadj, ContinuousLinearEquiv.coe_coe, he, hOO,
      ← LinearMap.comp_apply, hT.sqrt_sq, ContinuousLinearMap.coe_coe]
  · rcases eq_or_ne ν 0 with rfl | hν
    · exact ⟨1, one_pos, by simp⟩
    refine ⟨‖R ν‖ / ‖ν‖, by have := norm_pos_iff.2 (hRν hν); positivity, ?_⟩
    have hRw : R ν = ((‖R ν‖ / ‖ν‖ : ℝ) : 𝕜) • w := by
      rw [smul_smul, ← RCLike.ofReal_mul, div_mul_div_cancel₀ (norm_ne_zero_iff.2 hν),
        div_self (norm_ne_zero_iff.2 (hRν hν)), RCLike.ofReal_one, one_smul]
    rw [hadj]
    exact (congrArg O hRw).trans (by rw [map_smul, hOw])
  · -- `λ ‖y‖² ≤ ‖R (O y)‖² = ‖e y‖²`
    refine e.norm_symm_apply_le_inv_sqrt_mul_norm hlam (fun y => ?_) x
    have h := hRn (O y)
    rwa [← he, O.norm_map] at h

end TauCeti
