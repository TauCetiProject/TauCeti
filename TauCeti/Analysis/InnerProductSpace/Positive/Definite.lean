/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import TauCeti.Analysis.InnerProductSpace.Positive.SquareRoot

/-!
# A positive-definite form is the standard one in suitable coordinates

Let `S` be a symmetric operator on a finite-dimensional inner product space `V` whose associated
Hermitian form `⟪S v, w⟫` is positive definite. This file produces a linear automorphism of `V`
along which that form pulls back to the inner product `V` already carries:

`TauCeti.exists_continuousLinearEquiv_inner_map_map` gives `e : V ≃L[𝕜] V` with
`⟪S (e x), e y⟫ = ⟪x, y⟫` for all `x` and `y`.

Equivalently `e` is an isometry from `(V, ⟪·,·⟫)` onto `(V, ⟪S ·, ·⟫)`, so its inverse is the
operator usually written `S ^ (1 / 2)`; the construction here avoids building an operator square
root by scaling an orthonormal eigenbasis of `S` instead. The eigenvalues of `S` are positive
because the form is definite, so dividing the `i`-th eigenvector by `√(λ i)` produces a basis that
is orthonormal *for the form*, and `e` is the map carrying the eigenbasis to it.

Over the reals, a related factorization can be chosen compatibly with a prescribed direction `ν`:
`ContinuousLinearMap.exists_continuousLinearEquiv_comp_adjoint_eq_of_isSymmetric` factors a
positive-definite symmetric operator as `A = e e†`, so that `⟪A x, y⟫ = ⟪e† x, e† y⟫`, with
`e† ν` a positive multiple of `ν`. Composing with such an `e` turns the second-order operator
`u ↦ tr (A D²u)` into the Laplacian, since `D²(u ∘ e) = e† (D²u ∘ e) e`, while `e⁻¹` maps each
half-space `{⟪x, ν⟫ > a}` onto another half-space with the same normal. This is how
constant-coefficient elliptic equations on a half-space reduce to Poisson's equation on a
half-space.

## Main statements

* `TauCeti.exists_continuousLinearEquiv_inner_map_map`: a positive-definite symmetric operator's
  form becomes the standard inner product after a change of coordinates.
* `ContinuousLinearMap.exists_continuousLinearEquiv_comp_adjoint_eq_of_isSymmetric`: a
  positive-definite symmetric operator factors as `e e†`, with `e†` fixing the direction of a
  given vector.

Only the existence of `e` is exported, since it depends on a choice of eigenbasis. The operator is
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

The automorphism is the inverse of the square root of `S`, built without any operator functional
calculus: an orthonormal eigenbasis `b` of `S` has positive eigenvalues `λ i`, so the vectors
`(√(λ i))⁻¹ • b i` are orthonormal for the form `⟪S ·, ·⟫`, and `e` is the automorphism carrying
`b i` to them. -/
theorem exists_continuousLinearEquiv_inner_map_map (S : V →L[𝕜] V)
    (hsymm : (S : V →ₗ[𝕜] V).IsSymmetric) (hpos : ∀ v : V, v ≠ 0 → 0 < re ⟪S v, v⟫_𝕜) :
    ∃ e : V ≃L[𝕜] V, ∀ x y : V, ⟪S (e x), e y⟫_𝕜 = ⟪x, y⟫_𝕜 := by
  classical
  set n := Module.finrank 𝕜 V with hn
  set b := hsymm.eigenvectorBasis hn.symm
  set lam := hsymm.eigenvalues hn.symm
  have hSb : ∀ i, S (b i) = (lam i : 𝕜) • b i := fun i ↦
    hsymm.apply_eigenvectorBasis hn.symm i
  have hbb : ∀ i j, ⟪b i, b j⟫_𝕜 = if i = j then 1 else 0 :=
    orthonormal_iff_ite.mp b.orthonormal
  -- The eigenvalues are positive: `⟪S (b i), b i⟫ = λ i` and the form is definite.
  have hlam : ∀ i, 0 < lam i := fun i ↦ by
    have h := hpos (b i) (b.orthonormal.ne_zero i)
    rw [hSb i, inner_smul_left, hbb i i] at h
    simpa using h
  -- Scaling the `i`-th eigenvector by `(√(λ i))⁻¹` makes the family orthonormal for the form.
  set w : Fin n → 𝕜 := fun i ↦ ((Real.sqrt (lam i))⁻¹ : ℝ) with hwdef
  have hw : ∀ i, IsUnit (w i) := fun i ↦ by
    refine isUnit_iff_ne_zero.mpr ?_
    simp [hwdef, Real.sqrt_eq_zero', (hlam i).not_ge]
  set el : V ≃ₗ[𝕜] V := b.toBasis.equiv (b.toBasis.isUnitSMul hw) (Equiv.refl (Fin n)) with heldef
  set e : V ≃L[𝕜] V := el.toContinuousLinearEquiv with hedef
  have he' : ∀ i, e (b.toBasis i) = w i • b.toBasis i := fun i ↦ by
    simp only [hedef, heldef, LinearEquiv.coe_toContinuousLinearEquiv',
      Module.Basis.equiv_apply, Equiv.refl_apply, Module.Basis.isUnitSMul_apply]
  have he : ∀ i, e (b i) = w i • b i := by simpa only [b.coe_toBasis] using he'
  have hkey : ∀ i j, ⟪S (e (b i)), e (b j)⟫_𝕜 = if i = j then 1 else 0 := fun i j ↦ by
    rw [he i, he j, map_smul, hSb i, smul_smul, inner_smul_left, inner_smul_right, hbb i j]
    rcases eq_or_ne i j with rfl | hij
    · have hr : ((Real.sqrt (lam i))⁻¹ * lam i * (Real.sqrt (lam i))⁻¹ : ℝ) = 1 := by
        have hne : Real.sqrt (lam i) ≠ 0 := (Real.sqrt_pos.mpr (hlam i)).ne'
        field_simp
        exact (Real.sq_sqrt (hlam i).le).symm
      rw [ite_eq_left rfl, mul_one, hwdef, ← RCLike.ofReal_mul, conj_ofReal, ← RCLike.ofReal_mul,
        hr, RCLike.ofReal_one]
    · simp [hij]
  -- Both sides are sesquilinear, so the basis computation determines them.
  refine ⟨e, fun x y ↦ ?_⟩
  rw [← b.sum_inner_mul_inner x y]
  conv_lhs => rw [← b.sum_repr' x, ← b.sum_repr' y]
  simp only [map_sum, map_smul, sum_inner, inner_sum, inner_smul_left, inner_smul_right, hkey]
  simp [inner_conj_symm, mul_comm]

section Real

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- **Factoring a positive-definite operator through a prescribed direction.** Let `A` be a
symmetric operator on a finite-dimensional real inner product space with `λ ‖ξ‖² ≤ ⟪A ξ, ξ⟫` for
some `λ > 0`, and let `ν ≠ 0`. Then there is a continuous linear automorphism `e` with
`e e† = A`, whose adjoint maps `ν` to a positive multiple of `ν`, and with
`‖e⁻¹ x‖ ≤ ‖x‖ / √λ`.

One can take `e = √A ∘ R`, where `√A` is the positive square root of `A` and `R` is the reflection
exchanging `ν` and the vector of the same length in the direction of `√A ν`. -/
theorem _root_.ContinuousLinearMap.exists_continuousLinearEquiv_comp_adjoint_eq_of_isSymmetric
    (A : V →L[ℝ] V) (hA : (A : V →ₗ[ℝ] V).IsSymmetric) {lam : ℝ} (hlam : 0 < lam)
    (hpos : ∀ ξ : V, lam * ‖ξ‖ ^ 2 ≤ ⟪A ξ, ξ⟫_ℝ) {ν : V} (hν : ν ≠ 0) :
    ∃ e : V ≃L[ℝ] V, (e : V →L[ℝ] V) ∘L (e : V →L[ℝ] V).adjoint = A ∧
      (∃ c : ℝ, 0 < c ∧ (e : V →L[ℝ] V).adjoint ν = c • ν) ∧
      ∀ x : V, ‖e.symm x‖ ≤ (√lam)⁻¹ * ‖x‖ := by
  have hT : (A : V →ₗ[ℝ] V).IsPositive :=
    ((A : V →ₗ[ℝ] V).isPositive_iff).2 ⟨hA, fun x => (by positivity : 0 ≤ lam * ‖x‖ ^ 2).trans
      (hpos x)⟩
  set R := hT.sqrt
  -- `‖R x‖² = ⟪A x, x⟫ ≥ λ ‖x‖²`, so `R` is injective.
  have hRn : ∀ x, lam * ‖x‖ ^ 2 ≤ ‖R x‖ ^ 2 := fun x => by
    rw [hT.norm_sqrt_apply_sq x, RCLike.re_to_real]
    exact hpos x
  have hRinj : Function.Injective R := by
    refine (injective_iff_map_eq_zero R).2 fun x hx => ?_
    have h := hRn x
    rw [hx, norm_zero] at h
    have : ‖x‖ ^ 2 ≤ 0 := by nlinarith
    exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm this (sq_nonneg _)))
  set Rc : V ≃L[ℝ] V := (LinearEquiv.ofInjectiveEndo R hRinj).toContinuousLinearEquiv
  have hRν : R ν ≠ 0 := fun h => hν (hRinj (h.trans (map_zero R).symm))
  -- the reflection `O` carries `ν` to the direction of `R ν`, with the same norm
  set w : V := (‖ν‖ / ‖R ν‖) • R ν
  have hw : ‖ν‖ = ‖w‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      div_mul_cancel₀ _ (norm_ne_zero_iff.2 hRν)]
  set O := (ℝ ∙ (ν - w))ᗮ.reflection
  have hOν : O ν = w := Submodule.reflection_sub hw
  have hOw : O w = ν := by rw [← hOν, Submodule.reflection_reflection]
  have hOO : ∀ x, O (O x) = x := Submodule.reflection_reflection _
  have hOinner : ∀ x y, ⟪O x, y⟫_ℝ = ⟪x, O y⟫_ℝ := fun x y => by
    rw [← O.inner_map_map x (O y), hOO]
  set e : V ≃L[ℝ] V := O.toContinuousLinearEquiv.trans Rc
  -- `Rc` is `R` bundled as an equivalence, so `e` is `R ∘ O` by construction
  have he : ∀ y, e y = R (O y) := fun y => rfl
  -- the adjoint of `e = R ∘ O` is `O ∘ R`
  have hadj : ∀ x, (e : V →L[ℝ] V).adjoint x = O (R x) := by
    intro x
    refine ext_inner_right ℝ fun y => ?_
    rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearEquiv.coe_coe, he,
      ← hT.sqrt_isSymmetric, hOinner]
  refine ⟨e, ?_, ⟨‖R ν‖ / ‖ν‖, by positivity, ?_⟩, fun x => ?_⟩
  · ext x
    rw [ContinuousLinearMap.comp_apply, hadj, ContinuousLinearEquiv.coe_coe, he, hOO,
      ← LinearMap.comp_apply, hT.sqrt_sq, ContinuousLinearMap.coe_coe]
  · have hRw : R ν = (‖R ν‖ / ‖ν‖) • w := by
      rw [smul_smul, div_mul_div_cancel₀ (norm_ne_zero_iff.2 hν),
        div_self (norm_ne_zero_iff.2 hRν), one_smul]
    rw [hadj]
    exact (congrArg O hRw).trans (by rw [map_smul, hOw])
  · -- `λ ‖y‖² ≤ ‖R (O y)‖² = ‖e y‖²`, applied to `y = e⁻¹ x`
    have h := hRn (O (e.symm x))
    rw [← he, e.apply_symm_apply, O.norm_map] at h
    rw [inv_mul_eq_div, le_div_iff₀ (Real.sqrt_pos.2 hlam)]
    refine (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).1 ?_
    rw [mul_pow, Real.sq_sqrt hlam.le, mul_comm]
    exact h

end Real

end TauCeti
