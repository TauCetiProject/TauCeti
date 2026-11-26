/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Analysis.Matrix.Hermitian
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Coordinates
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
* `ContinuousLinearMap.exists_continuousLinearEquiv_comp_adjoint_eq_two_inv_smul_add`: the same
  factorization for the symmetric part `(A + A†) / 2` of a coercive operator `A` that need not be
  symmetric (`ContinuousLinearMap.isSymmetric_two_inv_smul_add_adjoint`), which has the same real
  quadratic form as `A` (`ContinuousLinearMap.re_inner_two_inv_smul_add_adjoint_apply`).
* `ContinuousLinearMap.posDef_toMatrix_symmPart`: over the reals, the matrix of the symmetric part
  of a positive-definite operator in an orthonormal basis is positive definite.
* `ContinuousLinearMap.norm_conj_symmPart_sub_id_le`: over the reals, after the change of
  variables `e` with `e e† = (A + A†) / 2` and `‖e⁻¹‖ ≤ λ^{-1/2}`, the symmetric part of `a` becomes
  `e⁻¹ ((a + a†) / 2) e⁻†`, within `‖a - A‖ / λ` of the identity;
  `ContinuousLinearMap.norm_conj_symmPart_sub_id_le_of_norm_sub_le` is the form used with
  `‖a - A‖ ≤ δ λ`, and `ContinuousLinearMap.continuous_conj_symmPart` gives the continuity of
  `X ↦ N ((X + X†) / 2) N†`.
* `TauCeti.exists_linearEquiv_inner_eq_of_posDef`: a symmetric positive-definite bilinear form on a
  finite-dimensional real vector space transfers along a linear equivalence to the inner product of
  any real inner product space of the same dimension.

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

omit [FiniteDimensional 𝕜 V] in
/-- The symmetric part `(A + A†) / 2` of an operator `A` is symmetric. -/
theorem _root_.ContinuousLinearMap.isSymmetric_two_inv_smul_add_adjoint [CompleteSpace V]
    (A : V →L[𝕜] V) : (((2⁻¹ : 𝕜) • (A + A.adjoint) : V →L[𝕜] V) : V →ₗ[𝕜] V).IsSymmetric :=
  fun x y => by
    simp only [ContinuousLinearMap.coe_coe, smul_apply, add_apply, inner_smul_left,
      inner_smul_right, inner_add_left, inner_add_right, ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearMap.adjoint_inner_right, map_inv₀, map_ofNat]
    ring

omit [FiniteDimensional 𝕜 V] in
/-- The symmetric part `(A + A†) / 2` of an operator `A` has the same real quadratic form
`re ⟪A ξ, ξ⟫` as `A`. -/
theorem _root_.ContinuousLinearMap.re_inner_two_inv_smul_add_adjoint_apply [CompleteSpace V]
    (A : V →L[𝕜] V) (ξ : V) :
    re ⟪((2⁻¹ : 𝕜) • (A + A.adjoint)) ξ, ξ⟫_𝕜 = re ⟪A ξ, ξ⟫_𝕜 := by
  simp [inner_add_left, inner_smul_left, ContinuousLinearMap.adjoint_inner_left,
    inner_re_symm ξ (A ξ), normSq_apply]
  ring

/-- **Factoring the symmetric part of a coercive operator through a prescribed direction.** Let
`A` be an operator on a finite-dimensional inner product space, not necessarily symmetric, with
`λ ‖ξ‖² ≤ re ⟪A ξ, ξ⟫` for some `λ > 0`, and let `ν` be a vector. Then there is a continuous linear
automorphism `e` with `e e† = (A + A†) / 2`, whose adjoint maps `ν` to a positive real multiple
of `ν`, and with `‖e⁻¹ x‖ ≤ ‖x‖ / √λ`. -/
theorem _root_.ContinuousLinearMap.exists_continuousLinearEquiv_comp_adjoint_eq_two_inv_smul_add
    [CompleteSpace V] (A : V →L[𝕜] V) {lam : ℝ} (hlam : 0 < lam)
    (hpos : ∀ ξ : V, lam * ‖ξ‖ ^ 2 ≤ re ⟪A ξ, ξ⟫_𝕜) {ν : V} :
    ∃ e : V ≃L[𝕜] V,
      (e : V →L[𝕜] V) ∘L (e : V →L[𝕜] V).adjoint = (2⁻¹ : 𝕜) • (A + A.adjoint) ∧
      (∃ c : ℝ, 0 < c ∧ (e : V →L[𝕜] V).adjoint ν = (c : 𝕜) • ν) ∧
      ∀ x : V, ‖e.symm x‖ ≤ (√lam)⁻¹ * ‖x‖ :=
  ContinuousLinearMap.exists_continuousLinearEquiv_comp_adjoint_eq_of_isSymmetric _
    A.isSymmetric_two_inv_smul_add_adjoint hlam fun ξ =>
      (hpos ξ).trans_eq (A.re_inner_two_inv_smul_add_adjoint_apply ξ).symm

/-- A symmetric positive-definite bilinear form on a finite-dimensional real vector space `W`
transfers along a linear equivalence to the inner product of any real inner product space `E` of
the same finite dimension. -/
theorem exists_linearEquiv_inner_eq_of_posDef {W E : Type*} [AddCommGroup W] [Module ℝ W]
    [FiniteDimensional ℝ W] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (hdim : Module.finrank ℝ W = Module.finrank ℝ E) {B : LinearMap.BilinForm ℝ W}
    (hpos : B.toQuadraticMap.PosDef) (hsymm : B.IsSymm) :
    ∃ φ : W ≃ₗ[ℝ] E, ∀ x y, ⟪φ x, φ y⟫_ℝ = B x y := by
  let core : InnerProductSpace.Core ℝ W :=
    { inner x y := B x y
      conj_inner_symm x y := by simp [hsymm.eq y x]
      re_inner_nonneg x := hpos.nonneg x
      add_left x y z := by simp
      smul_left x y r := by simp
      definite x hx := hpos.anisotropic x hx }
  let _ : NormedAddCommGroup W := core.toNormedAddCommGroup
  let _ : InnerProductSpace ℝ W := InnerProductSpace.ofCore core.toCore
  let φ : W ≃ₗᵢ[ℝ] E :=
    (stdOrthonormalBasis ℝ W).equiv (stdOrthonormalBasis ℝ E) (finCongr hdim)
  refine ⟨φ.toLinearEquiv, fun x y ↦ ?_⟩
  rw [LinearIsometryEquiv.coe_toLinearEquiv]
  exact φ.inner_map_map x y

end TauCeti

namespace ContinuousLinearMap

open scoped Matrix in
/-- The matrix of the symmetric part `(A + A†) / 2` of a positive definite endomorphism `A` of a
real inner product space in an orthonormal basis is positive definite. -/
theorem posDef_toMatrix_symmPart {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] {A : V →L[ℝ] V} (hA : ∀ ξ, ξ ≠ 0 → 0 < ⟪A ξ, ξ⟫_ℝ) {ι : Type*}
    [Fintype ι] [DecidableEq ι] (b : OrthonormalBasis ι ℝ V) :
    (LinearMap.toMatrix b.toBasis b.toBasis
      (((2⁻¹ : ℝ) • (A + A.adjoint) : V →L[ℝ] V) : V →ₗ[ℝ] V)).PosDef := by
  set S : V →L[ℝ] V := (2⁻¹ : ℝ) • (A + A.adjoint)
  have hS : ∀ x y, ⟪S x, y⟫_ℝ = ⟪x, S y⟫_ℝ := A.isSymmetric_two_inv_smul_add_adjoint
  refine Matrix.posDef_iff_dotProduct_mulVec.2
    ⟨(LinearMap.isHermitian_toMatrix_iff b).2 A.isSymmetric_two_inv_smul_add_adjoint,
      fun x hx => ?_⟩
  set v : V := b.repr.symm (WithLp.toLp 2 x)
  have hxv : ∀ i, x i = ⟪b i, v⟫_ℝ := fun i => by
    rw [← b.repr_apply_apply, LinearIsometryEquiv.apply_symm_apply]
  have hv : v ≠ 0 := fun h => hx (funext fun i => by rw [hxv i, h, inner_zero_right]; rfl)
  calc 0 < ⟪A v, v⟫_ℝ := hA v hv
    _ = ⟪S v, v⟫_ℝ := (A.re_inner_two_inv_smul_add_adjoint_apply v).symm
    _ = ∑ i, ⟪v, b i⟫_ℝ * ∑ j, ⟪S (b i), b j⟫_ℝ * ⟪b j, v⟫_ℝ := by
        simp only [b.sum_inner_mul_inner]
        simp only [hS, b.sum_inner_mul_inner]
    _ = star x ⬝ᵥ (LinearMap.toMatrix b.toBasis b.toBasis (S : V →ₗ[ℝ] V) *ᵥ x) := by
        simp only [dotProduct, Matrix.mulVec, star_trivial,
          LinearMap.toMatrix_orthonormalBasis_apply, coe_coe, ← hS, hxv, real_inner_comm v]

section ConjSymmPart

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- After the change of variables `e` with `e e† = (A + A†) / 2` and `‖e⁻¹‖ ≤ λ^{-1/2}`, the
symmetric part of `a` becomes `e⁻¹ ((a + a†) / 2) e⁻†`, which lies within `‖a - A‖ / λ` of the
identity. -/
theorem norm_conj_symmPart_sub_id_le (a : V →L[ℝ] V) {lam : ℝ} (hlam : 0 < lam)
    {A : V →L[ℝ] V} (e : V ≃L[ℝ] V)
    (hee : (e : V →L[ℝ] V) ∘L (e : V →L[ℝ] V).adjoint = (2⁻¹ : ℝ) • (A + A.adjoint))
    (he : ∀ x, ‖e.symm x‖ ≤ (√lam)⁻¹ * ‖x‖) :
    ‖(e.symm : V →L[ℝ] V) ∘L ((2⁻¹ : ℝ) • (a + a.adjoint)) ∘L (e.symm : V →L[ℝ] V).adjoint -
      ContinuousLinearMap.id ℝ V‖ ≤ lam⁻¹ * ‖a - A‖ := by
  set N : V →L[ℝ] V := (e.symm : V →L[ℝ] V)
  set M : V →L[ℝ] V := (e : V →L[ℝ] V)
  have hNM : N ∘L M = ContinuousLinearMap.id ℝ V := by ext x; simp [N, M]
  -- `e⁻¹ ((A + A†) / 2) e⁻† = e⁻¹ e e† e⁻† = 1`.
  have hid : N ∘L ((2⁻¹ : ℝ) • (A + A.adjoint)) ∘L N.adjoint = ContinuousLinearMap.id ℝ V := by
    rw [← hee]
    calc N ∘L (M ∘L M.adjoint) ∘L N.adjoint = (N ∘L M) ∘L (N ∘L M).adjoint := by
          rw [ContinuousLinearMap.adjoint_comp]; simp only [ContinuousLinearMap.comp_assoc]
      _ = _ := by rw [hNM, ContinuousLinearMap.adjoint_id, ContinuousLinearMap.id_comp]
  set B := a - A
  have hsub : N ∘L ((2⁻¹ : ℝ) • (a + a.adjoint)) ∘L N.adjoint - ContinuousLinearMap.id ℝ V =
      N ∘L ((2⁻¹ : ℝ) • (B + B.adjoint)) ∘L N.adjoint := by
    rw [← hid, ← ContinuousLinearMap.comp_sub, ← ContinuousLinearMap.sub_comp, ← smul_sub,
      show a + a.adjoint - (A + A.adjoint) = B + B.adjoint by simp only [B, map_sub]; abel]
  have hN : ‖N‖ ≤ (√lam)⁻¹ := N.opNorm_le_bound (by positivity) he
  have hX : ‖(2⁻¹ : ℝ) • (B + B.adjoint)‖ ≤ ‖B‖ := by
    rw [norm_smul, Real.norm_of_nonneg (by norm_num)]
    calc 2⁻¹ * ‖B + B.adjoint‖ ≤ 2⁻¹ * (‖B‖ + ‖B‖) := by
          gcongr
          exact (norm_add_le _ _).trans_eq (by rw [LinearIsometryEquiv.norm_map])
      _ = ‖B‖ := by ring
  rw [hsub]
  calc ‖N ∘L ((2⁻¹ : ℝ) • (B + B.adjoint)) ∘L N.adjoint‖
      ≤ ‖N‖ * (‖(2⁻¹ : ℝ) • (B + B.adjoint)‖ * ‖N‖) := by
        refine (N.opNorm_comp_le _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
        exact (ContinuousLinearMap.opNorm_comp_le _ _).trans_eq
          (by rw [LinearIsometryEquiv.norm_map])
    _ ≤ (√lam)⁻¹ * (‖B‖ * (√lam)⁻¹) := by gcongr
    _ = lam⁻¹ * ‖B‖ := by
        rw [mul_comm ‖B‖, ← mul_assoc, ← mul_inv, Real.mul_self_sqrt hlam.le]

/-- In the setting of `ContinuousLinearMap.norm_conj_symmPart_sub_id_le`, if `‖a - A‖ ≤ δ λ`, then
the transformed coefficient `e⁻¹ ((a + a†) / 2) e⁻†` lies within `δ` of the identity. -/
theorem norm_conj_symmPart_sub_id_le_of_norm_sub_le {a A : V →L[ℝ] V} {lam δ : ℝ}
    (hlam : 0 < lam) (e : V ≃L[ℝ] V)
    (hee : (e : V →L[ℝ] V) ∘L (e : V →L[ℝ] V).adjoint = (2⁻¹ : ℝ) • (A + A.adjoint))
    (he : ∀ x, ‖e.symm x‖ ≤ (√lam)⁻¹ * ‖x‖) (h : ‖a - A‖ ≤ δ * lam) :
    ‖(e.symm : V →L[ℝ] V) ∘L ((2⁻¹ : ℝ) • (a + a.adjoint)) ∘L (e.symm : V →L[ℝ] V).adjoint -
      ContinuousLinearMap.id ℝ V‖ ≤ δ :=
  (a.norm_conj_symmPart_sub_id_le hlam e hee he).trans
    ((inv_mul_le_iff₀ hlam).2 (by rwa [mul_comm]))

/-- The coefficient `N ((X + X†) / 2) N†` of an equation `tr (X D²u) = f` after a linear change of
variables depends continuously on `X`. -/
theorem continuous_conj_symmPart (N : V →L[ℝ] V) :
    Continuous fun X : V →L[ℝ] V ↦ N ∘L ((2⁻¹ : ℝ) • (X + X.adjoint)) ∘L N.adjoint :=
  continuous_const.clm_comp
    (((continuous_id.add ContinuousLinearMap.adjoint.continuous).const_smul (2⁻¹ : ℝ)).clm_comp
      continuous_const)

end ConjSymmPart

end ContinuousLinearMap
