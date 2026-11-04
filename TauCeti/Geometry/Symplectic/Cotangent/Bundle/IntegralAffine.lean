/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Torus
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Fiberwise

/-!
# Integral affine changes of action–angle coordinates

Let `p > 0` and let `Tⁿ = ι → AddCircle p` be the torus with angle coordinates `θ` and coordinate
time forms `dθ_i` (`TauCeti.torusTimeForm`). Its cotangent bundle `T*Tⁿ` is the model of
action–angle coordinates: a covector `ξ` over `θ` has actions `I_i = ξ(e_i)`, the values of `ξ` on
the coordinate vectors, the Liouville form is `λ = ∑ I_i dθ_i`, and the canonical symplectic form is
`ω = -dλ = ∑ dθ_i ∧ dI_i`.

The angle coordinates of an action–angle chart depend on a choice of basis of the period lattice,
and the actions on that basis and on an additive constant. This file shows that the corresponding
changes of coordinates are symplectomorphisms of `T*Tⁿ`. Let `A ∈ GL(ι, ℤ)` and `b : ι → ℝ`.

* The integer matrix `A` acts on the torus by `θ ↦ A θ`
  (`AddCircle.instDistribMulActionGeneralLinearGroup`), hence on `T*Tⁿ` by cotangent lifts, which
  preserve `λ` and `ω` (`TauCeti.CotangentBundle.mpullback_smul_liouvilleForm`,
  `TauCeti.CotangentBundle.mpullback_smul_symplecticForm`). The lifted action sends a covector
  `ξ` to `ξ ∘ A⁻¹` (`TauCeti.CotangentBundle.generalLinearGroup_smul_snd_apply`), so it changes
  the actions by the inverse transpose, `I' = A⁻ᵀ I`
  (`TauCeti.CotangentBundle.generalLinearGroup_smul_snd_apply_single`). As `A` ranges over
  `GL(ι, ℤ)`, so does `A⁻ᵀ`.
* The **integral affine change** `Φ_(A, b)` (`TauCeti.CotangentBundle.integralAffineDiffeomorph`)
  is this cotangent lift followed by the fibre translation by the closed one-form
  `∑ j, b j • dθ_j`. In action–angle coordinates

  `Φ_(A, b)(θ, I) = (A θ, A⁻ᵀ I + b)`

  (`TauCeti.CotangentBundle.proj_integralAffineDiffeomorph`,
  `TauCeti.CotangentBundle.integralAffineDiffeomorph_snd_apply_single`).

The integral affine changes preserve `ω`
(`TauCeti.CotangentBundle.mpullback_integralAffineDiffeomorph_symplecticForm`) and change `λ` by
the pullback of a closed one-form with constant coefficients,
`Φ_(A, b)^* λ = λ + π^* (∑ k, (Aᵀ b)_k dθ_k)`
(`TauCeti.CotangentBundle.mpullback_integralAffineDiffeomorph_liouvilleForm`). The shift `b` is
visible on the zero section, which `Φ_(A, b)` carries onto the graph of `∑ j, b j • dθ_j`
(`TauCeti.CotangentBundle.integralAffineDiffeomorph_zeroSection`); that graph is an exact
Lagrangian section only for `b = 0`
(`TauCeti.CotangentBundle.exists_isExactLagrangianMap_section_sum_smul_torusTimeForm_iff`). The
changes compose as integral affine maps of the actions:
`Φ_(A, b) ∘ Φ_(A', b') = Φ_(A A', A⁻ᵀ b' + b)`
(`TauCeti.CotangentBundle.integralAffineDiffeomorph_trans`), `Φ_(1, 0)` is the identity, and
the inverse of `Φ_(A, b)` is `Φ_(A⁻¹, -Aᵀ b)`
(`TauCeti.CotangentBundle.integralAffineDiffeomorph_symm`).

These pullback identities are instances of the general ones for a cotangent lift followed by a
fibre translation
(`Diffeomorph.mpullback_cotangent_trans_vectorBundleTranslateDiffeomorph_liouvilleForm`,
`Diffeomorph.mpullback_cotangent_trans_vectorBundleTranslateDiffeomorph_symplecticForm`).

## Main definitions

* `TauCeti.CotangentBundle.integralAffineDiffeomorph p A b`: the integral affine change of
  action–angle coordinates `(θ, I) ↦ (A θ, A⁻ᵀ I + b)` of `T*Tⁿ`.

## Main results

* `TauCeti.CotangentBundle.generalLinearGroup_smul_snd_apply_single`: the cotangent lift of
  `θ ↦ A θ` changes the actions by `A⁻ᵀ`.
* `TauCeti.CotangentBundle.integralAffineDiffeomorph_snd_apply_single`: the actions transform as
  `I' = A⁻ᵀ I + b`.
* `TauCeti.CotangentBundle.mpullback_integralAffineDiffeomorph_symplecticForm`: the change is a
  symplectomorphism of `(T*Tⁿ, ω)`.
* `TauCeti.CotangentBundle.mpullback_integralAffineDiffeomorph_liouvilleForm`: its effect on the
  Liouville form.
* `TauCeti.CotangentBundle.integralAffineDiffeomorph_trans`,
  `TauCeti.CotangentBundle.integralAffineDiffeomorph_symm`: the composition law and the inverse.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Sections 49–50 (action–angle variables and the choice of basis
  of the period lattice).
* J. J. Duistermaat, *On global action-angle coordinates*, Comm. Pure Appl. Math. 33 (1980),
  687–706, Section 1 (integral affine changes of action coordinates).
-/

public section

noncomputable section

open Bundle Matrix
open scoped Manifold ContDiff

namespace TauCeti

namespace CotangentBundle

variable (p : ℝ) [Fact (0 < p)] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The cotangent lift of an integral linear automorphism -/

/-- The cotangent lift of the action of an integer matrix `A` on the torus sends a covector `ξ` to
`ξ ∘ A⁻¹`: it evaluates a tangent vector `v` as `ξ` evaluates `A⁻¹ *ᵥ v`. -/
@[simp]
theorem generalLinearGroup_smul_snd_apply (A : GL ι ℤ)
    (z : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p))
    (v : ι → ℝ) :
    (A • z).2 v = z.2 (((A⁻¹ : GL ι ℤ) : Matrix ι ι ℤ).map ((↑) : ℤ → ℝ) *ᵥ v) :=
  (smul_snd_apply A z v).trans
    (congrArg z.2 (AddCircle.mfderiv_generalLinearGroup_smul_apply p A⁻¹ _ v))

/-- **The cotangent lift of an integral linear automorphism changes the actions by the inverse
transpose.** The action `I_i = ξ(e_i)` of `A • ξ` is `∑ j, A⁻¹ j i * I_j`. -/
theorem generalLinearGroup_smul_snd_apply_single (A : GL ι ℤ)
    (z : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p)) (i : ι) :
    (A • z).2 (Pi.single i 1) =
      ∑ j, (((A⁻¹ : GL ι ℤ) : Matrix ι ι ℤ) j i : ℝ) * z.2 (Pi.single j 1) := by
  refine (generalLinearGroup_smul_snd_apply p A z _).trans ?_
  rw [Matrix.mulVec_single_one]
  -- The `i`-th column of `A⁻¹` has coordinates `A⁻¹ j i`.
  refine (LinearMap.pi_apply_eq_sum_univ z.2.toLinearMap _).trans ?_
  simp only [← Pi.single_apply, Pi.single_comm]
  simp only [smul_eq_mul, Matrix.col_apply, Matrix.map_apply]
  -- `z.2` is a covector on the tangent space, a type synonym of `ι → ℝ`, so
  -- `ContinuousLinearMap.coe_coe` does not match its coercion to a linear map.
  rfl

/-! ### Integral affine changes of action–angle coordinates -/

/-- Casting invertible integer matrices to real matrices is multiplicative: it is the coercion of
`Matrix.GeneralLinearGroup.map (Int.castRingHom ℝ)`. -/
private theorem map_intCast_mul (A B : GL ι ℤ) :
    ((A * B : GL ι ℤ) : Matrix ι ι ℤ).map ((↑) : ℤ → ℝ) =
      (A : Matrix ι ι ℤ).map ((↑) : ℤ → ℝ) * (B : Matrix ι ι ℤ).map ((↑) : ℤ → ℝ) :=
  congrArg Units.val (Matrix.GeneralLinearGroup.map_mul (Int.castRingHom ℝ) A B)

/-- Casting the identity integer matrix to a real matrix gives the identity. -/
private theorem map_intCast_one : ((1 : GL ι ℤ) : Matrix ι ι ℤ).map ((↑) : ℤ → ℝ) = 1 :=
  congrArg Units.val (Matrix.GeneralLinearGroup.map_one (Int.castRingHom ℝ))

/-- The **integral affine change of action–angle coordinates** of `T*Tⁿ` given by an integer matrix
`A ∈ GL(ι, ℤ)` and a shift `b : ι → ℝ`: the cotangent lift of `θ ↦ A θ` followed by the fibre
translation by the closed one-form `∑ j, b j • dθ_j`. In action–angle coordinates it is
`(θ, I) ↦ (A θ, A⁻ᵀ I + b)`. -/
def integralAffineDiffeomorph (A : GL ι ℤ) (b : ι → ℝ) :
    CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p) ≃ₘ⟮
      (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ),
      (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)⟯
    CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p) :=
  (Diffeomorph.constSmul (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) ∞ A).cotangent.trans
    (vectorBundleTranslateDiffeomorph
      (SmoothForm.degreeOneEquiv (∑ j, b j • torusTimeForm (fun _ ↦ p) j))
      (SmoothForm.degreeOneEquiv (∑ j, b j • torusTimeForm (fun _ ↦ p) j)).contMDiff)

/-- The integral affine change is the cotangent-lifted action of `A` followed by the translation
of the fibres by the closed one-form `∑ j, b j • dθ_j`. -/
theorem integralAffineDiffeomorph_apply (A : GL ι ℤ) (b : ι → ℝ)
    (z : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p)) :
    integralAffineDiffeomorph p A b z =
      vectorBundleTranslateDiffeomorph
        (SmoothForm.degreeOneEquiv (∑ j, b j • torusTimeForm (fun _ ↦ p) j))
        (SmoothForm.degreeOneEquiv (∑ j, b j • torusTimeForm (fun _ ↦ p) j)).contMDiff (A • z) := by
  rw [integralAffineDiffeomorph, Diffeomorph.coe_trans, Function.comp_apply, ← smul_def]

/-- The integral affine change covers the action of `A` on the torus: it changes the angles by
`θ ↦ A θ`. -/
@[simp]
theorem proj_integralAffineDiffeomorph (A : GL ι ℤ) (b : ι → ℝ)
    (z : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p)) :
    (integralAffineDiffeomorph p A b z).proj = A • z.proj := by
  rw [integralAffineDiffeomorph_apply, vectorBundleTranslateDiffeomorph_apply]
  exact proj_smul A z

/-- The integral affine change sends a covector `ξ` to `ξ ∘ A⁻¹ + ∑ j, b j • dθ_j`. -/
@[simp]
theorem integralAffineDiffeomorph_snd_apply (A : GL ι ℤ) (b : ι → ℝ)
    (z : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p))
    (v : ι → ℝ) :
    (integralAffineDiffeomorph p A b z).2 v =
      z.2 (((A⁻¹ : GL ι ℤ) : Matrix ι ι ℤ).map ((↑) : ℤ → ℝ) *ᵥ v) + ∑ j, b j * v j := by
  rw [integralAffineDiffeomorph_apply, vectorBundleTranslateDiffeomorph_apply]
  -- The translated covector is the sum of the lifted covector and the value of the form.
  exact congrArg₂ (· + ·) (generalLinearGroup_smul_snd_apply p A z v)
    ((SmoothForm.degreeOneEquiv_apply_apply _ _ v).trans
      (sum_smul_torusTimeForm_apply (fun _ ↦ p) b (A • z).proj fun _ ↦ v))

/-- **The actions transform by an integral affine map.** The action `I_i = ξ(e_i)` of the image of
`ξ` under the integral affine change is `∑ j, A⁻¹ j i * I_j + b i`: in action–angle coordinates the
change is `(θ, I) ↦ (A θ, A⁻ᵀ I + b)`. -/
theorem integralAffineDiffeomorph_snd_apply_single (A : GL ι ℤ) (b : ι → ℝ)
    (z : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p)) (i : ι) :
    (integralAffineDiffeomorph p A b z).2 (Pi.single i 1) =
      ∑ j, (((A⁻¹ : GL ι ℤ) : Matrix ι ι ℤ) j i : ℝ) * z.2 (Pi.single j 1) + b i := by
  rw [integralAffineDiffeomorph_apply, vectorBundleTranslateDiffeomorph_apply]
  -- The lifted covector gives `A⁻ᵀ I`; the translating form contributes `b i`.
  exact congrArg₂ (· + ·) (generalLinearGroup_smul_snd_apply_single p A z i)
    ((SmoothForm.degreeOneEquiv_apply_apply _ _ _).trans
      ((sum_smul_torusTimeForm_apply (fun _ ↦ p) b (A • z).proj _).trans
        (by simp [Pi.single_apply])))

/-- The integral affine change carries the zero covector over `θ` to the value at `A θ` of the
closed one-form `∑ j, b j • dθ_j`: it maps the zero section onto the graph of this form. -/
theorem integralAffineDiffeomorph_zeroSection (A : GL ι ℤ) (b : ι → ℝ) (x : ι → AddCircle p) :
    integralAffineDiffeomorph p A b
        (zeroSection ((ι → ℝ) →L[ℝ] ℝ)
          (fun y : ι → AddCircle p ↦
            TangentSpace (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) y →L[ℝ] ℝ) x) =
      TotalSpace.mk' ((ι → ℝ) →L[ℝ] ℝ) (A • x)
        (SmoothForm.degreeOneEquiv (∑ j, b j • torusTimeForm (fun _ ↦ p) j) (A • x)) := by
  rw [integralAffineDiffeomorph_apply, vectorBundleTranslateDiffeomorph_apply, smul_zeroSection]
  exact congrArg (TotalSpace.mk' ((ι → ℝ) →L[ℝ] ℝ) (A • x)) (zero_add _)

/-- **The Liouville form under an integral affine change.** The integral affine change of
action–angle coordinates pulls the Liouville form `λ` back to `λ + π^* (∑ k, (Aᵀ b)_k • dθ_k)`,
the sum of `λ` and the pullback of a closed one-form with constant coefficients. -/
theorem mpullback_integralAffineDiffeomorph_liouvilleForm (A : GL ι ℤ) (b : ι → ℝ) :
    SmoothForm.mpullback _ (integralAffineDiffeomorph p A b).contMDiff
        (liouvilleForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p)) =
      liouvilleForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p) +
        SmoothForm.mpullback (TotalSpace.proj :
            CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p) →
              ι → AddCircle p) (contMDiff_proj _)
          (∑ k, (((↑A : Matrix ι ι ℤ).map ((↑) : ℤ → ℝ))ᵀ *ᵥ b) k •
            torusTimeForm (fun _ ↦ p) k) := by
  have h := Diffeomorph.mpullback_cotangent_trans_vectorBundleTranslateDiffeomorph_liouvilleForm
    (Diffeomorph.constSmul (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) ∞ A)
    (∑ j, b j • torusTimeForm (fun _ ↦ p) j)
  simp only [Diffeomorph.coe_constSmul] at h
  -- The action pulls `∑ j, b j • dθ_j` back to `∑ k, (Aᵀ b)_k • dθ_k`.
  rw [mpullback_generalLinearGroup_smul_sum_smul_torusTimeForm] at h
  exact h

/-- **Integral affine changes are symplectomorphisms.** The integral affine change of action–angle
coordinates pulls the canonical symplectic form `ω = ∑ dθ_i ∧ dI_i` of `T*Tⁿ` back to itself. -/
@[simp]
theorem mpullback_integralAffineDiffeomorph_symplecticForm (A : GL ι ℤ) (b : ι → ℝ) :
    SmoothForm.mpullback _ (integralAffineDiffeomorph p A b).contMDiff
        (symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p)) =
      symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p) :=
  -- The translating one-form has constant coefficients, so it is closed.
  Diffeomorph.mpullback_cotangent_trans_vectorBundleTranslateDiffeomorph_symplecticForm
    (Diffeomorph.constSmul (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) ∞ A)
    (isClosed_sum_smul_torusTimeForm (fun _ ↦ p) b)

/-- The integral affine change with `A = 1` and `b = 0` is the identity. -/
@[simp]
theorem integralAffineDiffeomorph_one_zero :
    integralAffineDiffeomorph p (1 : GL ι ℤ) 0 = Diffeomorph.refl _ _ _ :=
  Diffeomorph.ext fun z ↦ CotangentBundle.ext (by simp) fun v ↦
    (integralAffineDiffeomorph_snd_apply p 1 0 z v).trans <| by
      simp only [inv_one, map_intCast_one, Pi.zero_apply, zero_mul, Finset.sum_const_zero,
        add_zero]
      exact congrArg z.2 (Matrix.one_mulVec v)

/-- **Composition of integral affine changes.** Applying `Φ_(A', b')` and then `Φ_(A, b)` is the
integral affine change `Φ_(A A', A⁻ᵀ b' + b)`, matching the composite
`I ↦ A⁻ᵀ (A'⁻ᵀ I + b') + b` of the action transformations. -/
theorem integralAffineDiffeomorph_trans (A A' : GL ι ℤ) (b b' : ι → ℝ) :
    (integralAffineDiffeomorph p A' b').trans (integralAffineDiffeomorph p A b) =
      integralAffineDiffeomorph p (A * A')
        ((((A⁻¹ : GL ι ℤ) : Matrix ι ι ℤ).map ((↑) : ℤ → ℝ))ᵀ *ᵥ b' + b) :=
  Diffeomorph.ext fun z ↦ CotangentBundle.ext (by simp [mul_smul]) fun v ↦ by
    rw [Diffeomorph.coe_trans, Function.comp_apply]
    refine ((integralAffineDiffeomorph_snd_apply p A b _ v).trans ?_).trans
      (integralAffineDiffeomorph_snd_apply p (A * A') _ z v).symm
    refine (congrArg (· + ∑ j, b j * v j)
      (integralAffineDiffeomorph_snd_apply p A' b' z _)).trans ?_
    -- The linear parts compose to `(A A')⁻¹`, and the shift `b'` is carried along by `A⁻ᵀ`.
    have hz (w : ι → ℝ) : ((A'⁻¹ : GL ι ℤ) : Matrix ι ι ℤ).map ((↑) : ℤ → ℝ) *ᵥ
          (((A⁻¹ : GL ι ℤ) : Matrix ι ι ℤ).map ((↑) : ℤ → ℝ) *ᵥ w) =
        (((A * A')⁻¹ : GL ι ℤ) : Matrix ι ι ℤ).map ((↑) : ℤ → ℝ) *ᵥ w := by
      rw [Matrix.mulVec_mulVec, _root_.mul_inv_rev, map_intCast_mul]
    have hb (w : ι → ℝ) :
        ∑ j, b' j * ((((A⁻¹ : GL ι ℤ) : Matrix ι ι ℤ).map ((↑) : ℤ → ℝ)) *ᵥ w) j =
          ∑ j, ((((A⁻¹ : GL ι ℤ) : Matrix ι ι ℤ).map ((↑) : ℤ → ℝ))ᵀ *ᵥ b') j * w j := by
      -- Both sides are dot products: `b' ⬝ᵥ (M *ᵥ w) = (b' ᵥ* M) ⬝ᵥ w`.
      rw [Matrix.mulVec_transpose]
      exact Matrix.dotProduct_mulVec b' _ w
    rw [congrArg z.2 (hz v), hb v, add_assoc, ← Finset.sum_add_distrib]
    simp only [Pi.add_apply, add_mul]

/-- **Inverse of an integral affine change.** The inverse of `Φ_(A, b)` is the integral affine
change `Φ_(A⁻¹, -Aᵀ b)`, matching the inverse `I ↦ Aᵀ (I - b)` of the action transformation
`I ↦ A⁻ᵀ I + b`. -/
@[simp]
theorem integralAffineDiffeomorph_symm (A : GL ι ℤ) (b : ι → ℝ) :
    (integralAffineDiffeomorph p A b).symm =
      integralAffineDiffeomorph p A⁻¹ (-(((A : Matrix ι ι ℤ).map ((↑) : ℤ → ℝ))ᵀ *ᵥ b)) := by
  -- `Φ_(A, b) ∘ Φ_(A⁻¹, -Aᵀ b) = Φ_(1, 0)`, the identity: the new shift is
  -- `-(A⁻ᵀ Aᵀ b) + b = -((A A⁻¹)ᵀ b) + b = 0`.
  have h : (integralAffineDiffeomorph p A⁻¹ (-(((A : Matrix ι ι ℤ).map ((↑) : ℤ → ℝ))ᵀ *ᵥ b))).trans
      (integralAffineDiffeomorph p A b) = Diffeomorph.refl _ _ _ := by
    have hb : (((A⁻¹ : GL ι ℤ) : Matrix ι ι ℤ).map ((↑) : ℤ → ℝ))ᵀ *ᵥ
        -(((A : Matrix ι ι ℤ).map ((↑) : ℤ → ℝ))ᵀ *ᵥ b) + b = 0 := by
      rw [Matrix.mulVec_neg, Matrix.mulVec_mulVec, ← Matrix.transpose_mul, ← map_intCast_mul]
      simp
    rw [integralAffineDiffeomorph_trans, mul_inv_cancel, hb, integralAffineDiffeomorph_one_zero]
  exact Diffeomorph.ext fun z ↦
    (congrArg (integralAffineDiffeomorph p A b).symm (DFunLike.congr_fun h z)).symm.trans
      ((integralAffineDiffeomorph p A b).symm_apply_apply _)

end CotangentBundle

end TauCeti
