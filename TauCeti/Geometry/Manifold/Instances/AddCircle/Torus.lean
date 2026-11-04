/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import TauCeti.Geometry.Manifold.Algebra.SMul
public import TauCeti.Geometry.Manifold.Instances.AddCircle
public import TauCeti.Geometry.Manifold.MFDeriv.Pi

/-!
# Integral linear automorphisms of a torus

Let `p > 0` and let `Tⁿ = ι → AddCircle p` be the torus with all periods equal to `p`, a smooth
manifold modelled on `ModelWithCorners.pi fun _ ↦ 𝓘(ℝ)` whose tangent space at every point is
`ι → ℝ`. An invertible integer matrix `A ∈ GL(ι, ℤ)` acts on `Tⁿ` by

`(A • x) i = ∑ j, A i j • x j`

(`AddCircle.generalLinearGroup_smul_apply`), each `A i j • x j` being integer multiplication in the
circle. This is an action of the group `GL(ι, ℤ)` by additive maps
(`AddCircle.instDistribMulActionGeneralLinearGroup`), and each `A` acts by smooth maps
(`AddCircle.instContMDiffConstSMulGeneralLinearGroup`). So `x ↦ A • x` is a diffeomorphism of the
torus, with inverse `x ↦ A⁻¹ • x` (`Diffeomorph.constSmul`), and the cotangent bundle `T*Tⁿ`
inherits the cotangent-lifted action (`TauCeti.CotangentBundle.instMulAction`).

The covering map `(ι → ℝ) → Tⁿ`, `t ↦ ([t i])ᵢ`, has derivative the identity of `ι → ℝ` at every
point (`AddCircle.hasMFDerivAt_coe_pi`), and it intertwines the action of `A` on the torus with
multiplication of real vectors by the matrix `A` (`AddCircle.generalLinearGroup_smul_coe_pi`).
Hence the derivative of `x ↦ A • x` at every point is the matrix `A`, acting on `ι → ℝ`
(`AddCircle.mfderiv_generalLinearGroup_smul_apply`). Choosing a basis of the period lattice of a
torus is choosing such an `A`: these maps are the changes of angle coordinates of action–angle
charts.

## Main results

* `AddCircle.instDistribMulActionGeneralLinearGroup`: the action of `GL(ι, ℤ)` on
  `ι → AddCircle p` by additive maps.
* `AddCircle.instContMDiffConstSMulGeneralLinearGroup`: it acts by smooth maps.
* `AddCircle.hasMFDerivAt_coe_pi`: the covering map `(ι → ℝ) → Tⁿ` has derivative the identity.
* `AddCircle.hasMFDerivAt_generalLinearGroup_smul`,
  `AddCircle.mfderiv_generalLinearGroup_smul_apply`: the derivative of `x ↦ A • x` is the matrix
  `A`.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Section 50 (changes of the basis of the period lattice).
-/

public section

noncomputable section

open Function Matrix
open scoped Manifold ContDiff

namespace AddCircle

variable (p : ℝ) {ι : Type*} [Fintype ι]

/-! ### The covering map -/

section Cover

variable [Fact (0 < p)]

/-- The covering map `(ι → ℝ) → (ι → AddCircle p)`, `t ↦ ([t i])ᵢ`, has derivative the identity of
`ι → ℝ`, the tangent spaces of the torus being read in its product charts. -/
theorem hasMFDerivAt_coe_pi (t : ι → ℝ) :
    HasMFDerivAt 𝓘(ℝ, ι → ℝ) (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      (fun t : ι → ℝ ↦ fun i ↦ (t i : AddCircle p)) t (ContinuousLinearMap.id ℝ (ι → ℝ)) :=
  (TauCeti.hasMFDerivAt_pi (M := fun _ : ι ↦ AddCircle p) (I := fun _ ↦ 𝓘(ℝ))
    (f := fun t : ι → ℝ ↦ fun i ↦ (t i : AddCircle p)) fun i ↦ (hasMFDerivAt_coe p (t i)).comp t
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i).hasMFDerivAt).congr_mfderiv <| by
    -- The product of the coordinate projections is the identity of `ι → ℝ`.
    ext v i
    rfl

end Cover

/-! ### The action of `GL(ι, ℤ)` -/

variable [DecidableEq ι]

/-- An integer matrix `A` acts on the torus `ι → AddCircle p` by `(A • x) i = ∑ j, A i j • x j`. -/
instance instSMulGeneralLinearGroup : SMul (GL ι ℤ) (ι → AddCircle p) where
  smul A x i := ∑ j, (A : Matrix ι ι ℤ) i j • x j

/-- The `i`-th coordinate of `A • x` is `∑ j, A i j • x j`. -/
@[simp]
theorem generalLinearGroup_smul_apply (A : GL ι ℤ) (x : ι → AddCircle p) (i : ι) :
    (A • x) i = ∑ j, (A : Matrix ι ι ℤ) i j • x j :=
  (rfl)

/-- The invertible integer matrices act on the torus `ι → AddCircle p` by additive maps, by matrix
multiplication of the coordinates. -/
instance instDistribMulActionGeneralLinearGroup : DistribMulAction (GL ι ℤ) (ι → AddCircle p) where
  one_smul x := funext fun i ↦ by
    simp [generalLinearGroup_smul_apply, Matrix.one_apply, ite_smul]
  mul_smul A B x := funext fun i ↦ by
    simp only [generalLinearGroup_smul_apply, Units.val_mul, Matrix.mul_apply, Finset.sum_smul,
      Finset.smul_sum, mul_smul]
    exact Finset.sum_comm
  smul_zero A := funext fun i ↦ by simp [generalLinearGroup_smul_apply]
  smul_add A x y := funext fun i ↦ by
    simp only [generalLinearGroup_smul_apply, Pi.add_apply, smul_add, Finset.sum_add_distrib]

/-- The covering map `(ι → ℝ) → (ι → AddCircle p)` intertwines the action of an integer matrix `A`
on the torus with the multiplication of real vectors by `A`. -/
theorem generalLinearGroup_smul_coe_pi (A : GL ι ℤ) (t : ι → ℝ) :
    A • (fun i ↦ (t i : AddCircle p)) =
      fun i ↦ (((A : Matrix ι ι ℤ).map ((↑) : ℤ → ℝ) *ᵥ t) i : AddCircle p) :=
  funext fun i ↦ by
    simp only [generalLinearGroup_smul_apply, Matrix.mulVec, dotProduct, Matrix.map_apply,
      ← zsmul_eq_mul]
    exact (map_sum (QuotientAddGroup.mk' (AddSubgroup.zmultiples p)) _ _).symm.trans <| by
      simp only [QuotientAddGroup.mk'_apply]

/-! ### Smoothness and derivative -/

variable [Fact (0 < p)]

/-- Integer matrices act on the torus `ι → AddCircle p` by smooth maps. -/
instance instContMDiffConstSMulGeneralLinearGroup {n : ℕ∞ω} :
    ContMDiffConstSMul (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) n (GL ι ℤ) (ι → AddCircle p) where
  contMDiff_const_smul A := contMDiff_pi_iff.2 fun i ↦ by
    simp only [generalLinearGroup_smul_apply]
    exact ContMDiff.sum fun j _ ↦ (contMDiff_zsmul p n _).comp contMDiff_apply

/-- The derivative of the action of an integer matrix `A` on the torus `ι → AddCircle p` is, at
every point, multiplication of tangent vectors `v : ι → ℝ` by the matrix `A`. -/
theorem hasMFDerivAt_generalLinearGroup_smul (A : GL ι ℤ) (x : ι → AddCircle p) :
    HasMFDerivAt (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      (fun y ↦ A • y) x
      (LinearMap.toContinuousLinearMap (Matrix.toLin' ((A : Matrix ι ι ℤ).map ((↑) : ℤ → ℝ)))) := by
  set L := LinearMap.toContinuousLinearMap (Matrix.toLin' ((A : Matrix ι ι ℤ).map ((↑) : ℤ → ℝ)))
  obtain ⟨t, rfl⟩ : ∃ t : ι → ℝ, (fun i ↦ (t i : AddCircle p)) = x :=
    ⟨fun i ↦ (QuotientAddGroup.mk_surjective (x i)).choose,
      funext fun i ↦ (QuotientAddGroup.mk_surjective (x i)).choose_spec⟩
  -- The action composed with the covering map is the covering map composed with `L`.
  have hcomp : HasMFDerivAt 𝓘(ℝ, ι → ℝ) (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      ((fun y ↦ A • y) ∘ fun t : ι → ℝ ↦ fun i ↦ (t i : AddCircle p)) t L := by
    have hfun : ((fun y ↦ A • y) ∘ fun t : ι → ℝ ↦ fun i ↦ (t i : AddCircle p)) =
        (fun t : ι → ℝ ↦ fun i ↦ (t i : AddCircle p)) ∘ L :=
      funext (generalLinearGroup_smul_coe_pi p A)
    rw [hfun]
    refine ((hasMFDerivAt_coe_pi p (L t)).comp t L.hasMFDerivAt).congr_mfderiv ?_
    -- Composing with the identity of `ι → ℝ` changes nothing.
    ext v
    rfl
  have hd : MDifferentiableAt (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (fun y ↦ A • y) (fun i ↦ (t i : AddCircle p)) :=
    ((contMDiff_const_smul A).mdifferentiableAt (n := 1) one_ne_zero)
  have h := mfderiv_comp t hd (hasMFDerivAt_coe_pi p t).mdifferentiableAt
  rw [hcomp.mfderiv, (hasMFDerivAt_coe_pi p t).mfderiv] at h
  -- Composing with the identity of `ι → ℝ` changes nothing.
  have h' : mfderiv (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      (fun y ↦ A • y) (fun i ↦ (t i : AddCircle p)) = L := by
    rw [h]
    ext v
    rfl
  exact hd.hasMFDerivAt.congr_mfderiv h'

/-- The derivative of the action of an integer matrix `A` on the torus sends a tangent vector
`v : ι → ℝ` to `A *ᵥ v`. -/
@[simp]
theorem mfderiv_generalLinearGroup_smul_apply (A : GL ι ℤ) (x : ι → AddCircle p) (v : ι → ℝ) :
    mfderiv (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      (fun y ↦ A • y) x v = (A : Matrix ι ι ℤ).map ((↑) : ℤ → ℝ) *ᵥ v := by
  rw [(hasMFDerivAt_generalLinearGroup_smul p A x).mfderiv]
  exact Matrix.toLin'_apply _ v

end AddCircle
