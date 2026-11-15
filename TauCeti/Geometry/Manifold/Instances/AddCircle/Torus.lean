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

import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions

/-!
# Covering map and integral linear automorphisms of a torus

For a finite family of positive periods `p i`, the torus `∀ i, AddCircle (p i)` is an analytic
manifold modelled on `ModelWithCorners.pi fun _ ↦ 𝓘(ℝ)` whose tangent space at every point is
`ι → ℝ`. Its covering map `(ι → ℝ) → ∀ i, AddCircle (p i)`, `t ↦ ([t i])ᵢ`, is surjective
(`AddCircle.pi_coe_surjective`), identifies two vectors exactly when they differ by an integer
multiple of the periods (`AddCircle.pi_coe_eq_iff`), has derivative the identity of `ι → ℝ` at
every point (`AddCircle.hasMFDerivAt_pi_coe`, `AddCircle.mfderiv_pi_coe`), and is an analytic local
diffeomorphism (`AddCircle.isLocalDiffeomorph_pi_coe`). On its target, the inverse of every
extended product chart is this covering map (`AddCircle.extChartAt_pi_symm_apply`), so its
derivative is also the identity (`AddCircle.mfderiv_extChartAt_pi_symm`).

When all periods equal `p > 0`, let `Tⁿ = ι → AddCircle p`. An invertible integer matrix
`A ∈ GL(ι, ℤ)` acts on `Tⁿ` by

`(A • x) i = ∑ j, A i j • x j`

(`AddCircle.generalLinearGroup_smul_apply`), each `A i j • x j` being integer multiplication in the
circle. This is an action of the group `GL(ι, ℤ)` by additive maps
(`AddCircle.instDistribMulActionGeneralLinearGroup`), and each `A` acts by smooth maps
(`AddCircle.instContMDiffConstSMulGeneralLinearGroup`). So `x ↦ A • x` is a diffeomorphism of the
torus, with inverse `x ↦ A⁻¹ • x` (`Diffeomorph.constSmul`), and the cotangent bundle `T*Tⁿ`
inherits the cotangent-lifted action (`TauCeti.CotangentBundle.instMulAction`).

The covering map `(ι → ℝ) → Tⁿ` has derivative the identity (`AddCircle.hasMFDerivAt_coe_pi`), and
it intertwines the action of `A` on the torus with multiplication of real vectors by the matrix `A`
(`AddCircle.generalLinearGroup_smul_coe_pi`). Hence the derivative of `x ↦ A • x` at every point is
the matrix `A`, acting on `ι → ℝ` (`AddCircle.mfderiv_generalLinearGroup_smul_apply`). Choosing a
basis of the period lattice of a torus is choosing such an `A`: these maps are the changes of angle
coordinates of action–angle charts.

For a torus `∀ i, AddCircle (p i)` with arbitrary positive periods, every translation
`x ↦ x + a` likewise has derivative the identity of `ι → ℝ` (`AddCircle.mfderiv_pi_add_right`).

## Main results

* `AddCircle.pi_coe_surjective`, `AddCircle.pi_coe_eq_iff`: surjectivity and fibres of the covering
  map `(ι → 𝕜) → ∀ i, AddCircle (p i)`.
* `AddCircle.contMDiff_pi_coe`, `AddCircle.hasMFDerivAt_pi_coe`, `AddCircle.mfderiv_pi_coe`,
  `AddCircle.isLocalDiffeomorph_pi_coe`: the covering map `(ι → ℝ) → ∀ i, AddCircle (p i)` is an
  analytic local diffeomorphism whose derivative is the identity.
* `AddCircle.extChartAt_pi_symm_apply`, `AddCircle.mfderiv_extChartAt_pi_symm`: the inverse of an
  extended product chart is the covering map on its target and has derivative the identity.
* `AddCircle.instDistribMulActionGeneralLinearGroup`: the action of `GL(ι, ℤ)` on
  `ι → AddCircle p` by additive maps.
* `AddCircle.instContMDiffConstSMulGeneralLinearGroup`: it acts by smooth maps.
* `AddCircle.hasMFDerivAt_coe_pi`: the covering map `(ι → ℝ) → Tⁿ` has derivative the identity.
* `AddCircle.hasMFDerivAt_pi_add_right`, `AddCircle.mfderiv_pi_add_right`: translations of a torus
  `∀ i, AddCircle (p i)` have derivative the identity.
* `AddCircle.hasMFDerivAt_generalLinearGroup_smul`,
  `AddCircle.mfderiv_generalLinearGroup_smul_apply`: the derivative of `x ↦ A • x` is the matrix
  `A`.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Section 50 (changes of the basis of the period lattice).
-/

public section

noncomputable section

open Function Matrix Set Topology
open scoped Manifold ContDiff

namespace AddCircle

/-! ### The covering map -/

section CoverAlgebra

variable {ι 𝕜 : Type*} [AddCommGroup 𝕜]

/-- The quotient map `(ι → 𝕜) → ∀ i, AddCircle (p i)` onto a product of additive circles is
surjective. -/
theorem pi_coe_surjective (p : ι → 𝕜) :
    Surjective (fun t : ι → 𝕜 ↦ fun i ↦ (t i : AddCircle (p i))) := fun x ↦
  ⟨fun i ↦ (QuotientAddGroup.mk_surjective (x i)).choose,
    funext fun i ↦ (QuotientAddGroup.mk_surjective (x i)).choose_spec⟩

/-- Two vectors in `ι → 𝕜` project to the same point of `∀ i, AddCircle (p i)` if and only if their
coordinates differ by integer multiples of the periods `p i`. -/
theorem pi_coe_eq_iff {p : ι → 𝕜} {s t : ι → 𝕜} :
    (fun i ↦ (s i : AddCircle (p i))) = (fun i ↦ (t i : AddCircle (p i))) ↔
      ∃ m : ι → ℤ, t = s + fun i ↦ m i • p i := by
  simp only [funext_iff, Pi.add_apply]
  refine ⟨fun h ↦ ?_, fun ⟨m, hm⟩ i ↦ ?_⟩
  · have hm (i : ι) : ∃ n : ℤ, n • p i = t i - s i := by
      rw [← coe_eq_zero_iff, QuotientAddGroup.mk_sub, h i, sub_self]
    exact ⟨fun i ↦ (hm i).choose, fun i ↦ eq_add_of_sub_eq' (hm i).choose_spec.symm⟩
  · rw [hm i, QuotientAddGroup.mk_add, coe_zsmul, coe_period, zsmul_zero, add_zero]

end CoverAlgebra

variable (p : ℝ) {ι : Type*} [Fintype ι]

section Cover

section VariablePeriods

variable (q : ι → ℝ) [∀ i, Fact (0 < q i)]

/-- The covering map `(ι → ℝ) → ∀ i, AddCircle (q i)` is analytic (and hence `C^n` for every
`n`). -/
theorem contMDiff_pi_coe (n : ℕ∞ω) :
    ContMDiff 𝓘(ℝ, ι → ℝ) (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) n
      (fun t : ι → ℝ ↦ fun i ↦ (t i : AddCircle (q i))) :=
  contMDiff_pi_iff.2 fun i ↦ (contMDiff_coe (q i) n).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i).contMDiff

/-- The covering map `(ι → ℝ) → ∀ i, AddCircle (q i)`, `t ↦ ([t i])ᵢ`, has derivative the identity
of `ι → ℝ`, the tangent spaces of the torus being read in its product charts. -/
theorem hasMFDerivAt_pi_coe (t : ι → ℝ) :
    HasMFDerivAt 𝓘(ℝ, ι → ℝ) (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      (fun t : ι → ℝ ↦ fun i ↦ (t i : AddCircle (q i))) t (ContinuousLinearMap.id ℝ (ι → ℝ)) :=
  (TauCeti.hasMFDerivAt_pi (M := fun i : ι ↦ AddCircle (q i)) (I := fun _ ↦ 𝓘(ℝ))
    (f := fun t : ι → ℝ ↦ fun i ↦ (t i : AddCircle (q i))) fun i ↦
    (hasMFDerivAt_coe (q i) (t i)).comp t
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i).hasMFDerivAt).congr_mfderiv <| by
    -- The product of the coordinate projections is the identity of `ι → ℝ`.
    ext v i
    rfl

/-- The derivative of the covering map `(ι → ℝ) → ∀ i, AddCircle (q i)` at every point is the
identity of `ι → ℝ`. -/
@[simp]
theorem mfderiv_pi_coe (t : ι → ℝ) :
    mfderiv 𝓘(ℝ, ι → ℝ) (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      (fun t : ι → ℝ ↦ fun i ↦ (t i : AddCircle (q i))) t = ContinuousLinearMap.id ℝ (ι → ℝ) :=
  (hasMFDerivAt_pi_coe q t).mfderiv

/-- The covering map `(ι → ℝ) → ∀ i, AddCircle (q i)` is an analytic local diffeomorphism (and
hence a `C^n` local diffeomorphism for every `n`). -/
theorem isLocalDiffeomorph_pi_coe (n : ℕ∞ω) :
    IsLocalDiffeomorph 𝓘(ℝ, ι → ℝ) (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) n
      (fun t : ι → ℝ ↦ fun i ↦ (t i : AddCircle (q i))) := by
  -- Prove analyticity (`n = ω`) by the inverse function theorem, then lower to `n`.
  have hω : IsLocalDiffeomorph 𝓘(ℝ, ι → ℝ) (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) ω
      (fun t : ι → ℝ ↦ fun i ↦ (t i : AddCircle (q i))) :=
    TauCeti.isLocalDiffeomorph_of_mfderiv_eq (contMDiff_pi_coe q ω) (by simp) fun t ↦
      ⟨ContinuousLinearEquiv.refl ℝ (ι → ℝ), (mfderiv_pi_coe q t).symm⟩
  exact hω.of_le le_top

variable {q} in
/-- On its target, the inverse of an extended product chart of `∀ i, AddCircle (q i)` is the
covering map `z ↦ ([z i])ᵢ`. -/
theorem extChartAt_pi_symm_apply (x : ∀ i, AddCircle (q i)) {z : ι → ℝ}
    (hz : z ∈ (extChartAt (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) x).target) :
    (extChartAt (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) x).symm z =
      fun i ↦ (z i : AddCircle (q i)) := by
  rw [TauCeti.extChartAt_pi] at hz ⊢
  exact funext fun i ↦ extChartAt_symm_apply (x i) (hz i (mem_univ i))

variable {q} in
/-- At each point of its target, the inverse of an extended product chart of
`∀ i, AddCircle (q i)` has derivative the identity of `ι → ℝ`. -/
theorem mfderiv_extChartAt_pi_symm (x : ∀ i, AddCircle (q i)) {z : ι → ℝ}
    (hz : z ∈ (extChartAt (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) x).target) :
    mfderiv 𝓘(ℝ, ι → ℝ) (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      (extChartAt (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) x).symm z =
      ContinuousLinearMap.id ℝ (ι → ℝ) := by
  have h : (extChartAt (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) x).symm =ᶠ[𝓝 z]
      fun t : ι → ℝ ↦ fun i ↦ (t i : AddCircle (q i)) := by
    filter_upwards [(isOpen_extChartAt_target x).mem_nhds hz] with u hu
    exact extChartAt_pi_symm_apply x hu
  rw [h.mfderiv_eq, mfderiv_pi_coe]
  -- The identification `tangentSpaceCast` of tangent spaces at equal points is the identity.
  rfl

end VariablePeriods

variable [Fact (0 < p)]

/-- The covering map `(ι → ℝ) → (ι → AddCircle p)`, `t ↦ ([t i])ᵢ`, has derivative the identity of
`ι → ℝ`, the tangent spaces of the torus being read in its product charts. -/
theorem hasMFDerivAt_coe_pi (t : ι → ℝ) :
    HasMFDerivAt 𝓘(ℝ, ι → ℝ) (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      (fun t : ι → ℝ ↦ fun i ↦ (t i : AddCircle p)) t (ContinuousLinearMap.id ℝ (ι → ℝ)) :=
  hasMFDerivAt_pi_coe (fun _ ↦ p) t

end Cover

/-! ### Translations -/

section Translation

variable {p : ι → ℝ} [∀ i, Fact (0 < p i)]

/-- Every translation `x ↦ x + a` of the torus `∀ i, AddCircle (p i)` has derivative the identity
of `ι → ℝ`, the tangent spaces of the torus being read in its product charts. -/
theorem hasMFDerivAt_pi_add_right (a x : ∀ i, AddCircle (p i)) :
    HasMFDerivAt (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      (· + a) x (ContinuousLinearMap.id ℝ (ι → ℝ)) := by
  -- Each component is the projection followed by a translation of a circle, whose derivative is
  -- the identity of `ℝ`.
  have h (i : ι) : HasMFDerivAt (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) 𝓘(ℝ)
      (fun z : ∀ i, AddCircle (p i) ↦ (z + a) i) x (ContinuousLinearMap.proj i) := by
    have h₁ := ((contMDiff_add_right (I := 𝓘(ℝ)) (n := 1) (a := a i)).mdifferentiableAt
      one_ne_zero (x := x i)).hasMFDerivAt
    refine (h₁.comp x (TauCeti.hasMFDerivAt_apply i x)).congr_mfderiv ?_
    rw [mfderiv_add_right]
    exact ContinuousLinearMap.id_comp _
  exact (TauCeti.hasMFDerivAt_pi h).congr_mfderiv ContinuousLinearMap.pi_proj

/-- Every translation `x ↦ x + a` of the torus `∀ i, AddCircle (p i)` has derivative the identity
of `ι → ℝ`. -/
@[simp]
theorem mfderiv_pi_add_right (a x : ∀ i, AddCircle (p i)) :
    mfderiv (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      (· + a) x = ContinuousLinearMap.id ℝ (ι → ℝ) :=
  (hasMFDerivAt_pi_add_right a x).mfderiv

end Translation

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
      ← zsmul_eq_mul, QuotientAddGroup.mk_sum, coe_zsmul]

/-! ### Smoothness and derivative -/

variable [Fact (0 < p)]

/-- Integer matrices act on the torus `ι → AddCircle p` by smooth maps. -/
instance instContMDiffConstSMulGeneralLinearGroup {n : ℕ∞ω} :
    ContMDiffConstSMul (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) n (GL ι ℤ) (ι → AddCircle p) where
  contMDiff_const_smul A := contMDiff_pi_iff.2 fun i ↦ by
    simp only [generalLinearGroup_smul_apply]
    exact ContMDiff.sum fun j _ ↦ (TauCeti.contMDiff_zsmul (I := 𝓘(ℝ)) _).comp contMDiff_apply

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
    exact ((hasMFDerivAt_coe_pi p (L t)).comp t L.hasMFDerivAt).congr_mfderiv
      (ContinuousLinearMap.id_comp L)
  have hd : MDifferentiableAt (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (fun y ↦ A • y) (fun i ↦ (t i : AddCircle p)) :=
    ((contMDiff_const_smul A).mdifferentiableAt (n := 1) one_ne_zero)
  have h := mfderiv_comp t hd (hasMFDerivAt_coe_pi p t).mdifferentiableAt
  rw [hcomp.mfderiv, (hasMFDerivAt_coe_pi p t).mfderiv] at h
  have h' : mfderiv (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      (fun y ↦ A • y) (fun i ↦ (t i : AddCircle p)) = L := by
    rw [h]
    exact (ContinuousLinearMap.comp_id _).symm
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
