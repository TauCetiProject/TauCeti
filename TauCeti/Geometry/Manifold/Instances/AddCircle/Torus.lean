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
point (`AddCircle.hasMFDerivAt_coe_pi`). In the same way the changes of charts of `Tⁿ` are
translations, so the tangent trivializations of `Tⁿ` are the identity of `ι → ℝ` on the sources of
their charts (`AddCircle.symmL_trivializationAt_pi`). The covering map intertwines the action of
`A` on the torus with multiplication of real vectors by the matrix `A`
(`AddCircle.generalLinearGroup_smul_coe_pi`).
Hence the derivative of `x ↦ A • x` at every point is the matrix `A`, acting on `ι → ℝ`
(`AddCircle.mfderiv_generalLinearGroup_smul_apply`). Choosing a basis of the period lattice of a
torus is choosing such an `A`: these maps are the changes of angle coordinates of action–angle
charts.

For a torus `∀ i, AddCircle (p i)` with arbitrary positive periods, every translation
`x ↦ x + a` likewise has derivative the identity of `ι → ℝ` (`AddCircle.mfderiv_pi_add_right`).

## Main results

* `AddCircle.instDistribMulActionGeneralLinearGroup`: the action of `GL(ι, ℤ)` on
  `ι → AddCircle p` by additive maps.
* `AddCircle.instContMDiffConstSMulGeneralLinearGroup`: it acts by smooth maps.
* `AddCircle.hasMFDerivAt_coe_pi`, `AddCircle.contMDiff_coe_pi`: the covering map
  `(ι → ℝ) → Tⁿ` is smooth, with derivative the identity.
* `AddCircle.symmL_trivializationAt_pi`: the tangent trivializations of the torus are the identity
  on the sources of their charts.
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

open Function Matrix
open scoped Manifold ContDiff Topology

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

/-- The covering map `(ι → ℝ) → (ι → AddCircle p)`, `t ↦ ([t i])ᵢ`, is `C^n` for every order `n`. -/
theorem contMDiff_coe_pi (n : ℕ∞ω) :
    ContMDiff 𝓘(ℝ, ι → ℝ) (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) n
      (fun t : ι → ℝ ↦ fun i ↦ (t i : AddCircle p)) :=
  contMDiff_pi_iff.2 fun i ↦ (contMDiff_coe p n).comp (contMDiff_pi_module_iff.1 contMDiff_id i)

/-- **The tangent bundle of the torus is trivialized by its charts.** On the source of the chart
at `x`, the inverse tangent trivialization at `x` is the identity of `ι → ℝ`: in each coordinate
two charts of `AddCircle p` differ near a common point by a constant integer multiple of `p`
(`AddCircle.exists_eventuallyEq_add_zsmul`), so the changes of charts are translations. -/
theorem symmL_trivializationAt_pi (x : ι → AddCircle p) {y : ι → AddCircle p}
    (hy : y ∈ (chartAt (ModelPi fun _ : ι ↦ ℝ) x).source) :
    (trivializationAt (ι → ℝ) (TangentSpace (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))) x).symmL ℝ y =
      ContinuousLinearMap.id ℝ (ι → ℝ) := by
  rw [TangentBundle.symmL_trivializationAt_eq_core hy]
  simp only [tangentBundleCore_coordChange, achart_val]
  have hyi (i : ι) : y i ∈ (chartAt ℝ (x i)).source := by
    simpa using (Set.mem_univ_pi.1 hy) i
  -- In each coordinate, the two charts differ by an integer multiple of `p` near `y i`.
  have hk (i : ι) : ∃ k : ℤ, chartAt ℝ (y i) =ᶠ[𝓝 (y i)] fun z ↦ chartAt ℝ (x i) z + k • p :=
    exists_eventuallyEq_add_zsmul (fun _ hz ↦ coe_apply_of_mem_atlas (chart_mem_atlas ℝ _) hz)
      (fun _ hz ↦ coe_apply_of_mem_atlas (chart_mem_atlas ℝ _) hz) (hyi i)
      (mem_chart_source ℝ (y i))
  choose k hk using hk
  set q₀ := (chartAt (ModelPi fun _ : ι ↦ ℝ) x).extend (ModelWithCorners.pi fun _ ↦ 𝓘(ℝ)) y
  -- Hence the change of charts is the translation by `(k i • p)ᵢ` near `q₀`.
  have heq : (((chartAt (ModelPi fun _ : ι ↦ ℝ) y).extend (ModelWithCorners.pi fun _ ↦ 𝓘(ℝ))) ∘
      ((chartAt (ModelPi fun _ : ι ↦ ℝ) x).extend (ModelWithCorners.pi fun _ ↦ 𝓘(ℝ))).symm) =ᶠ[𝓝 q₀]
      fun q ↦ q + fun i ↦ k i • p := by
    have hev (i : ι) : ∀ᶠ q in 𝓝 q₀, q i ∈ (chartAt ℝ (x i)).target ∧
        chartAt ℝ (y i) ((chartAt ℝ (x i)).symm (q i)) =
          chartAt ℝ (x i) ((chartAt ℝ (x i)).symm (q i)) + k i • p := by
      have hq₀ : q₀ i = chartAt ℝ (x i) (y i) := (rfl)
      have hev : ContinuousAt (fun q : ι → ℝ ↦ q i) q₀ := (continuous_apply i).continuousAt
      have hc : Filter.Tendsto (fun q : ι → ℝ ↦ (chartAt ℝ (x i)).symm (q i)) (𝓝 q₀)
          (𝓝 (y i)) := by
        have h : ContinuousAt (chartAt ℝ (x i)).symm (q₀ i) :=
          hq₀ ▸ (chartAt ℝ (x i)).continuousAt_symm ((chartAt ℝ (x i)).map_source (hyi i))
        have h' := (h.comp (f := fun q : ι → ℝ ↦ q i) hev).tendsto
        rwa [Function.comp_apply, hq₀, (chartAt ℝ (x i)).left_inv (hyi i)] at h'
      have ht := hev.preimage_mem_nhds ((chartAt ℝ (x i)).open_target.mem_nhds
        (hq₀ ▸ (chartAt ℝ (x i)).map_source (hyi i)))
      filter_upwards [ht, hc.eventually (hk i)] with q hq hq'
      exact ⟨hq, hq'⟩
    filter_upwards [Filter.eventually_all.2 hev] with q hq
    funext i
    simp only [Function.comp_apply, OpenPartialHomeomorph.extend_coe,
      OpenPartialHomeomorph.extend_coe_symm]
    -- The model `ModelWithCorners.pi fun _ ↦ 𝓘(ℝ)` acts as the identity coordinatewise, so the
    -- `i`-th coordinate of the change of charts is the change of charts of the `i`-th circle.
    have h := (hq i).2
    rw [(chartAt ℝ (x i)).right_inv (hq i).1] at h
    exact h
  have hr : Set.range (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) = Set.univ := by simp
  rw [hr, fderivWithin_univ, heq.fderiv_eq, fderiv_add_const, fderiv_fun_id]

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
