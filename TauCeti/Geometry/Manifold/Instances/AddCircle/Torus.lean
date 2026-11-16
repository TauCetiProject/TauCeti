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

import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import TauCeti.Geometry.Manifold.Diffeomorph.NormedSpace
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic

/-!
# Covering map, period rescalings, and integral linear automorphisms of a torus

For a finite family of positive periods `p : ι → ℝ`, let `Tⁿ = ∀ i, AddCircle (p i)` be the torus,
a smooth manifold modelled on `ModelWithCorners.pi fun _ ↦ 𝓘(ℝ)` whose tangent space at every point
is `ι → ℝ`.

The covering map `(ι → ℝ) → Tⁿ`, `t ↦ ([t i])ᵢ`, is an analytic local diffeomorphism
(`AddCircle.isLocalDiffeomorph_pi_coe`) whose derivative at every point is the identity of `ι → ℝ`
(`AddCircle.hasMFDerivAt_pi_coe`, and `AddCircle.hasMFDerivAt_coe_pi` for equal periods). On its
target, the inverse of every preferred chart of `Tⁿ` is the covering map
(`AddCircle.extChartAt_pi_symm_apply`), so the tangent-bundle trivializations of `Tⁿ` are the
identity of `ι → ℝ` on their chart domains (`AddCircle.symmL_trivializationAt_pi`,
`AddCircle.continuousLinearMapAt_trivializationAt_pi`). Every translation `x ↦ x + a` of `Tⁿ` also
has derivative the identity of `ι → ℝ` (`AddCircle.mfderiv_pi_add_right`), and coordinatewise
period rescaling defines an analytic diffeomorphism `AddCircle.piDiffeomorphAddCircle p q n`
between tori of periods `p` and `q`, with diagonal derivative `v ↦ ((p i)⁻¹ * q i * v i)ᵢ`
(`AddCircle.mfderiv_piDiffeomorphAddCircle_apply`).

When all periods are equal to `p`, an invertible integer matrix `A ∈ GL(ι, ℤ)` acts on
`ι → AddCircle p` by

`(A • x) i = ∑ j, A i j • x j`

(`AddCircle.generalLinearGroup_smul_apply`), each `A i j • x j` being integer multiplication in the
circle. This is an action of the group `GL(ι, ℤ)` by additive maps
(`AddCircle.instDistribMulActionGeneralLinearGroup`), and each `A` acts by smooth maps
(`AddCircle.instContMDiffConstSMulGeneralLinearGroup`). So `x ↦ A • x` is a diffeomorphism of the
torus, with inverse `x ↦ A⁻¹ • x` (`Diffeomorph.constSmul`), and the cotangent bundle `T*Tⁿ`
inherits the cotangent-lifted action (`TauCeti.CotangentBundle.instMulAction`). The covering map
intertwines this action with multiplication of real vectors by `A`
(`AddCircle.generalLinearGroup_smul_coe_pi`), so the derivative of `x ↦ A • x` at every point is
the matrix `A`, acting on `ι → ℝ` (`AddCircle.mfderiv_generalLinearGroup_smul_apply`). Choosing a
basis of the period lattice of a torus is choosing such an `A`: these maps are the changes of angle
coordinates of action–angle charts.

## Main results

* `AddCircle.extChartAt_pi_symm_apply`, `AddCircle.isLocalDiffeomorph_pi_coe`,
  `AddCircle.hasMFDerivAt_pi_coe`, `AddCircle.hasMFDerivAt_coe_pi`: the covering map
  `(ι → ℝ) → ∀ i, AddCircle (p i)` is an analytic local diffeomorphism with identity derivative,
  agreeing with the inverse of every extended chart.
* `AddCircle.symmL_trivializationAt_pi`, `AddCircle.continuousLinearMapAt_trivializationAt_pi`:
  the tangent-bundle trivializations of a torus are the identity on their chart domains.
* `AddCircle.piDiffeomorphAddCircle`, `AddCircle.mfderiv_piDiffeomorphAddCircle_apply`:
  coordinatewise rescaling of the periods of a torus, and its derivative.
* `AddCircle.hasMFDerivAt_pi_add_right`, `AddCircle.mfderiv_pi_add_right`: translations of a torus
  `∀ i, AddCircle (p i)` have derivative the identity.
* `AddCircle.instDistribMulActionGeneralLinearGroup`: the action of `GL(ι, ℤ)` on
  `ι → AddCircle p` by additive maps.
* `AddCircle.instContMDiffConstSMulGeneralLinearGroup`: it acts by smooth maps.
* `AddCircle.hasMFDerivAt_generalLinearGroup_smul`,
  `AddCircle.mfderiv_generalLinearGroup_smul_apply`: the derivative of `x ↦ A • x` is the matrix
  `A`.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Section 50 (changes of the basis of the period lattice).
-/

public section

noncomputable section

open Function Matrix Set
open scoped Manifold ContDiff Topology

namespace AddCircle

variable (p : ℝ) {ι : Type*} [Fintype ι]

/-! ### The covering map -/

section Cover

variable {p' : ι → ℝ} [∀ i, Fact (0 < p' i)]

/-- On its target, the inverse of an extended chart of the torus `∀ i, AddCircle (p' i)` is the
covering map `(ι → ℝ) → ∀ i, AddCircle (p' i)`. -/
theorem extChartAt_pi_symm_apply (x : ∀ i, AddCircle (p' i)) {z : ι → ℝ}
    (hz : z ∈ (extChartAt (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) x).target) :
    (extChartAt (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) x).symm z =
      fun i ↦ (z i : AddCircle (p' i)) := by
  rw [TauCeti.extChartAt_pi] at hz ⊢
  rw [PartialEquiv.pi_symm_apply]
  exact funext fun i ↦ extChartAt_symm_apply (x i) (hz i (mem_univ i))

/-- The covering map `(ι → ℝ) → (∀ i, AddCircle (p' i))`, `t ↦ ([t i])ᵢ`, is analytic. -/
theorem contMDiff_pi_coe (p' : ι → ℝ) [∀ i, Fact (0 < p' i)] (n : ℕ∞ω) :
    ContMDiff 𝓘(ℝ, ι → ℝ) (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) n
      (fun t : ι → ℝ ↦ fun i ↦ (t i : AddCircle (p' i))) :=
  contMDiff_pi_iff.2 fun i ↦
    (contMDiff_coe (p' i) n).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i).contMDiff

/-- The covering map `(ι → ℝ) → (∀ i, AddCircle (p' i))`, `t ↦ ([t i])ᵢ`, has derivative the
identity of `ι → ℝ`, the tangent spaces of the torus being read in its product charts. -/
theorem hasMFDerivAt_pi_coe (p' : ι → ℝ) [∀ i, Fact (0 < p' i)] (t : ι → ℝ) :
    HasMFDerivAt 𝓘(ℝ, ι → ℝ) (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      (fun t : ι → ℝ ↦ fun i ↦ (t i : AddCircle (p' i))) t (ContinuousLinearMap.id ℝ (ι → ℝ)) :=
  (TauCeti.hasMFDerivAt_pi (M := fun i : ι ↦ AddCircle (p' i)) (I := fun _ ↦ 𝓘(ℝ))
    (f := fun t : ι → ℝ ↦ fun i ↦ (t i : AddCircle (p' i))) fun i ↦ (hasMFDerivAt_coe (p' i)
    (t i)).comp t (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i).hasMFDerivAt
    ).congr_mfderiv <| by
    -- The product of the coordinate projections is the identity of `ι → ℝ`.
    ext v i
    rfl

/-- The derivative of the covering map `(ι → ℝ) → (∀ i, AddCircle (p' i))` is the identity of
`ι → ℝ`. -/
@[simp]
theorem mfderiv_pi_coe (p' : ι → ℝ) [∀ i, Fact (0 < p' i)] (t : ι → ℝ) :
    mfderiv 𝓘(ℝ, ι → ℝ) (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      (fun t : ι → ℝ ↦ fun i ↦ (t i : AddCircle (p' i))) t = ContinuousLinearMap.id ℝ (ι → ℝ) :=
  (hasMFDerivAt_pi_coe p' t).mfderiv

/-- The covering map `(ι → ℝ) → (∀ i, AddCircle (p' i))`, `t ↦ ([t i])ᵢ`, is an analytic local
diffeomorphism. -/
theorem isLocalDiffeomorph_pi_coe (p' : ι → ℝ) [∀ i, Fact (0 < p' i)] (n : ℕ∞ω) :
    IsLocalDiffeomorph 𝓘(ℝ, ι → ℝ) (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) n
      (fun t : ι → ℝ ↦ fun i ↦ (t i : AddCircle (p' i))) := by
  intro t
  set I_T := ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)
  set x : ∀ i, AddCircle (p' i) := fun i ↦ (t i : AddCircle (p' i))
  -- Translate by `u - t`, where `u = extChartAt I_T x x` is a lift of `x` in the chart target,
  -- and follow with the inverse extended chart at `x`.
  set u : ι → ℝ := extChartAt I_T x x
  have hu : ∀ i, (u i : AddCircle (p' i)) = (t i : AddCircle (p' i)) := fun i ↦ by
    simpa only [u, I_T, TauCeti.extChartAt_pi_apply] using coe_extChartAt_self (x i)
  set τ : (ι → ℝ) ≃ₘ^n⟮𝓘(ℝ, ι → ℝ), 𝓘(ℝ, ι → ℝ)⟯ (ι → ℝ) :=
    Diffeomorph.smulAdd n (1 : ℝ) (u - t) one_ne_zero
  set Φ := τ.toPartialDiffeomorph.trans (TauCeti.extChartPartialDiffeomorph I_T n x).symm
  have htΦ : t ∈ Φ.source := by
    have hu_int : u ∈ interior (extChartAt I_T x).target := by
      rw [(isOpen_extChartAt_target x).interior_eq]
      exact mem_extChartAt_target x
    simpa [Φ, τ, one_smul, add_sub_cancel] using hu_int
  refine TauCeti.isLocalDiffeomorphAt_of_eqOn htΦ fun s hs ↦ ?_
  have hs_tgt : s + (u - t) ∈ (extChartAt I_T x).target := by
    have hs' : τ s ∈ interior (extChartAt I_T x).target := by simpa [Φ] using hs
    exact interior_subset (by simpa [τ, one_smul] using hs')
  have hΦs : Φ s = (extChartAt I_T x).symm (s + (u - t)) := by
    simp [Φ, τ, one_smul]
  rw [hΦs, extChartAt_pi_symm_apply x hs_tgt]
  funext i
  rw [Pi.add_apply, Pi.sub_apply, coe_add, coe_sub, hu i, sub_self, add_zero]

/-- On the source of the preferred chart of the torus `∀ i, AddCircle (p' i)` at `x₀`, the inverse
of the tangent bundle trivialization at `x₀` is the identity of `ι → ℝ`. -/
theorem symmL_trivializationAt_pi {x₀ x : ∀ i, AddCircle (p' i)}
    (hx : x ∈ (chartAt (ModelPi fun _ : ι ↦ ℝ) x₀).source) :
    (trivializationAt (ι → ℝ) (TangentSpace (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))) x₀).symmL ℝ x =
      ContinuousLinearMap.id ℝ (ι → ℝ) := by
  set I_T := ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)
  have hxt : extChartAt I_T x₀ x ∈ (extChartAt I_T x₀).target :=
    (extChartAt I_T x₀).map_source (by simpa only [extChartAt_source] using hx)
  rw [TangentBundle.symmL_trivializationAt (I := I_T) hx, I_T.range_eq_univ, mfderivWithin_univ]
  have hev : (extChartAt I_T x₀).symm =ᶠ[𝓝 (extChartAt I_T x₀ x)]
      fun t : ι → ℝ ↦ fun i ↦ (t i : AddCircle (p' i)) := by
    filter_upwards [(isOpen_extChartAt_target x₀).mem_nhds hxt] with z hz
    exact extChartAt_pi_symm_apply x₀ hz
  rw [hev.mfderiv_eq, mfderiv_pi_coe]
  -- `TangentSpace I_T _` is definitionally `ι → ℝ` at every point, so the tangent-space cast is
  -- the identity.
  rfl

/-- On the source of the preferred chart of the torus `∀ i, AddCircle (p' i)` at `x₀`, the tangent
bundle trivialization at `x₀` is the identity of `ι → ℝ`. -/
theorem continuousLinearMapAt_trivializationAt_pi {x₀ x : ∀ i, AddCircle (p' i)}
    (hx : x ∈ (chartAt (ModelPi fun _ : ι ↦ ℝ) x₀).source) :
    (trivializationAt (ι → ℝ)
        (TangentSpace (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))) x₀).continuousLinearMapAt ℝ x =
      ContinuousLinearMap.id ℝ (ι → ℝ) := by
  set e := trivializationAt (ι → ℝ) (TangentSpace (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))) x₀
  refine ContinuousLinearMap.ext fun v ↦ ?_
  have hv := e.continuousLinearMapAt_symmL (R := ℝ) (b := x) hx v
  have hsymm : e.symmL ℝ x v = v := DFunLike.congr_fun (symmL_trivializationAt_pi hx) v
  exact (congrArg (e.continuousLinearMapAt ℝ x) hsymm).symm.trans hv

variable [Fact (0 < p)]

/-- The covering map `(ι → ℝ) → (ι → AddCircle p)`, `t ↦ ([t i])ᵢ`, has derivative the identity of
`ι → ℝ`, the tangent spaces of the torus being read in its product charts. -/
theorem hasMFDerivAt_coe_pi (t : ι → ℝ) :
    HasMFDerivAt 𝓘(ℝ, ι → ℝ) (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      (fun t : ι → ℝ ↦ fun i ↦ (t i : AddCircle p)) t (ContinuousLinearMap.id ℝ (ι → ℝ)) :=
  hasMFDerivAt_pi_coe (fun _ ↦ p) t

end Cover

/-! ### Rescaling the periods -/

section Rescale

variable (p₁ p₂ : ι → ℝ) [∀ i, Fact (0 < p₁ i)] [∀ i, Fact (0 < p₂ i)]

/-- Coordinatewise rescaling `(∀ i, AddCircle (p₁ i)) ≃ (∀ i, AddCircle (p₂ i))`, applying
`AddCircle.diffeomorphAddCircle (p₁ i) (p₂ i) n` in each coordinate. -/
def piDiffeomorphAddCircle (n : ℕ∞ω) :
    (∀ i, AddCircle (p₁ i)) ≃ₘ^n⟮ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ),
      ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)⟯ (∀ i, AddCircle (p₂ i)) where
  toEquiv := Equiv.piCongrRight fun i ↦ (diffeomorphAddCircle (p₁ i) (p₂ i) n).toEquiv
  contMDiff_toFun := ContMDiff.piMap fun i ↦ (diffeomorphAddCircle (p₁ i) (p₂ i) n).contMDiff
  contMDiff_invFun := ContMDiff.piMap fun i ↦ (diffeomorphAddCircle (p₁ i) (p₂ i) n).symm.contMDiff

/-- The coordinatewise rescaling acts in each coordinate by `AddCircle.diffeomorphAddCircle`. -/
@[simp]
theorem piDiffeomorphAddCircle_apply (n : ℕ∞ω) (x : ∀ i, AddCircle (p₁ i)) (i : ι) :
    piDiffeomorphAddCircle p₁ p₂ n x i = diffeomorphAddCircle (p₁ i) (p₂ i) n (x i) :=
  (rfl)

/-- The inverse of the coordinatewise rescaling from `p₁` to `p₂` is the rescaling back. -/
@[simp]
theorem piDiffeomorphAddCircle_symm (n : ℕ∞ω) :
    (piDiffeomorphAddCircle p₁ p₂ n).symm = piDiffeomorphAddCircle p₂ p₁ n :=
  Diffeomorph.ext fun x ↦ funext fun i ↦
    DFunLike.congr_fun (diffeomorphAddCircle_symm (p₁ i) (p₂ i) n) (x i)

/-- The coordinatewise rescaling from `p₁` to `p₂` has diagonal derivative scaling the `i`-th
component by `(p₁ i)⁻¹ * p₂ i`. -/
theorem hasMFDerivAt_piDiffeomorphAddCircle (n : ℕ∞ω) (x : ∀ i, AddCircle (p₁ i)) :
    HasMFDerivAt (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      (piDiffeomorphAddCircle p₁ p₂ n) x
      (ContinuousLinearMap.pi fun i ↦
        ((p₁ i)⁻¹ * p₂ i) • (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)) := by
  refine TauCeti.hasMFDerivAt_pi fun i ↦ ?_
  have hd : MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ) (diffeomorphAddCircle (p₁ i) (p₂ i) n) (x i) := by
    rw [coe_diffeomorphAddCircle, ← coe_diffeomorphAddCircle (p := p₁ i) (q := p₂ i) (n := 1)]
    exact ((diffeomorphAddCircle (p₁ i) (p₂ i) 1).contMDiff (x i)).mdifferentiableAt one_ne_zero
  refine (hd.hasMFDerivAt.comp x (TauCeti.hasMFDerivAt_apply i x)).congr_mfderiv ?_
  rw [mfderiv_diffeomorphAddCircle]
  refine ContinuousLinearMap.ext fun v ↦ ?_
  -- Both sides act on a tangent vector `v : ι → ℝ` by multiplying `v i` by `(p₁ i)⁻¹ * p₂ i`.
  rfl

/-- The derivative of the coordinatewise rescaling sends `v` to `((p₁ i)⁻¹ * p₂ i * v i)ᵢ`. -/
@[simp]
theorem mfderiv_piDiffeomorphAddCircle_apply (n : ℕ∞ω) (x : ∀ i, AddCircle (p₁ i)) (v : ι → ℝ)
    (i : ι) :
    mfderiv (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
        (piDiffeomorphAddCircle p₁ p₂ n) x v i =
      (p₁ i)⁻¹ * p₂ i * v i := by
  rw [(hasMFDerivAt_piDiffeomorphAddCircle p₁ p₂ n x).mfderiv]
  rfl

end Rescale

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
