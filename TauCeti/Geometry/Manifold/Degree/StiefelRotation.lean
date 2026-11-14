/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Complex.Orientation
public import TauCeti.Geometry.Manifold.Degree.Basic
public import TauCeti.Geometry.Manifold.Instances.Sphere
public import TauCeti.Geometry.Manifold.Instances.Stiefel.Rotation
public import TauCeti.Geometry.Manifold.Orientation.Prod
public import TauCeti.Geometry.Manifold.Orientation.Sphere
public import TauCeti.Geometry.Manifold.Orientation.Stiefel
import TauCeti.Geometry.Manifold.MFDeriv.IsInvertible
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.MFDeriv.Prod

/-!
# The degree of the Stiefel rotation family

Let `E` be a real inner product space of dimension `n + 2`, with unit sphere `Sⁿ⁺¹` and unit
tangent bundle the Stiefel manifold `TauCeti.stiefel E 2` of orthonormal pairs `(u, v)`. The
Stiefel rotation family (`TauCeti.stiefelRotationFamily`)

`τ : T¹Sⁿ⁺¹ × S¹ → Sⁿ⁺¹ × Sⁿ⁺¹`, `τ ((u, v), z) = (u, Re z • u + Im z • v)`,

is the map of the proof of Proposition 6.17 of Barraud–Damian–Humilière–Oancea. This file
computes its degree.

Its derivative is computed in `TauCeti.mvfderiv_coe_snd_stiefelRotationFamily_apply`. At a point
with `Im z ≠ 0` it is invertible (`TauCeti.isInvertible_mfderiv_stiefelRotationFamily`). A point
`(u, q)` with `q ≠ ±u` has exactly two preimages, both with `Im z ≠ 0` and exchanged by the
involution `((u, v), z) ↦ ((u, -v), conj z)` (`TauCeti.stiefelRotationInvolution`), so it is a
regular value (`TauCeti.isRegularValue_stiefelRotationFamily`). Because `τ` is unchanged by this
involution, the orientation signs at the two preimages differ by the orientation sign of the
involution. That sign is computed from the frame reflection `(u, v) ↦ (u, -v)` of the Stiefel
manifold, of sign `(-1)ⁿ⁺¹` for the normal orientations `O.stiefelTwoOrientation`, and from complex
conjugation on `S¹`, which reverses its orientation. So it is `(-1)ⁿ`, and the degree of `τ` at a
regular value is `±(1 + (-1)ⁿ)`
(`TauCeti.exists_degreeAtRegularValue_stiefelRotationFamily_eq`), for every orientation of the
target:`±2` when the fibre sphere `Sⁿ` has even dimension and `0` when it has
odd dimension. This is the degree computation of the proof of Proposition 6.17 (for the
even-dimensional sphere `Sⁿ⁺²` of the paper's `H_{2m−3}(Ω²Sᵐ)`, `m = n + 2`), together with the
vanishing of its footnote 16.

## Main declarations

* `TauCeti.mvfderiv_stiefel_coe_fst_apply`: the derivative of a frame vector, read in `E`.
* `TauCeti.mvfderiv_coe_fst_stiefelRotationFamily_apply`,
  `TauCeti.mvfderiv_coe_snd_stiefelRotationFamily_apply`: the derivative, read in `E`.
* `TauCeti.injective_mfderiv_stiefelRotationFamily`,
  `TauCeti.isInvertible_mfderiv_stiefelRotationFamily`: it is injective, hence invertible, where
  `Im z ≠ 0`.
* `TauCeti.isRegularValue_stiefelRotationFamily`: points `(u, q)` with `q ≠ ±u` are regular values.
* `TauCeti.orientationSign_stiefelRotationInvolution`: the involution has orientation sign `(-1)ⁿ`.
* `TauCeti.exists_degreeAtRegularValue_stiefelRotationFamily_eq`: the degree is `±(1 + (-1)ⁿ)`
  there.
* `TauCeti.abs_degreeAtRegularValue_stiefelRotationFamily_of_even`,
  `TauCeti.degreeAtRegularValue_stiefelRotationFamily_of_odd`: it is `±2` for even `n` and `0` for
  odd `n`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4.2 (proof of Proposition 6.17).
* J. W. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia, 1965,
  §5 (the degree as a signed count of preimages).
-/

public section

noncomputable section

open Metric Module Set TauCeti.Manifold.Orientation
open scoped Manifold ContDiff RealInnerProductSpace

namespace TauCeti

attribute [local instance] finrank_real_complex_fact'

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {n : ℕ} [Fact (finrank ℝ E = n + 1 + 1)]

/-- The model space of the Stiefel manifold of orthonormal two-frames of `E`. -/
local notation "𝓢" => 𝓘(ℝ, Fin (2 * finrank ℝ E - Nat.choose (2 + 1) 2) → ℝ)

/-! ### The derivative -/

/-- Read in `E`, the derivative of the `i`th frame vector `((u₀, u₁), z) ↦ uᵢ` sends a tangent
vector `(t, c)` to the `i`th vector of `t`, read in `Fin 2 → E`. -/
theorem mvfderiv_stiefel_coe_fst_apply (x : stiefel E 2 × sphere (0 : ℂ) 1)
    (p : TangentSpace ((𝓢).prod (𝓡 1)) x) (i : Fin 2) :
    mvfderiv ((𝓢).prod (𝓡 1)) (fun y : stiefel E 2 × sphere (0 : ℂ) 1 ↦ (y.1 : Fin 2 → E) i) x p =
      mvfderiv 𝓢 ((↑) : stiefel E 2 → Fin 2 → E) x.1 (Manifold.tangentSpaceProdEquiv x p).1 i := by
  rw [Manifold.tangentSpaceProdEquiv_apply]
  -- The map is `y ↦ proj i (y.1 : Fin 2 → E)` by definition.
  exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ E) i).mvfderiv_comp_fst_apply
    (((contMDiff_coe_stiefel E 2 (r := 1)) x.1).mdifferentiableAt one_ne_zero) p

/-- Read in `E`, the derivative of the first component `((u, v), z) ↦ u` of the Stiefel rotation
family sends a tangent vector `(t, c)` to the first vector of `t`, read in `Fin 2 → E`. -/
theorem mvfderiv_coe_fst_stiefelRotationFamily_apply (x : stiefel E 2 × sphere (0 : ℂ) 1)
    (p : TangentSpace ((𝓢).prod (𝓡 1)) x) :
    mvfderiv ((𝓢).prod (𝓡 1)) (fun y ↦ ((stiefelRotationFamily y).1 : E)) x p =
      mvfderiv 𝓢 ((↑) : stiefel E 2 → Fin 2 → E) x.1 (Manifold.tangentSpaceProdEquiv x p).1 0 := by
  have hf : (fun y : stiefel E 2 × sphere (0 : ℂ) 1 ↦ ((stiefelRotationFamily y).1 : E)) =
      fun y ↦ (y.1 : Fin 2 → E) 0 :=
    funext fun y ↦ coe_fst_stiefelRotationFamily y
  rw [hf]
  exact mvfderiv_stiefel_coe_fst_apply x p 0

/-- **The derivative of the Stiefel rotation family.** Read in `E`, the derivative of the second
component `((u, v), z) ↦ Re z • u + Im z • v` sends a tangent vector `(t, c)` at `((u, v), z)` to
`Re γ • u + Im γ • v + Re z • a + Im z • b`, where `(a, b)` is `t` read in `Fin 2 → E` and `γ` is
`c` read in `ℂ`. -/
theorem mvfderiv_coe_snd_stiefelRotationFamily_apply (x : stiefel E 2 × sphere (0 : ℂ) 1)
    (p : TangentSpace ((𝓢).prod (𝓡 1)) x) :
    mvfderiv ((𝓢).prod (𝓡 1)) (fun y ↦ ((stiefelRotationFamily y).2 : E)) x p =
      (mvfderiv (𝓡 1) ((↑) : sphere (0 : ℂ) 1 → ℂ) x.2
          (Manifold.tangentSpaceProdEquiv x p).2).re • x.1.1 0 +
        (mvfderiv (𝓡 1) ((↑) : sphere (0 : ℂ) 1 → ℂ) x.2
          (Manifold.tangentSpaceProdEquiv x p).2).im • x.1.1 1 +
        ((x.2 : ℂ).re • mvfderiv 𝓢 ((↑) : stiefel E 2 → Fin 2 → E) x.1
          (Manifold.tangentSpaceProdEquiv x p).1 0 +
        (x.2 : ℂ).im • mvfderiv 𝓢 ((↑) : stiefel E 2 → Fin 2 → E) x.1
          (Manifold.tangentSpaceProdEquiv x p).1 1) := by
  have hι := ((contMDiff_coe_stiefel E 2 (r := 1)) x.1).mdifferentiableAt one_ne_zero
  have hκ := (contMDiff_coe_sphere (E := ℂ) (n := 1) (m := 1) x.2).mdifferentiableAt one_ne_zero
  have hv (i : Fin 2) : MDifferentiableAt ((𝓢).prod (𝓡 1)) 𝓘(ℝ, E)
      (fun y : stiefel E 2 × sphere (0 : ℂ) 1 ↦ (y.1 : Fin 2 → E) i) x :=
    (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ E) i).mdifferentiableAt.comp
      x.1 hι).comp x mdifferentiableAt_fst)
  have hL (L : ℂ →L[ℝ] ℝ) : MDifferentiableAt ((𝓢).prod (𝓡 1)) 𝓘(ℝ)
      (fun y : stiefel E 2 × sphere (0 : ℂ) 1 ↦ L (y.2 : ℂ)) x :=
    (L.mdifferentiableAt.comp x.2 hκ).comp x mdifferentiableAt_snd
  -- Write the map as a sum of products of scalar and vector-valued functions.
  have hf : (fun y : stiefel E 2 × sphere (0 : ℂ) 1 ↦ ((stiefelRotationFamily y).2 : E)) =
      (fun y : stiefel E 2 × sphere (0 : ℂ) 1 ↦ Complex.reCLM (y.2 : ℂ)) •
          (fun y : stiefel E 2 × sphere (0 : ℂ) 1 ↦ (y.1 : Fin 2 → E) 0) +
        (fun y : stiefel E 2 × sphere (0 : ℂ) 1 ↦ Complex.imCLM (y.2 : ℂ)) •
          (fun y : stiefel E 2 × sphere (0 : ℂ) 1 ↦ (y.1 : Fin 2 → E) 1) :=
    funext coe_snd_stiefelRotationFamily
  rw [hf, mvfderiv_add ((hL _).smul (hv 0)) ((hL _).smul (hv 1)),
    mvfderiv_smul (hL _) (hv 0), mvfderiv_smul (hL _) (hv 1)]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply]
  rw [Complex.reCLM.mvfderiv_comp_snd_apply hκ, Complex.imCLM.mvfderiv_comp_snd_apply hκ,
    mvfderiv_stiefel_coe_fst_apply, mvfderiv_stiefel_coe_fst_apply,
    Manifold.tangentSpaceProdEquiv_apply]
  simp only [Complex.reCLM_apply, Complex.imCLM_apply]
  abel

/-- At a point `((u, v), z)` with `Im z ≠ 0`, the derivative of the Stiefel rotation family is
injective. -/
theorem injective_mfderiv_stiefelRotationFamily {x : stiefel E 2 × sphere (0 : ℂ) 1}
    (hx : (x.2 : ℂ).im ≠ 0) :
    Function.Injective
      (mfderiv ((𝓢).prod (𝓡 1)) ((𝓡 (n + 1)).prod (𝓡 (n + 1))) stiefelRotationFamily x) := by
  have hτ : MDifferentiableAt ((𝓢).prod (𝓡 1)) ((𝓡 (n + 1)).prod (𝓡 (n + 1)))
      (stiefelRotationFamily (E := E)) x :=
    (contMDiff_stiefelRotationFamily x).mdifferentiableAt (by simp)
  -- If a tangent vector `(t, c)` is sent to zero, the first component gives `a = 0`, where
  -- `(a, b)` is `t` read in `Fin 2 → E`. Then `b` is orthogonal to `u` and `v`, as `t` is
  -- tangent to the Stiefel manifold, and pairing the second component with `u` and `v` kills
  -- `c`, so that `Im z • b = 0`.
  rw [injective_iff_map_eq_zero]
  intro p hp
  obtain ⟨hu, hv, huv⟩ := mem_stiefel_two_iff.1 x.1.2
  set t := (Manifold.tangentSpaceProdEquiv x p).1
  set γ := mvfderiv (𝓡 1) ((↑) : sphere (0 : ℂ) 1 → ℂ) x.2 (Manifold.tangentSpaceProdEquiv x p).2
  set T := mvfderiv 𝓢 ((↑) : stiefel E 2 → Fin 2 → E) x.1 t
  -- Both components of the image, read in `E`, vanish.
  have hcomp (g : sphere (0 : E) 1 × sphere (0 : E) 1 → E)
      (hg : MDifferentiableAt ((𝓡 (n + 1)).prod (𝓡 (n + 1))) 𝓘(ℝ, E) g
        (stiefelRotationFamily x)) :
      mvfderiv ((𝓢).prod (𝓡 1)) (g ∘ stiefelRotationFamily) x p = 0 := by
    rw [mvfderiv_comp_apply x hg hτ]
    exact (congrArg _ hp).trans (map_zero _)
  have hι₁ : MDifferentiableAt ((𝓡 (n + 1)).prod (𝓡 (n + 1))) 𝓘(ℝ, E)
      (fun q : sphere (0 : E) 1 × sphere (0 : E) 1 ↦ (q.1 : E)) (stiefelRotationFamily x) :=
    ((contMDiff_coe_sphere.comp contMDiff_fst) _).mdifferentiableAt one_ne_zero
  have hι₂ : MDifferentiableAt ((𝓡 (n + 1)).prod (𝓡 (n + 1))) 𝓘(ℝ, E)
      (fun q : sphere (0 : E) 1 × sphere (0 : E) 1 ↦ (q.2 : E)) (stiefelRotationFamily x) :=
    ((contMDiff_coe_sphere.comp contMDiff_snd) _).mdifferentiableAt one_ne_zero
  have h₁ := hcomp _ hι₁
  have h₂ := hcomp _ hι₂
  rw [show (fun q : sphere (0 : E) 1 × sphere (0 : E) 1 ↦ (q.1 : E)) ∘ stiefelRotationFamily =
    fun y ↦ ((stiefelRotationFamily y).1 : E) from rfl,
    mvfderiv_coe_fst_stiefelRotationFamily_apply] at h₁
  rw [show (fun q : sphere (0 : E) 1 × sphere (0 : E) 1 ↦ (q.2 : E)) ∘ stiefelRotationFamily =
    fun y ↦ ((stiefelRotationFamily y).2 : E) from rfl,
    mvfderiv_coe_snd_stiefelRotationFamily_apply] at h₂
  -- Restate both components with the abbreviations `T` and `γ` introduced above.
  change T 0 = 0 at h₁
  change γ.re • x.1.1 0 + γ.im • x.1.1 1 + ((x.2 : ℂ).re • T 0 + (x.2 : ℂ).im • T 1) = 0 at h₂
  -- `T` is tangent to the Stiefel manifold.
  have hT : gramSym2Deriv E 2 x.1.1 T = 0 := gramSym2Deriv_mfderiv_coe_stiefel x.1 t
  have h01 := congrFun hT s(0, 1)
  have h11 := congrFun hT s(1, 1)
  simp only [gramSym2Deriv_apply_mk, h₁, inner_zero_left, add_zero, Pi.zero_apply] at h01 h11
  have h11' : ⟪x.1.1 1, T 1⟫ = 0 := by
    rw [real_inner_comm (T 1) (x.1.1 1)] at h11 ⊢
    linarith
  rw [h₁, smul_zero, zero_add] at h₂
  have hu' : ⟪x.1.1 0, x.1.1 0⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hu, one_pow]
  have hv' : ⟪x.1.1 1, x.1.1 1⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hv, one_pow]
  have hre := congrArg (fun e ↦ ⟪x.1.1 0, e⟫) h₂
  have him := congrArg (fun e ↦ ⟪x.1.1 1, e⟫) h₂
  simp only [inner_add_right, inner_smul_right, hu', huv, h01, real_inner_comm (x.1.1 0),
    hv', h11', inner_zero_right] at hre him
  have hγre : γ.re = 0 := by linarith
  have hγim : γ.im = 0 := by linarith
  rw [hγre, hγim, zero_smul, zero_smul, zero_add, zero_add, smul_eq_zero] at h₂
  have hT1 : T 1 = 0 := h₂.resolve_left hx
  have hT0 : T = 0 := funext fun i ↦ by fin_cases i <;> simp [h₁, hT1]
  have ht : t = 0 := injective_mfderiv_coe_stiefel x.1 (hT0.trans (map_zero _).symm)
  have hc : (Manifold.tangentSpaceProdEquiv x p).2 = 0 :=
    injective_mvfderiv_subtypeVal_sphere x.2 ((Complex.ext hγre hγim).trans (map_zero _).symm)
  apply (Manifold.tangentSpaceProdEquiv x).injective
  rw [map_zero]
  exact Prod.ext ht hc

/-- At a point `((u, v), z)` with `Im z ≠ 0`, the derivative of the Stiefel rotation family is
invertible. -/
theorem isInvertible_mfderiv_stiefelRotationFamily {x : stiefel E 2 × sphere (0 : ℂ) 1}
    (hx : (x.2 : ℂ).im ≠ 0) :
    (mfderiv ((𝓢).prod (𝓡 1)) ((𝓡 (n + 1)).prod (𝓡 (n + 1))) stiefelRotationFamily
      x).IsInvertible := by
  refine isInvertible_mfderiv_of_injective ?_ (injective_mfderiv_stiefelRotationFamily hx)
  rw [finrank_prod, finrank_prod, finrank_stiefelTwoModel (n := n), finrank_euclideanSpace_fin,
    finrank_euclideanSpace_fin]
  ring

/-- Every point `(u, q)` of `Sⁿ⁺¹ × Sⁿ⁺¹` with `q ≠ ±u` is a regular value of the Stiefel
rotation family. -/
theorem isRegularValue_stiefelRotationFamily {y : sphere (0 : E) 1 × sphere (0 : E) 1}
    (hy : y.2 ≠ y.1) (hy' : y.2 ≠ -y.1) :
    IsRegularValue ((𝓢).prod (𝓡 1)) ((𝓡 (n + 1)).prod (𝓡 (n + 1))) stiefelRotationFamily y := by
  rw [isRegularValue_iff]
  intro x hx
  rw [isRegularPoint_iff]
  exact (isInvertible_mfderiv_stiefelRotationFamily
    (im_ne_zero_of_stiefelRotationFamily_eq hy hy' hx)).surjective

/-! ### Orientation signs -/

/-- The orientation sign of the involution `((u, v), z) ↦ ((u, -v), conj z)` is `(-1)ⁿ`: the
frame reflection has sign `(-1)ⁿ⁺¹` and conjugation reverses `S¹`. -/
theorem orientationSign_stiefelRotationInvolution
    (O : _root_.Orientation ℝ (Fin 2 → E) (Fin (2 * n + 4)))
    (x : stiefel E 2 × sphere (0 : ℂ) 1) :
    orientationSign (O.stiefelTwoOrientation.prod Complex.orientation.sphereOrientation)
      (O.stiefelTwoOrientation.prod Complex.orientation.sphereOrientation)
      stiefelRotationInvolution x = (-1) ^ n := by
  rw [stiefelRotationInvolution_eq_prodMap]
  have hconj := isOrientationReversingAt_conjSphere x.2
  rw [← isOrientationPreservingAt_neg_right] at hconj
  rcases Nat.even_or_odd n with hn | hn
  · have hK := isOrientationReversingAt_stiefelTwoReflection hn O x.1
    rw [← isOrientationPreservingAt_neg_right] at hK
    have h := hK.prodMap hconj
    rw [prod_neg_neg] at h
    exact (orientationSign_of_isOrientationPreservingAt h).trans hn.neg_one_pow.symm
  · have hK := isOrientationPreservingAt_stiefelTwoReflection hn O x.1
    have h := hK.prodMap hconj
    rw [prod_neg_right, isOrientationPreservingAt_neg_right] at h
    exact (orientationSign_of_isOrientationReversingAt h).trans hn.neg_one_pow.symm

/-! ### The degree -/

/-- **The degree of the Stiefel rotation family.** At every point `(u, q)` of `Sⁿ⁺¹ × Sⁿ⁺¹` with
`q ≠ ±u`, a regular value (`TauCeti.isRegularValue_stiefelRotationFamily`), the Stiefel rotation
family `T¹Sⁿ⁺¹ × S¹ → Sⁿ⁺¹ × Sⁿ⁺¹` has degree `±(1 + (-1)ⁿ)` for the normal orientation
`O.stiefelTwoOrientation` of `T¹Sⁿ⁺¹`, the standard orientation of `S¹`, and any orientation of the
target. The two preimages of `(u, q)` are exchanged by an involution of orientation sign `(-1)ⁿ`
that leaves the map unchanged, so they contribute `s` and `(-1)ⁿ s` with `s = ±1`. -/
theorem exists_degreeAtRegularValue_stiefelRotationFamily_eq
    (O : _root_.Orientation ℝ (Fin 2 → E) (Fin (2 * n + 4)))
    (o : Manifold.Orientation ((𝓡 (n + 1)).prod (𝓡 (n + 1)))
      (sphere (0 : E) 1 × sphere (0 : E) 1) (Fin (2 * n + 1 + 1)))
    {y : sphere (0 : E) 1 × sphere (0 : E) 1} (hy : y.2 ≠ y.1) (hy' : y.2 ≠ -y.1) :
    ∃ s : ℤ, (s = 1 ∨ s = -1) ∧
      degreeAtRegularValue (O.stiefelTwoOrientation.prod Complex.orientation.sphereOrientation)
        o stiefelRotationFamily y = s * (1 + (-1) ^ n) := by
  classical
  set oD := O.stiefelTwoOrientation.prod Complex.orientation.sphereOrientation
  obtain ⟨x, hxim, hx⟩ := exists_stiefelRotationFamily_eq hy hy'
  have hxy : stiefelRotationFamily x = y := hx
  subst hxy
  have hne : x ≠ stiefelRotationInvolution x := fun h ↦ by
    have h' := congrArg (fun y : stiefel E 2 × sphere (0 : ℂ) 1 ↦ (y.2 : ℂ).im) h
    simp only [snd_stiefelRotationInvolution, coe_conjSphere, Complex.conj_im] at h'
    linarith
  -- The orientation signs at the two preimages differ by the sign `(-1)ⁿ` of the involution.
  have hτ : MDifferentiableAt ((𝓢).prod (𝓡 1)) ((𝓡 (n + 1)).prod (𝓡 (n + 1)))
      (stiefelRotationFamily (E := E)) (stiefelRotationInvolution x) :=
    (contMDiff_stiefelRotationFamily (stiefelRotationInvolution x)).mdifferentiableAt (by simp)
  have hJ : MDifferentiableAt ((𝓢).prod (𝓡 1)) ((𝓢).prod (𝓡 1))
      (stiefelRotationInvolution (E := E)) x :=
    ((contMDiff_stiefelRotationInvolution (r := 1)) x).mdifferentiableAt one_ne_zero
  have hcomp := orientationSign_comp (o := oD) (o' := oD) (o'' := o) hτ hJ
  have hfun : stiefelRotationFamily ∘ stiefelRotationInvolution = stiefelRotationFamily (E := E) :=
    funext stiefelRotationFamily_stiefelRotationInvolution
  rw [hfun, orientationSign_stiefelRotationInvolution] at hcomp
  set s := orientationSign oD o stiefelRotationFamily x
  have hs : s = 1 ∨ s = -1 := orientationSign_eq_one_or_eq_neg_one
    (isInvertible_mfderiv_stiefelRotationFamily hxim.ne')
  have hs' : orientationSign oD o stiefelRotationFamily (stiefelRotationInvolution x) =
      (-1) ^ n * s := by
    have h2 : ((-1 : ℤ) ^ n) * (-1) ^ n = 1 := by rw [← mul_pow]; norm_num
    linear_combination (-(-1 : ℤ) ^ n) * hcomp -
      orientationSign oD o stiefelRotationFamily (stiefelRotationInvolution x) * h2
  refine ⟨s, hs, ?_⟩
  rw [degreeAtRegularValue_eq_sum (s := {x, stiefelRotationInvolution x}) fun y ↦ ?_,
    Finset.sum_pair hne, hs']
  · ring
  rw [Finset.mem_insert, Finset.mem_singleton,
    stiefelRotationFamily_eq_iff_eq_or_eq_stiefelRotationInvolution hxim.ne']

/-- For even `n`, the Stiefel rotation family `T¹Sⁿ⁺¹ × S¹ → Sⁿ⁺¹ × Sⁿ⁺¹` has degree `±2` at
every point `(u, q)` with `q ≠ ±u`. -/
theorem abs_degreeAtRegularValue_stiefelRotationFamily_of_even (hn : Even n)
    (O : _root_.Orientation ℝ (Fin 2 → E) (Fin (2 * n + 4)))
    (o : Manifold.Orientation ((𝓡 (n + 1)).prod (𝓡 (n + 1)))
      (sphere (0 : E) 1 × sphere (0 : E) 1) (Fin (2 * n + 1 + 1)))
    {y : sphere (0 : E) 1 × sphere (0 : E) 1} (hy : y.2 ≠ y.1) (hy' : y.2 ≠ -y.1) :
    |degreeAtRegularValue (O.stiefelTwoOrientation.prod Complex.orientation.sphereOrientation)
      o stiefelRotationFamily y| = 2 := by
  obtain ⟨s, hs, h⟩ := exists_degreeAtRegularValue_stiefelRotationFamily_eq O o hy hy'
  rw [h, hn.neg_one_pow]
  rcases hs with rfl | rfl <;> norm_num

/-- For odd `n`, the Stiefel rotation family `T¹Sⁿ⁺¹ × S¹ → Sⁿ⁺¹ × Sⁿ⁺¹` has degree `0` at every
point `(u, q)` with `q ≠ ±u`. -/
theorem degreeAtRegularValue_stiefelRotationFamily_of_odd (hn : Odd n)
    (O : _root_.Orientation ℝ (Fin 2 → E) (Fin (2 * n + 4)))
    (o : Manifold.Orientation ((𝓡 (n + 1)).prod (𝓡 (n + 1)))
      (sphere (0 : E) 1 × sphere (0 : E) 1) (Fin (2 * n + 1 + 1)))
    {y : sphere (0 : E) 1 × sphere (0 : E) 1} (hy : y.2 ≠ y.1) (hy' : y.2 ≠ -y.1) :
    degreeAtRegularValue (O.stiefelTwoOrientation.prod Complex.orientation.sphereOrientation)
      o stiefelRotationFamily y = 0 := by
  obtain ⟨s, -, h⟩ := exists_degreeAtRegularValue_stiefelRotationFamily_eq O o hy hy'
  rw [h, hn.neg_one_pow]
  ring

end TauCeti
