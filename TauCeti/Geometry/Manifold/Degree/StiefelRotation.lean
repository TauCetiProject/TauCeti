/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Complex.Orientation
public import TauCeti.Geometry.Manifold.Degree.Basic
public import TauCeti.Geometry.Manifold.Instances.Sphere
public import TauCeti.Geometry.Manifold.Orientation.Prod
public import TauCeti.Geometry.Manifold.Orientation.Sphere
public import TauCeti.Geometry.Manifold.Orientation.Stiefel
import TauCeti.Analysis.Complex.Circle
import TauCeti.Geometry.Manifold.Degree.SphereRotation
import TauCeti.Geometry.Manifold.MFDeriv.IsInvertible
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.MFDeriv.Prod

/-!
# The rotation map of the unit tangent bundle of a sphere and its degree

Let `E` be a real inner product space of dimension `n = m + 2`, with unit sphere `Sⁿ⁻¹`. Its unit
tangent bundle `T¹Sⁿ⁻¹` is the Stiefel manifold `TauCeti.stiefel E 2` of orthonormal pairs
`(u, v)`. Rotating `u` towards `v` by the angle of `z ∈ S¹` gives the **Stiefel rotation map**
(`TauCeti.stiefelTwoRotation`)

`τ : T¹Sⁿ⁻¹ × S¹ → Sⁿ⁻¹ × Sⁿ⁻¹`, `τ ((u, v), z) = (u, Re z • u + Im z • v)`,

with `S¹` the unit circle of `ℂ`. This is the map `τ` of the proof of Proposition 6.17 of
Barraud–Damian–Humilière–Oancea, written there with `z = e^{iθ}`. Over each `u` it is the
rotation family of `Sⁿ⁻¹` at `u` (`TauCeti.sphereRotationFamily`).

Its derivative is computed in `TauCeti.mvfderiv_coe_snd_stiefelTwoRotation_apply`. At a point with
`Im z ≠ 0` it is invertible (`TauCeti.isInvertible_mfderiv_stiefelTwoRotation`). A point
`(u, q)` with `q ≠ ±u` has exactly two preimages, which are exchanged by the involution
`((u, v), z) ↦ ((u, -v), conj z)` (`TauCeti.stiefelTwoRotation_eq_iff`), so it is a regular value
(`TauCeti.isRegularValue_stiefelTwoRotation`). Because `τ` is unchanged by this involution, the
orientation signs at the two preimages differ by the orientation sign of the involution. That sign
is computed from the frame reflection `(u, v) ↦ (u, -v)` of the Stiefel manifold, of sign
`(-1)ⁿ⁺¹` for the orientations `TauCeti.stiefelTwoOrientation Ω`, and from complex conjugation on
`S¹`, which reverses its orientation. So it is `(-1)ⁿ`, and the degree of `τ` at a regular value is
`±(1 + (-1)ⁿ)` (`TauCeti.degreeAtRegularValue_stiefelTwoRotation`), for every orientation of the
target: `±2` when `n` is even and `0` when `n` is odd. This is the degree computation of the
proof of Proposition 6.17, together with the vanishing for odd spheres of its footnote 16.

In the statements `n = m + 2`, so that `Sⁿ⁻¹ = Sᵐ⁺¹` is modelled on `ℝᵐ⁺¹`, and `T¹Sⁿ⁻¹` has
dimension `2 m + 1`.

## Main declarations

* `TauCeti.stiefelTwoRotation`: the map `((u, v), z) ↦ (u, Re z • u + Im z • v)`.
* `TauCeti.contMDiff_stiefelTwoRotation`: it is smooth.
* `TauCeti.isInvertible_mfderiv_stiefelTwoRotation`: its derivative is invertible where
  `Im z ≠ 0`.
* `TauCeti.stiefelTwoRotationInvolution`: the involution `((u, v), z) ↦ ((u, -v), conj z)`, under
  which the map is invariant.
* `TauCeti.stiefelTwoRotation_eq_iff`: the two preimages of a point `(u, q)` with `q ≠ ±u`.
* `TauCeti.isRegularValue_stiefelTwoRotation`: such points are regular values.
* `TauCeti.degreeAtRegularValue_stiefelTwoRotation`: the degree is `±(1 + (-1)ⁿ)` there.
* `TauCeti.abs_degreeAtRegularValue_stiefelTwoRotation_of_even`,
  `TauCeti.degreeAtRegularValue_stiefelTwoRotation_of_odd`: it is `±2` for even `n` and `0` for odd
  `n`.

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
  {m : ℕ} [Fact (finrank ℝ E = m + 1 + 1)]

/-- The model space of the Stiefel manifold of orthonormal two-frames of `E`. -/
local notation "𝓢" => 𝓘(ℝ, Fin (2 * finrank ℝ E - Nat.choose (2 + 1) 2) → ℝ)

/-! ### The rotation map -/

/-- The second vector `v` of an orthonormal pair `(u, v)` with `u = p`, as a unit vector of `p^⊥`,
the space of the rotation family of the sphere at `p`. -/
private def stiefelTwoSnd (p : sphere (0 : E) 1) (w : stiefel E 2) (hw : w.1 0 = p) :
    sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 :=
  ⟨⟨w.1 1, Submodule.mem_orthogonal_singleton_iff_inner_right.2
      (hw ▸ (mem_stiefel_two_iff.1 w.2).2.2)⟩,
    mem_sphere_zero_iff_norm.2 (mem_stiefel_two_iff.1 w.2).2.1⟩

omit [FiniteDimensional ℝ E] [Fact (finrank ℝ E = m + 1 + 1)] in
private theorem coe_stiefelTwoSnd (p : sphere (0 : E) 1) (w : stiefel E 2) (hw : w.1 0 = p) :
    ((stiefelTwoSnd p w hw : (ℝ ∙ (p : E))ᗮ) : E) = w.1 1 :=
  rfl

/-- The **Stiefel rotation map** `T¹Sⁿ⁻¹ × S¹ → Sⁿ⁻¹ × Sⁿ⁻¹`: an orthonormal pair `(u, v)`, a
point `u` of the unit sphere with a unit tangent vector `v` at it, and a point `z` of the unit
circle of `ℂ` are sent to `u` and to `Re z • u + Im z • v`, the point reached by rotating `u`
towards `v` by the angle of `z`. -/
def stiefelTwoRotation (x : stiefel E 2 × sphere (0 : ℂ) 1) :
    sphere (0 : E) 1 × sphere (0 : E) 1 :=
  (stiefelProj E 2 0 x.1, sphereRotationFamily (stiefelProj E 2 0 x.1)
    (stiefelTwoSnd _ x.1 (coe_stiefelProj 0 x.1).symm, x.2))

omit [FiniteDimensional ℝ E] [Fact (finrank ℝ E = m + 1 + 1)] in
@[simp]
theorem coe_fst_stiefelTwoRotation (x : stiefel E 2 × sphere (0 : ℂ) 1) :
    ((stiefelTwoRotation x).1 : E) = x.1.1 0 :=
  coe_stiefelProj 0 x.1

omit [FiniteDimensional ℝ E] [Fact (finrank ℝ E = m + 1 + 1)] in
@[simp]
theorem coe_snd_stiefelTwoRotation (x : stiefel E 2 × sphere (0 : ℂ) 1) :
    ((stiefelTwoRotation x).2 : E) = (x.2 : ℂ).re • x.1.1 0 + (x.2 : ℂ).im • x.1.1 1 := by
  simp [stiefelTwoRotation, coe_stiefelTwoSnd]

/-- The smooth map `((u, v), z) ↦ (u, v)`, read in `Fin 2 → E`. -/
private theorem contMDiff_coe_fst {r : ℕ∞ω} :
    ContMDiff ((𝓢).prod (𝓡 1)) 𝓘(ℝ, Fin 2 → E) r
      fun x : stiefel E 2 × sphere (0 : ℂ) 1 ↦ (x.1 : Fin 2 → E) :=
  (contMDiff_coe_stiefel E 2).comp contMDiff_fst

/-- The Stiefel rotation map is smooth. -/
theorem contMDiff_stiefelTwoRotation {r : ℕ∞ω} :
    ContMDiff ((𝓢).prod (𝓡 1)) ((𝓡 (m + 1)).prod (𝓡 (m + 1))) r
      (stiefelTwoRotation (E := E)) := by
  have hz : ContMDiff ((𝓢).prod (𝓡 1)) 𝓘(ℝ, ℂ) r
      fun x : stiefel E 2 × sphere (0 : ℂ) 1 ↦ (x.2 : ℂ) :=
    contMDiff_coe_sphere.comp contMDiff_snd
  have hv (i : Fin 2) : ContMDiff ((𝓢).prod (𝓡 1)) 𝓘(ℝ, E) r
      fun x : stiefel E 2 × sphere (0 : ℂ) 1 ↦ (x.1 : Fin 2 → E) i :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ E) i).contMDiff.comp contMDiff_coe_fst
  have h₂ : ContMDiff ((𝓢).prod (𝓡 1)) (𝓡 (m + 1)) r
      fun x : stiefel E 2 × sphere (0 : ℂ) 1 ↦ (stiefelTwoRotation x).2 := by
    convert ContMDiff.codRestrict_sphere
      (((Complex.reCLM.contMDiff.comp hz).smul (hv 0)).add
        ((Complex.imCLM.contMDiff.comp hz).smul (hv 1)))
      fun x ↦ show (x.2 : ℂ).re • x.1.1 0 + (x.2 : ℂ).im • x.1.1 1 ∈ sphere (0 : E) 1 from
        coe_snd_stiefelTwoRotation x ▸ (stiefelTwoRotation x).2.2 using 1
    exact funext fun x ↦ Subtype.ext (coe_snd_stiefelTwoRotation x)
  exact ((contMDiff_stiefelProj E 2 0).comp contMDiff_fst).prodMk h₂

/-! ### The derivative -/

/-- Read in `E`, the derivative of the first component `((u, v), z) ↦ u` of the Stiefel rotation
map sends a tangent vector `(t, c)` to the first vector of `t`, read in `Fin 2 → E`. -/
theorem mvfderiv_coe_fst_stiefelTwoRotation_apply (x : stiefel E 2 × sphere (0 : ℂ) 1)
    (p : TangentSpace ((𝓢).prod (𝓡 1)) x) :
    mvfderiv ((𝓢).prod (𝓡 1)) (fun y ↦ ((stiefelTwoRotation y).1 : E)) x p =
      mvfderiv 𝓢 ((↑) : stiefel E 2 → Fin 2 → E) x.1 (Manifold.tangentSpaceProdEquiv x p).1 0 := by
  have hι := ((contMDiff_coe_stiefel E 2 (r := 1)) x.1).mdifferentiableAt one_ne_zero
  have hf : (fun y : stiefel E 2 × sphere (0 : ℂ) 1 ↦ ((stiefelTwoRotation y).1 : E)) =
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ E) 0) ∘
        ((↑) : stiefel E 2 → Fin 2 → E)) ∘ Prod.fst :=
    funext fun y ↦ coe_fst_stiefelTwoRotation y
  rw [hf, mvfderiv_comp_fst_apply, Manifold.tangentSpaceProdEquiv_apply]
  exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ E) 0).mvfderiv_comp_apply hι p.1

/-- **The derivative of the Stiefel rotation map.** Read in `E`, the derivative of the second
component `((u, v), z) ↦ Re z • u + Im z • v` sends a tangent vector `(t, c)` at `((u, v), z)` to
`Re γ • u + Im γ • v + Re z • a + Im z • b`, where `(a, b)` is `t` read in `Fin 2 → E` and `γ` is
`c` read in `ℂ`. -/
theorem mvfderiv_coe_snd_stiefelTwoRotation_apply (x : stiefel E 2 × sphere (0 : ℂ) 1)
    (p : TangentSpace ((𝓢).prod (𝓡 1)) x) :
    mvfderiv ((𝓢).prod (𝓡 1)) (fun y ↦ ((stiefelTwoRotation y).2 : E)) x p =
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
  have hv' (i : Fin 2) : mvfderiv ((𝓢).prod (𝓡 1))
      (fun y : stiefel E 2 × sphere (0 : ℂ) 1 ↦ (y.1 : Fin 2 → E) i) x p =
      mvfderiv 𝓢 ((↑) : stiefel E 2 → Fin 2 → E) x.1 (Manifold.tangentSpaceProdEquiv x p).1 i := by
    have hf : (fun y : stiefel E 2 × sphere (0 : ℂ) 1 ↦ (y.1 : Fin 2 → E) i) =
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ E) i) ∘
          ((↑) : stiefel E 2 → Fin 2 → E)) ∘ Prod.fst := rfl
    rw [hf, mvfderiv_comp_fst_apply, Manifold.tangentSpaceProdEquiv_apply]
    exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ E) i).mvfderiv_comp_apply hι
      p.1
  have hL' (L : ℂ →L[ℝ] ℝ) : mvfderiv ((𝓢).prod (𝓡 1))
      (fun y : stiefel E 2 × sphere (0 : ℂ) 1 ↦ L (y.2 : ℂ)) x p =
      L (mvfderiv (𝓡 1) ((↑) : sphere (0 : ℂ) 1 → ℂ) x.2
        (Manifold.tangentSpaceProdEquiv x p).2) := by
    have hf : (fun y : stiefel E 2 × sphere (0 : ℂ) 1 ↦ L (y.2 : ℂ)) =
        (L ∘ ((↑) : sphere (0 : ℂ) 1 → ℂ)) ∘ Prod.snd := rfl
    rw [hf, mvfderiv_comp_snd_apply, Manifold.tangentSpaceProdEquiv_apply]
    exact L.mvfderiv_comp_apply hκ p.2
  -- Write the map as a sum of products of scalar and vector-valued functions.
  have hf : (fun y : stiefel E 2 × sphere (0 : ℂ) 1 ↦ ((stiefelTwoRotation y).2 : E)) =
      (fun y : stiefel E 2 × sphere (0 : ℂ) 1 ↦ Complex.reCLM (y.2 : ℂ)) •
          (fun y : stiefel E 2 × sphere (0 : ℂ) 1 ↦ (y.1 : Fin 2 → E) 0) +
        (fun y : stiefel E 2 × sphere (0 : ℂ) 1 ↦ Complex.imCLM (y.2 : ℂ)) •
          (fun y : stiefel E 2 × sphere (0 : ℂ) 1 ↦ (y.1 : Fin 2 → E) 1) :=
    funext coe_snd_stiefelTwoRotation
  rw [hf, mvfderiv_add ((hL _).smul (hv 0)) ((hL _).smul (hv 1)),
    mvfderiv_smul (hL _) (hv 0), mvfderiv_smul (hL _) (hv 1)]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply]
  rw [hL' Complex.reCLM, hL' Complex.imCLM, hv' 0, hv' 1]
  simp only [Complex.reCLM_apply, Complex.imCLM_apply]
  abel

/-- At a point `((u, v), z)` with `Im z ≠ 0`, the derivative of the Stiefel rotation map is
invertible. -/
theorem isInvertible_mfderiv_stiefelTwoRotation {x : stiefel E 2 × sphere (0 : ℂ) 1}
    (hx : (x.2 : ℂ).im ≠ 0) :
    (mfderiv ((𝓢).prod (𝓡 1)) ((𝓡 (m + 1)).prod (𝓡 (m + 1))) stiefelTwoRotation
      x).IsInvertible := by
  have hτ : MDifferentiableAt ((𝓢).prod (𝓡 1)) ((𝓡 (m + 1)).prod (𝓡 (m + 1)))
      (stiefelTwoRotation (E := E)) x :=
    ((contMDiff_stiefelTwoRotation (r := 1)) x).mdifferentiableAt one_ne_zero
  have hdim : finrank ℝ (TangentSpace ((𝓢).prod (𝓡 1)) x) =
      finrank ℝ (TangentSpace ((𝓡 (m + 1)).prod (𝓡 (m + 1))) (stiefelTwoRotation x)) := by
    -- The tangent spaces are, by definition, the model vector spaces.
    change finrank ℝ ((Fin (2 * finrank ℝ E - Nat.choose (2 + 1) 2) → ℝ) ×
        EuclideanSpace ℝ (Fin 1)) =
      finrank ℝ (EuclideanSpace ℝ (Fin (m + 1)) × EuclideanSpace ℝ (Fin (m + 1)))
    rw [finrank_prod, finrank_prod, finrank_stiefelTwoModel (m := m), finrank_euclideanSpace_fin,
      finrank_euclideanSpace_fin]
    ring
  have hinj : Function.Injective
      (mfderiv ((𝓢).prod (𝓡 1)) ((𝓡 (m + 1)).prod (𝓡 (m + 1))) stiefelTwoRotation x) := by
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
        (hg : MDifferentiableAt ((𝓡 (m + 1)).prod (𝓡 (m + 1))) 𝓘(ℝ, E) g (stiefelTwoRotation x)) :
        mvfderiv ((𝓢).prod (𝓡 1)) (g ∘ stiefelTwoRotation) x p = 0 := by
      rw [mvfderiv_comp_apply x hg hτ]
      exact (congrArg _ hp).trans (map_zero _)
    have hι₁ : MDifferentiableAt ((𝓡 (m + 1)).prod (𝓡 (m + 1))) 𝓘(ℝ, E)
        (fun q : sphere (0 : E) 1 × sphere (0 : E) 1 ↦ (q.1 : E)) (stiefelTwoRotation x) :=
      ((contMDiff_coe_sphere.comp contMDiff_fst) _).mdifferentiableAt one_ne_zero
    have hι₂ : MDifferentiableAt ((𝓡 (m + 1)).prod (𝓡 (m + 1))) 𝓘(ℝ, E)
        (fun q : sphere (0 : E) 1 × sphere (0 : E) 1 ↦ (q.2 : E)) (stiefelTwoRotation x) :=
      ((contMDiff_coe_sphere.comp contMDiff_snd) _).mdifferentiableAt one_ne_zero
    have h₁ := hcomp _ hι₁
    have h₂ := hcomp _ hι₂
    rw [show (fun q : sphere (0 : E) 1 × sphere (0 : E) 1 ↦ (q.1 : E)) ∘ stiefelTwoRotation =
      fun y ↦ ((stiefelTwoRotation y).1 : E) from rfl,
      mvfderiv_coe_fst_stiefelTwoRotation_apply] at h₁
    rw [show (fun q : sphere (0 : E) 1 × sphere (0 : E) 1 ↦ (q.2 : E)) ∘ stiefelTwoRotation =
      fun y ↦ ((stiefelTwoRotation y).2 : E) from rfl,
      mvfderiv_coe_snd_stiefelTwoRotation_apply] at h₂
    -- Restate both components with the abbreviations `T` and `γ` introduced above.
    change T 0 = 0 at h₁
    change γ.re • x.1.1 0 + γ.im • x.1.1 1 + ((x.2 : ℂ).re • T 0 + (x.2 : ℂ).im • T 1) = 0 at h₂
    -- `T` is tangent to the Stiefel manifold.
    have hT : gramSym2Deriv E 2 x.1.1 T = 0 := by
      have h : T ∈ LinearMap.range
          (mfderiv 𝓢 𝓘(ℝ, Fin 2 → E) ((↑) : stiefel E 2 → Fin 2 → E) x.1).toLinearMap :=
        ⟨t, rfl⟩
      rwa [range_mfderiv_coe_stiefel] at h
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
  exact ⟨(LinearEquiv.ofBijective _
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hinj⟩
      ).toContinuousLinearEquiv, ContinuousLinearMap.ext fun _ ↦ rfl⟩

/-! ### Fibres -/

/-- The involution `((u, v), z) ↦ ((u, -v), conj z)` of `T¹Sⁿ⁻¹ × S¹`, under which the Stiefel
rotation map is invariant (`TauCeti.stiefelTwoRotation_stiefelTwoRotationInvolution`). -/
def stiefelTwoRotationInvolution (x : stiefel E 2 × sphere (0 : ℂ) 1) :
    stiefel E 2 × sphere (0 : ℂ) 1 :=
  (stiefelTwoReflection x.1, ⟨(starRingEnd ℂ) (x.2 : ℂ), by simp⟩)

omit [FiniteDimensional ℝ E] [Fact (finrank ℝ E = m + 1 + 1)] in
@[simp]
theorem fst_stiefelTwoRotationInvolution (x : stiefel E 2 × sphere (0 : ℂ) 1) :
    (stiefelTwoRotationInvolution x).1 = stiefelTwoReflection x.1 :=
  (rfl)

omit [FiniteDimensional ℝ E] [Fact (finrank ℝ E = m + 1 + 1)] in
@[simp]
theorem coe_snd_stiefelTwoRotationInvolution (x : stiefel E 2 × sphere (0 : ℂ) 1) :
    ((stiefelTwoRotationInvolution x).2 : ℂ) = (starRingEnd ℂ) (x.2 : ℂ) :=
  (rfl)

omit [FiniteDimensional ℝ E] [Fact (finrank ℝ E = m + 1 + 1)] in
/-- The map `((u, v), z) ↦ ((u, -v), conj z)` is an involution. -/
@[simp]
theorem stiefelTwoRotationInvolution_stiefelTwoRotationInvolution
    (x : stiefel E 2 × sphere (0 : ℂ) 1) :
    stiefelTwoRotationInvolution (stiefelTwoRotationInvolution x) = x :=
  Prod.ext (stiefelTwoReflection_stiefelTwoReflection x.1) (Subtype.ext (by simp))

omit [FiniteDimensional ℝ E] [Fact (finrank ℝ E = m + 1 + 1)] in
@[simp]
theorem stiefelTwoRotation_stiefelTwoRotationInvolution (x : stiefel E 2 × sphere (0 : ℂ) 1) :
    stiefelTwoRotation (stiefelTwoRotationInvolution x) = stiefelTwoRotation x := by
  refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
  · simp [stiefelTwoRotationInvolution]
  · simp [stiefelTwoRotationInvolution]

omit [FiniteDimensional ℝ E] [Fact (finrank ℝ E = m + 1 + 1)] in
/-- Two points of `T¹Sⁿ⁻¹ × S¹`, one of them off `Im z = 0`, have the same image under the Stiefel
rotation map exactly when they are equal or exchanged by `((u, v), z) ↦ ((u, -v), conj z)`. -/
theorem stiefelTwoRotation_eq_iff {x y : stiefel E 2 × sphere (0 : ℂ) 1}
    (hx : (x.2 : ℂ).im ≠ 0) :
    stiefelTwoRotation y = stiefelTwoRotation x ↔ y = x ∨ y = stiefelTwoRotationInvolution x := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · set p := stiefelProj E 2 0 x.1
    have hp : x.1.1 0 = (p : E) := (coe_stiefelProj 0 x.1).symm
    have h₁ : y.1.1 0 = x.1.1 0 := by
      simpa using congrArg (fun q : sphere (0 : E) 1 × sphere (0 : E) 1 ↦ (q.1 : E)) h
    -- Both points lie in the domain of the rotation family of the sphere at `u`.
    have h₂ : sphereRotationFamily p (stiefelTwoSnd p y.1 (h₁.trans hp), y.2) =
        sphereRotationFamily p (stiefelTwoSnd p x.1 hp, x.2) := by
      have h' := congrArg (fun q : sphere (0 : E) 1 × sphere (0 : E) 1 ↦ (q.2 : E)) h
      simp only [coe_snd_stiefelTwoRotation, h₁] at h'
      refine Subtype.ext ?_
      simpa only [coe_sphereRotationFamily, coe_stiefelTwoSnd, ← hp] using h'
    rcases (sphereRotationFamily_eq_sphereRotationFamily_iff p hx).1 h₂ with h₃ | ⟨hv, hz⟩
    · have hv : y.1.1 1 = x.1.1 1 := congrArg (fun q ↦ ((q.1 : (ℝ ∙ (p : E))ᗮ) : E)) h₃
      refine .inl (Prod.ext (Subtype.ext (funext fun i ↦ ?_)) (Prod.mk.inj h₃).2)
      fin_cases i
      exacts [h₁, hv]
    · refine .inr (Prod.ext (Subtype.ext (funext fun i ↦ ?_)) (Subtype.ext (by simpa using hz)))
      rw [coe_stiefelTwoSnd, coe_stiefelTwoSnd] at hv
      fin_cases i
      · simpa using h₁
      · simpa using hv
  · rintro (rfl | rfl)
    · rfl
    · exact stiefelTwoRotation_stiefelTwoRotationInvolution x

omit [FiniteDimensional ℝ E] in
/-- Every point `(u, q)` of `Sⁿ⁻¹ × Sⁿ⁻¹` with `q ≠ ±u` is the image of a point with `Im z > 0`. -/
theorem exists_stiefelTwoRotation_eq {y : sphere (0 : E) 1 × sphere (0 : E) 1}
    (hy : y.2 ≠ y.1) (hy' : y.2 ≠ -y.1) :
    ∃ x, 0 < (x.2 : ℂ).im ∧ stiefelTwoRotation x = y := by
  obtain ⟨⟨v, z⟩, hz, hvz⟩ := exists_sphereRotationFamily_eq y.1 hy hy'
  have hv : ⟪(y.1 : E), ((v : (ℝ ∙ (y.1 : E))ᗮ) : E)⟫ = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.1 (v : (ℝ ∙ (y.1 : E))ᗮ).2
  refine ⟨(⟨![(y.1 : E), ((v : (ℝ ∙ (y.1 : E))ᗮ) : E)], mem_stiefel_two_iff.2
    ⟨by simp, by
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
      exact (norm_eq_of_mem_sphere v : ‖((v : (ℝ ∙ (y.1 : E))ᗮ) : E)‖ = 1), hv⟩⟩, z),
    hz, Prod.ext (Subtype.ext (by simp)) (Subtype.ext ?_)⟩
  rw [← hvz]
  simp

/-- Every point `(u, q)` of `Sⁿ⁻¹ × Sⁿ⁻¹` with `q ≠ ±u` is a regular value of the Stiefel
rotation map. -/
theorem isRegularValue_stiefelTwoRotation {y : sphere (0 : E) 1 × sphere (0 : E) 1}
    (hy : y.2 ≠ y.1) (hy' : y.2 ≠ -y.1) :
    IsRegularValue ((𝓢).prod (𝓡 1)) ((𝓡 (m + 1)).prod (𝓡 (m + 1))) stiefelTwoRotation y := by
  rw [isRegularValue_iff]
  rintro x rfl
  -- The second component is the rotation family of the sphere at `u`, which sends the points
  -- with `Im z = 0` to `±u`.
  have him : (x.2 : ℂ).im ≠ 0 := fun h0 ↦
    (sphereRotationFamily_eq_or_eq_neg_of_im_eq_zero (stiefelProj E 2 0 x.1)
      (x := (stiefelTwoSnd _ x.1 (coe_stiefelProj 0 x.1).symm, x.2)) h0).elim hy hy'
  rw [isRegularPoint_iff]
  exact (isInvertible_mfderiv_stiefelTwoRotation him).surjective

/-! ### Orientation signs -/

/-- The involution `((u, v), z) ↦ ((u, -v), conj z)` is smooth. -/
theorem contMDiff_stiefelTwoRotationInvolution {r : ℕ∞ω} :
    ContMDiff ((𝓢).prod (𝓡 1)) ((𝓢).prod (𝓡 1)) r (stiefelTwoRotationInvolution (E := E)) :=
  (contMDiff_stiefelTwoReflection.comp contMDiff_fst).prodMk
    (ContMDiff.codRestrict_sphere
      ((Complex.conjCLE : ℂ →L[ℝ] ℂ).contMDiff.comp (contMDiff_coe_sphere.comp contMDiff_snd))
      fun x ↦ (stiefelTwoRotationInvolution x).2.2)

/-- The orientation sign of the involution `((u, v), z) ↦ ((u, -v), conj z)` is `(-1)ᵐ`, that is
`(-1)ⁿ`: the frame reflection has sign `(-1)ᵐ⁺¹` and conjugation reverses `S¹`. -/
theorem orientationSign_stiefelTwoRotationInvolution
    (Ω : (Fin 2 → E) [⋀^Fin (2 * m + 1 + 1 + 1 + 1)]→L[ℝ] ℝ) (hΩ : Ω ≠ 0)
    (x : stiefel E 2 × sphere (0 : ℂ) 1) :
    orientationSign ((stiefelTwoOrientation Ω hΩ).prod Complex.orientation.sphereOrientation)
      ((stiefelTwoOrientation Ω hΩ).prod Complex.orientation.sphereOrientation)
      stiefelTwoRotationInvolution x = (-1) ^ m := by
  have hconj := Complex.isOrientationReversingAt_conj_sphere x.2
  rw [← isOrientationPreservingAt_neg_right] at hconj
  rcases Nat.even_or_odd m with hm | hm
  · have hK := isOrientationReversingAt_stiefelTwoReflection hm Ω hΩ x.1
    rw [← isOrientationPreservingAt_neg_right] at hK
    have h := hK.prodMap hconj
    rw [prod_neg_neg] at h
    exact (orientationSign_of_isOrientationPreservingAt h).trans hm.neg_one_pow.symm
  · have hK := isOrientationPreservingAt_stiefelTwoReflection hm Ω hΩ x.1
    have h := hK.prodMap hconj
    rw [prod_neg_right, isOrientationPreservingAt_neg_right] at h
    exact (orientationSign_of_isOrientationReversingAt h).trans hm.neg_one_pow.symm

/-! ### The degree -/

/-- **The degree of the Stiefel rotation map.** At every point `(u, q)` of `Sⁿ⁻¹ × Sⁿ⁻¹` with
`q ≠ ±u`, a regular value (`TauCeti.isRegularValue_stiefelTwoRotation`), the Stiefel rotation map
`T¹Sⁿ⁻¹ × S¹ → Sⁿ⁻¹ × Sⁿ⁻¹` has degree `±(1 + (-1)ⁿ)`, where `n = m + 2`, for the orientation
`TauCeti.stiefelTwoOrientation Ω` of `T¹Sⁿ⁻¹`, the standard orientation of `S¹`, and any orientation
of the target. The two preimages of `(u, q)` are exchanged by an involution of orientation sign
`(-1)ⁿ` that leaves the map unchanged, so they contribute `s` and `(-1)ⁿ s` with `s = ±1`. -/
theorem degreeAtRegularValue_stiefelTwoRotation
    (Ω : (Fin 2 → E) [⋀^Fin (2 * m + 1 + 1 + 1 + 1)]→L[ℝ] ℝ) (hΩ : Ω ≠ 0)
    (o : Manifold.Orientation ((𝓡 (m + 1)).prod (𝓡 (m + 1)))
      (sphere (0 : E) 1 × sphere (0 : E) 1) (Fin (2 * m + 1 + 1)))
    {y : sphere (0 : E) 1 × sphere (0 : E) 1} (hy : y.2 ≠ y.1) (hy' : y.2 ≠ -y.1) :
    ∃ s : ℤ, (s = 1 ∨ s = -1) ∧
      degreeAtRegularValue ((stiefelTwoOrientation Ω hΩ).prod Complex.orientation.sphereOrientation)
        o stiefelTwoRotation y = s * (1 + (-1) ^ m) := by
  classical
  set oD := (stiefelTwoOrientation Ω hΩ).prod Complex.orientation.sphereOrientation
  obtain ⟨x, hxim, rfl⟩ := exists_stiefelTwoRotation_eq hy hy'
  have hne : x ≠ (stiefelTwoRotationInvolution x) := fun h ↦ by
    have h' := congrArg (fun y : stiefel E 2 × sphere (0 : ℂ) 1 ↦ (y.2 : ℂ).im) h
    simp only [stiefelTwoRotationInvolution, Complex.conj_im] at h'
    linarith
  -- The orientation signs at the two preimages differ by the sign `(-1)ᵐ` of the involution.
  have hτ : MDifferentiableAt ((𝓢).prod (𝓡 1)) ((𝓡 (m + 1)).prod (𝓡 (m + 1)))
      (stiefelTwoRotation (E := E)) (stiefelTwoRotationInvolution x) :=
    ((contMDiff_stiefelTwoRotation (r := 1)) (stiefelTwoRotationInvolution x)).mdifferentiableAt
      one_ne_zero
  have hJ : MDifferentiableAt ((𝓢).prod (𝓡 1)) ((𝓢).prod (𝓡 1))
      (stiefelTwoRotationInvolution (E := E)) x :=
    ((contMDiff_stiefelTwoRotationInvolution (r := 1)) x).mdifferentiableAt one_ne_zero
  have hcomp := orientationSign_comp (o := oD) (o' := oD) (o'' := o) hτ hJ
  have hfun : stiefelTwoRotation ∘ stiefelTwoRotationInvolution = stiefelTwoRotation (E := E) :=
    funext stiefelTwoRotation_stiefelTwoRotationInvolution
  rw [hfun, orientationSign_stiefelTwoRotationInvolution] at hcomp
  set s := orientationSign oD o stiefelTwoRotation x
  have hs : s = 1 ∨ s = -1 := orientationSign_eq_one_or_eq_neg_one
    (isInvertible_mfderiv_stiefelTwoRotation hxim.ne')
  have hs' : orientationSign oD o stiefelTwoRotation (stiefelTwoRotationInvolution x) =
      (-1) ^ m * s := by
    have h2 : ((-1 : ℤ) ^ m) * (-1) ^ m = 1 := by rw [← mul_pow]; norm_num
    linear_combination (-(-1 : ℤ) ^ m) * hcomp -
      orientationSign oD o stiefelTwoRotation (stiefelTwoRotationInvolution x) * h2
  refine ⟨s, hs, ?_⟩
  rw [degreeAtRegularValue_eq_sum (s := {x, stiefelTwoRotationInvolution x}) fun y ↦ ?_,
    Finset.sum_pair hne, hs']
  · ring
  rw [Finset.mem_insert, Finset.mem_singleton, stiefelTwoRotation_eq_iff hxim.ne']

/-- For even `n = m + 2`, the Stiefel rotation map `T¹Sⁿ⁻¹ × S¹ → Sⁿ⁻¹ × Sⁿ⁻¹` has degree `±2` at
every point `(u, q)` with `q ≠ ±u`. -/
theorem abs_degreeAtRegularValue_stiefelTwoRotation_of_even (hm : Even m)
    (Ω : (Fin 2 → E) [⋀^Fin (2 * m + 1 + 1 + 1 + 1)]→L[ℝ] ℝ) (hΩ : Ω ≠ 0)
    (o : Manifold.Orientation ((𝓡 (m + 1)).prod (𝓡 (m + 1)))
      (sphere (0 : E) 1 × sphere (0 : E) 1) (Fin (2 * m + 1 + 1)))
    {y : sphere (0 : E) 1 × sphere (0 : E) 1} (hy : y.2 ≠ y.1) (hy' : y.2 ≠ -y.1) :
    |degreeAtRegularValue ((stiefelTwoOrientation Ω hΩ).prod Complex.orientation.sphereOrientation)
      o stiefelTwoRotation y| = 2 := by
  obtain ⟨s, hs, h⟩ := degreeAtRegularValue_stiefelTwoRotation Ω hΩ o hy hy'
  rw [h, hm.neg_one_pow]
  rcases hs with rfl | rfl <;> norm_num

/-- For odd `n = m + 2`, the Stiefel rotation map `T¹Sⁿ⁻¹ × S¹ → Sⁿ⁻¹ × Sⁿ⁻¹` has degree `0` at
every point `(u, q)` with `q ≠ ±u`. -/
theorem degreeAtRegularValue_stiefelTwoRotation_of_odd (hm : Odd m)
    (Ω : (Fin 2 → E) [⋀^Fin (2 * m + 1 + 1 + 1 + 1)]→L[ℝ] ℝ) (hΩ : Ω ≠ 0)
    (o : Manifold.Orientation ((𝓡 (m + 1)).prod (𝓡 (m + 1)))
      (sphere (0 : E) 1 × sphere (0 : E) 1) (Fin (2 * m + 1 + 1)))
    {y : sphere (0 : E) 1 × sphere (0 : E) 1} (hy : y.2 ≠ y.1) (hy' : y.2 ≠ -y.1) :
    degreeAtRegularValue ((stiefelTwoOrientation Ω hΩ).prod Complex.orientation.sphereOrientation)
      o stiefelTwoRotation y = 0 := by
  obtain ⟨s, -, h⟩ := degreeAtRegularValue_stiefelTwoRotation Ω hΩ o hy hy'
  rw [h, hm.neg_one_pow]
  ring

end TauCeti
