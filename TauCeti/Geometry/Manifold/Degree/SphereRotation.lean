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
import TauCeti.Analysis.Complex.Circle
import TauCeti.Analysis.InnerProductSpace.Projection.Basic
import TauCeti.Geometry.Manifold.MFDeriv.IsInvertible
import TauCeti.Geometry.Manifold.MFDeriv.Prod
import TauCeti.LinearAlgebra.Alternating.ConsCons

/-!
# The rotation family of a sphere and its degree

Let `E` be an oriented real inner product space of dimension `n + 1`, with unit sphere `Sⁿ`, and
fix `p ∈ Sⁿ`. The unit tangent vectors of `Sⁿ` at `p` are the unit vectors `v` of the hyperplane
`p^⊥ = (ℝ ∙ p)ᗮ`, the image of the tangent space at `p` in `E` (`range_mvfderiv_subtypeVal`), so
they form the unit sphere `Sⁿ⁻¹` of `p^⊥`. Rotating `p` towards `v` traces the great circle
`z ↦ Re z • p + Im z • v`. These circles assemble into the **rotation family**
(`TauCeti.sphereRotationFamily`)

`F : Sⁿ⁻¹ × S¹ → Sⁿ`, `F (v, z) = Re z • p + Im z • v`,

with `S¹` the unit circle of `ℂ`. Each point `q ≠ ±p` has exactly two preimages under `F`,
`(v₀, z₀)` and `(-v₀, conj z₀)`, which trace the same great circle through `p` and `q` in opposite
directions (`TauCeti.sphereRotationFamily_eq_sphereRotationFamily_iff`), while `F` collapses
`Sⁿ⁻¹ × {±1}` to `±p`.

We orient `Sⁿ` and `Sⁿ⁻¹ ⊆ p^⊥` by their outward normals (`Orientation.sphereOrientation`), the
hyperplane `p^⊥` with `p` as positive normal (`Orientation.orthogonalSpanSingleton`), `S¹` as the
unit circle of `ℂ`, and `Sⁿ⁻¹ × S¹` as a product with the first factor first. The derivative of `F`
is computed in `TauCeti.mvfderiv_coe_sphereRotationFamily_apply`. At a point with `Im z ≠ 0` it is
invertible (`TauCeti.isInvertible_mfderiv_sphereRotationFamily`), with orientation sign
`(-1)ⁿ⁻¹ · sign(Im z)ⁿ⁻¹` (`Orientation.orientationSign_sphereRotationFamily`). The two preimages of
`q ≠ ±p` have `Im z` of opposite signs, so every such `q` is a regular value
(`TauCeti.isRegularValue_sphereRotationFamily`) at which the degree of `F` is `1 + (-1)ⁿ⁻¹`
(`Orientation.degreeAtRegularValue_sphereRotationFamily`). For odd `n` the degree is `2`
(`Orientation.degreeAtRegularValue_sphereRotationFamily_of_even`), and for even `n` it is `0`.

Evaluated at `p`, the rotation of `Sⁿ` by the angle of `z` in the plane spanned by `p` and `v`
gives `F (v, z)`. So `F` is the evaluation at `p` of a family of rotations, and its degree two
in odd dimensions is the input to the direct proof that odd spheres are covered by
diffeomorphisms (Barraud–Damian–Humilière–Oancea, Proposition 6.34).

In the statements, `n = m + 1`, so that `Sⁿ⁻¹ = Sᵐ` is modelled on `ℝᵐ`.

## Main declarations

* `TauCeti.sphereRotationFamily`: the rotation family `(v, z) ↦ Re z • p + Im z • v`.
* `TauCeti.contMDiff_sphereRotationFamily`: it is smooth.
* `TauCeti.mvfderiv_coe_sphereRotationFamily_apply`: its derivative.
* `TauCeti.sphereRotationFamily_eq_sphereRotationFamily_iff`: the two preimages of a point
  `q ≠ ±p`.
* `TauCeti.isInvertible_mfderiv_sphereRotationFamily`: its derivative is invertible where
  `Im z ≠ 0`.
* `Orientation.orientationSign_sphereRotationFamily`: its orientation sign there.
* `TauCeti.isRegularValue_sphereRotationFamily`: every point other than `±p` is a regular value.
* `Orientation.degreeAtRegularValue_sphereRotationFamily`: the degree is `1 + (-1)ⁿ⁻¹` there.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4 (Proposition 6.34).
* J. W. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia, 1965,
  §5 (the degree as a signed count of preimages).
-/

public section

noncomputable section

open Metric Module Set TauCeti.Manifold.Orientation
open scoped Manifold ContDiff RealInnerProductSpace

namespace TauCeti

attribute [local instance] finrank_real_complex_fact'

/-! ### The rotation family -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {m : ℕ}
  [Fact (finrank ℝ E = m + 1 + 1)]

private theorem inner_coe_coe_sphere (p : sphere (0 : E) 1)
    (v : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1) : ⟪(p : E), ((v : (ℝ ∙ (p : E))ᗮ) : E)⟫ = 0 :=
  Submodule.mem_orthogonal_singleton_iff_inner_right.1 (v : (ℝ ∙ (p : E))ᗮ).2

/-- The **rotation family** at a point `p` of the unit sphere `Sⁿ` of `E`: a unit vector `v` of
`p^⊥`, that is a unit tangent vector of `Sⁿ` at `p`, and a point `z` of the unit circle of `ℂ` are
sent to `Re z • p + Im z • v`, the point reached by rotating `p` towards `v` by the angle of
`z`. -/
def sphereRotationFamily (p : sphere (0 : E) 1) :
    sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1 → sphere (0 : E) 1 := fun x ↦
  ⟨(x.2 : ℂ).re • (p : E) + (x.2 : ℂ).im • ((x.1 : (ℝ ∙ (p : E))ᗮ) : E), by
    -- `p` and `v` are orthonormal, and `Re z ^ 2 + Im z ^ 2 = ‖z‖ ^ 2 = 1`.
    rw [mem_sphere_zero_iff_norm, ← pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero]
    have hv : ‖((x.1 : (ℝ ∙ (p : E))ᗮ) : E)‖ = 1 := norm_eq_of_mem_sphere x.1
    simp [norm_add_sq_real, norm_smul, real_inner_smul_left, real_inner_smul_right,
      inner_coe_coe_sphere, norm_eq_of_mem_sphere p, hv]
    linarith [Complex.re_sq_add_im_sq_of_mem_sphere x.2.2]⟩

@[simp]
theorem coe_sphereRotationFamily (p : sphere (0 : E) 1)
    (x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1) :
    (sphereRotationFamily p x : E) =
      (x.2 : ℂ).re • (p : E) + (x.2 : ℂ).im • ((x.1 : (ℝ ∙ (p : E))ᗮ) : E) :=
  (rfl)

/-- The rotation family is smooth. -/
theorem contMDiff_sphereRotationFamily (p : sphere (0 : E) 1) :
    ContMDiff ((𝓡 m).prod (𝓡 1)) (𝓡 (m + 1)) ∞ (sphereRotationFamily p) := by
  have hv : ContMDiff ((𝓡 m).prod (𝓡 1)) 𝓘(ℝ, E) ∞
      fun x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1 ↦
        ((x.1 : (ℝ ∙ (p : E))ᗮ) : E) :=
    ((ℝ ∙ (p : E))ᗮ.subtypeL.contDiff.contMDiff.comp contMDiff_coe_sphere).comp contMDiff_fst
  have hz : ContMDiff ((𝓡 m).prod (𝓡 1)) 𝓘(ℝ, ℂ) ∞
      fun x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1 ↦ (x.2 : ℂ) :=
    contMDiff_coe_sphere.comp contMDiff_snd
  exact ContMDiff.codRestrict_sphere
    (((Complex.reCLM.contDiff.contMDiff.comp hz).smul contMDiff_const).add
      ((Complex.imCLM.contDiff.contMDiff.comp hz).smul hv))
    fun x ↦ (sphereRotationFamily p x).2

/-- The derivative of the inclusion `Sᵐ ⊆ p^⊥ ⊆ E`, read in `E`, is the derivative of the
inclusion into `p^⊥` followed by the inclusion of `p^⊥`. -/
private theorem mvfderiv_coe_coe_sphere_apply (p : sphere (0 : E) 1)
    (v : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1) (a : TangentSpace (𝓡 m) v) :
    mvfderiv (𝓡 m) (fun v : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 ↦ ((v : (ℝ ∙ (p : E))ᗮ) : E)) v a =
      ((mvfderiv (𝓡 m) ((↑) : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 → (ℝ ∙ (p : E))ᗮ) v a :
        (ℝ ∙ (p : E))ᗮ) : E) := by
  have hι := (contMDiff_coe_sphere (E := (ℝ ∙ (p : E))ᗮ) (n := m) (m := 1) v).mdifferentiableAt
    one_ne_zero
  have h := mvfderiv_comp_apply (g := Submodule.subtypeL (ℝ ∙ (p : E))ᗮ) v
    (Submodule.subtypeL (ℝ ∙ (p : E))ᗮ).mdifferentiableAt hι a
  rw [mvfderiv_eq_fderiv, ContinuousLinearMap.fderiv] at h
  -- `mvfderiv` of the inclusion into `p^⊥` is its `mfderiv`, and the identification of the tangent
  -- spaces of `p^⊥` with `p^⊥` is the identity.
  exact h

/-- The derivative of a real-linear function of the circle coordinate, read on the product. -/
private theorem mvfderiv_clm_coe_snd_apply (p : sphere (0 : E) 1) (L : ℂ →L[ℝ] ℝ)
    (x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1)
    (w : TangentSpace ((𝓡 m).prod (𝓡 1)) x) :
    mvfderiv ((𝓡 m).prod (𝓡 1))
        (fun y : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1 ↦ L (y.2 : ℂ)) x w =
      L (mvfderiv (𝓡 1) ((↑) : sphere (0 : ℂ) 1 → ℂ) x.2
        (Manifold.tangentSpaceProdEquiv x w).2) := by
  have hκ := (contMDiff_coe_sphere (E := ℂ) (n := 1) (m := 1) x.2).mdifferentiableAt one_ne_zero
  have h := mvfderiv_comp_apply (g := L) x.2 L.mdifferentiableAt hκ
    (Manifold.tangentSpaceProdEquiv x w).2
  rw [mvfderiv_eq_fderiv, ContinuousLinearMap.fderiv] at h
  -- `mvfderiv_comp_snd_apply` rewrites the derivative of a composition `g ∘ Prod.snd`, so the
  -- map, a lambda, is first written definitionally in that form.
  rw [show (fun y : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1 ↦ L (y.2 : ℂ)) =
    (L ∘ ((↑) : sphere (0 : ℂ) 1 → ℂ)) ∘ Prod.snd from rfl, mvfderiv_comp_snd_apply,
    Manifold.tangentSpaceProdEquiv_apply]
  rw [Manifold.tangentSpaceProdEquiv_apply] at h
  -- As above, `mvfderiv` of the inclusion of the circle is its `mfderiv`.
  exact h

/-- **The derivative of the rotation family.** Read in `E`, a tangent vector `(a, b)` at `(v, z)`
is sent to `Re b • p + Im b • v + Im z • a`, where `a` and `b` are read in `p^⊥` and in `ℂ` through
the derivatives of the inclusions. -/
theorem mvfderiv_coe_sphereRotationFamily_apply (p : sphere (0 : E) 1)
    (x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1)
    (w : TangentSpace ((𝓡 m).prod (𝓡 1)) x) :
    mvfderiv ((𝓡 m).prod (𝓡 1)) (fun y ↦ (sphereRotationFamily p y : E)) x w =
      (mvfderiv (𝓡 1) ((↑) : sphere (0 : ℂ) 1 → ℂ) x.2
          (Manifold.tangentSpaceProdEquiv x w).2).re • (p : E) +
        (mvfderiv (𝓡 1) ((↑) : sphere (0 : ℂ) 1 → ℂ) x.2
          (Manifold.tangentSpaceProdEquiv x w).2).im • ((x.1 : (ℝ ∙ (p : E))ᗮ) : E) +
        (x.2 : ℂ).im • ((mvfderiv (𝓡 m) ((↑) : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 → (ℝ ∙ (p : E))ᗮ)
          x.1 (Manifold.tangentSpaceProdEquiv x w).1 : (ℝ ∙ (p : E))ᗮ) : E) := by
  have hι := (contMDiff_coe_sphere (E := (ℝ ∙ (p : E))ᗮ) (n := m) (m := 1) x.1).mdifferentiableAt
    one_ne_zero
  have hκ := (contMDiff_coe_sphere (E := ℂ) (n := 1) (m := 1) x.2).mdifferentiableAt one_ne_zero
  have hv : MDifferentiableAt ((𝓡 m).prod (𝓡 1)) 𝓘(ℝ, E)
      (fun y : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1 ↦
        ((y.1 : (ℝ ∙ (p : E))ᗮ) : E)) x :=
    ((Submodule.subtypeL (ℝ ∙ (p : E))ᗮ).mdifferentiableAt.comp x.1 hι).comp x
      mdifferentiableAt_fst
  have hre : MDifferentiableAt ((𝓡 m).prod (𝓡 1)) 𝓘(ℝ)
      (fun y : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1 ↦ Complex.reCLM (y.2 : ℂ)) x :=
    (Complex.reCLM.mdifferentiableAt.comp x.2 hκ).comp x
      mdifferentiableAt_snd
  have him : MDifferentiableAt ((𝓡 m).prod (𝓡 1)) 𝓘(ℝ)
      (fun y : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1 ↦ Complex.imCLM (y.2 : ℂ)) x :=
    (Complex.imCLM.mdifferentiableAt.comp x.2 hκ).comp x
      mdifferentiableAt_snd
  have hv' : mvfderiv ((𝓡 m).prod (𝓡 1))
      (fun y : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1 ↦
        ((y.1 : (ℝ ∙ (p : E))ᗮ) : E)) x w =
      ((mvfderiv (𝓡 m) ((↑) : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 → (ℝ ∙ (p : E))ᗮ) x.1
        (Manifold.tangentSpaceProdEquiv x w).1 : (ℝ ∙ (p : E))ᗮ) : E) := by
    rw [← mvfderiv_coe_coe_sphere_apply, Manifold.tangentSpaceProdEquiv_apply]
    exact mvfderiv_comp_fst_apply
      (fun v : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 ↦ ((v : (ℝ ∙ (p : E))ᗮ) : E)) x w
  -- Write the map as a sum of products of scalar and vector-valued functions.
  rw [show (fun y ↦ (sphereRotationFamily p y : E)) =
    ((fun y : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1 ↦ Complex.reCLM (y.2 : ℂ)) •
        fun _ ↦ (p : E)) +
      (fun y : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1 ↦ Complex.imCLM (y.2 : ℂ)) •
        fun y ↦ ((y.1 : (ℝ ∙ (p : E))ᗮ) : E) from rfl,
    mvfderiv_add (hre.smul mdifferentiableAt_const) (him.smul hv),
    mvfderiv_smul hre mdifferentiableAt_const, mvfderiv_smul him hv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply]
  rw [mvfderiv_clm_coe_snd_apply p Complex.reCLM x w,
    mvfderiv_clm_coe_snd_apply p Complex.imCLM x w,
    hv', mvfderiv_const]
  simp only [zero_apply, smul_zero, zero_add, Complex.reCLM_apply, Complex.imCLM_apply]
  abel

/-! ### Fibres -/

/-- Two points of the domain, one of them off `Sᵐ × {±1}`, have the same image exactly when they
are equal or exchanged by the involution `(v, z) ↦ (-v, conj z)`. -/
theorem sphereRotationFamily_eq_sphereRotationFamily_iff (p : sphere (0 : E) 1)
    {x y : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1} (hx : (x.2 : ℂ).im ≠ 0) :
    sphereRotationFamily p y = sphereRotationFamily p x ↔
      y = x ∨ (((y.1 : (ℝ ∙ (p : E))ᗮ) : E) = -((x.1 : (ℝ ∙ (p : E))ᗮ) : E) ∧
        (y.2 : ℂ) = (starRingEnd ℂ) (x.2 : ℂ)) := by
  constructor
  · intro h
    have hE := congrArg Subtype.val h
    simp only [coe_sphereRotationFamily] at hE
    -- Pairing with `p` recovers the real parts.
    have hre : (y.2 : ℂ).re = (x.2 : ℂ).re := by
      have h' := congrArg (fun w ↦ ⟪(p : E), w⟫) hE
      simpa only [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
        norm_eq_of_mem_sphere p, inner_coe_coe_sphere, mul_zero, add_zero, one_pow,
        mul_one] using h'
    have him : (y.2 : ℂ).im • ((y.1 : (ℝ ∙ (p : E))ᗮ) : E) =
        (x.2 : ℂ).im • ((x.1 : (ℝ ∙ (p : E))ᗮ) : E) := by
      rw [hre] at hE
      exact add_left_cancel hE
    have hsq : (y.2 : ℂ).im ^ 2 = (x.2 : ℂ).im ^ 2 := by
      linarith [congrArg (· ^ 2) hre, Complex.re_sq_add_im_sq_of_mem_sphere y.2.2,
        Complex.re_sq_add_im_sq_of_mem_sphere x.2.2]
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with him' | him'
    · left
      rw [him'] at him
      refine Prod.ext (Subtype.ext (Subtype.ext (smul_right_injective E hx him)))
        (Subtype.ext (Complex.ext hre him'))
    · right
      rw [him', neg_smul, ← smul_neg] at him
      exact ⟨neg_eq_iff_eq_neg.1 (smul_right_injective E hx him),
        Complex.ext (by simpa using hre) (by simpa using him')⟩
  · rintro (rfl | ⟨hv, hz⟩)
    · rfl
    · refine Subtype.ext ?_
      simp only [coe_sphereRotationFamily, hv, hz, Complex.conj_re, Complex.conj_im, neg_smul,
        smul_neg, neg_neg]

/-- A point with `Im z = 0` is sent to `p` or to `-p`. -/
private theorem sphereRotationFamily_eq_or_eq_neg_of_im_eq_zero (p : sphere (0 : E) 1)
    {x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1} (hx : (x.2 : ℂ).im = 0) :
    sphereRotationFamily p x = p ∨ sphereRotationFamily p x = -p := by
  have hre : (x.2 : ℂ).re ^ 2 = 1 ^ 2 := by
    linarith [sq_eq_zero_iff.2 hx, Complex.re_sq_add_im_sq_of_mem_sphere x.2.2]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hre with h | h
  · exact .inl (Subtype.ext (by simp [h, hx]))
  · exact .inr (Subtype.ext (by simp [h, hx]))

/-- Every point of the sphere other than `±p` is the image of a point with `Im z > 0`. -/
theorem exists_sphereRotationFamily_eq (p : sphere (0 : E) 1) {q : sphere (0 : E) 1}
    (hqp : q ≠ p) (hqp' : q ≠ -p) :
    ∃ x, 0 < (x.2 : ℂ).im ∧ sphereRotationFamily p x = q := by
  -- Split `q = c • p + r` with `r` orthogonal to `p`, and normalize `r`.
  set c : ℝ := ⟪(q : E), (p : E)⟫ with hc
  set r : E := (q : E) - c • (p : E) with hr
  have hp := norm_eq_of_mem_sphere p
  have hpr : ⟪(p : E), r⟫ = 0 := by
    rw [hr, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hp, hc,
      real_inner_comm]
    ring
  have hr0 : r ≠ 0 := by
    intro h0
    have hq : (q : E) = c • (p : E) := by rw [← sub_eq_zero, ← hr, h0]
    have hc1 : |c| = 1 := by
      rw [← norm_eq_of_mem_sphere q, hq, norm_smul, hp, mul_one, Real.norm_eq_abs]
    rcases abs_eq (zero_le_one' ℝ) |>.1 hc1 with h | h
    · exact hqp (Subtype.ext (by rw [hq, h, one_smul]))
    · exact hqp' (Subtype.ext (by rw [hq, h, coe_neg_sphere, neg_one_smul]))
  have hs : 0 < ‖r‖ := norm_pos_iff.2 hr0
  have hq' : c • (p : E) + r = q := by rw [hr]; abel
  have hcs : c ^ 2 + ‖r‖ ^ 2 = 1 := by
    have h := @norm_add_sq_real E _ _ (c • (p : E)) r
    rw [hq', norm_eq_of_mem_sphere q, norm_smul, real_inner_smul_left, hpr, hp,
      Real.norm_eq_abs, mul_one, sq_abs] at h
    linarith
  have hv : ‖‖r‖⁻¹ • r‖ = 1 := by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hs.ne']
  -- The norm of an element of `p^⊥` is its norm in `E`.
  let v : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 :=
    ⟨⟨‖r‖⁻¹ • r, Submodule.smul_mem _ _ (Submodule.mem_orthogonal_singleton_iff_inner_right.2 hpr)⟩,
      mem_sphere_zero_iff_norm.2 hv⟩
  let z : sphere (0 : ℂ) 1 := ⟨⟨c, ‖r‖⟩, by
    rw [mem_sphere_zero_iff_norm, ← pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero,
      Complex.sq_norm, Complex.normSq_mk]
    linarith⟩
  have hzre : (z : ℂ).re = c := rfl
  have hzim : (z : ℂ).im = ‖r‖ := rfl
  have hv' : ((v : (ℝ ∙ (p : E))ᗮ) : E) = ‖r‖⁻¹ • r := rfl
  refine ⟨(v, z), hs, Subtype.ext ?_⟩
  rw [coe_sphereRotationFamily, ← hq', hzre, hzim, hv', smul_smul, mul_inv_cancel₀ hs.ne',
    one_smul]

/-! ### Orientation signs -/

/-- The derivative of the rotation family followed by that of the inclusion of `Sᵐ⁺¹` is the
derivative of the family read in `E`. -/
private theorem mvfderiv_coe_mfderiv_sphereRotationFamily_apply (p : sphere (0 : E) 1)
    (x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1)
    (w : TangentSpace ((𝓡 m).prod (𝓡 1)) x) :
    mvfderiv (𝓡 (m + 1)) ((↑) : sphere (0 : E) 1 → E) (sphereRotationFamily p x)
        (mfderiv ((𝓡 m).prod (𝓡 1)) (𝓡 (m + 1)) (sphereRotationFamily p) x w) =
      mvfderiv ((𝓡 m).prod (𝓡 1)) (fun y ↦ (sphereRotationFamily p y : E)) x w :=
  (mvfderiv_comp_apply x
    ((contMDiff_coe_sphere (E := E) (n := m + 1) (m := 1) _).mdifferentiableAt one_ne_zero)
    ((contMDiff_sphereRotationFamily p x).mdifferentiableAt (by simp)) w).symm

/-- A tangent basis `b` of the unit sphere of `p^⊥` at `v` is positive for the outward-normal
orientation exactly when `p, v, b₁, …, bₘ`, read in `E`, has positive volume, and this volume does
not vanish. -/
private theorem volumeForm_cons_cons_mvfderiv (o : Orientation ℝ E (Fin (m + 1 + 1)))
    (p : sphere (0 : E) 1) (v : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1)
    (b : Basis (Fin m) ℝ (TangentSpace (𝓡 m) v)) :
    o.volumeForm (Fin.cons (p : E) (Fin.cons ((v : (ℝ ∙ (p : E))ᗮ) : E) fun j ↦
        ((mvfderiv (𝓡 m) ((↑) : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 → (ℝ ∙ (p : E))ᗮ) v (b j) :
          (ℝ ∙ (p : E))ᗮ) : E))) ≠ 0 ∧
      (b.orientation = (o.orthogonalSpanSingleton
          (ne_zero_of_mem_unit_sphere p)).sphereOrientation.orientationAt v ↔
        0 < o.volumeForm (Fin.cons (p : E) (Fin.cons ((v : (ℝ ∙ (p : E))ᗮ) : E) fun j ↦
          ((mvfderiv (𝓡 m) ((↑) : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 → (ℝ ∙ (p : E))ᗮ) v (b j) :
            (ℝ ∙ (p : E))ᗮ) : E)))) := by
  -- `v` followed by the image of `b` is a basis `W` of `p^⊥`, oriented like `b`.
  have hli := LinearIndependent.finCons_mvfderiv_coe_sphere v b.linearIndependent
  let W := basisOfLinearIndependentOfCardEqFinrank hli (by
    rw [Fintype.card_fin]
    exact (Fact.out : finrank ℝ (ℝ ∙ (p : E))ᗮ = m + 1).symm)
  have hW : (fun i ↦ (W i : E)) = Fin.cons ((v : (ℝ ∙ (p : E))ᗮ) : E) fun j ↦
      ((mvfderiv (𝓡 m) ((↑) : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 → (ℝ ∙ (p : E))ᗮ) v (b j) :
        (ℝ ∙ (p : E))ᗮ) : E) := by
    ext i
    -- Both sides are `Fin.cons` of the same entries, the coercion taken inside or outside.
    refine Fin.cases ?_ (fun j ↦ ?_) i <;>
      simp only [W, coe_basisOfLinearIndependentOfCardEqFinrank] <;> rfl
  refine ⟨?_, ?_⟩
  · rw [← hW]
    -- Only the linear independence of `W` is used here; clearing its construction keeps
    -- unification from unfolding it.
    clear_value W
    exact Orientation.volumeForm_apply_ne_zero_iff.2
      (LinearIndependent.finCons_orthogonal_span_singleton (ne_zero_of_mem_unit_sphere p)
        (W.linearIndependent.map' _ (Submodule.ker_subtype _)) fun i ↦ (W i).2)
  · rw [Orientation.orientation_eq_orientationAt_sphereOrientation_iff,
      show (Fin.cons ((v : (ℝ ∙ (p : E))ᗮ)) fun i ↦ mvfderiv (𝓡 m)
        ((↑) : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 → (ℝ ∙ (p : E))ᗮ) v (b i)) = ⇑W by simp [W],
      Orientation.volumeForm_apply_pos_iff, Orientation.orientation_eq_orthogonalSpanSingleton_iff,
      hW]

/-- The volume of the image under the derivative of the rotation family of the basis
`(Im z • a, β)` of a point with circle coordinate `z`: moving the last vector to the second place
costs the sign `(-1)ᵐ` of a cycle, scaling `m` vectors by `Im z` costs `(Im z)ᵐ`, and the first two
vectors span the plane of `p` and `v` with the factor `Re z Im β - Im z Re β`
(`AlternatingMap.map_cons_snoc_add_smul`). -/
private theorem volumeForm_cons_snoc (o : Orientation ℝ E (Fin (m + 1 + 1))) (p v : E)
    (a : Fin m → E) (z β : ℂ) :
    o.volumeForm (Fin.cons (z.re • p + z.im • v)
        (Fin.snoc (fun j ↦ z.im • a j) (β.re • p + β.im • v))) =
      (-1) ^ m * z.im ^ m * (z.re * β.im - z.im * β.re) *
        o.volumeForm (Fin.cons p (Fin.cons v a)) := by
  -- Scaling the last `m` vectors by `Im z` multiplies the volume by `(Im z)ᵐ`.
  have hs := o.volumeForm.map_smul_univ (Fin.cons 1 (Fin.cons 1 fun _ ↦ z.im))
    (Fin.cons p (Fin.cons v a))
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ] at hs
  simp only [Fin.cons_zero, Fin.cons_succ, one_mul, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul] at hs
  have hcons : (fun i ↦ (Fin.cons 1 (Fin.cons 1 fun _ ↦ z.im) : Fin (m + 1 + 1) → ℝ) i •
      (Fin.cons p (Fin.cons v a) : Fin (m + 1 + 1) → E) i) =
      Fin.cons p (Fin.cons v fun j ↦ z.im • a j) := by
    ext i
    refine Fin.cases ?_ (fun i ↦ Fin.cases ?_ (fun j ↦ ?_) i) i <;> simp
  rw [hcons] at hs
  rw [AlternatingMap.map_cons_snoc_add_smul, hs, smul_eq_mul]
  ring

/-- A tangent basis of the unit sphere `Sᵐ` of `p^⊥` at `v`, positively or negatively oriented
(when `m = 0` it is empty). -/
private def sphereTangentBasis {p : sphere (0 : E) 1} (v : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1) :
    Basis (Fin m) ℝ (TangentSpace (𝓡 m) v) :=
  finBasisOfFinrankEq ℝ (TangentSpace (𝓡 m) v) (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := m))

/-- A positively oriented tangent basis of the unit circle of `ℂ` at `z`. -/
private def circleTangentBasis (z : sphere (0 : ℂ) 1) : Basis (Fin 1) ℝ (TangentSpace (𝓡 1) z) :=
  (finBasisOfFinrankEq ℝ (TangentSpace (𝓡 1) z)
    ((Complex.orientation.sphereOrientation.finrank_tangentSpace_eq z).trans
      (Fintype.card_fin 1))).adjustToOrientation
      (Complex.orientation.sphereOrientation.orientationAt z)

private theorem orientation_circleTangentBasis (z : sphere (0 : ℂ) 1) :
    (circleTangentBasis z).orientation = Complex.orientation.sphereOrientation.orientationAt z :=
  Basis.orientation_adjustToOrientation _ _

/-- The product of tangent bases `b` of `Sᵐ` at `v` and `c` of `S¹` at `z`, with `b` first, as a
basis of the tangent space of `Sᵐ × S¹` at `(v, z)`. -/
private def prodTangentBasis {p : sphere (0 : E) 1}
    {x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1}
    (b : Basis (Fin m) ℝ (TangentSpace (𝓡 m) x.1)) (c : Basis (Fin 1) ℝ (TangentSpace (𝓡 1) x.2)) :
    Basis (Fin (m + 1)) ℝ (TangentSpace ((𝓡 m).prod (𝓡 1)) x) :=
  (b.prod c).reindex finSumFinEquiv

/-- The derivative of the rotation family at `x = (v, z)`, read in `E`, carries the product basis
of a tangent basis `b` at `v` and a tangent basis `c` at `z` to `Im z • a₁, …, Im z • aₘ, β`, where
`a` and `β` are `b` and `c` read in `p^⊥` and in `ℂ`. So the volume of `F x` followed by this image
is that of `p, v, a₁, …, aₘ` times `(-1)ᵐ (Im z)ᵐ (Re z Im β - Im z Re β)`. -/
private theorem volumeForm_cons_mfderiv_sphereRotationFamily
    (o : Orientation ℝ E (Fin (m + 1 + 1))) (p : sphere (0 : E) 1)
    (x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1)
    (b : Basis (Fin m) ℝ (TangentSpace (𝓡 m) x.1)) (c : Basis (Fin 1) ℝ (TangentSpace (𝓡 1) x.2)) :
    o.volumeForm (Fin.cons (sphereRotationFamily p x : E) fun i ↦
      mvfderiv (𝓡 (m + 1)) ((↑) : sphere (0 : E) 1 → E) (sphereRotationFamily p x)
        (mfderiv ((𝓡 m).prod (𝓡 1)) (𝓡 (m + 1)) (sphereRotationFamily p) x
          (prodTangentBasis b c i))) =
      (-1) ^ m * (x.2 : ℂ).im ^ m *
        ((x.2 : ℂ).re * (mvfderiv (𝓡 1) ((↑) : sphere (0 : ℂ) 1 → ℂ) x.2 (c 0)).im -
          (x.2 : ℂ).im * (mvfderiv (𝓡 1) ((↑) : sphere (0 : ℂ) 1 → ℂ) x.2 (c 0)).re) *
        o.volumeForm (Fin.cons (p : E) (Fin.cons ((x.1 : (ℝ ∙ (p : E))ᗮ) : E) fun j ↦
          ((mvfderiv (𝓡 m) ((↑) : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 → (ℝ ∙ (p : E))ᗮ) x.1 (b j) :
            (ℝ ∙ (p : E))ᗮ) : E))) := by
  set v : E := ((x.1 : (ℝ ∙ (p : E))ᗮ) : E)
  set a : Fin m → E := fun j ↦ ((mvfderiv (𝓡 m)
    ((↑) : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 → (ℝ ∙ (p : E))ᗮ) x.1 (b j) : (ℝ ∙ (p : E))ᗮ) : E)
  set β : ℂ := mvfderiv (𝓡 1) ((↑) : sphere (0 : ℂ) 1 → ℂ) x.2 (c 0)
  have himage : (fun i ↦ mvfderiv (𝓡 (m + 1)) ((↑) : sphere (0 : E) 1 → E)
      (sphereRotationFamily p x)
        (mfderiv ((𝓡 m).prod (𝓡 1)) (𝓡 (m + 1)) (sphereRotationFamily p) x
          (prodTangentBasis b c i))) =
      Fin.snoc (fun j ↦ (x.2 : ℂ).im • a j) (β.re • (p : E) + β.im • v) := by
    have hBi (i : Fin (m + 1)) :
        Manifold.tangentSpaceProdEquiv x (prodTangentBasis b c i) =
          (b.prod c) (finSumFinEquiv.symm i) := by
      rw [Manifold.tangentSpaceProdEquiv_apply]
      exact Basis.reindex_apply _ _ _
    funext i
    rw [mvfderiv_coe_mfderiv_sphereRotationFamily_apply, mvfderiv_coe_sphereRotationFamily_apply,
      hBi]
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simp [β, v, ContinuousLinearMap.map_zero]
    · simp [a, ContinuousLinearMap.map_zero]
  rw [himage, coe_sphereRotationFamily]
  exact volumeForm_cons_snoc o p v a x.2 β

/-- At a point `(v, z)` with `Im z ≠ 0`, the derivative of the rotation family carries the product
basis of a tangent basis `b` at `v` and a positively oriented tangent basis `c` at `z` to a linearly
independent family: the volume computed in `volumeForm_cons_mfderiv_sphereRotationFamily` does not
vanish. -/
private theorem linearIndependent_mfderiv_sphereRotationFamily
    (o : Orientation ℝ E (Fin (m + 1 + 1))) (p : sphere (0 : E) 1)
    {x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1} (hx : (x.2 : ℂ).im ≠ 0)
    (b : Basis (Fin m) ℝ (TangentSpace (𝓡 m) x.1)) {c : Basis (Fin 1) ℝ (TangentSpace (𝓡 1) x.2)}
    (hc : c.orientation = Complex.orientation.sphereOrientation.orientationAt x.2) :
    LinearIndependent ℝ fun i ↦ mfderiv ((𝓡 m).prod (𝓡 1)) (𝓡 (m + 1)) (sphereRotationFamily p) x
      (prodTangentBasis b c i) := by
  have hκ0 : (-1 : ℝ) ^ m * (x.2 : ℂ).im ^ m ≠ 0 := by simp [hx]
  have hvol := volumeForm_cons_mfderiv_sphereRotationFamily o p x b c
  have h := Orientation.volumeForm_apply_ne_zero_iff.1 (by
    rw [hvol]
    exact mul_ne_zero (mul_ne_zero hκ0
      ((Complex.orientation_eq_orientationAt_sphereOrientation_iff c).1 hc).ne')
      (volumeForm_cons_cons_mvfderiv o p x.1 b).1)
  exact LinearIndependent.of_comp (mvfderiv (𝓡 (m + 1)) ((↑) : sphere (0 : E) 1 → E)
    (sphereRotationFamily p x)).toLinearMap (linearIndependent_finCons.1 h).1

/-- At a point `(v, z)` with `Im z ≠ 0`, the derivative of the rotation family carries the product
basis of a tangent basis `b` at `v` and a positively oriented tangent basis `c` at `z` onto a basis
of the tangent space of the target. -/
private theorem exists_basis_eq_mfderiv_sphereRotationFamily
    (o : Orientation ℝ E (Fin (m + 1 + 1))) (p : sphere (0 : E) 1)
    {x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1} (hx : (x.2 : ℂ).im ≠ 0)
    (b : Basis (Fin m) ℝ (TangentSpace (𝓡 m) x.1)) {c : Basis (Fin 1) ℝ (TangentSpace (𝓡 1) x.2)}
    (hc : c.orientation = Complex.orientation.sphereOrientation.orientationAt x.2) :
    ∃ b' : Basis (Fin (m + 1)) ℝ (TangentSpace (𝓡 (m + 1)) (sphereRotationFamily p x)),
      ∀ i, mfderiv ((𝓡 m).prod (𝓡 1)) (𝓡 (m + 1)) (sphereRotationFamily p) x
        (prodTangentBasis b c i) = b' i :=
  ⟨basisOfLinearIndependentOfCardEqFinrank
    (linearIndependent_mfderiv_sphereRotationFamily o p hx b hc)
    ((Fintype.card_fin _).trans (finrank_euclideanSpace_fin (𝕜 := ℝ)).symm), fun i ↦ by simp⟩

/-- At a point with `Im z ≠ 0`, the derivative of the rotation family is invertible. -/
theorem isInvertible_mfderiv_sphereRotationFamily (p : sphere (0 : E) 1)
    {x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1} (hx : (x.2 : ℂ).im ≠ 0) :
    (mfderiv ((𝓡 m).prod (𝓡 1)) (𝓡 (m + 1)) (sphereRotationFamily p) x).IsInvertible := by
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ (m + 1)
  -- The volume form of any orientation of `E` detects that the image of the product basis is a
  -- basis of the tangent space of the target.
  obtain ⟨b', hb'⟩ := exists_basis_eq_mfderiv_sphereRotationFamily
    (finBasisOfFinrankEq ℝ E (Fact.out : finrank ℝ E = m + 1 + 1)).orientation p hx
    (sphereTangentBasis x.1) (orientation_circleTangentBasis x.2)
  exact isInvertible_mfderiv_of_basis _ b' hb'

/-- At a point `(v, z)` with `Im z ≠ 0`, the orientation sign of the rotation family is the sign
of `(-1)ᵐ (Im z)ᵐ`. -/
theorem _root_.Orientation.orientationSign_sphereRotationFamily
    (o : Orientation ℝ E (Fin (m + 1 + 1))) (p : sphere (0 : E) 1)
    {x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1} (hx : (x.2 : ℂ).im ≠ 0) :
    orientationSign
      ((o.orthogonalSpanSingleton (ne_zero_of_mem_unit_sphere p)).sphereOrientation.prod
        Complex.orientation.sphereOrientation) o.sphereOrientation
      (sphereRotationFamily p) x = SignType.sign ((-1) ^ m * (x.2 : ℂ).im ^ m) := by
  set op := o.orthogonalSpanSingleton (ne_zero_of_mem_unit_sphere p)
  -- A basis of the tangent space of the first factor, which may be positively or negatively
  -- oriented, a positively oriented one of the second factor, and their product, which the
  -- derivative carries to a basis `b'` of the target.
  set b := sphereTangentBasis (p := p) (m := m) x.1
  set c := circleTangentBasis x.2
  have hc := orientation_circleTangentBasis x.2
  have hB : (prodTangentBasis b c).orientation =
      (op.sphereOrientation.prod Complex.orientation.sphereOrientation).orientationAt x ↔
      b.orientation = op.sphereOrientation.orientationAt x.1 :=
    (op.sphereOrientation.orientation_eq_orientationAt_prod_iff _ b c).trans (iff_true_right hc)
  have h₁ := (volumeForm_cons_cons_mvfderiv o p x.1 b).2
  have h₂ := (Complex.orientation_eq_orientationAt_sphereOrientation_iff c).1 hc
  obtain ⟨b', hb'⟩ := exists_basis_eq_mfderiv_sphereRotationFamily o p hx b hc
  rcases lt_trichotomy ((-1 : ℝ) ^ m * (x.2 : ℂ).im ^ m) 0 with hκ | hκ | hκ
  · rw [sign_neg hκ, SignType.coe_neg_one]
    refine orientationSign_of_isOrientationReversingAt ?_
    rw [isOrientationReversingAt_iff_of_basis (prodTangentBasis b c) b' hb', hB, h₁,
      Orientation.orientation_eq_neg_orientationAt_sphereOrientation_iff]
    simp only [← hb', volumeForm_cons_mfderiv_sphereRotationFamily]
    have hκw := mul_neg_of_neg_of_pos hκ h₂
    exact ⟨fun hD ↦ mul_neg_of_neg_of_pos hκw hD, fun h ↦ pos_of_mul_neg_right h hκw.le⟩
  · simp [hx] at hκ
  · rw [sign_pos hκ, SignType.coe_one]
    refine orientationSign_of_isOrientationPreservingAt ?_
    rw [isOrientationPreservingAt_iff_of_basis (prodTangentBasis b c) b' hb', hB, h₁,
      Orientation.orientation_eq_orientationAt_sphereOrientation_iff]
    simp only [← hb', volumeForm_cons_mfderiv_sphereRotationFamily]
    exact (mul_pos_iff_of_pos_left (mul_pos hκ h₂)).symm

/-- At a point with `Im z > 0`, the orientation sign of the rotation family is `(-1)ᵐ`. -/
theorem _root_.Orientation.orientationSign_sphereRotationFamily_of_im_pos
    (o : Orientation ℝ E (Fin (m + 1 + 1)))
    (p : sphere (0 : E) 1) {x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1}
    (hx : 0 < (x.2 : ℂ).im) :
    orientationSign
      ((o.orthogonalSpanSingleton (ne_zero_of_mem_unit_sphere p)).sphereOrientation.prod
        Complex.orientation.sphereOrientation) o.sphereOrientation
      (sphereRotationFamily p) x = (-1) ^ m := by
  rw [o.orientationSign_sphereRotationFamily p hx.ne', sign_mul, sign_pow, sign_pow, sign_pos hx,
    one_pow, mul_one]
  simp

/-- At a point with `Im z < 0`, the rotation family preserves orientations. -/
theorem _root_.Orientation.orientationSign_sphereRotationFamily_of_im_neg
    (o : Orientation ℝ E (Fin (m + 1 + 1)))
    (p : sphere (0 : E) 1) {x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1}
    (hx : (x.2 : ℂ).im < 0) :
    orientationSign
      ((o.orthogonalSpanSingleton (ne_zero_of_mem_unit_sphere p)).sphereOrientation.prod
        Complex.orientation.sphereOrientation) o.sphereOrientation
      (sphereRotationFamily p) x = 1 := by
  rw [o.orientationSign_sphereRotationFamily p hx.ne, ← mul_pow, sign_pow,
    sign_pos (by linarith : (0 : ℝ) < -1 * (x.2 : ℂ).im), one_pow, SignType.coe_one]

/-! ### Regular values and the degree -/

/-- Every point of the sphere other than `±p` is a regular value of the rotation family. -/
theorem isRegularValue_sphereRotationFamily (p : sphere (0 : E) 1) {q : sphere (0 : E) 1}
    (hqp : q ≠ p) (hqp' : q ≠ -p) :
    IsRegularValue ((𝓡 m).prod (𝓡 1)) (𝓡 (m + 1)) (sphereRotationFamily p) q := by
  rw [isRegularValue_iff]
  intro x hx
  have him : (x.2 : ℂ).im ≠ 0 := fun h0 ↦
    (sphereRotationFamily_eq_or_eq_neg_of_im_eq_zero p h0).elim (fun h ↦ hqp (hx ▸ h))
      fun h ↦ hqp' (hx ▸ h)
  rw [isRegularPoint_iff]
  exact (isInvertible_mfderiv_sphereRotationFamily p him).surjective

/-- **The degree of the rotation family.** At every point `q ≠ ±p` of `Sᵐ⁺¹`, a regular value
(`TauCeti.isRegularValue_sphereRotationFamily`), the rotation family `Sᵐ × S¹ → Sᵐ⁺¹` has degree
`1 + (-1)ᵐ` for the outward-normal orientations. The two preimages of `q` contribute `(-1)ᵐ` and
`1`. -/
theorem _root_.Orientation.degreeAtRegularValue_sphereRotationFamily
    (o : Orientation ℝ E (Fin (m + 1 + 1)))
    (p : sphere (0 : E) 1) {q : sphere (0 : E) 1} (hqp : q ≠ p) (hqp' : q ≠ -p) :
    degreeAtRegularValue
      ((o.orthogonalSpanSingleton (ne_zero_of_mem_unit_sphere p)).sphereOrientation.prod
        Complex.orientation.sphereOrientation) o.sphereOrientation
      (sphereRotationFamily p) q = 1 + (-1) ^ m := by
  classical
  obtain ⟨x, hxim, rfl⟩ := exists_sphereRotationFamily_eq p hqp hqp'
  -- The second preimage is the image of `x` under `(v, z) ↦ (-v, conj z)`.
  let x' : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1 :=
    (-x.1, ⟨(starRingEnd ℂ) (x.2 : ℂ), by
      rw [mem_sphere_zero_iff_norm, Complex.norm_conj]
      exact norm_eq_of_mem_sphere x.2⟩)
  have hx'im : (x'.2 : ℂ).im < 0 := by
    -- The second coordinate of the local `x'` is, as a complex number, `conj z`; unfolding it
    -- exposes the imaginary part for `Complex.conj_im`.
    change ((starRingEnd ℂ) (x.2 : ℂ)).im < 0
    rw [Complex.conj_im]
    linarith
  have hne : x ≠ x' := fun h ↦ by
    have h' := congrArg (fun y : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1 ↦
      (y.2 : ℂ).im) h
    linarith
  rw [degreeAtRegularValue_eq_sum (s := {x, x'}) fun y ↦ ?_, Finset.sum_pair hne,
    o.orientationSign_sphereRotationFamily_of_im_pos p hxim,
    o.orientationSign_sphereRotationFamily_of_im_neg p hx'im, add_comm]
  rw [Finset.mem_insert, Finset.mem_singleton,
    sphereRotationFamily_eq_sphereRotationFamily_iff p hxim.ne']
  refine or_congr_right ⟨?_, fun ⟨h₁, h₂⟩ ↦ Prod.ext (Subtype.ext (Subtype.ext ?_))
    (Subtype.ext h₂)⟩
  · rintro rfl
    exact ⟨by simp [x'], rfl⟩
  · simp [x', h₁]

/-- For odd `n = m + 1`, the rotation family `Sⁿ⁻¹ × S¹ → Sⁿ` has degree `2` at every point
`q ≠ ±p`. -/
theorem _root_.Orientation.degreeAtRegularValue_sphereRotationFamily_of_even
    (o : Orientation ℝ E (Fin (m + 1 + 1)))
    (p : sphere (0 : E) 1) (hm : Even m) {q : sphere (0 : E) 1} (hqp : q ≠ p) (hqp' : q ≠ -p) :
    degreeAtRegularValue
      ((o.orthogonalSpanSingleton (ne_zero_of_mem_unit_sphere p)).sphereOrientation.prod
        Complex.orientation.sphereOrientation) o.sphereOrientation
      (sphereRotationFamily p) q = 2 := by
  rw [o.degreeAtRegularValue_sphereRotationFamily p hqp hqp', hm.neg_one_pow]
  norm_num

end TauCeti
