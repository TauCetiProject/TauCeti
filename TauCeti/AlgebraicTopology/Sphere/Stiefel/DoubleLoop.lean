/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Circle
public import TauCeti.Geometry.Manifold.Instances.Stiefel.Rotation
public import TauCeti.Topology.MappingSpace.Sphere.LoopFamily
import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic

/-!
# The double loops of a sphere swept by orthonormal two-frames

Let `p` be a point of the unit sphere `Sⁿ` of a real inner product space `E`, and let
`Σ_p = V₂(p^⊥)` be the Stiefel manifold of orthonormal two-frames `x = (u, v)` of the tangent
space `p^⊥` of the sphere at `p`. Barraud–Damian–Humilière–Oancea (Example 6.16) attach to each
frame a double loop `σ_{p,u,v}` at `p`, which sweeps the round two-sphere through `p` spanned by
`p`, `u` and `v`. This file constructs this family and proves the homotopy on which their proof
of Proposition 6.17 rests.

For a unit vector `w ⊥ p`, the meridian `γ_w` (`TauCeti.sphereMeridian`) is the half great circle
from `p` to `-p` leaving `p` in the direction `w`. For a pair `(u, w)` the loop
`γ_w · γ_u⁻¹` at `p` goes to `-p` along `γ_w` and comes back along `γ_u`
(`TauCeti.meridianLoop`); this is the map `α` of the source. For a frame `x = (u, v)`:

* the loop of loops `Γ_{u,v}` (`TauCeti.rotatingMeridianLoop`) is `θ ↦ γ_w · γ_u⁻¹` for the
  direction `w = cos θ • u + sin θ • v` turning once around the plane of `u` and `v`; it is a loop
  in the loop space based at `γ_u · γ_u⁻¹`;
* the path of loops `χ_u` (`TauCeti.meridianContraction`) runs from the constant loop at `p` to
  `γ_u · γ_u⁻¹`: at time `s` it goes along `γ_u` up to time `s` and back;
* the double loop `σ_{p,u,v} = χ_u · Γ_{u,v} · χ_u⁻¹` (`TauCeti.stiefelDoubleLoop`) is based at
  the constant loop, and depends continuously on the frame (`TauCeti.continuous_stiefelDoubleLoop`).

The source computes the class of the family `σ_p : Σ_p → Ω²Sⁿ` through the evaluation
`β : Σ_p × S¹ → ΩSⁿ`, `(x, z) ↦ σ_x(z)`. Under the rotation family
`τ : V₂(p^⊥) × S¹ → S^{n-1} × S^{n-1}`, `((u, v), θ) ↦ (u, cos θ • u + sin θ • v)`
(`TauCeti.stiefelRotationFamily`), the map `α ∘ τ` is the evaluation of the undoubled loops
`Γ_{u,v}` (`TauCeti.meridianLoopRotation_eq_loopFamilyCircleMap`). Since conjugating a family of
loops by a family of paths does not change its free homotopy class
(`TauCeti.homotopic_loopFamilyCircleMap_trans_symm`), the evaluation `β` is homotopic to `α ∘ τ`
(`TauCeti.homotopic_loopFamilyCircleMap_stiefelDoubleLoop`). This reduces the class of `β` to the
degree of `τ` and the class of `α`.

## Main declarations

* `TauCeti.sphereMeridian`: the meridian `γ_w : p ⇝ -p`.
* `TauCeti.meridianLoop`: the loop `γ_w · γ_u⁻¹` at `p`, the map `α`.
* `TauCeti.meridianContraction`: the path of loops `χ_u`.
* `TauCeti.rotatingMeridianLoop`: the loop of loops `Γ_{u,v}`.
* `TauCeti.stiefelDoubleLoop`: the double loop `σ_{p,u,v}`, with
  `TauCeti.continuous_stiefelDoubleLoop`.
* `LinearMap.map_stiefelDoubleLoop`: a linear map carrying `(p, u, v)` to `(q, u', v')` carries
  `σ_{p,u,v}` to `σ_{q,u',v'}`.
* `TauCeti.meridianLoopRotation`: the map `α ∘ τ : Σ_p × S¹ → ΩSⁿ`.
* `TauCeti.homotopic_loopFamilyCircleMap_stiefelDoubleLoop`: the evaluation `β` of the double loops
  on the circle is homotopic to `α ∘ τ`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4.2, Example 6.16 and the proof of
  Proposition 6.17.
-/

public section

noncomputable section

open Metric Real
open scoped unitInterval

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (p : sphere (0 : E) 1)

/-! ### Meridians and the loops `α` -/

/-- The **meridian** `γ_w` of the unit sphere from `p` to `-p` in the direction of a unit vector
`w` orthogonal to `p`: the half great circle `t ↦ cos (π t) • p + sin (π t) • w`, a geodesic of the
round metric. -/
def sphereMeridian (w : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1) : Path p (-p) where
  toFun t := sphereRotationFamily p (w, Circle.homeomorphSphere (Circle.exp (π * t)))
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    simp only [coe_sphereRotationFamily, Circle.coe_homeomorphSphere_apply, Circle.coe_exp,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    fun_prop
  source' := by
    apply Subtype.ext
    simp [coe_sphereRotationFamily, Circle.coe_homeomorphSphere_apply]
  target' := by
    apply Subtype.ext
    simp [coe_sphereRotationFamily, Circle.coe_homeomorphSphere_apply]

theorem sphereMeridian_apply (w : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1) (t : I) :
    sphereMeridian p w t =
      sphereRotationFamily p (w, Circle.homeomorphSphere (Circle.exp (π * t))) :=
  (rfl)

@[simp]
theorem coe_sphereMeridian (w : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1) (t : I) :
    (sphereMeridian p w t : E) =
      cos (π * t) • (p : E) + sin (π * t) • ((w : (ℝ ∙ (p : E))ᗮ) : E) := by
  simp only [sphereMeridian_apply, coe_sphereRotationFamily,
    Circle.coe_homeomorphSphere_apply, Circle.coe_exp, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im]

/-- The meridians form a continuous family in the direction and the time. -/
theorem _root_.Continuous.sphereMeridian {Y : Type*} [TopologicalSpace Y]
    {f : Y → sphere (0 : (ℝ ∙ (p : E))ᗮ) 1} {g : Y → I} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun y => TauCeti.sphereMeridian p (f y) (g y) := by
  refine continuous_induced_rng.2 ?_
  simp only [Function.comp_def, coe_sphereMeridian]
  fun_prop

/-- The loop `γ_w · γ_u⁻¹` at `p` for a pair `x = (u, w)` of unit vectors orthogonal to `p`: along
the meridian in the direction `w` to `-p`, and back along the meridian in the direction `u`. -/
def meridianLoop (x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : (ℝ ∙ (p : E))ᗮ) 1) :
    Path p p :=
  (sphereMeridian p x.2).trans (sphereMeridian p x.1).symm

theorem meridianLoop_def (x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : (ℝ ∙ (p : E))ᗮ) 1) :
    meridianLoop p x = (sphereMeridian p x.2).trans (sphereMeridian p x.1).symm :=
  (rfl)

@[fun_prop]
theorem continuous_meridianLoop : Continuous (meridianLoop p) := by
  have h₁ : Continuous ↿(fun x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 =>
      sphereMeridian p x.2) := continuous_fst.snd.sphereMeridian p continuous_snd
  have h₂ : Continuous ↿(fun x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 =>
      sphereMeridian p x.1) := continuous_fst.fst.sphereMeridian p continuous_snd
  -- `Path.trans_continuous_family` must be elaborated before its result is compared with
  -- `meridianLoop`, otherwise unification unfolds the meridians.
  have h₃ := Path.trans_continuous_family _ h₁ _ (Path.symm_continuous_family _ h₂)
  exact Path.continuous_uncurry_iff.mp h₃

/-! ### The path of loops `χ_u` -/

/-- The **path of loops `χ_u`** from the constant loop at `p` to `γ_u · γ_u⁻¹`: at time `s` it
runs along the meridian `γ_u` up to time `s` and back. It is the path in the loop space traced by
Mathlib's homotopy `Path.Homotopy.reflTransSymm` from the constant loop to `γ_u · γ_u⁻¹`. -/
def meridianContraction (u : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1) :
    Path (Path.refl p) (meridianLoop p (u, u)) where
  toFun := (Path.Homotopy.reflTransSymm (sphereMeridian p u)).eval
  continuous_toFun := Path.continuous_uncurry_iff.mp
    (Path.Homotopy.reflTransSymm (sphereMeridian p u)).continuous
  source' := Path.Homotopy.eval_zero _
  target' := Path.Homotopy.eval_one _

@[simp]
theorem meridianContraction_apply (u : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1) (s : I) :
    meridianContraction p u s = (Path.Homotopy.reflTransSymm (sphereMeridian p u)).eval s :=
  (rfl)

theorem continuous_meridianContraction :
    Continuous fun q : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × I => meridianContraction p q.1 q.2 :=
  -- By definition, `Path.Homotopy.reflTransSymm γ` evaluates `γ` at `reflTransSymmAux`.
  Path.continuous_uncurry_iff.mp <| continuous_fst.fst.sphereMeridian p
    ((Path.Homotopy.continuous_reflTransSymmAux.comp
      (continuous_fst.snd.prodMk continuous_snd)).subtype_mk _)

/-! ### The loops of loops `Γ_{u,v}` and the double loops `σ_{p,u,v}` -/

/-- The **loop of loops `Γ_{u,v}`**, for an orthonormal pair `x = (u, v)` of vectors orthogonal to
`p`: at time `s` it is the loop `γ_w · γ_u⁻¹` for the direction `w = cos (2πs) • u + sin (2πs) • v`,
which turns once around the plane of `u` and `v`. -/
def rotatingMeridianLoop (x : stiefel (ℝ ∙ (p : E))ᗮ 2) :
    Path (meridianLoop p (stiefelProj _ 2 0 x, stiefelProj _ 2 0 x))
      (meridianLoop p (stiefelProj _ 2 0 x, stiefelProj _ 2 0 x)) where
  toFun s := meridianLoop p
    (stiefelRotationFamily (x, Circle.homeomorphSphere (Circle.exp (2 * π * s))))
  continuous_toFun := by fun_prop
  source' := by
    rw [stiefelRotationFamily_of_coe_eq_one]
    simp [Circle.coe_homeomorphSphere_apply]
  target' := by
    rw [stiefelRotationFamily_of_coe_eq_one]
    simp [Circle.coe_homeomorphSphere_apply]

@[simp]
theorem rotatingMeridianLoop_apply (x : stiefel (ℝ ∙ (p : E))ᗮ 2) (s : I) :
    rotatingMeridianLoop p x s = meridianLoop p
      (stiefelRotationFamily (x, Circle.homeomorphSphere (Circle.exp (2 * π * s)))) :=
  (rfl)

theorem continuous_rotatingMeridianLoop :
    Continuous fun q : stiefel (ℝ ∙ (p : E))ᗮ 2 × I => rotatingMeridianLoop p q.1 q.2 := by
  simp only [rotatingMeridianLoop_apply]
  fun_prop

/-- The **double loop `σ_{p,u,v}`** of Barraud–Damian–Humilière–Oancea, for an orthonormal pair
`x = (u, v)` of unit tangent vectors of the sphere at `p`: the loop of loops `Γ_{u,v}`
(`TauCeti.rotatingMeridianLoop`), based at the constant loop by conjugation with the path of loops
`χ_u` (`TauCeti.meridianContraction`). It sweeps the round two-sphere spanned by `p`, `u` and
`v`. -/
def stiefelDoubleLoop (x : stiefel (ℝ ∙ (p : E))ᗮ 2) : Path (Path.refl p) (Path.refl p) :=
  ((meridianContraction p (stiefelProj _ 2 0 x)).trans (rotatingMeridianLoop p x)).trans
    (meridianContraction p (stiefelProj _ 2 0 x)).symm

theorem stiefelDoubleLoop_def (x : stiefel (ℝ ∙ (p : E))ᗮ 2) :
    stiefelDoubleLoop p x =
      ((meridianContraction p (stiefelProj _ 2 0 x)).trans (rotatingMeridianLoop p x)).trans
        (meridianContraction p (stiefelProj _ 2 0 x)).symm :=
  (rfl)

private theorem continuous_meridianContraction_stiefelProj :
    Continuous ↿fun x : stiefel (ℝ ∙ (p : E))ᗮ 2 =>
      meridianContraction p (stiefelProj _ 2 0 x) := by
  have hf : Continuous fun q : stiefel (ℝ ∙ (p : E))ᗮ 2 × I => (stiefelProj _ 2 0 q.1, q.2) :=
    ((continuous_stiefelProj 0).comp continuous_fst).prodMk continuous_snd
  -- As in `continuous_meridianLoop`, the composite is elaborated before it is compared with the
  -- uncurried family.
  have h := (continuous_meridianContraction p).comp hf
  exact h

/-- The double loops `σ_{p,u,v}` depend continuously on the frame. -/
theorem continuous_stiefelDoubleLoop : Continuous (stiefelDoubleLoop p) := by
  have h₁ := continuous_meridianContraction_stiefelProj p
  have h₂ : Continuous ↿fun x : stiefel (ℝ ∙ (p : E))ᗮ 2 => rotatingMeridianLoop p x :=
    continuous_rotatingMeridianLoop p
  have h₃ := Path.trans_continuous_family _ (Path.trans_continuous_family _ h₁ _ h₂) _
    (Path.symm_continuous_family _ h₁)
  exact Path.continuous_uncurry_iff.mp h₃

/-! ### Equivariance under linear maps -/

section Equivariance

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] (L : E →ₗ[ℝ] F)
  {p} {q : sphere (0 : F) 1}

private theorem _root_.LinearMap.map_sphereMeridian (hq : (q : F) = L p)
    {w : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1} {w' : sphere (0 : (ℝ ∙ (q : F))ᗮ) 1}
    (hw : ((w' : (ℝ ∙ (q : F))ᗮ) : F) = L ((w : (ℝ ∙ (p : E))ᗮ) : E)) (t : I) :
    L (sphereMeridian p w t) = (sphereMeridian q w' t : F) := by
  simp [hq, hw]

private theorem _root_.LinearMap.map_meridianLoop (hq : (q : F) = L p)
    {x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : (ℝ ∙ (p : E))ᗮ) 1}
    {x' : sphere (0 : (ℝ ∙ (q : F))ᗮ) 1 × sphere (0 : (ℝ ∙ (q : F))ᗮ) 1}
    (h₁ : ((x'.1 : (ℝ ∙ (q : F))ᗮ) : F) = L ((x.1 : (ℝ ∙ (p : E))ᗮ) : E))
    (h₂ : ((x'.2 : (ℝ ∙ (q : F))ᗮ) : F) = L ((x.2 : (ℝ ∙ (p : E))ᗮ) : E)) (t : I) :
    L (meridianLoop p x t) = (meridianLoop q x' t : F) := by
  rw [meridianLoop_def, meridianLoop_def, Path.trans_apply, Path.trans_apply]
  split_ifs
  · exact L.map_sphereMeridian hq h₂ _
  · rw [Path.symm_apply, Path.symm_apply]
    exact L.map_sphereMeridian hq h₁ _

/-- **The double loops are equivariant under linear maps.** If a linear map `L : E → F` carries
the point `p` and the frame `(u, v)` of `p^⊥` to the point `q` and the frame `(u', v')` of `q^⊥`,
then it carries the double loop `σ_{p,u,v}` to `σ_{q,u',v'}`. The meridians and rotations that
the double loops are built from are linear combinations of `p`, `u` and `v` whose coefficients only
depend on the times. -/
theorem _root_.LinearMap.map_stiefelDoubleLoop (hq : (q : F) = L p)
    {x : stiefel (ℝ ∙ (p : E))ᗮ 2} {y : stiefel (ℝ ∙ (q : F))ᗮ 2}
    (hy : ∀ i, ((y : Fin 2 → (ℝ ∙ (q : F))ᗮ) i : F) = L ((x : Fin 2 → (ℝ ∙ (p : E))ᗮ) i))
    (s t : I) :
    L (stiefelDoubleLoop p x s t) = (stiefelDoubleLoop q y s t : F) := by
  have h₀ : ((stiefelProj _ 2 0 y : (ℝ ∙ (q : F))ᗮ) : F) =
      L ((stiefelProj _ 2 0 x : (ℝ ∙ (p : E))ᗮ) : E) := by simpa using hy 0
  have hcontr (s' : I) : L (meridianContraction p (stiefelProj _ 2 0 x) s' t) =
      (meridianContraction q (stiefelProj _ 2 0 y) s' t : F) := by
    rw [meridianContraction_apply, meridianContraction_apply]
    -- `Path.Homotopy.reflTransSymm γ` evaluates `γ` at `reflTransSymmAux`.
    exact L.map_sphereMeridian hq h₀ _
  rw [stiefelDoubleLoop_def, stiefelDoubleLoop_def, Path.trans_apply, Path.trans_apply]
  split_ifs
  · rw [Path.trans_apply, Path.trans_apply]
    split_ifs
    · exact hcontr _
    · rw [rotatingMeridianLoop_apply, rotatingMeridianLoop_apply]
      refine L.map_meridianLoop hq ?_ ?_ _
      · simpa using hy 0
      · simp [hy]
  · rw [Path.symm_apply, Path.symm_apply]
    exact hcontr _

end Equivariance

/-! ### The evaluation of the double loops on the circle -/

/-- The map `α ∘ τ : Σ_p × S¹ → ΩSⁿ` of Barraud–Damian–Humilière–Oancea: a frame `x` and a point
`z` of the circle are sent to the loop `γ_w · γ_u⁻¹` for `(u, w) = τ(x, z)` the image under the
Stiefel rotation family, the circle `S¹ ⊆ ℝ²` being identified with the unit circle of `ℂ`. -/
def meridianLoopRotation : C(stiefel (ℝ ∙ (p : E))ᗮ 2 × Sphere1, Path p p) where
  toFun q := meridianLoop p (stiefelRotationFamily
    (q.1, Circle.homeomorphSphere (EuclideanSpace.sphereHomeomorphCircle q.2)))
  continuous_toFun := (continuous_meridianLoop p).comp (continuous_stiefelRotationFamily.comp
    (continuous_fst.prodMk (Circle.homeomorphSphere.continuous.comp
      (EuclideanSpace.sphereHomeomorphCircle.continuous.comp continuous_snd))))

@[simp]
theorem meridianLoopRotation_apply (x : stiefel (ℝ ∙ (p : E))ᗮ 2) (z : Sphere1) :
    meridianLoopRotation p (x, z) = meridianLoop p (stiefelRotationFamily
      (x, Circle.homeomorphSphere (EuclideanSpace.sphereHomeomorphCircle z))) :=
  (rfl)

/-- The map `α ∘ τ` is the evaluation on the circle of the loops of loops `Γ_{u,v}`. -/
theorem meridianLoopRotation_eq_loopFamilyCircleMap :
    meridianLoopRotation p = loopFamilyCircleMap (rotatingMeridianLoop p)
      (continuous_rotatingMeridianLoop p) := by
  refine ext_circleLoop fun x t => ?_
  rw [loopFamilyCircleMap_apply_circleLoop, rotatingMeridianLoop_apply, meridianLoopRotation_apply,
    sphereHomeomorphCircle_circleLoop]

/-- **The evaluation of the double loops `σ_{p,u,v}` on the circle is homotopic to `α ∘ τ`**
(Barraud–Damian–Humilière–Oancea, proof of Proposition 6.17): the map
`β : Σ_p × S¹ → ΩSⁿ`, `(x, z) ↦ σ_x(z)`, is homotopic to `TauCeti.meridianLoopRotation`, which sends
`(x, z)` to `γ_w · γ_u⁻¹` for `(u, w) = τ(x, z)`. -/
theorem homotopic_loopFamilyCircleMap_stiefelDoubleLoop :
    (loopFamilyCircleMap (stiefelDoubleLoop p)
      (Path.continuous_uncurry_iff.mpr (continuous_stiefelDoubleLoop p))).Homotopic
      (meridianLoopRotation p) := by
  rw [meridianLoopRotation_eq_loopFamilyCircleMap]
  exact homotopic_loopFamilyCircleMap_trans_symm _ (continuous_meridianContraction_stiefelProj p)
    _ (continuous_rotatingMeridianLoop p)

end TauCeti
