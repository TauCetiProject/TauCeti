/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Homotopy
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Path
public import TauCeti.Geometry.Manifold.ContMDiff.Curve
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import TauCeti.Analysis.Calculus.DifferentialForm.Stokes
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
import TauCeti.Geometry.Manifold.ContMDiff.Fract

/-!
# Gluing and reparametrization of integrals over rectangles

This file develops the integral
`∫_u φ = ∫_{a.1}^{b.1} ∫_{a.2}^{b.2} φ_{u(s, t)}(∂_s u, ∂_t u) dt ds`
of a two-form `φ` over a map `u : ℝ × ℝ → M` (`TauCeti.rectangleIntegral`, defined in
`TauCeti.Geometry.Manifold.DifferentialForm.Integration.Homotopy`) along the first
coordinate `s`, the coordinate along which a cylinder `u` joins its boundary loops `u(a.1, ·)` and
`u(b.1, ·)`. For a continuous form and a `C¹` map:

* the integral is additive under subdivision of `[a.1, b.1]`
  (`TauCeti.rectangleIntegral_add_adjacent_fst`);
* specializing its invariance under a `C¹` change of the first coordinate, proved in
  `Integration.Homotopy` (`TauCeti.rectangleIntegral_comp_prodMap` and
  `TauCeti.rectangleIntegral_comp_prodMap_of_contDiff`), it is invariant under an affine change of
  the first coordinate (`TauCeti.rectangleIntegral_comp_prodMap_affine`), and reversing the first
  coordinate changes its sign (`TauCeti.rectangleIntegral_comp_prodMap_one_sub`); so does
  reversing the second coordinate (`TauCeti.rectangleIntegral_comp_prodMap_id_one_sub`);
* it is likewise additive under subdivision of `[a.2, b.2]`
  (`TauCeti.rectangleIntegral_add_adjacent_snd`) and invariant under a `C¹` change of the second
  coordinate (`TauCeti.rectangleIntegral_comp_prodMap_snd`).

In the second coordinate, the circle coordinate of a cylinder, a differentiable map `u` that is
`T`-periodic in `t` has the same integral as its rotation `z ↦ u (z + (0, θ))` over a rectangle
spanning one period (`TauCeti.rectangleIntegral_comp_add_snd_of_periodic`). This is the invariance
of the area of a cylinder or cap under a change of the origin of its circle coordinate.

Two maps `u₁ u₂ : ℝ × ℝ → M` with `u₁(1, ·) = u₂(0, ·)` are glued into their concatenation
`TauCeti.rectangleTrans u₁ u₂`, the curve concatenation `TauCeti.curveConcat` in the first
coordinate of `u₁` and `u₂` reparametrized by a smooth transition function. It runs through `u₁`
for `s ∈ [0, 1/3]`, rests at the common edge for `s ∈ [1/3, 2/3]` and runs through `u₂` for
`s ∈ [2/3, 1]`, so it is as smooth as `u₁` and `u₂` (`TauCeti.contMDiff_rectangleTrans`). It
is periodic in `t` when `u₁` and `u₂` are, and its integral is the sum of the integrals of `u₁` and
`u₂` (`TauCeti.rectangleIntegral_rectangleTrans`). This is how a cap of a loop is glued to a
cylinder ending at the loop, and how two caps of the same loop are glued into a sphere, whose
integral is the difference of the integrals of the two caps
(`TauCeti.rectangleIntegral_rectangleTrans_comp_prodMap_one_sub`).

Two maps `u₁ u₂ : ℝ × ℝ → M` with `u₁(·, 1) = u₂(·, 0)` and `u₂(·, 1) = u₁(·, 0)` are placed
side by side in their loopwise concatenation `TauCeti.loopwiseTrans u₁ u₂`, which for each `s`
runs through the loop `u₁(s, ·)` on `[0, 1/2]` and through `u₂(s, ·)` on `[1/2, 1]`, reparametrized
so that it rests near `t = 1/2` and near the integers, and is `1`-periodic in `t`. It is as smooth
as `u₁` and `u₂` (`TauCeti.contMDiff_loopwiseTrans`), and its integral over `[a₁, b₁] × [0, 1]` is
the sum of those of `u₁` and `u₂` (`TauCeti.rectangleIntegral_loopwiseTrans`). This is how caps of
two loops based at the same point are placed side by side, as a cap of their collared
concatenation (`Path.collaredTrans`).

A smooth cylinder from the loop `γ` to the loop `γ₀` (`TauCeti.IsSmoothCylinder`) is a smooth map
`u` with `u (0, ·) = γ`, `u (1, ·) = γ₀` and `u (s, 1) = u (s, 0)`. More generally, for a map
`f : M → M`, a smooth `f`-seamed cylinder (`TauCeti.IsSmoothSeamedCylinder`) asks
`u (s, 1) = f (u (s, 0))` instead, so that it joins two `f`-seamed paths, the paths `γ` with
`γ 1 = f (γ 0)` on which the Floer theory of a symplectomorphism `f` is built; the cylinders are
defined as the case `f = id`. Seamed cylinders concatenate and reverse, and a smooth family of
seamed paths gives seamed cylinders between any two of its members.

Finally, a two-form vanishes on spheres (`TauCeti.VanishesOnSpheres`) or on tori
(`TauCeti.VanishesOnTori`) when its integral over every map of the square factoring through a
sphere, respectively a torus, vanishes. It vanishes on `f`-seamed tori
(`TauCeti.VanishesOnSeamedTori`) when its integral vanishes over every map of the square that
agrees on the two vertical edges and is `f`-seamed along the horizontal ones, so that it sweeps out
a loop of `f`-seamed paths; for `f = id` these are the tori. Such a form has the same integral over
any two caps of a loop (`TauCeti.VanishesOnSpheres.rectangleIntegral_eq`), respectively over any
two seamed cylinders between the same seamed paths
(`TauCeti.VanishesOnSeamedTori.rectangleIntegral_eq`, and
`TauCeti.VanishesOnTori.rectangleIntegral_eq` for cylinders). By Green's formula
`TauCeti.rectangleIntegral_mextDeriv` from `Integration.Homotopy`, which expresses the integral of
an exact two-form `dα` as the signed sum of the line integrals of `α` along the four edges of the
rectangle, exact two-forms vanish on spheres, and on `f`-seamed tori when `f` preserves the
primitive, `f^* α = α`, in particular on tori. A symplectic form need not vanish on seamed tori
even when it vanishes on spheres: for `f = id` on a torus, the loop of seamed paths
`s ↦ (t ↦ (t, s))` sweeps out the whole torus.

## Main definitions

* `TauCeti.rectangleTrans u₁ u₂`: the concatenation of two maps of the plane along the first
  coordinate.
* `TauCeti.loopwiseTrans u₁ u₂`: the concatenation of two maps of the plane along the second
  coordinate, periodic in it.
* `TauCeti.IsSmoothSeamedCylinder I f γ γ₀ u`, `TauCeti.IsSmoothCylinder I γ γ₀ u`: `u` is a
  smooth `f`-seamed cylinder, respectively a smooth cylinder, from `γ` to `γ₀`.
* `TauCeti.VanishesOnSpheres φ`, `TauCeti.VanishesOnTori φ`: the integral of `φ` vanishes over
  every map of the square factoring through a sphere, respectively a torus.
* `TauCeti.VanishesOnSeamedTori f φ`: the integral of `φ` vanishes over every map of the square
  that agrees on its vertical edges and is `f`-seamed, `u (s, 1) = f (u (s, 0))`.

## Main results

* `TauCeti.rectangleIntegral_comp_add_snd_of_periodic`: rotation invariance in the second
  coordinate over a full period.
* `TauCeti.rectangleIntegral_add_adjacent_fst`: additivity in the first coordinate.
* `TauCeti.rectangleIntegral_comp_prodMap_affine`: reparametrization by an affine function in the
  first coordinate.
* `TauCeti.rectangleIntegral_add_adjacent_snd`, `TauCeti.rectangleIntegral_comp_prodMap_snd`:
  additivity and reparametrization in the second coordinate.
* `TauCeti.rectangleIntegral_rectangleTrans`: the integral over a concatenation.
* `TauCeti.rectangleIntegral_rectangleTrans_comp_prodMap_one_sub`: the integral over two maps
  glued along their common start.
* `TauCeti.loopwiseTrans_congr`, `TauCeti.loopwiseTrans_mem`, `TauCeti.apply_loopwiseTrans`: a
  loopwise concatenation only depends on its maps over `t ∈ [0, 1]`, lies in every set containing
  their values there, and commutes with composition.
* `TauCeti.contMDiff_loopwiseTrans`, `TauCeti.rectangleIntegral_loopwiseTrans`: smoothness of and
  the integral over a loopwise concatenation.
* `TauCeti.IsSmoothSeamedCylinder.trans`, `TauCeti.IsSmoothCylinder.trans`: the concatenation of
  two smooth (seamed) cylinders is a smooth (seamed) cylinder.
* `TauCeti.IsSmoothSeamedCylinder.comp_prodMap_one_sub`,
  `TauCeti.IsSmoothCylinder.comp_prodMap_one_sub`: a smooth (seamed) cylinder run backwards is a
  smooth (seamed) cylinder.
* `TauCeti.isSmoothSeamedCylinder_comp_prodMap_affine`,
  `TauCeti.isSmoothCylinder_comp_prodMap_affine`: rescaling a smooth family of seamed paths, or a
  smooth map `1`-periodic in `t`, from `[a, b]` to `[0, 1]` in the first coordinate gives a smooth
  (seamed) cylinder.
* `TauCeti.VanishesOnSpheres.rectangleIntegral_eq`,
  `TauCeti.VanishesOnSeamedTori.rectangleIntegral_eq`,
  `TauCeti.VanishesOnTori.rectangleIntegral_eq`: independence of the cap and of the (seamed)
  cylinder.
* `TauCeti.vanishesOnSpheres_mextDeriv`, `TauCeti.vanishesOnSeamedTori_mextDeriv`,
  `TauCeti.vanishesOnTori_mextDeriv`: exact two-forms vanish on spheres, on seamed tori when the
  seam preserves the primitive, and on tori.

## References

* R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*, GTM 82, Springer, 1982, §3
  (Stokes' theorem).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS, 2012,
  the chapter on Floer homology (gluing cylinders and caps of loops).
* Y.-J. Lee, *Reidemeister torsion in Floer–Novikov theory and counting pseudo-holomorphic tori,
  I*, J. Symplectic Geom. 3 (2005), 221–311, §3.1 (paths seamed by a symplectomorphism and the
  tori swept out by their loops).
-/

public section

noncomputable section

open Set Real MeasureTheory
open scoped Manifold Interval ContDiff Topology

namespace TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ### Rotation in the second coordinate -/

/-- **Rotating a periodic map.** If a differentiable map `u` of the plane is `T`-periodic in its
second coordinate, its rotation `z ↦ u (z + (0, θ))` has the same integral as `u` over every
rectangle `[a₁, b₁] × [a₂, a₂ + T]` spanning one period in the second coordinate. For a cylinder,
`T = 1`, this is the invariance of its integral under a rotation of the circle coordinate. -/
theorem rectangleIntegral_comp_add_snd_of_periodic (φ : RoughForm I M F 2) {u : ℝ × ℝ → M}
    (hu : MDifferentiable 𝓘(ℝ, ℝ × ℝ) I u) {T : ℝ} (hT : ∀ z : ℝ × ℝ, u (z.1, z.2 + T) = u z)
    (θ a₁ b₁ a₂ : ℝ) :
    rectangleIntegral φ (fun z ↦ u (z + (0, θ))) (a₁, a₂) (b₁, a₂ + T) =
      rectangleIntegral φ u (a₁, a₂) (b₁, a₂ + T) := by
  set G : ℝ × ℝ → F := fun z ↦ mpullback 𝓘(ℝ, ℝ × ℝ) I u φ z ![(1, 0), (0, 1)]
  -- The integrand `G` is `T`-periodic in the second coordinate, since `u` is.
  have hG (z : ℝ × ℝ) : G (z + (0, T)) = G z := by
    have hu' : (fun w ↦ u (w + (0, T))) = u := funext fun ⟨a, b⟩ ↦ by simpa using hT (a, b)
    have h := congrArg (fun A ↦ A ![(1, 0), (0, 1)])
      (mpullback_comp_add_right (c := ((0 : ℝ), T)) (hu (z + (0, T))) φ)
    rw [hu'] at h
    exact h.symm
  have hper (s : ℝ) : Function.Periodic (fun t ↦ G (s, t)) T := fun t ↦ by
    simpa using hG (s, t)
  rw [rectangleIntegral_comp_add_right φ hu]
  simp only [Prod.mk_add_mk, add_zero, rectangleIntegral_def]
  refine intervalIntegral.integral_congr fun s _ ↦ ?_
  rw [add_right_comm]
  exact Function.Periodic.intervalIntegral_add_eq (hper s) (a₂ + θ) a₂

/-! ### Additivity and reparametrization in the first coordinate -/

section Continuous

variable [IsManifold I 1 M]

/-- The inner integral of a rectangle integral of a continuous form over a `C¹` map is a
continuous function of the first coordinate. -/
theorem continuous_integral_mpullback {φ : RoughForm I M F 2} (hφ : IsSmoothForm I 0 φ)
    {u : ℝ × ℝ → M} (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u) (a₂ b₂ : ℝ) :
    Continuous fun s ↦ ∫ t in a₂..b₂, mpullback 𝓘(ℝ, ℝ × ℝ) I u φ (s, t) ![(1, 0), (0, 1)] :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume)
    ((hφ.continuous_mpullback_apply hu ![(1, 0), (0, 1)]).congr fun _ ↦ rfl) a₂ b₂

/-- **Additivity in the first coordinate.** For a continuous form and a `C¹` map, the integral
over `[a.1, b.1] × [a.2, b.2]` is the sum of the integrals over `[a.1, c] × [a.2, b.2]` and
`[c, b.1] × [a.2, b.2]`. -/
theorem rectangleIntegral_add_adjacent_fst {φ : RoughForm I M F 2} (hφ : IsSmoothForm I 0 φ)
    {u : ℝ × ℝ → M} (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u) (a b : ℝ × ℝ) (c : ℝ) :
    rectangleIntegral φ u a (c, b.2) + rectangleIntegral φ u (c, a.2) b =
      rectangleIntegral φ u a b := by
  have h := continuous_integral_mpullback hφ hu a.2 b.2
  simp only [rectangleIntegral_def]
  exact intervalIntegral.integral_add_adjacent_intervals (h.intervalIntegrable (μ := volume) _ _)
    (h.intervalIntegrable _ _)

/-- Reversing the first coordinate changes the sign of the integral. -/
theorem rectangleIntegral_comp_prodMap_one_sub {φ : RoughForm I M F 2} (hφ : IsSmoothForm I 0 φ)
    {u : ℝ × ℝ → M} (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u) (a₂ b₂ : ℝ) :
    rectangleIntegral φ (u ∘ Prod.map (fun s ↦ 1 - s) id) (0, a₂) (1, b₂) =
      -rectangleIntegral φ u (0, a₂) (1, b₂) := by
  rw [rectangleIntegral_comp_prodMap hφ hu (σ' := fun _ ↦ -1)
    (fun s _ ↦ by simpa using (hasDerivAt_id s).const_sub 1) continuousOn_const]
  simpa using rectangleIntegral_symm_fst φ u 0 a₂ 1 b₂

/-- The affine rescaling `(s, t) ↦ (a + (b - a) s, t)` of the plane, carrying `[0, 1]` onto
`[a, b]` in the first coordinate, is smooth. -/
theorem contMDiff_prodMap_affine {n : WithTop ℕ∞} (a b : ℝ) :
    ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) n
      (Prod.map (fun s : ℝ ↦ a + (b - a) * s) (id : ℝ → ℝ)) :=
  ((contDiff_const.add (contDiff_const.mul contDiff_id)).prodMap contDiff_id).contMDiff

/-- Rescaling the first coordinate affinely from `[0, 1]` to `[a, b]` does not change the
integral. -/
theorem rectangleIntegral_comp_prodMap_affine {φ : RoughForm I M F 2} (hφ : IsSmoothForm I 0 φ)
    {u : ℝ × ℝ → M} (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u) (a b a₂ b₂ : ℝ) :
    rectangleIntegral φ (u ∘ Prod.map (fun s ↦ a + (b - a) * s) id) (0, a₂) (1, b₂) =
      rectangleIntegral φ u (a, a₂) (b, b₂) := by
  rw [rectangleIntegral_comp_prodMap hφ hu (σ' := fun _ ↦ b - a)
    (fun s _ ↦ by simpa using ((hasDerivAt_id s).const_mul (b - a)).const_add a)
    continuousOn_const]
  simp

/-- **The area swept by a variation.** For a continuous form and a `C¹` map `u`, the integral over
the restriction of `u` to `[s, s₀] × [a₂, b₂]`, rescaled to `[0, 1]` in the first coordinate, has
derivative `-∫_{a₂}^{b₂} φ(∂_s u, ∂_t u) dt` in `s` at `s₀`, the integrand taken at `(s₀, t)`. -/
theorem hasDerivAt_rectangleIntegral_comp_prodMap_affine [CompleteSpace F]
    {φ : RoughForm I M F 2} (hφ : IsSmoothForm I 0 φ) {u : ℝ × ℝ → M}
    (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u) (s₀ a₂ b₂ : ℝ) :
    HasDerivAt
      (fun s ↦ rectangleIntegral φ (u ∘ Prod.map (fun r ↦ s + (s₀ - s) * r) id) (0, a₂) (1, b₂))
      (-∫ t in a₂..b₂, φ (u (s₀, t)) ![mfderiv 𝓘(ℝ, ℝ × ℝ) I u (s₀, t) (1, 0),
        mfderiv 𝓘(ℝ, ℝ × ℝ) I u (s₀, t) (0, 1)]) s₀ := by
  have hf := continuous_integral_mpullback hφ hu a₂ b₂
  have heq : (fun s ↦ rectangleIntegral φ (u ∘ Prod.map (fun r ↦ s + (s₀ - s) * r) id)
      (0, a₂) (1, b₂)) = fun s ↦ -∫ x in s₀..s,
        ∫ t in a₂..b₂, mpullback 𝓘(ℝ, ℝ × ℝ) I u φ (x, t) ![(1, 0), (0, 1)] := by
    funext s
    rw [rectangleIntegral_comp_prodMap_affine hφ hu, rectangleIntegral_def,
      intervalIntegral.integral_symm]
  rw [heq]
  convert (hf.integral_hasStrictDerivAt s₀ s₀).hasDerivAt.neg using 2
  exact intervalIntegral.integral_congr fun t _ ↦ (mpullback_apply_pair u φ (s₀, t) _ _).symm

/-! ### Additivity and reparametrization in the second coordinate -/

/-- **Additivity in the second coordinate.** For a continuous form and a `C¹` map, the integral
over `[a.1, b.1] × [a.2, b.2]` is the sum of the integrals over `[a.1, b.1] × [a.2, c]` and
`[a.1, b.1] × [c, b.2]`. -/
theorem rectangleIntegral_add_adjacent_snd {φ : RoughForm I M F 2} (hφ : IsSmoothForm I 0 φ)
    {u : ℝ × ℝ → M} (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u) (a b : ℝ × ℝ) (c : ℝ) :
    rectangleIntegral φ u a (b.1, c) + rectangleIntegral φ u (a.1, c) b =
      rectangleIntegral φ u a b := by
  have hG := hφ.continuous_mpullback_apply hu ![(1, 0), (0, 1)]
  have hi (s c d : ℝ) : IntervalIntegrable
      (fun t ↦ mpullback 𝓘(ℝ, ℝ × ℝ) I u φ (s, t) ![(1, 0), (0, 1)]) volume c d :=
    (hG.comp (Continuous.prodMk_right s)).intervalIntegrable _ _
  simp only [rectangleIntegral_def]
  rw [← intervalIntegral.integral_add
    ((continuous_integral_mpullback hφ hu _ _).intervalIntegrable _ _)
    ((continuous_integral_mpullback hφ hu _ _).intervalIntegrable _ _)]
  exact intervalIntegral.integral_congr fun s _ ↦
    intervalIntegral.integral_add_adjacent_intervals (hi s _ _) (hi s _ _)

/-- **Reparametrization invariance in the second coordinate.** For a continuous form `φ`, a `C¹`
map `u` of the plane and a `C¹` change of parameter `τ`, the integral over
`(s, t) ↦ u (s, τ t)` is the integral over `u` on the rectangle between the image corners. The
change of parameter need not be monotone. -/
theorem rectangleIntegral_comp_prodMap_snd {φ : RoughForm I M F 2} (hφ : IsSmoothForm I 0 φ)
    {u : ℝ × ℝ → M} (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u) {τ τ' : ℝ → ℝ} {a b : ℝ × ℝ}
    (hτ : ∀ t ∈ [[a.2, b.2]], HasDerivAt τ (τ' t) t) (hτ' : ContinuousOn τ' [[a.2, b.2]]) :
    rectangleIntegral φ (u ∘ Prod.map id τ) a b =
      rectangleIntegral φ u (a.1, τ a.2) (b.1, τ b.2) := by
  have hG := hφ.continuous_mpullback_apply hu ![(1, 0), (0, 1)]
  simp only [rectangleIntegral_def]
  refine intervalIntegral.integral_congr fun s _ ↦ ?_
  refine Eq.trans ?_
    (intervalIntegral.integral_deriv_smul_comp hτ hτ' (hG.comp (Continuous.prodMk_right s)))
  refine intervalIntegral.integral_congr fun t ht ↦ ?_
  -- The derivative of `Prod.map id τ` sends the coordinate vectors to `(1, 0)` and `(0, τ' t)`.
  let A : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
    (ContinuousLinearMap.id ℝ ℝ).prodMap (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (τ' t))
  have hL : HasFDerivAt (Prod.map id τ) A (s, t) :=
    (hasFDerivAt_id s).prodMap (s, t) (hτ t ht).hasFDerivAt
  have hv : (A ∘ ![(1, 0), (0, 1)]) =
      Function.update ![((1 : ℝ), (0 : ℝ)), (0, 1)] 1 (τ' t • ((0 : ℝ), (1 : ℝ))) := by
    funext i
    fin_cases i <;> simp [A]
  rw [mpullback_comp_apply_of_hasFDerivAt hL ((hu _).mdifferentiableAt one_ne_zero)]
  -- Read the pullback as a flat form on the plane, whose tangent spaces are `ℝ × ℝ` itself.
  let ψ : ℝ × ℝ → (ℝ × ℝ) [⋀^Fin 2]→L[ℝ] F := mpullback 𝓘(ℝ, ℝ × ℝ) I u φ
  refine (((ContinuousAlternatingMap.compContinuousLinearMap_apply _ _ _).trans
    (congrArg _ hv)).trans ((ψ (s, τ t)).map_update_smul _ _ _ _)).trans ?_
  congr 2
  funext i
  fin_cases i <;> rfl

/-- **Reparametrization by a `C¹` function in the second coordinate.** For a continuous form, a
`C¹` map `u` and a `C¹` function `τ`, the integral over `(s, t) ↦ u (s, τ t)` is the integral over
`u` on the rectangle between the image corners. -/
theorem rectangleIntegral_comp_prodMap_snd_of_contDiff {φ : RoughForm I M F 2}
    (hφ : IsSmoothForm I 0 φ) {u : ℝ × ℝ → M} (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u) {τ : ℝ → ℝ}
    (hτ : ContDiff ℝ 1 τ) {a b : ℝ × ℝ} :
    rectangleIntegral φ (u ∘ Prod.map id τ) a b =
      rectangleIntegral φ u (a.1, τ a.2) (b.1, τ b.2) :=
  rectangleIntegral_comp_prodMap_snd hφ hu (fun t _ ↦ (hτ.differentiable one_ne_zero t).hasDerivAt)
    (hτ.continuous_deriv le_rfl).continuousOn

end Continuous

/-- Reversing the second coordinate of a differentiable map changes the sign of its integral over
`[a₁, b₁] × [0, 1]`. -/
theorem rectangleIntegral_comp_prodMap_id_one_sub (φ : RoughForm I M F 2) {u : ℝ × ℝ → M}
    (hu : MDifferentiable 𝓘(ℝ, ℝ × ℝ) I u) (a₁ b₁ : ℝ) :
    rectangleIntegral φ (u ∘ Prod.map id (fun t ↦ 1 - t)) (a₁, 0) (b₁, 1) =
      -rectangleIntegral φ u (a₁, 0) (b₁, 1) := by
  rw [rectangleIntegral_def, rectangleIntegral_def, ← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr fun s _ ↦ ?_
  -- The derivative of `Prod.map id (1 - ·)` sends `(0, 1)` to `-(0, 1)`, so the integrand at
  -- `(s, t)` is minus the integrand of `u` at `(s, 1 - t)`.
  have hpt (t : ℝ) : mpullback 𝓘(ℝ, ℝ × ℝ) I (u ∘ Prod.map id fun t ↦ 1 - t) φ (s, t)
      ![(1, 0), (0, 1)] = -mpullback 𝓘(ℝ, ℝ × ℝ) I u φ (s, 1 - t) ![(1, 0), (0, 1)] := by
    simpa using mpullback_comp_prodMap_apply φ (hasDerivAt_id s)
      ((hasDerivAt_id t).const_sub 1) (hu _)
  simp_rw [hpt, intervalIntegral.integral_neg,
    intervalIntegral.integral_comp_sub_left (fun t ↦ mpullback 𝓘(ℝ, ℝ × ℝ) I u φ (s, t)
      ![(1, 0), (0, 1)]) 1, sub_self, sub_zero]

/-! ### Concatenation along the first coordinate -/

/-- The concatenation of two maps `u₁ u₂ : ℝ × ℝ → M` along the first coordinate: for each `t`,
the concatenation `TauCeti.curveConcat` of the curves `s ↦ u₁ (β s, t)` and `s ↦ u₂ (β s, t)`,
where `β = Real.smoothTransition` rests at `0` before time `0` and at `1` after time `1`. On
`[0, 1]` it runs through `u₁` for `s ∈ [0, 1/3]` and through `u₂` for `s ∈ [2/3, 1]`. When
`u₁ (1, ·) = u₂ (0, ·)` it rests at this common edge for `s ∈ [1/3, 2/3]`, so it is as smooth as
`u₁` and `u₂`. It starts at `u₁ (0, ·)` and ends at `u₂ (1, ·)`. -/
def rectangleTrans (u₁ u₂ : ℝ × ℝ → M) (z : ℝ × ℝ) : M :=
  curveConcat (fun s ↦ u₁ (Real.smoothTransition s, z.2))
    (fun s ↦ u₂ (Real.smoothTransition s, z.2)) z.1

omit [TopologicalSpace M] in
/-- The concatenation starts at the initial edge of the first map. -/
@[simp]
theorem rectangleTrans_apply_zero (u₁ u₂ : ℝ × ℝ → M) (t : ℝ) :
    rectangleTrans u₁ u₂ (0, t) = u₁ (0, t) := by
  simp [rectangleTrans]

omit [TopologicalSpace M] in
/-- The concatenation ends at the final edge of the second map. -/
@[simp]
theorem rectangleTrans_apply_one (u₁ u₂ : ℝ × ℝ → M) (t : ℝ) :
    rectangleTrans u₁ u₂ (1, t) = u₂ (1, t) := by
  rw [rectangleTrans, curveConcat_of_lt (by norm_num)]
  norm_num

omit [TopologicalSpace M] in
/-- The concatenation of two maps that are periodic in the second coordinate is periodic. -/
theorem rectangleTrans_apply_add_snd {u₁ u₂ : ℝ × ℝ → M} {T : ℝ}
    (h₁ : ∀ z : ℝ × ℝ, u₁ (z.1, z.2 + T) = u₁ z) (h₂ : ∀ z : ℝ × ℝ, u₂ (z.1, z.2 + T) = u₂ z)
    (z : ℝ × ℝ) : rectangleTrans u₁ u₂ (z.1, z.2 + T) = rectangleTrans u₁ u₂ z := by
  simp only [rectangleTrans, h₁ (_, z.2), h₂ (_, z.2)]

omit [TopologicalSpace M] in
/-- A map applied to a concatenation is the concatenation of the composites. -/
theorem apply_rectangleTrans {N : Type*} (f : M → N) (u₁ u₂ : ℝ × ℝ → M) (z : ℝ × ℝ) :
    f (rectangleTrans u₁ u₂ z) = rectangleTrans (f ∘ u₁) (f ∘ u₂) z := by
  rw [rectangleTrans, rectangleTrans]
  rcases le_or_gt z.1 2⁻¹ with h | h
  · rw [curveConcat_of_le h, curveConcat_of_le h, Function.comp_apply]
  · rw [curveConcat_of_lt h, curveConcat_of_lt h, Function.comp_apply]

omit [TopologicalSpace M] in
/-- The concatenation of two maps with values in a set `A` has values in `A`. -/
theorem rectangleTrans_mem {u₁ u₂ : ℝ × ℝ → M} {A : Set M} (h₁ : ∀ z, u₁ z ∈ A)
    (h₂ : ∀ z, u₂ z ∈ A) (z : ℝ × ℝ) : rectangleTrans u₁ u₂ z ∈ A := by
  rw [rectangleTrans]
  rcases le_or_gt z.1 2⁻¹ with h | h
  · rw [curveConcat_of_le h]
    exact h₁ _
  · rw [curveConcat_of_lt h]
    exact h₂ _

omit [TopologicalSpace M] in
/-- Below `s = 2/3` the concatenation is a reparametrization of the first map. -/
theorem rectangleTrans_eq_left {u₁ u₂ : ℝ × ℝ → M} (h : ∀ t, u₁ (1, t) = u₂ (0, t))
    {z : ℝ × ℝ} (hz : z.1 < 2 / 3) :
    rectangleTrans u₁ u₂ z =
      (u₁ ∘ Prod.map (fun s ↦ Real.smoothTransition (3 * s)) id) z := by
  rw [rectangleTrans, eqOn_curveConcat_left (y := u₁ (1, z.2))
    (fun r hr ↦ by rw [Real.smoothTransition.one_of_one_le hr])
    (fun r hr ↦ by rw [Real.smoothTransition.zero_of_nonpos hr, h]) hz]
  rfl

omit [TopologicalSpace M] in
/-- Above `s = 1/3` the concatenation is a reparametrization of the second map. -/
theorem rectangleTrans_eq_right {u₁ u₂ : ℝ × ℝ → M} (h : ∀ t, u₁ (1, t) = u₂ (0, t))
    {z : ℝ × ℝ} (hz : 1 / 3 < z.1) :
    rectangleTrans u₁ u₂ z =
      (u₂ ∘ Prod.map (fun s ↦ Real.smoothTransition (3 * s - 2)) id) z := by
  rw [rectangleTrans, eqOn_curveConcat_right (y := u₁ (1, z.2))
    (fun r hr ↦ by rw [Real.smoothTransition.one_of_one_le hr])
    (fun r hr ↦ by rw [Real.smoothTransition.zero_of_nonpos hr, h]) hz]
  rfl

/-- The concatenation of two `C^n` maps sharing an edge is `C^n`. -/
theorem contMDiff_rectangleTrans {n : ℕ∞} {u₁ u₂ : ℝ × ℝ → M}
    (hu₁ : ContMDiff 𝓘(ℝ, ℝ × ℝ) I n u₁) (hu₂ : ContMDiff 𝓘(ℝ, ℝ × ℝ) I n u₂)
    (h : ∀ t, u₁ (1, t) = u₂ (0, t)) : ContMDiff 𝓘(ℝ, ℝ × ℝ) I n (rectangleTrans u₁ u₂) := by
  have hL {f : ℝ → ℝ} (hf : ContDiff ℝ n f) : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) n
      (Prod.map (fun s ↦ Real.smoothTransition (f s)) (id : ℝ → ℝ)) :=
    ((Real.smoothTransition.contDiff.comp hf).prodMap contDiff_id).contMDiff
  intro z
  rcases lt_or_ge z.1 (2 / 3) with hz | hz
  · have hev : rectangleTrans u₁ u₂ =ᶠ[𝓝 z]
        u₁ ∘ Prod.map (fun s ↦ Real.smoothTransition (3 * s)) id :=
      (isOpen_lt continuous_fst continuous_const).eventually_mem hz |>.mono
        fun w hw ↦ rectangleTrans_eq_left h hw
    exact ((hu₁.comp (hL (f := fun s ↦ 3 * s) (by fun_prop))) z).congr_of_eventuallyEq hev
  · have hev : rectangleTrans u₁ u₂ =ᶠ[𝓝 z]
        u₂ ∘ Prod.map (fun s ↦ Real.smoothTransition (3 * s - 2)) id :=
      (isOpen_lt continuous_const continuous_fst).eventually_mem (by linarith : (1 / 3 : ℝ) < z.1)
        |>.mono fun w hw ↦ rectangleTrans_eq_right h hw
    exact ((hu₂.comp (hL (f := fun s ↦ 3 * s - 2) (by fun_prop))) z).congr_of_eventuallyEq hev

/-- **The integral over a concatenation.** For a continuous form and two `C¹` maps `u₁` and `u₂`
with `u₁ (1, ·) = u₂ (0, ·)`, the integral over `[0, 1] × [a₂, b₂]` of their concatenation is the
sum of the integrals of `u₁` and `u₂`. -/
theorem rectangleIntegral_rectangleTrans [IsManifold I 1 M] {φ : RoughForm I M F 2}
    (hφ : IsSmoothForm I 0 φ) {u₁ u₂ : ℝ × ℝ → M} (hu₁ : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u₁)
    (hu₂ : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u₂) (h : ∀ t, u₁ (1, t) = u₂ (0, t)) (a₂ b₂ : ℝ) :
    rectangleIntegral φ (rectangleTrans u₁ u₂) (0, a₂) (1, b₂) =
      rectangleIntegral φ u₁ (0, a₂) (1, b₂) + rectangleIntegral φ u₂ (0, a₂) (1, b₂) := by
  -- The two reparametrizations `s ↦ β (f s)`, for `f s = 3 s` and `f s = 3 s - 2`, are `C¹`.
  have hβ {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) : ContDiff ℝ 1 fun s ↦ Real.smoothTransition (f s) :=
    Real.smoothTransition.contDiff.comp hf
  rw [← rectangleIntegral_add_adjacent_fst hφ (contMDiff_rectangleTrans hu₁ hu₂ h) _ _ (1 / 2)]
  congr 1
  · -- On `[0, 1/2]` the concatenation is `u₁` reparametrized by `s ↦ β (3 s)`.
    rw [rectangleIntegral_congr fun z hz ↦ rectangleTrans_eq_left h (z := z) (by
        simp only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hz
        linarith [hz.1.2]),
      rectangleIntegral_comp_prodMap_of_contDiff hφ hu₁ (hβ (f := fun s ↦ 3 * s) (by fun_prop))]
    norm_num [Real.smoothTransition.one_of_one_le]
  · -- On `[1/2, 1]` it is `u₂` reparametrized by `s ↦ β (3 s - 2)`.
    rw [rectangleIntegral_congr fun z hz ↦ rectangleTrans_eq_right h (z := z) (by
        simp only [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)] at hz
        linarith [hz.1.1]),
      rectangleIntegral_comp_prodMap_of_contDiff hφ hu₂
        (hβ (f := fun s ↦ 3 * s - 2) (by fun_prop))]
    norm_num [Real.smoothTransition.zero_of_nonpos]

/-- **The integral over two maps glued along their common start.** For a continuous form and two
`C¹` maps `u` and `v` with `u (0, ·) = v (0, ·)`, the concatenation that runs backwards through
`u` and then forwards through `v` has the integral of `v` minus the integral of `u`. When `u`
and `v` are caps of the same loop, this concatenation is the sphere by which they differ. -/
theorem rectangleIntegral_rectangleTrans_comp_prodMap_one_sub [IsManifold I 1 M]
    {φ : RoughForm I M F 2} (hφ : IsSmoothForm I 0 φ) {u v : ℝ × ℝ → M}
    (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u) (hv : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 v)
    (h : ∀ t, u (0, t) = v (0, t)) (a₂ b₂ : ℝ) :
    rectangleIntegral φ (rectangleTrans (u ∘ Prod.map (fun s ↦ 1 - s) id) v) (0, a₂) (1, b₂) =
      rectangleIntegral φ v (0, a₂) (1, b₂) - rectangleIntegral φ u (0, a₂) (1, b₂) := by
  have hu' : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 (u ∘ Prod.map (fun s ↦ 1 - s) id) :=
    hu.comp ((contDiff_const.sub contDiff_id).prodMap contDiff_id).contMDiff
  rw [rectangleIntegral_rectangleTrans hφ hu' hv (fun t ↦ by simpa using h t),
    rectangleIntegral_comp_prodMap_one_sub hφ hu, neg_add_eq_sub]

/-! ### Concatenation along the second coordinate -/

/-- The loopwise concatenation of two maps `u₁ u₂ : ℝ × ℝ → M`: for each `s`, the loop that runs
through `t ↦ u₁ (s, t)` and then through `t ↦ u₂ (s, t)`, both over `t ∈ [0, 1]`. It is the curve
concatenation `TauCeti.curveConcat` of `r ↦ u₁ (s, β (2 r - 1))` and `r ↦ u₂ (s, β (2 r))`,
where `β = Real.smoothTransition`, evaluated at the fractional part of `t`. So on `[0, 1)` it is
`u₁ (s, β (6 t - 1))` for `t ≤ 1/2` and `u₂ (s, β (6 t - 4))` for `t > 1/2`, and it is
`1`-periodic in `t`. When `u₁ (s, 1) = u₂ (s, 0)` and
`u₂ (s, 1) = u₁ (s, 0)` for all `s`, it rests at these common points for `t` near `1/2` and near
the integers, so it is as smooth as `u₁` and `u₂` (`TauCeti.contMDiff_loopwiseTrans`). This is how
caps of two loops based at the same point are placed side by side, as a cap of their collared
concatenation (`Path.collaredTrans`). -/
def loopwiseTrans (u₁ u₂ : ℝ × ℝ → M) (z : ℝ × ℝ) : M :=
  curveConcat (fun r ↦ u₁ (z.1, Real.smoothTransition (2 * r - 1)))
    (fun r ↦ u₂ (z.1, Real.smoothTransition (2 * r))) (Int.fract z.2)

omit [TopologicalSpace M] in
/-- The loopwise concatenation is `1`-periodic in the second coordinate. -/
@[simp]
theorem loopwiseTrans_apply_add_one (u₁ u₂ : ℝ × ℝ → M) (s t : ℝ) :
    loopwiseTrans u₁ u₂ (s, t + 1) = loopwiseTrans u₁ u₂ (s, t) := by
  simp only [loopwiseTrans, Int.fract_add_one]

omit [TopologicalSpace M] in
/-- On `[0, 1/2]` the loopwise concatenation runs through the first map. -/
theorem loopwiseTrans_of_le (u₁ u₂ : ℝ × ℝ → M) {z : ℝ × ℝ} (h₀ : 0 ≤ z.2) (h : z.2 ≤ 1 / 2) :
    loopwiseTrans u₁ u₂ z = u₁ (z.1, Real.smoothTransition (6 * z.2 - 1)) := by
  rw [loopwiseTrans, Int.fract_eq_self.2 ⟨h₀, by linarith⟩, curveConcat_of_le (by linarith),
    ← mul_assoc]
  norm_num

omit [TopologicalSpace M] in
/-- On `(1/2, 1)` the loopwise concatenation runs through the second map. -/
theorem loopwiseTrans_of_lt (u₁ u₂ : ℝ × ℝ → M) {z : ℝ × ℝ} (h : 1 / 2 < z.2) (h₁ : z.2 < 1) :
    loopwiseTrans u₁ u₂ z = u₂ (z.1, Real.smoothTransition (6 * z.2 - 4)) := by
  rw [loopwiseTrans, Int.fract_eq_self.2 ⟨by linarith, h₁⟩, curveConcat_of_lt (by linarith),
    mul_sub, ← mul_assoc]
  norm_num

omit [TopologicalSpace M] in
/-- From `t = 1/3` up to `t = 1` the loopwise concatenation is a reparametrization of the second
map, if each map ends where the other starts. -/
theorem loopwiseTrans_eq_right {u₁ u₂ : ℝ × ℝ → M} (h₁ : ∀ s, u₁ (s, 1) = u₂ (s, 0))
    (h₂ : ∀ s, u₂ (s, 1) = u₁ (s, 0)) {z : ℝ × ℝ} (hz : z.2 ∈ Ioc (1 / 3) 1) :
    loopwiseTrans u₁ u₂ z = u₂ (z.1, Real.smoothTransition (6 * z.2 - 4)) := by
  obtain ⟨hz₁, hz₂⟩ := hz
  rcases hz₂.lt_or_eq with hz₂ | hz₂
  · -- From `t = 1/3` on, the concatenation is past the rest at the junction of the two maps.
    rw [loopwiseTrans, Int.fract_eq_self.2 ⟨by linarith, hz₂⟩,
      eqOn_curveConcat_right (y := u₁ (z.1, 1))
        (fun r hr ↦ by rw [Real.smoothTransition.one_of_one_le (by linarith)])
        (fun r hr ↦ by rw [Real.smoothTransition.zero_of_nonpos (by linarith), h₁]) hz₁]
    dsimp only
    congr 3
    ring
  · -- At `t = 1` it is back at the start of the first map, where the second map ends.
    rw [loopwiseTrans, hz₂, Int.fract_one, curveConcat_of_le (by norm_num),
      Real.smoothTransition.zero_of_nonpos (by norm_num),
      Real.smoothTransition.one_of_one_le (by norm_num), h₂]

omit [TopologicalSpace M] in
/-- The loopwise concatenation at `(s, t)` only depends on the two loops `r ↦ u₁ (s, r)` and
`r ↦ u₂ (s, r)` at parameters `r ∈ [0, 1]`. -/
theorem loopwiseTrans_congr {u₁ u₂ v₁ v₂ : ℝ × ℝ → M} {s s' t : ℝ}
    (h₁ : ∀ r ∈ Icc (0 : ℝ) 1, u₁ (s, r) = v₁ (s', r))
    (h₂ : ∀ r ∈ Icc (0 : ℝ) 1, u₂ (s, r) = v₂ (s', r)) :
    loopwiseTrans u₁ u₂ (s, t) = loopwiseTrans v₁ v₂ (s', t) := by
  rw [loopwiseTrans, loopwiseTrans]
  rcases le_or_gt (Int.fract t) 2⁻¹ with h | h
  · rw [curveConcat_of_le h, curveConcat_of_le h]
    exact h₁ _ ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  · rw [curveConcat_of_lt h, curveConcat_of_lt h]
    exact h₂ _ ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

omit [TopologicalSpace M] in
/-- The loopwise concatenation at `(s, t)` lies in a set `A` if the two loops `r ↦ u₁ (s, r)` and
`r ↦ u₂ (s, r)` lie in `A` at parameters `r ∈ [0, 1]`. -/
theorem loopwiseTrans_mem {u₁ u₂ : ℝ × ℝ → M} {A : Set M} {s t : ℝ}
    (h₁ : ∀ r ∈ Icc (0 : ℝ) 1, u₁ (s, r) ∈ A) (h₂ : ∀ r ∈ Icc (0 : ℝ) 1, u₂ (s, r) ∈ A) :
    loopwiseTrans u₁ u₂ (s, t) ∈ A := by
  rw [loopwiseTrans]
  rcases le_or_gt (Int.fract t) 2⁻¹ with h | h
  · rw [curveConcat_of_le h]
    exact h₁ _ ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  · rw [curveConcat_of_lt h]
    exact h₂ _ ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

omit [TopologicalSpace M] in
/-- A map applied to a loopwise concatenation is the loopwise concatenation of the composites. -/
theorem apply_loopwiseTrans {N : Type*} (f : M → N) (u₁ u₂ : ℝ × ℝ → M) (z : ℝ × ℝ) :
    f (loopwiseTrans u₁ u₂ z) = loopwiseTrans (f ∘ u₁) (f ∘ u₂) z := by
  rw [loopwiseTrans, loopwiseTrans]
  rcases le_or_gt (Int.fract z.2) 2⁻¹ with h | h
  · rw [curveConcat_of_le h, curveConcat_of_le h, Function.comp_apply]
  · rw [curveConcat_of_lt h, curveConcat_of_lt h, Function.comp_apply]

/-- The loopwise concatenation of two `C^n` maps, each ending where the other starts, is
`C^n`. -/
theorem contMDiff_loopwiseTrans {n : ℕ∞} {u₁ u₂ : ℝ × ℝ → M}
    (hu₁ : ContMDiff 𝓘(ℝ, ℝ × ℝ) I n u₁) (hu₂ : ContMDiff 𝓘(ℝ, ℝ × ℝ) I n u₂)
    (h₁ : ∀ s, u₁ (s, 1) = u₂ (s, 0)) (h₂ : ∀ s, u₂ (s, 1) = u₁ (s, 0)) :
    ContMDiff 𝓘(ℝ, ℝ × ℝ) I n (loopwiseTrans u₁ u₂) := by
  -- `loopwiseTrans u₁ u₂` is the periodization in `t` of the concatenation `G`, which near every
  -- point is a reparametrization of `u₁` or of `u₂`.
  let G : ℝ × ℝ → M := fun p ↦ curveConcat (fun r ↦ u₁ (p.1, Real.smoothTransition (2 * r - 1)))
    (fun r ↦ u₂ (p.1, Real.smoothTransition (2 * r))) p.2
  have hR {d : ℝ} : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) n
      (Prod.map (id : ℝ → ℝ) fun t ↦ Real.smoothTransition (6 * t - d)) :=
    (contDiff_id.prodMap (Real.smoothTransition.contDiff.comp (by fun_prop))).contMDiff
  have hrest₁ (s : ℝ) : ∀ r, 1 ≤ r → u₁ (s, Real.smoothTransition (2 * r - 1)) = u₁ (s, 1) :=
    fun r hr ↦ by rw [Real.smoothTransition.one_of_one_le (by linarith)]
  have hrest₂ (s : ℝ) : ∀ r ≤ 0, u₂ (s, Real.smoothTransition (2 * r)) = u₁ (s, 1) :=
    fun r hr ↦ by rw [Real.smoothTransition.zero_of_nonpos (by linarith), h₁]
  have hG : ContMDiff 𝓘(ℝ, ℝ × ℝ) I n G := by
    intro z
    rcases lt_or_ge z.2 (2 / 3) with hz | hz
    · refine ((hu₁.comp (hR (d := 1))) z).congr_of_eventuallyEq ?_
      filter_upwards [(isOpen_lt continuous_snd continuous_const).eventually_mem hz] with w hw
      refine (eqOn_curveConcat_left (hrest₁ w.1) (hrest₂ w.1) hw).trans ?_
      simp only [Function.comp_apply, Prod.map_apply', id, ← mul_assoc]
      norm_num
    · refine ((hu₂.comp (hR (d := 4))) z).congr_of_eventuallyEq ?_
      filter_upwards [(isOpen_lt continuous_const continuous_snd).eventually_mem
        (by linarith : (1 / 3 : ℝ) < z.2)] with w hw
      refine (eqOn_curveConcat_right (hrest₁ w.1) (hrest₂ w.1) hw).trans ?_
      simp only [Function.comp_apply, Prod.map_apply', id]
      congr 3
      ring
  refine contMDiff_prod_modelWithCornersSelf_iff.1 <|
    (contMDiff_prod_modelWithCornersSelf_iff.2 hG).comp_fract_snd (ε := 1 / 6) (by norm_num)
      fun s t ht₀ ht₁ ↦ ?_
  -- Just below `t = 0` the concatenation rests where `u₂` ends and `u₁` starts.
  simp only [G]
  rw [curveConcat_of_lt (by linarith), curveConcat_of_le (by linarith),
    Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.zero_of_nonpos (by linarith), h₂]

/-- **The integral over a loopwise concatenation.** For a continuous form and two `C¹` maps,
each ending where the other starts, the integral over `[a₁, b₁] × [0, 1]` of their loopwise
concatenation is the sum of the integrals of `u₁` and `u₂`. -/
theorem rectangleIntegral_loopwiseTrans [IsManifold I 1 M] {φ : RoughForm I M F 2}
    (hφ : IsSmoothForm I 0 φ) {u₁ u₂ : ℝ × ℝ → M} (hu₁ : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u₁)
    (hu₂ : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u₂) (h₁ : ∀ s, u₁ (s, 1) = u₂ (s, 0))
    (h₂ : ∀ s, u₂ (s, 1) = u₁ (s, 0)) (a₁ b₁ : ℝ) :
    rectangleIntegral φ (loopwiseTrans u₁ u₂) (a₁, 0) (b₁, 1) =
      rectangleIntegral φ u₁ (a₁, 0) (b₁, 1) + rectangleIntegral φ u₂ (a₁, 0) (b₁, 1) := by
  -- The two reparametrizations `t ↦ β (6 t - d)` are `C¹`.
  have hβ (d : ℝ) : ContDiff ℝ 1 fun t : ℝ ↦ Real.smoothTransition (6 * t - d) :=
    Real.smoothTransition.contDiff.comp (by fun_prop)
  have hsplit := rectangleIntegral_add_adjacent_snd hφ (contMDiff_loopwiseTrans hu₁ hu₂ h₁ h₂)
    (a₁, 0) (b₁, 1) (1 / 2)
  rw [← hsplit]
  congr 1
  · -- On `[0, 1/2]` the concatenation is `u₁` reparametrized by `t ↦ β (6 t - 1)`.
    rw [rectangleIntegral_congr (v := u₁ ∘ Prod.map id fun t ↦ Real.smoothTransition (6 * t - 1))
        fun z hz ↦ by
          simp only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hz
          exact loopwiseTrans_of_le u₁ u₂ hz.2.1 hz.2.2,
      rectangleIntegral_comp_prodMap_snd_of_contDiff hφ hu₁ (hβ 1)]
    norm_num [Real.smoothTransition.one_of_one_le, Real.smoothTransition.zero_of_nonpos]
  · -- On `[1/2, 1]` it is `u₂` reparametrized by `t ↦ β (6 t - 4)`.
    rw [rectangleIntegral_congr (v := u₂ ∘ Prod.map id fun t ↦ Real.smoothTransition (6 * t - 4))
        fun z hz ↦ by
          simp only [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)] at hz
          rw [Function.comp_apply, Prod.map_apply',
            loopwiseTrans_eq_right h₁ h₂ ⟨by linarith [hz.2.1], hz.2.2⟩, id],
      rectangleIntegral_comp_prodMap_snd_of_contDiff hφ hu₂ (hβ 4)]
    norm_num [Real.smoothTransition.one_of_one_le, Real.smoothTransition.zero_of_nonpos]

/-! ### Seamed cylinders and cylinders -/

variable (I) in
/-- A smooth `f`-seamed cylinder from the path `γ` to the path `γ₀`: a smooth map
`u : ℝ × ℝ → M` running along `γ` at `s = 0` and along `γ₀` at `s = 1`, each path being traversed
over `t ∈ [0, 1]`, with `u (s, 1) = f (u (s, 0))` for `s ∈ [0, 1]`, so that every `u (s, ·)` is an
`f`-seamed path (`TauCeti.SeamedPath`). The start is prescribed for all `t`, so that two seamed
cylinders from the same path can be glued smoothly along it; the other conditions only concern the
unit square. For `f = id` these are the smooth cylinders `TauCeti.IsSmoothCylinder`. -/
structure IsSmoothSeamedCylinder (f : M → M) (γ γ₀ : ℝ → M) (u : ℝ × ℝ → M) : Prop where
  contMDiff : ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ u
  apply_zero (t : ℝ) : u (0, t) = γ t
  apply_one : ∀ t ∈ Icc (0 : ℝ) 1, u (1, t) = γ₀ t
  seam : ∀ s ∈ Icc (0 : ℝ) 1, u (s, 1) = f (u (s, 0))

variable (I) in
/-- A smooth cylinder from the loop `γ` to the loop `γ₀`: a smooth map `u : ℝ × ℝ → M` running
along `γ` at `s = 0` and along `γ₀` at `s = 1`, each loop being traversed over `t ∈ [0, 1]`,
with `u (s, 1) = u (s, 0)` for `s ∈ [0, 1]`: a smooth `id`-seamed cylinder. The start is
prescribed for all `t`, so that two cylinders from the same loop can be glued smoothly along it;
the other conditions only concern the unit square. When `γ₀` is constant, `u` is a cap of `γ`. -/
def IsSmoothCylinder (γ γ₀ : ℝ → M) (u : ℝ × ℝ → M) : Prop :=
  IsSmoothSeamedCylinder I id γ γ₀ u

section Seamed

variable {f : M → M} {γ γ' γ₀ : ℝ → M} {u u₁ u₂ : ℝ × ℝ → M}

/-- **Seamed cylinders for the identity are cylinders.** -/
@[simp]
theorem isSmoothSeamedCylinder_id_iff :
    IsSmoothSeamedCylinder I id γ γ₀ u ↔ IsSmoothCylinder I γ γ₀ u :=
  Iff.rfl

/-- A smooth cylinder is smooth. -/
theorem IsSmoothCylinder.contMDiff (hu : IsSmoothCylinder I γ γ₀ u) :
    ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ u :=
  IsSmoothSeamedCylinder.contMDiff hu

/-- A smooth cylinder from `γ` runs along `γ` at `s = 0`. -/
theorem IsSmoothCylinder.apply_zero (hu : IsSmoothCylinder I γ γ₀ u) (t : ℝ) : u (0, t) = γ t :=
  IsSmoothSeamedCylinder.apply_zero hu t

/-- A smooth cylinder to `γ₀` runs along `γ₀` at `s = 1`, for `t ∈ [0, 1]`. -/
theorem IsSmoothCylinder.apply_one (hu : IsSmoothCylinder I γ γ₀ u) :
    ∀ t ∈ Icc (0 : ℝ) 1, u (1, t) = γ₀ t :=
  IsSmoothSeamedCylinder.apply_one hu

/-- Every loop `u (s, ·)`, `s ∈ [0, 1]`, of a smooth cylinder closes up at `t = 1`. -/
theorem IsSmoothCylinder.periodic (hu : IsSmoothCylinder I γ γ₀ u) :
    ∀ s ∈ Icc (0 : ℝ) 1, u (s, 1) = u (s, 0) :=
  IsSmoothSeamedCylinder.seam hu

/-- Constructing a smooth cylinder from its smoothness, its two ends and the closing condition
`u (s, 1) = u (s, 0)` of its loops. -/
theorem IsSmoothCylinder.mk (contMDiff : ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ u)
    (apply_zero : ∀ t, u (0, t) = γ t) (apply_one : ∀ t ∈ Icc (0 : ℝ) 1, u (1, t) = γ₀ t)
    (periodic : ∀ s ∈ Icc (0 : ℝ) 1, u (s, 1) = u (s, 0)) : IsSmoothCylinder I γ γ₀ u :=
  ⟨contMDiff, apply_zero, apply_one, periodic⟩

/-- The initial path of an `f`-seamed cylinder is `f`-seamed. -/
theorem IsSmoothSeamedCylinder.source_apply_one (hu : IsSmoothSeamedCylinder I f γ γ₀ u) :
    γ 1 = f (γ 0) := by
  simpa only [hu.apply_zero] using hu.seam 0 (left_mem_Icc.mpr zero_le_one)

/-- The final path of an `f`-seamed cylinder is `f`-seamed. -/
theorem IsSmoothSeamedCylinder.target_apply_one (hu : IsSmoothSeamedCylinder I f γ γ₀ u) :
    γ₀ 1 = f (γ₀ 0) := by
  have h₀ : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := left_mem_Icc.mpr zero_le_one
  have h₁ : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := right_mem_Icc.mpr zero_le_one
  rw [← hu.apply_one 1 h₁, ← hu.apply_one 0 h₀]
  exact hu.seam 1 h₁

/-- The concatenation of a smooth `f`-seamed cylinder from `γ` to `γ'` and a smooth `f`-seamed
cylinder from `γ'` to `γ₀`, sharing their common edge for every `t`, is a smooth `f`-seamed
cylinder from `γ` to `γ₀`. -/
theorem IsSmoothSeamedCylinder.trans (h₁ : IsSmoothSeamedCylinder I f γ γ' u₁)
    (h₂ : IsSmoothSeamedCylinder I f γ' γ₀ u₂) (h : ∀ t, u₁ (1, t) = u₂ (0, t)) :
    IsSmoothSeamedCylinder I f γ γ₀ (rectangleTrans u₁ u₂) where
  contMDiff := contMDiff_rectangleTrans h₁.contMDiff h₂.contMDiff h
  apply_zero t := by rw [rectangleTrans_apply_zero, h₁.apply_zero]
  apply_one t ht := by rw [rectangleTrans_apply_one, h₂.apply_one t ht]
  seam s _ := by
    -- Near each `s` the concatenation is one of the two maps, reparametrized in the first
    -- coordinate by `smoothTransition`, which takes values in `[0, 1]`.
    have hβ (r : ℝ) : Real.smoothTransition r ∈ Icc (0 : ℝ) 1 :=
      ⟨Real.smoothTransition.nonneg r, Real.smoothTransition.le_one r⟩
    rcases lt_or_ge s (2 / 3) with hs | hs
    · rw [rectangleTrans_eq_left h (z := (s, 1)) hs, rectangleTrans_eq_left h (z := (s, 0)) hs]
      exact h₁.seam _ (hβ _)
    · have hs' : (1 / 3 : ℝ) < s := by linarith
      rw [rectangleTrans_eq_right h (z := (s, 1)) hs', rectangleTrans_eq_right h (z := (s, 0)) hs']
      exact h₂.seam _ (hβ _)

/-- Reversing the first coordinate of a smooth `f`-seamed cylinder from `γ` gives a smooth
`f`-seamed cylinder from its final edge `u (1, ·)` back to `γ`. -/
theorem IsSmoothSeamedCylinder.comp_prodMap_one_sub (hu : IsSmoothSeamedCylinder I f γ γ₀ u) :
    IsSmoothSeamedCylinder I f (fun t ↦ u (1, t)) γ (u ∘ Prod.map (fun s ↦ 1 - s) id) where
  contMDiff := hu.contMDiff.comp ((contDiff_const.sub contDiff_id).prodMap contDiff_id).contMDiff
  apply_zero t := by simp
  apply_one t _ := by simp [hu.apply_zero]
  seam s hs := by simpa using hu.seam (1 - s) ⟨by linarith [hs.2], by linarith [hs.1]⟩

/-- Rescaling the first coordinate from `[0, 1]` to `[a, b]` turns a smooth family `u` of
`f`-seamed paths `u (s, ·)` into a smooth `f`-seamed cylinder from `u (a, ·)` to `u (b, ·)`. -/
theorem isSmoothSeamedCylinder_comp_prodMap_affine (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ u)
    (hseam : ∀ s, u (s, 1) = f (u (s, 0))) (a b : ℝ) :
    IsSmoothSeamedCylinder I f (fun t ↦ u (a, t)) (fun t ↦ u (b, t))
      (u ∘ Prod.map (fun s ↦ a + (b - a) * s) id) where
  contMDiff := hu.comp (contMDiff_prodMap_affine a b)
  apply_zero t := by simp
  apply_one t _ := by simp
  seam s _ := by simpa using hseam (a + (b - a) * s)

end Seamed

/-- The concatenation of a smooth cylinder from `γ` to `γ'` and a smooth cylinder from `γ'` to
`γ₀`, sharing their common edge for every `t`, is a smooth cylinder from `γ` to `γ₀`. -/
theorem IsSmoothCylinder.trans {γ γ' γ₀ : ℝ → M} {u₁ u₂ : ℝ × ℝ → M}
    (h₁ : IsSmoothCylinder I γ γ' u₁) (h₂ : IsSmoothCylinder I γ' γ₀ u₂)
    (h : ∀ t, u₁ (1, t) = u₂ (0, t)) : IsSmoothCylinder I γ γ₀ (rectangleTrans u₁ u₂) :=
  isSmoothSeamedCylinder_id_iff.mp
    ((isSmoothSeamedCylinder_id_iff.mpr h₁).trans (isSmoothSeamedCylinder_id_iff.mpr h₂) h)

/-- Reversing the first coordinate of a smooth cylinder from `γ` gives a smooth cylinder from its
final edge `u (1, ·)` back to `γ`. -/
theorem IsSmoothCylinder.comp_prodMap_one_sub {γ γ₀ : ℝ → M} {u : ℝ × ℝ → M}
    (hu : IsSmoothCylinder I γ γ₀ u) :
    IsSmoothCylinder I (fun t ↦ u (1, t)) γ (u ∘ Prod.map (fun s ↦ 1 - s) id) :=
  isSmoothSeamedCylinder_id_iff.mp (isSmoothSeamedCylinder_id_iff.mpr hu).comp_prodMap_one_sub

/-- Rescaling the first coordinate from `[0, 1]` to `[a, b]` turns a smooth map `u : ℝ × ℝ → M`,
`1`-periodic in `t`, into a smooth cylinder from the loop `u(a, ·)` to the loop `u(b, ·)`. -/
theorem isSmoothCylinder_comp_prodMap_affine {u : ℝ × ℝ → M}
    (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ u) (hper : ∀ z : ℝ × ℝ, u (z.1, z.2 + 1) = u z)
    (a b : ℝ) :
    IsSmoothCylinder I (fun t ↦ u (a, t)) (fun t ↦ u (b, t))
      (u ∘ Prod.map (fun s ↦ a + (b - a) * s) id) :=
  isSmoothSeamedCylinder_id_iff.mp
    (isSmoothSeamedCylinder_comp_prodMap_affine hu (fun s ↦ by simpa using hper (s, 0)) a b)

/-- A two-form `φ` **vanishes on spheres** when its integral over the unit square vanishes for
every smooth map `u : ℝ × ℝ → M` that is constant on each of the two vertical edges of the square
and agrees on its two horizontal edges. Such a map factors through the sphere obtained from the
square by collapsing the vertical edges and identifying the horizontal ones; composing a smooth
map of the round sphere with spherical coordinates gives such a map. For a symplectic form this
formulates the area condition of symplectic asphericity on maps of the square. -/
def VanishesOnSpheres (φ : RoughForm I M F 2) : Prop :=
  ∀ u : ℝ × ℝ → M, ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ u →
    (∀ t ∈ Icc (0 : ℝ) 1, u (0, t) = u (0, 0)) → (∀ t ∈ Icc (0 : ℝ) 1, u (1, t) = u (1, 0)) →
    (∀ s ∈ Icc (0 : ℝ) 1, u (s, 1) = u (s, 0)) → rectangleIntegral φ u (0, 0) (1, 1) = 0

/-- A two-form `φ` **vanishes on `f`-seamed tori** when its integral over the unit square
vanishes for every smooth map `u : ℝ × ℝ → M` that agrees on the two vertical edges of the square
and maps its bottom edge to its top edge by `f`, `u (s, 1) = f (u (s, 0))`. Such a map is the
torus swept out by a loop `s ↦ u (s, ·)` of `f`-seamed paths. For `f = id` this is
`TauCeti.VanishesOnTori`. -/
def VanishesOnSeamedTori (f : M → M) (φ : RoughForm I M F 2) : Prop :=
  ∀ u : ℝ × ℝ → M, ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ u →
    (∀ t ∈ Icc (0 : ℝ) 1, u (1, t) = u (0, t)) →
    (∀ s ∈ Icc (0 : ℝ) 1, u (s, 1) = f (u (s, 0))) → rectangleIntegral φ u (0, 0) (1, 1) = 0

/-- A two-form `φ` **vanishes on tori** when its integral over the unit square vanishes for every
smooth map `u : ℝ × ℝ → M` that agrees on opposite edges of the square, so that it factors
through the torus: it vanishes on `id`-seamed tori. For a symplectic form this formulates the
area condition of symplectic atoroidality on maps of the square. -/
def VanishesOnTori (φ : RoughForm I M F 2) : Prop :=
  VanishesOnSeamedTori id φ

/-- Unfolding `TauCeti.VanishesOnSpheres`. -/
theorem vanishesOnSpheres_iff (φ : RoughForm I M F 2) :
    VanishesOnSpheres φ ↔ ∀ u : ℝ × ℝ → M, ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ u →
      (∀ t ∈ Icc (0 : ℝ) 1, u (0, t) = u (0, 0)) → (∀ t ∈ Icc (0 : ℝ) 1, u (1, t) = u (1, 0)) →
      (∀ s ∈ Icc (0 : ℝ) 1, u (s, 1) = u (s, 0)) → rectangleIntegral φ u (0, 0) (1, 1) = 0 :=
  Iff.rfl

/-- Unfolding `TauCeti.VanishesOnTori`. -/
theorem vanishesOnTori_iff (φ : RoughForm I M F 2) :
    VanishesOnTori φ ↔ ∀ u : ℝ × ℝ → M, ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ u →
      (∀ t ∈ Icc (0 : ℝ) 1, u (1, t) = u (0, t)) →
      (∀ s ∈ Icc (0 : ℝ) 1, u (s, 1) = u (s, 0)) → rectangleIntegral φ u (0, 0) (1, 1) = 0 :=
  Iff.rfl

/-- Unfolding `TauCeti.VanishesOnSeamedTori`. -/
theorem vanishesOnSeamedTori_iff (f : M → M) (φ : RoughForm I M F 2) :
    VanishesOnSeamedTori f φ ↔ ∀ u : ℝ × ℝ → M, ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ u →
      (∀ t ∈ Icc (0 : ℝ) 1, u (1, t) = u (0, t)) →
      (∀ s ∈ Icc (0 : ℝ) 1, u (s, 1) = f (u (s, 0))) → rectangleIntegral φ u (0, 0) (1, 1) = 0 :=
  Iff.rfl

/-- **Vanishing on seamed tori for the identity is vanishing on tori.** -/
@[simp]
theorem vanishesOnSeamedTori_id_iff (φ : RoughForm I M F 2) :
    VanishesOnSeamedTori id φ ↔ VanishesOnTori φ :=
  Iff.rfl

/-! ### Independence of the cylinder -/

section Independence

variable [IsManifold I 1 M] {φ : RoughForm I M F 2} {γ γ₀ : ℝ → M}
  {u v : ℝ × ℝ → M}

/-- **Independence of the cap.** A continuous two-form that vanishes on spheres has the same
integral over any two caps of a loop, even if they end at different points. -/
theorem VanishesOnSpheres.rectangleIntegral_eq (hS : VanishesOnSpheres φ)
    (hφ : IsSmoothForm I 0 φ) {x y : M} (hu : IsSmoothCylinder I γ (fun _ ↦ x) u)
    (hv : IsSmoothCylinder I γ (fun _ ↦ y) v) :
    rectangleIntegral φ u (0, 0) (1, 1) = rectangleIntegral φ v (0, 0) (1, 1) := by
  -- Glue `u`, run backwards, to `v` along `γ`: this is a sphere, with integral `∫ v - ∫ u`.
  have h t : u (0, t) = v (0, t) := (hu.apply_zero t).trans (hv.apply_zero t).symm
  have hw := hu.comp_prodMap_one_sub.trans hv fun t ↦ by simpa using h t
  have h₀ : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := left_mem_Icc.mpr zero_le_one
  have hglue := hS _ hw.contMDiff
    (fun t ht ↦ by rw [hw.apply_zero, hw.apply_zero, hu.apply_one t ht, hu.apply_one 0 h₀])
    (fun t ht ↦ by rw [hw.apply_one t ht, hw.apply_one 0 h₀]) hw.periodic
  rw [rectangleIntegral_rectangleTrans_comp_prodMap_one_sub hφ (hu.contMDiff.of_le (by simp))
    (hv.contMDiff.of_le (by simp)) h, sub_eq_zero] at hglue
  exact hglue.symm

/-- **Independence of the seamed cylinder.** A continuous two-form that vanishes on `f`-seamed
tori has the same integral over any two `f`-seamed cylinders from a path `γ` to a path `γ₀`. -/
theorem VanishesOnSeamedTori.rectangleIntegral_eq {f : M → M} (hT : VanishesOnSeamedTori f φ)
    (hφ : IsSmoothForm I 0 φ) (hu : IsSmoothSeamedCylinder I f γ γ₀ u)
    (hv : IsSmoothSeamedCylinder I f γ γ₀ v) :
    rectangleIntegral φ u (0, 0) (1, 1) = rectangleIntegral φ v (0, 0) (1, 1) := by
  -- Glue `u`, run backwards, to `v` along `γ`: this is a seamed torus, with integral `∫ v - ∫ u`.
  have h t : u (0, t) = v (0, t) := (hu.apply_zero t).trans (hv.apply_zero t).symm
  have hw := hu.comp_prodMap_one_sub.trans hv fun t ↦ by simpa using h t
  have hglue := hT _ hw.contMDiff
    (fun t ht ↦ by rw [hw.apply_one t ht, hw.apply_zero, hu.apply_one t ht]) hw.seam
  rw [rectangleIntegral_rectangleTrans_comp_prodMap_one_sub hφ (hu.contMDiff.of_le (by simp))
    (hv.contMDiff.of_le (by simp)) h, sub_eq_zero] at hglue
  exact hglue.symm

/-- **Independence of the cylinder.** A continuous two-form that vanishes on tori has the same
integral over any two cylinders from a loop `γ` to a loop `γ₀`. -/
theorem VanishesOnTori.rectangleIntegral_eq (hT : VanishesOnTori φ) (hφ : IsSmoothForm I 0 φ)
    (hu : IsSmoothCylinder I γ γ₀ u) (hv : IsSmoothCylinder I γ γ₀ v) :
    rectangleIntegral φ u (0, 0) (1, 1) = rectangleIntegral φ v (0, 0) (1, 1) :=
  ((vanishesOnSeamedTori_id_iff φ).mpr hT).rectangleIntegral_eq hφ
    (isSmoothSeamedCylinder_id_iff.mpr hu) (isSmoothSeamedCylinder_id_iff.mpr hv)

end Independence

/-! ### Exact forms -/

section Exact

variable [IsManifold I 2 M] {α : RoughForm I M F 1}

/-- Exact two-forms vanish on spheres: by Stokes' formula the integral over a sphere is the sum
of the line integrals along its edges, which vanish on the collapsed vertical edges and cancel on
the identified horizontal ones. -/
theorem vanishesOnSpheres_mextDeriv (hα : IsSmoothForm I 1 α) :
    VanishesOnSpheres (mextDeriv α) := by
  intro u hu h₀ h₁ hp
  have hI : uIoo (0 : ℝ) 1 ⊆ Icc 0 1 := by
    rw [uIoo_of_le zero_le_one]
    exact Ioo_subset_Icc_self
  rw [rectangleIntegral_mextDeriv hα (hu.of_le (by simp))]
  dsimp only
  rw [pathIntegral_congr_of_eqOn_uIoo (γ := fun t ↦ u (1, t)) (γ' := fun _ ↦ u (1, 0))
      fun t ht ↦ h₁ t (hI ht),
    pathIntegral_congr_of_eqOn_uIoo (γ := fun t ↦ u (0, t)) (γ' := fun _ ↦ u (0, 0))
      fun t ht ↦ h₀ t (hI ht),
    pathIntegral_congr_of_eqOn_uIoo (γ := fun s ↦ u (s, 1)) (γ' := fun s ↦ u (s, 0))
      fun s hs ↦ hp s (hI hs)]
  simp

/-- **Exact forms with an invariant primitive vanish on seamed tori.** If `f` is differentiable
and preserves the `C¹` one-form `α`, `f^* α = α`, then `dα` vanishes on `f`-seamed tori: by
Stokes' formula the integral over a seamed torus is the sum of the line integrals of `α` along
its edges, which cancel on the two vertical edges, and on the two horizontal edges since one is
the image of the other under `f`. -/
theorem vanishesOnSeamedTori_mextDeriv (hα : IsSmoothForm I 1 α) {f : M → M}
    (hf : MDifferentiable I I f) (hfα : mpullback I I f α = α) :
    VanishesOnSeamedTori f (mextDeriv α) := by
  intro u hu h₁ hseam
  have hI : uIoo (0 : ℝ) 1 ⊆ Icc 0 1 := by
    rw [uIoo_of_le zero_le_one]
    exact Ioo_subset_Icc_self
  -- the line integral along the top edge is that of `f^* α = α` along the bottom edge
  have htop : pathIntegral α (fun s ↦ u (s, 1)) 0 1 = pathIntegral α (fun s ↦ u (s, 0)) 0 1 := by
    have hbot : ContMDiff 𝓘(ℝ, ℝ) I ∞ fun s ↦ u (s, 0) :=
      hu.comp (contDiff_id.prodMk contDiff_const).contMDiff
    rw [pathIntegral_congr_of_eqOn_uIoo (γ' := f ∘ fun s ↦ u (s, 0))
        fun s hs ↦ hseam s (hI hs),
      ← pathIntegral_mpullback (a := 0) (b := 1) α (fun _ _ ↦ hf _)
        fun _ _ ↦ hbot.mdifferentiableAt (by simp), hfα]
  rw [rectangleIntegral_mextDeriv hα (hu.of_le (by simp))]
  dsimp only
  rw [pathIntegral_congr_of_eqOn_uIoo (γ := fun t ↦ u (1, t)) (γ' := fun t ↦ u (0, t))
      fun t ht ↦ h₁ t (hI ht), htop]
  simp

/-- Exact two-forms vanish on tori: by Stokes' formula the integral over a torus is the sum of the
line integrals along its edges, which cancel on opposite edges. -/
theorem vanishesOnTori_mextDeriv (hα : IsSmoothForm I 1 α) : VanishesOnTori (mextDeriv α) :=
  (vanishesOnSeamedTori_id_iff _).mp
    (vanishesOnSeamedTori_mextDeriv hα mdifferentiable_id (mpullback_id α))

end Exact

end TauCeti
