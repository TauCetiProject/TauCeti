/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Homotopy
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Two-forms vanishing on spheres and tori, and integrals over cylinders

A *smooth cylinder* from a loop `γ` to a loop `γ₀` in a manifold `M` is a smooth map
`u : ℝ × ℝ → M` with `u (0, t) = γ t`, `u (1, t) = γ₀ t` and `u (s, 1) = u (s, 0)`, the last two
on the unit interval (`TauCeti.IsSmoothCylinder`). When `γ₀` is constant, `u` is a *cap* of `γ`.
Cylinders are the reference surfaces of the Hamiltonian action functional, whose area term is
the integral `∫ u^* ω` of the symplectic form over a cylinder from a loop to a reference loop in
its free homotopy class, or over a cap of a contractible loop.

The integral of a two-form `φ` over a cylinder depends on the cylinder in general. It only depends
on the loops when `φ` integrates to zero over every smooth sphere (for caps) or over every smooth
torus (for cylinders between two given loops). Here a smooth sphere is presented as a smooth map
of the unit square that is constant on each vertical edge and agrees on the two horizontal edges;
it factors through the quotient of the square collapsing the vertical edges and identifying the
horizontal ones, which is a sphere. Composing a smooth map of the round sphere with spherical
coordinates gives such a map. Likewise a smooth torus is a smooth map of the square agreeing on
opposite edges. These are the conditions `TauCeti.VanishesOnSpheres` and `TauCeti.VanishesOnTori`.
For a symplectic form they formulate the area conditions of symplectic asphericity and
atoroidality on maps of the square, the parametrization in which caps and cylinders are
integrated.

The independence of the cylinder (`TauCeti.VanishesOnSpheres.rectangleIntegral_eq`,
`TauCeti.VanishesOnTori.rectangleIntegral_eq`) is proved by gluing: two cylinders `u` and `v`
from the same loop, reparametrized to rest on that loop near the seam, glue to a smooth sphere or
torus whose integral is `∫ v^* φ - ∫ u^* φ`. Exact forms vanish on spheres and tori
(`TauCeti.vanishesOnSpheres_mextDeriv`, `TauCeti.vanishesOnTori_mextDeriv`), by Stokes' formula
`TauCeti.rectangleIntegral_mextDeriv`; this covers exact symplectic manifolds such as Liouville
domains and cotangent bundles.

## Main definitions

* `TauCeti.IsSmoothCylinder I γ γ₀ u`: `u` is a smooth cylinder from the loop `γ` to the loop
  `γ₀`.
* `TauCeti.VanishesOnSpheres φ`: the two-form `φ` integrates to zero over every smooth sphere.
* `TauCeti.VanishesOnTori φ`: the two-form `φ` integrates to zero over every smooth torus.

## Main results

* `TauCeti.VanishesOnSpheres.rectangleIntegral_eq`: a form vanishing on spheres has the same
  integral over any two caps of a loop.
* `TauCeti.VanishesOnTori.rectangleIntegral_eq`: a form vanishing on tori has the same integral
  over any two cylinders between the same two loops.
* `TauCeti.vanishesOnSpheres_mextDeriv`, `TauCeti.vanishesOnTori_mextDeriv`: exact forms vanish on
  spheres and tori.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS, 2012,
  the chapter on Floer homology (the symplectic action and its dependence on the cylinder).
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 1 (the action functional on contractible loops of a symplectically
  aspherical manifold).
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §3.2 (asphericity, atoroidality and the
  action functional relative to reference loops).
-/

public section

noncomputable section

open Set Real
open scoped Manifold Interval ContDiff Topology

namespace TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

variable (I) in
/-- A smooth cylinder from the loop `γ` to the loop `γ₀`: a smooth map `u : ℝ × ℝ → M` running
along `γ` at `s = 0` and along `γ₀` at `s = 1`, each loop being traversed over `t ∈ [0, 1]`,
with `u (s, 1) = u (s, 0)` for `s ∈ [0, 1]`. The start is prescribed for all `t`, so that two
cylinders from the same loop can be glued smoothly along it; the other conditions only concern
the unit square. When `γ₀` is constant, `u` is a cap of `γ`. -/
structure IsSmoothCylinder (γ γ₀ : ℝ → M) (u : ℝ × ℝ → M) : Prop where
  contMDiff : ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ u
  apply_zero (t : ℝ) : u (0, t) = γ t
  apply_one : ∀ t ∈ Icc (0 : ℝ) 1, u (1, t) = γ₀ t
  periodic : ∀ s ∈ Icc (0 : ℝ) 1, u (s, 1) = u (s, 0)

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

/-- A two-form `φ` **vanishes on tori** when its integral over the unit square vanishes for every
smooth map `u : ℝ × ℝ → M` that agrees on opposite edges of the square, so that it factors
through the torus. For a symplectic form this formulates the area condition of symplectic
atoroidality on maps of the square. -/
def VanishesOnTori (φ : RoughForm I M F 2) : Prop :=
  ∀ u : ℝ × ℝ → M, ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ u →
    (∀ t ∈ Icc (0 : ℝ) 1, u (1, t) = u (0, t)) →
    (∀ s ∈ Icc (0 : ℝ) 1, u (s, 1) = u (s, 0)) → rectangleIntegral φ u (0, 0) (1, 1) = 0

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

/-! ### Gluing two cylinders along their common start -/

section Glue

variable {X : Type*} {u v : ℝ × ℝ → X}

/-- The map gluing `u` and `v` along their common start: on `[0, 1/2]` it runs backwards
through `u`, and on `[1/2, 1]` forwards through `v`, each reparametrized by a smooth transition
so that the glued map rests on the common loop for `s ∈ [1/3, 2/3]`. -/
private def glue (u v : ℝ × ℝ → X) (z : ℝ × ℝ) : X :=
  if z.1 ≤ 1 / 2 then u (smoothTransition (-3 * z.1 + 1), z.2)
  else v (smoothTransition (3 * z.1 + -2), z.2)

private theorem glue_of_le {z : ℝ × ℝ} (hz : z.1 ≤ 1 / 2) :
    glue u v z = u (smoothTransition (-3 * z.1 + 1), z.2) := by
  simp only [glue, hz, ↓reduceIte]

private theorem glue_of_gt {z : ℝ × ℝ} (hz : 1 / 2 < z.1) :
    glue u v z = v (smoothTransition (3 * z.1 + -2), z.2) := by
  simp only [glue, hz.not_ge, ↓reduceIte]

private theorem glue_eq_left (h : ∀ t, u (0, t) = v (0, t)) {z : ℝ × ℝ} (hz : z.1 < 2 / 3) :
    glue u v z = u (smoothTransition (-3 * z.1 + 1), z.2) := by
  rcases le_or_gt z.1 (1 / 2) with hz' | hz'
  · exact glue_of_le hz'
  · rw [glue_of_gt hz', smoothTransition.zero_of_nonpos (by linarith),
      smoothTransition.zero_of_nonpos (by linarith), h]

private theorem glue_eq_right (h : ∀ t, u (0, t) = v (0, t)) {z : ℝ × ℝ} (hz : 1 / 3 < z.1) :
    glue u v z = v (smoothTransition (3 * z.1 + -2), z.2) := by
  rcases le_or_gt z.1 (1 / 2) with hz' | hz'
  · rw [glue_of_le hz', smoothTransition.zero_of_nonpos (by linarith),
      smoothTransition.zero_of_nonpos (by linarith), h]
  · exact glue_of_gt hz'

private theorem glue_zero (t : ℝ) : glue u v (0, t) = u (1, t) := by
  rw [glue_of_le (by norm_num)]
  norm_num

private theorem glue_one (t : ℝ) : glue u v (1, t) = v (1, t) := by
  rw [glue_of_gt (by norm_num)]
  norm_num

private theorem glue_periodic (hu : ∀ s ∈ Icc (0 : ℝ) 1, u (s, 1) = u (s, 0))
    (hv : ∀ s ∈ Icc (0 : ℝ) 1, v (s, 1) = v (s, 0)) (s : ℝ) :
    glue u v (s, 1) = glue u v (s, 0) := by
  simp only [glue]
  split_ifs
  · exact hu _ ⟨smoothTransition.nonneg _, smoothTransition.le_one _⟩
  · exact hv _ ⟨smoothTransition.nonneg _, smoothTransition.le_one _⟩

/-- The reparametrizations used in the gluing are smooth. -/
private theorem contDiff_smoothTransition_affine {n : ℕ∞} (c d : ℝ) :
    ContDiff ℝ n fun s : ℝ ↦ smoothTransition (c * s + d) :=
  smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).add contDiff_const)

variable {u v : ℝ × ℝ → M}

private theorem contMDiff_glue {n : ℕ∞} (h : ∀ t, u (0, t) = v (0, t))
    (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I n u) (hv : ContMDiff 𝓘(ℝ, ℝ × ℝ) I n v) :
    ContMDiff 𝓘(ℝ, ℝ × ℝ) I n (glue u v) := by
  -- Near a point with `s < 2/3` the glued map is a reparametrization of `u`, and near a point
  -- with `s > 1/3` it is a reparametrization of `v`.
  have hcomp {w : ℝ × ℝ → M} (hw : ContMDiff 𝓘(ℝ, ℝ × ℝ) I n w) (c d : ℝ) :
      ContMDiff 𝓘(ℝ, ℝ × ℝ) I n fun z : ℝ × ℝ ↦ w (smoothTransition (c * z.1 + d), z.2) :=
    hw.comp (((contDiff_smoothTransition_affine c d).comp contDiff_fst).prodMk
      contDiff_snd).contMDiff
  intro z
  rcases lt_or_ge z.1 (2 / 3) with hz | hz
  · refine (hcomp hu (-3) 1 z).congr_of_eventuallyEq ?_
    filter_upwards [(isOpen_lt continuous_fst continuous_const).mem_nhds hz] with w hw
    exact glue_eq_left h hw
  · have hz' : (1 / 3 : ℝ) < z.1 := by linarith
    refine (hcomp hv 3 (-2) z).congr_of_eventuallyEq ?_
    filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds hz'] with w hw
    exact glue_eq_right h hw

/-- The integral over the glued map is the integral over `v` minus the integral over `u`. -/
private theorem rectangleIntegral_glue [IsManifold I 1 M]
    {φ : RoughForm I M F 2} (hφ : IsSmoothForm I 0 φ) (h : ∀ t, u (0, t) = v (0, t))
    (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u) (hv : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 v) :
    rectangleIntegral φ (glue u v) (0, 0) (1, 1) =
      rectangleIntegral φ v (0, 0) (1, 1) - rectangleIntegral φ u (0, 0) (1, 1) := by
  -- A reparametrization `s ↦ smoothTransition (c * s + d)` of the first coordinate.
  have hreparam {w : ℝ × ℝ → M} (hw : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 w) (c d : ℝ) (a b : ℝ × ℝ) :
      rectangleIntegral φ (w ∘ Prod.map (fun s ↦ smoothTransition (c * s + d)) id) a b =
        rectangleIntegral φ w (smoothTransition (c * a.1 + d), a.2)
          (smoothTransition (c * b.1 + d), b.2) :=
    rectangleIntegral_comp_prodMap hφ hw
      (fun s _ ↦ ((contDiff_smoothTransition_affine (n := 1) c d).differentiable
        one_ne_zero s).hasDerivAt)
      ((contDiff_smoothTransition_affine (n := 1) c d).continuous_deriv le_rfl).continuousOn
  rw [← rectangleIntegral_add_adjacent hφ (contMDiff_glue h hu hv) (0, 0) (1 / 2) (1, 1)]
  -- On `[0, 1/2]` the glued map runs backwards through `u`, on `[1/2, 1]` forwards through `v`.
  have hl : rectangleIntegral φ (glue u v) (0, 0) (1 / 2, 1) =
      -rectangleIntegral φ u (0, 0) (1, 1) := by
    have heq : EqOn (glue u v) (u ∘ Prod.map (fun s ↦ smoothTransition (-3 * s + 1)) id)
        ([[(0 : ℝ), 1 / 2]] ×ˢ [[(0 : ℝ), 1]]) := by
      intro z hz
      rw [uIcc_of_le (by norm_num)] at hz
      exact glue_of_le hz.1.2
    rw [rectangleIntegral_congr heq, hreparam hu, ← rectangleIntegral_symm_fst]
    norm_num
    rw [smoothTransition.zero_of_nonpos (by norm_num)]
  have hr : rectangleIntegral φ (glue u v) (1 / 2, 0) (1, 1) =
      rectangleIntegral φ v (0, 0) (1, 1) := by
    have heq : EqOn (glue u v) (v ∘ Prod.map (fun s ↦ smoothTransition (3 * s + -2)) id)
        ([[(1 / 2 : ℝ), 1]] ×ˢ [[(0 : ℝ), 1]]) := by
      intro z hz
      rw [uIcc_of_le (by norm_num), uIcc_of_le (by norm_num)] at hz
      exact glue_eq_right h (by linarith [hz.1.1])
    rw [rectangleIntegral_congr heq, hreparam hv]
    norm_num
    rw [smoothTransition.zero_of_nonpos (by norm_num)]
  rw [hl, hr]
  abel

end Glue

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
  have h t : u (0, t) = v (0, t) := (hu.apply_zero t).trans (hv.apply_zero t).symm
  have hglue := hS (glue u v) (contMDiff_glue h hu.contMDiff hv.contMDiff)
    (fun t ht ↦ by rw [glue_zero, glue_zero, hu.apply_one t ht, hu.apply_one 0 (by simp)])
    (fun t ht ↦ by rw [glue_one, glue_one, hv.apply_one t ht, hv.apply_one 0 (by simp)])
    (fun s _ ↦ glue_periodic hu.periodic hv.periodic s)
  rw [rectangleIntegral_glue hφ h (hu.contMDiff.of_le (by simp))
    (hv.contMDiff.of_le (by simp)), sub_eq_zero] at hglue
  exact hglue.symm

/-- **Independence of the cylinder.** A continuous two-form that vanishes on tori has the same
integral over any two cylinders from a loop `γ` to a loop `γ₀`. -/
theorem VanishesOnTori.rectangleIntegral_eq (hT : VanishesOnTori φ) (hφ : IsSmoothForm I 0 φ)
    (hu : IsSmoothCylinder I γ γ₀ u) (hv : IsSmoothCylinder I γ γ₀ v) :
    rectangleIntegral φ u (0, 0) (1, 1) = rectangleIntegral φ v (0, 0) (1, 1) := by
  have h t : u (0, t) = v (0, t) := (hu.apply_zero t).trans (hv.apply_zero t).symm
  have hglue := hT (glue u v) (contMDiff_glue h hu.contMDiff hv.contMDiff)
    (fun t ht ↦ by rw [glue_zero, glue_one, hu.apply_one t ht, hv.apply_one t ht])
    (fun s _ ↦ glue_periodic hu.periodic hv.periodic s)
  rw [rectangleIntegral_glue hφ h (hu.contMDiff.of_le (by simp))
    (hv.contMDiff.of_le (by simp)), sub_eq_zero] at hglue
  exact hglue.symm

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

/-- Exact two-forms vanish on tori: by Stokes' formula the integral over a torus is the sum of the
line integrals along its edges, which cancel on opposite edges. -/
theorem vanishesOnTori_mextDeriv (hα : IsSmoothForm I 1 α) : VanishesOnTori (mextDeriv α) := by
  intro u hu h₁ hp
  have hI : uIoo (0 : ℝ) 1 ⊆ Icc 0 1 := by
    rw [uIoo_of_le zero_le_one]
    exact Ioo_subset_Icc_self
  rw [rectangleIntegral_mextDeriv hα (hu.of_le (by simp))]
  dsimp only
  rw [pathIntegral_congr_of_eqOn_uIoo (γ := fun t ↦ u (1, t)) (γ' := fun t ↦ u (0, t))
      fun t ht ↦ h₁ t (hI ht),
    pathIntegral_congr_of_eqOn_uIoo (γ := fun s ↦ u (s, 1)) (γ' := fun s ↦ u (s, 0))
      fun s hs ↦ hp s (hI hs)]
  simp

end Exact

end TauCeti
