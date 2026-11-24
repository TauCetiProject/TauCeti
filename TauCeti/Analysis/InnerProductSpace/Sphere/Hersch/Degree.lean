/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Sphere.Hersch.Basic
public import TauCeti.Geometry.Manifold.Degree.Global
public import TauCeti.Geometry.Manifold.Instances.Sphere
import TauCeti.Analysis.InnerProductSpace.Sphere.Hersch.Stereographic
import TauCeti.Geometry.Sphere.Connected

/-!
# The mapping degree of Hersch's sphere transformation

The path `t ↦ T_(t a)` is a smooth homotopy from the identity to Hersch's transformation `T_a`.
On a positive-dimensional sphere, homotopy invariance gives degree one. On a zero-dimensional
sphere, both points are fixed because the parameter is a multiple of each unit vector.
-/

public section

noncomputable section

open Metric
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]

/-- Hersch's transformation is a smooth map of the unit sphere. -/
theorem contMDiff_herschHomeomorph {a : E} (ha : ‖a‖ < 1) :
    ContMDiff (𝓡 n) (𝓡 n) ∞ (herschHomeomorph ha) := by
  refine ContMDiff.codRestrict_sphere (f := fun x ↦ (herschHomeomorph ha x : E)) ?_
    (fun x ↦ (herschHomeomorph ha x).property)
  · simp_rw [coe_herschHomeomorph]
    intro x
    have hpair : ContMDiff (𝓡 n) 𝓘(ℝ, E × E) ∞
        (fun y : sphere (0 : E) 1 ↦ (a, (y : E))) :=
      contMDiff_const.prodMk_space contMDiff_coe_sphere
    have hH : ContMDiffAt 𝓘(ℝ, E × E) 𝓘(ℝ, E) ∞
        (fun q : E × E ↦ herschMap q.1 q.2) (a, (x : E)) :=
      (contDiffAt_herschMap ha
        (inner_ne_neg_one ha (mem_sphere_zero_iff_norm.1 x.property).le)).contMDiffAt
    have hcomp : ContMDiffAt (𝓡 n) 𝓘(ℝ, E) ∞
        ((fun q : E × E ↦ herschMap q.1 q.2) ∘
          (fun y : sphere (0 : E) 1 ↦ (a, (y : E)))) x :=
      hH.comp x (hpair.contMDiffAt)
    exact hcomp

/-- The straight path in the parameter ball gives a smooth homotopy from the identity to
Hersch's sphere transformation. -/
theorem contMDiff_herschHomotopy {a : E} (ha : ‖a‖ < 1) :
    let hparam (t : unitInterval) : ‖(t : ℝ) • a‖ < 1 :=
      mem_ball_zero_iff.mp <|
        (convex_ball (0 : E) 1).smul_mem_of_zero_mem (mem_ball_self zero_lt_one)
          (mem_ball_zero_iff.mpr ha) t.property
    ContMDiff ((𝓡 n).prod (𝓡∂ 1)) (𝓡 n) ∞
      (fun p : sphere (0 : E) 1 × unitInterval ↦
        (⟨herschMap ((p.2 : ℝ) • a) p.1, herschMap_mem_sphere (hparam p.2) p.1.property⟩ :
            sphere (0 : E) 1)) := by
  intro hparam
  refine ContMDiff.codRestrict_sphere
    (f := fun p : sphere (0 : E) 1 × unitInterval ↦
      herschMap ((p.2 : ℝ) • a) p.1) ?_ ?_
  · intro p
    have hp := hparam p.2
    have hscale : ContMDiff ((𝓡 n).prod (𝓡∂ 1)) 𝓘(ℝ, E) ∞
        (fun q : sphere (0 : E) 1 × unitInterval ↦ (q.2 : ℝ) • a) :=
      (contDiff_id.smul contDiff_const).contMDiff.comp
        (contMDiff_subtypeVal_Icc.comp contMDiff_snd)
    have hpair : ContMDiff ((𝓡 n).prod (𝓡∂ 1)) 𝓘(ℝ, E × E) ∞
        (fun q : sphere (0 : E) 1 × unitInterval ↦ ((q.2 : ℝ) • a, (q.1 : E))) :=
      hscale.prodMk_space (contMDiff_coe_sphere.comp contMDiff_fst)
    have hH : ContMDiffAt 𝓘(ℝ, E × E) 𝓘(ℝ, E) ∞
        (fun q : E × E ↦ herschMap q.1 q.2) ((p.2 : ℝ) • a, (p.1 : E)) :=
      (contDiffAt_herschMap hp
        (inner_ne_neg_one hp (mem_sphere_zero_iff_norm.1 p.1.property).le)).contMDiffAt
    exact hH.comp p (hpair.contMDiffAt)

private theorem herschHomeomorph_eq_id_of_finrank_eq_one (hE : Module.finrank ℝ E = 1)
    {a : E} (ha : ‖a‖ < 1) : (herschHomeomorph ha : sphere (0 : E) 1 → sphere (0 : E) 1) = id := by
  funext x
  apply Subtype.ext
  rw [coe_herschHomeomorph, id_eq]
  have hx : ‖(x : E)‖ = 1 := mem_sphere_zero_iff_norm.mp x.property
  have hx₀ : (x : E) ≠ 0 := norm_ne_zero_iff.mp (by simp [hx])
  obtain ⟨s, rfl⟩ := (finrank_eq_one_iff_of_ne_zero' (x : E) hx₀).mp hE a
  have hs : |s| < 1 := by simpa only [norm_smul, hx, mul_one, Real.norm_eq_abs] using ha
  exact herschMap_smul_self hx (abs_lt.mp hs).1 (abs_lt.mp hs).2.le

/-- Hersch's transformation has mapping degree one on every unit sphere. -/
theorem degree_herschHomeomorph
    (o : Manifold.Orientation (𝓡 n) (sphere (0 : E) 1) (Fin n))
    {a : E} (ha : ‖a‖ < 1) : degree o o (herschHomeomorph ha) = 1 := by
  rcases n.eq_zero_or_pos with rfl | hn
  · have hE := Fact.out (p := Module.finrank ℝ E = 0 + 1)
    have : Nontrivial E := Module.nontrivial_of_finrank_eq_succ hE
    rw [herschHomeomorph_eq_id_of_finrank_eq_one hE ha, degree_id]
  · have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
    have : ConnectedSpace (sphere (0 : E) 1) :=
      Subtype.connectedSpace (isConnected_sphere_of_one_le hn)
    have hdeg := degree_eq_of_homotopy o o contMDiff_id
      (contMDiff_herschHomeomorph ha) (contMDiff_herschHomotopy ha)
      (fun x ↦ Subtype.ext (by simp)) (fun x ↦ Subtype.ext (by simp))
    simpa using hdeg.symm

/-- Postcomposing a smooth map into a unit sphere with Hersch's transformation preserves its
mapping degree. -/
theorem degree_herschHomeomorph_comp
    {F H M : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace H] {I : ModelWithCorners ℝ F H} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [BoundarylessManifold I M]
    [T2Space M] [CompactSpace M]
    (o : Manifold.Orientation I M (Fin n))
    (o' : Manifold.Orientation (𝓡 n) (sphere (0 : E) 1) (Fin n))
    {f : M → sphere (0 : E) 1} (hf : ContMDiff I (𝓡 n) ∞ f)
    {a : E} (ha : ‖a‖ < 1) :
    degree o o' ((herschHomeomorph ha) ∘ f) = degree o o' f := by
  rcases n.eq_zero_or_pos with rfl | hn
  · rw [herschHomeomorph_eq_id_of_finrank_eq_one (Fact.out (p := Module.finrank ℝ E = 0 + 1)) ha,
      Function.id_comp]
  · have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
    have : ConnectedSpace (sphere (0 : E) 1) :=
      Subtype.connectedSpace (isConnected_sphere_of_one_le hn)
    rw [degree_comp o o' o' hf (contMDiff_herschHomeomorph ha)
      hf.continuous.isProperMap (herschHomeomorph ha).isProperMap,
      degree_herschHomeomorph o' ha, one_mul]

end TauCeti
