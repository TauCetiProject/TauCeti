/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Scalar
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import TauCeti.Geometry.Manifold.RegularValue.Level
public import TauCeti.Geometry.Manifold.PullbackGroupoid
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Analysis.Calculus.Deriv.Pow
import TauCeti.Geometry.Manifold.SmoothEmbedding.Diffeomorph

/-!
# Sphere bundles as smooth hypersurfaces

In a smooth real Riemannian vector bundle, the vectors of a prescribed positive smooth
length form a smooth embedded hypersurface of the total space. Its smooth structure is
obtained from the regular level theorem applied to the squared fibre norm minus the
squared radius. Radial variation proves regularity without choosing orthonormal frames.
These sphere bundles describe the boundaries of normal disc neighbourhoods in surgery.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Corollary 5.14
  (regular level sets) and Theorem 6.24 (tubular neighbourhoods).
* M. W. Hirsch, *Differential Topology*, Chapter 4, Theorem 6.3.
-/

public noncomputable section

open Bundle Function Set Manifold TauCeti
open scoped Manifold ContDiff

variable {B : Type*} {V : B → Type*} {F : Type*}
  [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
  [TopologicalSpace B]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [ChartedSpace H B] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]

namespace Bundle.TotalSpace

/-- Subtracting any smooth function of the base from the squared fibre norm leaves every
nonzero vector a regular point. Radial variation alone detects a nonzero differential. -/
theorem isRegularPoint_norm_sq_sub_proj
    [IsContMDiffRiemannianBundle I 1 F V] (p : TotalSpace F V) {a : B → ℝ}
    (ha : ContMDiffAt I 𝓘(ℝ) 1 a p.proj) (hp : p.2 ≠ 0) :
    IsRegularPoint (I.prod 𝓘(ℝ, F)) 𝓘(ℝ)
      (fun q : TotalSpace F V => ‖q.2‖ ^ 2 - a q.proj) p := by
  let g : TotalSpace F V → ℝ := fun q => ‖q.2‖ ^ 2 - a q.proj
  let c : ℝ → TotalSpace F V := fun t => ⟨p.proj, t • p.2⟩
  have hsq : ContMDiff (I.prod 𝓘(ℝ, F)) 𝓘(ℝ) 1
      (fun q : TotalSpace F V => ‖q.2‖ ^ 2) := by
    simpa only [real_inner_self_eq_norm_sq] using
      (contMDiff_id (I := I.prod 𝓘(ℝ, F)) (n := 1)).inner_bundle contMDiff_id
  have hg : ContMDiffAt (I.prod 𝓘(ℝ, F)) 𝓘(ℝ) 1 g p :=
    (hsq p).sub (ha.comp p (Bundle.contMDiff_proj (IB := I) (F := F) V p))
  have hc : ContMDiff 𝓘(ℝ) (I.prod 𝓘(ℝ, F)) 1 c :=
    contMDiff_id.smul_totalSpace (contMDiff_const (c := p))
  have hc1 : c 1 = p := by simp [c]
  have hgc : g ∘ c = fun t : ℝ => t ^ 2 * ‖p.2‖ ^ 2 - a p.proj := by
    funext t
    simp [g, c, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have hd : HasDerivAt (g ∘ c) (2 * ‖p.2‖ ^ 2) 1 := by
    rw [hgc]
    convert (((hasDerivAt_id (1 : ℝ)).pow 2).mul_const (‖p.2‖ ^ 2)).sub_const (a p.proj) using 1 <;>
      norm_num
  rw [isRegularPoint_iff_mvfderiv_ne_zero]
  intro hzero
  -- Keep the chain rule based at `c 1`, so its dependent tangent vectors need no transport.
  have hg1 := hc1.symm ▸ hg.mdifferentiableAt one_ne_zero
  have hzero1 : mvfderiv (I.prod 𝓘(ℝ, F)) g (c 1) = 0 := hc1.symm ▸ hzero
  have hchain := mvfderiv_comp_apply (I := I.prod 𝓘(ℝ, F)) (I' := 𝓘(ℝ))
    (1 : ℝ) hg1 ((hc 1).mdifferentiableAt one_ne_zero)
    ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (1 : ℝ)).symm 1)
  have hnorm : 2 * ‖p.2‖ ^ 2 = 0 := by
    simpa [hzero1, mvfderiv_eq_fderiv, hd.hasFDerivAt.fderiv] using hchain
  have hne : 2 * ‖p.2‖ ^ 2 ≠ 0 := by positivity
  exact hne hnorm

end Bundle.TotalSpace

namespace TauCeti

/-- The squared fibre norm minus the squared radius. Its zero set is the sphere bundle
when the radius is positive. -/
def sphereBundleEquation (r : B → ℝ) (p : TotalSpace F V) : ℝ :=
  ‖p.2‖ ^ 2 - (r p.proj) ^ 2

omit [∀ b, InnerProductSpace ℝ (V b)] [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V] in
/-- The defining scalar equation of a variable-radius sphere bundle. -/
@[simp] theorem sphereBundleEquation_apply (r : B → ℝ) (p : TotalSpace F V) :
    sphereBundleEquation r p = ‖p.2‖ ^ 2 - (r p.proj) ^ 2 := (rfl)

omit [∀ b, InnerProductSpace ℝ (V b)] [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V] in
/-- For a nonnegative radius, the equation cuts out exactly the vectors of that length. -/
theorem sphereBundleEquation_eq_zero_iff (r : B → ℝ) (p : TotalSpace F V)
    (hr : 0 ≤ r p.proj) :
    sphereBundleEquation r p = 0 ↔ ‖p.2‖ = r p.proj := by
  rw [sphereBundleEquation_apply, sub_eq_zero]
  exact (sq_eq_sq₀ (norm_nonneg _) hr)

/-- The sphere-bundle equation is as smooth as the fibre metric and radius. -/
theorem contMDiff_sphereBundleEquation {n : ℕ∞ω}
    [IsContMDiffRiemannianBundle I n F V] {r : B → ℝ}
    (hr : ContMDiff I 𝓘(ℝ) n r) :
    ContMDiff (I.prod 𝓘(ℝ, F)) 𝓘(ℝ) n (sphereBundleEquation (F := F) (V := V) r) := by
  have hsq : ContMDiff (I.prod 𝓘(ℝ, F)) 𝓘(ℝ) n
      (fun p : TotalSpace F V => ‖p.2‖ ^ 2) := by
    simpa only [real_inner_self_eq_norm_sq] using
      (contMDiff_id (I := I.prod 𝓘(ℝ, F)) (n := n)).inner_bundle contMDiff_id
  exact hsq.sub ((hr.comp (Bundle.contMDiff_proj (IB := I) (F := F) V)).pow 2)

/-- Zero is a regular value of the sphere-bundle equation for a nowhere-zero `C¹` radius. -/
theorem isRegularValue_sphereBundleEquation
    [IsContMDiffRiemannianBundle I 1 F V] {r : B → ℝ}
    (hr : ContMDiff I 𝓘(ℝ) 1 r) (hr0 : ∀ b, r b ≠ 0) :
    IsRegularValue (I.prod 𝓘(ℝ, F)) 𝓘(ℝ)
      (sphereBundleEquation (F := F) (V := V) r) 0 := by
  rw [isRegularValue_iff]
  intro p hp
  apply p.isRegularPoint_norm_sq_sub_proj ((hr p.proj).pow 2)
  intro hv
  apply hr0 p.proj
  simpa [sphereBundleEquation_apply, hv] using hp

variable [I.Boundaryless] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  {n : ℕ∞ω} [IsManifold I n B] [ContMDiffVectorBundle n F V I]
  [IsContMDiffRiemannianBundle I n F V]

/-- The sphere bundle with positive `C^n` radius, endowed with the regular-level atlas.
The model has dimension `dim B + rank V - 1` (natural subtraction). Install this atlas
locally to use the manifold and smooth embedding theorems. -/
@[instance_reducible]
def sphereBundleChartedSpace {r : B → ℝ} (hr : ContMDiff I 𝓘(ℝ) n r)
    (hn : 1 ≤ n) (hrpos : ∀ b, 0 < r b) :
    ChartedSpace (Fin (Module.finrank ℝ (E × F) - 1) → ℝ)
      {p : TotalSpace F V // ‖p.2‖ = r p.proj} := by
  let : IsContMDiffRiemannianBundle I 1 F V := .of_le hn
  let hreg := isRegularValue_sphereBundleEquation (F := F) (V := V)
    (hr.of_le hn) (fun b => (hrpos b).ne')
  let := regularLevelChartedSpace (n := Module.finrank ℝ (E × F) - 1)
    (fun p _ => (contMDiff_sphereBundleEquation hr p).of_le hn) hreg (by rw [Module.finrank_self])
  let e : {p : TotalSpace F V // ‖p.2‖ = r p.proj} ≃ₜ
      {p : TotalSpace F V // sphereBundleEquation r p = 0} :=
    Homeomorph.setCongr
      (s := {p : TotalSpace F V | ‖p.2‖ = r p.proj})
      (t := {p : TotalSpace F V | sphereBundleEquation r p = 0}) (Set.ext fun p =>
        (sphereBundleEquation_eq_zero_iff r p (hrpos p.proj).le).symm)
  exact e.pullbackChartedSpace

/-- A positive-radius sphere bundle is a manifold one dimension below the total space. -/
theorem isManifold_sphereBundle {r : B → ℝ} (hr : ContMDiff I 𝓘(ℝ) n r)
    (hn : 1 ≤ n) (hrpos : ∀ b, 0 < r b) :
    letI := sphereBundleChartedSpace (F := F) (V := V) hr hn hrpos
    IsManifold 𝓘(ℝ, Fin (Module.finrank ℝ (E × F) - 1) → ℝ) n
      {p : TotalSpace F V // ‖p.2‖ = r p.proj} := by
  let : IsContMDiffRiemannianBundle I 1 F V := .of_le hn
  let hreg := isRegularValue_sphereBundleEquation (F := F) (V := V)
    (hr.of_le hn) (fun b => (hrpos b).ne')
  let hfm := fun (p : TotalSpace F V) (_ : sphereBundleEquation r p = 0) =>
    contMDiff_sphereBundleEquation hr p
  let := regularLevelChartedSpace (n := Module.finrank ℝ (E × F) - 1)
    (fun p hp => (hfm p hp).of_le hn) hreg (by rw [Module.finrank_self])
  have := isManifold_regularLevel hn hfm hreg (by rw [Module.finrank_self])
  exact (Homeomorph.setCongr
    (s := {p : TotalSpace F V | ‖p.2‖ = r p.proj})
    (t := {p : TotalSpace F V | sphereBundleEquation r p = 0}) (Set.ext fun p =>
      (sphereBundleEquation_eq_zero_iff r p (hrpos p.proj).le).symm)).pullback_isManifold _ n

/-- The inclusion of a positive-radius sphere bundle into the total space is a smooth
embedding for its regular-level atlas. -/
theorem isSmoothEmbedding_coe_sphereBundle {r : B → ℝ} (hr : ContMDiff I 𝓘(ℝ) n r)
    (hn : 1 ≤ n) (hrpos : ∀ b, 0 < r b) :
    letI := sphereBundleChartedSpace (F := F) (V := V) hr hn hrpos
    Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin (Module.finrank ℝ (E × F) - 1) → ℝ)
      (I.prod 𝓘(ℝ, F)) n
      (Subtype.val : {p : TotalSpace F V // ‖p.2‖ = r p.proj} → TotalSpace F V) := by
  let : IsContMDiffRiemannianBundle I 1 F V := .of_le hn
  let hreg := isRegularValue_sphereBundleEquation (F := F) (V := V)
    (hr.of_le hn) (fun b => (hrpos b).ne')
  let hfm := fun (p : TotalSpace F V) (_ : sphereBundleEquation r p = 0) =>
    contMDiff_sphereBundleEquation hr p
  let := regularLevelChartedSpace (n := Module.finrank ℝ (E × F) - 1)
    (fun p hp => (hfm p hp).of_le hn) hreg (by rw [Module.finrank_self])
  have := isManifold_regularLevel hn hfm hreg (by rw [Module.finrank_self])
  let e : {p : TotalSpace F V // ‖p.2‖ = r p.proj} ≃ₜ
      {p : TotalSpace F V // sphereBundleEquation r p = 0} :=
    Homeomorph.setCongr
      (s := {p : TotalSpace F V | ‖p.2‖ = r p.proj})
      (t := {p : TotalSpace F V | sphereBundleEquation r p = 0}) (Set.ext fun p =>
        (sphereBundleEquation_eq_zero_iff r p (hrpos p.proj).le).symm)
  let := e.pullbackChartedSpace (H := Fin (Module.finrank ℝ (E × F) - 1) → ℝ)
  have := e.pullback_isManifold 𝓘(ℝ, Fin (Module.finrank ℝ (E × F) - 1) → ℝ) n
  have h := isSmoothEmbedding_comp_diffeomorph
    (I := 𝓘(ℝ, Fin (Module.finrank ℝ (E × F) - 1) → ℝ))
    (e.pullbackDiffeomorph 𝓘(ℝ, Fin (Module.finrank ℝ (E × F) - 1) → ℝ) n)
    (isSmoothEmbedding_coe_regularLevel hn hfm hreg (by rw [Module.finrank_self]))
  have hcoe : Subtype.val ∘ e.pullbackDiffeomorph
      𝓘(ℝ, Fin (Module.finrank ℝ (E × F) - 1) → ℝ) n =
      (Subtype.val : {p : TotalSpace F V // ‖p.2‖ = r p.proj} → TotalSpace F V) := by
    rw [Homeomorph.coe_pullbackDiffeomorph]
    -- A set-congruence homeomorphism preserves the underlying point.
    rfl
  rw [hcoe] at h
  exact h

end TauCeti
