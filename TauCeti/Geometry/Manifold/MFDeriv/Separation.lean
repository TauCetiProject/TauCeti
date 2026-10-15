/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.MFDeriv.Constancy
public import TauCeti.Geometry.Manifold.MFDeriv.Prod

/-!
# Separating manifold maps by their differentials

A differentiable map on a product whose differential kills the second tangent factor
is independent of the second variable when that factor is preconnected and boundaryless.
The corresponding statement holds for the first factor. For maps between products,
vanishing of both mixed differential blocks characterizes separation into a product map.

This is the passage from preservation of tangent factors to global separation needed
in the classification of isometries of product Riemannian manifolds. The result concerns
arbitrary differentiable maps and does not require a metric or finite dimension.
-/

public section

open Function
open scoped Manifold

namespace MDifferentiable

variable {E F V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {H G A : Type*} [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace A]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  {K : ModelWithCorners ℝ V A}
  {M N P : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N] [TopologicalSpace P] [ChartedSpace A P]
  [IsManifold K 1 P]

/-- Killing all second-factor tangent vectors forces independence of the second variable
on a preconnected boundaryless factor. -/
theorem apply_eq_of_mfderiv_inr_eq_zero [IsManifold J 1 N] [J.Boundaryless]
    [PreconnectedSpace N] {f : M × N → P} (hf : MDifferentiable (I.prod J) K f)
    (hzero : ∀ p : M × N, ∀ v : TangentSpace J p.2,
      mfderiv (I.prod J) K f p (0, v) = 0) (x : M) (y y₀ : N) :
    f (x, y) = f (x, y₀) := by
  have hslice : MDifferentiable J K (fun z => f (x, z)) :=
    hf.comp (mdifferentiable_const.prodMk mdifferentiable_id)
  apply hslice.apply_eq_of_mfderiv_eq_zero _ y y₀
  intro z
  have hcomp := mfderiv_comp z (hf (x, z))
    (mdifferentiableAt_const.prodMk mdifferentiableAt_id)
  rw [mfderiv_prod_right] at hcomp
  ext v
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
    zero_apply] using
    (DFunLike.congr_fun hcomp v).trans (hzero (x, z) v)

/-- Killing all first-factor tangent vectors forces independence of the first variable
on a preconnected boundaryless factor. -/
theorem apply_eq_of_mfderiv_inl_eq_zero [IsManifold I 1 M] [I.Boundaryless]
    [PreconnectedSpace M] {f : M × N → P} (hf : MDifferentiable (I.prod J) K f)
    (hzero : ∀ p : M × N, ∀ v : TangentSpace I p.1,
      mfderiv (I.prod J) K f p (v, 0) = 0) (x x₀ : M) (y : N) :
    f (x, y) = f (x₀, y) := by
  have hslice : MDifferentiable I K (fun z => f (z, y)) :=
    hf.comp (mdifferentiable_id.prodMk mdifferentiable_const)
  apply hslice.apply_eq_of_mfderiv_eq_zero _ x x₀
  intro z
  have hcomp := mfderiv_comp z (hf (z, y))
    (mdifferentiableAt_id.prodMk mdifferentiableAt_const)
  simp only [id_eq] at hcomp
  rw [mfderiv_prod_left] at hcomp
  ext v
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
    zero_apply] using
    (DFunLike.congr_fun hcomp v).trans (hzero (z, y) v)

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  {B : Type*} [TopologicalSpace B] {L : ModelWithCorners ℝ W B}
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace B Q] [IsManifold L 1 Q]
  [IsManifold I 1 M] [IsManifold J 1 N] [I.Boundaryless] [J.Boundaryless]
  [PreconnectedSpace M] [PreconnectedSpace N]

/-- A differentiable map between products separates into its two slices exactly when
its differential has zero mixed blocks. The specified base points make the slices canonical. -/
theorem eq_prodMap_iff_mfderiv_mixed_eq_zero
    {f : M × N → P × Q} (hf : MDifferentiable (I.prod J) (K.prod L) f)
    (x₀ : M) (y₀ : N) :
    f = Prod.map (fun x => (f (x, y₀)).1) (fun y => (f (x₀, y)).2) ↔
      (∀ p : M × N, ∀ v : TangentSpace J p.2,
        (mfderiv (I.prod J) (K.prod L) f p (0, v)).1 = 0) ∧
      (∀ p : M × N, ∀ v : TangentSpace I p.1,
        (mfderiv (I.prod J) (K.prod L) f p (v, 0)).2 = 0) := by
  have hfst : MDifferentiable (I.prod J) K (fun p => (f p).1) :=
    mdifferentiable_fst.comp hf
  have hsnd : MDifferentiable (I.prod J) L (fun p => (f p).2) :=
    mdifferentiable_snd.comp hf
  have hdfst (p : M × N) (v : TangentSpace (I.prod J) p) :
      mfderiv (I.prod J) K (fun p => (f p).1) p v =
        (mfderiv (I.prod J) (K.prod L) f p v).1 := by
    have h := mfderiv_comp p mdifferentiableAt_fst (hf p)
    rw [mfderiv_fst] at h
    exact DFunLike.congr_fun h v
  have hdsnd (p : M × N) (v : TangentSpace (I.prod J) p) :
      mfderiv (I.prod J) L (fun p => (f p).2) p v =
        (mfderiv (I.prod J) (K.prod L) f p v).2 := by
    have h := mfderiv_comp p mdifferentiableAt_snd (hf p)
    rw [mfderiv_snd] at h
    exact DFunLike.congr_fun h v
  constructor
  · intro h
    constructor
    · intro p v
      refine (hdfst p (0, v)).symm.trans ?_
      have heq : (fun p => (f p).1) = (fun x => (f (x, y₀)).1) ∘ Prod.fst := by
        funext p
        simpa only [Prod.map_fst, Function.comp_apply] using
          congrArg Prod.fst (congrFun h p)
      -- The product tangent space and the product of the two tangent spaces
      -- have different type indices but the same underlying model space.
      erw [heq, TauCeti.mfderiv_comp_fst]
      exact (mfderiv I K (fun x => (f (x, y₀)).1) p.1).map_zero
    · intro p v
      refine (hdsnd p (v, 0)).symm.trans ?_
      have heq : (fun p => (f p).2) = (fun y => (f (x₀, y)).2) ∘ Prod.snd := by
        funext p
        simpa only [Prod.map_snd, Function.comp_apply] using
          congrArg Prod.snd (congrFun h p)
      -- As above, identify the product tangent models when applying the projection.
      erw [heq, TauCeti.mfderiv_comp_snd]
      exact (mfderiv J L (fun y => (f (x₀, y)).2) p.2).map_zero
  · rintro ⟨h₁, h₂⟩
    funext p
    exact Prod.ext
      (hfst.apply_eq_of_mfderiv_inr_eq_zero (fun p v => (hdfst p (0, v)).trans (h₁ p v))
        p.1 p.2 y₀)
      (hsnd.apply_eq_of_mfderiv_inl_eq_zero (fun p v => (hdsnd p (v, 0)).trans (h₂ p v))
        p.1 x₀ p.2)

end MDifferentiable
