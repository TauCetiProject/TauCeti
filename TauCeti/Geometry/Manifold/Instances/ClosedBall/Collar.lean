/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import TauCeti.Geometry.Manifold.Boundary.Collar.Basic
public import TauCeti.Geometry.Manifold.Boundary.Collar.ClosedBall
public import TauCeti.Geometry.Manifold.Instances.ClosedBall.Basic

/-!
# Collar charts of the closed unit ball

The radial collar `TauCeti.ballCollar` identifies the unit sphere times the half-line
`EuclideanHalfSpace 1` with the punctured closed unit ball, the point at normal coordinate `s`
above `u` being `exp (-s) • u`. This file shows that it is a diffeomorphism onto the punctured ball
in the sense of manifolds with boundary: it is analytic (`TauCeti.contMDiff_ballCollar`), and so is
its inverse `TauCeti.ballCollarInv`, `y ↦ (y / ‖y‖, -log ‖y‖)`, on the punctured ball. The latter
is what makes the collar charts below charts of the closed ball.

Consequently every chart `ψ` of the product `Sⁿ × [0, ∞)`, read through the collar and through the
identification `TauCeti.EuclideanHalfSpace.collarDiffeomorph` of `ℝⁿ × [0, ∞)` with the half-space
`EuclideanHalfSpace (n + 1)`, is a chart of the closed ball (`TauCeti.ballCollarChart ψ`,
`TauCeti.ballCollarChart_mem_maximalAtlas`). These *collar charts* turn statements about maps
between closed balls near their boundary spheres into statements about maps between products of
spheres with the half-line, where the boundary is the zero slice of the second factor.

The main application is to immersions. If a map `Φ` of closed unit balls reads, in the radial
collars, as an immersion `G` of the products near a point `q`, then `Φ` is an immersion at
`ballCollar q` (`TauCeti.isImmersionAt_of_comp_ballCollar_eventuallyEq`): in collar charts built
from the normal-form charts of `G`, the map `Φ` reads as the normal form of `G` conjugated by the
linear collar identification `TauCeti.EuclideanHalfSpace.collarAmbientEquiv`. In particular, a map
which near a point is the cone `r • u ↦ r • g u` over an immersion `g` of the unit spheres is an
immersion there, also at points of the boundary sphere
(`TauCeti.isImmersionAt_of_comp_ballCollar_eventuallyEq_prodMap`). This is the local model at the
boundary circle of a disc in the closed ball which is the cone over a smooth knot near that circle,
such as a concordance from a great circle capped off by the flat disc.

## Main definitions

* `TauCeti.ballCollarChart ψ`: the chart of the closed unit ball induced by a chart `ψ` of the
  unit sphere times the half-line.

## Main results

* `TauCeti.contMDiff_ballCollar`: the radial collar is analytic.
* `TauCeti.ballCollarChart_mem_maximalAtlas`: collar charts induced by charts of the maximal atlas
  of the product lie in the maximal atlas of the closed ball.
* `TauCeti.isImmersionAt_of_comp_ballCollar_eventuallyEq`: a map of closed balls which reads in the
  radial collars as an immersion is an immersion.
* `TauCeti.isImmersionAt_of_comp_ballCollar_eventuallyEq_prodMap`: the cone over an immersion of
  unit spheres is an immersion, up to the boundary sphere.

## References

* M. W. Hirsch, *Differential Topology*, Graduate Texts in Mathematics 33, Springer, 1976,
  Chapter 1, §4 (manifolds with boundary).
-/

public section

noncomputable section

namespace TauCeti

open Metric Set Topology Module Manifold Filter TopologicalSpace
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

/-! ### The radial collar is a diffeomorphism onto the punctured ball -/

/-- The radial collar of the closed unit ball is analytic, as a map from the unit sphere times the
half-line to the closed ball, both with their structures of manifolds with boundary. -/
theorem contMDiff_ballCollar {k : ℕ∞ω} :
    ContMDiff ((𝓡 n).prod (𝓡∂ 1)) (𝓡∂ (n + 1)) k (ballCollar (V := E)) := by
  rw [contMDiff_iff_comp_subtypeVal_closedBall]
  have hs : ContMDiff ((𝓡 n).prod (𝓡∂ 1)) 𝓘(ℝ) k
      (fun q : sphere (0 : E) 1 × EuclideanHalfSpace 1 ↦ Real.exp (-q.2.1 0)) :=
    (Real.contDiff_exp (n := k)).contMDiff.comp
      ((EuclideanSpace.proj (0 : Fin 1)).contDiff.neg.contMDiff.comp
        ((𝓡∂ 1).contMDiff.comp contMDiff_snd))
  refine (hs.smul (contMDiff_coe_sphere.comp contMDiff_fst)).congr fun q ↦ ?_
  simp [coe_ballCollar]

/-- The identification `ℝ ≃ ℝ¹` of the reals with the model vector space of the half-line. -/
private def realEquivEuclideanOne : ℝ ≃L[ℝ] EuclideanSpace ℝ (Fin 1) :=
  ((EuclideanSpace.equiv (Fin 1) ℝ).trans (ContinuousLinearEquiv.piUnique ℝ fun _ ↦ ℝ)).symm

private theorem realEquivEuclideanOne_apply_zero (r : ℝ) : realEquivEuclideanOne r 0 = r := by
  simp [realEquivEuclideanOne]

/-- The normal ray is the model inverse of the half-line, read on the reals. -/
private theorem normalRay_eq_symm (r : ℝ) :
    EuclideanHalfSpace.normalRay r = (𝓡∂ 1).symm (realEquivEuclideanOne r) := by
  apply Subtype.ext
  ext i
  fin_cases i
  simp [modelWithCornersEuclideanHalfSpace_symm_apply, EuclideanHalfSpace.normalRay_coe_apply,
    realEquivEuclideanOne_apply_zero]

variable (E) in
/-- The punctured closed unit ball, as an open subset of the closed unit ball. -/
private def puncturedClosedBall : Opens (closedBall (0 : E) 1) :=
  ⟨{y | (y : E) ≠ 0}, isOpen_ne_fun continuous_subtype_val continuous_const⟩

omit [InnerProductSpace ℝ E] in
private theorem mem_puncturedClosedBall {y : closedBall (0 : E) 1} :
    y ∈ puncturedClosedBall E ↔ (y : E) ≠ 0 :=
  Iff.rfl

/-- The inverse of the radial collar is analytic on the punctured ball. -/
private theorem contMDiff_ballCollarInv {k : ℕ∞ω} :
    ContMDiff (𝓡∂ (n + 1)) ((𝓡 n).prod (𝓡∂ 1)) k
      (fun y : puncturedClosedBall E ↦
        ballCollarInv (y : closedBall (0 : E) 1) (mem_puncturedClosedBall.1 y.2)) := by
  have hy : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ, E) k
      (fun y : puncturedClosedBall E ↦ ((y : closedBall (0 : E) 1) : E)) :=
    contMDiff_subtypeVal_closedBall.comp contMDiff_subtype_val
  have hnorm (y : puncturedClosedBall E) : ContMDiffAt (𝓡∂ (n + 1)) 𝓘(ℝ) k
      (fun y : puncturedClosedBall E ↦ ‖((y : closedBall (0 : E) 1) : E)‖) y :=
    (contDiffAt_norm ℝ (show ((y : closedBall (0 : E) 1) : E) ≠ 0 from y.2)).comp_contMDiffAt
      (f := fun y : puncturedClosedBall E ↦ ((y : closedBall (0 : E) 1) : E)) hy.contMDiffAt
  refine ContMDiff.prodMk ?_ ?_
  · refine ContMDiff.codRestrict_sphere (fun y ↦ ?_) _
    simp only [coe_ballCollarInv_fst]
    exact ((hnorm y).inv₀ (norm_ne_zero_iff.2 y.2)).smul hy.contMDiffAt
  · have hcoord : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) k
        (fun y : puncturedClosedBall E ↦
          realEquivEuclideanOne (-Real.log ‖((y : closedBall (0 : E) 1) : E)‖)) := fun y ↦ by
      have hlog : ContDiffAt ℝ k Real.log ‖((y : closedBall (0 : E) 1) : E)‖ :=
        Real.contDiffAt_log.2 (norm_ne_zero_iff.2 y.2)
      exact realEquivEuclideanOne.contDiff.contMDiff.contMDiffAt.comp y
        (hlog.comp_contMDiffAt
          (f := fun y : puncturedClosedBall E ↦ ‖((y : closedBall (0 : E) 1) : E)‖) (hnorm y)).neg
    have hrange (y : puncturedClosedBall E) :
        realEquivEuclideanOne (-Real.log ‖((y : closedBall (0 : E) 1) : E)‖) ∈ range (𝓡∂ 1) := by
      rw [range_modelWithCornersEuclideanHalfSpace, mem_ofPred_eq,
        realEquivEuclideanOne_apply_zero, neg_nonneg]
      exact Real.log_nonpos (norm_nonneg _) (mem_closedBall_zero_iff.1 y.1.2)
    exact ((𝓡∂ 1).contMDiffOn_symm.comp_contMDiff hcoord hrange).congr fun y ↦ by
      rw [ballCollarInv_snd, Function.comp_apply, normalRay_eq_symm]

variable (E) in
/-- The radial collar as an open partial homeomorphism onto the punctured closed ball. -/
private def ballCollarPartialHomeomorph :
    OpenPartialHomeomorph (sphere (0 : E) 1 × EuclideanHalfSpace 1) (closedBall (0 : E) 1) :=
  haveI : Nontrivial E := Module.nontrivial_of_finrank_eq_succ (Fact.out : finrank ℝ E = n + 1)
  haveI : Nonempty (sphere (0 : E) 1) := (NormedSpace.sphere_nonempty.2 zero_le_one).to_subtype
  isOpenEmbedding_ballCollar.toOpenPartialHomeomorph ballCollar

@[simp]
private theorem coe_ballCollarPartialHomeomorph :
    ⇑(ballCollarPartialHomeomorph E (n := n)) = ballCollar := by
  simp [ballCollarPartialHomeomorph]

private theorem ballCollarPartialHomeomorph_source :
    (ballCollarPartialHomeomorph E (n := n)).source = univ := by
  simp [ballCollarPartialHomeomorph]

private theorem ballCollarPartialHomeomorph_target :
    (ballCollarPartialHomeomorph E (n := n)).target = range ballCollar := by
  simp [ballCollarPartialHomeomorph]

private theorem ballCollarPartialHomeomorph_symm_apply_ballCollar
    (q : sphere (0 : E) 1 × EuclideanHalfSpace 1) :
    (ballCollarPartialHomeomorph E (n := n)).symm (ballCollar q) = q := by
  conv_lhs => rw [← coe_ballCollarPartialHomeomorph (n := n)]
  exact (ballCollarPartialHomeomorph E).left_inv (by simp [ballCollarPartialHomeomorph_source])

private theorem ballCollarPartialHomeomorph_symm_apply {y : closedBall (0 : E) 1}
    (hy : (y : E) ≠ 0) :
    (ballCollarPartialHomeomorph E (n := n)).symm y = ballCollarInv y hy := by
  conv_lhs => rw [← ballCollar_ballCollarInv y hy]
  exact ballCollarPartialHomeomorph_symm_apply_ballCollar _

private theorem contMDiffOn_ballCollarPartialHomeomorph_symm {k : ℕ∞ω} :
    ContMDiffOn (𝓡∂ (n + 1)) ((𝓡 n).prod (𝓡∂ 1)) k (ballCollarPartialHomeomorph E (n := n)).symm
      (ballCollarPartialHomeomorph E (n := n)).target := by
  rw [ballCollarPartialHomeomorph_target, range_ballCollar]
  intro y hy
  refine (ContMDiffAt.contMDiffWithinAt ?_)
  have h := contMDiffAt_subtype_iff (U := puncturedClosedBall E) (x := ⟨y, hy⟩) (n := k)
    (f := fun y ↦ (ballCollarPartialHomeomorph E (n := n)).symm y) (I := 𝓡∂ (n + 1))
    (I' := (𝓡 n).prod (𝓡∂ 1))
  refine h.1 ((contMDiff_ballCollarInv (E := E) ⟨y, hy⟩).congr_of_eventuallyEq ?_)
  exact Eventually.of_forall fun z ↦
    ballCollarPartialHomeomorph_symm_apply (mem_puncturedClosedBall.1 z.2)

/-! ### Collar charts -/

/-- The **collar chart** of the closed unit ball induced by a chart `ψ` of the unit sphere times
the half-line: a point `exp (-s) • u` of the punctured ball is read as `ψ (u, s)`, a point of
`ℝⁿ × [0, ∞)`, identified with a point of the half-space `EuclideanHalfSpace (n + 1)` by
`EuclideanHalfSpace.collarDiffeomorph`. -/
def ballCollarChart (ψ : OpenPartialHomeomorph (sphere (0 : E) 1 × EuclideanHalfSpace 1)
    (ModelProd (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace 1))) :
    OpenPartialHomeomorph (closedBall (0 : E) 1) (EuclideanHalfSpace (n + 1)) :=
  ((ballCollarPartialHomeomorph E (n := n)).symm.trans ψ).transHomeomorph
    (EuclideanHalfSpace.collarDiffeomorph (k := ⊤) n).toHomeomorph

variable {ψ : OpenPartialHomeomorph (sphere (0 : E) 1 × EuclideanHalfSpace 1)
  (ModelProd (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace 1))}

/-- A point lies in the source of the collar chart of `ψ` exactly when it is the radial collar of
a point of the source of `ψ`. -/
theorem mem_ballCollarChart_source {y : closedBall (0 : E) 1} :
    y ∈ (ballCollarChart ψ).source ↔ ∃ q ∈ ψ.source, ballCollar q = y := by
  simp only [ballCollarChart, OpenPartialHomeomorph.transHomeomorph_source,
    OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
    ballCollarPartialHomeomorph_target, mem_inter_iff, mem_preimage]
  constructor
  · rintro ⟨⟨q, rfl⟩, hq⟩
    rw [ballCollarPartialHomeomorph_symm_apply_ballCollar] at hq
    exact ⟨q, hq, rfl⟩
  · rintro ⟨q, hq, rfl⟩
    rw [ballCollarPartialHomeomorph_symm_apply_ballCollar]
    exact ⟨mem_range_self q, hq⟩

/-- The collar chart of `ψ` reads the radial collar of `q` as `ψ q`. -/
@[simp]
theorem ballCollarChart_apply_ballCollar (q : sphere (0 : E) 1 × EuclideanHalfSpace 1) :
    ballCollarChart ψ (ballCollar q) = EuclideanHalfSpace.collarDiffeomorph (k := ⊤) n (ψ q) := by
  simp [ballCollarChart, ballCollarPartialHomeomorph_symm_apply_ballCollar]

/-- The inverse of the collar chart of `ψ` is the radial collar of the inverse of `ψ`. -/
@[simp]
theorem ballCollarChart_symm_apply (y : EuclideanHalfSpace (n + 1)) :
    (ballCollarChart ψ).symm y =
      ballCollar (ψ.symm ((EuclideanHalfSpace.collarDiffeomorph (k := ⊤) n).symm y)) := by
  simp [ballCollarChart]

/-- A point lies in the target of the collar chart of `ψ` exactly when it corresponds to a point
of the target of `ψ`. -/
theorem mem_ballCollarChart_target {y : EuclideanHalfSpace (n + 1)} :
    y ∈ (ballCollarChart ψ).target ↔
      (EuclideanHalfSpace.collarDiffeomorph (k := ⊤) n).symm y ∈ ψ.target := by
  simp only [ballCollarChart, OpenPartialHomeomorph.transHomeomorph_target,
    OpenPartialHomeomorph.trans_target, OpenPartialHomeomorph.symm_target,
    ballCollarPartialHomeomorph_source, preimage_univ, inter_univ, mem_preimage]
  rfl

/-- The model of the half-space and the model of the product of `ℝⁿ` with the half-line are
intertwined by the collar identifications. -/
private theorem model_collarDiffeomorph
    (p : ModelProd (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace 1)) :
    (𝓡∂ (n + 1)) (EuclideanHalfSpace.collarDiffeomorph (k := ⊤) n p) =
      EuclideanHalfSpace.collarAmbientEquiv n (((𝓡 n).prod (𝓡∂ 1)) p) := by
  rw [modelWithCornersEuclideanHalfSpace_apply, EuclideanHalfSpace.coe_collarDiffeomorph_apply,
    modelWithCorners_prod_coe]
  rfl

private theorem model_collarDiffeomorph_symm (y : EuclideanHalfSpace (n + 1)) :
    ((𝓡 n).prod (𝓡∂ 1)) ((EuclideanHalfSpace.collarDiffeomorph (k := ⊤) n).symm y) =
      (EuclideanHalfSpace.collarAmbientEquiv n).symm y.1 :=
  EuclideanHalfSpace.collarDiffeomorph_symm_apply_coe n y

/-- The collar identification is smooth as a map from the model of `ℝⁿ × [0, ∞)` with its own
charts: it is the linear equivalence `collarAmbientEquiv` read in the models. -/
private theorem contMDiff_collarDiffeomorph {k : ℕ∞ω} :
    ContMDiff ((𝓡 n).prod (𝓡∂ 1)) (𝓡∂ (n + 1)) k
      (fun p : ModelProd (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace 1) ↦
        EuclideanHalfSpace.collarDiffeomorph (k := ⊤) n p) := by
  have hrange (p : ModelProd (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace 1)) :
      EuclideanHalfSpace.collarAmbientEquiv n (((𝓡 n).prod (𝓡∂ 1)) p) ∈ range (𝓡∂ (n + 1)) := by
    rw [← model_collarDiffeomorph]
    exact mem_range_self _
  refine ((𝓡∂ (n + 1)).contMDiffOn_symm.comp_contMDiff
    ((EuclideanHalfSpace.collarAmbientEquiv n).contDiff.contMDiff.comp
      ((𝓡 n).prod (𝓡∂ 1)).contMDiff) hrange).congr fun p ↦ ?_
  rw [Function.comp_apply, Function.comp_apply, ← model_collarDiffeomorph,
    ModelWithCorners.left_inv]

/-- The inverse collar identification is smooth as a map to the model of `ℝⁿ × [0, ∞)` with its
own charts. -/
private theorem contMDiff_collarDiffeomorph_symm {k : ℕ∞ω} :
    ContMDiff (𝓡∂ (n + 1)) ((𝓡 n).prod (𝓡∂ 1)) k
      (fun y ↦ id (α := ModelProd (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace 1))
        ((EuclideanHalfSpace.collarDiffeomorph (k := ⊤) n).symm y)) := by
  have hrange (y : EuclideanHalfSpace (n + 1)) :
      (EuclideanHalfSpace.collarAmbientEquiv n).symm ((𝓡∂ (n + 1)) y) ∈
        range ((𝓡 n).prod (𝓡∂ 1)) := by
    rw [modelWithCornersEuclideanHalfSpace_apply, ← model_collarDiffeomorph_symm]
    exact mem_range_self _
  refine ((((𝓡 n).prod (𝓡∂ 1))).contMDiffOn_symm.comp_contMDiff
    ((EuclideanHalfSpace.collarAmbientEquiv n).symm.contDiff.contMDiff.comp
      (𝓡∂ (n + 1)).contMDiff) hrange).congr fun y ↦ ?_
  rw [Function.comp_apply, Function.comp_apply, modelWithCornersEuclideanHalfSpace_apply,
    ← model_collarDiffeomorph_symm, ModelWithCorners.left_inv, id]

/-- Collar charts induced by charts of the maximal atlas of the unit sphere times the half-line lie
in the maximal atlas of the closed unit ball. -/
theorem ballCollarChart_mem_maximalAtlas {k : ℕ∞ω}
    (hψ : ψ ∈ IsManifold.maximalAtlas ((𝓡 n).prod (𝓡∂ 1)) k
      (sphere (0 : E) 1 × EuclideanHalfSpace 1)) :
    ballCollarChart ψ ∈ IsManifold.maximalAtlas (𝓡∂ (n + 1)) k (closedBall (0 : E) 1) := by
  have : IsManifold (𝓡∂ (n + 1)) k (closedBall (0 : E) 1) := .of_le le_top
  have : IsManifold ((𝓡 n).prod (𝓡∂ 1)) k (sphere (0 : E) 1 × EuclideanHalfSpace 1) :=
    .of_le le_top
  -- The collar identification, as a map of the model of the product with its own charts.
  have hC : ContMDiff ((𝓡 n).prod (𝓡∂ 1)) (𝓡∂ (n + 1)) k
      (fun p : ModelProd (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace 1) ↦
        EuclideanHalfSpace.collarDiffeomorph (k := ⊤) n p) :=
    contMDiff_collarDiffeomorph
  have hC' : ContMDiff (𝓡∂ (n + 1)) ((𝓡 n).prod (𝓡∂ 1)) k
      (fun y ↦ id (α := ModelProd (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace 1))
        ((EuclideanHalfSpace.collarDiffeomorph (k := ⊤) n).symm y)) :=
    contMDiff_collarDiffeomorph_symm
  refine OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn _ ?_ ?_
  · have h₁ : ContMDiffOn (𝓡∂ (n + 1)) ((𝓡 n).prod (𝓡∂ 1)) k
        (ψ ∘ (ballCollarPartialHomeomorph E (n := n)).symm)
        ((ballCollarPartialHomeomorph E (n := n)).symm.trans ψ).source := by
      rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source]
      exact (contMDiffOn_of_mem_maximalAtlas hψ).comp
        (contMDiffOn_ballCollarPartialHomeomorph_symm.mono inter_subset_left) fun y hy ↦ hy.2
    exact (hC.comp_contMDiffOn h₁).congr fun y _ ↦ rfl
  · have h := (contMDiff_ballCollar (E := E) (k := k)).comp_contMDiffOn
      ((contMDiffOn_symm_of_mem_maximalAtlas hψ).comp hC'.contMDiffOn
        fun y hy ↦ mem_ballCollarChart_target.1 hy)
    exact h.congr fun y _ ↦ ballCollarChart_symm_apply y

/-! ### Immersions read in the radial collars -/

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] {m : ℕ}
  [Fact (finrank ℝ F = m + 1)]

/-- **Immersions in the radial collars.** Let `Φ` be a map between the closed unit balls of `F`
and `E`. If near a point `q` of the unit sphere of `F` times the half-line, `Φ` reads in the radial
collars as a map `G` of the unit spheres times the half-line, `Φ ∘ ballCollar = ballCollar ∘ G`,
and `G` is an immersion at `q`, then `Φ` is an immersion at `ballCollar q`. When `q` has normal
coordinate `0` this is a point of the boundary sphere. -/
theorem isImmersionAt_of_comp_ballCollar_eventuallyEq {k : ℕ∞ω}
    {Φ : closedBall (0 : F) 1 → closedBall (0 : E) 1}
    {G : sphere (0 : F) 1 × EuclideanHalfSpace 1 → sphere (0 : E) 1 × EuclideanHalfSpace 1}
    {q : sphere (0 : F) 1 × EuclideanHalfSpace 1}
    (hG : IsImmersionAt ((𝓡 m).prod (𝓡∂ 1)) ((𝓡 n).prod (𝓡∂ 1)) k G q)
    (hΦ : Φ ∘ ballCollar =ᶠ[𝓝 q] ballCollar ∘ G) :
    IsImmersionAt (𝓡∂ (m + 1)) (𝓡∂ (n + 1)) k Φ (ballCollar q) := by
  -- Build the two collar charts, check the four chart conditions, and then compute `Φ` in these
  -- charts by transporting the normal form of `G` along `collarAmbientEquiv`.
  obtain ⟨W, hWeq, hW, hqW⟩ := eventually_nhds_iff.1 hΦ
  have hWo : IsOpen (ballCollar '' W) := isOpenEmbedding_ballCollar.isOpenMap W hW
  -- The domain chart is the collar chart of the normal-form domain chart of `G`, restricted to
  -- the collar of `W`, where `Φ` reads as `G`; the codomain chart is the collar chart of the
  -- normal-form codomain chart of `G`.
  set dom := (ballCollarChart hG.domChart).restr (ballCollar '' W)
  set cod := ballCollarChart (E := E) hG.codChart
  have hdom_source {y : closedBall (0 : F) 1} (hy : y ∈ dom.source) :
      ∃ p ∈ W, p ∈ hG.domChart.source ∧ ballCollar p = y := by
    rw [OpenPartialHomeomorph.restr_source' _ _ hWo] at hy
    obtain ⟨⟨p, hp, rfl⟩, ⟨p', hp', hpp'⟩⟩ := (And.imp_left mem_ballCollarChart_source.1 hy)
    rw [isOpenEmbedding_ballCollar.injective hpp'] at hp'
    exact ⟨p, hp', hp, rfl⟩
  have hsource {p} (hp : p ∈ W) (hpd : p ∈ hG.domChart.source) :
      Φ (ballCollar p) ∈ cod.source := by
    have h := hWeq p hp
    simp only [Function.comp_apply] at h
    rw [h]
    exact mem_ballCollarChart_source.2 ⟨G p, hG.source_subset_preimage_source hpd, rfl⟩
  let equiv : (EuclideanSpace ℝ (Fin (m + 1)) × hG.complement) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (n + 1)) :=
    ((EuclideanHalfSpace.collarAmbientEquiv m).symm.prodCongr
      (ContinuousLinearEquiv.refl ℝ hG.complement)).trans
      (hG.equiv.trans (EuclideanHalfSpace.collarAmbientEquiv n))
  refine IsImmersionAt.mk_of_charts equiv dom cod ?_ ?_ ?_ ?_ ?_ ?_
  · rw [OpenPartialHomeomorph.restr_source' _ _ hWo]
    exact ⟨mem_ballCollarChart_source.2 ⟨q, hG.mem_domChart_source, rfl⟩, mem_image_of_mem _ hqW⟩
  · exact hsource hqW hG.mem_domChart_source
  · exact restr_mem_maximalAtlas _ (ballCollarChart_mem_maximalAtlas hG.domChart_mem_maximalAtlas)
      hWo
  · exact ballCollarChart_mem_maximalAtlas hG.codChart_mem_maximalAtlas
  · intro y hy
    obtain ⟨p, hp, hpd, rfl⟩ := hdom_source hy
    exact hsource hp hpd
  · intro u hu
    have hu' := hu
    rw [OpenPartialHomeomorph.extend_target, mem_inter_iff, mem_preimage] at hu'
    obtain ⟨hut, ⟨u', rfl⟩⟩ := hu'
    rw [ModelWithCorners.left_inv] at hut
    -- The point of the product whose collar is the chart preimage of `u`.
    set p := hG.domChart.symm ((EuclideanHalfSpace.collarDiffeomorph (k := ⊤) m).symm u')
    have hsymm : (dom.extend (𝓡∂ (m + 1))).symm ((𝓡∂ (m + 1)) u') = ballCollar p := by
      rw [OpenPartialHomeomorph.extend_coe_symm, Function.comp_apply, ModelWithCorners.left_inv]
      simp [dom, p]
    have hmem : ballCollar p ∈ dom.source := by
      rw [← hsymm, ← dom.extend_source (I := 𝓡∂ (m + 1))]
      exact (dom.extend (𝓡∂ (m + 1))).map_target hu
    obtain ⟨p', hp', -, hpp'⟩ := hdom_source hmem
    rw [isOpenEmbedding_ballCollar.injective hpp'] at hp'
    have hΦp : Φ (ballCollar p) = ballCollar (G p) := hWeq p hp'
    -- The normal form of `G` at the corresponding point of the model of the product.
    have hv : ((𝓡 m).prod (𝓡∂ 1))
        ((EuclideanHalfSpace.collarDiffeomorph (k := ⊤) m).symm u') ∈
          (hG.domChart.extend ((𝓡 m).prod (𝓡∂ 1))).target := by
      rw [OpenPartialHomeomorph.extend_target, mem_inter_iff, mem_preimage,
        ModelWithCorners.left_inv]
      have hut' : u' ∈ (ballCollarChart hG.domChart).target := by
        simp only [dom, OpenPartialHomeomorph.restr_target] at hut
        exact hut.1
      exact ⟨mem_ballCollarChart_target.1 hut', mem_range_self _⟩
    have hnf := hG.writtenInCharts hv
    simp only [Function.comp_apply, OpenPartialHomeomorph.extend_coe_symm,
      OpenPartialHomeomorph.extend_coe, ModelWithCorners.left_inv] at hnf
    rw [Function.comp_apply, Function.comp_apply, hsymm, hΦp, OpenPartialHomeomorph.extend_coe,
      Function.comp_apply, ballCollarChart_apply_ballCollar, model_collarDiffeomorph, hnf,
      model_collarDiffeomorph_symm]
    simp [equiv]

/-- **Cones over immersions of spheres are immersions.** Let `g` be an immersion of the unit sphere
of `F` into the unit sphere of `E` at a point `q.1`. If near `q` the map `Φ` of closed unit balls is
the cone `exp (-s) • u ↦ exp (-s) • g u` over `g`, then `Φ` is an immersion at `ballCollar q`, also
when `q` has normal coordinate `0`, so that `ballCollar q` lies on the boundary sphere. -/
theorem isImmersionAt_of_comp_ballCollar_eventuallyEq_prodMap {k : ℕ∞ω}
    {Φ : closedBall (0 : F) 1 → closedBall (0 : E) 1} {g : sphere (0 : F) 1 → sphere (0 : E) 1}
    {q : sphere (0 : F) 1 × EuclideanHalfSpace 1} (hg : IsImmersionAt (𝓡 m) (𝓡 n) k g q.1)
    (hΦ : Φ ∘ ballCollar =ᶠ[𝓝 q] ballCollar ∘ Prod.map g id) :
    IsImmersionAt (𝓡∂ (m + 1)) (𝓡∂ (n + 1)) k Φ (ballCollar q) := by
  have : IsManifold (𝓡 m) k (sphere (0 : F) 1) := .of_le le_top
  have : IsManifold (𝓡 n) k (sphere (0 : E) 1) := .of_le le_top
  have hid : IsImmersionAtOfComplement PUnit.{1} (𝓡∂ 1) (𝓡∂ 1) k (@id (EuclideanHalfSpace 1)) q.2 :=
    IsImmersionOfComplement.id q.2
  exact isImmersionAt_of_comp_ballCollar_eventuallyEq
    (hg.isImmersionAtOfComplement_complement.prodMap hid).isImmersionAt hΦ

end TauCeti
