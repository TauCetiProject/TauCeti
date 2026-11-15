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
* `TauCeti.contMDiff_ballCollarInv`: its inverse is analytic on the punctured closed ball
  `TauCeti.puncturedClosedBall`.
* `TauCeti.ballCollarChart_mem_maximalAtlas`: collar charts induced by charts of the maximal atlas
  of the product lie in the maximal atlas of the closed ball.
* `TauCeti.isImmersionAt_of_comp_ballCollar_eventuallyEq`: if a map `Φ` of closed balls reads near
  `q` in the radial collars as a map `G` that is an immersion at `q`, then `Φ` is an immersion at
  `ballCollar q`.
* `TauCeti.isImmersionAt_of_comp_ballCollar_eventuallyEq_prodMap`: a map that near a collar point
  is the cone over a map of unit spheres which is an immersion at the matching point is an
  immersion at that collar point, including on the boundary sphere.

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

variable (E) in
/-- The punctured closed unit ball, as an open subset of the closed unit ball. It is the range of
the radial collar (`TauCeti.range_ballCollar`). -/
def puncturedClosedBall : Opens (closedBall (0 : E) 1) :=
  ⟨{y | (y : E) ≠ 0}, isOpen_ne_fun continuous_subtype_val continuous_const⟩

omit [InnerProductSpace ℝ E] in
/-- A point of the closed unit ball lies in the punctured closed ball exactly when it is nonzero. -/
@[simp]
theorem mem_puncturedClosedBall {y : closedBall (0 : E) 1} :
    y ∈ puncturedClosedBall E ↔ (y : E) ≠ 0 :=
  Iff.rfl

/-- The inverse of the radial collar is analytic on the punctured ball, as a map to the unit sphere
times the half-line with its structure of manifold with boundary. -/
theorem contMDiff_ballCollarInv {k : ℕ∞ω} :
    ContMDiff (𝓡∂ (n + 1)) ((𝓡 n).prod (𝓡∂ 1)) k
      (fun y : puncturedClosedBall E ↦
        ballCollarInv (y : closedBall (0 : E) 1) (mem_puncturedClosedBall.1 y.2)) := by
  have hy : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ, E) k
      (fun y : puncturedClosedBall E ↦ ((y : closedBall (0 : E) 1) : E)) :=
    contMDiff_subtypeVal_closedBall.comp contMDiff_subtype_val
  have hnorm (y : puncturedClosedBall E) : ContMDiffAt (𝓡∂ (n + 1)) 𝓘(ℝ) k
      (fun y : puncturedClosedBall E ↦ ‖((y : closedBall (0 : E) 1) : E)‖) y :=
    (contDiffAt_norm ℝ (mem_puncturedClosedBall.1 y.2)).comp_contMDiffAt
      (f := fun y : puncturedClosedBall E ↦ ((y : closedBall (0 : E) 1) : E)) hy.contMDiffAt
  refine ContMDiff.prodMk ?_ ?_
  · refine ContMDiff.codRestrict_sphere (fun y ↦ ?_) _
    simp only [coe_ballCollarInv_fst]
    exact ((hnorm y).inv₀ (norm_ne_zero_iff.2 y.2)).smul hy.contMDiffAt
  · have hcoord : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) k
        (fun y : puncturedClosedBall E ↦
          (PiLp.equivOfUnique 2 ℝ fun _ : Fin 1 ↦ ℝ).symm
            (-Real.log ‖((y : closedBall (0 : E) 1) : E)‖)) := fun y ↦ by
      have hlog : ContDiffAt ℝ k Real.log ‖((y : closedBall (0 : E) 1) : E)‖ :=
        Real.contDiffAt_log.2 (norm_ne_zero_iff.2 y.2)
      exact (PiLp.equivOfUnique 2 ℝ fun _ : Fin 1 ↦ ℝ).symm.contDiff.contMDiff.contMDiffAt.comp y
        (hlog.comp_contMDiffAt
          (f := fun y : puncturedClosedBall E ↦ ‖((y : closedBall (0 : E) 1) : E)‖) (hnorm y)).neg
    have hrange (y : puncturedClosedBall E) :
        (PiLp.equivOfUnique 2 ℝ fun _ : Fin 1 ↦ ℝ).symm
          (-Real.log ‖((y : closedBall (0 : E) 1) : E)‖) ∈ range (𝓡∂ 1) := by
      rw [range_modelWithCornersEuclideanHalfSpace, mem_ofPred_eq]
      simpa using Real.log_nonpos (norm_nonneg _) (mem_closedBall_zero_iff.1 y.1.2)
    exact ((𝓡∂ 1).contMDiffOn_symm.comp_contMDiff hcoord hrange).congr fun y ↦ by
      rw [ballCollarInv_snd, Function.comp_apply, EuclideanHalfSpace.normalRay_eq_symm]

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
@[simp]
theorem mem_ballCollarChart_target {y : EuclideanHalfSpace (n + 1)} :
    y ∈ (ballCollarChart ψ).target ↔
      (EuclideanHalfSpace.collarDiffeomorph (k := ⊤) n).symm y ∈ ψ.target := by
  simp only [ballCollarChart, OpenPartialHomeomorph.transHomeomorph_target,
    OpenPartialHomeomorph.trans_target, OpenPartialHomeomorph.symm_target,
    ballCollarPartialHomeomorph_source, preimage_univ, inter_univ, mem_preimage,
    Diffeomorph.coe_toHomeomorph_symm]

/-- Collar charts induced by charts of the maximal atlas of the unit sphere times the half-line lie
in the maximal atlas of the closed unit ball. -/
theorem ballCollarChart_mem_maximalAtlas {k : ℕ∞ω}
    (hψ : ψ ∈ IsManifold.maximalAtlas ((𝓡 n).prod (𝓡∂ 1)) k
      (sphere (0 : E) 1 × EuclideanHalfSpace 1)) :
    ballCollarChart ψ ∈ IsManifold.maximalAtlas (𝓡∂ (n + 1)) k (closedBall (0 : E) 1) := by
  have : IsManifold (𝓡∂ (n + 1)) k (closedBall (0 : E) 1) := .of_le le_top
  have : IsManifold ((𝓡 n).prod (𝓡∂ 1)) k (sphere (0 : E) 1 × EuclideanHalfSpace 1) :=
    .of_le le_top
  refine OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn _ ?_ ?_
  · have h₁ : ContMDiffOn (𝓡∂ (n + 1)) ((𝓡 n).prod (𝓡∂ 1)) k
        (ψ ∘ (ballCollarPartialHomeomorph E (n := n)).symm)
        ((ballCollarPartialHomeomorph E (n := n)).symm.trans ψ).source := by
      rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source]
      exact (contMDiffOn_of_mem_maximalAtlas hψ).comp
        (contMDiffOn_ballCollarPartialHomeomorph_symm.mono inter_subset_left) fun y hy ↦ hy.2
    exact (EuclideanHalfSpace.contMDiff_collarDiffeomorph_modelProd n).comp_contMDiffOn h₁
  · have h := (contMDiff_ballCollar (E := E) (k := k)).comp_contMDiffOn
      ((contMDiffOn_symm_of_mem_maximalAtlas hψ).comp
        (EuclideanHalfSpace.contMDiff_collarDiffeomorph_symm_modelProd n).contMDiffOn
        fun y hy ↦ mem_ballCollarChart_target.1 hy)
    exact h.congr fun y _ ↦ ballCollarChart_symm_apply y

/-- The collar chart of `ψ`, extended to the model vector space, reads the radial collar of `q` as
the model point of `ψ q` carried to `ℝⁿ⁺¹` by `collarAmbientEquiv`. -/
theorem ballCollarChart_extend_apply_ballCollar (q : sphere (0 : E) 1 × EuclideanHalfSpace 1) :
    (ballCollarChart ψ).extend (𝓡∂ (n + 1)) (ballCollar q) =
      EuclideanHalfSpace.collarAmbientEquiv n (((𝓡 n).prod (𝓡∂ 1)) (ψ q)) := by
  rw [OpenPartialHomeomorph.extend_coe, Function.comp_apply, ballCollarChart_apply_ballCollar,
    EuclideanHalfSpace.model_collarDiffeomorph]

/-- The inverse of the extended collar chart of `ψ` sends the model point of `u` to the radial
collar of the inverse of `ψ` at the point of `ℝⁿ × [0, ∞)` corresponding to `u`. -/
theorem ballCollarChart_extend_symm_apply (u : EuclideanHalfSpace (n + 1)) :
    ((ballCollarChart ψ).extend (𝓡∂ (n + 1))).symm ((𝓡∂ (n + 1)) u) =
      ballCollar (ψ.symm ((EuclideanHalfSpace.collarDiffeomorph (k := ⊤) n).symm u)) := by
  rw [OpenPartialHomeomorph.extend_coe_symm, Function.comp_apply, ModelWithCorners.left_inv,
    ballCollarChart_symm_apply]

/-- A point lies in the source of the collar chart of `ψ` restricted to the radial collar of an
open set `W` exactly when it is the radial collar of a point of `W` in the source of `ψ`. -/
theorem mem_ballCollarChart_restr_source {W : Set (sphere (0 : E) 1 × EuclideanHalfSpace 1)}
    (hW : IsOpen W) {y : closedBall (0 : E) 1} :
    y ∈ ((ballCollarChart ψ).restr (ballCollar '' W)).source ↔
      ∃ p ∈ W, p ∈ ψ.source ∧ ballCollar p = y := by
  rw [OpenPartialHomeomorph.restr_source' _ _ (isOpenEmbedding_ballCollar.isOpenMap W hW),
    mem_inter_iff, mem_ballCollarChart_source]
  constructor
  · rintro ⟨⟨p, hp, rfl⟩, p', hp', hpp'⟩
    rw [isOpenEmbedding_ballCollar.injective hpp'] at hp'
    exact ⟨p, hp', hp, rfl⟩
  · rintro ⟨p, hpW, hp, rfl⟩
    exact ⟨⟨p, hp, rfl⟩, mem_image_of_mem _ hpW⟩

/-! ### Immersions read in the radial collars -/

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] {m : ℕ}
  [Fact (finrank ℝ F = m + 1)]

omit [InnerProductSpace ℝ F] [Fact (finrank ℝ F = m + 1)] in
/-- **Maps read in collar charts.** Let `ψ` and `ψ'` be charts of the unit sphere times the
half-line for `F` and for `E`, and `G` a map between these products. In the extended collar
charts of `ψ` and `ψ'`, the map `ballCollar ∘ G` read at the chart preimage of `u` is `G` read in
the extended charts `ψ` and `ψ'`, conjugated by the linear collar identifications
`EuclideanHalfSpace.collarAmbientEquiv`. -/
theorem ballCollarChart_extend_ballCollar_apply
    (ψ : OpenPartialHomeomorph (sphere (0 : F) 1 × EuclideanHalfSpace 1)
      (ModelProd (EuclideanSpace ℝ (Fin m)) (EuclideanHalfSpace 1)))
    (ψ' : OpenPartialHomeomorph (sphere (0 : E) 1 × EuclideanHalfSpace 1)
      (ModelProd (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace 1)))
    (G : sphere (0 : F) 1 × EuclideanHalfSpace 1 → sphere (0 : E) 1 × EuclideanHalfSpace 1)
    (u : EuclideanHalfSpace (m + 1)) :
    (ballCollarChart ψ').extend (𝓡∂ (n + 1))
        (ballCollar (G (ψ.symm ((EuclideanHalfSpace.collarDiffeomorph (k := ⊤) m).symm u)))) =
      EuclideanHalfSpace.collarAmbientEquiv n
        ((ψ'.extend ((𝓡 n).prod (𝓡∂ 1)) ∘ G ∘ (ψ.extend ((𝓡 m).prod (𝓡∂ 1))).symm)
          ((EuclideanHalfSpace.collarAmbientEquiv m).symm ((𝓡∂ (m + 1)) u))) := by
  have hu : (EuclideanHalfSpace.collarAmbientEquiv m).symm ((𝓡∂ (m + 1)) u) =
      ((𝓡 m).prod (𝓡∂ 1)) ((EuclideanHalfSpace.collarDiffeomorph (k := ⊤) m).symm u) :=
    (EuclideanHalfSpace.collarDiffeomorph_symm_apply_coe m u).symm
  rw [ballCollarChart_extend_apply_ballCollar, hu]
  simp only [Function.comp_apply, OpenPartialHomeomorph.extend_coe_symm,
    OpenPartialHomeomorph.extend_coe, ModelWithCorners.left_inv]

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
  -- The domain chart is the collar chart of the normal-form domain chart of `G`, restricted to
  -- the collar of `W`, where `Φ` reads as `G`; the codomain chart is the collar chart of the
  -- normal-form codomain chart of `G`. In these charts `Φ` is the normal form of `G` transported
  -- along `collarAmbientEquiv`.
  obtain ⟨W, hWeq, hW, hqW⟩ := eventually_nhds_iff.1 hΦ
  simp only [Function.comp_apply] at hWeq
  set dom := (ballCollarChart hG.domChart).restr (ballCollar '' W)
  set cod := ballCollarChart (E := E) hG.codChart
  have hsource {p} (hp : p ∈ W) (hpd : p ∈ hG.domChart.source) :
      Φ (ballCollar p) ∈ cod.source := by
    rw [hWeq p hp]
    exact mem_ballCollarChart_source.2 ⟨G p, hG.source_subset_preimage_source hpd, rfl⟩
  let equiv : (EuclideanSpace ℝ (Fin (m + 1)) × hG.complement) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (n + 1)) :=
    ((EuclideanHalfSpace.collarAmbientEquiv m).symm.prodCongr
      (ContinuousLinearEquiv.refl ℝ hG.complement)).trans
      (hG.equiv.trans (EuclideanHalfSpace.collarAmbientEquiv n))
  refine IsImmersionAt.mk_of_charts equiv dom cod ?_ ?_ ?_ ?_ ?_ ?_
  · exact (mem_ballCollarChart_restr_source hW).2 ⟨q, hqW, hG.mem_domChart_source, rfl⟩
  · exact hsource hqW hG.mem_domChart_source
  · exact restr_mem_maximalAtlas _ (ballCollarChart_mem_maximalAtlas hG.domChart_mem_maximalAtlas)
      (isOpenEmbedding_ballCollar.isOpenMap W hW)
  · exact ballCollarChart_mem_maximalAtlas hG.codChart_mem_maximalAtlas
  · intro y hy
    obtain ⟨p, hp, hpd, rfl⟩ := (mem_ballCollarChart_restr_source hW).1 hy
    exact hsource hp hpd
  · intro u hu
    have hu' := hu
    rw [OpenPartialHomeomorph.extend_target'] at hu'
    obtain ⟨u', hut, rfl⟩ := hu'
    -- The point of the product whose collar is the chart preimage of `u`.
    set p := hG.domChart.symm ((EuclideanHalfSpace.collarDiffeomorph (k := ⊤) m).symm u')
    have hsymm : (dom.extend (𝓡∂ (m + 1))).symm ((𝓡∂ (m + 1)) u') = ballCollar p := by
      simpa [dom] using ballCollarChart_extend_symm_apply (ψ := hG.domChart) u'
    have hmem : ballCollar p ∈ dom.source := by
      rw [← hsymm, ← dom.extend_source (I := 𝓡∂ (m + 1))]
      exact (dom.extend (𝓡∂ (m + 1))).map_target hu
    obtain ⟨p', hp', -, hpp'⟩ := (mem_ballCollarChart_restr_source hW).1 hmem
    rw [isOpenEmbedding_ballCollar.injective hpp'] at hp'
    -- The normal form of `G` at the corresponding point of the model of the product.
    have hv : (EuclideanHalfSpace.collarAmbientEquiv m).symm ((𝓡∂ (m + 1)) u') ∈
        (hG.domChart.extend ((𝓡 m).prod (𝓡∂ 1))).target := by
      rw [OpenPartialHomeomorph.restr_target] at hut
      rw [OpenPartialHomeomorph.extend_target']
      exact ⟨_, mem_ballCollarChart_target.1 hut.1,
        EuclideanHalfSpace.collarDiffeomorph_symm_apply_coe m u'⟩
    rw [Function.comp_apply, Function.comp_apply, hsymm, hWeq p hp',
      ballCollarChart_extend_ballCollar_apply, hG.writtenInCharts hv]
    rfl

/-- **A map that is a cone near a collar point is an immersion there.** Let `g` be a map of the
unit sphere of `F` into the unit sphere of `E` which is an immersion at `q.1`. If near `q` the map
`Φ` of closed unit balls is the cone `exp (-s) • u ↦ exp (-s) • g u` over `g`, then `Φ` is an
immersion at `ballCollar q`, also when `q` has normal coordinate `0`, so that `ballCollar q` lies
on the boundary sphere. The cone point `0` is not in the range of the collar and is not covered. -/
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
