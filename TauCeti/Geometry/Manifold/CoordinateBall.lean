/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Geometry.Manifold.ChartedSpace
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.Orientation.Preserving
import Mathlib.Analysis.InnerProductSpace.Calculus
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.Orientation.Pullback
import TauCeti.Geometry.Manifold.Orientation.Reflection

/-!
# Coordinate balls

Let `X` be a Hausdorff space charted on a real normed space `E`. Finitely many points of `X` have
pairwise disjoint coordinate balls about them: for a finite `S ⊆ X` and `r > 0`, there is an open
embedding of `S × ball 0 r` into `X` sending `(s, 0)` to `s`. The proof builds each slice as the
inverse of the chart at `s` precomposed with an affine rescaling, and sends distinct slices into
the disjoint open sets given by `Set.Finite.t2_separation`.

On a boundaryless smooth manifold `M` modelled on a real inner product space `E`, a coordinate ball
can be taken to be the whole of `E`: every point `x` is the image of `0` under an open embedding
`E → M` which is a smooth local diffeomorphism
(`TauCeti.exists_isOpenEmbedding_isLocalDiffeomorph_apply_zero`). It is the inverse of the chart at
`x` precomposed with Mathlib's diffeomorphism `OpenPartialHomeomorph.univBall` of `E` onto a small
ball. These are the balls along which a connected sum is formed. For orientations `o` of `E` and
`oM` of `M`, with `E` finite-dimensional and nontrivial, the ball can moreover be chosen to
preserve orientation from `o` to `oM` at every point
(`TauCeti.exists_isOpenEmbedding_isLocalDiffeomorph_isOrientationPreservingAt`): as `E` is
connected, `o` is the orientation pulled back from `oM` along the ball or its opposite, and in the
second case the ball is precomposed with a reflection of `E`.

## Main results

* `Set.Finite.exists_isOpenEmbedding_prod_ball`: the open embedding of `S × ball 0 r`.
* `TauCeti.exists_isOpenEmbedding_isLocalDiffeomorph_apply_zero`: every point of a boundaryless
  manifold is the centre of a coordinate ball `E → M` which is a local diffeomorphism.
* `TauCeti.exists_isOpenEmbedding_isLocalDiffeomorph_isOrientationPreservingAt`: the ball can be
  chosen to preserve given orientations.
-/

public section

open Metric Set Topology

namespace Set.Finite

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace X] [T2Space X] [ChartedSpace E X] {S : Set X}

/-- **Disjoint coordinate balls about finitely many points.** For a finite set `S` and `r > 0`,
there is an open embedding of `S × ball 0 r` into `X` sending `(s, 0)` to `s`. -/
theorem exists_isOpenEmbedding_prod_ball (hS : S.Finite) {r : ℝ} (hr : 0 < r) :
    ∃ F : S × ball (0 : E) r → X, IsOpenEmbedding F ∧
      ∀ s, F (s, ⟨0, mem_ball_self hr⟩) = s := by
  have := hS.to_subtype
  obtain ⟨W, hW, hWd⟩ := hS.t2_separation
  -- In the chart at `s`, a ball of radius `ε s` about `s` lies in the target and maps into `W s`.
  have hε (s : S) : ∃ ε > 0, ball (chartAt E (s : X) s) ε ⊆
      (chartAt E (s : X)).target ∩ (chartAt E (s : X)).symm ⁻¹' W s :=
    isOpen_iff.1 ((chartAt E (s : X)).isOpen_inter_preimage_symm (hW s).2) _
      ⟨(chartAt E (s : X)).map_source (mem_chart_source E _), by
        simpa [(chartAt E (s : X)).left_inv (mem_chart_source E _)] using (hW s).1⟩
  choose ε hε₀ hεW using hε
  have hc (s : S) : ε s / r ≠ 0 := (div_pos (hε₀ s) hr).ne'
  -- The rescaling `z ↦ c s + (ε s / r) • z` sends `ball 0 r` into `ball (c s) (ε s)`.
  have hball (s : S) {z : E} (hz : z ∈ ball (0 : E) r) :
      chartAt E (s : X) s + (ε s / r) • z ∈ ball (chartAt E (s : X) s) (ε s) := by
    rw [mem_ball_zero_iff] at hz
    rw [mem_ball, dist_self_add_left, norm_smul]
    calc ‖ε s / r‖ * ‖z‖ < ‖ε s / r‖ * r := by gcongr; exact norm_pos_iff.2 (hc s)
      _ = ε s := by rw [Real.norm_of_nonneg (div_pos (hε₀ s) hr).le]; field_simp
  let g (s : S) (z : E) : X := (chartAt E (s : X)).symm (chartAt E (s : X) s + (ε s / r) • z)
  refine ⟨fun p ↦ g p.1 p.2, .of_continuous_injective_isOpenMap
    (continuous_prod_of_discrete_left.2 fun s ↦ ((chartAt E (s : X)).continuousOn_symm.comp
      (by fun_prop) fun z hz ↦ (hεW s (hball s hz)).1).comp_continuous continuous_subtype_val
        fun z ↦ z.2) (fun p q h ↦ ?_) (isOpenMap_prod_of_discrete_left.2 fun s U hU ↦ ?_),
    fun s ↦ by simp [g, (chartAt E (s : X)).left_inv (mem_chart_source E _)]⟩
  · -- The common value lies in `W p.1 ∩ W q.1`, so `p.1 = q.1`; charts are injective.
    obtain ⟨⟨s, hsS⟩, z, hz⟩ := p
    obtain ⟨⟨s', hs'S⟩, z', hz'⟩ := q
    have h₁ : g ⟨s, hsS⟩ z ∈ W s := (hεW ⟨s, hsS⟩ (hball ⟨s, hsS⟩ hz)).2
    have h₂ : g ⟨s', hs'S⟩ z' ∈ W s' := (hεW ⟨s', hs'S⟩ (hball _ hz')).2
    simp only at h
    obtain rfl : s = s' := hWd.elim hsS hs'S <| not_disjoint_iff.2 ⟨_, h₁, h ▸ h₂⟩
    have := (chartAt E s).symm.injOn (hεW ⟨s, hsS⟩ (hball _ hz)).1
      (hεW ⟨s, hsS⟩ (hball _ hz')).1 h
    simpa using smul_right_injective E (hc ⟨s, hsS⟩) (add_left_cancel this)
  · -- On a slice the map is a chart inverse after an affine homeomorphism of `E`.
    rw [← image_image (g s), ← image_image (chartAt E (s : X)).symm]
    exact (chartAt E (s : X)).isOpen_image_symm_of_subset_target
      (((isOpenMap_add_left _).comp (isOpenMap_smul₀ (hc s))) _
        (isOpen_ball.isOpenMap_subtype_val U hU))
      (by rintro _ ⟨_, ⟨z, -, rfl⟩, rfl⟩; exact (hεW s (hball s z.2)).1)

end Set.Finite

/-! ### Smooth and oriented coordinate balls -/

open scoped Manifold ContDiff
open TauCeti.Manifold.Orientation

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

/-- **Coordinate balls exist.** Every point `x` of a boundaryless `C^n` manifold modelled on a real
inner product space `E` is the image of `0` under an open embedding `E → M` which is a `C^n` local
diffeomorphism. -/
theorem exists_isOpenEmbedding_isLocalDiffeomorph_apply_zero {n : ℕ∞}
    [IsManifold 𝓘(ℝ, E) n M] (x : M) :
    ∃ e : E → M, IsOpenEmbedding e ∧ IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) n e ∧ e 0 = x := by
  set φ := chartAt E x
  obtain ⟨r, hr, hrφ⟩ : ∃ r > 0, ball (φ x) r ⊆ φ.target :=
    Metric.isOpen_iff.1 φ.open_target _ (mem_chart_target E x)
  -- A diffeomorphism of `E` onto a ball about `φ x` in the target of the chart.
  set u := OpenPartialHomeomorph.univBall (φ x) r
  have hu (v : E) : u v ∈ φ.target := by
    refine hrφ ?_
    rw [← OpenPartialHomeomorph.univBall_target (φ x) hr]
    exact u.map_source (by simp [u])
  refine ⟨u.trans φ.symm, (u.trans φ.symm).isOpenEmbedding ?_, fun v ↦ ?_, ?_⟩
  · simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source, u,
      OpenPartialHomeomorph.univBall_source, univ_inter, eq_univ_iff_forall]
    exact hu
  · have hU : IsLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, E) n u v :=
      isLocalDiffeomorphAt_of_eqOn (f := u) (Φ := PartialDiffeomorph.ofOpenPartialHomeomorph u
        OpenPartialHomeomorph.contDiff_univBall.contDiffOn
        (by rw [OpenPartialHomeomorph.univBall_target _ hr]
            exact OpenPartialHomeomorph.contDiffOn_univBall_symm))
        (by simp [u]) fun _ _ ↦ by simp
    rw [OpenPartialHomeomorph.coe_trans]
    exact hU.comp (hg := φ.isLocalDiffeomorphAt_symm_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas x) (hu v))
  · simp [u, φ]

variable [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι]

/-- **Oriented coordinate balls exist.** For orientations `o` of `E` and `oM` of a boundaryless
smooth manifold `M` modelled on a nontrivial finite-dimensional real inner product space `E`, every
point `x` of `M` is the image of `0` under an open embedding `E → M` which is a smooth local
diffeomorphism preserving orientation from `o` to `oM` at every point. -/
theorem exists_isOpenEmbedding_isLocalDiffeomorph_isOrientationPreservingAt [Nontrivial E]
    [IsManifold 𝓘(ℝ, E) ∞ M] (o : Manifold.Orientation 𝓘(ℝ, E) E ι)
    (oM : Manifold.Orientation 𝓘(ℝ, E) M ι) (x : M) :
    ∃ e : E → M, IsOpenEmbedding e ∧ IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ e ∧ e 0 = x ∧
      ∀ v, IsOrientationPreservingAt o oM e v := by
  obtain ⟨e, he, de, rfl⟩ :=
    exists_isOpenEmbedding_isLocalDiffeomorph_apply_zero (E := E) (n := ⊤) x
  have hdf (v : E) : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e v).IsInvertible :=
    (de v).isInvertible_mfderiv (by simp)
  have hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 1 e := de.contMDiff.of_le (by simp)
  -- `o` is the orientation pulled back along `e`, or its opposite, as `E` is connected.
  rcases o.eq_or_eq_neg (oM.pullback hf hdf o.card_eq) with h | h
  · exact ⟨e, he, de, rfl, fun v ↦ h ▸ isOrientationPreservingAt_pullback oM hf hdf _ v⟩
  -- In the second case, precompose `e` with a reflection of `E`, which reverses `o`.
  obtain ⟨u, hu⟩ := exists_ne (0 : E)
  set ρ := (ℝ ∙ u)ᗮ.reflection
  refine ⟨e ∘ ρ, he.comp (ρ.toHomeomorph.isOpenEmbedding : IsOpenEmbedding ρ),
    fun v ↦ (ρ.toContinuousLinearEquiv.toDiffeomorph.isLocalDiffeomorph v).comp (hg := de (ρ v)),
    by simp, fun v ↦ ?_⟩
  refine IsOrientationReversingAt.comp ?_ (isOrientationReversingAt_reflection o hu v)
  rw [h, isOrientationReversingAt_neg_left]
  exact isOrientationPreservingAt_pullback oM hf hdf _ _

end TauCeti
