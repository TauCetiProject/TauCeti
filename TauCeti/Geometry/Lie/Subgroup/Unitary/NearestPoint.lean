/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Topology.MetricSpace.Thickening
public import TauCeti.Analysis.Matrix.Frobenius
public import TauCeti.Geometry.Lie.Subgroup.Unitary.TangentSpace
import TauCeti.Geometry.Lie.Subgroup.Embedded
import TauCeti.Geometry.Lie.Subgroup.Unitary.Retraction
import TauCeti.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
import TauCeti.Geometry.Manifold.TangentCone.Basic
import TauCeti.Geometry.Manifold.TubularNeighborhood.NearestPoint
import TauCeti.Topology.Algebra.Star.Unitary

/-!
# The nearest-point retraction onto a closed subgroup of the unitary group

Let `G` be a closed subgroup of `U(n) = Matrix.unitaryGroup n 𝕜` (over `ℝ` or `ℂ`), viewed as a
compact subset of the real inner product space of `n × n` matrices with the Frobenius inner
product. This file constructs the nearest-point retraction `π_G` onto `G`
(`ClosedSubgroup.matrixNearestPoint`): a chosen point of `G` nearest to a matrix `M`. By the
closed-subgroup theorem `G` is a compact embedded submanifold of the matrices, so the tubular
neighbourhood theorem `TauCeti.exists_isOpenEmbedding_normalTube` and the smoothness of the
nearest-point map `TauCeti.exists_contMDiffOn_nearestPoint_retraction` apply. They give `ε > 0`
such that on the neighbourhood `𝒰 = {M : dist(M, G) < ε}`
(`ClosedSubgroup.exists_pos_contDiffOn_matrixNearestPoint`)

* the nearest point of `G` to `M` is unique,
* `π_G` is smooth, and
* `π_G (g + v) = g` for every `g ∈ G` and every `v` orthogonal to the tangent space `g 𝔤` of `G`
  at `g` with `‖v‖ < ε`.

The last property uses that the image of the differential of the inclusion of `G` lies in the
tangent cone of `G`, which is `g 𝔤` (`ClosedSubgroup.tangentConeAt_eq_matrixTangentSpace`), so a
vector orthogonal to `g 𝔤` is normal in the sense of the tubular neighbourhood theorem.

It follows (`ClosedSubgroup.fderiv_matrixNearestPoint`) that the derivative of `π_G` at `g ∈ G` is
the orthogonal projection onto `g 𝔤`: `π_G` is the identity on `G`, and constant along short
segments normal to `g 𝔤`, which is what `ClosedSubgroup.fderiv_eq_starProjection_matrixTangentSpace`
needs. For every matrix `M`, the residual `M - π_G M` is orthogonal to the tangent space of `G` at
`π_G M` (`ClosedSubgroup.inner_sub_matrixNearestPoint_eq_zero`). For `G = U(n)` the derivative at
`1` is the skew-Hermitian part `H ↦ (H - Hᴴ) / 2`
(`ClosedSubgroup.fderiv_matrixNearestPoint_one_of_forall_mem`), and for a countable `G`, such as
the finite group `{±1}`, it vanishes
(`ClosedSubgroup.fderiv_matrixNearestPoint_eq_zero_of_countable`).

Every point of `G` has Frobenius norm `√(card n)`, so every point of `G` is a nearest point of `G`
to `0`. Hence, as soon as `G` is not the trivial group, `0` has no unique nearest point and lies
outside `𝒰` (`ClosedSubgroup.zero_notMem_thickening_image_coe_matrix`).

The manifold structure on `G` comes from the closed-subgroup theorem applied to `G` as a closed
subgroup of the units of the matrices, normed by the Frobenius norm. The Frobenius norm is a scoped
instance; this file opens `Matrix.Norms.Frobenius`.

## References

* S.-J. Oh and D. Tataru, *The hyperbolic Yang–Mills equation for connections in an arbitrary
  topological class*, Comm. Math. Phys. 365 (2019), arXiv:1709.08604 (the nearest-point
  projection onto `G`).
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer (2013), Theorem 6.24.
-/

public section

noncomputable section

open Set Metric Function Filter
open scoped Matrix Manifold ContDiff InnerProductSpace Topology

attribute [local instance 100] LieRing.ofAssociativeRing

namespace ClosedSubgroup

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]
  (G : ClosedSubgroup (Matrix.unitaryGroup n 𝕜))

open scoped Matrix.Norms.Frobenius

/-- Some point of the compact set `G` is nearest to `M`. -/
private theorem exists_isMinOn_dist (M : Matrix n n 𝕜) :
    ∃ A ∈ ((↑) : Matrix.unitaryGroup n 𝕜 → Matrix n n 𝕜) '' G,
      IsMinOn (dist M) (((↑) : Matrix.unitaryGroup n 𝕜 → Matrix n n 𝕜) '' G) A :=
  G.isCompact_image_coe_matrix.exists_isMinOn ⟨1, 1, G.one_mem, rfl⟩
    (continuous_const.dist continuous_id (f := fun _ ↦ M)).continuousOn

/-- The **nearest-point retraction** `π_G` onto a closed subgroup `G` of `U(n)`: a chosen point of
`G` nearest to `M` for the Frobenius distance. On a neighbourhood of `G` this nearest point is
unique and depends smoothly on `M` (`ClosedSubgroup.exists_pos_contDiffOn_matrixNearestPoint`). -/
def matrixNearestPoint (M : Matrix n n 𝕜) : Matrix n n 𝕜 :=
  (G.exists_isMinOn_dist M).choose

/-- `π_G M` lies in `G`. -/
theorem matrixNearestPoint_mem (M : Matrix n n 𝕜) :
    G.matrixNearestPoint M ∈ ((↑) : Matrix.unitaryGroup n 𝕜 → Matrix n n 𝕜) '' G :=
  (G.exists_isMinOn_dist M).choose_spec.1

/-- `π_G M` is a point of `G` nearest to `M`. -/
theorem isMinOn_matrixNearestPoint (M : Matrix n n 𝕜) :
    IsMinOn (dist M) (((↑) : Matrix.unitaryGroup n 𝕜 → Matrix n n 𝕜) '' G)
      (G.matrixNearestPoint M) :=
  (G.exists_isMinOn_dist M).choose_spec.2

/-- `π_G` is the identity on `G`. -/
@[simp]
theorem matrixNearestPoint_coe {g : Matrix.unitaryGroup n 𝕜} (hg : g ∈ G) :
    G.matrixNearestPoint g = g := by
  have h : dist (g : Matrix n n 𝕜) (G.matrixNearestPoint g) ≤ dist (g : Matrix n n 𝕜) g :=
    G.isMinOn_matrixNearestPoint g ⟨g, hg, rfl⟩
  rw [dist_self] at h
  exact (dist_le_zero.mp h).symm

section Manifold

/-- The topology of the Frobenius norm on matrices (`Matrix.frobeniusTopologicalSpace`), selected
so that the units of the Frobenius normed algebra receive their charts. It is private so that, under
the module system, only the private declarations of this section see it: the statement of
`ClosedSubgroup.exists_pos_contDiffOn_matrixNearestPoint`, including the type of `G`, keeps the
entrywise topology on matrices. -/
private abbrev frobeniusTopologicalSpace : TopologicalSpace (Matrix n n 𝕜) :=
  Matrix.frobeniusTopologicalSpace n n 𝕜

attribute [local instance] frobeniusTopologicalSpace

private theorem isCompact_toGL : IsCompact (G.toGL : Set (Matrix n n 𝕜)ˣ) :=
  G.coe_toGL ▸ G.isClosed'.isCompact.image <| by
    rw [show frobeniusTopologicalSpace = _ from Matrix.frobeniusTopologicalSpace_eq n n 𝕜]
    exact Unitary.continuous_toUnits

/-- The inclusion of the units of `G` into the matrices. -/
private def coeUnits (k : G.toGL) : Matrix n n 𝕜 :=
  ((k : (Matrix n n 𝕜)ˣ) : Matrix n n 𝕜)

/-- A point of `G`, as a point of the units of `G`. -/
private def toGLPoint (g : G) : G.toGL :=
  ⟨Unitary.toUnits g, toUnits_mem_toGL g.property⟩

private theorem coeUnits_toGLPoint (g : G) : G.coeUnits (G.toGLPoint g) = g :=
  Unitary.val_toUnits_apply _

private theorem range_coeUnits :
    range G.coeUnits = ((↑) : Matrix.unitaryGroup n 𝕜 → Matrix n n 𝕜) '' G := by
  ext M
  constructor
  · rintro ⟨⟨_, hu⟩, rfl⟩
    obtain ⟨g, hg, rfl⟩ := mem_toGL.mp hu
    exact ⟨g, hg, (G.coeUnits_toGLPoint ⟨g, hg⟩).symm⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨G.toGLPoint ⟨g, hg⟩, G.coeUnits_toGLPoint ⟨g, hg⟩⟩

private theorem injective_coeUnits : Injective G.coeUnits :=
  fun _ _ h ↦ Subtype.ext (Units.ext h)

/-- The closed-subgroup charts on `G`, as a subgroup of the units of the matrices. -/
private def chartData : TauCeti.Lie.EmbeddedLieSubgroupData 𝓘(ℝ, Matrix n n 𝕜) G.toGL
    (TauCeti.Lie.lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix n n 𝕜)) G.toGL).toSubmodule :=
  TauCeti.Lie.EmbeddedLieSubgroupData.ofIsClosed G.isCompact_toGL.isClosed

private instance instChartedSpaceToGL :
    ChartedSpace (TauCeti.Lie.lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix n n 𝕜))
      G.toGL).toSubmodule G.toGL :=
  G.chartData.chartedSpace

private instance instLieGroupToGL :
    LieGroup 𝓘(ℝ, (TauCeti.Lie.lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix n n 𝕜))
      G.toGL).toSubmodule) ∞ G.toGL :=
  G.chartData.lieGroup

private instance instCompactSpaceToGL : CompactSpace G.toGL :=
  isCompact_iff_compactSpace.mp G.isCompact_toGL

private theorem contMDiff_coeUnits :
    ContMDiff 𝓘(ℝ, (TauCeti.Lie.lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix n n 𝕜))
      G.toGL).toSubmodule) 𝓘(ℝ, Matrix n n 𝕜) ∞ G.coeUnits :=
  (Units.contMDiff_val (𝕜 := ℝ)).comp G.chartData.contMDiff_subtypeVal

private theorem injective_mfderiv_coeUnits (k : G.toGL) :
    Injective (mfderiv 𝓘(ℝ, (TauCeti.Lie.lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix n n 𝕜))
      G.toGL).toSubmodule) 𝓘(ℝ, Matrix n n 𝕜) G.coeUnits k) := by
  have hcomp : G.coeUnits = Units.val ∘ fun x : G.toGL ↦ (x : (Matrix n n 𝕜)ˣ) := rfl
  rw [hcomp, mfderiv_comp k ((Units.contMDiff_val (𝕜 := ℝ) (n := ∞)).mdifferentiableAt (by simp))
    (G.chartData.contMDiff_subtypeVal.mdifferentiableAt (by simp)), ContinuousLinearMap.coe_comp]
  obtain ⟨L, hL⟩ := Units.isInvertible_mfderiv_val (𝕜 := ℝ) (k : (Matrix n n 𝕜)ˣ)
  exact hL ▸ L.injective.comp (G.chartData.injective_mfderiv_subtypeVal k)

/-- A vector orthogonal to the tangent space `g 𝔤` of `G` is normal to the inclusion of `G` at
`g`: the differential of the inclusion takes values in the tangent cone of `G`, which is `g 𝔤`. -/
private theorem mem_normalSubspace_of_mem_orthogonal (g : G) {v : Matrix n n 𝕜}
    (hv : v ∈ (G.matrixTangentSpace g)ᗮ) :
    v ∈ TauCeti.normalSubspace 𝓘(ℝ, (TauCeti.Lie.lieSubalgebraOfSubgroup
      (I := 𝓘(ℝ, Matrix n n 𝕜)) G.toGL).toSubmodule) G.coeUnits (G.toGLPoint g) := by
  let k : G.toGL := G.toGLPoint g
  let D : (TauCeti.Lie.lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix n n 𝕜))
      G.toGL).toSubmodule →L[ℝ] Matrix n n 𝕜 :=
    mfderiv 𝓘(ℝ, (TauCeti.Lie.lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix n n 𝕜))
      G.toGL).toSubmodule) 𝓘(ℝ, Matrix n n 𝕜) G.coeUnits k
  have htan (u) : D u ∈ G.matrixTangentSpace g := by
    have hmaps := HasMFDerivWithinAt.mapsTo_mtangentConeAt (s := univ)
      (G.contMDiff_coeUnits.mdifferentiableAt (x := k) (by simp)).hasMFDerivAt.hasMFDerivWithinAt
    have hu := hmaps (x := u) <| by
      simp only [TauCeti.mtangentConeAt_def, preimage_univ, univ_inter, modelWithCornersSelf_coe,
        range_id, tangentConeAt_univ]
      exact mem_univ _
    rw [image_univ, TauCeti.mtangentConeAt_eq_tangentConeAt, G.coeUnits_toGLPoint,
      G.range_coeUnits] at hu
    rw [← SetLike.mem_coe, ← tangentConeAt_eq_matrixTangentSpace]
    exact hu
  exact TauCeti.mem_normalSubspace_iff.mpr fun u ↦
    Submodule.inner_left_of_mem_orthogonal (htan u) hv

/-- **The nearest-point retraction onto `G`.** There is `ε > 0` such that, on the neighbourhood
`𝒰 = {M : dist(M, G) < ε}` of `G`, the retraction `π_G` is smooth, `π_G M` is the unique point of
`G` nearest to `M`, and `π_G (g + v) = g` for every `g ∈ G` and every `v` orthogonal to the tangent
space `g 𝔤` of `G` at `g` with `‖v‖ < ε`. -/
theorem exists_pos_contDiffOn_matrixNearestPoint :
    ∃ ε > 0, ContDiffOn ℝ ∞ G.matrixNearestPoint
        (thickening ε (((↑) : Matrix.unitaryGroup n 𝕜 → Matrix n n 𝕜) '' G)) ∧
      (∀ M ∈ thickening ε (((↑) : Matrix.unitaryGroup n 𝕜 → Matrix n n 𝕜) '' G),
        ∀ A ∈ ((↑) : Matrix.unitaryGroup n 𝕜 → Matrix n n 𝕜) '' G,
          IsMinOn (dist M) (((↑) : Matrix.unitaryGroup n 𝕜 → Matrix n n 𝕜) '' G) A →
            A = G.matrixNearestPoint M) ∧
      ∀ g : G, ∀ v ∈ (G.matrixTangentSpace g)ᗮ, ‖v‖ < ε →
        G.matrixNearestPoint ((g : Matrix n n 𝕜) + v) = g := by
  have : IsManifold 𝓘(ℝ, (TauCeti.Lie.lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix n n 𝕜))
      G.toGL).toSubmodule) (∞ + 1) G.toGL := IsManifold.of_le (n := ∞) (by simp)
  have hf := G.contMDiff_coeUnits
  obtain ⟨ε, hε, hemb⟩ := TauCeti.exists_isOpenEmbedding_normalTube (hf.of_le (by simp))
    G.injective_mfderiv_coeUnits G.injective_coeUnits
  obtain ⟨δ, hδ, hδε, r, hr, -, hmin, huniq⟩ :=
    TauCeti.exists_contMDiffOn_nearestPoint_retraction (n := ∞) (hf.of_le (by simp)) (by simp)
      G.injective_mfderiv_coeUnits hε (injOn_iff_injective.mpr hemb.injective)
  rw [← G.range_coeUnits]
  -- On the neighbourhood, every nearest point of `G` is the image of `r`.
  have hr' : ∀ M ∈ thickening δ (range G.coeUnits), ∀ A ∈ range G.coeUnits,
      IsMinOn (dist M) (range G.coeUnits) A → A = G.coeUnits (r M) := by
    rintro M hM _ ⟨z, rfl⟩ hA
    rw [huniq M (thickening_mono hδε _ hM) z fun w _ ↦ hA ⟨w, rfl⟩]
  have hπ : ∀ M ∈ thickening δ (range G.coeUnits), G.matrixNearestPoint M = G.coeUnits (r M) :=
    fun M hM ↦ hr' M hM _ (G.range_coeUnits ▸ G.matrixNearestPoint_mem M)
      (G.range_coeUnits ▸ G.isMinOn_matrixNearestPoint M)
  refine ⟨δ, hδ, ?_, fun M hM A hA hAmin ↦ (hr' M hM A hA hAmin).trans (hπ M hM).symm, ?_⟩
  · have h := hf.comp_contMDiffOn hr
    rw [contMDiffOn_iff_contDiffOn] at h
    exact h.congr hπ
  · intro g v hv hvδ
    -- A vector orthogonal to `g 𝔤` is normal to `G` at `g`, so `r (g + v) = g`.
    have hrk := TauCeti.eq_fst_of_isMinOn_dist_of_mem_normalTube (hf.mdifferentiable (by simp))
      (injOn_iff_injective.mpr hemb.injective)
      (p := (G.toGLPoint g, v))
      (TauCeti.mem_normalTube.mpr ⟨G.mem_normalSubspace_of_mem_orthogonal g hv,
        hvδ.trans_le hδε⟩) (hmin _)
    have hM : (g : Matrix n n 𝕜) + v ∈ thickening δ (range G.coeUnits) :=
      mem_thickening_iff.mpr ⟨g, ⟨G.toGLPoint g, G.coeUnits_toGLPoint g⟩,
        by simpa [dist_eq_norm] using hvδ⟩
    simp only [G.coeUnits_toGLPoint] at hrk
    rw [hπ _ hM, hrk, G.coeUnits_toGLPoint]

end Manifold

/-- **The derivative of `π_G` on `G`.** At `g ∈ G`, the derivative of the nearest-point
retraction is the orthogonal projection onto the tangent space `g 𝔤`. -/
theorem fderiv_matrixNearestPoint (g : G) :
    fderiv ℝ G.matrixNearestPoint g = (G.matrixTangentSpace g).starProjection := by
  obtain ⟨ε, hε, hsmooth, -, hnormal⟩ := G.exists_pos_contDiffOn_matrixNearestPoint
  have hg : (g : Matrix n n 𝕜) ∈
      thickening ε (((↑) : Matrix.unitaryGroup n 𝕜 → Matrix n n 𝕜) '' G) :=
    self_subset_thickening hε _ ⟨g, g.property, rfl⟩
  refine fderiv_eq_starProjection_matrixTangentSpace
    ((hsmooth.contDiffAt (isOpen_thickening.mem_nhds hg)).differentiableAt (by simp))
    (fun _ hh ↦ G.matrixNearestPoint_coe hh) fun v hv ↦ ?_
  -- `π_G (g + t v) = g` once `‖t v‖ < ε`.
  have hlim : Tendsto (fun t : ℝ ↦ ‖t‖ * ‖v‖) (𝓝 0) (𝓝 0) :=
    (continuous_norm.mul continuous_const).tendsto' 0 0 (by simp)
  filter_upwards [hlim.eventually (gt_mem_nhds hε)] with t ht
  exact hnormal g _ (Submodule.smul_mem _ t hv) ((norm_smul t v).trans_lt ht)

/-- **The residual of `π_G` is normal to `G`.** For every matrix `M`, `M - π_G M` is orthogonal to
the tangent space `g 𝔤` of `G` at `g = π_G M`. -/
theorem inner_sub_matrixNearestPoint_eq_zero (M : Matrix n n 𝕜) {g : G}
    (hg : G.matrixNearestPoint M = g) {V : Matrix n n 𝕜} (hV : V ∈ G.matrixTangentSpace g) :
    ⟪M - G.matrixNearestPoint M, V⟫_ℝ = 0 := by
  rw [hg]
  exact inner_sub_eq_zero_of_isLocalMinOn (hg ▸ (G.isMinOn_matrixNearestPoint M).isLocalMinOn) hV

variable {G}

/-- **The derivative of `π_{U(n)}` at `1`.** For `G = U(n)`, the derivative of the nearest-point
retraction at `1` is the skew-Hermitian part `H ↦ (H - Hᴴ) / 2`, the orthogonal projection onto the
Lie algebra of skew-Hermitian matrices. For `n = 1` and `𝕜 = ℂ` this is `a + i b ↦ i b`. -/
theorem fderiv_matrixNearestPoint_one_of_forall_mem (hG : ∀ g, g ∈ G) (H : Matrix n n 𝕜) :
    fderiv ℝ G.matrixNearestPoint 1 H = (2⁻¹ : ℝ) • (H - Hᴴ) := by
  have h1 : (((1 : G) : Matrix.unitaryGroup n 𝕜) : Matrix n n 𝕜) = 1 := by simp
  rw [← h1, fderiv_matrixNearestPoint, matrixTangentSpace_one]
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ fun W hW ↦ ?_
  · rw [LieSubalgebra.mem_toSubmodule,
      mem_matrixLieAlgebra_iff_conjTranspose_eq_neg_of_forall_mem hG, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose]
    simp [smul_sub]
  -- The remainder `H - (H - Hᴴ) / 2 = (H + Hᴴ) / 2` is Hermitian, and `W` is skew-Hermitian.
  refine Matrix.IsHermitian.frobenius_real_inner_eq_zero_of_conjTranspose_eq_neg ?_
    ((mem_matrixLieAlgebra_iff_conjTranspose_eq_neg_of_forall_mem hG).mp hW)
  simp only [Matrix.IsHermitian, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_conjTranspose, star_trivial]
  module

/-- **The derivative of `π_G` for a countable `G`.** If `G` is countable, for instance finite such
as `{±1}`, its Lie algebra is `0`, so the derivative of the nearest-point retraction at every
`g ∈ G` is `0`, the projection onto the zero space. -/
theorem fderiv_matrixNearestPoint_eq_zero_of_countable
    (hG : (G : Set (Matrix.unitaryGroup n 𝕜)).Countable) (g : G) :
    fderiv ℝ G.matrixNearestPoint g = 0 := by
  have hbot : G.matrixTangentSpace g = ⊥ := by
    rw [eq_bot_iff]
    intro V hV
    have h0 := eq_zero_of_mem_matrixLieAlgebra_of_countable hG (mem_matrixTangentSpace_iff.mp hV)
    have hV' : V = (g : Matrix n n 𝕜) * (star (g : Matrix n n 𝕜) * V) := by simp [← mul_assoc]
    rw [Submodule.mem_bot, hV', h0, mul_zero]
  -- `fderiv` is taken for the entrywise topology `instTopologicalSpaceMatrix` and the projection
  -- for the Frobenius-norm topology, which agree (`Matrix.frobeniusTopologicalSpace_eq`).
  -- Evaluating at `H` compares the two maps through their values, which are plain matrices.
  ext H : 1
  have h : fderiv ℝ G.matrixNearestPoint g H = (G.matrixTangentSpace g).starProjection H :=
    DFunLike.congr_fun (G.fderiv_matrixNearestPoint g) H
  rw [h, hbot, Submodule.starProjection_bot, zero_apply, zero_apply]

/-- **`0` lies outside `𝒰` for a nontrivial `G`.** Every point of `G` has Frobenius norm
`√(card n)`, so every point of `G` is a nearest point to `0`. If nearest points are unique on the
`ε`-neighbourhood of `G` and `G` has a point other than `1`, then `0` is not in that
neighbourhood. -/
theorem zero_notMem_thickening_image_coe_matrix {ε : ℝ}
    (huniq : ∀ M ∈ thickening ε (((↑) : Matrix.unitaryGroup n 𝕜 → Matrix n n 𝕜) '' G),
      ∀ A ∈ ((↑) : Matrix.unitaryGroup n 𝕜 → Matrix n n 𝕜) '' G,
        IsMinOn (dist M) (((↑) : Matrix.unitaryGroup n 𝕜 → Matrix n n 𝕜) '' G) A →
          A = G.matrixNearestPoint M)
    {g : Matrix.unitaryGroup n 𝕜} (hg : g ∈ G) (hg1 : g ≠ 1) :
    (0 : Matrix n n 𝕜) ∉ thickening ε (((↑) : Matrix.unitaryGroup n 𝕜 → Matrix n n 𝕜) '' G) := by
  intro h0
  -- All points of `G` are at the same distance from `0`.
  have hmin (u : Matrix.unitaryGroup n 𝕜) :
      IsMinOn (dist 0) (((↑) : Matrix.unitaryGroup n 𝕜 → Matrix n n 𝕜) '' G)
        (u : Matrix n n 𝕜) := by
    rintro _ ⟨w, -, rfl⟩
    simp only [mem_ofPred_eq, dist_zero_left]
    exact ((sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      ((Matrix.frobenius_norm_sq_of_mem_unitaryGroup _ u.property).trans
        (Matrix.frobenius_norm_sq_of_mem_unitaryGroup _ w.property).symm)).le
  have h1 := huniq 0 h0 _ ⟨1, G.one_mem, rfl⟩ (hmin 1)
  have hg' := huniq 0 h0 _ ⟨g, hg, rfl⟩ (hmin g)
  exact hg1 (Subtype.ext (hg'.trans h1.symm))

end ClosedSubgroup
