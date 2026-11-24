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
import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
import TauCeti.Geometry.Lie.Subgroup.Embedded
import TauCeti.Geometry.Manifold.TubularNeighborhood.NearestPoint
import TauCeti.Topology.Algebra.Star.Unitary

/-!
# The nearest-point retraction onto a closed subgroup of the unitary group

Let `G` be a closed subgroup of `U(n) = Matrix.unitaryGroup n 𝕜` (over `ℝ` or `ℂ`), viewed as a
compact subset of the real inner product space of `n × n` matrices with the Frobenius inner
product. This file constructs the nearest-point retraction `π_G` onto `G`
(`ClosedSubgroup.nearestPoint`): a chosen point of `G` nearest to a matrix `M`. By the
closed-subgroup theorem `G` is a compact embedded submanifold of the matrices, so the tubular
neighbourhood theorem `TauCeti.exists_isOpenEmbedding_normalTube` and the smoothness of the
nearest-point map `TauCeti.exists_contMDiffOn_nearestPoint_retraction` apply. They give `ε > 0`
such that on the neighbourhood `𝒰 = {M : dist(M, G) < ε}` (`ClosedSubgroup.exists_pos_nearestPoint`)

* the nearest point of `G` to `M` is unique,
* `π_G` is smooth, and
* `π_G (g + v) = g` for every `g ∈ G` and every `v` orthogonal to the tangent space `g 𝔤` of `G`
  at `g` with `‖v‖ < ε`.

The last property uses that the image of the differential of the inclusion of `G` lies in the
tangent cone of `G`, which is `g 𝔤` (`ClosedSubgroup.tangentConeAt_eq_matrixTangentSpace`), so a
vector orthogonal to `g 𝔤` is normal in the sense of the tubular neighbourhood theorem.

Every point of `G` has Frobenius norm `√(card n)`, so every point of `G` is a nearest point of `G`
to `0`. Hence, as soon as `G` is not the trivial group, `0` has no unique nearest point and lies
outside `𝒰` (`ClosedSubgroup.zero_notMem_thickening`).

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

open Set Metric Function
open scoped Matrix Manifold ContDiff InnerProductSpace

namespace ClosedSubgroup

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]
  (G : ClosedSubgroup (Matrix.unitaryGroup n 𝕜))

open scoped Matrix.Norms.Frobenius

/-- A closed subgroup of `U(n)` is compact as a set of matrices. -/
theorem isCompact_image_coe :
    IsCompact (((↑) : Matrix.unitaryGroup n 𝕜 → Matrix n n 𝕜) '' G) :=
  G.isClosed'.isCompact.image continuous_subtypeVal

/-- The **nearest-point retraction** `π_G` onto a closed subgroup `G` of `U(n)`: a chosen point of
`G` nearest to `M` for the Frobenius distance. On a neighbourhood of `G` this nearest point is
unique and depends smoothly on `M` (`ClosedSubgroup.exists_pos_nearestPoint`). -/
def nearestPoint (M : Matrix n n 𝕜) : Matrix n n 𝕜 :=
  (G.isCompact_image_coe.exists_isMinOn ⟨1, 1, G.one_mem, rfl⟩
    (continuous_const.dist continuous_id (f := fun _ ↦ M)).continuousOn).choose

/-- `π_G M` lies in `G`. -/
theorem nearestPoint_mem (M : Matrix n n 𝕜) :
    G.nearestPoint M ∈ ((↑) : Matrix.unitaryGroup n 𝕜 → Matrix n n 𝕜) '' G :=
  (G.isCompact_image_coe.exists_isMinOn ⟨1, 1, G.one_mem, rfl⟩
    (continuous_const.dist continuous_id (f := fun _ ↦ M)).continuousOn).choose_spec.1

/-- `π_G M` is a point of `G` nearest to `M`. -/
theorem isMinOn_nearestPoint (M : Matrix n n 𝕜) :
    IsMinOn (dist M) (((↑) : Matrix.unitaryGroup n 𝕜 → Matrix n n 𝕜) '' G) (G.nearestPoint M) :=
  (G.isCompact_image_coe.exists_isMinOn ⟨1, 1, G.one_mem, rfl⟩
    (continuous_const.dist continuous_id (f := fun _ ↦ M)).continuousOn).choose_spec.2

/-- `π_G` is the identity on `G`. -/
theorem nearestPoint_coe {g : Matrix.unitaryGroup n 𝕜} (hg : g ∈ G) :
    G.nearestPoint g = g := by
  have h : dist (g : Matrix n n 𝕜) (G.nearestPoint g) ≤ dist (g : Matrix n n 𝕜) g :=
    G.isMinOn_nearestPoint g ⟨g, hg, rfl⟩
  rw [dist_self] at h
  exact (dist_le_zero.mp h).symm

section Manifold

/-- The topology of the Frobenius norm on matrices, selected so that the units of the Frobenius
normed algebra receive their charts. It is the entrywise topology up to unfolding. -/
private abbrev frobeniusTopologicalSpace : TopologicalSpace (Matrix n n 𝕜) :=
  (Matrix.frobeniusSeminormedAddCommGroup (m := n) (n := n) (α := 𝕜)).toPseudoMetricSpace
    |>.toUniformSpace |>.toTopologicalSpace

attribute [local instance] frobeniusTopologicalSpace

/-- The closed subgroup of the units of the matrices carried by `G`. -/
private def toUnits : Subgroup (Matrix n n 𝕜)ˣ :=
  (G : Subgroup (Matrix.unitaryGroup n 𝕜)).map Unitary.toUnits

private theorem isCompact_toUnits : IsCompact (G.toUnits : Set (Matrix n n 𝕜)ˣ) :=
  G.isClosed'.isCompact.image Unitary.continuous_toUnits

/-- The inclusion of the units of `G` into the matrices. -/
private def coeUnits (k : G.toUnits) : Matrix n n 𝕜 :=
  ((k : (Matrix n n 𝕜)ˣ) : Matrix n n 𝕜)

private theorem range_coeUnits :
    range G.coeUnits = ((↑) : Matrix.unitaryGroup n 𝕜 → Matrix n n 𝕜) '' G := by
  ext M
  constructor
  · rintro ⟨⟨_, g, hg, rfl⟩, rfl⟩
    exact ⟨g, hg, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨Unitary.toUnits g, g, hg, rfl⟩, rfl⟩

private theorem injective_coeUnits : Injective G.coeUnits :=
  fun _ _ h ↦ Subtype.ext (Units.ext h)

/-- The closed-subgroup charts on `G`, as a subgroup of the units of the matrices. -/
private def chartData : TauCeti.Lie.EmbeddedLieSubgroupData 𝓘(ℝ, Matrix n n 𝕜) G.toUnits
    (TauCeti.Lie.lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix n n 𝕜)) G.toUnits).toSubmodule :=
  TauCeti.Lie.EmbeddedLieSubgroupData.ofIsClosed G.isCompact_toUnits.isClosed

private instance instChartedSpaceToUnits :
    ChartedSpace (TauCeti.Lie.lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix n n 𝕜))
      G.toUnits).toSubmodule G.toUnits :=
  G.chartData.chartedSpace

private instance instLieGroupToUnits :
    LieGroup 𝓘(ℝ, (TauCeti.Lie.lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix n n 𝕜))
      G.toUnits).toSubmodule) ∞ G.toUnits :=
  G.chartData.lieGroup

private instance instCompactSpaceToUnits : CompactSpace G.toUnits :=
  isCompact_iff_compactSpace.mp G.isCompact_toUnits

private theorem contMDiff_coeUnits :
    ContMDiff 𝓘(ℝ, (TauCeti.Lie.lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix n n 𝕜))
      G.toUnits).toSubmodule) 𝓘(ℝ, Matrix n n 𝕜) ∞ G.coeUnits :=
  (Units.contMDiff_val (𝕜 := ℝ)).comp G.chartData.contMDiff_subtypeVal

/-- `Units.val` is the chart of the units, so its differential is invertible. -/
private theorem injective_mfderiv_val (u : (Matrix n n 𝕜)ˣ) :
    Injective (mfderiv 𝓘(ℝ, Matrix n n 𝕜) 𝓘(ℝ, Matrix n n 𝕜) Units.val u) := by
  obtain ⟨L, hL⟩ := isInvertible_mfderiv_extChartAt (I := 𝓘(ℝ, Matrix n n 𝕜))
    (mem_extChartAt_source (I := 𝓘(ℝ, Matrix n n 𝕜)) u)
  have : (extChartAt 𝓘(ℝ, Matrix n n 𝕜) u : (Matrix n n 𝕜)ˣ → Matrix n n 𝕜) = Units.val := rfl
  rw [← this, ← hL]
  exact L.injective

private theorem injective_mfderiv_coeUnits (k : G.toUnits) :
    Injective (mfderiv 𝓘(ℝ, (TauCeti.Lie.lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix n n 𝕜))
      G.toUnits).toSubmodule) 𝓘(ℝ, Matrix n n 𝕜) G.coeUnits k) := by
  have hcomp : G.coeUnits = Units.val ∘ fun x : G.toUnits ↦ (x : (Matrix n n 𝕜)ˣ) := rfl
  rw [hcomp, mfderiv_comp k ((Units.contMDiff_val (𝕜 := ℝ) (n := ∞)).mdifferentiableAt (by simp))
    (G.chartData.contMDiff_subtypeVal.mdifferentiableAt (by simp)), ContinuousLinearMap.coe_comp]
  exact (injective_mfderiv_val _).comp (G.chartData.injective_mfderiv_subtypeVal k)

/-- A vector orthogonal to the tangent space `g 𝔤` of `G` is normal to the inclusion of `G` at
`g`: the differential of the inclusion takes values in the tangent cone of `G`, which is `g 𝔤`. -/
private theorem mem_normalSubspace_of_mem_orthogonal (g : G) {v : Matrix n n 𝕜}
    (hv : v ∈ (G.matrixTangentSpace g)ᗮ) :
    v ∈ TauCeti.normalSubspace 𝓘(ℝ, (TauCeti.Lie.lieSubalgebraOfSubgroup
      (I := 𝓘(ℝ, Matrix n n 𝕜)) G.toUnits).toSubmodule) G.coeUnits
        ⟨Unitary.toUnits g, g, g.property, rfl⟩ := by
  let k : G.toUnits := ⟨Unitary.toUnits g, g, g.property, rfl⟩
  let D : (TauCeti.Lie.lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix n n 𝕜))
      G.toUnits).toSubmodule →L[ℝ] Matrix n n 𝕜 :=
    mfderiv 𝓘(ℝ, (TauCeti.Lie.lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix n n 𝕜))
      G.toUnits).toSubmodule) 𝓘(ℝ, Matrix n n 𝕜) G.coeUnits k
  have htan (u) : D u ∈ G.matrixTangentSpace g := by
    have hd := ((G.contMDiff_coeUnits.mdifferentiableAt (x := k) (by simp)).hasMFDerivAt).2
    simp only [modelWithCornersSelf_coe, range_id, hasFDerivWithinAt_univ] at hd
    have hu := hd.hasFDerivWithinAt.mapsTo_tangent_cone (s := univ)
      (by rw [tangentConeAt_univ]; exact mem_univ u)
    simp only [writtenInExtChartAt, extChartAt_model_space_eq_id, image_univ,
      PartialEquiv.refl_coe, Function.id_comp, Function.comp_apply, extChartAt_to_inv] at hu
    rw [← SetLike.mem_coe, ← tangentConeAt_eq_matrixTangentSpace]
    refine tangentConeAt_mono ?_ hu
    rintro _ ⟨y, rfl⟩
    exact G.range_coeUnits ▸ ⟨_, rfl⟩
  exact TauCeti.mem_normalSubspace_iff.mpr fun u ↦
    Submodule.inner_left_of_mem_orthogonal (htan u) hv

/-- **The nearest-point retraction from the tubular neighbourhood theorem**, in terms of the
closed-subgroup charts on `G`. -/
private theorem exists_pos_nearestPoint_aux :
    ∃ ε > 0, ContDiffOn ℝ ∞ G.nearestPoint
        (thickening ε (((↑) : Matrix.unitaryGroup n 𝕜 → Matrix n n 𝕜) '' G)) ∧
      (∀ M ∈ thickening ε (((↑) : Matrix.unitaryGroup n 𝕜 → Matrix n n 𝕜) '' G),
        ∀ A ∈ ((↑) : Matrix.unitaryGroup n 𝕜 → Matrix n n 𝕜) '' G,
          IsMinOn (dist M) (((↑) : Matrix.unitaryGroup n 𝕜 → Matrix n n 𝕜) '' G) A →
            A = G.nearestPoint M) ∧
      ∀ g : G, ∀ v ∈ (G.matrixTangentSpace g)ᗮ, ‖v‖ < ε →
        G.nearestPoint ((g : Matrix n n 𝕜) + v) = g := by
  have : IsManifold 𝓘(ℝ, (TauCeti.Lie.lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix n n 𝕜))
      G.toUnits).toSubmodule) (∞ + 1) G.toUnits := IsManifold.of_le (n := ∞) (by simp)
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
  have hπ : ∀ M ∈ thickening δ (range G.coeUnits), G.nearestPoint M = G.coeUnits (r M) :=
    fun M hM ↦ hr' M hM _ (G.range_coeUnits ▸ G.nearestPoint_mem M)
      (G.range_coeUnits ▸ G.isMinOn_nearestPoint M)
  refine ⟨δ, hδ, ?_, fun M hM A hA hAmin ↦ (hr' M hM A hA hAmin).trans (hπ M hM).symm, ?_⟩
  · have h := hf.comp_contMDiffOn hr
    rw [contMDiffOn_iff_contDiffOn] at h
    exact h.congr hπ
  · intro g v hv hvδ
    -- A vector orthogonal to `g 𝔤` is normal to `G` at `g`, so `r (g + v) = g`.
    have hrk := TauCeti.eq_fst_of_isMinOn_dist_of_mem_normalTube (hf.mdifferentiable (by simp))
      (injOn_iff_injective.mpr hemb.injective) (p := (⟨Unitary.toUnits g, g, g.property, rfl⟩, v))
      (TauCeti.mem_normalTube.mpr ⟨G.mem_normalSubspace_of_mem_orthogonal g hv,
        hvδ.trans_le hδε⟩) (hmin _)
    have hM : (g : Matrix n n 𝕜) + v ∈ thickening δ (range G.coeUnits) :=
      mem_thickening_iff.mpr ⟨g, ⟨⟨Unitary.toUnits g, g, g.property, rfl⟩, rfl⟩,
        by simpa [dist_eq_norm] using hvδ⟩
    rw [hπ _ hM]
    exact congrArg G.coeUnits hrk

end Manifold

/-- **The nearest-point retraction onto `G`.** There is `ε > 0` such that, on the neighbourhood
`𝒰 = {M : dist(M, G) < ε}` of `G`, the retraction `π_G` is smooth, `π_G M` is the unique point of
`G` nearest to `M`, and `π_G (g + v) = g` for every `g ∈ G` and every `v` orthogonal to the tangent
space `g 𝔤` of `G` at `g` with `‖v‖ < ε`. -/
theorem exists_pos_nearestPoint :
    ∃ ε > 0, ContDiffOn ℝ ∞ G.nearestPoint
        (thickening ε (((↑) : Matrix.unitaryGroup n 𝕜 → Matrix n n 𝕜) '' G)) ∧
      (∀ M ∈ thickening ε (((↑) : Matrix.unitaryGroup n 𝕜 → Matrix n n 𝕜) '' G),
        ∀ A ∈ ((↑) : Matrix.unitaryGroup n 𝕜 → Matrix n n 𝕜) '' G,
          IsMinOn (dist M) (((↑) : Matrix.unitaryGroup n 𝕜 → Matrix n n 𝕜) '' G) A →
            A = G.nearestPoint M) ∧
      ∀ g : G, ∀ v ∈ (G.matrixTangentSpace g)ᗮ, ‖v‖ < ε →
        G.nearestPoint ((g : Matrix n n 𝕜) + v) = g :=
  G.exists_pos_nearestPoint_aux

/-- A unitary matrix has squared Frobenius norm `card n`. -/
private theorem norm_sq_coe_unitary (u : Matrix.unitaryGroup n 𝕜) :
    ‖(u : Matrix n n 𝕜)‖ ^ 2 = Fintype.card n := by
  have h := inner_self_eq_norm_sq_to_K (𝕜 := 𝕜) (u : Matrix n n 𝕜)
  rw [Matrix.frobenius_inner_eq_trace_conjTranspose_mul, ← Matrix.star_eq_conjTranspose,
    Matrix.UnitaryGroup.star_mul_self, Matrix.trace_one] at h
  exact_mod_cast h.symm

/-- **`0` lies outside `𝒰` for a nontrivial `G`.** Every point of `G` has Frobenius norm
`√(card n)`, so every point of `G` is a nearest point to `0`. If nearest points are unique on the
`ε`-neighbourhood of `G` and `G` has a point other than `1`, then `0` is not in that
neighbourhood. -/
theorem zero_notMem_thickening {ε : ℝ}
    (huniq : ∀ M ∈ thickening ε (((↑) : Matrix.unitaryGroup n 𝕜 → Matrix n n 𝕜) '' G),
      ∀ A ∈ ((↑) : Matrix.unitaryGroup n 𝕜 → Matrix n n 𝕜) '' G,
        IsMinOn (dist M) (((↑) : Matrix.unitaryGroup n 𝕜 → Matrix n n 𝕜) '' G) A →
          A = G.nearestPoint M)
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
      ((norm_sq_coe_unitary u).trans (norm_sq_coe_unitary w).symm)).le
  have h1 := huniq 0 h0 _ ⟨1, G.one_mem, rfl⟩ (hmin 1)
  have hg' := huniq 0 h0 _ ⟨g, hg, rfl⟩ (hmin g)
  exact hg1 (Subtype.ext (hg'.trans h1.symm))

end ClosedSubgroup
