/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Subgroup.ChartedSpace
public import Mathlib.Geometry.Manifold.Algebra.Monoid

/-!
# Smooth subgroup slice charts

An ambient smooth chart that identifies a subgroup with a linear slice induces a smooth atlas on
the subgroup. The transition between the preferred charts at `g` and `h` is obtained by inserting
the zero transverse coordinate, applying the ambient inverse chart, translating by `h⁻¹ * g`, and
then reading the tangential coordinate of the ambient chart.

## Main results

* `Subgroup.contDiffOn_preferredSliceChart_transition` proves that transitions between preferred
  subgroup slice charts are smooth.
* `Subgroup.isManifold_chartedSpaceOfIsSliceChart` equips the charted subgroup with a smooth
  manifold structure.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd edition (2013), Theorem 20.12.
* H. Hilgert and K.-H. Neeb, *Structure and Geometry of Lie Groups* (2012), Section 9.1.
-/

public section

namespace Subgroup

open Set
open scoped ContDiff Manifold Topology

section TransitionFormula

variable {G F F' : Type*} [Group G] [TopologicalSpace G]
  [TopologicalSpace F] [TopologicalSpace F'] [Zero F'] [ContinuousConstSMul G G]

/-- The transition from the preferred chart at `g` to the preferred chart at `h` is the
tangential coordinate of ambient translation by `h⁻¹ * g`, restricted to the zero transverse
slice. -/
theorem preferredSliceChart_transition_apply (K : Subgroup G)
    (e : OpenPartialHomeomorph G (F × F'))
    (he : TauCeti.IsSliceChart e ((univ : Set F) ×ˢ ({0} : Set F')) (K : Set G))
    (g h : K) {y : F}
    (hy : y ∈ ((preferredSliceChart K e he g).symm.trans
      (preferredSliceChart K e he h)).source) :
    ((preferredSliceChart K e he g).symm.trans
      (preferredSliceChart K e he h)) y =
        (e ((h : G)⁻¹ * ((g : G) * e.symm (y, 0)))).1 := by
  rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source] at hy
  have hytarget : (y, (0 : F')) ∈ e.target := by
    rw [preferredSliceChart_target] at hy
    exact hy.1
  rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply,
    preferredSliceChart_apply,
    coe_preferredSliceChart_symm_apply K e he g hytarget]

end TransitionFormula

section SmoothAtlas

variable {E H G F F' : Type*} {n : ℕ∞ω} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup F'] [NormedSpace ℝ F']
  [ContMDiffMul I n G]

/-- Transitions between preferred subgroup slice charts are smooth when the ambient slice chart
and its inverse are smooth. -/
theorem contDiffOn_preferredSliceChart_transition
    (K : Subgroup G) (e : OpenPartialHomeomorph G (F × F'))
    (he : TauCeti.IsSliceChart e ((univ : Set F) ×ˢ ({0} : Set F')) (K : Set G))
    (he' : ContMDiffOn I 𝓘(ℝ, F × F') n e e.source)
    (he_symm : ContMDiffOn 𝓘(ℝ, F × F') I n e.symm e.target)
    (g h : K) :
    let _ : ContinuousMul G := continuousMul_of_contMDiffMul I n
    ContDiffOn ℝ n
      ((preferredSliceChart K e he g).symm.trans
        (preferredSliceChart K e he h))
      ((preferredSliceChart K e he g).symm.trans
        (preferredSliceChart K e he h)).source := by
  dsimp only
  let _ : ContinuousMul G := continuousMul_of_contMDiffMul I n
  intro y hy
  rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source] at hy
  have hytarget : (y, (0 : F')) ∈ e.target := by
    rw [preferredSliceChart_target] at hy
    exact hy.1
  have hzsource : (h : G)⁻¹ * ((g : G) * e.symm (y, 0)) ∈ e.source := by
    have hdsource : (h : G)⁻¹ *
        ((↑((preferredSliceChart K e he g).symm y) : G)) ∈ e.source := by
      simpa only [preferredSliceChart_source,
        Homeomorph.transOpenPartialHomeomorph_source, Set.mem_preimage,
        Homeomorph.smul_symm_apply, smul_eq_mul] using hy.2
    rw [coe_preferredSliceChart_symm_apply K e he g hytarget] at hdsource
    exact hdsource
  have hzero : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, F × F') n
      (fun z : F => (z, (0 : F'))) :=
    (contDiff_prodMk_left (0 : F')).contMDiff
  have hinv : ContMDiffAt 𝓘(ℝ, F × F') I n e.symm (y, 0) :=
    he_symm.contMDiffAt (e.open_target.mem_nhds hytarget)
  have hleft : ContMDiffAt I I n
      (fun x : G => (h : G)⁻¹ * ((g : G) * x)) (e.symm (y, 0)) :=
    contMDiff_mul_left.contMDiffAt.comp _ contMDiff_mul_left.contMDiffAt
  have hforward : ContMDiffAt I 𝓘(ℝ, F × F') n e
      ((h : G)⁻¹ * ((g : G) * e.symm (y, 0))) :=
    he'.contMDiffAt (e.open_source.mem_nhds hzsource)
  have hinv0 : ContMDiffAt 𝓘(ℝ, F) I n
      (e.symm ∘ fun z : F => (z, (0 : F'))) y :=
    hinv.comp y hzero.contMDiffAt
  have htranslated : ContMDiffAt 𝓘(ℝ, F) I n
      ((fun x : G => (h : G)⁻¹ * ((g : G) * x)) ∘
        (e.symm ∘ fun z : F => (z, (0 : F')))) y :=
    hleft.comp y hinv0
  have hecoord : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, F × F') n
      (e ∘ ((fun x : G => (h : G)⁻¹ * ((g : G) * x)) ∘
        (e.symm ∘ fun z : F => (z, (0 : F'))))) y :=
    hforward.comp y htranslated
  have hsmooth : ContDiffAt ℝ n
      (fun z : F => (e ((h : G)⁻¹ * ((g : G) * e.symm (z, 0)))).1) y := by
    convert hecoord.contDiffAt.fst using 1
    ext z
    rfl
  exact hsmooth.contDiffWithinAt.congr_of_mem
    (fun z hz => preferredSliceChart_transition_apply K e he g h hz) hy

/-- The preferred charts induced by a smooth ambient slice chart make the subgroup a smooth
manifold. -/
theorem isManifold_chartedSpaceOfIsSliceChart
    (K : Subgroup G) (e : OpenPartialHomeomorph G (F × F'))
    (he : TauCeti.IsSliceChart e ((univ : Set F) ×ˢ ({0} : Set F')) (K : Set G))
    (h1 : (1 : G) ∈ e.source)
    (he' : ContMDiffOn I 𝓘(ℝ, F × F') n e e.source)
    (he_symm : ContMDiffOn 𝓘(ℝ, F × F') I n e.symm e.target) :
    let _ : ContinuousMul G := continuousMul_of_contMDiffMul I n
    let _ : ChartedSpace F K := chartedSpaceOfIsSliceChart K e he h1
    IsManifold 𝓘(ℝ, F) n K := by
  dsimp only
  let _ : ContinuousMul G := continuousMul_of_contMDiffMul I n
  let _ : ChartedSpace F K := chartedSpaceOfIsSliceChart K e he h1
  refine isManifold_of_contDiffOn 𝓘(ℝ, F) n K ?_
  rw [chartedSpaceOfIsSliceChart_atlas]
  rintro _ _ ⟨g, rfl⟩ ⟨h, rfl⟩
  simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_def, id_eq, preimage_id_eq, range_id, inter_univ] using
      contDiffOn_preferredSliceChart_transition K e he he' he_symm g h

end SmoothAtlas

end Subgroup
