/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Defs

import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.Constructions
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import TauCeti.Analysis.Calculus.ParametricIntegral
import TauCeti.Geometry.Manifold.ContMDiff.Prod

/-!
# Partial derivatives of maps with a manifold parameter

Let `Φ : E × G → F` be a `C^n` map on an open set, where `E` and `F` are normed spaces and `G` is
a manifold without boundary. For a fixed parameter `g`, the map `x ↦ Φ (x, g)` is a `C^n` map
between normed spaces, with ordinary iterated derivatives. This file proves that these partial
derivatives of every order `k ≤ n` are jointly continuous in `(x, g)`
(`ContMDiffOn.continuousOn_iteratedFDeriv_partial`). The proof reads the parameter in a chart of
`G`, where it becomes `ContDiffOn.continuousOn_iteratedFDeriv_partial` for a parameter in a normed
space.

Joint continuity of the partial derivatives is the hypothesis under which derivatives pass under
an integral over a compact parameter space
(`TauCeti.contDiffOn_integral_smul_of_continuousOn_iteratedFDeriv`), for instance an average over
a compact Lie group acting smoothly.
-/

public section

open Set Function
open scoped Topology Manifold ContDiff

section PartialDerivatives

variable {E F EG HG G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedAddCommGroup EG] [NormedSpace ℝ EG] [TopologicalSpace HG]
  {IG : ModelWithCorners ℝ EG HG} [IG.Boundaryless] [TopologicalSpace G] [ChartedSpace HG G]
  {n : WithTop ℕ∞} [IsManifold IG n G]

/-- **Continuity of partial derivatives with a manifold parameter.** If `Φ : E × G → F` is `C^n`
on an open set `W`, where `G` is a manifold without boundary, then for every `k ≤ n` the `k`-th
derivative of `x ↦ Φ (x, p.2)` at `p.1` is continuous in `p` on `W`. -/
theorem ContMDiffOn.continuousOn_iteratedFDeriv_partial {Φ : E × G → F} {W : Set (E × G)}
    (hΦ : ContMDiffOn (𝓘(ℝ, E).prod IG) 𝓘(ℝ, F) n Φ W) (hW : IsOpen W) {k : ℕ}
    (hk : (k : WithTop ℕ∞) ≤ n) :
    ContinuousOn (fun p : E × G ↦ iteratedFDeriv ℝ k (fun x ↦ Φ (x, p.2)) p.1) W := by
  intro p hp
  set ψ := extChartAt IG p.2
  -- Read the parameter in the chart `ψ` of `G` at `p.2`, where `Φ` becomes a `C^n` map on an
  -- open subset of the normed space `E × EG`.
  let j : E × EG → E × G := fun q ↦ (q.1, ψ.symm q.2)
  let O : Set (E × EG) := (univ ×ˢ ψ.target) ∩ j ⁻¹' W
  have hj : ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ, EG)) (𝓘(ℝ, E).prod IG) n j (univ ×ˢ ψ.target) :=
    contMDiffOn_fst.prodMk ((contMDiffOn_extChartAt_symm p.2).comp contMDiffOn_snd
      fun q hq ↦ hq.2)
  have hO : IsOpen O :=
    hj.continuousOn.isOpen_inter_preimage (isOpen_univ.prod (isOpen_extChartAt_target p.2)) hW
  have hΦj : ContDiffOn ℝ n (Φ ∘ j) O := by
    rw [← contMDiffOn_iff_contDiffOn, ← contMDiffOn_prod_modelWithCornersSelf_iff]
    exact hΦ.comp (hj.mono inter_subset_left) fun q hq ↦ hq.2
  have hmem : (p.1, ψ p.2) ∈ O :=
    ⟨⟨mem_univ _, mem_extChartAt_target p.2⟩, by simpa [j, ψ, extChartAt_to_inv] using hp⟩
  have hc : ContinuousAt (fun q : E × G ↦ (q.1, ψ q.2)) p :=
    continuousAt_fst.prodMk ((continuousAt_extChartAt p.2).comp continuousAt_snd)
  have h := ((hΦj.continuousOn_iteratedFDeriv_partial hO hk).continuousAt
    (hO.mem_nhds hmem)).comp (x := p) hc
  refine (h.congr ?_).continuousWithinAt
  filter_upwards [continuousAt_snd.preimage_mem_nhds (extChartAt_source_mem_nhds (I := IG) p.2)]
    with q hq
  simp only [comp_apply, j, ψ, (extChartAt IG p.2).left_inv hq]

end PartialDerivatives
