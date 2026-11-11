/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import TauCeti.Analysis.Calculus.ContDiff.FinInsertNth
public import TauCeti.Geometry.Manifold.IsManifold.RestrictScalars
public import TauCeti.Topology.Algebra.Projectivization

/-!
# Projective space as an analytic manifold

For a nontrivially normed field `𝕜`, the standard affine charts
`Projectivization.affineOpenPartialHomeomorph i` identify the open sets `U_i = {[v] | v i ≠ 0}` of
the projective space `ℙ 𝕜 (Fin (n + 1) → 𝕜)`, with its quotient topology, with the affine space
`Fin n → 𝕜`. Their transition maps divide the homogeneous coordinates `Fin.insertNth i 1 z` by one
of their entries, so they are analytic where defined. Hence these `n + 1` charts form an atlas
making projective space a manifold modelled on `𝓘(𝕜, Fin n → 𝕜)` at every order of smoothness
`r`, including the analytic order `ω`.

Over `ℂ` this is the standard complex manifold structure on complex projective space `ℂℙⁿ`, and
over `ℝ` the standard smooth structure on real projective space `ℝℙⁿ`.

## Main declarations

* `Projectivization.instChartedSpace`: the atlas of standard affine charts.
* `Projectivization.contDiffOn_affineChart_symm_trans`: the transition maps are `C^r` for
  every `r`.
* `Projectivization.instIsManifold`: projective space is a `C^r` manifold for every `r`.
* `Projectivization.instIsManifoldReal`: over a normed `ℝ`-algebra, such as `ℂ`, it is also a real
  `C^r` manifold with the same charts.
* `Projectivization.affineOpenPartialHomeomorph_mem_maximalAtlas`: the affine charts lie in the
  maximal atlas of either manifold structure.
* `Projectivization.contMDiffOn_affineChart` and `Projectivization.contMDiff_affineChart_symm`:
  the affine charts and their inverses are `C^r` maps.
* `Projectivization.contMDiff_of_contDiffOn_mk`: a function on projective space given by a `C^r`
  function of the nonzero homogeneous coordinates is `C^r`.

## References

* P. Griffiths and J. Harris, *Principles of Algebraic Geometry*, Chapter 0, §1.
* The atlas `range affineOpenPartialHomeomorph`, the choice of `chartAt` through
  `exists_mem_affineOpen`, and the proof of the manifold instance by `isManifold_of_contDiffOn`
  are adapted from the sphere-quotient construction of `TauCeti.ComplexProjectiveSpace` in
  `TauCeti.Geometry.Manifold.Instances.ComplexProjectiveSpace`.
-/

public section

open Set
open scoped ContDiff Manifold LinearAlgebra.Projectivization

namespace Projectivization

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : ℕ}

/-- The atlas of projective space consisting of its `n + 1` standard affine charts. -/
noncomputable instance instChartedSpace : ChartedSpace (Fin n → 𝕜) (ℙ 𝕜 (Fin (n + 1) → 𝕜)) where
  atlas := range affineOpenPartialHomeomorph
  chartAt x := affineOpenPartialHomeomorph (exists_mem_affineOpen x).choose
  mem_chart_source x := by
    simpa using (exists_mem_affineOpen x).choose_spec
  chart_mem_atlas _ := mem_range_self _

/-- The charts of the atlas of projective space are exactly its standard affine charts. -/
theorem mem_atlas_iff (e : OpenPartialHomeomorph (ℙ 𝕜 (Fin (n + 1) → 𝕜)) (Fin n → 𝕜)) :
    e ∈ atlas (Fin n → 𝕜) (ℙ 𝕜 (Fin (n + 1) → 𝕜)) ↔ ∃ i, affineOpenPartialHomeomorph i = e :=
  Iff.rfl

/-- Each standard affine chart belongs to the atlas of projective space. -/
theorem affineOpenPartialHomeomorph_mem_atlas (i : Fin (n + 1)) :
    affineOpenPartialHomeomorph i ∈ atlas (Fin n → 𝕜) (ℙ 𝕜 (Fin (n + 1) → 𝕜)) :=
  mem_range_self i

/-- The transition maps between the standard affine charts of projective space are `C^r` for
every `r`, including the analytic order `ω`. -/
theorem contDiffOn_affineChart_symm_trans (i j : Fin (n + 1)) (r : ℕ∞ω) :
    ContDiffOn 𝕜 r ((affineChart i).symm.trans (affineChart j))
      ((affineChart (K := 𝕜) i).symm.trans (affineChart j)).source := by
  rw [affineChart_symm_trans_source]
  exact (Fin.contDiffOn_insertNth_one_div i j).congr fun z _ ↦ affineChart_symm_trans_apply i j z

/-- Projective space over a nontrivially normed field, with its standard affine charts, is a
`C^r` manifold for every `r`; for `r = ω` it is an analytic manifold. Over `ℂ` this is the
standard complex manifold structure on `ℂℙⁿ`. -/
instance instIsManifold (r : ℕ∞ω) :
    IsManifold 𝓘(𝕜, Fin n → 𝕜) r (ℙ 𝕜 (Fin (n + 1) → 𝕜)) := by
  apply isManifold_of_contDiffOn
  rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
  simpa using contDiffOn_affineChart_symm_trans i j r

/-- Projective space over a normed `ℝ`-algebra `𝕜` is, with the same affine charts, a real `C^r`
manifold for every `r`. Over `ℂ` this is the underlying real smooth structure of `ℂℙⁿ`, modelled
on `𝓘(ℝ, Fin n → ℂ)`. -/
instance instIsManifoldReal [NormedAlgebra ℝ 𝕜] (r : ℕ∞ω) :
    IsManifold 𝓘(ℝ, Fin n → 𝕜) r (ℙ 𝕜 (Fin (n + 1) → 𝕜)) :=
  (instIsManifold r).restrictScalars ℝ

section Model

variable {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedSpace 𝕜' (Fin n → 𝕜)]

/-- Each standard affine chart lies in the maximal atlas of any `C^r` manifold structure on
projective space built on its atlas, such as `𝓘(𝕜, Fin n → 𝕜)` or, over a normed `ℝ`-algebra,
`𝓘(ℝ, Fin n → 𝕜)`. -/
theorem affineOpenPartialHomeomorph_mem_maximalAtlas
    {I : ModelWithCorners 𝕜' (Fin n → 𝕜) (Fin n → 𝕜)} {r : ℕ∞ω}
    [IsManifold I r (ℙ 𝕜 (Fin (n + 1) → 𝕜))] (i : Fin (n + 1)) :
    affineOpenPartialHomeomorph i ∈ IsManifold.maximalAtlas I r (ℙ 𝕜 (Fin (n + 1) → 𝕜)) :=
  IsManifold.subset_maximalAtlas (affineOpenPartialHomeomorph_mem_atlas i)

/-- For a trivial model `𝓘(𝕜', Fin n → 𝕜)`, the extended standard affine chart of `i` is the
affine chart itself. -/
theorem affineOpenPartialHomeomorph_extend_apply (i : Fin (n + 1)) (x : ℙ 𝕜 (Fin (n + 1) → 𝕜)) :
    (affineOpenPartialHomeomorph i).extend 𝓘(𝕜', Fin n → 𝕜) x = affineChart i x := by
  rw [OpenPartialHomeomorph.extend_coe, Function.comp_apply, modelWithCornersSelf_coe, id_eq,
    coe_affineOpenPartialHomeomorph]

/-- For a trivial model `𝓘(𝕜', Fin n → 𝕜)`, the extended standard affine chart of `i` sends the
coordinate point `[eᵢ]` to `0`. -/
theorem affineOpenPartialHomeomorph_extend_mk_single (i : Fin (n + 1)) :
    (affineOpenPartialHomeomorph i).extend 𝓘(𝕜', Fin n → 𝕜) (mk 𝕜 (Pi.single i 1) (by simp)) =
      0 := by
  rw [affineOpenPartialHomeomorph_extend_apply, affineChart_mk_single]

end Model

/-- Each standard affine chart of projective space is a `C^r` map on its domain. -/
theorem contMDiffOn_affineChart (i : Fin (n + 1)) (r : ℕ∞ω) :
    ContMDiffOn 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) r (affineChart i) (affineOpen (K := 𝕜) i) := by
  simpa using contMDiffOn_of_mem_maximalAtlas
    (IsManifold.subset_maximalAtlas (n := r) (affineOpenPartialHomeomorph_mem_atlas (𝕜 := 𝕜) i))

/-- The inverse `z ↦ [Fin.insertNth i 1 z]` of each standard affine chart of projective space is
a `C^r` map. -/
theorem contMDiff_affineChart_symm (i : Fin (n + 1)) (r : ℕ∞ω) :
    ContMDiff 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) r (affineChart (K := 𝕜) i).symm := by
  rw [← contMDiffOn_univ]
  simpa using contMDiffOn_symm_of_mem_maximalAtlas
    (IsManifold.subset_maximalAtlas (n := r) (affineOpenPartialHomeomorph_mem_atlas (𝕜 := 𝕜) i))

/-- A function on projective space with values in a normed space, given in homogeneous coordinates
by a function `F` which is `C^r` on the nonzero vectors, is `C^r`; for `r = ω` it is analytic.
On the affine open at `i` it is `z ↦ F (Fin.insertNth i 1 z)` read in the chart at `i`. -/
theorem contMDiff_of_contDiffOn_mk {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {f : ℙ 𝕜 (Fin (n + 1) → 𝕜) → E} {F : (Fin (n + 1) → 𝕜) → E} {r : ℕ∞ω}
    (hF : ContDiffOn 𝕜 r F {v | v ≠ 0}) (hf : ∀ v (hv : v ≠ 0), f (mk 𝕜 v hv) = F v) :
    ContMDiff 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, E) r f := by
  intro x
  obtain ⟨i, hi⟩ := exists_mem_affineOpen x
  have hG : ContDiff 𝕜 r fun z : Fin n → 𝕜 ↦ F (Fin.insertNth (α := fun _ ↦ 𝕜) i 1 z) :=
    hF.comp_contDiff ((contDiff_const (c := (1 : 𝕜))).finInsertNth (F := fun _ ↦ 𝕜) i
      contDiff_id) fun z ↦ Fin.insertNth_one_ne_zero i z
  refine ((hG.contMDiff.comp_contMDiffOn (contMDiffOn_affineChart i r)).congr fun y hy ↦ ?_)
    |>.contMDiffAt ((isOpen_affineOpen i).mem_nhds hi)
  obtain ⟨z, rfl⟩ : ∃ z, (affineChart i).symm z = y :=
    ⟨_, (affineChart i).left_inv (by simpa using hy)⟩
  rw [Function.comp_apply, (affineChart i).right_inv (by simp), affineChart_symm_apply, hf]

end Projectivization
