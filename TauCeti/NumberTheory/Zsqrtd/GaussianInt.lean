/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.Topology.Instances.ZMultiples

/-!
# The Gaussian integers as a lattice in `ℂ`

The Gaussian integers `ℤ[i]`, embedded in `ℂ` by `GaussianInt.toComplex`, form a lattice: their
image is discrete, in the strong sense that only finitely many Gaussian integers lie in any compact
subset of `ℂ`, and it is cocompact, since every complex number differs from a Gaussian integer by an
element of the half-open unit square `[0, 1) × [0, 1)`.

These are the two inputs needed to show that a group built from Gaussian integers acts properly
discontinuously and cocompactly on a complex vector space, as for the Iwasawa manifold.

## Main results

* `GaussianInt.tendsto_toComplex_cofinite_cocompact`: the embedding `GaussianInt → ℂ` tends to
  infinity along the cofinite filter.
* `GaussianInt.exists_sub_mem_reProdIm_Ico`: every complex number differs from a Gaussian integer
  by an element of the half-open unit square.
-/

public section

open Filter Set

namespace GaussianInt

/-- The Gaussian integers are discrete in `ℂ`: the embedding `GaussianInt → ℂ` tends to infinity
along the cofinite filter, so only finitely many Gaussian integers lie in a compact subset of
`ℂ`. -/
theorem tendsto_toComplex_cofinite_cocompact :
    Tendsto ((↑) : GaussianInt → ℂ) cofinite (cocompact ℂ) := by
  have hcast : Tendsto (Prod.map ((↑) : ℤ → ℝ) ((↑) : ℤ → ℝ)) cofinite (cocompact (ℝ × ℝ)) := by
    simpa only [coprod_cofinite, coprod_cocompact] using
      Int.tendsto_coe_cofinite.prodMap_coprod Int.tendsto_coe_cofinite
  have hinj : Function.Injective fun z : GaussianInt ↦ (z.re, z.im) := fun z w h ↦
    Zsqrtd.ext (congrArg Prod.fst h) (congrArg Prod.snd h)
  rw [← Complex.equivRealProdCLM.toHomeomorph.comap_cocompact, tendsto_comap_iff]
  convert hcast.comp hinj.tendsto_cofinite using 1
  funext z
  exact Prod.ext (intCast_re z).symm (intCast_im z).symm

/-- Every complex number differs from a Gaussian integer by an element of the half-open unit square
`[0, 1) × [0, 1)`. -/
theorem exists_sub_mem_reProdIm_Ico (w : ℂ) :
    ∃ g : GaussianInt, w - g ∈ Ico (0 : ℝ) 1 ×ℂ Ico 0 1 := by
  refine ⟨⟨⌊w.re⌋, ⌊w.im⌋⟩, ?_⟩
  simp only [Complex.mem_reProdIm, Complex.sub_re, Complex.sub_im, re_toComplex, im_toComplex,
    Int.self_sub_floor, mem_Ico]
  exact ⟨⟨Int.fract_nonneg _, Int.fract_lt_one _⟩, Int.fract_nonneg _, Int.fract_lt_one _⟩

end GaussianInt
