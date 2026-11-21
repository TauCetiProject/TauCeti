/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas

import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.Algebra.SMul
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import TauCeti.Geometry.Manifold.ContMDiff.Subtype

/-!
# Smooth contractions of star-convex chart domains and open subsets

An open subset `U` of an extended chart source `(extChartAt I x).source` in a `C^n` manifold
modelled on a real model with corners `I` whose image under `extChartAt I x` is star-convex with
respect to `extChartAt I x c` admits a global `C^n` contraction `F : ℝ × U → U` with
`F (0, z) = z` and `F (1, z) = c`
(`TauCeti.exists_contMDiff_contraction_of_starConvex_image_extChartAt`).

In a real normed space `V`, a star-convex open subset `U` about `c` admits the explicit radial
contraction `StarConvex.smoothContraction : ℝ × U → U`, defined on all of `ℝ × U` as
`(t, x) ↦ c + Real.smoothTransition t • (x - c)`, stationary at `c` for `t ≤ 0` and equal to the
identity on `U` for `1 ≤ t`, which is `C^n` for every `n : ℕ∞`.

## Main definitions and results

* `TauCeti.exists_contMDiff_contraction_of_starConvex_image_extChartAt`: an open subset of an
  extended chart source with star-convex chart image admits a `C^n` contraction.
* `StarConvex.smoothContraction`: the contraction `(t, x) ↦ c + Real.smoothTransition t • (x - c)`
  on `ℝ × U` for a star-convex open subset `U` of a real normed space.
* `StarConvex.coe_smoothContraction_apply`: its value in the ambient normed space.
* `StarConvex.contMDiff_smoothContraction`: `C^n` regularity of `StarConvex.smoothContraction` on
  `ℝ × U` for every `n : ℕ∞`.
* `StarConvex.smoothContraction_of_nonpos`, `StarConvex.smoothContraction_zero`,
  `StarConvex.smoothContraction_of_one_le`, `StarConvex.smoothContraction_one`: values for `t ≤ 0`
  (in particular `t = 0`) and `1 ≤ t` (in particular `t = 1`).

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 18, proof of Theorem 18.7.
-/

public section

noncomputable section

open scoped Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞}

/-- **Smooth contraction of an open chart domain with star-convex chart image.** Let `U` be an open
subset of `M` contained in `(extChartAt I x).source` whose image under `extChartAt I x` is
star-convex with respect to `extChartAt I x c` for `c : U`. Reparametrizing straight-line
interpolation towards `extChartAt I x c` in chart coordinates by `Real.smoothTransition` produces a
`C^n` map `F : ℝ × U → U` with `F (0, z) = z` and `F (1, z) = c`. -/
theorem exists_contMDiff_contraction_of_starConvex_image_extChartAt [IsManifold I n M]
    {x : M} {U : TopologicalSpace.Opens M} (hU : (U : Set M) ⊆ (extChartAt I x).source) (c : U)
    (hc : StarConvex ℝ (extChartAt I x c) (extChartAt I x '' (U : Set M))) :
    ∃ F : ℝ × U → U, ContMDiff (𝓘(ℝ).prod I) I n F ∧
      (∀ z, F (0, z) = z) ∧ (∀ z, F (1, z) = c) := by
  let φ : U → E := fun y ↦ extChartAt I x y.val
  have hφ : ContMDiff I 𝓘(ℝ, E) n φ :=
    (contMDiffOn_extChartAt (I := I) (x := x) (n := n)).comp_contMDiff contMDiff_subtypeVal
      fun y ↦ (extChartAt_source I x) ▸ hU y.property
  let G : ℝ × U → E := fun p ↦ φ c + (1 - Real.smoothTransition p.1) • (φ p.2 - φ c)
  have hG_im (p : ℝ × U) : G p ∈ extChartAt I x '' (U : Set M) :=
    hc.add_smul_sub_mem ⟨p.2.val, p.2.property, rfl⟩
      (by linarith [Real.smoothTransition.le_one p.1])
      (by linarith [Real.smoothTransition.nonneg p.1])
  have hG_tgt (p : ℝ × U) : G p ∈ (extChartAt I x).target := by
    obtain ⟨w, hwU, hw⟩ := hG_im p
    exact hw ▸ (extChartAt I x).map_source (hU hwU)
  have hF_U (p : ℝ × U) : (extChartAt I x).symm (G p) ∈ U := by
    obtain ⟨w, hwU, hw⟩ := hG_im p
    have heq : (extChartAt I x).symm (G p) = w := by
      rw [← hw]
      exact (extChartAt I x).left_inv (hU hwU)
    exact heq ▸ hwU
  have hlin : ContDiff ℝ n (fun q : ℝ × E ↦ φ c + (1 - Real.smoothTransition q.1) • (q.2 - φ c)) :=
    contDiff_const.add ((contDiff_const.sub
      (Real.smoothTransition.contDiff.comp contDiff_fst)).smul (contDiff_snd.sub contDiff_const))
  have hG : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ, E) n G :=
    hlin.comp_contMDiff (contMDiff_fst.prodMk_space (hφ.comp contMDiff_snd))
  refine ⟨fun p ↦ ⟨(extChartAt I x).symm (G p), hF_U p⟩, ?_, ?_, ?_⟩
  · rw [← ContMDiff.subtypeVal_comp_iff]
    exact (contMDiffOn_extChartAt_symm (I := I) (n := n) x).comp_contMDiff hG hG_tgt
  · intro z
    refine Subtype.ext ?_
    dsimp only [G, φ]
    rw [Real.smoothTransition.zero, sub_zero, one_smul, add_sub_cancel]
    exact (extChartAt I x).left_inv (hU z.property)
  · intro z
    refine Subtype.ext ?_
    dsimp only [G, φ]
    rw [Real.smoothTransition.one, sub_self, zero_smul, add_zero]
    exact (extChartAt I x).left_inv (hU c.property)

end TauCeti

namespace StarConvex

open TopologicalSpace
open scoped ContDiff

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {U : Opens V} {c : V}

/-- The smooth radial contraction `(t, x) ↦ c + Real.smoothTransition t • (x - c)` of a star-convex
open subset `U` of a real normed space `V` onto its star-centre `c`, defined on all of `ℝ × U`. -/
def smoothContraction (hU : StarConvex ℝ c (U : Set V)) (p : ℝ × U) : U :=
  ⟨c + Real.smoothTransition p.fst • ((p.snd : V) - c),
    hU.add_smul_sub_mem p.snd.prop (Real.smoothTransition.nonneg p.fst)
      (Real.smoothTransition.le_one p.fst)⟩

/-- In the ambient normed space `V`, `hU.smoothContraction (t, x)` is
`c + Real.smoothTransition t • (x - c)`. -/
@[simp]
theorem coe_smoothContraction_apply (hU : StarConvex ℝ c (U : Set V)) (p : ℝ × U) :
    (hU.smoothContraction p : V) = c + Real.smoothTransition p.fst • ((p.snd : V) - c) :=
  (rfl)

/-- The radial contraction `hU.smoothContraction` is `C^n` on `ℝ × U` for every `n : ℕ∞` (including
`C^∞`; `Real.smoothTransition` is `C^∞` rather than analytic). -/
theorem contMDiff_smoothContraction {n : ℕ∞} (hU : StarConvex ℝ c (U : Set V)) :
    ContMDiff (𝓘(ℝ).prod 𝓘(ℝ, V)) 𝓘(ℝ, V) n hU.smoothContraction := by
  rw [← TauCeti.ContMDiff.subtypeVal_comp_iff U]
  have hψ : ContMDiff (𝓘(ℝ).prod 𝓘(ℝ, V)) 𝓘(ℝ) n fun p : ℝ × U ↦ Real.smoothTransition p.fst :=
    Real.smoothTransition.contDiff.contMDiff.comp contMDiff_fst
  have hx : ContMDiff (𝓘(ℝ).prod 𝓘(ℝ, V)) 𝓘(ℝ, V) n fun p : ℝ × U ↦ (p.snd : V) :=
    contMDiff_subtypeVal.comp contMDiff_snd
  exact contMDiff_const.add (hψ.smul (hx.sub contMDiff_const))

/-- For `t ≤ 0`, `hU.smoothContraction (t, x)` is the star-centre `c`. -/
theorem smoothContraction_of_nonpos (hU : StarConvex ℝ c (U : Set V)) {t : ℝ} (ht : t ≤ 0)
    (x : U) :
    hU.smoothContraction (t, x) = ⟨c, hU.mem ⟨x.val, x.prop⟩⟩ :=
  Subtype.ext (by simp [coe_smoothContraction_apply, Real.smoothTransition.zero_of_nonpos ht])

/-- For `1 ≤ t`, `hU.smoothContraction (t, x)` is `x`. -/
theorem smoothContraction_of_one_le (hU : StarConvex ℝ c (U : Set V)) {t : ℝ} (ht : 1 ≤ t)
    (x : U) :
    hU.smoothContraction (t, x) = x :=
  Subtype.ext (by simp [coe_smoothContraction_apply, Real.smoothTransition.one_of_one_le ht])

/-- At `t = 0`, `hU.smoothContraction (0, x)` is the star-centre `c`. -/
@[simp]
theorem smoothContraction_zero (hU : StarConvex ℝ c (U : Set V)) (x : U) :
    hU.smoothContraction (0, x) = ⟨c, hU.mem ⟨x.val, x.prop⟩⟩ :=
  hU.smoothContraction_of_nonpos le_rfl x

/-- At `t = 1`, `hU.smoothContraction (1, x)` is `x`. -/
@[simp]
theorem smoothContraction_one (hU : StarConvex ℝ c (U : Set V)) (x : U) :
    hU.smoothContraction (1, x) = x :=
  hU.smoothContraction_of_one_le le_rfl x

end StarConvex
