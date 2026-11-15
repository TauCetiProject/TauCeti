/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.Algebra.SMul
import TauCeti.Geometry.Manifold.ContMDiff.Subtype

/-!
# Smooth contraction of a star-convex open subset

Let `U` be an open subset of a real normed space `V` that is star-convex about a point `c`.
Reparametrizing the radial straight-line homotopy `(t, x) ↦ c + t • (x - c)` in time by
`Real.smoothTransition` produces a map `StarConvex.smoothContraction : ℝ × U → U` defined on the
entire real time line `ℝ`, stationary at `c` for `t ≤ 0` and equal to the identity on `U` for
`1 ≤ t`, which is `C^n` on `ℝ × U` for every `n : ℕ∞` (including `C^∞`), without corners at the
interval endpoints `0` and `1`.

## Main definitions and results

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

open TopologicalSpace
open scoped ContDiff Manifold

namespace StarConvex

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {U : Opens V} {c : V}

/-- The smooth radial contraction `(t, x) ↦ c + Real.smoothTransition t • (x - c)` of a star-convex
open subset `U` of a real normed space `V` onto its star-centre `c`, defined on all of `ℝ × U`. -/
def smoothContraction (hU : StarConvex ℝ c (U : Set V)) (p : ℝ × U) : U :=
  ⟨c + Real.smoothTransition p.1 • ((p.2 : V) - c),
    hU.add_smul_sub_mem p.2.2 (Real.smoothTransition.nonneg p.1)
      (Real.smoothTransition.le_one p.1)⟩

/-- In the ambient normed space `V`, `hU.smoothContraction (t, x)` is
`c + Real.smoothTransition t • (x - c)`. -/
@[simp]
theorem coe_smoothContraction_apply (hU : StarConvex ℝ c (U : Set V)) (p : ℝ × U) :
    (hU.smoothContraction p : V) = c + Real.smoothTransition p.1 • ((p.2 : V) - c) :=
  (rfl)

/-- The radial contraction `hU.smoothContraction` is `C^n` on `ℝ × U` for every `n : ℕ∞` (including
`C^∞`; `Real.smoothTransition` is `C^∞` rather than analytic). -/
theorem contMDiff_smoothContraction {n : ℕ∞} (hU : StarConvex ℝ c (U : Set V)) :
    ContMDiff (𝓘(ℝ).prod 𝓘(ℝ, V)) 𝓘(ℝ, V) n hU.smoothContraction := by
  rw [← TauCeti.ContMDiff.subtypeVal_comp_iff U]
  have hψ : ContMDiff (𝓘(ℝ).prod 𝓘(ℝ, V)) 𝓘(ℝ) n fun p : ℝ × U ↦ Real.smoothTransition p.1 :=
    Real.smoothTransition.contDiff.contMDiff.comp contMDiff_fst
  have hx : ContMDiff (𝓘(ℝ).prod 𝓘(ℝ, V)) 𝓘(ℝ, V) n fun p : ℝ × U ↦ (p.2 : V) :=
    contMDiff_subtype_val.comp contMDiff_snd
  exact contMDiff_const.add (hψ.smul (hx.sub contMDiff_const))

/-- For `t ≤ 0`, `hU.smoothContraction (t, x)` is the star-centre `c`. -/
theorem smoothContraction_of_nonpos (hU : StarConvex ℝ c (U : Set V)) {t : ℝ} (ht : t ≤ 0)
    (x : U) :
    hU.smoothContraction (t, x) = ⟨c, hU.mem ⟨x.1, x.2⟩⟩ :=
  Subtype.ext (by simp [coe_smoothContraction_apply, Real.smoothTransition.zero_of_nonpos ht])

/-- For `1 ≤ t`, `hU.smoothContraction (t, x)` is `x`. -/
theorem smoothContraction_of_one_le (hU : StarConvex ℝ c (U : Set V)) {t : ℝ} (ht : 1 ≤ t)
    (x : U) :
    hU.smoothContraction (t, x) = x :=
  Subtype.ext (by simp [coe_smoothContraction_apply, Real.smoothTransition.one_of_one_le ht])

/-- At `t = 0`, `hU.smoothContraction (0, x)` is the star-centre `c`. -/
@[simp]
theorem smoothContraction_zero (hU : StarConvex ℝ c (U : Set V)) (x : U) :
    hU.smoothContraction (0, x) = ⟨c, hU.mem ⟨x.1, x.2⟩⟩ :=
  hU.smoothContraction_of_nonpos le_rfl x

/-- At `t = 1`, `hU.smoothContraction (1, x)` is `x`. -/
@[simp]
theorem smoothContraction_one (hU : StarConvex ℝ c (U : Set V)) (x : U) :
    hU.smoothContraction (1, x) = x :=
  hU.smoothContraction_of_one_le le_rfl x

end StarConvex
