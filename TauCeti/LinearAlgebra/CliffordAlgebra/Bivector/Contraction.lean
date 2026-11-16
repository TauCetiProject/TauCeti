/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import TauCeti.Analysis.InnerProductSpace.ExteriorPower.Basic
public import TauCeti.LinearAlgebra.CliffordAlgebra.Bivector.Basic
import Mathlib.Data.Fin.Tuple.Reflection

/-!
# The commutator of a Clifford two-vector with a generator

Let `V` be a real inner product space and `Q` the quadratic form `Q v = -‖v‖²`. Write
`c = CliffordAlgebra.ι Q` and `c₂ = CliffordAlgebra.bivectorExterior Q` for Clifford
multiplication by vectors and by two-forms. The commutator of `c₂(F)` with a generator is
the Clifford image of the contraction `v ⌟ F` (`TauCeti.twoVectorContraction`):
`⁅c₂(F), c(v)⁆ = 2 c(v ⌟ F)`. So `c₂(F)` acts on the generators by the skew endomorphism of `F`.

## Main results

* `CliffordAlgebra.bivectorExterior_lie_ι`: `⁅c₂(F), c(v)⁆ = 2 c(v ⌟ F)`.
-/

public section

namespace CliffordAlgebra

open TauCeti exteriorPower
open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {Q : QuadraticForm ℝ V}

/-- **The Clifford image of a two-vector generates its contraction**: for `Q v = -‖v‖²`,
`⁅c₂(F), c(v)⁆ = 2 c(v ⌟ F)`, where `v ⌟ F` is `TauCeti.twoVectorContraction F v`. -/
theorem bivectorExterior_lie_ι (hQ : ∀ v, Q v = -‖v‖ ^ 2) (F : ⋀[ℝ]^2 V) (v : V) :
    ⁅bivectorExterior Q F, ι Q v⁆ = ι Q ((2 : ℝ) • twoVectorContraction F v) := by
  have hpolar (x y : V) : QuadraticMap.polar Q x y = -2 * ⟪x, y⟫ := by
    simp only [QuadraticMap.polar, hQ, norm_add_sq_real]
    ring
  -- Both sides are linear in `F`; compare them on `a ∧ b`.
  have key : (LinearMap.mulRight ℝ (ι Q v) - LinearMap.mulLeft ℝ (ι Q v)) ∘ₗ bivectorExterior Q =
      ((2 : ℝ) • ι Q) ∘ₗ (LinearMap.applyₗ (R := ℝ) v ∘ₗ twoVectorContractionₗ) := by
    refine exteriorPower.linearMap_ext (AlternatingMap.ext fun w ↦ ?_)
    have hw : w = ![w 0, w 1] := (FinVec.etaExpand_eq w).symm
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.sub_apply, LinearMap.mulRight_apply, LinearMap.mulLeft_apply, LinearMap.smul_apply,
      twoVectorContractionₗ_apply, LinearMap.applyₗ_apply_apply, twoVectorContraction_ιMulti]
    conv_lhs => rw [hw]
    rw [bivectorExterior_apply_ιMulti, ← Ring.lie_def, bivector_lie_ι, hpolar, hpolar]
    simp only [map_sub, map_smul, smul_sub, smul_smul]
    rw [real_inner_comm (w 1) v, real_inner_comm (w 0) v]
    module
  simpa [Ring.lie_def] using LinearMap.congr_fun key F

end CliffordAlgebra
