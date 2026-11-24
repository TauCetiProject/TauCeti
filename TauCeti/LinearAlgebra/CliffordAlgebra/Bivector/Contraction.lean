/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import TauCeti.Analysis.InnerProductSpace.ExteriorPower.Basic
public import TauCeti.LinearAlgebra.CliffordAlgebra.Bivector.Basic
import TauCeti.LinearAlgebra.CliffordAlgebra.OrthonormalBasis
import TauCeti.LinearAlgebra.ExteriorAlgebra.Contraction
import TauCeti.LinearAlgebra.ExteriorPower.Square

/-!
# The commutator of a Clifford two-vector with a generator

Write `c = CliffordAlgebra.ι Q` and `c₂ = CliffordAlgebra.bivectorExterior Q` for Clifford
multiplication by vectors and by two-forms, over a commutative ring in which `2` is invertible.
The commutator of `c₂(F)` with a generator is the Clifford image of the contraction of `F` by the
polar form of `Q`: `⁅c₂(F), c(v)⁆ = -c(Q(v, ·) ⌟ F)`.

For a real inner product space `V` and the quadratic form `Q v = -‖v‖²`, the polar form is
`-2 ⟪v, ·⟫`, so `⁅c₂(F), c(v)⁆ = 2 c(v ⌟ F)` with `v ⌟ F` the contraction
`TauCeti.twoVectorContraction F v`. So `c₂(F)` acts on the generators by twice the skew
endomorphism of `F`.

## Main results

* `TauCeti.bivectorExterior_lie_ι`: `⁅c₂(F), c(v)⁆ = -c(Q(v, ·) ⌟ F)`.
* `TauCeti.bivectorExterior_lie_ι_of_eq_neg_norm_sq`: for `Q v = -‖v‖²`,
  `⁅c₂(F), c(v)⁆ = 2 c(v ⌟ F)`.
-/

public section

namespace TauCeti

open CliffordAlgebra exteriorPower
open scoped RealInnerProductSpace

/-- **The commutator of a Clifford two-vector with a generator**: over a commutative ring in which
`2` is invertible, `⁅c₂(F), c(v)⁆ = -c(Q(v, ·) ⌟ F)`, the contraction of `F` by the polar form of
`Q` at `v`, read as a vector with `ExteriorAlgebra.ιInv`. -/
theorem bivectorExterior_lie_ι {R M : Type*} [CommRing R] [Invertible (2 : R)] [AddCommGroup M]
    [Module R M] {Q : QuadraticForm R M} (F : ⋀[R]^2 M) (v : M) :
    ⁅bivectorExterior Q F, ι Q v⁆ = -ι Q (ExteriorAlgebra.ιInv
      (contractLeft (QuadraticMap.polarBilin Q v) (F : ExteriorAlgebra R M))) := by
  -- Both sides are linear in `F`; compare them on `a ∧ b`.
  have key : (LinearMap.mulRight R (ι Q v) - LinearMap.mulLeft R (ι Q v)) ∘ₗ bivectorExterior Q =
      -(ι Q ∘ₗ ExteriorAlgebra.ιInv ∘ₗ contractLeft (QuadraticMap.polarBilin Q v) ∘ₗ
        (⋀[R]^2 M).subtype) :=
    linearMap_ext_ιMulti_two fun a b ↦ by
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.sub_apply,
        LinearMap.mulRight_apply, LinearMap.mulLeft_apply, LinearMap.neg_apply,
        Submodule.subtype_apply, ιMulti_apply_coe, ExteriorAlgebra.contractLeft_ιMulti]
      rw [bivectorExterior_apply_ιMulti, ← Ring.lie_def, bivector_lie_ι]
      simp [Fin.sum_univ_two, Fin.removeNth, ExteriorAlgebra.ιMulti_apply, sub_eq_add_neg,
        QuadraticMap.polar_comm Q v, ExteriorAlgebra.ι_leftInverse _]
  simpa [Ring.lie_def] using LinearMap.congr_fun key F

/-- **The Clifford image of a two-vector generates its contraction**: for `Q v = -‖v‖²`,
`⁅c₂(F), c(v)⁆ = 2 c(v ⌟ F)`, where `v ⌟ F` is `TauCeti.twoVectorContraction F v`. -/
theorem bivectorExterior_lie_ι_of_eq_neg_norm_sq {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {Q : QuadraticForm ℝ V} (hQ : ∀ v, Q v = -‖v‖ ^ 2) (F : ⋀[ℝ]^2 V)
    (v : V) : ⁅bivectorExterior Q F, ι Q v⁆ = ι Q ((2 : ℝ) • twoVectorContraction F v) := by
  have hpolar : QuadraticMap.polarBilin Q v = (-2 : ℝ) • innerₗ V v :=
    LinearMap.ext fun w ↦ by simp [QuadraticMap.polar_eq_neg_two_inner hQ]
  rw [bivectorExterior_lie_ι, hpolar, map_smul, LinearMap.smul_apply, map_smul, map_smul,
    twoVectorContraction_apply, map_smul]
  module

end TauCeti
