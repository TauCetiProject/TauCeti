/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Spin.Polarization.TypeD.CartanWeights
public import TauCeti.RepresentationTheory.Spin.Polarization.TypeD.Serre.Equiv
public import TauCeti.RepresentationTheory.Spin.Polarization.TypeD.Split

/-!
# The type-D₄ Serre presentation: worked examples

Two checks on the Serre presentation of the quadratic Clifford Lie algebra of type `D₄`.

* At the fork node `3`, the presented raising generator goes to `C₃ C₄` and the lowering
  generator to `A₄ A₃` (one-based Clifford indices, `C` creation and `A` contraction). Their
  bracket is `N₃ + N₄ - 1`, which acts on the vacuum `1` of the spinor module by `-1`.
* The four Cartan generators and the `24` root vectors span the presented algebra, of dimension
  `28 = dim 𝔰𝔬₈`, the dimension of the split orthogonal matrix algebra.
-/

public section

open CliffordAlgebra

namespace TauCeti.Examples

open SpinPolarizationData

variable {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} (P : SpinPolarizationData Q) (b : Module.Basis (Fin 4) K P.W)
  (hline : P.line = ⊥)

/-- The fork bracket `⁅E₃, F₃⁆` (zero-based) acts on the vacuum of the spinor module by `-1`. -/
theorem spinAction_typeDSerreQuadraticEquiv_lie_serreE_serreF_three_one :
    spinAction Q P (P.typeDSerreQuadraticEquiv b le_rfl hline
        ⁅serreE K (CartanMatrix.D 4) 3, serreF K (CartanMatrix.D 4) 3⁆ : CliffordAlgebra Q) 1 =
      -1 := by
  have hvac : b.ExteriorAlgebra ∅ = 1 := by simp [b.exteriorAlgebra_eq_prod_map_sort]
  rw [lie_serreE_serreF_self, typeDSerreQuadraticEquiv_serreH, ← hvac,
    spinAction_typeDSimpleCorootBivector_basis]
  simp [DynkinType.typeDSpinWeight_apply]

/-- The Lie algebra presented by Serre's relations for `CartanMatrix.D 4` has dimension `28`. -/
theorem finrank_toLieAlgebra_D_four :
    Module.finrank ℚ (Matrix.ToLieAlgebra ℚ (CartanMatrix.D 4)) = 28 := by
  rw [(TypeDStd.serreEquiv 4 le_rfl).toLinearEquiv.finrank_eq,
    (typeDSplitPolarization 4).finrank_typeD (typeDSplitBasis 4) (typeDSplitPolarization_line 4)]
  rfl

end TauCeti.Examples
