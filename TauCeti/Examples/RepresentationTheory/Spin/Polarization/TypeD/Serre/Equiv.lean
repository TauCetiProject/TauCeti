/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Spin.Polarization.Hyperbolic
public import TauCeti.RepresentationTheory.Spin.Polarization.TypeD.CartanWeights
public import TauCeti.RepresentationTheory.Spin.Polarization.TypeD.Serre.Equiv

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

/-- The Lie algebra presented by Serre's relations for `CartanMatrix.D 4` over a field of
characteristic zero has dimension `28`, computed through the hyperbolic polarization of `K⁴`. -/
theorem finrank_toLieAlgebra_D_four :
    Module.finrank K (Matrix.ToLieAlgebra K (CartanMatrix.D 4)) = 28 := by
  have hM := Module.eval_apply_injective K (V := Fin 4 → K)
  rw [(TypeDStd.serreEquiv 4 le_rfl).toLinearEquiv.finrank_eq,
    (hyperbolic hM).finrank_typeD
      ((hyperbolicBasis (Pi.basisFun K (Fin 4))).map (LinearEquiv.ofEq _ _ (hyperbolic_W hM).symm))
      (hyperbolic_line hM), Fintype.card_fin]
  rfl

end TauCeti.Examples
