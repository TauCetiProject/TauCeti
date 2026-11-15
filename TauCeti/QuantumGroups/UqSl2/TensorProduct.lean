/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Bialgebra.Module.TensorProduct
public import TauCeti.QuantumGroups.UqSl2.Hopf

/-!
# Tensor actions of the rank-one quantum group

The generic bialgebra tensor product gives an action of `UqSl2 q` on the algebraic tensor
product of any two native modules. This file records the generator actions for the coproduct
`ΔE = E ⊗ 1 + K ⊗ E`, `ΔF = F ⊗ K⁻¹ + 1 ⊗ F`, and `ΔK = K ⊗ K`.
In particular, the two terms in the root-generator formulas retain their prescribed order.
No finite-dimensionality or generic-parameter hypothesis is needed beyond `q ≠ 0`.

The coproduct conventions follow A. Virelizier, *Quantum groups*, Sections 2.3--2.4.
-/

public section

namespace TauCeti.UqSl2

open BialgebraModule

variable (q : ℂ) [Fact (q ≠ 0)]
variable {M N : Type*} [AddCommMonoid M] [Module ℂ M] [Module (UqSl2 q) M]
variable [IsScalarTower ℂ (UqSl2 q) M]
variable [AddCommMonoid N] [Module ℂ N] [Module (UqSl2 q) N]
variable [IsScalarTower ℂ (UqSl2 q) N]

/-- The raising generator acts through `E ⊗ 1 + K ⊗ E`. -/
@[simp] theorem e_smul_tmul (m : M) (n : N) :
    e q • tmul ℂ (UqSl2 q) m n =
      tmul ℂ (UqSl2 q) (e q • m) n +
        tmul ℂ (UqSl2 q) (k q • m) (e q • n) := by
  apply (tensorEquiv ℂ (UqSl2 q) M N).injective
  simp [tensorAction_apply]

/-- The lowering generator acts through `F ⊗ K⁻¹ + 1 ⊗ F`. -/
@[simp] theorem f_smul_tmul (m : M) (n : N) :
    f q • tmul ℂ (UqSl2 q) m n =
      tmul ℂ (UqSl2 q) (f q • m) (kInv q • n) +
        tmul ℂ (UqSl2 q) m (f q • n) := by
  apply (tensorEquiv ℂ (UqSl2 q) M N).injective
  simp [tensorAction_apply]

/-- The weight generator acts on both tensor factors. -/
@[simp] theorem k_smul_tmul (m : M) (n : N) :
    k q • tmul ℂ (UqSl2 q) m n =
      tmul ℂ (UqSl2 q) (k q • m) (k q • n) := by
  apply (tensorEquiv ℂ (UqSl2 q) M N).injective
  simp [tensorAction_apply]

/-- The inverse weight generator acts on both tensor factors. -/
@[simp] theorem kInv_smul_tmul (m : M) (n : N) :
    kInv q • tmul ℂ (UqSl2 q) m n =
      tmul ℂ (UqSl2 q) (kInv q • m) (kInv q • n) := by
  apply (tensorEquiv ℂ (UqSl2 q) M N).injective
  simp [tensorAction_apply]

end TauCeti.UqSl2
