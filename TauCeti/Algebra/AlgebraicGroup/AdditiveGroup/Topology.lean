/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.Basic
public import TauCeti.Topology.Algebra.PointTopology.Group

/-!
# The point topology on the additive group

For a commutative topological `R`-algebra `A`, evaluation at `SymmetricAlgebra.ι R R 1` upgrades
`TauCeti.AdditiveGroup.gaPointsMulEquiv` to a topological multiplicative equivalence
`TauCeti.AdditiveGroup.gaPointsContinuousMulEquiv`.

## References

* B. Conrad, *Weil and Grothendieck approaches to adelic points*, Enseign. Math. (2) 58 (2012),
  Prop. 2.1, p. 2, and §3, pp. 3–4.
-/

public section

open SymmetricAlgebra WithConv TauCeti.PointTopology

namespace TauCeti.AdditiveGroup

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A] [TopologicalSpace A]
  [IsTopologicalSemiring A]

variable (R A) in
/-- The `A`-points of `𝔾ₐ = Spec (SymmetricAlgebra R R)`, with the point topology, are isomorphic
as topological monoids (and topological groups when `R`, `A` are commutative rings) to
`Multiplicative A`. -/
noncomputable def gaPointsContinuousMulEquiv :
    WithConv (SymmetricAlgebra R R →ₐ[R] A) ≃ₜ* Multiplicative A where
  toMulEquiv := gaPointsMulEquiv
  continuous_toFun := (continuous_ofAdd.comp (continuous_eval_ofConv (ι R R 1))).congr fun F ↦
    (congrArg Multiplicative.ofAdd (toAdd_gaPointsMulEquiv F).symm).trans (ofAdd_toAdd _)
  continuous_invFun := continuous_withConv_iff.2 fun s ↦ by
    induction s using SymmetricAlgebra.induction with
    | algebraMap r => simpa only [MulEquiv.invFun_eq_symm, AlgHom.commutes] using continuous_const
    | ι r => exact (continuous_const.fun_mul continuous_toAdd).congr fun x ↦
        (Eq.symm <| by rw [MulEquiv.invFun_eq_symm, ι_self_eq_smul_ι_one, map_smul,
          gaPointsMulEquiv_symm_apply_ι, Algebra.smul_def])
    | add p q hp hq => simpa only [MulEquiv.invFun_eq_symm, map_add] using hp.fun_add hq
    | mul p q hp hq => simpa only [MulEquiv.invFun_eq_symm, map_mul] using hp.fun_mul hq

/-- The underlying `MulEquiv` of `gaPointsContinuousMulEquiv` is `gaPointsMulEquiv`. -/
@[simp]
theorem coe_gaPointsContinuousMulEquiv :
    (gaPointsContinuousMulEquiv R A :
      WithConv (SymmetricAlgebra R R →ₐ[R] A) ≃* Multiplicative A) = gaPointsMulEquiv := (rfl)

/-- The forward map of `gaPointsContinuousMulEquiv` is `gaPointsMulEquiv`. -/
@[simp]
theorem gaPointsContinuousMulEquiv_apply (F : WithConv (SymmetricAlgebra R R →ₐ[R] A)) :
    gaPointsContinuousMulEquiv R A F = gaPointsMulEquiv F := (rfl)

/-- The inverse map of `gaPointsContinuousMulEquiv` is `gaPointsMulEquiv.symm`. -/
@[simp]
theorem gaPointsContinuousMulEquiv_symm_apply (a : Multiplicative A) :
    (gaPointsContinuousMulEquiv R A).symm a = (gaPointsMulEquiv (R := R)).symm a := (rfl)

end TauCeti.AdditiveGroup
