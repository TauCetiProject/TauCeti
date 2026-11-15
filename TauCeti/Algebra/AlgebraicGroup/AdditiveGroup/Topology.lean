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

For a commutative topological `R`-algebra `A`, the points of `𝔾ₐ = Spec (SymmetricAlgebra R R)`
valued in `A` are identified with `Multiplicative A` by evaluation at `SymmetricAlgebra.ι R R 1`
(`TauCeti.AdditiveGroup.gaPointsMulEquiv`). Since `SymmetricAlgebra R R` is generated as an
`R`-algebra by that single coordinate, this upgrades `gaPointsMulEquiv` to a topological
multiplicative equivalence `TauCeti.AdditiveGroup.gaPointsContinuousMulEquiv`.

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
  continuous_toFun :=
    (continuous_ofAdd.comp (continuous_eval_ofConv (ι R R 1))).congr fun F ↦ by
      rw [Function.comp_apply, MulEquiv.toFun_eq_coe, ← ofAdd_toAdd (gaPointsMulEquiv F),
        toAdd_gaPointsMulEquiv]
  continuous_invFun := continuous_withConv_iff.2 fun s ↦ by
    -- Induct on `SymmetricAlgebra R R`; on `ι R R r`, the inverse evaluates to `r • toAdd x`.
    induction s using SymmetricAlgebra.induction with
    | algebraMap r => simpa only [MulEquiv.invFun_eq_symm, AlgHom.commutes] using continuous_const
    | ι r =>
      have hι (x : Multiplicative A) :
          ((gaPointsMulEquiv (R := R) (A := A)).symm x).ofConv (ι R R r) =
            algebraMap R A r * Multiplicative.toAdd x := by
        have hr : ι R R r = r • ι R R 1 := by rw [← map_smul, smul_eq_mul, mul_one]
        rw [hr, map_smul, gaPointsMulEquiv_symm_apply_ι, Algebra.smul_def]
      simpa only [MulEquiv.invFun_eq_symm, hι] using continuous_const.fun_mul continuous_toAdd
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
