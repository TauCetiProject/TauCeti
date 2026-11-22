/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Cofree.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.Regular
public import TauCeti.Algebra.HopfAlgebra.Antipode
import TauCeti.Algebra.Coalgebra.Comodule.Inverse

/-!
# Right Hopf modules and the fundamental theorem

Let `H` be a bialgebra over a commutative semiring `R`. A **right `H`-Hopf module** is an
`R`-module `M` carrying both a right `H`-action (`Module Hᵐᵒᵖ M` compatible with `R`) and a right
`H`-coaction (`Comodule R H M`) such that the right action `M ⊗[R] H → M` is a morphism of right
`H`-comodules for the diagonal tensor-product coaction:

`ρ(m ◃ h) = ∑ (m₀ ◃ h₁) ⊗ (m₁ h₂)`.

For any `R`-module `N`, the cofree comodule `N ⊗[R] H`, with `H` acting by right multiplication on
the second tensor factor, is the model example (`Comodule.cofreeRightModule`,
`Comodule.isRightHopfModule_cofree`); its fixed subcomodule of coinvariant elements is identified
with `N` in `TauCeti.Algebra.Coalgebra.Comodule.Cofree.Fixed`.

When `H` is a Hopf algebra, every right `H`-Hopf module is canonically of this form. The
coinvariant projection `coinvariantProj` sends `m` to `∑ m₀ ◃ S(m₁)`, lands in
`Comodule.fixedSubcomodule R H M`, transforms by the counit under the right `H`-action, and fixes
coinvariants; in particular `Comodule.fixedSubcomodule R H M` is an `R`-linear retract of `M`, so
it inherits projectivity and finite generation over `R`. Combining `toFixedSubcomodule` with the
coaction gives the **Fundamental Theorem of Hopf Modules** (`coinvariantTensorEquiv`):

`Comodule.fixedSubcomodule R H M ⊗[R] H ≃ₗ[R] M`,

sending `n ⊗ h` to `n ◃ h`, and intertwining both the right `H`-actions and the right
`H`-coactions. No subtraction on `R`, finiteness on `H`, or bijectivity of the antipode is needed.

## Main declarations

* `TauCeti.RightHopfModule.opSMulTensor`: the right `H`-action bundled as `M ⊗[R] H →ₗ[R] M`.
* `TauCeti.IsRightHopfModule`: Prop-valued compatibility class making `M` a right `H`-Hopf module.
* `TauCeti.RightHopfModule.instSelf`: the regular right `H`-Hopf module structure on `H`.
* `TauCeti.Comodule.cofreeRightModule`, `TauCeti.Comodule.isRightHopfModule_cofree`: the model
  right `H`-Hopf module structure on `N ⊗[R] H`.
* `TauCeti.RightHopfModule.coinvariantProj` and `TauCeti.RightHopfModule.toFixedSubcomodule`: the
  projection `m ↦ ∑ m₀ ◃ S(m₁)` onto coinvariants, with
  `TauCeti.RightHopfModule.projective_fixedSubcomodule` and
  `TauCeti.RightHopfModule.finite_fixedSubcomodule`.
* `TauCeti.RightHopfModule.coinvariantTensorEquiv`: the fundamental isomorphism
  `Comodule.fixedSubcomodule R H M ⊗[R] H ≃ₗ[R] M`, together with its right-module and
  right-comodule equivariance (`coinvariantTensorEquiv_tmul_mul`, `coinvariantTensorComoduleHom`,
  `coinvariantTensorSymmComoduleHom`).

## References

* R. G. Larson and M. E. Sweedler, *An associative orthogonal bilinear form for Hopf algebras*,
  Amer. J. Math. 91 (1969), 75–94, Proposition 1.
* M. E. Sweedler, *Hopf Algebras*, W. A. Benjamin, 1969, Theorem 4.1.1.
* S. Montgomery, *Hopf Algebras and Their Actions on Rings*, CBMS Regional Conference Series in
  Mathematics 82, 1993, Section 1.9, Theorem 1.9.4.
-/

public noncomputable section

open scoped TensorProduct Coalgebra

namespace TauCeti

universe u v w

namespace RightHopfModule

section Action

variable (R : Type u) (H : Type v) (M : Type w)
variable [CommSemiring R] [Semiring H] [Algebra R H]
variable [AddCommMonoid M] [Module R M] [Module Hᵐᵒᵖ M] [IsScalarTower R Hᵐᵒᵖ M]

/-- The right `H`-action on `M`, bundled as an `R`-linear map `M ⊗[R] H →ₗ[R] M` sending `m ⊗ h`
to `op h • m`. -/
def opSMulTensor : M ⊗[R] H →ₗ[R] M :=
  TensorProduct.lift <| LinearMap.mk₂ R (fun m h => MulOpposite.op h • m)
    (fun m₁ m₂ h => smul_add (MulOpposite.op h) m₁ m₂)
    (fun r m h => smul_comm (MulOpposite.op h) r m)
    (fun m h₁ h₂ => by rw [MulOpposite.op_add, add_smul])
    (fun r m h => by rw [MulOpposite.op_smul, smul_assoc])

variable {R H M}

/-- On a pure tensor, `opSMulTensor` acts on the vector leg by the opposite of the algebra leg. -/
@[simp]
theorem opSMulTensor_tmul (m : M) (h : H) :
    opSMulTensor R H M (m ⊗ₜ[R] h) = MulOpposite.op h • m := (rfl)

/-- Associativity of the right `H`-action in tensor-product form: acting sequentially by the two
`H` factors agrees with multiplying them in `H` before acting. -/
theorem opSMulTensor_assoc :
    opSMulTensor R H M ∘ₗ (opSMulTensor R H M).rTensor H ∘ₗ
        (TensorProduct.assoc R M H H).symm.toLinearMap =
      opSMulTensor R H M ∘ₗ (LinearMap.mul' R H).lTensor M := by
  refine TensorProduct.ext_threefold' fun m h₁ h₂ => ?_
  simp [MulOpposite.op_mul, mul_smul]

private theorem opSMulTensor_comp_lTensor_linearMap :
    opSMulTensor R H M ∘ₗ (Algebra.linearMap R H).lTensor M =
      (TensorProduct.rid R M).toLinearMap :=
  TensorProduct.ext' fun m r => by
    simp [Algebra.algebraMap_eq_smul_one]

end Action

end RightHopfModule

/-- Compatibility between a right `H`-module structure and a right `H`-comodule structure on `M`
over a bialgebra `H`: coacting after acting by `h` agrees with the diagonal coaction on `M ⊗[R] H`
followed by the right action on the module leg. -/
class IsRightHopfModule (R : Type u) (H : Type v) (M : Type w)
    [CommSemiring R] [Semiring H] [Bialgebra R H]
    [AddCommMonoid M] [Module R M] [Module Hᵐᵒᵖ M] [IsScalarTower R Hᵐᵒᵖ M]
    [Comodule R H M] : Prop where
  /-- Coaction distributes diagonally over the right `H`-action. -/
  coact_op_smul (h : H) (m : M) :
    Comodule.coact (R := R) (C := H) (MulOpposite.op h • m) =
      (RightHopfModule.opSMulTensor R H M).rTensor H
        (Comodule.tensorCombine (R := R) (C := H) (M := M) (N := H)
          (Comodule.coact (R := R) (C := H) m ⊗ₜ[R] Coalgebra.comul (R := R) h))

namespace RightHopfModule

section Bialgebra

variable {R : Type u} {H : Type v} {M : Type w}
variable [CommSemiring R] [Semiring H] [Bialgebra R H]
variable [AddCommMonoid M] [Module R M] [Module Hᵐᵒᵖ M] [IsScalarTower R Hᵐᵒᵖ M]
variable [Comodule R H M] [IsRightHopfModule R H M]

/-- Sweedler-sum form of the right Hopf-module law for a representation of `Δ(h)` and a sum
expression for `coact m`. -/
theorem coact_op_smul_eq_sum {h : H} {m : M} {ι κ : Type*}
    (s : Finset ι) (m₀ : ι → M) (m₁ : ι → H)
    (hm : ∑ i ∈ s, m₀ i ⊗ₜ[R] m₁ i = Comodule.coact (R := R) (C := H) m)
    (rh : Coalgebra.Repr R h κ) :
    Comodule.coact (R := R) (C := H) (MulOpposite.op h • m) =
      ∑ i ∈ s, ∑ j ∈ rh.index,
        (MulOpposite.op (rh.left j) • m₀ i) ⊗ₜ[R] (m₁ i * rh.right j) := by
  rw [IsRightHopfModule.coact_op_smul, ← hm, ← rh.eq, TensorProduct.sum_tmul]
  simp [TensorProduct.tmul_sum, map_sum]

/-- Acting on a coinvariant vector `m` by `h` produces a vector whose coaction is
`∑ (m ◃ h₁) ⊗ h₂`. -/
theorem coact_op_smul_of_mem_fixedSubcomodule {m : M}
    (hm : m ∈ Comodule.fixedSubcomodule R H M) (h : H) :
    Comodule.coact (R := R) (C := H) (MulOpposite.op h • m) =
      (opSMulTensor R H M ∘ₗ TensorProduct.mk R M H m).rTensor H
        (Coalgebra.comul (R := R) h) := by
  rw [IsRightHopfModule.coact_op_smul, Comodule.mem_fixedSubcomodule.mp hm]
  induction Coalgebra.comul (R := R) h using TensorProduct.inductionOn with
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
  | tmul h₁ h₂ => simp

variable (R H M) in
/-- The right action `M ⊗[R] H → M` of a right `H`-Hopf module, bundled as a morphism of right
`H`-comodules from the diagonal tensor-product comodule. -/
def opSMulHom :
    letI := Comodule.tensor R H M H
    Comodule.Hom R H (M ⊗[R] H) M :=
  letI := Comodule.tensor R H M H
  { toLinearMap := opSMulTensor R H M
    map_coact := by
      refine TensorProduct.ext' fun m h => ?_
      simpa only [LinearMap.comp_apply, opSMulTensor_tmul, Comodule.tensor_coact,
        Comodule.tensorCoact_tmul, Comodule.instSelf_coact, LinearMap.rTensor_def] using
        (IsRightHopfModule.coact_op_smul h m).symm }

/-- The underlying linear map of `opSMulHom` is `opSMulTensor`. -/
@[simp]
theorem opSMulHom_toLinearMap :
    letI := Comodule.tensor R H M H
    (opSMulHom R H M).toLinearMap = opSMulTensor R H M := (rfl)

/-- Pointwise evaluation of `opSMulHom` agrees with `opSMulTensor`. -/
@[simp]
theorem opSMulHom_apply (z : M ⊗[R] H) :
    letI := Comodule.tensor R H M H
    opSMulHom R H M z = opSMulTensor R H M z := (rfl)

end Bialgebra

section Self

variable {R : Type u} {H : Type v}
variable [CommSemiring R] [Semiring H] [Bialgebra R H]

/-- The regular right `H`-Hopf module of a bialgebra over itself, with right multiplication as the
action and comultiplication as the coaction. -/
instance instSelf : IsRightHopfModule R H H where
  coact_op_smul h m := by
    have hmul :
        (opSMulTensor R H H).rTensor H
            (Comodule.tensorCombine (R := R) (C := H) (M := H) (N := H)
              (Coalgebra.comul (R := R) m ⊗ₜ[R] Coalgebra.comul (R := R) h)) =
          Coalgebra.comul (R := R) m * Coalgebra.comul (R := R) h := by
      induction Coalgebra.comul (R := R) m using TensorProduct.inductionOn with
      | add x y hx hy =>
        simp only [TensorProduct.add_tmul, map_add, add_mul, hx, hy]
      | tmul m₁ m₂ =>
        induction Coalgebra.comul (R := R) h using TensorProduct.inductionOn with
        | add x y hx hy =>
          simp only [TensorProduct.tmul_add, map_add, mul_add, hx, hy]
        | tmul h₁ h₂ =>
          simp [Algebra.TensorProduct.tmul_mul_tmul]
    simpa [Comodule.instSelf_coact, Bialgebra.comul_mul] using hmul.symm

/-- On the regular right `H`-Hopf module, `opSMulHom` coincides with `Comodule.Hom.regularMul`. -/
@[simp]
theorem opSMulHom_self :
    letI := Comodule.tensor R H H H
    opSMulHom R H H = Comodule.Hom.regularMul (R := R) (H := H) := by
  let := Comodule.tensor R H H H
  refine Comodule.Hom.toLinearMap_injective (TensorProduct.ext' fun x y => ?_)
  simp

end Self

end RightHopfModule

namespace Comodule

section Cofree

variable (R : Type u) (H : Type v) (N : Type w)
variable [CommSemiring R] [Semiring H] [AddCommMonoid N] [Module R N]

/-- The right `H`-module structure on `N ⊗[R] H` acting by right multiplication on the `H` factor.

Like `Comodule.cofree`, this is an explicit definition rather than a global instance so it cannot
compete with other module actions on tensor products. -/
@[implicit_reducible]
def cofreeRightModule [Algebra R H] : Module Hᵐᵒᵖ (N ⊗[R] H) :=
  Module.compHom (N ⊗[R] H)
    ((Module.End.lTensorAlgHom R H N).comp (Algebra.lsmul (A := Hᵐᵒᵖ) R R H)).toRingHom

section Algebra

variable [Algebra R H]

attribute [local instance] cofreeRightModule

variable {R H N} in
/-- On pure tensors, the cofree right `H`-action multiplies the right tensor factor on the right. -/
@[simp]
theorem cofreeRightModule_op_smul_tmul (h : H) (n : N) (x : H) :
    MulOpposite.op h • (n ⊗ₜ[R] x) = n ⊗ₜ[R] (x * h) := (rfl)

/-- Scalar compatibility of the right `H`-action on `N ⊗[R] H` with `R`. -/
instance cofreeRightIsScalarTower : IsScalarTower R Hᵐᵒᵖ (N ⊗[R] H) :=
  IsScalarTower.of_algebraMap_smul fun r z =>
    (LinearMap.congr_fun
      (((Module.End.lTensorAlgHom R H N).comp
        (Algebra.lsmul (A := Hᵐᵒᵖ) R R H)).commutes r) z).trans
      (Module.algebraMap_end_apply R R (N ⊗[R] H) r z)

end Algebra

section Bialgebra

variable [Bialgebra R H]

attribute [local instance] cofree cofreeRightModule

/-- The cofree comodule `N ⊗[R] H` with right multiplication on the `H` factor is a right
`H`-Hopf module. -/
theorem isRightHopfModule_cofree : IsRightHopfModule R H (N ⊗[R] H) where
  coact_op_smul h z := by
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simp only [smul_add, map_add, TensorProduct.add_tmul, hx, hy]
    | tmul n x =>
      rw [cofreeRightModule_op_smul_tmul, cofree_coact_tmul, cofree_coact_tmul,
        Bialgebra.comul_mul]
      induction Coalgebra.comul (R := R) x using TensorProduct.inductionOn with
      | add u v hu hv =>
        simp only [add_mul, TensorProduct.tmul_add, map_add, TensorProduct.add_tmul]
        exact congrArg₂ (· + ·) hu hv
      | tmul x₁ x₂ =>
        induction Coalgebra.comul (R := R) h using TensorProduct.inductionOn with
        | add u v hu hv =>
          simp only [mul_add, TensorProduct.tmul_add, map_add]
          exact congrArg₂ (· + ·) hu hv
        | tmul h₁ h₂ => simp [Algebra.TensorProduct.tmul_mul_tmul]

end Bialgebra

end Cofree

end Comodule

namespace RightHopfModule

section HopfAlgebra

variable (R : Type u) (H : Type v) (M : Type w)
variable [CommSemiring R] [Semiring H] [_root_.HopfAlgebra R H]
variable [AddCommMonoid M] [Module R M] [Module Hᵐᵒᵖ M] [IsScalarTower R Hᵐᵒᵖ M]
variable [Comodule R H M]

/-- The coinvariant projection `m ↦ ∑ m₀ ◃ S(m₁)` on a right `H`-Hopf module. -/
def coinvariantProj : M →ₗ[R] M :=
  opSMulTensor R H M ∘ₗ (HopfAlgebra.antipode R).lTensor M ∘ₗ
    Comodule.coact (R := R) (C := H) (M := M)

variable {R H M}

/-- Pointwise formula for `coinvariantProj` in terms of `opSMulTensor`, the antipode, and the
coaction. -/
theorem coinvariantProj_apply (m : M) :
    coinvariantProj R H M m =
      opSMulTensor R H M
        ((HopfAlgebra.antipode R).lTensor M (Comodule.coact (R := R) (C := H) m)) := (rfl)

/-- Sweedler-sum form of `coinvariantProj` for any finite sum presentation of `coact m`. -/
theorem coinvariantProj_eq_sum {m : M} {ι : Type*} (s : Finset ι) (m₀ : ι → M) (m₁ : ι → H)
    (hm : ∑ i ∈ s, m₀ i ⊗ₜ[R] m₁ i = Comodule.coact (R := R) (C := H) m) :
    coinvariantProj R H M m =
      ∑ i ∈ s, MulOpposite.op (HopfAlgebra.antipode R (m₁ i)) • m₀ i := by
  rw [coinvariantProj_apply, ← hm]
  simp [map_sum]

omit [Comodule R H M] in
private def antipodeCombineContract (n : M) : H ⊗[R] (H ⊗[R] H) →ₗ[R] M ⊗[R] H :=
  TensorProduct.map
    (opSMulTensor R H M ∘ₗ TensorProduct.mk R M H n ∘ₗ HopfAlgebra.antipode R)
    (LinearMap.mul' R H ∘ₗ (HopfAlgebra.antipode R).lTensor H) ∘ₗ
    (TensorProduct.comm R (H ⊗[R] H) H).toLinearMap ∘ₗ
      (TensorProduct.assoc R H H H).symm.toLinearMap

omit [Comodule R H M] in
private theorem antipodeCombineContract_assoc_rTensor_comul (n : M) (w : H ⊗[R] H) :
    antipodeCombineContract n
        (TensorProduct.assoc R H H H ((Coalgebra.comul (R := R)).rTensor H w)) =
      (opSMulTensor R H M ((HopfAlgebra.antipode R).lTensor M
        (n ⊗ₜ[R] TensorProduct.lid R H ((Coalgebra.counit (R := R)).rTensor H w)))) ⊗ₜ[R]
        (1 : H) := by
  induction w using TensorProduct.inductionOn with
  | add u v hu hv =>
    simp only [map_add, TensorProduct.tmul_add, TensorProduct.add_tmul, hu, hv]
  | tmul c₁ d =>
    simpa [antipodeCombineContract, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul'] using
      congrArg (· ⊗ₜ[R] (1 : H))
        (smul_comm (Coalgebra.counit (R := R) c₁)
          (MulOpposite.op (HopfAlgebra.antipode R d)) n)

omit [Comodule R H M] in
/-- Universal tensor identity underlying `coact_coinvariantProj`: after applying
`(id ⊗ Δ) ∘ assoc⁻¹` to `z : M ⊗[R] H`, applying `Δ ∘ S` on the outer `H` leg and combining cancels
the middle antipode pair to `1` on the right factor. -/
private theorem opSMulTensor_tensorCombine_antipode_comul (z : M ⊗[R] H) :
    (opSMulTensor R H M).rTensor H
        (Comodule.tensorCombine (R := R) (C := H) (M := M) (N := H)
          (((Coalgebra.comul (R := R) ∘ₗ HopfAlgebra.antipode R).lTensor (M ⊗[R] H))
            ((TensorProduct.assoc R M H H).symm ((Coalgebra.comul (R := R)).lTensor M z)))) =
      (opSMulTensor R H M ((HopfAlgebra.antipode R).lTensor M z)) ⊗ₜ[R] (1 : H) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, TensorProduct.add_tmul, hx, hy]
  | tmul n c =>
    have hLHS (w : H ⊗[R] H) :
        (opSMulTensor R H M).rTensor H
          (Comodule.tensorCombine (R := R) (C := H) (M := M) (N := H)
            (((Coalgebra.comul (R := R) ∘ₗ HopfAlgebra.antipode R).lTensor (M ⊗[R] H))
              ((TensorProduct.assoc R M H H).symm (n ⊗ₜ[R] w)))) =
          antipodeCombineContract n ((Coalgebra.comul (R := R)).lTensor H w) := by
      induction w using TensorProduct.inductionOn with
      | add u v hu hv => simp only [TensorProduct.tmul_add, map_add, hu, hv]
      | tmul a b =>
        rw [TensorProduct.assoc_symm_tmul, LinearMap.lTensor_tmul, LinearMap.lTensor_tmul,
          LinearMap.comp_apply, HopfAlgebra.antipode_comul_antidistrib_apply]
        induction Coalgebra.comul (R := R) b using TensorProduct.inductionOn with
        | add u v hu hv => simp only [map_add, TensorProduct.tmul_add, hu, hv]
        | tmul b₁ b₂ => simp [antipodeCombineContract]
    rw [LinearMap.lTensor_tmul, hLHS, ← Coalgebra.coassoc_apply,
      antipodeCombineContract_assoc_rTensor_comul]
    simp

/-- The coinvariant projection fixes every coinvariant element. -/
theorem coinvariantProj_eq_self {m : M} (hm : m ∈ Comodule.fixedSubcomodule R H M) :
    coinvariantProj R H M m = m := by
  rw [coinvariantProj_apply, Comodule.mem_fixedSubcomodule.mp hm]
  simp

variable [IsRightHopfModule R H M]

/-- Every value of `coinvariantProj` has trivial right `H`-coaction:
`coact (coinvariantProj m) = coinvariantProj m ⊗ 1`. -/
@[simp]
theorem coact_coinvariantProj (m : M) :
    Comodule.coact (R := R) (C := H) (coinvariantProj R H M m) =
      coinvariantProj R H M m ⊗ₜ[R] (1 : H) := by
  let Q : M ⊗[R] H →ₗ[R] M ⊗[R] H :=
    (opSMulTensor R H M).rTensor H ∘ₗ
      Comodule.tensorCombine (R := R) (C := H) (M := M) (N := H) ∘ₗ
        TensorProduct.map (Comodule.coact (R := R) (C := H) (M := M))
          (Coalgebra.comul (R := R) ∘ₗ HopfAlgebra.antipode R)
  have hQ (z : M ⊗[R] H) :
      Comodule.coact (R := R) (C := H)
          (opSMulTensor R H M ((HopfAlgebra.antipode R).lTensor M z)) = Q z := by
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul n c =>
      simp only [LinearMap.lTensor_tmul, opSMulTensor_tmul, IsRightHopfModule.coact_op_smul, Q,
        LinearMap.comp_apply, TensorProduct.map_tmul]
  have hmap (z : M ⊗[R] H) :
      TensorProduct.map (Comodule.coact (R := R) (C := H) (M := M))
          (Coalgebra.comul (R := R) ∘ₗ HopfAlgebra.antipode R) z =
        ((Coalgebra.comul (R := R) ∘ₗ HopfAlgebra.antipode R).lTensor (M ⊗[R] H))
          ((Comodule.coact (R := R) (C := H) (M := M)).rTensor H z) := by
    rw [← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor]
  rw [coinvariantProj_apply, hQ]
  simp only [Q, LinearMap.comp_apply, hmap]
  rw [← Comodule.coassoc_symm_apply]
  exact opSMulTensor_tensorCombine_antipode_comul (Comodule.coact (R := R) (C := H) m)

/-- The coinvariant projection lands in `Comodule.fixedSubcomodule R H M`. -/
theorem coinvariantProj_mem_fixedSubcomodule (m : M) :
    coinvariantProj R H M m ∈ Comodule.fixedSubcomodule R H M :=
  Comodule.mem_fixedSubcomodule.mpr (coact_coinvariantProj m)

/-- Right `H`-actions are sent to counit scalar multiplications by `coinvariantProj`:
`P(m ◃ h) = ε(h) • P(m)`. -/
@[simp]
theorem coinvariantProj_op_smul (h : H) (m : M) :
    coinvariantProj R H M (MulOpposite.op h • m) =
      Coalgebra.counit (R := R) h • coinvariantProj R H M m := by
  rw [coinvariantProj_apply, IsRightHopfModule.coact_op_smul, coinvariantProj_apply]
  induction Comodule.coact (R := R) (C := H) m using TensorProduct.inductionOn with
  | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, smul_add, hx, hy]
  | tmul m₀ m₁ =>
    have hF (w : H ⊗[R] H) :
        opSMulTensor R H M
          ((HopfAlgebra.antipode R).lTensor M
            ((opSMulTensor R H M).rTensor H
              (Comodule.tensorCombine (R := R) (C := H) (M := M) (N := H)
                ((m₀ ⊗ₜ[R] m₁) ⊗ₜ[R] w)))) =
          MulOpposite.op
            (LinearMap.mul' R H ((HopfAlgebra.antipode R).lTensor H w) *
              HopfAlgebra.antipode R m₁) • m₀ := by
      induction w using TensorProduct.inductionOn with
      | add u v hu hv =>
        simp only [TensorProduct.tmul_add, map_add, add_mul, MulOpposite.op_add, add_smul, hu, hv]
      | tmul h₁ h₂ =>
        simp [_root_.HopfAlgebra.antipode_mul_antidistrib, mul_assoc, mul_smul]
    rw [hF]
    simp [Algebra.algebraMap_eq_smul_one]

/-- The coinvariant projection is idempotent. -/
@[simp]
theorem coinvariantProj_idem (m : M) :
    coinvariantProj R H M (coinvariantProj R H M m) = coinvariantProj R H M m :=
  coinvariantProj_eq_self (coinvariantProj_mem_fixedSubcomodule m)

variable (R H M) in
/-- The coinvariant projection with codomain restricted to `Comodule.fixedSubcomodule R H M`. -/
def toFixedSubcomodule : M →ₗ[R] Comodule.fixedSubcomodule R H M :=
  (coinvariantProj R H M).codRestrict (Comodule.fixedSubcomodule R H M).toSubmodule
    coinvariantProj_mem_fixedSubcomodule

/-- Coercing `toFixedSubcomodule m` back to `M` gives `coinvariantProj R H M m`. -/
@[simp]
theorem coe_toFixedSubcomodule (m : M) :
    (toFixedSubcomodule R H M m : M) = coinvariantProj R H M m :=
  LinearMap.codRestrict_apply _ _ m

/-- On coinvariant vectors, `toFixedSubcomodule` is the identity. -/
@[simp]
theorem toFixedSubcomodule_coe (n : Comodule.fixedSubcomodule R H M) :
    toFixedSubcomodule R H M (n : M) = n :=
  Subtype.ext ((coe_toFixedSubcomodule (n : M)).trans (coinvariantProj_eq_self n.property))

/-- Right `H`-actions are sent to counit scalar multiplications by `toFixedSubcomodule`. -/
@[simp]
theorem toFixedSubcomodule_op_smul (h : H) (m : M) :
    toFixedSubcomodule R H M (MulOpposite.op h • m) =
      Coalgebra.counit (R := R) h • toFixedSubcomodule R H M m := by
  ext
  simp

variable (R H M) in
/-- The coinvariant subcomodule of a projective right `H`-Hopf module is projective over `R`, being
split off `M` by `toFixedSubcomodule`. -/
theorem projective_fixedSubcomodule [Module.Projective R M] :
    Module.Projective R (Comodule.fixedSubcomodule R H M) :=
  Module.Projective.of_split (SMulMemClass.subtype (Comodule.fixedSubcomodule R H M))
    (toFixedSubcomodule R H M) (LinearMap.ext toFixedSubcomodule_coe)

variable (R H M) in
/-- The coinvariant subcomodule of a finitely generated right `H`-Hopf module is finitely generated
over `R`, being a surjective image of `M` under `toFixedSubcomodule`. -/
theorem finite_fixedSubcomodule [Module.Finite R M] :
    Module.Finite R (Comodule.fixedSubcomodule R H M) :=
  Module.Finite.of_surjective (toFixedSubcomodule R H M) fun n => ⟨n, toFixedSubcomodule_coe n⟩

private theorem opSMulTensor_toFixedSubcomodule_coact (m : M) :
    opSMulTensor R H M
      ((SMulMemClass.subtype (Comodule.fixedSubcomodule R H M) ∘ₗ
        toFixedSubcomodule R H M).rTensor H
        (Comodule.coact (R := R) (C := H) m)) = m := by
  have hsub :
      SMulMemClass.subtype (Comodule.fixedSubcomodule R H M) ∘ₗ toFixedSubcomodule R H M =
        coinvariantProj R H M := by
    ext
    simp
  have hcancel :
      opSMulTensor R H M ∘ₗ
        (opSMulTensor R H M ∘ₗ (HopfAlgebra.antipode R).lTensor M).rTensor H ∘ₗ
          (TensorProduct.assoc R M H H).symm.toLinearMap ∘ₗ
            (Coalgebra.comul (R := R)).lTensor M =
        (TensorProduct.rid R M).toLinearMap ∘ₗ (Coalgebra.counit (R := R)).lTensor M := by
    calc
      _ = (opSMulTensor R H M ∘ₗ (opSMulTensor R H M).rTensor H) ∘ₗ
            (((HopfAlgebra.antipode R).lTensor M).rTensor H ∘ₗ
              (TensorProduct.assoc R M H H).symm.toLinearMap) ∘ₗ
            (Coalgebra.comul (R := R)).lTensor M := by
        simp only [LinearMap.rTensor_comp, LinearMap.comp_assoc]
      _ = (opSMulTensor R H M ∘ₗ (opSMulTensor R H M).rTensor H ∘ₗ
            (TensorProduct.assoc R M H H).symm.toLinearMap) ∘ₗ
            ((HopfAlgebra.antipode R).rTensor H).lTensor M ∘ₗ
            (Coalgebra.comul (R := R)).lTensor M := by
        rw [LinearMap.rTensor_lTensor_comp_assoc_symm]
        simp only [LinearMap.comp_assoc]
      _ = opSMulTensor R H M ∘ₗ
            (LinearMap.mul' R H ∘ₗ (HopfAlgebra.antipode R).rTensor H ∘ₗ
              Coalgebra.comul (R := R)).lTensor M := by
        rw [opSMulTensor_assoc]
        simp only [LinearMap.comp_assoc, ← LinearMap.lTensor_comp]
      _ = (TensorProduct.rid R M).toLinearMap ∘ₗ (Coalgebra.counit (R := R)).lTensor M := by
        rw [_root_.HopfAlgebra.mul_antipode_rTensor_comul, LinearMap.lTensor_comp,
          ← LinearMap.comp_assoc, opSMulTensor_comp_lTensor_linearMap]
  rw [hsub, coinvariantProj, ← LinearMap.comp_assoc, LinearMap.rTensor_comp_apply,
    ← Comodule.coassoc_symm_apply]
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe] using
    (LinearMap.congr_fun hcancel (Comodule.coact (R := R) (C := H) m)).trans
      (Comodule.rid_lTensor_counit_coact m)

private theorem toFixedSubcomodule_coact_opSMul (n : Comodule.fixedSubcomodule R H M) (h : H) :
    (toFixedSubcomodule R H M).rTensor H
        (Comodule.coact (R := R) (C := H) (MulOpposite.op h • (n : M))) =
      n ⊗ₜ[R] h := by
  rw [coact_op_smul_of_mem_fixedSubcomodule n.property h, ← LinearMap.rTensor_comp_apply]
  have hcomp :
      toFixedSubcomodule R H M ∘ₗ (opSMulTensor R H M ∘ₗ TensorProduct.mk R M H (n : M)) =
        LinearMap.toSpanSingleton R (Comodule.fixedSubcomodule R H M) n ∘ₗ
          Coalgebra.counit (R := R) := by
    ext x
    simp
  rw [hcomp, LinearMap.rTensor_comp_apply, Coalgebra.rTensor_counit_comul]
  simp

variable (R H M) in
/-- **Fundamental Theorem of Hopf Modules** (Larson–Sweedler): a right `H`-Hopf module `M` over a
Hopf algebra `H` is canonically isomorphic to `Comodule.fixedSubcomodule R H M ⊗[R] H` via the
action map `n ⊗ h ↦ op h • n`, with inverse `m ↦ ∑ toFixedSubcomodule(m₀) ⊗ m₁`. -/
def coinvariantTensorEquiv : Comodule.fixedSubcomodule R H M ⊗[R] H ≃ₗ[R] M :=
  LinearEquiv.ofLinearMap
    (opSMulTensor R H M ∘ₗ
      (SMulMemClass.subtype (Comodule.fixedSubcomodule R H M)).rTensor H)
    ((toFixedSubcomodule R H M).rTensor H ∘ₗ Comodule.coact (R := R) (C := H) (M := M))
    (LinearMap.ext fun m => by
      simpa only [LinearMap.comp_apply, LinearMap.id_apply, ← LinearMap.rTensor_comp_apply] using
        opSMulTensor_toFixedSubcomodule_coact (R := R) (H := H) m)
    (TensorProduct.ext' fun n h => by
      simpa only [LinearMap.comp_apply, LinearMap.rTensor_tmul, SMulMemClass.subtype_apply,
        opSMulTensor_tmul, LinearMap.id_apply] using toFixedSubcomodule_coact_opSMul n h)

/-- On pure tensors, `coinvariantTensorEquiv` acts on the coinvariant vector by the Hopf-algebra
factor. -/
@[simp]
theorem coinvariantTensorEquiv_tmul (n : Comodule.fixedSubcomodule R H M) (h : H) :
    coinvariantTensorEquiv R H M (n ⊗ₜ[R] h) = MulOpposite.op h • (n : M) := (rfl)

/-- The inverse of `coinvariantTensorEquiv` applies `toFixedSubcomodule` to the left leg of the
coaction. -/
@[simp]
theorem coinvariantTensorEquiv_symm_apply (m : M) :
    (coinvariantTensorEquiv R H M).symm m =
      (toFixedSubcomodule R H M).rTensor H (Comodule.coact (R := R) (C := H) m) := (rfl)

/-- `coinvariantTensorEquiv` is equivariant for right multiplication on the `H` factor. -/
theorem coinvariantTensorEquiv_tmul_mul (n : Comodule.fixedSubcomodule R H M) (x h : H) :
    coinvariantTensorEquiv R H M (n ⊗ₜ[R] (x * h)) =
      MulOpposite.op h • coinvariantTensorEquiv R H M (n ⊗ₜ[R] x) := by
  simp [MulOpposite.op_mul, mul_smul]

/-- With `Comodule.cofreeRightModule`, `coinvariantTensorEquiv` intertwines the right `H`-actions
on all tensors. -/
theorem coinvariantTensorEquiv_op_smul (h : H)
    (z : Comodule.fixedSubcomodule R H M ⊗[R] H) :
    letI := Comodule.cofreeRightModule R H (Comodule.fixedSubcomodule R H M)
    coinvariantTensorEquiv R H M (MulOpposite.op h • z) =
      MulOpposite.op h • coinvariantTensorEquiv R H M z := by
  let := Comodule.cofreeRightModule R H (Comodule.fixedSubcomodule R H M)
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  | tmul n x => exact coinvariantTensorEquiv_tmul_mul n x h

variable (R H M) in
/-- The inverse in the Fundamental Theorem of Hopf Modules, bundled as a morphism of right
`H`-comodules from `M` to the cofree comodule on `Comodule.fixedSubcomodule R H M`: it is the
cofree lift of `toFixedSubcomodule`. -/
def coinvariantTensorSymmComoduleHom :
    letI := Comodule.cofree R H (Comodule.fixedSubcomodule R H M)
    Comodule.Hom R H M (Comodule.fixedSubcomodule R H M ⊗[R] H) :=
  letI := Comodule.cofree R H (Comodule.fixedSubcomodule R H M)
  Comodule.Hom.cofreeLift (C := H) (toFixedSubcomodule R H M)

/-- The underlying linear map of `coinvariantTensorSymmComoduleHom` is
`(coinvariantTensorEquiv R H M).symm`. -/
@[simp]
theorem coinvariantTensorSymmComoduleHom_toLinearMap :
    letI := Comodule.cofree R H (Comodule.fixedSubcomodule R H M)
    (coinvariantTensorSymmComoduleHom R H M).toLinearMap =
      (coinvariantTensorEquiv R H M).symm.toLinearMap := by
  ext m
  simp [coinvariantTensorSymmComoduleHom]

/-- Pointwise evaluation of `coinvariantTensorSymmComoduleHom` agrees with
`(coinvariantTensorEquiv R H M).symm`. -/
@[simp]
theorem coinvariantTensorSymmComoduleHom_apply (m : M) :
    letI := Comodule.cofree R H (Comodule.fixedSubcomodule R H M)
    coinvariantTensorSymmComoduleHom R H M m = (coinvariantTensorEquiv R H M).symm m := by
  let := Comodule.cofree R H (Comodule.fixedSubcomodule R H M)
  simp [coinvariantTensorSymmComoduleHom]

variable (R H M) in
/-- The forward direction of the Fundamental Theorem of Hopf Modules, bundled as a morphism of
right `H`-comodules from the cofree comodule on `Comodule.fixedSubcomodule R H M` to `M`. -/
def coinvariantTensorComoduleHom :
    letI := Comodule.cofree R H (Comodule.fixedSubcomodule R H M)
    Comodule.Hom R H (Comodule.fixedSubcomodule R H M ⊗[R] H) M :=
  letI := Comodule.cofree R H (Comodule.fixedSubcomodule R H M)
  { toLinearMap := (coinvariantTensorEquiv R H M).toLinearMap
    map_coact :=
      Comodule.Hom.map_coact_of_comp_eq_id (coinvariantTensorSymmComoduleHom R H M)
        (by
          rw [coinvariantTensorSymmComoduleHom_toLinearMap]
          exact (coinvariantTensorEquiv R H M).comp_symm)
        (by
          rw [coinvariantTensorSymmComoduleHom_toLinearMap]
          exact (coinvariantTensorEquiv R H M).symm_comp) }

/-- The underlying linear map of `coinvariantTensorComoduleHom` is `coinvariantTensorEquiv`. -/
@[simp]
theorem coinvariantTensorComoduleHom_toLinearMap :
    letI := Comodule.cofree R H (Comodule.fixedSubcomodule R H M)
    (coinvariantTensorComoduleHom R H M).toLinearMap =
      (coinvariantTensorEquiv R H M).toLinearMap := (rfl)

/-- Pointwise evaluation of `coinvariantTensorComoduleHom` agrees with `coinvariantTensorEquiv`. -/
@[simp]
theorem coinvariantTensorComoduleHom_apply (z : Comodule.fixedSubcomodule R H M ⊗[R] H) :
    letI := Comodule.cofree R H (Comodule.fixedSubcomodule R H M)
    coinvariantTensorComoduleHom R H M z = coinvariantTensorEquiv R H M z := (rfl)

/-- `coinvariantTensorComoduleHom` is a left inverse to `coinvariantTensorSymmComoduleHom` as a
morphism of right `H`-comodules. -/
@[simp]
theorem coinvariantTensorComoduleHom_comp_coinvariantTensorSymmComoduleHom :
    letI := Comodule.cofree R H (Comodule.fixedSubcomodule R H M)
    (coinvariantTensorComoduleHom R H M).comp (coinvariantTensorSymmComoduleHom R H M) =
      Comodule.Hom.id R H M := by
  let := Comodule.cofree R H (Comodule.fixedSubcomodule R H M)
  exact Comodule.Hom.toLinearMap_injective <| by
    rw [Comodule.Hom.comp_toLinearMap, coinvariantTensorComoduleHom_toLinearMap,
      coinvariantTensorSymmComoduleHom_toLinearMap, Comodule.Hom.id_toLinearMap]
    exact (coinvariantTensorEquiv R H M).comp_symm

/-- `coinvariantTensorSymmComoduleHom` is a left inverse to `coinvariantTensorComoduleHom` as a
morphism of right `H`-comodules. -/
@[simp]
theorem coinvariantTensorSymmComoduleHom_comp_coinvariantTensorComoduleHom :
    letI := Comodule.cofree R H (Comodule.fixedSubcomodule R H M)
    (coinvariantTensorSymmComoduleHom R H M).comp (coinvariantTensorComoduleHom R H M) =
      Comodule.Hom.id R H (Comodule.fixedSubcomodule R H M ⊗[R] H) := by
  let := Comodule.cofree R H (Comodule.fixedSubcomodule R H M)
  exact Comodule.Hom.toLinearMap_injective <| by
    rw [Comodule.Hom.comp_toLinearMap, coinvariantTensorSymmComoduleHom_toLinearMap,
      coinvariantTensorComoduleHom_toLinearMap, Comodule.Hom.id_toLinearMap]
    exact (coinvariantTensorEquiv R H M).symm_comp

end HopfAlgebra

end RightHopfModule

end TauCeti
