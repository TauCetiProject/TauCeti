/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Opposite
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.Cofree.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.Fixed
public import TauCeti.Algebra.HopfAlgebra.Antipode
public import TauCeti.Algebra.TensorProduct.Module

/-!
# Right Hopf modules and the fundamental theorem of Hopf modules

Let `H` be a bialgebra over a commutative semiring `R`. A **right `H`-Hopf module** is an
`R`-module `M` equipped with both a right `H`-action (written as a `Module Hᵐᵒᵖ M` compatible
with `R`) and a right `H`-coaction `coact : M →ₗ[R] M ⊗[R] H` such that the coaction is
equivariant for the diagonal right `H`-action `(m ⊗ x) · h = ∑ (m · h₁) ⊗ (x * h₂)` on
`M ⊗[R] H`.

The regular bialgebra `H` itself is a right `H`-Hopf module (`instIsRightHopfModuleSelf`). More
generally, for every `R`-module `N`, the cofree right comodule `N ⊗[R] H` with `H` acting by
right multiplication on the second factor is a right `H`-Hopf module (`cofreeIsRightHopfModule`),
whose fixed subcomodule of coinvariants is canonically isomorphic to `N`
(`cofreeFixedSubcomoduleEquiv`).

When `H` is a Hopf algebra, every right `H`-Hopf module is of this cofree form. The coinvariant
projection `coinvariantProj`, sending `m` to `∑ m₀ · S(m₁)`, lands in
`Comodule.fixedSubcomodule R H M` and retracts the action map `n ⊗ h ↦ n · h`. Together with the
cofree comodule lift `Comodule.Hom.cofreeLift`, this gives the **Fundamental Theorem of Hopf
Modules** (`hopfModuleEquiv`): an `R`-linear isomorphism
`Comodule.fixedSubcomodule R H M ⊗[R] H ≃ₗ[R] M` that intertwines both the cofree right
coaction and right multiplication on the `H` factor. Neither subtraction in `R` nor bijectivity
of the antipode is assumed.

## Main definitions

* `TauCeti.rightTensorAction`: the diagonal right `H`-action on `M ⊗[R] H` induced by the
  coproduct of `H`.
* `TauCeti.IsRightHopfModule`: compatibility class for a right `H`-module and right
  `H`-comodule.
* `TauCeti.cofreeRightModule` and `TauCeti.cofreeIsRightHopfModule`: the right `H`-Hopf module
  structure on `N ⊗[R] H`.
* `TauCeti.cofreeFixedSubcomoduleEquiv`: the `R`-linear equivalence
  `Comodule.fixedSubcomodule R H (N ⊗[R] H) ≃ₗ[R] N`.
* `TauCeti.coinvariantProj` and `TauCeti.coinvariantProjFixed`: the coinvariant projection
  `m ↦ ∑ m₀ · S(m₁)` on a right `H`-Hopf module.
* `TauCeti.hopfModuleHom` and `TauCeti.hopfModuleEquiv`: the action morphism from
  `Comodule.fixedSubcomodule R H M ⊗[R] H` to `M` and the fundamental-theorem equivalence.

## References

* R. G. Larson and M. E. Sweedler, *An associative orthogonal bilinear form for Hopf algebras*,
  Amer. J. Math. 91 (1969), 75–94, Theorem 1.
* S. Montgomery, *Hopf Algebras and Their Actions on Rings*, CBMS Regional Conference Series in
  Mathematics 82, 1993, Theorem 1.9.4.
-/

public noncomputable section

open scoped TensorProduct Coalgebra
open TensorProduct

namespace TauCeti

universe u v w

section Bialgebra

variable (R : Type u) (H : Type v) (M : Type w)
variable [CommSemiring R] [Semiring H] [Bialgebra R H]
variable [AddCommMonoid M] [Module R M] [Module Hᵐᵒᵖ M] [IsScalarTower R Hᵐᵒᵖ M]

/-- The diagonal right `H`-action on `M ⊗[R] H`, given on pure tensors by
`(m ⊗ x) · h = ∑ (m · h₁) ⊗ (x * h₂)`.

Because `M ⊗[R] H` already carries Mathlib's left-factor `Module Hᵐᵒᵖ` instance, this diagonal
action is packaged as an explicit algebra representation rather than a competing typeclass
instance. -/
def rightTensorAction : Hᵐᵒᵖ →ₐ[R] Module.End R (M ⊗[R] H) :=
  (BialgebraModule.tensorPairAction R (A := Hᵐᵒᵖ) (B := Hᵐᵒᵖ) M H).comp
    ((_root_.Algebra.TensorProduct.opAlgEquiv R R H H).symm.toAlgHom.comp
      (Bialgebra.comulAlgHom R H).op)

variable {R H M}

/-- Evaluating the diagonal right action through the opposite coproduct. -/
theorem rightTensorAction_apply (h : H) (w : M ⊗[R] H) :
    rightTensorAction R H M (MulOpposite.op h) w =
      BialgebraModule.tensorPairAction R (A := Hᵐᵒᵖ) (B := Hᵐᵒᵖ) M H
        ((_root_.Algebra.TensorProduct.opAlgEquiv R R H H).symm
          (MulOpposite.op (Coalgebra.comul (R := R) h)))
        w :=
  (rfl)

/-- Evaluating the diagonal right action through the opposite coproduct on a pure tensor. -/
theorem rightTensorAction_tmul (h : H) (m : M) (x : H) :
    rightTensorAction R H M (MulOpposite.op h) (m ⊗ₜ[R] x) =
      BialgebraModule.tensorPairAction R (A := Hᵐᵒᵖ) (B := Hᵐᵒᵖ) M H
        ((_root_.Algebra.TensorProduct.opAlgEquiv R R H H).symm
          (MulOpposite.op (Coalgebra.comul (R := R) h)))
        (m ⊗ₜ[R] x) :=
  (rfl)

/-- On a pure tensor and for any coproduct representation of `h`, the diagonal right action
applies the left coproduct legs to `M` and multiplies the `H` factor on the right by the right
coproduct legs. -/
theorem rightTensorAction_tmul_sum {h : H} {ι : Type*} (r : Coalgebra.Repr R h ι)
    (m : M) (x : H) :
    rightTensorAction R H M (MulOpposite.op h) (m ⊗ₜ[R] x) =
      ∑ i ∈ r.index, (MulOpposite.op (r.left i) • m) ⊗ₜ[R] (x * r.right i) := by
  have hcomul :
      (_root_.Algebra.TensorProduct.opAlgEquiv R R H H).symm
          (MulOpposite.op (Coalgebra.comul (R := R) h)) =
        ∑ i ∈ r.index, MulOpposite.op (r.left i) ⊗ₜ[R] MulOpposite.op (r.right i) := by
    rw [← r.eq]
    change (_root_.Algebra.TensorProduct.opAlgEquiv R R H H).symm
        (MulOpposite.opAddEquiv (∑ i ∈ r.index, r.left i ⊗ₜ[R] r.right i)) = _
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    exact _root_.Algebra.TensorProduct.opAlgEquiv_symm_tmul R R H H (r.left i) (r.right i)
  rw [rightTensorAction_tmul, hcomul, map_sum, LinearMap.sum_apply]
  simp only [BialgebraModule.tensorPairAction_tmul]
  rfl

variable (R H M) in
/-- A **right `H`-Hopf module** over an `R`-bialgebra `H` is an `R`-module `M` carrying compatible
right `H`-module and right `H`-comodule structures: the coaction `M → M ⊗[R] H` intertwines the
right `H`-action on `M` with `rightTensorAction` on `M ⊗[R] H`. -/
class IsRightHopfModule [Comodule R H M] : Prop where
  /-- Right `H`-equivariance of the coaction. -/
  coact_smul (h : H) (m : M) :
    Comodule.coact (R := R) (C := H) (MulOpposite.op h • m) =
      rightTensorAction R H M (MulOpposite.op h) (Comodule.coact (R := R) (C := H) m)

/-- The coaction of a right Hopf module commutes with the right `H`-action. -/
theorem coact_op_smul [Comodule R H M] [IsRightHopfModule R H M] (h : H) (m : M) :
    Comodule.coact (R := R) (C := H) (MulOpposite.op h • m) =
      rightTensorAction R H M (MulOpposite.op h) (Comodule.coact (R := R) (C := H) m) :=
  IsRightHopfModule.coact_smul h m

/-- On a coinvariant vector `m`, the coaction of `m · h` is `(m · h₁) ⊗ h₂`. -/
theorem coact_op_smul_of_mem_fixedSubcomodule [Comodule R H M] [IsRightHopfModule R H M]
    {m : M} (hm : m ∈ Comodule.fixedSubcomodule R H M) (h : H) :
    Comodule.coact (R := R) (C := H) (MulOpposite.op h • m) =
      rightTensorAction R H M (MulOpposite.op h) (m ⊗ₜ[R] (1 : H)) := by
  rw [coact_op_smul, Comodule.mem_fixedSubcomodule.mp hm]

variable (R H) in
/-- The regular bialgebra `H` is a right `H`-Hopf module under right multiplication and
comultiplication. -/
instance instIsRightHopfModuleSelf : IsRightHopfModule R H H where
  coact_smul h x := by
    change Coalgebra.comul (R := R) (x * h) =
      rightTensorAction R H H (MulOpposite.op h) (Coalgebra.comul (R := R) x)
    rw [Bialgebra.comul_mul]
    induction Coalgebra.comul (R := R) x using TensorProduct.inductionOn with
    | add y z hy hz => simp only [add_mul, map_add, hy, hz]
    | tmul a b =>
      rw [rightTensorAction_tmul]
      induction Coalgebra.comul (R := R) h using TensorProduct.inductionOn with
      | add y z hy hz =>
        simp only [mul_add, MulOpposite.op_add, map_add, LinearMap.add_apply, hy, hz]
      | tmul c d =>
        rw [_root_.Algebra.TensorProduct.tmul_mul_tmul,
          _root_.Algebra.TensorProduct.opAlgEquiv_symm_tmul,
          BialgebraModule.tensorPairAction_tmul]
        rfl

section Cofree

variable (R H)
variable (N : Type w) [AddCommMonoid N] [Module R N]

/-- The right `H`-action on `N ⊗[R] H` by right multiplication on the second factor. -/
def cofreeRightAction : Hᵐᵒᵖ →ₐ[R] Module.End R (N ⊗[R] H) where
  toFun a := (LinearMap.mulRight R a.unop).lTensor N
  map_one' := by ext n x; simp
  map_mul' a b := by ext n x; simp [mul_assoc, mul_apply_eq_comp]
  map_zero' := by ext n x; simp
  map_add' a b := by ext n x; simp [mul_add, tmul_add]
  commutes' r := by
    ext n x
    simp [← Algebra.commutes, ← Algebra.smul_def]

/-- The right `H`-module structure on `N ⊗[R] H` acting by right multiplication on `H`.

As with `Comodule.cofree`, this is an explicit definition rather than a global instance, because
`N ⊗[R] H` already carries `TensorProduct.leftModule` when `N` is an `Hᵐᵒᵖ`-module. -/
@[implicit_reducible]
def cofreeRightModule : Module Hᵐᵒᵖ (N ⊗[R] H) :=
  Module.compHom (N ⊗[R] H) (cofreeRightAction R H N).toRingHom

/-- Scalar compatibility between `R` and `cofreeRightModule R H N`. -/
theorem cofreeRightIsScalarTower :
    letI := cofreeRightModule R H N
    IsScalarTower R Hᵐᵒᵖ (N ⊗[R] H) := by
  let := cofreeRightModule R H N
  refine IsScalarTower.of_algebraMap_smul fun r z ↦ ?_
  exact LinearMap.congr_fun ((cofreeRightAction R H N).commutes r) z

/-- The cofree comodule `N ⊗[R] H`, equipped with `cofreeRightModule`, is a right `H`-Hopf
module. -/
theorem cofreeIsRightHopfModule :
    letI := cofreeRightModule R H N
    letI := cofreeRightIsScalarTower R H N
    letI := Comodule.cofree R H N
    IsRightHopfModule R H (N ⊗[R] H) := by
  let := cofreeRightModule R H N
  let := cofreeRightIsScalarTower R H N
  let := Comodule.cofree R H N
  refine ⟨fun h z ↦ ?_⟩
  induction z using TensorProduct.inductionOn with
  | add u v hu hv => simp only [smul_add, map_add, hu, hv]
  | tmul n x =>
    change Comodule.cofreeCoact R H N (n ⊗ₜ[R] (x * h)) =
      rightTensorAction R H (N ⊗[R] H) (MulOpposite.op h) (Comodule.cofreeCoact R H N (n ⊗ₜ[R] x))
    rw [Comodule.cofreeCoact_tmul, Comodule.cofreeCoact_tmul, Bialgebra.comul_mul]
    induction Coalgebra.comul (R := R) x using TensorProduct.inductionOn with
    | add u v hu hv => simp only [add_mul, tmul_add, map_add, hu, hv]
    | tmul a b =>
      rw [assoc_symm_tmul, rightTensorAction_tmul]
      induction Coalgebra.comul (R := R) h using TensorProduct.inductionOn with
      | add u v hu hv =>
        simp only [mul_add, tmul_add, MulOpposite.op_add, map_add, LinearMap.add_apply, hu, hv]
      | tmul c d =>
        rw [_root_.Algebra.TensorProduct.tmul_mul_tmul, assoc_symm_tmul,
          _root_.Algebra.TensorProduct.opAlgEquiv_symm_tmul,
          BialgebraModule.tensorPairAction_tmul]
        rfl

/-- The fixed subcomodule of the cofree right comodule `N ⊗[R] H` is canonically isomorphic to
`N`, via `id ⊗ ε` and `n ↦ n ⊗ 1`. -/
def cofreeFixedSubcomoduleEquiv :
    letI := Comodule.cofree R H N
    Comodule.fixedSubcomodule R H (N ⊗[R] H) ≃ₗ[R] N := by
  letI := Comodule.cofree R H N
  have hmem (n : N) : n ⊗ₜ[R] (1 : H) ∈ Comodule.fixedSubcomodule R H (N ⊗[R] H) := by
    rw [Comodule.mem_fixedSubcomodule, Comodule.cofree_coact_tmul, Bialgebra.comul_one,
      _root_.Algebra.TensorProduct.one_def, assoc_symm_tmul]
  refine LinearEquiv.ofLinearMap
    (((TensorProduct.rid R N).toLinearMap ∘ₗ
        (Coalgebra.counit (R := R) (A := H)).lTensor N).comp
      (SMulMemClass.subtype (Comodule.fixedSubcomodule R H (N ⊗[R] H))))
    { toFun n := ⟨n ⊗ₜ[R] (1 : H), hmem n⟩
      map_add' x y := Subtype.ext (add_tmul x y 1)
      map_smul' r x := Subtype.ext (smul_tmul' r x 1) }
    (LinearMap.ext fun n ↦ by
      simp only [LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk,
        SMulMemClass.coe_subtype, LinearMap.lTensor_tmul,
        Bialgebra.counit_one, LinearEquiv.coe_coe, rid_tmul, one_smul, LinearMap.id_apply])
    (LinearMap.ext fun z ↦ Subtype.ext ?_)
  have hz : Comodule.cofreeCoact R H N z.1 = z.1 ⊗ₜ[R] (1 : H) :=
    Comodule.mem_fixedSubcomodule.mp z.2
  have hret := LinearMap.congr_fun
    (Comodule.rTensor_rid_comp_lTensor_counit_comp_cofreeCoact (R := R) (C := H) (M := N)) z.1
  rw [LinearMap.comp_apply, hz, LinearMap.rTensor_tmul, LinearMap.id_apply] at hret
  exact hret

@[simp]
theorem cofreeFixedSubcomoduleEquiv_apply
    (z : letI := Comodule.cofree R H N; Comodule.fixedSubcomodule R H (N ⊗[R] H)) :
    cofreeFixedSubcomoduleEquiv R H N z =
      TensorProduct.rid R N (Coalgebra.counit.lTensor N z.1) :=
  (rfl)

@[simp]
theorem cofreeFixedSubcomoduleEquiv_symm_coe (n : N) :
    ((cofreeFixedSubcomoduleEquiv R H N).symm n : N ⊗[R] H) = n ⊗ₜ[R] (1 : H) :=
  (rfl)

end Cofree

end Bialgebra

section HopfAlgebra

variable (R : Type u) (H : Type v) (M : Type w)
variable [CommSemiring R] [Semiring H] [HopfAlgebra R H]
variable [AddCommMonoid M] [Module R M] [Module Hᵐᵒᵖ M] [IsScalarTower R Hᵐᵒᵖ M]

/-- Contract `M ⊗[R] H` into `M` by the right `H`-action `m ⊗ h ↦ m · h`. -/
private def rightSMulContract : M ⊗[R] H →ₗ[R] M :=
  TensorProduct.lift
    (((_root_.Algebra.lsmul R R M : Hᵐᵒᵖ →ₐ[R] Module.End R M).toLinearMap ∘ₗ
      (MulOpposite.opLinearEquiv R).toLinearMap).flip)

@[simp]
private theorem rightSMulContract_tmul (m : M) (h : H) :
    rightSMulContract R H M (m ⊗ₜ[R] h) = MulOpposite.op h • m := by
  simp [rightSMulContract]

private theorem op_algebraMap_smul (r : R) (m : M) :
    MulOpposite.op (algebraMap R H r) • m = r • m := by
  rw [← MulOpposite.algebraMap_apply, IsScalarTower.algebraMap_smul]

variable [Comodule R H M]

/-- The **coinvariant projection** on a right `H`-Hopf module `M`, sending `m` to
`∑ (MulOpposite.op (S m₁) • m₀)`. -/
def coinvariantProj : M →ₗ[R] M :=
  rightSMulContract R H M ∘ₗ (HopfAlgebra.antipode R).lTensor M ∘ₗ
    Comodule.coact (R := R) (C := H) (M := M)

variable {R H M}

/-- If `coact m = ∑ i ∈ s, vᵢ ⊗ cᵢ`, then `coinvariantProj m = ∑ i ∈ s, vᵢ · S(cᵢ)`. -/
theorem coinvariantProj_eq_sum {ι : Type*} (s : Finset ι) (v : ι → M) (c : ι → H) {m : M}
    (hm : Comodule.coact (R := R) (C := H) m = ∑ i ∈ s, v i ⊗ₜ[R] c i) :
    coinvariantProj R H M m =
      ∑ i ∈ s, MulOpposite.op (HopfAlgebra.antipode R (c i)) • v i := by
  simp [coinvariantProj, hm, map_sum]

/-- Every coinvariant vector is fixed by `coinvariantProj`. -/
@[simp]
theorem coinvariantProj_of_mem_fixedSubcomodule {m : M}
    (hm : m ∈ Comodule.fixedSubcomodule R H M) :
    coinvariantProj R H M m = m := by
  simp [coinvariantProj, Comodule.mem_fixedSubcomodule.mp hm]

variable [IsRightHopfModule R H M]

/-- On `m · h` with `m` coinvariant, `coinvariantProj` acts as multiplication by `counit h`. -/
@[simp]
theorem coinvariantProj_smul_of_mem_fixedSubcomodule {m : M}
    (hm : m ∈ Comodule.fixedSubcomodule R H M) (h : H) :
    coinvariantProj R H M (MulOpposite.op h • m) = Coalgebra.counit (R := R) h • m := by
  simp only [coinvariantProj, LinearMap.comp_apply, coact_op_smul_of_mem_fixedSubcomodule hm]
  have hstep (t : H ⊗[R] H) :
      rightSMulContract R H M
        ((HopfAlgebra.antipode R).lTensor M
          (BialgebraModule.tensorPairAction R (A := Hᵐᵒᵖ) (B := Hᵐᵒᵖ) M H
            ((_root_.Algebra.TensorProduct.opAlgEquiv R R H H).symm (MulOpposite.op t))
            (m ⊗ₜ[R] (1 : H)))) =
        MulOpposite.op (LinearMap.mul' R H ((HopfAlgebra.antipode R).lTensor H t)) • m := by
    induction t using TensorProduct.inductionOn with
    | add x y hx hy =>
      simp only [MulOpposite.op_add, map_add, LinearMap.add_apply, add_smul, hx, hy]
    | tmul a b =>
      rw [_root_.Algebra.TensorProduct.opAlgEquiv_symm_tmul,
        BialgebraModule.tensorPairAction_tmul, LinearMap.lTensor_tmul,
        rightSMulContract_tmul, LinearMap.lTensor_tmul, LinearMap.mul'_apply]
      change MulOpposite.op (HopfAlgebra.antipode R ((1 : H) * b)) • (MulOpposite.op a • m) = _
      rw [one_mul, ← mul_smul, ← MulOpposite.op_mul]
  rw [rightTensorAction_tmul, hstep, HopfAlgebra.mul_antipode_lTensor_comul_apply,
    op_algebraMap_smul]

omit [Comodule R H M] [IsRightHopfModule R H M] in
/-- Key cancellation for `coinvariantProj_mem_fixedSubcomodule`: applying the antipode-twisted
diagonal right action across `Δ(x)` leaves `(m₀ · S x) ⊗ 1`. -/
private theorem coact_coinvariantProj_aux (m₀ : M) (x : H) :
    let Ψ : (M ⊗[R] H) ⊗[R] H →ₗ[R] M ⊗[R] H :=
      TensorProduct.lift
        ((rightTensorAction R H M).toLinearMap ∘ₗ
          (MulOpposite.opLinearEquiv R).toLinearMap ∘ₗ HopfAlgebra.antipode R).flip
    Ψ ((TensorProduct.assoc R M H H).symm (m₀ ⊗ₜ[R] Coalgebra.comul (R := R) x)) =
      (MulOpposite.op (HopfAlgebra.antipode R x) • m₀) ⊗ₜ[R] (1 : H) := by
  intro Ψ
  -- Reorganize `Ψ ((m₀ ⊗ a) ⊗ b)` through `(id ⊗ Δ) Δ(x) = assoc ((Δ ⊗ id) Δ(x))`.
  let Ξ : (H ⊗[R] H) ⊗[R] H →ₗ[R] M ⊗[R] H :=
    (TensorProduct.comm R H M).toLinearMap ∘ₗ
      TensorProduct.map
        (LinearMap.mul' R H ∘ₗ (HopfAlgebra.antipode R).lTensor H)
        ((_root_.Algebra.lsmul R R M : Hᵐᵒᵖ →ₐ[R] Module.End R M).toLinearMap.flip m₀ ∘ₗ
          (MulOpposite.opLinearEquiv R).toLinearMap ∘ₗ HopfAlgebra.antipode R)
  have hΨΞ (t : H ⊗[R] H) :
      Ψ ((TensorProduct.assoc R M H H).symm (m₀ ⊗ₜ[R] t)) =
        Ξ ((TensorProduct.assoc R H H H).symm
          ((Coalgebra.comul (R := R) (A := H)).lTensor H t)) := by
    induction t using TensorProduct.inductionOn with
    | add t₁ t₂ ht₁ ht₂ => simp only [tmul_add, map_add, ht₁, ht₂]
    | tmul a b =>
      have hb :
          Ψ ((m₀ ⊗ₜ[R] a) ⊗ₜ[R] b) =
            rightTensorAction R H M (MulOpposite.op (HopfAlgebra.antipode R b)) (m₀ ⊗ₜ[R] a) :=
        rfl
      rw [assoc_symm_tmul, hb, LinearMap.lTensor_tmul, rightTensorAction_tmul,
        TauCeti.HopfAlgebra.antipode_comul_antidistrib_apply]
      induction Coalgebra.comul (R := R) b using TensorProduct.inductionOn with
      | add w₁ w₂ hw₁ hw₂ =>
        simp only [tmul_add, map_add, MulOpposite.op_add, LinearMap.add_apply, hw₁, hw₂]
      | tmul u v =>
        simp [Ξ, _root_.Algebra.TensorProduct.opAlgEquiv_symm_tmul]
  rw [hΨΞ, Coalgebra.coassoc_symm_apply]
  have hΞ_comul (w : H ⊗[R] H) :
      Ξ ((Coalgebra.comul (R := R) (A := H)).rTensor H w) =
        (MulOpposite.op (HopfAlgebra.antipode R
            (TensorProduct.lid R H ((Coalgebra.counit (R := R)).rTensor H w))) • m₀) ⊗ₜ[R]
          (1 : H) := by
    induction w using TensorProduct.inductionOn with
    | add w₁ w₂ hw₁ hw₂ =>
      rw [map_add, map_add, hw₁, hw₂]
      simp only [map_add, MulOpposite.op_add, add_smul, add_tmul]
    | tmul p q =>
      simp [Ξ, HopfAlgebra.mul_antipode_lTensor_comul_apply, smul_assoc,
        Algebra.algebraMap_eq_smul_one, tmul_smul, smul_tmul']
  rw [hΞ_comul, Coalgebra.rTensor_counit_comul, lid_tmul, one_smul]

/-- The image of `coinvariantProj` lies in the fixed subcomodule of coinvariants. -/
theorem coinvariantProj_mem_fixedSubcomodule (m : M) :
    coinvariantProj R H M m ∈ Comodule.fixedSubcomodule R H M := by
  rw [Comodule.mem_fixedSubcomodule]
  let Ψ : (M ⊗[R] H) ⊗[R] H →ₗ[R] M ⊗[R] H :=
    TensorProduct.lift
      ((rightTensorAction R H M).toLinearMap ∘ₗ
        (MulOpposite.opLinearEquiv R).toLinearMap ∘ₗ HopfAlgebra.antipode R).flip
  have hcoact (z : M ⊗[R] H) :
      Comodule.coact (R := R) (C := H)
          (rightSMulContract R H M ((HopfAlgebra.antipode R).lTensor M z)) =
        Ψ ((Comodule.coact (R := R) (C := H) (M := M)).rTensor H z) := by
    induction z using TensorProduct.inductionOn with
    | add z₁ z₂ hz₁ hz₂ => simp only [map_add, hz₁, hz₂]
    | tmul m₀ c =>
      rw [LinearMap.lTensor_tmul, rightSMulContract_tmul, LinearMap.rTensor_tmul]
      exact coact_op_smul (HopfAlgebra.antipode R c) m₀
  simp only [coinvariantProj, LinearMap.comp_apply]
  rw [hcoact, ← Comodule.coassoc_symm_apply]
  induction Comodule.coact (R := R) (C := H) m using TensorProduct.inductionOn with
  | add z₁ z₂ hz₁ hz₂ => simp only [map_add, add_tmul, hz₁, hz₂]
  | tmul m₀ x =>
    simpa only [LinearMap.lTensor_tmul, rightSMulContract_tmul] using
      coact_coinvariantProj_aux (R := R) (H := H) m₀ x

/-- `coinvariantProj` is idempotent. -/
@[simp]
theorem coinvariantProj_idem (m : M) :
    coinvariantProj R H M (coinvariantProj R H M m) = coinvariantProj R H M m :=
  coinvariantProj_of_mem_fixedSubcomodule (coinvariantProj_mem_fixedSubcomodule m)

variable (R H M) in
/-- `coinvariantProj` corestricted to the fixed subcomodule `Comodule.fixedSubcomodule R H M`. -/
def coinvariantProjFixed : M →ₗ[R] Comodule.fixedSubcomodule R H M where
  toFun m := ⟨coinvariantProj R H M m, coinvariantProj_mem_fixedSubcomodule m⟩
  map_add' x y := Subtype.ext (map_add (coinvariantProj R H M) x y)
  map_smul' r x := Subtype.ext (map_smul (coinvariantProj R H M) r x)

@[simp]
theorem coe_coinvariantProjFixed (m : M) :
    (coinvariantProjFixed R H M m : M) = coinvariantProj R H M m :=
  (rfl)

@[simp]
theorem coinvariantProjFixed_subtype (n : Comodule.fixedSubcomodule R H M) :
    coinvariantProjFixed R H M (n : M) = n :=
  Subtype.ext (coinvariantProj_of_mem_fixedSubcomodule n.2)

@[simp]
theorem coinvariantProjFixed_smul (n : Comodule.fixedSubcomodule R H M) (h : H) :
    coinvariantProjFixed R H M (MulOpposite.op h • (n : M)) =
      Coalgebra.counit (R := R) h • n :=
  Subtype.ext (coinvariantProj_smul_of_mem_fixedSubcomodule n.2 h)

variable (R H M) in
/-- The right-action map `Comodule.fixedSubcomodule R H M ⊗[R] H → M` sending `n ⊗ h` to `n · h`,
bundled as a morphism of right `H`-comodules from the cofree comodule. -/
def hopfModuleHom :
    letI := Comodule.cofree R H (Comodule.fixedSubcomodule R H M)
    Comodule.Hom R H (Comodule.fixedSubcomodule R H M ⊗[R] H) M := by
  letI := Comodule.cofree R H (Comodule.fixedSubcomodule R H M)
  refine
    { toLinearMap := rightSMulContract R H M ∘ₗ
        (SMulMemClass.subtype (Comodule.fixedSubcomodule R H M)).rTensor H
      map_coact := TensorProduct.ext' fun n h ↦ ?_ }
  simp only [LinearMap.comp_apply, LinearMap.rTensor_tmul, SMulMemClass.coe_subtype,
    rightSMulContract_tmul, Comodule.cofree_coact_tmul]
  rw [coact_op_smul_of_mem_fixedSubcomodule n.2, rightTensorAction_tmul]
  induction Coalgebra.comul (R := R) h using TensorProduct.inductionOn with
  | add x y hx hy =>
    simp only [tmul_add, MulOpposite.op_add, map_add, LinearMap.add_apply, hx, hy]
  | tmul a b =>
    rw [assoc_symm_tmul, map_tmul, LinearMap.comp_apply, LinearMap.rTensor_tmul,
      SMulMemClass.coe_subtype, rightSMulContract_tmul, LinearMap.id_apply,
      _root_.Algebra.TensorProduct.opAlgEquiv_symm_tmul, BialgebraModule.tensorPairAction_tmul]
    change _ = _ ⊗ₜ[R] ((1 : H) * b)
    rw [one_mul]

@[simp]
theorem hopfModuleHom_tmul (n : Comodule.fixedSubcomodule R H M) (h : H) :
    hopfModuleHom R H M (n ⊗ₜ[R] h) = MulOpposite.op h • (n : M) := by
  simp [hopfModuleHom]

/-- Reconstructing `m` from the cofree lift of `coinvariantProjFixed` via the right action
recovers `m`: `∑ coinvariantProj(m₀) · m₁ = m`. -/
private theorem hopfModuleHom_comp_cofreeLift_apply (m : M) :
    letI := Comodule.cofree R H (Comodule.fixedSubcomodule R H M)
    hopfModuleHom R H M (Comodule.Hom.cofreeLift (C := H) (coinvariantProjFixed R H M) m) = m := by
  let := Comodule.cofree R H (Comodule.fixedSubcomodule R H M)
  have hsub :
      SMulMemClass.subtype (Comodule.fixedSubcomodule R H M) ∘ₗ coinvariantProjFixed R H M =
        coinvariantProj R H M :=
    LinearMap.ext fun _ ↦ rfl
  have hlhs :
      hopfModuleHom R H M (Comodule.Hom.cofreeLift (C := H) (coinvariantProjFixed R H M) m) =
        rightSMulContract R H M ((coinvariantProj R H M).rTensor H
          (Comodule.coact (R := R) (C := H) m)) := by
    simp only [hopfModuleHom, Comodule.Hom.coe_mk, Comodule.Hom.cofreeLift_apply,
      LinearMap.comp_apply, ← LinearMap.rTensor_comp_apply, hsub]
  rw [hlhs]
  have hcomp :
      (coinvariantProj R H M).rTensor H (Comodule.coact (R := R) (C := H) m) =
        (rightSMulContract R H M ∘ₗ (HopfAlgebra.antipode R).lTensor M).rTensor H
          ((Comodule.coact (R := R) (C := H)).rTensor H (Comodule.coact (R := R) (C := H) m)) := by
    rw [coinvariantProj, ← LinearMap.rTensor_comp_apply, LinearMap.comp_assoc]
  rw [hcomp, ← Comodule.coassoc_symm_apply]
  have hcancel (z : M ⊗[R] H) :
      rightSMulContract R H M
        ((rightSMulContract R H M ∘ₗ (HopfAlgebra.antipode R).lTensor M).rTensor H
          ((TensorProduct.assoc R M H H).symm
            ((Coalgebra.comul (R := R) (A := H)).lTensor M z))) =
        TensorProduct.rid R M ((Coalgebra.counit (R := R)).lTensor M z) := by
    induction z using TensorProduct.inductionOn with
    | add z₁ z₂ hz₁ hz₂ => simp only [map_add, hz₁, hz₂]
    | tmul m₀ c =>
      have hc (t : H ⊗[R] H) :
          rightSMulContract R H M
            ((rightSMulContract R H M ∘ₗ (HopfAlgebra.antipode R).lTensor M).rTensor H
              ((TensorProduct.assoc R M H H).symm (m₀ ⊗ₜ[R] t))) =
            MulOpposite.op (LinearMap.mul' R H ((HopfAlgebra.antipode R).rTensor H t)) • m₀ := by
        induction t using TensorProduct.inductionOn with
        | add t₁ t₂ ht₁ ht₂ =>
          simp only [tmul_add, map_add, MulOpposite.op_add, add_smul, ht₁, ht₂]
        | tmul a b =>
          simp only [assoc_symm_tmul, LinearMap.rTensor_tmul, LinearMap.comp_apply,
            LinearMap.lTensor_tmul, rightSMulContract_tmul, LinearMap.mul'_apply]
          rw [← mul_smul, ← MulOpposite.op_mul]
      rw [LinearMap.lTensor_tmul, hc, HopfAlgebra.mul_antipode_rTensor_comul_apply,
        op_algebraMap_smul, LinearMap.lTensor_tmul, rid_tmul]
  rw [hcancel, Comodule.rid_lTensor_counit_coact]

variable (R H M) in
/-- **Fundamental Theorem of Hopf Modules** (Larson–Sweedler). Every right `H`-Hopf module `M` over
a Hopf algebra `H` is isomorphic to the cofree Hopf module `Comodule.fixedSubcomodule R H M ⊗[R] H`
via `n ⊗ h ↦ n · h`, with inverse `m ↦ ∑ coinvariantProjFixed(m₀) ⊗ m₁`. -/
def hopfModuleEquiv : Comodule.fixedSubcomodule R H M ⊗[R] H ≃ₗ[R] M := by
  letI := Comodule.cofree R H (Comodule.fixedSubcomodule R H M)
  refine LinearEquiv.ofLinearMap
    (hopfModuleHom R H M).toLinearMap
    (Comodule.Hom.cofreeLift (C := H) (coinvariantProjFixed R H M)).toLinearMap
    (LinearMap.ext hopfModuleHom_comp_cofreeLift_apply)
    ?_
  -- Both `(cofreeLift coinvariantProjFixed).comp hopfModuleHom` and `id` are comodule morphisms
  -- into the cofree comodule, so `cofreeEquiv` reduces their equality to their counit components.
  have hhom :
      Comodule.Hom.comp (Comodule.Hom.cofreeLift (C := H) (coinvariantProjFixed R H M))
          (hopfModuleHom R H M) =
        Comodule.Hom.id R H (Comodule.fixedSubcomodule R H M ⊗[R] H) := by
    apply (Comodule.Hom.cofreeEquiv (R := R) (C := H)
      (M := Comodule.fixedSubcomodule R H M)
      (P := Comodule.fixedSubcomodule R H M ⊗[R] H)).injective
    rw [Comodule.Hom.cofreeLift_comp, ← Comodule.Hom.cofreeEquiv_symm_apply,
      LinearEquiv.apply_symm_apply]
    refine TensorProduct.ext' fun n h ↦ ?_
    simp
  exact congrArg Comodule.Hom.toLinearMap hhom

/-- On pure tensors, `hopfModuleEquiv` acts by the right `H`-action `n ⊗ h ↦ n · h`. -/
@[simp]
theorem hopfModuleEquiv_tmul (n : Comodule.fixedSubcomodule R H M) (h : H) :
    hopfModuleEquiv R H M (n ⊗ₜ[R] h) = MulOpposite.op h • (n : M) := by
  simp [hopfModuleEquiv]

/-- The underlying linear map of `hopfModuleEquiv` is `hopfModuleHom`. -/
theorem hopfModuleEquiv_toLinearMap :
    (hopfModuleEquiv R H M).toLinearMap =
      (letI := Comodule.cofree R H (Comodule.fixedSubcomodule R H M);
        (hopfModuleHom R H M).toLinearMap) :=
  (rfl)

/-- The inverse of `hopfModuleEquiv` is the cofree comodule lift of `coinvariantProjFixed`. -/
theorem hopfModuleEquiv_symm_apply (m : M) :
    (hopfModuleEquiv R H M).symm m =
      (coinvariantProjFixed R H M).rTensor H (Comodule.coact (R := R) (C := H) m) :=
  (rfl)

/-- `hopfModuleEquiv` intertwines right multiplication on the `H` factor with the right `H`-action
on `M`. -/
@[simp]
theorem hopfModuleEquiv_lTensor_mulRight (h : H)
    (z : Comodule.fixedSubcomodule R H M ⊗[R] H) :
    hopfModuleEquiv R H M ((LinearMap.mulRight R h).lTensor _ z) =
      MulOpposite.op h • hopfModuleEquiv R H M z := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, smul_add, hx, hy]
  | tmul n x =>
    simp only [LinearMap.lTensor_tmul, LinearMap.mulRight_apply, hopfModuleEquiv_tmul]
    rw [← mul_smul, ← MulOpposite.op_mul]

/-- `(hopfModuleEquiv).symm` intertwines the right `H`-action on `M` with right multiplication on
the `H` factor. -/
@[simp]
theorem hopfModuleEquiv_symm_smul (h : H) (m : M) :
    (hopfModuleEquiv R H M).symm (MulOpposite.op h • m) =
      (LinearMap.mulRight R h).lTensor _ ((hopfModuleEquiv R H M).symm m) := by
  apply (hopfModuleEquiv R H M).injective
  rw [hopfModuleEquiv_lTensor_mulRight, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply]

/-- `hopfModuleEquiv` intertwines the cofree coaction on `fixedSubcomodule R H M ⊗[R] H` with the
coaction on `M`. -/
theorem coact_hopfModuleEquiv (z : Comodule.fixedSubcomodule R H M ⊗[R] H) :
    Comodule.coact (R := R) (C := H) (hopfModuleEquiv R H M z) =
      (hopfModuleEquiv R H M).toLinearMap.rTensor H (Comodule.cofreeCoact R H _ z) := by
  let := Comodule.cofree R H (Comodule.fixedSubcomodule R H M)
  exact ((hopfModuleHom R H M).map_coact_apply z).symm

end HopfAlgebra

end TauCeti
