/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.Projective
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import TauCeti.LinearAlgebra.Dual.BaseChange

/-!
# Scalar extension of linear maps and Hom spaces

The canonical map from `A ⊗[R] Hom_R(M,N)` to `Hom_A(A ⊗[R] M, A ⊗[R] N)` sends
`a ⊗ f` to `a • f.baseChange A`. It is an equivalence when `M` is finite projective;
no finiteness condition is needed on `N` or on the commutative value algebra `A`.
This comparison allows a scalar-extended Hom representation to act on scalar-extended vectors.

Under `TensorProduct.piScalarRight`, the scalar extension of `Matrix.mulVecLin M` corresponds to
left multiplication by `M.map (algebraMap A B)`
(`TensorProduct.piScalarRight_baseChange_mulVecLin`).

When the coefficient algebra is faithfully flat, extension of scalars is injective on linear
maps (`LinearMap.baseChange_injective`). Faithful flatness therefore permits checking equality of
linear maps after extension of scalars, including comparing maps defined over two intermediate
algebras inside a common enlargement (`LinearMap.baseChange_eq_of_baseChange_eq`).

For a finitely generated projective `R`-module `V` and a finitely generated projective `A`-module
`E`, an `R`-linear map `c : V → End_A E` extends `A`-linearly to `A ⊗[R] V`, and the finite
Hom/tensor identifications `dualTensorHomEquiv` turn that extension into a tensor in
`(A ⊗[R] V)* ⊗[A] (E* ⊗[A] E)` (`TauCeti.endValuedTensorEquiv`). The pure tensor
`φ ⊗ (ψ ⊗ e)` corresponds to the map `v ↦ (x ↦ φ (1 ⊗ v) • ψ x • e)`
(`TauCeti.endValuedTensorEquiv_symm_tmul_apply_apply`).
-/

public section

open scoped TensorProduct

namespace LinearMap

universe u v w x

variable (R : Type u) (A : Type v) (M : Type w) (N : Type x)
variable [CommSemiring R] [CommSemiring A] [Algebra R A]
variable [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

/-- The canonical scalar-extension map on linear Hom spaces. -/
noncomputable def baseChangeTensorHom :
    A ⊗[R] (M →ₗ[R] N) →ₗ[A] (A ⊗[R] M →ₗ[A] A ⊗[R] N) :=
  liftBaseChange A (baseChangeHom R A M N)

variable {R A M N}

/-- A pure tensor acts by the scalar multiple of the base-changed linear map. -/
@[simp]
theorem baseChangeTensorHom_tmul (a : A) (f : M →ₗ[R] N) :
    baseChangeTensorHom R A M N (a ⊗ₜ[R] f) = a • f.baseChange A := by
  simp [baseChangeTensorHom]

/-- Scalar extension of a rank-one map evaluates by the scalar-extended dual pairing.
The tensor comparison assembles the scalar-extended functional and target vector. -/
@[simp]
theorem baseChangeTensorHom_distribBaseChange_symm_tmul
    (ξ : A ⊗[R] Module.Dual R M) (η : A ⊗[R] N) (z : A ⊗[R] M) :
    baseChangeTensorHom R A M N
        ((dualTensorHom R M N).baseChange A
          ((TensorProduct.AlgebraTensorModule.distribBaseChange R A (Module.Dual R M) N).symm
            (ξ ⊗ₜ[A] η))) z =
      TauCeti.Module.Dual.baseChangeEvaluation ξ z • η := by
  induction ξ using TensorProduct.inductionOn with
  | add ξ ξ' h h' =>
      simp only [TensorProduct.add_tmul, map_add, LinearMap.add_apply, h, h', add_smul]
  | tmul a φ =>
      induction η using TensorProduct.inductionOn with
      | add η η' h h' =>
          simp only [TensorProduct.tmul_add, map_add, LinearMap.add_apply, h, h', smul_add]
      | tmul b n =>
          induction z using TensorProduct.inductionOn with
          | add z z' h h' => simp only [map_add, h, h', add_smul]
          | tmul c m =>
              simp [TensorProduct.smul_tmul', Algebra.smul_def, mul_comm, mul_left_comm,
                mul_assoc]

variable [Module.Finite R M] [Module.Projective R M]

/-- Scalar extension commutes with linear Hom out of a finite projective module. -/
-- Construct the Hom comparison from Mathlib's `lTensorHomEquivHomLTensor` and
-- `LinearMap.liftBaseChangeEquiv`, as in `TauCeti.Module.Dual.baseChangeEvaluationEquiv`.
noncomputable def baseChangeTensorHomEquiv :
    A ⊗[R] (M →ₗ[R] N) ≃ₗ[A] (A ⊗[R] M →ₗ[A] A ⊗[R] N) :=
  LinearEquiv.ofBijective (baseChangeTensorHom R A M N) <| by
    let e := (lTensorHomEquivHomLTensor R M A N).trans
      ((liftBaseChangeEquiv A).restrictScalars R)
    have he : e.toLinearMap = (baseChangeTensorHom R A M N).restrictScalars R := by
      apply TensorProduct.ext'
      intro a f
      apply TensorProduct.AlgebraTensorModule.ext
      intro b m
      simp only [e, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
        LinearEquiv.restrictScalars_apply, lTensorHomEquivHomLTensor_apply,
        LinearMap.restrictScalars_apply, baseChangeTensorHom_tmul, LinearMap.smul_apply,
        LinearMap.baseChange_tmul]
      rw [← liftBaseChange]
      simp [TensorProduct.smul_tmul', mul_comm]
    rw [← coe_restrictScalars R, ← he]
    exact e.bijective

/-- The Hom comparison equivalence is the canonical scalar-extension map. -/
@[simp]
theorem baseChangeTensorHomEquiv_apply (z : A ⊗[R] (M →ₗ[R] N)) :
    baseChangeTensorHomEquiv (R := R) (A := A) (M := M) (N := N) z =
      baseChangeTensorHom R A M N z :=
  (rfl)

/-- The inverse Hom comparison sends a base-changed map to the corresponding tensor
with scalar coefficient one. -/
@[simp]
theorem baseChangeTensorHomEquiv_symm_baseChange (f : M →ₗ[R] N) :
    (baseChangeTensorHomEquiv (R := R) (A := A) (M := M) (N := N)).symm
        (f.baseChange A) = 1 ⊗ₜ[R] f := by
  apply (baseChangeTensorHomEquiv (R := R) (A := A) (M := M) (N := N)).injective
  simp

end LinearMap

namespace TensorProduct

/-- Applying `TensorProduct.piScalarRight` intertwines the scalar extension of
`Matrix.mulVecLin M` with left multiplication by the mapped matrix `M.map (algebraMap A B)`. -/
theorem piScalarRight_baseChange_mulVecLin {A B ι₁ ι₂ : Type*}
    [CommSemiring A] [CommSemiring B] [Algebra A B]
    [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (M : Matrix ι₂ ι₁ A) (x : B ⊗[A] (ι₁ → A)) :
    TensorProduct.piScalarRight A B B ι₂ ((Matrix.mulVecLin M).baseChange B x) =
      (M.map (algebraMap A B)).mulVec (TensorProduct.piScalarRight A B B ι₁ x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, Matrix.mulVec_add, hx, hy]
  | tmul b v =>
    ext i
    simp only [LinearMap.baseChange_tmul, Matrix.mulVecLin_apply,
      TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul,
      Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.sum_smul, mul_smul]
    exact Finset.sum_congr rfl fun j _ ↦ _root_.Algebra.smul_def _ _

/-- Under `TensorProduct.piScalarRight` and basis coordinates `Module.Basis.equivFun`, the
scalar extension of `Matrix.mulVecLin M` intertwines with a linear map `f` whose matrix is
`M.map (algebraMap E L)`. -/
theorem piScalarRight_equivFun_intertwining {E L V W ιV ιW : Type*}
    [CommSemiring E] [CommSemiring L] [Algebra E L]
    [AddCommMonoid V] [Module L V] [AddCommMonoid W] [Module L W]
    [Fintype ιV] [DecidableEq ιV] [Fintype ιW] [DecidableEq ιW]
    (bV : Module.Basis ιV L V) (bW : Module.Basis ιW L W)
    (f : V →ₗ[L] W) (M : Matrix ιW ιV E)
    (hM : M.map (algebraMap E L) = LinearMap.toMatrix bV bW f)
    (x : L ⊗[E] (ιV → E)) :
    bW.equivFun.symm (TensorProduct.piScalarRight E L L ιW ((Matrix.mulVecLin M).baseChange L x)) =
      f (bV.equivFun.symm (TensorProduct.piScalarRight E L L ιV x)) := by
  apply bW.equivFun.injective
  rw [LinearEquiv.apply_symm_apply, TensorProduct.piScalarRight_baseChange_mulVecLin, hM]
  have hrepr : (bV.repr (bV.equivFun.symm (TensorProduct.piScalarRight E L L ιV x)) : ιV → L) =
      TensorProduct.piScalarRight E L L ιV x := by
    ext i
    simp only [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  rw [← hrepr, LinearMap.toMatrix_mulVec_repr bV bW f, hrepr]
  exact (Module.Basis.equivFun_apply bW _).symm

end TensorProduct

public section

open TensorProduct

namespace LinearMap

universe u v w x

variable {R : Type u} {A : Type v} {M : Type w} {N : Type x}
variable [CommRing R] [Ring A] [Algebra R A]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable [Module.FaithfullyFlat R A]

/-- Over a faithfully flat coefficient algebra, extension of scalars loses no information about a
linear map: two maps agreeing after extension of scalars are equal.

Mathlib's `LinearMap.baseChangeHom_injective` proves injectivity under the incomparable hypotheses
that `A` is merely faithful over `R` and that the *target* module `N` is flat over `R`; faithful
flatness of the coefficient algebra asks nothing of `N`. -/
theorem baseChange_injective :
    Function.Injective (baseChange A : (M →ₗ[R] N) → A ⊗[R] M →ₗ[A] A ⊗[R] N) := by
  intro f g h
  apply sub_eq_zero.mp
  apply (Module.FaithfullyFlat.zero_iff_lTensor_zero R A (f - g)).mpr
  have hTensor : f.lTensor A = g.lTensor A := by
    apply LinearMap.ext
    intro z
    simpa only [← baseChange_eq_lTensor] using DFunLike.congr_fun h z
  rw [lTensor_sub, hTensor]
  exact _root_.sub_self (g.lTensor A)

end LinearMap

public section

open TensorProduct

namespace TensorProduct.AlgebraTensorModule

/-- Tower compatibility for `AlgebraTensorModule.cancelBaseChange` on nested unit scalar
extensions `(1 : L) ⊗ₜ cancelBaseChange E E₁ E' E' W ((1 : E') ⊗ₜ y)`. -/
@[simp]
theorem cancelBaseChange_one_tmul_cancelBaseChange
    {E E₁ E' L W : Type*} [CommSemiring E] [CommSemiring E₁] [CommSemiring E'] [Semiring L]
    [Algebra E E₁] [Algebra E E'] [Algebra E L] [Algebra E₁ E'] [Algebra E₁ L] [Algebra E' L]
    [IsScalarTower E E₁ E'] [IsScalarTower E E₁ L] [IsScalarTower E₁ E' L] [IsScalarTower E E' L]
    [AddCommMonoid W] [Module E W] (y : E₁ ⊗[E] W) :
    AlgebraTensorModule.cancelBaseChange E E' L L W
        ((1 : L) ⊗ₜ[E'] AlgebraTensorModule.cancelBaseChange E E₁ E' E' W ((1 : E') ⊗ₜ[E₁] y)) =
      AlgebraTensorModule.cancelBaseChange E E₁ L L W ((1 : L) ⊗ₜ[E₁] y) := by
  induction y using TensorProduct.inductionOn with
  | add a b ha hb => simp only [TensorProduct.tmul_add, map_add, ha, hb]
  | tmul c w => simp

end TensorProduct.AlgebraTensorModule

namespace LinearMap

/-- **Linear maps equal over a faithfully flat extension agree over any common enlargement.**
If `f₁` over `E₁` and `f₂` over `E₂` induce the same map `L ⊗[E] V → L ⊗[E] W` after extending
scalars to `L`, then they already induce the same map `E' ⊗[E] V → E' ⊗[E] W` over any common
enlargement `E'` over which `L` is faithfully flat. -/
theorem baseChange_eq_of_baseChange_eq
    {E E₁ E₂ E' L V W : Type*}
    [CommSemiring E] [CommSemiring E₁] [CommSemiring E₂] [CommRing E'] [Ring L]
    [Algebra E E₁] [Algebra E E₂] [Algebra E E'] [Algebra E L]
    [Algebra E₁ E'] [Algebra E₁ L] [Algebra E₂ E'] [Algebra E₂ L] [Algebra E' L]
    [IsScalarTower E E₁ E'] [IsScalarTower E E₁ L] [IsScalarTower E₁ E' L]
    [IsScalarTower E E₂ E'] [IsScalarTower E E₂ L] [IsScalarTower E₂ E' L]
    [IsScalarTower E E' L]
    [Module.FaithfullyFlat E' L]
    [AddCommMonoid V] [Module E V] [AddCommMonoid W] [Module E W]
    (f₁ : (E₁ ⊗[E] V) →ₗ[E₁] (E₁ ⊗[E] W))
    (f₂ : (E₂ ⊗[E] V) →ₗ[E₂] (E₂ ⊗[E] W))
    (hL : ∀ x : L ⊗[E] V,
      AlgebraTensorModule.cancelBaseChange E E₁ L L W
          (f₁.baseChange L ((AlgebraTensorModule.cancelBaseChange E E₁ L L V).symm x)) =
        AlgebraTensorModule.cancelBaseChange E E₂ L L W
          (f₂.baseChange L ((AlgebraTensorModule.cancelBaseChange E E₂ L L V).symm x))) :
    ∀ x : E' ⊗[E] V,
      AlgebraTensorModule.cancelBaseChange E E₁ E' E' W
          (f₁.baseChange E' ((AlgebraTensorModule.cancelBaseChange E E₁ E' E' V).symm x)) =
        AlgebraTensorModule.cancelBaseChange E E₂ E' E' W
          (f₂.baseChange E' ((AlgebraTensorModule.cancelBaseChange E E₂ E' E' V).symm x)) := by
  let : AddCommGroup (E' ⊗[E] V) := Module.addCommMonoidToAddCommGroup E'
  let : AddCommGroup (E' ⊗[E] W) := Module.addCommMonoidToAddCommGroup E'
  let g₁ : (E' ⊗[E] V) →ₗ[E'] (E' ⊗[E] W) :=
    (AlgebraTensorModule.cancelBaseChange E E₁ E' E' W).toLinearMap ∘ₗ
      (f₁.baseChange E') ∘ₗ
      (AlgebraTensorModule.cancelBaseChange E E₁ E' E' V).symm.toLinearMap
  let g₂ : (E' ⊗[E] V) →ₗ[E'] (E' ⊗[E] W) :=
    (AlgebraTensorModule.cancelBaseChange E E₂ E' E' W).toLinearMap ∘ₗ
      (f₂.baseChange E') ∘ₗ
      (AlgebraTensorModule.cancelBaseChange E E₂ E' E' V).symm.toLinearMap
  suffices h : g₁ = g₂ from fun x ↦ by
    simpa only [g₁, g₂, LinearMap.comp_apply, LinearEquiv.coe_coe] using LinearMap.congr_fun h x
  apply LinearMap.baseChange_injective (R := E') (A := L)
  ext v
  apply (AlgebraTensorModule.cancelBaseChange E E' L L W).injective
  have hv := hL ((1 : L) ⊗ₜ[E] v)
  simp only [AlgebraTensorModule.cancelBaseChange_symm_tmul, LinearMap.baseChange_tmul] at hv
  simp only [g₁, g₂, AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
    LinearMap.restrictScalars_apply, LinearMap.baseChange_tmul, LinearMap.comp_apply,
    LinearEquiv.coe_coe, AlgebraTensorModule.cancelBaseChange_symm_tmul]
  exact (AlgebraTensorModule.cancelBaseChange_one_tmul_cancelBaseChange _).trans
    (hv.trans (AlgebraTensorModule.cancelBaseChange_one_tmul_cancelBaseChange _).symm)

end LinearMap

public section

open TensorProduct

namespace TauCeti

noncomputable section

variable (R A V E : Type*) [CommSemiring R] [CommSemiring A] [Algebra R A]
  [AddCommMonoid V] [Module R V] [Module.Finite R V] [Module.Projective R V]
  [AddCommMonoid E] [Module A E] [Module.Finite A E] [Module.Projective A E]
  [Module R E] [IsScalarTower R A E]

/-- **An endomorphism-valued linear map as a tensor.** An `R`-linear map `c : V → End_A E`
corresponds to its `A`-linear extension `A ⊗[R] V → End_A E`, and hence, `A ⊗[R] V` and `E`
being finitely generated and projective, to a tensor in `(A ⊗[R] V)* ⊗[A] (E* ⊗[A] E)`. -/
def endValuedTensorEquiv :
    (V →ₗ[R] Module.End A E) ≃ₗ[A] Module.Dual A (A ⊗[R] V) ⊗[A] (Module.Dual A E ⊗[A] E) :=
  (LinearMap.liftBaseChangeEquiv A).trans
    ((TensorProduct.congr (LinearEquiv.refl A _) (dualTensorHomEquiv A E E)).trans
      (dualTensorHomEquiv A (A ⊗[R] V) (Module.End A E))).symm

variable {R A V E}

/-- The endomorphism-valued map attached to a pure tensor `φ ⊗ (ψ ⊗ e)` sends `v` to the
rank-one endomorphism `x ↦ φ (1 ⊗ v) • ψ x • e`. -/
@[simp]
theorem endValuedTensorEquiv_symm_tmul_apply_apply (φ : Module.Dual A (A ⊗[R] V))
    (ψ : Module.Dual A E) (e : E) (v : V) (x : E) :
    (endValuedTensorEquiv R A V E).symm (φ ⊗ₜ (ψ ⊗ₜ e)) v x = φ (1 ⊗ₜ v) • ψ x • e := by
  simp [endValuedTensorEquiv]

end

end TauCeti
