/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.LinearAlgebra.TensorProduct.Projective
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import TauCeti.LinearAlgebra.Dual.BaseChange
import TauCeti.LinearAlgebra.TensorProduct.Tower

/-!
# Scalar extension of linear maps and Hom spaces

The canonical map from `A ⊗[R] Hom_R(M,N)` to `Hom_A(A ⊗[R] M, A ⊗[R] N)` sends
`a ⊗ f` to `a • f.baseChange A`. It is an equivalence when `M` is finite projective;
no finiteness condition is needed on `N` or on the commutative value algebra `A`.
This comparison allows a scalar-extended Hom representation to act on scalar-extended vectors.

When the coefficient algebra is faithfully flat, extension of scalars is injective on linear
maps (`LinearMap.baseChange_injective`). Faithful flatness therefore permits checking equality of
linear maps after extension of scalars, including comparing maps defined over two intermediate
algebras inside a common enlargement (`LinearMap.baseChange_eq_of_baseChange_eq`) and noting
that only the identity extends to the identity (`LinearEquiv.baseChange_eq_one_iff`). Scalar-tower
cancellation `AlgebraTensorModule.cancelBaseChange` also commutes with scalar multiples and finite
sums of scalar multiples of base-changed linear maps
(`LinearMap.cancelBaseChange_comp_smul_baseChange`,
`LinearMap.cancelBaseChange_comp_sum_smul_baseChange`).

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

namespace LinearEquiv

variable {R : Type*} {A : Type*} {M : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Module.FaithfullyFlat R A]

/-- A faithfully flat extension of scalars, for instance a field extension, sends only the
identity to the identity. -/
@[simp]
theorem baseChange_eq_one_iff {e : M ≃ₗ[R] M} : e.baseChange R A M M = 1 ↔ e = 1 := by
  rw [← baseChange_one R A M, ← toLinearMap_inj, ← toLinearMap_inj, coe_baseChange,
    coe_baseChange]
  exact LinearMap.baseChange_injective.eq_iff

end LinearEquiv

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
    (hL :
      (AlgebraTensorModule.cancelBaseChange E E₁ L L W).toLinearMap ∘ₗ
          f₁.baseChange L ∘ₗ
          (AlgebraTensorModule.cancelBaseChange E E₁ L L V).symm.toLinearMap =
        (AlgebraTensorModule.cancelBaseChange E E₂ L L W).toLinearMap ∘ₗ
          f₂.baseChange L ∘ₗ
          (AlgebraTensorModule.cancelBaseChange E E₂ L L V).symm.toLinearMap) :
    (AlgebraTensorModule.cancelBaseChange E E₁ E' E' W).toLinearMap ∘ₗ
        f₁.baseChange E' ∘ₗ
        (AlgebraTensorModule.cancelBaseChange E E₁ E' E' V).symm.toLinearMap =
      (AlgebraTensorModule.cancelBaseChange E E₂ E' E' W).toLinearMap ∘ₗ
        f₂.baseChange E' ∘ₗ
        (AlgebraTensorModule.cancelBaseChange E E₂ E' E' V).symm.toLinearMap := by
  -- `LinearMap.baseChange_injective` requires `AddCommGroup`, which `E' ⊗[E] _` inherits from
  -- `[CommRing E']`.
  let : AddCommGroup (E' ⊗[E] V) := Module.addCommMonoidToAddCommGroup E'
  let : AddCommGroup (E' ⊗[E] W) := Module.addCommMonoidToAddCommGroup E'
  apply LinearMap.baseChange_injective (R := E') (A := L)
  ext v
  apply (AlgebraTensorModule.cancelBaseChange E E' L L W).injective
  have hv := LinearMap.congr_fun hL ((1 : L) ⊗ₜ[E] v)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    AlgebraTensorModule.cancelBaseChange_symm_tmul, LinearMap.baseChange_tmul] at hv
  simp only [AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
    LinearMap.restrictScalars_apply, LinearMap.baseChange_tmul, LinearMap.comp_apply,
    LinearEquiv.coe_coe, AlgebraTensorModule.cancelBaseChange_symm_tmul]
  exact (AlgebraTensorModule.cancelBaseChange_one_tmul_cancelBaseChange _).trans
    (hv.trans (AlgebraTensorModule.cancelBaseChange_one_tmul_cancelBaseChange _).symm)

/-- Scalar-tower naturality for a single scalar multiple of a base-changed linear map. -/
theorem cancelBaseChange_comp_smul_baseChange
    {E E' L V W : Type*} [CommSemiring E] [CommSemiring E'] [CommSemiring L]
    [Algebra E E'] [Algebra E L] [Algebra E' L] [IsScalarTower E E' L]
    [AddCommMonoid V] [Module E V] [AddCommMonoid W] [Module E W]
    (c : E') (g : V →ₗ[E] W) :
    (AlgebraTensorModule.cancelBaseChange E E' L L W).toLinearMap ∘ₗ
        (c • g.baseChange E').baseChange L =
      (algebraMap E' L c • g.baseChange L) ∘ₗ
        (AlgebraTensorModule.cancelBaseChange E E' L L V).toLinearMap := by
  ext v
  simp [TensorProduct.smul_tmul', Algebra.smul_def]

/-- Scalar-tower naturality for a finite sum of scalar multiples of base-changed linear maps. -/
theorem cancelBaseChange_comp_sum_smul_baseChange
    {E E' L V W ι : Type*} [CommSemiring E] [CommSemiring E'] [CommSemiring L]
    [Algebra E E'] [Algebra E L] [Algebra E' L] [IsScalarTower E E' L]
    [AddCommMonoid V] [Module E V] [AddCommMonoid W] [Module E W]
    (s : Finset ι) (c : ι → E') (g : ι → (V →ₗ[E] W)) :
    (AlgebraTensorModule.cancelBaseChange E E' L L W).toLinearMap ∘ₗ
        (∑ i ∈ s, c i • (g i).baseChange E').baseChange L =
      (∑ i ∈ s, algebraMap E' L (c i) • (g i).baseChange L) ∘ₗ
        (AlgebraTensorModule.cancelBaseChange E E' L L V).toLinearMap := by
  rw [← LinearMap.baseChangeHom_apply, map_sum,
    ← LinearMap.llcomp_apply' (R₃ := L)
      (AlgebraTensorModule.cancelBaseChange E E' L L W).toLinearMap,
    map_sum,
    ← LinearMap.lcomp_apply' (S := L) (N := L ⊗[E] W)
      (AlgebraTensorModule.cancelBaseChange E E' L L V).toLinearMap,
    map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simpa only [LinearMap.baseChangeHom_apply, LinearMap.llcomp_apply', LinearMap.lcomp_apply'] using
    cancelBaseChange_comp_smul_baseChange (c i) (g i)

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
