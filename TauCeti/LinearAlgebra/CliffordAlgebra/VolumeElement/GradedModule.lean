/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Grading
public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Complex
public import TauCeti.LinearAlgebra.Eigenspace.TensorProduct.Involution
public import TauCeti.RingTheory.Morita.ModuleEnd
-- Private: transporting eigenspaces along the evaluation isomorphism.
import TauCeti.LinearAlgebra.Eigenspace.Transport

/-!
# Graded Clifford modules and their multiplicity spaces

Let `V` be an oriented real inner product space of even dimension `n`, `Q v = -‖v‖²`, and
`Cℓ = CliffordAlgebra (Q.baseChange ℂ)`. A **graded** `Cℓ`-module is a module `E` with an involution
`γ` anticommuting with Clifford multiplication by every vector,

`γ (c(w) ψ) = -c(w) γ ψ`,

so that every `a ∈ Cℓ` satisfies `γ (a ψ) = involute a • γ ψ`
(`CliffordAlgebra.apply_smul_eq_involute_smul`). The chirality `Γ`
(`CliffordAlgebra.complexVolume`) is the intrinsic example. In even dimension `Γ` is a product of
an even number of vectors, so it commutes with `γ`, and the product

`γ_W = γ Γ`  (`CliffordAlgebra.twistingGrading`)

is a `Cℓ`-linear involution of `E` with `γ = Γ γ_W`. Postcomposition with it is therefore the
**induced grading** of the multiplicity space `W = Hom_Cℓ(S, E)` of a spinor module `S`, on which
`Cℓ` acts as all of `End_ℂ S`. Through the Morita evaluation
`S ⊗ Hom_Cℓ(S, E) ≃ E`, `s ⊗ T ↦ T s` (`TauCeti.isotypicTensorEquivOfBijective`), the grading of `E`
becomes the tensor grading:

`γ (T s) = T' (Γ s)`  for `T' = γ_W ∘ T`,  that is,  `γ ↔ Γ_S ⊗ γ_W`.

Combined with the eigenspaces of a tensor product of involutions
(`Module.End.eigenspaceTensorMapEquiv`), the even and odd parts of `E` are

`E^{γ = 1} ≃ S⁺ ⊗ W⁺ × S⁻ ⊗ W⁻`,  `E^{γ = -1} ≃ S⁺ ⊗ W⁻ × S⁻ ⊗ W⁺`

(`CliffordAlgebra.eigenspaceTwistingGradingEquiv`), where `S^±` are the half-spin spaces and `W^±`
the eigenspaces of the induced grading. The chiral grading `Γ` of `E` is instead `Γ_S ⊗ 1`, since
`Cℓ` acts on `S ⊗ W` through the left factor.

Conversely, for any complex vector space `A` with an involution `γ_A`, the **graded twist** `S ⊗ A`
carries the Clifford action `c(w) ⊗ 1` and the tensor grading `Γ ⊗ γ_A`, which anticommutes with
every vector (`CliffordAlgebra.map_lsmul_complexVolume_ι_smul`). Its twisting grading is `1 ⊗ γ_A`
(`CliffordAlgebra.twistingGrading_map_lsmul_complexVolume_apply`): it acts on the twisting factor
`A` by the given grading, while the chirality acts by `Γ ⊗ 1`. Its even part
`S⁺ ⊗ A⁺ ⊕ S⁻ ⊗ A⁻` and odd part `S⁺ ⊗ A⁻ ⊕ S⁻ ⊗ A⁺` are `Module.End.eigenspaceTensorMapEquiv` for
`Γ` and `γ_A`.

## Main definitions

* `CliffordAlgebra.twistingGrading`: the `Cℓ`-linear involution `γ Γ` of a graded module.
* `CliffordAlgebra.eigenspaceTwistingGradingEquiv`: the eigenspaces of the grading of `E` in terms
  of the half-spin spaces and the graded multiplicity space.

## Main results

* `CliffordAlgebra.complexVolume_smul_twistingGrading`: `γ = Γ γ_W`.
* `CliffordAlgebra.eigenspaceTwistingGradingEquiv_apply`: the components of an eigenvector of `γ`.
* `CliffordAlgebra.isotypicEval_map_twistingGrading`: evaluation intertwines `Γ ⊗ γ_W` with `γ`.
* `CliffordAlgebra.map_lsmul_complexVolume_ι_smul`: the graded twist is a graded module.
* `CliffordAlgebra.twistingGrading_map_lsmul_complexVolume_apply`: its twisting grading is
  `1 ⊗ γ_A`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
* N. Berline, E. Getzler and M. Vergne, *Heat Kernels and Dirac Operators* (1992), Chapter 3.
-/

public section

noncomputable section

open Module Module.End TauCeti TensorProduct

namespace CliffordAlgebra

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {n : ℕ} [Fact (finrank ℝ V = n)] {Q : QuadraticForm ℝ V} (o : Orientation ℝ V (Fin n))
variable {E : Type*} [AddCommGroup E] [Module ℂ E] [Module (CliffordAlgebra (Q.baseChange ℂ)) E]
  [IsScalarTower ℂ (CliffordAlgebra (Q.baseChange ℂ)) E]

/-! ### The twisting grading of a graded module -/

section Grading

variable (hn : Even n) {γ : E →ₗ[ℂ] E}
  (hγ : ∀ w (ψ : E), γ (ι (Q.baseChange ℂ) w • ψ) = -(ι (Q.baseChange ℂ) w • γ ψ))

include hn hγ in
/-- In even dimension a grading commutes with the chirality: `γ (Γ ψ) = Γ γ ψ`. -/
theorem apply_complexVolume_smul (ψ : E) :
    γ (complexVolume Q o • ψ) = complexVolume Q o • γ ψ := by
  rw [apply_smul_eq_involute_smul hγ, involute_complexVolume, hn.neg_one_pow, one_smul]

variable (γ) in
/-- **The twisting grading** `γ_W = γ Γ` of a graded module over the complexified Clifford algebra
of an even-dimensional oriented space: the product of the grading `γ`, which anticommutes with
every vector, and the chirality `Γ`. It commutes with the whole Clifford algebra, so
postcomposition with it grades the multiplicity space `Hom_Cℓ(S, E)` of a spinor module `S`, and
evaluation `S ⊗ Hom_Cℓ(S, E) → E` carries the tensor grading `Γ ⊗ γ_W` to `γ`
(`CliffordAlgebra.isotypicEval_map_twistingGrading`). -/
def twistingGrading : E →ₗ[CliffordAlgebra (Q.baseChange ℂ)] E where
  toFun ψ := γ (complexVolume Q o • ψ)
  map_add' ψ φ := by rw [smul_add, map_add]
  map_smul' a ψ := by
    rw [RingHom.id_apply, ← mul_smul, complexVolume_mul_eq_involute_mul o hn, mul_smul,
      apply_smul_eq_involute_smul hγ, involute_involute]

/-- The twisting grading applies the chirality and then the grading. -/
@[simp]
theorem twistingGrading_apply (ψ : E) :
    twistingGrading o hn γ hγ ψ = γ (complexVolume Q o • ψ) :=
  (rfl)

variable (hQ : ∀ v, Q v = -‖v‖ ^ 2)
include hQ

/-- **The grading factors through the chirality**: `γ = Γ γ_W`. -/
theorem complexVolume_smul_twistingGrading (ψ : E) :
    complexVolume Q o • twistingGrading o hn γ hγ ψ = γ ψ := by
  rw [twistingGrading_apply, ← apply_complexVolume_smul o hn hγ,
    complexVolume_smul_complexVolume_smul o hQ]

/-- The twisting grading of an involutive grading is an involution. -/
theorem twistingGrading_involutive (hγ₂ : Function.Involutive γ) :
    Function.Involutive (twistingGrading o hn γ hγ) := fun ψ ↦ by
  rw [twistingGrading_apply, twistingGrading_apply, apply_complexVolume_smul o hn hγ, hγ₂,
    complexVolume_smul_complexVolume_smul o hQ]

/-! ### The multiplicity space of a graded module -/

variable {S : Type*} [AddCommGroup S] [Module ℂ S] [Module (CliffordAlgebra (Q.baseChange ℂ)) S]
  [IsScalarTower ℂ (CliffordAlgebra (Q.baseChange ℂ)) S]

/-- **Evaluation is graded**: through `S ⊗ Hom_Cℓ(S, E) → E`, `s ⊗ T ↦ T s`, the tensor grading
`Γ ⊗ γ_W` of the chirality of `S` and the twisting grading acting on the multiplicity space becomes
the grading `γ` of `E`. -/
theorem isotypicEval_map_twistingGrading (x : S ⊗[ℂ] (S →ₗ[CliffordAlgebra (Q.baseChange ℂ)] E)) :
    isotypicEval ℂ (TensorProduct.map (Algebra.lsmul ℂ ℂ S (complexVolume Q o))
        (LinearMap.compRight ℂ (twistingGrading o hn γ hγ)) x) =
      γ (isotypicEval ℂ x) := by
  induction x using TensorProduct.inductionOn with
  | tmul s T =>
    rw [map_tmul, isotypicEval_tmul, isotypicEval_tmul, LinearMap.compRight_apply,
      LinearMap.comp_apply, twistingGrading_apply, Algebra.lsmul_coe, ← LinearMap.map_smul,
      complexVolume_smul_complexVolume_smul o hQ]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

omit [Module ℂ S] [IsScalarTower ℂ (CliffordAlgebra (Q.baseChange ℂ)) S] in
/-- Postcomposition with the twisting grading of an involutive grading is an involution of the
multiplicity space `Hom_Cℓ(S, E)`. -/
theorem compRight_twistingGrading_involutive (hγ₂ : Function.Involutive γ) :
    Function.Involutive (LinearMap.compRight (M := S) ℂ (twistingGrading o hn γ hγ)) :=
  fun T ↦ LinearMap.ext fun s ↦ by
    simp only [LinearMap.compRight_apply, LinearMap.comp_apply,
      twistingGrading_involutive o hn hγ hQ hγ₂ (T s)]

variable [Module.Finite ℂ S]
  (h : Function.Bijective
    (Algebra.lsmul ℂ ℂ S : CliffordAlgebra (Q.baseChange ℂ) →ₐ[ℂ] Module.End ℂ S))

/-- **The even and odd parts of a graded module.** Let `S` be a spinor module, on which the
complexified Clifford algebra acts as all of `End_ℂ S`, and let `γ` be an involutive grading of
`E`. Write `S^±` for the half-spin spaces, the `±1`-eigenspaces of `Γ`, and `W^ν` for the
eigenspaces of the twisting grading acting on the multiplicity space `W = Hom_Cℓ(S, E)`. Then for
`μ * μ = 1` evaluation identifies

`E^{γ = μ} ≃ S⁺ ⊗ W^μ × S⁻ ⊗ W^{-μ}`;

so the even part of `E` is `S⁺ ⊗ W⁺ ⊕ S⁻ ⊗ W⁻` and the odd part is `S⁺ ⊗ W⁻ ⊕ S⁻ ⊗ W⁺`. -/
def eigenspaceTwistingGradingEquiv (hγ₂ : Function.Involutive γ) {μ : ℂ} (hμ : μ * μ = 1) :
    eigenspace γ μ ≃ₗ[ℂ]
      ((Algebra.lsmul ℂ ℂ S (complexVolume Q o)).eigenspace 1 ⊗[ℂ]
          eigenspace (LinearMap.compRight (M := S) ℂ (twistingGrading o hn γ hγ)) μ) ×
        ((Algebra.lsmul ℂ ℂ S (complexVolume Q o)).eigenspace (-1) ⊗[ℂ]
          eigenspace (LinearMap.compRight (M := S) ℂ (twistingGrading o hn γ hγ)) (-μ)) :=
  let e := (isotypicTensorEquivOfBijective h (M := E)).restrictScalars ℂ
  (e.ofSubmodule' (eigenspace γ μ)).symm ≪≫ₗ
    (LinearEquiv.ofEq _ _ (eigenspace_eq_comap_of_intertwine (e := e)
      (fun x ↦ by simpa [e] using isotypicEval_map_twistingGrading o hn hγ hQ x) μ).symm) ≪≫ₗ
    eigenspaceTensorMapEquiv _ _ (lsmul_complexVolume_involutive o hQ)
      (compRight_twistingGrading_involutive o hn hγ hQ hγ₂) hμ

/-- The forward map of `CliffordAlgebra.eigenspaceTwistingGradingEquiv` inverts evaluation and
then applies the tensor products of the eigenspace projections of `Γ` and of the twisting grading
on the multiplicity space, as in `Module.End.eigenspaceTensorMapEquiv_apply`. -/
theorem eigenspaceTwistingGradingEquiv_apply (hγ₂ : Function.Involutive γ) {μ : ℂ}
    (hμ : μ * μ = 1) (z : eigenspace γ μ) :
    eigenspaceTwistingGradingEquiv o hn hγ hQ h hγ₂ hμ z =
      (TensorProduct.map
          (eigenProjOfInvolutive (lsmul_complexVolume_involutive o hQ) (one_mul 1))
          (eigenProjOfInvolutive (compRight_twistingGrading_involutive o hn hγ hQ hγ₂) hμ)
          ((isotypicTensorEquivOfBijective h).symm z),
        TensorProduct.map
          (eigenProjOfInvolutive (lsmul_complexVolume_involutive o hQ)
            ((neg_mul_neg (1 : ℂ) 1).trans (one_mul 1)))
          (eigenProjOfInvolutive (compRight_twistingGrading_involutive o hn hγ hQ hγ₂)
            ((neg_mul_neg μ μ).trans hμ))
          ((isotypicTensorEquivOfBijective h).symm z)) := by
  simp only [eigenspaceTwistingGradingEquiv, LinearEquiv.trans_apply]
  rw [eigenspaceTensorMapEquiv_apply, LinearEquiv.coe_ofEq_apply,
    LinearEquiv.ofSubmodule'_symm_apply, LinearEquiv.restrictScalars_symm_apply]

/-- The inverse of `CliffordAlgebra.eigenspaceTwistingGradingEquiv` is evaluation, `s ⊗ T ↦ T s`,
on both summands. -/
@[simp]
theorem coe_eigenspaceTwistingGradingEquiv_symm_apply (hγ₂ : Function.Involutive γ) {μ : ℂ}
    (hμ : μ * μ = 1)
    (p : ((Algebra.lsmul ℂ ℂ S (complexVolume Q o)).eigenspace 1 ⊗[ℂ]
          eigenspace (LinearMap.compRight (M := S) ℂ (twistingGrading o hn γ hγ)) μ) ×
        ((Algebra.lsmul ℂ ℂ S (complexVolume Q o)).eigenspace (-1) ⊗[ℂ]
          eigenspace (LinearMap.compRight (M := S) ℂ (twistingGrading o hn γ hγ)) (-μ))) :
    ((eigenspaceTwistingGradingEquiv o hn hγ hQ h hγ₂ hμ).symm p : E) =
      isotypicEval ℂ (TensorProduct.map (Submodule.subtype _) (Submodule.subtype _) p.1 +
        TensorProduct.map (Submodule.subtype _) (Submodule.subtype _) p.2) := by
  simp only [eigenspaceTwistingGradingEquiv, LinearEquiv.trans_symm, LinearEquiv.ofEq_symm,
    LinearEquiv.symm_symm, LinearEquiv.trans_apply, LinearEquiv.ofSubmodule'_apply,
    LinearEquiv.coe_ofEq_apply, LinearEquiv.restrictScalars_apply,
    isotypicTensorEquivOfBijective_apply]
  exact congrArg (isotypicEval ℂ) (coe_eigenspaceTensorMapEquiv_symm_apply _ _ _ p)

end Grading

/-! ### The graded twist `S ⊗ A` -/

section Twist

variable (hn : Even n)
variable {S : Type*} [AddCommGroup S] [Module ℂ S] [Module (CliffordAlgebra (Q.baseChange ℂ)) S]
  [IsScalarTower ℂ (CliffordAlgebra (Q.baseChange ℂ)) S]
variable {A : Type*} [AddCommGroup A] [Module ℂ A] (γA : A →ₗ[ℂ] A)

include hn in
/-- **The graded twist is a graded module**: on `S ⊗ A`, with Clifford action `c(w) ⊗ 1`, the
tensor grading `Γ ⊗ γ_A` anticommutes with every vector. -/
theorem map_lsmul_complexVolume_ι_smul (w : ℂ ⊗[ℝ] V) (z : S ⊗[ℂ] A) :
    TensorProduct.map (Algebra.lsmul ℂ ℂ S (complexVolume Q o)) γA (ι (Q.baseChange ℂ) w • z) =
      -(ι (Q.baseChange ℂ) w •
        TensorProduct.map (Algebra.lsmul ℂ ℂ S (complexVolume Q o)) γA z) := by
  induction z using TensorProduct.inductionOn with
  | tmul s a =>
    simp only [smul_tmul', map_tmul, Algebra.lsmul_coe, ← mul_smul,
      complexVolume_mul_ι_of_even o hn, neg_smul, neg_tmul]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add, neg_add]

/-- **The twisting grading of the graded twist** `S ⊗ A` is `1 ⊗ γ_A`: it acts on the twisting
factor `A` by the given grading. -/
theorem twistingGrading_map_lsmul_complexVolume_apply (hQ : ∀ v, Q v = -‖v‖ ^ 2)
    (z : S ⊗[ℂ] A) :
    twistingGrading o hn (TensorProduct.map (Algebra.lsmul ℂ ℂ S (complexVolume Q o)) γA)
        (map_lsmul_complexVolume_ι_smul o hn γA) z =
      γA.lTensor S z := by
  induction z using TensorProduct.inductionOn with
  | tmul s a =>
    simp only [twistingGrading_apply, smul_tmul', map_tmul, Algebra.lsmul_coe,
      complexVolume_smul_complexVolume_smul o hQ, LinearMap.lTensor_tmul]
  | add x y hx hy => rw [map_add, hx, hy, map_add]

end Twist

end CliffordAlgebra
