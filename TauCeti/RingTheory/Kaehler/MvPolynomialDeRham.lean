/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.LinearAlgebra.ExteriorAlgebra.BaseChange
import TauCeti.LinearAlgebra.ExteriorAlgebra.Contraction
import TauCeti.LinearAlgebra.ExteriorAlgebra.Derivation
import TauCeti.LinearAlgebra.ExteriorPower.Basic

/-!
# The algebraic de Rham complex of a multivariate polynomial ring

For any commutative ring `B` and arbitrary variable type `σ`, the Kähler differential module
`Ω[MvPolynomial σ B⁄B]` is free over `P = MvPolynomial σ B` on `{dXᵢ | i ∈ σ}`. Base change of
the exterior algebra therefore identifies the full algebra of algebraic differential forms
`ExteriorAlgebra P (Ω[P⁄B])` with `P ⊗[R] ExteriorAlgebra R (σ →₀ R)` for any commutative ring
`R` with an algebra map `R → B` (`TauCeti.MvPolynomialDeRham.tensorEquiv`).

In this trivialization, the algebraic exterior derivative `TauCeti.MvPolynomialDeRham.d B σ` sends
`p ⊗ₜ ω` to `ι P (D B P p) * (1 ⊗ₜ ω)`. It satisfies:

* `d (algebraMap P _ p) = ι P (KaehlerDifferential.D B P p)` and `d (ι P (D B P (X i))) = 0`,
* the graded Leibniz rule `d (α * β) = d α * β + involute α * d β`,
* `d (d α) = 0` unconditionally over every commutative ring `B`, including in characteristic two,
* degree shift `⋀[P]^n Ω[P⁄B] → ⋀[P]^(n + 1) Ω[P⁄B]`,
* preservation of the subalgebra `supportedForms B s` of forms using only variables in `s`.

For any `R`-derivation `D : Derivation R P P`, the algebraic Lie derivative
`TauCeti.MvPolynomialDeRham.lieDeriv D` is the unique degree-zero `R`-derivation of
`ExteriorAlgebra P (Ω[P⁄B])` acting as `D` on coefficients `algebraMap P _ p` and sending
`ι P (D B P (X i))` to `ι P (D B P (D (X i)))`. Whenever `D` maps constants `C b` to elements
with zero relative differential (in particular, for every `B`-derivation or every coefficient-wise
extension of a derivation on `B`), `lieDeriv D` commutes with the exterior derivative `d` and
preserves commutativity of derivations.

## Main definitions

* `TauCeti.MvPolynomialDeRham.tensorEquiv`: algebra isomorphism
  `MvPolynomial σ B ⊗[R] ExteriorAlgebra R (σ →₀ R) ≃ₐ[MvPolynomial σ B]
    ExteriorAlgebra (MvPolynomial σ B) (Ω[MvPolynomial σ B⁄B])`.
* `TauCeti.MvPolynomialDeRham.d`: the exterior derivative on algebraic polynomial forms.
* `TauCeti.MvPolynomialDeRham.lieDeriv`: the algebraic Lie derivative along an `R`-derivation.
* `TauCeti.MvPolynomialDeRham.supportedForms`: the subalgebra of forms supported on a set of
  variables.

## Main results

* `TauCeti.MvPolynomialDeRham.d_mul`: graded Leibniz rule for `d`.
* `TauCeti.MvPolynomialDeRham.d_d`: `d (d α) = 0`.
* `TauCeti.MvPolynomialDeRham.d_mem_exteriorPower`: `d` shifts exterior degree by one.
* `TauCeti.MvPolynomialDeRham.d_lieDeriv`: `d` commutes with `lieDeriv D`.
* `TauCeti.MvPolynomialDeRham.lieDeriv_comm`: commuting derivations have commuting Lie derivatives.
* `TauCeti.MvPolynomialDeRham.d_mem_supportedForms` and
  `TauCeti.MvPolynomialDeRham.exists_mem_supportedForms_finset`: finite-variable support.
-/

public section

open ExteriorAlgebra KaehlerDifferential MvPolynomial TensorProduct

namespace TauCeti.MvPolynomialDeRham

noncomputable section

section TensorEquiv

variable (R B σ : Type*) [CommRing R] [CommRing B] [Algebra R B]

/-- The `MvPolynomial σ B`-linear equivalence `P ⊗[R] (σ →₀ R) ≃ₗ[P] Ω[P⁄B]`. -/
private def moduleEquiv :
    MvPolynomial σ B ⊗[R] (σ →₀ R) ≃ₗ[MvPolynomial σ B] Ω[MvPolynomial σ B⁄B] := by
  classical
  exact (TensorProduct.finsuppScalarRight R (MvPolynomial σ B) (MvPolynomial σ B) σ).trans
    (KaehlerDifferential.mvPolynomialEquiv B σ).symm

/-- Algebra equivalence on exterior algebras induced by a linear equivalence of modules. -/
private def exteriorMapEquiv {A M N : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (e : M ≃ₗ[A] N) :
    ExteriorAlgebra A M ≃ₐ[A] ExteriorAlgebra A N :=
  AlgEquiv.ofAlgHom (ExteriorAlgebra.map e.toLinearMap) (ExteriorAlgebra.map e.symm.toLinearMap)
    (by ext m; simp) (by ext m; simp)

/-- **Tensor-product trivialization of polynomial forms**: for any commutative algebra tower
`R → B → MvPolynomial σ B`, the exterior algebra of Kähler differentials `Ω[MvPolynomial σ B⁄B]`
is isomorphic as an `MvPolynomial σ B`-algebra to
`MvPolynomial σ B ⊗[R] ExteriorAlgebra R (σ →₀ R)`. -/
def tensorEquiv :
    MvPolynomial σ B ⊗[R] ExteriorAlgebra R (σ →₀ R) ≃ₐ[MvPolynomial σ B]
      ExteriorAlgebra (MvPolynomial σ B) (Ω[MvPolynomial σ B⁄B]) :=
  (ExteriorAlgebra.baseChangeEquiv R (σ →₀ R) (MvPolynomial σ B)).trans
    (exteriorMapEquiv (moduleEquiv R B σ))

variable {R B σ}

private theorem moduleEquiv_tmul_single (p : MvPolynomial σ B) (i : σ) :
    moduleEquiv R B σ (p ⊗ₜ[R] Finsupp.single i (1 : R)) =
      p • KaehlerDifferential.D B (MvPolynomial σ B) (X i) := by
  classical
  have hsingle : TensorProduct.finsuppScalarRight R (MvPolynomial σ B) (MvPolynomial σ B) σ
      (p ⊗ₜ[R] Finsupp.single i (1 : R)) = Finsupp.single i p := by
    rw [← TensorProduct.finsuppScalarRight_symm_apply_single (R := R) (S := MvPolynomial σ B)
      (M := MvPolynomial σ B) (ι := σ) i p, LinearEquiv.apply_symm_apply]
  rw [moduleEquiv, LinearEquiv.trans_apply, hsingle]
  exact KaehlerDifferential.mvPolynomialBasis_repr_symm_single B σ i p

/-- Under `tensorEquiv`, `p ⊗ₜ 1` corresponds to the zero-form `algebraMap p`. -/
@[simp]
theorem tensorEquiv_tmul_one (p : MvPolynomial σ B) :
    tensorEquiv R B σ (p ⊗ₜ[R] (1 : ExteriorAlgebra R (σ →₀ R))) =
      algebraMap (MvPolynomial σ B) _ p := by
  have h1 : p ⊗ₜ[R] (1 : ExteriorAlgebra R (σ →₀ R)) =
      algebraMap (MvPolynomial σ B) (MvPolynomial σ B ⊗[R] ExteriorAlgebra R (σ →₀ R)) p := by
    simp [Algebra.TensorProduct.algebraMap_apply]
  rw [h1, AlgEquiv.commutes]

/-- Under `tensorEquiv`, `1 ⊗ₜ ι (single i 1)` corresponds to the coordinate one-form `dXᵢ`. -/
theorem tensorEquiv_one_tmul_ι_single (i : σ) :
    tensorEquiv R B σ (1 ⊗ₜ[R] ι R (Finsupp.single i (1 : R))) =
      ι (MvPolynomial σ B) (KaehlerDifferential.D B (MvPolynomial σ B) (X i)) := by
  simp only [tensorEquiv, AlgEquiv.trans_apply, ExteriorAlgebra.baseChangeEquiv_apply,
    exteriorMapEquiv, AlgEquiv.ofAlgHom_apply, ExteriorAlgebra.map_apply_ι,
    LinearEquiv.coe_coe, moduleEquiv_tmul_single, one_smul]

/-- Under `tensorEquiv`, `p ⊗ₜ ι (single i 1)` corresponds to `p • dXᵢ`. -/
@[simp]
theorem tensorEquiv_tmul_ι_single (p : MvPolynomial σ B) (i : σ) :
    tensorEquiv R B σ (p ⊗ₜ[R] ι R (Finsupp.single i (1 : R))) =
      p • ι (MvPolynomial σ B) (KaehlerDifferential.D B (MvPolynomial σ B) (X i)) := by
  have hp : p ⊗ₜ[R] ι R (Finsupp.single i (1 : R)) =
      p • ((1 : MvPolynomial σ B) ⊗ₜ[R] ι R (Finsupp.single i (1 : R))) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [hp, map_smul, tensorEquiv_one_tmul_ι_single]

/-- The inverse trivialization sends a zero-form `algebraMap p` to `p ⊗ₜ 1`. -/
theorem tensorEquiv_symm_algebraMap (p : MvPolynomial σ B) :
    (tensorEquiv R B σ).symm (algebraMap (MvPolynomial σ B) _ p) = p ⊗ₜ[R] 1 := by
  apply (tensorEquiv R B σ).injective
  rw [AlgEquiv.apply_symm_apply, tensorEquiv_tmul_one]

/-- The inverse trivialization sends `dXᵢ` to `1 ⊗ₜ ι (single i 1)`. -/
@[simp]
theorem tensorEquiv_symm_ι_D_X (i : σ) :
    (tensorEquiv R B σ).symm
        (ι (MvPolynomial σ B) (KaehlerDifferential.D B (MvPolynomial σ B) (X i))) =
      1 ⊗ₜ[R] ι R (Finsupp.single i (1 : R)) := by
  apply (tensorEquiv R B σ).injective
  rw [AlgEquiv.apply_symm_apply, tensorEquiv_one_tmul_ι_single]

/-- The trivialization `tensorEquiv` commutes with the grade involution on the exterior factor. -/
theorem tensorEquiv_involute (p : MvPolynomial σ B) (ω : ExteriorAlgebra R (σ →₀ R)) :
    CliffordAlgebra.involute (Q := (0 : QuadraticForm (MvPolynomial σ B) _))
        (tensorEquiv R B σ (p ⊗ₜ[R] ω)) =
      tensorEquiv R B σ (p ⊗ₜ[R] CliffordAlgebra.involute (Q := (0 : QuadraticForm R _)) ω) := by
  have h1 : ∀ η : ExteriorAlgebra R (σ →₀ R),
      CliffordAlgebra.involute (Q := (0 : QuadraticForm (MvPolynomial σ B) _))
          (tensorEquiv R B σ (1 ⊗ₜ[R] η)) =
        tensorEquiv R B σ
          (1 ⊗ₜ[R] CliffordAlgebra.involute (Q := (0 : QuadraticForm R _)) η) := by
    intro η
    induction η using CliffordAlgebra.induction with
    | algebraMap r =>
      have hrm : (1 : MvPolynomial σ B) ⊗ₜ[R] algebraMap R (ExteriorAlgebra R (σ →₀ R)) r =
          algebraMap R (MvPolynomial σ B) r ⊗ₜ[R] 1 := by
        rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
          TensorProduct.smul_tmul']
      rw [AlgHom.commutes, hrm, tensorEquiv_tmul_one, AlgHom.commutes]
    | ι m =>
      simp only [CliffordAlgebra.involute_ι, TensorProduct.tmul_neg, map_neg]
      simp only [tensorEquiv, AlgEquiv.trans_apply, ExteriorAlgebra.baseChangeEquiv_apply,
        exteriorMapEquiv, AlgEquiv.ofAlgHom_apply, ExteriorAlgebra.map_apply_ι,
        LinearEquiv.coe_coe, CliffordAlgebra.involute_ι]
    | mul a b ha hb =>
      have hmul : (1 : MvPolynomial σ B) ⊗ₜ[R] (a * b) =
          (1 ⊗ₜ[R] a) * (1 ⊗ₜ[R] b) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
      have hmul' : (1 : MvPolynomial σ B) ⊗ₜ[R]
          (CliffordAlgebra.involute (Q := (0 : QuadraticForm R _)) a *
            CliffordAlgebra.involute (Q := (0 : QuadraticForm R _)) b) =
          (1 ⊗ₜ[R] CliffordAlgebra.involute (Q := (0 : QuadraticForm R _)) a) *
            (1 ⊗ₜ[R] CliffordAlgebra.involute (Q := (0 : QuadraticForm R _)) b) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
      rw [hmul, map_mul, map_mul, ha, hb, map_mul, hmul', map_mul]
    | add a b ha hb =>
      rw [TensorProduct.tmul_add, map_add, map_add, ha, hb, map_add, TensorProduct.tmul_add,
        map_add]
  have hp : p ⊗ₜ[R] ω = p • ((1 : MvPolynomial σ B) ⊗ₜ[R] ω) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hp' : p ⊗ₜ[R] CliffordAlgebra.involute (Q := (0 : QuadraticForm R _)) ω =
      p • ((1 : MvPolynomial σ B) ⊗ₜ[R]
        CliffordAlgebra.involute (Q := (0 : QuadraticForm R _)) ω) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [hp, hp', map_smul, map_smul, map_smul, h1]

/-- `tensorEquiv` sends pure tensors of degree `n` into the `n`-th exterior power of
`Ω[MvPolynomial σ B⁄B]`. -/
theorem tensorEquiv_tmul_mem_exteriorPower {n : ℕ} (p : MvPolynomial σ B)
    {ω : ExteriorAlgebra R (σ →₀ R)} (hω : ω ∈ ⋀[R]^n (σ →₀ R)) :
    tensorEquiv R B σ (p ⊗ₜ[R] ω) ∈
      ⋀[MvPolynomial σ B]^n (Ω[MvPolynomial σ B⁄B]) := by
  have hp : p ⊗ₜ[R] ω = p • ((1 : MvPolynomial σ B) ⊗ₜ[R] ω) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [hp, map_smul]
  refine Submodule.smul_mem _ p ?_
  clear hp
  induction hω using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    have hrm : (1 : MvPolynomial σ B) ⊗ₜ[R] algebraMap R (ExteriorAlgebra R (σ →₀ R)) r =
        algebraMap R (MvPolynomial σ B) r ⊗ₜ[R] 1 := by
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
        TensorProduct.smul_tmul']
    rw [hrm, tensorEquiv_tmul_one]
    exact Submodule.algebraMap_mem _
  | add x y i _ _ ihx ihy =>
    rw [TensorProduct.tmul_add, map_add]
    exact add_mem ihx ihy
  | mem_mul m hm i x _ ih =>
    obtain ⟨v, rfl⟩ := hm
    have hmul : (1 : MvPolynomial σ B) ⊗ₜ[R] (ι R v * x) =
        (1 ⊗ₜ[R] ι R v) * (1 ⊗ₜ[R] x) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    rw [hmul, map_mul]
    have hι : tensorEquiv R B σ (1 ⊗ₜ[R] ι R v) =
        ι (MvPolynomial σ B) (moduleEquiv R B σ (1 ⊗ₜ[R] v)) := by
      simp [tensorEquiv, exteriorMapEquiv, ExteriorAlgebra.baseChangeEquiv_apply]
    rw [hι]
    exact TauCeti.ExteriorAlgebra.ι_mul_mem_exteriorPower _ ih

end TensorEquiv

section ExteriorDerivative

variable (B σ : Type*) [CommRing B]

/-- The exterior derivative on `MvPolynomial σ B ⊗[B] ExteriorAlgebra B (σ →₀ B)`, sending
`p ⊗ₜ ω` to `ι (D p) * tensorEquiv (1 ⊗ₜ ω)`. -/
private def dTensor :
    MvPolynomial σ B ⊗[B] ExteriorAlgebra B (σ →₀ B) →ₗ[B]
      ExteriorAlgebra (MvPolynomial σ B) (Ω[MvPolynomial σ B⁄B]) :=
  TensorProduct.lift
    { toFun := fun p ↦
        (LinearMap.mulLeft B
          (ι (MvPolynomial σ B) (KaehlerDifferential.D B (MvPolynomial σ B) p))).comp
          (((tensorEquiv B B σ).toLinearMap.restrictScalars B).comp
            (TensorProduct.mk B (MvPolynomial σ B) (ExteriorAlgebra B (σ →₀ B)) 1))
      map_add' := fun p q ↦ by
        ext ω
        simp [add_mul]
      map_smul' := fun b p ↦ by
        ext ω
        simp }

/-- **The algebraic exterior derivative** on polynomial differential forms
`ExteriorAlgebra (MvPolynomial σ B) (Ω[MvPolynomial σ B⁄B])`. -/
def d :
    ExteriorAlgebra (MvPolynomial σ B) (Ω[MvPolynomial σ B⁄B]) →ₗ[B]
      ExteriorAlgebra (MvPolynomial σ B) (Ω[MvPolynomial σ B⁄B]) :=
  (dTensor B σ).comp ((tensorEquiv B B σ).symm.toLinearMap.restrictScalars B)

variable {B σ}

private theorem d_tensorEquiv_self (p : MvPolynomial σ B) (ω : ExteriorAlgebra B (σ →₀ B)) :
    d B σ (tensorEquiv B B σ (p ⊗ₜ[B] ω)) =
      ι (MvPolynomial σ B) (KaehlerDifferential.D B (MvPolynomial σ B) p) *
        tensorEquiv B B σ (1 ⊗ₜ[B] ω) := by
  simp [d, dTensor]

/-- On zero-forms, `d` is the universal Kähler derivation `D`. -/
@[simp]
theorem d_algebraMap (p : MvPolynomial σ B) :
    d B σ (algebraMap (MvPolynomial σ B) _ p) =
      ι (MvPolynomial σ B) (KaehlerDifferential.D B (MvPolynomial σ B) p) := by
  rw [← tensorEquiv_tmul_one (R := B), d_tensorEquiv_self, tensorEquiv_tmul_one, map_one, mul_one]

/-- The exterior derivative vanishes on `1`. -/
@[simp]
theorem d_one : d B σ 1 = 0 := by
  simpa using d_algebraMap (B := B) (σ := σ) 1

/-- The exterior derivative vanishes on coordinate one-forms `dXᵢ`. -/
theorem d_ι_D_X (i : σ) :
    d B σ (ι (MvPolynomial σ B) (KaehlerDifferential.D B (MvPolynomial σ B) (X i))) = 0 := by
  rw [← tensorEquiv_one_tmul_ι_single (R := B), d_tensorEquiv_self, Derivation.map_one_eq_zero,
    map_zero, zero_mul]

/-- **Graded Leibniz rule**: `d (α * β) = d α * β + involute α * d β`. -/
theorem d_mul (α β : ExteriorAlgebra (MvPolynomial σ B) (Ω[MvPolynomial σ B⁄B])) :
    d B σ (α * β) =
      d B σ α * β +
        CliffordAlgebra.involute (Q := (0 : QuadraticForm (MvPolynomial σ B) _)) α * d B σ β := by
  obtain ⟨u, rfl⟩ := (tensorEquiv B B σ).surjective α
  obtain ⟨v, rfl⟩ := (tensorEquiv B B σ).surjective β
  induction u using TensorProduct.inductionOn with
  | add u₁ u₂ hu₁ hu₂ =>
    simp only [map_add, add_mul, hu₁, hu₂]
    abel
  | tmul p ω =>
    induction v using TensorProduct.inductionOn with
    | add v₁ v₂ hv₁ hv₂ =>
      simp only [map_add, mul_add, hv₁, hv₂]
      abel
    | tmul q η =>
      rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, d_tensorEquiv_self,
        d_tensorEquiv_self, d_tensorEquiv_self, Derivation.leibniz, map_add, map_smul, map_smul,
        add_mul]
      have h1ωη : tensorEquiv B B σ (1 ⊗ₜ[B] (ω * η)) =
          tensorEquiv B B σ (1 ⊗ₜ[B] ω) * tensorEquiv B B σ (1 ⊗ₜ[B] η) := by
        rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
      have hpω : tensorEquiv B B σ (p ⊗ₜ[B] ω) = p • tensorEquiv B B σ (1 ⊗ₜ[B] ω) := by
        rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      have hqη : tensorEquiv B B σ (q ⊗ₜ[B] η) = q • tensorEquiv B B σ (1 ⊗ₜ[B] η) := by
        rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [h1ωη, smul_mul_assoc, smul_mul_assoc, ← mul_assoc, ← mul_assoc,
        ExteriorAlgebra.ι_mul_eq_involute_mul, mul_assoc, ← smul_mul_assoc, ← map_smul, ← hpω,
        ← mul_smul_comm, ← hqη, add_comm]

/-- Graded Leibniz rule on a homogeneous `n`-form: `d (α * β) = d α * β + (-1) ^ n • (α * d β)`. -/
theorem d_mul_of_mem_exteriorPower {n : ℕ}
    {α : ExteriorAlgebra (MvPolynomial σ B) (Ω[MvPolynomial σ B⁄B])}
    (hα : α ∈ ⋀[MvPolynomial σ B]^n (Ω[MvPolynomial σ B⁄B]))
    (β : ExteriorAlgebra (MvPolynomial σ B) (Ω[MvPolynomial σ B⁄B])) :
    d B σ (α * β) = d B σ α * β + (-1 : MvPolynomial σ B) ^ n • (α * d B σ β) := by
  rw [d_mul, TauCeti.ExteriorAlgebra.involute_of_mem_exteriorPower hα, smul_mul_assoc]

/-- Action of `d` on a polynomial multiple `p • α` of a form. -/
theorem d_smul (p : MvPolynomial σ B)
    (α : ExteriorAlgebra (MvPolynomial σ B) (Ω[MvPolynomial σ B⁄B])) :
    d B σ (p • α) =
      ι (MvPolynomial σ B) (KaehlerDifferential.D B (MvPolynomial σ B) p) * α + p • d B σ α := by
  rw [Algebra.smul_def, d_mul, d_algebraMap, AlgHom.commutes, ← Algebra.smul_def]

/-- `d` anticommutes with the grade involution. -/
theorem d_involute (α : ExteriorAlgebra (MvPolynomial σ B) (Ω[MvPolynomial σ B⁄B])) :
    d B σ (CliffordAlgebra.involute (Q := (0 : QuadraticForm (MvPolynomial σ B) _)) α) =
      -CliffordAlgebra.involute (Q := (0 : QuadraticForm (MvPolynomial σ B) _)) (d B σ α) := by
  obtain ⟨u, rfl⟩ := (tensorEquiv B B σ).surjective α
  induction u using TensorProduct.inductionOn with
  | add u₁ u₂ hu₁ hu₂ =>
    simp only [map_add, hu₁, hu₂, neg_add]
  | tmul p ω =>
    rw [tensorEquiv_involute, d_tensorEquiv_self, d_tensorEquiv_self, map_mul,
      CliffordAlgebra.involute_ι, neg_mul, neg_neg, ← tensorEquiv_involute]

/-- Action of `d` on a pure tensor in any scalar-tower trivialization `tensorEquiv R B σ`. -/
theorem d_tensorEquiv_tmul {R : Type*} [CommRing R] [Algebra R B]
    (p : MvPolynomial σ B) (ω : ExteriorAlgebra R (σ →₀ R)) :
    d B σ (tensorEquiv R B σ (p ⊗ₜ[R] ω)) =
      ι (MvPolynomial σ B) (KaehlerDifferential.D B (MvPolynomial σ B) p) *
        tensorEquiv R B σ (1 ⊗ₜ[R] ω) := by
  have h1 : ∀ η : ExteriorAlgebra R (σ →₀ R), d B σ (tensorEquiv R B σ (1 ⊗ₜ[R] η)) = 0 := by
    intro η
    induction η using CliffordAlgebra.induction with
    | algebraMap r =>
      have hrm : (1 : MvPolynomial σ B) ⊗ₜ[R] algebraMap R (ExteriorAlgebra R (σ →₀ R)) r =
          algebraMap R (MvPolynomial σ B) r ⊗ₜ[R] 1 := by
        rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
          TensorProduct.smul_tmul']
      rw [hrm, tensorEquiv_tmul_one, d_algebraMap]
      have hC : algebraMap R (MvPolynomial σ B) r = C (algebraMap R B r) :=
        IsScalarTower.algebraMap_apply R B (MvPolynomial σ B) r
      rw [hC, MvPolynomial.derivation_C, map_zero]
    | ι m =>
      induction m using Finsupp.induction_linear with
      | zero => simp
      | add m₁ m₂ h₁ h₂ => simp only [map_add, TensorProduct.tmul_add, h₁, h₂, add_zero]
      | single i r =>
        have hsingle : Finsupp.single i r = r • Finsupp.single i (1 : R) := by
          rw [Finsupp.smul_single, smul_eq_mul, mul_one]
        rw [hsingle, map_smul, TensorProduct.tmul_smul,
          ← IsScalarTower.algebraMap_smul B r, ← IsScalarTower.algebraMap_smul (MvPolynomial σ B),
          map_smul, IsScalarTower.algebraMap_smul, map_smul, tensorEquiv_one_tmul_ι_single,
          d_ι_D_X, smul_zero]
    | mul a b ha hb =>
      have hmul : (1 : MvPolynomial σ B) ⊗ₜ[R] (a * b) =
          (1 ⊗ₜ[R] a) * (1 ⊗ₜ[R] b) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
      rw [hmul, map_mul, d_mul, ha, hb, zero_mul, mul_zero, add_zero]
    | add a b ha hb =>
      rw [TensorProduct.tmul_add, map_add, map_add, ha, hb, add_zero]
  have hp : p ⊗ₜ[R] ω = p • ((1 : MvPolynomial σ B) ⊗ₜ[R] ω) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [hp, map_smul, d_smul, h1, smul_zero, add_zero]

/-- `d` annihilates every exact one-form `ι (D p)`. -/
@[simp]
theorem d_ι_D (p : MvPolynomial σ B) :
    d B σ (ι (MvPolynomial σ B) (KaehlerDifferential.D B (MvPolynomial σ B) p)) = 0 := by
  induction p using MvPolynomial.induction_on with
  | C b => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    rw [Derivation.leibniz, map_add, map_smul, map_smul, map_add, d_smul, d_smul, d_ι_D_X, hp,
      smul_zero, smul_zero, add_zero, add_zero, ExteriorAlgebra.ι_add_mul_swap]

/-- **Nilpotency of the exterior derivative**: `d (d α) = 0` over every commutative ring `B`. -/
@[simp]
theorem d_d (α : ExteriorAlgebra (MvPolynomial σ B) (Ω[MvPolynomial σ B⁄B])) :
    d B σ (d B σ α) = 0 := by
  induction α using CliffordAlgebra.induction with
  | algebraMap p => rw [d_algebraMap, d_ι_D]
  | ι ω =>
    obtain ⟨v, rfl⟩ := (KaehlerDifferential.mvPolynomialEquiv B σ).symm.surjective ω
    induction v using Finsupp.induction_linear with
    | zero => simp
    | add v₁ v₂ h₁ h₂ => simp only [map_add, h₁, h₂, add_zero]
    | single i p =>
      have hsingle : (KaehlerDifferential.mvPolynomialEquiv B σ).symm (Finsupp.single i p) =
          p • KaehlerDifferential.D B (MvPolynomial σ B) (X i) :=
        KaehlerDifferential.mvPolynomialBasis_repr_symm_single B σ i p
      rw [hsingle, map_smul, d_smul, d_ι_D_X, smul_zero, add_zero, d_mul, d_ι_D, d_ι_D_X,
        zero_mul, mul_zero, add_zero]
  | mul α β hα hβ =>
    rw [d_mul, map_add, d_mul, d_mul, hα, hβ, d_involute, zero_mul, mul_zero, zero_add, add_zero,
      neg_mul, add_neg_cancel]
  | add α β hα hβ => rw [map_add, map_add, hα, hβ, add_zero]

/-- As a composition of `B`-linear endomorphisms, `d ∘ d = 0`. -/
theorem d_comp_d : (d B σ).comp (d B σ) = 0 := by
  ext α
  exact d_d α

/-- The exterior derivative raises exterior degree by one. -/
theorem d_mem_exteriorPower {n : ℕ}
    {α : ExteriorAlgebra (MvPolynomial σ B) (Ω[MvPolynomial σ B⁄B])}
    (hα : α ∈ ⋀[MvPolynomial σ B]^n (Ω[MvPolynomial σ B⁄B])) :
    d B σ α ∈ ⋀[MvPolynomial σ B]^(n + 1) (Ω[MvPolynomial σ B⁄B]) := by
  induction hα using Submodule.pow_induction_on_left' with
  | algebraMap p =>
    rw [d_algebraMap]
    exact TauCeti.ExteriorAlgebra.ι_mem_exteriorPower_one _
  | add x y i _ _ ihx ihy =>
    rw [map_add]
    exact add_mem ihx ihy
  | mem_mul m hm i x hx ih =>
    obtain ⟨ω, rfl⟩ := hm
    rw [d_mul, CliffordAlgebra.involute_ι, neg_mul]
    refine add_mem ?_ (neg_mem (TauCeti.ExteriorAlgebra.ι_mul_mem_exteriorPower ω ih))
    obtain ⟨v, rfl⟩ := (KaehlerDifferential.mvPolynomialEquiv B σ).symm.surjective ω
    have hdω : d B σ (ι (MvPolynomial σ B)
        ((KaehlerDifferential.mvPolynomialEquiv B σ).symm v)) ∈
        ⋀[MvPolynomial σ B]^2 (Ω[MvPolynomial σ B⁄B]) := by
      induction v using Finsupp.induction_linear with
      | zero => simp
      | add v₁ v₂ h₁ h₂ => simp only [map_add]; exact add_mem h₁ h₂
      | single j p =>
        have hsingle : (KaehlerDifferential.mvPolynomialEquiv B σ).symm (Finsupp.single j p) =
            p • KaehlerDifferential.D B (MvPolynomial σ B) (X j) :=
          KaehlerDifferential.mvPolynomialBasis_repr_symm_single B σ j p
        rw [hsingle, map_smul, d_smul, d_ι_D_X, smul_zero, add_zero]
        exact TauCeti.ExteriorAlgebra.ι_mul_mem_exteriorPower _
          (TauCeti.ExteriorAlgebra.ι_mem_exteriorPower_one _)
    have hmul := SetLike.mul_mem_graded hdω hx
    simpa [add_comm, add_left_comm, add_assoc] using hmul

/-- **Uniqueness of the exterior derivative**: any `B`-linear map satisfying the graded Leibniz
rule, agreeing with `ι ∘ D` on zero-forms, and annihilating each `dXᵢ` equals `d B σ`. -/
theorem d_unique
    (δ : ExteriorAlgebra (MvPolynomial σ B) (Ω[MvPolynomial σ B⁄B]) →ₗ[B]
      ExteriorAlgebra (MvPolynomial σ B) (Ω[MvPolynomial σ B⁄B]))
    (hmul : ∀ α β, δ (α * β) =
      δ α * β + CliffordAlgebra.involute (Q := (0 : QuadraticForm (MvPolynomial σ B) _)) α * δ β)
    (halg : ∀ p, δ (algebraMap (MvPolynomial σ B) _ p) =
      ι (MvPolynomial σ B) (KaehlerDifferential.D B (MvPolynomial σ B) p))
    (hX : ∀ i, δ (ι (MvPolynomial σ B) (KaehlerDifferential.D B (MvPolynomial σ B) (X i))) = 0) :
    δ = d B σ := by
  refine LinearMap.ext fun α ↦ ?_
  induction α using CliffordAlgebra.induction with
  | algebraMap p => rw [halg, d_algebraMap]
  | ι ω =>
    obtain ⟨v, rfl⟩ := (KaehlerDifferential.mvPolynomialEquiv B σ).symm.surjective ω
    induction v using Finsupp.induction_linear with
    | zero => simp
    | add v₁ v₂ h₁ h₂ => simp only [map_add, h₁, h₂]
    | single i p =>
      have hsingle : (KaehlerDifferential.mvPolynomialEquiv B σ).symm (Finsupp.single i p) =
          p • KaehlerDifferential.D B (MvPolynomial σ B) (X i) :=
        KaehlerDifferential.mvPolynomialBasis_repr_symm_single B σ i p
      rw [hsingle, map_smul, Algebra.smul_def, hmul, d_mul, halg, d_algebraMap, hX, d_ι_D_X]
  | mul α β hα hβ => rw [hmul, d_mul, hα, hβ]
  | add α β hα hβ => rw [map_add, map_add, hα, hβ]

end ExteriorDerivative

section LieDerivative

variable {R B σ : Type*} [CommRing R] [CommRing B] [Algebra R B]

/-- The coefficient-wise action of an `R`-derivation `D` on polynomial forms, fixing every `dXᵢ`. -/
private def coeffPart (D : Derivation R (MvPolynomial σ B) (MvPolynomial σ B)) :
    Module.End R (ExteriorAlgebra (MvPolynomial σ B) (Ω[MvPolynomial σ B⁄B])) :=
  ((tensorEquiv R B σ).toLinearEquiv.restrictScalars R).conj
    (D.toLinearMap.rTensor (ExteriorAlgebra R (σ →₀ R)))

private theorem coeffPart_tensorEquiv (D : Derivation R (MvPolynomial σ B) (MvPolynomial σ B))
    (p : MvPolynomial σ B) (ω : ExteriorAlgebra R (σ →₀ R)) :
    coeffPart D (tensorEquiv R B σ (p ⊗ₜ[R] ω)) = tensorEquiv R B σ (D p ⊗ₜ[R] ω) := by
  simp [coeffPart]

private theorem coeffPart_algebraMap (D : Derivation R (MvPolynomial σ B) (MvPolynomial σ B))
    (p : MvPolynomial σ B) :
    coeffPart D (algebraMap (MvPolynomial σ B) _ p) =
      algebraMap (MvPolynomial σ B) _ (D p) := by
  rw [← tensorEquiv_tmul_one (R := R), coeffPart_tensorEquiv, tensorEquiv_tmul_one]

private theorem coeffPart_ι_D_X (D : Derivation R (MvPolynomial σ B) (MvPolynomial σ B)) (i : σ) :
    coeffPart D (ι (MvPolynomial σ B) (KaehlerDifferential.D B (MvPolynomial σ B) (X i))) = 0 := by
  rw [← tensorEquiv_one_tmul_ι_single (R := R), coeffPart_tensorEquiv,
    Derivation.map_one_eq_zero, TensorProduct.zero_tmul, map_zero]

private theorem coeffPart_mul (D : Derivation R (MvPolynomial σ B) (MvPolynomial σ B))
    (α β : ExteriorAlgebra (MvPolynomial σ B) (Ω[MvPolynomial σ B⁄B])) :
    coeffPart D (α * β) = coeffPart D α * β + α * coeffPart D β := by
  obtain ⟨u, rfl⟩ := (tensorEquiv R B σ).surjective α
  obtain ⟨v, rfl⟩ := (tensorEquiv R B σ).surjective β
  induction u using TensorProduct.inductionOn with
  | add u₁ u₂ hu₁ hu₂ =>
    simp only [map_add, add_mul, hu₁, hu₂]
    abel
  | tmul p ω =>
    induction v using TensorProduct.inductionOn with
    | add v₁ v₂ hv₁ hv₂ =>
      simp only [map_add, mul_add, hv₁, hv₂]
      abel
    | tmul q η =>
      rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, coeffPart_tensorEquiv,
        coeffPart_tensorEquiv, coeffPart_tensorEquiv, Derivation.leibniz, smul_eq_mul, smul_eq_mul,
        TensorProduct.add_tmul, map_add, ← map_mul, ← map_mul,
        Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
        mul_comm q (D p), add_comm]

private theorem coeffPart_involute (D : Derivation R (MvPolynomial σ B) (MvPolynomial σ B))
    (α : ExteriorAlgebra (MvPolynomial σ B) (Ω[MvPolynomial σ B⁄B])) :
    coeffPart D (CliffordAlgebra.involute (Q := (0 : QuadraticForm (MvPolynomial σ B) _)) α) =
      CliffordAlgebra.involute (Q := (0 : QuadraticForm (MvPolynomial σ B) _)) (coeffPart D α) := by
  obtain ⟨u, rfl⟩ := (tensorEquiv R B σ).surjective α
  induction u using TensorProduct.inductionOn with
  | add u₁ u₂ hu₁ hu₂ => simp only [map_add, hu₁, hu₂]
  | tmul p ω =>
    rw [tensorEquiv_involute, coeffPart_tensorEquiv, coeffPart_tensorEquiv, tensorEquiv_involute]

private theorem coeffPart_mem_exteriorPower (D : Derivation R (MvPolynomial σ B) (MvPolynomial σ B))
    {n : ℕ} {α : ExteriorAlgebra (MvPolynomial σ B) (Ω[MvPolynomial σ B⁄B])}
    (hα : α ∈ ⋀[MvPolynomial σ B]^n (Ω[MvPolynomial σ B⁄B])) :
    coeffPart D α ∈ ⋀[MvPolynomial σ B]^n (Ω[MvPolynomial σ B⁄B]) := by
  induction hα using Submodule.pow_induction_on_left' with
  | algebraMap p =>
    rw [coeffPart_algebraMap]
    exact Submodule.algebraMap_mem _
  | add x y i _ _ ihx ihy =>
    rw [map_add]
    exact add_mem ihx ihy
  | mem_mul m hm i x hx ih =>
    obtain ⟨ω, rfl⟩ := hm
    rw [coeffPart_mul]
    refine add_mem ?_ (TauCeti.ExteriorAlgebra.ι_mul_mem_exteriorPower ω ih)
    obtain ⟨v, rfl⟩ := (KaehlerDifferential.mvPolynomialEquiv B σ).symm.surjective ω
    have h1 : coeffPart D (ι (MvPolynomial σ B)
        ((KaehlerDifferential.mvPolynomialEquiv B σ).symm v)) ∈
        ⋀[MvPolynomial σ B]^1 (Ω[MvPolynomial σ B⁄B]) := by
      induction v using Finsupp.induction_linear with
      | zero => simp
      | add v₁ v₂ h₁ h₂ => simp only [map_add]; exact add_mem h₁ h₂
      | single j p =>
        have hsingle : (KaehlerDifferential.mvPolynomialEquiv B σ).symm (Finsupp.single j p) =
            p • KaehlerDifferential.D B (MvPolynomial σ B) (X j) :=
          KaehlerDifferential.mvPolynomialBasis_repr_symm_single B σ j p
        rw [hsingle, map_smul, Algebra.smul_def, coeffPart_mul, coeffPart_algebraMap,
          coeffPart_ι_D_X, mul_zero, add_zero, ← Algebra.smul_def]
        exact Submodule.smul_mem _ _ (TauCeti.ExteriorAlgebra.ι_mem_exteriorPower_one _)
    have hmul := SetLike.mul_mem_graded h1 hx
    simpa [add_comm] using hmul

/-- The `P`-linear endomorphism of `Ω[P⁄B]` sending `dXᵢ` to `D B P (D (X i))`. -/
private def diffShift (D : Derivation R (MvPolynomial σ B) (MvPolynomial σ B)) :
    Ω[MvPolynomial σ B⁄B] →ₗ[MvPolynomial σ B] Ω[MvPolynomial σ B⁄B] :=
  (Finsupp.linearCombination (MvPolynomial σ B) fun i ↦
    KaehlerDifferential.D B (MvPolynomial σ B) (D (X i))).comp
    (KaehlerDifferential.mvPolynomialEquiv B σ).toLinearMap

private theorem diffShift_D_X (D : Derivation R (MvPolynomial σ B) (MvPolynomial σ B)) (i : σ) :
    diffShift D (KaehlerDifferential.D B (MvPolynomial σ B) (X i)) =
      KaehlerDifferential.D B (MvPolynomial σ B) (D (X i)) := by
  have h : KaehlerDifferential.mvPolynomialEquiv B σ
      (KaehlerDifferential.D B (MvPolynomial σ B) (X i)) = Finsupp.single i 1 :=
    KaehlerDifferential.mvPolynomialBasis_repr_D_X B σ i
  simp [diffShift, h]

/-- **The algebraic Lie derivative** on polynomial forms along an `R`-derivation `D`: the unique
degree-zero `R`-derivation acting as `D` on zero-forms and sending `dXᵢ` to `d(D Xᵢ)`. -/
def lieDeriv (D : Derivation R (MvPolynomial σ B) (MvPolynomial σ B)) :
    Module.End R (ExteriorAlgebra (MvPolynomial σ B) (Ω[MvPolynomial σ B⁄B])) :=
  coeffPart D + (ExteriorAlgebra.liftDeriv (diffShift D)).restrictScalars R

/-- On zero-forms, `lieDeriv D` acts by `D`. -/
@[simp]
theorem lieDeriv_algebraMap (D : Derivation R (MvPolynomial σ B) (MvPolynomial σ B))
    (p : MvPolynomial σ B) :
    lieDeriv D (algebraMap (MvPolynomial σ B) _ p) =
      algebraMap (MvPolynomial σ B) _ (D p) := by
  simp [lieDeriv, coeffPart_algebraMap]

/-- On coordinate one-forms `dXᵢ`, `lieDeriv D` sends `dXᵢ` to `d(D Xᵢ)`. -/
@[simp]
theorem lieDeriv_ι_D_X (D : Derivation R (MvPolynomial σ B) (MvPolynomial σ B)) (i : σ) :
    lieDeriv D (ι (MvPolynomial σ B) (KaehlerDifferential.D B (MvPolynomial σ B) (X i))) =
      ι (MvPolynomial σ B) (KaehlerDifferential.D B (MvPolynomial σ B) (D (X i))) := by
  simp [lieDeriv, coeffPart_ι_D_X, diffShift_D_X]

/-- `lieDeriv D` satisfies the degree-zero Leibniz rule on wedge products. -/
theorem lieDeriv_mul (D : Derivation R (MvPolynomial σ B) (MvPolynomial σ B))
    (α β : ExteriorAlgebra (MvPolynomial σ B) (Ω[MvPolynomial σ B⁄B])) :
    lieDeriv D (α * β) = lieDeriv D α * β + α * lieDeriv D β := by
  simp only [lieDeriv, LinearMap.add_apply, LinearMap.coe_restrictScalars, coeffPart_mul,
    ExteriorAlgebra.liftDeriv_mul, add_mul, mul_add]
  abel

/-- Action of `lieDeriv D` on a polynomial multiple `p • α` of a form. -/
theorem lieDeriv_smul (D : Derivation R (MvPolynomial σ B) (MvPolynomial σ B))
    (p : MvPolynomial σ B)
    (α : ExteriorAlgebra (MvPolynomial σ B) (Ω[MvPolynomial σ B⁄B])) :
    lieDeriv D (p • α) = D p • α + p • lieDeriv D α := by
  rw [Algebra.smul_def, lieDeriv_mul, lieDeriv_algebraMap, ← Algebra.smul_def, ← Algebra.smul_def]

/-- `lieDeriv D` vanishes on `1`. -/
@[simp]
theorem lieDeriv_one (D : Derivation R (MvPolynomial σ B) (MvPolynomial σ B)) :
    lieDeriv D 1 = 0 := by
  simpa using lieDeriv_algebraMap D 1

/-- `lieDeriv D` commutes with the grade involution. -/
theorem lieDeriv_involute (D : Derivation R (MvPolynomial σ B) (MvPolynomial σ B))
    (α : ExteriorAlgebra (MvPolynomial σ B) (Ω[MvPolynomial σ B⁄B])) :
    lieDeriv D (CliffordAlgebra.involute (Q := (0 : QuadraticForm (MvPolynomial σ B) _)) α) =
      CliffordAlgebra.involute (Q := (0 : QuadraticForm (MvPolynomial σ B) _)) (lieDeriv D α) := by
  simp only [lieDeriv, LinearMap.add_apply, LinearMap.coe_restrictScalars, coeffPart_involute,
    ExteriorAlgebra.liftDeriv_involute, map_add]

/-- `lieDeriv D` preserves each exterior power `⋀[MvPolynomial σ B]^n (Ω[MvPolynomial σ B⁄B])`. -/
theorem lieDeriv_mem_exteriorPower (D : Derivation R (MvPolynomial σ B) (MvPolynomial σ B))
    {n : ℕ} {α : ExteriorAlgebra (MvPolynomial σ B) (Ω[MvPolynomial σ B⁄B])}
    (hα : α ∈ ⋀[MvPolynomial σ B]^n (Ω[MvPolynomial σ B⁄B])) :
    lieDeriv D α ∈ ⋀[MvPolynomial σ B]^n (Ω[MvPolynomial σ B⁄B]) :=
  add_mem (coeffPart_mem_exteriorPower D hα)
    (ExteriorAlgebra.liftDeriv_mem_exteriorPower (diffShift D) hα)

/-- **Uniqueness of the Lie derivative**: any `R`-linear degree-zero derivation of polynomial
forms agreeing with `D` on zero-forms and with `d(D Xᵢ)` on `dXᵢ` equals `lieDeriv D`. -/
theorem lieDeriv_unique (D : Derivation R (MvPolynomial σ B) (MvPolynomial σ B))
    (L : Module.End R (ExteriorAlgebra (MvPolynomial σ B) (Ω[MvPolynomial σ B⁄B])))
    (hmul : ∀ α β, L (α * β) = L α * β + α * L β)
    (halg : ∀ p, L (algebraMap (MvPolynomial σ B) _ p) = algebraMap (MvPolynomial σ B) _ (D p))
    (hX : ∀ i, L (ι (MvPolynomial σ B) (KaehlerDifferential.D B (MvPolynomial σ B) (X i))) =
      ι (MvPolynomial σ B) (KaehlerDifferential.D B (MvPolynomial σ B) (D (X i)))) :
    L = lieDeriv D := by
  refine LinearMap.ext fun α ↦ ?_
  induction α using CliffordAlgebra.induction with
  | algebraMap p => rw [halg, lieDeriv_algebraMap]
  | ι ω =>
    obtain ⟨v, rfl⟩ := (KaehlerDifferential.mvPolynomialEquiv B σ).symm.surjective ω
    induction v using Finsupp.induction_linear with
    | zero => simp
    | add v₁ v₂ h₁ h₂ => simp only [map_add, h₁, h₂]
    | single i p =>
      have hsingle : (KaehlerDifferential.mvPolynomialEquiv B σ).symm (Finsupp.single i p) =
          p • KaehlerDifferential.D B (MvPolynomial σ B) (X i) :=
        KaehlerDifferential.mvPolynomialBasis_repr_symm_single B σ i p
      rw [hsingle, map_smul, Algebra.smul_def, hmul, lieDeriv_mul, halg, lieDeriv_algebraMap,
        hX, lieDeriv_ι_D_X]
  | mul α β hα hβ => rw [hmul, lieDeriv_mul, hα, hβ]
  | add α β hα hβ => rw [map_add, map_add, hα, hβ]

/-- Whenever `D` sends constants `C b` to elements with zero relative differential, `lieDeriv D`
commutes with `ι ∘ D` on all polynomials. -/
theorem lieDeriv_ι_D (D : Derivation R (MvPolynomial σ B) (MvPolynomial σ B))
    (hB : ∀ b : B, KaehlerDifferential.D B (MvPolynomial σ B) (D (C b)) = 0)
    (p : MvPolynomial σ B) :
    lieDeriv D (ι (MvPolynomial σ B) (KaehlerDifferential.D B (MvPolynomial σ B) p)) =
      ι (MvPolynomial σ B) (KaehlerDifferential.D B (MvPolynomial σ B) (D p)) := by
  induction p using MvPolynomial.induction_on with
  | C b => simp [hB b]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    rw [Derivation.leibniz, map_add, map_smul, map_smul, map_add, lieDeriv_smul, lieDeriv_smul,
      lieDeriv_ι_D_X, hp, Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add,
      Derivation.leibniz, Derivation.leibniz, map_add, map_add, map_add, map_smul, map_smul,
      map_smul, map_smul]
    abel

/-- **Naturality of the exterior derivative**: whenever `D` sends constants `C b` to elements with
zero relative differential, `d` commutes with `lieDeriv D` on all polynomial forms. -/
theorem d_lieDeriv (D : Derivation R (MvPolynomial σ B) (MvPolynomial σ B))
    (hB : ∀ b : B, KaehlerDifferential.D B (MvPolynomial σ B) (D (C b)) = 0)
    (α : ExteriorAlgebra (MvPolynomial σ B) (Ω[MvPolynomial σ B⁄B])) :
    d B σ (lieDeriv D α) = lieDeriv D (d B σ α) := by
  induction α using CliffordAlgebra.induction with
  | algebraMap p =>
    rw [lieDeriv_algebraMap, d_algebraMap, d_algebraMap, lieDeriv_ι_D D hB]
  | ι ω =>
    obtain ⟨v, rfl⟩ := (KaehlerDifferential.mvPolynomialEquiv B σ).symm.surjective ω
    induction v using Finsupp.induction_linear with
    | zero => simp
    | add v₁ v₂ h₁ h₂ => simp only [map_add, h₁, h₂]
    | single i p =>
      have hsingle : (KaehlerDifferential.mvPolynomialEquiv B σ).symm (Finsupp.single i p) =
          p • KaehlerDifferential.D B (MvPolynomial σ B) (X i) :=
        KaehlerDifferential.mvPolynomialBasis_repr_symm_single B σ i p
      rw [hsingle, map_smul, lieDeriv_smul, lieDeriv_ι_D_X, map_add, d_smul, d_smul, d_smul,
        d_ι_D_X, d_ι_D, smul_zero, smul_zero, add_zero, add_zero, add_zero,
        lieDeriv_mul, lieDeriv_ι_D D hB, lieDeriv_ι_D_X]
  | mul α β hα hβ =>
    rw [lieDeriv_mul, d_mul, map_add, map_add, d_mul, d_mul, lieDeriv_mul, lieDeriv_mul,
      lieDeriv_involute, hα, hβ]
    abel
  | add α β hα hβ => simp only [map_add, hα, hβ]

/-- Commuting derivations preserving constants lift to commuting Lie derivatives on all forms. -/
theorem lieDeriv_comm (D₁ D₂ : Derivation R (MvPolynomial σ B) (MvPolynomial σ B))
    (hB₁ : ∀ b : B, KaehlerDifferential.D B (MvPolynomial σ B) (D₁ (C b)) = 0)
    (hB₂ : ∀ b : B, KaehlerDifferential.D B (MvPolynomial σ B) (D₂ (C b)) = 0)
    (hcomm : ∀ p, D₁ (D₂ p) = D₂ (D₁ p))
    (α : ExteriorAlgebra (MvPolynomial σ B) (Ω[MvPolynomial σ B⁄B])) :
    lieDeriv D₁ (lieDeriv D₂ α) = lieDeriv D₂ (lieDeriv D₁ α) := by
  induction α using CliffordAlgebra.induction with
  | algebraMap p =>
    simp only [lieDeriv_algebraMap, hcomm]
  | ι ω =>
    obtain ⟨v, rfl⟩ := (KaehlerDifferential.mvPolynomialEquiv B σ).symm.surjective ω
    induction v using Finsupp.induction_linear with
    | zero => simp
    | add v₁ v₂ h₁ h₂ => simp only [map_add, h₁, h₂]
    | single i p =>
      have hsingle : (KaehlerDifferential.mvPolynomialEquiv B σ).symm (Finsupp.single i p) =
          p • KaehlerDifferential.D B (MvPolynomial σ B) (X i) :=
        KaehlerDifferential.mvPolynomialBasis_repr_symm_single B σ i p
      rw [hsingle, map_smul, lieDeriv_smul, lieDeriv_smul, map_add, map_add,
        lieDeriv_smul, lieDeriv_smul, lieDeriv_smul, lieDeriv_smul,
        lieDeriv_ι_D_X, lieDeriv_ι_D_X, lieDeriv_ι_D D₁ hB₁, lieDeriv_ι_D D₂ hB₂, hcomm, hcomm]
      abel
  | mul α β hα hβ =>
    simp only [lieDeriv_mul, map_add, hα, hβ]
    abel
  | add α β hα hβ => simp only [map_add, hα, hβ]

end LieDerivative

section SupportedForms

variable (B : Type*) [CommRing B] {σ : Type*}

/-- The `B`-subalgebra of polynomial differential forms supported on a set `s` of variables,
generated by polynomials in `MvPolynomial.supported B s` and coordinate one-forms `dXᵢ` with
`i ∈ s`. -/
def supportedForms (s : Set σ) :
    Subalgebra B (ExteriorAlgebra (MvPolynomial σ B) (Ω[MvPolynomial σ B⁄B])) :=
  Algebra.adjoin B
    ((algebraMap (MvPolynomial σ B) _ '' (MvPolynomial.supported B s : Set (MvPolynomial σ B))) ∪
      ((fun i ↦ ι (MvPolynomial σ B) (KaehlerDifferential.D B (MvPolynomial σ B) (X i))) '' s))

variable {B}

/-- `supportedForms B s` is the `B`-subalgebra generated by zero-forms supported on `s` and
coordinate one-forms `dXᵢ` for `i ∈ s`. -/
theorem supportedForms_eq_adjoin (s : Set σ) :
    supportedForms B s = Algebra.adjoin B
      ((algebraMap (MvPolynomial σ B) _ ''
          (MvPolynomial.supported B s : Set (MvPolynomial σ B))) ∪
        ((fun i ↦
          ι (MvPolynomial σ B) (KaehlerDifferential.D B (MvPolynomial σ B) (X i))) '' s)) := by
  rfl

/-- Enlarging the set of allowed variables enlarges the subalgebra of supported forms. -/
theorem supportedForms_mono : Monotone (supportedForms B (σ := σ)) := by
  intro s t hst
  refine Algebra.adjoin_mono (Set.union_subset_union ?_ (Set.image_mono hst))
  exact Set.image_mono (MvPolynomial.supported_mono hst)

/-- A zero-form whose polynomial is supported on `s` belongs to `supportedForms B s`. -/
theorem algebraMap_mem_supportedForms {s : Set σ} {p : MvPolynomial σ B}
    (hp : p ∈ MvPolynomial.supported B s) :
    algebraMap (MvPolynomial σ B)
        (ExteriorAlgebra (MvPolynomial σ B) (Ω[MvPolynomial σ B⁄B])) p ∈
      supportedForms B s :=
  Algebra.subset_adjoin (Or.inl ⟨p, hp, rfl⟩)

/-- A coordinate one-form `dXᵢ` with `i ∈ s` belongs to `supportedForms B s`. -/
theorem ι_D_X_mem_supportedForms {s : Set σ} {i : σ} (hi : i ∈ s) :
    ι (MvPolynomial σ B) (KaehlerDifferential.D B (MvPolynomial σ B) (X i)) ∈
      supportedForms B s :=
  Algebra.subset_adjoin (Or.inr ⟨i, hi, rfl⟩)

/-- A polynomial multiple of a form in `supportedForms B s` stays in `supportedForms B s` when
the polynomial is supported on `s`. -/
theorem smul_mem_supportedForms {s : Set σ} {p : MvPolynomial σ B}
    (hp : p ∈ MvPolynomial.supported B s)
    {α : ExteriorAlgebra (MvPolynomial σ B) (Ω[MvPolynomial σ B⁄B])}
    (hα : α ∈ supportedForms B s) : p • α ∈ supportedForms B s := by
  rw [Algebra.smul_def]
  exact mul_mem (algebraMap_mem_supportedForms hp) hα

/-- The differential of a polynomial supported on `s` belongs to `supportedForms B s`. -/
theorem ι_D_mem_supportedForms {s : Set σ} {p : MvPolynomial σ B}
    (hp : p ∈ MvPolynomial.supported B s) :
    ι (MvPolynomial σ B) (KaehlerDifferential.D B (MvPolynomial σ B) p) ∈
      supportedForms B s := by
  induction hp using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    exact ι_D_X_mem_supportedForms hi
  | algebraMap b => simp
  | add x y _ _ hx hy =>
    rw [map_add, map_add]
    exact add_mem hx hy
  | mul x y hx hy ihx ihy =>
    rw [Derivation.leibniz, map_add, map_smul, map_smul]
    exact add_mem (smul_mem_supportedForms hx ihy) (smul_mem_supportedForms hy ihx)

/-- The grade involution preserves `supportedForms B s`. -/
theorem involute_mem_supportedForms {s : Set σ}
    {α : ExteriorAlgebra (MvPolynomial σ B) (Ω[MvPolynomial σ B⁄B])}
    (hα : α ∈ supportedForms B s) :
    CliffordAlgebra.involute (Q := (0 : QuadraticForm (MvPolynomial σ B) _)) α ∈
      supportedForms B s := by
  induction hα using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with ⟨p, hp, rfl⟩ | ⟨i, hi, rfl⟩
    · rw [AlgHom.commutes]
      exact algebraMap_mem_supportedForms hp
    · rw [CliffordAlgebra.involute_ι]
      exact neg_mem (ι_D_X_mem_supportedForms hi)
  | algebraMap b =>
    have hb : algebraMap B (ExteriorAlgebra (MvPolynomial σ B) (Ω[MvPolynomial σ B⁄B])) b =
        algebraMap (MvPolynomial σ B) _ (C b) :=
      IsScalarTower.algebraMap_apply B (MvPolynomial σ B) _ b
    rw [hb, AlgHom.commutes]
    exact algebraMap_mem_supportedForms (Subalgebra.algebraMap_mem _ b)
  | add x y _ _ hx hy =>
    rw [map_add]
    exact add_mem hx hy
  | mul x y _ _ hx hy =>
    rw [map_mul]
    exact mul_mem hx hy

/-- The exterior derivative preserves every supported-form subalgebra. -/
theorem d_mem_supportedForms {s : Set σ}
    {α : ExteriorAlgebra (MvPolynomial σ B) (Ω[MvPolynomial σ B⁄B])}
    (hα : α ∈ supportedForms B s) : d B σ α ∈ supportedForms B s := by
  induction hα using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with ⟨p, hp, rfl⟩ | ⟨i, _, rfl⟩
    · rw [d_algebraMap]
      exact ι_D_mem_supportedForms hp
    · rw [d_ι_D_X]
      exact zero_mem _
  | algebraMap b =>
    have hb : algebraMap B (ExteriorAlgebra (MvPolynomial σ B) (Ω[MvPolynomial σ B⁄B])) b =
        algebraMap (MvPolynomial σ B) _ (C b) :=
      IsScalarTower.algebraMap_apply B (MvPolynomial σ B) _ b
    rw [hb, d_algebraMap, MvPolynomial.derivation_C, map_zero]
    exact zero_mem _
  | add x y _ _ hx hy =>
    rw [map_add]
    exact add_mem hx hy
  | mul x y hx hy ihx ihy =>
    rw [d_mul]
    exact add_mem (mul_mem ihx hy) (mul_mem (involute_mem_supportedForms hx) ihy)

/-- If an `R`-derivation `D` maps polynomials supported on `s` into polynomials supported on
`t ⊇ s`, then `lieDeriv D` maps `supportedForms B s` into `supportedForms B t`. -/
theorem lieDeriv_mem_supportedForms {R : Type*} [CommRing R] [Algebra R B]
    {D : Derivation R (MvPolynomial σ B) (MvPolynomial σ B)} {s t : Set σ} (hst : s ⊆ t)
    (hD : ∀ p ∈ MvPolynomial.supported B s, D p ∈ MvPolynomial.supported B t)
    {α : ExteriorAlgebra (MvPolynomial σ B) (Ω[MvPolynomial σ B⁄B])}
    (hα : α ∈ supportedForms B s) : lieDeriv D α ∈ supportedForms B t := by
  induction hα using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with ⟨p, hp, rfl⟩ | ⟨i, hi, rfl⟩
    · rw [lieDeriv_algebraMap]
      exact algebraMap_mem_supportedForms (hD p hp)
    · rw [lieDeriv_ι_D_X]
      exact ι_D_mem_supportedForms (hD (X i) (Algebra.subset_adjoin ⟨i, hi, rfl⟩))
  | algebraMap b =>
    have hb : algebraMap B (ExteriorAlgebra (MvPolynomial σ B) (Ω[MvPolynomial σ B⁄B])) b =
        algebraMap (MvPolynomial σ B) _ (C b) :=
      IsScalarTower.algebraMap_apply B (MvPolynomial σ B) _ b
    rw [hb, lieDeriv_algebraMap]
    exact algebraMap_mem_supportedForms (hD (C b) (Subalgebra.algebraMap_mem _ b))
  | add x y _ _ hx hy =>
    rw [map_add]
    exact add_mem hx hy
  | mul x y hx hy ihx ihy =>
    rw [lieDeriv_mul]
    exact add_mem (mul_mem ihx (supportedForms_mono hst hy))
      (mul_mem (supportedForms_mono hst hx) ihy)

/-- Every polynomial differential form uses only finitely many variables. -/
theorem exists_mem_supportedForms_finset
    (α : ExteriorAlgebra (MvPolynomial σ B) (Ω[MvPolynomial σ B⁄B])) :
    ∃ s : Finset σ, α ∈ supportedForms B (s : Set σ) := by
  classical
  induction α using CliffordAlgebra.induction with
  | algebraMap p =>
    exact ⟨p.vars, algebraMap_mem_supportedForms p.mem_supported_vars⟩
  | ι ω =>
    obtain ⟨v, rfl⟩ := (KaehlerDifferential.mvPolynomialEquiv B σ).symm.surjective ω
    induction v using Finsupp.induction_linear with
    | zero => exact ⟨∅, by simp⟩
    | add v₁ v₂ h₁ h₂ =>
      obtain ⟨s₁, hs₁⟩ := h₁
      obtain ⟨s₂, hs₂⟩ := h₂
      refine ⟨s₁ ∪ s₂, ?_⟩
      rw [map_add, map_add]
      exact add_mem
        (supportedForms_mono (Finset.coe_subset.mpr Finset.subset_union_left) hs₁)
        (supportedForms_mono (Finset.coe_subset.mpr Finset.subset_union_right) hs₂)
    | single i p =>
      have hsingle : (KaehlerDifferential.mvPolynomialEquiv B σ).symm (Finsupp.single i p) =
          p • KaehlerDifferential.D B (MvPolynomial σ B) (X i) :=
        KaehlerDifferential.mvPolynomialBasis_repr_symm_single B σ i p
      refine ⟨insert i p.vars, ?_⟩
      rw [hsingle, map_smul]
      exact smul_mem_supportedForms
        (MvPolynomial.supported_mono (Finset.coe_subset.mpr (Finset.subset_insert i p.vars))
          p.mem_supported_vars)
        (ι_D_X_mem_supportedForms (by simp))
  | mul α β hα hβ =>
    obtain ⟨s₁, hs₁⟩ := hα
    obtain ⟨s₂, hs₂⟩ := hβ
    exact ⟨s₁ ∪ s₂, mul_mem
      (supportedForms_mono (Finset.coe_subset.mpr Finset.subset_union_left) hs₁)
      (supportedForms_mono (Finset.coe_subset.mpr Finset.subset_union_right) hs₂)⟩
  | add α β hα hβ =>
    obtain ⟨s₁, hs₁⟩ := hα
    obtain ⟨s₂, hs₂⟩ := hβ
    exact ⟨s₁ ∪ s₂, add_mem
      (supportedForms_mono (Finset.coe_subset.mpr Finset.subset_union_left) hs₁)
      (supportedForms_mono (Finset.coe_subset.mpr Finset.subset_union_right) hs₂)⟩

end SupportedForms

end

end TauCeti.MvPolynomialDeRham
