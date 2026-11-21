/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.Kaehler.Polynomial
public import TauCeti.RingTheory.Kaehler.DeRham.Basic
public import TauCeti.RingTheory.Kaehler.DeRham.LieDerivative
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.LinearAlgebra.ExteriorAlgebra.BaseChange
import TauCeti.LinearAlgebra.ExteriorPower.Basic
import TauCeti.RingTheory.Kaehler.MvPolynomial

/-!
# Algebraic de Rham coordinate formulas, trivialization, and support over multivariate polynomials

Over a multivariate polynomial ring `MvPolynomial σ R` (for an arbitrary, possibly infinite
variable set `σ`), the universal Kähler differential `D R (MvPolynomial σ R) p` expands in terms
of formal partial derivatives (`KaehlerDifferential.mvPolynomial_D_apply_eq_sum_vars`). This file
transfers those coordinate formulas to the algebraic exterior derivative
`TauCeti.KaehlerDeRham.extDeriv` on `ExteriorAlgebra (MvPolynomial σ R) Ω[MvPolynomial σ R⁄R]`.

In addition, for any commutative algebra tower `R → B → MvPolynomial σ B`, base change of the
exterior algebra identifies `ExteriorAlgebra (MvPolynomial σ B) (Ω[MvPolynomial σ B⁄B])` with
`MvPolynomial σ B ⊗[R] ExteriorAlgebra R (σ →₀ R)` (`TauCeti.KaehlerDeRham.tensorEquiv`), and
`TauCeti.KaehlerDeRham.supportedForms B s` defines the `B`-subalgebra of forms supported on a set
`s : Set σ` of variables, preserved by `extDeriv`, grade involution, and
`Derivation.deRhamLieDeriv`.

## Main definitions

* `TauCeti.KaehlerDeRham.tensorEquiv`: algebra isomorphism
  `MvPolynomial σ B ⊗[R] ExteriorAlgebra R (σ →₀ R) ≃ₐ[MvPolynomial σ B]
    ExteriorAlgebra (MvPolynomial σ B) (Ω[MvPolynomial σ B⁄B])`.
* `TauCeti.KaehlerDeRham.supportedForms`: the subalgebra of polynomial forms supported on a set of
  variables.

## Main results

* `TauCeti.KaehlerDeRham.extDeriv_algebraMap_mvPolynomial_eq_sum_vars`:
  `d p = ∑ i ∈ p.vars, MvPolynomial.pderiv i p • ι (D (X i))` for arbitrary `σ`.
* `TauCeti.KaehlerDeRham.extDeriv_algebraMap_mvPolynomial`:
  `d p = ∑ i : σ, MvPolynomial.pderiv i p • ι (D (X i))` when `[Fintype σ]`.
* `TauCeti.KaehlerDeRham.extDeriv_smul_eq_sum_vars_of_extDeriv_eq_zero`:
  for any closed form `x` (`extDeriv R (MvPolynomial σ R) x = 0`),
  `d (p • x) = ∑ j ∈ p.vars, MvPolynomial.pderiv j p • (ι (D (X j)) * x)`.
* `TauCeti.KaehlerDeRham.extDeriv_tensorEquiv_tmul`: action of `extDeriv` on a pure tensor.
* `TauCeti.KaehlerDeRham.extDeriv_mem_supportedForms`,
  `TauCeti.KaehlerDeRham.deRhamLieDeriv_mem_supportedForms`, and
  `TauCeti.KaehlerDeRham.exists_mem_supportedForms_finset`: variable-support preservation and
  finiteness.
-/

public section

namespace TauCeti.KaehlerDeRham

section CoordinateFormulas

variable {R σ : Type*} [CommRing R]

/-- Over a multivariate polynomial ring `MvPolynomial σ R` (with `σ` possibly infinite), the
algebraic exterior derivative of a polynomial `p` is the finite sum over `p.vars` of its formal
partial derivatives wedged with the coordinate differentials `D (X i)`. -/
theorem extDeriv_algebraMap_mvPolynomial_eq_sum_vars (p : MvPolynomial σ R) :
    extDeriv R (MvPolynomial σ R)
        (algebraMap (MvPolynomial σ R) (ExteriorAlgebra (MvPolynomial σ R) Ω[MvPolynomial σ R⁄R])
          p) =
      ∑ i ∈ p.vars,
        MvPolynomial.pderiv i p •
          ExteriorAlgebra.ι (MvPolynomial σ R)
            (KaehlerDifferential.D R (MvPolynomial σ R) (MvPolynomial.X i)) := by
  rw [extDeriv_algebraMap, KaehlerDifferential.mvPolynomial_D_apply_eq_sum_vars, map_sum]
  simp only [LinearMap.map_smul]

/-- Over a multivariate polynomial ring on a finite variable set `σ`, the exterior derivative of `p`
is `∑ i : σ, MvPolynomial.pderiv i p • ι (D (X i))`. -/
theorem extDeriv_algebraMap_mvPolynomial [Fintype σ] (p : MvPolynomial σ R) :
    extDeriv R (MvPolynomial σ R)
        (algebraMap (MvPolynomial σ R) (ExteriorAlgebra (MvPolynomial σ R) Ω[MvPolynomial σ R⁄R])
          p) =
      ∑ i : σ,
        MvPolynomial.pderiv i p •
          ExteriorAlgebra.ι (MvPolynomial σ R)
            (KaehlerDifferential.D R (MvPolynomial σ R) (MvPolynomial.X i)) := by
  rw [extDeriv_algebraMap, KaehlerDifferential.mvPolynomial_D_apply, map_sum]
  simp only [LinearMap.map_smul]

/-- Coordinate formula for `extDeriv` on `p • x` for any closed form `x`
(`extDeriv R (MvPolynomial σ R) x = 0`) over `MvPolynomial σ R`, valid without finiteness
hypotheses on `σ`. -/
theorem extDeriv_smul_eq_sum_vars_of_extDeriv_eq_zero (p : MvPolynomial σ R)
    {x : ExteriorAlgebra (MvPolynomial σ R) Ω[MvPolynomial σ R⁄R]}
    (hx : extDeriv R (MvPolynomial σ R) x = 0) :
    extDeriv R (MvPolynomial σ R) (p • x) =
      ∑ j ∈ p.vars,
        MvPolynomial.pderiv j p •
          (ExteriorAlgebra.ι (MvPolynomial σ R)
              (KaehlerDifferential.D R (MvPolynomial σ R) (MvPolynomial.X j)) * x) := by
  rw [extDeriv_smul, hx, smul_zero, add_zero, ← extDeriv_algebraMap,
    extDeriv_algebraMap_mvPolynomial_eq_sum_vars, Finset.sum_mul]
  simp only [smul_mul_assoc]

end CoordinateFormulas

section TensorEquiv

open _root_.ExteriorAlgebra _root_.KaehlerDifferential MvPolynomial TensorProduct

noncomputable section

variable (R B σ : Type*) [CommRing R] [CommRing B] [Algebra R B]

/-- The `MvPolynomial σ B`-linear equivalence `P ⊗[R] (σ →₀ R) ≃ₗ[P] Ω[P⁄B]`. -/
private def mvModuleEquiv :
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
    (exteriorMapEquiv (mvModuleEquiv R B σ))

variable {R B σ}

private theorem mvModuleEquiv_tmul_single (p : MvPolynomial σ B) (i : σ) :
    mvModuleEquiv R B σ (p ⊗ₜ[R] Finsupp.single i (1 : R)) =
      p • KaehlerDifferential.D B (MvPolynomial σ B) (X i) := by
  classical
  have hsingle : TensorProduct.finsuppScalarRight R (MvPolynomial σ B) (MvPolynomial σ B) σ
      (p ⊗ₜ[R] Finsupp.single i (1 : R)) = Finsupp.single i p := by
    rw [← TensorProduct.finsuppScalarRight_symm_apply_single (R := R) (S := MvPolynomial σ B)
      (M := MvPolynomial σ B) (ι := σ) i p, LinearEquiv.apply_symm_apply]
  rw [mvModuleEquiv, LinearEquiv.trans_apply, hsingle]
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
    LinearEquiv.coe_coe, mvModuleEquiv_tmul_single, one_smul]

/-- Under `tensorEquiv`, `p ⊗ₜ ι (single i 1)` corresponds to `p • dXᵢ`. -/
@[simp]
theorem tensorEquiv_tmul_ι_single (p : MvPolynomial σ B) (i : σ) :
    tensorEquiv R B σ (p ⊗ₜ[R] ι R (Finsupp.single i (1 : R))) =
      p • ι (MvPolynomial σ B) (KaehlerDifferential.D B (MvPolynomial σ B) (X i)) := by
  have hp : p ⊗ₜ[R] ι R (Finsupp.single i (1 : R)) =
      p • ((1 : MvPolynomial σ B) ⊗ₜ[R] ι R (Finsupp.single i (1 : R))) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [hp, _root_.map_smul, tensorEquiv_one_tmul_ι_single]

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
  rw [hp, hp', _root_.map_smul, _root_.map_smul, _root_.map_smul, h1]

/-- `tensorEquiv` sends pure tensors of degree `n` into the `n`-th exterior power of
`Ω[MvPolynomial σ B⁄B]`. -/
theorem tensorEquiv_tmul_mem_exteriorPower {n : ℕ} (p : MvPolynomial σ B)
    {ω : ExteriorAlgebra R (σ →₀ R)} (hω : ω ∈ ⋀[R]^n (σ →₀ R)) :
    tensorEquiv R B σ (p ⊗ₜ[R] ω) ∈
      ⋀[MvPolynomial σ B]^n (Ω[MvPolynomial σ B⁄B]) := by
  have hp : p ⊗ₜ[R] ω = p • ((1 : MvPolynomial σ B) ⊗ₜ[R] ω) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [hp, _root_.map_smul]
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
        ι (MvPolynomial σ B) (mvModuleEquiv R B σ (1 ⊗ₜ[R] v)) := by
      simp [tensorEquiv, exteriorMapEquiv, ExteriorAlgebra.baseChangeEquiv_apply]
    rw [hι]
    exact TauCeti.ExteriorAlgebra.ι_mul_mem_exteriorPower _ ih

/-- Action of `extDeriv` on a pure tensor in any scalar-tower trivialization
`tensorEquiv R B σ`. -/
theorem extDeriv_tensorEquiv_tmul
    (p : MvPolynomial σ B) (ω : ExteriorAlgebra R (σ →₀ R)) :
    extDeriv B (MvPolynomial σ B) (tensorEquiv R B σ (p ⊗ₜ[R] ω)) =
      ι (MvPolynomial σ B) (KaehlerDifferential.D B (MvPolynomial σ B) p) *
        tensorEquiv R B σ (1 ⊗ₜ[R] ω) := by
  have h1 : ∀ η : ExteriorAlgebra R (σ →₀ R),
      extDeriv B (MvPolynomial σ B) (tensorEquiv R B σ (1 ⊗ₜ[R] η)) = 0 := by
    intro η
    induction η using CliffordAlgebra.induction with
    | algebraMap r =>
      have hrm : (1 : MvPolynomial σ B) ⊗ₜ[R] algebraMap R (ExteriorAlgebra R (σ →₀ R)) r =
          algebraMap R (MvPolynomial σ B) r ⊗ₜ[R] 1 := by
        rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
          TensorProduct.smul_tmul']
      rw [hrm, tensorEquiv_tmul_one, extDeriv_algebraMap]
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
        rw [hsingle, _root_.map_smul, TensorProduct.tmul_smul,
          ← IsScalarTower.algebraMap_smul B r, ← IsScalarTower.algebraMap_smul (MvPolynomial σ B),
          _root_.map_smul, IsScalarTower.algebraMap_smul, _root_.map_smul,
          tensorEquiv_one_tmul_ι_single, extDeriv_ι_D, smul_zero]
    | mul a b ha hb =>
      have hmul : (1 : MvPolynomial σ B) ⊗ₜ[R] (a * b) =
          (1 ⊗ₜ[R] a) * (1 ⊗ₜ[R] b) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
      rw [hmul, map_mul, extDeriv_mul, ha, hb, zero_mul, mul_zero, add_zero]
    | add a b ha hb =>
      rw [TensorProduct.tmul_add, map_add, map_add, ha, hb, add_zero]
  have hp : p ⊗ₜ[R] ω = p • ((1 : MvPolynomial σ B) ⊗ₜ[R] ω) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [hp, _root_.map_smul, extDeriv_smul, h1, smul_zero, add_zero]

end

end TensorEquiv

section SupportedForms

open _root_.ExteriorAlgebra _root_.KaehlerDifferential MvPolynomial

noncomputable section

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
    rw [Derivation.leibniz, map_add, _root_.map_smul, _root_.map_smul]
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

/-- The algebraic exterior derivative preserves every supported-form subalgebra. -/
theorem extDeriv_mem_supportedForms {s : Set σ}
    {α : ExteriorAlgebra (MvPolynomial σ B) (Ω[MvPolynomial σ B⁄B])}
    (hα : α ∈ supportedForms B s) :
    extDeriv B (MvPolynomial σ B) α ∈ supportedForms B s := by
  induction hα using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with ⟨p, hp, rfl⟩ | ⟨i, _, rfl⟩
    · rw [extDeriv_algebraMap]
      exact ι_D_mem_supportedForms hp
    · rw [extDeriv_ι_D]
      exact zero_mem _
  | algebraMap b =>
    rw [extDeriv_algebraMap_base]
    exact zero_mem _
  | add x y _ _ hx hy =>
    rw [map_add]
    exact add_mem hx hy
  | mul x y hx hy ihx ihy =>
    rw [extDeriv_mul]
    exact add_mem (mul_mem ihx hy) (mul_mem (involute_mem_supportedForms hx) ihy)

/-- If an `R`-derivation `D` preserving `B`-constants maps polynomials supported on `s` into
polynomials supported on `t ⊇ s`, then `D.deRhamLieDeriv hB` maps `supportedForms B s` into
`supportedForms B t`. -/
theorem deRhamLieDeriv_mem_supportedForms {R : Type*} [CommRing R] [Algebra R B]
    {D : Derivation R (MvPolynomial σ B) (MvPolynomial σ B)}
    (hB : ∀ b : B, KaehlerDifferential.D B (MvPolynomial σ B) (D (algebraMap B _ b)) = 0)
    {s t : Set σ} (hst : s ⊆ t)
    (hD : ∀ p ∈ MvPolynomial.supported B s, D p ∈ MvPolynomial.supported B t)
    {α : ExteriorAlgebra (MvPolynomial σ B) (Ω[MvPolynomial σ B⁄B])}
    (hα : α ∈ supportedForms B s) : D.deRhamLieDeriv hB α ∈ supportedForms B t := by
  induction hα using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with ⟨p, hp, rfl⟩ | ⟨i, hi, rfl⟩
    · rw [Derivation.deRhamLieDeriv_algebraMap]
      exact algebraMap_mem_supportedForms (hD p hp)
    · rw [Derivation.deRhamLieDeriv_ι, Derivation.kaehlerLieDeriv_D]
      exact ι_D_mem_supportedForms (hD (X i) (Algebra.subset_adjoin ⟨i, hi, rfl⟩))
  | algebraMap b =>
    have hb : algebraMap B (ExteriorAlgebra (MvPolynomial σ B) (Ω[MvPolynomial σ B⁄B])) b =
        algebraMap (MvPolynomial σ B) _ (C b) :=
      IsScalarTower.algebraMap_apply B (MvPolynomial σ B) _ b
    rw [hb, Derivation.deRhamLieDeriv_algebraMap]
    exact algebraMap_mem_supportedForms (hD (C b) (Subalgebra.algebraMap_mem _ b))
  | add x y _ _ hx hy =>
    rw [map_add]
    exact add_mem hx hy
  | mul x y hx hy ihx ihy =>
    rw [Derivation.deRhamLieDeriv_mul]
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
      rw [hsingle, _root_.map_smul]
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

end

end SupportedForms

end TauCeti.KaehlerDeRham
