/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import Mathlib.Algebra.MvPolynomial.Expand
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.CharP.Algebra
import Mathlib.RingTheory.Flat.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.Dual
public import TauCeti.Algebra.Coalgebra.Comodule.SymmetricAlgebra.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.Transport
public import TauCeti.LinearAlgebra.SymmetricAlgebra.BasisComparison
public import TauCeti.RingTheory.TensorProduct.Maps

/-!
# Polynomial functions on a comodule

Let `V` be a right comodule over a commutative Hopf algebra `H`, with a finite basis `b`
indexed by `ι`. The polynomial functions on `V` are the symmetric algebra of the dual comodule
`V*`. Writing them in the coordinates `X i = b*ᵢ` identifies them with `MvPolynomial ι R`, and this
file transports the comodule structure along that identification.

Concretely, the coaction is the algebra homomorphism sending the coordinate `X i` to
`∑ j, X j ⊗ S(c(b*ᵢ, b j))`, where `c(b*ᵢ, b j)` is a matrix coefficient of `V` and `S` is the
antipode. On algebra-valued points this is the contragredient action `(g • f)(v) = f(g⁻¹ v)`: a
point `g` substitutes `∑ j, g(S(c(b*ᵢ, b j))) X j` for `X i`. Every homogeneous component is a
subcomodule. In prime characteristic, the polynomials in the pth powers of the variables
also form a subcomodule, without a perfectness hypothesis on the coefficient ring.

For the standard representation of `SL₂` these are the binary forms, the basic rational
representations of `SL₂`.

## Main declarations

* `TauCeti.Comodule.polynomial`: the comodule of polynomial functions on `V`, in the coordinates
  of the basis `b`.
* `TauCeti.Comodule.polynomial_coact_X`: the coaction of a coordinate function.
* `TauCeti.Comodule.polynomialCoact`: the coaction as an algebra homomorphism.
* `TauCeti.Comodule.polynomialCoact_expand_mem`: the coaction preserves polynomials in
  pth powers of variables.
* `TauCeti.Comodule.polynomialExpandSubcomodule`: polynomials in pth powers of variables, as a
  subcomodule over any coefficient semiring of characteristic `p`.
* `TauCeti.Comodule.polynomialHomogeneousSubcomodule`: the homogeneous polynomial functions of a
  fixed degree, as a subcomodule.
* `TauCeti.Comodule.algebraTensorAlgEquiv_endOfPoint_polynomial`: a point acts on polynomial
  functions by the contragredient linear substitution.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, 2nd ed., I.2.
* J. S. Milne, *Algebraic Groups* (2017), §4.a.
-/

public section

open Module
open scoped TensorProduct

namespace TauCeti

namespace Comodule

variable {R H V ι : Type*} [CommSemiring R] [CommSemiring H] [HopfAlgebra R H]
  [AddCommMonoid V] [Module R V] [Comodule R H V] [Fintype ι]

section Coact

variable (H) in
/-- The coaction on polynomial functions on `V`, as an algebra homomorphism: it sends the
coordinate `X i` to `∑ j, X j ⊗ S(c(b*ᵢ, b j))`. By `polynomial_coact` it is the coaction of
`polynomial H b`. -/
noncomputable def polynomialCoact (b : Basis ι R V) :
    MvPolynomial ι R →ₐ[R] MvPolynomial ι R ⊗[R] H :=
  MvPolynomial.aeval fun i ↦ ∑ j, MvPolynomial.X j ⊗ₜ[R]
    HopfAlgebra.antipode R (matrixCoefficient (C := H) (b.coord i) (b j))

@[simp]
theorem polynomialCoact_X (b : Basis ι R V) (i : ι) :
    polynomialCoact H b (MvPolynomial.X i) = ∑ j, MvPolynomial.X j ⊗ₜ[R]
      HopfAlgebra.antipode R (matrixCoefficient (C := H) (b.coord i) (b j)) :=
  MvPolynomial.aeval_X _ _

end Coact

section Frobenius

variable (H) (b : Basis ι R V) (p : ℕ) [Fact p.Prime] [CharP R p]

/-- The range of substitution `X i ↦ X i ^ p` is stable under the polynomial coaction.
The coefficients are left unchanged, so this does not require a perfect base ring. -/
theorem polynomialCoact_expand_mem (f : MvPolynomial ι R) :
    polynomialCoact H b (MvPolynomial.expand p f) ∈
      LinearMap.range (TensorProduct.map
        (MvPolynomial.expand (σ := ι) (R := R) p).range.toSubmodule.subtype
        (LinearMap.id : H →ₗ[R] H)) := by
  classical
  let : CharP (MvPolynomial ι R ⊗[R] H) p := charP_of_injective_ringHom
    (Algebra.TensorProduct.includeLeft_injective (S := R)
      (Bialgebra.algebraMap_injective (R := R) H)) p
  let N := (MvPolynomial.expand (σ := ι) (R := R) p).range
  let ψ : MvPolynomial ι R →ₐ[R] N ⊗[R] H := MvPolynomial.aeval fun i ↦
    ∑ j, (⟨MvPolynomial.X j ^ p, ⟨MvPolynomial.X j, MvPolynomial.expand_X p j⟩⟩ : N) ⊗ₜ[R]
      ((HopfAlgebra.antipode R (matrixCoefficient (C := H) (b.coord i) (b j))) ^ p)
  let inc := Algebra.TensorProduct.map N.val (AlgHom.id R H)
  have h : inc.comp ψ = (polynomialCoact H b).comp (MvPolynomial.expand p) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, MvPolynomial.aeval_X, MvPolynomial.expand_X,
      map_pow, polynomialCoact_X, sum_pow_char p, map_sum, Algebra.TensorProduct.map_tmul,
      AlgHom.id_apply, ψ, inc]
    simp only [Subalgebra.val_apply, Algebra.TensorProduct.tmul_pow]
  have hinc : inc.toLinearMap = TensorProduct.map N.toSubmodule.subtype
      (LinearMap.id : H →ₗ[R] H) :=
    (Algebra.TensorProduct.toLinearMap_map N.val (AlgHom.id R H)).trans
      (TensorProduct.AlgebraTensorModule.map_eq _ _)
  -- The remaining carrier identification is `↥N = ↥N.toSubmodule`: both are the same subtype.
  refine ⟨ψ f, ?_⟩
  rw [← hinc, AlgHom.toLinearMap_apply]
  exact DFunLike.congr_fun h f

end Frobenius

variable [DecidableEq ι]

variable (H) in
/-- The comodule of polynomial functions on a comodule `V` with a finite basis `b`, in the
coordinates of `b`: the symmetric algebra of the dual comodule, transported along the
identification of `Sym(V*)` with `MvPolynomial ι R` sending `b*ᵢ` to `X i`.

This is deliberately not a global instance, since `MvPolynomial ι R` carries many coactions. -/
@[implicit_reducible]
noncomputable def polynomial (b : Basis ι R V) : Comodule R H (MvPolynomial ι R) :=
  haveI := Module.Finite.of_basis b
  haveI := Module.Projective.of_basis b
  letI := dual R H V
  letI := symmetricAlgebra R H (Module.Dual R V)
  Transport (SymmetricAlgebra.equivMvPolynomial b.dualBasis).toLinearEquiv

/-- The coaction of the coordinate function `X i` on polynomial functions. -/
theorem polynomial_coact_X (b : Basis ι R V) (i : ι) :
    letI := polynomial H b
    coact (R := R) (C := H) (MvPolynomial.X i : MvPolynomial ι R) =
      ∑ j, MvPolynomial.X j ⊗ₜ[R]
        HopfAlgebra.antipode R (matrixCoefficient (C := H) (b.coord i) (b j)) := by
  have := Module.Finite.of_basis b
  have := Module.Projective.of_basis b
  let _ := dual R H V
  let _ := symmetricAlgebra R H (Module.Dual R V)
  have he : (SymmetricAlgebra.equivMvPolynomial b.dualBasis).toLinearEquiv.symm
      (MvPolynomial.X i) = SymmetricAlgebra.ι R (Module.Dual R V) (b.dualBasis i) :=
    SymmetricAlgebra.equivMvPolynomial_symm_X b.dualBasis i
  rw [polynomial, transport_coact_apply, he, symmetricAlgebra_coact, AlgHom.toLinearMap_apply,
    symmetricAlgebraCoact_ι, dual_coact, dualCoact_eq_sum b, map_sum, map_sum]
  simp only [LinearMap.rTensor_tmul, TensorProduct.map_tmul, LinearEquiv.coe_coe,
    AlgEquiv.toLinearEquiv_apply, SymmetricAlgebra.equivMvPolynomial_ι_apply, LinearMap.id_coe,
    id_eq]
  simp only [Basis.coe_dualBasis]

/-- The coaction on polynomial functions is the algebra homomorphism `polynomialCoact`. -/
theorem polynomial_coact (b : Basis ι R V) :
    letI := polynomial H b
    coact (R := R) (C := H) (M := MvPolynomial ι R) = (polynomialCoact H b).toLinearMap := by
  have := Module.Finite.of_basis b
  have := Module.Projective.of_basis b
  let _ := dual R H V
  let _ := symmetricAlgebra R H (Module.Dual R V)
  let e := SymmetricAlgebra.equivMvPolynomial b.dualBasis
  -- The transported coaction is a composite of algebra homomorphisms.
  let φ : MvPolynomial ι R →ₐ[R] MvPolynomial ι R ⊗[R] H :=
    (Algebra.TensorProduct.map e.toAlgHom (AlgHom.id R H)).comp
      ((symmetricAlgebraCoact R H (Module.Dual R V)).comp e.symm.toAlgHom)
  have hφ : (letI := polynomial H b; coact (R := R) (C := H) (M := MvPolynomial ι R)) =
      φ.toLinearMap := by
    refine LinearMap.ext fun f ↦ ?_
    rw [polynomial, transport_coact_apply, ← LinearMap.rTensor_def,
      ← AlgEquiv.toAlgHom_toLinearMap, AlgHom.rTensor_toLinearMap_apply,
      ← AlgEquiv.toLinearEquiv_symm, AlgEquiv.toLinearEquiv_apply, symmetricAlgebra_coact]
    simp only [φ, e, AlgHom.toLinearMap_apply, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom]
  have h : φ = polynomialCoact H b := MvPolynomial.algHom_ext fun i ↦ by
    rw [polynomialCoact_X, ← polynomial_coact_X b i, hφ, AlgHom.toLinearMap_apply]
  exact hφ.trans (by rw [h])

theorem polynomial_coact_apply (b : Basis ι R V) (f : MvPolynomial ι R) :
    letI := polynomial H b
    coact (R := R) (C := H) f = polynomialCoact H b f := by
  rw [polynomial_coact, AlgHom.toLinearMap_apply]

variable (H) in
/-- The polynomial functions in the pth powers of the coordinates form a subcomodule in
characteristic `p`. The coefficients remain in the original semiring. -/
noncomputable def polynomialExpandSubcomodule (b : Basis ι R V) (p : ℕ)
    [Fact p.Prime] [CharP R p] :
    letI := polynomial H b
    Subcomodule R H (MvPolynomial ι R) :=
  letI := polynomial H b
  { carrier := (MvPolynomial.expand p).range.toSubmodule
    coact_mem' := by
      rintro _ ⟨f, rfl⟩
      rw [polynomial_coact_apply]
      exact polynomialCoact_expand_mem H b p f }

/-- Membership in the polynomial Frobenius subcomodule means being an expansion by `p`. -/
@[simp]
theorem mem_polynomialExpandSubcomodule (b : Basis ι R V) (p : ℕ)
    [Fact p.Prime] [CharP R p] {f : MvPolynomial ι R} :
    f ∈ polynomialExpandSubcomodule H b p ↔ ∃ g, MvPolynomial.expand p g = f :=
  Iff.rfl

variable (H) in
/-- The homogeneous polynomial functions of degree `d` on `V`, as a subcomodule of
`polynomial H b`: the image of the `d`-th symmetric power of `V*`. -/
noncomputable def polynomialHomogeneousSubcomodule (b : Basis ι R V) (d : ℕ) :
    letI := polynomial H b
    Subcomodule R H (MvPolynomial ι R) :=
  letI := polynomial H b
  haveI := Module.Finite.of_basis b
  haveI := Module.Projective.of_basis b
  letI := dual R H V
  letI := symmetricAlgebra R H (Module.Dual R V)
  (symmetricPowerSubcomodule R H (Module.Dual R V) d).map
    (transportToHom (SymmetricAlgebra.equivMvPolynomial b.dualBasis).toLinearEquiv)

@[simp]
theorem mem_polynomialHomogeneousSubcomodule (b : Basis ι R V) {d : ℕ} {f : MvPolynomial ι R} :
    f ∈ polynomialHomogeneousSubcomodule H b d ↔ f.IsHomogeneous d := by
  let _ := polynomial H b
  have := Module.Finite.of_basis b
  have := Module.Projective.of_basis b
  let _ := dual R H V
  let _ := symmetricAlgebra R H (Module.Dual R V)
  rw [polynomialHomogeneousSubcomodule, ← Subcomodule.mem_toSubmodule,
    Subcomodule.map_toSubmodule, transportToHom_toLinearMap, AlgEquiv.toLinearEquiv_toLinearMap,
    symmetricPowerSubcomodule_toSubmodule,
    SymmetricAlgebra.map_homogeneousSubmodule_equivMvPolynomial,
    MvPolynomial.mem_homogeneousSubmodule]

section Points

variable {A : Type*} [CommSemiring A] [Algebra R A]

/-- **Points act on polynomial functions by the contragredient substitution.** Under
`A ⊗[R] R[X] ≃ A[X]`, an `A`-point `g` substitutes `∑ j, g(S(c(b*ᵢ, b j))) X j` for `X i`; that
is, `(g • f)(v) = f(g⁻¹ v)`. -/
theorem algebraTensorAlgEquiv_endOfPoint_polynomial (b : Basis ι R V) (g : H →ₐ[R] A)
    (f : MvPolynomial ι R) :
    letI := polynomial H b
    MvPolynomial.algebraTensorAlgEquiv R A (endOfPoint (MvPolynomial ι R) g (1 ⊗ₜ f)) =
      MvPolynomial.aeval (fun i ↦ ∑ j, MvPolynomial.C
        (g (HopfAlgebra.antipode R (matrixCoefficient (C := H) (b.coord i) (b j)))) *
          MvPolynomial.X j) f := by
  let _ := polynomial H b
  -- Both sides are algebra homomorphisms in `f`, so it suffices to compare them on `X i`.
  let Ψ : MvPolynomial ι R →ₐ[R] MvPolynomial ι A :=
    ((MvPolynomial.algebraTensorAlgEquiv R A).toAlgHom.restrictScalars R).comp
      ((Algebra.TensorProduct.comm R (MvPolynomial ι R) A).toAlgHom.comp
        ((Algebra.TensorProduct.map (AlgHom.id R _) g).comp (polynomialCoact H b)))
  have hΨ (f : MvPolynomial ι R) :
      MvPolynomial.algebraTensorAlgEquiv R A (endOfPoint (MvPolynomial ι R) g (1 ⊗ₜ f)) =
        Ψ f := by
    rw [endOfPoint_tmul, one_smul, polynomial_coact_apply]
    simp only [Ψ, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgHom.coe_restrictScalars']
    rw [AlgHom.lTensor_toLinearMap_apply, ← Algebra.TensorProduct.comm_toLinearEquiv,
      AlgEquiv.toLinearEquiv_apply]
  rw [hΨ]
  congr 1
  refine MvPolynomial.algHom_ext fun i ↦ ?_
  simp [Ψ, Algebra.TensorProduct.map_tmul, MvPolynomial.smul_eq_C_mul]

end Points

end Comodule

end TauCeti
