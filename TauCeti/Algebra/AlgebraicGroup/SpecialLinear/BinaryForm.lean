/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.StandardComodule
public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Coaction
public import TauCeti.Algebra.Polynomial.Homogenize
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.UpperTriangular.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.SymmetricAlgebra.Polynomial

/-!
# Binary forms as rational representations of `SL₂`

The polynomial functions on the standard representation of `SLₙ` form a comodule over `O(SLₙ)`,
on which a point `g` acts contragrediently, `(g • f)(v) = f(g⁻¹ v)`. For `n = 2` the homogeneous
components are the binary forms `R[x, y]_d`, the basic rational representations of `SL₂`. A point
with matrix `[[a, b], [c, d]]` acts by `(g • f)(x, y) = f(d x - b y, a y - c x)`. The monomial
`xⁱ yʲ` has weight `j - i` for the diagonal torus, and `yᵈ` spans a line stable under the
upper-triangular subgroup `B⁺`, which acts on it through the character `aᵈ`.

Over a domain, every `B⁺`-stable line of binary forms of degree `d` is contained in `R yᵈ`, in
every characteristic; over a field, `R yᵈ` is therefore the unique such line. Stability is meant
scheme-theoretically: restricted to `B⁺`, the coaction sends `f` to `f ⊗ h` for some function `h`
on `B⁺`. It is tested on the universal unitriangular point `[[1, t], [0, 1]]` over `R[t]`, which
sends `f(x, y)` to `f(x - t y, y)`; comparing the values at `(x, y) = (t, 1)` and `(0, 1)` shows
that the dehomogenization `f(x, 1)` is constant. Over a finite field, invariance under the rational
points of `B⁺` alone would not suffice.

## Main declarations

* `TauCeti.SpecialLinear.polynomialComodule`: polynomial functions on the standard representation
  of `SLₙ`.
* `TauCeti.SpecialLinear.algebraTensorAlgEquiv_endOfPoint_polynomialComodule`: points act by the
  inverse matrix on the coordinates.
* `TauCeti.SpecialLinear.columnOrbitHom`: evaluation at the `j`-th column, as a comodule morphism
  into the left regular comodule of `O(SLₙ)`.
* `TauCeti.SpecialLinear.binaryForms`: the binary forms of degree `d`, as a subcomodule.
* `TauCeti.SpecialLinear.algebraTensorAlgEquiv_endOfPoint_binaryForm`: the explicit action of
  `SL₂` on binary forms.
* `TauCeti.SpecialLinear.endOfPoint_binaryForm_monomial_of_diagonal`: torus weights of monomials.
* `TauCeti.SpecialLinear.lTensor_coact_X_one_pow`: `yᵈ` spans a `B⁺`-stable line of weight `d`.
* `TauCeti.SpecialLinear.exists_lTensor_coact_eq_tmul_iff_mem_span`: a binary form spans a
  `B⁺`-stable line iff it is a multiple of `yᵈ`.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, 2nd ed., II.2.16.
* J. S. Milne, *Algebraic Groups* (2017), §4.a.
-/

public section

open Module WithConv
open scoped TensorProduct

namespace TauCeti.SpecialLinear

universe u v

variable (R : Type u) [CommRing R] (n : ℕ)

attribute [local instance] GeneralLinear.standardComodule standardComodule

/-- The comodule of polynomial functions on the standard representation of `SLₙ`, in the
coordinates `X i` of the standard basis. Points act contragrediently, `(g • f)(v) = f(g⁻¹ v)`
(`algebraTensorAlgEquiv_endOfPoint_polynomialComodule`). -/
@[implicit_reducible]
noncomputable def polynomialComodule :
    Comodule R (coordinateHopfAlgebra R n) (MvPolynomial (Fin n) R) :=
  Comodule.polynomial (coordinateHopfAlgebra R n) (Pi.basisFun R (Fin n))

/-- The coaction on polynomial functions on the standard representation of `SLₙ` is the algebra
homomorphism `Comodule.polynomialCoact` of the standard basis. -/
theorem polynomialComodule_coact :
    letI := polynomialComodule R n
    Comodule.coact (R := R) (C := coordinateHopfAlgebra R n) (M := MvPolynomial (Fin n) R) =
      (Comodule.polynomialCoact (coordinateHopfAlgebra R n) (Pi.basisFun R (Fin n))).toLinearMap :=
  Comodule.polynomial_coact _

section Column

/-- **Evaluation at a column is equivariant.** Evaluating a polynomial function on the standard
representation at the `j`-th column, `f ↦ f(x₀ⱼ, …, xₙ₋₁ⱼ)`, is a comodule morphism from the
polynomial functions to the left regular comodule of `O(SLₙ)`. It is the pullback along the orbit
map `g ↦ g eⱼ`, given by the orbit coordinates `Comodule.polynomialOrbitCoordinates`. -/
noncomputable def columnOrbitHom (j : Fin n) :
    letI := polynomialComodule R n
    letI := Comodule.leftRegular R (coordinateHopfAlgebra R n)
    Comodule.Hom R (coordinateHopfAlgebra R n) (MvPolynomial (Fin n) R)
      (coordinateHopfAlgebra R n) :=
  letI := polynomialComodule R n
  letI := Comodule.leftRegular R (coordinateHopfAlgebra R n)
  { toLinearMap := (Comodule.polynomialOrbitCoordinates (coordinateHopfAlgebra R n)
      (Pi.basisFun R (Fin n)) (Pi.single j 1)).toLinearMap
    map_coact := by
      rw [polynomialComodule_coact, Comodule.leftRegular_coact]
      exact Comodule.map_polynomialOrbitCoordinates_comp_polynomialCoact _ _ }

variable {R n}

/-- Evaluation at the `j`-th column substitutes the generic entry `xᵢⱼ` for `X i`. -/
@[simp]
theorem columnOrbitHom_apply (j : Fin n) (f : MvPolynomial (Fin n) R) :
    letI := polynomialComodule R n
    letI := Comodule.leftRegular R (coordinateHopfAlgebra R n)
    columnOrbitHom R n j f =
      MvPolynomial.aeval (fun i ↦ (GeneralLinear.genericMatrix R n).map (coordinateMap R n).hom i j)
        f := by
  let _ := polynomialComodule R n
  let _ := Comodule.leftRegular R (coordinateHopfAlgebra R n)
  rw [columnOrbitHom, Comodule.Hom.coe_mk, AlgHom.coe_toLinearMap]
  refine DFunLike.congr_fun (MvPolynomial.algHom_ext fun i ↦ ?_) f
  rw [Comodule.polynomialOrbitCoordinates_X, MvPolynomial.aeval_X, ← Pi.basisFun_apply R (Fin n) j,
    ← Comodule.coefficientMatrix_apply, coefficientMatrix_basisFun]

end Column

variable {R n} {A : Type v} [CommRing A] [Algebra R A]

/-- **Points of `SLₙ` act on polynomial functions contragrediently.** Under
`A ⊗[R] R[X] ≃ A[X]`, a point with matrix `g` substitutes `∑ j, (g⁻¹)ᵢⱼ X j` for `X i`, so that
`(g • f)(v) = f(g⁻¹ v)`. -/
theorem algebraTensorAlgEquiv_endOfPoint_polynomialComodule
    (g : WithConv (coordinateHopfAlgebra R n →ₐ[R] A)) (f : MvPolynomial (Fin n) R) :
    letI := polynomialComodule R n
    MvPolynomial.algebraTensorAlgEquiv R A
        (Comodule.endOfPoint (MvPolynomial (Fin n) R) g.ofConv (1 ⊗ₜ f)) =
      MvPolynomial.aeval (fun i ↦ ∑ j, MvPolynomial.C
        (((pointsMulEquiv (R := R) (A := A) n g)⁻¹ : Matrix.SpecialLinearGroup (Fin n) A) i j) *
          MvPolynomial.X j) f := by
  rw [polynomialComodule, Comodule.algebraTensorAlgEquiv_endOfPoint_polynomial]
  refine congrArg (MvPolynomial.aeval · f) (funext fun i ↦ Finset.sum_congr rfl fun j _ ↦ ?_)
  rw [← Comodule.coefficientMatrix_apply, ← WithConv.algHom_inv_apply, ofConv_coefficientMatrix,
    map_inv]

/-! ### Binary forms -/

section BinaryForm

variable (R) in
/-- The binary forms of degree `d`: the homogeneous polynomials of degree `d` in `x = X 0` and
`y = X 1`, as a subcomodule of the polynomial functions on the standard representation of
`SL₂`. -/
noncomputable def binaryForms (d : ℕ) :
    letI := polynomialComodule R 2
    Subcomodule R (coordinateHopfAlgebra R 2) (MvPolynomial (Fin 2) R) :=
  Comodule.polynomialHomogeneousSubcomodule (coordinateHopfAlgebra R 2) (Pi.basisFun R (Fin 2)) d

@[simp]
theorem mem_binaryForms {d : ℕ} {f : MvPolynomial (Fin 2) R} :
    f ∈ binaryForms R d ↔ f.IsHomogeneous d :=
  Comodule.mem_polynomialHomogeneousSubcomodule _

/-- **The rational action of `SL₂` on binary forms.** A point with matrix `[[a, b], [c, d]]` acts
by `(g • f)(x, y) = f(d x - b y, a y - c x)`. -/
theorem algebraTensorAlgEquiv_endOfPoint_binaryForm
    (g : WithConv (coordinateHopfAlgebra R 2 →ₐ[R] A)) {a b c d : A}
    (hg : (pointsMulEquiv (R := R) (A := A) 2 g : Matrix (Fin 2) (Fin 2) A) = !![a, b; c, d])
    (f : MvPolynomial (Fin 2) R) :
    letI := polynomialComodule R 2
    MvPolynomial.algebraTensorAlgEquiv R A
        (Comodule.endOfPoint (MvPolynomial (Fin 2) R) g.ofConv (1 ⊗ₜ f)) =
      MvPolynomial.aeval
        ![MvPolynomial.C d * MvPolynomial.X 0 - MvPolynomial.C b * MvPolynomial.X 1,
          MvPolynomial.C a * MvPolynomial.X 1 - MvPolynomial.C c * MvPolynomial.X 0] f := by
  rw [algebraTensorAlgEquiv_endOfPoint_polynomialComodule, Matrix.SpecialLinearGroup.SL2_inv_expl]
  refine congrArg (MvPolynomial.aeval · f) (funext fun i ↦ ?_)
  fin_cases i <;> simp [Fin.sum_univ_two, hg, sub_eq_add_neg, add_comm]

/-- **Torus weights of binary forms.** The diagonal point `diag(t, t⁻¹)` scales the monomial
`xⁱ yʲ` by `t⁻ⁱ tʲ`: it is a weight vector of weight `j - i`. -/
theorem endOfPoint_binaryForm_monomial_of_diagonal
    (g : WithConv (coordinateHopfAlgebra R 2 →ₐ[R] A)) (t : Aˣ)
    (hg : (pointsMulEquiv (R := R) (A := A) 2 g : Matrix (Fin 2) (Fin 2) A) =
      !![(t : A), 0; 0, ((t⁻¹ : Aˣ) : A)]) (i j : ℕ) :
    letI := polynomialComodule R 2
    Comodule.endOfPoint (MvPolynomial (Fin 2) R) g.ofConv
        (1 ⊗ₜ (MvPolynomial.X 0 ^ i * MvPolynomial.X 1 ^ j)) =
      (((t⁻¹ : Aˣ) : A) ^ i * (t : A) ^ j) •
        (1 ⊗ₜ (MvPolynomial.X 0 ^ i * MvPolynomial.X 1 ^ j)) := by
  apply (MvPolynomial.algebraTensorAlgEquiv R A).injective
  rw [algebraTensorAlgEquiv_endOfPoint_binaryForm g hg, map_smul,
    MvPolynomial.algebraTensorAlgEquiv_tmul]
  simp [mul_pow, MvPolynomial.smul_eq_C_mul]
  ring

end BinaryForm

/-! ### The highest line `R yᵈ` -/

section HighestLine

/-- **The line `R yᵈ` is stable under the upper-triangular subgroup.** Restricted to the
upper-triangular subgroup, the coaction of `yᵈ` is `yᵈ ⊗ aᵈ`, where `a` is the upper-left
coordinate: `yᵈ` is a highest weight vector of weight `d`. -/
theorem lTensor_coact_X_one_pow (d : ℕ) :
    letI := polynomialComodule R 2
    (UpperTriangular.coordinateMap R 2).hom.toLinearMap.lTensor (MvPolynomial (Fin 2) R)
        (Comodule.coact (R := R) (C := coordinateHopfAlgebra R 2)
          (MvPolynomial.X 1 ^ d : MvPolynomial (Fin 2) R)) =
      (MvPolynomial.X 1 ^ d) ⊗ₜ ((UpperTriangular.coordinateMap R 2).hom
        (Comodule.coefficientMatrix (C := coordinateHopfAlgebra R 2)
          (Pi.basisFun R (Fin 2)) 0 0) ^ d) := by
  let q := (UpperTriangular.coordinateMap R 2).hom
  -- Restriction to the upper-triangular subgroup is an algebra homomorphism.
  have hq : q.toLinearMap = (q : _ →ₐ[R] _).toLinearMap := (BialgHom.toAlgHom_toLinearMap q).symm
  rw [polynomialComodule, Comodule.polynomial_coact_apply, map_pow, Comodule.polynomialCoact_X,
    Fin.sum_univ_two, hq, AlgHom.lTensor_toLinearMap_apply]
  simp only [← Comodule.coefficientMatrix_apply, map_pow, map_add,
    Algebra.TensorProduct.map_tmul, AlgHom.id_apply, BialgHom.coe_toAlgHom, q]
  rw [antipode_coefficientMatrix_one_zero, antipode_coefficientMatrix_one_one, map_neg,
    coefficientMatrix_basisFun, Matrix.map_apply,
    UpperTriangular.coordinateMap_coordinateMap_genericMatrix_eq_zero_of_lt
      (by decide : (0 : Fin 2) < 1),
    neg_zero, TensorProduct.tmul_zero, zero_add, Algebra.TensorProduct.tmul_pow]

end HighestLine

/-! ### Uniqueness of the highest line -/

section Uniqueness

open Polynomial

/-- **A binary form spans a line stable under the upper-triangular subgroup iff it is a multiple
of `yᵈ`.** Over a domain, a binary form `f` of degree `d` spans a stable line, that is, its
coaction restricted to the upper-triangular subgroup is `f ⊗ h` for some function `h`, exactly
when `f` is a multiple of `yᵈ`. This holds in every characteristic. So every stable line is
contained in `R yᵈ`; over a field, `R yᵈ` is the unique stable line, while over `ℤ`, for example,
`ℤ (2 yᵈ)` is a different stable line. -/
theorem exists_lTensor_coact_eq_tmul_iff_mem_span [IsDomain R] {d : ℕ} {f : MvPolynomial (Fin 2) R}
    (hf : f ∈ binaryForms R d) :
    letI := polynomialComodule R 2
    (∃ h : UpperTriangular.coordinateHopfAlgebra R 2,
      (UpperTriangular.coordinateMap R 2).hom.toLinearMap.lTensor (MvPolynomial (Fin 2) R)
        (Comodule.coact (R := R) (C := coordinateHopfAlgebra R 2) f) = f ⊗ₜ h) ↔
      f ∈ R ∙ (MvPolynomial.X 1 ^ d : MvPolynomial (Fin 2) R) := by
  let _ := polynomialComodule R 2
  refine ⟨fun ⟨h, hfh⟩ ↦ ?_, fun hmem ↦ ?_⟩
  · -- The universal upper unitriangular point over `R[t]`, as a point of the Borel subgroup.
    let u : Matrix.SpecialLinearGroup (Fin 2) R[X] :=
      ⟨!![1, X; 0, 1], by simp [Matrix.det_fin_two]⟩
    have hu : u ∈ (upperTriangularGroup (Fin 2) R[X]).comap Matrix.SpecialLinearGroup.toGL := by
      rw [UpperTriangularGroup.mem_comap_toGL_iff]
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [u]
    let uB := (UpperTriangular.pointsMulEquiv R 2 (A := R[X])).symm ⟨u, hu⟩
    let g := CommHopfAlgCat.quotientPointsHom (coordinateHopfAlgebra R 2)
      (UpperTriangular.definingHopfIdeal R 2) (CommAlgCat.of R R[X]) uB
    have hg : (pointsMulEquiv (R := R) (A := R[X]) 2 g : Matrix (Fin 2) (Fin 2) R[X]) =
        !![1, X; 0, 1] := by
      simp [g, uB, u]
    -- The point acts on `f` by the scalar `uB h`.
    have key : Comodule.endOfPoint (MvPolynomial (Fin 2) R) g.ofConv (1 ⊗ₜ f) =
        uB.ofConv h • (1 ⊗ₜ f) := by
      have hgB : g.ofConv.toLinearMap = uB.ofConv.toLinearMap ∘ₗ
          (UpperTriangular.coordinateMap R 2).hom.toLinearMap := LinearMap.ext fun x ↦ by
        simp [g, BialgHom.toCoalgHom_apply]
      rw [Comodule.endOfPoint_tmul, hgB, LinearMap.lTensor_comp_apply, hfh]
      simp [TensorProduct.smul_tmul']
    have hpoly := congrArg (MvPolynomial.algebraTensorAlgEquiv R R[X]) key
    rw [algebraTensorAlgEquiv_endOfPoint_binaryForm g hg, map_smul,
      MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul] at hpoly
    simp only [map_one, one_mul, map_zero, zero_mul, sub_zero] at hpoly
    exact (mem_binaryForms.mp hf).mem_span_X_one_pow_of_aeval_eq_smul _ hpoly
  · obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hmem
    exact ⟨_, by rw [map_smul, map_smul, lTensor_coact_X_one_pow, TensorProduct.smul_tmul']⟩

end Uniqueness

end TauCeti.SpecialLinear
