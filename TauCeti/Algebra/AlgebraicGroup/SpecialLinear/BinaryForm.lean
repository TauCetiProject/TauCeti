/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.StandardComodule
public import TauCeti.Algebra.Polynomial.Homogenize
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.UpperTriangular.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.SymmetricAlgebra.Polynomial
import Mathlib.Algebra.MvPolynomial.Coeff
import TauCeti.Algebra.Coalgebra.Subcomodule.PointSeparation
import TauCeti.Algebra.MvPolynomial.Fin.Two
import TauCeti.RingTheory.TensorProduct.MvPolynomial

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

Subrepresentations are detected by the universal unitriangular points over `R[t]`: a
subrepresentation containing `f` contains every `t`-coefficient of `f(x - t y, y)` and of
`f(x, y - t x)`. On monomials these are the divided-power operators
`xⁱ yʲ ↦ (i choose n) xⁱ⁻ⁿ yʲ⁺ⁿ` and `xⁱ yʲ ↦ (j choose n) xⁱ⁺ⁿ yʲ⁻ⁿ`, up to sign. Over a field,
the top `t`-coefficient of `f(x - t y, y)` is a nonzero multiple of `yᵈ`, so `yᵈ` lies in every
nonzero subrepresentation of the binary forms of degree `d`, in every characteristic. Hence the
binary forms are indecomposable, and they are simple as soon as every `d choose n` is nonzero in
the field, in particular in characteristic zero. In characteristic `p` this binomial condition
holds exactly for `d = (a + 1) pᵐ - 1` with `0 ≤ a < p`, by Lucas' theorem; the converse, that the
binary forms of any other degree have a proper nonzero subrepresentation, is not proved here.

## Main declarations

* `TauCeti.SpecialLinear.polynomialComodule`: polynomial functions on the standard representation
  of `SLₙ`.
* `TauCeti.SpecialLinear.algebraTensorAlgEquiv_endOfPoint_polynomialComodule`: points act by the
  inverse matrix on the coordinates.
* `TauCeti.SpecialLinear.binaryForms`: the binary forms of degree `d`, as a subcomodule.
* `TauCeti.SpecialLinear.algebraTensorAlgEquiv_endOfPoint_binaryForm`: the explicit action of
  `SL₂` on binary forms.
* `TauCeti.SpecialLinear.endOfPoint_binaryForm_monomial_of_diagonal`: torus weights of monomials.
* `TauCeti.SpecialLinear.lTensor_coact_X_one_pow`: `yᵈ` spans a `B⁺`-stable line of weight `d`.
* `TauCeti.SpecialLinear.exists_lTensor_coact_eq_tmul_iff_mem_span`: a binary form spans a
  `B⁺`-stable line iff it is a multiple of `yᵈ`.
* `TauCeti.SpecialLinear.choose_smul_X_pow_sub_mul_X_pow_add_mem` and
  `TauCeti.SpecialLinear.choose_smul_X_pow_add_mul_X_pow_sub_mem`: subrepresentations are stable
  under the divided-power operators of the two root subgroups.
* `TauCeti.SpecialLinear.X_one_pow_mem_of_ne_bot`: every nonzero subrepresentation of the binary
  forms of degree `d` contains `yᵈ`.
* `TauCeti.SpecialLinear.eq_bot_or_eq_bot_of_le_binaryForms_of_disjoint`: the binary forms are
  indecomposable.
* `TauCeti.SpecialLinear.isAtom_binaryForms` and
  `TauCeti.SpecialLinear.isAtom_binaryForms_of_charZero`: the binary forms of degree `d` are simple
  when every `d choose n` is nonzero, in particular in characteristic zero.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, 2nd ed., II.2.16.
* J. C. Jantzen, *Representations of Algebraic Groups*, 2nd ed., Part II, Chapter 3, for the
  simple modules of `SL₂` in positive characteristic.
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

/-! ### Subrepresentations -/

section Subrepresentations

open Polynomial

attribute [local instance] polynomialComodule

/-- The universal upper unitriangular point `[[1, t], [0, 1]]` over `R[t]`. -/
private noncomputable def upperPoint : WithConv (coordinateHopfAlgebra R 2 →ₐ[R] R[X]) :=
  (pointsMulEquiv (R := R) (A := R[X]) 2).symm (Matrix.SpecialLinearGroup.transvection
    (zero_ne_one : (0 : Fin 2) ≠ 1) X)

/-- The universal lower unitriangular point `[[1, 0], [t, 1]]` over `R[t]`. -/
private noncomputable def lowerPoint : WithConv (coordinateHopfAlgebra R 2 →ₐ[R] R[X]) :=
  (pointsMulEquiv (R := R) (A := R[X]) 2).symm (Matrix.SpecialLinearGroup.transvection
    (one_ne_zero : (1 : Fin 2) ≠ 0) X)

private theorem algebraTensorAlgEquiv_endOfPoint_upperPoint (f : MvPolynomial (Fin 2) R) :
    MvPolynomial.algebraTensorAlgEquiv R R[X]
        (Comodule.endOfPoint (MvPolynomial (Fin 2) R) (upperPoint (R := R)).ofConv (1 ⊗ₜ f)) =
      MvPolynomial.aeval
        ![MvPolynomial.X 0 - MvPolynomial.C X * MvPolynomial.X 1, MvPolynomial.X 1] f := by
  rw [algebraTensorAlgEquiv_endOfPoint_binaryForm _ (a := 1) (b := X) (c := 0) (d := 1)
    (by
      rw [upperPoint, MulEquiv.apply_symm_apply, Matrix.SpecialLinearGroup.transvection_coe]
      ext i j; fin_cases i <;> fin_cases j <;> simp)]
  simp

private theorem algebraTensorAlgEquiv_endOfPoint_lowerPoint (f : MvPolynomial (Fin 2) R) :
    MvPolynomial.algebraTensorAlgEquiv R R[X]
        (Comodule.endOfPoint (MvPolynomial (Fin 2) R) (lowerPoint (R := R)).ofConv (1 ⊗ₜ f)) =
      MvPolynomial.aeval
        ![MvPolynomial.X 0, MvPolynomial.X 1 - MvPolynomial.C X * MvPolynomial.X 0] f := by
  rw [algebraTensorAlgEquiv_endOfPoint_binaryForm _ (a := 1) (b := 0) (c := X) (d := 1)
    (by
      rw [lowerPoint, MulEquiv.apply_symm_apply, Matrix.SpecialLinearGroup.transvection_coe]
      ext i j; fin_cases i <;> fin_cases j <;> simp)]
  simp

/-- Contracting the action of a point over `R[t]` against the coefficient of `tⁿ`, as a linear
map on polynomial functions. -/
private noncomputable def coeffAction (g : WithConv (coordinateHopfAlgebra R 2 →ₐ[R] R[X]))
    (n : ℕ) : MvPolynomial (Fin 2) R →ₗ[R] MvPolynomial (Fin 2) R :=
  (TensorProduct.lid R _).toLinearMap ∘ₗ LinearMap.rTensor _ (lcoeff R n) ∘ₗ
    (Comodule.endOfPoint (MvPolynomial (Fin 2) R) g.ofConv).restrictScalars R ∘ₗ
      TensorProduct.mk R R[X] _ 1

private theorem coeffAction_mem (W : Subcomodule R (coordinateHopfAlgebra R 2)
    (MvPolynomial (Fin 2) R)) (g : WithConv (coordinateHopfAlgebra R 2 →ₐ[R] R[X])) (n : ℕ)
    {f : MvPolynomial (Fin 2) R} (hf : f ∈ W) : coeffAction g n f ∈ W :=
  W.lid_rTensor_endOfPoint_mem g.ofConv (lcoeff R n) hf

/-- If a point over `R[t]` acts on `f` by `(u - t v) ^ i * w`, then the coefficient of `tⁿ` is
`(-1)ⁿ (i choose n) uⁱ⁻ⁿ vⁿ w`. -/
private theorem coeffAction_eq (g : WithConv (coordinateHopfAlgebra R 2 →ₐ[R] R[X]))
    {f u v w : MvPolynomial (Fin 2) R} {i : ℕ}
    (hf : MvPolynomial.algebraTensorAlgEquiv R R[X]
        (Comodule.endOfPoint (MvPolynomial (Fin 2) R) g.ofConv (1 ⊗ₜ f)) =
      (MvPolynomial.map (algebraMap R R[X]) u -
          MvPolynomial.C X * MvPolynomial.map (algebraMap R R[X]) v) ^ i *
        MvPolynomial.map (algebraMap R R[X]) w) (n : ℕ) :
    coeffAction g n f = ((-1) ^ n * (i.choose n : R)) • (u ^ (i - n) * v ^ n * w) := by
  have h : Comodule.endOfPoint (MvPolynomial (Fin 2) R) g.ofConv (1 ⊗ₜ f) =
      ∑ l ∈ Finset.range (i + 1),
        (((-1) ^ l * (i.choose l : R)) • X ^ l) ⊗ₜ[R] (u ^ (i - l) * v ^ l * w) := by
    apply (MvPolynomial.algebraTensorAlgEquiv R R[X]).injective
    rw [hf, ← MvPolynomial.algebraTensorAlgEquiv_sum_tmul_pow_mul_pow, map_sum, map_sum,
      Finset.sum_mul]
    simp only [MvPolynomial.algebraTensorAlgEquiv_tmul, map_mul, smul_mul_assoc]
  simp only [coeffAction, LinearMap.coe_comp, Function.comp_apply, TensorProduct.mk_apply,
    LinearMap.restrictScalars_apply, h, map_sum, LinearMap.rTensor_tmul, lcoeff_apply,
    coeff_smul, coeff_X_pow, smul_eq_mul, mul_ite, mul_one, mul_zero, LinearEquiv.coe_coe,
    TensorProduct.lid_tmul, ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_range]
  split_ifs with hn
  · rfl
  · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero, zero_smul]

/-- The coefficient of `tⁿ` in `f(x - t y, y)` for a monomial `f = xⁱ yʲ`. -/
private theorem coeffAction_upperPoint_X_pow_mul_X_pow (i j n : ℕ) :
    coeffAction upperPoint n (MvPolynomial.X 0 ^ i * MvPolynomial.X 1 ^ j :
        MvPolynomial (Fin 2) R) =
      ((-1) ^ n * (i.choose n : R)) •
        (MvPolynomial.X 0 ^ (i - n) * MvPolynomial.X 1 ^ n * MvPolynomial.X 1 ^ j) :=
  coeffAction_eq upperPoint (w := MvPolynomial.X 1 ^ j)
    (by rw [algebraTensorAlgEquiv_endOfPoint_upperPoint]; simp) n

/-- The coefficient of `tⁿ` in `f(x, y - t x)` for a monomial `f = xⁱ yʲ`. -/
private theorem coeffAction_lowerPoint_X_pow_mul_X_pow (i j n : ℕ) :
    coeffAction lowerPoint n (MvPolynomial.X 0 ^ i * MvPolynomial.X 1 ^ j :
        MvPolynomial (Fin 2) R) =
      ((-1) ^ n * (j.choose n : R)) •
        (MvPolynomial.X 1 ^ (j - n) * MvPolynomial.X 0 ^ n * MvPolynomial.X 0 ^ i) :=
  coeffAction_eq lowerPoint (w := MvPolynomial.X 0 ^ i)
    (by rw [algebraTensorAlgEquiv_endOfPoint_lowerPoint]; simp [mul_comm]) n

/-- **Lowering the `x`-degree.** A subrepresentation of the polynomial functions containing
`xⁱ yʲ` contains `(i choose n) xⁱ⁻ⁿ yʲ⁺ⁿ`, over every commutative ring. Up to sign this is the
coefficient of `tⁿ` in the action `xⁱ yʲ ↦ (x - t y)ⁱ yʲ` of the upper unitriangular point
`[[1, t], [0, 1]]`. -/
theorem choose_smul_X_pow_sub_mul_X_pow_add_mem
    (W : Subcomodule R (coordinateHopfAlgebra R 2) (MvPolynomial (Fin 2) R)) {i j : ℕ}
    (h : (MvPolynomial.X 0 ^ i * MvPolynomial.X 1 ^ j : MvPolynomial (Fin 2) R) ∈ W) (n : ℕ) :
    (i.choose n : R) • (MvPolynomial.X 0 ^ (i - n) * MvPolynomial.X 1 ^ (j + n) :
      MvPolynomial (Fin 2) R) ∈ W := by
  have hmem := SMulMemClass.smul_mem ((-1) ^ n : R) (coeffAction_mem W upperPoint n h)
  rw [coeffAction_upperPoint_X_pow_mul_X_pow, smul_smul] at hmem
  convert hmem using 2
  · simp [← mul_assoc, ← mul_pow]
  · ring

/-- **Raising the `x`-degree.** A subrepresentation of the polynomial functions containing
`xⁱ yʲ` contains `(j choose n) xⁱ⁺ⁿ yʲ⁻ⁿ`, over every commutative ring. Up to sign this is the
coefficient of `tⁿ` in the action `xⁱ yʲ ↦ xⁱ (y - t x)ʲ` of the lower unitriangular point
`[[1, 0], [t, 1]]`. -/
theorem choose_smul_X_pow_add_mul_X_pow_sub_mem
    (W : Subcomodule R (coordinateHopfAlgebra R 2) (MvPolynomial (Fin 2) R)) {i j : ℕ}
    (h : (MvPolynomial.X 0 ^ i * MvPolynomial.X 1 ^ j : MvPolynomial (Fin 2) R) ∈ W) (n : ℕ) :
    (j.choose n : R) • (MvPolynomial.X 0 ^ (i + n) * MvPolynomial.X 1 ^ (j - n) :
      MvPolynomial (Fin 2) R) ∈ W := by
  have hmem := SMulMemClass.smul_mem ((-1) ^ n : R) (coeffAction_mem W lowerPoint n h)
  rw [coeffAction_lowerPoint_X_pow_mul_X_pow, smul_smul] at hmem
  convert hmem using 2
  · simp [← mul_assoc, ← mul_pow]
  · ring

section Field

variable {k : Type u} [Field k] {d : ℕ}

/-- **Every nonzero subrepresentation of the binary forms of degree `d` contains `yᵈ`**, over every
field and in every characteristic. Hence every nonzero subrepresentation contains the
subrepresentation generated by the highest line `k yᵈ`, which is therefore the simple socle. -/
theorem X_one_pow_mem_of_ne_bot {W : Subcomodule k (coordinateHopfAlgebra k 2)
      (MvPolynomial (Fin 2) k)} (hW : W ≤ binaryForms k d) (hW₀ : W ≠ ⊥) :
    MvPolynomial.X 1 ^ d ∈ W := by
  classical
  obtain ⟨f, hfW, hf₀⟩ := Subcomodule.ne_bot_iff.mp hW₀
  have hf := mem_binaryForms.mp (hW hfW)
  -- The largest power of `x` occurring in `f`, and a monomial `m₀` of `f` realizing it.
  have hne : (f.support.image (· 0)).Nonempty :=
    (Finset.nonempty_iff_ne_empty.mpr (by simpa using hf₀)).image _
  obtain ⟨m₀, hm₀, hm₀i⟩ := Finset.mem_image.mp ((f.support.image (· 0)).max'_mem hne)
  set i₀ := (f.support.image (· 0)).max' hne
  -- The coefficient of `t ^ i₀` in `f(x - t y, y)` only sees the monomial `m₀`.
  have key : coeffAction upperPoint i₀ f = (f.coeff m₀ * (-1) ^ i₀) • MvPolynomial.X 1 ^ d := by
    conv_lhs => rw [f.as_sum]
    rw [map_sum, Finset.sum_eq_single m₀]
    · rw [MvPolynomial.monomial_fin_two, mul_assoc, ← MvPolynomial.smul_eq_C_mul, map_smul,
        coeffAction_upperPoint_X_pow_mul_X_pow, hm₀i, Nat.choose_self, Nat.sub_self,
        ← hf.add_eq_of_mem_support hm₀, hm₀i]
      simp [smul_smul, pow_add, mul_comm]
    · -- Every other monomial has a smaller power of `x`, so its binomial coefficient vanishes.
      intro m hm hne₀
      have hle : m 0 ≤ i₀ := (f.support.image (· 0)).le_max' _ (Finset.mem_image_of_mem _ hm)
      have hlt : m 0 < i₀ := by
        refine hle.lt_of_ne fun heq ↦ hne₀ ?_
        have h₁ := hf.add_eq_of_mem_support hm
        have h₂ := hf.add_eq_of_mem_support hm₀
        exact Finsupp.ext (Fin.forall_fin_two.mpr ⟨heq.trans hm₀i.symm, by omega⟩)
      rw [MvPolynomial.monomial_fin_two, mul_assoc, ← MvPolynomial.smul_eq_C_mul, map_smul,
        coeffAction_upperPoint_X_pow_mul_X_pow, Nat.choose_eq_zero_of_lt hlt]
      simp
    · intro h
      exact absurd hm₀ h
  have hmem := SMulMemClass.smul_mem (f.coeff m₀ * (-1) ^ i₀)⁻¹
    (coeffAction_mem W upperPoint i₀ hfW)
  rwa [key, smul_smul, inv_mul_cancel₀ (mul_ne_zero (MvPolynomial.mem_support_iff.mp hm₀)
    (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))), one_smul] at hmem

/-- **The binary forms of degree `d` are indecomposable**, over every field and in every
characteristic: two subrepresentations meeting trivially cannot both be nonzero. -/
theorem eq_bot_or_eq_bot_of_le_binaryForms_of_disjoint
    {W₁ W₂ : Subcomodule k (coordinateHopfAlgebra k 2) (MvPolynomial (Fin 2) k)}
    (hW₁ : W₁ ≤ binaryForms k d) (hW₂ : W₂ ≤ binaryForms k d)
    (h : Disjoint W₁.toSubmodule W₂.toSubmodule) : W₁ = ⊥ ∨ W₂ = ⊥ := by
  by_contra! hne
  exact pow_ne_zero d (MvPolynomial.X_ne_zero 1) <| (Submodule.disjoint_def.mp h) _
    (X_one_pow_mem_of_ne_bot hW₁ hne.1) (X_one_pow_mem_of_ne_bot hW₂ hne.2)

/-- If the binomial coefficients `d choose n` are nonzero in `k`, every nonzero subrepresentation
of the binary forms of degree `d` is everything: starting from `yᵈ`, the lower unitriangular
points produce every monomial of degree `d`. -/
private theorem binaryForms_le_of_ne_bot (hd : ∀ n ≤ d, (d.choose n : k) ≠ 0)
    {W : Subcomodule k (coordinateHopfAlgebra k 2) (MvPolynomial (Fin 2) k)}
    (hW : W ≤ binaryForms k d) (hW₀ : W ≠ ⊥) : binaryForms k d ≤ W := by
  intro f hf
  have hy : (MvPolynomial.X 0 ^ 0 * MvPolynomial.X 1 ^ d : MvPolynomial (Fin 2) k) ∈ W := by
    simpa using X_one_pow_mem_of_ne_bot hW hW₀
  have hmon (n : ℕ) (hn : n ≤ d) :
      (MvPolynomial.X 0 ^ n * MvPolynomial.X 1 ^ (d - n) : MvPolynomial (Fin 2) k) ∈ W := by
    have hmem := SMulMemClass.smul_mem (d.choose n : k)⁻¹
      (choose_smul_X_pow_add_mul_X_pow_sub_mem W hy n)
    rwa [smul_smul, inv_mul_cancel₀ (hd n hn), one_smul, zero_add] at hmem
  have hf' := mem_binaryForms.mp hf
  rw [f.as_sum]
  refine sum_mem fun m hm ↦ ?_
  rw [MvPolynomial.monomial_fin_two, mul_assoc, ← MvPolynomial.smul_eq_C_mul]
  refine SMulMemClass.smul_mem _ ?_
  have hmd := hf'.add_eq_of_mem_support hm
  simpa [← hmd] using hmon (m 0) (hmd ▸ Nat.le_add_right _ _)

/-- **The binary forms of degree `d` are simple when the binomial coefficients `d choose n` are
nonzero in `k`**: they form an atom of the lattice of subrepresentations of the polynomial
functions, so each of their subrepresentations is zero or everything. -/
theorem isAtom_binaryForms (hd : ∀ n ≤ d, (d.choose n : k) ≠ 0) : IsAtom (binaryForms k d) := by
  refine ⟨fun h ↦ pow_ne_zero d (MvPolynomial.X_ne_zero (R := k) (1 : Fin 2)) ?_, fun W hW ↦ ?_⟩
  · have hmem : (MvPolynomial.X 1 ^ d : MvPolynomial (Fin 2) k) ∈ binaryForms k d :=
      mem_binaryForms.mpr (MvPolynomial.isHomogeneous_X_pow _ _)
    rwa [h, Subcomodule.mem_bot] at hmem
  · by_contra hW₀
    exact hW.not_ge (binaryForms_le_of_ne_bot hd hW.le hW₀)

/-- **In characteristic zero the binary forms of every degree form a simple representation.** -/
theorem isAtom_binaryForms_of_charZero [CharZero k] : IsAtom (binaryForms k d) :=
  isAtom_binaryForms fun _ hn ↦ Nat.cast_ne_zero.mpr (Nat.choose_pos hn).ne'

end Field

end Subrepresentations

end TauCeti.SpecialLinear
