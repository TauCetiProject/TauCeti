/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.BinaryForm
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.RootSubgroup.Invariants
public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Coaction
import TauCeti.RingTheory.MvPolynomial.Homogeneous

/-!
# Binary forms as functions on `SL₂ / N⁺`

Evaluating a polynomial function on the standard representation of `SLₙ` at the `j`-th column of
a matrix is the pullback along the orbit map `g ↦ g eⱼ`. It is a comodule morphism from the
polynomial functions, with their contragredient action `(g • f)(v) = f(g⁻¹ v)`, to the functions
on `SLₙ` under left translation `(g • φ)(x) = φ(g⁻¹ x)`.

For `SL₂` and the first column `(a, c)`, this identifies the binary forms of degree `d` with the
degree-`d` polynomials in `a` and `c`, as rational representations under left translation:

* the map `f ↦ f(a, c)` is injective, because `a` and `c` are algebraically independent;
* its image is the algebra `O(SL₂)^{N⁺}` of functions invariant under right translation by the
  upper unipotent subgroup `N⁺`;
* right translation by `diag(t, t⁻¹)` scales the first column by `t`, so it acts on the image of
  the degree-`d` forms by the character `t ↦ tᵈ`, including `d = 0`.

All statements hold over every commutative ring, and invariance and equivariance are meant
scheme-theoretically, through coactions or points over every commutative algebra. Over a finite
field this is stronger than a statement about rational points.

## Main declarations

* `TauCeti.SpecialLinear.columnOrbitHom`: evaluation at the `j`-th column, as a comodule morphism
  into the left regular comodule of `O(SLₙ)`.
* `TauCeti.SpecialLinear.columnOrbitHom_two_injective`: for `SL₂` and the first column it is
  injective.
* `TauCeti.SpecialLinear.range_columnOrbitHom_two_eq_coinvariants`: its range is `O(SL₂)^{N⁺}`.
* `TauCeti.SpecialLinear.ofConv_mul_columnOrbitHom_two_of_diagonal`: right translation by
  `diag(t, t⁻¹)` acts on the degree-`d` forms by `tᵈ`.
* `TauCeti.SpecialLinear.binaryFormFunctions`: the degree-`d` polynomials in `a` and `c`, as a
  subcomodule of the left regular comodule; it is the injective image of the binary forms
  `R[x, y]_d` under `columnOrbitHom`.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, 2nd ed., II.2.16.
-/

public section

open scoped TensorProduct

namespace TauCeti.SpecialLinear

universe u v

variable (R : Type u) [CommRing R]

attribute [local instance] GeneralLinear.standardComodule standardComodule

noncomputable section

section Column

variable (n : ℕ)

/-- **Evaluation at a column is equivariant.** Evaluating a polynomial function on the standard
representation at the `j`-th column, `f ↦ f(x₀ⱼ, …, xₙ₋₁ⱼ)`, is a comodule morphism from the
polynomial functions to the left regular comodule of `O(SLₙ)`. It is the pullback along the orbit
map `g ↦ g eⱼ`, given by the orbit coordinates `Comodule.polynomialOrbitCoordinates`. -/
def columnOrbitHom (j : Fin n) :
    letI := polynomialComodule R n
    letI := Comodule.leftRegular R (coordinateHopfAlgebra R n)
    Comodule.Hom R (coordinateHopfAlgebra R n) (MvPolynomial (Fin n) R)
      (coordinateHopfAlgebra R n) :=
  letI := polynomialComodule R n
  letI := Comodule.leftRegular R (coordinateHopfAlgebra R n)
  { toLinearMap := (Comodule.polynomialOrbitCoordinates (coordinateHopfAlgebra R n)
      (Pi.basisFun R (Fin n)) (Pi.single j 1)).toLinearMap
    map_coact := by
      rw [polynomialComodule_coact, Comodule.leftRegular_coact,
        ← Comodule.toLinearMap_leftRegularCoactAlgHom, ← AlgHom.comp_toLinearMap,
        Comodule.leftRegularCoactAlgHom_comp_polynomialOrbitCoordinates, AlgHom.comp_toLinearMap]
      rfl }

variable {R n}

/-- Evaluation at the `j`-th column substitutes the generic entry `xᵢⱼ` for `X i`. -/
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

section SL2

variable {R}

private theorem columnOrbitHom_two_zero_apply (f : MvPolynomial (Fin 2) R) :
    letI := polynomialComodule R 2
    letI := Comodule.leftRegular R (coordinateHopfAlgebra R 2)
    columnOrbitHom R 2 0 f = MvPolynomial.aeval
      ![(GeneralLinear.genericMatrix R 2).map (coordinateMap R 2).hom 0 0,
        (GeneralLinear.genericMatrix R 2).map (coordinateMap R 2).hom 1 0] f := by
  let _ := polynomialComodule R 2
  let _ := Comodule.leftRegular R (coordinateHopfAlgebra R 2)
  rw [columnOrbitHom_apply]
  refine congrArg (MvPolynomial.aeval · f) (funext fun i ↦ ?_)
  fin_cases i <;> rfl

/-- **Evaluation at the first column of `SL₂` is injective**: the entries `a` and `c` are
algebraically independent over every commutative ring. -/
theorem columnOrbitHom_two_injective :
    letI := polynomialComodule R 2
    letI := Comodule.leftRegular R (coordinateHopfAlgebra R 2)
    Function.Injective (columnOrbitHom R 2 0) := by
  let _ := polynomialComodule R 2
  let _ := Comodule.leftRegular R (coordinateHopfAlgebra R 2)
  intro f f' h
  rw [columnOrbitHom_two_zero_apply, columnOrbitHom_two_zero_apply] at h
  exact (algebraicIndependent_iff_injective_aeval.mp
    (algebraicIndependent_genericMatrix_col_zero_two (R := R))) h

/-- **The right invariants of the upper unipotent subgroup are the polynomials in the first
column.** The range of evaluation at the first column of `SL₂` is the algebra of functions
invariant under right translation by `N⁺`. -/
theorem range_columnOrbitHom_two_eq_coinvariants :
    letI := polynomialComodule R 2
    letI := Comodule.leftRegular R (coordinateHopfAlgebra R 2)
    LinearMap.range (columnOrbitHom R 2 0).toLinearMap =
      Subalgebra.toSubmodule
        (rootSubgroupHopfIdeal (R := R) (zero_ne_one : (0 : Fin 2) ≠ 1)).coinvariants := by
  let _ := polynomialComodule R 2
  let _ := Comodule.leftRegular R (coordinateHopfAlgebra R 2)
  rw [coinvariants_rootSubgroupHopfIdeal_two_eq_adjoin,
    ← Matrix.range_cons_cons_empty _ _ ![], Algebra.adjoin_range_eq_range_aeval]
  ext φ
  simp only [LinearMap.mem_range, Comodule.Hom.coe_toLinearMap, Subalgebra.mem_toSubmodule,
    AlgHom.mem_range]
  exact exists_congr fun f ↦ by rw [columnOrbitHom_two_zero_apply]

/-- **Right translation by the diagonal torus on binary forms.** Right translation by
`diag(t, t⁻¹)` scales the first column by `t`, so it multiplies the image of a binary form of
degree `d` by `tᵈ`. The statement holds for points `x` and `h` over every commutative
`R`-algebra `A`; since `x * h` is the point `y ↦ x(y) h(y)` of `SL₂`, it is right translation by
the torus on the functor of points. -/
theorem ofConv_mul_columnOrbitHom_two_of_diagonal {A : Type v} [CommRing A] [Algebra R A]
    (x h : WithConv (coordinateHopfAlgebra R 2 →ₐ[R] A)) (t : Aˣ)
    (hh : (pointsMulEquiv (R := R) (A := A) 2 h : Matrix (Fin 2) (Fin 2) A) =
      !![(t : A), 0; 0, ((t⁻¹ : Aˣ) : A)])
    {d : ℕ} {f : MvPolynomial (Fin 2) R} (hf : f ∈ binaryForms R d) :
    letI := polynomialComodule R 2
    letI := Comodule.leftRegular R (coordinateHopfAlgebra R 2)
    (x * h).ofConv (columnOrbitHom R 2 0 f) = (t : A) ^ d * x.ofConv (columnOrbitHom R 2 0 f) := by
  let _ := polynomialComodule R 2
  let _ := Comodule.leftRegular R (coordinateHopfAlgebra R 2)
  rw [columnOrbitHom_two_zero_apply, MvPolynomial.comp_aeval_apply, MvPolynomial.comp_aeval_apply]
  -- The first column of `x * h` is `t` times the first column of `x`.
  have hcol (i : Fin 2) : (x * h).ofConv ((GeneralLinear.genericMatrix R 2).map
      (coordinateMap R 2).hom i 0) =
        (t : A) * x.ofConv ((GeneralLinear.genericMatrix R 2).map (coordinateMap R 2).hom i 0) := by
    have hmul : (pointsMulEquiv (R := R) (A := A) 2 (x * h) : Matrix (Fin 2) (Fin 2) A) i 0 =
        (pointsMulEquiv (R := R) (A := A) 2 x : Matrix (Fin 2) (Fin 2) A) i 0 * t := by
      rw [map_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hh]
      simp
    rw [coe_pointsMulEquiv_apply, coe_pointsMulEquiv_apply] at hmul
    rw [hmul, mul_comm]
  have hvec : (fun i ↦ (x * h).ofConv (![(GeneralLinear.genericMatrix R 2).map
      (coordinateMap R 2).hom 0 0, (GeneralLinear.genericMatrix R 2).map
        (coordinateMap R 2).hom 1 0] i)) =
      (t : A) • fun i ↦ x.ofConv (![(GeneralLinear.genericMatrix R 2).map
        (coordinateMap R 2).hom 0 0, (GeneralLinear.genericMatrix R 2).map
          (coordinateMap R 2).hom 1 0] i) := by
    funext i
    fin_cases i <;> exact hcol _
  rw [hvec, ((mem_binaryForms).mp hf).aeval_smul, smul_eq_mul]

variable (R) in
/-- The degree-`d` polynomials in the first-column entries `a` and `c`, as a subcomodule of the
functions on `SL₂` under left translation: the image of the binary forms of degree `d` under
evaluation at the first column. -/
def binaryFormFunctions (d : ℕ) :
    letI := Comodule.leftRegular R (coordinateHopfAlgebra R 2)
    Subcomodule R (coordinateHopfAlgebra R 2) (coordinateHopfAlgebra R 2) :=
  letI := polynomialComodule R 2
  letI := Comodule.leftRegular R (coordinateHopfAlgebra R 2)
  (binaryForms R d).map (columnOrbitHom R 2 0)

/-- A function on `SL₂` is a degree-`d` function of the first column exactly when it is a binary
form of degree `d` evaluated at `(a, c)`. -/
theorem mem_binaryFormFunctions {d : ℕ} {φ : coordinateHopfAlgebra R 2} :
    letI := polynomialComodule R 2
    letI := Comodule.leftRegular R (coordinateHopfAlgebra R 2)
    φ ∈ binaryFormFunctions R d ↔ ∃ f : MvPolynomial (Fin 2) R, f.IsHomogeneous d ∧
      columnOrbitHom R 2 0 f = φ := by
  let _ := polynomialComodule R 2
  let _ := Comodule.leftRegular R (coordinateHopfAlgebra R 2)
  rw [binaryFormFunctions, Subcomodule.mem_map]
  exact exists_congr fun f ↦ and_congr_left fun _ ↦ mem_binaryForms

end SL2

end

end TauCeti.SpecialLinear
