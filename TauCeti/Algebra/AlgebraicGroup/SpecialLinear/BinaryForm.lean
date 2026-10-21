/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Homogenize
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.StandardComodule
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.UpperTriangular.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.PointAction
public import TauCeti.Algebra.Coalgebra.Comodule.SymmetricAlgebra.Polynomial

/-!
# Binary forms as rational representations of `SL₂`

The polynomial functions on the standard representation of `SLₙ` form a comodule over `O(SLₙ)`,
on which a point `g` acts contragrediently, `(g • f)(v) = f(g⁻¹ v)`. For `n = 2` the homogeneous
components are the binary forms `R[x, y]_d`, the basic rational representations of `SL₂`. A point
with matrix `[[a, b], [c, d]]` acts by `(g • f)(x, y) = f(d x - b y, a y - c x)`. The monomial
`xⁱ yʲ` has weight `j - i` for the diagonal torus, and `yᵈ` spans a line stable under the
upper-triangular subgroup `B⁺`, which acts on it through the character `aᵈ`.

Over a domain, `R yᵈ` is the only `B⁺`-stable line of binary forms of degree `d`, in every
characteristic. Stability is meant scheme-theoretically: restricted to `B⁺`, the coaction sends
`f` to `f ⊗ h` for some function `h` on `B⁺`. It is tested on the universal unitriangular point
`[[1, t], [0, 1]]` over `R[t]`, which sends `f(x, y)` to `f(x - t y, y)`; comparing the values at
`(x, y) = (t, 1)` and `(0, 1)` shows that the dehomogenization `f(x, 1)` is constant. Over a finite
field, invariance under the rational points of `B⁺` alone would not suffice.

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
* `TauCeti.SpecialLinear.exists_lTensor_coact_eq_tmul_iff_mem_span`: the `B⁺`-stable lines of
  binary forms are exactly the multiples of `yᵈ`.

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

variable {R n} {A : Type v} [CommRing A] [Algebra R A]

/-- In the base change of the standard basis, coordinates on `A ⊗[R] Rⁿ` are read off through
`piScalarRight`. -/
private theorem baseChange_basisFun_repr (x : A ⊗[R] (Fin n → R)) (p : Fin n) :
    ((Pi.basisFun R (Fin n)).baseChange A).repr x p =
      TensorProduct.piScalarRight R A A (Fin n) x p := by
  induction x using TensorProduct.inductionOn with
  | tmul a v => simp [Basis.baseChange_repr_tmul]
  | add x y hx hy => simp [hx, hy]

/-- In the standard basis, a point of `SLₙ` acts on the standard comodule by its matrix. -/
private theorem toMatrix_endOfPoint_standardComodule
    (g : WithConv (coordinateHopfAlgebra R n →ₐ[R] A)) :
    LinearMap.toMatrix ((Pi.basisFun R (Fin n)).baseChange A)
        ((Pi.basisFun R (Fin n)).baseChange A) (Comodule.endOfPoint (Fin n → R) g.ofConv) =
      (pointsMulEquiv (R := R) (A := A) n g : Matrix (Fin n) (Fin n) A) := by
  ext p q
  have h := LinearMap.congr_fun (piScalarRight_comp_endOfPoint R n g)
    ((Pi.basisFun R (Fin n)).baseChange A q)
  rw [LinearMap.comp_apply, LinearMap.comp_apply] at h
  rw [LinearMap.toMatrix_apply, baseChange_basisFun_repr, ← LinearEquiv.coe_coe, h]
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

/-- A point of `SLₙ` takes the coefficient matrix of the standard comodule to its matrix. -/
private theorem ofConv_coefficientMatrix (g : WithConv (coordinateHopfAlgebra R n →ₐ[R] A))
    (i j : Fin n) :
    g.ofConv (Comodule.coefficientMatrix (C := coordinateHopfAlgebra R n)
        (Pi.basisFun R (Fin n)) i j) =
      (pointsMulEquiv (R := R) (A := A) n g : Matrix (Fin n) (Fin n) A) i j := by
  have h := congrFun (congrFun (Comodule.toMatrix_endOfPoint (Pi.basisFun R (Fin n)) g.ofConv) i) j
  rw [toMatrix_endOfPoint_standardComodule, Matrix.map_apply] at h
  exact h.symm

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
  have h := congrFun (congrFun (Comodule.toMatrix_endOfPoint (Pi.basisFun R (Fin n))
    (g⁻¹).ofConv) i) j
  rw [toMatrix_endOfPoint_standardComodule, map_inv, Matrix.map_apply,
    Comodule.coefficientMatrix_apply] at h
  rw [h, ← WithConv.algHom_inv_apply]

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

variable (R n) in
/-- In `O(SLₙ)` the antipode of the coefficient matrix of the standard comodule is its adjugate:
the inverse of a determinant-one matrix. -/
private theorem map_antipode_coefficientMatrix :
    (Comodule.coefficientMatrix (C := coordinateHopfAlgebra R n) (Pi.basisFun R (Fin n))).map
        (HopfAlgebra.antipode R) =
      (Comodule.coefficientMatrix (C := coordinateHopfAlgebra R n)
        (Pi.basisFun R (Fin n))).adjugate := by
  -- Evaluate on the universal point, whose matrix is the coefficient matrix itself.
  let g : WithConv (coordinateHopfAlgebra R n →ₐ[R] coordinateHopfAlgebra R n) :=
    toConv (AlgHom.id R _)
  have hg : (pointsMulEquiv (R := R) (A := coordinateHopfAlgebra R n) n g :
      Matrix (Fin n) (Fin n) _) =
      Comodule.coefficientMatrix (C := coordinateHopfAlgebra R n) (Pi.basisFun R (Fin n)) :=
    Matrix.ext fun i j ↦ (ofConv_coefficientMatrix g i j).symm
  ext i j
  rw [Matrix.map_apply]
  calc HopfAlgebra.antipode R
        (Comodule.coefficientMatrix (C := coordinateHopfAlgebra R n) (Pi.basisFun R (Fin n)) i j)
      = (g⁻¹).ofConv
          (Comodule.coefficientMatrix (C := coordinateHopfAlgebra R n)
            (Pi.basisFun R (Fin n)) i j) := (WithConv.algHom_inv_apply g _).symm
    _ = _ := ofConv_coefficientMatrix _ i j
    _ = _ := by rw [map_inv, Matrix.SpecialLinearGroup.coe_inv, hg]

variable (R) in
/-- The coordinate `c` of `SL₂` vanishes on the upper-triangular subgroup. -/
private theorem coordinateMap_coefficientMatrix_one_zero :
    (UpperTriangular.coordinateMap R 2).hom
        (Comodule.coefficientMatrix (C := coordinateHopfAlgebra R 2) (Pi.basisFun R (Fin 2)) 1 0) =
      0 := by
  -- Evaluate on the universal point of the upper-triangular subgroup.
  let u : HopfAlgebra.points (R := R) (H := UpperTriangular.coordinateHopfAlgebra R 2)
      (CommAlgCat.of R (UpperTriangular.coordinateHopfAlgebra R 2)) := toConv (AlgHom.id R _)
  have h := ofConv_coefficientMatrix (CommHopfAlgCat.quotientPointsHom
    (coordinateHopfAlgebra R 2) (UpperTriangular.definingHopfIdeal R 2) _ u) 1 0
  rw [UpperTriangular.pointsMulEquiv_coe, CommHopfAlgCat.quotientPointsHom_apply, ofConv_toConv,
    AlgHom.comp_apply, AlgHom.id_apply, BialgHom.coe_toAlgHom] at h
  rw [h]
  exact UpperTriangularGroup.mem_comap_toGL_iff.mp
    (UpperTriangular.pointsMulEquiv R 2 (A := UpperTriangular.coordinateHopfAlgebra R 2) u).2
    (by decide : (0 : Fin 2) < 1)

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
  -- On the tensor factor `O(SL₂)`, restriction to the upper-triangular subgroup is multiplicative.
  have hq (z : MvPolynomial (Fin 2) R ⊗[R] coordinateHopfAlgebra R 2) :
      q.toLinearMap.lTensor (MvPolynomial (Fin 2) R) z =
        Algebra.TensorProduct.map (AlgHom.id R _) (q : _ →ₐ[R] _) z := by
    induction z using TensorProduct.inductionOn with
    | tmul x h => simp [BialgHom.toCoalgHom_apply]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hS := map_antipode_coefficientMatrix R 2
  rw [Matrix.adjugate_fin_two] at hS
  have hS₁₀ := congrFun (congrFun hS 1) 0
  have hS₁₁ := congrFun (congrFun hS 1) 1
  simp only [Matrix.map_apply, Matrix.of_apply, Matrix.cons_val_one, Matrix.cons_val_zero,
    Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one] at hS₁₀ hS₁₁
  rw [polynomialComodule, Comodule.polynomial_coact_apply, map_pow,
    Comodule.polynomialCoact_X, Fin.sum_univ_two, hq]
  simp only [← Comodule.coefficientMatrix_apply, hS₁₀, hS₁₁, map_pow, map_add,
    Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_neg, BialgHom.coe_toAlgHom, q]
  rw [coordinateMap_coefficientMatrix_one_zero, neg_zero, TensorProduct.tmul_zero, zero_add,
    Algebra.TensorProduct.tmul_pow]

end HighestLine

/-! ### Uniqueness of the highest line -/

section Uniqueness

open Polynomial

/-- A binary form of degree `d` over a domain that is semi-invariant under the universal
unipotent substitution `x ↦ x - t y` is a multiple of `y ^ d`. -/
private theorem mem_span_X_one_pow_of_aeval_eq_smul [IsDomain R] {d : ℕ}
    {f : MvPolynomial (Fin 2) R} (hf : f.IsHomogeneous d) (c : R[X])
    (h : MvPolynomial.aeval ![MvPolynomial.X 0 - MvPolynomial.C X * MvPolynomial.X 1,
      MvPolynomial.X 1] f = c • MvPolynomial.map (algebraMap R R[X]) f) :
    f ∈ R ∙ (MvPolynomial.X 1 ^ d : MvPolynomial (Fin 2) R) := by
  -- The dehomogenization `p = f(x, 1)` and the value `a = f(0, 1)`.
  set p : R[X] := MvPolynomial.aeval ![(X : R[X]), 1] f with hp
  set a : R := MvPolynomial.aeval ![(0 : R), 1] f with ha
  -- Evaluate the semi-invariance at `(x, y) = (t, 1)` and at `(x, y) = (0, 1)`.
  -- The two evaluations, as `R`-algebra homomorphisms out of `MvPolynomial (Fin 2) R[t]`.
  let ev₁ : MvPolynomial (Fin 2) R[X] →ₐ[R] R[X] :=
    (MvPolynomial.aeval (R := R[X]) ![X, 1]).restrictScalars R
  let ev₀ : MvPolynomial (Fin 2) R[X] →ₐ[R] R[X] :=
    (MvPolynomial.aeval (R := R[X]) ![0, 1]).restrictScalars R
  let σ : MvPolynomial (Fin 2) R →ₐ[R] MvPolynomial (Fin 2) R[X] := MvPolynomial.aeval
    ![MvPolynomial.X 0 - MvPolynomial.C X * MvPolynomial.X 1, MvPolynomial.X 1]
  let ι := MvPolynomial.mapAlgHom (σ := Fin 2) (Algebra.ofId R R[X])
  have k₁ : ev₁.comp σ = (Algebra.ofId R R[X]).comp (MvPolynomial.aeval ![(0 : R), 1]) :=
    MvPolynomial.algHom_ext fun i ↦ by fin_cases i <;> simp [ev₁, σ]
  have k₁' : ev₁.comp ι = MvPolynomial.aeval ![(X : R[X]), 1] :=
    MvPolynomial.algHom_ext fun i ↦ by fin_cases i <;> simp [ev₁, ι]
  have k₀ : ev₀.comp σ = MvPolynomial.aeval ![(-X : R[X]), 1] :=
    MvPolynomial.algHom_ext fun i ↦ by fin_cases i <;> simp [ev₀, σ]
  have k₀' : ev₀.comp ι = (Algebra.ofId R R[X]).comp (MvPolynomial.aeval ![(0 : R), 1]) :=
    MvPolynomial.algHom_ext fun i ↦ by fin_cases i <;> simp [ev₀, ι]
  have hι : ι f = MvPolynomial.map (algebraMap R R[X]) f := by simp [ι]
  have h1 : C a = c * p := by
    have e := congrArg (MvPolynomial.aeval (R := R[X]) ![(X : R[X]), 1]) h
    rw [map_smul, smul_eq_mul, ← hι] at e
    have eL := DFunLike.congr_fun k₁ f
    have eR := DFunLike.congr_fun k₁' f
    simp only [AlgHom.comp_apply] at eL eR
    rw [hp, ha, ← eR, ← Polynomial.algebraMap_eq, ← Algebra.ofId_apply, ← eL]
    exact e
  have h2 : aeval (-X) p = c * C a := by
    have e := congrArg (MvPolynomial.aeval (R := R[X]) ![(0 : R[X]), 1]) h
    rw [map_smul, smul_eq_mul, ← hι] at e
    have eL := DFunLike.congr_fun k₀ f
    have eR := DFunLike.congr_fun k₀' f
    simp only [AlgHom.comp_apply] at eL eR
    have hcomp : aeval (-X) p = MvPolynomial.aeval ![(-X : R[X]), 1] f := by
      rw [hp, MvPolynomial.comp_aeval_apply]
      refine congrArg (MvPolynomial.aeval · f) (funext fun i ↦ ?_)
      fin_cases i <;> simp
    rw [hcomp, ← eL, ha, ← Polynomial.algebraMap_eq, ← Algebra.ofId_apply, ← eR]
    exact e
  have hdeg : p.natDegree = 0 := by
    rcases eq_or_ne p 0 with hp0 | hp0
    · rw [hp0, natDegree_zero]
    rcases eq_or_ne c 0 with hc0 | hc0
    · rw [hc0, zero_mul, ← Polynomial.comp_eq_aeval, comp_eq_zero_iff] at h2
      rcases h2 with h2 | ⟨-, h2⟩
      · exact absurd h2 hp0
      · have := congrArg natDegree h2
        simp at this
    · have := congrArg natDegree h1
      rw [natDegree_C, natDegree_mul hc0 hp0] at this
      omega
  -- `f` is the homogenization of its dehomogenization `p`, which is constant.
  have hf' : f = MvPolynomial.C (p.coeff 0) * MvPolynomial.X 1 ^ d := by
    rw [← homogenize_C, ← eq_C_of_natDegree_eq_zero hdeg,
      homogenize_eq_of_isHomogeneous hf hp.symm]
  exact Submodule.mem_span_singleton.mpr ⟨p.coeff 0, by rw [hf', MvPolynomial.smul_eq_C_mul]⟩

/-- **`R yᵈ` is the unique line of binary forms of degree `d` stable under the upper-triangular
subgroup.** Over a domain, a binary form `f` of degree `d` spans a stable line, that is, its
coaction restricted to the upper-triangular subgroup is `f ⊗ h` for some function `h`, exactly
when `f` is a multiple of `yᵈ`. This holds in every characteristic. -/
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
          (UpperTriangular.coordinateMap R 2).hom.toLinearMap := by
        simp only [g, CommHopfAlgCat.quotientPointsHom_apply, ofConv_toConv,
          AlgHom.comp_toLinearMap]
        -- The quotient map has the same underlying linear map as an algebra homomorphism and as
        -- a bialgebra homomorphism (`BialgHom.toAlgHom_toLinearMap`).
        rfl
      rw [Comodule.endOfPoint_tmul, one_smul, hgB, LinearMap.lTensor_comp_apply, hfh,
        LinearMap.lTensor_tmul, TensorProduct.comm_tmul, TensorProduct.smul_tmul', smul_eq_mul,
        mul_one, AlgHom.toLinearMap_apply]
    have hpoly := congrArg (MvPolynomial.algebraTensorAlgEquiv R R[X]) key
    rw [algebraTensorAlgEquiv_endOfPoint_binaryForm g hg, map_smul,
      MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul] at hpoly
    simp only [map_one, one_mul, map_zero, zero_mul, sub_zero] at hpoly
    exact mem_span_X_one_pow_of_aeval_eq_smul (mem_binaryForms.mp hf) _ hpoly
  · obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hmem
    exact ⟨_, by rw [map_smul, map_smul, lTensor_coact_X_one_pow, TensorProduct.smul_tmul']⟩

end Uniqueness

end TauCeti.SpecialLinear
