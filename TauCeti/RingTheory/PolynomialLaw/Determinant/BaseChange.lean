/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PolynomialLaw.Determinant.Comap
public import TauCeti.RingTheory.PolynomialLaw.BaseChange
public import TauCeti.RingTheory.TensorProduct.Maps
import TauCeti.LinearAlgebra.TensorProduct.ScalarExtension

/-!
# Scalar extension of Chenevier determinants

A determinant on an associative `A`-algebra `R` extends along a commutative
`A`-algebra `B` to a determinant of the same dimension on `B ⊗[A] R`.
On elements coming from `R`, its values, characteristic coefficients, trace and
characteristic polynomial are obtained by mapping their coefficients to `B`.
The equivalence `scalarExtensionEquiv` also identifies the determinants over
`B` on `B ⊗[A] R` with the homogeneous multiplicative laws over `A` from
`R` to `B`, with both sides of fixed degree `d`.

## References

* [G. Chenevier, *The p-adic analytic space of pseudocharacters of a profinite group and
  pseudorepresentations over arbitrary rings*, Remark 1.4 and §1.5](https://arxiv.org/abs/0809.0415)
-/

public section

noncomputable section

open TensorProduct Polynomial
open TauCeti.Algebra.TensorProduct
open _root_.Algebra.TensorProduct (scalarRestrictionInput scalarRestrictionInput_apply
  scalarRestrictionInput_tmul scalarRestrictionOutput scalarRestrictionOutput_apply
  scalarRestrictionOutput_tmul)

namespace TauCeti.Determinant

section Semiring

variable {A : Type*} [CommSemiring A] {R : Type*} [Semiring R] [Algebra A R]
  {d : ℕ} (D : Determinant A R d) (B : Type*) [CommSemiring B] [Algebra A B]

/-- A homogeneous multiplicative law over `A` valued in the coefficient algebra `B`
gives a determinant over `B` on the scalar-extended source. -/
def ofPolynomialLaw (f : R →ₚₗ[A] B) (hf : f.IsHomogeneousOfDegree d)
    (hm : f.IsMultiplicative) : Determinant B (B ⊗[A] R) d where
  toLaw := (Algebra.TensorProduct.mulLeft : B ⊗[A] B →ₐ[B] B).toLinearMap.toPolynomialLaw.comp
    (f.baseChange B)
  isHomogeneousOfDegree := by
    let μ : B ⊗[A] B →ₐ[B] B := Algebra.TensorProduct.mulLeft
    simpa using μ.toLinearMap.isHomogeneousOfDegree_toPolynomialLaw.comp (hf.baseChange B)
  isMultiplicative :=
    (Algebra.TensorProduct.mulLeft : B ⊗[A] B →ₐ[B] B).isMultiplicative_toPolynomialLaw.comp
      (hm.baseChange B)

/-- The extended determinant evaluates a law with values in `B` using the structural
map from `B` to the test algebra. -/
theorem rid_toFun_ofPolynomialLaw (f : R →ₚₗ[A] B) (hf : f.IsHomogeneousOfDegree d)
    (hm : f.IsMultiplicative) (S : Type*) [CommSemiring S] [Algebra B S]
    [Algebra A S] [IsScalarTower A B S] (x : S ⊗[B] (B ⊗[A] R)) :
    Algebra.TensorProduct.rid B S S ((ofPolynomialLaw B f hf hm).toLaw.toFun S x) =
      Algebra.TensorProduct.mulRight (f.toFun S (baseChangeTowerAlgEquiv A B R S x)) := by
  rw [ofPolynomialLaw, PolynomialLaw.toFun_comp_apply, LinearMap.toPolynomialLaw_toFun,
    LinearMap.baseChange_eq_lTensor, PolynomialLaw.baseChange_toFun]
  simp only [← AlgEquiv.toLinearEquiv_apply (e := baseChangeTowerAlgEquiv A B R S),
    baseChangeTowerAlgEquiv_toLinearEquiv]
  rw [AlgebraTensorModule.cancelBaseChange_apply_eq]
  have h (y : S ⊗[A] B) :
      Algebra.TensorProduct.rid B S S
          ((Algebra.TensorProduct.mulLeft : B ⊗[A] B →ₐ[B] B).toLinearMap.lTensor S
            ((AlgebraTensorModule.cancelBaseChange A B B S B).symm y)) =
        Algebra.TensorProduct.mulRight y := by
    induction y using TensorProduct.inductionOn with
    | tmul s b =>
      simp [Algebra.smul_def, mul_comm]
    | add x y hx hy => simp [hx, hy]
  exact h _

/-- Extend the coefficient ring of a determinant along `A → B`. -/
def baseChange : Determinant B (B ⊗[A] R) d :=
  ofPolynomialLaw B ((Algebra.ofId A B).toLinearMap.toPolynomialLaw.comp D.toLaw)
    (by
      simpa using (Algebra.ofId A B).toLinearMap.isHomogeneousOfDegree_toPolynomialLaw.comp
        D.isHomogeneousOfDegree)
    ((Algebra.ofId A B).isMultiplicative_toPolynomialLaw.comp D.isMultiplicative)

/-- The scalar-extended determinant at a further coefficient algebra is the original
determinant evaluated at that algebra, under tensor cancellation. -/
theorem rid_toFun_baseChange (S : Type*) [CommSemiring S] [Algebra B S]
    [Algebra A S] [IsScalarTower A B S] (x : S ⊗[B] (B ⊗[A] R)) :
    Algebra.TensorProduct.rid B S S ((D.baseChange B).toLaw.toFun S x) =
      Algebra.TensorProduct.rid A S S (D.toLaw.toFun S (baseChangeTowerAlgEquiv A B R S x)) := by
  rw [baseChange, rid_toFun_ofPolynomialLaw, PolynomialLaw.toFun_comp_apply,
    LinearMap.toPolynomialLaw_toFun, LinearMap.baseChange_eq_lTensor,
    AlgHom.lTensor_toLinearMap_apply]
  have h (y : S ⊗[A] A) :
      Algebra.TensorProduct.mulRight
        (Algebra.TensorProduct.map (AlgHom.id A S) (Algebra.ofId A B) y) =
      Algebra.TensorProduct.rid A S S y := by
    induction y using TensorProduct.inductionOn with
    | tmul s a =>
      simp [Algebra.smul_def, IsScalarTower.algebraMap_apply A B S, mul_comm]
    | add y z hy hz => simp [hy, hz]
  exact h _

/-- At the extended coefficient ring, evaluate the original law and remove the scalar tensor
factor in its output. -/
theorem baseChange_apply (x : B ⊗[A] R) :
    D.baseChange B x = Algebra.TensorProduct.rid A B B (D.toLaw.toFun B x) := by
  rw [apply_eq_lid_toFun, TensorProduct.lid_eq_rid, ← Algebra.TensorProduct.coe_rid B B B,
    rid_toFun_baseChange]
  congr 2
  suffices h : (baseChangeTowerAlgEquiv A B R B).toLinearEquiv =
      TensorProduct.lid B (B ⊗[A] R) from DFunLike.congr_fun h (1 ⊗ₜ x) |>.trans (by simp)
  rw [baseChangeTowerAlgEquiv_toLinearEquiv, AlgebraTensorModule.cancelBaseChange_self_eq_lid]

/-- On an element of the original algebra, base change maps the determinant value to `B`. -/
@[simp]
theorem baseChange_apply_one_tmul (x : R) :
    D.baseChange B (1 ⊗ₜ x) = algebraMap A B (D x) := by
  rw [baseChange_apply, ← D.ground_toLaw, ← D.toLaw.one_tmul_ground B]
  simp [Algebra.algebraMap_eq_smul_one]

/-- The characteristic coefficients commute with change of scalars on original elements. -/
@[simp]
theorem charCoeff_baseChange_one_tmul (i : ℕ) (x : R) :
    (D.baseChange B).charCoeff i (1 ⊗ₜ x) = algebraMap A B (D.charCoeff i x) := by
  rcases lt_or_ge d i with hi | hi
  · simp [charCoeff_eq_zero _ hi]
  have h :
      Algebra.TensorProduct.rid B B B[X]
          ((D.baseChange B).toLaw.toFun B[X] (1 ⊗ₜ (1 ⊗ₜ x) + X ⊗ₜ 1)) =
        (Algebra.TensorProduct.rid A A A[X]
          (D.toLaw.toFun A[X] (1 ⊗ₜ x + X ⊗ₜ 1))).map (algebraMap A B) := by
    let φ : A[X] →ₐ[A] B[X] := Polynomial.mapAlgHom (Algebra.ofId A B)
    have hout (y : A[X] ⊗[A] A) :
        Algebra.TensorProduct.rid A B[X] B[X] (φ.toLinearMap.rTensor A y) =
          (Algebra.TensorProduct.rid A A[X] A[X] y).map (algebraMap A B) := by
      induction y using TensorProduct.inductionOn with
      | tmul p a =>
        simp [φ, Algebra.smul_def, IsScalarTower.algebraMap_apply A B B[X]]
      | add y z hy hz => simp [hy, hz]
    rw [Algebra.TensorProduct.coe_rid, ← Algebra.TensorProduct.coe_rid B B[X] B[X],
      rid_toFun_baseChange]
    have hn := congrArg (Algebra.TensorProduct.rid A B[X] B[X])
      (D.toLaw.isCompat_apply φ (1 ⊗ₜ x + X ⊗ₜ 1))
    rw [hout] at hn
    simpa [φ, Algebra.TensorProduct.one_def, Algebra.TensorProduct.coe_rid] using hn.symm
  simpa only [Polynomial.coeff_map, coeff_rid_toFun_one_tmul_add_X_tmul_one _ hi] using
    congrArg (fun p : B[X] ↦ p.coeff (d - i)) h

/-- The trace commutes with change of scalars on original elements. -/
@[simp]
theorem trace_baseChange_one_tmul (x : R) :
    (D.baseChange B).trace (1 ⊗ₜ x) = algebraMap A B (D.trace x) := by
  simp [trace_apply]

/-- Extending scalars to the original coefficient ring is restriction along the left unitor. -/
theorem baseChange_self :
    D.baseChange A = D.comap (Algebra.TensorProduct.lid A R).toAlgHom := by
  ext S _ _ x
  simp only [PolynomialLaw.toFun'_eq_toFun, comap_toFun]
  apply (Algebra.TensorProduct.rid A S S).injective
  rw [rid_toFun_baseChange]
  congr 2
  exact AlgHom.congr_fun (baseChangeTowerAlgEquiv_self A R S) x

/-- Extending along a tower of coefficient rings agrees with extending in one step,
under the canonical identification of the scalar-extended algebras. -/
theorem baseChange_baseChange (C : Type*) [CommSemiring C] [Algebra A C] [Algebra B C]
    [IsScalarTower A B C] :
    (D.baseChange B).baseChange C =
      (D.baseChange C).comap (baseChangeTowerAlgEquiv A B R C).toAlgHom := by
  ext S _ _ x
  let : Algebra B S := Algebra.compHom S (algebraMap B C)
  let : Algebra A S := Algebra.compHom S (algebraMap A C)
  let : IsScalarTower B C S := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower A C S := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower A B S := IsScalarTower.of_algebraMap_eq fun a ↦ calc
    algebraMap A S a = algebraMap C S (algebraMap A C a) := rfl
    _ = algebraMap C S (algebraMap B C (algebraMap A B a)) := by
      rw [IsScalarTower.algebraMap_apply A B C]
    _ = _ := rfl
  simp only [PolynomialLaw.toFun'_eq_toFun, comap_toFun]
  apply (Algebra.TensorProduct.rid C S S).injective
  rw [rid_toFun_baseChange (D.baseChange B) C, rid_toFun_baseChange D B,
    rid_toFun_baseChange D C]
  congr 2
  exact AlgHom.congr_fun (baseChangeTowerAlgEquiv_comp A B R C S) x

end Semiring

section CoefficientAlgebra

universe u

variable {A : Type u} [CommSemiring A] {R : Type*} [Semiring R] [Algebra A R]
  {d : ℕ} (B : Type*) [CommSemiring B] [Algebra A B]

private def restrictedComponent (D : Determinant B (B ⊗[A] R) d)
    (S : Type*) [CommSemiring S] [Algebra A S] (x : S ⊗[A] R) :=
  scalarRestrictionOutput B S (D.toLaw.toFun (B ⊗[A] S) (scalarRestrictionInput B S x))

private theorem restrictedComponent_natural (D : Determinant B (B ⊗[A] R) d)
    {S T : Type*} [CommSemiring S] [Algebra A S] [CommSemiring T] [Algebra A T]
    (φ : S →ₐ[A] T) (x : S ⊗[A] R) :
    φ.toLinearMap.rTensor B (restrictedComponent B D S x) =
      restrictedComponent B D T (φ.toLinearMap.rTensor R x) := by
  let ψ := Algebra.TensorProduct.map (AlgHom.id B B) φ
  have hin (x : S ⊗[A] R) :
      ψ.toLinearMap.rTensor (B ⊗[A] R) (scalarRestrictionInput B S x) =
        scalarRestrictionInput B T (φ.toLinearMap.rTensor R x) := by
    apply (baseChangeTowerAlgEquiv A B R (B ⊗[A] T)).injective
    rw [← AlgEquiv.toLinearEquiv_apply, baseChangeTowerAlgEquiv_toLinearEquiv,
      ← AlgebraTensorModule.cancelBaseChange_apply_eq,
      AlgebraTensorModule.cancelBaseChange_rTensor, AlgebraTensorModule.cancelBaseChange_apply_eq]
    simp only [scalarRestrictionInput_apply]
    rw [← baseChangeTowerAlgEquiv_toLinearEquiv, AlgEquiv.toLinearEquiv_apply,
      AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
    rw [← AlgHom.rTensor_toLinearMap_apply, ← LinearMap.rTensor_comp_apply,
      ← AlgHom.toLinearMap_restrictScalars,
      ← AlgHom.comp_toLinearMap, ← AlgHom.rTensor_toLinearMap_apply,
      ← LinearMap.rTensor_comp_apply, ← AlgHom.comp_toLinearMap]
    congr 2
  have hout (y : (B ⊗[A] S) ⊗[B] B) :
      φ.toLinearMap.rTensor B (scalarRestrictionOutput B S y) =
        scalarRestrictionOutput B T (ψ.toLinearMap.rTensor B y) := by
    induction y using TensorProduct.inductionOn with
    | add y z hy hz => simp [hy, hz]
    | tmul z c =>
      induction z using TensorProduct.inductionOn with
      | tmul b s => simp [scalarRestrictionOutput_tmul, ψ]
      | add x y hx hy => simp only [add_tmul, map_add, hx, hy]
  simp only [restrictedComponent, hout, D.toLaw.isCompat_apply, hin]

/-- Regard a determinant on `B ⊗[A] R` as an `A`-polynomial law on `R` valued in `B`.
Its component at `S` evaluates the determinant at the `B`-algebra `B ⊗[A] S`. -/
def restrictLaw (D : Determinant B (B ⊗[A] R) d) : R →ₚₗ[A] B where
  toFun' S _ _ x := restrictedComponent B D S x
  isCompat' φ := funext (restrictedComponent_natural B D φ)

/-- To evaluate a restricted determinant law at `S`, insert `S` into `B ⊗[A] S`, evaluate
the determinant there, and swap the scalar factors in the output. -/
theorem restrictLaw_toFun' (D : Determinant B (B ⊗[A] R) d) (S : Type u)
    [CommSemiring S] [Algebra A S] (x : S ⊗[A] R) :
    (D.restrictLaw B).toFun' S x =
      Algebra.TensorProduct.comm A B S
        (Algebra.TensorProduct.rid B B (B ⊗[A] S)
          (D.toLaw.toFun (B ⊗[A] S)
            ((baseChangeTowerAlgEquiv A B R (B ⊗[A] S)).symm
              (Algebra.TensorProduct.map Algebra.TensorProduct.includeRight
                (AlgHom.id A R) x)))) := by
  simp only [restrictLaw, restrictedComponent, scalarRestrictionInput_apply,
    scalarRestrictionOutput_apply]

/-- The restriction formula holds at test algebras in any universe. -/
theorem restrictLaw_toFun (D : Determinant B (B ⊗[A] R) d) (S : Type*)
    [CommSemiring S] [Algebra A S] (x : S ⊗[A] R) :
    (D.restrictLaw B).toFun S x =
      scalarRestrictionOutput B S (D.toLaw.toFun (B ⊗[A] S) (scalarRestrictionInput B S x)) := by
  obtain ⟨k, φ, p, rfl⟩ := PolynomialLaw.exists_lift x
  rw [← PolynomialLaw.isCompat_apply, ← PolynomialLaw.toFun'_eq_toFun]
  exact restrictedComponent_natural B D φ p

/-- Restricting the base of a determinant law preserves its degree. -/
theorem isHomogeneousOfDegree_restrictLaw (D : Determinant B (B ⊗[A] R) d) :
    (D.restrictLaw B).IsHomogeneousOfDegree d := by
  rw [PolynomialLaw.isHomogeneousOfDegree_iff]
  intro S _ _ s x
  let ι : S →ₐ[A] B ⊗[A] S := Algebra.TensorProduct.includeRight
  have hin :
      scalarRestrictionInput B S (s • x) = ι s • scalarRestrictionInput B S x := by
    induction x using TensorProduct.inductionOn with
    | tmul t r =>
      simp [smul_tmul', scalarRestrictionInput_tmul, ι, Algebra.smul_def,
        Algebra.TensorProduct.tmul_mul_tmul]
    | add y z hy hz => simp [smul_add, hy, hz]
  have hout (y : (B ⊗[A] S) ⊗[B] B) :
      scalarRestrictionOutput B S (ι s ^ d • y) = s ^ d • scalarRestrictionOutput B S y := by
    induction y using TensorProduct.inductionOn with
    | add y z hy hz => simp [smul_add, hy, hz]
    | tmul z c =>
      induction z using TensorProduct.inductionOn with
      | tmul b t =>
        rw [← map_pow]
        simp [smul_tmul', scalarRestrictionOutput_tmul, ι, Algebra.smul_def,
          Algebra.TensorProduct.tmul_mul_tmul]
      | add y z hy hz => simp only [smul_add, add_tmul, map_add, hy, hz]
  simp only [restrictLaw, restrictedComponent, hin, D.isHomogeneousOfDegree.toFun_smul, hout]

/-- Restricting the base of a determinant law preserves the unit and multiplication. -/
theorem isMultiplicative_restrictLaw (D : Determinant B (B ⊗[A] R) d) :
    (D.restrictLaw B).IsMultiplicative where
  toFun'_one S _ _ := by
    let g := scalarRestrictionInput (A := A) (R := R) B S
    let h := scalarRestrictionOutput (A := A) B S
    calc
      h (D.toLaw.toFun (B ⊗[A] S) (g 1)) = h (D.toLaw.toFun (B ⊗[A] S) 1) :=
        congrArg (fun y ↦ h (D.toLaw.toFun (B ⊗[A] S) y)) g.map_one
      _ = h 1 := congrArg h (D.isMultiplicative.toFun_one (B ⊗[A] S))
      _ = 1 := h.map_one
  toFun'_mul {S} _ _ x y := by
    let g := scalarRestrictionInput (A := A) (R := R) B S
    let h := scalarRestrictionOutput (A := A) B S
    let f := D.toLaw.toFun (B ⊗[A] S)
    calc
      h (f (g (x * y))) = h (f (g x * g y)) := congrArg (h ∘ f) (g.map_mul x y)
      _ = h (f (g x) * f (g y)) := congrArg h (D.isMultiplicative.toFun_mul (g x) (g y))
      _ = h (f (g x)) * h (f (g y)) := h.map_mul _ _

/-- Changing the base of a law valued in `B` and restricting it recovers the original law. -/
@[simp]
theorem restrictLaw_ofPolynomialLaw (f : R →ₚₗ[A] B) (hf : f.IsHomogeneousOfDegree d)
    (hm : f.IsMultiplicative) : (ofPolynomialLaw B f hf hm).restrictLaw B = f := by
  ext S _ _ x
  let ι : S →ₐ[A] B ⊗[A] S := Algebra.TensorProduct.includeRight
  have hin :
      baseChangeTowerAlgEquiv A B R (B ⊗[A] S) (scalarRestrictionInput B S x) =
        ι.toLinearMap.rTensor R x := by
    rw [AlgHom.rTensor_toLinearMap_apply]
    simp [scalarRestrictionInput_apply, ι]
  have hout (y : S ⊗[A] B) :
      Algebra.TensorProduct.comm A B S
          (Algebra.TensorProduct.mulRight (ι.toLinearMap.rTensor B y)) = y := by
    induction y using TensorProduct.inductionOn with
    | tmul s b =>
      simp [ι, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]
    | add y z hy hz => simp [hy, hz]
  rw [PolynomialLaw.toFun'_eq_toFun f]
  simp only [restrictLaw, restrictedComponent, scalarRestrictionOutput_apply]
  rw [Algebra.TensorProduct.coe_rid, ← Algebra.TensorProduct.coe_rid B (B ⊗[A] S) (B ⊗[A] S),
    rid_toFun_ofPolynomialLaw, hin, ← f.isCompat_apply, hout]

/-- Restriction of the extended determinant law is postcomposition with the coefficient map. -/
@[simp]
theorem restrictLaw_baseChange (D : Determinant A R d) :
    (D.baseChange B).restrictLaw B =
      (Algebra.ofId A B).toLinearMap.toPolynomialLaw.comp D.toLaw := by
  rw [baseChange, restrictLaw_ofPolynomialLaw]

end CoefficientAlgebra

section Equivalence

universe u

variable {A : Type u} [CommSemiring A] {R : Type*} [Semiring R] [Algebra A R]
  {d : ℕ} (B : Type*) [CommSemiring B] [Algebra A B]

/-- Extending the base of the restricted law recovers the determinant over `B`. -/
@[simp]
theorem ofPolynomialLaw_restrictLaw (D : Determinant B (B ⊗[A] R) d) :
    ofPolynomialLaw B (D.restrictLaw B) (isHomogeneousOfDegree_restrictLaw B D)
      (isMultiplicative_restrictLaw B D) = D := by
  ext S _ _ x
  let : Algebra A S := Algebra.compHom S (algebraMap A B)
  let : IsScalarTower A B S := IsScalarTower.of_algebraMap_eq' rfl
  let μ : B ⊗[A] S →ₐ[B] S := Algebra.TensorProduct.mulLeft
  have hin (y : S ⊗[A] R) :
      μ.toLinearMap.rTensor (B ⊗[A] R) (scalarRestrictionInput B S y) =
        (baseChangeTowerAlgEquiv A B R S).symm y := by
    apply (baseChangeTowerAlgEquiv A B R S).injective
    rw [← AlgEquiv.toLinearEquiv_apply, baseChangeTowerAlgEquiv_toLinearEquiv,
      ← AlgebraTensorModule.cancelBaseChange_apply_eq,
      AlgebraTensorModule.cancelBaseChange_rTensor, AlgebraTensorModule.cancelBaseChange_apply_eq,
      ← baseChangeTowerAlgEquiv_toLinearEquiv, AlgEquiv.toLinearEquiv_apply,
      scalarRestrictionInput_apply, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
    rw [← AlgHom.rTensor_toLinearMap_apply, ← LinearMap.rTensor_comp_apply,
      ← AlgHom.toLinearMap_restrictScalars,
      ← AlgHom.comp_toLinearMap]
    have hμ : (μ.restrictScalars A).comp Algebra.TensorProduct.includeRight = AlgHom.id A S := by
      ext s
      simp [μ]
    rw [hμ]
    simp
  have hout (y : (B ⊗[A] S) ⊗[B] B) :
      Algebra.TensorProduct.mulRight (scalarRestrictionOutput B S y) =
        Algebra.TensorProduct.rid B S S (μ.toLinearMap.rTensor B y) := by
    induction y using TensorProduct.inductionOn with
    | add y z hy hz => simp [hy, hz]
    | tmul z c =>
      induction z using TensorProduct.inductionOn with
      | tmul b s =>
        simp [scalarRestrictionOutput_tmul, μ, Algebra.smul_def]
        ac_rfl
      | add z w hz hw => simp only [add_tmul, map_add, hz, hw]
  simp only [PolynomialLaw.toFun'_eq_toFun]
  apply (Algebra.TensorProduct.rid B S S).injective
  rw [rid_toFun_ofPolynomialLaw, restrictLaw_toFun]
  simp only [hout, D.toLaw.isCompat_apply, hin, AlgEquiv.symm_apply_apply]

/-- Homogeneous multiplicative laws of fixed degree `d` over `A` with values in `B`
are equivalent to degree-`d` determinants on the scalar-extended algebra over `B`. -/
def scalarExtensionEquiv :
    {f : R →ₚₗ[A] B // f.IsHomogeneousOfDegree d ∧ f.IsMultiplicative} ≃
      Determinant B (B ⊗[A] R) d where
  toFun f := ofPolynomialLaw B f.val f.property.left f.property.right
  invFun D := ⟨D.restrictLaw B, isHomogeneousOfDegree_restrictLaw B D,
    isMultiplicative_restrictLaw B D⟩
  left_inv f := Subtype.ext (restrictLaw_ofPolynomialLaw B f.val f.property.left f.property.right)
  right_inv := ofPolynomialLaw_restrictLaw B

/-- The equivalence extends the base of a homogeneous multiplicative law of degree `d`. -/
@[simp]
theorem scalarExtensionEquiv_apply
    (f : {f : R →ₚₗ[A] B // f.IsHomogeneousOfDegree d ∧ f.IsMultiplicative}) :
    scalarExtensionEquiv B f = ofPolynomialLaw B f.val f.property.left f.property.right :=
  (rfl)

/-- The scalar-extension equivalence is natural in the coefficient algebra: postcomposing
with the coefficient map corresponds to base-changing the determinant under tensor cancellation. -/
theorem scalarExtensionEquiv_baseChange (C : Type*) [CommSemiring C] [Algebra A C]
    [Algebra B C] [IsScalarTower A B C]
    (f : {f : R →ₚₗ[A] B // f.IsHomogeneousOfDegree d ∧ f.IsMultiplicative}) :
    (scalarExtensionEquiv B f).baseChange C =
      (scalarExtensionEquiv (d := d) C
        ⟨(IsScalarTower.toAlgHom A B C).toLinearMap.toPolynomialLaw.comp f.val,
          by
            simpa using
              (IsScalarTower.toAlgHom A B C).toLinearMap.isHomogeneousOfDegree_toPolynomialLaw.comp
                f.property.left,
          (IsScalarTower.toAlgHom A B C).isMultiplicative_toPolynomialLaw.comp
            f.property.right⟩).comap (baseChangeTowerAlgEquiv A B R C).toAlgHom := by
  ext S _ _ x
  let : Algebra B S := Algebra.compHom S (algebraMap B C)
  let : Algebra A S := Algebra.compHom S (algebraMap A C)
  let : IsScalarTower B C S := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower A C S := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower A B S := IsScalarTower.of_algebraMap_eq fun a ↦ calc
    algebraMap A S a = algebraMap C S (algebraMap A C a) := rfl
    _ = algebraMap C S (algebraMap B C (algebraMap A B a)) := by
      rw [IsScalarTower.algebraMap_apply A B C]
    _ = _ := rfl
  simp only [PolynomialLaw.toFun'_eq_toFun, scalarExtensionEquiv_apply, comap_toFun]
  apply (Algebra.TensorProduct.rid C S S).injective
  rw [rid_toFun_baseChange, rid_toFun_ofPolynomialLaw, rid_toFun_ofPolynomialLaw,
    PolynomialLaw.toFun_comp_apply, LinearMap.toPolynomialLaw_toFun,
    LinearMap.baseChange_eq_lTensor, AlgHom.lTensor_toLinearMap_apply]
  have hout (y : S ⊗[A] B) :
      Algebra.TensorProduct.mulRight
          (Algebra.TensorProduct.map (AlgHom.id A S) (IsScalarTower.toAlgHom A B C) y) =
        Algebra.TensorProduct.mulRight y := by
    induction y using TensorProduct.inductionOn with
    | tmul s b => simp [IsScalarTower.algebraMap_apply B C S]
    | add y z hy hz => simp [hy, hz]
  rw [hout]
  congr 2
  exact AlgHom.congr_fun (baseChangeTowerAlgEquiv_comp A B R C S) x

/-- The inverse equivalence restricts the base of the degree-`d` determinant law. -/
@[simp]
theorem val_scalarExtensionEquiv_symm_apply (D : Determinant B (B ⊗[A] R) d) :
    ((scalarExtensionEquiv B).symm D).val = D.restrictLaw B :=
  (rfl)

end Equivalence

section Ring

variable {A : Type*} [CommRing A] {R : Type*} [Semiring R] [Algebra A R]
  {d : ℕ} (D : Determinant A R d) (B : Type*) [CommRing B] [Algebra A B]

/-- The characteristic polynomial of an original element maps coefficientwise under
base change. -/
@[simp]
theorem charpoly_baseChange_one_tmul (x : R) :
    (D.baseChange B).charpoly (1 ⊗ₜ x) = (D.charpoly x).map (algebraMap A B) := by
  simp [charpoly_eq_sum, Polynomial.map_sum]

/-- Extending the determinant of a matrix representation gives the determinant of the
scalar-extended representation. -/
@[simp]
theorem baseChange_algHomDet {n : Type*} [Fintype n] [DecidableEq n]
    (ρ : R →ₐ[A] Matrix n n A) :
    (algHomDet ρ).baseChange B = algHomDet
      ((Algebra.matrixBaseChangeAlgEquiv A B n).toAlgHom.comp
        (Algebra.TensorProduct.map (AlgHom.id B B) ρ)) := by
  ext S _ _ x
  let : CommRing S := (algebraMap B S).commSemiringToCommRing
  let : Algebra A S := Algebra.compHom S (algebraMap A B)
  let : IsScalarTower A B S := IsScalarTower.of_algebraMap_eq' rfl
  simp only [PolynomialLaw.toFun'_eq_toFun]
  apply (Algebra.TensorProduct.rid B S S).injective
  rw [rid_toFun_baseChange, algHomDet_toFun, algHomDet_toFun,
    Algebra.TensorProduct.rid_tmul, Algebra.TensorProduct.rid_tmul, one_smul, one_smul]
  congr 1
  exact AlgHom.congr_fun (Algebra.matrixBaseChangeAlgEquiv_comp_tower A B R S n ρ) x

end Ring

end TauCeti.Determinant
