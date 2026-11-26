/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PolynomialLaw.Determinant.Comap
public import TauCeti.RingTheory.PolynomialLaw.BaseChange
public import TauCeti.Algebra.TensorProduct.BaseChange
public import TauCeti.RingTheory.TensorProduct.Maps

/-!
# Scalar extension of Chenevier determinants

A determinant on an associative `A`-algebra `R` extends along a commutative
`A`-algebra `B` to a determinant of the same dimension on `B ⊗[A] R`.
On elements coming from `R`, its values, characteristic coefficients, trace and
characteristic polynomial are obtained by mapping their coefficients to `B`.
The equivalence `scalarExtensionEquiv` also identifies the determinants over
`B` on `B ⊗[A] R` with the homogeneous multiplicative laws over `A` from
`R` to `B`.

## References

* [G. Chenevier, *The p-adic analytic space of pseudocharacters of a profinite group and
  pseudorepresentations over arbitrary rings*, Remark 1.4 and §1.5](https://arxiv.org/abs/0809.0415)
-/

public section

noncomputable section

open TensorProduct Polynomial
open TauCeti.Algebra.TensorProduct

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
    rw [Algebra.TensorProduct.coe_rid, ← Algebra.TensorProduct.coe_rid B B[X] B[X],
      rid_toFun_baseChange, map_add, baseChangeTowerAlgEquiv_tmul, one_smul,
      Algebra.TensorProduct.one_def, baseChangeTowerAlgEquiv_tmul, one_smul,
      D.toFun_tmul_add_tmul_one, map_sum, rid_toFun_one_tmul_add_X_tmul_one, Polynomial.map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp only [one_pow, one_mul, Algebra.TensorProduct.rid_tmul, Algebra.smul_def,
      IsScalarTower.algebraMap_apply A B B[X], Polynomial.map_mul, Polynomial.map_C,
      Polynomial.map_pow, Polynomial.map_X]
    rfl
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
  suffices h :
      (baseChangeTowerAlgEquiv A A R S).toAlgHom.restrictScalars A =
        Algebra.TensorProduct.map (AlgHom.id A S) (Algebra.TensorProduct.lid A R).toAlgHom
    from AlgHom.congr_fun h x
  apply Algebra.TensorProduct.ext'
  intro s y
  induction y using TensorProduct.inductionOn with
  | tmul a r => simp [tmul_smul, smul_tmul']
  | add y z hy hz => simp only [tmul_add, map_add, hy, hz]

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
  suffices h :
      ((baseChangeTowerAlgEquiv A B R S).toAlgHom.comp
        (baseChangeTowerAlgEquiv B C (B ⊗[A] R) S).toAlgHom).restrictScalars C =
      ((baseChangeTowerAlgEquiv A C R S).toAlgHom.restrictScalars C).comp
        (Algebra.TensorProduct.map (AlgHom.id C S) (baseChangeTowerAlgEquiv A B R C).toAlgHom)
    from AlgHom.congr_fun h x
  refine Algebra.TensorProduct.ext' fun s y ↦ ?_
  induction y using TensorProduct.inductionOn with
  | add y z hy hz => simp only [tmul_add, map_add, hy, hz]
  | tmul c z =>
    induction z using TensorProduct.inductionOn with
    | tmul b r =>
      simp only [AlgHom.restrictScalars_apply, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
        baseChangeTowerAlgEquiv_tmul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        Algebra.smul_def, IsScalarTower.algebraMap_apply B C S]
      exact congrArg (fun t : S ↦ t ⊗ₜ[A] r) (by rw [(algebraMap C S).map_mul, mul_assoc])
    | add y z hy hz => simp only [tmul_add, map_add, hy, hz]

end Semiring

section CoefficientAlgebra

universe u

variable {A : Type u} [CommSemiring A] {R : Type*} [Semiring R] [Algebra A R]
  {d : ℕ} (B : Type*) [CommSemiring B] [Algebra A B]

private def restrictLawInput (S : Type*) [CommSemiring S] [Algebra A S] :
    S ⊗[A] R →ₐ[A] (B ⊗[A] S) ⊗[B] (B ⊗[A] R) :=
  ((baseChangeTowerAlgEquiv A B R (B ⊗[A] S)).symm.toAlgHom.restrictScalars A).comp
    (Algebra.TensorProduct.map Algebra.TensorProduct.includeRight (AlgHom.id A R))

private theorem restrictLawInput_tmul {S : Type*} [CommSemiring S] [Algebra A S] (s : S) (r : R) :
    restrictLawInput (R := R) B S (s ⊗ₜ[A] r) = (1 ⊗ₜ[A] s) ⊗ₜ[B] (1 ⊗ₜ[A] r) := by
  simp [restrictLawInput]

private def restrictLawOutput (S : Type*) [CommSemiring S] [Algebra A S] :
    (B ⊗[A] S) ⊗[B] B →ₐ[A] S ⊗[A] B :=
  (Algebra.TensorProduct.comm A B S).toAlgHom.comp
    ((Algebra.TensorProduct.rid B B (B ⊗[A] S)).toAlgHom.restrictScalars A)

private theorem restrictLawOutput_tmul {S : Type*} [CommSemiring S] [Algebra A S]
    (b c : B) (s : S) :
    restrictLawOutput B S ((b ⊗ₜ[A] s) ⊗ₜ[B] c) = s ⊗ₜ[A] (c * b) := by
  simp [restrictLawOutput, smul_tmul', smul_eq_mul]

/-- Regard a determinant on `B ⊗[A] R` as an `A`-polynomial law on `R` valued in `B`.
Its component at `S` evaluates the determinant at the `B`-algebra `B ⊗[A] S`. -/
def restrictLaw (D : Determinant B (B ⊗[A] R) d) : R →ₚₗ[A] B where
  toFun' S _ _ x := restrictLawOutput B S
    (D.toLaw.toFun (B ⊗[A] S) (restrictLawInput B S x))
  isCompat' {S} _ _ {T} _ _ φ := by
    let ψ := Algebra.TensorProduct.map (AlgHom.id B B) φ
    have hin (x : S ⊗[A] R) :
        ψ.toLinearMap.rTensor (B ⊗[A] R) (restrictLawInput B S x) =
          restrictLawInput B T (φ.toLinearMap.rTensor R x) := by
      induction x using TensorProduct.inductionOn with
      | tmul s r => simp [restrictLawInput_tmul, ψ]
      | add x y hx hy => simp [hx, hy]
    have hout (y : (B ⊗[A] S) ⊗[B] B) :
        φ.toLinearMap.rTensor B (restrictLawOutput B S y) =
          restrictLawOutput B T (ψ.toLinearMap.rTensor B y) := by
      induction y using TensorProduct.inductionOn with
      | add y z hy hz => simp [hy, hz]
      | tmul z c =>
        induction z using TensorProduct.inductionOn with
        | tmul b s => simp [restrictLawOutput_tmul, ψ]
        | add x y hx hy => simp only [add_tmul, map_add, hx, hy]
    funext x
    simp only [Function.comp_apply, hout, D.toLaw.isCompat_apply, hin]

/-- To evaluate a restricted determinant law at `S`, insert `S` into `B ⊗[A] S`, evaluate
the determinant there, and swap the scalar factors in the output. -/
theorem restrictLaw_toFun' (D : Determinant B (B ⊗[A] R) d) (S : Type u)
    [CommSemiring S] [Algebra A S] (x : S ⊗[A] R) :
    (D.restrictLaw B).toFun' S x =
      Algebra.TensorProduct.comm A B S
        (Algebra.TensorProduct.rid B B (B ⊗[A] S)
          (D.toLaw.toFun (B ⊗[A] S)
            ((baseChangeTowerAlgEquiv A B R (B ⊗[A] S)).symm
              (Algebra.TensorProduct.map Algebra.TensorProduct.includeRight (AlgHom.id A R) x)))) :=
  (rfl)

/-- Restricting the base of a determinant law preserves its degree. -/
theorem isHomogeneousOfDegree_restrictLaw (D : Determinant B (B ⊗[A] R) d) :
    (D.restrictLaw B).IsHomogeneousOfDegree d := by
  rw [PolynomialLaw.isHomogeneousOfDegree_iff]
  intro S _ _ s x
  let ι : S →ₐ[A] B ⊗[A] S := Algebra.TensorProduct.includeRight
  have hin :
      restrictLawInput B S (s • x) = ι s • restrictLawInput B S x := by
    induction x using TensorProduct.inductionOn with
    | tmul t r =>
      simp [smul_tmul', restrictLawInput_tmul, ι, Algebra.smul_def,
        Algebra.TensorProduct.tmul_mul_tmul]
    | add y z hy hz => simp [smul_add, hy, hz]
  have hout (y : (B ⊗[A] S) ⊗[B] B) :
      restrictLawOutput B S (ι s ^ d • y) = s ^ d • restrictLawOutput B S y := by
    induction y using TensorProduct.inductionOn with
    | add y z hy hz => simp [smul_add, hy, hz]
    | tmul z c =>
      induction z using TensorProduct.inductionOn with
      | tmul b t =>
        rw [← map_pow]
        simp [smul_tmul', restrictLawOutput_tmul, ι, Algebra.smul_def,
          Algebra.TensorProduct.tmul_mul_tmul]
      | add y z hy hz => simp only [smul_add, add_tmul, map_add, hy, hz]
  simp only [restrictLaw, hin, D.isHomogeneousOfDegree.toFun_smul, hout]

/-- Restricting the base of a determinant law preserves the unit and multiplication. -/
theorem isMultiplicative_restrictLaw (D : Determinant B (B ⊗[A] R) d) :
    (D.restrictLaw B).IsMultiplicative where
  toFun'_one S _ _ := by
    let g := restrictLawInput (A := A) (R := R) B S
    let h := restrictLawOutput (A := A) B S
    calc
      h (D.toLaw.toFun (B ⊗[A] S) (g 1)) = h (D.toLaw.toFun (B ⊗[A] S) 1) :=
        congrArg (fun y ↦ h (D.toLaw.toFun (B ⊗[A] S) y)) g.map_one
      _ = h 1 := congrArg h (D.isMultiplicative.toFun_one (B ⊗[A] S))
      _ = 1 := h.map_one
  toFun'_mul {S} _ _ x y := by
    let g := restrictLawInput (A := A) (R := R) B S
    let h := restrictLawOutput (A := A) B S
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
      baseChangeTowerAlgEquiv A B R (B ⊗[A] S) (restrictLawInput B S x) =
        ι.toLinearMap.rTensor R x := by
    rw [AlgHom.rTensor_toLinearMap_apply]
    simp [restrictLawInput, ι]
  have hout (y : S ⊗[A] B) :
      Algebra.TensorProduct.comm A B S
          (Algebra.TensorProduct.mulRight (ι.toLinearMap.rTensor B y)) = y := by
    induction y using TensorProduct.inductionOn with
    | tmul s b =>
      simp [ι, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]
    | add y z hy hz => simp [hy, hz]
  rw [PolynomialLaw.toFun'_eq_toFun f]
  simp only [restrictLaw, restrictLawOutput, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    AlgHom.restrictScalars_apply]
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
  {d : ℕ} (B : Type u) [CommSemiring B] [Algebra A B]

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
      μ.toLinearMap.rTensor (B ⊗[A] R) (restrictLawInput B S y) =
        (baseChangeTowerAlgEquiv A B R S).symm y := by
    induction y using TensorProduct.inductionOn with
    | tmul s r => simp [restrictLawInput_tmul, μ]
    | add y z hy hz => simp [hy, hz]
  have hout (y : (B ⊗[A] S) ⊗[B] B) :
      Algebra.TensorProduct.mulRight (restrictLawOutput B S y) =
        Algebra.TensorProduct.rid B S S (μ.toLinearMap.rTensor B y) := by
    induction y using TensorProduct.inductionOn with
    | add y z hy hz => simp [hy, hz]
    | tmul z c =>
      induction z using TensorProduct.inductionOn with
      | tmul b s =>
        simp [restrictLawOutput_tmul, μ, Algebra.smul_def]
        ac_rfl
      | add z w hz hw => simp only [add_tmul, map_add, hz, hw]
  simp only [PolynomialLaw.toFun'_eq_toFun]
  apply (Algebra.TensorProduct.rid B S S).injective
  rw [rid_toFun_ofPolynomialLaw, ← PolynomialLaw.toFun'_eq_toFun (D.restrictLaw B)]
  simp only [restrictLaw, hout, D.toLaw.isCompat_apply, hin, AlgEquiv.symm_apply_apply]

/-- Homogeneous multiplicative laws over `A` with values in `B` are equivalent to
determinants on the scalar-extended algebra over `B`. -/
def scalarExtensionEquiv :
    {f : R →ₚₗ[A] B // f.IsHomogeneousOfDegree d ∧ f.IsMultiplicative} ≃
      Determinant B (B ⊗[A] R) d where
  toFun f := ofPolynomialLaw B f.val f.property.left f.property.right
  invFun D := ⟨D.restrictLaw B, isHomogeneousOfDegree_restrictLaw B D,
    isMultiplicative_restrictLaw B D⟩
  left_inv f := Subtype.ext (restrictLaw_ofPolynomialLaw B f.val f.property.left f.property.right)
  right_inv := ofPolynomialLaw_restrictLaw B

/-- The equivalence extends the base of a homogeneous multiplicative law. -/
@[simp]
theorem scalarExtensionEquiv_apply
    (f : {f : R →ₚₗ[A] B // f.IsHomogeneousOfDegree d ∧ f.IsMultiplicative}) :
    scalarExtensionEquiv B f = ofPolynomialLaw B f.val f.property.left f.property.right :=
  (rfl)

/-- The inverse equivalence restricts the base of the determinant law. -/
@[simp]
theorem coe_scalarExtensionEquiv_symm_apply (D : Determinant B (B ⊗[A] R) d) :
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
  suffices h :
      (Algebra.matrixBaseChangeAlgEquiv A S n).toAlgHom.comp
        ((Algebra.TensorProduct.map (AlgHom.id S S) ρ).comp
          (baseChangeTowerAlgEquiv A B R S).toAlgHom) =
      (Algebra.matrixBaseChangeAlgEquiv B S n).toAlgHom.comp
        (Algebra.TensorProduct.map (AlgHom.id S S)
          ((Algebra.matrixBaseChangeAlgEquiv A B n).toAlgHom.comp
            (Algebra.TensorProduct.map (AlgHom.id B B) ρ)))
    from AlgHom.congr_fun h x
  refine Algebra.TensorProduct.ext' fun s y ↦ ?_
  induction y using TensorProduct.inductionOn with
  | add y z hy hz => simp only [tmul_add, map_add, hy, hz]
  | tmul b r =>
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, baseChangeTowerAlgEquiv_tmul,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.matrixBaseChangeAlgEquiv_tmul]
    rw [Matrix.map_smulₛₗ (algebraMap B S) (algebraMap B S) b (fun z ↦ by
      simp)]
    ext i j
    simp only [Matrix.smul_apply, Matrix.map_apply]
    simp only [Algebra.smul_def, Algebra.algebraMap_self_apply,
      IsScalarTower.algebraMap_apply A B S]
    ac_rfl

end Ring

end TauCeti.Determinant
