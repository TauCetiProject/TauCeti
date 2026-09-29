/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.CrossedProduct.BrauerClass
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Tensor products of crossed-product algebras

The pointwise product of two Galois `2`-cocycles is again a `2`-cocycle. This file proves that its
crossed product represents the product of the two original Brauer classes.

The algebra-level argument is the standard matrix stabilization. If `c` and `d` are cocycles of
`G = Aut_K(L)`, the two crossed products act by commuting monomial matrices over the crossed
product for `c * d`. The first action has its nonzero entry in column `r * g` of row `r`; the
second has its nonzero entry in row `h * s` of column `s`. The cocycle identity says that these
are algebra maps and commute. They therefore induce

`CrossedProduct c ⊗[K] CrossedProduct d ≃ₐ[K]
  Matrix G G (CrossedProduct (c * d))`.

The equality of dimensions makes the induced injective map an equivalence. Reindexing by
`G ≃ Fin #G` exhibits the tensor product as a matrix algebra over `CrossedProduct (c * d)`, so
the two sides have the same Brauer class.

## Main results

* `TauCeti.TwoCocycle.instMul`: pointwise multiplication of Galois `2`-cocycles.
* `TauCeti.CrossedProduct.tensorProductAlgEquivMatrix`: the matrix stabilization above.
* `TauCeti.BrauerGroup.crossedProductClass_mul`: pointwise multiplication of cocycles presents
  multiplication of their Brauer classes.

## References

* P. Gille and T. Szamuely, *Central Simple Algebras and Galois Cohomology* (2006), §4.4.
* J.-P. Serre, *Local Fields*, GTM 67 (1979), Chapter X.
-/

public section

open scoped TensorProduct
open groupCohomology

universe u

namespace TauCeti

variable {K : Type u} [Field K] {L : Type u} [Field L] [Algebra K L]

namespace TwoCocycle

/-- The pointwise product of two Galois `2`-cocycles. -/
protected abbrev mul (c d : TwoCocycle K L) : TwoCocycle K L where
  toFun σ τ := c.toFun σ τ * d.toFun σ τ
  isMulCocycle₂ σ τ ρ := by
    rw [mul_mul_mul_comm, c.isMulCocycle₂ σ τ ρ, d.isMulCocycle₂ σ τ ρ]
    simp only [AlgEquiv.smul_units_def, map_mul]
    ac_rfl

instance : Mul (TwoCocycle K L) := ⟨TwoCocycle.mul⟩

/-- Multiplication of `2`-cocycles is pointwise multiplication. -/
@[simp]
theorem toFun_mul (c d : TwoCocycle K L) (σ τ : L ≃ₐ[K] L) :
    (c * d).toFun σ τ = c.toFun σ τ * d.toFun σ τ :=
  rfl

end TwoCocycle

namespace CrossedProduct

variable [FiniteDimensional K L] [IsGalois K L]

/-- Decidable equality on the finite Galois group, used to form its matrix algebra. -/
noncomputable local instance : DecidableEq (L ≃ₐ[K] L) := Classical.decEq _

private noncomputable def leftEntry (c d : TwoCocycle K L) (σ ρ : L ≃ₐ[K] L) :
    L →ₗ[K] CrossedProduct (c * d) where
  toFun x := inc (c * d) (ρ x * c.toFun ρ σ)
  map_add' x y := by simp [add_mul]
  map_smul' r x := by simp

private noncomputable def leftGenerator (c d : TwoCocycle K L) (σ : L ≃ₐ[K] L) :
    L →ₗ[K] Matrix (L ≃ₐ[K] L) (L ≃ₐ[K] L) (CrossedProduct (c * d)) := by
  classical
  let f := LinearMap.pi fun ρ ↦ LinearMap.pi fun τ ↦
    if τ = ρ * σ then leftEntry c d σ ρ else 0
  exact
    { toFun := f
      map_add' := f.map_add
      map_smul' := f.map_smul }

private noncomputable def rightEntry (c d : TwoCocycle K L) (σ τ : L ≃ₐ[K] L) :
    L →ₗ[K] CrossedProduct (c * d) where
  toFun x := inc (c * d) (x * (c.toFun σ τ)⁻¹) * basis (c * d) σ
  map_add' x y := by simp [add_mul, add_mul]
  map_smul' r x := by simp [mul_assoc]

private noncomputable def rightGenerator (c d : TwoCocycle K L) (σ : L ≃ₐ[K] L) :
    L →ₗ[K] Matrix (L ≃ₐ[K] L) (L ≃ₐ[K] L) (CrossedProduct (c * d)) := by
  classical
  let f := LinearMap.pi fun ρ ↦ LinearMap.pi fun τ ↦
    if ρ = σ * τ then rightEntry c d σ τ else 0
  exact
    { toFun := f
      map_add' := f.map_add
      map_smul' := f.map_smul }

omit [FiniteDimensional K L] [IsGalois K L] in
@[simp]
private theorem leftGenerator_apply (c d : TwoCocycle K L) (σ : L ≃ₐ[K] L) (x : L)
    (ρ τ : L ≃ₐ[K] L) :
    leftGenerator c d σ x ρ τ =
      if τ = ρ * σ then inc (c * d) (ρ x * c.toFun ρ σ) else 0 := by
  classical
  rw [leftGenerator]
  change (if τ = ρ * σ then leftEntry c d σ ρ else 0) x = _
  split <;> rfl

omit [FiniteDimensional K L] [IsGalois K L] in
@[simp]
private theorem rightGenerator_apply (c d : TwoCocycle K L) (σ : L ≃ₐ[K] L) (x : L)
    (ρ τ : L ≃ₐ[K] L) :
    rightGenerator c d σ x ρ τ = if ρ = σ * τ then
      inc (c * d) (x * (c.toFun σ τ)⁻¹) * basis (c * d) σ else 0 := by
  classical
  rw [rightGenerator]
  change (if ρ = σ * τ then rightEntry c d σ τ else 0) x = _
  split <;> rfl

omit [IsGalois K L] in
private theorem leftGenerator_mul (c d : TwoCocycle K L) (σ τ : L ≃ₐ[K] L) (x y : L) :
    leftGenerator c d σ x * leftGenerator c d τ y =
      leftGenerator c d (σ * τ) (x * σ y * c.toFun σ τ) := by
  classical
  apply Matrix.ext
  intro ρ υ
  rw [Matrix.mul_apply]
  by_cases hυ : υ = ρ * (σ * τ)
  · rw [Finset.sum_eq_single (ρ * σ)]
    · simp only [leftGenerator_apply, ite_true, hυ, mul_assoc, map_mul,
        AlgEquiv.mul_apply]
      have hscalar :
          ρ x * (c.toFun ρ σ * (ρ (σ y) * c.toFun (ρ * σ) τ)) =
            ρ x * (ρ (σ y) * (ρ (c.toFun σ τ) * c.toFun ρ (σ * τ))) := by
        have hc := c.map_toFun_mul_toFun ρ σ τ
        calc
          _ = ρ x * (ρ (σ y) * (c.toFun ρ σ * c.toFun (ρ * σ) τ)) := by ring
          _ = _ := by rw [← hc]
      simpa only [map_mul] using congrArg (inc (c * d)) hscalar
    · intro κ _ hκ
      by_cases h : κ = ρ * σ
      · exact (hκ h).elim
      · simp [h]
    · simp
  · rw [Finset.sum_eq_zero]
    · simp [hυ]
    · intro κ _
      by_cases hκ : κ = ρ * σ
      · subst κ
        simp [hυ, mul_assoc]
      · simp [hκ]

omit [IsGalois K L] in
private theorem rightGenerator_mul (c d : TwoCocycle K L) (σ τ : L ≃ₐ[K] L) (x y : L) :
    rightGenerator c d σ x * rightGenerator c d τ y =
      rightGenerator c d (σ * τ) (x * σ y * d.toFun σ τ) := by
  classical
  apply Matrix.ext
  intro ρ υ
  rw [Matrix.mul_apply]
  by_cases hρ : ρ = (σ * τ) * υ
  · rw [Finset.sum_eq_single (τ * υ)]
    · simp only [rightGenerator_apply, hρ, mul_assoc, ite_true]
      rw [← mul_assoc]
      rw [← smul_def, ← smul_def, ← smul_def, smul_basis_mul_smul_basis]
      congr 1
      have hc := c.map_toFun_mul_toFun σ τ υ
      simp only [map_mul, Units.val_inv_eq_inv_val, map_inv₀, Units.val_mul,
        TwoCocycle.toFun_mul]
      field_simp
      linear_combination -x * σ y * hc
    · intro κ _ hκ
      by_cases h : κ = τ * υ
      · exact (hκ h).elim
      · simp [h]
    · simp
  · rw [Finset.sum_eq_zero]
    · rw [rightGenerator_apply]
      exact (ite_eq_right hρ).symm
    · intro κ _
      by_cases hκ : κ = τ * υ
      · subst κ
        have hρ' : ρ ≠ σ * (τ * υ) := by simpa [mul_assoc] using hρ
        have hz : rightGenerator c d σ x ρ (τ * υ) = 0 := by
          rw [rightGenerator_apply]
          exact ite_eq_right hρ'
        rw [hz, zero_mul]
      · have hz : rightGenerator c d τ y κ υ = 0 := by
          rw [rightGenerator_apply]
          exact ite_eq_right hκ
        rw [hz, mul_zero]

private noncomputable def leftLinear (c d : TwoCocycle K L) :
    CrossedProduct c →ₗ[K]
      Matrix (L ≃ₐ[K] L) (L ≃ₐ[K] L) (CrossedProduct (c * d)) :=
  (Finsupp.lsum K (leftGenerator c d)).comp ((basis c).repr.toLinearMap.restrictScalars K)

private noncomputable def rightLinear (c d : TwoCocycle K L) :
    CrossedProduct d →ₗ[K]
      Matrix (L ≃ₐ[K] L) (L ≃ₐ[K] L) (CrossedProduct (c * d)) :=
  (Finsupp.lsum K (rightGenerator c d)).comp ((basis d).repr.toLinearMap.restrictScalars K)

omit [FiniteDimensional K L] [IsGalois K L] in
@[simp]
private theorem leftLinear_smul_basis (c d : TwoCocycle K L) (σ : L ≃ₐ[K] L) (x : L) :
    leftLinear c d (x • basis c σ) = leftGenerator c d σ x := by
  simp [leftLinear]

omit [FiniteDimensional K L] [IsGalois K L] in
@[simp]
private theorem rightLinear_smul_basis (c d : TwoCocycle K L) (σ : L ≃ₐ[K] L) (x : L) :
    rightLinear c d (x • basis d σ) = rightGenerator c d σ x := by
  simp [rightLinear]

omit [FiniteDimensional K L] [IsGalois K L] in
private theorem leftLinear_one (c d : TwoCocycle K L) : leftLinear c d 1 = 1 := by
  classical
  rw [one_def, leftLinear_smul_basis]
  apply Matrix.ext
  intro ρ τ
  rw [leftGenerator_apply, Matrix.one_apply]
  by_cases h : τ = ρ
  · subst τ
    simp only [mul_one, ite_true]
    rw [c.toFun_one_right]
    simp [Units.val_inv_eq_inv_val]
  · have h' : τ ≠ ρ * 1 := by simpa using h
    rw [ite_eq_right h', ite_eq_right (Ne.symm h)]

omit [FiniteDimensional K L] [IsGalois K L] in
private theorem rightLinear_one (c d : TwoCocycle K L) : rightLinear c d 1 = 1 := by
  classical
  rw [one_def, rightLinear_smul_basis]
  apply Matrix.ext
  intro ρ τ
  rw [rightGenerator_apply, Matrix.one_apply]
  by_cases h : ρ = τ
  · subst ρ
    simp only [one_mul, c.toFun_one_left, ite_true]
    rw [basis_one, ← map_mul]
    simp only [TwoCocycle.toFun_mul, Units.val_mul, Units.val_inv_eq_inv_val]
    field_simp
    ring_nf
    exact map_one (inc (c * d))
  · have h' : ρ ≠ 1 * τ := by simpa using h
    rw [ite_eq_right h', ite_eq_right h]

omit [IsGalois K L] in
private theorem leftLinear_mul (c d : TwoCocycle K L) (a b : CrossedProduct c) :
    leftLinear c d (a * b) = leftLinear c d a * leftLinear c d b := by
  induction a using induction_on with
  | zero => simp
  | add a a' ha ha' => simp only [add_mul, map_add, ha, ha', add_mul]
  | smul_basis σ x =>
    induction b using induction_on with
    | zero => simp
    | add b b' hb hb' => simp only [mul_add, map_add, hb, hb', mul_add]
    | smul_basis τ y =>
      simp only [smul_basis_mul_smul_basis, leftLinear_smul_basis]
      exact (leftGenerator_mul c d σ τ x y).symm

omit [IsGalois K L] in
private theorem rightLinear_mul (c d : TwoCocycle K L) (a b : CrossedProduct d) :
    rightLinear c d (a * b) = rightLinear c d a * rightLinear c d b := by
  induction a using induction_on with
  | zero => simp
  | add a a' ha ha' => simp only [add_mul, map_add, ha, ha', add_mul]
  | smul_basis σ x =>
    induction b using induction_on with
    | zero => simp
    | add b b' hb hb' => simp only [mul_add, map_add, hb, hb', mul_add]
    | smul_basis τ y =>
      simp only [smul_basis_mul_smul_basis, rightLinear_smul_basis]
      exact (rightGenerator_mul c d σ τ x y).symm

private noncomputable def leftAlgHom (c d : TwoCocycle K L) :
    CrossedProduct c →ₐ[K]
      Matrix (L ≃ₐ[K] L) (L ≃ₐ[K] L) (CrossedProduct (c * d)) :=
  AlgHom.ofLinearMap (leftLinear c d) (leftLinear_one c d) (leftLinear_mul c d)

private noncomputable def rightAlgHom (c d : TwoCocycle K L) :
    CrossedProduct d →ₐ[K]
      Matrix (L ≃ₐ[K] L) (L ≃ₐ[K] L) (CrossedProduct (c * d)) :=
  AlgHom.ofLinearMap (rightLinear c d) (rightLinear_one c d) (rightLinear_mul c d)

omit [IsGalois K L] in
private theorem leftGenerator_comm_rightGenerator (c d : TwoCocycle K L)
    (σ τ : L ≃ₐ[K] L) (x y : L) :
    leftGenerator c d σ x * rightGenerator c d τ y =
      rightGenerator c d τ y * leftGenerator c d σ x := by
  classical
  apply Matrix.ext
  intro ρ υ
  simp only [Matrix.mul_apply]
  by_cases h : ρ * σ = τ * υ
  · rw [Finset.sum_eq_single (ρ * σ), Finset.sum_eq_single (τ⁻¹ * ρ)]
    · have hρ : ρ = τ * (τ⁻¹ * ρ) := by group
      have hυ : υ = (τ⁻¹ * ρ) * σ := by
        calc
          υ = τ⁻¹ * (τ * υ) := by group
          _ = τ⁻¹ * (ρ * σ) := by rw [h]
          _ = (τ⁻¹ * ρ) * σ := by group
      rw [leftGenerator_apply, rightGenerator_apply, rightGenerator_apply,
        leftGenerator_apply, ite_eq_left rfl, ite_eq_left h, ite_eq_left hρ,
        ite_eq_left hυ]
      rw [← mul_assoc
          (inc (c * d) (ρ x * c.toFun ρ σ))
          (inc (c * d) (y * (c.toFun τ υ)⁻¹))
          (basis (c * d) τ),
        ← map_mul,
        mul_assoc
          (inc (c * d) (y * (c.toFun τ (τ⁻¹ * ρ))⁻¹))
          (basis (c * d) τ)
          (inc (c * d) ((τ⁻¹ * ρ) x * c.toFun (τ⁻¹ * ρ) σ)),
        basis_mul_inc,
        ← mul_assoc
          (inc (c * d) (y * (c.toFun τ (τ⁻¹ * ρ))⁻¹))
          (inc (c * d) (τ ((τ⁻¹ * ρ) x * c.toFun (τ⁻¹ * ρ) σ)))
          (basis (c * d) τ),
        ← map_mul,
        ← smul_def, ← smul_def]
      congr 1
      rw [hυ]
      have hc := c.map_toFun_mul_toFun τ (τ⁻¹ * ρ) σ
      rw [← hρ] at hc
      have hx : τ ((τ⁻¹ * ρ) x) = ρ x := by
        rw [← AlgEquiv.mul_apply, ← hρ]
      simp only [map_mul]
      rw [hx]
      simp only [Units.val_inv_eq_inv_val]
      field_simp
      linear_combination -ρ x * y * hc
    · intro κ _ hκ
      have hκ' : ρ ≠ τ * κ := by
        intro h'
        apply hκ
        rw [h']
        group
      have hz : rightGenerator c d τ y ρ κ = 0 := by
        rw [rightGenerator_apply]
        exact ite_eq_right hκ'
      rw [hz, zero_mul]
    · simp
    · intro κ _ hκ
      have hz : leftGenerator c d σ x ρ κ = 0 := by
        rw [leftGenerator_apply]
        exact ite_eq_right hκ
      rw [hz, zero_mul]
    · simp
  · rw [Finset.sum_eq_zero, Finset.sum_eq_zero]
    · intro κ _
      by_cases hκ : ρ = τ * κ
      · have hκ' : υ ≠ κ * σ := by
          intro h'
          apply h
          rw [hκ, h', mul_assoc]
        have hz : leftGenerator c d σ x κ υ = 0 := by
          rw [leftGenerator_apply]
          exact ite_eq_right hκ'
        rw [hz, mul_zero]
      · have hz : rightGenerator c d τ y ρ κ = 0 := by
          rw [rightGenerator_apply]
          exact ite_eq_right hκ
        rw [hz, zero_mul]
    · intro κ _
      by_cases hκ : κ = ρ * σ
      · subst κ
        have hz : rightGenerator c d τ y (ρ * σ) υ = 0 := by
          rw [rightGenerator_apply]
          exact ite_eq_right h
        rw [hz, mul_zero]
      · have hz : leftGenerator c d σ x ρ κ = 0 := by
          rw [leftGenerator_apply]
          exact ite_eq_right hκ
        rw [hz, zero_mul]

omit [IsGalois K L] in
private theorem leftAlgHom_comm_rightAlgHom (c d : TwoCocycle K L)
    (a : CrossedProduct c) (b : CrossedProduct d) :
    leftAlgHom c d a * rightAlgHom c d b = rightAlgHom c d b * leftAlgHom c d a := by
  induction a using induction_on with
  | zero => simp
  | add a a' ha ha' => simp only [map_add, add_mul, mul_add, ha, ha']
  | smul_basis σ x =>
    induction b using induction_on with
    | zero => simp
    | add b b' hb hb' => simp only [map_add, mul_add, add_mul, hb, hb']
    | smul_basis τ y =>
      simpa [leftAlgHom, rightAlgHom, AlgHom.ofLinearMap_apply] using
        leftGenerator_comm_rightGenerator c d σ τ x y

private noncomputable def tensorProductToMatrix (c d : TwoCocycle K L) :
    CrossedProduct c ⊗[K] CrossedProduct d →ₐ[K]
      Matrix (L ≃ₐ[K] L) (L ≃ₐ[K] L) (CrossedProduct (c * d)) :=
  Algebra.TensorProduct.lift (leftAlgHom c d) (rightAlgHom c d) fun a b ↦
    leftAlgHom_comm_rightAlgHom c d a b

private theorem finrank_tensorProduct_eq_matrix (c d : TwoCocycle K L) :
    Module.finrank K (CrossedProduct c ⊗[K] CrossedProduct d) =
      Module.finrank K
        (Matrix (L ≃ₐ[K] L) (L ≃ₐ[K] L) (CrossedProduct (c * d))) := by
  rw [Module.finrank_tensorProduct, finrank_eq_finrank_sq, finrank_eq_finrank_sq,
    Module.finrank_matrix, Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank,
    finrank_eq_finrank_sq]
  ring

/-- The tensor product of the crossed products for `c` and `d` is a matrix algebra over the
crossed product for their pointwise product. -/
noncomputable def tensorProductAlgEquivMatrix (c d : TwoCocycle K L) :
    CrossedProduct c ⊗[K] CrossedProduct d ≃ₐ[K]
      Matrix (L ≃ₐ[K] L) (L ≃ₐ[K] L) (CrossedProduct (c * d)) := by
  let f := tensorProductToMatrix c d
  have hinj : Function.Injective f := f.toRingHom.injective
  have hsurj : Function.Surjective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (finrank_tensorProduct_eq_matrix c d)).mp hinj
  exact AlgEquiv.ofBijective f ⟨hinj, hsurj⟩

end CrossedProduct

namespace BrauerGroup

variable [FiniteDimensional K L] [IsGalois K L]

/-- **Multiplication of crossed-product classes.** The pointwise product of two Galois
`2`-cocycles presents the product of the Brauer classes presented by the two cocycles. -/
theorem crossedProductClass_mul (c d : TwoCocycle K L) :
    crossedProductClass (c * d) = crossedProductClass c * crossedProductClass d := by
  classical
  let e := Fintype.equivFin (L ≃ₐ[K] L)
  let φ := (CrossedProduct.tensorProductAlgEquivMatrix c d).trans
    (Matrix.reindexAlgEquiv K (CrossedProduct (c * d)) e)
  rw [crossedProductClass_def, crossedProductClass_def, crossedProductClass_def,
    ← mk_tensorProduct]
  calc
    mk (CSA.of K (CrossedProduct (c * d))) =
        mk (CSA.matrix (CSA.of K (CrossedProduct (c * d))) (Fintype.card (L ≃ₐ[K] L))) := by
          symm
          exact mk_matrix _ _
    _ = mk (CSA.tensorProduct (CSA.of K (CrossedProduct c))
          (CSA.of K (CrossedProduct d))) := by
      symm
      exact mk_eq_mk_of_algEquiv φ

end BrauerGroup

end TauCeti
