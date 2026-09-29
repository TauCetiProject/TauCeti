/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.CrossedProduct.BrauerClass
public import TauCeti.Algebra.CrossedProduct.Splitting.Basic
public import TauCeti.Algebra.CentralSimple.Splitting
-- Non-public: the dimension counts and the matrix model of `End_K(Lⁿ)` are used only in proofs.
import Mathlib.LinearAlgebra.Basis.MulOpposite
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import TauCeti.Algebra.BrauerGroup.Trivial

/-!
# The cocycle of a splitting recovers the class of the algebra being split

Let `L/K` be a finite Galois extension and `A` a finite-dimensional central simple `K`-algebra with
a splitting `φ : L ⊗[K] A ≃ₐ[L] Mₙ(L)`. This file proves that the crossed product of the cocycle
`c = cocycleOfSplitting φ` has the Brauer class of `A`, and deduces that every central simple
algebra split by `L` has the class of a crossed product over `L`.

Together with the existence of finite Galois splitting fields, this shows that every Brauer class
of `K` is the class of a crossed product, i.e. that the crossed-product construction from Galois
`2`-cocycles to the Brauer group is surjective.

## Main results

* `TauCeti.BrauerGroup.crossedProductClass_cocycleOfSplitting`: the crossed product of the
  cocycle attached to a splitting of `A` has the Brauer class of `A`.
* `TauCeti.BrauerGroup.exists_crossedProductClass_eq_of_isSplittingField`: every central simple
  algebra split by a finite Galois `L/K` has the Brauer class of a crossed product over `L`.

## Implementation notes

`A` and `L` live in the universe of `K`, because the proof uses the group law of
`BrauerGroup.{u, u} K`, in which the class of `Aᵐᵒᵖ` is the inverse of the class of `A`.

## References

* P. Gille and T. Szamuely, *Central Simple Algebras and Galois Cohomology* (2006), §4.4.
* J.-P. Serre, *Local Fields*, GTM 67 (1979), Chapter X.
-/

public section

open scoped TensorProduct

open Matrix Matrix.GeneralLinearGroup

universe u

namespace TauCeti

variable {K : Type u} [Field K] {A : Type u} [Ring A] [Algebra K A]
  {L : Type u} [Field L] [Algebra K L] {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
  (φ : L ⊗[K] A ≃ₐ[L] Matrix n n L)

/-- The right action of `A` on the row vectors `Lⁿ` through `a ↦ φ(1 ⊗ a)`, as a `K`-algebra
homomorphism out of `Aᵐᵒᵖ`. -/
private noncomputable def rowAction : Aᵐᵒᵖ →ₐ[K] Module.End K (n → L) where
  toFun a := (vecMulLinear (φ (1 ⊗ₜ a.unop))).restrictScalars K
  map_one' := LinearMap.ext fun w ↦ by
    simp [← Algebra.TensorProduct.one_def]
  map_mul' a b := LinearMap.ext fun w ↦ by
    simp [vecMul_vecMul, ← map_mul]
  map_zero' := LinearMap.ext fun w ↦ by simp
  map_add' a b := LinearMap.ext fun w ↦ by simp [TensorProduct.tmul_add]
  commutes' r := LinearMap.ext fun w ↦ by
    have h : φ (1 ⊗ₜ algebraMap K A r) = algebraMap K (Matrix n n L) r :=
      ((φ.toAlgHom.restrictScalars K).comp Algebra.TensorProduct.includeRight).commutes r
    simp [h, Algebra.algebraMap_eq_smul_one (A := Matrix n n L)]

omit [Nonempty n] in
private theorem rowAction_apply (a : Aᵐᵒᵖ) (w : n → L) :
    rowAction φ a w = w ᵥ* φ (1 ⊗ₜ a.unop) :=
  (rfl)

/-- The operator `w ↦ σ(w) · g_σ⁻¹` on the row vectors `Lⁿ`, with `g_σ = splittingConjugator φ σ`
and `σ` acting entrywise. -/
private noncomputable def rowGenerator (σ : L ≃ₐ[K] L) : Module.End K (n → L) where
  toFun w := (fun i ↦ σ (w i)) ᵥ* ((splittingConjugator φ σ)⁻¹ : GL n L)
  map_add' v w := by
    rw [← add_vecMul]
    simp only [Pi.add_apply, map_add]
    rfl
  map_smul' r w := by
    rw [RingHom.id_apply, ← smul_vecMul]
    simp only [Pi.smul_apply, map_smul]
    rfl

private theorem rowGenerator_apply (σ : L ≃ₐ[K] L) (w : n → L) :
    rowGenerator φ σ w = (fun i ↦ σ (w i)) ᵥ* ((splittingConjugator φ σ)⁻¹ : GL n L) :=
  (rfl)

/-- `g_σ⁻¹` intertwines the entrywise action of `σ` on `φ(1 ⊗ a)` with `φ(1 ⊗ a)`: the matrices
`φ(1 ⊗ a)` are the fixed points of the twisted action `M ↦ g_σ · σ(M) · g_σ⁻¹`. -/
private theorem map_mul_inv_eq (σ : L ≃ₐ[K] L) (a : A) :
    (φ (1 ⊗ₜ a)).map σ * ((splittingConjugator φ σ)⁻¹ : GL n L) =
      ((splittingConjugator φ σ)⁻¹ : GL n L) * φ (1 ⊗ₜ a) := by
  have h := splittingConjugator_mul_mul_inv φ σ ((φ (1 ⊗ₜ a)).map σ)
  rw [splittingAut_map, AlgEquiv.symm_apply_apply, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul, map_one, ← Matrix.coe_units_inv] at h
  simp only [AlgEquiv.refl_toAlgHom, AlgHom.coe_id, id_eq] at h
  conv_rhs => rw [← h]
  simp only [← mul_assoc, Units.inv_mul, one_mul]

/-- `g_σ⁻¹ ∈ GL_n(L)` read through the entrywise action: `σ(g_τ⁻¹) · g_σ⁻¹ = c(σ, τ) · g_στ⁻¹`. -/
private theorem map_inv_mul_inv (σ τ : L ≃ₐ[K] L) :
    map (σ : L →+* L) (splittingConjugator φ τ)⁻¹ * (splittingConjugator φ σ)⁻¹ =
      scalar n ((cocycleOfSplitting φ).toFun σ τ) * (splittingConjugator φ (σ * τ))⁻¹ := by
  rw [← scalar_cocycleOfSplitting_mul φ σ τ, _root_.mul_inv_rev, _root_.mul_inv_rev, map_inv,
    GeneralLinearGroup.scalar_commute, inv_mul_cancel_right]

/-- `g_1⁻¹ = c(1, 1)`, the normalization of the conjugators at the identity. -/
private theorem inv_splittingConjugator_one :
    (splittingConjugator φ 1)⁻¹ = scalar n ((cocycleOfSplitting φ).toFun 1 1) := by
  have h := scalar_cocycleOfSplitting_mul φ 1 1
  have hmap : map ((1 : L ≃ₐ[K] L) : L →+* L) (splittingConjugator φ 1) =
      splittingConjugator φ 1 := by
    ext; simp
  rw [hmap, one_mul, ← mul_assoc, mul_eq_right] at h
  exact inv_eq_of_mul_eq_one_left h

/-- The crossed product of `cocycleOfSplitting φ` acting on the row vectors `Lⁿ`: `L` by scalars
and `u_σ` by `rowGenerator φ σ`. -/
private noncomputable def rowCrossedAction :
    CrossedProduct (cocycleOfSplitting φ) →ₐ[K] Module.End K (n → L) :=
  CrossedProduct.lift (Algebra.lsmul K K (n → L)) (rowGenerator φ)
    (fun σ x ↦ LinearMap.ext fun w ↦ by
      simp only [Module.End.mul_apply, rowGenerator_apply, Algebra.lsmul_coe, ← smul_vecMul]
      congr 1
      ext i
      simp)
    (fun σ τ ↦ LinearMap.ext fun w ↦ by
      have hmap : (((splittingConjugator φ τ)⁻¹ : GL n L) : Matrix n n L).map σ =
          (map (σ : L →+* L) (splittingConjugator φ τ)⁻¹ : GL n L) := by
        ext i j
        rw [Matrix.map_apply, GeneralLinearGroup.map_apply, RingHom.coe_coe]
      have hσ (v : n → L) (M : Matrix n n L) :
          (fun i ↦ σ ((v ᵥ* M) i)) = (fun i ↦ σ (v i)) ᵥ* M.map σ :=
        funext (RingHom.map_vecMul (σ : L →+* L) M v)
      simp only [Module.End.mul_apply, rowGenerator_apply, Algebra.lsmul_coe, hσ,
        vecMul_vecMul, hmap]
      rw [← Units.val_mul, map_inv_mul_inv, Units.val_mul, coe_scalar, scalar_apply,
        ← smul_eq_diagonal_mul, vecMul_smul]
      rfl)
    (LinearMap.ext fun w ↦ by
      simp [rowGenerator_apply, inv_splittingConjugator_one, scalar_apply])

private theorem commute_rowCrossedAction_rowAction (b : CrossedProduct (cocycleOfSplitting φ))
    (a : Aᵐᵒᵖ) : Commute (rowCrossedAction φ b) (rowAction φ a) := by
  induction b using CrossedProduct.induction_on with
  | zero => simp
  | add b b' hb hb' => simpa only [map_add] using hb.add_left hb'
  | smul_basis σ x =>
    rw [rowCrossedAction, CrossedProduct.lift_smul_basis]
    refine Commute.mul_left (LinearMap.ext fun w ↦ ?_) (LinearMap.ext fun w ↦ ?_)
    · simp [rowAction_apply, smul_vecMul]
    · have hσ (v : n → L) (M : Matrix n n L) :
          (fun i ↦ σ ((v ᵥ* M) i)) = (fun i ↦ σ (v i)) ᵥ* M.map σ :=
        funext (RingHom.map_vecMul (σ : L →+* L) M v)
      simp only [Module.End.mul_apply, rowAction_apply, rowGenerator_apply, hσ,
        vecMul_vecMul, map_mul_inv_eq]

/-- The action of `CrossedProduct c ⊗[K] Aᵐᵒᵖ` on the row vectors `Lⁿ`. -/
private noncomputable def rowTensorAction :
    CrossedProduct (cocycleOfSplitting φ) ⊗[K] Aᵐᵒᵖ →ₐ[K] Module.End K (n → L) :=
  Algebra.TensorProduct.lift (rowCrossedAction φ) (rowAction φ)
    (commute_rowCrossedAction_rowAction φ)

variable [FiniteDimensional K L] [IsGalois K L] [Algebra.IsCentral K A] [IsSimpleRing A]
  [FiniteDimensional K A]

private theorem rowTensorAction_bijective : Function.Bijective (rowTensorAction φ) := by
  have hinj : Function.Injective (rowTensorAction φ) := (rowTensorAction φ).toRingHom.injective
  have hA : Module.finrank K A = Fintype.card n * Fintype.card n := by
    rw [← Module.finrank_baseChange (R := L), φ.toLinearEquiv.finrank_eq, Module.finrank_matrix,
      Module.finrank_self, mul_one]
  have hdim : Module.finrank K (CrossedProduct (cocycleOfSplitting φ) ⊗[K] Aᵐᵒᵖ) =
      Module.finrank K (Module.End K (n → L)) := by
    rw [Module.finrank_tensorProduct, CrossedProduct.finrank_eq_finrank_sq,
      MulOpposite.finrank, hA, Module.finrank_linearMap, Module.finrank_pi_fintype,
      Finset.sum_const, Finset.card_univ, smul_eq_mul]
    ring
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
    (f := (rowTensorAction φ).toLinearMap)).mp hinj⟩

namespace BrauerGroup

/-- **The cocycle of a splitting recovers the class of the algebra being split.** For a finite
Galois `L/K` and a splitting `φ : L ⊗[K] A ≃ₐ[L] Mₙ(L)` of a finite-dimensional central simple
`K`-algebra `A`, the crossed product of `cocycleOfSplitting φ` is Brauer equivalent to `A`. -/
theorem crossedProductClass_cocycleOfSplitting :
    crossedProductClass (cocycleOfSplitting φ) = mk (CSA.of K A) := by
  let d := Module.finrank K (n → L)
  have : NeZero d := ⟨Module.finrank_pos.ne'⟩
  let e := (AlgEquiv.ofBijective _ (rowTensorAction_bijective φ)).trans
    (LinearMap.toMatrixAlgEquiv (Module.finBasisOfFinrankEq K (n → L) rfl))
  have h : mk (CSA.tensorProduct (CSA.of K (CrossedProduct (cocycleOfSplitting φ)))
      (CSA.op (CSA.of K A))) = mk (CSA.matrix (CSA.base K) d) :=
    mk_eq_mk_of_algEquiv e
  rw [mk_matrix, mk_base, mk_tensorProduct, mk_op, mul_inv_eq_one] at h
  rwa [crossedProductClass_def]

/-- **Every algebra split by a finite Galois extension is a crossed product up to Brauer
equivalence**: if `L/K` is finite Galois and splits the finite-dimensional central simple
`K`-algebra `A`, then some `2`-cocycle of `Gal(L/K)` has the Brauer class of `A`, namely the
cocycle of any splitting. -/
theorem exists_crossedProductClass_eq_of_isSplittingField (h : Algebra.IsSplittingField K A L) :
    ∃ c : TwoCocycle K L, crossedProductClass c = mk (CSA.of K A) := by
  obtain ⟨m, ⟨φ⟩⟩ := (Algebra.isSplittingField_iff K A L).1 h
  have : NeZero m := ⟨ne_zero_of_algEquiv_matrix L φ⟩
  exact ⟨cocycleOfSplitting φ, crossedProductClass_cocycleOfSplitting φ⟩

end BrauerGroup

end TauCeti
