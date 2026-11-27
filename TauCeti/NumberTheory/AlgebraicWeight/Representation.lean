/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.LinearAlgebra.PiTensorProduct.Finite
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.SplitPoints
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Transvection
public import TauCeti.NumberTheory.AlgebraicWeight.Embedding
public import TauCeti.RepresentationTheory.ClassicalGroups.WeylModule.Rational
public import TauCeti.RepresentationTheory.Tensor.Pi.External
public import TauCeti.RingTheory.Etale.Field
import TauCeti.LinearAlgebra.PiTensorProduct.Dual
import TauCeti.RepresentationTheory.ClassicalGroups.WeylModule.Rationality
import TauCeti.RepresentationTheory.ClassicalGroups.WeylModule.Weight.HighestWeight

/-!
# Algebraic coefficient representations for embedding-indexed weights

The coefficient representation of a labelled dominant weight is the external tensor product
of the rational Weyl modules of the individual weights. A tuple acts on each tensor factor
through its component at that label. For a number field, the splitting of the complex points
of the Weil restriction labels the factors by the complex embeddings of the field.

## References

* P. Allen et al., *Potential automorphy over CM fields*, Ann. of Math. 197 (2023), §2.2.
-/

public section

open Matrix Module
open scoped TensorProduct

namespace TauCeti.EmbeddingWeight

variable {ι : Type*} {n : ℕ}

/-- The carrier of the algebraic coefficient representation, with one rational Weyl module
per label. -/
abbrev CoefficientSpace (a : EmbeddingWeight ι n) :=
  ⨂[ℂ] i, (weylModuleOfShape ℂ n (a i).detShiftShape).toSubmodule

/-- Register the additive group on the coefficient space directly. The tensor product instance
requires a dependent family of additive group instances that typeclass search does not
synthesize for these factors. -/
noncomputable instance (a : EmbeddingWeight ι n) : AddCommGroup a.CoefficientSpace :=
  Module.addCommMonoidToAddCommGroup ℂ

/-- The algebraic coefficient representation on the split group, formed by taking the external
tensor product of the rational Weyl representations of the labelled dominant weights. -/
noncomputable def coefficientRep (a : EmbeddingWeight ι n) :
    Representation ℂ (ι → GL (Fin n) ℂ) a.CoefficientSpace :=
  Representation.piExternalTensor fun i ↦ rationalWeylRep ℂ n (a i)

/-- The coefficient representation on the split group is the indexed external tensor product
of the rational Weyl representations. -/
theorem coefficientRep_eq (a : EmbeddingWeight ι n) :
    a.coefficientRep = Representation.piExternalTensor fun i ↦ rationalWeylRep ℂ n (a i) :=
  (rfl)

/-- Each coordinate acts through the Weyl representation at its own label. -/
@[simp]
theorem coefficientRep_apply_tprod (a : EmbeddingWeight ι n) (g : ι → GL (Fin n) ℂ)
    (v : ∀ i, (weylModuleOfShape ℂ n (a i).detShiftShape).toSubmodule) :
    a.coefficientRep g (PiTensorProduct.tprod ℂ v) =
      PiTensorProduct.tprod ℂ fun i ↦ rationalWeylRep ℂ n (a i) (g i) (v i) := by
  simp [coefficientRep_eq]

-- The general tensor product lemmas ask for a dependent family of additive group instances.
-- Typeclass search finds each factor's instance pointwise, so assemble the family here.
private noncomputable local instance (a : EmbeddingWeight ι n) :
    ∀ i, AddCommGroup (weylModuleOfShape ℂ n (a i).detShiftShape).toSubmodule :=
  fun _ ↦ inferInstance

/-- The coefficient representation for finitely many labels is irreducible. -/
instance isIrreducible_coefficientRep [Finite ι] (a : EmbeddingWeight ι n) :
    a.coefficientRep.IsIrreducible := by
  rw [coefficientRep_eq]
  have : ∀ i, FiniteDimensional ℂ (weylModuleOfShape ℂ n (a i).detShiftShape).toSubmodule :=
    fun _ ↦ inferInstance
  exact Representation.isIrreducible_piExternalTensor _ fun _ ↦ inferInstance

/-- A tensor of highest weight vectors is a nonzero vector of the labelled weight on the
diagonal torus and is fixed by each upper root subgroup in every factor. -/
theorem exists_highestWeightVector [Fintype ι] [DecidableEq ι] (a : EmbeddingWeight ι n) :
    ∃ v : a.CoefficientSpace, v ≠ 0 ∧
      (∀ t : ι → Fin n → ℂˣ, a.coefficientRep (fun i ↦ diagGL (t i)) v =
        (∏ i, (↑(weightChar ℂ (a i).val (t i)) : ℂ)) • v) ∧
      ∀ (i : ι) (p q : Fin n) (h : p < q) (c : ℂ),
        a.coefficientRep (Function.update 1 i (transvectionUnit h.ne c)) v = v := by
  have : ∀ i, Module.Projective ℂ (weylModuleOfShape ℂ n (a i).detShiftShape).toSubmodule :=
    fun _ ↦ inferInstance
  choose v hv hv₀ using fun i ↦ Submodule.exists_mem_ne_zero_of_ne_bot
    (weightSpace_rationalWeylRep_self_ne_bot ℂ (a i))
  refine ⟨PiTensorProduct.tprod ℂ v, PiTensorProduct.tprod_ne_zero hv₀, ?_, ?_⟩
  · intro t
    rw [coefficientRep_apply_tprod]
    simp only [apply_of_mem_weightSpace (hv _) _]
    exact (PiTensorProduct.tprod ℂ).map_smul_univ _ _
  · intro i p q h c
    rw [coefficientRep_apply_tprod]
    congr 1
    funext j
    by_cases hj : j = i
    · subst j
      rw [Function.update_self]
      exact rationalWeylRep_apply_transvectionUnit_eq_self (a i) h (hv i) c
    · simp [Function.update_of_ne hj]

/-- In some basis indexed by tuples of factor indices, the matrix entries of the coefficient
representation are polynomials in the labelled matrix entries divided by a product of powers
of the component determinants, with one denominator valid for every matrix entry. -/
theorem exists_toMatrix_coefficientRep_eq [Fintype ι] [DecidableEq ι] (a : EmbeddingWeight ι n) :
    ∃ (d : ι → ℕ) (b : Basis (∀ i, Fin (d i)) ℂ a.CoefficientSpace)
      (P : (∀ i, Fin (d i)) → (∀ i, Fin (d i)) → MvPolynomial (ι × (Fin n × Fin n)) ℂ)
      (m : ι → ℕ), ∀ (g : ι → GL (Fin n) ℂ) (p q : ∀ i, Fin (d i)),
        LinearMap.toMatrix b b (a.coefficientRep g) p q =
          (∏ i, ((g i : Matrix (Fin n) (Fin n) ℂ).det ^ m i)⁻¹) *
            MvPolynomial.eval (fun j ↦ g j.1 j.2.1 j.2.2) (P p q) := by
  choose b P m h using fun i ↦
    (isRationalRep_iff _).mp (isRationalRep_rationalWeylRep n (a i))
  refine ⟨_, Basis.piTensorProduct b,
    fun p q ↦ ∏ i, MvPolynomial.rename (Prod.mk i) (P i (p i) (q i)), m, ?_⟩
  intro g p q
  rw [coefficientRep_eq, Representation.toMatrix_piExternalTensor]
  simp only [h, Finset.prod_mul_distrib, map_prod, MvPolynomial.eval_rename_prod_mk]

section NumberField

open WithConv TauCeti.Algebra TauCeti.Algebra.WeilRestriction

variable {F : Type*} [Field F] [NumberField F]

/-- The coefficient representation `Ξ_a` of the complex points of
`Res_{F/ℚ} GLₙ`, using the given weight at each complex embedding of `F`. -/
noncomputable def weilRestrictionRep (a : EmbeddingWeight (F →+* ℂ) n) :
    Representation ℂ
      (WithConv (WeilRestriction ℚ F (GeneralLinear.coordinateHopfAlgebra F n) →ₐ[ℚ] ℂ))
      a.CoefficientSpace :=
  have : Algebra.Etale ℚ F := Algebra.Etale.of_isSeparable _ _
  a.coefficientRep.comp ((MonoidHom.pi fun τ : F →+* ℂ ↦
      Pi.evalMonoidHom (fun _ : F →ₐ[ℚ] ℂ ↦ GL (Fin n) ℂ) τ.toRatAlgHom).comp
      (generalLinearSplitPoints ℚ F ℂ n).toMonoidHom)

/-- The action of a Weil-restriction point is the coefficient action of its tuple of split
components, indexed by the complex embeddings. -/
theorem weilRestrictionRep_apply (a : EmbeddingWeight (F →+* ℂ) n)
    (g : WithConv (WeilRestriction ℚ F (GeneralLinear.coordinateHopfAlgebra F n) →ₐ[ℚ] ℂ)) :
    haveI : Algebra.Etale ℚ F := Algebra.Etale.of_isSeparable _ _
    a.weilRestrictionRep g =
      a.coefficientRep (fun τ ↦ generalLinearSplitPoints ℚ F ℂ n g τ.toRatAlgHom) :=
  (rfl)

/-- Under the splitting of the Weil restriction, the action on each factor is that of its
own complex embedding. -/
@[simp]
theorem weilRestrictionRep_apply_tprod (a : EmbeddingWeight (F →+* ℂ) n)
    (g : WithConv (WeilRestriction ℚ F (GeneralLinear.coordinateHopfAlgebra F n) →ₐ[ℚ] ℂ))
    (v : ∀ i, (weylModuleOfShape ℂ n (a i).detShiftShape).toSubmodule) :
    a.weilRestrictionRep g (PiTensorProduct.tprod ℂ v) =
      PiTensorProduct.tprod ℂ fun τ ↦ rationalWeylRep ℂ n (a τ)
        (GeneralLinearGroup.map (Algebra.TensorProduct.productMap τ.toRatAlgHom (AlgHom.id ℚ ℂ) :
          F ⊗[ℚ] ℂ →+* ℂ) (generalLinearPoints ℚ F n ℂ g)) (v τ) := by
  simp [weilRestrictionRep_apply]

/-- The embedding-wise coefficient representation is irreducible as a representation of the
complex points of the Weil restriction. -/
instance isIrreducible_weilRestrictionRep (a : EmbeddingWeight (F →+* ℂ) n) :
    a.weilRestrictionRep.IsIrreducible := by
  have : Algebra.Etale ℚ F := Algebra.Etale.of_isSeparable _ _
  rw [weilRestrictionRep]
  refine (MonoidHom.isIrreducible_comp_surjective_iff _ ?_ _).mpr inferInstance
  intro g
  refine ⟨(generalLinearSplitPoints ℚ F ℂ n).symm (fun τ ↦ g τ.toRingHom), funext fun τ ↦ ?_⟩
  simp

end NumberField

end TauCeti.EmbeddingWeight
