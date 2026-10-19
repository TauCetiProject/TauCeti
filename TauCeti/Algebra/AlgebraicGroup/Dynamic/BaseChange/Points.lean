/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Dynamic.Parabolic
public import TauCeti.Algebra.AlgebraicGroup.BaseChange.Naturality
public import TauCeti.Algebra.Bialgebra.AddMonoidAlgebra.BaseChange

/-!
# Base change of dynamic subgroups on points

The tensor-product adjunction identifies points of a scalar-extended group with points
of the original group on the same value algebra. Under this identification the dynamic
parabolic, Levi, and unipotent subgroups of a cocharacter are unchanged. The extension
of a conjugation family and its value at the origin are unchanged as well.

All value algebras are allowed, including nonreduced ones. No flatness, smoothness,
finite-type, or field hypothesis is needed.

The constructions use `TauCeti.AlgHom.baseChangePointsMulEquiv` and the scalar-extension
comparison for additive monoid bialgebras.

## References

* B. Conrad, O. Gabber, G. Prasad, *Pseudo-reductive Groups*, §2.1.
* J. S. Milne, *Algebraic Groups* (2017), Chapter 13.
-/

public section

open TensorProduct WithConv TauCeti

namespace BialgHom

variable {R H : Type*} (S : Type*) [CommSemiring R] [CommSemiring S] [Algebra R S]
variable [Semiring H] [Bialgebra R H]

/-- Extend a cocharacter along a homomorphism of base semirings, using the canonical
identification of the scalar-extended Laurent coordinate algebra. -/
noncomputable def baseChangeCocharacter (l : H →ₐc[R] LaurentPolynomial R) :
    S ⊗[R] H →ₐc[S] LaurentPolynomial S :=
  (AddMonoidAlgebra.scalarTensorBialgEquiv R S (M := ℤ)).toBialgHom.comp
    (_root_.Bialgebra.TensorProduct.map (BialgHom.id S S) l)

/-- The base-changed cocharacter on a pure tensor. -/
@[simp]
theorem baseChangeCocharacter_tmul (l : H →ₐc[R] LaurentPolynomial R) (s : S) (h : H) :
    l.baseChangeCocharacter S (s ⊗ₜ[R] h) =
      s • _root_.AddMonoidAlgebra.mapAlgHom ℤ (Algebra.ofId R S) (l h) := by
  simp [baseChangeCocharacter]

end BialgHom

namespace TauCeti.Cocharacter

variable {R S H A : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
variable [Semiring H]
variable [CommSemiring A] [Algebra S A] [Algebra R A] [IsScalarTower R S A]

section Bialgebra

variable [Bialgebra R H]

/-- The map on multiplicative-group points is unchanged by scalar extension. -/
theorem baseChangePointsMulEquiv_pointsHom (l : H →ₐc[R] LaurentPolynomial R) (u : Aˣ) :
    AlgHom.baseChangePointsMulEquiv (k := R) (K := S) (A := H) (pointsHom A l u) =
      pointsHom A (l.baseChangeCocharacter S) u := by
  have hev : ((laurentEval (R := S) u).restrictScalars R).comp
      (_root_.AddMonoidAlgebra.mapAlgHom ℤ (Algebra.ofId R S)) =
        laurentEval (R := R) u := by
    apply laurentEval_unique
    simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply,
      LaurentPolynomial.mapAlgHom_T, laurentEval_T_one]
  apply WithConv.ofConv_injective
  apply Algebra.TensorProduct.ext'
  intro s h
  simp only [AlgHom.baseChangePointsMulEquiv_apply_ofConv, AlgHom.liftEquiv_tmul,
    pointsHom_apply, BialgHom.mapDomain_apply, ofConv_toConv, AlgHom.comp_apply,
    BialgHom.coe_toAlgHom, BialgHom.baseChangeCocharacter_tmul, map_smul]
  exact congrArg (s • ·) (AlgHom.congr_fun hev (l h)).symm

/-- Base change carries the generic value of a cocharacter to the generic value of its
scalar extension. -/
theorem baseChangePointsMulEquiv_genericPoint (l : H →ₐc[R] LaurentPolynomial R) :
    AlgHom.baseChangePointsMulEquiv (k := R) (K := S) (A := H) (genericPoint A l) =
      genericPoint A (l.baseChangeCocharacter S) := by
  simp only [genericPoint_eq_pointsHom]
  exact baseChangePointsMulEquiv_pointsHom (S := S) l (LaurentPolynomial.genericUnit A)

/-- Constant Laurent-valued points commute with scalar extension. -/
theorem baseChangePointsMulEquiv_constPoint (g : WithConv (H →ₐ[R] A)) :
    AlgHom.baseChangePointsMulEquiv (k := R) (K := S) (A := H) (constPoint A g) =
      constPoint A (AlgHom.baseChangePointsMulEquiv (k := R) (K := S) (A := H) g) := by
  have hφ : (IsScalarTower.toAlgHom S A (LaurentPolynomial A)).restrictScalars R =
      IsScalarTower.toAlgHom R A (LaurentPolynomial A) := AlgHom.ext fun _ ↦ rfl
  rw [constPoint_apply, constPoint_apply]
  simpa only [AlgHom.mapValue_apply, hφ] using
    (AlgHom.mapValue_baseChangePointsMulEquiv
      (IsScalarTower.toAlgHom S A (LaurentPolynomial A)) g).symm

/-- Inclusion of polynomial-valued points commutes with scalar extension. -/
theorem baseChangePointsMulEquiv_ofPolyPoint (F : WithConv (H →ₐ[R] Polynomial A)) :
    AlgHom.baseChangePointsMulEquiv (k := R) (K := S) (A := H) (ofPolyPoint A F) =
      ofPolyPoint A (AlgHom.baseChangePointsMulEquiv (k := R) (K := S) (A := H) F) := by
  have hφ : (Polynomial.toLaurentAlg.restrictScalars S).restrictScalars R =
      (Polynomial.toLaurentAlg : Polynomial A →ₐ[A] LaurentPolynomial A).restrictScalars R :=
    AlgHom.ext fun _ ↦ rfl
  rw [ofPolyPoint_apply, ofPolyPoint_apply]
  simpa only [AlgHom.mapValue_apply, hφ] using
    (AlgHom.mapValue_baseChangePointsMulEquiv
      (Polynomial.toLaurentAlg.restrictScalars S) F).symm

/-- Evaluation at the origin commutes with scalar extension. -/
theorem baseChangePointsMulEquiv_evalZeroPoint (F : WithConv (H →ₐ[R] Polynomial A)) :
    AlgHom.baseChangePointsMulEquiv (k := R) (K := S) (A := H) (evalZeroPoint A F) =
      evalZeroPoint A (AlgHom.baseChangePointsMulEquiv (k := R) (K := S) (A := H) F) := by
  have hφ : ((Polynomial.aeval (R := A) (0 : A)).restrictScalars S).restrictScalars R =
      (Polynomial.aeval (R := A) (0 : A)).restrictScalars R := AlgHom.ext fun _ ↦ rfl
  rw [evalZeroPoint_apply, evalZeroPoint_apply]
  simpa only [AlgHom.mapValue_apply, hφ] using
    (AlgHom.mapValue_baseChangePointsMulEquiv
      ((Polynomial.aeval (R := A) (0 : A)).restrictScalars S) F).symm

end Bialgebra

variable [HopfAlgebra R H]

/-- Conjugation families commute with scalar extension. -/
theorem baseChangePointsMulEquiv_conjugate (l : H →ₐc[R] LaurentPolynomial R)
    (g : WithConv (H →ₐ[R] A)) :
    AlgHom.baseChangePointsMulEquiv (k := R) (K := S) (A := H) (conjugate A l g) =
      conjugate A (l.baseChangeCocharacter S)
        (AlgHom.baseChangePointsMulEquiv (k := R) (K := S) (A := H) g) := by
  simp only [conjugate_apply, map_mul, map_inv, baseChangePointsMulEquiv_genericPoint,
    baseChangePointsMulEquiv_constPoint]

/-- A point belongs to the dynamic parabolic exactly when its scalar extension does. -/
@[simp]
theorem baseChangePointsMulEquiv_mem_parabolic_iff (l : H →ₐc[R] LaurentPolynomial R)
    (g : WithConv (H →ₐ[R] A)) :
    AlgHom.baseChangePointsMulEquiv (k := R) (K := S) (A := H) g ∈
        parabolic A (l.baseChangeCocharacter S) ↔
      g ∈ parabolic A l := by
  simp only [mem_parabolic_iff]
  constructor
  · rintro ⟨F, hF⟩
    refine ⟨(AlgHom.baseChangePointsMulEquiv (k := R) (K := S) (A := H)).symm F, ?_⟩
    apply (AlgHom.baseChangePointsMulEquiv (k := R) (K := S) (A := H)
      (R := LaurentPolynomial A)).injective
    rw [baseChangePointsMulEquiv_ofPolyPoint, MulEquiv.apply_symm_apply,
      baseChangePointsMulEquiv_conjugate, hF]
  · rintro ⟨F, hF⟩
    refine ⟨AlgHom.baseChangePointsMulEquiv (k := R) (K := S) (A := H) F, ?_⟩
    rw [← baseChangePointsMulEquiv_ofPolyPoint, hF, baseChangePointsMulEquiv_conjugate]

/-- Polynomial extension of a conjugation family commutes with scalar extension. -/
theorem baseChangePointsMulEquiv_extend (l : H →ₐc[R] LaurentPolynomial R)
    (g : parabolic A l) :
    AlgHom.baseChangePointsMulEquiv (k := R) (K := S) (A := H) (extend A l g) =
      extend A (l.baseChangeCocharacter S)
        ⟨AlgHom.baseChangePointsMulEquiv (k := R) (K := S) (A := H) g.1,
          (baseChangePointsMulEquiv_mem_parabolic_iff l g.1).mpr g.2⟩ := by
  apply (extend_unique ?_).symm
  rw [← baseChangePointsMulEquiv_ofPolyPoint, ofPolyPoint_extend,
    baseChangePointsMulEquiv_conjugate]

/-- Taking the dynamic limit commutes with scalar extension. -/
theorem baseChangePointsMulEquiv_limit (l : H →ₐc[R] LaurentPolynomial R)
    (g : parabolic A l) :
    AlgHom.baseChangePointsMulEquiv (k := R) (K := S) (A := H) (limit A l g) =
      limit A (l.baseChangeCocharacter S)
        ⟨AlgHom.baseChangePointsMulEquiv (k := R) (K := S) (A := H) g.1,
          (baseChangePointsMulEquiv_mem_parabolic_iff l g.1).mpr g.2⟩ := by
  rw [limit_apply, limit_apply, baseChangePointsMulEquiv_evalZeroPoint,
    baseChangePointsMulEquiv_extend]

/-- A point belongs to the dynamic Levi exactly when its scalar extension does. -/
@[simp]
theorem baseChangePointsMulEquiv_mem_levi_iff (l : H →ₐc[R] LaurentPolynomial R)
    (g : WithConv (H →ₐ[R] A)) :
    AlgHom.baseChangePointsMulEquiv (k := R) (K := S) (A := H) g ∈
        levi A (l.baseChangeCocharacter S) ↔
      g ∈ levi A l := by
  rw [mem_levi_iff, mem_levi_iff, ← baseChangePointsMulEquiv_conjugate,
    ← baseChangePointsMulEquiv_constPoint]
  exact (AlgHom.baseChangePointsMulEquiv (k := R) (K := S) (A := H)
    (R := LaurentPolynomial A)).injective.eq_iff

/-- A point belongs to the dynamic unipotent subgroup exactly when its scalar extension does. -/
@[simp]
theorem baseChangePointsMulEquiv_mem_unipotent_iff (l : H →ₐc[R] LaurentPolynomial R)
    (g : WithConv (H →ₐ[R] A)) :
    AlgHom.baseChangePointsMulEquiv (k := R) (K := S) (A := H) g ∈
        unipotent A (l.baseChangeCocharacter S) ↔
      g ∈ unipotent A l := by
  rw [mem_unipotent_iff, mem_unipotent_iff]
  constructor
  · rintro ⟨hg, hlim⟩
    have hg' := (baseChangePointsMulEquiv_mem_parabolic_iff l g).mp hg
    refine ⟨hg', (AlgHom.baseChangePointsMulEquiv (k := R) (K := S) (A := H)).injective ?_⟩
    rw [baseChangePointsMulEquiv_limit, hlim, map_one]
  · rintro ⟨hg, hlim⟩
    refine ⟨(baseChangePointsMulEquiv_mem_parabolic_iff l g).mpr hg, ?_⟩
    rw [← baseChangePointsMulEquiv_limit l ⟨g, hg⟩, hlim, map_one]

end TauCeti.Cocharacter
