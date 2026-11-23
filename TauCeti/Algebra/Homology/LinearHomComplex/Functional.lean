/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.LinearHomComplex.Bidual
public import TauCeti.Algebra.Homology.LinearHomComplex.Curry
public import TauCeti.Algebra.Homology.LinearHomComplex.DualTensor
public import TauCeti.Algebra.Homology.LinearHomComplex.Tensor
public import TauCeti.Algebra.Homology.ModuleCat.Tensor

/-!
# Reading functionals on `A ⊗ B∨` as operators from `A` to `B`

Let `A` and `B` be cochain complexes of modules over a commutative ring `R`, with dual complexes
`A∨ = Hom(A, R[0])` and `B∨`, the `R`-linear Hom complexes into the tensor unit. An operation
from `A` to `B` is often recorded as a functional on the external kernel `A ⊗ B∨`, for instance
when it counts points of zero-dimensional moduli spaces whose orientation lines are tensor
products of the lines of the inputs with the duals of the lines of the outputs. This file
identifies such functionals with operators, with the Koszul signs of Mathlib's totalized tensor
product and Hom complex, and compares the two standard ways of doing so.

**Currying and the bidual map.** Currying identifies `(A ⊗ B∨)∨` with `Hom(A, B∨∨)`
(`TauCeti.linearHomComplexCurryIso`), and the chain-compatible bidual map
`j : B ⟶ B∨∨` (`CochainComplex.bidualHom`) is an isomorphism when every term of `B` is reflexive.
Together they give the isomorphism of complexes

`TauCeti.linearHomComplexTensorDualIso R A B : (A ⊗ B∨)∨ ≅ Hom(A, B)`.

On a functional `w` of degree `n`, an element `a` of `Aᵖ` and a form `φ` on `B^(p + n)`, the
operator `T` of `w` satisfies
`φ (T a) = (-1)^(p + n) w (a ⊗ φ)`
(`TauCeti.linearDualXEquiv_linearHomComplexTensorDualIso_hom_f_apply`); the sign is the sign of
`j` in degree `p + n`, and it is what makes `w ↦ T` commute with the differentials, so that
`linearHomComplexTensorDualIso` is an isomorphism of complexes. Degree-zero cocycles are morphisms
of complexes, so a chain map `A ⊗ B∨ ⟶ R[0]` is read as a chain map `A ⟶ B`
(`TauCeti.linearHomComplexTensorDualHomEquiv`).

**Through the dual of a tensor product.** The other reading inverts the comparison
`B∨∨ ⊗ A∨ ⟶ (A ⊗ B∨)∨` (`TauCeti.linearHomComplexDualDistrib`), then inverts `j` on the first
factor and contracts with the dual-tensor comparison `B ⊗ A∨ ⟶ Hom(A, B)`
(`TauCeti.linearHomComplexDualTensor`). The comparison of the dual of a tensor product is the
dual-tensor comparison into `B∨` followed by uncurrying
(`TauCeti.linearHomComplexDualDistrib_comp_linearHomComplexCurryIso_hom`). Consequently:

* `B∨ ⊗ A∨ ⟶ (A ⊗ B)∨` is an isomorphism for every `B` as soon as `A` has finitely many nonzero
  terms, all finitely generated projective (`TauCeti.isIso_linearHomComplexDualDistrib`);
* the two readings agree: the dual-tensor comparison is `j ⊗ A∨`, then the comparison and then
  `linearHomComplexTensorDualIso`
  (`TauCeti.linearHomComplexDualTensor_eq_comp_linearHomComplexTensorDualIso_hom`). So when the
  comparison is invertible, `linearHomComplexTensorDualIso` is its inverse, then the inverse of
  `j` on the first factor, then the dual-tensor comparison
  (`TauCeti.linearHomComplexTensorDualIso_hom_eq_inv_comp`), and that reading of a functional
  carries the sign given above.

## References

* C. A. Weibel, *An introduction to homological algebra*, Section 2.7, on the Hom and tensor
  complexes and their sign conventions.
* Mathlib's `TensorProduct.dualDistrib` and `dualTensorHom` for the degreewise comparisons.
-/

public section

open CategoryTheory Limits MonoidalCategory CochainComplex CochainComplex.HomComplex
open scoped TensorProduct

namespace TauCeti

universe v

variable {R : Type v} [CommRing R]

section DualDistrib

variable (R) (A B : CochainComplex (ModuleCat.{v} R) ℤ)

/-- **The dual of a tensor product through currying.** The comparison `B∨ ⊗ A∨ ⟶ (A ⊗ B)∨`,
`(g ⊗ f)(a ⊗ b) = f(a) g(b)`, followed by currying `(A ⊗ B)∨ ≅ Hom(A, B∨)`, is the dual-tensor
comparison `B∨ ⊗ A∨ ⟶ Hom(A, B∨)`, `g ⊗ f ↦ (a ↦ f(a) • g)`. -/
theorem linearHomComplexDualDistrib_comp_linearHomComplexCurryIso_hom :
    linearHomComplexDualDistrib R A B ≫ (linearHomComplexCurryIso A B (𝟙_ _)).hom =
      linearHomComplexDualTensor R A (linearHomComplex R B (𝟙_ _)) := by
  apply linearHomComplex_tensor_hom_ext
  intro i j n h g f
  rw [HomologicalComplex.comp_f, ← Category.assoc, ModuleCat.hom_comp, LinearMap.comp_apply,
    ι_linearHomComplexDualDistrib_tmul, linearHomComplexCurryIso_hom_f_apply]
  -- `HomologicalComplex.ιTensorObj` is the inclusion `HomologicalComplex.ιMapBifunctor` of the
  -- summand for the tensor product bifunctor.
  erw [linearHomComplexDualTensor_ιTensorObj_tmul]
  replace h : i + j = n := h
  refine Cochain.ext_linearHomComplex fun p q hpq x a b hab y => ?_
  rw [Cochain.curry_v_hom_apply_v_hom_apply _ hpq x hab y rfl]
  -- Both sides lie in the degree-`b` term of `R[0]`, which vanishes unless `b = 0`.
  by_cases hb : b = 0
  swap
  · exact (ModuleCat.subsingleton_of_isZero
      (HomologicalComplex.isZero_single_obj_X _ _ _ _ hb)).elim _ _
  subst hb
  by_cases hp : p + j = 0
  · obtain rfl : q = i := by omega
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp,
      Cochain.ιTensorObj_dualDistrib_v g f h p a (p + a) 0 0 0 rfl (by omega) hp (by omega),
      Cochain.comp_v _ _ _ p 0 q hp (by omega), cochainFromTensorUnitLinearEquiv_symm_apply,
      Cochain.fromSingleMk_v]
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.MonoidalCategory.tensorHom_tmul,
      ModuleCat.hom_ofHom, LinearMap.toSpanSingleton_apply]
    rw [Cochain.smul_linearHomComplex_v, ModuleCat.hom_smul, LinearMap.smul_apply]
    exact leftUnitor_hom_f_zero_ιTensorObj_tmul _ _
  · -- The form `f` vanishes on `Aᵖ`, whose image lies in a zero term of `R[0]`.
    have hf : f.v p (p + j) rfl = 0 :=
      (HomologicalComplex.isZero_single_obj_X _ _ _ _ hp).eq_of_tgt _ _
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp,
      Cochain.ιTensorObj_dualDistrib_v g f h p a (p + a) 0 (p + j) (a + i) rfl (by omega) rfl rfl,
      Cochain.comp_v _ _ _ p (p + j) q rfl (by omega), hf]
    simp

variable [∀ i, Module.Finite R (A.X i)] [∀ i, Module.Projective R (A.X i)]

/-- **The dual of a tensor product.** If `A` has only finitely many nonzero terms, all finitely
generated projective, then the comparison `B∨ ⊗ A∨ ⟶ (A ⊗ B)∨` is an isomorphism of complexes for
every `B`. -/
theorem isIso_linearHomComplexDualDistrib (S : Finset ℤ) (hS : ∀ i ∉ S, IsZero (A.X i)) :
    IsIso (linearHomComplexDualDistrib R A B) := by
  have := isIso_linearHomComplexDualTensor A (linearHomComplex R B (𝟙_ _)) S hS
  rw [← linearHomComplexDualDistrib_comp_linearHomComplexCurryIso_hom] at this
  exact IsIso.of_isIso_comp_right _ (linearHomComplexCurryIso A B (𝟙_ _)).hom

/-- The comparison `B∨ ⊗ A∨ ⟶ (A ⊗ B)∨` is an isomorphism of complexes when `A` is bounded with
finitely generated projective terms. -/
theorem isIso_linearHomComplexDualDistrib_of_isStrictlyGE_of_isStrictlyLE (a b : ℤ)
    [CochainComplex.IsStrictlyGE A a] [CochainComplex.IsStrictlyLE A b] :
    IsIso (linearHomComplexDualDistrib R A B) := by
  have := isIso_linearHomComplexDualTensor_of_isStrictlyGE_of_isStrictlyLE A
    (linearHomComplex R B (𝟙_ _)) a b
  rw [← linearHomComplexDualDistrib_comp_linearHomComplexCurryIso_hom] at this
  exact IsIso.of_isIso_comp_right _ (linearHomComplexCurryIso A B (𝟙_ _)).hom

end DualDistrib

section TensorDual

variable (R) (A B : CochainComplex (ModuleCat.{v} R) ℤ)

variable [∀ p, Module.IsReflexive R (B.X p)]

/-- **Functionals on `A ⊗ B∨` are operators from `A` to `B`.** When every term of `B` is
reflexive, currying `(A ⊗ B∨)∨ ≅ Hom(A, B∨∨)` followed by the inverse of the chain-compatible
bidual map `j : B ≅ B∨∨` is an isomorphism of complexes `(A ⊗ B∨)∨ ≅ Hom(A, B)`. On elements it
is characterized by `TauCeti.linearDualXEquiv_linearHomComplexTensorDualIso_hom_f_apply`. -/
noncomputable def linearHomComplexTensorDualIso :
    linearDual R (A ⊗ linearDual R B) ≅ linearHomComplex R A B :=
  linearHomComplexCurryIso A (linearDual R B) (𝟙_ _) ≪≫
    ((linearHomComplexFunctor R).obj (.op A)).mapIso (asIso (bidualHom B)).symm

/-- `TauCeti.linearHomComplexTensorDualIso` is currying followed by postcomposition with the
inverse of the bidual map. -/
theorem linearHomComplexTensorDualIso_hom :
    (linearHomComplexTensorDualIso R A B).hom =
      (linearHomComplexCurryIso A (linearDual R B) (𝟙_ _)).hom ≫
        linearHomComplexPostcomp R A (inv (bidualHom B)) :=
  (rfl)

/-- The inverse of `TauCeti.linearHomComplexTensorDualIso` is postcomposition with the bidual
map followed by uncurrying. -/
theorem linearHomComplexTensorDualIso_inv :
    (linearHomComplexTensorDualIso R A B).inv =
      linearHomComplexPostcomp R A (bidualHom B) ≫
        (linearHomComplexCurryIso A (linearDual R B) (𝟙_ _)).inv :=
  (rfl)

variable {R A B}

/-- **The sign of the operator of a functional.** The operator `T` of a functional `w` of degree
`n` on `A ⊗ B∨` satisfies `φ (T a) = (-1)^(p + n) w (a ⊗ φ)` for `a` in `Aᵖ` and a form `φ` on
`B^(p + n)`, of degree `q = -(p + n)`. -/
theorem linearDualXEquiv_linearHomComplexTensorDualIso_hom_f_apply {n p q : ℤ} (hpq : p + n + q = 0)
    (w : (linearDual R (A ⊗ linearDual R B)).X n) (a : A.X p) (φ : (linearDual R B).X q) :
    linearDualXEquiv B hpq φ
        (((((linearHomComplexTensorDualIso R A B).hom.f n).hom w : Cochain A B n).v p (p + n)
          rfl).hom a) =
      (p + n).negOnePow • linearDualXEquiv (A ⊗ linearDual R B) (by omega : p + q + n = 0) w
        ((HomologicalComplex.ιTensorObj A (linearDual R B) p q (p + q) rfl).hom (a ⊗ₜ φ)) := by
  -- `T a` is the inverse of the bidual map applied to the curried functional `φ ↦ w (a ⊗ φ)`.
  rw [linearHomComplexTensorDualIso_hom, HomologicalComplex.comp_f, ModuleCat.hom_comp,
    LinearMap.comp_apply, linearHomComplexCurryIso_hom_f_apply, linearHomComplexPostcomp_f_apply,
    Cochain.comp_zero_cochain_v, Cochain.ofHom_v, ModuleCat.hom_comp, LinearMap.comp_apply,
    linearDualXEquiv_inv_bidualHom_f_apply, linearDualXEquiv_apply, Cochain.toSingleEquiv_apply,
    ModuleCat.hom_comp, LinearMap.comp_apply, Cochain.curry_v_hom_apply_v_hom_apply _ rfl a _ φ rfl,
    linearDualXEquiv_apply, Cochain.toSingleEquiv_apply, ModuleCat.hom_comp, LinearMap.comp_apply]

/-- **The functional of an operator.** The functional `w` of an operator `T` of degree `n` from
`A` to `B` takes the value `w (a ⊗ φ) = (-1)^(p + n) φ (T a)` on `a` in `Aᵖ` and a form `φ` on
`B^(p + n)`. -/
@[simp]
theorem linearDualXEquiv_linearHomComplexTensorDualIso_inv_f_apply {n p q : ℤ} (hpq : p + n + q = 0)
    (T : (linearHomComplex R A B).X n) (a : A.X p) (φ : (linearDual R B).X q) :
    (dsimp% only [linearHomComplex_X]
      linearDualXEquiv (A ⊗ linearDual R B) (by omega : p + q + n = 0)
        (((linearHomComplexTensorDualIso R A B).inv.f n).hom T)
        ((HomologicalComplex.ιTensorObj A (linearDual R B) p q (p + q) rfl).hom (a ⊗ₜ φ))) =
      (p + n).negOnePow •
        linearDualXEquiv B hpq φ (((T : Cochain A B n).v p (p + n) rfl).hom a) := by
  have := linearDualXEquiv_linearHomComplexTensorDualIso_hom_f_apply hpq
    (((linearHomComplexTensorDualIso R A B).inv.f n).hom T) a φ
  have hT : ((linearHomComplexTensorDualIso R A B).hom.f n).hom
      (((linearHomComplexTensorDualIso R A B).inv.f n).hom T) = T :=
    Iso.inv_hom_id_apply (HomologicalComplex.Hom.isoApp (linearHomComplexTensorDualIso R A B) n) T
  rw [hT] at this
  rw [this, smul_smul, Int.units_mul_self, one_smul]

variable (R A B)

/-- **The two readings of a functional agree.** The dual-tensor comparison `B ⊗ A∨ ⟶ Hom(A, B)`
is the bidual map `j` on the first factor, then the comparison `B∨∨ ⊗ A∨ ⟶ (A ⊗ B∨)∨`, then
`TauCeti.linearHomComplexTensorDualIso`. -/
theorem linearHomComplexDualTensor_eq_comp_linearHomComplexTensorDualIso_hom :
    linearHomComplexDualTensor R A B =
      bidualHom B ▷ linearHomComplex R A (𝟙_ _) ≫
        linearHomComplexDualDistrib R A (linearDual R B) ≫
          (linearHomComplexTensorDualIso R A B).hom := by
  rw [linearHomComplexTensorDualIso_hom, ← Category.assoc, ← Category.assoc,
    Category.assoc _ _ (linearHomComplexCurryIso _ _ _).hom,
    linearHomComplexDualDistrib_comp_linearHomComplexCurryIso_hom,
    -- The goal names `B∨∨` as `Hom(B∨, R[0])`, not as `linearDual R B∨`.
    linearHomComplexDualTensor_naturality_target (B₂ := linearHomComplex R (linearDual R B) (𝟙_ _))
      A (bidualHom B), Category.assoc, ← linearHomComplexPostcomp_comp, IsIso.hom_inv_id,
    linearHomComplexPostcomp_id, Category.comp_id]

/-- **Reading a functional through the dual of a tensor product.** When the comparison
`B∨∨ ⊗ A∨ ⟶ (A ⊗ B∨)∨` is an isomorphism, for instance when `A` has finitely many nonzero terms,
all finitely generated projective (`TauCeti.isIso_linearHomComplexDualDistrib`), the isomorphism
`TauCeti.linearHomComplexTensorDualIso` is its inverse, followed by the inverse of the bidual map
`j` on the first factor and the dual-tensor comparison `B ⊗ A∨ ⟶ Hom(A, B)`. -/
theorem linearHomComplexTensorDualIso_hom_eq_inv_comp
    [IsIso (linearHomComplexDualDistrib R A (linearDual R B))] :
    (linearHomComplexTensorDualIso R A B).hom =
      inv (linearHomComplexDualDistrib R A (linearDual R B)) ≫
        inv (bidualHom B) ▷ linearHomComplex R A (𝟙_ _) ≫ linearHomComplexDualTensor R A B := by
  rw [linearHomComplexDualTensor_eq_comp_linearHomComplexTensorDualIso_hom,
    ← Category.assoc (inv (bidualHom B) ▷ _), ← comp_whiskerRight, IsIso.inv_hom_id,
    id_whiskerRight, Category.id_comp, IsIso.inv_hom_id_assoc]

/-- **Chain maps out of `A ⊗ B∨` into `R[0]` are chain maps from `A` to `B`**, when every term of
`B` is reflexive: currying, followed by the inverse of the chain-compatible bidual map. On
elements it is characterized by
`TauCeti.linearDualXEquiv_linearHomComplexTensorDualHomEquiv_f_apply`. -/
noncomputable def linearHomComplexTensorDualHomEquiv :
    (A ⊗ linearDual R B ⟶ 𝟙_ _) ≃ (A ⟶ B) :=
  (linearHomComplexHomEquiv A (linearDual R B) (𝟙_ _)).trans
    ((Iso.refl A).homCongr (asIso (bidualHom B)).symm)

variable {R A B}

/-- `TauCeti.linearHomComplexTensorDualHomEquiv` is the curried morphism followed by the inverse
of the bidual map. -/
theorem linearHomComplexTensorDualHomEquiv_apply (F : A ⊗ linearDual R B ⟶ 𝟙_ _) :
    linearHomComplexTensorDualHomEquiv R A B F =
      linearHomComplexHomEquiv A (linearDual R B) (𝟙_ _) F ≫ inv (bidualHom B) := by
  simp [linearHomComplexTensorDualHomEquiv]

/-- `TauCeti.linearHomComplexTensorDualHomEquiv` sends a chain map `T : A ⟶ B` back to the
uncurried form of `T` followed by the bidual map. -/
theorem linearHomComplexTensorDualHomEquiv_symm_apply (T : A ⟶ B) :
    (linearHomComplexTensorDualHomEquiv R A B).symm T =
      (linearHomComplexHomEquiv A (linearDual R B) (𝟙_ _)).symm (T ≫ bidualHom B) := by
  simp [linearHomComplexTensorDualHomEquiv]

/-- The chain map `T` read from a chain map `F : A ⊗ B∨ ⟶ R[0]` satisfies
`φ (T a) = (-1)^p F (a ⊗ φ)` for `a` in `Aᵖ` and a form `φ` on `Bᵖ`, of degree `-p`. -/
@[simp]
theorem linearDualXEquiv_linearHomComplexTensorDualHomEquiv_f_apply
    (F : A ⊗ linearDual R B ⟶ 𝟙_ _) {p : ℤ} (a : A.X p) (φ : (linearDual R B).X (-p)) :
    linearDualXEquiv B (add_neg_cancel p) φ
        (((linearHomComplexTensorDualHomEquiv R A B F).f p).hom a) =
      p.negOnePow • (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat.{v} R))).hom.hom
        ((F.f 0).hom ((HomologicalComplex.ιTensorObj A (linearDual R B) p (-p) 0
          (add_neg_cancel p)).hom (a ⊗ₜ φ))) := by
  rw [linearHomComplexTensorDualHomEquiv_apply, HomologicalComplex.comp_f, ModuleCat.hom_comp,
    LinearMap.comp_apply, linearDualXEquiv_inv_bidualHom_f_apply, linearDualXEquiv_apply,
    Cochain.toSingleEquiv_apply, ModuleCat.hom_comp, LinearMap.comp_apply]
  exact congrArg _ (linearHomComplexHomEquiv_f_hom_apply_v_hom_apply F a (neg_add_cancel p) φ)

/-- The chain map `F : A ⊗ B∨ ⟶ R[0]` of a chain map `T : A ⟶ B` takes the value
`F (a ⊗ φ) = (-1)^p φ (T a)` on `a` in `Aᵖ` and a form `φ` on `Bᵖ`, of degree `-p`. -/
@[simp]
theorem singleObjXSelf_hom_linearHomComplexTensorDualHomEquiv_symm_f_apply (T : A ⟶ B) {p : ℤ}
    (a : A.X p) (φ : (linearDual R B).X (-p)) :
    (dsimp% only [linearHomComplex_X]
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat.{v} R))).hom.hom
        ((((linearHomComplexTensorDualHomEquiv R A B).symm T).f 0).hom
          ((HomologicalComplex.ιTensorObj A (linearDual R B) p (-p) 0
            (add_neg_cancel p)).hom (a ⊗ₜ φ)))) =
      p.negOnePow • linearDualXEquiv B (add_neg_cancel p) φ ((T.f p).hom a) := by
  have := linearDualXEquiv_linearHomComplexTensorDualHomEquiv_f_apply
    ((linearHomComplexTensorDualHomEquiv R A B).symm T) a φ
  rw [Equiv.apply_symm_apply] at this
  rw [this, smul_smul, Int.units_mul_self, one_smul]

end TensorDual

end TauCeti
