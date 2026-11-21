/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.ScalarChange
public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.StableEquivalent
public import TauCeti.LinearAlgebra.Matrix.Idempotent.Monoid

import TauCeti.Data.Matrix.Mul

/-!
# Projective `K₀` as the group completion of the idempotent monoid

For a ring `R`, not necessarily commutative, the finitely generated projective right `R`-modules
form the full subcategory `(TauCeti.finiteProjectiveModules Rᵐᵒᵖ).FullSubcategory` of
`ModuleCat Rᵐᵒᵖ`, whose split Grothendieck group `TauCeti.SplitK0` is the projective `K₀` of `R`.

Every finitely generated projective right `R`-module is isomorphic to the column range `e Rⁿ` of an
idempotent matrix `e ∈ Mₙ(R)`, two idempotent matrices have isomorphic column ranges if and only if
they are rectangularly algebraically equivalent, and block direct sums correspond to direct sums of
column ranges. Consequently:

* `TauCeti.IdempotentMonoid R` is canonically isomorphic as an additive commutative monoid to the
  monoid `TauCeti.ObjectCode` of isomorphism classes of finitely generated projective right
  `R`-modules under binary biproducts (`TauCeti.IdempotentMonoid.objectCodeAddEquiv`);
* its group completion `Algebra.GrothendieckAddGroup (TauCeti.IdempotentMonoid R)` is canonically
  isomorphic to `TauCeti.SplitK0 (TauCeti.finiteProjectiveModules Rᵐᵒᵖ).FullSubcategory`
  (`TauCeti.IdempotentMonoid.grothendieckAddGroupEquivSplitK0`), sending `[e]` to `[e Rⁿ]`;
* this comparison is natural with respect to extension of scalars along any ring homomorphism
  `f : R →+* S` (`TauCeti.IdempotentMonoid.map_toSplitK0` and
  `TauCeti.IdempotentMonoid.map_comp_grothendieckAddGroupEquivSplitK0`), through the base-change
  identification `(e Rⁿ) ⊗_R S ≃ f(e) Sⁿ` (`TauCeti.BalancedExtension.rangeMulVecBilinEquiv`);
* the image of `TauCeti.IdempotentMonoid R` in projective `K₀` is the algebraic positive cone of
  classes of actual finitely generated projective right `R`-modules
  (`TauCeti.IdempotentMonoid.mem_mrange_toSplitK0_iff`), without assuming cancellation in
  `IdempotentMonoid R` or antisymmetry of the cone;
* every class in projective `K₀` can be written in the standard form `[e] - [1ₘ]` by adding a
  finite free complement to the negative summand
  (`TauCeti.IdempotentMonoid.exists_eq_toSplitK0_sub_one`).

## Main definitions

* `TauCeti.BalancedExtension.rangeMulVecBilinEquiv`: base change of the column range of an
  idempotent matrix along `f : R →+* S`, identifying `(e R^ι) ⊗_R S` with `f(e) S^ι`.
* `TauCeti.FiniteProjectiveModules.ofIdempotent` and
  `TauCeti.FiniteProjectiveModules.ofIdempotentLinearEquiv`: the finitely generated projective right
  `R`-module `e R^ι` attached to an idempotent matrix `e` and its identification with the column
  range.
* `TauCeti.IdempotentMonoid.objectCodeAddEquiv`: the monoid isomorphism between `IdempotentMonoid R`
  and isomorphism classes of finitely generated projective right `R`-modules.
* `TauCeti.IdempotentMonoid.grothendieckAddGroupEquivSplitK0` and
  `TauCeti.IdempotentMonoid.toSplitK0`: the group-completion isomorphism with projective `K₀` and
  its monoid class map `[e] ↦ [e R^ι]`.

## Main results

* `TauCeti.IdempotentMonoid.map_toSplitK0`: naturality of `[e] ↦ [e R^ι]` under scalar extension.
* `TauCeti.IdempotentMonoid.toSplitK0_of_eq_toSplitK0_of_iff`: two idempotents define the same class
  in projective `K₀` if and only if they become algebraically equivalent after adding `1ₖ`.
* `TauCeti.IdempotentMonoid.mem_mrange_toSplitK0_iff`: the image of `toSplitK0` consists of the
  classes of finitely generated projective right `R`-modules.
* `TauCeti.IdempotentMonoid.exists_eq_toSplitK0_sub_one` and
  `TauCeti.IdempotentMonoid.toSplitK0_sub_one_eq_classOf_of_linearEquiv`: every projective `K₀`
  class has the form `[e] - [1ₘ]`, matching `FiniteProjectiveModules.classOf`.

## References

* J. Rosenberg, *Algebraic K-Theory and Its Applications*, §1.2.
* C. A. Weibel, *The K-book*, Chapter II, §2.
* B. Blackadar, *K-Theory for Operator Algebras*, §§1.7.2 and 4.6.
-/

public section

open CategoryTheory CategoryTheory.Limits LinearMap Matrix MulOpposite ZeroObject

universe u

namespace TauCeti

section BalancedExtension

namespace BalancedExtension

variable {R S : Type*} [Ring R] [Ring S] (f : R →+* S) {ι : Type*} [Fintype ι] {e : Matrix ι ι R}

/-- **Extension of scalars on the column range of an idempotent matrix.** Along a ring homomorphism
`f : R →+* S`, the right `S`-module extension of scalars of the column range `e R^ι` is canonically
isomorphic to the column range `f(e) S^ι` of `e.map f`. -/
noncomputable def rangeMulVecBilinEquiv (he : IsIdempotentElem e) :
    BalancedExtension (RingHom.op f) (range (e.mulVecBilin R Rᵐᵒᵖ)) ≃ₗ[Sᵐᵒᵖ]
      range ((e.map f).mulVecBilin S Sᵐᵒᵖ) :=
  (congr (RingHom.op f) e.rangeMulVecBilinEquivRangeVecMulLinear).trans <|
    (rangeVecMulLinearEquiv (RingHom.op f) he.transpose_map_op).trans <|
      (LinearEquiv.ofEq _ _ (congrArg (fun M ↦ range M.vecMulLinear)
        (transpose_map_op_map_ringHom_op e f))).trans
        (e.map f).rangeMulVecBilinEquivRangeVecMulLinear.symm

@[simp]
theorem coe_rangeMulVecBilinEquiv_tmul (he : IsIdempotentElem e) (s : Sᵐᵒᵖ)
    (v : range (e.mulVecBilin R Rᵐᵒᵖ)) :
    (rangeMulVecBilinEquiv f he (tmul (RingHom.op f) s v) : ι → S) =
      fun i ↦ f ((v : ι → R) i) * s.unop := by
  ext i
  simp [rangeMulVecBilinEquiv, LinearEquiv.trans_apply]

@[simp]
theorem rangeMulVecBilinEquiv_symm_apply (he : IsIdempotentElem e)
    (w : range ((e.map f).mulVecBilin S Sᵐᵒᵖ)) :
    (rangeMulVecBilinEquiv f he).symm w =
      ∑ j, tmul (RingHom.op f) (op ((w : ι → S) j)) ⟨e.col j, e.col_mem_range_mulVecBilin j⟩ := by
  rw [rangeMulVecBilinEquiv, LinearEquiv.trans_symm, LinearEquiv.trans_symm,
    LinearEquiv.trans_symm, LinearEquiv.symm_symm, congr_symm]
  simp only [LinearEquiv.trans_apply, rangeVecMulLinearEquiv_symm_apply, map_sum, congr_tmul]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hj : ((LinearEquiv.ofEq _ _ (congrArg (fun M ↦ range M.vecMulLinear)
      (transpose_map_op_map_ringHom_op e f))).symm
      ((e.map f).rangeMulVecBilinEquivRangeVecMulLinear w) : ι → Sᵐᵒᵖ) j = op ((w : ι → S) j) := by
    simp
  rw [hj]
  exact congrArg (tmul (RingHom.op f) _) (Subtype.ext (by simp; rfl))

end BalancedExtension

end BalancedExtension

section FiniteProjective

/-- The column range `e R^ι` of an idempotent matrix `e`, packaged as an object of the category of
finitely generated projective right `R`-modules via reindexing to `Fin (Fintype.card ι)`. -/
noncomputable def FiniteProjectiveModules.ofIdempotent {R : Type u} [Ring R] {ι : Type*}
    [Fintype ι] (e : Matrix ι ι R) (he : IsIdempotentElem e) :
    (finiteProjectiveModules Rᵐᵒᵖ).FullSubcategory :=
  let σ := Fintype.equivFin ι
  ⟨ModuleCat.of Rᵐᵒᵖ (range ((e.reindex σ σ).mulVecBilin R Rᵐᵒᵖ)),
    finiteProjectiveModules_iff.mpr ⟨inferInstance,
      (he.isAlgebraicEquivalent_reindex σ).isIdempotentElem_left.projective_range_mulVecBilin⟩⟩

/-- Canonical `Rᵐᵒᵖ`-linear equivalence between the underlying module of
`FiniteProjectiveModules.ofIdempotent e he` and the original column range `e R^ι`. -/
noncomputable def FiniteProjectiveModules.ofIdempotentLinearEquiv {R : Type u} [Ring R]
    {ι : Type*} [Fintype ι] (e : Matrix ι ι R) (he : IsIdempotentElem e) :
    (ofIdempotent e he).obj ≃ₗ[Rᵐᵒᵖ] range (e.mulVecBilin R Rᵐᵒᵖ) :=
  (e.rangeMulVecBilinReindexEquiv (Fintype.equivFin ι) (Fintype.equivFin ι)).symm

namespace IdempotentMonoid

section ObjectCode

variable (R : Type u) [Ring R]

private theorem objectCode_ofIdempotent_congr {ι κ : Type*} [Fintype ι] [Fintype κ]
    {e : Matrix ι ι R} {f : Matrix κ κ R} (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (h : e.IsAlgebraicEquivalent f) :
    objectCode.{u} (FiniteProjectiveModules.ofIdempotent e he) =
      objectCode.{u} (FiniteProjectiveModules.ofIdempotent f hf) := by
  obtain ⟨ψ⟩ := (isAlgebraicEquivalent_iff_nonempty_linearEquiv_range_mulVecBilin he hf).mp h
  exact objectCode_congr.{u} (ObjectProperty.isoMk (finiteProjectiveModules Rᵐᵒᵖ)
    (X := FiniteProjectiveModules.ofIdempotent e he)
    (Y := FiniteProjectiveModules.ofIdempotent f hf)
    ((FiniteProjectiveModules.ofIdempotentLinearEquiv e he).trans
      (ψ.trans (FiniteProjectiveModules.ofIdempotentLinearEquiv f hf).symm)).toModuleIso)

private noncomputable def objectCodeFun :
    IdempotentMonoid R → ObjectCode.{u} (finiteProjectiveModules Rᵐᵒᵖ).FullSubcategory :=
  lift (fun _ e he ↦ objectCode.{u} (FiniteProjectiveModules.ofIdempotent e he))
    fun _ _ _ _ he hg h ↦ objectCode_ofIdempotent_congr R he hg h

variable {R} in
private theorem objectCodeFun_of_linearEquiv {ι : Type*} [Fintype ι] {e : Matrix ι ι R}
    (he : IsIdempotentElem e) {P : (finiteProjectiveModules Rᵐᵒᵖ).FullSubcategory}
    (θ : P.obj ≃ₗ[Rᵐᵒᵖ] range (e.mulVecBilin R Rᵐᵒᵖ)) :
    objectCodeFun R (of e he) = objectCode.{u} P := by
  let σ := Fintype.equivFin ι
  let hre := (he.isAlgebraicEquivalent_reindex σ).isIdempotentElem_left
  let ψ := (FiniteProjectiveModules.ofIdempotentLinearEquiv (e.reindex σ σ) hre).trans
    (e.rangeMulVecBilinReindexEquiv σ σ).symm
  rw [← of_reindex e he σ, objectCodeFun, lift_of_fin]
  exact objectCode_congr.{u} (ObjectProperty.isoMk (finiteProjectiveModules Rᵐᵒᵖ)
    (X := FiniteProjectiveModules.ofIdempotent (e.reindex σ σ) hre)
    (Y := P) (ψ.trans θ.symm).toModuleIso)

variable {R} in
private theorem objectCodeFun_of {ι : Type*} [Fintype ι] (e : Matrix ι ι R)
    (he : IsIdempotentElem e) :
    objectCodeFun R (of e he) = objectCode.{u} (FiniteProjectiveModules.ofIdempotent e he) :=
  objectCodeFun_of_linearEquiv (P := FiniteProjectiveModules.ofIdempotent e he) he
    (FiniteProjectiveModules.ofIdempotentLinearEquiv e he)

private noncomputable def objectCodeHom :
    IdempotentMonoid R →+ ObjectCode.{u} (finiteProjectiveModules Rᵐᵒᵖ).FullSubcategory where
  toFun := objectCodeFun R
  map_zero' := by
    let Z := FiniteProjectiveModules.ofIdempotent (0 : Matrix (Fin 0) (Fin 0) R)
      IsIdempotentElem.zero
    have hsub : Subsingleton ((finiteProjectiveModules Rᵐᵒᵖ).ι.obj Z) :=
      (FiniteProjectiveModules.ofIdempotentLinearEquiv
        (0 : Matrix (Fin 0) (Fin 0) R) IsIdempotentElem.zero).toEquiv.subsingleton
    have hzero : IsZero Z :=
      IsZero.of_full_of_faithful_of_isZero (finiteProjectiveModules Rᵐᵒᵖ).ι Z
        (ModuleCat.isZero_of_subsingleton _)
    exact (objectCodeFun_of (0 : Matrix (Fin 0) (Fin 0) R) IsIdempotentElem.zero).trans
      ((objectCode_congr.{u} (hzero.iso (isZero_zero _))).trans objectCode_zero.{u})
  map_add' a b := by
    induction a using induction_on with | of m e he =>
    induction b using induction_on with | of n f hf =>
    rw [of_add_of, objectCodeFun_of e he, objectCodeFun_of f hf, ← objectCode_biprod.{u}]
    exact objectCodeFun_of_linearEquiv (he.fromBlocks_zero₁₂_zero₂₁ hf)
      (((FiniteProjectiveModules.biprodLinearEquiv _ _).trans
        ((FiniteProjectiveModules.ofIdempotentLinearEquiv e he).prodCongr
          (FiniteProjectiveModules.ofIdempotentLinearEquiv f hf))).trans
        (rangeMulVecBilinFromBlocksEquiv e f).symm)

private theorem objectCodeHom_apply (x : IdempotentMonoid R) :
    objectCodeHom R x = objectCodeFun R x :=
  (rfl)

private theorem objectCodeHom_bijective : Function.Bijective (objectCodeHom R) :=
  ⟨fun a b hab ↦ by
    induction a using induction_on with | of m e he =>
    induction b using induction_on with | of n f hf =>
    rw [objectCodeHom_apply R, objectCodeHom_apply R, objectCodeFun_of e he,
      objectCodeFun_of f hf, objectCode_eq_objectCode_iff.{u}] at hab
    obtain ⟨iso⟩ := hab
    exact of_eq_of_iff.mpr
      ((isAlgebraicEquivalent_iff_nonempty_linearEquiv_range_mulVecBilin he hf).mpr
        ⟨(FiniteProjectiveModules.ofIdempotentLinearEquiv e he).symm.trans
          (((finiteProjectiveModules Rᵐᵒᵖ).ι.mapIso iso).toLinearEquiv.trans
            (FiniteProjectiveModules.ofIdempotentLinearEquiv f hf))⟩),
  fun c ↦ by
    obtain ⟨P, rfl⟩ := objectCode_surjective.{u} c
    have : Module.Finite Rᵐᵒᵖ P.obj := (finiteProjectiveModules_iff.mp P.property).1
    have : Module.Projective Rᵐᵒᵖ P.obj := (finiteProjectiveModules_iff.mp P.property).2
    obtain ⟨n, e, he, ⟨θ⟩⟩ := Module.Finite.exists_linearEquiv_range_mulVecBilin R P.obj
    exact ⟨of e he, (objectCodeHom_apply R (of e he)).trans (objectCodeFun_of_linearEquiv he θ)⟩⟩

/-- **Idempotent presentation of the monoid of projective modules.** Sending the rectangular
equivalence class of `e` to the isomorphism class of its column range `e Rⁿ` is an isomorphism of
additive commutative monoids between `IdempotentMonoid R` and the isomorphism classes of finitely
generated projective right `R`-modules under binary biproducts. -/
noncomputable def objectCodeAddEquiv :
    IdempotentMonoid R ≃+ ObjectCode.{u} (finiteProjectiveModules Rᵐᵒᵖ).FullSubcategory :=
  AddEquiv.ofBijective (objectCodeHom R) (objectCodeHom_bijective R)

variable {R} in
/-- Evaluating `objectCodeAddEquiv` on `[e]` yields the code of any finitely generated projective
right `R`-module linearly isomorphic to `e R^ι`. -/
theorem objectCodeAddEquiv_of_linearEquiv {ι : Type*} [Fintype ι] {e : Matrix ι ι R}
    (he : IsIdempotentElem e) {P : (finiteProjectiveModules Rᵐᵒᵖ).FullSubcategory}
    (θ : P.obj ≃ₗ[Rᵐᵒᵖ] range (e.mulVecBilin R Rᵐᵒᵖ)) :
    objectCodeAddEquiv R (of e he) = objectCode.{u} P := by
  rw [objectCodeAddEquiv, AddEquiv.ofBijective_apply, objectCodeHom_apply R]
  exact objectCodeFun_of_linearEquiv he θ

variable {R} in
@[simp]
theorem objectCodeAddEquiv_of {ι : Type*} [Fintype ι] (e : Matrix ι ι R)
    (he : IsIdempotentElem e) :
    objectCodeAddEquiv R (of e he) = objectCode.{u} (FiniteProjectiveModules.ofIdempotent e he) :=
  objectCodeAddEquiv_of_linearEquiv (P := FiniteProjectiveModules.ofIdempotent e he) he
    (FiniteProjectiveModules.ofIdempotentLinearEquiv e he)

/-- **Projective `K₀` is the group completion of the idempotent monoid.** Group completion of
`IdempotentMonoid R` is canonically isomorphic to the split Grothendieck group of finitely generated
projective right `R`-modules. -/
noncomputable def grothendieckAddGroupEquivSplitK0 :
    Algebra.GrothendieckAddGroup (IdempotentMonoid R) ≃+
      SplitK0.{u} (finiteProjectiveModules Rᵐᵒᵖ).FullSubcategory :=
  ((AddLocalization.addMonoidOf (⊤ : AddSubmonoid (IdempotentMonoid R))).addEquivOfAddEquiv
      (AddLocalization.addMonoidOf
        (⊤ : AddSubmonoid (ObjectCode.{u} (finiteProjectiveModules Rᵐᵒᵖ).FullSubcategory)))
      (AddSubmonoid.map_equiv_top (objectCodeAddEquiv R))).trans
    (SplitK0.grothendieckAddGroupEquiv.{u} (finiteProjectiveModules Rᵐᵒᵖ).FullSubcategory)

/-- The canonical additive monoid homomorphism from `IdempotentMonoid R` to projective `K₀`,
sending `[e]` to the class `[e R^ι]` of its column range. -/
noncomputable def toSplitK0 :
    IdempotentMonoid R →+ SplitK0.{u} (finiteProjectiveModules Rᵐᵒᵖ).FullSubcategory :=
  (grothendieckAddGroupEquivSplitK0 R).toAddMonoidHom.comp Algebra.GrothendieckAddGroup.of

/-- The group-completion isomorphism restricts along `Algebra.GrothendieckAddGroup.of` to
`toSplitK0`. Not marked `@[simp]` because `Algebra.GrothendieckAddGroup.of` is reducible. -/
theorem grothendieckAddGroupEquivSplitK0_of (x : IdempotentMonoid R) :
    grothendieckAddGroupEquivSplitK0 R (Algebra.GrothendieckAddGroup.of x) = toSplitK0 R x :=
  (rfl)

@[simp]
theorem lift_toSplitK0 :
    Algebra.GrothendieckAddGroup.lift (toSplitK0 R) =
      (grothendieckAddGroupEquivSplitK0 R).toAddMonoidHom :=
  Algebra.GrothendieckAddGroup.lift.eq_symm_apply.mp
    (Algebra.GrothendieckAddGroup.lift_symm_apply _).symm

variable {R} in
/-- If a finitely generated projective right `R`-module `P` is linearly isomorphic to `e R^ι`, then
`toSplitK0` sends `[e]` to `[P]`. -/
theorem toSplitK0_of_linearEquiv {ι : Type*} [Fintype ι] {e : Matrix ι ι R}
    (he : IsIdempotentElem e) {P : (finiteProjectiveModules Rᵐᵒᵖ).FullSubcategory}
    (θ : P.obj ≃ₗ[Rᵐᵒᵖ] range (e.mulVecBilin R Rᵐᵒᵖ)) :
    toSplitK0 R (of e he) = SplitK0.of.{u} P := by
  rw [toSplitK0, AddMonoidHom.comp_apply, grothendieckAddGroupEquivSplitK0,
    AddEquiv.coe_toAddMonoidHom, AddEquiv.trans_apply]
  refine (congrArg (SplitK0.grothendieckAddGroupEquiv.{u} _) ?_).trans
    (SplitK0.grothendieckAddGroupEquiv_of_objectCode.{u} P)
  refine ((AddLocalization.addMonoidOf
    (⊤ : AddSubmonoid (IdempotentMonoid R))).addEquivOfAddEquiv_eq
    (AddSubmonoid.map_equiv_top (objectCodeAddEquiv R)) (of e he)).trans ?_
  exact congrArg Algebra.GrothendieckAddGroup.of (objectCodeAddEquiv_of_linearEquiv he θ)

variable {R} in
@[simp]
theorem toSplitK0_of {ι : Type*} [Fintype ι] (e : Matrix ι ι R) (he : IsIdempotentElem e) :
    toSplitK0 R (of e he) = SplitK0.of.{u} (FiniteProjectiveModules.ofIdempotent e he) :=
  toSplitK0_of_linearEquiv (P := FiniteProjectiveModules.ofIdempotent e he) he
    (FiniteProjectiveModules.ofIdempotentLinearEquiv e he)

/-- The class of the `m × m` identity matrix in projective `K₀` is `m` times the class of the
rank-one free right `R`-module. -/
theorem toSplitK0_of_one (m : ℕ) :
    toSplitK0 R (of (1 : Matrix (Fin m) (Fin m) R) IsIdempotentElem.one) =
      m • SplitK0.of.{u} ⟨ModuleCat.of Rᵐᵒᵖ Rᵐᵒᵖ,
        finiteProjectiveModules_iff.mpr ⟨inferInstance, inferInstance⟩⟩ := by
  rw [toSplitK0_of]
  exact SplitK0.of_eq_nsmul_of_linearEquiv_fin
    (X := FiniteProjectiveModules.ofIdempotent (1 : Matrix (Fin m) (Fin m) R) IsIdempotentElem.one)
    (R' := ⟨ModuleCat.of Rᵐᵒᵖ Rᵐᵒᵖ,
      finiteProjectiveModules_iff.mpr ⟨inferInstance, inferInstance⟩⟩)
    ((FiniteProjectiveModules.ofIdempotentLinearEquiv _ _).trans
      (rangeMulVecBilinOneEquiv (Fin m) R))
    (LinearEquiv.refl Rᵐᵒᵖ Rᵐᵒᵖ)

end ObjectCode

section Functoriality

variable {R S : Type u} [Ring R] [Ring S]

/-- **Naturality of `toSplitK0` under scalar extension.** Extending scalars of right modules along
`f : R →+* S` intertwines `toSplitK0` with entrywise application of `f` on `IdempotentMonoid`. -/
@[simp]
theorem map_toSplitK0 (f : R →+* S) (x : IdempotentMonoid R) :
    SplitK0.map.{u, u} (RingHom.op f).finiteProjectiveModulesExtendScalars (toSplitK0 R x) =
      toSplitK0 S (IdempotentMonoid.map f x) := by
  induction x using induction_on with | of n e he =>
  rw [toSplitK0_of, SplitK0.map_of,
    SplitK0.of_extendScalars_obj
      (Q := FiniteProjectiveModules.ofIdempotent (e.map f) (he.matrix_map f))
      ((BalancedExtension.congr (RingHom.op f)
        (FiniteProjectiveModules.ofIdempotentLinearEquiv e he)).trans
        ((BalancedExtension.rangeMulVecBilinEquiv f he).trans
          (FiniteProjectiveModules.ofIdempotentLinearEquiv (e.map f) (he.matrix_map f)).symm)),
    IdempotentMonoid.map_of, toSplitK0_of]

theorem toSplitK0_comp_map (f : R →+* S) :
    (toSplitK0 S).comp (IdempotentMonoid.map f) =
      (SplitK0.map.{u, u} (RingHom.op f).finiteProjectiveModulesExtendScalars).comp
        (toSplitK0 R) :=
  AddMonoidHom.ext fun x ↦ (map_toSplitK0 f x).symm

/-- **Naturality of the group-completion comparison.** Along `f : R →+* S`, the group-completion
homomorphism induced by `IdempotentMonoid.map f` corresponds under
`grothendieckAddGroupEquivSplitK0` to `SplitK0.map` of scalar extension. -/
theorem map_comp_grothendieckAddGroupEquivSplitK0 (f : R →+* S) :
    (SplitK0.map.{u, u} (RingHom.op f).finiteProjectiveModulesExtendScalars).comp
        (grothendieckAddGroupEquivSplitK0 R).toAddMonoidHom =
      (grothendieckAddGroupEquivSplitK0 S).toAddMonoidHom.comp
        (Algebra.GrothendieckAddGroup.lift
          (Algebra.GrothendieckAddGroup.of.comp (IdempotentMonoid.map f))) := by
  refine Algebra.GrothendieckAddGroup.lift.symm.injective ?_
  rw [Algebra.GrothendieckAddGroup.lift_symm_apply, AddMonoidHom.comp_assoc, ← toSplitK0,
    ← toSplitK0_comp_map, Algebra.GrothendieckAddGroup.lift_symm_apply, AddMonoidHom.comp_assoc,
    ← Algebra.GrothendieckAddGroup.lift_symm_apply, Equiv.symm_apply_apply,
    ← AddMonoidHom.comp_assoc, ← toSplitK0]

end Functoriality

section PresentationAndCone

variable {R : Type u} [Ring R]

/-- Two idempotent matrices have the same class in projective `K₀` if and only if their column
ranges are stably equivalent right `R`-modules. -/
theorem toSplitK0_of_eq_toSplitK0_of_iff_stableEquivalent {ι κ : Type*} [Fintype ι] [Fintype κ]
    {e : Matrix ι ι R} {f : Matrix κ κ R} {he : IsIdempotentElem e} {hf : IsIdempotentElem f} :
    toSplitK0 R (of e he) = toSplitK0 R (of f hf) ↔
      StableEquivalent Rᵐᵒᵖ (range (e.mulVecBilin R Rᵐᵒᵖ)) (range (f.mulVecBilin R Rᵐᵒᵖ)) := by
  rw [toSplitK0_of, toSplitK0_of, SplitK0.of_eq_of_iff_stableEquivalent]
  let ψe := FiniteProjectiveModules.ofIdempotentLinearEquiv e he
  let ψf := FiniteProjectiveModules.ofIdempotentLinearEquiv f hf
  exact ⟨fun h ↦ (StableEquivalent.of_equiv ψe.symm).trans (h.trans (.of_equiv ψf)),
    fun h ↦ (StableEquivalent.of_equiv ψe).trans (h.trans (.of_equiv ψf.symm))⟩

/-- **Equality of idempotent classes in projective `K₀`.** Two idempotent matrices have the same
class in projective `K₀` if and only if they become rectangularly algebraically equivalent after
adding a common identity block `1ₖ`. -/
theorem toSplitK0_of_eq_toSplitK0_of_iff {ι κ : Type*} [Fintype ι] [Fintype κ]
    {e : Matrix ι ι R} {f : Matrix κ κ R} {he : IsIdempotentElem e} {hf : IsIdempotentElem f} :
    toSplitK0 R (of e he) = toSplitK0 R (of f hf) ↔
      ∃ k : ℕ, (fromBlocks e 0 0 (1 : Matrix (Fin k) (Fin k) R)).IsAlgebraicEquivalent
        (fromBlocks f 0 0 (1 : Matrix (Fin k) (Fin k) R)) :=
  toSplitK0_of_eq_toSplitK0_of_iff_stableEquivalent.trans
    (stableEquivalent_range_mulVecBilin_iff he hf)

/-- **Algebraic positive cone of projective `K₀`.** The image submonoid of `IdempotentMonoid R` in
projective `K₀` consists precisely of the classes `[P]` of finitely generated projective right
`R`-modules. -/
theorem mem_mrange_toSplitK0_iff
    {x : SplitK0.{u} (finiteProjectiveModules Rᵐᵒᵖ).FullSubcategory} :
    x ∈ AddMonoidHom.mrange (toSplitK0 R) ↔
      ∃ P : (finiteProjectiveModules Rᵐᵒᵖ).FullSubcategory, x = SplitK0.of.{u} P := by
  constructor
  · rintro ⟨a, rfl⟩
    induction a using induction_on with | of n e he =>
    exact ⟨FiniteProjectiveModules.ofIdempotent e he, toSplitK0_of e he⟩
  · rintro ⟨P, rfl⟩
    have : Module.Finite Rᵐᵒᵖ P.obj := (finiteProjectiveModules_iff.mp P.property).1
    have : Module.Projective Rᵐᵒᵖ P.obj := (finiteProjectiveModules_iff.mp P.property).2
    obtain ⟨n, e, he, ⟨θ⟩⟩ := Module.Finite.exists_linearEquiv_range_mulVecBilin R P.obj
    exact ⟨of e he, toSplitK0_of_linearEquiv he θ⟩

/-- Subtracting `[1ₘ]` from `[e]` in projective `K₀` gives the relative class
`FiniteProjectiveModules.classOf Rᵐᵒᵖ P m = [P] - m[R]` of any finitely generated projective right
`R`-module `P` linearly isomorphic to `e R^ι`. -/
theorem toSplitK0_sub_one_eq_classOf_of_linearEquiv {ι : Type*} [Fintype ι] {e : Matrix ι ι R}
    (he : IsIdempotentElem e) {P : Type u} [AddCommGroup P] [Module Rᵐᵒᵖ P] [Module.Finite Rᵐᵒᵖ P]
    [Module.Projective Rᵐᵒᵖ P] (θ : P ≃ₗ[Rᵐᵒᵖ] range (e.mulVecBilin R Rᵐᵒᵖ)) (m : ℕ) :
    toSplitK0 R (of e he) -
        toSplitK0 R (of (1 : Matrix (Fin m) (Fin m) R) IsIdempotentElem.one) =
      FiniteProjectiveModules.classOf Rᵐᵒᵖ P m := by
  rw [toSplitK0_of_linearEquiv
      (P := ⟨ModuleCat.of Rᵐᵒᵖ P, finiteProjectiveModules_iff.mpr ⟨inferInstance, inferInstance⟩⟩)
      he θ,
    toSplitK0_of_one, FiniteProjectiveModules.classOf_def]

variable (R) in
/-- **Standard `[e] - [1ₘ]` presentation of projective `K₀`.** Every element of projective `K₀` can
be written as the difference `[e] - [1ₘ]` of the class of an idempotent matrix `e` and the class of
a finite identity matrix `1ₘ`. -/
theorem exists_eq_toSplitK0_sub_one
    (x : SplitK0.{u} (finiteProjectiveModules Rᵐᵒᵖ).FullSubcategory) :
    ∃ (n m : ℕ) (e : Matrix (Fin n) (Fin n) R) (he : IsIdempotentElem e),
      x = toSplitK0 R (of e he) -
        toSplitK0 R (of (1 : Matrix (Fin m) (Fin m) R) IsIdempotentElem.one) := by
  obtain ⟨P, Q, rfl⟩ := SplitK0.exists_eq_sub x
  have : Module.Finite Rᵐᵒᵖ Q.obj := (finiteProjectiveModules_iff.mp Q.property).1
  have : Module.Projective Rᵐᵒᵖ Q.obj := (finiteProjectiveModules_iff.mp Q.property).2
  -- Choose a complement `N` so `Q × N ≃ Rᵐ`, replacing `[P] - [Q]` by `[P ⊞ N] - [Rᵐ]`.
  obtain ⟨N, _, _, _, _, m, ⟨c⟩⟩ := Module.Projective.exists_prod_linearEquiv_fin Rᵐᵒᵖ Q.obj
  let Nobj : (finiteProjectiveModules Rᵐᵒᵖ).FullSubcategory :=
    ⟨ModuleCat.of Rᵐᵒᵖ N, finiteProjectiveModules_iff.mpr ⟨‹_›, ‹_›⟩⟩
  have hQN : SplitK0.of.{u}
      (FiniteProjectiveModules.ofIdempotent (1 : Matrix (Fin m) (Fin m) R) IsIdempotentElem.one) =
        SplitK0.of.{u} Q + SplitK0.of.{u} Nobj :=
    SplitK0.of_eq_add_of_linearEquiv_prod
      (X := FiniteProjectiveModules.ofIdempotent (1 : Matrix (Fin m) (Fin m) R)
        IsIdempotentElem.one)
      (P := Q) (Q := Nobj)
      (((FiniteProjectiveModules.ofIdempotentLinearEquiv _ _).trans
        (rangeMulVecBilinOneEquiv (Fin m) R)).trans c.symm)
  have : Module.Finite Rᵐᵒᵖ (P ⊞ Nobj).obj :=
    (finiteProjectiveModules_iff.mp (P ⊞ Nobj).property).1
  have : Module.Projective Rᵐᵒᵖ (P ⊞ Nobj).obj :=
    (finiteProjectiveModules_iff.mp (P ⊞ Nobj).property).2
  obtain ⟨n, e, he, ⟨θ⟩⟩ := Module.Finite.exists_linearEquiv_range_mulVecBilin R (P ⊞ Nobj).obj
  refine ⟨n, m, e, he, ?_⟩
  rw [toSplitK0_of_linearEquiv he θ, toSplitK0_of, SplitK0.of_biprod, hQN]
  abel

end PresentationAndCone

end IdempotentMonoid

end FiniteProjective

end TauCeti
