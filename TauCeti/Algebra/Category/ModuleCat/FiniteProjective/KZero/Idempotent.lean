/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Unique
public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.KZero.Defs
public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.ScalarChange
public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.StableEquivalent
public import TauCeti.LinearAlgebra.Matrix.Idempotent.Monoid

import TauCeti.Algebra.Category.ModuleCat.CartanMap.Morita
import TauCeti.RingTheory.GrothendieckRing
import TauCeti.RingTheory.Idempotents.Projective

/-!
# The idempotent monoid and projective `K₀`

Building on `TauCeti.IdempotentMonoid` in `TauCeti.LinearAlgebra.Matrix.Idempotent.Monoid`, this
file proves `objectCodeAddEquiv : IdempotentMonoid R ≃+ ObjectCode (FiniteProjectiveRight R)` and
identifies the group completions of `V(R)` with split projective `K₀` for right modules
(`kZeroEquiv`, `kZeroEquiv_of_mk`, `kZeroEquiv_of_mk_one`, `exists_kZeroEquiv_sub_nsmul_eq`,
`toKZero`, `toKZero_mk`, `toKZero_mk_one`, `map_toKZero`, `map_comp_kZeroEquiv`,
`toKZero_mk_eq_toKZero_mk_iff`, `mem_mrange_toKZero_iff`,
`toKZero_mk_sub_toKZero_mk_one_eq_classOf_of_linearEquiv`) and left modules via `opEquiv`
(`splitK0Equiv`, `toSplitK0`, `splitK0Equiv_of_mk`), via `ofIdempotent` and
`extendScalarsOfIdempotentIso`. The principal right ideal `eR` of an idempotent `e`
(`TauCeti.KZero.principalRightIdeal`) has the class of the `1 × 1` matrix `(e)`, the image of `e`
under `Matrix.uniqueRingEquiv.symm` (`TauCeti.IdempotentMonoid.toKZero_mk_of_unique`).

## References

* J. Rosenberg, *Algebraic K-Theory and Its Applications*, §1.2.
* C. A. Weibel, *The K-book*, Chapter II, §2, the definition of `K₀` by idempotent matrices.
* B. Blackadar, *K-Theory for Operator Algebras*, §§1.7.2 and 4.6.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits _root_.LinearMap Matrix MulOpposite _root_.Algebra

namespace TauCeti

universe u

section KZero

/-- The column range `e R^ι` of an idempotent matrix `e`, packaged as an object of
`FiniteProjectiveRight R` via reindexing to `Fin (Fintype.card ι)`. -/
@[expose] noncomputable def FiniteProjectiveModules.ofIdempotent {R : Type u} [Ring R]
    {ι : Type*} [Fintype ι] (e : Matrix ι ι R) (he : IsIdempotentElem e) :
    FiniteProjectiveRight R :=
  let σ := Fintype.equivFin ι
  ⟨ModuleCat.of Rᵐᵒᵖ (range ((e.reindex σ σ).mulVecBilin R Rᵐᵒᵖ)),
    finiteProjectiveModules_iff.mpr ⟨inferInstance,
      (idempotentEquivalent_submatrix he
        σ.symm).isIdempotentElem_right.projective_range_mulVecBilin⟩⟩

/-- Canonical `Rᵐᵒᵖ`-linear equivalence between the underlying module of
`FiniteProjectiveModules.ofIdempotent e he` and the original column range `e R^ι`. -/
noncomputable def FiniteProjectiveModules.ofIdempotentLinearEquiv {R : Type u} [Ring R]
    {ι : Type*} [Fintype ι] (e : Matrix ι ι R) (he : IsIdempotentElem e) :
    (ofIdempotent e he).obj ≃ₗ[Rᵐᵒᵖ] range (e.mulVecBilin R Rᵐᵒᵖ) :=
  (e.rangeMulVecBilinSubmatrixEquiv (Fintype.equivFin ι).symm (Fintype.equivFin ι).symm).symm

@[simp]
theorem FiniteProjectiveModules.coe_ofIdempotentLinearEquiv_apply {R : Type u} [Ring R]
    {ι : Type*} [Fintype ι] (e : Matrix ι ι R) (he : IsIdempotentElem e)
    (v : (ofIdempotent e he).obj) :
    (ofIdempotentLinearEquiv e he v : ι → R) = v.val ∘ Fintype.equivFin ι :=
  coe_rangeMulVecBilinSubmatrixEquiv_symm_apply e _ _ v

@[simp]
theorem FiniteProjectiveModules.coe_ofIdempotentLinearEquiv_symm_apply {R : Type u} [Ring R]
    {ι : Type*} [Fintype ι] (e : Matrix ι ι R) (he : IsIdempotentElem e)
    (w : range (e.mulVecBilin R Rᵐᵒᵖ)) :
    ((ofIdempotentLinearEquiv e he).symm w).val = (w : ι → R) ∘ (Fintype.equivFin ι).symm :=
  coe_rangeMulVecBilinSubmatrixEquiv_apply e _ _ w

namespace IdempotentMonoid

variable (R : Type u) [Ring R]

private theorem objectCode_ofIdempotent_congr {ι κ : Type*} [Fintype ι] [Fintype κ]
    {e : Matrix ι ι R} {f : Matrix κ κ R} (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (h : IdempotentEquivalent e f) :
    objectCode.{u} (FiniteProjectiveModules.ofIdempotent e he) =
      objectCode.{u} (FiniteProjectiveModules.ofIdempotent f hf) := by
  obtain ⟨ψ⟩ := (nonempty_linearEquiv_range_mulVecBilin_iff he hf).mpr h
  exact objectCode_congr.{u} (ObjectProperty.isoMk (finiteProjectiveModules Rᵐᵒᵖ)
    (X := FiniteProjectiveModules.ofIdempotent e he)
    (Y := FiniteProjectiveModules.ofIdempotent f hf)
    ((FiniteProjectiveModules.ofIdempotentLinearEquiv e he).trans
      (ψ.trans (FiniteProjectiveModules.ofIdempotentLinearEquiv f hf).symm)).toModuleIso)

private def objectCodeFun :
    IdempotentMonoid R → ObjectCode.{u} (FiniteProjectiveRight R) :=
  lift (fun e he ↦ objectCode.{u} (FiniteProjectiveModules.ofIdempotent e he))
    fun _ _ he hg h ↦ objectCode_ofIdempotent_congr R he hg h

variable {R} in
private theorem objectCodeFun_mk_eq_of_linearEquiv {ι : Type*} [Fintype ι] {e : Matrix ι ι R}
    (he : IsIdempotentElem e) {P : FiniteProjectiveRight R}
    (θ : P.obj ≃ₗ[Rᵐᵒᵖ] range (e.mulVecBilin R Rᵐᵒᵖ)) :
    objectCodeFun R (mk e he) = objectCode.{u} P := by
  let σ := (Fintype.equivFin ι).symm
  let hsub := (idempotentEquivalent_submatrix he σ).isIdempotentElem_right
  refine lift_mk_eq (hF := fun _ _ he hg h ↦ objectCode_ofIdempotent_congr R he hg h) e he ?_
  exact objectCode_congr.{u} (ObjectProperty.isoMk (finiteProjectiveModules Rᵐᵒᵖ)
    (X := FiniteProjectiveModules.ofIdempotent (e.submatrix σ σ) hsub) (Y := P)
    ((FiniteProjectiveModules.ofIdempotentLinearEquiv (e.submatrix σ σ) hsub).trans
      ((e.rangeMulVecBilinSubmatrixEquiv σ σ).symm.trans θ.symm)).toModuleIso)

variable {R} in
private theorem objectCodeFun_mk {ι : Type*} [Fintype ι] (e : Matrix ι ι R)
    (he : IsIdempotentElem e) :
    objectCodeFun R (mk e he) = objectCode.{u} (FiniteProjectiveModules.ofIdempotent e he) :=
  objectCodeFun_mk_eq_of_linearEquiv (P := FiniteProjectiveModules.ofIdempotent e he) he
    (FiniteProjectiveModules.ofIdempotentLinearEquiv e he)

private def objectCodeHom : IdempotentMonoid R →+ ObjectCode.{u} (FiniteProjectiveRight R) where
  toFun := objectCodeFun R
  map_zero' := by
    let Z := FiniteProjectiveModules.ofIdempotent (0 : Matrix (Fin 0) (Fin 0) R) .zero
    have : Subsingleton ((finiteProjectiveModules Rᵐᵒᵖ).ι.obj Z) :=
      (FiniteProjectiveModules.ofIdempotentLinearEquiv
        (0 : Matrix (Fin 0) (Fin 0) R) .zero).toEquiv.subsingleton
    have hzero : Limits.IsZero Z := Limits.IsZero.of_full_of_faithful_of_isZero
      (finiteProjectiveModules Rᵐᵒᵖ).ι Z (ModuleCat.isZero_of_subsingleton _)
    exact (objectCodeFun_mk (0 : Matrix (Fin 0) (Fin 0) R) .zero).trans
      ((objectCode_congr.{u} (hzero.iso (Limits.isZero_zero _))).trans objectCode_zero.{u})
  map_add' a b := by
    induction a using ind with | mk m e he =>
    induction b using ind with | mk n f hf =>
    rw [mk_add_mk, objectCodeFun_mk e he, objectCodeFun_mk f hf, ← objectCode_biprod.{u}]
    exact objectCodeFun_mk_eq_of_linearEquiv (he.fromBlocks_zero₁₂_zero₂₁ hf)
      (((FiniteProjectiveModules.biprodLinearEquiv _ _).trans
        ((FiniteProjectiveModules.ofIdempotentLinearEquiv e he).prodCongr
          (FiniteProjectiveModules.ofIdempotentLinearEquiv f hf))).trans
        (rangeMulVecBilinFromBlocksEquiv e f).symm)

private theorem objectCodeHom_apply (x : IdempotentMonoid R) :
    objectCodeHom R x = objectCodeFun R x :=
  rfl

private theorem objectCodeHom_bijective : Function.Bijective (objectCodeHom R) :=
  ⟨fun a b hab ↦ by
    induction a using ind with | mk m e he =>
    induction b using ind with | mk n f hf =>
    rw [objectCodeHom_apply, objectCodeHom_apply, objectCodeFun_mk e he, objectCodeFun_mk f hf,
      objectCode_eq_objectCode_iff.{u}] at hab
    obtain ⟨iso⟩ := hab
    exact (mk_eq_mk_iff he hf).mpr ((nonempty_linearEquiv_range_mulVecBilin_iff he hf).mp
      ⟨(FiniteProjectiveModules.ofIdempotentLinearEquiv e he).symm.trans
        (((finiteProjectiveModules Rᵐᵒᵖ).ι.mapIso iso).toLinearEquiv.trans
          (FiniteProjectiveModules.ofIdempotentLinearEquiv f hf))⟩),
  fun c ↦ by
    obtain ⟨P, rfl⟩ := objectCode_surjective.{u} c
    have := (finiteProjectiveModules_iff.mp P.property).1
    have := (finiteProjectiveModules_iff.mp P.property).2
    obtain ⟨n, e, he, ⟨θ⟩⟩ := Module.Finite.exists_linearEquiv_range_mulVecBilin R P.obj
    exact ⟨mk e he, objectCodeFun_mk_eq_of_linearEquiv he θ⟩⟩

/-- **Idempotent presentation of the monoid of projective modules.** `[e] ↦ [e Rⁿ]` is an
additive isomorphism `IdempotentMonoid R ≃+ ObjectCode (FiniteProjectiveRight R)`. -/
def objectCodeAddEquiv : IdempotentMonoid R ≃+ ObjectCode.{u} (FiniteProjectiveRight R) :=
  AddEquiv.ofBijective (objectCodeHom R) (objectCodeHom_bijective R)

variable {R} in
/-- Evaluating `objectCodeAddEquiv` on `[e]` yields `objectCode P` for any `P ≃ₗ[Rᵐᵒᵖ] e R^ι`. -/
theorem objectCodeAddEquiv_mk_eq_of_linearEquiv {ι : Type*} [Fintype ι] {e : Matrix ι ι R}
    (he : IsIdempotentElem e) {P : FiniteProjectiveRight R}
    (θ : P.obj ≃ₗ[Rᵐᵒᵖ] range (e.mulVecBilin R Rᵐᵒᵖ)) :
    objectCodeAddEquiv R (mk e he) = objectCode.{u} P :=
  objectCodeFun_mk_eq_of_linearEquiv he θ

variable {R} in
@[simp]
theorem objectCodeAddEquiv_mk {ι : Type*} [Fintype ι] (e : Matrix ι ι R)
    (he : IsIdempotentElem e) :
    objectCodeAddEquiv R (mk e he) = objectCode.{u} (FiniteProjectiveModules.ofIdempotent e he) :=
  objectCodeAddEquiv_mk_eq_of_linearEquiv (P := FiniteProjectiveModules.ofIdempotent e he) he
    (FiniteProjectiveModules.ofIdempotentLinearEquiv e he)

/-- **`K₀(R)` is the group completion of the idempotent monoid `V(R)`.** Sends `[e]` to `[eRⁿ]`
(`TauCeti.IdempotentMonoid.kZeroEquiv_of_mk`). -/
def kZeroEquiv : GrothendieckAddGroup (IdempotentMonoid R) ≃+ KZero R :=
  (GrothendieckAddGroup.congr (objectCodeAddEquiv R)).trans
    (SplitK0.grothendieckAddGroupEquiv.{u} (FiniteProjectiveRight R))

variable {R} {ι : Type*} [Fintype ι]

/-- `TauCeti.IdempotentMonoid.kZeroEquiv` sends `[e]` to `[X]` for any `X ≃ₗ[Rᵐᵒᵖ] e Rⁿ`. -/
theorem kZeroEquiv_of_mk {e : Matrix ι ι R} (he : IsIdempotentElem e) (X : FiniteProjectiveRight R)
    (θ : X.obj ≃ₗ[Rᵐᵒᵖ] range (mulVecBilin R Rᵐᵒᵖ e)) :
    kZeroEquiv R (GrothendieckAddGroup.of (mk e he)) = SplitK0.of.{u} X := by
  rw [kZeroEquiv, AddEquiv.trans_apply, GrothendieckAddGroup.congr_of,
    objectCodeAddEquiv_mk_eq_of_linearEquiv he θ]
  exact SplitK0.grothendieckAddGroupEquiv_of_objectCode.{u} X

-- Not `@[simp]`: the simp normal form of `GrothendieckAddGroup.of x` is
-- `AddLocalization.addMonoidOf ⊤ x`, as for `Algebra.GrothendieckAddGroup.lift_apply_of`.
/-- `TauCeti.IdempotentMonoid.kZeroEquiv` sends the class of the identity matrix of size `m` to
`m[R]`, the class of the free right module `Rᵐ`. -/
theorem kZeroEquiv_of_mk_one (m : ℕ) :
    kZeroEquiv R (GrothendieckAddGroup.of (mk (1 : Matrix (Fin m) (Fin m) R) .one)) =
      m • SplitK0.of.{u} (finiteProjectiveModulesRegular Rᵐᵒᵖ) := by
  rw [kZeroEquiv_of_mk _ (FiniteProjectiveModules.of Rᵐᵒᵖ (Fin m → Rᵐᵒᵖ))
    (rangeMulVecBilinOneEquiv (Fin m) R).symm]
  exact SplitK0.of_eq_nsmul_of_linearEquiv_fin (.refl _ _) (.refl _ _)

-- Not `@[simp]`, for the same reason as `TauCeti.IdempotentMonoid.kZeroEquiv_of_mk_one`.
/-- Padding an idempotent matrix `e` by an identity block of size `m` adds `m[R]` to its class:
`[e ⊕ 1ₘ] = [e] + m[R]` in `K₀(R)`. -/
theorem kZeroEquiv_of_mk_fromBlocks_one {e : Matrix ι ι R} (he : IsIdempotentElem e) (m : ℕ) :
    kZeroEquiv R (GrothendieckAddGroup.of (mk (fromBlocks e 0 0 (1 : Matrix (Fin m) (Fin m) R))
        (he.fromBlocks_zero₁₂_zero₂₁ .one))) =
      kZeroEquiv R (GrothendieckAddGroup.of (mk e he)) +
        m • SplitK0.of.{u} (finiteProjectiveModulesRegular Rᵐᵒᵖ) := by
  rw [← mk_add_mk he .one, map_add, map_add, kZeroEquiv_of_mk_one]

/-- **Every class in `K₀(R)` is `[eRⁿ] - m[R]`.** Every element of `K₀(R)` is the difference of
the class of the image of an idempotent matrix `e` acting on column vectors and the class of a
finite free right module `Rᵐ`. -/
theorem exists_kZeroEquiv_sub_nsmul_eq (x : KZero R) :
    ∃ (n : ℕ) (e : Matrix (Fin n) (Fin n) R) (he : IsIdempotentElem e) (m : ℕ),
      kZeroEquiv R (GrothendieckAddGroup.of (mk e he)) -
        m • SplitK0.of.{u} (finiteProjectiveModulesRegular Rᵐᵒᵖ) = x := by
  obtain ⟨n, e, he, m, h⟩ := exists_of_mk_sub_of_mk_one_eq ((kZeroEquiv R).symm x)
  refine ⟨n, e, he, m, ?_⟩
  rw [← kZeroEquiv_of_mk_one, ← map_sub, h, AddEquiv.apply_symm_apply]

end IdempotentMonoid

end KZero

section ScalarExtension

namespace FiniteProjectiveModules

variable {R S : Type u} [Ring R] [Ring S]

/-- **Extension of scalars on `ofIdempotent`.** Along a ring homomorphism `f : R →+* S`,
extending scalars of the finitely generated projective right `R`-module
`FiniteProjectiveModules.ofIdempotent e he` yields a module canonically isomorphic to
`FiniteProjectiveModules.ofIdempotent (e.map f) (he.matrix_map f)`. -/
noncomputable def extendScalarsOfIdempotentIso (f : R →+* S) {ι : Type*} [Fintype ι]
    {e : Matrix ι ι R} (he : IsIdempotentElem e) :
    (RingHom.op f).finiteProjectiveModulesExtendScalars.obj (ofIdempotent e he) ≅
      ofIdempotent (e.map f) (he.matrix_map f) :=
  ObjectProperty.isoMk (finiteProjectiveModules Sᵐᵒᵖ)
    (eqToIso ((RingHom.op f).finiteProjectiveModulesExtendScalars_obj_obj _) ≪≫
      ((BalancedExtension.congr (RingHom.op f) (ofIdempotentLinearEquiv e he)).trans
        ((BalancedExtension.rangeMulVecBilinEquiv f he).trans
          (ofIdempotentLinearEquiv (e.map f) (he.matrix_map f)).symm)).toModuleIso)

/-- Transport of `(extendScalarsOfIdempotentIso f he).hom` through `ofIdempotentLinearEquiv`. -/
@[simp]
theorem ofIdempotentLinearEquiv_extendScalarsOfIdempotentIso_hom_apply (f : R →+* S)
    {ι : Type*} [Fintype ι] {e : Matrix ι ι R} (he : IsIdempotentElem e)
    (x : ((RingHom.op f).finiteProjectiveModulesExtendScalars.obj (ofIdempotent e he)).obj) :
    ofIdempotentLinearEquiv (e.map f) (he.matrix_map f)
        ((extendScalarsOfIdempotentIso f he).hom.hom x) =
      BalancedExtension.rangeMulVecBilinEquiv f he
        (BalancedExtension.congr (RingHom.op f) (ofIdempotentLinearEquiv e he)
          ((eqToHom ((RingHom.op f).finiteProjectiveModulesExtendScalars_obj_obj _)).hom x)) := by
  dsimp [extendScalarsOfIdempotentIso]; simp

/-- Pure-tensor coordinate formula for `(extendScalarsOfIdempotentIso f he).hom`. -/
theorem coe_ofIdempotentLinearEquiv_extendScalarsOfIdempotentIso_hom_tmul (f : R →+* S)
    {ι : Type*} [Fintype ι] {e : Matrix ι ι R} (he : IsIdempotentElem e) (s : Sᵐᵒᵖ)
    (v : (ofIdempotent e he).obj) :
    (ofIdempotentLinearEquiv (e.map f) (he.matrix_map f)
        ((extendScalarsOfIdempotentIso f he).hom.hom
          ((eqToHom ((RingHom.op f).finiteProjectiveModulesExtendScalars_obj_obj _).symm).hom
            (BalancedExtension.tmul (RingHom.op f) s v))) : ι → S) =
      fun i ↦ f ((ofIdempotentLinearEquiv e he v : ι → R) i) * s.unop := by
  rw [ofIdempotentLinearEquiv_extendScalarsOfIdempotentIso_hom_apply, ← ModuleCat.comp_apply,
    eqToHom_trans, eqToHom_refl]; simp

/-- Transport of `(extendScalarsOfIdempotentIso f he).inv` into `BalancedExtension.congr`. -/
@[simp]
theorem balancedExtensionCongr_extendScalarsOfIdempotentIso_inv_apply (f : R →+* S)
    {ι : Type*} [Fintype ι] {e : Matrix ι ι R} (he : IsIdempotentElem e)
    (w : (ofIdempotent (e.map f) (he.matrix_map f)).obj) :
    BalancedExtension.congr (RingHom.op f) (ofIdempotentLinearEquiv e he)
        ((eqToHom ((RingHom.op f).finiteProjectiveModulesExtendScalars_obj_obj _)).hom
          ((extendScalarsOfIdempotentIso f he).inv.hom w)) =
      (BalancedExtension.rangeMulVecBilinEquiv f he).symm
        (ofIdempotentLinearEquiv (e.map f) (he.matrix_map f) w) := by
  rw [LinearEquiv.eq_symm_apply, ← ofIdempotentLinearEquiv_extendScalarsOfIdempotentIso_hom_apply]
  congr 1
  have h := ConcreteCategory.congr_hom ((finiteProjectiveModules Sᵐᵒᵖ).ι.mapIso
    (extendScalarsOfIdempotentIso f he)).inv_hom_id w
  rw [ModuleCat.comp_apply, ModuleCat.id_apply] at h
  exact h

/-- Explicit column-sum formula for `(extendScalarsOfIdempotentIso f he).inv`. -/
theorem extendScalarsOfIdempotentIso_inv_apply (f : R →+* S)
    {ι : Type*} [Fintype ι] {e : Matrix ι ι R} (he : IsIdempotentElem e)
    (w : (ofIdempotent (e.map f) (he.matrix_map f)).obj) :
    (extendScalarsOfIdempotentIso f he).inv.hom w =
      (eqToHom ((RingHom.op f).finiteProjectiveModulesExtendScalars_obj_obj _).symm).hom
        (∑ j, BalancedExtension.tmul (RingHom.op f)
          (op ((ofIdempotentLinearEquiv (e.map f) (he.matrix_map f) w : ι → S) j))
          ((ofIdempotentLinearEquiv e he).symm ⟨e.col j, e.col_mem_range_mulVecBilin j⟩)) := by
  apply (ConcreteCategory.bijective_of_isIso
    (eqToHom ((RingHom.op f).finiteProjectiveModulesExtendScalars_obj_obj
      (ofIdempotent e he)))).injective
  apply (BalancedExtension.congr (RingHom.op f) (ofIdempotentLinearEquiv e he)).injective
  rw [balancedExtensionCongr_extendScalarsOfIdempotentIso_inv_apply, ← ModuleCat.comp_apply,
    eqToHom_trans, eqToHom_refl]; simp

end FiniteProjectiveModules

namespace IdempotentMonoid

section ObjectCode

variable (R : Type u) [Ring R]

/-- The canonical additive monoid homomorphism from `IdempotentMonoid R` to `KZero R`, sending
`[e]` to the class `[e R^ι]` of its column range (`TauCeti.IdempotentMonoid.kZeroEquiv` restricted
along `GrothendieckAddGroup.of`). -/
noncomputable def toKZero : IdempotentMonoid R →+ KZero R :=
  (kZeroEquiv R).toAddMonoidHom.comp _root_.Algebra.GrothendieckAddGroup.of

/-- The group-completion isomorphism `kZeroEquiv R` restricts along `GrothendieckAddGroup.of` to
`toKZero R`. Not marked `@[simp]` because `GrothendieckAddGroup.of` is reducible. -/
theorem kZeroEquiv_of (x : IdempotentMonoid R) :
    kZeroEquiv R (_root_.Algebra.GrothendieckAddGroup.of x) = toKZero R x := (rfl)

@[simp]
theorem lift_toKZero :
    _root_.Algebra.GrothendieckAddGroup.lift (toKZero R) = (kZeroEquiv R).toAddMonoidHom :=
  _root_.Algebra.GrothendieckAddGroup.lift.eq_symm_apply.mp
    (_root_.Algebra.GrothendieckAddGroup.lift_symm_apply _).symm

variable {R} in
@[simp]
theorem toKZero_mk {ι : Type*} [Fintype ι] (e : Matrix ι ι R) (he : IsIdempotentElem e) :
    toKZero R (mk e he) = SplitK0.of.{u} (FiniteProjectiveModules.ofIdempotent e he) :=
  kZeroEquiv_of_mk he _ (FiniteProjectiveModules.ofIdempotentLinearEquiv e he)

-- Not `@[simp]`: `TauCeti.IdempotentMonoid.toKZero_mk` rewrites the left-hand side.
/-- `TauCeti.IdempotentMonoid.toKZero` sends the class of the `1 × 1` identity matrix to `[R]`, the
class of the free right module of rank one. -/
theorem toKZero_mk_one :
    toKZero R (mk (1 : Matrix (Fin 1) (Fin 1) R) .one) =
      SplitK0.of.{u} (finiteProjectiveModulesRegular Rᵐᵒᵖ) := by
  rw [← kZeroEquiv_of, kZeroEquiv_of_mk_one, one_nsmul]

/-- `TauCeti.IdempotentMonoid.toKZero R` factors via `objectCodeAddEquiv R` and `SplitK0.ofCode`. -/
theorem ofCode_comp_objectCodeAddEquiv :
    SplitK0.ofCode.{u}.comp (objectCodeAddEquiv R).toAddMonoidHom = toKZero R := by
  ext n e he; simp

end ObjectCode

section Functoriality

variable {R S : Type u} [Ring R] [Ring S]

/-- **Naturality of `toKZero` under scalar extension.** -/
@[simp]
theorem map_toKZero (f : R →+* S) (x : IdempotentMonoid R) :
    SplitK0.map.{u, u} (RingHom.op f).finiteProjectiveModulesExtendScalars (toKZero R x) =
      toKZero S (IdempotentMonoid.map f.toNonUnitalRingHom x) := by
  induction x using ind with | mk n e he =>
  rw [toKZero_mk, SplitK0.map_of,
    SplitK0.of_congr.{u} (FiniteProjectiveModules.extendScalarsOfIdempotentIso f he),
    IdempotentMonoid.map_mk]
  exact (toKZero_mk (e.map f.toNonUnitalRingHom) (he.matrix_map f.toNonUnitalRingHom)).symm

theorem toKZero_comp_map (f : R →+* S) :
    (toKZero S).comp (IdempotentMonoid.map f.toNonUnitalRingHom) =
      (SplitK0.map.{u, u} (RingHom.op f).finiteProjectiveModulesExtendScalars).comp
        (toKZero R) :=
  AddMonoidHom.ext fun x ↦ (map_toKZero f x).symm

/-- **Naturality of `kZeroEquiv` under scalar extension.** -/
theorem map_comp_kZeroEquiv (f : R →+* S) :
    (SplitK0.map.{u, u} (RingHom.op f).finiteProjectiveModulesExtendScalars).comp
        (kZeroEquiv R).toAddMonoidHom =
      (kZeroEquiv S).toAddMonoidHom.comp (_root_.Algebra.GrothendieckAddGroup.lift
        (_root_.Algebra.GrothendieckAddGroup.of.comp
          (IdempotentMonoid.map f.toNonUnitalRingHom))) := by
  refine _root_.Algebra.GrothendieckAddGroup.addHom_ext fun a ↦ ?_
  simp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom]
  rw [_root_.Algebra.GrothendieckAddGroup.lift_apply_of, AddMonoidHom.comp_apply,
    kZeroEquiv_of, kZeroEquiv_of, map_toKZero]

end Functoriality

section PresentationAndCone

variable {R : Type u} [Ring R]

/-- Two idempotent matrices have the same class in `K₀(R)` iff their column ranges are stably
equivalent right `R`-modules. -/
theorem toKZero_mk_eq_toKZero_mk_iff_stableEquivalent {ι κ : Type*} [Fintype ι] [Fintype κ]
    {e : Matrix ι ι R} {f : Matrix κ κ R} {he : IsIdempotentElem e} {hf : IsIdempotentElem f} :
    toKZero R (mk e he) = toKZero R (mk f hf) ↔
      StableEquivalent Rᵐᵒᵖ (range (e.mulVecBilin R Rᵐᵒᵖ)) (range (f.mulVecBilin R Rᵐᵒᵖ)) := by
  rw [toKZero_mk, toKZero_mk, SplitK0.of_eq_of_iff_stableEquivalent]
  let ψe := FiniteProjectiveModules.ofIdempotentLinearEquiv e he
  let ψf := FiniteProjectiveModules.ofIdempotentLinearEquiv f hf
  exact ⟨fun h ↦ (StableEquivalent.of_equiv ψe.symm).trans (h.trans (.of_equiv ψf)),
    fun h ↦ (StableEquivalent.of_equiv ψe).trans (h.trans (.of_equiv ψf.symm))⟩

/-- **Equality of idempotent classes in `K₀(R)`.** Two idempotent matrices have the same class in
`K₀(R)` iff they become equivalent after adding a common identity block `1ₖ`. -/
theorem toKZero_mk_eq_toKZero_mk_iff {ι κ : Type*} [Fintype ι] [Fintype κ]
    {e : Matrix ι ι R} {f : Matrix κ κ R} {he : IsIdempotentElem e} {hf : IsIdempotentElem f} :
    toKZero R (mk e he) = toKZero R (mk f hf) ↔
      ∃ k : ℕ, IdempotentEquivalent (fromBlocks e 0 0 (1 : Matrix (Fin k) (Fin k) R))
        (fromBlocks f 0 0 (1 : Matrix (Fin k) (Fin k) R)) :=
  toKZero_mk_eq_toKZero_mk_iff_stableEquivalent.trans (stableEquivalent_range_mulVecBilin_iff he hf)

/-- **Algebraic positive cone of projective `K₀`.** The image submonoid of `IdempotentMonoid R` in
`K₀(R)` consists precisely of the classes `[P]` of finitely generated projective right `R`-modules.
-/
theorem mem_mrange_toKZero_iff {x : KZero R} :
    x ∈ AddMonoidHom.mrange (toKZero R) ↔ ∃ P : FiniteProjectiveRight R, x = SplitK0.of.{u} P := by
  rw [← ofCode_comp_objectCodeAddEquiv R]
  constructor
  · rintro ⟨a, rfl⟩; obtain ⟨P, hP⟩ := objectCode_surjective.{u} (objectCodeAddEquiv R a)
    exact ⟨P, by simp [← hP]⟩
  · rintro ⟨P, rfl⟩; obtain ⟨a, ha⟩ := (objectCodeAddEquiv R).surjective (objectCode.{u} P)
    exact ⟨a, by simp [ha]⟩

/-- Subtracting `[1ₘ]` from `[e]` in `K₀(R)` gives `classOf Rᵐᵒᵖ P m = [P] - m[R]`. -/
theorem toKZero_mk_sub_toKZero_mk_one_eq_classOf_of_linearEquiv {ι : Type*} [Fintype ι]
    {e : Matrix ι ι R} (he : IsIdempotentElem e) {P : Type u} [AddCommGroup P] [Module Rᵐᵒᵖ P]
    [Module.Finite Rᵐᵒᵖ P] [Module.Projective Rᵐᵒᵖ P]
    (θ : P ≃ₗ[Rᵐᵒᵖ] range (e.mulVecBilin R Rᵐᵒᵖ)) (m : ℕ) :
    toKZero R (mk e he) - toKZero R (mk (1 : Matrix (Fin m) (Fin m) R) IsIdempotentElem.one) =
      FiniteProjectiveModules.classOf Rᵐᵒᵖ P m := by
  rw [← kZeroEquiv_of, ← kZeroEquiv_of,
    kZeroEquiv_of_mk he ⟨ModuleCat.of Rᵐᵒᵖ P, finiteProjectiveModules_iff.mpr
      ⟨inferInstance, inferInstance⟩⟩ θ,
    kZeroEquiv_of_mk_one, FiniteProjectiveModules.classOf_def,
    SplitK0.of_congr.{u} (X := finiteProjectiveModulesRegular Rᵐᵒᵖ) (Y := ⟨ModuleCat.of Rᵐᵒᵖ Rᵐᵒᵖ,
      finiteProjectiveModules_iff.2 ⟨inferInstance, inferInstance⟩⟩)
      (ObjectProperty.isoMk _ (Iso.refl _))]

end PresentationAndCone

end IdempotentMonoid

section PrincipalRightIdeal

variable {R : Type u} [Ring R] {e : R}

/-- **The principal right ideal** `eR` of an idempotent `e` of `R`, as a finitely generated
projective right `R`-module: the submodule of `Rᵐᵒᵖ` spanned by `op e`. It is a direct summand of
the regular module, the image of left multiplication by `e`. -/
def KZero.principalRightIdeal (he : IsIdempotentElem e) : FiniteProjectiveRight R :=
  ⟨ModuleCat.of Rᵐᵒᵖ (Submodule.span Rᵐᵒᵖ {op e}), finiteProjectiveModules_iff.2
    ⟨inferInstance, IsIdempotentElem.projective_span_singleton (congrArg op he.eq)⟩⟩

/-- The underlying module of `TauCeti.KZero.principalRightIdeal he` is the right ideal spanned by
`e`. -/
@[simp]
theorem KZero.principalRightIdeal_obj (he : IsIdempotentElem e) :
    (KZero.principalRightIdeal he).obj = ModuleCat.of Rᵐᵒᵖ (Submodule.span Rᵐᵒᵖ {op e}) :=
  (rfl)

/-- The identification of the underlying module of `TauCeti.KZero.principalRightIdeal he` with the
right ideal spanned by `e`, as an isomorphism of right `R`-modules
(`TauCeti.KZero.principalRightIdeal_obj`). -/
def KZero.principalRightIdealObjIso (he : IsIdempotentElem e) :
    (KZero.principalRightIdeal he).obj ≅ ModuleCat.of Rᵐᵒᵖ (Submodule.span Rᵐᵒᵖ {op e}) :=
  eqToIso (KZero.principalRightIdeal_obj he)

/-- **The class of a principal right ideal.** The principal right ideal `eR` of an idempotent `e`
has the class of the `1 × 1` idempotent matrix with entry `e`, its image under
`Matrix.uniqueRingEquiv.symm`. -/
theorem IdempotentMonoid.toKZero_mk_of_unique {m : Type*} [Unique m] (he : IsIdempotentElem e) :
    IdempotentMonoid.toKZero R
      (IdempotentMonoid.mk ((Matrix.uniqueRingEquiv (m := m)).symm e)
        (he.map Matrix.uniqueRingEquiv.symm)) =
      SplitK0.of.{u} (KZero.principalRightIdeal he) := by
  rw [← IdempotentMonoid.kZeroEquiv_of]
  exact IdempotentMonoid.kZeroEquiv_of_mk _ _
    ((KZero.principalRightIdealObjIso he).toLinearEquiv.trans
      (rangeMulVecBilinOfUniqueEquivSpan R m e).symm)

end PrincipalRightIdeal

end ScalarExtension

section Ring

namespace IdempotentMonoid

open MulOpposite

variable (A : Type u) [Ring A]

/-- **`K₀` is the group completion of the idempotent monoid.** Obtained from the right-module
comparison `TauCeti.IdempotentMonoid.kZeroEquiv` via transposition over the opposite ring
(`TauCeti.IdempotentMonoid.opEquiv`): the class of an idempotent matrix `e` goes to the class of
the image `Aⁿe` of its action on row vectors (`TauCeti.IdempotentMonoid.splitK0Equiv_of_mk`). -/
def splitK0Equiv :
    GrothendieckAddGroup (IdempotentMonoid A) ≃+
      SplitK0.{u} (finiteProjectiveModules A).FullSubcategory :=
  ((GrothendieckAddGroup.congr (opEquiv A)).trans (kZeroEquiv Aᵐᵒᵖ)).trans
    (SplitK0.mapEquiv
      (ModuleCat.restrictScalarsEquivalenceOfRingEquiv
        (RingEquiv.opOp A)).finiteProjectiveModulesEquivalence)

variable {A}

/-- **The class map `V(A) → K₀(A)`.** The class of an idempotent matrix `e` goes to the class of
the image `Aⁿe` of its action on row vectors, a finitely generated projective left `A`-module; see
`TauCeti.IdempotentMonoid.toSplitK0_mk`. -/
def toSplitK0 : IdempotentMonoid A →+ SplitK0.{u} (finiteProjectiveModules A).FullSubcategory :=
  (splitK0Equiv A).toAddMonoidHom.comp GrothendieckAddGroup.of

-- Not `@[simp]`: the simp normal form of `GrothendieckAddGroup.of x` is
-- `AddLocalization.addMonoidOf ⊤ x`, as for `Algebra.GrothendieckAddGroup.lift_apply_of`.
/-- On `V(A)`, the isomorphism `TauCeti.IdempotentMonoid.splitK0Equiv` is the class map
`TauCeti.IdempotentMonoid.toSplitK0`. -/
theorem splitK0Equiv_of (x : IdempotentMonoid A) :
    splitK0Equiv A (GrothendieckAddGroup.of x) = toSplitK0 x := by
  rw [toSplitK0, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom]

/-- The isomorphism `TauCeti.IdempotentMonoid.splitK0Equiv` sends the class of an idempotent
matrix `e` to the class of any module isomorphic to the image `Aⁿe` of its action on row vectors. -/
theorem splitK0Equiv_of_mk {ι : Type*} [Fintype ι] {e : Matrix ι ι A} (he : IsIdempotentElem e)
    (X : (finiteProjectiveModules A).FullSubcategory) (θ : X.obj ≃ₗ[A] range e.vecMulLinear) :
    splitK0Equiv A (GrothendieckAddGroup.of (mk e he)) = SplitK0.of.{u} X := by
  let E₀ := ModuleCat.restrictScalarsEquivalenceOfRingEquiv (RingEquiv.opOp A)
  let E := E₀.finiteProjectiveModulesEquivalence
  let Y : FiniteProjectiveRight Aᵐᵒᵖ := E.inverse.obj X
  have : RingHomInvPair (RingEquiv.opOp A : A →+* Aᵐᵒᵖᵐᵒᵖ) _ := .of_ringEquiv (RingEquiv.opOp A)
  have : RingHomInvPair ((RingEquiv.opOp A).symm : Aᵐᵒᵖᵐᵒᵖ →+* A) _ :=
    .of_ringEquiv_symm (RingEquiv.opOp A)
  let eY : Y.obj ≃ₛₗ[((RingEquiv.opOp A).symm : Aᵐᵒᵖᵐᵒᵖ →+* A)] X.obj :=
    (eqToIso (E₀.finiteProjectiveModulesEquivalence_inverse_obj_obj X)).toLinearEquiv.trans
      ((RingEquiv.opOp A).symm.restrictScalarsSemilinearEquiv X.obj)
  have heOp : (eᵀ.map op)ᵀ.map op = e.map (RingEquiv.opOp A) := by
    ext i j; simp [RingEquiv.opOp_apply]
  let eOp : range e.vecMulLinear ≃ₛₗ[(RingEquiv.opOp A : A →+* Aᵐᵒᵖᵐᵒᵖ)]
      range ((eᵀ.map op)ᵀ.map op).vecMulLinear :=
    (e.rangeVecMulLinearEquiv (RingEquiv.opOp A)).trans (LinearEquiv.ofEq _ _ (by rw [← heOp]))
  let θ' : Y.obj ≃ₗ[Aᵐᵒᵖᵐᵒᵖ] range ((eᵀ.map op).mulVecBilin Aᵐᵒᵖ Aᵐᵒᵖᵐᵒᵖ) :=
    ((eY.trans θ).trans eOp).trans (rangeVecMulLinearTransposeMapOpEquiv (eᵀ.map op))
  rw [splitK0Equiv, AddEquiv.trans_apply, AddEquiv.trans_apply, GrothendieckAddGroup.congr_of,
    opEquiv_mk,
    kZeroEquiv_of_mk he.matrix_transpose_map_op Y θ', SplitK0.mapEquiv_of]
  exact SplitK0.of_congr (E.counitIso.app X)

/-- The class of an idempotent matrix `e` goes to the class of any module `X` isomorphic to the
image `Aⁿe` of its action on row vectors. -/
theorem toSplitK0_mk {ι : Type*} [Fintype ι] {e : Matrix ι ι A} (he : IsIdempotentElem e)
    (X : (finiteProjectiveModules A).FullSubcategory) (θ : X.obj ≃ₗ[A] range e.vecMulLinear) :
    toSplitK0 (mk e he) = SplitK0.of.{u} X :=
  splitK0Equiv_of_mk he X θ

end IdempotentMonoid

end Ring

end TauCeti
