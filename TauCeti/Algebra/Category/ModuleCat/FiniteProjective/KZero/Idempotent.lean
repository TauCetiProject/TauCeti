/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.KZero.Defs
public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.StableEquivalent
public import TauCeti.LinearAlgebra.Matrix.Idempotent.Monoid

import TauCeti.Algebra.Category.ModuleCat.CartanMap.Morita

/-!
# The idempotent monoid and projective `K₀`

Building on `TauCeti.IdempotentMonoid` in `TauCeti.LinearAlgebra.Matrix.Idempotent.Monoid`, this
file proves `objectCodeAddEquiv : IdempotentMonoid R ≃+ ObjectCode (FiniteProjectiveRight R)` and
identifies the group completions of `V(R)` with split projective `K₀` for right modules
(`kZeroEquiv`, with `kZeroEquiv_of_mk` and `exists_kZeroEquiv_sub_nsmul_eq`) and left modules via
`opEquiv` (`splitK0Equiv`, `toSplitK0`, `splitK0Equiv_of_mk`), via `ofIdempotent`.

## References

* J. Rosenberg, *Algebraic K-Theory and Its Applications*, §1.2.
* C. A. Weibel, *The K-book*, Chapter II, §2, the definition of `K₀` by idempotent matrices.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory Matrix LinearMap _root_.Algebra

universe u

section KZero

/-- The column range `e R^ι` of an idempotent matrix `e`, packaged as an object of
`FiniteProjectiveRight R` via reindexing to `Fin (Fintype.card ι)`. -/
noncomputable def FiniteProjectiveModules.ofIdempotent {R : Type u} [Ring R] {ι : Type*}
    [Fintype ι] (e : Matrix ι ι R) (he : IsIdempotentElem e) : FiniteProjectiveRight R :=
  let σ := Fintype.equivFin ι
  ⟨ModuleCat.of Rᵐᵒᵖ (range ((e.reindex σ σ).mulVecBilin R Rᵐᵒᵖ)),
    finiteProjectiveModules_iff.mpr ⟨inferInstance,
      (he.idempotentEquivalent_reindex σ).isIdempotentElem_left.projective_range_mulVecBilin⟩⟩

/-- Canonical `Rᵐᵒᵖ`-linear equivalence between the underlying module of
`FiniteProjectiveModules.ofIdempotent e he` and the original column range `e R^ι`. -/
noncomputable def FiniteProjectiveModules.ofIdempotentLinearEquiv {R : Type u} [Ring R]
    {ι : Type*} [Fintype ι] (e : Matrix ι ι R) (he : IsIdempotentElem e) :
    (ofIdempotent e he).obj ≃ₗ[Rᵐᵒᵖ] range (e.mulVecBilin R Rᵐᵒᵖ) :=
  (e.rangeMulVecBilinReindexEquiv (Fintype.equivFin ι) (Fintype.equivFin ι)).symm

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
private theorem objectCodeFun_mk_linearEquiv {ι : Type*} [Fintype ι] {e : Matrix ι ι R}
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
  objectCodeFun_mk_linearEquiv (P := FiniteProjectiveModules.ofIdempotent e he) he
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
    exact objectCodeFun_mk_linearEquiv (he.fromBlocks_zero₁₂_zero₂₁ hf)
      (((FiniteProjectiveModules.biprodLinearEquiv _ _).trans
        ((FiniteProjectiveModules.ofIdempotentLinearEquiv e he).prodCongr
          (FiniteProjectiveModules.ofIdempotentLinearEquiv f hf))).trans
        (rangeMulVecBilinFromBlocksEquiv e f).symm)

private theorem objectCodeHom_bijective : Function.Bijective (objectCodeHom R) :=
  ⟨fun a b hab ↦ by
    induction a using ind with | mk m e he =>
    induction b using ind with | mk n f hf =>
    change objectCodeFun R (mk e he) = objectCodeFun R (mk f hf) at hab
    rw [objectCodeFun_mk e he, objectCodeFun_mk f hf, objectCode_eq_objectCode_iff.{u}] at hab
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
    exact ⟨mk e he, objectCodeFun_mk_linearEquiv he θ⟩⟩

/-- **Idempotent presentation of the monoid of projective modules.** `[e] ↦ [e Rⁿ]` is an
additive isomorphism `IdempotentMonoid R ≃+ ObjectCode (FiniteProjectiveRight R)`. -/
def objectCodeAddEquiv : IdempotentMonoid R ≃+ ObjectCode.{u} (FiniteProjectiveRight R) :=
  AddEquiv.ofBijective (objectCodeHom R) (objectCodeHom_bijective R)

variable {R} in
/-- Evaluating `objectCodeAddEquiv` on `[e]` yields `objectCode P` for any `P ≃ₗ[Rᵐᵒᵖ] e R^ι`. -/
theorem objectCodeAddEquiv_mk_linearEquiv {ι : Type*} [Fintype ι] {e : Matrix ι ι R}
    (he : IsIdempotentElem e) {P : FiniteProjectiveRight R}
    (θ : P.obj ≃ₗ[Rᵐᵒᵖ] range (e.mulVecBilin R Rᵐᵒᵖ)) :
    objectCodeAddEquiv R (mk e he) = objectCode.{u} P :=
  objectCodeFun_mk_linearEquiv he θ

variable {R} in
@[simp]
theorem objectCodeAddEquiv_mk {ι : Type*} [Fintype ι] (e : Matrix ι ι R)
    (he : IsIdempotentElem e) :
    objectCodeAddEquiv R (mk e he) = objectCode.{u} (FiniteProjectiveModules.ofIdempotent e he) :=
  objectCodeAddEquiv_mk_linearEquiv (P := FiniteProjectiveModules.ofIdempotent e he) he
    (FiniteProjectiveModules.ofIdempotentLinearEquiv e he)

/-- **`K₀(R)` is the group completion of the idempotent monoid `V(R)`.** Sends `[e]` to `[eRⁿ]`
(`TauCeti.IdempotentMonoid.kZeroEquiv_of_mk`). -/
def kZeroEquiv : GrothendieckAddGroup (IdempotentMonoid R) ≃+ KZero R :=
  ((AddLocalization.addMonoidOf ⊤).addEquivOfAddEquiv
    (AddLocalization.addMonoidOf (M := ObjectCode.{u} (FiniteProjectiveRight R)) ⊤)
    (j := objectCodeAddEquiv R) (AddSubmonoid.map_equiv_top (objectCodeAddEquiv R))).trans
    (SplitK0.grothendieckAddGroupEquiv.{u} (FiniteProjectiveRight R))

variable {R} {ι : Type*} [Fintype ι]

/-- `TauCeti.IdempotentMonoid.kZeroEquiv` sends `[e]` to `[X]` for any `X ≃ₗ[Rᵐᵒᵖ] e Rⁿ`. -/
theorem kZeroEquiv_of_mk {e : Matrix ι ι R} (he : IsIdempotentElem e) (X : FiniteProjectiveRight R)
    (θ : X.obj ≃ₗ[Rᵐᵒᵖ] range (mulVecBilin R Rᵐᵒᵖ e)) :
    kZeroEquiv R (GrothendieckAddGroup.of (mk e he)) = SplitK0.of.{u} X := by
  refine (congrArg (SplitK0.grothendieckAddGroupEquiv.{u} (FiniteProjectiveRight R))
    ((AddLocalization.addMonoidOf ⊤).addEquivOfAddEquiv_eq
      (k := AddLocalization.addMonoidOf (M := ObjectCode.{u} (FiniteProjectiveRight R)) ⊤)
      (AddSubmonoid.map_equiv_top (objectCodeAddEquiv R)) (mk e he))).trans ?_
  rw [objectCodeAddEquiv_mk_linearEquiv he θ]
  exact SplitK0.grothendieckAddGroupEquiv_of_objectCode.{u} X

-- Not `@[simp]`: the simp normal form of `GrothendieckAddGroup.of x` is
-- `AddLocalization.addMonoidOf ⊤ x`, as for `Algebra.GrothendieckAddGroup.lift_apply_of`.
/-- `TauCeti.IdempotentMonoid.kZeroEquiv` sends the class of the identity matrix of size `m` to
`m[R]`, the class of the free right module `Rᵐ`. -/
theorem kZeroEquiv_of_mk_one (m : ℕ) :
    kZeroEquiv R (GrothendieckAddGroup.of (mk (1 : Matrix (Fin m) (Fin m) R) .one)) =
      m • SplitK0.of.{u} (finiteProjectiveModulesRegular Rᵐᵒᵖ) := by
  -- `Rᵐ`, the image of the identity matrix, written as `(Rᵐᵒᵖ)ᵐ` through `unop` on coordinates.
  let L : (Fin m → Rᵐᵒᵖ) ≃ₗ[Rᵐᵒᵖ] (Fin m → R) :=
    .piCongrRight fun _ ↦ (MulOpposite.opLinearEquiv Rᵐᵒᵖ).symm
  have htop : range (mulVecBilin R Rᵐᵒᵖ (1 : Matrix (Fin m) (Fin m) R)) = ⊤ :=
    range_eq_top.2 fun v ↦ ⟨v, one_mulVec v⟩
  rw [kZeroEquiv_of_mk _ ⟨ModuleCat.of Rᵐᵒᵖ (Fin m → Rᵐᵒᵖ),
    finiteProjectiveModules_iff.2 ⟨inferInstance, inferInstance⟩⟩
    (L.trans (LinearEquiv.ofTop _ htop).symm)]
  exact SplitK0.of_eq_nsmul_of_linearEquiv_fin (.refl _ _) (.refl _ _)

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
  (((AddLocalization.addMonoidOf ⊤).addEquivOfAddEquiv (AddLocalization.addMonoidOf ⊤)
    (j := opEquiv A) (AddSubmonoid.map_equiv_top (opEquiv A))).trans
    (kZeroEquiv Aᵐᵒᵖ)).trans
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
  have hop : (AddLocalization.addMonoidOf ⊤).addEquivOfAddEquiv (AddLocalization.addMonoidOf ⊤)
      (AddSubmonoid.map_equiv_top (opEquiv A)) (GrothendieckAddGroup.of (mk e he)) =
        GrothendieckAddGroup.of (opEquiv A (mk e he)) :=
    AddSubmonoid.LocalizationMap.addEquivOfAddEquiv_eq _ _ _
  let E₀ := ModuleCat.restrictScalarsEquivalenceOfRingEquiv (RingEquiv.opOp A)
  let E := E₀.finiteProjectiveModulesEquivalence
  let Y : FiniteProjectiveRight Aᵐᵒᵖ := E.inverse.obj X
  have : RingHomInvPair (RingEquiv.opOp A).toRingHom (RingEquiv.opOp A).symm.toRingHom :=
    RingHomInvPair.of_ringEquiv (RingEquiv.opOp A)
  have : RingHomInvPair (RingEquiv.opOp A).symm.toRingHom (RingEquiv.opOp A).toRingHom :=
    RingHomInvPair.of_ringEquiv_symm (RingEquiv.opOp A)
  let eY : Y.obj ≃ₛₗ[(RingEquiv.opOp A).symm.toRingHom] X.obj :=
    (eqToIso (E₀.finiteProjectiveModulesEquivalence_inverse_obj_obj X)).toLinearEquiv.trans
      { toFun := fun x ↦ x, invFun := fun x ↦ x, left_inv := fun _ ↦ rfl,
        right_inv := fun _ ↦ rfl, map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
  -- Transport `θ` across `RingEquiv.opOp A` and then across
  -- `Matrix.rangeVecMulLinearTransposeMapOpEquiv`, turning row vectors `Aⁿe` into column vectors
  -- `(eᵀ.map op) (Aᵐᵒᵖ)ⁿ`.
  have heOp : (eᵀ.map op)ᵀ.map op = e.map (RingEquiv.opOp A).toRingHom := by
    ext i j; rfl
  let f := e.rangeVecMulLinearMap (RingEquiv.opOp A).toRingHom
  let eOp₁ : range e.vecMulLinear ≃ₛₗ[(RingEquiv.opOp A).toRingHom]
      range (e.map (RingEquiv.opOp A).toRingHom).vecMulLinear :=
    { toFun := f
      invFun := (e.map (RingEquiv.opOp A).toRingHom).rangeVecMulLinearMap
        (RingEquiv.opOp A).symm.toRingHom
      map_add' := f.map_add'
      map_smul' := f.map_smul'
      left_inv := fun v ↦ Subtype.ext <| funext fun i ↦ by
        rw [coe_rangeVecMulLinearMap_apply, coe_rangeVecMulLinearMap_apply]
        simp
      right_inv := fun w ↦ Subtype.ext <| funext fun i ↦ by
        have h1 := congrFun (coe_rangeVecMulLinearMap_apply e (RingEquiv.opOp A).toRingHom
          (((e.map (RingEquiv.opOp A).toRingHom).rangeVecMulLinearMap
            (RingEquiv.opOp A).symm.toRingHom) w)) i
        have h2 := congrFun (coe_rangeVecMulLinearMap_apply (e.map (RingEquiv.opOp A).toRingHom)
          (RingEquiv.opOp A).symm.toRingHom w) i
        simp only [Function.comp_apply] at h1 h2
        exact h1.trans (congrArg _ h2 |>.trans (by simp)) }
  let eOp : range e.vecMulLinear ≃ₛₗ[(RingEquiv.opOp A).toRingHom]
      range ((eᵀ.map op)ᵀ.map op).vecMulLinear :=
    eOp₁.trans (LinearEquiv.ofEq _ _ (by rw [heOp]))
  let θ' : Y.obj ≃ₗ[Aᵐᵒᵖᵐᵒᵖ] range ((eᵀ.map op).mulVecBilin Aᵐᵒᵖ Aᵐᵒᵖᵐᵒᵖ) :=
    ((eY.trans θ).trans eOp).trans (rangeVecMulLinearTransposeMapOpEquiv (eᵀ.map op))
  rw [splitK0Equiv, AddEquiv.trans_apply, AddEquiv.trans_apply, hop, opEquiv_mk,
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
