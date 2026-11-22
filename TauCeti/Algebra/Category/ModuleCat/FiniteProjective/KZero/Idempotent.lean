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

Building on `TauCeti.IdempotentMonoid` from `TauCeti.LinearAlgebra.Matrix.Idempotent.Monoid`, this
file compares the idempotent monoid `V(R)` with `ObjectCode (FiniteProjectiveRight R)` and with
split projective `K₀`:

Over a ring, `V(R)` models the isomorphism classes of finitely generated projective modules under
direct sum: an idempotent `e` presents the image of its action on vectors, every finitely
generated projective module is such an image, and two idempotents present isomorphic modules
exactly when they are equivalent. Accordingly, `V(R)` is isomorphic as an additive monoid to
`ObjectCode (FiniteProjectiveRight R)` (`TauCeti.IdempotentMonoid.objectCodeAddEquiv`), whose
group completion is the projective `K₀` (`TauCeti.IdempotentMonoid.kZeroEquiv`). Transposition over
the opposite ring (`TauCeti.IdempotentMonoid.opEquiv`) supplies the corresponding left-module
comparison `TauCeti.IdempotentMonoid.splitK0Equiv`. As a consequence every element of `K₀(R)` is
`[eRⁿ] - m[R]` for an idempotent matrix `e` and some `m`.

## Main definitions

* `TauCeti.FiniteProjectiveModules.ofIdempotent`: the column range `e R^ι` of an idempotent matrix
  as an object of `FiniteProjectiveRight R`, with canonical linear equivalence
  `TauCeti.FiniteProjectiveModules.ofIdempotentLinearEquiv`.
* `TauCeti.IdempotentMonoid.objectCodeAddEquiv`: the monoid isomorphism
  `IdempotentMonoid R ≃+ ObjectCode (FiniteProjectiveRight R)` before group completion.
* `TauCeti.IdempotentMonoid.kZeroEquiv`: the group completion of `V(R)` is `K₀(R)`, the split `K₀`
  of finitely generated projective right `R`-modules.
* `TauCeti.IdempotentMonoid.toSplitK0`: the class map `V(A) → K₀(A)`, `[e] ↦ [Aⁿe]`, for left
  modules.
* `TauCeti.IdempotentMonoid.splitK0Equiv`: the group completion of `V(A)` is the split `K₀` of
  finitely generated projective left `A`-modules.

## Main results

* `TauCeti.IdempotentMonoid.kZeroEquiv_of_mk`: the class of `e` goes to the class `[eRⁿ]`, and
  `TauCeti.IdempotentMonoid.kZeroEquiv_of_mk_one`: the class of `1ₘ` goes to `m[R]`.
* `TauCeti.IdempotentMonoid.exists_kZeroEquiv_sub_nsmul_eq`: every element of `K₀(R)` is
  `[eRⁿ] - m[R]`.
* `TauCeti.IdempotentMonoid.splitK0Equiv_of_mk`: the class of `e` goes to the class `[Aⁿe]`.

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

private def objectCodeHom :
    IdempotentMonoid R →+ ObjectCode.{u} (FiniteProjectiveRight R) where
  toFun := objectCodeFun R
  map_zero' := by
    let Z := FiniteProjectiveModules.ofIdempotent (0 : Matrix (Fin 0) (Fin 0) R)
      IsIdempotentElem.zero
    have hsub : Subsingleton ((finiteProjectiveModules Rᵐᵒᵖ).ι.obj Z) :=
      (FiniteProjectiveModules.ofIdempotentLinearEquiv
        (0 : Matrix (Fin 0) (Fin 0) R) IsIdempotentElem.zero).toEquiv.subsingleton
    have hzero : Limits.IsZero Z :=
      Limits.IsZero.of_full_of_faithful_of_isZero (finiteProjectiveModules Rᵐᵒᵖ).ι Z
        (ModuleCat.isZero_of_subsingleton _)
    exact (objectCodeFun_mk (0 : Matrix (Fin 0) (Fin 0) R) IsIdempotentElem.zero).trans
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

private theorem objectCodeHom_apply (x : IdempotentMonoid R) :
    objectCodeHom R x = objectCodeFun R x :=
  (rfl)

private theorem objectCodeHom_bijective : Function.Bijective (objectCodeHom R) :=
  ⟨fun a b hab ↦ by
    induction a using ind with | mk m e he =>
    induction b using ind with | mk n f hf =>
    rw [objectCodeHom_apply R, objectCodeHom_apply R, objectCodeFun_mk e he,
      objectCodeFun_mk f hf, objectCode_eq_objectCode_iff.{u}] at hab
    obtain ⟨iso⟩ := hab
    exact (mk_eq_mk_iff he hf).mpr
      ((nonempty_linearEquiv_range_mulVecBilin_iff he hf).mp
        ⟨(FiniteProjectiveModules.ofIdempotentLinearEquiv e he).symm.trans
          (((finiteProjectiveModules Rᵐᵒᵖ).ι.mapIso iso).toLinearEquiv.trans
            (FiniteProjectiveModules.ofIdempotentLinearEquiv f hf))⟩),
  fun c ↦ by
    obtain ⟨P, rfl⟩ := objectCode_surjective.{u} c
    have : Module.Finite Rᵐᵒᵖ P.obj := (finiteProjectiveModules_iff.mp P.property).1
    have : Module.Projective Rᵐᵒᵖ P.obj := (finiteProjectiveModules_iff.mp P.property).2
    obtain ⟨n, e, he, ⟨θ⟩⟩ := Module.Finite.exists_linearEquiv_range_mulVecBilin R P.obj
    exact ⟨mk e he, (objectCodeHom_apply R (mk e he)).trans (objectCodeFun_mk_linearEquiv he θ)⟩⟩

/-- **Idempotent presentation of the monoid of projective modules.** Sending the equivalence class
of `e` to the isomorphism class of its column range `e Rⁿ` is an isomorphism of additive
commutative monoids between `IdempotentMonoid R` and the isomorphism classes of finitely
generated projective right `R`-modules under binary biproducts. -/
def objectCodeAddEquiv :
    IdempotentMonoid R ≃+ ObjectCode.{u} (FiniteProjectiveRight R) :=
  AddEquiv.ofBijective (objectCodeHom R) (objectCodeHom_bijective R)

variable {R} in
/-- Evaluating `objectCodeAddEquiv` on `[e]` yields the code of any finitely generated projective
right `R`-module linearly isomorphic to `e R^ι`. -/
theorem objectCodeAddEquiv_mk_linearEquiv {ι : Type*} [Fintype ι] {e : Matrix ι ι R}
    (he : IsIdempotentElem e) {P : FiniteProjectiveRight R}
    (θ : P.obj ≃ₗ[Rᵐᵒᵖ] range (e.mulVecBilin R Rᵐᵒᵖ)) :
    objectCodeAddEquiv R (mk e he) = objectCode.{u} P := by
  rw [objectCodeAddEquiv, AddEquiv.ofBijective_apply, objectCodeHom_apply R]
  exact objectCodeFun_mk_linearEquiv he θ

variable {R} in
@[simp]
theorem objectCodeAddEquiv_mk {ι : Type*} [Fintype ι] (e : Matrix ι ι R)
    (he : IsIdempotentElem e) :
    objectCodeAddEquiv R (mk e he) = objectCode.{u} (FiniteProjectiveModules.ofIdempotent e he) :=
  objectCodeAddEquiv_mk_linearEquiv (P := FiniteProjectiveModules.ofIdempotent e he) he
    (FiniteProjectiveModules.ofIdempotentLinearEquiv e he)

/-- **`K₀(R)` is the group completion of the idempotent monoid `V(R)`.** Obtained by group
completing `TauCeti.IdempotentMonoid.objectCodeAddEquiv` and composing with
`TauCeti.SplitK0.grothendieckAddGroupEquiv`: the class of an idempotent matrix `e` goes to the
class `[eRⁿ]` of the image of its action on column vectors, a finitely generated projective right
`R`-module (`TauCeti.IdempotentMonoid.kZeroEquiv_of_mk`). -/
def kZeroEquiv : GrothendieckAddGroup (IdempotentMonoid R) ≃+ KZero R :=
  ((AddLocalization.addMonoidOf ⊤).addEquivOfAddEquiv
    (AddLocalization.addMonoidOf (M := ObjectCode.{u} (FiniteProjectiveRight R)) ⊤)
    (j := objectCodeAddEquiv R) (AddSubmonoid.map_equiv_top (objectCodeAddEquiv R))).trans
    (SplitK0.grothendieckAddGroupEquiv.{u} (FiniteProjectiveRight R))

variable {R} {ι : Type*} [Fintype ι]

/-- `TauCeti.IdempotentMonoid.kZeroEquiv` sends the class of an idempotent matrix `e` to the class
of any finitely generated projective right `R`-module isomorphic to `eRⁿ`, the image of the action
`v ↦ e *ᵥ v` of `e` on column vectors. -/
theorem kZeroEquiv_of_mk {e : Matrix ι ι R} (he : IsIdempotentElem e) (X : FiniteProjectiveRight R)
    (θ : X.obj ≃ₗ[Rᵐᵒᵖ] range (mulVecBilin R Rᵐᵒᵖ e)) :
    kZeroEquiv R (GrothendieckAddGroup.of (mk e he)) = SplitK0.of.{u} X := by
  have h : (AddLocalization.addMonoidOf ⊤).addEquivOfAddEquiv
      (AddLocalization.addMonoidOf (M := ObjectCode.{u} (FiniteProjectiveRight R)) ⊤)
      (AddSubmonoid.map_equiv_top (objectCodeAddEquiv R)) (GrothendieckAddGroup.of (mk e he)) =
        GrothendieckAddGroup.of (objectCodeAddEquiv R (mk e he)) :=
    AddSubmonoid.LocalizationMap.addEquivOfAddEquiv_eq _ _ _
  rw [kZeroEquiv, AddEquiv.trans_apply, h, objectCodeAddEquiv_mk_linearEquiv he θ,
    SplitK0.grothendieckAddGroupEquiv_of_objectCode]

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
  -- Transport `θ` across `opOp` and coordinatewise `MulOpposite.op`, turning row vectors `Aⁿe`
  -- into column vectors `(eᵀ.map op) (Aᵐᵒᵖ)ⁿ`.
  let ψ : range e.vecMulLinear ≃+ range ((eᵀ.map op).mulVecBilin Aᵐᵒᵖ Aᵐᵒᵖᵐᵒᵖ) :=
    { toFun := fun v ↦ ⟨op ∘ (v : ι → A), let ⟨u, hu⟩ := v.property; ⟨op ∘ u, funext fun i ↦ by
        simpa [mulVecBilin_apply, mulVec, vecMul, dotProduct] using congrArg op (congrFun hu i)⟩⟩
      invFun := fun w ↦ ⟨unop ∘ (w : ι → Aᵐᵒᵖ), let ⟨u, hu⟩ := w.property
        ⟨unop ∘ u, funext fun i ↦ by
          simpa [mulVecBilin_apply, mulVec, vecMul, dotProduct] using
            congrArg unop (congrFun hu i)⟩⟩
      left_inv := fun _ ↦ Subtype.ext (funext fun _ ↦ rfl)
      right_inv := fun _ ↦ Subtype.ext (funext fun _ ↦ rfl)
      map_add' := fun _ _ ↦ rfl }
  let θ' : Y.obj ≃ₗ[Aᵐᵒᵖᵐᵒᵖ] range ((eᵀ.map op).mulVecBilin Aᵐᵒᵖ Aᵐᵒᵖᵐᵒᵖ) :=
    { toFun := fun x ↦ ψ (θ (eY x)), invFun := fun y ↦ eY.symm (θ.symm (ψ.symm y))
      left_inv := (eY.toEquiv.trans (θ.toEquiv.trans ψ.toEquiv)).left_inv
      right_inv := (eY.toEquiv.trans (θ.toEquiv.trans ψ.toEquiv)).right_inv
      map_add' := fun x y ↦ by rw [eY.map_add, θ.map_add, ψ.map_add]
      map_smul' := fun c x ↦ by
        induction c using MulOpposite.rec' with | h c =>
        induction c using MulOpposite.rec' with | h a =>
        have hact : eY (op (op a) • x) = a • eY x := eY.map_smulₛₗ (op (op a)) x
        apply Subtype.ext; ext i
        dsimp only [ψ, AddEquiv.coe_mk, Equiv.coe_fn_mk, Function.comp_apply]
        rw [hact, θ.map_smul, RingHom.id_apply]; exact op_mul a _ }
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
