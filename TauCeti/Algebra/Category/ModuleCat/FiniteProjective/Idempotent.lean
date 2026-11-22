/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.KZero.Idempotent
public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.ScalarChange
public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.StableEquivalent

/-!
# Projective `K₀` comparison: `ObjectCode`, scalar extension, and positive cone

Building on `TauCeti.IdempotentMonoid.kZeroEquiv` and `TauCeti.IdempotentMonoid.objectCodeAddEquiv`,
this file packages `toKZero : IdempotentMonoid R →+ KZero R` (`ofCode_comp_objectCodeAddEquiv`),
the base-change isomorphism `FiniteProjectiveModules.extendScalarsOfIdempotentIso` with its
forward/inverse computation lemmas, naturality under scalar extension (`map_toKZero`,
`map_comp_kZeroEquiv`), `toKZero_mk_eq_toKZero_mk_iff`, positive cone `mem_mrange_toKZero_iff`, and
`toKZero_sub_one_eq_classOf_of_linearEquiv`.

## References

* J. Rosenberg, *Algebraic K-Theory and Its Applications*, §1.2.
* C. A. Weibel, *The K-book*, Chapter II, §2.
* B. Blackadar, *K-Theory for Operator Algebras*, §§1.7.2 and 4.6.
-/

public section

open CategoryTheory CategoryTheory.Limits LinearMap Matrix MulOpposite ZeroObject

universe u

namespace TauCeti

section FiniteProjective

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

private theorem eqToHom_hom_eqToHom_hom {S : Type u} [Ring S] {M N : ModuleCat Sᵐᵒᵖ}
    (h1 : M = N) (h2 : N = M) (y : M) : (eqToHom h2).hom ((eqToHom h1).hom y) = y := by
  cases h1; rfl

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
  rw [ofIdempotentLinearEquiv_extendScalarsOfIdempotentIso_hom_apply, eqToHom_hom_eqToHom_hom]; simp

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
  dsimp [extendScalarsOfIdempotentIso]
  simp only [ObjectProperty.isoMk_inv, Iso.trans_inv, LinearEquiv.toModuleIso_inv,
    LinearEquiv.trans_symm, LinearEquiv.symm_symm, BalancedExtension.congr_symm, eqToIso.inv,
    ObjectProperty.homMk_hom, ModuleCat.hom_comp, ConcreteCategory.hom_ofHom, coe_comp,
    LinearEquiv.coe_coe, Function.comp_apply, LinearEquiv.trans_apply]
  rw [eqToHom_hom_eqToHom_hom]; simp

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
  rw [balancedExtensionCongr_extendScalarsOfIdempotentIso_inv_apply, eqToHom_hom_eqToHom_hom]; simp

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
    kZeroEquiv R (_root_.Algebra.GrothendieckAddGroup.of x) = toKZero R x :=
  (rfl)

@[simp]
theorem lift_toKZero :
    _root_.Algebra.GrothendieckAddGroup.lift (toKZero R) = (kZeroEquiv R).toAddMonoidHom :=
  _root_.Algebra.GrothendieckAddGroup.lift.eq_symm_apply.mp
    (_root_.Algebra.GrothendieckAddGroup.lift_symm_apply _).symm

variable {R} in
/-- If a finitely generated projective right `R`-module `P` is linearly isomorphic to `e R^ι`, then
`toKZero` sends `[e]` to `[P]`. -/
theorem toKZero_mk_linearEquiv {ι : Type*} [Fintype ι] {e : Matrix ι ι R}
    (he : IsIdempotentElem e) {P : FiniteProjectiveRight R}
    (θ : P.obj ≃ₗ[Rᵐᵒᵖ] range (e.mulVecBilin R Rᵐᵒᵖ)) :
    toKZero R (mk e he) = SplitK0.of.{u} P :=
  kZeroEquiv_of_mk he P θ

variable {R} in
@[simp]
theorem toKZero_mk {ι : Type*} [Fintype ι] (e : Matrix ι ι R) (he : IsIdempotentElem e) :
    toKZero R (mk e he) = SplitK0.of.{u} (FiniteProjectiveModules.ofIdempotent e he) :=
  toKZero_mk_linearEquiv (P := FiniteProjectiveModules.ofIdempotent e he) he
    (FiniteProjectiveModules.ofIdempotentLinearEquiv e he)

/-- `TauCeti.IdempotentMonoid.toKZero R` factors via `objectCodeAddEquiv R` and `SplitK0.ofCode`. -/
theorem ofCode_comp_objectCodeAddEquiv :
    SplitK0.ofCode.{u}.comp (objectCodeAddEquiv R).toAddMonoidHom = toKZero R := by
  ext n e he; simp

/-- The class of `1ₘ` in `K₀(R)` is `m` times the class of the rank-one free right `R`-module. -/
theorem toKZero_mk_one (m : ℕ) :
    toKZero R (mk (1 : Matrix (Fin m) (Fin m) R) IsIdempotentElem.one) =
      m • SplitK0.of.{u} (finiteProjectiveModulesRegular Rᵐᵒᵖ) :=
  kZeroEquiv_of_mk_one m

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
  refine _root_.Algebra.GrothendieckAddGroup.lift.symm.injective ?_
  rw [_root_.Algebra.GrothendieckAddGroup.lift_symm_apply, AddMonoidHom.comp_assoc, ← toKZero,
    ← toKZero_comp_map, _root_.Algebra.GrothendieckAddGroup.lift_symm_apply,
    AddMonoidHom.comp_assoc, ← _root_.Algebra.GrothendieckAddGroup.lift_symm_apply,
    Equiv.symm_apply_apply, ← AddMonoidHom.comp_assoc, ← toKZero]

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
  · rintro ⟨a, rfl⟩
    obtain ⟨P, hP⟩ := objectCode_surjective.{u} (objectCodeAddEquiv R a)
    exact ⟨P, by simp [← hP]⟩
  · rintro ⟨P, rfl⟩
    obtain ⟨a, ha⟩ := (objectCodeAddEquiv R).surjective (objectCode.{u} P)
    exact ⟨a, by simp [ha]⟩

/-- Subtracting `[1ₘ]` from `[e]` in `K₀(R)` gives `classOf Rᵐᵒᵖ P m = [P] - m[R]`. -/
theorem toKZero_sub_one_eq_classOf_of_linearEquiv {ι : Type*} [Fintype ι] {e : Matrix ι ι R}
    (he : IsIdempotentElem e) {P : Type u} [AddCommGroup P] [Module Rᵐᵒᵖ P] [Module.Finite Rᵐᵒᵖ P]
    [Module.Projective Rᵐᵒᵖ P] (θ : P ≃ₗ[Rᵐᵒᵖ] range (e.mulVecBilin R Rᵐᵒᵖ)) (m : ℕ) :
    toKZero R (mk e he) - toKZero R (mk (1 : Matrix (Fin m) (Fin m) R) IsIdempotentElem.one) =
      FiniteProjectiveModules.classOf Rᵐᵒᵖ P m := by
  rw [toKZero_mk_linearEquiv (P := ⟨ModuleCat.of Rᵐᵒᵖ P, finiteProjectiveModules_iff.mpr
      ⟨inferInstance, inferInstance⟩⟩) he θ, toKZero_mk_one, FiniteProjectiveModules.classOf_def,
    SplitK0.of_congr.{u} (X := finiteProjectiveModulesRegular Rᵐᵒᵖ) (Y := ⟨ModuleCat.of Rᵐᵒᵖ Rᵐᵒᵖ,
      finiteProjectiveModules_iff.2 ⟨inferInstance, inferInstance⟩⟩)
      (ObjectProperty.isoMk _ (Iso.refl _))]

end PresentationAndCone

end IdempotentMonoid

end FiniteProjective

end TauCeti
