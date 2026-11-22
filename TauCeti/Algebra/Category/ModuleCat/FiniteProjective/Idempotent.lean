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
# Projective `K₀` comparison: `ObjectCode`, scalar extension, and positive cone

Building on `TauCeti.IdempotentMonoid.kZeroEquiv` in
`TauCeti.Algebra.Category.ModuleCat.FiniteProjective.KZero.Idempotent`, this file establishes the
monoid-level comparison with `TauCeti.ObjectCode`, naturality under scalar extension, the stable
equivalence criterion in `K₀`, and the algebraic positive cone:

* `TauCeti.BalancedExtension.rangeMulVecBilinEquiv`: base change `(e R^ι) ⊗_R S ≃ f(e) S^ι` of
  the column range of an idempotent matrix along `f : R →+* S`;
* `TauCeti.IdempotentMonoid.objectCodeAddEquiv`: the monoid isomorphism
  `IdempotentMonoid R ≃+ ObjectCode (FiniteProjectiveRight R)` before group completion;
* `TauCeti.IdempotentMonoid.toKZero`: the right-module class map `IdempotentMonoid R →+ KZero R`
  (`kZeroEquiv` restricted along `GrothendieckAddGroup.of`), and its naturality under scalar
  extension (`TauCeti.IdempotentMonoid.map_toKZero` and
  `TauCeti.IdempotentMonoid.map_comp_kZeroEquiv`);
* `TauCeti.IdempotentMonoid.toKZero_mk_eq_toKZero_mk_iff`: two idempotents have the same class in
  `K₀(R)` if and only if they become equivalent after adding a common identity block `1ₖ`;
* `TauCeti.IdempotentMonoid.mem_mrange_toKZero_iff`: the image of `IdempotentMonoid R` in
  `K₀(R)` is the algebraic positive cone of classes `[P]` of actual finitely generated projective
  right `R`-modules, without assuming cancellation or antisymmetry;
* `TauCeti.IdempotentMonoid.toKZero_sub_one_eq_classOf_of_linearEquiv`: comparison of `[e] - [1ₘ]`
  with `FiniteProjectiveModules.classOf Rᵐᵒᵖ P m`.

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
  (congr (RingHom.op f) (rangeVecMulLinearTransposeMapOpEquiv e).symm).trans <|
    (rangeVecMulLinearEquiv (RingHom.op f) he.matrix_transpose_map_op).trans <|
      (LinearEquiv.ofEq _ _ (congrArg (fun M ↦ range M.vecMulLinear)
        (transpose_map_op_map_ringHom_op e f))).trans
        (rangeVecMulLinearTransposeMapOpEquiv (e.map f))

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
    LinearEquiv.trans_symm, congr_symm, LinearEquiv.symm_symm]
  simp only [LinearEquiv.trans_apply, rangeVecMulLinearEquiv_symm_apply, map_sum, congr_tmul]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hj : ((LinearEquiv.ofEq _ _ (congrArg (fun M ↦ range M.vecMulLinear)
      (transpose_map_op_map_ringHom_op e f))).symm
      ((rangeVecMulLinearTransposeMapOpEquiv (e.map f)).symm w) : ι → Sᵐᵒᵖ) j =
        op ((w : ι → S) j) := by
    simp
  rw [hj]
  exact congrArg (tmul (RingHom.op f) _) (Subtype.ext (by simp; rfl))

end BalancedExtension

end BalancedExtension

section FiniteProjective

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

section ObjectCode

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

private noncomputable def objectCodeFun :
    IdempotentMonoid R → ObjectCode.{u} (FiniteProjectiveRight R) :=
  lift (fun e he ↦ objectCode.{u} (FiniteProjectiveModules.ofIdempotent e he))
    fun _ _ he hg h ↦ objectCode_ofIdempotent_congr R he hg h

variable {R} in
private theorem objectCodeFun_mk_linearEquiv {ι : Type*} [Fintype ι] {e : Matrix ι ι R}
    (he : IsIdempotentElem e) {P : FiniteProjectiveRight R}
    (θ : P.obj ≃ₗ[Rᵐᵒᵖ] range (e.mulVecBilin R Rᵐᵒᵖ)) :
    objectCodeFun R (mk e he) = objectCode.{u} P := by
  let σ := Fintype.equivFin ι
  let hre := (he.idempotentEquivalent_reindex σ).isIdempotentElem_left
  let ψ := (FiniteProjectiveModules.ofIdempotentLinearEquiv (e.reindex σ σ) hre).trans
    (e.rangeMulVecBilinReindexEquiv σ σ).symm
  rw [← mk_reindex e he σ, objectCodeFun]
  exact (lift_mk (hF := fun _ _ he hg h ↦ objectCode_ofIdempotent_congr R he hg h) _ _).trans <|
    objectCode_congr.{u} (ObjectProperty.isoMk (finiteProjectiveModules Rᵐᵒᵖ)
      (X := FiniteProjectiveModules.ofIdempotent (e.reindex σ σ) hre)
      (Y := P) (ψ.trans θ.symm).toModuleIso)

variable {R} in
private theorem objectCodeFun_mk {ι : Type*} [Fintype ι] (e : Matrix ι ι R)
    (he : IsIdempotentElem e) :
    objectCodeFun R (mk e he) = objectCode.{u} (FiniteProjectiveModules.ofIdempotent e he) :=
  objectCodeFun_mk_linearEquiv (P := FiniteProjectiveModules.ofIdempotent e he) he
    (FiniteProjectiveModules.ofIdempotentLinearEquiv e he)

private noncomputable def objectCodeHom :
    IdempotentMonoid R →+ ObjectCode.{u} (FiniteProjectiveRight R) where
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
    exact (objectCodeFun_mk (0 : Matrix (Fin 0) (Fin 0) R) IsIdempotentElem.zero).trans
      ((objectCode_congr.{u} (hzero.iso (isZero_zero _))).trans objectCode_zero.{u})
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
noncomputable def objectCodeAddEquiv :
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

/-- The class of the `m × m` identity matrix in `K₀(R)` is `m` times the class of the rank-one
free right `R`-module. -/
theorem toKZero_mk_one (m : ℕ) :
    toKZero R (mk (1 : Matrix (Fin m) (Fin m) R) IsIdempotentElem.one) =
      m • SplitK0.of.{u} (finiteProjectiveModulesRegular Rᵐᵒᵖ) :=
  kZeroEquiv_of_mk_one m

end ObjectCode

section Functoriality

variable {R S : Type u} [Ring R] [Ring S]

/-- **Naturality of `toKZero` under scalar extension.** Extending scalars of right modules along
`f : R →+* S` intertwines `toKZero` with entrywise application of `f` on `IdempotentMonoid`. -/
@[simp]
theorem map_toKZero (f : R →+* S) (x : IdempotentMonoid R) :
    SplitK0.map.{u, u} (RingHom.op f).finiteProjectiveModulesExtendScalars (toKZero R x) =
      toKZero S (IdempotentMonoid.map f x) := by
  induction x using ind with | mk n e he =>
  rw [toKZero_mk, SplitK0.map_of,
    SplitK0.of_extendScalars_obj
      (Q := FiniteProjectiveModules.ofIdempotent (e.map f) (he.matrix_map f))
      ((BalancedExtension.congr (RingHom.op f)
        (FiniteProjectiveModules.ofIdempotentLinearEquiv e he)).trans
        ((BalancedExtension.rangeMulVecBilinEquiv f he).trans
          (FiniteProjectiveModules.ofIdempotentLinearEquiv (e.map f) (he.matrix_map f)).symm)),
    IdempotentMonoid.map_mk, toKZero_mk]

theorem toKZero_comp_map (f : R →+* S) :
    (toKZero S).comp (IdempotentMonoid.map f) =
      (SplitK0.map.{u, u} (RingHom.op f).finiteProjectiveModulesExtendScalars).comp
        (toKZero R) :=
  AddMonoidHom.ext fun x ↦ (map_toKZero f x).symm

/-- **Naturality of `kZeroEquiv` under scalar extension.** Along `f : R →+* S`, the
group-completion homomorphism induced by `IdempotentMonoid.map f` corresponds under `kZeroEquiv`
to `SplitK0.map` of scalar extension. -/
theorem map_comp_kZeroEquiv (f : R →+* S) :
    (SplitK0.map.{u, u} (RingHom.op f).finiteProjectiveModulesExtendScalars).comp
        (kZeroEquiv R).toAddMonoidHom =
      (kZeroEquiv S).toAddMonoidHom.comp
        (_root_.Algebra.GrothendieckAddGroup.lift
          (_root_.Algebra.GrothendieckAddGroup.of.comp (IdempotentMonoid.map f))) := by
  refine _root_.Algebra.GrothendieckAddGroup.lift.symm.injective ?_
  rw [_root_.Algebra.GrothendieckAddGroup.lift_symm_apply, AddMonoidHom.comp_assoc, ← toKZero,
    ← toKZero_comp_map, _root_.Algebra.GrothendieckAddGroup.lift_symm_apply,
    AddMonoidHom.comp_assoc, ← _root_.Algebra.GrothendieckAddGroup.lift_symm_apply,
    Equiv.symm_apply_apply, ← AddMonoidHom.comp_assoc, ← toKZero]

end Functoriality

section PresentationAndCone

variable {R : Type u} [Ring R]

/-- Two idempotent matrices have the same class in `K₀(R)` if and only if their column ranges are
stably equivalent right `R`-modules. -/
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
`K₀(R)` if and only if they become equivalent after adding a common identity block `1ₖ`. -/
theorem toKZero_mk_eq_toKZero_mk_iff {ι κ : Type*} [Fintype ι] [Fintype κ]
    {e : Matrix ι ι R} {f : Matrix κ κ R} {he : IsIdempotentElem e} {hf : IsIdempotentElem f} :
    toKZero R (mk e he) = toKZero R (mk f hf) ↔
      ∃ k : ℕ, IdempotentEquivalent (fromBlocks e 0 0 (1 : Matrix (Fin k) (Fin k) R))
        (fromBlocks f 0 0 (1 : Matrix (Fin k) (Fin k) R)) :=
  toKZero_mk_eq_toKZero_mk_iff_stableEquivalent.trans
    (stableEquivalent_range_mulVecBilin_iff he hf)

/-- **Algebraic positive cone of projective `K₀`.** The image submonoid of `IdempotentMonoid R` in
`K₀(R)` consists precisely of the classes `[P]` of finitely generated projective right
`R`-modules. -/
theorem mem_mrange_toKZero_iff {x : KZero R} :
    x ∈ AddMonoidHom.mrange (toKZero R) ↔ ∃ P : FiniteProjectiveRight R, x = SplitK0.of.{u} P := by
  constructor
  · rintro ⟨a, rfl⟩
    induction a using ind with | mk n e he =>
    exact ⟨FiniteProjectiveModules.ofIdempotent e he, toKZero_mk e he⟩
  · rintro ⟨P, rfl⟩
    have : Module.Finite Rᵐᵒᵖ P.obj := (finiteProjectiveModules_iff.mp P.property).1
    have : Module.Projective Rᵐᵒᵖ P.obj := (finiteProjectiveModules_iff.mp P.property).2
    obtain ⟨n, e, he, ⟨θ⟩⟩ := Module.Finite.exists_linearEquiv_range_mulVecBilin R P.obj
    exact ⟨mk e he, toKZero_mk_linearEquiv he θ⟩

/-- Subtracting `[1ₘ]` from `[e]` in `K₀(R)` gives the relative class
`FiniteProjectiveModules.classOf Rᵐᵒᵖ P m = [P] - m[R]` of any finitely generated projective right
`R`-module `P` linearly isomorphic to `e R^ι`. -/
theorem toKZero_sub_one_eq_classOf_of_linearEquiv {ι : Type*} [Fintype ι] {e : Matrix ι ι R}
    (he : IsIdempotentElem e) {P : Type u} [AddCommGroup P] [Module Rᵐᵒᵖ P] [Module.Finite Rᵐᵒᵖ P]
    [Module.Projective Rᵐᵒᵖ P] (θ : P ≃ₗ[Rᵐᵒᵖ] range (e.mulVecBilin R Rᵐᵒᵖ)) (m : ℕ) :
    toKZero R (mk e he) -
        toKZero R (mk (1 : Matrix (Fin m) (Fin m) R) IsIdempotentElem.one) =
      FiniteProjectiveModules.classOf Rᵐᵒᵖ P m := by
  rw [toKZero_mk_linearEquiv
      (P := ⟨ModuleCat.of Rᵐᵒᵖ P, finiteProjectiveModules_iff.mpr ⟨inferInstance, inferInstance⟩⟩)
      he θ,
    toKZero_mk_one, FiniteProjectiveModules.classOf_def,
    SplitK0.of_congr.{u} (X := finiteProjectiveModulesRegular Rᵐᵒᵖ)
      (Y := ⟨ModuleCat.of Rᵐᵒᵖ Rᵐᵒᵖ,
        finiteProjectiveModules_iff.2 ⟨inferInstance, inferInstance⟩⟩)
      (ObjectProperty.isoMk _ (Iso.refl _))]

end PresentationAndCone

end IdempotentMonoid

end FiniteProjective

end TauCeti
