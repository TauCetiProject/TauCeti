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

Building on `TauCeti.IdempotentMonoid.kZeroEquiv` and
`TauCeti.IdempotentMonoid.objectCodeAddEquiv` in
`TauCeti.Algebra.Category.ModuleCat.FiniteProjective.KZero.Idempotent`, this file establishes
the factorization of `toKZero` through `SplitK0.ofCode` and `objectCodeAddEquiv`, naturality under
scalar extension, the stable equivalence criterion in `K₀`, and the algebraic positive cone:

* `TauCeti.BalancedExtension.rangeMulVecBilinEquiv`: base change `(e R^ι) ⊗_R S ≃ f(e) S^ι` of
  the column range of an idempotent matrix along `f : R →+* S`;
* `TauCeti.IdempotentMonoid.toKZero`: the right-module class map `IdempotentMonoid R →+ KZero R`
  (`kZeroEquiv` restricted along `GrothendieckAddGroup.of`), its factorization
  `TauCeti.IdempotentMonoid.ofCode_comp_objectCodeAddEquiv` through `SplitK0.ofCode`, and its
  naturality under scalar extension (`TauCeti.IdempotentMonoid.map_toKZero` and
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

/-- `TauCeti.IdempotentMonoid.toKZero R` factors through the monoid isomorphism
`TauCeti.IdempotentMonoid.objectCodeAddEquiv R` and `TauCeti.SplitK0.ofCode`. -/
theorem ofCode_comp_objectCodeAddEquiv :
    SplitK0.ofCode.{u}.comp (objectCodeAddEquiv R).toAddMonoidHom = toKZero R := by
  ext n e he
  simp

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
      toKZero S (IdempotentMonoid.map f.toNonUnitalRingHom x) := by
  induction x using ind with | mk n e he =>
  rw [toKZero_mk, SplitK0.map_of,
    SplitK0.of_extendScalars_obj
      (Q := FiniteProjectiveModules.ofIdempotent (e.map f) (he.matrix_map f))
      ((BalancedExtension.congr (RingHom.op f)
        (FiniteProjectiveModules.ofIdempotentLinearEquiv e he)).trans
        ((BalancedExtension.rangeMulVecBilinEquiv f he).trans
          (FiniteProjectiveModules.ofIdempotentLinearEquiv (e.map f) (he.matrix_map f)).symm)),
    IdempotentMonoid.map_mk]
  exact (toKZero_mk (e.map f.toNonUnitalRingHom) (he.matrix_map f.toNonUnitalRingHom)).symm

theorem toKZero_comp_map (f : R →+* S) :
    (toKZero S).comp (IdempotentMonoid.map f.toNonUnitalRingHom) =
      (SplitK0.map.{u, u} (RingHom.op f).finiteProjectiveModulesExtendScalars).comp
        (toKZero R) :=
  AddMonoidHom.ext fun x ↦ (map_toKZero f x).symm

/-- **Naturality of `kZeroEquiv` under scalar extension.** Along `f : R →+* S`, the
group-completion homomorphism induced by `IdempotentMonoid.map f.toNonUnitalRingHom` corresponds
under `kZeroEquiv` to `SplitK0.map` of scalar extension. -/
theorem map_comp_kZeroEquiv (f : R →+* S) :
    (SplitK0.map.{u, u} (RingHom.op f).finiteProjectiveModulesExtendScalars).comp
        (kZeroEquiv R).toAddMonoidHom =
      (kZeroEquiv S).toAddMonoidHom.comp
        (_root_.Algebra.GrothendieckAddGroup.lift
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
  rw [← ofCode_comp_objectCodeAddEquiv R]
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨P, hP⟩ := objectCode_surjective.{u} (objectCodeAddEquiv R a)
    exact ⟨P, by rw [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, ← hP,
      SplitK0.ofCode_objectCode]⟩
  · rintro ⟨P, rfl⟩
    obtain ⟨a, ha⟩ := (objectCodeAddEquiv R).surjective (objectCode.{u} P)
    exact ⟨a, by rw [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, ha,
      SplitK0.ofCode_objectCode]⟩

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
