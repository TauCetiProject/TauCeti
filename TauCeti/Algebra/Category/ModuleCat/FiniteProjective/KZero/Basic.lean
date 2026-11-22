/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.KZero.Defs
public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.SplitK0.Basic

import TauCeti.Algebra.Ring.Opposite

/-!
# Algebraic `K₀` of a ring and covariant functoriality

Built on `TauCeti.KZero R` and `TauCeti.KZero.regular` (from
`TauCeti.Algebra.Category.ModuleCat.FiniteProjective.KZero.Defs`), this file provides:

* the standard normal form `[P] - n • [R]` (`TauCeti.KZero.exists_eq_of_sub_nsmul_regular`),
* covariant functoriality (`TauCeti.KZero.map`, `RingEquiv.kZeroEquiv`),
* comparison with left-module `SplitK0` for commutative rings
  (`TauCeti.KZero.commRingLeftSplitK0Equiv`).

## References

* C. A. Weibel, *The K-book*, Chapter II, §2, Lemma 2.1, Examples 2.1.1–2.1.2, §2.8.
-/

public section

open CategoryTheory MulOpposite

universe u

namespace TauCeti.KZero

variable {R S T : Type u} [Ring R] [Ring S] [Ring T]

/-- Every class in `KZero R` has the form `[P] - n • [R]`. -/
theorem exists_eq_of_sub_nsmul_regular (x : KZero R) :
    ∃ (P : FiniteProjectiveRight R) (n : ℕ),
      x = SplitK0.of.{u} P - n • regular R :=
  regular_def R ▸ SplitK0.exists_eq_of_sub_nsmul_finiteProjectiveModulesRegular x

/-- **Covariant functoriality of `KZero`**, via balanced extension of scalars along
`RingHom.op f : Rᵐᵒᵖ →+* Sᵐᵒᵖ`. -/
@[expose] noncomputable def map (f : R →+* S) : KZero R →+ KZero S :=
  SplitK0.map.{u, u} (RingHom.op f).finiteProjectiveModulesExtendScalars

@[simp] theorem map_of (f : R →+* S) (P) : map f (SplitK0.of.{u} P) =
    SplitK0.of.{u} ((RingHom.op f).finiteProjectiveModulesExtendScalars.obj P) :=
  SplitK0.map_of.{u, u} _ P

@[simp] theorem map_id (R : Type u) [Ring R] : map (RingHom.id R) = AddMonoidHom.id _ :=
  (SplitK0.map_finiteProjectiveModulesExtendScalars_congr (RingHom.op_id R)).trans
    SplitK0.map_finiteProjectiveModulesExtendScalars_id

theorem map_comp (f : R →+* S) (g : S →+* T) : map (g.comp f) = (map g).comp (map f) :=
  (SplitK0.map_finiteProjectiveModulesExtendScalars_congr (RingHom.op_comp f g)).trans
    (SplitK0.map_finiteProjectiveModulesExtendScalars_comp (RingHom.op g))

@[simp] theorem map_map (f : R →+* S) (g : S →+* T) (x : KZero R) :
    map g (map f x) = map (g.comp f) x := (DFunLike.congr_fun (map_comp f g) x).symm

@[simp] theorem map_regular (f : R →+* S) : map f (regular R) = regular S := by
  simp [map, regular_def]

end TauCeti.KZero

namespace RingEquiv

open TauCeti

variable {R S T : Type u} [Ring R] [Ring S] [Ring T]

/-- A ring isomorphism `e : R ≃+* S` induces an isomorphism `KZero R ≃+ KZero S`. -/
noncomputable def kZeroEquiv (e : R ≃+* S) : KZero R ≃+ KZero S :=
  (RingEquiv.op e).finiteProjectiveModulesSplitK0Equiv

@[simp] theorem kZeroEquiv_apply (e : R ≃+* S) (x : KZero R) :
    e.kZeroEquiv x = KZero.map e.toRingHom x :=
  (RingEquiv.op e).finiteProjectiveModulesSplitK0Equiv_apply x

@[simp] theorem kZeroEquiv_symm (e : R ≃+* S) :
    e.kZeroEquiv.symm = e.symm.kZeroEquiv :=
  (RingEquiv.op e).finiteProjectiveModulesSplitK0Equiv_symm

theorem kZeroEquiv_trans (e : R ≃+* S) (e' : S ≃+* T) :
    (e.trans e').kZeroEquiv = e.kZeroEquiv.trans e'.kZeroEquiv := by
  ext; simp [RingEquiv.toRingHom_trans]

@[simp] theorem kZeroEquiv_refl (R : Type u) [Ring R] :
    (RingEquiv.refl R).kZeroEquiv = AddEquiv.refl (KZero R) := by ext; simp

end RingEquiv

namespace TauCeti.KZero

section CommRing
variable (R : Type u) [CommRing R]

/-- For a commutative ring `R`, `RingEquiv.toOpposite R` identifies `KZero R` with
left-module `SplitK0`. -/
noncomputable def commRingLeftSplitK0Equiv :
    KZero R ≃+ SplitK0.{u} (finiteProjectiveModules R).FullSubcategory :=
  (RingEquiv.toOpposite R).symm.finiteProjectiveModulesSplitK0Equiv

theorem commRingLeftSplitK0Equiv_apply (x : KZero R) :
    commRingLeftSplitK0Equiv R x =
      (RingEquiv.toOpposite R).symm.finiteProjectiveModulesSplitK0Equiv x := (rfl)

theorem commRingLeftSplitK0Equiv_symm_apply (x) : (commRingLeftSplitK0Equiv R).symm x =
    (RingEquiv.toOpposite R).finiteProjectiveModulesSplitK0Equiv x := by
  simp [commRingLeftSplitK0Equiv]

@[simp] theorem commRingLeftSplitK0Equiv_of (P) :
    commRingLeftSplitK0Equiv R (SplitK0.of.{u} P) = SplitK0.of.{u}
      ((RingEquiv.toOpposite R).symm.toRingHom.finiteProjectiveModulesExtendScalars.obj P) := by
  simp [commRingLeftSplitK0Equiv_apply]

@[simp] theorem commRingLeftSplitK0Equiv_symm_of (P) :
    (commRingLeftSplitK0Equiv R).symm (SplitK0.of.{u} P) = SplitK0.of.{u}
      ((RingEquiv.toOpposite R).toRingHom.finiteProjectiveModulesExtendScalars.obj P) := by
  simp [commRingLeftSplitK0Equiv_symm_apply]

@[simp] theorem commRingLeftSplitK0Equiv_regular :
    commRingLeftSplitK0Equiv R (regular R) =
      SplitK0.of.{u} (finiteProjectiveModulesRegular R) := by
  simp [commRingLeftSplitK0Equiv_apply, regular_def]

end CommRing

end TauCeti.KZero
