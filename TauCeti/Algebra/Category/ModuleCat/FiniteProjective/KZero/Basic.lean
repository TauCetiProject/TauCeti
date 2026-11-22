/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.KZero.Defs
public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.SplitK0

import TauCeti.Algebra.Ring.Opposite

/-!
# Algebraic `K₀` of a ring, functoriality, and Morita invariance

Built on `TauCeti.KZero R` and `TauCeti.KZero.regular` (from
`TauCeti.Algebra.Category.ModuleCat.FiniteProjective.KZero.Defs`), this file provides covariant
functoriality (`KZero.map`, `RingEquiv.kZeroEquiv`), comparison with left-module `SplitK0` for
commutative rings (`KZero.commRingLeftSplitK0Equiv`), binary product decomposition
(`KZero.prodEquiv`), and matrix Morita invariance (`KZero.matrixEquiv`).

## References

* C. A. Weibel, *The K-book*, Chapter II, §2, Lemma 2.1, Examples 2.1.1–2.1.2, Prop. 2.4, §2.8.
-/

public section

open CategoryTheory MulOpposite

universe u v

namespace TauCeti.KZero

variable {R S T : Type u} [Ring R] [Ring S] [Ring T]

/-- Every class in `KZero R` has the form `[P] - n • [R]`. -/
theorem exists_eq_of_sub_nsmul_regular (x : KZero R) :
    ∃ (P : FiniteProjectiveRight R) (n : ℕ),
      x = SplitK0.of.{u} P - n • regular R :=
  regular_def R ▸ SplitK0.exists_eq_of_sub_nsmul_finiteProjectiveModulesRegular x

/-- **Covariant functoriality of `KZero`**, via balanced extension of scalars along
`RingHom.op f : Rᵐᵒᵖ →+* Sᵐᵒᵖ`. -/
noncomputable def map (f : R →+* S) : KZero R →+ KZero S :=
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

/-- **Product decomposition:** `KZero (R × S) ≃+ KZero R × KZero S`. -/
noncomputable def prodEquiv (R S : Type u) [Ring R] [Ring S] :
    KZero (R × S) ≃+ KZero R × KZero S :=
  (RingEquiv.prodMulOpposite R S).finiteProjectiveModulesSplitK0Equiv.trans
    (finiteProjectiveModulesProdSplitK0Equiv Rᵐᵒᵖ Sᵐᵒᵖ)

@[simp] theorem prodEquiv_apply (R S : Type u) [Ring R] [Ring S] (x : KZero (R × S)) :
    prodEquiv R S x = (map (RingHom.fst R S) x, map (RingHom.snd R S) x) := by
  simp only [prodEquiv, AddEquiv.trans_apply, RingEquiv.finiteProjectiveModulesSplitK0Equiv_apply,
    finiteProjectiveModulesProdSplitK0Equiv_apply,
    SplitK0.map_finiteProjectiveModulesExtendScalars_apply_map]
  exact Prod.ext (DFunLike.congr_fun (SplitK0.map_finiteProjectiveModulesExtendScalars_congr
    (RingEquiv.fst_comp_prodMulOpposite R S)) x) (DFunLike.congr_fun
      (SplitK0.map_finiteProjectiveModulesExtendScalars_congr
        (RingEquiv.snd_comp_prodMulOpposite R S)) x)

@[simp] theorem prodEquiv_symm_apply (R S : Type u) [Ring R] [Ring S]
    (x : KZero R × KZero S) : (prodEquiv R S).symm x =
      SplitK0.map.{u, u} ((RingHom.op (RingHom.fst R S)).finiteProjectiveModulesRestrictScalars
        (RingHom.finite_op_fst R S) (RingHom.projective_op_fst R S)) x.1 +
      SplitK0.map.{u, u} ((RingHom.op (RingHom.snd R S)).finiteProjectiveModulesRestrictScalars
        (RingHom.finite_op_snd R S) (RingHom.projective_op_snd R S)) x.2 := by
  apply (prodEquiv R S).injective
  rw [AddEquiv.apply_symm_apply, prodEquiv_apply, map_add, map_add]
  refine Prod.ext ?_ ?_ <;>
    (dsimp only; rw [map, ← AddMonoidHom.comp_apply, ← AddMonoidHom.comp_apply])
  · rw [SplitK0.map_extendScalars_comp_restrictScalars_self _ (fun a ↦ ⟨op (a.unop, 0), rfl⟩),
      SplitK0.map_extendScalars_comp_restrictScalars_eq_zero _ _ _ _ (op (1, 0)) rfl rfl]; simp
  · rw [SplitK0.map_extendScalars_comp_restrictScalars_eq_zero _ _ _ _ (op (0, 1)) rfl rfl,
      SplitK0.map_extendScalars_comp_restrictScalars_self _ (fun b ↦ ⟨op (0, b.unop), rfl⟩)]; simp

section Matrix

variable (R : Type u) [Ring R] (ι : Type v) [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- **Matrix Morita invariance:** canonical isomorphism
`KZero.{u} R ≃+ KZero.{max u v} (Matrix ι ι R)` sending `|ι| • [R]` to `[M_ι(R)]`. -/
noncomputable def matrixEquiv : KZero.{u} R ≃+ KZero.{max u v} (Matrix ι ι R) :=
  (finiteProjectiveModulesMatrixSplitK0Equiv Rᵐᵒᵖ ι).trans
    (RingEquiv.mopMatrix (m := ι) (α := R)).finiteProjectiveModulesSplitK0Equiv

theorem matrixEquiv_apply (x : KZero.{u} R) :
    matrixEquiv R ι x = (RingEquiv.mopMatrix (m := ι) (α := R)).finiteProjectiveModulesSplitK0Equiv
      (finiteProjectiveModulesMatrixSplitK0Equiv Rᵐᵒᵖ ι x) := (rfl)

@[simp] theorem matrixEquiv_of (P) : matrixEquiv R ι (SplitK0.of.{u} P) = SplitK0.of.{max u v}
    ((RingEquiv.mopMatrix (m := ι) (α := R)).toRingHom.finiteProjectiveModulesExtendScalars.obj
      ((finiteProjectiveModulesToMatrixFunctor Rᵐᵒᵖ ι).obj P)) := by simp [matrixEquiv_apply]

@[simp] theorem matrixEquiv_card_nsmul_regular :
    matrixEquiv R ι (Fintype.card ι • regular R) = regular (Matrix ι ι R) := by
  simp [matrixEquiv_apply, regular_def]

end Matrix

/-- For every `i : ι`, `matrixEquiv` agrees with `ModuleCat.matrixEquivalence` composed with
`RingEquiv.mopMatrix`. -/
theorem matrixEquiv_eq (R : Type u) [Ring R] (ι : Type u) [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (i : ι) : matrixEquiv R ι =
      (ModuleCat.matrixEquivalence Rᵐᵒᵖ (ι := ι) i).finiteProjectiveModulesSplitK0Equiv.trans
        (RingEquiv.mopMatrix (m := ι) (α := R)).finiteProjectiveModulesSplitK0Equiv := by
  rw [matrixEquiv, finiteProjectiveModulesMatrixSplitK0Equiv_eq Rᵐᵒᵖ ι i]

end TauCeti.KZero
