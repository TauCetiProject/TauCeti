/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.SplitK0

import Mathlib.Algebra.Field.Opposite
import TauCeti.Algebra.Ring.Opposite

/-!
# Algebraic `K₀` of a ring, functoriality, Morita invariance, and rank computations

For a possibly noncommutative ring `R`, this file defines algebraic `K₀` in the right-module
convention `AlgebraicK0 R := SplitK0 (finiteProjectiveModules Rᵐᵒᵖ).FullSubcategory`, matching
`TauCeti.AlgebraicK1` and Weibel, *The K-book*, Definition II.2.1, building on
`TauCeti.Algebra.Category.ModuleCat.FiniteProjective.SplitK0`.

## Main definitions

* `TauCeti.AlgebraicK0`, `TauCeti.AlgebraicK0.freeRankOne`, and `TauCeti.AlgebraicK0.one`:
  algebraic `K₀` of a ring `R` and the canonical class `[R]` of the free right `R`-module of rank 1.
* `TauCeti.AlgebraicK0.map`, `RingEquiv.algebraicK0Equiv`, and
  `TauCeti.AlgebraicK0.commRingLeftSplitK0Equiv`: covariant functoriality along `R →+* S`, induced
  isomorphisms for `R ≃+* S`, and comparison with left-module `SplitK0` when `R` is commutative.
* `TauCeti.AlgebraicK0.prodEquiv`, `TauCeti.AlgebraicK0.matrixEquiv`, and
  `TauCeti.AlgebraicK0.matrixFinEquiv`: binary product decomposition and canonical index-independent
  matrix Morita isomorphisms.
* `TauCeti.AlgebraicK0.finrankEquivDivisionRing`, `TauCeti.AlgebraicK0.finrankEquivPID`,
  `TauCeti.AlgebraicK0.finrankEquivInt`, and `TauCeti.AlgebraicK0.finrankEquivLocalRing`: rank
  isomorphisms `AlgebraicK0 R ≃+ ℤ` normalized so that `[R] ↦ 1`.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II, §2,
  Definition 2.1, Lemma 2.1, Examples 2.1.1–2.1.2, Proposition 2.4, and §2.8.
-/

public section

open CategoryTheory MulOpposite

universe u

namespace TauCeti

/-- **Algebraic `K₀` of a ring `R`**: the split Grothendieck group of finitely generated projective
right `R`-modules (encoded as left `Rᵐᵒᵖ`-modules). This matches the right-module convention of
`TauCeti.AlgebraicK1`, where `GL_n(R)` acts on finite free right `R`-modules. -/
abbrev AlgebraicK0 (R : Type u) [Ring R] : Type u :=
  SplitK0.{u} (finiteProjectiveModules Rᵐᵒᵖ).FullSubcategory

namespace AlgebraicK0

/-- The regular right `R`-module `R` (viewed as a left `Rᵐᵒᵖ`-module) in
`(finiteProjectiveModules Rᵐᵒᵖ).FullSubcategory`. -/
def freeRankOne (R : Type u) [Ring R] : (finiteProjectiveModules Rᵐᵒᵖ).FullSubcategory :=
  FiniteProjectiveModules.selfObj Rᵐᵒᵖ

/-- The canonical class `[R]` of the free right `R`-module of rank one in `AlgebraicK0 R`. -/
noncomputable def one (R : Type u) [Ring R] : AlgebraicK0 R := SplitK0.of.{u} (freeRankOne R)

theorem one_def (R : Type u) [Ring R] : one R = SplitK0.of.{u} (freeRankOne R) := (rfl)

/-- Every class in `AlgebraicK0 R` has the form `[P] - n • [R]` for some finitely generated
projective right `R`-module `P` and `n : ℕ`. -/
theorem exists_eq_of_sub_nsmul_one {R : Type u} [Ring R] (x : AlgebraicK0 R) :
    ∃ (P : (finiteProjectiveModules Rᵐᵒᵖ).FullSubcategory) (n : ℕ),
      x = SplitK0.of.{u} P - n • one R :=
  SplitK0.exists_eq_of_sub_nsmul_selfObj x

section Functoriality

variable {R S T : Type u} [Ring R] [Ring S] [Ring T]

/-- **Covariant functoriality of algebraic `K₀`.** A ring homomorphism `f : R →+* S` induces
`AlgebraicK0 R →+ AlgebraicK0 S` by balanced extension of scalars `P ↦ P ⊗_R S` on right modules
(encoded via `RingHom.op f : Rᵐᵒᵖ →+* Sᵐᵒᵖ`). -/
noncomputable def map (f : R →+* S) : AlgebraicK0 R →+ AlgebraicK0 S :=
  SplitK0.map.{u, u} (RingHom.op f).finiteProjectiveModulesExtendScalars

@[simp] theorem map_of (f : R →+* S) (P : (finiteProjectiveModules Rᵐᵒᵖ).FullSubcategory) :
    map f (SplitK0.of.{u} P) =
      SplitK0.of.{u} ((RingHom.op f).finiteProjectiveModulesExtendScalars.obj P) :=
  SplitK0.map_of.{u, u} _ P

@[simp] theorem map_id (R : Type u) [Ring R] : map (RingHom.id R) = AddMonoidHom.id _ :=
  (SplitK0.map_finiteProjectiveModulesExtendScalars_congr (RingHom.op_id R)).trans
    SplitK0.map_finiteProjectiveModulesExtendScalars_id

theorem map_comp (f : R →+* S) (g : S →+* T) : map (g.comp f) = (map g).comp (map f) :=
  (SplitK0.map_finiteProjectiveModulesExtendScalars_congr (RingHom.op_comp f g)).trans
    (SplitK0.map_finiteProjectiveModulesExtendScalars_comp (RingHom.op g))

@[simp] theorem map_map (f : R →+* S) (g : S →+* T) (x : AlgebraicK0 R) :
    map g (map f x) = map (g.comp f) x := (DFunLike.congr_fun (map_comp f g) x).symm

@[simp] theorem map_one (f : R →+* S) : map f (one R) = one S :=
  SplitK0.map_finiteProjectiveModulesExtendScalars_selfObj (RingHom.op f)

end Functoriality

end AlgebraicK0

end TauCeti

namespace RingEquiv

open TauCeti

section Basic

variable {R S T : Type u} [Ring R] [Ring S] [Ring T]

/-- A ring isomorphism `e : R ≃+* S` induces an isomorphism `AlgebraicK0 R ≃+ AlgebraicK0 S`. -/
noncomputable def algebraicK0Equiv (e : R ≃+* S) : AlgebraicK0 R ≃+ AlgebraicK0 S :=
  (RingEquiv.op e).finiteProjectiveModulesSplitK0Equiv

@[simp] theorem algebraicK0Equiv_apply (e : R ≃+* S) (x : AlgebraicK0 R) :
    e.algebraicK0Equiv x = AlgebraicK0.map e.toRingHom x :=
  (RingEquiv.op e).finiteProjectiveModulesSplitK0Equiv_apply x

@[simp] theorem algebraicK0Equiv_symm (e : R ≃+* S) :
    e.algebraicK0Equiv.symm = e.symm.algebraicK0Equiv :=
  (RingEquiv.op e).finiteProjectiveModulesSplitK0Equiv_symm

theorem algebraicK0Equiv_trans (e : R ≃+* S) (e' : S ≃+* T) :
    (e.trans e').algebraicK0Equiv = e.algebraicK0Equiv.trans e'.algebraicK0Equiv := by
  ext x; simp [RingEquiv.toRingHom_trans]

theorem algebraicK0Equiv_one (e : R ≃+* S) :
    e.algebraicK0Equiv (AlgebraicK0.one R) = AlgebraicK0.one S := by simp

end Basic

@[simp] theorem algebraicK0Equiv_refl (R : Type u) [Ring R] :
    (RingEquiv.refl R).algebraicK0Equiv = AddEquiv.refl (AlgebraicK0 R) := by ext x; simp

end RingEquiv

namespace TauCeti.AlgebraicK0

/-- For a commutative ring `R`, `RingEquiv.toOpposite R : R ≃+* Rᵐᵒᵖ` identifies `AlgebraicK0 R`
with the left-module `SplitK0` of `R` (and with `ExactK0 (finiteProjectiveModulesExactStructure R)`
after composing with `TauCeti.finiteProjectiveModulesSplitK0Equiv`). -/
noncomputable def commRingLeftSplitK0Equiv (R : Type u) [CommRing R] :
    AlgebraicK0 R ≃+ SplitK0.{u} (finiteProjectiveModules R).FullSubcategory :=
  (RingEquiv.toOpposite R).symm.finiteProjectiveModulesSplitK0Equiv

@[simp] theorem commRingLeftSplitK0Equiv_one (R : Type u) [CommRing R] :
    commRingLeftSplitK0Equiv R (one R) = SplitK0.of.{u} (FiniteProjectiveModules.selfObj R) :=
  ((RingEquiv.toOpposite R).symm.finiteProjectiveModulesSplitK0Equiv_apply (one R)).trans
    (SplitK0.map_finiteProjectiveModulesExtendScalars_selfObj _)

/-- Over a subsingleton (zero) ring, `AlgebraicK0 R` is trivial. -/
theorem subsingleton (R : Type u) [Ring R] [Subsingleton R] : Subsingleton (AlgebraicK0 R) :=
  inferInstance

/-- **Product decomposition of algebraic `K₀`.** For rings `R` and `S`,
`AlgebraicK0 (R × S) ≃+ AlgebraicK0 R × AlgebraicK0 S`, acting by `AlgebraicK0.map` along the two
projections. -/
noncomputable def prodEquiv (R S : Type u) [Ring R] [Ring S] :
    AlgebraicK0 (R × S) ≃+ AlgebraicK0 R × AlgebraicK0 S :=
  (RingEquiv.prodMulOpposite R S).finiteProjectiveModulesSplitK0Equiv.trans
    (finiteProjectiveModulesProdSplitK0Equiv Rᵐᵒᵖ Sᵐᵒᵖ)

@[simp] theorem prodEquiv_apply (R S : Type u) [Ring R] [Ring S] (x : AlgebraicK0 (R × S)) :
    prodEquiv R S x = (map (RingHom.fst R S) x, map (RingHom.snd R S) x) := by
  rw [prodEquiv, AddEquiv.trans_apply, RingEquiv.finiteProjectiveModulesSplitK0Equiv_apply,
    finiteProjectiveModulesProdSplitK0Equiv_apply,
    SplitK0.map_finiteProjectiveModulesExtendScalars_apply_map,
    SplitK0.map_finiteProjectiveModulesExtendScalars_apply_map]
  exact Prod.ext
    (DFunLike.congr_fun (SplitK0.map_finiteProjectiveModulesExtendScalars_congr
      (RingEquiv.fst_comp_prodMulOpposite R S)) x)
    (DFunLike.congr_fun (SplitK0.map_finiteProjectiveModulesExtendScalars_congr
      (RingEquiv.snd_comp_prodMulOpposite R S)) x)

theorem prodEquiv_one (R S : Type u) [Ring R] [Ring S] :
    prodEquiv R S (one (R × S)) = (one R, one S) := by simp

section Index

variable (R : Type u) [Ring R] (ι : Type u) [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- **Matrix Morita invariance of algebraic `K₀`.** For a nonempty finite index type `ι`,
`AlgebraicK0 R ≃+ AlgebraicK0 (Matrix ι ι R)` canonically (with no dependence on a chosen index in
`ι`), sending `|ι| • [R]` to `[Matrix ι ι R]`. -/
noncomputable def matrixEquiv : AlgebraicK0 R ≃+ AlgebraicK0 (Matrix ι ι R) :=
  (finiteProjectiveModulesMatrixSplitK0Equiv Rᵐᵒᵖ ι).trans
    (RingEquiv.mopMatrix (m := ι) (α := R)).finiteProjectiveModulesSplitK0Equiv

theorem matrixEquiv_apply (x : AlgebraicK0 R) :
    matrixEquiv R ι x =
      (RingEquiv.mopMatrix (m := ι) (α := R)).finiteProjectiveModulesSplitK0Equiv
        (finiteProjectiveModulesMatrixSplitK0Equiv Rᵐᵒᵖ ι x) := (rfl)

@[simp] theorem matrixEquiv_of (P : (finiteProjectiveModules Rᵐᵒᵖ).FullSubcategory) :
    matrixEquiv R ι (SplitK0.of.{u} P) = SplitK0.of.{u}
      ((RingEquiv.mopMatrix (m := ι) (α := R)).toRingHom.finiteProjectiveModulesExtendScalars.obj
        ((finiteProjectiveModulesToMatrixFunctor Rᵐᵒᵖ ι).obj P)) := by simp [matrixEquiv_apply]

/-- For every `i : ι`, `TauCeti.AlgebraicK0.matrixEquiv` agrees with the Morita equivalence
`ModuleCat.matrixEquivalence Rᵐᵒᵖ i` composed with `RingEquiv.mopMatrix`. -/
theorem matrixEquiv_eq (i : ι) :
    matrixEquiv R ι =
      (ModuleCat.matrixEquivalence Rᵐᵒᵖ (ι := ι) i).finiteProjectiveModulesSplitK0Equiv.trans
        (RingEquiv.mopMatrix (m := ι) (α := R)).finiteProjectiveModulesSplitK0Equiv := by
  rw [matrixEquiv, finiteProjectiveModulesMatrixSplitK0Equiv_eq Rᵐᵒᵖ ι i]

@[simp] theorem matrixEquiv_card_nsmul_one :
    matrixEquiv R ι (Fintype.card ι • one R) = one (Matrix ι ι R) := by
  rw [matrixEquiv_apply, one, freeRankOne,
    finiteProjectiveModulesMatrixSplitK0Equiv_card_nsmul_selfObj,
    RingEquiv.finiteProjectiveModulesSplitK0Equiv_apply]
  exact SplitK0.map_finiteProjectiveModulesExtendScalars_selfObj _

end Index

section Fin

variable (R : Type u) [Ring R] (n : ℕ) [NeZero n]

/-- **Matrix Morita invariance of algebraic `K₀` for `n × n` matrices (`n ≠ 0`)**, sending
`n • [R]` to `[Matrix (Fin n) (Fin n) R]`. -/
noncomputable def matrixFinEquiv : AlgebraicK0 R ≃+ AlgebraicK0 (Matrix (Fin n) (Fin n) R) :=
  (matrixEquiv R (ULift.{u} (Fin n))).trans
    (RingEquiv.algebraicK0Equiv
      (Matrix.reindexRingEquiv R (Equiv.ulift : ULift.{u} (Fin n) ≃ Fin n)))

theorem matrixFinEquiv_apply (x : AlgebraicK0 R) :
    matrixFinEquiv R n x =
      map (Matrix.reindexRingEquiv R (Equiv.ulift : ULift.{u} (Fin n) ≃ Fin n)).toRingHom
        (matrixEquiv R (ULift.{u} (Fin n)) x) := by
  rw [matrixFinEquiv, AddEquiv.trans_apply, RingEquiv.algebraicK0Equiv_apply]

@[simp] theorem matrixFinEquiv_of (P : (finiteProjectiveModules Rᵐᵒᵖ).FullSubcategory) :
    matrixFinEquiv R n (SplitK0.of.{u} P) =
      SplitK0.of.{u}
        ((RingHom.op (Matrix.reindexRingEquiv R
            Equiv.ulift).toRingHom).finiteProjectiveModulesExtendScalars.obj
          ((RingEquiv.mopMatrix (m := ULift.{u} (Fin n))
              (α := R)).toRingHom.finiteProjectiveModulesExtendScalars.obj
            ((finiteProjectiveModulesToMatrixFunctor Rᵐᵒᵖ (ULift.{u} (Fin n))).obj P))) := by
  rw [matrixFinEquiv_apply, matrixEquiv_of, map_of]

@[simp] theorem matrixFinEquiv_nsmul_one :
    matrixFinEquiv R n (n • one R) = one (Matrix (Fin n) (Fin n) R) := by
  have h := matrixEquiv_card_nsmul_one R (ULift.{u} (Fin n))
  simp only [Fintype.card_ulift, Fintype.card_fin] at h
  rw [matrixFinEquiv_apply, h, map_one]

end Fin

/-- **Rank isomorphism `AlgebraicK0 D ≃+ ℤ` over a division ring `D`**, normalized so that
`[D] ↦ 1`. -/
noncomputable def finrankEquivDivisionRing (D : Type u) [DivisionRing D] : AlgebraicK0 D ≃+ ℤ :=
  finiteProjectiveModulesFinrankSplitK0EquivDivisionRing Dᵐᵒᵖ

@[simp] theorem finrankEquivDivisionRing_of (D : Type u) [DivisionRing D]
    (P : (finiteProjectiveModules Dᵐᵒᵖ).FullSubcategory) :
    finrankEquivDivisionRing D (SplitK0.of.{u} P) = (Module.finrank Dᵐᵒᵖ P.obj : ℤ) :=
  finiteProjectiveModulesFinrankSplitK0EquivDivisionRing_of Dᵐᵒᵖ P

@[simp] theorem finrankEquivDivisionRing_one (D : Type u) [DivisionRing D] :
    finrankEquivDivisionRing D (one D) = 1 :=
  (finiteProjectiveModulesFinrankSplitK0EquivDivisionRing_of Dᵐᵒᵖ
    (FiniteProjectiveModules.selfObj Dᵐᵒᵖ)).trans (by simp)

@[simp] theorem finrankEquivDivisionRing_symm_apply (D : Type u) [DivisionRing D] (n : ℤ) :
    (finrankEquivDivisionRing D).symm n = n • one D :=
  finiteProjectiveModulesFinrankSplitK0EquivDivisionRing_symm_apply Dᵐᵒᵖ n

section PID

variable (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]

/-- **Rank isomorphism `AlgebraicK0 R ≃+ ℤ` over a principal ideal domain `R`**, normalized so that
`[R] ↦ 1`. -/
noncomputable def finrankEquivPID : AlgebraicK0 R ≃+ ℤ :=
  (commRingLeftSplitK0Equiv R).trans (finiteProjectiveModulesFinrankSplitK0EquivPID R)

@[simp] theorem finrankEquivPID_one : finrankEquivPID R (one R) = 1 := by
  rw [finrankEquivPID, AddEquiv.trans_apply, commRingLeftSplitK0Equiv_one,
    finiteProjectiveModulesFinrankSplitK0EquivPID_of]; simp

@[simp] theorem finrankEquivPID_symm_apply (n : ℤ) : (finrankEquivPID R).symm n = n • one R := by
  apply (finrankEquivPID R).injective; simp

end PID

/-- **Rank isomorphism `AlgebraicK0 ℤ ≃+ ℤ`**, sending `[ℤ]` to `1`. -/
noncomputable def finrankEquivInt : AlgebraicK0 ℤ ≃+ ℤ := finrankEquivPID ℤ

@[simp] theorem finrankEquivInt_one : finrankEquivInt (one ℤ) = 1 := finrankEquivPID_one ℤ

@[simp] theorem finrankEquivInt_symm_apply (n : ℤ) : finrankEquivInt.symm n = n • one ℤ :=
  finrankEquivPID_symm_apply ℤ n

section LocalRing

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-- **Rank isomorphism `AlgebraicK0 R ≃+ ℤ` over a commutative local ring `R`**, normalized so that
`[R] ↦ 1`. -/
noncomputable def finrankEquivLocalRing : AlgebraicK0 R ≃+ ℤ :=
  (commRingLeftSplitK0Equiv R).trans (finiteProjectiveModulesFinrankSplitK0EquivLocalRing R)

@[simp] theorem finrankEquivLocalRing_one : finrankEquivLocalRing R (one R) = 1 := by
  rw [finrankEquivLocalRing, AddEquiv.trans_apply, commRingLeftSplitK0Equiv_one,
    finiteProjectiveModulesFinrankSplitK0EquivLocalRing_of]; simp

@[simp] theorem finrankEquivLocalRing_symm_apply (n : ℤ) :
    (finrankEquivLocalRing R).symm n = n • one R := by
  apply (finrankEquivLocalRing R).injective; simp

end LocalRing

end TauCeti.AlgebraicK0
