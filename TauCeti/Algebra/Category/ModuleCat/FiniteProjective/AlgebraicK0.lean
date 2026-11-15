/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.SplitK0
public import TauCeti.RingTheory.PrincipalIdealDomain.MulOpposite

import Mathlib.Algebra.Field.Opposite
import TauCeti.Algebra.Ring.Opposite

/-!
# Algebraic `K₀` of a ring, functoriality, Morita invariance, and rank computations

For a possibly noncommutative ring `R`, this file defines algebraic `K₀` in the right-module
convention `AlgebraicK0 R := SplitK0 (finiteProjectiveModules Rᵐᵒᵖ).FullSubcategory`, matching
`TauCeti.AlgebraicK1` and Weibel, *The K-book*, Chapter II, §2, building on
`TauCeti.Algebra.Category.ModuleCat.FiniteProjective.SplitK0`.

## Main definitions

* `TauCeti.AlgebraicK0` and `TauCeti.AlgebraicK0.one`: algebraic `K₀` of a ring `R` and the
  canonical class `[R]` of the free right `R`-module of rank 1.
* `TauCeti.AlgebraicK0.map`, `RingEquiv.algebraicK0Equiv`, and
  `TauCeti.AlgebraicK0.commRingLeftSplitK0Equiv`: covariant functoriality along `R →+* S`, induced
  isomorphisms for `R ≃+* S`, and comparison with left-module `SplitK0` when `R` is commutative.
* `TauCeti.AlgebraicK0.prodEquiv` and `TauCeti.AlgebraicK0.matrixEquiv`: binary product
  decomposition and canonical universe-polymorphic, index-independent matrix Morita isomorphism.
* `TauCeti.AlgebraicK0.finrankEquivDivisionRing`, `TauCeti.AlgebraicK0.finrankEquivPID`,
  `TauCeti.AlgebraicK0.finrankEquivInt`, and `TauCeti.AlgebraicK0.finrankEquivLocalRing`: rank
  isomorphisms `AlgebraicK0 R ≃+ ℤ` normalized so that `[R] ↦ 1`.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II, §2,
  Lemma 2.1, Examples 2.1.1–2.1.2, Proposition 2.4, and §2.8.
-/

public section

open CategoryTheory MulOpposite

universe u v

namespace TauCeti

/-- **Algebraic `K₀` of a ring `R`**: the split Grothendieck group of finitely generated projective
right `R`-modules (encoded as left `Rᵐᵒᵖ`-modules). This matches the right-module convention of
`TauCeti.AlgebraicK1`, where `GL_n(R)` acts on finite free right `R`-modules. -/
abbrev AlgebraicK0 (R : Type u) [Ring R] : Type u :=
  SplitK0.{u} (finiteProjectiveModules Rᵐᵒᵖ).FullSubcategory

namespace AlgebraicK0

/-- The canonical class `[R]` of the free right `R`-module of rank one in `AlgebraicK0 R`. -/
noncomputable def one (R : Type u) [Ring R] : AlgebraicK0 R :=
  SplitK0.of.{u} (FiniteProjectiveModules.selfObj Rᵐᵒᵖ)

theorem one_def (R : Type u) [Ring R] :
    one R = SplitK0.of.{u} (FiniteProjectiveModules.selfObj Rᵐᵒᵖ) := (rfl)

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

@[simp] theorem map_one (f : R →+* S) : map f (one R) = one S := by
  simp [map, one]

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

end Basic

@[simp] theorem algebraicK0Equiv_refl (R : Type u) [Ring R] :
    (RingEquiv.refl R).algebraicK0Equiv = AddEquiv.refl (AlgebraicK0 R) := by ext x; simp

end RingEquiv

namespace TauCeti.AlgebraicK0

/-- For a commutative ring `R`, `RingEquiv.toOpposite R : R ≃+* Rᵐᵒᵖ` identifies `AlgebraicK0 R`
with the left-module `SplitK0` of `R` (and with `ExactK0 (finiteProjectiveModulesExactStructure R)`
after composing with `TauCeti.finiteProjectiveModulesSplitK0EquivExactK0`). -/
noncomputable def commRingLeftSplitK0Equiv (R : Type u) [CommRing R] :
    AlgebraicK0 R ≃+ SplitK0.{u} (finiteProjectiveModules R).FullSubcategory :=
  (RingEquiv.toOpposite R).symm.finiteProjectiveModulesSplitK0Equiv

theorem commRingLeftSplitK0Equiv_apply (R : Type u) [CommRing R] (x : AlgebraicK0 R) :
    commRingLeftSplitK0Equiv R x =
      (RingEquiv.toOpposite R).symm.finiteProjectiveModulesSplitK0Equiv x := (rfl)

theorem commRingLeftSplitK0Equiv_symm_apply (R : Type u) [CommRing R]
    (x : SplitK0.{u} (finiteProjectiveModules R).FullSubcategory) :
    (commRingLeftSplitK0Equiv R).symm x =
      (RingEquiv.toOpposite R).finiteProjectiveModulesSplitK0Equiv x := by
  rw [commRingLeftSplitK0Equiv, RingEquiv.finiteProjectiveModulesSplitK0Equiv_symm,
    RingEquiv.symm_symm]

@[simp] theorem commRingLeftSplitK0Equiv_of (R : Type u) [CommRing R]
    (P : (finiteProjectiveModules Rᵐᵒᵖ).FullSubcategory) :
    commRingLeftSplitK0Equiv R (SplitK0.of.{u} P) =
      SplitK0.of.{u}
        ((RingEquiv.toOpposite R).symm.toRingHom.finiteProjectiveModulesExtendScalars.obj P) := by
  simp [commRingLeftSplitK0Equiv_apply]

@[simp] theorem commRingLeftSplitK0Equiv_symm_of (R : Type u) [CommRing R]
    (P : (finiteProjectiveModules R).FullSubcategory) :
    (commRingLeftSplitK0Equiv R).symm (SplitK0.of.{u} P) =
      SplitK0.of.{u}
        ((RingEquiv.toOpposite R).toRingHom.finiteProjectiveModulesExtendScalars.obj P) := by
  simp [commRingLeftSplitK0Equiv_symm_apply]

@[simp] theorem commRingLeftSplitK0Equiv_one (R : Type u) [CommRing R] :
    commRingLeftSplitK0Equiv R (one R) = SplitK0.of.{u} (FiniteProjectiveModules.selfObj R) := by
  simp [commRingLeftSplitK0Equiv_apply, one]

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

private theorem map_restrictScalars_eq_zero {E A B : Type u} [Ring E] [Ring A] [Ring B]
    (p : E →+* A) (p' : E →+* B)
    (hfin : letI := p'.toModule; Module.Finite E B)
    (hproj : letI := p'.toModule; Module.Projective E B)
    (e : E) (hp : p e = 1) (hp' : p' e = 0)
    (x : SplitK0.{u} (finiteProjectiveModules B).FullSubcategory) :
    SplitK0.map.{u, u} p.finiteProjectiveModulesExtendScalars
      (SplitK0.map.{u, u} (p'.finiteProjectiveModulesRestrictScalars hfin hproj) x) = 0 :=
  DFunLike.congr_fun (SplitK0.hom_ext
    (f := (SplitK0.map.{u, u} p.finiteProjectiveModulesExtendScalars).comp
      (SplitK0.map.{u, u} (p'.finiteProjectiveModulesRestrictScalars hfin hproj)))
    (g := 0) fun N ↦ by
      simp only [AddMonoidHom.comp_apply, SplitK0.map_of, AddMonoidHom.zero_apply]
      let Z : ModuleCat.{u} A :=
        ModuleCat.of A (BalancedExtension p ((ModuleCat.restrictScalars.{u} p').obj N.obj))
      have : Subsingleton Z :=
        BalancedExtension.subsingleton_restrictScalars_of_map_eq_one_of_map_eq_zero
          p p' e hp hp' N.obj
      have hZ : (p.finiteProjectiveModulesExtendScalars.obj
          ((p'.finiteProjectiveModulesRestrictScalars hfin hproj).obj N)).obj = Z := by
        rw [p.finiteProjectiveModulesExtendScalars_obj_obj,
          p'.finiteProjectiveModulesRestrictScalars_obj_obj]
      exact SplitK0.of_eq_zero_of_isZero <| Limits.IsZero.of_full_of_faithful_of_isZero
        (finiteProjectiveModules A).ι _ <| (ModuleCat.isZero_of_subsingleton Z).of_iso
          (eqToIso hZ)) x

private theorem map_restrictScalars_self {E A : Type u} [Ring E] [Ring A]
    (p : E →+* A) (hp : Function.Surjective p)
    (hfin : letI := p.toModule; Module.Finite E A)
    (hproj : letI := p.toModule; Module.Projective E A)
    (x : SplitK0.{u} (finiteProjectiveModules A).FullSubcategory) :
    SplitK0.map.{u, u} p.finiteProjectiveModulesExtendScalars
      (SplitK0.map.{u, u} (p.finiteProjectiveModulesRestrictScalars hfin hproj) x) = x :=
  DFunLike.congr_fun (SplitK0.hom_ext
    (f := (SplitK0.map.{u, u} p.finiteProjectiveModulesExtendScalars).comp
      (SplitK0.map.{u, u} (p.finiteProjectiveModulesRestrictScalars hfin hproj)))
    (g := AddMonoidHom.id _) fun M ↦ by
      simp only [AddMonoidHom.comp_apply, SplitK0.map_of, AddMonoidHom.id_apply]
      exact SplitK0.of_extendScalars_obj
        ((BalancedExtension.congr p
            (eqToIso
              (p.finiteProjectiveModulesRestrictScalars_obj_obj hfin hproj M)).toLinearEquiv).trans
          (BalancedExtension.restrictScalarsSelfEquiv p hp M.obj))) x

@[simp] theorem prodEquiv_symm_apply (R S : Type u) [Ring R] [Ring S]
    (x : AlgebraicK0 R × AlgebraicK0 S) :
    (prodEquiv R S).symm x =
      SplitK0.map.{u, u} ((RingHom.op (RingHom.fst R S)).finiteProjectiveModulesRestrictScalars
          (RingHom.finite_toModule_of_surjective _ fun a ↦ ⟨op (a.unop, 0), rfl⟩)
          (RingHom.projective_toModule_of_split _
            ((opAddEquiv.toAddMonoidHom.comp (AddMonoidHom.inl R S)).comp
              opAddEquiv.symm.toAddMonoidHom)
            (fun _ ↦ rfl)
            (fun _ _ ↦ MulOpposite.unop_injective (Prod.ext rfl (zero_mul _))))) x.1 +
        SplitK0.map.{u, u} ((RingHom.op (RingHom.snd R S)).finiteProjectiveModulesRestrictScalars
          (RingHom.finite_toModule_of_surjective _ fun b ↦ ⟨op (0, b.unop), rfl⟩)
          (RingHom.projective_toModule_of_split _
            ((opAddEquiv.toAddMonoidHom.comp (AddMonoidHom.inr R S)).comp
              opAddEquiv.symm.toAddMonoidHom)
            (fun _ ↦ rfl)
            (fun _ _ ↦ MulOpposite.unop_injective (Prod.ext (zero_mul _) rfl)))) x.2 := by
  apply (prodEquiv R S).injective
  rw [AddEquiv.apply_symm_apply, prodEquiv_apply, map_add, map_add]
  refine Prod.ext ?_ ?_
  · rw [map, map,
      map_restrictScalars_self (RingHom.op (RingHom.fst R S)) fun a ↦ ⟨op (a.unop, 0), rfl⟩,
      map_restrictScalars_eq_zero (RingHom.op (RingHom.fst R S)) (RingHom.op (RingHom.snd R S))
        _ _ (op (1, 0)) rfl rfl, add_zero]
  · rw [map, map,
      map_restrictScalars_eq_zero (RingHom.op (RingHom.snd R S)) (RingHom.op (RingHom.fst R S))
        _ _ (op (0, 1)) rfl rfl,
      map_restrictScalars_self (RingHom.op (RingHom.snd R S)) fun b ↦ ⟨op (0, b.unop), rfl⟩,
      zero_add]

section Index

variable (R : Type u) [Ring R] (ι : Type v) [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- **Matrix Morita invariance of algebraic `K₀`.** For a nonempty finite index type `ι`,
`AlgebraicK0.{u} R ≃+ AlgebraicK0.{max u v} (Matrix ι ι R)` canonically (with no dependence on a
chosen index in `ι`), sending `|ι| • [R]` to `[Matrix ι ι R]`. -/
noncomputable def matrixEquiv : AlgebraicK0.{u} R ≃+ AlgebraicK0.{max u v} (Matrix ι ι R) :=
  (finiteProjectiveModulesMatrixSplitK0Equiv Rᵐᵒᵖ ι).trans
    (RingEquiv.mopMatrix (m := ι) (α := R)).finiteProjectiveModulesSplitK0Equiv

theorem matrixEquiv_apply (x : AlgebraicK0.{u} R) :
    matrixEquiv R ι x =
      (RingEquiv.mopMatrix (m := ι) (α := R)).finiteProjectiveModulesSplitK0Equiv
        (finiteProjectiveModulesMatrixSplitK0Equiv Rᵐᵒᵖ ι x) := (rfl)

@[simp] theorem matrixEquiv_of (P : (finiteProjectiveModules Rᵐᵒᵖ).FullSubcategory) :
    matrixEquiv R ι (SplitK0.of.{u} P) = SplitK0.of.{max u v}
      ((RingEquiv.mopMatrix (m := ι) (α := R)).toRingHom.finiteProjectiveModulesExtendScalars.obj
        ((finiteProjectiveModulesToMatrixFunctor Rᵐᵒᵖ ι).obj P)) := by simp [matrixEquiv_apply]

@[simp] theorem matrixEquiv_card_nsmul_one :
    matrixEquiv R ι (Fintype.card ι • one R) = one (Matrix ι ι R) := by
  simp [matrixEquiv_apply, one]

end Index

section SameUniverse

variable (R : Type u) [Ring R] (ι : Type u) [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- For every `i : ι`, `TauCeti.AlgebraicK0.matrixEquiv` agrees with the Morita equivalence
`ModuleCat.matrixEquivalence Rᵐᵒᵖ i` composed with `RingEquiv.mopMatrix`. -/
theorem matrixEquiv_eq (i : ι) :
    matrixEquiv R ι =
      (ModuleCat.matrixEquivalence Rᵐᵒᵖ (ι := ι) i).finiteProjectiveModulesSplitK0Equiv.trans
        (RingEquiv.mopMatrix (m := ι) (α := R)).finiteProjectiveModulesSplitK0Equiv := by
  rw [matrixEquiv, finiteProjectiveModulesMatrixSplitK0Equiv_eq Rᵐᵒᵖ ι i]

end SameUniverse

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

variable (R : Type u) [Ring R] [Nontrivial R] [NoZeroDivisors R] [IsPrincipalIdealRing Rᵐᵒᵖ]

/-- **Rank isomorphism `AlgebraicK0 R ≃+ ℤ` over a principal right-ideal domain `R`** (including any
commutative principal ideal domain), normalized so that `[R] ↦ 1`. -/
noncomputable def finrankEquivPID : AlgebraicK0 R ≃+ ℤ :=
  finiteProjectiveModulesFinrankSplitK0EquivPID Rᵐᵒᵖ

@[simp] theorem finrankEquivPID_of (P : (finiteProjectiveModules Rᵐᵒᵖ).FullSubcategory) :
    finrankEquivPID R (SplitK0.of.{u} P) = (Module.finrank Rᵐᵒᵖ P.obj : ℤ) :=
  finiteProjectiveModulesFinrankSplitK0EquivPID_of Rᵐᵒᵖ P

@[simp] theorem finrankEquivPID_one : finrankEquivPID R (one R) = 1 :=
  (finiteProjectiveModulesFinrankSplitK0EquivPID_of Rᵐᵒᵖ
    (FiniteProjectiveModules.selfObj Rᵐᵒᵖ)).trans (by simp)

@[simp] theorem finrankEquivPID_symm_apply (n : ℤ) : (finrankEquivPID R).symm n = n • one R :=
  finiteProjectiveModulesFinrankSplitK0EquivPID_symm_apply Rᵐᵒᵖ n

end PID

/-- **Rank isomorphism `AlgebraicK0 ℤ ≃+ ℤ`**, sending `[ℤ]` to `1`. -/
noncomputable def finrankEquivInt : AlgebraicK0 ℤ ≃+ ℤ := finrankEquivPID ℤ

@[simp] theorem finrankEquivInt_of (P : (finiteProjectiveModules ℤᵐᵒᵖ).FullSubcategory) :
    finrankEquivInt (SplitK0.of.{0} P) = (Module.finrank ℤᵐᵒᵖ P.obj : ℤ) :=
  finrankEquivPID_of ℤ P

@[simp] theorem finrankEquivInt_one : finrankEquivInt (one ℤ) = 1 := finrankEquivPID_one ℤ

@[simp] theorem finrankEquivInt_symm_apply (n : ℤ) : finrankEquivInt.symm n = n • one ℤ :=
  finrankEquivPID_symm_apply ℤ n

section LocalRing

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-- **Rank isomorphism `AlgebraicK0 R ≃+ ℤ` over a commutative local ring `R`**, normalized so that
`[R] ↦ 1`. -/
noncomputable def finrankEquivLocalRing : AlgebraicK0 R ≃+ ℤ :=
  finiteProjectiveModulesFinrankSplitK0EquivLocalRing Rᵐᵒᵖ

@[simp] theorem finrankEquivLocalRing_of (P : (finiteProjectiveModules Rᵐᵒᵖ).FullSubcategory) :
    finrankEquivLocalRing R (SplitK0.of.{u} P) = (Module.finrank Rᵐᵒᵖ P.obj : ℤ) :=
  finiteProjectiveModulesFinrankSplitK0EquivLocalRing_of Rᵐᵒᵖ P

@[simp] theorem finrankEquivLocalRing_one : finrankEquivLocalRing R (one R) = 1 :=
  (finiteProjectiveModulesFinrankSplitK0EquivLocalRing_of Rᵐᵒᵖ
    (FiniteProjectiveModules.selfObj Rᵐᵒᵖ)).trans (by simp)

@[simp] theorem finrankEquivLocalRing_symm_apply (n : ℤ) :
    (finrankEquivLocalRing R).symm n = n • one R :=
  finiteProjectiveModulesFinrankSplitK0EquivLocalRing_symm_apply Rᵐᵒᵖ n

end LocalRing

end TauCeti.AlgebraicK0
