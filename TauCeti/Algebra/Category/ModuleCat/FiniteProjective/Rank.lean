/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.Topology.LocallyConstant.Algebra
public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.Monoidal
public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.ScalarChange
public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.StableEquivalent
public import TauCeti.CategoryTheory.GrothendieckGroup.Monoidal.Basic
public import TauCeti.RingTheory.Idempotents.Clopen
public import TauCeti.Topology.LocallyConstant.Connected

import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Flat.TorsionFree

/-!
# The locally constant rank homomorphism on `K₀`, reduced `K₀`, and semilocal / PID classification

For a commutative ring `R`, the split Grothendieck group
`SplitK0.{u} (finiteProjectiveModules R).FullSubcategory` is a commutative ring under the tensor
product (`TauCeti.SplitK0.instCommRing`). Every finitely generated projective `R`-module `P` is
finitely presented and flat, so its stalk rank `p ↦ Module.rankAtStalk P p` is locally constant on
`Spec R`, additive on direct sums, sends `R` to `1`, and is multiplicative on tensor products.
By the universal property `TauCeti.SplitK0.liftRingHom`, stalk rank therefore descends to a
natural ring homomorphism

```text
rankHom R : K₀(proj R) →+* LocallyConstant (PrimeSpectrum R) ℤ.
```

Using the correspondence between clopen subsets `U ⊆ Spec R` and idempotents `e_U ∈ R`, each
clopen `U` defines a finitely generated projective module `R e_U` whose class `clopenClass R U`
has rank equal to the characteristic function `LocallyConstant.charFn ℤ U.isClopen`. Extending
additively over the finite clopen fibers of any `g : LocallyConstant (PrimeSpectrum R) ℤ` yields
a natural ring-homomorphism section `rankSection R` with `(rankHom R).comp (rankSection R) = id`.
Thus `K₀(proj R)` splits additively as `LocallyConstant (PrimeSpectrum R) ℤ × reducedK0 R`, where
`reducedK0 R := RingHom.ker (rankHom R)` is the reduced `K₀` ideal.

Moreover, scalar extension along any ring homomorphism `f : R →+* S` between commutative rings
upgrades `SplitK0.map f.finiteProjectiveModulesExtendScalars` to a ring homomorphism
`f.finiteProjectiveModulesSplitK0Extend`, natural with respect to both `rankHom` and
`rankSection`.

## Main definitions

* `RingHom.finiteProjectiveModulesSplitK0Extend`: the ring homomorphism
  `K₀(proj R) →+* K₀(proj S)` induced by scalar extension along `f : R →+* S`.
* `TauCeti.FiniteProjectiveModules.rankHom`: the locally constant rank ring homomorphism
  `K₀(proj R) →+* LocallyConstant (PrimeSpectrum R) ℤ`.
* `TauCeti.FiniteProjectiveModules.clopenObj`, `clopenClass`, and `clopenRankObj`: the
  finitely generated projective modules and `K₀` classes attached to clopen subsets of `Spec R`
  and locally constant `ℕ`-valued rank functions.
* `TauCeti.FiniteProjectiveModules.rankSection`: the natural ring-homomorphism section
  `LocallyConstant (PrimeSpectrum R) ℤ →+* K₀(proj R)` of `rankHom R`.
* `TauCeti.FiniteProjectiveModules.reducedK0`: the ideal `RingHom.ker (rankHom R)` of rank-zero
  classes, together with the splitting `splitK0EquivProdReducedK0`.
* `TauCeti.FiniteProjectiveModules.rankEquivOfFiniteMaximalSpectrum`: for a commutative semilocal
  ring (`Finite (MaximalSpectrum R)`), the ring isomorphism
  `K₀(proj R) ≃+* LocallyConstant (PrimeSpectrum R) ℤ`.
* `TauCeti.FiniteProjectiveModules.rankEquivIntOfForallFree`,
  `rankEquivIntOfFiniteMaximalSpectrum`, and `rankEquivIntOfIsPrincipalIdealRing`: the ring
  isomorphism `K₀(proj R) ≃+* ℤ` whenever every finite projective `R`-module is free (over a
  nontrivial commutative ring) — in particular for connected semilocal rings (including all
  commutative local rings) and principal ideal domains.

## Main results

* `TauCeti.FiniteProjectiveModules.rankHom_comp_extend` and `extend_comp_rankSection`: naturality
  of `rankHom` and `rankSection` under ring homomorphisms.
* `TauCeti.FiniteProjectiveModules.rankHom_comp_rankSection`: `rankSection R` is a right inverse
  to `rankHom R`, so `rankHom R` is surjective and `rankSection R` is injective.
* `TauCeti.FiniteProjectiveModules.mem_reducedK0_iff_forall_localization`: a class in `K₀(proj R)`
  lies in `reducedK0 R` if and only if its image vanishes in `K₀(proj R_p)` for every prime `p`.
* `TauCeti.FiniteProjectiveModules.reducedK0_eq_bot_of_finite_maximalSpectrum` and
  `reducedK0_eq_bot_of_forall_free`: vanishing of reduced `K₀` for semilocal rings and rings whose
  finitely generated projective modules are free.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II, §2,
  Lemmas 2.2–2.3 and Corollary 2.6.2, pp. 71–75.
* J. Rosenberg, *Algebraic K-Theory and Its Applications*, §§1.1–1.3.
-/

public section

open CategoryTheory MonoidalCategory TopologicalSpace
open scoped TensorProduct

universe u

/-! ### Scalar extension as a ring homomorphism on split `K₀` -/

namespace RingHom

open TauCeti

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]

/-- Scalar extension preserves multiplication on split `K₀` of finitely generated projective
modules over commutative rings. -/
private theorem map_extendScalars_mul (f : R →+* S) :
    ∀ x y : SplitK0.{u} (finiteProjectiveModules R).FullSubcategory,
      SplitK0.map.{u, u} f.finiteProjectiveModulesExtendScalars (x * y) =
        SplitK0.map.{u, u} f.finiteProjectiveModulesExtendScalars x *
          SplitK0.map.{u, u} f.finiteProjectiveModulesExtendScalars y := by
  rw [AddMonoidHom.map_mul_iff]
  refine SplitK0.hom_ext fun P ↦ SplitK0.hom_ext fun Q ↦ ?_
  let : Algebra R S := f.toAlgebra
  simp only [AddMonoidHom.compr₂_apply, AddMonoidHom.mul_apply, AddMonoidHom.compl₂_apply,
    AddMonoidHom.comp_apply, SplitK0.of_mul_of, SplitK0.map_of]
  have eP := BalancedExtension.equivTensorProduct R S P.obj
  have eQ := BalancedExtension.equivTensorProduct R S Q.obj
  have ePQ := BalancedExtension.equivTensorProduct R S (P.obj ⊗[R] Q.obj)
  let eP' : BalancedExtension f P.obj ≃ₗ[S] (f.finiteProjectiveModulesExtendScalars.obj P).obj :=
    (eqToIso (f.finiteProjectiveModulesExtendScalars_obj_obj P)).symm.toLinearEquiv
  let eQ' : BalancedExtension f Q.obj ≃ₗ[S] (f.finiteProjectiveModulesExtendScalars.obj Q).obj :=
    (eqToIso (f.finiteProjectiveModulesExtendScalars_obj_obj Q)).symm.toLinearEquiv
  let θ : BalancedExtension f (P ⊗ Q).obj ≃ₗ[S]
      (f.finiteProjectiveModulesExtendScalars.obj P ⊗
        f.finiteProjectiveModulesExtendScalars.obj Q).obj :=
    (BalancedExtension.congr f (LinearEquiv.refl R _ : (P ⊗ Q).obj ≃ₗ[R] P.obj ⊗[R] Q.obj)).trans
      (ePQ.trans ((TensorProduct.AlgebraTensorModule.distribBaseChange R S P.obj Q.obj).trans
        ((TensorProduct.congr (eP.symm.trans eP') (eQ.symm.trans eQ')).trans
          (LinearEquiv.refl S _))))
  exact SplitK0.of_extendScalars_obj (P := P ⊗ Q)
    (Q := f.finiteProjectiveModulesExtendScalars.obj P ⊗
      f.finiteProjectiveModulesExtendScalars.obj Q) θ

/-- **Extension of scalars as a ring homomorphism on split `K₀`.** For commutative rings, a ring
homomorphism `f : R →+* S` induces a ring homomorphism
`K₀(proj R) →+* K₀(proj S)` extending `SplitK0.map f.finiteProjectiveModulesExtendScalars`. -/
noncomputable def finiteProjectiveModulesSplitK0Extend (f : R →+* S) :
    SplitK0.{u} (finiteProjectiveModules R).FullSubcategory →+*
      SplitK0.{u} (finiteProjectiveModules S).FullSubcategory where
  __ := SplitK0.map.{u, u} f.finiteProjectiveModulesExtendScalars
  map_one' := by
    let : Algebra R S := f.toAlgebra
    rw [SplitK0.one_def, SplitK0.one_def, AddMonoidHom.toFun_eq_coe, SplitK0.map_of]
    exact SplitK0.of_extendScalars_obj (Q := 𝟙_ (finiteProjectiveModules S).FullSubcategory)
      ((BalancedExtension.equivTensorProduct R S R).trans
        (TensorProduct.AlgebraTensorModule.rid R S S))
  map_mul' := map_extendScalars_mul f

@[simp]
theorem finiteProjectiveModulesSplitK0Extend_toAddMonoidHom (f : R →+* S) :
    (f.finiteProjectiveModulesSplitK0Extend : _ →+ _) =
      SplitK0.map.{u, u} f.finiteProjectiveModulesExtendScalars := (rfl)

@[simp]
theorem finiteProjectiveModulesSplitK0Extend_of (f : R →+* S)
    (P : (finiteProjectiveModules R).FullSubcategory) :
    f.finiteProjectiveModulesSplitK0Extend (SplitK0.of.{u} P) =
      SplitK0.of.{u} (f.finiteProjectiveModulesExtendScalars.obj P) :=
  SplitK0.map_of.{u, u} f.finiteProjectiveModulesExtendScalars P

@[simp]
theorem finiteProjectiveModulesSplitK0Extend_id :
    (RingHom.id R).finiteProjectiveModulesSplitK0Extend = RingHom.id _ := by
  refine SplitK0.ringHom_ext fun P ↦ ?_
  rw [finiteProjectiveModulesSplitK0Extend_of, RingHom.id_apply]
  exact SplitK0.of_extendScalars_obj (BalancedExtension.lid R P.obj)

theorem finiteProjectiveModulesSplitK0Extend_comp (g : S →+* T) (f : R →+* S) :
    (g.comp f).finiteProjectiveModulesSplitK0Extend =
      g.finiteProjectiveModulesSplitK0Extend.comp f.finiteProjectiveModulesSplitK0Extend := by
  refine SplitK0.ringHom_ext fun P ↦ ?_
  rw [RingHom.comp_apply, finiteProjectiveModulesSplitK0Extend_of,
    finiteProjectiveModulesSplitK0Extend_of, finiteProjectiveModulesSplitK0Extend_of]
  let θ : BalancedExtension g (f.finiteProjectiveModulesExtendScalars.obj P).obj ≃ₗ[T]
      ((g.comp f).finiteProjectiveModulesExtendScalars.obj P).obj :=
    (BalancedExtension.congr g
        (eqToIso (f.finiteProjectiveModulesExtendScalars_obj_obj P)).toLinearEquiv).trans
      ((BalancedExtension.cancelBaseChange f g).trans
        (eqToIso ((g.comp f).finiteProjectiveModulesExtendScalars_obj_obj P)).symm.toLinearEquiv)
  exact (SplitK0.of_extendScalars_obj (P := f.finiteProjectiveModulesExtendScalars.obj P)
    (Q := (g.comp f).finiteProjectiveModulesExtendScalars.obj P) θ).symm

end RingHom

/-! ### The locally constant rank homomorphism -/

namespace TauCeti.FiniteProjectiveModules

section RankHom

variable (R : Type u) [CommRing R]

/-- Stalk rank as a biproduct-additive invariant taking values in
`LocallyConstant (PrimeSpectrum R) ℤ`. -/
private noncomputable def rankInvariant :
    SplitK0.AdditiveInvariant (finiteProjectiveModules R).FullSubcategory
      (LocallyConstant (PrimeSpectrum R) ℤ) where
  obj P :=
    ⟨fun p ↦ (Module.rankAtStalk (R := R) P.obj p : ℤ),
      have := Module.finitePresentation_of_projective R P.obj
      have := Module.Flat.of_projective (R := R) (M := P.obj)
      Module.isLocallyConstant_rankAtStalk.comp (Nat.cast : ℕ → ℤ)⟩
  map_iso {P Q} e := by
    ext p
    exact congrArg (Nat.cast : ℕ → ℤ) (congrFun (Module.rankAtStalk_eq_of_equiv
      ((finiteProjectiveModules R).ι.mapIso e).toLinearEquiv) p)
  map_biprod P Q := by
    ext p
    have := Module.Flat.of_projective (R := R) (M := P.obj)
    have := Module.Flat.of_projective (R := R) (M := Q.obj)
    have h1 := congrFun (Module.rankAtStalk_eq_of_equiv (biprodLinearEquiv P Q)) p
    have h2 := congrFun (Module.rankAtStalk_prod (R := R) P.obj Q.obj) p
    simp only [LocallyConstant.coe_add, Pi.add_apply, LocallyConstant.coe_mk]
    rw [h1, h2, Pi.add_apply, Nat.cast_add]

/-- **The locally constant rank homomorphism.** Stalk rank on finitely generated projective
`R`-modules descends to a ring homomorphism
`K₀(proj R) →+* LocallyConstant (PrimeSpectrum R) ℤ`. -/
noncomputable def rankHom :
    SplitK0.{u} (finiteProjectiveModules R).FullSubcategory →+*
      LocallyConstant (PrimeSpectrum R) ℤ :=
  SplitK0.liftRingHom (rankInvariant R)
    (by
      ext p
      have : Nontrivial R := PrimeSpectrum.nonempty_iff_nontrivial.1 ⟨p⟩
      have h : Module.rankAtStalk (R := R) (𝟙_ (finiteProjectiveModules R).FullSubcategory).obj p =
          1 := congrFun (Module.rankAtStalk_self (R := R)) p
      simp only [rankInvariant, LocallyConstant.coe_one, Pi.one_apply, LocallyConstant.coe_mk]
      rw [h, Nat.cast_one])
    (fun P Q ↦ by
      ext p
      have := Module.Flat.of_projective (R := R) (M := P.obj)
      have := Module.Flat.of_projective (R := R) (M := Q.obj)
      have h1 : Module.rankAtStalk (R := R) (P ⊗ Q).obj p =
          Module.rankAtStalk (R := R) (P.obj ⊗[R] Q.obj) p :=
        congrFun (Module.rankAtStalk_eq_of_equiv
          (LinearEquiv.refl R _ : (P ⊗ Q).obj ≃ₗ[R] P.obj ⊗[R] Q.obj)) p
      have h2 := congrFun (Module.rankAtStalk_tensorProduct (R := R) (M := P.obj) Q.obj) p
      simp only [rankInvariant, LocallyConstant.coe_mul, Pi.mul_apply, LocallyConstant.coe_mk]
      rw [h1, h2, Pi.mul_apply, Nat.cast_mul])

@[simp]
theorem rankHom_of (P : (finiteProjectiveModules R).FullSubcategory) (p : PrimeSpectrum R) :
    rankHom R (SplitK0.of.{u} P) p = (Module.rankAtStalk (R := R) P.obj p : ℤ) := by
  rw [rankHom, SplitK0.liftRingHom_of]
  rfl

/-- **Naturality of rank under scalar extension.** For `f : R →+* S`, rank commutes with scalar
extension along `f` and pullback of locally constant functions along `Spec S → Spec R`. -/
theorem rankHom_comp_extend {S : Type u} [CommRing S] (f : R →+* S) :
    (rankHom S).comp f.finiteProjectiveModulesSplitK0Extend =
      (LocallyConstant.comapRingHom ⟨PrimeSpectrum.comap f, PrimeSpectrum.continuous_comap f⟩).comp
        (rankHom R) := by
  refine SplitK0.ringHom_ext fun P ↦ ?_
  ext q
  let : Algebra R S := f.toAlgebra
  have := Module.Flat.of_projective (R := R) (M := P.obj)
  rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.finiteProjectiveModulesSplitK0Extend_of,
    rankHom_of]
  have h0 := congrFun (Module.rankAtStalk_eq_of_equiv
    (eqToIso (f.finiteProjectiveModulesExtendScalars_obj_obj P)).toLinearEquiv) q
  have h1 := congrFun (Module.rankAtStalk_eq_of_equiv
    (BalancedExtension.equivTensorProduct R S P.obj)) q
  have h2 := Module.rankAtStalk_baseChange (R := R) (S := S) (M := P.obj) q
  exact (congrArg (Nat.cast : ℕ → ℤ) (h0.trans (h1.trans h2))).trans
    (rankHom_of R P (q.comap f)).symm

@[simp]
theorem rankHom_extend_apply {S : Type u} [CommRing S] (f : R →+* S)
    (x : SplitK0.{u} (finiteProjectiveModules R).FullSubcategory) (q : PrimeSpectrum S) :
    rankHom S (f.finiteProjectiveModulesSplitK0Extend x) q = rankHom R x (q.comap f) := by
  have h := DFunLike.congr_fun (rankHom_comp_extend R f) x
  exact DFunLike.congr_fun h q

end RankHom

/-! ### Clopen idempotent classes and the rank section -/

section RankSection

variable (R : Type u) [CommRing R]

/-- The finitely generated projective `R`-module `R e_U` attached to a clopen subset
`U ⊆ Spec R`. -/
noncomputable def clopenObj (U : Clopens (PrimeSpectrum R)) :
    (finiteProjectiveModules R).FullSubcategory :=
  ⟨ModuleCat.of R
      (Ideal.span {(PrimeSpectrum.isIdempotentElemEquivClopens.symm U).1} : Ideal R),
    finiteProjectiveModules_iff.2
      ⟨Module.Finite.iff_fg.2 (Submodule.fg_span_singleton _),
       (PrimeSpectrum.isIdempotentElemEquivClopens.symm U).2.projective_span_singleton⟩⟩

/-- The class `[R e_U]` in `K₀(proj R)` attached to a clopen subset `U ⊆ Spec R`. -/
noncomputable def clopenClass (U : Clopens (PrimeSpectrum R)) :
    SplitK0.{u} (finiteProjectiveModules R).FullSubcategory :=
  SplitK0.of.{u} (clopenObj R U)

/-- `ClopenRankModule R f` as an object of `(finiteProjectiveModules R).FullSubcategory`. -/
noncomputable def clopenRankObj (f : LocallyConstant (PrimeSpectrum R) ℕ) :
    (finiteProjectiveModules R).FullSubcategory :=
  ⟨ModuleCat.of R (ClopenRankModule R f),
    finiteProjectiveModules_iff.2 ⟨inferInstance, inferInstance⟩⟩

@[simp]
theorem clopenClass_bot : clopenClass R ⊥ = 0 := by
  have : Subsingleton ((finiteProjectiveModules R).ι.obj (clopenObj R ⊥)) := by
    dsimp only [clopenObj, ObjectProperty.ι_obj]
    rw [PrimeSpectrum.isIdempotentElemEquivClopens_symm_bot, Ideal.span_singleton_zero]
    infer_instance
  exact SplitK0.of_eq_zero_of_isZero (Limits.IsZero.of_full_of_faithful_of_isZero
    (finiteProjectiveModules R).ι (clopenObj R ⊥) (ModuleCat.isZero_of_subsingleton _))

@[simp]
theorem clopenClass_top : clopenClass R ⊤ = 1 := by
  rw [clopenClass, SplitK0.one_def]
  let θ : (Ideal.span {(PrimeSpectrum.isIdempotentElemEquivClopens.symm
      (⊤ : Clopens (PrimeSpectrum R))).1} : Ideal R) ≃ₗ[R] R :=
    (LinearEquiv.ofEq _ _ (by
      rw [PrimeSpectrum.isIdempotentElemEquivClopens_symm_top, Ideal.span_singleton_one]))
      |>.trans Submodule.topEquiv
  exact SplitK0.of_congr (ObjectProperty.isoMk _ θ.toModuleIso)

theorem clopenClass_inf (U V : Clopens (PrimeSpectrum R)) :
    clopenClass R (U ⊓ V) = clopenClass R U * clopenClass R V := by
  rw [clopenClass, clopenClass, clopenClass, SplitK0.of_mul_of]
  let θ : (Ideal.span {(PrimeSpectrum.isIdempotentElemEquivClopens.symm (U ⊓ V)).1} : Ideal R)
      ≃ₗ[R]
      (Ideal.span {(PrimeSpectrum.isIdempotentElemEquivClopens.symm U).1} : Ideal R) ⊗[R]
        (Ideal.span {(PrimeSpectrum.isIdempotentElemEquivClopens.symm V).1} : Ideal R) :=
    (LinearEquiv.ofEq _ _ (by
      rw [congrArg Subtype.val (PrimeSpectrum.isIdempotentElemEquivClopens_symm_inf U V)])).trans
      ((PrimeSpectrum.isIdempotentElemEquivClopens.symm U).2.spanSingletonTensorEquiv
        (PrimeSpectrum.isIdempotentElemEquivClopens.symm V).2).symm
  exact SplitK0.of_congr (ObjectProperty.isoMk _ θ.toModuleIso)

theorem clopenClass_sup_of_disjoint {U V : Clopens (PrimeSpectrum R)} (h : Disjoint U V) :
    clopenClass R (U ⊔ V) = clopenClass R U + clopenClass R V := by
  let θ : (Ideal.span {(PrimeSpectrum.isIdempotentElemEquivClopens.symm (U ⊔ V)).1} : Ideal R)
      ≃ₗ[R]
      (Ideal.span {(PrimeSpectrum.isIdempotentElemEquivClopens.symm U).1} : Ideal R) ×
        (Ideal.span {(PrimeSpectrum.isIdempotentElemEquivClopens.symm V).1} : Ideal R) :=
    (LinearEquiv.ofEq _ _ (by
      rw [PrimeSpectrum.isIdempotentElemEquivClopens_symm_sup_of_disjoint h])).trans
      ((PrimeSpectrum.isIdempotentElemEquivClopens.symm U).2.spanSingletonAddEquivProd
        (PrimeSpectrum.isIdempotentElemEquivClopens.symm V).2
        (PrimeSpectrum.isIdempotentElemEquivClopens_symm_mul_eq_zero_of_disjoint h)
        (PrimeSpectrum.isIdempotentElemEquivClopens_symm_mul_eq_zero_of_disjoint h.symm))
  exact SplitK0.of_eq_add_of_linearEquiv_prod (X := clopenObj R (U ⊔ V))
    (P := clopenObj R U) (Q := clopenObj R V) θ

theorem clopenClass_finset_sup {ι : Type*} (s : Finset ι)
    (U : ι → Clopens (PrimeSpectrum R)) (hdisj : (s : Set ι).PairwiseDisjoint U) :
    clopenClass R (s.sup U) = ∑ i ∈ s, clopenClass R (U i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hda : Disjoint (U a) (s.sup U) :=
      Finset.disjoint_sup_right.2 fun b hb ↦
        hdisj (Finset.mem_insert_self a s) (Finset.mem_insert_of_mem hb)
          (fun h ↦ ha (h ▸ hb))
    rw [Finset.sup_insert, clopenClass_sup_of_disjoint R hda, Finset.sum_insert ha,
      ih (hdisj.subset (Finset.subset_insert a s))]

theorem clopenClass_add_compl (U : Clopens (PrimeSpectrum R)) :
    clopenClass R U + clopenClass R Uᶜ = 1 := by
  rw [← clopenClass_sup_of_disjoint R disjoint_compl_right, sup_compl_eq_top, clopenClass_top]

@[simp]
theorem rankHom_clopenClass (U : Clopens (PrimeSpectrum R)) :
    rankHom R (clopenClass R U) = LocallyConstant.charFn ℤ U.isClopen := by
  ext p
  rw [clopenClass, rankHom_of]
  have h1 : Module.rankAtStalk (R := R) (clopenObj R U).obj p =
      Module.rankAtStalk (R := R)
        (Ideal.span {(PrimeSpectrum.isIdempotentElemEquivClopens.symm U).1} : Ideal R) p :=
    congrFun (Module.rankAtStalk_eq_of_equiv (LinearEquiv.refl R _)) p
  have h2 := (PrimeSpectrum.isIdempotentElemEquivClopens.symm U).2.rankAtStalk_span_singleton p
  rw [h1, h2, PrimeSpectrum.mem_asIdeal_isIdempotentElemEquivClopens_symm_iff]
  by_cases hp : p ∈ U <;> simp [LocallyConstant.coe_charFn, hp]

theorem extend_clopenClass {S : Type u} [CommRing S] (f : R →+* S)
    (U : Clopens (PrimeSpectrum R)) :
    f.finiteProjectiveModulesSplitK0Extend (clopenClass R U) =
      clopenClass S ⟨PrimeSpectrum.comap f ⁻¹' U,
        U.isClopen.preimage (PrimeSpectrum.continuous_comap f)⟩ := by
  rw [clopenClass, RingHom.finiteProjectiveModulesSplitK0Extend_of, clopenClass]
  let θ : BalancedExtension f (clopenObj R U).obj ≃ₗ[S]
      (clopenObj S ⟨PrimeSpectrum.comap f ⁻¹' U,
        U.isClopen.preimage (PrimeSpectrum.continuous_comap f)⟩).obj :=
    ((PrimeSpectrum.isIdempotentElemEquivClopens.symm U).2.balancedExtensionSpanSingletonEquiv f)
      |>.trans (LinearEquiv.ofEq _ _ (by rw [PrimeSpectrum.map_isIdempotentElemEquivClopens_symm]))
  exact SplitK0.of_extendScalars_obj θ

/-- Refining a clopen class along any finite clopen partition of `Spec R`. -/
private theorem clopenClass_eq_sum_inf {κ : Type*} (t : Finset κ)
    (U : Clopens (PrimeSpectrum R)) (V : κ → Clopens (PrimeSpectrum R))
    (hVd : (t : Set κ).PairwiseDisjoint V) (hVc : t.sup V = ⊤) :
    clopenClass R U = ∑ j ∈ t, clopenClass R (U ⊓ V j) := by
  have heq : U = t.sup fun j ↦ U ⊓ V j := by
    apply Clopens.ext
    ext p
    have htop : p ∈ (t.sup V : Clopens (PrimeSpectrum R)) := by rw [hVc]; trivial
    rw [← SetLike.mem_coe, Clopens.coe_finset_sup, Set.mem_iUnion₂] at htop
    rw [Clopens.coe_finset_sup, Set.mem_iUnion₂]
    exact ⟨fun hp ↦ let ⟨j, hj, hpj⟩ := htop; ⟨j, hj, hp, hpj⟩, fun ⟨_, _, hp, _⟩ ↦ hp⟩
  have hd : (t : Set κ).PairwiseDisjoint fun j ↦ U ⊓ V j :=
    fun j₁ hj₁ j₂ hj₂ hne ↦ (hVd hj₁ hj₂ hne).mono inf_le_right inf_le_right
  conv_lhs => rw [heq]
  exact clopenClass_finset_sup R t _ hd

/-- Partition independence for `ℤ`-linear combinations of clopen classes: two finite clopen
partitions with matching weights on every nonempty overlap yield the same class in `K₀(proj R)`. -/
private theorem sum_smul_clopenClass_eq_of_partition {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (U : ι → Clopens (PrimeSpectrum R)) (V : κ → Clopens (PrimeSpectrum R))
    (c : ι → ℤ) (d : κ → ℤ)
    (hUd : (s : Set ι).PairwiseDisjoint U) (hUc : s.sup U = ⊤)
    (hVd : (t : Set κ).PairwiseDisjoint V) (hVc : t.sup V = ⊤)
    (hagree : ∀ i ∈ s, ∀ j ∈ t, U i ⊓ V j ≠ ⊥ → c i = d j) :
    ∑ i ∈ s, c i • clopenClass R (U i) = ∑ j ∈ t, d j • clopenClass R (V j) := by
  calc ∑ i ∈ s, c i • clopenClass R (U i)
      = ∑ i ∈ s, ∑ j ∈ t, c i • clopenClass R (U i ⊓ V j) := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [clopenClass_eq_sum_inf R t (U i) V hVd hVc, Finset.smul_sum]
    _ = ∑ i ∈ s, ∑ j ∈ t, d j • clopenClass R (U i ⊓ V j) := by
        refine Finset.sum_congr rfl fun i hi ↦ Finset.sum_congr rfl fun j hj ↦ ?_
        by_cases hne : U i ⊓ V j = ⊥
        · rw [hne, clopenClass_bot, smul_zero, smul_zero]
        · rw [hagree i hi j hj hne]
    _ = ∑ j ∈ t, d j • clopenClass R (V j) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [clopenClass_eq_sum_inf R s (V j) U hUd hUc, Finset.smul_sum]
        exact Finset.sum_congr rfl fun i _ ↦ by rw [inf_comm]

/-- The raw function underlying `rankSection`: sum of `n • [R e_{g⁻¹{n}}]` over the finite range
of `g`. -/
private noncomputable def rankSectionFun (g : LocallyConstant (PrimeSpectrum R) ℤ) :
    SplitK0.{u} (finiteProjectiveModules R).FullSubcategory :=
  ∑ n ∈ g.range_finite.toFinset, n • clopenClass R (g.fiberClopens n)

/-- `rankSectionFun R g` agrees with the weighted sum over any finite clopen partition on which `g`
is constant on each piece. -/
private theorem rankSectionFun_eq_sum_of_partition (g : LocallyConstant (PrimeSpectrum R) ℤ)
    {ι : Type*} (s : Finset ι) (U : ι → Clopens (PrimeSpectrum R)) (c : ι → ℤ)
    (hdisj : (s : Set ι).PairwiseDisjoint U) (hcover : s.sup U = ⊤)
    (hval : ∀ i ∈ s, ∀ p ∈ U i, g p = c i) :
    rankSectionFun R g = ∑ i ∈ s, c i • clopenClass R (U i) := by
  refine sum_smul_clopenClass_eq_of_partition R g.range_finite.toFinset s g.fiberClopens U id c
    (g.pairwise_disjoint_fiberClopens.set_pairwise _) g.finset_sup_fiberClopens hdisj hcover
    fun n _ i hi hne ↦ ?_
  have hnonempty : (↑(g.fiberClopens n ⊓ U i) : Set (PrimeSpectrum R)).Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    exact hne (Clopens.ext hempty)
  obtain ⟨p, hpn, hpi⟩ := hnonempty
  exact (LocallyConstant.mem_fiberClopens.1 hpn).symm.trans (hval i hi p hpi)

/-- Pairwise disjointness and covering of the product refinement of the fiber partitions of two
locally constant functions. -/
private theorem product_fiber_partition (g h : LocallyConstant (PrimeSpectrum R) ℤ) :
    let s := g.range_finite.toFinset ×ˢ h.range_finite.toFinset
    let U : ℤ × ℤ → Clopens (PrimeSpectrum R) := fun ab ↦ g.fiberClopens ab.1 ⊓ h.fiberClopens ab.2
    (s : Set (ℤ × ℤ)).PairwiseDisjoint U ∧ s.sup U = ⊤ := by
  refine ⟨fun ab _ cd _ hne ↦ ?_, ?_⟩
  · dsimp only [Function.onFun]
    rw [← Clopens.coe_disjoint, Set.disjoint_left]
    rintro p ⟨hpa, hpb⟩ ⟨hpc, hpd⟩
    exact hne (Prod.ext
      ((LocallyConstant.mem_fiberClopens.1 hpa).symm.trans (LocallyConstant.mem_fiberClopens.1 hpc))
      ((LocallyConstant.mem_fiberClopens.1 hpb).symm.trans
        (LocallyConstant.mem_fiberClopens.1 hpd)))
  · apply Clopens.ext
    rw [Clopens.coe_finset_sup, Clopens.coe_top]
    exact Set.eq_univ_of_forall fun p ↦
      Set.mem_iUnion₂.2 ⟨(g p, h p),
        Finset.mem_product.2
          ⟨g.range_finite.mem_toFinset.2 ⟨p, rfl⟩, h.range_finite.mem_toFinset.2 ⟨p, rfl⟩⟩,
        ⟨LocallyConstant.mem_fiberClopens.2 rfl, LocallyConstant.mem_fiberClopens.2 rfl⟩⟩

private theorem rankSectionFun_add (g h : LocallyConstant (PrimeSpectrum R) ℤ) :
    rankSectionFun R (g + h) = rankSectionFun R g + rankSectionFun R h := by
  obtain ⟨hdisj, hcover⟩ := product_fiber_partition R g h
  let s := g.range_finite.toFinset ×ˢ h.range_finite.toFinset
  let U : ℤ × ℤ → Clopens (PrimeSpectrum R) := fun ab ↦ g.fiberClopens ab.1 ⊓ h.fiberClopens ab.2
  rw [rankSectionFun_eq_sum_of_partition R (g + h) s U (fun ab ↦ ab.1 + ab.2) hdisj hcover
      (fun ab _ p hp ↦ by
        have h1 : g p = ab.1 := LocallyConstant.mem_fiberClopens.1 hp.1
        have h2 : h p = ab.2 := LocallyConstant.mem_fiberClopens.1 hp.2
        simp [h1, h2]),
    rankSectionFun_eq_sum_of_partition R g s U Prod.fst hdisj hcover
      (fun ab _ p hp ↦ LocallyConstant.mem_fiberClopens.1 hp.1),
    rankSectionFun_eq_sum_of_partition R h s U Prod.snd hdisj hcover
      (fun ab _ p hp ↦ LocallyConstant.mem_fiberClopens.1 hp.2)]
  simp_rw [add_zsmul]
  exact Finset.sum_add_distrib

private theorem rankSectionFun_mul (g h : LocallyConstant (PrimeSpectrum R) ℤ) :
    rankSectionFun R (g * h) = rankSectionFun R g * rankSectionFun R h := by
  obtain ⟨hdisj, hcover⟩ := product_fiber_partition R g h
  let s := g.range_finite.toFinset ×ˢ h.range_finite.toFinset
  let U : ℤ × ℤ → Clopens (PrimeSpectrum R) := fun ab ↦ g.fiberClopens ab.1 ⊓ h.fiberClopens ab.2
  rw [rankSectionFun_eq_sum_of_partition R (g * h) s U (fun ab ↦ ab.1 * ab.2) hdisj hcover
      (fun ab _ p hp ↦ by
        have h1 : g p = ab.1 := LocallyConstant.mem_fiberClopens.1 hp.1
        have h2 : h p = ab.2 := LocallyConstant.mem_fiberClopens.1 hp.2
        simp [h1, h2])]
  simp only [rankSectionFun, s, U, Finset.sum_product, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ ?_
  rw [clopenClass_inf, smul_mul_assoc, mul_smul_comm, smul_smul]

/-- **The clopen rank section.** Sending a locally constant function `g : Spec R → ℤ` to the
weighted sum of its clopen-fiber classes defines a ring-homomorphism section of `rankHom R`. -/
noncomputable def rankSection :
    LocallyConstant (PrimeSpectrum R) ℤ →+*
      SplitK0.{u} (finiteProjectiveModules R).FullSubcategory where
  toFun := rankSectionFun R
  map_zero' := by
    rw [rankSectionFun_eq_sum_of_partition R 0 ({()} : Finset Unit) (fun _ ↦ ⊤) (fun _ ↦ 0)
      (by simp) (by simp) (fun _ _ _ _ ↦ rfl)]
    simp
  map_one' := by
    rw [rankSectionFun_eq_sum_of_partition R 1 ({()} : Finset Unit) (fun _ ↦ ⊤) (fun _ ↦ 1)
      (by simp) (by simp) (fun _ _ _ _ ↦ rfl)]
    simp
  map_add' := rankSectionFun_add R
  map_mul' := rankSectionFun_mul R

/-- Explicit fiber-sum formula for `rankSection R g`. -/
theorem rankSection_apply (g : LocallyConstant (PrimeSpectrum R) ℤ) :
    rankSection R g = ∑ n ∈ g.range_finite.toFinset, n • clopenClass R (g.fiberClopens n) :=
  (rfl)

/-- `rankSection R g` is computed by any finite clopen partition of `Spec R` on which `g` is
constant on each piece. -/
theorem rankSection_eq_sum_of_partition (g : LocallyConstant (PrimeSpectrum R) ℤ)
    {ι : Type*} (s : Finset ι) (U : ι → Clopens (PrimeSpectrum R)) (c : ι → ℤ)
    (hdisj : (s : Set ι).PairwiseDisjoint U) (hcover : s.sup U = ⊤)
    (hval : ∀ i ∈ s, ∀ p ∈ U i, g p = c i) :
    rankSection R g = ∑ i ∈ s, c i • clopenClass R (U i) :=
  rankSectionFun_eq_sum_of_partition R g s U c hdisj hcover hval

@[simp]
theorem rankSection_charFn (U : Clopens (PrimeSpectrum R)) :
    rankSection R (LocallyConstant.charFn ℤ U.isClopen) = clopenClass R U := by
  let V : Bool → Clopens (PrimeSpectrum R) := fun b ↦ if b then U else Uᶜ
  let c : Bool → ℤ := fun b ↦ if b then 1 else 0
  have hdisj : ((Finset.univ : Finset Bool) : Set Bool).PairwiseDisjoint V := by
    intro a _ b _ hab
    dsimp only [Function.onFun, V]
    cases a <;> cases b
    · exact (hab rfl).elim
    · exact disjoint_compl_left
    · exact disjoint_compl_right
    · exact (hab rfl).elim
  have hcover : (Finset.univ : Finset Bool).sup V = ⊤ := by
    simp [V, sup_compl_eq_top]
  rw [rankSection_eq_sum_of_partition R _ Finset.univ V c hdisj hcover (fun b _ p hp ↦ by
    cases b
    · rw [LocallyConstant.coe_charFn]
      exact Set.indicator_of_notMem hp 1
    · rw [LocallyConstant.coe_charFn]
      exact Set.indicator_of_mem hp 1)]
  simp [V, c]

@[simp]
theorem rankSection_const (n : ℤ) :
    rankSection R (LocallyConstant.const (PrimeSpectrum R) n) = n := by
  rw [rankSection_eq_sum_of_partition R _ ({()} : Finset Unit) (fun _ ↦ ⊤) (fun _ ↦ n)
    (by simp) (by simp) (fun _ _ _ _ ↦ rfl)]
  simp

/-- On a nonnegative locally constant function `f : Spec R → ℕ`, the rank section produces the
class of the clopen-glued module `ClopenRankModule R f`. -/
theorem rankSection_map_natCast (f : LocallyConstant (PrimeSpectrum R) ℕ) :
    rankSection R (f.map (Nat.cast : ℕ → ℤ)) = SplitK0.of.{u} (clopenRankObj R f) := by
  let s := f.range_finite.toFinset
  rw [rankSection_eq_sum_of_partition R _ s f.fiberClopens (Nat.cast : ℕ → ℤ)
    (f.pairwise_disjoint_fiberClopens.set_pairwise _) f.finset_sup_fiberClopens
    (fun k _ p hp ↦ congrArg (Nat.cast : ℕ → ℤ) (LocallyConstant.mem_fiberClopens.1 hp))]
  let piece (k : s) : (finiteProjectiveModules R).FullSubcategory :=
    ⟨ModuleCat.of R (Fin k.1 → (clopenObj R (f.fiberClopens k.1)).obj),
      finiteProjectiveModules_iff.2
        ⟨inferInstance, Module.Projective.of_equiv (DFinsupp.linearEquivFunOnFintype (R := R))⟩⟩
  have hpi : SplitK0.of.{u} (clopenRankObj R f) = ∑ k : s, SplitK0.of.{u} (piece k) :=
    SplitK0.of_eq_sum_of_linearEquiv_pi piece (ClopenRankModule.equivPi R f)
  have hpiece (k : s) :
      SplitK0.of.{u} (piece k) = (k.1 : ℤ) • clopenClass R (f.fiberClopens k.1) := by
    have hfin : SplitK0.of.{u} (piece k) =
        ∑ _ : Fin k.1, SplitK0.of.{u} (clopenObj R (f.fiberClopens k.1)) :=
      SplitK0.of_eq_sum_of_linearEquiv_pi (fun _ : Fin k.1 ↦ clopenObj R (f.fiberClopens k.1))
        (LinearEquiv.refl R _)
    rw [hfin, Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← natCast_zsmul]
    rfl
  rw [hpi, Finset.sum_congr rfl fun k _ ↦ hpiece k]
  exact (Finset.sum_coe_sort s fun k ↦ (k : ℤ) • clopenClass R (f.fiberClopens k)).symm

/-- **`rankSection R` is a right inverse to `rankHom R`.** -/
@[simp]
theorem rankHom_comp_rankSection :
    (rankHom R).comp (rankSection R) = RingHom.id _ := by
  ext g p
  simp only [RingHom.comp_apply, RingHom.id_apply, rankSection_apply, map_sum]
  rw [← LocallyConstant.evalRingHom_apply p, map_sum]
  have hmem : g p ∈ g.range_finite.toFinset := g.range_finite.mem_toFinset.2 ⟨p, rfl⟩
  rw [Finset.sum_eq_single (g p)]
  · rw [map_zsmul, rankHom_clopenClass, map_zsmul, LocallyConstant.evalRingHom_apply,
      LocallyConstant.coe_charFn, Set.indicator_of_mem (LocallyConstant.mem_fiberClopens.2 rfl),
      Pi.one_apply, smul_eq_mul, mul_one]
  · intro n _ hne
    rw [map_zsmul, rankHom_clopenClass, map_zsmul, LocallyConstant.evalRingHom_apply,
      LocallyConstant.coe_charFn,
      Set.indicator_of_notMem (fun hp ↦ hne.symm (LocallyConstant.mem_fiberClopens.1 hp)),
      smul_zero]
  · intro h; exact (h hmem).elim

@[simp]
theorem rankHom_rankSection (g : LocallyConstant (PrimeSpectrum R) ℤ) :
    rankHom R (rankSection R g) = g :=
  DFunLike.congr_fun (rankHom_comp_rankSection R) g

theorem rankHom_surjective : Function.Surjective (rankHom R) :=
  Function.RightInverse.surjective (rankHom_rankSection R)

theorem rankSection_injective : Function.Injective (rankSection R) :=
  Function.LeftInverse.injective (rankHom_rankSection R)

/-- **Naturality of the rank section under scalar extension.** -/
theorem extend_comp_rankSection {S : Type u} [CommRing S] (f : R →+* S) :
    f.finiteProjectiveModulesSplitK0Extend.comp (rankSection R) =
      (rankSection S).comp
        (LocallyConstant.comapRingHom
          ⟨PrimeSpectrum.comap f, PrimeSpectrum.continuous_comap f⟩) := by
  ext g
  let g' : LocallyConstant (PrimeSpectrum S) ℤ :=
    LocallyConstant.comapRingHom ⟨PrimeSpectrum.comap f, PrimeSpectrum.continuous_comap f⟩ g
  let s := g.range_finite.toFinset
  let U : ℤ → Clopens (PrimeSpectrum S) := fun n ↦
    ⟨PrimeSpectrum.comap f ⁻¹' (g.fiberClopens n),
      (g.fiberClopens n).isClopen.preimage (PrimeSpectrum.continuous_comap f)⟩
  have hdisj : (s : Set ℤ).PairwiseDisjoint U := fun a _ b _ hab ↦ by
    dsimp only [Function.onFun]
    rw [← Clopens.coe_disjoint, Set.disjoint_left]
    intro q hqa hqb
    exact hab ((LocallyConstant.mem_fiberClopens.1 hqa).symm.trans
      (LocallyConstant.mem_fiberClopens.1 hqb))
  have hcover : s.sup U = ⊤ := by
    apply Clopens.ext
    rw [Clopens.coe_finset_sup, Clopens.coe_top]
    exact Set.eq_univ_of_forall fun q ↦
      Set.mem_iUnion₂.2 ⟨g (q.comap f), g.range_finite.mem_toFinset.2 ⟨q.comap f, rfl⟩,
        LocallyConstant.mem_fiberClopens.2 rfl⟩
  rw [RingHom.comp_apply, RingHom.comp_apply, rankSection_apply, map_sum,
    rankSection_eq_sum_of_partition S g' s U id hdisj hcover
      (fun n _ q hq ↦ (LocallyConstant.mem_fiberClopens (f := g)).1 hq)]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  rw [map_zsmul, extend_clopenClass R f (g.fiberClopens n), id_eq]

theorem extend_rankSection {S : Type u} [CommRing S] (f : R →+* S)
    (g : LocallyConstant (PrimeSpectrum R) ℤ) :
    f.finiteProjectiveModulesSplitK0Extend (rankSection R g) =
      rankSection S (g.comap ⟨PrimeSpectrum.comap f, PrimeSpectrum.continuous_comap f⟩) :=
  DFunLike.congr_fun (extend_comp_rankSection R f) g

end RankSection

/-! ### Reduced `K₀` and split exactness -/

section ReducedK0

variable (R : Type u) [CommRing R]

/-- **Reduced `K₀` of a commutative ring.** The ideal `K̃₀(R) := ker(rankHom R)` of virtual
finitely generated projective modules of locally constant rank zero. -/
noncomputable def reducedK0 : Ideal (SplitK0.{u} (finiteProjectiveModules R).FullSubcategory) :=
  RingHom.ker (rankHom R)

variable {R} in
@[simp]
theorem mem_reducedK0_iff {x : SplitK0.{u} (finiteProjectiveModules R).FullSubcategory} :
    x ∈ reducedK0 R ↔ rankHom R x = 0 :=
  Iff.rfl

/-- **Splitting of `K₀(proj R)`.** The rank homomorphism and its clopen section split
`K₀(proj R)` additively into `LocallyConstant (PrimeSpectrum R) ℤ × reducedK0 R`. -/
noncomputable def splitK0EquivProdReducedK0 :
    SplitK0.{u} (finiteProjectiveModules R).FullSubcategory ≃+
      LocallyConstant (PrimeSpectrum R) ℤ × reducedK0 R where
  toFun x := (rankHom R x, ⟨x - rankSection R (rankHom R x), by simp⟩)
  invFun p := rankSection R p.1 + p.2.1
  map_add' x y := by
    apply Prod.ext
    · exact map_add (rankHom R) x y
    · apply Subtype.ext
      simp only [Prod.snd_add, Submodule.coe_add, map_add]
      abel
  left_inv x := by simp
  right_inv p := by
    apply Prod.ext
    · simp [mem_reducedK0_iff.1 p.2.2]
    · apply Subtype.ext
      simp [mem_reducedK0_iff.1 p.2.2]

@[simp]
theorem splitK0EquivProdReducedK0_fst
    (x : SplitK0.{u} (finiteProjectiveModules R).FullSubcategory) :
    (splitK0EquivProdReducedK0 R x).1 = rankHom R x := (rfl)

@[simp]
theorem splitK0EquivProdReducedK0_snd
    (x : SplitK0.{u} (finiteProjectiveModules R).FullSubcategory) :
    ((splitK0EquivProdReducedK0 R x).2 :
      SplitK0.{u} (finiteProjectiveModules R).FullSubcategory) =
      x - rankSection R (rankHom R x) := (rfl)

@[simp]
theorem splitK0EquivProdReducedK0_symm_apply
    (p : LocallyConstant (PrimeSpectrum R) ℤ × reducedK0 R) :
    (splitK0EquivProdReducedK0 R).symm p = rankSection R p.1 + p.2.1 := (rfl)

end ReducedK0

/-! ### Semilocal, localization-kernel, and PID classifications -/

section Classification

variable (R : Type u) [CommRing R]

/-- Over a commutative semilocal ring, `rankSection R` is also a left inverse to `rankHom R`. -/
@[simp]
theorem rankSection_comp_rankHom_of_finite_maximalSpectrum [Finite (MaximalSpectrum R)] :
    (rankSection R).comp (rankHom R) = RingHom.id _ := by
  refine SplitK0.ringHom_ext fun P ↦ ?_
  have := Module.finitePresentation_of_projective R P.obj
  have := Module.Flat.of_projective (R := R) (M := P.obj)
  obtain ⟨θ⟩ := nonempty_linearEquiv_clopenRankModule_of_finite_maximalSpectrum (R := R) P.obj
  have hr : rankHom R (SplitK0.of.{u} P) =
      (Module.rankLocallyConstant R P.obj).map (Nat.cast : ℕ → ℤ) := by
    ext p; simp
  rw [RingHom.comp_apply, RingHom.id_apply, hr, rankSection_map_natCast]
  exact (SplitK0.of_congr (ObjectProperty.isoMk _ θ.toModuleIso)).symm

@[simp]
theorem rankSection_rankHom_of_finite_maximalSpectrum [Finite (MaximalSpectrum R)]
    (x : SplitK0.{u} (finiteProjectiveModules R).FullSubcategory) :
    rankSection R (rankHom R x) = x :=
  DFunLike.congr_fun (rankSection_comp_rankHom_of_finite_maximalSpectrum R) x

/-- **Semilocal `K₀` classification.** For a commutative semilocal ring `R`, the locally constant
rank homomorphism is a ring isomorphism
`K₀(proj R) ≃+* LocallyConstant (PrimeSpectrum R) ℤ`. -/
noncomputable def rankEquivOfFiniteMaximalSpectrum [Finite (MaximalSpectrum R)] :
    SplitK0.{u} (finiteProjectiveModules R).FullSubcategory ≃+*
      LocallyConstant (PrimeSpectrum R) ℤ :=
  RingEquiv.ofRingHom (rankHom R) (rankSection R)
    (rankHom_comp_rankSection R)
    (rankSection_comp_rankHom_of_finite_maximalSpectrum R)

@[simp]
theorem rankEquivOfFiniteMaximalSpectrum_apply [Finite (MaximalSpectrum R)]
    (x : SplitK0.{u} (finiteProjectiveModules R).FullSubcategory) :
    rankEquivOfFiniteMaximalSpectrum R x = rankHom R x := (rfl)

@[simp]
theorem rankEquivOfFiniteMaximalSpectrum_symm_apply [Finite (MaximalSpectrum R)]
    (g : LocallyConstant (PrimeSpectrum R) ℤ) :
    (rankEquivOfFiniteMaximalSpectrum R).symm g = rankSection R g := (rfl)

theorem rankEquivOfFiniteMaximalSpectrum_of [Finite (MaximalSpectrum R)]
    (P : (finiteProjectiveModules R).FullSubcategory) (p : PrimeSpectrum R) :
    rankEquivOfFiniteMaximalSpectrum R (SplitK0.of.{u} P) p =
      (Module.rankAtStalk (R := R) P.obj p : ℤ) :=
  rankHom_of R P p

/-- The reduced `K₀` ideal of a commutative semilocal ring vanishes. -/
theorem reducedK0_eq_bot_of_finite_maximalSpectrum [Finite (MaximalSpectrum R)] :
    reducedK0 R = ⊥ :=
  eq_bot_iff.2 fun x hx ↦ by
    rw [Submodule.mem_bot, ← rankSection_rankHom_of_finite_maximalSpectrum R x,
      mem_reducedK0_iff.1 hx, map_zero]

/-- **Localization-kernel characterization of reduced `K₀`.** A class in `K₀(proj R)` has rank
zero everywhere on `Spec R` if and only if it maps to zero in `K₀(proj R_p)` at every prime `p`. -/
theorem mem_reducedK0_iff_forall_localization
    (x : SplitK0.{u} (finiteProjectiveModules R).FullSubcategory) :
    x ∈ reducedK0 R ↔
      ∀ p : PrimeSpectrum R,
        (algebraMap R (Localization.AtPrime p.asIdeal)).finiteProjectiveModulesSplitK0Extend x =
          0 := by
  refine ⟨fun hx p ↦ ?_, fun hloc ↦ ?_⟩
  · have hrank : rankHom (Localization.AtPrime p.asIdeal)
        ((algebraMap R (Localization.AtPrime p.asIdeal)).finiteProjectiveModulesSplitK0Extend x) =
        0 := by
      ext q
      rw [rankHom_extend_apply, mem_reducedK0_iff.1 hx]
      rfl
    have hmem :
        (algebraMap R (Localization.AtPrime p.asIdeal)).finiteProjectiveModulesSplitK0Extend x ∈
          reducedK0 (Localization.AtPrime p.asIdeal) :=
      mem_reducedK0_iff.2 hrank
    rwa [reducedK0_eq_bot_of_finite_maximalSpectrum] at hmem
  · rw [mem_reducedK0_iff]
    ext p
    have hclosed :
        (IsLocalRing.closedPoint (Localization.AtPrime p.asIdeal)).comap
          (algebraMap R (Localization.AtPrime p.asIdeal)) = p :=
      PrimeSpectrum.ext
        (IsLocalization.AtPrime.under_maximalIdeal (Localization.AtPrime p.asIdeal) p.asIdeal)
    have h := congrFun (congrArg DFunLike.coe (congrArg
      (rankHom (Localization.AtPrime p.asIdeal)) (hloc p)))
      (IsLocalRing.closedPoint (Localization.AtPrime p.asIdeal))
    rw [rankHom_extend_apply, hclosed, map_zero] at h
    exact h

/-- If every finitely generated projective `R`-module is free, then `rankSection R` is a left
inverse to `rankHom R`. -/
theorem rankSection_comp_rankHom_of_forall_free
    (hfree : ∀ P : (finiteProjectiveModules R).FullSubcategory, Module.Free R P.obj) :
    (rankSection R).comp (rankHom R) = RingHom.id _ := by
  refine SplitK0.ringHom_ext fun P ↦ ?_
  rcases subsingleton_or_nontrivial R with _ | _
  · have : Subsingleton ((finiteProjectiveModules R).ι.obj P) := Module.subsingleton R P.obj
    have hzero : SplitK0.of.{u} P = 0 :=
      SplitK0.of_eq_zero_of_isZero (Limits.IsZero.of_full_of_faithful_of_isZero
        (finiteProjectiveModules R).ι P (ModuleCat.isZero_of_subsingleton _))
    rw [RingHom.comp_apply, RingHom.id_apply, hzero, map_zero, map_zero]
  · have := hfree P
    let b := Module.Free.chooseBasis R P.obj
    let n := Fintype.card (Module.Free.ChooseBasisIndex R P.obj)
    let θ : P.obj ≃ₗ[R] (Fin n → R) :=
      b.equivFun.trans (LinearEquiv.funCongrLeft R R (Fintype.equivFin _).symm)
    have hrank :
        rankHom R (SplitK0.of.{u} P) = LocallyConstant.const (PrimeSpectrum R) (n : ℤ) := by
      ext p
      rw [rankHom_of, congrFun (Module.rankAtStalk_eq_of_equiv θ) p, Module.rankAtStalk_fin_fun]
      rfl
    have hof : SplitK0.of.{u} P =
        (n : SplitK0.{u} (finiteProjectiveModules R).FullSubcategory) := by
      rw [SplitK0.of_eq_nsmul_of_linearEquiv_fin
          (R' := 𝟙_ (finiteProjectiveModules R).FullSubcategory) θ (LinearEquiv.refl R R),
        ← SplitK0.one_def, nsmul_eq_mul, mul_one]
    rw [RingHom.comp_apply, RingHom.id_apply, hrank, rankSection_const, Int.cast_natCast, hof]

/-- If every finitely generated projective `R`-module is free, then the reduced `K₀` ideal of `R`
vanishes. -/
theorem reducedK0_eq_bot_of_forall_free
    (hfree : ∀ P : (finiteProjectiveModules R).FullSubcategory, Module.Free R P.obj) :
    reducedK0 R = ⊥ :=
  eq_bot_iff.2 fun x hx ↦ by
    have h := DFunLike.congr_fun (rankSection_comp_rankHom_of_forall_free R hfree) x
    rw [RingHom.comp_apply, RingHom.id_apply, mem_reducedK0_iff.1 hx, map_zero] at h
    exact (Submodule.mem_bot _).2 h.symm

/-- If `R` is nontrivial and every finitely generated projective `R`-module is free, then `Spec R`
is connected. -/
theorem connectedSpace_primeSpectrum_of_forall_free [Nontrivial R]
    (hfree : ∀ P : (finiteProjectiveModules R).FullSubcategory, Module.Free R P.obj) :
    ConnectedSpace (PrimeSpectrum R) :=
  (connectedSpace_primeSpectrum_iff_forall_finite_projective_rankAtStalk_const R).2
    fun P _ _ _ _ ↦
      have := hfree ⟨ModuleCat.of R P, finiteProjectiveModules_iff.2 ⟨inferInstance, inferInstance⟩⟩
      ⟨Module.finrank R P, fun p ↦
        congrFun (Module.rankAtStalk_eq_finrank_of_free (R := R) (M := P)) p⟩

/-- If `R` is nontrivial and every finitely generated projective `R`-module is free, then stalk
rank gives a ring isomorphism `K₀(proj R) ≃+* ℤ`. -/
noncomputable def rankEquivIntOfForallFree [Nontrivial R]
    (hfree : ∀ P : (finiteProjectiveModules R).FullSubcategory, Module.Free R P.obj) :
    SplitK0.{u} (finiteProjectiveModules R).FullSubcategory ≃+* ℤ :=
  haveI := connectedSpace_primeSpectrum_of_forall_free R hfree
  (RingEquiv.ofRingHom (rankHom R) (rankSection R)
    (rankHom_comp_rankSection R) (rankSection_comp_rankHom_of_forall_free R hfree)).trans
    (LocallyConstant.constRingEquiv (PrimeSpectrum R) ℤ).symm

@[simp]
theorem rankEquivIntOfForallFree_of [Nontrivial R]
    (hfree : ∀ P : (finiteProjectiveModules R).FullSubcategory, Module.Free R P.obj)
    (P : (finiteProjectiveModules R).FullSubcategory) :
    rankEquivIntOfForallFree R hfree (SplitK0.of.{u} P) = (Module.finrank R P.obj : ℤ) := by
  have := connectedSpace_primeSpectrum_of_forall_free R hfree
  have := hfree P
  obtain ⟨p₀⟩ : Nonempty (PrimeSpectrum R) := inferInstance
  rw [rankEquivIntOfForallFree, RingEquiv.trans_apply, RingEquiv.ofRingHom_apply,
    LocallyConstant.constRingEquiv_symm_apply _ _ _ p₀, rankHom_of,
    congrFun (Module.rankAtStalk_eq_finrank_of_free (R := R) (M := P.obj)) p₀]
  rfl

/-- **Connected semilocal / local `K₀` classification.** Over a commutative semilocal ring with
connected prime spectrum (in particular, over any commutative local ring), stalk rank gives a ring
isomorphism `K₀(proj R) ≃+* ℤ`. -/
noncomputable def rankEquivIntOfFiniteMaximalSpectrum
    [Finite (MaximalSpectrum R)] [ConnectedSpace (PrimeSpectrum R)] :
    SplitK0.{u} (finiteProjectiveModules R).FullSubcategory ≃+* ℤ :=
  (rankEquivOfFiniteMaximalSpectrum R).trans
    (LocallyConstant.constRingEquiv (PrimeSpectrum R) ℤ).symm

@[simp]
theorem rankEquivIntOfFiniteMaximalSpectrum_of
    [Finite (MaximalSpectrum R)] [ConnectedSpace (PrimeSpectrum R)]
    (P : (finiteProjectiveModules R).FullSubcategory) :
    rankEquivIntOfFiniteMaximalSpectrum R (SplitK0.of.{u} P) = (Module.finrank R P.obj : ℤ) := by
  have := Module.finitePresentation_of_projective R P.obj
  have := Module.Flat.of_projective (R := R) (M := P.obj)
  have : Module.Free R P.obj := free_of_finite_maximalSpectrum_of_preconnectedSpace P.obj
  obtain ⟨p₀⟩ : Nonempty (PrimeSpectrum R) := inferInstance
  rw [rankEquivIntOfFiniteMaximalSpectrum, RingEquiv.trans_apply,
    rankEquivOfFiniteMaximalSpectrum_apply, LocallyConstant.constRingEquiv_symm_apply _ _ _ p₀,
    rankHom_of, congrFun (Module.rankAtStalk_eq_finrank_of_free (R := R) (M := P.obj)) p₀]
  rfl

/-- **PID `K₀` classification.** Over a principal ideal domain `R`, every finitely generated
projective module is free, so stalk rank gives a ring isomorphism `K₀(proj R) ≃+* ℤ`. -/
noncomputable def rankEquivIntOfIsPrincipalIdealRing [IsDomain R] [IsPrincipalIdealRing R] :
    SplitK0.{u} (finiteProjectiveModules R).FullSubcategory ≃+* ℤ :=
  rankEquivIntOfForallFree R fun P ↦
    have := Module.Flat.of_projective (R := R) (M := P.obj)
    Module.free_of_finite_type_torsion_free'

@[simp]
theorem rankEquivIntOfIsPrincipalIdealRing_of [IsDomain R] [IsPrincipalIdealRing R]
    (P : (finiteProjectiveModules R).FullSubcategory) :
    rankEquivIntOfIsPrincipalIdealRing R (SplitK0.of.{u} P) = (Module.finrank R P.obj : ℤ) :=
  rankEquivIntOfForallFree_of R _ P

end Classification

end TauCeti.FiniteProjectiveModules
