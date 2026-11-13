/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import TauCeti.Algebra.Category.ModuleCat.FiniteLength
public import TauCeti.Algebra.Category.ModuleCat.MatlisDual
public import TauCeti.RingTheory.Length.Algebra
public import TauCeti.CategoryTheory.Preadditive.Indecomposable

/-!
# Matlis duality on modules of finite length

Let `R` be a commutative ring, `A` an `R`-algebra, and `E` an injective `R`-module such that
`Hom_R(R ⧸ 𝔪, E)` has length one for every maximal ideal `𝔪`: for instance an injective hull of
`R ⧸ J(R)` when `R ⧸ J(R)` is semisimple
(`TauCeti.IsInjectiveEnvelope.length_quotient_linearMap_eq_one`), `E = R` for a field `R`, or
`E = ℚ ⧸ ℤ` for `R = ℤ`. Then the Matlis dual `D_R = Hom_R(-, E)` is an anti-equivalence between the
left and the right `A`-modules of finite length over `R` (`ModuleCat.matlisDuality`), with
evaluation `M → D_R (D_R M)` as unit and counit. These are the modules whose restriction of scalars
to `R` has finite length; over a field they are the finite-dimensional modules.

When `A` is finitely generated as an `R`-module, a module has finite length over `R` exactly when it
has finite length over `A` (`TauCeti.isFiniteLength_iff_of_finite`), so the duality is one between
the categories of left and right `A`-modules of finite length (`ModuleCat.matlisDualityOfFinite`).
Without finiteness of `A` the two classes can differ, and the duality is on the first: the free
algebra `k⟨x, y⟩` has simple modules of infinite dimension over `k`, for which evaluation
`M → D_R (D_R M)` is not surjective.

The construction `ModuleCat.matlisDualityOn` restricts `D_R` to any two classes of modules of
finite length over `R` that it exchanges. Besides the two dualities above, it gives the duality
between finitely generated modules over an Artin algebra
(`TauCeti.IsInjectiveEnvelope.fgModuleCatMatlisDuality`).

The consequences of the duality are recorded for bundled modules of finite length over `R`:
dualizing is bijective on morphisms, reflects isomorphisms, reverses endomorphism rings, and
preserves and reflects indecomposability.

## Main definitions

* `ModuleCat.matlisDualityOn`: `D_R` as an anti-equivalence between two classes of modules of
  finite length over `R` that it exchanges.
* `ModuleCat.matlisDuality`: the anti-equivalence between left and right `A`-modules of finite
  length over `R`.
* `ModuleCat.matlisDualityOfFinite`: for `A` finite over `R`, the anti-equivalence between left and
  right `A`-modules of finite length.
* `ModuleCat.matlisDualEndRingEquiv` and `ModuleCat.matlisDualOpEndRingEquiv`: the ring isomorphism
  `End(M)ᵐᵒᵖ ≃ End(D_R M)`.

## Main results

* `ModuleCat.bijective_matlisDualMap` and `ModuleCat.bijective_matlisDualOpMap`: dualizing is
  bijective on morphisms.
* `ModuleCat.nonempty_iso_matlisDualObj_iff` and `ModuleCat.nonempty_iso_matlisDualOpObj_iff`:
  dualizing reflects isomorphisms.
* `ModuleCat.indecomposable_matlisDualObj_iff` and `ModuleCat.indecomposable_matlisDualOpObj_iff`:
  dualizing preserves and reflects indecomposability.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, Cambridge
  University Press (1995), Section II.3.
* The Stacks Project, Section 47.7, Matlis duality, Tag 08Z1.
-/

public section

open CategoryTheory TauCeti TauCeti.MatlisDual

universe u v w t

namespace ModuleCat

attribute [local instance] moduleOfAlgebra isScalarTower_moduleOfAlgebra

variable {R : Type u} [CommRing R] {E : Type v} [AddCommGroup E] [Module R E]
  [Module.Injective R E] [Small.{v} R] {A : Type t} [Ring A] [Algebra R A]
  (hE : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Module.length R (R ⧸ 𝔪 →ₗ[R] E) = 1)


omit [Module.Injective R E] [Small.{v} R] in
/-- A module over an `R`-algebra lies in the inverse image of the modules of finite length over `R`
exactly when it has finite length over `R`. -/
theorem isFiniteLength_inverseImage_restrictScalars_iff {B : Type*} [Ring B] [Algebra R B]
    (M : ModuleCat.{w} B) :
    (isFiniteLength.{w} R).inverseImage (restrictScalars.{w} (algebraMap R B)) M ↔
      IsFiniteLength R M := by
  rw [ObjectProperty.prop_inverseImage_iff, isFiniteLength_iff]
  rfl

include hE in
/-- The dual of a left module of finite length over `R` has finite length over `R`. -/
theorem isFiniteLength_matlisDualObj {M : ModuleCat.{max v w} A} (hM : IsFiniteLength R M) :
    IsFiniteLength R (matlisDualObj R E M) := by
  rw [← Module.length_ne_top_iff] at hM ⊢
  rwa [(matlisDualObjLinearEquiv R E M).length_eq, length_linearMap_of_forall_isMaximal hE]

include hE in
/-- The dual of a right module of finite length over `R` has finite length over `R`. -/
theorem isFiniteLength_matlisDualOpObj {N : ModuleCat.{max v w} Aᵐᵒᵖ} (hN : IsFiniteLength R N) :
    IsFiniteLength R (matlisDualOpObj R E N) := by
  rw [← Module.length_ne_top_iff] at hN ⊢
  rwa [((matlisDualOpObjEquiv R E N).restrictScalars R).length_eq,
    (equivLinearMap R E N).length_eq, length_linearMap_of_forall_isMaximal hE]

/-- **Matlis duality on classes of modules it exchanges.** If `P` and `Q` are classes of left and
right `A`-modules of finite length over `R`, and `D_R` sends `P` into `Q` and `Q` into `P`, then
`D_R` is an anti-equivalence between them, with evaluation as unit and counit. -/
@[expose]
noncomputable def matlisDualityOn (P : ObjectProperty (ModuleCat.{max v w} A))
    (Q : ObjectProperty (ModuleCat.{max v w} Aᵐᵒᵖ))
    (hP : ∀ M, P M → IsFiniteLength R M) (hQ : ∀ N, Q N → IsFiniteLength R N)
    (hPQ : ∀ M, P M → Q (matlisDualObj R E M)) (hQP : ∀ N, Q N → P (matlisDualOpObj R E N)) :
    P.FullSubcategoryᵒᵖ ≌ Q.FullSubcategory where
  functor := ObjectProperty.lift _ (P.ι.op ⋙ matlisDual R E) fun M => hPQ _ M.unop.property
  inverse := (ObjectProperty.lift _ (Q.ι.op ⋙ matlisDualOp R E) fun N =>
    hQP _ N.unop.property).rightOp
  unitIso := NatIso.ofComponents (fun M =>
      (ObjectProperty.isoMk _ (matlisDualEvalIso hE M.unop.obj (hP _ M.unop.property))).symm.op)
    (fun {X Y} g => Quiver.Hom.unop_inj <| (Iso.inv_comp_eq _).mpr <|
      ((Iso.eq_comp_inv _).mpr <| ObjectProperty.hom_ext _ <|
        matlisDualEvalIso_hom_naturality hE g.unop.hom (hP _ Y.unop.property)
          (hP _ X.unop.property)).trans (Category.assoc _ _ _))
  counitIso := NatIso.ofComponents (fun N =>
      (ObjectProperty.isoMk _ (matlisDualEvalIsoOp (A := A) hE N.obj (hQ _ N.property))).symm)
    (fun {X Y} g => (Iso.comp_inv_eq _).mpr <| ((Iso.eq_inv_comp _).mpr <|
      (ObjectProperty.hom_ext _ <|
        (matlisDualEvalIsoOp_hom_naturality (A := A) hE g.hom (hQ _ X.property)
          (hQ _ Y.property)).symm)).trans
        (Category.assoc _ _ _).symm)
  functor_unitIso_comp M := by
    refine ObjectProperty.hom_ext _ ?_
    exact (Iso.comp_inv_eq_id (matlisDualEvalIsoOp (A := A) hE (matlisDualObj R E M.unop.obj)
      (hQ _ (hPQ _ M.unop.property)))).mpr
      (matlisDualEvalIsoOp_matlisDualObj_hom hE M.unop.obj (hP _ M.unop.property)
        (hQ _ (hPQ _ M.unop.property))).symm

section OnLemmas

variable (P : ObjectProperty (ModuleCat.{max v w} A))
  (Q : ObjectProperty (ModuleCat.{max v w} Aᵐᵒᵖ))
  (hP : ∀ M, P M → IsFiniteLength R M) (hQ : ∀ N, Q N → IsFiniteLength R N)
  (hPQ : ∀ M, P M → Q (matlisDualObj R E M)) (hQP : ∀ N, Q N → P (matlisDualOpObj R E N))

@[simp]
theorem matlisDualityOn_functor_obj_obj (M : P.FullSubcategoryᵒᵖ) :
    ((matlisDualityOn hE P Q hP hQ hPQ hQP).functor.obj M).obj = matlisDualObj R E M.unop.obj :=
  rfl

@[simp]
theorem matlisDualityOn_functor_map_hom {M M' : P.FullSubcategoryᵒᵖ} (g : M ⟶ M') :
    ((matlisDualityOn hE P Q hP hQ hPQ hQP).functor.map g).hom = matlisDualMap R E g.unop.hom :=
  rfl

@[simp]
theorem matlisDualityOn_inverse_obj_unop_obj (N : Q.FullSubcategory) :
    ((matlisDualityOn hE P Q hP hQ hPQ hQP).inverse.obj N).unop.obj = matlisDualOpObj R E N.obj :=
  rfl

@[simp]
theorem matlisDualityOn_inverse_map_unop_hom {N N' : Q.FullSubcategory} (g : N ⟶ N') :
    ((matlisDualityOn hE P Q hP hQ hPQ hQP).inverse.map g).unop.hom = matlisDualOpMap R E g.hom :=
  rfl

/-- The unit of the duality is evaluation `M → D_R (D_R M)`. -/
@[simp]
theorem matlisDualityOn_unitIso_inv_app (M : P.FullSubcategoryᵒᵖ) :
    ((matlisDualityOn hE P Q hP hQ hPQ hQP).unitIso.inv.app M).unop.hom =
      (matlisDualEvalIso hE M.unop.obj (hP _ M.unop.property)).hom :=
  rfl

/-- The inverse of the counit of the duality is evaluation `N → D_R (D_R N)`. -/
@[simp]
theorem matlisDualityOn_counitIso_inv_app (N : Q.FullSubcategory) :
    ((matlisDualityOn hE P Q hP hQ hPQ hQP).counitIso.inv.app N).hom =
      (matlisDualEvalIsoOp (A := A) hE N.obj (hQ _ N.property)).hom :=
  rfl

end OnLemmas

/-- **Matlis duality on modules of finite length.** If `E` is injective and `Hom_R(R ⧸ 𝔪, E)` has
length one for every maximal ideal `𝔪`, then `D_R = Hom_R(-, E)` is an anti-equivalence between the
left and the right `A`-modules of finite length over `R`, for every `R`-algebra `A`. Over a field
these are the finite-dimensional modules. -/
@[expose]
noncomputable def matlisDuality :
    ((isFiniteLength.{max v w} R).inverseImage
        (restrictScalars.{max v w} (algebraMap R A))).FullSubcategoryᵒᵖ ≌
      ((isFiniteLength.{max v w} R).inverseImage
        (restrictScalars.{max v w} (algebraMap R Aᵐᵒᵖ))).FullSubcategory :=
  matlisDualityOn hE _ _ (fun M h ↦ (isFiniteLength_inverseImage_restrictScalars_iff M).mp h)
    (fun N h ↦ (isFiniteLength_inverseImage_restrictScalars_iff N).mp h)
    (fun M h ↦ (isFiniteLength_inverseImage_restrictScalars_iff _).mpr
      (isFiniteLength_matlisDualObj hE ((isFiniteLength_inverseImage_restrictScalars_iff M).mp h)))
    (fun N h ↦ (isFiniteLength_inverseImage_restrictScalars_iff _).mpr
      (isFiniteLength_matlisDualOpObj hE
        ((isFiniteLength_inverseImage_restrictScalars_iff N).mp h)))

/-- **Matlis duality for modules of finite length over a finite algebra.** For an `R`-algebra `A`
that is finitely generated as an `R`-module, `D_R` is an anti-equivalence between the left and the
right `A`-modules of finite length, since these are the modules of finite length over `R`
(`TauCeti.isFiniteLength_iff_of_finite`). -/
@[expose]
noncomputable def matlisDualityOfFinite [Module.Finite R A] :
    (isFiniteLength.{max v w} A).FullSubcategoryᵒᵖ ≌
      (isFiniteLength.{max v w} Aᵐᵒᵖ).FullSubcategory :=
  matlisDualityOn hE _ _
    (fun M h ↦ (isFiniteLength_iff_of_finite R A M).mp ((isFiniteLength_iff M).mp h))
    (fun N h ↦ (isFiniteLength_iff_of_finite R Aᵐᵒᵖ N).mp ((isFiniteLength_iff N).mp h))
    (fun M h ↦ (isFiniteLength_iff _).mpr ((isFiniteLength_iff_of_finite R Aᵐᵒᵖ _).mpr
      (isFiniteLength_matlisDualObj hE
        ((isFiniteLength_iff_of_finite R A M).mp ((isFiniteLength_iff M).mp h)))))
    (fun N h ↦ (isFiniteLength_iff _).mpr ((isFiniteLength_iff_of_finite R A _).mpr
      (isFiniteLength_matlisDualOpObj hE
        ((isFiniteLength_iff_of_finite R Aᵐᵒᵖ N).mp ((isFiniteLength_iff N).mp h)))))

section Consequences

/-! ### Consequences of the duality

Each statement below is about modules of finite length over `R`, as objects of `ModuleCat`, and
is read off from `ModuleCat.matlisDuality`: an anti-equivalence is fully faithful, so it is
bijective on morphisms, reflects isomorphisms, and identifies endomorphism rings up to reversal of
multiplication, which in turn transfers indecomposability. -/

variable {M M' : ModuleCat.{max v w} A}

include hE in
/-- **Matlis duality is bijective on morphisms** between left modules of finite length over `R`. -/
theorem bijective_matlisDualMap (hM : IsFiniteLength R M) (hM' : IsFiniteLength R M') :
    Function.Bijective
      (matlisDualMap R E : (M ⟶ M') → (matlisDualObj R E M' ⟶ matlisDualObj R E M)) := by
  let X : ((isFiniteLength.{max v w} R).inverseImage
      (restrictScalars.{max v w} (algebraMap R A))).FullSubcategory :=
    ⟨M, (isFiniteLength_inverseImage_restrictScalars_iff M).mpr hM⟩
  let X' : ((isFiniteLength.{max v w} R).inverseImage
      (restrictScalars.{max v w} (algebraMap R A))).FullSubcategory :=
    ⟨M', (isFiniteLength_inverseImage_restrictScalars_iff M').mpr hM'⟩
  have h := (matlisDuality hE (A := A)).fullyFaithfulFunctor.map_bijective (Opposite.op X')
    (Opposite.op X)
  refine ⟨fun g g' hg ↦ ?_, fun f ↦ ?_⟩
  · exact congrArg (fun k ↦ k.unop.hom) (h.1 (a₁ := (ObjectProperty.homMk g : X ⟶ X').op)
      (a₂ := (ObjectProperty.homMk g' : X ⟶ X').op) (ObjectProperty.hom_ext _ hg))
  · obtain ⟨k, hk⟩ := h.2 (ObjectProperty.homMk f)
    exact ⟨k.unop.hom, congrArg (fun k ↦ k.hom) hk⟩

include hE in
/-- **Matlis duality reflects isomorphisms** of left modules of finite length over `R`. -/
theorem nonempty_iso_matlisDualObj_iff (hM : IsFiniteLength R M) (hM' : IsFiniteLength R M') :
    Nonempty (matlisDualObj R E M ≅ matlisDualObj R E M') ↔ Nonempty (M ≅ M') := by
  refine ⟨fun ⟨i⟩ ↦ ?_, fun ⟨i⟩ ↦ ⟨((matlisDual R E).mapIso i.op).symm⟩⟩
  let P := (isFiniteLength.{max v w} R).inverseImage (restrictScalars.{max v w} (algebraMap R A))
  let X : P.FullSubcategory := ⟨M, (isFiniteLength_inverseImage_restrictScalars_iff M).mpr hM⟩
  let X' : P.FullSubcategory := ⟨M', (isFiniteLength_inverseImage_restrictScalars_iff M').mpr hM'⟩
  let k := (matlisDuality hE (A := A)).fullyFaithfulFunctor.preimageIso
    (ObjectProperty.isoMk _ i : (matlisDuality hE).functor.obj (Opposite.op X) ≅
      (matlisDuality hE).functor.obj (Opposite.op X'))
  exact ⟨(P.ι.mapIso k.unop).symm⟩

include hE in
/-- **Matlis duality reverses endomorphism rings**: for a left module `M` of finite length over
`R`, dualizing is a ring isomorphism `End(M)ᵐᵒᵖ ≃ End(D_R M)`. -/
noncomputable def matlisDualEndRingEquiv (hM : IsFiniteLength R M) :
    (End M)ᵐᵒᵖ ≃+* End (matlisDualObj R E M) :=
  RingEquiv.ofBijective
    ({ toFun f := End.of (matlisDualMap R E f.unop.asHom)
       map_one' := End.ext ((matlisDual R E).map_id _)
       map_mul' f g := End.ext ((matlisDual R E).map_comp g.unop.asHom.op f.unop.asHom.op)
       map_zero' := End.ext ((matlisDual R E).map_zero _ _)
       map_add' _ _ := End.ext (matlisDualMap_add R E _ _) } :
      (End M)ᵐᵒᵖ →+* End (matlisDualObj R E M))
    (End.homEquiv.symm.bijective.comp ((bijective_matlisDualMap hE hM hM).comp
      (End.homEquiv.bijective.comp MulOpposite.unop_bijective)))

@[simp]
theorem matlisDualEndRingEquiv_apply_asHom (hM : IsFiniteLength R M) (f : (End M)ᵐᵒᵖ) :
    (matlisDualEndRingEquiv hE hM f).asHom = matlisDualMap R E f.unop.asHom :=
  (rfl)

include hE in
/-- **Matlis duality preserves and reflects indecomposability** of left modules of finite length
over `R`. -/
theorem indecomposable_matlisDualObj_iff (hM : IsFiniteLength R M) :
    Indecomposable (matlisDualObj R E M) ↔ Indecomposable M :=
  (TauCeti.indecomposable_iff_of_bijective_of_map_comp (matlisDualMap R E)
    (bijective_matlisDualMap hE hM hM) ((matlisDual R E).map_id _)
    ((matlisDual R E).map_zero _ _) fun f g ↦ (matlisDual R E).map_comp g.op f.op).symm

variable {N N' : ModuleCat.{max v w} Aᵐᵒᵖ}

include hE in
/-- **Matlis duality is bijective on morphisms** between right modules of finite length over
`R`. -/
theorem bijective_matlisDualOpMap (hN : IsFiniteLength R N) (hN' : IsFiniteLength R N') :
    Function.Bijective
      (matlisDualOpMap R E : (N ⟶ N') → (matlisDualOpObj R E N' ⟶ matlisDualOpObj R E N)) := by
  let Y : ((isFiniteLength.{max v w} R).inverseImage
      (restrictScalars.{max v w} (algebraMap R Aᵐᵒᵖ))).FullSubcategory :=
    ⟨N, (isFiniteLength_inverseImage_restrictScalars_iff N).mpr hN⟩
  let Y' : ((isFiniteLength.{max v w} R).inverseImage
      (restrictScalars.{max v w} (algebraMap R Aᵐᵒᵖ))).FullSubcategory :=
    ⟨N', (isFiniteLength_inverseImage_restrictScalars_iff N').mpr hN'⟩
  have h := (matlisDuality hE (A := A)).fullyFaithfulInverse.map_bijective Y Y'
  refine ⟨fun g g' hg ↦ ?_, fun f ↦ ?_⟩
  · exact congrArg (fun k ↦ k.hom) (h.1 (a₁ := (ObjectProperty.homMk g : Y ⟶ Y'))
      (a₂ := ObjectProperty.homMk g') (Quiver.Hom.unop_inj (ObjectProperty.hom_ext _ hg)))
  · obtain ⟨k, hk⟩ := h.2 (ObjectProperty.homMk f).op
    exact ⟨k.hom, congrArg (fun k ↦ k.unop.hom) hk⟩

include hE in
/-- **Matlis duality reflects isomorphisms** of right modules of finite length over `R`. -/
theorem nonempty_iso_matlisDualOpObj_iff (hN : IsFiniteLength R N) (hN' : IsFiniteLength R N') :
    Nonempty (matlisDualOpObj R E N ≅ matlisDualOpObj R E N') ↔ Nonempty (N ≅ N') := by
  refine ⟨fun ⟨i⟩ ↦ ?_, fun ⟨i⟩ ↦ ⟨((matlisDualOp R E).mapIso i.op).symm⟩⟩
  let Q := (isFiniteLength.{max v w} R).inverseImage
    (restrictScalars.{max v w} (algebraMap R Aᵐᵒᵖ))
  let Y : Q.FullSubcategory := ⟨N, (isFiniteLength_inverseImage_restrictScalars_iff N).mpr hN⟩
  let Y' : Q.FullSubcategory := ⟨N', (isFiniteLength_inverseImage_restrictScalars_iff N').mpr hN'⟩
  let k := (matlisDuality hE (A := A)).fullyFaithfulInverse.preimageIso
    ((ObjectProperty.isoMk _ i).op : (matlisDuality hE).inverse.obj Y' ≅
      (matlisDuality hE).inverse.obj Y)
  exact ⟨(Q.ι.mapIso k).symm⟩

include hE in
/-- **Matlis duality reverses endomorphism rings**: for a right module `N` of finite length over
`R`, dualizing is a ring isomorphism `End(N)ᵐᵒᵖ ≃ End(D_R N)`. -/
noncomputable def matlisDualOpEndRingEquiv (hN : IsFiniteLength R N) :
    (End N)ᵐᵒᵖ ≃+* End (matlisDualOpObj R E N) :=
  RingEquiv.ofBijective
    ({ toFun f := End.of (matlisDualOpMap R E f.unop.asHom)
       map_one' := End.ext ((matlisDualOp R E).map_id _)
       map_mul' f g := End.ext ((matlisDualOp R E).map_comp g.unop.asHom.op f.unop.asHom.op)
       map_zero' := End.ext ((matlisDualOp R E).map_zero _ _)
       map_add' _ _ := End.ext (matlisDualOpMap_add R E _ _) } :
      (End N)ᵐᵒᵖ →+* End (matlisDualOpObj R E N))
    (End.homEquiv.symm.bijective.comp ((bijective_matlisDualOpMap hE hN hN).comp
      (End.homEquiv.bijective.comp MulOpposite.unop_bijective)))

@[simp]
theorem matlisDualOpEndRingEquiv_apply_asHom (hN : IsFiniteLength R N) (f : (End N)ᵐᵒᵖ) :
    (matlisDualOpEndRingEquiv hE hN f).asHom = matlisDualOpMap R E f.unop.asHom :=
  (rfl)

include hE in
/-- **Matlis duality preserves and reflects indecomposability** of right modules of finite length
over `R`. -/
theorem indecomposable_matlisDualOpObj_iff (hN : IsFiniteLength R N) :
    Indecomposable (matlisDualOpObj R E N) ↔ Indecomposable N :=
  (TauCeti.indecomposable_iff_of_bijective_of_map_comp (matlisDualOpMap R E)
    (bijective_matlisDualOpMap hE hN hN) ((matlisDualOp R E).map_id _)
    ((matlisDualOp R E).map_zero _ _) fun f g ↦ (matlisDualOp R E).map_comp g.op f.op).symm

end Consequences

end ModuleCat
