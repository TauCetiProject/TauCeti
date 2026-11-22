/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.SmallObject.Basic
public import TauCeti.Algebra.Homology.DerivedCategory.KInjective
public import TauCeti.Algebra.Homology.ModelCategory.MonoQuasiIso

import TauCeti.Algebra.Homology.HomologicalComplex.QuasiIso
import TauCeti.CategoryTheory.Abelian.GrothendieckCategory.SmallObjectArgument

/-!
# K-injective resolutions in Grothendieck abelian categories

Let `C` be a Grothendieck abelian category. Every morphism of unbounded cochain complexes in `C`
factors functorially as a monomorphic quasi-isomorphism followed by a morphism with the right
lifting property with respect to all monomorphic quasi-isomorphisms; these are the factorizations
of the injective model structure on unbounded complexes. Applied to the morphism from a complex
`K` to zero, this gives a monomorphic quasi-isomorphism from `K` to a K-injective complex of
injective objects, functorial in `K`. Hence `C` has K-injective resolutions
(`TauCeti.HasKInjectiveResolutions`), with no boundedness assumption. This applies to sheaves of
modules over a sheaf of rings on a small site, which form a Grothendieck abelian category.

## Main results

* `CochainComplex.llp_rlp_monomorphisms_inf_quasiIso`: a morphism has the left lifting property
  with respect to the morphisms which have the right lifting property with respect to the
  monomorphic quasi-isomorphisms if and only if it is a monomorphic quasi-isomorphism.
* `CochainComplex.exists_hasSmallObjectArgument_le_monomorphisms_inf_quasiIso_and_rlp_eq`: a
  family of monomorphic quasi-isomorphisms to which the small object argument applies, with the
  same right lifting property as all monomorphic quasi-isomorphisms.
* `CochainComplex.monoQuasiIsoMapFactorizationDataRlp`: the functorial factorization.
* `CochainComplex.injectiveReplacement` and `CochainComplex.ιInjectiveReplacement`: the resulting
  functorial K-injective replacement, with its natural monomorphic quasi-isomorphism. A morphism is
  a quasi-isomorphism exactly when its replacement is
  (`CochainComplex.quasiIso_injectiveReplacement_map_iff`).
* `TauCeti.hasKInjectiveResolutions_of_isGrothendieckAbelian`: Grothendieck abelian categories
  have K-injective resolutions.

## Implementation notes

The small object argument is applied to a `w`-small family of monomorphic quasi-isomorphisms
with the same right lifting property as all monomorphic quasi-isomorphisms
(`CochainComplex.exists_isSmall_le_monomorphisms_inf_quasiIso_and_rlp_eq`). Its relative cell
complexes are monomorphic quasi-isomorphisms because these are stable under coproducts, pushouts,
transfinite compositions and retracts. The argument follows the proof that Grothendieck abelian
categories have enough injectives in Mathlib's
`Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives`, by Joël Riou.

## References

* J. Lurie, *Higher Algebra*, Proposition 1.3.5.3.
* [Stacks: Theorem 079P](https://stacks.math.columbia.edu/tag/079P).
-/

public section

universe w v u

open CategoryTheory Limits MorphismProperty ZeroObject

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]

/-- There is a family of monomorphic quasi-isomorphisms of cochain complexes over a Grothendieck
abelian category to which the small object argument applies, and which has the same right lifting
property as all monomorphic quasi-isomorphisms. In the injective model structure, it is a family
of generating trivial cofibrations. -/
theorem exists_hasSmallObjectArgument_le_monomorphisms_inf_quasiIso_and_rlp_eq :
    ∃ I : MorphismProperty (CochainComplex C ℤ), HasSmallObjectArgument.{w} I ∧
      I ≤ monomorphisms _ ⊓ HomologicalComplex.quasiIso C (.up ℤ) ∧
        I.rlp = (monomorphisms _ ⊓ HomologicalComplex.quasiIso C (.up ℤ)).rlp := by
  obtain ⟨I, _, hI, hIrlp⟩ :=
    exists_isSmall_le_monomorphisms_inf_quasiIso_and_rlp_eq.{w} (C := C)
  exact ⟨I, IsGrothendieckAbelian.hasSmallObjectArgument_of_le_monomorphisms I
    fun _ _ _ hi ↦ (hI _ hi).1, hI, hIrlp⟩

/-- A morphism of cochain complexes over a Grothendieck abelian category has the left lifting
property with respect to all morphisms which have the right lifting property with respect to the
monomorphic quasi-isomorphisms if and only if it is a monomorphic quasi-isomorphism. -/
theorem llp_rlp_monomorphisms_inf_quasiIso :
    (monomorphisms (CochainComplex C ℤ) ⊓ HomologicalComplex.quasiIso C (.up ℤ)).rlp.llp =
      monomorphisms _ ⊓ HomologicalComplex.quasiIso C (.up ℤ) := by
  obtain ⟨I, _, hI, hIrlp⟩ :=
    exists_hasSmallObjectArgument_le_monomorphisms_inf_quasiIso_and_rlp_eq.{w} (C := C)
  refine le_antisymm ?_ (le_llp_rlp _)
  rw [← hIrlp, llp_rlp_of_hasSmallObjectArgument, retracts_le_iff, transfiniteCompositions_le_iff,
    pushouts_le_iff, coproducts_le_iff]
  exact hI

/-- Every morphism of cochain complexes over a Grothendieck abelian category factors functorially
as a monomorphic quasi-isomorphism followed by a morphism with the right lifting property with
respect to all monomorphic quasi-isomorphisms. -/
instance : HasFunctorialFactorization
    (monomorphisms (CochainComplex C ℤ) ⊓ HomologicalComplex.quasiIso C (.up ℤ))
    (monomorphisms _ ⊓ HomologicalComplex.quasiIso C (.up ℤ)).rlp := by
  obtain ⟨I, _, -, hIrlp⟩ :=
    exists_hasSmallObjectArgument_le_monomorphisms_inf_quasiIso_and_rlp_eq.{w} (C := C)
  rw [← hIrlp, ← llp_rlp_monomorphisms_inf_quasiIso.{w}, ← hIrlp]
  infer_instance

/-- A functorial factorization of a morphism of cochain complexes over a Grothendieck abelian
category as a monomorphic quasi-isomorphism followed by a morphism with the right lifting property
with respect to all monomorphic quasi-isomorphisms. -/
noncomputable abbrev monoQuasiIsoMapFactorizationDataRlp {X Y : CochainComplex C ℤ}
    (f : X ⟶ Y) :
    MapFactorizationData (monomorphisms _ ⊓ HomologicalComplex.quasiIso C (.up ℤ))
      (monomorphisms _ ⊓ HomologicalComplex.quasiIso C (.up ℤ)).rlp f :=
  (functorialFactorizationData _ _).factorizationData f

instance {X Y : CochainComplex C ℤ} (f : X ⟶ Y) :
    Mono (monoQuasiIsoMapFactorizationDataRlp f).i :=
  (monoQuasiIsoMapFactorizationDataRlp f).hi.1

instance {X Y : CochainComplex C ℤ} (f : X ⟶ Y) :
    QuasiIso (monoQuasiIsoMapFactorizationDataRlp f).i :=
  (monoQuasiIsoMapFactorizationDataRlp f).hi.2

/-- The middle object of the factorization of the morphism from a complex to zero is a
K-injective complex of injective objects. -/
private lemma injective_X_and_isKInjective_monoQuasiIsoMapFactorizationDataRlp_zero
    (K : CochainComplex C ℤ) :
    (∀ n, Injective ((monoQuasiIsoMapFactorizationDataRlp (0 : K ⟶ 0)).Z.X n)) ∧
      IsKInjective (monoQuasiIsoMapFactorizationDataRlp (0 : K ⟶ 0)).Z :=
  (rlp_monomorphisms_inf_quasiIso_iff_of_isZero _ (isZero_zero _)).1
    (monoQuasiIsoMapFactorizationDataRlp (0 : K ⟶ 0)).hp

instance (K : CochainComplex C ℤ) (n : ℤ) :
    Injective ((monoQuasiIsoMapFactorizationDataRlp (0 : K ⟶ 0)).Z.X n) :=
  (injective_X_and_isKInjective_monoQuasiIsoMapFactorizationDataRlp_zero K).1 n

instance (K : CochainComplex C ℤ) :
    IsKInjective (monoQuasiIsoMapFactorizationDataRlp (0 : K ⟶ 0)).Z :=
  (injective_X_and_isKInjective_monoQuasiIsoMapFactorizationDataRlp_zero K).2

/-- The morphism from a complex to zero, as a functor to the arrow category. -/
private noncomputable def arrowToZero : CochainComplex C ℤ ⥤ Arrow (CochainComplex C ℤ) where
  obj K := Arrow.mk (0 : K ⟶ 0)
  map f := Arrow.homMk f (𝟙 0)

variable (C) in
/-- The **functorial K-injective replacement** of unbounded complexes in a Grothendieck abelian
category: the middle object of the functorial factorization of the morphism from a complex to zero.
It is a K-injective complex of injective objects, receiving a monomorphic quasi-isomorphism
`CochainComplex.ιInjectiveReplacement C` from the complex. -/
noncomputable def injectiveReplacement : CochainComplex C ℤ ⥤ CochainComplex C ℤ :=
  arrowToZero ⋙ (functorialFactorizationData
    (monomorphisms (CochainComplex C ℤ) ⊓ HomologicalComplex.quasiIso C (.up ℤ))
    (monomorphisms _ ⊓ HomologicalComplex.quasiIso C (.up ℤ)).rlp).Z

variable (C) in
/-- The natural monomorphic quasi-isomorphism from a complex to its K-injective replacement. -/
noncomputable def ιInjectiveReplacement : 𝟭 (CochainComplex C ℤ) ⟶ injectiveReplacement C where
  app K := (monoQuasiIsoMapFactorizationDataRlp (0 : K ⟶ 0)).i
  naturality _ _ f := (functorialFactorizationData _ _).i.naturality (arrowToZero.map f)

/-- The replacement of a complex is the middle object of the factorization of the morphism from
it to zero. -/
private lemma injectiveReplacement_obj (K : CochainComplex C ℤ) :
    (injectiveReplacement C).obj K = (monoQuasiIsoMapFactorizationDataRlp (0 : K ⟶ 0)).Z :=
  rfl

instance (K : CochainComplex C ℤ) : ((injectiveReplacement C).obj K).IsKInjective := by
  rw [injectiveReplacement_obj]
  infer_instance

instance (K : CochainComplex C ℤ) (n : ℤ) : Injective (((injectiveReplacement C).obj K).X n) := by
  rw [injectiveReplacement_obj]
  infer_instance

instance (K : CochainComplex C ℤ) : Mono ((ιInjectiveReplacement C).app K) :=
  inferInstanceAs (Mono (monoQuasiIsoMapFactorizationDataRlp (0 : K ⟶ 0)).i)

instance (K : CochainComplex C ℤ) : QuasiIso ((ιInjectiveReplacement C).app K) :=
  inferInstanceAs (QuasiIso (monoQuasiIsoMapFactorizationDataRlp (0 : K ⟶ 0)).i)

/-- The replacement of a morphism of complexes is a quasi-isomorphism exactly when the morphism
is. -/
theorem quasiIso_injectiveReplacement_map_iff {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    QuasiIso ((injectiveReplacement C).map f) ↔ QuasiIso f := by
  rw [← quasiIso_iff_comp_left ((ιInjectiveReplacement C).app K),
    ← (ιInjectiveReplacement C).naturality f, Functor.id_map,
    quasiIso_iff_comp_right f ((ιInjectiveReplacement C).app L)]

end CochainComplex

namespace TauCeti

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]

/-- A Grothendieck abelian category has K-injective resolutions: every unbounded cochain complex
admits a quasi-isomorphism into a K-injective complex. -/
@[stacks 079P]
instance hasKInjectiveResolutions_of_isGrothendieckAbelian : HasKInjectiveResolutions C where
  exists_quasiIso_isKInjective K :=
    ⟨_, (CochainComplex.monoQuasiIsoMapFactorizationDataRlp (0 : K ⟶ 0)).i, inferInstance,
      inferInstance⟩

end TauCeti
