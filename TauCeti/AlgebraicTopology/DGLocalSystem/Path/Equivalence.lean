/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Localization.Equivalence
public import Mathlib.CategoryTheory.Localization.LocalizerMorphism
public import TauCeti.AlgebraicTopology.DGLocalSystem.Path.CompositeChange
public import TauCeti.AlgebraicTopology.DGLocalSystem.Path.Unit
public import TauCeti.CategoryTheory.Localization.LocalizerMorphism

/-!
# Changing the basepoint is an equivalence of derived categories

A DG local system at a point `a` of a space `B` is a right DG module over the chain algebra
`C_*(Ω_a B)` of Moore loops, and tensoring with the chain bimodule `C_*(P_{a→b} B)` of Moore paths
from `a` to `b` changes its basepoint to `b`. This functor preserves quasi-isomorphisms
(`TauCeti.isQuasiIso_tensorBimoduleMap_pathChainBimodule`), so it is a morphism of localizers
(`TauCeti.tensorPathChainLocalizerMorphism`) and induces a functor between the localizations of
the two categories of DG local systems at their quasi-isomorphisms, the derived categories of DG
local systems at `a` and at `b`. Mathlib's `CategoryTheory.LocalizerMorphism.localizedFunctor`
is this induced functor, for any choice of localization functors.

This file shows that these induced functors compose like the path spaces they come from. With
`D_a` a localization at `a`:

* changing the basepoint along the paths from `a` to `b` and then along those from `b` to `c` is
  isomorphic, on derived categories, to changing it along the paths from `a` to `c`, as soon as
  `a` and `b` are joined by a Moore path (`TauCeti.tensorPathChainLocalizedFunctorCompIso`). The
  isomorphism is induced by the natural quasi-isomorphism `(m ⊗ σ) ⊗ τ ↦ m ⊗ (σ ⋆ τ)` that
  concatenates the paths (`TauCeti.tensorPathChainConcatNatTrans`);
* changing the basepoint along the paths from `a` to itself is isomorphic to the identity of
  `D_a` (`TauCeti.tensorPathChainLocalizedFunctorSelfIso`), through
  `TauCeti.tensorPathChainOneNatIso`.

So if `a` and `b` lie in the same path component of `B`, the changes of basepoint along the paths
from `a` to `b` and from `b` to `a` are mutually inverse equivalences of derived categories
(`TauCeti.tensorPathChainLocalizedEquivalence`), and the localizer morphism is a localized
equivalence (`TauCeti.isLocalizedEquivalence_tensorPathChainLocalizerMorphism`). The comparison
does not conjugate by a single path, which would not be a map of DG algebras: it uses all the
paths from `a` to `b` at once, and the quasi-isomorphisms come from concatenation and its
reverse.

The categories of DG local systems are taken with carriers in a universe containing those of `B`
and the ground ring, so that changing the basepoint is a functor from such a category to another
one of the same kind. The localization functors are arbitrary, so the statements apply to every
model of the derived categories, for instance `MorphismProperty.Localization`.

## Main definitions

* `TauCeti.tensorPathChainLocalizerMorphism`: changing the basepoint, as a morphism of localizers
  for the quasi-isomorphisms.
* `TauCeti.tensorPathChainLocalizedFunctorCompIso`: the derived changes of basepoint compose.
* `TauCeti.tensorPathChainLocalizedFunctorSelfIso`: the derived change of basepoint along the
  paths from a point to itself is the identity.
* `TauCeti.tensorPathChainLocalizedEquivalence`: changing the basepoint within a path component
  is an equivalence of derived categories.

## Main results

* `TauCeti.tensorPathChainLocalizedFunctorCompIso_hom_app`,
  `TauCeti.tensorPathChainLocalizedFunctorSelfIso_hom_app`: on the image of a DG local system,
  these isomorphisms are the images of concatenation and of `M ⊗ C_*(P_{a→a} B) ≅ M`.
* `TauCeti.tensorPathChainLocalizedEquivalence_counitIso_hom_app`: on the image of a DG local
  system at `b`, the counit of the equivalence is the image of concatenation followed by
  `M ⊗ C_*(P_{b→b} B) ≅ M`.
* `TauCeti.isLocalizedEquivalence_tensorPathChainLocalizerMorphism`: changing the basepoint
  within a path component is a localized equivalence.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapter 2 and §7.1.
* B. Keller, *Deriving DG categories*, Ann. Sci. École Norm. Sup. (4) 27 (1994), Sections 4
  and 6.
-/

public noncomputable section

open CategoryTheory Localization

namespace TauCeti

open BalancedTensorProduct DGRightModuleCat

universe u w v

variable {B : Type u} [TopologicalSpace B] {R : Type w} [CommRing R]

section LocalizerMorphism

variable (B R)

-- The body is exposed so that the objects and morphisms of its functor remain those of the
-- tensor product, as consumers of the induced functors on localizations need.
/-- **Changing the basepoint as a morphism of localizers**: tensoring with the chain bimodule
`C_*(P_{a→b} B)` of Moore paths from `a` to `b` sends quasi-isomorphisms of DG local systems at `a`
to quasi-isomorphisms of DG local systems at `b`. -/
@[expose]
def tensorPathChainLocalizerMorphism (a b : B) :
    LocalizerMorphism
      (quasiIsos.{w, max u w, max u v w} (loopChain_isDGAlgebra B a R))
      (quasiIsos.{w, max u w, max u v w} (loopChain_isDGAlgebra B b R)) where
  functor :=
    tensorBimoduleFunctor.{w, max u w, max u w, max u v w, max u w}.flip.obj
      (pathChainBimodule B a b R)
  map _ _ _ hf := (quasiIsos_iff _).2
    (isQuasiIso_tensorBimoduleMap_pathChainBimodule ((quasiIsos_iff _).1 hf))

/-- The functor of `TauCeti.tensorPathChainLocalizerMorphism` is the change of basepoint. -/
@[simp]
theorem tensorPathChainLocalizerMorphism_functor (a b : B) :
    (tensorPathChainLocalizerMorphism.{u, w, v} B R a b).functor =
      tensorBimoduleFunctor.flip.obj (pathChainBimodule B a b R) :=
  (rfl)

end LocalizerMorphism

section Localization

variable {a b c : B}
  {Da : Type*} {Db : Type*} {Dc : Type*} [Category* Da] [Category* Db] [Category* Dc]
  (La : DGRightModuleCat.{w, max u w, max u v w} (loopChain_isDGAlgebra B a R) ⥤ Da)
  [La.IsLocalization (quasiIsos _)]
  (Lb : DGRightModuleCat.{w, max u w, max u v w} (loopChain_isDGAlgebra B b R) ⥤ Db)
  [Lb.IsLocalization (quasiIsos _)]
  (Lc : DGRightModuleCat.{w, max u w, max u v w} (loopChain_isDGAlgebra B c R) ⥤ Dc)
  [Lc.IsLocalization (quasiIsos _)]

/-- On localizations, the composite change of basepoint becomes an isomorphism when `a` and `b`
are joined by a Moore path. -/
theorem isIso_whiskerRight_tensorPathChainConcatNatTrans (h : Nonempty (MoorePathBetween B a b)) :
    IsIso (Functor.whiskerRight (tensorPathChainConcatNatTrans.{u, w, v} B R a b c) Lc) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  rw [Functor.whiskerRight_app, tensorPathChainConcatNatTrans_app]
  exact Localization.inverts Lc _ _ ((quasiIsos_iff _).2 (isQuasiIso_tensorPathChainConcat M h))

/-- **The derived changes of basepoint compose**: if `a` and `b` are joined by a Moore path, the
functor induced on derived categories by changing the basepoint along the paths from `a` to `b`
and then along the paths from `b` to `c` is isomorphic to the one induced by changing it along
the paths from `a` to `c`. The isomorphism is induced by concatenation of paths
(`TauCeti.tensorPathChainConcatNatTrans`). -/
def tensorPathChainLocalizedFunctorCompIso (h : Nonempty (MoorePathBetween B a b)) :
    (tensorPathChainLocalizerMorphism.{u, w, v} B R a b).localizedFunctor La Lb ⋙
        (tensorPathChainLocalizerMorphism.{u, w, v} B R b c).localizedFunctor Lb Lc ≅
      (tensorPathChainLocalizerMorphism.{u, w, v} B R a c).localizedFunctor La Lc :=
  haveI := isIso_whiskerRight_tensorPathChainConcatNatTrans.{u, w, v} Lc h
  liftNatIso La (quasiIsos _)
    (((tensorPathChainLocalizerMorphism.{u, w, v} B R a b).functor ⋙
      (tensorPathChainLocalizerMorphism.{u, w, v} B R b c).functor) ⋙ Lc)
    ((tensorPathChainLocalizerMorphism.{u, w, v} B R a c).functor ⋙ Lc) _ _
    (asIso (Functor.whiskerRight (tensorPathChainConcatNatTrans.{u, w, v} B R a b c) Lc) :)

/-- On the image of a DG local system `M`, the isomorphism
`TauCeti.tensorPathChainLocalizedFunctorCompIso` is the image under `Lc` of the composite change
of basepoint `(M ⊗ C_*(P_{a→b} B)) ⊗ C_*(P_{b→c} B) ⟶ M ⊗ C_*(P_{a→c} B)`, up to the
identifications of the induced functors on `La.obj M`. -/
theorem tensorPathChainLocalizedFunctorCompIso_hom_app (h : Nonempty (MoorePathBetween B a b))
    (M : DGRightModuleCat.{w, max u w, max u v w} (loopChain_isDGAlgebra B a R)) :
    (tensorPathChainLocalizedFunctorCompIso.{u, w, v} La Lb Lc h).hom.app (La.obj M) =
      (Lifting.iso La (quasiIsos _)
          (((tensorPathChainLocalizerMorphism.{u, w, v} B R a b).functor ⋙
            (tensorPathChainLocalizerMorphism.{u, w, v} B R b c).functor) ⋙ Lc)
          ((tensorPathChainLocalizerMorphism.{u, w, v} B R a b).localizedFunctor La Lb ⋙
            (tensorPathChainLocalizerMorphism.{u, w, v} B R b c).localizedFunctor
              Lb Lc)).hom.app M ≫
        Lc.map (tensorPathChainConcat M b c) ≫
        (Lifting.iso La (quasiIsos _)
          ((tensorPathChainLocalizerMorphism.{u, w, v} B R a c).functor ⋙ Lc)
          ((tensorPathChainLocalizerMorphism.{u, w, v} B R a c).localizedFunctor
            La Lc)).inv.app M := by
  refine (liftNatTrans_app _ _ _ _ _ _ _ M).trans ?_
  rw [asIso_hom, Functor.whiskerRight_app, tensorPathChainConcatNatTrans_app]
  rfl

/-- The change of basepoint along the paths from `a` to itself, followed by `La`, is isomorphic
to `La`, through `TauCeti.tensorPathChainOneNatIso`. -/
def tensorPathChainSelfCompIso :
    (tensorPathChainLocalizerMorphism.{u, w, v} B R a a).functor ⋙ La ≅ La :=
  Functor.isoWhiskerRight (tensorPathChainOneNatIso.{u, w, v} B a R) La ≪≫ Functor.leftUnitor La

omit [La.IsLocalization (quasiIsos _)] in
/-- The components of `TauCeti.tensorPathChainSelfCompIso` are the images under `La` of
`M ⊗ C_*(P_{a→a} B) ≅ M`. -/
@[simp]
theorem tensorPathChainSelfCompIso_hom_app
    (M : DGRightModuleCat.{w, max u w, max u v w} (loopChain_isDGAlgebra B a R)) :
    (tensorPathChainSelfCompIso.{u, w, v} La).hom.app M =
      La.map (tensorPathChainOneIso.{u, w, v} B a R M).hom := by
  rw [← tensorPathChainOneNatIso_app, Iso.app_hom]
  exact Category.comp_id _

/-- **The derived change of basepoint along the paths from a point to itself is the identity**:
the functor it induces on the derived category of DG local systems at `a` is isomorphic to the
identity, through `m ⊗ c ↦ m · ρ(c)` (`TauCeti.tensorPathChainOneNatIso`). -/
def tensorPathChainLocalizedFunctorSelfIso :
    (tensorPathChainLocalizerMorphism.{u, w, v} B R a a).localizedFunctor La La ≅ 𝟭 Da :=
  liftNatIso La (quasiIsos _) ((tensorPathChainLocalizerMorphism.{u, w, v} B R a a).functor ⋙ La)
    La _ _ (tensorPathChainSelfCompIso.{u, w, v} La)

/-- On the image of a DG local system `M`, the isomorphism
`TauCeti.tensorPathChainLocalizedFunctorSelfIso` is the image under `La` of
`M ⊗ C_*(P_{a→a} B) ≅ M`, up to the identification of the induced functor on `La.obj M`. -/
theorem tensorPathChainLocalizedFunctorSelfIso_hom_app
    (M : DGRightModuleCat.{w, max u w, max u v w} (loopChain_isDGAlgebra B a R)) :
    (tensorPathChainLocalizedFunctorSelfIso.{u, w, v} La).hom.app (La.obj M) =
      (Lifting.iso La (quasiIsos _)
          ((tensorPathChainLocalizerMorphism.{u, w, v} B R a a).functor ⋙ La)
          ((tensorPathChainLocalizerMorphism.{u, w, v} B R a a).localizedFunctor
            La La)).hom.app M ≫
        La.map (tensorPathChainOneIso.{u, w, v} B a R M).hom := by
  refine (liftNatTrans_app _ _ _ _ _ _ _ _).trans ?_
  rw [tensorPathChainSelfCompIso_hom_app]
  exact congrArg _ (Category.comp_id _)

/-- The change of basepoint along `a → b` and back along `b → a`, followed by `La`, is
isomorphic to `La` when `a` and `b` are joined by a Moore path. -/
def tensorPathChainRoundTripIso (h : Nonempty (MoorePathBetween B a b)) :
    (tensorPathChainLocalizerMorphism.{u, w, v} B R a b).functor ⋙
        ((tensorPathChainLocalizerMorphism.{u, w, v} B R b a).functor ⋙ La) ≅ La :=
  haveI := isIso_whiskerRight_tensorPathChainConcatNatTrans.{u, w, v} (c := a) La h
  (Functor.associator _ _ _).symm ≪≫
    (asIso (Functor.whiskerRight (tensorPathChainConcatNatTrans.{u, w, v} B R a b a) La) :) ≪≫
    tensorPathChainSelfCompIso.{u, w, v} La

/-- The components of `TauCeti.tensorPathChainRoundTripIso` are the images under `La` of the
composite change of basepoint `(M ⊗ C_*(P_{a→b} B)) ⊗ C_*(P_{b→a} B) ⟶ M ⊗ C_*(P_{a→a} B)`
followed by `M ⊗ C_*(P_{a→a} B) ≅ M`. -/
@[simp]
theorem tensorPathChainRoundTripIso_hom_app (h : Nonempty (MoorePathBetween B a b))
    (M : DGRightModuleCat.{w, max u w, max u v w} (loopChain_isDGAlgebra B a R)) :
    (tensorPathChainRoundTripIso.{u, w, v} La h).hom.app M =
      La.map (tensorPathChainConcat M b a) ≫
        La.map (tensorPathChainOneIso.{u, w, v} B a R M).hom := by
  -- `tensorPathChainRoundTripIso` ascribes the whiskered concatenation iso a source written with
  -- `tensorPathChainLocalizerMorphism`, which agrees with the source of `asIso` only up to
  -- unfolding. After unfolding, `simp only [tensorPathChainRoundTripIso, Iso.trans_hom]` sees an
  -- ill-typed `Iso.trans` and does not rewrite past it, so `change` states the unfolded components.
  -- For the same reason, the two sides left after `rw` differ in hidden implicit arguments that
  -- agree only up to unfolding, which the closing `rfl` checks.
  change 𝟙 _ ≫ La.map ((tensorPathChainConcatNatTrans.{u, w, v} B R a b a).app M) ≫
    (tensorPathChainSelfCompIso.{u, w, v} La).hom.app M = _
  rw [Category.id_comp, tensorPathChainConcatNatTrans_app, tensorPathChainSelfCompIso_hom_app]
  rfl

-- The body is exposed so that the counit can be described on the images of DG local systems.
/-- **Changing the basepoint is an equivalence of derived categories.** If `a` and `b` are joined
by a Moore path, the functors induced on derived categories by tensoring with the path chain
bimodules `C_*(P_{a→b} B)` and `C_*(P_{b→a} B)` are mutually inverse equivalences. The counit
comes from concatenation of paths, `M ⊗ C_*(P_{b→a} B) ⊗ C_*(P_{a→b} B) → M ⊗ C_*(P_{b→b} B)`,
followed by `M ⊗ C_*(P_{b→b} B) ≅ M`
(`TauCeti.tensorPathChainLocalizedEquivalence_counitIso_hom_app`). The unit is built from the
same maps at `a`, adjusted so that the equivalence is adjoint. -/
@[expose]
def tensorPathChainLocalizedEquivalence (h : Nonempty (MoorePathBetween B a b)) : Da ≌ Db :=
  Localization.equivalence La (quasiIsos _) Lb (quasiIsos _)
    ((tensorPathChainLocalizerMorphism.{u, w, v} B R a b).functor ⋙ Lb)
    ((tensorPathChainLocalizerMorphism.{u, w, v} B R a b).localizedFunctor La Lb)
    ((tensorPathChainLocalizerMorphism.{u, w, v} B R b a).functor ⋙ La)
    ((tensorPathChainLocalizerMorphism.{u, w, v} B R b a).localizedFunctor Lb La)
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (CatCommSq.iso _ Lb La _).symm ≪≫
        tensorPathChainRoundTripIso.{u, w, v} La h)
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (CatCommSq.iso _ La Lb _).symm ≪≫
        tensorPathChainRoundTripIso.{u, w, v} Lb (h.map MoorePathBetween.symm))

/-- The functor of `TauCeti.tensorPathChainLocalizedEquivalence` is the change of basepoint along
the paths from `a` to `b`, induced on derived categories. -/
@[simp]
theorem tensorPathChainLocalizedEquivalence_functor (h : Nonempty (MoorePathBetween B a b)) :
    (tensorPathChainLocalizedEquivalence.{u, w, v} La Lb h).functor =
      (tensorPathChainLocalizerMorphism.{u, w, v} B R a b).localizedFunctor La Lb :=
  (rfl)

/-- The inverse of `TauCeti.tensorPathChainLocalizedEquivalence` is the change of basepoint along
the paths from `b` to `a`, induced on derived categories. -/
@[simp]
theorem tensorPathChainLocalizedEquivalence_inverse (h : Nonempty (MoorePathBetween B a b)) :
    (tensorPathChainLocalizedEquivalence.{u, w, v} La Lb h).inverse =
      (tensorPathChainLocalizerMorphism.{u, w, v} B R b a).localizedFunctor Lb La :=
  (rfl)

variable (B R) in
/-- **Changing the basepoint within a path component is a localized equivalence**: if `a` and `b`
are joined by a Moore path, tensoring with `C_*(P_{a→b} B)` induces an equivalence between the
localizations of DG local systems at `a` and at `b` at their quasi-isomorphisms. -/
theorem isLocalizedEquivalence_tensorPathChainLocalizerMorphism
    (h : Nonempty (MoorePathBetween B a b)) :
    (tensorPathChainLocalizerMorphism.{u, w, v} B R a b).IsLocalizedEquivalence :=
  ⟨(tensorPathChainLocalizedEquivalence.{u, w, v} _ _ h).isEquivalence_functor⟩

/-- On the image of a DG local system `M` at `b`, the counit of
`TauCeti.tensorPathChainLocalizedEquivalence` is the image under `Lb` of concatenation followed by
`M ⊗ C_*(P_{b→b} B) ≅ M` (`TauCeti.tensorPathChainRoundTripIso`), up to the identifications of
the induced functors on `Lb.obj M`. -/
theorem tensorPathChainLocalizedEquivalence_counitIso_hom_app
    (h : Nonempty (MoorePathBetween B a b))
    (M : DGRightModuleCat.{w, max u w, max u v w} (loopChain_isDGAlgebra B b R)) :
    (tensorPathChainLocalizedEquivalence.{u, w, v} La Lb h).counitIso.hom.app (Lb.obj M) =
      (Lifting.iso Lb (quasiIsos _)
          (((tensorPathChainLocalizerMorphism.{u, w, v} B R b a).functor ⋙ La) ⋙
            (tensorPathChainLocalizerMorphism.{u, w, v} B R a b).localizedFunctor La Lb)
          ((tensorPathChainLocalizerMorphism.{u, w, v} B R b a).localizedFunctor Lb La ⋙
            (tensorPathChainLocalizerMorphism.{u, w, v} B R a b).localizedFunctor
              La Lb)).hom.app M ≫
        (CatCommSq.iso (tensorPathChainLocalizerMorphism.{u, w, v} B R a b).functor La Lb
          ((tensorPathChainLocalizerMorphism.{u, w, v} B R a b).localizedFunctor La Lb)).inv.app
            ((tensorPathChainLocalizerMorphism.{u, w, v} B R b a).functor.obj M) ≫
        (tensorPathChainRoundTripIso.{u, w, v} Lb (h.map MoorePathBetween.symm)).hom.app M := by
  dsimp only [tensorPathChainLocalizedEquivalence]
  rw [← Iso.app_hom, equivalence_counitIso_app]
  simp only [Iso.trans_hom, Iso.app_hom, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.symm_hom, Category.id_comp]
  rfl

end Localization

end TauCeti
