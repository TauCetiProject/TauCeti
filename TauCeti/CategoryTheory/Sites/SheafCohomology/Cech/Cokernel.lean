/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Ext.Basic
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Exact
public import TauCeti.CategoryTheory.Sites.SheafCohomology.LongExactSequence

/-!
# Čech complexes of an injective cokernel sequence

The chosen injective embedding of an abelian sheaf induces a left exact sequence of Čech
complexes, functorial in the sheaf and in refinements. First-cohomology vanishing on the finite
products of members makes it short exact, provided the tuple-indexed products are exact.
The cover index and coefficient universes are independent of the site's hom universe.
-/

public section
noncomputable section

open CategoryTheory Limits Opposite

universe b w' w v u

namespace TauCeti.CategoryTheory

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C] {J : GrothendieckTopology C}
  {ι : Type w} (U : ι → C)

section Core

variable [HasSheafify J AddCommGrpCat.{b}] [HasProducts.{w} AddCommGrpCat.{b}]

/-! ### The Čech complexes of an injective cokernel sequence -/

variable [EnoughInjectives (Sheaf J AddCommGrpCat.{b})]

/-- The sequence of Čech complexes `0 ⟶ Č(U, F) ⟶ Č(U, I) ⟶ Č(U, Q) ⟶ 0` of the chosen injective
cokernel sequence `0 ⟶ F ⟶ I ⟶ Q ⟶ 0` (`TauCeti.injectiveCokernelSequence`) for the family `U`.
It is short exact when `F` has no first cohomology on the finite products of members of `U`. -/
abbrev cechInjectiveCokernelSequence (F : Sheaf J AddCommGrpCat.{b}) :
    ShortComplex (CochainComplex AddCommGrpCat.{b} ℕ) :=
  -- this is `((injectiveCokernelSequence F).map (sheafToPresheaf _ _)).map (cechComplexFunctor U)`,
  -- restated so that its objects are syntactically the Čech complexes of `F`, `I` and `Q`
  ShortComplex.mk ((cechComplexFunctor U).map (Injective.ι F).hom)
    ((cechComplexFunctor U).map (cokernel.π (Injective.ι F)).hom)
    (((injectiveCokernelSequence F).map (sheafToPresheaf _ AddCommGrpCat.{b})).map
      (cechComplexFunctor U)).zero

/-- A morphism `F ⟶ G` induces a morphism of the sequences of Čech complexes of the chosen
injective cokernel sequences, through `TauCeti.injectiveCokernelSequenceMap`. -/
def cechInjectiveCokernelSequenceMap {F G : Sheaf J AddCommGrpCat.{b}} (f : F ⟶ G) :
    cechInjectiveCokernelSequence U F ⟶ cechInjectiveCokernelSequence U G :=
  (sheafToPresheaf J AddCommGrpCat.{b} ⋙ cechComplexFunctor U).mapShortComplex.map
    (injectiveCokernelSequenceMap f)

/-- On the first term, the map of Čech sequences is induced by the original morphism. -/
@[simp]
theorem cechInjectiveCokernelSequenceMap_τ₁ {F G : Sheaf J AddCommGrpCat.{b}} (f : F ⟶ G) :
    (cechInjectiveCokernelSequenceMap U f).τ₁ = (cechComplexFunctor U).map f.hom := by
  simp [cechInjectiveCokernelSequenceMap]

/-- On the injective term, the map of Čech sequences is induced by the chosen injective lift. -/
@[simp]
theorem cechInjectiveCokernelSequenceMap_τ₂ {F G : Sheaf J AddCommGrpCat.{b}} (f : F ⟶ G) :
    (cechInjectiveCokernelSequenceMap U f).τ₂ =
      (cechComplexFunctor U).map (injectiveCokernelSequenceMap f).τ₂.hom :=
  (rfl)

/-- On the quotient term, the map of Čech sequences is induced by the chosen quotient map. -/
@[simp]
theorem cechInjectiveCokernelSequenceMap_τ₃ {F G : Sheaf J AddCommGrpCat.{b}} (f : F ⟶ G) :
    (cechInjectiveCokernelSequenceMap U f).τ₃ =
      (cechComplexFunctor U).map (injectiveCokernelSequenceMap f).τ₃.hom :=
  (rfl)

/-- The sequence of Čech complexes of the chosen injective cokernel sequence is left exact: it is
exact at `Č(U, I)`. -/
theorem cechInjectiveCokernelSequence_exact (F : Sheaf J AddCommGrpCat.{b}) :
    (cechInjectiveCokernelSequence U F).Exact :=
  (injectiveCokernelSequence_shortExact F).exact.map_of_mono_of_preservesKernel
    (sheafToPresheaf _ AddCommGrpCat.{b} ⋙ cechComplexFunctor U) inferInstance inferInstance

/-- The sequence of Čech complexes of the chosen injective cokernel sequence is left exact: the
map `Č(U, F) ⟶ Č(U, I)` is a monomorphism. -/
instance mono_cechInjectiveCokernelSequence_f (F : Sheaf J AddCommGrpCat.{b}) :
    Mono (cechInjectiveCokernelSequence U F).f :=
  Functor.map_mono (sheafToPresheaf _ AddCommGrpCat.{b} ⋙ cechComplexFunctor U) (Injective.ι F)

/-- A morphism of families `U ⟶ V` induces a morphism from the sequence of Čech complexes of the
chosen injective cokernel sequence for `V` to that for `U`, through `cechComplexMap`. -/
def cechInjectiveCokernelSequenceRefinement {κ : Type w} (V : κ → C)
    (F : Sheaf J AddCommGrpCat.{b}) (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V) :
    cechInjectiveCokernelSequence V F ⟶ cechInjectiveCokernelSequence U F :=
  cechRefinementShortComplexHom U V
    ((injectiveCokernelSequence F).map (sheafToPresheaf J AddCommGrpCat.{b})) φ

/-- On the first term, the refinement map of Čech sequences is the refinement map of `F`. -/
@[simp]
theorem cechInjectiveCokernelSequenceRefinement_τ₁ {κ : Type w} (V : κ → C)
    (F : Sheaf J AddCommGrpCat.{b}) (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V) :
    (cechInjectiveCokernelSequenceRefinement U V F φ).τ₁ = cechComplexMap F.obj φ := by
  simp [cechInjectiveCokernelSequenceRefinement]

/-- On the injective term, the refinement map of Čech sequences is the refinement map of `I`. -/
@[simp]
theorem cechInjectiveCokernelSequenceRefinement_τ₂ {κ : Type w} (V : κ → C)
    (F : Sheaf J AddCommGrpCat.{b}) (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V) :
    (cechInjectiveCokernelSequenceRefinement U V F φ).τ₂ =
      cechComplexMap (Injective.under F).obj φ := by
  simp [cechInjectiveCokernelSequenceRefinement]

/-- On the quotient term, the refinement map of Čech sequences is the refinement map of `Q`. -/
@[simp]
theorem cechInjectiveCokernelSequenceRefinement_τ₃ {κ : Type w} (V : κ → C)
    (F : Sheaf J AddCommGrpCat.{b}) (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V) :
    (cechInjectiveCokernelSequenceRefinement U V F φ).τ₃ =
      cechComplexMap (cokernel (Injective.ι F)).obj φ := by
  simp [cechInjectiveCokernelSequenceRefinement]

end Core

variable [HasSheafify J AddCommGrpCat.{v}] [HasProducts.{w} AddCommGrpCat.{v}]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{v})]

/-- If `F` has no first cohomology on the finite products `U (a 0) × ⋯ × U (a m)` of members of
the family, the sections of `0 ⟶ F ⟶ I ⟶ Q ⟶ 0` on them are short exact, so the sequence of Čech
complexes `0 ⟶ Č(U, F) ⟶ Č(U, I) ⟶ Č(U, Q) ⟶ 0` is short exact. -/
theorem cechInjectiveCokernelSequence_shortExact
    [∀ n : ℕ, HasExactLimitsOfShape (Discrete (Fin (n + 1) → ι)) AddCommGrpCat.{v}]
    [HasExt.{w'} (Sheaf J AddCommGrpCat.{v})]
    {F : Sheaf J AddCommGrpCat.{v}}
    (hF : ∀ (m : ℕ) (a : Fin (m + 1) → ι), Subsingleton (F.H'.{w'} 1 (∏ᶜ fun j ↦ U (a j)))) :
    (cechInjectiveCokernelSequence U F).ShortExact :=
  shortExact_map_cechComplexFunctor U
    ((injectiveCokernelSequence F).map (sheafToPresheaf _ AddCommGrpCat.{v})) fun m a ↦
      _root_.CategoryTheory.Sheaf.H'.shortExact_map_sheafSections
        (injectiveCokernelSequence_shortExact F) _ (hF m a)

end TauCeti.CategoryTheory
