/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Ext.Basic
public import TauCeti.CategoryTheory.Sites.SheafCohomology.FreeYoneda
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Terminal
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.Flasque
public import Mathlib.Topology.Sheaves.Skyscraper
import TauCeti.CategoryTheory.Sites.SheafCohomology.LongExactSequence

/-!
# Flasque sheaves are acyclic

A sheaf of abelian groups on a topological space is flasque when all of its restriction maps are
surjective. This file proves that a flasque sheaf has no higher cohomology.

## Main declarations

* `TauCeti.Topology.isFlasque_of_injective`: an injective object in the category of abelian
  sheaves is flasque;
* `TauCeti.Topology.subsingleton_H'_succ_of_isFlasque`: a flasque sheaf has vanishing
  cohomology in every positive degree over every open subset;
* `TauCeti.Topology.subsingleton_H_succ_of_isFlasque`: the same statement for the cohomology
  of the whole space;
* `TauCeti.Topology.isFlasque_skyscraperSheaf`: skyscraper sheaves are flasque, and hence acyclic;
* `TopCat.Sheaf.IsFlasque.epi_cokernel_π_app` and `TopCat.Sheaf.IsFlasque.exact_cokernel_π_app`:
  if `0 ⟶ A ⟶ B ⟶ C` is exact with `A` and `B` flasque, then taking sections over an open `U`
  gives an exact sequence `B(U) ⟶ C(U) ⟶ (coker (B ⟶ C))(U) ⟶ 0`.

The proof is the classical dimension shift. Embedding a flasque sheaf `F` in an injective sheaf
`I` gives a short exact sequence `0 ⟶ F ⟶ I ⟶ Q ⟶ 0`, and the covariant long exact sequence of
`Ext` presents `Hⁿ⁺¹(U, F)` as a quotient of `Hⁿ(U, Q)`. In degree zero, the sections of `Q` over
`U` lift to sections of `I` because `F` is flasque, so the quotient vanishes; in higher degrees
`Q` is again flasque, because `I` is, and induction applies. That `I` is flasque is the point at
which `TauCeti/CategoryTheory/Sites/SheafCohomology/FreeYoneda.lean` enters: an inclusion of open
subsets induces a monomorphism of the free abelian sheaves they generate, and `Hom(-, I)` turns it
into the restriction map of `I`.

This advances `TauCetiRoadmap/JacobianChallenge/README.md`, Layer B, "coherent sheaves and
cohomology `Hⁱ(X, ℱ)`: acyclicity of affines, …, vanishing above dimension": it is the first
acyclicity theorem of the lane, and the acyclic skyscraper sheaves are the coefficients in which
the Riemann-Roch induction over the points of a divisor reads the additivity of
`TauCeti/AlgebraicGeometry/Cohomology/EulerCharacteristic.lean`.

No formalization is vendored: flasqueness, the surjectivity of sections out of a flasque
subsheaf, the stability of flasqueness under quotients and the flasqueness of skyscraper sheaves
are Mathlib's `Mathlib/Topology/Sheaves/Flasque.lean`, and the long exact sequence is Mathlib's
`CategoryTheory.Abelian.Ext.covariant_sequence_exact₁`.

## References

* R. Hartshorne, *Algebraic Geometry*, III.2.4–2.5.
* The Stacks Project, tag 09SY, Lemma 20.12.3, *Flasque sheaves*.
-/

public section

open CategoryTheory Limits Opposite TopologicalSpace
open TauCeti.CategoryTheory (freeYonedaSheafFunctor freeYonedaSheafSectionsEquiv sheafH'_eq
  freeYonedaSheafSectionsEquiv_naturality_left freeYonedaSheafSectionsEquiv_naturality_right)

universe u

namespace TauCeti

namespace Topology

variable {X : TopCat.{u}}

noncomputable section

/-- An injective object in the category of sheaves of abelian groups is flasque. -/
instance isFlasque_of_injective
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) [Injective F] :
    TopCat.Presheaf.IsFlasque F.obj where
  -- Given `s : I(V)` and `V ≤ U`, represent `s` by `ℤ_V ⟶ I`, extend it along the
  -- monomorphism `ℤ_V ⟶ ℤ_U` using injectivity, and translate the extension back to a section.
  epi {U V} i := by
    rw [AddCommGrpCat.epi_iff_surjective]
    intro s
    refine ⟨freeYonedaSheafSectionsEquiv _ U.unop F
      (Injective.factorThru ((freeYonedaSheafSectionsEquiv _ V.unop F).symm s)
        ((freeYonedaSheafFunctor (Opens.grothendieckTopology X)).map i.unop)), ?_⟩
    have h := freeYonedaSheafSectionsEquiv_naturality_left
      (Opens.grothendieckTopology X) i.unop F
      (Injective.factorThru ((freeYonedaSheafSectionsEquiv _ V.unop F).symm s)
        ((freeYonedaSheafFunctor (Opens.grothendieckTopology X)).map i.unop))
    rw [Injective.comp_factorThru, AddEquiv.apply_symm_apply] at h
    exact h.symm

/-- The dimension-shifting induction: a flasque sheaf has no cohomology in positive degrees over
any open subset. -/
private lemma subsingleton_H'_succ_of_isFlasque_aux (n : ℕ) :
    ∀ (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}),
      TopCat.Presheaf.IsFlasque F.obj → ∀ U : Opens X,
      Subsingleton (_root_.CategoryTheory.Sheaf.H'.{u} F (n + 1) U) := by
  -- the injective sheaf `I` in `0 ⟶ F ⟶ I ⟶ Q ⟶ 0` has no higher cohomology
  have hI (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (m : ℕ) (U : Opens X) :
      Subsingleton (_root_.CategoryTheory.Sheaf.H'.{u} (Injective.under F) (m + 1) U) := by
    rw [sheafH'_eq]
    exact Abelian.Ext.subsingleton_of_injective _ _ m
  induction n with
  | zero =>
    intro F hF U
    have hS := injectiveCokernelSequence_shortExact F
    have : TopCat.Presheaf.IsFlasque (injectiveCokernelSequence F).X₁.obj := hF
    have : TopCat.Presheaf.IsFlasque (injectiveCokernelSequence F).X₂.obj :=
      isFlasque_of_injective _
    -- sections of `Q` lift to `I`, because `F` is flasque
    have hepi : Epi ((injectiveCokernelSequence F).g.hom.app (op U)) :=
      TopCat.Sheaf.IsFlasque.epi_of_shortExact hS
    exact Sheaf.H'.subsingleton_X₁_one hS U ((AddCommGrpCat.epi_iff_surjective _).1 hepi)
      (hI F 0 U)
  | succ n ih =>
    intro F hF U
    have hS := injectiveCokernelSequence_shortExact F
    have : TopCat.Presheaf.IsFlasque (injectiveCokernelSequence F).X₁.obj := hF
    have : TopCat.Presheaf.IsFlasque (injectiveCokernelSequence F).X₂.obj :=
      isFlasque_of_injective _
    -- `Q` is flasque, as a quotient of flasque sheaves
    exact Sheaf.H'.subsingleton_X₁ hS U (n + 1)
      (ih _ (TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂ hS) U) (hI F (n + 1) U)

/-- A flasque sheaf of abelian groups has vanishing cohomology in every positive degree over
every open subset. -/
instance subsingleton_H'_succ_of_isFlasque
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    [TopCat.Presheaf.IsFlasque F.obj] (n : ℕ) (U : Opens X) :
    Subsingleton (_root_.CategoryTheory.Sheaf.H'.{u} F (n + 1) U) :=
  subsingleton_H'_succ_of_isFlasque_aux n F inferInstance U

/-- A flasque sheaf of abelian groups has vanishing cohomology in every positive degree. -/
instance subsingleton_H_succ_of_isFlasque
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    [TopCat.Presheaf.IsFlasque F.obj] (n : ℕ) :
    Subsingleton (_root_.CategoryTheory.Sheaf.H.{u} F (n + 1)) := by
  have := subsingleton_H'_succ_of_isFlasque F n (⊤ : Opens X)
  exact Function.Injective.subsingleton
    (f := ConcreteCategory.hom
      (F.cohomologyPresheafObjIsoH (n + 1) isTerminalTop).inv)
    ((ConcreteCategory.bijective_of_isIso _).injective)

/-- A skyscraper sheaf of abelian groups is flasque. -/
instance isFlasque_skyscraperSheaf (p₀ : X) (A : AddCommGrpCat.{u})
    [(U : Opens X) → Decidable (p₀ ∈ U)] :
    TopCat.Presheaf.IsFlasque (skyscraperSheaf p₀ A).obj :=
  isFlasque_skyscraperSheaf_of_hasZeroObject p₀ A

end

end Topology

end TauCeti

namespace TopCat.Presheaf.IsFlasque

/-- A zero presheaf is flasque: each of its restriction maps lands in a zero object. -/
theorem of_isZero {C : Type*} [Category* C] [HasZeroObject C] {X : TopCat.{u}}
    {F : Presheaf C X} (h : IsZero F) : IsFlasque F :=
  ⟨fun _ ↦ (h.obj _).epi _⟩

end TopCat.Presheaf.IsFlasque

namespace TopCat.Sheaf.IsFlasque

variable {X : TopCat.{u}}
  {E : ShortComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})}

/-- If `0 ⟶ A ⟶ B ⟶ C` is an exact sequence of sheaves of abelian groups with `A` and `B` flasque,
then every section of the cokernel of `B ⟶ C` lifts to a section of `C`. -/
theorem epi_cokernel_π_app (hE : E.Exact) [Mono E.f] [Presheaf.IsFlasque E.X₁.obj]
    [Presheaf.IsFlasque E.X₂.obj] (U : Opens X) : Epi ((cokernel.π E.g).hom.app (op U)) :=
  have := of_shortExact_of_isFlasque₁₂ hE.shortExact_factorThruImage
  epi_of_shortExact (ShortComplex.shortExact_image_ι_cokernel_π E.g)

/-- If `0 ⟶ A ⟶ B ⟶ C` is an exact sequence of sheaves of abelian groups with `A` flasque, then a
section of `C` maps to zero in the cokernel of `B ⟶ C` exactly when it comes from a section of
`B`. -/
theorem exact_cokernel_π_app (hE : E.Exact) [Mono E.f] [Presheaf.IsFlasque E.X₁.obj]
    (U : Opens X) :
    (ShortComplex.mk (E.g.hom.app (op U)) ((cokernel.π E.g).hom.app (op U)) (by
      simp [← NatTrans.comp_app, ← ObjectProperty.FullSubcategory.comp_hom])).Exact := by
  rw [ShortComplex.ab_exact_iff]
  intro c hc
  -- `c` is a section of the image sheaf, since sections preserve kernels
  have h₂ := (ShortComplex.shortExact_image_ι_cokernel_π E.g).exact.map_of_mono_of_preservesKernel
    (sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op U)) inferInstance inferInstance
  obtain ⟨i, rfl⟩ := (ShortComplex.ab_exact_iff _).1 h₂ c hc
  -- and sections of the image lift to `B`, because the kernel `A` is flasque
  obtain ⟨b, rfl⟩ := (AddCommGrpCat.epi_iff_surjective _).1
    (epi_of_shortExact hE.shortExact_factorThruImage (U := U)) i
  exact ⟨b, by simp [← ConcreteCategory.comp_apply, ← NatTrans.comp_app,
    ← ObjectProperty.FullSubcategory.comp_hom]⟩

end TopCat.Sheaf.IsFlasque
