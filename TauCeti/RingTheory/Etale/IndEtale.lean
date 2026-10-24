/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.RingTheory.Etale.Basic
import Mathlib.CategoryTheory.Filtered.Connected
import Mathlib.CategoryTheory.Limits.Connected
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Smooth.Flat
import TauCeti.Algebra.Category.AlgCat.FilteredColimits
import TauCeti.Algebra.Category.CommAlgCat.FilteredColimits
import TauCeti.RingTheory.Flat.Colimit

/-!
# Ind-étale algebras

An algebra `S` over a commutative ring `R` is *ind-étale* if it is a small filtered colimit of
étale `R`-algebras, the colimit being taken in the category of commutative `R`-algebras. The
henselization of a pair, built as the filtered colimit of its étale neighbourhoods, is the
motivating example, and ind-étale algebras are the local building blocks of the pro-étale
topology of Bhatt and Scholze. Their first property is flatness, which comes from the general
fact that filtered colimits of flat modules are flat.

## Main definitions and results

* `TauCeti.Algebra.IndEtale R S`: the `R`-algebra `S` is a small filtered colimit of étale
  `R`-algebras.
* `TauCeti.Algebra.IndEtale.of_isColimit`: the point of a colimit cocone of a small filtered
  diagram of étale algebras is ind-étale.
* `TauCeti.Algebra.IndEtale.of_etale`: an étale algebra is ind-étale.
* `TauCeti.Algebra.IndEtale.of_equiv`: being ind-étale is invariant under isomorphism.
* `TauCeti.Algebra.IndEtale.flat`: an ind-étale algebra is flat (Stacks, Lemma 10.39.3 (05UU)).

## Implementation notes

The base ring, the algebra and the indexing category live in a single universe `u`, so that the
colimit is a small colimit in `CommAlgCat.{u} R`, whose forgetful functors to algebras, modules
and types preserve small filtered colimits.

## References

* [Stacks Project, Tag 05UU](https://stacks.math.columbia.edu/tag/05UU)
* B. Bhatt and P. Scholze, *The pro-étale topology for schemes*, Astérisque 369 (2015),
  Definition 2.2.1
-/

public section

open CategoryTheory Limits

universe u

namespace TauCeti.Algebra

/-- An `R`-algebra `S` is *ind-étale* if it is the colimit, in the category of commutative
`R`-algebras, of a small filtered diagram of étale `R`-algebras. -/
class IndEtale (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] : Prop where
  /-- `S` is the point of a colimit cocone of a small filtered diagram of étale algebras. -/
  exists_isColimit : ∃ (J : Type u) (_ : SmallCategory J) (_ : IsFiltered J)
    (D : J ⥤ CommAlgCat.{u} R) (ι : D ⟶ (Functor.const J).obj (CommAlgCat.of R S)),
      (∀ j, Algebra.Etale R (D.obj j)) ∧ Nonempty (IsColimit (Cocone.mk _ ι))

namespace IndEtale

variable {R S S' : Type u} [CommRing R] [CommRing S] [Algebra R S] [CommRing S'] [Algebra R S']

/-- The point of a colimit cocone of a small filtered diagram of étale `R`-algebras is ind-étale,
and so is every `R`-algebra isomorphic to it. -/
theorem of_isColimit {J : Type u} [SmallCategory J] [IsFiltered J] {D : J ⥤ CommAlgCat.{u} R}
    (hD : ∀ j, Algebra.Etale R (D.obj j)) {c : Cocone D} (hc : IsColimit c) (e : c.pt ≃ₐ[R] S) :
    IndEtale R S :=
  ⟨⟨J, inferInstance, inferInstance, D, _, hD,
    ⟨hc.ofIsoColimit (c.extendIso (CommAlgCat.isoMk e))⟩⟩⟩

/-- An étale algebra is ind-étale, as the colimit of the diagram consisting of itself. -/
instance of_etale [Algebra.Etale R S] : IndEtale R S :=
  of_isColimit (D := (Functor.const (Discrete PUnit.{u + 1})).obj (CommAlgCat.of R S))
    (fun _ => ‹_›) (isColimitConstCocone _ _) AlgEquiv.refl

/-- Being ind-étale is invariant under isomorphism of algebras. -/
theorem of_equiv [IndEtale R S] (e : S ≃ₐ[R] S') : IndEtale R S' := by
  obtain ⟨J, _, _, D, _, hD, ⟨hc⟩⟩ := IndEtale.exists_isColimit (R := R) (S := S)
  exact of_isColimit hD hc e

/-- An ind-étale algebra is flat: it is a filtered colimit of étale, hence flat, modules. -/
instance flat [IndEtale R S] : Module.Flat R S := by
  obtain ⟨J, _, _, D, _, hD, ⟨hc⟩⟩ := IndEtale.exists_isColimit (R := R) (S := S)
  -- The forgetful functors to algebras and to modules do not change the underlying type or the
  -- `R`-module structure, so the stages and the colimit below are the original algebras with
  -- their `R`-module structures.
  let G := forget₂ (CommAlgCat.{u} R) (AlgCat.{u} R) ⋙ forget₂ (AlgCat.{u} R) (ModuleCat.{u} R)
  have (j : J) : Module.Flat R ((D ⋙ G).obj j) :=
    have := hD j
    inferInstanceAs (Module.Flat R (D.obj j))
  exact Module.Flat.of_isColimit (isColimitOfPreserves G hc)

end IndEtale

-- `ℤ ⧸ 2` is not ind-étale over `ℤ`: it is not flat, since multiplication by `2` kills `1`.
example : ¬ IndEtale ℤ (ZMod 2) := by
  intro _
  have h := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := ZMod 2)
    (mem_nonZeroDivisors_of_ne_zero (two_ne_zero : (2 : ℤ) ≠ 0))
  exact one_ne_zero (h (show (2 : ℤ) • (1 : ZMod 2) = (2 : ℤ) • 0 by decide))

end TauCeti.Algebra
