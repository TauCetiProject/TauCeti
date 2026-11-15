/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.CommAlgCat.FinitePresentation
public import TauCeti.RingTheory.StrictHenselization.Algebra

/-!
# Isomorphisms of finitely presented algebras over pointed étale neighbourhoods

The colimit `algebra R Ω` of the pointed étale neighbourhoods of `R → Ω` is a small filtered
colimit of `R`-algebras. So an isomorphism between the base changes to `algebra R Ω` of two
finitely presented `R`-algebras `S` and `T` is already defined over some pointed étale
neighbourhood (`TauCeti.CommAlgCat.exists_algEquiv_tensorProduct_of_isColimit`). For a local
ring `R` and a separable closure `Ω` of its residue field, this is the step that spreads a
decomposition over the strict henselization `R^{sh}` to an étale neighbourhood of the closed
point.

## Main results

* `TauCeti.StrictHenselization.exists_neighbourhood_algEquiv_tensorProduct`: an
  `algebra R Ω`-algebra isomorphism `algebra R Ω ⊗[R] S ≃ algebra R Ω ⊗[R] T` is the base change
  of an isomorphism over a pointed étale neighbourhood.

## References

* [Stacks Project, Lemma 10.127.8](https://stacks.math.columbia.edu/tag/05N9).
* [Stacks Project, Tag 04GW](https://stacks.math.columbia.edu/tag/04GW), the description of the
  strict henselization as a colimit of étale neighbourhoods.
-/

public section

open CategoryTheory Limits
open scoped TensorProduct

universe u

namespace TauCeti.StrictHenselization

variable {R Ω : Type u} [CommRing R] [CommRing Ω] [Algebra R Ω]

/-- An `algebra R Ω`-algebra isomorphism `algebra R Ω ⊗[R] S ≃ algebra R Ω ⊗[R] T` between base
changes of finitely presented `R`-algebras is the base change of a `B`-algebra isomorphism
`B ⊗[R] S ≃ B ⊗[R] T` over some pointed étale neighbourhood `B`: the two agree on `S`. -/
theorem exists_neighbourhood_algEquiv_tensorProduct {S T : Type u} [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S] [CommRing T] [Algebra R T] [Algebra.FinitePresentation R T]
    (e : algebra R Ω ⊗[R] S ≃ₐ[algebra R Ω] algebra R Ω ⊗[R] T) :
    ∃ (B : Neighbourhood R Ω) (e' : B.obj.left ⊗[R] S ≃ₐ[B.obj.left] B.obj.left ⊗[R] T),
      ∀ s : S, Algebra.TensorProduct.map (stage R Ω B) (AlgHom.id R T) (e' (1 ⊗ₜ s)) =
        e (1 ⊗ₜ s) := by
  have : IsFiltered (SmallModel.{u} (Neighbourhood R Ω)) :=
    IsFiltered.of_equivalence (equivSmallModel.{u} (Neighbourhood R Ω))
  -- The small-model colimit cocone, with apex `algebra R Ω`.
  let c := (colimit.cocone (diagram R Ω)).extend (algebraIsoColimitDiagram R Ω).inv
  have hc : IsColimit c := (colimit.isColimit _).extendIso _
  obtain ⟨j, e', he'⟩ := TauCeti.CommAlgCat.exists_algEquiv_tensorProduct_of_isColimit hc e
  refine ⟨(equivSmallModel.{u} (Neighbourhood R Ω)).inverse.obj j, e', fun s ↦ ?_⟩
  rw [← he' s, ← algebraIsoColimitDiagram_inv_comp_ι]
  simp [c]

end TauCeti.StrictHenselization
