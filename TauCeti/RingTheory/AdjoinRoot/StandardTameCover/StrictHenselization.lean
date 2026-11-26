/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.AdjoinRoot.StandardTameCover.Basic
public import TauCeti.RingTheory.StrictHenselization.FinitePresentation

/-!
# Products of standard tame covers over a strict henselization

Let `R → Ω` be a ring map and `algebra R Ω` the colimit of the pointed étale neighbourhoods of
`R → Ω`; for a local ring `R` and a separable closure `Ω` of its residue field, this is the strict
henselization `R^{sh}`. Let `S` be a finitely presented `R`-algebra and `a ∈ R`. If the base
change of `S` to `algebra R Ω` is a finite product of standard tamely ramified covers
`algebra R Ω [x]/(x^e − a)` with exponents invertible in `algebra R Ω`, then the same holds over
some pointed étale neighbourhood `B` of `R → Ω`, that is, an étale `R`-algebra `B` with a point
`B → Ω`.

In the proof of Abhyankar's lemma for a regular divisor (Stacks, Lemma 58.31.5 (0EYG)), the
structure of a tamely ramified cover is first determined over the strict henselization of the
local ring at a point of the divisor; this result spreads the conclusion to an étale
neighbourhood of that point. The decomposition over `algebra R Ω` is an isomorphism with the base
change of the finitely presented `R`-algebra `∏ R[x]/(x^(e i) − a)`, which descends to a pointed
étale neighbourhood (`AlgEquiv.exists_neighbourhood_tensorProduct`).
Each exponent is a unit at the point, so it becomes a unit after inverting it in a further
neighbourhood.

## Main results

* `TauCeti.StrictHenselization.exists_neighbourhood_isFiniteProductOfStandardTameCovers`: a
  decomposition into standard tame covers over `algebra R Ω` comes from one over a pointed étale
  neighbourhood.

## References

* [Stacks Project, Lemma 58.31.5](https://stacks.math.columbia.edu/tag/0EYG).
* [Stacks Project, Lemma 10.127.8](https://stacks.math.columbia.edu/tag/05N9).
-/

public section

open scoped TensorProduct

universe u

namespace TauCeti.StrictHenselization

variable {R Ω : Type u} [CommRing R] [CommRing Ω] [Algebra R Ω]

/-- If the base change of a finitely presented `R`-algebra `S` to the colimit `algebra R Ω` of
the pointed étale neighbourhoods of `R → Ω` is a finite product of standard tamely ramified covers
along `a`, then so is its base change to some pointed étale neighbourhood `B`. -/
theorem exists_neighbourhood_isFiniteProductOfStandardTameCovers {S : Type u} [CommRing S]
    [Algebra R S] [Algebra.FinitePresentation R S] {a : R}
    (h : IsFiniteProductOfStandardTameCovers (algebra R Ω) (algebra R Ω ⊗[R] S)
      (algebraMap R (algebra R Ω) a)) :
    ∃ B : Neighbourhood R Ω,
      IsFiniteProductOfStandardTameCovers B.obj.left (B.obj.left ⊗[R] S)
        (algebraMap R B.obj.left a) := by
  classical
  obtain ⟨ι, _, e, he, heu, ⟨σ⟩⟩ := (isFiniteProductOfStandardTameCovers_iff _).mp h
  -- Descend the decomposition, an isomorphism with a base change of `∏ R[x]/(x^(e i) − a)`.
  obtain ⟨B₁, σ₁, -⟩ := AlgEquiv.exists_neighbourhood_tensorProduct
    (T := ∀ i, standardTameCover R a (e i))
    (σ.trans (standardTameCoverPiBaseChangeAlgEquiv (algebra R Ω) a e).symm)
  -- The product `N` of the exponents is a unit at the point, so it is inverted in a refinement.
  let N : R := ∏ i, (e i : R)
  have hunit : IsUnit (algebraMap R (algebra R Ω) N) := by simp [N, heu]
  have hN : IsUnit (B₁.point (algebraMap R B₁.obj.left N)) := by
    simpa [← toTarget_stage_apply] using hunit.map (toTarget R Ω)
  obtain ⟨B₂, f, hf⟩ := Neighbourhood.exists_refinement_isUnit B₁ _ hN
  rw [AlgHom.commutes] at hf
  -- Base change the isomorphism along the refinement `B₁ ⟶ B₂`.
  let _ : Algebra B₁.obj.left B₂.obj.left := f.hom.left.hom.toRingHom.toAlgebra
  have : IsScalarTower R B₁.obj.left B₂.obj.left :=
    .of_algebraMap_eq fun r ↦ (f.hom.left.hom.commutes r).symm
  refine ⟨B₂, (isFiniteProductOfStandardTameCovers_iff _).mpr
    ⟨ι, inferInstance, e, he, fun i ↦ ?_, ⟨?_⟩⟩⟩
  · simp only [N, map_prod, map_natCast, IsUnit.prod_iff, Finset.mem_univ, forall_const] at hf
    exact hf i
  · exact (Algebra.TensorProduct.cancelBaseChange R B₁.obj.left _ B₂.obj.left S).symm.trans
      <| (Algebra.TensorProduct.congr AlgEquiv.refl σ₁).trans
      <| (Algebra.TensorProduct.cancelBaseChange R B₁.obj.left _ B₂.obj.left _).trans
      <| standardTameCoverPiBaseChangeAlgEquiv B₂.obj.left a e

end TauCeti.StrictHenselization
