/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ModelCategory.KInjective.Tower.Basic
public import TauCeti.Algebra.Homology.ModelCategory.KInjective.ModelStructure
public import TauCeti.CategoryTheory.LiftingProperties.OfOpSequence

/-!
# Limits of towers of injective complexes

Degreewise epimorphisms with injective kernels between bounded below complexes are fibrations
of the injective model structure. Lifting properties pass to limits of towers, so the limits
constructed here are K-injective complexes of injective objects, without a boundedness
assumption on the limit. This applies in particular to the resolved truncation tower used in
Spaltenstein's construction of unbounded K-injective replacements.

## References

* N. Spaltenstein, *Resolutions of unbounded complexes*, Compositio Math. 65 (1988), 121–154, §3.
* [Stacks: Lemma 13.31.7](https://stacks.math.columbia.edu/tag/070K).
-/

public section

open CategoryTheory Limits Opposite HomotopicalAlgebra ZeroObject

namespace CochainComplex

variable {C : Type*} [Category* C] [Abelian C]

open modelCategoryInjective in
/-- **Limits of towers of injective complexes.** Let `p n : X (n + 1) ⟶ X n` be degreewise
epimorphisms with injective kernels between complexes of injective objects, each vanishing in
sufficiently negative degrees. Then a limit of the tower is a K-injective complex of injective
objects, although it need not vanish in any degree. -/
theorem isKInjective_of_isLimit_ofOpSequence {X : ℕ → CochainComplex C ℤ}
    (p : ∀ n, X (n + 1) ⟶ X n) (hp : ∀ n, degreewiseEpiWithInjectiveKernel (p n))
    (hX : ∀ n, ∃ d : ℤ, (X n).IsStrictlyGE d) (hX₀ : ∀ i, Injective ((X 0).X i))
    {c : Cone (Functor.ofOpSequence p)} (hc : IsLimit c) :
    (∀ i, Injective (c.pt.X i)) ∧ c.pt.IsKInjective := by
  rw [← modelCategoryInjective.isFibrant_iff, HomotopicalAlgebra.isFibrant_iff,
    HomotopicalAlgebra.fibration_iff, modelCategoryInjective.fibrations_eq]
  intro A B i hi
  have (n : ℕ) : HasLiftingProperty i (p n) := by
    obtain ⟨d, _⟩ := hX (n + 1)
    have := modelCategoryInjective.fibration_of_degreewiseEpiWithInjectiveKernel (p n) (hp n) d
    rw [HomotopicalAlgebra.fibration_iff, modelCategoryInjective.fibrations_eq] at this
    exact this i hi
  have h₀ : HasLiftingProperty i (terminal.from (X 0)) := by
    obtain ⟨d, _⟩ := hX 0
    have : IsFibrant (X 0) :=
      (modelCategoryInjective.isFibrant_iff _).2 ⟨hX₀, isKInjective_of_injective _ d⟩
    rw [HomotopicalAlgebra.isFibrant_iff, HomotopicalAlgebra.fibration_iff,
      modelCategoryInjective.fibrations_eq] at this
    exact this i hi
  have := hasLiftingProperty_π_app_zero_of_isLimit i p hc
  rw [show terminal.from c.pt = c.π.app (op 0) ≫ terminal.from (X 0) from terminal.hom_ext _ _]
  exact @HasLiftingProperty.of_comp_right _ _ _ _ _ _ _ (terminal.from (X 0)) (c.π.app (op 0)) i
    h₀ this

section TowerResolution

variable [EnoughInjectives C] (b : ℕ → ℤ) (hb : Antitone b)
  (T : ℕ → CochainComplex C ℤ) [∀ n, (T n).IsStrictlyGE (b n)]
  (u : ∀ n, T (n + 1) ⟶ T n)

/-- The limit of the resolution of a tower of bounded below complexes is a K-injective complex of
injective objects. -/
theorem isKInjective_of_isLimit_towerResolution
    {c : Cone (Functor.ofOpSequence (towerResolutionπ b hb T u))} (hc : IsLimit c) :
    (∀ i, Injective (c.pt.X i)) ∧ c.pt.IsKInjective :=
  isKInjective_of_isLimit_ofOpSequence _
    (degreewiseEpiWithInjectiveKernel_towerResolutionπ b hb T u)
    (fun n ↦ ⟨b n - 1, inferInstance⟩) inferInstance hc

end TowerResolution

variable [EnoughInjectives C] (K : CochainComplex C ℤ)

/-- A limit of the resolved truncation tower is a K-injective complex of injective objects. -/
theorem isKInjective_of_isLimit_truncGETower {c : Cone (truncGETower K)} (hc : IsLimit c) :
    (∀ i, Injective (c.pt.X i)) ∧ c.pt.IsKInjective :=
  isKInjective_of_isLimit_towerResolution _ _ _ _ hc

end CochainComplex
