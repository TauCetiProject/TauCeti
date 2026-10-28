/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.HomologicalComplex.Augmented

/-!
# Comparison maps into augmented exact complexes

A map from a degreewise projective chain complex to an object lifts through any exact,
epimorphically augmented chain complex resolving that object. Only the target must be exact:
this allows, for example, comparison of a Koszul complex with a resolution of its quotient
without requiring the sequence defining the Koszul complex to be regular.

`ChainComplex.liftToAugmented` constructs the comparison from a degree-zero map annihilating
the first differential. `ChainComplex.liftToAugmented_comp` expresses the compatibility as an
equality of chain maps to the single complex. Together with
`ChainComplex.homotopyOfCompAugmentationEq`, this gives existence and homotopy uniqueness.

The construction adapts Mathlib's `CategoryTheory.ProjectiveResolution.lift` by Markus Himmel,
Kim Morrison, Jakob von Raumer and Joël Riou: neither exactness of the source nor projectivity
of the target is used. It reuses Mathlib's inductive chain-map constructor and exact lifting
from projective objects.

## References

* The Stacks Project, Lemma 10.71.4 (00LS), comparison with an exact complex.
* C. A. Weibel, *An Introduction to Homological Algebra*, Section 2.2.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace ChainComplex

variable {C : Type*} [Category* C] [Abelian C] (P : ChainComplex C ℕ)
  {Q : ChainComplex C ℕ}
  [∀ n, Projective (P.X n)] {Z : C} (ε : Q.X 0 ⟶ Z) [Epi ε]
  (w : Q.d 1 0 ≫ ε = 0) (h₀ : (ShortComplex.mk _ _ w).Exact)
  (hQ : ∀ n, (ShortComplex.mk _ _ (Q.d_comp_d (n + 2) (n + 1) n)).Exact)
  (f : P.X 0 ⟶ Z) (hf : P.d 1 0 ≫ f = 0)

/-- Lift a map annihilating the first differential of a degreewise projective complex through
an exact epimorphic augmentation. The source need not be exact and the target terms need not
be projective. -/
@[stacks 00LS "(1), for projective objects in an abelian category"]
def liftToAugmented : P ⟶ Q := by
  let f₀ := Projective.factorThru f ε
  have hf₀ : f₀ ≫ ε = f := Projective.factorThru_comp f ε
  let f₁ := h₀.liftFromProjective (P.d 1 0 ≫ f₀) (by simp [hf₀, hf])
  have hf₁ : f₁ ≫ Q.d 1 0 = P.d 1 0 ≫ f₀ := h₀.liftFromProjective_comp _ _
  refine ChainComplex.mkHom P Q f₀ f₁ hf₁ ?_
  intro n ⟨g, g', hg⟩
  have hz : (P.d (n + 2) (n + 1) ≫ g') ≫ Q.d (n + 1) n = 0 := by
    rw [Category.assoc, hg, ← Category.assoc, P.d_comp_d, zero_comp]
  exact ⟨(hQ n).liftFromProjective _ hz, (hQ n).liftFromProjective_comp _ _⟩

/-- The comparison map lifts the prescribed degree-zero map through the augmentation. -/
@[reassoc (attr := simp)]
theorem liftToAugmented_f_zero_comp :
    (liftToAugmented P ε w h₀ hQ f hf).f 0 ≫ ε = f := by
  simp only [liftToAugmented, mkHom_f_0, Projective.factorThru_comp]

/-- The comparison map preserves the augmentation, as an equality of chain maps. -/
@[reassoc (attr := simp)]
theorem liftToAugmented_comp :
    liftToAugmented P ε w h₀ hQ f hf ≫ (toSingle₀Equiv Q Z).symm ⟨ε, w⟩ =
      (toSingle₀Equiv P Z).symm ⟨f, hf⟩ := by
  ext
  simp

end ChainComplex

namespace CategoryTheory.ProjectiveResolution

variable {C : Type*} [Category* C] [Abelian C] {Z : C}

/-- An augmented degreewise projective complex admits an augmentation-preserving map into
any projective resolution. No exactness assumption is made on the source complex. -/
def liftFromComplex (Q : ProjectiveResolution Z) (P : ChainComplex C ℕ)
    [∀ n, Projective (P.X n)] (f : P ⟶ (ChainComplex.single₀ C).obj Z) : P ⟶ Q.complex :=
  P.liftToAugmented (Q.π.f 0) Q.complex_d_comp_π_f_zero Q.exact₀ Q.exact_succ
    (f.f 0) (ChainComplex.toSingle₀Equiv P Z f).property

/-- The comparison from an augmented projective complex lies over its given augmentation. -/
@[reassoc (attr := simp)]
theorem liftFromComplex_comp (Q : ProjectiveResolution Z) (P : ChainComplex C ℕ)
    [∀ n, Projective (P.X n)] (f : P ⟶ (ChainComplex.single₀ C).obj Z) :
    Q.liftFromComplex P f ≫ Q.π = f := by
  ext
  exact ChainComplex.liftToAugmented_f_zero_comp _ _ _ _ _ _ _

end CategoryTheory.ProjectiveResolution
