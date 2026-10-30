/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.Projective.Resolution

/-!
# Homotopy uniqueness for augmented exact complexes

Maps from a degreewise projective chain complex to an augmented exact complex are homotopic
when their degree-zero components agree after augmentation. The target terms need not be
projective. In particular, this applies to the restriction of a projective resolution along
an arbitrary group homomorphism, even when restriction fails to preserve projective objects.

The construction follows Kim Morrison and Joël Riou's
`CategoryTheory.ProjectiveResolution.liftHomotopyZero` in Mathlib, using only the exactness
assumptions on its target. The induction is Mathlib's `Homotopy.mkInductive`.

## References

* C. A. Weibel, *An Introduction to Homological Algebra*, Section 2.2,
  the comparison theorem for resolutions.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace ChainComplex

variable {C : Type*} [Category* C] [Abelian C] {P Q : ChainComplex C ℕ}
  [∀ n, Projective (P.X n)] {Z : C} (ε : Q.X 0 ⟶ Z)
  (w : Q.d 1 0 ≫ ε = 0) (h₀ : (ShortComplex.mk _ _ w).Exact)
  (hQ : ∀ n, (ShortComplex.mk _ _ (Q.d_comp_d (n + 2) (n + 1) n)).Exact)

/-- A map from a degreewise projective chain complex to an augmented exact complex that
vanishes after augmentation is null-homotopic. No projectivity of the target, exactness of
the source, or surjectivity of the augmentation is required. -/
def nullHomotopyOfCompAugmentationEqZero (f : P ⟶ Q) (hf : f.f 0 ≫ ε = 0) :
    Homotopy f 0 := by
  let s₀ := h₀.liftFromProjective (f.f 0) hf
  have hs₀ : s₀ ≫ Q.d 1 0 = f.f 0 := h₀.liftFromProjective_comp _ _
  have hz : (f.f 1 - P.d 1 0 ≫ s₀) ≫ Q.d 1 0 = 0 := by
    rw [Preadditive.sub_comp, Category.assoc, hs₀, f.comm, sub_self]
  let s₁ := (hQ 0).liftFromProjective (f.f 1 - P.d 1 0 ≫ s₀) hz
  have hs₁ : s₁ ≫ Q.d 2 1 = f.f 1 - P.d 1 0 ≫ s₀ :=
    (hQ 0).liftFromProjective_comp _ _
  refine Homotopy.mkInductive f s₀ hs₀.symm s₁ (by rw [hs₁]; abel) ?_
  intro n ⟨s, s', hs⟩
  have hz' : (f.f (n + 2) - P.d (n + 2) (n + 1) ≫ s') ≫
      Q.d (n + 2) (n + 1) = 0 := by
    rw [Preadditive.sub_comp, f.comm, hs, Preadditive.comp_add,
      ← Category.assoc, P.d_comp_d, zero_comp, zero_add, Category.assoc, sub_self]
  exact ⟨(hQ (n + 1)).liftFromProjective _ hz', by
    rw [(hQ (n + 1)).liftFromProjective_comp]
    abel⟩

/-- Two maps from a degreewise projective complex into an augmented exact complex are
homotopic if they agree after augmentation. The target need not be degreewise projective. -/
def homotopyOfCompAugmentationEq (f g : P ⟶ Q) (hfg : f.f 0 ≫ ε = g.f 0 ≫ ε) :
    Homotopy f g :=
  Homotopy.equivSubZero.symm <|
    nullHomotopyOfCompAugmentationEqZero ε w h₀ hQ (f - g) (by
      simp only [HomologicalComplex.sub_f_apply, Preadditive.sub_comp, hfg, sub_self])

end ChainComplex
