/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Projective

/-!
# A projective horseshoe step

Package a conflation between two fixed outer objects and the projective horseshoe step between
such rows. Both complete and unbounded resolutions iterate this construction; the step itself
requires only the two outer conflations and projectivity of the right resolving term.

See Bühler, *Exact categories*, Section 12, and Weibel, *An Introduction to Homological Algebra*,
Lemma 2.2.8.
-/

public section

namespace TauCeti.ExactStructure

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C]

/-- A conflation with fixed outer objects and a variable middle object. -/
structure ConflationRow (E : ExactStructure C) (A B : C) where
  /-- The middle object. -/
  Z : C
  /-- The inflation from the left outer object. -/
  v : A ⟶ Z
  /-- The deflation to the right outer object. -/
  w : Z ⟶ B
  zero : v ≫ w = 0
  /-- The row is a distinguished conflation. -/
  conflation : E.Conflation (ShortComplex.mk v w zero)

attribute [reassoc (attr := simp)] ConflationRow.zero

namespace ConflationRow

variable {E : ExactStructure C} (S₁ S₃ : ShortComplex C)

/-- A projective horseshoe step linking a row of cokernels to a row of kernels. Its middle
resolving object is the biproduct of the outer resolving objects. -/
structure ProjectiveStep (R : ConflationRow E S₁.X₃ S₃.X₃)
    (R' : ConflationRow E S₁.X₁ S₃.X₁) where
  /-- The middle inflation. -/
  ι : R'.Z ⟶ S₁.X₂ ⊞ S₃.X₂
  /-- The middle deflation. -/
  π : S₁.X₂ ⊞ S₃.X₂ ⟶ R.Z
  zero : ι ≫ π = 0
  /-- The middle column is a distinguished conflation. -/
  conflation : E.Conflation (ShortComplex.mk ι π zero)
  inl_π : biprod.inl ≫ π = S₁.g ≫ R.v
  π_w : π ≫ R.w = biprod.snd ≫ S₃.g
  v_ι : R'.v ≫ ι = S₁.f ≫ biprod.inl
  ι_snd : ι ≫ biprod.snd = R'.w ≫ S₃.f

attribute [reassoc (attr := simp)] ProjectiveStep.zero
attribute [reassoc] ProjectiveStep.inl_π ProjectiveStep.π_w ProjectiveStep.v_ι ProjectiveStep.ι_snd

variable {S₁ S₃}

/-- A row of cokernels extends to a row of kernels when the right resolving term is projective. -/
theorem nonempty_projectiveStep (R : ConflationRow E S₁.X₃ S₃.X₃)
    (h₁ : E.Conflation S₁) (h₃ : E.Conflation S₃) (hP : E.isProjective S₃.X₂) :
    Nonempty (Σ R' : ConflationRow E S₁.X₁ S₃.X₁, ProjectiveStep S₁ S₃ R R') := by
  obtain ⟨K, u, a, hua, v, w, hvw, hu, hv, ha₁, ha₃, hu₁, hu₃⟩ :=
    E.exists_conflation_biprod_of_conflation_of_projective R.conflation h₁ h₃ hP
  exact ⟨⟨⟨K, v, w, hvw, hv⟩, ⟨u, a, hua, hu, ha₁, ha₃, hu₁, hu₃⟩⟩⟩

end ConflationRow

end TauCeti.ExactStructure
