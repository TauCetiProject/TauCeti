/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Sections cut out by ideal sheaves

Let `f : X ⟶ S` be a morphism of schemes. A section `s` of `f` which is a closed immersion, for
instance any section of a separated morphism, is determined by its ideal sheaf `s.ker`: a second
section `t` of `f` with `s.ker ≤ t.ker` is equal to `s`. Conversely, an ideal sheaf `I` on `X` is
the ideal sheaf of a section of a separated morphism `f` exactly when its closed subscheme `V(I)`
maps isomorphically to `S`, and the section is then the inverse of `V(I) ⟶ S` followed by the
inclusion `V(I) ⟶ X`.

On a relative curve, this is how a relative effective Cartier divisor of degree one is the divisor
of a unique section.

## Main declarations

* `AlgebraicGeometry.Scheme.Hom.isClosedImmersion_of_comp_eq_id`: a section of a separated
  morphism is a closed immersion;
* `AlgebraicGeometry.Scheme.Hom.eq_of_ker_le_of_comp_eq_id`: a section of `f` which is a closed
  immersion is determined by its ideal sheaf;
* `AlgebraicGeometry.Scheme.Hom.ker_eq_ker_iff_of_comp_eq_id`: two sections of a separated
  morphism are equal exactly when their ideal sheaves are;
* `AlgebraicGeometry.Scheme.IdealSheafData.sectionOfIsIso`: the section cut out by an ideal sheaf
  whose closed subscheme maps isomorphically to `S`, characterised by
  `AlgebraicGeometry.Scheme.IdealSheafData.eq_sectionOfIsIso_iff`;
* `AlgebraicGeometry.Scheme.IdealSheafData.isIso_subschemeι_comp_iff`: an ideal sheaf is the ideal
  sheaf of a section of a separated morphism `f` exactly when its closed subscheme maps
  isomorphically to the base.
-/

public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

namespace Scheme.Hom

/-- **A section of a separated morphism is a closed immersion.** -/
theorem isClosedImmersion_of_comp_eq_id (s : S ⟶ X) {f : X ⟶ S} [IsSeparated f] (hs : s ≫ f = 𝟙 S) :
    IsClosedImmersion s := by
  have : IsClosedImmersion (s ≫ f) := hs ▸ inferInstance
  exact IsClosedImmersion.of_comp s f

/-- **A closed-immersion section is determined by its ideal sheaf.** If `s` and `t` are sections
of `f : X ⟶ S`, `t` is a closed immersion, and the ideal sheaf of `t` is contained in that of `s`,
then `s = t`. -/
theorem eq_of_ker_le_of_comp_eq_id (s t : S ⟶ X) {f : X ⟶ S} [IsClosedImmersion t]
    (hs : s ≫ f = 𝟙 S) (ht : t ≫ f = 𝟙 S) (h : t.ker ≤ s.ker) : s = t := by
  -- `s` factors through the closed immersion `t`, by an endomorphism of `S` that is then `𝟙 S`.
  have hl : IsClosedImmersion.lift t s h = 𝟙 S := by
    simpa [hs] using congr(IsClosedImmersion.lift t s h ≫ $ht).symm
  rw [← IsClosedImmersion.lift_fac t s h, hl, Category.id_comp]

/-- **Two sections of a separated morphism are equal exactly when their ideal sheaves are.** -/
theorem ker_eq_ker_iff_of_comp_eq_id (s t : S ⟶ X) {f : X ⟶ S} [IsSeparated f] (hs : s ≫ f = 𝟙 S)
    (ht : t ≫ f = 𝟙 S) : s.ker = t.ker ↔ s = t := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ rfl⟩
  have := t.isClosedImmersion_of_comp_eq_id ht
  exact s.eq_of_ker_le_of_comp_eq_id t hs ht h.ge

/-- The closed subscheme cut out by a closed-immersion section `s` of `f : X ⟶ S` maps
isomorphically to `S`. -/
theorem isIso_ker_subschemeι_comp (s : S ⟶ X) {f : X ⟶ S} [IsClosedImmersion s] (hs : s ≫ f = 𝟙 S) :
    IsIso (s.ker.subschemeι ≫ f) := by
  rw [IsIso.eq_inv_of_hom_inv_id (f := s.toImage) (g := s.ker.subschemeι ≫ f)
    (by rw [← Category.assoc, Scheme.Hom.toImage_imageι, hs])]
  infer_instance

end Scheme.Hom

namespace Scheme.IdealSheafData

variable {f : X ⟶ S}

section sectionOfIsIso

variable (I : X.IdealSheafData) (f) [IsIso (I.subschemeι ≫ f)]

/-- The **section cut out by an ideal sheaf** `I` on `X` whose closed subscheme `V(I)` maps
isomorphically to `S` under `f : X ⟶ S`: the inverse of `V(I) ⟶ S` followed by the inclusion
`V(I) ⟶ X`. It is the unique section of `f` with ideal sheaf `I` (`eq_sectionOfIsIso_iff`). -/
noncomputable def sectionOfIsIso : S ⟶ X :=
  inv (I.subschemeι ≫ f) ≫ I.subschemeι

/-- The section cut out by `I` is a section of `f`. -/
@[reassoc (attr := simp)]
theorem sectionOfIsIso_comp : I.sectionOfIsIso f ≫ f = 𝟙 S := by
  simp [sectionOfIsIso]

/-- The section cut out by `I` factors through the inclusion `V(I) ⟶ X`: precomposing it with
`V(I) ⟶ S` gives back that inclusion. -/
@[reassoc (attr := simp)]
theorem subschemeι_comp_comp_sectionOfIsIso :
    I.subschemeι ≫ f ≫ I.sectionOfIsIso f = I.subschemeι := by
  rw [sectionOfIsIso, ← Category.assoc, IsIso.hom_inv_id_assoc]

instance : IsClosedImmersion (I.sectionOfIsIso f) := by
  rw [sectionOfIsIso]
  infer_instance

/-- The ideal sheaf of the section cut out by `I` is `I`. -/
@[simp]
theorem ker_sectionOfIsIso : (I.sectionOfIsIso f).ker = I := by
  rw [sectionOfIsIso, Scheme.Hom.ker_comp_of_isIso, ker_subschemeι]

/-- **The section cut out by `I` is the unique section with ideal sheaf `I`.** A section `s` of
`f` is the section cut out by `I` exactly when its ideal sheaf is `I`. -/
theorem eq_sectionOfIsIso_iff {s : S ⟶ X} (hs : s ≫ f = 𝟙 S) :
    s = I.sectionOfIsIso f ↔ s.ker = I := by
  refine ⟨fun h ↦ h ▸ I.ker_sectionOfIsIso f, fun h ↦ ?_⟩
  exact s.eq_of_ker_le_of_comp_eq_id _ hs (I.sectionOfIsIso_comp f) (by simp [h])

end sectionOfIsIso

/-- **Ideal sheaves of sections.** An ideal sheaf `I` on `X` is the ideal sheaf of a section of a
separated morphism `f : X ⟶ S` exactly when its closed subscheme maps isomorphically to `S`. -/
theorem isIso_subschemeι_comp_iff [IsSeparated f] (I : X.IdealSheafData) :
    IsIso (I.subschemeι ≫ f) ↔ ∃ s : S ⟶ X, s ≫ f = 𝟙 S ∧ s.ker = I := by
  refine ⟨fun _ ↦ ⟨I.sectionOfIsIso f, I.sectionOfIsIso_comp f, I.ker_sectionOfIsIso f⟩, ?_⟩
  rintro ⟨s, hs, rfl⟩
  have := s.isClosedImmersion_of_comp_eq_id hs
  exact s.isIso_ker_subschemeι_comp hs

end Scheme.IdealSheafData

end AlgebraicGeometry
