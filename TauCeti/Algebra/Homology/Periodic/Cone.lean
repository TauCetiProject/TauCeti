/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Periodic.Shift
public import TauCeti.CategoryTheory.Exact.HomologicalComplex
public import TauCeti.Algebra.Homology.HomotopyCofiber

/-!
# The mapping-cone conflation of periodic complexes

Mathlib's `HomologicalComplex.homotopyCofiber` supplies mapping cones for arbitrary complex
shapes. For a cyclic cochain complex its first projection is a chain map to the cochain shift:
the differential on the shifted summand carries a minus sign. This gives the short complex
`Y ⟶ homotopyCofiber f ⟶ X⟦1⟧`, split in every degree, for any map `f : X ⟶ Y`.

The sequence is a conflation for the degreewise extension of every exact structure on the base
category, including the componentwise split structure. Taking `f` to be the identity gives
the cone sequence used to compute suspension in the componentwise split exact category.
The splitting is only degreewise: its retraction and section need not commute with differentials.

All constructions also work at period zero, where `ZMod 0` is integer indexing; finite periodic
complexes are obtained by taking a positive period.

## References

* B. Keller, *Chain complexes and stable categories*, Manuscripta Mathematica **67**
  (1990), 379–417, Section 1.
* T. Stai, *The triangulated hull of periodic complexes*, Mathematical Research Letters **25**
  (2018), 199–236, Section 3.

The cone and its component calculus are Mathlib's `HomologicalComplex.homotopyCofiber`.
-/

public section

universe v u

namespace TauCeti.PeriodicComplex

open CategoryTheory CategoryTheory.Limits HomologicalComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
  {n : ℕ} {X Y : CochainComplex C (ZMod n)}

/-- The first projection of the periodic mapping cone, with target the signed cochain shift. -/
noncomputable def coneProjection (f : X ⟶ Y) : homotopyCofiber f ⟶ X⟦(1 : ℤ)⟧ :=
  CochainComplex.ofHom
    (fun i => homotopyCofiber.fstX f i (i + ((1 : ℤ) : ZMod n)) (by simp))
    (fun i => by
      -- Rebuild the hom-group operations at the unfolded cone and shift components: the
      -- automatically inserted group instances otherwise retain the dependent complex wrappers.
      change homotopyCofiber.fstX f i (i + ((1 : ℤ) : ZMod n)) (by simp) ≫
          ((1 : ℤ).negOnePow • X.d (i + ((1 : ℤ) : ZMod n))
            (i + 1 + ((1 : ℤ) : ZMod n))) =
        homotopyCofiber.d f i (i + 1) ≫
          homotopyCofiber.fstX f (i + 1) (i + 1 + ((1 : ℤ) : ZMod n)) (by simp)
      generalize_proofs
      generalize hOne : ((1 : ℤ) : ZMod n) = a at *
      have ha : a = 1 := hOne.symm.trans Int.cast_one
      clear hOne
      subst a
      simpa using (homotopyCofiber.d_fstX f i (i + 1) (i + 1 + 1) rfl rfl).symm)

/-- The projection in degree `i` is Mathlib's first cone projection. -/
@[simp]
theorem coneProjection_f (f : X ⟶ Y) (i : ZMod n) :
    (coneProjection f).f i = homotopyCofiber.fstX f i (i + ((1 : ℤ) : ZMod n)) (by simp) := (rfl)

/-- The cone inclusion followed by its shift projection is zero. -/
@[reassoc (attr := simp), simp]
theorem coneInclusion_comp_coneProjection (f : X ⟶ Y) :
    homotopyCofiber.inr f ≫ coneProjection f = 0 := by
  ext i
  simp

/-- The mapping-cone short complex `Y ⟶ homotopyCofiber f ⟶ X⟦1⟧`. -/
-- The endpoints must compute when constructing morphisms and evaluated splittings.
@[expose, implicit_reducible]
noncomputable def coneSequence (f : X ⟶ Y) : ShortComplex (CochainComplex C (ZMod n)) :=
  ShortComplex.mk (homotopyCofiber.inr f) (coneProjection f)
    (coneInclusion_comp_coneProjection f)

@[simp] theorem coneSequence_X₁ (f : X ⟶ Y) : (coneSequence f).X₁ = Y := (rfl)
@[simp] theorem coneSequence_X₂ (f : X ⟶ Y) :
    (coneSequence f).X₂ = homotopyCofiber f := (rfl)
@[simp] theorem coneSequence_X₃ (f : X ⟶ Y) :
    (coneSequence f).X₃ = X⟦(1 : ℤ)⟧ := (rfl)
@[simp] theorem coneSequence_f (f : X ⟶ Y) :
    (coneSequence f).f = homotopyCofiber.inr f := (rfl)
@[simp] theorem coneSequence_g (f : X ⟶ Y) :
    (coneSequence f).g = coneProjection f := (rfl)

/-- The mapping-cone sequence splits in every degree. The retraction is the second projection
and the section is the first inclusion; neither is asserted to be a chain map. -/
noncomputable def coneSequenceSplitting (f : X ⟶ Y) (i : ZMod n) :
    ((coneSequence f).map (eval C (ComplexShape.up (ZMod n)) i)).Splitting where
  r := homotopyCofiber.sndX f i
  s := homotopyCofiber.inlX f (i + ((1 : ℤ) : ZMod n)) i (by simp)
  f_r := homotopyCofiber.inrX_sndX f i
  s_g := homotopyCofiber.inlX_fstX f (i + ((1 : ℤ) : ZMod n)) i (by simp)
  id := by
    apply homotopyCofiber.ext_to_X f i (i + ((1 : ℤ) : ZMod n)) (by simp) <;>
      simp [coneSequence, Preadditive.add_comp, Category.assoc]

@[simp] theorem coneSequenceSplitting_r (f : X ⟶ Y) (i : ZMod n) :
    (coneSequenceSplitting f i).r = homotopyCofiber.sndX f i := (rfl)
@[simp] theorem coneSequenceSplitting_s (f : X ⟶ Y) (i : ZMod n) :
    (coneSequenceSplitting f i).s =
      homotopyCofiber.inlX f (i + ((1 : ℤ) : ZMod n)) i (by simp) := (rfl)

/-- The first cone projection is natural under commutative squares of periodic chain maps. -/
@[reassoc (attr := simp), simp]
theorem mapArrowHom_comp_coneProjection {X' Y' : CochainComplex C (ZMod n)}
    (f : X ⟶ Y) (g : X' ⟶ Y') (α : Arrow.mk f ⟶ Arrow.mk g) :
    homotopyCofiber.mapArrowHom f g (fun j => ⟨j - 1, by simp⟩) α ≫ coneProjection g =
      coneProjection f ≫ α.left⟦(1 : ℤ)⟧' := by
  ext i
  simp only [comp_f, coneProjection_f, shiftFunctor_map_f']
  apply homotopyCofiber.ext_from_X f (i + ((1 : ℤ) : ZMod n)) i (by simp)
  · simp
  · simp

/-- A commutative square induces a morphism of the corresponding mapping-cone short complexes. -/
noncomputable def coneSequenceMap {X' Y' : CochainComplex C (ZMod n)}
    (f : X ⟶ Y) (g : X' ⟶ Y') (α : Arrow.mk f ⟶ Arrow.mk g) :
    coneSequence f ⟶ coneSequence g :=
  ShortComplex.homMk α.right
    (homotopyCofiber.mapArrowHom f g (fun j => ⟨j - 1, by simp⟩) α)
    (α.left⟦(1 : ℤ)⟧')
    (by simp [coneSequence])
    (mapArrowHom_comp_coneProjection f g α)

@[simp] theorem coneSequenceMap_τ₁ {X' Y' : CochainComplex C (ZMod n)}
    (f : X ⟶ Y) (g : X' ⟶ Y') (α : Arrow.mk f ⟶ Arrow.mk g) :
    (coneSequenceMap f g α).τ₁ = α.right := (rfl)
@[simp] theorem coneSequenceMap_τ₂ {X' Y' : CochainComplex C (ZMod n)}
    (f : X ⟶ Y) (g : X' ⟶ Y') (α : Arrow.mk f ⟶ Arrow.mk g) :
    (coneSequenceMap f g α).τ₂ =
      homotopyCofiber.mapArrowHom f g (fun j => ⟨j - 1, by simp⟩) α := (rfl)
@[simp] theorem coneSequenceMap_τ₃ {X' Y' : CochainComplex C (ZMod n)}
    (f : X ⟶ Y) (g : X' ⟶ Y') (α : Arrow.mk f ⟶ Arrow.mk g) :
    (coneSequenceMap f g α).τ₃ = α.left⟦(1 : ℤ)⟧' := (rfl)

/-- Mapping-cone sequences depend functorially on arrows of periodic complexes. -/
-- Expose the object formula so morphism endpoints compute in the component API.
@[expose, implicit_reducible, simps obj map]
noncomputable def coneSequenceFunctor :
    Arrow (CochainComplex C (ZMod n)) ⥤ ShortComplex (CochainComplex C (ZMod n)) where
  obj f := coneSequence f.hom
  map {f g} α := coneSequenceMap f.hom g.hom α
  map_id f := by
    apply ShortComplex.hom_ext
    · simp [coneSequenceMap, coneSequence]
    · exact homotopyCofiber.mapArrowHom_id f.hom _
    · simp [coneSequenceMap, coneSequence]
  map_comp α β := by
    apply ShortComplex.hom_ext
    · simp [coneSequenceMap]
    · exact homotopyCofiber.mapArrowHom_comp _ _ _ _ α β
    · simp [coneSequenceMap]

variable [HasZeroObject C]

/-- The mapping-cone sequence is a conflation for the degreewise extension of any exact structure
on the base category. -/
theorem conflation_coneSequence (E : ExactStructure C) (f : X ⟶ Y) :
    (E.homologicalComplex (ComplexShape.up (ZMod n))).Conflation (coneSequence f) := by
  rw [ExactStructure.homologicalComplex_conflation_iff]
  exact fun i => E.conflation_of_splitting (coneSequenceSplitting f i)

end TauCeti.PeriodicComplex
