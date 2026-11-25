/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import TauCeti.AlgebraicGeometry.Compactification.BaseChange
public import TauCeti.AlgebraicGeometry.Compactification.Refinement
public import TauCeti.AlgebraicGeometry.Compactification.Uniqueness
public import TauCeti.AlgebraicGeometry.Morphisms.Separated

/-!
# Strict morphisms of scheme compactifications

A morphism `h : C ⟶ D` of compactifications of `f : X ⟶ S` always carries the interior
`C.j(X)` into the interior `D.j(X)`. It is *strict* if the inverse image of the target interior
is exactly the source interior, equivalently if the square formed by `h`, the two open
immersions and the identity of `X` is cartesian. Morphisms of compactifications need not be
strict: the fold map from `X ⨿ X`, compactifying `X` by its first summand, to the identity
compactification of a proper map is not strict as soon as `X` is nonempty.

Strict morphisms contain the isomorphisms, are closed under composition, are left-cancellable
(if `h ≫ k` is strict then so is `h`), and are preserved by base change. Every morphism out of a
compactification with topologically dense interior is strict; topological density suffices,
even over non-reduced ambient schemes. In particular every morphism out of a compactification
with schematically dense interior, such as a common refinement, is strict. Hence any two
compactifications have a common refinement by strict morphisms, and any two parallel morphisms
are equalized by a strict morphism.

## Main declarations

* `TauCeti.Compactification.strict`: the strict morphisms of compactifications, a
  multiplicative class of morphisms respecting isomorphisms.
* `TauCeti.Compactification.strict_iff_isPullback`: strictness as a cartesian square.
* `TauCeti.Compactification.strict_baseChangeMap`: base change preserves strictness.
* `TauCeti.Compactification.strict_of_isDominant`: morphisms out of a compactification with
  topologically dense interior are strict.
* `TauCeti.Compactification.exists_strict_commonRefinement`,
  `TauCeti.Compactification.exists_strict_comp_eq_comp`: common strict refinements and strict
  equalizing morphisms.
* `TauCeti.Compactification.not_strict_coprodSelfCodiag`: the fold map from the
  compactification with a boundary copy of the source is not strict.

## References

* B. Zavyalov, *Mod-p Poincaré duality in p-adic analytic geometry*, Ann. of Math. 201 (2025),
  arXiv:2111.01830, Definition 2.1.1 and Remark 2.1.3.
* G. Boxer and V. Pilloni, *Higher Hida theory for Siegel modular forms*, Lemma 2.1.4, and the
  Stacks Project, Lemma 38.32.1 (tag 0ATU), for strictness of maps out of a compactification
  with dense interior.
-/

public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace TauCeti

variable {X S T : Scheme.{u}} {f : X ⟶ S}

namespace Compactification

variable (f) in
/-- The *strict* morphisms of compactifications: those for which the inverse image of the
interior of the target is the interior of the source. -/
def strict : MorphismProperty (Compactification f) :=
  fun C D h ↦ h.hom.h ⁻¹ᵁ D.j.opensRange = C.j.opensRange

theorem strict_iff {C D : Compactification f} (h : C ⟶ D) :
    strict f h ↔ h.hom.h ⁻¹ᵁ D.j.opensRange = C.j.opensRange :=
  Iff.rfl

/-- The interior of the source always lies in the inverse image of the interior of the
target. -/
theorem opensRange_le_preimage_opensRange {C D : Compactification f} (h : C ⟶ D) :
    C.j.opensRange ≤ h.hom.h ⁻¹ᵁ D.j.opensRange := by
  intro y hy
  obtain ⟨x, rfl⟩ := Scheme.Hom.mem_opensRange.mp hy
  rw [Scheme.Hom.mem_preimage, Scheme.Hom.mem_opensRange]
  exact ⟨x, by rw [← Scheme.Hom.comp_apply, h.hom.ι_h]⟩

/-- Strictness only needs the inclusion of the inverse image of the target interior into the
source interior; the reverse inclusion always holds. -/
theorem strict_iff_preimage_le {C D : Compactification f} (h : C ⟶ D) :
    strict f h ↔ h.hom.h ⁻¹ᵁ D.j.opensRange ≤ C.j.opensRange :=
  ⟨le_of_eq, fun hle ↦ le_antisymm hle (opensRange_le_preimage_opensRange h)⟩

/-- A morphism of compactifications is strict exactly when the square formed by its map of
ambient schemes, the two open immersions and the identity of the source is cartesian. -/
theorem strict_iff_isPullback {C D : Compactification f} (h : C ⟶ D) :
    strict f h ↔ IsPullback (𝟙 X) C.j D.j h.hom.h := by
  refine ⟨fun hh ↦ IsOpenImmersion.isPullback _ _ _ _ (by simp) hh, fun H ↦ ?_⟩
  simpa [strict_iff, ← Scheme.Hom.opensRange_pullbackSnd] using
    (Scheme.Hom.opensRange_comp_of_isIso H.isoPullback.hom (pullback.snd D.j h.hom.h)).symm

/-- Identities are strict and composites of strict morphisms are strict. -/
instance : (strict f).IsMultiplicative where
  id_mem C := (strict_iff _).mpr (by simp)
  comp_mem h k hh hk := by
    rw [strict_iff] at hh hk ⊢
    simp [hk, hh]

/-- Isomorphisms of compactifications are strict. -/
theorem strict_of_isIso {C D : Compactification f} (h : C ⟶ D) [IsIso h] : strict f h :=
  (strict_iff_isPullback h).mpr <|
    IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, h.hom.ι_h]⟩

instance : (strict f).RespectsIso :=
  MorphismProperty.respectsIso_of_isStableUnderComposition fun _ _ h (_ : IsIso h) ↦
    strict_of_isIso h

/-- If a composite `h ≫ k` is strict, then so is `h`, whatever `k` is. -/
instance : (strict f).HasOfPostcompProperty ⊤ where
  of_postcomp {C D E} h k _ hhk := by
    refine (strict_iff_preimage_le h).mpr ?_
    calc h.hom.h ⁻¹ᵁ D.j.opensRange
        ≤ h.hom.h ⁻¹ᵁ (k.hom.h ⁻¹ᵁ E.j.opensRange) :=
          Scheme.Hom.preimage_mono _ (opensRange_le_preimage_opensRange k)
      _ = C.j.opensRange := by simpa [strict_iff, Scheme.Hom.comp_preimage] using hhk

/-- If the source is empty, every morphism of compactifications is strict. -/
theorem strict_of_isEmpty [IsEmpty X] {C D : Compactification f} (h : C ⟶ D) : strict f h := by
  have hbot {Y : Scheme.{u}} (i : X ⟶ Y) [IsOpenImmersion i] : i.opensRange = ⊥ := by
    ext
    simp [Scheme.Hom.coe_opensRange]
  rw [strict_iff, hbot, hbot, Scheme.Hom.preimage_bot]

/-- Base change along any map of bases preserves strictness: the inverse image of the
base-changed target interior is the base-changed source interior. -/
theorem strict_baseChangeMap {C D : Compactification f} {h : C ⟶ D} (hh : strict f h)
    (g : T ⟶ S) : strict _ (baseChangeMap h g) := by
  rw [strict_iff_isPullback] at hh ⊢
  -- Paste with the cartesian square comparing the target's interior with its base change; the
  -- composite is the square of `h` pasted with that of the source's interior.
  refine IsPullback.of_right ?_ (by simpa using (baseChangeMap h g).hom.ι_h.symm)
    (D.isPullback_baseChange g)
  simpa using (C.isPullback_baseChange g).paste_horiz hh

/-- A morphism out of a compactification whose interior is topologically dense is strict.
Topological density suffices, and no reducedness assumption is needed. -/
theorem strict_of_isDominant {C D : Compactification f} [IsDominant C.j] (h : C ⟶ D) :
    strict f h := by
  refine (strict_iff_preimage_le h).mpr ?_
  set V := h.hom.h ⁻¹ᵁ D.j.opensRange
  -- The interior of `C` lies in `V`, so `C.j` factors through `V` by a map `s`.
  have hsV : Set.range C.j ⊆ Set.range V.ι := by
    simpa [V] using SetLike.coe_subset_coe.mpr (opensRange_le_preimage_opensRange h)
  let s : X ⟶ V := IsOpenImmersion.lift V.ι C.j hsV
  -- The map `V ⟶ X` induced by `h` is separated, and `s` is a section of it.
  have hrV : Set.range (V.ι ≫ h.hom.h) ⊆ Set.range D.j := by
    simp [Set.range_comp, Set.image_subset_iff, V]
  let r : V.toScheme ⟶ X := IsOpenImmersion.lift D.j (V.ι ≫ h.hom.h) hrV
  have : IsSeparated (r ≫ D.j) := by
    rw [IsOpenImmersion.lift_fac]
    infer_instance
  have : IsSeparated r := IsSeparated.of_comp r D.j
  have hsr : s ≫ r = 𝟙 X := by
    rw [← cancel_mono D.j, Category.assoc, IsOpenImmersion.lift_fac,
      IsOpenImmersion.lift_fac_assoc, h.hom.ι_h, Category.id_comp]
  -- The range of `s` is dense in `V` because that of `C.j = s ≫ V.ι` is, so `s` is surjective.
  have : IsDominant (s ≫ V.ι) := by rwa [IsOpenImmersion.lift_fac]
  have : IsDominant s := IsDominant.of_comp_of_isOpenImmersion s V.ι
  have : Surjective s := surjective_of_isDominant_of_comp_eq_id hsr
  intro x hx
  obtain ⟨v, rfl⟩ : x ∈ Set.range V.ι := by simpa using hx
  obtain ⟨y, rfl⟩ := s.surjective v
  simp [← Scheme.Hom.comp_apply, s]

/-- Any two compactifications have a common refinement by strict morphisms, for example their
common refinement `commonRefinement C₁ C₂`. -/
theorem exists_strict_commonRefinement (C₁ C₂ : Compactification f) :
    ∃ (E : Compactification f) (g₁ : E ⟶ C₁) (g₂ : E ⟶ C₂), strict f g₁ ∧ strict f g₂ :=
  ⟨_, commonRefinementFst C₁ C₂, commonRefinementSnd C₁ C₂, strict_of_isDominant _,
    strict_of_isDominant _⟩

/-- Any two parallel morphisms of compactifications are equalized by a strict morphism, for
example the map to `C₁` from the common refinement of `C₁` with itself. -/
theorem exists_strict_comp_eq_comp {C₁ C₂ : Compactification f} (a b : C₁ ⟶ C₂) :
    ∃ (E : Compactification f) (g : E ⟶ C₁), strict f g ∧ g ≫ a = g ≫ b :=
  ⟨_, commonRefinementFst C₁ C₁, strict_of_isDominant _, hom_unique _ _⟩

variable (f)

/-- The compactification of a proper morphism `f : X ⟶ S` by `X ⨿ X`, with the first summand as
interior and a second copy of `X` as boundary. -/
-- Exposure and implicit reducibility let the projection formulas below state its ambient scheme
-- and maps as the coproduct and its maps.
@[expose, implicit_reducible]
noncomputable def coprodSelf [IsProper f] : Compactification f :=
  have : QuasiCompact ((coprod.inl : X ⟶ X ⨿ X) ≫ codiag X) := by
    rw [codiag, coprod.inl_desc]
    infer_instance
  have : QuasiCompact (coprod.inl : X ⟶ X ⨿ X) := QuasiCompact.of_comp _ (codiag X)
  ofHom coprod.inl (codiag X ≫ f) (by simp [codiag])

@[simp]
theorem coprodSelf_Xbar [IsProper f] : (coprodSelf f).Xbar = (X ⨿ X) :=
  (rfl)

@[simp]
theorem coprodSelf_j [IsProper f] : (coprodSelf f).j = (coprod.inl : X ⟶ X ⨿ X) :=
  (rfl)

@[simp]
theorem coprodSelf_p [IsProper f] : (coprodSelf f).p = codiag X ≫ f :=
  (rfl)

/-- The fold map from `coprodSelf f` to the identity compactification of `f`. -/
noncomputable def coprodSelfCodiag [IsProper f] : coprodSelf f ⟶ identity f :=
  ObjectProperty.homMk
    { h := codiag X
      ι_h := by simp [codiag]
      h_π := by simp }

@[simp]
theorem coprodSelfCodiag_hom_h [IsProper f] : (coprodSelfCodiag f).hom.h = codiag X :=
  (rfl)

/-- Morphisms of compactifications need not be strict: the fold map from `X ⨿ X` to `X`,
compactifying `X` by its first summand, is not strict when `X` is nonempty. -/
theorem not_strict_coprodSelfCodiag [IsProper f] [Nonempty X] :
    ¬ strict f (coprodSelfCodiag f) := by
  intro hh
  obtain ⟨x⟩ := ‹Nonempty X›
  have hx : (coprod.inr : X ⟶ X ⨿ X) x ∈ (coprodSelfCodiag f).hom.h ⁻¹ᵁ
      (identity f).j.opensRange := by
    simp
  rw [hh] at hx
  obtain ⟨y, hy⟩ := Scheme.Hom.mem_opensRange.mp hx
  exact inl_ne_inr X X y x hy

end Compactification

end TauCeti
