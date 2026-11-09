/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.AlmostSplit.Ext
public import TauCeti.CategoryTheory.AlmostSplit.Uniqueness
public import TauCeti.CategoryTheory.Exact.Abelian
public import TauCeti.CategoryTheory.Exact.Opposite
public import TauCeti.CategoryTheory.Exact.YonedaExt.Basic
public import TauCeti.CategoryTheory.Preadditive.KrullSchmidt.Basic

/-!
# Almost-split conflations

A conflation of an exact category is *almost split* when, as a short complex, it satisfies
`CategoryTheory.ShortComplex.IsAlmostSplit`: its inflation is left almost split and its deflation
is right almost split. Its end terms are then automatically indecomposable, with local
endomorphism rings (`TauCeti.IsLeftAlmostSplit.isLocalRing_end`,
`TauCeti.IsRightAlmostSplit.isLocalRing_end`).

This file recognizes such conflations through one lifting property or through `Ext¹`, with no
ambient abelian category and without enough projectives or injectives, which is the generality
needed for Auslander–Reiten duality in an exact category:

* one lifting property implies the other, as soon as the opposite end has a local endomorphism
  ring;
* **the extension-class criterion**: a conflation `e : X ⟶ Y ⟶ Z` with `End Z` local is almost
  split exactly when its class `[e] ∈ Ext¹_E(Z, X)` is nonzero and is killed by cobase change along
  every morphism out of `X` that is not a split monomorphism. Dually, when `End X` is local, it is
  almost split exactly when `[e]` is nonzero and killed by base change along every morphism into
  `Z` that is not a split epimorphism. In a Krull-Schmidt category the locality hypotheses are
  indecomposability of the end terms. In an abelian category, this recovers the criterion through
  Mathlib's `CategoryTheory.ShortComplex.ShortExact.extClass`;
* an almost-split conflation is determined up to isomorphism of conflations by either of its end
  terms.

## Main results

* `TauCeti.ExactStructure.Extension.isRightAlmostSplit_g_of_isLeftAlmostSplit_f` and
  `TauCeti.ExactStructure.Extension.isLeftAlmostSplit_f_of_isRightAlmostSplit_g`: one lifting
  property implies the other.
* `TauCeti.ExactStructure.Extension.isAlmostSplit_iff_ext1_pushout`,
  `TauCeti.ExactStructure.Extension.isAlmostSplit_iff_ext1_pullback`, and, in a Krull-Schmidt
  category, `TauCeti.ExactStructure.Extension.isAlmostSplit_iff_ext1_pushout_of_indecomposable` and
  `TauCeti.ExactStructure.Extension.isAlmostSplit_iff_ext1_pullback_of_indecomposable`: the
  extension-class criterion.
* `TauCeti.ExactStructure.Extension.not_isAlmostSplit_of_mk_eq_zero`: a split conflation is never
  almost split.
* `TauCeti.ExactStructure.isIso_of_isAlmostSplit_of_isIso_τ₃`,
  `TauCeti.ExactStructure.isIso_of_isAlmostSplit_of_isIso_τ₁`,
  `TauCeti.ExactStructure.exists_iso_τ₃_eq_of_isAlmostSplit`, and
  `TauCeti.ExactStructure.exists_iso_τ₁_eq_of_isAlmostSplit`: uniqueness at each end.
* `CategoryTheory.ShortComplex.ShortExact.isAlmostSplit_iff_extClass`: the abelian criterion.

## References

* O. Iyama, H. Nakaoka, Y. Palu, *Auslander–Reiten theory in extriangulated categories*,
  arXiv:1805.03776, Theorem 2.9 and Proposition 2.10.
* M. Auslander, I. Reiten, S. Smalø, *Representation Theory of Artin Algebras*, CUP (1995), V.1.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]

namespace ExactStructure

variable {E : ExactStructure C}

namespace Extension

open Preadditive

variable {X Z : C}

/-- **A conflation with left almost split inflation and local right-hand endomorphism ring has
right almost split deflation.** -/
theorem isRightAlmostSplit_g_of_isLeftAlmostSplit_f [IsLocalRing (End Z)] (e : E.Extension Z X)
    (hf : IsLeftAlmostSplit e.f) : IsRightAlmostSplit e.g := by
  have hg : ¬ IsSplitEpi e.g := fun hg ↦ hf.not_isSplitMono <|
    (Ext1.mk_eq_zero_iff_isSplitMono e).mp ((Ext1.mk_eq_zero_iff_isSplitEpi e).mpr hg)
  refine isRightAlmostSplit_iff.mpr ⟨hg, fun W u hu ↦ ?_⟩
  refine (Ext1.mk_pullback_eq_zero_iff e u).mp ?_
  rw [Ext1.pullback_mk, Ext1.mk_eq_zero_iff_isSplitMono]
  by_contra hs
  -- The inflation of the base change factors through `e.f`, which decomposes `𝟙 Z`.
  obtain ⟨t, ht⟩ := hf.factors _ (e.pullback u).f hs
  have h₁ : e.f ≫ (𝟙 e.obj - t ≫ e.pullbackFst u) = 0 := by
    simp [comp_sub, reassoc_of% ht]
  have h₂ : e.f ≫ t ≫ (e.pullback u).g = 0 := by
    simp [reassoc_of% ht]
  have hK := e.isKernelCokernelPair
  have hepi := hK.epi_g
  have hid : hK.desc _ h₁ ≫ e.g + hK.desc _ h₂ ≫ u = 𝟙 Z := by
    rw [← cancel_epi e.g]
    have h₃ := hK.g_desc _ h₁
    have h₄ := hK.g_desc _ h₂
    dsimp only [Extension.shortComplex] at h₃ h₄
    simp [comp_add, reassoc_of% h₃, reassoc_of% h₄, sub_comp, Extension.pullbackFst_g]
  exact (isSplitEpi_or_isSplitEpi_of_add_eq_id hid).elim hg hu

/-- **A conflation with right almost split deflation and local left-hand endomorphism ring has left
almost split inflation.** -/
theorem isLeftAlmostSplit_f_of_isRightAlmostSplit_g [IsLocalRing (End X)] (e : E.Extension Z X)
    (hg : IsRightAlmostSplit e.g) : IsLeftAlmostSplit e.f := by
  have hf : ¬ IsSplitMono e.f := fun hf ↦ hg.not_isSplitEpi <|
    (Ext1.mk_eq_zero_iff_isSplitEpi e).mp ((Ext1.mk_eq_zero_iff_isSplitMono e).mpr hf)
  refine isLeftAlmostSplit_iff.mpr ⟨hf, fun W v hv ↦ ?_⟩
  refine (Ext1.mk_pushout_eq_zero_iff e v).mp ?_
  rw [Ext1.pushout_mk, Ext1.mk_eq_zero_iff_isSplitEpi]
  by_contra hs
  -- The deflation of the cobase change factors through `e.g`, which decomposes `𝟙 X`.
  obtain ⟨t, ht⟩ := hg.factors _ (e.pushout v).g hs
  have h₁ : (𝟙 e.obj - e.pushoutInl v ≫ t) ≫ e.g = 0 := by
    simp [sub_comp, ht]
  have h₂ : ((e.pushout v).f ≫ t) ≫ e.g = 0 := by
    simp [ht]
  have hK := e.isKernelCokernelPair
  have hmono := hK.mono_f
  have hid : e.f ≫ hK.lift _ h₁ + v ≫ hK.lift _ h₂ = 𝟙 X := by
    rw [← cancel_mono e.f]
    have h₃ := hK.lift_f _ h₁
    have h₄ := hK.lift_f _ h₂
    dsimp only [Extension.shortComplex] at h₃ h₄
    simp [add_comp, h₃, h₄, comp_sub, Extension.f_pushoutInl_assoc]
  exact (isSplitMono_or_isSplitMono_of_add_eq_id hid).elim hf hv

/-- A conflation with local right-hand endomorphism ring is almost split exactly when its inflation
is left almost split. -/
theorem isAlmostSplit_iff_isLeftAlmostSplit_f [IsLocalRing (End Z)] (e : E.Extension Z X) :
    e.shortComplex.IsAlmostSplit ↔ IsLeftAlmostSplit e.f :=
  ⟨fun h ↦ h.isLeftAlmostSplit_f, fun h ↦
    ⟨e.shortExact, h, e.isRightAlmostSplit_g_of_isLeftAlmostSplit_f h⟩⟩

/-- A conflation with local left-hand endomorphism ring is almost split exactly when its deflation
is right almost split. -/
theorem isAlmostSplit_iff_isRightAlmostSplit_g [IsLocalRing (End X)] (e : E.Extension Z X) :
    e.shortComplex.IsAlmostSplit ↔ IsRightAlmostSplit e.g :=
  ⟨fun h ↦ h.isRightAlmostSplit_g, fun h ↦
    ⟨e.shortExact, e.isLeftAlmostSplit_f_of_isRightAlmostSplit_g h, h⟩⟩

/-- The inflation of a conflation is left almost split exactly when its class is nonzero and is
killed by cobase change along every morphism out of the first term that is not a split
monomorphism. -/
theorem isLeftAlmostSplit_f_iff_ext1 (e : E.Extension Z X) :
    IsLeftAlmostSplit e.f ↔ Ext1.mk e ≠ 0 ∧
      ∀ (W : C) (v : X ⟶ W), ¬ IsSplitMono v → (Ext1.mk e).pushout v = 0 := by
  simp only [isLeftAlmostSplit_iff, ne_eq, Ext1.mk_eq_zero_iff_isSplitMono,
    Ext1.mk_pushout_eq_zero_iff]

/-- The deflation of a conflation is right almost split exactly when its class is nonzero and is
killed by base change along every morphism into the last term that is not a split epimorphism. -/
theorem isRightAlmostSplit_g_iff_ext1 (e : E.Extension Z X) :
    IsRightAlmostSplit e.g ↔ Ext1.mk e ≠ 0 ∧
      ∀ (W : C) (u : W ⟶ Z), ¬ IsSplitEpi u → (Ext1.mk e).pullback u = 0 := by
  simp only [isRightAlmostSplit_iff, ne_eq, Ext1.mk_eq_zero_iff_isSplitEpi,
    Ext1.mk_pullback_eq_zero_iff]

/-- **The extension-class criterion.** A conflation with local right-hand endomorphism ring is
almost split exactly when its class is nonzero and is killed by cobase change along every morphism
out of the first term that is not a split monomorphism. -/
theorem isAlmostSplit_iff_ext1_pushout [IsLocalRing (End Z)] (e : E.Extension Z X) :
    e.shortComplex.IsAlmostSplit ↔ Ext1.mk e ≠ 0 ∧
      ∀ (W : C) (v : X ⟶ W), ¬ IsSplitMono v → (Ext1.mk e).pushout v = 0 :=
  e.isAlmostSplit_iff_isLeftAlmostSplit_f.trans e.isLeftAlmostSplit_f_iff_ext1

/-- **The extension-class criterion, from the right-hand end.** A conflation with local left-hand
endomorphism ring is almost split exactly when its class is nonzero and is killed by base change
along every morphism into the last term that is not a split epimorphism. -/
theorem isAlmostSplit_iff_ext1_pullback [IsLocalRing (End X)] (e : E.Extension Z X) :
    e.shortComplex.IsAlmostSplit ↔ Ext1.mk e ≠ 0 ∧
      ∀ (W : C) (u : W ⟶ Z), ¬ IsSplitEpi u → (Ext1.mk e).pullback u = 0 :=
  e.isAlmostSplit_iff_isRightAlmostSplit_g.trans e.isRightAlmostSplit_g_iff_ext1

/-- **The extension-class criterion in a Krull-Schmidt exact category.** A conflation with
indecomposable right-hand end is almost split exactly when its class is nonzero and is killed by
cobase change along every morphism out of the first term that is not a split monomorphism. The
left-hand end of an almost-split conflation is automatically indecomposable. -/
theorem isAlmostSplit_iff_ext1_pushout_of_indecomposable [HasFiniteBiproducts C] [IsKrullSchmidt C]
    (e : E.Extension Z X) (hZ : Indecomposable Z) :
    e.shortComplex.IsAlmostSplit ↔ Ext1.mk e ≠ 0 ∧
      ∀ (W : C) (v : X ⟶ W), ¬ IsSplitMono v → (Ext1.mk e).pushout v = 0 :=
  have := (IsKrullSchmidt.indecomposable_iff_isLocalRing_end Z).mp hZ
  e.isAlmostSplit_iff_ext1_pushout

/-- **The extension-class criterion in a Krull-Schmidt exact category, from the right-hand end.** A
conflation with indecomposable left-hand end is almost split exactly when its class is nonzero and
is killed by base change along every morphism into the last term that is not a split epimorphism.
The right-hand end of an almost-split conflation is automatically indecomposable. -/
theorem isAlmostSplit_iff_ext1_pullback_of_indecomposable [HasFiniteBiproducts C] [IsKrullSchmidt C]
    (e : E.Extension Z X) (hX : Indecomposable X) :
    e.shortComplex.IsAlmostSplit ↔ Ext1.mk e ≠ 0 ∧
      ∀ (W : C) (u : W ⟶ Z), ¬ IsSplitEpi u → (Ext1.mk e).pullback u = 0 :=
  have := (IsKrullSchmidt.indecomposable_iff_isLocalRing_end X).mp hX
  e.isAlmostSplit_iff_ext1_pullback

/-- **A split conflation is never almost split**, since its class vanishes. -/
theorem not_isAlmostSplit_of_mk_eq_zero (e : E.Extension Z X) (he : Ext1.mk e = 0) :
    ¬ e.shortComplex.IsAlmostSplit := fun h ↦
  (e.isLeftAlmostSplit_f_iff_ext1.mp h.isLeftAlmostSplit_f).1 he

end Extension

variable {S S' : ShortComplex C}

/-- **A morphism of almost-split conflations that is invertible at the right-hand end is
invertible.** -/
theorem isIso_of_isAlmostSplit_of_isIso_τ₃ (E : ExactStructure C) (hS : E.Conflation S)
    (hS' : E.Conflation S') (ha : S.IsAlmostSplit) (ha' : S'.IsAlmostSplit) (φ : S ⟶ S')
    [IsIso φ.τ₃] : IsIso φ := by
  have : IsIso φ.τ₁ := ha.isIso_τ₁_of_isIso_τ₃ ha' (E.isKernelCokernelPair S hS).fIsKernel φ
  have : IsIso φ.τ₂ := E.isIso₂_of_conflation_of_isIso₁₃ φ hS hS'
  exact ShortComplex.isIso_of_isIso φ

/-- **Uniqueness of the almost-split conflation at a given right-hand end**: an isomorphism between
the right-hand ends of two almost-split conflations is realized by an isomorphism of
conflations. -/
theorem exists_iso_τ₃_eq_of_isAlmostSplit (E : ExactStructure C) (hS : E.Conflation S)
    (hS' : E.Conflation S') (ha : S.IsAlmostSplit) (ha' : S'.IsAlmostSplit) (e : S.X₃ ≅ S'.X₃) :
    ∃ f : S ≅ S', f.hom.τ₃ = e.hom := by
  obtain ⟨φ, hφ⟩ := ha'.isRightAlmostSplit_g.exists_hom_τ₃_eq_of_not_isSplitEpi
    (E.isKernelCokernelPair S' hS').fIsKernel e.hom
    (ha.isRightAlmostSplit_g.comp_iso e.hom).not_isSplitEpi
  have : IsIso φ.τ₃ := hφ ▸ inferInstanceAs (IsIso e.hom)
  have := E.isIso_of_isAlmostSplit_of_isIso_τ₃ hS hS' ha ha' φ
  exact ⟨asIso φ, hφ⟩

/-- **A morphism of almost-split conflations that is invertible at the left-hand end is
invertible**, by passage to the opposite exact structure. -/
theorem isIso_of_isAlmostSplit_of_isIso_τ₁ (E : ExactStructure C) (hS : E.Conflation S)
    (hS' : E.Conflation S') (ha : S.IsAlmostSplit) (ha' : S'.IsAlmostSplit) (φ : S ⟶ S')
    [IsIso φ.τ₁] : IsIso φ := by
  -- The components of `opMap φ` are the opposites of those of `φ`, in reverse order.
  have : IsIso (ShortComplex.opMap φ).τ₃ := inferInstanceAs (IsIso φ.τ₁.op)
  have := E.op.isIso_of_isAlmostSplit_of_isIso_τ₃ ((E.op_conflation_op_iff S').mpr hS')
    ((E.op_conflation_op_iff S).mpr hS) ha'.op ha.op (ShortComplex.opMap φ)
  have : IsIso φ.τ₂ := (isIso_op_iff φ.τ₂).mp
    (inferInstanceAs (IsIso ((ShortComplex.π₂ : _ ⥤ _).map (ShortComplex.opMap φ))))
  have : IsIso φ.τ₃ := (isIso_op_iff φ.τ₃).mp
    (inferInstanceAs (IsIso ((ShortComplex.π₁ : _ ⥤ _).map (ShortComplex.opMap φ))))
  exact ShortComplex.isIso_of_isIso φ

/-- **Uniqueness of the almost-split conflation at a given left-hand end**: an isomorphism between
the left-hand ends of two almost-split conflations is realized by an isomorphism of conflations. -/
theorem exists_iso_τ₁_eq_of_isAlmostSplit (E : ExactStructure C) (hS : E.Conflation S)
    (hS' : E.Conflation S') (ha : S.IsAlmostSplit) (ha' : S'.IsAlmostSplit) (e : S.X₁ ≅ S'.X₁) :
    ∃ f : S ≅ S', f.hom.τ₁ = e.hom := by
  obtain ⟨f, hf⟩ := E.op.exists_iso_τ₃_eq_of_isAlmostSplit ((E.op_conflation_op_iff S').mpr hS')
    ((E.op_conflation_op_iff S).mpr hS) ha'.op ha.op e.op
  let φ : S ⟶ S' := ShortComplex.unopMap f.hom
  -- The first component of `unopMap f.hom` is the opposite of its third component.
  have hφ : φ.τ₁ = e.hom := congrArg Quiver.Hom.unop hf
  have : IsIso φ.τ₁ := hφ ▸ inferInstanceAs (IsIso e.hom)
  have := E.isIso_of_isAlmostSplit_of_isIso_τ₁ hS hS' ha ha' φ
  exact ⟨asIso φ, hφ⟩

end ExactStructure

end TauCeti

namespace CategoryTheory.ShortComplex.ShortExact

open CategoryTheory.Abelian TauCeti

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C] {S : ShortComplex C}

/-- **The extension-class criterion in an abelian category**: a short exact sequence with local
right-hand endomorphism ring is almost split exactly when its class is nonzero and is killed by
pushforward along every map out of the first term that is not a split monomorphism. -/
theorem isAlmostSplit_iff_extClass (hS : S.ShortExact) [IsLocalRing (End S.X₃)] :
    S.IsAlmostSplit ↔ hS.extClass ≠ 0 ∧
      ∀ (N : C) (g : S.X₁ ⟶ N), ¬ IsSplitMono g →
        hS.extClass.comp (Ext.mk₀ g) (add_zero 1) = 0 :=
  (ExactStructure.Extension.isAlmostSplit_iff_isLeftAlmostSplit_f
    (E := ExactStructure.abelian C)
      ⟨S.X₂, S.f, S.g, S.zero, (ExactStructure.abelian_conflation _).mpr hS⟩).trans
      hS.isLeftAlmostSplit_f_iff_extClass

end CategoryTheory.ShortComplex.ShortExact
