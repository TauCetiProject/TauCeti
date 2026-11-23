/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Birational.Composition
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# Base change of rational maps

Consider cartesian squares `X' = X ×_S S'` and `Y' = Y ×_S S'` along a morphism `p : S' ⟶ S`, with
projections `πX : X' ⟶ X` and `πY : Y' ⟶ Y`, and an `S`-rational map `f : X ⤏ Y`. Its base change
is the `S'`-rational map `f' : X' ⤏ Y'` defined on `πX⁻¹(U)` for a representative `f_U` of `f`, as
the map `(πX, f_U ∘ πX)` into the fibre product. This file characterizes it, without fixing a
choice, as the unique `S'`-rational map with `πY ∘ f' = f ∘ πX`, in Mathlib's terms
`f'.compHom πY = πX.toRationalMap.comp f`. For a field extension `K'/K` and a geometrically
integral `X`, this is the rational map `f_{K'}` of the dynamical-degrees roadmap.

Uniqueness only uses that `Y'` is the fibre product: two `S'`-rational maps into `Y'` whose
composites with `πY` agree, agree on a dense open by the universal property. It needs no
hypothesis on `X'`.

## Main definitions

* `AlgebraicGeometry.Scheme.PartialMap.baseChange`: the base change of an `S`-partial map, defined
  on the preimage of its domain.

## Main results

* `AlgebraicGeometry.Scheme.RationalMap.eq_of_compHom_eq_of_isPullback`: `S'`-rational maps into
  `Y'` are determined by their composites with `πY`.
* `AlgebraicGeometry.Scheme.RationalMap.existsUnique_compHom_eq_comp`: for `X'` irreducible and
  `πX` dominant, there is a unique `S'`-rational map `f'` with
  `f'.compHom πY = πX.toRationalMap.comp f`.
* `AlgebraicGeometry.Scheme.dense_preimage_of_isPullback`: the preimage of a dense open under the
  base change of a universally open morphism, such as `Spec K' ⟶ Spec K`, is dense.
* `AlgebraicGeometry.Scheme.RationalMap.compHom_comp_eq_comp`: base change commutes with
  composition, `(g ∘ f)' = g' ∘ f'`.

## References

* TauCetiRoadmap, `DynamicalDegreesOfRationalMaps/README.md`, §1.4 (extension of the field).
-/

public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme

variable {X Y X' Y' S S' : Scheme.{u}}

/-- Two `S'`-partial maps into a fibre product `Y' = Y ×_S S'` are equivalent when their composites
with the projection `Y' ⟶ Y` are. -/
theorem PartialMap.equiv_of_compHom_equiv_of_isPullback {πY : Y' ⟶ Y} {sY' : Y' ⟶ S'}
    {sY : Y ⟶ S} {p : S' ⟶ S} (hY : IsPullback πY sY' sY p) {sX' : X' ⟶ S'}
    {f₁ f₂ : X'.PartialMap Y'} [f₁.IsOver sX' sY'] [f₂.IsOver sX' sY']
    (h : (f₁.compHom πY).equiv (f₂.compHom πY)) : f₁.equiv f₂ := by
  obtain ⟨W, hW, hW₁ : W ≤ f₁.domain, hW₂ : W ≤ f₂.domain, e⟩ := h
  have e' : X'.homOfLE hW₁ ≫ f₁.hom ≫ πY = X'.homOfLE hW₂ ≫ f₂.hom ≫ πY := e
  have key : X'.homOfLE hW₁ ≫ f₁.hom = X'.homOfLE hW₂ ≫ f₂.hom := by
    refine hY.hom_ext (by simpa using e') ?_
    simp [f₁.over sX' sY', f₂.over sX' sY']
  exact ⟨W, hW, hW₁, hW₂, key⟩

/-- Two `S'`-rational maps into a fibre product `Y' = Y ×_S S'` are equal when their composites
with the projection `Y' ⟶ Y` are. -/
theorem RationalMap.eq_of_compHom_eq_of_isPullback {πY : Y' ⟶ Y} {sY' : Y' ⟶ S'}
    {sY : Y ⟶ S} {p : S' ⟶ S} (hY : IsPullback πY sY' sY p) {sX' : X' ⟶ S'}
    {f₁ f₂ : X' ⤏ Y'} [f₁.IsOver sX' sY'] [f₂.IsOver sX' sY']
    (h : f₁.compHom πY = f₂.compHom πY) : f₁ = f₂ := by
  obtain ⟨g₁, _, rfl⟩ := f₁.exists_partialMap_over sX' sY'
  obtain ⟨g₂, _, rfl⟩ := f₂.exists_partialMap_over sX' sY'
  rw [← RationalMap.compHom_toRationalMap, ← RationalMap.compHom_toRationalMap,
    PartialMap.toRationalMap_eq_iff] at h
  exact PartialMap.toRationalMap_eq_iff.mpr
    (PartialMap.equiv_of_compHom_equiv_of_isPullback (sX' := sX') hY h)

/-- The preimage of a dense open under the base change of a universally open morphism is dense. -/
theorem dense_preimage_of_isPullback {πX : X' ⟶ X} {sX' : X' ⟶ S'} {sX : X ⟶ S} {p : S' ⟶ S}
    (hX : IsPullback πX sX' sX p) [UniversallyOpen p] {U : X.Opens} (hU : Dense (U : Set X)) :
    Dense (πX ⁻¹ᵁ U : Set X') := by
  have : UniversallyOpen πX := MorphismProperty.of_isPullback hX.flip inferInstance
  exact hU.preimage πX.isOpenMap

/-- The base change of an `S`-partial map `f : X ⤏ Y` to an `S'`-partial map `X' ⤏ Y'`, where
`Y' = Y ×_S S'` and `πX : X' ⟶ X` lies over `S' ⟶ S`: it is defined on `πX⁻¹(dom f)`, where it is
the morphism into `Y'` with components `f ∘ πX` and the structure morphism of `X'`. -/
@[expose, simps domain]
noncomputable def PartialMap.baseChange {πY : Y' ⟶ Y} {sY' : Y' ⟶ S'} {sY : Y ⟶ S}
    {p : S' ⟶ S} (hY : IsPullback πY sY' sY p) {sX : X ⟶ S} (f : X.PartialMap Y)
    [f.IsOver sX sY] (πX : X' ⟶ X) (sX' : X' ⟶ S') (w : πX ≫ sX = sX' ≫ p)
    (hd : Dense (πX ⁻¹ᵁ f.domain : Set X')) : X'.PartialMap Y' where
  domain := πX ⁻¹ᵁ f.domain
  dense_domain := hd
  hom := hY.lift (πX ∣_ f.domain ≫ f.hom) ((πX ⁻¹ᵁ f.domain).ι ≫ sX') <| by
    rw [Category.assoc, f.over sX sY, morphismRestrict_ι_assoc, w, Category.assoc]

/-- On the domain of a composite of partial maps, the first map followed by the inclusion of the
domain of the second is the first map. -/
private theorem homOfLE_isoImage_inv_morphismRestrict_ι (D : X'.Opens) (h : D.toScheme ⟶ X)
    (U : X.Opens) (W : X'.Opens) (hW : W ≤ D.ι ''ᵁ h ⁻¹ᵁ U) (hWD : W ≤ D) :
    X'.homOfLE hW ≫ (D.ι.isoImage (h ⁻¹ᵁ U)).inv ≫ h ∣_ U ≫ U.ι = X'.homOfLE hWD ≫ h := by
  simp only [morphismRestrict_ι, Opens.isoImage_ι_inv_ι_assoc, homOfLE_homOfLE_assoc]

section baseChange

variable {πY : Y' ⟶ Y} {sY' : Y' ⟶ S'} {sY : Y ⟶ S} {p : S' ⟶ S}
  (hY : IsPullback πY sY' sY p) {sX : X ⟶ S} (f : X.PartialMap Y)
  [f.IsOver sX sY] (πX : X' ⟶ X) (sX' : X' ⟶ S') (w : πX ≫ sX = sX' ≫ p)
  (hd : Dense (πX ⁻¹ᵁ f.domain : Set X'))

/-- The base change of `f` followed by the projection to `Y` is `f ∘ πX`. -/
theorem PartialMap.baseChange_hom_fst :
    (f.baseChange hY πX sX' w hd).hom ≫ πY = πX ∣_ f.domain ≫ f.hom :=
  hY.lift_fst _ _ _

/-- The base change of `f` followed by the structure morphism of `Y'` is the structure morphism
of `X'`. -/
theorem PartialMap.baseChange_hom_snd :
    (f.baseChange hY πX sX' w hd).hom ≫ sY' = (πX ⁻¹ᵁ f.domain).ι ≫ sX' :=
  hY.lift_snd _ _ _

/-- The base change of an `S`-partial map is an `S'`-partial map. -/
instance PartialMap.isOver_baseChange : (f.baseChange hY πX sX' w hd).IsOver sX' sY' :=
  ⟨f.baseChange_hom_snd hY πX sX' w hd⟩

/-- The base change `f'` of `f` satisfies `πY ∘ f' = f ∘ πX` as rational maps. -/
theorem PartialMap.baseChange_compHom_toRationalMap [PreirreducibleSpace X'] [Nonempty X]
    [IsDominant πX] :
    (f.baseChange hY πX sX' w hd).toRationalMap.compHom πY =
      πX.toRationalMap.comp f.toRationalMap := by
  rw [RationalMap.toRationalMap_comp, ← RationalMap.compHom_toRationalMap,
    PartialMap.toRationalMap_eq_iff]
  have hle : πX ⁻¹ᵁ f.domain ≤
      πX.toPartialMap.domain.ι ''ᵁ πX.toPartialMap.hom ⁻¹ᵁ f.domain :=
    fun x hx ↦ ⟨⟨x, trivial⟩, hx, rfl⟩
  refine ⟨πX ⁻¹ᵁ f.domain, hd, le_rfl, hle, ?_⟩
  change X'.homOfLE le_rfl ≫ (f.baseChange hY πX sX' w hd).hom ≫ πY = _
  have key : X'.homOfLE (le_refl (πX ⁻¹ᵁ f.domain)) ≫ πX ∣_ f.domain =
      X'.homOfLE hle ≫ (πX.toPartialMap.domain.ι.isoImage _).inv ≫
        πX.toPartialMap.hom ∣_ f.domain := by
    rw [← cancel_mono f.domain.ι]
    calc _ = X'.homOfLE (le_top : πX ⁻¹ᵁ f.domain ≤ ⊤) ≫ X'.topIso.hom ≫ πX := by simp
      _ = _ := by
        simp only [Category.assoc]
        exact (homOfLE_isoImage_inv_morphismRestrict_ι _ _ _ _ hle le_top).symm
  exact (congrArg (X'.homOfLE le_rfl ≫ ·) (f.baseChange_hom_fst hY πX sX' w hd)).trans
    ((reassoc_of% key) f.hom)

end baseChange

/-- The preimage of a nonempty open under a dominant morphism from a preirreducible scheme is
dense. -/
theorem dense_preimage_of_isDominant [PreirreducibleSpace X'] (πX : X' ⟶ X) [IsDominant πX]
    {U : X.Opens} (hU : (U : Set X).Nonempty) : Dense (πX ⁻¹ᵁ U : Set X') :=
  (πX ⁻¹ᵁ U).isOpen.dense <| by
    simpa [← Set.nonempty_preimage_iff] using
      πX.denseRange.inter_open_nonempty _ U.isOpen hU

/-- **Characterization of the base change of a rational map.** Let `Y' = Y ×_S S'`, let `X'` be
a preirreducible `S'`-scheme with a dominant morphism `πX : X' ⟶ X` over `S' ⟶ S`, and let
`f : X ⤏ Y` be an `S`-rational map. There is a unique `S'`-rational map `f' : X' ⤏ Y'` with
`πY ∘ f' = f ∘ πX`. -/
theorem RationalMap.existsUnique_compHom_eq_comp {πY : Y' ⟶ Y} {sY' : Y' ⟶ S'} {sY : Y ⟶ S}
    {p : S' ⟶ S} (hY : IsPullback πY sY' sY p) {sX : X ⟶ S} (f : X ⤏ Y) [f.IsOver sX sY]
    (πX : X' ⟶ X) (sX' : X' ⟶ S') (w : πX ≫ sX = sX' ≫ p) [PreirreducibleSpace X']
    [Nonempty X] [IsDominant πX] :
    ∃! f' : X' ⤏ Y', f'.IsOver sX' sY' ∧ f'.compHom πY = πX.toRationalMap.comp f := by
  obtain ⟨g, _, rfl⟩ := f.exists_partialMap_over sX sY
  have hd := dense_preimage_of_isDominant πX g.dense_domain.nonempty
  refine ⟨(g.baseChange hY πX sX' w hd).toRationalMap, ⟨inferInstance,
    g.baseChange_compHom_toRationalMap hY πX sX' w hd⟩, fun f' ⟨_, hf'⟩ ↦ ?_⟩
  exact eq_of_compHom_eq_of_isPullback hY (sX' := sX')
    (hf'.trans (g.baseChange_compHom_toRationalMap hY πX sX' w hd).symm)

/-- Composing a composite of partial maps with a morphism. -/
theorem PartialMap.comp_compHom {Z W : Scheme.{u}} [PreirreducibleSpace X] [Nonempty Y]
    (f : X.PartialMap Y) [IsDominant f.hom] (g : Y.PartialMap Z) (h : Z ⟶ W) :
    (f.comp g).compHom h = f.comp (g.compHom h) := by
  simp only [PartialMap.comp, PartialMap.compHom, Category.assoc]

/-- Composing a composite of rational maps with a morphism. -/
theorem RationalMap.comp_compHom {Z W : Scheme.{u}} [PreirreducibleSpace X] [Nonempty Y]
    (f : X ⤏ Y) [f.IsDominant] (g : Y ⤏ Z) (h : Z ⟶ W) :
    (f.comp g).compHom h = f.comp (g.compHom h) := by
  obtain ⟨g, rfl⟩ := g.exists_rep
  rw [← compHom_toRationalMap, comp_def, comp_def, ← compHom_toRationalMap,
    PartialMap.comp_compHom]

/-- **Base change commutes with composition.** If `f'` and `g'` satisfy the characterizing
identities `πY ∘ f' = f ∘ πX` and `πZ ∘ g' = g ∘ πY`, then `g' ∘ f'` satisfies the one of `g ∘ f`.
Together with `RationalMap.eq_of_compHom_eq_of_isPullback` this gives `(g ∘ f)' = g' ∘ f'`. -/
theorem RationalMap.compHom_comp_eq_comp {Z Z' : Scheme.{u}} {πX : X' ⟶ X} {πY : Y' ⟶ Y}
    {πZ : Z' ⟶ Z} [PreirreducibleSpace X'] [IrreducibleSpace X] [IrreducibleSpace Y']
    [Nonempty Y] [IsDominant πX] [IsDominant πY]
    {f : X ⤏ Y} [f.IsDominant] {g : Y ⤏ Z} {f' : X' ⤏ Y'} [f'.IsDominant] {g' : Y' ⤏ Z'}
    (hf : f'.compHom πY = πX.toRationalMap.comp f) (hg : g'.compHom πZ = πY.toRationalMap.comp g) :
    (f'.comp g').compHom πZ = πX.toRationalMap.comp (f.comp g) := by
  have key : (f'.comp πY.toRationalMap).comp g = (πX.toRationalMap.comp f).comp g := by
    simp_rw [comp_toRationalMap, hf]
  rw [comp_compHom, hg, ← comp_assoc, key, comp_assoc]

end AlgebraicGeometry.Scheme
