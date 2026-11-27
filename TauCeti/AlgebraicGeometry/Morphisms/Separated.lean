/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed

import TauCeti.CategoryTheory.MorphismProperty.Limits

/-!
# Separated morphisms: a criterion from an open cover, and rigidity

A morphism `f : X ⟶ S` is separated when its diagonal `X ⟶ X ×_S X` is a closed immersion.
Given an open cover `{Uᵢ}` of `X`, the products `Uᵢ ×_S Uⱼ` cover `X ×_S X`, and the diagonal
restricted over `Uᵢ ×_S Uⱼ` is the canonical map `Uᵢ ×_X Uⱼ ⟶ Uᵢ ×_S Uⱼ` from the intersection of
the two pieces (`pullback.mapDesc`). Over `Uᵢ ×_S Uᵢ` this map is the diagonal of `Uᵢ ⟶ S`. So `f`
is separated as soon as each piece is separated over `S` and the maps `Uᵢ ×_X Uⱼ ⟶ Uᵢ ×_S Uⱼ` for
distinct pieces are closed immersions. When the pieces and `S` are affine and `Uᵢ ×_X Uⱼ` is affine,
the latter is the classical condition that the functions on `Uᵢ` and `Uⱼ` generate the functions on
the intersection.

This is the shape of Mathlib's proof that `Proj` is separated
(`AlgebraicGeometry.Proj.isSeparated`), with the computation on its affine charts abstracted away.
Mathlib's `AffineTargetMorphismProperty.diagonal_of_openCover_source` is the analogue for an affine
target and affine pieces, phrased for affine-target properties and asking for every pair of pieces;
here the target is arbitrary, and the pairs of equal pieces are replaced by the separatedness of
each piece over the target. It is the criterion used to show that a scheme glued from two affine
charts, such as the two-chart model of an algebraic function field, is separated.

Separated morphisms compose, so a scheme separated over a separated scheme is itself separated;
in particular a scheme proper over a separated base, such as a field, is a separated scheme.
Likewise the canonical map `X ×_S Y ⟶ X ×_T Y` over a separated `S ⟶ T` is a closed immersion, so
`X ×_S Y` is a closed subscheme of `X × Y` (through `AlgebraicGeometry.pullbackToProd`) when `S` is
a separated scheme.
A section of a separated morphism is a closed immersion, so a section with dense range is
surjective. Separatedness descends along universally closed surjections: if `f ≫ g` is separated
and `f` is universally closed and surjective, then `g` is separated, as the diagonal of `g` then
has closed range.

Morphisms from a reduced scheme to a separated one are determined by their values on a dense
set of points. Mathlib states this for a single dominant test morphism
(`AlgebraicGeometry.ext_of_isDominant_of_isSeparated`) and for the residue-field points
(`AlgebraicGeometry.ext_of_fromSpecResidueField_eq`); here the test points form an arbitrary
family, such as a Zariski-dense set of rational points. If the source is moreover irreducible,
the same holds up to a finite ambiguity: a morphism that agrees at each test point with some
member of a finite set `W` of morphisms is a member of `W`. The proof covers the source by the
finitely many closures of the sets of test points on which it agrees with a given member; by
irreducibility one of these is the whole space. This is the rigidity lemma of Kisin, Madapusi,
Pappas and Shin (KMPS22, Lemma 2.2.11), used to compare automorphisms of a torus that agree
pointwise with members of a finite group on a dense set of rational points.

## Main results

* `AlgebraicGeometry.IsSeparated.of_openCover`: `f` is separated if each piece of an open cover of
  its source is separated over the target and the pieces meet in closed subschemes of their
  products over the target.
* `AlgebraicGeometry.Scheme.IsSeparated.of_isSeparated`: the source of a separated morphism to a
  separated scheme is a separated scheme.
* `AlgebraicGeometry.isClosedImmersion_pullbackMap_id`: the canonical map `X ×_S Y ⟶ X ×_T Y` over
  a separated `S ⟶ T` is a closed immersion.
* `AlgebraicGeometry.surjective_of_isDominant_of_comp_eq_id`: a section of a separated morphism
  with dense range is surjective.
* `AlgebraicGeometry.IsSeparated.of_comp_surjective`: separatedness descends along universally
  closed surjections; the instance of `MorphismProperty.HasOfPrecompProperty` records this.
* `AlgebraicGeometry.isAffineHom_hasOfPostcompProperty`: since affine morphisms are separated,
  `f` is affine whenever `f ≫ g` and `g` are; this gives finite limits of affine schemes over a
  base, computed in schemes.
* `AlgebraicGeometry.ext_of_dense_iUnion_range_of_isSeparated`: morphisms from a reduced scheme
  agreeing over a separated morphism are equal if they agree on a family of morphisms with dense
  images.
* `AlgebraicGeometry.exists_mem_eq_of_dense_iUnion_range_of_isSeparated` and its variant `'` over
  a base scheme: rigidity under a finite set of morphisms from a reduced irreducible scheme.

## References

* [M. Kisin, K. Madapusi Pera, G. Pappas, S. W. Shin, *Honda–Tate theory for Shimura varieties*]
  (KMPS22), Lemma 2.2.11.
-/

public section

open CategoryTheory Limits

namespace AlgebraicGeometry

universe u

variable {X S : Scheme.{u}}

/-- **Separatedness from an open cover of the source.** If every piece `Uᵢ` of an open cover of
`X` is separated over `S`, and for distinct pieces the canonical map `Uᵢ ×_X Uⱼ ⟶ Uᵢ ×_S Uⱼ` is a
closed immersion, then `f : X ⟶ S` is separated. -/
theorem IsSeparated.of_openCover (f : X ⟶ S) (𝒰 : X.OpenCover) [∀ i, IsSeparated (𝒰.f i ≫ f)]
    (H : ∀ i j, i ≠ j → IsClosedImmersion (pullback.mapDesc (𝒰.f i) (𝒰.f j) f)) :
    IsSeparated f := by
  refine ⟨IsZariskiLocalAtTarget.of_openCover (Scheme.Pullback.openCoverOfLeftRight 𝒰 𝒰 f f) ?_⟩
  rintro ⟨i, j⟩
  -- Over `Uᵢ ×_S Uⱼ`, the diagonal of `f` is the base change of `Uᵢ ×_X Uⱼ ⟶ Uᵢ ×_S Uⱼ`.
  have h := pullback_map_diagonal_isPullback (𝒰.f i) (𝒰.f j) f
  -- `Cover.pullbackHom` is by definition `pullback.snd`, and the pieces of `openCoverOfLeftRight`
  -- are by definition these `pullback.map`s; but its index type is `𝒰.I₀ × 𝒰.I₀` only up to
  -- unfolding `Cover.copy`, which blocks rewriting, so `change` states the unfolded goal.
  change IsClosedImmersion (pullback.snd (pullback.diagonal f)
    (pullback.map (𝒰.f i ≫ f) (𝒰.f j ≫ f) f f (𝒰.f i) (𝒰.f j) (𝟙 S) (by simp) (by simp)))
  rw [← h.isoPullback_inv_snd, MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion]
  obtain rfl | hij := eq_or_ne i j
  · -- For a single piece, the map is the diagonal of `Uᵢ ⟶ S`, up to the isomorphism
    -- `Uᵢ ≅ Uᵢ ×_X Uᵢ` given by the diagonal of the open immersion `Uᵢ ⟶ X`.
    rw [← MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion
      (pullback.diagonal (𝒰.f i))]
    convert (inferInstance : IsClosedImmersion (pullback.diagonal (𝒰.f i ≫ f))) using 1
    ext <;> simp
  · exact H i j hij

/-- **A scheme separated over a separated scheme is separated.** If `f : X ⟶ S` is separated and
`S` is a separated scheme, then so is `X`, since `X ⟶ ⊤_ Scheme` factors as `f` followed by the
separated morphism `S ⟶ ⊤_ Scheme`. For instance, a scheme proper over a field is separated. -/
theorem Scheme.IsSeparated.of_isSeparated (f : X ⟶ S) [IsSeparated f] [S.IsSeparated] :
    X.IsSeparated :=
  ⟨by rw [← terminal.comp_from f]; infer_instance⟩

/-- **Separatedness descends along universally closed surjections**: if `f ≫ g` is separated and
`f : Y ⟶ X` is universally closed and surjective, then `g : X ⟶ S` is separated. Indeed `f ≫ Δ_g`
is the diagonal of `f ≫ g` followed by the universally closed map `f ×_S f`, so the diagonal `Δ_g`
of `g` has closed range; being an immersion, it is a closed immersion. -/
theorem IsSeparated.of_comp_surjective {Y : Scheme.{u}} (f : Y ⟶ X) (g : X ⟶ S)
    [IsSeparated (f ≫ g)] [UniversallyClosed f] [Surjective f] : IsSeparated g := by
  have : UniversallyClosed (f ≫ pullback.diagonal g) :=
    MorphismProperty.comp_diagonal f g ‹_› inferInstance
  have := UniversallyClosed.of_comp_surjective f (pullback.diagonal g)
  exact ⟨.of_isPreimmersion _ (pullback.diagonal g).isClosedMap.isClosed_range⟩

/-- Separatedness descends along universally closed surjections
(`IsSeparated.of_comp_surjective`). -/
instance : MorphismProperty.HasOfPrecompProperty @IsSeparated
    (@UniversallyClosed.{u} ⊓ @Surjective) where
  of_precomp f g hf (_ : IsSeparated (f ≫ g)) :=
    have : UniversallyClosed f := hf.1
    have : Surjective f := hf.2
    .of_comp_surjective f g

/-- **The canonical map `X ×_S Y ⟶ X ×_T Y` over a separated morphism is a closed immersion.**
Here `i : S ⟶ T` is separated and `f' : X ⟶ T`, `g' : Y ⟶ T` factor as `f ≫ i` and `g ≫ i`.
Mathlib's instance for `pullback.mapDesc` is the case where `f'` and `g'` are literally `f ≫ i` and
`g ≫ i`. For instance, `X ×_S Y ⟶ X × Y` is a closed immersion when `S` is a separated scheme. -/
instance isClosedImmersion_pullbackMap_id {Y T : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (f' : X ⟶ T) (g' : Y ⟶ T) (i : S ⟶ T) [IsSeparated i] (h₁ : f ≫ i = 𝟙 X ≫ f')
    (h₂ : g ≫ i = 𝟙 Y ≫ g') :
    IsClosedImmersion (pullback.map f g f' g' (𝟙 X) (𝟙 Y) i h₁ h₂) := by
  obtain rfl : f' = f ≫ i := by simpa using h₁.symm
  obtain rfl : g' = g ≫ i := by simpa using h₂.symm
  exact inferInstanceAs (IsClosedImmersion (pullback.mapDesc f g i))

/-- The canonical map `X ×_S Y ⟶ X × Y` from the fibre product over `S` to the product, that is,
the fibre product over the terminal scheme. It is a closed immersion when `S` is a separated
scheme, by `isClosedImmersion_pullbackMap_id`. -/
noncomputable abbrev pullbackToProd {Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    pullback f g ⟶ pullback (terminal.from X) (terminal.from Y) :=
  pullback.map f g _ _ (𝟙 X) (𝟙 Y) (terminal.from S) (terminal.hom_ext _ _) (terminal.hom_ext _ _)

/-- A section of a separated morphism with dense range is surjective: it is a closed immersion,
so its range is closed as well as dense. -/
theorem surjective_of_isDominant_of_comp_eq_id {Y : Scheme.{u}} {s : X ⟶ Y} {r : Y ⟶ X}
    [IsSeparated r] [IsDominant s] (hsr : s ≫ r = 𝟙 X) : Surjective s := by
  have : IsClosedImmersion (s ≫ r) := hsr ▸ inferInstance
  have : IsClosedImmersion s := IsClosedImmersion.of_comp s r
  exact surjective_of_isDominant_of_isClosed_range s s.isClosedEmbedding.isClosed_range

/-- If `f ≫ g` and `g` are affine, then so is `f`, because affine morphisms are separated. -/
instance isAffineHom_hasOfPostcompProperty :
    MorphismProperty.HasOfPostcompProperty @IsAffineHom @IsAffineHom :=
  .of_le _ @IsSeparated fun _ _ _ _ ↦ inferInstance

section Rigidity

variable {Y Z : Scheme.{u}}

/-- **Morphisms agreeing on a dense family of points are equal.** Let `X` be reduced and let
`f g : X ⟶ Y` agree over some separated `s : Y ⟶ Z`. If `γ i ≫ f = γ i ≫ g` for a family of
morphisms `γ i : T i ⟶ X` whose images together are dense, then `f = g`.

This generalizes `AlgebraicGeometry.ext_of_fromSpecResidueField_eq`, which tests on the canonical
residue-field points: here the test points may be arbitrary, for instance rational points
`Spec k ⟶ X` of a scheme over a field `k`. The proof adapts that of
`AlgebraicGeometry.ext_of_fromSpecResidueField_eq` in Mathlib. -/
theorem ext_of_dense_iUnion_range_of_isSeparated [IsReduced X] {f g : X ⟶ Y} (s : Y ⟶ Z)
    [IsSeparated s] (h : f ≫ s = g ≫ s) {ι : Type*} {T : ι → Scheme.{u}} (γ : ∀ i, T i ⟶ X)
    (hγ : Dense (⋃ i, Set.range (γ i))) (hfg : ∀ i, γ i ≫ f = γ i ≫ g) : f = g := by
  suffices IsDominant (equalizer.ι f g) from
    ext_of_isDominant_of_isSeparated s h (equalizer.ι f g) (equalizer.condition _ _)
  refine ⟨hγ.mono ?_⟩
  rintro _ ⟨_, ⟨i, rfl⟩, t, rfl⟩
  exact ⟨equalizer.lift (γ i) (hfg i) t, by rw [← Scheme.Hom.comp_apply, equalizer.lift_ι]⟩

/-- **Rigidity under a finite set of morphisms.** Let `X` be reduced and irreducible, `W` a finite
set of morphisms `X ⟶ Y` agreeing with `f` over some separated `s : Y ⟶ Z`, and `γ i : T i ⟶ X` a
family of morphisms whose images together are dense. If `f` agrees with some member of `W` on each
`γ i`, then `f` is a member of `W`.

The member may depend on `i`; the conclusion is that one member works everywhere. Typically `X`
is an algebraic torus over a field `k`, the `γ i` are a Zariski-dense set of `k`-points, and `W` a
finite group of automorphisms (KMPS22, Lemma 2.2.11). Reducedness is needed: on
`Spec k[ε]/(ε²)`, `ε ↦ 2ε` fixes the unique point. So is separatedness: on the affine line with
doubled origin, exchanging the origins fixes the dense punctured line. -/
theorem exists_mem_eq_of_dense_iUnion_range_of_isSeparated [IsReduced X] [IrreducibleSpace X]
    (s : Y ⟶ Z) [IsSeparated s] (f : X ⟶ Y) {W : Set (X ⟶ Y)} (hW : W.Finite)
    (hWs : ∀ w ∈ W, w ≫ s = f ≫ s) {ι : Type*} {T : ι → Scheme.{u}} (γ : ∀ i, T i ⟶ X)
    (hγ : Dense (⋃ i, Set.range (γ i))) (hfγ : ∀ i, ∃ w ∈ W, γ i ≫ f = γ i ≫ w) :
    ∃ w ∈ W, f = w := by
  classical
  -- The points of the family on which `f` agrees with `w`.
  let A (w : X ⟶ Y) : Set X := ⋃ i : {i // γ i ≫ f = γ i ≫ w}, Set.range (γ i)
  have hcover : (Set.univ : Set X) ⊆ ⋃₀ ↑(hW.toFinset.image fun w ↦ closure (A w)) := by
    rw [← hγ.closure_eq, Finset.coe_image, Set.sUnion_image, Set.Finite.coe_toFinset,
      ← hW.closure_biUnion]
    refine closure_mono (Set.iUnion_subset fun i ↦ ?_)
    obtain ⟨w, hw, hiw⟩ := hfγ i
    exact (Set.subset_iUnion_of_subset ⟨i, hiw⟩ subset_rfl).trans
      (Set.subset_biUnion_of_mem (u := A) hw)
  obtain ⟨_, hz, hsub⟩ := isIrreducible_iff_sUnion_isClosed.mp
    (IrreducibleSpace.isIrreducible_univ X) _ (by simp) hcover
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
  rw [Set.Finite.mem_toFinset] at hw
  exact ⟨w, hw, ext_of_dense_iUnion_range_of_isSeparated s (hWs w hw).symm
    (fun i : {i // γ i ≫ f = γ i ≫ w} ↦ γ i) (fun x ↦ hsub (Set.mem_univ x)) fun i ↦ i.property⟩

variable (S) in
/-- **Rigidity under a finite set of `S`-morphisms.** Let `X` be a reduced, irreducible
`S`-scheme and `Y` a separated `S`-scheme, for instance over `S = Spec k` for a field `k`. If an
`S`-morphism `f : X ⟶ Y` agrees, on each member of a family of morphisms `γ i : T i ⟶ X` with
dense images, with some member of a finite set `W` of `S`-morphisms, then `f` is a member of `W`.
See `exists_mem_eq_of_dense_iUnion_range_of_isSeparated`. -/
theorem exists_mem_eq_of_dense_iUnion_range_of_isSeparated' [X.Over S] [Y.Over S] [IsReduced X]
    [IrreducibleSpace X] [IsSeparated (Y ↘ S)] (f : X ⟶ Y) [f.IsOver S] {W : Set (X ⟶ Y)}
    (hW : W.Finite) (hWS : ∀ w ∈ W, w.IsOver S) {ι : Type*} {T : ι → Scheme.{u}}
    (γ : ∀ i, T i ⟶ X) (hγ : Dense (⋃ i, Set.range (γ i)))
    (hfγ : ∀ i, ∃ w ∈ W, γ i ≫ f = γ i ≫ w) : ∃ w ∈ W, f = w :=
  exists_mem_eq_of_dense_iUnion_range_of_isSeparated (Y ↘ S) f hW
    (fun w hw ↦ by have := hWS w hw; simp) γ hγ hfγ

end Rigidity

end AlgebraicGeometry
