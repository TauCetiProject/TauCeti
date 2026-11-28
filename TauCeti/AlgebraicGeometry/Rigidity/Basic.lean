/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import TauCeti.AlgebraicGeometry.Morphisms.Contraction
import TauCeti.AlgebraicGeometry.AffineScheme.Factorization
import TauCeti.AlgebraicGeometry.Morphisms.Flat.StructureSheaf
import TauCeti.AlgebraicGeometry.Morphisms.Flat.Reduced

/-!
# The rigidity lemma over a field

Let `X` be a proper scheme over a field `K`, let `X ×_K Y` be integral, and let `Z` be
separated over `K`. If a morphism `f : X ×_K Y ⟶ Z` is constant on the fibre over a rational
point of `Y`, then it factors through the second projection, given a rational point of `X`
(`eq_snd_comp_lift_comp_of_isIntegral`).

For integral `X` with a rational point, the second projection is a contraction for arbitrary `Y`
(`isContraction_snd_left_of_isIntegral`), by `appTop_bijective_of_section` and flat base change
for functions. Closedness of the projection
lets us restrict to an open neighbourhood over which `f` lands in an affine open of `Z`.
There it factors through the projection by the isomorphism on functions. The factorization
extends by `AlgebraicGeometry.ext_of_isDominant_of_isSeparated`.

## References

* D. Mumford, *Abelian Varieties*, Section 4, the rigidity lemma.
* J. S. Milne, *Abelian Varieties* (2022), Theorem 1.1.
-/

public section

open Filter Topology CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

namespace TauCeti

namespace AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

variable {K : Type u} [Field K]

/-- The fibre of the second projection `X × Y ⟶ Y` over a `K`-rational point `y` of `Y` is the
range of the map `X × Y ⟶ X × Y`, `(x, y') ↦ (x, y)`. -/
lemma preimage_snd_left_eq_range_whiskerLeft_left (X Y : Over (Spec (.of K)))
    (y : 𝟙_ (Over (Spec (.of K))) ⟶ Y) :
    (snd X Y).left ⁻¹' {y.left (IsLocalRing.closedPoint K)} =
      Set.range (X ◁ (toUnit Y ≫ y)).left := by
  have (a : Y.left) : (toUnit Y ≫ y).left a = y.left (IsLocalRing.closedPoint K) := by
    rw [Over.comp_left, Scheme.Hom.comp_apply]
    exact congr_arg y.left (Subsingleton.elim (α := Spec (.of K)) _ _)
  rw [Over.whiskerLeft_left, Scheme.Pullback.range_map]
  ext z
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_range, this,
    Over.snd_left]
  exact ⟨fun h ↦ ⟨⟨_, rfl⟩, (snd X Y).left z, h.symm⟩, fun ⟨_, _, hb⟩ ↦ hb.symm⟩

/-- Let `f : X ⟶ Y` and `g : Y ⟶ S` with `f ≫ g` proper and `g` separated and locally of finite
type. If `f` has finite image on the fibre of `f ≫ g` over `s`, then the same holds over every
point of a neighbourhood of `s`. This is a consequence of Zariski's main theorem. -/
theorem exists_forall_finite_image_preimage_of_finite_image_preimage
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) (s : S)
    (H : (f '' ((f ≫ g) ⁻¹' {s})).Finite)
    [IsProper (f ≫ g)] [IsSeparated g] [LocallyOfFiniteType g] :
    ∃ U : S.Opens, s ∈ U ∧ ∀ t ∈ U, (f '' ((f ≫ g) ⁻¹' {t})).Finite := by
  obtain ⟨U, hsU, hU⟩ :=
    exists_finite_imageι_comp_morphismRestrict_of_finite_image_preimage f g s H
  refine ⟨U, hsU, fun t ht ↦ ?_⟩
  obtain ⟨t, rfl⟩ : t ∈ Set.range U.ι := by rwa [Scheme.Opens.range_ι]
  let h := f.imageι ≫ g
  refine (((h ∣_ U).finite_preimage_singleton t).image ((h ⁻¹ᵁ U).ι ≫ f.imageι)).subset ?_
  rintro _ ⟨x, hx, rfl⟩
  have hhx : h (f.toImage x) = U.ι t := by
    rw [← hx, ← Scheme.Hom.comp_apply, Scheme.Hom.toImage_imageι_assoc]
  obtain ⟨x', hx'⟩ : f.toImage x ∈ Set.range (h ⁻¹ᵁ U).ι := by
    rwa [Scheme.Opens.range_ι, SetLike.mem_coe, Scheme.Hom.mem_preimage, hhx]
  refine ⟨x', U.ι.isOpenEmbedding.injective ?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply, hx', hhx]
  · rw [Scheme.Hom.comp_apply, hx', ← Scheme.Hom.comp_apply, Scheme.Hom.toImage_imageι]

/-- If `X` is proper and integral over a field and has a rational point, then the second
projection `X × Y ⟶ Y` is a contraction for every `Y` over that field. -/
theorem isContraction_snd_left_of_isIntegral {X Y : Over (Spec (.of K))}
    [IsProper X.hom] [IsIntegral X.left]
    (x₀ : 𝟙_ _ ⟶ X) : IsContraction (snd X Y).left := by
  have hx : x₀.left ≫ X.hom = 𝟙 (Spec (.of K)) := x₀.w
  have hΓ : IsIso X.hom.appTop :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (appTop_bijective_of_section hx)
  rw [Over.snd_left]
  exact ⟨fun U ↦ isIso_app_pullback_snd_of_flat X.hom Y.hom
    (fun V ↦ X.hom.isIso_app_of_isIso_appTop V) U⟩

/-- A morphism that is constant on a rational slice sends the points in the corresponding
fibre of the second projection to that single point. -/
lemma mapsTo_preimage_snd_left_of_comp_eq {X Y Z : Over (Spec (.of K))}
    (f : X ⊗ Y ⟶ Z) (y₀ : 𝟙_ _ ⟶ Y) {z₀ : 𝟙_ _ ⟶ Z}
    (hf : lift (𝟙 X) (toUnit X ≫ y₀) ≫ f = toUnit X ≫ z₀) :
    Set.MapsTo f.left ((snd X Y).left ⁻¹' {y₀.left (IsLocalRing.closedPoint K)})
      {z₀.left (IsLocalRing.closedPoint K)} := by
  have hslice : (X ◁ (toUnit Y ≫ y₀)) ≫ f = toUnit (X ⊗ Y) ≫ z₀ := by
    have : X ◁ (toUnit Y ≫ y₀) = fst X Y ≫ lift (𝟙 X) (toUnit X ≫ y₀) := by
      ext1 <;> simp
    rw [this, Category.assoc, hf, ← Category.assoc, toUnit_unique (fst X Y ≫ toUnit X)]
  rw [preimage_snd_left_eq_range_whiskerLeft_left]
  rintro _ ⟨x, rfl⟩
  -- Evaluate the collapsed-slice equation at the chosen point of the product.
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hslice, Over.comp_left, Scheme.Hom.comp_apply,
    Set.mem_singleton_iff]
  exact congrArg z₀.left (Subsingleton.elim (α := Spec (.of K)) _ _)

/-- **The rigidity lemma** over a field `K`. Let `X` be proper over `K`, with `X × Y`
integral and `Z` separated over `K`. If `f : X × Y ⟶ Z` sends the fibre
`X × {y₀}` over a `K`-point `y₀` of `Y` to a `K`-point `z₀` of `Z`, then
`f (x, y) = f (x₀, y)` for any `K`-point `x₀` of `X`. -/
theorem eq_snd_comp_lift_comp_of_isIntegral {X Y Z : Over (Spec (.of K))}
    [IsProper X.hom] [IsIntegral (X ⊗ Y).left] [IsSeparated Z.hom]
    (f : X ⊗ Y ⟶ Z) (x₀ : 𝟙_ _ ⟶ X) (y₀ : 𝟙_ _ ⟶ Y) (z₀ : 𝟙_ _ ⟶ Z)
    (hf : lift (𝟙 X) (toUnit X ≫ y₀) ≫ f = toUnit X ≫ z₀) :
    f = snd X Y ≫ lift (toUnit Y ≫ x₀) (𝟙 Y) ≫ f := by
  let point : Spec (.of K) := IsLocalRing.closedPoint K
  let p := (snd X Y).left
  let a := (lift (toUnit Y ≫ x₀) (𝟙 Y)).left
  have ha : a ≫ p = 𝟙 _ := by rw [← Over.comp_left, lift_snd, Over.id_left]
  obtain ⟨V, hV, hzV, -⟩ := exists_isAffineOpen_mem_and_subset
    (TopologicalSpace.Opens.mem_top (z₀.left point))
  have : IsIntegral X.left := by
    let b := (lift (𝟙 X) (toUnit X ≫ y₀)).left
    have : Surjective (b ≫ (fst X Y).left) := by
      rw [← Over.comp_left, lift_fst, Over.id_left]; infer_instance
    have : Surjective (fst X Y).left := Surjective.of_comp b _
    have hr := (fst X Y).left.surjective
    have : IrreducibleSpace X.left := hr.irreducibleSpace (fst X Y).left.continuous
    have : Flat (fst X Y).left := by rw [Over.fst_left]; infer_instance
    have (x : X.left) : _root_.IsReduced (X.left.presheaf.stalk x) := by
      obtain ⟨z, rfl⟩ := hr x
      exact (fst X Y).left.isReduced_stalk_of_flat z
    have : IsReduced X.left := isReduced_of_isReduced_stalk X.left
    exact isIntegral_of_irreducibleSpace_of_isReduced X.left
  have : IsContraction p := isContraction_snd_left_of_isIntegral x₀
  have hnear := p.isClosedMap.eventually_nhds_fiber (p := fun x ↦ f.left x ∈ V)
    (y₀.left point) (fun x hx ↦ V.isOpen.preimage f.left.continuous |>.mem_nhds
      (Set.mem_preimage.mpr
        ((Set.mem_singleton_iff.mp (mapsTo_preimage_snd_left_of_comp_eq f y₀ hf hx)).symm ▸ hzV)))
  obtain ⟨U, hU, hUopen, hyU⟩ := mem_nhds_iff.mp hnear
  let W : Y.left.Opens := ⟨U, hUopen⟩
  have hrestrict :
      (p ⁻¹ᵁ W).ι ≫ f.left = (p ⁻¹ᵁ W).ι ≫ (p ≫ a ≫ f.left) := by
    have : IsIso (p ∣_ W).appTop := IsContraction.isIso_app (f := p ∣_ W) ⊤
    exact p.comp_eq_comp_section_of_preimage_le ha f.left hV (fun x hx ↦ hU hx x rfl)
  have : IsDominant (p ⁻¹ᵁ W).ι :=
    Opens.isDominant_ι ((p ⁻¹ᵁ W).isOpen.dense ⟨(lift x₀ y₀).left point, by
      apply (Scheme.Hom.mem_preimage _).mpr
      have hp' : p = (snd X Y).left := rfl
      rwa [hp', ← Scheme.Hom.comp_apply, ← Over.comp_left, lift_snd]⟩)
  have hbase := (Over.w f).trans (Over.w (snd X Y ≫ lift (toUnit Y ≫ x₀) (𝟙 Y) ≫ f)).symm
  exact Over.OverMorphism.ext
    (ext_of_isDominant_of_isSeparated Z.hom hbase _ hrestrict)

end AlgebraicGeometry

end TauCeti
