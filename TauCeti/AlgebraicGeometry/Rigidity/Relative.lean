/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Rigidity.Basic
import TauCeti.AlgebraicGeometry.Descent.GeometricFibers
import TauCeti.AlgebraicGeometry.Morphisms.Flat.StructureSheaf

/-!
# The relative rigidity lemma over an arbitrary base scheme

Let `S` be an arbitrary scheme and let `X`, `Y`, `Z` be schemes over `S` such that:
* `X ⟶ S` is proper and geometrically integral, and satisfies `X.hom_* 𝒪_X = 𝒪_S` (it suffices to
  require `Γ(S, V) ≅ Γ(X, X.hom⁻¹ V)` on affine opens `V` of `S`);
* `Y ⟶ S` is flat, locally of finite type, and geometrically integral;
* `Z ⟶ S` is separated and locally of finite type.

Suppose `f : X ×_S Y ⟶ Z` is a morphism over `S` whose restriction to one slice `X ×_S {y₀}` along
a section `y₀` of `Y ⟶ S` is a constant section `z₀` of `Z ⟶ S`. The **relative rigidity lemma**
asserts that `f` factors uniquely through the second projection `pr₂ : X ×_S Y ⟶ Y` as a morphism
over `S` (`TauCeti.AlgebraicGeometry.existsUnique_snd_comp_eq_of_flat`). No section of `X ⟶ S`, no
reducedness of `S`, and no Noetherian hypothesis are required. When `X ⟶ S` also admits a section
`x₀`, the descended morphism is `y ↦ f(x₀, y)`, so `f(x, y) = f(x₀, y)`
(`TauCeti.AlgebraicGeometry.eq_snd_comp_lift_comp_of_flat`).

The proof combines contraction descent (`AlgebraicGeometry.Scheme.Hom.descOfIsQuotientMap`) with
the rigidity lemma over algebraically closed fields
(`TauCeti.AlgebraicGeometry.eq_snd_comp_lift_comp_of_isAlgClosed`):
1. Because `X ⟶ S` is proper and surjective (`GeometricallyIntegral` implies `Surjective`) and
   `Y ⟶ S` is flat, flat base change for `X.hom_* 𝒪_X = 𝒪_S`
   (`TauCeti.AlgebraicGeometry.isIso_app_pullback_snd_of_flat`) shows that the second projection
   `c : X ×_S Y ⟶ Y` is universally closed, surjective, and satisfies `c_* 𝒪_{X ×_S Y} = 𝒪_Y`.
2. By `AlgebraicGeometry.Scheme.Hom.factorsThrough_iff_forall_isAlgClosed_subsingleton_range`, to
   descend `f` uniquely along `c` it suffices to show that for every algebraically closed field `K`
   and every `K`-valued point `y : Spec K ⟶ Y`, the restriction of `f` to the geometric fibre of
   `c` over `y` has at most one image point.
3. Base-changing `X`, `Y`, `Z`, and `f` to `Spec K` along `y ≫ Y.hom` produces a proper
   geometrically integral scheme `X_K` over the algebraically closed field `K` (which has a
   `K`-rational point by Hilbert's Nullstellensatz) and an integral product `X_K ×_K Y_K`. Applying
   `eq_snd_comp_lift_comp_of_isAlgClosed` over `Spec K` shows that `f_K` factors through `Y_K`, so
   its restriction to the fibre over `y` factors through the one-point scheme `Spec K`.

Over a field `K`, flatness of `Y` and `X.hom_* 𝒪_X = 𝒪_{Spec K}` hold automatically, yielding the
section-free specialization `TauCeti.AlgebraicGeometry.existsUnique_snd_comp_eq`.

## Main results

* `TauCeti.AlgebraicGeometry.existsUnique_snd_comp_eq_of_flat`: the relative rigidity lemma over an
  arbitrary scheme `S`, without requiring a section of `X ⟶ S`.
* `TauCeti.AlgebraicGeometry.eq_snd_comp_lift_comp_of_flat`: the explicit factorization
  `f = snd X Y ≫ lift (toUnit Y ≫ x₀) (𝟙 Y) ≫ f` when `X ⟶ S` has a section `x₀`.
* `TauCeti.AlgebraicGeometry.existsUnique_fst_comp_eq_of_flat` and
  `TauCeti.AlgebraicGeometry.eq_fst_comp_lift_comp_of_flat`: the symmetric statements factoring
  through the first projection `X ×_S Y ⟶ X`.
* `TauCeti.AlgebraicGeometry.existsUnique_snd_comp_eq`: the section-free rigidity lemma over an
  arbitrary field `K`.

## References

* [The Stacks Project, Tag 0BF6](https://stacks.math.columbia.edu/tag/0BF6).
* D. Mumford, J. Fogarty, F. Kirwan, *Geometric Invariant Theory*, Proposition 6.1.
* S. Bosch, W. Lütkebohmert, M. Raynaud, *Néron Models*, Section 8.1, Lemma 2.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

namespace TauCeti

namespace AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

section Relative

variable {S : Scheme.{u}}

/-- If the base change of `f : X ⊗ Y ⟶ Z` along `s = y ≫ Y.hom` factors through the second
projection in `Over R`, then the restriction of `f.left` to the fibre of `pullback.snd X.hom Y.hom`
over `y : R ⟶ Y.left` factors through `pullback.snd _ y : _ ⟶ R`. -/
private theorem exists_pullback_snd_comp_eq_of_pullback {X Y Z : Over S} (f : X ⊗ Y ⟶ Z)
    {R : Scheme.{u}} (y : R ⟶ Y.left)
    {gR : (Over.pullback (y ≫ Y.hom)).obj Y ⟶ (Over.pullback (y ≫ Y.hom)).obj Z}
    (hgR : Functor.LaxMonoidal.μ (Over.pullback (y ≫ Y.hom)) X Y ≫
      (Over.pullback (y ≫ Y.hom)).map f = snd _ _ ≫ gR) :
    ∃ h : R ⟶ Z.left,
      pullback.fst (pullback.snd X.hom Y.hom) y ≫ f.left =
        pullback.snd (pullback.snd X.hom Y.hom) y ≫ h := by
  let c := pullback.snd X.hom Y.hom
  let s := y ≫ Y.hom
  let F : Over S ⥤ Over R := Over.pullback s
  let wX : pullback c y ⟶ (F.obj X).left :=
    pullback.lift (pullback.fst c y ≫ pullback.fst X.hom Y.hom) (pullback.snd c y)
      (by rw [Category.assoc, pullback.condition, pullback.condition_assoc])
  let yR : R ⟶ (F.obj Y).left := pullback.lift y (𝟙 R) (by simp [s])
  let φ : pullback c y ⟶ pullback (F.obj X).hom (F.obj Y).hom :=
    pullback.lift wX (pullback.snd c y ≫ yR) (by simp [F, wX, yR])
  have hμ : φ ≫ (Functor.LaxMonoidal.μ F X Y).left ≫ pullback.fst (X ⊗ Y).hom s =
      pullback.fst c y := by
    apply pullback.hom_ext
    · have h1 := congrArg Over.Hom.left (Functor.Monoidal.μ_fst F X Y) =≫ pullback.fst X.hom s
      simp only [Over.comp_left, Over.fst_left, Category.assoc] at h1
      have h1' : (F.map (fst X Y)).left ≫ pullback.fst X.hom s =
          pullback.fst (X ⊗ Y).hom s ≫ pullback.fst X.hom Y.hom := by simp [F]
      rw [h1'] at h1
      rw [Category.assoc φ, Category.assoc _ _ (pullback.fst X.hom Y.hom), h1]
      simp [φ, F, wX]
    · have h2 := congrArg Over.Hom.left (Functor.Monoidal.μ_snd F X Y) =≫ pullback.fst Y.hom s
      simp only [Over.comp_left, Over.snd_left, Category.assoc] at h2
      have h2' : (F.map (snd X Y)).left ≫ pullback.fst Y.hom s =
          pullback.fst (X ⊗ Y).hom s ≫ pullback.snd X.hom Y.hom := by simp [F]
      rw [h2'] at h2
      rw [Category.assoc φ, Category.assoc _ _ (pullback.snd X.hom Y.hom), h2]
      simp [φ, F, yR, c, pullback.condition]
  have hmap : (F.map f).left ≫ pullback.fst Z.hom s = pullback.fst (X ⊗ Y).hom s ≫ f.left := by
    simp [F]
  refine ⟨yR ≫ gR.left ≫ pullback.fst Z.hom s, ?_⟩
  calc pullback.fst c y ≫ f.left
    _ = φ ≫ (Functor.LaxMonoidal.μ F X Y ≫ F.map f).left ≫ pullback.fst Z.hom s := by
      rw [Over.comp_left, Category.assoc, hmap, ← Category.assoc _ _ f.left, ← Category.assoc φ, hμ]
    _ = pullback.snd c y ≫ yR ≫ gR.left ≫ pullback.fst Z.hom s := by
      rw [hgR, Over.comp_left]
      simp [φ, F, s, Category.assoc]

/-- **The relative rigidity lemma.** Let `X`, `Y`, `Z` be schemes over an arbitrary base scheme `S`,
with `X` proper and geometrically integral over `S` satisfying `X.hom_* 𝒪_X = 𝒪_S`, `Y` flat,
locally of finite type and geometrically integral over `S`, and `Z` separated and locally of finite
type over `S`. If `f : X ×_S Y ⟶ Z` collapses the slice `X ×_S {y₀}` along a section `y₀` of `Y`
to a section `z₀` of `Z`, then `f` factors uniquely through the second projection `X ×_S Y ⟶ Y` in
`Over S`. No section of `X ⟶ S` is required. -/
theorem existsUnique_snd_comp_eq_of_flat {X Y Z : Over S}
    [IsProper X.hom] [GeometricallyIntegral X.hom]
    (hX : ∀ V : S.affineOpens, IsIso (X.hom.app V))
    [Flat Y.hom] [LocallyOfFiniteType Y.hom] [GeometricallyIntegral Y.hom]
    [IsSeparated Z.hom] [LocallyOfFiniteType Z.hom]
    (f : X ⊗ Y ⟶ Z) (y₀ : 𝟙_ (Over S) ⟶ Y) (z₀ : 𝟙_ (Over S) ⟶ Z)
    (hf : lift (𝟙 X) (toUnit X ≫ y₀) ≫ f = toUnit X ≫ z₀) :
    ∃! g : Y ⟶ Z, snd X Y ≫ g = f := by
  let c : (X ⊗ Y).left ⟶ Y.left := (snd X Y).left
  have hc_eq : c = pullback.snd X.hom Y.hom := Over.snd_left
  have : UniversallyClosed c := by rw [hc_eq]; infer_instance
  have : Surjective c := by rw [hc_eq]; infer_instance
  have hq : Topology.IsQuotientMap c := c.isClosedMap.isQuotientMap c.continuous c.surjective
  have hc : ∀ U : Y.left.Opens, IsIso (c.app U) := fun U ↦ by
    rw [hc_eq]; exact isIso_app_pullback_snd_of_flat X.hom Y.hom hX U
  -- Check constancy on geometric fibres by pulling back along any point `y : Spec K ⟶ Y`
  -- with `K` algebraically closed and applying the rigidity lemma over `Spec K`.
  have hconst : Function.FactorsThrough f.left c := by
    rw [c.factorsThrough_iff_forall_isAlgClosed_subsingleton_range f.left, hc_eq]
    intro K _ _ y
    let F : Over S ⥤ Over (Spec (.of K)) := Over.pullback (y ≫ Y.hom)
    have : IsProper (F.obj X).hom := by dsimp [F]; infer_instance
    have : GeometricallyIntegral (F.obj X).hom := by dsimp [F]; infer_instance
    have : IsIntegral (F.obj X).left :=
      GeometricallyIntegral.isIntegral_of_subsingleton (F.obj X).hom
    have : LocallyOfFiniteType (F.obj X).hom := by dsimp [F]; infer_instance
    have : JacobsonSpace (F.obj X).left := LocallyOfFiniteType.jacobsonSpace (F.obj X).hom
    have : LocallyOfFiniteType (F.obj Y).hom := by dsimp [F]; infer_instance
    have : GeometricallyIntegral (F.obj Y).hom := by dsimp [F]; infer_instance
    have : IsIntegral (F.obj Y).left :=
      GeometricallyIntegral.isIntegral_of_subsingleton (F.obj Y).hom
    have : IsLocallyNoetherian (F.obj Y).left := by dsimp [F]; infer_instance
    have : IsIntegral (F.obj X ⊗ F.obj Y).left :=
      GeometricallyIntegral.isIntegral_of_isLocallyNoetherian
        (pullback.snd (F.obj X).hom (F.obj Y).hom)
    have : IsSeparated (F.obj Z).hom := by dsimp [F]; infer_instance
    have : LocallyOfFiniteType (F.obj Z).hom := by dsimp [F]; infer_instance
    obtain ⟨pt, -, hpt⟩ := nonempty_inter_closedPoints (X := (F.obj X).left) Set.univ_nonempty
      isOpen_univ.isLocallyClosed
    let x₀ : 𝟙_ (Over (Spec (.of K))) ⟶ F.obj X :=
      Over.homMk (pointOfClosedPoint (F.obj X).hom pt hpt)
        (by dsimp; exact pointOfClosedPoint_comp (F.obj X).hom pt hpt)
    have H := eq_snd_comp_lift_comp_of_isAlgClosed
      (Functor.LaxMonoidal.μ F X Y ≫ F.map f) x₀
      (Functor.LaxMonoidal.ε F ≫ F.map y₀) (Functor.LaxMonoidal.ε F ≫ F.map z₀) (by
        rw [← Category.assoc, ← F.map_id, Functor.Monoidal.toUnit_ε_assoc, ← F.map_comp,
          Functor.Monoidal.lift_μ, ← F.map_comp, hf, F.map_comp,
          Functor.Monoidal.toUnit_ε_assoc])
    obtain ⟨h, hfactor⟩ := exists_pullback_snd_comp_eq_of_pullback f y H
    rw [hfactor]
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    simp only [Scheme.Hom.comp_apply,
      Subsingleton.elim (pullback.snd (pullback.snd X.hom Y.hom) y a)
        (pullback.snd (pullback.snd X.hom Y.hom) y b)]
  refine ⟨Over.homMk (c.descOfIsQuotientMap hq hc f.left hconst)
      (c.descOfIsQuotientMap_comp_eq hq hc f.left hconst
        ((Over.w f).trans (Over.w (snd X Y)).symm)),
    Over.OverMorphism.ext (c.comp_descOfIsQuotientMap hq hc f.left hconst),
    fun g hg ↦ Over.OverMorphism.ext
      (c.eq_descOfIsQuotientMap hq hc f.left hconst (congrArg Over.Hom.left hg))⟩

/-- **The relative rigidity lemma with a section.** Under the hypotheses of
`existsUnique_snd_comp_eq_of_flat`, if `X ⟶ S` also has a section `x₀`, then
`f(x, y) = f(x₀, y)`, that is, `f = snd X Y ≫ lift (toUnit Y ≫ x₀) (𝟙 Y) ≫ f`. -/
theorem eq_snd_comp_lift_comp_of_flat {X Y Z : Over S}
    [IsProper X.hom] [GeometricallyIntegral X.hom]
    (hX : ∀ V : S.affineOpens, IsIso (X.hom.app V))
    [Flat Y.hom] [LocallyOfFiniteType Y.hom] [GeometricallyIntegral Y.hom]
    [IsSeparated Z.hom] [LocallyOfFiniteType Z.hom]
    (f : X ⊗ Y ⟶ Z) (x₀ : 𝟙_ (Over S) ⟶ X) (y₀ : 𝟙_ (Over S) ⟶ Y) (z₀ : 𝟙_ (Over S) ⟶ Z)
    (hf : lift (𝟙 X) (toUnit X ≫ y₀) ≫ f = toUnit X ≫ z₀) :
    f = snd X Y ≫ lift (toUnit Y ≫ x₀) (𝟙 Y) ≫ f := by
  obtain ⟨g, hg, -⟩ := existsUnique_snd_comp_eq_of_flat hX f y₀ z₀ hf
  have hgx₀ : g = lift (toUnit Y ≫ x₀) (𝟙 Y) ≫ f := by
    rw [← hg, lift_snd_assoc, Category.id_comp]
  rw [← hgx₀, hg]

/-- **The relative rigidity lemma, first projection.** Symmetric form of
`existsUnique_snd_comp_eq_of_flat`: if `Y` is proper and geometrically integral over `S` with
`Y.hom_* 𝒪_Y = 𝒪_S`, `X` is flat, locally of finite type and geometrically integral over `S`, `Z`
is separated and locally of finite type over `S`, and `f : X ×_S Y ⟶ Z` collapses `{x₀} ×_S Y` to
`z₀`, then `f` factors uniquely through `fst X Y`. -/
theorem existsUnique_fst_comp_eq_of_flat {X Y Z : Over S}
    [Flat X.hom] [LocallyOfFiniteType X.hom] [GeometricallyIntegral X.hom]
    [IsProper Y.hom] [GeometricallyIntegral Y.hom]
    (hY : ∀ V : S.affineOpens, IsIso (Y.hom.app V))
    [IsSeparated Z.hom] [LocallyOfFiniteType Z.hom]
    (f : X ⊗ Y ⟶ Z) (x₀ : 𝟙_ (Over S) ⟶ X) (z₀ : 𝟙_ (Over S) ⟶ Z)
    (hf : lift (toUnit Y ≫ x₀) (𝟙 Y) ≫ f = toUnit Y ≫ z₀) :
    ∃! g : X ⟶ Z, fst X Y ≫ g = f := by
  have hf' : lift (𝟙 Y) (toUnit Y ≫ x₀) ≫ (β_ Y X).hom ≫ f = toUnit Y ≫ z₀ := by
    rw [← Category.assoc, ← hf]
    congr 1
    ext1 <;> simp
  obtain ⟨g, hg, huniq⟩ := existsUnique_snd_comp_eq_of_flat hY ((β_ Y X).hom ≫ f) x₀ z₀ hf'
  refine ⟨g, ?_, fun g' hg' ↦ huniq g' ?_⟩
  · dsimp only
    rw [← cancel_epi (β_ Y X).hom, ← Category.assoc, braiding_hom_fst, hg]
  · rw [← hg', ← Category.assoc, braiding_hom_fst]

/-- **The relative rigidity lemma with a section, first projection.** Symmetric form of
`eq_snd_comp_lift_comp_of_flat`. -/
theorem eq_fst_comp_lift_comp_of_flat {X Y Z : Over S}
    [Flat X.hom] [LocallyOfFiniteType X.hom] [GeometricallyIntegral X.hom]
    [IsProper Y.hom] [GeometricallyIntegral Y.hom]
    (hY : ∀ V : S.affineOpens, IsIso (Y.hom.app V))
    [IsSeparated Z.hom] [LocallyOfFiniteType Z.hom]
    (f : X ⊗ Y ⟶ Z) (x₀ : 𝟙_ (Over S) ⟶ X) (y₀ : 𝟙_ (Over S) ⟶ Y) (z₀ : 𝟙_ (Over S) ⟶ Z)
    (hf : lift (toUnit Y ≫ x₀) (𝟙 Y) ≫ f = toUnit Y ≫ z₀) :
    f = fst X Y ≫ lift (𝟙 X) (toUnit X ≫ y₀) ≫ f := by
  obtain ⟨g, hg, -⟩ := existsUnique_fst_comp_eq_of_flat hY f x₀ z₀ hf
  have hgy₀ : g = lift (𝟙 X) (toUnit X ≫ y₀) ≫ f := by
    rw [← hg, lift_fst_assoc, Category.id_comp]
  rw [← hgy₀, hg]

end Relative

section Field

variable {K : Type u} [Field K]

/-- **The section-free rigidity lemma over a field.** Let `X` be proper and geometrically integral
over a field `K`, `Y` geometrically integral and locally of finite type over `K`, and `Z` separated
and locally of finite type over `K`. If `f : X ×_K Y ⟶ Z` collapses the slice `X ×_K {y₀}` over a
`K`-rational point `y₀` of `Y` to a `K`-rational point `z₀` of `Z`, then `f` factors uniquely
through `snd X Y : X ×_K Y ⟶ Y`, even if `X` has no `K`-rational point. -/
theorem existsUnique_snd_comp_eq {X Y Z : Over (Spec (.of K))}
    [IsProper X.hom] [GeometricallyIntegral X.hom]
    [LocallyOfFiniteType Y.hom] [GeometricallyIntegral Y.hom]
    [IsSeparated Z.hom] [LocallyOfFiniteType Z.hom]
    (f : X ⊗ Y ⟶ Z) (y₀ : 𝟙_ (Over (Spec (.of K))) ⟶ Y) (z₀ : 𝟙_ (Over (Spec (.of K))) ⟶ Z)
    (hf : lift (𝟙 X) (toUnit X ≫ y₀) ≫ f = toUnit X ≫ z₀) :
    ∃! g : Y ⟶ Z, snd X Y ≫ g = f :=
  existsUnique_snd_comp_eq_of_flat
    (fun V ↦ X.hom.isIso_app_of_universallyClosed_of_geometricallyIntegral V) f y₀ z₀ hf

end Field

end AlgebraicGeometry

end TauCeti
