/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FiniteEtale.Fiber
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import TauCeti.AlgebraicGeometry.Morphisms.FormallyUnramified

/-!
# Fullness of restriction of finite étale schemes is Zariski local

Let `U` be a dense open subscheme of a scheme `X` and `𝒰` an open cover of `X`. If, over every
chart `Xᵢ` of `𝒰`, restriction of finite étale schemes to the preimage of `U` is full, then
restriction of finite étale schemes over `X` to `U` is full.

Given a morphism `φ` over `U` between the restrictions of finite étale schemes `Y`, `Y'` over `X`,
fullness over `Xᵢ` extends `φ` to a morphism from `Y ×_X Xᵢ` to `Y'` over `X`. These extensions
are glued with `AlgebraicGeometry.Scheme.OpenCover.glueMorphisms`. They agree on overlaps because
two morphisms into a finite étale scheme agree as soon as they agree over a dense open subset of
an étale source, and the preimage of the dense open `U` in an overlap, which is étale over `X`, is
dense.

## Main results

* `TauCeti.FiniteEtaleScheme.full_pullback_ι_of_openCover`: restriction to a dense open `U` is full
  if it is full over every chart of an open cover.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace TauCeti.FiniteEtaleScheme

section Glue

variable {X Y Y' : Scheme.{u}} (U : X.Opens) {p : Y ⟶ X} {p' : Y' ⟶ X}

/-- The base change of `p` along `f`, restricted further to `f ⁻¹ᵁ U`, maps to the restriction of
`p` to `U`. -/
private noncomputable def toRestrict {T : Scheme.{u}} (f : T ⟶ X) (p : Y ⟶ X) :
    Limits.pullback (Limits.pullback.snd p f) (f ⁻¹ᵁ U).ι ⟶ Limits.pullback p U.ι :=
  Limits.pullback.lift (Limits.pullback.fst _ _ ≫ Limits.pullback.fst _ _)
    (Limits.pullback.snd _ _ ≫ f ∣_ U) (by
      simp [Limits.pullback.condition, ← Limits.pullback.condition_assoc])

/-- A morphism `φ` between the restrictions of `p` and `p'` to `U`, base changed along `f` to a
morphism between the restrictions of their base changes to `f ⁻¹ᵁ U`. -/
private noncomputable def restrictMap {T : Scheme.{u}} (f : T ⟶ X)
    (φ : Limits.pullback p U.ι ⟶ Limits.pullback p' U.ι)
    (hφ : φ ≫ Limits.pullback.snd _ _ = Limits.pullback.snd _ _) :
    Limits.pullback (Limits.pullback.snd p f) (f ⁻¹ᵁ U).ι ⟶
      Limits.pullback (Limits.pullback.snd p' f) (f ⁻¹ᵁ U).ι :=
  Limits.pullback.lift
    (Limits.pullback.lift (toRestrict U f p ≫ φ ≫ Limits.pullback.fst _ _)
      (Limits.pullback.fst _ _ ≫ Limits.pullback.snd _ _) (by
        simp [toRestrict, Limits.pullback.condition, reassoc_of% hφ,
          ← Limits.pullback.condition_assoc]))
    (Limits.pullback.snd _ _) (by simp [Limits.pullback.condition])

/-- `restrictMap` is a morphism over `f ⁻¹ᵁ U`. -/
private theorem restrictMap_snd {T : Scheme.{u}} (f : T ⟶ X)
    (φ : Limits.pullback p U.ι ⟶ Limits.pullback p' U.ι)
    (hφ : φ ≫ Limits.pullback.snd _ _ = Limits.pullback.snd _ _) :
    restrictMap U f φ hφ ≫ Limits.pullback.snd _ _ = Limits.pullback.snd _ _ :=
  Limits.pullback.lift_snd _ _ _

/-- A morphism `ψ` between the base changes along `f` which restricts over `f ⁻¹ᵁ U` to
`restrictMap U f φ hφ` agrees with `φ` on every point of the base change lying over `U`. -/
private theorem comp_fst_eq_of_fst_comp_eq_restrictMap {T : Scheme.{u}} (f : T ⟶ X)
    (φ : Limits.pullback p U.ι ⟶ Limits.pullback p' U.ι)
    (hφ : φ ≫ Limits.pullback.snd _ _ = Limits.pullback.snd _ _)
    (ψ : Limits.pullback p f ⟶ Limits.pullback p' f)
    (hψ : Limits.pullback.fst _ _ ≫ ψ = restrictMap U f φ hφ ≫ Limits.pullback.fst _ _)
    {S : Scheme.{u}} (t : S ⟶ Limits.pullback p f) (s : S ⟶ Limits.pullback p U.ι)
    (h : t ≫ Limits.pullback.fst _ _ = s ≫ Limits.pullback.fst _ _) :
    t ≫ ψ ≫ Limits.pullback.fst _ _ = s ≫ φ ≫ Limits.pullback.fst _ _ := by
  have hts : t ≫ Limits.pullback.snd _ _ ≫ f = s ≫ Limits.pullback.snd _ _ ≫ U.ι := by
    rw [← Limits.pullback.condition, ← Limits.pullback.condition, reassoc_of% h]
  -- The point `t` lies over `f ⁻¹ᵁ U`, so it factors through the restriction of `p`.
  let q : S ⟶ f ⁻¹ᵁ U := Limits.pullback.lift (f := f) (g := U.ι)
    (t ≫ Limits.pullback.snd _ _) (s ≫ Limits.pullback.snd _ _) (by simpa using hts) ≫
      (pullbackRestrictIsoRestrict f U).hom
  let r : S ⟶ Limits.pullback (Limits.pullback.snd p f) (f ⁻¹ᵁ U).ι :=
    Limits.pullback.lift t q (by simp [q])
  have hr : r ≫ toRestrict U f p = s := by
    apply Limits.pullback.hom_ext
    · simp [r, toRestrict, h]
    · simp [r, q, toRestrict]
  calc t ≫ ψ ≫ Limits.pullback.fst _ _
      = r ≫ (Limits.pullback.fst _ _ ≫ ψ) ≫ Limits.pullback.fst _ _ := by simp [r]
    _ = s ≫ φ ≫ Limits.pullback.fst _ _ := by simp [hψ, restrictMap, reassoc_of% hr]

/-- Let `f : T ⟶ X` be a chart over which restriction to `f ⁻¹ᵁ U` is full. A morphism `φ` over
`U` between the restrictions of finite étale schemes `Y`, `Y'` over `X` then extends to a morphism
over `X` from the base change of `Y` along `f` to `Y'`, agreeing with `φ` over `U`. -/
private theorem exists_extension_of_full {Y Y' : FiniteEtaleScheme X} {T : Scheme.{u}}
    (f : T ⟶ X) [hf : (pullback (f ⁻¹ᵁ U).ι).Full]
    (φ : Limits.pullback Y.obj.hom U.ι ⟶ Limits.pullback Y'.obj.hom U.ι)
    (hφ : φ ≫ Limits.pullback.snd _ _ = Limits.pullback.snd _ _) :
    ∃ g : Limits.pullback Y.obj.hom f ⟶ Y'.obj.left,
      g ≫ Y'.obj.hom = Limits.pullback.fst _ _ ≫ Y.obj.hom ∧
      ∀ {S : Scheme.{u}} (t : S ⟶ Limits.pullback Y.obj.hom f)
        (s : S ⟶ Limits.pullback Y.obj.hom U.ι),
        t ≫ Limits.pullback.fst _ _ = s ≫ Limits.pullback.fst _ _ →
          t ≫ g = s ≫ φ ≫ Limits.pullback.fst _ _ := by
  obtain ⟨ψ, hψ⟩ := (pullback (f ⁻¹ᵁ U).ι).map_surjective
    (ObjectProperty.homMk (Over.homMk (restrictMap U f φ hφ) (restrictMap_snd ..)) :
      (pullback (f ⁻¹ᵁ U).ι).obj ((pullback f).obj Y) ⟶
        (pullback (f ⁻¹ᵁ U).ι).obj ((pullback f).obj Y'))
  have hψf : ((pullback (f ⁻¹ᵁ U).ι).map ψ).hom.left ≫ Limits.pullback.fst _ _ =
      Limits.pullback.fst _ _ ≫ ψ.hom.left :=
    Limits.pullback.lift_fst _ _ _
  rw [hψ] at hψf
  -- Record the underlying morphism of schemes with its type as a morphism of pullbacks.
  obtain ⟨ψl, hψs, hψf⟩ : ∃ ψl : Limits.pullback Y.obj.hom f ⟶ Limits.pullback Y'.obj.hom f,
      ψl ≫ Limits.pullback.snd _ _ = Limits.pullback.snd _ _ ∧
        Limits.pullback.fst _ _ ≫ ψl = restrictMap U f φ hφ ≫ Limits.pullback.fst _ _ :=
    ⟨ψ.hom.left, Over.w ψ.hom, hψf.symm⟩
  refine ⟨ψl ≫ Limits.pullback.fst _ _, ?_, fun t s h ↦
    comp_fst_eq_of_fst_comp_eq_restrictMap U f φ hφ _ hψf t s h⟩
  rw [Category.assoc, Limits.pullback.condition (f := Y'.obj.hom) (g := f), reassoc_of% hψs]
  exact Limits.pullback.condition.symm

end Glue

variable {X : Scheme.{u}}

/-- **Fullness of restriction is Zariski local.** Let `U` be a dense open subscheme of `X` and `𝒰`
an open cover of `X` such that over every chart `Xᵢ`, restriction of finite étale schemes to the
preimage of `U` is full. Then restriction of finite étale schemes over `X` to `U` is full. -/
theorem full_pullback_ι_of_openCover (U : X.Opens) (hU : Dense (U : Set X)) (𝒰 : X.OpenCover)
    (H : ∀ i, (pullback (𝒰.f i ⁻¹ᵁ U).ι).Full) : (pullback U.ι).Full := by
  refine ⟨fun {Y Y'} φ ↦ ?_⟩
  let φl : Limits.pullback Y.obj.hom U.ι ⟶ Limits.pullback Y'.obj.hom U.ι := φ.hom.left
  have hφ : φl ≫ Limits.pullback.snd _ _ = Limits.pullback.snd _ _ := Over.w φ.hom
  -- Extend `φ` over each chart, then glue the extensions along the cover `𝒱` of `Y`.
  choose g hg key using fun i ↦ exists_extension_of_full U (hf := H i) (𝒰.f i) φl hφ
  let 𝒱 : Y.obj.left.OpenCover := 𝒰.pullback₁ Y.obj.hom
  -- On an overlap the two extensions agree over the preimage of `U`, which is dense since the
  -- overlap is étale over `X`.
  have hcompat (i j : 𝒰.I₀) :
      Limits.pullback.fst (Limits.pullback.fst Y.obj.hom (𝒰.f i))
          (Limits.pullback.fst Y.obj.hom (𝒰.f j)) ≫ g i =
        Limits.pullback.snd _ _ ≫ g j := by
    let z := Limits.pullback.fst (Limits.pullback.fst Y.obj.hom (𝒰.f i))
      (Limits.pullback.fst Y.obj.hom (𝒰.f j)) ≫ Limits.pullback.fst _ _ ≫ Y.obj.hom
    have := Opens.isDominant_ι (U := z ⁻¹ᵁ U) (hU.preimage z.isOpenMap)
    refine ext_of_isDominant_of_isSeparated_of_formallyUnramified Y'.obj.hom ?_
      (z ⁻¹ᵁ U).ι ?_
    · simp only [Category.assoc, hg, Limits.pullback.condition_assoc]
    · -- The right side of `morphismRestrict_ι` is `z` itself, which is a local definition.
      let s : (z ⁻¹ᵁ U).toScheme ⟶ Limits.pullback Y.obj.hom U.ι :=
        Limits.pullback.lift ((z ⁻¹ᵁ U).ι ≫ Limits.pullback.fst _ _ ≫ Limits.pullback.fst _ _)
          (z ∣_ U) (by rw [morphismRestrict_ι]; rfl)
      rw [← Category.assoc, ← Category.assoc (z ⁻¹ᵁ U).ι, key i _ s (by simp [s]),
        key j _ s (by simp [s, Limits.pullback.condition])]
  let G := 𝒱.glueMorphisms g hcompat
  have hG (i : 𝒰.I₀) : Limits.pullback.fst Y.obj.hom (𝒰.f i) ≫ G = g i :=
    𝒱.ι_glueMorphisms g hcompat i
  have hGY : G ≫ Y'.obj.hom = Y.obj.hom :=
    𝒱.hom_ext _ _ fun i ↦ (congrArg (· ≫ Y'.obj.hom) (hG i)).trans (hg i)
  -- The glued morphism restricts to `φ`, as checked on the cover of `Y ×_X U` induced by `𝒱`.
  have hGφ : Limits.pullback.fst Y.obj.hom U.ι ≫ G = φl ≫ Limits.pullback.fst _ _ := by
    have hloc (i : 𝒰.I₀) :
        Limits.pullback.fst (Limits.pullback.fst Y.obj.hom U.ι)
            (Limits.pullback.fst Y.obj.hom (𝒰.f i)) ≫ Limits.pullback.fst Y.obj.hom U.ι ≫ G =
          Limits.pullback.fst _ _ ≫ φl ≫ Limits.pullback.fst _ _ := by
      have hc := Limits.pullback.condition (f := Limits.pullback.fst Y.obj.hom U.ι)
        (g := Limits.pullback.fst Y.obj.hom (𝒰.f i))
      rw [← Category.assoc, hc, Category.assoc, hG]
      exact key i _ _ hc.symm
    exact Scheme.Cover.hom_ext (𝒱.pullback₁ (Limits.pullback.fst Y.obj.hom U.ι)) _ _ hloc
  refine ⟨ObjectProperty.homMk (Over.homMk G hGY), ?_⟩
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  apply Limits.pullback.hom_ext
  · exact (Limits.pullback.lift_fst _ _ _).trans hGφ
  · exact (Limits.pullback.lift_snd _ _ _).trans hφ.symm

end TauCeti.FiniteEtaleScheme
