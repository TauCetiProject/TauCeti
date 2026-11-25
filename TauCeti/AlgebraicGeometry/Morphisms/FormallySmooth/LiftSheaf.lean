/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import TauCeti.AlgebraicGeometry.Morphisms.FormallySmooth.LiftTorsor
import Mathlib.AlgebraicGeometry.Gluing

/-!
# The sheaf of lifts along a first-order thickening

Let `f : X ⟶ S` be a morphism of schemes, `i : T ⟶ T'` a morphism with `T` and `T'` over `S`
through `a : T ⟶ X` and `h : T' ⟶ S`. Over an open `U` of `T'`, the lifts of `a` along `i` are the
morphisms `U ⟶ X` over `S` restricting to `a` on `i⁻¹(U)`
(`TauCeti.AlgebraicGeometry.ThickeningLift (i ∣_ U) ((i ⁻¹ᵁ U).ι ≫ a) f (U.ι ≫ h)`). Restricting
lifts to smaller opens makes them a presheaf of sets on `T'`
(`TauCeti.AlgebraicGeometry.liftPresheaf i a f h`), and since morphisms of schemes glue along open
covers it is a sheaf (`TauCeti.AlgebraicGeometry.isSheaf_liftPresheaf`). For `f` smooth and `i` a
first-order thickening, the sheaf of lifts has a section near every point of `T'`
(`TauCeti.AlgebraicGeometry.exists_mem_and_nonempty_liftPresheaf`), and by
`TauCeti.AlgebraicGeometry.ThickeningLift.instAddTorsor` its nonempty sets of sections are torsors
under derivations. This is the sheaf of lifts of Stacks, Lemma 37.9.5 (04FJ).

## Main definitions

* `TauCeti.AlgebraicGeometry.ThickeningLift.restrictLE`: restricting a lift over `U` to `V ≤ U`.
* `TauCeti.AlgebraicGeometry.liftPresheaf i a f h`: the presheaf of lifts on `T'`.

## Main results

* `TauCeti.AlgebraicGeometry.isSheaf_liftPresheaf`: the presheaf of lifts is a sheaf.
* `TauCeti.AlgebraicGeometry.exists_mem_and_nonempty_liftPresheaf`: for `f` smooth and `i` a
  first-order thickening, lifts exist locally on `T'`.

## References

* [Stacks Project, Lemma 37.9.5](https://stacks.math.columbia.edu/tag/04FJ): the sheaf of lifts
  is a torsor.
-/

public section

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace TauCeti.AlgebraicGeometry

variable {X S T T' : Scheme.{u}} {i : T ⟶ T'} {a : T ⟶ X} {f : X ⟶ S} {h : T' ⟶ S}

namespace ThickeningLift

/-- Restricting a lift over an open `U` of `T'` to an open `V ≤ U`. -/
@[expose] noncomputable def restrictLE {U V : T'.Opens} (hVU : V ≤ U)
    (b : ThickeningLift (i ∣_ U) ((i ⁻¹ᵁ U).ι ≫ a) f (U.ι ≫ h)) :
    ThickeningLift (i ∣_ V) ((i ⁻¹ᵁ V).ι ≫ a) f (V.ι ≫ h) where
  hom := T'.homOfLE hVU ≫ b.hom
  comp_hom := by
    have e : i ∣_ V ≫ T'.homOfLE hVU = T.homOfLE (i.preimage_mono hVU) ≫ i ∣_ U := by
      rw [← cancel_mono U.ι]
      simp
    rw [reassoc_of% e, b.comp_hom, Scheme.homOfLE_ι_assoc]
  hom_comp := by rw [Category.assoc, b.hom_comp, Scheme.homOfLE_ι_assoc]

/-- The restriction of a lift is its composite with the inclusion of opens. -/
@[simp]
theorem restrictLE_hom {U V : T'.Opens} (hVU : V ≤ U)
    (b : ThickeningLift (i ∣_ U) ((i ⁻¹ᵁ U).ι ≫ a) f (U.ι ≫ h)) :
    (restrictLE hVU b).hom = T'.homOfLE hVU ≫ b.hom :=
  (rfl)

/-- Restricting a lift to the same open does nothing. -/
@[simp]
theorem restrictLE_rfl {U : T'.Opens}
    (b : ThickeningLift (i ∣_ U) ((i ⁻¹ᵁ U).ι ≫ a) f (U.ι ≫ h)) :
    restrictLE le_rfl b = b := by
  ext1
  simp

/-- Restricting a lift twice is restricting it once. -/
theorem restrictLE_restrictLE {U V W : T'.Opens} (hVU : V ≤ U) (hWV : W ≤ V)
    (b : ThickeningLift (i ∣_ U) ((i ⁻¹ᵁ U).ι ≫ a) f (U.ι ≫ h)) :
    restrictLE hWV (restrictLE hVU b) = restrictLE (hWV.trans hVU) b := by
  ext1
  simp

end ThickeningLift

variable (i a f h) in
/-- The **presheaf of lifts** on `T'`: over an open `U`, the lifts of `a` restricted to `i⁻¹(U)`
along `i ∣_ U`, over `h` restricted to `U`, with restriction of lifts to smaller opens. -/
noncomputable abbrev liftPresheaf : TopCat.Presheaf (Type u) T'.carrier where
  obj U := ThickeningLift (i ∣_ U.unop) ((i ⁻¹ᵁ U.unop).ι ≫ a) f (Scheme.Opens.ι U.unop ≫ h)
  map g := ↾ThickeningLift.restrictLE g.unop.le
  map_id U := by
    ext b
    exact congrArg ThickeningLift.hom (ThickeningLift.restrictLE_rfl b)
  map_comp g g' := by
    ext b
    exact congrArg ThickeningLift.hom
      (ThickeningLift.restrictLE_restrictLE g.unop.le g'.unop.le b).symm

/-- The restriction maps of the presheaf of lifts precompose with the inclusion of opens. -/
theorem liftPresheaf_map_hom {U V : T'.Opensᵒᵖ} (g : U ⟶ V) (b : (liftPresheaf i a f h).obj U) :
    ((liftPresheaf i a f h).map g b).hom = T'.homOfLE g.unop.le ≫ b.hom :=
  (rfl)

/-- On the pullback of the inclusions of two opens `U₁` and `U₂`, the first projection followed by
`U₁ ⟶ T'` factors through `U₁ ⊓ U₂`, compatibly with both projections. -/
private theorem exists_pullback_homOfLE {W U₁ U₂ : T'.Opens} (h₁ : U₁ ≤ W) (h₂ : U₂ ≤ W) :
    ∃ m : pullback (T'.homOfLE h₁) (T'.homOfLE h₂) ⟶ (U₁ ⊓ U₂ : T'.Opens),
      m ≫ T'.homOfLE inf_le_left = pullback.fst _ _ ∧
        m ≫ T'.homOfLE inf_le_right = pullback.snd _ _ := by
  have hc : pullback.fst (T'.homOfLE h₁) (T'.homOfLE h₂) ≫ U₁.ι = pullback.snd _ _ ≫ U₂.ι := by
    rw [← T'.homOfLE_ι h₁, ← T'.homOfLE_ι h₂, pullback.condition_assoc]
  have hr : Set.range (pullback.fst (T'.homOfLE h₁) (T'.homOfLE h₂) ≫ U₁.ι) ⊆
      Set.range (U₁ ⊓ U₂).ι := by
    rintro _ ⟨p, rfl⟩
    rw [Scheme.Opens.range_ι]
    refine ⟨?_, ?_⟩
    · exact (pullback.fst (T'.homOfLE h₁) (T'.homOfLE h₂) p).property
    · rw [hc]
      exact (pullback.snd (T'.homOfLE h₁) (T'.homOfLE h₂) p).property
  refine ⟨IsOpenImmersion.lift _ _ hr, ?_, ?_⟩
  · rw [← cancel_mono U₁.ι, Category.assoc, Scheme.homOfLE_ι, IsOpenImmersion.lift_fac]
  · rw [← cancel_mono U₂.ι, Category.assoc, Scheme.homOfLE_ι, IsOpenImmersion.lift_fac, hc]

/-- On the pullback of `i ∣_ W` along the inclusion of an open `V ≤ W`, the first projection
factors through `i⁻¹(V)`, and the second projection is then `i ∣_ V`. -/
private theorem exists_pullback_morphismRestrict {V W : T'.Opens} (hVW : V ≤ W) :
    ∃ m : pullback (i ∣_ W) (T'.homOfLE hVW) ⟶ (i ⁻¹ᵁ V : T.Opens),
      m ≫ (i ⁻¹ᵁ V).ι = pullback.fst _ _ ≫ (i ⁻¹ᵁ W).ι ∧ m ≫ i ∣_ V = pullback.snd _ _ := by
  have hc : pullback.fst (i ∣_ W) (T'.homOfLE hVW) ≫ (i ⁻¹ᵁ W).ι ≫ i =
      pullback.snd _ _ ≫ V.ι := by
    rw [← morphismRestrict_ι, pullback.condition_assoc, Scheme.homOfLE_ι]
  have hr : Set.range (pullback.fst (i ∣_ W) (T'.homOfLE hVW) ≫ (i ⁻¹ᵁ W).ι) ⊆
      Set.range (i ⁻¹ᵁ V).ι := by
    rintro _ ⟨p, rfl⟩
    rw [Scheme.Opens.range_ι]
    change i ((pullback.fst (i ∣_ W) (T'.homOfLE hVW) ≫ (i ⁻¹ᵁ W).ι) p) ∈ V
    rw [← Scheme.Hom.comp_apply, Category.assoc, hc, Scheme.Hom.comp_apply]
    exact (pullback.snd (i ∣_ W) (T'.homOfLE hVW) p).property
  refine ⟨IsOpenImmersion.lift _ _ hr, IsOpenImmersion.lift_fac _ _ _, ?_⟩
  rw [← cancel_mono V.ι, Category.assoc, morphismRestrict_ι, IsOpenImmersion.lift_fac_assoc,
    Category.assoc, hc]

variable (i a f h) in
/-- **The presheaf of lifts is a sheaf**: lifts over the members of an open cover that agree on
the overlaps glue uniquely, since morphisms of schemes glue along open covers. -/
theorem isSheaf_liftPresheaf : (liftPresheaf i a f h).IsSheaf := by
  refine TopCat.Presheaf.isSheaf_of_isSheafUniqueGluing_types _ fun ι U sf hsf ↦ ?_
  let 𝒰 := Scheme.Opens.iSupOpenCover U
  have compat : ∀ k l, pullback.fst (𝒰.f k) (𝒰.f l) ≫ (sf k).hom =
      pullback.snd (𝒰.f k) (𝒰.f l) ≫ (sf l).hom := fun (k l : ι) ↦ by
    obtain ⟨m, hm₁, hm₂⟩ := exists_pullback_homOfLE (le_iSup U k) (le_iSup U l)
    have e := congrArg ThickeningLift.hom (hsf k l)
    change _ = pullback.fst (T'.homOfLE (le_iSup U k)) (T'.homOfLE (le_iSup U l)) at hm₁
    change _ = pullback.snd (T'.homOfLE (le_iSup U k)) (T'.homOfLE (le_iSup U l)) at hm₂
    change pullback.fst (T'.homOfLE (le_iSup U k)) (T'.homOfLE (le_iSup U l)) ≫ (sf k).hom =
      pullback.snd (T'.homOfLE (le_iSup U k)) (T'.homOfLE (le_iSup U l)) ≫ (sf l).hom
    rw [← hm₁, ← hm₂, Category.assoc, Category.assoc]
    exact congrArg (m ≫ ·) e
  -- Gluing the lifts on the members of the cover gives a lift on `⨆ U`.
  let g := 𝒰.glueMorphisms (fun k ↦ (sf k).hom) compat
  have hg : ∀ k, T'.homOfLE (le_iSup U k) ≫ g = (sf k).hom := 𝒰.ι_glueMorphisms _ compat
  have comp_hom : i ∣_ (⨆ k, U k) ≫ g = (i ⁻¹ᵁ ⨆ k, U k).ι ≫ a := by
    refine Scheme.Cover.hom_ext (𝒰.pullback₁ (i ∣_ (⨆ k, U k))) _ _ fun (k : ι) ↦ ?_
    obtain ⟨m, hm₁, hm₂⟩ := exists_pullback_morphismRestrict (i := i) (le_iSup U k)
    change pullback.fst (i ∣_ (⨆ k, U k)) (T'.homOfLE (le_iSup U k)) ≫ _ =
      pullback.fst (i ∣_ (⨆ k, U k)) (T'.homOfLE (le_iSup U k)) ≫ _
    rw [pullback.condition_assoc, hg, ← hm₂, Category.assoc, (sf k).comp_hom,
      reassoc_of% hm₁]
  have hom_comp : g ≫ f = Scheme.Opens.ι (⨆ k, U k) ≫ h :=
    𝒰.hom_ext _ _ fun (k : ι) ↦ by
      change T'.homOfLE (le_iSup U k) ≫ g ≫ f = T'.homOfLE (le_iSup U k) ≫ _
      rw [reassoc_of% hg, (sf k).hom_comp, Scheme.homOfLE_ι_assoc]
  refine ⟨⟨g, comp_hom, hom_comp⟩, fun k ↦ ThickeningLift.ext (hg k), fun s hs ↦ ?_⟩
  refine ThickeningLift.ext (𝒰.hom_ext _ _ fun (k : ι) ↦ ?_)
  change T'.homOfLE (le_iSup U k) ≫ s.hom = T'.homOfLE (le_iSup U k) ≫ g
  rw [hg]
  exact congrArg ThickeningLift.hom (hs k)

/-- **Lifts exist locally.** For `f` smooth and `i` a first-order thickening, every point of `T'`
has an open neighbourhood over which the sheaf of lifts has a section. -/
theorem exists_mem_and_nonempty_liftPresheaf [Smooth f] [IsFirstOrderThickening i]
    (ha : a ≫ f = i ≫ h) (x : T') :
    ∃ U : T'.Opens, x ∈ U ∧ Nonempty ((liftPresheaf i a f h).obj (op U)) :=
  exists_thickeningLift_restrict h ha x

end TauCeti.AlgebraicGeometry
