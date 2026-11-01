/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FiniteEtale.Fiber
public import TauCeti.AlgebraicGeometry.Modules.Tilde.Hartogs
public import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import TauCeti.AlgebraicGeometry.AffineScheme
import TauCeti.AlgebraicGeometry.FiniteEtale.MorphismProperty
import TauCeti.AlgebraicGeometry.Morphisms.FormallyUnramified
import TauCeti.RingTheory.Depth.Finite

/-!
# Restricting finite étale schemes to an open whose complement has depth two

Let `R` be a Noetherian ring and `W` an open subset of `Spec R` such that `depth R_𝔭 ≥ 2` for
every prime `𝔭 ∉ W`. Then restricting finite étale schemes over `Spec R` to `W` is fully
faithful: every morphism over `W` between restrictions extends uniquely to `Spec R`. Without the
Noetherian hypothesis, the same holds when `D(a), D(b) ⊆ W` for a weakly regular sequence `a, b`
on `R`.

The proof has two parts.

* A criterion over an affine base `S`. Let `j : T ⟶ S` be a morphism, `Y` a scheme over `S`
  whose global sections are not changed by base change along `j`, that is,
  `Γ(Y, 𝒪) → Γ(Y ×_S T, 𝒪)` is an isomorphism, and `Y'` an affine scheme over `S`. Then every
  morphism `Y ×_S T ⟶ Y' ×_S T` over `T` is the base change of a unique morphism `Y ⟶ Y'` over
  `S`, since morphisms into the affine scheme `Y'` are determined by their effect on global
  sections (`TauCeti.AlgebraicGeometry.overPullback_map_bijective_of_isIso_appTop`). Finite
  schemes over an affine base are affine, so this applies to finite étale schemes.
* The algebraic Hartogs principle. If `a, b` is a weakly regular sequence on `R` with
  `D(a), D(b) ⊆ W` and `C` is a flat `R`-algebra, then `a, b` stays weakly regular on `C`, and
  every section of `Spec C` over the preimage of `W` comes from a unique element of `C`
  (`TauCeti.AlgebraicGeometry.isIso_appTop_pullback_fst_ι_of_isWeaklyRegular`).

For a Noetherian ring, such a pair exists in the vanishing ideal of the complement of `W` as soon
as `depth R_𝔭 ≥ 2` for every prime `𝔭 ∉ W`. For a Noetherian local ring of depth at least two,
this applies to the punctured spectrum, the complement of the closed point.

The affine statement globalizes. Let `X` be a locally Noetherian scheme and `U` an open subscheme
such that the local ring `𝒪_{X,x}` has depth at least two at every point `x ∉ U`. Then restriction
of finite étale schemes over `X` to `U` is fully faithful. Fullness is Zariski local on `X` once `U`
is dense (`TauCeti.FiniteEtaleScheme.full_pullback_ι_of_openCover`): the extensions over the
charts of an open cover agree on overlaps, because two morphisms into a finite étale scheme agree
as soon as they agree over a dense open subset of an étale source. On an affine chart `Spec R`
the depth hypothesis gives a weakly regular pair `a, b` with `D(a), D(b)` in the preimage of `U`;
this supplies both the affine fullness and the density of `U`, as `D(a)` is dense for a
nonzerodivisor `a`.

## Main results

* `TauCeti.FiniteEtaleScheme.pullback_map_bijective_of_isIso_appTop`: the criterion for finite
  étale schemes over an affine base.
* `TauCeti.FiniteEtaleScheme.fullyFaithfulPullbackιOfIsWeaklyRegular`: restriction to `W` is
  fully faithful if `D(a), D(b) ⊆ W` for a weakly regular sequence `a, b` on `R`.
* `TauCeti.FiniteEtaleScheme.fullyFaithfulPullbackιOfTwoLeDepth`: restriction to `W` is fully
  faithful if `R` is Noetherian and `depth R_𝔭 ≥ 2` for every prime `𝔭 ∉ W`.
* `TauCeti.FiniteEtaleScheme.fullyFaithfulPullbackιOfTwoLeDepthOfIsLocalRing`: restriction to an
  open containing the punctured spectrum of a Noetherian local ring of depth at least two is
  fully faithful.
* `TauCeti.FiniteEtaleScheme.full_pullback_ι_of_openCover`: restriction to a dense open `U` is full
  if it is full over every chart of an open cover.
* `TauCeti.FiniteEtaleScheme.fullyFaithfulPullbackιOfTwoLeDepthStalk`: restriction to `U` is fully
  faithful if `X` is locally Noetherian and `depth 𝒪_{X,x} ≥ 2` for every point `x ∉ U`.

## References

* [The Stacks Project, Lemma 31.5.11](https://stacks.math.columbia.edu/tag/0E9I), extension of
  sections across a closed subset of depth at least two.
* [The Stacks Project, Lemma 58.20.2](https://stacks.math.columbia.edu/tag/0BLK), whose proof
  uses that a finite étale algebra over a local ring of depth at least two is recovered from its
  sections over the punctured spectrum.
* [The Stacks Project, Lemma 58.21.6](https://stacks.math.columbia.edu/tag/0EY7), extension of
  finite étale covers across points where purity holds, whose gluing step uses this full
  faithfulness.
-/

public section

open CategoryTheory Limits AlgebraicGeometry Opposite IsLocalRing RingTheory.Sequence

universe u

namespace TauCeti.FiniteEtaleScheme

/-- Let `j : T ⟶ S` be a morphism to an affine scheme and `Y`, `Y'` finite étale schemes over
`S`. If restriction of global sections `Γ(Y, 𝒪) → Γ(Y ×_S T, 𝒪)` is an isomorphism, then base
change along `j` is a bijection from morphisms `Y ⟶ Y'` over `S` to morphisms
`Y ×_S T ⟶ Y' ×_S T` over `T`. -/
theorem pullback_map_bijective_of_isIso_appTop {S T : Scheme.{u}} [IsAffine S] (j : T ⟶ S)
    {Y Y' : FiniteEtaleScheme S} (h : IsIso (Limits.pullback.fst Y.obj.hom j).appTop) :
    Function.Bijective (fun g : Y ⟶ Y' ↦ (pullback j).map g) := by
  have : IsAffine Y'.obj.left := isAffine_of_isAffineHom Y'.obj.hom
  have hbij := TauCeti.AlgebraicGeometry.overPullback_map_bijective_of_isIso_appTop j
    (Y' := Y'.obj) h
  refine ⟨fun g g' hgg' ↦ ObjectProperty.hom_ext _ (hbij.1 (congrArg (·.hom) hgg')), fun φ ↦ ?_⟩
  obtain ⟨g, hg⟩ := hbij.2 φ.hom
  exact ⟨ObjectProperty.homMk g, ObjectProperty.hom_ext _ hg⟩

variable {R : CommRingCat.{u}}

/-- Let `W` be an open subset of `Spec R` containing `D(a)` and `D(b)` for a weakly regular
sequence `a, b` on `R`. Then restriction of finite étale schemes over `Spec R` to `W` is fully
faithful. -/
noncomputable def fullyFaithfulPullbackιOfIsWeaklyRegular (W : (Spec R).Opens) {a b : R}
    (hab : IsWeaklyRegular R [a, b]) (ha : PrimeSpectrum.basicOpen a ≤ W)
    (hb : PrimeSpectrum.basicOpen b ≤ W) : (pullback W.ι).FullyFaithful :=
  -- Every finite étale scheme over `Spec R` is the spectrum of a finite étale `R`-algebra.
  have hbij (C D : (CommAlgCat.FiniteEtale.{u} R)ᵒᵖ) :
      Function.Bijective (fun g : (spec R).obj C ⟶ (spec R).obj D ↦ (pullback W.ι).map g) :=
    pullback_map_bijective_of_isIso_appTop W.ι <| by
      rw [spec_obj_obj]
      exact TauCeti.AlgebraicGeometry.isIso_appTop_pullback_fst_ι_of_isWeaklyRegular C.unop W hab
        ha hb
  have := (pullback W.ι).full_of_comp_essSurj (spec R) fun C D φ ↦ (hbij C D).2 φ
  have := (pullback W.ι).faithful_of_comp_essSurj (spec R) fun C D _ _ h ↦ (hbij C D).1 h
  .ofFullyFaithful _

/-- Let `R` be a Noetherian ring and `W` an open subset of `Spec R` such that `depth R_𝔭 ≥ 2` for
every prime `𝔭 ∉ W`. Then restriction of finite étale schemes over `Spec R` to `W` is fully
faithful. -/
noncomputable def fullyFaithfulPullbackιOfTwoLeDepth [IsNoetherianRing R] (W : (Spec R).Opens)
    (h : ∀ p : PrimeSpectrum R, p ∉ W →
      2 ≤ depth (ModuleCat.of (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal))) :
    (pullback W.ι).FullyFaithful :=
  have ⟨_, _⟩ : (pullback W.ι).Full ∧ (pullback W.ι).Faithful := by
    obtain ⟨a, b, hab, ha, hb⟩ :=
      TauCeti.AlgebraicGeometry.StructureSheaf.exists_isWeaklyRegular_basicOpen_le_of_two_le_depth
        (M := R) W fun p hp ↦ p.asIdeal.depth_localizedModule_self.trans_ge (h p hp)
    exact ⟨(fullyFaithfulPullbackιOfIsWeaklyRegular W hab ha hb).full,
      (fullyFaithfulPullbackιOfIsWeaklyRegular W hab ha hb).faithful⟩
  .ofFullyFaithful _

/-- Let `R` be a Noetherian local ring of depth at least two and `W` an open subset of `Spec R`
containing every point other than the closed point, for instance the punctured spectrum. Then
restriction of finite étale schemes over `Spec R` to `W` is fully faithful. -/
noncomputable def fullyFaithfulPullbackιOfTwoLeDepthOfIsLocalRing [IsLocalRing R]
    [IsNoetherianRing R] (W : (Spec R).Opens) (hdepth : 2 ≤ depth (ModuleCat.of R R))
    (hW : ∀ p : PrimeSpectrum R, p ≠ closedPoint R → p ∈ W) :
    (pullback W.ι).FullyFaithful :=
  fullyFaithfulPullbackιOfTwoLeDepth W fun p hp ↦ by
    -- The only point outside `W` is the closed point, at which the localization is `R` itself.
    obtain rfl : p = closedPoint R := not_not.mp (mt (hW p) hp)
    have := (le_depth_iff_forall_isMaximal (S := R) (N := R) 2).mp hdepth (maximalIdeal R)
    rwa [Ideal.depth_localizedModule_self] at this

section Glue

/-! ### Zariski-local fullness -/

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
        rw [Category.assoc, Category.assoc, Limits.pullback.condition, reassoc_of% hφ,
          toRestrict, Limits.pullback.lift_snd_assoc, Category.assoc, morphismRestrict_ι,
          ← Limits.pullback.condition_assoc, Category.assoc]))
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
    _ = s ≫ φ ≫ Limits.pullback.fst _ _ := by
      rw [hψ, Category.assoc, restrictMap, Limits.pullback.lift_fst_assoc,
        Limits.pullback.lift_fst, reassoc_of% hr]

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

/-- Let `X` be a locally Noetherian scheme and `U` an open subscheme such that the local ring
`𝒪_{X,x}` has depth at least two at every point `x ∉ U`. Then restriction of finite étale schemes
over `X` to `U` is fully faithful. -/
noncomputable def fullyFaithfulPullbackιOfTwoLeDepthStalk [IsLocallyNoetherian X] (U : X.Opens)
    (h : ∀ x : X, x ∉ U →
      2 ≤ depth (ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x))) :
    (pullback U.ι).FullyFaithful :=
  have ⟨_, _⟩ : (pullback U.ι).Full ∧ (pullback U.ι).Faithful := by
    let 𝒰 := X.affineOpenCover
    have (i : 𝒰.I₀) : IsNoetherianRing (𝒰.X i) :=
      isLocallyNoetherian_Spec.mp (isLocallyNoetherian_of_isOpenImmersion (𝒰.f i))
    -- On each affine chart `Spec R`, the local rings at primes outside the preimage of `U` are
    -- the stalks of `X` at their images, so they have depth at least two.
    have hchart (i : 𝒰.I₀) (p : PrimeSpectrum (𝒰.X i)) (hp : p ∉ 𝒰.f i ⁻¹ᵁ U) :
        2 ≤ depth (ModuleCat.of (Localization.AtPrime p.asIdeal)
          (Localization.AtPrime p.asIdeal)) := by
      have := (IsOpenImmersion.iff_isIso_stalkMap (f := 𝒰.f i)).mp inferInstance |>.2 p
      let e := (asIso ((𝒰.f i).stalkMap p) ≪≫ Spec.stalkIso (𝒰.X i) p).commRingCatIsoToRingEquiv
      exact e.depth_self_eq ▸ h _ hp
    choose a b hab ha hb using fun i ↦
      TauCeti.AlgebraicGeometry.StructureSheaf.exists_isWeaklyRegular_basicOpen_le_of_two_le_depth
        (M := 𝒰.X i) (𝒰.f i ⁻¹ᵁ U) fun p hp ↦
          p.asIdeal.depth_localizedModule_self.trans_ge (hchart i p hp)
    -- `U` is dense: on each chart its preimage contains `D(a)` for a nonzerodivisor `a`.
    have hdense : Dense (U : Set X) := by
      refine dense_iff_inter_open.mpr fun V hV ⟨x, hxV⟩ ↦ ?_
      obtain ⟨i, y, rfl⟩ := 𝒰.openCover.exists_eq x
      have hreg : a i ∈ nonZeroDivisors (𝒰.X i) := isRegular_iff_mem_nonZeroDivisors.mp
        (isLeftRegular_iff_isRegular.mp (RingTheory.Sequence.isWeaklyRegular_cons_iff ..
          |>.mp (hab i)).1)
      have hDa : Dense (PrimeSpectrum.basicOpen (a i) : Set (PrimeSpectrum (𝒰.X i))) := by
        rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away (a i)) (a i)]
        refine (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr ?_
        rw [(RingHom.injective_iff_ker_eq_bot _).mp (IsLocalization.injective
          (Localization.Away (a i)) (Submonoid.powers_le.mpr hreg))]
        exact bot_le
      obtain ⟨z, hzV, hzD⟩ :=
        hDa.inter_open_nonempty _ (hV.preimage (𝒰.f i).continuous) ⟨y, hxV⟩
      exact ⟨_, hzV, ha i hzD⟩
    have := Opens.isDominant_ι hdense
    exact ⟨full_pullback_ι_of_openCover U hdense 𝒰.openCover fun i ↦
      (fullyFaithfulPullbackιOfIsWeaklyRegular _ (hab i) (ha i) (hb i)).full, inferInstance⟩
  .ofFullyFaithful _

end TauCeti.FiniteEtaleScheme
