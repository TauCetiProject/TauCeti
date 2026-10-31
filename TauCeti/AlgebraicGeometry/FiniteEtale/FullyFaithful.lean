/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FiniteEtale.Fiber
public import TauCeti.AlgebraicGeometry.Modules.Tilde.Hartogs
import TauCeti.RingTheory.Depth.Finite
import Mathlib.RingTheory.Regular.Flat

/-!
# Restricting finite étale schemes to an open whose complement has depth two

Let `R` be a commutative ring and `W` an open subset of `Spec R`. If the complement of `W` has
depth at least two, then restricting finite étale schemes over `Spec R` to `W` is fully
faithful: every morphism over `W` between restrictions extends uniquely to `Spec R`.

The proof has two parts.

* A criterion over an affine base `S`. Let `j : T ⟶ S` be a morphism and `Y` a finite étale
  scheme over `S` whose global sections are not changed by base change along `j`, that is,
  `Γ(Y, 𝒪) → Γ(Y ×_S T, 𝒪)` is an isomorphism. Then every morphism `Y ×_S T ⟶ Y' ×_S T` over `T`
  is the base change of a unique morphism `Y ⟶ Y'` over `S`. Finite schemes over an affine base
  are affine, so morphisms into `Y'` are determined by their effect on global sections.
* The algebraic Hartogs principle. If `a, b` is a weakly regular sequence on `R` with
  `D(a), D(b) ⊆ W` and `C` is a flat `R`-algebra, then `a, b` stays weakly regular on `C`, and
  every section of `Spec C` over the preimage of `W` comes from a unique element of `C`
  (`TauCeti.AlgebraicGeometry.StructureSheaf.toOpenₗ_bijective_of_isWeaklyRegular`).

For a Noetherian ring, such a pair exists in the vanishing ideal of the complement of `W` as soon
as `depth R_𝔭 ≥ 2` for every prime `𝔭 ∉ W`. For a Noetherian local ring of depth at least two,
this applies to the punctured spectrum, the complement of the closed point.

## Main results

* `TauCeti.FiniteEtaleScheme.pullback_map_bijective_of_isIso_appTop`: the criterion over an
  affine base.
* `TauCeti.AlgebraicGeometry.isIso_appTop_pullback_fst_ι_of_isWeaklyRegular`: global sections
  of the spectrum of a flat algebra do not change under restriction to `W`.
* `TauCeti.FiniteEtaleScheme.fullyFaithfulPullbackιOfIsWeaklyRegular`: restriction to `W` is
  fully faithful if `D(a), D(b) ⊆ W` for a weakly regular sequence `a, b` on `R`.
* `TauCeti.FiniteEtaleScheme.fullyFaithfulPullbackιOfTwoLeDepth`: restriction to `W` is fully
  faithful if `R` is Noetherian and `depth R_𝔭 ≥ 2` for every prime `𝔭 ∉ W`.
* `TauCeti.FiniteEtaleScheme.fullyFaithfulPullbackιOfTwoLeDepthOfIsLocalRing`: restriction to an
  open containing the punctured spectrum of a Noetherian local ring of depth at least two is
  fully faithful.

## References

* [The Stacks Project, Lemma 31.5.11](https://stacks.math.columbia.edu/tag/0E9I), extension of
  sections across a closed subset of depth at least two.
* [The Stacks Project, Lemma 58.20.2](https://stacks.math.columbia.edu/tag/0BLK), whose proof
  uses that a finite étale algebra over a local ring of depth at least two is recovered from its
  sections over the punctured spectrum.
-/

public section

open CategoryTheory Limits AlgebraicGeometry Opposite IsLocalRing RingTheory.Sequence

universe u

namespace TauCeti.AlgebraicGeometry

variable {R : CommRingCat.{u}}

/-- Let `C` be a flat `R`-algebra and `W` an open subset of `Spec R` containing `D(a)` and `D(b)`
for a weakly regular sequence `a, b` on `R`. Then restriction of global sections
`Γ(Spec C, 𝒪) → Γ(Spec C ×_{Spec R} W, 𝒪)` is an isomorphism. -/
theorem isIso_appTop_pullback_fst_ι_of_isWeaklyRegular (C : Type u) [CommRing C] [Algebra R C]
    [Module.Flat R C] (W : (Spec R).Opens) {a b : R} (hab : IsWeaklyRegular R [a, b])
    (ha : PrimeSpectrum.basicOpen a ≤ W) (hb : PrimeSpectrum.basicOpen b ≤ W) :
    IsIso (Limits.pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R C))) W.ι).appTop := by
  set f := Spec.map (CommRingCat.ofHom (algebraMap R C))
  rw [← pullbackRestrictIsoRestrict_hom_ι, Scheme.Hom.comp_appTop]
  suffices IsIso (f ⁻¹ᵁ W).ι.appTop from
    have : IsIso (pullbackRestrictIsoRestrict f W).hom.appTop :=
      inferInstanceAs (IsIso ((pullbackRestrictIsoRestrict f W).hom.app ⊤))
    inferInstance
  -- The preimage of `W` contains the basic opens of the images of `a` and `b`.
  have hD {r : R} (hr : PrimeSpectrum.basicOpen r ≤ W) :
      PrimeSpectrum.basicOpen (algebraMap R C r) ≤ (f ⁻¹ᵁ W).ι ''ᵁ ⊤ := by
    rw [Scheme.Opens.ι_image_top]
    exact fun p hp ↦ hr hp
  have hreg : IsWeaklyRegular C [algebraMap R C a, algebraMap R C b] := by
    simpa using hab.of_flat (S := C)
  have hbij := AlgebraicGeometry.StructureSheaf.toOpenₗ_bijective_of_isWeaklyRegular hreg
    (hD ha) (hD hb)
  -- By definition, `toOpenₗ C C U` is the restriction of sections of `Spec C` from `⊤` to `U`,
  -- precomposed with the bijection `C → Γ(Spec C, 𝒪)`.
  have hcomp : ⇑(AlgebraicGeometry.StructureSheaf.toOpenₗ C C ((f ⁻¹ᵁ W).ι ''ᵁ ⊤)) =
      (f ⁻¹ᵁ W).ι.appTop ∘ AlgebraicGeometry.StructureSheaf.toOpenₗ C C ⊤ := rfl
  rw [hcomp] at hbij
  exact (ConcreteCategory.isIso_iff_bijective _).mpr ((Function.Bijective.of_comp_iff _
    AlgebraicGeometry.StructureSheaf.toOpenₗ_top_bijective).mp hbij)

end TauCeti.AlgebraicGeometry

namespace TauCeti.FiniteEtaleScheme

section Criterion

variable {S T : Scheme.{u}} [IsAffine S] (j : T ⟶ S)

/-- Let `j : T ⟶ S` be a morphism to an affine scheme and `Y`, `Y'` finite étale schemes over
`S`. If restriction of global sections `Γ(Y, 𝒪) → Γ(Y ×_S T, 𝒪)` is an isomorphism, then base
change along `j` is a bijection from morphisms `Y ⟶ Y'` over `S` to morphisms
`Y ×_S T ⟶ Y' ×_S T` over `T`. -/
theorem pullback_map_bijective_of_isIso_appTop {Y Y' : FiniteEtaleScheme S}
    (h : IsIso (Limits.pullback.fst Y.obj.hom j).appTop) :
    Function.Bijective (fun g : Y ⟶ Y' ↦ (pullback j).map g) := by
  set e := Limits.pullback.fst Y.obj.hom j
  have := h
  have : IsAffine Y'.obj.left := isAffine_of_isAffineHom Y'.obj.hom
  -- Morphisms from `Y` to an affine scheme are determined by their composites with `e`.
  have hcancel {Z : Scheme.{u}} [IsAffine Z] {g g' : Y.obj.left ⟶ Z} (hg : e ≫ g = e ≫ g') :
      g = g' := by
    refine ext_of_isAffine ((cancel_mono e.appTop).mp ?_)
    rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, hg]
  -- The base change of `g` is determined by its composite with the first projection.
  have hmap (g : Y ⟶ Y') : ((pullback j).map g).hom.left ≫ Limits.pullback.fst Y'.obj.hom j =
      e ≫ g.hom.left :=
    pullback.lift_fst _ _ _
  refine ⟨fun g g' hgg' ↦ ?_, fun φ ↦ ?_⟩
  · refine ObjectProperty.hom_ext _ (Over.OverMorphism.ext (hcancel ?_))
    rw [← hmap, ← hmap]
    exact congrArg (fun k ↦ k.hom.left ≫ Limits.pullback.fst Y'.obj.hom j) hgg'
  -- The composite `χ : Y ×_S T ⟶ Y'` corresponds to a ring map `Γ(Y', 𝒪) ⟶ Γ(Y ×_S T, 𝒪)`,
  -- which factors through the isomorphism `Γ(Y, 𝒪) ≅ Γ(Y ×_S T, 𝒪)`.
  set φ' : Limits.pullback Y.obj.hom j ⟶ Limits.pullback Y'.obj.hom j := φ.hom.left
  have hw : φ' ≫ Limits.pullback.snd Y'.obj.hom j = Limits.pullback.snd Y.obj.hom j :=
    Over.w φ.hom
  set χ := φ' ≫ Limits.pullback.fst Y'.obj.hom j with hχ
  let ψ : Y.obj.left ⟶ Y'.obj.left :=
    Y.obj.left.toSpecΓ ≫ Spec.map (χ.appTop ≫ inv e.appTop) ≫ Y'.obj.left.isoSpec.inv
  have hψ : e ≫ ψ = χ := by
    rw [Scheme.toSpecΓ_naturality_assoc, ← Spec.map_comp_assoc, Category.assoc,
      IsIso.inv_hom_id, Category.comp_id, ← Scheme.toSpecΓ_naturality_assoc,
      Scheme.toSpecΓ_isoSpec_inv, Category.comp_id]
  have hψS : ψ ≫ Y'.obj.hom = Y.obj.hom := hcancel <| by
    calc e ≫ ψ ≫ Y'.obj.hom = φ' ≫ Limits.pullback.snd Y'.obj.hom j ≫ j := by
          rw [reassoc_of% hψ, hχ, Category.assoc, Limits.pullback.condition]
      _ = Limits.pullback.snd Y.obj.hom j ≫ j := by rw [reassoc_of% hw]
      _ = e ≫ Y.obj.hom := Limits.pullback.condition.symm
  refine ⟨ObjectProperty.homMk (Over.homMk ψ hψS), ObjectProperty.hom_ext _ ?_⟩
  refine Over.OverMorphism.ext ?_
  dsimp only
  apply Limits.pullback.hom_ext
  · exact (hmap _).trans hψ
  · exact (pullback.lift_snd _ _ _).trans hw.symm

end Criterion

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
  -- The vanishing ideal of the closed set `Spec R ∖ W` contains a weakly regular pair.
  have hpair : ∃ a b : R, IsWeaklyRegular R [a, b] ∧ PrimeSpectrum.basicOpen a ≤ W ∧
      PrimeSpectrum.basicOpen b ≤ W := by
    let I : Ideal R := PrimeSpectrum.vanishingIdeal (W : Set (Spec R))ᶜ
    have hI (p : Ideal R) [p.IsPrime] (hle : I ≤ p) :
        ((2 : ℕ) : ℕ∞) ≤ depth (ModuleCat.of (Localization.AtPrime p)
          (LocalizedModule p.primeCompl R)) := by
      have hp : (⟨p, ‹_›⟩ : PrimeSpectrum R) ∉ W := by
        have hp : (⟨p, ‹_›⟩ : PrimeSpectrum R) ∈ PrimeSpectrum.zeroLocus (I : Set R) := hle
        rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure] at hp
        exact W.isOpen.isClosed_compl.closure_subset hp
      let e : LocalizedModule p.primeCompl R ≃ₗ[Localization.AtPrime p]
          Localization.AtPrime p :=
        (IsLocalizedModule.iso p.primeCompl
          (Algebra.linearMap R (Localization.AtPrime p))).extendScalarsOfIsLocalization
          p.primeCompl _
      have := h ⟨p, ‹_›⟩ hp
      rw [← depth_eq_of_linearEquiv e] at this
      exact_mod_cast this
    obtain ⟨rs, hlen, hmem, hreg⟩ := exists_isWeaklyRegular_of_le_depth_localizedModule I 2 hI
    obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hlen
    have hD (r : R) (hr : r ∈ [a, b]) : PrimeSpectrum.basicOpen r ≤ W := fun q hq ↦ by
      by_contra hqW
      exact hq ((PrimeSpectrum.mem_vanishingIdeal _ _).mp (hmem r hr) q hqW)
    exact ⟨a, b, hreg, hD a (by simp), hD b (by simp)⟩
  have : (pullback W.ι).Full := by
    obtain ⟨a, b, hab, ha, hb⟩ := hpair
    exact (fullyFaithfulPullbackιOfIsWeaklyRegular W hab ha hb).full
  have : (pullback W.ι).Faithful := by
    obtain ⟨a, b, hab, ha, hb⟩ := hpair
    exact (fullyFaithfulPullbackιOfIsWeaklyRegular W hab ha hb).faithful
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
    let e : LocalizedModule (maximalIdeal R).primeCompl R ≃ₗ[Localization.AtPrime (maximalIdeal R)]
        Localization.AtPrime (maximalIdeal R) :=
      (IsLocalizedModule.iso (maximalIdeal R).primeCompl
        (Algebra.linearMap R (Localization.AtPrime (maximalIdeal R)))).extendScalarsOfIsLocalization
        (maximalIdeal R).primeCompl _
    have := (le_depth_iff_forall_isMaximal (S := R) (N := R) 2).mp hdepth (maximalIdeal R)
    rw [depth_eq_of_linearEquiv e] at this
    exact this

end TauCeti.FiniteEtaleScheme
