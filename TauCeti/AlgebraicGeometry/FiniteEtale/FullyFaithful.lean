/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FiniteEtale.Fiber
public import TauCeti.AlgebraicGeometry.Modules.Tilde.Hartogs
import TauCeti.AlgebraicGeometry.AffineScheme
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

end TauCeti.FiniteEtaleScheme
