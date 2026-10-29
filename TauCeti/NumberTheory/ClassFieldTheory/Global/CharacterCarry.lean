/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Brauer.CharacterCarry
public import TauCeti.NumberTheory.ClassFieldTheory.Brauer.CharacterFormula
public import TauCeti.NumberTheory.ClassFieldTheory.Global.IdeleLocalization
public import TauCeti.NumberTheory.ClassFieldTheory.Global.LayerInvariant
public import TauCeti.NumberTheory.ClassFieldTheory.Global.LiftingObstruction
public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Layer.Hom

/-!
# Localization of global character carry classes and the idelic character formula

Let `K` be a number field and let `χ : G_K → ℚ / ℤ` be a character with open kernel. For an
invariant idele `a ∈ I_{Kˢ}^{G_K}`, the carry cocycle of `χ` and `a` represents the class usually
written `a ∪ δχ` in `H²(G_K, I_{Kˢ})`; for `a ∈ Kˣ` it represents the Brauer class `a ∪ δχ` in
`Br K`.

This file computes the localizations of these classes. At a finite place `v`, an embedding of
separable closures `τ : Kˢ → K_vˢ` restricts `χ` along the decomposition map and reads the
`v`-component of `a`. The localized idele class is the carry class of precisely those two local
objects (`ideleBrLocalization_characterCarryCocycle`). The same statement holds at an infinite
place (`ideleInfiniteBrLocalization_characterCarryCocycle`). In particular, the localization
vanishes where the corresponding component of `a` is `1`. Together with the local invariant
formula for carry classes, these identities let a global character and an idele concentrated at
one place produce an idele-cohomology class with a prescribed sum of local invariants.

The local character formula evaluates these localizations for an arbitrary idele: if the
component of `a` at `v` is `a_v ∈ K_vˣ`, then the localization of `a ∪ δχ` at `v` has invariant
`χ (Art_v a_v)`, the value of `χ` on the local Artin symbol of `a_v` read in `G_K` through the
decomposition map (`invMap_ideleBrLocalization_characterCarryCocycle_of_mk_eq_artinMap`), with no
hypothesis on the ramification of `χ`, and likewise at an infinite place
(`infiniteInvMap_ideleInfiniteBrLocalization_characterCarryCocycle_of_mk_eq_infiniteArtinAt`).
Hence the sum of the local invariants of the idele carry class is the sum of the values of `χ` on
the local Artin symbols of the components of `a`
(`sumLocalInv_ideleLocalization_characterCarryCocycle`,
`sumLocalInv_ideleLocalization_characterCarryCocycle_eq_finsum`).

These classes are the classes `a ∪ δχ` of the character formula on the layers of the idele
formation over `K`: for a character `χ'` of the Galois group of the layer `V ◁ G_K`, read on `G_K`
as `χ`, the class over `G_K` of `a ∪ δχ'` is the idele carry class of `χ` and `a`
(`ideleLayerCorInfl_artinCharacterCup`). So the sum of the local invariants of an idele layer is
computed on these classes by the local Artin maps (`ideleSumLocalInv_artinCharacterCup`):

```text
Σ inv (a ∪ δχ') = ∑ᶠ v, χ (Art_v a_v) + ∑_w χ (Art_w a_w).
```

For a class formation on the idele-class formation whose invariant on the layers over `K` is the
sum of the local invariants of a lift to the ideles, the character formula of the abstract Artin
map turns this into the local–global formula for the Artin map on idele classes
(`ClassFormation.apply_artinMap_eq_finsum_of_inv_eq_ideleSumLocalInv`): a character of the Galois
group of the layer takes on the Artin symbol of an idele class the sum of its values on the local
Artin symbols of the components.

For `a ∈ Kˣ`, the localization of the Brauer class `a ∪ δχ` at a place is the carry class of the
restricted character and of the image of `a`
(`TauCeti.ClassFieldTheory.brBaseChange_characterCarryCocycle`), so the local character formula
(`TauCeti.ClassFieldTheory.invMap_characterCarryCocycle_of_mk_eq_artinMap`) evaluates its local
invariants:

```text
inv_v (a ∪ δχ) = χ (Art_v a),
```

where `Art_v a` is the local Artin symbol of `a ∈ K_vˣ`, read in `G_K` through the decomposition
map (`finiteInvAt_characterCarryCocycle_of_mk_eq_artinMap`,
`infiniteInvAt_characterCarryCocycle_of_mk_eq_infiniteArtinAt`). Since a global Brauer class has
nonzero local invariant at only finitely many places, `χ (Art_v a) = 0` for all but finitely
many finite places `v` (`finite_setOf_apply_absoluteGaloisGroupMap_ne_zero`), and the sum of the
local invariants of `a ∪ δχ` is the sum of the values of `χ` on the local Artin symbols of `a`
(`sumLocalInv_brLocalization_characterCarryCocycle`,
`sumLocalInv_brLocalization_characterCarryCocycle_eq_finsum`).

If `E/K` is cyclic and `χ` sends a generator of `Gal(E/K)` to `1 / [E : K]`, every Brauer class
split by `E` is such a carry class (`exists_characterCarryCocycle_eq_relBrInfl`). So the sum of the
local invariants vanishes on all classes split by `E` exactly when the local Artin symbols of every
`a ∈ Kˣ` satisfy the product formula `∑_v χ (Art_v a) = 0`
(`forall_sumLocalInv_brLocalization_relBrInfl_eq_zero_iff`).

## Main results

* `TauCeti.ClassFieldTheory.ideleBrLocalization_characterCarryCocycle`,
  `TauCeti.ClassFieldTheory.ideleInfiniteBrLocalization_characterCarryCocycle`: the localizations
  of an idele carry class are the local carry classes.
* `TauCeti.ClassFieldTheory.invMap_ideleBrLocalization_characterCarryCocycle_of_mk_eq_artinMap`,
  `infiniteInvMap_ideleInfiniteBrLocalization_characterCarryCocycle_of_mk_eq_infiniteArtinAt`:
  the local invariant of an idele carry class `a ∪ δχ` at a place is `χ (Art_v a_v)`.
* `TauCeti.ClassFieldTheory.sumLocalInv_ideleLocalization_characterCarryCocycle`,
  `TauCeti.ClassFieldTheory.sumLocalInv_ideleLocalization_characterCarryCocycle_eq_finsum`: the
  sum of the local invariants of an idele carry class is `∑_v χ (Art_v a_v)`.
* `TauCeti.ClassFieldTheory.ideleLayerCorInfl_artinCharacterCup`,
  `TauCeti.ClassFieldTheory.ideleSumLocalInv_artinCharacterCup`: on the layer `V ◁ G_K` of the
  idele formation, the class `a ∪ δχ'` of the character formula is the idele carry class, and
  its sum of local invariants is `∑_v χ (Art_v a_v)`.
* `TauCeti.ClassFieldTheory.ClassFormation.apply_artinMap_eq_finsum_of_inv_eq_ideleSumLocalInv`:
  for a class formation on idele classes whose invariant is the sum of the local invariants,
  `χ (Art [a]) = ∑_v χ (Art_v a_v)`.
* `TauCeti.ClassFieldTheory.finiteInvAt_characterCarryCocycle_of_mk_eq_artinMap`,
  `TauCeti.ClassFieldTheory.infiniteInvAt_characterCarryCocycle_of_mk_eq_infiniteArtinAt`: the
  local invariant of `a ∪ δχ` at a place is `χ (Art_v a)`.
* `TauCeti.ClassFieldTheory.finite_setOf_apply_absoluteGaloisGroupMap_ne_zero`: `χ (Art_v a)`
  vanishes at all but finitely many finite places.
* `TauCeti.ClassFieldTheory.sumLocalInv_brLocalization_characterCarryCocycle`,
  `TauCeti.ClassFieldTheory.sumLocalInv_brLocalization_characterCarryCocycle_eq_finsum`: the sum
  of the local invariants of `a ∪ δχ` is `∑_v χ (Art_v a)`.
* `TauCeti.ClassFieldTheory.forall_sumLocalInv_brLocalization_relBrInfl_eq_zero_iff`: for a
  cyclic extension `E/K`, the sum of the local invariants vanishes on the classes split by `E`
  exactly when the local Artin symbols satisfy the product formula.

## References

* J. S. Milne, *Class Field Theory*, Chapter VII, Lemma 7.3 and Lemma 8.5.
* J.-P. Serre, *Local Fields*, Chapter XIV, §1.
* J. Tate, *Global class field theory*, in J. W. S. Cassels and A. Fröhlich (eds.), *Algebraic
  Number Theory*, Chapter VII, §11.
* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §5.
-/

public section

noncomputable section

namespace TauCeti.ClassFieldTheory

open IsDedekindDomain _root_.NumberField ContCohomology

variable {K : Type} [Field K]

section Idele

variable [NumberField K]

/-! ### Finite places -/

section Finite

variable {v : HeightOneSpectrum (𝓞 K)}
  (τ : SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K))

/-- **A global idele carry class localizes to the corresponding local carry class.** The local
character is obtained by restricting along the decomposition map, and its invariant coefficient
is the component of the global idele along the chosen embedding of separable closures. -/
theorem ideleBrLocalization_characterCarryCocycle
    (χ : Additive (AbsoluteGaloisGroup K) →+ AddCircle (1 : ℚ))
    (hχ : IsOpen (χ.ker : Set (Additive (AbsoluteGaloisGroup K))))
    (a : H0 (AbsoluteGaloisGroup K) (IdeleCoeff K)) :
    ideleBrLocalization v (characterCarryCocycle χ hχ a :
      H2 (AbsoluteGaloisGroup K) (IdeleCoeff K)) =
      unitsRepH2Equiv (v.adicCompletion K)
        (characterCarryCocycle
          (χ.comp (absoluteGaloisGroupMap τ :
            AbsoluteGaloisGroup (v.adicCompletion K) →* AbsoluteGaloisGroup K).toAdditive)
          (by
            rw [← AddMonoidHom.comap_ker, AddSubgroup.coe_comap]
            exact hχ.preimage (continuous_ofMul.comp
              ((absoluteGaloisGroupMap τ).continuous.comp continuous_toMul)))
          (explicitMap0 (AbsoluteGaloisGroup K) (IdeleCoeff K)
            (absoluteGaloisGroupMap τ) (ideleCoeffComponent τ)
            (ideleCoeffComponent_smul τ) a) :
          H2 (AbsoluteGaloisGroup (v.adicCompletion K))
            (UnitsCoeff (v.adicCompletion K))) := by
  rw [ideleBrLocalization_apply τ, explicitMap2_mk,
    cocyclesMap2_characterCarryCocycle]

/-- A global idele carry class has zero localization at a finite place where its idele coefficient
has component `1` (written `0` in the additive coefficient module). -/
theorem ideleBrLocalization_characterCarryCocycle_eq_zero_of_component_eq_zero
    (χ : Additive (AbsoluteGaloisGroup K) →+ AddCircle (1 : ℚ))
    (hχ : IsOpen (χ.ker : Set (Additive (AbsoluteGaloisGroup K))))
    (a : H0 (AbsoluteGaloisGroup K) (IdeleCoeff K))
    (ha : ideleCoeffComponent τ (a : IdeleCoeff K) = 0) :
    ideleBrLocalization v (characterCarryCocycle χ hχ a :
      H2 (AbsoluteGaloisGroup K) (IdeleCoeff K)) = 0 := by
  rw [ideleBrLocalization_characterCarryCocycle τ]
  have ha' : explicitMap0 (AbsoluteGaloisGroup K) (IdeleCoeff K)
      (absoluteGaloisGroupMap τ :
        AbsoluteGaloisGroup (v.adicCompletion K) →* AbsoluteGaloisGroup K)
      (ideleCoeffComponent τ)
      (ideleCoeffComponent_smul τ) a = 0 := by
    apply Subtype.ext
    simpa only [coe_explicitMap0, AddSubgroup.coe_zero] using ha
  rw [ha']
  simp

/-- **The local invariant of a global idele carry class.** Suppose the restricted global
character is the character of a finite unramified extension `E / K_v`, and the selected component
of the invariant idele is the image of `b ∈ K_vˣ`. Then the localized class has invariant
`v(b) · χ_v(Frob)`. -/
theorem invMap_ideleBrLocalization_characterCarryCocycle
    (E : IntermediateField (v.adicCompletion K)
      (SeparableClosure (v.adicCompletion K)))
    [FiniteDimensional (v.adicCompletion K) E]
    [IsGalois (v.adicCompletion K) E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] [ValuativeExtension (v.adicCompletion K) E]
    [IsUnramified (v.adicCompletion K) E]
    (χ : Additive (AbsoluteGaloisGroup K) →+ AddCircle (1 : ℚ))
    (hχ : IsOpen (χ.ker : Set (Additive (AbsoluteGaloisGroup K))))
    (χv : Additive Gal(E/(v.adicCompletion K)) →+ AddCircle (1 : ℚ))
    (a : H0 (AbsoluteGaloisGroup K) (IdeleCoeff K)) (b : (v.adicCompletion K)ˣ)
    (hχv : χ.comp (absoluteGaloisGroupMap τ :
        AbsoluteGaloisGroup (v.adicCompletion K) →*
          AbsoluteGaloisGroup K).toAdditive =
      χv.comp (AlgEquiv.restrictNormalHom
        (K₁ := SeparableClosure (v.adicCompletion K)) E).toAdditive)
    (ha : ideleCoeffComponent τ (a : IdeleCoeff K) =
      (baseUnitsEquivInvariants (v.adicCompletion K) (.ofMul b) :
        UnitsCoeff (v.adicCompletion K))) :
    invMap (v.adicCompletion K)
        (ideleBrLocalization v (characterCarryCocycle χ hχ a :
          H2 (AbsoluteGaloisGroup K) (IdeleCoeff K))) =
      (normalizedValuation (v.adicCompletion K) b).toAdd •
        χv (.ofMul (frobeniusAlgEquiv (K := v.adicCompletion K) (L := E))) := by
  rw [ideleBrLocalization_characterCarryCocycle τ]
  have ha' : explicitMap0 (AbsoluteGaloisGroup K) (IdeleCoeff K)
      (absoluteGaloisGroupMap τ :
        AbsoluteGaloisGroup (v.adicCompletion K) →* AbsoluteGaloisGroup K)
      (ideleCoeffComponent τ) (ideleCoeffComponent_smul τ) a =
        baseUnitsEquivInvariants (v.adicCompletion K) (.ofMul b) := by
    apply Subtype.ext
    simpa only [coe_explicitMap0] using ha
  simpa only [hχv, ha'] using invMap_characterCarryCocycle E χv b

/-- **The local character formula for a global idele carry class.** Let `χ : G_K → ℚ/ℤ` be a
character with open kernel and `a` an invariant idele of `Kˢ` whose component at `v` along `τ` is
`b ∈ K_vˣ`. If `σ` represents the absolute local Artin symbol of `b`, then the localization at `v`
of the carry class `a ∪ δχ` has invariant `χ` of the image of `σ` under the decomposition map of
`τ`. No hypothesis on the ramification of `χ` at `v` is needed. -/
theorem invMap_ideleBrLocalization_characterCarryCocycle_of_mk_eq_artinMap
    (χ : Additive (AbsoluteGaloisGroup K) →+ AddCircle (1 : ℚ))
    (hχ : IsOpen (χ.ker : Set (Additive (AbsoluteGaloisGroup K))))
    (a : H0 (AbsoluteGaloisGroup K) (IdeleCoeff K)) (b : (v.adicCompletion K)ˣ)
    (hb : ideleCoeffComponent τ (a : IdeleCoeff K) =
      (baseUnitsEquivInvariants (v.adicCompletion K) (.ofMul b) :
        UnitsCoeff (v.adicCompletion K)))
    (σ : Field.absoluteGaloisGroup (v.adicCompletion K))
    (hσ : (σ : Field.absoluteGaloisGroupAbelianization (v.adicCompletion K)) =
      artinMap (v.adicCompletion K) b) :
    invMap (v.adicCompletion K) (ideleBrLocalization v (characterCarryCocycle χ hχ a :
        H2 (AbsoluteGaloisGroup K) (IdeleCoeff K))) =
      χ (.ofMul (absoluteGaloisGroupMap τ
        (absoluteGaloisGroupRestrictEquiv (v.adicCompletion K) σ))) := by
  rw [ideleBrLocalization_characterCarryCocycle τ]
  have hb' : explicitMap0 (AbsoluteGaloisGroup K) (IdeleCoeff K)
      (absoluteGaloisGroupMap τ :
        AbsoluteGaloisGroup (v.adicCompletion K) →* AbsoluteGaloisGroup K)
      (ideleCoeffComponent τ) (ideleCoeffComponent_smul τ) a =
        baseUnitsEquivInvariants (v.adicCompletion K) (.ofMul b) :=
    Subtype.ext (by simpa only [coe_explicitMap0] using hb)
  rw [hb']
  exact invMap_characterCarryCocycle_of_mk_eq_artinMap _ _ b σ hσ

end Finite

/-! ### Infinite places -/

section Infinite

variable {w : InfinitePlace K}
  (τ : SeparableClosure K →ₐ[K] SeparableClosure w.Completion)

/-- **A global idele carry class localizes at an infinite place to the corresponding local carry
class.** The local character is the restriction along the archimedean decomposition map and the
coefficient is the selected infinite component of the idele. -/
theorem ideleInfiniteBrLocalization_characterCarryCocycle
    (χ : Additive (AbsoluteGaloisGroup K) →+ AddCircle (1 : ℚ))
    (hχ : IsOpen (χ.ker : Set (Additive (AbsoluteGaloisGroup K))))
    (a : H0 (AbsoluteGaloisGroup K) (IdeleCoeff K)) :
    ideleInfiniteBrLocalization w (characterCarryCocycle χ hχ a :
      H2 (AbsoluteGaloisGroup K) (IdeleCoeff K)) =
      unitsRepH2Equiv w.Completion
        (characterCarryCocycle
          (χ.comp (absoluteGaloisGroupMap τ :
            AbsoluteGaloisGroup w.Completion →* AbsoluteGaloisGroup K).toAdditive)
          (by
            rw [← AddMonoidHom.comap_ker, AddSubgroup.coe_comap]
            exact hχ.preimage (continuous_ofMul.comp
              ((absoluteGaloisGroupMap τ).continuous.comp continuous_toMul)))
          (explicitMap0 (AbsoluteGaloisGroup K) (IdeleCoeff K)
            (absoluteGaloisGroupMap τ) (ideleCoeffInfiniteComponent τ)
            (ideleCoeffInfiniteComponent_smul τ) a) :
          H2 (AbsoluteGaloisGroup w.Completion) (UnitsCoeff w.Completion)) := by
  rw [ideleInfiniteBrLocalization_apply τ, explicitMap2_mk,
    cocyclesMap2_characterCarryCocycle]

/-- A global idele carry class has zero localization at an infinite place where its idele
coefficient has component `1` (written `0` in the additive coefficient module). -/
theorem ideleInfiniteBrLocalization_characterCarryCocycle_eq_zero_of_component_eq_zero
    (χ : Additive (AbsoluteGaloisGroup K) →+ AddCircle (1 : ℚ))
    (hχ : IsOpen (χ.ker : Set (Additive (AbsoluteGaloisGroup K))))
    (a : H0 (AbsoluteGaloisGroup K) (IdeleCoeff K))
    (ha : ideleCoeffInfiniteComponent τ (a : IdeleCoeff K) = 0) :
    ideleInfiniteBrLocalization w (characterCarryCocycle χ hχ a :
      H2 (AbsoluteGaloisGroup K) (IdeleCoeff K)) = 0 := by
  rw [ideleInfiniteBrLocalization_characterCarryCocycle τ]
  have ha' : explicitMap0 (AbsoluteGaloisGroup K) (IdeleCoeff K)
      (absoluteGaloisGroupMap τ :
        AbsoluteGaloisGroup w.Completion →* AbsoluteGaloisGroup K)
      (ideleCoeffInfiniteComponent τ)
      (ideleCoeffInfiniteComponent_smul τ) a = 0 := by
    apply Subtype.ext
    simpa only [coe_explicitMap0, AddSubgroup.coe_zero] using ha
  rw [ha']
  simp

/-- **The archimedean character formula for a global idele carry class.** Let
`χ : G_K → ℚ/ℤ` be a character with open kernel and `a` an invariant idele of `Kˢ` whose component
at the infinite place `w` along `τ` is `b ∈ K_wˣ`. If `σ` represents the archimedean Artin symbol
of `b`, then the localization at `w` of the carry class `a ∪ δχ` has invariant `χ` of the image of
`σ` under the decomposition map of `τ`. -/
theorem infiniteInvMap_ideleInfiniteBrLocalization_characterCarryCocycle_of_mk_eq_infiniteArtinAt
    (χ : Additive (AbsoluteGaloisGroup K) →+ AddCircle (1 : ℚ))
    (hχ : IsOpen (χ.ker : Set (Additive (AbsoluteGaloisGroup K))))
    (a : H0 (AbsoluteGaloisGroup K) (IdeleCoeff K)) (b : w.Completionˣ)
    (hb : ideleCoeffInfiniteComponent τ (a : IdeleCoeff K) =
      (baseUnitsEquivInvariants w.Completion (.ofMul b) : UnitsCoeff w.Completion))
    (σ : Field.absoluteGaloisGroup w.Completion)
    (hσ : (σ : Field.absoluteGaloisGroupAbelianization w.Completion) = infiniteArtinAt w b) :
    infiniteInvMap w (ideleInfiniteBrLocalization w (characterCarryCocycle χ hχ a :
        H2 (AbsoluteGaloisGroup K) (IdeleCoeff K))) =
      χ (.ofMul (absoluteGaloisGroupMap τ (absoluteGaloisGroupRestrictEquiv w.Completion σ))) := by
  rw [ideleInfiniteBrLocalization_characterCarryCocycle τ]
  have hb' : explicitMap0 (AbsoluteGaloisGroup K) (IdeleCoeff K)
      (absoluteGaloisGroupMap τ : AbsoluteGaloisGroup w.Completion →* AbsoluteGaloisGroup K)
      (ideleCoeffInfiniteComponent τ) (ideleCoeffInfiniteComponent_smul τ) a =
        baseUnitsEquivInvariants w.Completion (.ofMul b) :=
    Subtype.ext (by simpa only [coe_explicitMap0] using hb)
  rw [hb']
  exact infiniteInvMap_characterCarryCocycle_of_mk_eq_infiniteArtinAt w _ b σ hσ

end Infinite

/-! ### The sum of the local invariants of an idele carry class -/

section Sum

variable (χ : Additive (AbsoluteGaloisGroup K) →+ AddCircle (1 : ℚ))
  (hχ : IsOpen (χ.ker : Set (Additive (AbsoluteGaloisGroup K))))
  (a : H0 (AbsoluteGaloisGroup K) (IdeleCoeff K))
  (τ : ∀ v : HeightOneSpectrum (𝓞 K),
    SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K))
  (b : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ)
  (σ : ∀ v : HeightOneSpectrum (𝓞 K), Field.absoluteGaloisGroup (v.adicCompletion K))
  (τ' : ∀ w : InfinitePlace K, SeparableClosure K →ₐ[K] SeparableClosure w.Completion)
  (b' : ∀ w : InfinitePlace K, w.Completionˣ)
  (σ' : ∀ w : InfinitePlace K, Field.absoluteGaloisGroup w.Completion)
  (hb : ∀ v, ideleCoeffComponent (τ v) (a : IdeleCoeff K) =
    (baseUnitsEquivInvariants (v.adicCompletion K) (.ofMul (b v)) :
      UnitsCoeff (v.adicCompletion K)))
  (hσ : ∀ v, (σ v : Field.absoluteGaloisGroupAbelianization (v.adicCompletion K)) =
    artinMap (v.adicCompletion K) (b v))
  (hb' : ∀ w, ideleCoeffInfiniteComponent (τ' w) (a : IdeleCoeff K) =
    (baseUnitsEquivInvariants w.Completion (.ofMul (b' w)) : UnitsCoeff w.Completion))
  (hσ' : ∀ w, (σ' w : Field.absoluteGaloisGroupAbelianization w.Completion) =
    infiniteArtinAt w (b' w))

include hb hσ hb' hσ' in
/-- **The sum of the local invariants of a global idele carry class.** Let `χ : G_K → ℚ/ℤ` be a
character with open kernel and `a` an invariant idele of `Kˢ` with components `b v ∈ K_vˣ` and
`b' w ∈ K_wˣ` along chosen embeddings of separable closures. Choose at every place a
representative of the local Artin symbol of the component. Then the sum of the local invariants of
`a ∪ δχ` is the sum of the values of `χ` on the images of these representatives in `G_K`, computed
over any finite set `S` of finite places outside which those values vanish. -/
theorem sumLocalInv_ideleLocalization_characterCarryCocycle {S : Finset (HeightOneSpectrum (𝓞 K))}
    (hS : ∀ v ∉ S, χ (.ofMul (absoluteGaloisGroupMap (τ v)
      (absoluteGaloisGroupRestrictEquiv (v.adicCompletion K) (σ v)))) = 0) :
    sumLocalInv K (ideleLocalization K (characterCarryCocycle χ hχ a :
        H2 (AbsoluteGaloisGroup K) (IdeleCoeff K))) =
      ∑ v ∈ S, χ (.ofMul (absoluteGaloisGroupMap (τ v)
          (absoluteGaloisGroupRestrictEquiv (v.adicCompletion K) (σ v)))) +
        ∑ w, χ (.ofMul (absoluteGaloisGroupMap (τ' w)
          (absoluteGaloisGroupRestrictEquiv w.Completion (σ' w)))) := by
  have hfin (v) := invMap_ideleBrLocalization_characterCarryCocycle_of_mk_eq_artinMap (τ v) χ hχ
    a (b v) (hb v) (σ v) (hσ v)
  have hinf (w) :=
    infiniteInvMap_ideleInfiniteBrLocalization_characterCarryCocycle_of_mk_eq_infiniteArtinAt
      (τ' w) χ hχ a (b' w) (hb' w) (σ' w) (hσ' w)
  rw [sumLocalInv_eq_sum K _ fun v hv ↦ by
    rw [ideleLocalization_fst_apply, ← map_eq_zero_iff _ (invMap (v.adicCompletion K)).injective]
    exact (hfin v).trans (hS v hv)]
  simp only [ideleLocalization_fst_apply, ideleLocalization_snd_apply, hfin, hinf]

include hχ hb hσ in
/-- **A character vanishes on almost all local Artin symbols of the components of an idele.** In
the setting of `sumLocalInv_ideleLocalization_characterCarryCocycle`, `χ` vanishes on the image
in `G_K` of the local Artin symbol of the component of `a` at all but finitely many finite places:
these values are the local invariants of the idele carry class `a ∪ δχ`. -/
theorem finite_setOf_apply_absoluteGaloisGroupMap_ne_zero_of_ideleCoeffComponent_eq :
    {v | χ (.ofMul (absoluteGaloisGroupMap (τ v)
      (absoluteGaloisGroupRestrictEquiv (v.adicCompletion K) (σ v)))) ≠ 0}.Finite :=
  (finite_setOfPred_ideleBrLocalization_ne_zero (characterCarryCocycle χ hχ a :
      H2 (AbsoluteGaloisGroup K) (IdeleCoeff K))).subset fun v hv h ↦ hv <| by
    rw [← invMap_ideleBrLocalization_characterCarryCocycle_of_mk_eq_artinMap (τ v) χ hχ a (b v)
      (hb v) (σ v) (hσ v), h, map_zero]

include hb hσ hb' hσ' in
/-- **The sum of the local invariants of a global idele carry class**, as a finite sum over all
finite places: `Σ inv (a ∪ δχ) = ∑ᶠ v, χ (Art_v a_v) + ∑_w χ (Art_w a_w)`, the local Artin
symbols of the components of `a` being read in `G_K` through chosen representatives and
decomposition maps. -/
theorem sumLocalInv_ideleLocalization_characterCarryCocycle_eq_finsum :
    sumLocalInv K (ideleLocalization K (characterCarryCocycle χ hχ a :
        H2 (AbsoluteGaloisGroup K) (IdeleCoeff K))) =
      ∑ᶠ v, χ (.ofMul (absoluteGaloisGroupMap (τ v)
          (absoluteGaloisGroupRestrictEquiv (v.adicCompletion K) (σ v)))) +
        ∑ w, χ (.ofMul (absoluteGaloisGroupMap (τ' w)
          (absoluteGaloisGroupRestrictEquiv w.Completion (σ' w)))) := by
  have hfin := finite_setOf_apply_absoluteGaloisGroupMap_ne_zero_of_ideleCoeffComponent_eq χ hχ a
    τ b σ hb hσ
  rw [finsum_eq_sum_of_support_subset _ (s := hfin.toFinset) fun v hv ↦ by simpa using hv]
  exact sumLocalInv_ideleLocalization_characterCarryCocycle χ hχ a τ b σ τ' b' σ' hb hσ hb' hσ'
    fun v hv ↦ by simpa using hv

end Sum

/-! ### Carry classes on the layers over `K` -/

section Layer

open NormalLayer

variable (χ : Additive (AbsoluteGaloisGroup K) →+ AddCircle (1 : ℚ))
  (V : OpenNormalSubgroup (AbsoluteGaloisGroup K))
  (χ' : Additive (Abelianization (ofOpenNormal V).Gal) →+ AddCircle (1 : ℚ))
  (hχ' : ∀ g : AbsoluteGaloisGroup K, χ (.ofMul g) =
    χ' (.ofMul (Abelianization.of
      ((galOfOpenNormalEquiv V).symm (g : AbsoluteGaloisGroup K ⧸ V.toSubgroup)))))
  (a' : (ideleFormation K).level (ofOpenNormal V).ground)

include hχ' in
/-- **The class over `G_K` of the Artin character cup of an idele is its carry class.** Let `χ'` be
a character of the abelianized Galois group of the layer `V ◁ G_K` of the idele formation, read on
`G_K` as `χ`, and let `a'` be an element of the ground level of the layer, an invariant idele, which
is `a` as an element of `H⁰(G_K, I_{Kˢ})`. Then the class over `G_K` of the class `a' ∪ δχ'` of the
character formula of the layer is the idele carry class of `χ` and `a`. -/
theorem ideleLayerCorInfl_artinCharacterCup
    (hχ : IsOpen (χ.ker : Set (Additive (AbsoluteGaloisGroup K))))
    (a : H0 (AbsoluteGaloisGroup K) (IdeleCoeff K))
    (ha : ideleCoeffEquivIdeleFormation K (a : IdeleCoeff K) = a') :
    ideleLayerCorInfl K (ofOpenNormal V)
        ((ofOpenNormal V).artinCharacterCup (ideleFormation K) a' χ') =
      (characterCarryCocycle χ hχ a : H2 (AbsoluteGaloisGroup K) (IdeleCoeff K)) := by
  -- The carry of `χ` at `u, v ∈ G_K` is the carry of `χ'` at their classes in `G_K ⧸ V`.
  have hcarry (u v : (ofOpenNormal V).ground) :
      characterCarry (χ'.comp Abelianization.of.toAdditive) (u : (ofOpenNormal V).Gal) v =
        characterCarry χ (u : AbsoluteGaloisGroup K) v := by
    simpa only [galOfOpenNormalEquiv_symm_mk] using
      characterCarry_galOfOpenNormalEquiv_symm V χ' χ hχ' u v
  rw [ideleLayerCorInfl_apply,
    ← LinearEquiv.apply_symm_apply ((ofOpenNormal V).groundLevelEquiv (ideleFormation K)) a',
    artinCharacterCup_groundLevelEquiv_eq_H2π, NormalLayer.explicitInfl2_H2π]
  -- The inflated layer cocycle is the restriction of the carry cocycle of `χ` to the ground
  -- subgroup `⊤`, and corestriction from `⊤` after restriction is multiplication by the index `1`.
  refine (congrArg (explicitCor2 _ _ _ _) (?_ : _ = explicitRes2 (AbsoluteGaloisGroup K)
    (IdeleCoeff K) _ (characterCarryCocycle χ hχ a :
      H2 (AbsoluteGaloisGroup K) (IdeleCoeff K)))).trans ?_
  · rw [explicitRes2_mk]
    congr 1
    refine Subtype.ext (funext fun ⟨u, v⟩ ↦ ?_)
    simp only [inflCocycle2_apply, TauCeti.groupCohomology.characterCarryCocycles₂_apply,
      cocyclesMap2_apply, characterCarryCocycle_apply, AddSubgroupClass.coe_zsmul, map_zsmul,
      AddMonoidHom.id_apply]
    refine congrArg₂ (· • ·) (hcarry u v) ((AddEquiv.symm_apply_eq _).2 ?_)
    exact (groundLevelEquiv_symm_apply_coe _ _ a').trans ha.symm
  · rw [explicitCor2_comp_res2, ground_ofOpenNormal, OpenSubgroup.toSubgroup_top,
      Subgroup.index_top, one_smul]

include hχ' in
/-- **The idelic character formula on the layers over `K`.** Let `χ'` be a character of the
abelianized Galois group of the layer `V ◁ G_K` of the idele formation, read on `G_K` as `χ`, and
let `a'` be an element of the ground level of the layer, an invariant idele, with components `b v`
and `b' w` along chosen embeddings of separable closures. Choose at every place a representative
of the local Artin symbol of the component. Then the sum of the local invariants of the class
`a' ∪ δχ'` of the character formula of the layer is the sum over all places of the values of `χ`
on the images of these representatives in `G_K`:

```text
Σ inv (a' ∪ δχ') = ∑ᶠ v, χ (Art_v a_v) + ∑_w χ (Art_w a_w).
```
-/
theorem ideleSumLocalInv_artinCharacterCup
    (τ : ∀ v : HeightOneSpectrum (𝓞 K),
      SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K))
    (b : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ)
    (σ : ∀ v : HeightOneSpectrum (𝓞 K), Field.absoluteGaloisGroup (v.adicCompletion K))
    (τ' : ∀ w : InfinitePlace K, SeparableClosure K →ₐ[K] SeparableClosure w.Completion)
    (b' : ∀ w : InfinitePlace K, w.Completionˣ)
    (σ' : ∀ w : InfinitePlace K, Field.absoluteGaloisGroup w.Completion)
    (hb : ∀ v, ideleCoeffComponent (τ v)
      ((ideleCoeffEquivIdeleFormation K).symm (a' : (ideleFormation K).toRep.V)) =
        (baseUnitsEquivInvariants (v.adicCompletion K) (.ofMul (b v)) :
          UnitsCoeff (v.adicCompletion K)))
    (hσ : ∀ v, (σ v : Field.absoluteGaloisGroupAbelianization (v.adicCompletion K)) =
      artinMap (v.adicCompletion K) (b v))
    (hb' : ∀ w, ideleCoeffInfiniteComponent (τ' w)
      ((ideleCoeffEquivIdeleFormation K).symm (a' : (ideleFormation K).toRep.V)) =
        (baseUnitsEquivInvariants w.Completion (.ofMul (b' w)) : UnitsCoeff w.Completion))
    (hσ' : ∀ w, (σ' w : Field.absoluteGaloisGroupAbelianization w.Completion) =
      infiniteArtinAt w (b' w)) :
    ideleSumLocalInv K (ofOpenNormal V)
        ((ofOpenNormal V).artinCharacterCup (ideleFormation K) a' χ') =
      ∑ᶠ v, χ (.ofMul (absoluteGaloisGroupMap (τ v)
          (absoluteGaloisGroupRestrictEquiv (v.adicCompletion K) (σ v)))) +
        ∑ w, χ (.ofMul (absoluteGaloisGroupMap (τ' w)
          (absoluteGaloisGroupRestrictEquiv w.Completion (σ' w)))) := by
  -- `χ` vanishes on the open subgroup `V`, so its kernel is open.
  have hχ : IsOpen (χ.ker : Set (Additive (AbsoluteGaloisGroup K))) :=
    AddSubgroup.isOpen_mono (H₁ := V.toSubgroup.toAddSubgroup)
      (fun g hg ↦ by
        rw [AddMonoidHom.mem_ker, ← ofMul_toMul g, hχ', (QuotientGroup.eq_one_iff g.toMul).2 hg]
        simp)
      (V.isOpen.preimage continuous_toMul)
  -- The invariant idele `a'`, as an element of `H⁰(G_K, I_{Kˢ})`.
  let a : H0 (AbsoluteGaloisGroup K) (IdeleCoeff K) :=
    ⟨(ideleCoeffEquivIdeleFormation K).symm a', (FixedPoints.mem_addSubgroup _ _ _).2 fun g ↦
      (ideleCoeffEquivIdeleFormation K).injective <| by
        rw [ideleCoeffEquivIdeleFormation_smul, AddEquiv.apply_symm_apply]
        exact (Formation.mem_level _).1 a'.2 g (by simp)⟩
  rw [ideleSumLocalInv_apply, ideleLayerCorInfl_artinCharacterCup χ V χ' hχ' a' hχ a
    ((ideleCoeffEquivIdeleFormation K).apply_symm_apply _)]
  exact sumLocalInv_ideleLocalization_characterCarryCocycle_eq_finsum χ hχ a τ b σ τ' b' σ' hb hσ
    hb' hσ'

include hχ' in
/-- **The local–global character formula for the Artin map on idele classes.** Let `cf` be a class
formation on the idele-class formation of `K` whose invariant on the layer `V ◁ G_K` of an open
normal subgroup `V` is the sum of the local invariants of a lift to the ideles. Let `χ'` be a
character of the abelianized Galois group of the layer, read on `G_K` as `χ`, and let `a'` be an
invariant idele, with components `b v` and `b' w` along chosen embeddings of separable closures.
Then the character `χ'` of the Artin symbol of the idele class of `a'` is the sum over all places
of the values of `χ` on the local Artin symbols of the components of `a'`:

```text
χ' (Art [a']) = ∑ᶠ v, χ (Art_v a_v) + ∑_w χ (Art_w a_w).
```
-/
theorem ClassFormation.apply_artinMap_eq_finsum_of_inv_eq_ideleSumLocalInv
    (cf : ClassFormation (globalFormation K))
    (hcf : ∀ y : (ofOpenNormal V).H (ideleFormation K) 2,
      cf.inv (ofOpenNormal V) (groupCohomology.map (MonoidHom.id _)
        ((ofOpenNormal V).repMap (ideleClassHom K)) 2 y) = ideleSumLocalInv K (ofOpenNormal V) y)
    (τ : ∀ v : HeightOneSpectrum (𝓞 K),
      SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K))
    (b : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ)
    (σ : ∀ v : HeightOneSpectrum (𝓞 K), Field.absoluteGaloisGroup (v.adicCompletion K))
    (τ' : ∀ w : InfinitePlace K, SeparableClosure K →ₐ[K] SeparableClosure w.Completion)
    (b' : ∀ w : InfinitePlace K, w.Completionˣ)
    (σ' : ∀ w : InfinitePlace K, Field.absoluteGaloisGroup w.Completion)
    (hb : ∀ v, ideleCoeffComponent (τ v)
      ((ideleCoeffEquivIdeleFormation K).symm (a' : (ideleFormation K).toRep.V)) =
        (baseUnitsEquivInvariants (v.adicCompletion K) (.ofMul (b v)) :
          UnitsCoeff (v.adicCompletion K)))
    (hσ : ∀ v, (σ v : Field.absoluteGaloisGroupAbelianization (v.adicCompletion K)) =
      _root_.TauCeti.ClassFieldTheory.artinMap (v.adicCompletion K) (b v))
    (hb' : ∀ w, ideleCoeffInfiniteComponent (τ' w)
      ((ideleCoeffEquivIdeleFormation K).symm (a' : (ideleFormation K).toRep.V)) =
        (baseUnitsEquivInvariants w.Completion (.ofMul (b' w)) : UnitsCoeff w.Completion))
    (hσ' : ∀ w, (σ' w : Field.absoluteGaloisGroupAbelianization w.Completion) =
      infiniteArtinAt w (b' w)) :
    χ' (cf.artinMap (ofOpenNormal V)
        (((ofOpenNormal V).repMapLayerHom (ideleClassHom K)).groundMap a')) =
      ∑ᶠ v, χ (.ofMul (absoluteGaloisGroupMap (τ v)
          (absoluteGaloisGroupRestrictEquiv (v.adicCompletion K) (σ v)))) +
        ∑ w, χ (.ofMul (absoluteGaloisGroupMap (τ' w)
          (absoluteGaloisGroupRestrictEquiv w.Completion (σ' w)))) := by
  -- The layer morphism induced on `V ◁ G_K` by the map from ideles to idele classes is the
  -- identity on the Galois group of the layer, and it carries `a' ∪ δχ'` to `[a'] ∪ δχ'`.
  have hχ'' : χ'.comp (((ofOpenNormal V).repMapLayerHom (ideleClassHom K)).galEquiv
      |>.abelianizationCongr : Abelianization (ofOpenNormal V).Gal →*
        Abelianization (ofOpenNormal V).Gal).toAdditive = χ' := by
    rw [NormalLayer.repMapLayerHom_galEquiv, abelianizationCongr_refl]
    rfl
  have h := (congrArg (fun χ'' ↦
    ((ofOpenNormal V).repMapLayerHom (ideleClassHom K)).cohomologyMap 2
      ((ofOpenNormal V).artinCharacterCup (ideleFormation K) a' χ'')) hχ'').symm.trans
    (((ofOpenNormal V).repMapLayerHom (ideleClassHom K)).cohomologyMap_artinCharacterCup a' χ')
  -- By the character formula `χ' (Art [a']) = inv ([a'] ∪ δχ')`, and `inv` on the image of
  -- `a' ∪ δχ'` is its sum of local invariants.
  refine (cf.character_artinMap _ _ _).symm.trans ((congrArg (cf.inv _) h.symm).trans ?_)
  refine (congrArg (fun f : (ofOpenNormal V).H (ideleFormation K) 2 ⟶
      (ofOpenNormal V).H (globalFormation K) 2 ↦ cf.inv (ofOpenNormal V)
        (f ((ofOpenNormal V).artinCharacterCup (ideleFormation K) a' χ')))
    (NormalLayer.cohomologyMap_repMapLayerHom _ (ideleClassHom K) 2)).trans ?_
  exact (hcf _).trans (ideleSumLocalInv_artinCharacterCup χ V χ' hχ' a' τ b σ τ' b' σ' hb hσ
    hb' hσ')

end Layer

end Idele

/-! ### Brauer classes of global elements -/

section Brauer

variable (χ : Additive (AbsoluteGaloisGroup K) →+ AddCircle (1 : ℚ))
  (hχ : IsOpen (χ.ker : Set (Additive (AbsoluteGaloisGroup K)))) (a : Kˣ)

/-- **The archimedean invariant of a global carry class.** Let `w` be an infinite place of a
field `K`, `χ : G_K → ℚ/ℤ` a character with open kernel and `a ∈ Kˣ`. If `σ` represents the
archimedean Artin symbol of `a ∈ K_wˣ`, then the local invariant at `w` of the carry class
`a ∪ δχ` is `χ` of the image of `σ` under the decomposition map of an embedding `Kˢ → K_wˢ`. -/
theorem infiniteInvAt_characterCarryCocycle_of_mk_eq_infiniteArtinAt (w : InfinitePlace K)
    (τ : SeparableClosure K →ₐ[K] SeparableClosure w.Completion)
    (σ : Field.absoluteGaloisGroup w.Completion)
    (hσ : (σ : Field.absoluteGaloisGroupAbelianization w.Completion) =
      infiniteArtinAt w (Units.map (algebraMap K w.Completion) a)) :
    infiniteInvAt K w (unitsRepH2Equiv K (characterCarryCocycle χ hχ
        (baseUnitsEquivInvariants K (.ofMul a)) : H2 (AbsoluteGaloisGroup K) (UnitsCoeff K))) =
      χ (.ofMul (absoluteGaloisGroupMap τ
        (absoluteGaloisGroupRestrictEquiv w.Completion σ))) := by
  rw [infiniteInvAt_apply, brBaseChange_characterCarryCocycle K w.Completion τ]
  exact infiniteInvMap_characterCarryCocycle_of_mk_eq_infiniteArtinAt w _ _ σ hσ

variable [NumberField K]

/-- **The local invariant of a global carry class at a finite place.** Let `v` be a finite place
of a number field `K`, `χ : G_K → ℚ/ℤ` a character with open kernel and `a ∈ Kˣ`. If `σ`
represents the absolute local Artin symbol of `a ∈ K_vˣ`, then the local invariant at `v` of the
carry class `a ∪ δχ` is `χ` of the image of `σ` under the decomposition map of an embedding
`Kˢ → K_vˢ`. -/
theorem finiteInvAt_characterCarryCocycle_of_mk_eq_artinMap (v : HeightOneSpectrum (𝓞 K))
    (τ : SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K))
    (σ : Field.absoluteGaloisGroup (v.adicCompletion K))
    (hσ : (σ : Field.absoluteGaloisGroupAbelianization (v.adicCompletion K)) =
      artinMap (v.adicCompletion K) (Units.map (algebraMap K (v.adicCompletion K)) a)) :
    finiteInvAt K v (unitsRepH2Equiv K (characterCarryCocycle χ hχ
        (baseUnitsEquivInvariants K (.ofMul a)) : H2 (AbsoluteGaloisGroup K) (UnitsCoeff K))) =
      χ (.ofMul (absoluteGaloisGroupMap τ
        (absoluteGaloisGroupRestrictEquiv (v.adicCompletion K) σ))) := by
  rw [finiteInvAt_apply, brBaseChange_characterCarryCocycle K (v.adicCompletion K) τ]
  exact invMap_characterCarryCocycle_of_mk_eq_artinMap _ _ _ σ hσ

variable (τ : ∀ v : HeightOneSpectrum (𝓞 K),
    SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K))
  (σ : ∀ v : HeightOneSpectrum (𝓞 K), Field.absoluteGaloisGroup (v.adicCompletion K))

include hχ in
/-- **A character vanishes on almost all local Artin symbols of a global element.** For a
character `χ : G_K → ℚ/ℤ` with open kernel and `a ∈ Kˣ`, choose at every finite place `v` a
representative `σ v` of the absolute local Artin symbol of `a ∈ K_vˣ`. Then `χ` vanishes on the
image of `σ v` in `G_K` at all but finitely many `v`: these values are the local invariants of
the global carry class `a ∪ δχ`. -/
theorem finite_setOf_apply_absoluteGaloisGroupMap_ne_zero
    (hσ : ∀ v, (σ v : Field.absoluteGaloisGroupAbelianization (v.adicCompletion K)) =
      artinMap (v.adicCompletion K) (Units.map (algebraMap K (v.adicCompletion K)) a)) :
    {v | χ (.ofMul (absoluteGaloisGroupMap (τ v)
      (absoluteGaloisGroupRestrictEquiv (v.adicCompletion K) (σ v)))) ≠ 0}.Finite :=
  (brauerSupport K _).finite_toSet.subset fun v hv ↦ (mem_brauerSupport K).2 <| by
    rwa [finiteInvAt_characterCarryCocycle_of_mk_eq_artinMap χ hχ a v (τ v) (σ v) (hσ v)]

variable (τ' : ∀ w : InfinitePlace K, SeparableClosure K →ₐ[K] SeparableClosure w.Completion)
  (σ' : ∀ w : InfinitePlace K, Field.absoluteGaloisGroup w.Completion)

/-- **The sum of the local invariants of a global carry class.** For a character
`χ : G_K → ℚ/ℤ` with open kernel and `a ∈ Kˣ`, choose at every place a representative of the
local Artin symbol of `a`. Then the sum of the local invariants of the carry class `a ∪ δχ` is the
sum of the values of `χ` on the images of these representatives in `G_K`, computed over any finite
set `S` of finite places outside which those values vanish. -/
theorem sumLocalInv_brLocalization_characterCarryCocycle
    (hσ : ∀ v, (σ v : Field.absoluteGaloisGroupAbelianization (v.adicCompletion K)) =
      artinMap (v.adicCompletion K) (Units.map (algebraMap K (v.adicCompletion K)) a))
    (hσ' : ∀ w, (σ' w : Field.absoluteGaloisGroupAbelianization w.Completion) =
      infiniteArtinAt w (Units.map (algebraMap K w.Completion) a))
    {S : Finset (HeightOneSpectrum (𝓞 K))}
    (hS : ∀ v ∉ S, χ (.ofMul (absoluteGaloisGroupMap (τ v)
      (absoluteGaloisGroupRestrictEquiv (v.adicCompletion K) (σ v)))) = 0) :
    sumLocalInv K (brLocalization K (unitsRepH2Equiv K (characterCarryCocycle χ hχ
        (baseUnitsEquivInvariants K (.ofMul a)) : H2 (AbsoluteGaloisGroup K) (UnitsCoeff K)))) =
      ∑ v ∈ S, χ (.ofMul (absoluteGaloisGroupMap (τ v)
          (absoluteGaloisGroupRestrictEquiv (v.adicCompletion K) (σ v)))) +
        ∑ w, χ (.ofMul (absoluteGaloisGroupMap (τ' w)
          (absoluteGaloisGroupRestrictEquiv w.Completion (σ' w)))) := by
  have hfin (v) := finiteInvAt_characterCarryCocycle_of_mk_eq_artinMap χ hχ a v (τ v) (σ v) (hσ v)
  rw [sumLocalInv_brLocalization K _ fun v hv ↦ by_contra fun hvS ↦
      (mem_brauerSupport K).1 hv ((hfin v).trans (hS v hvS))]
  simp only [hfin, infiniteInvAt_characterCarryCocycle_of_mk_eq_infiniteArtinAt χ hχ a _ (τ' _)
    (σ' _) (hσ' _)]

/-- **The sum of the local invariants of a global carry class**, as a finite sum over all finite
places: for a character `χ : G_K → ℚ/ℤ` with open kernel and `a ∈ Kˣ`, the sum of the local
invariants of `a ∪ δχ` is `∑ᶠ v, χ (Art_v a) + ∑_w χ (Art_w a)`, the local Artin symbols being
read in `G_K` through chosen representatives and decomposition maps. -/
theorem sumLocalInv_brLocalization_characterCarryCocycle_eq_finsum
    (hσ : ∀ v, (σ v : Field.absoluteGaloisGroupAbelianization (v.adicCompletion K)) =
      artinMap (v.adicCompletion K) (Units.map (algebraMap K (v.adicCompletion K)) a))
    (hσ' : ∀ w, (σ' w : Field.absoluteGaloisGroupAbelianization w.Completion) =
      infiniteArtinAt w (Units.map (algebraMap K w.Completion) a)) :
    sumLocalInv K (brLocalization K (unitsRepH2Equiv K (characterCarryCocycle χ hχ
        (baseUnitsEquivInvariants K (.ofMul a)) : H2 (AbsoluteGaloisGroup K) (UnitsCoeff K)))) =
      ∑ᶠ v, χ (.ofMul (absoluteGaloisGroupMap (τ v)
          (absoluteGaloisGroupRestrictEquiv (v.adicCompletion K) (σ v)))) +
        ∑ w, χ (.ofMul (absoluteGaloisGroupMap (τ' w)
          (absoluteGaloisGroupRestrictEquiv w.Completion (σ' w)))) := by
  have hfin := finite_setOf_apply_absoluteGaloisGroupMap_ne_zero χ hχ a τ σ hσ
  rw [finsum_eq_sum_of_support_subset _ (s := hfin.toFinset) fun v hv ↦ by simpa using hv]
  exact sumLocalInv_brLocalization_characterCarryCocycle χ hχ a τ σ τ' σ' hσ hσ'
    fun v hv ↦ by simpa using hv

end Brauer

/-! ### Classes split by a cyclic extension -/

section Cyclic

variable [NumberField K] (E : IntermediateField K (SeparableClosure K)) [FiniteDimensional K E]
  [IsGalois K E] {g : Gal(E/K)} (hg : ∀ σ, σ ∈ Subgroup.zpowers g)
  {χ : Additive Gal(E/K) →+ AddCircle (1 : ℚ)}
  (τ : ∀ v : HeightOneSpectrum (𝓞 K),
    SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K))
  (τ' : ∀ w : InfinitePlace K, SeparableClosure K →ₐ[K] SeparableClosure w.Completion)
  (σ : Kˣ → ∀ v : HeightOneSpectrum (𝓞 K), Field.absoluteGaloisGroup (v.adicCompletion K))
  (σ' : Kˣ → ∀ w : InfinitePlace K, Field.absoluteGaloisGroup w.Completion)

include hg in
/-- **The sum of the local invariants on the classes split by a cyclic extension.** Let `E/K` be a
cyclic Galois extension of a number field inside `Kˢ`, with generator `g`, and `χ` the character of
`Gal(E/K)` with `χ(g) = 1 / [E : K]`. For every `a ∈ Kˣ`, choose at every place a representative
of the local Artin symbol of `a` and read it in `Gal(E/K)` through a decomposition map. Then the
sum of the local invariants vanishes on every Brauer class split by `E` exactly when the product
formula `∑_v χ (Art_v a) = 0` holds for every `a ∈ Kˣ`. -/
theorem forall_sumLocalInv_brLocalization_relBrInfl_eq_zero_iff
    (hχ : χ (.ofMul g) = ((1 / Module.finrank K E : ℚ) : AddCircle (1 : ℚ)))
    (hσ : ∀ a v, (σ a v : Field.absoluteGaloisGroupAbelianization (v.adicCompletion K)) =
      artinMap (v.adicCompletion K) (Units.map (algebraMap K (v.adicCompletion K)) a))
    (hσ' : ∀ a w, (σ' a w : Field.absoluteGaloisGroupAbelianization w.Completion) =
      infiniteArtinAt w (Units.map (algebraMap K w.Completion) a)) :
    (∀ y : groupCohomology (Rep.ofMulDistribMulAction Gal(E/K) Eˣ) 2,
        sumLocalInv K (brLocalization K (relBrInfl K E E.val y)) = 0) ↔
      ∀ a : Kˣ, ∑ᶠ v, χ (.ofMul (AlgEquiv.restrictNormalHom E (absoluteGaloisGroupMap (τ v)
          (absoluteGaloisGroupRestrictEquiv (v.adicCompletion K) (σ a v))))) +
        ∑ w, χ (.ofMul (AlgEquiv.restrictNormalHom E (absoluteGaloisGroupMap (τ' w)
          (absoluteGaloisGroupRestrictEquiv w.Completion (σ' a w))))) = 0 := by
  -- The sum of the local invariants of the carry class of `a` is the sum in the statement.
  have hsum (a : Kˣ) := sumLocalInv_brLocalization_characterCarryCocycle_eq_finsum
    (χ.comp (AlgEquiv.restrictNormalHom (K₁ := SeparableClosure K) E).toAdditive)
    (E.isOpen_ker_comp_restrictNormalHom χ) a τ (σ a) τ' (σ' a) (hσ a) (hσ' a)
  simp only [AddMonoidHom.comp_apply, MonoidHom.toAdditive_apply_apply, toMul_ofMul] at hsum
  refine ⟨fun h a ↦ ?_, fun h y ↦ ?_⟩
  · rw [← hsum, ← relBrInfl_cyclicClass E hg hχ]
    exact h _
  · obtain ⟨a, ha⟩ := exists_characterCarryCocycle_eq_relBrInfl E hg hχ y
    rw [← ha, hsum]
    exact h a

end Cyclic

end TauCeti.ClassFieldTheory
