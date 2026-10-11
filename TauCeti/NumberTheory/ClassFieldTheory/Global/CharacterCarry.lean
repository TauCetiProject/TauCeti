/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Brauer.CharacterCarry
public import TauCeti.NumberTheory.ClassFieldTheory.Brauer.CharacterFormula
public import TauCeti.NumberTheory.ClassFieldTheory.Global.IdeleLocalization

/-!
# Localization of global character carry classes

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
-/

public section

noncomputable section

namespace TauCeti.ClassFieldTheory

open IsDedekindDomain NumberField ContCohomology

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

end Infinite

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
