/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.Reciprocity
public import TauCeti.NumberTheory.ClassFieldTheory.Global.LocalArtin.FinitePlace
public import TauCeti.NumberTheory.ClassFieldTheory.Global.LocalArtin.InfinitePlace
import TauCeti.NumberTheory.ClassFieldTheory.Global.CharacterCarry

/-!
# Local–global compatibility of the global Artin map

Let `L/K` be a finite Galois extension of number fields. The global Artin map
`globalArtinMap K L ι : C_K → Gal(L/K)^ab` is the abstract Artin map of the global class formation,
whose invariant is the sum of the local invariants. Its local factors are the local Artin symbols
`localArtinAt K L v : K_vˣ → Gal(L/K)^ab` at the finite places and
`infiniteLocalArtinAt K L w : K_wˣ → Gal(L/K)^ab` at the infinite places, the local Artin maps read
in `Gal(L/K)^ab` through the decomposition group of a place of `L` above.

The global Artin symbol of the class of an idele `a` is determined by these local factors: every
character `χ : Gal(L/K)^ab → ℚ/ℤ` satisfies

```text
χ (Art [a]) = ∑ᶠ v, χ (Art_v a_v) + ∑_w χ (Art_w a_w)
```

(`apply_globalArtinMap_eq_finsum`). It is the character formula of the global class formation
on idele classes, `ClassFormation.apply_artinMap_eq_finsum_of_inv_eq_ideleSumLocalInv`, for the
idele `a` regarded as an invariant idele of `Kˢ`, whose coordinates are its components
(`exists_ideleCoeffComponent_ideleExtension_eq`,
`exists_ideleCoeffInfiniteComponent_ideleExtension_eq`), and with the local symbols read in
`Gal(L/K)^ab` by `decompositionRestrict_mk_eq_restrictNormalHom_absoluteGaloisGroupMap`.

Since characters separate the points of `Gal(L/K)^ab`, the restriction of the global Artin map to
the units of one completion, embedded in `C_K` as ideles concentrated at one place, is the local
Artin symbol there: `globalArtinMap_local` at a finite place, `globalArtinMap_infiniteLocal` at an
infinite place. No hypothesis of abelianity or unramifiedness is needed.

## Main results

* `TauCeti.ClassFieldTheory.apply_globalArtinMap_eq_finsum`: the value of a character on the global
  Artin symbol of an idele class is the sum of its values on the local Artin symbols of the
  components.
* `TauCeti.ClassFieldTheory.globalArtinMap_local`: on `K_vˣ` at a finite place `v`, the global
  Artin map is the local Artin symbol `localArtinAt K L v`.
* `TauCeti.ClassFieldTheory.globalArtinMap_infiniteLocal`: on `K_wˣ` at an infinite place `w`, the
  global Artin map is the local Artin symbol `infiniteLocalArtinAt K L w`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §5 (the global reciprocity law and its local
  factors).
* J. S. Milne, *Class Field Theory*, v4.03, Chapter VIII.
* J. Tate, *Global class field theory*, in J. W. S. Cassels and A. Fröhlich (eds.), *Algebraic
  Number Theory*, Chapter VII, §11.
-/

public section

noncomputable section

namespace TauCeti.ClassFieldTheory

open IsDedekindDomain _root_.NumberField NormalLayer

variable (K : Type) [Field K] [NumberField K] (L : Type) [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]

local notation "E₀" =>
  ((⊥ : FiniteGaloisIntermediateField K (SeparableClosure K)) :
    IntermediateField K (SeparableClosure K))

/-- **The local–global character formula for the global Artin map.** For a finite Galois extension
`L/K` of number fields, embedded in `Kˢ` by `ι`, every character `χ : Gal(L/K)^ab → ℚ/ℤ` takes on
the global Artin symbol of the class of an idele `a` the sum of its values on the local Artin
symbols of the components of `a`, at the finite places and at the infinite places:

```text
χ (Art [a]) = ∑ᶠ v, χ (Art_v a_v) + ∑_w χ (Art_w a_w).
```
-/
theorem apply_globalArtinMap_eq_finsum (ι : L →ₐ[K] SeparableClosure K)
    (χ : Additive (Abelianization Gal(L/K)) →+ AddCircle (1 : ℚ)) (a : IdeleGroup (𝓞 K) K) :
    χ (globalArtinMap K L ι (.ofMul (a : IdeleClassGroup (𝓞 K) K))) =
      ∑ᶠ v, χ (.ofMul (localArtinAt K L v (v.ideleFiniteCoord a))) +
        ∑ w, χ (.ofMul (infiniteLocalArtinAt K L w (w.ideleInfiniteCoord a))) := by
  -- The argument adapts the finite-place comparison of Tau Ceti pull request 20832.
  -- The idele `a`, extended to `Kˢ`, as an element of the ground level of the layer of `L`.
  let V := fixingOpenNormalSubgroup K L
  let a' : (ideleFormation K).level (ofOpenNormal V).ground :=
    groundEquivOfOpenNormal (ideleFormation K) V
      (ideleLevelEquiv (E := E₀) (fixedField_toSubgroup_top K)
        (.ofMul (GlobalNumberFields.ideleExtension K E₀ a)))
  have ha' : (ideleCoeffEquivIdeleFormation K).symm (a' : (ideleFormation K).toRep.V) =
      ideleCoeffOfIntermediateField K E₀ (.ofMul (GlobalNumberFields.ideleExtension K E₀ a)) := by
    simp only [a', groundEquivOfOpenNormal_apply_coe, ideleLevelEquiv_apply_coe,
      AddEquiv.symm_apply_apply]
  have hground : ((ofOpenNormal V).repMapLayerHom (ideleClassHom K)).groundMap a' =
      groundEquivOfOpenNormal (globalFormation K) V
        (globalGroundEquiv K (.ofMul (a : IdeleClassGroup (𝓞 K) K))) := by
    apply Subtype.ext
    simp only [LayerHom.groundMap_apply_coe, repMapLayerHom_coeffMap,
      Representation.IntertwiningMap.coe_toLinearMap, repMap_hom_apply_coe,
      Submodule.coe_inclusion, groundEquivOfOpenNormal_apply_coe, a',
      ideleLevelEquiv_apply_coe, ideleCoeffOfIntermediateField_coe, globalGroundEquiv_mk]
    exact ideleClassHom_hom_apply K _
  -- The character `χ`, read on the layer of `L` and on `G_K`.
  let χ' := χ.comp (MulEquiv.toAdditive (layerGalEquiv ι).abelianizationCongr).toAddMonoidHom
  let ψ := (χ.comp Abelianization.of.toAdditive).comp ι.restrictNormalHom.toAdditive
  have hψ (g : AbsoluteGaloisGroup K) : ψ (.ofMul g) =
      χ' (.ofMul (Abelianization.of
        ((galOfOpenNormalEquiv V).symm (g : AbsoluteGaloisGroup K ⧸ V.toSubgroup)))) := by
    simp only [ψ, χ', AddMonoidHom.comp_apply, MonoidHom.coe_toAdditive,
      Function.comp_apply, toMul_ofMul, AddEquiv.coe_toAddMonoidHom,
      MulEquiv.toAdditive_apply_apply, abelianizationCongr_of]
    rw [← layerGalEquiv_symm_restrictNormalHom ι g, MulEquiv.apply_symm_apply]
  -- Embeddings of separable closures reading the components of `a`, and representatives of the
  -- local Artin symbols of the components.
  choose τ hτ using exists_ideleCoeffComponent_ideleExtension_eq (K := K)
  choose τ' hτ' using exists_ideleCoeffInfiniteComponent_ideleExtension_eq (K := K)
  choose σ hσ using fun v : HeightOneSpectrum (𝓞 K) ↦
    QuotientGroup.mk_surjective (artinMap (v.adicCompletion K) (v.ideleFiniteCoord a))
  choose σ' hσ' using fun w : InfinitePlace K ↦
    QuotientGroup.mk_surjective (infiniteArtinAt w (w.ideleInfiniteCoord a))
  have h := (globalClassFormation K).apply_artinMap_eq_finsum_of_inv_eq_ideleSumLocalInv
    ψ V χ' hψ a'
    (fun y ↦ by rw [globalClassFormation_inv, ← ideleToClassH2_apply, globalInv_ideleToClassH2])
    τ (fun v ↦ v.ideleFiniteCoord a) σ τ' (fun w ↦ w.ideleInfiniteCoord a) σ'
    (fun v ↦ ha' ▸ hτ v a) hσ (fun w ↦ ha' ▸ hτ' w a) hσ'
  -- Read in `Gal(L/K)^ab`, the images in `G_K` of the local representatives are the local
  -- Artin symbols.
  have hfin (v : HeightOneSpectrum (𝓞 K)) :
      ψ (.ofMul (absoluteGaloisGroupMap (τ v)
        (absoluteGaloisGroupRestrictEquiv (v.adicCompletion K) (σ v)))) =
      χ (.ofMul (localArtinAt K L v (v.ideleFiniteCoord a))) := by
    rw [localArtinAt_apply, ← hσ v,
      decompositionRestrict_mk_eq_restrictNormalHom_absoluteGaloisGroupMap ι (τ v) (σ v)]
    simp only [ψ, AddMonoidHom.comp_apply, MonoidHom.coe_toAdditive, Function.comp_apply,
      toMul_ofMul]
  have hinf (w : InfinitePlace K) :
      ψ (.ofMul (absoluteGaloisGroupMap (τ' w)
        (absoluteGaloisGroupRestrictEquiv w.Completion (σ' w)))) =
      χ (.ofMul (infiniteLocalArtinAt K L w (w.ideleInfiniteCoord a))) := by
    rw [infiniteLocalArtinAt_apply, ← hσ' w,
      decompositionRestrict_mk_eq_restrictNormalHom_absoluteGaloisGroupMap ι (τ' w) (σ' w)]
    simp only [ψ, AddMonoidHom.comp_apply, MonoidHom.coe_toAdditive, Function.comp_apply,
      toMul_ofMul]
  simp only [hfin, hinf, hground] at h
  rw [globalArtinMap_apply, globalArtinEquiv_mk]
  exact h

/-- **Local–global compatibility at a finite place.** For a finite Galois extension `L/K` of number
fields and a finite place `v` of `K`, the global Artin symbol of the class of the idele
concentrated at `v` with component `x ∈ K_vˣ` is the local Artin symbol of `x` at `v`, read in
`Gal(L/K)^ab` through the decomposition group of a place of `L` above `v`. -/
@[simp]
theorem globalArtinMap_local (ι : L →ₐ[K] SeparableClosure K) (v : HeightOneSpectrum (𝓞 K))
    (x : (v.adicCompletion K)ˣ) :
    globalArtinMap K L ι
        (.ofMul (IdeleGroup.ofAdicCompletion (𝓞 K) K v x : IdeleClassGroup (𝓞 K) K)) =
      .ofMul (localArtinAt K L v x) := by
  refine sub_eq_zero.mp (CharacterModule.eq_zero_of_character_apply fun χ ↦ ?_)
  -- A character of `Gal(L/K)^ab` is an additive map to `ℚ/ℤ`.
  let χ' : Additive (Abelianization Gal(L/K)) →+ AddCircle (1 : ℚ) := χ
  have h := apply_globalArtinMap_eq_finsum K L ι χ' (IdeleGroup.ofAdicCompletion (𝓞 K) K v x)
  rw [finsum_eq_single _ v fun v' hv' ↦ by
    rw [HeightOneSpectrum.ideleFiniteCoord_ofAdicCompletion_of_ne v' hv', map_one, ofMul_one,
      map_zero]] at h
  simp only [HeightOneSpectrum.ideleFiniteCoord_ofAdicCompletion_self,
    InfinitePlace.ideleInfiniteCoord_ofAdicCompletion, map_one, ofMul_one, map_zero,
    Finset.sum_const_zero, add_zero] at h
  rw [map_sub, sub_eq_zero]
  exact h

/-- **Local–global compatibility at an infinite place.** For a finite Galois extension `L/K` of
number fields and an infinite place `w` of `K`, the global Artin symbol of the class of the idele
concentrated at `w` with component `x ∈ K_wˣ` is the archimedean local Artin symbol of `x` at `w`,
read in `Gal(L/K)^ab` through the decomposition group of a place of `L` above `w`. -/
@[simp]
theorem globalArtinMap_infiniteLocal (ι : L →ₐ[K] SeparableClosure K) (w : InfinitePlace K)
    (x : w.Completionˣ) :
    globalArtinMap K L ι
        (.ofMul (IdeleGroup.ofCompletion (𝓞 K) K w x : IdeleClassGroup (𝓞 K) K)) =
      .ofMul (infiniteLocalArtinAt K L w x) := by
  refine sub_eq_zero.mp (CharacterModule.eq_zero_of_character_apply fun χ ↦ ?_)
  -- A character of `Gal(L/K)^ab` is an additive map to `ℚ/ℤ`.
  let χ' : Additive (Abelianization Gal(L/K)) →+ AddCircle (1 : ℚ) := χ
  have h := apply_globalArtinMap_eq_finsum K L ι χ' (IdeleGroup.ofCompletion (𝓞 K) K w x)
  rw [Fintype.sum_eq_single w fun w' hw' ↦ by
    rw [InfinitePlace.ideleInfiniteCoord_ofCompletion_of_ne w' hw', map_one, ofMul_one,
      map_zero]] at h
  simp only [HeightOneSpectrum.ideleFiniteCoord_ofCompletion,
    InfinitePlace.ideleInfiniteCoord_ofCompletion_self, map_one, ofMul_one, map_zero,
    finsum_zero, zero_add] at h
  rw [map_sub, sub_eq_zero]
  exact h

end TauCeti.ClassFieldTheory
