/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.Reciprocity
public import TauCeti.NumberTheory.ClassFieldTheory.Global.LocalArtin.FinitePlace
import TauCeti.NumberTheory.ClassFieldTheory.Global.CharacterCarry
import TauCeti.NumberTheory.ClassFieldTheory.Global.Ideles.Ground

/-!
# Local–global compatibility at finite places

The global Artin map evaluated on an idele supported at one finite place is the local Artin
symbol at that place. Both maps retain their existing constructions: global reciprocity is cup
product with the fundamental class, and the local symbol is the absolute local Artin map followed
by restriction to the global extension. The comparison follows from the local–global character
formula for the sum-of-local-invariants class formation.

## References

* J. S. Milne, *Class Field Theory*, Chapter VIII, §4.
* J. Tate, *Global class field theory*, in Cassels–Fröhlich, *Algebraic Number Theory*, §11.
-/

public noncomputable section

namespace TauCeti.ClassFieldTheory

open IsDedekindDomain _root_.NumberField NormalLayer

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]

/-- The global Artin symbol of an idele supported at a finite place is its local Artin symbol,
read in the abelianized Galois group by the decomposition map. -/
@[simp]
theorem globalArtinMap_local (ι : L →ₐ[K] SeparableClosure K)
    (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ) :
    globalArtinMap K L ι
        (.ofMul (IdeleClassGroup.ofAdicCompletion (𝓞 K) K v x)) =
      .ofMul (localArtinAt K L v x) := by
  classical
  apply sub_eq_zero.mp
  apply CharacterModule.eq_zero_of_character_apply
  intro χ
  rw [map_sub, sub_eq_zero]
  let χ₀ : Additive (Abelianization Gal(L/K)) →+ AddCircle (1 : ℚ) :=
    AddMonoidHom.ofClass χ
  -- Lift the single-place idele to the ground level and pull the character back to the layer.
  let V := fixingOpenNormalSubgroup K L
  let E₀ : IntermediateField K (SeparableClosure K) :=
    (⊥ : FiniteGaloisIntermediateField K (SeparableClosure K))
  let a := IdeleGroup.ofAdicCompletion (𝓞 K) K v x
  let a' : (ideleFormation K).level (ofOpenNormal V).ground :=
    groundEquivOfOpenNormal (ideleFormation K) V
      (ideleLevelEquiv (E := E₀) (fixedField_toSubgroup_top K)
        (.ofMul (GlobalNumberFields.ideleExtension K E₀ a)))
  let χ' := χ₀.comp (MulEquiv.toAdditive (layerGalEquiv ι).abelianizationCongr).toAddMonoidHom
  let ψ := (χ₀.comp Abelianization.of.toAdditive).comp ι.restrictNormalHom.toAdditive
  have hψ (g : AbsoluteGaloisGroup K) : ψ (.ofMul g) =
      χ' (.ofMul (Abelianization.of
        ((galOfOpenNormalEquiv V).symm (g : AbsoluteGaloisGroup K ⧸ V.toSubgroup)))) := by
    simp only [ψ, χ', AddMonoidHom.comp_apply, MonoidHom.coe_toAdditive,
      Function.comp_apply, toMul_ofMul, AddEquiv.coe_toAddMonoidHom,
      MulEquiv.toAdditive_apply_apply, abelianizationCongr_of]
    rw [← layerGalEquiv_symm_restrictNormalHom ι g, MulEquiv.apply_symm_apply]
  let τ (w : HeightOneSpectrum (𝓞 K)) :
      SeparableClosure K →ₐ[K] SeparableClosure (w.adicCompletion K) := IsSepClosed.lift
  let τ' (w : InfinitePlace K) :
      SeparableClosure K →ₐ[K] SeparableClosure w.Completion := IsSepClosed.lift
  choose σ hσ using fun w : HeightOneSpectrum (𝓞 K) ↦
    QuotientGroup.mk_surjective (artinMap (w.adicCompletion K) (w.ideleFiniteCoord a))
  -- Its finite coordinates are the original components, and all infinite coordinates vanish.
  have hb (w : HeightOneSpectrum (𝓞 K)) : ideleCoeffComponent (τ w)
      ((ideleCoeffEquivIdeleFormation K).symm (a' : (ideleFormation K).toRep.V)) =
        (baseUnitsEquivInvariants (w.adicCompletion K) (.ofMul (w.ideleFiniteCoord a)) :
          UnitsCoeff (w.adicCompletion K)) := by
    simp only [a', groundEquivOfOpenNormal_apply_coe, ideleLevelEquiv_apply_coe,
      AddEquiv.symm_apply_apply, E₀, ideleCoeffOfIntermediateField_coe]
    exact ideleCoeffComponent_ideleExtension_bot w (τ w) a
  have hb' (w : InfinitePlace K) : ideleCoeffInfiniteComponent (τ' w)
      ((ideleCoeffEquivIdeleFormation K).symm (a' : (ideleFormation K).toRep.V)) =
        (baseUnitsEquivInvariants w.Completion (.ofMul (1 : w.Completionˣ)) :
          UnitsCoeff w.Completion) := by
    simp only [ofMul_one, map_zero, ZeroMemClass.coe_zero, a',
      groundEquivOfOpenNormal_apply_coe, ideleLevelEquiv_apply_coe,
      AddEquiv.symm_apply_apply]
    apply ideleCoeffInfiniteComponent_eq_zero_of_fst_eq_one
    simp [a, GlobalNumberFields.coe_ideleExtension, NumberField.adeleExtension_fst,
      IdeleGroup.val_ofAdicCompletion_apply]
  have hground : ((ofOpenNormal V).repMapLayerHom (ideleClassHom K)).groundMap a' =
      groundEquivOfOpenNormal (globalFormation K) V
        (globalGroundEquiv K (.ofMul (a : IdeleClassGroup (𝓞 K) K))) := by
    apply Subtype.ext
    simp only [LayerHom.groundMap_apply_coe, repMapLayerHom_coeffMap,
      Representation.IntertwiningMap.coe_toLinearMap, repMap_hom_apply_coe,
      Submodule.coe_inclusion, groundEquivOfOpenNormal_apply_coe, a',
      ideleLevelEquiv_apply_coe, E₀, ideleCoeffOfIntermediateField_coe, globalGroundEquiv_mk]
    exact ideleClassHom_hom_apply K _
  -- The invariant of a lifted idele class is its sum of local invariants.
  have h := (globalClassFormation K).apply_artinMap_eq_finsum_of_inv_eq_ideleSumLocalInv
    ψ V χ' hψ a'
    (fun y ↦ by rw [globalClassFormation_inv, ← ideleToClassH2_apply,
      globalInv_ideleToClassH2])
    τ (fun w ↦ w.ideleFiniteCoord a) σ τ' (fun _ ↦ 1) (fun _ ↦ 1)
    hb hσ hb' (fun _ ↦ by simp)
  have hlocal (w : HeightOneSpectrum (𝓞 K)) :
      ψ (.ofMul (absoluteGaloisGroupMap (τ w)
        (absoluteGaloisGroupRestrictEquiv (w.adicCompletion K) (σ w)))) =
      χ₀ (.ofMul (localArtinAt K L w (w.ideleFiniteCoord a))) := by
    simp only [ψ, AddMonoidHom.comp_apply, MonoidHom.coe_toAdditive,
      Function.comp_apply, toMul_ofMul]
    rw [localArtinAt_apply, ← hσ w,
      decompositionRestrict_mk_eq_restrictNormalHom_absoluteGaloisGroupMap ι (τ w) (σ w)]
  simp only [hlocal, map_one, ofMul_one, map_zero, Finset.sum_const_zero, add_zero] at h
  -- Only the component at the selected place contributes to the character formula.
  have hsum : (∑ᶠ w, χ₀ (.ofMul (localArtinAt K L w (w.ideleFiniteCoord a)))) =
      χ₀ (.ofMul (localArtinAt K L v x)) := by
    rw [finsum_eq_single _ v]
    · simp [a, HeightOneSpectrum.ideleFiniteCoord_ofAdicCompletion_self]
    · intro w hw
      simp [a, HeightOneSpectrum.ideleFiniteCoord_ofAdicCompletion_of_ne w hw]
  rw [hsum, hground] at h
  simpa only [globalArtinMap_apply, globalArtinEquiv_mk, χ', AddMonoidHom.comp_apply,
    AddEquiv.coe_toAddMonoidHom, a, V, ← IdeleClassGroup.ofAdicCompletion_apply,
    χ₀, AddMonoidHom.coe_ofClass] using h

end TauCeti.ClassFieldTheory
