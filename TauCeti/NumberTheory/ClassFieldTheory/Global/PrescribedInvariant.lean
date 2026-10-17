/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.CharacterCarry
public import TauCeti.NumberTheory.ClassFieldTheory.Global.LayerInvariant
import TauCeti.NumberTheory.ClassFieldTheory.Global.Cyclotomic.Input
import TauCeti.NumberTheory.LocalField.Unramified.Existence
import TauCeti.NumberTheory.NumberField.FinitePlace
import TauCeti.RepresentationTheory.Homological.ContCohomology.Corestriction.Conjugation
import TauCeti.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Idele classes with prescribed sum of local invariants

Let `K` be a number field. This file proves the cyclotomic input to the global invariant map: every
finite Galois layer `L/F` of the idele formation of `K` has a refinement `L'/F` carrying a class of
`H²(Gal(L'/F), I_{L'})` whose local invariants sum to `1 / [L : F]`
(`exists_refinement_ideleSumLocalInv_eq`).

The class is first built over `G_K` (`exists_sumLocalInv_ideleLocalization_eq`). Fix a finite place
`v` of `K` whose residue field has `q` elements, and `n ≥ 1`. The class of `q` in
`(ℤ / (q ^ n - 1))ˣ` has order `n`, so some character `ψ` of this group sends it to `1 / n`. Let `χ`
be `ψ` of the action of `G_K` on a primitive `(q ^ n - 1)`-th root of unity `ζ`: a character of
the cyclotomic extension `K(ζ)/K`. Let `a` be the idele with a uniformizer `π` of `K_v` at `v` and
`1` elsewhere. The carry class `a ∪ δχ` of `χ` and `a` localizes at every place to the carry class
of the restricted character and of the component of `a` there
(`ideleBrLocalization_characterCarryCocycle`). Away from `v` that component is `1`, so the
localization vanishes. At `v`, the root of unity `ζ` generates the unramified extension of degree
`n` of `K_v`, whose arithmetic Frobenius raises `ζ` to the `q`-th power, so the local invariant is
`v(π) · χ(Frob_v) = 1 / n` (`invMap_ideleBrLocalization_characterCarryCocycle`).

To reach a layer `V ◁ U` of `G_K`, take `n = [L : F] · [G_K : U]`. The restriction of the class to
`U` is inflated from a refinement `V' ◁ U` of the layer (`NormalLayer.exists_explicitInfl2_eq`).
Corestricting back to `G_K` multiplies by the index
(`exists_refinement_ideleLayerCorInfl_eq_index_nsmul`), which turns the sum `1 / n` into
`1 / [L : F]`.

On a layer `V ◁ G_K` over `K` itself the class can be found on the layer, not only on a
refinement, once some place has full local degree. Let `χ` be a character of `G_K` with open
kernel, `v` a finite place and `g ∈ G_{K_v}`, read in `G_K` along an embedding `τ : Kˢ → K_vˢ`.
The Artin symbols are dense in `G_{K_v}^ab`, so some `b ∈ K_vˣ` has `χ(Art_v b) = χ(τ_* g)`, and
the carry class of `χ` and of the idele concentrated at `v` with component `b` has sum of local
invariants `χ(τ_* g)` (`exists_sumLocalInv_ideleLocalization_characterCarryCocycle_eq`). For a
character of the Galois group of the layer this class comes from the layer
(`exists_ideleSumLocalInv_eq_apply_absoluteGaloisGroupMap`). If the Galois group `G_K ⧸ V` is
cyclic of order `n` and the decomposition group at `v` maps onto it, a character sending the image
of a generator to `1 / n` gives a class of the layer with sum of local invariants `1 / n`
(`exists_ideleSumLocalInv_eq_one_div_degree_of_isCyclic`). This is the class of invariant `1 / n`
that `NormalLayer.map_eq_zero_of_natCard_H2_dvd_degree` takes as input.

## Main results

* `TauCeti.ClassFieldTheory.exists_sumLocalInv_ideleLocalization_eq`: for every `n ≥ 1` there is
  a class of `H²(G_K, I_{Kˢ})` whose local invariants sum to `1 / n`.
* `TauCeti.ClassFieldTheory.exists_refinement_ideleLayerCorInfl_eq_index_nsmul`: `[G_K : U]`
  times every class of `H²(G_K, I_{Kˢ})` is the class over `G_K` of an idele-layer class of a
  refinement of a given layer over `U`.
* `TauCeti.ClassFieldTheory.exists_refinement_ideleSumLocalInv_eq`: every layer has a refinement
  carrying an idele-layer class whose local invariants sum to `1 / [L : F]`.
* `TauCeti.ClassFieldTheory.exists_sumLocalInv_ideleLocalization_characterCarryCocycle_eq`: every
  value of a character of `G_K` on a decomposition group is the sum of the local invariants of one
  of its carry classes.
* `TauCeti.ClassFieldTheory.exists_ideleSumLocalInv_eq_apply_absoluteGaloisGroupMap`: the same on
  a layer `V ◁ G_K`, for a character of its Galois group.
* `TauCeti.ClassFieldTheory.exists_ideleSumLocalInv_eq_one_div_degree_of_isCyclic`: a cyclic layer
  `V ◁ G_K` whose decomposition group at some finite place is the whole Galois group carries a
  class whose local invariants sum to `1 / [G_K : V]`.

## References

* J. S. Milne, *Class Field Theory*, Chapter VII, Lemma 7.3, and Chapter VIII, §4.
* J. Tate, *Global class field theory*, in J. W. S. Cassels and A. Fröhlich (eds.),
  *Algebraic Number Theory*, Chapter VII, §11.
-/

public section

noncomputable section

namespace TauCeti.ClassFieldTheory

open IsDedekindDomain NumberField ContCohomology
open _root_.ValuativeRel
open scoped AdicCompletionExtension _root_.IntermediateField

variable {K : Type} [Field K] [NumberField K]

local notation "Ω" => FiniteGaloisIntermediateField K (SeparableClosure K)

/-- The coordinate at `v` of an idele of `E`, along a suitable embedding of separable closures, is
its component at a place `w` of `E` above `v`. -/
private theorem exists_ideleCoeffComponent_ideleCoeffOf_eq {E : Ω} {v : HeightOneSpectrum (𝓞 K)}
    (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver v.asIdeal] (a : IdeleGroup (𝓞 E) E) :
    ∃ (τ' : w.adicCompletion E →ₐ[v.adicCompletion K] SeparableClosure (v.adicCompletion K))
      (τ : SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K)),
      (ideleCoeffComponent τ (ideleCoeffOf K E (.ofMul a))).toMul =
        Units.map (τ' : w.adicCompletion E →* _) (w.ideleFiniteCoord a) := by
  let τ' : w.adicCompletion E →ₐ[v.adicCompletion K] SeparableClosure (v.adicCompletion K) :=
    IsSepClosed.lift
  let φ : E →ₐ[K] SeparableClosure (v.adicCompletion K) :=
    (τ'.restrictScalars K).comp (IsScalarTower.toAlgHom K E (w.adicCompletion E))
  obtain ⟨τ, hτ⟩ := IsSepClosed.surjective_domRestrict_of_isSeparable (K := K)
    E.toIntermediateField (E := SeparableClosure K) (M := SeparableClosure (v.adicCompletion K)) φ
  have hτ' (x : E) : τ x = τ' (algebraMap E (w.adicCompletion E) x) :=
    congrArg (fun φ : E →ₐ[K] _ ↦ φ x) hτ
  refine ⟨τ', τ, ?_⟩
  have h := @toMul_ideleCoeffComponent_ideleCoeffOf_eq_map_ideleFiniteCoord _ _ _ v E w _ τ' τ
  exact h hτ' a

/-- An idele of a finite Galois subextension `E` with `E = K` is a `G_K`-invariant idele of
`Kˢ`. -/
private def baseIdele {E : Ω} (hE : E.toIntermediateField = ⊥) (a : IdeleGroup (𝓞 E) E) :
    H0 (AbsoluteGaloisGroup K) (IdeleCoeff K) :=
  ⟨ideleCoeffOf K E (.ofMul a), (FixedPoints.mem_addSubgroup _ _ _).2 fun g ↦
    smul_ideleCoeffOf_of_mem_fixingSubgroup
      (by rw [hE, IntermediateField.fixingSubgroup_bot]; trivial) a⟩

/-- The idele of `E` concentrated at a place `w` above `v`, with component `π ∈ K_v` there. -/
private def placeIdele {E : Ω} {v : HeightOneSpectrum (𝓞 K)} (w : HeightOneSpectrum (𝓞 E))
    [w.asIdeal.LiesOver v.asIdeal] (π : (v.adicCompletion K)ˣ) : IdeleGroup (𝓞 E) E :=
  IdeleGroup.ofAdicCompletion _ _ w
    (Units.map (algebraMap (v.adicCompletion K) (w.adicCompletion E)) π)

/-- The idele concentrated at `w` has component `π` at `w`. -/
private theorem ideleFiniteCoord_placeIdele_self {E : Ω} {v : HeightOneSpectrum (𝓞 K)}
    (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver v.asIdeal] (π : (v.adicCompletion K)ˣ) :
    w.ideleFiniteCoord (placeIdele w π) =
      Units.map (algebraMap (v.adicCompletion K) (w.adicCompletion E)) π :=
  HeightOneSpectrum.ideleFiniteCoord_ofAdicCompletion_self w _

/-- The idele concentrated at `w` has component `1` away from `w`. -/
private theorem ideleFiniteCoord_placeIdele_of_ne {E : Ω} {v : HeightOneSpectrum (𝓞 K)}
    {w' w : HeightOneSpectrum (𝓞 E)} [w.asIdeal.LiesOver v.asIdeal] (h : w' ≠ w)
    (π : (v.adicCompletion K)ˣ) :
    w'.ideleFiniteCoord (placeIdele w π) = 1 :=
  HeightOneSpectrum.ideleFiniteCoord_ofAdicCompletion_of_ne w' h _

/-- At `v`, the coordinate of the idele concentrated above `v` with component `π` is `π`. -/
private theorem exists_ideleCoeffComponent_placeIdele {E : Ω} {v : HeightOneSpectrum (𝓞 K)}
    (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver v.asIdeal] (π : (v.adicCompletion K)ˣ) :
    ∃ τ : SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K),
      ideleCoeffComponent τ (ideleCoeffOf K E (.ofMul (placeIdele w π))) =
        (baseUnitsEquivInvariants _ (.ofMul π) : UnitsCoeff _) := by
  obtain ⟨τ', τ, h⟩ := exists_ideleCoeffComponent_ideleCoeffOf_eq (v := v) w (placeIdele w π)
  have h2 := ideleFiniteCoord_placeIdele_self w π
  -- Term-mode `trans` chains: rewriting the coordinates with `rw` is far slower.
  exact ⟨τ, Additive.toMul.injective (h.trans ((congrArg (Units.map (τ' : w.adicCompletion E →*
    SeparableClosure (v.adicCompletion K))) h2).trans
      (Units.ext ((τ'.commutes (π : v.adicCompletion K)).trans
        (congrArg Units.val (toMul_coe_baseUnitsEquivInvariants _ (.ofMul π))).symm))))⟩

/-- Away from `v`, the coordinates of the idele concentrated above `v` vanish. -/
private theorem exists_ideleCoeffComponent_placeIdele_eq_zero {E : Ω}
    {v : HeightOneSpectrum (𝓞 K)} (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver v.asIdeal]
    (π : (v.adicCompletion K)ˣ) {v' : HeightOneSpectrum (𝓞 K)} (hv : v' ≠ v) :
    ∃ τ : SeparableClosure K →ₐ[K] SeparableClosure (v'.adicCompletion K),
      ideleCoeffComponent τ (ideleCoeffOf K E (.ofMul (placeIdele w π))) = 0 := by
  obtain ⟨w', rfl⟩ := HeightOneSpectrum.under_surjective (𝓞 K) (𝓞 E) v'
  obtain ⟨τ', τ, h⟩ := exists_ideleCoeffComponent_ideleCoeffOf_eq (v := w'.under (𝓞 K)) w'
    (placeIdele w π)
  have hw : w' ≠ w := by
    rintro rfl
    exact hv (HeightOneSpectrum.ext (Ideal.LiesOver.over (P := w'.asIdeal)).symm)
  have h2 := ideleFiniteCoord_placeIdele_of_ne hw π
  exact ⟨τ, Additive.toMul.injective (h.trans ((congrArg (Units.map (τ' : w'.adicCompletion E →*
    SeparableClosure ((w'.under (𝓞 K)).adicCompletion K))) h2).trans (map_one _)))⟩

/-- At the infinite places, the coordinates of an idele concentrated at a finite place vanish. -/
private theorem ideleCoeffInfiniteComponent_placeIdele {E : Ω} {v : HeightOneSpectrum (𝓞 K)}
    (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver v.asIdeal] (π : (v.adicCompletion K)ˣ)
    {u : InfinitePlace K} (τ : SeparableClosure K →ₐ[K] SeparableClosure u.Completion) :
    ideleCoeffInfiniteComponent τ (ideleCoeffOf K E (.ofMul (placeIdele w π))) = 0 := by
  -- The infinite part of `IdeleGroup.ofAdicCompletion` is `1` by definition.
  have h1 : ((placeIdele w π : IdeleGroup (𝓞 E) E) : AdeleRing (𝓞 E) E).1 = 1 := rfl
  refine Additive.toMul.injective (Units.ext ((toMul_ideleCoeffInfiniteComponent_ideleCoeffOf τ E
    _).trans ?_))
  simp only [h1, map_one, toMul_zero, Units.val_one]

/-- **A carry class of an idele concentrated at a finite place is supported there**: for an idele
of `E = K` concentrated at a place `w` above `v`, the local invariants of the carry class `a ∪ δχ`
vanish away from `v`, so their sum is the invariant at `v`. -/
private theorem sumLocalInv_ideleLocalization_characterCarryCocycle_placeIdele {E : Ω}
    (hE : E.toIntermediateField = ⊥) {v : HeightOneSpectrum (𝓞 K)} (w : HeightOneSpectrum (𝓞 E))
    [w.asIdeal.LiesOver v.asIdeal] (π : (v.adicCompletion K)ˣ)
    (χ : Additive (AbsoluteGaloisGroup K) →+ AddCircle (1 : ℚ))
    (hχ : IsOpen (χ.ker : Set (Additive (AbsoluteGaloisGroup K)))) :
    sumLocalInv K (ideleLocalization K (characterCarryCocycle χ hχ
        (baseIdele hE (placeIdele w π)) : H2 (AbsoluteGaloisGroup K) (IdeleCoeff K))) =
      invMap (v.adicCompletion K) ((ideleLocalization K (characterCarryCocycle χ hχ
        (baseIdele hE (placeIdele w π)) : H2 (AbsoluteGaloisGroup K) (IdeleCoeff K))).1 v) := by
  have hS (v' : HeightOneSpectrum (𝓞 K)) (hv' : v' ∉ ({v} : Finset _)) :
      (ideleLocalization K (characterCarryCocycle χ hχ (baseIdele hE (placeIdele w π)) :
        H2 (AbsoluteGaloisGroup K) (IdeleCoeff K))).1 v' = 0 := by
    obtain ⟨τ', hτ'⟩ := exists_ideleCoeffComponent_placeIdele_eq_zero (E := E) w π
      (Finset.notMem_singleton.1 hv')
    exact (ideleLocalization_fst_apply _ _).trans
      (ideleBrLocalization_characterCarryCocycle_eq_zero_of_component_eq_zero τ' χ hχ _ hτ')
  have hinf (u : InfinitePlace K) :
      infiniteInvMap u ((ideleLocalization K (characterCarryCocycle χ hχ
        (baseIdele hE (placeIdele w π)) : H2 (AbsoluteGaloisGroup K) (IdeleCoeff K))).2 u) = 0 := by
    rw [ideleLocalization_snd_apply,
      ideleInfiniteBrLocalization_characterCarryCocycle_eq_zero_of_component_eq_zero
        (IsSepClosed.lift : SeparableClosure K →ₐ[K] SeparableClosure u.Completion) χ hχ _
        (ideleCoeffInfiniteComponent_placeIdele w π _), map_zero]
  rw [sumLocalInv_eq_sum K _ hS, Finset.sum_singleton, Finset.sum_eq_zero fun u _ ↦ hinf u,
    add_zero]

/-- **A class of `H²(G_K, I_{Kˢ})` with sum of local invariants `1 / n`**, supported at `v`: the
carry class of a cyclotomic character and of an idele of `K` concentrated at `v`, read in the
ideles of a finite Galois subextension `E` equal to `K`. -/
private theorem exists_sumLocalInv_ideleLocalization_eq_aux {E : Ω}
    (hE : E.toIntermediateField = ⊥) (v : HeightOneSpectrum (𝓞 K)) {n : ℕ} (hn : n ≠ 0) :
    ∃ x : H2 (AbsoluteGaloisGroup K) (IdeleCoeff K),
      sumLocalInv K (ideleLocalization K x) = ((1 / n : ℚ) : AddCircle (1 : ℚ)) := by
  obtain ⟨w, hw⟩ := HeightOneSpectrum.under_surjective (𝓞 K) (𝓞 E) v
  have : w.asIdeal.LiesOver v.asIdeal := hw ▸ inferInstance
  obtain ⟨π, hπ⟩ := exists_isUniformizer (K := v.adicCompletion K)
  -- The character of `(ℤ / (q ^ n - 1))ˣ` taking `q` to `1 / n`, with `q` the residue cardinality.
  have hq : 1 < Nat.card 𝓀[v.adicCompletion K] := Finite.one_lt_card
  obtain ⟨ψ, hψ⟩ := CharacterModule.exists_apply_unitOfCoprime_pow_sub_one _ n hq hn
  have : NeZero (Nat.card 𝓀[v.adicCompletion K] ^ n - 1) :=
    ⟨by have := Nat.one_lt_pow hn hq; omega⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot (SeparableClosure K)
    (Nat.card 𝓀[v.adicCompletion K] ^ n - 1)
  -- The global character: `ψ` of the action of `G_K` on `ζ`. It kills the fixing subgroup of
  -- `K(ζ)`, which is open.
  let χ : Additive (AbsoluteGaloisGroup K) →+ AddCircle (1 : ℚ) := ψ.comp (hζ.autToPow K).toAdditive
  have hχ : IsOpen (χ.ker : Set (Additive (AbsoluteGaloisGroup K))) := by
    have : FiniteDimensional K K⟮ζ⟯ :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral ζ)
    refine AddSubgroup.isOpen_mono (H₁ := Subgroup.toAddSubgroup K⟮ζ⟯.fixingSubgroup)
      (fun g hg ↦ ?_) (K⟮ζ⟯.fixingSubgroup_isOpen.preimage continuous_toMul)
    have hu : hζ.autToPow K g.toMul = 1 := (hζ.autToPow_eq_one_iff g.toMul).2 <|
      (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg ζ
        (IntermediateField.mem_adjoin_simple_self K ζ)
    -- `ψ : CharacterModule _` is a semireducible `→+`, so `AddMonoidHom.comp_apply` cannot
    -- rewrite the composite `χ`; evaluate it definitionally.
    change ψ (.ofMul (hζ.autToPow K g.toMul)) = 0
    rw [hu, ofMul_one, map_zero]
  -- An embedding `τ : Kˢ → K_vˢ` along which the idele has coordinate `π` at `v`.
  -- `cases` rather than `obtain`, which exceeds the heartbeat budget here (as does stating this
  -- for the subextension `⊥` itself rather than a variable `E = ⊥`).
  have h0 := exists_ideleCoeffComponent_placeIdele (E := E) w π
  cases h0 with
  | intro τ hτ =>
  -- The unramified extension `E_v` of `K_v` of degree `n` contains `τ ζ`.
  let Ev := unramifiedExtension (v.adicCompletion K) (SeparableClosure (v.adicCompletion K)) n
  let := algebraicExtensionValuativeRel (v.adicCompletion K) Ev
  let := algebraicExtensionNormedFieldTopology (v.adicCompletion K) Ev
  have := finiteExtension_isNonarchimedeanLocalField (v.adicCompletion K) Ev
  have := algebraicExtension_valuativeExtension (v.adicCompletion K) Ev
  have : IsUnramified (v.adicCompletion K) Ev := isUnramified_unramifiedExtension hn
  have hτζ : τ ζ ^ Nat.card 𝓀[v.adicCompletion K] ^ n = τ ζ := by
    rw [← map_pow, ← Nat.sub_add_cancel (Nat.one_le_pow _ _ (by omega) : 1 ≤ _), pow_succ,
      hζ.pow_eq_one, one_mul]
  have hmem : τ ζ ∈ Ev := rootSet_subset_unramifiedExtension _ _ n <| by
    rw [Polynomial.mem_rootSet]
    refine ⟨FiniteField.X_pow_card_pow_sub_X_ne_zero _ hn hq, ?_⟩
    simp [hτζ]
  let ζv : Ev := ⟨τ ζ, hmem⟩
  have hζv : IsPrimitiveRoot ζv (Nat.card 𝓀[v.adicCompletion K] ^ n - 1) :=
    IsPrimitiveRoot.of_map_of_injective (f := Ev.val) (hζ.map_of_injective τ.injective)
      Subtype.val_injective
  -- The local character: `ψ` of the action of `Gal(E_v/K_v)` on `τ ζ`.
  let χv : Additive Gal(Ev/v.adicCompletion K) →+ AddCircle (1 : ℚ) :=
    ψ.comp (hζv.autToPow (v.adicCompletion K)).toAdditive
  have hχv : χ.comp (absoluteGaloisGroupMap τ :
      AbsoluteGaloisGroup (v.adicCompletion K) →* AbsoluteGaloisGroup K).toAdditive =
      χv.comp (AlgEquiv.restrictNormalHom (K₁ := SeparableClosure (v.adicCompletion K))
        Ev).toAdditive := by
    refine AddMonoidHom.ext fun g ↦ ?_
    -- Evaluate both composites with `ψ` definitionally, as for `hχ`.
    change ψ (.ofMul (hζ.autToPow K (absoluteGaloisGroupMap τ g.toMul))) =
      ψ (.ofMul (hζv.autToPow _ (AlgEquiv.restrictNormalHom Ev g.toMul)))
    -- Both automorphisms raise the root of unity to the same power.
    have hg := (hζ.autToPow_spec K (absoluteGaloisGroupMap τ g.toMul)).symm
    have hgv : AlgEquiv.restrictNormalHom Ev g.toMul ζv =
        ζv ^ ((hζ.autToPow K (absoluteGaloisGroupMap τ g.toMul) :
          ZMod (Nat.card 𝓀[v.adicCompletion K] ^ n - 1))).val := by
      refine Subtype.ext ?_
      rw [AlgEquiv.restrictNormalHom_apply, SubmonoidClass.coe_pow]
      -- `ζv` is `τ ζ` as an element of `E_v`.
      change g.toMul (τ ζ) = τ ζ ^ _
      rw [← absoluteGaloisGroupMap_commutes, hg, map_pow]
    congr 2
    exact Units.ext ((hζv.coe_autToPow_eq_natCast hgv).trans (ZMod.natCast_zmod_val _)).symm
  -- Arithmetic Frobenius raises `τ ζ` to the `q`-th power, so `χ_v (Frob) = 1 / n`.
  have hfrob : χv (.ofMul (frobeniusAlgEquiv (K := v.adicCompletion K) (L := Ev))) =
      ((1 / n : ℚ) : AddCircle (1 : ℚ)) := by
    have hy : ζv ^ Nat.card 𝓀[v.adicCompletion K] ^ n = ζv := Subtype.ext hτζ
    have hf := frobeniusAlgEquiv_apply_of_pow_natCard_pow_eq_self hn hy
    -- Evaluate the composite `χ_v` definitionally, as for `hχ`.
    change ψ (.ofMul (hζv.autToPow _ _)) = _
    rw [← hψ]
    congr 2
    exact Units.ext ((hζv.coe_autToPow_eq_natCast hf).trans (ZMod.coe_unitOfCoprime _ _).symm)
  -- The carry class of `χ` and the idele concentrated at `v` with component `π`.
  let a := baseIdele hE (placeIdele w π)
  let x : H2 (AbsoluteGaloisGroup K) (IdeleCoeff K) := characterCarryCocycle χ hχ a
  refine ⟨x, ?_⟩
  -- Its localizations vanish away from `v`, and at `v` the invariant is
  -- `v(π) · χ_v(Frob) = 1 / n`.
  refine (sumLocalInv_ideleLocalization_characterCarryCocycle_placeIdele hE w π χ hχ).trans ?_
  rw [ideleLocalization_fst_apply,
    invMap_ideleBrLocalization_characterCarryCocycle τ Ev χ hχ χv a π hχv hτ, hfrob,
    (isUniformizer_def π).1 hπ, toAdd_ofAdd, one_smul]

/-- **A class of `H²(G_K, I_{Kˢ})` with sum of local invariants `1 / n`.** -/
theorem exists_sumLocalInv_ideleLocalization_eq {n : ℕ} (hn : n ≠ 0) :
    ∃ x : H2 (AbsoluteGaloisGroup K) (IdeleCoeff K),
      sumLocalInv K (ideleLocalization K x) = ((1 / n : ℚ) : AddCircle (1 : ℚ)) :=
  exists_sumLocalInv_ideleLocalization_eq_aux (E := ⊥) rfl (Classical.arbitrary _) hn

variable (K) in
/-- **Classes over `G_K` come from refinements of a layer, up to the index of its ground.** For a
layer `V ◁ U` of the idele formation and a class `x ∈ H²(G_K, I_{Kˢ})`, the restriction of `x` to
`U` is inflated from a refinement `V' ◁ U` of the layer, and corestricting it back to `G_K` gives
`[G_K : U] • x`. -/
theorem exists_refinement_ideleLayerCorInfl_eq_index_nsmul (L : NormalLayer (AbsoluteGaloisGroup K))
    (x : H2 (AbsoluteGaloisGroup K) (IdeleCoeff K)) :
    ∃ (L' : NormalLayer (AbsoluteGaloisGroup K)) (_ : LayerRefinement L L')
      (y : L'.H (ideleFormation K) 2),
      ideleLayerCorInfl K L' y = L.ground.toSubgroup.index • x := by
  obtain ⟨L', T, y, hy⟩ := L.exists_explicitInfl2_eq (ideleCoeffEquivIdeleFormation K)
    (ideleCoeffEquivIdeleFormation_smul K) (explicitRes2 _ _ L.ground.toSubgroup x)
  refine ⟨L', T, y, ?_⟩
  rw [ideleLayerCorInfl_apply, hy]
  -- Reading a class of `U` on the same subgroup `U` is conjugation by `1`.
  refine (explicitCor2_explicitMap2_of_conj L.ground.toSubgroup L'.ground.toSubgroup
    (IdeleCoeff K) 1 _ (fun v ↦ by simp) (AddMonoidHom.id _) (fun m ↦ (one_smul _ m).symm)
    (by rw [map_one]; exact T.same_ground_toSubgroup.symm.trans (Subgroup.map_id _).symm)
    L.ground.isOpen L'.ground.isOpen _).trans ?_
  exact explicitCor2_comp_res2 _ _ _ _ x

/-- **The cyclotomic input**: every layer `L/F` of the idele formation has a refinement carrying an
idele-layer class whose local invariants sum to `1 / [L : F]`. -/
theorem exists_refinement_ideleSumLocalInv_eq (L : NormalLayer (AbsoluteGaloisGroup K)) :
    ∃ (L' : NormalLayer (AbsoluteGaloisGroup K)) (_ : LayerRefinement L L')
      (y : L'.H (ideleFormation K) 2),
      ideleSumLocalInv K L' y = ((1 / L.degree : ℚ) : AddCircle (1 : ℚ)) := by
  have hd : L.ground.toSubgroup.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  obtain ⟨x, hx⟩ := exists_sumLocalInv_ideleLocalization_eq (K := K)
    (mul_ne_zero L.degree_pos.ne' hd)
  obtain ⟨L', T, y, hy⟩ := exists_refinement_ideleLayerCorInfl_eq_index_nsmul K L x
  refine ⟨L', T, y, ?_⟩
  rw [ideleSumLocalInv_apply, hy, map_nsmul, map_nsmul, hx, ← AddCircle.coe_nsmul]
  congr 1
  rw [nsmul_eq_mul]
  push_cast
  field_simp

/-! ### Invariants prescribed on a decomposition group -/

/-- **A value of a character on a decomposition group is a value on a local Artin symbol.** For a
character `χ` of `G_K` with open kernel, an embedding `τ : Kˢ → K_vˢ` and `g ∈ G_{K_v}`, some
`b ∈ K_vˣ` has a representative `σ` of its Artin symbol with `χ(τ_* σ) = χ(τ_* g)`: the Artin
symbols are dense in `G_{K_v}^ab`, and the classes of the elements on which `χ ∘ τ_*` takes the
value `χ(τ_* g)` form a nonempty open subset. -/
private theorem exists_mk_eq_artinMap_and_apply_eq {v : HeightOneSpectrum (𝓞 K)}
    (χ : Additive (AbsoluteGaloisGroup K) →+ AddCircle (1 : ℚ))
    (hχ : IsOpen (χ.ker : Set (Additive (AbsoluteGaloisGroup K))))
    (τ : SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K))
    (g : AbsoluteGaloisGroup (v.adicCompletion K)) :
    ∃ (b : (v.adicCompletion K)ˣ) (σ : Field.absoluteGaloisGroup (v.adicCompletion K)),
      (σ : Field.absoluteGaloisGroupAbelianization (v.adicCompletion K)) =
          artinMap (v.adicCompletion K) b ∧
        χ (.ofMul (absoluteGaloisGroupMap τ
          (absoluteGaloisGroupRestrictEquiv (v.adicCompletion K) σ))) =
          χ (.ofMul (absoluteGaloisGroupMap τ g)) := by
  let e := absoluteGaloisGroupRestrictEquiv (v.adicCompletion K)
  let ψ : Field.absoluteGaloisGroup (v.adicCompletion K) → AbsoluteGaloisGroup K :=
    fun σ ↦ absoluteGaloisGroupMap τ (e σ)
  let x₀ := absoluteGaloisGroupMap τ g
  -- The elements on which `χ` takes the value `χ(x₀)` form a coset of the open kernel of `χ`.
  let T : Set (AbsoluteGaloisGroup K) := {x | χ (.ofMul x) = χ (.ofMul x₀)}
  have hT : T = (fun x ↦ Additive.ofMul (x₀⁻¹ * x)) ⁻¹' χ.ker := Set.ext fun x ↦ by
    simp [T, neg_add_eq_sub, sub_eq_zero]
  have hS : IsOpen (ψ ⁻¹' T) := by
    rw [hT]
    exact hχ.preimage (continuous_ofMul.comp (continuous_const.mul
      ((absoluteGaloisGroupMap τ).continuous.comp e.continuous)))
  have hψ : ψ (e.symm g) = x₀ := congrArg _ (e.apply_symm_apply g)
  have hg : e.symm g ∈ ψ ⁻¹' T := by
    rw [Set.mem_preimage, hψ]
    exact rfl
  obtain ⟨b, σ, hσS, hσ⟩ := (denseRange_artinMap (v.adicCompletion K)).exists_mem_open
    (QuotientGroup.isOpenMap_coe _ hS) ⟨_, Set.mem_image_of_mem _ hg⟩
  exact ⟨b, σ, hσ, hσS⟩

/-- **A carry class with sum of local invariants a value of its character on a decomposition
group**, read in the ideles of a finite Galois subextension `E` equal to `K`. -/
private theorem exists_sumLocalInv_ideleLocalization_characterCarryCocycle_eq_aux {E : Ω}
    (hE : E.toIntermediateField = ⊥) {v : HeightOneSpectrum (𝓞 K)}
    (χ : Additive (AbsoluteGaloisGroup K) →+ AddCircle (1 : ℚ))
    (hχ : IsOpen (χ.ker : Set (Additive (AbsoluteGaloisGroup K))))
    (τ : SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K))
    (g : AbsoluteGaloisGroup (v.adicCompletion K)) :
    ∃ a : H0 (AbsoluteGaloisGroup K) (IdeleCoeff K),
      sumLocalInv K (ideleLocalization K (characterCarryCocycle χ hχ a :
        H2 (AbsoluteGaloisGroup K) (IdeleCoeff K))) = χ (.ofMul (absoluteGaloisGroupMap τ g)) := by
  obtain ⟨b, σ, hσ, hχσ⟩ := exists_mk_eq_artinMap_and_apply_eq χ hχ τ g
  obtain ⟨w, hw⟩ := HeightOneSpectrum.under_surjective (𝓞 K) (𝓞 E) v
  have : w.asIdeal.LiesOver v.asIdeal := hw ▸ inferInstance
  -- An embedding `τ₁ : Kˢ → K_vˢ` along which the idele concentrated at `v` has coordinate `b`.
  have h0 := exists_ideleCoeffComponent_placeIdele (E := E) w b
  cases h0 with
  | intro τ₁ hτ₁ =>
  let a := baseIdele hE (placeIdele w b)
  refine ⟨a, ?_⟩
  -- The localizations of `a ∪ δχ` vanish away from `v`, and at `v` the invariant is
  -- `χ(τ₁_* σ)`, which does not depend on the embedding.
  rw [sumLocalInv_ideleLocalization_characterCarryCocycle_placeIdele hE w b χ hχ,
    ideleLocalization_fst_apply,
    invMap_ideleBrLocalization_characterCarryCocycle_of_mk_eq_artinMap τ₁ χ hχ a b hτ₁ σ hσ,
    ← hχσ]
  exact χ.map_ofMul_absoluteGaloisGroupMap_eq τ τ₁ _

/-- **Every value of a character on a decomposition group is the sum of the local invariants of
one of its carry classes.** Let `χ` be a character of `G_K` with open kernel, `v` a finite place
of `K`, `τ : Kˢ → K_vˢ` an embedding of separable closures and `g ∈ G_{K_v}`. Then for some
invariant idele `a`, concentrated at `v`, the local invariants of the carry class `a ∪ δχ` sum to
`χ(τ_* g)`. -/
theorem exists_sumLocalInv_ideleLocalization_characterCarryCocycle_eq
    {v : HeightOneSpectrum (𝓞 K)} (χ : Additive (AbsoluteGaloisGroup K) →+ AddCircle (1 : ℚ))
    (hχ : IsOpen (χ.ker : Set (Additive (AbsoluteGaloisGroup K))))
    (τ : SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K))
    (g : AbsoluteGaloisGroup (v.adicCompletion K)) :
    ∃ a : H0 (AbsoluteGaloisGroup K) (IdeleCoeff K),
      sumLocalInv K (ideleLocalization K (characterCarryCocycle χ hχ a :
        H2 (AbsoluteGaloisGroup K) (IdeleCoeff K))) = χ (.ofMul (absoluteGaloisGroupMap τ g)) :=
  exists_sumLocalInv_ideleLocalization_characterCarryCocycle_eq_aux (E := ⊥) rfl χ hχ τ g

open NormalLayer in
/-- **A layer over `K` carries a class whose invariant is any value of a character on a
decomposition group.** Let `χ'` be a character of the abelianized Galois group `G_K ⧸ V` of the
layer `V ◁ G_K` of the idele formation, `v` a finite place of `K`, `τ : Kˢ → K_vˢ` an embedding of
separable closures and `g ∈ G_{K_v}`. Then some class of the layer has local invariants summing to
`χ'` of the image of `g` in `G_K ⧸ V`. -/
theorem exists_ideleSumLocalInv_eq_apply_absoluteGaloisGroupMap
    (V : OpenNormalSubgroup (AbsoluteGaloisGroup K))
    (χ' : Additive (Abelianization (ofOpenNormal V).Gal) →+ AddCircle (1 : ℚ))
    {v : HeightOneSpectrum (𝓞 K)}
    (τ : SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K))
    (g : AbsoluteGaloisGroup (v.adicCompletion K)) :
    ∃ y : (ofOpenNormal V).H (ideleFormation K) 2,
      ideleSumLocalInv K (ofOpenNormal V) y =
        χ' (.ofMul (Abelianization.of ((galOfOpenNormalEquiv V).symm
          (absoluteGaloisGroupMap τ g : AbsoluteGaloisGroup K ⧸ V.toSubgroup)))) := by
  -- `χ'` read on `G_K`; it vanishes on the open subgroup `V`, so its kernel is open.
  let χ : Additive (AbsoluteGaloisGroup K) →+ AddCircle (1 : ℚ) :=
    χ'.comp (Abelianization.of.comp ((galOfOpenNormalEquiv V).symm.toMonoidHom.comp
      (QuotientGroup.mk' V.toSubgroup))).toAdditive
  have hχχ' (x : AbsoluteGaloisGroup K) : χ (.ofMul x) =
      χ' (.ofMul (Abelianization.of
        ((galOfOpenNormalEquiv V).symm (x : AbsoluteGaloisGroup K ⧸ V.toSubgroup)))) := by
    simp [χ]
  have hχ : IsOpen (χ.ker : Set (Additive (AbsoluteGaloisGroup K))) :=
    AddSubgroup.isOpen_mono (H₁ := V.toSubgroup.toAddSubgroup)
      (fun g hg ↦ by
        simp [χ, (QuotientGroup.eq_one_iff g.toMul).2 hg])
      (V.isOpen.preimage continuous_toMul)
  obtain ⟨a, ha⟩ := exists_sumLocalInv_ideleLocalization_characterCarryCocycle_eq χ hχ τ g
  -- The invariant idele `a` lies in the ground level of the layer.
  have hmem : ideleCoeffEquivIdeleFormation K (a : IdeleCoeff K) ∈
      (ideleFormation K).level (ofOpenNormal V).ground :=
    (Formation.mem_level _).2 fun u _ ↦ by
      rw [← ideleCoeffEquivIdeleFormation_smul]
      exact congrArg _ ((FixedPoints.mem_addSubgroup _ _ _).1 a.2 u)
  refine ⟨(ofOpenNormal V).artinCharacterCup (ideleFormation K) ⟨_, hmem⟩ χ', ?_⟩
  rw [ideleSumLocalInv_apply, ideleLayerCorInfl_artinCharacterCup χ V χ' hχχ' _ hχ a
    (Subtype.coe_mk _ hmem).symm, ha, hχχ']

open NormalLayer in
/-- **A cyclic layer over `K` with a place of full local degree carries a class of invariant
`1 / [L : K]`.** If the Galois group `G_K ⧸ V` of the layer `V ◁ G_K` of the idele formation is
cyclic and the decomposition group at a finite place `v`, the image of `G_{K_v}` along an
embedding `τ : Kˢ → K_vˢ`, maps onto `G_K ⧸ V`, then some class of the layer has local invariants
summing to `1 / [G_K : V]`. -/
theorem exists_ideleSumLocalInv_eq_one_div_degree_of_isCyclic
    (V : OpenNormalSubgroup (AbsoluteGaloisGroup K)) [IsCyclic (ofOpenNormal V).Gal]
    {v : HeightOneSpectrum (𝓞 K)}
    (τ : SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K))
    (hv : Function.Surjective fun g : AbsoluteGaloisGroup (v.adicCompletion K) ↦
      (absoluteGaloisGroupMap τ g : AbsoluteGaloisGroup K ⧸ V.toSubgroup)) :
    ∃ y : (ofOpenNormal V).H (ideleFormation K) 2,
      ideleSumLocalInv K (ofOpenNormal V) y =
        ((1 / (ofOpenNormal V).degree : ℚ) : AddCircle (1 : ℚ)) := by
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ofOpenNormal V).Gal)
  obtain ⟨g, hg⟩ := hv (galOfOpenNormalEquiv V γ)
  replace hg : (absoluteGaloisGroupMap τ g : AbsoluteGaloisGroup K ⧸ V.toSubgroup) =
      galOfOpenNormalEquiv V γ := hg
  -- The Galois group is commutative, so `Abelianization.of` is injective and `γ` keeps its order.
  have hof : orderOf (Abelianization.of γ) = (ofOpenNormal V).degree := by
    refine ((orderOf_injective _ ((injective_iff_map_eq_one _).2 fun x hx ↦ ?_) γ).trans
      hγ).trans (ofOpenNormal V).degree_eq_natCard_gal.symm
    rwa [← MonoidHom.mem_ker, Abelianization.ker_of,
      (commutator_eq_bot_iff _).2 inferInstance, Subgroup.mem_bot] at hx
  obtain ⟨χ', hχ'⟩ := CharacterModule.exists_apply_eq_inv_addOrderOf
    (Additive.ofMul (Abelianization.of γ))
    (by rw [addOrderOf_ofMul_eq_orderOf, hof]; exact (ofOpenNormal V).degree_pos.ne')
  obtain ⟨y, hy⟩ := exists_ideleSumLocalInv_eq_apply_absoluteGaloisGroupMap V χ' τ g
  refine ⟨y, hy.trans ?_⟩
  rw [hg, MulEquiv.symm_apply_apply]
  -- `CharacterModule` is a semireducible definition for `A →+ AddCircle (1 : ℚ)`, so `hχ'` does
  -- not rewrite the goal, which is stated for the bundled homomorphism; it applies by `exact`.
  exact hχ'.trans (by rw [addOrderOf_ofMul_eq_orderOf, hof])

end TauCeti.ClassFieldTheory
