/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.CharacterCarry
public import TauCeti.NumberTheory.ClassFieldTheory.Global.LayerInvariant
import TauCeti.NumberTheory.ClassFieldTheory.Global.CyclotomicInput
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

## Main results

* `TauCeti.ClassFieldTheory.exists_sumLocalInv_ideleLocalization_eq`: for every `n ≥ 1` there is
  a class of `H²(G_K, I_{Kˢ})` whose local invariants sum to `1 / n`.
* `TauCeti.ClassFieldTheory.exists_refinement_ideleLayerCorInfl_eq_index_nsmul`: `[G_K : U]`
  times every class of `H²(G_K, I_{Kˢ})` is the class over `G_K` of an idele-layer class of a
  refinement of a given layer over `U`.
* `TauCeti.ClassFieldTheory.exists_refinement_ideleSumLocalInv_eq`: every layer has a refinement
  carrying an idele-layer class whose local invariants sum to `1 / [L : F]`.

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
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (SeparableClosure K)
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
  let := finiteExtensionValuativeRel (v.adicCompletion K) Ev
  let := finiteExtensionNormedFieldTopology (v.adicCompletion K) Ev
  have := finiteExtension_isNonarchimedeanLocalField (v.adicCompletion K) Ev
  have := finiteExtension_valuativeExtension (v.adicCompletion K) Ev
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
  -- Its localizations vanish away from `v`.
  have hS (v' : HeightOneSpectrum (𝓞 K)) (hv' : v' ∉ ({v} : Finset _)) :
      (ideleLocalization K x).1 v' = 0 := by
    obtain ⟨τ', hτ'⟩ := exists_ideleCoeffComponent_placeIdele_eq_zero (E := E) w π
      (Finset.notMem_singleton.1 hv')
    exact (ideleLocalization_fst_apply _ _).trans
      (ideleBrLocalization_characterCarryCocycle_eq_zero_of_component_eq_zero τ' χ hχ a hτ')
  have hinf (u : InfinitePlace K) :
      infiniteInvMap u ((ideleLocalization K x).2 u) = 0 := by
    rw [ideleLocalization_snd_apply,
      ideleInfiniteBrLocalization_characterCarryCocycle_eq_zero_of_component_eq_zero
        IsSepClosed.lift χ hχ a (ideleCoeffInfiniteComponent_placeIdele w π _), map_zero]
  -- At `v` the invariant is `v(π) · χ_v(Frob) = 1 / n`.
  have hv : invMap (v.adicCompletion K) ((ideleLocalization K x).1 v) =
      ((1 / n : ℚ) : AddCircle (1 : ℚ)) := by
    rw [ideleLocalization_fst_apply,
      invMap_ideleBrLocalization_characterCarryCocycle τ Ev χ hχ χv a π hχv hτ, hfrob,
      (isUniformizer_def π).1 hπ, toAdd_ofAdd, one_smul]
  rw [sumLocalInv_eq_sum K _ hS, Finset.sum_singleton, hv, Finset.sum_eq_zero fun u _ ↦ hinf u,
    add_zero]

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

end TauCeti.ClassFieldTheory
