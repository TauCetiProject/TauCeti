/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.CharacterCarry
public import TauCeti.NumberTheory.ClassFieldTheory.Global.LayerInvariant
import TauCeti.FieldTheory.Normal.Embeddings
import TauCeti.NumberTheory.ClassFieldTheory.Formation.PrimeDegree
import TauCeti.NumberTheory.ClassFieldTheory.Global.CorestrictionLocalization
import TauCeti.NumberTheory.ClassFieldTheory.Global.Brauer.Sequence
import TauCeti.NumberTheory.ClassFieldTheory.Global.Cyclotomic.Input
import TauCeti.NumberTheory.ClassFieldTheory.Global.PrimeDegreeDecomposition
import TauCeti.NumberTheory.LocalField.Unramified.Existence
import TauCeti.NumberTheory.NumberField.FinitePlace
import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Basic
import TauCeti.RepresentationTheory.Homological.ContCohomology.Corestriction.Conjugation
import TauCeti.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Idele classes with prescribed local invariants

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

The integer multiples of these classes realize every family of local Brauer classes supported at
one finite place. At a real place `w`, the carry class of the idele with component `-1` at `w` and
`1` elsewhere, and of a character `ψ` of the action of `G_K` on a primitive fourth root of unity
with `ψ (-1) = 1 / 2`, has invariant `1 / 2` at `w` and vanishes elsewhere: the archimedean Artin
symbol of `-1` is complex conjugation (`infiniteArtinAt_rootsOfUnity_of_isReal`), which inverts the
root of unity. Every family of local Brauer classes is therefore the family of localizations of a
class of `H²(G_K, I_{Kˢ})` (`ideleLocalization_surjective`).

To reach a layer `V ◁ U` of `G_K`, take `n = [L : F] · [G_K : U]`. The restriction of the class to
`U` is inflated from a refinement `V' ◁ U` of the layer (`NormalLayer.exists_explicitInfl2_eq`).
Corestricting back to `G_K` multiplies by the index
(`exists_refinement_ideleLayerCorInfl_eq_index_nsmul`), which turns the sum `1 / n` into
`1 / [L : F]`.

Over `G_K` itself, every value of a character on a decomposition group is the sum of the local
invariants of a carry class. Let `χ` be a character of `G_K` with open kernel, `v` a finite place
and `g ∈ G_{K_v}`, read in `G_K` along an embedding `τ : Kˢ → K_vˢ`. The Artin symbols are dense
in `G_{K_v}^ab`, so some `b ∈ K_vˣ` has `χ(Art_v b) = χ(τ_* g)`, and the carry class of `χ` and of
the idele concentrated at `v` with component `b` has sum of local invariants `χ(τ_* g)`
(`exists_sumLocalInv_ideleLocalization_characterCarryCocycle_eq`).

On every layer `V ◁ U` the class can be found on the layer itself, not only on a refinement. Let
`F` be the fixed field of `U`, `χ` a character of `U ⧸ V`, and `g ∈ G_{K_v}` with `τ_* g ∈ U`. On
`F`, the embedding `τ` extends an embedding `τ'` of the completion `F_w` at a place `w` above `v`
(`TauCeti.exists_algHom_adicCompletion_eq`). The subgroup `H = τ_*⁻¹(U)` of `G_{K_v}` contains the
subgroup fixing `τ'(F_w)`, so by local class field theory for the open subgroup `H`
(`exists_subgroupInvMap_characterCarryCocycle_eq`) some `b ∈ F_wˣ` has
`inv_H (τ' b ∪ δχ) = χ(τ_* g)`. Let `a` be the idele of `F` concentrated at `w` with component
`b`, an idele of `Kˢ` fixed by `U`. The class `a ∪ δχ` of the layer is inflated to the carry class
of `χ` and `a` over `U` (`NormalLayer.explicitInfl2_artinCharacterCup`), and its local invariants
are computed by the Mackey formula for the corestriction from `U` to `G_K`
(`invMap_ideleBrLocalization_explicitCor2`): every place other than `v` sees only coordinates of
`a` equal to `1`, and at `v` the conjugates `τ ∘ s` of `τ` outside the double coset
`τ_*(G_{K_v}) · 1 · U` read places of `F` other than `w`. The only surviving term is the
localization along `τ`, the local carry class `τ' b ∪ δχ`, so the sum of the local invariants of
`a ∪ δχ` is `χ(τ_* g)` (`exists_ideleSumLocalInv_eq_apply_absoluteGaloisGroupMap`). If the Galois
group `U ⧸ V` is cyclic of order `n` and the decomposition subgroup `H` maps onto it, a character
sending the image of a generator to `1 / n` gives a class of the layer with sum of local
invariants `1 / n` (`exists_ideleSumLocalInv_eq_one_div_degree_of_isCyclic`). This is the class of
invariant `1 / n` that `NormalLayer.map_eq_zero_of_natCard_H2_dvd_degree` takes as input. Every
layer of prime degree has such a place
(`NormalLayer.exists_surjective_absoluteGaloisGroupMap_of_degree_prime`), so it carries a class of
invariant `1 / [U : V]` (`exists_ideleSumLocalInv_eq_one_div_degree_of_prime`).

## Main results

* `TauCeti.ClassFieldTheory.exists_sumLocalInv_ideleLocalization_eq`: for every `n ≥ 1` there is
  a class of `H²(G_K, I_{Kˢ})` whose local invariants sum to `1 / n`.
* `TauCeti.ClassFieldTheory.ideleLocalization_surjective`: every family of local Brauer classes is
  the family of localizations of a class of `H²(G_K, I_{Kˢ})`.
* `TauCeti.ClassFieldTheory.exists_refinement_ideleLayerCorInfl_eq_index_nsmul`: `[G_K : U]`
  times every class of `H²(G_K, I_{Kˢ})` is the class over `G_K` of an idele-layer class of a
  refinement of a given layer over `U`.
* `TauCeti.ClassFieldTheory.exists_refinement_ideleSumLocalInv_eq`: every layer has a refinement
  carrying an idele-layer class whose local invariants sum to `1 / [L : F]`.
* `TauCeti.ClassFieldTheory.exists_sumLocalInv_ideleLocalization_characterCarryCocycle_eq`: every
  value of a character of `G_K` on a decomposition group is the sum of the local invariants of one
  of its carry classes.
* `TauCeti.ClassFieldTheory.exists_ideleSumLocalInv_eq_apply_absoluteGaloisGroupMap`: on every
  layer `V ◁ U`, every value of a character of `U ⧸ V` on the image of a decomposition subgroup is
  the sum of the local invariants of a class of the layer.
* `TauCeti.ClassFieldTheory.exists_ideleSumLocalInv_eq_one_div_degree_of_isCyclic`: a cyclic layer
  `V ◁ U` onto whose Galois group some decomposition subgroup maps carries a class whose local
  invariants sum to `1 / [U : V]`.
* `TauCeti.ClassFieldTheory.exists_ideleSumLocalInv_eq_one_div_degree_of_prime`: every layer
  `V ◁ U` of prime degree carries such a class.

## References

* J. S. Milne, *Class Field Theory*, Chapter VII, Lemma 7.3, and Chapter VIII, §4.
* J. Tate, *Global class field theory*, in J. W. S. Cassels and A. Fröhlich (eds.),
  *Algebraic Number Theory*, Chapter VII, §11.
-/

public section

noncomputable section

namespace TauCeti.ClassFieldTheory

open IsDedekindDomain _root_.NumberField ContCohomology
open _root_.ValuativeRel
open scoped AdicCompletionExtension _root_.IntermediateField

variable {K : Type} [Field K] [NumberField K]

local notation "Ω" => FiniteGaloisIntermediateField K (SeparableClosure K)

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
  obtain ⟨τ', τ, h⟩ :=
    exists_ideleCoeffComponent_ideleCoeffOfIntermediateField_eq (v := v) w
  have h := h (placeIdele w π)
  simp only [ideleCoeffOfIntermediateField_coe] at h
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
  obtain ⟨τ', τ, h⟩ := exists_ideleCoeffComponent_ideleCoeffOfIntermediateField_eq
    (v := w'.under (𝓞 K)) w'
  have h := h (placeIdele w π)
  simp only [ideleCoeffOfIntermediateField_coe] at h
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
  have hc := toMul_ideleCoeffInfiniteComponent_ideleCoeffOfIntermediateField τ E (placeIdele w π)
  simp only [ideleCoeffOfIntermediateField_coe] at hc
  refine Additive.toMul.injective (Units.ext (hc.trans ?_))
  simp only [h1, map_one, toMul_zero, Units.val_one]

/-- **A carry class of an idele concentrated at a finite place is supported there**: for an idele
of `E = K` concentrated at a place `w` above `v`, the localizations of the carry class `a ∪ δχ`
vanish away from `v`. -/
private theorem ideleLocalization_characterCarryCocycle_placeIdele {E : Ω}
    [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (hE : E.toIntermediateField = ⊥) {v : HeightOneSpectrum (𝓞 K)} (w : HeightOneSpectrum (𝓞 E))
    [w.asIdeal.LiesOver v.asIdeal] (π : (v.adicCompletion K)ˣ)
    (χ : Additive (AbsoluteGaloisGroup K) →+ AddCircle (1 : ℚ))
    (hχ : IsOpen (χ.ker : Set (Additive (AbsoluteGaloisGroup K)))) :
    ideleLocalization K (characterCarryCocycle χ hχ (baseIdele hE (placeIdele w π)) :
        H2 (AbsoluteGaloisGroup K) (IdeleCoeff K)) =
      (DFinsupp.single v ((ideleLocalization K (characterCarryCocycle χ hχ
        (baseIdele hE (placeIdele w π)) : H2 (AbsoluteGaloisGroup K) (IdeleCoeff K))).1 v), 0) := by
  refine Prod.ext (DFinsupp.ext fun v' ↦ ?_) (funext fun u ↦ ?_)
  · obtain rfl | hv' := eq_or_ne v' v
    · rw [DFinsupp.single_eq_same]
    obtain ⟨τ', hτ'⟩ := exists_ideleCoeffComponent_placeIdele_eq_zero (E := E) w π hv'
    rw [DFinsupp.single_eq_of_ne hv']
    exact (ideleLocalization_fst_apply _ _).trans
      (ideleBrLocalization_characterCarryCocycle_eq_zero_of_component_eq_zero τ' χ hχ _ hτ')
  · exact (ideleLocalization_snd_apply _ _).trans
      (ideleInfiniteBrLocalization_characterCarryCocycle_eq_zero_of_component_eq_zero
        (IsSepClosed.lift : SeparableClosure K →ₐ[K] SeparableClosure u.Completion) χ hχ _
        (ideleCoeffInfiniteComponent_placeIdele w π _))

/-- The local invariants of a carry class of an idele concentrated at a finite place `v` sum to
its invariant at `v`. -/
private theorem sumLocalInv_ideleLocalization_characterCarryCocycle_placeIdele {E : Ω}
    (hE : E.toIntermediateField = ⊥) {v : HeightOneSpectrum (𝓞 K)} (w : HeightOneSpectrum (𝓞 E))
    [w.asIdeal.LiesOver v.asIdeal] (π : (v.adicCompletion K)ˣ)
    (χ : Additive (AbsoluteGaloisGroup K) →+ AddCircle (1 : ℚ))
    (hχ : IsOpen (χ.ker : Set (Additive (AbsoluteGaloisGroup K)))) :
    sumLocalInv K (ideleLocalization K (characterCarryCocycle χ hχ
        (baseIdele hE (placeIdele w π)) : H2 (AbsoluteGaloisGroup K) (IdeleCoeff K))) =
      invMap (v.adicCompletion K) ((ideleLocalization K (characterCarryCocycle χ hχ
        (baseIdele hE (placeIdele w π)) : H2 (AbsoluteGaloisGroup K) (IdeleCoeff K))).1 v) := by
  classical
  conv_lhs => rw [ideleLocalization_characterCarryCocycle_placeIdele hE w π χ hχ]
  exact sumLocalInv_single K v _

omit [NumberField K] in
/-- The kernel of a character of `(ℤ / m)ˣ` read on the action of `G_K` on a primitive `m`-th
root of unity is open: it contains the fixing subgroup of `K(ζ)`. -/
private theorem isOpen_ker_comp_autToPow {m : ℕ} [NeZero m] {ζ : SeparableClosure K}
    (hζ : IsPrimitiveRoot ζ m) (ψ : Additive (ZMod m)ˣ →+ AddCircle (1 : ℚ)) :
    IsOpen ((ψ.comp (hζ.autToPow K).toAdditive).ker :
      Set (Additive (AbsoluteGaloisGroup K))) := by
  have : FiniteDimensional K K⟮ζ⟯ :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral ζ)
  refine AddSubgroup.isOpen_mono (H₁ := Subgroup.toAddSubgroup K⟮ζ⟯.fixingSubgroup)
    (fun g hg ↦ ?_) (K⟮ζ⟯.fixingSubgroup_isOpen.preimage continuous_toMul)
  have hu : hζ.autToPow K g.toMul = 1 := (hζ.autToPow_eq_one_iff g.toMul).2 <|
    (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg ζ
      (IntermediateField.mem_adjoin_simple_self K ζ)
  rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, MonoidHom.toAdditive_apply_apply, hu,
    ofMul_one, map_zero]

/-- **A class of `H²(G_K, I_{Kˢ})` localizing to the invariant `1 / n` at `v` and to `0` at every
other place**: the carry class of a cyclotomic character and of an idele of `K` concentrated at
`v`, read in the ideles of a finite Galois subextension `E` equal to `K`. -/
private theorem exists_ideleLocalization_eq_sumLocalInvSection_one_div_aux {E : Ω}
    [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (hE : E.toIntermediateField = ⊥) (v : HeightOneSpectrum (𝓞 K)) {n : ℕ} (hn : n ≠ 0) :
    ∃ x : H2 (AbsoluteGaloisGroup K) (IdeleCoeff K),
      ideleLocalization K x = sumLocalInvSection K v ((1 / n : ℚ) : AddCircle (1 : ℚ)) := by
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
  -- The global character: `ψ` of the action of `G_K` on `ζ`, with open kernel.
  let χ : Additive (AbsoluteGaloisGroup K) →+ AddCircle (1 : ℚ) := ψ.comp (hζ.autToPow K).toAdditive
  have hχ : IsOpen (χ.ker : Set (Additive (AbsoluteGaloisGroup K))) :=
    isOpen_ker_comp_autToPow hζ ψ
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
    refine ⟨Polynomial.X_pow_sub_X_ne_zero (Nat.one_lt_pow hn hq), ?_⟩
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
  -- Its localizations vanish away from `v`, and at `v` the invariant is
  -- `v(π) · χ_v(Frob) = 1 / n`.
  have hx : invMap (v.adicCompletion K) (ideleBrLocalization v x) =
      ((1 / n : ℚ) : AddCircle (1 : ℚ)) := by
    rw [invMap_ideleBrLocalization_characterCarryCocycle τ Ev χ hχ χv a π hχv hτ, hfrob,
      (isUniformizer_def π).1 hπ, toAdd_ofAdd, one_smul]
  refine ⟨x, (ideleLocalization_characterCarryCocycle_placeIdele hE w π χ hχ).trans ?_⟩
  rw [sumLocalInvSection_apply, ideleLocalization_fst_apply, ← hx, AddEquiv.symm_apply_apply]

/-- **A class of `H²(G_K, I_{Kˢ})` with sum of local invariants `1 / n`.** -/
theorem exists_sumLocalInv_ideleLocalization_eq {n : ℕ} (hn : n ≠ 0) :
    ∃ x : H2 (AbsoluteGaloisGroup K) (IdeleCoeff K),
      sumLocalInv K (ideleLocalization K x) = ((1 / n : ℚ) : AddCircle (1 : ℚ)) := by
  classical
  obtain ⟨x, hx⟩ := exists_ideleLocalization_eq_sumLocalInvSection_one_div_aux (E := ⊥) rfl
    (Classical.arbitrary (HeightOneSpectrum (𝓞 K))) hn
  exact ⟨x, by rw [hx, sumLocalInv_sumLocalInvSection]⟩

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

/-! ### Ideles concentrated at one place of a finite subextension -/

section Concentrated

variable {F : IntermediateField K (SeparableClosure K)} [NumberField F]
  (w : HeightOneSpectrum (𝓞 F)) (b : (w.adicCompletion F)ˣ)

/-- The coordinate along `τ₁` of the idele of `F` concentrated at `w` vanishes if `τ₁` reads
another place `w'` of `F`. -/
private theorem ideleCoeffComponent_ofAdicCompletion_of_ne {v' : HeightOneSpectrum (𝓞 K)}
    {w' : HeightOneSpectrum (𝓞 F)} [w'.asIdeal.LiesOver v'.asIdeal]
    (τ'₁ : w'.adicCompletion F →ₐ[v'.adicCompletion K] SeparableClosure (v'.adicCompletion K))
    (τ₁ : SeparableClosure K →ₐ[K] SeparableClosure (v'.adicCompletion K))
    (hτ₁ : ∀ x : F, τ₁ x = τ'₁ (algebraMap F (w'.adicCompletion F) x)) (hw : w' ≠ w) :
    ideleCoeffComponent τ₁ (ideleCoeffOfIntermediateField K F
      (.ofMul (IdeleGroup.ofAdicCompletion (𝓞 F) F w b))) = 0 := by
  refine Additive.toMul.injective
    ((toMul_ideleCoeffComponent_ideleCoeffOfIntermediateField_eq_map_ideleFiniteCoord w' τ'₁ τ₁
      hτ₁ _).trans ?_)
  rw [HeightOneSpectrum.ideleFiniteCoord_ofAdicCompletion_of_ne w' hw, map_one]
  rfl

/-- The coordinate along `τ₁` of the idele of `F` concentrated at `w` vanishes unless `τ₁`
extends, on `F`, an embedding of the completion `F_w`. -/
private theorem ideleCoeffComponent_ofAdicCompletion_eq_zero {v' : HeightOneSpectrum (𝓞 K)}
    (τ₁ : SeparableClosure K →ₐ[K] SeparableClosure (v'.adicCompletion K))
    (h : ∀ [w.asIdeal.LiesOver v'.asIdeal]
      (τ'₁ : w.adicCompletion F →ₐ[v'.adicCompletion K] SeparableClosure (v'.adicCompletion K)),
      ¬ ∀ x : F, τ₁ x = τ'₁ (algebraMap F (w.adicCompletion F) x)) :
    ideleCoeffComponent τ₁ (ideleCoeffOfIntermediateField K F
      (.ofMul (IdeleGroup.ofAdicCompletion (𝓞 F) F w b))) = 0 := by
  obtain ⟨w₁, _, τ'₁, hτ₁⟩ := exists_algHom_adicCompletion_eq F v'
    (τ₁.comp (IsScalarTower.toAlgHom K F (SeparableClosure K)))
  by_cases hw : w₁ = w
  · subst hw
    exact absurd hτ₁ (h τ'₁)
  · exact ideleCoeffComponent_ofAdicCompletion_of_ne w b τ'₁ τ₁ hτ₁ hw

/-- The coordinate along `τ` of the idele of `F` concentrated at `w` is its component there, if `τ`
extends on `F` an embedding `τ'` of the completion `F_w`. -/
private theorem ideleCoeffComponent_ofAdicCompletion_self {v : HeightOneSpectrum (𝓞 K)}
    [w.asIdeal.LiesOver v.asIdeal]
    (τ' : w.adicCompletion F →ₐ[v.adicCompletion K] SeparableClosure (v.adicCompletion K))
    (τ : SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K))
    (hτ : ∀ x : F, τ x = τ' (algebraMap F (w.adicCompletion F) x)) :
    ideleCoeffComponent τ (ideleCoeffOfIntermediateField K F
      (.ofMul (IdeleGroup.ofAdicCompletion (𝓞 F) F w b))) =
        .ofMul (Units.map (τ' : w.adicCompletion F →* SeparableClosure (v.adicCompletion K))
          b) := by
  refine Additive.toMul.injective
    ((toMul_ideleCoeffComponent_ideleCoeffOfIntermediateField_eq_map_ideleFiniteCoord w τ' τ hτ
      _).trans ?_)
  rw [HeightOneSpectrum.ideleFiniteCoord_ofAdicCompletion_self]
  rfl

/-- At the infinite places, the coordinates of an idele of `F` concentrated at a finite place
vanish. -/
private theorem ideleCoeffInfiniteComponent_ofAdicCompletion {u : InfinitePlace K}
    (τ₁ : SeparableClosure K →ₐ[K] SeparableClosure u.Completion) :
    ideleCoeffInfiniteComponent τ₁ (ideleCoeffOfIntermediateField K F
      (.ofMul (IdeleGroup.ofAdicCompletion (𝓞 F) F w b))) = 0 := by
  -- The infinite part of `IdeleGroup.ofAdicCompletion` is `1` by definition.
  have h1 : ((IdeleGroup.ofAdicCompletion (𝓞 F) F w b : IdeleGroup (𝓞 F) F) :
      AdeleRing (𝓞 F) F).1 = 1 := rfl
  refine Additive.toMul.injective (Units.ext
    ((toMul_ideleCoeffInfiniteComponent_ideleCoeffOfIntermediateField τ₁ F _).trans ?_))
  simp only [h1, map_one, toMul_zero, Units.val_one]

/-- **Embeddings through one place of `F` lie in one double coset.** If `τ` and `τ ∘ s` both
extend, on `F`, embeddings of the same completion `F_w`, then `s` lies in the double coset
`φ_τ(G_{K_v}) · 1 · G_F`: the two embeddings of `F_w` differ by some `g ∈ G_{K_v}`, and `s` agrees
with `φ_τ(g)` on `F`. -/
private theorem doubleCoset_mk_eq_mk_one {v : HeightOneSpectrum (𝓞 K)}
    [w.asIdeal.LiesOver v.asIdeal]
    (τ' τ'₁ : w.adicCompletion F →ₐ[v.adicCompletion K] SeparableClosure (v.adicCompletion K))
    (τ : SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K))
    (hτ : ∀ x : F, τ x = τ' (algebraMap F (w.adicCompletion F) x)) (s : AbsoluteGaloisGroup K)
    (hs : ∀ x : F, τ.comp (s : SeparableClosure K →ₐ[K] SeparableClosure K) x =
      τ'₁ (algebraMap F (w.adicCompletion F) x)) :
    DoubleCoset.mk (absoluteGaloisGroupMap τ :
        AbsoluteGaloisGroup (v.adicCompletion K) →* AbsoluteGaloisGroup K).range
      F.fixingSubgroup s = DoubleCoset.mk _ _ 1 := by
  -- An automorphism `g₀` of `K_vˢ` with `g₀ ∘ τ' = τ'₁`.
  let g₀ : AbsoluteGaloisGroup (v.adicCompletion K) :=
    (τ'.equivFieldRange.symm.trans τ'₁.equivFieldRange).liftNormal _
  have hg₀ (y : w.adicCompletion F) : g₀ (τ' y) = τ'₁ y :=
    AlgHom.liftNormal_equivFieldRange_apply τ' τ'₁ y
  have hmem : (absoluteGaloisGroupMap τ g₀)⁻¹ * s ∈ F.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have h' : τ (s x) = τ (absoluteGaloisGroupMap τ g₀ x) := by
      rw [absoluteGaloisGroupMap_commutes]
      have h1 := hs ⟨x, hx⟩
      simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom] at h1
      rw [h1, ← hg₀]
      exact congrArg g₀ (hτ ⟨x, hx⟩).symm
    rw [AlgEquiv.mul_apply, τ.injective h', ← AlgEquiv.mul_apply, inv_mul_cancel,
      AlgEquiv.one_apply]
  rw [eq_comm, DoubleCoset.eq]
  exact ⟨_, ⟨g₀, rfl⟩, _, hmem, by rw [mul_one]; exact (mul_inv_cancel_left _ _).symm⟩

/-- **An invariant of a decomposition subgroup is a unit of the completion.** If `τ` extends, on
`F`, an embedding `τ'` of `F_w`, an invariant `c` of the open subgroup `φ_τ⁻¹(G_F)` of `G_{K_v}` in
`(K_vˢ)ˣ` is the image under `τ'` of a unit of `F_w`: that subgroup contains the subgroup fixing
`τ'(F_w)`, whose fixed field is `τ'(F_w)`. -/
private theorem exists_coe_eq_ofMul_units_map {U : Subgroup (AbsoluteGaloisGroup K)}
    (hF : U = F.fixingSubgroup) {v : HeightOneSpectrum (𝓞 K)} [w.asIdeal.LiesOver v.asIdeal]
    (τ' : w.adicCompletion F →ₐ[v.adicCompletion K] SeparableClosure (v.adicCompletion K))
    (τ : SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K))
    (hτ : ∀ x : F, τ x = τ' (algebraMap F (w.adicCompletion F) x))
    (c : H0 (U.comap (absoluteGaloisGroupMap τ :
      AbsoluteGaloisGroup (v.adicCompletion K) →* AbsoluteGaloisGroup K))
        (UnitsCoeff (v.adicCompletion K))) :
    ∃ b : (w.adicCompletion F)ˣ, (c : UnitsCoeff (v.adicCompletion K)) =
      .ofMul (Units.map (τ' : w.adicCompletion F →* SeparableClosure (v.adicCompletion K)) b) := by
  have hle : τ'.fieldRange.fixingSubgroup ≤ U.comap
      (absoluteGaloisGroupMap τ : AbsoluteGaloisGroup (v.adicCompletion K) →*
        AbsoluteGaloisGroup K) := by
    intro g' hg'
    rw [Subgroup.mem_comap, hF, IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have h : τ (absoluteGaloisGroupMap τ g' x) = τ x := by
      rw [absoluteGaloisGroupMap_commutes, hτ ⟨x, hx⟩]
      exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg' _ ⟨_, rfl⟩
    exact τ.injective h
  obtain ⟨b₀, hb₀⟩ : ((Additive.toMul (c : UnitsCoeff (v.adicCompletion K)) :
      (SeparableClosure (v.adicCompletion K))ˣ) : SeparableClosure (v.adicCompletion K)) ∈
        τ'.fieldRange := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup τ'.fieldRange,
      IntermediateField.mem_fixedField_iff]
    intro g' hg'
    exact congrArg (fun z : UnitsCoeff (v.adicCompletion K) ↦
      ((Additive.toMul z : (SeparableClosure (v.adicCompletion K))ˣ) :
        SeparableClosure (v.adicCompletion K)))
      ((FixedPoints.mem_addSubgroup _ _ _).1 c.2 ⟨g', hle hg'⟩)
  have hb₀0 : b₀ ≠ 0 := by
    rintro rfl
    exact (Additive.toMul (c : UnitsCoeff (v.adicCompletion K))).ne_zero (by rw [← hb₀, map_zero])
  exact ⟨Units.mk0 b₀ hb₀0, congrArg Additive.ofMul (Units.ext hb₀.symm)⟩

end Concentrated

/-! ### Local invariants of corestricted carry classes -/

section Corestricted

variable (U : Subgroup (AbsoluteGaloisGroup K)) [U.FiniteIndex]
  (hU : IsOpen (U : Set (AbsoluteGaloisGroup K)))
  (χ : Additive U →+ AddCircle (1 : ℚ)) (hχ : IsOpen (χ.ker : Set (Additive U)))
  (a : H0 U (IdeleCoeff K))

/-- The corestriction to `G_K` of the carry class of an invariant idele of `U` has zero
localization at a finite place where all the coordinates of the idele vanish. -/
private theorem ideleBrLocalization_explicitCor2_characterCarryCocycle_eq_zero
    {v : HeightOneSpectrum (𝓞 K)}
    (ha : ∀ τ : SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K),
      ideleCoeffComponent τ (a : IdeleCoeff K) = 0) :
    ideleBrLocalization v (explicitCor2 (AbsoluteGaloisGroup K) (IdeleCoeff K) U hU
      (characterCarryCocycle χ hχ a : H2 U (IdeleCoeff K))) = 0 := by
  obtain ⟨τ⟩ : Nonempty (SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K)) :=
    ⟨IsSepClosed.lift⟩
  rw [ideleBrLocalization_explicitCor2 U hU τ (fun D ↦ Quotient.out D)
    (fun D ↦ DoubleCoset.out_eq' D)]
  refine Finset.sum_eq_zero fun D _ ↦ ?_
  rw [explicitMap2_characterCarryCocycle_eq_zero _ _ _ _ χ hχ a (ha _), map_zero, map_zero]

/-- The corestriction to `G_K` of the carry class of an invariant idele of `U` has zero
localization at an infinite place where all the coordinates of the idele vanish. -/
private theorem ideleInfiniteBrLocalization_explicitCor2_characterCarryCocycle_eq_zero
    {w : InfinitePlace K}
    (ha : ∀ τ : SeparableClosure K →ₐ[K] SeparableClosure w.Completion,
      ideleCoeffInfiniteComponent τ (a : IdeleCoeff K) = 0) :
    ideleInfiniteBrLocalization w (explicitCor2 (AbsoluteGaloisGroup K) (IdeleCoeff K) U hU
      (characterCarryCocycle χ hχ a : H2 U (IdeleCoeff K))) = 0 := by
  obtain ⟨τ⟩ : Nonempty (SeparableClosure K →ₐ[K] SeparableClosure w.Completion) :=
    ⟨IsSepClosed.lift⟩
  rw [ideleInfiniteBrLocalization_explicitCor2 U hU τ (fun D ↦ Quotient.out D)
    (fun D ↦ DoubleCoset.out_eq' D)]
  refine Finset.sum_eq_zero fun D _ ↦ ?_
  rw [explicitMap2_characterCarryCocycle_eq_zero _ _ _ _ χ hχ a (ha _), map_zero, map_zero]

/-- The invariant of the localization of a carry class along `τ₁` only depends on `τ₁`. -/
private theorem subgroupInvMap_explicitMap2_characterCarryCocycle_congr
    {v : HeightOneSpectrum (𝓞 K)}
    {τ₁ τ : SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K)} (h : τ₁ = τ) :
    subgroupInvMap (v.adicCompletion K)
      (U.comap (absoluteGaloisGroupMap τ₁ : AbsoluteGaloisGroup (v.adicCompletion K) →*
        AbsoluteGaloisGroup K)) (hU.preimage (absoluteGaloisGroupMap τ₁).continuous)
      (explicitMap2 U (IdeleCoeff K) _ (UnitsCoeff (v.adicCompletion K))
        ((absoluteGaloisGroupMap τ₁).subgroupComap U) (ideleCoeffComponent τ₁)
        continuous_of_discreteTopology (fun y m ↦
          ContinuousMonoidHom.subgroupComap_smul _ U y m ▸ ideleCoeffComponent_smul _ y.1 m)
        (characterCarryCocycle χ hχ a : H2 U (IdeleCoeff K))) =
    subgroupInvMap (v.adicCompletion K)
      (U.comap (absoluteGaloisGroupMap τ : AbsoluteGaloisGroup (v.adicCompletion K) →*
        AbsoluteGaloisGroup K)) (hU.preimage (absoluteGaloisGroupMap τ).continuous)
      (explicitMap2 U (IdeleCoeff K) _ (UnitsCoeff (v.adicCompletion K))
        ((absoluteGaloisGroupMap τ).subgroupComap U) (ideleCoeffComponent τ)
        continuous_of_discreteTopology (fun y m ↦
          ContinuousMonoidHom.subgroupComap_smul _ U y m ▸ ideleCoeffComponent_smul _ y.1 m)
        (characterCarryCocycle χ hχ a : H2 U (IdeleCoeff K))) := by
  subst h
  rfl

/-- **A carry class supported on one double coset.** If the coordinates of an invariant idele `a`
of `U` vanish along every conjugate `τ ∘ s` of `τ` with `s` outside the double coset
`φ_τ(G_{K_v}) · 1 · U`, then the invariant at `v` of the corestriction of `a ∪ δχ` is the invariant
of its localization along `τ`, the only surviving term of the Mackey formula. -/
private theorem invMap_ideleBrLocalization_explicitCor2_characterCarryCocycle
    {v : HeightOneSpectrum (𝓞 K)}
    (τ : SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K))
    (ha : ∀ s : AbsoluteGaloisGroup K,
      DoubleCoset.mk (absoluteGaloisGroupMap τ : AbsoluteGaloisGroup (v.adicCompletion K) →*
        AbsoluteGaloisGroup K).range U s ≠ DoubleCoset.mk _ U 1 →
      ideleCoeffComponent (τ.comp (s : SeparableClosure K →ₐ[K] SeparableClosure K))
        (a : IdeleCoeff K) = 0) :
    invMap (v.adicCompletion K) (ideleBrLocalization v (explicitCor2 (AbsoluteGaloisGroup K)
      (IdeleCoeff K) U hU (characterCarryCocycle χ hχ a : H2 U (IdeleCoeff K)))) =
      subgroupInvMap (v.adicCompletion K)
        (U.comap (absoluteGaloisGroupMap τ : AbsoluteGaloisGroup (v.adicCompletion K) →*
          AbsoluteGaloisGroup K)) (hU.preimage (absoluteGaloisGroupMap τ).continuous)
        (explicitMap2 U (IdeleCoeff K) _ (UnitsCoeff (v.adicCompletion K))
          ((absoluteGaloisGroupMap τ).subgroupComap U) (ideleCoeffComponent τ)
          continuous_of_discreteTopology (fun y m ↦
            ContinuousMonoidHom.subgroupComap_smul _ U y m ▸ ideleCoeffComponent_smul _ y.1 m)
          (characterCarryCocycle χ hχ a : H2 U (IdeleCoeff K))) := by
  classical
  -- Representatives of the double cosets, with `1` for the double coset of `1`.
  obtain ⟨r, hr, hr₀⟩ : ∃ r : DoubleCoset.Quotient ((absoluteGaloisGroupMap τ :
      AbsoluteGaloisGroup (v.adicCompletion K) →* AbsoluteGaloisGroup K).range :
        Set (AbsoluteGaloisGroup K)) (U : Set (AbsoluteGaloisGroup K)) → AbsoluteGaloisGroup K,
      (∀ D, DoubleCoset.mk _ U (r D) = D) ∧ r (DoubleCoset.mk _ U 1) = 1 := by
    refine ⟨fun D ↦ if D = DoubleCoset.mk _ U 1 then 1 else Quotient.out D, fun D ↦ ?_,
      by simp only [↓reduceIte]⟩
    by_cases h : D = DoubleCoset.mk _ U 1
    · simp only [h, ↓reduceIte]
    · simp only [h, ↓reduceIte]
      exact DoubleCoset.out_eq' D
  let := Fintype.ofFinite (DoubleCoset.Quotient ((absoluteGaloisGroupMap τ :
    AbsoluteGaloisGroup (v.adicCompletion K) →* AbsoluteGaloisGroup K).range :
      Set (AbsoluteGaloisGroup K)) (U : Set (AbsoluteGaloisGroup K)))
  -- The statements are large, so the proof is a chain of `trans` rather than `rw`.
  refine (invMap_ideleBrLocalization_explicitCor2 U hU τ r hr _).trans <|
    (Fintype.sum_eq_single (DoubleCoset.mk _ U 1) fun D hD ↦ ?_).trans ?_
  · exact (congrArg _ (explicitMap2_characterCarryCocycle_eq_zero _ _ _ _ χ hχ a
      (ha _ (by rw [hr]; exact hD)))).trans (map_zero _)
  · have hτ₁ : τ.comp ((r (DoubleCoset.mk _ U 1) : AbsoluteGaloisGroup K) :
        SeparableClosure K →ₐ[K] SeparableClosure K) = τ := by
      rw [hr₀]
      rfl
    exact subgroupInvMap_explicitMap2_characterCarryCocycle_congr U hU χ hχ a hτ₁

end Corestricted

/-! ### Invariants prescribed on a decomposition group -/

/-- **The sum of the local invariants of a carry class supported on one double coset.** Let `y` be
a class of a layer `V ◁ U` whose inflation to `U` is the carry class of `χ` and of an invariant
idele `a` whose coordinates vanish at the infinite places, at the finite places other than `v`,
and at `v` along every conjugate `τ ∘ s` of `τ` with `s` outside `φ_τ(G_{K_v}) · 1 · U`. Then the
sum of the local invariants of `y` is the invariant of the localization of `a ∪ δχ` along `τ`. -/
private theorem ideleSumLocalInv_eq_subgroupInvMap_of_explicitInfl2_eq
    (L : NormalLayer (AbsoluteGaloisGroup K))
    (χ : Additive L.ground.toSubgroup →+ AddCircle (1 : ℚ))
    (hχ : IsOpen (χ.ker : Set (Additive L.ground.toSubgroup)))
    (a : H0 L.ground.toSubgroup (IdeleCoeff K)) {v : HeightOneSpectrum (𝓞 K)}
    (τ : SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K))
    (hfin : ∀ v' ≠ v, ∀ τ₁ : SeparableClosure K →ₐ[K] SeparableClosure (v'.adicCompletion K),
      ideleCoeffComponent τ₁ (a : IdeleCoeff K) = 0)
    (hinf : ∀ (u : InfinitePlace K) (τ₁ : SeparableClosure K →ₐ[K] SeparableClosure u.Completion),
      ideleCoeffInfiniteComponent τ₁ (a : IdeleCoeff K) = 0)
    (hv : ∀ s : AbsoluteGaloisGroup K,
      DoubleCoset.mk (absoluteGaloisGroupMap τ : AbsoluteGaloisGroup (v.adicCompletion K) →*
        AbsoluteGaloisGroup K).range L.ground.toSubgroup s ≠ DoubleCoset.mk _ _ 1 →
      ideleCoeffComponent (τ.comp (s : SeparableClosure K →ₐ[K] SeparableClosure K))
        (a : IdeleCoeff K) = 0)
    (y : L.H (ideleFormation K) 2)
    (hy : L.explicitInfl2 (ideleCoeffEquivIdeleFormation K)
      (ideleCoeffEquivIdeleFormation_smul K) y =
        (characterCarryCocycle χ hχ a : H2 L.ground.toSubgroup (IdeleCoeff K))) :
    ideleSumLocalInv K L y =
      subgroupInvMap (v.adicCompletion K)
        (L.ground.toSubgroup.comap (absoluteGaloisGroupMap τ :
          AbsoluteGaloisGroup (v.adicCompletion K) →* AbsoluteGaloisGroup K))
        (L.ground.isOpen.preimage (absoluteGaloisGroupMap τ).continuous)
        (explicitMap2 L.ground.toSubgroup (IdeleCoeff K) _ (UnitsCoeff (v.adicCompletion K))
          ((absoluteGaloisGroupMap τ).subgroupComap L.ground.toSubgroup) (ideleCoeffComponent τ)
          continuous_of_discreteTopology (fun y m ↦
            ContinuousMonoidHom.subgroupComap_smul _ _ y m ▸ ideleCoeffComponent_smul _ y.1 m)
          (characterCarryCocycle χ hχ a : H2 L.ground.toSubgroup (IdeleCoeff K))) := by
  have hfin' (v' : HeightOneSpectrum (𝓞 K)) (hv' : v' ≠ v) : ideleLocalInvAt K L v' y = 0 := by
    rw [ideleLocalInvAt_apply, ideleLayerCorInfl_apply, hy,
      ideleBrLocalization_explicitCor2_characterCarryCocycle_eq_zero _ _ _ _ a (hfin v' hv'),
      map_zero]
  have hinf' (u : InfinitePlace K) : ideleInfiniteInvAt K L u y = 0 := by
    rw [ideleInfiniteInvAt_apply, ideleLayerCorInfl_apply, hy,
      ideleInfiniteBrLocalization_explicitCor2_characterCarryCocycle_eq_zero _ _ _ _ a (hinf u),
      map_zero]
  have hsum : ideleSumLocalInv K L y = ideleLocalInvAt K L v y := by
    rw [ideleSumLocalInv_eq_sum K L y (S := {v}) fun v' hv' ↦ ?_, Finset.sum_singleton,
      Finset.sum_eq_zero fun u _ ↦ hinf' u, add_zero]
    rw [mem_ideleSupport] at hv'
    exact Finset.mem_singleton.2 (by_contra fun h ↦ hv' (hfin' v' h))
  have h2 : ideleLocalInvAt K L v y = invMap (v.adicCompletion K) (ideleBrLocalization v
      (explicitCor2 (AbsoluteGaloisGroup K) (IdeleCoeff K) L.ground.toSubgroup L.ground.isOpen
        (characterCarryCocycle χ hχ a : H2 L.ground.toSubgroup (IdeleCoeff K)))) := by
    rw [ideleLocalInvAt_apply, ideleLayerCorInfl_apply, hy]
  exact hsum.trans (h2.trans
    (invMap_ideleBrLocalization_explicitCor2_characterCarryCocycle _ _ _ _ a τ hv))

/-- **The carry class of an idele of `F` concentrated at one place.** Let `F` be the fixed field of
the ground `U` of a layer, `w` a place of `F` above `v`, and `τ` an embedding extending, on `F`,
an embedding `τ'` of `F_w`. For the idele `a` of `F` concentrated at `w` with component `b`, the
sum of the local invariants of a class of the layer inflating to `a ∪ δχ` is the invariant of the
localization of `a ∪ δχ` along `τ`. -/
private theorem ideleSumLocalInv_eq_subgroupInvMap_of_ofAdicCompletion
    (L : NormalLayer (AbsoluteGaloisGroup K))
    (χ : Additive L.ground.toSubgroup →+ AddCircle (1 : ℚ))
    (hχ : IsOpen (χ.ker : Set (Additive L.ground.toSubgroup)))
    {F : IntermediateField K (SeparableClosure K)} [NumberField F]
    (hF : L.ground.toSubgroup = F.fixingSubgroup) {v : HeightOneSpectrum (𝓞 K)}
    (w : HeightOneSpectrum (𝓞 F)) [w.asIdeal.LiesOver v.asIdeal]
    (τ' : w.adicCompletion F →ₐ[v.adicCompletion K] SeparableClosure (v.adicCompletion K))
    (τ : SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K))
    (hτ : ∀ x : F, τ x = τ' (algebraMap F (w.adicCompletion F) x))
    (b : (w.adicCompletion F)ˣ) (a : H0 L.ground.toSubgroup (IdeleCoeff K))
    (ha : ideleCoeffOfIntermediateField K F (.ofMul (IdeleGroup.ofAdicCompletion (𝓞 F) F w b)) =
      (a : IdeleCoeff K))
    (y : L.H (ideleFormation K) 2)
    (hy : L.explicitInfl2 (ideleCoeffEquivIdeleFormation K)
      (ideleCoeffEquivIdeleFormation_smul K) y =
        (characterCarryCocycle χ hχ a : H2 L.ground.toSubgroup (IdeleCoeff K))) :
    ideleSumLocalInv K L y =
      subgroupInvMap (v.adicCompletion K)
        (L.ground.toSubgroup.comap (absoluteGaloisGroupMap τ :
          AbsoluteGaloisGroup (v.adicCompletion K) →* AbsoluteGaloisGroup K))
        (L.ground.isOpen.preimage (absoluteGaloisGroupMap τ).continuous)
        (explicitMap2 L.ground.toSubgroup (IdeleCoeff K) _ (UnitsCoeff (v.adicCompletion K))
          ((absoluteGaloisGroupMap τ).subgroupComap L.ground.toSubgroup) (ideleCoeffComponent τ)
          continuous_of_discreteTopology (fun y m ↦
            ContinuousMonoidHom.subgroupComap_smul _ _ y m ▸ ideleCoeffComponent_smul _ y.1 m)
          (characterCarryCocycle χ hχ a : H2 L.ground.toSubgroup (IdeleCoeff K))) := by
  refine ideleSumLocalInv_eq_subgroupInvMap_of_explicitInfl2_eq L χ hχ a τ
    (fun v' hv' τ₁ ↦ ?_) (fun u τ₁ ↦ ?_) (fun s hs ↦ ?_) y hy
  · -- Away from `v`: the place `w` lies over `v`.
    rw [← ha]
    refine ideleCoeffComponent_ofAdicCompletion_eq_zero w b _ fun _ _ ↦ hv' ?_
    exact HeightOneSpectrum.ext ((Ideal.LiesOver.over (P := w.asIdeal) (p := v'.asIdeal)).trans
      (Ideal.LiesOver.over (P := w.asIdeal) (p := v.asIdeal)).symm)
  · rw [← ha]
    exact ideleCoeffInfiniteComponent_ofAdicCompletion w b _
  · -- At `v`, away from the double coset of `1`, the embedding `τ ∘ s` reads another place of `F`.
    rw [← ha]
    refine ideleCoeffComponent_ofAdicCompletion_eq_zero w b _ fun τ'₁ hτ'₁ ↦ hs ?_
    rw [hF]
    exact doubleCoset_mk_eq_mk_one w τ' τ'₁ τ hτ s hτ'₁

/-- **A layer class with the invariant of a local carry class.** With `F`, `w`, `τ'` and `τ` as
above, let `χ'` be a character of the abelianized Galois group of the layer, read on `U` as `χ`,
and `c` an invariant of `H = φ_τ⁻¹(U)` which is the image under `τ'` of a unit `b` of `F_w`. Then
the class `a ∪ δχ'` of the layer, for the idele `a` of `F` concentrated at `w` with component `b`,
has sum of local invariants `inv_H (c ∪ δχ)`. -/
private theorem exists_ideleSumLocalInv_eq_subgroupInvMap
    (L : NormalLayer (AbsoluteGaloisGroup K))
    (χ' : Additive (Abelianization L.Gal) →+ AddCircle (1 : ℚ))
    (χ : Additive L.ground.toSubgroup →+ AddCircle (1 : ℚ))
    (hχ : IsOpen (χ.ker : Set (Additive L.ground.toSubgroup)))
    (hχχ' : ∀ u : L.ground.toSubgroup,
      χ (.ofMul u) = χ' (.ofMul (Abelianization.of (u : L.Gal))))
    {F : IntermediateField K (SeparableClosure K)} [NumberField F]
    (hF : L.ground.toSubgroup = F.fixingSubgroup) {v : HeightOneSpectrum (𝓞 K)}
    (w : HeightOneSpectrum (𝓞 F)) [w.asIdeal.LiesOver v.asIdeal]
    (τ' : w.adicCompletion F →ₐ[v.adicCompletion K] SeparableClosure (v.adicCompletion K))
    (τ : SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K))
    (hτ : ∀ x : F, τ x = τ' (algebraMap F (w.adicCompletion F) x))
    (c : H0 (L.ground.toSubgroup.comap (absoluteGaloisGroupMap τ :
      AbsoluteGaloisGroup (v.adicCompletion K) →* AbsoluteGaloisGroup K))
        (UnitsCoeff (v.adicCompletion K)))
    (b : (w.adicCompletion F)ˣ)
    (hcb : (c : UnitsCoeff (v.adicCompletion K)) =
      .ofMul (Units.map (τ' : w.adicCompletion F →* SeparableClosure (v.adicCompletion K)) b)) :
    ∃ y : L.H (ideleFormation K) 2,
      ideleSumLocalInv K L y =
        subgroupInvMap (v.adicCompletion K)
          (L.ground.toSubgroup.comap (absoluteGaloisGroupMap τ :
            AbsoluteGaloisGroup (v.adicCompletion K) →* AbsoluteGaloisGroup K))
          (L.ground.isOpen.preimage (absoluteGaloisGroupMap τ).continuous)
          (characterCarryCocycle (χ.comp ((absoluteGaloisGroupMap τ).subgroupComap
            L.ground.toSubgroup : L.ground.toSubgroup.comap (absoluteGaloisGroupMap τ :
              AbsoluteGaloisGroup (v.adicCompletion K) →* AbsoluteGaloisGroup K) →*
                L.ground.toSubgroup).toAdditive)
            (by
              rw [← AddMonoidHom.comap_ker, AddSubgroup.coe_comap]
              exact hχ.preimage (continuous_ofMul.comp
                (((absoluteGaloisGroupMap τ).subgroupComap L.ground.toSubgroup).continuous.comp
                  continuous_toMul))) c :
            H2 _ (UnitsCoeff (v.adicCompletion K))) := by
  -- The idele `a` of `F` concentrated at `w` with component `b` is fixed by `U = G_F`.
  have ha₀ (u : AbsoluteGaloisGroup K) (hu : u ∈ L.ground) :
      u • ideleCoeffOfIntermediateField K F (.ofMul (IdeleGroup.ofAdicCompletion (𝓞 F) F w b)) =
        ideleCoeffOfIntermediateField K F (.ofMul (IdeleGroup.ofAdicCompletion (𝓞 F) F w b)) :=
    smul_ideleCoeffOfIntermediateField_of_mem_fixingSubgroup (by rw [← hF]; exact hu) _
  let a : H0 L.ground.toSubgroup (IdeleCoeff K) :=
    ⟨_, (FixedPoints.mem_addSubgroup _ _ _).2 fun u ↦ ha₀ u u.2⟩
  -- The class `a ∪ δχ'` of the layer, inflated to `U`, is the carry class of `χ` and `a`.
  have hy := L.explicitInfl2_artinCharacterCup (ideleCoeffEquivIdeleFormation K)
    (ideleCoeffEquivIdeleFormation_smul K) ⟨ideleCoeffEquivIdeleFormation K a,
      (Formation.mem_level _).2 fun u hu ↦ by
        rw [← ideleCoeffEquivIdeleFormation_smul]; exact congrArg _ (ha₀ u hu)⟩ χ' χ hχ hχχ' a rfl
  -- Along `τ`, the coordinate of `a` is `c`.
  have hc : explicitMap0 L.ground.toSubgroup (IdeleCoeff K)
      ((absoluteGaloisGroupMap τ).subgroupComap L.ground.toSubgroup :
        L.ground.toSubgroup.comap (absoluteGaloisGroupMap τ :
          AbsoluteGaloisGroup (v.adicCompletion K) →* AbsoluteGaloisGroup K) →*
            L.ground.toSubgroup) (ideleCoeffComponent τ)
      (fun y m ↦ ContinuousMonoidHom.subgroupComap_smul _ _ y m ▸ ideleCoeffComponent_smul _ y.1 m)
      a = c := by
    refine Subtype.ext ?_
    rw [coe_explicitMap0, hcb]
    exact ideleCoeffComponent_ofAdicCompletion_self w b τ' τ hτ
  exact ⟨_, (ideleSumLocalInv_eq_subgroupInvMap_of_ofAdicCompletion L χ hχ hF w τ' τ hτ b a
    rfl _ hy).trans ((congrArg _ (explicitMap2_characterCarryCocycle _ _ _ _ _ _ _)).trans
      (congrArg _ (congrArg _ (congrArg _ hc))))⟩

/-- The value of a character of `U` at an element of a decomposition subgroup `φ_τ⁻¹(U)` is the
sum of the local invariants of a class of the layer, for `F`, `w`, `τ'` and `τ` as above. -/
private theorem exists_ideleSumLocalInv_eq_apply_of_fixingSubgroup
    (L : NormalLayer (AbsoluteGaloisGroup K))
    (χ' : Additive (Abelianization L.Gal) →+ AddCircle (1 : ℚ))
    (χ : Additive L.ground.toSubgroup →+ AddCircle (1 : ℚ))
    (hχ : IsOpen (χ.ker : Set (Additive L.ground.toSubgroup)))
    (hχχ' : ∀ u : L.ground.toSubgroup,
      χ (.ofMul u) = χ' (.ofMul (Abelianization.of (u : L.Gal))))
    {F : IntermediateField K (SeparableClosure K)} [NumberField F]
    (hF : L.ground.toSubgroup = F.fixingSubgroup) {v : HeightOneSpectrum (𝓞 K)}
    (w : HeightOneSpectrum (𝓞 F)) [w.asIdeal.LiesOver v.asIdeal]
    (τ' : w.adicCompletion F →ₐ[v.adicCompletion K] SeparableClosure (v.adicCompletion K))
    (τ : SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K))
    (hτ : ∀ x : F, τ x = τ' (algebraMap F (w.adicCompletion F) x))
    (g : AbsoluteGaloisGroup (v.adicCompletion K)) (hg : absoluteGaloisGroupMap τ g ∈ L.ground) :
    ∃ y : L.H (ideleFormation K) 2,
      ideleSumLocalInv K L y = χ (.ofMul ⟨absoluteGaloisGroupMap τ g, hg⟩) := by
  have hH : IsOpen (L.ground.toSubgroup.comap (absoluteGaloisGroupMap τ :
      AbsoluteGaloisGroup (v.adicCompletion K) →* AbsoluteGaloisGroup K) :
        Set (AbsoluteGaloisGroup (v.adicCompletion K))) :=
    L.ground.isOpen.preimage (absoluteGaloisGroupMap τ).continuous
  have hψ : IsOpen ((χ.comp ((absoluteGaloisGroupMap τ).subgroupComap L.ground.toSubgroup :
      L.ground.toSubgroup.comap (absoluteGaloisGroupMap τ :
        AbsoluteGaloisGroup (v.adicCompletion K) →* AbsoluteGaloisGroup K) →*
          L.ground.toSubgroup).toAdditive).ker : Set (Additive (L.ground.toSubgroup.comap
            (absoluteGaloisGroupMap τ :
              AbsoluteGaloisGroup (v.adicCompletion K) →* AbsoluteGaloisGroup K)))) := by
    rw [← AddMonoidHom.comap_ker, AddSubgroup.coe_comap]
    exact hχ.preimage (continuous_ofMul.comp
      (((absoluteGaloisGroupMap τ).subgroupComap L.ground.toSubgroup).continuous.comp
        continuous_toMul))
  -- An invariant `c` of `H = φ_τ⁻¹(U)` with `inv_H (c ∪ δχ) = χ(φ_τ g)`; it is a unit of `F_w`.
  obtain ⟨c, hc⟩ := exists_subgroupInvMap_characterCarryCocycle_eq _ hH _ hψ ⟨g, hg⟩
  obtain ⟨b, hb⟩ := exists_coe_eq_ofMul_units_map w hF τ' τ hτ c
  obtain ⟨y, hy⟩ := exists_ideleSumLocalInv_eq_subgroupInvMap L χ' χ hχ hχχ' hF w τ' τ hτ c b hb
  exact ⟨y, hy.trans (hc.trans (congrArg χ (congrArg Additive.ofMul
    (Subtype.ext (ContinuousMonoidHom.subgroupComap_apply_coe _ _ _)))))⟩

/-- **Every layer carries a class whose invariant is any value of a character on a decomposition
group.** Let `χ'` be a character of the abelianized Galois group `U ⧸ V` of a layer `V ◁ U` of the
idele formation, `v` a finite place of `K`, `τ : Kˢ → K_vˢ` an embedding of separable closures and
`g ∈ G_{K_v}` whose image `φ_τ(g)` in `G_K` lies in `U`. Then some class of the layer has local
invariants summing to `χ'` of the image of `φ_τ(g)` in `U ⧸ V`. -/
theorem exists_ideleSumLocalInv_eq_apply_absoluteGaloisGroupMap
    (L : NormalLayer (AbsoluteGaloisGroup K))
    (χ' : Additive (Abelianization L.Gal) →+ AddCircle (1 : ℚ))
    {v : HeightOneSpectrum (𝓞 K)}
    (τ : SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K))
    (g : AbsoluteGaloisGroup (v.adicCompletion K)) (hg : absoluteGaloisGroupMap τ g ∈ L.ground) :
    ∃ y : L.H (ideleFormation K) 2,
      ideleSumLocalInv K L y = χ' (.ofMul (Abelianization.of
        (QuotientGroup.mk (⟨absoluteGaloisGroupMap τ g, hg⟩ : L.ground) : L.Gal))) := by
  -- The fixed field `F` of the ground `U` of the layer, a number field with `G_F = U`.
  obtain ⟨F, _, hF⟩ : ∃ F : IntermediateField K (SeparableClosure K),
      NumberField F ∧ L.ground.toSubgroup = F.fixingSubgroup :=
    ⟨_, have := finiteDimensional_fixedField_toSubgroup L.ground
      NumberField.of_module_finite K _, toSubgroup_eq_fixingSubgroup_of_fixedField_eq rfl⟩
  -- On `F`, the embedding `τ` extends an embedding `τ'` of a completion `F_w` above `v`. The type
  -- ascription reads `τ'` with the ring structure of `K_vˢ` used in the statements below.
  obtain ⟨w, _, τ', hτ⟩ : ∃ (w : HeightOneSpectrum (𝓞 F)) (_ : w.asIdeal.LiesOver v.asIdeal)
      (τ' : w.adicCompletion F →ₐ[v.adicCompletion K] SeparableClosure (v.adicCompletion K)),
      ∀ x : F, τ x = τ' (algebraMap F (w.adicCompletion F) x) :=
    exists_algHom_adicCompletion_eq F v (τ.comp (IsScalarTower.toAlgHom K F (SeparableClosure K)))
  -- The character `χ'` read on `U`; it kills the open subgroup `V`.
  obtain ⟨χ, hχ, hχχ'⟩ : ∃ χ : Additive L.ground.toSubgroup →+ AddCircle (1 : ℚ),
      IsOpen (χ.ker : Set (Additive L.ground.toSubgroup)) ∧ ∀ u : L.ground.toSubgroup,
        χ (.ofMul u) = χ' (.ofMul (Abelianization.of (u : L.Gal))) :=
    ⟨(χ'.comp Abelianization.of.toAdditive).comp
      (QuotientGroup.mk' L.relativeTop : L.ground.toSubgroup →* L.Gal).toAdditive,
      AddSubgroup.isOpen_mono
        (H₁ := Subgroup.toAddSubgroup (G := L.ground.toSubgroup) L.relativeTop)
        (fun u hu ↦ by simp [(QuotientGroup.eq_one_iff u.toMul).2 hu])
        ((L.ground.toSubgroup.subgroupOf_isOpen L.top.toSubgroup L.top.isOpen).preimage
          continuous_toMul), fun _ ↦ rfl⟩
  obtain ⟨y, hy⟩ := exists_ideleSumLocalInv_eq_apply_of_fixingSubgroup L χ' χ hχ hχχ' hF w τ' τ hτ
    g hg
  exact ⟨y, hy.trans (hχχ' _)⟩

/-- **A cyclic layer with a place of full local degree carries a class of invariant
`1 / [L : F]`.** If the Galois group `U ⧸ V` of a layer `V ◁ U` of the idele formation is cyclic
and the decomposition subgroup `φ_τ⁻¹(U)` at a finite place `v`, read along an embedding
`τ : Kˢ → K_vˢ`, maps onto `U ⧸ V`, then some class of the layer has local invariants summing to
`1 / [U : V]`. -/
theorem exists_ideleSumLocalInv_eq_one_div_degree_of_isCyclic
    (L : NormalLayer (AbsoluteGaloisGroup K)) [IsCyclic L.Gal] {v : HeightOneSpectrum (𝓞 K)}
    (τ : SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K))
    (hv : Function.Surjective fun g : L.ground.toSubgroup.comap (absoluteGaloisGroupMap τ :
      AbsoluteGaloisGroup (v.adicCompletion K) →* AbsoluteGaloisGroup K) ↦
        ((absoluteGaloisGroupMap τ).subgroupComap L.ground.toSubgroup g : L.Gal)) :
    ∃ y : L.H (ideleFormation K) 2,
      ideleSumLocalInv K L y = ((1 / L.degree : ℚ) : AddCircle (1 : ℚ)) := by
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := L.Gal)
  obtain ⟨⟨g, hg⟩, hgγ⟩ := hv γ
  -- The Galois group is commutative, so `Abelianization.of` is injective and `γ` keeps its order.
  have hof : orderOf (Abelianization.of γ) = L.degree := by
    refine ((orderOf_injective _ ((injective_iff_map_eq_one _).2 fun x hx ↦ ?_) γ).trans
      hγ).trans L.degree_eq_natCard_gal.symm
    rwa [← MonoidHom.mem_ker, Abelianization.ker_of,
      (commutator_eq_bot_iff _).2 inferInstance, Subgroup.mem_bot] at hx
  obtain ⟨χ', hχ'⟩ := CharacterModule.exists_apply_eq_inv_addOrderOf
    (Additive.ofMul (Abelianization.of γ))
    (by rw [addOrderOf_ofMul_eq_orderOf, hof]; exact L.degree_pos.ne')
  obtain ⟨y, hy⟩ := exists_ideleSumLocalInv_eq_apply_absoluteGaloisGroupMap L χ' τ g hg
  refine ⟨y, hy.trans ?_⟩
  have hγ' : (QuotientGroup.mk (⟨absoluteGaloisGroupMap τ g, hg⟩ : L.ground) : L.Gal) = γ :=
    (congrArg QuotientGroup.mk
      (Subtype.ext (ContinuousMonoidHom.subgroupComap_apply_coe (absoluteGaloisGroupMap τ)
        L.ground.toSubgroup ⟨g, hg⟩).symm)).trans hgγ
  rw [hγ']
  -- `CharacterModule` is a semireducible definition for `A →+ AddCircle (1 : ℚ)`, so `hχ'` does
  -- not rewrite the goal, which is stated for the bundled homomorphism; it applies by `exact`.
  exact hχ'.trans (by rw [addOrderOf_ofMul_eq_orderOf, hof])

/-- **A prime-degree layer carries a class of invariant `1 / [U : V]`.** A layer `V ◁ U` of prime
degree has a finite place whose decomposition map onto `U ⧸ V` is surjective, and its Galois group
is cyclic, so the prescribed-invariant construction applies at that place. -/
theorem exists_ideleSumLocalInv_eq_one_div_degree_of_prime
    (L : NormalLayer (AbsoluteGaloisGroup K)) (hL : L.degree.Prime) :
    ∃ y : L.H (ideleFormation K) 2,
      ideleSumLocalInv K L y = ((1 / L.degree : ℚ) : AddCircle (1 : ℚ)) := by
  have := NormalLayer.isCyclic_gal_of_prime_degree hL
  obtain ⟨v, τ, hτ⟩ := L.exists_surjective_absoluteGaloisGroupMap_of_degree_prime hL
  exact exists_ideleSumLocalInv_eq_one_div_degree_of_isCyclic L τ hτ

/-! ### Classes with prescribed localizations

Every family of local Brauer classes is the family of localizations of a class of
`H²(G_K, I_{Kˢ})`. By additivity it suffices to treat a family supported at one place. At a finite
place this is the class of invariant `1 / n` built above, and its integer multiples. At a real
place `w`, take the carry class of the idele concentrated at `w` with component `-1` and of a
character `ψ` of the action of `G_K` on a primitive fourth root of unity `ζ` with `ψ (-1) = 1 / 2`.
The Artin symbol of `-1 ∈ K_w = ℝ` is complex conjugation, which inverts `ζ`, so this class has
invariant `ψ (-1) = 1 / 2` at `w` and vanishes at every other place. -/

/-- **A class of `H²(G_K, I_{Kˢ})` with any prescribed localization at one finite place** and
trivial localizations at the other places. -/
private theorem exists_ideleLocalization_eq_sumLocalInvSection
    [DecidableEq (HeightOneSpectrum (𝓞 K))] (v : HeightOneSpectrum (𝓞 K))
    (r : AddCircle (1 : ℚ)) :
    ∃ x : H2 (AbsoluteGaloisGroup K) (IdeleCoeff K),
      ideleLocalization K x = sumLocalInvSection K v r := by
  -- `r` is an integer multiple of `1 / n` for some `n ≥ 1`.
  obtain ⟨n, hn, hr⟩ := AddCircle.exists_mem_torsionBy_rat r
  obtain ⟨k, rfl⟩ := AddCircle.exists_zsmul_eq_of_mem_torsionBy (1 : ℚ)
    (by exact_mod_cast hn.ne' : (n : ℚ) ≠ 0) hr
  obtain ⟨x, hx⟩ := exists_ideleLocalization_eq_sumLocalInvSection_one_div_aux (E := ⊥) rfl v
    hn.ne'
  exact ⟨k • x, by rw [map_zsmul, hx, map_zsmul]⟩

omit [NumberField K] in
/-- **At a real place, the Artin symbol of `-1` inverts the fourth roots of unity**: if `σ`
represents the archimedean Artin symbol of `-1 ∈ K_wˣ`, its image in `G_K` along `τ : Kˢ → K_wˢ`
acts on a primitive fourth root of unity of `Kˢ` by the exponent `-1`. -/
private theorem autToPow_absoluteGaloisGroupMap_of_isReal {w : InfinitePlace K} (hw : w.IsReal)
    {ζ : SeparableClosure K} (hζ : IsPrimitiveRoot ζ 4)
    (τ : SeparableClosure K →ₐ[K] SeparableClosure w.Completion)
    (σ : Field.absoluteGaloisGroup w.Completion)
    (hσ : (σ : Field.absoluteGaloisGroupAbelianization w.Completion) = infiniteArtinAt w (-1)) :
    hζ.autToPow K (absoluteGaloisGroupMap τ (absoluteGaloisGroupRestrictEquiv w.Completion σ)) =
      -1 := by
  have hz : algebraMap (SeparableClosure w.Completion) (AlgebraicClosure w.Completion) (τ ζ) ^ 4 =
      1 := by
    rw [← map_pow, ← map_pow, hζ.pow_eq_one, map_one, map_one]
  have h := infiniteArtinAt_rootsOfUnity_of_isReal w hw 4 (-1) σ hσ hz
  rw [realCyclotomicSymbol_of_neg _ _ (by simp)] at h
  -- Read in `K_wˢ`, the image of `σ` in `G_K` raises `ζ` to the power `3 = -1 mod 4`. The
  -- hypothesis of `AlgHom.injective` is stated for the underlying ring homomorphism; `show` reads
  -- it through the coercion of `τ`, on which `absoluteGaloisGroupMap_commutes` is stated.
  have hg : absoluteGaloisGroupMap τ (absoluteGaloisGroupRestrictEquiv w.Completion σ) ζ = ζ ^ 3 :=
    τ.injective <| show τ _ = τ _ by
      rw [absoluteGaloisGroupMap_commutes, map_pow]
      refine (algebraMap (SeparableClosure w.Completion)
        (AlgebraicClosure w.Completion)).injective ?_
      rw [map_pow]
      exact (coe_absoluteGaloisGroupRestrictEquiv_apply w.Completion σ _).trans
        (h.trans (congrArg _ (by decide : ((-1 : (ZMod 4)ˣ) : ZMod 4).val = 3)))
  refine Units.ext ((hζ.coe_autToPow_eq_natCast hg).trans ?_)
  decide

/-- **A class of `H²(G_K, I_{Kˢ})` localizing to the nonzero class at a real place `w` and to `0`
at every other place**: the carry class of a character detecting complex conjugation on the
fourth roots of unity and of the idele concentrated at `w` with component `-1`, read in the ideles
of a finite Galois subextension `E` equal to `K`. -/
private theorem exists_ideleLocalization_eq_pi_single_aux {E : Ω}
    (hE : E.toIntermediateField = ⊥) {w : InfinitePlace K} (hw : w.IsReal) :
    ∃ x : H2 (AbsoluteGaloisGroup K) (IdeleCoeff K),
      (ideleLocalization K x).1 = 0 ∧ (∀ u ≠ w, (ideleLocalization K x).2 u = 0) ∧
        infiniteInvMap w ((ideleLocalization K x).2 w) = ((1 / 2 : ℚ) : AddCircle (1 : ℚ)) := by
  -- A place `u` of `E = K` above `w`, and the idele of `E` concentrated at `u` with component
  -- `-1`.
  obtain ⟨u, hu⟩ := InfinitePlace.comap_surjective (K := E) w
  have : u.LiesOver w := hu ▸ inferInstance
  let a := baseIdele hE (IdeleGroup.ofCompletion (𝓞 E) E u (-1))
  -- The character `ψ` of the action of `G_K` on a primitive fourth root of unity `ζ`, with
  -- `ψ (-1) = 1 / 2`.
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot (SeparableClosure K) 4
  have hneg : addOrderOf (Additive.ofMul (-1 : (ZMod 4)ˣ)) = 2 := by
    rw [addOrderOf_ofMul_eq_orderOf]
    exact orderOf_eq_prime (by simp) (by decide)
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Additive (ZMod 4)ˣ →+ AddCircle (1 : ℚ),
      ψ (Additive.ofMul (-1)) =
        ((1 / addOrderOf (Additive.ofMul (-1 : (ZMod 4)ˣ)) : ℚ) : AddCircle (1 : ℚ)) :=
    CharacterModule.exists_apply_eq_inv_addOrderOf _ (hneg.trans_ne (by decide))
  set χ := ψ.comp (hζ.autToPow K).toAdditive with hχ_def
  have hχ := isOpen_ker_comp_autToPow hζ ψ
  refine ⟨characterCarryCocycle χ hχ a, DFinsupp.ext fun v ↦ ?_, fun u' hu' ↦ ?_, ?_⟩
  · -- At a finite place the component of `a` is `1`.
    obtain ⟨v', hv'⟩ := HeightOneSpectrum.under_surjective (𝓞 K) (𝓞 E) v
    have : v'.asIdeal.LiesOver v.asIdeal := hv' ▸ inferInstance
    obtain ⟨τ', τ, h⟩ := exists_ideleCoeffComponent_ideleCoeffOfIntermediateField_eq (v := v) v'
    have h := h (IdeleGroup.ofCompletion (𝓞 E) E u (-1))
    simp only [ideleCoeffOfIntermediateField_coe, HeightOneSpectrum.ideleFiniteCoord_ofCompletion,
      map_one] at h
    rw [ideleLocalization_fst_apply, DFinsupp.zero_apply]
    exact ideleBrLocalization_characterCarryCocycle_eq_zero_of_component_eq_zero τ χ hχ a
      (Additive.toMul.injective h)
  · -- At another infinite place `u'`, read through a place `u''` of `E` above it, the component
    -- of `a` is `1`.
    obtain ⟨u'', hu''⟩ := InfinitePlace.comap_surjective (K := E) u'
    have : u''.LiesOver u' := hu'' ▸ inferInstance
    obtain ⟨τ', τ, h⟩ :=
      exists_ideleCoeffInfiniteComponent_ideleCoeffOfIntermediateField_eq (w := u') u''
    have hne : u'' ≠ u := by
      rintro rfl
      exact hu' (hu''.symm.trans hu)
    have h := h (IdeleGroup.ofCompletion (𝓞 E) E u (-1))
    simp only [ideleCoeffOfIntermediateField_coe,
      InfinitePlace.ideleInfiniteCoord_ofCompletion_of_ne _ hne, map_one] at h
    rw [ideleLocalization_snd_apply]
    exact ideleInfiniteBrLocalization_characterCarryCocycle_eq_zero_of_component_eq_zero τ χ hχ a
      (Additive.toMul.injective h)
  · -- At `w` the component of `a` is `-1`, whose Artin symbol inverts `ζ`.
    obtain ⟨τ', τ, h⟩ :=
      exists_ideleCoeffInfiniteComponent_ideleCoeffOfIntermediateField_eq (w := w) u
    have h := h (IdeleGroup.ofCompletion (𝓞 E) E u (-1))
    simp only [ideleCoeffOfIntermediateField_coe,
      InfinitePlace.ideleInfiniteCoord_ofCompletion_self, Units.map_neg_one] at h
    obtain ⟨σ, hσ⟩ := QuotientGroup.mk_surjective (infiniteArtinAt w (-1))
    rw [ideleLocalization_snd_apply,
      infiniteInvMap_ideleInfiniteBrLocalization_characterCarryCocycle_of_mk_eq_infiniteArtinAt τ χ
        hχ a (-1) (Additive.toMul.injective (h.trans (by simp))) σ hσ, hχ_def,
      AddMonoidHom.comp_apply, MonoidHom.toAdditive_apply_apply, toMul_ofMul,
      autToPow_absoluteGaloisGroupMap_of_isReal hw hζ τ σ hσ, hψ, hneg]
    norm_num

/-- **A class of `H²(G_K, I_{Kˢ})` with any prescribed localization at one infinite place** and
trivial localizations at the other places. -/
private theorem exists_ideleLocalization_eq_pi_single [DecidableEq (InfinitePlace K)]
    (w : InfinitePlace K) (b : Br w.Completion) :
    ∃ x : H2 (AbsoluteGaloisGroup K) (IdeleCoeff K),
      ideleLocalization K x = (0, Pi.single w b) := by
  -- The zero class needs no construction; at a complex place every class is zero.
  obtain rfl | hb := eq_or_ne b 0
  · exact ⟨0, by rw [map_zero, Pi.single_zero, Prod.mk_zero_zero]⟩
  have hw : w.IsReal := InfinitePlace.not_isComplex_iff_isReal.1 fun hw ↦
    hb (brCompletion_eq_zero_of_isComplex w hw b)
  obtain ⟨x, hfin, hinf, hw'⟩ := exists_ideleLocalization_eq_pi_single_aux (E := ⊥) rfl hw
  -- At the real place `w` the two nonzero classes have the same invariant `1 / 2`.
  have hb' : (ideleLocalization K x).2 w = b := by
    refine infiniteInvMap_injective w ?_
    rw [hw', infiniteInvMap_apply_of_isReal w hw]
    simp [hb]
  refine ⟨x, Prod.ext hfin (funext fun u ↦ ?_)⟩
  dsimp only
  obtain rfl | hu := eq_or_ne u w
  · rw [Pi.single_eq_same, hb']
  · rw [Pi.single_eq_of_ne hu, hinf u hu]

variable (K) in
/-- **Every family of local Brauer classes is the localization of an idele class**: the
localization map `H²(G_K, I_{Kˢ}) → ⨁_v Br K_v` is surjective. -/
theorem ideleLocalization_surjective : Function.Surjective (ideleLocalization K) := by
  classical
  rintro ⟨y₁, y₂⟩
  -- The family at the finite places, by induction on its finite support.
  have h₁ : ((y₁, 0) : _ × ((w : InfinitePlace K) → Br w.Completion)) ∈
      (ideleLocalization K).range := by
    induction y₁ using DFinsupp.induction with
    | h0 => exact ⟨0, by rw [map_zero, Prod.mk_zero_zero]⟩
    | ha v b f _ _ ih =>
      obtain ⟨x, hx⟩ := exists_ideleLocalization_eq_sumLocalInvSection v
        (invMap (v.adicCompletion K) b)
      rw [sumLocalInvSection_apply, AddEquiv.symm_apply_apply] at hx
      rw [← add_zero (0 : (w : InfinitePlace K) → Br w.Completion), ← Prod.mk_add_mk]
      exact add_mem ⟨x, hx⟩ ih
  -- The family at the finitely many infinite places, one place at a time.
  have h₂ : ((0, y₂) : (Π₀ v : HeightOneSpectrum (𝓞 K), Br (v.adicCompletion K)) × _) ∈
      (ideleLocalization K).range := by
    rw [← Finset.univ_sum_single y₂, show ((0, ∑ w, Pi.single w (y₂ w)) :
      (Π₀ v : HeightOneSpectrum (𝓞 K), Br (v.adicCompletion K)) × _) =
        ∑ w, (0, Pi.single w (y₂ w)) from
          Prod.ext (by simp [Prod.fst_sum]) (by simp [Prod.snd_sum])]
    exact sum_mem fun w _ ↦ exists_ideleLocalization_eq_pi_single w (y₂ w)
  obtain ⟨x, hx⟩ := add_mem h₁ h₂
  exact ⟨x, by rw [hx, Prod.mk_add_mk, add_zero, zero_add]⟩

end TauCeti.ClassFieldTheory
