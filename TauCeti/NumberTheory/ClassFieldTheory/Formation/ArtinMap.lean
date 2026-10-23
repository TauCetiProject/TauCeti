/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Tate.ArtinLowDegree
public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Tate.Conjugation
public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Tate.Naturality
public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Character

import TauCeti.Algebra.Module.CharacterModule
import TauCeti.NumberTheory.ClassFieldTheory.Formation.Tate.Inflation
import TauCeti.RepresentationTheory.Homological.TateCohomology.Cup.Associativity
import TauCeti.RepresentationTheory.Homological.TateCohomology.Cup.Character
import TauCeti.RepresentationTheory.Homological.TateCohomology.Cup.GradedComm

/-!
# The abstract Artin map of a class formation

Let `V ◁ U` be a finite normal layer of a class formation with coefficient module `A`, and let
`Γ = U ⧸ V`. In degree `r = -2`, Tate's theorem for the class formation
(`ClassFormation.tateIso`) is cup product with the fundamental class,
`H^{-2}(Γ, ℤ) ≃ H^0(Γ, A^V)`. Reading both sides through the low-degree identifications
`H^{-2}(Γ, ℤ) ≃ Γ^ab` (`NormalLayer.tateHMinusTwoEquivAbelianization`) and
`H^0(Γ, A^V) ≃ A^U / N_{U/V}(A^V)` (`NormalLayer.tateHZeroEquivNormQuotient`) gives the
**Nakayama map** `Γ^ab ≃ A^U / N_{U/V}(A^V)`. The **Artin reciprocity isomorphism** is its inverse,
and the **Artin map** of the layer is the composite `A^U → A^U / N_{U/V}(A^V) ≃ Γ^ab`.

All three are ordinary definitions with bodies: Artin reciprocity `artinEquiv` is by definition
the inverse of cup product with the fundamental class read through the two low-degree
identifications, not an arbitrary isomorphism between two groups of the same order, and the Artin
map `artinMap` is its composite with `NormalLayer.normQuotientMk`; this fixes the direction once
for every downstream use. The characterizing property
(`ClassFormation.cupFundamentalClass_artinMap`, `ClassFormation.artinMap_eq_iff`) is that the
Artin symbol `σ = artinMap a` of `a ∈ A^U` is the unique `σ ∈ Γ^ab` whose degree `-2` class cups
with the fundamental class to the zero-dimensional Tate class of `a`.

The consequences recorded here are the ones that need nothing beyond the isomorphism: the kernel
of the Artin map is exactly the norm subgroup (`ClassFormation.ker_artinMap`), the Artin map is
surjective (`ClassFormation.surjective_artinMap`), the norm quotient has as many elements as `Γ^ab`
(`ClassFormation.natCard_normQuotient_eq_natCard_abelianization`), and the Artin symbol of `a`
generates `Γ^ab` exactly when the class of `a` generates the norm quotient
(`ClassFormation.isGenerator_artinMap_iff`).

Conjugation by an element `g` of the ambient group carries the layer to `gVg⁻¹ ◁ gUg⁻¹`. Since
Tate's isomorphism commutes with conjugation (`ClassFormation.tateIso_conj`), so do the Nakayama
map and Artin reciprocity, and the Artin map is equivariant: the Artin symbol of `g · a` for the
conjugate layer is the conjugate of the Artin symbol of `a` (`ClassFormation.artinMap_conj`).

Raising the ground field from `F` to an intermediate field `E` of a layer `K/F` includes the ground
level `A^U` into `A^{U'}` and restricts Tate cohomology. Since Tate's isomorphism commutes with
restriction (`ClassFormation.tateIso_res`), restriction in degree `-2` is the transfer
`Gal(K/F)^ab → Gal(K/E)^ab` and restriction in degree `0` is the ground-level inclusion, the Artin
symbol of `a ∈ A^U` over `E` is the transfer of its Artin symbol over `F`
(`ClassFormation.artinMap_groundInclusion`). Dually, since Tate's isomorphism commutes with
corestriction (`ClassFormation.tateIso_cor`), corestriction in degree `-2` is induced by the
inclusion `Gal(K/E) → Gal(K/F)` and corestriction in degree `0` is the ground-level norm
`N_{E/F}`, the Artin symbol over `F` of the norm of `b ∈ A^{U'}` is the image of its Artin symbol
over `E` (`ClassFormation.artinMap_groundNorm`).

For a character `χ : Γ^ab → ℚ/ℤ` with connecting class `δχ ∈ H^2(Γ, ℤ)`, the Artin map satisfies
the character formula `χ(artinMap a) = inv(a₀ ∪ δχ)` (`ClassFormation.character_artinMap`), and
since characters separate the points of `Γ^ab` it is the only homomorphism that does
(`ClassFormation.eq_artinMap_of_character`). The formula fixes the sign of the degree `-2`
identification: with the opposite sign the same construction would give the inverse of the
classical reciprocity map.

Refining the top field from `K` to `L` gives a quotient
`Gal(L/F)^ab → Gal(K/F)^ab`. Compatibility of the character cup pairing with inflation, together
with the character formula, shows that the Artin symbol for `K/F` is the image of the
Artin symbol for `L/F` (`ClassFormation.artinMap_quotient`).

## Main definitions

* `TauCeti.ClassFieldTheory.ClassFormation.nakayamaNegTwo`: the Nakayama map
  `Γ^ab ≃ A^U / N_{U/V}(A^V)`.
* `TauCeti.ClassFieldTheory.ClassFormation.artinEquiv`: Artin reciprocity
  `A^U / N_{U/V}(A^V) ≃ Γ^ab`, the inverse of the Nakayama map.
* `TauCeti.ClassFieldTheory.ClassFormation.artinMap`: the Artin map `A^U → Γ^ab` of a layer.

## Main statements

* `TauCeti.ClassFieldTheory.ClassFormation.cupFundamentalClass_artinMap`,
  `TauCeti.ClassFieldTheory.ClassFormation.artinMap_eq_iff`: the Artin symbol of `a` is the unique
  element of `Γ^ab` which cups with the fundamental class to the zero-dimensional class of `a`.
* `TauCeti.ClassFieldTheory.ClassFormation.ker_artinMap`,
  `TauCeti.ClassFieldTheory.ClassFormation.artinMap_eq_zero_iff`: the kernel of the Artin map is
  the norm subgroup.
* `TauCeti.ClassFieldTheory.ClassFormation.surjective_artinMap`: the Artin map is surjective.
* `TauCeti.ClassFieldTheory.ClassFormation.artinMap_conj`: the Artin map commutes with conjugation.
* `TauCeti.ClassFieldTheory.ClassFormation.artinMap_groundInclusion`: inclusion of ground levels
  corresponds to the transfer of abelianized Galois groups.
* `TauCeti.ClassFieldTheory.ClassFormation.artinMap_groundNorm`: the norm between ground levels
  corresponds to the map of abelianized Galois groups induced by inclusion.
* `TauCeti.ClassFieldTheory.ClassFormation.character_artinMap`: the character formula
  `χ (artinMap a) = inv (a₀ ∪ δχ)` for the Artin map.
* `TauCeti.ClassFieldTheory.ClassFormation.eq_artinMap_of_character`: the Artin map is the only
  homomorphism satisfying the character formula.
* `TauCeti.ClassFieldTheory.ClassFormation.artinMap_quotient`: refinement of the top field
  corresponds to the quotient map of abelianized Galois groups.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV, §§4–5.
* J.-P. Serre, *Local Fields*, Chapter XI, §3.
* J. Neukirch, *Class Field Theory*, Chapter III, §5.
-/

public noncomputable section

open CategoryTheory MonoidalCategory Rep

namespace TauCeti.ClassFieldTheory.ClassFormation

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {F : Formation G} (cf : ClassFormation F) (L : NormalLayer G)

/-- The **Nakayama map** `Γ^ab ≃ A^U / N_{U/V}(A^V)` of a finite normal layer of a class
formation: Tate's theorem in degree `-2`, cup product with the fundamental class, read through the
layer's sign-normalized identification of `H^{-2}(Γ, ℤ)` with `Γ^ab` (the negative of the generic
one, so that the Artin map satisfies the character formula) and the canonical identification of
`H^0(Γ, A^V)` with the norm quotient. The codomain `L.TateH F (-2 + 2)` of `cf.tateIso L (-2)`
is `L.TateH F 0` because `-2 + 2` reduces to `0`. -/
def nakayamaNegTwo : Additive (Abelianization L.Gal) ≃+ L.NormQuotient F :=
  L.tateHMinusTwoEquivAbelianization.symm.trans
    ((cf.tateIso L (-2)).trans (L.tateHZeroEquivNormQuotient F))

/-- The Nakayama map sends `σ ∈ Γ^ab` to the class in the norm quotient of the cup product of the
degree `-2` class of `σ` with the fundamental class. -/
theorem nakayamaNegTwo_apply (σ : Additive (Abelianization L.Gal)) :
    cf.nakayamaNegTwo L σ = L.tateHZeroEquivNormQuotient F
      (cf.cupFundamentalClass L (-2) (L.tateHMinusTwoEquivAbelianization.symm σ)) := by
  rw [nakayamaNegTwo, AddEquiv.trans_apply, AddEquiv.trans_apply, tateIso_apply]

/-- **Artin reciprocity** for a finite normal layer of a class formation,
`A^U / N_{U/V}(A^V) ≃ Γ^ab`. It is, by definition, the inverse of the Nakayama map. -/
def artinEquiv : L.NormQuotient F ≃+ Additive (Abelianization L.Gal) :=
  (cf.nakayamaNegTwo L).symm

/-- Artin reciprocity is the inverse of the cup product with the fundamental class in degree
`-2`, read through the two low-degree identifications. -/
theorem artinEquiv_eq_tateIso :
    cf.artinEquiv L =
      (L.tateHMinusTwoEquivAbelianization.symm.trans
        ((cf.tateIso L (-2)).trans (L.tateHZeroEquivNormQuotient F))).symm :=
  (rfl)

/-- The inverse of Artin reciprocity is the Nakayama map. -/
@[simp]
theorem artinEquiv_symm : (cf.artinEquiv L).symm = cf.nakayamaNegTwo L :=
  (rfl)

/-- Artin reciprocity inverts the Nakayama map. -/
@[simp]
theorem artinEquiv_nakayamaNegTwo (σ : Additive (Abelianization L.Gal)) :
    cf.artinEquiv L (cf.nakayamaNegTwo L σ) = σ :=
  (cf.nakayamaNegTwo L).symm_apply_apply σ

/-- The Nakayama map inverts Artin reciprocity. -/
@[simp]
theorem nakayamaNegTwo_artinEquiv (x : L.NormQuotient F) :
    cf.nakayamaNegTwo L (cf.artinEquiv L x) = x :=
  (cf.nakayamaNegTwo L).apply_symm_apply x

/-- The **Artin map** `A^U → Γ^ab` of a finite normal layer of a class formation: the class of an
element of the ground level in the norm quotient, followed by Artin reciprocity. -/
def artinMap : F.level L.ground →+ Additive (Abelianization L.Gal) :=
  (cf.artinEquiv L).toAddMonoidHom.comp (L.normQuotientMk F).toAddMonoidHom

/-- The Artin map is Artin reciprocity applied to the class modulo norms. -/
theorem artinMap_apply (a : F.level L.ground) :
    cf.artinMap L a = cf.artinEquiv L (L.normQuotientMk F a) :=
  (rfl)

/-- The Nakayama map sends the Artin symbol of `a` to the class of `a` modulo norms. -/
@[simp]
theorem nakayamaNegTwo_artinMap (a : F.level L.ground) :
    cf.nakayamaNegTwo L (cf.artinMap L a) = L.normQuotientMk F a := by
  rw [artinMap_apply, nakayamaNegTwo_artinEquiv]

/-- **The defining property of the Artin symbol**: the degree `-2` class of `artinMap a`, cupped
with the fundamental class, is the zero-dimensional Tate class of `a`. -/
theorem cupFundamentalClass_artinMap (a : F.level L.ground) :
    cf.cupFundamentalClass L (-2) (L.tateHMinusTwoEquivAbelianization.symm (cf.artinMap L a)) =
      L.zeroTateClass F a := by
  apply (L.tateHZeroEquivNormQuotient F).injective
  rw [← nakayamaNegTwo_apply, nakayamaNegTwo_artinMap,
    NormalLayer.tateHZeroEquivNormQuotient_zeroTateClass]

/-- **Characterization of the Artin symbol**: `artinMap a = σ` exactly when the degree `-2` class
of `σ`, cupped with the fundamental class, is the zero-dimensional Tate class of `a`. -/
theorem artinMap_eq_iff (a : F.level L.ground) (σ : Additive (Abelianization L.Gal)) :
    cf.artinMap L a = σ ↔
      cf.cupFundamentalClass L (-2) (L.tateHMinusTwoEquivAbelianization.symm σ) =
        L.zeroTateClass F a := by
  rw [← cupFundamentalClass_artinMap, ← tateIso_apply, ← tateIso_apply,
    (cf.tateIso L (-2)).injective.eq_iff, L.tateHMinusTwoEquivAbelianization.symm.injective.eq_iff,
    eq_comm]

/-- The Artin symbol of `a` vanishes exactly when `a` is a norm. -/
@[simp]
theorem artinMap_eq_zero_iff (a : F.level L.ground) :
    cf.artinMap L a = 0 ↔ a ∈ L.normSubgroup F := by
  rw [artinMap_apply, AddEquiv.map_eq_zero_iff, NormalLayer.normQuotientMk_apply,
    Submodule.Quotient.mk_eq_zero]

/-- **The kernel of the Artin map is the norm subgroup** `N_{U/V}(A^V)`. -/
theorem ker_artinMap : (cf.artinMap L).ker = (L.normSubgroup F).toAddSubgroup := by
  ext a
  exact cf.artinMap_eq_zero_iff L a

/-- **The Artin map is surjective** onto the abelianized Galois group of the layer. -/
theorem surjective_artinMap : Function.Surjective (cf.artinMap L) := by
  intro σ
  obtain ⟨x, rfl⟩ := (cf.artinEquiv L).surjective σ
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact ⟨a, by rw [artinMap_apply, NormalLayer.normQuotientMk_apply]⟩

include cf in
/-- **Norm index**: the norm quotient `A^U / N_{U/V}(A^V)` of a finite normal layer of a class
formation has as many elements as the abelianized Galois group of the layer. -/
theorem natCard_normQuotient_eq_natCard_abelianization :
    Nat.card (L.NormQuotient F) = Nat.card (Abelianization L.Gal) :=
  Nat.card_congr (cf.artinEquiv L).toEquiv

/-- The Artin symbol of `a` generates the abelianized Galois group exactly when the class of `a`
generates the norm quotient. -/
theorem isGenerator_artinMap_iff (a : F.level L.ground) :
    AddSubgroup.zmultiples (cf.artinMap L a) = ⊤ ↔
      AddSubgroup.zmultiples (L.normQuotientMk F a) = ⊤ := by
  rw [artinMap_apply, ← AddMonoidHom.coe_ofClass, ← AddMonoidHom.map_zmultiples,
    ← AddSubgroup.map_equiv_top (cf.artinEquiv L),
    (AddSubgroup.map_injective (cf.artinEquiv L).injective).eq_iff]

/-! ### Conjugation -/

/-- **The Nakayama map commutes with conjugation**: conjugating the abelianized Galois group by
`g` and conjugating the norm quotient by `g` are matched by the Nakayama maps of a layer and its
conjugate. -/
@[simp]
theorem nakayamaNegTwo_conj (g : G) (σ : Additive (Abelianization L.Gal)) :
    cf.nakayamaNegTwo (L.conjugate g)
        (Additive.ofMul ((L.conjugateGalEquiv g).abelianizationCongr (Additive.toMul σ))) =
      L.conjugateNormQuotientEquiv F g (cf.nakayamaNegTwo L σ) := by
  obtain ⟨x, rfl⟩ := L.tateHMinusTwoEquivAbelianization.surjective σ
  rw [← MulEquiv.toAdditive_apply_apply]
  rw [nakayamaNegTwo_apply, nakayamaNegTwo_apply, AddEquiv.symm_apply_apply,
    ← L.tateHMinusTwoEquivAbelianization_conjugateTrivialTateIso_apply g x,
    AddEquiv.symm_apply_apply, ← tateIso_apply, ← tateIso_apply, ← cf.tateIso_conj L g (-2) x]
  exact L.tateHZeroEquivNormQuotient_conjugateTateIso_apply F g _

/-- **Artin reciprocity commutes with conjugation**: Artin reciprocity of the conjugate layer,
applied to the conjugate of a class modulo norms, is the conjugate of its Artin symbol. -/
@[simp]
theorem artinEquiv_conj (g : G) (y : L.NormQuotient F) :
    cf.artinEquiv (L.conjugate g) (L.conjugateNormQuotientEquiv F g y) =
      (L.conjugateGalEquiv g).abelianizationCongr.toAdditive (cf.artinEquiv L y) := by
  simp only [MulEquiv.toAdditive_apply_apply]
  rw [← nakayamaNegTwo_artinEquiv cf L y, ← nakayamaNegTwo_conj, artinEquiv_nakayamaNegTwo,
    nakayamaNegTwo_artinEquiv]

/-- **The Artin map commutes with conjugation**, one of the four Artin–Tate functoriality
diagrams: the Artin symbol of `g · a` for the conjugate layer `gVg⁻¹ ◁ gUg⁻¹` is the conjugate by
`g` of the Artin symbol of `a`. -/
@[simp]
theorem artinMap_conj (g : G) (a : F.level L.ground) :
    cf.artinMap (L.conjugate g) (L.conjugateGroundLevelEquiv F g a) =
      (L.conjugateGalEquiv g).abelianizationCongr.toAdditive (cf.artinMap L a) := by
  rw [artinMap_apply, artinMap_apply, ← artinEquiv_conj, NormalLayer.normQuotientMk_apply,
    NormalLayer.normQuotientMk_apply, NormalLayer.conjugateNormQuotientEquiv_mk]

/-! ### Restriction to an intermediate ground field -/

/-- **Inclusion of ground levels corresponds to transfer**, one of the four Artin–Tate
functoriality diagrams: for an intermediate field `F ⊆ E ⊆ K` of a layer `K/F`, the Artin symbol
over `E` of an element `a` of the ground level `A^U` of `K/F` is the transfer
`Gal(K/F)^ab → Gal(K/E)^ab` of its Artin symbol over `F`. -/
@[simp]
theorem artinMap_groundInclusion {small big : NormalLayer G} (T : LayerRestriction small big)
    (a : F.level big.ground) :
    cf.artinMap small (T.groundInclusion F a) = T.transferHom (cf.artinMap big a) := by
  set σ := cf.artinMap big a
  rw [artinMap_eq_iff]
  calc cf.cupFundamentalClass small (-2)
        (small.tateHMinusTwoEquivAbelianization.symm (T.transferHom σ))
      = cf.tateIso small (-2)
          (T.trivialTateRes (-2) (big.tateHMinusTwoEquivAbelianization.symm σ)) := by
        -- in degree `-2`, restriction is the transfer
        rw [tateIso_apply]
        congr 1
        rw [AddEquiv.symm_apply_eq, T.tateHMinusTwoEquivAbelianization_trivialTateRes,
          AddEquiv.apply_symm_apply]
    -- Tate's isomorphism commutes with restriction
    _ = T.tateRes F 0 (cf.tateIso big (-2) (big.tateHMinusTwoEquivAbelianization.symm σ)) :=
        (cf.tateIso_res T (-2) _).symm
    _ = T.tateRes F 0 (big.zeroTateClass F a) := by
        rw [tateIso_apply, cupFundamentalClass_artinMap]
    -- in degree `0`, restriction is the ground-level inclusion
    _ = small.zeroTateClass F (T.groundInclusion F a) := T.tateRes_zeroTateClass F a

/-! ### Corestriction from an intermediate ground field -/

/-- **The norm corresponds to inclusion of Galois groups**, one of the four Artin–Tate
functoriality diagrams: for an intermediate field `F ⊆ E ⊆ K` of a layer `K/F`, the Artin symbol
over `F` of the norm `N_{E/F}(b)` of an element `b` of the ground level `A^{U'}` of `K/E` is the
image of its Artin symbol over `E` under the map `Gal(K/E)^ab → Gal(K/F)^ab` induced by
inclusion. -/
@[simp]
theorem artinMap_groundNorm {small big : NormalLayer G} (T : LayerRestriction small big)
    (b : F.level small.ground) :
    cf.artinMap big (T.groundNorm F b) = T.inclusionHom (cf.artinMap small b) := by
  set σ := cf.artinMap small b
  rw [artinMap_eq_iff]
  calc cf.cupFundamentalClass big (-2)
        (big.tateHMinusTwoEquivAbelianization.symm (T.inclusionHom σ))
      = cf.tateIso big (-2)
          (T.trivialTateCor (-2) (small.tateHMinusTwoEquivAbelianization.symm σ)) := by
        -- in degree `-2`, corestriction is the inclusion
        rw [tateIso_apply]
        congr 1
        rw [AddEquiv.symm_apply_eq, T.tateHMinusTwoEquivAbelianization_trivialTateCor,
          AddEquiv.apply_symm_apply]
    -- Tate's isomorphism commutes with corestriction
    _ = T.tateCor F 0 (cf.tateIso small (-2) (small.tateHMinusTwoEquivAbelianization.symm σ)) :=
        (cf.tateIso_cor T (-2) _).symm
    _ = T.tateCor F 0 (small.zeroTateClass F b) := by
        rw [tateIso_apply, cupFundamentalClass_artinMap]
    -- in degree `0`, corestriction is the ground-level norm
    _ = big.zeroTateClass F (T.groundNorm F b) := T.tateCor_zeroTateClass F b

/-! ### The character formula -/

private theorem inv_cupFundamentalClass_zero (x : L.TrivialTateH 0) :
    cf.inv L ((L.tateHIsoH F 2).hom (cf.cupFundamentalClass L 0 x)) =
      ZMod.toRatAddCircle (Nat.card L.Gal)
        (TateCohomology.H0LinearEquivTrivialIntZModCard L.Gal x) := by
  obtain ⟨k, hk⟩ := ZMod.intCast_surjective
    (TateCohomology.H0LinearEquivTrivialIntZModCard L.Gal x)
  have hx : x = k • TateCohomology.trivialTateHZeroOne L.Gal := by
    apply (TateCohomology.H0LinearEquivTrivialIntZModCard L.Gal).injective
    rw [map_zsmul, TateCohomology.H0LinearEquivTrivialIntZModCard_trivialTateHZeroOne,
      zsmul_one, hk]
  rw [hx, map_zsmul, map_zsmul, cupFundamentalClass_apply,
    cupClass_trivialTateHZeroOne, map_zsmul, Iso.inv_hom_id_apply,
    map_zsmul, inv_fundamentalClass, map_zsmul,
    TateCohomology.H0LinearEquivTrivialIntZModCard_trivialTateHZeroOne]
  congr 1
  rw [← L.degree_eq_natCard_gal]
  simpa only [Nat.cast_one] using (ZMod.toRatAddCircle_natCast L.degree 1).symm

/-- **The character formula for the Artin map**: for every character `χ` of the abelianized Galois
group, `χ (artinMap a) = inv (a₀ ∪ δχ)`, where `a₀` is the zero-dimensional Tate class of `a` and
`δχ` is the connecting class of `χ`. -/
@[simp]
theorem character_artinMap (a : F.level L.ground)
    (chi : Additive (Abelianization L.Gal) →+ AddCircle (1 : ℚ)) :
    cf.inv L (L.artinCharacterCup F a chi) = chi (cf.artinMap L a) := by
  let sigma := L.tateHMinusTwoEquivAbelianization.symm (cf.artinMap L a)
  let pairing :=
    (tateCohomologyFunctor 0).map (λ_ (Rep.trivial ℤ L.Gal ℤ)).hom
      (TateCohomology.cup (Rep.trivial ℤ L.Gal ℤ) (Rep.trivial ℤ L.Gal ℤ)
        (-2) 2 0 (by omega) sigma (L.characterConnectingClass chi))
  have hcup :
      L.artinCharacterCup F a chi =
        (L.tateHIsoH F 2).hom (cf.cupFundamentalClass L 0 pairing) := by
    rw [NormalLayer.artinCharacterCup_apply,
      ← cf.cupFundamentalClass_artinMap L a, cupFundamentalClass_apply, cupClass_apply]
    congr 1
    rw [cupFundamentalClass_apply, cupClass_apply]
    dsimp only [pairing, sigma]
    have hstruct :
        ((λ_ (L.rep F)).hom ▷ Rep.trivial ℤ L.Gal ℤ) ≫ (ρ_ (L.rep F)).hom =
          (α_ (𝟙_ (Rep ℤ L.Gal)) (L.rep F) (Rep.trivial ℤ L.Gal ℤ)).hom ≫
            ((𝟙_ (Rep ℤ L.Gal)) ◁ (β_ (L.rep F) (Rep.trivial ℤ L.Gal ℤ)).hom) ≫
            (α_ (𝟙_ (Rep ℤ L.Gal)) (Rep.trivial ℤ L.Gal ℤ) (L.rep F)).inv ≫
            ((λ_ (Rep.trivial ℤ L.Gal ℤ)).hom ▷ L.rep F) ≫ (λ_ (L.rep F)).hom := by
      -- `Rep.trivial ℤ L.Gal ℤ` is the tensor unit, but the braided coherence tactic needs
      -- that unit displayed as `𝟙_ (Rep ℤ L.Gal)` in order to recognize the unit braiding.
      change ((λ_ (L.rep F)).hom ▷ (𝟙_ (Rep ℤ L.Gal))) ≫ (ρ_ (L.rep F)).hom =
        (α_ (𝟙_ (Rep ℤ L.Gal)) (L.rep F) (𝟙_ (Rep ℤ L.Gal))).hom ≫
          ((𝟙_ (Rep ℤ L.Gal)) ◁ (β_ (L.rep F) (𝟙_ (Rep ℤ L.Gal))).hom) ≫
          (α_ (𝟙_ (Rep ℤ L.Gal)) (𝟙_ (Rep ℤ L.Gal)) (L.rep F)).inv ≫
          ((λ_ (𝟙_ (Rep ℤ L.Gal))).hom ▷ L.rep F) ≫ (λ_ (L.rep F)).hom
      rw [braiding_tensorUnit_right]
      monoidal
    simp only [Int.reduceAdd]
    rw [TateCohomology.cup_map_left, ← ModuleCat.comp_apply, ← Functor.map_comp, hstruct,
      Functor.map_comp, Functor.map_comp, Functor.map_comp, Functor.map_comp,
      ModuleCat.comp_apply, ModuleCat.comp_apply, ModuleCat.comp_apply, ModuleCat.comp_apply]
    -- Reassociate so that graded commutativity can exchange the degree-two factors.
    have hAssoc₁ := TateCohomology.cup_assoc
      (𝟙_ (Rep ℤ L.Gal)) (L.rep F) (Rep.trivial ℤ L.Gal ℤ)
      (p := -2) (q := 2) (s := 2) (r₁ := 0) (r₂ := 4) (r := 2)
      (by omega) (by omega) (by omega) sigma
      ((L.tateHIsoH F 2).inv (cf.fundamentalClass L)) (L.characterConnectingClass chi)
    have hAssoc₁' :
        (tateCohomologyFunctor 2).map
            (α_ (𝟙_ (Rep ℤ L.Gal)) (L.rep F) (Rep.trivial ℤ L.Gal ℤ)).hom
          (TateCohomology.cup ((𝟙_ (Rep ℤ L.Gal)) ⊗ L.rep F)
            (Rep.trivial ℤ L.Gal ℤ) 0 2 2 (by omega)
            (TateCohomology.cup (Rep.trivial ℤ L.Gal ℤ) (L.rep F) (-2) 2 0 (by omega)
              sigma ((L.tateHIsoH F 2).inv (cf.fundamentalClass L)))
            (L.characterConnectingClass chi)) =
          TateCohomology.cup (𝟙_ (Rep ℤ L.Gal))
            ((L.rep F) ⊗ Rep.trivial ℤ L.Gal ℤ) (-2) 4 2 (by omega) sigma
            (TateCohomology.cup (L.rep F) (Rep.trivial ℤ L.Gal ℤ) 2 2 4 (by omega)
              ((L.tateHIsoH F 2).inv (cf.fundamentalClass L))
              (L.characterConnectingClass chi)) := by
      exact hAssoc₁
    rw [hAssoc₁', ← TateCohomology.cup_map_right, TateCohomology.cup_gradedComm]
    rw [Int.negOnePow_even (2 * 2) ⟨2, rfl⟩, one_smul]
    -- Reassociate back; the intervening associator and its inverse then cancel.
    have hAssoc₂ := TateCohomology.cup_assoc
      (𝟙_ (Rep ℤ L.Gal)) (Rep.trivial ℤ L.Gal ℤ) (L.rep F)
      (p := -2) (q := 2) (s := 2) (r₁ := 0) (r₂ := 4) (r := 2)
      (by omega) (by omega) (by omega) sigma (L.characterConnectingClass chi)
      ((L.tateHIsoH F 2).inv (cf.fundamentalClass L))
    have hAssoc₂' :
        (tateCohomologyFunctor 2).map
            (α_ (𝟙_ (Rep ℤ L.Gal)) (Rep.trivial ℤ L.Gal ℤ) (L.rep F)).hom
          (TateCohomology.cup ((𝟙_ (Rep ℤ L.Gal)) ⊗ Rep.trivial ℤ L.Gal ℤ)
            (L.rep F) 0 2 2 (by omega)
            (TateCohomology.cup (Rep.trivial ℤ L.Gal ℤ) (Rep.trivial ℤ L.Gal ℤ)
              (-2) 2 0 (by omega) sigma (L.characterConnectingClass chi))
            ((L.tateHIsoH F 2).inv (cf.fundamentalClass L))) =
          TateCohomology.cup (𝟙_ (Rep ℤ L.Gal))
            (Rep.trivial ℤ L.Gal ℤ ⊗ L.rep F) (-2) 4 2 (by omega) sigma
            (TateCohomology.cup (Rep.trivial ℤ L.Gal ℤ) (L.rep F) 2 2 4 (by omega)
              (L.characterConnectingClass chi)
              ((L.tateHIsoH F 2).inv (cf.fundamentalClass L))) := by
      exact hAssoc₂
    have hcancel (z : tateCohomology
        (((𝟙_ (Rep ℤ L.Gal)) ⊗ Rep.trivial ℤ L.Gal ℤ) ⊗ L.rep F) 2) :
        (tateCohomologyFunctor 2).map
            (α_ (𝟙_ (Rep ℤ L.Gal)) (Rep.trivial ℤ L.Gal ℤ) (L.rep F)).inv
          ((tateCohomologyFunctor 2).map
            (α_ (𝟙_ (Rep ℤ L.Gal)) (Rep.trivial ℤ L.Gal ℤ) (L.rep F)).hom z) = z := by
      rw [← ModuleCat.comp_apply, ← Functor.map_comp, Iso.hom_inv_id,
        (tateCohomologyFunctor 2).map_id]
      rfl
    rw [← hAssoc₂', hcancel, ← TateCohomology.cup_map_left]
  rw [hcup, cf.inv_cupFundamentalClass_zero]
  -- The layer's degree `-2` identification is the negative of the generic one, which turns the
  -- generic pairing `-χ(σ)` into `χ(σ)`.
  have hsigma : sigma = TateCohomology.HNegTwoAddEquivAbelianization.symm
      (-cf.artinMap L a) := by
    apply L.tateHMinusTwoEquivAbelianization.injective
    simp only [sigma, AddEquiv.apply_symm_apply,
      NormalLayer.tateHMinusTwoEquivAbelianization_apply, neg_neg]
  simp only [pairing, NormalLayer.characterConnectingClass_def, hsigma]
  rw [TateCohomology.toRatAddCircle_map_leftUnitor_cup_characterConnectingClass, map_neg,
    neg_neg]

/-- **Uniqueness of the Artin map**: a homomorphism `φ` from the ground level to the abelianized
Galois group which satisfies the character formula `χ (φ a) = inv (a₀ ∪ δχ)` for every `a` and
every character `χ` is the Artin map. -/
theorem eq_artinMap_of_character (φ : F.level L.ground →+ Additive (Abelianization L.Gal))
    (hφ : ∀ (a : F.level L.ground) (chi : Additive (Abelianization L.Gal) →+ AddCircle (1 : ℚ)),
      chi (φ a) = cf.inv L (L.artinCharacterCup F a chi)) :
    φ = cf.artinMap L := by
  refine AddMonoidHom.ext fun a ↦ sub_eq_zero.mp (CharacterModule.eq_zero_of_character_apply ?_)
  intro chi
  rw [map_sub, sub_eq_zero]
  exact (hφ a chi).trans (cf.character_artinMap L a chi)

/-! ### Refinement of the top field -/

/-- **Passage to a quotient extension corresponds to the quotient map on Galois groups**, the
fourth Artin–Tate functoriality diagram. Under a refinement of the top field from `K` to `L`, the
Artin symbol for `K/F` is the image of the Artin symbol for `L/F` under
`Gal(L/F)^ab → Gal(K/F)^ab`. -/
@[simp]
theorem artinMap_quotient {old new : NormalLayer G} (T : LayerRefinement old new)
    (a : F.level old.ground) :
    cf.artinMap old a = T.quotientHom (cf.artinMap new (T.groundEquiv F a)) := by
  apply sub_eq_zero.mp
  apply CharacterModule.eq_zero_of_character_apply
  intro chi
  rw [map_sub, sub_eq_zero]
  calc
    chi (cf.artinMap old a) = cf.inv old (old.artinCharacterCup F a chi) :=
      (cf.character_artinMap old a chi).symm
    _ = cf.inv new
        (new.artinCharacterCup F (T.groundEquiv F a) (chi.comp T.quotientHom)) :=
      (cf.inv_artinCharacterCup_comp_quotientHom T a chi).symm
    _ = (chi.comp T.quotientHom) (cf.artinMap new (T.groundEquiv F a)) :=
      cf.character_artinMap new (T.groundEquiv F a) (chi.comp T.quotientHom)

end TauCeti.ClassFieldTheory.ClassFormation
