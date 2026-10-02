/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Tate.Conjugation

/-!
# The abstract Artin map of a class formation

Let `V ◁ U` be a finite normal layer of a class formation with coefficient module `A`, and let
`Γ = U ⧸ V`. In degree `r = -2`, Tate's theorem for the class formation
(`ClassFormation.tateIso`) is cup product with the fundamental class,
`H^{-2}(Γ, ℤ) ≃ H^0(Γ, A^V)`. Reading both sides through the canonical low-degree identifications
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

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV, §§4–5.
* J.-P. Serre, *Local Fields*, Chapter XI, §3.
* J. Neukirch, *Class Field Theory*, Chapter III, §5.
-/

public noncomputable section

namespace TauCeti.ClassFieldTheory.ClassFormation

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {F : Formation G} (cf : ClassFormation F) (L : NormalLayer G)

/-- The **Nakayama map** `Γ^ab ≃ A^U / N_{U/V}(A^V)` of a finite normal layer of a class
formation: Tate's theorem in degree `-2`, cup product with the fundamental class, read through the
canonical identifications of `H^{-2}(Γ, ℤ)` with `Γ^ab` and of `H^0(Γ, A^V)` with the norm
quotient. The codomain `L.TateH F (-2 + 2)` of `cf.tateIso L (-2)` is `L.TateH F 0` because
`-2 + 2` reduces to `0`. -/
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

end TauCeti.ClassFieldTheory.ClassFormation
