/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Tate.Theorem
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Cup.Functoriality
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Restriction.Abelianization

/-!
# Conjugation and the Tate isomorphism of a class formation

An element `g` of the ambient group carries a finite normal layer `V ◁ U` to its conjugate
`gVg⁻¹ ◁ gUg⁻¹` (`NormalLayer.conjugate`), with an isomorphism of Galois groups
(`NormalLayer.conjugateGalEquiv`) and the action of `g` on the coefficient modules. Conjugation of
Tate cohomology with formation coefficients is `NormalLayer.conjugateTateIso`. This file adds the
same conjugation on Tate cohomology with trivial integral coefficients
(`NormalLayer.conjugateTrivialTateIso`), which in degree `-2` is the induced isomorphism of
abelianized Galois groups, and proves that cup product with a degree-two class is equivariant:
conjugating `x ∪ u` gives the cup product of the conjugates (`cupClass_conj`).

Since conjugation carries the fundamental class of a layer of a class formation to the fundamental
class of the conjugate layer (`ClassFormation.fundamentalClass_conj`), Tate's isomorphism
`H^r(U/V, ℤ) ≃ H^{r+2}(U/V, A^V)` commutes with conjugation in every degree
(`ClassFormation.tateIso_conj`). In degree `-2` this is the conjugation compatibility of the Artin
map.

## Main definitions

* `TauCeti.ClassFieldTheory.NormalLayer.conjugateTrivialTateIso`: conjugation on Tate cohomology of
  a layer with trivial integral coefficients.

## Main statements

* `NormalLayer.tateHMinusTwoEquivAbelianization_conjugateTrivialTateIso_apply`: in degree `-2`,
  conjugation is the induced isomorphism of abelianized Galois groups.
* `TauCeti.ClassFieldTheory.cupClass_conj`: cup product with a degree-two class commutes with
  conjugation.
* `TauCeti.ClassFieldTheory.ClassFormation.tateIso_conj`: Tate's isomorphism of a class formation
  commutes with conjugation.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV, §4.
* J.-P. Serre, *Local Fields*, Chapter XI, §3.
-/

public noncomputable section

open CategoryTheory MonoidalCategory Rep

namespace TauCeti.ClassFieldTheory

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

namespace NormalLayer

variable (L : NormalLayer G) (F : Formation G) (g : G)

/-- **Conjugation on Tate cohomology with trivial integral coefficients**: the isomorphism
`H^r(U/V, ℤ) ≅ H^r(gUg⁻¹/gVg⁻¹, ℤ)` induced by the isomorphism of Galois groups. -/
def conjugateTrivialTateIso (r : ℤ) : L.TrivialTateH r ≅ (L.conjugate g).TrivialTateH r :=
  TateCohomology.mapIso (e := L.conjugateGalEquiv g)
    (Rep.isIntertwiningMap_trivial ℤ (L.conjugateGalEquiv g).toMonoidHom) r

/-- Conjugation with trivial integral coefficients is the Tate map of the compatible pair formed by
the isomorphism of Galois groups and the identity of `ℤ`. -/
theorem conjugateTrivialTateIso_hom (r : ℤ) :
    (L.conjugateTrivialTateIso g r).hom =
      TateCohomology.map (e := L.conjugateGalEquiv g)
        (Rep.isIntertwiningMap_trivial ℤ (L.conjugateGalEquiv g).toMonoidHom) r :=
  TateCohomology.mapIso_hom _ r

private theorem map_eq_conjugateTrivialTateIso_hom {L' : NormalLayer G}
    (hL : L.conjugate g = L') {e : L.Gal ≃* L'.Gal}
    (he : e = (L.conjugateGalEquiv g).trans
      (MulEquiv.cast (M := fun K : NormalLayer G => K.Gal) hL)) (r : ℤ) :
    TateCohomology.map (e := e) (Rep.isIntertwiningMap_trivial ℤ (e : L.Gal →* L'.Gal)) r =
      (L.conjugateTrivialTateIso g r).hom ≫ eqToHom (by rw [hL]) := by
  subst hL
  rw [eqToHom_refl, Category.comp_id, conjugateTrivialTateIso_hom]
  exact TateCohomology.map_congr (he.trans (by ext x; rfl)) rfl r

/-- Conjugation by `1` is the identity on Tate cohomology with trivial integral coefficients,
up to transport along `conjugate_one`. -/
theorem conjugateTrivialTateIso_one (r : ℤ) :
    L.conjugateTrivialTateIso 1 r = eqToIso (by rw [conjugate_one]) := by
  refine Iso.ext ?_
  have key := L.map_eq_conjugateTrivialTateIso_hom 1 L.conjugate_one
    L.conjugateGalEquiv_one.symm r
  have hid : TateCohomology.map (e := MulEquiv.refl L.Gal)
      (Rep.isIntertwiningMap_trivial ℤ (MonoidHom.id L.Gal)) r = 𝟙 _ :=
    TateCohomology.map_id (M := Rep.trivial ℤ L.Gal ℤ) r
  rw [hid] at key
  simpa using (comp_eqToHom_iff _ _ _).1 key.symm

/-- Conjugation by `h` and then by `g` on Tate cohomology with trivial integral coefficients
is conjugation by `g * h`, up to transport along `conjugate_conjugate`. -/
theorem conjugateTrivialTateIso_trans_conjugateTrivialTateIso (g h : G) (r : ℤ) :
    L.conjugateTrivialTateIso h r ≪≫ (L.conjugate h).conjugateTrivialTateIso g r =
      L.conjugateTrivialTateIso (g * h) r ≪≫ eqToIso (by rw [conjugate_conjugate]) := by
  refine Iso.ext ?_
  rw [Iso.trans_hom, Iso.trans_hom, eqToIso.hom, conjugateTrivialTateIso_hom,
    conjugateTrivialTateIso_hom]
  refine (TateCohomology.map_comp (e₁ := L.conjugateGalEquiv h)
    (e₂ := (L.conjugate h).conjugateGalEquiv g)
    (Rep.isIntertwiningMap_trivial ℤ (L.conjugateGalEquiv h).toMonoidHom)
    (Rep.isIntertwiningMap_trivial ℤ ((L.conjugate h).conjugateGalEquiv g).toMonoidHom) r).trans ?_
  exact L.map_eq_conjugateTrivialTateIso_hom (g * h) (L.conjugate_conjugate g h).symm
    (L.conjugateGalEquiv_trans_conjugateGalEquiv g h) r

/-- **In degree `-2`, conjugation is conjugation of abelianized Galois groups**: under the
identifications `H^{-2}(U/V, ℤ) ≃ (U/V)^ab`, it is the isomorphism induced by
`conjugateGalEquiv`. -/
@[simp]
theorem tateHMinusTwoEquivAbelianization_conjugateTrivialTateIso_apply
    (x : L.TrivialTateH (-2)) :
    (L.conjugate g).tateHMinusTwoEquivAbelianization ((L.conjugateTrivialTateIso g (-2)).hom x) =
      (L.conjugateGalEquiv g).abelianizationCongr.toAdditive
        (L.tateHMinusTwoEquivAbelianization x) := by
  rw [conjugateTrivialTateIso_hom, tateHMinusTwoEquivAbelianization_apply,
    tateHMinusTwoEquivAbelianization_apply, map_neg, neg_inj]
  exact TateCohomology.HNegTwoAddEquivAbelianization_map _ x

end NormalLayer

/-- **Cup product with a degree-two class commutes with conjugation**: conjugating `x ∪ u` by `g`
gives the cup product of the conjugate of `x` with the conjugate of `u`, in every degree. -/
@[simp]
theorem cupClass_conj (F : Formation G) (L : NormalLayer G) (g : G) (u : L.H F 2) (r : ℤ)
    (x : L.TrivialTateH r) :
    (L.conjugateTateIso F g (r + 2)).hom (cupClass F L u r x) =
      cupClass F (L.conjugate g) ((L.conjugateCohomologyIso F g 2).hom u) r
        ((L.conjugateTrivialTateIso g r).hom x) := by
  have hφ := L.isIntertwiningMap_conjugateCoefficientEquiv F g
  have h₀ := Rep.isIntertwiningMap_trivial (R := ℤ) ℤ (L.conjugateGalEquiv g).toMonoidHom
  -- The conjugation pair commutes with the left unitors `ℤ ⊗ A^V ≅ A^V`.
  have hl := TateCohomology.tateCohomologyFunctor_map_comp_map (h₀.tensor hφ) hφ
    (λ_ (L.rep F)).hom (λ_ ((L.conjugate g).rep F)).hom
    (TensorProduct.ext' fun n c ↦ by simp) (r + 2)
  rw [cupClass_apply, cupClass_apply, ← L.conjugateTateIso_hom_tateHIsoH_inv F g 2,
    NormalLayer.conjugateTrivialTateIso_hom, NormalLayer.conjugateTateIso_hom,
    NormalLayer.conjugateTateIso_hom, ← ModuleCat.comp_apply, hl, ModuleCat.comp_apply]
  exact congrArg _ (TateCohomology.map_cup h₀ hφ r 2 (r + 2) _ x _)

namespace ClassFormation

variable {F : Formation G}

/-- **Tate's isomorphism of a class formation commutes with conjugation**: conjugating
`x ∪ u_{U/V}` by `g` gives the cup product of the conjugate of `x` with the fundamental class of
the conjugate layer. -/
theorem tateIso_conj (cf : ClassFormation F) (L : NormalLayer G) (g : G) (r : ℤ)
    (x : L.TrivialTateH r) :
    (L.conjugateTateIso F g (r + 2)).hom (cf.tateIso L r x) =
      cf.tateIso (L.conjugate g) r ((L.conjugateTrivialTateIso g r).hom x) := by
  simp

end ClassFormation

end TauCeti.ClassFieldTheory
