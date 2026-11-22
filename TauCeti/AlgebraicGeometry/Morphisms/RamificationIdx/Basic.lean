/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.SurjectiveOnStalks
public import TauCeti.RingTheory.RamificationInertia.Bijective
public import TauCeti.RingTheory.RamificationInertia.DiscreteValuationRing
public import TauCeti.RingTheory.RamificationInertia.Localization
public import TauCeti.RingTheory.RamificationInertia.QuasiFinite

/-!
# The ramification index of a morphism at a point

The ramification index `ramificationIdxAt f x` of a morphism of schemes `f : X ⟶ Y` at a point
`x` is Mathlib's ramification index `Ideal.ramificationIdx` of the maximal ideal of the local ring
`𝒪_{X,x}` over `𝒪_{Y,f(x)}` along the stalk map, that is, the length of
`𝒪_{X,x} ⧸ 𝔪_{f(x)} 𝒪_{X,x}` when this length is finite, and `0` when it is infinite. When the stalk
map is a finite injective local homomorphism of discrete valuation rings, this is the usual
ramification index of that extension (Stacks, Definition 15.113.1 (09E4)).

It is finite and positive at every point where `f` is quasi-finite, since the stalk map is then
quasi-finite and `Ideal.ramificationIdx_pos_of_quasiFiniteAt` applies.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.ramificationIdxAt`: the ramification index of a morphism at a point.

## Main results

* `AlgebraicGeometry.Scheme.Hom.ramificationIdxAt_def`: the defining equation.
* `AlgebraicGeometry.Scheme.Hom.ramificationIdxAt_pos`: the ramification index is positive at every
  point where the morphism is quasi-finite.
* `AlgebraicGeometry.Scheme.Hom.ramificationIdxAt_comp_of_flat_stalkMap`: ramification indices
  multiply in a tower when the first stalk map is flat.
* `AlgebraicGeometry.Scheme.Hom.ramificationIdxAt_comp`: ramification indices multiply in a tower
  whose first morphism is flat.
* `AlgebraicGeometry.Scheme.Hom.map_maximalIdeal_eq_pow_ramificationIdxAt_of_map_ne_bot`: when the
  source stalk is a DVR and the mapped maximal ideal is nonzero, it equals the power of the source
  maximal ideal with exponent the ramification index.
* `AlgebraicGeometry.Scheme.Hom.ramificationIdxAt_eq_of_map_maximalIdeal_eq_pow`: when the source
  stalk is a DVR, the index equals any exponent satisfying that maximal-ideal identity.
* `AlgebraicGeometry.Scheme.Hom.ramificationIdxAt_eq_one_of_isField`,
  `AlgebraicGeometry.Scheme.Hom.ramificationIdxAt_eq_one_of_surjectiveOnStalks`,
  `AlgebraicGeometry.Scheme.Hom.ramificationIdxAt_comp_of_surjectiveOnStalks`,
  `AlgebraicGeometry.Scheme.Hom.ramificationIdxAt_eq_of_isOpenImmersion_square`: invariance under
  field stalks, morphisms surjective on stalks, and open immersions.
* `AlgebraicGeometry.Scheme.Hom.ramificationIdxAt_specMap`: affine comparison with
  `Ideal.ramificationIdx`.
* `AlgebraicGeometry.Scheme.Hom.ramificationIdxAt_eq_of_commSq_of_eq_one`: horizontal comparison
  in a commutative square with flat left stalk map and vertical ramification indices `1`.

## References

* Ported from T. Dupuy, T. Tucker and Z. Wang,
  [pcfawd-formalization](https://github.com/tdupu/pcfawd-formalization) at commit
  `9a20b3f351446d64e6015d704198bc71c7002008` (Apache-2.0),
  `lean/Pcf/Bounding/SchemeDynamics.lean`: `ramificationIdxAt` is its
  `Pcf.schemeDivisorRamificationIdx` (there restricted to codimension-one points), and
  `ramificationIdxAt_pos` generalizes its `Pcf.schemeDivisorRamificationIdx_pos` (there for a
  locally quasi-finite morphism). The composition theorem generalizes its
  `Pcf.schemeDivisorRamificationIdx_comp` (there for a finite dominant first morphism with integral
  source and a codimension-one point on a locally Noetherian normal intermediate scheme).
  The maximal-ideal comparison generalizes its `Pcf.heightOneRamificationIdx_eq_dvrExponent`
  (`lean/Pcf/Bounding/Divisors.lean`).
* [Stacks Project, Definition 15.113.1](https://stacks.math.columbia.edu/tag/09E4).
-/

public section

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The **ramification index of `f` at `x`**: the ramification index (Mathlib
`Ideal.ramificationIdx`) of the maximal ideal of `𝒪_{X,x}` over `𝒪_{Y,f(x)}` along the stalk
map: the length of `𝒪_{X,x} ⧸ 𝔪_{f(x)} 𝒪_{X,x}` when it is finite, and `0` otherwise. -/
noncomputable def ramificationIdxAt (x : X) : ℕ :=
  letI := (f.stalkMap x).hom.toAlgebra
  (IsLocalRing.maximalIdeal (X.presheaf.stalk x)).ramificationIdx (Y.presheaf.stalk (f x))

/-- The ramification index of `f` at `x` is the ramification index of the maximal ideal of
`𝒪_{X,x}` over `𝒪_{Y,f(x)}`, for the algebra structure given by the stalk map. -/
theorem ramificationIdxAt_def (x : X) :
    ramificationIdxAt f x =
      letI := (f.stalkMap x).hom.toAlgebra
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x)).ramificationIdx (Y.presheaf.stalk (f x)) :=
  (rfl)

/-- The ramification index of `f` is positive at every point where `f` is quasi-finite. -/
theorem ramificationIdxAt_pos {x : X} (hx : f.QuasiFiniteAt x) : 0 < ramificationIdxAt f x := by
  let := (f.stalkMap x).hom.toAlgebra
  rw [Scheme.Hom.QuasiFiniteAt] at hx
  have : Algebra.QuasiFinite (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    RingHom.quasiFinite_algebraMap.mp hx
  rw [ramificationIdxAt_def]
  exact Ideal.ramificationIdx_pos_of_quasiFiniteAt _

/-- Ramification indices multiply along a composite at any point where the first stalk map is
flat. No finiteness, normality, or codimension assumptions are required. -/
theorem ramificationIdxAt_comp_of_flat_stalkMap {Z : Scheme.{u}} (g : Y ⟶ Z) (x : X)
    (hflat : (f.stalkMap x).hom.Flat) :
    ramificationIdxAt (f ≫ g) x = ramificationIdxAt f x * ramificationIdxAt g (f x) := by
  let sourceStalk := Z.presheaf.stalk (g (f x))
  let middleStalk := Y.presheaf.stalk (f x)
  let targetStalk := X.presheaf.stalk x
  let compositeStalkMap : sourceStalk ⟶ targetStalk :=
    eqToHom (congrArg Z.presheaf.stalk (Scheme.Hom.comp_apply f g x).symm) ≫
      (f ≫ g).stalkMap x
  let : Algebra sourceStalk middleStalk := (g.stalkMap (f x)).hom.toAlgebra
  let : Algebra middleStalk targetStalk := (f.stalkMap x).hom.toAlgebra
  let : Algebra sourceStalk targetStalk := compositeStalkMap.hom.toAlgebra
  have htransport :
      eqToHom (congrArg Z.presheaf.stalk (Scheme.Hom.comp_apply f g x).symm) =
        𝟙 sourceStalk := by
    cases Scheme.Hom.comp_apply f g x
    rfl
  have hcomp : compositeStalkMap.hom =
      (f.stalkMap x).hom.comp (g.stalkMap (f x)).hom := by
    dsimp only [compositeStalkMap]
    erw [htransport, Category.id_comp, Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp]
  have : IsScalarTower sourceStalk middleStalk targetStalk := .of_algebraMap_eq' hcomp
  have : IsLocalHom (algebraMap middleStalk targetStalk) :=
    inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
  have : Module.Flat middleStalk targetStalk := RingHom.flat_algebraMap_iff.mp hflat
  rw [ramificationIdxAt_def, ramificationIdxAt_def, ramificationIdxAt_def, mul_comm]
  exact Ideal.ramificationIdx_tower (R := sourceStalk) (maximalIdeal middleStalk)
    (maximalIdeal targetStalk)

/-- Ramification indices multiply along any composite whose first morphism is flat. -/
@[simp]
theorem ramificationIdxAt_comp {Z : Scheme.{u}} (g : Y ⟶ Z) [Flat f] (x : X) :
    ramificationIdxAt (f ≫ g) x = ramificationIdxAt f x * ramificationIdxAt g (f x) :=
  f.ramificationIdxAt_comp_of_flat_stalkMap g x (Flat.stalkMap f x)

/-- The maximal-ideal power identity at a point with a DVR stalk, assuming that the mapped
maximal ideal is nonzero. -/
theorem map_maximalIdeal_eq_pow_ramificationIdxAt_of_map_ne_bot
    (x : X) [IsDomain (X.presheaf.stalk x)] [IsDiscreteValuationRing (X.presheaf.stalk x)]
    (hmap : (maximalIdeal (Y.presheaf.stalk (f x))).map (f.stalkMap x).hom ≠ ⊥) :
    (maximalIdeal (Y.presheaf.stalk (f x))).map (f.stalkMap x).hom =
      maximalIdeal (X.presheaf.stalk x) ^ ramificationIdxAt f x := by
  let := (f.stalkMap x).hom.toAlgebra
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
  rw [ramificationIdxAt_def]
  exact TauCeti.IsDiscreteValuationRing.map_maximalIdeal_eq_pow_ramificationIdx hmap

/-- The pointwise ramification index equals the DVR exponent characterized by the maximal-ideal
identity in Stacks, Definition 15.113.1 (09E4).

Divergence from Stacks: only the source stalk needs to be a DVR. No dominance or assumption
on the target is required when the maximal-ideal power identity is supplied. -/
@[stacks 09E4 "comparison with the exponent in the maximal-ideal identity"]
theorem ramificationIdxAt_eq_of_map_maximalIdeal_eq_pow
    (x : X) [IsDomain (X.presheaf.stalk x)] [IsDiscreteValuationRing (X.presheaf.stalk x)]
    {exponent : ℕ}
    (hexponent : (maximalIdeal (Y.presheaf.stalk (f x))).map (f.stalkMap x).hom =
      maximalIdeal (X.presheaf.stalk x) ^ exponent) :
    f.ramificationIdxAt x = exponent := by
  let := (f.stalkMap x).hom.toAlgebra
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
  rw [ramificationIdxAt_def]
  exact TauCeti.IsDiscreteValuationRing.ramificationIdx_eq_of_map_maximalIdeal_eq_pow hexponent

/-- If the stalk of `X` at `x` is a field, then `f.ramificationIdxAt x = 1`. -/
theorem ramificationIdxAt_eq_one_of_isField {x : X} (hx : IsField (X.presheaf.stalk x)) :
    f.ramificationIdxAt x = 1 := by
  let := (f.stalkMap x).hom.toAlgebra; let := hx.toField
  rw [ramificationIdxAt_def, isField_iff_maximalIdeal_eq.mp hx, Ideal.ramificationIdx_bot_eq_one]

/-- If `f.stalkMap x` is surjective, `f.ramificationIdxAt x = 1`. -/
theorem ramificationIdxAt_eq_one_of_surjective_stalkMap {x : X}
    (hsurj : Function.Surjective (f.stalkMap x).hom) : f.ramificationIdxAt x = 1 := by
  let := (f.stalkMap x).hom.toAlgebra
  rw [ramificationIdxAt_def, ramificationIdx_maximalIdeal_eq_one_iff]
  exact Ideal.map_comap_of_surjective _ hsurj _

/-- A morphism surjective on stalks has ramification index `1` at every point. -/
@[simp]
theorem ramificationIdxAt_eq_one_of_surjectiveOnStalks [SurjectiveOnStalks f] (x : X) :
    f.ramificationIdxAt x = 1 :=
  f.ramificationIdxAt_eq_one_of_surjective_stalkMap (SurjectiveOnStalks.stalkMap_surjective f x)

/-- Postcomposing `f` with `g` surjective on stalks at `f x` preserves `ramificationIdxAt`. -/
theorem ramificationIdxAt_comp_of_surjective_stalkMap {Z : Scheme.{u}} (g : Y ⟶ Z)
    (x : X) (hsurj : Function.Surjective (g.stalkMap (f x)).hom) :
    (f ≫ g).ramificationIdxAt x = f.ramificationIdxAt x := by
  let : Algebra (Z.presheaf.stalk ((f ≫ g) x)) (Y.presheaf.stalk (f x)) :=
    (g.stalkMap (f x)).hom.toAlgebra
  let : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := (f.stalkMap x).hom.toAlgebra
  let : Algebra (Z.presheaf.stalk ((f ≫ g) x)) (X.presheaf.stalk x) :=
    ((f ≫ g).stalkMap x).hom.toAlgebra
  have : IsScalarTower (Z.presheaf.stalk ((f ≫ g) x)) (Y.presheaf.stalk (f x))
      (X.presheaf.stalk x) :=
    .of_algebraMap_eq' (congrArg CommRingCat.Hom.hom (Scheme.Hom.stalkMap_comp f g x))
  rw [ramificationIdxAt_def, ramificationIdxAt_def]
  exact (Ideal.ramificationIdx_eq_of_surjective hsurj _).symm

/-- Postcomposing `f` with a morphism surjective on stalks preserves `ramificationIdxAt`. -/
@[simp]
theorem ramificationIdxAt_comp_of_surjectiveOnStalks {Z : Scheme.{u}} (g : Y ⟶ Z)
    [SurjectiveOnStalks g] (x : X) :
    (f ≫ g).ramificationIdxAt x = f.ramificationIdxAt x :=
  ramificationIdxAt_comp_of_surjective_stalkMap f g x
    (SurjectiveOnStalks.stalkMap_surjective g (f x))

/-- In a commutative square `ι ≫ f' = h ≫ j` with open immersions `ι` and `j`,
`f'.ramificationIdxAt (ι q) = h.ramificationIdxAt q`. -/
theorem ramificationIdxAt_eq_of_isOpenImmersion_square {X₀ Y₀ X' Y' : Scheme.{u}} (ι : X₀ ⟶ X')
    (f' : X' ⟶ Y') (h : X₀ ⟶ Y₀) (j : Y₀ ⟶ Y') [IsOpenImmersion ι] [IsOpenImmersion j]
    (e : ι ≫ f' = h ≫ j) (q : X₀) :
    f'.ramificationIdxAt (ι q) = h.ramificationIdxAt q := by
  simpa using congrArg (fun k : X₀ ⟶ Y' ↦ k.ramificationIdxAt q) e

/-- For `Spec.map (algebraMap R S)`, `ramificationIdxAt` at `q` is `q.asIdeal.ramificationIdx R`. -/
@[simp]
theorem ramificationIdxAt_specMap {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (q : Spec (.of S)) :
    (Spec.map (CommRingCat.ofHom (algebraMap R S))).ramificationIdxAt q =
      q.asIdeal.ramificationIdx R := by
  have := q.isPrime
  let φ := CommRingCat.ofHom (algebraMap R S)
  let p := PrimeSpectrum.comap φ.hom q
  have : p.asIdeal.IsPrime := p.isPrime; have : q.asIdeal.LiesOver p.asIdeal := ⟨rfl⟩
  let Rp := Localization.AtPrime p.asIdeal; let Sq := Localization.AtPrime q.asIdeal
  let : Algebra Rp Sq := (Localization.localRingHom p.asIdeal q.asIdeal φ.hom rfl).toAlgebra
  have : IsScalarTower R Rp Sq := .of_algebraMap_eq fun r ↦
    (Localization.localRingHom_to_map p.asIdeal q.asIdeal φ.hom rfl r).symm
  have : IsLocalHom (algebraMap Rp Sq) :=
    Localization.isLocalHom_localRingHom p.asIdeal q.asIdeal φ.hom rfl
  let SR := (Spec (.of R)).presheaf.stalk ((Spec.map φ) q)
  let SS := (Spec (.of S)).presheaf.stalk q
  let ep : CommRingCat.of Rp ≅ SR := (AlgebraicGeometry.Spec.stalkIso (.of R) p).symm
  let eq : SS ≅ CommRingCat.of Sq := AlgebraicGeometry.Spec.stalkIso (.of S) q
  let : Algebra Rp SR := ep.hom.hom.toAlgebra
  let : Algebra SR SS := ((Spec.map φ).stalkMap q).hom.toAlgebra
  let : Algebra SR Sq := (((Spec.map φ).stalkMap q) ≫ eq.hom).hom.toAlgebra
  have hsq : ep.hom ≫ (Spec.map φ).stalkMap q ≫ eq.hom = CommRingCat.ofHom (algebraMap Rp Sq) :=
    (Iso.inv_comp_eq ep.symm).mpr ((Iso.comp_inv_eq eq).mp <|
      (Category.assoc ep.symm.hom _ eq.inv).trans (localRingHom_comp_stalkIso φ q)).symm
  have : IsScalarTower Rp SR Sq := .of_algebraMap_eq' (congrArg CommRingCat.Hom.hom hsq).symm
  let algEq : SS ≃ₐ[SR] Sq := AlgEquiv.ofRingEquiv (f := eq.commRingCatIsoToRingEquiv) fun x ↦ by
    rw [← RingEquiv.coe_toRingHom, Iso.commRingCatIsoToRingEquiv_toRingHom,
      RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra, CommRingCat.hom_comp,
      RingHom.comp_apply]
  have : IsLocalHom algEq.toRingHom := ⟨fun a ha ↦ (isUnit_map_iff algEq a).mp ha⟩
  have hmax : (maximalIdeal SS).map algEq = maximalIdeal Sq := by
    rw [← maximalIdeal_comap algEq.toRingHom]
    exact Ideal.map_comap_of_surjective algEq.toRingHom algEq.surjective _
  rw [ramificationIdxAt_def, ← Ideal.ramificationIdx_map_algEquiv algEq, hmax,
    Ideal.ramificationIdx_eq_of_surjective (ConcreteCategory.bijective_of_isIso ep.hom).surjective,
    Ideal.ramificationIdx_maximalIdeal_localization_of_liesOver p.asIdeal q.asIdeal]

/-- **Comparison of `ramificationIdxAt` in a commutative square** with flat left stalk map and
vertical ramification indices `1`. -/
theorem ramificationIdxAt_eq_of_commSq_of_eq_one {X' Y' : Scheme.{u}} {gX : X' ⟶ X}
    {f' : X' ⟶ Y'} {f : X ⟶ Y} {gY : Y' ⟶ Y} (w : gX ≫ f = f' ≫ gY) (x' : X')
    (hflat : (gX.stalkMap x').hom.Flat) (hgX : gX.ramificationIdxAt x' = 1)
    (hgY : gY.ramificationIdxAt (f' x') = 1) :
    f'.ramificationIdxAt x' = f.ramificationIdxAt (gX x') := by
  let R := Y.presheaf.stalk (f (gX x')); let R' := Y.presheaf.stalk (gY (f' x'))
  let S := Y'.presheaf.stalk (f' x'); let A := X.presheaf.stalk (gX x')
  let B := X'.presheaf.stalk x'
  have hw : f (gX x') = gY (f' x') := by rw [← Scheme.Hom.comp_apply, w, Scheme.Hom.comp_apply]
  let eR : R ⟶ R' := (Y.presheaf.stalkCongr (.of_eq hw)).hom
  let : Algebra R R' := eR.hom.toAlgebra; let : Algebra R' S := (gY.stalkMap (f' x')).hom.toAlgebra
  let : Algebra R S := (eR ≫ gY.stalkMap (f' x')).hom.toAlgebra
  let : Algebra R A := (f.stalkMap (gX x')).hom.toAlgebra
  let : Algebra A B := (gX.stalkMap x').hom.toAlgebra
  let : Algebra S B := (f'.stalkMap x').hom.toAlgebra
  let : Algebra R B := (f.stalkMap (gX x') ≫ gX.stalkMap x').hom.toAlgebra
  have hsq : f.stalkMap (gX x') ≫ gX.stalkMap x' =
      (eR ≫ gY.stalkMap (f' x')) ≫ f'.stalkMap x' := by
    rw [← Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_congr_hom _ _ w x',
      Scheme.Hom.stalkMap_comp, Category.assoc]; rfl
  have : IsScalarTower R R' S := .of_algebraMap_eq' rfl
  have : IsScalarTower R A B := .of_algebraMap_eq' rfl
  have : IsScalarTower R S B := .of_algebraMap_eq' (congrArg CommRingCat.Hom.hom hsq)
  have : IsLocalHom (algebraMap S B) := inferInstanceAs (IsLocalHom (f'.stalkMap x').hom)
  have : IsLocalHom (algebraMap A B) := inferInstanceAs (IsLocalHom (gX.stalkMap x').hom)
  have : Module.Flat A B := RingHom.flat_algebraMap_iff.mp hflat
  rw [ramificationIdxAt_def] at hgX hgY
  have hRS : (maximalIdeal S).ramificationIdx R = 1 := by
    rw [← Ideal.ramificationIdx_eq_of_surjective (T := S)
      (ConcreteCategory.bijective_of_isIso eR).surjective]
    exact hgY
  rw [ramificationIdxAt_def, ramificationIdxAt_def]
  exact Ideal.ramificationIdx_eq_of_isLocalHom_square (R := R) (S := S) (A := A) (B := B) hgX hRS

end AlgebraicGeometry.Scheme.Hom
