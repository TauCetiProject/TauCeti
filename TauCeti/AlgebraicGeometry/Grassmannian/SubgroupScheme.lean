/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Scheme.Classification
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.HopfSpec
public import TauCeti.RingTheory.Grassmannian.QuotientHopfAlgebra

/-!
# Subgroup schemes classified by the Hopf-ideal locus

Let `H` be a commutative Hopf algebra over a commutative ring `R`, so that `Spec H` is an affine
group scheme over `Spec R`, and let `A` be an `R`-algebra. A point `N` of the Grassmannian functor
`G(k, A ⊗[R] H; A)` on the Hopf-ideal locus (`N.hopfIdealLocus = ⊥`) is a two-sided Hopf ideal of
`A ⊗[R] H` whose quotient is finite projective of constant rank `k` over `A`. This file attaches to
it the closed subgroup scheme `Spec ((A ⊗[R] H) ⧸ N)` of the base change `Spec (A ⊗[R] H)` of
`Spec H` to `Spec A`, and proves that it is finite, flat and of finite presentation over `Spec A`,
of constant rank `k`.

Conversely, every closed subgroup scheme of `Spec (A ⊗[R] H)` which is finite locally free of
constant rank `k` over `Spec A` arises from exactly one such point
(`Module.Grassmannian.hopfIdealLocusEquivClosedSubgroupScheme`). So the Hopf-ideal locus is the
functor of rank-`k` finite locally free subgroup schemes of `Spec H`, evaluated on affine schemes,
and `subgroupScheme` is its universal subgroup at each point. The equivalence combines the
ring-level description of the locus (`Module.Grassmannian.hopfIdealLocusEquiv`) with the
classification of closed subgroup schemes of an affine group scheme by Hopf ideals
(`TauCeti.CommHopfAlgCat.hopfIdealOrderIsoClosedSubgroup`). Finiteness, flatness, finite
presentation and rank of the Hopf spectrum of the quotient are read off from the quotient
Hopf algebra by `TauCeti.moduleFinite_iff_isFinite_hopfSpec`,
`TauCeti.moduleProjective_iff_flat_and_locallyOfFinitePresentation_hopfSpec` and
`TauCeti.finrank_hopfSpec`.

The scheme-level statements use Mathlib's `hopfSpec`, which requires the base ring and the Hopf
algebra to lie in the same universe.

## Main definitions

* `Module.Grassmannian.subgroupScheme N hN`: the closed subgroup scheme of `Spec (A ⊗[R] H)`
  attached to a point `N` of the Hopf-ideal locus.
* `Module.Grassmannian.hopfIdealLocusEquivClosedSubgroupScheme`: the points of the Hopf-ideal
  locus correspond to the closed subgroup schemes of `Spec (A ⊗[R] H)` which are finite locally
  free of constant rank `k` over `Spec A`.

## Main results

* `Module.Grassmannian.isFinite_subgroupScheme`, `Module.Grassmannian.flat_subgroupScheme`,
  `Module.Grassmannian.locallyOfFinitePresentation_subgroupScheme` and
  `Module.Grassmannian.finrank_subgroupScheme`: the subgroup scheme attached to `N` is finite
  locally free of constant rank `k` over `Spec A`.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, §1.1, for finite locally free
  subgroup schemes and their ranks.
* W. C. Waterhouse, *Introduction to Affine Group Schemes* (Springer, 1979), §2.1, for closed
  subgroup schemes of affine group schemes as quotients by Hopf ideals.
* [The Stacks Project, Tag 089R](https://stacks.math.columbia.edu/tag/089R), for the Grassmannian
  functor.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite TensorProduct

universe u

namespace Module.Grassmannian

variable {R : Type u} [CommRing R] {k : ℕ} {A : Type u} [CommRing A] [Algebra R A]
  {H : Type u} [CommRing H] [HopfAlgebra R H]

/-- Being finite locally free of constant rank `k` is invariant under isomorphism over the
base. -/
private theorem finiteLocallyFree_iff_of_iso {S : Scheme.{u}} {X Y : Over S} (e : X ≅ Y) :
    (IsFinite X.hom ∧ AlgebraicGeometry.Flat X.hom ∧ LocallyOfFinitePresentation X.hom ∧
        ∀ s, X.hom.finrank s = k) ↔
      (IsFinite Y.hom ∧ AlgebraicGeometry.Flat Y.hom ∧ LocallyOfFinitePresentation Y.hom ∧
        ∀ s, Y.hom.finrank s = k) := by
  rw [← Over.w e.hom, MorphismProperty.cancel_left_of_respectsIso (P := @IsFinite),
    MorphismProperty.cancel_left_of_respectsIso (P := @AlgebraicGeometry.Flat),
    MorphismProperty.cancel_left_of_respectsIso (P := @LocallyOfFinitePresentation)]
  refine and_congr_right fun _ ↦ and_congr_right fun _ ↦ and_congr_right fun _ ↦ ?_
  rw [Scheme.Hom.finrank_comp_left_of_isIso]

/-- The closed subgroup scheme cut out by a Hopf ideal `I` of a commutative `A`-Hopf algebra `G`
is finite locally free of constant rank `k` over `Spec A` exactly when `G ⧸ I` is finite projective
of constant rank `k` over `A`. -/
private theorem finiteLocallyFree_quotientClosedSubgroup_iff (G : CommHopfAlgCat.{u} A)
    (I : TauCeti.HopfIdeal A G) :
    (IsFinite ((TauCeti.CommHopfAlgCat.quotientClosedSubgroup G I).1 :
          Grp (Over (Spec (CommRingCat.of A)))).X.hom ∧
        AlgebraicGeometry.Flat ((TauCeti.CommHopfAlgCat.quotientClosedSubgroup G I).1 :
          Grp (Over (Spec (CommRingCat.of A)))).X.hom ∧
        LocallyOfFinitePresentation ((TauCeti.CommHopfAlgCat.quotientClosedSubgroup G I).1 :
          Grp (Over (Spec (CommRingCat.of A)))).X.hom ∧
        ∀ s, (((TauCeti.CommHopfAlgCat.quotientClosedSubgroup G I).1 :
          Grp (Over (Spec (CommRingCat.of A)))).X.hom).finrank s = k) ↔
      Module.Finite A (G ⧸ I.toIdeal) ∧ Module.Projective A (G ⧸ I.toIdeal) ∧
        ∀ p, rankAtStalk (R := A) (G ⧸ I.toIdeal) p = k := by
  let e : ((TauCeti.CommHopfAlgCat.quotientClosedSubgroup G I).1 :
      Grp (Over (Spec (CommRingCat.of A)))).X ≅ (TauCeti.CommHopfAlgCat.quotientSpec G I).X :=
    (Grp.forget _).mapIso (Subobject.underlying.mapIso
      (eqToIso (TauCeti.CommHopfAlgCat.quotientClosedSubgroup_coe G I)) ≪≫
        Subobject.underlyingIso (TauCeti.CommHopfAlgCat.quotientSpecι G I))
  refine (finiteLocallyFree_iff_of_iso e).trans ?_
  rw [← TauCeti.moduleFinite_iff_isFinite_hopfSpec]
  refine and_congr_right fun _ ↦ ?_
  rw [← and_assoc, ← TauCeti.moduleProjective_iff_flat_and_locallyOfFinitePresentation_hopfSpec]
  refine and_congr_right fun _ ↦ ?_
  -- The points of `Spec A` are the prime ideals of `A`, where `finrank_hopfSpec` is stated.
  exact forall_congr' fun s ↦ (congrArg (· = k)
    (TauCeti.finrank_hopfSpec A (_root_.CommHopfAlgCat.quotient G I) s)).to_iff

section SubgroupScheme

variable (N : G(k, A ⊗[R] H; A)) (hN : N.hopfIdealLocus = ⊥)

/-- The closed subgroup scheme of the base change `Spec (A ⊗[R] H)` of `Spec H` to `Spec A`
attached to a point `N` of the Hopf-ideal locus: the spectrum of the quotient Hopf algebra
`(A ⊗[R] H) ⧸ N.hopfIdeal hN`. It is finite locally free of rank `k` over `Spec A`. -/
noncomputable def subgroupScheme :
    TauCeti.ClosedSubgroupScheme
      ((hopfSpec (CommRingCat.of A)).obj (op (CommHopfAlgCat.of A (A ⊗[R] H)))) :=
  TauCeti.CommHopfAlgCat.quotientClosedSubgroup _
    (TauCeti.HopfIdeal.ofIsHopfIdeal A (N.hopfIdeal hN))

/-- The subgroup scheme attached to `N` is cut out by the Hopf ideal `N.hopfIdeal hN`. -/
theorem subgroupScheme_def :
    N.subgroupScheme hN = TauCeti.CommHopfAlgCat.quotientClosedSubgroup _
      (TauCeti.HopfIdeal.ofIsHopfIdeal A (N.hopfIdeal hN)) :=
  (rfl)

/-- The subgroup scheme attached to a point of the Hopf-ideal locus is finite locally free of
rank `k`. -/
private theorem finiteLocallyFree_subgroupScheme :
    IsFinite ((N.subgroupScheme hN).1 : Grp (Over (Spec (CommRingCat.of A)))).X.hom ∧
      AlgebraicGeometry.Flat ((N.subgroupScheme hN).1 :
        Grp (Over (Spec (CommRingCat.of A)))).X.hom ∧
      LocallyOfFinitePresentation ((N.subgroupScheme hN).1 :
        Grp (Over (Spec (CommRingCat.of A)))).X.hom ∧
      ∀ s, (((N.subgroupScheme hN).1 :
        Grp (Over (Spec (CommRingCat.of A)))).X.hom).finrank s = k :=
  (finiteLocallyFree_quotientClosedSubgroup_iff _ _).2 <| by
    rw [TauCeti.HopfIdeal.ofIsHopfIdeal_toIdeal]
    exact ⟨inferInstance, inferInstance, rankAtStalk_quotient_hopfIdeal N hN⟩

/-- The subgroup scheme attached to a point of the Hopf-ideal locus is finite over `Spec A`. -/
instance isFinite_subgroupScheme :
    IsFinite ((N.subgroupScheme hN).1 : Grp (Over (Spec (CommRingCat.of A)))).X.hom :=
  (finiteLocallyFree_subgroupScheme N hN).1

/-- The subgroup scheme attached to a point of the Hopf-ideal locus is flat over `Spec A`. -/
instance flat_subgroupScheme :
    AlgebraicGeometry.Flat ((N.subgroupScheme hN).1 :
      Grp (Over (Spec (CommRingCat.of A)))).X.hom :=
  (finiteLocallyFree_subgroupScheme N hN).2.1

/-- The subgroup scheme attached to a point of the Hopf-ideal locus is of finite presentation
over `Spec A`. -/
instance locallyOfFinitePresentation_subgroupScheme :
    LocallyOfFinitePresentation ((N.subgroupScheme hN).1 :
      Grp (Over (Spec (CommRingCat.of A)))).X.hom :=
  (finiteLocallyFree_subgroupScheme N hN).2.2.1

/-- The subgroup scheme attached to a point `N` of `G(k, A ⊗[R] H; A)` on the Hopf-ideal locus
has constant rank `k` over `Spec A`. -/
theorem finrank_subgroupScheme (s : Spec (CommRingCat.of A)) :
    (((N.subgroupScheme hN).1 : Grp (Over (Spec (CommRingCat.of A)))).X.hom).finrank s = k :=
  (finiteLocallyFree_subgroupScheme N hN).2.2.2 s

end SubgroupScheme

/-- **The Hopf-ideal locus classifies subgroup schemes of rank `k`.** For a commutative Hopf
algebra `H` over `R` and an `R`-algebra `A`, the points of `G(k, A ⊗[R] H; A)` on the Hopf-ideal
locus correspond to the closed subgroup schemes of `Spec (A ⊗[R] H)` which are finite locally free
of constant rank `k` over `Spec A`. A point `N` goes to `N.subgroupScheme hN`. -/
noncomputable def hopfIdealLocusEquivClosedSubgroupScheme :
    {N : G(k, A ⊗[R] H; A) // N.hopfIdealLocus = ⊥} ≃
      {P : TauCeti.ClosedSubgroupScheme
          ((hopfSpec (CommRingCat.of A)).obj (op (CommHopfAlgCat.of A (A ⊗[R] H)))) //
        IsFinite (P.1 : Grp (Over (Spec (CommRingCat.of A)))).X.hom ∧
          AlgebraicGeometry.Flat (P.1 : Grp (Over (Spec (CommRingCat.of A)))).X.hom ∧
          LocallyOfFinitePresentation (P.1 : Grp (Over (Spec (CommRingCat.of A)))).X.hom ∧
          ∀ s, ((P.1 : Grp (Over (Spec (CommRingCat.of A)))).X.hom).finrank s = k} :=
  hopfIdealLocusEquiv.trans <| Equiv.subtypeEquiv
    (OrderDual.toDual.trans (TauCeti.CommHopfAlgCat.hopfIdealOrderIsoClosedSubgroup
      (CommHopfAlgCat.of A (A ⊗[R] H))).toEquiv)
    fun I ↦ by
      rw [Equiv.trans_apply, OrderIso.coe_toEquiv,
        TauCeti.CommHopfAlgCat.hopfIdealOrderIsoClosedSubgroup_apply, OrderDual.ofDual_toDual,
        finiteLocallyFree_quotientClosedSubgroup_iff]

/-- `hopfIdealLocusEquivClosedSubgroupScheme` sends a point `N` of the Hopf-ideal locus to
`N.subgroupScheme hN`. -/
@[simp↓]
theorem hopfIdealLocusEquivClosedSubgroupScheme_apply_coe
    (N : {N : G(k, A ⊗[R] H; A) // N.hopfIdealLocus = ⊥}) :
    (hopfIdealLocusEquivClosedSubgroupScheme N).1 = N.1.subgroupScheme N.2 := by
  simp only [hopfIdealLocusEquivClosedSubgroupScheme, Equiv.trans_apply, Equiv.subtypeEquiv_apply,
    OrderIso.coe_toEquiv, hopfIdealLocusEquiv_apply_coe, subgroupScheme_def]
  exact TauCeti.CommHopfAlgCat.hopfIdealOrderIsoClosedSubgroup_apply _ _

/-- `hopfIdealLocusEquivClosedSubgroupScheme.symm` sends a closed subgroup scheme to the
underlying `A`-submodule of its defining Hopf ideal. -/
@[simp↓]
theorem hopfIdealLocusEquivClosedSubgroupScheme_symm_apply_toSubmodule
    (P : {P : TauCeti.ClosedSubgroupScheme
          ((hopfSpec (CommRingCat.of A)).obj (op (CommHopfAlgCat.of A (A ⊗[R] H)))) //
        IsFinite (P.1 : Grp (Over (Spec (CommRingCat.of A)))).X.hom ∧
          AlgebraicGeometry.Flat (P.1 : Grp (Over (Spec (CommRingCat.of A)))).X.hom ∧
          LocallyOfFinitePresentation (P.1 : Grp (Over (Spec (CommRingCat.of A)))).X.hom ∧
          ∀ s, ((P.1 : Grp (Over (Spec (CommRingCat.of A)))).X.hom).finrank s = k}) :
    (hopfIdealLocusEquivClosedSubgroupScheme.symm P).1.toSubmodule =
      (OrderDual.ofDual ((TauCeti.CommHopfAlgCat.hopfIdealOrderIsoClosedSubgroup
        (CommHopfAlgCat.of A (A ⊗[R] H))).symm P.1)).toIdeal.restrictScalars A := by
  simp only [hopfIdealLocusEquivClosedSubgroupScheme, Equiv.symm_trans_apply,
    Equiv.subtypeEquiv_symm, Equiv.subtypeEquiv_apply, hopfIdealLocusEquiv_symm_apply_toSubmodule,
    OrderIso.coe_symm_toEquiv, OrderDual.toDual_symm_eq]

end Module.Grassmannian
