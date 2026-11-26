/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Subsystem.Basic
import TauCeti.Algebra.AlgebraicGroup.Chevalley.OrderedProduct
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Weyl.Root

/-!
# Ordered root-product coordinates on Chevalley root-set subgroups

For any set of roots `S` of a Chevalley datum `D` and any point subgroup `U` containing the root
subgroups indexed by `S` (in particular `D.subsystemPoints S A`, `D.positivePoints A`, and
`D.negativePoints A`), `rootSetProduct` multiplies root parameters `u : S → A` in the order of a
list `l : List S` to produce an element of `U`. When an additive rational weight functional `degree`
is strictly positive on `S`, any duplicate-free enumeration `l` of `S` gives an injective
coordinate map over every commutative ring `A`. Moreover, conjugation by an element of
`D.weylSubgroup A` from `ChevalleyDatum.exists_conj_rootSubgroupPoints_eq_of_weylGroup` transports
ordered-product surjectivity along any Weyl-group element `w`.

`TauCeti.Algebra.AlgebraicGroup.Chevalley.Positive.Coordinates` and
`TauCeti.Algebra.AlgebraicGroup.Chevalley.Opposite.Coordinates` instantiate these constructions for
`D.positivePoints A` and `D.negativePoints A`. No closure condition on `S` is required for the
product map or its injectivity, and no scheme-theoretic isomorphism is asserted here.

## Main declarations

* `TauCeti.DynkinType.ChevalleyDatum.rootSetProduct`: ordered multiplication of `S`-indexed root
  parameters into a point subgroup `U` containing `{X_γ | γ ∈ S}`.
* `TauCeti.DynkinType.ChevalleyDatum.rootSetProduct_injective_of_degree_pos`: parameter injectivity
  when an additive functional `degree` is positive on `S`.
* `TauCeti.DynkinType.ChevalleyDatum.rootSetProduct_surjective_of_weylGroup`: Weyl-conjugation
  transport of ordered-product surjectivity across root sets.
* `TauCeti.DynkinType.ChevalleyDatum.rootSetEquiv`: the coordinate bijection `(S → A) ≃ U`
  associated to an injective and surjective enumeration.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemmas 17, 19, and 22.
* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.3.3 and §7.2.
-/

public section

open Multiplicative

namespace TauCeti.DynkinType.ChevalleyDatum

universe v w

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

/-- Multiply `S`-indexed root parameters in the order of `l`, landing in a point subgroup `U`
containing the root subgroups indexed by `S`. -/
noncomputable def rootSetProduct {S : Set (Fin t.numRoots)} {A : Type v} [CommRing A]
    (U : Subgroup (D.points A)) (hU : ∀ γ ∈ S, ∀ a, D.rootSubgroupPoints γ A a ∈ U)
    (l : List S) (u : S → A) : U :=
  ⟨(l.map fun γ => D.rootSubgroupPoints γ.val A (ofAdd (u γ))).prod,
    Subgroup.list_prod_mem _ fun _ hg => by
      obtain ⟨γ, _, rfl⟩ := List.mem_map.mp hg
      exact hU γ.val γ.property _⟩

/-- The root-set product has the stated ordered factors in the datum point group. -/
@[simp]
theorem coe_rootSetProduct {S : Set (Fin t.numRoots)} {A : Type v} [CommRing A]
    (U : Subgroup (D.points A)) (hU : ∀ γ ∈ S, ∀ a, D.rootSubgroupPoints γ A a ∈ U)
    (l : List S) (u : S → A) :
    (D.rootSetProduct U hU l u : D.points A) =
      (l.map fun γ => D.rootSubgroupPoints γ.val A (ofAdd (u γ))).prod :=
  (rfl)

/-- Changing the value ring applies the ring map to each root coordinate in the ambient group. -/
theorem map_rootSetProduct {S : Set (Fin t.numRoots)}
    {A : Type v} {B : Type w} [CommRing A] [CommRing B]
    (UA : Subgroup (D.points A)) (hUA : ∀ γ ∈ S, ∀ a, D.rootSubgroupPoints γ A a ∈ UA)
    (UB : Subgroup (D.points B)) (hUB : ∀ γ ∈ S, ∀ b, D.rootSubgroupPoints γ B b ∈ UB)
    (l : List S) (f : A →+* B) (u : S → A) :
    (D.pointsPresentation A).map (D.pointsPresentation B) f
        (D.rootSetProduct UA hUA l u : D.points A) =
      (D.rootSetProduct UB hUB l (fun γ => f (u γ)) : D.points B) := by
  simp only [coe_rootSetProduct, map_list_prod, List.map_map, Function.comp_def,
    D.map_rootSubgroupPoints, toAdd_ofAdd]

/-- Evaluating an ordered root-set product at the zero tuple gives the identity point. -/
@[simp]
theorem rootSetProduct_zero {S : Set (Fin t.numRoots)} {A : Type v} [CommRing A]
    (U : Subgroup (D.points A)) (hU : ∀ γ ∈ S, ∀ a, D.rootSubgroupPoints γ A a ∈ U)
    (l : List S) :
    D.rootSetProduct U hU l 0 = 1 := by
  apply Subtype.ext
  rw [coe_rootSetProduct, Subgroup.coe_one]
  exact List.prod_eq_one fun x hx => by
    obtain ⟨γ, _, rfl⟩ := List.mem_map.mp hx
    simp

/-- Evaluating a duplicate-free ordered root-set product on `Pi.single γ a` for `γ ∈ l` recovers the
corresponding root generator. -/
@[simp]
theorem rootSetProduct_single {S : Set (Fin t.numRoots)} {A : Type v} [CommRing A]
    (U : Subgroup (D.points A)) (hU : ∀ γ ∈ S, ∀ a, D.rootSubgroupPoints γ A a ∈ U)
    {l : List S} (hl : l.Nodup) {γ : S} (hγ : γ ∈ l) (a : A) :
    D.rootSetProduct U hU l (Pi.single γ a) =
      ⟨D.rootSubgroupPoints γ.val A (ofAdd a), hU γ.val γ.property _⟩ := by
  apply Subtype.ext
  rw [coe_rootSetProduct, List.prod_map_eq_pow_single γ _ fun η hη _ => by
    simp [Pi.single_eq_of_ne hη]]
  rw [@List.count_eq_one_of_mem _ instBEqOfDecidableEq _ _ _ hl hγ, pow_one, Pi.single_eq_same]

/-- If an additive rational weight functional `degree` is strictly positive on `S`, any
duplicate-free enumeration of `S` defines an injective root-product map over every commutative
ring. -/
theorem rootSetProduct_injective_of_degree_pos {S : Set (Fin t.numRoots)} {A : Type v} [CommRing A]
    (U : Subgroup (D.points A)) (hU : ∀ γ ∈ S, ∀ a, D.rootSubgroupPoints γ A a ∈ U)
    (degree : (Fin t.rank → ℤ) →+ ℚ)
    (hdeg : ∀ γ ∈ S, 0 < degree ((t.simplyConnectedRootDatum ht).root γ))
    (l : List S) (hl : l.Nodup) (hcover : ∀ γ, γ ∈ l) :
    Function.Injective (D.rootSetProduct U hU l) := by
  classical
  intro u v huv
  let extend := fun (w : S → A) (γ : Fin t.numRoots) =>
    if h : γ ∈ S then w ⟨γ, h⟩ else 0
  have heq := congrArg Subtype.val huv
  have hprod (w : S → A) :
      ((l.map Subtype.val).map fun γ => D.rootSubgroupPoints γ A
        (ofAdd (extend w γ))).prod = (D.rootSetProduct U hU l w : D.points A) := by
    simp only [coe_rootSetProduct, List.map_map, Function.comp_def]
    exact congrArg List.prod (List.map_congr_left fun γ _ => by
      simp only [extend, dite_eq_left γ.property])
  have hparams := (D.list_prod_map_rootSubgroupPoints_inj_of_degree_pos A degree
    (hl.map Subtype.val_injective)
    (by rintro γ hγ; obtain ⟨δ, _, rfl⟩ := List.mem_map.mp hγ; exact hdeg δ.val δ.property)).mp
      ((hprod u).trans (heq.trans (hprod v).symm))
  funext γ
  simpa only [extend, dite_eq_left γ.property] using
    hparams γ.val (List.mem_map.mpr ⟨γ, hcover γ, rfl⟩)

/-- If `w` in the pinned Weyl group maps a root set `S'` bijectively onto `S` and `U'` is generated
by the root subgroups in `S'`, surjectivity of `rootSetProduct` on `U` along the `w`-transported
list `l'.map (...)` implies surjectivity of `rootSetProduct` on `U'` along `l'`. -/
theorem rootSetProduct_surjective_of_weylGroup {S S' : Set (Fin t.numRoots)}
    {A : Type v} [CommRing A]
    (U : Subgroup (D.points A)) (hU : ∀ γ ∈ S, ∀ a, D.rootSubgroupPoints γ A a ∈ U)
    (U' : Subgroup (D.points A)) (hU' : ∀ γ ∈ S', ∀ a, D.rootSubgroupPoints γ A a ∈ U')
    (hU'_le : ∀ P : Subgroup (D.points A), (∀ γ ∈ S', ∀ a, D.rootSubgroupPoints γ A a ∈ P) → U' ≤ P)
    (w : (t.simplyConnectedRootDatum ht).weylGroup)
    (hw : ∀ γ, γ ∈ S' ↔ (t.simplyConnectedRootDatum ht).weylGroupToPerm w γ ∈ S)
    (l' : List S')
    (hsurj : Function.Surjective
      (D.rootSetProduct U hU
        (l'.map (((t.simplyConnectedRootDatum ht).weylGroupToPerm w).subtypeEquiv hw)))) :
    Function.Surjective (D.rootSetProduct U' hU' l') := by
  intro g
  let σ := (t.simplyConnectedRootDatum ht).weylGroupToPerm w
  let e : S' ≃ S := σ.subtypeEquiv hw
  obtain ⟨n, ε, hn⟩ := D.exists_conj_rootSubgroupPoints_eq_of_weylGroup w A
  have hconj_mem : MulAut.conj (n : D.points A) (g : D.points A) ∈ U := by
    refine hU'_le (U.comap (MulAut.conj (n : D.points A)).toMonoidHom) (fun γ hγ a => ?_) g.property
    rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, ← ofAdd_toAdd a, hn γ (toAdd a)]
    exact hU (σ γ) ((hw γ).mp hγ) _
  obtain ⟨v, hv⟩ := hsurj ⟨MulAut.conj (n : D.points A) (g : D.points A), hconj_mem⟩
  refine ⟨fun γ => ((((ε γ.val)⁻¹ : ℤˣ) : ℤ) : A) * v (e γ), ?_⟩
  apply Subtype.ext
  apply (MulAut.conj (n : D.points A)).injective
  have hv' : ((l'.map e).map fun δ => D.rootSubgroupPoints δ.val A (ofAdd (v δ))).prod =
      MulAut.conj (n : D.points A) (g : D.points A) := by
    simpa only [coe_rootSetProduct] using congrArg Subtype.val hv
  rw [← hv', coe_rootSetProduct, ← MulEquiv.coe_toMonoidHom, map_list_prod]
  simp only [List.map_map, Function.comp_def, MulEquiv.coe_toMonoidHom]
  refine congrArg List.prod (List.map_congr_left fun γ _ => ?_)
  rw [hn γ.val, ← mul_assoc, ← Int.cast_mul, ← Units.val_mul]
  simp [e, σ]

/-- When `rootSetProduct U hU l` is bijective, membership in `U` is equivalent to a unique ordered
root-product factorization along `l`. -/
theorem mem_iff_existsUnique_rootSetProduct {S : Set (Fin t.numRoots)} {A : Type v} [CommRing A]
    (U : Subgroup (D.points A)) (hU : ∀ γ ∈ S, ∀ a, D.rootSubgroupPoints γ A a ∈ U)
    {l : List S}
    (hinj : Function.Injective (D.rootSetProduct U hU l))
    (hsurj : Function.Surjective (D.rootSetProduct U hU l)) (g : D.points A) :
    g ∈ U ↔
      ∃! u : S → A, (l.map fun γ => D.rootSubgroupPoints γ.val A (ofAdd (u γ))).prod = g := by
  constructor
  · intro hg
    obtain ⟨u, hu⟩ := hsurj ⟨g, hg⟩
    exact ⟨u, congrArg Subtype.val hu, fun v hv =>
      hinj (Subtype.ext (hv.trans (congrArg Subtype.val hu).symm))⟩
  · rintro ⟨u, rfl, _⟩
    exact (D.rootSetProduct U hU l u).property

/-- Coordinate bijection `(S → A) ≃ U` attached to a bijective ordered root-set product. -/
noncomputable def rootSetEquiv {S : Set (Fin t.numRoots)} {A : Type v} [CommRing A]
    (U : Subgroup (D.points A)) (hU : ∀ γ ∈ S, ∀ a, D.rootSubgroupPoints γ A a ∈ U)
    (l : List S)
    (hinj : Function.Injective (D.rootSetProduct U hU l))
    (hsurj : Function.Surjective (D.rootSetProduct U hU l)) :
    (S → A) ≃ U :=
  Equiv.ofBijective (D.rootSetProduct U hU l) ⟨hinj, hsurj⟩

/-- Applying `rootSetEquiv` multiplies the given root parameters in the order of `l`. -/
@[simp]
theorem rootSetEquiv_apply {S : Set (Fin t.numRoots)} {A : Type v} [CommRing A]
    (U : Subgroup (D.points A)) (hU : ∀ γ ∈ S, ∀ a, D.rootSubgroupPoints γ A a ∈ U)
    (l : List S)
    (hinj : Function.Injective (D.rootSetProduct U hU l))
    (hsurj : Function.Surjective (D.rootSetProduct U hU l))
    (u : S → A) :
    D.rootSetEquiv U hU l hinj hsurj u = D.rootSetProduct U hU l u :=
  (rfl)

/-- The identity point in `U` has zero coordinates. -/
@[simp]
theorem rootSetEquiv_symm_one {S : Set (Fin t.numRoots)} {A : Type v} [CommRing A]
    (U : Subgroup (D.points A)) (hU : ∀ γ ∈ S, ∀ a, D.rootSubgroupPoints γ A a ∈ U)
    (l : List S)
    (hinj : Function.Injective (D.rootSetProduct U hU l))
    (hsurj : Function.Surjective (D.rootSetProduct U hU l)) :
    (D.rootSetEquiv U hU l hinj hsurj).symm 1 = 0 := by
  rw [← D.rootSetProduct_zero U hU l, ← D.rootSetEquiv_apply U hU l hinj hsurj 0]
  exact (D.rootSetEquiv U hU l hinj hsurj).symm_apply_apply 0

/-- For a duplicate-free list `l` (`l.Nodup`) containing `γ` (`γ ∈ l`), the single root generator at
`γ` has single-coordinate tuple `Pi.single γ a`. -/
@[simp]
theorem rootSetEquiv_symm_rootSubgroupPoints {S : Set (Fin t.numRoots)} {A : Type v} [CommRing A]
    (U : Subgroup (D.points A)) (hU : ∀ γ ∈ S, ∀ a, D.rootSubgroupPoints γ A a ∈ U)
    {l : List S} (hl : l.Nodup) {γ : S} (hγ : γ ∈ l)
    (hinj : Function.Injective (D.rootSetProduct U hU l))
    (hsurj : Function.Surjective (D.rootSetProduct U hU l)) (a : A) :
    (D.rootSetEquiv U hU l hinj hsurj).symm
        ⟨D.rootSubgroupPoints γ.val A (ofAdd a), hU γ.val γ.property _⟩ =
      Pi.single γ a := by
  rw [← D.rootSetProduct_single U hU hl hγ a, ← D.rootSetEquiv_apply U hU l hinj hsurj]
  exact (D.rootSetEquiv U hU l hinj hsurj).symm_apply_apply _

/-- Extracting coordinates after a subgroup map acting coordinatewise on `rootSetProduct` applies
`f` coordinatewise. -/
theorem rootSetEquiv_symm_map {S : Set (Fin t.numRoots)}
    {A : Type v} {B : Type w} [CommRing A] [CommRing B]
    (UA : Subgroup (D.points A)) (hUA : ∀ γ ∈ S, ∀ a, D.rootSubgroupPoints γ A a ∈ UA)
    (UB : Subgroup (D.points B)) (hUB : ∀ γ ∈ S, ∀ b, D.rootSubgroupPoints γ B b ∈ UB)
    (l : List S) (f : A →+* B) (F : UA →* UB)
    (hF : ∀ u : S → A, F (D.rootSetProduct UA hUA l u) =
      D.rootSetProduct UB hUB l (fun γ => f (u γ)))
    (hinjA : Function.Injective (D.rootSetProduct UA hUA l))
    (hsurjA : Function.Surjective (D.rootSetProduct UA hUA l))
    (hinjB : Function.Injective (D.rootSetProduct UB hUB l))
    (hsurjB : Function.Surjective (D.rootSetProduct UB hUB l))
    (g : UA) :
    (D.rootSetEquiv UB hUB l hinjB hsurjB).symm (F g) =
      fun γ => f ((D.rootSetEquiv UA hUA l hinjA hsurjA).symm g γ) := by
  apply (D.rootSetEquiv UB hUB l hinjB hsurjB).injective
  rw [Equiv.apply_symm_apply, D.rootSetEquiv_apply, ← hF,
    ← D.rootSetEquiv_apply UA hUA l hinjA hsurjA, Equiv.apply_symm_apply]

end TauCeti.DynkinType.ChevalleyDatum
