/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Naturality
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Order
public import TauCeti.Algebra.AlgebraicGroup.LoopGroup.Basic
public import TauCeti.Algebra.AlgebraicGroup.LoopGroup.Jet

/-!
# The preimage in the positive loop group of a closed subgroup

Let `G` be the affine group over a commutative ring `k` with coordinate Hopf algebra `H`, and let
`B ⊆ G` be the closed subgroup cut out by a Hopf ideal `I` of `H`, with points
`B(R) = TauCeti.CommHopfAlgCat.quotientPointsSubgroup H I R`, the points of `G` vanishing on `I`.
For a commutative `k`-algebra `R`, reduction modulo `t` is the homomorphism
`TauCeti.HopfAlgebra.positiveLoopEvalZero : L⁺G(R) = G(R⟦t⟧) → G(R)`, and this file studies the
preimage

  `L⁺G(R) ×_{G(R)} B(R) = {g ∈ L⁺G(R) | g mod t ∈ B(R)}`

of `B(R)`. When `G` is a split reductive group over a field and `B` a Borel subgroup, it is the
Iwahori subgroup of `L⁺G`, the group whose orbits on the affine flag variety are the Schubert
cells; for a parabolic subgroup it is the corresponding parahoric subgroup.

The preimage is a group functor of `R` on all commutative `k`-algebras, nonreduced ones included,
and a subfunctor of `L⁺G`. It contains the first congruence subgroup `K_1(R)`, the kernel of
reduction modulo `t`, as a normal subgroup, it contains the constant loops of `B`, and reduction
modulo `t` identifies its quotient by `K_1(R)` with `B(R)`, naturally in `R`. For `B = G` it is
all of `L⁺G(R)`, and for the trivial subgroup it is `K_1(R)`. The case of the upper triangular
subgroup of `GL_n` is in `TauCeti.Algebra.AlgebraicGroup.GeneralLinear.UpperTriangular.Iwahori`.

## Main definitions

* `TauCeti.HopfAlgebra.positiveLoopPreimage H I R`: the preimage of `B(R)` in `L⁺G(R)`.
* `TauCeti.HopfAlgebra.positiveLoopPreimageEvalZero H I R`: reduction modulo `t`, as a surjective
  homomorphism from the preimage onto `B(R)` with kernel `K_1(R)`.
* `TauCeti.HopfAlgebra.positiveLoopPreimageQuotientMulEquiv H I R`: the isomorphism of the
  quotient of the preimage by `K_1(R)` with `B(R)`.
* `TauCeti.HopfAlgebra.positiveLoopPreimageGroup H I`: the preimage as a functor
  `CommAlgCat k ⥤ GrpCat`, with its inclusion `positiveLoopPreimageIncl` into `L⁺G` and the
  natural reduction `positiveLoopPreimageReduction` onto the functor of points of `B`.

## Main results

* `TauCeti.HopfAlgebra.mem_positiveLoopPreimage_iff`: a positive loop lies in the preimage exactly
  when the constant coefficient of its value at every element of `I` vanishes.
* `TauCeti.HopfAlgebra.congruenceSubgroup_span_X_le_positiveLoopPreimage`: `K_1(R)` lies in the
  preimage; it is normal there by the instance `Subgroup.normal_subgroupOf`.
* `TauCeti.HopfAlgebra.constantPositiveLoop_mem_positiveLoopPreimage`: the constant loops of `B`
  lie in the preimage.
* `TauCeti.HopfAlgebra.ker_positiveLoopPreimageEvalZero` and
  `TauCeti.HopfAlgebra.positiveLoopPreimageEvalZero_surjective`: the reduction onto `B(R)` is
  surjective with kernel `K_1(R)`.
* `TauCeti.HopfAlgebra.positiveLoopPreimage_bot` and
  `TauCeti.HopfAlgebra.positiveLoopPreimage_augmentation`: the preimages of `G` and of the trivial
  subgroup are `L⁺G(R)` and `K_1(R)`.

## References

* G. Pappas, M. Rapoport, *Twisted loop groups and their affine flag varieties*, Adv. Math. 219
  (2008), §1.b and §8.
* X. Zhu, *An introduction to affine Grassmannians and the geometric Satake equivalence*, in
  *Geometry of moduli spaces and representation theory*, IAS/Park City Math. Ser. 24 (2017),
  §1.4.
-/

public section

open CategoryTheory WithConv PowerSeries

universe u v w w'

namespace TauCeti.HopfAlgebra

variable {k : Type u} [CommRing k] (H : _root_.CommHopfAlgCat.{v} k) (I : HopfIdeal k H)

section Subgroup

variable (R : Type w) [CommRing R] [Algebra k R]

/-- **The preimage of a closed subgroup in the positive loop group.** For the closed subgroup `B`
of `G` cut out by the Hopf ideal `I`, the subgroup of the positive loops `g ∈ L⁺G(R) = G(R⟦t⟧)`
whose reduction `g mod t ∈ G(R)` lies in `B(R)`. For a Borel subgroup `B` of a reductive group
this is the Iwahori subgroup. -/
noncomputable def positiveLoopPreimage : Subgroup (WithConv (H →ₐ[k] R⟦X⟧)) :=
  (CommHopfAlgCat.quotientPointsSubgroup H I (CommAlgCat.of k R)).comap
    (positiveLoopEvalZero k H R)

variable {H I R}

/-- A positive loop lies in the preimage of `B(R)` exactly when its reduction modulo `t` lies in
`B(R)`. -/
theorem mem_positiveLoopPreimage {g : WithConv (H →ₐ[k] R⟦X⟧)} :
    g ∈ positiveLoopPreimage H I R ↔
      positiveLoopEvalZero k H R g ∈
        CommHopfAlgCat.quotientPointsSubgroup H I (CommAlgCat.of k R) :=
  Iff.rfl

/-- A positive loop lies in the preimage of `B(R)` exactly when its values at the elements of
the Hopf ideal `I` have vanishing constant coefficient. -/
@[simp]
theorem mem_positiveLoopPreimage_iff {g : WithConv (H →ₐ[k] R⟦X⟧)} :
    g ∈ positiveLoopPreimage H I R ↔ ∀ h ∈ I, constantCoeff (g.ofConv h) = 0 := by
  rw [mem_positiveLoopPreimage, CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
  exact forall₂_congr fun h _ ↦ by rw [ofConv_positiveLoopEvalZero_apply]

variable (H I R)

/-- **The congruence subgroup `K_1(R)` lies in the preimage of `B(R)`**: a positive loop that
reduces to the identity modulo `t` reduces into `B(R)`. It is a normal subgroup of the preimage,
by the instance `Subgroup.normal_subgroupOf`, being normal in `L⁺G(R)`. -/
theorem congruenceSubgroup_span_X_le_positiveLoopPreimage :
    congruenceSubgroup k H (Ideal.span {(X : R⟦X⟧)}) ≤ positiveLoopPreimage H I R := by
  intro g hg
  rw [← ker_positiveLoopEvalZero, MonoidHom.mem_ker] at hg
  rw [mem_positiveLoopPreimage, hg]
  exact one_mem _

variable {H I R} in
/-- **The constant loops of `B` lie in the preimage of `B(R)`.** -/
theorem constantPositiveLoop_mem_positiveLoopPreimage {b : WithConv (H →ₐ[k] R)}
    (hb : b ∈ CommHopfAlgCat.quotientPointsSubgroup H I (CommAlgCat.of k R)) :
    constantPositiveLoop k H R b ∈ positiveLoopPreimage H I R := by
  rwa [mem_positiveLoopPreimage, positiveLoopEvalZero_constantPositiveLoop]

/-- The preimage of `G(R)` itself, cut out by the zero Hopf ideal, is all of `L⁺G(R)`. -/
@[simp]
theorem positiveLoopPreimage_bot : positiveLoopPreimage H ⊥ R = ⊤ := by
  rw [positiveLoopPreimage, CommHopfAlgCat.quotientPointsSubgroup_bot, Subgroup.comap_top]

/-- The preimage of the trivial subgroup, cut out by the augmentation ideal, is the congruence
subgroup `K_1(R)`. -/
theorem positiveLoopPreimage_augmentation :
    positiveLoopPreimage H (HopfIdeal.augmentation k H) R =
      congruenceSubgroup k H (Ideal.span {(X : R⟦X⟧)}) := by
  ext g
  rw [mem_positiveLoopPreimage, CommHopfAlgCat.mem_quotientPointsSubgroup_augmentation_iff,
    ← ker_positiveLoopEvalZero, MonoidHom.mem_ker]

/-- The preimage of `B(R)` is antitone in the Hopf ideal: a larger Hopf ideal cuts out a smaller
closed subgroup, with a smaller preimage. -/
theorem positiveLoopPreimage_antitone :
    Antitone fun I : HopfIdeal k H ↦ positiveLoopPreimage H I R :=
  fun _ _ hIJ ↦ Subgroup.comap_mono
    (CommHopfAlgCat.quotientPointsSubgroup_antitone H (CommAlgCat.of k R) hIJ)

/-- **Reduction modulo `t` on the preimage of `B(R)`**, the homomorphism onto `B(R)`
restricting `positiveLoopEvalZero`. It is surjective
(`positiveLoopPreimageEvalZero_surjective`) with kernel `K_1(R)`
(`ker_positiveLoopPreimageEvalZero`). -/
noncomputable def positiveLoopPreimageEvalZero :
    positiveLoopPreimage H I R →*
      CommHopfAlgCat.quotientPointsSubgroup H I (CommAlgCat.of k R) :=
  (positiveLoopEvalZero k H R).subgroupComap _

variable {H I R} in
/-- The reduction of an element of the preimage is its reduction as a positive loop. -/
@[simp]
theorem coe_positiveLoopPreimageEvalZero_apply (g : positiveLoopPreimage H I R) :
    (positiveLoopPreimageEvalZero H I R g : WithConv (H →ₐ[k] R)) =
      positiveLoopEvalZero k H R g :=
  (rfl)

/-- Reduction modulo `t` maps the preimage of `B(R)` onto `B(R)`: the constant loops are a
section. -/
theorem positiveLoopPreimageEvalZero_surjective :
    Function.Surjective (positiveLoopPreimageEvalZero H I R) := fun b ↦
  ⟨⟨constantPositiveLoop k H R b, constantPositiveLoop_mem_positiveLoopPreimage b.property⟩,
    Subtype.ext (positiveLoopEvalZero_constantPositiveLoop _)⟩

/-- The kernel of reduction modulo `t` on the preimage of `B(R)` is the congruence subgroup
`K_1(R)`. -/
theorem ker_positiveLoopPreimageEvalZero :
    (positiveLoopPreimageEvalZero H I R).ker =
      (congruenceSubgroup k H (Ideal.span {(X : R⟦X⟧)})).subgroupOf
        (positiveLoopPreimage H I R) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← ker_positiveLoopEvalZero, MonoidHom.mem_ker,
    ← coe_positiveLoopPreimageEvalZero_apply, OneMemClass.coe_eq_one]

/-- **The preimage of `B(R)` modulo `K_1(R)` is `B(R)`**, through reduction modulo `t`. -/
noncomputable def positiveLoopPreimageQuotientMulEquiv :
    positiveLoopPreimage H I R ⧸
        (congruenceSubgroup k H (Ideal.span {(X : R⟦X⟧)})).subgroupOf
          (positiveLoopPreimage H I R) ≃*
      CommHopfAlgCat.quotientPointsSubgroup H I (CommAlgCat.of k R) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_positiveLoopPreimageEvalZero H I R).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (positiveLoopPreimageEvalZero_surjective H I R))

variable {H I R} in
/-- The class of an element of the preimage modulo `K_1(R)` corresponds to its reduction modulo
`t`. -/
@[simp]
theorem positiveLoopPreimageQuotientMulEquiv_mk (g : positiveLoopPreimage H I R) :
    positiveLoopPreimageQuotientMulEquiv H I R (QuotientGroup.mk g) =
      positiveLoopPreimageEvalZero H I R g :=
  (rfl)

/-- `K_1(R)` is a normal subgroup of the preimage of `B(R)`. -/
example : ((congruenceSubgroup k H (Ideal.span {(X : R⟦X⟧)})).subgroupOf
    (positiveLoopPreimage H I R)).Normal :=
  inferInstance

end Subgroup

section Functor

variable {H I} {R : Type w} [CommRing R] [Algebra k R] {S : Type w'} [CommRing S] [Algebra k S]

/-- A coefficient map `φ : R →ₐ[k] S` carries the preimage of `B(R)` into the preimage of
`B(S)`. -/
theorem mapValue_mem_positiveLoopPreimage (φ : R →ₐ[k] S) {g : WithConv (H →ₐ[k] R⟦X⟧)}
    (hg : g ∈ positiveLoopPreimage H I R) :
    AlgHom.mapValue (PowerSeries.mapAlgHom φ) g ∈ positiveLoopPreimage H I S := by
  rw [mem_positiveLoopPreimage, positiveLoopEvalZero_naturality]
  exact CommHopfAlgCat.mapValue_mem_quotientPointsSubgroup H I φ hg

variable (H I)

/-- **The preimage of `B` in `L⁺G` as a group functor**: `R ↦ positiveLoopPreimage H I R` on
commutative `k`-algebras, a morphism acting on the coefficients of the values of a positive
loop. It is a subfunctor of `L⁺G` (`positiveLoopPreimageIncl`) and reduces naturally onto the
functor of points of `B` (`positiveLoopPreimageReduction`). -/
@[expose] noncomputable def positiveLoopPreimageGroup :
    CommAlgCat.{w} k ⥤ GrpCat.{max v w} where
  obj R := GrpCat.of (positiveLoopPreimage H I R)
  map {R S} f := GrpCat.ofHom
    (((AlgHom.mapValue (H := H) (PowerSeries.mapAlgHom f.hom)).domRestrict
      (positiveLoopPreimage H I R)).codRestrict (positiveLoopPreimage H I S)
      fun g ↦ mapValue_mem_positiveLoopPreimage f.hom g.property)
  -- The action on the preimage is the action of `L⁺G` (`positiveLoopGroup_map_apply`), so the
  -- functor laws are those of `L⁺G`.
  map_id R := GrpCat.ext fun g ↦ Subtype.ext <|
    congrArg (fun φ ↦ φ.hom g.val) ((positiveLoopGroup k H).map_id R)
  map_comp f g := GrpCat.ext fun x ↦ Subtype.ext <|
    congrArg (fun φ ↦ φ.hom x.val) ((positiveLoopGroup k H).map_comp f g)

/-- The group `positiveLoopPreimageGroup H I` at `R` is the preimage of `B(R)`. -/
lemma positiveLoopPreimageGroup_obj (R : CommAlgCat.{w} k) :
    (positiveLoopPreimageGroup H I).obj R = GrpCat.of (positiveLoopPreimage H I R) :=
  (rfl)

variable {H I} in
/-- A morphism `f : R ⟶ S` acts on the preimage by applying `f` to the coefficients of the values
of a positive loop. -/
@[simp]
lemma positiveLoopPreimageGroup_map_apply {R S : CommAlgCat.{w} k} (f : R ⟶ S)
    (g : (positiveLoopPreimageGroup H I).obj R) :
    Subtype.val ((positiveLoopPreimageGroup H I).map f g) =
      AlgHom.mapValue (PowerSeries.mapAlgHom f.hom) (Subtype.val g) :=
  (rfl)

/-- The natural inclusion of the preimage of `B` into `L⁺G`. -/
noncomputable def positiveLoopPreimageIncl :
    positiveLoopPreimageGroup.{u, v, w} H I ⟶ positiveLoopGroup k H where
  app _ := GrpCat.ofHom (Subgroup.subtype _)
  naturality _ _ _ := rfl

/-- The component of `positiveLoopPreimageIncl` at `R` is the subgroup inclusion. -/
@[simp]
lemma positiveLoopPreimageIncl_app (R : CommAlgCat.{w} k) :
    (positiveLoopPreimageIncl H I).app R =
      GrpCat.ofHom (positiveLoopPreimage H I R).subtype :=
  (rfl)

/-- **Reduction modulo `t`, naturally in `R`**: the natural transformation from the preimage of
`B` in `L⁺G` onto the functor of points of `B`, with components `positiveLoopPreimageEvalZero`,
each surjective with kernel `K_1(R)`. -/
noncomputable def positiveLoopPreimageReduction :
    positiveLoopPreimageGroup.{u, v, w} H I ⟶
      CommHopfAlgCat.quotientPointsSubgroupFunctor H I where
  app R := GrpCat.ofHom (positiveLoopPreimageEvalZero H I R)
  naturality _ _ f := GrpCat.ext fun g ↦ Subtype.ext <|
    positiveLoopEvalZero_naturality f.hom g.val

/-- The component of `positiveLoopPreimageReduction` at `R` is reduction modulo `t`. -/
@[simp]
lemma positiveLoopPreimageReduction_app (R : CommAlgCat.{w} k) :
    (positiveLoopPreimageReduction H I).app R =
      GrpCat.ofHom (positiveLoopPreimageEvalZero H I R) :=
  (rfl)

end Functor

end TauCeti.HopfAlgebra
