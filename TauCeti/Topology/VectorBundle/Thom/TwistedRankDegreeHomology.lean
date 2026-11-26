/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.MayerVietoris.Twisted
public import TauCeti.Topology.VectorBundle.Orientation.ThomClass
public import TauCeti.Topology.VectorBundle.Thom.Sign.LocalSystem
import TauCeti.Algebra.Category.ModuleCat.SpanSingleton
import TauCeti.AlgebraicTopology.Singular.Twisted.Coefficients
import TauCeti.AlgebraicTopology.Singular.Twisted.ConstantNaturality
import TauCeti.Topology.Category.TopCat.Limits.Basic
import TauCeti.Topology.VectorBundle.MayerVietoris.DirectedUnion
import TauCeti.Topology.VectorBundle.MayerVietoris.TwistedDirectedUnion
import TauCeti.Topology.VectorBundle.Thom.RankDegreeHomology
import TauCeti.Topology.VectorBundle.Thom.Sign.Restriction

/-!
# The Thom pair in the rank degree with coefficients in the orientation system

Let `E → B` be a real vector bundle of rank `r` with Thom pair `(E, E₀)`, `E₀` the complement of
the zero section, let `R` be a ring, and let `o(E)` be the orientation local system of `E`
(`TauCeti.VectorBundleOrientationCover.signLocalSystem`), whose fibre over `b` is a copy of `R`
with the two orientations of `E_b` as generators. Pull it back to the total space along the
projection `π`: `π^*o(E)` (`TauCeti.thomPairSignLocalSystem`). This file computes the first
homology group of the Thom pair with these coefficients that can be nonzero,

`Hᵣ(E, E₀; π^*o(E)) ≅ H₀(B; R)`,

over an arbitrary base and without any orientation of `E`
(`TauCeti.thomPairTwistedHomologyFinrankIso`). The twist cancels: on the fibre over `b` the
coefficients are the constant module `o(E)_b`, and the class of the fibre pair `(E_b, E_b ∖ {0})`
read through a linear trivialization, tensored with the orientation of `E_b` read by the same
trivialization, does not change when both readings are reversed. So these classes, the fibre
classes `TauCeti.thomPairSignFiberClass`, are canonical up to the choice of an orientation `ω` of
the model fibre, and the isomorphism sends the fibre class over `b` to the class of the point `b`
(`TauCeti.thomPairTwistedHomologyFinrankIso_hom_thomPairSignFiberClass`). Without twisted
coefficients, `TauCeti.thomPairSingularHomologyFinrankIso` and its oriented variant
`TauCeti.VectorBundleOrientation.thomPairSingularHomologyFinrankIso` identify `Hᵣ(E, E₀; K)` with
`H₀(B; K)` when `1` is the only unit of the commutative ring `K`, or for an oriented bundle.

This is the bottom degree of the Thom isomorphism with coefficients twisted by the orientation
system: by universal coefficients, a homomorphism `Hᵣ(E, E₀; π^*o(E)) ⟶ R` taking the value `1` on
every fibre class is a twisted Thom class of `E`.

## The proof

The proof follows the computation of `Hᵣ(E, E₀; R) ≅ H₀(B; R)` for oriented bundles in
`TauCeti.Topology.VectorBundle.Thom.RankDegreeHomology`, and shares with it the point class
`TauCeti.complZeroPairPointHom` of `Hᵣ(F, F ∖ {0}; R)` and the Mayer–Vietoris induction
`TauCeti.isIso_biUnion_of_mayerVietoris`. The map `H₀(W; R) ⟶ Hᵣ(E|_W, E₀|_W; π^*o(E))`
(`TauCeti.thomPairOverTwistedHomologyFinrankInv`) sends the class of a point to the fibre class
over it (`TauCeti.thomPairOverSignFiberClass`); it is well defined because the fibre classes are
constant along paths (`TauCeti.thomPairOverSignFiberClass_eq_of_path`). Every linear trivialization
at `x` reads the fibre class over `x` the same way (`TauCeti.thomPairOverSignFiberClass_eq`): if it
reads the orientations of `E_x` oppositely, both the generator of the fibre pair and the
trivialization of the coefficients change sign. Over a subset `W` of the base set of a linear
trivialization, the orientations of the fibres read by the trivialization trivialize `π^*o(E)` over
`E|_W`, identifying `Hᵣ(E|_W, E₀|_W; π^*o(E))` with the untwisted rank-degree homology
`Hᵣ(W × F, W × (F ∖ {0}); R)` of the product Thom pair, and hence with `H₀(W; R)`, carrying fibre
classes to classes of points. The Mayer–Vietoris sequence of Thom pairs with local coefficients
(`TauCeti.thomPairOverTwistedMayerVietoris_exact₂`) ends in degree `r`, since the twisted homology
of the Thom pair vanishes below the rank, so the map is an isomorphism over every finite union of
trivializing open sets (`TauCeti.isIso_thomPairOverTwistedHomologyFinrankInv_biUnion`). Following
the untwisted filtered-colimit gluing in `TauCeti.isIso_of_isColimit_biUnion_baseSet`, both
`H₀(B; R)` and `Hᵣ(E, E₀; π^*o(E))` are the filtered colimits of the corresponding groups over the
finite unions of the chosen trivializing open sets
(`TauCeti.isColimitThomPairFiniteTrivializingUnionTwistedHomologyCocone`), giving the isomorphism
over an arbitrary base.

## Main definitions and results

The orientation local system on the total space (`TauCeti.thomPairSignLocalSystem`), its fibre
trivialization (`TauCeti.fiberThomPairSignLocalSystemIso`), and the all-degree fibre map
(`TauCeti.thomPairSignFiberMap`) are defined in
`TauCeti.Topology.VectorBundle.Thom.Sign.LocalSystem`, and its restrictions and local
trivializations over subsets of the base in
`TauCeti.Topology.VectorBundle.Thom.Sign.Restriction`.

* `TauCeti.thomPairOverSignFiberClass` and `TauCeti.thomPairSignFiberClass`: the fibre classes over
  a point in `(E|_W, E₀|_W)` and in `(E, E₀)`; replacing `ω` by `-ω` negates them
  (`TauCeti.thomPairOverSignFiberClass_neg`, `TauCeti.thomPairSignFiberClass_neg`), and inclusions
  `W ⊆ W'` carry fibre classes to fibre classes
  (`TauCeti.thomPairOverTwistedHomologyMap_thomPairOverSignFiberClass`).
* `TauCeti.thomPairOverSignFiberClass_eq`: every linear trivialization at `x` reads the fibre class
  over `x` as the generator of the fibre pair.
* `TauCeti.thomPairSignFiberClass_eq_thomPairSignFiberMap`: for every orientation `o` of `E_b`, the
  fibre class over `b` is the image under `TauCeti.thomPairSignFiberMap` of the generator of
  `Hᵣ(E_b, E_b ∖ {0}; R)` attached to `o` (`TauCeti.orientedFiberGenerator`).
* `TauCeti.thomPairOverTwistedHomologyFinrankInv` and
  `TauCeti.thomPairOverTwistedHomologyFinrankInv_naturality`: the natural map
  `H₀(W; R) ⟶ Hᵣ(E|_W, E₀|_W; π^*o(E))` sending point classes to fibre classes.
* `TauCeti.isIso_thomPairOverTwistedHomologyFinrankInv_biUnion`:
  `H₀(W; R) ≅ Hᵣ(E|_W, E₀|_W; π^*o(E))` for a finite union `W` of trivializing open sets.
* `TauCeti.thomPairTwistedHomologyFinrankIso`: `Hᵣ(E, E₀; π^*o(E)) ≅ H₀(B; R)` over an arbitrary
  base.
* `TauCeti.thomPairTwistedHomologyFinrankIso_hom_thomPairSignFiberClass`: it sends the fibre class
  over `b` to the class of `b`.
* `TauCeti.thomPairTwistedHomology_hom_ext`: morphisms out of `Hᵣ(E, E₀; π^*o(E))` are determined
  by their values on the fibre classes.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10, Lemma 10.3 and the proof of Theorem 10.4 (the induction over finite unions
  of trivializing open sets and directed unions of chains), and §12 (the orientation double cover
  and twisted coefficients).
* A. Hatcher, *Algebraic Topology*, Section 3.H (local coefficients and the orientation system)
  and Section 4.D, Theorem 4D.10 and its proof.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Bundle Module Set Topology

universe w

namespace TauCeti

variable {B : Type w} [TopologicalSpace B] {F : Type w}
  [NormedAddCommGroup F] [NormedSpace ℝ F] {E : B → Type w}
  [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)]
  [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E] {ι : Type} [Fintype ι]
  {R : Type w} [Ring R] (hι : Fintype.card ι = finrank ℝ F)

/-! ### Fibre classes over subsets of the base -/

section FiberClass

variable [FiniteDimensional ℝ F] (ω : Orientation ℝ F ι)

variable (R) in
/-- The fibre class over `x ∈ W` in `Hᵣ(E|_W, E₀|_W; π^*o(E))`, read through a linear trivialization
`e` at `x`: the image of the class of the fibre pair `(E_x, E_x ∖ {0})` which `e` reads as the
point class of `1` in `Hᵣ(F, F ∖ {0}; R)`, with the coefficients `o(E)_x` trivialized by the
orientation of `E_x` which `e` reads as `ω`. It does not depend on `e`
(`TauCeti.thomPairOverSignFiberClassOf_eq`). -/
def thomPairOverSignFiberClassOf (e : Trivialization F (π F E)) [e.IsLinear ℝ] {x : B}
    (hx : x ∈ e.baseSet) {W : Set B} (hxW : x ∈ W) :
    (thomPairOver F E W).twistedHomology (thomPairOverSignLocalSystem F E R hι W) (finrank ℝ F) :=
  TopPair.twistedHomologyMap (fiberThomPairOverMap F E hxW) (thomPairOverSignLocalSystem F E R hι W)
    (finrank ℝ F)
    ((TopPair.ofSubset (X := TopCat.of (E x)) ({0}ᶜ : Set (E x))).twistedHomologyCoefficientMap
      (fiberThomPairOverSignLocalSystemIso F E R hι hxW ((e.mapOrientation ι hx).symm ω)).inv
      (finrank ℝ F)
      (((TopPair.ofSubset (X := TopCat.of (E x)) ({0}ᶜ : Set (E x))).twistedHomologyConstantIso
        (ModuleCat.of R R) (finrank ℝ F)).inv
        (TopPair.singularHomologyMap (e.continuousLinearEquivAt ℝ x hx).complZeroPairIso.inv
          (ModuleCat.of R R) (finrank ℝ F)
          (complZeroPairPointHom (ModuleCat.of R R) F (finrank ℝ F) rfl (1 : R)))))

/-- Over a subset `W` of the base set of a linear trivialization `e`, the trivialization identifies
`Hᵣ(E|_W, E₀|_W; π^*o(E))` with `H₀(W; R)`. -/
private def localIso (e : Trivialization F (π F E)) [e.IsLinear ℝ] {W : Set B}
    (hW : W ⊆ e.baseSet) :
    (thomPairOver F E W).twistedHomology (thomPairOverSignLocalSystem F E R hι W) (finrank ℝ F) ≅
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} R) 0).obj
        (ModuleCat.of R R)).obj (TopCat.of W) :=
  (thomPairOver F E W).twistedHomologyCoefficientIso
      (thomPairOverSignLocalSystemIso F E R hι e hW ω) (finrank ℝ F) ≪≫
    (thomPairOver F E W).twistedHomologyConstantIso (ModuleCat.of R R) (finrank ℝ F) ≪≫
    asIso (TopPair.singularHomologyMap (e.thomPairOverIso ℝ hW).hom
      (ModuleCat.of R R) (finrank ℝ F)) ≪≫
    prodThomPairSingularHomologyIso (ModuleCat.of R R) W F 0 (finrank ℝ F)

private theorem localIso_hom (e : Trivialization F (π F E)) [e.IsLinear ℝ] {W : Set B}
    (hW : W ⊆ e.baseSet) :
    (localIso (R := R) hι ω e hW).hom =
      (thomPairOver F E W).twistedHomologyCoefficientMap
          (thomPairOverSignLocalSystemIso F E R hι e hW ω).hom (finrank ℝ F) ≫
        ((thomPairOver F E W).twistedHomologyConstantIso (ModuleCat.of R R) (finrank ℝ F)).hom ≫
        TopPair.singularHomologyMap (e.thomPairOverIso ℝ hW).hom
          (ModuleCat.of R R) (finrank ℝ F) ≫
        (prodThomPairSingularHomologyIso (ModuleCat.of R R) W F 0 (finrank ℝ F)).hom := by
  simp only [localIso, Iso.trans_hom, TopPair.twistedHomologyCoefficientIso_hom, asIso_hom]

/-- Through a linear trivialization `e`, the fibre class over `x ∈ W` read through that
trivialization is the class of the point `x`. -/
private theorem localIso_hom_thomPairOverSignFiberClassOf (e : Trivialization F (π F E))
    [e.IsLinear ℝ] {W : Set B} (hW : W ⊆ e.baseSet) {x : B} (hxW : x ∈ W) :
    (localIso hι ω e hW).hom (thomPairOverSignFiberClassOf R hι ω e (hW hxW) hxW) =
      singularHomology₀Section (ModuleCat.of R R) (X := TopCat.of W) ⟨x, hxW⟩ 1 := by
  have h := ConcreteCategory.congr_hom
    (fiberThomPairOverSign_comp_twistedHomologyMap_comp_iso_assoc (R := R) hι e hW ω hxW
      (finrank ℝ F)
      (TopPair.singularHomologyMap (e.thomPairOverIso ℝ hW).hom
          (ModuleCat.of R R) (finrank ℝ F) ≫
        (prodThomPairSingularHomologyIso (ModuleCat.of R R) W F 0 (finrank ℝ F)).hom))
    (TopPair.singularHomologyMap (e.continuousLinearEquivAt
      ℝ x (hW hxW)).complZeroPairIso.inv (ModuleCat.of R R) (finrank ℝ F)
      (complZeroPairPointHom (ModuleCat.of R R) F (finrank ℝ F) rfl (1 : R)))
  rw [localIso_hom, thomPairOverSignFiberClassOf]
  simp only [ConcreteCategory.comp_apply] at h ⊢
  rw [h, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    ← TopPair.singularHomologyMap_comp_assoc,
    Trivialization.fiberThomPairOverMap_comp_thomPairOverIso_hom, ← ConcreteCategory.comp_apply,
    ← TopPair.singularHomologyMap_comp_assoc, Iso.inv_hom_id_assoc, ConcreteCategory.comp_apply,
    singularHomologyMap_prodThomPairFiberMap_complZeroPairPointHom_one, Iso.inv_hom_id_apply]

/-- **The fibre class does not depend on the linear trivialization through which it is read**: two
trivializations reading the fibre orientation alike read the generator alike, and reading it
oppositely negates both the generator and the trivialization of the coefficients. -/
theorem thomPairOverSignFiberClassOf_eq (e e' : Trivialization F (π F E)) [e.IsLinear ℝ]
    [e'.IsLinear ℝ] {x : B} (hx : x ∈ e.baseSet) (hx' : x ∈ e'.baseSet) {W : Set B}
    (hxW : x ∈ W) :
    thomPairOverSignFiberClassOf R hι ω e hx hxW =
      thomPairOverSignFiberClassOf R hι ω e' hx' hxW := by
  set o := (e.mapOrientation ι hx).symm ω
  have ho : e.mapOrientation ι hx o = ω := Equiv.apply_symm_apply _ ω
  rcases (e'.mapOrientation ι hx' o).eq_or_eq_neg ω (Nat.card_eq_fintype_card.trans hι) with h | h
  · have h' : (e'.mapOrientation ι hx').symm ω = o := (Equiv.symm_apply_eq _).2 h.symm
    have hinv := e.singularHomologyMap_complZeroPairIso_inv_eq_of_mapOrientation_eq e' hx hx' hι
      (ModuleCat.of R R) (h.trans ho.symm) (finrank ℝ F)
    rw [thomPairOverSignFiberClassOf, thomPairOverSignFiberClassOf, h', hinv]
  · have h' : (e'.mapOrientation ι hx').symm ω = -o := e'.mapOrientation_symm_eq_neg_of_eq_neg hx' h
    have hinv := e.singularHomologyMap_complZeroPairIso_inv_eq_neg_of_mapOrientation_eq_neg e' hx
      hx' hι (ModuleCat.of R R) (h.trans (congrArg Neg.neg ho.symm)) (finrank ℝ F)
    rw [thomPairOverSignFiberClassOf, thomPairOverSignFiberClassOf, h', hinv,
      fiberThomPairOverSignLocalSystemIso_neg_inv, TopPair.twistedHomologyCoefficientMap_neg]
    simp only [ModuleCat.hom_neg, LinearMap.neg_apply, map_neg, neg_neg, o]

/-- Restriction carries fibre classes to fibre classes (stated for a chosen linear trivialization).
-/
private theorem thomPairOverTwistedHomologyMap_thomPairOverSignFiberClassOf
    (e : Trivialization F (π F E)) [e.IsLinear ℝ] {x : B} (hx : x ∈ e.baseSet) {W W' : Set B}
    (h : W ⊆ W') (hxW : x ∈ W) :
    thomPairOverTwistedHomologyMap (thomPairSignLocalSystem F E R hι) h (finrank ℝ F)
        (thomPairOverSignFiberClassOf R hι ω e hx hxW) =
      thomPairOverSignFiberClassOf R hι ω e hx (h hxW) := by
  have hmap :
      (TopPair.ofSubset (X := TopCat.of (E x)) ({0}ᶜ : Set (E x))).twistedHomologyCoefficientMap
          (fiberThomPairOverSignLocalSystemIso F E R hι hxW
            ((e.mapOrientation ι hx).symm ω)).inv (finrank ℝ F) ≫
        TopPair.twistedHomologyMap (fiberThomPairOverMap F E hxW)
          (thomPairOverSignLocalSystem F E R hι W) (finrank ℝ F) ≫
        thomPairOverTwistedHomologyMap (thomPairSignLocalSystem F E R hι) h (finrank ℝ F) =
      (TopPair.ofSubset (X := TopCat.of (E x)) ({0}ᶜ : Set (E x))).twistedHomologyCoefficientMap
          (fiberThomPairOverSignLocalSystemIso F E R hι (h hxW)
            ((e.mapOrientation ι hx).symm ω)).inv (finrank ℝ F) ≫
        TopPair.twistedHomologyMap (fiberThomPairOverMap F E (h hxW))
          (thomPairOverSignLocalSystem F E R hι W') (finrank ℝ F) := by
    rw [thomPairOverTwistedHomologyMap_eq]
    -- `erw`: `(thomPairOver F E W).fst` is `TopCat.of ↥(π F E ⁻¹' W)` after unfolding.
    erw [TopPair.twistedHomologyMap_naturality_assoc,
      TopPair.twistedHomologyMap_comp_of_comp_eq (fiberThomPairOverMap F E hxW)
        (thomPairOverMap F E h) (thomPairOverSignLocalSystem F E R hι W')
        (fiberThomPairOverMap_comp_thomPairOverMap F E h hxW)]
    rw [← TopPair.twistedHomologyCoefficientMap_comp_assoc,
      ← TopPair.twistedHomologyCoefficientMap_comp_assoc]
    congr 2
    exact fiberThomPairOverSignLocalSystemIso_inv_comp_thomPairOverMap hι h hxW _
  simpa only [thomPairOverSignFiberClassOf, ConcreteCategory.comp_apply] using
    ConcreteCategory.congr_hom hmap
      (((TopPair.ofSubset (X := TopCat.of (E x)) ({0}ᶜ : Set (E x))).twistedHomologyConstantIso
        (ModuleCat.of R R) (finrank ℝ F)).inv
        (TopPair.singularHomologyMap (e.continuousLinearEquivAt ℝ x hx).complZeroPairIso.inv
          (ModuleCat.of R R) (finrank ℝ F)
          (complZeroPairPointHom (ModuleCat.of R R) F (finrank ℝ F) rfl 1)))

variable (F E R) in
/-- The fibre class over `x ∈ W` in `Hᵣ(E|_W, E₀|_W; π^*o(E))`: the image of the generator of the
fibre pair over `x`, read through the chosen trivialization at `x`, with coefficients trivialized by
the orientation that this trivialization reads as `ω`. Every linear trivialization at `x` reads it
the same way (`TauCeti.thomPairOverSignFiberClass_eq`). -/
def thomPairOverSignFiberClass {W : Set B} {x : B} (hxW : x ∈ W) :
    (thomPairOver F E W).twistedHomology (thomPairOverSignLocalSystem F E R hι W) (finrank ℝ F) :=
  thomPairOverSignFiberClassOf R hι ω (trivializationAt F E x)
    (FiberBundle.mem_baseSet_trivializationAt' x) hxW

/-- **Canonicity of the fibre class**: every linear trivialization `e` at `x` reads the fibre class
over `x` as the generator of the fibre pair, with the coefficients trivialized by the orientation
which `e` reads as `ω`. -/
theorem thomPairOverSignFiberClass_eq (e : Trivialization F (π F E)) [e.IsLinear ℝ] {x : B}
    (hx : x ∈ e.baseSet) {W : Set B} (hxW : x ∈ W) :
    thomPairOverSignFiberClass F E R hι ω hxW = thomPairOverSignFiberClassOf R hι ω e hx hxW :=
  thomPairOverSignFiberClassOf_eq hι ω _ e _ hx hxW

/-- Reading the fibre orientation through `-ω` instead of `ω` negates the fibre class read through
a linear trivialization. -/
@[simp]
theorem thomPairOverSignFiberClassOf_neg (e : Trivialization F (π F E)) [e.IsLinear ℝ] {x : B}
    (hx : x ∈ e.baseSet) {W : Set B} (hxW : x ∈ W) :
    thomPairOverSignFiberClassOf R hι (-ω) e hx hxW =
      -thomPairOverSignFiberClassOf R hι ω e hx hxW := by
  have h : (e.mapOrientation ι hx).symm (-ω) = -(e.mapOrientation ι hx).symm ω := by
    rw [Equiv.symm_apply_eq, Trivialization.mapOrientation_neg, Equiv.apply_symm_apply]
  rw [thomPairOverSignFiberClassOf, thomPairOverSignFiberClassOf, h,
    fiberThomPairOverSignLocalSystemIso_neg_inv, TopPair.twistedHomologyCoefficientMap_neg]
  simp only [ModuleCat.hom_neg, LinearMap.neg_apply, map_neg]

/-- Replacing the orientation `ω` of the model fibre by `-ω` negates the fibre classes. -/
@[simp]
theorem thomPairOverSignFiberClass_neg {W : Set B} {x : B} (hxW : x ∈ W) :
    thomPairOverSignFiberClass F E R hι (-ω) hxW = -thomPairOverSignFiberClass F E R hι ω hxW :=
  thomPairOverSignFiberClassOf_neg hι ω _ _ hxW

private theorem localIso_hom_thomPairOverSignFiberClass (e : Trivialization F (π F E))
    [e.IsLinear ℝ] {W : Set B} (hW : W ⊆ e.baseSet) {x : B} (hxW : x ∈ W) :
    (localIso hι ω e hW).hom (thomPairOverSignFiberClass F E R hι ω hxW) =
      singularHomology₀Section (ModuleCat.of R R) (X := TopCat.of W) ⟨x, hxW⟩ 1 := by
  rw [thomPairOverSignFiberClass, thomPairOverSignFiberClassOf_eq hι ω _ e _ (hW hxW),
    localIso_hom_thomPairOverSignFiberClassOf]

/-- Restriction along an inclusion `W ⊆ W'` carries the fibre class over `x ∈ W` to the fibre
class over `x ∈ W'`. -/
@[simp]
theorem thomPairOverTwistedHomologyMap_thomPairOverSignFiberClass {W W' : Set B}
    (h : W ⊆ W') {x : B} (hxW : x ∈ W) :
    thomPairOverTwistedHomologyMap (thomPairSignLocalSystem F E R hι) h (finrank ℝ F)
        (thomPairOverSignFiberClass F E R hι ω hxW) =
      thomPairOverSignFiberClass F E R hι ω (h hxW) :=
  thomPairOverTwistedHomologyMap_thomPairOverSignFiberClassOf hι ω _ _ h hxW

/-- **The fibre classes are constant along paths**: near each point `b` they are read through the
chosen trivialization at `b` as the classes of the points. -/
theorem thomPairOverSignFiberClass_eq_of_path {W : Set B} {x y : W} (γ : Path x y) :
    thomPairOverSignFiberClass F E R hι ω x.property =
      thomPairOverSignFiberClass F E R hι ω y.property :=
  eq_of_path_of_mono (fun h ↦ thomPairOverTwistedHomologyMap (thomPairSignLocalSystem F E R hι) h
      (finrank ℝ F))
    (fun _ x ↦ thomPairOverSignFiberClass F E R hι ω x.property)
    (fun h x ↦ thomPairOverTwistedHomologyMap_thomPairOverSignFiberClass hι ω h x.property)
    (fun b ↦ (trivializationAt F E b).baseSet)
    (fun b ↦ (trivializationAt F E b).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt' b))
    (fun b _ ↦ ⟨(localIso hι ω (trivializationAt F E b) inter_subset_right).hom, 1,
      inferInstance, fun x ↦ by rw [localIso_hom_thomPairOverSignFiberClass, one_smul]⟩) γ

variable (F E R) in
/-- The map `H₀(W; R) ⟶ Hᵣ(E|_W, E₀|_W; π^*o(E))` sending the class of a point to the fibre class
over it (`TauCeti.thomPairOverSignFiberClass`). It is an isomorphism over every finite union of open
sets each inside the base set of a linear trivialization
(`TauCeti.isIso_thomPairOverTwistedHomologyFinrankInv_biUnion`). -/
def thomPairOverTwistedHomologyFinrankInv (W : Set B) :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} R) 0).obj (ModuleCat.of R R)).obj
        (TopCat.of W) ⟶
      (thomPairOver F E W).twistedHomology (thomPairOverSignLocalSystem F E R hι W) (finrank ℝ F) :=
  singularHomology₀Desc (ModuleCat.of R R) (X := TopCat.of W)
    (fun x ↦ ModuleCat.ofHom
      (LinearMap.toSpanSingleton R _ (thomPairOverSignFiberClass F E R hι ω x.property)))
    fun _ _ γ ↦ by rw [thomPairOverSignFiberClass_eq_of_path hι ω γ]

/-- The map `H₀(W; R) ⟶ Hᵣ(E|_W, E₀|_W; π^*o(E))` sends the class of a point to the fibre class
over it. -/
@[reassoc]
theorem singularHomology₀Section_thomPairOverTwistedHomologyFinrankInv {W : Set B} (x : W) :
    singularHomology₀Section (ModuleCat.of R R) (X := TopCat.of W) x ≫
        thomPairOverTwistedHomologyFinrankInv F E R hι ω W =
      ModuleCat.ofHom
        (LinearMap.toSpanSingleton R _ (thomPairOverSignFiberClass F E R hι ω x.property)) :=
  singularHomology₀Section_singularHomology₀Desc (X := TopCat.of W) _ _ _ x

/-- The maps `TauCeti.thomPairOverTwistedHomologyFinrankInv` over `W ⊆ W'` commute with the
inclusions on `H₀` and `Hᵣ`. -/
@[reassoc]
theorem thomPairOverTwistedHomologyFinrankInv_naturality {W W' : Set B} (h : W ⊆ W') :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} R) 0).obj (ModuleCat.of R R)).map
        (TopCat.ofHom (ContinuousMap.inclusion h)) ≫
        thomPairOverTwistedHomologyFinrankInv F E R hι ω W' =
      thomPairOverTwistedHomologyFinrankInv F E R hι ω W ≫
        thomPairOverTwistedHomologyMap (thomPairSignLocalSystem F E R hι) h (finrank ℝ F) := by
  refine singularHomology₀_hom_ext _ fun x ↦ ?_
  rw [singularHomology₀Section_naturality_assoc,
    singularHomology₀Section_thomPairOverTwistedHomologyFinrankInv,
    singularHomology₀Section_thomPairOverTwistedHomologyFinrankInv_assoc,
    ModuleCat.ofHom_toSpanSingleton_comp, thomPairOverTwistedHomologyMap_thomPairOverSignFiberClass]
  simp only [TopCat.hom_ofHom, ContinuousMap.inclusion_apply_coe]

/-- Over a subset of the base set of a linear trivialization, the map is an isomorphism, inverse to
`localIso`. -/
private theorem thomPairOverTwistedHomologyFinrankInv_comp_localIso_hom
    (e : Trivialization F (π F E)) [e.IsLinear ℝ] {W : Set B} (hW : W ⊆ e.baseSet) :
    thomPairOverTwistedHomologyFinrankInv F E R hι ω W ≫ (localIso hι ω e hW).hom = 𝟙 _ := by
  refine singularHomology₀_hom_ext _ fun x ↦ ?_
  rw [singularHomology₀Section_thomPairOverTwistedHomologyFinrankInv_assoc,
    ModuleCat.ofHom_toSpanSingleton_comp,
    localIso_hom_thomPairOverSignFiberClass, Category.comp_id]
  ext
  simp

private theorem isIso_thomPairOverTwistedHomologyFinrankInv_of_subset (e : Trivialization F (π F E))
    [e.IsLinear ℝ] {W : Set B} (hW : W ⊆ e.baseSet) :
    IsIso (thomPairOverTwistedHomologyFinrankInv F E R hι ω W) := by
  rw [(Iso.comp_hom_eq_id _).1 (thomPairOverTwistedHomologyFinrankInv_comp_localIso_hom hι ω e hW)]
  infer_instance

/-! ### Finite unions of trivializing open sets -/

/-- **The rank-degree homology over a finite union of trivializing open sets**: if `W` is the union
of finitely many open sets, each inside the base set of a linear trivialization, then
`H₀(W; R) ⟶ Hᵣ(E|_W, E₀|_W; π^*o(E))`, sending the class of a point to the fibre class over it, is
an isomorphism. -/
theorem isIso_thomPairOverTwistedHomologyFinrankInv_biUnion {κ : Type*} (s : Finset κ)
    {W : κ → Set B} (hWo : ∀ i ∈ s, IsOpen (W i))
    (hWe : ∀ i ∈ s, ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), W i ⊆ e.baseSet) :
    IsIso (thomPairOverTwistedHomologyFinrankInv F E R hι ω (⋃ i ∈ s, W i)) :=
  -- The Mayer–Vietoris induction over finite unions of open sets in the base sets of linear
  -- trivializations; the homology over `U ∩ V` vanishes in degree `r - 1` for such a `U`.
  isIso_biUnion_of_mayerVietoris
    (A := TopCat.subspaceDiagram (A := (id : Set B → Set B)) monotone_id ⋙
      (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} R) 0).obj (ModuleCat.of R R))
    (fun _ _ h ↦ thomPairOverTwistedHomologyMap (thomPairSignLocalSystem F E R hι) h (finrank ℝ F))
    (thomPairOverTwistedHomologyFinrankInv F E R hι ω)
    (fun _ _ h ↦ thomPairOverTwistedHomologyFinrankInv_naturality hι ω h)
    (fun U V _ _ ↦ epi_biprod_desc_singularHomologyMap_inclusion _ U V)
    (fun W ↦ ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), W ⊆ e.baseSet)
    (fun _ _ h ⟨e, he, hW⟩ ↦ ⟨e, he, h.trans hW⟩)
    (fun _ ⟨e, _, hW⟩ ↦ isIso_thomPairOverTwistedHomologyFinrankInv_of_subset hι ω e hW)
    (isIso_of_source_target_iso_zero _
      (isZero_singularHomology_of_isEmpty _ (TopCat.of (∅ : Set B)) _).isoZero
      (isZero_thomPairOverTwistedHomology_empty (thomPairSignLocalSystem F E R hι) _).isoZero)
    (fun U V ↦ by
      rw [← thomPairOverTwistedMayerVietorisToBiprod_def,
        ← thomPairOverTwistedMayerVietorisFromBiprod_def]
      exact thomPairOverTwistedMayerVietorisToBiprod_fromBiprod
        (thomPairSignLocalSystem F E R hι) U V (finrank ℝ F))
    (fun U V hU hV ↦ by
      have hex := thomPairOverTwistedMayerVietoris_exact₂ (thomPairSignLocalSystem F E R hι) hU hV
        (finrank ℝ F)
      simpa only [thomPairOverTwistedMayerVietorisToBiprod_def,
        thomPairOverTwistedMayerVietorisFromBiprod_def] using hex)
    (fun U V hU hV ⟨e, _, hW⟩ ↦ by
      rw [← thomPairOverTwistedMayerVietorisFromBiprod_def]
      exact epi_thomPairOverTwistedMayerVietorisFromBiprod_of_isZero
        (thomPairSignLocalSystem F E R hι) hU hV (n := finrank ℝ F) fun _ hm ↦
          e.isZero_thomPairOverTwistedHomology (thomPairSignLocalSystem F E R hι)
            (inter_subset_left.trans hW) (by omega))
    s hWo hWe

/-! ### The Thom pair over an arbitrary base -/

variable (F E R) in
/-- The fibre class over `b` in the homology of the Thom pair with coefficients in the pulled-back
orientation system: the image of the class of the fibre pair `(E_b, E_b ∖ {0})` which a linear
trivialization at `b` reads as the class of the point, with the coefficients `o(E)_b` trivialized
by the orientation of `E_b` which this trivialization reads as `ω`. Reversing both readings
together does not change it, so it does not depend on the trivialization. -/
def thomPairSignFiberClass (b : B) :
    (thomPair F E).twistedHomology (thomPairSignLocalSystem F E R hι) (finrank ℝ F) :=
  (thomPairOverTwistedHomologyUnivIso (thomPairSignLocalSystem F E R hι) (finrank ℝ F)).hom
    (thomPairOverSignFiberClass F E R hι ω (mem_univ b))

/-- Replacing the orientation `ω` of the model fibre by `-ω` negates the fibre classes. -/
@[simp]
theorem thomPairSignFiberClass_neg (b : B) :
    thomPairSignFiberClass F E R hι (-ω) b = -thomPairSignFiberClass F E R hι ω b := by
  rw [thomPairSignFiberClass, thomPairSignFiberClass, thomPairOverSignFiberClass_neg, map_neg]

/-- **The fibre class through the fibre inclusion.** For every orientation `o` of `E_b`, the fibre
class over `b` is the image of the generator of `Hᵣ(E_b, E_b ∖ {0}; R)` attached to `o`
(`TauCeti.orientedFiberGenerator`) under the inclusion of the fibre pair, with the coefficients over
the fibre trivialized by `o`. Replacing `o` by `-o` negates both the generator and the
trivialization. -/
theorem thomPairSignFiberClass_eq_thomPairSignFiberMap (b : B) (o : Orientation ℝ (E b) ι) :
    thomPairSignFiberClass F E R hι ω b =
      thomPairSignFiberMap F E R hι b o (finrank ℝ F) (orientedFiberGenerator R ω o) := by
  set e := trivializationAt F E b
  have hb : b ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' b
  set o₀ := (e.mapOrientation ι hb).symm ω
  have ho₀ : e.mapOrientation ι hb o₀ = ω := Equiv.apply_symm_apply _ ω
  -- For the orientation read as `ω` by the chosen trivialization, this is the definition of the
  -- fibre class, read in the Thom pair rather than in the pair over the whole base.
  have key : thomPairSignFiberClass F E R hι ω b =
      thomPairSignFiberMap F E R hι b o₀ (finrank ℝ F) (orientedFiberGenerator R ω o₀) := by
    rw [orientedFiberGenerator_of_mapOrientation_eq ω hι e hb ho₀, thomPairSignFiberClass,
      thomPairOverSignFiberClass, thomPairOverSignFiberClassOf, thomPairSignFiberMap_def,
      ModuleCat.comp_apply, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      ← twistedHomologyCoefficientMap_fiberThomPairOverSignLocalSystemIso_inv_comp_overUnivIso_hom]
  rcases (e.mapOrientation ι hb o).eq_or_eq_neg ω (Nat.card_eq_fintype_card.trans hι) with h | h
  · rwa [(e.mapOrientation ι hb).injective (h.trans ho₀.symm)]
  · have ho : o = -o₀ := by
      have h' : o₀ = -o := e.mapOrientation_symm_eq_neg_of_eq_neg hb h
      rw [h']
      exact (neg_neg o).symm
    rw [ho, thomPairSignFiberMap_neg, orientedFiberGenerator_neg ω hι]
    simpa only [ModuleCat.hom_neg, LinearMap.neg_apply, map_neg, neg_neg] using key

/-- The map `H₀(B; R) ⟶ Hᵣ(E, E₀; π^*o(E))` sending the class of a point to the fibre class over
it. -/
private def thomPairTwistedHomologyFinrankInv :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} R) 0).obj (ModuleCat.of R R)).obj
        (TopCat.of B) ⟶
      (thomPair F E).twistedHomology (thomPairSignLocalSystem F E R hι) (finrank ℝ F) :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} R) 0).obj (ModuleCat.of R R)).map
      (TopCat.isoOfHomeo (Homeomorph.Set.univ B).symm).hom ≫
    thomPairOverTwistedHomologyFinrankInv F E R hι ω univ ≫
    (thomPairOverTwistedHomologyUnivIso (thomPairSignLocalSystem F E R hι) (finrank ℝ F)).hom

private theorem singularHomology₀Section_thomPairTwistedHomologyFinrankInv (b : B) :
    singularHomology₀Section (ModuleCat.of R R) (X := TopCat.of B) b ≫
        thomPairTwistedHomologyFinrankInv hι ω =
      ModuleCat.ofHom (LinearMap.toSpanSingleton R _ (thomPairSignFiberClass F E R hι ω b)) := by
  rw [thomPairTwistedHomologyFinrankInv, singularHomology₀Section_naturality_assoc,
    singularHomology₀Section_thomPairOverTwistedHomologyFinrankInv_assoc,
    ModuleCat.ofHom_toSpanSingleton_comp, thomPairSignFiberClass]
  -- `(Homeomorph.Set.univ B).symm b` is `⟨b, mem_univ b⟩` by definition.
  rfl

/-- On any subset `W` of the base, `thomPairTwistedHomologyFinrankInv` restricts to
`thomPairOverTwistedHomologyFinrankInv W` followed by the inclusion into `(E, E₀)`. -/
private theorem thomPairTwistedHomologyFinrankInv_restrict (W : Set B) :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} R) 0).obj (ModuleCat.of R R)).map
        (TopCat.ofHom (ContinuousMap.subtypeVal W)) ≫
        thomPairTwistedHomologyFinrankInv hι ω =
      thomPairOverTwistedHomologyFinrankInv F E R hι ω W ≫
        (thomPairOver F E W).twistedHomologyCoefficientMap
          (eqToHom (TopPair.pullback_subtypeVal_eq_pullback_restrictPreimagePairMap
            (X := TopCat.of (TotalSpace F E)) (zeroSectionCompl F E)
            (thomPairSignLocalSystem F E R hι) (π F E) W)) (finrank ℝ F) ≫
        TopPair.twistedHomologyMap (TopCat.restrictPreimagePairMap
          (X := TopCat.of (TotalSpace F E)) (π F E) (zeroSectionCompl F E) W)
          (thomPairSignLocalSystem F E R hι) (finrank ℝ F) := by
  rw [← thomPairOverTwistedHomologyMap_subset_univ_comp_thomPairOverTwistedHomologyUnivIso_hom,
    ← thomPairOverTwistedHomologyFinrankInv_naturality_assoc (R := R) hι ω (subset_univ W)]
  refine singularHomology₀_hom_ext _ fun x ↦ ?_
  rw [singularHomology₀Section_naturality_assoc,
    singularHomology₀Section_thomPairTwistedHomologyFinrankInv,
    singularHomology₀Section_naturality_assoc,
    singularHomology₀Section_thomPairOverTwistedHomologyFinrankInv_assoc,
    ModuleCat.ofHom_toSpanSingleton_comp, thomPairSignFiberClass]
  -- `ContinuousMap.subtypeVal W x` and `(ContinuousMap.inclusion (subset_univ W) x).val` are both
  -- `x.val` by definition.
  rfl

/-- The component isomorphism over a finite union of chosen trivializing open sets, comparing `H₀`
with the twisted `Hᵣ` diagram object. -/
private def thomPairFiniteTrivializingUnionComponentIso (s : Finset B) :
    (baseFiniteTrivializingUnionDiagram F E ⋙
        (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} R) 0).obj (ModuleCat.of R R)).obj
        s ≅
      (TopPair.restrictPreimagePairTwistedHomologyFunctor (X := TopCat.of (TotalSpace F E))
        (zeroSectionCompl F E) (thomPairSignLocalSystem F E R hι) (π F E)
        (monotone_biUnion_baseSet_trivializationAt F E) (finrank ℝ F)).obj s :=
  eqToIso (congrArg
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} R) 0).obj (ModuleCat.of R R)).obj
      (baseFiniteTrivializingUnionDiagram_obj F E s)) ≪≫
    @asIso _ _ _ _ (thomPairOverTwistedHomologyFinrankInv F E R hι ω
        (⋃ b ∈ s, (trivializationAt F E b).baseSet))
      (isIso_thomPairOverTwistedHomologyFinrankInv_biUnion hι ω s
        (fun b _ ↦ (trivializationAt F E b).open_baseSet)
        fun _ _ ↦ ⟨_, inferInstance, subset_rfl⟩) ≪≫
    (thomPairOver F E (⋃ b ∈ s, (trivializationAt F E b).baseSet)).twistedHomologyCoefficientIso
      (eqToIso (TopPair.pullback_subtypeVal_eq_pullback_restrictPreimagePairMap
        (X := TopCat.of (TotalSpace F E)) (zeroSectionCompl F E)
        (thomPairSignLocalSystem F E R hι) (π F E)
        (⋃ b ∈ s, (trivializationAt F E b).baseSet))) (finrank ℝ F)

private theorem thomPairFiniteTrivializingUnionComponentIso_hom (s : Finset B) :
    (thomPairFiniteTrivializingUnionComponentIso (F := F) (E := E) (R := R) hι ω s).hom =
      eqToHom (congrArg
          ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} R) 0).obj
            (ModuleCat.of R R)).obj
          (baseFiniteTrivializingUnionDiagram_obj F E s)) ≫
        thomPairOverTwistedHomologyFinrankInv F E R hι ω
            (⋃ b ∈ s, (trivializationAt F E b).baseSet) ≫
          (thomPairOver F E
            (⋃ b ∈ s, (trivializationAt F E b).baseSet)).twistedHomologyCoefficientMap
            (eqToHom (TopPair.pullback_subtypeVal_eq_pullback_restrictPreimagePairMap
              (X := TopCat.of (TotalSpace F E)) (zeroSectionCompl F E)
              (thomPairSignLocalSystem F E R hι) (π F E)
              (⋃ b ∈ s, (trivializationAt F E b).baseSet))) (finrank ℝ F) := by
  -- `erw`: `(thomPairOver F E _).fst` matches `TopCat.of ↥(π F E ⁻¹' _)` after unfolding.
  erw [thomPairFiniteTrivializingUnionComponentIso, Iso.trans_hom, Iso.trans_hom, eqToIso.hom,
    asIso_hom, TopPair.twistedHomologyCoefficientIso_hom, eqToIso.hom]
  -- Both sides are identical after reducing the `asIso` and `twistedHomologyCoefficientIso`
  -- components.
  rfl

/-- Over finite unions of the chosen trivializing open sets, `thomPairOverTwistedHomologyFinrankInv`
gives a natural isomorphism between the `H₀` diagram of the base and the twisted `Hᵣ` diagram of the
Thom pairs. -/
private def thomPairFiniteTrivializingUnionNatIso :
    baseFiniteTrivializingUnionDiagram F E ⋙
        (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} R) 0).obj (ModuleCat.of R R) ≅
      TopPair.restrictPreimagePairTwistedHomologyFunctor (X := TopCat.of (TotalSpace F E))
        (zeroSectionCompl F E) (thomPairSignLocalSystem F E R hι) (π F E)
        (monotone_biUnion_baseSet_trivializationAt F E) (finrank ℝ F) :=
  NatIso.ofComponents (thomPairFiniteTrivializingUnionComponentIso hι ω) fun {s t} f ↦ by
    -- `erw`: unfold `baseFiniteTrivializingUnionDiagram` and
    -- `restrictPreimagePairTwistedHomologyFunctor` on morphisms.
    erw [Functor.comp_map, baseFiniteTrivializingUnionDiagram_map, Functor.map_comp,
      Functor.map_comp, eqToHom_map, eqToHom_map,
      thomPairFiniteTrivializingUnionComponentIso_hom,
      thomPairFiniteTrivializingUnionComponentIso_hom, Category.assoc, Category.assoc,
      eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
      thomPairOverTwistedHomologyFinrankInv_naturality_assoc (E := E) (R := R) hι ω
        (monotone_biUnion_baseSet_trivializationAt F E f.le)]
    exact congrArg (_ ≫ ·) (congrArg (_ ≫ ·) (thomPairOverTwistedHomologyMap_comp_eqToHom
      (thomPairSignLocalSystem F E R hι)
      (monotone_biUnion_baseSet_trivializationAt F E f.le) (finrank ℝ F)))

/-- **The passage to the whole base**: both `H₀(B; R)` and `Hᵣ(E, E₀; π^*o(E))` are the filtered
colimits of the corresponding groups over finite unions of the chosen trivializing open sets, on
each of which `thomPairOverTwistedHomologyFinrankInv` is an isomorphism. -/
private theorem isIso_thomPairTwistedHomologyFinrankInv :
    IsIso (thomPairTwistedHomologyFinrankInv (F := F) (E := E) (R := R) hι ω) := by
  let c₁ := isColimitMapCoconeSingularHomologyBaseFiniteTrivializingUnion F E (ModuleCat.of R R) 0
  let c₂ := isColimitThomPairFiniteTrivializingUnionTwistedHomologyCocone (F := F) (E := E)
    (thomPairSignLocalSystem F E R hι) (finrank ℝ F)
  let α := thomPairFiniteTrivializingUnionNatIso (F := F) (E := E) (R := R) hι ω
  let hbase := congrArg
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} R) 0).obj (ModuleCat.of R R)).obj
    (baseFiniteTrivializingUnionCocone_pt F E)
  have h : eqToHom hbase ≫ thomPairTwistedHomologyFinrankInv (F := F) (E := E) (R := R) hι ω =
      (c₁.coconePointsIsoOfNatIso c₂ α).hom := by
    refine c₁.hom_ext fun s ↦ ?_
    refine Eq.trans ?_ (c₁.comp_coconePointsIsoOfNatIso_hom c₂ α s).symm
    dsimp only [Functor.mapCocone_ι_app, α, thomPairFiniteTrivializingUnionNatIso,
      NatIso.ofComponents_hom_app]
    -- `erw`: unfold `c₁.ι`, `c₂.ι`, and `α.hom.app` across `(thomPair F E).fst`.
    erw [baseFiniteTrivializingUnionCocone_ι_app, Functor.map_comp, Functor.map_comp,
      eqToHom_map, eqToHom_map, Category.assoc, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp, TopPair.restrictPreimagePairTwistedHomologyCocone_ι_app,
      thomPairFiniteTrivializingUnionComponentIso_hom, Category.assoc, Category.assoc]
    exact congrArg (_ ≫ ·) (thomPairTwistedHomologyFinrankInv_restrict hι ω _)
  have : IsIso (eqToHom hbase ≫
      thomPairTwistedHomologyFinrankInv (F := F) (E := E) (R := R) hι ω) := by
    rw [h]
    exact Iso.isIso_hom _
  exact IsIso.of_isIso_comp_left (eqToHom hbase) _

variable (F E R) in
/-- **The homology of the Thom pair in the rank degree with coefficients in the pulled-back
orientation system.** For a real vector bundle `E → B` of rank `r` over an arbitrary base, with
Thom pair `(E, E₀)`, and a ring `R`, `Hᵣ(E, E₀; π^*o(E)) ≅ H₀(B; R)`, where `π^*o(E)` is the
orientation local system of `E` pulled back to the total space
(`TauCeti.thomPairSignLocalSystem`). No orientation of `E` is needed: the isomorphism is
normalized by an orientation `ω` of the model fibre, and sends the fibre class over `b`
(`TauCeti.thomPairSignFiberClass`) to the class of `b`
(`TauCeti.thomPairTwistedHomologyFinrankIso_hom_thomPairSignFiberClass`). -/
def thomPairTwistedHomologyFinrankIso :
    (thomPair F E).twistedHomology (thomPairSignLocalSystem F E R hι) (finrank ℝ F) ≅
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} R) 0).obj
        (ModuleCat.of R R)).obj (TopCat.of B) :=
  have := isIso_thomPairTwistedHomologyFinrankInv (F := F) (E := E) (R := R) hι ω
  (asIso (thomPairTwistedHomologyFinrankInv (F := F) (E := E) (R := R) hι ω)).symm

/-- The isomorphism `Hᵣ(E, E₀; π^*o(E)) ≅ H₀(B; R)` sends the fibre class over `b` to the class of
the point `b`. -/
@[simp]
theorem thomPairTwistedHomologyFinrankIso_hom_thomPairSignFiberClass (b : B) :
    (thomPairTwistedHomologyFinrankIso F E R hι ω).hom (thomPairSignFiberClass F E R hι ω b) =
      singularHomology₀Section (ModuleCat.of R R) (X := TopCat.of B) b 1 := by
  have := isIso_thomPairTwistedHomologyFinrankInv (F := F) (E := E) (R := R) hι ω
  have hb := ConcreteCategory.congr_hom
    (singularHomology₀Section_thomPairTwistedHomologyFinrankInv (F := F) (E := E) (R := R) hι ω b)
    1
  simp only [ConcreteCategory.comp_apply, ModuleCat.hom_ofHom, LinearMap.toSpanSingleton_apply,
    one_smul] at hb
  rw [thomPairTwistedHomologyFinrankIso, Iso.symm_hom, asIso_inv, ← hb, IsIso.hom_inv_id_apply]

/-- **Morphisms out of `Hᵣ(E, E₀; π^*o(E))` are determined by the fibre classes**: two morphisms to
a module `M` that agree on the fibre class over every point are equal. -/
theorem thomPairTwistedHomology_hom_ext {M : ModuleCat.{w} R}
    {f g : (thomPair F E).twistedHomology (thomPairSignLocalSystem F E R hι) (finrank ℝ F) ⟶ M}
    (h : ∀ b, f.hom (thomPairSignFiberClass F E R hι ω b) =
      g.hom (thomPairSignFiberClass F E R hι ω b)) :
    f = g := by
  rw [← Iso.hom_inv_id_assoc (thomPairTwistedHomologyFinrankIso F E R hι ω) f,
    ← Iso.hom_inv_id_assoc (thomPairTwistedHomologyFinrankIso F E R hι ω) g]
  congr 1
  refine singularHomology₀_hom_ext _ fun b ↦ ?_
  -- The class of `b` is the image of the fibre class over `b`.
  have hb : singularHomology₀Section (ModuleCat.of R R) (X := TopCat.of B) b =
      ModuleCat.ofHom (LinearMap.toSpanSingleton R _ ((thomPairTwistedHomologyFinrankIso F E R hι
        ω).hom (thomPairSignFiberClass F E R hι ω b))) := by
    rw [thomPairTwistedHomologyFinrankIso_hom_thomPairSignFiberClass]
    exact ModuleCat.hom_ext (LinearMap.ext_ring (by simp))
  rw [hb, ModuleCat.ofHom_toSpanSingleton_comp, ModuleCat.ofHom_toSpanSingleton_comp,
    ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, Iso.hom_inv_id_apply, h b]

end FiberClass

end TauCeti
