/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.MayerVietoris.DirectedUnion
public import TauCeti.AlgebraicTopology.Singular.Reduced
public import TauCeti.AlgebraicTopology.Singular.Twisted.Zero
public import TauCeti.Topology.VectorBundle.Orientation.LocalSystem
import TauCeti.Algebra.Category.ModuleCat.SpanSingleton
import TauCeti.AlgebraicTopology.Singular.LocalHomology.Basic
import TauCeti.AlgebraicTopology.Singular.LocalHomology.Linear

/-!
# The homology of the Thom pair in the rank degree

Let `E → B` be a real vector bundle of rank `r` over an arbitrary base, with Thom pair `(E, E₀)`,
and let `K` be a commutative ring whose only unit is `1`, such as `ZMod 2`. The relative homology
`Hₙ(E, E₀; K)` vanishes for `n < r` (`TauCeti.isZero_singularHomology_thomPair`). This file
computes the first group that does not vanish:

`Hᵣ(E, E₀; K) ≅ H₀(B; K)`

(`TauCeti.thomPairSingularHomologyFinrankIso`). The isomorphism sends the class of the fibre over a
point `b`, the image of a generator of `Hᵣ(E_b, E_b ∖ {0}; K) ≅ K` under the inclusion of the fibre
pair, to the class of the point `b` (`TauCeti.thomPairSingularHomologyFinrankIso_hom_apply`). No
orientation of the bundle is needed: since `1` is the only unit of `K`, the module
`Hᵣ(E_b, E_b ∖ {0}; K) ≅ K` has a single generator, so the fibre classes do not depend on any
choice.
This is the bottom degree of the Thom isomorphism `Hₙ₊ᵣ(E, E₀; K) ≅ Hₙ(B; K)` in homology with
coefficients in `K`.

Over an arbitrary commutative ring `K`, such as `ℤ`, the generators of `Hᵣ(E_b, E_b ∖ {0}; K)`
correspond to the orientations of `E_b`, and the group in the rank degree is the zeroth homology of
`B` twisted by the orientation local system `o(E)`
(`TauCeti.VectorBundleOrientationCover.signLocalSystem`):

`Hᵣ(E, E₀; K) ≅ H₀(B; o(E) ⊗ K)`

(`TauCeti.thomPairSingularHomologyFinrankIsoTwistedHomology`), again with no orientability
assumption. The fibre of `o(E)` over `b` consists of the functions `f` on the orientations of `E_b`
with `f (-o) = -f o`, and the class of `f` goes to `f o` times the fibre class of the generator of
`o`. Which generator belongs to which orientation is fixed by an orientation `ω` of the model fibre
`F`: a linear trivialization reading `o` as `ω` carries the generator of `o` to the generator
`TauCeti.complZeroPairGenerator K F` of `Hᵣ(F, F ∖ {0}; K)`. When `E` is the negative normal
bundle of a Morse–Bott critical submanifold, `Hᵣ(E, E₀)` is the bottom relative homology group
across the critical level, so this identifies that group with the zeroth homology of the
submanifold twisted by the orientations of its negative bundle.

## The proof

The inverse map `H₀(B; K) ⟶ Hᵣ(E, E₀; K)` is defined on the classes of points, which generate
`H₀(B; K)`: it sends the class of `b` to the fibre class over `b`. This is well defined because the
fibre classes are constant along paths in the base. Over a subset `W` of the base set of a linear
trivialization, the trivialization identifies the Thom pair `(E|_W, E₀|_W)` with the Thom pair of
the product bundle `W × F`, whose homology in degree `r` is `H₀(W; K)`
(`TauCeti.prodThomPairSingularHomologyIso`), and this identification sends the fibre class over a
point to the class of the point; so the fibre classes over two points joined by a path in `W`
agree, and the map is an isomorphism over `W`. The Mayer–Vietoris sequence of the Thom pairs over
two open sets (`TauCeti.singularHomology_thomPairOver_mayerVietoris_exact`) ends in degree `r`,
since the homology vanishes below the rank, so the map is an isomorphism over a finite union of
trivializing open sets by induction on their number. Singular homology has compact supports, so
the homology of the base and of the Thom pair are the filtered colimits of their homology over
these finite unions, and the map is an isomorphism over the whole base.

The twisted isomorphism has the same structure, with the colimit description of twisted zeroth
homology (`TauCeti.LocalCoefficientSystem.isColimitTwistedHomology₀Cocone`) in place of the classes
of points. A linear automorphism of `F` acts on `Hᵣ(F, F ∖ {0})` and on the orientations of `F` by
the sign of its determinant, so the generator of an orientation of `E_b` does not depend on the
trivialization through which it is read. The fibre classes of these generators are constant along
paths in the orientation double cover, since near each point such a path stays in a sheet of a
trivialization; transport in `o(E)` is lifting of paths to the double cover, so the fibre classes
form a cocone over `o(E)` and define `H₀(B; o(E) ⊗ K) ⟶ Hᵣ(E, E₀; K)`. The map in the other
direction is built over a trivializing set from `Hᵣ(E|_W, E₀|_W; K) ≅ H₀(W; K)`, sending the class
of a point to the class of the orientation read as `ω`, and is glued over finite unions of
trivializing open sets by the Mayer–Vietoris sequence and over the whole base by compact supports.

## Main results

* `TauCeti.thomPairSingularHomologyFinrankIso`: `Hᵣ(E, E₀; K) ≅ H₀(B; K)` for `r` the rank and `K`
  a commutative ring whose only unit is `1`.
* `TauCeti.thomPairSingularHomologyFinrankIso_hom_apply`: it sends the fibre class over `b` to the
  class of `b`.
* `TauCeti.thomPairSingularHomologyFinrankIsoTwistedHomology`: `Hᵣ(E, E₀; K) ≅ H₀(B; o(E) ⊗ K)` for
  any commutative ring `K`.
* `TauCeti.thomPairSingularHomologyFinrankIsoTwistedHomology_inv_ιTwistedHomology₀`,
  `TauCeti.thomPairSingularHomologyFinrankIsoTwistedHomology_hom_apply`: its values on the classes
  of the fibres.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10, Lemma 10.3 and the proof of Theorem 10.4 (the induction over finite unions
  of trivializing open sets and the passage to a directed union).
* A. Hatcher, *Algebraic Topology*, Section 4.D, Theorem 4D.10 and its proof, which also covers
  `ℤ/2` coefficients for bundles without an orientation, and Section 3.H (local coefficients and
  the orientation local system).
* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261 (the
  relative homology across a critical level with coefficients twisted by the orientations of the
  negative bundle).
-/

public noncomputable section

open Bundle CategoryTheory Limits Set Module AlgebraicTopology Topology

universe w

namespace TauCeti

section Fiber

variable (K : Type w) [CommRing K] (F : Type w) [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- The generator of `Hᵣ(F, F ∖ {0}; K)`, `r = dim F`, corresponding to the class of the point in
`H₀(pt; K)` under `Hᵣ(pt × F, pt × (F ∖ {0}); K) ≅ H₀(pt; K)`. -/
def complZeroPairGenerator :
    ((TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularHomology (ModuleCat.of K K)
      (finrank ℝ F) : ModuleCat.{w} K) :=
  TopPair.singularHomologyMap (complZeroPairIsoProdThomPair F).inv (ModuleCat.of K K) (finrank ℝ F)
    ((prodThomPairSingularHomologyIso (ModuleCat.of K K) PUnit.{w + 1} F 0 (finrank ℝ F)).inv
      (singularHomology₀Section (ModuleCat.of K K) (X := TopCat.of PUnit.{w + 1}) PUnit.unit 1))

/-- The fibre inclusion over the point carries the generator to the class of the point. -/
private theorem singularHomologyMap_prodThomPairFiberMap_complZeroPairGenerator_punit :
    TopPair.singularHomologyMap (prodThomPairFiberMap F PUnit.unit) (ModuleCat.of K K)
        (finrank ℝ F) (complZeroPairGenerator K F) =
      (prodThomPairSingularHomologyIso (ModuleCat.of K K) PUnit.{w + 1} F 0 (finrank ℝ F)).inv
        (singularHomology₀Section (ModuleCat.of K K) (X := TopCat.of PUnit.{w + 1}) PUnit.unit
          1) := by
  rw [complZeroPairGenerator, ← ConcreteCategory.comp_apply, ← TopPair.singularHomologyMap_comp]
  exact congrArg (fun f ↦ TopPair.singularHomologyMap f (ModuleCat.of K K) (finrank ℝ F) _)
    (complZeroPairIsoProdThomPair F).inv_hom_id |>.trans (by simp)

/-- The fibre inclusion over a point `x` of `W` carries the generator to the class of `x` under
`Hᵣ(W × F, W × (F ∖ {0}); K) ≅ H₀(W; K)`. -/
theorem singularHomologyMap_prodThomPairFiberMap_complZeroPairGenerator
    {W : Type w} [TopologicalSpace W] (x : W) :
    TopPair.singularHomologyMap (prodThomPairFiberMap F x) (ModuleCat.of K K) (finrank ℝ F)
        (complZeroPairGenerator K F) =
      (prodThomPairSingularHomologyIso (ModuleCat.of K K) W F 0 (finrank ℝ F)).inv
        (singularHomology₀Section (ModuleCat.of K K) (X := TopCat.of W) x 1) := by
  -- The fibre over `x` is the fibre over the point, pushed forward along the constant map `x`.
  have hx := prodThomPairFiberMap_comp_prodThomPairMap F PUnit.unit
    (ContinuousMap.const PUnit.{w + 1} x)
  rw [ContinuousMap.const_apply] at hx
  rw [← hx, TopPair.singularHomologyMap_comp, ConcreteCategory.comp_apply,
    singularHomologyMap_prodThomPairFiberMap_complZeroPairGenerator_punit,
    ← ConcreteCategory.comp_apply, prodThomPairSingularHomologyIso_inv_naturality (ModuleCat.of K K)
      PUnit.{w + 1} F (ContinuousMap.const PUnit.{w + 1} x) 0 (finrank ℝ F),
    ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply (singularHomology₀Section _ _),
    singularHomology₀Section_naturality]
  simp

/-- The class `complZeroPairGenerator K F` generates `Hᵣ(F, F ∖ {0}; K)`. -/
theorem span_complZeroPairGenerator :
    Submodule.span K {complZeroPairGenerator K F} = ⊤ := by
  -- The class of the point generates `H₀(pt; K)`, being the inverse of the augmentation `≅ K`
  -- applied to `1`.
  have hpt : Submodule.span K {(singularHomology₀Section (ModuleCat.of K K)
      (X := TopCat.of PUnit.{w + 1}) PUnit.unit (1 : K) :)} = ⊤ := by
    rw [IsIso.eq_inv_of_inv_hom_id (singularHomology₀Section_singularHomology₀ε _ _)]
    exact (ModuleCat.span_singleton_apply_eq_top_iff _).2 Ideal.span_singleton_one
  exact (ModuleCat.span_singleton_apply_eq_top_iff _).2
    ((ModuleCat.span_singleton_apply_eq_top_iff _).2 hpt)

variable [Subsingleton Kˣ]

/-- With coefficients in a ring whose only unit is `1`, the module `Hᵣ(F, F ∖ {0}; K) ≅ K` has a
single generator. -/
private theorem eq_complZeroPairGenerator {x : ((TopPair.ofSubset (X := TopCat.of F)
    ({0}ᶜ : Set F)).singularHomology (ModuleCat.of K K) (finrank ℝ F) : ModuleCat.{w} K)}
    (hx : Submodule.span K {x} = ⊤) : x = complZeroPairGenerator K F :=
  LinearEquiv.eq_of_span_singleton_eq_top (singularHomologyComplSingletonFinrankIso
      (ModuleCat.of K K) (OpenPartialHomeomorph.refl F) (mem_univ 0)).toLinearEquiv hx
    (span_complZeroPairGenerator K F)

end Fiber

section Bundle

variable {K : Type w} [CommRing K] {B : Type w} [TopologicalSpace B] {F : Type w}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {E : B → Type w}
  [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)]
  [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]

variable (K F E) in
/-- The generator of `Hᵣ(E_b, E_b ∖ {0}; K) ≅ K`, read through the trivialization at `b`. -/
private def fiberGenerator (b : B) :
    ((TopPair.ofSubset (X := TopCat.of (E b)) ({0}ᶜ : Set (E b))).singularHomology
      (ModuleCat.of K K) (finrank ℝ F) : ModuleCat.{w} K) :=
  TopPair.singularHomologyMap ((trivializationAt F E b).continuousLinearEquivAt ℝ b
      (mem_baseSet_trivializationAt F E b)).complZeroPairIso.inv (ModuleCat.of K K) (finrank ℝ F)
    (complZeroPairGenerator K F)

private theorem span_fiberGenerator (b : B) : Submodule.span K {fiberGenerator K F E b} = ⊤ :=
  (ModuleCat.span_singleton_apply_eq_top_iff _).2 (span_complZeroPairGenerator K F)

variable (K F E) in
/-- The fibre class over a point `x` of `W`: the image of the fibre generator in
`Hᵣ(E|_W, E₀|_W; K)`. -/
private def fiberClassOver (W : Set B) (x : W) :
    ((thomPairOver F E W).singularHomology (ModuleCat.of K K) (finrank ℝ F) : ModuleCat.{w} K) :=
  TopPair.singularHomologyMap (fiberThomPairOverMap F E x.2) (ModuleCat.of K K) (finrank ℝ F)
    (fiberGenerator K F E x)

/-- Restricting from `W` to `W'` carries fibre classes to fibre classes. -/
private theorem singularHomologyMap_thomPairOverMap_fiberClassOver {W W' : Set B} (h : W ⊆ W')
    (x : W) :
    TopPair.singularHomologyMap (thomPairOverMap F E h) (ModuleCat.of K K) (finrank ℝ F)
        (fiberClassOver K F E W x) = fiberClassOver K F E W' (inclusion h x) := by
  rw [fiberClassOver, fiberClassOver, ← ConcreteCategory.comp_apply,
    ← TopPair.singularHomologyMap_comp, fiberThomPairOverMap_comp_thomPairOverMap]

variable [Subsingleton Kˣ]

/-- Every generator of `Hᵣ(E_b, E_b ∖ {0}; K)` is the fibre generator. -/
private theorem eq_fiberGenerator {b : B} {x : ((TopPair.ofSubset (X := TopCat.of (E b))
    ({0}ᶜ : Set (E b))).singularHomology (ModuleCat.of K K) (finrank ℝ F) : ModuleCat.{w} K)}
    (hx : Submodule.span K {x} = ⊤) : x = fiberGenerator K F E b := by
  let L := (trivializationAt F E b).continuousLinearEquivAt ℝ b (mem_baseSet_trivializationAt F E b)
  apply (ModuleCat.mono_iff_injective (TopPair.singularHomologyMap L.complZeroPairIso.hom
    (ModuleCat.of K K) (finrank ℝ F))).1 inferInstance
  rw [eq_complZeroPairGenerator K F ((ModuleCat.span_singleton_apply_eq_top_iff _).2 hx),
    eq_complZeroPairGenerator K F
      ((ModuleCat.span_singleton_apply_eq_top_iff _).2 (span_fiberGenerator b))]

/-- A linear trivialization at `b` carries the fibre generator to the generator of
`Hᵣ(F, F ∖ {0}; K)`. -/
private theorem singularHomologyMap_complZeroPairIso_fiberGenerator
    (e : Trivialization F (π F E)) [e.IsLinear ℝ] {b : B} (hb : b ∈ e.baseSet) :
    TopPair.singularHomologyMap (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.hom
      (ModuleCat.of K K) (finrank ℝ F) (fiberGenerator K F E b) = complZeroPairGenerator K F :=
  eq_complZeroPairGenerator K F
    ((ModuleCat.span_singleton_apply_eq_top_iff _).2 (span_fiberGenerator b))

/-- **The fibre classes over a trivializing set are the classes of the points**: a linear
trivialization over `W` identifies `Hᵣ(E|_W, E₀|_W; K)` with
`Hᵣ(W × F, W × (F ∖ {0}); K) ≅ H₀(W; K)`, and this sends the fibre class over `x` to the class
of `x`. -/
private theorem singularHomologyMap_thomPairOverIso_fiberClassOver (e : Trivialization F (π F E))
    [e.IsLinear ℝ] {W : Set B} (hW : W ⊆ e.baseSet) (x : W) :
    TopPair.singularHomologyMap (e.thomPairOverIso ℝ hW).hom (ModuleCat.of K K) (finrank ℝ F)
        (fiberClassOver K F E W x) =
      (prodThomPairSingularHomologyIso (ModuleCat.of K K) W F 0 (finrank ℝ F)).inv
        (singularHomology₀Section (ModuleCat.of K K) (X := TopCat.of W) x 1) := by
  rw [fiberClassOver, ← ConcreteCategory.comp_apply, ← TopPair.singularHomologyMap_comp,
    Bundle.Trivialization.fiberThomPairOverMap_comp_thomPairOverIso_hom ℝ e hW x.2,
    TopPair.singularHomologyMap_comp, ConcreteCategory.comp_apply,
    singularHomologyMap_complZeroPairIso_fiberGenerator e (hW x.2), Subtype.coe_eta,
    singularHomologyMap_prodThomPairFiberMap_complZeroPairGenerator]

/-- The fibre classes over two points of `W` joined by a path in `W` over the base set of a linear
trivialization agree. -/
private theorem fiberClassOver_eq_of_joinedIn (e : Trivialization F (π F E)) [e.IsLinear ℝ]
    {W : Set B} {x y : W} (h : JoinedIn {z : W | (z : B) ∈ e.baseSet} x y) :
    fiberClassOver K F E W x = fiberClassOver K F E W y := by
  have hW : W ∩ e.baseSet ⊆ e.baseSet := inter_subset_right
  let x' : ↥(W ∩ e.baseSet) := ⟨x, x.2, h.source_mem⟩
  let y' : ↥(W ∩ e.baseSet) := ⟨y, y.2, h.target_mem⟩
  -- The two points are joined in `W ∩ e.baseSet`, so their classes in `H₀` agree.
  have hj : Joined x' y' :=
    h.joined_subtype.map (f := fun z : {z : W | (z : B) ∈ e.baseSet} ↦
      (⟨z.1.1, z.1.2, z.2⟩ : ↥(W ∩ e.baseSet))) (by fun_prop)
  have hxy : fiberClassOver K F E (W ∩ e.baseSet) x' = fiberClassOver K F E (W ∩ e.baseSet) y' := by
    apply (ModuleCat.mono_iff_injective (TopPair.singularHomologyMap (e.thomPairOverIso ℝ hW).hom
      (ModuleCat.of K K) (finrank ℝ F))).1 inferInstance
    rw [singularHomologyMap_thomPairOverIso_fiberClassOver e hW,
      singularHomologyMap_thomPairOverIso_fiberClassOver e hW,
      singularHomology₀Section_eq_of_joined _ hj]
  have := congrArg (TopPair.singularHomologyMap (thomPairOverMap F E inter_subset_left)
    (ModuleCat.of K K) (finrank ℝ F)) hxy
  rwa [singularHomologyMap_thomPairOverMap_fiberClassOver,
    singularHomologyMap_thomPairOverMap_fiberClassOver] at this

/-- **The fibre classes are constant along paths.** -/
private theorem fiberClassOver_eq_of_path {W : Set B} {x y : W} (γ : Path x y) :
    fiberClassOver K F E W x = fiberClassOver K F E W y := by
  have : LocallyPathConnectedSpace unitInterval :=
    Convex.locallyPathConnectedSpace ℝ (convex_Icc (0 : ℝ) 1)
  have hlc : IsLocallyConstant fun t ↦ fiberClassOver K F E W (γ t) := by
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun t ↦ ?_
    let e := trivializationAt F E (γ t : B)
    have hO : {s : unitInterval | ((γ s : W) : B) ∈ e.baseSet} ∈ 𝓝 t :=
      (e.open_baseSet.preimage (continuous_subtype_val.comp γ.continuous)).mem_nhds
        (mem_baseSet_trivializationAt F E _)
    filter_upwards [pathComponentIn_mem_nhds hO] with s hs
    refine (fiberClassOver_eq_of_joinedIn e ((hs.map γ.continuous.continuousOn).mono ?_)).symm
    rintro _ ⟨u, hu, rfl⟩
    exact hu
  simpa using hlc.apply_eq_of_preconnectedSpace 0 1

variable (K F E) in
/-- The map `H₀(W; K) ⟶ Hᵣ(E|_W, E₀|_W; K)` sending the class of a point to the fibre class over
it. -/
private def thomPairOverSingularHomologyFinrankInv (W : Set B) :
    ((singularHomologyFunctor (ModuleCat.{w} K) 0).obj (ModuleCat.of K K)).obj (TopCat.of W) ⟶
      (thomPairOver F E W).singularHomology (ModuleCat.of K K) (finrank ℝ F) :=
  singularHomology₀Desc (ModuleCat.of K K) (X := TopCat.of W)
    (fun x ↦ ModuleCat.ofHom (LinearMap.toSpanSingleton K _ (fiberClassOver K F E W x)))
    fun _ _ γ ↦ by rw [fiberClassOver_eq_of_path γ]

@[reassoc]
private theorem singularHomology₀Section_thomPairOverSingularHomologyFinrankInv {W : Set B}
    (x : W) :
    singularHomology₀Section (ModuleCat.of K K) (X := TopCat.of W) x ≫
        thomPairOverSingularHomologyFinrankInv K F E W =
      ModuleCat.ofHom (LinearMap.toSpanSingleton K _ (fiberClassOver K F E W x)) := by
  rw [thomPairOverSingularHomologyFinrankInv]
  exact singularHomology₀Section_singularHomology₀Desc (X := TopCat.of W) _ _ _ x

/-- The maps over `W ⊆ W'` commute with the restrictions. -/
private theorem thomPairOverSingularHomologyFinrankInv_naturality {W W' : Set B} (h : W ⊆ W') :
    ((singularHomologyFunctor (ModuleCat.{w} K) 0).obj (ModuleCat.of K K)).map
        (TopCat.ofHom (ContinuousMap.inclusion h)) ≫
        thomPairOverSingularHomologyFinrankInv K F E W' =
      thomPairOverSingularHomologyFinrankInv K F E W ≫
        TopPair.singularHomologyMap (thomPairOverMap F E h) (ModuleCat.of K K) (finrank ℝ F) := by
  refine singularHomology₀_hom_ext _ fun x ↦ ?_
  rw [singularHomology₀Section_naturality_assoc,
    singularHomology₀Section_thomPairOverSingularHomologyFinrankInv,
    singularHomology₀Section_thomPairOverSingularHomologyFinrankInv_assoc,
    ModuleCat.ofHom_toSpanSingleton_comp, singularHomologyMap_thomPairOverMap_fiberClassOver]
  rw [ConcreteCategory.hom_ofHom, show ContinuousMap.inclusion h x = inclusion h x from
    Subtype.ext ((ContinuousMap.inclusion_apply_coe h x).trans (coe_inclusion h x).symm)]

/-- Over a subset of the base set of a linear trivialization, the map is the inverse of the
isomorphism `Hᵣ(W × F, W × (F ∖ {0})) ≅ H₀(W)` of the product bundle, read through the
trivialization. -/
private theorem thomPairOverSingularHomologyFinrankInv_comp_thomPairOverIso
    (e : Trivialization F (π F E)) [e.IsLinear ℝ] {W : Set B} (hW : W ⊆ e.baseSet) :
    thomPairOverSingularHomologyFinrankInv K F E W ≫
        TopPair.singularHomologyMap (e.thomPairOverIso ℝ hW).hom (ModuleCat.of K K)
          (finrank ℝ F) =
      (prodThomPairSingularHomologyIso (ModuleCat.of K K) W F 0 (finrank ℝ F)).inv := by
  refine singularHomology₀_hom_ext _ fun x ↦ ?_
  rw [singularHomology₀Section_thomPairOverSingularHomologyFinrankInv_assoc,
    ModuleCat.ofHom_toSpanSingleton_comp, singularHomologyMap_thomPairOverIso_fiberClassOver e hW]
  ext
  simp

private theorem isIso_thomPairOverSingularHomologyFinrankInv_of_subset
    (e : Trivialization F (π F E)) [e.IsLinear ℝ] {W : Set B} (hW : W ⊆ e.baseSet) :
    IsIso (thomPairOverSingularHomologyFinrankInv K F E W) := by
  rw [(IsIso.eq_comp_inv _).2
    (thomPairOverSingularHomologyFinrankInv_comp_thomPairOverIso (K := K) e hW)]
  infer_instance

private theorem isIso_thomPairOverSingularHomologyFinrankInv_empty :
    IsIso (thomPairOverSingularHomologyFinrankInv K F E ∅) :=
  isIso_of_source_target_iso_zero _
    (isZero_singularHomologyFunctor_zero_of_isEmpty _ _).isoZero
    (isZero_singularHomology_thomPairOver_empty _ _).isoZero

/-- Over `W ⊆ W'`, with the map over `W'` an isomorphism, the restriction from `W` to `W'` read
through the maps over `W` and `W'` is the map induced by the inclusion. -/
@[reassoc]
private theorem thomPairOverSingularHomologyFinrankInv_comp_singularHomologyMap_comp_inv
    {W W' : Set B} (h : W ⊆ W') [IsIso (thomPairOverSingularHomologyFinrankInv K F E W')] :
    thomPairOverSingularHomologyFinrankInv K F E W ≫
        TopPair.singularHomologyMap (thomPairOverMap F E h) (ModuleCat.of K K) (finrank ℝ F) ≫
          inv (thomPairOverSingularHomologyFinrankInv K F E W') =
      ((singularHomologyFunctor (ModuleCat.{w} K) 0).obj (ModuleCat.of K K)).map
        (TopCat.ofHom (ContinuousMap.inclusion h)) := by
  rw [← Category.assoc, ← thomPairOverSingularHomologyFinrankInv_naturality, Category.assoc,
    IsIso.hom_inv_id, Category.comp_id]

/-- In the Mayer–Vietoris step, a candidate inverse `Φ` of the map over `W'` is built which on the
classes over a subset `W` is the inverse of the map over `W` followed by the inclusion. Such a `Φ`
inverts the map over `W'` on the classes of points of `W`. -/
private theorem singularHomology₀Section_thomPairOverSingularHomologyFinrankInv_comp_of_comp_eq
    {W W' : Set B} (h : W ⊆ W') [IsIso (thomPairOverSingularHomologyFinrankInv K F E W)]
    {Φ : (thomPairOver F E W').singularHomology (ModuleCat.of K K) (finrank ℝ F) ⟶
      ((singularHomologyFunctor (ModuleCat.{w} K) 0).obj (ModuleCat.of K K)).obj (TopCat.of W')}
    (hΦ : TopPair.singularHomologyMap (thomPairOverMap F E h) (ModuleCat.of K K) (finrank ℝ F) ≫
      Φ = inv (thomPairOverSingularHomologyFinrankInv K F E W) ≫
        ((singularHomologyFunctor (ModuleCat.{w} K) 0).obj (ModuleCat.of K K)).map
          (TopCat.ofHom (ContinuousMap.inclusion h)))
    (x : W) :
    singularHomology₀Section (ModuleCat.of K K) (X := TopCat.of W')
          (TopCat.ofHom (ContinuousMap.inclusion h) x) ≫
        thomPairOverSingularHomologyFinrankInv K F E W' ≫ Φ =
      singularHomology₀Section (ModuleCat.of K K) (X := TopCat.of W')
        (TopCat.ofHom (ContinuousMap.inclusion h) x) := by
  rw [← singularHomology₀Section_naturality, Category.assoc,
    reassoc_of% (thomPairOverSingularHomologyFinrankInv_naturality (K := K) (F := F) (E := E) h),
    hΦ, IsIso.hom_inv_id_assoc]

/-- Such a `Φ` also inverts the map over `W'` on the classes over `W`. -/
private theorem singularHomologyMap_thomPairOverMap_comp_comp_of_comp_eq
    {W W' : Set B} (h : W ⊆ W') [IsIso (thomPairOverSingularHomologyFinrankInv K F E W)]
    {Φ : (thomPairOver F E W').singularHomology (ModuleCat.of K K) (finrank ℝ F) ⟶
      ((singularHomologyFunctor (ModuleCat.{w} K) 0).obj (ModuleCat.of K K)).obj (TopCat.of W')}
    (hΦ : TopPair.singularHomologyMap (thomPairOverMap F E h) (ModuleCat.of K K) (finrank ℝ F) ≫
      Φ = inv (thomPairOverSingularHomologyFinrankInv K F E W) ≫
        ((singularHomologyFunctor (ModuleCat.{w} K) 0).obj (ModuleCat.of K K)).map
          (TopCat.ofHom (ContinuousMap.inclusion h))) :
    TopPair.singularHomologyMap (thomPairOverMap F E h) (ModuleCat.of K K) (finrank ℝ F) ≫ Φ ≫
        thomPairOverSingularHomologyFinrankInv K F E W' =
      TopPair.singularHomologyMap (thomPairOverMap F E h) (ModuleCat.of K K) (finrank ℝ F) := by
  rw [reassoc_of% hΦ, thomPairOverSingularHomologyFinrankInv_naturality, IsIso.inv_hom_id_assoc]

/-- **The Mayer–Vietoris step**: if the maps over the open sets `U` and `V` are isomorphisms, the
map over `U ∩ V` is surjective and the homology of the Thom pair over `U ∩ V` vanishes in degree
`r - 1`, the map over `U ∪ V` is an isomorphism. -/
private theorem isIso_thomPairOverSingularHomologyFinrankInv_union {U V : Set B} (hU : IsOpen U)
    (hV : IsOpen V) [IsIso (thomPairOverSingularHomologyFinrankInv K F E U)]
    [IsIso (thomPairOverSingularHomologyFinrankInv K F E V)]
    [Epi (thomPairOverSingularHomologyFinrankInv K F E (U ∩ V))]
    (hUV : ∀ m, m + 1 = finrank ℝ F →
      IsZero ((thomPairOver F E (U ∩ V)).singularHomology (ModuleCat.of K K) m)) :
    IsIso (thomPairOverSingularHomologyFinrankInv K F E (U ∪ V)) := by
  let ψ := thomPairOverSingularHomologyFinrankInv K F E
  let H₀ := (singularHomologyFunctor (ModuleCat.{w} K) 0).obj (ModuleCat.of K K)
  let S := ShortComplex.mk _ _ (singularHomology_thomPairOver_mayerVietoris_comp_eq_zero
    (F := F) (E := E) (U := U) (V := V) (ModuleCat.of K K) (finrank ℝ F))
  have hS : S.Exact :=
    singularHomology_thomPairOver_mayerVietoris_exact (ModuleCat.of K K) hU hV _
  have : Epi S.g := epi_singularHomology_thomPairOver_union (ModuleCat.of K K) hU hV hUV
  -- The inverse map, on the middle term of the Mayer–Vietoris sequence.
  let φ : S.X₂ ⟶ H₀.obj (TopCat.of ↥(U ∪ V)) :=
    biprod.desc (inv (ψ U) ≫ H₀.map (TopCat.ofHom (ContinuousMap.inclusion subset_union_left)))
      (inv (ψ V) ≫ H₀.map (TopCat.ofHom (ContinuousMap.inclusion subset_union_right)))
  -- It vanishes on the image of the first map, since both restrictions of a class over `U ∩ V`
  -- give the same class over `U ∪ V`.
  have hφ : S.f ≫ φ = 0 := by
    rw [← cancel_epi (ψ (U ∩ V)), comp_zero]
    simp only [S, φ, ψ, H₀, biprod.lift_desc, Preadditive.neg_comp, Preadditive.comp_add,
      Preadditive.comp_neg,
      thomPairOverSingularHomologyFinrankInv_comp_singularHomologyMap_comp_inv_assoc,
      ← Functor.map_comp, ← TopCat.ofHom_comp, ContinuousMap.inclusion_comp_inclusion,
      add_neg_eq_zero]
  let Φ := (hS.gIsCokernel).desc (CokernelCofork.ofπ φ hφ)
  have hgΦ : S.g ≫ Φ = φ := (hS.gIsCokernel).fac (CokernelCofork.ofπ φ hφ) WalkingParallelPair.one
  -- On the classes over `U` and over `V`, `Φ` is the inverse of the map over `U` or `V`.
  have hΦ {W : Set B} (hW : W ⊆ U ∪ V) [IsIso (ψ W)]
      (j : (thomPairOver F E W).singularHomology (ModuleCat.of K K) (finrank ℝ F) ⟶ S.X₂)
      (hj : j ≫ S.g = TopPair.singularHomologyMap (thomPairOverMap F E hW) (ModuleCat.of K K)
        (finrank ℝ F))
      (hjφ : j ≫ φ = inv (ψ W) ≫ H₀.map (TopCat.ofHom (ContinuousMap.inclusion hW))) :
      TopPair.singularHomologyMap (thomPairOverMap F E hW) (ModuleCat.of K K) (finrank ℝ F) ≫ Φ =
        inv (ψ W) ≫ H₀.map (TopCat.ofHom (ContinuousMap.inclusion hW)) := by
    rw [← hj, Category.assoc, hgΦ, hjφ]
  have hΦU := hΦ subset_union_left biprod.inl (biprod.inl_desc _ _) (biprod.inl_desc _ _)
  have hΦV := hΦ subset_union_right biprod.inr (biprod.inr_desc _ _) (biprod.inr_desc _ _)
  refine ⟨Φ, singularHomology₀_hom_ext _ fun x ↦ ?_, (cancel_epi S.g).1 (biprod.hom_ext' _ _ ?_ ?_)⟩
  · -- A point of `U ∪ V` lies in `U` or in `V`, where the composite is computed.
    rw [Category.comp_id]
    obtain ⟨x, hx | hx⟩ := x
    · exact singularHomology₀Section_thomPairOverSingularHomologyFinrankInv_comp_of_comp_eq _ hΦU
        ⟨x, hx⟩
    · exact singularHomology₀Section_thomPairOverSingularHomologyFinrankInv_comp_of_comp_eq _ hΦV
        ⟨x, hx⟩
  -- The second map of the Mayer–Vietoris sequence is an epimorphism.
  · simpa [S] using singularHomologyMap_thomPairOverMap_comp_comp_of_comp_eq _ hΦU
  · simpa [S] using singularHomologyMap_thomPairOverMap_comp_comp_of_comp_eq _ hΦV

/-- **Finite unions of trivializing open sets**: the map is an isomorphism over a finite union of
open sets each lying in the base set of a linear trivialization. -/
private theorem isIso_thomPairOverSingularHomologyFinrankInv_biUnion {ι : Type*} (s : Finset ι)
    {W : ι → Set B} (hWo : ∀ i ∈ s, IsOpen (W i))
    (hWe : ∀ i ∈ s, ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), W i ⊆ e.baseSet) :
    IsIso (thomPairOverSingularHomologyFinrankInv K F E (⋃ i ∈ s, W i)) := by
  classical
  induction s using Finset.induction_on generalizing W with
  | empty =>
    rw [show (⋃ i ∈ (∅ : Finset ι), W i) = ∅ by simp]
    exact isIso_thomPairOverSingularHomologyFinrankInv_empty
  | insert a s _ ih =>
    rw [Finset.set_biUnion_insert]
    obtain ⟨e, _, he⟩ := hWe a (Finset.mem_insert_self a s)
    have : IsIso (thomPairOverSingularHomologyFinrankInv K F E (W a)) :=
      isIso_thomPairOverSingularHomologyFinrankInv_of_subset e he
    have : IsIso (thomPairOverSingularHomologyFinrankInv K F E (⋃ i ∈ s, W i)) :=
      ih (fun i hi ↦ hWo i (Finset.mem_insert_of_mem hi))
        (fun i hi ↦ hWe i (Finset.mem_insert_of_mem hi))
    -- `W a ∩ ⋃ i ∈ s, W i` is the union of the trivializing open sets `W a ∩ W i`, `i ∈ s`.
    have : IsIso (thomPairOverSingularHomologyFinrankInv K F E (W a ∩ ⋃ i ∈ s, W i)) := by
      rw [inter_iUnion₂]
      refine ih (fun i hi ↦ (hWo a (Finset.mem_insert_self a s)).inter
        (hWo i (Finset.mem_insert_of_mem hi))) fun i hi ↦ ?_
      obtain ⟨e', he', hi'⟩ := hWe i (Finset.mem_insert_of_mem hi)
      exact ⟨e', he', inter_subset_right.trans hi'⟩
    exact isIso_thomPairOverSingularHomologyFinrankInv_union (hWo a (Finset.mem_insert_self a s))
      (isOpen_iUnion fun i ↦ isOpen_iUnion fun hi ↦ hWo i (Finset.mem_insert_of_mem hi))
      fun m hm ↦ e.isZero_singularHomology_thomPairOver (inter_subset_left.trans he) _ (by omega)

/-! ### The passage to the whole base -/

variable (K F E) in
/-- The map `H₀(B; K) ⟶ Hᵣ(E, E₀; K)` sending the class of a point to the fibre class over it. -/
private def thomPairSingularHomologyFinrankInv :
    ((singularHomologyFunctor (ModuleCat.{w} K) 0).obj (ModuleCat.of K K)).obj (TopCat.of B) ⟶
      (thomPair F E).singularHomology (ModuleCat.of K K) (finrank ℝ F) :=
  ((singularHomologyFunctor (ModuleCat.{w} K) 0).obj (ModuleCat.of K K)).map
      (TopCat.isoOfHomeo (Homeomorph.Set.univ B).symm).hom ≫
    thomPairOverSingularHomologyFinrankInv K F E univ ≫
      TopPair.singularHomologyMap (thomPairOverUnivIso F E).hom (ModuleCat.of K K) (finrank ℝ F)

private theorem singularHomology₀Section_thomPairSingularHomologyFinrankInv (b : B) :
    singularHomology₀Section (ModuleCat.of K K) (X := TopCat.of B) b ≫
        thomPairSingularHomologyFinrankInv K F E =
      ModuleCat.ofHom (LinearMap.toSpanSingleton K _ (TopPair.singularHomologyMap
        (fiberThomPairMap F E b) (ModuleCat.of K K) (finrank ℝ F) (fiberGenerator K F E b))) := by
  rw [thomPairSingularHomologyFinrankInv, singularHomology₀Section_naturality_assoc,
    singularHomology₀Section_thomPairOverSingularHomologyFinrankInv_assoc,
    ModuleCat.ofHom_toSpanSingleton_comp, fiberClassOver, ← ConcreteCategory.comp_apply,
    ← TopPair.singularHomologyMap_comp]
  exact congrArg (fun f ↦ ModuleCat.ofHom (LinearMap.toSpanSingleton K _
    (TopPair.singularHomologyMap f (ModuleCat.of K K) (finrank ℝ F) (fiberGenerator K F E b))))
    (fiberThomPairOverMap_comp_thomPairOverUnivIso_hom F E b)

/-- On a finite union of the chosen trivializing sets, the map over the base restricts to the
map over the union. -/
private theorem thomPairSingularHomologyFinrankInv_restrict (s : Finset B) :
    ((singularHomologyFunctor (ModuleCat.{w} K) 0).obj (ModuleCat.of K K)).map
        (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ :
          TopCat.of ↥(⋃ b ∈ s, (trivializationAt F E b).baseSet) ⟶ TopCat.of B) ≫
        thomPairSingularHomologyFinrankInv K F E =
      thomPairOverSingularHomologyFinrankInv K F E (⋃ b ∈ s, (trivializationAt F E b).baseSet) ≫
        TopPair.singularHomologyMap (thomPairOverMap F E (subset_univ _) ≫
          (thomPairOverUnivIso F E).hom) (ModuleCat.of K K) (finrank ℝ F) := by
  refine singularHomology₀_hom_ext _ fun x ↦ ?_
  rw [singularHomology₀Section_naturality_assoc,
    singularHomology₀Section_thomPairSingularHomologyFinrankInv,
    singularHomology₀Section_thomPairOverSingularHomologyFinrankInv_assoc,
    ModuleCat.ofHom_toSpanSingleton_comp, fiberClassOver, ← ConcreteCategory.comp_apply,
    ← TopPair.singularHomologyMap_comp, fiberThomPairOverMap_comp_thomPairOverMap_assoc,
    fiberThomPairOverMap_comp_thomPairOverUnivIso_hom]

variable (F E) in
/-- The finite unions of the chosen trivializing open sets, as subspaces of the base: the bases of
the Thom pairs in `TauCeti.thomPairFiniteTrivializingUnionDiagram`. -/
private def baseFiniteTrivializingUnionDiagram : Finset B ⥤ TopCat.{w} where
  obj s := TopCat.of ↥(⋃ b ∈ s, (trivializationAt F E b).baseSet)
  map f := TopCat.ofHom (ContinuousMap.inclusion (biUnion_subset_biUnion_left f.le))

variable (F E) in
/-- The inclusions of the finite unions of the chosen trivializing open sets into the base. -/
private def baseFiniteTrivializingUnionCocone :
    Cocone (baseFiniteTrivializingUnionDiagram (B := B) F E) where
  pt := TopCat.of B
  ι := { app _ := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ }

variable (K F E) in
/-- The homology of the base is the filtered colimit of the homologies of the finite unions of the
chosen trivializing sets. -/
private def isColimitSingularHomologyBaseFiniteTrivializingUnion :
    IsColimit (((singularHomologyFunctor (ModuleCat.{w} K) 0).obj (ModuleCat.of K K)).mapCocone
      (baseFiniteTrivializingUnionCocone (B := B) F E)) :=
  isColimitMapCoconeSingularHomology (ModuleCat.of K K) 0
    (baseFiniteTrivializingUnionCocone F E) (fun _ ↦ IsEmbedding.subtypeVal) fun L hL ↦ by
      obtain ⟨s, hs⟩ := hL.elim_finite_subcover _
        (fun b ↦ (trivializationAt F E b).open_baseSet) fun b _ ↦
          mem_iUnion.2 ⟨b, mem_baseSet_trivializationAt F E b⟩
      exact ⟨s, fun b hb ↦ ⟨⟨b, hs hb⟩, rfl⟩⟩

/-- The map is an isomorphism over each finite union of the chosen trivializing sets. -/
private theorem isIso_thomPairOverSingularHomologyFinrankInv_finiteTrivializingUnion
    (s : Finset B) : IsIso (thomPairOverSingularHomologyFinrankInv K F E
      (⋃ b ∈ s, (trivializationAt F E b).baseSet)) :=
  isIso_thomPairOverSingularHomologyFinrankInv_biUnion s
    (fun b _ ↦ (trivializationAt F E b).open_baseSet)
    fun b _ ↦ ⟨trivializationAt F E b, inferInstance, subset_rfl⟩

omit [FiniteDimensional ℝ F] [∀ b, Module ℝ (E b)] [VectorBundle ℝ F E] [Subsingleton Kˣ] in
variable (K) in
/-- The objects of the diagram of Thom pairs are the Thom pairs over the finite unions only up to
the equations `thomPairFiniteTrivializingUnionDiagram_obj`. -/
private theorem singularHomology_thomPairOver_finiteTrivializingUnion_eq (s : Finset B) :
    (thomPairOver F E (⋃ b ∈ s, (trivializationAt F E b).baseSet)).singularHomology
        (ModuleCat.of K K) (finrank ℝ F) =
      (TopPair.singularHomologyFunctor (ModuleCat.of K K) (finrank ℝ F)).obj
        ((thomPairFiniteTrivializingUnionDiagram (F := F) (E := E)).obj s) := by
  rw [thomPairFiniteTrivializingUnionDiagram_obj, TopPair.singularHomologyFunctor_obj]

omit [FiniteDimensional ℝ F] [∀ b, Module ℝ (E b)] [VectorBundle ℝ F E] [Subsingleton Kˣ] in
variable (K) in
/-- The Thom pair is the cocone point of the diagram of Thom pairs only up to the equation
`thomPairFiniteTrivializingUnionCocone_pt`. -/
private theorem singularHomology_thomPair_eq :
    (thomPair F E).singularHomology (ModuleCat.of K K) (finrank ℝ F) =
      (TopPair.singularHomologyFunctor (ModuleCat.of K K) (finrank ℝ F)).obj
        (thomPairFiniteTrivializingUnionCocone (F := F) (E := E)).pt := by
  rw [thomPairFiniteTrivializingUnionCocone_pt, TopPair.singularHomologyFunctor_obj]

variable (K F E) in
/-- The maps over the finite unions of the chosen trivializing sets, as a natural isomorphism
between the homologies of the bases and of the Thom pairs. -/
private def thomPairFiniteTrivializingUnionSingularHomologyFinrankIso :
    baseFiniteTrivializingUnionDiagram F E ⋙
        (singularHomologyFunctor (ModuleCat.{w} K) 0).obj (ModuleCat.of K K) ≅
      thomPairFiniteTrivializingUnionDiagram (F := F) (E := E) ⋙
        TopPair.singularHomologyFunctor (ModuleCat.of K K) (finrank ℝ F) :=
  NatIso.ofComponents (fun s ↦ @asIso _ _ _ _ (thomPairOverSingularHomologyFinrankInv K F E
      (⋃ b ∈ s, (trivializationAt F E b).baseSet))
        (isIso_thomPairOverSingularHomologyFinrankInv_finiteTrivializingUnion s) ≪≫
      eqToIso (singularHomology_thomPairOver_finiteTrivializingUnion_eq K s))
    fun {s t} f ↦ by
      have := isIso_thomPairOverSingularHomologyFinrankInv_finiteTrivializingUnion (K := K)
        (F := F) (E := E) s
      have := isIso_thomPairOverSingularHomologyFinrankInv_finiteTrivializingUnion (K := K)
        (F := F) (E := E) t
      dsimp only [Functor.comp_obj, Functor.comp_map, baseFiniteTrivializingUnionDiagram]
      simp only [thomPairFiniteTrivializingUnionDiagram_map,
        TopPair.singularHomologyFunctor_map, Iso.trans_hom, asIso_hom, eqToIso.hom,
        Category.assoc, TopPair.singularHomologyMap_comp, TopPair.singularHomologyMap_eqToHom,
        eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      rw [← Category.assoc, thomPairOverSingularHomologyFinrankInv_naturality
        (W := ⋃ b ∈ s, (trivializationAt F E b).baseSet)
        (W' := ⋃ b ∈ t, (trivializationAt F E b).baseSet) (biUnion_subset_biUnion_left f.le),
        Category.assoc, eqToHom_trans]

/-- On a finite union of the chosen trivializing sets, the map over the base is the map over the
union followed by the inclusion into the whole Thom pair: these are the components of
`thomPairFiniteTrivializingUnionSingularHomologyFinrankIso` and the inclusions of the colimit
cocones. -/
private theorem singularHomologyMap_ι_thomPairSingularHomologyFinrankInv (s : Finset B) :
    ((singularHomologyFunctor (ModuleCat.{w} K) 0).obj (ModuleCat.of K K)).map
        (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ :
          TopCat.of ↥(⋃ b ∈ s, (trivializationAt F E b).baseSet) ⟶ TopCat.of B) ≫
        thomPairSingularHomologyFinrankInv K F E ≫ eqToHom (singularHomology_thomPair_eq K) =
      thomPairOverSingularHomologyFinrankInv K F E (⋃ b ∈ s, (trivializationAt F E b).baseSet) ≫
        eqToHom (singularHomology_thomPairOver_finiteTrivializingUnion_eq K s) ≫
          (TopPair.singularHomologyFunctor (ModuleCat.of K K) (finrank ℝ F)).map
            ((thomPairFiniteTrivializingUnionCocone (F := F) (E := E)).ι.app s) := by
  rw [reassoc_of% (thomPairSingularHomologyFinrankInv_restrict (K := K) s)]
  simp only [thomPairFiniteTrivializingUnionCocone_ι_app, TopPair.singularHomologyFunctor_map,
    Category.assoc, TopPair.singularHomologyMap_comp, TopPair.singularHomologyMap_eqToHom,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, eqToHom_trans]

/-- **The passage to the whole base**: the homologies of the base and of the Thom pair are the
filtered colimits of their homologies over the finite unions of the chosen trivializing sets, and
over these the map is an isomorphism. -/
private instance : IsIso (thomPairSingularHomologyFinrankInv K F E) := by
  let P₁ := isColimitSingularHomologyBaseFiniteTrivializingUnion K F E
  let P₂ := isColimitMapCoconeSingularHomologyThomPairFiniteTrivializingUnion (F := F) (E := E)
    (ModuleCat.of K K) (finrank ℝ F)
  let α := thomPairFiniteTrivializingUnionSingularHomologyFinrankIso K F E
  have h : thomPairSingularHomologyFinrankInv K F E ≫ eqToHom (singularHomology_thomPair_eq K) =
      (P₁.coconePointsIsoOfNatIso P₂ α).hom :=
    P₁.hom_ext fun s ↦ (singularHomologyMap_ι_thomPairSingularHomologyFinrankInv s).trans
      (P₁.comp_coconePointsIsoOfNatIso_hom P₂ α s).symm
  have : IsIso (thomPairSingularHomologyFinrankInv K F E ≫
      eqToHom (singularHomology_thomPair_eq K)) := by
    rw [h]
    exact (P₁.coconePointsIsoOfNatIso P₂ α).isIso_hom
  exact IsIso.of_isIso_comp_right _ (eqToHom (singularHomology_thomPair_eq K))

variable (K F E) in
/-- **The homology of the Thom pair in the rank degree**: for a real vector bundle `E → B` of
rank `r`, with Thom pair `(E, E₀)`, and a commutative ring `K` whose only unit is `1`, such as
`ZMod 2`, `Hᵣ(E, E₀; K) ≅ H₀(B; K)`. It sends the fibre class over `b` to the class of `b`
(`TauCeti.thomPairSingularHomologyFinrankIso_hom_apply`). The base is arbitrary and the bundle
need not be orientable. -/
def thomPairSingularHomologyFinrankIso :
    (thomPair F E).singularHomology (ModuleCat.of K K) (finrank ℝ F) ≅
      ((singularHomologyFunctor (ModuleCat.{w} K) 0).obj (ModuleCat.of K K)).obj (TopCat.of B) :=
  (asIso (thomPairSingularHomologyFinrankInv K F E)).symm

/-- **The isomorphism `Hᵣ(E, E₀; K) ≅ H₀(B; K)` sends the fibre class over `b` to the class of
`b`**: the fibre class is the image of any generator of `Hᵣ(E_b, E_b ∖ {0}; K) ≅ K` under the
inclusion of the fibre pair. -/
theorem thomPairSingularHomologyFinrankIso_hom_apply (b : B)
    {x : ((TopPair.ofSubset (X := TopCat.of (E b)) ({0}ᶜ : Set (E b))).singularHomology
      (ModuleCat.of K K) (finrank ℝ F) : ModuleCat.{w} K)} (hx : Submodule.span K {x} = ⊤) :
    (thomPairSingularHomologyFinrankIso K F E).hom
        (TopPair.singularHomologyMap (fiberThomPairMap F E b) (ModuleCat.of K K) (finrank ℝ F) x) =
      singularHomology₀Section (ModuleCat.of K K) (X := TopCat.of B) b 1 := by
  have h := congrArg (fun f ↦ f (1 : K))
    (singularHomology₀Section_thomPairSingularHomologyFinrankInv (K := K) (F := F) (E := E) b)
  simp only [ModuleCat.hom_ofHom, LinearMap.toSpanSingleton_apply, one_smul,
    ConcreteCategory.comp_apply] at h
  rw [eq_fiberGenerator hx, ← h, thomPairSingularHomologyFinrankIso, Iso.symm_hom, asIso_inv,
    ← ConcreteCategory.comp_apply, IsIso.hom_inv_id, ConcreteCategory.id_apply]

end Bundle

/-! ### Twisted coefficients: the orientation local system -/

section Model

variable (K : Type w) [CommRing K] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {ι : Type*} [Fintype ι]

open scoped Classical in
/-- The generator of `Hᵣ(F, F ∖ {0}; K)` attached to an orientation `ω'` of `F`, normalized by a
model orientation `ω`: the generator `complZeroPairGenerator K F` for `ω' = ω`, its negative
otherwise. -/
private def orientationModelGenerator (ω ω' : Orientation ℝ F ι) :
    ((TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularHomology (ModuleCat.of K K)
      (finrank ℝ F) : ModuleCat.{w} K) :=
  if ω' = ω then complZeroPairGenerator K F else -complZeroPairGenerator K F

omit [Fintype ι] in
private theorem orientationModelGenerator_self (ω : Orientation ℝ F ι) :
    orientationModelGenerator K ω ω = complZeroPairGenerator K F := by
  simp [orientationModelGenerator]

variable {K} (hι : Fintype.card ι = finrank ℝ F)
include hι

private theorem orientationModelGenerator_neg (ω ω' : Orientation ℝ F ι) :
    orientationModelGenerator K ω (-ω') = -orientationModelGenerator K ω ω' := by
  rcases ω'.eq_or_eq_neg ω hι with rfl | rfl
  · simp [orientationModelGenerator, (Module.Ray.ne_neg_self ω').symm]
  · rw [show - -ω = ω from neg_neg ω]
    simp [orientationModelGenerator, (Module.Ray.ne_neg_self ω).symm]

/-- A linear automorphism of `F` carries the generator of an orientation to the generator of its
image: it acts on `Hᵣ(F, F ∖ {0})` by the sign of its determinant, which is also how it acts on
orientations. -/
private theorem singularHomologyMap_complZeroPairIso_hom_orientationModelGenerator
    (ω ω' : Orientation ℝ F ι) (T : F ≃L[ℝ] F) :
    TopPair.singularHomologyMap T.complZeroPairIso.hom (ModuleCat.of K K) (finrank ℝ F)
        (orientationModelGenerator K ω ω') =
      orientationModelGenerator K ω (Orientation.map ι T.toLinearEquiv ω') := by
  have hT : TopPair.singularHomologyMap T.complZeroPairIso.hom (ModuleCat.of K K) (finrank ℝ F) =
      (SignType.sign (T : F →L[ℝ] F).det : ℤ) • 𝟙 _ := by
    rw [T.complZeroPairIso_hom]
    exact singularHomologyMap_continuousLinearMap_compl_zero _ _ _ _
  rw [hT]
  -- `ContinuousLinearMap.det` is by definition the determinant of the underlying linear map.
  have hdet : (T : F →L[ℝ] F).det ≠ 0 := T.toLinearEquiv.isUnit_det'.ne_zero
  rcases hdet.lt_or_gt with h | h
  · rw [(Orientation.map_eq_neg_iff_det_neg _ _ hι).2 h, orientationModelGenerator_neg hι,
      sign_neg h]
    simp
  · rw [(Orientation.map_eq_iff_det_pos _ _ hι).2 h, sign_pos h]
    simp

end Model

section Twisted

variable {K : Type w} [CommRing K] {B : Type w} [TopologicalSpace B] {F : Type w}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {E : B → Type w}
  [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)]
  [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]
  {ι : Type} [Fintype ι] (hι : Fintype.card ι = finrank ℝ F) (ω : Orientation ℝ F ι)

omit [VectorBundle ℝ F E] in
include hι in
/-- Two linear trivializations read the generator of an orientation of a fibre as the same class
of the fibre pair: the coordinate change at `b` acts on `Hᵣ(F, F ∖ {0})` and on the orientations
of `F` by the same sign. -/
private theorem singularHomologyMap_complZeroPairIso_inv_orientationModelGenerator
    (e e' : Trivialization F (π F E)) [e.IsLinear ℝ] [e'.IsLinear ℝ] {b : B}
    (hb : b ∈ e.baseSet) (hb' : b ∈ e'.baseSet) (o : Orientation ℝ (E b) ι) :
    TopPair.singularHomologyMap (e'.continuousLinearEquivAt ℝ b hb').complZeroPairIso.inv
        (ModuleCat.of K K) (finrank ℝ F)
        (orientationModelGenerator K ω (e'.mapOrientation ι hb' o)) =
      TopPair.singularHomologyMap (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.inv
        (ModuleCat.of K K) (finrank ℝ F)
        (orientationModelGenerator K ω (e.mapOrientation ι hb o)) := by
  rw [e.mapOrientation_eq_map_coordChangeL e' hb hb',
    ← e.continuousLinearEquivAt_trans_coordChangeL ℝ e' hb hb',
    ContinuousLinearEquiv.complZeroPairIso_trans, Iso.trans_inv, TopPair.singularHomologyMap_comp,
    ConcreteCategory.comp_apply]
  congr 1
  rw [← Iso.symm_hom, ← ContinuousLinearEquiv.complZeroPairIso_symm,
    singularHomologyMap_complZeroPairIso_hom_orientationModelGenerator hι,
    ContinuousLinearEquiv.toLinearEquiv_symm, ← Orientation.map_symm, Equiv.symm_apply_apply]

variable (K) in
/-- The generator of `Hᵣ(E_b, E_b ∖ {0}; K)` of an orientation `o` of the fibre `E_b`, normalized
by the model orientation `ω`: a linear trivialization reading `o` as `ω` carries it to
`complZeroPairGenerator K F`. -/
private def orientedFiberGenerator {b : B} (o : Orientation ℝ (E b) ι) :
    ((TopPair.ofSubset (X := TopCat.of (E b)) ({0}ᶜ : Set (E b))).singularHomology
      (ModuleCat.of K K) (finrank ℝ F) : ModuleCat.{w} K) :=
  TopPair.singularHomologyMap ((trivializationAt F E b).continuousLinearEquivAt ℝ b
      (mem_baseSet_trivializationAt F E b)).complZeroPairIso.inv (ModuleCat.of K K) (finrank ℝ F)
    (orientationModelGenerator K ω
      ((trivializationAt F E b).mapOrientation ι (mem_baseSet_trivializationAt F E b) o))

include hι in
/-- The generator of an orientation, read in any linear trivialization. -/
private theorem orientedFiberGenerator_eq (e : Trivialization F (π F E)) [e.IsLinear ℝ] {b : B}
    (hb : b ∈ e.baseSet) (o : Orientation ℝ (E b) ι) :
    orientedFiberGenerator K ω o =
      TopPair.singularHomologyMap (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.inv
        (ModuleCat.of K K) (finrank ℝ F)
        (orientationModelGenerator K ω (e.mapOrientation ι hb o)) :=
  singularHomologyMap_complZeroPairIso_inv_orientationModelGenerator hι ω e _ hb _ o

include hι in
private theorem orientedFiberGenerator_neg {b : B} (o : Orientation ℝ (E b) ι) :
    orientedFiberGenerator K ω (-o) = -orientedFiberGenerator K ω o := by
  rw [orientedFiberGenerator, Trivialization.mapOrientation_neg,
    orientationModelGenerator_neg hι, map_neg, orientedFiberGenerator]

omit [VectorBundle ℝ F E] in
/-- Over a product, the fibre inclusions over two points joined by a path agree in homology. -/
private theorem singularHomologyMap_prodThomPairFiberMap_eq_of_joined {W : Type w}
    [TopologicalSpace W] {x y : W} (h : Joined x y)
    (g : ((TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularHomology
      (ModuleCat.of K K) (finrank ℝ F) : ModuleCat.{w} K)) :
    TopPair.singularHomologyMap (prodThomPairFiberMap F x) (ModuleCat.of K K) (finrank ℝ F) g =
      TopPair.singularHomologyMap (prodThomPairFiberMap F y) (ModuleCat.of K K) (finrank ℝ F)
        g := by
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1
    ((span_complZeroPairGenerator K F).symm ▸ Submodule.mem_top (x := g))
  rw [map_smul, map_smul, singularHomologyMap_prodThomPairFiberMap_complZeroPairGenerator,
    singularHomologyMap_prodThomPairFiberMap_complZeroPairGenerator,
    singularHomology₀Section_eq_of_joined _ h]

omit [FiniteDimensional ℝ F] [VectorBundle ℝ F E] in
/-- Read through a linear trivialization, the inclusion of the fibre pair over `z` into the Thom
pair factors through the fibre inclusion of the product bundle over the base set. -/
private theorem complZeroPairIso_inv_comp_fiberThomPairMap (e : Trivialization F (π F E))
    [e.IsLinear ℝ] {z : B} (hz : z ∈ e.baseSet) :
    (e.continuousLinearEquivAt ℝ z hz).complZeroPairIso.inv ≫ fiberThomPairMap F E z =
      prodThomPairFiberMap F (⟨z, hz⟩ : e.baseSet) ≫ (e.thomPairOverIso ℝ subset_rfl).inv ≫
        thomPairOverMap F E (subset_univ _) ≫ (thomPairOverUnivIso F E).hom := by
  have h : (e.continuousLinearEquivAt ℝ z hz).complZeroPairIso.inv ≫
      fiberThomPairOverMap F E hz = prodThomPairFiberMap F (⟨z, hz⟩ : e.baseSet) ≫
        (e.thomPairOverIso ℝ subset_rfl).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    exact e.fiberThomPairOverMap_comp_thomPairOverIso_hom ℝ subset_rfl hz
  rw [← fiberThomPairOverMap_comp_thomPairOverUnivIso_hom,
    ← fiberThomPairOverMap_comp_thomPairOverMap F E (subset_univ _) hz, Category.assoc,
    reassoc_of% h]

omit [VectorBundle ℝ F E] in
/-- The fibre classes of a fixed class of `Hᵣ(F, F ∖ {0})`, read through a linear trivialization
over two points joined by a path in its base set, agree. -/
private theorem singularHomologyMap_fiberThomPairMap_eq_of_joinedIn
    (e : Trivialization F (π F E)) [e.IsLinear ℝ] {x y : B} (hx : x ∈ e.baseSet)
    (hy : y ∈ e.baseSet) (h : JoinedIn e.baseSet x y)
    (g : ((TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularHomology
      (ModuleCat.of K K) (finrank ℝ F) : ModuleCat.{w} K)) :
    TopPair.singularHomologyMap (fiberThomPairMap F E x) (ModuleCat.of K K) (finrank ℝ F)
        (TopPair.singularHomologyMap (e.continuousLinearEquivAt ℝ x hx).complZeroPairIso.inv
          (ModuleCat.of K K) (finrank ℝ F) g) =
      TopPair.singularHomologyMap (fiberThomPairMap F E y) (ModuleCat.of K K) (finrank ℝ F)
        (TopPair.singularHomologyMap (e.continuousLinearEquivAt ℝ y hy).complZeroPairIso.inv
          (ModuleCat.of K K) (finrank ℝ F) g) := by
  simp only [← ConcreteCategory.comp_apply, ← TopPair.singularHomologyMap_comp,
    complZeroPairIso_inv_comp_fiberThomPairMap]
  simp only [TopPair.singularHomologyMap_comp, ConcreteCategory.comp_apply]
  rw [singularHomologyMap_prodThomPairFiberMap_eq_of_joined h.joined_subtype]

open VectorBundleOrientationCover

variable (K) in
/-- The fibre class in `Hᵣ(E, E₀; K)` of a point of the orientation double cover: the image of
the generator of its orientation under the inclusion of the fibre pair. -/
private def coverFiberClass (p : VectorBundleOrientationCover F E ι) :
    ((thomPair F E).singularHomology (ModuleCat.of K K) (finrank ℝ F) : ModuleCat.{w} K) :=
  TopPair.singularHomologyMap (fiberThomPairMap F E p.proj) (ModuleCat.of K K) (finrank ℝ F)
    (orientedFiberGenerator K ω p.orientation)

omit [Fintype ι] in
private theorem coverFiberClass_mk {b : B} (o : Orientation ℝ (E b) ι) :
    coverFiberClass K ω ⟨b, o⟩ = TopPair.singularHomologyMap (fiberThomPairMap F E b)
      (ModuleCat.of K K) (finrank ℝ F) (orientedFiberGenerator K ω o) :=
  rfl

include hι in
/-- Two points on the same sheet of a linear trivialization over points joined in its base set
have the same fibre class. -/
private theorem coverFiberClass_eq_of_mem_sheet (e : Trivialization F (π F E)) [e.IsLinear ℝ]
    {ω' : Orientation ℝ F ι} {p q : VectorBundleOrientationCover F E ι} (hp : p ∈ sheet e ω')
    (hq : q ∈ sheet e ω') (h : JoinedIn e.baseSet p.proj q.proj) :
    coverFiberClass K ω p = coverFiberClass K ω q := by
  obtain ⟨hpe, hp⟩ := mem_sheet_iff.1 hp
  obtain ⟨hqe, hq⟩ := mem_sheet_iff.1 hq
  rw [coverFiberClass, coverFiberClass, orientedFiberGenerator_eq hι ω e hpe,
    orientedFiberGenerator_eq hι ω e hqe, hp, hq]
  exact singularHomologyMap_fiberThomPairMap_eq_of_joinedIn e hpe hqe h _

include hι in
/-- **The fibre classes are constant along paths in the orientation double cover.** -/
private theorem coverFiberClass_apply_zero
    (Γ : C(unitInterval, VectorBundleOrientationCover F E ι)) :
    coverFiberClass K ω (Γ 0) = coverFiberClass K ω (Γ 1) := by
  have : LocallyPathConnectedSpace unitInterval :=
    Convex.locallyPathConnectedSpace ℝ (convex_Icc (0 : ℝ) 1)
  have hlc : IsLocallyConstant fun t ↦ coverFiberClass K ω (Γ t) := by
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun t ↦ ?_
    -- Near `t` the path stays on the sheet through `Γ t` of the preferred trivialization.
    let e := trivializationAt F E (Γ t).proj
    let ω' := e.mapOrientation ι (mem_baseSet_trivializationAt F E _) (Γ t).orientation
    have ht : Γ t ∈ sheet e ω' := mem_sheet_iff.2 ⟨mem_baseSet_trivializationAt F E _, rfl⟩
    have hS : Γ ⁻¹' sheet e ω' ∈ 𝓝 t :=
      ((isOpen_sheet hι e ω').preimage Γ.continuous).mem_nhds ht
    filter_upwards [pathComponentIn_mem_nhds hS] with s hs
    refine (coverFiberClass_eq_of_mem_sheet hι ω e ht hs.target_mem ?_).symm
    refine (hs.map (continuous_proj.comp Γ.continuous).continuousOn).mono ?_
    rintro _ ⟨u, hu, rfl⟩
    exact (mem_sheet_iff.1 hu).1
  simpa using hlc.apply_eq_of_preconnectedSpace 0 1

include hι in
/-- Monodromy in the orientation double cover preserves the fibre classes. -/
private theorem coverFiberClass_monodromy {x y : B} (P : Path.Homotopic.Quotient x y)
    (q : (proj ⁻¹' {x} : Set (VectorBundleOrientationCover F E ι))) :
    coverFiberClass K ω ((isCoveringMap_proj (F := F) (E := E) hι).monodromy P q : _) =
      coverFiberClass K ω q.1 := by
  induction P using Path.Homotopic.Quotient.ind with
  | mk γ =>
    rw [IsCoveringMap.coe_monodromy_mk, ← coverFiberClass_apply_zero hι ω,
      IsCoveringMap.liftPath_zero]

include hι in
private theorem coverFiberClass_mk_neg {b : B} (o : Orientation ℝ (E b) ι) :
    coverFiberClass K ω ⟨b, -o⟩ = -coverFiberClass K ω ⟨b, o⟩ := by
  rw [coverFiberClass, coverFiberClass, orientedFiberGenerator_neg hι, map_neg]

/-- The orientation of the fibre over `b` that the preferred trivialization at `b` reads as the
model orientation `ω`. -/
private def modelFiberOrientation (b : B) : Orientation ℝ (E b) ι :=
  ((trivializationAt F E b).mapOrientation ι (mem_baseSet_trivializationAt F E b)).symm ω

variable (K) in
/-- The map from the fibre of the orientation local system over `b` to `Hᵣ(E, E₀; K)`: a
function `f` on the orientations of `E_b` goes to `f o` times the fibre class of `o`, for any
orientation `o`. -/
private def twistedFiberClass (b : B) :
    (signLocalSystem F E K hι).obj (FundamentalGroupoid.mk b) ⟶
      (thomPair F E).singularHomology (ModuleCat.of K K) (finrank ℝ F) :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton K _
      (coverFiberClass K ω ⟨b, modelFiberOrientation ω b⟩) ∘ₗ
    (signLocalSystemFiberEquiv (R := K) hι (modelFiberOrientation ω b)).toLinearMap)

/-- The value of `twistedFiberClass` on `f`, computed at any point `q` of the double cover over
`b`. -/
private theorem twistedFiberClass_apply {b : B}
    (q : (proj ⁻¹' {b} : Set (VectorBundleOrientationCover F E ι)))
    (f : (signLocalSystem F E K hι).obj (FundamentalGroupoid.mk b)) :
    twistedFiberClass K hι ω b f =
      (signLocalSystemObjEquiv hι (FundamentalGroupoid.mk b) f :
        (proj ⁻¹' {b} : Set (VectorBundleOrientationCover F E ι)) → K) q •
        coverFiberClass K ω q.1 := by
  obtain ⟨⟨b', o⟩, hq⟩ := q
  obtain rfl : b' = b := hq
  rw [← signLocalSystemFiberEquiv_apply]
  set e := trivializationAt F E b'
  rcases (e.mapOrientation ι (mem_baseSet_trivializationAt F E b') o).eq_or_eq_neg ω hι with h | h
  · obtain rfl : o = modelFiberOrientation ω b' := (Equiv.eq_symm_apply _).2 h
    -- This is the definition of `twistedFiberClass`.
    rfl
  · obtain rfl : o = -modelFiberOrientation ω b' := by
      apply (e.mapOrientation ι (mem_baseSet_trivializationAt F E b')).injective
      rw [h, Trivialization.mapOrientation_neg, modelFiberOrientation, Equiv.apply_symm_apply]
    rw [signLocalSystemFiberEquiv_neg, coverFiberClass_mk_neg hι, neg_smul_neg]
    -- This is the definition of `twistedFiberClass`.
    rfl

variable (K) in
/-- The fibre classes form a cocone over the orientation local system: transport along a path
corresponds to monodromy in the orientation double cover, which preserves the fibre classes. -/
private def twistedFiberCocone : Cocone (signLocalSystem F E K hι) where
  pt := (thomPair F E).singularHomology (ModuleCat.of K K) (finrank ℝ F)
  ι :=
    { app x := twistedFiberClass K hι ω x.as
      naturality x y P := by
        refine ModuleCat.hom_ext (LinearMap.ext fun f ↦ ?_)
        let q : (proj ⁻¹' {y.as} : Set (VectorBundleOrientationCover F E ι)) :=
          ⟨⟨y.as, modelFiberOrientation ω y.as⟩, rfl⟩
        simp only [Functor.const_obj_map, ModuleCat.hom_comp, LinearMap.comp_apply]
        rw [twistedFiberClass_apply hι ω q, signLocalSystemObjEquiv_map_apply,
          ← coverFiberClass_monodromy hι ω (inv P) q, ← twistedFiberClass_apply]
        -- The remaining identity morphism is that of the constant functor.
        rfl }

variable (K) in
/-- The map `H₀(B; o(E) ⊗ K) ⟶ Hᵣ(E, E₀; K)` sending the class of `f` in the fibre over `b` to
`twistedFiberClass`. -/
private def twistedHomologyThomPairDesc :
    LocalCoefficientSystem.twistedHomology.{w, w, w} (signLocalSystem F E K hι) 0 ⟶
      (thomPair F E).singularHomology (ModuleCat.of K K) (finrank ℝ F) :=
  (LocalCoefficientSystem.isColimitTwistedHomology₀Cocone.{w, w, w} _).desc
    (twistedFiberCocone K hι ω)

@[reassoc]
private theorem ιTwistedHomology₀_twistedHomologyThomPairDesc (b : B) :
    LocalCoefficientSystem.ιTwistedHomology₀.{w, w, w} (signLocalSystem F E K hι) b ≫
        twistedHomologyThomPairDesc K hι ω =
      twistedFiberClass K hι ω b :=
  (LocalCoefficientSystem.isColimitTwistedHomology₀Cocone.{w, w, w} _).fac
    (twistedFiberCocone K hι ω) (FundamentalGroupoid.mk b)

/-! ### The comparison map out of the Thom pair -/

omit [Fintype ι] in
private theorem span_orientedFiberGenerator {b : B} (o : Orientation ℝ (E b) ι) :
    Submodule.span K {orientedFiberGenerator K ω o} = ⊤ := by
  refine (ModuleCat.span_singleton_apply_eq_top_iff _).2 ?_
  rw [orientationModelGenerator]
  split_ifs
  · exact span_complZeroPairGenerator K F
  · rw [← Set.neg_singleton, Submodule.span_neg]
    exact span_complZeroPairGenerator K F

omit [Fintype ι] in
/-- Morphisms out of `Hᵣ(E_b, E_b ∖ {0}; K)` are determined by their value on the generator of
one orientation. -/
private theorem orientedFiberGenerator_hom_ext {b : B} (o : Orientation ℝ (E b) ι)
    {T : ModuleCat.{w} K}
    {g g' : (TopPair.ofSubset (X := TopCat.of (E b)) ({0}ᶜ : Set (E b))).singularHomology
      (ModuleCat.of K K) (finrank ℝ F) ⟶ T}
    (h : g (orientedFiberGenerator K ω o) = g' (orientedFiberGenerator K ω o)) : g = g' :=
  ModuleCat.hom_ext (LinearMap.ext_on (span_orientedFiberGenerator ω o) fun _ hx ↦ by
    rw [Set.mem_singleton_iff.1 hx]
    exact h)

/-- The fibre generator of an orientation `o` of `E_b` as a class of the fibre of the orientation
local system: the function on orientations taking the value `1` at `o`. -/
private abbrev signFiberOne {b : B} (o : Orientation ℝ (E b) ι) :
    (signLocalSystem F E K hι).obj (FundamentalGroupoid.mk b) :=
  (signLocalSystemFiberEquiv hι o).symm 1

omit [FiniteDimensional ℝ F] in
private theorem signFiberOne_neg {b : B} (o : Orientation ℝ (E b) ι) :
    signFiberOne (K := K) hι (-o) = -signFiberOne hι o := by
  apply (signLocalSystemFiberEquiv (R := K) hι o).injective
  rw [map_neg, LinearEquiv.apply_symm_apply, ← neg_eq_iff_eq_neg,
    ← signLocalSystemFiberEquiv_neg, LinearEquiv.apply_symm_apply]

variable (K) in
/-- A morphism from `Hᵣ(E|_W, E₀|_W; K)` to the twisted zeroth homology sending the fibre class
of the generator of each orientation `o` of a fibre over `W` to the class of `o`. -/
private def IsTwistedThomPairOverDesc (W : Set B)
    (φ : (thomPairOver F E W).singularHomology (ModuleCat.of K K) (finrank ℝ F) ⟶
      LocalCoefficientSystem.twistedHomology.{w, w, w} (signLocalSystem F E K hι) 0) : Prop :=
  ∀ b (hb : b ∈ W) (o : Orientation ℝ (E b) ι),
    φ (TopPair.singularHomologyMap (fiberThomPairOverMap F E hb) (ModuleCat.of K K) (finrank ℝ F)
      (orientedFiberGenerator K ω o)) =
      LocalCoefficientSystem.ιTwistedHomology₀.{w, w, w} (signLocalSystem F E K hι) b
        (signFiberOne hι o)

/-- It suffices to check `IsTwistedThomPairOverDesc` on one orientation of each fibre. -/
private theorem isTwistedThomPairOverDesc_of_forall {W : Set B}
    {φ : (thomPairOver F E W).singularHomology (ModuleCat.of K K) (finrank ℝ F) ⟶
      LocalCoefficientSystem.twistedHomology.{w, w, w} (signLocalSystem F E K hι) 0}
    (o : ∀ b, b ∈ W → Orientation ℝ (E b) ι)
    (h : ∀ b (hb : b ∈ W), φ (TopPair.singularHomologyMap (fiberThomPairOverMap F E hb)
      (ModuleCat.of K K) (finrank ℝ F) (orientedFiberGenerator K ω (o b hb))) =
      LocalCoefficientSystem.ιTwistedHomology₀.{w, w, w} (signLocalSystem F E K hι) b
        (signFiberOne hι (o b hb))) :
    IsTwistedThomPairOverDesc K hι ω W φ := by
  intro b hb o'
  set e := trivializationAt F E b
  have he := mem_baseSet_trivializationAt F E b
  rcases (e.mapOrientation ι he o').eq_or_eq_neg (e.mapOrientation ι he (o b hb)) hι with h' | h'
  · rw [(e.mapOrientation ι he).injective h']
    exact h b hb
  · rw [show o' = -o b hb from (e.mapOrientation ι he).injective
      (h'.trans (Trivialization.mapOrientation_neg e he (o b hb)).symm),
      orientedFiberGenerator_neg hι, map_neg, map_neg, h b hb, signFiberOne_neg, map_neg]

omit [FiniteDimensional ℝ F] in
include hι in
/-- Transport in the orientation local system along a path in the base set of a trivialization
of the atlas carries the function equal to `1` on the orientation read as `ω` to the same function
at the endpoint. -/
private theorem signLocalSystem_map_signFiberOne (e : Trivialization F (π F E))
    [MemTrivializationAtlas e] {x y : B} (γ : Path x y) (hγ : ∀ t, γ t ∈ e.baseSet)
    (hx : x ∈ e.baseSet) (hy : y ∈ e.baseSet) :
    ((signLocalSystem F E K hι).map (Path.Homotopic.Quotient.mk γ :
        FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y)).hom
      (signFiberOne hι ((e.mapOrientation ι hx).symm ω)) =
      signFiberOne hι ((e.mapOrientation ι hy).symm ω) := by
  -- The section of the double cover over `e.baseSet` read as `ω`; along it lies the lift of the
  -- reversed path, which computes the monodromy.
  let σ : C(e.baseSet, VectorBundleOrientationCover F E ι) :=
    ⟨fun z ↦ ⟨z, (e.mapOrientation ι z.2).symm ω⟩, continuous_mk_mapOrientation_symm hι e ω⟩
  let Γ : C(unitInterval, VectorBundleOrientationCover F E ι) :=
    σ.comp ⟨fun t ↦ ⟨γ.symm t, hγ _⟩, by fun_prop⟩
  let P : (FundamentalGroupoid.mk x : FundamentalGroupoid (TopCat.of B)) ⟶
      FundamentalGroupoid.mk y := Path.Homotopic.Quotient.mk γ
  have hm : (isCoveringMap_proj hι).monodromy (inv P)
      (⟨σ ⟨y, hy⟩, rfl⟩ : (proj ⁻¹' {y} : Set (VectorBundleOrientationCover F E ι))) =
      (⟨σ ⟨x, hx⟩, rfl⟩ : (proj ⁻¹' {x} : Set (VectorBundleOrientationCover F E ι))) := by
    have hinv : inv P = Path.Homotopic.Quotient.mk γ.symm :=
      IsIso.inv_eq_of_hom_inv_id (Path.Homotopic.Quotient.trans_symm _)
    rw [hinv]
    refine Subtype.ext ((IsCoveringMap.monodromy_eq_apply_one _ (Γ := Γ) (funext fun _ ↦ rfl)
      (congrArg σ (Subtype.ext (by simp)))).trans (congrArg σ (Subtype.ext (by simp))))
  have h := signLocalSystemObjEquiv_map_apply (R := K) hι P
    (signFiberOne hι ((e.mapOrientation ι hx).symm ω)) ⟨σ ⟨y, hy⟩, rfl⟩
  rw [hm] at h
  apply (signLocalSystemFiberEquiv (R := K) hι ((e.mapOrientation ι hy).symm ω)).injective
  rw [LinearEquiv.apply_symm_apply, signLocalSystemFiberEquiv_apply]
  refine h.trans ?_
  exact (signLocalSystemFiberEquiv_apply hι _ _).symm.trans (LinearEquiv.apply_symm_apply _ _)

include hι in
/-- **Over a trivializing set**, the comparison map exists: a trivialization identifies
`Hᵣ(E|_W, E₀|_W; K)` with `H₀(W; K)`, and the class of a point of `W` goes to the class of the
orientation that the trivialization reads as `ω`. These classes are constant along paths in `W`,
since transport along such a path follows the orientations read as `ω`. -/
private theorem exists_isTwistedThomPairOverDesc_of_subset (e : Trivialization F (π F E))
    [MemTrivializationAtlas e] {W : Set B} (hW : W ⊆ e.baseSet) :
    ∃ φ, IsTwistedThomPairOverDesc (E := E) K hι ω W φ := by
  let o (b : B) (hb : b ∈ W) : Orientation ℝ (E b) ι := (e.mapOrientation ι (hW hb)).symm ω
  let v (b : TopCat.of W) : ModuleCat.of K K ⟶
      LocalCoefficientSystem.twistedHomology.{w, w, w} (signLocalSystem F E K hι) 0 :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton K _
      (LocalCoefficientSystem.ιTwistedHomology₀.{w, w, w} (signLocalSystem F E K hι) b
        (signFiberOne hι (o b b.2))))
  have hv ⦃x y : TopCat.of W⦄ (γ : Path x y) : v x = v y := by
    let P : (FundamentalGroupoid.mk (x : B) : FundamentalGroupoid (TopCat.of B)) ⟶
        FundamentalGroupoid.mk (y : B) :=
      Path.Homotopic.Quotient.mk (γ.map continuous_subtype_val)
    have h := congr($(LocalCoefficientSystem.map_ιTwistedHomology₀ (signLocalSystem F E K hι) P)
      (signFiberOne hι (o x x.2)))
    rw [ConcreteCategory.comp_apply] at h
    simp only [v]
    congr 2
    rw [← h]
    exact congrArg _
      (signLocalSystem_map_signFiberOne hι ω e _ (fun t ↦ hW (γ t).2) (hW x.2) (hW y.2))
  refine ⟨TopPair.singularHomologyMap (e.thomPairOverIso ℝ hW).hom (ModuleCat.of K K)
      (finrank ℝ F) ≫ (prodThomPairSingularHomologyIso (ModuleCat.of K K) W F 0 (finrank ℝ F)).hom ≫
      singularHomology₀Desc (ModuleCat.of K K) (X := TopCat.of W) v hv,
    isTwistedThomPairOverDesc_of_forall hι ω o fun b hb ↦ ?_⟩
  -- Through the trivialization, the fibre generator of `o b` is the class of the point `b`.
  have hA : (e.continuousLinearEquivAt ℝ b (hW hb)).complZeroPairIso.inv ≫
      fiberThomPairOverMap F E hb ≫ (e.thomPairOverIso ℝ hW).hom =
        prodThomPairFiberMap F (⟨b, hb⟩ : W) := by
    rw [e.fiberThomPairOverMap_comp_thomPairOverIso_hom ℝ hW hb, Iso.inv_hom_id_assoc]
  have hφb := congr($(show TopPair.singularHomologyMap
      (e.continuousLinearEquivAt ℝ b (hW hb)).complZeroPairIso.inv (ModuleCat.of K K)
        (finrank ℝ F) ≫ TopPair.singularHomologyMap (fiberThomPairOverMap F E hb)
          (ModuleCat.of K K) (finrank ℝ F) ≫
        TopPair.singularHomologyMap (e.thomPairOverIso ℝ hW).hom (ModuleCat.of K K)
          (finrank ℝ F) ≫ (prodThomPairSingularHomologyIso (ModuleCat.of K K) W F 0
            (finrank ℝ F)).hom ≫ singularHomology₀Desc (ModuleCat.of K K) (X := TopCat.of W) v hv =
      TopPair.singularHomologyMap (prodThomPairFiberMap F (⟨b, hb⟩ : W)) (ModuleCat.of K K)
          (finrank ℝ F) ≫ (prodThomPairSingularHomologyIso (ModuleCat.of K K) W F 0
            (finrank ℝ F)).hom ≫ singularHomology₀Desc (ModuleCat.of K K) (X := TopCat.of W) v hv by
    simp only [← Category.assoc, ← TopPair.singularHomologyMap_comp]
    simp only [Category.assoc, hA]) (complZeroPairGenerator K F))
  simp only [ConcreteCategory.comp_apply,
    singularHomologyMap_prodThomPairFiberMap_complZeroPairGenerator, Iso.inv_hom_id_apply] at hφb
  rw [orientedFiberGenerator_eq hι ω e (hW hb), Equiv.apply_symm_apply,
    orientationModelGenerator_self]
  refine hφb.trans ?_
  rw [← ConcreteCategory.comp_apply, singularHomology₀Section_singularHomology₀Desc]
  exact one_smul K _

include hι in
/-- **The Mayer–Vietoris step**: comparison maps over open sets `U` and `V` glue to one over
`U ∪ V`, when `Hᵣ₋₁(E|_{U ∩ V}, E₀|_{U ∩ V})` vanishes and morphisms out of
`Hᵣ(E|_{U ∩ V}, E₀|_{U ∩ V})` are determined on the fibres. -/
private theorem exists_isTwistedThomPairOverDesc_union {U V : Set B} (hU : IsOpen U)
    (hV : IsOpen V)
    (hUV : ∀ m, m + 1 = finrank ℝ F →
      IsZero ((thomPairOver F E (U ∩ V)).singularHomology (ModuleCat.of K K) m))
    (hext : ∀ {T : ModuleCat.{w} K}
      {g g' : (thomPairOver F E (U ∩ V)).singularHomology (ModuleCat.of K K) (finrank ℝ F) ⟶ T},
      (∀ b (hb : b ∈ U ∩ V),
        TopPair.singularHomologyMap (fiberThomPairOverMap F E hb) (ModuleCat.of K K) _ ≫ g =
          TopPair.singularHomologyMap (fiberThomPairOverMap F E hb) (ModuleCat.of K K) _ ≫ g') →
        g = g')
    (hφU : ∃ φ, IsTwistedThomPairOverDesc (E := E) K hι ω U φ)
    (hφV : ∃ φ, IsTwistedThomPairOverDesc (E := E) K hι ω V φ) :
    ∃ φ, IsTwistedThomPairOverDesc (E := E) K hι ω (U ∪ V) φ := by
  obtain ⟨φU, hφU⟩ := hφU
  obtain ⟨φV, hφV⟩ := hφV
  let S := ShortComplex.mk _ _ (singularHomology_thomPairOver_mayerVietoris_comp_eq_zero
    (F := F) (E := E) (U := U) (V := V) (ModuleCat.of K K) (finrank ℝ F))
  have hS : S.Exact :=
    singularHomology_thomPairOver_mayerVietoris_exact (ModuleCat.of K K) hU hV _
  have : Epi S.g := epi_singularHomology_thomPairOver_union (ModuleCat.of K K) hU hV hUV
  let φ : S.X₂ ⟶ _ := biprod.desc φU φV
  -- `φ` vanishes on the classes over `U ∩ V`: both restrictions of a fibre class have the same
  -- image.
  have hφ : S.f ≫ φ = 0 := by
    refine hext fun b hb ↦ orientedFiberGenerator_hom_ext ω (modelFiberOrientation ω b) ?_
    simp only [S, φ, biprod.lift_desc, Preadditive.comp_add, Preadditive.neg_comp,
      Preadditive.comp_neg, comp_zero, ← TopPair.singularHomologyMap_comp_assoc,
      fiberThomPairOverMap_comp_thomPairOverMap]
    simp [hφU b hb.1, hφV b hb.2]
  let Φ := hS.gIsCokernel.desc (CokernelCofork.ofπ φ hφ)
  have hgΦ : S.g ≫ Φ = φ := hS.gIsCokernel.fac (CokernelCofork.ofπ φ hφ) WalkingParallelPair.one
  have hΦU : TopPair.singularHomologyMap (thomPairOverMap F E (subset_union_left : U ⊆ U ∪ V))
      (ModuleCat.of K K) (finrank ℝ F) ≫ Φ = φU := by
    rw [← biprod.inl_desc (TopPair.singularHomologyMap (thomPairOverMap F E
      (subset_union_left : U ⊆ U ∪ V)) (ModuleCat.of K K) (finrank ℝ F))
      (TopPair.singularHomologyMap (thomPairOverMap F E (subset_union_right : V ⊆ U ∪ V))
        (ModuleCat.of K K) (finrank ℝ F)), Category.assoc]
    exact (congrArg (biprod.inl ≫ ·) hgΦ).trans (biprod.inl_desc _ _)
  have hΦV : TopPair.singularHomologyMap (thomPairOverMap F E (subset_union_right : V ⊆ U ∪ V))
      (ModuleCat.of K K) (finrank ℝ F) ≫ Φ = φV := by
    rw [← biprod.inr_desc (TopPair.singularHomologyMap (thomPairOverMap F E
      (subset_union_left : U ⊆ U ∪ V)) (ModuleCat.of K K) (finrank ℝ F))
      (TopPair.singularHomologyMap (thomPairOverMap F E (subset_union_right : V ⊆ U ∪ V))
        (ModuleCat.of K K) (finrank ℝ F)), Category.assoc]
    exact (congrArg (biprod.inr ≫ ·) hgΦ).trans (biprod.inr_desc _ _)
  refine ⟨Φ, fun b hb o ↦ ?_⟩
  rcases hb with hb | hb
  · rw [← fiberThomPairOverMap_comp_thomPairOverMap F E subset_union_left hb,
      TopPair.singularHomologyMap_comp, ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      hΦU, hφU b hb]
  · rw [← fiberThomPairOverMap_comp_thomPairOverMap F E subset_union_right hb,
      TopPair.singularHomologyMap_comp, ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      hΦV, hφV b hb]

include hι in
/-- **Finite unions of trivializing open sets**: the comparison map exists over a finite union of
open sets each lying in the base set of a trivialization of the atlas. -/
private theorem exists_isTwistedThomPairOverDesc_biUnion {κ : Type*} (s : Finset κ)
    {W : κ → Set B} (hWo : ∀ i ∈ s, IsOpen (W i))
    (hWe : ∀ i ∈ s, ∃ (e : Trivialization F (π F E)) (_ : MemTrivializationAtlas e),
      W i ⊆ e.baseSet) :
    ∃ φ, IsTwistedThomPairOverDesc (E := E) K hι ω (⋃ i ∈ s, W i) φ := by
  classical
  induction s using Finset.induction_on generalizing W with
  | empty =>
    rw [show (⋃ i ∈ (∅ : Finset κ), W i) = ∅ by simp]
    exact ⟨0, fun b hb ↦ absurd hb (notMem_empty b)⟩
  | insert a s _ ih =>
    rw [Finset.set_biUnion_insert]
    obtain ⟨e, _, he⟩ := hWe a (Finset.mem_insert_self a s)
    have hWo' : ∀ i ∈ s, IsOpen (W i) := fun i hi ↦ hWo i (Finset.mem_insert_of_mem hi)
    have hWe' : ∀ i ∈ s, ∃ (e : Trivialization F (π F E)) (_ : MemTrivializationAtlas e),
        W i ⊆ e.baseSet := fun i hi ↦ hWe i (Finset.mem_insert_of_mem hi)
    refine exists_isTwistedThomPairOverDesc_union hι ω (hWo a (Finset.mem_insert_self a s))
      (isOpen_biUnion hWo')
      (fun m hm ↦ e.isZero_singularHomology_thomPairOver (inter_subset_left.trans he) _
        (by omega)) ?_ (exists_isTwistedThomPairOverDesc_of_subset hι ω e he) (ih hWo' hWe')
    -- `W a ∩ ⋃ i ∈ s, W i` is the union of the trivializing open sets `W a ∩ W i`, `i ∈ s`.
    intro T
    rw [inter_iUnion₂]
    intro g g' h
    refine singularHomology_thomPairOver_biUnion_hom_ext s
      (fun i hi ↦ (hWo a (Finset.mem_insert_self a s)).inter (hWo' i hi)) (fun i hi ↦ ?_) h
    obtain ⟨e', _, hi'⟩ := hWe' i hi
    exact ⟨e', inferInstance, inter_subset_right.trans hi'⟩

include hι in
/-- **The passage to the whole base**: the homology of the Thom pair is the filtered colimit of
its homology over the finite unions of the chosen trivializing sets, over each of which the
comparison map exists, and these maps are compatible since they are determined on the fibres. -/
private theorem exists_thomPair_twistedDesc :
    ∃ φ : (thomPair F E).singularHomology (ModuleCat.of K K) (finrank ℝ F) ⟶
        LocalCoefficientSystem.twistedHomology.{w, w, w} (signLocalSystem F E K hι) 0,
      ∀ b (o : Orientation ℝ (E b) ι),
        φ (TopPair.singularHomologyMap (fiberThomPairMap F E b) (ModuleCat.of K K) (finrank ℝ F)
          (orientedFiberGenerator K ω o)) =
          LocalCoefficientSystem.ιTwistedHomology₀.{w, w, w} (signLocalSystem F E K hι) b
            (signFiberOne hι o) := by
  choose φ hφ using fun s : Finset B ↦ exists_isTwistedThomPairOverDesc_biUnion (K := K) hι ω s
    (W := fun b ↦ (trivializationAt F E b).baseSet)
    (fun b _ ↦ (trivializationAt F E b).open_baseSet)
    fun b _ ↦ ⟨trivializationAt F E b, inferInstance, subset_rfl⟩
  have hres {s t : Finset B} (h : s ≤ t) :
      TopPair.singularHomologyMap (thomPairOverMap F E (biUnion_subset_biUnion_left h))
        (ModuleCat.of K K) (finrank ℝ F) ≫ φ t = φ s := by
    refine singularHomology_thomPairOver_biUnion_hom_ext s
      (fun b _ ↦ (trivializationAt F E b).open_baseSet)
      (fun b _ ↦ ⟨trivializationAt F E b, inferInstance, subset_rfl⟩)
      fun b hb ↦ orientedFiberGenerator_hom_ext ω (modelFiberOrientation ω b) ?_
    rw [← TopPair.singularHomologyMap_comp_assoc, fiberThomPairOverMap_comp_thomPairOverMap,
      ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hφ t, hφ s]
  let P := isColimitMapCoconeSingularHomologyThomPairFiniteTrivializingUnion (F := F) (E := E)
    (ModuleCat.of K K) (finrank ℝ F)
  let c : Cocone (thomPairFiniteTrivializingUnionDiagram (F := F) (E := E) ⋙
      TopPair.singularHomologyFunctor (ModuleCat.of K K) (finrank ℝ F)) :=
    { pt := LocalCoefficientSystem.twistedHomology.{w, w, w} (signLocalSystem F E K hι) 0
      ι :=
        { app s := eqToHom (singularHomology_thomPairOver_finiteTrivializingUnion_eq K s).symm ≫
            φ s
          naturality s t f := by
            dsimp only [Functor.comp_obj, Functor.comp_map, Functor.const_obj_map]
            simp only [thomPairFiniteTrivializingUnionDiagram_map,
              TopPair.singularHomologyFunctor_map, TopPair.singularHomologyMap_comp,
              TopPair.singularHomologyMap_eqToHom, Category.assoc, eqToHom_trans_assoc,
              eqToHom_refl, Category.id_comp, hres f.le]
            exact congrArg _ (Category.comp_id _).symm } }
  -- On a finite union of the chosen trivializing sets, the map is the one over the union.
  have hleg (s : Finset B) :
      TopPair.singularHomologyMap (thomPairOverMap F E (subset_univ _) ≫
          (thomPairOverUnivIso F E).hom) (ModuleCat.of K K) (finrank ℝ F) ≫
        eqToHom (singularHomology_thomPair_eq K) ≫ P.desc c = φ s := by
    have h := singularHomologyFunctor_mapCocone_thomPairFiniteTrivializingUnionCocone_ι_app
      (F := F) (E := E) (ModuleCat.of K K) (finrank ℝ F) s
    rw [(eqToHom_comp_iff _ _ _).1 h.symm]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, P.fac]
    simp [c]
  refine ⟨eqToHom (singularHomology_thomPair_eq K) ≫ P.desc c, fun b o ↦ ?_⟩
  have hb : b ∈ ⋃ c ∈ ({b} : Finset B), (trivializationAt F E c).baseSet := by
    simp [mem_baseSet_trivializationAt]
  have h := congr($(hleg {b}) (TopPair.singularHomologyMap (fiberThomPairOverMap F E hb)
    (ModuleCat.of K K) (finrank ℝ F) (orientedFiberGenerator K ω o)))
  rw [ConcreteCategory.comp_apply, hφ {b} b hb] at h
  rw [← fiberThomPairOverMap_comp_thomPairOverUnivIso_hom,
    ← fiberThomPairOverMap_comp_thomPairOverMap F E (subset_univ _) hb, Category.assoc,
    TopPair.singularHomologyMap_comp]
  exact h

variable (K F E) in
/-- **The homology of the Thom pair in the rank degree, with twisted coefficients.** For a real
vector bundle `E → B` of rank `r` over an arbitrary base, with Thom pair `(E, E₀)`, and any
commutative ring `K`, `Hᵣ(E, E₀; K)` is the zeroth homology of `B` with coefficients in the
orientation local system `o(E)` of `E` (with coefficients `K`). No orientability is assumed; an
orientation of `E` trivializes `o(E)` (`TauCeti.VectorBundleOrientation.signLocalSystemIso`).

The isomorphism depends on the choice of an orientation `ω` of the model fibre `F` (`ι` indexes
the orientations, of cardinality `r`), which fixes which orientation of a fibre corresponds to
the generator `TauCeti.complZeroPairGenerator K F` of `Hᵣ(F, F ∖ {0}; K)`: a linear trivialization
reading an orientation of `E_b` as `ω` carries the class of that orientation to the fibre class of
`complZeroPairGenerator K F`
(`TauCeti.thomPairSingularHomologyFinrankIsoTwistedHomology_inv_ιTwistedHomology₀`,
`TauCeti.thomPairSingularHomologyFinrankIsoTwistedHomology_hom_apply`). The opposite choice of `ω`
negates the isomorphism. -/
def thomPairSingularHomologyFinrankIsoTwistedHomology :
    (thomPair F E).singularHomology (ModuleCat.of K K) (finrank ℝ F) ≅
      LocalCoefficientSystem.twistedHomology.{w, w, w} (signLocalSystem F E K hι) 0 where
  hom := (exists_thomPair_twistedDesc hι ω).choose
  inv := twistedHomologyThomPairDesc K hι ω
  hom_inv_id := by
    refine singularHomology_thomPair_hom_ext fun b ↦
      orientedFiberGenerator_hom_ext ω (modelFiberOrientation ω b) ?_
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
      (exists_thomPair_twistedDesc hι ω).choose_spec, ← ConcreteCategory.comp_apply,
      ιTwistedHomology₀_twistedHomologyThomPairDesc, twistedFiberClass_apply hι ω
        ⟨⟨b, modelFiberOrientation ω b⟩, rfl⟩, ← signLocalSystemFiberEquiv_apply,
      LinearEquiv.apply_symm_apply, one_smul, Category.comp_id]
    rfl
  inv_hom_id := by
    refine LocalCoefficientSystem.twistedHomology₀_hom_ext _ fun b ↦
      ConcreteCategory.hom_ext _ _ fun f ↦ ?_
    let o := modelFiberOrientation (E := E) ω b
    -- The fibre of the orientation local system is free on the function equal to `1` at `o`.
    have hf : f = signLocalSystemFiberEquiv hι o f • signFiberOne hι o :=
      (signLocalSystemFiberEquiv (R := K) hι o).injective (by
        rw [map_smul, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one])
    rw [Category.comp_id, ← Category.assoc, ConcreteCategory.comp_apply,
      ιTwistedHomology₀_twistedHomologyThomPairDesc, twistedFiberClass_apply hι ω ⟨⟨b, o⟩, rfl⟩,
      ← signLocalSystemFiberEquiv_apply, map_smul, coverFiberClass_mk,
      (exists_thomPair_twistedDesc hι ω).choose_spec b o, ← map_smul, ← hf]

private theorem thomPairSingularHomologyFinrankIsoTwistedHomology_inv :
    (thomPairSingularHomologyFinrankIsoTwistedHomology K F E hι ω).inv =
      twistedHomologyThomPairDesc K hι ω :=
  rfl

/-- **The twisted Thom isomorphism on the class of a fibre function.** Let `e` be a linear
trivialization whose base set contains `b`, and `o` the orientation of `E_b` that `e` reads as the
model orientation `ω`. The class of `f` in the fibre of the orientation local system over `b`
goes to `f o` times the fibre class of `complZeroPairGenerator K F` carried to `E_b` by `e`. -/
theorem thomPairSingularHomologyFinrankIsoTwistedHomology_inv_ιTwistedHomology₀
    (e : Trivialization F (π F E)) [e.IsLinear ℝ] {b : B} (hb : b ∈ e.baseSet)
    (f : (signLocalSystem F E K hι).obj (FundamentalGroupoid.mk b)) :
    (thomPairSingularHomologyFinrankIsoTwistedHomology K F E hι ω).inv
        (LocalCoefficientSystem.ιTwistedHomology₀.{w, w, w} (signLocalSystem F E K hι) b f) =
      signLocalSystemFiberEquiv hι ((e.mapOrientation ι hb).symm ω) f •
        TopPair.singularHomologyMap (fiberThomPairMap F E b) (ModuleCat.of K K) (finrank ℝ F)
          (TopPair.singularHomologyMap (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.inv
            (ModuleCat.of K K) (finrank ℝ F) (complZeroPairGenerator K F)) := by
  rw [← ConcreteCategory.comp_apply, thomPairSingularHomologyFinrankIsoTwistedHomology_inv,
    ιTwistedHomology₀_twistedHomologyThomPairDesc,
    twistedFiberClass_apply hι ω ⟨⟨b, (e.mapOrientation ι hb).symm ω⟩, rfl⟩,
    ← signLocalSystemFiberEquiv_apply, coverFiberClass_mk, orientedFiberGenerator_eq hι ω e hb,
    Equiv.apply_symm_apply, orientationModelGenerator_self]

/-- **The twisted Thom isomorphism on a fibre class.** Let `e` be a linear trivialization whose
base set contains `b`, and `o` the orientation of `E_b` that `e` reads as the model orientation
`ω`. The fibre class of `complZeroPairGenerator K F` carried to `E_b` by `e` goes to the class of
the function on the orientations of `E_b` equal to `1` at `o`. -/
theorem thomPairSingularHomologyFinrankIsoTwistedHomology_hom_apply
    (e : Trivialization F (π F E)) [e.IsLinear ℝ] {b : B} (hb : b ∈ e.baseSet) :
    (thomPairSingularHomologyFinrankIsoTwistedHomology K F E hι ω).hom
        (TopPair.singularHomologyMap (fiberThomPairMap F E b) (ModuleCat.of K K) (finrank ℝ F)
          (TopPair.singularHomologyMap (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.inv
            (ModuleCat.of K K) (finrank ℝ F) (complZeroPairGenerator K F))) =
      LocalCoefficientSystem.ιTwistedHomology₀.{w, w, w} (signLocalSystem F E K hι) b
        ((signLocalSystemFiberEquiv hι ((e.mapOrientation ι hb).symm ω)).symm 1) := by
  have h := thomPairSingularHomologyFinrankIsoTwistedHomology_inv_ιTwistedHomology₀ hι ω e hb
    ((signLocalSystemFiberEquiv (R := K) hι ((e.mapOrientation ι hb).symm ω)).symm 1)
  rw [LinearEquiv.apply_symm_apply, one_smul] at h
  rw [← h, Iso.inv_hom_id_apply]

end Twisted

end TauCeti
