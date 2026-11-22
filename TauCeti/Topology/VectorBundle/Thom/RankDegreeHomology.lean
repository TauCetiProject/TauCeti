/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.MayerVietoris.RankDegree
public import TauCeti.AlgebraicTopology.Singular.Reduced
public import TauCeti.Topology.VectorBundle.Orientation.Basic
import TauCeti.Algebra.Category.ModuleCat.SpanSingleton
import TauCeti.AlgebraicTopology.Singular.CompactSupport
import TauCeti.AlgebraicTopology.Singular.MayerVietoris.FiniteUnion
import TauCeti.Topology.Category.TopCat.Limits.Basic
import TauCeti.Topology.Connected.PathConnected
import TauCeti.Topology.VectorBundle.Orientation.ThomClass

/-!
# The homology of the Thom pair in the rank degree

Let `E → B` be a real vector bundle of rank `r` over an arbitrary base, with Thom pair `(E, E₀)`,
and let `K` be a commutative ring. The relative homology `Hₙ(E, E₀; K)` vanishes for `n < r`
(`TauCeti.isZero_singularHomology_thomPair`). This file computes the first group that does not
vanish,

`Hᵣ(E, E₀; K) ≅ H₀(B; K)`,

in two cases:

* when `1` is the only unit of `K`, such as `ZMod 2`, for every bundle
  (`TauCeti.thomPairSingularHomologyFinrankIso`). The isomorphism sends the class of the fibre over
  a point `b`, the image of a generator of `Hᵣ(E_b, E_b ∖ {0}; K) ≅ K` under the inclusion of the
  fibre pair, to the class of the point `b`
  (`TauCeti.thomPairSingularHomologyFinrankIso_hom_apply`).
  No orientation is needed: since `1` is the only unit of `K`, the module
  `Hᵣ(E_b, E_b ∖ {0}; K) ≅ K` has a single generator, so the fibre classes do not depend on any
  choice.
* for an oriented bundle and every commutative ring `K`, for instance `ℤ`
  (`TauCeti.VectorBundleOrientation.thomPairSingularHomologyFinrankIso`). Here the fibre classes
  are chosen by the orientation: fixing an orientation `ω` of the model fibre `F` and a generator
  `γ` of `Hᵣ(F, F ∖ {0}; K)`, the fibre class over `b` is the class which a linear trivialization
  reads as `γ` if it reads the orientation of `E_b` as `ω`, and as `-γ` otherwise. Two linear
  trivializations induce maps `Hᵣ(E_b, E_b ∖ {0}) ⟶ Hᵣ(F, F ∖ {0})` differing by the sign of the
  determinant of their coordinate change
  (`Bundle.Trivialization.singularHomologyMap_complZeroPairIso_hom_eq_sign_det_smul`), and this
  sign is `+1` exactly when they read the orientation alike
  (`Bundle.Trivialization.singularHomologyMap_complZeroPairIso_hom_eq_of_mapOrientation_eq`), so
  this class does not depend on the trivialization.

These are the bottom degree of the Thom isomorphism `Hₙ₊ᵣ(E, E₀; K) ≅ Hₙ(B; K)` in homology, with
coefficients in `ZMod 2` for every bundle and integral coefficients for an oriented one. Attaching
the disc bundle of `E` along its sphere bundle contributes the relative homology of the Thom pair,
so for the negative bundle of a Morse–Bott critical submanifold of index `r` this computes the
relative homology across its critical level in degree `r`, the lowest degree in which it can be
nonzero.

Without an orientation and over an arbitrary commutative ring, the group in the rank degree is
the zeroth homology of `B` twisted by the orientation local system of `E`; this is
`TauCeti.Topology.VectorBundle.Orientation.RingRankDegreeHomology`.

## The proof

Both cases are instances of one argument, for a family of fibre classes which every chosen
trivialization reads, near each point of its base set, as a generator of `Hᵣ(F, F ∖ {0}; K)`
multiplied by a locally constant unit. The inverse map `H₀(B; K) ⟶ Hᵣ(E, E₀; K)` is defined on the
classes of points, which generate `H₀(B; K)`: it sends the class of `b` to the fibre class over
`b`. This is well defined because the fibre classes are constant along paths in the base. Over a
subset `W` of the base set of a linear trivialization, the trivialization identifies the Thom pair
`(E|_W, E₀|_W)` with the Thom pair of the product bundle `W × F`, whose homology in degree `r` is
`H₀(W; K)` (`TauCeti.prodThomPairSingularHomologyIso`), and this identification sends the fibre
class over a point to the class of the point multiplied by its unit; multiplying the class of each
point by a unit that is constant along paths is an automorphism of `H₀(W; K)`, so the map is an
isomorphism over `W`. The Mayer–Vietoris sequence of the Thom pairs over two open sets
(`TauCeti.singularHomology_thomPairOver_mayerVietoris_exact`) ends in degree `r`, since the
homology vanishes below the rank, so the map is an isomorphism over a finite union of trivializing
open sets by induction on their number. Singular homology has compact supports, so the homology of
the base and of the Thom pair are the filtered colimits of their homology over these finite unions,
and the map is an isomorphism over the whole base. These two steps hold for any such maps into the
homology of Thom pairs (`TauCeti.isIso_of_isColimit_biUnion_baseSet`).

## Main results

* `TauCeti.singularHomologyMap_prodThomPairFiberMap_complZeroPairPointHom_one`: the fibre inclusion
  over a point carries the point class of `1` to the class of the point, for any ring `K`.
* `TauCeti.thomPairSingularHomologyFinrankIso`: `Hᵣ(E, E₀; K) ≅ H₀(B; K)` for `r` the rank and `K`
  a commutative ring whose only unit is `1`.
* `TauCeti.thomPairSingularHomologyFinrankIso_hom_apply`: it sends the fibre class over `b` to the
  class of `b`.
* `TauCeti.VectorBundleOrientation.thomPairSingularHomologyFinrankIso`: `Hᵣ(E, E₀; K) ≅ H₀(B; K)`
  for an oriented bundle and any commutative ring `K`.
* `VectorBundleOrientation.thomPairSingularHomologyFinrankIso_hom_apply_of_mapOrientation_eq`
  and `..._of_mapOrientation_eq_neg`: it sends the class of the fibre pair over `b` read as `γ` by
  a trivialization to the class of `b`, or to its negative, according to whether the
  trivialization reads the orientation of `E_b` as `ω` or as `-ω`.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10, Lemma 10.3 and the proof of Theorem 10.4 (the induction over finite unions
  of trivializing open sets and the passage to a directed union).
* A. Hatcher, *Algebraic Topology*, Section 4.D, Theorem 4D.10 and its proof, which also covers
  `ℤ/2` coefficients for bundles without an orientation.
-/

public noncomputable section

open Bundle CategoryTheory Limits Set Module AlgebraicTopology Topology

universe w v u

namespace TauCeti

section Fiber

variable (K : Type w) [Ring K] (F : Type w) [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- The fibre inclusion over a point `x` of `W` carries the point class of `1` to the class of `x`
under `Hᵣ(W × F, W × (F ∖ {0}); K) ≅ H₀(W; K)`. -/
theorem singularHomologyMap_prodThomPairFiberMap_complZeroPairPointHom_one
    {W : Type w} [TopologicalSpace W] (x : W) :
    TopPair.singularHomologyMap (prodThomPairFiberMap F x) (ModuleCat.of K K) (finrank ℝ F)
        (complZeroPairPointHom (ModuleCat.of K K) F (finrank ℝ F) rfl (1 : K)) =
      (prodThomPairSingularHomologyIso (ModuleCat.of K K) W F 0 (finrank ℝ F)).inv
        (singularHomology₀Section (ModuleCat.of K K) (X := TopCat.of W) x 1) :=
  ConcreteCategory.congr_hom (complZeroPairPointHom_comp_singularHomologyMap_prodThomPairFiberMap
    (ModuleCat.of K K) W F (finrank ℝ F) rfl x) (1 : K)

end Fiber

section Bundle

variable {K : Type w} [CommRing K] {B : Type w} [TopologicalSpace B] {F : Type w}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {E : B → Type w}
  [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)]
  [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]

/-! ### Locally constant families of fibre generators -/

variable (K F E) in
/-- A family of classes `g b` of the fibre pairs `(E_b, E_b ∖ {0})` which the chosen trivialization
`trivializationAt F E c` reads, at each point `x` of its base set, as the generator of
`Hᵣ(F, F ∖ {0}; K)` multiplied by a unit `ε c x`, locally constant in `x`. Such a family is a
family of generators of the fibre pairs, and the isomorphism `Hᵣ(E, E₀; K) ≅ H₀(B; K)` sends its
fibre classes to the classes of the points. -/
private structure IsLocalFiberGenerator
    (g : ∀ b, ((TopPair.ofSubset (X := TopCat.of (E b)) ({0}ᶜ : Set (E b))).singularHomology
      (ModuleCat.of K K) (finrank ℝ F) : ModuleCat.{w} K))
    (ε : B → B → Kˣ) : Prop where
  /-- The unit by which the trivialization at `c` reads `g x` is locally constant in `x`. -/
  eventually_eq (c b : B) (hb : b ∈ (trivializationAt F E c).baseSet) :
    ∀ᶠ x in 𝓝 b, ε c x = ε c b
  /-- The trivialization at `c` reads `g x` as the generator multiplied by `ε c x`. -/
  map_eq (c x : B) (hx : x ∈ (trivializationAt F E c).baseSet) :
    TopPair.singularHomologyMap ((trivializationAt F E c).continuousLinearEquivAt ℝ x
        hx).complZeroPairIso.hom (ModuleCat.of K K) (finrank ℝ F) (g x) =
      (ε c x : K) • complZeroPairPointHom (ModuleCat.of K K) F (finrank ℝ F) rfl (1 : K)

variable {g : ∀ b, ((TopPair.ofSubset (X := TopCat.of (E b)) ({0}ᶜ : Set (E b))).singularHomology
    (ModuleCat.of K K) (finrank ℝ F) : ModuleCat.{w} K)} {ε : B → B → Kˣ}

/-- The multipliers are constant along paths in the base set of the trivialization. -/
private theorem IsLocalFiberGenerator.eq_of_path (hg : IsLocalFiberGenerator K F E g ε) (c : B)
    {X : Type*} [TopologicalSpace X] {φ : X → B} (hφ : Continuous φ)
    (hφc : ∀ x, φ x ∈ (trivializationAt F E c).baseSet) {x y : X} (γ : Path x y) :
    ε c (φ x) = ε c (φ y) :=
  γ.eq_of_eventually_eq (f := fun x ↦ ε c (φ x)) fun t ↦
    ((hφ.comp γ.continuous).tendsto t).eventually (hg.eventually_eq c _ (hφc (γ t)))

variable (g) in
/-- The fibre class over a point `x` of `W`: the image of `g x` in `Hᵣ(E|_W, E₀|_W; K)`. -/
private def fiberClassOver (W : Set B) (x : W) :
    ((thomPairOver F E W).singularHomology (ModuleCat.of K K) (finrank ℝ F) : ModuleCat.{w} K) :=
  TopPair.singularHomologyMap (fiberThomPairOverMap F E x.property) (ModuleCat.of K K) (finrank ℝ F)
    (g x)

omit [FiniteDimensional ℝ F] [∀ b, Module ℝ (E b)] [VectorBundle ℝ F E] in
/-- Restricting from `W` to `W'` carries fibre classes to fibre classes. -/
private theorem singularHomologyMap_thomPairOverMap_fiberClassOver {W W' : Set B} (h : W ⊆ W')
    (x : W) :
    TopPair.singularHomologyMap (thomPairOverMap F E h) (ModuleCat.of K K) (finrank ℝ F)
        (fiberClassOver g W x) = fiberClassOver g W' (inclusion h x) := by
  rw [fiberClassOver, fiberClassOver, ← ConcreteCategory.comp_apply,
    ← TopPair.singularHomologyMap_comp, fiberThomPairOverMap_comp_thomPairOverMap]

/-- **The fibre classes over a trivializing set are multiples of the classes of the points**: the
chosen trivialization at `c` identifies `Hᵣ(E|_W, E₀|_W; K)` with
`Hᵣ(W × F, W × (F ∖ {0}); K) ≅ H₀(W; K)` for `W` in its base set, and this sends the fibre class
over `x` to the class of `x` multiplied by `ε c x`. -/
private theorem singularHomologyMap_thomPairOverIso_fiberClassOver
    (hg : IsLocalFiberGenerator K F E g ε) (c : B) {W : Set B}
    (hW : W ⊆ (trivializationAt F E c).baseSet) (x : W) :
    TopPair.singularHomologyMap ((trivializationAt F E c).thomPairOverIso ℝ hW).hom
        (ModuleCat.of K K) (finrank ℝ F) (fiberClassOver g W x) =
      (ε c x : K) • (prodThomPairSingularHomologyIso (ModuleCat.of K K) W F 0 (finrank ℝ F)).inv
        (singularHomology₀Section (ModuleCat.of K K) (X := TopCat.of W) x 1) := by
  rw [fiberClassOver, ← ConcreteCategory.comp_apply, ← TopPair.singularHomologyMap_comp,
    Bundle.Trivialization.fiberThomPairOverMap_comp_thomPairOverIso_hom ℝ _ hW x.property,
    TopPair.singularHomologyMap_comp, ConcreteCategory.comp_apply, hg.map_eq c x (hW x.property),
    map_smul, Subtype.coe_eta, singularHomologyMap_prodThomPairFiberMap_complZeroPairPointHom_one]

/-- **The fibre classes are constant along paths**: near each point `b` they are read through the
chosen trivialization at `b` as multiples of the classes of the points by the locally constant unit
`ε b`. -/
private theorem fiberClassOver_eq_of_path (hg : IsLocalFiberGenerator K F E g ε) {W : Set B}
    {x y : W} (γ : Path x y) : fiberClassOver g W x = fiberClassOver g W y := by
  refine eq_of_path_of_mono (fun h ↦ TopPair.singularHomologyMap (thomPairOverMap F E h)
      (ModuleCat.of K K) (finrank ℝ F)) (fiberClassOver g)
    (singularHomologyMap_thomPairOverMap_fiberClassOver)
    (fun b ↦ {z | z ∈ (trivializationAt F E b).baseSet ∧ ε b z = ε b b})
    (fun b ↦ Filter.Eventually.and ((trivializationAt F E b).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt F E b))
      (hg.eventually_eq _ _ (mem_baseSet_trivializationAt F E b)))
    (fun b W ↦ ?_) γ
  have hW : W ∩ {z | z ∈ (trivializationAt F E b).baseSet ∧ ε b z = ε b b} ⊆
      (trivializationAt F E b).baseSet := fun _ hz ↦ hz.2.1
  refine ⟨TopPair.singularHomologyMap ((trivializationAt F E b).thomPairOverIso ℝ hW).hom
      (ModuleCat.of K K) (finrank ℝ F) ≫
    (prodThomPairSingularHomologyIso (ModuleCat.of K K) _ F 0 (finrank ℝ F)).hom, ε b b,
    inferInstance, fun x ↦ ?_⟩
  rw [ConcreteCategory.comp_apply, singularHomologyMap_thomPairOverIso_fiberClassOver hg b hW,
    map_smul, Iso.inv_hom_id_apply, x.property.2.2]

/-- The map `H₀(W; K) ⟶ Hᵣ(E|_W, E₀|_W; K)` sending the class of a point to the fibre class over
it. -/
private def thomPairOverSingularHomologyFinrankInv (hg : IsLocalFiberGenerator K F E g ε)
    (W : Set B) :
    ((singularHomologyFunctor (ModuleCat.{w} K) 0).obj (ModuleCat.of K K)).obj (TopCat.of W) ⟶
      (thomPairOver F E W).singularHomology (ModuleCat.of K K) (finrank ℝ F) :=
  singularHomology₀Desc (ModuleCat.of K K) (X := TopCat.of W)
    (fun x ↦ ModuleCat.ofHom (LinearMap.toSpanSingleton K _ (fiberClassOver g W x)))
    fun _ _ γ ↦ by rw [fiberClassOver_eq_of_path hg γ]

@[reassoc]
private theorem singularHomology₀Section_thomPairOverSingularHomologyFinrankInv
    (hg : IsLocalFiberGenerator K F E g ε) {W : Set B} (x : W) :
    singularHomology₀Section (ModuleCat.of K K) (X := TopCat.of W) x ≫
        thomPairOverSingularHomologyFinrankInv hg W =
      ModuleCat.ofHom (LinearMap.toSpanSingleton K _ (fiberClassOver g W x)) := by
  rw [thomPairOverSingularHomologyFinrankInv]
  exact singularHomology₀Section_singularHomology₀Desc (X := TopCat.of W) _ _ _ x

/-- The maps over `W ⊆ W'` commute with the restrictions. -/
private theorem thomPairOverSingularHomologyFinrankInv_naturality
    (hg : IsLocalFiberGenerator K F E g ε) {W W' : Set B} (h : W ⊆ W') :
    ((singularHomologyFunctor (ModuleCat.{w} K) 0).obj (ModuleCat.of K K)).map
        (TopCat.ofHom (ContinuousMap.inclusion h)) ≫
        thomPairOverSingularHomologyFinrankInv hg W' =
      thomPairOverSingularHomologyFinrankInv hg W ≫
        TopPair.singularHomologyMap (thomPairOverMap F E h) (ModuleCat.of K K) (finrank ℝ F) := by
  refine singularHomology₀_hom_ext _ fun x ↦ ?_
  rw [singularHomology₀Section_naturality_assoc,
    singularHomology₀Section_thomPairOverSingularHomologyFinrankInv,
    singularHomology₀Section_thomPairOverSingularHomologyFinrankInv_assoc,
    ModuleCat.ofHom_toSpanSingleton_comp, singularHomologyMap_thomPairOverMap_fiberClassOver]
  rw [ConcreteCategory.hom_ofHom, show ContinuousMap.inclusion h x = inclusion h x from
    Subtype.ext ((ContinuousMap.inclusion_apply_coe h x).trans (coe_inclusion h x).symm)]

/-- Over a subset of the base set of a chosen trivialization, the map is an isomorphism: read
through the trivialization it is the isomorphism `H₀(W) ≅ Hᵣ(W × F, W × (F ∖ {0}))` of the product
bundle after multiplying the class of each point by its unit. -/
private theorem isIso_thomPairOverSingularHomologyFinrankInv_of_subset
    (hg : IsLocalFiberGenerator K F E g ε) (c : B) {W : Set B}
    (hW : W ⊆ (trivializationAt F E c).baseSet) :
    IsIso (thomPairOverSingularHomologyFinrankInv hg W) := by
  have hu : ∀ ⦃x y : TopCat.of W⦄, Path x y → ε c x = ε c y := fun _ _ γ ↦
    hg.eq_of_path c continuous_subtypeVal (fun x ↦ hW x.property) γ
  have h : thomPairOverSingularHomologyFinrankInv hg W ≫
      TopPair.singularHomologyMap ((trivializationAt F E c).thomPairOverIso ℝ hW).hom
        (ModuleCat.of K K) (finrank ℝ F) =
      singularHomology₀UnitsSmul (ModuleCat.of K K) (fun x : TopCat.of W ↦ ε c x) hu ≫
        (prodThomPairSingularHomologyIso (ModuleCat.of K K) W F 0 (finrank ℝ F)).inv := by
    refine singularHomology₀_hom_ext _ fun x ↦ ?_
    rw [singularHomology₀Section_thomPairOverSingularHomologyFinrankInv_assoc,
      ModuleCat.ofHom_toSpanSingleton_comp,
      singularHomologyMap_thomPairOverIso_fiberClassOver hg c hW,
      singularHomology₀Section_singularHomology₀UnitsSmul_assoc, Linear.smul_comp]
    ext
    simp
  rw [(IsIso.eq_comp_inv _).2 h]
  infer_instance

/-! ### The passage to the whole base -/

/-- The map `H₀(B; K) ⟶ Hᵣ(E, E₀; K)` sending the class of a point to the fibre class over it. -/
private def thomPairSingularHomologyFinrankInv (hg : IsLocalFiberGenerator K F E g ε) :
    ((singularHomologyFunctor (ModuleCat.{w} K) 0).obj (ModuleCat.of K K)).obj (TopCat.of B) ⟶
      (thomPair F E).singularHomology (ModuleCat.of K K) (finrank ℝ F) :=
  ((singularHomologyFunctor (ModuleCat.{w} K) 0).obj (ModuleCat.of K K)).map
      (TopCat.isoOfHomeo (Homeomorph.Set.univ B).symm).hom ≫
    thomPairOverSingularHomologyFinrankInv hg univ ≫
      TopPair.singularHomologyMap (thomPairOverUnivIso F E).hom (ModuleCat.of K K) (finrank ℝ F)

private theorem singularHomology₀Section_thomPairSingularHomologyFinrankInv
    (hg : IsLocalFiberGenerator K F E g ε) (b : B) :
    singularHomology₀Section (ModuleCat.of K K) (X := TopCat.of B) b ≫
        thomPairSingularHomologyFinrankInv hg =
      ModuleCat.ofHom (LinearMap.toSpanSingleton K _ (TopPair.singularHomologyMap
        (fiberThomPairMap F E b) (ModuleCat.of K K) (finrank ℝ F) (g b))) := by
  rw [thomPairSingularHomologyFinrankInv, singularHomology₀Section_naturality_assoc,
    singularHomology₀Section_thomPairOverSingularHomologyFinrankInv_assoc,
    ModuleCat.ofHom_toSpanSingleton_comp, fiberClassOver, ← ConcreteCategory.comp_apply,
    ← TopPair.singularHomologyMap_comp]
  exact congrArg (fun f ↦ ModuleCat.ofHom (LinearMap.toSpanSingleton K _
    (TopPair.singularHomologyMap f (ModuleCat.of K K) (finrank ℝ F) (g b))))
    (fiberThomPairOverMap_comp_thomPairOverUnivIso_hom F E b)

/-- On a finite union of the chosen trivializing sets, the map over the base restricts to the
map over the union. -/
private theorem thomPairSingularHomologyFinrankInv_restrict (hg : IsLocalFiberGenerator K F E g ε)
    (s : Finset B) :
    ((singularHomologyFunctor (ModuleCat.{w} K) 0).obj (ModuleCat.of K K)).map
        (TopCat.ofHom ⟨Subtype.val, continuous_subtypeVal⟩ :
          TopCat.of ↥(⋃ b ∈ s, (trivializationAt F E b).baseSet) ⟶ TopCat.of B) ≫
        thomPairSingularHomologyFinrankInv hg =
      thomPairOverSingularHomologyFinrankInv hg (⋃ b ∈ s, (trivializationAt F E b).baseSet) ≫
        TopPair.singularHomologyMap (thomPairOverMap F E (subset_univ _) ≫
          (thomPairOverUnivIso F E).hom) (ModuleCat.of K K) (finrank ℝ F) := by
  refine singularHomology₀_hom_ext _ fun x ↦ ?_
  rw [singularHomology₀Section_naturality_assoc,
    singularHomology₀Section_thomPairSingularHomologyFinrankInv,
    singularHomology₀Section_thomPairOverSingularHomologyFinrankInv_assoc,
    ModuleCat.ofHom_toSpanSingleton_comp, fiberClassOver, ← ConcreteCategory.comp_apply,
    ← TopPair.singularHomologyMap_comp, fiberThomPairOverMap_comp_thomPairOverMap_assoc,
    fiberThomPairOverMap_comp_thomPairOverUnivIso_hom]

/-- **The passage to the whole base**: the homologies of the base and of the Thom pair are the
filtered colimits of their homologies over the finite unions of the chosen trivializing sets, and
over these the map is an isomorphism by the Mayer–Vietoris argument. -/
private theorem isIso_thomPairSingularHomologyFinrankInv (hg : IsLocalFiberGenerator K F E g ε) :
    IsIso (thomPairSingularHomologyFinrankInv hg) :=
  isIso_of_isColimit_biUnion_baseSet
    (A := TopCat.subspaceDiagram (A := (id : Set B → Set B)) monotone_id ⋙
      (singularHomologyFunctor (ModuleCat.{w} K) 0).obj (ModuleCat.of K K))
    (ψ := thomPairOverSingularHomologyFinrankInv hg) le_rfl
    (fun h ↦ thomPairOverSingularHomologyFinrankInv_naturality hg h)
    (fun _ _ ↦ epi_biprod_desc_singularHomologyMap_inclusion _ _ _)
    (isZero_singularHomology_of_isEmpty _ (TopCat.of (∅ : Set B)) 0)
    (fun c _ hW ↦ isIso_thomPairOverSingularHomologyFinrankInv_of_subset hg c hW)
    (isColimitMapCoconeSingularHomologySubset (X := TopCat.of B) (ModuleCat.of K K) 0
      (monotone_biUnion_baseSet_trivializationAt F E) fun _ hL ↦
        hL.elim_finite_subcover _ (fun b ↦ (trivializationAt F E b).open_baseSet) fun b _ ↦
          mem_iUnion.2 ⟨b, mem_baseSet_trivializationAt F E b⟩)
    (thomPairSingularHomologyFinrankInv hg) (thomPairSingularHomologyFinrankInv_restrict hg)

/-- The isomorphism `Hᵣ(E, E₀; K) ≅ H₀(B; K)` sending the fibre class of each `g b` to the class of
`b`. -/
private def thomPairSingularHomologyFinrankIsoOfIsLocalFiberGenerator
    (hg : IsLocalFiberGenerator K F E g ε) :
    (thomPair F E).singularHomology (ModuleCat.of K K) (finrank ℝ F) ≅
      ((singularHomologyFunctor (ModuleCat.{w} K) 0).obj (ModuleCat.of K K)).obj (TopCat.of B) :=
  have := isIso_thomPairSingularHomologyFinrankInv hg
  (asIso (thomPairSingularHomologyFinrankInv hg)).symm

private theorem thomPairSingularHomologyFinrankIsoOfIsLocalFiberGenerator_hom_apply
    (hg : IsLocalFiberGenerator K F E g ε) (b : B) :
    (thomPairSingularHomologyFinrankIsoOfIsLocalFiberGenerator hg).hom
        (TopPair.singularHomologyMap (fiberThomPairMap F E b) (ModuleCat.of K K) (finrank ℝ F)
          (g b)) =
      singularHomology₀Section (ModuleCat.of K K) (X := TopCat.of B) b 1 := by
  have := isIso_thomPairSingularHomologyFinrankInv hg
  have h := congrArg (fun f ↦ f (1 : K))
    (singularHomology₀Section_thomPairSingularHomologyFinrankInv hg b)
  simp only [ModuleCat.hom_ofHom, LinearMap.toSpanSingleton_apply, one_smul,
    ConcreteCategory.comp_apply] at h
  rw [← h, thomPairSingularHomologyFinrankIsoOfIsLocalFiberGenerator, Iso.symm_hom, asIso_inv,
    ← ConcreteCategory.comp_apply, IsIso.hom_inv_id, ConcreteCategory.id_apply]

/-! ### Coefficients with a single unit -/

variable (K F E) in
/-- The generator of `Hᵣ(E_b, E_b ∖ {0}; K) ≅ K`, read through the trivialization at `b`. -/
private def fiberGenerator (b : B) :
    ((TopPair.ofSubset (X := TopCat.of (E b)) ({0}ᶜ : Set (E b))).singularHomology
      (ModuleCat.of K K) (finrank ℝ F) : ModuleCat.{w} K) :=
  TopPair.singularHomologyMap ((trivializationAt F E b).continuousLinearEquivAt ℝ b
      (mem_baseSet_trivializationAt F E b)).complZeroPairIso.inv (ModuleCat.of K K) (finrank ℝ F)
    (complZeroPairPointHom (ModuleCat.of K K) F (finrank ℝ F) rfl (1 : K))

private theorem span_fiberGenerator (b : B) : Submodule.span K {fiberGenerator K F E b} = ⊤ :=
  (ModuleCat.span_singleton_apply_eq_top_iff _).2 (span_complZeroPairPointHom_one F K)

variable [Subsingleton Kˣ]

/-- Every generator of `Hᵣ(E_b, E_b ∖ {0}; K)` is the fibre generator. -/
private theorem eq_fiberGenerator {b : B} {x : ((TopPair.ofSubset (X := TopCat.of (E b))
    ({0}ᶜ : Set (E b))).singularHomology (ModuleCat.of K K) (finrank ℝ F) : ModuleCat.{w} K)}
    (hx : Submodule.span K {x} = ⊤) : x = fiberGenerator K F E b := by
  let L := (trivializationAt F E b).continuousLinearEquivAt ℝ b (mem_baseSet_trivializationAt F E b)
  apply (ModuleCat.mono_iff_injective (TopPair.singularHomologyMap L.complZeroPairIso.hom
    (ModuleCat.of K K) (finrank ℝ F))).1 inferInstance
  rw [eq_complZeroPairPointHom_one F K ((ModuleCat.span_singleton_apply_eq_top_iff _).2 hx),
    eq_complZeroPairPointHom_one F K
      ((ModuleCat.span_singleton_apply_eq_top_iff _).2 (span_fiberGenerator b))]

/-- With a single unit, the fibre generators are read as the generator of `Hᵣ(F, F ∖ {0}; K)` in
every trivialization. -/
private theorem isLocalFiberGenerator_fiberGenerator :
    IsLocalFiberGenerator K F E (fiberGenerator K F E) fun _ _ ↦ 1 where
  eventually_eq _ _ _ := .of_forall fun _ ↦ rfl
  map_eq c x hx := by
    simp only [Units.val_one, one_smul]
    exact eq_complZeroPairPointHom_one F K
      ((ModuleCat.span_singleton_apply_eq_top_iff _).2 (span_fiberGenerator x))

variable (K F E) in
/-- **The homology of the Thom pair in the rank degree**: for a real vector bundle `E → B` of
rank `r`, with Thom pair `(E, E₀)`, and a commutative ring `K` whose only unit is `1`, such as
`ZMod 2`, `Hᵣ(E, E₀; K) ≅ H₀(B; K)`. It sends the fibre class over `b` to the class of `b`
(`TauCeti.thomPairSingularHomologyFinrankIso_hom_apply`). The base is arbitrary and the bundle
need not be orientable. For an oriented bundle and an arbitrary commutative ring, see
`TauCeti.VectorBundleOrientation.thomPairSingularHomologyFinrankIso`. -/
def thomPairSingularHomologyFinrankIso :
    (thomPair F E).singularHomology (ModuleCat.of K K) (finrank ℝ F) ≅
      ((singularHomologyFunctor (ModuleCat.{w} K) 0).obj (ModuleCat.of K K)).obj (TopCat.of B) :=
  thomPairSingularHomologyFinrankIsoOfIsLocalFiberGenerator isLocalFiberGenerator_fiberGenerator

/-- **The isomorphism `Hᵣ(E, E₀; K) ≅ H₀(B; K)` sends the fibre class over `b` to the class of
`b`**: the fibre class is the image of any generator of `Hᵣ(E_b, E_b ∖ {0}; K) ≅ K` under the
inclusion of the fibre pair. -/
theorem thomPairSingularHomologyFinrankIso_hom_apply (b : B)
    {x : ((TopPair.ofSubset (X := TopCat.of (E b)) ({0}ᶜ : Set (E b))).singularHomology
      (ModuleCat.of K K) (finrank ℝ F) : ModuleCat.{w} K)} (hx : Submodule.span K {x} = ⊤) :
    (thomPairSingularHomologyFinrankIso K F E).hom
        (TopPair.singularHomologyMap (fiberThomPairMap F E b) (ModuleCat.of K K) (finrank ℝ F) x) =
      singularHomology₀Section (ModuleCat.of K K) (X := TopCat.of B) b 1 := by
  rw [eq_fiberGenerator hx]
  exact thomPairSingularHomologyFinrankIsoOfIsLocalFiberGenerator_hom_apply _ b

end Bundle

/-! ### Oriented bundles -/

namespace VectorBundleOrientation

variable {K : Type w} [CommRing K] {B : Type w} [TopologicalSpace B] {F : Type w}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {E : B → Type w}
  [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)]
  [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E] {ι : Type*} [Fintype ι]
  (o : VectorBundleOrientation F E ι) (hι : Fintype.card ι = finrank ℝ F)
  (ω : Orientation ℝ F ι)
  {γ : ((TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularHomology (ModuleCat.of K K)
    (finrank ℝ F) : ModuleCat.{w} K)}

open scoped Classical in
variable (γ) in
/-- The class of the fibre pair `(E_b, E_b ∖ {0})` which the trivialization at `b` reads as `γ`
if it reads the orientation `o b` as `ω`, and as `-γ` otherwise. -/
private def orientedFiberGenerator (b : B) :
    ((TopPair.ofSubset (X := TopCat.of (E b)) ({0}ᶜ : Set (E b))).singularHomology
      (ModuleCat.of K K) (finrank ℝ F) : ModuleCat.{w} K) :=
  if (trivializationAt F E b).mapOrientation ι (mem_baseSet_trivializationAt F E b) (o b) = ω then
    TopPair.singularHomologyMap ((trivializationAt F E b).continuousLinearEquivAt ℝ b
      (mem_baseSet_trivializationAt F E b)).complZeroPairIso.inv (ModuleCat.of K K) (finrank ℝ F) γ
  else
    -TopPair.singularHomologyMap ((trivializationAt F E b).continuousLinearEquivAt ℝ b
      (mem_baseSet_trivializationAt F E b)).complZeroPairIso.inv (ModuleCat.of K K) (finrank ℝ F) γ

open scoped Classical in
include hι in
/-- Every linear trivialization reads the oriented fibre generator as `γ` if it reads the
orientation as `ω`, and as `-γ` otherwise. -/
private theorem singularHomologyMap_complZeroPairIso_hom_orientedFiberGenerator
    (e : Trivialization F (π F E)) [e.IsLinear ℝ] {b : B} (hb : b ∈ e.baseSet) :
    TopPair.singularHomologyMap (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.hom
        (ModuleCat.of K K) (finrank ℝ F) (o.orientedFiberGenerator ω γ b) =
      if e.mapOrientation ι hb (o b) = ω then γ else -γ := by
  rw [orientedFiberGenerator]
  have hb₀ := mem_baseSet_trivializationAt F E b
  -- The trivialization at `b` reads its own pull-back of `γ` as `γ`.
  have h₀ : TopPair.singularHomologyMap
      ((trivializationAt F E b).continuousLinearEquivAt ℝ b hb₀).complZeroPairIso.hom
        (ModuleCat.of K K) (finrank ℝ F) (TopPair.singularHomologyMap
          ((trivializationAt F E b).continuousLinearEquivAt ℝ b hb₀).complZeroPairIso.inv
            (ModuleCat.of K K) (finrank ℝ F) γ) = γ :=
    (TopPair.singularHomologyMapIso _
      ((trivializationAt F E b).continuousLinearEquivAt ℝ b hb₀).complZeroPairIso
        _).inv_hom_id_apply γ
  have hne : -ω ≠ ω := (Module.Ray.ne_neg_self ω).symm
  -- Compare `e` with the trivialization at `b`: they induce equal maps if they read `o b` alike,
  -- and opposite ones otherwise.
  have hι' : Nat.card ι = finrank ℝ F := Nat.card_eq_fintype_card.trans hι
  rcases Orientation.eq_or_eq_neg ((trivializationAt F E b).mapOrientation ι hb₀ (o b)) ω hι'
    with h | h <;> rcases Orientation.eq_or_eq_neg (e.mapOrientation ι hb (o b)) ω hι' with h' | h'
  · rw [Trivialization.singularHomologyMap_complZeroPairIso_hom_eq_of_mapOrientation_eq
      _ e hb₀ hb hι _ (h'.trans h.symm)]
    simp [h, h', h₀]
  · rw [Trivialization.singularHomologyMap_complZeroPairIso_hom_eq_neg_of_mapOrientation_eq_neg
      _ e hb₀ hb hι _ (by rw [h, h'])]
    simp [h, h', h₀, hne]
  · rw [Trivialization.singularHomologyMap_complZeroPairIso_hom_eq_neg_of_mapOrientation_eq_neg
      _ e hb₀ hb hι _ (by rw [h, h']; exact (neg_neg ω).symm)]
    simp [h, h', h₀, hne]
  · rw [Trivialization.singularHomologyMap_complZeroPairIso_hom_eq_of_mapOrientation_eq
      _ e hb₀ hb hι _ (h'.trans h.symm)]
    simp [h, h', h₀, hne]

open scoped Classical in
include hι in
/-- Every linear trivialization pulls `γ` back to the oriented fibre generator if it reads the
orientation as `ω`, and to its negative otherwise. -/
private theorem singularHomologyMap_complZeroPairIso_inv_eq_orientedFiberGenerator
    (e : Trivialization F (π F E)) [e.IsLinear ℝ] {b : B} (hb : b ∈ e.baseSet) :
    TopPair.singularHomologyMap (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.inv
        (ModuleCat.of K K) (finrank ℝ F) γ =
      if e.mapOrientation ι hb (o b) = ω then o.orientedFiberGenerator ω γ b
      else -o.orientedFiberGenerator ω γ b := by
  apply (ModuleCat.mono_iff_injective (TopPair.singularHomologyMap
    (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.hom (ModuleCat.of K K)
      (finrank ℝ F))).1 inferInstance
  refine ((TopPair.singularHomologyMapIso _ (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso
    _).inv_hom_id_apply γ).trans ?_
  split_ifs with h
  · rw [o.singularHomologyMap_complZeroPairIso_hom_orientedFiberGenerator hι ω e hb, ite_eq_left h]
  · rw [map_neg, o.singularHomologyMap_complZeroPairIso_hom_orientedFiberGenerator hι ω e hb,
      ite_eq_right h, neg_neg]

open scoped Classical in
include hι in
/-- The oriented fibre generators of a generator `γ = u • γ₀` of `Hᵣ(F, F ∖ {0}; K)` are read in
the trivialization at `c` as `γ₀` multiplied by `u` or `-u`, according to the reading of the
orientation, which is locally constant. -/
private theorem isLocalFiberGenerator_orientedFiberGenerator {u : Kˣ}
    (hu : γ = (u : K) • complZeroPairPointHom (ModuleCat.of K K) F (finrank ℝ F) rfl (1 : K)) :
    IsLocalFiberGenerator K F E (o.orientedFiberGenerator ω γ) fun c x ↦
      if hx : x ∈ (trivializationAt F E c).baseSet then
        if (trivializationAt F E c).mapOrientation ι hx (o x) = ω then u else -u
      else u where
  eventually_eq c b hb := by
    filter_upwards [o.eventually_mapOrientation_eq hι (trivializationAt F E c) hb,
      (trivializationAt F E c).open_baseSet.mem_nhds hb] with x hx hxb
    simp only [dite_eq_left hxb, dite_eq_left hb, hx hxb]
  map_eq c x hx := by
    simp only [o.singularHomologyMap_complZeroPairIso_hom_orientedFiberGenerator hι ω _ hx,
      dite_eq_left hx]
    split_ifs
    · exact hu
    · rw [hu, Units.val_neg, neg_smul]

/-- **The homology of the Thom pair of an oriented bundle in the rank degree**: for a real vector
bundle `E → B` of rank `r` with an orientation `o`, with Thom pair `(E, E₀)`, and any commutative
ring `K`, for instance `ℤ`, `Hᵣ(E, E₀; K) ≅ H₀(B; K)`. It is normalized by an orientation `ω` of
the model fibre `F` and a generator `γ` of `Hᵣ(F, F ∖ {0}; K) ≅ K`: it sends the class of the fibre
pair over `b` which a linear trivialization reads as `γ` to the class of `b` if the trivialization
reads `o b` as `ω`
(`thomPairSingularHomologyFinrankIso_hom_apply_of_mapOrientation_eq`),
and to its negative if it reads `o b` as `-ω`. The base is arbitrary. Without an orientation the
same holds when `1` is the only unit of `K` (`TauCeti.thomPairSingularHomologyFinrankIso`). -/
def thomPairSingularHomologyFinrankIso (hγ : Submodule.span K {γ} = ⊤) :
    (thomPair F E).singularHomology (ModuleCat.of K K) (finrank ℝ F) ≅
      ((singularHomologyFunctor (ModuleCat.{w} K) 0).obj (ModuleCat.of K K)).obj (TopCat.of B) :=
  thomPairSingularHomologyFinrankIsoOfIsLocalFiberGenerator
    (o.isLocalFiberGenerator_orientedFiberGenerator hι ω
      (exists_eq_units_smul_complZeroPairPointHom_one F K hγ).choose_spec)

/-- The oriented isomorphism `Hᵣ(E, E₀; K) ≅ H₀(B; K)` sends the class of the fibre pair over `b`
which a linear trivialization reading `o b` as `ω` reads as `γ` to the class of `b`. -/
theorem thomPairSingularHomologyFinrankIso_hom_apply_of_mapOrientation_eq
    (hγ : Submodule.span K {γ} = ⊤) (e : Trivialization F (π F E)) [e.IsLinear ℝ] {b : B}
    (hb : b ∈ e.baseSet) (h : e.mapOrientation ι hb (o b) = ω) :
    (o.thomPairSingularHomologyFinrankIso hι ω hγ).hom
        (TopPair.singularHomologyMap (fiberThomPairMap F E b) (ModuleCat.of K K) (finrank ℝ F)
          (TopPair.singularHomologyMap (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.inv
            (ModuleCat.of K K) (finrank ℝ F) γ)) =
      singularHomology₀Section (ModuleCat.of K K) (X := TopCat.of B) b 1 := by
  rw [o.singularHomologyMap_complZeroPairIso_inv_eq_orientedFiberGenerator hι ω e hb, ite_eq_left h]
  exact thomPairSingularHomologyFinrankIsoOfIsLocalFiberGenerator_hom_apply _ b

/-- The oriented isomorphism `Hᵣ(E, E₀; K) ≅ H₀(B; K)` sends the class of the fibre pair over `b`
which a linear trivialization reading `o b` as `-ω` reads as `γ` to minus the class of `b`. -/
theorem thomPairSingularHomologyFinrankIso_hom_apply_of_mapOrientation_eq_neg
    (hγ : Submodule.span K {γ} = ⊤) (e : Trivialization F (π F E)) [e.IsLinear ℝ] {b : B}
    (hb : b ∈ e.baseSet) (h : e.mapOrientation ι hb (o b) = -ω) :
    (o.thomPairSingularHomologyFinrankIso hι ω hγ).hom
        (TopPair.singularHomologyMap (fiberThomPairMap F E b) (ModuleCat.of K K) (finrank ℝ F)
          (TopPair.singularHomologyMap (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.inv
            (ModuleCat.of K K) (finrank ℝ F) γ)) =
      -singularHomology₀Section (ModuleCat.of K K) (X := TopCat.of B) b 1 := by
  rw [o.singularHomologyMap_complZeroPairIso_inv_eq_orientedFiberGenerator hι ω e hb,
    ite_eq_right (h.trans_ne (Module.Ray.ne_neg_self ω).symm), map_neg, map_neg]
  exact congrArg Neg.neg (thomPairSingularHomologyFinrankIsoOfIsLocalFiberGenerator_hom_apply _ b)

end VectorBundleOrientation

end TauCeti
