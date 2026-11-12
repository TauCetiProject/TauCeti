/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.MayerVietoris.DirectedUnion
public import TauCeti.AlgebraicTopology.Singular.ZerothHomology
import TauCeti.Algebra.Module.Equiv.SpanSingleton
import TauCeti.AlgebraicTopology.Singular.LocalHomology.Basic

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

## Main results

* `TauCeti.thomPairSingularHomologyFinrankIso`: `Hᵣ(E, E₀; K) ≅ H₀(B; K)` for `r` the rank and `K`
  a commutative ring whose only unit is `1`.
* `TauCeti.thomPairSingularHomologyFinrankIso_hom_apply`: it sends the fibre class over `b` to the
  class of `b`.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10, Lemma 10.3 and the proof of Theorem 10.4 (the induction over finite unions
  of trivializing open sets and the passage to a directed union).
* A. Hatcher, *Algebraic Topology*, Section 4.D, Theorem 4D.10 and its proof, which also covers
  `ℤ/2` coefficients for bundles without an orientation.
-/

public noncomputable section

open Bundle CategoryTheory Limits Set Module AlgebraicTopology Topology

universe w

namespace TauCeti

section Module

variable {K : Type w} [CommRing K]

/-- Following the map `K ⟶ M`, `a ↦ a • m`, by a morphism `f` gives `a ↦ a • f m`. -/
private theorem ofHom_toSpanSingleton_comp {M N : ModuleCat.{w} K} (m : M) (f : M ⟶ N) :
    ModuleCat.ofHom (LinearMap.toSpanSingleton K M m) ≫ f =
      ModuleCat.ofHom (LinearMap.toSpanSingleton K N (f m)) :=
  ModuleCat.hom_ext (LinearMap.comp_toSpanSingleton f.hom m)

/-- An isomorphism of modules carries generators to generators. -/
private theorem span_apply_eq_top_of_isIso {M N : ModuleCat.{w} K} (f : M ⟶ N) [IsIso f] {x : M}
    (hx : Submodule.span K {x} = ⊤) : Submodule.span K {f x} = ⊤ :=
  (LinearEquiv.span_singleton_apply_eq_top_iff (asIso f).toLinearEquiv).2 hx

end Module

section Fiber

variable (K : Type w) [CommRing K] (F : Type w) [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- The pair `(F, F ∖ {0})` is the Thom pair of the product bundle over a point. -/
private def complZeroPairIsoProdThomPair :
    TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F) ≅ prodThomPair PUnit.{w + 1} F where
  hom := prodThomPairFiberMap F PUnit.unit
  inv := prodThomPairSnd PUnit.{w + 1} F
  hom_inv_id := prodThomPairFiberMap_comp_prodThomPairSnd F _
  inv_hom_id := prodThomPairSnd_comp_prodThomPairFiberMap F

/-- The generator of `Hᵣ(F, F ∖ {0}; K)` corresponding to the class of the point in `H₀(pt; K)`. -/
private def complZeroPairGenerator :
    ((TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularHomology (ModuleCat.of K K)
      (finrank ℝ F) : ModuleCat.{w} K) :=
  TopPair.singularHomologyMap (complZeroPairIsoProdThomPair F).inv (ModuleCat.of K K) (finrank ℝ F)
    ((prodThomPairSingularHomologyIso (ModuleCat.of K K) PUnit.{w + 1} F 0 (finrank ℝ F)).inv
      (singularHomology₀Section (ModuleCat.of K K) (X := TopCat.of PUnit.{w + 1}) PUnit.unit 1))

/-- The fibre inclusion over the point carries the generator to the class of the point. -/
private theorem singularHomologyMap_prodThomPairFiberMap_complZeroPairGenerator :
    TopPair.singularHomologyMap (prodThomPairFiberMap F PUnit.unit) (ModuleCat.of K K)
        (finrank ℝ F) (complZeroPairGenerator K F) =
      (prodThomPairSingularHomologyIso (ModuleCat.of K K) PUnit.{w + 1} F 0 (finrank ℝ F)).inv
        (singularHomology₀Section (ModuleCat.of K K) (X := TopCat.of PUnit.{w + 1}) PUnit.unit
          1) := by
  rw [complZeroPairGenerator, ← ConcreteCategory.comp_apply, ← TopPair.singularHomologyMap_comp]
  exact congrArg (fun f ↦ TopPair.singularHomologyMap f (ModuleCat.of K K) (finrank ℝ F) _)
    (complZeroPairIsoProdThomPair F).inv_hom_id |>.trans (by simp)

private theorem span_complZeroPairGenerator :
    Submodule.span K {complZeroPairGenerator K F} = ⊤ := by
  -- The class of the point generates `H₀(pt; K)`, being the inverse of the augmentation `≅ K`
  -- applied to `1`.
  have hpt : Submodule.span K {(singularHomology₀Section (ModuleCat.of K K)
      (X := TopCat.of PUnit.{w + 1}) PUnit.unit (1 : K) :)} = ⊤ := by
    rw [IsIso.eq_inv_of_inv_hom_id (singularHomology₀Section_singularHomology₀ε _ _)]
    exact span_apply_eq_top_of_isIso _ Ideal.span_singleton_one
  exact span_apply_eq_top_of_isIso _ (span_apply_eq_top_of_isIso _ hpt)

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
  span_apply_eq_top_of_isIso _ (span_complZeroPairGenerator K F)

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
  rw [eq_complZeroPairGenerator K F (span_apply_eq_top_of_isIso _ hx),
    eq_complZeroPairGenerator K F (span_apply_eq_top_of_isIso _ (span_fiberGenerator b))]

/-- A linear trivialization at `b` carries the fibre generator to the generator of
`Hᵣ(F, F ∖ {0}; K)`. -/
private theorem singularHomologyMap_complZeroPairIso_fiberGenerator
    (e : Trivialization F (π F E)) [e.IsLinear ℝ] {b : B} (hb : b ∈ e.baseSet) :
    TopPair.singularHomologyMap (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.hom
      (ModuleCat.of K K) (finrank ℝ F) (fiberGenerator K F E b) = complZeroPairGenerator K F :=
  eq_complZeroPairGenerator K F (span_apply_eq_top_of_isIso _ (span_fiberGenerator b))

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
    TopPair.singularHomologyMap_comp,
    ConcreteCategory.comp_apply, singularHomologyMap_complZeroPairIso_fiberGenerator e (hW x.2),
    Subtype.coe_eta, ← ContinuousMap.const_apply (α := PUnit.{w + 1}) x PUnit.unit,
    ← prodThomPairFiberMap_comp_prodThomPairMap F PUnit.unit (ContinuousMap.const _ x),
    TopPair.singularHomologyMap_comp, ConcreteCategory.comp_apply,
    singularHomologyMap_prodThomPairFiberMap_complZeroPairGenerator]
  -- The isomorphism `Hᵣ(B × F, B × (F ∖ {0})) ≅ H₀(B)` is natural in the base.
  have h :
      (prodThomPairSingularHomologyIso (ModuleCat.of K K) PUnit.{w + 1} F 0 (finrank ℝ F)).inv ≫
      TopPair.singularHomologyMap (prodThomPairMap F (ContinuousMap.const PUnit.{w + 1} x))
        (ModuleCat.of K K) (finrank ℝ F) =
      ((singularHomologyFunctor (ModuleCat.{w} K) 0).obj (ModuleCat.of K K)).map
          (TopCat.ofHom (ContinuousMap.const PUnit.{w + 1} x)) ≫
        (prodThomPairSingularHomologyIso (ModuleCat.of K K) W F 0 (finrank ℝ F)).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv,
      prodThomPairSingularHomologyIso_hom_naturality (ModuleCat.of K K) PUnit.{w + 1} F
        (ContinuousMap.const PUnit.{w + 1} x) 0 (finrank ℝ F)]
  rw [← ConcreteCategory.comp_apply, h, ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply
    (singularHomology₀Section _ _), singularHomology₀Section_naturality]
  simp

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
    ofHom_toSpanSingleton_comp, singularHomologyMap_thomPairOverMap_fiberClassOver]
  -- `ContinuousMap.inclusion h` is `Set.inclusion h` by definition; Mathlib has no `apply` lemma.
  rfl

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
    ofHom_toSpanSingleton_comp, singularHomologyMap_thomPairOverIso_fiberClassOver e hW]
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

/-- **The Mayer–Vietoris step**: if the maps over the open sets `U` and `V` are isomorphisms and
the map over `U ∩ V` is surjective, the map over `U ∪ V` is an isomorphism. -/
private theorem isIso_thomPairOverSingularHomologyFinrankInv_union {U V : Set B} (hU : IsOpen U)
    (hV : IsOpen V) [IsIso (thomPairOverSingularHomologyFinrankInv K F E U)]
    [IsIso (thomPairOverSingularHomologyFinrankInv K F E V)]
    [Epi (thomPairOverSingularHomologyFinrankInv K F E (U ∩ V))]
    (hUV : ∀ m, m + 1 = finrank ℝ F →
      IsZero ((thomPairOver F E (U ∩ V)).singularHomology (ModuleCat.of K K) m)) :
    IsIso (thomPairOverSingularHomologyFinrankInv K F E (U ∪ V)) := by
  let ψ := thomPairOverSingularHomologyFinrankInv K F E
  let H₀ := (singularHomologyFunctor (ModuleCat.{w} K) 0).obj (ModuleCat.of K K)
  let S := ShortComplex.mk _ _ (singularHomology_thomPairOver_mayerVietoris_zero (F := F) (E := E)
    (U := U) (V := V) (ModuleCat.of K K) (finrank ℝ F))
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
    have hU' : ψ (U ∩ V) ≫ TopPair.singularHomologyMap (thomPairOverMap F E inter_subset_left)
        (ModuleCat.of K K) (finrank ℝ F) ≫ inv (ψ U) =
          H₀.map (TopCat.ofHom (ContinuousMap.inclusion inter_subset_left)) := by
      rw [← Category.assoc, ← thomPairOverSingularHomologyFinrankInv_naturality, Category.assoc,
        IsIso.hom_inv_id, Category.comp_id]
    have hV' : ψ (U ∩ V) ≫ TopPair.singularHomologyMap (thomPairOverMap F E inter_subset_right)
        (ModuleCat.of K K) (finrank ℝ F) ≫ inv (ψ V) =
          H₀.map (TopCat.ofHom (ContinuousMap.inclusion inter_subset_right)) := by
      rw [← Category.assoc, ← thomPairOverSingularHomologyFinrankInv_naturality, Category.assoc,
        IsIso.hom_inv_id, Category.comp_id]
    rw [← cancel_epi (ψ (U ∩ V)), comp_zero]
    simp only [S, φ, biprod.lift_desc, Preadditive.neg_comp, Preadditive.comp_add,
      Preadditive.comp_neg, reassoc_of% hU', reassoc_of% hV',
      ← Functor.map_comp, add_neg_eq_zero]
    -- Both composites are the inclusion of `U ∩ V` into `U ∪ V`.
    rfl
  let Φ := (hS.gIsCokernel).desc (CokernelCofork.ofπ φ hφ)
  have hgΦ : S.g ≫ Φ = φ := (hS.gIsCokernel).fac (CokernelCofork.ofπ φ hφ) WalkingParallelPair.one
  -- On the classes over `U` and over `V`, `Φ` is the inverse of the map over `U` or `V`.
  have hΦU : TopPair.singularHomologyMap (thomPairOverMap F E (subset_union_left : U ⊆ U ∪ V))
      (ModuleCat.of K K) (finrank ℝ F) ≫ Φ =
        inv (ψ U) ≫ H₀.map (TopCat.ofHom (ContinuousMap.inclusion subset_union_left)) := by
    rw [← biprod.inl_desc (TopPair.singularHomologyMap (thomPairOverMap F E
      (subset_union_left : U ⊆ U ∪ V)) (ModuleCat.of K K) (finrank ℝ F))
      (TopPair.singularHomologyMap (thomPairOverMap F E (subset_union_right : V ⊆ U ∪ V))
        (ModuleCat.of K K) (finrank ℝ F)), Category.assoc]
    exact (congrArg (biprod.inl ≫ ·) hgΦ).trans (biprod.inl_desc _ _)
  have hΦV : TopPair.singularHomologyMap (thomPairOverMap F E (subset_union_right : V ⊆ U ∪ V))
      (ModuleCat.of K K) (finrank ℝ F) ≫ Φ =
        inv (ψ V) ≫ H₀.map (TopCat.ofHom (ContinuousMap.inclusion subset_union_right)) := by
    rw [← biprod.inr_desc (TopPair.singularHomologyMap (thomPairOverMap F E
      (subset_union_left : U ⊆ U ∪ V)) (ModuleCat.of K K) (finrank ℝ F))
      (TopPair.singularHomologyMap (thomPairOverMap F E (subset_union_right : V ⊆ U ∪ V))
        (ModuleCat.of K K) (finrank ℝ F)), Category.assoc]
    exact (congrArg (biprod.inr ≫ ·) hgΦ).trans (biprod.inr_desc _ _)
  refine ⟨Φ, ?_, ?_⟩
  · -- On the class of a point of `U` (or of `V`), the composite is computed over `U` (or `V`).
    refine singularHomology₀_hom_ext _ fun x ↦ ?_
    rw [Category.comp_id]
    obtain ⟨x, hx | hx⟩ := x
    · have hx' : singularHomology₀Section (ModuleCat.of K K) (X := TopCat.of U) ⟨x, hx⟩ ≫
          H₀.map (TopCat.ofHom (ContinuousMap.inclusion subset_union_left)) =
            singularHomology₀Section (ModuleCat.of K K) (X := TopCat.of ↥(U ∪ V))
              ⟨x, Or.inl hx⟩ :=
        singularHomology₀Section_naturality _ _ _
      rw [← hx', Category.assoc, reassoc_of% (thomPairOverSingularHomologyFinrankInv_naturality
        (K := K) (F := F) (E := E) (subset_union_left : U ⊆ U ∪ V)), hΦU,
        IsIso.hom_inv_id_assoc]
    · have hx' : singularHomology₀Section (ModuleCat.of K K) (X := TopCat.of V) ⟨x, hx⟩ ≫
          H₀.map (TopCat.ofHom (ContinuousMap.inclusion subset_union_right)) =
            singularHomology₀Section (ModuleCat.of K K) (X := TopCat.of ↥(U ∪ V))
              ⟨x, Or.inr hx⟩ :=
        singularHomology₀Section_naturality _ _ _
      rw [← hx', Category.assoc, reassoc_of% (thomPairOverSingularHomologyFinrankInv_naturality
        (K := K) (F := F) (E := E) (subset_union_right : V ⊆ U ∪ V)), hΦV,
        IsIso.hom_inv_id_assoc]
  · -- The second map of the Mayer–Vietoris sequence is an epimorphism.
    refine (cancel_epi S.g).1 (biprod.hom_ext' _ _ ?_ ?_)
    · simp only [S, Category.comp_id, biprod.inl_desc_assoc, biprod.inl_desc]
      rw [reassoc_of% hΦU, thomPairOverSingularHomologyFinrankInv_naturality,
        IsIso.inv_hom_id_assoc]
    · simp only [S, Category.comp_id, biprod.inr_desc_assoc, biprod.inr_desc]
      rw [reassoc_of% hΦV, thomPairOverSingularHomologyFinrankInv_naturality,
        IsIso.inv_hom_id_assoc]

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
    ofHom_toSpanSingleton_comp, fiberClassOver, ← ConcreteCategory.comp_apply,
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
    ofHom_toSpanSingleton_comp, fiberClassOver, ← ConcreteCategory.comp_apply,
    ← TopPair.singularHomologyMap_comp, fiberThomPairOverMap_comp_thomPairOverMap_assoc,
    fiberThomPairOverMap_comp_thomPairOverUnivIso_hom]

omit [CommRing K] in
/-- The map on homology induced by `eqToHom` of an equation of pairs. -/
private theorem singularHomologyMap_eqToHom [CommRing K] {P Q : TopPair.{w}} (h : P = Q) (n : ℕ) :
    TopPair.singularHomologyMap (eqToHom h) (ModuleCat.of K K) n =
      eqToHom (congrArg (TopPair.singularHomology · (ModuleCat.of K K) n) h) := by
  subst h
  simp

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

/-- **The passage to the whole base**: the homologies of the base and of the Thom pair are the
filtered colimits of their homologies over the finite unions of the chosen trivializing sets, and
over these the map is an isomorphism. -/
private instance : IsIso (thomPairSingularHomologyFinrankInv K F E) := by
  let H₀ := (singularHomologyFunctor (ModuleCat.{w} K) 0).obj (ModuleCat.of K K)
  let H := TopPair.singularHomologyFunctor (ModuleCat.of K K) (finrank ℝ F)
  let P₁ := isColimitMapCoconeSingularHomology (ModuleCat.of K K) 0
    (baseFiniteTrivializingUnionCocone F E) (fun _ ↦ IsEmbedding.subtypeVal) fun L hL ↦ by
      obtain ⟨s, hs⟩ := hL.elim_finite_subcover _
        (fun b ↦ (trivializationAt F E b).open_baseSet) fun b _ ↦
          mem_iUnion.2 ⟨b, mem_baseSet_trivializationAt F E b⟩
      exact ⟨s, fun b hb ↦ ⟨⟨b, hs hb⟩, rfl⟩⟩
  let P₂ := isColimitMapCoconeSingularHomologyThomPairFiniteTrivializingUnion (F := F) (E := E)
    (ModuleCat.of K K) (finrank ℝ F)
  have hiso (s : Finset B) : IsIso (thomPairOverSingularHomologyFinrankInv K F E
      (⋃ b ∈ s, (trivializationAt F E b).baseSet)) :=
    isIso_thomPairOverSingularHomologyFinrankInv_biUnion s
      (fun b _ ↦ (trivializationAt F E b).open_baseSet)
      fun b _ ↦ ⟨trivializationAt F E b, inferInstance, subset_rfl⟩
  -- The objects of the diagram of Thom pairs are the Thom pairs over the finite unions only up to
  -- the equations `thomPairFiniteTrivializingUnionDiagram_obj`, so the components carry them.
  have hobj (s : Finset B) :
      (thomPairOver F E (⋃ b ∈ s, (trivializationAt F E b).baseSet)).singularHomology
        (ModuleCat.of K K) (finrank ℝ F) =
        H.obj ((thomPairFiniteTrivializingUnionDiagram (F := F) (E := E)).obj s) := by
    rw [thomPairFiniteTrivializingUnionDiagram_obj, TopPair.singularHomologyFunctor_obj]
  let α : baseFiniteTrivializingUnionDiagram F E ⋙ H₀ ≅
      thomPairFiniteTrivializingUnionDiagram (F := F) (E := E) ⋙ H :=
    NatIso.ofComponents (fun s ↦ @asIso _ _ _ _ (thomPairOverSingularHomologyFinrankInv K F E
        (⋃ b ∈ s, (trivializationAt F E b).baseSet)) (hiso s) ≪≫ eqToIso (hobj s))
      fun {s t} f ↦ by
        dsimp only [Functor.comp_obj, Functor.comp_map, baseFiniteTrivializingUnionDiagram]
        simp only [H, thomPairFiniteTrivializingUnionDiagram_map,
          TopPair.singularHomologyFunctor_map, Iso.trans_hom, asIso_hom, eqToIso.hom,
          Category.assoc, TopPair.singularHomologyMap_comp, singularHomologyMap_eqToHom,
          eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
        rw [← Category.assoc, thomPairOverSingularHomologyFinrankInv_naturality
          (W := ⋃ b ∈ s, (trivializationAt F E b).baseSet)
          (W' := ⋃ b ∈ t, (trivializationAt F E b).baseSet) (biUnion_subset_biUnion_left f.le),
          Category.assoc, eqToHom_trans]
  -- The induced map of colimits is the map over the base.
  have hpt : (thomPair F E).singularHomology (ModuleCat.of K K) (finrank ℝ F) =
      H.obj (thomPairFiniteTrivializingUnionCocone (F := F) (E := E)).pt := by
    rw [thomPairFiniteTrivializingUnionCocone_pt, TopPair.singularHomologyFunctor_obj]
  have h : thomPairSingularHomologyFinrankInv K F E ≫ eqToHom hpt =
      (P₁.coconePointsIsoOfNatIso P₂ α).hom := by
    refine P₁.hom_ext fun s ↦ Eq.trans ?_ (P₁.comp_coconePointsIsoOfNatIso_hom P₂ α s).symm
    have hs : H₀.map (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ :
          TopCat.of ↥(⋃ b ∈ s, (trivializationAt F E b).baseSet) ⟶ TopCat.of B) ≫
          thomPairSingularHomologyFinrankInv K F E ≫ eqToHom hpt =
        thomPairOverSingularHomologyFinrankInv K F E
            (⋃ b ∈ s, (trivializationAt F E b).baseSet) ≫ eqToHom (hobj s) ≫
          H.map ((thomPairFiniteTrivializingUnionCocone (F := F) (E := E)).ι.app s) := by
      rw [reassoc_of% (thomPairSingularHomologyFinrankInv_restrict (K := K) s)]
      simp only [H, thomPairFiniteTrivializingUnionCocone_ι_app,
        TopPair.singularHomologyFunctor_map, Category.assoc, TopPair.singularHomologyMap_comp,
        singularHomologyMap_eqToHom, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
        eqToHom_trans]
    exact hs
  have : IsIso (thomPairSingularHomologyFinrankInv K F E ≫ eqToHom hpt) := by
    rw [h]
    exact (P₁.coconePointsIsoOfNatIso P₂ α).isIso_hom
  exact IsIso.of_isIso_comp_right _ (eqToHom hpt)

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

end TauCeti
