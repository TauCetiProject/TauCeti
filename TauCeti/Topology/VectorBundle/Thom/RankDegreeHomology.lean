/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.MayerVietoris.DirectedUnion
public import TauCeti.Topology.VectorBundle.Orientation.Basic
public import TauCeti.AlgebraicTopology.Singular.Reduced
import TauCeti.Algebra.Category.ModuleCat.SpanSingleton
import TauCeti.AlgebraicTopology.Singular.LocalHomology.Basic
import TauCeti.AlgebraicTopology.Singular.LocalHomology.Linear

/-!
# The homology of the Thom pair in the rank degree

Let `E → B` be a real vector bundle of rank `r` over an arbitrary base, with Thom pair `(E, E₀)`,
and let `K` be a commutative ring. The relative homology `Hₙ(E, E₀; K)` vanishes for `n < r`
(`TauCeti.isZero_singularHomology_thomPair`). This file computes the first group that does not
vanish,

`Hᵣ(E, E₀; K) ≅ H₀(B; K)`,

whenever the generators of the fibre groups `Hᵣ(E_b, E_b ∖ {0}; K) ≅ K` can be chosen coherently.
A family `c` of such generators is coherent when it is locally constant read in the trivializations
of the atlas: a linear trivialization `e` identifies each fibre pair over its base set with
`(F, F ∖ {0})`, and the generators `c x` read through `e` must agree near each point. For such a
family the isomorphism sends the fibre class over `b`, the image of `c b` under the inclusion of the
fibre pair, to the class of the point `b`
(`TauCeti.thomPairSingularHomologyFinrankIsoOfGenerators`,
`TauCeti.thomPairSingularHomologyFinrankIsoOfGenerators_hom_apply`).
This is the bottom degree of the Thom isomorphism `Hₙ₊ᵣ(E, E₀; K) ≅ Hₙ(B; K)` in homology.

Two sources of coherent generators are treated.

* When `1` is the only unit of `K`, as for `ZMod 2`, the module `Hᵣ(E_b, E_b ∖ {0}; K) ≅ K` has a
  single generator, so the fibre classes do not depend on any choice and no orientation is needed
  (`TauCeti.thomPairSingularHomologyFinrankIso`).
* An orientation `o` of the bundle chooses them over every commutative ring `K`, the integers
  included. Fix an orientation `ω` of the model fibre `F` and a generator `g` of
  `Hᵣ(F, F ∖ {0}; K)`. A linear trivialization changes `g` by the sign of the determinant of its
  coordinate change
  (`Bundle.Trivialization.singularHomologyMap_complZeroPairIso_hom_eq_sign_det_smul`),
  so the class of the fibre pair over `b` that a trivialization carrying `o b` to `ω` reads as `g`,
  and one carrying `o b` to `-ω` reads as `-g`, does not depend on the trivialization. The resulting
  isomorphism `TauCeti.VectorBundleOrientation.thomPairSingularHomologyFinrankIsoOfModel` sends
  these fibre classes to the classes of the points. This is the homological counterpart of the
  Thom class `TauCeti.VectorBundleOrientation.thomClassOfModel` of an oriented bundle.

## The proof

The inverse map `H₀(B; K) ⟶ Hᵣ(E, E₀; K)` is defined on the classes of points, which generate
`H₀(B; K)`: it sends the class of `b` to the fibre class over `b`. This is well defined because the
fibre classes are constant along paths in the base. Over a subset `W` of the base set of a
trivialization `e` of the atlas, the trivialization identifies the Thom pair `(E|_W, E₀|_W)` with
the Thom pair of the product bundle `W × F`, whose homology in degree `r` is `H₀(W; K)`
(`TauCeti.prodThomPairSingularHomologyIso`). This identification sends the fibre class over a
point `x` to `u x` times the class of `x`, where `u x` is the unit by which `e` reads `c x` as a
multiple of a fixed generator of `Hᵣ(F, F ∖ {0}; K)`. Since `u` is locally constant, this
endomorphism of `H₀(W; K)` is an isomorphism
(`TauCeti.isIso_of_singularHomology₀Section_comp_eq`), and so is the map over `W`. The
Mayer–Vietoris sequence of the Thom pairs over two open sets
(`TauCeti.singularHomology_thomPairOver_mayerVietoris_exact`) ends in degree `r`, since the
homology vanishes below the rank, so the map is an isomorphism over a finite union of trivializing
open sets by induction on their number. Singular homology has compact supports, so the homology of
the base and of the Thom pair are the filtered colimits of their homology over these finite unions,
and the map is an isomorphism over the whole base.

## Main results

* `TauCeti.thomPairSingularHomologyFinrankIsoOfGenerators`: `Hᵣ(E, E₀; K) ≅ H₀(B; K)` for a
  family of generators of the fibre groups that is locally constant in the trivializations of the
  atlas, with `TauCeti.thomPairSingularHomologyFinrankIsoOfGenerators_hom_apply`.
* `TauCeti.thomPairSingularHomologyFinrankIso`: the isomorphism for a commutative ring `K` whose
  only unit is `1`, and `TauCeti.thomPairSingularHomologyFinrankIso_hom_apply`: it sends the fibre
  class over `b` to the class of `b`.
* `TauCeti.VectorBundleOrientation.thomPairSingularHomologyFinrankIsoOfModel`: the isomorphism for
  an oriented bundle and any commutative ring `K`, with its evaluation lemmas
  `thomPairSingularHomologyFinrankIsoOfModel_hom_apply_of_mapOrientation_eq` and
  `thomPairSingularHomologyFinrankIsoOfModel_hom_apply_of_mapOrientation_eq_neg` in the same
  namespace.
* `Bundle.Trivialization.singularHomologyMap_complZeroPairIso_hom_eq_sign_det_smul`: two linear
  trivializations read the homology of a fibre pair up to the sign of the determinant of their
  coordinate change.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10, Lemma 10.3 and the proof of Theorem 10.4 (the induction over finite unions
  of trivializing open sets and the passage to a directed union).
* A. Hatcher, *Algebraic Topology*, Section 4.D, Theorem 4D.10 and its proof, which also covers
  `ℤ/2` coefficients for bundles without an orientation.
-/

public noncomputable section

open Bundle CategoryTheory Filter Limits Set Module AlgebraicTopology Topology

universe w

namespace TauCeti

section Fiber

variable (K : Type w) [CommRing K] (F : Type w) [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- The generator of `Hᵣ(F, F ∖ {0}; K)` corresponding to the class of the point in `H₀(pt; K)`. -/
private def complZeroPairGenerator :
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
private theorem singularHomologyMap_prodThomPairFiberMap_complZeroPairGenerator
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

private theorem span_complZeroPairGenerator :
    Submodule.span K {complZeroPairGenerator K F} = ⊤ := by
  -- The class of the point generates `H₀(pt; K)`, being the inverse of the augmentation `≅ K`
  -- applied to `1`.
  have hpt : Submodule.span K {(singularHomology₀Section (ModuleCat.of K K)
      (X := TopCat.of PUnit.{w + 1}) PUnit.unit (1 : K) :)} = ⊤ := by
    rw [IsIso.eq_inv_of_inv_hom_id (singularHomology₀Section_singularHomology₀ε _ _)]
    exact (ModuleCat.span_singleton_apply_eq_top_iff _).2 Ideal.span_singleton_one
  exact (ModuleCat.span_singleton_apply_eq_top_iff _).2
    ((ModuleCat.span_singleton_apply_eq_top_iff _).2 hpt)

/-- Every generator of `Hᵣ(F, F ∖ {0}; K) ≅ K` is a unit multiple of the generator. -/
private theorem exists_eq_smul_complZeroPairGenerator {x : ((TopPair.ofSubset (X := TopCat.of F)
    ({0}ᶜ : Set F)).singularHomology (ModuleCat.of K K) (finrank ℝ F) : ModuleCat.{w} K)}
    (hx : Submodule.span K {x} = ⊤) : ∃ a : Kˣ, x = (a : K) • complZeroPairGenerator K F := by
  let φ := (singularHomologyComplSingletonFinrankIso (ModuleCat.of K K)
    (OpenPartialHomeomorph.refl F) (mem_univ 0)).toLinearEquiv
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1
    ((span_complZeroPairGenerator K F).symm ▸ Submodule.mem_top :
      x ∈ Submodule.span K {complZeroPairGenerator K F})
  have ha := φ.span_singleton_eq_top_iff_isUnit.1 hx
  rw [map_smul, smul_eq_mul] at ha
  exact ⟨(isUnit_of_mul_isUnit_left ha).unit, rfl⟩

/-- Distinct scalars give distinct multiples of the generator. -/
private theorem smul_complZeroPairGenerator_injective :
    Function.Injective fun a : K ↦ a • complZeroPairGenerator K F := by
  let φ := (singularHomologyComplSingletonFinrankIso (ModuleCat.of K K)
    (OpenPartialHomeomorph.refl F) (mem_univ 0)).toLinearEquiv
  have hg := φ.span_singleton_eq_top_iff_isUnit.1 (span_complZeroPairGenerator K F)
  intro a a' h
  have h' := congrArg φ h
  simp only [map_smul, smul_eq_mul] at h'
  exact hg.mul_left_injective h'

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

end TauCeti

namespace Bundle.Trivialization

open TauCeti

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {E : B → Type w} [TopologicalSpace (TotalSpace F E)]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)]
  [FiberBundle F E] (e e' : Trivialization F (π F E)) [e.IsLinear ℝ] [e'.IsLinear ℝ]
  {C : Type*} [Category C] [HasCoproducts.{w} C] [Abelian C] {R : C}

/-- **Two linear trivializations read the homology of a fibre pair up to a sign.** The
identifications of `Hₙ(E_b, E_b ∖ {0})` with `Hₙ(F, F ∖ {0})` given by two linear trivializations
differ by the sign of the determinant of their coordinate change at `b`. -/
theorem singularHomologyMap_complZeroPairIso_hom_eq_sign_det_smul {b : B} (hb : b ∈ e.baseSet)
    (hb' : b ∈ e'.baseSet) (n : ℕ) :
    TopPair.singularHomologyMap (e'.continuousLinearEquivAt ℝ b hb').complZeroPairIso.hom R n =
      (SignType.sign (e.coordChangeL ℝ e' b : F →L[ℝ] F).det : ℤ) •
        TopPair.singularHomologyMap (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.hom R
          n := by
  have hf : Set.MapsTo (e.coordChangeL ℝ e' b : F →L[ℝ] F) ({0}ᶜ : Set F) {0}ᶜ :=
    (e.coordChangeL ℝ e' b).mapsTo_compl_zero
  -- The fibre of `e'` at `b` is the fibre of `e` followed by the coordinate change.
  have hcomp : (e'.continuousLinearEquivAt ℝ b hb').complZeroPairIso.hom =
      (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.hom ≫
        TopPair.ofSubsetMap (TopCat.ofHom ((e.coordChangeL ℝ e' b : F →L[ℝ] F) : C(F, F))) hf := by
    have h := (e.continuousLinearEquivAt_trans_coordChangeL ℝ e' hb hb').symm
    rw [h, ContinuousLinearEquiv.complZeroPairIso_trans, Iso.trans_hom]
    exact congrArg _ (ContinuousLinearEquiv.complZeroPairIso_hom _)
  rw [hcomp, TopPair.singularHomologyMap_comp, singularHomologyMap_continuousLinearMap_compl_zero,
    Preadditive.comp_zsmul, Category.comp_id]

end Bundle.Trivialization

namespace TauCeti

section Family

variable {K : Type w} [CommRing K] {B : Type w} [TopologicalSpace B] {F : Type w}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {E : B → Type w}
  [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)]
  [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]
  (c : ∀ b, ((TopPair.ofSubset (X := TopCat.of (E b)) ({0}ᶜ : Set (E b))).singularHomology
    (ModuleCat.of K K) (finrank ℝ F) : ModuleCat.{w} K))

/-- The fibre class of `c` over a point `x` of `W`: the image of `c x` in
`Hᵣ(E|_W, E₀|_W; K)`. -/
private def fiberClassOver (W : Set B) (x : W) :
    ((thomPairOver F E W).singularHomology (ModuleCat.of K K) (finrank ℝ F) : ModuleCat.{w} K) :=
  TopPair.singularHomologyMap (fiberThomPairOverMap F E x.2) (ModuleCat.of K K) (finrank ℝ F)
    (c x)

omit [FiniteDimensional ℝ F] [∀ b, Module ℝ (E b)] [VectorBundle ℝ F E] in
/-- Restricting from `W` to `W'` carries fibre classes to fibre classes. -/
private theorem singularHomologyMap_thomPairOverMap_fiberClassOver {W W' : Set B} (h : W ⊆ W')
    (x : W) :
    TopPair.singularHomologyMap (thomPairOverMap F E h) (ModuleCat.of K K) (finrank ℝ F)
        (fiberClassOver c W x) = fiberClassOver c W' (inclusion h x) := by
  rw [fiberClassOver, fiberClassOver, ← ConcreteCategory.comp_apply,
    ← TopPair.singularHomologyMap_comp, fiberThomPairOverMap_comp_thomPairOverMap]

omit [VectorBundle ℝ F E] in
/-- **The fibre classes over a trivializing set are multiples of the classes of the points**: a
linear trivialization `e` over `W` identifies `Hᵣ(E|_W, E₀|_W; K)` with
`Hᵣ(W × F, W × (F ∖ {0}); K) ≅ H₀(W; K)`, and this sends the fibre class over `x` to `a` times the
class of `x` when `e` reads `c x` as `a` times the generator. -/
private theorem singularHomologyMap_thomPairOverIso_fiberClassOver (e : Trivialization F (π F E))
    [e.IsLinear ℝ] {W : Set B} (hW : W ⊆ e.baseSet) (x : W) {a : K}
    (ha : TopPair.singularHomologyMap (e.continuousLinearEquivAt ℝ x (hW x.2)).complZeroPairIso.hom
      (ModuleCat.of K K) (finrank ℝ F) (c x) = a • complZeroPairGenerator K F) :
    TopPair.singularHomologyMap (e.thomPairOverIso ℝ hW).hom (ModuleCat.of K K) (finrank ℝ F)
        (fiberClassOver c W x) =
      (prodThomPairSingularHomologyIso (ModuleCat.of K K) W F 0 (finrank ℝ F)).inv
        (singularHomology₀Section (ModuleCat.of K K) (X := TopCat.of W) x a) := by
  rw [fiberClassOver, ← ConcreteCategory.comp_apply, ← TopPair.singularHomologyMap_comp,
    Bundle.Trivialization.fiberThomPairOverMap_comp_thomPairOverIso_hom ℝ e hW x.2,
    TopPair.singularHomologyMap_comp, ConcreteCategory.comp_apply, ha, map_smul, Subtype.coe_eta,
    singularHomologyMap_prodThomPairFiberMap_complZeroPairGenerator, ← map_smul, ← map_smul,
    smul_eq_mul, mul_one]

omit [VectorBundle ℝ F E] in
/-- The fibre classes over two points of `W`, joined by a path in `W` along which a linear
trivialization reads `c` as a single generator, agree. -/
private theorem fiberClassOver_eq_of_joinedIn (e : Trivialization F (π F E)) [e.IsLinear ℝ]
    {W : Set B} {v : ((TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularHomology
      (ModuleCat.of K K) (finrank ℝ F) : ModuleCat.{w} K)} (hv : Submodule.span K {v} = ⊤)
    {x y : W} (h : JoinedIn {z : W | ∃ hz : (z : B) ∈ e.baseSet, TopPair.singularHomologyMap
      (e.continuousLinearEquivAt ℝ z hz).complZeroPairIso.hom (ModuleCat.of K K) (finrank ℝ F)
        (c z) = v} x y) :
    fiberClassOver c W x = fiberClassOver c W y := by
  obtain ⟨a, rfl⟩ := exists_eq_smul_complZeroPairGenerator K F hv
  have hW : W ∩ e.baseSet ⊆ e.baseSet := inter_subset_right
  obtain ⟨hxe, hxv⟩ := h.source_mem
  obtain ⟨hye, hyv⟩ := h.target_mem
  let x' : ↥(W ∩ e.baseSet) := ⟨x, x.2, hxe⟩
  let y' : ↥(W ∩ e.baseSet) := ⟨y, y.2, hye⟩
  -- The two points are joined in `W ∩ e.baseSet`, so their classes in `H₀` agree.
  have hj : Joined x' y' :=
    h.joined_subtype.map (f := fun z : {z : W | ∃ hz : (z : B) ∈ e.baseSet,
      TopPair.singularHomologyMap (e.continuousLinearEquivAt ℝ z hz).complZeroPairIso.hom
        (ModuleCat.of K K) (finrank ℝ F) (c z) = (a : K) • complZeroPairGenerator K F} ↦
      (⟨z.1.1, z.1.2, z.2.1⟩ : ↥(W ∩ e.baseSet))) (by fun_prop)
  have hxy : fiberClassOver c (W ∩ e.baseSet) x' = fiberClassOver c (W ∩ e.baseSet) y' := by
    apply (ModuleCat.mono_iff_injective (TopPair.singularHomologyMap (e.thomPairOverIso ℝ hW).hom
      (ModuleCat.of K K) (finrank ℝ F))).1 inferInstance
    rw [singularHomologyMap_thomPairOverIso_fiberClassOver c e hW x' hxv,
      singularHomologyMap_thomPairOverIso_fiberClassOver c e hW y' hyv,
      singularHomology₀Section_eq_of_joined _ hj]
  have := congrArg (TopPair.singularHomologyMap (thomPairOverMap F E inter_subset_left)
    (ModuleCat.of K K) (finrank ℝ F)) hxy
  rwa [singularHomologyMap_thomPairOverMap_fiberClassOver,
    singularHomologyMap_thomPairOverMap_fiberClassOver] at this

variable {c} (hgen : ∀ b, Submodule.span K {c b} = ⊤)
  (hc : ∀ (e : Trivialization F (π F E)) [MemTrivializationAtlas e] {b : B} (hb : b ∈ e.baseSet),
    ∀ᶠ x in 𝓝 b, ∀ hx : x ∈ e.baseSet,
      TopPair.singularHomologyMap (e.continuousLinearEquivAt ℝ x hx).complZeroPairIso.hom
          (ModuleCat.of K K) (finrank ℝ F) (c x) =
        TopPair.singularHomologyMap (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.hom
          (ModuleCat.of K K) (finrank ℝ F) (c b))

include hgen hc in
/-- **The fibre classes are constant along paths.** -/
private theorem fiberClassOver_eq_of_path {W : Set B} {x y : W} (γ : Path x y) :
    fiberClassOver c W x = fiberClassOver c W y := by
  have : LocallyPathConnectedSpace unitInterval :=
    Convex.locallyPathConnectedSpace ℝ (convex_Icc (0 : ℝ) 1)
  have hlc : IsLocallyConstant fun t ↦ fiberClassOver c W (γ t) := by
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun t ↦ ?_
    let e := trivializationAt F E (γ t : B)
    have hb := mem_baseSet_trivializationAt F E (γ t : B)
    -- Near `t`, the path stays in the base set of `e`, which reads `c` there as `c (γ t)`.
    have hO : {s : unitInterval | ∃ hz : ((γ s : W) : B) ∈ e.baseSet,
        TopPair.singularHomologyMap (e.continuousLinearEquivAt ℝ _ hz).complZeroPairIso.hom
          (ModuleCat.of K K) (finrank ℝ F) (c (γ s)) =
        TopPair.singularHomologyMap (e.continuousLinearEquivAt ℝ _ hb).complZeroPairIso.hom
          (ModuleCat.of K K) (finrank ℝ F) (c (γ t))} ∈ 𝓝 t := by
      filter_upwards [(continuous_subtype_val.comp γ.continuous).continuousAt.preimage_mem_nhds
        ((hc e hb).and (e.open_baseSet.mem_nhds hb))] with s hs
      exact ⟨hs.2, hs.1 hs.2⟩
    filter_upwards [pathComponentIn_mem_nhds hO] with s hs
    refine (fiberClassOver_eq_of_joinedIn c e ((ModuleCat.span_singleton_apply_eq_top_iff
      (TopPair.singularHomologyMap (e.continuousLinearEquivAt ℝ _ hb).complZeroPairIso.hom
        (ModuleCat.of K K) (finrank ℝ F))).2 (hgen _))
      ((hs.map γ.continuous.continuousOn).mono ?_)).symm
    rintro _ ⟨u, hu, rfl⟩
    exact hu
  simpa using hlc.apply_eq_of_preconnectedSpace 0 1

/-- The map `H₀(W; K) ⟶ Hᵣ(E|_W, E₀|_W; K)` sending the class of a point to the fibre class over
it. -/
private def thomPairOverSingularHomologyFinrankInv (W : Set B) :
    ((singularHomologyFunctor (ModuleCat.{w} K) 0).obj (ModuleCat.of K K)).obj (TopCat.of W) ⟶
      (thomPairOver F E W).singularHomology (ModuleCat.of K K) (finrank ℝ F) :=
  singularHomology₀Desc (ModuleCat.of K K) (X := TopCat.of W)
    (fun x ↦ ModuleCat.ofHom (LinearMap.toSpanSingleton K _ (fiberClassOver c W x)))
    fun _ _ γ ↦ by rw [fiberClassOver_eq_of_path hgen hc γ]

variable {hgen hc}

@[reassoc]
private theorem singularHomology₀Section_thomPairOverSingularHomologyFinrankInv {W : Set B}
    (x : W) :
    singularHomology₀Section (ModuleCat.of K K) (X := TopCat.of W) x ≫
        thomPairOverSingularHomologyFinrankInv hgen hc W =
      ModuleCat.ofHom (LinearMap.toSpanSingleton K _ (fiberClassOver c W x)) := by
  rw [thomPairOverSingularHomologyFinrankInv]
  exact singularHomology₀Section_singularHomology₀Desc (X := TopCat.of W) _ _ _ x

/-- The maps over `W ⊆ W'` commute with the restrictions. -/
private theorem thomPairOverSingularHomologyFinrankInv_naturality {W W' : Set B} (h : W ⊆ W') :
    ((singularHomologyFunctor (ModuleCat.{w} K) 0).obj (ModuleCat.of K K)).map
        (TopCat.ofHom (ContinuousMap.inclusion h)) ≫
        thomPairOverSingularHomologyFinrankInv hgen hc W' =
      thomPairOverSingularHomologyFinrankInv hgen hc W ≫
        TopPair.singularHomologyMap (thomPairOverMap F E h) (ModuleCat.of K K) (finrank ℝ F) := by
  refine singularHomology₀_hom_ext _ fun x ↦ ?_
  rw [singularHomology₀Section_naturality_assoc,
    singularHomology₀Section_thomPairOverSingularHomologyFinrankInv,
    singularHomology₀Section_thomPairOverSingularHomologyFinrankInv_assoc,
    ModuleCat.ofHom_toSpanSingleton_comp, singularHomologyMap_thomPairOverMap_fiberClassOver]
  rw [ConcreteCategory.hom_ofHom, show ContinuousMap.inclusion h x = inclusion h x from
    Subtype.ext ((ContinuousMap.inclusion_apply_coe h x).trans (coe_inclusion h x).symm)]

/-- Over a subset of the base set of a trivialization of the atlas, the map is an isomorphism:
read through the trivialization and the isomorphism `Hᵣ(W × F, W × (F ∖ {0})) ≅ H₀(W)` of the
product bundle, it multiplies the class of each point by a locally constant unit. -/
private theorem isIso_thomPairOverSingularHomologyFinrankInv_of_subset
    (e : Trivialization F (π F E)) [MemTrivializationAtlas e] {W : Set B} (hW : W ⊆ e.baseSet) :
    IsIso (thomPairOverSingularHomologyFinrankInv hgen hc W) := by
  -- The unit by which `e` reads `c x` as a multiple of the generator.
  choose a ha using fun x : W ↦ exists_eq_smul_complZeroPairGenerator K F
    ((ModuleCat.span_singleton_apply_eq_top_iff
      (TopPair.singularHomologyMap (e.continuousLinearEquivAt ℝ x (hW x.2)).complZeroPairIso.hom
        (ModuleCat.of K K) (finrank ℝ F))).2 (hgen x))
  have hlc : IsLocallyConstant a := (IsLocallyConstant.iff_eventually_eq _).2 fun x ↦ by
    filter_upwards [continuous_subtype_val.continuousAt.eventually (hc e (hW x.2))] with y hy
    exact Units.ext (smul_complZeroPairGenerator_injective K F
      ((ha y).symm.trans ((hy (hW y.2)).trans (ha x))))
  let P := (prodThomPairSingularHomologyIso (ModuleCat.of K K) W F 0 (finrank ℝ F)).symm
  have hN : IsIso (thomPairOverSingularHomologyFinrankInv hgen hc W ≫
      TopPair.singularHomologyMap (e.thomPairOverIso ℝ hW).hom (ModuleCat.of K K) (finrank ℝ F) ≫
        P.inv) := by
    refine isIso_of_singularHomology₀Section_comp_eq _
      (fun x ↦ (LinearEquiv.smulOfUnit (a x)).toModuleIso) (fun x y γ ↦ ?_) fun x ↦ ?_
    · rw [show a x = a y by
        simpa using (hlc.comp_continuous γ.continuous).apply_eq_of_preconnectedSpace 0 1]
    · refine ModuleCat.hom_ext (LinearMap.ext_ring ?_)
      rw [singularHomology₀Section_thomPairOverSingularHomologyFinrankInv_assoc]
      simp [P, singularHomologyMap_thomPairOverIso_fiberClassOver c e hW x (ha x),
        LinearEquiv.smulOfUnit, Units.smul_def]
  have : IsIso (TopPair.singularHomologyMap (e.thomPairOverIso ℝ hW).hom (ModuleCat.of K K)
      (finrank ℝ F) ≫ P.inv) := inferInstance
  exact IsIso.of_isIso_comp_right _
    (TopPair.singularHomologyMap (e.thomPairOverIso ℝ hW).hom (ModuleCat.of K K) (finrank ℝ F) ≫
      P.inv)

private theorem isIso_thomPairOverSingularHomologyFinrankInv_empty :
    IsIso (thomPairOverSingularHomologyFinrankInv hgen hc ∅) :=
  isIso_of_source_target_iso_zero _
    (isZero_singularHomologyFunctor_zero_of_isEmpty _ _).isoZero
    (isZero_singularHomology_thomPairOver_empty _ _).isoZero

/-- Over `W ⊆ W'`, with the map over `W'` an isomorphism, the restriction from `W` to `W'` read
through the maps over `W` and `W'` is the map induced by the inclusion. -/
@[reassoc]
private theorem thomPairOverSingularHomologyFinrankInv_comp_singularHomologyMap_comp_inv
    {W W' : Set B} (h : W ⊆ W') [IsIso (thomPairOverSingularHomologyFinrankInv hgen hc W')] :
    thomPairOverSingularHomologyFinrankInv hgen hc W ≫
        TopPair.singularHomologyMap (thomPairOverMap F E h) (ModuleCat.of K K) (finrank ℝ F) ≫
          inv (thomPairOverSingularHomologyFinrankInv hgen hc W') =
      ((singularHomologyFunctor (ModuleCat.{w} K) 0).obj (ModuleCat.of K K)).map
        (TopCat.ofHom (ContinuousMap.inclusion h)) := by
  rw [← Category.assoc, ← thomPairOverSingularHomologyFinrankInv_naturality, Category.assoc,
    IsIso.hom_inv_id, Category.comp_id]

/-- In the Mayer–Vietoris step, a candidate inverse `Φ` of the map over `W'` is built which on the
classes over a subset `W` is the inverse of the map over `W` followed by the inclusion. Such a `Φ`
inverts the map over `W'` on the classes of points of `W`. -/
private theorem singularHomology₀Section_thomPairOverSingularHomologyFinrankInv_comp_of_comp_eq
    {W W' : Set B} (h : W ⊆ W') [IsIso (thomPairOverSingularHomologyFinrankInv hgen hc W)]
    {Φ : (thomPairOver F E W').singularHomology (ModuleCat.of K K) (finrank ℝ F) ⟶
      ((singularHomologyFunctor (ModuleCat.{w} K) 0).obj (ModuleCat.of K K)).obj (TopCat.of W')}
    (hΦ : TopPair.singularHomologyMap (thomPairOverMap F E h) (ModuleCat.of K K) (finrank ℝ F) ≫
      Φ = inv (thomPairOverSingularHomologyFinrankInv hgen hc W) ≫
        ((singularHomologyFunctor (ModuleCat.{w} K) 0).obj (ModuleCat.of K K)).map
          (TopCat.ofHom (ContinuousMap.inclusion h)))
    (x : W) :
    singularHomology₀Section (ModuleCat.of K K) (X := TopCat.of W')
          (TopCat.ofHom (ContinuousMap.inclusion h) x) ≫
        thomPairOverSingularHomologyFinrankInv hgen hc W' ≫ Φ =
      singularHomology₀Section (ModuleCat.of K K) (X := TopCat.of W')
        (TopCat.ofHom (ContinuousMap.inclusion h) x) := by
  rw [← singularHomology₀Section_naturality, Category.assoc,
    reassoc_of% (thomPairOverSingularHomologyFinrankInv_naturality h),
    hΦ, IsIso.hom_inv_id_assoc]

/-- Such a `Φ` also inverts the map over `W'` on the classes over `W`. -/
private theorem singularHomologyMap_thomPairOverMap_comp_comp_of_comp_eq
    {W W' : Set B} (h : W ⊆ W') [IsIso (thomPairOverSingularHomologyFinrankInv hgen hc W)]
    {Φ : (thomPairOver F E W').singularHomology (ModuleCat.of K K) (finrank ℝ F) ⟶
      ((singularHomologyFunctor (ModuleCat.{w} K) 0).obj (ModuleCat.of K K)).obj (TopCat.of W')}
    (hΦ : TopPair.singularHomologyMap (thomPairOverMap F E h) (ModuleCat.of K K) (finrank ℝ F) ≫
      Φ = inv (thomPairOverSingularHomologyFinrankInv hgen hc W) ≫
        ((singularHomologyFunctor (ModuleCat.{w} K) 0).obj (ModuleCat.of K K)).map
          (TopCat.ofHom (ContinuousMap.inclusion h))) :
    TopPair.singularHomologyMap (thomPairOverMap F E h) (ModuleCat.of K K) (finrank ℝ F) ≫ Φ ≫
        thomPairOverSingularHomologyFinrankInv hgen hc W' =
      TopPair.singularHomologyMap (thomPairOverMap F E h) (ModuleCat.of K K) (finrank ℝ F) := by
  rw [reassoc_of% hΦ, thomPairOverSingularHomologyFinrankInv_naturality, IsIso.inv_hom_id_assoc]

/-- **The Mayer–Vietoris step**: if the maps over the open sets `U` and `V` are isomorphisms, the
map over `U ∩ V` is surjective and the homology of the Thom pair over `U ∩ V` vanishes in degree
`r - 1`, the map over `U ∪ V` is an isomorphism. -/
private theorem isIso_thomPairOverSingularHomologyFinrankInv_union {U V : Set B} (hU : IsOpen U)
    (hV : IsOpen V) [IsIso (thomPairOverSingularHomologyFinrankInv hgen hc U)]
    [IsIso (thomPairOverSingularHomologyFinrankInv hgen hc V)]
    [Epi (thomPairOverSingularHomologyFinrankInv hgen hc (U ∩ V))]
    (hUV : ∀ m, m + 1 = finrank ℝ F →
      IsZero ((thomPairOver F E (U ∩ V)).singularHomology (ModuleCat.of K K) m)) :
    IsIso (thomPairOverSingularHomologyFinrankInv hgen hc (U ∪ V)) := by
  let ψ := thomPairOverSingularHomologyFinrankInv hgen hc
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
    (hWe : ∀ i ∈ s,
      ∃ (e : Trivialization F (π F E)) (_ : MemTrivializationAtlas e), W i ⊆ e.baseSet) :
    IsIso (thomPairOverSingularHomologyFinrankInv hgen hc (⋃ i ∈ s, W i)) := by
  classical
  induction s using Finset.induction_on generalizing W with
  | empty =>
    rw [show (⋃ i ∈ (∅ : Finset ι), W i) = ∅ by simp]
    exact isIso_thomPairOverSingularHomologyFinrankInv_empty
  | insert a s _ ih =>
    rw [Finset.set_biUnion_insert]
    obtain ⟨e, _, he⟩ := hWe a (Finset.mem_insert_self a s)
    have : IsIso (thomPairOverSingularHomologyFinrankInv hgen hc (W a)) :=
      isIso_thomPairOverSingularHomologyFinrankInv_of_subset e he
    have : IsIso (thomPairOverSingularHomologyFinrankInv hgen hc (⋃ i ∈ s, W i)) :=
      ih (fun i hi ↦ hWo i (Finset.mem_insert_of_mem hi))
        (fun i hi ↦ hWe i (Finset.mem_insert_of_mem hi))
    -- `W a ∩ ⋃ i ∈ s, W i` is the union of the trivializing open sets `W a ∩ W i`, `i ∈ s`.
    have : IsIso (thomPairOverSingularHomologyFinrankInv hgen hc (W a ∩ ⋃ i ∈ s, W i)) := by
      rw [inter_iUnion₂]
      refine ih (fun i hi ↦ (hWo a (Finset.mem_insert_self a s)).inter
        (hWo i (Finset.mem_insert_of_mem hi))) fun i hi ↦ ?_
      obtain ⟨e', he', hi'⟩ := hWe i (Finset.mem_insert_of_mem hi)
      exact ⟨e', he', inter_subset_right.trans hi'⟩
    exact isIso_thomPairOverSingularHomologyFinrankInv_union (hWo a (Finset.mem_insert_self a s))
      (isOpen_iUnion fun i ↦ isOpen_iUnion fun hi ↦ hWo i (Finset.mem_insert_of_mem hi))
      fun m hm ↦ e.isZero_singularHomology_thomPairOver (inter_subset_left.trans he) _ (by omega)

/-! ### The passage to the whole base -/

variable (hgen hc) in
/-- The map `H₀(B; K) ⟶ Hᵣ(E, E₀; K)` sending the class of a point to the fibre class over it. -/
private def thomPairSingularHomologyFinrankInv :
    ((singularHomologyFunctor (ModuleCat.{w} K) 0).obj (ModuleCat.of K K)).obj (TopCat.of B) ⟶
      (thomPair F E).singularHomology (ModuleCat.of K K) (finrank ℝ F) :=
  ((singularHomologyFunctor (ModuleCat.{w} K) 0).obj (ModuleCat.of K K)).map
      (TopCat.isoOfHomeo (Homeomorph.Set.univ B).symm).hom ≫
    thomPairOverSingularHomologyFinrankInv hgen hc univ ≫
      TopPair.singularHomologyMap (thomPairOverUnivIso F E).hom (ModuleCat.of K K) (finrank ℝ F)

private theorem singularHomology₀Section_thomPairSingularHomologyFinrankInv (b : B) :
    singularHomology₀Section (ModuleCat.of K K) (X := TopCat.of B) b ≫
        thomPairSingularHomologyFinrankInv hgen hc =
      ModuleCat.ofHom (LinearMap.toSpanSingleton K _ (TopPair.singularHomologyMap
        (fiberThomPairMap F E b) (ModuleCat.of K K) (finrank ℝ F) (c b))) := by
  rw [thomPairSingularHomologyFinrankInv, singularHomology₀Section_naturality_assoc,
    singularHomology₀Section_thomPairOverSingularHomologyFinrankInv_assoc,
    ModuleCat.ofHom_toSpanSingleton_comp, fiberClassOver, ← ConcreteCategory.comp_apply,
    ← TopPair.singularHomologyMap_comp]
  exact congrArg (fun f ↦ ModuleCat.ofHom (LinearMap.toSpanSingleton K _
    (TopPair.singularHomologyMap f (ModuleCat.of K K) (finrank ℝ F) (c b))))
    (fiberThomPairOverMap_comp_thomPairOverUnivIso_hom F E b)

/-- On a finite union of the chosen trivializing sets, the map over the base restricts to the
map over the union. -/
private theorem thomPairSingularHomologyFinrankInv_restrict (s : Finset B) :
    ((singularHomologyFunctor (ModuleCat.{w} K) 0).obj (ModuleCat.of K K)).map
        (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ :
          TopCat.of ↥(⋃ b ∈ s, (trivializationAt F E b).baseSet) ⟶ TopCat.of B) ≫
        thomPairSingularHomologyFinrankInv hgen hc =
      thomPairOverSingularHomologyFinrankInv hgen hc (⋃ b ∈ s, (trivializationAt F E b).baseSet) ≫
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
    (s : Finset B) : IsIso (thomPairOverSingularHomologyFinrankInv hgen hc
      (⋃ b ∈ s, (trivializationAt F E b).baseSet)) :=
  isIso_thomPairOverSingularHomologyFinrankInv_biUnion s
    (fun b _ ↦ (trivializationAt F E b).open_baseSet)
    fun b _ ↦ ⟨trivializationAt F E b, inferInstance, subset_rfl⟩

omit [FiniteDimensional ℝ F] [∀ b, Module ℝ (E b)] [VectorBundle ℝ F E] in
variable (K) in
/-- The objects of the diagram of Thom pairs are the Thom pairs over the finite unions only up to
the equations `thomPairFiniteTrivializingUnionDiagram_obj`. -/
private theorem singularHomology_thomPairOver_finiteTrivializingUnion_eq (s : Finset B) :
    (thomPairOver F E (⋃ b ∈ s, (trivializationAt F E b).baseSet)).singularHomology
        (ModuleCat.of K K) (finrank ℝ F) =
      (TopPair.singularHomologyFunctor (ModuleCat.of K K) (finrank ℝ F)).obj
        ((thomPairFiniteTrivializingUnionDiagram (F := F) (E := E)).obj s) := by
  rw [thomPairFiniteTrivializingUnionDiagram_obj, TopPair.singularHomologyFunctor_obj]

omit [FiniteDimensional ℝ F] [∀ b, Module ℝ (E b)] [VectorBundle ℝ F E] in
variable (K) in
/-- The Thom pair is the cocone point of the diagram of Thom pairs only up to the equation
`thomPairFiniteTrivializingUnionCocone_pt`. -/
private theorem singularHomology_thomPair_eq :
    (thomPair F E).singularHomology (ModuleCat.of K K) (finrank ℝ F) =
      (TopPair.singularHomologyFunctor (ModuleCat.of K K) (finrank ℝ F)).obj
        (thomPairFiniteTrivializingUnionCocone (F := F) (E := E)).pt := by
  rw [thomPairFiniteTrivializingUnionCocone_pt, TopPair.singularHomologyFunctor_obj]

variable (hgen hc) in
/-- The maps over the finite unions of the chosen trivializing sets, as a natural isomorphism
between the homologies of the bases and of the Thom pairs. -/
private def thomPairFiniteTrivializingUnionSingularHomologyFinrankIso :
    baseFiniteTrivializingUnionDiagram F E ⋙
        (singularHomologyFunctor (ModuleCat.{w} K) 0).obj (ModuleCat.of K K) ≅
      thomPairFiniteTrivializingUnionDiagram (F := F) (E := E) ⋙
        TopPair.singularHomologyFunctor (ModuleCat.of K K) (finrank ℝ F) :=
  NatIso.ofComponents (fun s ↦ @asIso _ _ _ _ (thomPairOverSingularHomologyFinrankInv hgen hc
      (⋃ b ∈ s, (trivializationAt F E b).baseSet))
        (isIso_thomPairOverSingularHomologyFinrankInv_finiteTrivializingUnion s) ≪≫
      eqToIso (singularHomology_thomPairOver_finiteTrivializingUnion_eq K s))
    fun {s t} f ↦ by
      have := isIso_thomPairOverSingularHomologyFinrankInv_finiteTrivializingUnion
        (hgen := hgen) (hc := hc) s
      have := isIso_thomPairOverSingularHomologyFinrankInv_finiteTrivializingUnion
        (hgen := hgen) (hc := hc) t
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
        thomPairSingularHomologyFinrankInv hgen hc ≫ eqToHom (singularHomology_thomPair_eq K) =
      thomPairOverSingularHomologyFinrankInv hgen hc (⋃ b ∈ s, (trivializationAt F E b).baseSet) ≫
        eqToHom (singularHomology_thomPairOver_finiteTrivializingUnion_eq K s) ≫
          (TopPair.singularHomologyFunctor (ModuleCat.of K K) (finrank ℝ F)).map
            ((thomPairFiniteTrivializingUnionCocone (F := F) (E := E)).ι.app s) := by
  rw [reassoc_of% (thomPairSingularHomologyFinrankInv_restrict (hgen := hgen) (hc := hc) s)]
  simp only [thomPairFiniteTrivializingUnionCocone_ι_app, TopPair.singularHomologyFunctor_map,
    Category.assoc, TopPair.singularHomologyMap_comp, TopPair.singularHomologyMap_eqToHom,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, eqToHom_trans]

/-- **The passage to the whole base**: the homologies of the base and of the Thom pair are the
filtered colimits of their homologies over the finite unions of the chosen trivializing sets, and
over these the map is an isomorphism. -/
private theorem isIso_thomPairSingularHomologyFinrankInv :
    IsIso (thomPairSingularHomologyFinrankInv hgen hc) := by
  let P₁ := isColimitSingularHomologyBaseFiniteTrivializingUnion K F E
  let P₂ := isColimitMapCoconeSingularHomologyThomPairFiniteTrivializingUnion (F := F) (E := E)
    (ModuleCat.of K K) (finrank ℝ F)
  let α := thomPairFiniteTrivializingUnionSingularHomologyFinrankIso hgen hc
  have h : thomPairSingularHomologyFinrankInv hgen hc ≫ eqToHom (singularHomology_thomPair_eq K) =
      (P₁.coconePointsIsoOfNatIso P₂ α).hom :=
    P₁.hom_ext fun s ↦ (singularHomologyMap_ι_thomPairSingularHomologyFinrankInv s).trans
      (P₁.comp_coconePointsIsoOfNatIso_hom P₂ α s).symm
  have : IsIso (thomPairSingularHomologyFinrankInv hgen hc ≫
      eqToHom (singularHomology_thomPair_eq K)) := by
    rw [h]
    exact (P₁.coconePointsIsoOfNatIso P₂ α).isIso_hom
  exact IsIso.of_isIso_comp_right _ (eqToHom (singularHomology_thomPair_eq K))


variable (hgen hc) in
/-- **The homology of the Thom pair in the rank degree**: for a real vector bundle `E → B` of
rank `r`, with Thom pair `(E, E₀)`, a commutative ring `K` and a family `c` of generators of the
fibre groups `Hᵣ(E_b, E_b ∖ {0}; K)` that is locally constant read in the trivializations of the
atlas, `Hᵣ(E, E₀; K) ≅ H₀(B; K)`. It sends the fibre class over `b`, the image of `c b`, to the
class of `b` (`TauCeti.thomPairSingularHomologyFinrankIsoOfGenerators_hom_apply`). The base is
arbitrary. -/
def thomPairSingularHomologyFinrankIsoOfGenerators :
    (thomPair F E).singularHomology (ModuleCat.of K K) (finrank ℝ F) ≅
      ((singularHomologyFunctor (ModuleCat.{w} K) 0).obj (ModuleCat.of K K)).obj (TopCat.of B) :=
  have := isIso_thomPairSingularHomologyFinrankInv (hgen := hgen) (hc := hc)
  (asIso (thomPairSingularHomologyFinrankInv hgen hc)).symm

/-- **The isomorphism `Hᵣ(E, E₀; K) ≅ H₀(B; K)` sends the fibre class of `c` over `b` to the class
of `b`.** -/
@[simp]
theorem thomPairSingularHomologyFinrankIsoOfGenerators_hom_apply (b : B) :
    (thomPairSingularHomologyFinrankIsoOfGenerators hgen hc).hom
        (TopPair.singularHomologyMap (fiberThomPairMap F E b) (ModuleCat.of K K) (finrank ℝ F)
          (c b)) =
      singularHomology₀Section (ModuleCat.of K K) (X := TopCat.of B) b 1 := by
  have := isIso_thomPairSingularHomologyFinrankInv (hgen := hgen) (hc := hc)
  have h := congrArg (fun f ↦ f (1 : K))
    (singularHomology₀Section_thomPairSingularHomologyFinrankInv (hgen := hgen) (hc := hc) b)
  simp only [ModuleCat.hom_ofHom, LinearMap.toSpanSingleton_apply, one_smul,
    ConcreteCategory.comp_apply] at h
  rw [← h, thomPairSingularHomologyFinrankIsoOfGenerators, Iso.symm_hom, asIso_inv,
    ← ConcreteCategory.comp_apply, IsIso.hom_inv_id, ConcreteCategory.id_apply]

end Family

section SubsingletonUnits

variable (K : Type w) [CommRing K] {B : Type w} [TopologicalSpace B]
  (F : Type w) [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] (E : B → Type w)
  [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)]
  [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]

/-- The generator of `Hᵣ(E_b, E_b ∖ {0}; K) ≅ K`, read through the trivialization at `b`. -/
private def fiberGenerator (b : B) :
    ((TopPair.ofSubset (X := TopCat.of (E b)) ({0}ᶜ : Set (E b))).singularHomology
      (ModuleCat.of K K) (finrank ℝ F) : ModuleCat.{w} K) :=
  TopPair.singularHomologyMap ((trivializationAt F E b).continuousLinearEquivAt ℝ b
      (mem_baseSet_trivializationAt F E b)).complZeroPairIso.inv (ModuleCat.of K K) (finrank ℝ F)
    (complZeroPairGenerator K F)

private theorem span_fiberGenerator (b : B) : Submodule.span K {fiberGenerator K F E b} = ⊤ :=
  (ModuleCat.span_singleton_apply_eq_top_iff _).2 (span_complZeroPairGenerator K F)

variable {K F E} [Subsingleton Kˣ]

/-- Every generator of `Hᵣ(E_b, E_b ∖ {0}; K)` is the fibre generator. -/
private theorem eq_fiberGenerator {b : B} {x : ((TopPair.ofSubset (X := TopCat.of (E b))
    ({0}ᶜ : Set (E b))).singularHomology (ModuleCat.of K K) (finrank ℝ F) : ModuleCat.{w} K)}
    (hx : Submodule.span K {x} = ⊤) : x = fiberGenerator K F E b := by
  let L := (trivializationAt F E b).continuousLinearEquivAt ℝ b (mem_baseSet_trivializationAt F E b)
  apply (ModuleCat.mono_iff_injective (TopPair.singularHomologyMap L.complZeroPairIso.hom
    (ModuleCat.of K K) (finrank ℝ F))).1 inferInstance
  rw [eq_complZeroPairGenerator K F ((ModuleCat.span_singleton_apply_eq_top_iff _).2 hx),
    eq_complZeroPairGenerator K F
      ((ModuleCat.span_singleton_apply_eq_top_iff _).2 (span_fiberGenerator K F E b))]

/-- A linear trivialization reads every fibre generator as the generator of
`Hᵣ(F, F ∖ {0}; K)`. -/
private theorem singularHomologyMap_complZeroPairIso_fiberGenerator
    (e : Trivialization F (π F E)) [e.IsLinear ℝ] {b : B} (hb : b ∈ e.baseSet) :
    TopPair.singularHomologyMap (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.hom
      (ModuleCat.of K K) (finrank ℝ F) (fiberGenerator K F E b) = complZeroPairGenerator K F :=
  eq_complZeroPairGenerator K F
    ((ModuleCat.span_singleton_apply_eq_top_iff _).2 (span_fiberGenerator K F E b))

variable (K F E) in
/-- **The homology of the Thom pair in the rank degree, without orientation**: for a real vector
bundle `E → B` of rank `r`, with Thom pair `(E, E₀)`, and a commutative ring `K` whose only unit is
`1`, such as `ZMod 2`, `Hᵣ(E, E₀; K) ≅ H₀(B; K)`. It sends the fibre class over `b` to the class of
`b` (`TauCeti.thomPairSingularHomologyFinrankIso_hom_apply`). The base is arbitrary and the bundle
need not be orientable. -/
def thomPairSingularHomologyFinrankIso :
    (thomPair F E).singularHomology (ModuleCat.of K K) (finrank ℝ F) ≅
      ((singularHomologyFunctor (ModuleCat.{w} K) 0).obj (ModuleCat.of K K)).obj (TopCat.of B) :=
  thomPairSingularHomologyFinrankIsoOfGenerators (span_fiberGenerator K F E) fun e _ b hb ↦
    Eventually.of_forall fun x hx ↦ by
      rw [singularHomologyMap_complZeroPairIso_fiberGenerator,
        singularHomologyMap_complZeroPairIso_fiberGenerator]

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
  exact thomPairSingularHomologyFinrankIsoOfGenerators_hom_apply b

end SubsingletonUnits

namespace VectorBundleOrientation

section Oriented

variable {K : Type w} [CommRing K] {B : Type w} [TopologicalSpace B] {F : Type w}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {E : B → Type w}
  [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)]
  [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E] {ι : Type*} [Fintype ι]
  (o : VectorBundleOrientation F E ι) (hι : Fintype.card ι = finrank ℝ F) (ω : Orientation ℝ F ι)
  (g : ((TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularHomology (ModuleCat.of K K)
    (finrank ℝ F) : ModuleCat.{w} K))

open scoped Classical in
/-- The class of the fibre pair over `b` read off from `g` along the trivialization at `b`, with
the sign `+1` if that trivialization carries the orientation `o b` to `ω` and `-1` otherwise. -/
private def orientedFiberGenerator (b : B) :
    ((TopPair.ofSubset (X := TopCat.of (E b)) ({0}ᶜ : Set (E b))).singularHomology
      (ModuleCat.of K K) (finrank ℝ F) : ModuleCat.{w} K) :=
  if (trivializationAt F E b).mapOrientation ι (mem_baseSet_trivializationAt F E b) (o b) = ω then
    TopPair.singularHomologyMap ((trivializationAt F E b).continuousLinearEquivAt ℝ b
      (mem_baseSet_trivializationAt F E b)).complZeroPairIso.inv (ModuleCat.of K K) (finrank ℝ F) g
  else -TopPair.singularHomologyMap ((trivializationAt F E b).continuousLinearEquivAt ℝ b
      (mem_baseSet_trivializationAt F E b)).complZeroPairIso.inv (ModuleCat.of K K) (finrank ℝ F) g

omit [FiniteDimensional ℝ F] [VectorBundle ℝ F E] in
/-- A linear trivialization reads the class it pulls back from a class `y` of `Hᵣ(F, F ∖ {0})` as
`y`: the form of `Iso.inv_hom_id_apply` for `TopPair.singularHomologyMapIso` used to rewrite. -/
private theorem singularHomologyMap_complZeroPairIso_hom_inv (e : Trivialization F (π F E))
    [e.IsLinear ℝ] {b : B} (hb : b ∈ e.baseSet)
    (y : ((TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularHomology (ModuleCat.of K K)
      (finrank ℝ F) : ModuleCat.{w} K)) :
    TopPair.singularHomologyMap (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.hom
        (ModuleCat.of K K) (finrank ℝ F)
        (TopPair.singularHomologyMap (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.inv
          (ModuleCat.of K K) (finrank ℝ F) y) = y :=
  (TopPair.singularHomologyMapIso (ModuleCat.of K K)
    (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso (finrank ℝ F)).inv_hom_id_apply y

open scoped Classical in
include hι in
omit [VectorBundle ℝ F E] in
/-- A linear trivialization `e` reads the class pulled back from `g` along a linear trivialization
`e₀` as `g` if the two read an orientation `x` of the fibre as the same orientation of `F`, and as
`-g` otherwise. -/
private theorem singularHomologyMap_complZeroPairIso_hom_inv_eq_ite
    (e₀ e : Trivialization F (π F E)) [e₀.IsLinear ℝ] [e.IsLinear ℝ] {b : B}
    (hb₀ : b ∈ e₀.baseSet) (hb : b ∈ e.baseSet) (x : Orientation ℝ (E b) ι) :
    TopPair.singularHomologyMap (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.hom
        (ModuleCat.of K K) (finrank ℝ F)
        (TopPair.singularHomologyMap (e₀.continuousLinearEquivAt ℝ b hb₀).complZeroPairIso.inv
          (ModuleCat.of K K) (finrank ℝ F) g) =
      if e.mapOrientation ι hb x = e₀.mapOrientation ι hb₀ x then g else -g := by
  rw [e₀.singularHomologyMap_complZeroPairIso_hom_eq_sign_det_smul e hb₀ hb]
  have hmap := e₀.mapOrientation_eq_map_coordChangeL e hb₀ hb x
  rcases Orientation.eq_or_eq_neg (e.mapOrientation ι hb x) (e₀.mapOrientation ι hb₀ x) hι
    with h | h
  · have hd : 0 < (e₀.coordChangeL ℝ e b : F →L[ℝ] F).det :=
      (Orientation.map_eq_iff_det_pos _ _ hι).1 (hmap.symm.trans h)
    simp [h, sign_pos hd, singularHomologyMap_complZeroPairIso_hom_inv]
  · have hd : (e₀.coordChangeL ℝ e b : F →L[ℝ] F).det < 0 :=
      (Orientation.map_eq_neg_iff_det_neg _ _ hι).1 (hmap.symm.trans h)
    simp [h, sign_neg hd, (Module.Ray.ne_neg_self (e₀.mapOrientation ι hb₀ x)).symm,
      singularHomologyMap_complZeroPairIso_hom_inv]

open scoped Classical in
include hι in
/-- **A linear trivialization reads the oriented fibre generator as `±g`**: as `g` if it carries
the orientation of the fibre to `ω`, and as `-g` otherwise. -/
private theorem singularHomologyMap_complZeroPairIso_hom_orientedFiberGenerator
    (e : Trivialization F (π F E)) [e.IsLinear ℝ] {b : B} (hb : b ∈ e.baseSet) :
    TopPair.singularHomologyMap (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.hom
        (ModuleCat.of K K) (finrank ℝ F) (orientedFiberGenerator o ω g b) =
      if e.mapOrientation ι hb (o b) = ω then g else -g := by
  have hread := singularHomologyMap_complZeroPairIso_hom_inv_eq_ite hι g _ e
    (mem_baseSet_trivializationAt F E b) hb (o b)
  have hne : (-ω : Orientation ℝ F ι) ≠ ω := (Module.Ray.ne_neg_self ω).symm
  -- The trivialization at `b` and `e` each read `o b` as `±ω`.
  rw [orientedFiberGenerator]
  rcases Orientation.eq_or_eq_neg ((trivializationAt F E b).mapOrientation ι
      (mem_baseSet_trivializationAt F E b) (o b)) ω hι with h₀ | h₀ <;>
    rcases Orientation.eq_or_eq_neg (e.mapOrientation ι hb (o b)) ω hι with h | h <;>
    simp [hread, h₀, h, hne, hne.symm]

include hι in
private theorem span_orientedFiberGenerator (hg : Submodule.span K {g} = ⊤) (b : B) :
    Submodule.span K {orientedFiberGenerator o ω g b} = ⊤ := by
  classical
  rw [← ModuleCat.span_singleton_apply_eq_top_iff
    (TopPair.singularHomologyMap ((trivializationAt F E b).continuousLinearEquivAt ℝ b
      (mem_baseSet_trivializationAt F E b)).complZeroPairIso.hom (ModuleCat.of K K) (finrank ℝ F)),
    singularHomologyMap_complZeroPairIso_hom_orientedFiberGenerator o hι]
  split_ifs
  · exact hg
  · rwa [← Set.neg_singleton, Submodule.span_neg]

/-- **The homology of the Thom pair of an oriented bundle in the rank degree**: for a real vector
bundle `E → B` of rank `r` with an orientation `o`, an orientation `ω` of the model fibre `F` and a
generator `g` of `Hᵣ(F, F ∖ {0}; K)`, over any commutative ring `K`, `Hᵣ(E, E₀; K) ≅ H₀(B; K)`. It
sends the fibre class over `b` that a linear trivialization carrying `o b` to `ω` reads as `g`
to the class of `b`
(`thomPairSingularHomologyFinrankIsoOfModel_hom_apply_of_mapOrientation_eq`),
and the one read as `g` along a trivialization carrying `o b` to `-ω` to the negative of that
class. The base is arbitrary. -/
def thomPairSingularHomologyFinrankIsoOfModel (hg : Submodule.span K {g} = ⊤) :
    (thomPair F E).singularHomology (ModuleCat.of K K) (finrank ℝ F) ≅
      ((singularHomologyFunctor (ModuleCat.{w} K) 0).obj (ModuleCat.of K K)).obj (TopCat.of B) :=
  thomPairSingularHomologyFinrankIsoOfGenerators (span_orientedFiberGenerator o hι ω g hg)
    fun e _ b hb ↦ by
      filter_upwards [o.eventually_mapOrientation_eq hι e hb] with x hx hx'
      rw [singularHomologyMap_complZeroPairIso_hom_orientedFiberGenerator o hι,
        singularHomologyMap_complZeroPairIso_hom_orientedFiberGenerator o hι, hx hx']

variable {o hι ω g}

/-- Over a point where a linear trivialization `e` reads the orientation as `ω`, the isomorphism
`thomPairSingularHomologyFinrankIsoOfModel o hι ω g hg` sends the fibre class pulled back from `g`
along `e` to the class of the point. -/
theorem thomPairSingularHomologyFinrankIsoOfModel_hom_apply_of_mapOrientation_eq
    (hg : Submodule.span K {g} = ⊤) (e : Trivialization F (π F E)) [e.IsLinear ℝ] {b : B}
    (hb : b ∈ e.baseSet) (h : e.mapOrientation ι hb (o b) = ω) :
    (o.thomPairSingularHomologyFinrankIsoOfModel hι ω g hg).hom
        (TopPair.singularHomologyMap (fiberThomPairMap F E b) (ModuleCat.of K K) (finrank ℝ F)
          (TopPair.singularHomologyMap (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.inv
            (ModuleCat.of K K) (finrank ℝ F) g)) =
      singularHomology₀Section (ModuleCat.of K K) (X := TopCat.of B) b 1 := by
  have hc : TopPair.singularHomologyMap (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.inv
      (ModuleCat.of K K) (finrank ℝ F) g = orientedFiberGenerator o ω g b := by
    apply (ModuleCat.mono_iff_injective (TopPair.singularHomologyMap
      (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.hom (ModuleCat.of K K)
        (finrank ℝ F))).1 inferInstance
    rw [singularHomologyMap_complZeroPairIso_hom_inv,
      singularHomologyMap_complZeroPairIso_hom_orientedFiberGenerator o hι, h]
    simp
  rw [hc]
  exact thomPairSingularHomologyFinrankIsoOfGenerators_hom_apply b

/-- Over a point where a linear trivialization `e` reads the orientation as `-ω`, the isomorphism
`thomPairSingularHomologyFinrankIsoOfModel o hι ω g hg` sends the fibre class pulled back from `g`
along `e` to the negative of the class of the point. -/
theorem thomPairSingularHomologyFinrankIsoOfModel_hom_apply_of_mapOrientation_eq_neg
    (hg : Submodule.span K {g} = ⊤) (e : Trivialization F (π F E)) [e.IsLinear ℝ] {b : B}
    (hb : b ∈ e.baseSet) (h : e.mapOrientation ι hb (o b) = -ω) :
    (o.thomPairSingularHomologyFinrankIsoOfModel hι ω g hg).hom
        (TopPair.singularHomologyMap (fiberThomPairMap F E b) (ModuleCat.of K K) (finrank ℝ F)
          (TopPair.singularHomologyMap (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.inv
            (ModuleCat.of K K) (finrank ℝ F) g)) =
      -singularHomology₀Section (ModuleCat.of K K) (X := TopCat.of B) b 1 := by
  have hc : TopPair.singularHomologyMap (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.inv
      (ModuleCat.of K K) (finrank ℝ F) g = -orientedFiberGenerator o ω g b := by
    apply (ModuleCat.mono_iff_injective (TopPair.singularHomologyMap
      (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.hom (ModuleCat.of K K)
        (finrank ℝ F))).1 inferInstance
    rw [singularHomologyMap_complZeroPairIso_hom_inv, map_neg,
      singularHomologyMap_complZeroPairIso_hom_orientedFiberGenerator o hι, h]
    simp [(Module.Ray.ne_neg_self ω).symm]
  rw [hc, map_neg, map_neg]
  exact congrArg Neg.neg (thomPairSingularHomologyFinrankIsoOfGenerators_hom_apply b)

end Oriented

end VectorBundleOrientation

end TauCeti
