/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.MayerVietoris.DirectedUnion
public import TauCeti.AlgebraicTopology.Singular.Reduced
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Linear
public import TauCeti.Topology.VectorBundle.Orientation.Basic
import TauCeti.Algebra.Category.ModuleCat.SpanSingleton
import TauCeti.AlgebraicTopology.Singular.LocalHomology.Basic

/-!
# The homology of the Thom pair in the rank degree

Let `E → B` be a real vector bundle of rank `r` over an arbitrary base, with Thom pair `(E, E₀)`,
and let `K` be a commutative ring. The relative homology `Hₙ(E, E₀; K)` vanishes for `n < r`
(`TauCeti.isZero_singularHomology_thomPair`). This file computes the first group that does not
vanish,

`Hᵣ(E, E₀; K) ≅ H₀(B; K)`,

in two cases.

* When `1` is the only unit of `K`, such as for `ZMod 2`, for every bundle
  (`TauCeti.thomPairSingularHomologyFinrankIso`). The isomorphism sends the class of the fibre over
  a point `b`, the image of a generator of `Hᵣ(E_b, E_b ∖ {0}; K) ≅ K` under the inclusion of the
  fibre pair, to the class of the point `b`
  (`TauCeti.thomPairSingularHomologyFinrankIso_hom_apply`).
  No orientation is needed: the module `Hᵣ(E_b, E_b ∖ {0}; K) ≅ K` has a single generator, so the
  fibre classes do not depend on any choice.
* For every `K`, integral coefficients included, when the bundle is oriented
  (`TauCeti.VectorBundleOrientation.thomPairSingularHomologyFinrankIso`). Here the generator of each
  fibre pair is chosen by the orientation: fix an orientation `ω` of the model fibre `F` and a
  generator `z` of `Hᵣ(F, F ∖ {0}; K)`. The isomorphism sends the class of the fibre over `b` of the
  pull-back of `z` along a linear trivialization reading the orientation of `E_b` as `ω` to the
  class of `b`, and that of `z` along one reading it as `-ω` to the negative of the class of `b`
  (`VectorBundleOrientation.thomPairSingularHomologyFinrankIso_hom_apply_of_mapOrientation_eq` and
  its `_neg` counterpart).

This is the bottom degree of the Thom isomorphism `Hₙ₊ᵣ(E, E₀; K) ≅ Hₙ(B; K)` in homology. Neither
case covers a bundle that is not orientable with coefficients in which `-1 ≠ 1`, such as `ℤ`: there
`Hᵣ(E, E₀; K)` is the homology of `B` twisted by the orientation system of `E`, which can differ
from `H₀(B; K)` (for the Möbius line over the circle and `K = ℤ` it is `ℤ/2`).

Two linear trivializations at `b` identify `Hᵣ(E_b, E_b ∖ {0})` with `Hᵣ(F, F ∖ {0})` up to the sign
of the determinant of their coordinate change
(`Bundle.Trivialization.singularHomologyMap_complZeroPairIso_hom_eq_sign_det_smul`), so they agree
exactly when they read an orientation of `E_b` as the same orientation of `F`
(`Bundle.Trivialization.singularHomologyMap_complZeroPairIso_hom_eq_of_mapOrientation_eq`).

## The proof

Both cases are instances of one argument, for a family of generators `g b` of the fibre pairs which
every preferred trivialization reads as `z` or `-z`, locally constantly in `b`. The inverse map
`H₀(B; K) ⟶ Hᵣ(E, E₀; K)` is defined on the classes of points, which generate `H₀(B; K)`: it sends
the class of `b` to the fibre class of `g b`. This is well defined because the fibre classes are
constant along paths in the base. Over a subset `W` of the base set of a linear trivialization
reading every `g b`, `b ∈ W`, as one generator, the trivialization identifies the Thom pair
`(E|_W, E₀|_W)` with the Thom pair of the product bundle `W × F`, whose homology in degree `r` is
`H₀(W; K)` (`TauCeti.prodThomPairSingularHomologyIso`), and this identification sends the fibre
class over a point to a fixed unit multiple of the class of the point; so the fibre classes over two
points joined by a path in `W` agree, and the map is an isomorphism over `W`. The Mayer–Vietoris
sequence of the Thom pairs over two open sets
(`TauCeti.singularHomology_thomPairOver_mayerVietoris_exact`) ends in degree `r`, since the homology
vanishes below the rank, so the map is an isomorphism over a finite union of such open sets by
induction on their number. Each base set of a preferred trivialization is the union of the two
open sets where it reads `g` as `z` and as `-z`. Singular homology has compact supports, so the
homology of the base and of the Thom pair are the filtered colimits of their homology over the
finite unions of these base sets, and the map is an isomorphism over the whole base.

## Main results

* `Bundle.Trivialization.singularHomologyMap_complZeroPairIso_hom_eq_sign_det_smul`: two linear
  trivializations identify the local homology of a fibre with that of the model fibre up to the
  sign of the determinant of their coordinate change.
* `TauCeti.thomPairSingularHomologyFinrankIso`: `Hᵣ(E, E₀; K) ≅ H₀(B; K)` for `r` the rank and `K`
  a commutative ring whose only unit is `1`.
* `TauCeti.thomPairSingularHomologyFinrankIso_hom_apply`: it sends the fibre class over `b` to the
  class of `b`.
* `TauCeti.VectorBundleOrientation.thomPairSingularHomologyFinrankIso`: `Hᵣ(E, E₀; K) ≅ H₀(B; K)`
  for an oriented bundle and any commutative ring `K`, normalized by an orientation `ω` and a
  generator `z` of the model fibre.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10, Lemma 10.3 and the proof of Theorem 10.4 (the induction over finite unions
  of trivializing open sets and the passage to a directed union).
* A. Hatcher, *Algebraic Topology*, Section 4.D, Theorem 4D.10 and its proof, which also covers
  `ℤ/2` coefficients for bundles without an orientation.
-/

public noncomputable section

open Bundle CategoryTheory Limits Set Module AlgebraicTopology Topology Filter

universe w

namespace Bundle.Trivialization

open TauCeti

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {E : B → Type w} [TopologicalSpace (TotalSpace F E)]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)]
  [FiberBundle F E] (e e' : Trivialization F (π F E)) [e.IsLinear ℝ] [e'.IsLinear ℝ] {b : B}
  (hb : b ∈ e.baseSet) (hb' : b ∈ e'.baseSet)
  {A : Type*} [Category A] [Abelian A] [HasCoproducts.{w} A] (R : A)

/-- **Fibre classes read in two trivializations differ by the sign of the coordinate change**: for
linear trivializations `e` and `e'` whose base sets contain `b`, the identification of
`Hₙ(E_b, E_b ∖ {0})` with `Hₙ(F, F ∖ {0})` given by `e'` is that given by `e` multiplied by the sign
of the determinant of the coordinate change from `e` to `e'` at `b`. -/
theorem singularHomologyMap_complZeroPairIso_hom_eq_sign_det_smul (n : ℕ) :
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

variable {ι : Type*} [Fintype ι] (hι : Fintype.card ι = finrank ℝ F)
  {o : Orientation ℝ (E b) ι}

include hι in
/-- Two linear trivializations reading an orientation of the fibre over `b` as the same
orientation of the model fibre identify `Hₙ(E_b, E_b ∖ {0})` with `Hₙ(F, F ∖ {0})` in the same
way. -/
theorem singularHomologyMap_complZeroPairIso_hom_eq_of_mapOrientation_eq
    (h : e'.mapOrientation ι hb' o = e.mapOrientation ι hb o) (n : ℕ) :
    TopPair.singularHomologyMap (e'.continuousLinearEquivAt ℝ b hb').complZeroPairIso.hom R n =
      TopPair.singularHomologyMap (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.hom R n := by
  rw [mapOrientation_eq_map_coordChangeL e e' hb hb', Orientation.map_eq_iff_det_pos _ _ hι] at h
  -- `ContinuousLinearMap.det` is by definition the determinant of the underlying linear map.
  have hd : 0 < (e.coordChangeL ℝ e' b : F →L[ℝ] F).det := h
  rw [e.singularHomologyMap_complZeroPairIso_hom_eq_sign_det_smul e' hb hb', sign_pos hd,
    SignType.coe_one, one_smul]

include hι in
/-- Two linear trivializations reading an orientation of the fibre over `b` as opposite
orientations of the model fibre identify `Hₙ(E_b, E_b ∖ {0})` with `Hₙ(F, F ∖ {0})` in opposite
ways. -/
theorem singularHomologyMap_complZeroPairIso_hom_eq_neg_of_mapOrientation_eq_neg
    (h : e'.mapOrientation ι hb' o = -e.mapOrientation ι hb o) (n : ℕ) :
    TopPair.singularHomologyMap (e'.continuousLinearEquivAt ℝ b hb').complZeroPairIso.hom R n =
      -TopPair.singularHomologyMap (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.hom R n := by
  rw [mapOrientation_eq_map_coordChangeL e e' hb hb', Orientation.map_eq_neg_iff_det_neg _ _ hι]
    at h
  -- `ContinuousLinearMap.det` is by definition the determinant of the underlying linear map.
  have hd : (e.coordChangeL ℝ e' b : F →L[ℝ] F).det < 0 := h
  rw [e.singularHomologyMap_complZeroPairIso_hom_eq_sign_det_smul e' hb hb', sign_neg hd,
    SignType.coe_neg_one, neg_one_smul]

end Bundle.Trivialization

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
private theorem exists_eq_units_smul_complZeroPairGenerator {z : ((TopPair.ofSubset
    (X := TopCat.of F) ({0}ᶜ : Set F)).singularHomology (ModuleCat.of K K) (finrank ℝ F) :
      ModuleCat.{w} K)} (hz : Submodule.span K {z} = ⊤) :
    ∃ u : Kˣ, z = u • complZeroPairGenerator K F := by
  let φ := (singularHomologyComplSingletonFinrankIso (ModuleCat.of K K)
    (OpenPartialHomeomorph.refl F) (mem_univ 0)).toLinearEquiv
  obtain ⟨u, hu⟩ := φ.span_singleton_eq_top_iff_isUnit.1 hz
  obtain ⟨v, hv⟩ := φ.span_singleton_eq_top_iff_isUnit.1 (span_complZeroPairGenerator K F)
  refine ⟨u * v⁻¹, φ.injective ?_⟩
  rw [Units.smul_def, map_smul, ← hu, ← hv, smul_eq_mul, Units.val_mul, mul_assoc,
    Units.inv_mul, mul_one]

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

/-! ### Families of fibre generators read uniformly in trivializations -/

variable (K F E) in
/-- A generator `z` of `Hᵣ(F, F ∖ {0}; K)` and a family `g` of classes of the fibre pairs
`(E_b, E_b ∖ {0})` *coherent* with it: every preferred trivialization reads `g` as `z` or `-z` at
each point of its base set, and locally constantly. -/
private structure CoherentFamily where
  /-- The generator of the local homology of the model fibre. -/
  z : ((TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularHomology
    (ModuleCat.of K K) (finrank ℝ F) : ModuleCat.{w} K)
  /-- The classes of the fibre pairs. -/
  g : ∀ b, ((TopPair.ofSubset (X := TopCat.of (E b)) ({0}ᶜ : Set (E b))).singularHomology
    (ModuleCat.of K K) (finrank ℝ F) : ModuleCat.{w} K)
  span_z : Submodule.span K {z} = ⊤
  eq_or_eq_neg (b x : B) (hx : x ∈ (trivializationAt F E b).baseSet) :
    TopPair.singularHomologyMap ((trivializationAt F E b).continuousLinearEquivAt ℝ x
        hx).complZeroPairIso.hom (ModuleCat.of K K) (finrank ℝ F) (g x) = z ∨
      TopPair.singularHomologyMap ((trivializationAt F E b).continuousLinearEquivAt ℝ x
        hx).complZeroPairIso.hom (ModuleCat.of K K) (finrank ℝ F) (g x) = -z
  eventually_eq (b x : B) (hx : x ∈ (trivializationAt F E b).baseSet) :
    ∀ᶠ y in 𝓝 x, ∀ hy : y ∈ (trivializationAt F E b).baseSet,
      TopPair.singularHomologyMap ((trivializationAt F E b).continuousLinearEquivAt ℝ y
          hy).complZeroPairIso.hom (ModuleCat.of K K) (finrank ℝ F) (g y) =
        TopPair.singularHomologyMap ((trivializationAt F E b).continuousLinearEquivAt ℝ x
          hx).complZeroPairIso.hom (ModuleCat.of K K) (finrank ℝ F) (g x)

/-- A set `W` of the base is *uniformly read* for a coherent family `G` if it lies in the base set
of a linear trivialization reading every `G.g x`, `x ∈ W`, as one generator of
`Hᵣ(F, F ∖ {0}; K)`. -/
private def IsUniformlyRead (G : CoherentFamily K F E) (W : Set B) : Prop :=
  ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ) (c : ((TopPair.ofSubset
      (X := TopCat.of F) ({0}ᶜ : Set F)).singularHomology (ModuleCat.of K K) (finrank ℝ F) :
        ModuleCat.{w} K)), Submodule.span K {c} = ⊤ ∧
    ∀ x ∈ W, ∃ hx : x ∈ e.baseSet, TopPair.singularHomologyMap (e.continuousLinearEquivAt ℝ x
      hx).complZeroPairIso.hom (ModuleCat.of K K) (finrank ℝ F) (G.g x) = c

omit [FiniteDimensional ℝ F] in
private theorem IsUniformlyRead.mono
    {G : CoherentFamily K F E} {W W' : Set B} (h : IsUniformlyRead G W') (hW : W ⊆ W') :
    IsUniformlyRead G W := by
  obtain ⟨e, he, c, hc, hg⟩ := h
  exact ⟨e, he, c, hc, fun x hx ↦ hg x (hW hx)⟩

omit [FiniteDimensional ℝ F] in
/-- The points of the base set of the preferred trivialization at `b` where it reads `G.g` as `c`
form an open set. -/
private theorem CoherentFamily.isOpen_setOf_eq (G : CoherentFamily K F E) (b : B)
    (c : ((TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularHomology
      (ModuleCat.of K K) (finrank ℝ F) : ModuleCat.{w} K)) :
    IsOpen {x | ∃ hx : x ∈ (trivializationAt F E b).baseSet,
      TopPair.singularHomologyMap ((trivializationAt F E b).continuousLinearEquivAt ℝ x
        hx).complZeroPairIso.hom (ModuleCat.of K K) (finrank ℝ F) (G.g x) = c} := by
  refine isOpen_iff_mem_nhds.2 fun x ⟨hx, hxc⟩ ↦ ?_
  filter_upwards [G.eventually_eq b x hx,
    (trivializationAt F E b).open_baseSet.mem_nhds hx] with y hy hyb
  exact ⟨hyb, (hy hyb).trans hxc⟩

omit [FiniteDimensional ℝ F] in
/-- Every point has a uniformly read neighbourhood. -/
private theorem CoherentFamily.exists_mem_nhds_isUniformlyRead (G : CoherentFamily K F E)
    (b : B) : ∃ V ∈ 𝓝 b, IsUniformlyRead G V := by
  have hb := mem_baseSet_trivializationAt F E b
  have hc : Submodule.span K
      {TopPair.singularHomologyMap ((trivializationAt F E b).continuousLinearEquivAt ℝ b
        hb).complZeroPairIso.hom (ModuleCat.of K K) (finrank ℝ F) (G.g b)} = ⊤ := by
    rcases G.eq_or_eq_neg b b hb with h | h <;> rw [h]
    · exact G.span_z
    · rw [← Set.neg_singleton, Submodule.span_neg, G.span_z]
  exact ⟨_, (G.isOpen_setOf_eq b _).mem_nhds ⟨hb, rfl⟩,
    trivializationAt F E b, inferInstance, _, hc, fun _ hx ↦ hx⟩

/-- The fibre class over a point `x` of `W`: the image of `G.g x` in `Hᵣ(E|_W, E₀|_W; K)`. -/
private def fiberClassOver (G : CoherentFamily K F E) (W : Set B) (x : W) :
    ((thomPairOver F E W).singularHomology (ModuleCat.of K K) (finrank ℝ F) : ModuleCat.{w} K) :=
  TopPair.singularHomologyMap (fiberThomPairOverMap F E x.2) (ModuleCat.of K K) (finrank ℝ F)
    (G.g x)

omit [FiniteDimensional ℝ F] in
/-- Restricting from `W` to `W'` carries fibre classes to fibre classes. -/
private theorem singularHomologyMap_thomPairOverMap_fiberClassOver
    {G : CoherentFamily K F E} {W W' : Set B} (h : W ⊆ W')
    (x : W) :
    TopPair.singularHomologyMap (thomPairOverMap F E h) (ModuleCat.of K K) (finrank ℝ F)
        (fiberClassOver G W x) = fiberClassOver G W' (inclusion h x) := by
  rw [fiberClassOver, fiberClassOver, ← ConcreteCategory.comp_apply,
    ← TopPair.singularHomologyMap_comp, fiberThomPairOverMap_comp_thomPairOverMap]

/-- **The fibre classes over a uniformly read set are multiples of the classes of the points**: a
linear trivialization over `W` reading every `G.g x` as `u • z₀`, for `z₀` the generator of
`Hᵣ(F, F ∖ {0}; K)` corresponding to the class of a point, identifies `Hᵣ(E|_W, E₀|_W; K)` with
`Hᵣ(W × F, W × (F ∖ {0}); K) ≅ H₀(W; K)`, and this sends the fibre class over `x` to `u` times the
class of `x`. -/
private theorem singularHomologyMap_thomPairOverIso_fiberClassOver
    {G : CoherentFamily K F E} (e : Trivialization F (π F E))
    [e.IsLinear ℝ] {W : Set B} (hW : W ⊆ e.baseSet) {u : K}
    (hg : ∀ x : W, TopPair.singularHomologyMap (e.continuousLinearEquivAt ℝ x
      (hW x.2)).complZeroPairIso.hom (ModuleCat.of K K) (finrank ℝ F) (G.g x) =
        u • complZeroPairGenerator K F) (x : W) :
    TopPair.singularHomologyMap (e.thomPairOverIso ℝ hW).hom (ModuleCat.of K K) (finrank ℝ F)
        (fiberClassOver G W x) =
      u • (prodThomPairSingularHomologyIso (ModuleCat.of K K) W F 0 (finrank ℝ F)).inv
        (singularHomology₀Section (ModuleCat.of K K) (X := TopCat.of W) x 1) := by
  rw [fiberClassOver, ← ConcreteCategory.comp_apply, ← TopPair.singularHomologyMap_comp,
    Bundle.Trivialization.fiberThomPairOverMap_comp_thomPairOverIso_hom ℝ e hW x.2,
    TopPair.singularHomologyMap_comp, ConcreteCategory.comp_apply, hg x, map_smul,
    Subtype.coe_eta, singularHomologyMap_prodThomPairFiberMap_complZeroPairGenerator]

/-- The fibre classes over two points of `W` joined by a path in a uniformly read part of `W`
agree. -/
private theorem fiberClassOver_eq_of_joinedIn
    {G : CoherentFamily K F E} {V : Set B} (hV : IsUniformlyRead G V)
    {W : Set B} {x y : W} (h : JoinedIn {z : W | (z : B) ∈ V} x y) :
    fiberClassOver G W x = fiberClassOver G W y := by
  obtain ⟨e, _, c, hc, hgc⟩ := hV.mono (inter_subset_right (s := W))
  obtain ⟨u, rfl⟩ := exists_eq_units_smul_complZeroPairGenerator K F hc
  have hW : W ∩ V ⊆ e.baseSet := fun b hb ↦ (hgc b hb).1
  let x' : ↥(W ∩ V) := ⟨x, x.2, h.source_mem⟩
  let y' : ↥(W ∩ V) := ⟨y, y.2, h.target_mem⟩
  -- The two points are joined in `W ∩ V`, so their classes in `H₀` agree.
  have hj : Joined x' y' :=
    h.joined_subtype.map (f := fun z : {z : W | (z : B) ∈ V} ↦
      (⟨z.1.1, z.1.2, z.2⟩ : ↥(W ∩ V))) (by fun_prop)
  have hxy : fiberClassOver G (W ∩ V) x' = fiberClassOver G (W ∩ V) y' := by
    apply (ModuleCat.mono_iff_injective (TopPair.singularHomologyMap (e.thomPairOverIso ℝ hW).hom
      (ModuleCat.of K K) (finrank ℝ F))).1 inferInstance
    have hu : ∀ b : ↥(W ∩ V), TopPair.singularHomologyMap (e.continuousLinearEquivAt ℝ b
        (hW b.2)).complZeroPairIso.hom (ModuleCat.of K K) (finrank ℝ F) (G.g b) =
          (u : K) • complZeroPairGenerator K F := fun b ↦ (hgc b b.2).2
    rw [singularHomologyMap_thomPairOverIso_fiberClassOver e hW hu,
      singularHomologyMap_thomPairOverIso_fiberClassOver e hW hu,
      singularHomology₀Section_eq_of_joined _ hj]
  have := congrArg (TopPair.singularHomologyMap (thomPairOverMap F E inter_subset_left)
    (ModuleCat.of K K) (finrank ℝ F)) hxy
  rwa [singularHomologyMap_thomPairOverMap_fiberClassOver,
    singularHomologyMap_thomPairOverMap_fiberClassOver] at this

/-- **The fibre classes are constant along paths.** -/
private theorem fiberClassOver_eq_of_path (G : CoherentFamily K F E)
    {W : Set B} {x y : W} (γ : Path x y) :
    fiberClassOver G W x = fiberClassOver G W y := by
  have : LocallyPathConnectedSpace unitInterval :=
    Convex.locallyPathConnectedSpace ℝ (convex_Icc (0 : ℝ) 1)
  have hlc : IsLocallyConstant fun t ↦ fiberClassOver G W (γ t) := by
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun t ↦ ?_
    obtain ⟨V, hVb, hV⟩ := G.exists_mem_nhds_isUniformlyRead (γ t : B)
    have hO : {s : unitInterval | ((γ s : W) : B) ∈ V} ∈ 𝓝 t :=
      (continuous_subtype_val.comp γ.continuous).continuousAt.preimage_mem_nhds hVb
    filter_upwards [pathComponentIn_mem_nhds hO] with s hs
    refine (fiberClassOver_eq_of_joinedIn hV ((hs.map γ.continuous.continuousOn).mono ?_)).symm
    rintro _ ⟨u, hu, rfl⟩
    exact hu
  simpa using hlc.apply_eq_of_preconnectedSpace 0 1

/-- The map `H₀(W; K) ⟶ Hᵣ(E|_W, E₀|_W; K)` sending the class of a point to the fibre class over
it. -/
private def thomPairOverSingularHomologyFinrankInv (G : CoherentFamily K F E) (W : Set B) :
    ((singularHomologyFunctor (ModuleCat.{w} K) 0).obj (ModuleCat.of K K)).obj (TopCat.of W) ⟶
      (thomPairOver F E W).singularHomology (ModuleCat.of K K) (finrank ℝ F) :=
  singularHomology₀Desc (ModuleCat.of K K) (X := TopCat.of W)
    (fun x ↦ ModuleCat.ofHom (LinearMap.toSpanSingleton K _ (fiberClassOver G W x)))
    fun _ _ γ ↦ by rw [fiberClassOver_eq_of_path G γ]

@[reassoc]
private theorem singularHomology₀Section_thomPairOverSingularHomologyFinrankInv
    {G : CoherentFamily K F E} {W : Set B} (x : W) :
    singularHomology₀Section (ModuleCat.of K K) (X := TopCat.of W) x ≫
        thomPairOverSingularHomologyFinrankInv G W =
      ModuleCat.ofHom (LinearMap.toSpanSingleton K _ (fiberClassOver G W x)) := by
  rw [thomPairOverSingularHomologyFinrankInv]
  exact singularHomology₀Section_singularHomology₀Desc (X := TopCat.of W) _ _ _ x

/-- The maps over `W ⊆ W'` commute with the restrictions. -/
private theorem thomPairOverSingularHomologyFinrankInv_naturality
    {G : CoherentFamily K F E} {W W' : Set B} (h : W ⊆ W') :
    ((singularHomologyFunctor (ModuleCat.{w} K) 0).obj (ModuleCat.of K K)).map
        (TopCat.ofHom (ContinuousMap.inclusion h)) ≫
        thomPairOverSingularHomologyFinrankInv G W' =
      thomPairOverSingularHomologyFinrankInv G W ≫
        TopPair.singularHomologyMap (thomPairOverMap F E h) (ModuleCat.of K K) (finrank ℝ F) := by
  refine singularHomology₀_hom_ext _ fun x ↦ ?_
  rw [singularHomology₀Section_naturality_assoc,
    singularHomology₀Section_thomPairOverSingularHomologyFinrankInv,
    singularHomology₀Section_thomPairOverSingularHomologyFinrankInv_assoc,
    ModuleCat.ofHom_toSpanSingleton_comp, singularHomologyMap_thomPairOverMap_fiberClassOver]
  rw [ConcreteCategory.hom_ofHom, show ContinuousMap.inclusion h x = inclusion h x from
    Subtype.ext ((ContinuousMap.inclusion_apply_coe h x).trans (coe_inclusion h x).symm)]

/-- Over a subset of the base set of a linear trivialization reading every `G.g x` as `u • z₀`, the
map is `u` times the inverse of the isomorphism `Hᵣ(W × F, W × (F ∖ {0})) ≅ H₀(W)` of the product
bundle, read through the trivialization. -/
private theorem thomPairOverSingularHomologyFinrankInv_comp_thomPairOverIso
    {G : CoherentFamily K F E}
    (e : Trivialization F (π F E)) [e.IsLinear ℝ] {W : Set B} (hW : W ⊆ e.baseSet) {u : K}
    (hu : ∀ x : W, TopPair.singularHomologyMap (e.continuousLinearEquivAt ℝ x
      (hW x.2)).complZeroPairIso.hom (ModuleCat.of K K) (finrank ℝ F) (G.g x) =
        u • complZeroPairGenerator K F) :
    thomPairOverSingularHomologyFinrankInv G W ≫
        TopPair.singularHomologyMap (e.thomPairOverIso ℝ hW).hom (ModuleCat.of K K)
          (finrank ℝ F) =
      u • (prodThomPairSingularHomologyIso (ModuleCat.of K K) W F 0 (finrank ℝ F)).inv := by
  refine singularHomology₀_hom_ext _ fun x ↦ ?_
  rw [singularHomology₀Section_thomPairOverSingularHomologyFinrankInv_assoc,
    ModuleCat.ofHom_toSpanSingleton_comp,
    singularHomologyMap_thomPairOverIso_fiberClassOver e hW hu]
  ext
  simp

private theorem isIso_thomPairOverSingularHomologyFinrankInv_of_isUniformlyRead
    {G : CoherentFamily K F E} {W : Set B}
    (hW : IsUniformlyRead G W) : IsIso (thomPairOverSingularHomologyFinrankInv G W) := by
  obtain ⟨e, _, c, hc, hgc⟩ := hW
  obtain ⟨u, rfl⟩ := exists_eq_units_smul_complZeroPairGenerator K F hc
  have hWe : W ⊆ e.baseSet := fun b hb ↦ (hgc b hb).1
  have h := thomPairOverSingularHomologyFinrankInv_comp_thomPairOverIso (G := G) e hWe
    (u := (u : K)) fun x ↦ (hgc x x.2).2
  -- A unit multiple of an isomorphism is an isomorphism.
  let P := prodThomPairSingularHomologyIso (ModuleCat.of K K) W F 0 (finrank ℝ F)
  have : IsIso ((u : K) • P.inv) :=
    ⟨(↑u⁻¹ : K) • P.hom, by simp [smul_smul], by simp [smul_smul]⟩
  rw [(IsIso.eq_comp_inv _).2 h]
  infer_instance

private theorem isIso_thomPairOverSingularHomologyFinrankInv_empty {G : CoherentFamily K F E} :
    IsIso (thomPairOverSingularHomologyFinrankInv G ∅) :=
  isIso_of_source_target_iso_zero _
    (isZero_singularHomologyFunctor_zero_of_isEmpty _ _).isoZero
    (isZero_singularHomology_thomPairOver_empty _ _).isoZero

/-- Over `W ⊆ W'`, with the map over `W'` an isomorphism, the restriction from `W` to `W'` read
through the maps over `W` and `W'` is the map induced by the inclusion. -/
@[reassoc]
private theorem thomPairOverSingularHomologyFinrankInv_comp_singularHomologyMap_comp_inv
    {G : CoherentFamily K F E}
    {W W' : Set B} (h : W ⊆ W') [IsIso (thomPairOverSingularHomologyFinrankInv G W')] :
    thomPairOverSingularHomologyFinrankInv G W ≫
        TopPair.singularHomologyMap (thomPairOverMap F E h) (ModuleCat.of K K) (finrank ℝ F) ≫
          inv (thomPairOverSingularHomologyFinrankInv G W') =
      ((singularHomologyFunctor (ModuleCat.{w} K) 0).obj (ModuleCat.of K K)).map
        (TopCat.ofHom (ContinuousMap.inclusion h)) := by
  rw [← Category.assoc, ← thomPairOverSingularHomologyFinrankInv_naturality, Category.assoc,
    IsIso.hom_inv_id, Category.comp_id]

/-- In the Mayer–Vietoris step, a candidate inverse `Φ` of the map over `W'` is built which on the
classes over a subset `W` is the inverse of the map over `W` followed by the inclusion. Such a `Φ`
inverts the map over `W'` on the classes of points of `W`. -/
private theorem singularHomology₀Section_thomPairOverSingularHomologyFinrankInv_comp_of_comp_eq
    {G : CoherentFamily K F E}
    {W W' : Set B} (h : W ⊆ W') [IsIso (thomPairOverSingularHomologyFinrankInv G W)]
    {Φ : (thomPairOver F E W').singularHomology (ModuleCat.of K K) (finrank ℝ F) ⟶
      ((singularHomologyFunctor (ModuleCat.{w} K) 0).obj (ModuleCat.of K K)).obj (TopCat.of W')}
    (hΦ : TopPair.singularHomologyMap (thomPairOverMap F E h) (ModuleCat.of K K) (finrank ℝ F) ≫
      Φ = inv (thomPairOverSingularHomologyFinrankInv G W) ≫
        ((singularHomologyFunctor (ModuleCat.{w} K) 0).obj (ModuleCat.of K K)).map
          (TopCat.ofHom (ContinuousMap.inclusion h)))
    (x : W) :
    singularHomology₀Section (ModuleCat.of K K) (X := TopCat.of W')
          (TopCat.ofHom (ContinuousMap.inclusion h) x) ≫
        thomPairOverSingularHomologyFinrankInv G W' ≫ Φ =
      singularHomology₀Section (ModuleCat.of K K) (X := TopCat.of W')
        (TopCat.ofHom (ContinuousMap.inclusion h) x) := by
  rw [← singularHomology₀Section_naturality, Category.assoc,
    reassoc_of% (thomPairOverSingularHomologyFinrankInv_naturality (K := K) (F := F) (E := E)
      (G := G) h),
    hΦ, IsIso.hom_inv_id_assoc]

/-- Such a `Φ` also inverts the map over `W'` on the classes over `W`. -/
private theorem singularHomologyMap_thomPairOverMap_comp_comp_of_comp_eq {G : CoherentFamily K F E}
    {W W' : Set B} (h : W ⊆ W') [IsIso (thomPairOverSingularHomologyFinrankInv G W)]
    {Φ : (thomPairOver F E W').singularHomology (ModuleCat.of K K) (finrank ℝ F) ⟶
      ((singularHomologyFunctor (ModuleCat.{w} K) 0).obj (ModuleCat.of K K)).obj (TopCat.of W')}
    (hΦ : TopPair.singularHomologyMap (thomPairOverMap F E h) (ModuleCat.of K K) (finrank ℝ F) ≫
      Φ = inv (thomPairOverSingularHomologyFinrankInv G W) ≫
        ((singularHomologyFunctor (ModuleCat.{w} K) 0).obj (ModuleCat.of K K)).map
          (TopCat.ofHom (ContinuousMap.inclusion h))) :
    TopPair.singularHomologyMap (thomPairOverMap F E h) (ModuleCat.of K K) (finrank ℝ F) ≫ Φ ≫
        thomPairOverSingularHomologyFinrankInv G W' =
      TopPair.singularHomologyMap (thomPairOverMap F E h) (ModuleCat.of K K) (finrank ℝ F) := by
  rw [reassoc_of% hΦ, thomPairOverSingularHomologyFinrankInv_naturality, IsIso.inv_hom_id_assoc]

/-- **The Mayer–Vietoris step**: if the maps over the open sets `U` and `V` are isomorphisms, the
map over `U ∩ V` is surjective and the homology of the Thom pair over `U ∩ V` vanishes in degree
`r - 1`, the map over `U ∪ V` is an isomorphism. -/
private theorem isIso_thomPairOverSingularHomologyFinrankInv_union
    {G : CoherentFamily K F E} {U V : Set B} (hU : IsOpen U)
    (hV : IsOpen V) [IsIso (thomPairOverSingularHomologyFinrankInv G U)]
    [IsIso (thomPairOverSingularHomologyFinrankInv G V)]
    [Epi (thomPairOverSingularHomologyFinrankInv G (U ∩ V))]
    (hUV : ∀ m, m + 1 = finrank ℝ F →
      IsZero ((thomPairOver F E (U ∩ V)).singularHomology (ModuleCat.of K K) m)) :
    IsIso (thomPairOverSingularHomologyFinrankInv G (U ∪ V)) := by
  let ψ := thomPairOverSingularHomologyFinrankInv G
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

/-- **Finite unions of uniformly read open sets**: the map is an isomorphism over a finite union of
open sets each uniformly read for `G`. -/
private theorem isIso_thomPairOverSingularHomologyFinrankInv_biUnion
    {G : CoherentFamily K F E} {ι : Type*} (s : Finset ι)
    {W : ι → Set B} (hWo : ∀ i ∈ s, IsOpen (W i)) (hWe : ∀ i ∈ s, IsUniformlyRead G (W i)) :
    IsIso (thomPairOverSingularHomologyFinrankInv G (⋃ i ∈ s, W i)) := by
  classical
  induction s using Finset.induction_on generalizing W with
  | empty =>
    rw [show (⋃ i ∈ (∅ : Finset ι), W i) = ∅ by simp]
    exact isIso_thomPairOverSingularHomologyFinrankInv_empty
  | insert a s _ ih =>
    rw [Finset.set_biUnion_insert]
    have hWa := hWe a (Finset.mem_insert_self a s)
    have : IsIso (thomPairOverSingularHomologyFinrankInv G (W a)) :=
      isIso_thomPairOverSingularHomologyFinrankInv_of_isUniformlyRead hWa
    have : IsIso (thomPairOverSingularHomologyFinrankInv G (⋃ i ∈ s, W i)) :=
      ih (fun i hi ↦ hWo i (Finset.mem_insert_of_mem hi))
        (fun i hi ↦ hWe i (Finset.mem_insert_of_mem hi))
    -- `W a ∩ ⋃ i ∈ s, W i` is the union of the uniformly read open sets `W a ∩ W i`, `i ∈ s`.
    have : IsIso (thomPairOverSingularHomologyFinrankInv G (W a ∩ ⋃ i ∈ s, W i)) := by
      rw [inter_iUnion₂]
      exact ih (fun i hi ↦ (hWo a (Finset.mem_insert_self a s)).inter
        (hWo i (Finset.mem_insert_of_mem hi)))
        fun i hi ↦ (hWe i (Finset.mem_insert_of_mem hi)).mono inter_subset_right
    obtain ⟨e, _, c, -, hgc⟩ := hWa
    exact isIso_thomPairOverSingularHomologyFinrankInv_union (hWo a (Finset.mem_insert_self a s))
      (isOpen_iUnion fun i ↦ isOpen_iUnion fun hi ↦ hWo i (Finset.mem_insert_of_mem hi))
      fun m hm ↦ e.isZero_singularHomology_thomPairOver
        (inter_subset_left.trans fun b hb ↦ (hgc b hb).1) _ (by omega)

/-! ### The passage to the whole base -/

/-- The map `H₀(B; K) ⟶ Hᵣ(E, E₀; K)` sending the class of a point to the fibre class over it. -/
private def thomPairSingularHomologyFinrankInv (G : CoherentFamily K F E) :
    ((singularHomologyFunctor (ModuleCat.{w} K) 0).obj (ModuleCat.of K K)).obj (TopCat.of B) ⟶
      (thomPair F E).singularHomology (ModuleCat.of K K) (finrank ℝ F) :=
  ((singularHomologyFunctor (ModuleCat.{w} K) 0).obj (ModuleCat.of K K)).map
      (TopCat.isoOfHomeo (Homeomorph.Set.univ B).symm).hom ≫
    thomPairOverSingularHomologyFinrankInv G univ ≫
      TopPair.singularHomologyMap (thomPairOverUnivIso F E).hom (ModuleCat.of K K) (finrank ℝ F)

private theorem singularHomology₀Section_thomPairSingularHomologyFinrankInv
    {G : CoherentFamily K F E} (b : B) :
    singularHomology₀Section (ModuleCat.of K K) (X := TopCat.of B) b ≫
        thomPairSingularHomologyFinrankInv G =
      ModuleCat.ofHom (LinearMap.toSpanSingleton K _ (TopPair.singularHomologyMap
        (fiberThomPairMap F E b) (ModuleCat.of K K) (finrank ℝ F) (G.g b))) := by
  rw [thomPairSingularHomologyFinrankInv, singularHomology₀Section_naturality_assoc,
    singularHomology₀Section_thomPairOverSingularHomologyFinrankInv_assoc,
    ModuleCat.ofHom_toSpanSingleton_comp, fiberClassOver, ← ConcreteCategory.comp_apply,
    ← TopPair.singularHomologyMap_comp]
  exact congrArg (fun f ↦ ModuleCat.ofHom (LinearMap.toSpanSingleton K _
    (TopPair.singularHomologyMap f (ModuleCat.of K K) (finrank ℝ F) (G.g b))))
    (fiberThomPairOverMap_comp_thomPairOverUnivIso_hom F E b)

/-- On a finite union of the chosen trivializing sets, the map over the base restricts to the
map over the union. -/
private theorem thomPairSingularHomologyFinrankInv_restrict
    {G : CoherentFamily K F E} (s : Finset B) :
    ((singularHomologyFunctor (ModuleCat.{w} K) 0).obj (ModuleCat.of K K)).map
        (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ :
          TopCat.of ↥(⋃ b ∈ s, (trivializationAt F E b).baseSet) ⟶ TopCat.of B) ≫
        thomPairSingularHomologyFinrankInv G =
      thomPairOverSingularHomologyFinrankInv G
          (⋃ b ∈ s, (trivializationAt F E b).baseSet) ≫
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

/-- The map is an isomorphism over each finite union of the chosen trivializing sets: the base set
of the preferred trivialization at `b` is the union of the two open sets where it reads `G.g` as
`G.z` and as `-G.z`, both uniformly read. -/
private theorem isIso_thomPairOverSingularHomologyFinrankInv_finiteTrivializingUnion
    {G : CoherentFamily K F E}
    (s : Finset B) : IsIso (thomPairOverSingularHomologyFinrankInv G
      (⋃ b ∈ s, (trivializationAt F E b).baseSet)) := by
  classical
  let S : B × Bool → Set B := fun p ↦ {x | ∃ hx : x ∈ (trivializationAt F E p.1).baseSet,
    TopPair.singularHomologyMap ((trivializationAt F E p.1).continuousLinearEquivAt ℝ x
      hx).complZeroPairIso.hom (ModuleCat.of K K) (finrank ℝ F) (G.g x) =
        bif p.2 then G.z else -G.z}
  have hS : (⋃ b ∈ s, (trivializationAt F E b).baseSet) = ⋃ p ∈ s ×ˢ Finset.univ, S p := by
    ext x
    simp only [mem_iUnion, Finset.mem_product, Finset.mem_univ, and_true, exists_prop, Prod.exists]
    constructor
    · rintro ⟨b, hb, hx⟩
      rcases G.eq_or_eq_neg b x hx with h | h
      · exact ⟨b, true, hb, hx, h⟩
      · exact ⟨b, false, hb, hx, h⟩
    · rintro ⟨b, _, hb, hx, -⟩
      exact ⟨b, hb, hx⟩
  rw [hS]
  refine isIso_thomPairOverSingularHomologyFinrankInv_biUnion _
    (fun p _ ↦ G.isOpen_setOf_eq p.1 _) fun p _ ↦
      ⟨trivializationAt F E p.1, inferInstance, bif p.2 then G.z else -G.z, ?_, fun _ hx ↦ hx⟩
  cases p.2
  · rw [Bool.cond_false, ← Set.neg_singleton, Submodule.span_neg, G.span_z]
  · exact G.span_z

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

/-- The maps over the finite unions of the chosen trivializing sets, as a natural isomorphism
between the homologies of the bases and of the Thom pairs. -/
private def thomPairFiniteTrivializingUnionSingularHomologyFinrankIso (G : CoherentFamily K F E) :
    baseFiniteTrivializingUnionDiagram F E ⋙
        (singularHomologyFunctor (ModuleCat.{w} K) 0).obj (ModuleCat.of K K) ≅
      thomPairFiniteTrivializingUnionDiagram (F := F) (E := E) ⋙
        TopPair.singularHomologyFunctor (ModuleCat.of K K) (finrank ℝ F) :=
  NatIso.ofComponents (fun s ↦ @asIso _ _ _ _ (thomPairOverSingularHomologyFinrankInv G
      (⋃ b ∈ s, (trivializationAt F E b).baseSet))
        (isIso_thomPairOverSingularHomologyFinrankInv_finiteTrivializingUnion s) ≪≫
      eqToIso (singularHomology_thomPairOver_finiteTrivializingUnion_eq K s))
    fun {s t} f ↦ by
      have := isIso_thomPairOverSingularHomologyFinrankInv_finiteTrivializingUnion (G := G) s
      have := isIso_thomPairOverSingularHomologyFinrankInv_finiteTrivializingUnion (G := G) t
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
private theorem singularHomologyMap_ι_thomPairSingularHomologyFinrankInv
    {G : CoherentFamily K F E} (s : Finset B) :
    ((singularHomologyFunctor (ModuleCat.{w} K) 0).obj (ModuleCat.of K K)).map
        (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ :
          TopCat.of ↥(⋃ b ∈ s, (trivializationAt F E b).baseSet) ⟶ TopCat.of B) ≫
        thomPairSingularHomologyFinrankInv G ≫ eqToHom (singularHomology_thomPair_eq K) =
      thomPairOverSingularHomologyFinrankInv G
          (⋃ b ∈ s, (trivializationAt F E b).baseSet) ≫
        eqToHom (singularHomology_thomPairOver_finiteTrivializingUnion_eq K s) ≫
          (TopPair.singularHomologyFunctor (ModuleCat.of K K) (finrank ℝ F)).map
            ((thomPairFiniteTrivializingUnionCocone (F := F) (E := E)).ι.app s) := by
  rw [reassoc_of% (thomPairSingularHomologyFinrankInv_restrict (G := G) s)]
  simp only [thomPairFiniteTrivializingUnionCocone_ι_app, TopPair.singularHomologyFunctor_map,
    Category.assoc, TopPair.singularHomologyMap_comp, TopPair.singularHomologyMap_eqToHom,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, eqToHom_trans]

/-- **The passage to the whole base**: the homologies of the base and of the Thom pair are the
filtered colimits of their homologies over the finite unions of the chosen trivializing sets, and
over these the map is an isomorphism. -/
private theorem isIso_thomPairSingularHomologyFinrankInv {G : CoherentFamily K F E} :
    IsIso (thomPairSingularHomologyFinrankInv G) := by
  let P₁ := isColimitSingularHomologyBaseFiniteTrivializingUnion K F E
  let P₂ := isColimitMapCoconeSingularHomologyThomPairFiniteTrivializingUnion (F := F) (E := E)
    (ModuleCat.of K K) (finrank ℝ F)
  let α := thomPairFiniteTrivializingUnionSingularHomologyFinrankIso G
  have h : thomPairSingularHomologyFinrankInv G ≫
      eqToHom (singularHomology_thomPair_eq K) = (P₁.coconePointsIsoOfNatIso P₂ α).hom :=
    P₁.hom_ext fun s ↦ (singularHomologyMap_ι_thomPairSingularHomologyFinrankInv s).trans
      (P₁.comp_coconePointsIsoOfNatIso_hom P₂ α s).symm
  have : IsIso (thomPairSingularHomologyFinrankInv G ≫
      eqToHom (singularHomology_thomPair_eq K)) := by
    rw [h]
    exact (P₁.coconePointsIsoOfNatIso P₂ α).isIso_hom
  exact IsIso.of_isIso_comp_right _ (eqToHom (singularHomology_thomPair_eq K))

/-- The isomorphism `Hᵣ(E, E₀; K) ≅ H₀(B; K)` of a coherent family of fibre generators, sending the
fibre class of `G.g b` to the class of `b`. -/
private def thomPairSingularHomologyFinrankIsoOfCoherentFamily (G : CoherentFamily K F E) :
    (thomPair F E).singularHomology (ModuleCat.of K K) (finrank ℝ F) ≅
      ((singularHomologyFunctor (ModuleCat.{w} K) 0).obj (ModuleCat.of K K)).obj (TopCat.of B) :=
  (@asIso _ _ _ _ (thomPairSingularHomologyFinrankInv G)
    isIso_thomPairSingularHomologyFinrankInv).symm

private theorem thomPairSingularHomologyFinrankIsoOfCoherentFamily_hom_apply
    {G : CoherentFamily K F E} (b : B) :
    (thomPairSingularHomologyFinrankIsoOfCoherentFamily G).hom
        (TopPair.singularHomologyMap (fiberThomPairMap F E b) (ModuleCat.of K K) (finrank ℝ F)
          (G.g b)) =
      singularHomology₀Section (ModuleCat.of K K) (X := TopCat.of B) b 1 := by
  have h := congrArg (fun f ↦ f (1 : K))
    (singularHomology₀Section_thomPairSingularHomologyFinrankInv (G := G) b)
  simp only [ModuleCat.hom_ofHom, LinearMap.toSpanSingleton_apply, one_smul,
    ConcreteCategory.comp_apply] at h
  rw [← h, thomPairSingularHomologyFinrankIsoOfCoherentFamily, Iso.symm_hom, asIso_inv,
    ← ConcreteCategory.comp_apply, IsIso.hom_inv_id, ConcreteCategory.id_apply]

/-! ### Coefficient rings whose only unit is `1` -/

variable (K F E) in
/-- The generator of `Hᵣ(E_b, E_b ∖ {0}; K)`, read through the trivialization at `b`. -/
private def fiberGenerator (b : B) :
    ((TopPair.ofSubset (X := TopCat.of (E b)) ({0}ᶜ : Set (E b))).singularHomology
      (ModuleCat.of K K) (finrank ℝ F) : ModuleCat.{w} K) :=
  TopPair.singularHomologyMap ((trivializationAt F E b).continuousLinearEquivAt ℝ b
      (mem_baseSet_trivializationAt F E b)).complZeroPairIso.inv (ModuleCat.of K K) (finrank ℝ F)
    (complZeroPairGenerator K F)

private theorem span_fiberGenerator (b : B) : Submodule.span K {fiberGenerator K F E b} = ⊤ :=
  (ModuleCat.span_singleton_apply_eq_top_iff _).2 (span_complZeroPairGenerator K F)

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

/-- Every linear trivialization reads the fibre generator over `x` as the generator of
`Hᵣ(F, F ∖ {0}; K)`. -/
private theorem singularHomologyMap_complZeroPairIso_hom_fiberGenerator
    (e : Trivialization F (π F E)) [e.IsLinear ℝ] {x : B} (hx : x ∈ e.baseSet) :
    TopPair.singularHomologyMap (e.continuousLinearEquivAt ℝ x hx).complZeroPairIso.hom
      (ModuleCat.of K K) (finrank ℝ F) (fiberGenerator K F E x) = complZeroPairGenerator K F :=
  eq_complZeroPairGenerator K F
    ((ModuleCat.span_singleton_apply_eq_top_iff _).2 (span_fiberGenerator x))

variable (K F E) in
/-- The fibre generators form a coherent family. -/
private def fiberGeneratorCoherentFamily : CoherentFamily K F E where
  z := complZeroPairGenerator K F
  g := fiberGenerator K F E
  span_z := span_complZeroPairGenerator K F
  eq_or_eq_neg _ _ hx := .inl (singularHomologyMap_complZeroPairIso_hom_fiberGenerator _ hx)
  eventually_eq _ _ hx := .of_forall fun _ hy ↦
    (singularHomologyMap_complZeroPairIso_hom_fiberGenerator _ hy).trans
      (singularHomologyMap_complZeroPairIso_hom_fiberGenerator _ hx).symm

variable (K F E) in
/-- **The homology of the Thom pair in the rank degree**: for a real vector bundle `E → B` of
rank `r`, with Thom pair `(E, E₀)`, and a commutative ring `K` whose only unit is `1`, such as
`ZMod 2`, `Hᵣ(E, E₀; K) ≅ H₀(B; K)`. It sends the fibre class over `b` to the class of `b`
(`TauCeti.thomPairSingularHomologyFinrankIso_hom_apply`). The base is arbitrary and the bundle
need not be orientable. -/
def thomPairSingularHomologyFinrankIso :
    (thomPair F E).singularHomology (ModuleCat.of K K) (finrank ℝ F) ≅
      ((singularHomologyFunctor (ModuleCat.{w} K) 0).obj (ModuleCat.of K K)).obj (TopCat.of B) :=
  thomPairSingularHomologyFinrankIsoOfCoherentFamily (fiberGeneratorCoherentFamily K F E)

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
  exact thomPairSingularHomologyFinrankIsoOfCoherentFamily_hom_apply (G :=
    fiberGeneratorCoherentFamily K F E) b

end Bundle

/-! ### Oriented bundles -/

namespace VectorBundleOrientation

variable {K : Type w} [CommRing K] {B : Type w} [TopologicalSpace B] {F : Type w}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {E : B → Type w}
  [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)]
  [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]
  {ι : Type*} [Fintype ι] (o : VectorBundleOrientation F E ι) (hι : Fintype.card ι = finrank ℝ F)
  (ω : Orientation ℝ F ι)
  (z : ((TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularHomology (ModuleCat.of K K)
    (finrank ℝ F) : ModuleCat.{w} K))

open scoped Classical in
/-- The class of the fibre pair over `b` read as `z` in a trivialization reading the orientation
`o b` as `ω`: the pull-back of `±z` along the preferred trivialization at `b`, with the sign by
which that trivialization reads `o b`. -/
private def fiberGeneratorOfModel (b : B) :
    ((TopPair.ofSubset (X := TopCat.of (E b)) ({0}ᶜ : Set (E b))).singularHomology
      (ModuleCat.of K K) (finrank ℝ F) : ModuleCat.{w} K) :=
  TopPair.singularHomologyMap ((trivializationAt F E b).continuousLinearEquivAt ℝ b
      (mem_baseSet_trivializationAt F E b)).complZeroPairIso.inv (ModuleCat.of K K) (finrank ℝ F)
    (if (trivializationAt F E b).mapOrientation ι (mem_baseSet_trivializationAt F E b) (o b) = ω
      then z else -z)

variable {o ω z}

open scoped Classical in
include hι in
/-- Every linear trivialization `e` reads the fibre generator over `x` as `z` or `-z`, according as
it reads the orientation `o x` as `ω` or not. -/
private theorem singularHomologyMap_complZeroPairIso_hom_fiberGeneratorOfModel
    (e : Trivialization F (π F E)) [e.IsLinear ℝ] {x : B} (hx : x ∈ e.baseSet) :
    TopPair.singularHomologyMap (e.continuousLinearEquivAt ℝ x hx).complZeroPairIso.hom
        (ModuleCat.of K K) (finrank ℝ F) (o.fiberGeneratorOfModel ω z x) =
      if e.mapOrientation ι hx (o x) = ω then z else -z := by
  have hx₀ := mem_baseSet_trivializationAt F E x
  let e₀ := trivializationAt F E x
  -- The preferred trivialization reads the fibre generator as `±z` by construction.
  have h₀ : TopPair.singularHomologyMap (e₀.continuousLinearEquivAt ℝ x hx₀).complZeroPairIso.hom
      (ModuleCat.of K K) (finrank ℝ F) (o.fiberGeneratorOfModel ω z x) =
        if e₀.mapOrientation ι hx₀ (o x) = ω then z else -z := by
    rw [fiberGeneratorOfModel, ← ConcreteCategory.comp_apply, ← TopPair.singularHomologyMap_comp,
      Iso.inv_hom_id, TopPair.singularHomologyMap_id, ConcreteCategory.id_apply]
  -- Compare `e` with the preferred trivialization through the orientation of `E_x` they read.
  have hcomp (h : e.mapOrientation ι hx (o x) = e₀.mapOrientation ι hx₀ (o x)) :=
    e₀.singularHomologyMap_complZeroPairIso_hom_eq_of_mapOrientation_eq e hx₀ hx (ModuleCat.of K K)
      hι h (finrank ℝ F)
  have hneg (h : e.mapOrientation ι hx (o x) = -e₀.mapOrientation ι hx₀ (o x)) :=
    e₀.singularHomologyMap_complZeroPairIso_hom_eq_neg_of_mapOrientation_eq_neg e hx₀ hx
      (ModuleCat.of K K) hι h (finrank ℝ F)
  have hω : ω ≠ -ω := Module.Ray.ne_neg_self ω
  rcases (e₀.mapOrientation ι hx₀ (o x)).eq_or_eq_neg ω hι with h | h <;>
    rcases (e.mapOrientation ι hx (o x)).eq_or_eq_neg ω hι with h' | h'
  · rw [hcomp (h'.trans h.symm), h₀]
    simp [h, h']
  · rw [hneg (by rw [h', h])]
    simp [h₀, h, h', hω.symm]
  · rw [hneg (by rw [h', h]; exact (neg_neg ω).symm)]
    simp [h₀, h, h', hω.symm]
  · rw [hcomp (h'.trans h.symm), h₀]
    simp [h, h', hω.symm]

variable (o ω z) in
/-- The fibre generators of an oriented bundle form a coherent family. -/
private def coherentFamilyOfModel (hz : Submodule.span K {z} = ⊤) : CoherentFamily K F E where
  z := z
  g := o.fiberGeneratorOfModel ω z
  span_z := hz
  eq_or_eq_neg b x hx := by
    classical
    rw [singularHomologyMap_complZeroPairIso_hom_fiberGeneratorOfModel hι]
    split_ifs
    · exact .inl rfl
    · exact .inr rfl
  eventually_eq b x hx := by
    classical
    filter_upwards [o.eventually_mapOrientation_eq hι (trivializationAt F E b) hx] with y hy hyb
    rw [singularHomologyMap_complZeroPairIso_hom_fiberGeneratorOfModel hι,
      singularHomologyMap_complZeroPairIso_hom_fiberGeneratorOfModel hι, hy hyb]

variable (o ω z) in
/-- **The homology of the Thom pair of an oriented bundle in the rank degree**: for a real vector
bundle `E → B` of rank `r` with an orientation `o`, and any commutative ring `K`, such as `ℤ`,
`Hᵣ(E, E₀; K) ≅ H₀(B; K)`. It is normalized by an orientation `ω` of the model fibre and a
generator `z` of `Hᵣ(F, F ∖ {0}; K)`: it sends the fibre class over `b` of the pull-back of `z`
along a linear trivialization reading `o b` as `ω` to the class of `b`, and along one reading `o b`
as `-ω` to its negative
(`thomPairSingularHomologyFinrankIso_hom_apply_of_mapOrientation_eq` and
`thomPairSingularHomologyFinrankIso_hom_apply_of_mapOrientation_eq_neg`).
The base is arbitrary. -/
def thomPairSingularHomologyFinrankIso (hz : Submodule.span K {z} = ⊤) :
    (thomPair F E).singularHomology (ModuleCat.of K K) (finrank ℝ F) ≅
      ((singularHomologyFunctor (ModuleCat.{w} K) 0).obj (ModuleCat.of K K)).obj (TopCat.of B) :=
  thomPairSingularHomologyFinrankIsoOfCoherentFamily (o.coherentFamilyOfModel hι ω z hz)

variable {hz : Submodule.span K {z} = ⊤}

/-- Over a point where a linear trivialization `e` reads the orientation as `ω`, the isomorphism
`o.thomPairSingularHomologyFinrankIso hι ω z hz` sends the fibre class of the pull-back of `z`
along `e` to the class of the point. -/
theorem thomPairSingularHomologyFinrankIso_hom_apply_of_mapOrientation_eq
    (e : Trivialization F (π F E)) [e.IsLinear ℝ] {b : B} (hb : b ∈ e.baseSet)
    (he : e.mapOrientation ι hb (o b) = ω) :
    (o.thomPairSingularHomologyFinrankIso hι ω z hz).hom
        (TopPair.singularHomologyMap (fiberThomPairMap F E b) (ModuleCat.of K K) (finrank ℝ F)
          (TopPair.singularHomologyMap (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.inv
            (ModuleCat.of K K) (finrank ℝ F) z)) =
      singularHomology₀Section (ModuleCat.of K K) (X := TopCat.of B) b 1 := by
  classical
  have h : TopPair.singularHomologyMap (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.inv
      (ModuleCat.of K K) (finrank ℝ F) z = o.fiberGeneratorOfModel ω z b := by
    apply (ModuleCat.mono_iff_injective (TopPair.singularHomologyMap
      (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.hom (ModuleCat.of K K)
        (finrank ℝ F))).1 inferInstance
    rw [singularHomologyMap_complZeroPairIso_hom_fiberGeneratorOfModel hι e hb,
      ← ConcreteCategory.comp_apply, ← TopPair.singularHomologyMap_comp, Iso.inv_hom_id,
      TopPair.singularHomologyMap_id, ConcreteCategory.id_apply]
    simp [he]
  rw [h]
  exact thomPairSingularHomologyFinrankIsoOfCoherentFamily_hom_apply
    (G := o.coherentFamilyOfModel hι ω z hz) b

/-- Over a point where a linear trivialization `e` reads the orientation as `-ω`, the isomorphism
`o.thomPairSingularHomologyFinrankIso hι ω z hz` sends the fibre class of the pull-back of `z`
along `e` to the negative of the class of the point. -/
theorem thomPairSingularHomologyFinrankIso_hom_apply_of_mapOrientation_eq_neg
    (e : Trivialization F (π F E)) [e.IsLinear ℝ] {b : B} (hb : b ∈ e.baseSet)
    (he : e.mapOrientation ι hb (o b) = -ω) :
    (o.thomPairSingularHomologyFinrankIso hι ω z hz).hom
        (TopPair.singularHomologyMap (fiberThomPairMap F E b) (ModuleCat.of K K) (finrank ℝ F)
          (TopPair.singularHomologyMap (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.inv
            (ModuleCat.of K K) (finrank ℝ F) z)) =
      -singularHomology₀Section (ModuleCat.of K K) (X := TopCat.of B) b 1 := by
  classical
  have h : TopPair.singularHomologyMap (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.inv
      (ModuleCat.of K K) (finrank ℝ F) z = -o.fiberGeneratorOfModel ω z b := by
    apply (ModuleCat.mono_iff_injective (TopPair.singularHomologyMap
      (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.hom (ModuleCat.of K K)
        (finrank ℝ F))).1 inferInstance
    rw [map_neg, singularHomologyMap_complZeroPairIso_hom_fiberGeneratorOfModel hι e hb,
      ← ConcreteCategory.comp_apply, ← TopPair.singularHomologyMap_comp, Iso.inv_hom_id,
      TopPair.singularHomologyMap_id, ConcreteCategory.id_apply]
    simp [he, (Module.Ray.ne_neg_self ω).symm]
  rw [h, map_neg, map_neg]
  exact congrArg Neg.neg (thomPairSingularHomologyFinrankIsoOfCoherentFamily_hom_apply
    (G := o.coherentFamilyOfModel hι ω z hz) b)

end VectorBundleOrientation

end TauCeti
