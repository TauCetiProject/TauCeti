/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Exponential.Generation
public import TauCeti.Geometry.Lie.Exponential.Trotter
public import TauCeti.Algebra.Module.ZLattice.Circle
public import TauCeti.Topology.Algebra.Module.Submodule
import TauCeti.Topology.Algebra.Module.CompactQuotient
import Mathlib.Topology.Algebra.Group.Neighborhood
import TauCeti.Topology.Algebra.ContinuousMonoidHom.QuotientKerEquiv

/-!
# The exponential map of a commutative Lie group

For a commutative finite-dimensional real Lie group `G` the exponential map `lieExp : 𝔤 → G` is a
homomorphism from the additive group of the Lie algebra. Its image is the identity component of
`G`; when `G` is preconnected, `lieExp` is surjective. Its kernel is a discrete subgroup of `𝔤`.

The exponential of a commutative `G` is moreover an open map, so for a preconnected `G` it
identifies `G` with the quotient of `𝔤` by the kernel as topological groups. When `G` is compact
the quotient of `𝔤` by the kernel is the identity component, hence compact, so the kernel spans
`𝔤` and is a lattice of full rank: a compact connected commutative Lie group is the quotient of
its Lie algebra by a lattice. A `ℤ`-basis of that lattice is a real basis of `𝔤`, and the circle
coordinates `X ↦ (exp (2πi bᵢ*(X)))ᵢ` it defines (`Module.Basis.circleExp`) have exactly the
lattice as kernel, so they identify the group with the product `(Circle)^r`, `r = dim G`.

## Main results

* `TauCeti.lieExp_add`: the exponential of a commutative Lie group is a homomorphism.
* `TauCeti.lieExpAddMonoidHom`: that homomorphism, bundled.
* `TauCeti.range_lieExp`: the exponential image is the identity component.
* `TauCeti.lieExp_surjective_of_preconnectedSpace`: the exponential of a preconnected
  commutative Lie group is surjective.
* `TauCeti.discreteTopology_ker_lieExpAddMonoidHom`: the kernel of the exponential is discrete.
* `TauCeti.isOpenMap_lieExpAddMonoidHom` and `TauCeti.isOpenMap_lieExp`: the exponential of a
  commutative Lie group is an open map.
* `TauCeti.lieExpAddMonoidHom_surjective_of_preconnectedSpace`: the exponential homomorphism of
  a preconnected commutative Lie group is surjective.
* `TauCeti.lieExpQuotientKerContinuousAddEquiv`: a preconnected commutative Lie group is the
  quotient of its Lie algebra by the kernel of the exponential, as topological groups.
* `TauCeti.compactSpace_quotient_ker_lieExpAddMonoidHom`: for a compact commutative Lie group
  the quotient of the Lie algebra by the kernel of the exponential is compact.
* `TauCeti.span_ker_lieExpAddMonoidHom_eq_top`, `TauCeti.isZLattice_ker_lieExpAddMonoidHom` and
  `TauCeti.finrank_ker_lieExpAddMonoidHom`: for a compact commutative Lie group the kernel of the
  exponential is a lattice of full rank in the Lie algebra.
* `TauCeti.continuousMulEquivPiCircle` and `TauCeti.continuousMulEquivPiCircle_lieExp`: a
  `ℤ`-basis of the kernel of the exponential identifies a compact connected commutative Lie group
  with a product of circles, as topological groups, through the circle coordinates of the basis.
* `TauCeti.nonempty_continuousMulEquiv_pi_circle`: a compact connected commutative Lie group of
  dimension `r` is isomorphic to `(Circle)^r` as a topological group.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 20
  (The Exponential Map), § One-Parameter Subgroups and the Exponential Map.
* T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*, Springer GTM 98 (1985),
  Chapter I, § 3 (The Exponential Map), Theorem (3.6) and Lemma (3.8).
* D. Bump, *Lie Groups*, 2nd ed., Springer GTM 225 (2013), Chapter 15 (Tori), Proposition 15.3.
-/

public section

noncomputable section

namespace TauCeti

open Filter Set
open scoped ContDiff Manifold Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [FiniteDimensional ℝ E] [LieGroup I ∞ G] [T2Space G] [BoundarylessManifold I G]

attribute [local instance] LieGroup.minSmoothnessThree

variable [IsMulCommutative G]

/-- **The exponential of a commutative Lie group is a homomorphism** from the additive group of
the Lie algebra. -/
@[simp]
theorem lieExp_add (X Y : LeftInvariantDerivation I G) :
    lieExp (X + Y) = lieExp X * lieExp Y :=
  lieExp_add_of_commute (I := I) (G := G) fun _ => mul_comm' _ _

/-- The exponential of a commutative Lie group, as a homomorphism from the additive group of the
Lie algebra to the group written additively. -/
def lieExpAddMonoidHom : LeftInvariantDerivation I G →+ Additive G where
  toFun X := Additive.ofMul (lieExp X)
  map_zero' := by rw [lieExp_zero, ofMul_one]
  map_add' X Y := by rw [lieExp_add, ofMul_mul]

@[simp]
theorem lieExpAddMonoidHom_apply (X : LeftInvariantDerivation I G) :
    lieExpAddMonoidHom (I := I) (G := G) X = Additive.ofMul (lieExp X) := by
  rw [lieExpAddMonoidHom]
  rfl

/-- The exponential homomorphism is the exponential, viewed as a map into `Additive G`. -/
theorem coe_lieExpAddMonoidHom :
    ⇑(lieExpAddMonoidHom (I := I) (G := G)) = Additive.ofMul ∘ lieExp (I := I) :=
  funext fun X => lieExpAddMonoidHom_apply X

/-- Membership in the kernel of the exponential. -/
theorem mem_ker_lieExpAddMonoidHom {X : LeftInvariantDerivation I G} :
    X ∈ (lieExpAddMonoidHom (I := I) (G := G)).ker ↔ lieExp X = 1 := by
  -- Not a `simp` lemma: `simp` already proves it from `AddMonoidHom.mem_ker`,
  -- `lieExpAddMonoidHom_apply` and `ofMul_eq_zero`, so the simpNF linter rejects the attribute.
  rw [AddMonoidHom.mem_ker, lieExpAddMonoidHom_apply, ofMul_eq_zero]

/-- **The kernel of the exponential of a commutative Lie group is a discrete subgroup** of the
Lie algebra. -/
instance discreteTopology_ker_lieExpAddMonoidHom :
    DiscreteTopology (lieExpAddMonoidHom (I := I) (G := G)).ker := by
  -- The exponential is injective near `0`, so `0` is isolated in the kernel.
  apply discreteTopology_of_isOpen_singleton_zero
  obtain ⟨U, hU, hUopen, h0⟩ :=
    eventually_nhds_iff.mp (eventually_lieLog_lieExp (I := I) (G := G))
  have hsingleton : ({0} : Set (lieExpAddMonoidHom (I := I) (G := G)).ker) =
      Subtype.val ⁻¹' U := by
    ext ⟨X, hX⟩
    rw [mem_ker_lieExpAddMonoidHom] at hX
    simp only [mem_singleton_iff, mem_preimage, Subtype.ext_iff, ZeroMemClass.coe_zero]
    exact ⟨fun h => by rw [h]; exact h0, fun h => by rw [← hU X h, hX, lieLog_one]⟩
  rw [hsingleton]
  exact hUopen.preimage continuous_subtype_val

/-- The exponential homomorphism is continuous. -/
@[fun_prop]
theorem continuous_lieExpAddMonoidHom : Continuous (lieExpAddMonoidHom (I := I) (G := G)) :=
  continuous_ofMul.comp (contMDiff_lieExp (I := I) (G := G)).continuous

variable [IsTopologicalGroup G]

/-- **The exponential homomorphism of a commutative Lie group is an open map.** -/
theorem isOpenMap_lieExpAddMonoidHom : IsOpenMap (lieExpAddMonoidHom (I := I) (G := G)) := by
  -- A homomorphism of topological groups is open as soon as it is open at the identity, and near
  -- the identity the logarithm is a continuous right inverse of the exponential.
  rw [IsTopologicalAddGroup.isOpenMap_iff_nhds_zero]
  intro s hs
  rw [Filter.mem_map] at hs
  have hlog : ContinuousAt (lieLog (I := I) (G := G) ∘ Additive.toMul) (0 : Additive G) :=
    (contMDiffAt_lieLog_one (I := I) (G := G)).continuousAt.comp_of_eq
      continuous_toMul.continuousAt toMul_zero
  filter_upwards [hlog.preimage_mem_nhds
      (by simpa only [Function.comp_apply, toMul_zero, lieLog_one] using hs),
    continuous_toMul.continuousAt.eventually (eventually_lieExp_lieLog (I := I) (G := G))]
    with g hg hexp
  simp only [Set.mem_preimage, Function.comp_apply, lieExpAddMonoidHom_apply, hexp, ofMul_toMul]
    at hg
  exact hg

/-- **The exponential of a commutative Lie group is an open map.** -/
theorem isOpenMap_lieExp : IsOpenMap (lieExp (I := I) (G := G)) := by
  have hopen := isOpenMap_lieExpAddMonoidHom (I := I) (G := G)
  rw [coe_lieExpAddMonoidHom] at hopen
  exact isOpenMap_toMul.comp hopen

/-- **The exponential image of a commutative Lie group is the identity component.** -/
theorem range_lieExp :
    range (lieExp (I := I) (G := G)) = (Subgroup.connectedComponentOfOne G : Set G) := by
  -- The image is the range of the homomorphism `lieExp`, hence a subgroup; it contains a
  -- neighbourhood of the identity, so it is the identity component, which is the subgroup
  -- generated by the exponential image.
  let M : Multiplicative (LeftInvariantDerivation I G) →* G :=
    AddMonoidHom.toMultiplicativeLeft (lieExpAddMonoidHom (I := I) (G := G))
  have hrange : (M.range : Set G) = range (lieExp (I := I) (G := G)) := by
    ext g
    simp only [M, MonoidHom.coe_range, AddMonoidHom.coe_toMultiplicativeLeft, mem_range,
      Function.comp_apply, lieExpAddMonoidHom_apply (I := I) (G := G), toMul_ofMul]
    exact ⟨fun ⟨X, hX⟩ => ⟨Multiplicative.toAdd X, hX⟩,
      fun ⟨X, hX⟩ => ⟨Multiplicative.ofAdd X, hX⟩⟩
  rw [← closure_range_lieExp_eq_connectedComponentOfOne (I := I) (G := G), ← hrange,
    Subgroup.closure_eq]

/-- **The exponential of a preconnected commutative Lie group is surjective.** -/
theorem lieExp_surjective_of_preconnectedSpace [PreconnectedSpace G] :
    Function.Surjective (lieExp (I := I) (G := G)) := by
  rw [← range_eq_univ, range_lieExp, Subgroup.connectedComponentOfOne_eq_top, Subgroup.coe_top]


/-! ### The exponential as a quotient map, and the lattice of a compact group -/

/-- The Lie algebra is finite-dimensional; a local instance for the rest of this file. -/
noncomputable local instance : FiniteDimensional ℝ (LeftInvariantDerivation I G) :=
  finiteDimensional_leftInvariantDerivation
    (ContMDiffMul.isInteriorPoint (I := I) (n := ∞) (by simp) (1 : G))

section Preconnected

variable [PreconnectedSpace G]

/-- **The exponential homomorphism of a preconnected commutative Lie group is surjective.** -/
theorem lieExpAddMonoidHom_surjective_of_preconnectedSpace :
    Function.Surjective (lieExpAddMonoidHom (I := I) (G := G)) := fun g =>
  (lieExp_surjective_of_preconnectedSpace (I := I) (G := G) (Additive.toMul g)).imp
    fun X hX => by rw [lieExpAddMonoidHom_apply, hX, ofMul_toMul]

/-- **A preconnected commutative Lie group is the quotient of its Lie algebra by the kernel of the
exponential**, as topological groups: the first isomorphism theorem for the open surjective
homomorphism `lieExpAddMonoidHom`. -/
def lieExpQuotientKerContinuousAddEquiv :
    (LeftInvariantDerivation I G ⧸ (lieExpAddMonoidHom (I := I) (G := G)).ker) ≃ₜ+ Additive G :=
  ContinuousAddEquiv.quotientKerEquivOfSurjective _
    ((isOpenMap_lieExpAddMonoidHom (I := I) (G := G)).isStrictMap
      (continuous_lieExpAddMonoidHom (I := I) (G := G)))
    (lieExpAddMonoidHom_surjective_of_preconnectedSpace (I := I) (G := G))

@[simp]
theorem lieExpQuotientKerContinuousAddEquiv_apply (X : LeftInvariantDerivation I G) :
    lieExpQuotientKerContinuousAddEquiv (I := I) (G := G) (QuotientAddGroup.mk X) =
      Additive.ofMul (lieExp (I := I) X) := by
  rw [lieExpQuotientKerContinuousAddEquiv,
    ContinuousAddEquiv.quotientKerEquivOfSurjective_apply_mk, lieExpAddMonoidHom_apply]

@[simp]
theorem lieExpQuotientKerContinuousAddEquiv_symm_apply (X : LeftInvariantDerivation I G) :
    (lieExpQuotientKerContinuousAddEquiv (I := I) (G := G)).symm
      (Additive.ofMul (lieExp (I := I) X)) = QuotientAddGroup.mk X := by
  rw [← lieExpQuotientKerContinuousAddEquiv_apply, ContinuousAddEquiv.symm_apply_apply]

end Preconnected

section Compact

variable [CompactSpace G]

/-- **The Lie algebra modulo the kernel of the exponential is compact** when the group is: it is
the identity component, which is closed. -/
instance compactSpace_quotient_ker_lieExpAddMonoidHom :
    CompactSpace (LeftInvariantDerivation I G ⧸ (lieExpAddMonoidHom (I := I) (G := G)).ker) := by
  -- The quotient is the range of the exponential homomorphism, as the exponential is strict.
  have hcompact : IsCompact (Set.range (lieExpAddMonoidHom (I := I) (G := G))) := by
    rw [coe_lieExpAddMonoidHom, Set.range_comp, range_lieExp, Equiv.image_eq_preimage_symm,
      Additive.ofMul_symm_eq]
    exact (isClosed_connectedComponent.preimage continuous_toMul).isCompact
  rw [← AddMonoidHom.coe_range, isCompact_iff_compactSpace] at hcompact
  exact (ContinuousAddEquiv.quotientKerEquivRange
    ((isOpenMap_lieExpAddMonoidHom (I := I) (G := G)).isStrictMap
      continuous_lieExpAddMonoidHom)).symm.toHomeomorph.compactSpace

/-- **The kernel of the exponential of a compact commutative Lie group spans the Lie
algebra.** -/
theorem span_ker_lieExpAddMonoidHom_eq_top :
    Submodule.span ℝ
      ((lieExpAddMonoidHom (I := I) (G := G)).ker : Set (LeftInvariantDerivation I G)) = ⊤ :=
  AddSubgroup.span_eq_top_of_compactSpace_quotient _

/-- **The kernel of the exponential of a compact commutative Lie group is a lattice**
in the Lie algebra. -/
instance isZLattice_ker_lieExpAddMonoidHom :
    IsZLattice ℝ (lieExpAddMonoidHom (I := I) (G := G)).ker.toIntSubmodule where
  span_top := by
    rw [AddSubgroup.coe_toIntSubmodule]
    exact span_ker_lieExpAddMonoidHom_eq_top (I := I) (G := G)

/-- The rank of the kernel of the exponential is the dimension of the group. -/
theorem finrank_ker_lieExpAddMonoidHom :
    Module.finrank ℤ (lieExpAddMonoidHom (I := I) (G := G)).ker.toIntSubmodule =
      Module.finrank ℝ (LeftInvariantDerivation I G) :=
  ZLattice.rank ℝ _

end Compact

/-! ### Compact connected commutative Lie groups are products of circles -/

section Circle

variable [CompactSpace G] {ι : Type*}
  (b : Module.Basis ι ℤ (lieExpAddMonoidHom (I := I) (G := G)).ker.toIntSubmodule)

/-- The kernel of the circle coordinates of a `ℤ`-basis of the exponential kernel is that
kernel. -/
private theorem ker_circleExp_ofZLatticeBasis_lieExp :
    (b.ofZLatticeBasis ℝ _).circleExp.ker = (lieExpAddMonoidHom (I := I) (G := G)).ker := by
  rw [Module.Basis.ker_circleExp_ofZLatticeBasis, AddSubgroup.toIntSubmodule_toAddSubgroup]

/-- The circle coordinates of a `ℤ`-basis of the exponential kernel, descended to the quotient of
the Lie algebra by that kernel. -/
private def quotientCircleExp :
    LeftInvariantDerivation I G ⧸ (lieExpAddMonoidHom (I := I) (G := G)).ker →+
      Additive (ι → Circle) :=
  QuotientAddGroup.lift _ (b.ofZLatticeBasis ℝ _).circleExp
    (ker_circleExp_ofZLatticeBasis_lieExp b).ge

private theorem quotientCircleExp_mk (X : LeftInvariantDerivation I G) :
    quotientCircleExp b (QuotientAddGroup.mk X) = (b.ofZLatticeBasis ℝ _).circleExp X := by
  rw [quotientCircleExp, QuotientAddGroup.lift_mk]

private theorem bijective_quotientCircleExp : Function.Bijective (quotientCircleExp b) := by
  have : Finite ι := Module.Finite.finite_basis b
  refine ⟨(injective_iff_map_eq_zero _).mpr fun q hq => ?_, fun z => ?_⟩
  · induction q using QuotientAddGroup.induction_on with | H X => ?_
    rw [quotientCircleExp_mk, ← AddMonoidHom.mem_ker, ker_circleExp_ofZLatticeBasis_lieExp] at hq
    exact (QuotientAddGroup.eq_zero_iff X).mpr hq
  · obtain ⟨X, rfl⟩ := (b.ofZLatticeBasis ℝ _).circleExp_surjective z
    exact ⟨QuotientAddGroup.mk X, quotientCircleExp_mk b X⟩

/-- The circle coordinates on the quotient of the Lie algebra by the exponential kernel, as a
homeomorphism onto the product of circles: a continuous bijection out of a compact space. -/
private def quotientHomeomorphPiCircle :
    LeftInvariantDerivation I G ⧸ (lieExpAddMonoidHom (I := I) (G := G)).ker ≃ₜ (ι → Circle) :=
  have : Finite ι := Module.Finite.finite_basis b
  Continuous.homeoOfEquivCompactToT2
    (f := (Equiv.ofBijective _ (bijective_quotientCircleExp b)).trans Additive.toMul) <| by
    refine (QuotientAddGroup.isQuotientMap_mk _).continuous_iff.mpr ?_
    have hcomp : (fun X : LeftInvariantDerivation I G =>
        Additive.toMul (quotientCircleExp b (QuotientAddGroup.mk X))) =
        Additive.toMul ∘ (b.ofZLatticeBasis ℝ _).circleExp :=
      funext fun X => by rw [quotientCircleExp_mk, Function.comp_apply]
    exact hcomp ▸ continuous_toMul.comp (b.ofZLatticeBasis ℝ _).continuous_circleExp

private theorem quotientHomeomorphPiCircle_apply
    (q : LeftInvariantDerivation I G ⧸ (lieExpAddMonoidHom (I := I) (G := G)).ker) :
    quotientHomeomorphPiCircle b q = Additive.toMul (quotientCircleExp b q) :=
  -- `Continuous.homeoOfEquivCompactToT2` keeps the underlying equivalence, which is this map.
  rfl

variable [PreconnectedSpace G]

/-- **A compact connected commutative Lie group is a product of circles.** A `ℤ`-basis `b` of the
kernel of the exponential, which is a lattice of full rank in the Lie algebra, is a real basis of
the Lie algebra, and its circle coordinates `lieExp X ↦ (exp (2πi bᵢ*(X)))ᵢ` are a well-defined
isomorphism of topological groups `G ≃ₜ* (ι → Circle)`. -/
def continuousMulEquivPiCircle : G ≃ₜ* (ι → Circle) where
  toFun g := quotientHomeomorphPiCircle b
    ((lieExpQuotientKerContinuousAddEquiv (I := I) (G := G)).symm (Additive.ofMul g))
  invFun z := Additive.toMul
    (lieExpQuotientKerContinuousAddEquiv (I := I) (G := G) ((quotientHomeomorphPiCircle b).symm z))
  left_inv g := by
    simp only [Homeomorph.symm_apply_apply, ContinuousAddEquiv.apply_symm_apply, toMul_ofMul]
  right_inv z := by
    simp only [ofMul_toMul, ContinuousAddEquiv.symm_apply_apply, Homeomorph.apply_symm_apply]
  map_mul' g h := by
    simp only [ofMul_mul, map_add, quotientHomeomorphPiCircle_apply, toMul_add]
  continuous_toFun := (quotientHomeomorphPiCircle b).continuous.comp
    ((lieExpQuotientKerContinuousAddEquiv (I := I) (G := G)).symm.continuous.comp continuous_ofMul)
  continuous_invFun := continuous_toMul.comp
    ((lieExpQuotientKerContinuousAddEquiv (I := I) (G := G)).continuous.comp
      (quotientHomeomorphPiCircle b).symm.continuous)

/-- The circle coordinates of `lieExp X` are `exp (2πi bᵢ*(X))`, the coordinates `bᵢ*` taken in
the real basis of the Lie algebra given by `b`. -/
@[simp]
theorem continuousMulEquivPiCircle_lieExp (X : LeftInvariantDerivation I G) :
    continuousMulEquivPiCircle b (lieExp X) =
      fun i => Circle.exp (2 * Real.pi * (b.ofZLatticeBasis ℝ _).repr X i) := by
  simp only [continuousMulEquivPiCircle, ContinuousMulEquiv.coe_mk, MulEquiv.coe_mk,
    Equiv.coe_fn_mk, lieExpQuotientKerContinuousAddEquiv_symm_apply,
    quotientHomeomorphPiCircle_apply, quotientCircleExp_mk, Module.Basis.circleExp_apply,
    toMul_ofMul]

variable (I) in
include I in
/-- **A compact connected commutative Lie group of dimension `r` is the torus `(Circle)^r`**, as a
topological group. -/
theorem nonempty_continuousMulEquiv_pi_circle :
    Nonempty (G ≃ₜ* (Fin (Module.finrank ℝ E) → Circle)) := by
  have := ZLattice.module_free ℝ (lieExpAddMonoidHom (I := I) (G := G)).ker.toIntSubmodule
  have := ZLattice.module_finite ℝ (lieExpAddMonoidHom (I := I) (G := G)).ker.toIntSubmodule
  exact ⟨continuousMulEquivPiCircle (Module.finBasisOfFinrankEq ℤ _
    ((finrank_ker_lieExpAddMonoidHom (I := I) (G := G)).trans
      (finrank_leftInvariantDerivation_eq_modelVectorSpace
        (ContMDiffMul.isInteriorPoint (I := I) (n := ∞) (by simp) (1 : G)))))⟩

end Circle

end TauCeti
