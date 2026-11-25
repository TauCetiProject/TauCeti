/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.MayerVietoris.Descent
public import TauCeti.Topology.VectorBundle.Orientation.LocalSystem
public import TauCeti.AlgebraicTopology.Singular.Twisted.Zero
import TauCeti.Topology.Connected.PathConnected
import TauCeti.Topology.VectorBundle.Orientation.ThomClass
import TauCeti.Topology.Homotopy.Monodromy.Basic

/-!
# The rank-degree homology of a Thom pair and the orientation local system

Let `E → B` be a real vector bundle of rank `r` with Thom pair `(E, E₀)`, `E₀` the complement of
the zero section. This file identifies the first relative homology group of the Thom pair that can
be nonzero with the zeroth homology of the base twisted by the orientation local system `o(E)`
(`TauCeti.VectorBundleOrientationCover.signLocalSystem`), for any ring `K`:

`Hᵣ(E, E₀; K) ≅ H₀(B; o(E) ⊗ K)`

(`TauCeti.VectorBundleOrientationCover.thomPairSingularHomologyIsoTwistedHomology₀`). This is the
bottom degree of the Thom isomorphism with twisted coefficients, `Hⱼ(E, E₀; K) ≅ Hⱼ₋ᵣ(B; o(E))`;
all degrees are `TauCeti.VectorBundleOrientationCover.thomPairSingularHomologyEquivTwistedHomology`
when `2` is invertible in a commutative ring `K`. No orientation of the bundle and no condition on
the base are needed, and the rank may be zero. An orientation of the bundle trivializes `o(E)`
(`TauCeti.VectorBundleOrientation.signLocalSystemIso`), which turns the right-hand side into
`H₀(B; K)`. Without one the twist matters: over a path-connected, locally path-connected base,
`H₀(B; o(E))` with integral coefficients is `ℤ` for an orientable bundle and `ℤ/2` for a
nonorientable one, such as the Möbius line over the circle. When `2 = 0` in `K`, as for `ZMod 2`,
the twist disappears (`TauCeti.VectorBundleOrientationCover.signLocalSystemIsoOfTwoEqZero`); for
commutative rings whose only unit is `1` the untwisted form is
`TauCeti.thomPairSingularHomologyFinrankIso`. With coefficients `ModuleCat.of K K` for a ring `K`
in the universe of the base and `ι : Type`, the same group is
`TauCeti.thomPairSingularHomologyFinrankIsoTwistedHomology`, described by the generators
`TauCeti.orientedFiberGenerator` of the orientations of the fibres. Across a critical level of a
Morse–Bott function the relative homology of the sublevels is that of the Thom pair of the negative
normal bundle, so its lowest group is the zeroth homology of the critical submanifold twisted by the
orientation of the negative normal bundle.

The coefficients are `ModuleCat.of K (ULift K)`, lifted to the universe of the fibres of `o(E)`, so
`K` and the index type `ι` of orientations may live in any universe; for `K = ℤ` and `ι = Fin r`
these are the integral coefficients `ModuleCat.of ℤ (ULift ℤ)` of singular homology.

## The identification on the fibres

The fibre of `o(E)` over `b` consists of the functions `φ` on the two orientations of `E_b` with
`φ (-ω) = -φ ω`, and `Hᵣ(E_b, E_b ∖ {0}; K)` is a free `K`-module of rank one. Fix an orientation
`ωF` of the model fibre `F` and the point class `K ≅ Hᵣ(F, F ∖ {0}; K)`
(`TauCeti.complZeroPairPointHom`). A linear trivialization `e` at `b` identifies `E_b` with `F`,
and so identifies the fibre of `o(E)`, by evaluation at the orientation that `e` reads as `ωF`, and
`Hᵣ(E_b, E_b ∖ {0}; K)` with `K`. This identification does not depend on `e`
(`TauCeti.VectorBundleOrientationCover.signLocalSystemFiberIsoSingularHomology_hom`): another
trivialization changes both identifications by the sign of the determinant of the coordinate
change, since a linear automorphism acts on `Hᵣ(F, F ∖ {0})` by the sign of its determinant
(`TauCeti.singularHomologyMap_continuousLinearMap_compl_zero`; for the fibre maps of two
trivializations, `singularHomologyMap_complZeroPairIso_inv_eq_of_mapOrientation_eq` and its `_neg`
variant in `Bundle.Trivialization`). The only remaining choice is `ωF`, and `-ωF` gives the
opposite identification
(`TauCeti.VectorBundleOrientationCover.signLocalSystemFiberIsoSingularHomology_neg_hom`).

## The proof

The identifications on the fibres followed by the inclusions of the fibre pairs form a cocone from
`o(E)` to `Hᵣ(E, E₀; K)` (`TauCeti.VectorBundleOrientationCover.thomPairSingularHomologyCocone`):
the class of an orientation `ω` of a fibre, the image of the function with value `1` at `ω`, is
constant along paths in the orientation double cover, because inside a sheet of a trivialization it
is the image of a fixed class of `Hᵣ(F, F ∖ {0})` under fibre inclusions that induce the same map
on relative singular homology along paths in the base set (in `Bundle.Trivialization`,
`singularHomologyMap_complZeroPairIso_inv_comp_fiberThomPairOverMap_eq_of_joinedIn`), and
transport in `o(E)` follows lifts of paths to the cover. This cocone is a colimit
(`TauCeti.VectorBundleOrientationCover.isColimitThomPairSingularHomologyCocone`): a cocone with
point `T` gives morphisms `Hᵣ(E_b, E_b ∖ {0}; K) ⟶ T` that are constant along paths when read in a
trivialization, because the orientations read as `ωF` form a section of the double cover over its
base set, which lifts paths
(`TauCeti.VectorBundleOrientationCover.signLocalSystem_map_mk_signLocalSystemFiberEquiv_symm`); such
morphisms factor uniquely through `Hᵣ(E, E₀; K)`
(`TauCeti.existsUnique_singularHomology_thomPair_fac`). Zeroth homology with local coefficients is
also the colimit of the local system
(`TauCeti.LocalCoefficientSystem.isColimitTwistedHomology₀Cocone`), and the two colimits are
isomorphic.

## Main definitions and results

* `TauCeti.VectorBundleOrientationCover.signLocalSystemFiberIsoSingularHomology`: the
  identification of the fibre of `o(E)` over `b` with `Hᵣ(E_b, E_b ∖ {0}; K)`, read in any linear
  trivialization at `b` (`signLocalSystemFiberIsoSingularHomology_hom` and
  `signLocalSystemFiberIsoSingularHomology_inv`).
* `TauCeti.VectorBundleOrientationCover.thomPairSingularHomologyCocone`,
  `TauCeti.VectorBundleOrientationCover.isColimitThomPairSingularHomologyCocone`: `Hᵣ(E, E₀; K)` is
  the colimit of `o(E)` over the fundamental groupoid of the base.
* `TauCeti.VectorBundleOrientationCover.thomPairSingularHomologyIsoTwistedHomology₀`:
  `Hᵣ(E, E₀; K) ≅ H₀(B; o(E))`, with its values on the fibre classes and on the classes of
  coefficients at points, in the namespace `TauCeti.VectorBundleOrientationCover`:
  `singularHomologyMap_fiberThomPairMap_thomPairSingularHomologyIsoTwistedHomology₀_hom` and
  `ιTwistedHomology₀_thomPairSingularHomologyIsoTwistedHomology₀_inv`; reversing `ωF` negates it
  (`thomPairSingularHomologyIsoTwistedHomology₀_neg_hom`).

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10 and §12 (the Thom isomorphism and the orientation double cover).
* A. Hatcher, *Algebraic Topology*, Section 3.H (local coefficients and the orientation system) and
  Section 4.D, Theorem 4D.10 (the Thom isomorphism).
* E. H. Spanier, *Algebraic Topology*, Chapter 5, Section 7.
-/

public noncomputable section

open Bundle CategoryTheory Limits Set Module AlgebraicTopology Topology

universe u uι w

namespace TauCeti

namespace VectorBundleOrientationCover

variable (K : Type u) [Ring K] {B : Type w} [TopologicalSpace B] {F : Type w}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {E : B → Type w}
  [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)]
  [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]
  {ι : Type uι} [Fintype ι] (hι : Fintype.card ι = finrank ℝ F) (ωF : Orientation ℝ F ι)

/-- The identification of the fibre of `o(E)` over `b` with `Hᵣ(E_b, E_b ∖ {0}; K)` read in a
linear trivialization `e`: evaluate at the orientation of `E_b` that `e` reads as `ωF`, then carry
the point class `K ≅ Hᵣ(F, F ∖ {0}; K)` to the fibre by `e`. -/
private def fiberIsoAt (e : Trivialization F (π F E)) [e.IsLinear ℝ] {b : B}
    (hb : b ∈ e.baseSet) :
    (signLocalSystem F E K hι).obj (FundamentalGroupoid.mk b) ≅
      (TopPair.ofSubset (X := TopCat.of (E b)) ({0}ᶜ : Set (E b))).singularHomology
        (ModuleCat.of K (ULift.{max w uι} K)) (finrank ℝ F) :=
  (signLocalSystemFiberEquiv hι ((e.mapOrientation ι hb).symm ωF) ≪≫ₗ
      ULift.moduleEquiv.{u, u, max w uι}.symm).toModuleIso ≪≫
    asIso (complZeroPairPointHom (ModuleCat.of K (ULift.{max w uι} K)) F (finrank ℝ F) rfl) ≪≫
      TopPair.singularHomologyMapIso _ (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.symm _

private theorem fiberIsoAt_hom (e : Trivialization F (π F E)) [e.IsLinear ℝ] {b : B}
    (hb : b ∈ e.baseSet) :
    (fiberIsoAt K hι ωF e hb).hom =
      ModuleCat.ofHom (signLocalSystemFiberEquiv hι ((e.mapOrientation ι hb).symm ωF) ≪≫ₗ
          ULift.moduleEquiv.{u, u, max w uι}.symm).toLinearMap ≫
        complZeroPairPointHom (ModuleCat.of K (ULift.{max w uι} K)) F (finrank ℝ F) rfl ≫
          TopPair.singularHomologyMap (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.inv
            (ModuleCat.of K (ULift.{max w uι} K)) (finrank ℝ F) :=
  (rfl)

omit [FiniteDimensional ℝ F] in
/-- Evaluation at the opposite orientation, read in the lifted coefficients, is the negative of
evaluation at `o`. -/
private theorem ofHom_signLocalSystemFiberEquiv_neg_trans {b : B} (o : Orientation ℝ (E b) ι) :
    ModuleCat.ofHom (signLocalSystemFiberEquiv (R := K) hι (-o) ≪≫ₗ
        ULift.moduleEquiv.{u, u, max w uι}.symm).toLinearMap =
      -ModuleCat.ofHom (signLocalSystemFiberEquiv hι o ≪≫ₗ
        ULift.moduleEquiv.{u, u, max w uι}.symm).toLinearMap := by
  refine ModuleCat.hom_ext (LinearMap.ext fun φ ↦ ?_)
  rw [ModuleCat.hom_neg, LinearMap.neg_apply, ModuleCat.hom_ofHom, ModuleCat.hom_ofHom,
    LinearEquiv.coe_coe, LinearEquiv.coe_coe, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    signLocalSystemFiberEquiv_neg, map_neg]

/-- **The identification does not depend on the trivialization.** Two linear trivializations
whose base sets contain `b` give the same identification of the fibre of `o(E)` over `b` with
`Hᵣ(E_b, E_b ∖ {0}; K)`. -/
private theorem fiberIsoAt_eq (e e' : Trivialization F (π F E)) [e.IsLinear ℝ] [e'.IsLinear ℝ]
    {b : B} (hb : b ∈ e.baseSet) (hb' : b ∈ e'.baseSet) :
    fiberIsoAt K hι ωF e hb = fiberIsoAt K hι ωF e' hb' := by
  ext : 1
  rw [fiberIsoAt_hom, fiberIsoAt_hom]
  -- Compare how `e'` reads the orientation `o` that `e` reads as `ωF`.
  set o := (e.mapOrientation ι hb).symm ωF
  have ho : e.mapOrientation ι hb o = ωF := Equiv.apply_symm_apply _ _
  rcases Orientation.eq_or_eq_neg (e'.mapOrientation ι hb' o) ωF
    (Nat.card_eq_fintype_card.trans hι) with h | h
  · rw [(Equiv.symm_apply_eq _).2 h.symm,
      e.singularHomologyMap_complZeroPairIso_inv_eq_of_mapOrientation_eq e' hb hb' hι _
        (h.trans ho.symm)]
  · rw [e'.mapOrientation_symm_eq_neg_of_eq_neg hb' h,
      e.singularHomologyMap_complZeroPairIso_inv_eq_neg_of_mapOrientation_eq_neg e' hb hb' hι _
        (by rw [h, ho]),
      ofHom_signLocalSystemFiberEquiv_neg_trans, Preadditive.neg_comp, Preadditive.comp_neg,
      Preadditive.comp_neg, neg_neg]

variable (E) in
/-- **The fibre of the orientation local system is the top local homology of the fibre.** The
fibre of the orientation local system `o(E)` over `b` is identified with `Hᵣ(E_b, E_b ∖ {0}; K)`:
in any linear trivialization `e` at `b`, evaluate at the orientation of `E_b` that `e` reads as
`ωF`, then carry the point class `K ≅ Hᵣ(F, F ∖ {0}; K)` to the fibre by `e`
(`TauCeti.VectorBundleOrientationCover.signLocalSystemFiberIsoSingularHomology_hom`). The result
does not depend on `e`. -/
def signLocalSystemFiberIsoSingularHomology (b : B) :
    (signLocalSystem F E K hι).obj (FundamentalGroupoid.mk b) ≅
      (TopPair.ofSubset (X := TopCat.of (E b)) ({0}ᶜ : Set (E b))).singularHomology
        (ModuleCat.of K (ULift.{max w uι} K)) (finrank ℝ F) :=
  fiberIsoAt K hι ωF (trivializationAt F E b) (FiberBundle.mem_baseSet_trivializationAt' b)

private theorem signLocalSystemFiberIsoSingularHomology_eq (e : Trivialization F (π F E))
    [e.IsLinear ℝ] {b : B} (hb : b ∈ e.baseSet) :
    signLocalSystemFiberIsoSingularHomology K E hι ωF b = fiberIsoAt K hι ωF e hb :=
  fiberIsoAt_eq K hι ωF _ e _ hb

/-- In any linear trivialization `e` at `b`, the identification evaluates at the orientation of
`E_b` that `e` reads as `ωF`, then carries the point class `K ≅ Hᵣ(F, F ∖ {0}; K)` to the fibre by
`e`. -/
theorem signLocalSystemFiberIsoSingularHomology_hom (e : Trivialization F (π F E)) [e.IsLinear ℝ]
    {b : B} (hb : b ∈ e.baseSet) :
    (signLocalSystemFiberIsoSingularHomology K E hι ωF b).hom =
      ModuleCat.ofHom (signLocalSystemFiberEquiv hι ((e.mapOrientation ι hb).symm ωF) ≪≫ₗ
          ULift.moduleEquiv.{u, u, max w uι}.symm).toLinearMap ≫
        complZeroPairPointHom (ModuleCat.of K (ULift.{max w uι} K)) F (finrank ℝ F) rfl ≫
          TopPair.singularHomologyMap (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.inv
            (ModuleCat.of K (ULift.{max w uι} K)) (finrank ℝ F) := by
  rw [signLocalSystemFiberIsoSingularHomology_eq K hι ωF e hb, fiberIsoAt_hom]

/-- In any linear trivialization `e` at `b`, the inverse identification carries the fibre to
`Hᵣ(F, F ∖ {0}; K)` by `e`, reads it in `K` through the point class, and takes the element of the
fibre of `o(E)` with that value at the orientation of `E_b` that `e` reads as `ωF`. -/
theorem signLocalSystemFiberIsoSingularHomology_inv (e : Trivialization F (π F E)) [e.IsLinear ℝ]
    {b : B} (hb : b ∈ e.baseSet) :
    (signLocalSystemFiberIsoSingularHomology K E hι ωF b).inv =
      TopPair.singularHomologyMap (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.hom
          (ModuleCat.of K (ULift.{max w uι} K)) (finrank ℝ F) ≫
        inv (complZeroPairPointHom (ModuleCat.of K (ULift.{max w uι} K)) F (finrank ℝ F) rfl) ≫
          ModuleCat.ofHom (ULift.moduleEquiv.{u, u, max w uι} ≪≫ₗ
            (signLocalSystemFiberEquiv hι ((e.mapOrientation ι hb).symm ωF)).symm).toLinearMap := by
  rw [signLocalSystemFiberIsoSingularHomology_eq K hι ωF e hb, fiberIsoAt, Iso.trans_inv,
    Iso.trans_inv, TopPair.singularHomologyMapIso_inv, Iso.symm_inv, asIso_inv,
    LinearEquiv.toModuleIso_inv, LinearEquiv.trans_symm, LinearEquiv.symm_symm, Category.assoc]

/-- Reversing the orientation `ωF` of the model fibre negates the identification. -/
@[simp]
theorem signLocalSystemFiberIsoSingularHomology_neg_hom (b : B) :
    (signLocalSystemFiberIsoSingularHomology K E hι (-ωF) b).hom =
      -(signLocalSystemFiberIsoSingularHomology K E hι ωF b).hom := by
  rw [signLocalSystemFiberIsoSingularHomology_hom K hι _ (trivializationAt F E b)
      (FiberBundle.mem_baseSet_trivializationAt' b),
    signLocalSystemFiberIsoSingularHomology_hom K hι _ (trivializationAt F E b)
      (FiberBundle.mem_baseSet_trivializationAt' b), Trivialization.mapOrientation_symm_neg,
    ofHom_signLocalSystemFiberEquiv_neg_trans, Preadditive.neg_comp]

/-- Reversing the orientation `ωF` of the model fibre negates the inverse identification. -/
@[simp]
theorem signLocalSystemFiberIsoSingularHomology_neg_inv (b : B) :
    (signLocalSystemFiberIsoSingularHomology K E hι (-ωF) b).inv =
      -(signLocalSystemFiberIsoSingularHomology K E hι ωF b).inv :=
  Iso.inv_ext (by simp)

/-! ### The cocone -/

variable (E) in
/-- The structure map at `b` of the cocone: the identification of the fibre of `o(E)` with
`Hᵣ(E_b, E_b ∖ {0}; K)` followed by the inclusion of the fibre pair. -/
private def leg (b : B) :
    (signLocalSystem F E K hι).obj (FundamentalGroupoid.mk b) ⟶
      (thomPair F E).singularHomology (ModuleCat.of K (ULift.{max w uι} K)) (finrank ℝ F) :=
  (signLocalSystemFiberIsoSingularHomology K E hι ωF b).hom ≫
    TopPair.singularHomologyMap (fiberThomPairMap F E b) (ModuleCat.of K (ULift.{max w uι} K))
      (finrank ℝ F)

/-- The class in `Hᵣ(E, E₀; K)` of a point `(b, ω)` of the orientation double cover: the image of
the function with value `1` at `ω`. -/
private def fiberClass (p : VectorBundleOrientationCover F E ι) :
    ((thomPair F E).singularHomology (ModuleCat.of K (ULift.{max w uι} K)) (finrank ℝ F) :
      ModuleCat K) :=
  (leg K E hι ωF p.proj).hom ((signLocalSystemFiberEquiv hι p.orientation).symm 1)

/-- The structure map at `b` evaluates at any orientation `o` of `E_b` and multiplies the class of
`(b, o)`. -/
private theorem leg_apply (b : B) (o : Orientation ℝ (E b) ι)
    (ψ : (signLocalSystem F E K hι).obj (FundamentalGroupoid.mk b)) :
    (leg K E hι ωF b).hom ψ = signLocalSystemFiberEquiv hι o ψ • fiberClass K hι ωF ⟨b, o⟩ := by
  have h : ψ = signLocalSystemFiberEquiv hι o ψ • (signLocalSystemFiberEquiv hι o).symm 1 := by
    rw [← map_smul, smul_eq_mul, mul_one, LinearEquiv.symm_apply_apply]
  conv_lhs => rw [h]
  rw [map_smul, fiberClass]

/-- The point class `K ≅ Hᵣ(F, F ∖ {0}; K)` carried into `Hᵣ(E, E₀; K)` by the fibre over `b` of
a linear trivialization. -/
private abbrev trivializationClass (e : Trivialization F (π F E)) [e.IsLinear ℝ] {b : B}
    (hb : b ∈ e.baseSet) :
    ((thomPair F E).singularHomology (ModuleCat.of K (ULift.{max w uι} K)) (finrank ℝ F) :
      ModuleCat K) :=
  (TopPair.singularHomologyMap ((e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.inv ≫
    fiberThomPairMap F E b) (ModuleCat.of K (ULift.{max w uι} K)) (finrank ℝ F)).hom
    (complZeroPairPointHom (ModuleCat.of K (ULift.{max w uι} K)) F (finrank ℝ F) rfl
      (ULift.up 1))

/-- In a trivialization reading the orientation of `p` as `ωF`, the class of `p` is the point
class carried by the trivialization. -/
private theorem fiberClass_of_eq (e : Trivialization F (π F E)) [e.IsLinear ℝ]
    {p : VectorBundleOrientationCover F E ι} (hp : p.proj ∈ e.baseSet)
    (ho : e.mapOrientation ι hp p.orientation = ωF) :
    fiberClass K hι ωF p = trivializationClass K e hp := by
  have hω : (e.mapOrientation ι hp).symm ωF = p.orientation := by
    rw [Equiv.symm_apply_eq, ho]
  rw [fiberClass, leg, signLocalSystemFiberIsoSingularHomology_hom K hι ωF e hp, hω,
    trivializationClass, TopPair.singularHomologyMap_comp]
  simp

/-- In a trivialization reading the orientation of `p` as `-ωF`, the class of `p` is minus the
point class carried by the trivialization. -/
private theorem fiberClass_of_eq_neg (e : Trivialization F (π F E)) [e.IsLinear ℝ]
    {p : VectorBundleOrientationCover F E ι} (hp : p.proj ∈ e.baseSet)
    (ho : e.mapOrientation ι hp p.orientation = -ωF) :
    fiberClass K hι ωF p = -trivializationClass K e hp := by
  rw [fiberClass, leg, signLocalSystemFiberIsoSingularHomology_hom K hι ωF e hp,
    e.mapOrientation_symm_eq_neg_of_eq_neg hp ho,
    ofHom_signLocalSystemFiberEquiv_neg_trans, Preadditive.neg_comp, trivializationClass,
    TopPair.singularHomologyMap_comp]
  simp

/-- **The class of an orientation is constant along paths in the orientation double cover.** -/
private theorem fiberClass_eq_of_joined {p q : VectorBundleOrientationCover F E ι}
    (hpq : Joined p q) : fiberClass K hι ωF p = fiberClass K hι ωF q := by
  obtain ⟨Γ⟩ := hpq
  -- Near each point `z`, take the sheet of the trivialization at `z.proj` containing `z`.
  refine Γ.eq_of_joinedIn_nhds (f := fiberClass K hι ωF) fun z ↦ ?_
  let e := trivializationAt F E z.proj
  have hz : z.proj ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' _
  let o := e.mapOrientation ι hz z.orientation
  refine ⟨sheet e o, (isOpen_sheet hι e o).mem_nhds (mem_sheet_iff.2 ⟨hz, rfl⟩), fun a b hj ↦ ?_⟩
  obtain ⟨ha, hao⟩ := mem_sheet_iff.1 hj.source_mem
  obtain ⟨hb, hbo⟩ := mem_sheet_iff.1 hj.target_mem
  -- Their base points are joined in the base set of `e`, where the fibre inclusions read
  -- through `e` induce the same map on homology.
  have hjb : JoinedIn (univ ∩ e.baseSet) a.proj b.proj :=
    (hj.map continuous_proj.continuousOn).mono (by
      rintro _ ⟨q, hq, rfl⟩
      exact ⟨trivial, (mem_sheet_iff.1 hq).1⟩)
  have hκ : (trivializationClass K e hb : ((thomPair F E).singularHomology
      (ModuleCat.of K (ULift.{max w uι} K)) (finrank ℝ F) : ModuleCat K)) =
        trivializationClass K e ha := by
    have h := e.singularHomologyMap_complZeroPairIso_inv_comp_fiberThomPairOverMap_eq_of_joinedIn
      (ModuleCat.of K (ULift.{max w uι} K)) hjb (finrank ℝ F) rfl
    have h' := congrArg (· ≫ TopPair.singularHomologyMap (thomPairOverUnivIso F E).hom
      (ModuleCat.of K (ULift.{max w uι} K)) (finrank ℝ F)) h
    simp only [← TopPair.singularHomologyMap_comp, Category.assoc,
      fiberThomPairOverMap_comp_thomPairOverUnivIso_hom] at h'
    rw [trivializationClass, trivializationClass, h']
  rcases Orientation.eq_or_eq_neg o ωF (Nat.card_eq_fintype_card.trans hι) with h | h
  · rw [fiberClass_of_eq K hι ωF e ha (hao.trans h), fiberClass_of_eq K hι ωF e hb (hbo.trans h),
      hκ]
  · rw [fiberClass_of_eq_neg K hι ωF e ha (hao.trans h),
      fiberClass_of_eq_neg K hι ωF e hb (hbo.trans h), hκ]

/-- **The fibre classes are compatible with transport in `o(E)`.** The identification of the
fibre of `o(E)` with `Hᵣ(E_b, E_b ∖ {0}; K)`, followed by the inclusion of the fibre pair, is
compatible with transport along paths in the base: the class of an orientation of a fibre is
constant along paths in the orientation double cover. -/
@[reassoc]
theorem signLocalSystem_map_comp_signLocalSystemFiberIsoSingularHomology_hom_comp_fiberThomPairMap
    {x y : FundamentalGroupoid (TopCat.of B)} (γ : x ⟶ y) :
    (signLocalSystem F E K hι).map γ ≫
        (signLocalSystemFiberIsoSingularHomology K E hι ωF y.as).hom ≫
          TopPair.singularHomologyMap (fiberThomPairMap F E y.as)
            (ModuleCat.of K (ULift.{max w uι} K)) (finrank ℝ F) =
      (signLocalSystemFiberIsoSingularHomology K E hι ωF x.as).hom ≫
        TopPair.singularHomologyMap (fiberThomPairMap F E x.as)
          (ModuleCat.of K (ULift.{max w uι} K)) (finrank ℝ F) := by
  rw [← leg, ← leg]
  -- Evaluate at an orientation `o` of `E_x` and at its monodromy `o'` over `y`.
  obtain ⟨o⟩ : Nonempty (Orientation ℝ (E x.as) ι) :=
    ⟨((trivializationAt F E x.as).mapOrientation ι
      (FiberBundle.mem_baseSet_trivializationAt' x.as)).symm ωF⟩
  let a : (proj ⁻¹' {x.as} : Set (VectorBundleOrientationCover F E ι)) := ⟨⟨x.as, o⟩, rfl⟩
  obtain ⟨⟨⟨y', o'⟩, hy'⟩, hm⟩ :
      ∃ m, (isCoveringMap_proj (F := F) (E := E) hι).monodromy γ a = m := ⟨_, rfl⟩
  obtain rfl : y' = y.as := hy'
  have hj : Joined (a : VectorBundleOrientationCover F E ι) ⟨y.as, o'⟩ := by
    simpa [hm] using (isCoveringMap_proj hι).joined_monodromy γ a
  ext φ
  rw [ModuleCat.hom_comp, LinearMap.comp_apply, leg_apply K hι ωF y.as o',
    leg_apply K hι ωF x.as o, signLocalSystemFiberEquiv_map hι γ hm,
    fiberClass_eq_of_joined K hι ωF hj]

variable (E) in
/-- **The cocone of fibre classes.** The identifications of the fibres of the orientation local
system `o(E)` with the groups `Hᵣ(E_b, E_b ∖ {0}; K)`
(`TauCeti.VectorBundleOrientationCover.signLocalSystemFiberIsoSingularHomology`), followed by the
inclusions of the fibre pairs, form a cocone from `o(E)` to `Hᵣ(E, E₀; K)`. -/
-- The cocone point must compute to the homology of the Thom pair in the signatures comparing the
-- structure maps with the fibre inclusions.
@[expose]
def thomPairSingularHomologyCocone : Cocone (signLocalSystem F E K hι) where
  pt := (thomPair F E).singularHomology (ModuleCat.of K (ULift.{max w uι} K)) (finrank ℝ F)
  ι :=
    { app x := (signLocalSystemFiberIsoSingularHomology K E hι ωF x.as).hom ≫
        TopPair.singularHomologyMap (fiberThomPairMap F E x.as)
          (ModuleCat.of K (ULift.{max w uι} K)) (finrank ℝ F)
      naturality _ _ γ :=
        (signLocalSystem_map_comp_signLocalSystemFiberIsoSingularHomology_hom_comp_fiberThomPairMap
          K hι ωF γ).trans (Category.comp_id _).symm }

variable (E) in
@[simp]
theorem thomPairSingularHomologyCocone_pt :
    (thomPairSingularHomologyCocone K E hι ωF).pt =
      (thomPair F E).singularHomology (ModuleCat.of K (ULift.{max w uι} K)) (finrank ℝ F) :=
  (rfl)

variable (E) in
/-- The structure map of the cocone at `x` is the identification of the fibre followed by the
inclusion of the fibre pair. -/
@[simp]
theorem thomPairSingularHomologyCocone_ι_app (x : FundamentalGroupoid (TopCat.of B)) :
    (thomPairSingularHomologyCocone K E hι ωF).ι.app x =
      (signLocalSystemFiberIsoSingularHomology K E hι ωF x.as).hom ≫
        TopPair.singularHomologyMap (fiberThomPairMap F E x.as)
          (ModuleCat.of K (ULift.{max w uι} K)) (finrank ℝ F) :=
  (rfl)

variable (E) in
/-- **`Hᵣ(E, E₀; K)` is the colimit of the orientation local system.** The cocone of fibre classes
(`TauCeti.VectorBundleOrientationCover.thomPairSingularHomologyCocone`) exhibits `Hᵣ(E, E₀; K)` as
the colimit of `o(E)` over the fundamental groupoid of the base. -/
def isColimitThomPairSingularHomologyCocone :
    IsColimit (thomPairSingularHomologyCocone K E hι ωF) :=
  IsColimit.ofExistsUnique fun s ↦ by
    -- The morphisms out of the fibre groups: read the fibre of `o(E)`, then map to `s`.
    let g (b : B) := (signLocalSystemFiberIsoSingularHomology K E hι ωF b).inv ≫
      s.ι.app (FundamentalGroupoid.mk b)
    obtain ⟨Φ, hΦ, hΦu⟩ := existsUnique_singularHomology_thomPair_fac g fun z x y hx hy hxy ↦ by
      obtain ⟨γ, hγ⟩ := hxy
      -- Read both fibres in the trivialization at `z`.
      set e := trivializationAt F E z
      have he (b : B) (hb : b ∈ e.baseSet) :
          TopPair.singularHomologyMap (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.inv
            (ModuleCat.of K (ULift.{max w uι} K)) (finrank ℝ F) ≫ g b =
          inv (complZeroPairPointHom (ModuleCat.of K (ULift.{max w uι} K)) F (finrank ℝ F) rfl) ≫
            ModuleCat.ofHom (ULift.moduleEquiv.{u, u, max w uι} ≪≫ₗ (signLocalSystemFiberEquiv hι
              ((e.mapOrientation ι hb).symm ωF)).symm).toLinearMap ≫
              s.ι.app (FundamentalGroupoid.mk b) := by
        simp only [g]
        rw [signLocalSystemFiberIsoSingularHomology_inv K hι ωF e hb]
        simp only [Category.assoc]
        rw [← TopPair.singularHomologyMap_comp_assoc, Iso.inv_hom_id,
          TopPair.singularHomologyMap_id, Category.id_comp]
      -- Transport along the path keeps the orientations read as `ωF`.
      have hmap : ModuleCat.ofHom (ULift.moduleEquiv.{u, u, max w uι} ≪≫ₗ
          (signLocalSystemFiberEquiv hι ((e.mapOrientation ι hx).symm ωF)).symm).toLinearMap ≫
            (signLocalSystem F E K hι).map
              (FundamentalGroupoid.fromPath (X := TopCat.of B) (Path.Homotopic.Quotient.mk γ)) =
          ModuleCat.ofHom (ULift.moduleEquiv.{u, u, max w uι} ≪≫ₗ (signLocalSystemFiberEquiv hι
            ((e.mapOrientation ι hy).symm ωF)).symm).toLinearMap := by
        ext r
        simpa using signLocalSystem_map_mk_signLocalSystemFiberEquiv_symm hι e ωF γ hγ hx hy
          (ULift.down r)
      rw [he x hx, he y hy,
        ← s.w (FundamentalGroupoid.fromPath (X := TopCat.of B) (Path.Homotopic.Quotient.mk γ)),
        reassoc_of% hmap]
    refine ⟨Φ, fun ⟨x⟩ ↦ ?_, fun Φ' hΦ' ↦ hΦu Φ' fun b ↦ ?_⟩
    -- The cocone point is `(thomPair F E).singularHomology _ _` only by unfolding the cocone
    -- (`thomPairSingularHomologyCocone_pt`), so neither `rw [Category.assoc]` nor `rw [hΦ]` can
    -- match the composites with `Φ`; these steps are applied as terms, which unify up to that
    -- unfolding.
    · rw [thomPairSingularHomologyCocone_ι_app]
      exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (hΦ x)).trans
        (Iso.hom_inv_id_assoc _ _))
    · rw [← cancel_epi (signLocalSystemFiberIsoSingularHomology K E hι ωF b).hom,
        Iso.hom_inv_id_assoc, ← hΦ' (FundamentalGroupoid.mk b),
        thomPairSingularHomologyCocone_ι_app]
      exact (Category.assoc _ _ _).symm

variable (E) in
/-- **The rank-degree homology of the Thom pair is the zeroth homology twisted by the orientation
local system.** For a real vector bundle `E → B` of rank `r` and a ring `K`,
`Hᵣ(E, E₀; K) ≅ H₀(B; o(E) ⊗ K)`, where `o(E)` is the orientation local system. The isomorphism
depends on an orientation `ωF` of the model fibre, through the identification of each fibre of
`o(E)` with `Hᵣ(E_b, E_b ∖ {0}; K)`
(`TauCeti.VectorBundleOrientationCover.signLocalSystemFiberIsoSingularHomology`); the opposite
orientation gives the opposite isomorphism
(`TauCeti.VectorBundleOrientationCover.thomPairSingularHomologyIsoTwistedHomology₀_neg_hom`). The
base is arbitrary and the bundle need not be orientable. -/
def thomPairSingularHomologyIsoTwistedHomology₀ :
    (thomPair F E).singularHomology (ModuleCat.of K (ULift.{max w uι} K)) (finrank ℝ F) ≅
      LocalCoefficientSystem.twistedHomology (signLocalSystem F E K hι) 0 :=
  (isColimitThomPairSingularHomologyCocone K E hι ωF).coconePointUniqueUpToIso
    (LocalCoefficientSystem.isColimitTwistedHomology₀Cocone _)

/-- **The isomorphism on the fibres.** The inclusion of the fibre pair over `b`, followed by
`Hᵣ(E, E₀; K) ≅ H₀(B; o(E))`, is the identification of `Hᵣ(E_b, E_b ∖ {0}; K)` with the fibre of
`o(E)` over `b`, followed by the class of a coefficient at `b` in twisted zeroth homology. -/
@[reassoc (attr := simp)]
theorem singularHomologyMap_fiberThomPairMap_thomPairSingularHomologyIsoTwistedHomology₀_hom
    (b : B) :
    TopPair.singularHomologyMap (fiberThomPairMap F E b) (ModuleCat.of K (ULift.{max w uι} K))
        (finrank ℝ F) ≫ (thomPairSingularHomologyIsoTwistedHomology₀ K E hι ωF).hom =
      (signLocalSystemFiberIsoSingularHomology K E hι ωF b).inv ≫
        LocalCoefficientSystem.ιTwistedHomology₀ (signLocalSystem F E K hι) b := by
  rw [Iso.eq_inv_comp, ← Category.assoc, ← thomPairSingularHomologyCocone_ι_app K E hι ωF
    (FundamentalGroupoid.mk b), thomPairSingularHomologyIsoTwistedHomology₀]
  exact (isColimitThomPairSingularHomologyCocone K E hι ωF).comp_coconePointUniqueUpToIso_hom
    (LocalCoefficientSystem.isColimitTwistedHomology₀Cocone _) (FundamentalGroupoid.mk b)

/-- The class of a coefficient at `b` in twisted zeroth homology corresponds, under
`H₀(B; o(E)) ≅ Hᵣ(E, E₀; K)`, to its image in `Hᵣ(E_b, E_b ∖ {0}; K)` followed by the inclusion of
the fibre pair. -/
@[reassoc (attr := simp)]
theorem ιTwistedHomology₀_thomPairSingularHomologyIsoTwistedHomology₀_inv (b : B) :
    LocalCoefficientSystem.ιTwistedHomology₀ (signLocalSystem F E K hι) b ≫
        (thomPairSingularHomologyIsoTwistedHomology₀ K E hι ωF).inv =
      (signLocalSystemFiberIsoSingularHomology K E hι ωF b).hom ≫
        TopPair.singularHomologyMap (fiberThomPairMap F E b)
          (ModuleCat.of K (ULift.{max w uι} K)) (finrank ℝ F) := by
  rw [← thomPairSingularHomologyCocone_ι_app K E hι ωF (FundamentalGroupoid.mk b),
    thomPairSingularHomologyIsoTwistedHomology₀]
  exact (isColimitThomPairSingularHomologyCocone K E hι ωF).comp_coconePointUniqueUpToIso_inv
    (LocalCoefficientSystem.isColimitTwistedHomology₀Cocone _) (FundamentalGroupoid.mk b)

/-- Reversing the orientation `ωF` of the model fibre negates the isomorphism. -/
@[simp]
theorem thomPairSingularHomologyIsoTwistedHomology₀_neg_hom :
    (thomPairSingularHomologyIsoTwistedHomology₀ K E hι (-ωF)).hom =
      -(thomPairSingularHomologyIsoTwistedHomology₀ K E hι ωF).hom :=
  singularHomology_thomPair_hom_ext fun b ↦ by simp

/-- Reversing the orientation `ωF` of the model fibre negates the inverse isomorphism. -/
@[simp]
theorem thomPairSingularHomologyIsoTwistedHomology₀_neg_inv :
    (thomPairSingularHomologyIsoTwistedHomology₀ K E hι (-ωF)).inv =
      -(thomPairSingularHomologyIsoTwistedHomology₀ K E hι ωF).inv :=
  Iso.inv_ext (by simp)

end VectorBundleOrientationCover

end TauCeti
