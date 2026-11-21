/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Thom.Descent
public import TauCeti.Topology.VectorBundle.Orientation.LocalSystem
public import TauCeti.AlgebraicTopology.Singular.Twisted.Zero
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Basic

/-!
# The top homology of a Thom pair and the orientation local system

Let `E → B` be a real vector bundle of rank `r` with Thom pair `(E, E₀)`, `E₀` the complement of
the zero section. This file identifies the first relative
homology group of the Thom pair that can be nonzero with the zeroth homology of the base twisted by
the orientation local system `o(E)` (`TauCeti.VectorBundleOrientationCover.signLocalSystem`), for
any ring `K`:

`Hᵣ(E, E₀; K) ≅ H₀(B; o(E) ⊗ K)`

(`TauCeti.VectorBundleOrientationCover.thomPairSingularHomologyIsoTwistedHomology₀`). This is the
bottom degree of the Thom isomorphism with twisted coefficients, `Hⱼ(E, E₀; K) ≅ Hⱼ₋ᵣ(B; o(E))`.
No orientation of the bundle and no condition on the base are needed. An orientation of the bundle
trivializes `o(E)` (`TauCeti.VectorBundleOrientation.signLocalSystemIso`), which turns the
right-hand side into `H₀(B; K)`. Without one the twist matters: over a path-connected, locally
path-connected base, `H₀(B; o(E))` with integral coefficients is `ℤ` for an orientable bundle and
`ℤ/2` for a nonorientable one, such as the Möbius line over the circle. When `-1 = 1` in `K`, as
for `ZMod 2`, the twist disappears; that case is `TauCeti.thomPairSingularHomologyFinrankIso`.
Across a critical level of a Morse–Bott function the relative homology of the sublevels is that of
the Thom pair of the negative normal bundle, so its lowest group is the zeroth homology of the
critical submanifold twisted by the orientation of the negative normal bundle.

## The identification on the fibres

The fibre of `o(E)` over `b` consists of the functions `φ` on the two orientations of `E_b` with
`φ (-ω) = -φ ω`, and `Hᵣ(E_b, E_b ∖ {0}; K)` is a free `K`-module of rank one. Fix an orientation
`ωF` of the model fibre `F` and the identification `Hᵣ(F, F ∖ {0}; K) ≅ K`
(`TauCeti.singularHomologyComplSingletonFinrankIso`). A linear trivialization `e` at `b`
identifies `E_b` with `F`, and so identifies the fibre of `o(E)`, by evaluation at the orientation
that `e` reads as `ωF`, and `Hᵣ(E_b, E_b ∖ {0}; K)` with `K`
(`TauCeti.VectorBundleOrientationCover.orientationFiberIso`). This identification does not
depend on `e` (`TauCeti.VectorBundleOrientationCover.orientationFiberIso_eq`): another
trivialization changes both identifications by the sign of the determinant of the coordinate
change, since a linear automorphism acts on `Hᵣ(F, F ∖ {0})` by the sign of its determinant
(`TauCeti.singularHomologyMap_continuousLinearMap_compl_zero`). The only remaining choice is `ωF`,
and `-ωF` gives the opposite identification.

## The proof

The identifications on the fibres followed by the inclusions of the fibre pairs form a cocone from
`o(E)` to `Hᵣ(E, E₀; K)` (`TauCeti.VectorBundleOrientationCover.thomPairCocone`): the class of an
orientation `ω` of a fibre, the image of the function with value `1` at `ω`, is constant along
paths in the orientation double cover, because inside a sheet of a trivialization it is the image
of a fixed class of `Hᵣ(F, F ∖ {0})` under fibre inclusions that are homotopic along paths in the
base set
(`Bundle.Trivialization.singularHomologyMap_fiberThomPairMap_eq_of_joinedIn`),
and transport in `o(E)` follows lifts of paths to the cover. This cocone is a colimit
(`TauCeti.VectorBundleOrientationCover.isColimitThomPairCocone`): a cocone with point `T` gives
morphisms `Hᵣ(E_b, E_b ∖ {0}; K) ⟶ T` that are constant along paths when read in a trivialization,
because the section of the double cover given by a trivialization over its base set lifts paths;
such morphisms factor uniquely through `Hᵣ(E, E₀; K)`
(`TauCeti.existsUnique_singularHomology_thomPair_fac`). Zeroth homology with local coefficients is
also the colimit of the local system
(`TauCeti.LocalCoefficientSystem.isColimitTwistedHomology₀Cocone`), and the two colimits are
isomorphic.

## Main definitions and results

* `TauCeti.VectorBundleOrientationCover.orientationFiberIso`: the identification of the fibre of
  `o(E)` over `b` with `Hᵣ(E_b, E_b ∖ {0}; K)`, read in a linear trivialization.
* `TauCeti.VectorBundleOrientationCover.orientationFiberIso_eq`: it does not depend on the
  trivialization.
* `TauCeti.VectorBundleOrientationCover.thomPairCocone`,
  `TauCeti.VectorBundleOrientationCover.isColimitThomPairCocone`: `Hᵣ(E, E₀; K)` is the colimit of
  `o(E)` over the fundamental groupoid of the base.
* `TauCeti.VectorBundleOrientationCover.thomPairSingularHomologyIsoTwistedHomology₀`:
  `Hᵣ(E, E₀; K) ≅ H₀(B; o(E))`, with its values on the fibre classes and on the classes of
  coefficients at points, in the namespace `TauCeti.VectorBundleOrientationCover`:
  `singularHomologyMap_fiberThomPairMap_thomPairSingularHomologyIsoTwistedHomology₀_hom` and
  `ιTwistedHomology₀_thomPairSingularHomologyIsoTwistedHomology₀_inv`.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10 and §12 (the Thom isomorphism and the orientation double cover).
* A. Hatcher, *Algebraic Topology*, Section 3.H (local coefficients and the orientation system) and
  Section 4.D, Theorem 4D.10 (the Thom isomorphism).
* E. H. Spanier, *Algebraic Topology*, Chapter 5, Section 7.
-/

public noncomputable section

open Bundle CategoryTheory Limits Set Module AlgebraicTopology Topology

universe w

namespace TauCeti

namespace VectorBundleOrientationCover

variable (K : Type w) [Ring K] {B : Type w} [TopologicalSpace B] {F : Type w}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {E : B → Type w}
  [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)]
  [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]
  {ι : Type} [Fintype ι] (hι : Fintype.card ι = finrank ℝ F) (ωF : Orientation ℝ F ι)

variable (F) in
/-- The identification `Hᵣ(F, F ∖ {0}; K) ≅ K` of the model fibre used in this file. -/
private abbrev modelIso :
    (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularHomology (ModuleCat.of K K)
      (finrank ℝ F) ≅ ModuleCat.of K K :=
  singularHomologyComplSingletonFinrankIso (ModuleCat.of K K) (OpenPartialHomeomorph.refl F)
    (mem_univ (0 : F))

/-- **The fibre of the orientation local system is the top local homology of the fibre.** For a
linear trivialization `e` whose base set contains `b`, the fibre of the orientation local system
`o(E)` over `b` is identified with `Hᵣ(E_b, E_b ∖ {0}; K)`: evaluate at the orientation of `E_b`
that `e` reads as `ωF`, then carry `K ≅ Hᵣ(F, F ∖ {0}; K)` to the fibre by `e`. It does not depend
on `e` (`TauCeti.VectorBundleOrientationCover.orientationFiberIso_eq`). -/
def orientationFiberIso (e : Trivialization F (π F E)) [e.IsLinear ℝ] {b : B}
    (hb : b ∈ e.baseSet) :
    (signLocalSystem F E K hι).obj (FundamentalGroupoid.mk b) ≅
      (TopPair.ofSubset (X := TopCat.of (E b)) ({0}ᶜ : Set (E b))).singularHomology
        (ModuleCat.of K K) (finrank ℝ F) :=
  (signLocalSystemFiberEquiv hι ((e.mapOrientation ι hb).symm ωF)).toModuleIso ≪≫
    (modelIso K F).symm ≪≫
      TopPair.singularHomologyMapIso _ (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.symm _

/-- The identification evaluates at the orientation of `E_b` that `e` reads as `ωF`, then carries
`K ≅ Hᵣ(F, F ∖ {0}; K)` to the fibre by `e`. -/
theorem orientationFiberIso_hom (e : Trivialization F (π F E)) [e.IsLinear ℝ] {b : B}
    (hb : b ∈ e.baseSet) :
    (orientationFiberIso K hι ωF e hb).hom =
      ModuleCat.ofHom (signLocalSystemFiberEquiv hι ((e.mapOrientation ι hb).symm ωF)).toLinearMap ≫
        (singularHomologyComplSingletonFinrankIso (ModuleCat.of K K)
          (OpenPartialHomeomorph.refl F) (mem_univ (0 : F))).inv ≫
          TopPair.singularHomologyMap (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.inv
            (ModuleCat.of K K) (finrank ℝ F) :=
  (rfl)

omit [FiniteDimensional ℝ F] in
/-- Evaluation at the opposite orientation is the negative of evaluation at `o`, as a morphism. -/
private theorem ofHom_signLocalSystemFiberEquiv_neg {b : B} (o : Orientation ℝ (E b) ι) :
    ModuleCat.ofHom (signLocalSystemFiberEquiv (R := K) hι (-o)).toLinearMap =
      -ModuleCat.ofHom (signLocalSystemFiberEquiv hι o).toLinearMap := by
  ext φ
  exact signLocalSystemFiberEquiv_neg hι o φ

/-- **The identification does not depend on the trivialization.** Two linear trivializations
whose base sets contain `b` give the same identification of the fibre of `o(E)` over `b` with
`Hᵣ(E_b, E_b ∖ {0}; K)`. -/
theorem orientationFiberIso_eq (e e' : Trivialization F (π F E)) [e.IsLinear ℝ] [e'.IsLinear ℝ]
    {b : B} (hb : b ∈ e.baseSet) (hb' : b ∈ e'.baseSet) :
    orientationFiberIso K hι ωF e hb = orientationFiberIso K hι ωF e' hb' := by
  set c := e.coordChangeL ℝ e' b
  -- Reading in `e'` is reading in `e` followed by the coordinate change `c`.
  have ho : e'.mapOrientation ι hb' ((e.mapOrientation ι hb).symm ωF) =
      Orientation.map ι c.toLinearEquiv ωF := by
    rw [Trivialization.mapOrientation_eq_map_coordChangeL e e' hb hb', Equiv.apply_symm_apply]
  have hH : TopPair.singularHomologyMap (e'.continuousLinearEquivAt ℝ b hb').complZeroPairIso.inv
      (ModuleCat.of K K) (finrank ℝ F) =
        TopPair.singularHomologyMap c.complZeroPairIso.inv (ModuleCat.of K K) (finrank ℝ F) ≫
          TopPair.singularHomologyMap (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.inv
            (ModuleCat.of K K) (finrank ℝ F) := by
    rw [← e.continuousLinearEquivAt_trans_coordChangeL ℝ e' hb hb',
      ContinuousLinearEquiv.complZeroPairIso_trans, Iso.trans_inv,
      TopPair.singularHomologyMap_comp]
  -- The coordinate change acts on `Hᵣ(F, F ∖ {0})` by the sign of its determinant.
  have hcH : TopPair.singularHomologyMap c.complZeroPairIso.hom (ModuleCat.of K K) (finrank ℝ F) =
      (SignType.sign (LinearMap.det (c.toLinearEquiv : F →ₗ[ℝ] F)) : ℤ) • 𝟙 _ := by
    rw [ContinuousLinearEquiv.complZeroPairIso_hom]
    exact singularHomologyMap_continuousLinearMap_compl_zero _ (c : F →L[ℝ] F) _ _
  have hcinv : TopPair.singularHomologyMap c.complZeroPairIso.inv (ModuleCat.of K K)
      (finrank ℝ F) =
        (SignType.sign (LinearMap.det (c.toLinearEquiv : F →ₗ[ℝ] F)) : ℤ) • 𝟙 _ := by
    have hinv : TopPair.singularHomologyMap c.complZeroPairIso.hom (ModuleCat.of K K)
        (finrank ℝ F) ≫ TopPair.singularHomologyMap c.complZeroPairIso.inv (ModuleCat.of K K)
          (finrank ℝ F) = 𝟙 _ := by
      rw [← TopPair.singularHomologyMap_comp, Iso.hom_inv_id, TopPair.singularHomologyMap_id]
    rw [hcH, Linear.smul_comp, Category.id_comp] at hinv
    have hsq : (SignType.sign (LinearMap.det (c.toLinearEquiv : F →ₗ[ℝ] F)) : ℤ) *
        SignType.sign (LinearMap.det (c.toLinearEquiv : F →ₗ[ℝ] F)) = 1 := by
      rcases (LinearEquiv.isUnit_det' c.toLinearEquiv).ne_zero.lt_or_gt with h | h <;> simp [h]
    rw [← hinv, smul_smul, hsq, one_smul]
  ext : 1
  rw [orientationFiberIso_hom, orientationFiberIso_hom, hH, hcinv]
  rcases (LinearEquiv.isUnit_det' c.toLinearEquiv).ne_zero.lt_or_gt with hneg | hpos
  · -- A coordinate change of negative determinant reverses the orientation read as `ωF`.
    have hω : (e'.mapOrientation ι hb').symm ωF = -(e.mapOrientation ι hb).symm ωF := by
      rw [Equiv.symm_apply_eq, Trivialization.mapOrientation_neg, ho,
        (Orientation.map_eq_neg_iff_det_neg ωF c.toLinearEquiv hι).2 hneg]
      exact (neg_neg ωF).symm
    rw [hω, ofHom_signLocalSystemFiberEquiv_neg, sign_neg hneg]
    simp
  · have hω : (e'.mapOrientation ι hb').symm ωF = (e.mapOrientation ι hb).symm ωF := by
      rw [Equiv.symm_apply_eq, ho, (Orientation.map_eq_iff_det_pos ωF c.toLinearEquiv hι).2 hpos]
    rw [hω, sign_pos hpos]
    simp


/-! ### The cocone -/

/-- The structure map at `b` of the cocone: the identification of the fibre of `o(E)` with
`Hᵣ(E_b, E_b ∖ {0}; K)` followed by the inclusion of the fibre pair. -/
private def leg (b : B) :
    (signLocalSystem F E K hι).obj (FundamentalGroupoid.mk b) ⟶
      (thomPair F E).singularHomology (ModuleCat.of K K) (finrank ℝ F) :=
  (orientationFiberIso K hι ωF (trivializationAt F E b)
      (FiberBundle.mem_baseSet_trivializationAt' b)).hom ≫
    TopPair.singularHomologyMap (fiberThomPairMap F E b) (ModuleCat.of K K) (finrank ℝ F)

private theorem leg_eq (e : Trivialization F (π F E)) [e.IsLinear ℝ] {b : B}
    (hb : b ∈ e.baseSet) :
    leg K hι ωF b = (orientationFiberIso K hι ωF e hb).hom ≫
      TopPair.singularHomologyMap (fiberThomPairMap F E b) (ModuleCat.of K K) (finrank ℝ F) := by
  rw [leg, orientationFiberIso_eq K hι ωF _ e]

/-- The class in `Hᵣ(E, E₀; K)` of a point `(b, ω)` of the orientation double cover: the image of
the function with value `1` at `ω`. -/
private def fiberClass (p : VectorBundleOrientationCover F E ι) :
    ((thomPair F E).singularHomology (ModuleCat.of K K) (finrank ℝ F) : ModuleCat.{w} K) :=
  (leg K hι ωF p.proj).hom ((signLocalSystemFiberEquiv hι p.orientation).symm 1)

/-- The structure map at `b` evaluates at any point of the fibre of the double cover over `b` and
multiplies the class of that point. -/
private theorem leg_apply (b : B) (q : (proj ⁻¹' {b} : Set (VectorBundleOrientationCover F E ι)))
    (ψ : (signLocalSystem F E K hι).obj (FundamentalGroupoid.mk b)) :
    (leg K hι ωF b).hom ψ =
      (signLocalSystemObjEquiv hι (FundamentalGroupoid.mk b) ψ :
        (proj ⁻¹' {b} : Set (VectorBundleOrientationCover F E ι)) → K) q •
        fiberClass K hι ωF q.1 := by
  obtain ⟨⟨b', o⟩, hb'⟩ := q
  obtain rfl : b' = b := hb'
  have h : ψ = signLocalSystemFiberEquiv hι o ψ • (signLocalSystemFiberEquiv hι o).symm 1 := by
    rw [← map_smul, smul_eq_mul, mul_one, LinearEquiv.symm_apply_apply]
  conv_lhs => rw [h]
  rw [map_smul, signLocalSystemFiberEquiv_apply]
  rfl

/-- The model class `K ≅ Hᵣ(F, F ∖ {0}; K)` carried into `Hᵣ(E, E₀; K)` by the fibre over `b` of
a linear trivialization. -/
private abbrev trivializationClass (e : Trivialization F (π F E)) [e.IsLinear ℝ] {b : B}
    (hb : b ∈ e.baseSet) :
    ((thomPair F E).singularHomology (ModuleCat.of K K) (finrank ℝ F) : ModuleCat.{w} K) :=
  (TopPair.singularHomologyMap ((e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.inv ≫
    fiberThomPairMap F E b) (ModuleCat.of K K) (finrank ℝ F)).hom ((modelIso K F).inv.hom 1)

/-- In a trivialization reading the orientation of `p` as `ωF`, the class of `p` is the model
class carried by the trivialization. -/
private theorem fiberClass_of_eq (e : Trivialization F (π F E)) [e.IsLinear ℝ]
    {p : VectorBundleOrientationCover F E ι} (hp : p.proj ∈ e.baseSet)
    (ho : e.mapOrientation ι hp p.orientation = ωF) :
    fiberClass K hι ωF p = trivializationClass K e hp := by
  have hω : (e.mapOrientation ι hp).symm ωF = p.orientation := by
    rw [Equiv.symm_apply_eq, ho]
  rw [fiberClass, leg_eq K hι ωF e hp, orientationFiberIso_hom, hω, trivializationClass,
    TopPair.singularHomologyMap_comp]
  simp

/-- In a trivialization reading the orientation of `p` as `-ωF`, the class of `p` is minus the
model class carried by the trivialization. -/
private theorem fiberClass_of_eq_neg (e : Trivialization F (π F E)) [e.IsLinear ℝ]
    {p : VectorBundleOrientationCover F E ι} (hp : p.proj ∈ e.baseSet)
    (ho : e.mapOrientation ι hp p.orientation = -ωF) :
    fiberClass K hι ωF p = -trivializationClass K e hp := by
  have hω : (e.mapOrientation ι hp).symm ωF = -p.orientation := by
    rw [Equiv.symm_apply_eq, Trivialization.mapOrientation_neg, ho]
    exact (neg_neg ωF).symm
  rw [fiberClass, leg_eq K hι ωF e hp, orientationFiberIso_hom, hω,
    ofHom_signLocalSystemFiberEquiv_neg, trivializationClass, TopPair.singularHomologyMap_comp]
  simp

/-- **The class of an orientation is constant along paths in the orientation double cover.** -/
private theorem fiberClass_zero_eq_one (Γ : C(unitInterval, VectorBundleOrientationCover F E ι)) :
    fiberClass K hι ωF (Γ 0) = fiberClass K hι ωF (Γ 1) := by
  have : LocallyPathConnectedSpace unitInterval :=
    Convex.locallyPathConnectedSpace ℝ (convex_Icc (0 : ℝ) 1)
  have hlc : IsLocallyConstant fun t ↦ fiberClass K hι ωF (Γ t) := by
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun t ↦ ?_
    -- Near `t` the path stays in the sheet of the trivialization at `Γ t` containing `Γ t`.
    let e := trivializationAt F E (Γ t).proj
    have ht : (Γ t).proj ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' _
    let o := e.mapOrientation ι ht (Γ t).orientation
    have hO : Γ ⁻¹' sheet e o ∈ 𝓝 t :=
      ((isOpen_sheet hι e o).preimage Γ.continuous).mem_nhds (mem_sheet_iff.2 ⟨ht, rfl⟩)
    filter_upwards [pathComponentIn_mem_nhds hO] with s hs
    have hj : JoinedIn (sheet e o) (Γ t) (Γ s) :=
      (hs.map Γ.continuous.continuousOn).mono (by rintro _ ⟨u, hu, rfl⟩; exact hu)
    obtain ⟨hsb, hso⟩ := mem_sheet_iff.1 hj.target_mem
    -- Their base points are joined in the base set of `e`.
    have hjb : JoinedIn e.baseSet (Γ t).proj (Γ s).proj :=
      (hj.map continuous_proj.continuousOn).mono (by
        rintro _ ⟨q, hq, rfl⟩
        exact (mem_sheet_iff.1 hq).1)
    have hκ : trivializationClass K e hsb = trivializationClass K e ht := by
      simp only [trivializationClass,
        e.singularHomologyMap_fiberThomPairMap_eq_of_joinedIn (ModuleCat.of K K) ht hsb hjb]
    rcases Orientation.eq_or_eq_neg o ωF hι with h | h
    · rw [fiberClass_of_eq K hι ωF e hsb (hso.trans h), fiberClass_of_eq K hι ωF e ht h, hκ]
    · rw [fiberClass_of_eq_neg K hι ωF e hsb (hso.trans h), fiberClass_of_eq_neg K hι ωF e ht h,
        hκ]
  exact hlc.apply_eq_of_preconnectedSpace 0 1

omit [FiniteDimensional ℝ F] in
/-- The monodromy of a path class is the endpoint of a path in the double cover from the starting
point. -/
private theorem exists_continuousMap_monodromy {x y : FundamentalGroupoid (TopCat.of B)}
    (γ : x ⟶ y) (a : (proj ⁻¹' {x.as} : Set (VectorBundleOrientationCover F E ι))) :
    ∃ Γ : C(unitInterval, VectorBundleOrientationCover F E ι),
      Γ 0 = a ∧ Γ 1 = (isCoveringMap_proj (F := F) (E := E) hι).monodromy γ a := by
  obtain ⟨γ⟩ := γ
  exact ⟨_, (isCoveringMap_proj hι).liftPath_zero .., ((isCoveringMap_proj hι).coe_monodromy_mk
    γ a).symm⟩

omit [FiniteDimensional ℝ F] in
/-- Transport in `o(E)`, evaluated at the monodromy of a point, is evaluation at that point. -/
private theorem signLocalSystemObjEquiv_map_monodromy
    {x y : FundamentalGroupoid (TopCat.of B)} (γ : x ⟶ y)
    (φ : (signLocalSystem F E K hι).obj x)
    (a : (proj ⁻¹' {x.as} : Set (VectorBundleOrientationCover F E ι))) :
    (signLocalSystemObjEquiv hι y (((signLocalSystem F E K hι).map γ).hom φ) :
      (proj ⁻¹' {y.as} : Set (VectorBundleOrientationCover F E ι)) → K)
        ((isCoveringMap_proj hι).monodromy γ a) =
      (signLocalSystemObjEquiv hι x φ :
        (proj ⁻¹' {x.as} : Set (VectorBundleOrientationCover F E ι)) → K) a := by
  rw [signLocalSystemObjEquiv_map_apply,
    ← (isCoveringMap_proj hι).monodromy_trans_apply γ (inv γ) a]
  have h := congrArg (fun δ ↦ (isCoveringMap_proj (F := F) (E := E) hι).monodromy δ a)
    (IsIso.hom_inv_id γ)
  exact congrArg _ (h.trans (congrFun (isCoveringMap_proj hι).monodromy_refl a))

/-- **The fibre classes are compatible with transport in `o(E)`.** The identification of the
fibre of `o(E)` with `Hᵣ(E_b, E_b ∖ {0}; K)`, followed by the inclusion of the fibre pair, is
compatible with transport along paths in the base: the class of an orientation of a fibre is
constant along paths in the orientation double cover. -/
theorem map_comp_orientationFiberIso_hom_comp_singularHomologyMap_fiberThomPairMap
    {x y : FundamentalGroupoid (TopCat.of B)} (γ : x ⟶ y) :
    (signLocalSystem F E K hι).map γ ≫ (orientationFiberIso K hι ωF (trivializationAt F E y.as)
        (FiberBundle.mem_baseSet_trivializationAt' y.as)).hom ≫
        TopPair.singularHomologyMap (fiberThomPairMap F E y.as) (ModuleCat.of K K) (finrank ℝ F) =
      (orientationFiberIso K hι ωF (trivializationAt F E x.as)
        (FiberBundle.mem_baseSet_trivializationAt' x.as)).hom ≫
        TopPair.singularHomologyMap (fiberThomPairMap F E x.as) (ModuleCat.of K K)
          (finrank ℝ F) := by
  rw [← leg, ← leg]
  ext φ
  -- Evaluate at a point over `x` and at its monodromy over `y`.
  let a : (proj ⁻¹' {x.as} : Set (VectorBundleOrientationCover F E ι)) :=
    ⟨⟨x.as, ((trivializationAt F E x.as).mapOrientation ι
      (FiberBundle.mem_baseSet_trivializationAt' x.as)).symm ωF⟩, rfl⟩
  obtain ⟨Γ, hΓ0, hΓ1⟩ := exists_continuousMap_monodromy hι γ a
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply]
  rw [leg_apply K hι ωF y.as ((isCoveringMap_proj hι).monodromy γ a),
    leg_apply K hι ωF x.as a, signLocalSystemObjEquiv_map_monodromy, ← hΓ1, ← hΓ0,
    fiberClass_zero_eq_one]

variable (E) in
/-- **The cocone of fibre classes.** The identifications of the fibres of the orientation local
system `o(E)` with the groups `Hᵣ(E_b, E_b ∖ {0}; K)` (`orientationFiberIso`), read in the
trivializations of the atlas and followed by the inclusions of the fibre pairs, form a cocone from
`o(E)` to `Hᵣ(E, E₀; K)`. -/
-- The cocone point must compute to the homology of the Thom pair in the signatures comparing the
-- structure maps with the fibre inclusions.
@[expose]
def thomPairCocone : Cocone (signLocalSystem F E K hι) where
  pt := (thomPair F E).singularHomology (ModuleCat.of K K) (finrank ℝ F)
  ι :=
    { app x := (orientationFiberIso K hι ωF (trivializationAt F E x.as)
          (FiberBundle.mem_baseSet_trivializationAt' x.as)).hom ≫
        TopPair.singularHomologyMap (fiberThomPairMap F E x.as) (ModuleCat.of K K) (finrank ℝ F)
      naturality _ _ γ :=
        (map_comp_orientationFiberIso_hom_comp_singularHomologyMap_fiberThomPairMap K hι ωF
          γ).trans (Category.comp_id _).symm }

@[simp]
theorem thomPairCocone_pt :
    (thomPairCocone K E hι ωF).pt =
      (thomPair F E).singularHomology (ModuleCat.of K K) (finrank ℝ F) :=
  (rfl)

/-- The structure map of the cocone at `b` is the identification of the fibre read in any linear
trivialization at `b`, followed by the inclusion of the fibre pair. -/
theorem thomPairCocone_ι_app (e : Trivialization F (π F E)) [e.IsLinear ℝ] {b : B}
    (hb : b ∈ e.baseSet) :
    (thomPairCocone K E hι ωF).ι.app (FundamentalGroupoid.mk b) =
      (orientationFiberIso K hι ωF e hb).hom ≫
        TopPair.singularHomologyMap (fiberThomPairMap F E b) (ModuleCat.of K K) (finrank ℝ F) :=
  leg_eq K hι ωF e hb

omit [FiniteDimensional ℝ F] in
/-- Transport in `o(E)` along a path in the base set of a trivialization of the atlas carries the
function with value `r` at the orientation read as `ωF` to the same function at the endpoint: the
orientations read as `ωF` form a section of the double cover over the base set, which lifts the
path. -/
private theorem map_signLocalSystemFiberEquiv_symm (e : Trivialization F (π F E))
    [MemTrivializationAtlas e] {x y : B} (hx : x ∈ e.baseSet) (hy : y ∈ e.baseSet)
    (γ : Path x y) (hγ : ∀ t, γ t ∈ e.baseSet) :
    ModuleCat.ofHom (signLocalSystemFiberEquiv (R := K) hι
        ((e.mapOrientation ι hx).symm ωF)).symm.toLinearMap ≫
        (signLocalSystem F E K hι).map
          (show FundamentalGroupoid.mk (X := TopCat.of B) x ⟶ FundamentalGroupoid.mk y from
            Path.Homotopic.Quotient.mk γ) =
      ModuleCat.ofHom (signLocalSystemFiberEquiv hι
        ((e.mapOrientation ι hy).symm ωF)).symm.toLinearMap := by
  -- The section of the double cover over the base set reading orientations as `ωF`.
  let σ : e.baseSet → VectorBundleOrientationCover F E ι :=
    fun z ↦ ⟨z, (e.mapOrientation ι z.2).symm ωF⟩
  let γ' : C(unitInterval, e.baseSet) := ⟨fun t ↦ ⟨γ t, hγ t⟩, γ.continuous.subtype_mk hγ⟩
  let a : (proj ⁻¹' {x} : Set (VectorBundleOrientationCover F E ι)) :=
    ⟨⟨x, (e.mapOrientation ι hx).symm ωF⟩, rfl⟩
  have hm : (isCoveringMap_proj (F := F) (E := E) hι).monodromy (Path.Homotopic.Quotient.mk γ) a =
      ⟨⟨y, (e.mapOrientation ι hy).symm ωF⟩, rfl⟩ := by
    refine Subtype.ext ((isCoveringMap_proj hι).monodromy_eq_apply_one (γ := γ) (e := a)
      (Γ := ⟨σ ∘ γ', (continuous_mk_mapOrientation_symm hι e ωF).comp γ'.continuous⟩)
      (funext fun _ ↦ rfl) ?_ |>.trans ?_)
    · exact congrArg σ (Subtype.ext γ.source : γ' 0 = ⟨x, hx⟩)
    · exact congrArg σ (Subtype.ext γ.target : γ' 1 = ⟨y, hy⟩)
  ext
  apply (signLocalSystemFiberEquiv hι ((e.mapOrientation ι hy).symm ωF)).injective
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply, ModuleCat.hom_ofHom,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  rw [signLocalSystemFiberEquiv_apply, ← hm, signLocalSystemObjEquiv_map_monodromy]
  exact (signLocalSystemFiberEquiv_apply hι _ _).symm.trans (LinearEquiv.apply_symm_apply _ _)

/-- **`Hᵣ(E, E₀; K)` is the colimit of the orientation local system.** The cocone of fibre classes
(`TauCeti.VectorBundleOrientationCover.thomPairCocone`) exhibits `Hᵣ(E, E₀; K)` as the colimit of
`o(E)` over the fundamental groupoid of the base. -/
def isColimitThomPairCocone : IsColimit (thomPairCocone K E hι ωF) :=
  IsColimit.ofExistsUnique fun s ↦ by
    -- The morphisms out of the fibre groups: read the fibre of `o(E)`, then map to `s`.
    let g (b : B) := (orientationFiberIso K hι ωF (trivializationAt F E b)
      (FiberBundle.mem_baseSet_trivializationAt' b)).inv ≫ s.ι.app (FundamentalGroupoid.mk b)
    obtain ⟨Φ, hΦ, hΦu⟩ := existsUnique_singularHomology_thomPair_fac g fun z x y hx hy hxy ↦ by
      obtain ⟨γ, hγ⟩ := hxy
      -- Read both fibres in the trivialization at `z`.
      set e := trivializationAt F E z
      have he (b : B) (hb : b ∈ e.baseSet) :
          TopPair.singularHomologyMap (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.inv
            (ModuleCat.of K K) (finrank ℝ F) ≫ g b =
          (modelIso K F).hom ≫ ModuleCat.ofHom (signLocalSystemFiberEquiv hι
            ((e.mapOrientation ι hb).symm ωF)).symm.toLinearMap ≫
              s.ι.app (FundamentalGroupoid.mk b) := by
        simp only [g]
        rw [orientationFiberIso_eq K hι ωF (trivializationAt F E b) e _ hb]
        simp only [orientationFiberIso, Iso.trans_inv, Category.assoc,
          TopPair.singularHomologyMapIso_inv, Iso.symm_inv]
        rw [← TopPair.singularHomologyMap_comp_assoc, Iso.inv_hom_id,
          TopPair.singularHomologyMap_id, Category.id_comp]
        rfl
      rw [he x hx, he y hy, ← s.w (show FundamentalGroupoid.mk (X := TopCat.of B) x ⟶
        FundamentalGroupoid.mk y from Path.Homotopic.Quotient.mk γ),
        reassoc_of% map_signLocalSystemFiberEquiv_symm K hι ωF e hx hy γ hγ]
    refine ⟨Φ, fun x ↦ ?_, fun Φ' hΦ' ↦ hΦu Φ' fun b ↦ ?_⟩
    · simp only [thomPairCocone, Category.assoc, hΦ, g, Iso.hom_inv_id_assoc]
    · rw [← cancel_epi (orientationFiberIso K hι ωF (trivializationAt F E b)
        (FiberBundle.mem_baseSet_trivializationAt' b)).hom, Iso.hom_inv_id_assoc,
        ← hΦ' (FundamentalGroupoid.mk b)]
      exact (Category.assoc _ _ _).symm

variable (E) in
/-- **The top homology of the Thom pair is the zeroth homology twisted by the orientation local
system.** For a real vector bundle `E → B` of rank `r` and a commutative ring `K`,
`Hᵣ(E, E₀; K) ≅ H₀(B; o(E) ⊗ K)`, where `o(E)` is the orientation local system. The isomorphism
depends on an orientation `ωF` of the model fibre, through the identification of each fibre of
`o(E)` with `Hᵣ(E_b, E_b ∖ {0}; K)` (`TauCeti.VectorBundleOrientationCover.orientationFiberIso`);
the opposite orientation gives the opposite isomorphism. The base is arbitrary and the bundle need
not be orientable. -/
def thomPairSingularHomologyIsoTwistedHomology₀ :
    (thomPair F E).singularHomology (ModuleCat.of K K) (finrank ℝ F) ≅
      LocalCoefficientSystem.twistedHomology (signLocalSystem F E K hι) 0 :=
  (isColimitThomPairCocone K hι ωF).coconePointUniqueUpToIso
    (LocalCoefficientSystem.isColimitTwistedHomology₀Cocone _)

/-- **The isomorphism on the fibres.** The inclusion of the fibre pair over `b`, followed by
`Hᵣ(E, E₀; K) ≅ H₀(B; o(E))`, is the identification of `Hᵣ(E_b, E_b ∖ {0}; K)` with the fibre of
`o(E)` over `b`, read in any linear trivialization at `b`, followed by the class of a coefficient
at `b` in twisted zeroth homology. -/
@[reassoc]
theorem singularHomologyMap_fiberThomPairMap_thomPairSingularHomologyIsoTwistedHomology₀_hom
    (e : Trivialization F (π F E)) [e.IsLinear ℝ] {b : B} (hb : b ∈ e.baseSet) :
    TopPair.singularHomologyMap (fiberThomPairMap F E b) (ModuleCat.of K K) (finrank ℝ F) ≫
        (thomPairSingularHomologyIsoTwistedHomology₀ K E hι ωF).hom =
      (orientationFiberIso K hι ωF e hb).inv ≫
        LocalCoefficientSystem.ιTwistedHomology₀ (signLocalSystem F E K hι) b := by
  rw [Iso.eq_inv_comp, ← Category.assoc, ← thomPairCocone_ι_app K hι ωF e hb,
    thomPairSingularHomologyIsoTwistedHomology₀]
  exact (isColimitThomPairCocone K hι ωF).comp_coconePointUniqueUpToIso_hom
    (LocalCoefficientSystem.isColimitTwistedHomology₀Cocone _) (FundamentalGroupoid.mk b)

/-- The class of a coefficient at `b` in twisted zeroth homology corresponds, under
`H₀(B; o(E)) ≅ Hᵣ(E, E₀; K)`, to its image in `Hᵣ(E_b, E_b ∖ {0}; K)` followed by the inclusion of
the fibre pair. -/
@[reassoc]
theorem ιTwistedHomology₀_thomPairSingularHomologyIsoTwistedHomology₀_inv
    (e : Trivialization F (π F E)) [e.IsLinear ℝ] {b : B} (hb : b ∈ e.baseSet) :
    LocalCoefficientSystem.ιTwistedHomology₀ (signLocalSystem F E K hι) b ≫
        (thomPairSingularHomologyIsoTwistedHomology₀ K E hι ωF).inv =
      (orientationFiberIso K hι ωF e hb).hom ≫
        TopPair.singularHomologyMap (fiberThomPairMap F E b) (ModuleCat.of K K) (finrank ℝ F) := by
  rw [← thomPairCocone_ι_app K hι ωF e hb, thomPairSingularHomologyIsoTwistedHomology₀]
  exact (isColimitThomPairCocone K hι ωF).comp_coconePointUniqueUpToIso_inv
    (LocalCoefficientSystem.isColimitTwistedHomology₀Cocone _) (FundamentalGroupoid.mk b)

end VectorBundleOrientationCover

end TauCeti
