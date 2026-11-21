/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.MayerVietoris.DirectedUnion
public import TauCeti.Topology.VectorBundle.Orientation.LocalSystem
public import TauCeti.AlgebraicTopology.Singular.Twisted.Zero
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Linear
public import TauCeti.AlgebraicTopology.Singular.Reduced

/-!
# The integral homology of the Thom pair in the rank degree

Let `E → B` be a real vector bundle of rank `n + 1` over an arbitrary base, with Thom pair
`(E, E₀)`, `E₀` the complement of the zero section. Its relative homology vanishes below the rank
(`TauCeti.isZero_singularHomology_thomPair`), and this file computes the first group that does not
vanish, with integer coefficients and without assuming that `E` is orientable:

`Hₙ₊₁(E, E₀; ℤ) ≅ H₀(B; o(E))`

(`TauCeti.thomPairSingularHomologyIsoTwistedHomology`), the zeroth homology of the base with
coefficients in the orientation local system `o(E)`
(`TauCeti.VectorBundleOrientationCover.signLocalSystem`). An orientation `o` of a fibre `E_b`
selects a generator of `Hₙ₊₁(E_b, E_b ∖ {0}; ℤ) ≅ ℤ` (`TauCeti.fiberLocalOrientation`), and the
opposite orientation selects its negative. A coefficient of `o(E)` at `b` is a function `f` on the
orientations of `E_b` with `f (-o) = -f o`, and the inverse isomorphism sends it to `f o` times the
class of the fibre over `b` oriented by `o`, which does not depend on `o`
(`TauCeti.thomPairSingularHomologyIsoTwistedHomology_inv_apply`). So the class of the fibre over
`b` oriented by `o` goes to the coefficient at `b` taking the value `1` at `o`
(`TauCeti.thomPairSingularHomologyIsoTwistedHomology_hom_apply`).

This is the bottom degree of the Thom isomorphism with twisted coefficients,
`Hₙ₊₁₊ₖ(E, E₀; ℤ) ≅ Hₖ(B; o(E))`. When `E` is orientable, an orientation trivializes `o(E)`
(`TauCeti.VectorBundleOrientation.signLocalSystemIso`), and `H₀(B; o(E))` is `H₀(B; ℤ)`; for a
nonorientable bundle the twisting is visible already here: for the Möbius line over the circle,
`H₀` of the circle with coefficients in its orientation system is `ℤ/2`, not `ℤ`. Relative homology
of Thom pairs is what attaching a disc bundle along its sphere bundle produces
(`TauCeti.isIso_singularHomologyMap_of_attach_discBundle`), for instance when a level of a
Morse–Bott function is crossed, and this file identifies it in the lowest degree, the rank of the
attached bundle.

## The proof

The argument follows that of `TauCeti.thomPairSingularHomologyFinrankIso`, with fibre classes
indexed by the points of the orientation double cover. These are constant along paths in the
cover, since near each point a trivialization identifies them with fibre classes of a product
bundle; transport in `o(E)` is path lifting in the cover, so the fibre classes over a subset `W`
define a map `H₀(W; o(E)) ⟶ Hₙ₊₁(E|_W, E₀|_W; ℤ)` out of the colimit description of twisted
zeroth homology. It is an isomorphism over trivializing sets, then over their finite unions by the
Mayer–Vietoris sequences of the Thom pairs, which end in the rank degree, and finally over the
whole base, since singular homology has compact supports.

## Main results

* `TauCeti.fiberLocalOrientation`: the generator of `Hₙ₊₁(E_b, E_b ∖ {0}; ℤ)` selected by an
  orientation of `E_b`.
* `TauCeti.thomPairSingularHomologyIsoTwistedHomology`: `Hₙ₊₁(E, E₀; ℤ) ≅ H₀(B; o(E))`.
* `TauCeti.thomPairSingularHomologyIsoTwistedHomology_inv_apply`,
  `TauCeti.thomPairSingularHomologyIsoTwistedHomology_hom_apply`: the isomorphism on fibre classes.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10, Lemma 10.3 and the proof of Theorem 10.4 (the induction over finite unions
  of trivializing open sets and the passage to a directed union).
* A. Hatcher, *Algebraic Topology*, Section 3.H (local coefficients and the orientation system)
  and Section 4.D, Theorem 4D.10 and its proof.
-/

public noncomputable section

open Bundle CategoryTheory Limits Set Module AlgebraicTopology Topology

universe w

namespace TauCeti

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]
  {n : ℕ}

open VectorBundleOrientationCover

variable (hF : finrank ℝ F = n + 1)

/-- The local orientation of the fibre `E_b` selected by an orientation `o` of `E_b`: the local
orientation of the model fibre `F` selected by `o` read in the preferred trivialization at `b`
(`Orientation.localOrientation`), carried back to `Hₙ₊₁(E_b, E_b ∖ {0}; ℤ)`. By naturality of the
selected local orientations it does not depend on the trivialization
(`TauCeti.singularHomologyMap_complZeroPairIso_fiberLocalOrientation`). -/
def fiberLocalOrientation (b : B) (o : Orientation ℝ (E b) (Fin (n + 1))) :
    ((TopPair.ofSubset (X := TopCat.of (E b)) ({0}ᶜ : Set (E b))).singularHomology
      (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1) : ModuleCat.{w} ℤ) :=
  TopPair.singularHomologyMap ((trivializationAt F E b).continuousLinearEquivAt ℝ b
      (FiberBundle.mem_baseSet_trivializationAt' b)).complZeroPairIso.inv
    (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1)
    (((trivializationAt F E b).mapOrientation (Fin (n + 1))
      (FiberBundle.mem_baseSet_trivializationAt' b) o).localOrientation hF).1

omit [TopologicalSpace B] [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E] in
private theorem toLinearEquiv_continuousLinearEquivAt [TopologicalSpace B]
    [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
    (e : Trivialization F (π F E)) [e.IsLinear ℝ] {b : B} (hb : b ∈ e.baseSet) :
    (e.continuousLinearEquivAt ℝ b hb).toLinearEquiv = e.linearEquivAt ℝ b hb :=
  LinearEquiv.ext fun _ ↦ rfl

/-- **The fibre local orientations in any trivialization**: a linear trivialization `e` at `b`
carries the local orientation of `E_b` selected by `o` to the local orientation of `F` selected by
`o` read in `e`. -/
theorem singularHomologyMap_complZeroPairIso_fiberLocalOrientation
    (e : Trivialization F (π F E)) [e.IsLinear ℝ] {b : B} (hb : b ∈ e.baseSet)
    (o : Orientation ℝ (E b) (Fin (n + 1))) :
    TopPair.singularHomologyMap (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.hom
        (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1) (fiberLocalOrientation hF b o) =
      ((e.mapOrientation (Fin (n + 1)) hb o).localOrientation hF).1 := by
  set L₀ := (trivializationAt F E b).continuousLinearEquivAt ℝ b
    (FiberBundle.mem_baseSet_trivializationAt' b)
  set L := e.continuousLinearEquivAt ℝ b hb
  have hcomp : L₀.complZeroPairIso.inv ≫ L.complZeroPairIso.hom =
      (L₀.symm.trans L).complZeroPairIso.hom := by
    rw [ContinuousLinearEquiv.complZeroPairIso_trans, ContinuousLinearEquiv.complZeroPairIso_symm,
      Iso.trans_hom, Iso.symm_hom]
  have ho : Orientation.map (Fin (n + 1)) (L₀.symm.trans L).toLinearEquiv
      (Orientation.map (Fin (n + 1)) L₀.toLinearEquiv o) =
      Orientation.map (Fin (n + 1)) L.toLinearEquiv o := by
    have hL : L₀.toLinearEquiv.trans (L₀.symm.trans L).toLinearEquiv = L.toLinearEquiv := by
      ext x
      simp
    rw [← Orientation.map_trans, hL]
  rw [fiberLocalOrientation, ← ConcreteCategory.comp_apply, ← TopPair.singularHomologyMap_comp,
    hcomp, Bundle.Trivialization.mapOrientation_apply, Bundle.Trivialization.mapOrientation_apply,
    ← toLinearEquiv_continuousLinearEquivAt, ← toLinearEquiv_continuousLinearEquivAt, ← ho,
    Orientation.localOrientation_map _ _ hF hF, LocalOrientation.coe_map]

/-- Reversing the orientation reverses the fibre local orientation. -/
@[simp]
theorem fiberLocalOrientation_neg (b : B) (o : Orientation ℝ (E b) (Fin (n + 1))) :
    fiberLocalOrientation hF b (-o) = -fiberLocalOrientation hF b o := by
  rw [fiberLocalOrientation, fiberLocalOrientation, Bundle.Trivialization.mapOrientation_neg,
    Orientation.localOrientation_neg, LocalOrientation.coe_neg, map_neg]

/-- The fibre class over `b ∈ W` of a point `(b, o)` of the orientation double cover. -/
private def fiberClass (W : Set B) (p : VectorBundleOrientationCover F E (Fin (n + 1)))
    (hp : p.proj ∈ W) :
    ((thomPairOver F E W).singularHomology (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1) :
      ModuleCat.{w} ℤ) :=
  TopPair.singularHomologyMap (fiberThomPairOverMap F E hp) (ModuleCat.of ℤ (ULift.{w} ℤ))
    (n + 1) (fiberLocalOrientation hF p.proj p.orientation)

/-- Reversing the orientation reverses the fibre class. -/
private theorem fiberClass_mk_neg (W : Set B) {b : B} (o : Orientation ℝ (E b) (Fin (n + 1)))
    (hb : b ∈ W) :
    fiberClass hF W ⟨b, -o⟩ hb = -fiberClass hF W ⟨b, o⟩ hb := by
  simp only [fiberClass, fiberLocalOrientation_neg, map_neg]

/-- The restriction maps of the Thom pairs carry fibre classes to fibre classes. -/
private theorem singularHomologyMap_thomPairOverMap_fiberClass {W W' : Set B} (h : W ⊆ W')
    (p : VectorBundleOrientationCover F E (Fin (n + 1))) (hp : p.proj ∈ W) :
    TopPair.singularHomologyMap (thomPairOverMap F E h) (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1)
        (fiberClass hF W p hp) = fiberClass hF W' p (h hp) := by
  rw [fiberClass, fiberClass, ← ConcreteCategory.comp_apply,
    ← TopPair.singularHomologyMap_comp, fiberThomPairOverMap_comp_thomPairOverMap]

/-! ### Fibre classes along paths -/

/-- A trivialization carries fibre classes to fibre classes of the product bundle. -/
private theorem singularHomologyMap_thomPairOverIso_fiberClass (e : Trivialization F (π F E))
    [e.IsLinear ℝ] {W : Set B} (hW : W ⊆ e.baseSet) {b : B} (hb : b ∈ W)
    (o : Orientation ℝ (E b) (Fin (n + 1))) :
    TopPair.singularHomologyMap (e.thomPairOverIso ℝ hW).hom (ModuleCat.of ℤ (ULift.{w} ℤ))
        (n + 1) (fiberClass hF W ⟨b, o⟩ hb) =
      TopPair.singularHomologyMap (prodThomPairFiberMap F (⟨b, hb⟩ : W))
        (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1)
        ((e.mapOrientation (Fin (n + 1)) (hW hb) o).localOrientation hF).1 := by
  rw [fiberClass, ← ConcreteCategory.comp_apply, ← TopPair.singularHomologyMap_comp,
    Bundle.Trivialization.fiberThomPairOverMap_comp_thomPairOverIso_hom ℝ e hW hb,
    TopPair.singularHomologyMap_comp, ConcreteCategory.comp_apply,
    singularHomologyMap_complZeroPairIso_fiberLocalOrientation]

/-- Product fibre inclusions over joined points agree in the rank degree. -/
private theorem singularHomologyMap_prodThomPairFiberMap_eq_of_joined {W : Type w}
    [TopologicalSpace W] {x y : W} (h : Joined x y) (hm : 0 + finrank ℝ F = n + 1) :
    TopPair.singularHomologyMap (prodThomPairFiberMap F x) (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1) =
      TopPair.singularHomologyMap (prodThomPairFiberMap F y) (ModuleCat.of ℤ (ULift.{w} ℤ))
        (n + 1) := by
  have := Module.finite_of_finrank_eq_succ ((zero_add _).symm.trans hm)
  -- The fibre over `z` is the fibre over `PUnit` followed by the constant map at `z`.
  have hfib (z : W) : prodThomPairFiberMap F z = prodThomPairFiberMap F PUnit.unit ≫
      prodThomPairMap F (ContinuousMap.const PUnit.{w + 1} z) := by
    rw [prodThomPairFiberMap_comp_prodThomPairMap, ContinuousMap.const_apply]
  have hmap (z : W) : TopPair.singularHomologyMap
      (prodThomPairMap F (ContinuousMap.const PUnit.{w + 1} z)) (ModuleCat.of ℤ (ULift.{w} ℤ))
        (n + 1) =
      (prodThomPairSingularHomologyIso _ PUnit.{w + 1} F 0 (n + 1) hm).hom ≫
        ((singularHomologyFunctor (ModuleCat.{w} ℤ) 0).obj (ModuleCat.of ℤ (ULift.{w} ℤ))).map
          (TopCat.ofHom (ContinuousMap.const PUnit.{w + 1} z)) ≫
          (prodThomPairSingularHomologyIso _ W F 0 (n + 1) hm).inv := by
    rw [← prodThomPairSingularHomologyIso_inv_naturality _ PUnit.{w + 1} F
      (ContinuousMap.const PUnit.{w + 1} z) 0 (n + 1) hm, Iso.hom_inv_id_assoc]
  have hconst : ((singularHomologyFunctor (ModuleCat.{w} ℤ) 0).obj
      (ModuleCat.of ℤ (ULift.{w} ℤ))).map (TopCat.ofHom (ContinuousMap.const PUnit.{w + 1} x)) =
      ((singularHomologyFunctor (ModuleCat.{w} ℤ) 0).obj (ModuleCat.of ℤ (ULift.{w} ℤ))).map
        (TopCat.ofHom (ContinuousMap.const PUnit.{w + 1} y)) :=
    singularHomology₀_hom_ext _ fun _ ↦ by
      rw [singularHomology₀Section_naturality, singularHomology₀Section_naturality]
      exact singularHomology₀Section_eq_of_joined _ h
  rw [hfib x, hfib y, TopPair.singularHomologyMap_comp, TopPair.singularHomologyMap_comp, hmap,
    hmap, hconst]

/-- Fibre classes are constant in a sheet over a path in a trivializing set. -/
private theorem fiberClass_eq_of_joinedIn (e : Trivialization F (π F E)) [e.IsLinear ℝ] {W : Set B}
    {b b' : B} {o : Orientation ℝ (E b) (Fin (n + 1))} {o' : Orientation ℝ (E b') (Fin (n + 1))}
    (hb : b ∈ W) (hb' : b' ∈ W) (hbe : b ∈ e.baseSet) (hbe' : b' ∈ e.baseSet)
    (ho : e.mapOrientation (Fin (n + 1)) hbe o = e.mapOrientation (Fin (n + 1)) hbe' o')
    (h : JoinedIn (W ∩ e.baseSet) b b') :
    fiberClass hF W ⟨b, o⟩ hb = fiberClass hF W ⟨b', o'⟩ hb' := by
  have hW : W ∩ e.baseSet ⊆ e.baseSet := inter_subset_right
  -- Over `W ∩ e.baseSet`, `e` identifies the classes with fibre classes of the product bundle.
  have hj : Joined (⟨b, hb, hbe⟩ : ↥(W ∩ e.baseSet)) ⟨b', hb', hbe'⟩ := h.joined_subtype
  have hclass : fiberClass hF (W ∩ e.baseSet) ⟨b, o⟩ ⟨hb, hbe⟩ =
      fiberClass hF (W ∩ e.baseSet) ⟨b', o'⟩ ⟨hb', hbe'⟩ := by
    apply (ModuleCat.mono_iff_injective (TopPair.singularHomologyMap (e.thomPairOverIso ℝ hW).hom
      (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1))).1 inferInstance
    rw [singularHomologyMap_thomPairOverIso_fiberClass hF e hW ⟨hb, hbe⟩,
      singularHomologyMap_thomPairOverIso_fiberClass hF e hW ⟨hb', hbe'⟩, ho,
      singularHomologyMap_prodThomPairFiberMap_eq_of_joined hj (by rw [hF, zero_add])]
  rw [← singularHomologyMap_thomPairOverMap_fiberClass hF (inter_subset_left : W ∩ e.baseSet ⊆ W)
      ⟨b, o⟩ ⟨hb, hbe⟩,
    ← singularHomologyMap_thomPairOverMap_fiberClass hF (inter_subset_left : W ∩ e.baseSet ⊆ W)
      ⟨b', o'⟩ ⟨hb', hbe'⟩, hclass]

/-- Fibre classes are constant along paths in the cover over `W`. -/
private theorem fiberClass_eq_of_path {W : Set B}
    (Γ : C(unitInterval, VectorBundleOrientationCover F E (Fin (n + 1))))
    (hΓ : ∀ t, (Γ t).proj ∈ W) :
    fiberClass hF W (Γ 0) (hΓ 0) = fiberClass hF W (Γ 1) (hΓ 1) := by
  have hι : Fintype.card (Fin (n + 1)) = finrank ℝ F := by rw [Fintype.card_fin, hF]
  have : LocallyPathConnectedSpace unitInterval :=
    Convex.locallyPathConnectedSpace ℝ (convex_Icc (0 : ℝ) 1)
  have hlc : IsLocallyConstant fun t ↦ fiberClass hF W (Γ t) (hΓ t) := by
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun t ↦ ?_
    let e := trivializationAt F E (Γ t).proj
    have hte : (Γ t).proj ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' _
    let ω := e.mapOrientation (Fin (n + 1)) hte (Γ t).orientation
    have hO : {s | Γ s ∈ sheet e ω} ∈ 𝓝 t :=
      ((isOpen_sheet hι e ω).preimage Γ.continuous).mem_nhds (mem_sheet_iff.2 ⟨hte, rfl⟩)
    filter_upwards [pathComponentIn_mem_nhds hO] with s hs
    have hsO : s ∈ {s | Γ s ∈ sheet e ω} := pathComponentIn_subset hs
    obtain ⟨hse, hsω⟩ := mem_sheet_iff.1 hsO
    -- The base points are joined in `W` inside the base set of `e`, by the projection of `Γ`.
    have hj : JoinedIn (W ∩ e.baseSet) (Γ t).proj (Γ s).proj := by
      refine (hs.map (continuous_proj.comp Γ.continuous).continuousOn).mono ?_
      rintro _ ⟨u, hu, rfl⟩
      exact ⟨hΓ u, (mem_sheet_iff.1 hu).1⟩
    exact (fiberClass_eq_of_joinedIn hF e (o := (Γ t).orientation) (o' := (Γ s).orientation)
      (hΓ t) (hΓ s) hte hse hsω.symm hj).symm
  exact hlc.apply_eq_of_preconnectedSpace 0 1

/-- The fibre class depends only on the point of the cover. -/
private theorem fiberClass_congr {W : Set B}
    {p q : VectorBundleOrientationCover F E (Fin (n + 1))} (h : p = q) (hp : p.proj ∈ W)
    (hq : q.proj ∈ W) : fiberClass hF W p hp = fiberClass hF W q hq := by
  subst h
  rfl

/-- Monodromy along a path in `W` preserves fibre classes. -/
private theorem fiberClass_monodromy {W : Set B} {x y : B} (γ : Path x y) (hγ : ∀ t, γ t ∈ W)
    (p : (proj ⁻¹' {x} : Set (VectorBundleOrientationCover F E (Fin (n + 1)))))
    (hp : p.1.proj ∈ W)
    (hq : ((isCoveringMap_proj (by rw [Fintype.card_fin, hF])).monodromy
      (Path.Homotopic.Quotient.mk γ) p).1.proj ∈ W) :
    fiberClass hF W ((isCoveringMap_proj (by rw [Fintype.card_fin, hF])).monodromy
      (Path.Homotopic.Quotient.mk γ) p).1 hq = fiberClass hF W p.1 hp := by
  have hι : Fintype.card (Fin (n + 1)) = finrank ℝ F := by rw [Fintype.card_fin, hF]
  let cov := isCoveringMap_proj (F := F) (E := E) hι
  let Γ := cov.liftPath γ p.1 (γ.source.trans p.2.symm)
  have hΓ (t : unitInterval) : (Γ t).proj ∈ W := by
    have := congr_fun (cov.liftPath_lifts γ p.1 (γ.source.trans p.2.symm)) t
    simp only [Function.comp_apply] at this
    rw [this]
    exact hγ t
  rw [fiberClass_congr hF (IsCoveringMap.coe_monodromy_mk cov γ p) hq (hΓ 1),
    ← fiberClass_eq_of_path hF Γ hΓ]
  exact fiberClass_congr hF (cov.liftPath_zero γ p.1 _) _ _

/-! ### The map from twisted zeroth homology -/

/-- A chosen orientation of the fibre over `b`. -/
private def fiberOrientation (b : B) : Orientation ℝ (E b) (Fin (n + 1)) :=
  ((trivializationAt F E b).mapOrientation (Fin (n + 1))
    (FiberBundle.mem_baseSet_trivializationAt' b)).symm
    (haveI := Module.finite_of_finrank_eq_succ hF; (Module.finBasisOfFinrankEq ℝ F hF).orientation)

/-- The map `o(E)_b ⟶ Hₙ₊₁(E|_W, E₀|_W; ℤ)`, `f ↦ f o • [o]`. -/
private def fiberClassHom (W : Set B) {b : B} (hb : b ∈ W) :
    (signLocalSystem F E ℤ ((Fintype.card_fin _).trans hF.symm)).obj (FundamentalGroupoid.mk b) ⟶
      ((thomPairOver F E W).singularHomology (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1) :
        ModuleCat.{w} ℤ) :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ _ (fiberClass hF W ⟨b, fiberOrientation hF b⟩ hb) ∘ₗ
    (signLocalSystemFiberEquiv ((Fintype.card_fin _).trans hF.symm)
      (fiberOrientation hF b)).toLinearMap)

private theorem fiberClassHom_apply_fiberOrientation (W : Set B) {b : B} (hb : b ∈ W)
    (f : (signLocalSystem F E ℤ ((Fintype.card_fin _).trans hF.symm)).obj
      (FundamentalGroupoid.mk b)) :
    fiberClassHom hF W hb f = signLocalSystemFiberEquiv ((Fintype.card_fin _).trans hF.symm)
      (fiberOrientation hF b) f • fiberClass hF W ⟨b, fiberOrientation hF b⟩ hb :=
  -- The module structure of the homology object and the `ℤ`-action agree only propositionally.
  int_smul_eq_zsmul _ _ _

/-- `fiberClassHom` evaluated at any orientation of the fibre. -/
private theorem fiberClassHom_apply (W : Set B) {b : B} (hb : b ∈ W)
    (p : (proj ⁻¹' {b} : Set (VectorBundleOrientationCover F E (Fin (n + 1)))))
    (hp : p.1.proj ∈ W) (f : (signLocalSystem F E ℤ ((Fintype.card_fin _).trans hF.symm)).obj
      (FundamentalGroupoid.mk b)) :
    fiberClassHom hF W hb f =
      (signLocalSystemObjEquiv ((Fintype.card_fin _).trans hF.symm) (FundamentalGroupoid.mk b) f :
        (proj ⁻¹' {b} : Set (VectorBundleOrientationCover F E (Fin (n + 1)))) → ℤ) p •
        fiberClass hF W p.1 hp := by
  obtain ⟨⟨b', o⟩, hb'⟩ := p
  obtain rfl : b' = b := hb'
  -- The two orientations of `E_b` are `o₀` and `-o₀`, as one sees in a trivialization.
  have := Module.finite_of_finrank_eq_succ hF
  set e := trivializationAt F E b'
  have hbe : b' ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' b'
  have ho : o = fiberOrientation hF b' ∨ o = -fiberOrientation hF b' := by
    rcases Orientation.eq_or_eq_neg (e.mapOrientation (Fin (n + 1)) hbe o)
      (e.mapOrientation (Fin (n + 1)) hbe (fiberOrientation hF b'))
      ((Fintype.card_fin _).trans hF.symm) with h | h
    · exact .inl ((e.mapOrientation (Fin (n + 1)) hbe).injective h)
    · rw [← Bundle.Trivialization.mapOrientation_neg] at h
      exact .inr ((e.mapOrientation (Fin (n + 1)) hbe).injective h)
  rcases ho with rfl | rfl
  · rw [fiberClassHom_apply_fiberOrientation, signLocalSystemFiberEquiv_apply]
  · rw [fiberClass_mk_neg, ← signLocalSystemFiberEquiv_apply, signLocalSystemFiberEquiv_neg,
      fiberClassHom_apply_fiberOrientation, neg_zsmul, zsmul_neg, neg_neg]

/-- The fibre class maps are compatible with transport along paths in `W`. -/
private theorem signLocalSystem_map_comp_fiberClassHom (W : Set B) {x y : B} (γ : Path x y)
    (hγ : ∀ t, γ t ∈ W) (hx : x ∈ W) (hy : y ∈ W) :
    (signLocalSystem F E ℤ ((Fintype.card_fin _).trans hF.symm)).map
        (FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk γ)) ≫ fiberClassHom hF W hy =
      fiberClassHom hF W hx := by
  refine ModuleCat.hom_ext (LinearMap.ext fun f ↦ ?_)
  let hι : Fintype.card (Fin (n + 1)) = finrank ℝ F := (Fintype.card_fin _).trans hF.symm
  let cov := isCoveringMap_proj (F := F) (E := E) hι
  -- Evaluate at the chosen orientation over `y`, and at its transport back to `x`.
  let p : (proj ⁻¹' {y} : Set (VectorBundleOrientationCover F E (Fin (n + 1)))) :=
    ⟨⟨y, fiberOrientation hF (E := E) y⟩, rfl⟩
  let q := cov.monodromy (Path.Homotopic.Quotient.mk γ.symm) p
  have hq : q.1.proj ∈ W := by
    rw [show q.1.proj = x from q.2]
    exact hx
  have hinv : inv (FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk γ)) =
      FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk γ.symm) := by
    rw [← Groupoid.inv_eq_inv]
    rfl
  have hm : cov.monodromy (inv (FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk γ))) p =
      q := by
    rw [hinv]
  rw [ModuleCat.comp_apply, fiberClassHom_apply hF W hy p hy, fiberClassHom_apply hF W hx q hq,
    ← fiberClass_monodromy hF γ.symm (fun t ↦ hγ _) p hy hq, signLocalSystemObjEquiv_map_apply, hm]

/-- The fibre class maps over `W` as a cocone over `o(E)` restricted to `W`. -/
private def fiberClassCocone (W : Set B) :
    Cocone ((LocalCoefficientSystem.pullback (X := TopCat.of W) (ContinuousMap.subtypeVal W)).obj
      (signLocalSystem F E ℤ ((Fintype.card_fin _).trans hF.symm))) where
  pt := ((thomPairOver F E W).singularHomology (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1) :
    ModuleCat.{w} ℤ)
  ι :=
    { app x := fiberClassHom hF W (ContinuousMap.subtypeVal_apply W x.as ▸ x.as.2)
      naturality x y γ := by
        refine Eq.trans ?_ (Category.comp_id _).symm
        induction γ using Path.Homotopic.Quotient.ind with
        | mk γ =>
          -- The fibres agree with those of `o(E)` only up to unfolding the pullback.
          exact signLocalSystem_map_comp_fiberClassHom hF W (γ.map continuous_subtype_val)
            (fun t ↦ (γ t).2) x.as.2 y.as.2 }

/-- The map `H₀(W; o(E)) ⟶ Hₙ₊₁(E|_W, E₀|_W; ℤ)`. -/
private def fiberClassDesc (W : Set B) :
    ((LocalCoefficientSystem.pullback (X := TopCat.of W) (ContinuousMap.subtypeVal W)).obj
      (signLocalSystem F E ℤ ((Fintype.card_fin _).trans hF.symm))).twistedHomology 0 ⟶
      ((thomPairOver F E W).singularHomology (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1) :
        ModuleCat.{w} ℤ) :=
  (LocalCoefficientSystem.isColimitTwistedHomology₀Cocone _).desc (fiberClassCocone hF W)

@[reassoc]
private theorem ιTwistedHomology₀_fiberClassDesc (W : Set B) (x : W) :
    LocalCoefficientSystem.ιTwistedHomology₀ _ x ≫ fiberClassDesc hF (E := E) W =
      fiberClassHom hF W x.2 :=
  (LocalCoefficientSystem.isColimitTwistedHomology₀Cocone _).fac (fiberClassCocone hF W)
    (FundamentalGroupoid.mk x)

/-- The fibre class maps commute with the restriction maps of the Thom pairs. -/
@[reassoc]
private theorem fiberClassHom_comp_singularHomologyMap_thomPairOverMap {W W' : Set B} (h : W ⊆ W')
    {b : B} (hb : b ∈ W) :
    fiberClassHom hF W hb ≫ TopPair.singularHomologyMap (thomPairOverMap F E h)
      (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1) = fiberClassHom hF W' (h hb) := by
  refine ModuleCat.hom_ext (LinearMap.ext fun f ↦ ?_)
  rw [ModuleCat.comp_apply, fiberClassHom_apply_fiberOrientation,
    fiberClassHom_apply_fiberOrientation, map_zsmul, singularHomologyMap_thomPairOverMap_fiberClass]

/-- The restriction `H₀(W; o(E)) ⟶ H₀(W'; o(E))` for `W ⊆ W'`. -/
private def twistedRestrict {W W' : Set B} (h : W ⊆ W') :
    ((LocalCoefficientSystem.pullback (X := TopCat.of W) (ContinuousMap.subtypeVal W)).obj
      (signLocalSystem F E ℤ ((Fintype.card_fin _).trans hF.symm))).twistedHomology 0 ⟶
    ((LocalCoefficientSystem.pullback (X := TopCat.of W') (ContinuousMap.subtypeVal W')).obj
      (signLocalSystem F E ℤ ((Fintype.card_fin _).trans hF.symm))).twistedHomology 0 :=
  LocalCoefficientSystem.twistedHomologyCoefficientMap
      ((LocalCoefficientSystem.pullbackCompIso (TopCat.ofHom (ContinuousMap.inclusion h)).hom
        (TopCat.ofHom (ContinuousMap.subtypeVal W')).hom).hom.app
          (signLocalSystem F E ℤ ((Fintype.card_fin _).trans hF.symm))) 0 ≫
    LocalCoefficientSystem.twistedHomologyMap (TopCat.ofHom (ContinuousMap.inclusion h))
      ((LocalCoefficientSystem.pullback (TopCat.ofHom (ContinuousMap.subtypeVal W')).hom).obj
        (signLocalSystem F E ℤ ((Fintype.card_fin _).trans hF.symm))) 0

/-- The maps over `W ⊆ W'` commute with the restrictions. -/
private theorem twistedRestrict_fiberClassDesc {W W' : Set B} (h : W ⊆ W') :
    twistedRestrict hF (E := E) h ≫ fiberClassDesc hF W' = fiberClassDesc hF W ≫
      TopPair.singularHomologyMap (thomPairOverMap F E h) (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1) :=
  LocalCoefficientSystem.twistedHomology₀_hom_ext _ fun x ↦ by
    rw [twistedRestrict, ← Category.assoc, ιTwistedHomology₀_fiberClassDesc_assoc]
    -- The coefficient comparison is the identity; fibres agree only up to unfolding pullbacks.
    erw [LocalCoefficientSystem.ιTwistedHomology₀_coefficientMap_assoc,
      LocalCoefficientSystem.pullbackCompIso_hom_app_app, Category.id_comp,
      LocalCoefficientSystem.ιTwistedHomology₀_homologyMap (L := (LocalCoefficientSystem.pullback
        (TopCat.ofHom (ContinuousMap.subtypeVal W')).hom).obj
          (signLocalSystem F E ℤ ((Fintype.card_fin _).trans hF.symm))),
      ιTwistedHomology₀_fiberClassDesc]
    exact (fiberClassHom_comp_singularHomologyMap_thomPairOverMap hF h x.2).symm

/-- The restriction carries the class of a point to that of the same point. -/
private theorem ιTwistedHomology₀_twistedRestrict_assoc {W W' : Set B} (h : W ⊆ W') (x : W)
    {T : ModuleCat.{w} ℤ}
    (g : ((LocalCoefficientSystem.pullback (X := TopCat.of W') (ContinuousMap.subtypeVal W')).obj
      (signLocalSystem F E ℤ ((Fintype.card_fin _).trans hF.symm))).twistedHomology 0 ⟶ T) :
    LocalCoefficientSystem.ιTwistedHomology₀ _ x ≫ twistedRestrict hF (E := E) h ≫ g =
      (LocalCoefficientSystem.ιTwistedHomology₀
        ((LocalCoefficientSystem.pullback (X := TopCat.of W') (ContinuousMap.subtypeVal W')).obj
          (signLocalSystem F E ℤ ((Fintype.card_fin _).trans hF.symm))) (inclusion h x) ≫ g :
        ((LocalCoefficientSystem.pullback (X := TopCat.of W) (ContinuousMap.subtypeVal W)).obj
          (signLocalSystem F E ℤ ((Fintype.card_fin _).trans hF.symm))).obj
            (FundamentalGroupoid.mk x) ⟶ T) := by
  rw [twistedRestrict, ← Category.assoc]
  -- The coefficient comparison is the identity; fibres agree only up to unfolding pullbacks.
  erw [LocalCoefficientSystem.ιTwistedHomology₀_coefficientMap_assoc,
    LocalCoefficientSystem.pullbackCompIso_hom_app_app, Category.id_comp,
    LocalCoefficientSystem.ιTwistedHomology₀_homologyMap (L := (LocalCoefficientSystem.pullback
      (TopCat.ofHom (ContinuousMap.subtypeVal W')).hom).obj
        (signLocalSystem F E ℤ ((Fintype.card_fin _).trans hF.symm)))]
  rfl

/-- The restriction maps compose. -/
private theorem twistedRestrict_comp {W W' W'' : Set B} (h : W ⊆ W') (h' : W' ⊆ W'') :
    twistedRestrict hF (E := E) h ≫ twistedRestrict hF h' = twistedRestrict hF (h.trans h') :=
  LocalCoefficientSystem.twistedHomology₀_hom_ext _ fun x ↦ by
    rw [ιTwistedHomology₀_twistedRestrict_assoc]
    have h₁ := (ιTwistedHomology₀_twistedRestrict_assoc hF (E := E) h' (inclusion h x)
      (𝟙 _)).trans (ιTwistedHomology₀_twistedRestrict_assoc hF (E := E) (h.trans h') x (𝟙 _)).symm
    rwa [Category.comp_id, Category.comp_id] at h₁

/-! ### Over a trivializing set -/

omit [∀ b, TopologicalSpace (E b)] [TopologicalSpace (TotalSpace F E)] [FiberBundle F E]
  [VectorBundle ℝ F E] in
/-- An orientation of `F` whose local orientation goes to the classes of points. -/
private theorem exists_orientation_singularHomologyMap_prodThomPairFiberMap
    [FiniteDimensional ℝ F] :
    ∃ ω : Orientation ℝ F (Fin (n + 1)), ∀ (W : Type w) [TopologicalSpace W] (x : W),
      TopPair.singularHomologyMap (prodThomPairFiberMap F x) (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1)
          (ω.localOrientation hF).1 =
        (prodThomPairSingularHomologyIso (ModuleCat.of ℤ (ULift.{w} ℤ)) W F 0 (n + 1)
          (by rw [hF, zero_add])).inv
          (singularHomology₀Section (ModuleCat.of ℤ (ULift.{w} ℤ)) (X := TopCat.of W) x 1) := by
  have hm : 0 + finrank ℝ F = n + 1 := by rw [hF, zero_add]
  -- The local homology of `F` at `0` is `ℤ`, through the product over a point and its `H₀`.
  let e : localHomology (A := ModuleCat.{w} ℤ) (ModuleCat.of ℤ (ULift.{w} ℤ)) ({0} : Set F)
      (n + 1) ≅ ModuleCat.of ℤ (ULift.{w} ℤ) :=
    { hom := TopPair.singularHomologyMap (complZeroPairIsoProdThomPair F).hom _ (n + 1)
      inv := TopPair.singularHomologyMap (complZeroPairIsoProdThomPair F).inv _ (n + 1)
      hom_inv_id := by
        rw [← TopPair.singularHomologyMap_comp, Iso.hom_inv_id, TopPair.singularHomologyMap_id]
      inv_hom_id := by
        rw [← TopPair.singularHomologyMap_comp, Iso.inv_hom_id,
          TopPair.singularHomologyMap_id] } ≪≫
      prodThomPairSingularHomologyIso (ModuleCat.of ℤ (ULift.{w} ℤ)) PUnit.{w + 1} F 0 (n + 1)
        hm ≪≫
      { hom := (TopCat.of PUnit.{w + 1}).singularHomology₀ε (ModuleCat.of ℤ (ULift.{w} ℤ))
        inv := singularHomology₀Section (ModuleCat.of ℤ (ULift.{w} ℤ)) PUnit.unit
        hom_inv_id := singularHomology₀ε_singularHomology₀Section _ _
        inv_hom_id := singularHomology₀Section_singularHomology₀ε _ _ }
  obtain ⟨ω, hω⟩ : ∃ ω : Orientation ℝ F (Fin (n + 1)), (ω.localOrientation hF).1 = e.inv 1 := by
    let ω₀ := (Module.finBasisOfFinrankEq ℝ F hF).orientation
    rcases IsLocalOrientation.eq_or_eq_neg e (ω₀.localOrientation hF).2
      (isLocalOrientation_inv_one e) with h | h
    · exact ⟨ω₀, h.symm⟩
    · exact ⟨-ω₀, by rw [Orientation.localOrientation_neg, LocalOrientation.coe_neg, h]⟩
  refine ⟨ω, fun W _ x ↦ ?_⟩
  -- The fibre over `x` is the fibre over the point followed by the constant map at `x`.
  have hfib : (complZeroPairIsoProdThomPair F).inv ≫ prodThomPairFiberMap F x =
      prodThomPairMap F (ContinuousMap.const PUnit.{w + 1} x) := by
    have h : prodThomPairFiberMap F x = prodThomPairFiberMap F PUnit.unit ≫
        prodThomPairMap F (ContinuousMap.const PUnit.{w + 1} x) := by
      rw [prodThomPairFiberMap_comp_prodThomPairMap, ContinuousMap.const_apply]
    rw [h, ← complZeroPairIsoProdThomPair_hom, Iso.inv_hom_id_assoc]
  have hmor : ((singularHomology₀Section (ModuleCat.of ℤ (ULift.{w} ℤ)) PUnit.unit ≫
      (prodThomPairSingularHomologyIso (ModuleCat.of ℤ (ULift.{w} ℤ)) PUnit.{w + 1} F 0 (n + 1)
        hm).inv) ≫ TopPair.singularHomologyMap (complZeroPairIsoProdThomPair F).inv _ (n + 1)) ≫
      TopPair.singularHomologyMap (prodThomPairFiberMap F x) _ (n + 1) =
      singularHomology₀Section (ModuleCat.of ℤ (ULift.{w} ℤ)) (X := TopCat.of W) x ≫
        (prodThomPairSingularHomologyIso (ModuleCat.of ℤ (ULift.{w} ℤ)) W F 0 (n + 1) hm).inv := by
    rw [Category.assoc, ← TopPair.singularHomologyMap_comp, hfib, Category.assoc,
      prodThomPairSingularHomologyIso_inv_naturality (ModuleCat.of ℤ (ULift.{w} ℤ)) PUnit.{w + 1} F
        (ContinuousMap.const PUnit.{w + 1} x) 0 (n + 1) hm, ← Category.assoc,
      singularHomology₀Section_naturality]
    rfl
  rw [hω]
  exact ConcreteCategory.congr_hom hmor 1

omit [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E] in
private theorem mk_mapOrientation_symm_congr (e : Trivialization F (π F E)) [e.IsLinear ℝ]
    (ω : Orientation ℝ F (Fin (n + 1))) {b b' : B} (h : b = b') (hb : b ∈ e.baseSet)
    (hb' : b' ∈ e.baseSet) :
    (⟨b, (e.mapOrientation (Fin (n + 1)) hb).symm ω⟩ :
      VectorBundleOrientationCover F E (Fin (n + 1))) =
      ⟨b', (e.mapOrientation (Fin (n + 1)) hb').symm ω⟩ := by
  subst h
  rfl

/-- Monodromy along a path in a trivializing set stays in a sheet. -/
private theorem monodromy_mk_mapOrientation_symm (e : Trivialization F (π F E))
    [MemTrivializationAtlas e] (ω : Orientation ℝ F (Fin (n + 1))) {x y : B} (γ : Path x y)
    (hγ : ∀ t, γ t ∈ e.baseSet) (hx : x ∈ e.baseSet) (hy : y ∈ e.baseSet) :
    (((isCoveringMap_proj ((Fintype.card_fin _).trans hF.symm)).monodromy
      (Path.Homotopic.Quotient.mk γ) ⟨⟨x, (e.mapOrientation (Fin (n + 1)) hx).symm ω⟩, rfl⟩ :
        VectorBundleOrientationCover F E (Fin (n + 1)))) =
      ⟨y, (e.mapOrientation (Fin (n + 1)) hy).symm ω⟩ := by
  let hι : Fintype.card (Fin (n + 1)) = finrank ℝ F := (Fintype.card_fin _).trans hF.symm
  -- The orientations read as `ω` in `e` form a continuous lift of `γ`.
  let Γ : C(unitInterval, VectorBundleOrientationCover F E (Fin (n + 1))) :=
    ⟨fun t ↦ ⟨γ t, (e.mapOrientation (Fin (n + 1)) (hγ t)).symm ω⟩,
      (continuous_mk_mapOrientation_symm hι e ω).comp (γ.continuous.subtype_mk hγ)⟩
  rw [IsCoveringMap.monodromy_eq_apply_one (isCoveringMap_proj hι) (Γ := Γ) (funext fun _ ↦ rfl)
    (mk_mapOrientation_symm_congr e ω γ.source (hγ 0) hx)]
  exact mk_mapOrientation_symm_congr e ω γ.target (hγ 1) hy

/-- Transport in a trivializing set preserves the coefficient `1` at a sheet. -/
private theorem signLocalSystem_map_signLocalSystemFiberEquiv_symm_one
    (e : Trivialization F (π F E)) [MemTrivializationAtlas e] (ω : Orientation ℝ F (Fin (n + 1)))
    {x y : B} (γ : Path x y)
    (hγ : ∀ t, γ t ∈ e.baseSet) (hx : x ∈ e.baseSet) (hy : y ∈ e.baseSet) :
    (signLocalSystem F E ℤ ((Fintype.card_fin _).trans hF.symm)).map
        (FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk γ))
        ((signLocalSystemFiberEquiv ((Fintype.card_fin _).trans hF.symm)
          ((e.mapOrientation (Fin (n + 1)) hx).symm ω)).symm 1) =
      (signLocalSystemFiberEquiv ((Fintype.card_fin _).trans hF.symm)
        ((e.mapOrientation (Fin (n + 1)) hy).symm ω)).symm 1 := by
  let hι : Fintype.card (Fin (n + 1)) = finrank ℝ F := (Fintype.card_fin _).trans hF.symm
  apply (signLocalSystemFiberEquiv hι ((e.mapOrientation (Fin (n + 1)) hy).symm ω)).injective
  have hinv : inv (FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk γ)) =
      FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk γ.symm) := by
    rw [← Groupoid.inv_eq_inv]
    rfl
  have hm := monodromy_mk_mapOrientation_symm hF e ω γ.symm (fun t ↦ hγ _) hy hx
  rw [LinearEquiv.apply_symm_apply, signLocalSystemFiberEquiv_apply,
    signLocalSystemObjEquiv_map_apply, hinv]
  have hq : (isCoveringMap_proj hι).monodromy (Path.Homotopic.Quotient.mk γ.symm)
      ⟨⟨y, (e.mapOrientation (Fin (n + 1)) hy).symm ω⟩, rfl⟩ =
      ⟨⟨x, (e.mapOrientation (Fin (n + 1)) hx).symm ω⟩, rfl⟩ := Subtype.ext hm
  rw [hq, ← signLocalSystemFiberEquiv_apply, LinearEquiv.apply_symm_apply]

/-- Over a trivializing set, fibre classes of a sheet go to the classes of points. -/
private theorem singularHomologyMap_thomPairOverIso_fiberClass_mapOrientation_symm
    [FiniteDimensional ℝ F] (e : Trivialization F (π F E)) [e.IsLinear ℝ] {W : Set B}
    (hW : W ⊆ e.baseSet) {ω : Orientation ℝ F (Fin (n + 1))}
    (hω : ∀ (W : Type w) [TopologicalSpace W] (x : W),
      TopPair.singularHomologyMap (prodThomPairFiberMap F x) (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1)
          (ω.localOrientation hF).1 =
        (prodThomPairSingularHomologyIso (ModuleCat.of ℤ (ULift.{w} ℤ)) W F 0 (n + 1)
          (by rw [hF, zero_add])).inv
          (singularHomology₀Section (ModuleCat.of ℤ (ULift.{w} ℤ)) (X := TopCat.of W) x 1))
    (x : W) :
    TopPair.singularHomologyMap (e.thomPairOverIso ℝ hW).hom (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1)
        (fiberClass hF W ⟨x, (e.mapOrientation (Fin (n + 1)) (hW x.2)).symm ω⟩ x.2) =
      (prodThomPairSingularHomologyIso (ModuleCat.of ℤ (ULift.{w} ℤ)) W F 0 (n + 1)
          (by rw [hF, zero_add])).inv
        (singularHomology₀Section (ModuleCat.of ℤ (ULift.{w} ℤ)) (X := TopCat.of W) x 1) := by
  rw [singularHomologyMap_thomPairOverIso_fiberClass, Equiv.apply_symm_apply, hω]

/-- **Over a trivializing set** the map is an isomorphism. -/
private theorem isIso_fiberClassDesc_of_subset (e : Trivialization F (π F E))
    [MemTrivializationAtlas e] {W : Set B} (hW : W ⊆ e.baseSet) :
    IsIso (fiberClassDesc hF (E := E) W) := by
  have := Module.finite_of_finrank_eq_succ hF
  let hι : Fintype.card (Fin (n + 1)) = finrank ℝ F := (Fintype.card_fin _).trans hF.symm
  have hm : 0 + finrank ℝ F = n + 1 := by rw [hF, zero_add]
  obtain ⟨ω, hω⟩ := exists_orientation_singularHomologyMap_prodThomPairFiberMap hF
  let L := (LocalCoefficientSystem.pullback (X := TopCat.of W) (ContinuousMap.subtypeVal W)).obj
    (signLocalSystem F E ℤ hι)
  let o (x : W) : Orientation ℝ (E x) (Fin (n + 1)) :=
    (e.mapOrientation (Fin (n + 1)) (hW x.2)).symm ω
  -- The coefficient over `x` taking the value `1` at the orientation read as `ω` in `e`.
  let σ (x : W) : L.obj (FundamentalGroupoid.mk x) := (signLocalSystemFiberEquiv hι (o x)).symm 1
  have hσ {x y : W} (γ : Path x y) : L.ιTwistedHomology₀ x (σ x) = L.ιTwistedHomology₀ y (σ y) := by
    have h := ConcreteCategory.congr_hom
      (LocalCoefficientSystem.map_ιTwistedHomology₀ L (FundamentalGroupoid.fromPath
        (Path.Homotopic.Quotient.mk γ))) (σ x)
    refine h.symm.trans (congrArg (L.ιTwistedHomology₀ y) ?_)
    exact signLocalSystem_map_signLocalSystemFiberEquiv_symm_one hF e ω
      (γ.map continuous_subtype_val) (fun t ↦ hW (γ t).2) (hW x.2) (hW y.2)
  -- The inverse on `H₀(W; ℤ)`: the class of a point `x` goes to the class of `σ x`.
  obtain ⟨D, hD⟩ : ∃ D : ((singularHomologyFunctor (ModuleCat.{w} ℤ) 0).obj
      (ModuleCat.of ℤ (ULift.{w} ℤ))).obj (TopCat.of W) ⟶ L.twistedHomology 0,
      ∀ x : W, singularHomology₀Section (ModuleCat.of ℤ (ULift.{w} ℤ)) (X := TopCat.of W) x ≫ D =
        ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ (L.twistedHomology 0)
          (L.ιTwistedHomology₀ x (σ x)) ∘ₗ ULift.moduleEquiv.toLinearMap) :=
    ⟨singularHomology₀Desc (C := ModuleCat.{w} ℤ) (X := TopCat.of W) (Y := L.twistedHomology 0) _
      (fun x ↦ ModuleCat.ofHom
      (LinearMap.toSpanSingleton ℤ (L.twistedHomology 0) (L.ιTwistedHomology₀ x (σ x)) ∘ₗ
        ULift.moduleEquiv.toLinearMap))
      (fun x y γ ↦ by rw [hσ γ]), fun x ↦
        singularHomology₀Section_singularHomology₀Desc (C := ModuleCat.{w} ℤ) (X := TopCat.of W)
          _ _ _ x⟩
  have hD₁ (x : W) : D (singularHomology₀Section (ModuleCat.of ℤ (ULift.{w} ℤ)) (X := TopCat.of W) x
      1) = L.ιTwistedHomology₀ x (σ x) := by
    rw [← ConcreteCategory.comp_apply, hD]
    exact (int_smul_eq_zsmul _ _ _).trans (one_zsmul _)
  let P := prodThomPairSingularHomologyIso (ModuleCat.of ℤ (ULift.{w} ℤ)) W F 0 (n + 1) hm
  let T := TopPair.singularHomologyMap (e.thomPairOverIso ℝ hW).hom (ModuleCat.of ℤ (ULift.{w} ℤ))
    (n + 1)
  have hT (x : W) : T (fiberClass hF W ⟨x, o x⟩ x.2) =
      P.inv (singularHomology₀Section (ModuleCat.of ℤ (ULift.{w} ℤ)) (X := TopCat.of W) x 1) :=
    singularHomologyMap_thomPairOverIso_fiberClass_mapOrientation_symm hF e hW hω x
  have hf (x : W) (f : L.obj (FundamentalGroupoid.mk x)) :
      fiberClassDesc hF W (L.ιTwistedHomology₀ x f) =
        signLocalSystemFiberEquiv hι (o x) f • fiberClass hF W ⟨x, o x⟩ x.2 := by
    rw [← ConcreteCategory.comp_apply, ιTwistedHomology₀_fiberClassDesc]
    -- The fibres of `L` are those of `o(E)` only up to unfolding the pullback.
    exact (fiberClassHom_apply hF W x.2 ⟨⟨x, o x⟩, rfl⟩ x.2 f).trans
      (congrArg (· • fiberClass hF W ⟨x, o x⟩ x.2)
        (signLocalSystemFiberEquiv_apply hι (o x) f).symm)
  have hsec (x : W) (k : ULift.{w} ℤ) :
      singularHomology₀Section (ModuleCat.of ℤ (ULift.{w} ℤ)) (X := TopCat.of W) x k =
        k.down •
          singularHomology₀Section (ModuleCat.of ℤ (ULift.{w} ℤ)) (X := TopCat.of W) x 1 := by
    rw [← map_zsmul]
    congr 1
    ext
    simp
  -- `D` followed by the map inverts the identification of `Hₙ₊₁(E|_W, E₀|_W; ℤ)` with `H₀(W)`.
  have hDf : D ≫ fiberClassDesc hF W = P.inv ≫ inv T := by
    refine singularHomology₀_hom_ext _ fun x ↦ ModuleCat.hom_ext (LinearMap.ext fun k ↦ ?_)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
    rw [hsec, map_zsmul, map_zsmul, hD₁, hf, LinearEquiv.apply_symm_apply, one_zsmul, map_zsmul,
      map_zsmul, ← hT, ← ConcreteCategory.comp_apply, IsIso.hom_inv_id, ConcreteCategory.id_apply]
  refine ⟨T ≫ P.hom ≫ D, ?_, ?_⟩
  · refine LocalCoefficientSystem.twistedHomology₀_hom_ext _ fun x ↦
      ModuleCat.hom_ext (LinearMap.ext fun f ↦ ?_)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, Category.comp_id]
    rw [hf, map_zsmul, map_zsmul, map_zsmul, hT, Iso.inv_hom_id_apply, hD₁, ← map_zsmul]
    congr 1
    apply (signLocalSystemFiberEquiv hι (o x)).injective
    -- The fibres of `L` are those of `o(E)` only up to unfolding the pullback.
    erw [map_zsmul, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]
  · rw [Category.assoc, Category.assoc, hDf, Iso.hom_inv_id_assoc, IsIso.hom_inv_id]

/-! ### Gluing over unions -/

/-- Restriction in twisted homology, read through the maps over `W` and `W'`. -/
@[reassoc]
private theorem fiberClassDesc_comp_singularHomologyMap_comp_inv {W W' : Set B} (h : W ⊆ W')
    [IsIso (fiberClassDesc hF (E := E) W')] :
    fiberClassDesc hF W ≫ TopPair.singularHomologyMap (thomPairOverMap F E h)
        (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1) ≫ inv (fiberClassDesc hF W') =
      twistedRestrict hF h := by
  rw [← Category.assoc, ← twistedRestrict_fiberClassDesc, Category.assoc, IsIso.hom_inv_id,
    Category.comp_id]

/-- **The Mayer–Vietoris step** for the maps over `U`, `V` and `U ∪ V`. -/
private theorem isIso_fiberClassDesc_union {U V : Set B} (hU : IsOpen U) (hV : IsOpen V)
    [IsIso (fiberClassDesc hF (E := E) U)] [IsIso (fiberClassDesc hF (E := E) V)]
    [Epi (fiberClassDesc hF (E := E) (U ∩ V))]
    (hUV : ∀ m, m + 1 = n + 1 →
      IsZero ((thomPairOver F E (U ∩ V)).singularHomology (ModuleCat.of ℤ (ULift.{w} ℤ)) m)) :
    IsIso (fiberClassDesc hF (E := E) (U ∪ V)) := by
  let S := ShortComplex.mk _ _ (singularHomology_thomPairOver_mayerVietoris_comp_eq_zero
    (F := F) (E := E) (U := U) (V := V) (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1))
  have hS : S.Exact :=
    singularHomology_thomPairOver_mayerVietoris_exact (ModuleCat.of ℤ (ULift.{w} ℤ)) hU hV _
  have : Epi S.g := epi_singularHomology_thomPairOver_union (ModuleCat.of ℤ (ULift.{w} ℤ)) hU hV hUV
  -- The inverse map, on the middle term of the Mayer–Vietoris sequence.
  let φ : S.X₂ ⟶ _ :=
    biprod.desc (inv (fiberClassDesc hF U) ≫ twistedRestrict hF (E := E) subset_union_left)
      (inv (fiberClassDesc hF V) ≫ twistedRestrict hF (E := E) subset_union_right)
  -- It vanishes on the image of the first map: both restrictions from `U ∩ V` agree.
  have hφ : S.f ≫ φ = 0 := by
    rw [← cancel_epi (fiberClassDesc hF (E := E) (U ∩ V)), comp_zero]
    simp only [S, φ, biprod.lift_desc, Preadditive.neg_comp, Preadditive.comp_add,
      Preadditive.comp_neg, fiberClassDesc_comp_singularHomologyMap_comp_inv_assoc,
      twistedRestrict_comp, add_neg_eq_zero]
  let Φ := hS.gIsCokernel.desc (CokernelCofork.ofπ φ hφ)
  have hgΦ : S.g ≫ Φ = φ := hS.gIsCokernel.fac (CokernelCofork.ofπ φ hφ) WalkingParallelPair.one
  -- On the classes over `U` and over `V`, `Φ` is the inverse of the map over `U` or `V`.
  have hΦ {W : Set B} (hW : W ⊆ U ∪ V) [IsIso (fiberClassDesc hF (E := E) W)]
      (j : (thomPairOver F E W).singularHomology (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1) ⟶ S.X₂)
      (hj : j ≫ S.g = TopPair.singularHomologyMap (thomPairOverMap F E hW)
        (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1))
      (hjφ : j ≫ φ = inv (fiberClassDesc hF W) ≫ twistedRestrict hF hW) :
      TopPair.singularHomologyMap (thomPairOverMap F E hW) (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1) ≫
        Φ = inv (fiberClassDesc hF W) ≫ twistedRestrict hF hW := by
    rw [← hj, Category.assoc, hgΦ, hjφ]
  have hΦU := hΦ subset_union_left biprod.inl (biprod.inl_desc _ _) (biprod.inl_desc _ _)
  have hΦV := hΦ subset_union_right biprod.inr (biprod.inr_desc _ _) (biprod.inr_desc _ _)
  -- So `Φ` inverts the map over `U ∪ V` on the restrictions from `U` and from `V`.
  have hr {W : Set B} (hW : W ⊆ U ∪ V) [IsIso (fiberClassDesc hF (E := E) W)]
      (hWΦ : TopPair.singularHomologyMap (thomPairOverMap F E hW) (ModuleCat.of ℤ (ULift.{w} ℤ))
        (n + 1) ≫ Φ = inv (fiberClassDesc hF W) ≫ twistedRestrict hF hW) :
      twistedRestrict hF hW ≫ fiberClassDesc hF (U ∪ V) ≫ Φ = twistedRestrict hF hW := by
    rw [← Category.assoc, twistedRestrict_fiberClassDesc, Category.assoc, hWΦ,
      IsIso.hom_inv_id_assoc]
  refine ⟨Φ, LocalCoefficientSystem.twistedHomology₀_hom_ext _ fun x ↦ ?_,
    (cancel_epi S.g).1 (biprod.hom_ext' _ _ ?_ ?_)⟩
  · -- A point of `U ∪ V` lies in `U` or in `V`, where the composite is computed.
    obtain ⟨x, hx | hx⟩ := x
    · exact (ιTwistedHomology₀_twistedRestrict_assoc hF subset_union_left ⟨x, hx⟩ _).symm.trans
        ((congrArg _ (hr subset_union_left hΦU)).trans ((Category.comp_id _).symm.trans
          (ιTwistedHomology₀_twistedRestrict_assoc hF subset_union_left ⟨x, hx⟩ (𝟙 _))))
    · exact (ιTwistedHomology₀_twistedRestrict_assoc hF subset_union_right ⟨x, hx⟩ _).symm.trans
        ((congrArg _ (hr subset_union_right hΦV)).trans ((Category.comp_id _).symm.trans
          (ιTwistedHomology₀_twistedRestrict_assoc hF subset_union_right ⟨x, hx⟩ (𝟙 _))))
  -- The second map of the Mayer–Vietoris sequence is an epimorphism.
  · simp only [S, biprod.inl_desc_assoc, biprod.inl_desc, Category.comp_id, reassoc_of% hΦU,
      twistedRestrict_fiberClassDesc, IsIso.inv_hom_id_assoc]
  · simp only [S, biprod.inr_desc_assoc, biprod.inr_desc, Category.comp_id, reassoc_of% hΦV,
      twistedRestrict_fiberClassDesc, IsIso.inv_hom_id_assoc]

private theorem isIso_fiberClassDesc_empty : IsIso (fiberClassDesc hF (E := E) ∅) :=
  isIso_of_source_target_iso_zero _
    ((IsZero.iff_id_eq_zero _).2 (LocalCoefficientSystem.twistedHomology₀_hom_ext
      ((LocalCoefficientSystem.pullback (X := TopCat.of (∅ : Set B))
        (ContinuousMap.subtypeVal ∅)).obj
          (signLocalSystem F E ℤ ((Fintype.card_fin _).trans hF.symm)))
      fun x ↦ x.2.elim)).isoZero
    (isZero_singularHomology_thomPairOver_empty _ _).isoZero

/-- The map is an isomorphism over finite unions of trivializing open sets. -/
private theorem isIso_fiberClassDesc_biUnion {ι : Type*} (s : Finset ι) {W : ι → Set B}
    (hWo : ∀ i ∈ s, IsOpen (W i))
    (hWe : ∀ i ∈ s, ∃ (e : Trivialization F (π F E)) (_ : MemTrivializationAtlas e),
      W i ⊆ e.baseSet) :
    IsIso (fiberClassDesc hF (E := E) (⋃ i ∈ s, W i)) := by
  classical
  have := Module.finite_of_finrank_eq_succ hF
  induction s using Finset.induction_on generalizing W with
  | empty =>
    rw [show (⋃ i ∈ (∅ : Finset ι), W i) = ∅ by simp]
    exact isIso_fiberClassDesc_empty hF
  | insert a s _ ih =>
    rw [Finset.set_biUnion_insert]
    obtain ⟨e, _, he⟩ := hWe a (Finset.mem_insert_self a s)
    have : IsIso (fiberClassDesc hF (E := E) (W a)) := isIso_fiberClassDesc_of_subset hF e he
    have : IsIso (fiberClassDesc hF (E := E) (⋃ i ∈ s, W i)) :=
      ih (fun i hi ↦ hWo i (Finset.mem_insert_of_mem hi))
        (fun i hi ↦ hWe i (Finset.mem_insert_of_mem hi))
    -- `W a ∩ ⋃ i ∈ s, W i` is the union of the trivializing open sets `W a ∩ W i`, `i ∈ s`.
    have : IsIso (fiberClassDesc hF (E := E) (W a ∩ ⋃ i ∈ s, W i)) := by
      rw [inter_iUnion₂]
      refine ih (fun i hi ↦ (hWo a (Finset.mem_insert_self a s)).inter
        (hWo i (Finset.mem_insert_of_mem hi))) fun i hi ↦ ?_
      obtain ⟨e', he', hi'⟩ := hWe i (Finset.mem_insert_of_mem hi)
      exact ⟨e', he', inter_subset_right.trans hi'⟩
    exact isIso_fiberClassDesc_union hF (hWo a (Finset.mem_insert_self a s))
      (isOpen_iUnion fun i ↦ isOpen_iUnion fun hi ↦ hWo i (Finset.mem_insert_of_mem hi))
      fun m hm ↦ e.isZero_singularHomology_thomPairOver (inter_subset_left.trans he) _
        (by omega)

/-! ### The passage to the whole base -/

/-- The fibre class maps over the base as a cocone over `o(E)`. -/
private def fiberClassCoconeBase :
    Cocone (signLocalSystem F E ℤ ((Fintype.card_fin _).trans hF.symm)) where
  pt := ((thomPair F E).singularHomology (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1) : ModuleCat.{w} ℤ)
  ι :=
    { app x := fiberClassHom hF univ (mem_univ x.as) ≫
        TopPair.singularHomologyMap (thomPairOverUnivIso F E).hom _ (n + 1)
      naturality x y γ := by
        refine Eq.trans ?_ (Category.comp_id _).symm
        induction γ using Path.Homotopic.Quotient.ind with
        | mk γ =>
          rw [← Category.assoc]
          exact congrArg (· ≫ _) (signLocalSystem_map_comp_fiberClassHom hF univ γ
            (fun _ ↦ mem_univ _) (mem_univ _) (mem_univ _)) }

/-- The map `H₀(W; o(E)) ⟶ Hₙ₊₁(E|_W, E₀|_W; ℤ)`. -/
private def fiberClassDescBase :
    (signLocalSystem F E ℤ ((Fintype.card_fin _).trans hF.symm)).twistedHomology 0 ⟶
      ((thomPair F E).singularHomology (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1) :
        ModuleCat.{w} ℤ) :=
  (LocalCoefficientSystem.isColimitTwistedHomology₀Cocone _).desc (fiberClassCoconeBase hF)

@[reassoc]
private theorem ιTwistedHomology₀_fiberClassDescBase (x : B) :
    LocalCoefficientSystem.ιTwistedHomology₀ _ x ≫ fiberClassDescBase hF (E := E) =
      fiberClassHom hF univ (mem_univ x) ≫
        TopPair.singularHomologyMap (thomPairOverUnivIso F E).hom _ (n + 1) :=
  (LocalCoefficientSystem.isColimitTwistedHomology₀Cocone _).fac (fiberClassCoconeBase hF)
    (FundamentalGroupoid.mk x)

/-- The map induced in twisted homology by the inclusion of `W` into the base. -/
private abbrev twistedLeg (W : Set B) :
    ((LocalCoefficientSystem.pullback (X := TopCat.of W) (ContinuousMap.subtypeVal W)).obj
      (signLocalSystem F E ℤ ((Fintype.card_fin _).trans hF.symm))).twistedHomology 0 ⟶
    (signLocalSystem F E ℤ ((Fintype.card_fin _).trans hF.symm)).twistedHomology 0 :=
  LocalCoefficientSystem.twistedHomologyMap (TopCat.ofHom (ContinuousMap.subtypeVal W)) _ 0

private theorem twistedRestrict_twistedLeg {W W' : Set B} (h : W ⊆ W') :
    twistedRestrict hF (E := E) h ≫ twistedLeg hF W' = twistedLeg hF W :=
  LocalCoefficientSystem.twistedHomology₀_hom_ext _ fun x ↦ by
    rw [ιTwistedHomology₀_twistedRestrict_assoc]
    -- The fibres agree only up to unfolding the pullbacks.
    erw [LocalCoefficientSystem.ιTwistedHomology₀_homologyMap,
      LocalCoefficientSystem.ιTwistedHomology₀_homologyMap]
    rfl

private theorem twistedLeg_fiberClassDescBase (W : Set B) :
    twistedLeg hF W ≫ fiberClassDescBase hF (E := E) = fiberClassDesc hF W ≫
      TopPair.singularHomologyMap (thomPairOverMap F E (subset_univ W) ≫
        (thomPairOverUnivIso F E).hom) (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1) :=
  LocalCoefficientSystem.twistedHomology₀_hom_ext _ fun x ↦ by
    -- The fibres agree only up to unfolding the pullback.
    erw [LocalCoefficientSystem.ιTwistedHomology₀_homologyMap_assoc,
      ιTwistedHomology₀_fiberClassDescBase]
    refine Eq.trans ?_ (ιTwistedHomology₀_fiberClassDesc_assoc hF W x _).symm
    rw [TopPair.singularHomologyMap_comp]
    exact (fiberClassHom_comp_singularHomologyMap_thomPairOverMap_assoc hF (E := E)
      (subset_univ W) x.2 _).symm

private theorem singularHomologyMap_thomPairOverMap_comp_inv_fiberClassDesc {W W' : Set B}
    (h : W ⊆ W') [IsIso (fiberClassDesc hF (E := E) W)] [IsIso (fiberClassDesc hF (E := E) W')] :
    TopPair.singularHomologyMap (thomPairOverMap F E h) (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1) ≫
        inv (fiberClassDesc hF W') = inv (fiberClassDesc hF W) ≫ twistedRestrict hF h := by
  rw [IsIso.comp_inv_eq, Category.assoc, twistedRestrict_fiberClassDesc, IsIso.inv_hom_id_assoc]

private theorem isIso_fiberClassDesc_finiteTrivializingUnion (s : Finset B) :
    IsIso (fiberClassDesc hF (E := E) (⋃ b ∈ s, (trivializationAt F E b).baseSet)) :=
  isIso_fiberClassDesc_biUnion hF s (fun b _ ↦ (trivializationAt F E b).open_baseSet)
    fun b _ ↦ ⟨trivializationAt F E b, inferInstance, subset_rfl⟩

omit [NormedSpace ℝ F] [∀ b, Module ℝ (E b)] [VectorBundle ℝ F E] in
private theorem singularHomologyFunctor_obj_thomPairFiniteTrivializingUnionDiagram_obj
    (s : Finset B) :
    (TopPair.singularHomologyFunctor (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1)).obj
      ((thomPairFiniteTrivializingUnionDiagram (F := F) (E := E)).obj s) =
      (thomPairOver F E (⋃ b ∈ s, (trivializationAt F E b).baseSet)).singularHomology
        (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1) := by
  rw [thomPairFiniteTrivializingUnionDiagram_obj, TopPair.singularHomologyFunctor_obj]

/-- The inverses over finite trivializing unions commute with restriction. -/
private theorem finiteTrivializingUnion_naturality {s t : Finset B} (f : s ⟶ t)
    [IsIso (fiberClassDesc hF (E := E) (⋃ b ∈ s, (trivializationAt F E b).baseSet))]
    [IsIso (fiberClassDesc hF (E := E) (⋃ b ∈ t, (trivializationAt F E b).baseSet))] :
    (thomPairFiniteTrivializingUnionDiagram (F := F) (E := E) ⋙
      TopPair.singularHomologyFunctor (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1)).map f ≫
        eqToHom (singularHomologyFunctor_obj_thomPairFiniteTrivializingUnionDiagram_obj t) ≫
          inv (fiberClassDesc hF (⋃ b ∈ t, (trivializationAt F E b).baseSet)) ≫ twistedLeg hF _ =
      eqToHom (singularHomologyFunctor_obj_thomPairFiniteTrivializingUnionDiagram_obj s) ≫
        inv (fiberClassDesc hF (⋃ b ∈ s, (trivializationAt F E b).baseSet)) ≫ twistedLeg hF _ := by
  simp only [Functor.comp_obj, Functor.comp_map, thomPairFiniteTrivializingUnionDiagram_map,
    TopPair.singularHomologyFunctor_map, TopPair.singularHomologyMap_comp,
    TopPair.singularHomologyMap_eqToHom, Category.assoc, eqToHom_trans_assoc]
  rw [eqToHom_refl, Category.id_comp,
    reassoc_of% (singularHomologyMap_thomPairOverMap_comp_inv_fiberClassDesc hF (E := E)
      (W := ⋃ b ∈ s, (trivializationAt F E b).baseSet)
      (W' := ⋃ b ∈ t, (trivializationAt F E b).baseSet)
      (biUnion_subset_biUnion_left f.le)), twistedRestrict_twistedLeg]

/-- **The passage to the whole base**: the map over the base is an isomorphism. -/
private instance isIso_fiberClassDescBase : IsIso (fiberClassDescBase hF (E := E)) := by
  have hI (s : Finset B) := isIso_fiberClassDesc_finiteTrivializingUnion hF (E := E) s
  have hobj (s : Finset B) := singularHomologyFunctor_obj_thomPairFiniteTrivializingUnionDiagram_obj
    (F := F) (E := E) (n := n) s
  let c : Cocone (thomPairFiniteTrivializingUnionDiagram (F := F) (E := E) ⋙
      TopPair.singularHomologyFunctor (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1)) :=
    { pt := (signLocalSystem F E ℤ ((Fintype.card_fin _).trans hF.symm)).twistedHomology 0
      ι :=
        { app s := eqToHom (hobj s) ≫
            inv (fiberClassDesc hF (⋃ b ∈ s, (trivializationAt F E b).baseSet)) ≫
              twistedLeg hF _
          naturality s t f :=
            (finiteTrivializingUnion_naturality hF f).trans (Category.comp_id _).symm } }
  let P := isColimitMapCoconeSingularHomologyThomPairFiniteTrivializingUnion (F := F) (E := E)
    (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1)
  have hpt : ((TopPair.singularHomologyFunctor (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1)).mapCocone
      (thomPairFiniteTrivializingUnionCocone (F := F) (E := E))).pt =
      (thomPair F E).singularHomology (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1) := by
    simp
  -- The legs of the colimit are the restrictions to the whole Thom pair.
  have hleg (s : Finset B) :
      ((TopPair.singularHomologyFunctor (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1)).mapCocone
        (thomPairFiniteTrivializingUnionCocone (F := F) (E := E))).ι.app s ≫ eqToHom hpt =
      eqToHom (hobj s) ≫ TopPair.singularHomologyMap (thomPairOverMap F E
        (subset_univ (⋃ b ∈ s, (trivializationAt F E b).baseSet)) ≫
          (thomPairOverUnivIso F E).hom) (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1) :=
    singularHomologyFunctor_mapCocone_thomPairFiniteTrivializingUnionCocone_ι_app _ _ s
  refine ⟨eqToHom hpt.symm ≫ P.desc c, LocalCoefficientSystem.twistedHomology₀_hom_ext _
    fun x ↦ ?_, ?_⟩
  · -- A point `x` lies in the trivializing set at `x`, over which the map is invertible.
    have hx : x ∈ ⋃ b ∈ ({x} : Finset B), (trivializationAt F E b).baseSet := by
      simpa using FiberBundle.mem_baseSet_trivializationAt' x
    have h₁ : LocalCoefficientSystem.ιTwistedHomology₀
        (signLocalSystem F E ℤ ((Fintype.card_fin _).trans hF.symm)) x =
        (LocalCoefficientSystem.ιTwistedHomology₀
          ((LocalCoefficientSystem.pullback
            (X := TopCat.of ↥(⋃ b ∈ ({x} : Finset B), (trivializationAt F E b).baseSet))
            (ContinuousMap.subtypeVal _)).obj
              (signLocalSystem F E ℤ ((Fintype.card_fin _).trans hF.symm)))
          (⟨x, hx⟩ : ↥(⋃ b ∈ ({x} : Finset B), (trivializationAt F E b).baseSet)) ≫
            twistedLeg hF _ : _) :=
      (LocalCoefficientSystem.ιTwistedHomology₀_homologyMap
        (signLocalSystem F E ℤ ((Fintype.card_fin _).trans hF.symm))
        (TopCat.ofHom (ContinuousMap.subtypeVal
          (⋃ b ∈ ({x} : Finset B), (trivializationAt F E b).baseSet))) ⟨x, hx⟩).symm
    have h₂ : TopPair.singularHomologyMap (thomPairOverMap F E
        (subset_univ (⋃ b ∈ ({x} : Finset B), (trivializationAt F E b).baseSet)) ≫
          (thomPairOverUnivIso F E).hom) (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1) ≫
        eqToHom hpt.symm ≫ P.desc c =
        inv (fiberClassDesc hF _) ≫ twistedLeg hF _ := by
      rw [← cancel_epi (eqToHom (hobj {x})), ← reassoc_of% (hleg {x}), eqToHom_trans_assoc,
        eqToHom_refl, Category.id_comp]
      exact P.fac c {x}
    have h₃ : twistedLeg hF (E := E) (⋃ b ∈ ({x} : Finset B), (trivializationAt F E b).baseSet) ≫
        fiberClassDescBase hF ≫ eqToHom hpt.symm ≫ P.desc c = twistedLeg hF _ := by
      rw [reassoc_of% (twistedLeg_fiberClassDescBase hF (E := E)), h₂, IsIso.hom_inv_id_assoc]
    rw [h₁]
    -- Fibres agree only up to unfolding the pullback, so reassociate by unification.
    exact (Category.assoc _ _ _).trans ((congrArg _ h₃).trans (Category.comp_id _).symm)
  · rw [Category.assoc, ← cancel_epi (eqToHom hpt), eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp, Category.comp_id]
    refine P.hom_ext fun s ↦ ?_
    rw [P.fac_assoc, hleg]
    simp only [c, Category.assoc, twistedLeg_fiberClassDescBase, IsIso.inv_hom_id_assoc]


variable (F E) in
/-- **The integral homology of the Thom pair in the rank degree is the zeroth homology of the base
with coefficients in the orientation local system**: for a real vector bundle `E → B` of rank
`n + 1` over an arbitrary base, `Hₙ₊₁(E, E₀; ℤ) ≅ H₀(B; o(E))`. The inverse sends a coefficient
`f` at `b`, a function on the orientations of `E_b` with `f (-o) = -f o`, to `f o` times the class
of the fibre over `b` oriented by `o`
(`TauCeti.thomPairSingularHomologyIsoTwistedHomology_inv_apply`). The bundle need not be
orientable. -/
def thomPairSingularHomologyIsoTwistedHomology (hF : finrank ℝ F = n + 1) :
    (thomPair F E).singularHomology (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1) ≅
      (signLocalSystem F E ℤ ((Fintype.card_fin _).trans hF.symm)).twistedHomology 0 :=
  (asIso (fiberClassDescBase hF)).symm

/-- The inverse of `Hₙ₊₁(E, E₀; ℤ) ≅ H₀(B; o(E))` sends the class of a coefficient `f` at `b` to
`f o` times the class of the fibre over `b` oriented by `o`, for any orientation `o` of `E_b`. -/
theorem thomPairSingularHomologyIsoTwistedHomology_inv_apply (hF : finrank ℝ F = n + 1) (b : B)
    (o : Orientation ℝ (E b) (Fin (n + 1)))
    (f : (signLocalSystem F E ℤ ((Fintype.card_fin _).trans hF.symm)).obj
      (FundamentalGroupoid.mk b)) :
    (thomPairSingularHomologyIsoTwistedHomology F E hF).inv
        (LocalCoefficientSystem.ιTwistedHomology₀ _ b f) =
      signLocalSystemFiberEquiv ((Fintype.card_fin _).trans hF.symm) o f •
        TopPair.singularHomologyMap (fiberThomPairMap F E b) (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1)
          (fiberLocalOrientation hF b o) := by
  rw [thomPairSingularHomologyIsoTwistedHomology, Iso.symm_inv, asIso_hom,
    ← ConcreteCategory.comp_apply, ιTwistedHomology₀_fiberClassDescBase,
    ConcreteCategory.comp_apply,
    fiberClassHom_apply hF univ (mem_univ b) ⟨⟨b, o⟩, rfl⟩ (mem_univ b),
    signLocalSystemFiberEquiv_apply, map_zsmul, fiberClass, ← ConcreteCategory.comp_apply,
    ← TopPair.singularHomologyMap_comp, fiberThomPairOverMap_comp_thomPairOverUnivIso_hom]

/-- `Hₙ₊₁(E, E₀; ℤ) ≅ H₀(B; o(E))` sends the class of the fibre over `b` oriented by `o` to the
class of the coefficient at `b` taking the value `1` at `o`. -/
@[simp]
theorem thomPairSingularHomologyIsoTwistedHomology_hom_apply (hF : finrank ℝ F = n + 1) (b : B)
    (o : Orientation ℝ (E b) (Fin (n + 1))) :
    (thomPairSingularHomologyIsoTwistedHomology F E hF).hom
        (TopPair.singularHomologyMap (fiberThomPairMap F E b) (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1)
          (fiberLocalOrientation hF b o)) =
      LocalCoefficientSystem.ιTwistedHomology₀ _ b
        ((signLocalSystemFiberEquiv ((Fintype.card_fin _).trans hF.symm) o).symm 1) := by
  have h := thomPairSingularHomologyIsoTwistedHomology_inv_apply hF b o
    ((signLocalSystemFiberEquiv ((Fintype.card_fin _).trans hF.symm) o).symm 1)
  rw [LinearEquiv.apply_symm_apply, one_zsmul] at h
  rw [← h, Iso.inv_hom_id_apply]


end TauCeti
