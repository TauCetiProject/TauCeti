/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.Topology.Homotopy.Contractible
public import TauCeti.CategoryTheory.GrothendieckGroup.Split
public import TauCeti.Topology.CWComplex.Classical.Finite
public import TauCeti.Topology.VectorBundle.FiniteRank.Pullback
public import TauCeti.Topology.VectorBundle.HomotopyInvariance

/-!
# Homotopy invariance and cylinder extension for finite-rank bundle cores

This module lifts total-space homotopy invariance and relative cylinder trivialization extension
from `TauCeti.Topology.VectorBundle.HomotopyInvariance` to the category
`TauCeti.FiniteRankBundleCore 𝕜 B` of point-indexed finite-rank coordinate cores and to its split
Grothendieck group `TauCeti.SplitK0 (TauCeti.FiniteRankBundleCore 𝕜 B)`.

## Main definitions and results

* `TauCeti.FiniteRankBundleCore.continuous_hom_bundle_core_iff`,
  `TauCeti.FiniteRankBundleCore.ofTotalSpaceContinuous`,
  `TauCeti.FiniteRankBundleCore.isoOfTotalSpaceContinuous`, and
  `TauCeti.FiniteRankBundleCore.pullbackIsoOfTotalSpaceContinuous`: total-space continuity criteria
  and categorical morphism/isomorphism constructors for finite-rank cores over any nontrivially
  normed field `𝕜`, without completeness of `𝕜`.
* `TauCeti.FiniteRankBundleCore.pullback_const`: pulling back any finite-rank core along a constant
  map produces `trivial 𝕜 X A.rank` strictly as a coordinate core.
* `TauCeti.FiniteRankBundleCore.cylinderSlice`,
  `TauCeti.FiniteRankBundleCore.exists_iso_cylinder`, and
  `TauCeti.FiniteRankBundleCore.nonempty_iso_pullback_cylinderSlice`: cylinder transport as a
  categorical isomorphism `(A.pullback (cylinderSlice X 0)).pullback ContinuousMap.fst ≅ A` equal to
  the identity over `X × {0}`, and isomorphism of slice pullbacks at arbitrary times `s, t : I`.
* `TauCeti.FiniteRankBundleCore.exists_iso_cylinder_of_isClosed`,
  `TauCeti.FiniteRankBundleCore.exists_iso_cylinder_of_relSubcomplex`, and
  `TauCeti.FiniteRankBundleCore.exists_iso_cylinder_of_subcomplex`: relative extension of a partial
  cylinder isomorphism from `s × I` (`s ⊆ X` closed, in particular a subcomplex of a finite CW or
  compact-based finite relative CW complex) to all of `X × I` for real or complex cores.
* `ContinuousMap.Homotopic.nonempty_iso_pullback`,
  `ContinuousMap.HomotopicRel.exists_iso_pullback`, and
  `TauCeti.FiniteRankBundleCore.nonempty_iso_trivial_of_contractibleSpace`: free and relative
  homotopy invariance of core pullbacks over paracompact R₁ bases, and triviality over contractible
  paracompact R₁ bases.
* `TauCeti.FiniteRankBundleCore.splitK0_of_pullback_cylinderSlice_eq`,
  `ContinuousMap.Homotopic.splitK0_map_pullbackFunctor_eq`, and
  `TauCeti.FiniteRankBundleCore.splitK0PullbackEquiv`: equality of slice classes, homotopy
  invariance of `SplitK0.map (pullbackFunctor f)` on `SplitK0 (FiniteRankBundleCore 𝕜 ·)`, and the
  additive group isomorphism induced by a homotopy equivalence `X ≃ₕ Y` between paracompact R₁
  spaces.

## Implementation notes

In `TauCeti.continuous_hom_bundle_iff` completeness of `𝕜` is used to choose a continuous basis of
an abstract finite-dimensional normed space. Because the model fibre `Fin m → 𝕜` of a
`FiniteRankBundleCore` already carries the standard coordinate projections and basis vectors
`Pi.single i 1`, every continuous linear operator `(Fin m → 𝕜) →L[𝕜] G` expands directly as a
finite sum of rank-one operators (`clm_fin_eq_sum`), so total-space descent for finite-rank cores
requires no completeness assumption on `𝕜`.

## References

* A. Hatcher, *Vector Bundles and K-Theory*, §1.2, Theorem 1.6, Proposition 1.7, and Corollary 1.8.
* M. F. Atiyah, *K-Theory*, §1.4, Lemma 1.4.3 and Theorem 1.4.3.
-/

public section

open Bundle CategoryTheory Set VectorBundleCore
open scoped ContinuousMap Topology unitInterval

namespace TauCeti.FiniteRankBundleCore

section TotalSpace

universe u v w z

private theorem clm_fin_eq_sum {𝕜 G : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] {m : ℕ} (L : (Fin m → 𝕜) →L[𝕜] G) :
    L = ∑ i : Fin m,
      ContinuousLinearMap.smulRightL 𝕜 (Fin m → 𝕜) G (ContinuousLinearMap.proj i)
        (L (Pi.single i 1)) := by
  ext v
  have hv : ∑ i : Fin m, v i • (Pi.single i (1 : 𝕜) : Fin m → 𝕜) = v := by
    ext j
    simp [Pi.single_apply]
  simpa only [sum_apply, ContinuousLinearMap.smulRightL_apply_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply, ← map_smul,
    ← map_sum] using congrArg L hv.symm

private theorem continuousAt_clm_fin_iff {𝕜 Z G : Type*} [NontriviallyNormedField 𝕜]
    [TopologicalSpace Z] [NormedAddCommGroup G] [NormedSpace 𝕜 G] {m : ℕ}
    {T : Z → (Fin m → 𝕜) →L[𝕜] G} {z₀ : Z} :
    ContinuousAt T z₀ ↔ ∀ v, ContinuousAt (fun z ↦ T z v) z₀ := by
  refine ⟨fun h v ↦ h.clm_apply continuousAt_const, fun h ↦ ?_⟩
  have hsum : ContinuousAt (fun z ↦ ∑ i : Fin m,
      ContinuousLinearMap.smulRightL 𝕜 (Fin m → 𝕜) G (ContinuousLinearMap.proj i)
        (T z (Pi.single i 1))) z₀ :=
    tendsto_finsetSum Finset.univ fun i _ ↦
      ((ContinuousLinearMap.smulRightL 𝕜 (Fin m → 𝕜) G
        (ContinuousLinearMap.proj i)).continuous.continuousAt).comp (h (Pi.single i 1))
  exact hsum.congr (Filter.Eventually.of_forall fun z ↦ (clm_fin_eq_sum (T z)).symm)

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜]
  {B : Type u} [TopologicalSpace B]

/-- A family of fibrewise continuous linear maps between two finite-rank cores is continuous as a
section of the Hom bundle if and only if the induced map on total spaces is continuous. Because the
source model `Fin A.rank → 𝕜` carries its standard coordinate basis, no completeness assumption on
`𝕜` is required. -/
theorem continuous_hom_bundle_core_iff {A D : FiniteRankBundleCore 𝕜 B}
    (ϕ : B → (Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜)) :
    Continuous (fun x ↦ TotalSpace.mk' ((Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜))
      (E := fun y ↦ A.core.Fiber y →L[𝕜] D.core.Fiber y) x (ϕ x)) ↔
      Continuous (fun p : A.core.TotalSpace ↦
        (⟨p.proj, ϕ p.proj p.2⟩ : D.core.TotalSpace)) := by
  constructor
  · intro hϕ
    have h := (CoordinateHom.ofContinuous ϕ hϕ).continuous_totalSpaceMap
    rwa [CoordinateHom.totalSpaceMap_def, CoordinateHom.fiberMap_ofContinuous] at h
  · intro hϕ
    refine continuous_hom_bundle_iff_forall_continuousOn.2 fun i j ↦ ?_
    have hU : IsOpen (A.core.baseSet i ∩ D.core.baseSet j) :=
      (A.core.isOpen_baseSet i).inter (D.core.isOpen_baseSet j)
    refine hU.continuousOn_iff.2 fun x hx ↦ continuousAt_clm_fin_iff.2 fun v ↦ ?_
    let e₁ := A.core.localTriv i
    let e₂ := D.core.localTriv j
    have hx₁ : x ∈ e₁.baseSet := hx.1
    have hx₂ : (⟨x, ϕ x (e₁.symm x v)⟩ : D.core.TotalSpace) ∈ e₂.source :=
      (D.core.mem_localTriv_source j _).2 hx.2
    have hs : ContinuousAt (fun y ↦ (⟨y, e₁.symm y v⟩ : A.core.TotalSpace)) x :=
      (e₁.continuousOn_symm.continuousAt
        ((e₁.open_baseSet.prod isOpen_univ).mem_nhds ⟨hx₁, mem_univ v⟩)).comp
          (continuousAt_id.prodMk continuousAt_const)
    have hg : ContinuousAt (fun y ↦ (⟨y, ϕ y (e₁.symm y v)⟩ : D.core.TotalSpace)) x :=
      hϕ.continuousAt.comp_of_eq hs rfl
    have ht : ContinuousAt (fun y ↦ e₂ ⟨y, ϕ y (e₁.symm y v)⟩) x :=
      (e₂.continuousOn.continuousAt (e₂.open_source.mem_nhds hx₂)).comp_of_eq hg rfl
    refine ht.snd.congr_of_eventuallyEq ?_
    filter_upwards [hU.mem_nhds hx] with y hy
    have hy₁ : y ∈ (A.core.localTriv i).baseSet := hy.1
    simp only [e₂, D.core.localTriv_apply, e₁, A.core.localTriv_symm_apply i hy₁,
      inChartCoordinates_apply]

/-- Construct a morphism of finite-rank cores from fibrewise continuous linear maps that induce a
continuous map on total spaces. -/
def ofTotalSpaceContinuous {A D : FiniteRankBundleCore 𝕜 B}
    (ϕ : B → (Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜))
    (hϕ : Continuous fun p : A.core.TotalSpace ↦
      (⟨p.proj, ϕ p.proj p.2⟩ : D.core.TotalSpace)) : A ⟶ D :=
  CoordinateHom.ofContinuous ϕ ((continuous_hom_bundle_core_iff ϕ).2 hϕ)

@[simp]
theorem fiberMap_ofTotalSpaceContinuous {A D : FiniteRankBundleCore 𝕜 B}
    (ϕ : B → (Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜))
    (hϕ : Continuous fun p : A.core.TotalSpace ↦
      (⟨p.proj, ϕ p.proj p.2⟩ : D.core.TotalSpace)) (x : B) :
    (ofTotalSpaceContinuous ϕ hϕ).fiberMap x = ϕ x :=
  congrFun (CoordinateHom.fiberMap_ofContinuous _ _) x

@[simp]
theorem totalSpaceMap_ofTotalSpaceContinuous {A D : FiniteRankBundleCore 𝕜 B}
    (ϕ : B → (Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜))
    (hϕ : Continuous fun p : A.core.TotalSpace ↦
      (⟨p.proj, ϕ p.proj p.2⟩ : D.core.TotalSpace)) (p : A.core.TotalSpace) :
    (ofTotalSpaceContinuous ϕ hϕ).totalSpaceMap p = ⟨p.proj, ϕ p.proj p.2⟩ := by
  rcases p with ⟨x, v⟩
  simp [CoordinateHom.totalSpaceMap_mk]

/-- Construct an isomorphism of finite-rank cores from fibrewise continuous linear equivalences
whose forward and inverse maps are continuous on total spaces. -/
def isoOfTotalSpaceContinuous {A D : FiniteRankBundleCore 𝕜 B}
    (Φ : B → (Fin A.rank → 𝕜) ≃L[𝕜] (Fin D.rank → 𝕜))
    (hΦ₁ : Continuous fun p : A.core.TotalSpace ↦
      (⟨p.proj, Φ p.proj p.2⟩ : D.core.TotalSpace))
    (hΦ₂ : Continuous fun p : D.core.TotalSpace ↦
      (⟨p.proj, (Φ p.proj).symm p.2⟩ : A.core.TotalSpace)) : A ≅ D where
  hom := ofTotalSpaceContinuous (fun x ↦ (Φ x : (Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜)))
    (hΦ₁.congr fun _ ↦ rfl)
  inv := ofTotalSpaceContinuous
    (fun x ↦ ((Φ x).symm : (Fin D.rank → 𝕜) →L[𝕜] (Fin A.rank → 𝕜)))
    (hΦ₂.congr fun _ ↦ rfl)
  hom_inv_id := hom_ext fun x ↦ by
    rw [fiberMap_comp, fiberMap_ofTotalSpaceContinuous, fiberMap_ofTotalSpaceContinuous,
      fiberMap_id]
    exact (Φ x).coe_symm_comp_coe
  inv_hom_id := hom_ext fun x ↦ by
    rw [fiberMap_comp, fiberMap_ofTotalSpaceContinuous, fiberMap_ofTotalSpaceContinuous,
      fiberMap_id]
    exact (Φ x).coe_comp_coe_symm

@[simp]
theorem fiberMap_isoOfTotalSpaceContinuous_hom {A D : FiniteRankBundleCore 𝕜 B}
    (Φ : B → (Fin A.rank → 𝕜) ≃L[𝕜] (Fin D.rank → 𝕜))
    (hΦ₁ : Continuous fun p : A.core.TotalSpace ↦
      (⟨p.proj, Φ p.proj p.2⟩ : D.core.TotalSpace))
    (hΦ₂ : Continuous fun p : D.core.TotalSpace ↦
      (⟨p.proj, (Φ p.proj).symm p.2⟩ : A.core.TotalSpace)) (x : B) :
    (isoOfTotalSpaceContinuous Φ hΦ₁ hΦ₂).hom.fiberMap x =
      (Φ x : (Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜)) :=
  fiberMap_ofTotalSpaceContinuous _ (hΦ₁.congr fun _ ↦ rfl) x

@[simp]
theorem fiberMap_isoOfTotalSpaceContinuous_inv {A D : FiniteRankBundleCore 𝕜 B}
    (Φ : B → (Fin A.rank → 𝕜) ≃L[𝕜] (Fin D.rank → 𝕜))
    (hΦ₁ : Continuous fun p : A.core.TotalSpace ↦
      (⟨p.proj, Φ p.proj p.2⟩ : D.core.TotalSpace))
    (hΦ₂ : Continuous fun p : D.core.TotalSpace ↦
      (⟨p.proj, (Φ p.proj).symm p.2⟩ : A.core.TotalSpace)) (x : B) :
    (isoOfTotalSpaceContinuous Φ hΦ₁ hΦ₂).inv.fiberMap x =
      ((Φ x).symm : (Fin D.rank → 𝕜) →L[𝕜] (Fin A.rank → 𝕜)) :=
  fiberMap_ofTotalSpaceContinuous _ (hΦ₂.congr fun _ ↦ rfl) x

/-- Construct an isomorphism `A.pullback f ≅ D.pullback g` from fibrewise continuous linear
equivalences that are continuous between Mathlib's native pullback total spaces together with their
inverses. -/
def pullbackIsoOfTotalSpaceContinuous {Y : Type w} {Z : Type z}
    [TopologicalSpace Y] [TopologicalSpace Z]
    (A : FiniteRankBundleCore 𝕜 Y) (D : FiniteRankBundleCore 𝕜 Z)
    (f : C(B, Y)) (g : C(B, Z))
    (Φ : B → (Fin A.rank → 𝕜) ≃L[𝕜] (Fin D.rank → 𝕜))
    (hΦ₁ : Continuous fun v : TotalSpace (Fin A.rank → 𝕜) ((f : B → Y) *ᵖ A.core.Fiber) ↦
      TotalSpace.mk' (Fin D.rank → 𝕜) (E := (g : B → Z) *ᵖ D.core.Fiber) v.proj (Φ v.proj v.2))
    (hΦ₂ : Continuous fun v : TotalSpace (Fin D.rank → 𝕜) ((g : B → Z) *ᵖ D.core.Fiber) ↦
      TotalSpace.mk' (Fin A.rank → 𝕜) (E := (f : B → Y) *ᵖ A.core.Fiber) v.proj
        ((Φ v.proj).symm v.2)) :
    A.pullback f ≅ D.pullback g :=
  isoOfTotalSpaceContinuous Φ
    (((D.pullbackHomeomorph g).symm.continuous.comp
      (hΦ₁.comp (A.pullbackHomeomorph f).continuous)).congr fun p ↦ by
        dsimp only [Function.comp_apply]
        rw [A.pullbackHomeomorph_apply]
        exact D.pullbackHomeomorph_symm_apply g _)
    (((A.pullbackHomeomorph f).symm.continuous.comp
      (hΦ₂.comp (D.pullbackHomeomorph g).continuous)).congr fun p ↦ by
        dsimp only [Function.comp_apply]
        rw [D.pullbackHomeomorph_apply]
        exact A.pullbackHomeomorph_symm_apply f _)

@[simp]
theorem fiberMap_pullbackIsoOfTotalSpaceContinuous_hom {Y : Type w} {Z : Type z}
    [TopologicalSpace Y] [TopologicalSpace Z]
    (A : FiniteRankBundleCore 𝕜 Y) (D : FiniteRankBundleCore 𝕜 Z)
    (f : C(B, Y)) (g : C(B, Z))
    (Φ : B → (Fin A.rank → 𝕜) ≃L[𝕜] (Fin D.rank → 𝕜))
    (hΦ₁ : Continuous fun v : TotalSpace (Fin A.rank → 𝕜) ((f : B → Y) *ᵖ A.core.Fiber) ↦
      TotalSpace.mk' (Fin D.rank → 𝕜) (E := (g : B → Z) *ᵖ D.core.Fiber) v.proj (Φ v.proj v.2))
    (hΦ₂ : Continuous fun v : TotalSpace (Fin D.rank → 𝕜) ((g : B → Z) *ᵖ D.core.Fiber) ↦
      TotalSpace.mk' (Fin A.rank → 𝕜) (E := (f : B → Y) *ᵖ A.core.Fiber) v.proj
        ((Φ v.proj).symm v.2)) (x : B) :
    (pullbackIsoOfTotalSpaceContinuous A D f g Φ hΦ₁ hΦ₂).hom.fiberMap x =
      (Φ x : (Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜)) :=
  fiberMap_isoOfTotalSpaceContinuous_hom _ _ _ x

@[simp]
theorem fiberMap_pullbackIsoOfTotalSpaceContinuous_inv {Y : Type w} {Z : Type z}
    [TopologicalSpace Y] [TopologicalSpace Z]
    (A : FiniteRankBundleCore 𝕜 Y) (D : FiniteRankBundleCore 𝕜 Z)
    (f : C(B, Y)) (g : C(B, Z))
    (Φ : B → (Fin A.rank → 𝕜) ≃L[𝕜] (Fin D.rank → 𝕜))
    (hΦ₁ : Continuous fun v : TotalSpace (Fin A.rank → 𝕜) ((f : B → Y) *ᵖ A.core.Fiber) ↦
      TotalSpace.mk' (Fin D.rank → 𝕜) (E := (g : B → Z) *ᵖ D.core.Fiber) v.proj (Φ v.proj v.2))
    (hΦ₂ : Continuous fun v : TotalSpace (Fin D.rank → 𝕜) ((g : B → Z) *ᵖ D.core.Fiber) ↦
      TotalSpace.mk' (Fin A.rank → 𝕜) (E := (f : B → Y) *ᵖ A.core.Fiber) v.proj
        ((Φ v.proj).symm v.2)) (x : B) :
    (pullbackIsoOfTotalSpaceContinuous A D f g Φ hΦ₁ hΦ₂).inv.fiberMap x =
      ((Φ x).symm : (Fin D.rank → 𝕜) →L[𝕜] (Fin A.rank → 𝕜)) :=
  fiberMap_isoOfTotalSpaceContinuous_inv _ _ _ x

/-- Re-express a continuous linear equivalence between core fibres directly on coordinate models so
its type reduces under `implicit` transparency. -/
private def ofCoreEquiv {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    (A : FiniteRankBundleCore 𝕜 Y) (D : FiniteRankBundleCore 𝕜 Z) (y : Y) (z : Z)
    (e : A.core.Fiber y ≃L[𝕜] D.core.Fiber z) :
    (Fin A.rank → 𝕜) ≃L[𝕜] (Fin D.rank → 𝕜) where
  toFun v := e v
  invFun v := e.symm v
  left_inv v := e.symm_apply_apply v
  right_inv v := e.apply_symm_apply v
  map_add' u v := e.map_add u v
  map_smul' c v := e.map_smul c v
  continuous_toFun := e.continuous
  continuous_invFun := e.symm.continuous

@[simp]
private theorem ofCoreEquiv_apply {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    (A : FiniteRankBundleCore 𝕜 Y) (D : FiniteRankBundleCore 𝕜 Z) (y : Y) (z : Z)
    (e : A.core.Fiber y ≃L[𝕜] D.core.Fiber z) (v : Fin A.rank → 𝕜) :
    ofCoreEquiv A D y z e v = e v :=
  rfl

@[simp]
private theorem ofCoreEquiv_symm_apply {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    (A : FiniteRankBundleCore 𝕜 Y) (D : FiniteRankBundleCore 𝕜 Z) (y : Y) (z : Z)
    (e : A.core.Fiber y ≃L[𝕜] D.core.Fiber z) (v : Fin D.rank → 𝕜) :
    (ofCoreEquiv A D y z e).symm v = e.symm v :=
  rfl

/-- Transport `A.pullbackHomeomorph f` along a pointwise equality `(f : B → Y) = f'`. -/
private def pullbackHomeomorphOfEq {Y : Type w} [TopologicalSpace Y]
    (A : FiniteRankBundleCore 𝕜 Y) (f : C(B, Y)) (f' : B → Y) (hf : (f : B → Y) = f') :
    (A.pullback f).core.TotalSpace ≃ₜ TotalSpace (Fin A.rank → 𝕜) (f' *ᵖ A.core.Fiber) where
  toEquiv :=
    { toFun p := ⟨p.proj, p.2⟩
      invFun p := ⟨p.proj, p.2⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  continuous_toFun := by
    subst hf
    exact (A.pullbackHomeomorph f).continuous.congr fun p ↦ A.pullbackHomeomorph_apply f p
  continuous_invFun := by
    subst hf
    exact (A.pullbackHomeomorph f).symm.continuous.congr fun p ↦ A.pullbackHomeomorph_symm_apply f p

end TotalSpace

section Slices

universe u v w

private theorem vectorBundleCore_eq {𝕜 B F ι : Type*} [NontriviallyNormedField 𝕜]
    [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {c₁ c₂ : VectorBundleCore 𝕜 B F ι} (hb : c₁.baseSet = c₂.baseSet)
    (hi : c₁.indexAt = c₂.indexAt) (hc : c₁.coordChange = c₂.coordChange) : c₁ = c₂ := by
  cases c₁
  cases c₂
  dsimp only at hb hi hc
  cases hb
  cases hi
  cases hc
  rfl

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜]
  {X : Type u} [TopologicalSpace X]
  {Y : Type w} [TopologicalSpace Y]

/-- Pulling back a finite-rank core along a constant map gives the trivial core of the same rank:
every pulled-back chart is the whole base and every transition operator is the identity at `y`. -/
@[simp]
theorem pullback_const (A : FiniteRankBundleCore 𝕜 Y) (X : Type u) [TopologicalSpace X] (y : Y) :
    A.pullback (.const X y) = trivial 𝕜 X A.rank := by
  have hcore : (A.pullback (.const X y)).core = (trivial 𝕜 X A.rank).core :=
    vectorBundleCore_eq
      (funext fun _ ↦ eq_univ_of_forall fun _ ↦ A.mem_baseSet_self y)
      rfl
      (by funext _ _ _; exact A.coordChange_self y)
  dsimp only [pullback, trivial] at hcore ⊢
  congr

/-- Time-`t` slice embedding `x ↦ (x, t)` into the cylinder `X × I`. -/
@[expose]
def cylinderSlice (X : Type u) [TopologicalSpace X] (t : I) : C(X, X × I) :=
  ⟨fun x ↦ (x, t), continuous_id.prodMk continuous_const⟩

@[simp]
theorem cylinderSlice_apply {X : Type u} [TopologicalSpace X] (t : I) (x : X) :
    cylinderSlice X t x = (x, t) :=
  (rfl)

@[simp]
theorem fst_comp_cylinderSlice (X : Type u) [TopologicalSpace X] (t : I) :
    ContinuousMap.fst.comp (cylinderSlice X t) = .id X := by
  ext x
  rfl

@[simp]
theorem cylinderSlice_zero_comp_fst (X : Type u) [TopologicalSpace X] :
    (cylinderSlice X 0).comp ContinuousMap.fst = cylinderZero X :=
  (rfl)

theorem pullback_cylinderSlice_pullback_fst (A : FiniteRankBundleCore 𝕜 X) (t : I) :
    (A.pullback ContinuousMap.fst).pullback (cylinderSlice X t) = A := by
  rw [pullback_comp, fst_comp_cylinderSlice, pullback_id]

end Slices

section Cylinder

universe u v

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜] [CompleteSpace 𝕜]
  {X : Type u} [TopologicalSpace X] [R1Space X] [ParacompactSpace X]

/-- **Categorical cylinder theorem for finite-rank bundle cores.** Over a paracompact R₁ base `X`,
every finite-rank core `A` over `X × I` is isomorphic to the cylinder pullback of its time-zero
slice `A.pullback (cylinderSlice X 0)` by an isomorphism equal to the identity on every fibre over
`X × {0}`. -/
theorem exists_iso_cylinder (A : FiniteRankBundleCore 𝕜 (X × I)) :
    ∃ e : (A.pullback (cylinderSlice X 0)).pullback ContinuousMap.fst ≅ A,
      ∀ x : X, e.hom.fiberMap (x, 0) = ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜) := by
  obtain ⟨Φ, hΦ₁, hΦ₂, hΦ0⟩ := exists_continuousLinearEquiv_cylinder
    (𝕜 := 𝕜) (F := Fin A.rank → 𝕜) (E := A.core.Fiber)
  let eZ : ((A.pullback (cylinderSlice X 0)).pullback ContinuousMap.fst).core.TotalSpace ≃ₜ
      TotalSpace (Fin A.rank → 𝕜) ((fun q : X × I ↦ (q.1, (0 : I))) *ᵖ A.core.Fiber) :=
    pullbackHomeomorphOfEq A (cylinderZero X) (fun q ↦ (q.1, 0)) (funext fun _ ↦ rfl)
  refine ⟨isoOfTotalSpaceContinuous (fun q ↦ ofCoreEquiv A A (q.1, 0) q (Φ q))
      ((hΦ₁.comp eZ.continuous).congr fun _ ↦ rfl)
      ((eZ.symm.continuous.comp hΦ₂).congr fun _ ↦ rfl),
    fun x ↦ ContinuousLinearMap.ext fun (v : Fin A.rank → 𝕜) ↦ ?_⟩
  rw [fiberMap_isoOfTotalSpaceContinuous_hom]
  simp [hΦ0 x]
  rfl

/-- Over a paracompact R₁ base `X`, the slice pullbacks of a finite-rank core over `X × I` at any
two times `s, t : I` are isomorphic. -/
theorem nonempty_iso_pullback_cylinderSlice (A : FiniteRankBundleCore 𝕜 (X × I)) (s t : I) :
    Nonempty (A.pullback (cylinderSlice X s) ≅ A.pullback (cylinderSlice X t)) := by
  obtain ⟨e, -⟩ := exists_iso_cylinder A
  exact ⟨((pullbackFunctor (cylinderSlice X s)).mapIso e).symm ≪≫
    (pullbackFunctor (cylinderSlice X t)).mapIso e⟩

end Cylinder

section RelativeCylinder

universe u v

variable {𝕜 : Type v} [RCLike 𝕜]
  {X : Type u} [TopologicalSpace X]

private def isoFiberEquiv {B : Type*} [TopologicalSpace B] {A D : FiniteRankBundleCore 𝕜 B}
    (e : A ≅ D) (x : B) : (Fin A.rank → 𝕜) ≃L[𝕜] (Fin D.rank → 𝕜) :=
  ContinuousLinearEquiv.equivOfInverse (e.hom.fiberMap x) (e.inv.fiberMap x)
    (fun v ↦ by
      have h := congrArg (fun k : A ⟶ A ↦ k.fiberMap x v) e.hom_inv_id
      simpa only [fiberMap_comp, fiberMap_id, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.id_apply] using h)
    (fun v ↦ by
      have h := congrArg (fun k : D ⟶ D ↦ k.fiberMap x v) e.inv_hom_id
      simpa only [fiberMap_comp, fiberMap_id, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.id_apply] using h)

/-- **Relative categorical cylinder theorem for finite-rank bundle cores.** Let `X` be paracompact
and R₁, let `s ⊆ X` be closed, and let `A` be a real or complex finite-rank core over `X × I`.
Every partial cylinder isomorphism `e₀` over `s × I` equal to the identity on `s × {0}` extends to
a global cylinder isomorphism `e` over `X × I` equal to the identity on `X × {0}` whose restriction
along `cylinderSetIncl s` is `e₀`. -/
theorem exists_iso_cylinder_of_isClosed [R1Space X] [ParacompactSpace X] {s : Set X}
    (hs : IsClosed s) (A : FiniteRankBundleCore 𝕜 (X × I))
    (e₀ : ((A.pullback (cylinderSlice X 0)).pullback ContinuousMap.fst).pullback
        (cylinderSetIncl s) ≅ A.pullback (cylinderSetIncl s))
    (he₀ : ∀ x : s, e₀.hom.fiberMap (x, 0) = ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜)) :
    ∃ e : (A.pullback (cylinderSlice X 0)).pullback ContinuousMap.fst ≅ A,
      (∀ x : X, e.hom.fiberMap (x, 0) = ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜)) ∧
      (pullbackFunctor (cylinderSetIncl s)).mapIso e = e₀ := by
  let Φ₀ : ∀ q : s × I, A.core.Fiber (q.1.1, 0) ≃L[𝕜] A.core.Fiber (q.1.1, q.2) := isoFiberEquiv e₀
  let eS₀ : (((A.pullback (cylinderSlice X 0)).pullback ContinuousMap.fst).pullback
      (cylinderSetIncl s)).core.TotalSpace ≃ₜ
      TotalSpace (Fin A.rank → 𝕜) ((fun q : s × I ↦ (q.1.1, (0 : I))) *ᵖ A.core.Fiber) :=
    pullbackHomeomorphOfEq A ((cylinderZero X).comp (cylinderSetIncl s))
      (fun q ↦ (q.1.1, 0)) (funext fun _ ↦ rfl)
  let eS₁ : (A.pullback (cylinderSetIncl s)).core.TotalSpace ≃ₜ
      TotalSpace (Fin A.rank → 𝕜) ((fun q : s × I ↦ (q.1.1, q.2)) *ᵖ A.core.Fiber) :=
    pullbackHomeomorphOfEq A (cylinderSetIncl s) (fun q ↦ (q.1.1, q.2)) (funext fun _ ↦ rfl)
  have hΦ₀ : Continuous fun v : TotalSpace (Fin A.rank → 𝕜)
      ((fun q : s × I ↦ (q.1.1, (0 : I))) *ᵖ A.core.Fiber) ↦
      TotalSpace.mk' (Fin A.rank → 𝕜) (E := (fun q : s × I ↦ (q.1.1, q.2)) *ᵖ A.core.Fiber)
        v.proj (Φ₀ v.proj v.2) :=
    (eS₁.continuous.comp (e₀.hom.continuous_totalSpaceMap.comp eS₀.symm.continuous)).congr
      fun v ↦ congrArg eS₁ (CoordinateHom.totalSpaceMap_mk e₀.hom v.proj (v.2 : Fin A.rank → 𝕜))
  have hΦ₀0 (x : s) : Φ₀ (x, 0) = ContinuousLinearEquiv.refl 𝕜 (A.core.Fiber (x.1, 0)) :=
    DFunLike.ext _ _ fun (v : Fin A.rank → 𝕜) ↦ by
      change (e₀.hom.fiberMap (x, 0) v : Fin A.rank → 𝕜) = v
      rw [he₀ x]
      rfl
  obtain ⟨Φ, hfwd, hinv, h0, hs'⟩ := exists_continuousLinearEquiv_cylinder_of_isClosed_of_continuous
    (𝕜 := 𝕜) (F := Fin A.rank → 𝕜) (E := A.core.Fiber) hs Φ₀ hΦ₀ hΦ₀0
  let eZ : ((A.pullback (cylinderSlice X 0)).pullback ContinuousMap.fst).core.TotalSpace ≃ₜ
      TotalSpace (Fin A.rank → 𝕜) ((fun q : X × I ↦ (q.1, (0 : I))) *ᵖ A.core.Fiber) :=
    pullbackHomeomorphOfEq A (cylinderZero X) (fun q ↦ (q.1, 0)) (funext fun _ ↦ rfl)
  refine ⟨isoOfTotalSpaceContinuous (fun q ↦ ofCoreEquiv A A (q.1, 0) q (Φ q))
      ((hfwd.comp eZ.continuous).congr fun _ ↦ rfl)
      ((eZ.symm.continuous.comp hinv).congr fun _ ↦ rfl),
    fun x ↦ ContinuousLinearMap.ext fun (v : Fin A.rank → 𝕜) ↦ ?_,
    Iso.ext (hom_ext fun ⟨x, t⟩ ↦ ContinuousLinearMap.ext fun (v : Fin A.rank → 𝕜) ↦ ?_)⟩
  · rw [fiberMap_isoOfTotalSpaceContinuous_hom]
    simp [h0 x]
    rfl
  · rw [Functor.mapIso_hom, pullbackFunctor_map, fiberMap_pullbackMap, cylinderSetIncl_apply,
      fiberMap_isoOfTotalSpaceContinuous_hom]
    simp only [ContinuousLinearEquiv.coe_coe, ofCoreEquiv_apply, hs' x t]
    rfl

/-- Relative cylinder extension from a subcomplex `E` of a finite relative CW structure on `X` over
a compact base `D`. -/
theorem exists_iso_cylinder_of_relSubcomplex [R1Space X] {D : Set X}
    [Topology.RelCWComplex (univ : Set X) D] [Topology.RelCWComplex.Finite (univ : Set X)]
    (hD : IsCompact D) (E : Topology.RelCWComplex.Subcomplex (univ : Set X))
    (A : FiniteRankBundleCore 𝕜 (X × I))
    (e₀ : ((A.pullback (cylinderSlice X 0)).pullback ContinuousMap.fst).pullback
        (cylinderSetIncl (E : Set X)) ≅ A.pullback (cylinderSetIncl (E : Set X)))
    (he₀ : ∀ x : (E : Set X),
      e₀.hom.fiberMap (x, 0) = ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜)) :
    ∃ e : (A.pullback (cylinderSlice X 0)).pullback ContinuousMap.fst ≅ A,
      (∀ x : X, e.hom.fiberMap (x, 0) = ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜)) ∧
      (pullbackFunctor (cylinderSetIncl (E : Set X))).mapIso e = e₀ := by
  have : CompactSpace X := ⟨Topology.RelCWComplex.isCompact_of_finite hD⟩
  exact exists_iso_cylinder_of_isClosed E.closed A e₀ he₀

/-- Relative cylinder extension from a subcomplex `E` of a finite CW structure on an R₁ space `X`
(for instance any Hausdorff finite CW complex). -/
theorem exists_iso_cylinder_of_subcomplex [R1Space X]
    [Topology.CWComplex (univ : Set X)] [Topology.RelCWComplex.Finite (univ : Set X)]
    (E : Topology.CWComplex.Subcomplex (univ : Set X))
    (A : FiniteRankBundleCore 𝕜 (X × I))
    (e₀ : ((A.pullback (cylinderSlice X 0)).pullback ContinuousMap.fst).pullback
        (cylinderSetIncl (E : Set X)) ≅ A.pullback (cylinderSetIncl (E : Set X)))
    (he₀ : ∀ x : (E : Set X),
      e₀.hom.fiberMap (x, 0) = ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜)) :
    ∃ e : (A.pullback (cylinderSlice X 0)).pullback ContinuousMap.fst ≅ A,
      (∀ x : X, e.hom.fiberMap (x, 0) = ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜)) ∧
      (pullbackFunctor (cylinderSetIncl (E : Set X))).mapIso e = e₀ :=
  exists_iso_cylinder_of_relSubcomplex isCompact_empty E A e₀ he₀

end RelativeCylinder

section Homotopy

universe u v w

section Free

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜] [CompleteSpace 𝕜]
  {X : Type u} [TopologicalSpace X] [R1Space X] [ParacompactSpace X]
  {Y : Type w} [TopologicalSpace Y]

/-- **Homotopy invariance of finite-rank bundle cores.** Over a paracompact R₁ base `X`, homotopic
maps `f₀ f₁ : C(X, Y)` induce isomorphic pullbacks `A.pullback f₀ ≅ A.pullback f₁` for every
finite-rank core `A` over `Y`. -/
theorem _root_.ContinuousMap.Homotopic.nonempty_iso_pullback {f₀ f₁ : C(X, Y)}
    (h : f₀.Homotopic f₁) (A : FiniteRankBundleCore 𝕜 Y) :
    Nonempty (A.pullback f₀ ≅ A.pullback f₁) := by
  obtain ⟨Φ, hΦ₁, hΦ₂⟩ :=
    h.exists_continuousLinearEquiv_pullback (𝕜 := 𝕜) (F := Fin A.rank → 𝕜) (E := A.core.Fiber)
  exact ⟨pullbackIsoOfTotalSpaceContinuous A A f₀ f₁
    (fun x ↦ ofCoreEquiv A A (f₀ x) (f₁ x) (Φ x))
    (hΦ₁.congr fun _ ↦ rfl) (hΦ₂.congr fun _ ↦ rfl)⟩

/-- **Finite-rank bundle cores over contractible paracompact R₁ bases are trivial.** -/
theorem nonempty_iso_trivial_of_contractibleSpace [ContractibleSpace X]
    (A : FiniteRankBundleCore 𝕜 X) :
    Nonempty (A ≅ trivial 𝕜 X A.rank) := by
  obtain ⟨y, hy⟩ := id_nullhomotopic X
  obtain ⟨e⟩ := hy.nonempty_iso_pullback A
  rw [pullback_id, pullback_const] at e
  exact ⟨e⟩

end Free

section Relative

variable {𝕜 : Type v} [RCLike 𝕜]
  {X : Type u} [TopologicalSpace X] [R1Space X] [ParacompactSpace X]
  {Y : Type w} [TopologicalSpace Y]

/-- **Relative homotopy invariance of finite-rank bundle cores.** Over a paracompact R₁ base `X`,
if `s ⊆ X` is closed and `f₀ f₁ : C(X, Y)` are homotopic relative to `s`, then for every real or
complex finite-rank core `A` over `Y` there is an isomorphism `A.pullback f₀ ≅ A.pullback f₁`
whose fibre map over every point of `s` is the identity on `Fin A.rank → 𝕜`. -/
theorem _root_.ContinuousMap.HomotopicRel.exists_iso_pullback {s : Set X}
    {f₀ f₁ : C(X, Y)} (h : f₀.HomotopicRel f₁ s) (hs : IsClosed s)
    (A : FiniteRankBundleCore 𝕜 Y) :
    ∃ e : A.pullback f₀ ≅ A.pullback f₁,
      ∀ x ∈ s, e.hom.fiberMap x = ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜) := by
  obtain ⟨Φ, hΦ₁, hΦ₂, hΦs⟩ := h.exists_continuousLinearEquiv_pullback
    (𝕜 := 𝕜) (F := Fin A.rank → 𝕜) (E := A.core.Fiber) hs
  refine ⟨pullbackIsoOfTotalSpaceContinuous A A f₀ f₁
      (fun x ↦ ofCoreEquiv A A (f₀ x) (f₁ x) (Φ x))
      (hΦ₁.congr fun _ ↦ rfl) (hΦ₂.congr fun _ ↦ rfl),
    fun x hx ↦ ContinuousLinearMap.ext fun (v : Fin A.rank → 𝕜) ↦ ?_⟩
  rw [fiberMap_pullbackIsoOfTotalSpaceContinuous_hom]
  simp only [ContinuousLinearEquiv.coe_coe, ofCoreEquiv_apply]
  let sndCoord (p : TotalSpace (Fin A.rank → 𝕜) A.core.Fiber) : Fin A.rank → 𝕜 := p.2
  exact congrArg sndCoord (hΦs x hx v)

end Relative

end Homotopy

section GrothendieckGroup

universe u v w z

variable {X : Type u} [TopologicalSpace X] [R1Space X] [ParacompactSpace X]
  {Y : Type w} [TopologicalSpace Y]

/-- Over a paracompact R₁ base `X`, the slice pullbacks of a finite-rank core over `X × I` at any
two times represent the same class in `SplitK0 (FiniteRankBundleCore 𝕜 X)`. -/
theorem splitK0_of_pullback_cylinderSlice_eq {𝕜 : Type v} [NontriviallyNormedField 𝕜]
    [NormedAlgebra ℝ 𝕜] [CompleteSpace 𝕜] (A : FiniteRankBundleCore 𝕜 (X × I)) (s t : I) :
    (SplitK0.of (A.pullback (cylinderSlice X s)) : SplitK0 (FiniteRankBundleCore 𝕜 X)) =
      SplitK0.of (A.pullback (cylinderSlice X t)) := by
  obtain ⟨e⟩ := nonempty_iso_pullback_cylinderSlice A s t
  exact SplitK0.of_congr e

/-- Homotopic maps out of a paracompact R₁ space induce equal pullback homomorphisms on
`SplitK0 (FiniteRankBundleCore 𝕜 ·)`. -/
theorem _root_.ContinuousMap.Homotopic.splitK0_map_pullbackFunctor_eq {f₀ f₁ : C(X, Y)}
    (h : f₀.Homotopic f₁) (𝕜 : Type v) [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]
    [CompleteSpace 𝕜] :
    SplitK0.map (pullbackFunctor (𝕜 := 𝕜) f₀) = SplitK0.map (pullbackFunctor (𝕜 := 𝕜) f₁) :=
  SplitK0.map_congr fun A ↦ h.nonempty_iso_pullback A

section HomotopyEquiv

variable [R1Space Y] [ParacompactSpace Y]

/-- A homotopy equivalence `e : X ≃ₕ Y` between paracompact R₁ spaces induces an additive
isomorphism `SplitK0 (FiniteRankBundleCore 𝕜 Y) ≃+ SplitK0 (FiniteRankBundleCore 𝕜 X)` by
pullback. -/
noncomputable def splitK0PullbackEquiv (𝕜 : Type v) [NontriviallyNormedField 𝕜]
    [NormedAlgebra ℝ 𝕜] [CompleteSpace 𝕜] (e : X ≃ₕ Y) :
    SplitK0 (FiniteRankBundleCore 𝕜 Y) ≃+ SplitK0 (FiniteRankBundleCore 𝕜 X) :=
  (SplitK0.map (pullbackFunctor (𝕜 := 𝕜) e.toFun)).toAddEquiv
    (SplitK0.map (pullbackFunctor (𝕜 := 𝕜) e.symm.toFun))
    (SplitK0.hom_ext fun A ↦ by
      have hsymm : e.symm.toFun = e.invFun := ContinuousMap.ext (congrFun e.coe_invFun.symm)
      obtain ⟨iso⟩ := e.right_inv.nonempty_iso_pullback A
      simp only [AddMonoidHom.comp_apply, SplitK0.map_of, pullback_comp, hsymm,
        SplitK0.of_congr iso, pullback_id, AddMonoidHom.id_apply])
    (SplitK0.hom_ext fun A ↦ by
      have hsymm : e.symm.toFun = e.invFun := ContinuousMap.ext (congrFun e.coe_invFun.symm)
      obtain ⟨iso⟩ := e.left_inv.nonempty_iso_pullback A
      simp only [AddMonoidHom.comp_apply, SplitK0.map_of, pullback_comp, hsymm,
        SplitK0.of_congr iso, pullback_id, AddMonoidHom.id_apply])

@[simp]
theorem splitK0PullbackEquiv_of (𝕜 : Type v) [NontriviallyNormedField 𝕜]
    [NormedAlgebra ℝ 𝕜] [CompleteSpace 𝕜] (e : X ≃ₕ Y) (A : FiniteRankBundleCore 𝕜 Y) :
    splitK0PullbackEquiv 𝕜 e (SplitK0.of A) = SplitK0.of (A.pullback e.toFun) :=
  SplitK0.map_of (pullbackFunctor (𝕜 := 𝕜) e.toFun) A

@[simp]
theorem splitK0PullbackEquiv_toAddMonoidHom (𝕜 : Type v) [NontriviallyNormedField 𝕜]
    [NormedAlgebra ℝ 𝕜] [CompleteSpace 𝕜] (e : X ≃ₕ Y) :
    ((splitK0PullbackEquiv 𝕜 e :
        SplitK0 (FiniteRankBundleCore 𝕜 Y) ≃+ SplitK0 (FiniteRankBundleCore 𝕜 X)) :
      SplitK0 (FiniteRankBundleCore 𝕜 Y) →+ SplitK0 (FiniteRankBundleCore 𝕜 X)) =
      SplitK0.map (pullbackFunctor (𝕜 := 𝕜) e.toFun) :=
  AddMonoidHom.ext fun _ ↦ rfl

@[simp]
theorem splitK0PullbackEquiv_symm (𝕜 : Type v) [NontriviallyNormedField 𝕜]
    [NormedAlgebra ℝ 𝕜] [CompleteSpace 𝕜] (e : X ≃ₕ Y) :
    (splitK0PullbackEquiv 𝕜 e).symm = splitK0PullbackEquiv 𝕜 e.symm :=
  AddEquiv.ext fun _ ↦ rfl

@[simp]
theorem splitK0PullbackEquiv_refl (𝕜 : Type v) [NontriviallyNormedField 𝕜]
    [NormedAlgebra ℝ 𝕜] [CompleteSpace 𝕜] (X : Type u) [TopologicalSpace X]
    [R1Space X] [ParacompactSpace X] :
    splitK0PullbackEquiv 𝕜 (ContinuousMap.HomotopyEquiv.refl X) =
      AddEquiv.refl (SplitK0 (FiniteRankBundleCore 𝕜 X)) :=
  AddEquiv.toAddMonoidHom_injective <| SplitK0.hom_ext fun A ↦ by
    have hrefl : (ContinuousMap.HomotopyEquiv.refl X).toFun = .id X := by
      ext a
      simp
    simp [hrefl]

@[simp]
theorem splitK0PullbackEquiv_trans {Z : Type z} [TopologicalSpace Z] [R1Space Z]
    [ParacompactSpace Z] (𝕜 : Type v) [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]
    [CompleteSpace 𝕜] (e₁ : X ≃ₕ Y) (e₂ : Y ≃ₕ Z) :
    splitK0PullbackEquiv 𝕜 (e₁.trans e₂) =
      (splitK0PullbackEquiv 𝕜 e₂).trans (splitK0PullbackEquiv 𝕜 e₁) :=
  AddEquiv.toAddMonoidHom_injective <| SplitK0.hom_ext fun A ↦ by
    have htrans : (e₁.trans e₂).toFun = e₂.toFun.comp e₁.toFun := by
      ext a
      simp
    simp [htrans]

end HomotopyEquiv

end GrothendieckGroup

end TauCeti.FiniteRankBundleCore
