/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Pullback
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteRank.Biproduct
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteRank.Dual
public import TauCeti.Geometry.Manifold.VectorBundle.Pullback

/-!
# `C^n` and holomorphic pullbacks of finite-rank bundle cores

Pulling back a `C^n` point-indexed finite-rank vector-bundle core `A : FiniteRankBundleCore 𝕜 Y`
along a `C^n` map `f : C(X, Y)` preserves `C^n` regularity of the transition cocycle
(`FiniteRankBundleCore.isContMDiff_pullback_of_contMDiff`,
`FiniteRankBundleCore.isContMDiff_pullback`), making `(A.pullback f).core.Fiber` a `C^n` vector
bundle over `X`. Over complex models `𝓘(ℂ, EX)` and `𝓘(ℂ, EY)` at `n = ∞`, this equips the
pullback of a holomorphic vector-bundle core along a holomorphic map with its holomorphic
vector-bundle structure on the point-indexed core `A.pullback f`.

The topological comparison `FiniteRankBundleCore.pullbackHomeomorph` with Mathlib's native pullback
carrier `TotalSpace (Fin A.rank → 𝕜) ((⇑f) *ᵖ A.core.Fiber)` upgrades unconditionally to a `C^n`
diffeomorphism `FiniteRankBundleCore.pullbackTotalSpaceDiffeomorph`, with no smoothness assumption
on `f`, on the base atlases, or on `A`, and without completeness of `𝕜`: in the preferred bundle
charts over each point `x : X`, both total spaces use the same fibre coordinate.

Via `pullbackTotalSpaceDiffeomorph`, Mathlib's pullback universal property transfers directly to
`(A.pullback f).core.TotalSpace`:

* `FiniteRankBundleCore.contMDiff_pullbackLift` and
  `FiniteRankBundleCore.contMDiff_core_pullback_iff` show that when `f` is `C^n`,
  `A.pullbackLift f` is `C^n` and a map into `(A.pullback f).core.TotalSpace` is `C^n` if and only
  if its base projection and its lift to `A.core.TotalSpace` are `C^n`;
* `FiniteRankBundleCore.contMDiff_totalSpaceMap_pullbackMap` and
  `FiniteRankBundleCore.pullbackMapIsoDiffeomorph` show that `C^n` bundle morphisms and core
  isomorphisms pull back along `C^n` maps to `C^n` total-space maps and diffeomorphisms without
  completeness or `IsContMDiff` hypotheses, while `FiniteRankBundleCore.pullbackMapDiffeomorph`
  glues pulled-back `C^n` chart-operator isomorphisms over a complete scalar field;
* along a surjective `C^n` local diffeomorphism `f`, `IsContMDiff` core regularity as well as `C^m`
  total-space regularity of bundle morphisms and sections (`m ≤ n`) descend from `X` to `Y`
  (`IsLocalDiffeomorph.isContMDiff_pullback_iff`,
  `IsLocalDiffeomorph.contMDiff_totalSpaceMap_pullbackMap_iff`,
  `IsLocalDiffeomorph.contMDiff_section_pullback_core_iff`);
* `FiniteRankBundleCore.pullbackIdDiffeomorph` (built from `Bundle.Pullback.idDiffeomorph`) and the
  compatibility lemmas with `Bundle.Pullback.compDiffeomorph`,
  `FiniteRankBundleCore.whitneySumTotalSpaceDiffeomorph`, and
  `FiniteRankBundleCore.dualTotalSpaceDiffeomorph` align identity, composition, Whitney-sum, and
  dual pullbacks on the reconstructed core and Mathlib pullback carriers.

## References

* Norman Steenrod, *The Topology of Fibre Bundles*, Princeton University Press, 1951, §2–§3, §10.
* Dale Husemoller, *Fibre Bundles*, 3rd ed., Graduate Texts in Mathematics 20, Springer, 1994,
  Chapter 2.
* Daniel Huybrechts, *Complex Geometry: An Introduction*, Springer, 2005, §2.2.
-/

public section

open Bundle CategoryTheory VectorBundleCore Set
open scoped Manifold ContDiff Topology

namespace TauCeti.FiniteRankBundleCore

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : WithTop ℕ∞}
  {EX : Type*} {HX : Type*} [NormedAddCommGroup EX] [NormedSpace 𝕜 EX] [TopologicalSpace HX]
  {IX : ModelWithCorners 𝕜 EX HX}
  {X : Type*} [TopologicalSpace X] [ChartedSpace HX X]

section MathlibPullback

variable {Y : Type*} [TopologicalSpace Y]

/-- `pullbackHomeomorph` is `C^n` on total spaces, without any smoothness assumption on `f`, on the
bases, or on `A`, and without completeness of `𝕜`. -/
theorem contMDiff_pullbackHomeomorph (A : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y)) :
    ContMDiff (IX.prod 𝓘(𝕜, Fin (A.pullback f).rank → 𝕜))
      (IX.prod 𝓘(𝕜, Fin A.rank → 𝕜)) n (A.pullbackHomeomorph f) :=
  (A.pullback f).contMDiff_of_localTriv_snd (A.pullbackHomeomorph f)
    (fun p ↦ by rw [pullbackHomeomorph_apply])
    (ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜)) fun x p ↦ by
      rw [pullback_trivializationAt_eq, A.pullbackHomeomorph_localTriv f x p]
      exact (ContinuousLinearMap.id_apply _).symm

/-- The inverse of `pullbackHomeomorph` is `C^n` on total spaces, without any smoothness assumption
on `f`, on the bases, or on `A`, and without completeness of `𝕜`. -/
theorem contMDiff_pullbackHomeomorph_symm (A : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y)) :
    ContMDiff (IX.prod 𝓘(𝕜, Fin A.rank → 𝕜))
      (IX.prod 𝓘(𝕜, Fin (A.pullback f).rank → 𝕜)) n (A.pullbackHomeomorph f).symm :=
  (A.pullback f).contMDiff_of_trivializationAt_snd (A.pullbackHomeomorph f).symm
    (fun p ↦ by rw [pullbackHomeomorph_symm_apply])
    (ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜)) fun x p ↦ by
      rw [pullback_trivializationAt_eq, ← A.pullbackHomeomorph_localTriv f x,
        Homeomorph.apply_symm_apply, ContinuousLinearMap.id_apply]

/-- The reconstructed total space of `A.pullback f` is `C^n`-diffeomorphic (and, over complex models
at `n = ∞`, biholomorphic) to the total space of Mathlib's native pullback bundle
`((⇑f) *ᵖ A.core.Fiber)`, covering the identity of `X` and acting as the identity in preferred fibre
coordinates. -/
def pullbackTotalSpaceDiffeomorph (IX : ModelWithCorners 𝕜 EX HX) (n : WithTop ℕ∞)
    (A : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y)) :
    (A.pullback f).core.TotalSpace
      ≃ₘ^n⟮IX.prod 𝓘(𝕜, Fin (A.pullback f).rank → 𝕜), IX.prod 𝓘(𝕜, Fin A.rank → 𝕜)⟯
      TotalSpace (Fin A.rank → 𝕜) ((⇑f) *ᵖ A.core.Fiber) where
  toEquiv := (A.pullbackHomeomorph f).toEquiv
  contMDiff_toFun := contMDiff_pullbackHomeomorph A f
  contMDiff_invFun := contMDiff_pullbackHomeomorph_symm A f

/-- `pullbackTotalSpaceDiffeomorph` acts as the identity on base points and preferred fibre
coordinates. -/
@[simp]
theorem pullbackTotalSpaceDiffeomorph_apply (IX : ModelWithCorners 𝕜 EX HX) (n : WithTop ℕ∞)
    (A : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y)) (p : (A.pullback f).core.TotalSpace) :
    pullbackTotalSpaceDiffeomorph IX n A f p = ⟨p.proj, p.2⟩ :=
  A.pullbackHomeomorph_apply f p

/-- The inverse of `pullbackTotalSpaceDiffeomorph` acts as the identity on base points and preferred
fibre coordinates. -/
@[simp]
theorem pullbackTotalSpaceDiffeomorph_symm_apply (IX : ModelWithCorners 𝕜 EX HX) (n : WithTop ℕ∞)
    (A : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y))
    (p : TotalSpace (Fin A.rank → 𝕜) ((⇑f) *ᵖ A.core.Fiber)) :
    (pullbackTotalSpaceDiffeomorph IX n A f).symm p = ⟨p.proj, p.2⟩ :=
  A.pullbackHomeomorph_symm_apply f p

/-- The underlying homeomorphism of `pullbackTotalSpaceDiffeomorph` is `pullbackHomeomorph`. -/
@[simp]
theorem toHomeomorph_pullbackTotalSpaceDiffeomorph (IX : ModelWithCorners 𝕜 EX HX)
    (n : WithTop ℕ∞) (A : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y)) :
    (pullbackTotalSpaceDiffeomorph IX n A f).toHomeomorph = A.pullbackHomeomorph f :=
  Homeomorph.ext fun _ ↦ rfl

/-- Mathlib's `Pullback.lift f` composed with `pullbackTotalSpaceDiffeomorph` is `pullbackLift`. -/
theorem lift_pullbackTotalSpaceDiffeomorph (IX : ModelWithCorners 𝕜 EX HX) (n : WithTop ℕ∞)
    (A : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y)) (p : (A.pullback f).core.TotalSpace) :
    Pullback.lift f (pullbackTotalSpaceDiffeomorph IX n A f p) = A.pullbackLift f p :=
  A.lift_pullbackHomeomorph f p

/-- `pullbackTotalSpaceDiffeomorph` carries the core chart at `i` to Mathlib's pullback of the chart
at `f i`. -/
theorem pullbackTotalSpaceDiffeomorph_localTriv (IX : ModelWithCorners 𝕜 EX HX) (n : WithTop ℕ∞)
    (A : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y)) (i : X) (p : (A.pullback f).core.TotalSpace) :
    (A.core.localTriv (f i)).pullback f (pullbackTotalSpaceDiffeomorph IX n A f p) =
      (A.pullback f).core.localTriv i p :=
  A.pullbackHomeomorph_localTriv f i p

/-- `pullbackTotalSpaceDiffeomorph` intertwines pulled-back bundle morphisms with Mathlib's
canonical lift to the original total space. -/
theorem pullbackTotalSpaceDiffeomorph_naturality (IX : ModelWithCorners 𝕜 EX HX) (n : WithTop ℕ∞)
    {A D : FiniteRankBundleCore 𝕜 Y} (a : A ⟶ D) (f : C(X, Y))
    (p : (A.pullback f).core.TotalSpace) :
    Pullback.lift f (pullbackTotalSpaceDiffeomorph IX n D f ((pullbackMap a f).totalSpaceMap p)) =
      a.totalSpaceMap (Pullback.lift f (pullbackTotalSpaceDiffeomorph IX n A f p)) :=
  pullbackHomeomorph_naturality a f p

end MathlibPullback

section PullbackRegularity

variable {EY : Type*} {HY : Type*} [NormedAddCommGroup EY] [NormedSpace 𝕜 EY]
  [TopologicalSpace HY] {IY : ModelWithCorners 𝕜 EY HY}
  {Y : Type*} [TopologicalSpace Y] [ChartedSpace HY Y]

/-- Pulling back a `C^n` finite-rank bundle core along a `C^n` map `f : C(X, Y)` produces a `C^n`
finite-rank bundle core. Over complex models at `n = ∞`, this equips the pullback of a holomorphic
vector-bundle core along a holomorphic map with its holomorphic vector-bundle structure on the
point-indexed core `A.pullback f`. -/
theorem isContMDiff_pullback_of_contMDiff (A : FiniteRankBundleCore 𝕜 Y)
    [A.core.IsContMDiff IY n] {f : C(X, Y)} (hf : ContMDiff IX IY n f) :
    (A.pullback f).core.IsContMDiff IX n where
  contMDiffOn_coordChange i j := by
    dsimp +instances only [pullback]
    exact (A.core.contMDiffOn_coordChange IY (f i) (f j)).comp hf.contMDiffOn fun _ hx ↦ hx

/-- For a `C^n` finite-rank bundle core `A` over `Y` and a bundled `C^n` map
`f : C^n⟮IX, X; IY, Y⟯`, the pulled-back core `A.pullback (f : C(X, Y))` is `C^n`. -/
instance isContMDiff_pullback (A : FiniteRankBundleCore 𝕜 Y) [A.core.IsContMDiff IY n]
    (f : C^n⟮IX, X; IY, Y⟯) : (A.pullback (f : C(X, Y))).core.IsContMDiff IX n :=
  isContMDiff_pullback_of_contMDiff A f.contMDiff

/-- If `a : A ⟶ D` has a `C^n` `(f i, f j)` chart operator and `f` is `C^n` on the pulled-back
chart overlap, then `pullbackMap a f` has a `C^n` `(i, j)` chart operator. -/
theorem contMDiffOn_inChartCoordinates_pullbackMap {A D : FiniteRankBundleCore 𝕜 Y} (a : A ⟶ D)
    {f : C(X, Y)} {i j : X}
    (ha : ContMDiffOn IY 𝓘(𝕜, (Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜)) n
      (fun y ↦ A.core.inChartCoordinates D.core (f i) (f j) y (a.fiberMap y))
      (A.core.baseSet (f i) ∩ D.core.baseSet (f j)))
    (hf : ContMDiffOn IX IY n f
      ((A.pullback f).core.baseSet i ∩ (D.pullback f).core.baseSet j)) :
    ContMDiffOn IX 𝓘(𝕜, (Fin (A.pullback f).rank → 𝕜) →L[𝕜] (Fin (D.pullback f).rank → 𝕜)) n
      (fun x ↦ (A.pullback f).core.inChartCoordinates (D.pullback f).core i j x
        ((pullbackMap a f).fiberMap x))
      ((A.pullback f).core.baseSet i ∩ (D.pullback f).core.baseSet j) := by
  refine (ha.comp hf fun _ hx ↦ hx).congr fun x _ ↦ ?_
  rw [Function.comp_apply, fiberMap_pullbackMap, inChartCoordinates_pullback]

/-- The canonical lift `A.pullbackLift f` is `C^n` at every total-space point over which `f` is
`C^n`. -/
theorem contMDiffAt_pullbackLift (A : FiniteRankBundleCore 𝕜 Y) {f : C(X, Y)}
    {p : (A.pullback f).core.TotalSpace} (hf : ContMDiffAt IX IY n f p.proj) :
    ContMDiffAt (IX.prod 𝓘(𝕜, Fin (A.pullback f).rank → 𝕜))
      (IY.prod 𝓘(𝕜, Fin A.rank → 𝕜)) n (A.pullbackLift f) p := by
  have hcomp : A.pullbackLift f =
      Pullback.lift f ∘ pullbackTotalSpaceDiffeomorph IX n A f :=
    funext fun q ↦ (lift_pullbackTotalSpaceDiffeomorph IX n A f q).symm
  have hf' : ContMDiffAt IX IY n f (pullbackTotalSpaceDiffeomorph IX n A f p).proj := by
    rwa [pullbackTotalSpaceDiffeomorph_apply]
  rw [hcomp]
  exact (Bundle.Pullback.contMDiffAt_lift f hf').comp p
    (pullbackTotalSpaceDiffeomorph IX n A f).contMDiff.contMDiffAt

/-- The canonical lift `A.pullbackLift f` is `C^n` when `f` is `C^n`. -/
theorem contMDiff_pullbackLift (A : FiniteRankBundleCore 𝕜 Y) {f : C(X, Y)}
    (hf : ContMDiff IX IY n f) :
    ContMDiff (IX.prod 𝓘(𝕜, Fin (A.pullback f).rank → 𝕜))
      (IY.prod 𝓘(𝕜, Fin A.rank → 𝕜)) n (A.pullbackLift f) :=
  fun p ↦ contMDiffAt_pullbackLift A (hf p.proj)

section UniversalProperty

variable {EZ : Type*} {HZ : Type*} {Z : Type*} [NormedAddCommGroup EZ] [NormedSpace 𝕜 EZ]
  [TopologicalSpace HZ] {IZ : ModelWithCorners 𝕜 EZ HZ} [TopologicalSpace Z] [ChartedSpace HZ Z]

/-- When `f` is `C^n` at `(q z).proj`, a map `q` into `(A.pullback f).core.TotalSpace` is `C^n` at
`z` if and only if its base projection and its lift to `A.core.TotalSpace` are `C^n` at `z`. -/
theorem contMDiffAt_core_pullback_iff (A : FiniteRankBundleCore 𝕜 Y) {f : C(X, Y)}
    {q : Z → (A.pullback f).core.TotalSpace} {z : Z}
    (hf : ContMDiffAt IX IY n f (q z).proj) :
    ContMDiffAt IZ (IX.prod 𝓘(𝕜, Fin (A.pullback f).rank → 𝕜)) n q z ↔
      ContMDiffAt IZ IX n (fun w ↦ (q w).proj) z ∧
        ContMDiffAt IZ (IY.prod 𝓘(𝕜, Fin A.rank → 𝕜)) n
          (fun w ↦ A.pullbackLift f (q w)) z := by
  have hf' : ContMDiffAt IX IY n f ((pullbackTotalSpaceDiffeomorph IX n A f ∘ q) z).proj := by
    rwa [Function.comp_apply, pullbackTotalSpaceDiffeomorph_apply]
  have h₁ : (fun y ↦ ((pullbackTotalSpaceDiffeomorph IX n A f ∘ q) y).proj) =
      fun w ↦ (q w).proj :=
    funext fun y ↦ congrArg TotalSpace.proj (pullbackTotalSpaceDiffeomorph_apply IX n A f (q y))
  have h₂ : (fun y ↦ Pullback.lift f ((pullbackTotalSpaceDiffeomorph IX n A f ∘ q) y)) =
      fun w ↦ A.pullbackLift f (q w) :=
    funext fun y ↦ lift_pullbackTotalSpaceDiffeomorph IX n A f (q y)
  rw [← (pullbackTotalSpaceDiffeomorph IX n A f).contMDiffAt_diffeomorph_comp_iff le_rfl,
    Bundle.Pullback.contMDiffAt_iff f (q := pullbackTotalSpaceDiffeomorph IX n A f ∘ q) hf',
    h₁, h₂]

/-- When `f` is `C^n`, a map `q` into `(A.pullback f).core.TotalSpace` is `C^n` if and only if its
base projection and its lift to `A.core.TotalSpace` are `C^n`. -/
theorem contMDiff_core_pullback_iff (A : FiniteRankBundleCore 𝕜 Y) {f : C(X, Y)}
    (hf : ContMDiff IX IY n f) {q : Z → (A.pullback f).core.TotalSpace} :
    ContMDiff IZ (IX.prod 𝓘(𝕜, Fin (A.pullback f).rank → 𝕜)) n q ↔
      ContMDiff IZ IX n (fun w ↦ (q w).proj) ∧
        ContMDiff IZ (IY.prod 𝓘(𝕜, Fin A.rank → 𝕜)) n (fun w ↦ A.pullbackLift f (q w)) := by
  simp only [ContMDiff, ← forall_and]
  exact forall_congr' fun z ↦ contMDiffAt_core_pullback_iff A hf.contMDiffAt

end UniversalProperty

/-- Pulling back a bundle morphism whose total-space map is `C^n` along a `C^n` map `f` yields a
bundle morphism whose total-space map is `C^n`, without completeness of `𝕜` or `IsContMDiff`
hypotheses on the cores. -/
theorem contMDiff_totalSpaceMap_pullbackMap {A D : FiniteRankBundleCore 𝕜 Y} (a : A ⟶ D)
    (ha : ContMDiff (IY.prod 𝓘(𝕜, Fin A.rank → 𝕜)) (IY.prod 𝓘(𝕜, Fin D.rank → 𝕜)) n
      a.totalSpaceMap)
    {f : C(X, Y)} (hf : ContMDiff IX IY n f) :
    ContMDiff (IX.prod 𝓘(𝕜, Fin (A.pullback f).rank → 𝕜))
      (IX.prod 𝓘(𝕜, Fin (D.pullback f).rank → 𝕜)) n (pullbackMap a f).totalSpaceMap := by
  refine (contMDiff_core_pullback_iff D hf).2 ⟨?_, ?_⟩
  · exact (contMDiff_proj _).congr fun p ↦ (pullbackMap a f).totalSpaceMap_proj p
  · exact (ha.comp (contMDiff_pullbackLift A hf)).congr fun p ↦ pullbackLift_totalSpaceMap a f p

/-- Pulling back a core isomorphism `e : A ≅ D` with `C^n` forward and inverse total-space maps
along a `C^n` map `f` yields a `C^n` diffeomorphism of pulled-back total spaces, without
completeness of `𝕜` or `IsContMDiff` hypotheses on the cores. -/
def pullbackMapIsoDiffeomorph {A D : FiniteRankBundleCore 𝕜 Y} (e : A ≅ D)
    (he : ContMDiff (IY.prod 𝓘(𝕜, Fin A.rank → 𝕜)) (IY.prod 𝓘(𝕜, Fin D.rank → 𝕜)) n
      e.hom.totalSpaceMap)
    (he' : ContMDiff (IY.prod 𝓘(𝕜, Fin D.rank → 𝕜)) (IY.prod 𝓘(𝕜, Fin A.rank → 𝕜)) n
      e.inv.totalSpaceMap)
    {f : C(X, Y)} (hf : ContMDiff IX IY n f) :
    (A.pullback f).core.TotalSpace
      ≃ₘ^n⟮IX.prod 𝓘(𝕜, Fin (A.pullback f).rank → 𝕜),
        IX.prod 𝓘(𝕜, Fin (D.pullback f).rank → 𝕜)⟯
      (D.pullback f).core.TotalSpace :=
  CoordinateHom.toDiffeomorphOfInv ((pullbackFunctor f).mapIso e).hom
    ((pullbackFunctor f).mapIso e).inv
    ((pullbackFunctor f).mapIso e).hom_inv_id
    ((pullbackFunctor f).mapIso e).inv_hom_id
    (contMDiff_totalSpaceMap_pullbackMap e.hom he hf)
    (contMDiff_totalSpaceMap_pullbackMap e.inv he' hf)

/-- `pullbackMapIsoDiffeomorph` acts on total spaces as `(pullbackMap e.hom f).totalSpaceMap`. -/
@[simp]
theorem coe_pullbackMapIsoDiffeomorph {A D : FiniteRankBundleCore 𝕜 Y} (e : A ≅ D)
    (he : ContMDiff (IY.prod 𝓘(𝕜, Fin A.rank → 𝕜)) (IY.prod 𝓘(𝕜, Fin D.rank → 𝕜)) n
      e.hom.totalSpaceMap)
    (he' : ContMDiff (IY.prod 𝓘(𝕜, Fin D.rank → 𝕜)) (IY.prod 𝓘(𝕜, Fin A.rank → 𝕜)) n
      e.inv.totalSpaceMap)
    {f : C(X, Y)} (hf : ContMDiff IX IY n f) :
    ⇑(pullbackMapIsoDiffeomorph e he he' hf) = (pullbackMap e.hom f).totalSpaceMap := by
  simp [pullbackMapIsoDiffeomorph]

/-- The inverse of `pullbackMapIsoDiffeomorph` acts on total spaces as
`(pullbackMap e.inv f).totalSpaceMap`. -/
@[simp]
theorem coe_pullbackMapIsoDiffeomorph_symm {A D : FiniteRankBundleCore 𝕜 Y} (e : A ≅ D)
    (he : ContMDiff (IY.prod 𝓘(𝕜, Fin A.rank → 𝕜)) (IY.prod 𝓘(𝕜, Fin D.rank → 𝕜)) n
      e.hom.totalSpaceMap)
    (he' : ContMDiff (IY.prod 𝓘(𝕜, Fin D.rank → 𝕜)) (IY.prod 𝓘(𝕜, Fin A.rank → 𝕜)) n
      e.inv.totalSpaceMap)
    {f : C(X, Y)} (hf : ContMDiff IX IY n f) :
    ⇑(pullbackMapIsoDiffeomorph e he he' hf).symm = (pullbackMap e.inv f).totalSpaceMap := by
  simp [pullbackMapIsoDiffeomorph]

section CompleteSpace

variable [CompleteSpace 𝕜]

/-- On every fibre, the continuous linear equivalence `CoordinateHom.fiberEquiv` of a pulled-back
cocycle morphism `pullbackMap a f` agrees with that of `a` at `f x`. -/
theorem fiberEquiv_pullbackMap {A D : FiniteRankBundleCore 𝕜 Y} (a : A ⟶ D)
    (hbij : ∀ y, Function.Bijective (a.fiberMap y)) (f : C(X, Y))
    (hbij' : ∀ x, Function.Bijective ((pullbackMap a f).fiberMap x)) (x : X) :
    (pullbackMap a f).fiberEquiv hbij' x = a.fiberEquiv hbij (f x) := by
  ext v
  rw [CoordinateHom.fiberEquiv_apply, fiberMap_pullbackMap]
  -- Both fibres are `Fin A.rank → 𝕜` (`rank_pullback`), matching `CoordinateHom.fiberEquiv_apply`.
  exact (CoordinateHom.fiberEquiv_apply a hbij (f x) v).symm

/-- Over a complete scalar field, pulling back a cocycle morphism `a : A ⟶ D` between `C^n` cores
with `C^n` chart operators and bijective fibre maps along a `C^n` map `f` produces a `C^n`
diffeomorphism of pulled-back total spaces. -/
noncomputable def pullbackMapDiffeomorph {A D : FiniteRankBundleCore 𝕜 Y}
    [A.core.IsContMDiff IY n] [D.core.IsContMDiff IY n] (a : A ⟶ D)
    (ha : ∀ i j, ContMDiffOn IY 𝓘(𝕜, (Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜)) n
      (fun y ↦ A.core.inChartCoordinates D.core i j y (a.fiberMap y))
      (A.core.baseSet i ∩ D.core.baseSet j))
    (hbij : ∀ y, Function.Bijective (a.fiberMap y))
    {f : C(X, Y)} (hf : ContMDiff IX IY n f) :
    (A.pullback f).core.TotalSpace
      ≃ₘ^n⟮IX.prod 𝓘(𝕜, Fin (A.pullback f).rank → 𝕜),
        IX.prod 𝓘(𝕜, Fin (D.pullback f).rank → 𝕜)⟯
      (D.pullback f).core.TotalSpace := by
  letI := isContMDiff_pullback_of_contMDiff A hf
  letI := isContMDiff_pullback_of_contMDiff D hf
  exact (pullbackMap a f).toDiffeomorph
    (fun i j ↦ contMDiffOn_inChartCoordinates_pullbackMap a (ha (f i) (f j)) hf.contMDiffOn)
    (bijective_fiberMap_pullbackMap a hbij f)

/-- `pullbackMapDiffeomorph` acts on total spaces as `(pullbackMap a f).totalSpaceMap`. -/
@[simp]
theorem coe_pullbackMapDiffeomorph {A D : FiniteRankBundleCore 𝕜 Y}
    [A.core.IsContMDiff IY n] [D.core.IsContMDiff IY n] (a : A ⟶ D)
    (ha : ∀ i j, ContMDiffOn IY 𝓘(𝕜, (Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜)) n
      (fun y ↦ A.core.inChartCoordinates D.core i j y (a.fiberMap y))
      (A.core.baseSet i ∩ D.core.baseSet j))
    (hbij : ∀ y, Function.Bijective (a.fiberMap y))
    {f : C(X, Y)} (hf : ContMDiff IX IY n f) :
    ⇑(pullbackMapDiffeomorph a ha hbij hf) = (pullbackMap a f).totalSpaceMap := by
  simp only [pullbackMapDiffeomorph, CoordinateHom.coe_toDiffeomorph]

/-- The inverse of `pullbackMapDiffeomorph` acts on the fibre over `x` by the inverse of
`a.fiberEquiv hbij (f x)`. -/
@[simp]
theorem pullbackMapDiffeomorph_symm_apply {A D : FiniteRankBundleCore 𝕜 Y}
    [A.core.IsContMDiff IY n] [D.core.IsContMDiff IY n] (a : A ⟶ D)
    (ha : ∀ i j, ContMDiffOn IY 𝓘(𝕜, (Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜)) n
      (fun y ↦ A.core.inChartCoordinates D.core i j y (a.fiberMap y))
      (A.core.baseSet i ∩ D.core.baseSet j))
    (hbij : ∀ y, Function.Bijective (a.fiberMap y))
    {f : C(X, Y)} (hf : ContMDiff IX IY n f) (p : (D.pullback f).core.TotalSpace) :
    (pullbackMapDiffeomorph a ha hbij hf).symm p =
      ⟨p.proj, (a.fiberEquiv hbij (f p.proj)).symm p.2⟩ := by
  simp only [pullbackMapDiffeomorph, CoordinateHom.toDiffeomorph_symm_apply,
    fiberEquiv_pullbackMap a hbij]
  -- Both fibres are `Fin A.rank → 𝕜` definitionally, as recorded by `rank_pullback`.
  rfl

end CompleteSpace

end PullbackRegularity

section LocalDiffeomorph

variable {EY : Type*} {HY : Type*} [NormedAddCommGroup EY] [NormedSpace 𝕜 EY]
  [TopologicalSpace HY] {IY : ModelWithCorners 𝕜 EY HY}
  {Y : Type*} [TopologicalSpace Y] [ChartedSpace HY Y]
  {m : WithTop ℕ∞}

/-- Along a surjective `C^n` local diffeomorphism `f : C(X, Y)` with `m ≤ n`, the pulled-back core
`A.pullback f` is `C^m` if and only if `A` is `C^m`. -/
theorem _root_.IsLocalDiffeomorph.isContMDiff_pullback_iff {f : C(X, Y)}
    (hf : IsLocalDiffeomorph IX IY n f) (hsurj : Function.Surjective f) (hm : m ≤ n)
    (A : FiniteRankBundleCore 𝕜 Y) :
    (A.pullback f).core.IsContMDiff IX m ↔ A.core.IsContMDiff IY m := by
  refine ⟨fun hpull ↦ ⟨fun y₁ y₂ y₀ hy₀ ↦ ?_⟩,
    fun _ ↦ isContMDiff_pullback_of_contMDiff A (hf.contMDiff.of_le hm)⟩
  obtain ⟨i, rfl⟩ := hsurj y₁
  obtain ⟨j, rfl⟩ := hsurj y₂
  obtain ⟨x₀, rfl⟩ := hsurj y₀
  have hUopen : IsOpen ((A.pullback f).core.baseSet i ∩ (A.pullback f).core.baseSet j) :=
    ((A.pullback f).core.isOpen_baseSet i).inter ((A.pullback f).core.isOpen_baseSet j)
  have hcoord : ContMDiffAt IX 𝓘(𝕜, (Fin A.rank → 𝕜) →L[𝕜] (Fin A.rank → 𝕜)) m
      (A.core.coordChange (f i) (f j) ∘ f) x₀ :=
    (hpull.contMDiffOn_coordChange i j).contMDiffAt (hUopen.mem_nhds hy₀)
  exact (((hf x₀).contMDiffAt_comp_iff hm).1 hcoord).contMDiffWithinAt

section TargetManifold

variable {EZ : Type*} {HZ : Type*} {Z : Type*} [NormedAddCommGroup EZ] [NormedSpace 𝕜 EZ]
  [TopologicalSpace HZ] {IZ : ModelWithCorners 𝕜 EZ HZ} [TopologicalSpace Z] [ChartedSpace HZ Z]

/-- If `f : C(X, Y)` is a `C^n` local diffeomorphism at `x` and `m ≤ n`, a map `g` out of
`A.core.TotalSpace` is `C^m` at `⟨f x, v⟩` if and only if `g ∘ A.pullbackLift f` is `C^m` at
`⟨x, v⟩`. -/
theorem _root_.IsLocalDiffeomorphAt.contMDiffAt_comp_pullbackLift_iff {f : C(X, Y)} {x : X}
    (hf : IsLocalDiffeomorphAt IX IY n f x) (hm : m ≤ n)
    {A : FiniteRankBundleCore 𝕜 Y} {g : A.core.TotalSpace → Z} (v : Fin A.rank → 𝕜) :
    ContMDiffAt (IX.prod 𝓘(𝕜, Fin (A.pullback f).rank → 𝕜)) IZ m
        (g ∘ A.pullbackLift f) ⟨x, v⟩ ↔
      ContMDiffAt (IY.prod 𝓘(𝕜, Fin A.rank → 𝕜)) IZ m g ⟨f x, v⟩ := by
  refine ⟨fun hg ↦ ?_,
    fun hg ↦ hg.comp_of_eq (contMDiffAt_pullbackLift A (hf.contMDiffAt.of_le hm))
      (A.pullbackLift_mk f x v)⟩
  let q₀ : A.core.TotalSpace := ⟨f x, v⟩
  let s : A.core.TotalSpace → (A.pullback f).core.TotalSpace :=
    fun q ↦ ⟨hf.localInverse q.proj, q.2⟩
  have hsq₀ : s q₀ = ⟨x, v⟩ :=
    congrArg (fun x' ↦ (⟨x', v⟩ : (A.pullback f).core.TotalSpace))
      (hf.localInverse_left_inv hf.localInverse_mem_target)
  have hproj : ContMDiffAt (IY.prod 𝓘(𝕜, Fin A.rank → 𝕜)) IX m
      (fun q : A.core.TotalSpace ↦ hf.localInverse q.proj) q₀ :=
    (hf.contMDiffAt_localInverse.of_le hm).comp q₀ (contMDiff_proj A.core.Fiber).contMDiffAt
  have heq : (fun q ↦ A.pullbackLift f (s q)) =ᶠ[nhds q₀] id := by
    filter_upwards [hf.localInverse_eventuallyEq_right.comp_tendsto
      (A.core.continuous_proj.tendsto q₀)] with q (hy : f (hf.localInverse q.proj) = q.proj)
    exact A.pullbackLift_eq_mk f (s q) hy rfl
  have hs : ContMDiffAt (IY.prod 𝓘(𝕜, Fin A.rank → 𝕜))
      (IX.prod 𝓘(𝕜, Fin (A.pullback f).rank → 𝕜)) m s q₀ :=
    (contMDiffAt_core_pullback_iff A
      (by simpa only [hsq₀] using hf.contMDiffAt.of_le hm)).2
      ⟨hproj, contMDiffAt_id.congr_of_eventuallyEq heq⟩
  exact (hg.comp_of_eq hs hsq₀).congr_of_eventuallyEq (heq.fun_comp g).symm

/-- If `f : C(X, Y)` is a surjective `C^n` local diffeomorphism and `m ≤ n`, a map `g` out of
`A.core.TotalSpace` is `C^m` if and only if `g ∘ A.pullbackLift f` is `C^m`. -/
theorem _root_.IsLocalDiffeomorph.contMDiff_comp_pullbackLift_iff {f : C(X, Y)}
    (hf : IsLocalDiffeomorph IX IY n f) (hsurj : Function.Surjective f) (hm : m ≤ n)
    {A : FiniteRankBundleCore 𝕜 Y} {g : A.core.TotalSpace → Z} :
    ContMDiff (IX.prod 𝓘(𝕜, Fin (A.pullback f).rank → 𝕜)) IZ m (g ∘ A.pullbackLift f) ↔
      ContMDiff (IY.prod 𝓘(𝕜, Fin A.rank → 𝕜)) IZ m g := by
  refine ⟨fun hg ⟨y, v⟩ ↦ ?_,
    fun hg ↦ hg.comp (contMDiff_pullbackLift A (hf.contMDiff.of_le hm))⟩
  obtain ⟨x, rfl⟩ := hsurj y
  exact ((hf x).contMDiffAt_comp_pullbackLift_iff hm v).1 (hg ⟨x, v⟩)

end TargetManifold

/-- Along a surjective `C^n` local diffeomorphism `f : C(X, Y)` with `m ≤ n`, a bundle morphism
`a : A ⟶ D` has a `C^m` total-space map if and only if `pullbackMap a f` does. -/
theorem _root_.IsLocalDiffeomorph.contMDiff_totalSpaceMap_pullbackMap_iff {f : C(X, Y)}
    (hf : IsLocalDiffeomorph IX IY n f) (hsurj : Function.Surjective f) (hm : m ≤ n)
    {A D : FiniteRankBundleCore 𝕜 Y} (a : A ⟶ D) :
    ContMDiff (IX.prod 𝓘(𝕜, Fin (A.pullback f).rank → 𝕜))
        (IX.prod 𝓘(𝕜, Fin (D.pullback f).rank → 𝕜)) m (pullbackMap a f).totalSpaceMap ↔
      ContMDiff (IY.prod 𝓘(𝕜, Fin A.rank → 𝕜)) (IY.prod 𝓘(𝕜, Fin D.rank → 𝕜)) m
        a.totalSpaceMap := by
  refine ⟨fun hpull ↦ (hf.contMDiff_comp_pullbackLift_iff hsurj hm).1 ?_,
    fun ha ↦ contMDiff_totalSpaceMap_pullbackMap a ha (hf.contMDiff.of_le hm)⟩
  exact ((contMDiff_pullbackLift D (hf.contMDiff.of_le hm)).comp hpull).congr
    fun p ↦ (pullbackLift_totalSpaceMap a f p).symm

/-- If `f : C(X, Y)` is a `C^n` local diffeomorphism at `x` and `m ≤ n`, a pulled-back section
`x' ↦ σ (f x')` of `A.pullback f` is `C^m` at `x` if and only if the section `σ` of `A` is `C^m`
at `f x`. -/
theorem _root_.IsLocalDiffeomorphAt.contMDiffAt_section_pullback_core_iff {f : C(X, Y)} {x : X}
    (hf : IsLocalDiffeomorphAt IX IY n f x) (hm : m ≤ n) (A : FiniteRankBundleCore 𝕜 Y)
    {σ : ∀ y, A.core.Fiber y} :
    ContMDiffAt IX (IX.prod 𝓘(𝕜, Fin (A.pullback f).rank → 𝕜)) m
        (fun x' ↦ TotalSpace.mk' (Fin (A.pullback f).rank → 𝕜)
          (E := (A.pullback f).core.Fiber) x' (σ (f x'))) x ↔
      ContMDiffAt IY (IY.prod 𝓘(𝕜, Fin A.rank → 𝕜)) m
        (fun y ↦ TotalSpace.mk' (Fin A.rank → 𝕜) y (σ y)) (f x) := by
  have hlift :
      (fun x' ↦ A.pullbackLift f
        (TotalSpace.mk' (Fin (A.pullback f).rank → 𝕜)
          (E := (A.pullback f).core.Fiber) x' (σ (f x')))) =
        (fun y ↦ TotalSpace.mk' (Fin A.rank → 𝕜) y (σ y)) ∘ f :=
    funext fun x' ↦ A.pullbackLift_mk f x' (σ (f x'))
  exact (contMDiffAt_core_pullback_iff A (hf.contMDiffAt.of_le hm)).trans
    ((and_iff_right contMDiffAt_id).trans (hlift ▸ hf.contMDiffAt_comp_iff hm))

/-- Along a surjective `C^n` local diffeomorphism `f : C(X, Y)` with `m ≤ n`, a pulled-back section
`x ↦ σ (f x)` of `A.pullback f` is `C^m` if and only if the section `σ` of `A` is `C^m`. -/
theorem _root_.IsLocalDiffeomorph.contMDiff_section_pullback_core_iff {f : C(X, Y)}
    (hf : IsLocalDiffeomorph IX IY n f) (hsurj : Function.Surjective f) (hm : m ≤ n)
    (A : FiniteRankBundleCore 𝕜 Y) {σ : ∀ y, A.core.Fiber y} :
    ContMDiff IX (IX.prod 𝓘(𝕜, Fin (A.pullback f).rank → 𝕜)) m
        (fun x ↦ TotalSpace.mk' (Fin (A.pullback f).rank → 𝕜)
          (E := (A.pullback f).core.Fiber) x (σ (f x))) ↔
      ContMDiff IY (IY.prod 𝓘(𝕜, Fin A.rank → 𝕜)) m
        (fun y ↦ TotalSpace.mk' (Fin A.rank → 𝕜) y (σ y)) := by
  refine ⟨fun h y ↦ ?_, fun h x ↦ ((hf x).contMDiffAt_section_pullback_core_iff hm A).2 (h (f x))⟩
  obtain ⟨x, rfl⟩ := hsurj y
  exact ((hf x).contMDiffAt_section_pullback_core_iff hm A).1 (h x)

end LocalDiffeomorph

section CoherenceAndOperations

variable {EY : Type*} {HY : Type*} [NormedAddCommGroup EY] [NormedSpace 𝕜 EY]
  [TopologicalSpace HY] {IY : ModelWithCorners 𝕜 EY HY}
  {Y : Type*} [TopologicalSpace Y] [ChartedSpace HY Y]

/-- Pulling back `A` along `ContinuousMap.id Y` yields a total space `C^n`-diffeomorphic to
`A.core.TotalSpace`, covering the identity of `Y` and acting as the identity on preferred fibre
coordinates. -/
noncomputable def pullbackIdDiffeomorph (IY : ModelWithCorners 𝕜 EY HY) (n : WithTop ℕ∞)
    (A : FiniteRankBundleCore 𝕜 Y) :
    (A.pullback (ContinuousMap.id Y)).core.TotalSpace
      ≃ₘ^n⟮IY.prod 𝓘(𝕜, Fin (A.pullback (ContinuousMap.id Y)).rank → 𝕜),
        IY.prod 𝓘(𝕜, Fin A.rank → 𝕜)⟯
      A.core.TotalSpace :=
  (pullbackTotalSpaceDiffeomorph IY n A (ContinuousMap.id Y)).trans
    (Bundle.Pullback.idDiffeomorph (I := IY) (m := n) (n := n) A.core.Fiber)

/-- `pullbackIdDiffeomorph` acts as the identity on base points and preferred fibre coordinates. -/
@[simp]
theorem pullbackIdDiffeomorph_apply (IY : ModelWithCorners 𝕜 EY HY) (n : WithTop ℕ∞)
    (A : FiniteRankBundleCore 𝕜 Y) (p : (A.pullback (ContinuousMap.id Y)).core.TotalSpace) :
    pullbackIdDiffeomorph IY n A p = ⟨p.proj, p.2⟩ := by
  -- `pullbackIdDiffeomorph` evaluates as `idDiffeomorph ∘ pullbackTotalSpaceDiffeomorph`;
  -- compare projections so `ContinuousMap.id` and `ContMDiffMap.id` do not block `rw`.
  let h := pullbackTotalSpaceDiffeomorph_apply IY n A (ContinuousMap.id Y) p
  exact (Bundle.Pullback.idDiffeomorph_apply (I := IY) (m := n) (n := n) (E := A.core.Fiber)
    (pullbackTotalSpaceDiffeomorph IY n A (ContinuousMap.id Y) p)).trans
    (TotalSpace.ext (congrArg TotalSpace.proj h) (heq_of_eq (congrArg TotalSpace.snd h)))

/-- The inverse of `pullbackIdDiffeomorph` acts as the identity on base points and preferred fibre
coordinates. -/
@[simp]
theorem pullbackIdDiffeomorph_symm_apply (IY : ModelWithCorners 𝕜 EY HY) (n : WithTop ℕ∞)
    (A : FiniteRankBundleCore 𝕜 Y) (p : A.core.TotalSpace) :
    (pullbackIdDiffeomorph IY n A).symm p = ⟨p.proj, p.2⟩ := by
  -- `(h₁.trans h₂).symm` evaluates as `h₁.symm ∘ h₂.symm`; compare projections as above.
  let h := Bundle.Pullback.idDiffeomorph_symm_apply (I := IY) (m := n) (n := n)
    (E := A.core.Fiber) p
  exact (pullbackTotalSpaceDiffeomorph_symm_apply IY n A (ContinuousMap.id Y) _).trans
    (TotalSpace.ext (congrArg TotalSpace.proj h) (heq_of_eq (congrArg TotalSpace.snd h)))

section Composition

variable {EZ : Type*} {HZ : Type*} {Z : Type*} [NormedAddCommGroup EZ] [NormedSpace 𝕜 EZ]
  [TopologicalSpace HZ] {IZ : ModelWithCorners 𝕜 EZ HZ} [TopologicalSpace Z] [ChartedSpace HZ Z]

/-- Under `Bundle.Pullback.compDiffeomorph`, the comparison `pullbackTotalSpaceDiffeomorph` for a
composite `g.comp f` agrees on every fibre with the iterated core pullback
`(A.pullback g).pullback f`. -/
theorem compDiffeomorph_pullbackTotalSpaceDiffeomorph {m : WithTop ℕ∞}
    (A : FiniteRankBundleCore 𝕜 Z) (g : C^m⟮IY, Y; IZ, Z⟯) (f : C^m⟮IX, X; IY, Y⟯)
    (p : (A.pullback ((g.comp f : C^m⟮IX, X; IZ, Z⟯) : C(X, Z))).core.TotalSpace) :
    Bundle.Pullback.compDiffeomorph (n := n) A.core.Fiber g f
        (pullbackTotalSpaceDiffeomorph IX n A (g.comp f : C(X, Z)) p) =
      ⟨p.proj, (pullbackTotalSpaceDiffeomorph IX n (A.pullback (g : C(Y, Z)))
        (f : C(X, Y)) p).2⟩ := by
  let q := pullbackTotalSpaceDiffeomorph IX n (A.pullback (g : C(Y, Z))) (f : C(X, Y)) p
  have hq : q.2 = p.2 :=
    congrArg TotalSpace.snd
      (pullbackTotalSpaceDiffeomorph_apply IX n (A.pullback (g : C(Y, Z))) (f : C(X, Y)) p)
  rw [pullbackTotalSpaceDiffeomorph_apply, hq]
  exact Bundle.Pullback.compDiffeomorph_apply g f _

/-- Under `Bundle.Pullback.compDiffeomorph` and `Pullback.lift f`, the comparison
`pullbackTotalSpaceDiffeomorph` for a composite `g.comp f` commutes on total spaces with
`(A.pullback g).pullbackLift f` and `pullbackTotalSpaceDiffeomorph` for `g`. -/
theorem lift_compDiffeomorph_pullbackTotalSpaceDiffeomorph {m : WithTop ℕ∞}
    (A : FiniteRankBundleCore 𝕜 Z) (g : C^m⟮IY, Y; IZ, Z⟯) (f : C^m⟮IX, X; IY, Y⟯)
    (p : (A.pullback ((g.comp f : C^m⟮IX, X; IZ, Z⟯) : C(X, Z))).core.TotalSpace) :
    Pullback.lift (f : C(X, Y)) (Bundle.Pullback.compDiffeomorph (n := n) A.core.Fiber g f
        (pullbackTotalSpaceDiffeomorph IX n A (g.comp f : C(X, Z)) p)) =
      pullbackTotalSpaceDiffeomorph IY n A (g : C(Y, Z))
        ((A.pullback (g : C(Y, Z))).pullbackLift (f : C(X, Y)) p) := by
  -- Rebind the intermediate points across `ContMDiffMap.coe_toContinuousMap` and `pullback_comp`
  -- so both projections are type-correct at `implicit` transparency for `simp`/`rw`.
  let q₁ : TotalSpace (Fin A.rank → 𝕜) ((g.comp f : X → Z) *ᵖ A.core.Fiber) :=
    pullbackTotalSpaceDiffeomorph IX n A (g.comp f : C(X, Z)) p
  let q₂ : ((A.pullback (g : C(Y, Z))).pullback (f : C(X, Y))).core.TotalSpace := p
  have h₁ := pullbackTotalSpaceDiffeomorph_apply IX n A (g.comp f : C(X, Z)) p
  refine TotalSpace.ext ?_ (heq_of_eq ?_)
  · change (Pullback.lift (f : C(X, Y))
        (Bundle.Pullback.compDiffeomorph (n := n) A.core.Fiber g f q₁)).proj =
      (pullbackTotalSpaceDiffeomorph IY n A (g : C(Y, Z))
        ((A.pullback (g : C(Y, Z))).pullbackLift (f : C(X, Y)) q₂)).proj
    simp only [Pullback.lift_proj, Bundle.Pullback.compDiffeomorph_apply,
      pullbackTotalSpaceDiffeomorph_apply, pullbackLift_proj]
    exact congrArg (f ∘ TotalSpace.proj) h₁
  · change (Pullback.lift (f : C(X, Y))
        (Bundle.Pullback.compDiffeomorph (n := n) A.core.Fiber g f q₁)).2 =
      (pullbackTotalSpaceDiffeomorph IY n A (g : C(Y, Z))
        ((A.pullback (g : C(Y, Z))).pullbackLift (f : C(X, Y)) q₂)).2
    rw [Pullback.lift_snd, Bundle.Pullback.compDiffeomorph_apply,
      pullbackTotalSpaceDiffeomorph_apply, pullbackLift_snd]
    exact congrArg TotalSpace.snd h₁

end Composition

/-- On a pulled-back Whitney sum, `whitneySumTotalSpaceDiffeomorph` over `X` and over `Y` agree
along `pullbackLift`. -/
theorem whitneySumTotalSpaceDiffeomorph_pullbackLift (A D : FiniteRankBundleCore 𝕜 Y)
    (f : C(X, Y)) (p : ((whitneySum A D).pullback f).core.TotalSpace) :
    whitneySumTotalSpaceDiffeomorph IY n A D ((whitneySum A D).pullbackLift f p) =
      ⟨f p.proj, (whitneySumTotalSpaceDiffeomorph IX n (A.pullback f) (D.pullback f) p).2⟩ := by
  rcases p with ⟨x, v⟩
  rw [pullbackLift_mk]
  -- Rebind the point across the definitional equality `pullback_whitneySum` so the pullback-side
  -- `whitneySumTotalSpaceDiffeomorph_apply` matches at reducible transparency.
  let q : (whitneySum (A.pullback f) (D.pullback f)).core.TotalSpace := ⟨x, v⟩
  change whitneySumTotalSpaceDiffeomorph IY n A D ⟨f x, v⟩ =
    ⟨f x, (whitneySumTotalSpaceDiffeomorph IX n (A.pullback f) (D.pullback f) q).2⟩
  rw [whitneySumTotalSpaceDiffeomorph_apply, whitneySumTotalSpaceDiffeomorph_apply]
  exact congrArg (TotalSpace.mk' _ (f x))
    (whitneySumFiberEquiv_pullback_apply A D f x q.2).symm

/-- On a pulled-back dual core, `dualTotalSpaceDiffeomorph` over `X` and over `Y` evaluate to the
same linear functional on every coordinate vector along `pullbackLift`. -/
theorem dualTotalSpaceDiffeomorph_pullbackLift [CompleteSpace 𝕜] (A : FiniteRankBundleCore 𝕜 Y)
    (f : C(X, Y)) (p : (A.dual.pullback f).core.TotalSpace) (v : Fin A.rank → 𝕜) :
    ((A.pullback f).dualTotalSpaceDiffeomorph IX n p).2 v =
      (A.dualTotalSpaceDiffeomorph IY n (A.dual.pullbackLift f p)).2 v := by
  rcases p with ⟨x, w⟩
  rw [pullbackLift_mk]
  -- Rebind the point across the definitional equality `pullback_dual` so the pullback-side
  -- `dualTotalSpaceDiffeomorph_apply` matches at reducible transparency.
  let q : (A.pullback f).dual.core.TotalSpace := ⟨x, w⟩
  change ((A.pullback f).dualTotalSpaceDiffeomorph IX n q).2 v =
    (A.dualTotalSpaceDiffeomorph IY n ⟨f x, w⟩).2 v
  rw [dualTotalSpaceDiffeomorph_apply, dualTotalSpaceDiffeomorph_apply]
  exact dualFiberEquiv_pullback_apply A f x w v

end CoherenceAndOperations

end TauCeti.FiniteRankBundleCore
