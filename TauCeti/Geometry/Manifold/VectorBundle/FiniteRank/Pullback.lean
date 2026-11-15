/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Pullback
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteRank.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteRank.Biproduct
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteRank.Dual
public import TauCeti.Geometry.Manifold.VectorBundle.Pullback

/-!
# `C^n` and holomorphic pullback of finite-rank bundle cores

If `A` is a point-indexed finite-rank vector-bundle core over a charted space `Y` with `C^n`
transition functions (`VectorBundleCore.IsContMDiff IY n`) and `f : X → Y` is `C^n`, then the
pulled-back point-indexed core `A.pullback f` has `C^n` transition functions
(`FiniteRankBundleCore.isContMDiff_pullback`, `FiniteRankBundleCore.instIsContMDiffPullback`),
making `(A.pullback f).core.Fiber` a `C^n` vector bundle on the existing topological carrier.
Over complex models `𝓘(ℂ, EX)` and `𝓘(ℂ, EY)` with `n = ∞`, this equips the pullback of a
holomorphic vector-bundle core along a holomorphic map with its holomorphic vector-bundle
structure while preserving strict equality under identity, composition, trivial bundles, Whitney
sums, duals, tensor products, and determinant lines.

On reconstructed total spaces, the comparison `pullbackHomeomorph` with Mathlib's installed
pullback bundle `(⇑f) *ᵖ A.core.Fiber` upgrades to a `C^n` (and in particular biholomorphic)
diffeomorphism `pullbackDiffeomorph` at every regularity `n`, without any smoothness assumption
on `f`, on `A`, or on the base atlases, and without completeness of the scalar field: in the
preferred chart at `x`, `pullbackHomeomorph` carries `(A.pullback f).core.localTriv x` to
`(A.core.localTriv (f x)).pullback f` as the identity on coordinates.

Transporting the pullback universal property across `pullbackDiffeomorph` gives:

* `contMDiffAt_pullback_totalSpace_iff` and `contMDiff_pullback_totalSpace_iff`: a map into
  `(A.pullback f).core.TotalSpace` is `C^n` when `f` is `C^n` if and only if its base projection
  and its canonical lift `A.pullbackLift f` into `A.core.TotalSpace` are `C^n`;
* `contMDiff_pullbackLift`, `contMDiff_totalSpaceMap_pullbackMap`, and `pullbackIsoDiffeomorph`:
  the canonical lift is `C^n`, pulling back a morphism with `C^n` total-space map yields a `C^n`
  total-space map, and pulling back a core isomorphism with `C^n` forward and inverse total-space
  maps yields a `C^n` diffeomorphism of pulled-back total spaces;
* `IsLocalDiffeomorph.isContMDiff_core_iff_pullback`,
  `IsLocalDiffeomorph.contMDiff_totalSpaceMap_pullbackMap_iff`, and
  `IsLocalDiffeomorph.contMDiff_section_pullback_core_iff`: along a surjective `C^m` local
  diffeomorphism (`n ≤ m`), `C^n` regularity of cores, bundle morphisms, and sections over `Y` is
  equivalent to `C^n` regularity of their pullbacks over `X`;
* `pullbackIdDiffeomorph`, `compDiffeomorph_pullbackDiffeomorph`,
  `lift_compDiffeomorph_pullbackDiffeomorph`, `whitneySumTotalSpaceDiffeomorph_pullbackLift`, and
  `dualTotalSpaceDiffeomorph_pullbackLift`: identity, composition, Whitney-sum, and dual-bundle
  carrier comparisons commute with pullback.

## References

* D. Husemoller, *Fibre Bundles*, 3rd ed., Graduate Texts in Mathematics 20, Springer, 1994,
  Chapter 2 (induced bundles).
* J. W. Milnor and J. D. Stasheff, *Characteristic Classes*, Princeton University Press, 1974, §3.
* D. Huybrechts, *Complex Geometry: An Introduction*, Springer, 2005, §2.2.
-/

public section

open Bundle CategoryTheory VectorBundleCore Set
open scoped Manifold ContDiff Topology

namespace TauCeti.FiniteRankBundleCore

universe u v w z

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜] {m n : ℕ∞ω}
  {EX : Type*} [NormedAddCommGroup EX] [NormedSpace 𝕜 EX]
  {HX : Type*} [TopologicalSpace HX] {IX : ModelWithCorners 𝕜 EX HX}
  {X : Type u} [TopologicalSpace X] [ChartedSpace HX X]
  {EY : Type*} [NormedAddCommGroup EY] [NormedSpace 𝕜 EY]
  {HY : Type*} [TopologicalSpace HY] {IY : ModelWithCorners 𝕜 EY HY}
  {Y : Type w} [TopologicalSpace Y] [ChartedSpace HY Y]
  {EZ : Type*} [NormedAddCommGroup EZ] [NormedSpace 𝕜 EZ]
  {HZ : Type*} [TopologicalSpace HZ] {IZ : ModelWithCorners 𝕜 EZ HZ}
  {Z : Type z} [TopologicalSpace Z] [ChartedSpace HZ Z]

section CoreRegularity

/-- Pulling back a `C^n` finite-rank bundle core along a `C^n` continuous map produces a `C^n`
finite-rank bundle core. Over complex models at `n = ∞`, this equips `A.pullback f` with its
holomorphic vector-bundle structure without requiring `IsManifold` or completeness of `𝕜`. -/
theorem isContMDiff_pullback (A : FiniteRankBundleCore 𝕜 Y) [A.core.IsContMDiff IY n]
    {f : C(X, Y)} (hf : ContMDiff IX IY n f) :
    (A.pullback f).core.IsContMDiff IX n where
  contMDiffOn_coordChange i j :=
    (A.core.contMDiffOn_coordChange IY (f i) (f j)).comp hf.contMDiffOn fun _ hx ↦ hx

/-- Automatic `C^n` (and in particular holomorphic) core regularity for pullback along a bundled
`C^n` map `f : C^n⟮IX, X; IY, Y⟯`. -/
instance instIsContMDiffPullback (A : FiniteRankBundleCore 𝕜 Y) [A.core.IsContMDiff IY n]
    (f : C^n⟮IX, X; IY, Y⟯) :
    (A.pullback (f : C(X, Y))).core.IsContMDiff IX n :=
  A.isContMDiff_pullback (IX := IX) (IY := IY) f.contMDiff

/-- Pulling back a bundle map along a `C^n` map preserves `C^n` regularity of chart operators on
matching chart intersections, without smoothness assumptions on the cores or completeness of `𝕜`. -/
theorem contMDiffOn_inChartCoordinates_pullbackMap {A D : FiniteRankBundleCore 𝕜 Y}
    (a : A ⟶ D) {f : C(X, Y)} (hf : ContMDiff IX IY n f) {i j : X}
    (ha : ContMDiffOn IY 𝓘(𝕜, (Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜)) n
      (fun y ↦ A.core.inChartCoordinates D.core (f i) (f j) y (a.fiberMap y))
      (A.core.baseSet (f i) ∩ D.core.baseSet (f j))) :
    ContMDiffOn IX 𝓘(𝕜, (Fin (A.pullback f).rank → 𝕜) →L[𝕜] (Fin (D.pullback f).rank → 𝕜)) n
      (fun x ↦ (A.pullback f).core.inChartCoordinates (D.pullback f).core i j x
        ((pullbackMap a f).fiberMap x))
      ((A.pullback f).core.baseSet i ∩ (D.pullback f).core.baseSet j) := by
  simp only [fiberMap_pullbackMap, inChartCoordinates_pullback]
  exact ha.comp hf.contMDiffOn fun _ hx ↦ hx

end CoreRegularity

section MathlibPullback

private theorem pullback_trivializationAt_eq (A : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y))
    (x : X) :
    trivializationAt (Fin A.rank → 𝕜) ((⇑f) *ᵖ A.core.Fiber) x =
      (A.core.localTriv (f x)).pullback f := by
  simp only [trivializationAt, FiberBundle.pullback_trivializationAt']
  exact congrArg (fun e ↦ e.pullback f) (A.trivializationAt_core (f x))

/-- `pullbackHomeomorph` is `C^n` on total spaces at every regularity `n`, without any smoothness
hypothesis on `f` or `A` and without completeness of `𝕜`. -/
theorem contMDiff_pullbackHomeomorph (A : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y)) :
    ContMDiff (IX.prod 𝓘(𝕜, Fin (A.pullback f).rank → 𝕜))
      (IX.prod 𝓘(𝕜, Fin A.rank → 𝕜)) n (A.pullbackHomeomorph f) :=
  (A.pullback f).contMDiff_of_localTriv_snd (A.pullbackHomeomorph f)
    (fun p ↦ by simp only [pullbackHomeomorph_apply])
    (ContinuousLinearMap.id 𝕜 (Fin (A.pullback f).rank → 𝕜)) fun x p ↦ by
      rw [pullback_trivializationAt_eq, ContinuousLinearMap.id_apply]
      exact congrArg Prod.snd (A.pullbackHomeomorph_localTriv f x p)

/-- The inverse of `pullbackHomeomorph` is `C^n` on total spaces at every regularity `n`, without
any smoothness hypothesis on `f` or `A` and without completeness of `𝕜`. -/
theorem contMDiff_pullbackHomeomorph_symm (A : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y)) :
    ContMDiff (IX.prod 𝓘(𝕜, Fin A.rank → 𝕜))
      (IX.prod 𝓘(𝕜, Fin (A.pullback f).rank → 𝕜)) n (A.pullbackHomeomorph f).symm := by
  intro p₀
  rw [Bundle.contMDiffAt_totalSpace_iff]
  refine ⟨?_, ?_⟩
  · simpa only [pullbackHomeomorph_symm_apply] using (contMDiff_proj _).contMDiffAt
  · have hproj : ((A.pullbackHomeomorph f).symm p₀).proj = p₀.proj := by
      simp only [pullbackHomeomorph_symm_apply]
    refine (p₀.contMDiffAt_trivializationAt_snd (IB := IX) (n := n)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun q ↦ ?_)
    rw [(A.pullback f).trivializationAt_core, hproj, pullback_trivializationAt_eq]
    simpa only [Homeomorph.apply_symm_apply] using
      congrArg Prod.snd
        (A.pullbackHomeomorph_localTriv f p₀.proj ((A.pullbackHomeomorph f).symm q)).symm

/-- The reconstructed total space of `A.pullback f` is `C^n`-diffeomorphic (and, over `𝓘(ℂ, EX)`
with `n = ∞`, biholomorphic) to the total space of Mathlib's native pullback bundle
`(⇑f) *ᵖ A.core.Fiber`, over the identity of `X` and by the identity in preferred fibre
coordinates. Neither smoothness of `f` nor smoothness of `A` is needed. -/
def pullbackDiffeomorph (IX : ModelWithCorners 𝕜 EX HX) (n : ℕ∞ω)
    (A : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y)) :
    (A.pullback f).core.TotalSpace
      ≃ₘ^n⟮IX.prod 𝓘(𝕜, Fin (A.pullback f).rank → 𝕜), IX.prod 𝓘(𝕜, Fin A.rank → 𝕜)⟯
      TotalSpace (Fin A.rank → 𝕜) ((⇑f) *ᵖ A.core.Fiber) where
  toEquiv := (A.pullbackHomeomorph f).toEquiv
  contMDiff_toFun := A.contMDiff_pullbackHomeomorph f
  contMDiff_invFun := A.contMDiff_pullbackHomeomorph_symm f

@[simp]
theorem pullbackDiffeomorph_apply (IX : ModelWithCorners 𝕜 EX HX) (n : ℕ∞ω)
    (A : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y)) (p : (A.pullback f).core.TotalSpace) :
    A.pullbackDiffeomorph IX n f p = ⟨p.proj, p.2⟩ :=
  A.pullbackHomeomorph_apply f p

@[simp]
theorem pullbackDiffeomorph_proj (IX : ModelWithCorners 𝕜 EX HX) (n : ℕ∞ω)
    (A : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y)) (p : (A.pullback f).core.TotalSpace) :
    (A.pullbackDiffeomorph IX n f p).proj = p.proj := by
  rw [pullbackDiffeomorph_apply]

@[simp]
theorem pullbackDiffeomorph_symm_apply (IX : ModelWithCorners 𝕜 EX HX) (n : ℕ∞ω)
    (A : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y))
    (p : TotalSpace (Fin A.rank → 𝕜) ((⇑f) *ᵖ A.core.Fiber)) :
    (A.pullbackDiffeomorph IX n f).symm p = ⟨p.proj, p.2⟩ :=
  A.pullbackHomeomorph_symm_apply f p

/-- `pullbackDiffeomorph` refines `pullbackHomeomorph`. -/
@[simp]
theorem toHomeomorph_pullbackDiffeomorph (IX : ModelWithCorners 𝕜 EX HX) (n : ℕ∞ω)
    (A : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y)) :
    (A.pullbackDiffeomorph IX n f).toHomeomorph = A.pullbackHomeomorph f :=
  Homeomorph.ext fun _ ↦ rfl

/-- Under `pullbackDiffeomorph`, Mathlib's `Pullback.lift f` agrees with `pullbackLift`. -/
@[simp]
theorem lift_pullbackDiffeomorph (IX : ModelWithCorners 𝕜 EX HX) (n : ℕ∞ω)
    (A : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y)) (p : (A.pullback f).core.TotalSpace) :
    Pullback.lift f (A.pullbackDiffeomorph IX n f p) = A.pullbackLift f p :=
  A.lift_pullbackHomeomorph f p

/-- `pullbackDiffeomorph` carries the core chart at `i` to Mathlib's pullback of the chart at
`f i`. -/
theorem pullbackDiffeomorph_localTriv (IX : ModelWithCorners 𝕜 EX HX) (n : ℕ∞ω)
    (A : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y)) (i : X) (p : (A.pullback f).core.TotalSpace) :
    (A.core.localTriv (f i)).pullback f (A.pullbackDiffeomorph IX n f p) =
      (A.pullback f).core.localTriv i p :=
  A.pullbackHomeomorph_localTriv f i p

/-- `pullbackDiffeomorph` intertwines pulled-back bundle morphisms with Mathlib's canonical lift
to the original total space. -/
theorem pullbackDiffeomorph_naturality (IX : ModelWithCorners 𝕜 EX HX) (n : ℕ∞ω)
    {A D : FiniteRankBundleCore 𝕜 Y} (a : A ⟶ D) (f : C(X, Y))
    (p : (A.pullback f).core.TotalSpace) :
    Pullback.lift f (D.pullbackDiffeomorph IX n f ((pullbackMap a f).totalSpaceMap p)) =
      a.totalSpaceMap (Pullback.lift f (A.pullbackDiffeomorph IX n f p)) :=
  pullbackHomeomorph_naturality a f p

end MathlibPullback

section UniversalProperty

variable {EW HW W : Type*} [NormedAddCommGroup EW] [NormedSpace 𝕜 EW]
  [TopologicalSpace HW] {IW : ModelWithCorners 𝕜 EW HW}
  [TopologicalSpace W] [ChartedSpace HW W]

/-- **Universal property of the pulled-back core total space (pointwise).** A map `q` into
`(A.pullback f).core.TotalSpace` is `C^n` at `w` when `f` is `C^n` at `(q w).proj` if and only if
its base projection and its lift `w' ↦ A.pullbackLift f (q w')` into `A.core.TotalSpace` are `C^n`
at `w`. -/
theorem contMDiffAt_pullback_totalSpace_iff (A : FiniteRankBundleCore 𝕜 Y) {f : C(X, Y)}
    {q : W → (A.pullback f).core.TotalSpace} {w : W} (hf : ContMDiffAt IX IY n f (q w).proj) :
    ContMDiffAt IW (IX.prod 𝓘(𝕜, Fin (A.pullback f).rank → 𝕜)) n q w ↔
      ContMDiffAt IW IX n (fun w' ↦ (q w').proj) w ∧
        ContMDiffAt IW (IY.prod 𝓘(𝕜, Fin A.rank → 𝕜)) n (fun w' ↦ A.pullbackLift f (q w')) w := by
  have hf' : ContMDiffAt IX IY n f ((A.pullbackDiffeomorph IX n f ∘ q) w).proj := by
    simpa only [Function.comp_apply, pullbackDiffeomorph_proj] using hf
  have hproj : (fun w' ↦ ((A.pullbackDiffeomorph IX n f ∘ q) w').proj) = fun w' ↦ (q w').proj :=
    funext fun w' ↦ A.pullbackDiffeomorph_proj IX n f (q w')
  have hlift : (fun w' ↦ Pullback.lift f ((A.pullbackDiffeomorph IX n f ∘ q) w')) =
      fun w' ↦ A.pullbackLift f (q w') :=
    funext fun w' ↦ A.lift_pullbackDiffeomorph IX n f (q w')
  rw [← (A.pullbackDiffeomorph IX n f).contMDiffAt_diffeomorph_comp_iff le_rfl]
  refine (Bundle.Pullback.contMDiffAt_iff (E := A.core.Fiber) f hf').trans ?_
  rw [hproj, hlift]

/-- **Universal property of the pulled-back core total space (global).** When `f` is `C^n`, a map
`q` into `(A.pullback f).core.TotalSpace` is `C^n` if and only if its base projection and its lift
`w ↦ A.pullbackLift f (q w)` into `A.core.TotalSpace` are `C^n`. -/
theorem contMDiff_pullback_totalSpace_iff (A : FiniteRankBundleCore 𝕜 Y) {f : C(X, Y)}
    (hf : ContMDiff IX IY n f) {q : W → (A.pullback f).core.TotalSpace} :
    ContMDiff IW (IX.prod 𝓘(𝕜, Fin (A.pullback f).rank → 𝕜)) n q ↔
      ContMDiff IW IX n (fun w ↦ (q w).proj) ∧
        ContMDiff IW (IY.prod 𝓘(𝕜, Fin A.rank → 𝕜)) n (fun w ↦ A.pullbackLift f (q w)) := by
  simp only [ContMDiff, ← forall_and]
  exact forall_congr' fun w ↦ A.contMDiffAt_pullback_totalSpace_iff (hf (q w).proj)

/-- The canonical lift `A.pullbackLift f` is `C^n` at every total-space point over which `f` is
`C^n`. -/
theorem contMDiffAt_pullbackLift (A : FiniteRankBundleCore 𝕜 Y) {f : C(X, Y)}
    {p : (A.pullback f).core.TotalSpace} (hf : ContMDiffAt IX IY n f p.proj) :
    ContMDiffAt (IX.prod 𝓘(𝕜, Fin (A.pullback f).rank → 𝕜))
      (IY.prod 𝓘(𝕜, Fin A.rank → 𝕜)) n (A.pullbackLift f) p :=
  ((A.contMDiffAt_pullback_totalSpace_iff (q := id) hf).1 contMDiffAt_id).2

/-- The canonical lift `A.pullbackLift f` from `(A.pullback f).core.TotalSpace` to
`A.core.TotalSpace` is `C^n` whenever `f` is `C^n`. -/
theorem contMDiff_pullbackLift (A : FiniteRankBundleCore 𝕜 Y) {f : C(X, Y)}
    (hf : ContMDiff IX IY n f) :
    ContMDiff (IX.prod 𝓘(𝕜, Fin (A.pullback f).rank → 𝕜))
      (IY.prod 𝓘(𝕜, Fin A.rank → 𝕜)) n (A.pullbackLift f) :=
  fun p ↦ A.contMDiffAt_pullbackLift (hf p.proj)

/-- Pulling back a bundle map whose total-space map is `C^n` along a `C^n` base map produces a
bundle map whose total-space map is `C^n`. Neither smoothness of the cores nor completeness of `𝕜`
is required. -/
theorem contMDiff_totalSpaceMap_pullbackMap {A D : FiniteRankBundleCore 𝕜 Y} (a : A ⟶ D)
    {f : C(X, Y)}
    (ha : ContMDiff (IY.prod 𝓘(𝕜, Fin A.rank → 𝕜)) (IY.prod 𝓘(𝕜, Fin D.rank → 𝕜)) n
      a.totalSpaceMap)
    (hf : ContMDiff IX IY n f) :
    ContMDiff (IX.prod 𝓘(𝕜, Fin (A.pullback f).rank → 𝕜))
      (IX.prod 𝓘(𝕜, Fin (D.pullback f).rank → 𝕜)) n (pullbackMap a f).totalSpaceMap := by
  refine (D.contMDiff_pullback_totalSpace_iff hf).2 ⟨?_, ?_⟩
  · simpa only [CoordinateHom.totalSpaceMap_proj] using contMDiff_proj (A.pullback f).core.Fiber
  · exact (ha.comp (A.contMDiff_pullbackLift hf)).congr
      fun w ↦ pullbackLift_totalSpaceMap_pullbackMap a f w

/-- Pulling back a core isomorphism whose forward and inverse total-space maps are `C^n` along a
`C^n` base map gives a `C^n` diffeomorphism of pulled-back total spaces. -/
def pullbackIsoDiffeomorph {A D : FiniteRankBundleCore 𝕜 Y} (e : A ≅ D) {f : C(X, Y)}
    (hf : ContMDiff IX IY n f)
    (he : ContMDiff (IY.prod 𝓘(𝕜, Fin A.rank → 𝕜)) (IY.prod 𝓘(𝕜, Fin D.rank → 𝕜)) n
      e.hom.totalSpaceMap)
    (he' : ContMDiff (IY.prod 𝓘(𝕜, Fin D.rank → 𝕜)) (IY.prod 𝓘(𝕜, Fin A.rank → 𝕜)) n
      e.inv.totalSpaceMap) :
    (A.pullback f).core.TotalSpace
      ≃ₘ^n⟮IX.prod 𝓘(𝕜, Fin (A.pullback f).rank → 𝕜), IX.prod 𝓘(𝕜, Fin (D.pullback f).rank → 𝕜)⟯
      (D.pullback f).core.TotalSpace :=
  CoordinateHom.toDiffeomorphOfInv
    ((pullbackFunctor f).mapIso e).hom ((pullbackFunctor f).mapIso e).inv
    ((pullbackFunctor f).mapIso e).hom_inv_id ((pullbackFunctor f).mapIso e).inv_hom_id
    (contMDiff_totalSpaceMap_pullbackMap e.hom he hf)
    (contMDiff_totalSpaceMap_pullbackMap e.inv he' hf)

@[simp]
theorem coe_pullbackIsoDiffeomorph {A D : FiniteRankBundleCore 𝕜 Y} (e : A ≅ D) {f : C(X, Y)}
    (hf : ContMDiff IX IY n f)
    (he : ContMDiff (IY.prod 𝓘(𝕜, Fin A.rank → 𝕜)) (IY.prod 𝓘(𝕜, Fin D.rank → 𝕜)) n
      e.hom.totalSpaceMap)
    (he' : ContMDiff (IY.prod 𝓘(𝕜, Fin D.rank → 𝕜)) (IY.prod 𝓘(𝕜, Fin A.rank → 𝕜)) n
      e.inv.totalSpaceMap) :
    ⇑(pullbackIsoDiffeomorph e hf he he') = (pullbackMap e.hom f).totalSpaceMap :=
  CoordinateHom.coe_toDiffeomorphOfInv _ _ _ _ _ _

@[simp]
theorem coe_pullbackIsoDiffeomorph_symm {A D : FiniteRankBundleCore 𝕜 Y} (e : A ≅ D)
    {f : C(X, Y)} (hf : ContMDiff IX IY n f)
    (he : ContMDiff (IY.prod 𝓘(𝕜, Fin A.rank → 𝕜)) (IY.prod 𝓘(𝕜, Fin D.rank → 𝕜)) n
      e.hom.totalSpaceMap)
    (he' : ContMDiff (IY.prod 𝓘(𝕜, Fin D.rank → 𝕜)) (IY.prod 𝓘(𝕜, Fin A.rank → 𝕜)) n
      e.inv.totalSpaceMap) :
    ⇑(pullbackIsoDiffeomorph e hf he he').symm = (pullbackMap e.inv f).totalSpaceMap :=
  CoordinateHom.coe_toDiffeomorphOfInv_symm _ _ _ _ _ _

end UniversalProperty

section LocalDiffeomorph

/-- Along a surjective `C^m` local diffeomorphism `f` (`n ≤ m`), a finite-rank core `A` over `Y`
has `C^n` transition functions if and only if its pullback `A.pullback f` over `X` does. In
particular, along a holomorphic covering projection, holomorphicity of a descended core is detected
after pullback. -/
theorem _root_.IsLocalDiffeomorph.isContMDiff_core_iff_pullback {f : C(X, Y)}
    (hf : IsLocalDiffeomorph IX IY m f) (hsurj : Function.Surjective f) (hn : n ≤ m)
    (A : FiniteRankBundleCore 𝕜 Y) :
    A.core.IsContMDiff IY n ↔ (A.pullback f).core.IsContMDiff IX n := by
  refine ⟨fun h ↦ by have := h; exact A.isContMDiff_pullback (hf.contMDiff.of_le hn),
    fun h ↦ ⟨fun i₀ j₀ y₀ hy₀ ↦ ?_⟩⟩
  obtain ⟨i, rfl⟩ := hsurj i₀
  obtain ⟨j, rfl⟩ := hsurj j₀
  obtain ⟨x₀, rfl⟩ := hsurj y₀
  have hx₀ : x₀ ∈ (A.pullback f).core.baseSet i ∩ (A.pullback f).core.baseSet j := hy₀
  have hU : (A.pullback f).core.baseSet i ∩ (A.pullback f).core.baseSet j ∈ nhds x₀ :=
    (((A.pullback f).core.isOpen_baseSet i).inter
      ((A.pullback f).core.isOpen_baseSet j)).mem_nhds hx₀
  have hcoord : ContMDiffAt IX 𝓘(𝕜, (Fin A.rank → 𝕜) →L[𝕜] (Fin A.rank → 𝕜)) n
      (A.core.coordChange (f i) (f j) ∘ f) x₀ :=
    (h.contMDiffOn_coordChange i j x₀ hx₀).contMDiffAt hU
  exact (((hf x₀).contMDiffAt_comp_iff hn).1 hcoord).contMDiffWithinAt

/-- Along a surjective `C^m` local diffeomorphism `f` (`n ≤ m`), a morphism `a : A ⟶ D` of
finite-rank cores over `Y` has `C^n` total-space map if and only if its pullback
`pullbackMap a f` over `X` does. Neither smoothness of the cores nor completeness of `𝕜` is
needed. -/
theorem _root_.IsLocalDiffeomorph.contMDiff_totalSpaceMap_pullbackMap_iff {f : C(X, Y)}
    (hf : IsLocalDiffeomorph IX IY m f) (hsurj : Function.Surjective f) (hn : n ≤ m)
    {A D : FiniteRankBundleCore 𝕜 Y} (a : A ⟶ D) :
    ContMDiff (IY.prod 𝓘(𝕜, Fin A.rank → 𝕜)) (IY.prod 𝓘(𝕜, Fin D.rank → 𝕜)) n a.totalSpaceMap ↔
      ContMDiff (IX.prod 𝓘(𝕜, Fin (A.pullback f).rank → 𝕜))
        (IX.prod 𝓘(𝕜, Fin (D.pullback f).rank → 𝕜)) n (pullbackMap a f).totalSpaceMap := by
  refine ⟨fun ha ↦ contMDiff_totalSpaceMap_pullbackMap a ha (hf.contMDiff.of_le hn),
    fun ha q₀ ↦ ?_⟩
  obtain ⟨x₀, hx₀⟩ := hsurj q₀.proj
  let g := (hf x₀).localInverse
  let s : A.core.TotalSpace → (A.pullback f).core.TotalSpace := fun q ↦ ⟨g q.proj, q.2⟩
  have hgx₀ : g q₀.proj = x₀ := by
    rw [← hx₀]
    exact (hf x₀).localInverse_left_inv (hf x₀).localInverse_mem_target
  have hfg : ∀ᶠ q : A.core.TotalSpace in nhds q₀, f (g q.proj) = q.proj := by
    have hfg_base : (f ∘ g) =ᶠ[nhds q₀.proj] id :=
      hx₀ ▸ (hf x₀).localInverse_eventuallyEq_right
    exact hfg_base.comp_tendsto (A.core.continuous_proj.tendsto q₀)
  have hs : ContMDiffAt (IY.prod 𝓘(𝕜, Fin A.rank → 𝕜))
      (IX.prod 𝓘(𝕜, Fin (A.pullback f).rank → 𝕜)) n s q₀ := by
    refine (A.contMDiffAt_pullback_totalSpace_iff
      (hf := hgx₀.symm ▸ (hf x₀).contMDiffAt.of_le hn)).2 ⟨?_, ?_⟩
    · exact (hx₀ ▸ (hf x₀).contMDiffAt_localInverse.of_le hn).comp q₀ (contMDiffAt_proj _)
    · refine contMDiffAt_id.congr_of_eventuallyEq ?_
      filter_upwards [hfg] with q hq
      rcases q with ⟨y, v⟩
      exact congrArg (fun y' ↦ (⟨y', v⟩ : A.core.TotalSpace)) hq
  have hcomp : ContMDiffAt (IY.prod 𝓘(𝕜, Fin A.rank → 𝕜))
      (IY.prod 𝓘(𝕜, Fin D.rank → 𝕜)) n
      (fun q ↦ D.pullbackLift f ((pullbackMap a f).totalSpaceMap (s q))) q₀ := by
    have hproj : ((pullbackMap a f).totalSpaceMap (s q₀)).proj = x₀ := by
      rw [CoordinateHom.totalSpaceMap_proj]
      exact hgx₀
    exact (D.contMDiffAt_pullbackLift (hproj.symm ▸ (hf x₀).contMDiffAt.of_le hn)).comp q₀
      ((ha (s q₀)).comp q₀ hs)
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [hfg] with q hq
  rw [pullbackLift_totalSpaceMap_pullbackMap]
  rcases q with ⟨y, v⟩
  exact congrArg a.totalSpaceMap (congrArg (fun y' ↦ (⟨y', v⟩ : A.core.TotalSpace)) hq).symm

/-- If `f` is a `C^m` local diffeomorphism at `x` (`n ≤ m`), a section `σ` of `A` is `C^n` at
`f x` if and only if its pulled-back section `x' ↦ σ (f x')` of `A.pullback f` is `C^n` at `x`. -/
theorem _root_.IsLocalDiffeomorphAt.contMDiffAt_section_pullback_core_iff {f : C(X, Y)} {x : X}
    (hf : IsLocalDiffeomorphAt IX IY m f x) (hn : n ≤ m) (A : FiniteRankBundleCore 𝕜 Y)
    {σ : ∀ y, A.core.Fiber y} :
    ContMDiffAt IY (IY.prod 𝓘(𝕜, Fin A.rank → 𝕜)) n
        (fun y ↦ TotalSpace.mk' (Fin A.rank → 𝕜) y (σ y)) (f x) ↔
      ContMDiffAt IX (IX.prod 𝓘(𝕜, Fin (A.pullback f).rank → 𝕜)) n
        (fun x' ↦ TotalSpace.mk' (Fin (A.pullback f).rank → 𝕜)
          (E := (A.pullback f).core.Fiber) x' (σ (f x'))) x := by
  rw [A.contMDiffAt_pullback_totalSpace_iff (hf.contMDiffAt.of_le hn),
    ← hf.contMDiffAt_comp_iff hn]
  -- `pullbackLift` is exposed, so `x' ↦ A.pullbackLift f ⟨x', σ (f x')⟩` reduces definitionally
  -- to `(fun y ↦ ⟨y, σ y⟩) ∘ f`.
  exact (and_iff_right contMDiffAt_id).symm

/-- Along a surjective `C^m` local diffeomorphism `f` (`n ≤ m`), a section `σ` of `A` is `C^n` if
and only if its pulled-back section `x ↦ σ (f x)` of `A.pullback f` is `C^n`. -/
theorem _root_.IsLocalDiffeomorph.contMDiff_section_pullback_core_iff {f : C(X, Y)}
    (hf : IsLocalDiffeomorph IX IY m f) (hsurj : Function.Surjective f) (hn : n ≤ m)
    (A : FiniteRankBundleCore 𝕜 Y) {σ : ∀ y, A.core.Fiber y} :
    ContMDiff IY (IY.prod 𝓘(𝕜, Fin A.rank → 𝕜)) n
        (fun y ↦ TotalSpace.mk' (Fin A.rank → 𝕜) y (σ y)) ↔
      ContMDiff IX (IX.prod 𝓘(𝕜, Fin (A.pullback f).rank → 𝕜)) n
        (fun x ↦ TotalSpace.mk' (Fin (A.pullback f).rank → 𝕜)
          (E := (A.pullback f).core.Fiber) x (σ (f x))) := by
  refine ⟨fun h x ↦ ((hf x).contMDiffAt_section_pullback_core_iff hn A).1 (h (f x)), fun h y ↦ ?_⟩
  obtain ⟨x, rfl⟩ := hsurj y
  exact ((hf x).contMDiffAt_section_pullback_core_iff hn A).2 (h x)

end LocalDiffeomorph

section Coherence

/-- Pulling back a finite-rank core along the identity map produces a total space canonically
`C^n`-diffeomorphic (and over `𝓘(ℂ, EY)` at `n = ∞`, biholomorphic) to `A.core.TotalSpace`,
defined as the composite of `pullbackDiffeomorph` with `Bundle.Pullback.idDiffeomorph`. -/
noncomputable def pullbackIdDiffeomorph (IY : ModelWithCorners 𝕜 EY HY) (n : ℕ∞ω)
    (A : FiniteRankBundleCore 𝕜 Y) :
    (A.pullback (ContinuousMap.id Y)).core.TotalSpace
      ≃ₘ^n⟮IY.prod 𝓘(𝕜, Fin (A.pullback (ContinuousMap.id Y)).rank → 𝕜),
        IY.prod 𝓘(𝕜, Fin A.rank → 𝕜)⟯
      A.core.TotalSpace :=
  (A.pullbackDiffeomorph IY n (ContinuousMap.id Y)).trans
    (Bundle.Pullback.idDiffeomorph (I := IY) (m := n) (n := n) A.core.Fiber)

@[simp]
theorem pullbackIdDiffeomorph_apply (IY : ModelWithCorners 𝕜 EY HY) (n : ℕ∞ω)
    (A : FiniteRankBundleCore 𝕜 Y) (p : (A.pullback (ContinuousMap.id Y)).core.TotalSpace) :
    A.pullbackIdDiffeomorph IY n p = ⟨p.proj, p.2⟩ := by
  -- Unfold `Diffeomorph.trans` to function composition on the two underlying diffeomorphisms.
  change Bundle.Pullback.idDiffeomorph (I := IY) (m := n) (n := n) A.core.Fiber
      (A.pullbackDiffeomorph IY n (ContinuousMap.id Y) p) = ⟨p.proj, p.2⟩
  rw [pullbackDiffeomorph_apply]
  exact Bundle.Pullback.idDiffeomorph_apply _

@[simp]
theorem pullbackIdDiffeomorph_symm_apply (IY : ModelWithCorners 𝕜 EY HY) (n : ℕ∞ω)
    (A : FiniteRankBundleCore 𝕜 Y) (p : A.core.TotalSpace) :
    (A.pullbackIdDiffeomorph IY n).symm p = ⟨p.proj, p.2⟩ := by
  -- Unfold the inverse of `Diffeomorph.trans` to the reverse composition of inverses.
  change (A.pullbackDiffeomorph IY n (ContinuousMap.id Y)).symm
      ((Bundle.Pullback.idDiffeomorph (I := IY) (m := n) (n := n) A.core.Fiber).symm p) =
    ⟨p.proj, p.2⟩
  rw [Bundle.Pullback.idDiffeomorph_symm_apply]
  exact A.pullbackDiffeomorph_symm_apply IY n (ContinuousMap.id Y) _

/-- Under the strict equality `(A.pullback g).pullback f = A.pullback (g.comp f)`, Mathlib's
installed composition comparison `Bundle.Pullback.compDiffeomorph` acts as the identity on
coordinates after `pullbackDiffeomorph`. -/
@[simp]
theorem compDiffeomorph_pullbackDiffeomorph (A : FiniteRankBundleCore 𝕜 Z)
    (g : C^m⟮IY, Y; IZ, Z⟯) (f : C^m⟮IX, X; IY, Y⟯)
    (p : (A.pullback ((g : C(Y, Z)).comp (f : C(X, Y)))).core.TotalSpace) :
    Bundle.Pullback.compDiffeomorph (n := n) A.core.Fiber g f
        (A.pullbackDiffeomorph IX n ((g : C(Y, Z)).comp (f : C(X, Y))) p) =
      ⟨p.proj, p.2⟩ := by
  have h₁ : A.pullbackDiffeomorph IX n ((g : C(Y, Z)).comp (f : C(X, Y))) p =
      (⟨p.proj, p.2⟩ : TotalSpace (Fin A.rank → 𝕜) ((g.comp f : X → Z) *ᵖ A.core.Fiber)) :=
    A.pullbackDiffeomorph_apply IX n _ p
  exact (congrArg _ h₁).trans (Bundle.Pullback.compDiffeomorph_apply (E := A.core.Fiber) g f _)

/-- Under `compDiffeomorph`, lifting the composite pullback one step along `f` agrees with
applying the core lift `pullbackLift f` followed by `pullbackDiffeomorph g`. -/
theorem lift_compDiffeomorph_pullbackDiffeomorph (A : FiniteRankBundleCore 𝕜 Z)
    (g : C^m⟮IY, Y; IZ, Z⟯) (f : C^m⟮IX, X; IY, Y⟯)
    (p : (A.pullback ((g : C(Y, Z)).comp (f : C(X, Y)))).core.TotalSpace) :
    Pullback.lift (f : X → Y)
        (Bundle.Pullback.compDiffeomorph (n := n) A.core.Fiber g f
          (A.pullbackDiffeomorph IX n ((g : C(Y, Z)).comp (f : C(X, Y))) p)) =
      A.pullbackDiffeomorph IY n (g : C(Y, Z))
        ((A.pullback (g : C(Y, Z))).pullbackLift (f : C(X, Y)) p) := by
  have hL : Pullback.lift (f : X → Y)
      (Bundle.Pullback.compDiffeomorph (n := n) A.core.Fiber g f
        (A.pullbackDiffeomorph IX n ((g : C(Y, Z)).comp (f : C(X, Y))) p)) =
      (⟨f p.proj, p.2⟩ : TotalSpace (Fin A.rank → 𝕜) ((g : Y → Z) *ᵖ A.core.Fiber)) :=
    (congrArg (Pullback.lift (f : X → Y)) (compDiffeomorph_pullbackDiffeomorph A g f p)).trans
      (Pullback.lift_mk (E := (g : Y → Z) *ᵖ A.core.Fiber) (F := Fin A.rank → 𝕜)
        (f : X → Y) p.proj p.2)
  exact hL.trans
    (A.pullbackDiffeomorph_apply IY n (g : C(Y, Z))
      ((A.pullback (g : C(Y, Z))).pullbackLift (f : C(X, Y)) p)).symm

/-- Under the strict equality
`(whitneySum A D).pullback f = whitneySum (A.pullback f) (D.pullback f)`, the `C^n` comparison
`whitneySumTotalSpaceDiffeomorph` with Mathlib's direct-sum bundle commutes with `pullbackLift`. -/
theorem whitneySumTotalSpaceDiffeomorph_pullbackLift
    (A D : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y))
    (p : ((whitneySum A D).pullback f).core.TotalSpace) :
    whitneySumTotalSpaceDiffeomorph IY n A D ((whitneySum A D).pullbackLift f p) =
      ⟨f p.proj, (whitneySumTotalSpaceDiffeomorph IX n (A.pullback f) (D.pullback f) p).2⟩ := by
  let projPair
      (q : TotalSpace ((Fin (A.pullback f).rank → 𝕜) × (Fin (D.pullback f).rank → 𝕜))
        ((A.pullback f).core.Fiber ×ᵇ (D.pullback f).core.Fiber)) :
      (Fin A.rank → 𝕜) × (Fin D.rank → 𝕜) := q.2
  have hX := congrArg projPair
    (whitneySumTotalSpaceDiffeomorph_apply IX n (A.pullback f) (D.pullback f) p)
  exact (whitneySumTotalSpaceDiffeomorph_apply IY n A D ((whitneySum A D).pullbackLift f p)).trans
    (congrArg (TotalSpace.mk' ((Fin A.rank → 𝕜) × (Fin D.rank → 𝕜))
      (E := A.core.Fiber ×ᵇ D.core.Fiber) (f p.proj))
      ((whitneySumFiberEquiv_apply A D (f p.proj) p.2).trans
        ((whitneySumFiberEquiv_apply (A.pullback f) (D.pullback f) p.proj p.2).symm.trans
          hX.symm)))

/-- Under the strict equality `A.dual.pullback f = (A.pullback f).dual`, the `C^n` comparison
`dualTotalSpaceDiffeomorph` with Mathlib's dual bundle commutes with `pullbackLift` on every
fibre vector. -/
theorem dualTotalSpaceDiffeomorph_pullbackLift [CompleteSpace 𝕜]
    (A : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y))
    (p : (A.dual.pullback f).core.TotalSpace) (v : Fin A.rank → 𝕜) :
    (A.dualTotalSpaceDiffeomorph IY n (A.dual.pullbackLift f p)).2 v =
      ((A.pullback f).dualTotalSpaceDiffeomorph IX n p).2 v :=
  calc (A.dualTotalSpaceDiffeomorph IY n (A.dual.pullbackLift f p)).2 v
      = dualFiberEquiv A (f p.proj) p.2 v :=
        congrArg (fun q ↦ q.2 v) (A.dualTotalSpaceDiffeomorph_apply (A.dual.pullbackLift f p))
    _ = dualFiberEquiv (A.pullback f) p.proj p.2 v :=
        (dualFiberEquiv_pullback_apply A f p.proj p.2 v).symm
    _ = ((A.pullback f).dualTotalSpaceDiffeomorph IX n p).2 v :=
        congrArg (fun q ↦ q.2 v) ((A.pullback f).dualTotalSpaceDiffeomorph_apply p).symm

end Coherence

end TauCeti.FiniteRankBundleCore
