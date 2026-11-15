/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Pullback
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteRank.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Pullback

import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic

/-!
# Smooth and holomorphic pullback of finite-rank bundle cores

Pulling back a point-indexed finite-rank vector-bundle core `A : FiniteRankBundleCore 𝕜 Y` along a
continuous map `f : C(X, Y)` produces the core `A.pullback f` over `X` with the same coordinate
space `Fin A.rank → 𝕜` and transition functions `x ↦ A.core.coordChange (f i) (f j) (f x)`. Over a
charted base `X`, this file establishes the `C^n` (and, for `𝕜 = ℂ` at `n = ∞`, holomorphic)
structure, comparisons, universal property, functoriality, and local-diffeomorphism descent criteria
for `A.pullback f`:

* `TauCeti.FiniteRankBundleCore.pullbackDiffeomorph`: `A.pullbackHomeomorph f` is a `C^n`
  diffeomorphism between `(A.pullback f).core.TotalSpace` and Mathlib's pullback total space
  `TotalSpace (Fin A.rank → 𝕜) ((⇑f) *ᵖ A.core.Fiber)`, without any smoothness hypothesis on `X`,
  `Y`, `f`, or `A`;
* `TauCeti.FiniteRankBundleCore.pullbackIdDiffeomorph`,
  `TauCeti.FiniteRankBundleCore.idDiffeomorph_pullbackDiffeomorph`, and
  `TauCeti.FiniteRankBundleCore.lift_compDiffeomorph_pullbackDiffeomorph`: `C^n` comparison for
  pullback along the identity and compatibility of `pullbackDiffeomorph` with
  `Bundle.Pullback.idDiffeomorph` and `Bundle.Pullback.compDiffeomorph`;
* `TauCeti.FiniteRankBundleCore.isContMDiff_pullback` and
  `TauCeti.FiniteRankBundleCore.instIsContMDiffPullbackContMDiffMap`: pulling back a `C^n` core
  along a `C^n` map yields a `C^n` core;
* `TauCeti.FiniteRankBundleCore.contMDiffAt_iff_pullbackLift`,
  `TauCeti.FiniteRankBundleCore.contMDiff_iff_pullbackLift`,
  `TauCeti.FiniteRankBundleCore.contMDiffAt_pullbackLift`, and
  `TauCeti.FiniteRankBundleCore.contMDiff_pullbackLift`: the smooth universal property of
  `(A.pullback f).core.TotalSpace` and smoothness of the canonical total-space lift
  `A.pullbackLift f`;
* `TauCeti.FiniteRankBundleCore.contMDiffOn_inChartCoordinates_pullbackMap`,
  `TauCeti.FiniteRankBundleCore.contMDiffAt_totalSpaceMap_pullbackMap`,
  `TauCeti.FiniteRankBundleCore.contMDiff_totalSpaceMap_pullbackMap`, and
  `TauCeti.FiniteRankBundleCore.pullbackIsoDiffeomorph`: pulling back morphisms and isomorphisms
  along a `C^n` map preserves `C^n` chart operators, `C^n` total-space maps, and `C^n` bundle
  equivalences without completeness assumptions on `𝕜`;
* `TauCeti.FiniteRankBundleCore.isLocalDiffeomorphAt_pullbackLift`,
  `TauCeti.FiniteRankBundleCore.isLocalDiffeomorph_pullbackLift`,
  `TauCeti.FiniteRankBundleCore.isContMDiff_pullback_iff_of_isLocalDiffeomorph`, and
  `TauCeti.FiniteRankBundleCore.contMDiff_totalSpaceMap_pullbackMap_iff_of_isLocalDiffeomorph`:
  along a `C^n` local diffeomorphism `f`, `A.pullbackLift f` is a `C^n` local diffeomorphism of
  total spaces, and when `f` is also surjective, `C^m` regularity (`m ≤ n`) of cores, sections, and
  bundle morphisms over `Y` is equivalent to `C^m` regularity of their pullbacks over `X`.

## References

* D. Husemoller, *Fibre Bundles*, 3rd ed., Graduate Texts in Mathematics 20, Springer, 1994,
  Chapter 2 (induced bundles).
* D. Huybrechts, *Complex Geometry: An Introduction*, Springer, 2005, §2.2.
-/

public section

open Bundle CategoryTheory Set VectorBundleCore
open scoped Manifold ContDiff Topology

namespace TauCeti.FiniteRankBundleCore

section Comparison

variable {𝕜 X Y : Type*} [NontriviallyNormedField 𝕜]
  [TopologicalSpace X] [TopologicalSpace Y]
  {EX HX : Type*} [NormedAddCommGroup EX] [NormedSpace 𝕜 EX]
  [TopologicalSpace HX] [ChartedSpace HX X]
  {IX : ModelWithCorners 𝕜 EX HX} {m n : ℕ∞ω}

/-- The homeomorphism `A.pullbackHomeomorph f` between the total space of the reconstructed
pullback core and Mathlib's native pullback bundle is a `C^n` diffeomorphism at every regularity
`n`, without any smoothness hypothesis on `X`, `Y`, `f`, or `A`: at every base point `b : X`, both
preferred trivializations read the same fibre coordinate `A.core.coordChange (f p.proj) (f b)
(f p.proj) p.2`. -/
noncomputable def pullbackDiffeomorph (A : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y)) :
    (A.pullback f).core.TotalSpace ≃ₘ^n⟮IX.prod 𝓘(𝕜, Fin (A.pullback f).rank → 𝕜),
      IX.prod 𝓘(𝕜, Fin A.rank → 𝕜)⟯
      TotalSpace (Fin A.rank → 𝕜) ((⇑f) *ᵖ A.core.Fiber) where
  toEquiv := (A.pullbackHomeomorph f).toEquiv
  contMDiff_toFun :=
    (A.pullback f).contMDiff_of_localTriv_snd (A.pullbackHomeomorph f)
      (fun p ↦ congrArg TotalSpace.proj (A.pullbackHomeomorph_apply f p))
      (ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜)) fun b p ↦ by
        have htriv : (FiberBundle.trivializationAt (Fin A.rank → 𝕜) ((⇑f) *ᵖ A.core.Fiber) b
            (A.pullbackHomeomorph f p)).2 = ((A.pullback f).core.localTriv b p).2 := by
          rw [FiberBundle.trivializationAt, FiberBundle.pullback_trivializationAt',
            A.trivializationAt_core (f b), A.pullbackHomeomorph_localTriv f b p]
        exact htriv.trans (ContinuousLinearMap.id_apply _).symm
  contMDiff_invFun p₀ := by
    rw [Bundle.contMDiffAt_totalSpace_iff]
    refine ⟨((contMDiff_proj ((⇑f) *ᵖ A.core.Fiber)).congr fun p ↦
        congrArg TotalSpace.proj (A.pullbackHomeomorph_symm_apply f p)).contMDiffAt, ?_⟩
    refine (p₀.contMDiffAt_trivializationAt_snd (IB := IX) (n := n)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun p ↦ ?_)
    have hb₀ : ((A.pullbackHomeomorph f).toEquiv.symm p₀).proj = p₀.proj :=
      congrArg TotalSpace.proj (A.pullbackHomeomorph_symm_apply f p₀)
    change (FiberBundle.trivializationAt (Fin (A.pullback f).rank → 𝕜) (A.pullback f).core.Fiber
        ((A.pullbackHomeomorph f).toEquiv.symm p₀).proj ((A.pullbackHomeomorph f).symm p)).2 =
      (FiberBundle.trivializationAt (Fin A.rank → 𝕜) ((⇑f) *ᵖ A.core.Fiber) p₀.proj p).2
    rw [hb₀, (A.pullback f).trivializationAt_core, FiberBundle.trivializationAt,
      FiberBundle.pullback_trivializationAt', A.trivializationAt_core (f p₀.proj)]
    simpa only [Homeomorph.apply_symm_apply] using
      (congrArg Prod.snd
        (A.pullbackHomeomorph_localTriv f p₀.proj ((A.pullbackHomeomorph f).symm p))).symm

@[simp]
theorem coe_pullbackDiffeomorph (A : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y)) :
    ⇑(A.pullbackDiffeomorph (IX := IX) (n := n) f) = A.pullbackHomeomorph f := (rfl)

@[simp]
theorem pullbackDiffeomorph_toHomeomorph (A : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y)) :
    (A.pullbackDiffeomorph (IX := IX) (n := n) f).toHomeomorph = A.pullbackHomeomorph f :=
  Homeomorph.ext fun _ ↦ rfl

@[simp]
theorem pullbackDiffeomorph_apply (A : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y))
    (p : (A.pullback f).core.TotalSpace) :
    A.pullbackDiffeomorph (IX := IX) (n := n) f p = ⟨p.proj, p.2⟩ :=
  A.pullbackHomeomorph_apply f p

@[simp]
theorem pullbackDiffeomorph_symm_apply (A : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y))
    (p : TotalSpace (Fin A.rank → 𝕜) ((⇑f) *ᵖ A.core.Fiber)) :
    (A.pullbackDiffeomorph (IX := IX) (n := n) f).symm p = ⟨p.proj, p.2⟩ :=
  A.pullbackHomeomorph_symm_apply f p

/-- Under `pullbackDiffeomorph`, Mathlib's `Pullback.lift f` agrees with `A.pullbackLift f`. -/
theorem lift_pullbackDiffeomorph (A : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y))
    (p : (A.pullback f).core.TotalSpace) :
    Pullback.lift f (A.pullbackDiffeomorph (IX := IX) (n := n) f p) = A.pullbackLift f p :=
  A.lift_pullbackHomeomorph f p

/-- `pullbackDiffeomorph` carries the preferred chart at `i` to Mathlib's pullback of the preferred
chart at `f i`. -/
theorem pullbackDiffeomorph_localTriv (A : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y)) (i : X)
    (p : (A.pullback f).core.TotalSpace) :
    (A.core.localTriv (f i)).pullback f (A.pullbackDiffeomorph (IX := IX) (n := n) f p) =
      (A.pullback f).core.localTriv i p :=
  A.pullbackHomeomorph_localTriv f i p

/-- The total space of `A.pullback (ContinuousMap.id X)` is `C^n` diffeomorphic to
`A.core.TotalSpace` by the identity on base points and preferred fibre coordinates, without any
smoothness hypothesis on `X` or `A`. -/
noncomputable def pullbackIdDiffeomorph (A : FiniteRankBundleCore 𝕜 X) :
    (A.pullback (ContinuousMap.id X)).core.TotalSpace ≃ₘ^n⟮
      IX.prod 𝓘(𝕜, Fin (A.pullback (ContinuousMap.id X)).rank → 𝕜),
      IX.prod 𝓘(𝕜, Fin A.rank → 𝕜)⟯ A.core.TotalSpace :=
  (A.pullbackDiffeomorph (IX := IX) (n := n) (ContinuousMap.id X)).trans
    (Bundle.Pullback.idDiffeomorph (I := IX) (m := 0) (n := n) A.core.Fiber)

@[simp]
theorem pullbackIdDiffeomorph_apply (A : FiniteRankBundleCore 𝕜 X)
    (p : (A.pullback (ContinuousMap.id X)).core.TotalSpace) :
    A.pullbackIdDiffeomorph (IX := IX) (n := n) p = ⟨p.proj, p.2⟩ :=
  (congrArg (Bundle.Pullback.idDiffeomorph (I := IX) (m := 0) (n := n) A.core.Fiber)
    (A.pullbackDiffeomorph_apply (IX := IX) (n := n) (ContinuousMap.id X) p)).trans
    (Bundle.Pullback.idDiffeomorph_apply (E := A.core.Fiber) (I := IX) (m := 0) (n := n)
      ⟨p.proj, p.2⟩)

@[simp]
theorem pullbackIdDiffeomorph_symm_apply (A : FiniteRankBundleCore 𝕜 X)
    (p : A.core.TotalSpace) :
    (A.pullbackIdDiffeomorph (IX := IX) (n := n)).symm p = ⟨p.proj, p.2⟩ :=
  (congrArg (A.pullbackDiffeomorph (IX := IX) (n := n) (ContinuousMap.id X)).symm
    (Bundle.Pullback.idDiffeomorph_symm_apply (E := A.core.Fiber) (I := IX) (m := 0) (n := n)
      p)).trans
    (A.pullbackDiffeomorph_symm_apply (IX := IX) (n := n) (ContinuousMap.id X) ⟨p.proj, p.2⟩)

@[simp]
theorem coe_pullbackIdDiffeomorph (A : FiniteRankBundleCore 𝕜 X) :
    ⇑(A.pullbackIdDiffeomorph (IX := IX) (n := n)) = A.pullbackLift (ContinuousMap.id X) :=
  funext fun ⟨x, v⟩ ↦
    (A.pullbackIdDiffeomorph_apply (IX := IX) (n := n) ⟨x, v⟩).trans
      (A.pullbackLift_mk (ContinuousMap.id X) x v).symm

/-- Under `pullbackDiffeomorph`, `A.pullbackIdDiffeomorph` agrees with Mathlib-carrier identity
comparison `Bundle.Pullback.idDiffeomorph`. -/
theorem idDiffeomorph_pullbackDiffeomorph (A : FiniteRankBundleCore 𝕜 X)
    (p : (A.pullback (ContinuousMap.id X)).core.TotalSpace) :
    Bundle.Pullback.idDiffeomorph (I := IX) (m := m) (n := n) A.core.Fiber
        (A.pullbackDiffeomorph (IX := IX) (n := n) (ContinuousMap.id X) p) =
      A.pullbackIdDiffeomorph (IX := IX) (n := n) p :=
  ((congrArg (Bundle.Pullback.idDiffeomorph (I := IX) (m := m) (n := n) A.core.Fiber)
    (A.pullbackDiffeomorph_apply (IX := IX) (n := n) (ContinuousMap.id X) p)).trans
    (Bundle.Pullback.idDiffeomorph_apply (E := A.core.Fiber) (I := IX) (m := m) (n := n)
      ⟨p.proj, p.2⟩)).trans
    (A.pullbackIdDiffeomorph_apply (IX := IX) (n := n) p).symm

/-- Under `pullbackDiffeomorph`, `Bundle.Pullback.compDiffeomorph` intertwines `Pullback.lift f`
with the first-step core lift `(A.pullback g).pullbackLift f` on the strictly equal composite core
`(A.pullback g).pullback f = A.pullback (g.comp f)`. -/
theorem lift_compDiffeomorph_pullbackDiffeomorph
    {EY HY EZ HZ Z : Type*} [NormedAddCommGroup EY] [NormedSpace 𝕜 EY]
    [TopologicalSpace HY] [ChartedSpace HY Y] {IY : ModelWithCorners 𝕜 EY HY}
    [NormedAddCommGroup EZ] [NormedSpace 𝕜 EZ] [TopologicalSpace HZ]
    [TopologicalSpace Z] [ChartedSpace HZ Z] {IZ : ModelWithCorners 𝕜 EZ HZ}
    (A : FiniteRankBundleCore 𝕜 Z) (g : C^m⟮IY, Y; IZ, Z⟯) (f : C^m⟮IX, X; IY, Y⟯) :
    ∀ p : (A.pullback ((g : C(Y, Z)).comp (f : C(X, Y)))).core.TotalSpace,
      Pullback.lift f
          (Bundle.Pullback.compDiffeomorph (n := n) A.core.Fiber g f
            (A.pullbackDiffeomorph (IX := IX) (n := n) ((g : C(Y, Z)).comp (f : C(X, Y))) p)) =
        A.pullbackDiffeomorph (IX := IY) (n := n) (g : C(Y, Z))
          ((A.pullback (g : C(Y, Z))).pullbackLift (f : C(X, Y)) p)
  | ⟨x, v⟩ =>
    ((congrArg (fun q ↦ Pullback.lift f
        (Bundle.Pullback.compDiffeomorph (n := n) A.core.Fiber g f q))
      (A.pullbackDiffeomorph_apply (IX := IX) (n := n) ((g : C(Y, Z)).comp (f : C(X, Y)))
        ⟨x, v⟩)).trans
      (congrArg (Pullback.lift f)
        (Bundle.Pullback.compDiffeomorph_apply (E := A.core.Fiber) (n := n) g f ⟨x, v⟩))).trans
      ((Pullback.lift_mk (E := (g : Y → Z) *ᵖ A.core.Fiber) (F := Fin A.rank → 𝕜) f x v).trans
        ((congrArg (A.pullbackDiffeomorph (IX := IY) (n := n) (g : C(Y, Z)))
          ((A.pullback (g : C(Y, Z))).pullbackLift_mk (f : C(X, Y)) x v)).trans
          (A.pullbackDiffeomorph_apply (IX := IY) (n := n) (g : C(Y, Z)) ⟨f x, v⟩)).symm)

end Comparison

section Smoothness

variable {𝕜 X Y : Type*} [NontriviallyNormedField 𝕜]
  [TopologicalSpace X] [TopologicalSpace Y]
  {EX HX EY HY : Type*} [NormedAddCommGroup EX] [NormedSpace 𝕜 EX]
  [TopologicalSpace HX] [ChartedSpace HX X] {IX : ModelWithCorners 𝕜 EX HX}
  [NormedAddCommGroup EY] [NormedSpace 𝕜 EY]
  [TopologicalSpace HY] [ChartedSpace HY Y] {IY : ModelWithCorners 𝕜 EY HY}
  {m n : ℕ∞ω}

/-- Pulling back a `C^n` finite-rank core along a `C^n` map gives a `C^n` core. Over a complex
manifold at regularity `∞`, pulling back a holomorphic core along a holomorphic map gives a
holomorphic core. -/
theorem isContMDiff_pullback (A : FiniteRankBundleCore 𝕜 Y) [A.core.IsContMDiff IY n]
    (f : C(X, Y)) (hf : ContMDiff IX IY n f) :
    (A.pullback f).core.IsContMDiff IX n where
  contMDiffOn_coordChange i j :=
    (A.core.contMDiffOn_coordChange IY (f i) (f j)).comp hf.contMDiffOn fun _ hx ↦ hx

/-- Pulling back a `C^n` core along a bundled `C^n` map gives a `C^n` core automatically. -/
instance instIsContMDiffPullbackContMDiffMap (A : FiniteRankBundleCore 𝕜 Y)
    [A.core.IsContMDiff IY n] (f : C^n⟮IX, X; IY, Y⟯) :
    (A.pullback (f : C(X, Y))).core.IsContMDiff IX n :=
  A.isContMDiff_pullback (f : C(X, Y)) f.contMDiff

section UniversalProperty

variable {EZ HZ Z : Type*} [NormedAddCommGroup EZ] [NormedSpace 𝕜 EZ]
  [TopologicalSpace HZ] [TopologicalSpace Z] [ChartedSpace HZ Z]
  {IZ : ModelWithCorners 𝕜 EZ HZ}

/-- A map into `(A.pullback f).core.TotalSpace` is `C^n` at `z` exactly when its base projection
and its composite with `A.pullbackLift f` are `C^n` at `z`, provided `f` is `C^n` at `(q z).proj`.
No smoothness assumption on `A` is needed. -/
theorem contMDiffAt_iff_pullbackLift (A : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y))
    {q : Z → (A.pullback f).core.TotalSpace} {z : Z}
    (hf : ContMDiffAt IX IY n f (q z).proj) :
    ContMDiffAt IZ (IX.prod 𝓘(𝕜, Fin (A.pullback f).rank → 𝕜)) n q z ↔
      ContMDiffAt IZ IX n (fun w ↦ (q w).proj) z ∧
        ContMDiffAt IZ (IY.prod 𝓘(𝕜, Fin A.rank → 𝕜)) n (fun w ↦ A.pullbackLift f (q w)) z := by
  have hf' : ContMDiffAt IX IY n f
      (A.pullbackDiffeomorph (IX := IX) (n := n) f (q z)).proj := by
    simpa only [pullbackDiffeomorph_apply] using hf
  rw [← (A.pullbackDiffeomorph (IX := IX) (n := n) f).contMDiffAt_diffeomorph_comp_iff le_rfl]
  refine (Bundle.Pullback.contMDiffAt_iff (IX := IZ) f hf'
    (q := (A.pullbackDiffeomorph (IX := IX) (n := n) f) ∘ q)).trans (and_congr ?_ ?_)
  · exact Filter.EventuallyEq.contMDiffAt_iff (Filter.Eventually.of_forall fun w ↦
      congrArg TotalSpace.proj (A.pullbackDiffeomorph_apply (IX := IX) (n := n) f (q w)))
  · exact Filter.EventuallyEq.contMDiffAt_iff (Filter.Eventually.of_forall fun w ↦
      A.lift_pullbackDiffeomorph (IX := IX) (n := n) f (q w))

/-- A map into `(A.pullback f).core.TotalSpace` is `C^n` exactly when its base projection and its
composite with `A.pullbackLift f` are `C^n`, provided `f` is `C^n`. -/
theorem contMDiff_iff_pullbackLift (A : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y))
    (hf : ContMDiff IX IY n f) {q : Z → (A.pullback f).core.TotalSpace} :
    ContMDiff IZ (IX.prod 𝓘(𝕜, Fin (A.pullback f).rank → 𝕜)) n q ↔
      ContMDiff IZ IX n (fun w ↦ (q w).proj) ∧
        ContMDiff IZ (IY.prod 𝓘(𝕜, Fin A.rank → 𝕜)) n (fun w ↦ A.pullbackLift f (q w)) := by
  simp only [ContMDiff, ← forall_and]
  exact forall_congr' fun z ↦ A.contMDiffAt_iff_pullbackLift f (hf (q z).proj)

end UniversalProperty

/-- The canonical lift `A.pullbackLift f` is `C^n` at every total-space point over which `f` is
`C^n`, without any smoothness assumption on `A`. -/
theorem contMDiffAt_pullbackLift (A : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y))
    {p : (A.pullback f).core.TotalSpace} (hf : ContMDiffAt IX IY n f p.proj) :
    ContMDiffAt (IX.prod 𝓘(𝕜, Fin (A.pullback f).rank → 𝕜))
      (IY.prod 𝓘(𝕜, Fin A.rank → 𝕜)) n (A.pullbackLift f) p :=
  ((A.contMDiffAt_iff_pullbackLift f hf).1 contMDiffAt_id).2

/-- The canonical lift `A.pullbackLift f` is `C^n` whenever `f` is `C^n`. -/
theorem contMDiff_pullbackLift (A : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y))
    (hf : ContMDiff IX IY n f) :
    ContMDiff (IX.prod 𝓘(𝕜, Fin (A.pullback f).rank → 𝕜))
      (IY.prod 𝓘(𝕜, Fin A.rank → 𝕜)) n (A.pullbackLift f) :=
  fun p ↦ A.contMDiffAt_pullbackLift f (hf p.proj)

/-- Pulling back a section `σ` of `A.core` along a map `f` that is `C^n` at `x` preserves `C^n`
regularity at `x`. -/
theorem contMDiffAt_pullback_section (A : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y))
    {x : X} (hf : ContMDiffAt IX IY n f x) {σ : ∀ y, A.core.Fiber y}
    (hσ : ContMDiffAt IY (IY.prod 𝓘(𝕜, Fin A.rank → 𝕜)) n
      (fun y ↦ (⟨y, σ y⟩ : A.core.TotalSpace)) (f x)) :
    ContMDiffAt IX (IX.prod 𝓘(𝕜, Fin (A.pullback f).rank → 𝕜)) n
      (fun x' ↦ (⟨x', σ (f x')⟩ : (A.pullback f).core.TotalSpace)) x :=
  (A.contMDiffAt_iff_pullbackLift (IZ := IX) f hf).2 ⟨contMDiffAt_id,
    (hσ.comp x hf).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun x' ↦ A.pullbackLift_mk f x' (σ (f x')))⟩

/-- Pulling back a `C^n` section `σ` of `A.core` along a `C^n` map `f` gives a `C^n` section of
`(A.pullback f).core`. -/
theorem contMDiff_pullback_section (A : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y))
    (hf : ContMDiff IX IY n f) {σ : ∀ y, A.core.Fiber y}
    (hσ : ContMDiff IY (IY.prod 𝓘(𝕜, Fin A.rank → 𝕜)) n
      (fun y ↦ (⟨y, σ y⟩ : A.core.TotalSpace))) :
    ContMDiff IX (IX.prod 𝓘(𝕜, Fin (A.pullback f).rank → 𝕜)) n
      (fun x ↦ (⟨x, σ (f x)⟩ : (A.pullback f).core.TotalSpace)) :=
  fun x ↦ A.contMDiffAt_pullback_section f (hf x) (hσ (f x))

/-! ### Smoothness of pulled-back morphisms and isomorphisms -/

/-- Pulling back a bundle morphism `a : A ⟶ D` along a `C^n` map `f` preserves `C^n` regularity of
chart operators on each chart overlap. -/
theorem contMDiffOn_inChartCoordinates_pullbackMap {A D : FiniteRankBundleCore 𝕜 Y}
    (a : A ⟶ D) (f : C(X, Y)) (hf : ContMDiff IX IY n f) {i j : X}
    (ha : ContMDiffOn IY 𝓘(𝕜, (Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜)) n
      (fun y ↦ A.core.inChartCoordinates D.core (f i) (f j) y (a.fiberMap y))
      (A.core.baseSet (f i) ∩ D.core.baseSet (f j))) :
    ContMDiffOn IX 𝓘(𝕜, (Fin (A.pullback f).rank → 𝕜) →L[𝕜] (Fin (D.pullback f).rank → 𝕜)) n
      (fun x ↦ (A.pullback f).core.inChartCoordinates (D.pullback f).core i j x
        ((pullbackMap a f).fiberMap x))
      ((A.pullback f).core.baseSet i ∩ (D.pullback f).core.baseSet j) := by
  refine (ha.comp hf.contMDiffOn fun _ hx ↦ hx).congr fun x hx ↦ ?_
  rw [← (pullbackMap a f).operator_eq i j ⟨x, hx⟩, operator_pullbackMap, Function.comp_apply,
    ← a.operator_eq (f i) (f j) ⟨f x, hx⟩]
  rfl

/-- Pulling back a bundle morphism `a : A ⟶ D` preserves `C^n` regularity of the total-space map at
every point `p` where `f` is `C^n` at `p.proj` and `a.totalSpaceMap` is `C^n` at
`A.pullbackLift f p`. Neither completeness of `𝕜` nor smoothness of `A` or `D` is needed. -/
theorem contMDiffAt_totalSpaceMap_pullbackMap {A D : FiniteRankBundleCore 𝕜 Y}
    (a : A ⟶ D) (f : C(X, Y)) {p : (A.pullback f).core.TotalSpace}
    (hf : ContMDiffAt IX IY n f p.proj)
    (ha : ContMDiffAt (IY.prod 𝓘(𝕜, Fin A.rank → 𝕜)) (IY.prod 𝓘(𝕜, Fin D.rank → 𝕜)) n
      a.totalSpaceMap (A.pullbackLift f p)) :
    ContMDiffAt (IX.prod 𝓘(𝕜, Fin (A.pullback f).rank → 𝕜))
      (IX.prod 𝓘(𝕜, Fin (D.pullback f).rank → 𝕜)) n
      (pullbackMap a f).totalSpaceMap p := by
  have hf' : ContMDiffAt IX IY n f ((pullbackMap a f).totalSpaceMap p).proj := by
    rwa [CoordinateHom.totalSpaceMap_proj]
  refine (D.contMDiffAt_iff_pullbackLift f hf').2 ⟨?_, ?_⟩
  · exact ((contMDiff_proj (A.pullback f).core.Fiber).congr
      (pullbackMap a f).totalSpaceMap_proj).contMDiffAt
  · exact (ha.comp p (A.contMDiffAt_pullbackLift f hf)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall (pullbackLift_totalSpaceMap_pullbackMap a f))

/-- Pulling back a bundle morphism `a : A ⟶ D` with `C^n` total-space map along a `C^n` map `f`
produces a bundle morphism with `C^n` total-space map. -/
theorem contMDiff_totalSpaceMap_pullbackMap {A D : FiniteRankBundleCore 𝕜 Y}
    (a : A ⟶ D) (f : C(X, Y)) (hf : ContMDiff IX IY n f)
    (ha : ContMDiff (IY.prod 𝓘(𝕜, Fin A.rank → 𝕜)) (IY.prod 𝓘(𝕜, Fin D.rank → 𝕜)) n
      a.totalSpaceMap) :
    ContMDiff (IX.prod 𝓘(𝕜, Fin (A.pullback f).rank → 𝕜))
      (IX.prod 𝓘(𝕜, Fin (D.pullback f).rank → 𝕜)) n
      (pullbackMap a f).totalSpaceMap :=
  fun p ↦ contMDiffAt_totalSpaceMap_pullbackMap a f (hf p.proj) (ha (A.pullbackLift f p))

/-- Pulling back a core isomorphism `e : A ≅ D` whose forward and inverse total-space maps are
`C^n` along a `C^n` map `f` produces a `C^n` diffeomorphism of pulled-back total spaces, without
completeness assumptions on `𝕜` or smoothness assumptions on `A` and `D`. -/
def pullbackIsoDiffeomorph {A D : FiniteRankBundleCore 𝕜 Y} (e : A ≅ D)
    (f : C(X, Y)) (hf : ContMDiff IX IY n f)
    (he_hom : ContMDiff (IY.prod 𝓘(𝕜, Fin A.rank → 𝕜)) (IY.prod 𝓘(𝕜, Fin D.rank → 𝕜)) n
      e.hom.totalSpaceMap)
    (he_inv : ContMDiff (IY.prod 𝓘(𝕜, Fin D.rank → 𝕜)) (IY.prod 𝓘(𝕜, Fin A.rank → 𝕜)) n
      e.inv.totalSpaceMap) :
    (A.pullback f).core.TotalSpace ≃ₘ^n⟮IX.prod 𝓘(𝕜, Fin (A.pullback f).rank → 𝕜),
      IX.prod 𝓘(𝕜, Fin (D.pullback f).rank → 𝕜)⟯ (D.pullback f).core.TotalSpace :=
  CoordinateHom.toDiffeomorphOfInv (pullbackMap e.hom f) (pullbackMap e.inv f)
    (((pullbackMap_comp e.hom e.inv f).symm.trans (congrArg (pullbackMap · f) e.hom_inv_id)).trans
      (pullbackMap_id A f))
    (((pullbackMap_comp e.inv e.hom f).symm.trans (congrArg (pullbackMap · f) e.inv_hom_id)).trans
      (pullbackMap_id D f))
    (contMDiff_totalSpaceMap_pullbackMap e.hom f hf he_hom)
    (contMDiff_totalSpaceMap_pullbackMap e.inv f hf he_inv)

@[simp]
theorem coe_pullbackIsoDiffeomorph {A D : FiniteRankBundleCore 𝕜 Y} (e : A ≅ D)
    (f : C(X, Y)) (hf : ContMDiff IX IY n f)
    (he_hom : ContMDiff (IY.prod 𝓘(𝕜, Fin A.rank → 𝕜)) (IY.prod 𝓘(𝕜, Fin D.rank → 𝕜)) n
      e.hom.totalSpaceMap)
    (he_inv : ContMDiff (IY.prod 𝓘(𝕜, Fin D.rank → 𝕜)) (IY.prod 𝓘(𝕜, Fin A.rank → 𝕜)) n
      e.inv.totalSpaceMap) :
    ⇑(pullbackIsoDiffeomorph e f hf he_hom he_inv) = (pullbackMap e.hom f).totalSpaceMap :=
  CoordinateHom.coe_toDiffeomorphOfInv _ _ _ _ _ _

@[simp]
theorem coe_pullbackIsoDiffeomorph_symm {A D : FiniteRankBundleCore 𝕜 Y} (e : A ≅ D)
    (f : C(X, Y)) (hf : ContMDiff IX IY n f)
    (he_hom : ContMDiff (IY.prod 𝓘(𝕜, Fin A.rank → 𝕜)) (IY.prod 𝓘(𝕜, Fin D.rank → 𝕜)) n
      e.hom.totalSpaceMap)
    (he_inv : ContMDiff (IY.prod 𝓘(𝕜, Fin D.rank → 𝕜)) (IY.prod 𝓘(𝕜, Fin A.rank → 𝕜)) n
      e.inv.totalSpaceMap) :
    ⇑(pullbackIsoDiffeomorph e f hf he_hom he_inv).symm =
      (pullbackMap e.inv f).totalSpaceMap :=
  CoordinateHom.coe_toDiffeomorphOfInv_symm _ _ _ _ _ _

/-! ### Local diffeomorphisms and regularity descent -/

/-- Auxiliary partial diffeomorphism witnessing `isLocalDiffeomorphAt_pullbackLift` over an open
base neighbourhood `W₀` of `p₀.proj` on which `f` is a `C^n` local diffeomorphism. -/
private noncomputable def pullbackLiftPartialDiffeomorph (A : FiniteRankBundleCore 𝕜 Y)
    (f : C(X, Y)) {p₀ : (A.pullback f).core.TotalSpace}
    (hf : IsLocalDiffeomorphAt IX IY n f p₀.proj)
    {W₀ : Set X} (hW₀_open : IsOpen W₀)
    (hW₀ : ∀ x ∈ W₀, IsLocalDiffeomorphAt IX IY n f x) :
    PartialDiffeomorph (IX.prod 𝓘(𝕜, Fin (A.pullback f).rank → 𝕜))
      (IY.prod 𝓘(𝕜, Fin A.rank → 𝕜))
      (A.pullback f).core.TotalSpace A.core.TotalSpace n :=
  let Ψ := hf.localInverse
  let U : Set X := W₀ ∩ (Ψ.target ∩ f ⁻¹' Ψ.source)
  let hU_open : IsOpen U :=
    hW₀_open.inter (Ψ.open_target.inter (Ψ.open_source.preimage f.continuous))
  let V : Set Y := Ψ.source ∩ Ψ ⁻¹' U
  let hV_open : IsOpen V := Ψ.toOpenPartialHomeomorph.isOpen_inter_preimage hU_open
  let inv : A.core.TotalSpace → (A.pullback f).core.TotalSpace := fun q ↦ ⟨Ψ q.proj, q.2⟩
  { toFun := A.pullbackLift f
    invFun := inv
    source := TotalSpace.proj ⁻¹' U
    target := TotalSpace.proj ⁻¹' V
    map_source' := fun p hp ↦ by
      rw [mem_preimage, A.pullbackLift_proj]
      exact ⟨hp.2.2, by rwa [mem_preimage, hf.localInverse_left_inv hp.2.1]⟩
    map_target' := fun _ hq ↦ hq.2
    left_inv' := fun ⟨x, v⟩ hp ↦
      (congrArg inv (A.pullbackLift_mk f x v)).trans
        (congrArg (fun x' ↦ (⟨x', v⟩ : (A.pullback f).core.TotalSpace))
          (hf.localInverse_left_inv hp.2.1))
    right_inv' := fun ⟨y, v⟩ hq ↦
      (A.pullbackLift_mk f (Ψ y) v).trans
        (congrArg (fun y' ↦ (⟨y', v⟩ : A.core.TotalSpace))
          (hf.localInverse_right_inv hq.1))
    open_source := hU_open.preimage (continuous_proj _)
    open_target := hV_open.preimage (continuous_proj _)
    contMDiffOn_toFun := fun p hp ↦
      (A.contMDiffAt_pullbackLift f (hW₀ p.proj hp.1).contMDiffAt).contMDiffWithinAt
    contMDiffOn_invFun := fun q hq ↦ by
      refine (ContMDiffAt.contMDiffWithinAt <|
        (A.contMDiffAt_iff_pullbackLift f (hW₀ (Ψ q.proj) hq.2.1).contMDiffAt).2 ⟨?_, ?_⟩)
      · exact ((Ψ.contMDiffOn q.proj hq.1).contMDiffAt
          (Ψ.open_source.mem_nhds hq.1)).comp q (contMDiff_proj A.core.Fiber).contMDiffAt
      · refine contMDiffAt_id.congr_of_eventuallyEq ?_
        filter_upwards [(Ψ.open_source.preimage (continuous_proj _)).mem_nhds hq.1] with ⟨y, v⟩ hq'
        exact (A.pullbackLift_mk f (Ψ y) v).trans
          (congrArg (fun y' ↦ (⟨y', v⟩ : A.core.TotalSpace)) (hf.localInverse_right_inv hq')) }

/-- If `f` is a `C^n` local diffeomorphism at `p₀.proj`, then the canonical lift `A.pullbackLift f`
is a `C^n` local diffeomorphism of total spaces at `p₀`. No smoothness assumption on `A` or
manifold assumption on `X` or `Y` is needed. -/
theorem isLocalDiffeomorphAt_pullbackLift (A : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y))
    {p₀ : (A.pullback f).core.TotalSpace} (hf : IsLocalDiffeomorphAt IX IY n f p₀.proj) :
    IsLocalDiffeomorphAt (IX.prod 𝓘(𝕜, Fin (A.pullback f).rank → 𝕜))
      (IY.prod 𝓘(𝕜, Fin A.rank → 𝕜)) n (A.pullbackLift f) p₀ := by
  obtain ⟨W₀, hW₀, hW₀_open, hp₀W₀⟩ := mem_nhds_iff.1 hf.eventually
  exact TauCeti.isLocalDiffeomorphAt_of_eqOn
    (Φ := A.pullbackLiftPartialDiffeomorph f hf hW₀_open hW₀)
    ⟨hp₀W₀, hf.localInverse_mem_target, hf.localInverse_mem_source⟩
    fun _ _ ↦ rfl

/-- If `f` is a `C^n` local diffeomorphism, then `A.pullbackLift f` is a `C^n` local diffeomorphism
between `(A.pullback f).core.TotalSpace` and `A.core.TotalSpace`. -/
theorem isLocalDiffeomorph_pullbackLift (A : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y))
    (hf : IsLocalDiffeomorph IX IY n f) :
    IsLocalDiffeomorph (IX.prod 𝓘(𝕜, Fin (A.pullback f).rank → 𝕜))
      (IY.prod 𝓘(𝕜, Fin A.rank → 𝕜)) n (A.pullbackLift f) :=
  fun p ↦ A.isLocalDiffeomorphAt_pullbackLift f (hf p.proj)

/-- Along a surjective `C^n` local diffeomorphism `f`, for `m ≤ n`, a finite-rank core `A` over `Y`
has `C^m` transition functions if and only if its pullback `A.pullback f` over `X` does. -/
theorem isContMDiff_pullback_iff_of_isLocalDiffeomorph (A : FiniteRankBundleCore 𝕜 Y)
    (f : C(X, Y)) (hf : IsLocalDiffeomorph IX IY n f) (hsurj : Function.Surjective f)
    (hm : m ≤ n) :
    (A.pullback f).core.IsContMDiff IX m ↔ A.core.IsContMDiff IY m := by
  refine ⟨fun hpull ↦ ⟨fun i j ↦ ?_⟩, fun hA ↦ A.isContMDiff_pullback f (hf.contMDiff.of_le hm)⟩
  intro y hy
  obtain ⟨i₀, rfl⟩ := hsurj i
  obtain ⟨j₀, rfl⟩ := hsurj j
  obtain ⟨x, rfl⟩ := hsurj y
  refine ContMDiffAt.contMDiffWithinAt <| ((hf x).contMDiffAt_comp_iff hm).1 ?_
  have hU : x ∈ (A.pullback f).core.baseSet i₀ ∩ (A.pullback f).core.baseSet j₀ := hy
  exact (hpull.contMDiffOn_coordChange i₀ j₀ x hU).contMDiffAt
    (((A.pullback f).core.isOpen_baseSet i₀ |>.inter
      ((A.pullback f).core.isOpen_baseSet j₀)).mem_nhds hU)

/-- If `f` is a `C^n` local diffeomorphism at `x` and `m ≤ n`, a section `σ` of `A.core` is `C^m`
at `f x` if and only if its pullback `x' ↦ σ (f x')` is a `C^m` section of `(A.pullback f).core`
at `x`. -/
theorem contMDiffAt_section_iff_pullback_of_isLocalDiffeomorphAt (A : FiniteRankBundleCore 𝕜 Y)
    (f : C(X, Y)) {x : X} (hf : IsLocalDiffeomorphAt IX IY n f x) (hm : m ≤ n)
    {σ : ∀ y, A.core.Fiber y} :
    ContMDiffAt IY (IY.prod 𝓘(𝕜, Fin A.rank → 𝕜)) m
        (fun y ↦ (⟨y, σ y⟩ : A.core.TotalSpace)) (f x) ↔
      ContMDiffAt IX (IX.prod 𝓘(𝕜, Fin (A.pullback f).rank → 𝕜)) m
        (fun x' ↦ (⟨x', σ (f x')⟩ : (A.pullback f).core.TotalSpace)) x :=
  ((hf.contMDiffAt_comp_iff (I' := IY.prod 𝓘(𝕜, Fin A.rank → 𝕜))
    (g := fun y ↦ (⟨y, σ y⟩ : A.core.TotalSpace)) hm).symm.trans
    (Filter.EventuallyEq.contMDiffAt_iff (Filter.Eventually.of_forall fun w ↦
      (A.pullbackLift_mk f w (σ (f w))).symm))).trans
    ((and_iff_right contMDiffAt_id).symm.trans
      (A.contMDiffAt_iff_pullbackLift (IZ := IX)
        (q := fun x' ↦ (⟨x', σ (f x')⟩ : (A.pullback f).core.TotalSpace)) f
        (hf.contMDiffAt.of_le hm)).symm)

/-- Along a surjective `C^n` local diffeomorphism `f`, for `m ≤ n`, a section `σ` of `A.core` is
`C^m` if and only if its pullback `x ↦ σ (f x)` is a `C^m` section of `(A.pullback f).core`. -/
theorem contMDiff_section_iff_pullback_of_isLocalDiffeomorph (A : FiniteRankBundleCore 𝕜 Y)
    (f : C(X, Y)) (hf : IsLocalDiffeomorph IX IY n f) (hsurj : Function.Surjective f)
    (hm : m ≤ n) {σ : ∀ y, A.core.Fiber y} :
    ContMDiff IY (IY.prod 𝓘(𝕜, Fin A.rank → 𝕜)) m
        (fun y ↦ (⟨y, σ y⟩ : A.core.TotalSpace)) ↔
      ContMDiff IX (IX.prod 𝓘(𝕜, Fin (A.pullback f).rank → 𝕜)) m
        (fun x ↦ (⟨x, σ (f x)⟩ : (A.pullback f).core.TotalSpace)) := by
  refine ⟨fun h x ↦ (A.contMDiffAt_section_iff_pullback_of_isLocalDiffeomorphAt f (hf x) hm).1
    (h (f x)), fun h y ↦ ?_⟩
  obtain ⟨x, rfl⟩ := hsurj y
  exact (A.contMDiffAt_section_iff_pullback_of_isLocalDiffeomorphAt f (hf x) hm).2 (h x)

/-- If `f` is a `C^n` local diffeomorphism at `p.proj` and `m ≤ n`, the pulled-back morphism
`pullbackMap a f` has `C^m` total-space map at `p` if and only if `a` has `C^m` total-space map at
`A.pullbackLift f p`. -/
theorem contMDiffAt_totalSpaceMap_pullbackMap_iff_of_isLocalDiffeomorphAt
    {A D : FiniteRankBundleCore 𝕜 Y} (a : A ⟶ D) (f : C(X, Y))
    {p : (A.pullback f).core.TotalSpace}
    (hf : IsLocalDiffeomorphAt IX IY n f p.proj) (hm : m ≤ n) :
    ContMDiffAt (IX.prod 𝓘(𝕜, Fin (A.pullback f).rank → 𝕜))
        (IX.prod 𝓘(𝕜, Fin (D.pullback f).rank → 𝕜)) m
        (pullbackMap a f).totalSpaceMap p ↔
      ContMDiffAt (IY.prod 𝓘(𝕜, Fin A.rank → 𝕜)) (IY.prod 𝓘(𝕜, Fin D.rank → 𝕜)) m
        a.totalSpaceMap (A.pullbackLift f p) := by
  have hf' : ContMDiffAt IX IY m f ((pullbackMap a f).totalSpaceMap p).proj := by
    rw [CoordinateHom.totalSpaceMap_proj]
    exact hf.contMDiffAt.of_le hm
  have hiff := D.contMDiffAt_iff_pullbackLift
    (IZ := IX.prod 𝓘(𝕜, Fin (A.pullback f).rank → 𝕜))
    (q := (pullbackMap a f).totalSpaceMap) f hf'
  have hproj : ContMDiffAt (IX.prod 𝓘(𝕜, Fin (A.pullback f).rank → 𝕜)) IX m
      (fun q ↦ ((pullbackMap a f).totalSpaceMap q).proj) p :=
    ((contMDiff_proj (A.pullback f).core.Fiber).congr
      (pullbackMap a f).totalSpaceMap_proj).contMDiffAt
  refine hiff.trans ((and_iff_right hproj).trans ?_)
  rw [← (A.isLocalDiffeomorphAt_pullbackLift f hf).contMDiffAt_comp_iff hm]
  exact Filter.EventuallyEq.contMDiffAt_iff
    (Filter.Eventually.of_forall (pullbackLift_totalSpaceMap_pullbackMap a f))

/-- Along a surjective `C^n` local diffeomorphism `f`, for `m ≤ n`, the pulled-back morphism
`pullbackMap a f` has `C^m` total-space map if and only if `a` does. -/
theorem contMDiff_totalSpaceMap_pullbackMap_iff_of_isLocalDiffeomorph
    {A D : FiniteRankBundleCore 𝕜 Y} (a : A ⟶ D) (f : C(X, Y))
    (hf : IsLocalDiffeomorph IX IY n f) (hsurj : Function.Surjective f) (hm : m ≤ n) :
    ContMDiff (IX.prod 𝓘(𝕜, Fin (A.pullback f).rank → 𝕜))
        (IX.prod 𝓘(𝕜, Fin (D.pullback f).rank → 𝕜)) m
        (pullbackMap a f).totalSpaceMap ↔
      ContMDiff (IY.prod 𝓘(𝕜, Fin A.rank → 𝕜)) (IY.prod 𝓘(𝕜, Fin D.rank → 𝕜)) m
        a.totalSpaceMap := by
  refine ⟨fun h q ↦ ?_, fun h p ↦
    (contMDiffAt_totalSpaceMap_pullbackMap_iff_of_isLocalDiffeomorphAt a f (hf p.proj) hm).2
      (h (A.pullbackLift f p))⟩
  obtain ⟨p, rfl⟩ := A.pullbackLift_surjective hsurj q
  exact (contMDiffAt_totalSpaceMap_pullbackMap_iff_of_isLocalDiffeomorphAt a f (hf p.proj) hm).1
    (h p)

end Smoothness

end TauCeti.FiniteRankBundleCore
