/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
public import TauCeti.Geometry.Manifold.PontryaginThom.Degree

/-!
# The Pontryagin–Thom collapse along a transverse map

Let `τ : S × V → Q` be a framed tube around `f : S → Q` (`TauCeti.IsFramedTube`) and let
`c : Q → OnePoint V` be its Pontryagin–Thom collapse. Near a point `x` at which a map
`σ : M → Q` enters the tube, `σ` reads in the tube as `τ ∘ g`, and `c ∘ σ` is the
**normal coordinate** `Prod.snd ∘ g` followed by the inclusion `V → OnePoint V`. So `c ∘ σ` is a
local homeomorphism at `x` as soon as the normal coordinate is
(`TauCeti.isLocalHomeomorphOn_pontryaginThomCollapse_comp`).

Let the tube be a smooth local diffeomorphism at `(y, 0)` and let `σ` read in the tube as `τ ∘ g`
near `x`, with `g x = (y, 0)`. If `σ` is transverse to `f` there, `im dσ_x + im df_y = T_{σ x} Q`,
then the normal coordinate has a surjective differential at `x`
(`TauCeti.IsFramedTube.surjective_mfderiv_snd_comp_of_transverse`). If moreover `σ` is smooth
near `x` and `dim M = dim V`, this differential is bijective. The inverse function theorem then
makes the normal coordinate a local diffeomorphism, and `c ∘ σ` a local homeomorphism at `x`
(`TauCeti.IsFramedTube.isLocalHomeomorphOn_pontryaginThomCollapse_comp_of_transverse`). This is
the transversality input of the degree computation for a map meeting the core of a framed tube in
one point: such a map, transverse to the core there, has collapse of degree `±1`
(`TauCeti.IsFramedTube.degree_pontryaginThomSphereMap_comp_eq_one_or_eq_neg_one_of_transverse`).

## Main results

* `TauCeti.IsFramedTube.surjective_mfderiv_snd_comp_of_transverse`: the normal coordinate of a map
  transverse to the core of a smooth tube is a submersion at the meeting point.
* `TauCeti.IsFramedTube.exists_isLocalDiffeomorphAt_snd_comp_of_transverse`: the normal coordinate
  of a smooth map transverse to the core of a smooth tube, from a manifold of the dimension of the
  fibre, is a local diffeomorphism at the meeting point.
* `TauCeti.IsFramedTube.isLocalHomeomorphOn_pontryaginThomCollapse_comp_of_transverse`,
  `TauCeti.IsFramedTube.isLocalHomeomorphOn_pontryaginThomSphereMap_comp_of_transverse`: a smooth
  map transverse to the core of a smooth tube, from a manifold of the dimension of the fibre, has
  collapse a local homeomorphism at the meeting point.
* `TauCeti.IsFramedTube.degree_pontryaginThomSphereMap_comp_eq_one_or_eq_neg_one_of_transverse`:
  a smooth map from a compact oriented `k`-manifold meeting the core once, transversely, has
  collapse onto `Sᵏ` of degree `±1`.

## References

* J. W. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia,
  1965, §7.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §7, proof of Lemma 7.6.
-/

public section

open Function Set Topology Filter
open scoped Manifold ContDiff

namespace TauCeti

namespace IsFramedTube

section Smooth

variable {𝕂 : Type*} [RCLike 𝕂]
  {ES : Type*} [NormedAddCommGroup ES] [NormedSpace 𝕂 ES] {HS : Type*} [TopologicalSpace HS]
  {IS : ModelWithCorners 𝕂 ES HS} {S : Type*} [TopologicalSpace S] [ChartedSpace HS S]
  {EQ : Type*} [NormedAddCommGroup EQ] [NormedSpace 𝕂 EQ] {HQ : Type*} [TopologicalSpace HQ]
  {IQ : ModelWithCorners 𝕂 EQ HQ} {Q : Type*} [TopologicalSpace Q] [ChartedSpace HQ Q]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕂 EM] {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners 𝕂 EM HM} {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕂 V]
  {n : WithTop ℕ∞} {f : S → Q} {τ : S × V → Q}

/-- **The normal coordinate of a transverse map is a submersion.** Let `τ : S × V → Q` be a framed
tube around `f` which is a `C^n` local diffeomorphism at `(y, 0)`, `n ≠ 0`, and let `σ : M → Q`
read in the tube as `τ ∘ g` near `x`, for a map `g` differentiable at `x` with `g x = (y, 0)`. If
`σ` is transverse to `f` there, `im dσ_x + im df_y = T_{σ x} Q`, then the normal coordinate
`Prod.snd ∘ g` has surjective differential at `x`. -/
theorem surjective_mfderiv_snd_comp_of_transverse (h : IsFramedTube f τ) {y : S}
    (hτ : IsLocalDiffeomorphAt (IS.prod 𝓘(𝕂, V)) IQ n τ (y, 0)) (hn : n ≠ 0) {σ : M → Q}
    {x : M} {g : M → S × V} (hg : τ ∘ g =ᶠ[𝓝 x] σ) (hgx : g x = (y, 0))
    (hgd : MDifferentiableAt IM (IS.prod 𝓘(𝕂, V)) g x)
    (htrans : (mfderiv IM IQ σ x).range ⊔
      (((tangentSpaceCast IQ (f y) (σ x)).toContinuousLinearMap).comp
        (mfderiv IS IQ f y)).range = ⊤) :
    Surjective (mfderiv IM 𝓘(𝕂, V) (Prod.snd ∘ g) x) := by
  have hτd : MDifferentiableAt (IS.prod 𝓘(𝕂, V)) IQ τ (y, 0) := hτ.mdifferentiableAt hn
  -- Tangent spaces are the model spaces by definition; read the differentials there.
  let dτ : ES × V →L[𝕂] EQ := mfderiv (IS.prod 𝓘(𝕂, V)) IQ τ (y, 0)
  let dg : EM →L[𝕂] ES × V := mfderiv IM (IS.prod 𝓘(𝕂, V)) g x
  -- `dτ` is injective, as `τ` is a local diffeomorphism at `(y, 0) = g x`.
  have hdτ : Injective dτ := (hτ.mfderivToContinuousLinearEquiv hn).injective
  have hτD : HasMFDerivAt (IS.prod 𝓘(𝕂, V)) IQ τ (g x) dτ := by
    rw [hgx]
    exact hτd.hasMFDerivAt
  -- The chain rule gives `dσ = dτ ∘ dg`; applied to `u`, the composite is `dτ (dg u)` by
  -- definition, through the identification of tangent spaces with model spaces.
  have hσd (u : EM) : mfderiv IM IQ σ x u = dτ (dg u) := by
    rw [((hτD.comp x hgd.hasMFDerivAt).congr_of_eventuallyEq_abuse hg.symm).mfderiv]
    rfl
  -- The differential of `f` is that of `τ` along the zero section.
  have hfd (v : ES) : mfderiv IS IQ f y v = dτ (v, 0) := by
    have hz : HasMFDerivAt IS (IS.prod 𝓘(𝕂, V)) (fun s ↦ (s, (0 : V))) y
        (ContinuousLinearMap.inl 𝕂 ES V) :=
      (hasMFDerivAt_id y).prodMk (hasMFDerivAt_const (0 : V) y)
    have : mfderiv IS IQ f y = dτ.comp (ContinuousLinearMap.inl 𝕂 ES V) :=
      ((hτd.hasMFDerivAt.comp y hz).congr_of_eventuallyEq_abuse
        (Eventually.of_forall fun s ↦ (h.apply_zero s).symm)).mfderiv
    -- `dτ ∘ inl` applied to `v` is `dτ (v, 0)` by definition, as above.
    rw [this]
    rfl
  -- The differential of the normal coordinate sends `u` to `(dg u).2`, again by definition.
  have hνd (u : EM) : mfderiv IM 𝓘(𝕂, V) (Prod.snd ∘ g) x u = (dg u).2 := by
    rw [((hasMFDerivAt_snd _).comp x hgd.hasMFDerivAt).mfderiv]
    rfl
  -- By transversality `dτ (0, w) = dσ u + df v = dτ (dg u + (v, 0))`, and `dτ` is injective.
  intro (w : V)
  obtain ⟨⟨u, v⟩, huv⟩ :=
    LinearMap.range_eq_top.1 ((LinearMap.range_coprod _ _).trans htrans) (dτ (0, w))
  simp only [LinearMap.coprod_apply, ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe] at huv
  change EM at u
  change ES at v
  -- `huv` is `dσ u + df v = dτ (0, w)`: `tangentSpaceCast` is the identity by definition (Mathlib
  -- has no `_apply` lemma for it), and the tangent spaces of `Q` are `EQ` by definition.
  have hdg : dg u + (v, 0) = (0, w) := hdτ (by rw [map_add, ← hσd, ← hfd]; exact huv)
  have hw : (dg u).2 = w := by simpa using congrArg Prod.snd hdg
  exact ⟨u, (hνd u).trans hw⟩

/-- **The normal coordinate of a transverse map is a local diffeomorphism.** Let `τ : S × V → Q`
be a framed tube around `f` which is a `C^n` local diffeomorphism at `(y, 0)`, `1 ≤ n`, and let
`σ : M → Q` be `C^n` near an interior point `x` of a manifold of the dimension of `V`, with
`σ x = f y`. If `σ` is transverse to `f` there, `im dσ_x + im df_y = T_{σ x} Q`, then near `x` the
map `σ` reads in the tube as `τ ∘ g` with normal coordinate `Prod.snd ∘ g` a `C^n` local
diffeomorphism at `x`. -/
theorem exists_isLocalDiffeomorphAt_snd_comp_of_transverse [FiniteDimensional 𝕂 EM]
    [FiniteDimensional 𝕂 V] [IsManifold IM n M] (h : IsFramedTube f τ)
    {y : S} (hτ : IsLocalDiffeomorphAt (IS.prod 𝓘(𝕂, V)) IQ n τ (y, 0)) {σ : M → Q} {x : M}
    {s : Set M} (hs : s ∈ 𝓝 x) (hσ : ContMDiffOn IM IQ n σ s) (hIx : IM.IsInteriorPoint x)
    (hn : 1 ≤ n) (hdim : Module.finrank 𝕂 EM = Module.finrank 𝕂 V) (hy : f y = σ x)
    (htrans : (mfderiv IM IQ σ x).range ⊔
      (((tangentSpaceCast IQ (f y) (σ x)).toContinuousLinearMap).comp
        (mfderiv IS IQ f y)).range = ⊤) :
    ∃ g : M → S × V, τ ∘ g =ᶠ[𝓝 x] σ ∧ IsLocalDiffeomorphAt IM 𝓘(𝕂, V) n (Prod.snd ∘ g) x := by
  have hn0 : n ≠ 0 := by rintro rfl; exact absurd hn (by simp)
  have : CompleteSpace EM := FiniteDimensional.completeSpace 𝕂 EM
  set L := hτ.localInverse
  have hτy : τ (y, 0) = σ x := (h.apply_zero y).trans hy
  -- The normal coordinate `m ↦ (L (σ m)).2` is defined where `σ` lands in the source of `L`.
  set U := interior s ∩ σ ⁻¹' L.source
  have hUopen : IsOpen U :=
    (hσ.continuousOn.mono interior_subset).isOpen_inter_preimage isOpen_interior
      L.open_source
  have hxU : x ∈ U := ⟨mem_interior_iff_mem_nhds.2 hs, by
    simpa only [mem_preimage, ← hτy] using hτ.localInverse_mem_source⟩
  have hLσ : ∀ m ∈ U, τ (L (σ m)) = σ m := fun m hm ↦ hτ.localInverse_right_inv hm.2
  have hLσx : (L ∘ σ) x = (y, 0) := by
    rw [comp_apply, ← hτy]
    exact hτ.localInverse_left_inv hτ.localInverse_mem_target
  have hLσd : MDifferentiableAt IM (IS.prod 𝓘(𝕂, V)) (L ∘ σ) x :=
    MDifferentiableAt.comp x (hτy ▸ hτ.mdifferentiableAt_localInverse hn0)
      ((hσ.contMDiffAt hs).mdifferentiableAt hn0)
  have hνsmooth : ContMDiffOn IM 𝓘(𝕂, V) n (fun m ↦ (L (σ m)).2) U :=
    contMDiff_snd.comp_contMDiffOn
      (hτ.contMDiffOn_localInverse.comp (hσ.mono fun m hm ↦ interior_subset hm.1)
        fun m hm ↦ hm.2)
  -- The differential of the normal coordinate is surjective, hence bijective in equal
  -- dimensions, and the inverse function theorem applies.
  have hg : τ ∘ L ∘ σ =ᶠ[𝓝 x] σ := eventually_of_mem (hUopen.mem_nhds hxU) hLσ
  have hsurj := h.surjective_mfderiv_snd_comp_of_transverse hτ hn0 hg hLσx hLσd htrans
  have hinj : Injective (mfderiv IM 𝓘(𝕂, V) (Prod.snd ∘ L ∘ σ) x) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).2 hsurj
  exact ⟨L ∘ σ, hg, isLocalDiffeomorphAt_of_injective_mfderiv hνsmooth hUopen hxU hIx hn hinj hdim⟩

/-- **The collapse along a transverse map is a local homeomorphism.** Let `τ : S × V → Q` be a
framed tube around `f` which is a `C^n` local diffeomorphism at `(y, 0)`, `1 ≤ n`, and let
`σ : M → Q` be `C^n` near an interior point `x` of a manifold of the dimension of `V`, with
`σ x = f y`. If `σ` is transverse to `f` there, `im dσ_x + im df_y = T_{σ x} Q`, then the
composite of `σ` with the Pontryagin–Thom collapse is a local homeomorphism at `x`. -/
theorem isLocalHomeomorphOn_pontryaginThomCollapse_comp_of_transverse [FiniteDimensional 𝕂 EM]
    [FiniteDimensional 𝕂 V] [IsManifold IM n M] (h : IsFramedTube f τ) {y : S}
    (hτ : IsLocalDiffeomorphAt (IS.prod 𝓘(𝕂, V)) IQ n τ (y, 0)) {σ : M → Q} {x : M}
    {s : Set M} (hs : s ∈ 𝓝 x) (hσ : ContMDiffOn IM IQ n σ s) (hIx : IM.IsInteriorPoint x)
    (hn : 1 ≤ n) (hdim : Module.finrank 𝕂 EM = Module.finrank 𝕂 V) (hy : f y = σ x)
    (htrans : (mfderiv IM IQ σ x).range ⊔
      (((tangentSpaceCast IQ (f y) (σ x)).toContinuousLinearMap).comp
        (mfderiv IS IQ f y)).range = ⊤) :
    IsLocalHomeomorphOn (pontryaginThomCollapse τ ∘ σ) {x} := by
  obtain ⟨g, hg, hν⟩ :=
    h.exists_isLocalDiffeomorphAt_snd_comp_of_transverse hτ hs hσ hIx hn hdim hy htrans
  refine isLocalHomeomorphOn_pontryaginThomCollapse_comp h.isOpenEmbedding.injective
    (by rintro _ rfl; exact hg) ?_
  exact IsLocalDiffeomorphOn.isLocalHomeomorphOn (I := IM) (J := 𝓘(𝕂, V)) (n := n)
    fun ⟨_, hz⟩ ↦ (mem_singleton_iff.1 hz).symm ▸ hν

end Smooth

section Sphere

variable {ES : Type*} [NormedAddCommGroup ES] [NormedSpace ℝ ES] {HS : Type*}
  [TopologicalSpace HS] {IS : ModelWithCorners ℝ ES HS} {S : Type*} [TopologicalSpace S]
  [ChartedSpace HS S] [CompactSpace S]
  {EQ : Type*} [NormedAddCommGroup EQ] [NormedSpace ℝ EQ] {HQ : Type*} [TopologicalSpace HQ]
  {IQ : ModelWithCorners ℝ EQ HQ} {Q : Type*} [TopologicalSpace Q] [ChartedSpace HQ Q] [T2Space Q]
  {n : WithTop ℕ∞} {k : ℕ} {f : S → Q} {τ : S × (Fin k → ℝ) → Q}

/-- **The collapse onto the sphere along a transverse map is a local homeomorphism.** For a framed
tube with fibre `ℝᵏ` which is a `C^n` local diffeomorphism at `(y, 0)`, `1 ≤ n`, and a map `σ`
from a `k`-manifold, `C^n` near an interior point `x` with `σ x = f y` and transverse to `f`
there, the composite of `σ` with the Pontryagin–Thom collapse onto `Sᵏ` is a local
homeomorphism at `x`. -/
theorem isLocalHomeomorphOn_pontryaginThomSphereMap_comp_of_transverse
    {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [FiniteDimensional ℝ EM]
    {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM}
    {M : Type*} [TopologicalSpace M] [ChartedSpace HM M] [IsManifold IM n M]
    (h : IsFramedTube f τ) (s₀ : Metric.sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) {y : S}
    (hτ : IsLocalDiffeomorphAt (IS.prod 𝓘(ℝ, Fin k → ℝ)) IQ n τ (y, 0)) {σ : M → Q} {x : M}
    {s : Set M} (hs : s ∈ 𝓝 x) (hσ : ContMDiffOn IM IQ n σ s) (hIx : IM.IsInteriorPoint x)
    (hn : 1 ≤ n) (hdim : Module.finrank ℝ EM = k) (hy : f y = σ x)
    (htrans : (mfderiv IM IQ σ x).range ⊔
      (((tangentSpaceCast IQ (f y) (σ x)).toContinuousLinearMap).comp
        (mfderiv IS IQ f y)).range = ⊤) :
    IsLocalHomeomorphOn (pontryaginThomSphereMap h.isOpenEmbedding s₀ ∘ σ) {x} := by
  rw [coe_pontryaginThomSphereMap, comp_assoc]
  exact (onePointHomeomorphSphere k s₀).isLocalHomeomorph.isLocalHomeomorphOn.comp
    (h.isLocalHomeomorphOn_pontryaginThomCollapse_comp_of_transverse hτ hs hσ hIx hn
      (by rw [hdim, Module.finrank_fin_fun]) hy htrans) (mapsTo_univ _ _)

end Sphere

section Degree

variable {ES : Type*} [NormedAddCommGroup ES] [NormedSpace ℝ ES] {HS : Type*}
  [TopologicalSpace HS] {IS : ModelWithCorners ℝ ES HS} {S : Type} [TopologicalSpace S]
  [ChartedSpace HS S] [CompactSpace S]
  {EQ : Type*} [NormedAddCommGroup EQ] [NormedSpace ℝ EQ] {HQ : Type*} [TopologicalSpace HQ]
  {IQ : ModelWithCorners ℝ EQ HQ} {Q : Type} [TopologicalSpace Q] [ChartedSpace HQ Q] [T2Space Q]
  {n : WithTop ℕ∞} {k : ℕ} {f : S → Q} {τ : S × (Fin k → ℝ) → Q}
  {M E : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) n M]

/-- **A smooth map meeting the core once, transversely, has collapse of degree `±1`.** Let
`σ : M → Q` be a map from a compact oriented `k`-manifold, `k ≥ 1`, which meets the core of a
framed tube with fibre `ℝᵏ` in the single point `x`, with `σ x = f y`. If the tube is a `C^n`
local diffeomorphism at `(y, 0)`, `1 ≤ n`, and `σ` is `C^n` near `x` and transverse to `f`
there, then the composite of `σ` with the Pontryagin–Thom collapse onto `Sᵏ` has degree `1` or
`-1`. -/
theorem degree_pontryaginThomSphereMap_comp_eq_one_or_eq_neg_one_of_transverse
    (o : HomologicalOrientation M E k)
    (o' : HomologicalOrientation (Metric.sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1)
      (EuclideanSpace ℝ (Fin k)) k)
    (hE : Module.finrank ℝ E = k) (h : IsFramedTube f τ)
    (s₀ : Metric.sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) (hk : 1 ≤ k) (σ : C(M, Q))
    {x : M} (hx : σ ⁻¹' range f = {x}) {y : S}
    (hτ : IsLocalDiffeomorphAt (IS.prod 𝓘(ℝ, Fin k → ℝ)) IQ n τ (y, 0))
    {s : Set M} (hs : s ∈ 𝓝 x) (hσ : ContMDiffOn 𝓘(ℝ, E) IQ n σ s) (hn : 1 ≤ n) (hy : f y = σ x)
    (htrans : (mfderiv 𝓘(ℝ, E) IQ σ x).range ⊔
      (((tangentSpaceCast IQ (f y) (σ x)).toContinuousLinearMap).comp
        (mfderiv IS IQ f y)).range = ⊤) :
    o.degree o' hE ((pontryaginThomSphereMap h.isOpenEmbedding s₀).comp σ) = 1 ∨
      o.degree o' hE ((pontryaginThomSphereMap h.isOpenEmbedding s₀).comp σ) = -1 :=
  h.degree_pontryaginThomSphereMap_comp_eq_one_or_eq_neg_one o o' hE s₀ hk σ hx
    (h.isLocalHomeomorphOn_pontryaginThomSphereMap_comp_of_transverse s₀ hτ hs hσ
      (BoundarylessManifold.isInteriorPoint) hn hE hy htrans)

end Degree

end IsFramedTube

end TauCeti
