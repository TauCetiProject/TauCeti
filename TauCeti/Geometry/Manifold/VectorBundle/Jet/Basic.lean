/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Jet.Symmetric
public import TauCeti.Geometry.Manifold.VectorBundle.FirstJet.Basic

/-!
# The bundle of `r`-jets of a vector bundle

For a `C^r` vector bundle `V → M` with model fibre `F` over a boundaryless `C^r` manifold
modelled on `E`, over `ℝ` or `ℂ`, the jet bundle `JᵣV` records the value and the derivatives up
to order `r` of local sections. We construct it as a vector bundle with model fibre the symmetric
`r`-jets `TauCeti.SymmetricJet 𝕜 E F r`, the tuples `(A₀, …, Aᵣ)` of symmetric continuous
multilinear maps `Aᵢ : E [×i]→L[𝕜] F`. Over the domain of the preferred chart `φᵢ` of `M` and
the preferred trivialization `eᵢ` of `V` at a point `i`, an `r`-jet at `y` is the tuple of
iterated derivatives at `φᵢ y` of a local representative `z ↦ eᵢ (s (φᵢ⁻¹ z))` of a section
`s`. Changing from `i` to `j` transforms these by the higher-order chain and product rules for the
coordinate change of `V` and the change of charts, `TauCeti.symmetricJetCoordChange`.

For `r = 1` a fibre element corresponds to an element of the fibre of the first-jet bundle
`TauCeti.FirstJetBundle`, a value and a derivative, up to the identifications of `E [×0]→L[𝕜] F`
with `F` and of `E [×1]→L[𝕜] F` with `E →L[𝕜] F`. This file reuses its chart domains
`TauCeti.FirstJetBundle.baseSet`, coordinate changes of `V` written in charts
`TauCeti.FirstJetBundle.fiberCoordChange` and local representatives
`TauCeti.FirstJetBundle.localRep`. Iterated derivatives are taken on the whole model space, which
is why the base is assumed boundaryless.

## Main definitions and results

* `TauCeti.JetBundle.coordChange`: the coordinate changes of `r`-jets. They satisfy the identity
  and cocycle laws (`TauCeti.JetBundle.coordChange_self_apply`,
  `TauCeti.JetBundle.coordChange_comp_apply`), and they are `C^n` when `V` and `M` are `C^(n+r)`
  (`TauCeti.JetBundle.contMDiffOn_coordChange`).
* `TauCeti.jetBundleCore` and `TauCeti.JetBundle`: the vector bundle core and the jet bundle
  itself, a `C^n` vector bundle when `V` and `M` are `C^(n+r)`
  (`TauCeti.JetBundle.contMDiffVectorBundle`), smooth when they are.
* `TauCeti.JetBundle.jet`: the `r`-jet `jʳs(x)` of a section. For a section that is `C^r` at the
  base point it is the tuple of iterated derivatives of the local representative at `x`
  (`TauCeti.JetBundle.toJets_jet`), and in every chart it is the tuple of iterated derivatives of
  the local representative in that chart (`TauCeti.JetBundle.toJets_trivializationAt_jet`). The
  jet of a `C^(n+r)` section is a `C^n` section of `JᵣV` (`TauCeti.JetBundle.contMDiff_jet`), and
  every `r`-jet is the jet of a section, `C^n` at the base point for any `n`
  (`TauCeti.JetBundle.exists_contMDiffAt_jet_eq`) and `C^n` near it when `M` and `V` are `C^n`
  (`TauCeti.JetBundle.exists_contMDiffOn_jet_eq`). The jet is local
  (`TauCeti.JetBundle.jet_congr_of_eventuallyEq`), linear on sections that are `C^r` at the base
  point (`TauCeti.JetBundle.jet_add`, `TauCeti.JetBundle.jet_smul`), and vanishes exactly when the
  derivatives of order at most `r` of the local representative do
  (`TauCeti.JetBundle.jet_eq_zero_iff_iteratedFDeriv_localRep`).

## References

* I. Kolář, P. W. Michor and J. Slovák, *Natural Operations in Differential Geometry*,
  §§12.2–12.5 and 12.16–12.17.
-/

public section

noncomputable section

open Bundle Set Filter
open scoped Manifold Topology ContDiff

namespace TauCeti

open SymmetricJet
open FirstJetBundle (mem_baseSet_iff contDiffAt_fiberCoordChange contDiffAt_localRep
  contDiffAt_ext_coord_change_of_mem_baseSet)

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners 𝕜 E H) {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  (V : M → Type*) [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommMonoid (V x)]
  [∀ x, Module 𝕜 (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle 𝕜 F V]
  (r : ℕ)

namespace JetBundle

/-- The change of `r`-jet coordinates at `y` from the chart and trivialization at `i` to the ones
at `j`: the coordinate change of symmetric jets along the change of charts from `j` to `i` and the
coordinate change of `V` from `i` to `j`, written in the chart at `j`. -/
def coordChange (i j y : M) : SymmetricJet 𝕜 E F r →L[𝕜] SymmetricJet 𝕜 E F r :=
  symmetricJetCoordChange r (extChartAt I i ∘ (extChartAt I j).symm)
    (FirstJetBundle.fiberCoordChange I F V i j) (extChartAt I j y)

/-- Unfolding the coordinate change of `r`-jets. -/
theorem coordChange_def (i j y : M) :
    coordChange I F V r i j y = symmetricJetCoordChange r (extChartAt I i ∘ (extChartAt I j).symm)
      (FirstJetBundle.fiberCoordChange I F V i j) (extChartAt I j y) :=
  (rfl)

variable {I F V r}

variable [I.Boundaryless]

/-- The `r`-jet coordinate change from a chart to itself is the identity. -/
theorem coordChange_self_apply {i y : M} (hy : y ∈ FirstJetBundle.baseSet (H := H) F V i)
    (A : SymmetricJet 𝕜 E F r) : coordChange I F V r i i y A = A := by
  have hy' := FirstJetBundle.mem_extChartAt_source_of_mem_baseSet I hy
  -- Near the image of `y`, the change of charts is the identity and the coordinate change of `V`
  -- is the identity map of `F`.
  have hh : extChartAt I i ∘ (extChartAt I i).symm =ᶠ[𝓝 (extChartAt I i y)] id := by
    filter_upwards [extChartAt_target_mem_nhds' ((extChartAt I i).map_source hy')] with z hz
    exact (extChartAt I i).right_inv hz
  have hg : FirstJetBundle.fiberCoordChange I F V i i =ᶠ[𝓝 (extChartAt I i y)]
      fun _ ↦ ContinuousLinearMap.id 𝕜 F := by
    filter_upwards [FirstJetBundle.eventually_extChartAt_symm_mem_baseSet_nhds I hy
      ((mem_baseSet_iff F V).1 hy).2] with z hz
    ext w
    rw [FirstJetBundle.fiberCoordChange_apply]
    exact (trivializationAt F V i).coordChangeL_same_apply 𝕜
      ((mem_baseSet_iff F V).1 hz).1 w
  rw [coordChange_def, symmetricJetCoordChange_congr hh hg, symmetricJetCoordChange_id,
    ContinuousLinearMap.id_apply]

section Laws

variable [IsManifold I r M] [ContMDiffVectorBundle r F V I]

/-- If the coordinate maps of `V` and `M` are `C^r`, the coordinate change of `r`-jets is the
coordinate change of jets of the local representatives. -/
theorem toJets_coordChange {i j y : M} (hi : y ∈ FirstJetBundle.baseSet (H := H) F V i)
    (hj : y ∈ FirstJetBundle.baseSet (H := H) F V j) (A : SymmetricJet 𝕜 E F r) :
    toJets 𝕜 E F r (coordChange I F V r i j y A) =
      linearJetCoordChange r (extChartAt I i ∘ (extChartAt I j).symm)
        (FirstJetBundle.fiberCoordChange I F V i j) (extChartAt I j y) (toJets 𝕜 E F r A) :=
  toJets_symmetricJetCoordChange (n := r)
    (contDiffAt_ext_coord_change_of_mem_baseSet I hi hj)
    (contDiffAt_fiberCoordChange ((mem_baseSet_iff F V).1 hi).1 hj) (by simp) A

/-- **Cocycle law for `r`-jet coordinate changes**. -/
theorem coordChange_comp_apply {i j k y : M} (hi : y ∈ FirstJetBundle.baseSet (H := H) F V i)
    (hj : y ∈ FirstJetBundle.baseSet (H := H) F V j)
    (hk : y ∈ FirstJetBundle.baseSet (H := H) F V k) (A : SymmetricJet 𝕜 E F r) :
    coordChange I F V r j k y (coordChange I F V r i j y A) = coordChange I F V r i k y A := by
  have hk' := FirstJetBundle.mem_extChartAt_source_of_mem_baseSet I hk
  -- The point of the chart at `j` is the change of charts of the point of the chart at `k`.
  have hjk : extChartAt I j y = (extChartAt I j ∘ (extChartAt I k).symm) (extChartAt I k y) := by
    rw [Function.comp_apply, (extChartAt I k).left_inv hk']
  have hhij : ContDiffAt 𝕜 r (extChartAt I i ∘ (extChartAt I j).symm)
      ((extChartAt I j ∘ (extChartAt I k).symm) (extChartAt I k y)) := by
    rw [← hjk]
    exact contDiffAt_ext_coord_change_of_mem_baseSet I hi hj
  have hgij : ContDiffAt 𝕜 r (FirstJetBundle.fiberCoordChange I F V i j)
      ((extChartAt I j ∘ (extChartAt I k).symm) (extChartAt I k y)) := by
    rw [← hjk]
    exact contDiffAt_fiberCoordChange ((mem_baseSet_iff F V).1 hi).1 hj
  -- Near the image of `y` in the chart at `k`, the composite coordinate changes are the ones
  -- from `i` to `k`.
  have hk₂ := ((mem_baseSet_iff F V).1 hk).2
  have hnear := FirstJetBundle.eventually_extChartAt_symm_mem_baseSet_nhds I hj hk₂
  have hnear_i := FirstJetBundle.eventually_extChartAt_symm_mem_baseSet_nhds I hi hk₂
  have hnear_k := FirstJetBundle.eventually_extChartAt_symm_mem_baseSet_nhds I hk hk₂
  have hh : (extChartAt I i ∘ (extChartAt I j).symm) ∘ (extChartAt I j ∘ (extChartAt I k).symm)
      =ᶠ[𝓝 (extChartAt I k y)] extChartAt I i ∘ (extChartAt I k).symm := by
    filter_upwards [hnear] with z hz
    simp only [Function.comp_apply,
      (extChartAt I j).left_inv (FirstJetBundle.mem_extChartAt_source_of_mem_baseSet I hz)]
  have hg : (fun z ↦ (FirstJetBundle.fiberCoordChange I F V j k z).comp
        (FirstJetBundle.fiberCoordChange I F V i j ((extChartAt I j ∘ (extChartAt I k).symm) z)))
      =ᶠ[𝓝 (extChartAt I k y)] FirstJetBundle.fiberCoordChange I F V i k := by
    filter_upwards [hnear, hnear_i, hnear_k] with z hzj hzi hzk
    ext w
    simp only [FirstJetBundle.fiberCoordChange_apply, Function.comp_apply,
      ContinuousLinearMap.coe_comp,
      (extChartAt I j).left_inv (FirstJetBundle.mem_extChartAt_source_of_mem_baseSet I hzj)]
    exact (trivializationAt F V i).coordChangeL_coordChangeL_apply 𝕜 _ _
      ((mem_baseSet_iff F V).1 hzi).1 ((mem_baseSet_iff F V).1 hzj).1
      ((mem_baseSet_iff F V).1 hzk).1 w
  rw [coordChange_def, coordChange_def, hjk,
    symmetricJetCoordChange_comp hhij hgij
      (contDiffAt_ext_coord_change_of_mem_baseSet I hj hk)
      (contDiffAt_fiberCoordChange ((mem_baseSet_iff F V).1 hj).1 hk) (by simp),
    symmetricJetCoordChange_congr hh hg, ← coordChange_def]

end Laws

/-- The `r`-jet coordinate changes of a `C^(n+r)` vector bundle over a `C^(n+r)` manifold are
`C^n`. -/
theorem contMDiffOn_coordChange {n : ℕ∞ω} [IsManifold I (n + r) M]
    [ContMDiffVectorBundle (n + r) F V I] (i j : M) :
    ContMDiffOn I 𝓘(𝕜, SymmetricJet 𝕜 E F r →L[𝕜] SymmetricJet 𝕜 E F r) n
      (coordChange I F V r i j)
      (FirstJetBundle.baseSet (H := H) F V i ∩ FirstJetBundle.baseSet (H := H) F V j) := by
  have : IsManifold I n M := .of_le (n := n + r) le_self_add
  set U := FirstJetBundle.baseSet (H := H) F V i ∩ FirstJetBundle.baseSet (H := H) F V j
  -- The domain of the coordinate change, read in the chart at `j`, is open.
  set T := (extChartAt I j).target ∩ (extChartAt I j).symm ⁻¹' U
  have hT : IsOpen T := (continuousOn_extChartAt_symm j).isOpen_inter_preimage
    (isOpen_extChartAt_target j) ((FirstJetBundle.isOpen_baseSet F V i).inter
      (FirstJetBundle.isOpen_baseSet F V j))
  have hTpt : ∀ z ∈ T, extChartAt I j ((extChartAt I j).symm z) = z := fun z hz ↦
    (extChartAt I j).right_inv hz.1
  have hh : ContDiffOn 𝕜 (n + r) (extChartAt I i ∘ (extChartAt I j).symm) T := fun z hz ↦ by
    rw [← hTpt z hz]
    exact (contDiffAt_ext_coord_change_of_mem_baseSet I hz.2.1 hz.2.2).contDiffWithinAt
  have hg : ContDiffOn 𝕜 (n + r) (FirstJetBundle.fiberCoordChange I F V i j) T := fun z hz ↦ by
    rw [← hTpt z hz]
    exact (contDiffAt_fiberCoordChange ((mem_baseSet_iff F V).1 hz.2.1).1
      hz.2.2).contDiffWithinAt
  have hΨ := ContDiffOn.symmetricJetCoordChange hT hh hg le_rfl
  have hmaps : MapsTo (extChartAt I j) U T := fun y hy ↦ by
    have hy' := FirstJetBundle.mem_extChartAt_source_of_mem_baseSet I hy.2
    exact ⟨(extChartAt I j).map_source hy', by rwa [mem_preimage, (extChartAt I j).left_inv hy']⟩
  exact (contMDiffOn_iff_contDiffOn.2 hΨ).comp (contMDiffOn_extChartAt.mono fun y hy ↦
    ((mem_baseSet_iff F V).1 hy.2).2)
    hmaps

end JetBundle

variable [I.Boundaryless]

section

variable [IsManifold I r M] [ContMDiffVectorBundle r F V I]

/-- The vector bundle core of the bundle of `r`-jets of `V`, indexed by the points of `M`. Over
the chart at `i`, an `r`-jet is described by the iterated derivatives up to order `r` of the local
representative of a section in the chart and the preferred trivialization of `V` at `i`. -/
def jetBundleCore : VectorBundleCore 𝕜 M (SymmetricJet 𝕜 E F r) M where
  baseSet := FirstJetBundle.baseSet F V
  isOpen_baseSet := FirstJetBundle.isOpen_baseSet F V
  indexAt := id
  mem_baseSet_at := FirstJetBundle.mem_baseSet_self F V
  coordChange := JetBundle.coordChange I F V r
  coordChange_self _ _ hy v := JetBundle.coordChange_self_apply hy v
  continuousOn_coordChange i j := by
    have : IsManifold I (0 + r) M := by simpa
    have : ContMDiffVectorBundle (0 + r) F V I := by simpa
    exact (JetBundle.contMDiffOn_coordChange (n := 0) i j).continuousOn
  coordChange_comp _ _ _ _ hy v := JetBundle.coordChange_comp_apply hy.1.1 hy.1.2 hy.2 v

/-- The `r`-jet chart domains are the domains of `FirstJetBundle.baseSet`. -/
@[simp]
theorem jetBundleCore_baseSet :
    (jetBundleCore I F V r).baseSet = FirstJetBundle.baseSet (H := H) F V := (rfl)

/-- The `r`-jet chart at a point is the one indexed by that point. -/
@[simp]
theorem jetBundleCore_indexAt (x : M) : (jetBundleCore I F V r).indexAt x = x := (rfl)

/-- The coordinate changes of `jetBundleCore` are `JetBundle.coordChange`. -/
@[simp]
theorem jetBundleCore_coordChange :
    (jetBundleCore I F V r).coordChange = JetBundle.coordChange I F V r := (rfl)

/-- The bundle `JᵣV` of `r`-jets of a vector bundle `V`. Its fibre over `x` is the space of
symmetric `r`-jets `SymmetricJet 𝕜 E F r`, read as the iterated derivatives up to order `r` of the
local representative of a section in the preferred chart of `M` and the preferred trivialization
of `V` at `x`. -/
abbrev JetBundle : M → Type _ :=
  (jetBundleCore I F V r).Fiber

end

/-- The vector bundle core of the bundle of `r`-jets of a `C^(n+r)` vector bundle over a
`C^(n+r)` manifold has `C^n` coordinate changes. -/
theorem jetBundleCore_isContMDiff {n : ℕ∞ω} [IsManifold I (n + r) M]
    [ContMDiffVectorBundle (n + r) F V I] :
    haveI : IsManifold I r M := .of_le (n := n + r) le_add_self
    haveI : ContMDiffVectorBundle r F V I := .of_le (n := n + r) le_add_self
    (jetBundleCore I F V r).IsContMDiff I n :=
  ⟨JetBundle.contMDiffOn_coordChange⟩

/-- The bundle of `r`-jets of a `C^(n+r)` vector bundle over a `C^(n+r)` manifold is a `C^n`
vector bundle. -/
theorem JetBundle.contMDiffVectorBundle {n : ℕ∞ω} [IsManifold I (n + r) M]
    [ContMDiffVectorBundle (n + r) F V I] :
    haveI : IsManifold I r M := .of_le (n := n + r) le_add_self
    haveI : ContMDiffVectorBundle r F V I := .of_le (n := n + r) le_add_self
    ContMDiffVectorBundle n (SymmetricJet 𝕜 E F r) (JetBundle I F V r) I := by
  have : IsManifold I r M := .of_le (n := n + r) le_add_self
  have : ContMDiffVectorBundle r F V I := .of_le (n := n + r) le_add_self
  have := jetBundleCore_isContMDiff I F V r (n := n)
  exact (jetBundleCore I F V r).instContMDiffVectorBundle

/-- The bundle of `r`-jets of a smooth vector bundle over a smooth manifold is smooth. -/
instance [IsManifold I ∞ M] [ContMDiffVectorBundle ∞ F V I] :
    ContMDiffVectorBundle ∞ (SymmetricJet 𝕜 E F r) (JetBundle I F V r) I := by
  have h : (∞ : ℕ∞ω) + r = ∞ := by exact_mod_cast top_add (r : ℕ∞)
  have : IsManifold I (∞ + r) M := by rw [h]; infer_instance
  have : ContMDiffVectorBundle (∞ + r) F V I := by rw [h]; infer_instance
  exact JetBundle.contMDiffVectorBundle I F V r

namespace JetBundle

variable {I F V r}

section Jet

variable [IsManifold I r M] [ContMDiffVectorBundle r F V I]

variable (I F r) in
/-- The `r`-jet `jʳs(x)` of a section `s` of `V` at `x`: the iterated derivatives up to order `r`
at `x` of the local representative of `s` in the chart and trivialization at `x`
(`TauCeti.JetBundle.toJets_jet`). They are symmetrized, which does nothing when `s` is `C^r` at
`x`, so that `jʳs(x)` is a symmetric jet whatever the regularity of `s`. -/
def jet (s : ∀ x, V x) (x : M) : JetBundle I F V r x :=
  symmetrizeJets 𝕜 E F r fun k : Fin (r + 1) ↦
    iteratedFDeriv 𝕜 k.val (FirstJetBundle.localRep I F s x) (extChartAt I x x)

/-- The `r`-jet of a section that is `C^r` at `x` is the tuple of iterated derivatives at `x` of
its local representative in the chart and trivialization at `x`. -/
theorem toJets_jet {s : ∀ x, V x} {x : M}
    (hs : ContMDiffAt I (I.prod 𝓘(𝕜, F)) r (fun x ↦ TotalSpace.mk' F x (s x)) x) :
    toJets 𝕜 E F r (jet I F r s x) = fun k : Fin (r + 1) ↦
      iteratedFDeriv 𝕜 k.val (FirstJetBundle.localRep I F s x) (extChartAt I x x) := by
  rw [jet]
  exact toJets_symmetrizeJets_iteratedFDeriv
    (contDiffAt_localRep I F hs (FirstJetBundle.mem_baseSet_self F V x)) (by simp)

/-- **The `r`-jet vanishes exactly when the derivatives do.** The `r`-jet of a section that is
`C^r` at `x` is zero if and only if its local representative in the chart and trivialization at
`x` has vanishing derivatives of every order at most `r` at the image of `x`. -/
theorem jet_eq_zero_iff_iteratedFDeriv_localRep {s : ∀ x, V x} {x : M}
    (hs : ContMDiffAt I (I.prod 𝓘(𝕜, F)) r (fun x ↦ TotalSpace.mk' F x (s x)) x) :
    jet I F r s x = 0 ↔ ∀ k ≤ r,
      iteratedFDeriv 𝕜 k (FirstJetBundle.localRep I F s x) (extChartAt I x x) = 0 := by
  -- The fibre `JetBundle I F V r x` is by definition the model fibre `SymmetricJet 𝕜 E F r`, so
  -- `toJets` applies to `r`-jets; its injectivity turns the equation into one of tuples.
  refine (toJets_injective.eq_iff (a := jet I F r s x) (b := 0)).symm.trans ?_
  rw [map_zero, toJets_jet hs, funext_iff]
  exact ⟨fun h k hk ↦ h ⟨k, Nat.lt_succ_of_le hk⟩, fun h k ↦ h k k.is_le⟩

/-- The `r`-jet of a section only depends on its local representative near the image of `x`. -/
private theorem jet_eq_symmetrizeJets_of_eventuallyEq {s : ∀ x, V x} {x : M} {g : E → F}
    (hg : FirstJetBundle.localRep I F s x =ᶠ[𝓝 (extChartAt I x x)] g) :
    jet I F r s x = symmetrizeJets 𝕜 E F r fun k : Fin (r + 1) ↦
      iteratedFDeriv 𝕜 k.val g (extChartAt I x x) := by
  rw [jet]
  congr 1
  funext k
  exact (hg.iteratedFDeriv 𝕜 k.val).eq_of_nhds

/-- **The `r`-jet is local**: two sections that agree near `x` have the same `r`-jet at `x`. -/
theorem jet_congr_of_eventuallyEq {s t : ∀ x, V x} {x : M} (hst : ∀ᶠ y in 𝓝 x, s y = t y) :
    jet I F r s x = jet I F r t x := by
  have h := (continuousAt_extChartAt_symm (I := I) x).tendsto
  rw [extChartAt_to_inv] at h
  have hloc : FirstJetBundle.localRep I F s x =ᶠ[𝓝 (extChartAt I x x)]
      FirstJetBundle.localRep I F t x := by
    filter_upwards [h.eventually hst] with z hz
    simp only [FirstJetBundle.localRep_apply, hz]
  rw [jet_eq_symmetrizeJets_of_eventuallyEq hloc, jet]

variable (I F V r) in
/-- The `r`-jet of the zero section is zero. -/
@[simp]
theorem jet_zero (x : M) : jet I F r (0 : ∀ x, V x) x = 0 := by
  rw [jet_eq_symmetrizeJets_of_eventuallyEq
    (FirstJetBundle.localRep_zero_eventuallyEq I F (FirstJetBundle.mem_baseSet_self F V x))]
  simp only [iteratedFDeriv_zero, Pi.zero_apply]
  -- `symmetrizeJets` is linear, with values in the model fibre of `JetBundle I F V r`.
  exact map_zero (symmetrizeJets 𝕜 E F r)

/-- **The `r`-jet is additive** on sections that are `C^r` at the base point. -/
theorem jet_add {s t : ∀ x, V x} {x : M}
    (hs : ContMDiffAt I (I.prod 𝓘(𝕜, F)) r (fun x ↦ TotalSpace.mk' F x (s x)) x)
    (ht : ContMDiffAt I (I.prod 𝓘(𝕜, F)) r (fun x ↦ TotalSpace.mk' F x (t x)) x) :
    jet I F r (s + t) x = jet I F r s x + jet I F r t x := by
  have hx := FirstJetBundle.mem_baseSet_self (H := H) F V x
  rw [jet_eq_symmetrizeJets_of_eventuallyEq (FirstJetBundle.localRep_add_eventuallyEq I F s t hx)]
  refine (congrArg (symmetrizeJets 𝕜 E F r) (funext fun k ↦ ?_)).trans (map_add _ _ _)
  have hk : (k.val : ℕ∞ω) ≤ r := by exact_mod_cast k.is_le
  exact iteratedFDeriv_add_apply ((contDiffAt_localRep I F hs hx).of_le hk)
    ((contDiffAt_localRep I F ht hx).of_le hk)

/-- **The `r`-jet is homogeneous** on sections that are `C^r` at the base point. -/
theorem jet_smul (c : 𝕜) {s : ∀ x, V x} {x : M}
    (hs : ContMDiffAt I (I.prod 𝓘(𝕜, F)) r (fun x ↦ TotalSpace.mk' F x (s x)) x) :
    jet I F r (c • s) x = c • jet I F r s x := by
  have hx := FirstJetBundle.mem_baseSet_self (H := H) F V x
  rw [jet_eq_symmetrizeJets_of_eventuallyEq
    (FirstJetBundle.localRep_const_smul_eventuallyEq I F c s hx)]
  refine (congrArg (symmetrizeJets 𝕜 E F r) (funext fun k ↦ ?_)).trans (map_smul _ c _)
  exact iteratedFDeriv_const_smul_apply
    ((contDiffAt_localRep I F hs hx).of_le (by exact_mod_cast k.is_le))

/-- The preferred trivialization of `JᵣV` at `i` reads an `r`-jet in the chart and trivialization
of `V` at `i`. -/
theorem trivializationAt_apply_snd (i : M)
    (p : TotalSpace (SymmetricJet 𝕜 E F r) (JetBundle I F V r)) :
    (trivializationAt (SymmetricJet 𝕜 E F r) (JetBundle I F V r) i p).2 =
      coordChange I F V r p.proj i p.proj p.snd := by
  rw [VectorBundleCore.trivializationAt, ← VectorBundleCore.localTrivAt_def,
    VectorBundleCore.localTriv_apply, jetBundleCore_indexAt, jetBundleCore_indexAt,
    jetBundleCore_coordChange]

/-- **The `r`-jet in an arbitrary chart.** In the preferred trivialization of `JᵣV` at `i`, the
`r`-jet of a section that is `C^r` at `y` is the tuple of iterated derivatives at the image of `y`
of the local representative of the section in the chart and trivialization at `i`. -/
theorem toJets_trivializationAt_jet {s : ∀ x, V x} {y : M}
    (hs : ContMDiffAt I (I.prod 𝓘(𝕜, F)) r (fun x ↦ TotalSpace.mk' F x (s x)) y) {i : M}
    (hi : y ∈ FirstJetBundle.baseSet (H := H) F V i) :
    toJets 𝕜 E F r (trivializationAt (SymmetricJet 𝕜 E F r) (JetBundle I F V r) i
        ⟨y, jet I F r s y⟩).2 = fun k : Fin (r + 1) ↦
      iteratedFDeriv 𝕜 k.val (FirstJetBundle.localRep I F s i) (extChartAt I i y) := by
  have hy := FirstJetBundle.mem_baseSet_self (H := H) F V y
  have hyi := FirstJetBundle.mem_extChartAt_source_of_mem_baseSet I hi
  -- The point of the chart at `y` is the change of charts of the point of the chart at `i`.
  have hx : (extChartAt I y ∘ (extChartAt I i).symm) (extChartAt I i y) = extChartAt I y y := by
    rw [Function.comp_apply, (extChartAt I i).left_inv hyi]
  have hrep : ContDiffAt 𝕜 r (FirstJetBundle.localRep I F s y)
      ((extChartAt I y ∘ (extChartAt I i).symm) (extChartAt I i y)) := by
    rw [hx]
    exact contDiffAt_localRep I F hs hy
  have hjet : jet I F r s y = mk (fun k : Fin (r + 1) ↦ iteratedFDeriv 𝕜 k.val
      (FirstJetBundle.localRep I F s y) ((extChartAt I y ∘ (extChartAt I i).symm)
        (extChartAt I i y))) (iteratedFDeriv_mem_symmetricJets hrep (by simp)) := by
    refine toJets_injective ?_
    rw [toJets_jet hs, toJets_mk, hx]
  rw [trivializationAt_apply_snd, coordChange_def, hjet,
    toJets_symmetricJetCoordChange_iteratedFDeriv hrep (by simp)
      (contDiffAt_ext_coord_change_of_mem_baseSet I hy hi)
      (contDiffAt_fiberCoordChange ((mem_baseSet_iff F V).1 hy).1 hi)]
  -- Near the image of `y`, the local representative at `i` is the transformed local
  -- representative at `y`.
  have hloc := FirstJetBundle.localRep_eventuallyEq_fiberCoordChange_nhds I F s hy hi
  funext k
  exact ((hloc.iteratedFDeriv 𝕜 k.val).eq_of_nhds).symm

variable (I F) in
/-- The section of `V` that reads, in the chart and trivialization at `x`, as the Taylor
polynomial at `x` of the `r`-jet `A`. -/
private def taylorSection (x : M) (A : JetBundle I F V r x) (y : M) : V y :=
  (trivializationAt F V x).symm y
    (finiteJetPolynomial r (toJets 𝕜 E F r A) (extChartAt I x x) (extChartAt I x y))

/-- In the trivialization at `x`, the section `taylorSection I F x A` reads as the Taylor
polynomial of `A` in the chart at `x`. -/
private theorem trivializationAt_taylorSection {x y : M} (A : JetBundle I F V r x)
    (hy : y ∈ (trivializationAt F V x).baseSet) :
    (trivializationAt F V x ⟨y, taylorSection I F x A y⟩).2 =
      finiteJetPolynomial r (toJets 𝕜 E F r A) (extChartAt I x x) (extChartAt I x y) := by
  rw [taylorSection, (trivializationAt F V x).apply_mk_symm hy]

/-- The section `taylorSection I F x A` is `C^n` at `x` for every `n`. -/
private theorem contMDiffAt_taylorSection {n : ℕ∞ω} (x : M) (A : JetBundle I F V r x) :
    ContMDiffAt I (I.prod 𝓘(𝕜, F)) n (fun y ↦ TotalSpace.mk' F y (taylorSection I F x A y)) x := by
  have hx := FirstJetBundle.mem_baseSet_self (H := H) F V x
  rw [contMDiffAt_section_iff]
  exact ((contDiff_finiteJetPolynomial r _ _).contMDiff.contMDiffAt.comp x
    contMDiffAt_extChartAt).congr_of_eventuallyEq
    (eventually_of_mem ((trivializationAt F V x).open_baseSet.mem_nhds
      ((mem_baseSet_iff F V).1 hx).1) fun y hy ↦ trivializationAt_taylorSection A hy)

/-- The `r`-jet at `x` of the section `taylorSection I F x A` is `A`. -/
private theorem jet_taylorSection (x : M) (A : JetBundle I F V r x) :
    jet I F r (taylorSection I F x A) x = A := by
  refine toJets_injective ?_
  have hx := FirstJetBundle.mem_baseSet_self (H := H) F V x
  -- Near the image of `x`, the local representative is the Taylor polynomial of `A`.
  have hrep : FirstJetBundle.localRep I F (taylorSection I F x A) x
      =ᶠ[𝓝 (extChartAt I x x)] finiteJetPolynomial r (toJets 𝕜 E F r A) (extChartAt I x x) := by
    filter_upwards [FirstJetBundle.eventually_extChartAt_symm_mem_baseSet_nhds I hx
      ((mem_baseSet_iff F V).1 hx).2, extChartAt_target_mem_nhds x] with z hz hzt
    rw [FirstJetBundle.localRep_apply,
      trivializationAt_taylorSection A ((mem_baseSet_iff F V).1 hz).1,
      (extChartAt I x).right_inv hzt]
  rw [toJets_jet (contMDiffAt_taylorSection x A)]
  funext k
  rw [(hrep.iteratedFDeriv 𝕜 k.val).eq_of_nhds]
  exact iteratedFDeriv_finiteJetPolynomial_self r _ _ k (mem_symmetricJets.1 (toJets_mem A) k)

/-- **Every `r`-jet is the `r`-jet of a section that is `C^n` at the base point.** In the chart
and trivialization at `x`, the section is the Taylor polynomial of the jet. -/
theorem exists_contMDiffAt_jet_eq {n : ℕ∞ω} (x : M) (A : JetBundle I F V r x) :
    ∃ s : ∀ y, V y, ContMDiffAt I (I.prod 𝓘(𝕜, F)) n (fun y ↦ TotalSpace.mk' F y (s y)) x ∧
      jet I F r s x = A :=
  ⟨taylorSection I F x A, contMDiffAt_taylorSection x A, jet_taylorSection x A⟩

/-- **Every `r`-jet is the `r`-jet of a section that is `C^n` near the base point**, when `M` and
`V` are `C^n`. The section is `C^n` on the domain `TauCeti.FirstJetBundle.baseSet F V x` of the
chart and trivialization at `x`, an open neighbourhood of `x`, and in these coordinates it is the
Taylor polynomial of the jet. -/
theorem exists_contMDiffOn_jet_eq {n : ℕ∞ω} [IsManifold I n M] [ContMDiffVectorBundle n F V I]
    (x : M) (A : JetBundle I F V r x) :
    ∃ s : ∀ y, V y, ContMDiffOn I (I.prod 𝓘(𝕜, F)) n (fun y ↦ TotalSpace.mk' F y (s y))
      (FirstJetBundle.baseSet (H := H) F V x) ∧ jet I F r s x = A := by
  refine ⟨taylorSection I F x A, ?_, jet_taylorSection x A⟩
  rw [(trivializationAt F V x).contMDiffOn_section_iff (FirstJetBundle.isOpen_baseSet F V x)
    fun y hy ↦ ((mem_baseSet_iff F V).1 hy).1]
  exact ((contDiff_finiteJetPolynomial r _ _).contMDiff.comp_contMDiffOn
    contMDiffOn_extChartAt).mono (fun y hy ↦ ((mem_baseSet_iff F V).1 hy).2) |>.congr
    fun y hy ↦ trivializationAt_taylorSection A ((mem_baseSet_iff F V).1 hy).1

end Jet

/-- **The `r`-jet of a section that is `C^(n+r)` on an open set is `C^n` there.** If a section
`s` of `V` is `C^(n+r)` on an open set `U`, then its `r`-jet is a section of `JᵣV` that is `C^n` on
`U`. -/
theorem contMDiffOn_jet {n : ℕ∞ω} [IsManifold I (n + r) M] [ContMDiffVectorBundle (n + r) F V I]
    {s : ∀ x, V x} {U : Set M} (hU : IsOpen U)
    (hs : ContMDiffOn I (I.prod 𝓘(𝕜, F)) (n + r) (fun x ↦ TotalSpace.mk' F x (s x)) U) :
    haveI : IsManifold I r M := .of_le (n := n + r) le_add_self
    haveI : ContMDiffVectorBundle r F V I := .of_le (n := n + r) le_add_self
    ContMDiffOn I (I.prod 𝓘(𝕜, SymmetricJet 𝕜 E F r)) n
      (fun x ↦ TotalSpace.mk' (SymmetricJet 𝕜 E F r) x (jet I F r s x)) U := by
  have : IsManifold I r M := .of_le (n := n + r) le_add_self
  have : ContMDiffVectorBundle r F V I := .of_le (n := n + r) le_add_self
  intro x₀ hx₀
  have hx₀b := FirstJetBundle.mem_baseSet_self (H := H) F V x₀
  have hrep := contDiffAt_localRep I F (hs.contMDiffAt (hU.mem_nhds hx₀)) hx₀b
  -- In the chart at `x₀`, the jet is the symmetrized tuple of iterated derivatives of the local
  -- representative at `x₀`, a `C^n` function of the chart coordinate.
  set Φ : E → SymmetricJet 𝕜 E F r := fun z ↦ symmetrizeJets 𝕜 E F r fun k : Fin (r + 1) ↦
    iteratedFDeriv 𝕜 k.val (FirstJetBundle.localRep I F s x₀) z
  have hΦ : ContDiffAt 𝕜 n Φ (extChartAt I x₀ x₀) :=
    (symmetrizeJets 𝕜 E F r).contDiff.contDiffAt.comp _ (contDiffAt_pi.2 fun k ↦
      hrep.iteratedFDeriv_right (add_le_add_right (by exact_mod_cast k.is_le) n))
  refine ContMDiffAt.contMDiffWithinAt ((contMDiffAt_section_iff x₀).2 ?_)
  refine (hΦ.contMDiffAt.comp x₀ contMDiffAt_extChartAt).congr_of_eventuallyEq ?_
  filter_upwards [hU.mem_nhds hx₀, (FirstJetBundle.isOpen_baseSet F V x₀).mem_nhds hx₀b]
    with x hxU hxb
  have hsx := ((hs x hxU).contMDiffAt (hU.mem_nhds hxU)).of_le
    (le_add_self : (r : ℕ∞ω) ≤ n + r)
  refine toJets_injective ?_
  rw [toJets_trivializationAt_jet hsx hxb, Function.comp_apply]
  simp only [Φ]
  exact (toJets_symmetrizeJets_iteratedFDeriv (contDiffAt_localRep I F hsx hxb) (by simp)).symm

/-- **The `r`-jet of a `C^(n+r)` section is a `C^n` section of `JᵣV`.** -/
theorem contMDiff_jet {n : ℕ∞ω} [IsManifold I (n + r) M] [ContMDiffVectorBundle (n + r) F V I]
    {s : ∀ x, V x}
    (hs : ContMDiff I (I.prod 𝓘(𝕜, F)) (n + r) fun x ↦ TotalSpace.mk' F x (s x)) :
    haveI : IsManifold I r M := .of_le (n := n + r) le_add_self
    haveI : ContMDiffVectorBundle r F V I := .of_le (n := n + r) le_add_self
    ContMDiff I (I.prod 𝓘(𝕜, SymmetricJet 𝕜 E F r)) n
      fun x ↦ TotalSpace.mk' (SymmetricJet 𝕜 E F r) x (jet I F r s x) := by
  rw [← contMDiffOn_univ] at hs ⊢
  exact contMDiffOn_jet isOpen_univ hs

end JetBundle

end TauCeti
