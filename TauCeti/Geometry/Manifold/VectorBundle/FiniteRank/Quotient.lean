/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Quotient
public import TauCeti.Geometry.Manifold.Quotient.BundleMap
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteRank.Pullback.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteRank.Tensor
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteRank.ExteriorPower

/-!
# `C^m` and holomorphic descent of finite-rank bundle operations over orbit quotients

Let a group `G` act freely and properly discontinuously by `C^n` maps on a `C^n` manifold `M`, with
orbit projection `q = TauCeti.continuousQuotientMk G M : C(M, MulAction.orbitRel.Quotient G M)`,
and let `m ≤ n`. For finite-rank vector-bundle cores `A` and `D` over `M ⧸ G`, this file upgrades
the topological descent in `TauCeti.Topology.VectorBundle.FiniteRank.Quotient` to `C^m` (and, over
`𝓘(ℂ, E)` at `m = n = ∞`, holomorphic) cores, bundle morphisms, bundle equivalences, and sections:

* **Core and bundle-map descent:** `(A.pullback q).core` is `C^m` iff `A.core` is `C^m`
  (`isContMDiff_pullback_continuousQuotientMk_iff`), `orbitRelQuotientDesc a ha` has `C^m`
  total-space map iff `a` does (`contMDiff_totalSpaceMap_orbitRelQuotientDesc_iff`,
  `existsUnique_contMDiff_orbitRelQuotientDesc_iff`), and isomorphisms descend to `C^m` total-space
  diffeomorphisms (`orbitRelQuotientDescIsoDiffeomorph`, `orbitRelQuotientDescDiffeomorph`).
* **`C^m` bundle-map descent and operations:** preserves `C^m` regularity under equivariant pullback
  (`contMDiff_totalSpaceMap_pullbackEquivariant`), dualization
  (`contMDiff_totalSpaceMap_orbitRelQuotientDesc_dualMap`), tensor products
  (`contMDiff_totalSpaceMap_orbitRelQuotientDesc_tensorHom`), exterior powers
  (`contMDiff_totalSpaceMap_orbitRelQuotientDesc_exteriorPower_map`), and determinant lines
  (`contMDiff_totalSpaceMap_orbitRelQuotientDesc_detMap`).
* **`C^m` section descent and operations:** `orbitRelQuotientRec t ht` is `C^m` iff `t` is `C^m` as
  a section of `A.pullback q` (`contMDiff_section_orbitRelQuotientRec_core_iff`), and preserves
  `C^m` regularity under equivariant pullback, bundle-map evaluation, dual pairing, pure tensors,
  exterior powers, and determinant wedges.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Chapter 21.
* Otto Forster, *Lectures on Riemann Surfaces*, §§4–5.
* Daniel Huybrechts, *Complex Geometry: An Introduction*, §2.2.
-/

public section

open Bundle CategoryTheory MulAction TauCeti.MulAction Set Topology VectorBundleCore
open scoped Manifold ContDiff

namespace TauCeti.FiniteRankBundleCore

section BundleMapDescent

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E H M : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M] [ChartedSpace H M] {m n : ℕ∞ω}
  {G : Type*} [Group G] [MulAction G M] [ProperlyDiscontinuousSMul G M]
  [ContinuousConstSMul G M] [IsCancelSMul G M] [T2Space M] [LocallyCompactSpace M]
  [IsManifold I n M] [ContMDiffConstSMul I n G M]

/-- Along the orbit projection of a free properly discontinuous `C^n` action (`m ≤ n`), the
pulled-back core `A.pullback (continuousQuotientMk G M)` is `C^m` if and only if `A` is `C^m`. -/
theorem isContMDiff_pullback_continuousQuotientMk_iff (hm : m ≤ n)
    (A : FiniteRankBundleCore 𝕜 (orbitRel.Quotient G M)) :
    (A.pullback (continuousQuotientMk G M)).core.IsContMDiff I m ↔ A.core.IsContMDiff I m :=
  (isLocalDiffeomorph_quotientMk (I := I) (n := n) (G := G)).isContMDiff_pullback_iff
    Quotient.mk_surjective hm A

/-- **Smooth and holomorphic bundle-map descent for finite-rank cores.** For `m ≤ n`, the descended
morphism `orbitRelQuotientDesc a ha : A ⟶ D` has a `C^m` total-space map if and only if `a` does,
without completeness of `𝕜` or `IsContMDiff` hypotheses on `A` and `D`. -/
theorem contMDiff_totalSpaceMap_orbitRelQuotientDesc_iff (hm : m ≤ n)
    {A D : FiniteRankBundleCore 𝕜 (orbitRel.Quotient G M)}
    (a : A.pullback (continuousQuotientMk G M) ⟶ D.pullback (continuousQuotientMk G M))
    (ha : ∀ (g : G) (x : M), a.fiberMap (g • x) = a.fiberMap x) :
    ContMDiff (I.prod 𝓘(𝕜, Fin A.rank → 𝕜)) (I.prod 𝓘(𝕜, Fin D.rank → 𝕜)) m
        (orbitRelQuotientDesc a ha).totalSpaceMap ↔
      ContMDiff (I.prod 𝓘(𝕜, Fin (A.pullback (continuousQuotientMk G M)).rank → 𝕜))
        (I.prod 𝓘(𝕜, Fin (D.pullback (continuousQuotientMk G M)).rank → 𝕜)) m a.totalSpaceMap := by
  have h := ((isLocalDiffeomorph_quotientMk (I := I) (n := n) (G := G))
    |>.contMDiff_totalSpaceMap_pullbackMap_iff (f := continuousQuotientMk G M)
      Quotient.mk_surjective hm (orbitRelQuotientDesc a ha)).symm
  rwa [pullbackMap_orbitRelQuotientDesc] at h

/-- A `G`-invariant morphism `a : A.pullback (continuousQuotientMk G M) ⟶
D.pullback (continuousQuotientMk G M)` has a `C^m` total-space map (`m ≤ n`) if and only if it is
the pullback of a unique morphism `b : A ⟶ D` with a `C^m` total-space map. -/
theorem existsUnique_contMDiff_orbitRelQuotientDesc_iff (hm : m ≤ n)
    {A D : FiniteRankBundleCore 𝕜 (orbitRel.Quotient G M)}
    (a : A.pullback (continuousQuotientMk G M) ⟶ D.pullback (continuousQuotientMk G M))
    (ha : ∀ (g : G) (x : M), a.fiberMap (g • x) = a.fiberMap x) :
    (∃! b : A ⟶ D, pullbackMap b (continuousQuotientMk G M) = a ∧
        ContMDiff (I.prod 𝓘(𝕜, Fin A.rank → 𝕜)) (I.prod 𝓘(𝕜, Fin D.rank → 𝕜)) m b.totalSpaceMap) ↔
      ContMDiff (I.prod 𝓘(𝕜, Fin (A.pullback (continuousQuotientMk G M)).rank → 𝕜))
        (I.prod 𝓘(𝕜, Fin (D.pullback (continuousQuotientMk G M)).rank → 𝕜)) m a.totalSpaceMap := by
  refine ⟨fun ⟨b, ⟨hb, hcm⟩, _⟩ ↦ ?_, fun hcm ↦ ?_⟩
  · rw [← eq_orbitRelQuotientDesc_iff (ha := ha)] at hb
    subst b
    exact (contMDiff_totalSpaceMap_orbitRelQuotientDesc_iff hm a ha).1 hcm
  · exact ⟨orbitRelQuotientDesc a ha, ⟨pullbackMap_orbitRelQuotientDesc a ha,
      (contMDiff_totalSpaceMap_orbitRelQuotientDesc_iff hm a ha).2 hcm⟩,
      fun b hb ↦ eq_orbitRelQuotientDesc_iff.2 hb.1⟩

/-- Descending a `G`-invariant isomorphism `e` between pulled-back finite-rank cores with `C^m`
forward and inverse total-space maps (`m ≤ n`) yields a `C^m` diffeomorphism of total spaces over
`M ⧸ G`, without completeness of `𝕜` or `IsContMDiff` assumptions. -/
noncomputable def orbitRelQuotientDescIsoDiffeomorph (hm : m ≤ n)
    {A D : FiniteRankBundleCore 𝕜 (orbitRel.Quotient G M)}
    (e : A.pullback (continuousQuotientMk G M) ≅ D.pullback (continuousQuotientMk G M))
    (he : ∀ (g : G) (x : M), e.hom.fiberMap (g • x) = e.hom.fiberMap x)
    (hcm : ContMDiff (I.prod 𝓘(𝕜, Fin (A.pullback (continuousQuotientMk G M)).rank → 𝕜))
      (I.prod 𝓘(𝕜, Fin (D.pullback (continuousQuotientMk G M)).rank → 𝕜)) m e.hom.totalSpaceMap)
    (hcm' : ContMDiff (I.prod 𝓘(𝕜, Fin (D.pullback (continuousQuotientMk G M)).rank → 𝕜))
      (I.prod 𝓘(𝕜, Fin (A.pullback (continuousQuotientMk G M)).rank → 𝕜)) m e.inv.totalSpaceMap) :
    A.core.TotalSpace ≃ₘ^m⟮I.prod 𝓘(𝕜, Fin A.rank → 𝕜), I.prod 𝓘(𝕜, Fin D.rank → 𝕜)⟯
      D.core.TotalSpace :=
  CoordinateHom.toDiffeomorphOfInv (orbitRelQuotientDescIso e he).hom
    (orbitRelQuotientDescIso e he).inv (orbitRelQuotientDescIso e he).hom_inv_id
    (orbitRelQuotientDescIso e he).inv_hom_id
    ((orbitRelQuotientDescIso_hom e he).symm ▸
      (contMDiff_totalSpaceMap_orbitRelQuotientDesc_iff hm e.hom he).2 hcm)
    ((orbitRelQuotientDescIso_inv e he).symm ▸
      (contMDiff_totalSpaceMap_orbitRelQuotientDesc_iff hm e.inv (fiberMap_inv_smul e he)).2 hcm')

@[simp] theorem coe_orbitRelQuotientDescIsoDiffeomorph (hm : m ≤ n)
    {A D : FiniteRankBundleCore 𝕜 (orbitRel.Quotient G M)}
    (e : A.pullback (continuousQuotientMk G M) ≅ D.pullback (continuousQuotientMk G M))
    (he : ∀ (g : G) (x : M), e.hom.fiberMap (g • x) = e.hom.fiberMap x)
    (hcm : ContMDiff (I.prod 𝓘(𝕜, Fin (A.pullback (continuousQuotientMk G M)).rank → 𝕜))
      (I.prod 𝓘(𝕜, Fin (D.pullback (continuousQuotientMk G M)).rank → 𝕜)) m e.hom.totalSpaceMap)
    (hcm' : ContMDiff (I.prod 𝓘(𝕜, Fin (D.pullback (continuousQuotientMk G M)).rank → 𝕜))
      (I.prod 𝓘(𝕜, Fin (A.pullback (continuousQuotientMk G M)).rank → 𝕜)) m e.inv.totalSpaceMap) :
    ⇑(orbitRelQuotientDescIsoDiffeomorph hm e he hcm hcm') =
      (orbitRelQuotientDesc e.hom he).totalSpaceMap := by
  simp [orbitRelQuotientDescIsoDiffeomorph]

@[simp] theorem coe_orbitRelQuotientDescIsoDiffeomorph_symm (hm : m ≤ n)
    {A D : FiniteRankBundleCore 𝕜 (orbitRel.Quotient G M)}
    (e : A.pullback (continuousQuotientMk G M) ≅ D.pullback (continuousQuotientMk G M))
    (he : ∀ (g : G) (x : M), e.hom.fiberMap (g • x) = e.hom.fiberMap x)
    (hcm : ContMDiff (I.prod 𝓘(𝕜, Fin (A.pullback (continuousQuotientMk G M)).rank → 𝕜))
      (I.prod 𝓘(𝕜, Fin (D.pullback (continuousQuotientMk G M)).rank → 𝕜)) m e.hom.totalSpaceMap)
    (hcm' : ContMDiff (I.prod 𝓘(𝕜, Fin (D.pullback (continuousQuotientMk G M)).rank → 𝕜))
      (I.prod 𝓘(𝕜, Fin (A.pullback (continuousQuotientMk G M)).rank → 𝕜)) m e.inv.totalSpaceMap) :
    ⇑(orbitRelQuotientDescIsoDiffeomorph hm e he hcm hcm').symm =
      (orbitRelQuotientDesc e.inv (fiberMap_inv_smul e he)).totalSpaceMap := by
  simp [orbitRelQuotientDescIsoDiffeomorph]

omit [ProperlyDiscontinuousSMul G M] [ContinuousConstSMul G M] [IsCancelSMul G M]
  [T2Space M] [LocallyCompactSpace M] in
private theorem bijective_fiberMap_orbitRelQuotientDesc
    {A D : FiniteRankBundleCore 𝕜 (orbitRel.Quotient G M)}
    (a : A.pullback (continuousQuotientMk G M) ⟶ D.pullback (continuousQuotientMk G M))
    (ha : ∀ (g : G) (x : M), a.fiberMap (g • x) = a.fiberMap x)
    (hbij : ∀ x : M, Function.Bijective (a.fiberMap x)) (z : orbitRel.Quotient G M) :
    Function.Bijective ((orbitRelQuotientDesc a ha).fiberMap z) :=
  Quotient.inductionOn z fun x ↦ by simpa only [fiberMap_orbitRelQuotientDesc_mk] using hbij x

/-- Over a complete scalar field, descending a `G`-invariant morphism `a` with `C^m` total-space map
(`m ≤ n`) and bijective fibre maps produces a `C^m` diffeomorphism of total spaces over `M ⧸ G`;
smoothness of the inverse follows automatically without `IsContMDiff` assumptions on the cores. -/
noncomputable def orbitRelQuotientDescDiffeomorph [CompleteSpace 𝕜] (hm : m ≤ n)
    {A D : FiniteRankBundleCore 𝕜 (orbitRel.Quotient G M)}
    (a : A.pullback (continuousQuotientMk G M) ⟶ D.pullback (continuousQuotientMk G M))
    (ha : ∀ (g : G) (x : M), a.fiberMap (g • x) = a.fiberMap x)
    (hcm : ContMDiff (I.prod 𝓘(𝕜, Fin (A.pullback (continuousQuotientMk G M)).rank → 𝕜))
      (I.prod 𝓘(𝕜, Fin (D.pullback (continuousQuotientMk G M)).rank → 𝕜)) m a.totalSpaceMap)
    (hbij : ∀ x : M, Function.Bijective (a.fiberMap x)) :
    A.core.TotalSpace ≃ₘ^m⟮I.prod 𝓘(𝕜, Fin A.rank → 𝕜), I.prod 𝓘(𝕜, Fin D.rank → 𝕜)⟯
      D.core.TotalSpace :=
  TauCeti.bundleDiffeomorph
    ((orbitRelQuotientDesc a ha).fiberEquiv (bijective_fiberMap_orbitRelQuotientDesc a ha hbij))
    (((contMDiff_totalSpaceMap_orbitRelQuotientDesc_iff hm a ha).2 hcm).congr
      fun ⟨_, _⟩ ↦ by simp only [CoordinateHom.fiberEquiv_apply, CoordinateHom.totalSpaceMap_mk])

@[simp] theorem coe_orbitRelQuotientDescDiffeomorph [CompleteSpace 𝕜] (hm : m ≤ n)
    {A D : FiniteRankBundleCore 𝕜 (orbitRel.Quotient G M)}
    (a : A.pullback (continuousQuotientMk G M) ⟶ D.pullback (continuousQuotientMk G M))
    (ha : ∀ (g : G) (x : M), a.fiberMap (g • x) = a.fiberMap x)
    (hcm : ContMDiff (I.prod 𝓘(𝕜, Fin (A.pullback (continuousQuotientMk G M)).rank → 𝕜))
      (I.prod 𝓘(𝕜, Fin (D.pullback (continuousQuotientMk G M)).rank → 𝕜)) m a.totalSpaceMap)
    (hbij : ∀ x : M, Function.Bijective (a.fiberMap x)) :
    ⇑(orbitRelQuotientDescDiffeomorph hm a ha hcm hbij) =
      (orbitRelQuotientDesc a ha).totalSpaceMap :=
  funext fun ⟨_, _⟩ ↦ by simp [orbitRelQuotientDescDiffeomorph]

@[simp] theorem orbitRelQuotientDescDiffeomorph_symm_mk [CompleteSpace 𝕜] (hm : m ≤ n)
    {A D : FiniteRankBundleCore 𝕜 (orbitRel.Quotient G M)}
    (a : A.pullback (continuousQuotientMk G M) ⟶ D.pullback (continuousQuotientMk G M))
    (ha : ∀ (g : G) (x : M), a.fiberMap (g • x) = a.fiberMap x)
    (hcm : ContMDiff (I.prod 𝓘(𝕜, Fin (A.pullback (continuousQuotientMk G M)).rank → 𝕜))
      (I.prod 𝓘(𝕜, Fin (D.pullback (continuousQuotientMk G M)).rank → 𝕜)) m a.totalSpaceMap)
    (hbij : ∀ x : M, Function.Bijective (a.fiberMap x))
    (x : M) (w : D.core.Fiber (Quotient.mk (orbitRel G M) x)) :
    (orbitRelQuotientDescDiffeomorph hm a ha hcm hbij).symm ⟨Quotient.mk (orbitRel G M) x, w⟩ =
      ⟨Quotient.mk (orbitRel G M) x, (a.fiberEquiv hbij x).symm w⟩ := by
  have heq : (orbitRelQuotientDesc a ha).fiberEquiv
      (bijective_fiberMap_orbitRelQuotientDesc a ha hbij) (Quotient.mk (orbitRel G M) x) =
      a.fiberEquiv hbij x :=
    DFunLike.ext _ _ fun (v : Fin A.rank → 𝕜) ↦
      ((orbitRelQuotientDesc a ha).fiberEquiv_apply _ _ v).trans
        ((congrArg (· v) (fiberMap_orbitRelQuotientDesc_mk a ha x)).trans
          (a.fiberEquiv_apply hbij x v).symm)
  rw [orbitRelQuotientDescDiffeomorph, TauCeti.bundleDiffeomorph_symm_apply]
  exact congrArg (TotalSpace.mk' (Fin A.rank → 𝕜) (Quotient.mk (orbitRel G M) x))
    (DFunLike.congr_fun (congrArg ContinuousLinearEquiv.symm heq) w)

end BundleMapDescent

/-! ### `C^m` bundle-map descent and bundle operations -/

section BundleMapOperations

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E H M E' H' M' : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  [TopologicalSpace M'] [ChartedSpace H' M']
  {m n : ℕ∞ω} {G K : Type*} [Group G] [Group K] [MulAction G M] [MulAction K M']

/-- For free properly discontinuous `C^n` actions and `m ≤ n`, the bundled continuous map
`φ.orbitRelQuotientContinuousMap hφ.continuous` induced by a `C^m` equivariant map `φ : M' →ₑ[σ] M`
is `C^m`. -/
theorem _root_.MulActionHom.contMDiff_orbitRelQuotientContinuousMap
    [ProperlyDiscontinuousSMul G M] [ContinuousConstSMul G M] [IsCancelSMul G M]
    [T2Space M] [LocallyCompactSpace M] [IsManifold I n M] [ContMDiffConstSMul I n G M]
    [ProperlyDiscontinuousSMul K M'] [ContinuousConstSMul K M'] [IsCancelSMul K M']
    [T2Space M'] [LocallyCompactSpace M'] [IsManifold I' n M'] [ContMDiffConstSMul I' n K M']
    (hm : m ≤ n) {σ : K → G} (φ : M' →ₑ[σ] M) (hφ : ContMDiff I' I m φ) :
    ContMDiff I' I m (φ.orbitRelQuotientContinuousMap hφ.continuous) := by
  rw [MulActionHom.coe_orbitRelQuotientContinuousMap]
  exact TauCeti.contMDiff_orbitRelQuotientMap hm hφ

/-- Pulling back a bundle morphism `a` with `C^m` total-space map along a `C^m` equivariant map
`φ : M' →ₑ[σ] M` yields a bundle morphism `pullbackEquivariant φ hφ.continuous a` with `C^m`
total-space map, without completeness of `𝕜` or `IsContMDiff` assumptions. -/
theorem contMDiff_totalSpaceMap_pullbackEquivariant {σ : K → G}
    (φ : M' →ₑ[σ] M) (hφ : ContMDiff I' I m φ)
    {A D : FiniteRankBundleCore 𝕜 (orbitRel.Quotient G M)}
    (a : A.pullback (continuousQuotientMk G M) ⟶ D.pullback (continuousQuotientMk G M))
    (ha : ContMDiff (I.prod 𝓘(𝕜, Fin (A.pullback (continuousQuotientMk G M)).rank → 𝕜))
      (I.prod 𝓘(𝕜, Fin (D.pullback (continuousQuotientMk G M)).rank → 𝕜)) m a.totalSpaceMap) :
    ContMDiff
      (I'.prod 𝓘(𝕜, Fin ((A.pullback (φ.orbitRelQuotientContinuousMap hφ.continuous)).pullback
        (continuousQuotientMk K M')).rank → 𝕜))
      (I'.prod 𝓘(𝕜, Fin ((D.pullback (φ.orbitRelQuotientContinuousMap hφ.continuous)).pullback
        (continuousQuotientMk K M')).rank → 𝕜))
      m (pullbackEquivariant φ hφ.continuous a).totalSpaceMap := by
  have heq : ∀ {C₁ C₂ : FiniteRankBundleCore 𝕜 M'} (h : C₁ = C₂),
      ContMDiff (I'.prod 𝓘(𝕜, Fin C₁.rank → 𝕜)) (I'.prod 𝓘(𝕜, Fin C₂.rank → 𝕜)) m
        (eqToHom h).totalSpaceMap := by
    rintro _ _ rfl; rw [eqToHom_refl]; exact CoordinateHom.contMDiff_totalSpaceMap_id _
  rw [totalSpaceMap_pullbackEquivariant]
  exact (heq _).comp
    ((contMDiff_totalSpaceMap_pullbackMap a ha (f := ⟨φ, hφ.continuous⟩) hφ).comp (heq _))

section QuotientOperations

variable [ProperlyDiscontinuousSMul G M] [ContinuousConstSMul G M] [IsCancelSMul G M]
  [T2Space M] [LocallyCompactSpace M] [IsManifold I n M] [ContMDiffConstSMul I n G M]
  [CompleteSpace 𝕜]

/-- Descending the transpose `dualMap a` of a `G`-invariant morphism `a` with `C^m` total-space map
(`m ≤ n`) between `C^m` cores yields a `C^m` map of dual total spaces over `M ⧸ G`. -/
theorem contMDiff_totalSpaceMap_orbitRelQuotientDesc_dualMap (hm : m ≤ n)
    {A D : FiniteRankBundleCore 𝕜 (orbitRel.Quotient G M)}
    [A.core.IsContMDiff I m] [D.core.IsContMDiff I m]
    (a : A.pullback (continuousQuotientMk G M) ⟶ D.pullback (continuousQuotientMk G M))
    (ha : ∀ (g : G) (x : M), a.fiberMap (g • x) = a.fiberMap x)
    (ha' : ∀ (g : G) (x : M), (dualMap a).fiberMap (g • x) = (dualMap a).fiberMap x)
    (hcm : ContMDiff (I.prod 𝓘(𝕜, Fin (A.pullback (continuousQuotientMk G M)).rank → 𝕜))
      (I.prod 𝓘(𝕜, Fin (D.pullback (continuousQuotientMk G M)).rank → 𝕜)) m a.totalSpaceMap) :
    ContMDiff (I.prod 𝓘(𝕜, Fin D.dual.rank → 𝕜)) (I.prod 𝓘(𝕜, Fin A.dual.rank → 𝕜)) m
      (orbitRelQuotientDesc (A := D.dual) (D := A.dual) (dualMap a) ha').totalSpaceMap :=
  (contMDiff_totalSpaceMap_dualMap (orbitRelQuotientDesc a ha)
    ((contMDiff_totalSpaceMap_orbitRelQuotientDesc_iff hm a ha).2 hcm)).congr fun p ↦
    congrFun (congrArg CoordinateHom.totalSpaceMap (orbitRelQuotientDesc_dualMap a ha ha')) p

/-- Descending the tensor product `tensorHom a b` of two `G`-invariant morphisms with `C^m`
total-space maps (`m ≤ n`) between `C^m` cores yields a `C^m` map of tensor-product total spaces
over `M ⧸ G`. -/
theorem contMDiff_totalSpaceMap_orbitRelQuotientDesc_tensorHom (hm : m ≤ n)
    {A A' D D' : FiniteRankBundleCore 𝕜 (orbitRel.Quotient G M)}
    [A.core.IsContMDiff I m] [A'.core.IsContMDiff I m]
    [D.core.IsContMDiff I m] [D'.core.IsContMDiff I m]
    (a : A.pullback (continuousQuotientMk G M) ⟶ A'.pullback (continuousQuotientMk G M))
    (b : D.pullback (continuousQuotientMk G M) ⟶ D'.pullback (continuousQuotientMk G M))
    (ha : ∀ (g : G) (x : M), a.fiberMap (g • x) = a.fiberMap x)
    (hb : ∀ (g : G) (x : M), b.fiberMap (g • x) = b.fiberMap x)
    (hab : ∀ (g : G) (x : M), (tensorHom a b).fiberMap (g • x) = (tensorHom a b).fiberMap x)
    (hcma : ContMDiff (I.prod 𝓘(𝕜, Fin (A.pullback (continuousQuotientMk G M)).rank → 𝕜))
      (I.prod 𝓘(𝕜, Fin (A'.pullback (continuousQuotientMk G M)).rank → 𝕜)) m a.totalSpaceMap)
    (hcmb : ContMDiff (I.prod 𝓘(𝕜, Fin (D.pullback (continuousQuotientMk G M)).rank → 𝕜))
      (I.prod 𝓘(𝕜, Fin (D'.pullback (continuousQuotientMk G M)).rank → 𝕜)) m b.totalSpaceMap) :
    ContMDiff (I.prod 𝓘(𝕜, Fin (tensor A D).rank → 𝕜)) (I.prod 𝓘(𝕜, Fin (tensor A' D').rank → 𝕜)) m
      (orbitRelQuotientDesc (A := tensor A D) (D := tensor A' D')
        (tensorHom a b) hab).totalSpaceMap :=
  (contMDiff_totalSpaceMap_tensorHom (orbitRelQuotientDesc a ha) (orbitRelQuotientDesc b hb)
    ((contMDiff_totalSpaceMap_orbitRelQuotientDesc_iff hm a ha).2 hcma)
    ((contMDiff_totalSpaceMap_orbitRelQuotientDesc_iff hm b hb).2 hcmb)).congr fun p ↦
    congrFun (congrArg CoordinateHom.totalSpaceMap (orbitRelQuotientDesc_tensorHom a b ha hb hab)) p

/-- Descending the exterior power `(exteriorPower 𝕜 M j).map a` of a `G`-invariant morphism `a` with
`C^m` total-space map (`m ≤ n`) between `C^m` cores yields a `C^m` map of exterior-power total
spaces over `M ⧸ G`. -/
theorem contMDiff_totalSpaceMap_orbitRelQuotientDesc_exteriorPower_map (hm : m ≤ n) (j : ℕ)
    {A D : FiniteRankBundleCore 𝕜 (orbitRel.Quotient G M)}
    [A.core.IsContMDiff I m] [D.core.IsContMDiff I m]
    (a : A.pullback (continuousQuotientMk G M) ⟶ D.pullback (continuousQuotientMk G M))
    (ha : ∀ (g : G) (x : M), a.fiberMap (g • x) = a.fiberMap x)
    (hja : ∀ (g : G) (x : M),
      ((exteriorPower 𝕜 M j).map a).fiberMap (g • x) = ((exteriorPower 𝕜 M j).map a).fiberMap x)
    (hcm : ContMDiff (I.prod 𝓘(𝕜, Fin (A.pullback (continuousQuotientMk G M)).rank → 𝕜))
      (I.prod 𝓘(𝕜, Fin (D.pullback (continuousQuotientMk G M)).rank → 𝕜)) m a.totalSpaceMap) :
    ContMDiff (I.prod 𝓘(𝕜, Fin ((exteriorPower 𝕜 (orbitRel.Quotient G M) j).obj A).rank → 𝕜))
      (I.prod 𝓘(𝕜, Fin ((exteriorPower 𝕜 (orbitRel.Quotient G M) j).obj D).rank → 𝕜)) m
      (orbitRelQuotientDesc (A := (exteriorPower 𝕜 (orbitRel.Quotient G M) j).obj A)
        (D := (exteriorPower 𝕜 (orbitRel.Quotient G M) j).obj D)
        ((exteriorPower 𝕜 M j).map a) hja).totalSpaceMap :=
  (contMDiff_totalSpaceMap_exteriorPower_map j (orbitRelQuotientDesc a ha)
    ((contMDiff_totalSpaceMap_orbitRelQuotientDesc_iff hm a ha).2 hcm)).congr fun p ↦
    congrFun (congrArg CoordinateHom.totalSpaceMap
      (orbitRelQuotientDesc_exteriorPower_map j a ha hja)) p

/-- Descending the determinant morphism `detMap a hr` of a `G`-invariant morphism `a` with `C^m`
total-space map (`m ≤ n`) between equal-rank `C^m` cores yields a `C^m` map of determinant total
spaces over `M ⧸ G`. -/
theorem contMDiff_totalSpaceMap_orbitRelQuotientDesc_detMap (hm : m ≤ n)
    {A D : FiniteRankBundleCore 𝕜 (orbitRel.Quotient G M)}
    [A.core.IsContMDiff I m] [D.core.IsContMDiff I m]
    (a : A.pullback (continuousQuotientMk G M) ⟶ D.pullback (continuousQuotientMk G M))
    (hr : A.rank = D.rank) (ha : ∀ (g : G) (x : M), a.fiberMap (g • x) = a.fiberMap x)
    (hda : ∀ (g : G) (x : M), (detMap a hr).fiberMap (g • x) = (detMap a hr).fiberMap x :=
      fun g x ↦ fiberMap_detMap_eq_of_fiberMap_eq (a := a) (b := a) hr (ha g x))
    (hcm : ContMDiff (I.prod 𝓘(𝕜, Fin (A.pullback (continuousQuotientMk G M)).rank → 𝕜))
      (I.prod 𝓘(𝕜, Fin (D.pullback (continuousQuotientMk G M)).rank → 𝕜)) m a.totalSpaceMap) :
    ContMDiff (I.prod 𝓘(𝕜, Fin A.det.rank → 𝕜)) (I.prod 𝓘(𝕜, Fin D.det.rank → 𝕜)) m
      (orbitRelQuotientDesc (A := A.det) (D := D.det) (detMap a hr) hda).totalSpaceMap :=
  (contMDiff_totalSpaceMap_detMap (orbitRelQuotientDesc a ha) hr
    ((contMDiff_totalSpaceMap_orbitRelQuotientDesc_iff hm a ha).2 hcm)).congr fun p ↦
    congrFun (congrArg CoordinateHom.totalSpaceMap (orbitRelQuotientDesc_detMap a hr ha hda)) p

end QuotientOperations

end BundleMapOperations

/-! ### `C^m` section descent and bundle operations -/

section SectionDescent

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E H M E' H' M' : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  [TopologicalSpace M'] [ChartedSpace H' M']
  {m n : ℕ∞ω} {G K : Type*} [Group G] [Group K] [MulAction G M] [MulAction K M']
  [ProperlyDiscontinuousSMul G M] [ContinuousConstSMul G M] [IsCancelSMul G M]
  [T2Space M] [LocallyCompactSpace M] [IsManifold I n M] [ContMDiffConstSMul I n G M]

/-- **Smooth and holomorphic section descent for finite-rank cores.** For `m ≤ n`, the descended
section `MulAction.orbitRelQuotientRec t ht` of `A` over `M ⧸ G` is `C^m` if and only if `t` is
`C^m` as a section of `(A.pullback (continuousQuotientMk G M)).core`, without completeness of `𝕜` or
`IsContMDiff` assumptions on `A`. -/
theorem contMDiff_section_orbitRelQuotientRec_core_iff (hm : m ≤ n)
    (A : FiniteRankBundleCore 𝕜 (orbitRel.Quotient G M))
    {t : ∀ x : M, A.core.Fiber (Quotient.mk (orbitRel G M) x)}
    (ht : ∀ (g : G) (x : M), t (g • x) ≍ t x) :
    ContMDiff I (I.prod 𝓘(𝕜, Fin A.rank → 𝕜)) m
        (fun z ↦ TotalSpace.mk' (Fin A.rank → 𝕜) z (orbitRelQuotientRec t ht z)) ↔
      ContMDiff I (I.prod 𝓘(𝕜, Fin (A.pullback (continuousQuotientMk G M)).rank → 𝕜)) m
        fun x ↦ TotalSpace.mk' (Fin (A.pullback (continuousQuotientMk G M)).rank → 𝕜)
          (E := (A.pullback (continuousQuotientMk G M)).core.Fiber) x (t x) := by
  have hq : ContMDiff I I m (continuousQuotientMk G M) :=
    (isLocalDiffeomorph_quotientMk (I := I) (n := n) (G := G)).contMDiff.of_le hm
  have hlift : (fun x ↦ A.pullbackLift (continuousQuotientMk G M)
      (TotalSpace.mk' (Fin (A.pullback (continuousQuotientMk G M)).rank → 𝕜)
        (E := (A.pullback (continuousQuotientMk G M)).core.Fiber) x (t x))) =
      fun x ↦ TotalSpace.mk' (Fin A.rank → 𝕜) (Quotient.mk (orbitRel G M) x) (t x) :=
    funext fun x ↦ A.pullbackLift_mk (continuousQuotientMk G M) x (t x)
  rw [contMDiff_section_orbitRelQuotientRec_iff hm, A.contMDiff_core_pullback_iff hq, hlift]
  exact ⟨fun h ↦ ⟨contMDiff_id, h⟩, fun h ↦ h.2⟩

/-- Along a `C^m` equivariant map `φ : M' →ₑ[σ] M` between free properly discontinuous `C^n`
actions (`m ≤ n`), descending the pulled-back section `fun x' ↦ t (φ x')` of a `C^m` `G`-invariant
section `t` yields a `C^m` section of `A.pullback (φ.orbitRelQuotientContinuousMap hφ.continuous)`
over `M' ⧸ K`. -/
theorem contMDiff_section_orbitRelQuotientRec_pullback
    [ProperlyDiscontinuousSMul K M'] [ContinuousConstSMul K M'] [IsCancelSMul K M']
    [T2Space M'] [LocallyCompactSpace M'] [IsManifold I' n M'] [ContMDiffConstSMul I' n K M']
    (hm : m ≤ n) {σ : K → G} (φ : M' →ₑ[σ] M) (hφ : ContMDiff I' I m φ)
    (A : FiniteRankBundleCore 𝕜 (orbitRel.Quotient G M))
    {t : ∀ x : M, A.core.Fiber (Quotient.mk (orbitRel G M) x)}
    (ht : ∀ (g : G) (x : M), t (g • x) ≍ t x)
    (htcm : ContMDiff I (I.prod 𝓘(𝕜, Fin (A.pullback (continuousQuotientMk G M)).rank → 𝕜)) m
      fun x ↦ TotalSpace.mk' (Fin (A.pullback (continuousQuotientMk G M)).rank → 𝕜)
        (E := (A.pullback (continuousQuotientMk G M)).core.Fiber) x (t x))
    (ht' : ∀ (k : K) (x' : M'),
      (t (φ (k • x')) : (A.pullback (φ.orbitRelQuotientContinuousMap hφ.continuous)).core.Fiber
        (Quotient.mk (orbitRel K M') (k • x'))) ≍
      (t (φ x') : (A.pullback (φ.orbitRelQuotientContinuousMap hφ.continuous)).core.Fiber
        (Quotient.mk (orbitRel K M') x'))) :
    ContMDiff I'
      (I'.prod 𝓘(𝕜, Fin (A.pullback (φ.orbitRelQuotientContinuousMap hφ.continuous)).rank → 𝕜)) m
      fun z' ↦ TotalSpace.mk'
        (Fin (A.pullback (φ.orbitRelQuotientContinuousMap hφ.continuous)).rank → 𝕜)
        (E := (A.pullback (φ.orbitRelQuotientContinuousMap hφ.continuous)).core.Fiber) z'
        (orbitRelQuotientRec
          (V := (A.pullback (φ.orbitRelQuotientContinuousMap hφ.continuous)).core.Fiber)
          (fun x' ↦ t (φ x')) ht' z') := by
  have hdesc := (contMDiff_section_orbitRelQuotientRec_core_iff hm A ht).2 htcm
  have hbar := φ.contMDiff_orbitRelQuotientContinuousMap hm hφ
  refine (A.contMDiff_core_pullback_iff hbar).2 ⟨contMDiff_id, (hdesc.comp hbar).congr fun z' ↦ ?_⟩
  rw [A.pullbackLift_mk, Function.comp_apply]
  exact congrArg
    (TotalSpace.mk' (Fin A.rank → 𝕜) (φ.orbitRelQuotientContinuousMap hφ.continuous z'))
    (orbitRelQuotientRec_pullback φ hφ.continuous A ht ht' z')

/-- Evaluating `orbitRelQuotientDesc a ha` on a descended `C^m` section (`m ≤ n`), equivalently
descending `fun x ↦ a.fiberMap x (t x)`, yields a `C^m` section of `D` over `M ⧸ G`. -/
theorem contMDiff_section_orbitRelQuotientRec_fiberMap_apply (hm : m ≤ n)
    {A D : FiniteRankBundleCore 𝕜 (orbitRel.Quotient G M)}
    (a : A.pullback (continuousQuotientMk G M) ⟶ D.pullback (continuousQuotientMk G M))
    (ha : ∀ (g : G) (x : M), a.fiberMap (g • x) = a.fiberMap x)
    (hcma : ContMDiff (I.prod 𝓘(𝕜, Fin (A.pullback (continuousQuotientMk G M)).rank → 𝕜))
      (I.prod 𝓘(𝕜, Fin (D.pullback (continuousQuotientMk G M)).rank → 𝕜)) m a.totalSpaceMap)
    {t : ∀ x : M, A.core.Fiber (Quotient.mk (orbitRel G M) x)}
    (ht : ∀ (g : G) (x : M), t (g • x) ≍ t x)
    (hcmt : ContMDiff I (I.prod 𝓘(𝕜, Fin (A.pullback (continuousQuotientMk G M)).rank → 𝕜)) m
      fun x ↦ TotalSpace.mk' (Fin (A.pullback (continuousQuotientMk G M)).rank → 𝕜)
        (E := (A.pullback (continuousQuotientMk G M)).core.Fiber) x (t x))
    (hat : ∀ (g : G) (x : M),
      (a.fiberMap (g • x) (t (g • x)) : D.core.Fiber (Quotient.mk (orbitRel G M) (g • x))) ≍
        (a.fiberMap x (t x) : D.core.Fiber (Quotient.mk (orbitRel G M) x)) := fun g x ↦ by
      simpa only [fiberMap_orbitRelQuotientDesc_mk] using
        apply_smul_heq (fun z v ↦ (orbitRelQuotientDesc a ha).fiberMap z v) ht g x) :
    ContMDiff I (I.prod 𝓘(𝕜, Fin D.rank → 𝕜)) m fun z ↦ TotalSpace.mk' (Fin D.rank → 𝕜) z
      (orbitRelQuotientRec (V := D.core.Fiber) (fun x ↦ a.fiberMap x (t x)) hat z) := by
  refine (((contMDiff_totalSpaceMap_orbitRelQuotientDesc_iff hm a ha).2 hcma).comp
    ((contMDiff_section_orbitRelQuotientRec_core_iff hm A ht).2 hcmt)).congr fun z ↦ ?_
  rw [Function.comp_apply, CoordinateHom.totalSpaceMap_mk]
  exact congrArg (TotalSpace.mk' (Fin D.rank → 𝕜) z)
    (orbitRelQuotientRec_fiberMap_apply a ha ht hat z)

/-- For `C^m` `G`-invariant dual and primal sections over `M` (`m ≤ n`), their descended scalar
pairing on `M ⧸ G` is `C^m`, without `IsContMDiff` assumptions on `A`. -/
theorem contMDiff_orbitRelQuotientLift_dualFiberEquiv [CompleteSpace 𝕜] (hm : m ≤ n)
    (A : FiniteRankBundleCore 𝕜 (orbitRel.Quotient G M))
    {w : ∀ x : M, A.dual.core.Fiber (Quotient.mk (orbitRel G M) x)}
    {v : ∀ x : M, A.core.Fiber (Quotient.mk (orbitRel G M) x)}
    (hw : ∀ (g : G) (x : M), w (g • x) ≍ w x) (hv : ∀ (g : G) (x : M), v (g • x) ≍ v x)
    (hcmw : ContMDiff I (I.prod 𝓘(𝕜, Fin (A.pullback (continuousQuotientMk G M)).dual.rank → 𝕜)) m
      fun x ↦ TotalSpace.mk' (Fin (A.pullback (continuousQuotientMk G M)).dual.rank → 𝕜)
        (E := (A.pullback (continuousQuotientMk G M)).dual.core.Fiber) x (w x))
    (hcmv : ContMDiff I (I.prod 𝓘(𝕜, Fin (A.pullback (continuousQuotientMk G M)).rank → 𝕜)) m
      fun x ↦ TotalSpace.mk' (Fin (A.pullback (continuousQuotientMk G M)).rank → 𝕜)
        (E := (A.pullback (continuousQuotientMk G M)).core.Fiber) x (v x))
    (hwv : ∀ (g : G) (x : M),
      dualFiberEquiv (A.pullback (continuousQuotientMk G M)) (g • x) (w (g • x)) (v (g • x)) =
        dualFiberEquiv (A.pullback (continuousQuotientMk G M)) x (w x) (v x) := fun g x ↦
      (dualFiberEquiv_pullback_apply A (continuousQuotientMk G M) (g • x) (w (g • x))
        (v (g • x))).trans ((eq_of_heq (apply₂_smul_heq (fun q w' v' ↦ dualFiberEquiv A q w' v')
          hw hv g x)).trans
          (dualFiberEquiv_pullback_apply A (continuousQuotientMk G M) x (w x) (v x)).symm)) :
    ContMDiff I 𝓘(𝕜, 𝕜) m (orbitRelQuotientLift
      (fun x ↦ dualFiberEquiv (A.pullback (continuousQuotientMk G M)) x (w x) (v x)) hwv) :=
  (contMDiff_orbitRelQuotientLift_iff hm).2
    ((A.pullback (continuousQuotientMk G M)).contMDiff_dualFiberEquiv_section hcmw hcmv)

/-- Descending the pure tensor of two `C^m` `G`-invariant sections (`m ≤ n`) yields a `C^m` section
of `tensor A D` over `M ⧸ G`, without completeness of `𝕜` or `IsContMDiff` assumptions. -/
theorem contMDiff_section_orbitRelQuotientRec_pureTensorSection (hm : m ≤ n)
    (A D : FiniteRankBundleCore 𝕜 (orbitRel.Quotient G M))
    {s₁ : ∀ x : M, A.core.Fiber (Quotient.mk (orbitRel G M) x)}
    {s₂ : ∀ x : M, D.core.Fiber (Quotient.mk (orbitRel G M) x)}
    (hs₁ : ∀ (g : G) (x : M), s₁ (g • x) ≍ s₁ x) (hs₂ : ∀ (g : G) (x : M), s₂ (g • x) ≍ s₂ x)
    (hcms₁ : ContMDiff I (I.prod 𝓘(𝕜, Fin (A.pullback (continuousQuotientMk G M)).rank → 𝕜)) m
      fun x ↦ TotalSpace.mk' (Fin (A.pullback (continuousQuotientMk G M)).rank → 𝕜)
        (E := (A.pullback (continuousQuotientMk G M)).core.Fiber) x (s₁ x))
    (hcms₂ : ContMDiff I (I.prod 𝓘(𝕜, Fin (D.pullback (continuousQuotientMk G M)).rank → 𝕜)) m
      fun x ↦ TotalSpace.mk' (Fin (D.pullback (continuousQuotientMk G M)).rank → 𝕜)
        (E := (D.pullback (continuousQuotientMk G M)).core.Fiber) x (s₂ x))
    (hst : ∀ (g : G) (x : M),
      (pureTensorSection (A.pullback (continuousQuotientMk G M))
        (D.pullback (continuousQuotientMk G M)) s₁ s₂ (g • x) :
          (tensor A D).core.Fiber (Quotient.mk (orbitRel G M) (g • x))) ≍
      (pureTensorSection (A.pullback (continuousQuotientMk G M))
        (D.pullback (continuousQuotientMk G M)) s₁ s₂ x :
          (tensor A D).core.Fiber (Quotient.mk (orbitRel G M) x))) :
    ContMDiff I (I.prod 𝓘(𝕜, Fin (tensor A D).rank → 𝕜)) m
      fun z ↦ TotalSpace.mk' (Fin (tensor A D).rank → 𝕜) z
        (orbitRelQuotientRec (V := (tensor A D).core.Fiber)
          (pureTensorSection (A.pullback (continuousQuotientMk G M))
            (D.pullback (continuousQuotientMk G M)) s₁ s₂) hst z) :=
  (contMDiff_pureTensorSection A D
    ((contMDiff_section_orbitRelQuotientRec_core_iff hm A hs₁).2 hcms₁)
    ((contMDiff_section_orbitRelQuotientRec_core_iff hm D hs₂).2 hcms₂)).congr fun z ↦
    congrArg (TotalSpace.mk' (Fin (tensor A D).rank → 𝕜) z)
      (orbitRelQuotientRec_pureTensorSection A D hs₁ hs₂ hst z)

/-- Descending the exterior product of `j` `C^m` `G`-invariant sections (`m ≤ n`) yields a `C^m`
section of `(exteriorPower 𝕜 (M ⧸ G) j).obj A`, without completeness of `𝕜` or `IsContMDiff`
assumptions. -/
theorem contMDiff_section_orbitRelQuotientRec_wedgeSection (hm : m ≤ n) (j : ℕ)
    (A : FiniteRankBundleCore 𝕜 (orbitRel.Quotient G M))
    {s : Fin j → ∀ x : M, A.core.Fiber (Quotient.mk (orbitRel G M) x)}
    (hs : ∀ (k : Fin j) (g : G) (x : M), s k (g • x) ≍ s k x)
    (hcms : ∀ k, ContMDiff I (I.prod 𝓘(𝕜, Fin (A.pullback (continuousQuotientMk G M)).rank → 𝕜)) m
      fun x ↦ TotalSpace.mk' (Fin (A.pullback (continuousQuotientMk G M)).rank → 𝕜)
        (E := (A.pullback (continuousQuotientMk G M)).core.Fiber) x (s k x))
    (hws : ∀ (g : G) (x : M),
      (wedgeSection j (A.pullback (continuousQuotientMk G M)) s (g • x) :
        ((exteriorPower 𝕜 (orbitRel.Quotient G M) j).obj A).core.Fiber
          (Quotient.mk (orbitRel G M) (g • x))) ≍
      (wedgeSection j (A.pullback (continuousQuotientMk G M)) s x :
        ((exteriorPower 𝕜 (orbitRel.Quotient G M) j).obj A).core.Fiber
          (Quotient.mk (orbitRel G M) x))) :
    ContMDiff I (I.prod 𝓘(𝕜, Fin ((exteriorPower 𝕜 (orbitRel.Quotient G M) j).obj A).rank → 𝕜)) m
      fun z ↦ TotalSpace.mk' (Fin ((exteriorPower 𝕜 (orbitRel.Quotient G M) j).obj A).rank → 𝕜) z
        (orbitRelQuotientRec (V := ((exteriorPower 𝕜 (orbitRel.Quotient G M) j).obj A).core.Fiber)
          (wedgeSection j (A.pullback (continuousQuotientMk G M)) s) hws z) :=
  (contMDiff_wedgeSection j A fun k ↦
    (contMDiff_section_orbitRelQuotientRec_core_iff hm A (hs k)).2 (hcms k)).congr fun z ↦
    congrArg (TotalSpace.mk' (Fin ((exteriorPower 𝕜 (orbitRel.Quotient G M) j).obj A).rank → 𝕜) z)
      (orbitRelQuotientRec_wedgeSection j A hs hws z)

/-- Descending the determinant wedge of `A.rank` `C^m` `G`-invariant sections (`m ≤ n`) yields a
`C^m` section of `A.det` over `M ⧸ G`, without completeness of `𝕜` or `IsContMDiff` assumptions. -/
theorem contMDiff_section_orbitRelQuotientRec_detSection (hm : m ≤ n)
    (A : FiniteRankBundleCore 𝕜 (orbitRel.Quotient G M))
    {s : Fin A.rank → ∀ x : M, A.core.Fiber (Quotient.mk (orbitRel G M) x)}
    (hs : ∀ (k : Fin A.rank) (g : G) (x : M), s k (g • x) ≍ s k x)
    (hcms : ∀ k, ContMDiff I (I.prod 𝓘(𝕜, Fin (A.pullback (continuousQuotientMk G M)).rank → 𝕜)) m
      fun x ↦ TotalSpace.mk' (Fin (A.pullback (continuousQuotientMk G M)).rank → 𝕜)
        (E := (A.pullback (continuousQuotientMk G M)).core.Fiber) x (s k x))
    (hds : ∀ (g : G) (x : M),
      (detSection (A.pullback (continuousQuotientMk G M)) s (g • x) :
        A.det.core.Fiber (Quotient.mk (orbitRel G M) (g • x))) ≍
      (detSection (A.pullback (continuousQuotientMk G M)) s x :
        A.det.core.Fiber (Quotient.mk (orbitRel G M) x))) :
    ContMDiff I (I.prod 𝓘(𝕜, Fin A.det.rank → 𝕜)) m fun z ↦ TotalSpace.mk' (Fin A.det.rank → 𝕜) z
      (orbitRelQuotientRec (V := A.det.core.Fiber)
        (detSection (A.pullback (continuousQuotientMk G M)) s) hds z) :=
  (contMDiff_detSection A fun k ↦
    (contMDiff_section_orbitRelQuotientRec_core_iff hm A (hs k)).2 (hcms k)).congr fun z ↦
    congrArg (TotalSpace.mk' (Fin A.det.rank → 𝕜) z) (orbitRelQuotientRec_detSection A hs hds z)

end SectionDescent

end TauCeti.FiniteRankBundleCore
