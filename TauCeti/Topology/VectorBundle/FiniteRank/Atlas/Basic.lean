/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Core.Basic
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# Small variable-rank vector-bundle atlases

`TauCeti.FiniteRankAtlas` assembles point-indexed Mathlib vector-bundle cores on the
clopen strata of a locally constant natural-number rank. Its data use only the base
universe (and the scalar universe), not the universe of any original bundle's fibres.
There is no bounded-rank or finite-cover hypothesis.

The reconstructed total space is a native `Bundle.TotalSpace`, with the topology of the
disjoint union of the core total spaces. Each core total space embeds openly, with image
exactly its rank stratum. Thus its existing Mathlib vector-bundle topology is retained,
rather than replaced by the product topology on coordinates.

`FiniteRankAtlas.ofBundles` takes actual vector bundles on the rank strata, in any fibre
universe. `FiniteRankAtlas.reconstructionHomeomorph` compares the reconstruction with
their disjoint union, using `TauCeti.pointIndexedCoreHomeomorph` on each stratum. Its
forward and inverse formulas retain the continuous linear fibre identifications.
-/

public section

open Bundle Topology

namespace TauCeti

universe u v w

variable (𝕜 : Type v) [NontriviallyNormedField 𝕜] (X : Type u) [TopologicalSpace X]

/-- A variable finite-rank bundle atlas, with charts indexed by the points of each
clopen rank stratum. All stored coordinate data are independent of the fibre universe. -/
structure FiniteRankAtlas where
  /-- The locally constant, not necessarily bounded, rank. -/
  rank : LocallyConstant X ℕ
  /-- The actual coordinate bundle core on each rank stratum. -/
  charts (n : ℕ) : VectorBundleCore 𝕜 {x : X // rank x = n} (Fin n → 𝕜)
    {x : X // rank x = n}
  /-- Each point labels its own preferred chart. -/
  indexAt_eq (n : ℕ) (x : {x : X // rank x = n}) : (charts n).indexAt x = x

namespace FiniteRankAtlas

variable {𝕜 X} (A : FiniteRankAtlas 𝕜 X)

/-- The finite coordinate fibre of the reconstructed variable-rank bundle.
This is an abbreviation so the standard topological-module instances are available. -/
abbrev Fiber (x : X) := Fin (A.rank x) → 𝕜

/-- The disjoint union of the native core total spaces. -/
abbrev GluedTotalSpace := Σ n : ℕ, (A.charts n).TotalSpace

/-- The projection of the disjoint union to the original base. -/
def gluedProj (p : A.GluedTotalSpace) : X := p.2.proj.1

@[simp] theorem gluedProj_mk (n : ℕ) (p : (A.charts n).TotalSpace) :
    A.gluedProj ⟨n, p⟩ = p.proj.1 := (rfl)

/-- The glued projection is continuous, since each stratum projection is continuous. -/
@[continuity, fun_prop] theorem continuous_gluedProj : Continuous A.gluedProj :=
  continuous_sigma fun n => continuous_subtype_val.comp (A.charts n).continuous_proj

/-- The glued projection is open: the rank strata are open in the base. -/
theorem isOpenMap_gluedProj : IsOpenMap A.gluedProj := by
  apply isOpenMap_sigma.2
  intro n
  exact ((A.rank.isLocallyConstant.isOpen_fiber n).isOpenEmbedding_subtypeVal.isOpenMap).comp
    (A.charts n).isOpenMap_proj

/-- Reindex the disjoint union as a native total space over the original base.
The cast uses the stratum equation to identify its coordinate index with the rank at `x`. -/
private def totalSpaceEquiv : A.GluedTotalSpace ≃ TotalSpace Unit A.Fiber where
  toFun p := ⟨p.2.proj.1, fun i => p.2.2 (Fin.cast p.2.proj.2 i)⟩
  invFun p := ⟨A.rank p.proj, ⟨⟨p.proj, rfl⟩, p.2⟩⟩
  left_inv p := by
    rcases p with ⟨n, ⟨⟨x, hx⟩, v⟩⟩
    cases hx
    rfl
  right_inv p := by
    cases p
    rfl

/-- The reconstructed topology is the disjoint-union topology of the native bundle
cores, transported to the total space over `X`. -/
instance : TopologicalSpace (TotalSpace Unit A.Fiber) :=
  TopologicalSpace.induced (fun p : TotalSpace Unit A.Fiber =>
    (⟨A.rank p.proj, ⟨⟨p.proj, rfl⟩, p.2⟩⟩ : A.GluedTotalSpace)) inferInstance

/-- Reindexing the core total spaces gives the reconstructed bundle topology. -/
def totalSpaceHomeomorph : A.GluedTotalSpace ≃ₜ TotalSpace Unit A.Fiber :=
  (A.totalSpaceEquiv.symm.toHomeomorphOfIsInducing ⟨rfl⟩).symm

@[simp] theorem totalSpaceHomeomorph_apply (p : A.GluedTotalSpace) :
    A.totalSpaceHomeomorph p =
      ⟨p.2.proj.1, fun i => p.2.2 (Fin.cast p.2.proj.2 i)⟩ := (rfl)

@[simp] theorem totalSpaceHomeomorph_symm_apply (p : TotalSpace Unit A.Fiber) :
    A.totalSpaceHomeomorph.symm p = ⟨A.rank p.proj, ⟨⟨p.proj, rfl⟩, p.2⟩⟩ := (rfl)

/-- The reconstructed total-space projection is continuous. -/
@[continuity, fun_prop] theorem continuous_proj :
    Continuous (TotalSpace.proj : TotalSpace Unit A.Fiber → X) :=
  A.continuous_gluedProj.comp A.totalSpaceHomeomorph.symm.continuous

/-- The reconstructed total-space projection is open. -/
theorem isOpenMap_proj : IsOpenMap (TotalSpace.proj : TotalSpace Unit A.Fiber → X) :=
  A.isOpenMap_gluedProj.comp A.totalSpaceHomeomorph.symm.isOpenMap

/-- Each native core total space is an open subspace of the reconstruction. -/
theorem isOpenEmbedding_stratum (n : ℕ) :
    IsOpenEmbedding (fun p : (A.charts n).TotalSpace => A.totalSpaceHomeomorph ⟨n, p⟩) :=
  A.totalSpaceHomeomorph.isOpenEmbedding.comp IsOpenEmbedding.sigmaMk

/-- The image of the `n`th core total space is exactly the rank-`n` part of the
reconstructed total space. -/
theorem range_stratum (n : ℕ) :
    Set.range (fun p : (A.charts n).TotalSpace => A.totalSpaceHomeomorph ⟨n, p⟩) =
      {p : TotalSpace Unit A.Fiber | A.rank p.proj = n} := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    exact q.proj.2
  · intro hp
    cases p with
    | mk x v =>
      cases hp
      exact ⟨⟨⟨x, rfl⟩, v⟩, rfl⟩

section Continuity

variable {Y : Type*} [TopologicalSpace Y] {b : Y → X}

/-- A map into a reconstructed total space is continuous exactly when its restrictions
to the rank strata, read in the native core total spaces, are continuous. -/
theorem continuous_mk_iff_rankStrata (hb : Continuous b) (s : ∀ y, A.Fiber (b y)) :
    Continuous (fun y => (⟨b y, s y⟩ : TotalSpace Unit A.Fiber)) ↔
      ∀ n : ℕ, Continuous (fun y : {y : Y // A.rank (b y) = n} =>
        (⟨⟨b y, y.2⟩, fun i => s y (Fin.cast y.2.symm i)⟩ : (A.charts n).TotalSpace)) := by
  constructor
  · intro hs n
    apply (IsEmbedding.sigmaMk (σ := fun n => (A.charts n).TotalSpace)).continuous_iff.2
    convert A.totalSpaceHomeomorph.symm.continuous.comp (hs.comp continuous_subtype_val) using 1
    funext ⟨y, hy⟩
    cases hy
    simp only [Function.comp_apply, totalSpaceHomeomorph_symm_apply, Fin.cast_refl, id_eq]
  · intro hs
    apply continuous_of_cover_nhds (s := fun n : ℕ => {y : Y | A.rank (b y) = n})
    · intro y
      exact ⟨A.rank (b y), ((A.rank.isLocallyConstant.isOpen_fiber _).preimage hb).mem_nhds rfl⟩
    · intro n
      rw [continuousOn_iff_continuous_domRestrict]
      convert A.totalSpaceHomeomorph.continuous.comp (continuous_sigmaMk.comp (hs n)) using 1
      funext ⟨y, hy⟩
      cases hy
      simp only [Set.domRestrict_apply, Function.comp_apply, totalSpaceHomeomorph_apply,
        Fin.cast_refl, id_eq]

/-- The zero section of a variable-rank atlas is continuous. -/
@[fun_prop]
theorem continuous_zeroSection :
    Continuous (fun x => (⟨x, 0⟩ : TotalSpace Unit A.Fiber)) := by
  apply (A.continuous_mk_iff_rankStrata continuous_id _).2
  intro n
  exact (Bundle.Trivialization.continuous_zeroSection 𝕜
    (F := Fin n → 𝕜) (E := (A.charts n).Fiber)).congr (fun _ => rfl)

end Continuity

section Reconstruction

variable (𝕜) (r : LocallyConstant X ℕ)
  (E : ∀ n : ℕ, {x : X // r x = n} → Type w)
  [∀ n x, AddCommMonoid (E n x)] [∀ n x, Module 𝕜 (E n x)]
  [∀ n x, TopologicalSpace (E n x)]
  [∀ n, TopologicalSpace (TotalSpace (Fin n → 𝕜) (E n))]
  [∀ n, FiberBundle (Fin n → 𝕜) (E n)]
  [∀ n, VectorBundle 𝕜 (Fin n → 𝕜) (E n)]

/-- Encode actual bundles on the clopen rank strata by small point-indexed cores.
The original fibre universe does not appear in the resulting atlas type. -/
-- Expose the rank projection to identify the reconstructed dependent coordinate fibres.
@[expose] noncomputable def ofBundles : FiniteRankAtlas 𝕜 X where
  rank := r
  charts n := pointIndexedCore 𝕜 (Fin n → 𝕜) (E n)
  indexAt_eq n := pointIndexedCore_indexAt 𝕜 (Fin n → 𝕜) (E n)

@[simp] theorem rank_ofBundles : (ofBundles 𝕜 r E).rank = r := (rfl)

@[simp] theorem charts_ofBundles (n : ℕ) :
    (ofBundles 𝕜 r E).charts n = pointIndexedCore 𝕜 (Fin n → 𝕜) (E n) := (rfl)

private noncomputable def gluedReconstructionHomeomorph :
    (ofBundles 𝕜 r E).GluedTotalSpace ≃ₜ Σ n : ℕ, TotalSpace (Fin n → 𝕜) (E n) where
  toEquiv := Equiv.sigmaCongrRight fun n => (pointIndexedCoreHomeomorph 𝕜 (Fin n → 𝕜) (E n)).toEquiv
  continuous_toFun := continuous_sigma fun n => continuous_sigmaMk.comp
    (pointIndexedCoreHomeomorph 𝕜 (Fin n → 𝕜) (E n)).continuous
  continuous_invFun := continuous_sigma fun n => continuous_sigmaMk.comp
    (pointIndexedCoreHomeomorph 𝕜 (Fin n → 𝕜) (E n)).symm.continuous

/-- The reconstructed atlas is homeomorphic, over the base, to the disjoint union
of the original bundles. The fibre maps are the preferred-chart continuous linear
equivalences `pointIndexedCoreFiberEquiv`. -/
noncomputable def reconstructionHomeomorph :
    TotalSpace Unit (ofBundles 𝕜 r E).Fiber ≃ₜ Σ n : ℕ, TotalSpace (Fin n → 𝕜) (E n) :=
  (ofBundles 𝕜 r E).totalSpaceHomeomorph.symm.trans (gluedReconstructionHomeomorph 𝕜 r E)

/-- On a rank stratum reconstruction is the original preferred-chart fibre equivalence. -/
@[simp] theorem reconstructionHomeomorph_apply (p : TotalSpace Unit (ofBundles 𝕜 r E).Fiber) :
    reconstructionHomeomorph 𝕜 r E p =
      ⟨r p.proj, ⟨⟨p.proj, rfl⟩,
        pointIndexedCoreFiberEquiv 𝕜 (Fin (r p.proj) → 𝕜) (E (r p.proj)) ⟨p.proj, rfl⟩ p.2⟩⟩ := by
  -- The sigma equivalence applies the existing reconstruction on the selected stratum.
  exact congrArg (Sigma.mk (r p.proj))
    (pointIndexedCoreHomeomorph_apply 𝕜 (Fin (r p.proj) → 𝕜) (E (r p.proj)) _)

/-- The inverse comparison is the inverse preferred-chart fibre equivalence, followed
by the canonical inclusion of that stratum into the reconstructed total space. -/
@[simp] theorem reconstructionHomeomorph_symm_apply
    (n : ℕ) (p : TotalSpace (Fin n → 𝕜) (E n)) :
    (reconstructionHomeomorph 𝕜 r E).symm ⟨n, p⟩ =
      (ofBundles 𝕜 r E).totalSpaceHomeomorph
        ⟨n, ⟨p.proj, (pointIndexedCoreFiberEquiv 𝕜 (Fin n → 𝕜) (E n) p.proj).symm p.2⟩⟩ := by
  exact congrArg (fun q => (ofBundles 𝕜 r E).totalSpaceHomeomorph ⟨n, q⟩)
    (pointIndexedCoreHomeomorph_symm_apply 𝕜 (Fin n → 𝕜) (E n) p)

/-- The reconstruction comparison covers the identity map on the original base. -/
@[simp] theorem proj_reconstructionHomeomorph
    (p : TotalSpace Unit (ofBundles 𝕜 r E).Fiber) :
    (reconstructionHomeomorph 𝕜 r E p).2.proj.1 = p.proj := by
  rw [reconstructionHomeomorph_apply]

end Reconstruction
end FiniteRankAtlas
end TauCeti
