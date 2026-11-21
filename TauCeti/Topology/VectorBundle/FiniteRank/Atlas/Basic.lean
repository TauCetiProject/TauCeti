/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homeomorph.Sigma
public import TauCeti.Topology.VectorBundle.Core.Basic
public import TauCeti.Topology.VectorBundle.FiniteRank.Basic
public import TauCeti.Topology.VectorBundle.FiniteRank.Glued

/-!
# Small variable-rank vector-bundle atlases

`TauCeti.FiniteRankAtlas` assembles point-indexed Mathlib vector-bundle cores on the clopen strata
of a locally constant natural-number rank, using only the base and scalar universes without
bounded-rank or finite-cover hypotheses. `FiniteRankAtlas.stratumCore` packages each clopen rank
stratum's coordinate core as a `TauCeti.FiniteRankBundleCore`. Instantiating
`TauCeti.VariableRankBundle` equips `TotalSpace Unit A.Fiber` with the glued stratum topology
(`Atlas/Category.lean` and `Atlas/Preadditive.lean` expose the induced preadditive category);
`FiniteRankAtlas.chartBaseSet` exposes the open domain in `X` of the preferred stratum chart at
each base point, and `ofBundles` and `reconstructionHomeomorph` encode actual stratum bundles via
`TauCeti.pointIndexedCoreHomeomorph`.
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

/-- Package the point-indexed coordinate core on the rank-`n` clopen stratum of `A` as a
`FiniteRankBundleCore`. -/
-- Expose the rank projection so the dependent coordinate model reduces to `Fin n → 𝕜`.
@[expose, implicit_reducible]
def stratumCore (n : ℕ) : FiniteRankBundleCore 𝕜 {x : X // A.rank x = n} where
  rank := n
  core := A.charts n
  indexAt_eq := A.indexAt_eq n

/-- Rank of `A.stratumCore n`. -/
@[simp]
theorem rank_stratumCore (n : ℕ) : (A.stratumCore n).rank = n := (rfl)

/-- Underlying `VectorBundleCore` of `A.stratumCore n`. -/
@[simp]
theorem core_stratumCore (n : ℕ) : (A.stratumCore n).core = A.charts n := (rfl)

/-- Small variable-rank coordinate atlases implement `VariableRankBundle` via their native stratum
`VectorBundleCore`s. -/
instance instVariableRankBundle :
    VariableRankBundle (FiniteRankAtlas 𝕜 X) 𝕜 X FiniteRankAtlas.Fiber where
  rank A := A.rank
  StratumFiber A n := (A.charts n).Fiber
  stratumFiberEquiv _ {_} y :=
    { toFun v i := v (Fin.cast y.property i), map_add' _ _ := rfl, map_smul' _ _ := rfl
      invFun u i := u (Fin.cast y.property.symm i)
      left_inv _ := funext fun _ ↦ by simp, right_inv _ := funext fun _ ↦ by simp }

@[simp] theorem variableRankBundle_rank : VariableRankBundle.rank A = A.rank := by rfl
@[simp] theorem stratumFiberEquiv_apply {n : ℕ} (y : {x : X // VariableRankBundle.rank A x = n})
    (v : VariableRankBundle.StratumFiber A n y) (i : Fin (A.rank y.val)) :
    VariableRankBundle.stratumFiberEquiv A y v i = v (Fin.cast y.property i) := by rfl
@[simp] theorem stratumFiberEquiv_symm_apply {n : ℕ}
    (y : {x : X // VariableRankBundle.rank A x = n}) (u : A.Fiber y.val) (i : Fin n) :
    (VariableRankBundle.stratumFiberEquiv A y).symm u i = u (Fin.cast y.property.symm i) := by rfl
@[simp] theorem stratumFiberEquiv_rfl_apply (x : X)
    (v : VariableRankBundle.StratumFiber A (VariableRankBundle.rank A x) ⟨x, rfl⟩) :
    VariableRankBundle.stratumFiberEquiv A ⟨x, rfl⟩ v = v := by rfl
@[simp] theorem stratumFiberEquiv_rfl_symm_apply (x : X) (u : A.Fiber x) :
    (VariableRankBundle.stratumFiberEquiv A ⟨x, rfl⟩).symm u = u := by rfl

/-- The disjoint union of the native core total spaces. -/
abbrev GluedTotalSpace := VariableRankBundle.GluedTotalSpace A

/-- The projection of the disjoint union to the original base. -/
abbrev gluedProj (p : A.GluedTotalSpace) : X := VariableRankBundle.gluedProj A p

theorem gluedProj_mk (n : ℕ) (p : (A.charts n).TotalSpace) :
    A.gluedProj ⟨n, p⟩ = p.proj.val :=
  VariableRankBundle.gluedProj_mk A n p

/-- The glued projection is continuous, since each stratum projection is continuous. -/
@[continuity, fun_prop] theorem continuous_gluedProj : Continuous A.gluedProj :=
  VariableRankBundle.continuous_gluedProj A

/-- The glued projection is open: the rank strata are open in the base. -/
theorem isOpenMap_gluedProj : IsOpenMap A.gluedProj :=
  VariableRankBundle.isOpenMap_gluedProj A

/-- Equip `TotalSpace Unit A.Fiber` with the glued topology of the native stratum bundle cores. -/
instance : TopologicalSpace (TotalSpace Unit A.Fiber) :=
  VariableRankBundle.instTopologicalSpaceTotalSpace A

/-- Reindexing the core total spaces gives the reconstructed bundle topology. -/
abbrev totalSpaceHomeomorph : A.GluedTotalSpace ≃ₜ TotalSpace Unit A.Fiber :=
  VariableRankBundle.totalSpaceHomeomorph A

theorem totalSpaceHomeomorph_apply (p : A.GluedTotalSpace) :
    A.totalSpaceHomeomorph p =
      ⟨p.snd.proj.val, fun i => p.snd.snd (Fin.cast p.snd.proj.property i)⟩ := by
  rw [VariableRankBundle.totalSpaceHomeomorph_apply]; rfl

@[simp high] theorem totalSpaceHomeomorph_rfl_apply (x : X)
    (v : (A.charts (A.rank x)).Fiber ⟨x, rfl⟩) :
    VariableRankBundle.totalSpaceHomeomorph A ⟨A.rank x, ⟨⟨x, rfl⟩, v⟩⟩ = ⟨x, v⟩ :=
  VariableRankBundle.totalSpaceHomeomorph_apply A ⟨A.rank x, ⟨⟨x, rfl⟩, v⟩⟩

@[simp high] theorem totalSpaceHomeomorph_symm_apply (p : TotalSpace Unit A.Fiber) :
    A.totalSpaceHomeomorph.symm p = ⟨A.rank p.proj, ⟨⟨p.proj, rfl⟩, p.snd⟩⟩ :=
  VariableRankBundle.totalSpaceHomeomorph_symm_apply A p

/-- The reconstructed total-space projection is continuous. -/
@[continuity, fun_prop] theorem continuous_proj :
    Continuous (TotalSpace.proj : TotalSpace Unit A.Fiber → X) :=
  VariableRankBundle.continuous_proj A

/-- The reconstructed total-space projection is open. -/
theorem isOpenMap_proj : IsOpenMap (TotalSpace.proj : TotalSpace Unit A.Fiber → X) :=
  VariableRankBundle.isOpenMap_proj A

/-- Each native core total space is an open subspace of the reconstruction. -/
theorem isOpenEmbedding_stratum (n : ℕ) :
    IsOpenEmbedding (fun p : (A.charts n).TotalSpace => A.totalSpaceHomeomorph ⟨n, p⟩) :=
  VariableRankBundle.isOpenEmbedding_stratum A n

/-- The image of the `n`th core total space is exactly the rank-`n` part of the
reconstructed total space. -/
theorem range_stratum (n : ℕ) :
    Set.range (fun p : (A.charts n).TotalSpace => A.totalSpaceHomeomorph ⟨n, p⟩) =
      {p : TotalSpace Unit A.Fiber | A.rank p.proj = n} :=
  VariableRankBundle.range_stratum A n

section Continuity

variable {Y : Type*} [TopologicalSpace Y] {b : Y → X}

/-- A map into a reconstructed total space is continuous exactly when its restrictions
to the rank strata, read in the native core total spaces, are continuous. -/
theorem continuous_mk_iff_rankStrata (hb : Continuous b) (s : ∀ y, A.Fiber (b y)) :
    Continuous (fun y => (⟨b y, s y⟩ : TotalSpace Unit A.Fiber)) ↔
      ∀ n : ℕ, Continuous (fun y : {y : Y // A.rank (b y) = n} =>
        (⟨⟨b y, y.property⟩, fun i => s y (Fin.cast y.property.symm i)⟩ :
          (A.charts n).TotalSpace)) :=
  VariableRankBundle.continuous_mk_iff_rankStrata A hb s

/-- The zero section of a variable-rank atlas is continuous. -/
@[fun_prop]
theorem continuous_zeroSection :
    Continuous (fun x => (⟨x, 0⟩ : TotalSpace Unit A.Fiber)) :=
  VariableRankBundle.continuous_zeroSection A

end Continuity

section ChartBaseSet

/-- The open domain in `X` of the preferred chart of `A` centred at `z`, lying inside the clopen
stratum `{x : X | A.rank x = A.rank z}`. -/
def chartBaseSet (z : X) : Set X :=
  Subtype.val '' (A.charts (A.rank z)).baseSet ⟨z, rfl⟩

theorem chartBaseSet_def (z : X) :
    A.chartBaseSet z = Subtype.val '' (A.charts (A.rank z)).baseSet ⟨z, rfl⟩ := (rfl)

variable {A} in
/-- Membership in `A.chartBaseSet z` means matching rank with `z` and membership in the stratum
chart at `z`. -/
theorem mem_chartBaseSet_iff {z x : X} :
    x ∈ A.chartBaseSet z ↔
      ∃ hx : A.rank x = A.rank z, ⟨x, hx⟩ ∈ (A.charts (A.rank z)).baseSet ⟨z, rfl⟩ := by
  constructor
  · rintro ⟨⟨y, hy⟩, hmem, rfl⟩
    exact ⟨hy, hmem⟩
  · rintro ⟨hx, hmem⟩
    exact ⟨⟨x, hx⟩, hmem, rfl⟩

variable {A} in
/-- Every point in the preferred chart centred at `z` has the same rank as `z`. -/
theorem rank_eq_of_mem_chartBaseSet {z x : X} (hx : x ∈ A.chartBaseSet z) :
    A.rank x = A.rank z :=
  (mem_chartBaseSet_iff.1 hx).1

/-- Each preferred chart domain `A.chartBaseSet z` is open in the base `X`. -/
theorem isOpen_chartBaseSet (z : X) : IsOpen (A.chartBaseSet z) :=
  (A.rank.isLocallyConstant.isOpen_fiber (A.rank z)).isOpenEmbedding_subtypeVal.isOpenMap _
    ((A.charts (A.rank z)).isOpen_baseSet ⟨z, rfl⟩)

/-- Every base point belongs to the domain of its own preferred chart. -/
@[simp] theorem mem_chartBaseSet_self (z : X) : z ∈ A.chartBaseSet z :=
  mem_chartBaseSet_iff.2
    ⟨rfl, by simpa only [A.indexAt_eq] using (A.charts (A.rank z)).mem_baseSet_at ⟨z, rfl⟩⟩

/-- On the rank-`m` stratum, the domain of the chart at `z` is the preimage of `A.chartBaseSet z.1`
under `Subtype.val`. -/
theorem baseSet_charts {m : ℕ} (z : {x : X // A.rank x = m}) :
    (A.charts m).baseSet z = Subtype.val ⁻¹' A.chartBaseSet z.val := by
  rcases z with ⟨z, rfl⟩
  ext ⟨x, hx⟩
  simp [mem_chartBaseSet_iff, hx]

variable {A} in
/-- A point of the rank-`m` stratum belongs to the stratum chart at `z` if and only if its
underlying point in `X` belongs to `A.chartBaseSet z.1`. -/
theorem mem_baseSet_charts_iff {m : ℕ} {z x : {x : X // A.rank x = m}} :
    x ∈ (A.charts m).baseSet z ↔ x.val ∈ A.chartBaseSet z.val := by
  rw [A.baseSet_charts z, Set.mem_preimage]

end ChartBaseSet

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
-- Expose the rank and chart projections so dependent coordinate fibres reduce at implicit level.
@[expose, implicit_reducible] noncomputable def ofBundles : FiniteRankAtlas 𝕜 X where
  rank := r
  charts n := pointIndexedCore 𝕜 (Fin n → 𝕜) (E n)
  indexAt_eq n := pointIndexedCore_indexAt 𝕜 (Fin n → 𝕜) (E n)

@[simp] theorem rank_ofBundles : (ofBundles 𝕜 r E).rank = r := (rfl)

@[simp] theorem charts_ofBundles (n : ℕ) :
    (ofBundles 𝕜 r E).charts n = pointIndexedCore 𝕜 (Fin n → 𝕜) (E n) := (rfl)

/-- The preferred chart domain of `ofBundles 𝕜 r E` at `z` is the image in `X` of the preferred
stratum trivialization domain at `z`. -/
@[simp] theorem chartBaseSet_ofBundles (z : X) :
    (ofBundles 𝕜 r E).chartBaseSet z =
      Subtype.val '' (trivializationAt (Fin (r z) → 𝕜) (E (r z)) ⟨z, rfl⟩).baseSet := by
  rw [chartBaseSet_def]
  dsimp only [ofBundles]
  rw [VectorBundleCore.baseSet_at, pointIndexedCore_localTriv_baseSet]

/-- The reconstructed atlas is homeomorphic, over the base, to the disjoint union
of the original bundles. The fibre maps are the preferred-chart continuous linear
equivalences `pointIndexedCoreFiberEquiv`. -/
noncomputable def reconstructionHomeomorph :
    TotalSpace Unit (ofBundles 𝕜 r E).Fiber ≃ₜ Σ n : ℕ, TotalSpace (Fin n → 𝕜) (E n) :=
  (VariableRankBundle.totalSpaceHomeomorph (ofBundles 𝕜 r E)).symm.trans
    (Homeomorph.sigmaCongrRight fun n ↦ pointIndexedCoreHomeomorph 𝕜 (Fin n → 𝕜) (E n))

/-- On a rank stratum reconstruction is the original preferred-chart fibre equivalence. -/
@[simp] theorem reconstructionHomeomorph_apply (p : TotalSpace Unit (ofBundles 𝕜 r E).Fiber) :
    reconstructionHomeomorph 𝕜 r E p =
      ⟨r p.proj, ⟨⟨p.proj, rfl⟩,
        pointIndexedCoreFiberEquiv 𝕜 (Fin (r p.proj) → 𝕜) (E (r p.proj)) ⟨p.proj, rfl⟩ p.snd⟩⟩ := by
  simp only [reconstructionHomeomorph, Homeomorph.trans_apply, Homeomorph.sigmaCongrRight_apply,
    VariableRankBundle.totalSpaceHomeomorph_symm_apply]
  exact congrArg (Sigma.mk (r p.proj))
    (pointIndexedCoreHomeomorph_apply 𝕜 (Fin (r p.proj) → 𝕜) (E (r p.proj)) ⟨⟨p.proj, rfl⟩, p.snd⟩)

/-- The inverse comparison is the inverse preferred-chart fibre equivalence, followed
by the canonical inclusion of that stratum into the reconstructed total space. -/
@[simp] theorem reconstructionHomeomorph_symm_apply
    (n : ℕ) (p : TotalSpace (Fin n → 𝕜) (E n)) :
    (reconstructionHomeomorph 𝕜 r E).symm ⟨n, p⟩ =
      VariableRankBundle.totalSpaceHomeomorph (ofBundles 𝕜 r E)
        ⟨n, ⟨p.proj, (pointIndexedCoreFiberEquiv 𝕜 (Fin n → 𝕜) (E n) p.proj).symm p.snd⟩⟩ := by
  simp only [reconstructionHomeomorph, Homeomorph.symm_trans_apply, Homeomorph.symm_symm,
    Homeomorph.sigmaCongrRight_symm_apply]
  exact congrArg (fun q ↦ VariableRankBundle.totalSpaceHomeomorph (ofBundles 𝕜 r E) ⟨n, q⟩)
    (pointIndexedCoreHomeomorph_symm_apply 𝕜 (Fin n → 𝕜) (E n) p)

/-- The reconstruction comparison covers the identity map on the original base. -/
@[simp] theorem proj_reconstructionHomeomorph
    (p : TotalSpace Unit (ofBundles 𝕜 r E).Fiber) :
    (reconstructionHomeomorph 𝕜 r E p).snd.proj.val = p.proj := by
  rw [reconstructionHomeomorph_apply]

end Reconstruction
end FiniteRankAtlas
end TauCeti
