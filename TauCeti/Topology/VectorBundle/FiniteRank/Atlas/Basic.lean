/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homeomorph.Sigma
public import TauCeti.Topology.VectorBundle.Core.Basic
public import TauCeti.Topology.VectorBundle.FiniteRank.Glued

/-!
# Small variable-rank vector-bundle atlases

`TauCeti.FiniteRankAtlas` assembles point-indexed Mathlib vector-bundle cores on the clopen strata
of a locally constant natural-number rank, using only the base and scalar universes without
bounded-rank or finite-cover hypotheses. Instantiating `TauCeti.VariableRankBundle` equips
`TotalSpace Unit A.Fiber` with the glued stratum topology (`Atlas/Category.lean` and
`Atlas/Preadditive.lean` expose the induced preadditive category); `ofBundles` and
`reconstructionHomeomorph` encode actual stratum bundles via `TauCeti.pointIndexedCoreHomeomorph`.
-/

public section

open Bundle Topology

namespace TauCeti

universe u v w

variable (𝕜 : Type v) [NontriviallyNormedField 𝕜] (X : Type u) [TopologicalSpace X]

/-- A variable finite-rank bundle atlas, with charts indexed by the points of each clopen rank
stratum. All stored coordinate data are independent of any external fibre universe. -/
structure FiniteRankAtlas where
  /-- The locally constant, not necessarily bounded, rank. -/
  rank : LocallyConstant X ℕ
  /-- The coordinate bundle core on each rank stratum. -/
  charts (n : ℕ) : VectorBundleCore 𝕜 {x : X // rank x = n} (Fin n → 𝕜)
    {x : X // rank x = n}
  /-- Each point labels its own preferred chart. -/
  indexAt_eq (n : ℕ) (x : {x : X // rank x = n}) : (charts n).indexAt x = x

namespace FiniteRankAtlas

variable {𝕜 X} (A : FiniteRankAtlas 𝕜 X)

/-- The finite coordinate fibre of the reconstructed variable-rank bundle.
This is an abbreviation so the standard topological-module instances are available. -/
abbrev Fiber (x : X) := Fin (A.rank x) → 𝕜

/-- Small variable-rank coordinate atlases implement `VariableRankBundle` via their native stratum
`VectorBundleCore`s. -/
instance instVariableRankBundle :
    VariableRankBundle (FiniteRankAtlas 𝕜 X) 𝕜 X FiniteRankAtlas.Fiber where
  rank A := A.rank
  StratumFiber A n := (A.charts n).Fiber
  stratumFiberEquiv _ {_} y :=
    { toFun v i := v (Fin.cast y.2 i), map_add' _ _ := rfl, map_smul' _ _ := rfl
      invFun u i := u (Fin.cast y.2.symm i)
      left_inv _ := funext fun _ ↦ by simp, right_inv _ := funext fun _ ↦ by simp }

@[simp] theorem variableRankBundle_rank : VariableRankBundle.rank A = A.rank := by rfl
@[simp] theorem stratumFiberEquiv_apply {n : ℕ} (y : {x : X // VariableRankBundle.rank A x = n})
    (v : VariableRankBundle.StratumFiber A n y) (i : Fin (A.rank y.1)) :
    VariableRankBundle.stratumFiberEquiv A y v i = v (Fin.cast y.2 i) := by rfl
@[simp] theorem stratumFiberEquiv_symm_apply {n : ℕ}
    (y : {x : X // VariableRankBundle.rank A x = n}) (u : A.Fiber y.1) (i : Fin n) :
    (VariableRankBundle.stratumFiberEquiv A y).symm u i = u (Fin.cast y.2.symm i) := by rfl
@[simp] theorem stratumFiberEquiv_rfl_apply (x : X)
    (v : VariableRankBundle.StratumFiber A (VariableRankBundle.rank A x) ⟨x, rfl⟩) :
    VariableRankBundle.stratumFiberEquiv A ⟨x, rfl⟩ v = v := by rfl
@[simp] theorem stratumFiberEquiv_rfl_symm_apply (x : X) (u : A.Fiber x) :
    (VariableRankBundle.stratumFiberEquiv A ⟨x, rfl⟩).symm u = u := by rfl

/-- Equip `TotalSpace Unit A.Fiber` with the glued topology of the native stratum bundle cores. -/
instance : TopologicalSpace (TotalSpace Unit A.Fiber) :=
  VariableRankBundle.instTopologicalSpaceTotalSpace A

@[simp high] theorem totalSpaceHomeomorph_rfl_apply (x : X)
    (v : (A.charts (A.rank x)).Fiber ⟨x, rfl⟩) :
    VariableRankBundle.totalSpaceHomeomorph A ⟨A.rank x, ⟨⟨x, rfl⟩, v⟩⟩ = ⟨x, v⟩ :=
  VariableRankBundle.totalSpaceHomeomorph_apply A ⟨A.rank x, ⟨⟨x, rfl⟩, v⟩⟩
@[simp high] theorem totalSpaceHomeomorph_symm_apply (p : TotalSpace Unit A.Fiber) :
    (VariableRankBundle.totalSpaceHomeomorph A).symm p = ⟨A.rank p.proj, ⟨⟨p.proj, rfl⟩, p.2⟩⟩ :=
  VariableRankBundle.totalSpaceHomeomorph_symm_apply A p

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
@[expose, implicit_reducible]
noncomputable def ofBundles : FiniteRankAtlas 𝕜 X where
  rank := r
  charts n := pointIndexedCore 𝕜 (Fin n → 𝕜) (E n)
  indexAt_eq n := pointIndexedCore_indexAt 𝕜 (Fin n → 𝕜) (E n)

@[simp] theorem rank_ofBundles : (ofBundles 𝕜 r E).rank = r := by rfl
@[simp] theorem charts_ofBundles (n : ℕ) :
    (ofBundles 𝕜 r E).charts n = pointIndexedCore 𝕜 (Fin n → 𝕜) (E n) := by rfl

/-- The reconstructed atlas is homeomorphic, over the base, to the disjoint union of the original
stratum bundles via `pointIndexedCoreFiberEquiv` on each fibre. -/
noncomputable def reconstructionHomeomorph :
    TotalSpace Unit (ofBundles 𝕜 r E).Fiber ≃ₜ Σ n : ℕ, TotalSpace (Fin n → 𝕜) (E n) :=
  (VariableRankBundle.totalSpaceHomeomorph (ofBundles 𝕜 r E)).symm.trans
    (Homeomorph.sigmaCongrRight fun n ↦ pointIndexedCoreHomeomorph 𝕜 (Fin n → 𝕜) (E n))

/-- On a rank stratum reconstruction is the preferred-chart fibre equivalence. -/
@[simp] theorem reconstructionHomeomorph_apply (p : TotalSpace Unit (ofBundles 𝕜 r E).Fiber) :
    reconstructionHomeomorph 𝕜 r E p = ⟨r p.proj, ⟨⟨p.proj, rfl⟩,
      pointIndexedCoreFiberEquiv 𝕜 (Fin (r p.proj) → 𝕜) (E (r p.proj)) ⟨p.proj, rfl⟩ p.2⟩⟩ :=
  let h := (VariableRankBundle.totalSpaceHomeomorph (ofBundles 𝕜 r E)).symm
  let e := Homeomorph.sigmaCongrRight fun n ↦ pointIndexedCoreHomeomorph 𝕜 (Fin n → 𝕜) (E n)
  (Homeomorph.trans_apply h e p).trans
    ((congrArg e (VariableRankBundle.totalSpaceHomeomorph_symm_apply (ofBundles 𝕜 r E) p)).trans
      ((Homeomorph.sigmaCongrRight_apply _ _).trans (congrArg (Sigma.mk (r p.proj))
        (pointIndexedCoreHomeomorph_apply 𝕜 (Fin (r p.proj) → 𝕜) (E (r p.proj))
          ⟨⟨p.proj, rfl⟩, p.2⟩))))

/-- The inverse comparison applies the inverse preferred-chart fibre equivalence, followed by the
canonical inclusion of that stratum into the reconstructed total space. -/
@[simp] theorem reconstructionHomeomorph_symm_apply (n : ℕ) (p : TotalSpace (Fin n → 𝕜) (E n)) :
    (reconstructionHomeomorph 𝕜 r E).symm ⟨n, p⟩ =
      VariableRankBundle.totalSpaceHomeomorph (ofBundles 𝕜 r E)
        ⟨n, ⟨p.proj, (pointIndexedCoreFiberEquiv 𝕜 (Fin n → 𝕜) (E n) p.proj).symm p.2⟩⟩ :=
  let h := VariableRankBundle.totalSpaceHomeomorph (ofBundles 𝕜 r E)
  let f := fun m ↦ pointIndexedCoreHomeomorph 𝕜 (Fin m → 𝕜) (E m)
  (Homeomorph.symm_trans_apply h.symm (Homeomorph.sigmaCongrRight f) ⟨n, p⟩).trans
    ((congrFun (congrArg DFunLike.coe h.symm_symm) _).trans (congrArg h
      ((Homeomorph.sigmaCongrRight_symm_apply f ⟨n, p⟩).trans
        (congrArg (Sigma.mk n) (pointIndexedCoreHomeomorph_symm_apply 𝕜 (Fin n → 𝕜) (E n) p)))))

/-- The reconstruction comparison covers the identity map on the original base. -/
@[simp] theorem proj_reconstructionHomeomorph (p : TotalSpace Unit (ofBundles 𝕜 r E).Fiber) :
    (reconstructionHomeomorph 𝕜 r E p).2.proj.1 = p.proj := by rw [reconstructionHomeomorph_apply]

end Reconstruction
end FiniteRankAtlas
end TauCeti
