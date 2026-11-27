/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.ImplicitAtlas.Boundary
public import TauCeti.Topology.Stratification.CellLike

/-!
# Implicit atlases with cell-like stratification

Compactified moduli spaces of pseudoholomorphic curves have corners: a stratum of broken
configurations can lie in the closure of several codimension-one strata, as the four edges of a
square meet at its vertices. Pardon records this structure by a stratification of the base and of
every thickening of an implicit atlas by a poset of faces. This file defines such a structure on an
implicit atlas with boundary (`TauCeti.ImplicitAtlasWithBoundary`).

Let `S` be a poset with a dimension function `dim : S → ℤ` and a lower set `∂S ⊆ S` of boundary
faces. A *cell-like stratification* of an implicit atlas with boundary `𝒜` of virtual dimension `d`
on `(X, ∂X)` (`TauCeti.ImplicitAtlasWithBoundary.CellLikeStratification`, Pardon,
Definition 6.1.6) consists of stratifications `σ_I : X_I → S` of all the thickenings
(`TauCeti.IsStratification`) such that

* `σ_I` is invariant under `Γ_I`, and `∂X_I = σ_I⁻¹(∂S)`;
* the footprint maps are compatible with the stratifications: `σ_I ∘ ψ_IJ = σ_J` on the zero set
  `Z_IJ`, so that the stratification of `Z_IJ` is pulled back from that of `X_I`;
* on the regular locus `X_I^reg` the stratification is cell-like with the dimensions shifted by the
  rank `m_I = ∑_(α ∈ I) dim E_α` of the obstruction space (`TauCeti.IsCellLikeOn`): every closed
  stratum `X_I^reg ∩ X_I^≤s` is a topological manifold of dimension `dim s + m_I` with boundary
  `X_I^reg ∩ X_I^<s`;
* over `ψ_IJ⁻¹(X_I^reg)` the stratification of `X_J` is pulled back from a cell-like stratification
  of the first factor of a local product model: near every such point there is a homeomorphism of
  an open subset of `X_J` onto an open subset of a product `F × E_(J \ I)`, whose second coordinate
  is the extra obstruction `s_(J \ I)`, and a cell-like stratification `τ` of `F` for the
  dimensions `dim s + m_I`, so that every closed stratum `(F^≤s, F^<s)` is a manifold with boundary
  of dimension `dim s + m_I`, with `σ_J = τ ∘ pr₁ ∘ e` on the chart.

The base `X` is stratified by `σ_∅` through the identification `X_∅ ≃ X`
(`TauCeti.ImplicitAtlasWithBoundary.CellLikeStratification.baseStratum`), with boundary
`∂X = σ⁻¹(∂S)`. Unlike the conditions on the regular loci, the zero-fibre compatibility also
constrains the thickenings outside their regular loci.

* **Dimensions.** Every point of `X` lies in the image of a regular zero of some thickening `X_I`,
  so its stratum `s` satisfies `dim s + m_I ≥ 0` for some `I`
  (`TauCeti.ImplicitAtlasWithBoundary.CellLikeStratification.exists_nonneg_baseStratum`). A
  stratum `s` with `dim s + m_I < 0` meets no regular point of `X_I`, and a regular point of `X_I`
  lying strictly below a stratum `t` forces `dim t + m_I ≥ 1`.
* **The interval.** The interval atlas `[0, 1]` stratified by `{0} < (0, 1) > {1}`, with
  dimensions `0`, `1`, `0` and the two endpoints as boundary faces, is a cell-like stratified atlas
  (`TauCeti.ImplicitAtlasWithBoundary.unitIntervalCellLikeStratification`, in
  `TauCeti.Topology.ImplicitAtlas.Examples`).

Pardon takes the poset `S` finite; nothing here uses finiteness, which enters through the closedness
of the preimages of lower sets (`TauCeti.IsStratification.isClosed_preimage`).

## References

* J. Pardon, *An algebraic approach to virtual fundamental cycles on moduli spaces of
  pseudo-holomorphic curves*, Geom. Topol. 20 (2016), 779–1034, Definitions 6.1.1, 6.1.2 and 6.1.6.
-/

public section

open Set Topology

universe u

namespace TauCeti

variable {A : Type*} [DecidableEq A] {Γ : A → Type*} [∀ α, Group (Γ α)] [∀ α, Finite (Γ α)]
  {E : A → Type*} [∀ α, NormedAddCommGroup (E α)] [∀ α, NormedSpace ℝ (E α)]
  [∀ α, FiniteDimensional ℝ (E α)] {ρ : ∀ α, Representation ℝ (Γ α) (E α)}
  {T : Finset A → Type u} [∀ I, TopologicalSpace (T I)] [∀ I, T2Space (T I)]
  {act : ∀ I : Finset A, ((α : I) → Γ α) →* (T I ≃ₜ T I)}
  {X : Type*} [TopologicalSpace X] {bd : Set X} {d : ℤ}

namespace ImplicitAtlasWithBoundary

/-- A **cell-like stratification** of an implicit atlas with boundary `𝒜` by a poset `S` with
dimension function `dim` and boundary faces `∂S` (Pardon, Definition 6.1.6): stratifications
`σ_I : X_I → S` of the thickenings, invariant under `Γ_I`, with `∂X_I = σ_I⁻¹(∂S)`, compatible
with the footprint maps on the zero sets, cell-like on the regular loci for the dimensions
`dim s + m_I`, and pulled back from a cell-like stratification of the first factor of a local
product model of the extra obstruction over `ψ_IJ⁻¹(X_I^reg)`. -/
@[ext]
structure CellLikeStratification (𝒜 : ImplicitAtlasWithBoundary Γ E ρ T act X bd d)
    (S : Type*) [Preorder S] (dim : S → ℤ) (bdS : LowerSet S) where
  /-- The stratification `σ_I : X_I → S` of the thickening `X_I`. -/
  stratum : ∀ I : Finset A, T I → S
  isStratification_stratum : ∀ I : Finset A, IsStratification (stratum I)
  stratum_act : ∀ (I : Finset A) (g : (α : I) → Γ α) (x : T I), stratum I (act I g x) = stratum I x
  /-- The boundary `∂X_I` is the union of the boundary strata. -/
  boundary_eq_preimage : ∀ I : Finset A, 𝒜.boundary I = stratum I ⁻¹' bdS
  /-- Zero-fibre compatibility: `σ_I ∘ ψ_IJ = σ_J` on `Z_IJ`. -/
  stratum_footprintMap : ∀ ⦃I J : Finset A⦄ (h : I ⊆ J) (x : kuranishiZeroSet 𝒜.kuranishi I J),
    stratum I (𝒜.footprintMap h x) = stratum J x.val
  /-- On the regular locus the stratification is cell-like for the dimensions `dim s + m_I`. -/
  isCellLikeOn_regLocus : ∀ I : Finset A, IsCellLikeOn (stratum I) (𝒜.regLocus I)
    fun s ↦ dim s + ∑ α ∈ I, (Module.finrank ℝ (E α) : ℤ)
  /-- Over `ψ_IJ⁻¹(X_I^reg)` the stratification of `X_J` is pulled back from a cell-like
  stratification `τ` of the first factor of a local product model `F × E_(J \ I)` whose second
  coordinate is `s_(J \ I)`, for the dimensions `dim s + m_I`. -/
  exists_openPartialHomeomorph_stratum : ∀ ⦃I J : Finset A⦄ (h : I ⊆ J)
    (x : kuranishiZeroSet 𝒜.kuranishi I J), 𝒜.footprintMap h x ∈ 𝒜.regLocus I →
      ∃ (F : Type u) (_ : TopologicalSpace F) (τ : F → S),
        IsCellLike τ (fun s ↦ dim s + ∑ α ∈ I, (Module.finrank ℝ (E α) : ℤ)) ∧
        ∃ e : OpenPartialHomeomorph (T J) (F × ((α : ↥(J \ I)) → E α)),
          x.val ∈ e.source ∧ (∀ y ∈ e.source, (e y).2 = kuranishiSdiff 𝒜.kuranishi I J y) ∧
            ∀ y ∈ e.source, stratum J y = τ (e y).1

namespace CellLikeStratification

variable {𝒜 : ImplicitAtlasWithBoundary Γ E ρ T act X bd d} {S : Type*} [Preorder S]
  {dim : S → ℤ} {bdS : LowerSet S} (σ : 𝒜.CellLikeStratification S dim bdS)

/-- A point of a thickening lies on its boundary exactly when its stratum is a boundary face. -/
theorem mem_boundary_iff {I : Finset A} {x : T I} : x ∈ 𝒜.boundary I ↔ σ.stratum I x ∈ bdS := by
  rw [σ.boundary_eq_preimage]
  rfl

/-- The stratification of the base `X`, through the identification `X_∅ ≃ X`. -/
def baseStratum (y : X) : S :=
  σ.stratum ∅ (𝒜.baseHomeomorph.symm y)

theorem baseStratum_apply (y : X) : σ.baseStratum y = σ.stratum ∅ (𝒜.baseHomeomorph.symm y) :=
  (rfl)

/-- The base stratification is a stratification of `X`. -/
theorem isStratification_baseStratum : IsStratification σ.baseStratum :=
  (σ.isStratification_stratum ∅).comp 𝒜.baseHomeomorph.symm.continuous

/-- The boundary `∂X` of the base is the union of its boundary strata. -/
theorem preimage_baseStratum_boundary : σ.baseStratum ⁻¹' bdS = bd := by
  ext y
  simp [baseStratum_apply, ← σ.mem_boundary_iff, 𝒜.boundary_empty]

/-- The stratum of the footprint of a point of `Z_∅I` is its stratum in `X_I`. -/
theorem baseStratum_footprintMap {I : Finset A} (x : kuranishiZeroSet 𝒜.kuranishi ∅ I) :
    σ.baseStratum (𝒜.baseHomeomorph (𝒜.footprintMap (Finset.empty_subset I) x)) =
      σ.stratum I x.val := by
  rw [baseStratum_apply, Homeomorph.symm_apply_apply, σ.stratum_footprintMap]

/-- A stratum `s` with `dim s + m_I < 0` meets no regular point of `X_I`. -/
theorem regLocus_inter_preimage_Iic_eq_empty {I : Finset A} {s : S}
    (hs : dim s + ∑ α ∈ I, (Module.finrank ℝ (E α) : ℤ) < 0) :
    𝒜.regLocus I ∩ σ.stratum I ⁻¹' Iic s = ∅ :=
  (σ.isCellLikeOn_regLocus I).inter_preimage_Iic_eq_empty hs

/-- The stratum of a regular point of `X_I` has nonnegative shifted dimension `dim s + m_I`. -/
theorem nonneg_of_mem_regLocus {I : Finset A} {x : T I} (hx : x ∈ 𝒜.regLocus I) :
    0 ≤ dim (σ.stratum I x) + ∑ α ∈ I, (Module.finrank ℝ (E α) : ℤ) :=
  (σ.isCellLikeOn_regLocus I).nonneg hx

/-- A regular point of `X_I` lying strictly below a stratum `t` is a boundary point of the closed
stratum of `t`, so `dim t + m_I ≥ 1`. -/
theorem one_le_of_mem_regLocus_of_lt {I : Finset A} {x : T I} (hx : x ∈ 𝒜.regLocus I) {t : S}
    (ht : σ.stratum I x < t) : 1 ≤ dim t + ∑ α ∈ I, (Module.finrank ℝ (E α) : ℤ) :=
  (σ.isCellLikeOn_regLocus I).one_le_of_lt hx ht

/-- **Every point lies in a stratum of nonnegative shifted dimension.** The stratum `s` of a point
of the base satisfies `dim s + m_I ≥ 0` for some finite set of indices `I`: the point is the
footprint of a regular zero of `X_I`. -/
theorem exists_nonneg_baseStratum (y : X) :
    ∃ I : Finset A, 0 ≤ dim (σ.baseStratum y) + ∑ α ∈ I, (Module.finrank ℝ (E α) : ℤ) := by
  obtain ⟨I, x, hx, rfl⟩ := 𝒜.exists_footprintMap_eq y
  exact ⟨I, σ.baseStratum_footprintMap x ▸ σ.nonneg_of_mem_regLocus hx⟩

end CellLikeStratification

end ImplicitAtlasWithBoundary

end TauCeti
