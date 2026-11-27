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
* **Restricted atlases.** For a finite poset `S` and a stratum `s`, the closed strata `X_I^≤s` of
  the thickenings form a closed subthickening
  (`TauCeti.ImplicitAtlasWithBoundary.CellLikeStratification.isClosedSubthickening_preimage_Iic`),
  and the restriction to it, with boundaries the open-boundary strata `X_I^<s`, is an implicit
  atlas with boundary of virtual dimension `dim s` on `(X^≤s, X^<s)`
  (`TauCeti.ImplicitAtlasWithBoundary.CellLikeStratification.restrictAtlas`, Pardon,
  Definition 6.1.6). Its product charts read the closed stratum `s` of the first factor of a
  cell-like product model through its charts as a manifold with boundary
  (`TauCeti.IsManifoldBoundaryPair.exists_openPartialHomeomorph_prod`). It is cell-like stratified
  by `(S^≤s, S^<s)`
  (`TauCeti.ImplicitAtlasWithBoundary.CellLikeStratification.restrictCellLikeStratification`).
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

/-! ### Restricted atlases on the closed strata -/

/-- The closed strata `X_I^≤s` of the thickenings form a closed subthickening of the atlas: they
are closed, invariant, and `ψ_IJ⁻¹(X_I^≤s) = Z_IJ ∩ X_J^≤s` by the zero-fibre compatibility. -/
theorem isClosedSubthickening_preimage_Iic (s : S) :
    𝒜.toCore.IsClosedSubthickening fun I ↦ σ.stratum I ⁻¹' Iic s where
  isClosed I := isStratification_iff.1 (σ.isStratification_stratum I) s
  act_mem I g x hx := by rwa [mem_preimage, σ.stratum_act]
  footprintMap_mem_iff I J h x := by rw [mem_preimage, mem_preimage, σ.stratum_footprintMap]

/-- The closed stratum `X_∅^≤s` is the closed stratum `X^≤s` of the base, through `X_∅ ≃ₜ X`. -/
theorem preimage_stratum_empty_Iic (s : S) :
    σ.stratum ∅ ⁻¹' Iic s = 𝒜.baseHomeomorph ⁻¹' (σ.baseStratum ⁻¹' Iic s) := by
  ext x
  simp [baseStratum_apply]

variable [Finite S]

/-- **The restricted atlas on a closed stratum** (Pardon, Definition 6.1.6). For a stratum `s`,
the closed strata `X_I^≤s` of the thickenings, with the restricted actions, Kuranishi maps,
regular loci and footprint maps and with boundaries the open-boundary strata `X_I^<s`, form an
implicit atlas with boundary of virtual dimension `dim s` on `(X^≤s, X^<s)`, with the same isotropy
groups and obstruction spaces. Its product charts are those of the cell-like local product models,
restricted to the closed stratum of their first factor and read through its charts as a manifold
with boundary (`TauCeti.IsManifoldBoundaryPair.exists_openPartialHomeomorph_prod`). -/
noncomputable def restrictAtlas (s : S) :
    ImplicitAtlasWithBoundary Γ E ρ (fun I ↦ σ.stratum I ⁻¹' Iic s)
      (ImplicitAtlas.restrictAct act _ (σ.isClosedSubthickening_preimage_Iic s).act_mem)
      (σ.baseStratum ⁻¹' Iic s) (Subtype.val ⁻¹' (σ.baseStratum ⁻¹' Iio s)) (dim s) where
  toCore := 𝒜.toCore.restrictThickening (σ.isClosedSubthickening_preimage_Iic s) _
    (σ.preimage_stratum_empty_Iic s)
  boundary I := Subtype.val ⁻¹' (σ.stratum I ⁻¹' Iio s)
  isClosed_boundary I :=
    ((σ.isStratification_stratum I).isClosed_preimage_Iio s).preimage continuous_subtypeVal
  act_mem_boundary I g x hx := by
    rwa [mem_preimage, ImplicitAtlas.coe_restrictAct_apply, mem_preimage, σ.stratum_act]
  boundary_empty := by
    ext x
    simp [baseStratum_apply]
  footprintMap_mem_boundary_iff I J h x := by
    simp [σ.stratum_footprintMap]
  exists_openPartialHomeomorph I J h x hx := by
    simp only [ImplicitAtlas.Core.regLocus_restrictThickening, mem_preimage,
      ImplicitAtlas.Core.coe_footprintMap_restrictThickening] at hx
    obtain ⟨F, _, τ, hτ, e, hxe, he, hστ⟩ := σ.exists_openPartialHomeomorph_stratum h _ hx
    have hkur : ∀ y ∈ e.source, ∀ hy : σ.stratum J y ≤ s, (e y).2 =
        kuranishiSdiff (𝒜.toCore.restrictThickening (σ.isClosedSubthickening_preimage_Iic s) _
          (σ.preimage_stratum_empty_Iic s)).kuranishi I J ⟨y, hy⟩ := fun y hy _ ↦ by
      rw [he y hy]
      ext α
      simp
    rcases (hτ.isManifoldBoundaryPair s).exists_openPartialHomeomorph_prod e
      (P := σ.stratum J ⁻¹' Iic s) (Q := σ.stratum J ⁻¹' Iio s) (fun y hy ↦ by simp [hστ y hy])
      (fun y hy ↦ by simp [hστ y hy]) hxe x.val.property with
      ⟨m, hm, c, hcx, hce, hcQ, hc⟩ | ⟨m, hm, c, hcx, hce, hcQ, hc⟩
    · exact Or.inl ⟨m, hm, c, hcx, hcQ, fun y hy ↦ by rw [hc y hy, hkur y (hce hy) y.property]⟩
    · exact Or.inr ⟨m, hm, c, hcx, hcQ, fun y hy ↦ by rw [hc y hy, hkur y (hce hy) y.property]⟩

variable (s : S)

/-- The base identification of the restricted atlas on `X^≤s` is that of the atlas. -/
@[simp]
theorem coe_baseHomeomorph_restrictAtlas (x : σ.stratum ∅ ⁻¹' Iic s) :
    ((σ.restrictAtlas s).baseHomeomorph x : X) = 𝒜.baseHomeomorph x :=
  ImplicitAtlas.Core.coe_baseHomeomorph_restrictThickening
    (σ.isClosedSubthickening_preimage_Iic s) (σ.preimage_stratum_empty_Iic s) x

/-- The Kuranishi maps of the restricted atlas on `X^≤s` are the restrictions of those of the
atlas. -/
@[simp]
theorem kuranishi_restrictAtlas (I : Finset A) (α : I) (x : σ.stratum I ⁻¹' Iic s) :
    (σ.restrictAtlas s).kuranishi I α x = 𝒜.kuranishi I α x :=
  ImplicitAtlas.Core.kuranishi_restrictThickening
    (σ.isClosedSubthickening_preimage_Iic s) (σ.preimage_stratum_empty_Iic s) I α x

/-- The zero sets of the restricted atlas on `X^≤s` are the zero sets of the atlas intersected
with the closed strata. -/
theorem mem_kuranishiZeroSet_restrictAtlas {I J : Finset A} {x : σ.stratum J ⁻¹' Iic s} :
    x ∈ kuranishiZeroSet (σ.restrictAtlas s).kuranishi I J ↔
      (x : T J) ∈ kuranishiZeroSet 𝒜.kuranishi I J :=
  ImplicitAtlas.Core.mem_kuranishiZeroSet_restrictThickening
    (σ.isClosedSubthickening_preimage_Iic s) (σ.preimage_stratum_empty_Iic s)

/-- The regular loci of the restricted atlas on `X^≤s` are the regular loci of the atlas
intersected with the closed strata. -/
@[simp]
theorem regLocus_restrictAtlas (I : Finset A) :
    (σ.restrictAtlas s).regLocus I = Subtype.val ⁻¹' 𝒜.regLocus I :=
  ImplicitAtlas.Core.regLocus_restrictThickening
    (σ.isClosedSubthickening_preimage_Iic s) (σ.preimage_stratum_empty_Iic s) I

/-- The footprint maps of the restricted atlas on `X^≤s` are the restrictions of those of the
atlas. -/
@[simp]
theorem coe_footprintMap_restrictAtlas {I J : Finset A} (h : I ⊆ J)
    (x : kuranishiZeroSet (σ.restrictAtlas s).kuranishi I J) :
    ((σ.restrictAtlas s).footprintMap h x : T I) =
      𝒜.footprintMap h ⟨x.val, (σ.mem_kuranishiZeroSet_restrictAtlas s).1 x.property⟩ :=
  ImplicitAtlas.Core.coe_footprintMap_restrictThickening
    (σ.isClosedSubthickening_preimage_Iic s) (σ.preimage_stratum_empty_Iic s) h x

/-- The regular footprints of the restricted atlas on `X^≤s` are the traces on `X^≤s` of the
regular footprints of the atlas. -/
@[simp]
theorem footprint_restrictAtlas (I : Finset A) :
    (σ.restrictAtlas s).footprint I = Subtype.val ⁻¹' 𝒜.footprint I :=
  ImplicitAtlas.Core.footprint_restrictThickening
    (σ.isClosedSubthickening_preimage_Iic s) (σ.preimage_stratum_empty_Iic s) I

/-- The boundaries of the restricted atlas on `X^≤s` are the open-boundary strata `X_I^<s`. -/
@[simp]
theorem boundary_restrictAtlas (I : Finset A) :
    (σ.restrictAtlas s).boundary I = Subtype.val ⁻¹' (σ.stratum I ⁻¹' Iio s) :=
  (rfl)

/-- **The restricted stratification** (Pardon, Definition 6.1.6). The restricted atlas on
`(X^≤s, X^<s)` is cell-like stratified by `(S^≤s, S^<s)`: each closed stratum `X_I^≤s` is
stratified by `S^≤s` through `σ_I`, with the dimensions of `S`. Its product models are the
cell-like product models of `σ`, restricted to the closed stratum `s` of their first factor. -/
noncomputable def restrictCellLikeStratification :
    (σ.restrictAtlas s).CellLikeStratification (Iic s) (fun t ↦ dim t)
      (LowerSet.Iio ⟨s, le_rfl⟩) where
  stratum I := (Iic s).restrictPreimage (σ.stratum I)
  isStratification_stratum I := (σ.isStratification_stratum I).restrictPreimage _
  stratum_act I g x := Subtype.ext <| by
    simp [σ.stratum_act]
  boundary_eq_preimage I := by
    ext x
    simp [← Subtype.coe_lt_coe]
  stratum_footprintMap I J h x := Subtype.ext <| by
    simp [σ.stratum_footprintMap]
  isCellLikeOn_regLocus I := by
    simpa using (σ.isCellLikeOn_regLocus I).restrictPreimage (IsLowerSet.Iic s)
  exists_openPartialHomeomorph_stratum I J h x hx := by
    simp only [regLocus_restrictAtlas, mem_preimage, coe_footprintMap_restrictAtlas] at hx
    obtain ⟨F, _, τ, hτ, e, hxe, he, hστ⟩ := σ.exists_openPartialHomeomorph_stratum h _ hx
    have hP : ∀ y ∈ e.source, y ∈ σ.stratum J ⁻¹' Iic s ↔ (e y).1 ∈ τ ⁻¹' Iic s :=
      fun y hy ↦ by simp [hστ y hy]
    have : Nonempty (σ.stratum J ⁻¹' Iic s) := ⟨x.val⟩
    have : Nonempty (τ ⁻¹' Iic s) := ⟨⟨_, (hP _ hxe).1 x.val.property⟩⟩
    refine ⟨τ ⁻¹' Iic s, inferInstance, (Iic s).restrictPreimage τ,
      hτ.restrictPreimage (IsLowerSet.Iic s), e.subtypeFst hP, by simpa using hxe,
      fun y hy ↦ ?_, fun y hy ↦ Subtype.ext ?_⟩ <;>
    replace hy : (y : T J) ∈ e.source := by simpa using hy
    · rw [OpenPartialHomeomorph.snd_subtypeFst_apply, he y hy]
      ext α
      simp
    · rw [OpenPartialHomeomorph.subtypeFst_apply _ _ hy]
      exact hστ y hy

/-- The restricted stratification of `X_I^≤s` is the stratification `σ_I`. -/
@[simp]
theorem coe_stratum_restrictCellLikeStratification (I : Finset A) (x : σ.stratum I ⁻¹' Iic s) :
    ((σ.restrictCellLikeStratification s).stratum I x : S) = σ.stratum I x :=
  (rfl)

end CellLikeStratification

end ImplicitAtlasWithBoundary

end TauCeti
