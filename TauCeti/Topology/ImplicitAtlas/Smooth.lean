/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.ImplicitAtlas.Basic
public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.Instances.Real
public import Mathlib.Geometry.Manifold.LocalDiffeomorph

-- Access the body of `IsLocalDiffeomorphAt` to destructure its witness.
import all Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Smooth enhancements of implicit atlases

An implicit atlas (`TauCeti.ImplicitAtlas`) is purely topological: its regular loci `X_I^reg` are
topological manifolds and its Kuranishi maps are continuous. A *smooth enhancement* (Pardon,
Definition 3.1.3) adds smooth structures on the regular loci for which the atlas data are smooth.
No smooth structure on the whole thickening `X_I` is imposed, and the topological atlas is
unchanged: the enhancement is extra data on top of it, and forgetting it returns the atlas.

Here the smooth structure on `X_I^reg` is a charted space structure on the subtype
`𝒜.regLocus I`, modelled on `ℝ^(N I)` for a dimension function `N`, passed as an instance
argument; the charts are open partial homeomorphisms for the subspace topology, so the smooth
structure induces the topology of `X_I^reg`. Different instances on the same atlas are different
enhancements: an enhancement is data, not a property of the topological atlas.
`TauCeti.ImplicitAtlas.IsSmoothEnhancement 𝒜 N` says that these structures form a smooth
enhancement of `𝒜`:

* each `X_I^reg` is a smooth manifold, of the expected dimension `d + m_I` when it is nonempty,
  where `m_I = ∑_(α ∈ I) dim E_α`;
* `Γ_I` acts on `X_I^reg` by smooth maps, and the Kuranishi maps `s_α` are smooth on `X_I^reg`;
* near every point `x` of `ψ_IJ⁻¹(X_I^reg)` there is a map `τ : X_J^reg → X_I^reg`, smooth near
  `x`, that agrees with the footprint map `ψ_IJ` on the zero set `Z_IJ = {s_(J \ I) = 0}` near
  `x` and such that `y ↦ (τ y, s_(J \ I) y)` is a local diffeomorphism
  `X_J^reg → X_I^reg × E_(J \ I)` at `x`.

The last condition is Pardon's requirement that the extra obstruction `s_(J \ I)` be a smooth
submersion over `ψ_IJ⁻¹(X_I^reg)` and that `ψ_IJ` be a local diffeomorphism on
`ψ_IJ⁻¹(X_I^reg) ∩ Z_IJ`, packaged in local normal form: `s_(J \ I)` is the second coordinate of
a local diffeomorphism, and `ψ_IJ` is its first coordinate on the zero set, the slice
`X_I^reg × {0}`. Phrasing it through `τ` avoids putting a smooth structure on the zero set itself.
The extra obstruction `s_(J \ I)` is the topological map `TauCeti.kuranishiSdiff` of
`TauCeti.Topology.ImplicitAtlas.Basic`.

## Main definitions

* `TauCeti.ImplicitAtlas.IsSmoothEnhancement`: the smooth structures on the regular loci form a
  smooth enhancement of the atlas.
* `TauCeti.ImplicitAtlas.IsSmoothEnhancement.actDiffeomorph`: `Γ_I` acts on `X_I^reg` by
  diffeomorphisms.

## Main results

* `TauCeti.ImplicitAtlas.IsSmoothEnhancement.exists_openPartialHomeomorph`: a smooth enhancement
  induces the topological product models of the atlas. Near every point of `ψ_IJ⁻¹(X_I^reg)`
  there is a homeomorphism of an open subset of `X_J` onto an open subset of
  `ℝ^n × E_(J \ I)`, with `n = d + m_I`, whose second coordinate is `s_(J \ I)` and whose first
  coordinate on the zero set is a smooth chart of `X_I^reg` composed with `ψ_IJ`.

The smooth structure of a smooth manifold is a smooth enhancement of its manifold atlas
(`TauCeti.ImplicitAtlas.isSmoothEnhancement_ofChartedSpace`, in
`TauCeti.Topology.ImplicitAtlas.Examples`).

## References

* J. Pardon, *An algebraic approach to virtual fundamental cycles on moduli spaces of
  pseudo-holomorphic curves*, Geom. Topol. 20 (2016), 779–1034, Definitions 3.1.1 (implicit
  atlases) and 3.1.3 (smooth implicit atlases).
-/

public section

open Set Topology
open scoped Manifold ContDiff

namespace TauCeti.ImplicitAtlas

variable {A : Type*} [DecidableEq A] {Γ : A → Type*} [∀ α, Group (Γ α)] [∀ α, Finite (Γ α)]
  {E : A → Type*} [∀ α, NormedAddCommGroup (E α)] [∀ α, NormedSpace ℝ (E α)]
  [∀ α, FiniteDimensional ℝ (E α)] {ρ : ∀ α, Representation ℝ (Γ α) (E α)}
  {T : Finset A → Type*} [∀ I, TopologicalSpace (T I)] [∀ I, T2Space (T I)]
  {act : ∀ I : Finset A, ((α : I) → Γ α) →* (T I ≃ₜ T I)}
  {X : Type*} [TopologicalSpace X] {d : ℤ} (𝒜 : ImplicitAtlas Γ E ρ T act X d)

variable (N : Finset A → ℕ) [∀ I, ChartedSpace (EuclideanSpace ℝ (Fin (N I))) (𝒜.regLocus I)]

/-- The charted space structures on the regular loci `X_I^reg`, modelled on `ℝ^(N I)`, form a
**smooth enhancement** of the implicit atlas `𝒜` (Pardon, Definition 3.1.3). See the module
docstring for the meaning of each field. -/
structure IsSmoothEnhancement : Prop where
  /-- A nonempty regular locus `X_I^reg` has the expected dimension `d + m_I`. -/
  natCast_eq : ∀ I : Finset A, (𝒜.regLocus I).Nonempty →
    (N I : ℤ) = d + ∑ α ∈ I, (Module.finrank ℝ (E α) : ℤ)
  /-- The charts of each regular locus `X_I^reg` are smoothly compatible. -/
  isManifold : ∀ I : Finset A, IsManifold (𝓡 (N I)) ∞ (𝒜.regLocus I)
  /-- The group `Γ_I` acts on `X_I^reg` by smooth maps. -/
  contMDiff_act : ∀ (I : Finset A) (g : (α : I) → Γ α),
    ContMDiff (𝓡 (N I)) (𝓡 (N I)) ∞
      (fun x : 𝒜.regLocus I ↦ (⟨act I g x, 𝒜.act_mem_regLocus I g x x.property⟩ : 𝒜.regLocus I))
  /-- The Kuranishi maps `s_α` are smooth on `X_I^reg`. -/
  contMDiff_kuranishi : ∀ (I : Finset A) (α : I),
    ContMDiff (𝓡 (N I)) 𝓘(ℝ, E α) ∞ (fun x : 𝒜.regLocus I ↦ 𝒜.kuranishi I α x)
  /-- Near every point `x` of `ψ_IJ⁻¹(X_I^reg)` there is a map `τ : X_J^reg → X_I^reg` that
  agrees with the footprint map `ψ_IJ` on the zero set `Z_IJ` near `x` and such that
  `y ↦ (τ y, s_(J \ I) y)` is a local diffeomorphism at `x`. -/
  exists_isLocalDiffeomorphAt : ∀ ⦃I J : Finset A⦄ (h : I ⊆ J)
    (x : kuranishiZeroSet 𝒜.kuranishi I J) (hx : 𝒜.footprintMap h x ∈ 𝒜.regLocus I),
    ∃ τ : 𝒜.regLocus J → 𝒜.regLocus I,
      (∀ᶠ y in 𝓝 (⟨x.val, 𝒜.mem_regLocus_of_footprintMap_mem h x hx⟩ : 𝒜.regLocus J),
        ∀ hy : y.val ∈ kuranishiZeroSet 𝒜.kuranishi I J,
          (τ y : T I) = 𝒜.footprintMap h ⟨y.val, hy⟩) ∧
      IsLocalDiffeomorphAt (𝓡 (N J)) ((𝓡 (N I)).prod 𝓘(ℝ, (α : ↥(J \ I)) → E α)) ∞
        (fun y ↦ (τ y, kuranishiSdiff 𝒜.kuranishi I J y))
        ⟨x.val, 𝒜.mem_regLocus_of_footprintMap_mem h x hx⟩

namespace IsSmoothEnhancement

variable {𝒜 N}

/-- **`Γ_I` acts on `X_I^reg` by diffeomorphisms**: the action of `g ∈ Γ_I` restricted to the
regular locus, as a diffeomorphism with inverse the action of `g⁻¹`. -/
noncomputable def actDiffeomorph (hS : 𝒜.IsSmoothEnhancement N) (I : Finset A)
    (g : (α : I) → Γ α) :
    Diffeomorph (𝓡 (N I)) (𝓡 (N I)) (𝒜.regLocus I) (𝒜.regLocus I) ∞ where
  toFun x := ⟨act I g x, 𝒜.act_mem_regLocus I g x x.property⟩
  invFun x := ⟨act I g⁻¹ x, 𝒜.act_mem_regLocus I g⁻¹ x x.property⟩
  left_inv x := Subtype.ext <| by
    simp only [map_inv, Homeomorph.inv_apply, Homeomorph.symm_apply_apply]
  right_inv x := Subtype.ext <| by
    simp only [map_inv, Homeomorph.inv_apply, Homeomorph.apply_symm_apply]
  contMDiff_toFun := hS.contMDiff_act I g
  contMDiff_invFun := hS.contMDiff_act I g⁻¹

@[simp]
theorem coe_actDiffeomorph_apply (hS : 𝒜.IsSmoothEnhancement N) (I : Finset A)
    (g : (α : I) → Γ α) (x : 𝒜.regLocus I) :
    (hS.actDiffeomorph I g x : T I) = act I g x :=
  (rfl)

@[simp]
theorem coe_actDiffeomorph_symm_apply (hS : 𝒜.IsSmoothEnhancement N) (I : Finset A)
    (g : (α : I) → Γ α) (x : 𝒜.regLocus I) :
    ((hS.actDiffeomorph I g).symm x : T I) = act I g⁻¹ x :=
  (rfl)

/-- **A smooth enhancement induces the topological product models.** Let `x ∈ Z_IJ` with
`ψ_IJ x ∈ X_I^reg`. There is a homeomorphism `e` of an open neighbourhood of `x` in `X_J` onto an
open subset of `ℝ^(N I) × E_(J \ I)`, where `N I = d + m_I` is the dimension of `X_I^reg`, whose
second coordinate is the extra obstruction `s_(J \ I)` and whose first coordinate, on the zero set
`Z_IJ`, is the smooth chart of `X_I^reg` at `ψ_IJ x` composed with the footprint map `ψ_IJ`. This
is the local product model of the topological atlas
(`TauCeti.ImplicitAtlas.exists_openPartialHomeomorph`), now adapted to the footprint map. -/
theorem exists_openPartialHomeomorph (hS : 𝒜.IsSmoothEnhancement N) {I J : Finset A}
    (h : I ⊆ J) (x : kuranishiZeroSet 𝒜.kuranishi I J)
    (hx : 𝒜.footprintMap h x ∈ 𝒜.regLocus I) :
    (N I : ℤ) = d + ∑ α ∈ I, (Module.finrank ℝ (E α) : ℤ) ∧
      ∃ e : OpenPartialHomeomorph (T J)
          (EuclideanSpace ℝ (Fin (N I)) × ((α : ↥(J \ I)) → E α)),
        x.val ∈ e.source ∧ (∀ y ∈ e.source, (e y).2 = kuranishiSdiff 𝒜.kuranishi I J y) ∧
        ∀ y : kuranishiZeroSet 𝒜.kuranishi I J, y.val ∈ e.source →
          ∃ hy : 𝒜.footprintMap h y ∈ 𝒜.regLocus I,
            (e y).1 = chartAt (EuclideanSpace ℝ (Fin (N I)))
              (⟨𝒜.footprintMap h x, hx⟩ : 𝒜.regLocus I) ⟨𝒜.footprintMap h y, hy⟩ := by
  refine ⟨hS.natCast_eq I ⟨_, hx⟩, ?_⟩
  set x' : 𝒜.regLocus J := ⟨x.val, 𝒜.mem_regLocus_of_footprintMap_mem h x hx⟩
  obtain ⟨τ, hτ, Φ, hxΦ, hfΦ⟩ := hS.exists_isLocalDiffeomorphAt h x hx
  have hΦ : ∀ y ∈ Φ.source, Φ y = (τ y, kuranishiSdiff 𝒜.kuranishi I J y) :=
    fun _ hy ↦ (hfΦ hy).symm
  have hτx : τ x' = ⟨𝒜.footprintMap h x, hx⟩ := Subtype.ext (hτ.self_of_nhds x.property)
  -- Near `x'`, `τ` extends `ψ_IJ` and the local diffeomorphism `Φ` is defined.
  obtain ⟨W, hW, hWo, hxW⟩ := eventually_nhds_iff.1 <| hτ.and <| Φ.open_source.mem_nhds hxΦ
  set c := chartAt (EuclideanSpace ℝ (Fin (N I))) (⟨𝒜.footprintMap h x, hx⟩ : 𝒜.regLocus I)
  -- `Φ = (τ, s_(J \ I))` followed by a chart of `X_I^reg`, cut down to `W`.
  set e₀ := (Φ.toOpenPartialHomeomorph.trans
    (c.prod (OpenPartialHomeomorph.refl ((α : ↥(J \ I)) → E α)))).restrOpen W hWo
  have he₀ : ∀ y ∈ e₀.source, y ∈ W ∧ e₀ y = (c (τ y), kuranishiSdiff 𝒜.kuranishi I J y) := by
    intro y hy
    simp only [e₀, OpenPartialHomeomorph.restrOpen_source, OpenPartialHomeomorph.trans_source,
      mem_inter_iff] at hy
    refine ⟨hy.2, ?_⟩
    simp [e₀, hΦ y (hW y hy.2).2]
  refine ⟨e₀.lift_openEmbedding (𝒜.isOpen_regLocus J).isOpenEmbedding_subtypeVal, ?_, ?_, ?_⟩
  · refine ⟨x', ?_, rfl⟩
    simp only [e₀, OpenPartialHomeomorph.restrOpen_source, OpenPartialHomeomorph.trans_source,
      mem_inter_iff, mem_preimage, OpenPartialHomeomorph.prod_source,
      OpenPartialHomeomorph.refl_source, mem_prod, mem_univ, and_true]
    refine ⟨⟨hxΦ, ?_⟩, hxW⟩
    rw [PartialDiffeomorph.toFun'_toOpenPartialHomeomorph, hΦ x' hxΦ, hτx]
    exact mem_chart_source _ _
  · rintro _ ⟨y, hy, rfl⟩
    rw [OpenPartialHomeomorph.lift_openEmbedding_apply, (he₀ y hy).2]
  · rintro y ⟨y', hy', hyy'⟩
    have hy'Z : y'.val ∈ kuranishiZeroSet 𝒜.kuranishi I J := hyy' ▸ y.property
    have hτy : (τ y' : T I) = 𝒜.footprintMap h y := by
      rw [(hW y' (he₀ y' hy').1).1 hy'Z]
      congr
    refine ⟨hτy ▸ (τ y').property, ?_⟩
    rw [← hyy', OpenPartialHomeomorph.lift_openEmbedding_apply, (he₀ y' hy').2]
    exact congrArg c (Subtype.ext hτy)

end IsSmoothEnhancement

end TauCeti.ImplicitAtlas
