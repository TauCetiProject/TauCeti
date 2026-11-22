/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Orthonormal
public import TauCeti.RepresentationTheory.Compact.RepresentativeDensity
public import TauCeti.RepresentationTheory.Compact.UnitaryModel
public import TauCeti.RepresentationTheory.Continuous.Unitary.HilbertSum
public import TauCeti.RepresentationTheory.Continuous.Unitary.Hom

/-!
# Small-kernel and faithful unitary representations of compact Hausdorff groups

On a compact Hausdorff group `G`, Peter–Weyl density separates every pair of distinct points by a
finite-dimensional continuous representation (`TauCeti.exists_contRepresentation_apply_ne`), and
Weyl's unitarian trick conjugates any such representation to a unitary one
(`ContRepresentation.exists_isUnitary_congr`).

This file combines those two ingredients with finite Hilbert direct sums to deduce the global
structural consequences for compact Hausdorff groups, uniformly over any `𝕜` with `[RCLike 𝕜]`
(so simultaneously for complex unitary representations and for real orthogonal representations):

1. **Point separation by unitary representations** (`TauCeti.exists_isUnitary_apply_ne`): any two
   distinct elements of `G` act differently in some continuous unitary representation on
   `EuclideanSpace 𝕜 (Fin n)`.
2. **The Peter–Weyl small-kernel theorem** (`TauCeti.exists_isUnitary_ker_subset`): for every
   identity neighbourhood `U ∈ 𝓝 (1 : G)`, there is a continuous unitary representation on
   `EuclideanSpace 𝕜 (Fin n)` whose kernel is contained in `U`. Indeed, `(interior U)ᶜ` is compact
   and avoids `1`, so finitely many open non-fixation sets `{g | ρ x g ≠ 1}` cover it; the finite
   Hilbert direct sum of the corresponding unitary representations has kernel inside
   `interior U ⊆ U` and transports isometrically along `(stdOrthonormalBasis 𝕜 W).repr` to
   `EuclideanSpace 𝕜 (Fin n)`.
3. **Characterization of no small subgroups**
   (`TauCeti.hasNoSmallSubgroups_iff_exists_faithful_isUnitary`): a compact Hausdorff group has no
   small subgroups if and only if it admits a faithful continuous unitary representation on
   `EuclideanSpace 𝕜 (Fin n)`, equivalently a closed topological-group embedding into
   `Matrix.unitaryGroup (Fin n) 𝕜`
   (`TauCeti.HasNoSmallSubgroups.exists_isClosedEmbedding_matrixUnitaryGroup`).

## Main results

* `TauCeti.exists_isUnitary_apply_ne`, `TauCeti.exists_isUnitary_apply_ne_one`: unitary point
  separation on compact Hausdorff groups.
* `TauCeti.exists_isUnitary_ker_subset`: **the Peter–Weyl small-kernel theorem.**
* `TauCeti.HasNoSmallSubgroups.exists_faithful_isUnitary`: a compact Hausdorff group with no small
  subgroups admits a faithful continuous finite-dimensional unitary representation.
* `TauCeti.hasNoSmallSubgroups_iff_exists_faithful_isUnitary`: `HasNoSmallSubgroups G` holds if and
  only if `G` has a faithful continuous unitary representation on `EuclideanSpace 𝕜 (Fin n)`.
* `TauCeti.HasNoSmallSubgroups.exists_isClosedEmbedding_matrixUnitaryGroup`: closed topological
  embedding of a compact Hausdorff NSS group into `Matrix.unitaryGroup (Fin n) 𝕜`.

## References

* T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*, Springer GTM 98 (1985),
  Chapter III, §4 (Corollary 4.2 and Theorem 4.4).
* G. B. Folland, *A Course in Abstract Harmonic Analysis*, 2nd ed., CRC (2016), Corollary 5.14.
* T. Tao, *Hilbert's Fifth Problem and Related Topics*, AMS GSM 153 (2014), Theorem 1.2.5.
-/

public section

noncomputable section

open Filter Set
open scoped Topology

namespace TauCeti

section CompactGroup

variable {𝕜 G : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T1Space G]

/-- **Unitary point separation.** Any two distinct elements of a compact Hausdorff group are
separated by a continuous unitary representation on `EuclideanSpace 𝕜 (Fin n)`. -/
theorem exists_isUnitary_apply_ne (x y : G) (hxy : x ≠ y) :
    ∃ (n : ℕ) (π : ContRepresentation 𝕜 G (EuclideanSpace 𝕜 (Fin n))),
      Continuous π ∧ π.IsUnitary ∧ π x ≠ π y := by
  obtain ⟨n, π₀, hπ₀, hne⟩ := exists_contRepresentation_apply_ne (𝕜 := 𝕜) x y hxy
  obtain ⟨e, he⟩ := π₀.exists_isUnitary_congr hπ₀
  refine ⟨n, ContinuousLinearEquiv.congr e π₀, e.continuous_congr hπ₀, he, fun hcon ↦ hne ?_⟩
  have hcoe := congrFun (e.coe_congr π₀)
  exact e.conjContinuousAlgEquiv.injective ((hcoe x).symm.trans (hcon.trans (hcoe y)))

/-- Every non-identity element of a compact Hausdorff group acts nontrivially in some continuous
unitary representation on `EuclideanSpace 𝕜 (Fin n)`. -/
theorem exists_isUnitary_apply_ne_one {g : G} (hg : g ≠ 1) :
    ∃ (n : ℕ) (π : ContRepresentation 𝕜 G (EuclideanSpace 𝕜 (Fin n))),
      Continuous π ∧ π.IsUnitary ∧ π g ≠ 1 := by
  obtain ⟨n, π, hπc, hπu, hne⟩ := exists_isUnitary_apply_ne (𝕜 := 𝕜) g 1 hg
  exact ⟨n, π, hπc, hπu, by rwa [map_one] at hne⟩

/-- **The Peter–Weyl small-kernel theorem.** Every identity neighbourhood `U ∈ 𝓝 (1 : G)` in a
compact Hausdorff group contains the kernel of a continuous unitary representation on
`EuclideanSpace 𝕜 (Fin n)`. -/
theorem exists_isUnitary_ker_subset {U : Set G} (hU : U ∈ 𝓝 (1 : G)) :
    ∃ (n : ℕ) (π : ContRepresentation 𝕜 G (EuclideanSpace 𝕜 (Fin n))),
      Continuous π ∧ π.IsUnitary ∧ ((π.toMonoidHom.ker : Subgroup G) : Set G) ⊆ U := by
  classical
  let K : Set G := (interior U)ᶜ
  have hK_compact : IsCompact K := isOpen_interior.isClosed_compl.isCompact
  have h1_not_mem : (1 : G) ∉ K := by
    simp [K, mem_interior_iff_mem_nhds.mpr hU]
  have hex : ∀ x : K, ∃ (d : ℕ) (ρ : ContRepresentation 𝕜 G (EuclideanSpace 𝕜 (Fin d))),
      Continuous ρ ∧ ρ.IsUnitary ∧ ρ x.val ≠ 1 :=
    fun x ↦ exists_isUnitary_apply_ne_one (𝕜 := 𝕜) fun hx1 ↦ h1_not_mem (hx1 ▸ x.property)
  choose d ρ hρc hρu hρne using hex
  let V : K → Set G := fun x ↦ {g : G | ρ x g ≠ 1}
  have hV_open : ∀ x : K, IsOpen (V x) :=
    fun x ↦ isClosed_singleton.isOpen_compl.preimage (hρc x)
  have hcover : K ⊆ ⋃ x : K, V x :=
    fun g hg ↦ mem_iUnion.mpr ⟨⟨g, hg⟩, hρne ⟨g, hg⟩⟩
  obtain ⟨s, hs⟩ := hK_compact.elim_finite_subcover V hV_open hcover
  -- Sum the finitely many witnessing representations and transport to `EuclideanSpace 𝕜 (Fin n)`.
  let H : s → Type _ := fun i ↦ EuclideanSpace 𝕜 (Fin (d i.val))
  let W := lp H 2
  have : FiniteDimensional 𝕜 W :=
    FiniteDimensional.of_injective
      ({ toFun x := ⇑x, map_add' _ _ := rfl, map_smul' _ _ := rfl } : W →ₗ[𝕜] ∀ i : s, H i)
      fun _ _ h ↦ lp.ext h
  let σ : ContRepresentation 𝕜 G W :=
    ContRepresentation.hilbertSum (fun i : s ↦ ρ i.val) (fun i : s ↦ hρu i.val)
  have hσc : Continuous σ :=
    ContRepresentation.continuous_hilbertSum (fun i : s ↦ ρ i.val) (fun i : s ↦ hρu i.val)
      (fun i : s ↦ hρc i.val)
  have hσu : σ.IsUnitary :=
    ContRepresentation.isUnitary_hilbertSum (fun i : s ↦ ρ i.val) (fun i : s ↦ hρu i.val)
  let b := stdOrthonormalBasis 𝕜 W
  let e : W ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 (Fin (Module.finrank 𝕜 W)) := b.repr
  let π : ContRepresentation 𝕜 G (EuclideanSpace 𝕜 (Fin (Module.finrank 𝕜 W))) :=
    ContinuousLinearEquiv.congr e.toContinuousLinearEquiv σ
  refine ⟨Module.finrank 𝕜 W, π, e.toContinuousLinearEquiv.continuous_congr hσc, hσu.congr e, ?_⟩
  intro g hg
  by_contra hgU
  have hgK : g ∈ K := fun hg_int ↦ hgU (interior_subset hg_int)
  obtain ⟨x, hxs, hgx⟩ := mem_iUnion₂.mp (hs hgK)
  have hπ1 : π g = 1 := MonoidHom.mem_ker.mp hg
  have hσ1 : σ g = 1 := by
    have hconj : e.toContinuousLinearEquiv.conjContinuousAlgEquiv (σ g) = 1 := by
      simpa only [π, ContinuousLinearEquiv.coe_congr] using hπ1
    exact (map_eq_one_iff _ e.toContinuousLinearEquiv.conjContinuousAlgEquiv.injective).mp hconj
  exact hgx ((ContRepresentation.hilbertSum_apply_eq_one_iff
    (fun i : s ↦ ρ i.val) (fun i : s ↦ hρu i.val) g).mp hσ1 ⟨x, hxs⟩)

/-- **Faithful unitary representation of a compact group with no small subgroups.** Every compact
Hausdorff group satisfying `TauCeti.HasNoSmallSubgroups` admits an injective continuous unitary
representation on `EuclideanSpace 𝕜 (Fin n)`. -/
theorem HasNoSmallSubgroups.exists_faithful_isUnitary (hG : HasNoSmallSubgroups G) :
    ∃ (n : ℕ) (π : ContRepresentation 𝕜 G (EuclideanSpace 𝕜 (Fin n))),
      Continuous π ∧ π.IsUnitary ∧ Function.Injective π := by
  obtain ⟨U, hU, hbot⟩ := hasNoSmallSubgroups_iff.mp hG
  obtain ⟨n, π, hπc, hπu, hker⟩ := exists_isUnitary_ker_subset (𝕜 := 𝕜) hU
  have hker_bot : π.toMonoidHom.ker = ⊥ := hbot π.toMonoidHom.ker hker
  have hinj : Function.Injective π :=
    (MonoidHom.ker_eq_bot_iff π.toMonoidHom).mp hker_bot
  exact ⟨n, π, hπc, hπu, hinj⟩

variable (𝕜) in
/-- **A compact Hausdorff group has no small subgroups if and only if it admits a faithful
continuous finite-dimensional unitary representation** (over `𝕜`, so in particular over `ℂ` or over
`ℝ`). -/
theorem hasNoSmallSubgroups_iff_exists_faithful_isUnitary :
    HasNoSmallSubgroups G ↔
      ∃ (n : ℕ) (π : ContRepresentation 𝕜 G (EuclideanSpace 𝕜 (Fin n))),
        Continuous π ∧ π.IsUnitary ∧ Function.Injective π :=
  ⟨fun hG ↦ hG.exists_faithful_isUnitary,
    fun ⟨_, π, hπc, _, hinj⟩ ↦ π.hasNoSmallSubgroups_of_injective hπc.continuousAt hinj⟩

variable (𝕜) in
/-- Every compact Hausdorff group with no small subgroups embeds as a closed topological subgroup
into `Matrix.unitaryGroup (Fin n) 𝕜` for some `n : ℕ`. -/
theorem HasNoSmallSubgroups.exists_isClosedEmbedding_matrixUnitaryGroup
    (hG : HasNoSmallSubgroups G) :
    ∃ (n : ℕ) (f : G →ₜ* Matrix.unitaryGroup (Fin n) 𝕜), Topology.IsClosedEmbedding f := by
  obtain ⟨n, π, hπc, hπu, hinj⟩ := hG.exists_faithful_isUnitary (𝕜 := 𝕜)
  refine ⟨n, hπu.toMatrixUnitaryGroupHom hπc, ?_⟩
  exact (hπu.toMatrixUnitaryGroupHom hπc).continuous.isClosedEmbedding
    ((hπu.injective_toMatrixUnitaryGroupHom_iff hπc).mpr hinj)

end CompactGroup

end TauCeti
