/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Geometry.Manifold.Algebra.Monoid
import TauCeti.Geometry.Manifold.BumpFunction

/-!
# Smooth cutoff functions around compact sets

On a Hausdorff manifold modelled on a finite-dimensional real space, a compact set `K` inside an
open set `W` has a cutoff of the manifold's differentiability class with values in `[0, 1]`, equal
to `1` on a neighbourhood of `K`, with topological support a compact subset of `W`
(`IsCompact.exists_contMDiff_one_nhds_tsupport_subset`).

Mathlib's smooth Urysohn lemma `exists_contMDiffMap_one_nhds_of_subset_interior` gives such a
function for a closed set, but assumes the manifold σ-compact and does not make the support
compact. Here neither is needed, since finitely many bump functions cover `K`. Cutoffs of this
form extend smooth vector fields near compact sets on boundaryless manifolds to compactly
supported smooth vector fields, which are complete. For the same reason a compact set has a smooth
bump covering indexed by a finite type
and subordinate to any given neighbourhoods of its points
(`IsCompact.exists_smoothBumpCovering_isSubordinate`), the input of Mathlib's Whitney embedding
`SmoothBumpCovering.embeddingPiTangent`.

The construction, smoothing a finite sum of bump functions by `Real.smoothTransition`, follows the
bump cover in the proof of `TauCeti.exists_vectorField_mvfderiv_eq_neg_one`. The finite-regularity
step uses `SmoothBumpFunction.contMDiff_of_isManifold`.
-/

public section

open Function Set Topology
open scoped ContDiff Manifold

universe u

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]

variable (I) in
/-- **A finite smooth bump covering of a compact set.** If `K` is a compact subset of a Hausdorff
manifold modelled on a finite-dimensional space and `U x` is a neighbourhood of `x` for every
`x ∈ K`, there is a smooth bump covering of `K` indexed by a finite type and subordinate to `U`.

Mathlib's `SmoothBumpCovering.exists_isSubordinate` covers a closed set of a σ-compact manifold,
with an index type which need not be finite. -/
theorem IsCompact.exists_smoothBumpCovering_isSubordinate {K : Set M} (hK : IsCompact K)
    {U : M → Set M} (hU : ∀ x ∈ K, U x ∈ 𝓝 x) :
    ∃ (ι : Type u) (_ : Fintype ι) (f : SmoothBumpCovering ι I M K), f.IsSubordinate U := by
  -- Bump functions at the points of `K` supported in `U`; finitely many of the open sets where
  -- one of them is `1` cover `K`.
  choose ρ hρ using fun x : K ↦
    (SmoothBumpFunction.nhds_basis_tsupport (I := I) (x : M)).mem_iff.1 (hU x x.property)
  obtain ⟨t, ht⟩ := hK.elim_nhds_subcover' (fun x hx ↦ interior {y | ρ ⟨x, hx⟩ y = 1})
    fun x hx ↦ interior_mem_nhds.2 (ρ ⟨x, hx⟩).eventuallyEq_one
  refine ⟨t, inferInstance, ⟨fun i ↦ i.val, fun i ↦ ρ i.val, fun i ↦ i.val.property,
    locallyFinite_of_finite _, fun x hx ↦ ?_⟩, fun i ↦ (hρ i.val).2⟩
  obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.1 (ht hx)
  exact ⟨⟨i, hi⟩, mem_interior_iff_mem_nhds.1 hxi⟩

variable (I) in
/-- **A `C^n` cutoff around a compact set.** If `K` is a compact subset of an open set `W` of a
Hausdorff `C^n` manifold modelled on a finite-dimensional space, there is a `C^n` function
`σ : M → [0, 1]` equal to `1` on a neighbourhood of `K` whose topological support is a compact
subset of `W`. -/
theorem IsCompact.exists_contMDiff_one_nhds_tsupport_subset {K W : Set M} (hK : IsCompact K)
    (hW : IsOpen W) (hKW : K ⊆ W) (n : ℕ∞ := ⊤) [IsManifold I n M] :
    ∃ σ : M → ℝ, ContMDiff I 𝓘(ℝ) n σ ∧ (∀ᶠ x in 𝓝ˢ K, σ x = 1) ∧ HasCompactSupport σ ∧
      tsupport σ ⊆ W ∧ ∀ x, σ x ∈ Icc 0 1 := by
  obtain ⟨ι, _, ρ, hρ⟩ := hK.exists_smoothBumpCovering_isSubordinate I
    (U := fun _ ↦ W) (fun x hx ↦ hW.mem_nhds (hKW hx))
  -- Smooth the finite sum of subordinate bumps to obtain a cutoff valued in the unit interval.
  set C := ⋃ i, tsupport (ρ i)
  have hC : IsCompact C := isCompact_iUnion fun i ↦ (ρ i).hasCompactSupport
  have hσC : ∀ y ∉ C, Real.smoothTransition (∑ i, ρ i y) = 0 := fun y hy ↦ by
    have h0 : ∀ i, ρ i y = 0 := fun i ↦
      image_eq_zero_of_notMem_tsupport fun h ↦ hy (mem_iUnion.2 ⟨i, h⟩)
    simp [h0]
  have hsupp : tsupport (fun y ↦ Real.smoothTransition (∑ i, ρ i y)) ⊆ C :=
    closure_minimal (fun y hy ↦ by_contra fun h ↦ mem_support.1 hy (hσC y h)) hC.isClosed
  refine ⟨fun y ↦ Real.smoothTransition (∑ i, ρ i y),
    Real.smoothTransition.contDiff.contMDiff.comp
      (ContMDiff.sum fun i _ ↦ (ρ i).contMDiff_of_isManifold),
    ?_, hC.of_isClosed_subset (isClosed_tsupport _) hsupp,
    hsupp.trans (iUnion_subset fun i ↦ hρ i),
    fun y ↦ ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩⟩
  apply eventually_nhdsSet_iff_forall.mpr
  intro x hx
  obtain ⟨i, hi⟩ := ρ.eventuallyEq_one' x hx
  filter_upwards [hi] with y hy
  apply Real.smoothTransition.one_of_one_le
  have hle := Finset.single_le_sum (fun j _ ↦ (ρ j).nonneg) (Finset.mem_univ i)
    (f := fun j ↦ ρ j y)
  simpa only [Pi.one_apply, hy] using hle
