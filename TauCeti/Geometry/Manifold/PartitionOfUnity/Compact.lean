/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import TauCeti.Geometry.Manifold.PartitionOfUnity.Basic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Geometry.Manifold.Algebra.Monoid
import TauCeti.Geometry.Manifold.BumpFunction

/-!
# Smooth cutoff functions around compact sets

On a Hausdorff manifold modelled on a finite-dimensional real space, a compact set `K` inside an
open set `W` has a smooth cutoff function: a smooth `σ : M → [0, 1]`, equal to `1` on a
neighbourhood of `K`, whose support is a compact subset of `W`
(`IsCompact.exists_contMDiff_one_nhds_tsupport_subset`), also as a bundled smooth map
(`IsCompact.exists_contMDiffMap_one_nhds_hasCompactSupport`).

Mathlib's smooth Urysohn lemma `exists_contMDiffMap_one_nhds_of_subset_interior` gives such a
function for a closed set, but assumes the manifold σ-compact and does not make the support
compact. Here neither is needed, since finitely many bump functions cover `K`. Cutoffs of this
form extend a vector field given near a compact set to a compactly supported one, and so a
complete one. For the same reason a compact set has a smooth bump covering indexed by a finite type
and subordinate to any given neighbourhoods of its points
(`IsCompact.exists_smoothBumpCovering_isSubordinate`), the input of Mathlib's Whitney embedding
`SmoothBumpCovering.embeddingPiTangent`, and any compactly supported `C^k` vector field decomposes
into a finite sum of `C^k` vector fields subordinate to a cover of its support
(`HasCompactSupport.exists_subordinate_vectorField_sum`).

The construction, smoothing a finite sum of bump functions by `Real.smoothTransition`, follows the
bump cover in the proof of `TauCeti.exists_vectorField_mvfderiv_eq_neg_one`.
-/

public section

open Function Set Topology
open scoped ContDiff Manifold

universe u

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]

section

variable [IsManifold I ∞ M]

variable (I) in
/-- **A smooth cutoff around a compact set.** If `K` is a compact subset of an open set `W` of a
Hausdorff manifold modelled on a finite-dimensional space, there is a smooth function
`σ : M → [0, 1]` equal to `1` on a neighbourhood of `K` whose topological support is a compact
subset of `W`. -/
theorem IsCompact.exists_contMDiff_one_nhds_tsupport_subset {K W : Set M} (hK : IsCompact K)
    (hW : IsOpen W) (hKW : K ⊆ W) :
    ∃ σ : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ σ ∧ (∀ᶠ x in 𝓝ˢ K, σ x = 1) ∧ HasCompactSupport σ ∧
      tsupport σ ⊆ W ∧ ∀ x, σ x ∈ Icc 0 1 := by
  -- Bump functions at the points of `K` supported in `W`; finitely many of the open sets where
  -- one of them is `1` cover `K`.
  choose ρ hρ using fun x : K ↦
    (SmoothBumpFunction.nhds_basis_tsupport (I := I) (x : M)).mem_iff.1 (hW.mem_nhds
        (hKW x.property))
  obtain ⟨t, ht⟩ := hK.elim_nhds_subcover' (fun x hx ↦ interior {y | ρ ⟨x, hx⟩ y = 1})
    fun x hx ↦ interior_mem_nhds.2 (ρ ⟨x, hx⟩).eventuallyEq_one
  -- Smoothing the sum of these bumps by a smooth step function gives a cutoff which is `1` where
  -- one of them is, and `0` off their supports.
  set C := ⋃ i ∈ t, tsupport (ρ i)
  have hC : IsCompact C := t.isCompact_biUnion fun i _ ↦ (ρ i).hasCompactSupport
  have hσC : ∀ y ∉ C, Real.smoothTransition (∑ i ∈ t, ρ i y) = 0 := fun y hy ↦ by
    have h0 : ∀ i ∈ t, ρ i y = 0 := fun i hi ↦
      image_eq_zero_of_notMem_tsupport fun h ↦ hy (mem_iUnion₂.2 ⟨i, hi, h⟩)
    simp [Finset.sum_eq_zero h0]
  have hsupp : tsupport (fun y ↦ Real.smoothTransition (∑ i ∈ t, ρ i y)) ⊆ C :=
    closure_minimal (fun y hy ↦ by_contra fun h ↦ mem_support.1 hy (hσC y h)) hC.isClosed
  refine ⟨fun y ↦ Real.smoothTransition (∑ i ∈ t, ρ i y),
    Real.smoothTransition.contDiff.contMDiff.comp (ContMDiff.sum fun i _ ↦ (ρ i).contMDiff),
    ?_, hC.of_isClosed_subset (isClosed_tsupport _) hsupp,
    hsupp.trans (iUnion₂_subset fun i _ ↦ (hρ i).2),
    fun y ↦ ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩⟩
  filter_upwards [(isOpen_biUnion fun _ _ ↦ isOpen_interior).mem_nhdsSet.2 ht] with y hy
  obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.1 hy
  refine Real.smoothTransition.one_of_one_le ?_
  have := Finset.single_le_sum (fun j _ ↦ (ρ j).nonneg) hi (f := fun j ↦ ρ j y)
  rwa [(interior_subset hyi : ρ i y = 1)] at this

variable (I) in
/-- **A bundled smooth cutoff around a compact set.** A compact subset `K` of a Hausdorff manifold
modelled on a finite-dimensional space has a smooth compactly supported function `χ : C^∞(M, ℝ)`
equal to `1` on a neighbourhood of `K`. -/
theorem IsCompact.exists_contMDiffMap_one_nhds_hasCompactSupport {K : Set M} (hK : IsCompact K) :
    ∃ χ : C^∞⟮I, M; ℝ⟯, HasCompactSupport χ ∧ ∀ᶠ x in 𝓝ˢ K, χ x = 1 := by
  obtain ⟨χ, hχ, h1, hc, -, -⟩ :=
    hK.exists_contMDiff_one_nhds_tsupport_subset I isOpen_univ (subset_univ _)
  exact ⟨⟨χ, hχ⟩, hc, h1⟩

end

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
/-- Decompose a compactly supported `C^k` vector field `X` into a finite sum of compactly
supported `C^k` vector fields `Y i`, each supported in `U (c i)`, for any family of neighbourhoods
`U x ∈ 𝓝 x` covering `tsupport X`. -/
theorem HasCompactSupport.exists_subordinate_vectorField_sum
    {k : ℕ∞ω} [ENat.LEInfty k] [IsManifold I 1 M] [IsManifold I (k + 1) M]
    {X : (x : M) → TangentSpace I x} (hc : HasCompactSupport (β := E) X)
    (hX : ContMDiff I I.tangent k (T% X)) {U : M → Set M}
    (hU : ∀ x ∈ tsupport (α := E) X, U x ∈ 𝓝 x) :
    ∃ (ι : Type u) (_ : Fintype ι) (c : ι → M) (Y : ι → (x : M) → TangentSpace I x),
      (∀ i, ContMDiff I I.tangent k (T% (Y i))) ∧
      (∀ i, HasCompactSupport (β := E) (Y i)) ∧
      (∀ i, tsupport (α := E) (Y i) ⊆ U (c i)) ∧
      (∀ x, X x = ∑ i, Y i x) := by
  classical
  have : IsManifold I k M := IsManifold.of_le (n := k + 1) le_self_add
  obtain ⟨ι, _, bc, hbc⟩ := hc.exists_smoothBumpCovering_isSubordinate I hU
  let bc' : BumpCovering ι M (tsupport (α := E) X) :=
    { toFun i := ⟨bc i, (SmoothBumpFunction.contMDiff_of_isManifold (n := k) (bc i)).continuous⟩
      locallyFinite' := bc.locallyFinite
      nonneg' i _ := (bc i).nonneg
      le_one' i _ := (bc i).le_one
      eventuallyEq_one' := bc.eventuallyEq_one' }
  let ρ := bc'.toPartitionOfUnity
  have hρ_diff (i : ι) : ContMDiff I 𝓘(ℝ) k (ρ i) :=
    bc'.contMDiff_toPartitionOfUnity_of_contMDiff
      (fun j ↦ SmoothBumpFunction.contMDiff_of_isManifold (n := k) (bc j)) i
  let Y : ι → (x : M) → TangentSpace I x := fun i x ↦ ρ i x • X x
  have hY (i : ι) : ContMDiff I I.tangent k (T% (Y i)) := (hρ_diff i).smul_section hX
  have hsum (x : M) : X x = ∑ i, Y i x := by
    by_cases hx : x ∈ tsupport (α := E) X
    · have h1 : ∑ i, ρ i x = 1 := by
        rw [← finsum_eq_sum_of_fintype]
        exact ρ.sum_eq_one hx
      rw [← Finset.sum_smul, h1, one_smul]
    · have hx0 : X x = 0 := image_eq_zero_of_notMem_tsupport (α := E) hx
      simp [Y, hx0]
  exact ⟨ι, inferInstance, bc.c, Y, hY,
    fun i ↦ hc.of_isClosed_subset (isClosed_tsupport _) (tsupport_smul_subset_right _ _),
    fun i ↦ (tsupport_smul_subset_left _ _).trans <|
      (closure_mono (bc'.support_toPartitionOfUnity_subset i)).trans (hbc i),
    hsum⟩
