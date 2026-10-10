/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import Mathlib.Analysis.InnerProductSpace.Orthonormal
public import TauCeti.Analysis.InnerProductSpace.LpIndexCongr
public import Mathlib.Analysis.Normed.Lp.LpEquiv
public import Mathlib.Topology.Bases

/-!
# Separability bounds the size of an orthonormal set

Two facts, in increasing specificity.

* `TauCeti.countable_of_pairwise_dist_le`: a uniformly separated set in a separable metric
  space is countable.
* `TauCeti.countable_of_orthonormal`: an orthonormal set in a separable inner
  product space is countable, because distinct orthonormal vectors are `√2` apart.

The second is the step Mathlib does not have, and it is the one a Hilbert-space classification
at separable scope needs first: it is what turns "the space is separable" into "the Hilbert
basis is indexed by a countable set", after which two infinite-dimensional separable Hilbert
spaces can be compared through `HilbertBasis.repr`.

Davis and Kahan work throughout on a separable Hilbert space, so this is the scope in which
their condition (3.5) -- equality of the Hilbert dimensions of two crossed defect spaces -- can
be connected to this repository's `CrossedDefectsEquivalent`, which asserts a linear isometric
equivalence.  In finite dimension the two readings are already proved equal
(`crossedDefectsEquivalent_iff_finrank_eq`); the separable infinite-dimensional half is what
remains, and it starts here.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Extraction class: **authored in place** for the Tau Ceti staging layer.
  `TauCeti.countable_of_pairwise_dist_le` was previously stated inside
  `ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/SeparableCyclic.lean`, which is a
  consumer rather than its owner; it moved here with its orthonormal corollary, and that module
  now imports this one.
* Spectra influence: **none** -- this module imports only Mathlib.
-/

namespace TauCeti

/-- **A uniformly separated set in a separable metric space is countable.**

Each member is tagged by a point of a fixed countable dense set within `δ / 2` of it, and the
tag determines the member because two members sharing a tag would be within `δ`. -/
public theorem countable_of_pairwise_dist_le {M : Type*} [MetricSpace M]
    [TopologicalSpace.SeparableSpace M] {s : Set M} {δ : ℝ} (hδ : 0 < δ)
    (h : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → δ ≤ dist x y) : s.Countable := by
  classical
  obtain ⟨t, htc, htd⟩ := TopologicalSpace.exists_countable_dense M
  have hchoice : ∀ x : M, ∃ y, y ∈ t ∧ dist x y < δ / 2 := fun x =>
    Metric.mem_closure_iff.mp (htd x) (δ / 2) (by positivity)
  choose g hgt hgd using hchoice
  refine Set.MapsTo.countable_of_injOn (f := g) (fun x _ => hgt x) ?_ htc
  intro x hx y hy hxy
  by_contra hne
  have hlt : dist x y < δ := by
    calc dist x y ≤ dist x (g x) + dist (g x) y := dist_triangle _ _ _
      _ = dist x (g x) + dist y (g y) := by rw [hxy, dist_comm (g y) y]
      _ < δ / 2 + δ / 2 := add_lt_add (hgd x) (hgd y)
      _ = δ := by ring
  exact absurd (h x hx y hy hne) (not_le.mpr hlt)

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **Distinct members of an orthonormal set are `√2` apart.** -/
public theorem dist_eq_sqrt_two_of_orthonormal {s : Set E}
    (h : Orthonormal 𝕜 ((↑) : s → E)) {x y : E} (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≠ y) :
    dist x y = Real.sqrt 2 := by
  have hne : (⟨x, hx⟩ : s) ≠ ⟨y, hy⟩ := by
    simpa [Subtype.ext_iff] using hxy
  have hinner : (inner 𝕜 x y : 𝕜) = 0 := h.2 hne
  have hnx : ‖x‖ = 1 := h.1 ⟨x, hx⟩
  have hny : ‖y‖ = 1 := h.1 ⟨y, hy⟩
  have hsq : ‖x - y‖ ^ 2 = 2 := by
    rw [@norm_sub_sq 𝕜, hinner, hnx, hny]
    norm_num
  have hnn : 0 ≤ ‖x - y‖ := norm_nonneg _
  rw [dist_eq_norm]
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2, hsq, hnn]

/-- **An orthonormal set in a separable inner product space is countable.**

Distinct orthonormal vectors are `√2 ≥ 1` apart, so the set is uniformly separated and
`TauCeti.countable_of_pairwise_dist_le` applies.  Mathlib proves that every Hilbert space has a
Hilbert basis but says nothing about its size; this is the missing step that makes "separable"
into "countably indexed". -/
public theorem countable_of_orthonormal
    [TopologicalSpace.SeparableSpace E] {s : Set E}
    (h : Orthonormal 𝕜 ((↑) : s → E)) : s.Countable := by
  refine countable_of_pairwise_dist_le (δ := 1) one_pos ?_
  intro x hx y hy hxy
  rw [dist_eq_sqrt_two_of_orthonormal h hx hy hxy]
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]

/-! ## Separable Hilbert spaces are classified by the size of a Hilbert basis

Mathlib proves that every Hilbert space has a Hilbert basis (`exists_hilbertBasis`) but says
nothing about how large it is.  With `countable_of_orthonormal` the separable case is settled:
the index set is countable, so two separable Hilbert spaces whose bases are both countably
infinite are isometric, by `TauCeti.nonempty_linearIsometryEquiv_of_hilbertBasis` through the
`ℓ²` reindexing.

This is the half of Davis--Kahan's condition (3.5) that the finite-dimensional bridge
`crossedDefectsEquivalent_iff_finrank_eq` does not reach. -/

section Classification

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- **A separable Hilbert space has a countably indexed Hilbert basis.**

`exists_hilbertBasis` produces one indexed by a set of vectors that is orthonormal; separability
makes that set countable. -/
public theorem exists_countable_hilbertBasis [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E] :
    ∃ (w : Set E) (_b : HilbertBasis w 𝕜 E), w.Countable := by
  obtain ⟨w, b, hb⟩ := exists_hilbertBasis 𝕜 E
  refine ⟨w, b, countable_of_orthonormal (𝕜 := 𝕜) ?_⟩
  have := b.orthonormal
  rwa [hb] at this

/-- **Two Hilbert spaces with countably infinite Hilbert bases are isometric.**

Two countably infinite index types are equinumerous, and the `ℓ²` reindexing carries one space
onto the other.  Separability enters through `exists_countable_hilbertBasis`, which is what
supplies `Countable` on the index; it is not needed again here. -/
public theorem nonempty_linearIsometryEquiv_of_countable_infinite_hilbertBasis
    {ι ι' : Type*} [Countable ι] [Infinite ι] [Countable ι'] [Infinite ι']
    (b : HilbertBasis ι 𝕜 E) (b' : HilbertBasis ι' 𝕜 F) :
    Nonempty (E ≃ₗᵢ[𝕜] F) :=
  nonempty_linearIsometryEquiv_of_hilbertBasis b b' nonempty_equiv_of_countable.some

/-- **Two separable Hilbert spaces with infinite Hilbert bases are isometric.**

The form the classification is actually used in: `exists_hilbertBasis` hands back a basis indexed
by an orthonormal *set* of vectors, so `hb` is the identification it comes with, separability
makes that set countable, and the hypothesis is only that it is infinite. -/
public theorem nonempty_linearIsometryEquiv_of_separable_of_infinite_hilbertBasis
    [CompleteSpace E] [TopologicalSpace.SeparableSpace E]
    [CompleteSpace F] [TopologicalSpace.SeparableSpace F]
    {w : Set E} {b : HilbertBasis w 𝕜 E} (hb : ⇑b = ((↑) : w → E)) (hw : w.Infinite)
    {w' : Set F} {b' : HilbertBasis w' 𝕜 F} (hb' : ⇑b' = ((↑) : w' → F)) (hw' : w'.Infinite) :
    Nonempty (E ≃ₗᵢ[𝕜] F) := by
  have hcw : w.Countable := countable_of_orthonormal (𝕜 := 𝕜) (by
    have h := b.orthonormal; rwa [hb] at h)
  have hcw' : w'.Countable := countable_of_orthonormal (𝕜 := 𝕜) (by
    have h := b'.orthonormal; rwa [hb'] at h)
  have := hcw.to_subtype
  have := hcw'.to_subtype
  have := hw.to_subtype
  have := hw'.to_subtype
  exact nonempty_linearIsometryEquiv_of_countable_infinite_hilbertBasis b b'

/-- **A finitely indexed Hilbert basis makes the space finite-dimensional.**

Through `lpPiLpₗᵢ`, the `ℓ²` model over a finite index is `PiLp 2` over that index, which is
finite-dimensional. -/
public theorem finiteDimensional_of_finite_hilbertBasis {ι : Type*} [Finite ι]
    (b : HilbertBasis ι 𝕜 E) : FiniteDimensional 𝕜 E := by
  have : Fintype ι := Fintype.ofFinite ι
  exact (b.repr.trans (lpPiLpₗᵢ (fun _ : ι => 𝕜) 𝕜)).toLinearEquiv.symm.finiteDimensional

/-- **Any two infinite-dimensional separable Hilbert spaces over the same field are
isometrically isomorphic.**

This is the classification the paper's separable scope permits, in the form Davis--Kahan's
condition (3.5) needs: the two crossed defect spaces have "the same Hilbert dimension" exactly
when they are both finite-dimensional of equal `finrank` or both infinite-dimensional, and in
the second case they are isometric with no further data.

The first case is `crossedDefectsEquivalent_iff_finrank_eq`; this is the second. -/
public theorem nonempty_linearIsometryEquiv_of_separable_of_infiniteDimensional
    [CompleteSpace E] [TopologicalSpace.SeparableSpace E]
    [CompleteSpace F] [TopologicalSpace.SeparableSpace F]
    (hE : ¬ FiniteDimensional 𝕜 E) (hF : ¬ FiniteDimensional 𝕜 F) :
    Nonempty (E ≃ₗᵢ[𝕜] F) := by
  classical
  obtain ⟨w, b, hb⟩ := exists_hilbertBasis 𝕜 E
  obtain ⟨w', b', hb'⟩ := exists_hilbertBasis 𝕜 F
  have hw : w.Infinite := by
    by_contra hfin
    rw [Set.not_infinite] at hfin
    have : Finite w := hfin
    exact hE (finiteDimensional_of_finite_hilbertBasis b)
  have hw' : w'.Infinite := by
    by_contra hfin
    rw [Set.not_infinite] at hfin
    have : Finite w' := hfin
    exact hF (finiteDimensional_of_finite_hilbertBasis b')
  exact nonempty_linearIsometryEquiv_of_separable_of_infinite_hilbertBasis hb hw hb' hw'

end Classification

end TauCeti
