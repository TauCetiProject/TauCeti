/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Intrinsic
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import TauCeti.Analysis.Analytic.Submanifold.Basic
public import TauCeti.Analysis.Convex.StdSimplex
import TauCeti.Analysis.Analytic.Submanifold.Transport
import TauCeti.Analysis.Convex.Intrinsic
import TauCeti.Analysis.Convex.OpenSimplex
import TauCeti.Topology.Algebra.Module.SubspaceExchange

/-!
# Affine subspaces, intrinsic interiors, and open simplices as analytic submanifolds

Over any nontrivially normed field `𝕜`, every linear subspace `W` of `Fin n → 𝕜` is an analytic
submanifold of dimension `Module.finrank 𝕜 W`, every nonempty affine subspace `A` is an analytic
submanifold of dimension `Module.finrank 𝕜 A.direction`, and every nonempty intrinsic interior
`intrinsicInterior 𝕜 s` is an analytic submanifold of dimension `Module.finrank 𝕜 (vectorSpan 𝕜 s)`.
No completeness assumption on `𝕜` is needed: any linear equivalence of `Fin n → 𝕜` is continuous
in both directions because `Fin n → 𝕜` carries the product topology
(`Submodule.exists_continuousLinearEquiv_preimage_coordSubspace`).

Over `ℝ`, this equips every nonempty open simplex — the intrinsic interior of the convex hull of a
nonempty finite affinely independent family — with the structure of an analytic submanifold of
dimension one less than its number of vertices, and in particular makes `TauCeti.openStdSimplex ℝ`
in `Fin m → ℝ` (`m ≥ 1`) an `(m - 1)`-dimensional analytic submanifold and each open facet
`TauCeti.openStdSimplexFacet ℝ i` (`m ≥ 2`) an `(m - 2)`-dimensional analytic submanifold.

## Main results

* `Submodule.isAnalyticSubmanifold`: a linear subspace `W ≤ (Fin n → 𝕜)` is a
  `(Module.finrank 𝕜 W)`-dimensional analytic submanifold.
* `AffineSubspace.isAnalyticSubmanifold`: a nonempty affine subspace `A` of `Fin n → 𝕜` is a
  `(Module.finrank 𝕜 A.direction)`-dimensional analytic submanifold.
* `TauCeti.isAnalyticSubmanifold_intrinsicInterior`: a nonempty intrinsic interior
  `intrinsicInterior 𝕜 s` in `Fin n → 𝕜` is a `(Module.finrank 𝕜 (vectorSpan 𝕜 s))`-dimensional
  analytic submanifold.
* `AffineIndependent.isAnalyticSubmanifold_intrinsicInterior_convexHull`: open simplices in
  `Fin n → ℝ` are analytic submanifolds of dimension `Fintype.card ι - 1`.
* `TauCeti.isAnalyticSubmanifold_openStdSimplex`,
  `TauCeti.isAnalyticSubmanifold_openStdSimplexFacet`: `TauCeti.openStdSimplex ℝ (Fin m)` and
  `TauCeti.openStdSimplexFacet ℝ i` are analytic submanifolds of dimensions `m - 1` and `m - 2`.

## References

* S. G. Krantz and H. R. Parks, *A Primer of Real Analytic Functions*, second edition,
  Birkhäuser, 2002, Chapter 2 (real analytic submanifolds).
* S. Łojasiewicz, *Triangulation of semi-analytic sets*, Annali della Scuola Normale Superiore di
  Pisa (3) 18 (1964), 449–474, §4 (analytic open simplices).
-/

public section

open Set Topology Convexity

section NormedField

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : ℕ}

/-- Every linear subspace `W` of `Fin n → 𝕜` is an analytic submanifold of dimension
`Module.finrank 𝕜 W`. -/
theorem Submodule.isAnalyticSubmanifold (W : Submodule 𝕜 (Fin n → 𝕜)) :
    TauCeti.IsAnalyticSubmanifold (Module.finrank 𝕜 W) (W : Set (Fin n → 𝕜)) := by
  obtain ⟨e, he⟩ := W.exists_continuousLinearEquiv_preimage_coordSubspace
  exact he ▸ (TauCeti.isAnalyticSubmanifold_coordSubspace
    (by simpa using W.finrank_le)).preimage_continuousLinearEquiv e

/-- Every nonempty affine subspace `A` of `Fin n → 𝕜` is an analytic submanifold of dimension
`Module.finrank 𝕜 A.direction`. -/
theorem AffineSubspace.isAnalyticSubmanifold {A : AffineSubspace 𝕜 (Fin n → 𝕜)}
    (hA : (A : Set (Fin n → 𝕜)).Nonempty) :
    TauCeti.IsAnalyticSubmanifold (Module.finrank 𝕜 A.direction) (A : Set (Fin n → 𝕜)) := by
  obtain ⟨x₀, hx₀⟩ := hA
  have htran : (A : Set (Fin n → 𝕜)) = (x₀ + ·) '' (A.direction : Set (Fin n → 𝕜)) := by
    ext x
    refine ⟨fun hx ↦ ⟨x - x₀, (AffineSubspace.vsub_right_mem_direction_iff_mem hx₀ x).2 hx,
      add_sub_cancel x₀ x⟩, ?_⟩
    rintro ⟨v, hv, rfl⟩
    simpa using (AffineSubspace.vsub_right_mem_direction_iff_mem hx₀ (x₀ + v)).1 (by simpa using hv)
  rw [htran]
  exact A.direction.isAnalyticSubmanifold.translate x₀

/-- Every nonempty intrinsic interior `intrinsicInterior 𝕜 s` in `Fin n → 𝕜` is an analytic
submanifold of dimension `Module.finrank 𝕜 (vectorSpan 𝕜 s)`. -/
theorem TauCeti.isAnalyticSubmanifold_intrinsicInterior {s : Set (Fin n → 𝕜)}
    (hne : (intrinsicInterior 𝕜 s).Nonempty) :
    TauCeti.IsAnalyticSubmanifold (Module.finrank 𝕜 (vectorSpan 𝕜 s))
      (intrinsicInterior 𝕜 s) := by
  have hsub : intrinsicInterior 𝕜 s ⊆ (affineSpan 𝕜 s : Set (Fin n → 𝕜)) :=
    TauCeti.intrinsicInterior_subset_affineSpan
  have hA : TauCeti.IsAnalyticSubmanifold (Module.finrank 𝕜 (vectorSpan 𝕜 s))
      (affineSpan 𝕜 s : Set (Fin n → 𝕜)) := by
    rw [← direction_affineSpan]
    exact (affineSpan 𝕜 s).isAnalyticSubmanifold (hne.mono hsub)
  exact hA.of_isOpen_preimage_val hsub TauCeti.isOpen_preimage_val_intrinsicInterior hne

end NormedField

section RealSimplex

variable {n m : ℕ}

/-- **Open simplices are analytic submanifolds.** The intrinsic interior of the convex hull of a
nonempty finite affinely independent family `p : ι → Fin n → ℝ` is an analytic submanifold of
dimension `Fintype.card ι - 1`. -/
theorem AffineIndependent.isAnalyticSubmanifold_intrinsicInterior_convexHull
    {ι : Type*} [Fintype ι] [Nonempty ι] {p : ι → Fin n → ℝ} (hp : AffineIndependent ℝ p) :
    TauCeti.IsAnalyticSubmanifold (Fintype.card ι - 1)
      (intrinsicInterior ℝ (convexHull ℝ (range p))) := by
  have hdim : Module.finrank ℝ (vectorSpan ℝ (convexHull ℝ (range p))) = Fintype.card ι - 1 := by
    rw [← direction_affineSpan, affineSpan_convexHull, direction_affineSpan]
    exact hp.finrank_vectorSpan
      (Nat.sub_add_cancel (Nat.succ_le_iff.2 Fintype.card_pos)).symm
  rw [← hdim]
  exact TauCeti.isAnalyticSubmanifold_intrinsicInterior
    ⟨_, hp.centroid_mem_intrinsicInterior_convexHull⟩

namespace TauCeti

/-- For a nonempty set `t` of coordinates of `Fin m`, the open coordinate face of the standard
simplex spanned by `t` is a `(t.card - 1)`-dimensional analytic submanifold. -/
theorem isAnalyticSubmanifold_intrinsicInterior_convexHull_pi_single
    {t : Finset (Fin m)} (ht : t.Nonempty) :
    IsAnalyticSubmanifold (t.card - 1)
      (intrinsicInterior ℝ
        (convexHull ℝ ((fun i : Fin m => (Pi.single i 1 : Fin m → ℝ)) '' t))) := by
  have : Nonempty (t : Set (Fin m)) := ht.coe_sort
  have hcard : Fintype.card (t : Set (Fin m)) = t.card := Fintype.card_coe t
  rw [Set.image_eq_range, ← hcard]
  exact (affineIndependent_pi_single ℝ
    (t : Set (Fin m))).isAnalyticSubmanifold_intrinsicInterior_convexHull

/-- The open standard simplex `openStdSimplex ℝ (Fin m)` (`m ≥ 1`) is an `(m - 1)`-dimensional
analytic submanifold. -/
theorem isAnalyticSubmanifold_openStdSimplex [NeZero m] :
    IsAnalyticSubmanifold (m - 1) (openStdSimplex ℝ (Fin m)) := by
  rw [← intrinsicInterior_range_toFun_comp_weights, ← convexHull_range_pi_single, ← image_univ]
  simpa using isAnalyticSubmanifold_intrinsicInterior_convexHull_pi_single
    (t := (Finset.univ : Finset (Fin m))) Finset.univ_nonempty

/-- For `m ≥ 2`, the `i`-th open facet `openStdSimplexFacet ℝ i` of the standard simplex in
`Fin m → ℝ` is an `(m - 2)`-dimensional analytic submanifold. -/
theorem isAnalyticSubmanifold_openStdSimplexFacet [Nontrivial (Fin m)] (i : Fin m) :
    IsAnalyticSubmanifold (m - 2) (openStdSimplexFacet ℝ i) := by
  obtain ⟨j, hj⟩ := exists_ne i
  have hne : (Finset.univ.erase i).Nonempty := ⟨j, Finset.mem_erase.2 ⟨hj, Finset.mem_univ j⟩⟩
  have hcard : (Finset.univ.erase i).card - 1 = m - 2 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_fin]
    omega
  rw [← intrinsicInterior_facet_range_toFun_comp_weights, ← convexHull_pi_single_compl_singleton,
    ← hcard]
  have hcoe : ((Finset.univ.erase i : Finset (Fin m)) : Set (Fin m)) = {i}ᶜ := by
    ext k
    simp
  rw [← hcoe]
  exact isAnalyticSubmanifold_intrinsicInterior_convexHull_pi_single hne

end TauCeti

end RealSimplex
