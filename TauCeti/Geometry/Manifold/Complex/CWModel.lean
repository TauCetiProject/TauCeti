/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Immersion
public import TauCeti.Geometry.Manifold.Complex.LeviForm
public import TauCeti.Geometry.Manifold.Morse.CWModel.Proper
public import TauCeti.Geometry.Manifold.Morse.CWModel.Relative
public import TauCeti.Geometry.Manifold.RegularValue.Polynomial
import TauCeti.AlgebraicTopology.Cellular.Dimension
import TauCeti.Geometry.Manifold.Complex.ExhaustionHomology
import TauCeti.Geometry.Manifold.Complex.SquaredDistance
import TauCeti.Topology.CWComplex.Classical.Finite
import TauCeti.Topology.Maps.Proper.Metric

/-!
# CW homotopy models of pseudoconvex complex manifolds and closed holomorphic embeddings

On a complex manifold `M` of complex dimension `n`, a real Morse function `f` that is strongly
`q`-pseudoconvex at its critical points has real Morse index at most `n + q` at each of them
(`TauCeti.IsManifoldStronglyPseudoconvexAt.manifoldMorseIndex_le`). Feeding this index bound into
the relative and proper Morse CW models upgrades the homological and cohomological vanishing results
of `TauCeti/Geometry/Manifold/Complex/SublevelHomology.lean` and
`TauCeti/Geometry/Manifold/Complex/ExhaustionHomology.lean` to genuine cellular homotopy models:

* Across a compact band `f⁻¹[a, b]` between regular values of a strongly `q`-pseudoconvex Morse
  function, `{f ≤ b}` is homotopy equivalent to a finite CW complex relative to `{f ≤ a}` with one
  `m`-cell for each critical point of index `m` in `(a, b]` and no cells in dimensions strictly
  above `n + q`
  (`IsMorse.exists_relCWComplex_homotopyEquiv_sublevel_of_isManifoldStronglyPseudoconvexAt`).
  Consequently, both the cellular Morse polynomial identity and Euler's alternating-sum equality for
  the sublevel pair hold already from degree `n + q` onwards rather than only from `2n`.
* Along a proper bounded-below strongly `q`-pseudoconvex Morse exhaustion, `M` is homotopy
  equivalent to a finite-dimensional Hausdorff CW complex `X` exhausted by finite subcomplexes `W k`
  modelling a regular sublevel exhaustion `{f ≤ a k}`, with cells corresponding to the critical
  points of `f` and no cells in dimensions strictly above `n + q`
  (`TauCeti.IsMorse.exists_cwComplex_subcomplex_homotopyEquiv_of_isManifoldStronglyPseudoconvexAt`,
  `TauCeti.IsMorse.exists_cwComplex_homotopyEquiv_of_isManifoldStronglyPseudoconvexAt`).
* By Whitney `C^∞` Morse approximation preserving strong `q`-pseudoconvexity and properness
  (`ContMDiffMap.exists_isMorse_isProperMap_bddBelow_isManifoldStronglyPseudoconvexAt`), any smooth
  (not necessarily Morse) proper bounded-below everywhere strongly `q`-pseudoconvex exhaustion gives
  a Hausdorff CW homotopy model of `M` of dimension at most `n + q`
  (`TauCeti.exists_cwComplex_homotopyEquiv_of_isProperMap_of_isManifoldStronglyPseudoconvexAt`), and
  of dimension at most `n` in the strictly plurisubharmonic case `q = 0`
  (`TauCeti.exists_cwComplex_homotopyEquiv_of_isProperMap_of_isManifoldStrictlyPlurisubharmonicAt`).
* Along a proper holomorphic immersion of `M` into any finite-dimensional complex normed space `F` —
  and in particular along any closed holomorphic embedding `M → F`, with Hausdorffness of `M` and
  finite-dimensionality of its model space deduced automatically — `M` is homotopy equivalent to a
  Hausdorff CW complex of dimension at most `n`
  (`TauCeti.exists_cwComplex_homotopyEquiv_of_isProperMap_holomorphic_immersion`,
  `TauCeti.exists_cwComplex_homotopyEquiv_of_isClosedEmbedding`,
  `Manifold.IsImmersion.exists_cwComplex_homotopyEquiv_of_isProperMap`,
  `Manifold.IsImmersion.exists_cwComplex_homotopyEquiv_of_isClosedEmbedding`). Specializing to
  polynomial regular zero loci gives the Andreotti–Frankel CW homotopy theorem for smooth affine
  complete intersections (`TauCeti.exists_cwComplex_homotopyEquiv_affineZeroLocus`).

## Main results

* `TauCeti.IsMorse.exists_relCWComplex_homotopyEquiv_sublevel_of_isManifoldStronglyPseudoconvexAt`:
  finite relative CW model of a compact regular band of a strongly `q`-pseudoconvex Morse function,
  with no relative cells above dimension `finrank ℂ E + q`.
* `IsMorse.exists_relCWComplex_sum_range_monomial_sublevelPair_of_isManifoldStronglyPseudoconvexAt`
  and `IsMorse.sum_range_finrank_singularHomology_sublevelPair_of_isManifoldStronglyPseudoconvexAt`:
  cellular Morse polynomial identity and Euler equality truncated at any `m ≥ finrank ℂ E + q`.
* `TauCeti.IsMorse.exists_cwComplex_subcomplex_homotopyEquiv_of_isManifoldStronglyPseudoconvexAt`
  and `TauCeti.IsMorse.exists_cwComplex_homotopyEquiv_of_isManifoldStronglyPseudoconvexAt`:
  sublevel-filtered and global CW homotopy models of proper strongly `q`-pseudoconvex Morse
  exhaustions.
* `TauCeti.exists_cwComplex_homotopyEquiv_of_isProperMap_of_isManifoldStronglyPseudoconvexAt` and
  `TauCeti.exists_cwComplex_homotopyEquiv_of_isProperMap_of_isManifoldStrictlyPlurisubharmonicAt`:
  CW homotopy models of dimension at most `finrank ℂ E + q` (respectively `finrank ℂ E`) for smooth
  non-Morse pseudoconvex and strictly plurisubharmonic exhaustions.
* `TauCeti.IsMorse.exists_cwComplex_subcomplex_homotopyEquiv_norm_sq_sub_comp` and
  `TauCeti.IsMorse.exists_cwComplex_homotopyEquiv_norm_sq_sub_comp`: sublevel-filtered and global CW
  models for Morse squared distance along a proper holomorphic immersion into a proper complex inner
  product space.
* `TauCeti.exists_cwComplex_homotopyEquiv_of_isProperMap_holomorphic_immersion`,
  `TauCeti.exists_cwComplex_homotopyEquiv_of_isClosedEmbedding`,
  `Manifold.IsImmersion.exists_cwComplex_homotopyEquiv_of_isProperMap`,
  `Manifold.IsImmersion.exists_cwComplex_homotopyEquiv_of_isClosedEmbedding`: Andreotti–Frankel CW
  dimension bound for proper holomorphic immersions and closed holomorphic embeddings into any
  finite-dimensional complex normed space.
* `TauCeti.IsMorse.exists_cwComplex_homotopyEquiv_norm_sq_sub_toLp_affineZeroLocus` and
  `TauCeti.exists_cwComplex_homotopyEquiv_affineZeroLocus`: CW homotopy models of smooth affine
  complete intersections of dimension at most `|σ| - |ι|`.

## References

* A. Andreotti and T. Frankel, *The Lefschetz theorem on hyperplane sections*, Annals of Mathematics
  69 (1959), 713–717.
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Section 7, Theorems 7.1 and 7.2.
* R. Lazarsfeld, *Positivity in Algebraic Geometry I*, Ergebnisse der Mathematik und ihrer
  Grenzgebiete (3) 48, Springer-Verlag, 2004, Section 3.1.A, Theorem 3.1.1.
-/

public section

noncomputable section

open AlgebraicTopology CategoryTheory ContMDiffMap Filter Limits Module Set Topology
open Topology.RelCWComplex
open Polynomial (monomial X)
open scoped ContDiff ContinuousMap Manifold Polynomial

universe u

namespace TauCeti

/-! ### Auxiliary lemmas for empty and proper complex manifolds -/

/-- An empty topological space in `Type u` is homotopy equivalent to `PEmpty.{u + 1}`, a Hausdorff
finite-dimensional CW complex with no cells in any dimension. -/
private theorem exists_cwComplex_homotopyEquiv_of_isEmpty (M : Type u) [TopologicalSpace M]
    [IsEmpty M] (d : ℕ) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      CWComplex.FiniteDimensional (univ : Set X) ∧ Nonempty (M ≃ₕ X) ∧
      ∀ m, d < m → IsEmpty (cell (univ : Set X) m) := by
  let _ : CWComplex (univ : Set PEmpty.{u + 1}) := CWComplex.ofDiscreteTopology
  have hempty (m : ℕ) : IsEmpty (cell (univ : Set PEmpty.{u + 1}) m) :=
    ⟨fun j ↦ isEmptyElim (map m j 0)⟩
  exact ⟨PEmpty.{u + 1}, _, inferInstance, ‹_›,
    CWComplex.finiteDimensional_of_isEmpty_cell_gt _ (d := 0) fun m _ ↦ hempty m,
    ⟨Homeomorph.empty.toHomotopyEquiv⟩, fun m _ ↦ hempty m⟩

/-- A nonempty Hausdorff manifold modelled on a complex normed space `E` and admitting a proper map
to a weakly locally compact space is locally compact, hence `E` is finite-dimensional by Riesz's
theorem (`FiniteDimensional.of_locallyCompact_manifold`). -/
private theorem finiteDimensional_of_isProperMap {E M Y : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M] [Nonempty M]
    [TopologicalSpace Y] [WeaklyLocallyCompactSpace Y] {f : M → Y} (hf : IsProperMap f) :
    FiniteDimensional ℂ E := by
  have : WeaklyLocallyCompactSpace M := ⟨fun x ↦
    let ⟨K, hKc, hxK⟩ := exists_compact_mem_nhds (f x)
    ⟨f ⁻¹' K, hf.isCompact_preimage hKc, hf.continuous.continuousAt.preimage_mem_nhds hxK⟩⟩
  exact FiniteDimensional.of_locallyCompact_manifold M 𝓘(ℂ, E)

/-! ### Compact regular bands of strongly `q`-pseudoconvex Morse functions -/

section Band

variable {E : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M] [T2Space M]

local instance : FiniteDimensional ℝ E := Module.Finite.trans ℂ E

local instance : IsManifold 𝓘(ℝ, E) ∞ M :=
  IsManifold.restrictScalars ℝ (inferInstance : IsManifold 𝓘(ℂ, E) ∞ M)

/-- **Relative CW model of a compact regular band of a strongly `q`-pseudoconvex Morse function.**
Let `f` be a real Morse function on a complex manifold `M` of complex dimension `n`, `a ≤ b` regular
values with compact band `f⁻¹[a, b]`, and suppose `f` is strongly `q`-pseudoconvex at every critical
point with value in `(a, b]`. Then `{f ≤ b}` is homotopy equivalent to a finite CW complex `X`
relative to the image of a closed embedding `j : {f ≤ a} → X`, extending the inclusion
`{f ≤ a} ⊆ {f ≤ b}`, whose relative `m`-cells correspond to the critical points of index `m` in
`(a, b]` and which has no relative cells in dimensions strictly above `n + q`. -/
theorem IsMorse.exists_relCWComplex_homotopyEquiv_sublevel_of_isManifoldStronglyPseudoconvexAt
    {f : M → ℝ} {q : ℕ} (hf : IsMorse 𝓘(ℝ, E) f) {a b : ℝ} (hab : a ≤ b)
    (hcompact : IsCompact (f ⁻¹' Icc a b)) (ha : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f a)
    (hb : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f b)
    (hq : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Ioc a b,
      IsManifoldStronglyPseudoconvexAt E q f x) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (j : C({x | f x ≤ a}, X))
      (_ : RelCWComplex (univ : Set X) (range j)) (h : X ≃ₕ {x | f x ≤ b}),
      IsClosedEmbedding j ∧ RelCWComplex.Finite (univ : Set X) ∧ (∀ x, (h (j x) : M) = x) ∧
      (∀ m, Nonempty (cell (univ : Set X) m ≃
        ↥{x ∈ criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Ioc a b | manifoldMorseIndex 𝓘(ℝ, E) f x = m})) ∧
      ∀ m, finrank ℂ E + q < m → IsEmpty (cell (univ : Set X) m) := by
  obtain ⟨X, _, _, j, _, h, hj, hh, ⟨c⟩⟩ :=
    hf.exists_relCWComplex_homotopyEquiv_sublevel hab hcompact ha hb
  have := finite_sigma_criticalPoints_inter ((hf.finite_criticalPoints_inter hcompact).subset
    (inter_subset_inter_right _ (preimage_mono Ioc_subset_Icc_self)))
  refine ⟨X, _, ‹_›, j, ‹_›, h, hj,
    RelCWComplex.finite_of_finite_cells (.of_equiv _ (Equiv.sigmaCongrRight c).symm),
    hh, fun m ↦ ⟨c m⟩, fun m hm ↦ (c m).isEmpty_congr.2 ⟨fun ⟨x, hx, hxm⟩ ↦ ?_⟩⟩
  exact hm.not_ge (hxm ▸ (hq x hx).manifoldMorseIndex_le_of_mem_criticalPoints
    (hf.contMDiff x) hx.1)

/-- **Truncated cellular Morse polynomial identity on a strongly `q`-pseudoconvex band.** Under the
hypotheses of
`TauCeti.IsMorse.exists_relCWComplex_homotopyEquiv_sublevel_of_isManifoldStronglyPseudoconvexAt`,
there is a finite relative CW model `(W, B)` with no relative cells above dimension
`finrank ℂ E + q` such that for every finite-dimensional module `V` over a division ring `k` and
every `m ≥ finrank ℂ E + q`, `∑ᵢ₌₀ᵐ cᵢ dim V · tⁱ = ∑ᵢ₌₀ᵐ bᵢ tⁱ + (1 + t) Q(t)`, where the
coefficient of `tⁱ` in `Q` is the rank of the relative cellular differential from degree `i + 1` to
degree `i`. -/
theorem
    IsMorse.exists_relCWComplex_sum_range_monomial_sublevelPair_of_isManifoldStronglyPseudoconvexAt
    {f : M → ℝ} {q : ℕ} (hf : IsMorse 𝓘(ℝ, E) f) {a b : ℝ} (hab : a ≤ b)
    (hcompact : IsCompact (f ⁻¹' Icc a b)) (ha : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f a)
    (hb : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f b)
    (hq : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Ioc a b,
      IsManifoldStronglyPseudoconvexAt E q f x) :
    ∃ (W : Type u) (_ : TopologicalSpace W) (_ : T2Space W) (B : Set W)
      (_ : RelCWComplex (univ : Set W) B),
      RelCWComplex.Finite (univ : Set W) ∧
      (∀ m, Nonempty (cell (univ : Set W) m ≃
        ↥{x ∈ criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Ioc a b | manifoldMorseIndex 𝓘(ℝ, E) f x = m})) ∧
      (∀ m, finrank ℂ E + q < m → IsEmpty (cell (univ : Set W) m)) ∧
      ∀ {k : Type u} [DivisionRing k] (V : ModuleCat.{u} k) [Module.Finite k V] {m : ℕ},
        finrank ℂ E + q ≤ m →
        ∑ i ∈ Finset.range (m + 1), monomial i
            ({x ∈ criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Ioc a b |
              manifoldMorseIndex 𝓘(ℝ, E) f x = i}.ncard * finrank k V) =
          ∑ i ∈ Finset.range (m + 1),
            monomial i (finrank k ((sublevelPair f hab).singularHomology V i : ModuleCat k)) +
            (1 + X) * ∑ i ∈ Finset.range m, monomial i (finrank k
              (LinearMap.range ((cellularChainComplex (univ : Set W) V).d (i + 1) i).hom)) := by
  obtain ⟨W, _, _, j, _, -, hfin, c, hH⟩ :=
    hf.exists_relCWComplex_singularHomology_iso_sublevelPair.{u, u + 1, u} hab hcompact ha hb
  have hempty (m : ℕ) (hm : finrank ℂ E + q < m) : IsEmpty (cell (univ : Set W) m) :=
    (c m).some.isEmpty_congr.2 ⟨fun ⟨x, hx, hxm⟩ ↦ by
      have := (hq x hx).manifoldMorseIndex_le_of_mem_criticalPoints (hf.contMDiff x) hx.1
      lia⟩
  refine ⟨W, _, ‹_›, range j, ‹_›, hfin, c, hempty, fun V _ m hm ↦ ?_⟩
  have hcell (i : ℕ) : Finite (cell (univ : Set W) i) := FiniteType.finite_cell i
  have h := sum_range_monomial_natCard_cell_mul_finrank_eq (univ : Set W) V (fun i _ ↦ hcell i)
    (hempty (m + 1) (by lia))
  simp only [Nat.card_congr (c _).some, Nat.card_coe_set_eq] at h
  rw [h]
  congr 1
  exact Finset.sum_congr rfl fun i _ ↦ by rw [(hH V i).some.toLinearEquiv.finrank_eq]

/-- **Truncated Euler equality on a strongly `q`-pseudoconvex band.** On a compact regular band
`f⁻¹[a, b]` of a real Morse function `f` that is strongly `q`-pseudoconvex at its critical points
in `(a, b]`, the alternating sum of relative Betti numbers equals `dim V` times the alternating sum
of critical counts already from degree `finrank ℂ E + q` onwards. -/
theorem
    IsMorse.sum_range_finrank_singularHomology_sublevelPair_of_isManifoldStronglyPseudoconvexAt
    {f : M → ℝ} {q : ℕ} (hf : IsMorse 𝓘(ℝ, E) f) {a b : ℝ} (hab : a ≤ b)
    (hcompact : IsCompact (f ⁻¹' Icc a b)) (ha : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f a)
    (hb : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f b)
    (hq : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Ioc a b,
      IsManifoldStronglyPseudoconvexAt E q f x)
    {k : Type u} [DivisionRing k] (V : ModuleCat.{u} k) [Module.Finite k V] {m : ℕ}
    (hm : finrank ℂ E + q ≤ m) :
    ∑ i ∈ Finset.range (m + 1), (-1 : ℤ) ^ i *
        finrank k ((sublevelPair f hab).singularHomology V i : ModuleCat k) =
      finrank k V * ∑ i ∈ Finset.range (m + 1), (-1 : ℤ) ^ i *
        {x ∈ criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Ioc a b |
          manifoldMorseIndex 𝓘(ℝ, E) f x = i}.ncard := by
  obtain ⟨W, _, _, j, _, -, hfin, c, hH⟩ :=
    hf.exists_relCWComplex_singularHomology_iso_sublevelPair.{u, u + 1, u} hab hcompact ha hb
  have hcell (i : ℕ) : Finite (cell (univ : Set W) i) := FiniteType.finite_cell i
  have hempty : IsEmpty (cell (univ : Set W) (m + 1)) :=
    (c (m + 1)).some.isEmpty_congr.2 ⟨fun ⟨x, hx, hxm⟩ ↦ by
      have := (hq x hx).manifoldMorseIndex_le_of_mem_criticalPoints (hf.contMDiff x) hx.1
      lia⟩
  have h := sum_range_finrank_singularHomology_complexBasePair (univ : Set W) V
    (fun i _ ↦ hcell i) hempty
  simp only [Nat.card_congr (c _).some, Nat.card_coe_set_eq,
    (hH V _).some.toLinearEquiv.finrank_eq] at h
  exact h

end Band

/-! ### Proper strongly `q`-pseudoconvex and strictly plurisubharmonic exhaustions -/

section PseudoconvexExhaustion

section StronglyPseudoconvex

variable {E : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M] [T2Space M]

local instance : FiniteDimensional ℝ E := Module.Finite.trans ℂ E

local instance : IsManifold 𝓘(ℝ, E) ∞ M :=
  IsManifold.restrictScalars ℝ (inferInstance : IsManifold 𝓘(ℂ, E) ∞ M)

/-- **Sublevel-filtered CW model of a strongly `q`-pseudoconvex Morse exhaustion.** Let `f` be a
proper bounded-below real Morse function on a complex manifold `M` of complex dimension `n`,
strongly `q`-pseudoconvex at every critical point. Then `M` is homotopy equivalent via `h : X ≃ₕ M`
to a finite-dimensional Hausdorff CW complex `X` exhausted by finite subcomplexes `W k` modelling a
regular sublevel exhaustion `{f ≤ a k}`, with `m`-cells corresponding to the critical points of
index `m` (globally and on each sublevel) and no cells in dimensions strictly above `n + q`. -/
theorem IsMorse.exists_cwComplex_subcomplex_homotopyEquiv_of_isManifoldStronglyPseudoconvexAt
    {f : M → ℝ} {q : ℕ} (hf : IsMorse 𝓘(ℝ, E) f) (hp : IsProperMap f) (hbdd : BddBelow (range f))
    (hq : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f, IsManifoldStronglyPseudoconvexAt E q f x) :
    ∃ (a : ℕ → ℝ) (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X)
      (_ : CWComplex (univ : Set X)) (h : X ≃ₕ M) (W : ℕ → Subcomplex (univ : Set X))
      (hW : ∀ k, (W k : Set X) ≃ₕ {x | f x ≤ a k}),
      CWComplex.FiniteDimensional (univ : Set X) ∧ StrictMono a ∧ Tendsto a Filter.atTop
        Filter.atTop ∧ (∀ k, IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f (a k)) ∧ (∀ x, a 0 < f x) ∧
      Monotone W ∧ (W 0 : Set X) = ∅ ∧ (⋃ k, (W k : Set X) = univ) ∧
      (∀ k, RelCWComplex.Finite (W k : Set X)) ∧ (∀ k (w : W k), (hW k w : M) = h w) ∧
      (∀ k, MapsTo h.symm {x | f x ≤ a k} (W k : Set X)) ∧
      (∀ m, Nonempty (cell (univ : Set X) m ≃
        ↥{x ∈ criticalPoints 𝓘(ℝ, E) f | manifoldMorseIndex 𝓘(ℝ, E) f x = m})) ∧
      (∀ k m, Nonempty (cell (W k : Set X) m ≃
        ↥{x ∈ criticalPoints 𝓘(ℝ, E) f ∩ {y | f y ≤ a k} |
          manifoldMorseIndex 𝓘(ℝ, E) f x = m})) ∧
      ∀ m, finrank ℂ E + q < m → IsEmpty (cell (univ : Set X) m) := by
  obtain ⟨a, X, _, _, _, h, W, hW, hmono, htop, hreg, ha0, hWmono, hW0, hWuniv, hWfin, hhW, hmaps,
    hcell, hWcell⟩ := hf.exists_cwComplex_subcomplex_homotopyEquiv hp hbdd
  have hempty (m : ℕ) (hm : finrank ℂ E + q < m) : IsEmpty (cell (univ : Set X) m) :=
    (hcell m).some.isEmpty_congr.2 ⟨fun ⟨x, hx, hxm⟩ ↦ hm.not_ge
      (hxm ▸ (hq x hx).manifoldMorseIndex_le_of_mem_criticalPoints (hf.contMDiff x) hx)⟩
  exact ⟨a, X, _, ‹_›, ‹_›, h, W, hW, CWComplex.finiteDimensional_of_isEmpty_cell_gt _ hempty,
    hmono, htop, hreg, ha0, hWmono, hW0, hWuniv, hWfin, hhW, hmaps, hcell, hWcell, hempty⟩

/-- **CW model of a strongly `q`-pseudoconvex Morse exhaustion.** A complex manifold `M` of complex
dimension `n` carrying a proper bounded-below real Morse function `f` that is strongly
`q`-pseudoconvex at every critical point is homotopy equivalent to a finite-dimensional Hausdorff
CW complex whose `m`-cells correspond to the critical points of index `m` and which has no cells in
dimensions strictly above `n + q`. -/
theorem IsMorse.exists_cwComplex_homotopyEquiv_of_isManifoldStronglyPseudoconvexAt
    {f : M → ℝ} {q : ℕ} (hf : IsMorse 𝓘(ℝ, E) f) (hp : IsProperMap f) (hbdd : BddBelow (range f))
    (hq : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f, IsManifoldStronglyPseudoconvexAt E q f x) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      CWComplex.FiniteDimensional (univ : Set X) ∧ Nonempty (M ≃ₕ X) ∧
      (∀ m, Nonempty (cell (univ : Set X) m ≃
        ↥{x ∈ criticalPoints 𝓘(ℝ, E) f | manifoldMorseIndex 𝓘(ℝ, E) f x = m})) ∧
      ∀ m, finrank ℂ E + q < m → IsEmpty (cell (univ : Set X) m) :=
  hf.exists_cwComplex_homotopyEquiv_of_manifoldMorseIndex_le hp hbdd fun x hx ↦
    (hq x hx).manifoldMorseIndex_le_of_mem_criticalPoints (hf.contMDiff x) hx

/-- **Andreotti–Frankel CW homotopy theorem for smooth strongly `q`-pseudoconvex exhaustions.** If a
Hausdorff complex manifold `M` of complex dimension `n` carries a smooth proper bounded-below
everywhere strongly `q`-pseudoconvex function `f : M → ℝ` (not assumed to be Morse), then `M` is
homotopy equivalent to a finite-dimensional Hausdorff CW complex `X` with no cells in dimensions
strictly above `n + q`. -/
theorem exists_cwComplex_homotopyEquiv_of_isProperMap_of_isManifoldStronglyPseudoconvexAt
    {f : M → ℝ} {q : ℕ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f) (hp : IsProperMap f)
    (hbdd : BddBelow (range f)) (hq : ∀ x, IsManifoldStronglyPseudoconvexAt E q f x) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      CWComplex.FiniteDimensional (univ : Set X) ∧ Nonempty (M ≃ₕ X) ∧
      ∀ m, finrank ℂ E + q < m → IsEmpty (cell (univ : Set X) m) := by
  let F : C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯ := ⟨f, hf⟩
  obtain ⟨g, hgm, hgp, hgbdd, -, -, -, hgidx⟩ :=
    F.exists_isMorse_isProperMap_bddBelow_isManifoldStronglyPseudoconvexAt q hq hp hbdd
      isClosed_empty isOpen_empty (subset_refl _) isMorseOn_empty
  obtain ⟨X, _, _, _, hfd, hM, -, hempty⟩ :=
    hgm.exists_cwComplex_homotopyEquiv_of_manifoldMorseIndex_le hgp hgbdd hgidx
  exact ⟨X, _, ‹_›, ‹_›, hfd, hM, hempty⟩

end StronglyPseudoconvex

/-- **CW homotopy theorem for smooth strictly plurisubharmonic exhaustions.** If a Hausdorff complex
manifold `M` modelled on a complex normed space `E` carries a smooth proper bounded-below everywhere
strictly plurisubharmonic function `f : M → ℝ` (not assumed to be Morse), then `M` is homotopy
equivalent to a finite-dimensional Hausdorff CW complex `X` with no cells in dimensions strictly
above `finrank ℂ E`. No finite-dimensionality assumption on `E` is needed: when `M` is nonempty it
follows from `IsProperMap f` by Riesz's theorem. -/
theorem exists_cwComplex_homotopyEquiv_of_isProperMap_of_isManifoldStrictlyPlurisubharmonicAt
    {E : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M] [T2Space M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f) (hp : IsProperMap f) (hbdd : BddBelow (range f))
    (hpsh : ∀ x, IsManifoldStrictlyPlurisubharmonicAt E f x) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      CWComplex.FiniteDimensional (univ : Set X) ∧ Nonempty (M ≃ₕ X) ∧
      ∀ m, finrank ℂ E < m → IsEmpty (cell (univ : Set X) m) := by
  rcases isEmpty_or_nonempty M with hM | _
  · exact exists_cwComplex_homotopyEquiv_of_isEmpty M (finrank ℂ E)
  have : FiniteDimensional ℂ E := finiteDimensional_of_isProperMap hp
  simpa only [Nat.add_zero] using
    exists_cwComplex_homotopyEquiv_of_isProperMap_of_isManifoldStronglyPseudoconvexAt (q := 0)
      hf hp hbdd fun x ↦ (hpsh x).isManifoldStronglyPseudoconvexAt 0

end PseudoconvexExhaustion

/-! ### Holomorphic immersions, closed holomorphic embeddings, and affine complete intersections -/

section HolomorphicImmersion

/-- **Sublevel-filtered CW model of Morse squared distance along a proper holomorphic immersion.**
Let `i : M → F` be a `C²` proper holomorphic immersion of a Hausdorff smooth complex manifold `M`
modelled on `E` into a proper complex inner product space `F`, and suppose `x ↦ ‖i x - a‖²` is a
real Morse function on `M` (no finite-dimensionality assumption on `E` is needed). Then `M` is
homotopy equivalent to a finite-dimensional Hausdorff CW complex `X` exhausted by finite
subcomplexes modelling closed-ball sublevels `{x | ‖i x - a‖² ≤ r k}`, with `m`-cells corresponding
to the critical points of index `m` and no cells in dimensions strictly above `finrank ℂ E`. -/
theorem IsMorse.exists_cwComplex_subcomplex_homotopyEquiv_norm_sq_sub_comp
    {E F : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [ProperSpace F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M] [T2Space M]
    {i : M → F} {a : F} (hi : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) 2 i)
    (hinj : ∀ x, Function.Injective (mvfderiv 𝓘(ℂ, E) i x)) (hip : IsProperMap i)
    (hf : IsMorse 𝓘(ℝ, E) fun x ↦ ‖i x - a‖ ^ 2) :
    ∃ (r : ℕ → ℝ) (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X)
      (_ : CWComplex (univ : Set X)) (h : X ≃ₕ M) (W : ℕ → Subcomplex (univ : Set X))
      (hW : ∀ k, (W k : Set X) ≃ₕ {x | ‖i x - a‖ ^ 2 ≤ r k}),
      CWComplex.FiniteDimensional (univ : Set X) ∧ StrictMono r ∧ Tendsto r Filter.atTop
        Filter.atTop ∧ (∀ k, IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) (fun x ↦ ‖i x - a‖ ^ 2) (r k)) ∧
      (∀ x, r 0 < ‖i x - a‖ ^ 2) ∧ Monotone W ∧ (W 0 : Set X) = ∅ ∧
      (⋃ k, (W k : Set X) = univ) ∧ (∀ k, RelCWComplex.Finite (W k : Set X)) ∧
      (∀ k (w : W k), (hW k w : M) = h w) ∧
      (∀ k, MapsTo h.symm {x | ‖i x - a‖ ^ 2 ≤ r k} (W k : Set X)) ∧
      (∀ m, Nonempty (cell (univ : Set X) m ≃
        ↥{x ∈ criticalPoints 𝓘(ℝ, E) (fun y ↦ ‖i y - a‖ ^ 2) |
          manifoldMorseIndex 𝓘(ℝ, E) (fun y ↦ ‖i y - a‖ ^ 2) x = m})) ∧
      (∀ k m, Nonempty (cell (W k : Set X) m ≃
        ↥{x ∈ criticalPoints 𝓘(ℝ, E) (fun y ↦ ‖i y - a‖ ^ 2) ∩ {y | ‖i y - a‖ ^ 2 ≤ r k} |
          manifoldMorseIndex 𝓘(ℝ, E) (fun y ↦ ‖i y - a‖ ^ 2) x = m})) ∧
      ∀ m, finrank ℂ E < m → IsEmpty (cell (univ : Set X) m) := by
  have : IsManifold 𝓘(ℝ, E) ∞ M :=
    IsManifold.restrictScalars ℝ (inferInstance : IsManifold 𝓘(ℂ, E) ∞ M)
  have : IsManifold 𝓘(ℂ, E) 2 M := .of_le (n := ∞) (by norm_cast)
  obtain ⟨r, X, _, _, _, h, W, hW, hmono, htop, hreg, hr0, hWmono, hW0, hWuniv, hWfin, hhW, hmaps,
    hcell, hWcell⟩ := hf.exists_cwComplex_subcomplex_homotopyEquiv
      ((isProperMap_norm_sq_sub_comp_iff hi.continuous a).2 hip)
      ⟨0, by rintro _ ⟨_, rfl⟩; positivity⟩
  have hempty (m : ℕ) (hm : finrank ℂ E < m) : IsEmpty (cell (univ : Set X) m) :=
    (hcell m).some.isEmpty_congr.2 ⟨fun ⟨x, hx, hxm⟩ ↦ hm.not_ge
      (hxm ▸ manifoldMorseIndex_norm_sq_sub_comp_le (hi x) (hinj x) (mem_criticalPoints.1 hx))⟩
  exact ⟨r, X, _, ‹_›, ‹_›, h, W, hW, CWComplex.finiteDimensional_of_isEmpty_cell_gt _ hempty,
    hmono, htop, hreg, hr0, hWmono, hW0, hWuniv, hWfin, hhW, hmaps, hcell, hWcell, hempty⟩

/-- **CW model of Morse squared distance along a proper holomorphic immersion.** Under the
hypotheses of `TauCeti.IsMorse.exists_cwComplex_subcomplex_homotopyEquiv_norm_sq_sub_comp`, `M` is
homotopy equivalent to a finite-dimensional Hausdorff CW complex whose `m`-cells correspond to the
critical points of `x ↦ ‖i x - a‖²` of index `m` and which has no cells in dimensions strictly above
`finrank ℂ E`. -/
theorem IsMorse.exists_cwComplex_homotopyEquiv_norm_sq_sub_comp
    {E F : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [ProperSpace F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M] [T2Space M]
    {i : M → F} {a : F} (hi : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) 2 i)
    (hinj : ∀ x, Function.Injective (mvfderiv 𝓘(ℂ, E) i x)) (hip : IsProperMap i)
    (hf : IsMorse 𝓘(ℝ, E) fun x ↦ ‖i x - a‖ ^ 2) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      CWComplex.FiniteDimensional (univ : Set X) ∧ Nonempty (M ≃ₕ X) ∧
      (∀ m, Nonempty (cell (univ : Set X) m ≃
        ↥{x ∈ criticalPoints 𝓘(ℝ, E) (fun y ↦ ‖i y - a‖ ^ 2) |
          manifoldMorseIndex 𝓘(ℝ, E) (fun y ↦ ‖i y - a‖ ^ 2) x = m})) ∧
      ∀ m, finrank ℂ E < m → IsEmpty (cell (univ : Set X) m) := by
  have : IsManifold 𝓘(ℝ, E) ∞ M :=
    IsManifold.restrictScalars ℝ (inferInstance : IsManifold 𝓘(ℂ, E) ∞ M)
  have : IsManifold 𝓘(ℂ, E) 2 M := .of_le (n := ∞) (by norm_cast)
  exact hf.exists_cwComplex_homotopyEquiv_of_manifoldMorseIndex_le
    ((isProperMap_norm_sq_sub_comp_iff hi.continuous a).2 hip)
    ⟨0, by rintro _ ⟨_, rfl⟩; positivity⟩
    fun x hx ↦ manifoldMorseIndex_norm_sq_sub_comp_le (hi x) (hinj x) (mem_criticalPoints.1 hx)

/-- **Andreotti–Frankel CW homotopy theorem for proper holomorphic immersions.** If a Hausdorff
smooth complex manifold `M` modelled on `E` admits a `C^r` (`r ≥ ∞`, in particular smooth or
analytic) proper holomorphic immersion into a finite-dimensional complex normed space `F` (no inner
product on `F`, second-countability on `M`, or finite-dimensionality assumption on `E` is needed),
then `M` is homotopy equivalent to a finite-dimensional Hausdorff CW complex `X` with no cells in
dimensions strictly above `finrank ℂ E`. -/
theorem exists_cwComplex_homotopyEquiv_of_isProperMap_holomorphic_immersion
    {E F : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M] [T2Space M]
    {r : ℕ∞ω} {i : M → F} (hi : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) r i)
    (hinj : ∀ x, Function.Injective (mvfderiv 𝓘(ℂ, E) i x)) (hip : IsProperMap i)
    (hr : ∞ ≤ r := by simp) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      CWComplex.FiniteDimensional (univ : Set X) ∧ Nonempty (M ≃ₕ X) ∧
      ∀ m, finrank ℂ E < m → IsEmpty (cell (univ : Set X) m) := by
  rcases isEmpty_or_nonempty M with hM | ⟨⟨x₀⟩⟩
  · exact exists_cwComplex_homotopyEquiv_of_isEmpty M (finrank ℂ E)
  -- Transport `F` to standard complex Euclidean space via a continuous linear equivalence.
  let L : F ≃L[ℂ] EuclideanSpace ℂ (Fin (finrank ℂ F)) :=
    (Module.finBasis ℂ F).equivFun.toContinuousLinearEquiv.trans
      (EuclideanSpace.equiv (Fin (finrank ℂ F)) ℂ).symm
  have hi' : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ∞ i := hi.of_le hr
  have : FiniteDimensional ℂ E :=
    Module.Finite.of_injective (mvfderiv 𝓘(ℂ, E) i x₀).toLinearMap (hinj x₀)
  have : FiniteDimensional ℝ E := Module.Finite.trans ℂ E
  have : IsManifold 𝓘(ℝ, E) ∞ M :=
    IsManifold.restrictScalars ℝ (inferInstance : IsManifold 𝓘(ℂ, E) ∞ M)
  have hLi : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, EuclideanSpace ℂ (Fin (finrank ℂ F))) ∞ (L ∘ i) :=
    L.contDiff.contMDiff.comp hi'
  have hLinj (x : M) : Function.Injective (mvfderiv 𝓘(ℂ, E) (L ∘ i) x) := fun v w hvw ↦ by
    have hL := L.toContinuousLinearMap.mvfderiv_comp_apply ((hi' x).mdifferentiableAt (by simp))
    exact hinj x (L.injective ((hL v).symm.trans (hvw.trans (hL w))))
  obtain ⟨a, ha, hap, hbdd, hidx⟩ :=
    exists_isMorse_isProperMap_bddBelow_and_manifoldMorseIndex_norm_sq_sub_comp_le hLi hLinj
      (L.toHomeomorph.isProperMap.comp hip)
  obtain ⟨X, _, _, _, hfd, hM, -, hempty⟩ :=
    ha.exists_cwComplex_homotopyEquiv_of_manifoldMorseIndex_le hap hbdd hidx
  exact ⟨X, _, ‹_›, ‹_›, hfd, hM, hempty⟩

/-- **Andreotti–Frankel CW homotopy theorem for closed holomorphic embeddings** (Milnor, *Morse
Theory*, Theorem 7.1). Let `i : M → F` be a `C^r` (`r ≥ ∞`, in particular smooth or analytic)
holomorphic immersion of a complex manifold `M` modelled on `E` into a finite-dimensional complex
normed space `F`, which is a closed topological embedding. Then `M` is homotopy equivalent to a
finite-dimensional Hausdorff CW complex `X` with no cells in dimensions strictly above
`finrank ℂ E`. Neither `[T2Space M]`, `[SecondCountableTopology M]`, `[FiniteDimensional ℂ E]`, nor
an inner product on `F` need be assumed. -/
theorem exists_cwComplex_homotopyEquiv_of_isClosedEmbedding
    {E F : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]
    {r : ℕ∞ω} {i : M → F} (hi : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) r i)
    (hinj : ∀ x, Function.Injective (mvfderiv 𝓘(ℂ, E) i x)) (hclosed : IsClosedEmbedding i)
    (hr : ∞ ≤ r := by simp) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      CWComplex.FiniteDimensional (univ : Set X) ∧ Nonempty (M ≃ₕ X) ∧
      ∀ m, finrank ℂ E < m → IsEmpty (cell (univ : Set X) m) := by
  have : T2Space M := hclosed.isEmbedding.t2Space
  have : FiniteDimensional ℝ F := Module.Finite.trans ℂ F
  exact exists_cwComplex_homotopyEquiv_of_isProperMap_holomorphic_immersion hi hinj
    hclosed.isProperMap hr

end HolomorphicImmersion

end TauCeti

/-! ### Dot-notation API on `Manifold.IsImmersion` -/

namespace Manifold.IsImmersion

/-- **Andreotti–Frankel CW homotopy theorem for proper `Manifold.IsImmersion` maps.** If
`hi : Manifold.IsImmersion 𝓘(ℂ, E) 𝓘(ℂ, F) r i` (`r ≥ ∞`) is a proper holomorphic immersion of a
Hausdorff smooth complex manifold `M` into a finite-dimensional complex normed space `F`, then `M`
is homotopy equivalent to a finite-dimensional Hausdorff CW complex with no cells in dimensions
strictly above `finrank ℂ E`. -/
theorem exists_cwComplex_homotopyEquiv_of_isProperMap
    {E F : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M] [T2Space M]
    {r : ℕ∞ω} {i : M → F} (hi : Manifold.IsImmersion 𝓘(ℂ, E) 𝓘(ℂ, F) r i) (hip : IsProperMap i)
    (hr : ∞ ≤ r := by simp) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      CWComplex.FiniteDimensional (univ : Set X) ∧ Nonempty (M ≃ₕ X) ∧
      ∀ m, finrank ℂ E < m → IsEmpty (cell (univ : Set X) m) :=
  TauCeti.exists_cwComplex_homotopyEquiv_of_isProperMap_holomorphic_immersion hi.contMDiff
    (fun x ↦ TauCeti.injective_mvfderiv_iff.2
      (hi.mfderiv_injective (ne_of_gt (lt_of_lt_of_le (by simp : (0 : ℕ∞ω) < ∞) hr)) x))
    hip hr

/-- **Andreotti–Frankel CW homotopy theorem for closed holomorphic embeddings via
`Manifold.IsImmersion`.** If `hi : Manifold.IsImmersion 𝓘(ℂ, E) 𝓘(ℂ, F) r i` (`r ≥ ∞`) is a closed
topological embedding of a smooth complex manifold `M` into a finite-dimensional complex normed
space `F`, then `M` is homotopy equivalent to a finite-dimensional Hausdorff CW complex with no
cells in dimensions strictly above `finrank ℂ E`. -/
theorem exists_cwComplex_homotopyEquiv_of_isClosedEmbedding
    {E F : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]
    {r : ℕ∞ω} {i : M → F} (hi : Manifold.IsImmersion 𝓘(ℂ, E) 𝓘(ℂ, F) r i)
    (hclosed : IsClosedEmbedding i) (hr : ∞ ≤ r := by simp) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      CWComplex.FiniteDimensional (univ : Set X) ∧ Nonempty (M ≃ₕ X) ∧
      ∀ m, finrank ℂ E < m → IsEmpty (cell (univ : Set X) m) :=
  TauCeti.exists_cwComplex_homotopyEquiv_of_isClosedEmbedding hi.contMDiff
    (fun x ↦ TauCeti.injective_mvfderiv_iff.2
      (hi.mfderiv_injective (ne_of_gt (lt_of_lt_of_le (by simp : (0 : ℕ∞ω) < ∞) hr)) x))
    hclosed hr

end Manifold.IsImmersion

namespace TauCeti

/-! ### Smooth affine complete intersections -/

section AffineZeroLocus

/-- **CW model of Morse squared distance on a smooth affine complete intersection.** Let
`affineZeroLocus p ⊆ ℂ^σ` be the common zero set of a polynomial family `p : ι → ℂ[X_σ]` with
surjective Jacobian at every common zero, and suppose the Euclidean squared distance from `a` is a
Morse function on `affineZeroLocus p`. Then `affineZeroLocus p` is homotopy equivalent to a
finite-dimensional Hausdorff CW complex whose `m`-cells correspond to the critical points of index
`m` of the squared distance and which has no cells in dimensions strictly above `|σ| - |ι|`. -/
theorem IsMorse.exists_cwComplex_homotopyEquiv_norm_sq_sub_toLp_affineZeroLocus
    {σ : Type u} {ι : Type*} [Fintype σ] [Fintype ι] {p : ι → MvPolynomial σ ℂ}
    (hp : ∀ x ∈ affineZeroLocus p, Function.Surjective (jacobiMatrixAt p x).mulVec)
    (a : EuclideanSpace ℂ σ)
    (hf : letI := affineZeroLocusChartedSpace hp
      IsMorse 𝓘(ℝ, Fin (Fintype.card σ - Fintype.card ι) → ℂ)
        fun y : affineZeroLocus p ↦ ‖WithLp.toLp 2 (y : σ → ℂ) - a‖ ^ 2) :
    letI := affineZeroLocusChartedSpace hp
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      CWComplex.FiniteDimensional (univ : Set X) ∧ Nonempty (affineZeroLocus p ≃ₕ X) ∧
      (∀ m, Nonempty (cell (univ : Set X) m ≃
        ↥{x ∈ criticalPoints 𝓘(ℝ, Fin (Fintype.card σ - Fintype.card ι) → ℂ)
            (fun y : affineZeroLocus p ↦ ‖WithLp.toLp 2 (y : σ → ℂ) - a‖ ^ 2) |
          manifoldMorseIndex 𝓘(ℝ, Fin (Fintype.card σ - Fintype.card ι) → ℂ)
            (fun y : affineZeroLocus p ↦ ‖WithLp.toLp 2 (y : σ → ℂ) - a‖ ^ 2) x = m})) ∧
      ∀ m, Fintype.card σ - Fintype.card ι < m → IsEmpty (cell (univ : Set X) m) := by
  let _ := affineZeroLocusChartedSpace hp
  have := isManifold_affineZeroLocus hp ∞
  have hclosed : IsClosedEmbedding (fun y : affineZeroLocus p ↦ WithLp.toLp 2 (y : σ → ℂ)) :=
    (EuclideanSpace.equiv σ ℂ).symm.toHomeomorph.isClosedEmbedding.comp
      (isClosed_affineZeroLocus p).isClosedEmbedding_subtypeVal
  simpa only [Module.finrank_fin_fun] using
    hf.exists_cwComplex_homotopyEquiv_norm_sq_sub_comp (contMDiff_toLp_coe_affineZeroLocus hp 2)
      (injective_mvfderiv_toLp_coe_affineZeroLocus hp) hclosed.isProperMap

/-- **Andreotti–Frankel CW homotopy theorem for smooth affine complete intersections** (Milnor,
*Morse Theory*, Theorem 7.2). Let `affineZeroLocus p ⊆ ℂ^σ` be the common zero set of a polynomial
family `p : ι → ℂ[X_σ]` whose Jacobian matrix is surjective at every common zero. Then
`affineZeroLocus p` is homotopy equivalent to a finite-dimensional Hausdorff CW complex `X` with no
cells in dimensions strictly above its complex dimension `|σ| - |ι|`. -/
theorem exists_cwComplex_homotopyEquiv_affineZeroLocus
    {σ : Type u} {ι : Type*} [Fintype σ] [Fintype ι] {p : ι → MvPolynomial σ ℂ}
    (hp : ∀ x ∈ affineZeroLocus p, Function.Surjective (jacobiMatrixAt p x).mulVec) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      CWComplex.FiniteDimensional (univ : Set X) ∧ Nonempty (affineZeroLocus p ≃ₕ X) ∧
      ∀ m, Fintype.card σ - Fintype.card ι < m → IsEmpty (cell (univ : Set X) m) := by
  let _ := affineZeroLocusChartedSpace hp
  have := isManifold_affineZeroLocus hp ∞
  simpa only [Module.finrank_fin_fun] using
    exists_cwComplex_homotopyEquiv_of_isClosedEmbedding (contMDiff_coe_affineZeroLocus hp ∞)
      (fun x ↦ injective_mvfderiv_iff.2 (injective_mfderiv_coe_affineZeroLocus hp x))
      (isClosed_affineZeroLocus p).isClosedEmbedding_subtypeVal

end AffineZeroLocus

/-! ### Checks -/

section Checks

/-- **Check: coordinate form of Andreotti–Frankel for closed holomorphic embeddings into `ℂᴺ`.** A
complex `n`-manifold charted on `Fin n → ℂ` with an analytic (`ω`) closed holomorphic immersion into
`Fin N → ℂ` is homotopy equivalent to a finite-dimensional Hausdorff CW complex with no cells above
dimension `n`, without assuming Hausdorffness or second-countability on `M`. -/
example {n N : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (Fin n → ℂ) M]
    [IsManifold 𝓘(ℂ, Fin n → ℂ) ω M] {f : M → Fin N → ℂ}
    (hf_imm : Manifold.IsImmersion 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin N → ℂ) ω f)
    (hf_closed : IsClosedEmbedding f) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      CWComplex.FiniteDimensional (univ : Set X) ∧ Nonempty (M ≃ₕ X) ∧
      ∀ m, n < m → IsEmpty (cell (univ : Set X) m) := by
  simpa only [Module.finrank_fin_fun] using
    hf_imm.exists_cwComplex_homotopyEquiv_of_isClosedEmbedding hf_closed

/-- **Check: top-degree freeness and cohomology vanishing directly from the CW model.** Feeding
`Manifold.IsImmersion.exists_cwComplex_homotopyEquiv_of_isClosedEmbedding` into the cellular
dimension API of `TauCeti.AlgebraicTopology.Cellular.Dimension` immediately recovers freeness of
`Hₙ(M; V)` over any PID and vanishing of `Hᵏ(M; R, N)` for `k > n` over any hereditary commutative
ring (in any universe). -/
example {E F : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]
    {i : M → F} (hi : Manifold.IsImmersion 𝓘(ℂ, E) 𝓘(ℂ, F) ∞ i) (hclosed : IsClosedEmbedding i) :
    Module.Free ℤ (((singularHomologyFunctor (ModuleCat.{u} ℤ) (finrank ℂ E)).obj
        (ModuleCat.of ℤ (ULift.{u} ℤ))).obj (TopCat.of M)) ∧
      ∀ {k : ℕ}, finrank ℂ E < k →
        IsZero ((TopCat.of M).singularCohomology (ModuleCat.of ℤ (ULift.{u} ℤ)) ℤ
          (ModuleCat.of ℤ (ULift.{u} ℤ)) k) := by
  obtain ⟨X, _, _, _, -, ⟨e⟩, hempty⟩ :=
    hi.exists_cwComplex_homotopyEquiv_of_isClosedEmbedding hclosed
  let e' : M ≃ₕ (univ : Set X) := e.trans (Homeomorph.Set.univ X).symm.toHomotopyEquiv
  have : IsEmpty (cell (univ : Set X) (finrank ℂ E + 1)) := hempty _ (Nat.lt_succ_self _)
  exact ⟨e'.free_singularHomology_of_isEmpty_cell_succ _ (finrank ℂ E),
    fun hk ↦ e'.isZero_singularCohomology_of_isEmpty_cell_gt _ _ hempty hk⟩

/-- **Check: the smooth affine hyperbola `{z ∈ ℂ² | z₀ z₁ - 1 = 0}`.** Its single defining equation
has nonvanishing partial derivative `∂(z₀ z₁ - 1)/∂z₀ = z₁` at every zero, so
`TauCeti.exists_cwComplex_homotopyEquiv_affineZeroLocus` gives a Hausdorff CW homotopy model of
dimension at most `1`. -/
example :
    let p : Unit → MvPolynomial (Fin 2) ℂ := fun _ ↦ MvPolynomial.X 0 * MvPolynomial.X 1 - 1
    ∃ (X : Type) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      CWComplex.FiniteDimensional (univ : Set X) ∧ Nonempty (affineZeroLocus p ≃ₕ X) ∧
      ∀ m, 1 < m → IsEmpty (cell (univ : Set X) m) := by
  intro p
  have hp : ∀ x ∈ affineZeroLocus p, Function.Surjective (jacobiMatrixAt p x).mulVec := by
    intro x hx
    rw [mulVec_surjective_jacobiMatrixAt_iff_exists_eval_pderiv_ne_zero]
    refine ⟨0, fun hv1 ↦ ?_⟩
    have h0 : x 0 * x 1 - 1 = 0 := by simpa [p] using (mem_affineZeroLocus.1 hx) ()
    have h1 : x 1 = 0 := by simpa [p] using hv1
    simp [h1] at h0
  simpa using exists_cwComplex_homotopyEquiv_affineZeroLocus hp

end Checks

end TauCeti
