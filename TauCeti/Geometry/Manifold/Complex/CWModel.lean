/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Immersion
public import TauCeti.Geometry.Manifold.Complex.Analytic
public import TauCeti.Geometry.Manifold.Complex.ExhaustionHomology
public import TauCeti.Geometry.Manifold.Complex.SublevelHomology
public import TauCeti.Geometry.Manifold.Morse.CWModel.Sublevel
public import TauCeti.Geometry.Manifold.Morse.Inequalities
import TauCeti.Algebra.Polynomial.AlternatingSum
import TauCeti.Geometry.Manifold.Morse.CWModel.Cobordism
import TauCeti.Geometry.Manifold.Morse.CWModel.Proper
import TauCeti.RingTheory.MvPolynomial.Jacobian.Basic
import TauCeti.Topology.Maps.Proper.Basic

/-!
# CW models of pseudoconvex complex manifolds and closed holomorphic embeddings

On a complex manifold `M` of complex dimension `n`, a real Morse function `f` which is strongly
`q`-pseudoconvex at its critical points has real Morse index at most `n + q` at each of them
(`TauCeti.IsManifoldStronglyPseudoconvexAt.manifoldMorseIndex_le_of_mem_criticalPoints`). Combining
this index bound with the Morse-theoretic CW models of regular bands, compact sublevels, and proper
Morse exhaustions (`TauCeti.Geometry.Manifold.Morse.CWModel`,
`TauCeti.Geometry.Manifold.Morse.CWModel.Sublevel`, and
`TauCeti.Geometry.Manifold.Morse.CWModel.Proper`) promotes the homology vanishing theorems of
`TauCeti.Geometry.Manifold.Complex.SublevelHomology` and
`TauCeti.Geometry.Manifold.Complex.ExhaustionHomology` to homotopy equivalences with classical CW
complexes having no cells in dimension above `n + q`:

* **Regular bands and cobordisms.** Across a compact band `f⁻¹[a, b]` between regular values of a
  Morse function strongly `q`-pseudoconvex on `(a, b]`, the sublevel `{f ≤ b}` (and the cobordism
  `f⁻¹[a, b]`) is homotopy equivalent to a finite CW complex relative to `{f ≤ a}` (respectively
  `f⁻¹(a)`) with one `m`-cell for each critical point of index `m` in `(a, b]`, and therefore no
  relative cells in dimension above `n + q`. Likewise, any (finite) CW model of `{f ≤ a}` of
  dimension at most `n + q` extends along a closed cofibration to one of `{f ≤ b}` of dimension at
  most `n + q`, and every compact regular sublevel `{f ≤ b}` has a finite CW model of dimension at
  most `n + q`.
* **Truncated band Betti vanishing, Euler equality, and Morse polynomial identity.** Across such a
  regular band, the relative Betti numbers `dim Hⱼ({f ≤ b}, {f ≤ a}; V)` and
  `dim Hⱼ(f⁻¹[a, b], f⁻¹(a); V)` vanish for `j > n + q`, so Euler's equality and the Morse
  polynomial identity already hold when truncated at any degree `m ≥ n + q` rather than
  `m ≥ 2n = dim_ℝ M`.
* **Smooth strongly `q`-pseudoconvex exhaustions and regular domains.** Via strong-Whitney Morse
  approximation preserving strong `q`-pseudoconvexity, any complex `n`-manifold carrying a smooth
  proper bounded-below everywhere strongly `q`-pseudoconvex exhaustion (not assumed Morse) is
  homotopy equivalent to a Hausdorff CW complex with no cells above dimension `n + q`
  (`TauCeti.exists_cwComplex_homotopyEquiv_of_isProperMap_of_isManifoldStronglyPseudoconvexAt`), and
  every smooth strongly `q`-pseudoconvex regular sublevel domain `{f ≤ b}` lying strictly inside a
  compact higher sublevel `{f ≤ c}` on a sigma-compact manifold has a finite CW homotopy model with
  no cells above dimension `n + q`
  (`TauCeti.exists_finite_cwComplex_homotopyEquiv_sublevel_of_isManifoldStronglyPseudoconvexAt`).
  Specializing to `q = 0` covers smooth strictly plurisubharmonic exhaustions and smoothly bounded
  strictly Levi-pseudoconvex regular domains, with CW dimension at most `n`.
* **Proper holomorphic immersions, closed holomorphic embeddings, and smooth affine complete
  intersections (Milnor's Theorem 7.2).** By Cauchy's integral formula on complex manifolds
  (`MDifferentiable.contMDiff`), every holomorphic (`MDifferentiable`) map is automatically smooth.
  Along a proper holomorphic immersion `i : M → F` into a proper complex inner product space, for
  Haar-almost every centre `a ∈ F` the squared distance `x ↦ ‖i x - a‖²` is a proper bounded-below
  Morse function giving a Hausdorff CW model of `M` with cells indexed by its critical points and
  no cells above dimension `n`
  (`TauCeti.ae_isMorse_and_exists_cwComplex_homotopyEquiv_norm_sq_sub_comp`). Transporting along a
  continuous `ℂ`-linear equivalence to `EuclideanSpace` yields the Andreotti–Frankel / Milnor CW
  bound for proper holomorphic immersions and closed holomorphic embeddings into any
  finite-dimensional complex normed space
  (`Manifold.IsImmersion.exists_cwComplex_homotopyEquiv_of_isProperMap`,
  `Manifold.IsImmersion.exists_cwComplex_homotopyEquiv_of_isClosedEmbedding`), and in particular for
  smooth affine complete intersections in `ℂ^σ`
  (`TauCeti.exists_cwComplex_homotopyEquiv_affineZeroLocus`).

## Main results

* `IsMorse.exists_relCWComplex_homotopyEquiv_sublevel_of_isManifoldStronglyPseudoconvexAt`,
  `IsMorse.exists_relCWComplex_homotopyEquiv_band_of_isManifoldStronglyPseudoconvexAt`,
  `IsMorse.exists_cwComplex_extension_homotopyEquiv_sublevel_of_isManifoldStronglyPseudoconvexAt`
  (and its finite-CW form) and
  `IsMorse.exists_finite_cwComplex_homotopyEquiv_sublevel_of_isManifoldStronglyPseudoconvexAt`:
  relative and finite CW models of regular bands and compact sublevels of strongly `q`-pseudoconvex
  Morse functions, with no cells above `finrank ℂ E + q`.
* `IsMorse.finrank_singularHomology_sublevelPair_eq_zero_of_isManifoldStronglyPseudoconvexAt`,
  `IsMorse.sum_range_neg_one_pow_mul_finrank_sublevelPair_eq_of_isManifoldStronglyPseudoconvexAt`,
  `IsMorse.exists_sum_range_monomial_sublevelPair_eq_add_mul_of_isManifoldStronglyPseudoconvexAt`:
  relative Betti vanishing above `finrank ℂ E + q` and Euler / Morse-polynomial identities truncated
  at `m ≥ finrank ℂ E + q` (together with their `bandPair` forms).
* `IsMorse.exists_cwComplex_homotopyEquiv_of_isManifoldStronglyPseudoconvexAt`,
  `TauCeti.exists_cwComplex_homotopyEquiv_of_isProperMap_of_isManifoldStronglyPseudoconvexAt`,
  `TauCeti.exists_cwComplex_homotopyEquiv_of_isProperMap_of_isManifoldStrictlyPlurisubharmonicAt`:
  Hausdorff CW models of dimension at most `n + q` (and `n` for `q = 0`) for Morse and smooth
  pseudoconvex exhaustions.
* `TauCeti.exists_finite_cwComplex_homotopyEquiv_sublevel_of_isManifoldStronglyPseudoconvexAt`,
  `TauCeti.exists_finite_cwComplex_homotopyEquiv_sublevel_of_isManifoldStrictlyPlurisubharmonicAt`
  (and the proper bounded-below exhaustion specialization): finite CW models of smooth strongly
  `q`-pseudoconvex and strictly plurisubharmonic regular sublevel domains.
* `TauCeti.ae_isMorse_and_exists_cwComplex_homotopyEquiv_norm_sq_sub_comp`,
  `TauCeti.exists_cwComplex_homotopyEquiv_norm_sq_sub_comp`,
  `TauCeti.exists_cwComplex_homotopyEquiv_of_isProperMap_holomorphic_immersion`,
  `Manifold.IsImmersion.exists_cwComplex_homotopyEquiv_of_isProperMap`,
  `TauCeti.exists_cwComplex_homotopyEquiv_of_isClosedEmbedding`,
  `Manifold.IsImmersion.exists_cwComplex_homotopyEquiv_of_isClosedEmbedding`:
  Milnor's Theorem 7.2 for proper holomorphic immersions and closed holomorphic embeddings.
* `TauCeti.exists_cwComplex_homotopyEquiv_norm_sq_sub_toLp_affineZeroLocus`,
  `TauCeti.exists_cwComplex_homotopyEquiv_affineZeroLocus`,
  `TauCeti.cwType_affineZeroLocus`:
  Hausdorff CW models of smooth affine complete intersections in `ℂ^σ` of dimension at most
  `|σ| - |ι|`.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 3.5, Section 5, and Section 7 (Theorems 7.1 and 7.2).
* A. Andreotti and T. Frankel, *The Lefschetz theorem on hyperplane sections*, Annals of Mathematics
  (2) 69 (1959), 713–717.
* R. Hain, *Notes on the Morse theory of complex manifolds*, Section 2.
-/

public section

noncomputable section

open AlgebraicTopology CategoryTheory ContMDiffMap Limits MeasureTheory Module
open Set Topology Topology.RelCWComplex
open Polynomial (monomial X)
open scoped ContDiff ContinuousMap Manifold Polynomial

universe u

namespace TauCeti

section PseudoconvexMorse

variable {E : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]

local instance : FiniteDimensional ℝ E := Module.Finite.trans ℂ E

local instance : IsManifold 𝓘(ℝ, E) ∞ M :=
  IsManifold.restrictScalars ℝ (inferInstance : IsManifold 𝓘(ℂ, E) ∞ M)

/-- A `C²` function strongly `q`-pseudoconvex on `criticalPoints 𝓘(ℝ, E) f ∩ s` has no critical
points in `s` of real Morse index larger than `finrank ℂ E + q`. -/
private theorem isEmpty_criticalPoints_inter_of_isManifoldStronglyPseudoconvexAt
    {f : M → ℝ} {s : Set M} {q k : ℕ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) 2 f)
    (hq : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f ∩ s, IsManifoldStronglyPseudoconvexAt E q f x)
    (hk : finrank ℂ E + q < k) :
    IsEmpty ↥{x ∈ criticalPoints 𝓘(ℝ, E) f ∩ s | manifoldMorseIndex 𝓘(ℝ, E) f x = k} := by
  have : IsManifold 𝓘(ℂ, E) 2 M := .of_le (n := ∞) (by norm_cast)
  refine ⟨fun x ↦ ?_⟩
  have hle := (hq x.1 x.2.1).manifoldMorseIndex_le_of_mem_criticalPoints (hf x.1) x.2.1.1
  have heq : manifoldMorseIndex 𝓘(ℝ, E) f x.1 = k := x.2.2
  omega

variable [T2Space M]

namespace IsMorse

/-- **Relative CW model across a compact regular band of a strongly `q`-pseudoconvex Morse
function.** Let `f` be a real Morse function on a complex manifold `M` of complex dimension `n`, let
`a ≤ b` be regular values with compact band `f⁻¹[a, b]`, and suppose `f` is strongly
`q`-pseudoconvex at every critical point with value in `(a, b]`. Then `{f ≤ b}` is homotopy
equivalent to a finite CW complex `X` relative to a closedly embedded copy of `{f ≤ a}`, whose
relative `m`-cells correspond to the critical points of index `m` in `(a, b]` and vanish for
`m > n + q`. -/
theorem exists_relCWComplex_homotopyEquiv_sublevel_of_isManifoldStronglyPseudoconvexAt
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
      ∀ k, finrank ℂ E + q < k → IsEmpty (cell (univ : Set X) k) := by
  obtain ⟨X, _, _, j, _, h, hj, hh, ⟨c⟩⟩ :=
    hf.exists_relCWComplex_homotopyEquiv_sublevel hab hcompact ha hb
  have hS : (criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Ioc a b).Finite :=
    (hf.finite_criticalPoints_inter hcompact).subset
      (inter_subset_inter_right _ (preimage_mono Ioc_subset_Icc_self))
  have := finite_sigma_criticalPoints_inter hS
  refine ⟨X, _, ‹_›, j, ‹_›, h, hj,
    RelCWComplex.finite_of_finite_cells (.of_equiv _ (Equiv.sigmaCongrRight c).symm),
    hh, fun m ↦ ⟨c m⟩, fun k hk ↦ (c k).isEmpty_congr.2 ?_⟩
  exact isEmpty_criticalPoints_inter_of_isManifoldStronglyPseudoconvexAt
    (hf.contMDiff.of_le (by norm_cast)) hq hk

/-- **Relative CW model of a regular cobordism of a strongly `q`-pseudoconvex Morse function.** Let
`f` be a real Morse function on `M`, `a ≤ b` regular values with compact band `f⁻¹[a, b]`, and
suppose `f` is strongly `q`-pseudoconvex at every critical point with value in `(a, b]`. Then the
cobordism `f⁻¹[a, b]` is homotopy equivalent to a finite CW complex `X` relative to a closedly
embedded copy of its incoming boundary `f⁻¹(a)`, with relative `m`-cells indexed by the critical
points of index `m` in `(a, b]` and no relative cells above `finrank ℂ E + q`. -/
theorem exists_relCWComplex_homotopyEquiv_band_of_isManifoldStronglyPseudoconvexAt
    {f : M → ℝ} {q : ℕ} (hf : IsMorse 𝓘(ℝ, E) f) {a b : ℝ} (hab : a ≤ b)
    (hcompact : IsCompact (f ⁻¹' Icc a b)) (ha : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f a)
    (hb : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f b)
    (hq : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Ioc a b,
      IsManifoldStronglyPseudoconvexAt E q f x) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (j : C(f ⁻¹' {a}, X))
      (_ : RelCWComplex (univ : Set X) (range j)) (h : X ≃ₕ f ⁻¹' Icc a b),
      IsClosedEmbedding j ∧ RelCWComplex.Finite (univ : Set X) ∧ (∀ x, (h (j x) : M) = x) ∧
      (∀ m, Nonempty (cell (univ : Set X) m ≃
        ↥{x ∈ criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Ioc a b | manifoldMorseIndex 𝓘(ℝ, E) f x = m})) ∧
      ∀ k, finrank ℂ E + q < k → IsEmpty (cell (univ : Set X) k) := by
  obtain ⟨X, _, _, j, _, h, hj, hh, ⟨c⟩⟩ :=
    hf.exists_relCWComplex_homotopyEquiv_band hab hcompact ha hb
  have hS : (criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Ioc a b).Finite :=
    (hf.finite_criticalPoints_inter hcompact).subset
      (inter_subset_inter_right _ (preimage_mono Ioc_subset_Icc_self))
  have := finite_sigma_criticalPoints_inter hS
  refine ⟨X, _, ‹_›, j, ‹_›, h, hj,
    RelCWComplex.finite_of_finite_cells (.of_equiv _ (Equiv.sigmaCongrRight c).symm),
    hh, fun m ↦ ⟨c m⟩, fun k hk ↦ (c k).isEmpty_congr.2 ?_⟩
  exact isEmpty_criticalPoints_inter_of_isManifoldStronglyPseudoconvexAt
    (hf.contMDiff.of_le (by norm_cast)) hq hk

/-- **Extending CW models across a strongly `q`-pseudoconvex regular band.** If `W ≃ₕ {f ≤ a}` is a
CW model with no cells above `finrank ℂ E + q`, and `f` is strongly `q`-pseudoconvex at its critical
points in `(a, b]`, then `W` extends along a closed cofibration `ι : W → W'` to a CW model
`W' ≃ₕ {f ≤ b}` which likewise has no cells above `finrank ℂ E + q`. -/
theorem
  exists_cwComplex_extension_homotopyEquiv_sublevel_of_isManifoldStronglyPseudoconvexAt
    {f : M → ℝ} {q : ℕ} (hf : IsMorse 𝓘(ℝ, E) f) {a b : ℝ} (hab : a ≤ b)
    (hcompact : IsCompact (f ⁻¹' Icc a b)) (ha : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f a)
    (hb : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f b)
    (hq : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Ioc a b,
      IsManifoldStronglyPseudoconvexAt E q f x)
    (W : Type u) [TopologicalSpace W] [T2Space W] [CWComplex (univ : Set W)]
    (hW : ∀ k, finrank ℂ E + q < k → IsEmpty (cell (univ : Set W) k))
    (h : W ≃ₕ {x | f x ≤ a}) :
    ∃ (W' : Type u) (_ : TopologicalSpace W') (_ : T2Space W') (_ : CWComplex (univ : Set W'))
      (ι : C(W, W')) (h' : W' ≃ₕ {x | f x ≤ b}),
      IsClosedEmbedding ι ∧ HasHomotopyExtensionProperty (range ι) ∧
      (∀ w, (h' (ι w) : M) = h w) ∧
      (∀ k, finrank ℂ E + q < k → IsEmpty (cell (univ : Set W') k)) ∧
      ∃ e : ∀ m, cell (univ : Set W') m ≃ cell (univ : Set W) m ⊕
          ↥{x ∈ criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Ioc a b | manifoldMorseIndex 𝓘(ℝ, E) f x = m},
        ∀ m j x, map m ((e m).symm (.inl j)) x = ι (map m j x) := by
  obtain ⟨W', _, _, _, ι, h', hι, hA, hh, e, he⟩ :=
    hf.exists_cwComplex_extension_homotopyEquiv_sublevel hab hcompact ha hb W h
  refine ⟨W', _, ‹_›, ‹_›, ι, h', hι, hA, hh, fun k hk ↦ ?_, e, he⟩
  have := hW k hk
  have := isEmpty_criticalPoints_inter_of_isManifoldStronglyPseudoconvexAt
    (hf.contMDiff.of_le (by norm_cast)) hq hk
  exact (e k).isEmpty_congr.2 inferInstance

/-- **Extending finite CW models across a strongly `q`-pseudoconvex regular band.** The finite-CW
form of
`IsMorse.exists_cwComplex_extension_homotopyEquiv_sublevel_of_isManifoldStronglyPseudoconvexAt`. -/
theorem
  exists_finite_cwComplex_extension_homotopyEquiv_sublevel_of_isManifoldStronglyPseudoconvexAt
    {f : M → ℝ} {q : ℕ} (hf : IsMorse 𝓘(ℝ, E) f) {a b : ℝ} (hab : a ≤ b)
    (hcompact : IsCompact (f ⁻¹' Icc a b)) (ha : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f a)
    (hb : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f b)
    (hq : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Ioc a b,
      IsManifoldStronglyPseudoconvexAt E q f x)
    (W : Type u) [TopologicalSpace W] [T2Space W] [CWComplex (univ : Set W)]
    [RelCWComplex.Finite (univ : Set W)]
    (hW : ∀ k, finrank ℂ E + q < k → IsEmpty (cell (univ : Set W) k))
    (h : W ≃ₕ {x | f x ≤ a}) :
    ∃ (W' : Type u) (_ : TopologicalSpace W') (_ : T2Space W') (_ : CWComplex (univ : Set W'))
      (ι : C(W, W')) (h' : W' ≃ₕ {x | f x ≤ b}),
      RelCWComplex.Finite (univ : Set W') ∧ IsClosedEmbedding ι ∧
      HasHomotopyExtensionProperty (range ι) ∧ (∀ w, (h' (ι w) : M) = h w) ∧
      (∀ k, finrank ℂ E + q < k → IsEmpty (cell (univ : Set W') k)) ∧
      ∃ e : ∀ m, cell (univ : Set W') m ≃ cell (univ : Set W) m ⊕
          ↥{x ∈ criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Ioc a b | manifoldMorseIndex 𝓘(ℝ, E) f x = m},
        ∀ m j x, map m ((e m).symm (.inl j)) x = ι (map m j x) := by
  obtain ⟨W', _, _, _, ι, h', hfin, hι, hA, hh, e, he⟩ :=
    hf.exists_finite_cwComplex_extension_homotopyEquiv_sublevel hab hcompact ha hb W h
  refine ⟨W', _, ‹_›, ‹_›, ι, h', hfin, hι, hA, hh, fun k hk ↦ ?_, e, he⟩
  have := hW k hk
  have := isEmpty_criticalPoints_inter_of_isManifoldStronglyPseudoconvexAt
    (hf.contMDiff.of_le (by norm_cast)) hq hk
  exact (e k).isEmpty_congr.2 inferInstance

/-- **Finite CW model of a compact regular sublevel of a strongly `q`-pseudoconvex Morse function.**
Let `f` be a real Morse function on `M`, let `b` be a regular value with compact sublevel `{f ≤ b}`,
and suppose `f` is strongly `q`-pseudoconvex at every critical point in `{f ≤ b}`. Then `{f ≤ b}` is
homotopy equivalent to a finite CW complex `W` whose `m`-cells correspond to the critical points of
index `m` in `{f ≤ b}`, with no cells above `finrank ℂ E + q`. -/
theorem exists_finite_cwComplex_homotopyEquiv_sublevel_of_isManifoldStronglyPseudoconvexAt
    {f : M → ℝ} {q : ℕ} (hf : IsMorse 𝓘(ℝ, E) f) {b : ℝ} (hcompact : IsCompact {x | f x ≤ b})
    (hb : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f b)
    (hq : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Iic b,
      IsManifoldStronglyPseudoconvexAt E q f x) :
    ∃ (W : Type u) (_ : TopologicalSpace W) (_ : T2Space W) (_ : CWComplex (univ : Set W)),
      RelCWComplex.Finite (univ : Set W) ∧ Nonempty (W ≃ₕ {x | f x ≤ b}) ∧
      (∀ m, Nonempty (cell (univ : Set W) m ≃
        ↥{x ∈ criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Iic b | manifoldMorseIndex 𝓘(ℝ, E) f x = m})) ∧
      ∀ k, finrank ℂ E + q < k → IsEmpty (cell (univ : Set W) k) := by
  obtain ⟨W, _, _, _, hfin, he, hc⟩ :=
    hf.exists_finite_cwComplex_homotopyEquiv_of_isCompact_sublevel hcompact hb
  refine ⟨W, _, ‹_›, ‹_›, hfin, he, hc, fun k hk ↦ (hc k).some.isEmpty_congr.2 ?_⟩
  exact isEmpty_criticalPoints_inter_of_isManifoldStronglyPseudoconvexAt
    (hf.contMDiff.of_le (by norm_cast)) hq hk

/-! ### Truncated Betti vanishing, Euler equality, and Morse polynomial identity across a band -/

section BandInequalities

variable {k : Type u} [DivisionRing k] (V : ModuleCat.{u} k) [Module.Finite k V]

/-- Across a compact regular band where a Morse function `f` is strongly `q`-pseudoconvex at its
critical points in `(a, b]`, the relative Betti numbers `dim Hⱼ({f ≤ b}, {f ≤ a}; V)` vanish for
`j > finrank ℂ E + q`. -/
theorem finrank_singularHomology_sublevelPair_eq_zero_of_isManifoldStronglyPseudoconvexAt
    {f : M → ℝ} {q : ℕ} (hf : IsMorse 𝓘(ℝ, E) f) {a b : ℝ} (hab : a ≤ b)
    (hcompact : IsCompact (f ⁻¹' Icc a b)) (ha : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f a)
    (hb : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f b)
    (hq : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Ioc a b,
      IsManifoldStronglyPseudoconvexAt E q f x) {j : ℕ} (hj : finrank ℂ E + q < j) :
    finrank k ((sublevelPair f hab).singularHomology V j : ModuleCat k) = 0 := by
  have hle := hf.finrank_singularHomology_sublevelPair_le V hab hcompact ha hb j
  have hempty : {x ∈ criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Ioc a b |
      manifoldMorseIndex 𝓘(ℝ, E) f x = j} = ∅ := by
    have := isEmpty_criticalPoints_inter_of_isManifoldStronglyPseudoconvexAt
      (hf.contMDiff.of_le (by norm_cast)) hq hj
    exact eq_empty_of_isEmpty _
  rw [hempty, ncard_empty, zero_mul, Nat.le_zero] at hle
  exact hle

/-- Across a compact regular band where a Morse function `f` is strongly `q`-pseudoconvex at its
critical points in `(a, b]`, the cobordism Betti numbers `dim Hⱼ(f⁻¹[a, b], f⁻¹(a); V)` vanish for
`j > finrank ℂ E + q`. -/
theorem finrank_singularHomology_bandPair_eq_zero_of_isManifoldStronglyPseudoconvexAt
    {f : M → ℝ} {q : ℕ} (hf : IsMorse 𝓘(ℝ, E) f) {a b : ℝ} (hab : a ≤ b)
    (hcompact : IsCompact (f ⁻¹' Icc a b)) (ha : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f a)
    (hb : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f b)
    (hq : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Ioc a b,
      IsManifoldStronglyPseudoconvexAt E q f x) {j : ℕ} (hj : finrank ℂ E + q < j) :
    finrank k ((bandPair f hab).singularHomology V j : ModuleCat k) = 0 := by
  have hle := hf.finrank_singularHomology_bandPair_le V hab hcompact ha hb j
  have hempty : {x ∈ criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Ioc a b |
      manifoldMorseIndex 𝓘(ℝ, E) f x = j} = ∅ := by
    have := isEmpty_criticalPoints_inter_of_isManifoldStronglyPseudoconvexAt
      (hf.contMDiff.of_le (by norm_cast)) hq hj
    exact eq_empty_of_isEmpty _
  rw [hempty, ncard_empty, zero_mul, Nat.le_zero] at hle
  exact hle

/-- **Truncated Euler equality for a strongly `q`-pseudoconvex band.** Because both the relative
Betti numbers and the critical counts vanish above `finrank ℂ E + q`, Euler's equality across a
compact regular band already holds at any truncation degree `m ≥ finrank ℂ E + q` (rather than
`m ≥ finrank ℝ E = 2 * finrank ℂ E`). -/
theorem sum_range_neg_one_pow_mul_finrank_sublevelPair_eq_of_isManifoldStronglyPseudoconvexAt
    {f : M → ℝ} {q : ℕ} (hf : IsMorse 𝓘(ℝ, E) f) {a b : ℝ} (hab : a ≤ b)
    (hcompact : IsCompact (f ⁻¹' Icc a b)) (ha : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f a)
    (hb : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f b)
    (hq : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Ioc a b,
      IsManifoldStronglyPseudoconvexAt E q f x) {m : ℕ} (hm : finrank ℂ E + q ≤ m) :
    ∑ i ∈ Finset.range (m + 1), (-1 : ℤ) ^ i *
        finrank k ((sublevelPair f hab).singularHomology V i : ModuleCat k) =
      finrank k V * ∑ i ∈ Finset.range (m + 1), (-1 : ℤ) ^ i *
        {x ∈ criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Ioc a b |
          manifoldMorseIndex 𝓘(ℝ, E) f x = i}.ncard := by
  set N := max m (finrank ℝ E)
  have hsub : Finset.range (m + 1) ⊆ Finset.range (N + 1) :=
    Finset.range_mono (Nat.add_le_add_right (le_max_left m _) 1)
  have hfull := hf.sum_range_neg_one_pow_mul_finrank_singularHomology_sublevelPair_eq V hab hcompact
    ha hb (le_max_right m (finrank ℝ E))
  have hL : ∑ i ∈ Finset.range (m + 1), (-1 : ℤ) ^ i *
      finrank k ((sublevelPair f hab).singularHomology V i : ModuleCat k) =
      ∑ i ∈ Finset.range (N + 1), (-1 : ℤ) ^ i *
        finrank k ((sublevelPair f hab).singularHomology V i : ModuleCat k) := by
    refine Finset.sum_subset hsub fun i _ hi ↦ ?_
    have him : finrank ℂ E + q < i := by simp only [Finset.mem_range] at hi; omega
    rw [hf.finrank_singularHomology_sublevelPair_eq_zero_of_isManifoldStronglyPseudoconvexAt V hab
      hcompact ha hb hq him, Nat.cast_zero, mul_zero]
  have hR : ∑ i ∈ Finset.range (m + 1), (-1 : ℤ) ^ i *
      ({x ∈ criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Ioc a b |
        manifoldMorseIndex 𝓘(ℝ, E) f x = i}.ncard : ℤ) =
      ∑ i ∈ Finset.range (N + 1), (-1 : ℤ) ^ i *
        {x ∈ criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Ioc a b |
          manifoldMorseIndex 𝓘(ℝ, E) f x = i}.ncard := by
    refine Finset.sum_subset hsub fun i _ hi ↦ ?_
    have him : finrank ℂ E + q < i := by simp only [Finset.mem_range] at hi; omega
    have := isEmpty_criticalPoints_inter_of_isManifoldStronglyPseudoconvexAt
      (hf.contMDiff.of_le (by norm_cast)) hq him
    rw [eq_empty_of_isEmpty {x ∈ criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Ioc a b |
      manifoldMorseIndex 𝓘(ℝ, E) f x = i}, ncard_empty, Nat.cast_zero, mul_zero]
  rw [hL, hfull, hR]

/-- **Truncated Euler equality for a strongly `q`-pseudoconvex cobordism.** The `bandPair` form of
`IsMorse.sum_range_neg_one_pow_mul_finrank_sublevelPair_eq_of_isManifoldStronglyPseudoconvexAt`. -/
theorem sum_range_neg_one_pow_mul_finrank_bandPair_eq_of_isManifoldStronglyPseudoconvexAt
    {f : M → ℝ} {q : ℕ} (hf : IsMorse 𝓘(ℝ, E) f) {a b : ℝ} (hab : a ≤ b)
    (hcompact : IsCompact (f ⁻¹' Icc a b)) (ha : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f a)
    (hb : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f b)
    (hq : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Ioc a b,
      IsManifoldStronglyPseudoconvexAt E q f x) {m : ℕ} (hm : finrank ℂ E + q ≤ m) :
    ∑ i ∈ Finset.range (m + 1), (-1 : ℤ) ^ i *
        finrank k ((bandPair f hab).singularHomology V i : ModuleCat k) =
      finrank k V * ∑ i ∈ Finset.range (m + 1), (-1 : ℤ) ^ i *
        {x ∈ criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Ioc a b |
          manifoldMorseIndex 𝓘(ℝ, E) f x = i}.ncard := by
  have h_eq (i : ℕ) : finrank k ((bandPair f hab).singularHomology V i : ModuleCat k) =
      finrank k ((sublevelPair f hab).singularHomology V i : ModuleCat k) := by
    have := isIso_singularHomologyMap_bandPairInclusion hf.contMDiff hab hcompact ha V i
    exact
      (asIso (TopPair.singularHomologyMap (bandPairInclusion f hab) V i)).toLinearEquiv.finrank_eq
  simpa only [h_eq] using
    hf.sum_range_neg_one_pow_mul_finrank_sublevelPair_eq_of_isManifoldStronglyPseudoconvexAt
      V hab hcompact ha hb hq hm

/-- **Truncated Morse polynomial identity for a strongly `q`-pseudoconvex band.** Across a compact
regular band where `f` is strongly `q`-pseudoconvex on `(a, b]`, for every `m ≥ finrank ℂ E + q`
there is a natural-coefficient polynomial `Q` of degree `< m` (`Q.coeff i = 0` for `i ≥ m`) such
that `∑ᵢ₌₀ᵐ cᵢ dim V · tⁱ = ∑ᵢ₌₀ᵐ bᵢ tⁱ + (1 + t) Q(t)`. -/
theorem exists_sum_range_monomial_sublevelPair_eq_add_mul_of_isManifoldStronglyPseudoconvexAt
    {f : M → ℝ} {q : ℕ} (hf : IsMorse 𝓘(ℝ, E) f) {a b : ℝ} (hab : a ≤ b)
    (hcompact : IsCompact (f ⁻¹' Icc a b)) (ha : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f a)
    (hb : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f b)
    (hq : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Ioc a b,
      IsManifoldStronglyPseudoconvexAt E q f x) {m : ℕ} (hm : finrank ℂ E + q ≤ m) :
    ∃ Q : ℕ[X], ∑ i ∈ Finset.range (m + 1), monomial i
          ({x ∈ criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Ioc a b |
            manifoldMorseIndex 𝓘(ℝ, E) f x = i}.ncard * finrank k V) =
        ∑ i ∈ Finset.range (m + 1),
          monomial i (finrank k ((sublevelPair f hab).singularHomology V i : ModuleCat k)) +
          (1 + X) * Q ∧
      (∀ i < m, (Q.coeff i : ℤ) =
        finrank k V * ∑ j ∈ Finset.range (i + 1), (-1 : ℤ) ^ (i - j) *
            {x ∈ criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Ioc a b |
              manifoldMorseIndex 𝓘(ℝ, E) f x = j}.ncard -
          ∑ j ∈ Finset.range (i + 1), (-1 : ℤ) ^ (i - j) *
            finrank k ((sublevelPair f hab).singularHomology V j : ModuleCat k)) ∧
      ∀ i, m ≤ i → Q.coeff i = 0 := by
  have hmul (r : ℕ) (g : ℕ → ℤ) : (finrank k V : ℤ) * ∑ j ∈ Finset.range (r + 1), g j *
      ({x ∈ criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Ioc a b |
        manifoldMorseIndex 𝓘(ℝ, E) f x = j}.ncard : ℤ) =
      ∑ j ∈ Finset.range (r + 1), g j *
        (({x ∈ criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Ioc a b |
          manifoldMorseIndex 𝓘(ℝ, E) f x = j}.ncard * finrank k V : ℕ) : ℤ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by push_cast; ring
  have heuler :=
    hf.sum_range_neg_one_pow_mul_finrank_sublevelPair_eq_of_isManifoldStronglyPseudoconvexAt
      V hab hcompact ha hb hq hm
  obtain ⟨Q, hQ, hcoeff, hzero⟩ := TauCeti.exists_sum_range_monomial_eq_add_mul
    (b := fun i ↦ finrank k ((sublevelPair f hab).singularHomology V i : ModuleCat k))
    (c := fun i ↦ {x ∈ criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Ioc a b |
      manifoldMorseIndex 𝓘(ℝ, E) f x = i}.ncard * finrank k V) (n := m)
    (fun r _ ↦ (hf.sum_range_neg_one_pow_mul_finrank_singularHomology_sublevelPair_le V hab
      hcompact ha hb r).trans_eq (hmul r _))
    (heuler.trans (hmul m _))
  refine ⟨Q, hQ, fun i hi ↦ ?_, hzero⟩
  rw [hcoeff i hi, ← hmul i _]

/-- **Truncated Morse polynomial identity for a strongly `q`-pseudoconvex cobordism.** The
`bandPair` form of
`IsMorse.exists_sum_range_monomial_sublevelPair_eq_add_mul_of_isManifoldStronglyPseudoconvexAt`. -/
theorem exists_sum_range_monomial_bandPair_eq_add_mul_of_isManifoldStronglyPseudoconvexAt
    {f : M → ℝ} {q : ℕ} (hf : IsMorse 𝓘(ℝ, E) f) {a b : ℝ} (hab : a ≤ b)
    (hcompact : IsCompact (f ⁻¹' Icc a b)) (ha : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f a)
    (hb : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f b)
    (hq : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Ioc a b,
      IsManifoldStronglyPseudoconvexAt E q f x) {m : ℕ} (hm : finrank ℂ E + q ≤ m) :
    ∃ Q : ℕ[X], ∑ i ∈ Finset.range (m + 1), monomial i
          ({x ∈ criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Ioc a b |
            manifoldMorseIndex 𝓘(ℝ, E) f x = i}.ncard * finrank k V) =
        ∑ i ∈ Finset.range (m + 1),
          monomial i (finrank k ((bandPair f hab).singularHomology V i : ModuleCat k)) +
          (1 + X) * Q ∧
      (∀ i < m, (Q.coeff i : ℤ) =
        finrank k V * ∑ j ∈ Finset.range (i + 1), (-1 : ℤ) ^ (i - j) *
            {x ∈ criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Ioc a b |
              manifoldMorseIndex 𝓘(ℝ, E) f x = j}.ncard -
          ∑ j ∈ Finset.range (i + 1), (-1 : ℤ) ^ (i - j) *
            finrank k ((bandPair f hab).singularHomology V j : ModuleCat k)) ∧
      ∀ i, m ≤ i → Q.coeff i = 0 := by
  have h_eq (i : ℕ) : finrank k ((bandPair f hab).singularHomology V i : ModuleCat k) =
      finrank k ((sublevelPair f hab).singularHomology V i : ModuleCat k) := by
    have := isIso_singularHomologyMap_bandPairInclusion hf.contMDiff hab hcompact ha V i
    exact
      (asIso (TopPair.singularHomologyMap (bandPairInclusion f hab) V i)).toLinearEquiv.finrank_eq
  simpa only [h_eq] using
    hf.exists_sum_range_monomial_sublevelPair_eq_add_mul_of_isManifoldStronglyPseudoconvexAt
      V hab hcompact ha hb hq hm

end BandInequalities

/-! ### Global Hausdorff CW model of a proper strongly `q`-pseudoconvex Morse exhaustion -/

/-- **The CW model of a proper strongly `q`-pseudoconvex Morse exhaustion.** Let `f` be a proper,
bounded-below real Morse function on a complex manifold `M` of complex dimension `n`, strongly
`q`-pseudoconvex at each of its critical points. Then `M` is homotopy equivalent to a Hausdorff CW
complex `X` whose `m`-cells correspond to the critical points of `f` of index `m`, and in particular
`X` has no cells in dimension above `n + q`. -/
theorem exists_cwComplex_homotopyEquiv_of_isManifoldStronglyPseudoconvexAt
    {f : M → ℝ} {q : ℕ} (hf : IsMorse 𝓘(ℝ, E) f) (hp : IsProperMap f) (hbdd : BddBelow (range f))
    (hq : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f, IsManifoldStronglyPseudoconvexAt E q f x) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      Nonempty (M ≃ₕ X) ∧
      (∀ m, Nonempty (cell (univ : Set X) m ≃
        ↥{x ∈ criticalPoints 𝓘(ℝ, E) f | manifoldMorseIndex 𝓘(ℝ, E) f x = m})) ∧
      ∀ k, finrank ℂ E + q < k → IsEmpty (cell (univ : Set X) k) := by
  obtain ⟨X, _, _, _, he, hc⟩ := hf.exists_cwComplex_homotopyEquiv hp hbdd
  refine ⟨X, _, ‹_›, ‹_›, he, hc, fun k hk ↦ (hc k).some.isEmpty_congr.2 ?_⟩
  simpa only [inter_univ] using
    isEmpty_criticalPoints_inter_of_isManifoldStronglyPseudoconvexAt (s := univ)
      (hf.contMDiff.of_le (by norm_cast)) (fun x hx ↦ hq x hx.1) hk

end IsMorse

end PseudoconvexMorse

/-! ### Smooth (non-Morse) pseudoconvex exhaustions and regular sublevel domains -/

section SmoothPseudoconvex

variable {E : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M] [T2Space M]

local instance : FiniteDimensional ℝ E := Module.Finite.trans ℂ E

local instance : IsManifold 𝓘(ℝ, E) ∞ M :=
  IsManifold.restrictScalars ℝ (inferInstance : IsManifold 𝓘(ℂ, E) ∞ M)

/-- **Hausdorff CW model of a complex manifold with a smooth strongly `q`-pseudoconvex exhaustion.**
If a complex manifold `M` of complex dimension `n` carries a smooth proper bounded-below everywhere
strongly `q`-pseudoconvex function `f : M → ℝ` (not assumed to be Morse), then `M` is homotopy
equivalent to a Hausdorff CW complex `X` with no cells in dimension above `n + q`. -/
theorem exists_cwComplex_homotopyEquiv_of_isProperMap_of_isManifoldStronglyPseudoconvexAt
    {f : M → ℝ} {q : ℕ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f) (hp : IsProperMap f)
    (hbdd : BddBelow (range f)) (hq : ∀ x, IsManifoldStronglyPseudoconvexAt E q f x) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      Nonempty (M ≃ₕ X) ∧ ∀ k, finrank ℂ E + q < k → IsEmpty (cell (univ : Set X) k) := by
  let F : C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯ := ⟨f, hf⟩
  obtain ⟨g, hgm, hgp, hgbdd, -, -, hgq, -⟩ :=
    F.exists_isMorse_isProperMap_bddBelow_isManifoldStronglyPseudoconvexAt q hq hp hbdd
      isClosed_empty isOpen_empty (subset_refl _) isMorseOn_empty
  obtain ⟨X, _, _, _, he, -, hempty⟩ :=
    hgm.exists_cwComplex_homotopyEquiv_of_isManifoldStronglyPseudoconvexAt hgp hgbdd
      fun x _ ↦ hgq x
  exact ⟨X, _, ‹_›, ‹_›, he, hempty⟩

/-- **Hausdorff CW model of a complex manifold with a smooth strictly plurisubharmonic exhaustion.**
If `M` carries a smooth proper bounded-below everywhere strictly plurisubharmonic function
(not assumed Morse), then `M` is homotopy equivalent to a Hausdorff CW complex with no cells above
the complex dimension `finrank ℂ E`. -/
theorem exists_cwComplex_homotopyEquiv_of_isProperMap_of_isManifoldStrictlyPlurisubharmonicAt
    {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f) (hp : IsProperMap f)
    (hbdd : BddBelow (range f)) (hpsh : ∀ x, IsManifoldStrictlyPlurisubharmonicAt E f x) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      Nonempty (M ≃ₕ X) ∧ ∀ k, finrank ℂ E < k → IsEmpty (cell (univ : Set X) k) := by
  simpa only [add_zero] using
    exists_cwComplex_homotopyEquiv_of_isProperMap_of_isManifoldStronglyPseudoconvexAt (q := 0) hf hp
      hbdd fun x ↦ (hpsh x).isManifoldStronglyPseudoconvexAt 0

/-- **Finite CW model of a smooth strongly `q`-pseudoconvex regular sublevel domain.** Let `f` be a
smooth everywhere strongly `q`-pseudoconvex function (not assumed Morse or proper) on a
sigma-compact complex manifold `M`, let `b < c` with `{f ≤ c}` compact, and suppose `b` is a
regular value of `f`. Then `{f ≤ b}` is homotopy equivalent to a finite CW complex `W` with no
cells in dimension above `finrank ℂ E + q`. -/
theorem exists_finite_cwComplex_homotopyEquiv_sublevel_of_isManifoldStronglyPseudoconvexAt
    [SigmaCompactSpace M] {f : M → ℝ} {q : ℕ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f)
    (hq : ∀ x, IsManifoldStronglyPseudoconvexAt E q f x) {b c : ℝ} (hbc : b < c)
    (hcompact : IsCompact {x | f x ≤ c}) (hb : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f b) :
    ∃ (W : Type u) (_ : TopologicalSpace W) (_ : T2Space W) (_ : CWComplex (univ : Set W)),
      RelCWComplex.Finite (univ : Set W) ∧ Nonempty (W ≃ₕ {x | f x ≤ b}) ∧
      ∀ k, finrank ℂ E + q < k → IsEmpty (cell (univ : Set W) k) := by
  have : IsManifold 𝓘(ℝ, E) 1 M := .of_le (n := ∞) (by norm_cast)
  obtain ⟨δ, hδ, -, hcrit⟩ :=
    exists_Icc_disjoint_criticalPoints_of_isCompact_sublevel (hf.of_le (by simp)) hbc hcompact hb
  let F : C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯ := ⟨f, hf⟩
  have hfV : IsMorseOn 𝓘(ℝ, E) F (f ⁻¹' Ioo (b - δ) (b + δ)) :=
    isMorseOn_iff_criticalPoints.2 ⟨hf.contMDiffOn, fun x hx_mem hx_crit ↦
      (hcrit x (Ioo_subset_Icc_self hx_mem) hx_crit).elim⟩
  obtain ⟨g, hgm, hgf, hgs, hgq, -⟩ := F.exists_isMorse_sub_compl_isManifoldStronglyPseudoconvexAt q
    hq continuous_const (fun _ ↦ half_pos hδ)
    (C := f ⁻¹' Icc (b - δ / 2) (b + δ / 2)) (V := f ⁻¹' Ioo (b - δ) (b + δ))
    (isClosed_Icc.preimage hf.continuous) (isOpen_Ioo.preimage hf.continuous)
    (preimage_mono (Icc_subset_Ioo (by linarith) (by linarith))) hfV
  obtain ⟨hsub_eq, hgb⟩ := sublevel_eq_and_isRegularValue_of_abs_sub_lt hf.continuous hδ hcrit hgf
    hgs
  have hcompact_b : IsCompact {x | (g : M → ℝ) x ≤ b} := by
    rw [hsub_eq]
    exact hcompact.of_isClosed_subset (isClosed_le hf.continuous continuous_const)
      fun x hx ↦ hx.trans hbc.le
  obtain ⟨W, _, _, _, hfin, ⟨e⟩, -, hempty⟩ :=
    hgm.exists_finite_cwComplex_homotopyEquiv_sublevel_of_isManifoldStronglyPseudoconvexAt
      hcompact_b hgb fun x _ ↦ hgq x
  exact ⟨W, _, ‹_›, ‹_›, hfin, ⟨e.trans (Homeomorph.setCongr hsub_eq).toHomotopyEquiv⟩, hempty⟩

/-- **Finite CW model of a smoothly bounded strictly Levi-pseudoconvex regular domain.** The
strictly plurisubharmonic (`q = 0`) specialization of
`TauCeti.exists_finite_cwComplex_homotopyEquiv_sublevel_of_isManifoldStronglyPseudoconvexAt`:
`{f ≤ b}` is homotopy equivalent to a finite CW complex of dimension at most `finrank ℂ E`. -/
theorem exists_finite_cwComplex_homotopyEquiv_sublevel_of_isManifoldStrictlyPlurisubharmonicAt
    [SigmaCompactSpace M] {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f)
    (hpsh : ∀ x, IsManifoldStrictlyPlurisubharmonicAt E f x) {b c : ℝ} (hbc : b < c)
    (hcompact : IsCompact {x | f x ≤ c}) (hb : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f b) :
    ∃ (W : Type u) (_ : TopologicalSpace W) (_ : T2Space W) (_ : CWComplex (univ : Set W)),
      RelCWComplex.Finite (univ : Set W) ∧ Nonempty (W ≃ₕ {x | f x ≤ b}) ∧
      ∀ k, finrank ℂ E < k → IsEmpty (cell (univ : Set W) k) := by
  simpa only [add_zero] using
    exists_finite_cwComplex_homotopyEquiv_sublevel_of_isManifoldStronglyPseudoconvexAt (q := 0) hf
      (fun x ↦ (hpsh x).isManifoldStronglyPseudoconvexAt 0) hbc hcompact hb

/-- **Finite CW model of a regular sublevel of a smooth strongly `q`-pseudoconvex exhaustion.** For
a smooth proper bounded-below everywhere strongly `q`-pseudoconvex exhaustion `f : M → ℝ` (not
assumed Morse, and without assuming sigma-compactness separately), every regular sublevel `{f ≤ b}`
is homotopy equivalent to a finite CW complex with no cells above `finrank ℂ E + q`. -/
theorem
  exists_finite_cwComplex_homotopyEquiv_sublevel_of_isProperMap_of_isManifoldStronglyPseudoconvexAt
    {f : M → ℝ} {q : ℕ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f) (hp : IsProperMap f)
    (hbdd : BddBelow (range f)) (hq : ∀ x, IsManifoldStronglyPseudoconvexAt E q f x) {b : ℝ}
    (hb : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f b) :
    ∃ (W : Type u) (_ : TopologicalSpace W) (_ : T2Space W) (_ : CWComplex (univ : Set W)),
      RelCWComplex.Finite (univ : Set W) ∧ Nonempty (W ≃ₕ {x | f x ≤ b}) ∧
      ∀ k, finrank ℂ E + q < k → IsEmpty (cell (univ : Set W) k) := by
  have : SigmaCompactSpace M := hp.sigmaCompactSpace
  obtain ⟨m, hm⟩ := hbdd
  have hcompact : IsCompact {x | f x ≤ b + 1} := by
    have heq : {x | f x ≤ b + 1} = f ⁻¹' Icc m (b + 1) := by
      ext x
      exact ⟨fun hx ↦ ⟨hm (mem_range_self x), hx⟩, And.right⟩
    rw [heq]
    exact hp.isCompact_preimage isCompact_Icc
  exact exists_finite_cwComplex_homotopyEquiv_sublevel_of_isManifoldStronglyPseudoconvexAt hf hq
    (lt_add_one b) hcompact hb

end SmoothPseudoconvex

/-! ### Proper holomorphic immersions, closed holomorphic embeddings, and affine zero loci -/

section HolomorphicImmersion

variable {E : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] {r : ℕ∞ω} [IsManifold 𝓘(ℂ, E) r M] [T2Space M]

/-- **Generic squared-distance CW models along a proper holomorphic immersion** (Milnor,
*Morse Theory*, Theorem 7.2). Let `i : M → F` be a proper holomorphic (`MDifferentiable`) immersion
of a complex manifold `M` of complex dimension `n` into a proper complex inner product space `F`.
For Haar-almost every centre `a ∈ F`, the squared distance `x ↦ ‖i x - a‖²` is a proper
bounded-below Morse function on `M` and `M` is homotopy equivalent to a Hausdorff CW complex `X`
whose `m`-cells correspond to its critical points of index `m`, with no cells in dimension above
`n`. -/
theorem ae_isMorse_and_exists_cwComplex_homotopyEquiv_norm_sq_sub_comp
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [ProperSpace F]
    [MeasurableSpace F] [BorelSpace F] (μ : Measure F) [μ.IsAddHaarMeasure]
    {i : M → F} (hi : MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, F) i)
    (hinj : ∀ x, Function.Injective (mvfderiv 𝓘(ℂ, E) i x)) (hip : IsProperMap i)
    (hr : r ≠ 0 := by simp) :
    ∀ᵐ a ∂μ, IsMorse 𝓘(ℝ, E) (fun x ↦ ‖i x - a‖ ^ 2) ∧
      ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
        Nonempty (M ≃ₕ X) ∧
        (∀ m, Nonempty (cell (univ : Set X) m ≃
          ↥{x ∈ criticalPoints 𝓘(ℝ, E) (fun y ↦ ‖i y - a‖ ^ 2) |
            manifoldMorseIndex 𝓘(ℝ, E) (fun y ↦ ‖i y - a‖ ^ 2) x = m})) ∧
        ∀ k, finrank ℂ E < k → IsEmpty (cell (univ : Set X) k) := by
  have : FiniteDimensional ℂ F := .of_locallyCompactSpace ℂ
  have : CompleteSpace F := FiniteDimensional.completeSpace ℂ F
  have : IsManifold 𝓘(ℂ, E) 1 M := IsManifold.of_ne_zero 1 hr ‹_›
  have : IsManifold 𝓘(ℂ, E) ∞ M := IsManifold.of_ne_zero ∞ hr ‹_›
  have : FiniteDimensional ℝ E := Module.Finite.trans ℂ E
  have : IsManifold 𝓘(ℝ, E) ∞ M := IsManifold.restrictScalars_of_ne_zero ∞ hr ‹_›
  have : SigmaCompactSpace M := hip.sigmaCompactSpace
  have : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact E M
  have hi_smooth : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ∞ i := hi.contMDiff
  filter_upwards [ae_isMorse_and_manifoldMorseIndex_norm_sq_sub_comp_le μ hi_smooth hinj]
    with a ⟨ha, hidx⟩
  have hap : IsProperMap (fun x ↦ ‖i x - a‖ ^ 2) :=
    (isProperMap_norm_sq_sub_comp_iff hi.continuous a).2 hip
  have hbdd : BddBelow (range fun x ↦ ‖i x - a‖ ^ 2) := ⟨0, by rintro _ ⟨x, rfl⟩; positivity⟩
  obtain ⟨X, _, _, _, he, hc⟩ := ha.exists_cwComplex_homotopyEquiv hap hbdd
  refine ⟨ha, X, _, ‹_›, ‹_›, he, hc, fun k hk ↦ (hc k).some.isEmpty_congr.2 ⟨fun x ↦ ?_⟩⟩
  have hle := hidx x.1 x.2.1
  have heq : manifoldMorseIndex 𝓘(ℝ, E) (fun y ↦ ‖i y - a‖ ^ 2) x.1 = k := x.2.2
  omega

/-- **Existence of a squared-distance CW model along a proper holomorphic immersion.** Along a
proper holomorphic (`MDifferentiable`) immersion `i : M → F` into a proper complex inner product
space, for some centre `a ∈ F` the squared distance `x ↦ ‖i x - a‖²` is a Morse function giving a
Hausdorff CW model of `M` with cells indexed by its critical points and no cells above
`finrank ℂ E`. -/
theorem exists_cwComplex_homotopyEquiv_norm_sq_sub_comp
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [ProperSpace F]
    {i : M → F} (hi : MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, F) i)
    (hinj : ∀ x, Function.Injective (mvfderiv 𝓘(ℂ, E) i x)) (hip : IsProperMap i)
    (hr : r ≠ 0 := by simp) :
    ∃ a : F, IsMorse 𝓘(ℝ, E) (fun x ↦ ‖i x - a‖ ^ 2) ∧
      ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
        Nonempty (M ≃ₕ X) ∧
        (∀ m, Nonempty (cell (univ : Set X) m ≃
          ↥{x ∈ criticalPoints 𝓘(ℝ, E) (fun y ↦ ‖i y - a‖ ^ 2) |
            manifoldMorseIndex 𝓘(ℝ, E) (fun y ↦ ‖i y - a‖ ^ 2) x = m})) ∧
        ∀ k, finrank ℂ E < k → IsEmpty (cell (univ : Set X) k) := by
  have : FiniteDimensional ℂ F := .of_locallyCompactSpace ℂ
  have : FiniteDimensional ℝ F := Module.Finite.trans ℂ F
  let _ : MeasurableSpace F := borel F
  have : BorelSpace F := ⟨rfl⟩
  exact (ae_isMorse_and_exists_cwComplex_homotopyEquiv_norm_sq_sub_comp Measure.addHaar hi hinj
    hip hr).exists

/-- **Andreotti–Frankel / Milnor CW dimension bound for proper holomorphic immersions.** If a
complex manifold `M` of complex dimension `n` admits a proper holomorphic (`MDifferentiable`)
immersion into a finite-dimensional complex normed space `F` (such as `Fin N → ℂ`), then `M` is
homotopy equivalent to a Hausdorff CW complex `X` with no cells in dimension above `n`. -/
theorem exists_cwComplex_homotopyEquiv_of_isProperMap_holomorphic_immersion
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    {i : M → F} (hi : MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, F) i)
    (hinj : ∀ x, Function.Injective (mvfderiv 𝓘(ℂ, E) i x)) (hip : IsProperMap i)
    (hr : r ≠ 0 := by simp) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      Nonempty (M ≃ₕ X) ∧ ∀ k, finrank ℂ E < k → IsEmpty (cell (univ : Set X) k) := by
  let L : F ≃L[ℂ] EuclideanSpace ℂ (Fin (finrank ℂ F)) :=
    (FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq
      (finrank_euclideanSpace_fin (𝕜 := ℂ) (n := finrank ℂ F)).symm).some
  have : FiniteDimensional ℝ (EuclideanSpace ℂ (Fin (finrank ℂ F))) := Module.Finite.trans ℂ _
  have hLi : MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, EuclideanSpace ℂ (Fin (finrank ℂ F))) (L ∘ i) :=
    (L.contDiff.contMDiff (n := 1).mdifferentiable one_ne_zero).comp hi
  have hLinj (x : M) : Function.Injective (mvfderiv 𝓘(ℂ, E) (L ∘ i) x) := by
    intro v w hvw
    simp only [mvfderiv_comp_apply_of_differentiableAt L.differentiableAt (hi x), L.fderiv] at hvw
    exact hinj x (L.injective hvw)
  have hLip : IsProperMap (L ∘ i) := L.toHomeomorph.isClosedEmbedding.isProperMap.comp hip
  obtain ⟨_, -, X, _, _, _, he, -, hempty⟩ :=
    exists_cwComplex_homotopyEquiv_norm_sq_sub_comp hLi hLinj hLip hr
  exact ⟨X, _, ‹_›, ‹_›, he, hempty⟩

/-- **Andreotti–Frankel / Milnor CW dimension bound for proper holomorphic `IsImmersion`s.** Applies
to complex `C^r` manifolds and `C^r` immersions for any `r ≠ 0` (including `1`, `∞`, and `ω`). -/
theorem _root_.Manifold.IsImmersion.exists_cwComplex_homotopyEquiv_of_isProperMap
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    {i : M → F} (hi : Manifold.IsImmersion 𝓘(ℂ, E) 𝓘(ℂ, F) r i) (hip : IsProperMap i)
    (hr : r ≠ 0 := by simp) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      Nonempty (M ≃ₕ X) ∧ ∀ k, finrank ℂ E < k → IsEmpty (cell (univ : Set X) k) :=
  exists_cwComplex_homotopyEquiv_of_isProperMap_holomorphic_immersion
    (hi.contMDiff.mdifferentiable hr)
    (fun x ↦ injective_mvfderiv_iff.2 (hi.mfderiv_injective hr x)) hip hr

/-- **Milnor's Theorem 7.2 for closed holomorphic embeddings.** Let `i : M → F` be a holomorphic
(`MDifferentiable`) immersion of a complex manifold `M` of complex dimension `n` into a
finite-dimensional complex normed space `F` (for instance `Fin N → ℂ`), which is a closed
topological embedding. Then `M` is homotopy equivalent to a Hausdorff CW complex `X` with no cells
in dimension above `n`. -/
theorem exists_cwComplex_homotopyEquiv_of_isClosedEmbedding
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    {i : M → F} (hi : MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, F) i)
    (hinj : ∀ x, Function.Injective (mvfderiv 𝓘(ℂ, E) i x)) (hclosed : IsClosedEmbedding i)
    (hr : r ≠ 0 := by simp) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      Nonempty (M ≃ₕ X) ∧ ∀ k, finrank ℂ E < k → IsEmpty (cell (univ : Set X) k) :=
  exists_cwComplex_homotopyEquiv_of_isProperMap_holomorphic_immersion hi hinj hclosed.isProperMap hr

/-- **Milnor's Theorem 7.2 (`Manifold.IsImmersion` form).** Every complex manifold `M` of complex
dimension `n` admitting a closed holomorphic `C^r` immersion (`r ≠ 0`) into a finite-dimensional
complex normed space `F` is homotopy equivalent to a Hausdorff CW complex `X` with no cells above
dimension `n`. -/
theorem _root_.Manifold.IsImmersion.exists_cwComplex_homotopyEquiv_of_isClosedEmbedding
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    {i : M → F} (hi : Manifold.IsImmersion 𝓘(ℂ, E) 𝓘(ℂ, F) r i) (hclosed : IsClosedEmbedding i)
    (hr : r ≠ 0 := by simp) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      Nonempty (M ≃ₕ X) ∧ ∀ k, finrank ℂ E < k → IsEmpty (cell (univ : Set X) k) :=
  hi.exists_cwComplex_homotopyEquiv_of_isProperMap hclosed.isProperMap hr

end HolomorphicImmersion

section AffineZeroLocus

open MvPolynomial

/-- **Squared-distance CW model of a smooth affine complete intersection.** Let `Z ⊆ ℂ^σ` be the
common zero locus of a polynomial family `p : ι → ℂ[X_σ]` whose Jacobian matrix has surjective
multiplication at every common zero, a complex manifold of complex dimension `|σ| - |ι|`. For some
Euclidean centre `a`, the squared distance `y ↦ ‖toLp 2 y - a‖²` is a Morse function on `Z`, and
`Z` is homotopy equivalent to a Hausdorff CW complex `X` whose `m`-cells correspond to the critical
points of index `m` and vanish for `m > |σ| - |ι|`. -/
theorem exists_cwComplex_homotopyEquiv_norm_sq_sub_toLp_affineZeroLocus
    {σ : Type u} {ι : Type*} [Fintype σ] [Fintype ι] {p : ι → MvPolynomial σ ℂ}
    (hp : ∀ x ∈ affineZeroLocus p, Function.Surjective (jacobiMatrixAt p x).mulVec) :
    letI := affineZeroLocusChartedSpace hp
    ∃ a : EuclideanSpace ℂ σ,
      IsMorse 𝓘(ℝ, Fin (Fintype.card σ - Fintype.card ι) → ℂ)
        (fun y : affineZeroLocus p ↦ ‖WithLp.toLp 2 (y : σ → ℂ) - a‖ ^ 2) ∧
      ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
        Nonempty (affineZeroLocus p ≃ₕ X) ∧
        (∀ m, Nonempty (cell (univ : Set X) m ≃
          ↥{x ∈ criticalPoints 𝓘(ℝ, Fin (Fintype.card σ - Fintype.card ι) → ℂ)
              (fun y : affineZeroLocus p ↦ ‖WithLp.toLp 2 (y : σ → ℂ) - a‖ ^ 2) |
            manifoldMorseIndex 𝓘(ℝ, Fin (Fintype.card σ - Fintype.card ι) → ℂ)
              (fun y : affineZeroLocus p ↦ ‖WithLp.toLp 2 (y : σ → ℂ) - a‖ ^ 2) x = m})) ∧
        ∀ k, Fintype.card σ - Fintype.card ι < k → IsEmpty (cell (univ : Set X) k) := by
  let _ := affineZeroLocusChartedSpace hp
  have := isManifold_affineZeroLocus hp ∞
  have : FiniteDimensional ℝ (EuclideanSpace ℂ σ) := Module.Finite.trans ℂ _
  have hip : IsProperMap (fun y : affineZeroLocus p ↦ WithLp.toLp 2 (y : σ → ℂ)) :=
    ((EuclideanSpace.equiv σ ℂ).symm.toHomeomorph.isClosedEmbedding.comp
      (isClosed_affineZeroLocus p).isClosedEmbedding_subtypeVal).isProperMap
  obtain ⟨a, ha, X, _, _, _, he, hc, hempty⟩ :=
    exists_cwComplex_homotopyEquiv_norm_sq_sub_comp
      ((contMDiff_toLp_coe_affineZeroLocus hp 1).mdifferentiable one_ne_zero)
      (injective_mvfderiv_toLp_coe_affineZeroLocus hp) hip (r := ∞)
  refine ⟨a, ha, X, _, ‹_›, ‹_›, he, hc, fun k hk ↦ hempty k ?_⟩
  rwa [Module.finrank_fin_fun]

/-- **Andreotti–Frankel / Milnor theorem for smooth affine complete intersections.** If the Jacobian
matrix of a polynomial family `p : ι → ℂ[X_σ]` is surjective at every common zero in `ℂ^σ`, then the
affine zero locus `affineZeroLocus p` is homotopy equivalent to a Hausdorff CW complex with no cells
in dimension above `|σ| - |ι|`. -/
theorem exists_cwComplex_homotopyEquiv_affineZeroLocus
    {σ : Type u} {ι : Type*} [Fintype σ] [Fintype ι] {p : ι → MvPolynomial σ ℂ}
    (hp : ∀ x ∈ affineZeroLocus p, Function.Surjective (jacobiMatrixAt p x).mulVec) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      Nonempty (affineZeroLocus p ≃ₕ X) ∧
      ∀ k, Fintype.card σ - Fintype.card ι < k → IsEmpty (cell (univ : Set X) k) := by
  obtain ⟨_, -, X, _, _, _, he, -, hempty⟩ :=
    exists_cwComplex_homotopyEquiv_norm_sq_sub_toLp_affineZeroLocus hp
  exact ⟨X, _, ‹_›, ‹_›, he, hempty⟩

/-- Every smooth affine complete intersection in `ℂ^σ` has CW type. Stated explicitly because the
implicit-function `ChartedSpace` structure on `affineZeroLocus p` depends on `hp` rather than being
a global typeclass instance. -/
theorem cwType_affineZeroLocus {σ : Type u} {ι : Type*} [Fintype σ] [_root_.Finite ι]
    {p : ι → MvPolynomial σ ℂ}
    (hp : ∀ x ∈ affineZeroLocus p, Function.Surjective (jacobiMatrixAt p x).mulVec) :
    CWType (affineZeroLocus p) := by
  let _ := Fintype.ofFinite ι
  obtain ⟨X, _, _, _, ⟨e⟩, -⟩ := exists_cwComplex_homotopyEquiv_affineZeroLocus hp
  exact (e.trans (Homeomorph.Set.univ X).symm.toHomotopyEquiv).cwType

end AffineZeroLocus

/-! ### Checks -/

section Checks

open MvPolynomial

/-- **Check: closed holomorphic embeddings into `ℂᴺ` (Milnor's Theorem 7.2).** A complex manifold
modelled on `Fin n → ℂ` admitting a smooth holomorphic immersion into `Fin N → ℂ` which is a closed
topological embedding has a Hausdorff CW homotopy model with no cells above dimension `n`. -/
example {n N : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (Fin n → ℂ) M]
    [IsManifold 𝓘(ℂ, Fin n → ℂ) ∞ M] [T2Space M] {i : M → Fin N → ℂ}
    (hi : Manifold.IsImmersion 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin N → ℂ) ∞ i)
    (hclosed : IsClosedEmbedding i) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      Nonempty (M ≃ₕ X) ∧ ∀ k, n < k → IsEmpty (cell (univ : Set X) k) := by
  simpa only [Module.finrank_fin_fun] using
    hi.exists_cwComplex_homotopyEquiv_of_isClosedEmbedding hclosed

/-- **Check: chartwise `q`-positive Levi exhaustions.** A complex `n`-manifold carrying a smooth
proper bounded-below exhaustion whose coordinate expression in a holomorphic chart around each point
is strongly `q`-pseudoconvex has a Hausdorff CW homotopy model with no cells above `n + q`. -/
example {n q : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (Fin n → ℂ) M]
    [IsManifold 𝓘(ℂ, Fin n → ℂ) ∞ M] [T2Space M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ) ∞ f) (hp : IsProperMap f) (hbdd : BddBelow (range f))
    (hlevi : ∀ x : M, ∃ e ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin n → ℂ) 2 M,
      x ∈ e.source ∧ IsStronglyPseudoconvexAt q (f ∘ e.symm) (e x)) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      Nonempty (M ≃ₕ X) ∧ ∀ k, n + q < k → IsEmpty (cell (univ : Set X) k) := by
  have : IsManifold 𝓘(ℂ, Fin n → ℂ) 2 M := .of_le (n := ∞) (by norm_cast)
  have hq (x : M) : IsManifoldStronglyPseudoconvexAt (Fin n → ℂ) q f x := by
    obtain ⟨e, he, hx, hxe⟩ := hlevi x
    exact (isManifoldStronglyPseudoconvexAt_iff_of_mem_maximalAtlas he hx
      ((hf.of_le (by norm_cast)).contMDiffAt)).2 hxe
  simpa only [Module.finrank_fin_fun] using
    exists_cwComplex_homotopyEquiv_of_isProperMap_of_isManifoldStronglyPseudoconvexAt hf hp hbdd hq

/-- **Check: the smooth affine hyperbola `{z₀ z₁ - 1 = 0} ⊆ ℂ²` has a 1-dimensional CW model.** At
every common zero of `X₀ X₁ - 1` in `ℂ²`, the partial derivative `∂(X₀ X₁ - 1)/∂X₀ = z₁` is
nonzero, so the Jacobian is surjective and `affineZeroLocus` has a Hausdorff CW model with no cells
above dimension `2 - 1 = 1`. -/
example :
    let p : Unit → MvPolynomial (Fin 2) ℂ := fun _ ↦ MvPolynomial.X 0 * MvPolynomial.X 1 - 1
    ∃ (X : Type) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      Nonempty (affineZeroLocus p ≃ₕ X) ∧ ∀ k, 1 < k → IsEmpty (cell (univ : Set X) k) := by
  intro p
  have hp : ∀ x ∈ affineZeroLocus p, Function.Surjective (jacobiMatrixAt p x).mulVec := by
    intro x hx
    rw [mulVec_surjective_jacobiMatrixAt_iff_exists_eval_pderiv_ne_zero]
    refine ⟨0, ?_⟩
    have hx0 : x 0 * x 1 - 1 = 0 := by simpa [p] using mem_affineZeroLocus.1 hx ()
    have hx1 : x 1 ≠ 0 := fun h0 ↦ by simp [h0] at hx0
    simpa [p, pderiv_mul, pderiv_X] using hx1
  simpa using exists_cwComplex_homotopyEquiv_affineZeroLocus hp

end Checks

end TauCeti
