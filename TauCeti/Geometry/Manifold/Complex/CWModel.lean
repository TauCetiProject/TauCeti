/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Immersion
public import TauCeti.Geometry.Manifold.Complex.Analytic
public import TauCeti.Geometry.Manifold.Complex.Pseudoconvex.Morse
public import TauCeti.Geometry.Manifold.Morse.CWModel.Proper
public import TauCeti.Geometry.Manifold.Morse.CWModel.Relative
public import TauCeti.Geometry.Manifold.RegularValue.Polynomial
import Mathlib.Analysis.InnerProductSpace.PiL2
import TauCeti.AlgebraicTopology.Cellular.Dimension
import TauCeti.Geometry.Manifold.Immersion.Basic
import TauCeti.Topology.CWComplex.Classical.Finite
import TauCeti.Topology.Maps.Proper.Basic

/-!
# CW homotopy models of pseudoconvex complex manifolds and holomorphic immersions

On a boundaryless Hausdorff complex manifold `M` of complex dimension `n`, a real Morse function
which is strongly `q`-pseudoconvex at its critical points has real Morse index at most `n + q` at
every critical point (`TauCeti.IsManifoldStronglyPseudoconvexAt.manifoldMorseIndex_le`). Feeding
this index bound into the CW model of a proper bounded-below Morse function
(`TauCeti.IsMorse.exists_cwComplex_subcomplex_homotopyEquiv_of_manifoldMorseIndex_le`) upgrades the
homological Andreotti–Frankel vanishing theorems of `SublevelHomology` and `ExhaustionHomology` to
genuine homotopy equivalences with finite-dimensional Hausdorff CW complexes.

## CW type of complex manifolds

* `TauCeti.ComplexManifold.cwType`, `TauCeti.ComplexManifold.cwType_of_isProperMap`, and
  `TauCeti.ComplexManifold.cwType_of_isClosedEmbedding`: CW type of sigma-compact `C^n` (`n ≠ 0`)
  complex manifolds and of complex manifolds admitting proper maps or closed embeddings.

## Pseudoconvex Morse and smooth exhaustions

When a proper bounded-below Morse function `f : M → ℝ` is strongly `q`-pseudoconvex at its critical
points, `M` admits a regular exhaustion `a 0 < a 1 < ⋯` and a finite-dimensional Hausdorff CW
homotopy model `X ≃ₕ M` exhausted by finite CW subcomplexes `W k ≃ₕ {f ≤ a k}`, with `m`-cells
corresponding globally and at each stage to the critical points of index `m`, and with no cells in
dimensions strictly above `n + q`
(`TauCeti.IsMorse.exists_cwComplex_subcomplex_homotopyEquiv_of_isManifoldStronglyPseudoconvexAt`,
`TauCeti.IsMorse.exists_cwComplex_homotopyEquiv_of_isManifoldStronglyPseudoconvexAt`), together with
finite CW models of compact regular bands and sublevels (in `TauCeti.IsMorse`:
`exists_finite_cwComplex_extension_homotopyEquiv_sublevel_of_isManifoldStronglyPseudoconvexAt`,
`exists_finite_cwComplex_homotopyEquiv_sublevel_of_isManifoldStronglyPseudoconvexAt`, and
`exists_finite_cwComplex_homotopyEquiv_sublevel_of_isManifoldStrictlyPlurisubharmonicAt`).
Across any compact regular band `f⁻¹[a, b]`, the Morse polynomial identity of `(M_b, M_a)` holds
already in every degree `m ≥ n + q` rather than only above the real dimension `2n`, with quotient
coefficients equal to the cellular differential ranks of an auxiliary finite relative CW complex
`(W, B)` without relative cells above dimension `n + q`
(`IsMorse.exists_relCWComplex_sum_range_monomial_sublevelPair_of_isManifoldStronglyPseudoconvexAt`);
the corresponding truncated Euler equality lives in `SublevelHomology`.

When `f : M → ℝ` is smooth, proper, bounded below, and everywhere strongly `q`-pseudoconvex —
without assuming `f` is Morse — strong-Whitney Morse perturbation
(`TauCeti.exists_isMorse_isProperMap_bddBelow_isManifoldStronglyPseudoconvexAt_sub_compl`) produces
a smooth proper bounded-below strongly `q`-pseudoconvex Morse exhaustion `g` within uniform `C⁰`
distance `1` of `f` (agreeing with `f` near any closed set on which `f` is already Morse). The
sublevel-compatible CW exhaustion of `g` therefore has regular sublevels
`{g ≤ a k}` sandwiched between `{f ≤ a k - 1}` and `{f ≤ a k + 1}`, and `M` has the homotopy type
of a finite-dimensional Hausdorff CW complex with no cells above dimension `n + q`
(`TauCeti.exists_cwComplex_subcomplex_homotopyEquiv_of_isManifoldStronglyPseudoconvexAt_sub_compl`,
`TauCeti.exists_cwComplex_homotopyEquiv_of_isProperMap_of_isManifoldStronglyPseudoconvexAt`), and
above `n` in the strictly plurisubharmonic case `q = 0` without assuming `[FiniteDimensional ℂ E]`
(`TauCeti.exists_cwComplex_homotopyEquiv_of_isProperMap_of_isManifoldStrictlyPlurisubharmonicAt`).

## Proper holomorphic immersions and closed holomorphic embeddings

Along a proper holomorphic immersion `i : M → F` into a proper complex inner product space, there
exist a centre `z₀ : F`, a Morse squared distance `x ↦ ‖i x - z₀‖²`, regular squared-distance
values `a 0 < a 1 < ⋯`, and a finite-dimensional Hausdorff CW homotopy model exhausted by finite
subcomplexes `W k ≃ₕ {x | ‖i x - z₀‖² ≤ a k}` with no cells above dimension `n`
(`TauCeti.exists_cwComplex_subcomplex_homotopyEquiv_norm_sq_sub_comp`).
For an arbitrary proper complex normed target `F` (which need not carry an inner product) and a
source `M` modelled on any boundaryless complex model `I` over `E` (not assumed finite-dimensional
a priori), transporting the source along `TauCeti.BoundarylessModel.homeomorph I M` and choosing a
complex continuous linear equivalence `F ≃L[ℂ] EuclideanSpace ℂ (Fin (finrank ℂ F))` transfers the
immersion to a Euclidean target, while `exists_cwComplex_subcomplex_homotopyEquiv_norm_sq_sub_comp`
handles empty `M` via `PEmpty` and forces `E` to be finite-dimensional on nonempty `M` via the
injective derivative. Every Hausdorff complex manifold admitting a proper holomorphic immersion
into a proper complex normed space — and in particular every complex manifold admitting a closed
holomorphic embedding into a finite-dimensional complex normed space, where Hausdorffness of `M` is
itself inherited from the embedding — therefore has the homotopy type of a finite-dimensional
Hausdorff CW complex with no cells above its complex dimension `n`
(`TauCeti.exists_cwComplex_homotopyEquiv_of_isProperMap_holomorphic_immersion`,
`TauCeti.exists_cwComplex_homotopyEquiv_of_isClosedEmbedding`,
`Manifold.IsImmersion.exists_cwComplex_homotopyEquiv_of_isProperMap`,
`Manifold.IsImmersion.exists_cwComplex_homotopyEquiv_of_isClosedEmbedding`). Specializing to
polynomial equations gives the Andreotti–Frankel CW homotopy bound `|σ| - |ι|` (with compatible
sublevel subcomplex models and `CWType`) for any smooth affine complete intersection
`affineZeroLocus p ⊆ ℂ^σ` with surjective Jacobian
(`TauCeti.exists_cwComplex_subcomplex_homotopyEquiv_affineZeroLocus`,
`TauCeti.exists_cwComplex_homotopyEquiv_affineZeroLocus`, `TauCeti.cwType_affineZeroLocus`).

## Checks

* `ℂ`, products of complex manifolds, and general finite-dimensional complex normed spaces admit CW
  homotopy models of dimension at most their complex dimension (`0` when subsingleton).
* The smooth affine hyperbola `z₀ z₁ = 1` in `ℂ²` (`ℂ*`), `0`-dimensional affine zero loci, and
  exhaustion-independence of pseudoconvex CW models.
* Sharpness of properness / closedness on `ℂ² \ {0}` is recorded in
  `TauCeti/Examples/Geometry/Manifold/Complex/PuncturedSpace.lean`.

## References

* A. Andreotti and T. Frankel, *The Lefschetz theorem on hyperplane sections*, Annals of
  Mathematics (2) 69 (1959), 713–717.
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 3.5, Section 5, and Section 7, Theorems 7.1 and 7.2.
* R. Hain, *Notes on the Morse theory of complex manifolds*, Section 2.
-/

public section

noncomputable section

open CategoryTheory Filter Function Module MvPolynomial Set Topology Topology.RelCWComplex
open Polynomial (monomial X)
open scoped ContDiff ContinuousMap Manifold Polynomial

universe u

namespace TauCeti

/-! ### CW type of sigma-compact complex manifolds -/

namespace ComplexManifold

section CWType

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [TopologicalSpace H] {M : Type u} [TopologicalSpace M] [T2Space M]

variable (M) (I : ModelWithCorners ℂ E H) [I.Boundaryless] [ChartedSpace H M] in
/-- **Sigma-compact complex manifolds have CW type.** A sigma-compact Hausdorff manifold modelled on
a boundaryless complex model `I` over a finite-dimensional space, of class `C^n` for some `n ≠ 0`,
is homotopy equivalent to a CW complex. -/
theorem cwType [SigmaCompactSpace M] {n : ℕ∞ω} (hn : n ≠ 0) [h : IsManifold I n M] : CWType M :=
  have : FiniteDimensional ℝ E := .trans ℝ ℂ E
  have : IsManifold (I.restrictScalars ℝ) ∞ M :=
    I.isManifold_restrictScalars ℝ (h.of_ne_zero ∞ hn)
  CWType.of_isManifold M (I.restrictScalars ℝ)

omit [FiniteDimensional ℂ E] in
variable (I : ModelWithCorners ℂ E H) [I.Boundaryless] [ChartedSpace H M] in
/-- A Hausdorff manifold modelled on a boundaryless complex model `I`, of class `C^n` for some
`n ≠ 0`, admitting a proper map to a weakly locally compact sigma-compact space has CW type,
without a separate finite-dimensionality assumption on `E`. -/
theorem cwType_of_isProperMap {n : ℕ∞ω} (hn : n ≠ 0) [IsManifold I n M] {Y : Type*}
    [TopologicalSpace Y] [WeaklyLocallyCompactSpace Y] [SigmaCompactSpace Y] {f : M → Y}
    (hf : IsProperMap f) : CWType M := by
  rcases isEmpty_or_nonempty M with _ | _
  · exact (Homeomorph.empty : M ≃ₜ PEmpty.{u + 1}).cwType
  have := hf.weaklyLocallyCompactSpace
  have : FiniteDimensional ℂ E := FiniteDimensional.of_locallyCompact_manifold M I
  have := hf.sigmaCompactSpace
  exact cwType M I hn

omit [FiniteDimensional ℂ E] [T2Space M] in
variable (I : ModelWithCorners ℂ E H) [I.Boundaryless] [ChartedSpace H M] in
/-- A manifold modelled on a boundaryless complex model `I`, of class `C^n` for some `n ≠ 0`,
admitting a closed topological embedding into a weakly locally compact sigma-compact Hausdorff space
has CW type. -/
theorem cwType_of_isClosedEmbedding {n : ℕ∞ω} (hn : n ≠ 0) [IsManifold I n M] {Y : Type*}
    [TopologicalSpace Y] [T2Space Y] [WeaklyLocallyCompactSpace Y] [SigmaCompactSpace Y]
    {i : M → Y} (hi : IsClosedEmbedding i) : CWType M :=
  have : T2Space M := hi.isEmbedding.t2Space
  cwType_of_isProperMap I hn hi.isProperMap

end CWType

end ComplexManifold

/-! ### Strongly `q`-pseudoconvex Morse exhaustions and compact regular bands -/

namespace IsMorse

variable {E : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) 1 M] [T2Space M] {f : M → ℝ}

/-- **Extending finite CW models across a compact regular band of a strongly `q`-pseudoconvex Morse
function.** Let `f` be a real Morse function on a complex manifold of complex dimension `n`, and let
`a ≤ b` be regular values with compact band `f⁻¹[a, b]` such that `f` is strongly `q`-pseudoconvex
at every critical point in `f⁻¹(a, b]`. Any finite CW model `h : W ≃ₕ {f ≤ a}` with no cells above
dimension `n + q` extends along a closed cofibration `ι : C(W, W')` to a finite CW model
`h' : W' ≃ₕ {f ≤ b}` with one new `m`-cell per index-`m` critical point in `f⁻¹(a, b]` and no cells
above dimension `n + q`. -/
theorem
    exists_finite_cwComplex_extension_homotopyEquiv_sublevel_of_isManifoldStronglyPseudoconvexAt
    {q : ℕ} (hf : IsMorse 𝓘(ℝ, E) f) {a b : ℝ} (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (ha : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f a) (hb : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f b)
    (hq : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Ioc a b, IsManifoldStronglyPseudoconvexAt E q f x)
    (W : Type u) [TopologicalSpace W] [T2Space W] [CWComplex (univ : Set W)]
    [RelCWComplex.Finite (univ : Set W)] (h : W ≃ₕ {x | f x ≤ a})
    (hW : ∀ k, finrank ℂ E + q < k → IsEmpty (cell (univ : Set W) k)) :
    ∃ (W' : Type u) (_ : TopologicalSpace W') (_ : T2Space W') (_ : CWComplex (univ : Set W'))
      (ι : C(W, W')) (h' : W' ≃ₕ {x | f x ≤ b}),
      RelCWComplex.Finite (univ : Set W') ∧ IsClosedEmbedding ι ∧
      HasHomotopyExtensionProperty (range ι) ∧ (∀ w, (h' (ι w) : M) = h w) ∧
      (∀ k, finrank ℂ E + q < k → IsEmpty (cell (univ : Set W') k)) ∧
      ∃ e : ∀ m, cell (univ : Set W') m ≃ cell (univ : Set W) m ⊕
          ↥{x ∈ criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Ioc a b | manifoldMorseIndex 𝓘(ℝ, E) f x = m},
        ∀ m j x, map m ((e m).symm (.inl j)) x = ι (map m j x) := by
  have : FiniteDimensional ℝ E := .trans ℝ ℂ E
  have : IsManifold 𝓘(ℂ, E) ∞ M := IsManifold.of_ne_zero ∞ one_ne_zero ‹_›
  have : IsManifold 𝓘(ℝ, E) ∞ M := IsManifold.restrictScalars_of_ne_zero ∞ one_ne_zero ‹_›
  exact hf.exists_finite_cwComplex_extension_homotopyEquiv_sublevel_of_manifoldMorseIndex_le
    hab hcompact ha hb
    (fun x hx ↦ (hq x hx).manifoldMorseIndex_le_of_mem_criticalPoints (hf.contMDiff x) hx.1) W h hW

/-- **Finite CW model of a compact regular sublevel of a strongly `q`-pseudoconvex Morse function.**
If `b` is a regular value of a real Morse function `f` on a complex manifold of complex dimension
`n` with compact sublevel `{f ≤ b}` in which `f` is strongly `q`-pseudoconvex at every critical
point, then `{f ≤ b}` is homotopy equivalent to a finite Hausdorff CW complex whose `m`-cells
correspond to the critical points of `f` in `{f ≤ b}` of index `m` and which has no cells above
dimension `n + q`. -/
theorem exists_finite_cwComplex_homotopyEquiv_sublevel_of_isManifoldStronglyPseudoconvexAt
    {q : ℕ} (hf : IsMorse 𝓘(ℝ, E) f) {b : ℝ} (hcompact : IsCompact {x | f x ≤ b})
    (hb : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f b)
    (hq : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f, f x ≤ b → IsManifoldStronglyPseudoconvexAt E q f x) :
    ∃ (W : Type u) (_ : TopologicalSpace W) (_ : T2Space W) (_ : CWComplex (univ : Set W)),
      RelCWComplex.Finite (univ : Set W) ∧ Nonempty (W ≃ₕ {x | f x ≤ b}) ∧
      (∀ k, finrank ℂ E + q < k → IsEmpty (cell (univ : Set W) k)) ∧
      ∀ m, Nonempty (cell (univ : Set W) m ≃
        ↥{x ∈ criticalPoints 𝓘(ℝ, E) f ∩ {x | f x ≤ b} | manifoldMorseIndex 𝓘(ℝ, E) f x = m}) := by
  have : FiniteDimensional ℝ E := .trans ℝ ℂ E
  have : IsManifold 𝓘(ℂ, E) ∞ M := IsManifold.of_ne_zero ∞ one_ne_zero ‹_›
  have : IsManifold 𝓘(ℝ, E) ∞ M := IsManifold.restrictScalars_of_ne_zero ∞ one_ne_zero ‹_›
  exact hf.exists_finite_cwComplex_homotopyEquiv_sublevel_of_manifoldMorseIndex_le hcompact hb
    fun x hx hxb ↦ (hq x hx hxb).manifoldMorseIndex_le_of_mem_criticalPoints (hf.contMDiff x) hx

omit [FiniteDimensional ℂ E] in
/-- **Finite CW model of a compact regular sublevel of a strictly plurisubharmonic Morse function.**
No separate finite-dimensionality assumption on the complex model space `E` is needed. -/
theorem exists_finite_cwComplex_homotopyEquiv_sublevel_of_isManifoldStrictlyPlurisubharmonicAt
    (hf : IsMorse 𝓘(ℝ, E) f) {b : ℝ} (hcompact : IsCompact {x | f x ≤ b})
    (hb : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f b)
    (hpsh : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f, f x ≤ b → IsManifoldStrictlyPlurisubharmonicAt E f x) :
    ∃ (W : Type u) (_ : TopologicalSpace W) (_ : T2Space W) (_ : CWComplex (univ : Set W)),
      RelCWComplex.Finite (univ : Set W) ∧ Nonempty (W ≃ₕ {x | f x ≤ b}) ∧
      (∀ k, finrank ℂ E < k → IsEmpty (cell (univ : Set W) k)) ∧
      ∀ m, Nonempty (cell (univ : Set W) m ≃
        ↥{x ∈ criticalPoints 𝓘(ℝ, E) f ∩ {x | f x ≤ b} | manifoldMorseIndex 𝓘(ℝ, E) f x = m}) := by
  rcases isEmpty_or_nonempty {x | f x ≤ b} with hEmpty | _
  · have (m : ℕ) : IsEmpty ↥{x ∈ criticalPoints 𝓘(ℝ, E) f ∩ {x | f x ≤ b} |
        manifoldMorseIndex 𝓘(ℝ, E) f x = m} := ⟨fun ⟨x, hx, _⟩ ↦ hEmpty.false ⟨x, hx.2⟩⟩
    exact ⟨PEmpty.{u + 1}, _, inferInstance, inferInstance, inferInstance,
      ⟨Homeomorph.empty.toHomotopyEquiv⟩, fun _ _ ↦ inferInstance,
      fun _ ↦ ⟨Equiv.equivOfIsEmpty _ _⟩⟩
  have : FiniteDimensional ℝ E :=
    finiteDimensional_of_isCompact_sublevel hf.contMDiff.continuous hcompact hb
  have : FiniteDimensional ℂ E := Module.Finite.of_restrictScalars_finite ℝ ℂ E
  simpa only [add_zero] using
    hf.exists_finite_cwComplex_homotopyEquiv_sublevel_of_isManifoldStronglyPseudoconvexAt (q := 0)
      hcompact hb fun x hx hxb ↦ (hpsh x hx hxb).isManifoldStronglyPseudoconvexAt 0

/-- **Sublevel-compatible CW exhaustion of a strongly `q`-pseudoconvex Morse function.** Let `f` be
a proper, bounded-below real Morse function on a Hausdorff complex manifold `M` of complex dimension
`n`, strongly `q`-pseudoconvex at every critical point. Then `M` admits a strictly increasing
regular exhaustion `a 0 < a 1 < ⋯` and a finite-dimensional Hausdorff CW homotopy model `X ≃ₕ M`
exhausted by finite CW subcomplexes `W k ≃ₕ {f ≤ a k}`, whose `m`-cells globally and at each stage
correspond to the critical points of index `m`, with no cells in dimensions strictly above
`n + q`. -/
theorem exists_cwComplex_subcomplex_homotopyEquiv_of_isManifoldStronglyPseudoconvexAt {q : ℕ}
    (hf : IsMorse 𝓘(ℝ, E) f) (hp : IsProperMap f) (hbdd : BddBelow (range f))
    (hq : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f, IsManifoldStronglyPseudoconvexAt E q f x) :
    ∃ (a : ℕ → ℝ) (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X)
      (_ : CWComplex (univ : Set X)) (W : ℕ → CWComplex.Subcomplex (univ : Set X))
      (h : X ≃ₕ M) (hW : ∀ k, (W k : Set X) ≃ₕ {x | f x ≤ a k}),
      StrictMono a ∧ Tendsto a atTop atTop ∧ (∀ x, a 0 < f x) ∧
      (∀ k, IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f (a k)) ∧ Monotone W ∧
      (W 0 : Set X) = ∅ ∧ (⋃ k, (W k : Set X)) = univ ∧
      (∀ k, RelCWComplex.Finite (W k : Set X)) ∧
      RelCWComplex.FiniteDimensional (univ : Set X) ∧
      (∀ k (x : (W k : Set X)), (hW k x : M) = h x) ∧
      (∀ k, MapsTo h.symm {x | f x ≤ a k} (W k)) ∧
      (∀ m, Nonempty (cell (univ : Set X) m ≃
        ↥{x ∈ criticalPoints 𝓘(ℝ, E) f | manifoldMorseIndex 𝓘(ℝ, E) f x = m})) ∧
      (∀ k m, Nonempty (cell (W k : Set X) m ≃
        ↥{x ∈ criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Iic (a k) |
          manifoldMorseIndex 𝓘(ℝ, E) f x = m})) ∧
      (∀ m, finrank ℂ E + q < m → IsEmpty (cell (univ : Set X) m)) ∧
      ∀ k m, finrank ℂ E + q < m → IsEmpty (cell (W k : Set X) m) := by
  have : FiniteDimensional ℝ E := .trans ℝ ℂ E
  have : IsManifold 𝓘(ℂ, E) ∞ M := IsManifold.of_ne_zero ∞ one_ne_zero ‹_›
  have : IsManifold 𝓘(ℝ, E) ∞ M := IsManifold.restrictScalars_of_ne_zero ∞ one_ne_zero ‹_›
  exact hf.exists_cwComplex_subcomplex_homotopyEquiv_of_manifoldMorseIndex_le hp hbdd
    fun x hx ↦ (hq x hx).manifoldMorseIndex_le_of_mem_criticalPoints (hf.contMDiff x) hx

/-- **CW homotopy model of a strongly `q`-pseudoconvex Morse exhaustion.** If `f : M → ℝ` is a
proper, bounded-below Morse function on a Hausdorff complex manifold `M` of complex dimension `n`
which is strongly `q`-pseudoconvex at every critical point, then `M` is homotopy equivalent to a
finite-dimensional Hausdorff CW complex whose `m`-cells correspond to the critical points of `f` of
index `m`, with no cells in dimensions strictly above `n + q`. -/
theorem exists_cwComplex_homotopyEquiv_of_isManifoldStronglyPseudoconvexAt {q : ℕ}
    (hf : IsMorse 𝓘(ℝ, E) f) (hp : IsProperMap f) (hbdd : BddBelow (range f))
    (hq : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f, IsManifoldStronglyPseudoconvexAt E q f x) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      RelCWComplex.FiniteDimensional (univ : Set X) ∧ Nonempty (M ≃ₕ X) ∧
      (∀ m, Nonempty (cell (univ : Set X) m ≃
        ↥{x ∈ criticalPoints 𝓘(ℝ, E) f | manifoldMorseIndex 𝓘(ℝ, E) f x = m})) ∧
      ∀ m, finrank ℂ E + q < m → IsEmpty (cell (univ : Set X) m) := by
  obtain ⟨_, X, instTop, instT2, instCW, _, h, _, -, -, -, -, -, -, -, -, hfd, -, -, hcell, -,
      hempty, -⟩ :=
    hf.exists_cwComplex_subcomplex_homotopyEquiv_of_isManifoldStronglyPseudoconvexAt hp hbdd hq
  exact ⟨X, instTop, instT2, instCW, hfd, ⟨h.symm⟩, hcell, hempty⟩

omit [FiniteDimensional ℂ E] in
/-- **CW homotopy model of a strictly plurisubharmonic Morse exhaustion.** If `f : M → ℝ` is a
proper, bounded-below Morse function on a Hausdorff complex manifold `M` of complex dimension `n`
which is strictly plurisubharmonic at every critical point, then `M` is homotopy equivalent to a
finite-dimensional Hausdorff CW complex whose `m`-cells correspond to the critical points of `f` of
index `m`, with no cells in dimensions strictly above `n`. No separate finite-dimensionality
assumption on `E` is needed. -/
theorem exists_cwComplex_homotopyEquiv_of_isManifoldStrictlyPlurisubharmonicAt
    (hf : IsMorse 𝓘(ℝ, E) f) (hp : IsProperMap f) (hbdd : BddBelow (range f))
    (hpos : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f, IsManifoldStrictlyPlurisubharmonicAt E f x) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      RelCWComplex.FiniteDimensional (univ : Set X) ∧ Nonempty (M ≃ₕ X) ∧
      (∀ m, Nonempty (cell (univ : Set X) m ≃
        ↥{x ∈ criticalPoints 𝓘(ℝ, E) f | manifoldMorseIndex 𝓘(ℝ, E) f x = m})) ∧
      ∀ m, finrank ℂ E < m → IsEmpty (cell (univ : Set X) m) := by
  rcases isEmpty_or_nonempty M with _ | _
  · exact ⟨PEmpty.{u + 1}, _, inferInstance, inferInstance,
      RelCWComplex.finiteDimensional_of_isEmpty_cell_gt _ (d := 0) fun _ _ ↦ inferInstance,
      ⟨Homeomorph.empty.toHomotopyEquiv⟩, fun _ ↦ ⟨Equiv.equivOfIsEmpty _ _⟩,
      fun _ _ ↦ inferInstance⟩
  have := hp.weaklyLocallyCompactSpace
  have : FiniteDimensional ℂ E := FiniteDimensional.of_locallyCompact_manifold M 𝓘(ℂ, E)
  simpa only [add_zero] using
    hf.exists_cwComplex_homotopyEquiv_of_isManifoldStronglyPseudoconvexAt (q := 0) hp hbdd
      fun x hx ↦ (hpos x hx).isManifoldStronglyPseudoconvexAt 0

/-- **Morse polynomial identity of a strongly `q`-pseudoconvex regular band, with cellular
coefficients.** Let `f` be a real Morse function on a Hausdorff complex manifold `M` of complex
dimension `n`, and let `a ≤ b` be regular values with compact band `f⁻¹[a, b]` such that `f` is
strongly `q`-pseudoconvex at every critical point in `(a, b]`. Then there is a finite relative CW
complex `(W, B)` without relative cells above dimension `n + q`, whose relative `m`-cells
correspond to the critical points of index `m` in `(a, b]`, such that the Morse polynomial identity
of `(M_b, M_a)` holds already in every degree `m ≥ n + q`, with quotient coefficients equal to the
ranks of the cellular differentials of `(W, B)`. -/
theorem exists_relCWComplex_sum_range_monomial_sublevelPair_of_isManifoldStronglyPseudoconvexAt
    {q : ℕ} (hf : IsMorse 𝓘(ℝ, E) f) {a b : ℝ} (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (ha : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f a) (hb : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f b)
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
            (1 + Polynomial.X) * ∑ i ∈ Finset.range m, monomial i (finrank k
              (LinearMap.range ((cellularChainComplex (univ : Set W) V).d (i + 1) i).hom)) := by
  have : FiniteDimensional ℝ E := .trans ℝ ℂ E
  have : IsManifold 𝓘(ℂ, E) ∞ M := IsManifold.of_ne_zero ∞ one_ne_zero ‹_›
  have : IsManifold 𝓘(ℝ, E) ∞ M := IsManifold.restrictScalars_of_ne_zero ∞ one_ne_zero ‹_›
  exact hf.exists_relCWComplex_sum_range_monomial_sublevelPair_eq_add_mul_of_manifoldMorseIndex_le
    hab hcompact ha hb fun x hx ↦
      (hq x hx).manifoldMorseIndex_le_of_mem_criticalPoints (hf.contMDiff x) hx.1

end IsMorse

/-! ### Smooth (possibly degenerate) strongly `q`-pseudoconvex exhaustions -/

section PseudoconvexExhaustion

variable {E : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) 1 M] [T2Space M]

/-- **Relative perturbed CW exhaustion of a smooth strongly `q`-pseudoconvex exhaustion.** Let
`f : M → ℝ` be a smooth, proper, bounded-below, everywhere strongly `q`-pseudoconvex function on a
Hausdorff complex manifold `M` of complex dimension `n`, already Morse on a closed set `C`. Then
there exist a smooth proper bounded-below strongly `q`-pseudoconvex Morse exhaustion `g` within
`C⁰` distance `1` of `f` (agreeing with `f` near `C`), a regular exhaustion `a 0 < a 1 < ⋯` for
`g`, and a finite-dimensional Hausdorff CW homotopy model `h : X ≃ₕ M` exhausted by finite CW
subcomplexes `W k ≃ₕ {g ≤ a k}` with `{f ≤ a k - 1} ⊆ {g ≤ a k} ⊆ {f ≤ a k + 1}`,
`MapsTo h.symm {f ≤ a k - 1} (W k)`, and no cells in dimensions strictly above `n + q`. -/
theorem
    exists_cwComplex_subcomplex_homotopyEquiv_of_isManifoldStronglyPseudoconvexAt_sub_compl
    {q : ℕ} {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f) (hp : IsProperMap f)
    (hbdd : BddBelow (range f)) (hq : ∀ x, IsManifoldStronglyPseudoconvexAt E q f x)
    {C : Set M} (hC : IsClosed C) (hfC : IsMorseOn 𝓘(ℝ, E) f C) :
    ∃ (g : C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯) (a : ℕ → ℝ) (X : Type u) (_ : TopologicalSpace X)
      (_ : T2Space X) (_ : CWComplex (univ : Set X))
      (W : ℕ → CWComplex.Subcomplex (univ : Set X))
      (h : X ≃ₕ M) (hW : ∀ k, (W k : Set X) ≃ₕ {x | g x ≤ a k}),
      IsMorse 𝓘(ℝ, E) g ∧ IsProperMap g ∧ BddBelow (range g) ∧
      (∀ x, IsManifoldStronglyPseudoconvexAt E q g x) ∧
      (∀ x, |g x - f x| < 1) ∧ tsupport (fun x ↦ g x - f x) ⊆ Cᶜ ∧
      StrictMono a ∧ Tendsto a atTop atTop ∧
      (∀ k, IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) g (a k)) ∧ Monotone W ∧
      (W 0 : Set X) = ∅ ∧ (⋃ k, (W k : Set X)) = univ ∧
      (∀ k, RelCWComplex.Finite (W k : Set X)) ∧
      RelCWComplex.FiniteDimensional (univ : Set X) ∧
      (∀ k (x : (W k : Set X)), (hW k x : M) = h x) ∧
      (∀ k, {x | f x ≤ a k - 1} ⊆ {x | g x ≤ a k}) ∧
      (∀ k, {x | g x ≤ a k} ⊆ {x | f x ≤ a k + 1}) ∧
      (∀ k, MapsTo h.symm {x | f x ≤ a k - 1} (W k)) ∧
      (∀ m, Nonempty (cell (univ : Set X) m ≃
        ↥{x ∈ criticalPoints 𝓘(ℝ, E) g | manifoldMorseIndex 𝓘(ℝ, E) g x = m})) ∧
      (∀ m, finrank ℂ E + q < m → IsEmpty (cell (univ : Set X) m)) ∧
      ∀ k m, finrank ℂ E + q < m → IsEmpty (cell (W k : Set X) m) := by
  have : IsManifold 𝓘(ℂ, E) ∞ M := IsManifold.of_ne_zero ∞ one_ne_zero ‹_›
  obtain ⟨g, hgm, hgp, hg_bdd, hg_pos, -, hgf, hgs⟩ :=
    exists_isMorse_isProperMap_bddBelow_isManifoldStronglyPseudoconvexAt_sub_compl hf hp hbdd hq
      hC hfC
  obtain ⟨a, X, instTop, instT2, instCW, W, h, hW, hmono, htop, -, hreg, hWmono, hW0, hWuniv,
      hWfin, hfd, hhW, hsymm, hcell, -, hempty, hWempty⟩ :=
    hgm.exists_cwComplex_subcomplex_homotopyEquiv_of_isManifoldStronglyPseudoconvexAt hgp hg_bdd
      fun x _ ↦ hg_pos x
  have hsub₁ (k : ℕ) : {x | f x ≤ a k - 1} ⊆ {x | g x ≤ a k} :=
    ofPred_subset_ofPred.2 fun x hx ↦ by linarith [(abs_lt.1 (hgf x)).2]
  have hsub₂ (k : ℕ) : {x | g x ≤ a k} ⊆ {x | f x ≤ a k + 1} :=
    ofPred_subset_ofPred.2 fun x hx ↦ by linarith [(abs_lt.1 (hgf x)).1]
  exact ⟨g, a, X, instTop, instT2, instCW, W, h, hW, hgm, hgp, hg_bdd, hg_pos, hgf, hgs, hmono,
    htop, hreg, hWmono, hW0, hWuniv, hWfin, hfd, hhW, hsub₁, hsub₂,
    fun k ↦ (hsymm k).mono_left (hsub₁ k), hcell, hempty, hWempty⟩

/-- **CW homotopy model of a smooth strongly `q`-pseudoconvex exhaustion** (Andreotti–Frankel;
Hain). Every Hausdorff complex manifold `M` of complex dimension `n` carrying a smooth, proper,
bounded-below, everywhere strongly `q`-pseudoconvex function `f : M → ℝ` (not assumed to be Morse)
is homotopy equivalent to a finite-dimensional Hausdorff CW complex with no cells in dimensions
strictly above `n + q`. -/
theorem exists_cwComplex_homotopyEquiv_of_isProperMap_of_isManifoldStronglyPseudoconvexAt
    {q : ℕ} {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f) (hp : IsProperMap f)
    (hbdd : BddBelow (range f)) (hq : ∀ x, IsManifoldStronglyPseudoconvexAt E q f x) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      RelCWComplex.FiniteDimensional (univ : Set X) ∧ Nonempty (M ≃ₕ X) ∧
      ∀ m, finrank ℂ E + q < m → IsEmpty (cell (univ : Set X) m) := by
  obtain ⟨_, _, X, instTop, instT2, instCW, _, h, _, -, -, -, -, -, -, -, -, -, -, -, -, -, hfd,
      -, -, -, -, -, hempty, -⟩ :=
    exists_cwComplex_subcomplex_homotopyEquiv_of_isManifoldStronglyPseudoconvexAt_sub_compl
      hf hp hbdd hq isClosed_empty isMorseOn_empty
  exact ⟨X, instTop, instT2, instCW, hfd, ⟨h.symm⟩, hempty⟩

omit [FiniteDimensional ℂ E] in
/-- **CW homotopy model of a smooth strictly plurisubharmonic exhaustion.** Every Hausdorff complex
manifold `M` of complex dimension `n` carrying a smooth, proper, bounded-below, everywhere strictly
plurisubharmonic function `f : M → ℝ` (for instance any Stein manifold) is homotopy equivalent to a
finite-dimensional Hausdorff CW complex with no cells in dimensions strictly above `n`. No separate
finite-dimensionality assumption on `E` is needed. -/
theorem exists_cwComplex_homotopyEquiv_of_isProperMap_of_isManifoldStrictlyPlurisubharmonicAt
    {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f) (hp : IsProperMap f)
    (hbdd : BddBelow (range f)) (hpos : ∀ x, IsManifoldStrictlyPlurisubharmonicAt E f x) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      RelCWComplex.FiniteDimensional (univ : Set X) ∧ Nonempty (M ≃ₕ X) ∧
      ∀ m, finrank ℂ E < m → IsEmpty (cell (univ : Set X) m) := by
  rcases isEmpty_or_nonempty M with _ | _
  · exact ⟨PEmpty.{u + 1}, _, inferInstance, inferInstance,
      RelCWComplex.finiteDimensional_of_isEmpty_cell_gt _ (d := 0) fun _ _ ↦ inferInstance,
      ⟨Homeomorph.empty.toHomotopyEquiv⟩, fun _ _ ↦ inferInstance⟩
  have := hp.weaklyLocallyCompactSpace
  have : FiniteDimensional ℂ E := FiniteDimensional.of_locallyCompact_manifold M 𝓘(ℂ, E)
  simpa only [add_zero] using
    exists_cwComplex_homotopyEquiv_of_isProperMap_of_isManifoldStronglyPseudoconvexAt (q := 0)
      hf hp hbdd fun x ↦ (hpos x).isManifoldStronglyPseudoconvexAt 0

end PseudoconvexExhaustion

/-! ### Proper holomorphic immersions, closed holomorphic embeddings, and affine zero loci -/

/-- **Squared-distance CW exhaustion along a proper holomorphic immersion.** Let `i : M → F` be a
proper holomorphic immersion from a Hausdorff complex manifold `M` into a proper complex inner
product space `F`. Then for some centre `z₀ : F` and regular squared-distance values
`a 0 < a 1 < ⋯` tending to infinity, `M` admits a finite-dimensional Hausdorff CW homotopy model
`X ≃ₕ M` exhausted by finite CW subcomplexes `W k ≃ₕ {x | ‖i x - z₀‖² ≤ a k}`, with `m`-cells
corresponding to the critical points of `x ↦ ‖i x - z₀‖²` of index `m`, and with no cells in
dimensions strictly above `finrank ℂ E`. -/
theorem exists_cwComplex_subcomplex_homotopyEquiv_norm_sq_sub_comp
    {E F : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [ProperSpace F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) 1 M] [T2Space M]
    {i : M → F} (hi : MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, F) i)
    (hinj : ∀ x, Injective (mvfderiv 𝓘(ℂ, E) i x)) (hip : IsProperMap i) :
    ∃ (z₀ : F) (a : ℕ → ℝ) (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X)
      (_ : CWComplex (univ : Set X)) (W : ℕ → CWComplex.Subcomplex (univ : Set X))
      (h : X ≃ₕ M) (hW : ∀ k, (W k : Set X) ≃ₕ {x | ‖i x - z₀‖ ^ 2 ≤ a k}),
      StrictMono a ∧ Tendsto a atTop atTop ∧
      (∀ k, IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) (fun x ↦ ‖i x - z₀‖ ^ 2) (a k)) ∧ Monotone W ∧
      (W 0 : Set X) = ∅ ∧ (⋃ k, (W k : Set X)) = univ ∧
      (∀ k, RelCWComplex.Finite (W k : Set X)) ∧
      RelCWComplex.FiniteDimensional (univ : Set X) ∧
      (∀ k (x : (W k : Set X)), (hW k x : M) = h x) ∧
      (∀ k, MapsTo h.symm {x | ‖i x - z₀‖ ^ 2 ≤ a k} (W k)) ∧
      (∀ m, Nonempty (cell (univ : Set X) m ≃
        ↥{x ∈ criticalPoints 𝓘(ℝ, E) (fun y ↦ ‖i y - z₀‖ ^ 2) |
          manifoldMorseIndex 𝓘(ℝ, E) (fun y ↦ ‖i y - z₀‖ ^ 2) x = m})) ∧
      (∀ k m, Nonempty (cell (W k : Set X) m ≃
        ↥{x ∈ criticalPoints 𝓘(ℝ, E) (fun y ↦ ‖i y - z₀‖ ^ 2) ∩
            {x | ‖i x - z₀‖ ^ 2 ≤ a k} |
          manifoldMorseIndex 𝓘(ℝ, E) (fun y ↦ ‖i y - z₀‖ ^ 2) x = m})) ∧
      (∀ m, finrank ℂ E < m → IsEmpty (cell (univ : Set X) m)) ∧
      ∀ k m, finrank ℂ E < m → IsEmpty (cell (W k : Set X) m) := by
  rcases isEmpty_or_nonempty M with hM | ⟨⟨x₀⟩⟩
  · -- When `M` is empty, `PEmpty` with constant empty subcomplexes witnesses every conjunct.
    let W : ℕ → CWComplex.Subcomplex (univ : Set PEmpty.{u + 1}) :=
      fun _ ↦ ⟨∅, fun _ ↦ ∅, isClosed_empty, by simp⟩
    have hempty (m : ℕ) : IsEmpty (cell (univ : Set PEmpty.{u + 1}) m) :=
      ⟨fun j ↦ PEmpty.elim (map m j 0)⟩
    have hWempty (k m : ℕ) : IsEmpty (cell (W k : Set PEmpty.{u + 1}) m) :=
      ⟨fun j ↦ PEmpty.elim (map m j 0)⟩
    have (k : ℕ) : IsEmpty {x : M | ‖i x - 0‖ ^ 2 ≤ (k : ℝ)} := ⟨fun x ↦ hM.elim x.val⟩
    refine ⟨0, Nat.cast, PEmpty.{u + 1}, inferInstance, inferInstance, inferInstance, W,
      Homeomorph.empty.toHomotopyEquiv, fun _ ↦ Homeomorph.empty.toHomotopyEquiv,
      Nat.strictMono_cast, tendsto_natCast_atTop_atTop,
      fun _ ↦ isRegularValue_iff.2 fun x ↦ hM.elim x, monotone_const, rfl,
      eq_univ_of_forall fun x ↦ PEmpty.elim x, fun k ↦ RelCWComplex.finite_of_finite_cells
        (have : IsEmpty (Σ n, cell (W k : Set PEmpty.{u + 1}) n) :=
          ⟨fun ⟨n, j⟩ ↦ (hWempty k n).elim j⟩
        inferInstance),
      RelCWComplex.finiteDimensional_of_isEmpty_cell_gt _ (d := 0) fun m _ ↦ hempty m,
      fun _ x ↦ PEmpty.elim x.val, fun _ x ↦ hM.elim x, fun m ↦ ⟨?_⟩, fun k m ↦ ⟨?_⟩,
      fun m _ ↦ hempty m, fun k m _ ↦ hWempty k m⟩
    · have : IsEmpty ↥{x ∈ criticalPoints 𝓘(ℝ, E) (fun y ↦ ‖i y - 0‖ ^ 2) |
          manifoldMorseIndex 𝓘(ℝ, E) (fun y ↦ ‖i y - 0‖ ^ 2) x = m} := ⟨fun x ↦ hM.elim x.val⟩
      exact Equiv.equivOfIsEmpty _ _
    · have : IsEmpty ↥{x ∈ criticalPoints 𝓘(ℝ, E) (fun y ↦ ‖i y - 0‖ ^ 2) ∩
          {x | ‖i x - 0‖ ^ 2 ≤ (k : ℝ)} |
          manifoldMorseIndex 𝓘(ℝ, E) (fun y ↦ ‖i y - 0‖ ^ 2) x = m} := ⟨fun x ↦ hM.elim x.val⟩
      exact Equiv.equivOfIsEmpty _ _
  · have : FiniteDimensional ℂ F := .of_locallyCompactSpace ℂ
    have : FiniteDimensional ℂ E :=
      Module.Finite.of_injective (mvfderiv 𝓘(ℂ, E) i x₀).toLinearMap (hinj x₀)
    have : FiniteDimensional ℝ E := .trans ℝ ℂ E
    have : IsManifold 𝓘(ℂ, E) ∞ M := IsManifold.of_ne_zero ∞ one_ne_zero ‹_›
    have : IsManifold 𝓘(ℝ, E) ∞ M := IsManifold.restrictScalars_of_ne_zero ∞ one_ne_zero ‹_›
    obtain ⟨z₀, hmorse, hprop, hbdd, hidx⟩ :=
      exists_isMorse_isProperMap_bddBelow_and_manifoldMorseIndex_norm_sq_sub_comp_le
        hi.contMDiff hinj hip
    obtain ⟨a, X, instTop, instT2, instCW, W, h, hW, hmono, htop, -, hreg, hWmono, hW0, hWuniv,
        hWfin, hfd, hhW, hsymm, hcell, hWcell, hempty, hWempty⟩ :=
      hmorse.exists_cwComplex_subcomplex_homotopyEquiv_of_manifoldMorseIndex_le hprop hbdd hidx
    exact ⟨z₀, a, X, instTop, instT2, instCW, W, h, hW, hmono, htop, hreg, hWmono, hW0, hWuniv,
      hWfin, hfd, hhW, hsymm, hcell, hWcell, hempty, hWempty⟩

section HolomorphicImmersionModel

variable {E H : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace H]
  {I : ModelWithCorners ℂ E H} [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] [T2Space M]

/-- **CW homotopy model along a proper holomorphic immersion** (Andreotti–Frankel; Milnor, Theorem
7.2). Let `i : M → F` be a proper holomorphic immersion from a Hausdorff manifold `M` modelled on
a boundaryless complex model `I` over `E` into a proper complex normed space `F` (no inner product
on `F`, finite-dimensionality of `E`, or second-countability of `M` is assumed). Then `M` is
homotopy equivalent to a finite-dimensional Hausdorff CW complex with no cells in dimensions
strictly above `finrank ℂ E`. -/
theorem exists_cwComplex_homotopyEquiv_of_isProperMap_holomorphic_immersion
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [ProperSpace F]
    {i : M → F} (hi : MDifferentiable I 𝓘(ℂ, F) i)
    (hinj : ∀ x, Injective (mvfderiv I i x)) (hip : IsProperMap i) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      RelCWComplex.FiniteDimensional (univ : Set X) ∧ Nonempty (M ≃ₕ X) ∧
      ∀ m, finrank ℂ E < m → IsEmpty (cell (univ : Set X) m) := by
  let hM := BoundarylessModel.homeomorph I M
  have : T2Space (BoundarylessModel I M) := hM.symm.isEmbedding.t2Space
  have : FiniteDimensional ℂ F := .of_locallyCompactSpace ℂ
  let e : F ≃L[ℂ] EuclideanSpace ℂ (Fin (finrank ℂ F)) :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
  let j : BoundarylessModel I M → EuclideanSpace ℂ (Fin (finrank ℂ F)) := (e ∘ i) ∘ hM.symm
  have hei : MDifferentiable I 𝓘(ℂ, EuclideanSpace ℂ (Fin (finrank ℂ F))) (e ∘ i) :=
    (e.contDiff.contMDiff.mdifferentiable one_ne_zero).comp hi
  have hj_diff : MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, EuclideanSpace ℂ (Fin (finrank ℂ F))) j :=
    fun x ↦ (BoundarylessModel.mdifferentiableAt_source_iff I 𝓘(ℂ, _) (e ∘ i) x).2 (hei _)
  have hj_inj : ∀ x, Injective (mvfderiv 𝓘(ℂ, E) j x) := fun x ↦ by
    rw [injective_mvfderiv_iff, BoundarylessModel.mfderiv_source I 𝓘(ℂ, _) (e ∘ i) x]
    have hein : Injective (mvfderiv I (e ∘ i) (hM.symm x)) := fun v w hvw ↦ by
      simp only [mvfderiv_comp_apply_of_differentiableAt e.differentiableAt (hi _),
        e.fderiv] at hvw
      exact hinj _ (e.injective hvw)
    exact ((injective_mvfderiv_iff.1 hein).comp
      (tangentSpaceCastModel I (hM.symm x)).symm.injective).comp
      (tangentSpaceCastModel 𝓘(ℂ, E) x).injective
  obtain ⟨_, _, X, instTop, instT2, instCW, _, h, _, -, -, -, -, -, -, -, hfd, -, -, -, -, hempty,
      -⟩ :=
    exists_cwComplex_subcomplex_homotopyEquiv_norm_sq_sub_comp hj_diff hj_inj
      ((e.toHomeomorph.isClosedEmbedding.isProperMap.comp hip).comp
        hM.symm.isClosedEmbedding.isProperMap)
  exact ⟨X, instTop, instT2, instCW, hfd, ⟨hM.toHomotopyEquiv.trans h.symm⟩, hempty⟩

omit [T2Space M] in
/-- **The closed holomorphic embedding CW theorem** (Andreotti–Frankel; Milnor, *Morse Theory*,
Theorem 7.2). Let `i : M → F` be a holomorphic immersion of a manifold `M` modelled on a
boundaryless complex model `I` over `E` into a finite-dimensional complex normed space `F` which
is a closed topological embedding. Then `M` is homotopy equivalent to a finite-dimensional Hausdorff
CW complex with no cells in dimensions strictly above its complex dimension `finrank ℂ E`. Neither
Hausdorffness of `M`, finite-dimensionality of `E`, nor an inner product on `F` need be assumed
separately. -/
theorem exists_cwComplex_homotopyEquiv_of_isClosedEmbedding
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    {i : M → F} (hi : MDifferentiable I 𝓘(ℂ, F) i)
    (hinj : ∀ x, Injective (mvfderiv I i x)) (hclosed : IsClosedEmbedding i) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      RelCWComplex.FiniteDimensional (univ : Set X) ∧ Nonempty (M ≃ₕ X) ∧
      ∀ m, finrank ℂ E < m → IsEmpty (cell (univ : Set X) m) := by
  have : FiniteDimensional ℝ F := .trans ℝ ℂ F
  have : ProperSpace F := FiniteDimensional.proper ℝ F
  have : T2Space M := hclosed.isEmbedding.t2Space
  exact exists_cwComplex_homotopyEquiv_of_isProperMap_holomorphic_immersion hi hinj
    hclosed.isProperMap

end HolomorphicImmersionModel

section AffineZeroLocus

/-- **Milnor's squared-distance CW exhaustion of a smooth affine complete intersection.** Let
`p : ι → MvPolynomial σ ℂ` be a finite polynomial family whose Jacobian matrix is surjective at
every point of `V = affineZeroLocus p`, so that `V` is a closed complex submanifold of `ℂ^σ` of
complex dimension `d = |σ| - |ι|`. Then for some Euclidean centre `a`, regular squared-distance
values `r 0 < r 1 < ⋯` tending to infinity, and finite-dimensional Hausdorff CW model `X ≃ₕ V`
exhausted by finite CW subcomplexes `W k ≃ₕ {y ∈ V | ‖toLp 2 y - a‖² ≤ r k}`, both `X` and each
`W k` have no cells above dimension `d`, and `m`-cells correspond to the index-`m` critical points
of `y ↦ ‖toLp 2 y - a‖²`. -/
theorem exists_cwComplex_subcomplex_homotopyEquiv_affineZeroLocus {σ : Type u} {ι : Type*}
    [Fintype σ] [Fintype ι] {p : ι → MvPolynomial σ ℂ}
    (hp : ∀ x ∈ affineZeroLocus p, Surjective (jacobiMatrixAt p x).mulVec) :
    letI := affineZeroLocusChartedSpace hp
    ∃ (a : EuclideanSpace ℂ σ) (r : ℕ → ℝ) (X : Type u) (_ : TopologicalSpace X)
      (_ : T2Space X) (_ : CWComplex (univ : Set X))
      (W : ℕ → CWComplex.Subcomplex (univ : Set X)) (h : X ≃ₕ affineZeroLocus p)
      (hW : ∀ k, (W k : Set X) ≃ₕ
        {y : affineZeroLocus p | ‖WithLp.toLp 2 (y : σ → ℂ) - a‖ ^ 2 ≤ r k}),
      StrictMono r ∧ Tendsto r atTop atTop ∧
      (∀ k, IsRegularValue 𝓘(ℝ, Fin (Fintype.card σ - Fintype.card ι) → ℂ) 𝓘(ℝ)
        (fun y : affineZeroLocus p ↦ ‖WithLp.toLp 2 (y : σ → ℂ) - a‖ ^ 2) (r k)) ∧
      Monotone W ∧ (W 0 : Set X) = ∅ ∧ (⋃ k, (W k : Set X)) = univ ∧
      (∀ k, RelCWComplex.Finite (W k : Set X)) ∧
      RelCWComplex.FiniteDimensional (univ : Set X) ∧
      (∀ k (x : (W k : Set X)), (hW k x : affineZeroLocus p) = h x) ∧
      (∀ k, MapsTo h.symm {y : affineZeroLocus p | ‖WithLp.toLp 2 (y : σ → ℂ) - a‖ ^ 2 ≤ r k}
        (W k)) ∧
      (∀ m, Nonempty (cell (univ : Set X) m ≃
        ↥{y ∈ criticalPoints 𝓘(ℝ, Fin (Fintype.card σ - Fintype.card ι) → ℂ)
            (fun z : affineZeroLocus p ↦ ‖WithLp.toLp 2 (z : σ → ℂ) - a‖ ^ 2) |
          manifoldMorseIndex 𝓘(ℝ, Fin (Fintype.card σ - Fintype.card ι) → ℂ)
            (fun z : affineZeroLocus p ↦ ‖WithLp.toLp 2 (z : σ → ℂ) - a‖ ^ 2) y = m})) ∧
      (∀ k m, Nonempty (cell (W k : Set X) m ≃
        ↥{y ∈ criticalPoints 𝓘(ℝ, Fin (Fintype.card σ - Fintype.card ι) → ℂ)
            (fun z : affineZeroLocus p ↦ ‖WithLp.toLp 2 (z : σ → ℂ) - a‖ ^ 2) ∩
            {y : affineZeroLocus p | ‖WithLp.toLp 2 (y : σ → ℂ) - a‖ ^ 2 ≤ r k} |
          manifoldMorseIndex 𝓘(ℝ, Fin (Fintype.card σ - Fintype.card ι) → ℂ)
            (fun z : affineZeroLocus p ↦ ‖WithLp.toLp 2 (z : σ → ℂ) - a‖ ^ 2) y = m})) ∧
      (∀ m, Fintype.card σ - Fintype.card ι < m → IsEmpty (cell (univ : Set X) m)) ∧
      ∀ k m, Fintype.card σ - Fintype.card ι < m → IsEmpty (cell (W k : Set X) m) := by
  let _ := affineZeroLocusChartedSpace hp
  have := isManifold_affineZeroLocus hp 1
  have hclosed : IsClosedEmbedding
      (fun y : affineZeroLocus p ↦ WithLp.toLp 2 (y : σ → ℂ)) :=
    (EuclideanSpace.equiv σ ℂ).symm.toHomeomorph.isClosedEmbedding.comp
      (isClosed_affineZeroLocus p).isClosedEmbedding_subtypeVal
  simpa only [Module.finrank_fin_fun] using
    exists_cwComplex_subcomplex_homotopyEquiv_norm_sq_sub_comp
      ((contMDiff_toLp_coe_affineZeroLocus hp 1).mdifferentiable one_ne_zero)
      (injective_mvfderiv_toLp_coe_affineZeroLocus hp) hclosed.isProperMap

/-- **CW homotopy model of a smooth affine complete intersection** (Andreotti–Frankel). Let
`affineZeroLocus p ⊆ ℂ^σ` be the common zero locus of a polynomial family `p : ι → ℂ[X_σ]` whose
Jacobian is surjective at every common zero, a smooth affine complex complete intersection of
dimension `|σ| - |ι|`. Then `affineZeroLocus p` is homotopy equivalent to a finite-dimensional
Hausdorff CW complex with no cells in dimensions strictly above `|σ| - |ι|`. -/
theorem exists_cwComplex_homotopyEquiv_affineZeroLocus {σ : Type u} {ι : Type*}
    [Fintype σ] [Fintype ι] {p : ι → MvPolynomial σ ℂ}
    (hp : ∀ x ∈ affineZeroLocus p, Surjective (jacobiMatrixAt p x).mulVec) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      RelCWComplex.FiniteDimensional (univ : Set X) ∧ Nonempty (affineZeroLocus p ≃ₕ X) ∧
      ∀ m, Fintype.card σ - Fintype.card ι < m → IsEmpty (cell (univ : Set X) m) := by
  obtain ⟨_, _, X, instTop, instT2, instCW, _, h, _, -, -, -, -, -, -, -, hfd, -, -, -, -, hempty,
      -⟩ :=
    exists_cwComplex_subcomplex_homotopyEquiv_affineZeroLocus hp
  exact ⟨X, instTop, instT2, instCW, hfd, ⟨h.symm⟩, hempty⟩

/-- Every smooth affine complete intersection over `ℂ` has CW type. -/
theorem cwType_affineZeroLocus {σ : Type u} {ι : Type*} [Fintype σ] [Finite ι]
    {p : ι → MvPolynomial σ ℂ}
    (hp : ∀ x ∈ affineZeroLocus p, Surjective (jacobiMatrixAt p x).mulVec) :
    CWType (affineZeroLocus p) := by
  let := Fintype.ofFinite ι
  obtain ⟨X, _, _, _, _, ⟨h⟩, -⟩ := exists_cwComplex_homotopyEquiv_affineZeroLocus hp
  exact h.cwType

end AffineZeroLocus

end TauCeti

namespace Manifold.IsImmersion

open Module Set Topology.RelCWComplex

/-- **CW homotopy model along a proper `C^r` (`r ≠ 0`) holomorphic immersion.** Every Hausdorff
manifold `M` modelled on a boundaryless complex model `I` over `E` admitting a proper `C^r`
(`r ≠ 0`) holomorphic immersion into a proper complex normed space is homotopy equivalent to a
finite-dimensional Hausdorff CW complex with no cells in dimensions strictly above `finrank ℂ E`.
Neither an inner product on the target, finite-dimensionality of `E`, nor a separate `IsManifold`
instance need be assumed. -/
theorem exists_cwComplex_homotopyEquiv_of_isProperMap
    {E H F : Type*} {M : Type u} {r : ℕ∞ω} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace H] {I : ModelWithCorners ℂ E H} [I.Boundaryless]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [ProperSpace F]
    [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    {i : M → F} (h : IsImmersion I 𝓘(ℂ, F) r i) (hr : r ≠ 0) (hip : IsProperMap i) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      RelCWComplex.FiniteDimensional (univ : Set X) ∧ Nonempty (M ≃ₕ X) ∧
      ∀ m, finrank ℂ E < m → IsEmpty (cell (univ : Set X) m) := by
  have : IsManifold I r M := h.isManifold
  have : IsManifold I 1 M := IsManifold.of_le (ENat.one_le_iff_ne_zero_withTop.2 hr)
  exact TauCeti.exists_cwComplex_homotopyEquiv_of_isProperMap_holomorphic_immersion
    (h.contMDiff.mdifferentiable hr)
    (fun x ↦ TauCeti.injective_mvfderiv_iff.2 (h.mfderiv_injective hr x)) hip

/-- **The closed holomorphic embedding CW theorem for `Manifold.IsImmersion`.** Every manifold `M`
modelled on a boundaryless complex model `I` over `E` admitting a `C^r` (`r ≠ 0`) holomorphic
immersion into a finite-dimensional complex normed space which is a closed topological embedding is
homotopy equivalent to a finite-dimensional Hausdorff CW complex with no cells in dimensions
strictly above `finrank ℂ E`. -/
theorem exists_cwComplex_homotopyEquiv_of_isClosedEmbedding
    {E H F : Type*} {M : Type u} {r : ℕ∞ω} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace H] {I : ModelWithCorners ℂ E H} [I.Boundaryless]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    [TopologicalSpace M] [ChartedSpace H M]
    {i : M → F} (h : IsImmersion I 𝓘(ℂ, F) r i) (hr : r ≠ 0)
    (hclosed : IsClosedEmbedding i) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      RelCWComplex.FiniteDimensional (univ : Set X) ∧ Nonempty (M ≃ₕ X) ∧
      ∀ m, finrank ℂ E < m → IsEmpty (cell (univ : Set X) m) := by
  have : FiniteDimensional ℝ F := .trans ℝ ℂ F
  have : ProperSpace F := FiniteDimensional.proper ℝ F
  have : T2Space M := hclosed.isEmbedding.t2Space
  exact h.exists_cwComplex_homotopyEquiv_of_isProperMap hr hclosed.isProperMap

end Manifold.IsImmersion

namespace TauCeti

/-! ### Checks -/

section Checks

open AlgebraicTopology CategoryTheory Limits

/-- **Check: finite-dimensional complex normed spaces.** The identity on any finite-dimensional
complex normed space `E` (in particular `ℂ`, with `finrank ℂ ℂ = 1`) is a closed holomorphic
embedding, yielding a finite-dimensional Hausdorff CW homotopy model with no cells above
`finrank ℂ E` (`0` when `E` is subsingleton). -/
example (E : Type u) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      RelCWComplex.FiniteDimensional (univ : Set X) ∧ Nonempty (E ≃ₕ X) ∧
      ∀ m, finrank ℂ E < m → IsEmpty (cell (univ : Set X) m) := by
  let h : Manifold.IsImmersion 𝓘(ℂ, E) 𝓘(ℂ, E) ∞ (@id E) := Manifold.IsImmersion.id
  exact h.exists_cwComplex_homotopyEquiv_of_isClosedEmbedding (by simp) .id

/-- **Check: zero-dimensional complex manifolds.** A `0`-dimensional complex manifold admitting a
closed holomorphic embedding into a finite-dimensional complex normed space has a Hausdorff CW
homotopy model with `0`-cells only (`IsEmpty (cell (univ : Set X) m)` for all `m > 0`). -/
example {E F : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [Subsingleton E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) 1 M]
    {i : M → F} (hi : MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, F) i)
    (hinj : ∀ x, Injective (mvfderiv 𝓘(ℂ, E) i x)) (hclosed : IsClosedEmbedding i) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      RelCWComplex.FiniteDimensional (univ : Set X) ∧ Nonempty (M ≃ₕ X) ∧
      ∀ m, 0 < m → IsEmpty (cell (univ : Set X) m) := by
  simpa only [finrank_zero_of_subsingleton] using
    exists_cwComplex_homotopyEquiv_of_isClosedEmbedding hi hinj hclosed

/-- **Check: product of complex manifolds (`𝓘(ℂ, E₁).prod 𝓘(ℂ, E₂)`).** Any product `M₁ × M₂` of
complex manifolds admitting a closed smooth holomorphic immersion into `Fin N → ℂ` is homotopy
equivalent to a Hausdorff CW complex of dimension at most `m + n`. -/
example {m n N : ℕ} {M₁ M₂ : Type u} [TopologicalSpace M₁] [TopologicalSpace M₂]
    [ChartedSpace (Fin m → ℂ) M₁] [ChartedSpace (Fin n → ℂ) M₂]
    [IsManifold 𝓘(ℂ, Fin m → ℂ) ∞ M₁] [IsManifold 𝓘(ℂ, Fin n → ℂ) ∞ M₂]
    {i : M₁ × M₂ → Fin N → ℂ}
    (hi : Manifold.IsImmersion (𝓘(ℂ, Fin m → ℂ).prod 𝓘(ℂ, Fin n → ℂ)) 𝓘(ℂ, Fin N → ℂ) ∞ i)
    (hclosed : IsClosedEmbedding i) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      Nonempty (M₁ × M₂ ≃ₕ X) ∧ ∀ k, m + n < k → IsEmpty (cell (univ : Set X) k) := by
  obtain ⟨X, _, _, _, _, hX, hdim⟩ :=
    hi.exists_cwComplex_homotopyEquiv_of_isClosedEmbedding (by simp) hclosed
  exact ⟨X, _, ‹_›, ‹_›, hX,
    fun k hk ↦ hdim k (by simpa [Module.finrank_prod, Module.finrank_fin_fun] using hk)⟩

/-- The defining polynomial `z₀ z₁ - 1` of the smooth affine hyperbola `ℂ* ↪ ℂ²`. -/
private abbrev hyperbolaPoly : Unit → MvPolynomial (Fin 2) ℂ :=
  fun _ ↦ MvPolynomial.X 0 * MvPolynomial.X 1 - 1

/-- The smooth affine hyperbola `z₀ z₁ = 1` in `ℂ²` is nonempty (`(1, 1)` lies on it). -/
private theorem nonempty_affineZeroLocus_hyperbolaPoly :
    Nonempty (affineZeroLocus hyperbolaPoly) :=
  ⟨⟨![1, 1], mem_affineZeroLocus.2 fun _ ↦ by simp [hyperbolaPoly]⟩⟩

/-- At every point `z` of the affine hyperbola `z₀ z₁ = 1`, the `1 × 2` Jacobian matrix `(z₁, z₀)`
is surjective because `z₁ ≠ 0`. -/
private theorem surjective_jacobiMatrixAt_hyperbolaPoly :
    ∀ z ∈ affineZeroLocus hyperbolaPoly, Surjective (jacobiMatrixAt hyperbolaPoly z).mulVec := by
  intro z hz
  rw [mulVec_surjective_jacobiMatrixAt_iff_exists_eval_pderiv_ne_zero]
  have hz_eq : z 0 * z 1 - 1 = 0 := by simpa [hyperbolaPoly] using mem_affineZeroLocus.1 hz ()
  refine ⟨0, ?_⟩
  have hz1 : z 1 ≠ 0 := by
    intro h0
    rw [h0, mul_zero, zero_sub] at hz_eq
    exact neg_ne_zero.2 one_ne_zero hz_eq
  simpa [hyperbolaPoly, pderiv_mul, pderiv_X] using hz1

/-- **Check: the smooth affine hyperbola `z₀ z₁ = 1` in `ℂ²` (`ℂ*`).** The zero locus is nonempty,
smooth of complex dimension `2 - 1 = 1`, and homotopy equivalent to a Hausdorff CW complex with no
cells above dimension `1`; transferring cellular dimension bounds across that CW homotopy
equivalence recovers `Hₖ = 0` and `Hᵏ = 0` for `k > 1` and freeness of `H₁(-; ℤ)`. -/
example : Nonempty (affineZeroLocus hyperbolaPoly) ∧
    ∃ (X : Type) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      Nonempty (affineZeroLocus hyperbolaPoly ≃ₕ X) ∧
      (∀ k, 1 < k → IsEmpty (cell (univ : Set X) k)) ∧
      (∀ k, 1 < k → IsZero (((singularHomologyFunctor (ModuleCat.{0} ℤ) k).obj
        (ModuleCat.of ℤ ℤ)).obj (TopCat.of (affineZeroLocus hyperbolaPoly)))) ∧
      (∀ k, 1 < k → IsZero ((TopCat.of (affineZeroLocus hyperbolaPoly)).singularCohomology
        (ModuleCat.of ℤ ℤ) ℤ (ModuleCat.of ℤ ℤ) k)) ∧
      Module.Free ℤ (((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
        (ModuleCat.of ℤ ℤ)).obj (TopCat.of (affineZeroLocus hyperbolaPoly))) := by
  refine ⟨nonempty_affineZeroLocus_hyperbolaPoly, ?_⟩
  obtain ⟨X, _, _, _, _, ⟨h⟩, hdim⟩ :=
    exists_cwComplex_homotopyEquiv_affineZeroLocus surjective_jacobiMatrixAt_hyperbolaPoly
  have hdim' : ∀ k, 1 < k → IsEmpty (cell (univ : Set X) k) :=
    fun k hk ↦ hdim k (by simpa only [Fintype.card_fin, Fintype.card_unit] using hk)
  let e : affineZeroLocus hyperbolaPoly ≃ₕ (univ : Set X) :=
    h.trans (Homeomorph.Set.univ X).symm.toHomotopyEquiv
  have : IsEmpty (cell (univ : Set X) (1 + 1)) := hdim' 2 (by omega)
  exact ⟨X, _, ‹_›, ‹_›, ⟨h⟩, hdim',
    fun k hk ↦ e.isZero_singularHomology_of_isEmpty_cell_gt _ hdim' hk,
    fun k hk ↦ e.isZero_singularCohomology_of_isEmpty_cell_gt _ _ hdim' hk,
    e.free_singularHomology_of_isEmpty_cell_succ (ModuleCat.of ℤ ℤ) 1⟩

/-- **Check: `0`-dimensional nonempty smooth affine zero locus (`z₀ = 0` in `ℂ¹`).** Its CW model
has no cells in positive dimensions. -/
example :
    let p : Unit → MvPolynomial (Fin 1) ℂ := fun _ ↦ MvPolynomial.X 0
    Nonempty (affineZeroLocus p) ∧
      ∃ (X : Type) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
        Nonempty (affineZeroLocus p ≃ₕ X) ∧ ∀ k, 0 < k → IsEmpty (cell (univ : Set X) k) := by
  intro p
  have hp : ∀ z ∈ affineZeroLocus p, Surjective (jacobiMatrixAt p z).mulVec := fun z _ ↦
    mulVec_surjective_jacobiMatrixAt_iff_exists_eval_pderiv_ne_zero.2 ⟨0, by simp [p]⟩
  obtain ⟨X, _, _, _, _, hX, hdim⟩ := exists_cwComplex_homotopyEquiv_affineZeroLocus hp
  exact ⟨⟨⟨![0], mem_affineZeroLocus.2 fun _ ↦ by simp [p]⟩⟩, X, _, ‹_›, ‹_›, hX,
    fun k hk ↦ hdim k (by simpa only [Fintype.card_fin, Fintype.card_unit] using hk)⟩

/-- **Check: empty smooth affine zero locus (`1 = 0` in `ℂ¹`).** -/
example :
    let p : Unit → MvPolynomial (Fin 1) ℂ := fun _ ↦ 1
    IsEmpty (affineZeroLocus p) ∧
      ∃ (X : Type) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
        Nonempty (affineZeroLocus p ≃ₕ X) ∧ ∀ k, 0 < k → IsEmpty (cell (univ : Set X) k) := by
  intro p
  have hEmpty : IsEmpty (affineZeroLocus p) :=
    ⟨fun ⟨z, hz⟩ ↦ (one_ne_zero (α := ℂ)) (by simpa [p] using mem_affineZeroLocus.1 hz ())⟩
  have hp : ∀ z ∈ affineZeroLocus p, Surjective (jacobiMatrixAt p z).mulVec :=
    fun z hz ↦ hEmpty.elim ⟨z, hz⟩
  obtain ⟨X, _, _, _, _, hX, hdim⟩ := exists_cwComplex_homotopyEquiv_affineZeroLocus hp
  exact ⟨hEmpty, X, _, ‹_›, ‹_›, hX,
    fun k hk ↦ hdim k (by simpa only [Fintype.card_fin, Fintype.card_unit] using hk)⟩

/-- **Check: exhaustion-independence of CW homotopy models.** Any two smooth proper bounded-below
strongly pseudoconvex exhaustions `f₁` (with parameter `q₁`) and `f₂` (with parameter `q₂`) on `M`
yield Hausdorff CW models `X₁` and `X₂` that are directly homotopy equivalent to one another. -/
example {E : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) 1 M] [T2Space M]
    {q₁ q₂ : ℕ} {f₁ f₂ : M → ℝ}
    (hf₁ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f₁) (hp₁ : IsProperMap f₁) (hbdd₁ : BddBelow (range f₁))
    (hq₁ : ∀ x, IsManifoldStronglyPseudoconvexAt E q₁ f₁ x)
    (hf₂ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f₂) (hp₂ : IsProperMap f₂) (hbdd₂ : BddBelow (range f₂))
    (hq₂ : ∀ x, IsManifoldStronglyPseudoconvexAt E q₂ f₂ x) :
    ∃ (X₁ X₂ : Type u) (_ : TopologicalSpace X₁) (_ : TopologicalSpace X₂) (_ : T2Space X₁)
      (_ : T2Space X₂) (_ : CWComplex (univ : Set X₁)) (_ : CWComplex (univ : Set X₂)),
      Nonempty (M ≃ₕ X₁) ∧ Nonempty (M ≃ₕ X₂) ∧ Nonempty (X₁ ≃ₕ X₂) ∧
      (∀ k, finrank ℂ E + q₁ < k → IsEmpty (cell (univ : Set X₁) k)) ∧
      (∀ k, finrank ℂ E + q₂ < k → IsEmpty (cell (univ : Set X₂) k)) := by
  obtain ⟨X₁, _, _, _, _, ⟨h₁⟩, hd₁⟩ :=
    exists_cwComplex_homotopyEquiv_of_isProperMap_of_isManifoldStronglyPseudoconvexAt hf₁ hp₁ hbdd₁
      hq₁
  obtain ⟨X₂, _, _, _, _, ⟨h₂⟩, hd₂⟩ :=
    exists_cwComplex_homotopyEquiv_of_isProperMap_of_isManifoldStronglyPseudoconvexAt hf₂ hp₂ hbdd₂
      hq₂
  exact ⟨X₁, X₂, _, _, ‹_›, ‹_›, ‹_›, ‹_›, ⟨h₁⟩, ⟨h₂⟩, ⟨h₁.symm.trans h₂⟩, hd₁, hd₂⟩

end Checks

end TauCeti
