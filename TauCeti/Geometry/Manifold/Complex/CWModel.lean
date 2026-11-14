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
public import TauCeti.Geometry.Manifold.RegularValue.Polynomial
import TauCeti.AlgebraicTopology.Cellular.Dimension
import TauCeti.Topology.Maps.Proper.Basic
import TauCeti.Topology.Maps.Proper.Metric

/-!
# CW homotopy models of pseudoconvex complex manifolds and holomorphic immersions

On a complex manifold `M` of complex dimension `n`, a real Morse function which is strongly
`q`-pseudoconvex at its critical points has real Morse index at most `n + q` at every critical point
(`TauCeti.IsManifoldStronglyPseudoconvexAt.manifoldMorseIndex_le`). Combining this index bound with
the CW model of a proper Morse function (`TauCeti.IsMorse.exists_cwComplex_sublevel_homotopyEquiv`)
and with strong-Whitney Morse approximation of pseudoconvex exhaustions
(`TauCeti.exists_isMorse_isProperMap_bddBelow_isManifoldStronglyPseudoconvexAt_sub_compl`) yields
the global CW homotopy models of Andreotti–Frankel and Milnor:

* **Strongly `q`-pseudoconvex Morse functions and exhaustions.** If `f : M → ℝ` is a proper
  bounded-below Morse function strongly `q`-pseudoconvex at its critical points, then `M` is
  homotopy equivalent to a Hausdorff CW complex `X` whose `m`-cells correspond to the critical
  points of `f` of index `m`, with no cells in dimensions strictly above `n + q`, realized as the
  union of compatible finite CW models of regular sublevels
  (`TauCeti.IsMorse.exists_cwComplex_sublevel_homotopyEquiv_of_isManifoldStronglyPseudoconvexAt`).
  When `f : M → ℝ` is an arbitrary smooth proper bounded-below everywhere strongly
  `q`-pseudoconvex exhaustion (not assumed Morse), perturbing `f` within `C⁰` error `1` produces a
  strongly `q`-pseudoconvex Morse exhaustion and hence a Hausdorff CW model of `M` of dimension at
  most `n + q`
  (`TauCeti.exists_cwComplex_homotopyEquiv_of_isProperMap_of_isManifoldStronglyPseudoconvexAt`).
  For `q = 0` — smooth strictly plurisubharmonic exhaustions, such as on Stein manifolds — `M` has
  the homotopy type of a Hausdorff CW complex of dimension at most `n`
  (`TauCeti.exists_cwComplex_homotopyEquiv_of_isProperMap_of_isManifoldStrictlyPlurisubharmonicAt`).
* **Proper holomorphic immersions and closed holomorphic embeddings** (Andreotti–Frankel; Milnor,
  *Morse Theory*, Theorem 7.2). Along a proper holomorphic immersion `i : M → F` into a proper
  complex inner product space, the squared distance `x ↦ ‖i x - a‖²` from a generic centre `a : F`
  is a proper bounded-below strictly plurisubharmonic Morse exhaustion, giving both a global
  Hausdorff CW model of `M` of dimension at most `n` and compatible finite CW models of the
  Euclidean ball intersections `{x | ‖i x - a‖² ≤ r k}`
  (`TauCeti.exists_cwComplex_sublevel_homotopyEquiv_norm_sq_sub_comp`). Transporting an inner
  product along a continuous linear equivalence extends the global `n`-dimensional CW homotopy model
  to proper holomorphic immersions into any proper complex normed space and closed holomorphic
  embeddings into any finite-dimensional complex normed space
  (`TauCeti.exists_cwComplex_homotopyEquiv_of_isProperMap_holomorphic_immersion`,
  `TauCeti.exists_cwComplex_homotopyEquiv_of_isClosedEmbedding`, and the `Manifold.IsImmersion`
  forms). Neither finite-dimensionality of the model space `E` nor second-countability of `M` is
  assumed separately, and for closed embeddings Hausdorffness of `M` follows from the embedding.
* **Smooth affine complete intersections.** If `p : ι → MvPolynomial σ ℂ` has surjective Jacobian
  at every point of `TauCeti.affineZeroLocus p`, then `affineZeroLocus p` is homotopy equivalent to
  a Hausdorff CW complex with no cells in dimensions strictly above its complex dimension
  `|σ| - |ι|` (`TauCeti.exists_cwComplex_homotopyEquiv_affineZeroLocus`).

## Main results

* `TauCeti.ComplexManifold.cwType`, `TauCeti.ComplexManifold.cwType_of_isProperMap`, and
  `TauCeti.ComplexManifold.cwType_of_isClosedEmbedding`: CW type of sigma-compact `C^n` (`n ≠ 0`)
  complex manifolds and of complex manifolds admitting proper maps or closed embeddings.
* `exists_finite_cwComplex_extension_homotopyEquiv_sublevel_of_isManifoldStronglyPseudoconvexAt`
  and `exists_finite_cwComplex_homotopyEquiv_sublevel_of_isManifoldStronglyPseudoconvexAt` (in
  `TauCeti.IsMorse`): finite CW models of compact regular bands and sublevels of strongly
  `q`-pseudoconvex Morse functions, with no cells above `dim_ℂ E + q`.
* `IsMorse.exists_cwComplex_sublevel_homotopyEquiv_of_isManifoldStronglyPseudoconvexAt` and
  `IsMorse.exists_cwComplex_homotopyEquiv_of_isManifoldStronglyPseudoconvexAt`: global CW homotopy
  model (with compatible finite sublevel models) of a proper bounded-below strongly
  `q`-pseudoconvex Morse function.
* `exists_isMorse_cwComplex_homotopyEquiv_isManifoldStronglyPseudoconvexAt_sub_compl`,
  `exists_cwComplex_homotopyEquiv_of_isProperMap_of_isManifoldStronglyPseudoconvexAt`, and
  `exists_cwComplex_homotopyEquiv_of_isProperMap_of_isManifoldStrictlyPlurisubharmonicAt`: CW
  homotopy models of smooth strongly `q`-pseudoconvex and strictly plurisubharmonic exhaustions.
* `TauCeti.exists_cwComplex_sublevel_homotopyEquiv_norm_sq_sub_comp`,
  `TauCeti.exists_cwComplex_homotopyEquiv_of_isProperMap_holomorphic_immersion`,
  `TauCeti.exists_cwComplex_homotopyEquiv_of_isClosedEmbedding`,
  `Manifold.IsImmersion.exists_cwComplex_homotopyEquiv_of_isProperMap`, and
  `Manifold.IsImmersion.exists_cwComplex_homotopyEquiv_of_isClosedEmbedding`: Andreotti–Frankel and
  Milnor CW dimension bounds for proper holomorphic immersions and closed holomorphic embeddings.
* `TauCeti.exists_cwComplex_sublevel_homotopyEquiv_affineZeroLocus`,
  `TauCeti.exists_cwComplex_homotopyEquiv_affineZeroLocus`, and `TauCeti.cwType_affineZeroLocus`:
  CW homotopy model and CW type of smooth affine complete intersections.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 3.5 and Section 7, Theorems 7.1 and 7.2.
* A. Andreotti and T. Frankel, *The Lefschetz theorem on hyperplane sections*, Annals of
  Mathematics 69 (1959), 713–717.
* R. Hain, *Notes on the Morse theory of complex manifolds*, Section 2.
-/

public section

noncomputable section

open Filter Function Module MvPolynomial Set Topology Topology.RelCWComplex
open scoped ContDiff ContinuousMap Manifold

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

/-! ### Strongly `q`-pseudoconvex and strictly plurisubharmonic Morse functions -/

section PseudoconvexMorse

variable {E : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) 1 M] [T2Space M] {f : M → ℝ}

namespace IsMorse

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
  have : IsManifold 𝓘(ℂ, E) 2 M := IsManifold.of_ne_zero 2 one_ne_zero ‹_›
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
  have : IsManifold 𝓘(ℂ, E) 2 M := IsManifold.of_ne_zero 2 one_ne_zero ‹_›
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

/-- **The CW model of a proper strongly `q`-pseudoconvex Morse function, with compatible finite
sublevel models.** Let `f` be a proper real Morse function, bounded below, on a Hausdorff complex
manifold `M` of complex dimension `n`, strongly `q`-pseudoconvex at every critical point. Then `M`
is homotopy equivalent to a Hausdorff CW complex `X` with one `m`-cell per index-`m` critical point
of `f` and no cells above dimension `n + q`, realized as the coherent union of cellular closed
embeddings `j k : C(W k, X)` of finite CW models `W k` (linked by cellular closed embeddings
`ι k : C(W k, W (k + 1))`) of regular sublevels `{f ≤ a k}` of dimension at most `n + q` commuting
with `h : X ≃ₕ M`. -/
theorem exists_cwComplex_sublevel_homotopyEquiv_of_isManifoldStronglyPseudoconvexAt
    {q : ℕ} (hf : IsMorse 𝓘(ℝ, E) f) (hp : IsProperMap f) (hbdd : BddBelow (range f))
    (hq : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f, IsManifoldStronglyPseudoconvexAt E q f x) :
    ∃ (a : ℕ → ℝ) (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X)
      (_ : CWComplex (univ : Set X)) (h : X ≃ₕ M)
      (W : ℕ → Type u) (_ : ∀ k, TopologicalSpace (W k)) (_ : ∀ k, T2Space (W k))
      (_ : ∀ k, CWComplex (univ : Set (W k))) (_ : ∀ k, RelCWComplex.Finite (univ : Set (W k)))
      (ι : ∀ k, C(W k, W (k + 1))) (j : ∀ k, C(W k, X)) (hSub : ∀ k, W k ≃ₕ {x | f x ≤ a k}),
      StrictMono a ∧ Tendsto a atTop atTop ∧ (∀ k, IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f (a k)) ∧
      (∀ x, a 0 < f x) ∧ (∀ k, IsClosedEmbedding (ι k)) ∧ (∀ k, IsClosedEmbedding (j k)) ∧
      (∀ k w, j (k + 1) (ι k w) = j k w) ∧
      IsCoherentWith (range fun k ↦ range (j k)) ∧ ⋃ k, range (j k) = univ ∧
      (∀ k w, h (j k w) = (hSub k w : M)) ∧
      (∀ k, MapsTo h.symm {x | f x ≤ a k} (range (j k))) ∧
      (∃ (ιc : ∀ k m, cell (univ : Set (W k)) m → cell (univ : Set (W (k + 1))) m)
         (jc : ∀ k m, cell (univ : Set (W k)) m → cell (univ : Set X) m),
        (∀ k m c x, map m (ιc k m c) x = ι k (map m c x)) ∧
        ∀ k m c x, map m (jc k m c) x = j k (map m c x)) ∧
      (∀ m, finrank ℂ E + q < m → IsEmpty (cell (univ : Set X) m)) ∧
      (∀ k m, finrank ℂ E + q < m → IsEmpty (cell (univ : Set (W k)) m)) ∧
      (∀ m, Nonempty (cell (univ : Set X) m ≃
        ↥{x ∈ criticalPoints 𝓘(ℝ, E) f | manifoldMorseIndex 𝓘(ℝ, E) f x = m})) ∧
      ∀ k m, Nonempty (cell (univ : Set (W k)) m ≃
        ↥{x ∈ criticalPoints 𝓘(ℝ, E) f ∩ {x | f x ≤ a k} |
          manifoldMorseIndex 𝓘(ℝ, E) f x = m}) := by
  have : IsManifold 𝓘(ℂ, E) 2 M := IsManifold.of_ne_zero 2 one_ne_zero ‹_›
  have : IsManifold 𝓘(ℝ, E) ∞ M := IsManifold.restrictScalars_of_ne_zero ∞ one_ne_zero ‹_›
  exact hf.exists_cwComplex_sublevel_homotopyEquiv_of_manifoldMorseIndex_le hp hbdd fun x hx ↦
    (hq x hx).manifoldMorseIndex_le_of_mem_criticalPoints (hf.contMDiff x) hx

/-- **The CW model of a proper strongly `q`-pseudoconvex Morse function.** Let `f` be a proper real
Morse function, bounded below, on a Hausdorff complex manifold `M` of complex dimension `n`,
strongly `q`-pseudoconvex at every critical point. Then `M` is homotopy equivalent to a Hausdorff CW
complex `X` whose `m`-cells correspond to the critical points of `f` of index `m` and which has no
cells in dimensions strictly greater than `n + q`. -/
theorem exists_cwComplex_homotopyEquiv_of_isManifoldStronglyPseudoconvexAt {q : ℕ}
    (hf : IsMorse 𝓘(ℝ, E) f) (hp : IsProperMap f) (hbdd : BddBelow (range f))
    (hq : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f, IsManifoldStronglyPseudoconvexAt E q f x) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      Nonempty (M ≃ₕ X) ∧ (∀ k, finrank ℂ E + q < k → IsEmpty (cell (univ : Set X) k)) ∧
      ∀ m, Nonempty (cell (univ : Set X) m ≃
        ↥{x ∈ criticalPoints 𝓘(ℝ, E) f | manifoldMorseIndex 𝓘(ℝ, E) f x = m}) := by
  have : IsManifold 𝓘(ℂ, E) 2 M := IsManifold.of_ne_zero 2 one_ne_zero ‹_›
  have : IsManifold 𝓘(ℝ, E) ∞ M := IsManifold.restrictScalars_of_ne_zero ∞ one_ne_zero ‹_›
  exact hf.exists_cwComplex_homotopyEquiv_of_manifoldMorseIndex_le hp hbdd fun x hx ↦
    (hq x hx).manifoldMorseIndex_le_of_mem_criticalPoints (hf.contMDiff x) hx

omit [FiniteDimensional ℂ E] in
/-- **The CW model of a proper strictly plurisubharmonic Morse function.** Let `f` be a proper real
Morse function, bounded below, on a Hausdorff complex manifold `M`, strictly plurisubharmonic at
every critical point. Then `M` is homotopy equivalent to a Hausdorff CW complex `X` whose `m`-cells
correspond to the critical points of `f` of index `m` and which has no cells in dimensions strictly
greater than `finrank ℂ E`. No separate finite-dimensionality assumption on `E` is needed. -/
theorem exists_cwComplex_homotopyEquiv_of_isManifoldStrictlyPlurisubharmonicAt
    (hf : IsMorse 𝓘(ℝ, E) f) (hp : IsProperMap f) (hbdd : BddBelow (range f))
    (hpsh : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f, IsManifoldStrictlyPlurisubharmonicAt E f x) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      Nonempty (M ≃ₕ X) ∧ (∀ k, finrank ℂ E < k → IsEmpty (cell (univ : Set X) k)) ∧
      ∀ m, Nonempty (cell (univ : Set X) m ≃
        ↥{x ∈ criticalPoints 𝓘(ℝ, E) f | manifoldMorseIndex 𝓘(ℝ, E) f x = m}) := by
  rcases isEmpty_or_nonempty M with _ | _
  · exact ⟨PEmpty.{u + 1}, _, inferInstance, inferInstance, ⟨Homeomorph.empty.toHomotopyEquiv⟩,
      fun _ _ ↦ inferInstance, fun _ ↦ ⟨Equiv.equivOfIsEmpty _ _⟩⟩
  have := hp.weaklyLocallyCompactSpace
  have : FiniteDimensional ℂ E := FiniteDimensional.of_locallyCompact_manifold M 𝓘(ℂ, E)
  simpa only [add_zero] using
    hf.exists_cwComplex_homotopyEquiv_of_isManifoldStronglyPseudoconvexAt (q := 0) hp hbdd
      fun x hx ↦ (hpsh x hx).isManifoldStronglyPseudoconvexAt 0

end IsMorse

end PseudoconvexMorse

/-! ### Smooth strongly `q`-pseudoconvex and strictly plurisubharmonic exhaustions -/

section PseudoconvexExhaustion

variable {E : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) 1 M] [T2Space M]

/-- **Relative Morse perturbation and CW homotopy model of a strongly `q`-pseudoconvex exhaustion.**
Given a smooth proper bounded-below everywhere strongly `q`-pseudoconvex function `f : M → ℝ` on a
Hausdorff complex manifold `M` of complex dimension `n` which is already Morse on an open
neighbourhood `V` of a closed set `C`, there exist a smooth proper bounded-below everywhere strongly
`q`-pseudoconvex Morse function `g` within `C⁰` distance `1` of `f` agreeing with `f` near `C` and a
Hausdorff CW complex `X` homotopy equivalent to `M` whose `m`-cells correspond to the critical
points of `g` of index `m`, with no cells in dimensions strictly greater than `n + q`. -/
theorem exists_isMorse_cwComplex_homotopyEquiv_isManifoldStronglyPseudoconvexAt_sub_compl
    {q : ℕ} {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f) (hp : IsProperMap f)
    (hbdd : BddBelow (range f)) (hq : ∀ x, IsManifoldStronglyPseudoconvexAt E q f x)
    {C V : Set M} (hC : IsClosed C) (hV : IsOpen V) (hCV : C ⊆ V)
    (hfV : IsMorseOn 𝓘(ℝ, E) f V) :
    ∃ (g : C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯) (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X)
      (_ : CWComplex (univ : Set X)),
      IsMorse 𝓘(ℝ, E) g ∧ IsProperMap g ∧ BddBelow (range g) ∧
      (∀ x, IsManifoldStronglyPseudoconvexAt E q g x) ∧
      (∀ x, |g x - f x| < 1) ∧ tsupport (fun x ↦ g x - f x) ⊆ Cᶜ ∧
      Nonempty (M ≃ₕ X) ∧ (∀ k, finrank ℂ E + q < k → IsEmpty (cell (univ : Set X) k)) ∧
      ∀ m, Nonempty (cell (univ : Set X) m ≃
        ↥{x ∈ criticalPoints 𝓘(ℝ, E) g | manifoldMorseIndex 𝓘(ℝ, E) g x = m}) := by
  have : IsManifold 𝓘(ℂ, E) ∞ M := IsManifold.of_ne_zero ∞ one_ne_zero ‹_›
  obtain ⟨g, hgm, hgp, hgbdd, hg_pos, -, hgf, hgs⟩ :=
    exists_isMorse_isProperMap_bddBelow_isManifoldStronglyPseudoconvexAt_sub_compl hf hp hbdd hq
      hC hV hCV hfV
  obtain ⟨X, _, _, _, hX, hdim, hcell⟩ :=
    hgm.exists_cwComplex_homotopyEquiv_of_isManifoldStronglyPseudoconvexAt hgp hgbdd
      fun x _ ↦ hg_pos x
  exact ⟨g, X, _, ‹_›, ‹_›, hgm, hgp, hgbdd, hg_pos, hgf, hgs, hX, hdim, hcell⟩

/-- **CW homotopy model of a complex manifold with a strongly `q`-pseudoconvex exhaustion.** If a
Hausdorff complex manifold `M` of complex dimension `n` admits a smooth proper bounded-below
everywhere strongly `q`-pseudoconvex function `f : M → ℝ` (not assumed to be Morse), then `M` is
homotopy equivalent to a Hausdorff CW complex with no cells in dimensions strictly greater than
`n + q`. No separate second-countability hypothesis on `M` is required. -/
theorem exists_cwComplex_homotopyEquiv_of_isProperMap_of_isManifoldStronglyPseudoconvexAt
    {q : ℕ} {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f) (hp : IsProperMap f)
    (hbdd : BddBelow (range f)) (hq : ∀ x, IsManifoldStronglyPseudoconvexAt E q f x) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      Nonempty (M ≃ₕ X) ∧ ∀ k, finrank ℂ E + q < k → IsEmpty (cell (univ : Set X) k) := by
  obtain ⟨_, X, _, _, _, -, -, -, -, -, -, hX, hdim, -⟩ :=
    exists_isMorse_cwComplex_homotopyEquiv_isManifoldStronglyPseudoconvexAt_sub_compl
      hf hp hbdd hq isClosed_empty isOpen_empty (subset_refl _) isMorseOn_empty
  exact ⟨X, _, ‹_›, ‹_›, hX, hdim⟩

omit [FiniteDimensional ℂ E] in
/-- **CW homotopy model of a complex manifold with a strictly plurisubharmonic exhaustion.** If a
Hausdorff complex manifold `M` admits a smooth proper bounded-below everywhere strictly
plurisubharmonic function `f : M → ℝ` (not assumed to be Morse, for example a Stein exhaustion),
then `M` is homotopy equivalent to a Hausdorff CW complex with no cells in dimensions strictly
greater than `finrank ℂ E`. Neither second-countability of `M` nor finite-dimensionality of `E` is
assumed separately. -/
theorem exists_cwComplex_homotopyEquiv_of_isProperMap_of_isManifoldStrictlyPlurisubharmonicAt
    {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f) (hp : IsProperMap f)
    (hbdd : BddBelow (range f)) (hpsh : ∀ x, IsManifoldStrictlyPlurisubharmonicAt E f x) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      Nonempty (M ≃ₕ X) ∧ ∀ k, finrank ℂ E < k → IsEmpty (cell (univ : Set X) k) := by
  rcases isEmpty_or_nonempty M with _ | _
  · exact ⟨PEmpty.{u + 1}, _, inferInstance, inferInstance, ⟨Homeomorph.empty.toHomotopyEquiv⟩,
      fun _ _ ↦ inferInstance⟩
  have := hp.weaklyLocallyCompactSpace
  have : FiniteDimensional ℂ E := FiniteDimensional.of_locallyCompact_manifold M 𝓘(ℂ, E)
  simpa only [add_zero] using
    exists_cwComplex_homotopyEquiv_of_isProperMap_of_isManifoldStronglyPseudoconvexAt (q := 0)
      hf hp hbdd fun x ↦ (hpsh x).isManifoldStronglyPseudoconvexAt 0

end PseudoconvexExhaustion

/-! ### Proper holomorphic immersions, closed holomorphic embeddings, and affine zero loci -/

section HolomorphicImmersion

variable {E : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) 1 M] [T2Space M]

/-- **Milnor's squared-distance CW exhaustion along a proper holomorphic immersion.** Let
`i : M → F` be a proper holomorphic immersion of a Hausdorff complex manifold `M` into a proper
complex inner product space `F`. For some centre `a : F`, the squared distance `ρ(x) = ‖i x - a‖²`
is a proper Morse function on `M`, and there exist strictly increasing regular values `r : ℕ → ℝ`
of `ρ` tending to infinity with `r 0` below all values of `ρ`, a Hausdorff CW complex `X` with a
homotopy equivalence `h : X ≃ₕ M` and no cells above `finrank ℂ E` whose `m`-cells correspond to
the index-`m` critical points of `ρ`, and finite CW models `W k ≃ₕ {x | ‖i x - a‖² ≤ r k}` of
dimension at most `finrank ℂ E` linked by cellular closed embeddings `ι k : C(W k, W (k + 1))` and
exhausting `X` coherently along cellular closed embeddings `j k : C(W k, X)`. -/
theorem exists_cwComplex_sublevel_homotopyEquiv_norm_sq_sub_comp {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [ProperSpace F] {i : M → F}
    (hi : MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, F) i)
    (hinj : ∀ x, Injective (mvfderiv 𝓘(ℂ, E) i x)) (hip : IsProperMap i) :
    ∃ (a : F) (r : ℕ → ℝ) (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X)
      (_ : CWComplex (univ : Set X)) (h : X ≃ₕ M)
      (W : ℕ → Type u) (_ : ∀ k, TopologicalSpace (W k)) (_ : ∀ k, T2Space (W k))
      (_ : ∀ k, CWComplex (univ : Set (W k))) (_ : ∀ k, RelCWComplex.Finite (univ : Set (W k)))
      (ι : ∀ k, C(W k, W (k + 1))) (j : ∀ k, C(W k, X))
      (hSub : ∀ k, W k ≃ₕ {x | ‖i x - a‖ ^ 2 ≤ r k}),
      IsMorse 𝓘(ℝ, E) (fun x ↦ ‖i x - a‖ ^ 2) ∧
      IsProperMap (fun x ↦ ‖i x - a‖ ^ 2) ∧
      StrictMono r ∧ Tendsto r atTop atTop ∧
      (∀ k, IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) (fun x ↦ ‖i x - a‖ ^ 2) (r k)) ∧
      (∀ x, r 0 < ‖i x - a‖ ^ 2) ∧
      (∀ k, IsClosedEmbedding (ι k)) ∧ (∀ k, IsClosedEmbedding (j k)) ∧
      (∀ k w, j (k + 1) (ι k w) = j k w) ∧
      IsCoherentWith (range fun k ↦ range (j k)) ∧ ⋃ k, range (j k) = univ ∧
      (∀ k w, h (j k w) = (hSub k w : M)) ∧
      (∀ k, MapsTo h.symm {x | ‖i x - a‖ ^ 2 ≤ r k} (range (j k))) ∧
      (∃ (ιc : ∀ k m, cell (univ : Set (W k)) m → cell (univ : Set (W (k + 1))) m)
         (jc : ∀ k m, cell (univ : Set (W k)) m → cell (univ : Set X) m),
        (∀ k m c x, map m (ιc k m c) x = ι k (map m c x)) ∧
        ∀ k m c x, map m (jc k m c) x = j k (map m c x)) ∧
      (∀ m, finrank ℂ E < m → IsEmpty (cell (univ : Set X) m)) ∧
      (∀ k m, finrank ℂ E < m → IsEmpty (cell (univ : Set (W k)) m)) ∧
      (∀ m, Nonempty (cell (univ : Set X) m ≃
        ↥{x ∈ criticalPoints 𝓘(ℝ, E) (fun y ↦ ‖i y - a‖ ^ 2) |
          manifoldMorseIndex 𝓘(ℝ, E) (fun y ↦ ‖i y - a‖ ^ 2) x = m})) ∧
      ∀ k m, Nonempty (cell (univ : Set (W k)) m ≃
        ↥{x ∈ criticalPoints 𝓘(ℝ, E) (fun y ↦ ‖i y - a‖ ^ 2) ∩ {x | ‖i x - a‖ ^ 2 ≤ r k} |
          manifoldMorseIndex 𝓘(ℝ, E) (fun y ↦ ‖i y - a‖ ^ 2) x = m}) := by
  have hex : ∃ (_ : IsManifold 𝓘(ℝ, E) ∞ M) (a : F),
      IsMorse 𝓘(ℝ, E) (fun x ↦ ‖i x - a‖ ^ 2) ∧
      IsProperMap (fun x ↦ ‖i x - a‖ ^ 2) ∧ BddBelow (range fun x ↦ ‖i x - a‖ ^ 2) ∧
      ∀ x ∈ criticalPoints 𝓘(ℝ, E) (fun y ↦ ‖i y - a‖ ^ 2),
        manifoldMorseIndex 𝓘(ℝ, E) (fun y ↦ ‖i y - a‖ ^ 2) x ≤ finrank ℂ E := by
    rcases isEmpty_or_nonempty M with hM | ⟨⟨x₀⟩⟩
    · refine ⟨inferInstance, 0, ?_, (isProperMap_norm_sq_sub_comp_iff hi.continuous 0).2 hip,
        ⟨0, by rintro _ ⟨x, rfl⟩; positivity⟩, fun x _ ↦ isEmptyElim x⟩
      rw [← isMorseOn_univ, Set.univ_eq_empty_iff.2 hM]
      exact isMorseOn_empty
    have : FiniteDimensional ℂ F := .of_locallyCompactSpace ℂ
    have : CompleteSpace F := FiniteDimensional.completeSpace ℂ F
    have : FiniteDimensional ℂ E :=
      Module.Finite.of_injective (mvfderiv 𝓘(ℂ, E) i x₀).toLinearMap (hinj x₀)
    have : IsManifold 𝓘(ℂ, E) ∞ M := IsManifold.of_ne_zero ∞ one_ne_zero ‹_›
    have hMR : IsManifold 𝓘(ℝ, E) ∞ M := IsManifold.restrictScalars ℝ ‹IsManifold 𝓘(ℂ, E) ∞ M›
    obtain ⟨a, ha, hap, hbdd, hidx⟩ :=
      exists_isMorse_isProperMap_bddBelow_and_manifoldMorseIndex_norm_sq_sub_comp_le
        hi.contMDiff hinj hip
    exact ⟨hMR, a, ha, hap, hbdd, hidx⟩
  obtain ⟨_, a, ha, hap, hbdd, hidx⟩ := hex
  obtain ⟨r, X, _, _, _, h, W, _, _, _, _, ι, j, hSub, hrest⟩ :=
    ha.exists_cwComplex_sublevel_homotopyEquiv_of_manifoldMorseIndex_le hap hbdd hidx
  exact ⟨a, r, X, _, ‹_›, ‹_›, h, W, _, ‹_›, ‹_›, ‹_›, ι, j, hSub, ha, hap, hrest⟩

/-- **Andreotti–Frankel–Milnor CW theorem for proper holomorphic immersions.** If a Hausdorff
complex manifold `M` admits a proper holomorphic immersion into a proper complex normed space, then
`M` is homotopy equivalent to a Hausdorff CW complex with no cells in dimensions strictly greater
than `finrank ℂ E`. Neither finite-dimensionality of `E` nor second-countability of `M` is assumed
separately. -/
theorem exists_cwComplex_homotopyEquiv_of_isProperMap_holomorphic_immersion {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℂ F] [ProperSpace F] {i : M → F}
    (hi : MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, F) i)
    (hinj : ∀ x, Injective (mvfderiv 𝓘(ℂ, E) i x)) (hip : IsProperMap i) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      Nonempty (M ≃ₕ X) ∧ ∀ k, finrank ℂ E < k → IsEmpty (cell (univ : Set X) k) := by
  -- Transport an inner product from `EuclideanSpace ℂ (Fin (finrank ℂ F))` along a continuous
  -- complex linear equivalence so that Milnor's squared-distance exhaustion applies.
  have : FiniteDimensional ℂ F := .of_locallyCompactSpace ℂ
  let e : F ≃L[ℂ] EuclideanSpace ℂ (Fin (finrank ℂ F)) :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
  have hein : ∀ x, Injective (mvfderiv 𝓘(ℂ, E) (e ∘ i) x) := fun x v w hvw ↦ by
    simp only [mvfderiv_comp_apply_of_differentiableAt e.differentiableAt (hi x), e.fderiv] at hvw
    exact hinj x (e.injective hvw)
  obtain ⟨_, _, X, _, _, _, h, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
      hdim, -⟩ :=
    exists_cwComplex_sublevel_homotopyEquiv_norm_sq_sub_comp
      ((e.contDiff.contMDiff.mdifferentiable one_ne_zero).comp hi) hein
      (e.toHomeomorph.isClosedEmbedding.isProperMap.comp hip)
  exact ⟨X, _, ‹_›, ‹_›, ⟨h.symm⟩, hdim⟩

omit [T2Space M] in
/-- **Andreotti–Frankel–Milnor CW theorem for closed holomorphic embeddings** (Milnor, *Morse
Theory*, Theorem 7.2). Every complex manifold admitting a holomorphic immersion into a
finite-dimensional complex normed space which is a closed topological embedding is homotopy
equivalent to a Hausdorff CW complex with no cells in dimensions strictly greater than
`finrank ℂ E`. Hausdorffness and second-countability of `M` follow from the closed embedding, and no
separate `FiniteDimensional ℂ E` assumption is needed. -/
theorem exists_cwComplex_homotopyEquiv_of_isClosedEmbedding {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℂ F] [FiniteDimensional ℂ F] {i : M → F}
    (hi : MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, F) i)
    (hinj : ∀ x, Injective (mvfderiv 𝓘(ℂ, E) i x)) (hclosed : IsClosedEmbedding i) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      Nonempty (M ≃ₕ X) ∧ ∀ k, finrank ℂ E < k → IsEmpty (cell (univ : Set X) k) := by
  have : T2Space M := hclosed.isEmbedding.t2Space
  have : FiniteDimensional ℝ F := .trans ℝ ℂ F
  exact exists_cwComplex_homotopyEquiv_of_isProperMap_holomorphic_immersion hi hinj
    hclosed.isProperMap

end HolomorphicImmersion

/-! ### Smooth affine complete intersections -/

section AffineZeroLocus

/-- **Milnor's squared-distance CW exhaustion of a smooth affine complete intersection.** Let
`p : ι → MvPolynomial σ ℂ` be a finite polynomial family whose Jacobian matrix is surjective at
every point of `V = affineZeroLocus p`, so that `V` is a closed complex submanifold of `ℂ^σ` of
complex dimension `d = |σ| - |ι|`. For some Euclidean centre `a`, the squared distance
`ρ(y) = ‖toLp 2 y - a‖²` is a proper Morse function on `V`, and there exist strictly increasing
regular values `r : ℕ → ℝ` of `ρ` tending to infinity with `r 0` below all values of `ρ`, a
Hausdorff CW complex `X` with `h : X ≃ₕ V` and no cells above dimension `d` whose `m`-cells
correspond to the index-`m` critical points of `ρ`, and finite CW models `W k` of dimension at most
`d` for the compact sublevels `{y ∈ V | ‖toLp 2 y - a‖² ≤ r k}` linked by cellular closed embeddings
`i k : C(W k, W (k + 1))` and exhausting `X` coherently along cellular closed embeddings
`j k : C(W k, X)`. -/
theorem exists_cwComplex_sublevel_homotopyEquiv_affineZeroLocus {σ : Type u} {ι : Type*}
    [Fintype σ] [Fintype ι] {p : ι → MvPolynomial σ ℂ}
    (hp : ∀ x ∈ affineZeroLocus p, Surjective (jacobiMatrixAt p x).mulVec) :
    letI := affineZeroLocusChartedSpace hp
    ∃ (a : EuclideanSpace ℂ σ) (r : ℕ → ℝ) (X : Type u) (_ : TopologicalSpace X)
      (_ : T2Space X) (_ : CWComplex (univ : Set X)) (h : X ≃ₕ affineZeroLocus p)
      (W : ℕ → Type u) (_ : ∀ k, TopologicalSpace (W k)) (_ : ∀ k, T2Space (W k))
      (_ : ∀ k, CWComplex (univ : Set (W k))) (_ : ∀ k, RelCWComplex.Finite (univ : Set (W k)))
      (i : ∀ k, C(W k, W (k + 1))) (j : ∀ k, C(W k, X))
      (hSub : ∀ k, W k ≃ₕ {y : affineZeroLocus p | ‖WithLp.toLp 2 (y : σ → ℂ) - a‖ ^ 2 ≤ r k}),
      IsMorse 𝓘(ℝ, Fin (Fintype.card σ - Fintype.card ι) → ℂ)
        (fun y : affineZeroLocus p ↦ ‖WithLp.toLp 2 (y : σ → ℂ) - a‖ ^ 2) ∧
      IsProperMap (fun y : affineZeroLocus p ↦ ‖WithLp.toLp 2 (y : σ → ℂ) - a‖ ^ 2) ∧
      StrictMono r ∧ Tendsto r atTop atTop ∧
      (∀ k, IsRegularValue 𝓘(ℝ, Fin (Fintype.card σ - Fintype.card ι) → ℂ) 𝓘(ℝ)
        (fun y : affineZeroLocus p ↦ ‖WithLp.toLp 2 (y : σ → ℂ) - a‖ ^ 2) (r k)) ∧
      (∀ y : affineZeroLocus p, r 0 < ‖WithLp.toLp 2 (y : σ → ℂ) - a‖ ^ 2) ∧
      (∀ k, IsClosedEmbedding (i k)) ∧ (∀ k, IsClosedEmbedding (j k)) ∧
      (∀ k w, j (k + 1) (i k w) = j k w) ∧
      IsCoherentWith (range fun k ↦ range (j k)) ∧ ⋃ k, range (j k) = univ ∧
      (∀ k w, h (j k w) = (hSub k w : affineZeroLocus p)) ∧
      (∀ k, MapsTo h.symm {y : affineZeroLocus p | ‖WithLp.toLp 2 (y : σ → ℂ) - a‖ ^ 2 ≤ r k}
        (range (j k))) ∧
      (∃ (ic : ∀ k m, cell (univ : Set (W k)) m → cell (univ : Set (W (k + 1))) m)
         (jc : ∀ k m, cell (univ : Set (W k)) m → cell (univ : Set X) m),
        (∀ k m c x, map m (ic k m c) x = i k (map m c x)) ∧
        ∀ k m c x, map m (jc k m c) x = j k (map m c x)) ∧
      (∀ m, Fintype.card σ - Fintype.card ι < m → IsEmpty (cell (univ : Set X) m)) ∧
      (∀ k m, Fintype.card σ - Fintype.card ι < m → IsEmpty (cell (univ : Set (W k)) m)) ∧
      (∀ m, Nonempty (cell (univ : Set X) m ≃
        ↥{y ∈ criticalPoints 𝓘(ℝ, Fin (Fintype.card σ - Fintype.card ι) → ℂ)
            (fun z : affineZeroLocus p ↦ ‖WithLp.toLp 2 (z : σ → ℂ) - a‖ ^ 2) |
          manifoldMorseIndex 𝓘(ℝ, Fin (Fintype.card σ - Fintype.card ι) → ℂ)
            (fun z : affineZeroLocus p ↦ ‖WithLp.toLp 2 (z : σ → ℂ) - a‖ ^ 2) y = m})) ∧
      ∀ k m, Nonempty (cell (univ : Set (W k)) m ≃
        ↥{y ∈ criticalPoints 𝓘(ℝ, Fin (Fintype.card σ - Fintype.card ι) → ℂ)
            (fun z : affineZeroLocus p ↦ ‖WithLp.toLp 2 (z : σ → ℂ) - a‖ ^ 2) ∩
            {y : affineZeroLocus p | ‖WithLp.toLp 2 (y : σ → ℂ) - a‖ ^ 2 ≤ r k} |
          manifoldMorseIndex 𝓘(ℝ, Fin (Fintype.card σ - Fintype.card ι) → ℂ)
            (fun z : affineZeroLocus p ↦ ‖WithLp.toLp 2 (z : σ → ℂ) - a‖ ^ 2) y = m}) := by
  let _ := affineZeroLocusChartedSpace hp
  have := isManifold_affineZeroLocus hp 1
  have hclosed : IsClosedEmbedding
      (fun y : affineZeroLocus p ↦ WithLp.toLp 2 (y : σ → ℂ)) :=
    (EuclideanSpace.equiv σ ℂ).symm.toHomeomorph.isClosedEmbedding.comp
      (isClosed_affineZeroLocus p).isClosedEmbedding_subtypeVal
  simpa only [Module.finrank_fin_fun] using
    exists_cwComplex_sublevel_homotopyEquiv_norm_sq_sub_comp
      ((contMDiff_toLp_coe_affineZeroLocus hp 1).mdifferentiable one_ne_zero)
      (injective_mvfderiv_toLp_coe_affineZeroLocus hp) hclosed.isProperMap

/-- **CW homotopy model of a smooth affine complete intersection** (Milnor, *Morse Theory*, Theorem
7.2). Let `p : ι → MvPolynomial σ ℂ` be a finite polynomial family whose Jacobian matrix is
surjective at every common zero. Then `affineZeroLocus p` is homotopy equivalent to a Hausdorff CW
complex with no cells in dimensions strictly greater than its complex dimension `|σ| - |ι|`. -/
theorem exists_cwComplex_homotopyEquiv_affineZeroLocus {σ : Type u} {ι : Type*}
    [Fintype σ] [Fintype ι] {p : ι → MvPolynomial σ ℂ}
    (hp : ∀ x ∈ affineZeroLocus p, Surjective (jacobiMatrixAt p x).mulVec) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      Nonempty (affineZeroLocus p ≃ₕ X) ∧
      ∀ k, Fintype.card σ - Fintype.card ι < k → IsEmpty (cell (univ : Set X) k) := by
  obtain ⟨_, _, X, _, _, _, h, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
      hdim, -⟩ :=
    exists_cwComplex_sublevel_homotopyEquiv_affineZeroLocus hp
  exact ⟨X, _, ‹_›, ‹_›, ⟨h.symm⟩, hdim⟩

/-- Every smooth affine complete intersection over `ℂ` has CW type. -/
theorem cwType_affineZeroLocus {σ : Type u} {ι : Type*} [Fintype σ] [Finite ι]
    {p : ι → MvPolynomial σ ℂ}
    (hp : ∀ x ∈ affineZeroLocus p, Surjective (jacobiMatrixAt p x).mulVec) :
    CWType (affineZeroLocus p) := by
  let := Fintype.ofFinite ι
  obtain ⟨X, _, _, _, ⟨h⟩, -⟩ := exists_cwComplex_homotopyEquiv_affineZeroLocus hp
  exact h.cwType

end AffineZeroLocus

end TauCeti

/-! ### `Manifold.IsImmersion` dot-notation forms -/

namespace Manifold.IsImmersion

variable {E : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) 1 M]

/-- **Andreotti–Frankel–Milnor CW theorem for `Manifold.IsImmersion` along a proper map.** If
`i : M → F` is a proper holomorphic `C^r` immersion (`r ≠ 0`) of a Hausdorff complex manifold into a
proper complex normed space, then `M` is homotopy equivalent to a Hausdorff CW complex with no cells
in dimensions strictly greater than `finrank ℂ E`. -/
theorem exists_cwComplex_homotopyEquiv_of_isProperMap [T2Space M] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℂ F] [ProperSpace F] {r : ℕ∞ω} {i : M → F}
    (hi : IsImmersion 𝓘(ℂ, E) 𝓘(ℂ, F) r i) (hr : r ≠ 0) (hip : IsProperMap i) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      Nonempty (M ≃ₕ X) ∧ ∀ k, finrank ℂ E < k → IsEmpty (cell (univ : Set X) k) :=
  TauCeti.exists_cwComplex_homotopyEquiv_of_isProperMap_holomorphic_immersion
    (hi.contMDiff.mdifferentiable hr)
    (fun x ↦ TauCeti.injective_mvfderiv_iff.2 (hi.mfderiv_injective hr x)) hip

/-- **Andreotti–Frankel–Milnor CW theorem for `Manifold.IsImmersion` along a closed embedding.** If
`i : M → F` is a holomorphic `C^r` immersion (`r ≠ 0`) into a finite-dimensional complex normed
space which is a closed embedding, then `M` is homotopy equivalent to a Hausdorff CW complex with no
cells in dimensions strictly greater than `finrank ℂ E`. -/
theorem exists_cwComplex_homotopyEquiv_of_isClosedEmbedding {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℂ F] [FiniteDimensional ℂ F] {r : ℕ∞ω} {i : M → F}
    (hi : IsImmersion 𝓘(ℂ, E) 𝓘(ℂ, F) r i) (hr : r ≠ 0) (hclosed : IsClosedEmbedding i) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      Nonempty (M ≃ₕ X) ∧ ∀ k, finrank ℂ E < k → IsEmpty (cell (univ : Set X) k) :=
  TauCeti.exists_cwComplex_homotopyEquiv_of_isClosedEmbedding (hi.contMDiff.mdifferentiable hr)
    (fun x ↦ TauCeti.injective_mvfderiv_iff.2 (hi.mfderiv_injective hr x)) hclosed

end Manifold.IsImmersion

/-! ### Checks -/

namespace TauCeti

section Checks

open AlgebraicTopology CategoryTheory Limits

/-- **Check: closed complex `n`-submanifolds of `ℂ^N`.** Any complex manifold charted on `Fin n → ℂ`
admitting a closed smooth holomorphic immersion into `Fin N → ℂ` is homotopy equivalent to a
Hausdorff CW complex of dimension at most `n`. -/
example {n N : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (Fin n → ℂ) M]
    [IsManifold 𝓘(ℂ, Fin n → ℂ) ∞ M] {i : M → Fin N → ℂ}
    (hi : Manifold.IsImmersion 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin N → ℂ) ∞ i)
    (hclosed : IsClosedEmbedding i) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      Nonempty (M ≃ₕ X) ∧ ∀ k, n < k → IsEmpty (cell (univ : Set X) k) := by
  obtain ⟨X, _, _, _, hX, hdim⟩ :=
    hi.exists_cwComplex_homotopyEquiv_of_isClosedEmbedding (by simp) hclosed
  exact ⟨X, _, ‹_›, ‹_›, hX, fun k hk ↦ hdim k (by rwa [Module.finrank_fin_fun])⟩

/-- **Check: smooth affine complex curves (`n = 1`).** Every complex curve charted on `ℂ` admitting
a closed holomorphic embedding into `Fin N → ℂ` has the homotopy type of a `1`-dimensional CW
complex. -/
example {N : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ∞ M]
    {i : M → Fin N → ℂ} (hi : Manifold.IsImmersion 𝓘(ℂ) 𝓘(ℂ, Fin N → ℂ) ∞ i)
    (hclosed : IsClosedEmbedding i) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      Nonempty (M ≃ₕ X) ∧ ∀ k, 1 < k → IsEmpty (cell (univ : Set X) k) := by
  obtain ⟨X, _, _, _, hX, hdim⟩ :=
    hi.exists_cwComplex_homotopyEquiv_of_isClosedEmbedding (by simp) hclosed
  exact ⟨X, _, ‹_›, ‹_›, hX, fun k hk ↦ hdim k (by rwa [Module.finrank_self])⟩

/-- The defining polynomial `z₀ z₁ - 1` of the smooth affine hyperbola `ℂ* ↪ ℂ²`. -/
private abbrev hyperbolaPoly : Unit → MvPolynomial (Fin 2) ℂ :=
  fun _ ↦ X 0 * X 1 - 1

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
  obtain ⟨X, _, _, _, ⟨h⟩, hdim⟩ :=
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
    let p : Unit → MvPolynomial (Fin 1) ℂ := fun _ ↦ X 0
    Nonempty (affineZeroLocus p) ∧
      ∃ (X : Type) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
        Nonempty (affineZeroLocus p ≃ₕ X) ∧ ∀ k, 0 < k → IsEmpty (cell (univ : Set X) k) := by
  intro p
  have hp : ∀ z ∈ affineZeroLocus p, Surjective (jacobiMatrixAt p z).mulVec := fun z _ ↦
    mulVec_surjective_jacobiMatrixAt_iff_exists_eval_pderiv_ne_zero.2 ⟨0, by simp [p]⟩
  obtain ⟨X, _, _, _, hX, hdim⟩ := exists_cwComplex_homotopyEquiv_affineZeroLocus hp
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
  obtain ⟨X, _, _, _, hX, hdim⟩ := exists_cwComplex_homotopyEquiv_affineZeroLocus hp
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
  obtain ⟨X₁, _, _, _, ⟨h₁⟩, hd₁⟩ :=
    exists_cwComplex_homotopyEquiv_of_isProperMap_of_isManifoldStronglyPseudoconvexAt hf₁ hp₁ hbdd₁
      hq₁
  obtain ⟨X₂, _, _, _, ⟨h₂⟩, hd₂⟩ :=
    exists_cwComplex_homotopyEquiv_of_isProperMap_of_isManifoldStronglyPseudoconvexAt hf₂ hp₂ hbdd₂
      hq₂
  exact ⟨X₁, X₂, _, _, ‹_›, ‹_›, ‹_›, ‹_›, ⟨h₁⟩, ⟨h₂⟩, ⟨h₁.symm.trans h₂⟩, hd₁, hd₂⟩

end Checks

end TauCeti
