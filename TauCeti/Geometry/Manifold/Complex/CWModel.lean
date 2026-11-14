/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Immersion
public import TauCeti.Geometry.Manifold.Complex.Analytic
public import TauCeti.Geometry.Manifold.Complex.Pseudoconvex.Morse
public import TauCeti.Geometry.Manifold.ContMDiff.Defs
public import TauCeti.Geometry.Manifold.Morse.CWModel.Proper
public import TauCeti.Geometry.Manifold.RegularValue.Polynomial

import TauCeti.AlgebraicTopology.Cellular.Dimension
import TauCeti.Topology.Maps.Proper.Basic
import TauCeti.Topology.Maps.Proper.Metric

/-!
# CW homotopy models for pseudoconvex complex manifolds and closed holomorphic embeddings

Let `M` be a Hausdorff complex manifold of complex dimension `n`. Combining the Morse CW exhaustion
theorem (`TauCeti.IsMorse.exists_cwComplex_subcomplex_homotopyEquiv`,
`TauCeti.IsMorse.exists_cwComplex_homotopyEquiv_of_manifoldMorseIndex_le`) with the Levi-form index
bounds and Morse approximation theory of complex manifolds upgrades the homological
Andreotti–Frankel vanishing theorems (`TauCeti.Geometry.Manifold.Complex.SublevelHomology` and
`TauCeti.Geometry.Manifold.Complex.ExhaustionHomology`) to cellular homotopy models:

* **Strongly `q`-pseudoconvex and strictly plurisubharmonic exhaustions:** A proper bounded-below
  real Morse function `f : M → ℝ` which is strongly `q`-pseudoconvex at its critical points yields a
  sublevel-filtered Hausdorff CW model `X ≃ₕ M` (`W k ≃ₕ {f ≤ a k}`) with one `m`-cell per critical
  point of real Morse index `m` and no cells in dimensions strictly above `n + q`
  (`TauCeti.IsMorse.exists_cwComplex_subcomplex_homotopyEquiv_of_isManifoldStronglyPseudoconvexAt`,
  `TauCeti.IsMorse.exists_cwComplex_homotopyEquiv_of_isManifoldStronglyPseudoconvexAt`). By strong
  Whitney Morse perturbation
  (`TauCeti.exists_isMorse_isProperMap_bddBelow_isManifoldStronglyPseudoconvexAt`), any smooth
  proper bounded-below everywhere strongly `q`-pseudoconvex exhaustion (not assumed Morse) gives a
  Hausdorff CW homotopy model of `M` of dimension at most `n + q`
  (`TauCeti.exists_cwComplex_homotopyEquiv_of_isProperMap_of_isManifoldStronglyPseudoconvexAt`), and
  of dimension at most `n` in the strictly plurisubharmonic case `q = 0` without assuming
  finite-dimensionality of the model space a priori
  (`TauCeti.exists_cwComplex_homotopyEquiv_of_isProperMap_of_isManifoldStrictlyPlurisubharmonicAt`).
* **Proper holomorphic immersions, closed holomorphic embeddings, and smooth affine complete
  intersections (Milnor, *Morse Theory*, Theorem 7.2):** Along a proper holomorphic immersion
  `i : M → F` into a proper complex inner product space, the squared distance `x ↦ ‖i x - a‖²` from
  some centre `a` is a proper bounded-below strictly plurisubharmonic Morse exhaustion, giving a
  sublevel-filtered CW model of `M` of dimension at most `n`
  (`TauCeti.exists_isMorse_cwComplex_subcomplex_homotopyEquiv_norm_sq_sub_comp`). Transporting along
  a complex-linear isomorphism to Euclidean space removes the inner-product hypothesis on `F` for
  arbitrary proper holomorphic immersions into proper complex normed spaces
  (`TauCeti.exists_cwComplex_homotopyEquiv_of_isProperMap_holomorphic_immersion`) and closed
  holomorphic embeddings into finite-dimensional complex normed spaces
  (`TauCeti.exists_cwComplex_homotopyEquiv_of_isClosedEmbedding`,
  `Manifold.IsImmersion.exists_cwComplex_homotopyEquiv_of_isClosedEmbedding`). Specializing to a
  polynomial family with surjective Jacobian at its common zeros shows that every smooth affine
  complete intersection `TauCeti.affineZeroLocus p ⊆ ℂ^σ` has the homotopy type of a Hausdorff CW
  complex of dimension at most `|σ| - |ι|`
  (`TauCeti.exists_cwComplex_homotopyEquiv_affineZeroLocus`).

## Main results

* `TauCeti.IsMorse.exists_cwComplex_subcomplex_homotopyEquiv_of_isManifoldStronglyPseudoconvexAt`,
  `TauCeti.IsMorse.exists_cwComplex_homotopyEquiv_of_isManifoldStronglyPseudoconvexAt`:
  sublevel-filtered and global CW homotopy models of dimension `≤ n + q` for strongly
  `q`-pseudoconvex Morse exhaustions.
* `TauCeti.exists_cwComplex_homotopyEquiv_of_isProperMap_of_isManifoldStronglyPseudoconvexAt`,
  `TauCeti.exists_cwComplex_homotopyEquiv_of_isProperMap_of_isManifoldStrictlyPlurisubharmonicAt`:
  CW homotopy models of dimension `≤ n + q` (and `≤ n` for `q = 0`) for smooth non-Morse
  exhaustions.
* `TauCeti.exists_isMorse_cwComplex_subcomplex_homotopyEquiv_norm_sq_sub_comp`: sublevel-filtered CW
  model of dimension `≤ n` from a generic squared-distance Morse exhaustion along a proper
  holomorphic immersion.
* `TauCeti.exists_cwComplex_homotopyEquiv_of_isProperMap_holomorphic_immersion`,
  `TauCeti.exists_cwComplex_homotopyEquiv_of_isClosedEmbedding`,
  `Manifold.IsImmersion.exists_cwComplex_homotopyEquiv_of_isClosedEmbedding`: Andreotti–Frankel /
  Milnor Theorem 7.2 CW homotopy models of dimension `≤ n` for proper holomorphic immersions and
  closed holomorphic embeddings.
* `TauCeti.exists_cwComplex_homotopyEquiv_affineZeroLocus`: CW homotopy model of dimension
  `≤ |σ| - |ι|` for a smooth affine complete intersection.

## Checks

* Signature checks matching the `Manifold.IsImmersion` closed-embedding CW bound and the chartwise
  `q`-positive Levi exhaustion CW bound.
* Concrete specializations to `ℂ` (no cells above dimension `1`), `0`-dimensional closed complex
  submanifolds (only `0`-cells), and the smooth affine hyperbola `{zw - 1 = 0} ⊆ ℂ²` (no cells above
  dimension `1`).
* Exhaustion-independent recovery of homology vanishing, PID top-homology freeness, and cohomology
  vanishing directly from the CW homotopy model via `TauCeti.AlgebraicTopology.Cellular.Dimension`.

## References

* A. Andreotti and T. Frankel, *The Lefschetz theorem on hyperplane sections*, Ann. of Math. (2)
  69 (1959), 713–717.
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Section 7, Theorem 7.2.
* R. Hain, *Notes on the Morse theory of complex manifolds*, Section 2.
-/

public section

noncomputable section

open AlgebraicTopology CategoryTheory ContMDiffMap Filter Function Limits Module MvPolynomial Set
  Topology Topology.CWComplex
open scoped ContDiff ContinuousMap Manifold Topology.Homotopy

universe u

namespace TauCeti

/-! ### Strongly `q`-pseudoconvex and strictly plurisubharmonic exhaustions -/

section StronglyPseudoconvex

variable {E : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] {r : ℕ∞ω} [hr : NeZero r] [hM : IsManifold 𝓘(ℂ, E) r M]
  [T2Space M]

include hr hM in
/-- **Sublevel-filtered CW model of a strongly `q`-pseudoconvex Morse exhaustion.** Let `f` be a
proper bounded-below real Morse function on a Hausdorff complex manifold `M` of complex dimension
`n`, strongly `q`-pseudoconvex at each of its critical points. Then `M` admits a Hausdorff CW model
`X ≃ₕ M` exhausted by finite CW subcomplexes `W k ≃ₕ {f ≤ a k}` at regular values `a k → ∞`, whose
`m`-cells correspond to the critical points of `f` of index `m` and which have no cells in
dimensions strictly above `n + q`. -/
theorem IsMorse.exists_cwComplex_subcomplex_homotopyEquiv_of_isManifoldStronglyPseudoconvexAt
    {f : M → ℝ} {q : ℕ} (hf : IsMorse 𝓘(ℝ, E) f) (hp : IsProperMap f) (hbdd : BddBelow (range f))
    (hq : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f, IsManifoldStronglyPseudoconvexAt E q f x) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X))
      (a : ℕ → ℝ) (W : ℕ → Subcomplex (univ : Set X)) (h : X ≃ₕ M)
      (hW : ∀ k, (W k : Set X) ≃ₕ {x | f x ≤ a k}),
      StrictMono a ∧ Tendsto a atTop atTop ∧ (∀ k, IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f (a k)) ∧
      Monotone W ∧ (⋃ k, (W k : Set X)) = univ ∧ (W 0 : Set X) = ∅ ∧
      (∀ k, RelCWComplex.Finite (W k : Set X)) ∧
      (∀ k (w : W k), (hW k w : M) = h w) ∧ (∀ k, MapsTo h.symm {x | f x ≤ a k} (W k)) ∧
      (∀ m, Nonempty (cell (univ : Set X) m ≃
        ↥{x ∈ criticalPoints 𝓘(ℝ, E) f | manifoldMorseIndex 𝓘(ℝ, E) f x = m})) ∧
      (∀ k m, Nonempty (cell (W k : Set X) m ≃
        ↥{x ∈ criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Iic (a k) |
          manifoldMorseIndex 𝓘(ℝ, E) f x = m})) ∧
      (∀ m, finrank ℂ E + q < m → IsEmpty (cell (univ : Set X) m)) ∧
      ∀ k m, finrank ℂ E + q < m → IsEmpty (cell (W k : Set X) m) := by
  have : IsManifold 𝓘(ℂ, E) 2 M := hM.of_ne_zero 2 hr.ne
  have : IsManifold 𝓘(ℝ, E) ∞ M := hM.restrictScalars_of_ne_zero ∞ hr.ne
  have hidx (x : M) (hx : x ∈ criticalPoints 𝓘(ℝ, E) f) :
      manifoldMorseIndex 𝓘(ℝ, E) f x ≤ finrank ℂ E + q :=
    (hq x hx).manifoldMorseIndex_le_of_mem_criticalPoints (hf.contMDiff x) hx
  obtain ⟨X, _, _, _, a, W, h, hW, hmono, htop, hreg, hWmono, hWuniv, hW0, hWfin, hWh, hsymm,
    hcell, hWcell⟩ := hf.exists_cwComplex_subcomplex_homotopyEquiv hp hbdd
  refine ⟨X, _, inferInstance, ‹_›, a, W, h, hW, hmono, htop, hreg, hWmono, hWuniv, hW0, hWfin,
    hWh, hsymm, hcell, hWcell, fun m hm ↦ ?_, fun k m hm ↦ ?_⟩
  · exact (hcell m).some.isEmpty_congr.2 ⟨fun ⟨x, hx, hxm⟩ ↦ not_lt_of_ge (hidx x hx) (hxm ▸ hm)⟩
  · exact (hWcell k m).some.isEmpty_congr.2
      ⟨fun ⟨x, hx, hxm⟩ ↦ not_lt_of_ge (hidx x hx.1) (hxm ▸ hm)⟩

include hr hM in
/-- **CW model of a strongly `q`-pseudoconvex Morse exhaustion.** If a Hausdorff complex manifold
`M` carries a proper bounded-below real Morse function strongly `q`-pseudoconvex at its critical
points, then `M` is homotopy equivalent to a Hausdorff CW complex with no cells in dimensions
strictly above `finrank ℂ E + q`. -/
theorem IsMorse.exists_cwComplex_homotopyEquiv_of_isManifoldStronglyPseudoconvexAt
    {f : M → ℝ} {q : ℕ} (hf : IsMorse 𝓘(ℝ, E) f) (hp : IsProperMap f) (hbdd : BddBelow (range f))
    (hq : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f, IsManifoldStronglyPseudoconvexAt E q f x) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      Nonempty (M ≃ₕ X) ∧ ∀ m, finrank ℂ E + q < m → IsEmpty (cell (univ : Set X) m) := by
  have : IsManifold 𝓘(ℂ, E) 2 M := hM.of_ne_zero 2 hr.ne
  have : IsManifold 𝓘(ℝ, E) ∞ M := hM.restrictScalars_of_ne_zero ∞ hr.ne
  exact hf.exists_cwComplex_homotopyEquiv_of_manifoldMorseIndex_le hp hbdd fun x hx ↦
    (hq x hx).manifoldMorseIndex_le_of_mem_criticalPoints (hf.contMDiff x) hx

include hr hM in
/-- **CW homotopy model of a manifold with a smooth strongly `q`-pseudoconvex exhaustion.** If a
Hausdorff complex manifold `M` of complex dimension `n` carries a smooth proper bounded-below
everywhere strongly `q`-pseudoconvex function `f : M → ℝ` (not assumed Morse), then `M` is homotopy
equivalent to a Hausdorff CW complex with no cells in dimensions strictly above `n + q`. -/
theorem exists_cwComplex_homotopyEquiv_of_isProperMap_of_isManifoldStronglyPseudoconvexAt
    {f : M → ℝ} {q : ℕ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f) (hp : IsProperMap f)
    (hbdd : BddBelow (range f)) (hq : ∀ x, IsManifoldStronglyPseudoconvexAt E q f x) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      Nonempty (M ≃ₕ X) ∧ ∀ m, finrank ℂ E + q < m → IsEmpty (cell (univ : Set X) m) := by
  have : IsManifold 𝓘(ℂ, E) ∞ M := hM.of_ne_zero ∞ hr.ne
  have : IsManifold 𝓘(ℝ, E) ∞ M := hM.restrictScalars_of_ne_zero ∞ hr.ne
  obtain ⟨g, hgm, hgp, hgbdd, -, hgidx, -⟩ :=
    exists_isMorse_isProperMap_bddBelow_isManifoldStronglyPseudoconvexAt hf hp hbdd hq
  exact hgm.exists_cwComplex_homotopyEquiv_of_manifoldMorseIndex_le hgp hgbdd hgidx

end StronglyPseudoconvex

section StrictlyPlurisubharmonic

variable {E : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] {r : ℕ∞ω} [hr : NeZero r] [hM : IsManifold 𝓘(ℂ, E) r M]
  [T2Space M]

include hr hM in
/-- **Sublevel-filtered CW model of a strictly plurisubharmonic Morse exhaustion.** If a Hausdorff
complex manifold `M` carries a proper bounded-below real Morse function strictly plurisubharmonic at
its critical points, then `M` admits a sublevel-filtered Hausdorff CW model `X ≃ₕ M` with one
`m`-cell per critical point of index `m` and no cells in dimensions strictly above `finrank ℂ E`
(without assuming finite-dimensionality of `E` a priori). -/
theorem IsMorse.exists_cwComplex_subcomplex_homotopyEquiv_of_isManifoldStrictlyPlurisubharmonicAt
    {f : M → ℝ} (hf : IsMorse 𝓘(ℝ, E) f) (hp : IsProperMap f) (hbdd : BddBelow (range f))
    (hpsh : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f, IsManifoldStrictlyPlurisubharmonicAt E f x) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X))
      (a : ℕ → ℝ) (W : ℕ → Subcomplex (univ : Set X)) (h : X ≃ₕ M)
      (hW : ∀ k, (W k : Set X) ≃ₕ {x | f x ≤ a k}),
      StrictMono a ∧ Tendsto a atTop atTop ∧ (∀ k, IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f (a k)) ∧
      Monotone W ∧ (⋃ k, (W k : Set X)) = univ ∧ (W 0 : Set X) = ∅ ∧
      (∀ k, RelCWComplex.Finite (W k : Set X)) ∧
      (∀ k (w : W k), (hW k w : M) = h w) ∧ (∀ k, MapsTo h.symm {x | f x ≤ a k} (W k)) ∧
      (∀ m, Nonempty (cell (univ : Set X) m ≃
        ↥{x ∈ criticalPoints 𝓘(ℝ, E) f | manifoldMorseIndex 𝓘(ℝ, E) f x = m})) ∧
      (∀ k m, Nonempty (cell (W k : Set X) m ≃
        ↥{x ∈ criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Iic (a k) |
          manifoldMorseIndex 𝓘(ℝ, E) f x = m})) ∧
      (∀ m, finrank ℂ E < m → IsEmpty (cell (univ : Set X) m)) ∧
      ∀ k m, finrank ℂ E < m → IsEmpty (cell (W k : Set X) m) := by
  rcases isEmpty_or_nonempty M with _ | _
  · obtain ⟨X, _, _, _, a, W, h, hW, hmono, htop, hreg, hWmono, hWuniv, hW0, hWfin, hWh, hsymm,
      hcell, hWcell⟩ := hf.exists_cwComplex_subcomplex_homotopyEquiv hp hbdd
    exact ⟨X, _, inferInstance, ‹_›, a, W, h, hW, hmono, htop, hreg, hWmono, hWuniv, hW0, hWfin,
      hWh, hsymm, hcell, hWcell,
      fun m _ ↦ (hcell m).some.isEmpty_congr.2 ⟨fun ⟨x, _⟩ ↦ isEmptyElim x⟩,
      fun k m _ ↦ (hWcell k m).some.isEmpty_congr.2 ⟨fun ⟨x, _⟩ ↦ isEmptyElim x⟩⟩
  have : WeaklyLocallyCompactSpace M := hp.weaklyLocallyCompactSpace
  have : FiniteDimensional ℂ E := .of_locallyCompact_manifold M 𝓘(ℂ, E)
  simpa only [Nat.add_zero] using
    hf.exists_cwComplex_subcomplex_homotopyEquiv_of_isManifoldStronglyPseudoconvexAt (r := r)
      (q := 0) hp hbdd fun x hx ↦ (hpsh x hx).isManifoldStronglyPseudoconvexAt 0

include hr hM in
/-- **CW model of a strictly plurisubharmonic Morse exhaustion.** If a Hausdorff complex manifold
`M` carries a proper bounded-below real Morse function strictly plurisubharmonic at its critical
points, then `M` is homotopy equivalent to a Hausdorff CW complex with no cells in dimensions
strictly above `finrank ℂ E`. -/
theorem IsMorse.exists_cwComplex_homotopyEquiv_of_isManifoldStrictlyPlurisubharmonicAt
    {f : M → ℝ} (hf : IsMorse 𝓘(ℝ, E) f) (hp : IsProperMap f) (hbdd : BddBelow (range f))
    (hpsh : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f, IsManifoldStrictlyPlurisubharmonicAt E f x) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      Nonempty (M ≃ₕ X) ∧ ∀ m, finrank ℂ E < m → IsEmpty (cell (univ : Set X) m) := by
  obtain ⟨X, _, _, _, -, -, h, -, -, -, -, -, -, -, -, -, -, -, -, hdim, -⟩ :=
    hf.exists_cwComplex_subcomplex_homotopyEquiv_of_isManifoldStrictlyPlurisubharmonicAt
      (r := r) hp hbdd hpsh
  exact ⟨X, _, inferInstance, ‹_›, ⟨h.symm⟩, hdim⟩

include hr hM in
/-- **CW homotopy model of a manifold with a smooth strictly plurisubharmonic exhaustion**
(in particular any Stein manifold). If a Hausdorff complex manifold `M` carries a smooth proper
bounded-below everywhere strictly plurisubharmonic function `f : M → ℝ` (not assumed Morse), then
`M` is homotopy equivalent to a Hausdorff CW complex with no cells in dimensions strictly above
`finrank ℂ E`. -/
theorem exists_cwComplex_homotopyEquiv_of_isProperMap_of_isManifoldStrictlyPlurisubharmonicAt
    {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f) (hp : IsProperMap f)
    (hbdd : BddBelow (range f)) (hpsh : ∀ x, IsManifoldStrictlyPlurisubharmonicAt E f x) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      Nonempty (M ≃ₕ X) ∧ ∀ m, finrank ℂ E < m → IsEmpty (cell (univ : Set X) m) := by
  rcases isEmpty_or_nonempty M with _ | _
  · exact ⟨PEmpty.{u + 1}, inferInstance, inferInstance, inferInstance,
      ⟨Homeomorph.empty.toHomotopyEquiv⟩, fun m _ ↦ ⟨fun j ↦ PEmpty.elim (map m j 0)⟩⟩
  have : WeaklyLocallyCompactSpace M := hp.weaklyLocallyCompactSpace
  have : FiniteDimensional ℂ E := .of_locallyCompact_manifold M 𝓘(ℂ, E)
  simpa only [Nat.add_zero] using
    exists_cwComplex_homotopyEquiv_of_isProperMap_of_isManifoldStronglyPseudoconvexAt (r := r)
      (q := 0) hf hp hbdd fun x ↦ (hpsh x).isManifoldStronglyPseudoconvexAt 0

end StrictlyPlurisubharmonic

/-! ### Proper holomorphic immersions, closed holomorphic embeddings, and affine zero loci -/

section HolomorphicImmersion

variable {E : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] {r : ℕ∞ω} [hr : NeZero r] [hM : IsManifold 𝓘(ℂ, E) r M]

include hr hM in
/-- **Sublevel-filtered CW model from squared distance along a proper holomorphic immersion**
(Milnor, *Morse Theory*, proof of Theorem 7.2). Let `i : M → F` be a proper holomorphic immersion of
a Hausdorff complex manifold `M` into a proper complex inner product space `F`. Then there is a
centre `a ∈ F` for which `x ↦ ‖i x - a‖²` is a proper real Morse exhaustion on `M`, together with a
Hausdorff CW model `X ≃ₕ M` exhausted by finite CW subcomplexes `W k ≃ₕ {x | ‖i x - a‖² ≤ b k}`,
whose `m`-cells correspond to the critical points of `‖i · - a‖²` of index `m` and which have no
cells in dimensions strictly above `finrank ℂ E`. -/
theorem exists_isMorse_cwComplex_subcomplex_homotopyEquiv_norm_sq_sub_comp [T2Space M]
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [ProperSpace F]
    {i : M → F} (hi : MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, F) i)
    (hinj : ∀ x, Injective (mvfderiv 𝓘(ℂ, E) i x)) (hip : IsProperMap i) :
    ∃ (a : F) (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X))
      (b : ℕ → ℝ) (W : ℕ → Subcomplex (univ : Set X)) (h : X ≃ₕ M)
      (hW : ∀ k, (W k : Set X) ≃ₕ {x | ‖i x - a‖ ^ 2 ≤ b k}),
      IsMorse 𝓘(ℝ, E) (fun x ↦ ‖i x - a‖ ^ 2) ∧
      IsProperMap (fun x ↦ ‖i x - a‖ ^ 2) ∧
      StrictMono b ∧ Tendsto b atTop atTop ∧
      (∀ k, IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) (fun x ↦ ‖i x - a‖ ^ 2) (b k)) ∧
      Monotone W ∧ (⋃ k, (W k : Set X)) = univ ∧ (W 0 : Set X) = ∅ ∧
      (∀ k, RelCWComplex.Finite (W k : Set X)) ∧
      (∀ k (w : W k), (hW k w : M) = h w) ∧
      (∀ k, MapsTo h.symm {x | ‖i x - a‖ ^ 2 ≤ b k} (W k)) ∧
      (∀ m, Nonempty (cell (univ : Set X) m ≃
        ↥{x ∈ criticalPoints 𝓘(ℝ, E) (fun y ↦ ‖i y - a‖ ^ 2) |
          manifoldMorseIndex 𝓘(ℝ, E) (fun y ↦ ‖i y - a‖ ^ 2) x = m})) ∧
      (∀ k m, Nonempty (cell (W k : Set X) m ≃
        ↥{x ∈ criticalPoints 𝓘(ℝ, E) (fun y ↦ ‖i y - a‖ ^ 2) ∩
            (fun y ↦ ‖i y - a‖ ^ 2) ⁻¹' Iic (b k) |
          manifoldMorseIndex 𝓘(ℝ, E) (fun y ↦ ‖i y - a‖ ^ 2) x = m})) ∧
      (∀ m, finrank ℂ E < m → IsEmpty (cell (univ : Set X) m)) ∧
      ∀ k m, finrank ℂ E < m → IsEmpty (cell (W k : Set X) m) := by
  have hchoice : ∃ a : F, IsMorse 𝓘(ℝ, E) (fun x ↦ ‖i x - a‖ ^ 2) ∧
      IsProperMap (fun x ↦ ‖i x - a‖ ^ 2) ∧ BddBelow (range fun x ↦ ‖i x - a‖ ^ 2) ∧
      ∀ x ∈ criticalPoints 𝓘(ℝ, E) (fun y ↦ ‖i y - a‖ ^ 2),
        IsManifoldStrictlyPlurisubharmonicAt E (fun y ↦ ‖i y - a‖ ^ 2) x := by
    rcases isEmpty_or_nonempty M with hE | _
    · refine ⟨0, ?_, (isProperMap_norm_sq_sub_comp_iff hi.continuous 0).2 hip,
        ⟨0, by rintro _ ⟨x, _⟩; exact isEmptyElim x⟩, fun x _ ↦ isEmptyElim x⟩
      rw [← isMorseOn_univ, univ_eq_empty_iff.2 hE]
      exact isMorseOn_empty
    have : WeaklyLocallyCompactSpace M := hip.weaklyLocallyCompactSpace
    have : FiniteDimensional ℂ E := .of_locallyCompact_manifold M 𝓘(ℂ, E)
    have : IsManifold 𝓘(ℂ, E) 1 M := hM.of_ne_zero 1 hr.ne
    have : IsManifold 𝓘(ℂ, E) ∞ M := hM.of_ne_zero ∞ hr.ne
    have hi' : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ∞ i := hi.contMDiff
    obtain ⟨a, ha, hap, hbdd, -⟩ :=
      exists_isMorse_isProperMap_bddBelow_and_manifoldMorseIndex_norm_sq_sub_comp_le hi' hinj hip
    exact ⟨a, ha, hap, hbdd, fun x _ ↦
      (isManifoldStrictlyPlurisubharmonicAt_norm_sq_sub_comp_iff ((hi' x).of_le (by simp))).2
        (hinj x)⟩
  obtain ⟨a, ha, hap, hbdd, hpsh⟩ := hchoice
  obtain ⟨X, _, _, _, b, W, h, hW, hmono, htop, hreg, hWmono, hWuniv, hW0, hWfin, hWh, hsymm,
    hcell, hWcell, hdim, hWdim⟩ :=
    ha.exists_cwComplex_subcomplex_homotopyEquiv_of_isManifoldStrictlyPlurisubharmonicAt
      (r := r) hap hbdd hpsh
  exact ⟨a, X, _, inferInstance, ‹_›, b, W, h, hW, ha, hap, hmono, htop, hreg, hWmono, hWuniv,
    hW0, hWfin, hWh, hsymm, hcell, hWcell, hdim, hWdim⟩

include hr hM in
/-- **Andreotti–Frankel / Milnor CW theorem for proper holomorphic immersions.** If a Hausdorff
complex manifold `M` admits a proper holomorphic immersion `i : M → F` into a proper complex normed
space `F` (not assumed to carry an inner product), then `M` is homotopy equivalent to a Hausdorff CW
complex with no cells in dimensions strictly above `finrank ℂ E`. -/
theorem exists_cwComplex_homotopyEquiv_of_isProperMap_holomorphic_immersion [T2Space M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [ProperSpace F]
    {i : M → F} (hi : MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, F) i)
    (hinj : ∀ x, Injective (mvfderiv 𝓘(ℂ, E) i x)) (hip : IsProperMap i) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      Nonempty (M ≃ₕ X) ∧ ∀ m, finrank ℂ E < m → IsEmpty (cell (univ : Set X) m) := by
  have : FiniteDimensional ℂ F := .of_locallyCompactSpace ℂ
  let G := EuclideanSpace ℂ (Fin (finrank ℂ F))
  have : FiniteDimensional ℝ G := Module.Finite.trans ℂ G
  let L : F ≃L[ℂ] G :=
    (LinearEquiv.ofFinrankEq F (Fin (finrank ℂ F) → ℂ)
      (Module.finrank_fin_fun ℂ).symm).toContinuousLinearEquiv.trans
      (EuclideanSpace.equiv (Fin (finrank ℂ F)) ℂ).symm
  have hLi : MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, G) (L ∘ i) :=
    (L.contDiff.contMDiff.mdifferentiable one_ne_zero).comp hi
  have hLinj (x : M) : Injective (mvfderiv 𝓘(ℂ, E) (L ∘ i) x) := by
    intro v w hvw
    simp only [mvfderiv_comp_apply_of_differentiableAt L.differentiableAt (hi x), L.fderiv] at hvw
    exact hinj x (L.injective hvw)
  have hLprop : IsProperMap (L ∘ i) := L.toHomeomorph.isClosedEmbedding.isProperMap.comp hip
  obtain ⟨_, X, _, _, _, -, -, h, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hdim, -⟩ :=
    exists_isMorse_cwComplex_subcomplex_homotopyEquiv_norm_sq_sub_comp (r := r) hLi hLinj hLprop
  exact ⟨X, _, inferInstance, ‹_›, ⟨h.symm⟩, hdim⟩

include hr hM in
/-- **Milnor's CW theorem for closed holomorphic embeddings** (Milnor, *Morse Theory*, Theorem 7.2).
Let `i : M → F` be a holomorphic map with injective differential at every point from a complex
manifold `M` into a finite-dimensional complex normed space `F`, which is a closed topological
embedding. Then `M` is homotopy equivalent to a Hausdorff CW complex with no cells in dimensions
strictly above `finrank ℂ E`. Neither Hausdorffness, second-countability, nor finite-dimensionality
of `E` is assumed separately: all follow from the closed immersion into `F`. -/
theorem exists_cwComplex_homotopyEquiv_of_isClosedEmbedding
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    {i : M → F} (hi : MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, F) i)
    (hinj : ∀ x, Injective (mvfderiv 𝓘(ℂ, E) i x)) (hclosed : IsClosedEmbedding i) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      Nonempty (M ≃ₕ X) ∧ ∀ m, finrank ℂ E < m → IsEmpty (cell (univ : Set X) m) := by
  have : T2Space M := hclosed.isEmbedding.t2Space
  have : FiniteDimensional ℝ F := Module.Finite.trans ℂ F
  exact exists_cwComplex_homotopyEquiv_of_isProperMap_holomorphic_immersion (r := r) hi hinj
    hclosed.isProperMap

/-- **Milnor's CW theorem for smooth affine complete intersections** (Milnor, *Morse Theory*,
Theorem 7.2). Let `p : ι → MvPolynomial σ ℂ` be a finite polynomial family whose Jacobian matrix is
surjective at every common zero in `TauCeti.affineZeroLocus p ⊆ ℂ^σ`. Then `affineZeroLocus p` has
the homotopy type of a Hausdorff CW complex with no cells in dimensions strictly above its complex
dimension `|σ| - |ι|`. -/
theorem exists_cwComplex_homotopyEquiv_affineZeroLocus {σ : Type u} {ι : Type*}
    [Fintype σ] [Fintype ι] {p : ι → MvPolynomial σ ℂ}
    (hp : ∀ x ∈ affineZeroLocus p, Surjective (jacobiMatrixAt p x).mulVec) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      Nonempty (affineZeroLocus p ≃ₕ X) ∧
      ∀ m, Fintype.card σ - Fintype.card ι < m → IsEmpty (cell (univ : Set X) m) := by
  let _ := affineZeroLocusChartedSpace hp
  have := isManifold_affineZeroLocus hp ∞
  obtain ⟨X, _, _, _, ⟨h⟩, hdim⟩ := exists_cwComplex_homotopyEquiv_of_isClosedEmbedding (r := ∞)
    ((contMDiff_coe_affineZeroLocus hp ∞).mdifferentiable (by simp))
    (fun x ↦ injective_mvfderiv_iff.2 (injective_mfderiv_coe_affineZeroLocus hp x))
    (isClosed_affineZeroLocus p).isClosedEmbedding_subtypeVal
  rw [Module.finrank_fin_fun] at hdim
  exact ⟨X, _, inferInstance, ‹_›, ⟨h⟩, hdim⟩

end HolomorphicImmersion

end TauCeti

namespace Manifold.IsImmersion

variable {E F : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [TopologicalSpace M] [ChartedSpace E M]
  {r : ℕ∞ω} [hr : NeZero r] [hM : IsManifold 𝓘(ℂ, E) r M] {i : M → F}

/-- **Proper holomorphic immersion CW bound (`Manifold.IsImmersion` form).** A proper holomorphic
`C^r` immersion (`r ≠ 0`) of a Hausdorff complex manifold `M` into a proper complex normed space
gives a Hausdorff CW homotopy model of `M` with no cells in dimensions strictly above
`finrank ℂ E`. -/
theorem exists_cwComplex_homotopyEquiv_of_isProperMap [T2Space M] [ProperSpace F]
    (hi : IsImmersion 𝓘(ℂ, E) 𝓘(ℂ, F) r i) (hip : IsProperMap i) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      Nonempty (M ≃ₕ X) ∧ ∀ m, finrank ℂ E < m → IsEmpty (cell (univ : Set X) m) :=
  TauCeti.exists_cwComplex_homotopyEquiv_of_isProperMap_holomorphic_immersion (r := r)
    (hi.contMDiff.mdifferentiable hr.ne)
    (fun x ↦ TauCeti.injective_mvfderiv_iff.2 (hi.mfderiv_injective hr.ne x)) hip

/-- **Closed holomorphic embedding CW bound (`Manifold.IsImmersion` form, Milnor Theorem 7.2).** A
closed holomorphic `C^r` immersion (`r ≠ 0`) of a complex manifold `M` into a finite-dimensional
complex normed space gives a Hausdorff CW homotopy model of `M` with no cells in dimensions strictly
above `finrank ℂ E`. -/
theorem exists_cwComplex_homotopyEquiv_of_isClosedEmbedding [FiniteDimensional ℂ F]
    (hi : IsImmersion 𝓘(ℂ, E) 𝓘(ℂ, F) r i) (hclosed : IsClosedEmbedding i) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      Nonempty (M ≃ₕ X) ∧ ∀ m, finrank ℂ E < m → IsEmpty (cell (univ : Set X) m) :=
  TauCeti.exists_cwComplex_homotopyEquiv_of_isClosedEmbedding (r := r)
    (hi.contMDiff.mdifferentiable hr.ne)
    (fun x ↦ TauCeti.injective_mvfderiv_iff.2 (hi.mfderiv_injective hr.ne x)) hclosed

end Manifold.IsImmersion

/-! ### Checks -/

namespace TauCeti

section Checks

/-- **Check (`closed_holomorphic_embedding_cw_bound`):** a closed holomorphic `C^∞` immersion of a
complex `n`-manifold into `ℂ^N` gives a CW homotopy model with no cells above dimension `n`. -/
example {n N : ℕ} (M : Type) [TopologicalSpace M] [ChartedSpace (Fin n → ℂ) M]
    [IsManifold 𝓘(ℂ, Fin n → ℂ) ∞ M] (i : M → (Fin N → ℂ))
    (hi : Manifold.IsImmersion 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin N → ℂ) ∞ i)
    (hc : IsClosedEmbedding i) :
    ∃ (K : Type) (t : TopologicalSpace K) (c : @CWComplex K t univ),
      Nonempty (@ContinuousMap.HomotopyEquiv M K _ t) ∧
      ∀ k, n < k → IsEmpty (@CWComplex.cell K t univ c k) := by
  obtain ⟨K, t, _, c, h, hdim⟩ := hi.exists_cwComplex_homotopyEquiv_of_isClosedEmbedding hc
  rw [Module.finrank_fin_fun] at hdim
  exact ⟨K, t, c, h, hdim⟩

/-- **Check (`q_positive_exhaustion_cw_bound`):** a proper bounded-below real function on a
Hausdorff complex `n`-manifold which is `C^∞` in every extended holomorphic chart and has positive
Levi diagonal on an `(n - q)`-dimensional complex subspace at each chart centre gives a CW homotopy
model with no cells above dimension `n + q`. -/
example {n : ℕ} (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace (Fin n → ℂ) M]
    [IsManifold 𝓘(ℂ, Fin n → ℂ) ∞ M] (q : ℕ) (hq : q ≤ n) (f : M → ℝ)
    (hf : ∀ x : M, ContDiffOn ℝ ∞ (f ∘ (extChartAt 𝓘(ℂ, Fin n → ℂ) x).symm)
      (extChartAt 𝓘(ℂ, Fin n → ℂ) x).target)
    (hp : IsProperMap f) (hb : BddBelow (range f))
    (hlevi : ∀ x : M, ∃ P : Submodule ℂ (Fin n → ℂ), n - q ≤ finrank ℂ P ∧ ∀ v ∈ P, v ≠ 0 →
      0 < (fderiv ℝ (fderiv ℝ (f ∘ (extChartAt 𝓘(ℂ, Fin n → ℂ) x).symm))
          (extChartAt 𝓘(ℂ, Fin n → ℂ) x x) v v +
        fderiv ℝ (fderiv ℝ (f ∘ (extChartAt 𝓘(ℂ, Fin n → ℂ) x).symm))
          (extChartAt 𝓘(ℂ, Fin n → ℂ) x x) (Complex.I • v) (Complex.I • v)) / 4) :
    ∃ (K : Type) (t : TopologicalSpace K) (c : @CWComplex K t univ),
      Nonempty (@ContinuousMap.HomotopyEquiv M K _ t) ∧
      ∀ k, n + q < k → IsEmpty (@CWComplex.cell K t univ c k) := by
  have : IsManifold 𝓘(ℝ, Fin n → ℂ) ∞ M := IsManifold.restrictScalars ℝ ‹_›
  have hf_smooth : ContMDiff 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ) ∞ f := fun x ↦ by
    have hd : ContDiffAt ℝ ∞ (f ∘ (chartAt (Fin n → ℂ) x).symm) (chartAt (Fin n → ℂ) x x) := by
      simpa using (hf x).contDiffAt
        ((isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x))
    have hc : ContinuousAt f x := by
      have heq : f =ᶠ[𝓝 x] (f ∘ (chartAt (Fin n → ℂ) x).symm) ∘ chartAt (Fin n → ℂ) x := by
        filter_upwards [(chartAt (Fin n → ℂ) x).open_source.mem_nhds (mem_chart_source _ x)]
          with y hy
        simp [(chartAt (Fin n → ℂ) x).left_inv hy]
      exact (hd.continuousAt.comp ((chartAt (Fin n → ℂ) x).continuousAt
        (mem_chart_source _ x))).congr heq.symm
    exact contMDiffAt_iff.2 ⟨hc, by simpa using hd.contDiffWithinAt⟩
  have hpos (x : M) : IsManifoldStronglyPseudoconvexAt (Fin n → ℂ) q f x := by
    obtain ⟨P, hP, hPpos⟩ := hlevi x
    rw [isManifoldStronglyPseudoconvexAt_iff, Module.finrank_fin_fun]
    refine ⟨P, by omega, fun v hv hv0 ↦ ?_⟩
    rw [manifoldLeviForm_def, re_leviForm_apply]
    simpa using hPpos v hv hv0
  obtain ⟨K, t, _, c, h, hdim⟩ :=
    exists_cwComplex_homotopyEquiv_of_isProperMap_of_isManifoldStronglyPseudoconvexAt (r := ∞)
      hf_smooth hp hb hpos
  rw [Module.finrank_fin_fun] at hdim
  exact ⟨K, t, c, h, hdim⟩

/-- **Check (`ℂ`):** the identity closed holomorphic embedding on `ℂ` produces a Hausdorff CW model
with no cells above dimension `1`. -/
example :
    ∃ (X : Type) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      Nonempty (ℂ ≃ₕ X) ∧ ∀ m, 1 < m → IsEmpty (cell (univ : Set X) m) := by
  simpa using exists_cwComplex_homotopyEquiv_of_isClosedEmbedding (E := ℂ) (F := ℂ) (r := ∞)
    mdifferentiable_id
    (fun _ ↦ injective_mvfderiv_iff.2 (by simpa using Function.injective_id)) .id

/-- **Check (zero-dimensional closed complex submanifold):** any closed complex submanifold `M`
modelled on a `0`-dimensional complex space has a Hausdorff CW model with only `0`-cells (`IsEmpty`
above dimension `0`). -/
example {E F : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [Subsingleton E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]
    {i : M → F} (hi : MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, F) i)
    (hclosed : IsClosedEmbedding i) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      Nonempty (M ≃ₕ X) ∧ ∀ m, 0 < m → IsEmpty (cell (univ : Set X) m) := by
  simpa [finrank_zero_of_subsingleton] using
    exists_cwComplex_homotopyEquiv_of_isClosedEmbedding (r := ∞) hi
      (fun _ _ _ _ ↦ Subsingleton.elim (α := E) _ _) hclosed

/-- **Check (smooth affine hyperbola `{zw - 1 = 0} ⊆ ℂ²`):** `ℂ*` embedded as the smooth affine
quadric `X 0 * X 1 - 1 = 0` in `ℂ²` has a Hausdorff CW homotopy model with no cells above dimension
`1`. -/
example :
    ∃ (X : Type) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      Nonempty (affineZeroLocus (fun _ : Unit ↦
        (MvPolynomial.X (0 : Fin 2) * MvPolynomial.X 1 - 1 : MvPolynomial (Fin 2) ℂ)) ≃ₕ X) ∧
      ∀ m, 1 < m → IsEmpty (cell (univ : Set X) m) := by
  let p : Unit → MvPolynomial (Fin 2) ℂ := fun _ ↦ MvPolynomial.X 0 * MvPolynomial.X 1 - 1
  have hp : ∀ x ∈ affineZeroLocus p, Surjective (jacobiMatrixAt p x).mulVec := by
    intro x hx
    have hx01 : x 0 * x 1 = 1 := by
      have h0 : eval x (p ()) = 0 := mem_affineZeroLocus.1 hx ()
      simpa [p, sub_eq_zero] using h0
    rw [mulVec_surjective_jacobiMatrixAt_iff_exists_eval_pderiv_ne_zero]
    exact ⟨0, by simp [p, right_ne_zero_of_mul_eq_one hx01]⟩
  simpa using exists_cwComplex_homotopyEquiv_affineZeroLocus hp

/-- **Check (exhaustion-independent homology, top freeness, and cohomology from the CW model):**
the CW homotopy model of a manifold with a strongly `q`-pseudoconvex exhaustion transfers vanishing
of singular homology above `n + q`, PID freeness of `H_{n+q}`, and vanishing of singular cohomology
above `n + q` directly via `ContinuousMap.HomotopyEquiv`, without referencing the exhaustion
again. -/
example {E : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M] [T2Space M]
    {f : M → ℝ} {q : ℕ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f) (hp : IsProperMap f)
    (hbdd : BddBelow (range f)) (hq : ∀ x, IsManifoldStronglyPseudoconvexAt E q f x)
    {k : Type u} [CommRing k] [NoZeroDivisors k] [IsPrincipalIdealRing k]
    [∀ V : ModuleCat.{u} k, HasProjectiveDimensionLE V 1]
    (V N : ModuleCat.{u} k) [Module.Projective k V] {m : ℕ} (hm : finrank ℂ E + q < m) :
    IsZero (((singularHomologyFunctor (ModuleCat.{u} k) m).obj V).obj (TopCat.of M)) ∧
    Module.Free k (((singularHomologyFunctor (ModuleCat.{u} k) (finrank ℂ E + q)).obj V).obj
      (TopCat.of M)) ∧
    IsZero ((TopCat.of M).singularCohomology V k N m) := by
  obtain ⟨X, _, _, _, ⟨h⟩, hdim⟩ :=
    exists_cwComplex_homotopyEquiv_of_isProperMap_of_isManifoldStronglyPseudoconvexAt (r := ∞)
      hf hp hbdd hq
  let e : M ≃ₕ (univ : Set X) := h.trans (Homeomorph.Set.univ X).symm.toHomotopyEquiv
  have : IsEmpty (cell (univ : Set X) (finrank ℂ E + q + 1)) := hdim _ (Nat.lt_succ_self _)
  exact ⟨e.isZero_singularHomology_of_isEmpty_cell_gt V hdim hm,
    e.free_singularHomology_of_isEmpty_cell_succ V (finrank ℂ E + q),
    e.isZero_singularCohomology_of_isEmpty_cell_gt V N hdim hm⟩

end Checks

end TauCeti
