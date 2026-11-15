/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Immersion
public import TauCeti.Geometry.Manifold.Complex.Pseudoconvex.Morse
public import TauCeti.Geometry.Manifold.Morse.CWModel.Proper
public import TauCeti.Geometry.Manifold.Morse.Inequalities
public import TauCeti.Geometry.Manifold.RegularValue.Polynomial
import Mathlib.Topology.Algebra.Module.FiniteDimension
import TauCeti.AlgebraicTopology.Cellular.Dimension
import TauCeti.Topology.CWComplex.Classical.Finite
import TauCeti.Topology.Maps.Proper.Metric

/-!
# CW homotopy models of pseudoconvex complex manifolds and closed complex submanifolds

On a complex manifold `M` of complex dimension `n`, a real Morse function `f` that is strongly
`q`-pseudoconvex at its critical points has real Morse index at most `n + q` at each of them
(`TauCeti.IsManifoldStronglyPseudoconvexAt.manifoldMorseIndex_le`). Crossing a critical level or a
compact regular band therefore attaches only cells of dimension at most `n + q`. Assembled across
compact sublevels and along proper exhaustions, this upgrades homological vanishing to genuine
cellular homotopy models:

* **Compact regular bands and sublevels.** For regular values `a ≤ b` of a strongly
  `q`-pseudoconvex Morse function `f` with compact band `f⁻¹[a, b]`, the sublevel `{f ≤ b}` has a
  finite relative CW homotopy model over `{f ≤ a}` with one `m`-cell for each critical point of
  index `m` in `(a, b]` and no cells in dimensions strictly above `n + q` (`IsMorse` theorem
  `exists_relCWComplex_homotopyEquiv_sublevel_of_isManifoldStronglyPseudoconvexAt`).
  Consequently, the relative Betti numbers of `({f ≤ b}, {f ≤ a})` and of the cobordism
  `(f⁻¹[a, b], f⁻¹(a))` vanish above degree `n + q`, and the Morse polynomial identity already holds
  from degree `n + q` onwards rather than only from the real dimension `2n` (`IsMorse` theorems
  `finrank_singularHomology_sublevelPair_eq_zero_of_isManifoldStronglyPseudoconvexAt` and
  `exists_sum_range_monomial_sublevelPair_eq_add_mul_of_isManifoldStronglyPseudoconvexAt`, together
  with their `bandPair` companions). Likewise, every compact regular sublevel `{f ≤ b}` has a
  finite CW homotopy model with no cells above dimension `n + q`
  (`TauCeti.IsMorse.exists_cwComplex_homotopyEquiv_sublevel_of_isManifoldStronglyPseudoconvexAt`).
* **Strongly `q`-pseudoconvex and strictly plurisubharmonic exhaustions.** When `f` is a proper
  bounded-below strongly `q`-pseudoconvex Morse exhaustion, `M` is homotopy equivalent to a
  finite-dimensional Hausdorff CW complex `X` with no cells above dimension `n + q`, exhausted by
  finite subcomplexes `W k` restricting to homotopy models of an exhausting sequence of regular
  sublevels `{f ≤ a k}`
  (`TauCeti.IsMorse.exists_cwComplex_subcomplex_homotopyEquiv_of_isManifoldStronglyPseudoconvexAt`,
  `TauCeti.IsMorse.exists_cwComplex_homotopyEquiv_of_isManifoldStronglyPseudoconvexAt`). When `f`
  is an arbitrary smooth (not necessarily Morse) proper bounded-below everywhere strongly
  `q`-pseudoconvex exhaustion, Morse perturbation
  (`TauCeti.exists_isMorse_isProperMap_bddBelow_isManifoldStronglyPseudoconvexAt`) still yields a
  finite-dimensional Hausdorff CW homotopy model of `M` with no cells above dimension `n + q`
  (`TauCeti.exists_cwComplex_homotopyEquiv_of_isProperMap_of_isManifoldStronglyPseudoconvexAt`),
  and in the strictly plurisubharmonic case `q = 0` with no cells above dimension `n`
  (`TauCeti.exists_cwComplex_homotopyEquiv_of_isProperMap_of_isManifoldStrictlyPlurisubharmonicAt`).
* **Proper holomorphic immersions, closed holomorphic embeddings, and smooth affine complete
  intersections (Milnor, Theorem 7.2).** Along a smooth proper holomorphic immersion `i : M → F`
  into a proper complex inner product space, the squared distance `x ↦ ‖i x - a‖²` from a generic
  centre `a` is a proper bounded-below Morse exhaustion of index at most `n`, giving a
  sublevel-compatible CW homotopy model of `M` of dimension at most `n`
  (`TauCeti.exists_cwComplex_subcomplex_homotopyEquiv_norm_sq_sub_comp_of_isProperMap`).
  Transporting along a continuous `ℂ`-linear equivalence to Euclidean space removes any choice of
  inner product on the ambient space: every complex `n`-manifold admitting a smooth proper
  holomorphic immersion — and in particular every closed holomorphic embedding — into a
  finite-dimensional complex normed space has the homotopy type of a Hausdorff CW complex with no
  cells above dimension `n`
  (`TauCeti.exists_cwComplex_homotopyEquiv_of_isProperMap_holomorphic_immersion`,
  `TauCeti.exists_cwComplex_homotopyEquiv_of_isClosedEmbedding`,
  `Manifold.IsImmersion.exists_cwComplex_homotopyEquiv_of_isProperMap`,
  `Manifold.IsImmersion.exists_cwComplex_homotopyEquiv_of_isClosedEmbedding`). Specializing to the
  common zero set in `ℂ^σ` of a polynomial family `p : ι → ℂ[X_σ]` with surjective Jacobian at
  every common zero gives a Hausdorff CW homotopy model of `affineZeroLocus p` with no cells above
  `|σ| - |ι|` (`TauCeti.exists_cwComplex_homotopyEquiv_affineZeroLocus`).

Because singular homology and cohomology are homotopy-invariant functors on `M`, these CW homotopy
equivalences `M ≃ₕ X` with no cells above degree `d` (`d = n + q` or `d = n`) exhibit the vanishing
of `H_k(M; R)` and `H^k(M; V, N)` for `k > d` and the freeness of `H_d(M; V)` over any principal
ideal domain as intrinsic topological properties of `M`, independent of any choice of exhaustion or
embedding, via `ContinuousMap.HomotopyEquiv.isZero_singularHomology_of_isEmpty_cell_gt`,
`ContinuousMap.HomotopyEquiv.isZero_singularCohomology_of_isEmpty_cell_gt`, and
`ContinuousMap.HomotopyEquiv.free_singularHomology_of_isEmpty_cell_succ`. Note that freeness of
`H_d(M; ℤ)` eliminates the `Ext` term in degree `d + 1` in the universal coefficient theorem,
forcing `H^{d+1}(M; ℤ) = 0`, whereas `H^d(M; ℤ)` itself can still contain torsion arising from
`Ext¹_ℤ(H_{d-1}(M; ℤ), ℤ)`.

## Main results

* `TauCeti.IsMorse.exists_relCWComplex_homotopyEquiv_sublevel_of_isManifoldStronglyPseudoconvexAt`
  and `TauCeti.IsMorse.exists_cwComplex_homotopyEquiv_sublevel_of_isManifoldStronglyPseudoconvexAt`:
  finite relative and absolute CW models of compact regular bands and sublevels of strongly
  `q`-pseudoconvex Morse functions, with no cells above `dim_ℂ E + q`.
* `IsMorse.finrank_singularHomology_sublevelPair_eq_zero_of_isManifoldStronglyPseudoconvexAt` and
  `IsMorse.exists_sum_range_monomial_sublevelPair_eq_add_mul_of_isManifoldStronglyPseudoconvexAt`
  (with `bandPair` companions): relative Betti vanishing and the Morse polynomial identity on
  compact regular bands, truncated at `dim_ℂ E + q`.
* `TauCeti.IsMorse.exists_cwComplex_subcomplex_homotopyEquiv_of_isManifoldStronglyPseudoconvexAt`
  and `TauCeti.exists_cwComplex_homotopyEquiv_of_isProperMap_of_isManifoldStronglyPseudoconvexAt`:
  CW homotopy models of dimension at most `dim_ℂ E + q` for Morse and arbitrary smooth strongly
  `q`-pseudoconvex exhaustions (and `q = 0` strictly plurisubharmonic specializations).
* `TauCeti.exists_cwComplex_homotopyEquiv_of_isProperMap_holomorphic_immersion`,
  `TauCeti.exists_cwComplex_homotopyEquiv_of_isClosedEmbedding`, and
  `TauCeti.exists_cwComplex_homotopyEquiv_affineZeroLocus`: Andreotti–Frankel / Milnor Theorem 7.2
  CW homotopy models of dimension at most the complex dimension for proper holomorphic immersions,
  closed holomorphic embeddings, and smooth affine complete intersections.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Sections 3, 5, and 7 (Theorems 3.5 and 7.2).
* A. Andreotti and T. Frankel, *The Lefschetz theorem on hyperplane sections*, Annals of
  Mathematics (2) 69 (1959), 713–717.
* A. Andreotti and H. Grauert, *Théorèmes de finitude pour la cohomologie des espaces complexes*,
  Bulletin de la Société Mathématique de France 90 (1962), 193–259.
* R. Hain, *Notes on the Morse theory of complex manifolds*, Section 2.
-/

public section

noncomputable section

open CategoryTheory Filter Function Limits Module Set Topology Topology.RelCWComplex
open Polynomial (monomial X)
open scoped ContDiff ContinuousMap Manifold Polynomial

universe u

namespace TauCeti

section Pseudoconvex

variable {E : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M] [T2Space M]

private local instance : FiniteDimensional ℝ E := Module.Finite.trans ℂ E

private local instance : IsManifold 𝓘(ℝ, E) ∞ M :=
  IsManifold.restrictScalars ℝ (inferInstance : IsManifold 𝓘(ℂ, E) ∞ M)

/-! ### Compact regular bands and sublevels -/

/-- **Relative finite CW model of a compact regular band of a strongly `q`-pseudoconvex Morse
function.** Let `f` be a real Morse function on a complex manifold of complex dimension `n`, `a ≤ b`
regular values with compact band `f⁻¹[a, b]`, and suppose `f` is strongly `q`-pseudoconvex at every
critical point in `{x | a < f x ≤ b}`. Then `{f ≤ b}` is homotopy equivalent, compatibly with the
inclusion of `{f ≤ a}`, to a finite CW complex `X` relative to the image of `{f ≤ a}`, whose
`m`-cells correspond to the critical points of index `m` in `(a, b]` and vanish for `m > n + q`. -/
theorem IsMorse.exists_relCWComplex_homotopyEquiv_sublevel_of_isManifoldStronglyPseudoconvexAt
    {f : M → ℝ} {q : ℕ} (hf : IsMorse 𝓘(ℝ, E) f) {a b : ℝ} (hab : a ≤ b)
    (hcompact : IsCompact (f ⁻¹' Icc a b)) (ha : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f a)
    (hb : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f b)
    (hq : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Ioc a b,
      IsManifoldStronglyPseudoconvexAt E q f x) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (j : C({x | f x ≤ a}, X))
      (_ : RelCWComplex (univ : Set X) (range j)) (h : X ≃ₕ {x | f x ≤ b}),
      RelCWComplex.Finite (univ : Set X) ∧ IsClosedEmbedding j ∧ (∀ x, (h (j x) : M) = x) ∧
      (∀ m, Nonempty (cell (univ : Set X) m ≃
        ↥{x ∈ criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Ioc a b | manifoldMorseIndex 𝓘(ℝ, E) f x = m})) ∧
      ∀ m, finrank ℂ E + q < m → IsEmpty (cell (univ : Set X) m) := by
  obtain ⟨X, _, _, j, _, h, hj, hh, ⟨e⟩⟩ :=
    hf.exists_relCWComplex_homotopyEquiv_sublevel hab hcompact ha hb
  have hS : (criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Ioc a b).Finite :=
    (hf.finite_criticalPoints_inter hcompact).subset
      (inter_subset_inter_right _ (preimage_mono Ioc_subset_Icc_self))
  have := finite_sigma_criticalPoints_inter hS
  have hfin : RelCWComplex.Finite (univ : Set X) :=
    RelCWComplex.finite_of_finite_cells (.of_equiv _ (Equiv.sigmaCongrRight e).symm)
  have hempty (m : ℕ) (hm : finrank ℂ E + q < m) : IsEmpty (cell (univ : Set X) m) :=
    ⟨fun c ↦ hm.not_ge <| (e m c).2.2 ▸
      (hq _ (e m c).2.1).manifoldMorseIndex_le_of_mem_criticalPoints
        (hf.contMDiff (e m c).1) (e m c).2.1.1⟩
  exact ⟨X, _, ‹_›, j, ‹_›, h, hfin, hj, hh, fun m ↦ ⟨e m⟩, hempty⟩

/-- **Finite CW model of a compact regular sublevel of a strongly `q`-pseudoconvex Morse
function.** If `b` is a regular value of a real Morse function `f` with compact sublevel `{f ≤ b}`
and `f` is strongly `q`-pseudoconvex at every critical point in `{f ≤ b}`, then `{f ≤ b}` is
homotopy equivalent to a finite Hausdorff CW complex whose `m`-cells correspond to the critical
points of index `m` in `{f ≤ b}` and vanish for `m > finrank ℂ E + q`. -/
theorem IsMorse.exists_cwComplex_homotopyEquiv_sublevel_of_isManifoldStronglyPseudoconvexAt
    {f : M → ℝ} {q : ℕ} (hf : IsMorse 𝓘(ℝ, E) f) {b : ℝ}
    (hb : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f b) (hcompact : IsCompact {x | f x ≤ b})
    (hq : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f ∩ {x | f x ≤ b},
      IsManifoldStronglyPseudoconvexAt E q f x) :
    ∃ (W : Type u) (_ : TopologicalSpace W) (_ : T2Space W) (_ : CWComplex (univ : Set W)),
      RelCWComplex.Finite (univ : Set W) ∧ Nonempty (W ≃ₕ {x | f x ≤ b}) ∧
      (∀ m, Nonempty (cell (univ : Set W) m ≃
        ↥{x ∈ criticalPoints 𝓘(ℝ, E) f ∩ {x | f x ≤ b} | manifoldMorseIndex 𝓘(ℝ, E) f x = m})) ∧
      ∀ m, finrank ℂ E + q < m → IsEmpty (cell (univ : Set W) m) := by
  obtain ⟨W, _, _, _, hfin, ⟨h⟩, he⟩ :=
    hf.exists_finite_cwComplex_homotopyEquiv_of_isCompact_sublevel hb hcompact
  have hempty (m : ℕ) (hm : finrank ℂ E + q < m) : IsEmpty (cell (univ : Set W) m) :=
    ⟨fun c ↦ hm.not_ge <| ((he m).some c).2.2 ▸
      (hq _ ((he m).some c).2.1).manifoldMorseIndex_le_of_mem_criticalPoints
        (hf.contMDiff ((he m).some c).1) ((he m).some c).2.1.1⟩
  exact ⟨W, _, ‹_›, ‹_›, hfin, ⟨h⟩, he, hempty⟩

/-- On a compact regular sublevel `{f ≤ b}` of a strongly `q`-pseudoconvex Morse function, the
Betti numbers over any nontrivial ring vanish above degree `finrank ℂ E + q`. -/
theorem IsMorse.bettiNumber_sublevel_eq_zero_of_isManifoldStronglyPseudoconvexAt
    {f : M → ℝ} {q : ℕ} (hf : IsMorse 𝓘(ℝ, E) f) {b : ℝ}
    (hb : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f b) (hcompact : IsCompact {x | f x ≤ b})
    (hq : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f ∩ {x | f x ≤ b},
      IsManifoldStronglyPseudoconvexAt E q f x)
    (k : Type u) [Ring k] [Nontrivial k] {j : ℕ} (hj : finrank ℂ E + q < j) :
    bettiNumber k {x | f x ≤ b} j = 0 := by
  obtain ⟨W, _, _, _, _, ⟨h⟩, -, hempty⟩ :=
    hf.exists_cwComplex_homotopyEquiv_sublevel_of_isManifoldStronglyPseudoconvexAt hb
      hcompact hq
  have hzero : IsZero (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) j).obj
      (ModuleCat.of k k)).obj (TopCat.of {x | f x ≤ b})) :=
    (h.symm.trans (Homeomorph.Set.univ W).symm.toHomotopyEquiv
      ).isZero_singularHomology_of_isEmpty_cell_gt (ModuleCat.of k k) hempty hj
  have := ModuleCat.isZero_iff_subsingleton.1 hzero
  rw [bettiNumber_def]
  exact finrank_zero_of_subsingleton

section BandInequalities

variable {k : Type u} [DivisionRing k] (V : ModuleCat.{u} k) [Module.Finite k V]

namespace IsMorse

/-- **Vanishing of relative Betti numbers of a strongly `q`-pseudoconvex regular band.** Across a
compact band `f⁻¹[a, b]` between regular values where `f` is strongly `q`-pseudoconvex at every
critical point in `(a, b]`, `dim Hⱼ({f ≤ b}, {f ≤ a}; V) = 0` for `j > finrank ℂ E + q`. -/
theorem finrank_singularHomology_sublevelPair_eq_zero_of_isManifoldStronglyPseudoconvexAt
    {f : M → ℝ} {q : ℕ} (hf : IsMorse 𝓘(ℝ, E) f) {a b : ℝ} (hab : a ≤ b)
    (hcompact : IsCompact (f ⁻¹' Icc a b)) (ha : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f a)
    (hb : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f b)
    (hq : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Ioc a b,
      IsManifoldStronglyPseudoconvexAt E q f x) {j : ℕ} (hj : finrank ℂ E + q < j) :
    finrank k ((sublevelPair f hab).singularHomology V j : ModuleCat k) = 0 :=
  hf.finrank_singularHomology_sublevelPair_eq_zero_of_manifoldMorseIndex_le V hab hcompact ha hb
    (fun x hx ↦ (hq x hx).manifoldMorseIndex_le_of_mem_criticalPoints (hf.contMDiff x) hx.1) hj

/-- **Vanishing of cobordism Betti numbers of a strongly `q`-pseudoconvex regular band.** Under the
same hypotheses, `dim Hⱼ(f⁻¹[a, b], f⁻¹(a); V) = 0` for `j > finrank ℂ E + q`. -/
theorem finrank_singularHomology_bandPair_eq_zero_of_isManifoldStronglyPseudoconvexAt
    {f : M → ℝ} {q : ℕ} (hf : IsMorse 𝓘(ℝ, E) f) {a b : ℝ} (hab : a ≤ b)
    (hcompact : IsCompact (f ⁻¹' Icc a b)) (ha : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f a)
    (hb : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f b)
    (hq : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Ioc a b,
      IsManifoldStronglyPseudoconvexAt E q f x) {j : ℕ} (hj : finrank ℂ E + q < j) :
    finrank k ((bandPair f hab).singularHomology V j : ModuleCat k) = 0 :=
  hf.finrank_singularHomology_bandPair_eq_zero_of_manifoldMorseIndex_le V hab hcompact ha hb
    (fun x hx ↦ (hq x hx).manifoldMorseIndex_le_of_mem_criticalPoints (hf.contMDiff x) hx.1) hj

/-- **Morse polynomial identity truncated at `finrank ℂ E + q` for a strongly `q`-pseudoconvex
regular band.** Across a compact regular band `f⁻¹[a, b]` where `f` is strongly `q`-pseudoconvex at
every critical point in `(a, b]`, for every `m ≥ finrank ℂ E + q` there is a polynomial `Q ∈ ℕ[X]`
supported in degrees `< m` such that `∑ᵢ₌₀ᵐ cᵢ dim V · Xⁱ = ∑ᵢ₌₀ᵐ bᵢ Xⁱ + (1 + X) Q`. -/
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
      ∀ i, m ≤ i → Q.coeff i = 0 :=
  hf.exists_sum_range_monomial_sublevelPair_eq_add_mul_of_manifoldMorseIndex_le V hab hcompact ha hb
    (fun x hx ↦ (hq x hx).manifoldMorseIndex_le_of_mem_criticalPoints (hf.contMDiff x) hx.1) hm

/-- **Morse polynomial identity truncated at `finrank ℂ E + q` for a strongly `q`-pseudoconvex
cobordism.** -/
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
      ∀ i, m ≤ i → Q.coeff i = 0 :=
  hf.exists_sum_range_monomial_bandPair_eq_add_mul_of_manifoldMorseIndex_le V hab hcompact ha hb
    (fun x hx ↦ (hq x hx).manifoldMorseIndex_le_of_mem_criticalPoints (hf.contMDiff x) hx.1) hm

end IsMorse

end BandInequalities

/-! ### CW homotopy models of strongly `q`-pseudoconvex and strictly plurisubharmonic exhaustions -/

/-- **Sublevel-compatible CW model of a strongly `q`-pseudoconvex Morse exhaustion.** Let `f` be a
proper bounded-below real Morse function on a Hausdorff complex `n`-manifold `M`, strongly
`q`-pseudoconvex at each of its critical points. Then `M` is homotopy equivalent via `h : X ≃ₕ M`
to a finite-dimensional Hausdorff CW complex `X` with one `m`-cell for each critical point of `f`
of index `m`, no cells in dimensions strictly above `n + q`, and an exhausting sequence of finite
subcomplexes `W k` restricting to homotopy equivalences `W k ≃ₕ {x | f x ≤ a k}` at regular levels
`a k → ∞`. -/
theorem IsMorse.exists_cwComplex_subcomplex_homotopyEquiv_of_isManifoldStronglyPseudoconvexAt
    {f : M → ℝ} {q : ℕ} (hf : IsMorse 𝓘(ℝ, E) f) (hp : IsProperMap f) (hbdd : BddBelow (range f))
    (hq : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f, IsManifoldStronglyPseudoconvexAt E q f x) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X))
      (h : X ≃ₕ M)
      (e : ∀ m, cell (univ : Set X) m ≃
        ↥{x ∈ criticalPoints 𝓘(ℝ, E) f | manifoldMorseIndex 𝓘(ℝ, E) f x = m})
      (a : ℕ → ℝ) (W : ℕ → Subcomplex (univ : Set X)),
      CWComplex.FiniteDimensional (univ : Set X) ∧
      (∀ m, finrank ℂ E + q < m → IsEmpty (cell (univ : Set X) m)) ∧
      StrictMono a ∧ Tendsto a atTop atTop ∧ (∀ k, IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f (a k)) ∧
      Monotone W ∧ ⋃ k, (W k : Set X) = univ ∧ (∀ k, RelCWComplex.Finite (W k : Set X)) ∧
      (∀ k m j, j ∈ (W k).I m ↔ f (e m j : M) ≤ a k) ∧
      (∀ k, MapsTo h.symm {x | f x ≤ a k} (W k)) ∧
      ∀ k, ∃ hW : (W k : Set X) ≃ₕ {x | f x ≤ a k}, ∀ w : W k, (hW w : M) = h w := by
  obtain ⟨X, _, _, _, h, e, a, W, hmono, htop, hreg, hWmono, hWiUnion, hWfin, hWI, hmaps, hW⟩ :=
    hf.exists_cwComplex_subcomplex_homotopyEquiv hp hbdd
  have hempty (m : ℕ) (hm : finrank ℂ E + q < m) : IsEmpty (cell (univ : Set X) m) :=
    ⟨fun j ↦ hm.not_ge <| (e m j).2.2 ▸
      (hq _ (e m j).2.1).manifoldMorseIndex_le_of_mem_criticalPoints
        (hf.contMDiff (e m j).1) (e m j).2.1⟩
  exact ⟨X, _, ‹_›, ‹_›, h, e, a, W,
    CWComplex.finiteDimensional_of_isEmpty_cell_gt (univ : Set X) hempty, hempty,
    hmono, htop, hreg, hWmono, hWiUnion, hWfin, hWI, hmaps, hW⟩

/-- **CW homotopy model of a strongly `q`-pseudoconvex Morse exhaustion.** A Hausdorff complex
`n`-manifold carrying a proper bounded-below real Morse function that is strongly `q`-pseudoconvex
at its critical points is homotopy equivalent to a finite-dimensional Hausdorff CW complex whose
`m`-cells correspond to the critical points of index `m` and vanish for `m > n + q`. -/
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

/-- **CW homotopy model of a strictly plurisubharmonic Morse exhaustion.** A Hausdorff complex
`n`-manifold carrying a proper bounded-below real Morse function that is strictly plurisubharmonic
at its critical points is homotopy equivalent to a finite-dimensional Hausdorff CW complex whose
`m`-cells correspond to the critical points of index `m` and vanish for `m > n`. -/
theorem IsMorse.exists_cwComplex_homotopyEquiv_of_isManifoldStrictlyPlurisubharmonicAt
    {f : M → ℝ} (hf : IsMorse 𝓘(ℝ, E) f) (hp : IsProperMap f) (hbdd : BddBelow (range f))
    (hpsh : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f, IsManifoldStrictlyPlurisubharmonicAt E f x) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      CWComplex.FiniteDimensional (univ : Set X) ∧ Nonempty (M ≃ₕ X) ∧
      (∀ m, Nonempty (cell (univ : Set X) m ≃
        ↥{x ∈ criticalPoints 𝓘(ℝ, E) f | manifoldMorseIndex 𝓘(ℝ, E) f x = m})) ∧
      ∀ m, finrank ℂ E < m → IsEmpty (cell (univ : Set X) m) := by
  simpa only [add_zero] using
    hf.exists_cwComplex_homotopyEquiv_of_isManifoldStronglyPseudoconvexAt (q := 0) hp hbdd
      fun x hx ↦ (hpsh x hx).isManifoldStronglyPseudoconvexAt 0

/-- **CW homotopy model of a smooth strongly `q`-pseudoconvex exhaustion.** If a Hausdorff complex
manifold `M` of complex dimension `n` carries a smooth proper bounded-below everywhere strongly
`q`-pseudoconvex function `f : M → ℝ` (not assumed to be Morse), then `M` has the homotopy type of
a finite-dimensional Hausdorff CW complex with no cells in dimensions strictly above `n + q`. -/
theorem exists_cwComplex_homotopyEquiv_of_isProperMap_of_isManifoldStronglyPseudoconvexAt
    {f : M → ℝ} {q : ℕ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f) (hp : IsProperMap f)
    (hbdd : BddBelow (range f)) (hq : ∀ x, IsManifoldStronglyPseudoconvexAt E q f x) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      CWComplex.FiniteDimensional (univ : Set X) ∧ Nonempty (M ≃ₕ X) ∧
      ∀ m, finrank ℂ E + q < m → IsEmpty (cell (univ : Set X) m) := by
  obtain ⟨g, hgm, hgp, hgbdd, -, hgidx, -⟩ :=
    exists_isMorse_isProperMap_bddBelow_isManifoldStronglyPseudoconvexAt hf hp hbdd hq
  obtain ⟨X, _, _, _, hfd, hX, -, hempty⟩ :=
    hgm.exists_cwComplex_homotopyEquiv_of_manifoldMorseIndex_le hgp hgbdd hgidx
  exact ⟨X, _, ‹_›, ‹_›, hfd, hX, hempty⟩

/-- **CW homotopy model of a smooth strictly plurisubharmonic exhaustion.** If a Hausdorff complex
manifold `M` of complex dimension `n` carries a smooth proper bounded-below everywhere strictly
plurisubharmonic function `f : M → ℝ` (not assumed to be Morse), then `M` has the homotopy type of
a finite-dimensional Hausdorff CW complex with no cells in dimensions strictly above `n`. -/
theorem exists_cwComplex_homotopyEquiv_of_isProperMap_of_isManifoldStrictlyPlurisubharmonicAt
    {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f) (hp : IsProperMap f)
    (hbdd : BddBelow (range f)) (hpsh : ∀ x, IsManifoldStrictlyPlurisubharmonicAt E f x) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      CWComplex.FiniteDimensional (univ : Set X) ∧ Nonempty (M ≃ₕ X) ∧
      ∀ m, finrank ℂ E < m → IsEmpty (cell (univ : Set X) m) := by
  simpa only [add_zero] using
    exists_cwComplex_homotopyEquiv_of_isProperMap_of_isManifoldStronglyPseudoconvexAt (q := 0) hf
      hp hbdd fun x ↦ (hpsh x).isManifoldStronglyPseudoconvexAt 0

end Pseudoconvex

/-! ### Proper holomorphic immersions, closed holomorphic embeddings, and affine zero loci -/

section ProperHolomorphicImmersion

/-- **Sublevel-compatible squared-distance CW model along a proper holomorphic immersion.** Let
`i : M → F` be a smooth proper holomorphic immersion of a Hausdorff complex `n`-manifold `M` into a
proper complex inner product space `F`. Then there exist a centre `a : F` for which
`ρ_a(x) = ‖i x - a‖²` is a proper bounded-below Morse function, a finite-dimensional Hausdorff CW
complex `X` with no cells above dimension `n`, a homotopy equivalence `h : X ≃ₕ M`, cell
bijections with the critical points of `ρ_a`, and an exhausting sequence of finite subcomplexes
`W k` restricting to homotopy models of the closed-ball preimages `{x | ‖i x - a‖² ≤ r k}`. -/
theorem exists_cwComplex_subcomplex_homotopyEquiv_norm_sq_sub_comp_of_isProperMap
    {E : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M] [T2Space M]
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [ProperSpace F]
    {i : M → F} (hi : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ∞ i)
    (hinj : ∀ x, Injective (mvfderiv 𝓘(ℂ, E) i x)) (hip : IsProperMap i) :
    ∃ (a : F) (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X))
      (h : X ≃ₕ M)
      (e : ∀ m, cell (univ : Set X) m ≃
        ↥{x ∈ criticalPoints 𝓘(ℝ, E) (fun y ↦ ‖i y - a‖ ^ 2) |
          manifoldMorseIndex 𝓘(ℝ, E) (fun y ↦ ‖i y - a‖ ^ 2) x = m})
      (r : ℕ → ℝ) (W : ℕ → Subcomplex (univ : Set X)),
      IsMorse 𝓘(ℝ, E) (fun y ↦ ‖i y - a‖ ^ 2) ∧
      CWComplex.FiniteDimensional (univ : Set X) ∧
      (∀ m, finrank ℂ E < m → IsEmpty (cell (univ : Set X) m)) ∧
      StrictMono r ∧ Tendsto r atTop atTop ∧
      (∀ k, IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) (fun y ↦ ‖i y - a‖ ^ 2) (r k)) ∧
      Monotone W ∧ ⋃ k, (W k : Set X) = univ ∧ (∀ k, RelCWComplex.Finite (W k : Set X)) ∧
      (∀ k m j, j ∈ (W k).I m ↔ ‖i (e m j : M) - a‖ ^ 2 ≤ r k) ∧
      (∀ k, MapsTo h.symm {x | ‖i x - a‖ ^ 2 ≤ r k} (W k)) ∧
      ∀ k, ∃ hW : (W k : Set X) ≃ₕ {x | ‖i x - a‖ ^ 2 ≤ r k}, ∀ w : W k, (hW w : M) = h w := by
  have : FiniteDimensional ℝ E := Module.Finite.trans ℂ E
  have : IsManifold 𝓘(ℝ, E) ∞ M :=
    IsManifold.restrictScalars ℝ (inferInstance : IsManifold 𝓘(ℂ, E) ∞ M)
  obtain ⟨a, hmorse, hap, hbdd, hidx⟩ :=
    exists_isMorse_isProperMap_bddBelow_and_manifoldMorseIndex_norm_sq_sub_comp_le hi hinj hip
  obtain ⟨X, _, _, _, h, e, r, W, hmono, htop, hreg, hWmono, hWiUnion, hWfin, hWI, hmaps, hW⟩ :=
    hmorse.exists_cwComplex_subcomplex_homotopyEquiv hap hbdd
  have hempty (m : ℕ) (hm : finrank ℂ E < m) : IsEmpty (cell (univ : Set X) m) :=
    ⟨fun j ↦ hm.not_ge <| (e m j).2.2 ▸ hidx _ (e m j).2.1⟩
  exact ⟨a, X, _, ‹_›, ‹_›, h, e, r, W, hmorse,
    CWComplex.finiteDimensional_of_isEmpty_cell_gt (univ : Set X) hempty, hempty,
    hmono, htop, hreg, hWmono, hWiUnion, hWfin, hWI, hmaps, hW⟩

/-- **Andreotti–Frankel / Milnor theorem for proper holomorphic immersions.** If a Hausdorff
complex manifold `M` modeled on `E` admits a smooth proper holomorphic immersion into a
finite-dimensional complex normed space `F`, then `M` has the homotopy type of a finite-dimensional
Hausdorff CW complex with no cells in dimensions strictly above `finrank ℂ E`. -/
theorem exists_cwComplex_homotopyEquiv_of_isProperMap_holomorphic_immersion
    {E : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M] [T2Space M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    {i : M → F} (hi : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ∞ i)
    (hinj : ∀ x, Injective (mvfderiv 𝓘(ℂ, E) i x)) (hip : IsProperMap i) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      CWComplex.FiniteDimensional (univ : Set X) ∧ Nonempty (M ≃ₕ X) ∧
      ∀ m, finrank ℂ E < m → IsEmpty (cell (univ : Set X) m) := by
  rcases isEmpty_or_nonempty M with hM | ⟨⟨x₀⟩⟩
  · have hempty (m : ℕ) : IsEmpty (cell (univ : Set PEmpty.{u + 1}) m) :=
      ⟨fun j ↦ PEmpty.elim (map m j 0)⟩
    exact ⟨PEmpty.{u + 1}, inferInstance, inferInstance, CWComplex.ofDiscreteTopology,
      CWComplex.finiteDimensional_of_isEmpty_cell_gt (d := 0) (univ : Set PEmpty.{u + 1})
        fun m _ ↦ hempty m,
      ⟨Homeomorph.empty.toHomotopyEquiv⟩, fun m _ ↦ hempty m⟩
  have : FiniteDimensional ℂ E :=
    Module.Finite.of_injective (mvfderiv 𝓘(ℂ, E) i x₀).toLinearMap (hinj x₀)
  have : IsManifold 𝓘(ℂ, E) 2 M := .of_le (n := ∞) (by simp)
  -- Identify `F` with a complex Euclidean space via a continuous `ℂ`-linear equivalence.
  let L : F ≃L[ℂ] EuclideanSpace ℂ (Fin (finrank ℂ F)) :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
  have hLi : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, EuclideanSpace ℂ (Fin (finrank ℂ F))) ∞ (L ∘ i) :=
    L.contDiff.contMDiff.comp hi
  have hLinj (x : M) : Injective (mvfderiv 𝓘(ℂ, E) (L ∘ i) x) := by
    intro v w hvw
    have hmd : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, F) i x :=
      ((hi x).of_le (by simp : (2 : ℕ∞ω) ≤ ∞)).mdifferentiableAt two_ne_zero
    simp only [mvfderiv_comp_apply_of_differentiableAt L.differentiableAt hmd, L.fderiv] at hvw
    exact hinj x (L.injective hvw)
  have hLprop : IsProperMap (L ∘ i) := L.toHomeomorph.isProperMap.comp hip
  have : FiniteDimensional ℝ (EuclideanSpace ℂ (Fin (finrank ℂ F))) :=
    Module.Finite.trans ℂ _
  obtain ⟨-, X, _, _, _, h, -, -, -, -, hfd, hempty, -⟩ :=
    exists_cwComplex_subcomplex_homotopyEquiv_norm_sq_sub_comp_of_isProperMap hLi hLinj hLprop
  exact ⟨X, _, ‹_›, ‹_›, hfd, ⟨h.symm⟩, hempty⟩

/-- **Milnor's Theorem 7.2 (Andreotti–Frankel theorem for closed holomorphic embeddings).** Let
`i : M → F` be a smooth holomorphic immersion of a complex manifold `M` modeled on `E` into a
finite-dimensional complex normed space `F`, which is a closed topological embedding. Then `M` has
the homotopy type of a finite-dimensional Hausdorff CW complex with no cells in dimensions strictly
above `finrank ℂ E`. -/
theorem exists_cwComplex_homotopyEquiv_of_isClosedEmbedding
    {E : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    {i : M → F} (hi : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ∞ i)
    (hinj : ∀ x, Injective (mvfderiv 𝓘(ℂ, E) i x)) (hclosed : IsClosedEmbedding i) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      CWComplex.FiniteDimensional (univ : Set X) ∧ Nonempty (M ≃ₕ X) ∧
      ∀ m, finrank ℂ E < m → IsEmpty (cell (univ : Set X) m) := by
  have : T2Space M := hclosed.isEmbedding.t2Space
  have : FiniteDimensional ℝ F := Module.Finite.trans ℂ F
  exact exists_cwComplex_homotopyEquiv_of_isProperMap_holomorphic_immersion hi hinj
    hclosed.isProperMap

/-- **Sublevel-compatible squared-distance CW model of a smooth affine complete intersection.** Let
`p : ι → ℂ[X_σ]` have surjective Jacobian at every point of `affineZeroLocus p`. Then for some
centre `a ∈ ℂ^σ`, the Euclidean squared distance `y ↦ ‖toLp 2 y - a‖²` on `affineZeroLocus p` is a
Morse exhaustion inducing a finite-dimensional Hausdorff CW homotopy model
`h : X ≃ₕ affineZeroLocus p` with no cells above dimension `|σ| - |ι|` and an exhausting sequence
of finite subcomplexes `W k` modeling the closed-ball intersections
`{y ∈ affineZeroLocus p | ‖toLp 2 y - a‖² ≤ r k}`. -/
theorem exists_cwComplex_subcomplex_homotopyEquiv_norm_sq_sub_toLp_affineZeroLocus
    {σ : Type u} {ι : Type*} [Fintype σ] [Fintype ι] {p : ι → MvPolynomial σ ℂ}
    (hp : ∀ x ∈ affineZeroLocus p, Surjective (jacobiMatrixAt p x).mulVec) :
    letI := affineZeroLocusChartedSpace hp
    ∃ (a : EuclideanSpace ℂ σ) (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X)
      (_ : CWComplex (univ : Set X)) (h : X ≃ₕ affineZeroLocus p)
      (e : ∀ m, cell (univ : Set X) m ≃
        ↥{x ∈ criticalPoints 𝓘(ℝ, Fin (Fintype.card σ - Fintype.card ι) → ℂ)
            (fun y : affineZeroLocus p ↦ ‖WithLp.toLp 2 (y : σ → ℂ) - a‖ ^ 2) |
          manifoldMorseIndex 𝓘(ℝ, Fin (Fintype.card σ - Fintype.card ι) → ℂ)
            (fun y : affineZeroLocus p ↦ ‖WithLp.toLp 2 (y : σ → ℂ) - a‖ ^ 2) x = m})
      (r : ℕ → ℝ) (W : ℕ → Subcomplex (univ : Set X)),
      IsMorse 𝓘(ℝ, Fin (Fintype.card σ - Fintype.card ι) → ℂ)
        (fun y : affineZeroLocus p ↦ ‖WithLp.toLp 2 (y : σ → ℂ) - a‖ ^ 2) ∧
      CWComplex.FiniteDimensional (univ : Set X) ∧
      (∀ m, Fintype.card σ - Fintype.card ι < m → IsEmpty (cell (univ : Set X) m)) ∧
      StrictMono r ∧ Tendsto r atTop atTop ∧
      (∀ k, IsRegularValue 𝓘(ℝ, Fin (Fintype.card σ - Fintype.card ι) → ℂ) 𝓘(ℝ)
        (fun y : affineZeroLocus p ↦ ‖WithLp.toLp 2 (y : σ → ℂ) - a‖ ^ 2) (r k)) ∧
      Monotone W ∧ ⋃ k, (W k : Set X) = univ ∧ (∀ k, RelCWComplex.Finite (W k : Set X)) ∧
      (∀ k m j, j ∈ (W k).I m ↔
        ‖WithLp.toLp 2 ((e m j : affineZeroLocus p) : σ → ℂ) - a‖ ^ 2 ≤ r k) ∧
      (∀ k, MapsTo h.symm
        {y : affineZeroLocus p | ‖WithLp.toLp 2 (y : σ → ℂ) - a‖ ^ 2 ≤ r k} (W k)) ∧
      ∀ k, ∃ hW : (W k : Set X) ≃ₕ
          {y : affineZeroLocus p | ‖WithLp.toLp 2 (y : σ → ℂ) - a‖ ^ 2 ≤ r k},
        ∀ w : W k, (hW w : affineZeroLocus p) = h w := by
  let _ := affineZeroLocusChartedSpace hp
  have := isManifold_affineZeroLocus hp ∞
  have : FiniteDimensional ℝ (EuclideanSpace ℂ σ) := Module.Finite.trans ℂ _
  have hclosed : IsClosedEmbedding (fun y : affineZeroLocus p ↦ WithLp.toLp 2 (y : σ → ℂ)) :=
    (EuclideanSpace.equiv σ ℂ).symm.toHomeomorph.isClosedEmbedding.comp
      (isClosed_affineZeroLocus p).isClosedEmbedding_subtypeVal
  simpa only [Module.finrank_fin_fun] using
    exists_cwComplex_subcomplex_homotopyEquiv_norm_sq_sub_comp_of_isProperMap
      (contMDiff_toLp_coe_affineZeroLocus hp ∞) (injective_mvfderiv_toLp_coe_affineZeroLocus hp)
      hclosed.isProperMap

/-- **CW homotopy model of a smooth affine complete intersection.** Let `X ⊆ ℂ^σ` be the common
zero set of a polynomial family `p : ι → ℂ[X_σ]` whose Jacobian is surjective at every common zero,
a complex manifold of dimension `|σ| - |ι|`. Then `affineZeroLocus p` has the homotopy type of a
finite-dimensional Hausdorff CW complex with no cells in dimensions strictly above
`|σ| - |ι|`. -/
theorem exists_cwComplex_homotopyEquiv_affineZeroLocus
    {σ : Type u} {ι : Type*} [Fintype σ] [Fintype ι] {p : ι → MvPolynomial σ ℂ}
    (hp : ∀ x ∈ affineZeroLocus p, Surjective (jacobiMatrixAt p x).mulVec) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      CWComplex.FiniteDimensional (univ : Set X) ∧ Nonempty (affineZeroLocus p ≃ₕ X) ∧
      ∀ m, Fintype.card σ - Fintype.card ι < m → IsEmpty (cell (univ : Set X) m) := by
  let _ := affineZeroLocusChartedSpace hp
  have := isManifold_affineZeroLocus hp ∞
  have hclosed : IsClosedEmbedding (fun y : affineZeroLocus p ↦ (y : σ → ℂ)) :=
    (isClosed_affineZeroLocus p).isClosedEmbedding_subtypeVal
  simpa only [Module.finrank_fin_fun] using
    exists_cwComplex_homotopyEquiv_of_isClosedEmbedding (contMDiff_coe_affineZeroLocus hp ∞)
      (fun x ↦ injective_mvfderiv_iff.2 (injective_mfderiv_coe_affineZeroLocus hp x)) hclosed

end ProperHolomorphicImmersion

end TauCeti

namespace Manifold.IsImmersion

/-- **CW homotopy model of a proper holomorphic immersion.** If `i : M → F` is a smooth proper
holomorphic immersion of a Hausdorff complex manifold `M` modeled on `E` into a finite-dimensional
complex normed space `F`, then `M` has the homotopy type of a finite-dimensional Hausdorff CW
complex with no cells in dimensions strictly above `Module.finrank ℂ E`. -/
theorem exists_cwComplex_homotopyEquiv_of_isProperMap
    {E : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M] [T2Space M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    {i : M → F} (hi : IsImmersion 𝓘(ℂ, E) 𝓘(ℂ, F) ∞ i) (hip : IsProperMap i) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      CWComplex.FiniteDimensional (univ : Set X) ∧ Nonempty (M ≃ₕ X) ∧
      ∀ m, Module.finrank ℂ E < m → IsEmpty (RelCWComplex.cell (univ : Set X) m) :=
  TauCeti.exists_cwComplex_homotopyEquiv_of_isProperMap_holomorphic_immersion hi.contMDiff
    (fun x ↦ TauCeti.injective_mvfderiv_iff.2 (hi.mfderiv_injective (by simp) x)) hip

/-- **Milnor's Theorem 7.2 for closed holomorphic immersions.** If `i : M → F` is a smooth
holomorphic immersion of a complex manifold `M` modeled on `E` into a finite-dimensional complex
normed space `F` that is also a closed topological embedding, then `M` has the homotopy type of a
finite-dimensional Hausdorff CW complex with no cells in dimensions strictly above
`Module.finrank ℂ E`. -/
theorem exists_cwComplex_homotopyEquiv_of_isClosedEmbedding
    {E : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    {i : M → F} (hi : IsImmersion 𝓘(ℂ, E) 𝓘(ℂ, F) ∞ i) (hclosed : IsClosedEmbedding i) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      CWComplex.FiniteDimensional (univ : Set X) ∧ Nonempty (M ≃ₕ X) ∧
      ∀ m, Module.finrank ℂ E < m → IsEmpty (RelCWComplex.cell (univ : Set X) m) :=
  TauCeti.exists_cwComplex_homotopyEquiv_of_isClosedEmbedding hi.contMDiff
    (fun x ↦ TauCeti.injective_mvfderiv_iff.2 (hi.mfderiv_injective (by simp) x)) hclosed

end Manifold.IsImmersion
