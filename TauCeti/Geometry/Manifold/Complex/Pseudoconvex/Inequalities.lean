/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.Analytic
public import TauCeti.Geometry.Manifold.Complex.LeviForm
public import TauCeti.Geometry.Manifold.ContMDiff.Defs
public import TauCeti.Geometry.Manifold.Morse.Inequalities

/-!
# Morse inequalities and Betti bounds for pseudoconvex Morse functions

Let `f` be a real Morse function on a Hausdorff complex manifold `M` of complex dimension `n`
(and real dimension `2n`), and let `V` be a finite-dimensional module over a division ring `k`. If
`f` is strongly `q`-pseudoconvex at every critical point in a compact regular band `f⁻¹[a, b]` (or
in a compact regular sublevel `{f ≤ b}`, without assuming `M` is compact), then every critical point
there has real Morse index at most `n + q`
(`TauCeti.IsManifoldStronglyPseudoconvexAt.manifoldMorseIndex_le`). Combining this complex-geometric
index bound with the index-bounded Morse inequalities of
`TauCeti/Geometry/Manifold/Morse/Inequalities.lean` yields:

* **Vanishing above `n + q`:** `dim Hₘ({f ≤ b}, {f ≤ a}; V) = 0`, `dim Hₘ({f ≤ b}; V) = 0`, and
  `bettiNumber k {f ≤ b} m = 0` for every `m > n + q`.
* **Euler's equality from degree `n + q` onwards:** the alternating sum of Betti dimensions equals
  `dim V` times the alternating sum of critical counts already in every degree `m ≥ n + q`, rather
  than only from the real dimension `2n` onwards.
* **The Morse polynomial identity from degree `n + q` onwards:**
  `∑ᵢ₌₀ᵐ cᵢ dim V · tⁱ = ∑ᵢ₌₀ᵐ bᵢ tⁱ + (1 + t) Q(t)` for `Q ∈ ℕ[X]` with `deg Q < m`, for every
  `m ≥ n + q`.

Specializing to `q = 0` gives the strictly plurisubharmonic counterparts, where homology vanishes
above the middle real dimension `n` and Euler's equality and the Morse polynomial identity stabilize
at `n`. Complex analyticity (`IsManifold.of_ne_zero`) allows the manifold hypothesis to be stated at
any regularity `r ≠ 0` (`C¹`, `C²`, `C^∞`, or `C^ω`).

## Main results

* `IsMorse.finrank_singularHomology_sublevelPair_eq_zero_of_isManifoldStronglyPseudoconvexAt`,
  `IsMorse.sum_range_neg_one_pow_mul_finrank_sublevelPair_eq_of_isManifoldStronglyPseudoconvexAt`,
  `IsMorse.exists_sum_range_monomial_sublevelPair_eq_add_mul_of_isManifoldStronglyPseudoconvexAt`:
  band Betti vanishing, Euler's equality, and the Morse polynomial identity from degree
  `finrank ℂ E + q` onwards, with strictly plurisubharmonic (`q = 0`) specializations.
* `IsMorse.finrank_singularHomology_sublevel_eq_zero_of_isManifoldStronglyPseudoconvexAt`,
  `IsMorse.bettiNumber_sublevel_eq_zero_of_isManifoldStronglyPseudoconvexAt`,
  `IsMorse.sum_range_neg_one_pow_mul_finrank_sublevel_eq_of_isManifoldStronglyPseudoconvexAt`,
  `IsMorse.exists_sum_range_monomial_sublevel_eq_add_mul_of_isManifoldStronglyPseudoconvexAt`:
  the corresponding Betti vanishing, Euler equality, and Morse polynomial identity on any compact
  regular sublevel `{f ≤ b}` of a possibly noncompact complex manifold, together with their strictly
  plurisubharmonic (`q = 0`) specializations.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Sections 5 and 7.
* R. Hain, *Notes on the Morse theory of complex manifolds*, Section 2.
-/

public section

noncomputable section

open CategoryTheory Limits Module Set Topology
open Polynomial (monomial X)
open scoped ContDiff Manifold Polynomial

universe u

namespace TauCeti

variable {E : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] {r : ℕ∞ω} [hr : NeZero r] [hM : IsManifold 𝓘(ℂ, E) r M]
  [T2Space M] {f : M → ℝ} {k : Type u} [DivisionRing k] (V : ModuleCat.{u} k) [Module.Finite k V]

local instance : FiniteDimensional ℝ E := Module.Finite.trans ℂ E

include hr hM

omit [FiniteDimensional ℂ E] [T2Space M] in
private theorem isManifold_real_top [FiniteDimensional ℂ E] : IsManifold 𝓘(ℝ, E) ∞ M :=
  have : IsManifold 𝓘(ℂ, E) ∞ M := hM.of_ne_zero ∞ hr.ne
  IsManifold.restrictScalars ℝ this

omit [T2Space M] in
private theorem index_le_of_stronglyPseudoconvexAt (hf : IsMorse 𝓘(ℝ, E) f) {q : ℕ} {x : M}
    (hx : x ∈ criticalPoints 𝓘(ℝ, E) f) (hq : IsManifoldStronglyPseudoconvexAt E q f x) :
    manifoldMorseIndex 𝓘(ℝ, E) f x ≤ finrank ℂ E + q := by
  have : IsManifold 𝓘(ℂ, E) ∞ M := hM.of_ne_zero ∞ hr.ne
  have : IsManifold 𝓘(ℂ, E) 2 M := IsManifold.of_le (by simp : (2 : ℕ∞ω) ≤ ∞)
  exact hq.manifoldMorseIndex_le_of_mem_criticalPoints (hf.contMDiff x) hx

namespace IsMorse

section Band

/-- **Vanishing of relative Betti numbers for a strongly `q`-pseudoconvex band.** Let `f` be a real
Morse function on a Hausdorff complex `n`-manifold, and `a ≤ b` regular values with compact band
`f⁻¹[a, b]`. If `f` is strongly `q`-pseudoconvex at every critical point in `(a, b]`, then
`dim Hₘ({f ≤ b}, {f ≤ a}; V) = 0` for every `m > n + q`. -/
theorem finrank_singularHomology_sublevelPair_eq_zero_of_isManifoldStronglyPseudoconvexAt
    (hf : IsMorse 𝓘(ℝ, E) f) {a b : ℝ} (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (ha : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f a) (hb : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f b) {q m : ℕ}
    (hq : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f, f x ∈ Ioc a b → IsManifoldStronglyPseudoconvexAt E q f x)
    (hm : finrank ℂ E + q < m) :
    finrank k ((sublevelPair f hab).singularHomology V m : ModuleCat k) = 0 := by
  have := isManifold_real_top (E := E) (M := M) (r := r)
  exact hf.finrank_singularHomology_sublevelPair_eq_zero_of_manifoldMorseIndex_le V hab hcompact ha
    hb (fun x hx hfx ↦ index_le_of_stronglyPseudoconvexAt (r := r) hf hx (hq x hx hfx)) hm

/-- **Euler's equality from degree `n + q` onwards for a strongly `q`-pseudoconvex band.** If a
Morse function `f` is strongly `q`-pseudoconvex at every critical point in `(a, b]`, then Euler's
equality for `({f ≤ b}, {f ≤ a})` holds in every degree `m ≥ finrank ℂ E + q`. -/
theorem sum_range_neg_one_pow_mul_finrank_sublevelPair_eq_of_isManifoldStronglyPseudoconvexAt
    (hf : IsMorse 𝓘(ℝ, E) f) {a b : ℝ} (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (ha : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f a) (hb : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f b) {q m : ℕ}
    (hq : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f, f x ∈ Ioc a b → IsManifoldStronglyPseudoconvexAt E q f x)
    (hm : finrank ℂ E + q ≤ m) :
    ∑ i ∈ Finset.range (m + 1), (-1 : ℤ) ^ i *
        finrank k ((sublevelPair f hab).singularHomology V i : ModuleCat k) =
      finrank k V * ∑ i ∈ Finset.range (m + 1), (-1 : ℤ) ^ i *
        {x ∈ criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Ioc a b |
          manifoldMorseIndex 𝓘(ℝ, E) f x = i}.ncard := by
  have := isManifold_real_top (E := E) (M := M) (r := r)
  exact
    hf.sum_range_neg_one_pow_mul_finrank_singularHomology_sublevelPair_eq_of_manifoldMorseIndex_le V
      hab hcompact ha hb
      (fun x hx hfx ↦ index_le_of_stronglyPseudoconvexAt (r := r) hf hx (hq x hx hfx)) hm

/-- **The Morse polynomial identity from degree `n + q` onwards for a strongly `q`-pseudoconvex
band.** -/
theorem exists_sum_range_monomial_sublevelPair_eq_add_mul_of_isManifoldStronglyPseudoconvexAt
    (hf : IsMorse 𝓘(ℝ, E) f) {a b : ℝ} (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (ha : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f a) (hb : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f b) {q m : ℕ}
    (hq : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f, f x ∈ Ioc a b → IsManifoldStronglyPseudoconvexAt E q f x)
    (hm : finrank ℂ E + q ≤ m) :
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
  have := isManifold_real_top (E := E) (M := M) (r := r)
  exact hf.exists_sum_range_monomial_sublevelPair_eq_add_mul_of_manifoldMorseIndex_le V hab hcompact
    ha hb (fun x hx hfx ↦ index_le_of_stronglyPseudoconvexAt (r := r) hf hx (hq x hx hfx)) hm

/-- **Vanishing of relative Betti numbers above the complex dimension for a strictly
plurisubharmonic band.** -/
theorem finrank_singularHomology_sublevelPair_eq_zero_of_isManifoldStrictlyPlurisubharmonicAt
    (hf : IsMorse 𝓘(ℝ, E) f) {a b : ℝ} (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (ha : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f a) (hb : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f b) {m : ℕ}
    (hpos : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f, f x ∈ Ioc a b →
      IsManifoldStrictlyPlurisubharmonicAt E f x)
    (hm : finrank ℂ E < m) :
    finrank k ((sublevelPair f hab).singularHomology V m : ModuleCat k) = 0 :=
  hf.finrank_singularHomology_sublevelPair_eq_zero_of_isManifoldStronglyPseudoconvexAt (r := r) V
    hab hcompact ha hb (q := 0)
    (fun x hx hfx ↦ (hpos x hx hfx).isManifoldStronglyPseudoconvexAt 0) (by simpa using hm)

/-- **Euler's equality from the complex dimension onwards for a strictly plurisubharmonic band.** -/
theorem sum_range_neg_one_pow_mul_finrank_sublevelPair_eq_of_isManifoldStrictlyPlurisubharmonicAt
    (hf : IsMorse 𝓘(ℝ, E) f) {a b : ℝ} (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (ha : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f a) (hb : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f b) {m : ℕ}
    (hpos : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f, f x ∈ Ioc a b →
      IsManifoldStrictlyPlurisubharmonicAt E f x)
    (hm : finrank ℂ E ≤ m) :
    ∑ i ∈ Finset.range (m + 1), (-1 : ℤ) ^ i *
        finrank k ((sublevelPair f hab).singularHomology V i : ModuleCat k) =
      finrank k V * ∑ i ∈ Finset.range (m + 1), (-1 : ℤ) ^ i *
        {x ∈ criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Ioc a b |
          manifoldMorseIndex 𝓘(ℝ, E) f x = i}.ncard :=
  hf.sum_range_neg_one_pow_mul_finrank_sublevelPair_eq_of_isManifoldStronglyPseudoconvexAt (r := r)
    V hab hcompact ha hb (q := 0)
    (fun x hx hfx ↦ (hpos x hx hfx).isManifoldStronglyPseudoconvexAt 0) (by simpa using hm)

/-- **The Morse polynomial identity from the complex dimension onwards for a strictly
plurisubharmonic band.** -/
theorem exists_sum_range_monomial_sublevelPair_eq_add_mul_of_isManifoldStrictlyPlurisubharmonicAt
    (hf : IsMorse 𝓘(ℝ, E) f) {a b : ℝ} (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (ha : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f a) (hb : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f b) {m : ℕ}
    (hpos : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f, f x ∈ Ioc a b →
      IsManifoldStrictlyPlurisubharmonicAt E f x)
    (hm : finrank ℂ E ≤ m) :
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
  hf.exists_sum_range_monomial_sublevelPair_eq_add_mul_of_isManifoldStronglyPseudoconvexAt (r := r)
    V hab hcompact ha hb (q := 0)
    (fun x hx hfx ↦ (hpos x hx hfx).isManifoldStronglyPseudoconvexAt 0) (by simpa using hm)

end Band

section Sublevel

/-- **Vanishing of homology dimension for a compact strongly `q`-pseudoconvex regular sublevel.**
Without assuming `M` is compact, if `{f ≤ b}` is compact, `b` is a regular value, and `f` is
strongly `q`-pseudoconvex at every critical point in `{f ≤ b}`, then `dim Hₘ({f ≤ b}; V) = 0` for
every `m > finrank ℂ E + q`. -/
theorem finrank_singularHomology_sublevel_eq_zero_of_isManifoldStronglyPseudoconvexAt
    (hf : IsMorse 𝓘(ℝ, E) f) {b : ℝ} (hcompact : IsCompact {x | f x ≤ b})
    (hb : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f b) {q m : ℕ}
    (hq : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f, f x ≤ b → IsManifoldStronglyPseudoconvexAt E q f x)
    (hm : finrank ℂ E + q < m) :
    finrank k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) m).obj V).obj
      (TopCat.of {x | f x ≤ b})) = 0 := by
  have := isManifold_real_top (E := E) (M := M) (r := r)
  exact hf.finrank_singularHomology_sublevel_eq_zero_of_manifoldMorseIndex_le V hcompact hb
    (fun x hx hfx ↦ index_le_of_stronglyPseudoconvexAt (r := r) hf hx (hq x hx hfx)) hm

/-- **Betti numbers of a compact strongly `q`-pseudoconvex regular sublevel vanish above
`finrank ℂ E + q`.** -/
theorem bettiNumber_sublevel_eq_zero_of_isManifoldStronglyPseudoconvexAt (k : Type u)
    [DivisionRing k] (hf : IsMorse 𝓘(ℝ, E) f) {b : ℝ} (hcompact : IsCompact {x | f x ≤ b})
    (hb : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f b) {q m : ℕ}
    (hq : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f, f x ≤ b → IsManifoldStronglyPseudoconvexAt E q f x)
    (hm : finrank ℂ E + q < m) :
    bettiNumber k {x | f x ≤ b} m = 0 := by
  rw [bettiNumber_def]
  exact hf.finrank_singularHomology_sublevel_eq_zero_of_isManifoldStronglyPseudoconvexAt (r := r)
    (ModuleCat.of k k) hcompact hb hq hm

/-- **Euler's equality from degree `n + q` onwards for a compact strongly `q`-pseudoconvex regular
sublevel.** -/
theorem sum_range_neg_one_pow_mul_finrank_sublevel_eq_of_isManifoldStronglyPseudoconvexAt
    (hf : IsMorse 𝓘(ℝ, E) f) {b : ℝ} (hcompact : IsCompact {x | f x ≤ b})
    (hb : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f b) {q m : ℕ}
    (hq : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f, f x ≤ b → IsManifoldStronglyPseudoconvexAt E q f x)
    (hm : finrank ℂ E + q ≤ m) :
    ∑ i ∈ Finset.range (m + 1), (-1 : ℤ) ^ i *
        finrank k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) i).obj V).obj
          (TopCat.of {x | f x ≤ b})) =
      finrank k V * ∑ i ∈ Finset.range (m + 1), (-1 : ℤ) ^ i *
        {x ∈ criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Iic b |
          manifoldMorseIndex 𝓘(ℝ, E) f x = i}.ncard := by
  have := isManifold_real_top (E := E) (M := M) (r := r)
  exact hf.sum_range_neg_one_pow_mul_finrank_singularHomology_sublevel_eq_of_manifoldMorseIndex_le V
    hcompact hb
    (fun x hx hfx ↦ index_le_of_stronglyPseudoconvexAt (r := r) hf hx (hq x hx hfx)) hm

/-- **The Morse polynomial identity from degree `n + q` onwards for a compact strongly
`q`-pseudoconvex regular sublevel.** -/
theorem exists_sum_range_monomial_sublevel_eq_add_mul_of_isManifoldStronglyPseudoconvexAt
    (hf : IsMorse 𝓘(ℝ, E) f) {b : ℝ} (hcompact : IsCompact {x | f x ≤ b})
    (hb : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f b) {q m : ℕ}
    (hq : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f, f x ≤ b → IsManifoldStronglyPseudoconvexAt E q f x)
    (hm : finrank ℂ E + q ≤ m) :
    ∃ Q : ℕ[X], ∑ i ∈ Finset.range (m + 1), monomial i
          ({x ∈ criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Iic b |
            manifoldMorseIndex 𝓘(ℝ, E) f x = i}.ncard * finrank k V) =
        ∑ i ∈ Finset.range (m + 1), monomial i
          (finrank k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) i).obj V).obj
            (TopCat.of {x | f x ≤ b}))) + (1 + X) * Q ∧
      (∀ i < m, (Q.coeff i : ℤ) =
        finrank k V * ∑ j ∈ Finset.range (i + 1), (-1 : ℤ) ^ (i - j) *
            {x ∈ criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Iic b |
              manifoldMorseIndex 𝓘(ℝ, E) f x = j}.ncard -
          ∑ j ∈ Finset.range (i + 1), (-1 : ℤ) ^ (i - j) *
            finrank k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) j).obj V).obj
              (TopCat.of {x | f x ≤ b}))) ∧
      ∀ i, m ≤ i → Q.coeff i = 0 := by
  have := isManifold_real_top (E := E) (M := M) (r := r)
  exact hf.exists_sum_range_monomial_sublevel_eq_add_mul_of_manifoldMorseIndex_le V hcompact hb
    (fun x hx hfx ↦ index_le_of_stronglyPseudoconvexAt (r := r) hf hx (hq x hx hfx)) hm

/-- **Betti numbers of a compact strictly plurisubharmonic regular sublevel vanish above the
complex dimension.** -/
theorem bettiNumber_sublevel_eq_zero_of_isManifoldStrictlyPlurisubharmonicAt (k : Type u)
    [DivisionRing k] (hf : IsMorse 𝓘(ℝ, E) f) {b : ℝ} (hcompact : IsCompact {x | f x ≤ b})
    (hb : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f b) {m : ℕ}
    (hpos : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f, f x ≤ b → IsManifoldStrictlyPlurisubharmonicAt E f x)
    (hm : finrank ℂ E < m) :
    bettiNumber k {x | f x ≤ b} m = 0 :=
  hf.bettiNumber_sublevel_eq_zero_of_isManifoldStronglyPseudoconvexAt (r := r) k hcompact hb
    (q := 0) (fun x hx hfx ↦ (hpos x hx hfx).isManifoldStronglyPseudoconvexAt 0)
    (by simpa using hm)

/-- **Euler's equality from the complex dimension onwards for a compact strictly plurisubharmonic
regular sublevel.** -/
theorem sum_range_neg_one_pow_mul_finrank_sublevel_eq_of_isManifoldStrictlyPlurisubharmonicAt
    (hf : IsMorse 𝓘(ℝ, E) f) {b : ℝ} (hcompact : IsCompact {x | f x ≤ b})
    (hb : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f b) {m : ℕ}
    (hpos : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f, f x ≤ b → IsManifoldStrictlyPlurisubharmonicAt E f x)
    (hm : finrank ℂ E ≤ m) :
    ∑ i ∈ Finset.range (m + 1), (-1 : ℤ) ^ i *
        finrank k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) i).obj V).obj
          (TopCat.of {x | f x ≤ b})) =
      finrank k V * ∑ i ∈ Finset.range (m + 1), (-1 : ℤ) ^ i *
        {x ∈ criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Iic b |
          manifoldMorseIndex 𝓘(ℝ, E) f x = i}.ncard :=
  hf.sum_range_neg_one_pow_mul_finrank_sublevel_eq_of_isManifoldStronglyPseudoconvexAt (r := r) V
    hcompact hb (q := 0) (fun x hx hfx ↦ (hpos x hx hfx).isManifoldStronglyPseudoconvexAt 0)
    (by simpa using hm)

/-- **The Morse polynomial identity from the complex dimension onwards for a compact strictly
plurisubharmonic regular sublevel.** -/
theorem exists_sum_range_monomial_sublevel_eq_add_mul_of_isManifoldStrictlyPlurisubharmonicAt
    (hf : IsMorse 𝓘(ℝ, E) f) {b : ℝ} (hcompact : IsCompact {x | f x ≤ b})
    (hb : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f b) {m : ℕ}
    (hpos : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f, f x ≤ b → IsManifoldStrictlyPlurisubharmonicAt E f x)
    (hm : finrank ℂ E ≤ m) :
    ∃ Q : ℕ[X], ∑ i ∈ Finset.range (m + 1), monomial i
          ({x ∈ criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Iic b |
            manifoldMorseIndex 𝓘(ℝ, E) f x = i}.ncard * finrank k V) =
        ∑ i ∈ Finset.range (m + 1), monomial i
          (finrank k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) i).obj V).obj
            (TopCat.of {x | f x ≤ b}))) + (1 + X) * Q ∧
      (∀ i < m, (Q.coeff i : ℤ) =
        finrank k V * ∑ j ∈ Finset.range (i + 1), (-1 : ℤ) ^ (i - j) *
            {x ∈ criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Iic b |
              manifoldMorseIndex 𝓘(ℝ, E) f x = j}.ncard -
          ∑ j ∈ Finset.range (i + 1), (-1 : ℤ) ^ (i - j) *
            finrank k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) j).obj V).obj
              (TopCat.of {x | f x ≤ b}))) ∧
      ∀ i, m ≤ i → Q.coeff i = 0 :=
  hf.exists_sum_range_monomial_sublevel_eq_add_mul_of_isManifoldStronglyPseudoconvexAt (r := r) V
    hcompact hb (q := 0) (fun x hx hfx ↦ (hpos x hx hfx).isManifoldStronglyPseudoconvexAt 0)
    (by simpa using hm)

end Sublevel

end IsMorse

end TauCeti
