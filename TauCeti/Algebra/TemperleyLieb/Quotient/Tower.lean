/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Hom
public import TauCeti.Algebra.TemperleyLieb.Quotient.Positivity
public import TauCeti.Analysis.CStarAlgebra.ConditionalExpectation.CompletelyPositive
public import TauCeti.Analysis.StarAlgebra.GNS.FiniteDimensional

import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances

/-!
# The C⋆-tower of positive Jones quotients and its conditional expectations

For every admissible loop parameter `δ ∈ jonesLoopParameters`, the finite-dimensional positive
trace quotients `htr.Quotient n = TemperleyLieb ℂ δ n ⧸ htr.traceRadical n` form a unital
C⋆-algebra tower equipped with faithful tracial states, isometric unital `⋆`-inclusions at all
levels `n ≥ 0`, and unital completely positive trace-preserving conditional expectations.

1. **All-level strand inclusions.** Extending `strandIncl` (`n + 1 → n + 2`) by scalar inclusion
   `0 → 1` via `aug` defines `strandInclAll n : TemperleyLieb R δ n →ₐ[R] TemperleyLieb R δ (n + 1)`
   for every `n : ℕ`. Whenever `δ` is a unit, `strandInclAll n` pulls back the trace radical
   exactly, inducing injective unital `⋆`-homomorphisms
   `IsMarkovTrace.quotientStrandStarAlgHom : htr.Quotient n →⋆ₐ[R] htr.Quotient (n + 1)` for all
   `n ≥ 0`.
2. **Path-algebra conditional expectation.** On `PathAlgebra K G v₀ (n + 1)`, the linear map
   `walkExpect G v₀ r δ` closes the final step of each walk with weight `δ⁻¹ (r v / r u) ^ 2`.
   It is a unital `PathAlgebra K G v₀ n`-bimodule retraction of `walkExtend`, scales `walkTrace` by
   `δ⁻¹`, and over `ℂ` with self-adjoint nonzero weights and `δ > 0` maps every square `star Y * Y`
   to an explicit finite sum of squares `∑ i, star (Z i) * Z i`.
3. **Jones quotient expectations, Jones projections, and C⋆-tower.** Transporting `walkExpect`
   across the discrete (`A_(m-1)`) or generic (`A_∞`) multimatrix isomorphism gives the unique
   trace-compatible expectation `IsMarkovTrace.quotientExpect` on `htr.Quotient (n + 1)`. On the
   tower normal form it acts as the scaled last-strand closure
   `ι a * mk (e δ (Fin.last n)) * ι b ↦ δ⁻¹ • (a * b)`, sending the Jones projection
   `p_n = δ⁻¹ • mk (e δ (Fin.last n))` to `δ⁻² • 1`, and satisfies both the unnormalized (`δ⁻¹`)
   and normalized (`δ⁻²`) Markov formulas. Equipping `htr.Quotient n` with its GNS operator C⋆-norm
   from `StarPositiveFunctional.cstarAlgebra` makes the strand inclusions isometric and bundles the
   expectations as completely positive `CStarConditionalExpectation`s.

## Main definitions

* `TauCeti.TemperleyLieb.strandInclAll`, `TauCeti.TemperleyLieb.strandInclStarAlgHom`: strand
  inclusions `TemperleyLieb R δ n → TemperleyLieb R δ (n + 1)` for all `n : ℕ`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.quotientStrandStarAlgHom`: injective unital `⋆`-inclusions
  `htr.Quotient n →⋆ₐ[R] htr.Quotient (n + 1)` for all `n : ℕ` when `IsUnit δ`.
* `TauCeti.TemperleyLieb.walkExpect`: path-algebra conditional expectation
  `PathAlgebra K G v₀ (n + 1) →ₗ[K] PathAlgebra K G v₀ n`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.quotientExpect`: trace-preserving conditional expectation
  `htr.Quotient (n + 1) →ₗ[ℂ] htr.Quotient n` for `δ ∈ jonesLoopParameters`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.normalizedQuotientTrace`: normalized faithful tracial state
  `δ⁻ⁿ • positiveQuotientTrace` on `htr.Quotient n`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.jonesProjection`: the self-adjoint idempotent
  `δ⁻¹ • mk (e δ (Fin.last n))` in `htr.Quotient (n + 2)`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.cstarConditionalExpectation`: `quotientExpect` bundled as a
  completely positive `CStarConditionalExpectation`.

## References

* V. F. R. Jones, *Index for subfactors*, Invent. Math. 72 (1983), 1–25.
* F. M. Goodman, P. de la Harpe, V. F. R. Jones, *Coxeter Graphs and Towers of Algebras*,
  MSRI Publications 14, Springer, 1989, §2.2–2.4.
* D. Penneys, *Unitary Quantum Symmetries Lite*, Chapter 4, §4.3–4.5.
-/

public section

noncomputable section

open scoped ComplexOrder CStarAlgebra

namespace TauCeti.TemperleyLieb

section StrandInclAll

section Semiring

variable {R : Type*} [CommSemiring R] {δ : R}

/-- On zero strands there are no generators, so every element is the image of its augmentation. -/
theorem eq_algebraMap_aug_zero (x : TemperleyLieb R δ 0) :
    x = algebraMap R (TemperleyLieb R δ 0) (aug x) := by
  have h := ((algEquivOfLeOne δ (n := 0) (Nat.zero_le 1)).symm_apply_apply x).symm
  rwa [algEquivOfLeOne_apply, algEquivOfLeOne_symm_apply] at h

/-- Strand inclusion `TemperleyLieb R δ n →ₐ[R] TemperleyLieb R δ (n + 1)` at every level `n ≥ 0`,
extending `strandIncl` (`n + 1 → n + 2`) by scalar inclusion via `aug` at `n = 0`. -/
def strandInclAll : ∀ n : ℕ, TemperleyLieb R δ n →ₐ[R] TemperleyLieb R δ (n + 1)
  | 0 => (Algebra.ofId R _).comp aug
  | _ + 1 => strandIncl

@[simp]
theorem strandInclAll_zero (x : TemperleyLieb R δ 0) :
    strandInclAll 0 x = algebraMap R (TemperleyLieb R δ 1) (aug x) :=
  (rfl)

@[simp]
theorem strandInclAll_succ (n : ℕ) :
    strandInclAll (R := R) (δ := δ) (n + 1) = strandIncl :=
  (rfl)

@[simp]
theorem strandInclAll_star [StarRing R] [Fact (IsSelfAdjoint δ)] (n : ℕ)
    (x : TemperleyLieb R δ n) :
    strandInclAll n (star x) = star (strandInclAll n x) := by
  cases n with
  | zero =>
    conv_lhs => rw [eq_algebraMap_aug_zero x]
    conv_rhs => rw [eq_algebraMap_aug_zero x]
    simp [Algebra.algebraMap_eq_smul_one]
  | succ n => exact strandIncl_star x

/-- `strandInclAll` bundled as a `⋆`-algebra homomorphism at every level `n ≥ 0`. -/
def strandInclStarAlgHom [StarRing R] [Fact (IsSelfAdjoint δ)] (n : ℕ) :
    TemperleyLieb R δ n →⋆ₐ[R] TemperleyLieb R δ (n + 1) :=
  { strandInclAll n with map_star' := strandInclAll_star n }

@[simp]
theorem strandInclStarAlgHom_toAlgHom [StarRing R] [Fact (IsSelfAdjoint δ)] (n : ℕ) :
    (strandInclStarAlgHom (R := R) (δ := δ) n).toAlgHom = strandInclAll n :=
  (rfl)

@[simp]
theorem strandInclStarAlgHom_apply [StarRing R] [Fact (IsSelfAdjoint δ)] (n : ℕ)
    (x : TemperleyLieb R δ n) :
    strandInclStarAlgHom n x = strandInclAll n x :=
  (rfl)

/-- Every Markov trace scales by `δ` under `strandInclAll` at all levels `n ≥ 0`. -/
@[simp]
theorem IsMarkovTrace.map_strandInclAll {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
    (htr : IsMarkovTrace R δ tr) (n : ℕ) (x : TemperleyLieb R δ n) :
    tr (n + 1) (strandInclAll n x) = δ * tr n x := by
  cases n with
  | zero =>
    conv_rhs => rw [eq_algebraMap_aug_zero x]
    simp [Algebra.algebraMap_eq_smul_one, htr.map_one, mul_comm]
  | succ n => exact htr.map_strandIncl n x

end Semiring

section WalkRep

variable {K : Type*} [Field K] {V : Type*} (G : SimpleGraph V) [DecidableEq V]
  [DecidableRel G.Adj] [G.LocallyFinite] (v₀ : V) {r : V → K} (hr : ∀ v, r v ≠ 0) {δ : K}
  (hδ : ∀ v, ∑ u ∈ G.neighborFinset v, r u ^ 2 = δ * r v ^ 2)

/-- `walkRep` intertwines `strandInclAll` with `walkExtend` at all levels `n ≥ 0`. -/
@[simp]
theorem walkRep_strandInclAll (n : ℕ) (x : TemperleyLieb K δ n) :
    walkRep G v₀ hr hδ (strandInclAll n x) = walkExtend G v₀ (walkRep G v₀ hr hδ x) := by
  cases n with
  | zero =>
    conv_rhs => rw [eq_algebraMap_aug_zero x]
    simp [Algebra.algebraMap_eq_smul_one]
  | succ n => exact walkRep_strandIncl hr hδ x

end WalkRep

namespace IsMarkovTrace

section CommRing

variable {R : Type*} [CommRing R] {δ : R} {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
  (htr : IsMarkovTrace R δ tr)

/-- When `δ` is a unit, `strandInclAll n` pulls back the `(n + 1)`-st trace radical to the `n`-th
trace radical for every `n ≥ 0`, including `n = 0`. -/
@[simp]
theorem comap_traceRadical_strandInclAll (hδ : IsUnit δ) (n : ℕ) :
    Ideal.comap (strandInclAll (R := R) (δ := δ) n) (htr.traceRadical (n + 1)) =
      htr.traceRadical n := by
  cases n with
  | zero =>
    ext x
    simp only [Ideal.mem_comap, mem_traceRadical_iff]
    constructor
    · intro hx y
      have h1 := hx 1
      simp only [strandInclAll_zero, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
        map_smul, htr.map_one, zero_add, pow_one, smul_eq_mul] at h1
      have haug : aug x = 0 := hδ.mul_left_eq_zero.mp h1
      rw [eq_algebraMap_aug_zero x, haug, map_zero, zero_mul, map_zero]
    · intro hx y
      have h0 := hx 1
      rw [eq_algebraMap_aug_zero x, Algebra.algebraMap_eq_smul_one, mul_one, map_smul,
        htr.map_one, pow_zero, smul_eq_mul, mul_one] at h0
      simp [h0]
  | succ n => exact htr.comap_traceRadical_strandIncl n

/-- The induced strand algebra map on trace-radical quotients at every level `n ≥ 0`. -/
def quotientStrandInclAll (hδ : IsUnit δ) (n : ℕ) :
    htr.Quotient n →ₐ[R] htr.Quotient (n + 1) :=
  Ideal.quotientMapₐ _ (strandInclAll n) (htr.comap_traceRadical_strandInclAll hδ n).ge

@[simp]
theorem quotientStrandInclAll_mk (hδ : IsUnit δ) (n : ℕ) (x : TemperleyLieb R δ n) :
    htr.quotientStrandInclAll hδ n (Ideal.Quotient.mk (htr.traceRadical n) x) =
      Ideal.Quotient.mk (htr.traceRadical (n + 1)) (strandInclAll n x) :=
  Ideal.quotient_map_mkₐ _ _ _

theorem quotientStrandInclAll_injective (hδ : IsUnit δ) (n : ℕ) :
    Function.Injective (htr.quotientStrandInclAll hδ n) :=
  Ideal.quotientMap_injective' (H := (htr.comap_traceRadical_strandInclAll hδ n).ge)
    (htr.comap_traceRadical_strandInclAll hδ n).le

/-- The unital `⋆`-algebra strand inclusion `htr.Quotient n →⋆ₐ[R] htr.Quotient (n + 1)` at every
level `n ≥ 0` (including `0` and `1`) when `δ` is a unit. -/
def quotientStrandStarAlgHom [StarRing R] [Fact (IsSelfAdjoint δ)] (hδ : IsUnit δ) (n : ℕ) :
    htr.Quotient n →⋆ₐ[R] htr.Quotient (n + 1) :=
  { htr.quotientStrandInclAll hδ n with
    map_star' x := by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact (htr.quotientStrandInclAll_mk hδ n (star a)).trans <| by
        rw [strandInclAll_star, ← Ideal.Quotient.star_mk]
        exact congrArg star (htr.quotientStrandInclAll_mk hδ n a).symm }

@[simp]
theorem quotientStrandStarAlgHom_mk [StarRing R] [Fact (IsSelfAdjoint δ)] (hδ : IsUnit δ) (n : ℕ)
    (x : TemperleyLieb R δ n) :
    htr.quotientStrandStarAlgHom hδ n (Ideal.Quotient.mk (htr.traceRadical n) x) =
      Ideal.Quotient.mk (htr.traceRadical (n + 1)) (strandInclAll n x) :=
  Ideal.quotient_map_mkₐ _ _ _

theorem quotientStrandStarAlgHom_succ_apply [StarRing R] [Fact (IsSelfAdjoint δ)] (hδ : IsUnit δ)
    (n : ℕ) (x : htr.Quotient (n + 1)) :
    htr.quotientStrandStarAlgHom hδ (n + 1) x = htr.quotientStrandIncl n x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [htr.quotientStrandStarAlgHom_mk, strandInclAll_succ]
  exact (htr.quotientStrandIncl_mk n a).symm

/-- All strand maps `htr.Quotient n →⋆ₐ[R] htr.Quotient (n + 1)` (`n ≥ 0`) are injective when
`IsUnit δ`. -/
theorem quotientStrandStarAlgHom_injective [StarRing R] [Fact (IsSelfAdjoint δ)] (hδ : IsUnit δ)
    (n : ℕ) :
    Function.Injective (htr.quotientStrandStarAlgHom hδ n) :=
  htr.quotientStrandInclAll_injective hδ n

@[simp]
theorem quotientTrace_quotientStrandStarAlgHom [StarRing R] [Fact (IsSelfAdjoint δ)]
    (hδ : IsUnit δ) (n : ℕ) (x : htr.Quotient n) :
    (tr (n + 1)).quotientTrace (htr.map_mul_comm (n + 1)) (htr.quotientStrandStarAlgHom hδ n x) =
      δ * (tr n).quotientTrace (htr.map_mul_comm n) x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [htr.quotientStrandStarAlgHom_mk]
  exact ((tr (n + 1)).quotientTrace_mk (htr.map_mul_comm (n + 1)) (strandInclAll n a)).trans <|
    (htr.map_strandInclAll n a).trans <|
      congrArg (δ * ·) ((tr n).quotientTrace_mk (htr.map_mul_comm n) a).symm

end CommRing

theorem quotientPathAlgebraEquiv_quotientStrandStarAlgHom {V : Type*} (G : SimpleGraph V)
    [DecidableEq V] [DecidableRel G.Adj] [G.LocallyFinite] (v₀ : V) {r : V → ℂ}
    (hr : ∀ v, r v ≠ 0) (hrs : ∀ v, IsSelfAdjoint (r v)) {δ : ℂ} [Fact (IsSelfAdjoint δ)]
    (hδ : ∀ v, ∑ u ∈ G.neighborFinset v, r u ^ 2 = δ * r v ^ 2) (hδu : IsUnit δ)
    {tr : ∀ n : ℕ, TemperleyLieb ℂ δ n →ₗ[ℂ] ℂ} (htr : IsMarkovTrace ℂ δ tr)
    {f : V → ℕ} (hf : Function.Injective f) (hf₀ : f v₀ = 0)
    (hadj : ∀ {x y}, G.Adj x y → f x + 1 = f y ∨ f y + 1 = f x) (n : ℕ) (x : htr.Quotient n) :
    htr.quotientPathAlgebraEquiv G v₀ hr hrs hδ hf hf₀ hadj (n + 1)
        (htr.quotientStrandStarAlgHom hδu n x) =
      walkExtend G v₀ (htr.quotientPathAlgebraEquiv G v₀ hr hrs hδ hf hf₀ hadj n x) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [htr.quotientStrandStarAlgHom_mk, quotientPathAlgebraEquiv_mk, quotientPathAlgebraEquiv_mk,
    walkRep_strandInclAll]

end IsMarkovTrace

end StrandInclAll

section WalkExpect

open SimpleGraph

section Field

variable {K : Type*} [Field K] {V : Type*} (G : SimpleGraph V) [DecidableEq V]
  [G.LocallyFinite] (v₀ : V) (r : V → K) (δ : K)

/-- Conditional expectation `PathAlgebra K G v₀ (n + 1) →ₗ[K] PathAlgebra K G v₀ n` closing the
final step of walks from `u` across neighbours `v ∈ G.neighborFinset u` with weight
`δ⁻¹ * (r v / r u) ^ 2`. -/
def walkExpect {n : ℕ} : PathAlgebra K G v₀ (n + 1) →ₗ[K] PathAlgebra K G v₀ n where
  toFun Y u := Matrix.of fun p q ↦
    δ⁻¹ * ∑ v ∈ (G.neighborFinset u.1).attach,
      (r v.1 / r u.1) ^ 2 *
        PathAlgebra.blockAt Y v.1 (p.snoc ((G.mem_neighborFinset u.1 v.1).1 v.2))
          (q.snoc ((G.mem_neighborFinset u.1 v.1).1 v.2))
  map_add' X Y := by
    ext u p q
    simp [PathAlgebra.blockAt_add, mul_add, Finset.sum_add_distrib]
  map_smul' c X := by
    funext u
    ext p q
    simp only [RingHom.id_apply, Pi.smul_apply, Matrix.smul_apply, Matrix.of_apply,
      PathAlgebra.blockAt_smul, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ ↦ by ring

theorem walkExpect_apply {n : ℕ} (Y : PathAlgebra K G v₀ (n + 1)) (u : G.walkEndpoints v₀ n)
    (p q : G.EndpointWalk v₀ n u.1) :
    walkExpect G v₀ r δ Y u p q =
      δ⁻¹ * ∑ v ∈ (G.neighborFinset u.1).attach,
        (r v.1 / r u.1) ^ 2 *
          PathAlgebra.blockAt Y v.1 (p.snoc ((G.mem_neighborFinset u.1 v.1).1 v.2))
            (q.snoc ((G.mem_neighborFinset u.1 v.1).1 v.2)) :=
  (rfl)

variable {G v₀ r δ}

@[simp]
theorem walkExpect_one (hr : ∀ v, r v ≠ 0) (hδ₀ : δ ≠ 0)
    (hδ : ∀ v, ∑ u ∈ G.neighborFinset v, r u ^ 2 = δ * r v ^ 2) (n : ℕ) :
    walkExpect G v₀ r δ (1 : PathAlgebra K G v₀ (n + 1)) = 1 := by
  funext u
  ext p q
  rw [walkExpect_apply, Pi.one_apply, Matrix.one_apply]
  have hsnoc_eq {v : V} (h : G.Adj u.1 v) :
      (p.snoc h = q.snoc h) ↔ p = q :=
    ⟨fun hpq ↦ EndpointWalk.ext fun i ↦ by
        simpa using congrFun (congrArg DFunLike.coe hpq) i.castSucc,
      fun hpq ↦ hpq ▸ rfl⟩
  split_ifs with hpq
  · subst hpq
    have hterm (v : {v // v ∈ G.neighborFinset u.1}) :
        (r v.1 / r u.1) ^ 2 *
          PathAlgebra.blockAt (1 : PathAlgebra K G v₀ (n + 1)) v.1
            (p.snoc ((G.mem_neighborFinset u.1 v.1).1 v.2))
            (p.snoc ((G.mem_neighborFinset u.1 v.1).1 v.2)) =
          (r v.1 / r u.1) ^ 2 := by
      have hv : v.1 ∈ G.walkEndpoints v₀ (n + 1) :=
        (G.mem_walkEndpoints_iff v₀).2 ⟨p.snoc ((G.mem_neighborFinset u.1 v.1).1 v.2)⟩
      simp only [PathAlgebra.blockAt_of_mem _ hv, Pi.one_apply, Matrix.one_apply, ↓reduceIte,
        mul_one]
    simp_rw [hterm]
    rw [Finset.sum_attach (G.neighborFinset u.1) (fun v ↦ (r v / r u.1) ^ 2)]
    simp_rw [div_pow, div_eq_mul_inv]
    rw [← Finset.sum_mul, hδ u.1]
    have := hr u.1
    field_simp
  · suffices ∑ v ∈ (G.neighborFinset u.1).attach,
        (r v.1 / r u.1) ^ 2 *
          PathAlgebra.blockAt (1 : PathAlgebra K G v₀ (n + 1)) v.1
            (p.snoc ((G.mem_neighborFinset u.1 v.1).1 v.2))
            (q.snoc ((G.mem_neighborFinset u.1 v.1).1 v.2)) = 0 by
      rw [this, mul_zero]
    refine Finset.sum_eq_zero fun v _ ↦ ?_
    have hv : v.1 ∈ G.walkEndpoints v₀ (n + 1) :=
      (G.mem_walkEndpoints_iff v₀).2 ⟨p.snoc ((G.mem_neighborFinset u.1 v.1).1 v.2)⟩
    have hne : p.snoc ((G.mem_neighborFinset u.1 v.1).1 v.2) ≠
        q.snoc ((G.mem_neighborFinset u.1 v.1).1 v.2) :=
      mt (hsnoc_eq _).1 hpq
    simp only [PathAlgebra.blockAt_of_mem _ hv, Pi.one_apply, Matrix.one_apply, hne, ↓reduceIte,
      mul_zero]

@[simp]
theorem walkExpect_walkExtend_mul {n : ℕ} (X : PathAlgebra K G v₀ n)
    (Y : PathAlgebra K G v₀ (n + 1)) :
    walkExpect G v₀ r δ (walkExtend G v₀ X * Y) = X * walkExpect G v₀ r δ Y := by
  ext u p q
  rw [walkExpect_apply, Pi.mul_apply, Matrix.mul_apply]
  have hterm (v : {v // v ∈ G.neighborFinset u.1}) :
      PathAlgebra.blockAt (walkExtend G v₀ X * Y) v.1
          (p.snoc ((G.mem_neighborFinset u.1 v.1).1 v.2))
          (q.snoc ((G.mem_neighborFinset u.1 v.1).1 v.2)) =
        ∑ p' : G.EndpointWalk v₀ n u.1,
          X u p p' * PathAlgebra.blockAt Y v.1
            (p'.snoc ((G.mem_neighborFinset u.1 v.1).1 v.2))
            (q.snoc ((G.mem_neighborFinset u.1 v.1).1 v.2)) := by
    set hadj := (G.mem_neighborFinset u.1 v.1).1 v.2
    have hv : v.1 ∈ G.walkEndpoints v₀ (n + 1) := (G.mem_walkEndpoints_iff v₀).2 ⟨p.snoc hadj⟩
    rw [PathAlgebra.blockAt_of_mem _ hv, PathAlgebra.blockAt_of_mem Y hv, Pi.mul_apply,
      Matrix.mul_apply, ← (EndpointWalk.succEquiv G v₀ n v.1).symm.sum_comp,
      ← Finset.univ_sigma_univ, Finset.sum_sigma]
    let u_nb : G.neighborSet v.1 := ⟨u.1, (G.mem_neighborSet v.1 u.1).2 hadj.symm⟩
    rw [Finset.sum_eq_single u_nb
      (fun u' _ hu' ↦ Finset.sum_eq_zero fun p' _ ↦ by
        rw [EndpointWalk.succEquiv_symm_apply, walkExtend_apply_snoc,
          dite_eq_right (fun h ↦ hu' (Subtype.ext h.symm)), zero_mul])
      (fun h ↦ (h (Finset.mem_univ _)).elim)]
    refine Finset.sum_congr rfl fun p' _ ↦ ?_
    rw [EndpointWalk.succEquiv_symm_apply, walkExtend_apply_snoc_same]
  simp_rw [hterm, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p' _ ↦ ?_
  rw [walkExpect_apply, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  ring

@[simp]
theorem walkExpect_mul_walkExtend {n : ℕ} (Y : PathAlgebra K G v₀ (n + 1))
    (X : PathAlgebra K G v₀ n) :
    walkExpect G v₀ r δ (Y * walkExtend G v₀ X) = walkExpect G v₀ r δ Y * X := by
  ext u p q
  rw [walkExpect_apply, Pi.mul_apply, Matrix.mul_apply]
  have hterm (v : {v // v ∈ G.neighborFinset u.1}) :
      PathAlgebra.blockAt (Y * walkExtend G v₀ X) v.1
          (p.snoc ((G.mem_neighborFinset u.1 v.1).1 v.2))
          (q.snoc ((G.mem_neighborFinset u.1 v.1).1 v.2)) =
        ∑ q' : G.EndpointWalk v₀ n u.1,
          PathAlgebra.blockAt Y v.1
            (p.snoc ((G.mem_neighborFinset u.1 v.1).1 v.2))
            (q'.snoc ((G.mem_neighborFinset u.1 v.1).1 v.2)) * X u q' q := by
    set hadj := (G.mem_neighborFinset u.1 v.1).1 v.2
    have hv : v.1 ∈ G.walkEndpoints v₀ (n + 1) := (G.mem_walkEndpoints_iff v₀).2 ⟨p.snoc hadj⟩
    rw [PathAlgebra.blockAt_of_mem _ hv, PathAlgebra.blockAt_of_mem Y hv, Pi.mul_apply,
      Matrix.mul_apply, ← (EndpointWalk.succEquiv G v₀ n v.1).symm.sum_comp,
      ← Finset.univ_sigma_univ, Finset.sum_sigma]
    let u_nb : G.neighborSet v.1 := ⟨u.1, (G.mem_neighborSet v.1 u.1).2 hadj.symm⟩
    rw [Finset.sum_eq_single u_nb
      (fun u' _ hu' ↦ Finset.sum_eq_zero fun q' _ ↦ by
        rw [EndpointWalk.succEquiv_symm_apply, walkExtend_apply_snoc,
          dite_eq_right (fun h ↦ hu' (Subtype.ext h)), mul_zero])
      (fun h ↦ (h (Finset.mem_univ _)).elim)]
    refine Finset.sum_congr rfl fun q' _ ↦ ?_
    rw [EndpointWalk.succEquiv_symm_apply, walkExtend_apply_snoc_same]
  simp_rw [hterm, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q' _ ↦ ?_
  rw [walkExpect_apply]
  simp only [mul_assoc, Finset.sum_mul, Finset.mul_sum]

@[simp]
theorem walkExpect_walkExtend (hr : ∀ v, r v ≠ 0) (hδ₀ : δ ≠ 0)
    (hδ : ∀ v, ∑ u ∈ G.neighborFinset v, r u ^ 2 = δ * r v ^ 2) {n : ℕ}
    (X : PathAlgebra K G v₀ n) :
    walkExpect G v₀ r δ (walkExtend G v₀ X) = X := by
  rw [← mul_one (walkExtend G v₀ X), walkExpect_walkExtend_mul, walkExpect_one hr hδ₀ hδ, mul_one]

/-- `walkExpect` scales `walkTrace` by `δ⁻¹`. -/
@[simp]
theorem walkTrace_walkExpect (hr : ∀ v, r v ≠ 0) {n : ℕ}
    (Y : PathAlgebra K G v₀ (n + 1)) :
    walkTrace G v₀ r (walkExpect G v₀ r δ Y) = δ⁻¹ * walkTrace G v₀ r Y := by
  classical
  let stepDiag (u v : V) : K :=
    if h : G.Adj u v then
      ∑ p : G.EndpointWalk v₀ n u, PathAlgebra.blockAt Y v (p.snoc h) (p.snoc h)
    else 0
  have htrY (v : G.walkEndpoints v₀ (n + 1)) :
      (Y v).trace = ∑ u ∈ G.neighborFinset v.1 ∩ G.walkEndpoints v₀ n, stepDiag u v.1 := by
    simp only [Matrix.trace, Matrix.diag_apply]
    rw [← (EndpointWalk.succEquiv G v₀ n v.1).symm.sum_comp,
      ← Finset.univ_sigma_univ, Finset.sum_sigma]
    have hnb (u : G.neighborSet v.1) :
        (∑ p : G.EndpointWalk v₀ n u.1,
          Y v ((EndpointWalk.succEquiv G v₀ n v.1).symm ⟨u, p⟩)
            ((EndpointWalk.succEquiv G v₀ n v.1).symm ⟨u, p⟩)) = stepDiag u.1 v.1 := by
      have hadj : G.Adj u.1 v.1 := ((G.mem_neighborSet v.1 u.1).1 u.2).symm
      dsimp only [stepDiag]
      rw [dite_eq_left hadj]
      refine Finset.sum_congr rfl fun p _ ↦ ?_
      rw [EndpointWalk.succEquiv_symm_apply, PathAlgebra.blockAt_of_mem Y v.2]
    simp_rw [hnb]
    have hbij : ∑ u : G.neighborSet v.1, stepDiag u.1 v.1 =
        ∑ u ∈ G.neighborFinset v.1, stepDiag u v.1 :=
      Finset.sum_bij (fun u _ ↦ u.1) (fun u _ ↦ (G.mem_neighborFinset v.1 u.1).2 u.2)
        (fun _ _ _ _ h ↦ Subtype.ext h)
        (fun u hu ↦ ⟨⟨u, (G.mem_neighborFinset v.1 u).1 hu⟩, Finset.mem_univ _, rfl⟩)
        (fun _ _ ↦ rfl)
    rw [hbij]
    refine (Finset.sum_subset Finset.inter_subset_left fun u hu hnu ↦ ?_).symm
    have hnot : u ∉ G.walkEndpoints v₀ n := fun h ↦ hnu (Finset.mem_inter.2 ⟨hu, h⟩)
    have hempty : IsEmpty (G.EndpointWalk v₀ n u) :=
      ⟨fun p ↦ hnot ((G.mem_walkEndpoints_iff v₀).2 ⟨p⟩)⟩
    dsimp only [stepDiag]
    split_ifs with hadj
    · exact (Finset.univ_eq_empty_iff.2 hempty) ▸ Finset.sum_empty
    · rfl
  have htrE (u : G.walkEndpoints v₀ n) :
      (walkExpect G v₀ r δ Y u).trace =
        δ⁻¹ * ∑ v ∈ G.neighborFinset u.1, (r v / r u.1) ^ 2 * stepDiag u.1 v := by
    simp only [Matrix.trace, Matrix.diag_apply, walkExpect_apply]
    rw [← Finset.mul_sum, Finset.sum_comm]
    refine congrArg (δ⁻¹ * ·) ?_
    have hatt : (∑ x ∈ (G.neighborFinset u.1).attach,
          ∑ p : G.EndpointWalk v₀ n u.1,
            (r x.1 / r u.1) ^ 2 *
              PathAlgebra.blockAt Y x.1 (p.snoc ((G.mem_neighborFinset u.1 x.1).1 x.2))
                (p.snoc ((G.mem_neighborFinset u.1 x.1).1 x.2))) =
        ∑ x ∈ (G.neighborFinset u.1).attach, (r x.1 / r u.1) ^ 2 * stepDiag u.1 x.1 := by
      refine Finset.sum_congr rfl fun x _ ↦ ?_
      have hadj : G.Adj u.1 x.1 := (G.mem_neighborFinset u.1 x.1).1 x.2
      dsimp only [stepDiag]
      rw [dite_eq_left hadj, Finset.mul_sum]
    rw [hatt, Finset.sum_attach (G.neighborFinset u.1)
      (fun v ↦ (r v / r u.1) ^ 2 * stepDiag u.1 v)]
  rw [walkTrace_apply, walkTrace_apply, Finset.mul_sum]
  simp_rw [htrE, htrY, Finset.mul_sum]
  rw [Finset.univ_eq_attach, Finset.sum_attach (G.walkEndpoints v₀ n)
      (fun u ↦ ∑ v ∈ G.neighborFinset u,
        (r u / r v₀) ^ 2 * (δ⁻¹ * ((r v / r u) ^ 2 * stepDiag u v))),
    Finset.sum_sigma' (G.walkEndpoints v₀ n) (fun u ↦ G.neighborFinset u)
      (fun u v ↦ (r u / r v₀) ^ 2 * (δ⁻¹ * ((r v / r u) ^ 2 * stepDiag u v))),
    Finset.univ_eq_attach, Finset.sum_attach (G.walkEndpoints v₀ (n + 1))
      (fun v ↦ ∑ u ∈ G.neighborFinset v ∩ G.walkEndpoints v₀ n,
        δ⁻¹ * ((r v / r v₀) ^ 2 * stepDiag u v)),
    Finset.sum_sigma' (G.walkEndpoints v₀ (n + 1))
      (fun v ↦ G.neighborFinset v ∩ G.walkEndpoints v₀ n)
      (fun v u ↦ δ⁻¹ * ((r v / r v₀) ^ 2 * stepDiag u v))]
  refine Finset.sum_bij (fun q _ ↦ ⟨q.2, q.1⟩)
    (fun q hq ↦ ?_)
    (fun q₁ _ q₂ _ h ↦ by cases q₁; cases q₂; cases h; rfl)
    (fun p hp ↦ ?_)
    (fun q _ ↦ ?_)
  · rcases Finset.mem_sigma.1 hq with ⟨hu, hadj⟩
    have hv : q.2 ∈ G.walkEndpoints v₀ (n + 1) := by
      rw [walkEndpoints_succ]
      exact Finset.mem_biUnion.2 ⟨q.1, hu, hadj⟩
    refine Finset.mem_sigma.2 ⟨hv, Finset.mem_inter.2 ⟨?_, hu⟩⟩
    exact (G.mem_neighborFinset _ _).2 ((G.mem_neighborFinset _ _).1 hadj).symm
  · rcases Finset.mem_sigma.1 hp with ⟨_, hp₂⟩
    rcases Finset.mem_inter.1 hp₂ with ⟨hadj, hu⟩
    exact ⟨⟨p.2, p.1⟩, Finset.mem_sigma.2
      ⟨hu, (G.mem_neighborFinset _ _).2 ((G.mem_neighborFinset _ _).1 hadj).symm⟩, rfl⟩
  · have := hr q.1
    have := hr v₀
    field_simp

end Field

section ComplexPositivity

variable {V : Type*} {G : SimpleGraph V} [DecidableEq V] [G.LocallyFinite] {v₀ : V}

/-- Over `ℂ` with self-adjoint weights and `δ > 0`, `walkExpect` maps every square
`star Y * Y` to an explicit finite sum of squares `∑ i, star (Z i) * Z i` in
`PathAlgebra ℂ G v₀ n`. -/
theorem exists_sum_star_mul_self_walkExpect_star_mul_self {r : V → ℂ}
    (hrs : ∀ v, IsSelfAdjoint (r v)) {δ : ℝ} (hδ₀ : 0 < δ) {n : ℕ}
    (Y : PathAlgebra ℂ G v₀ (n + 1)) :
    ∃ (m : ℕ) (Z : Fin m → PathAlgebra ℂ G v₀ n),
      walkExpect G v₀ r (δ : ℂ) (star Y * Y) = ∑ i : Fin m, star (Z i) * Z i := by
  classical
  let α (u v : V) : ℂ := ((√(δ⁻¹ * ((r v).re / (r u).re) ^ 2) : ℝ) : ℂ)
  have hα (u v : V) : star (α u v) * α u v = (δ : ℂ)⁻¹ * (r v / r u) ^ 2 := by
    have hrv : ((r v).re : ℂ) = r v := Complex.conj_eq_iff_re.mp (hrs v)
    have hru : ((r u).re : ℂ) = r u := Complex.conj_eq_iff_re.mp (hrs u)
    have hnn : 0 ≤ δ⁻¹ * ((r v).re / (r u).re) ^ 2 := by positivity
    dsimp only [α]
    rw [IsSelfAdjoint.star_eq (Complex.conj_ofReal _), ← Complex.ofReal_mul,
      Real.mul_self_sqrt hnn]
    push_cast
    rw [hrv, hru]
  let ι := Σ (u : G.walkEndpoints v₀ n) (v : G.neighborFinset u.1), G.EndpointWalk v₀ (n + 1) v.1
  let Z₀ (idx : ι) : PathAlgebra ℂ G v₀ n :=
    if hne : Nonempty (G.EndpointWalk v₀ n idx.1.1) then
      Pi.single idx.1 <| Matrix.of fun p' q ↦
        if p' = Classical.choice hne then
          α idx.1.1 idx.2.1.1 *
            PathAlgebra.blockAt Y idx.2.1.1 idx.2.2
              (q.snoc ((G.mem_neighborFinset idx.1.1 idx.2.1.1).1 idx.2.1.2))
        else 0
    else 0
  have hsum : walkExpect G v₀ r (δ : ℂ) (star Y * Y) = ∑ idx : ι, star (Z₀ idx) * Z₀ idx := by
    funext u
    ext p q
    have hne : Nonempty (G.EndpointWalk v₀ n u.1) := ⟨p⟩
    simp only [walkExpect_apply, Finset.sum_apply, Matrix.sum_apply]
    rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
    have houter : ∀ u' : G.walkEndpoints v₀ n, u' ≠ u →
        (∑ x : Σ v : G.neighborFinset u'.1, G.EndpointWalk v₀ (n + 1) v.1,
          (star (Z₀ ⟨u', x⟩) * Z₀ ⟨u', x⟩) u p q) = 0 := fun u' hu' ↦
      Finset.sum_eq_zero fun x _ ↦ by
        have h0 : Z₀ ⟨u', x⟩ u = 0 := by
          by_cases h : Nonempty (G.EndpointWalk v₀ n u'.1)
          · simp only [Z₀, h, ↓reduceDIte]
            exact Pi.single_eq_of_ne hu'.symm _
          · simp [Z₀, h]
        simp [Pi.mul_apply, h0]
    rw [Finset.sum_eq_single u (fun u' _ hu' ↦ houter u' hu')
      (fun h ↦ (h (Finset.mem_univ _)).elim)]
    rw [← Finset.univ_sigma_univ, Finset.sum_sigma, Finset.mul_sum, Finset.univ_eq_attach]
    refine Finset.sum_congr rfl fun v _ ↦ ?_
    set hadj := (G.mem_neighborFinset u.1 v.1).1 v.2
    have hv : v.1 ∈ G.walkEndpoints v₀ (n + 1) := (G.mem_walkEndpoints_iff v₀).2 ⟨p.snoc hadj⟩
    rw [PathAlgebra.blockAt_of_mem _ hv, Pi.mul_apply, Pi.star_apply,
      Matrix.star_eq_conjTranspose, Matrix.mul_apply, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ ↦ ?_
    have hZ : Z₀ ⟨u, ⟨v, w⟩⟩ u = Matrix.of fun p' q' ↦
        if p' = Classical.choice hne then
          α u.1 v.1 * PathAlgebra.blockAt Y v.1 w (q'.snoc hadj)
        else 0 := by
      simp only [Z₀, hne, ↓reduceDIte, Pi.single_eq_same]
    rw [Pi.mul_apply, Pi.star_apply, hZ, Matrix.star_eq_conjTranspose, Matrix.mul_apply,
      Finset.sum_eq_single (Classical.choice hne)
        (fun p' _ hp' ↦ by simp [hp'])
        (fun h ↦ (h (Finset.mem_univ _)).elim)]
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply, ↓reduceIte,
      PathAlgebra.blockAt_of_mem Y hv, star_mul]
    exact (calc star (Y ⟨v.1, hv⟩ w (p.snoc hadj)) * star (α u.1 v.1) *
          (α u.1 v.1 * Y ⟨v.1, hv⟩ w (q.snoc hadj))
        = (star (α u.1 v.1) * α u.1 v.1) *
            (star (Y ⟨v.1, hv⟩ w (p.snoc hadj)) * Y ⟨v.1, hv⟩ w (q.snoc hadj)) := by ring
      _ = (δ : ℂ)⁻¹ *
            ((r v.1 / r u.1) ^ 2 *
              (star (Y ⟨v.1, hv⟩ w (p.snoc hadj)) * Y ⟨v.1, hv⟩ w (q.snoc hadj))) := by
          rw [hα]; ring).symm
  let eqv := Fintype.equivFin ι
  refine ⟨Fintype.card ι, Z₀ ∘ eqv.symm, ?_⟩
  rw [hsum, ← eqv.symm.sum_comp]
  rfl

end ComplexPositivity

end WalkExpect

namespace IsMarkovTrace

section GraphExpect

open SimpleGraph

variable {V : Type*} (G : SimpleGraph V) [DecidableEq V] [DecidableRel G.Adj] [G.LocallyFinite]
  (v₀ : V) {r : V → ℂ} (hr : ∀ v, r v ≠ 0) (hrs : ∀ v, IsSelfAdjoint (r v))
  {δ : ℝ} [Fact (IsSelfAdjoint (δ : ℂ))]
  (hδ : ∀ v, ∑ u ∈ G.neighborFinset v, r u ^ 2 = (δ : ℂ) * r v ^ 2)
  {tr : ∀ n : ℕ, TemperleyLieb ℂ (δ : ℂ) n →ₗ[ℂ] ℂ} (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
  {f : V → ℕ} (hf : Function.Injective f) (hf₀ : f v₀ = 0)
  (hadj : ∀ {x y}, G.Adj x y → f x + 1 = f y ∨ f y + 1 = f x)

private def graphQuotientExpect (n : ℕ) : htr.Quotient (n + 1) →ₗ[ℂ] htr.Quotient n :=
  (htr.quotientPathAlgebraEquiv G v₀ hr hrs hδ hf hf₀ hadj n).symm.toAlgEquiv.toLinearMap.comp <|
    (walkExpect G v₀ r (δ : ℂ)).comp
      (htr.quotientPathAlgebraEquiv G v₀ hr hrs hδ hf hf₀ hadj (n + 1)).toAlgEquiv.toLinearMap

private theorem graphQuotientExpect_one (hδ₀ : 0 < δ) (n : ℕ) :
    htr.graphQuotientExpect G v₀ hr hrs hδ hf hf₀ hadj n 1 = 1 := by
  have hδc : (δ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hδ₀.ne'
  simp [graphQuotientExpect, walkExpect_one hr hδc hδ]

private theorem graphQuotientExpect_mul_left (hδu : IsUnit (δ : ℂ)) (n : ℕ)
    (x : htr.Quotient n) (y : htr.Quotient (n + 1)) :
    htr.graphQuotientExpect G v₀ hr hrs hδ hf hf₀ hadj n
        (htr.quotientStrandStarAlgHom hδu n x * y) =
      x * htr.graphQuotientExpect G v₀ hr hrs hδ hf hf₀ hadj n y := by
  let e := htr.quotientPathAlgebraEquiv G v₀ hr hrs hδ hf hf₀ hadj
  simp only [graphQuotientExpect, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
    StarAlgEquiv.coe_toAlgEquiv]
  rw [map_mul, htr.quotientPathAlgebraEquiv_quotientStrandStarAlgHom G v₀ hr hrs hδ hδu hf hf₀ hadj,
    walkExpect_walkExtend_mul, map_mul, (e n).symm_apply_apply]

private theorem graphQuotientExpect_mul_right (hδu : IsUnit (δ : ℂ)) (n : ℕ)
    (y : htr.Quotient (n + 1)) (x : htr.Quotient n) :
    htr.graphQuotientExpect G v₀ hr hrs hδ hf hf₀ hadj n
        (y * htr.quotientStrandStarAlgHom hδu n x) =
      htr.graphQuotientExpect G v₀ hr hrs hδ hf hf₀ hadj n y * x := by
  let e := htr.quotientPathAlgebraEquiv G v₀ hr hrs hδ hf hf₀ hadj
  simp only [graphQuotientExpect, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
    StarAlgEquiv.coe_toAlgEquiv]
  rw [map_mul, htr.quotientPathAlgebraEquiv_quotientStrandStarAlgHom G v₀ hr hrs hδ hδu hf hf₀ hadj,
    walkExpect_mul_walkExtend, map_mul, (e n).symm_apply_apply]

private theorem quotientTrace_graphQuotientExpect (n : ℕ) (y : htr.Quotient (n + 1)) :
    (tr n).quotientTrace (htr.map_mul_comm n)
        (htr.graphQuotientExpect G v₀ hr hrs hδ hf hf₀ hadj n y) =
      (δ : ℂ)⁻¹ * (tr (n + 1)).quotientTrace (htr.map_mul_comm (n + 1)) y := by
  let e := htr.quotientPathAlgebraEquiv G v₀ hr hrs hδ hf hf₀ hadj
  rw [← htr.walkTrace_quotientPathAlgebraEquiv G v₀ hr hrs hδ hf hf₀ hadj,
    ← htr.walkTrace_quotientPathAlgebraEquiv G v₀ hr hrs hδ hf hf₀ hadj (x := y)]
  simp only [graphQuotientExpect, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
    StarAlgEquiv.coe_toAlgEquiv]
  rw [(e n).apply_symm_apply, walkTrace_walkExpect hr]

private theorem exists_sum_star_mul_self_graphQuotientExpect (hδ₀ : 0 < δ) (n : ℕ)
    (y : htr.Quotient (n + 1)) :
    ∃ (m : ℕ) (z : Fin m → htr.Quotient n),
      htr.graphQuotientExpect G v₀ hr hrs hδ hf hf₀ hadj n (star y * y) =
        ∑ i : Fin m, star (z i) * z i := by
  let e := htr.quotientPathAlgebraEquiv G v₀ hr hrs hδ hf hf₀ hadj
  obtain ⟨m, Z, hZ⟩ := exists_sum_star_mul_self_walkExpect_star_mul_self hrs hδ₀ (e (n + 1) y)
  refine ⟨m, fun i ↦ (e n).symm (Z i), ?_⟩
  simp only [graphQuotientExpect, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
    StarAlgEquiv.coe_toAlgEquiv]
  rw [map_mul, StarHomClass.map_star]
  exact (congrArg (e n).symm hZ).trans <|
    (map_sum (e n).symm _ _).trans <|
      Finset.sum_congr rfl fun i _ ↦ by rw [map_mul, StarHomClass.map_star]

end GraphExpect

section JonesTower

open Real SimpleGraph

/-- For `δ ∈ jonesLoopParameters`, `(δ : ℂ)` is a unit since `δ ≥ 1 > 0`. -/
theorem isUnit_of_mem_jonesLoopParameters {δ : ℝ} (hδ : δ ∈ jonesLoopParameters) :
    IsUnit (δ : ℂ) :=
  (Complex.ofReal_ne_zero.2 (pos_of_mem_jonesLoopParameters hδ).ne').isUnit

variable {δ : ℝ} [Fact (IsSelfAdjoint (δ : ℂ))]
  {tr : ∀ n : ℕ, TemperleyLieb ℂ (δ : ℂ) n →ₗ[ℂ] ℂ} (htr : IsMarkovTrace ℂ (δ : ℂ) tr)

theorem positiveQuotientTrace_eq_quotientTrace (hδ : δ ∈ jonesLoopParameters) (n : ℕ)
    (x : htr.Quotient n) :
    htr.positiveQuotientTrace hδ n x = (tr n).quotientTrace (htr.map_mul_comm n) x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact (htr.positiveQuotientTrace_mk hδ a).trans
    ((tr n).quotientTrace_mk (htr.map_mul_comm n) a).symm

/-- Unital strand `⋆`-inclusion `htr.Quotient n →⋆ₐ[ℂ] htr.Quotient (n + 1)` at an admissible loop
parameter (`n ≥ 0`). -/
def jonesStrandIncl (hδ : δ ∈ jonesLoopParameters) (n : ℕ) :
    htr.Quotient n →⋆ₐ[ℂ] htr.Quotient (n + 1) :=
  htr.quotientStrandStarAlgHom (isUnit_of_mem_jonesLoopParameters hδ) n

@[simp]
theorem jonesStrandIncl_mk (hδ : δ ∈ jonesLoopParameters) (n : ℕ)
    (x : TemperleyLieb ℂ (δ : ℂ) n) :
    htr.jonesStrandIncl hδ n (Ideal.Quotient.mk (htr.traceRadical n) x) =
      Ideal.Quotient.mk (htr.traceRadical (n + 1)) (strandInclAll n x) :=
  htr.quotientStrandStarAlgHom_mk _ n x

theorem jonesStrandIncl_succ_apply (hδ : δ ∈ jonesLoopParameters) (n : ℕ)
    (x : htr.Quotient (n + 1)) :
    htr.jonesStrandIncl hδ (n + 1) x = htr.quotientStrandIncl n x :=
  htr.quotientStrandStarAlgHom_succ_apply _ n x

theorem jonesStrandIncl_injective (hδ : δ ∈ jonesLoopParameters) (n : ℕ) :
    Function.Injective (htr.jonesStrandIncl hδ n) :=
  htr.quotientStrandStarAlgHom_injective _ n

@[simp]
theorem positiveQuotientTrace_jonesStrandIncl (hδ : δ ∈ jonesLoopParameters) (n : ℕ)
    (x : htr.Quotient n) :
    htr.positiveQuotientTrace hδ (n + 1) (htr.jonesStrandIncl hδ n x) =
      (δ : ℂ) * htr.positiveQuotientTrace hδ n x := by
  rw [htr.positiveQuotientTrace_eq_quotientTrace, htr.positiveQuotientTrace_eq_quotientTrace]
  exact htr.quotientTrace_quotientStrandStarAlgHom _ n x

/-- **Trace-preserving conditional expectation on positive Jones quotients.** Constructed by
transporting `walkExpect` along the discrete (`A_(m-1)`) or generic (`A_∞`) multimatrix equivalence,
and uniquely determined by compatibility with `jonesStrandIncl` and `positiveQuotientTrace`. -/
def quotientExpect (hδ : δ ∈ jonesLoopParameters) (n : ℕ) :
    htr.Quotient (n + 1) →ₗ[ℂ] htr.Quotient n := by
  classical
  exact if hm : ∃ m : ℕ, 3 ≤ m ∧ δ = 2 * cos (π / m) then
    let m := Classical.choose hm
    have hm_spec := Classical.choose_spec hm
    htr.graphQuotientExpect (pathGraph (m - 1)) ⟨0, Nat.sub_pos_of_lt (by omega)⟩
      (discretePathWeight_ne_zero hm_spec.1) (isSelfAdjoint_discretePathWeight m)
      (fun v ↦ by rw [hm_spec.2]; exact sum_neighborFinset_discretePathWeight_sq hm_spec.1 v)
      Fin.val_injective rfl (fun h ↦ pathGraph_adj.1 h) n
  else
    have h2 : 2 ≤ δ := ((mem_jonesLoopParameters.1 hδ).resolve_left hm)
    htr.graphQuotientExpect (hasse ℕ) 0
      (genericPathWeight_ne_zero h2) (isSelfAdjoint_genericPathWeight δ)
      (sum_neighborFinset_genericPathWeight_sq h2)
      Function.injective_id rfl (fun h ↦ hasse_nat_adj.1 h) n

@[simp]
theorem quotientExpect_one (hδ : δ ∈ jonesLoopParameters) (n : ℕ) :
    htr.quotientExpect hδ n 1 = 1 := by
  have hpos := pos_of_mem_jonesLoopParameters hδ
  rw [quotientExpect]
  split_ifs with hm
  · exact htr.graphQuotientExpect_one _ _ _ _ _ _ _ (fun h ↦ pathGraph_adj.1 h) hpos n
  · exact htr.graphQuotientExpect_one _ _ _ _ _ _ _ (fun h ↦ hasse_nat_adj.1 h) hpos n

@[simp]
theorem quotientExpect_mul_left (hδ : δ ∈ jonesLoopParameters) {n : ℕ}
    (x : htr.Quotient n) (y : htr.Quotient (n + 1)) :
    htr.quotientExpect hδ n (htr.jonesStrandIncl hδ n x * y) =
      x * htr.quotientExpect hδ n y := by
  rw [quotientExpect, jonesStrandIncl]
  split_ifs with hm
  · exact htr.graphQuotientExpect_mul_left _ _ _ _ _ _ _ (fun h ↦ pathGraph_adj.1 h) _ n x y
  · exact htr.graphQuotientExpect_mul_left _ _ _ _ _ _ _ (fun h ↦ hasse_nat_adj.1 h) _ n x y

@[simp]
theorem quotientExpect_mul_right (hδ : δ ∈ jonesLoopParameters) {n : ℕ}
    (y : htr.Quotient (n + 1)) (x : htr.Quotient n) :
    htr.quotientExpect hδ n (y * htr.jonesStrandIncl hδ n x) =
      htr.quotientExpect hδ n y * x := by
  rw [quotientExpect, jonesStrandIncl]
  split_ifs with hm
  · exact htr.graphQuotientExpect_mul_right _ _ _ _ _ _ _ (fun h ↦ pathGraph_adj.1 h) _ n y x
  · exact htr.graphQuotientExpect_mul_right _ _ _ _ _ _ _ (fun h ↦ hasse_nat_adj.1 h) _ n y x

@[simp]
theorem quotientExpect_jonesStrandIncl (hδ : δ ∈ jonesLoopParameters) {n : ℕ}
    (x : htr.Quotient n) :
    htr.quotientExpect hδ n (htr.jonesStrandIncl hδ n x) = x := by
  rw [← mul_one (htr.jonesStrandIncl hδ n x), htr.quotientExpect_mul_left,
    htr.quotientExpect_one, mul_one]

@[simp]
theorem positiveQuotientTrace_quotientExpect (hδ : δ ∈ jonesLoopParameters) {n : ℕ}
    (y : htr.Quotient (n + 1)) :
    htr.positiveQuotientTrace hδ n (htr.quotientExpect hδ n y) =
      (δ : ℂ)⁻¹ * htr.positiveQuotientTrace hδ (n + 1) y := by
  rw [htr.positiveQuotientTrace_eq_quotientTrace, htr.positiveQuotientTrace_eq_quotientTrace,
    quotientExpect]
  split_ifs with hm
  · exact htr.quotientTrace_graphQuotientExpect _ _ _ _ _ _ _ (fun h ↦ pathGraph_adj.1 h) n y
  · exact htr.quotientTrace_graphQuotientExpect _ _ _ _ _ _ _ (fun h ↦ hasse_nat_adj.1 h) n y

theorem exists_sum_star_mul_self_quotientExpect_star_mul_self (hδ : δ ∈ jonesLoopParameters)
    {n : ℕ} (y : htr.Quotient (n + 1)) :
    ∃ (m : ℕ) (z : Fin m → htr.Quotient n),
       htr.quotientExpect hδ n (star y * y) = ∑ i : Fin m, star (z i) * z i := by
  have hpos := pos_of_mem_jonesLoopParameters hδ
  rw [quotientExpect]
  split_ifs with hm
  · exact htr.exists_sum_star_mul_self_graphQuotientExpect _ _ _ _ _ _ _
      (fun h ↦ pathGraph_adj.1 h) hpos n y
  · exact htr.exists_sum_star_mul_self_graphQuotientExpect _ _ _ _ _ _ _
      (fun h ↦ hasse_nat_adj.1 h) hpos n y

/-- **Uniqueness of the trace-compatible conditional expectation.** Any linear map
`F : htr.Quotient (n + 1) →ₗ[ℂ] htr.Quotient n` that is left `htr.Quotient n`-linear along
`jonesStrandIncl` and scales `positiveQuotientTrace` by `δ⁻¹` equals `quotientExpect`. -/
theorem quotientExpect_unique (hδ : δ ∈ jonesLoopParameters) {n : ℕ}
    (F : htr.Quotient (n + 1) →ₗ[ℂ] htr.Quotient n)
    (hmul : ∀ (x : htr.Quotient n) (y : htr.Quotient (n + 1)),
      F (htr.jonesStrandIncl hδ n x * y) = x * F y)
    (htrace : ∀ y : htr.Quotient (n + 1),
      htr.positiveQuotientTrace hδ n (F y) =
        (δ : ℂ)⁻¹ * htr.positiveQuotientTrace hδ (n + 1) y) :
    F = htr.quotientExpect hδ n := by
  ext y
  rw [← sub_eq_zero]
  set d := F y - htr.quotientExpect hδ n y
  have horth (x : htr.Quotient n) : htr.positiveQuotientTrace hδ n (x * d) = 0 := by
    rw [mul_sub, map_sub, ← hmul, ← htr.quotientExpect_mul_left, htrace,
      htr.positiveQuotientTrace_quotientExpect, sub_self]
  have hnull : d ∈ (htr.positiveQuotientTrace hδ n).nullSubmodule := by
    rw [StarPositiveFunctional.mem_nullSubmodule_iff_apply_star_mul_self_eq_zero]
    exact horth (star d)
  rwa [htr.nullSubmodule_positiveQuotientTrace hδ n, Submodule.mem_bot] at hnull

/-- **Scaled last-strand closure.** `quotientExpect` sends the last Temperley–Lieb generator
`mk (e δ (Fin.last n))` on `n + 2` strands to `δ⁻¹ • 1`. -/
@[simp]
theorem quotientExpect_mk_e_last (hδ : δ ∈ jonesLoopParameters) (n : ℕ) :
    htr.quotientExpect hδ (n + 1)
        (Ideal.Quotient.mk (htr.traceRadical (n + 2)) (e (δ : ℂ) (Fin.last n))) =
      (δ : ℂ)⁻¹ • 1 := by
  rw [← sub_eq_zero]
  set d := htr.quotientExpect hδ (n + 1)
    (Ideal.Quotient.mk (htr.traceRadical (n + 2)) (e (δ : ℂ) (Fin.last n))) - (δ : ℂ)⁻¹ • 1
  have horth (x : htr.Quotient (n + 1)) : htr.positiveQuotientTrace hδ (n + 1) (x * d) = 0 := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [mul_sub, map_sub, ← htr.quotientExpect_mul_left, htr.positiveQuotientTrace_quotientExpect,
      htr.jonesStrandIncl_mk, strandInclAll_succ, ← map_mul, htr.positiveQuotientTrace_mk,
      htr.map_strandIncl_mul_e_last, mul_smul_comm, mul_one, map_smul,
      htr.positiveQuotientTrace_mk, smul_eq_mul, sub_self]
  have hnull : d ∈ (htr.positiveQuotientTrace hδ (n + 1)).nullSubmodule := by
    rw [StarPositiveFunctional.mem_nullSubmodule_iff_apply_star_mul_self_eq_zero]
    exact horth (star d)
  rwa [htr.nullSubmodule_positiveQuotientTrace hδ (n + 1), Submodule.mem_bot] at hnull

/-- On the tower normal form `ι a * mk (e δ (Fin.last n)) * ι b`, `quotientExpect` acts as the
scaled last-strand closure `δ⁻¹ • (a * b)`. -/
theorem quotientExpect_mul_mk_e_last_mul (hδ : δ ∈ jonesLoopParameters) {n : ℕ}
    (a b : htr.Quotient (n + 1)) :
    htr.quotientExpect hδ (n + 1)
        (htr.jonesStrandIncl hδ (n + 1) a *
          Ideal.Quotient.mk (htr.traceRadical (n + 2)) (e (δ : ℂ) (Fin.last n)) *
          htr.jonesStrandIncl hδ (n + 1) b) =
      (δ : ℂ)⁻¹ • (a * b) := by
  rw [htr.quotientExpect_mul_right, htr.quotientExpect_mul_left, htr.quotientExpect_mk_e_last,
    mul_smul_comm, mul_one, smul_mul_assoc]

/-- The **Jones projection** `p_n = δ⁻¹ • mk (e δ (Fin.last n))` in `htr.Quotient (n + 2)`. -/
def jonesProjection (n : ℕ) : htr.Quotient (n + 2) :=
  (δ : ℂ)⁻¹ • Ideal.Quotient.mk (htr.traceRadical (n + 2)) (e (δ : ℂ) (Fin.last n))

theorem isSelfAdjoint_jonesProjection (n : ℕ) : IsSelfAdjoint (htr.jonesProjection n) := by
  rw [IsSelfAdjoint, jonesProjection, star_smul, Ideal.Quotient.star_mk, star_e,
    star_inv₀, IsSelfAdjoint.star_eq (Complex.conj_ofReal _)]

omit [Fact (IsSelfAdjoint (δ : ℂ))] in
theorem isIdempotentElem_jonesProjection (hδ : δ ≠ 0) (n : ℕ) :
    IsIdempotentElem (htr.jonesProjection n) := by
  have hδc : (δ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hδ
  rw [IsIdempotentElem, jonesProjection, ← Ideal.Quotient.mkₐ_eq_mk ℂ, smul_mul_smul_comm,
    ← map_mul, e_mul_self, map_smul, smul_smul, mul_assoc, inv_mul_cancel₀ hδc, mul_one]

@[simp]
theorem quotientExpect_jonesProjection (hδ : δ ∈ jonesLoopParameters) (n : ℕ) :
    htr.quotientExpect hδ (n + 1) (htr.jonesProjection n) = ((δ : ℂ)⁻¹ ^ 2) • 1 := by
  rw [jonesProjection, map_smul, htr.quotientExpect_mk_e_last, smul_smul, sq]

/-- **Unnormalized Markov formula** on the positive Jones quotients:
`τ_{n+2} (ι x * p_n) = δ⁻¹ * τ_{n+1} x`. -/
@[simp]
theorem positiveQuotientTrace_jonesStrandIncl_mul_jonesProjection (hδ : δ ∈ jonesLoopParameters)
    {n : ℕ} (x : htr.Quotient (n + 1)) :
    htr.positiveQuotientTrace hδ (n + 2)
        (htr.jonesStrandIncl hδ (n + 1) x * htr.jonesProjection n) =
      (δ : ℂ)⁻¹ * htr.positiveQuotientTrace hδ (n + 1) x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [htr.jonesStrandIncl_mk, strandInclAll_succ, jonesProjection, mul_smul_comm, ← map_mul,
    map_smul, htr.positiveQuotientTrace_mk, htr.map_strandIncl_mul_e_last,
    htr.positiveQuotientTrace_mk, smul_eq_mul]

/-- The **normalized faithful positive trace** `δ⁻ⁿ • positiveQuotientTrace` on `htr.Quotient n`,
taking value `1` on the unit. -/
def normalizedQuotientTrace (hδ : δ ∈ jonesLoopParameters) (n : ℕ) :
    StarPositiveFunctional (htr.Quotient n) where
  toLinearMap := ((δ : ℂ)⁻¹ ^ n) • (htr.positiveQuotientTrace hδ n).toLinearMap
  square_nonneg x := by
    have hpos : 0 ≤ (((δ⁻¹ ^ n : ℝ) : ℂ)) :=
      Complex.zero_le_real.2 (pow_nonneg (inv_nonneg.2 (pos_of_mem_jonesLoopParameters hδ).le) n)
    have hcast : ((δ : ℂ)⁻¹ ^ n) = ((δ⁻¹ ^ n : ℝ) : ℂ) := by push_cast; rfl
    rw [LinearMap.smul_apply, smul_eq_mul, hcast]
    exact mul_nonneg hpos ((htr.positiveQuotientTrace hδ n).square_nonneg x)

theorem normalizedQuotientTrace_apply (hδ : δ ∈ jonesLoopParameters) {n : ℕ}
    (x : htr.Quotient n) :
    htr.normalizedQuotientTrace hδ n x =
      (δ : ℂ)⁻¹ ^ n * htr.positiveQuotientTrace hδ n x :=
  (rfl)

@[simp]
theorem normalizedQuotientTrace_one (hδ : δ ∈ jonesLoopParameters) (n : ℕ) :
    htr.normalizedQuotientTrace hδ n 1 = 1 := by
  have hδc : (δ : ℂ) ≠ 0 := (isUnit_of_mem_jonesLoopParameters hδ).ne_zero
  rw [normalizedQuotientTrace_apply, htr.positiveQuotientTrace_one, inv_pow, inv_mul_cancel₀
    (pow_ne_zero n hδc)]

theorem normalizedQuotientTrace_mul_comm (hδ : δ ∈ jonesLoopParameters) {n : ℕ}
    (x y : htr.Quotient n) :
    htr.normalizedQuotientTrace hδ n (x * y) = htr.normalizedQuotientTrace hδ n (y * x) := by
  simp only [normalizedQuotientTrace_apply, htr.positiveQuotientTrace_mul_comm]

@[simp]
theorem nullSubmodule_normalizedQuotientTrace (hδ : δ ∈ jonesLoopParameters) (n : ℕ) :
    (htr.normalizedQuotientTrace hδ n).nullSubmodule = ⊥ := by
  have hδc : (δ : ℂ) ≠ 0 := (isUnit_of_mem_jonesLoopParameters hδ).ne_zero
  have hpow : (δ : ℂ)⁻¹ ^ n ≠ 0 := pow_ne_zero n (inv_ne_zero hδc)
  ext x
  rw [Submodule.mem_bot,
    StarPositiveFunctional.mem_nullSubmodule_iff_apply_star_mul_self_eq_zero,
    normalizedQuotientTrace_apply, mul_eq_zero, or_iff_right hpow,
    ← StarPositiveFunctional.mem_nullSubmodule_iff_apply_star_mul_self_eq_zero
      (htr.positiveQuotientTrace hδ n),
    htr.nullSubmodule_positiveQuotientTrace hδ n, Submodule.mem_bot]

/-- `normalizedQuotientTrace` is preserved by `jonesStrandIncl` at every level `n ≥ 0`. -/
@[simp]
theorem normalizedQuotientTrace_jonesStrandIncl (hδ : δ ∈ jonesLoopParameters) {n : ℕ}
    (x : htr.Quotient n) :
    htr.normalizedQuotientTrace hδ (n + 1) (htr.jonesStrandIncl hδ n x) =
      htr.normalizedQuotientTrace hδ n x := by
  have hδc : (δ : ℂ) ≠ 0 := (isUnit_of_mem_jonesLoopParameters hδ).ne_zero
  rw [normalizedQuotientTrace_apply, htr.positiveQuotientTrace_jonesStrandIncl,
    normalizedQuotientTrace_apply, pow_succ]
  calc (δ : ℂ)⁻¹ ^ n * (δ : ℂ)⁻¹ * ((δ : ℂ) * htr.positiveQuotientTrace hδ n x)
      = (δ : ℂ)⁻¹ ^ n * ((δ : ℂ)⁻¹ * (δ : ℂ)) * htr.positiveQuotientTrace hδ n x := by ring
    _ = (δ : ℂ)⁻¹ ^ n * htr.positiveQuotientTrace hδ n x := by
        rw [inv_mul_cancel₀ hδc, mul_one]

/-- `quotientExpect` preserves the normalized trace `normalizedQuotientTrace`. -/
@[simp]
theorem normalizedQuotientTrace_quotientExpect (hδ : δ ∈ jonesLoopParameters) {n : ℕ}
    (y : htr.Quotient (n + 1)) :
    htr.normalizedQuotientTrace hδ n (htr.quotientExpect hδ n y) =
      htr.normalizedQuotientTrace hδ (n + 1) y := by
  rw [normalizedQuotientTrace_apply, htr.positiveQuotientTrace_quotientExpect,
    normalizedQuotientTrace_apply, pow_succ]
  ring

/-- **Normalized Markov formula** on the positive Jones quotients:
`tr_{n+2} (ι x * p_n) = δ⁻² * tr_{n+1} x`. -/
@[simp]
theorem normalizedQuotientTrace_jonesStrandIncl_mul_jonesProjection (hδ : δ ∈ jonesLoopParameters)
    {n : ℕ} (x : htr.Quotient (n + 1)) :
    htr.normalizedQuotientTrace hδ (n + 2)
        (htr.jonesStrandIncl hδ (n + 1) x * htr.jonesProjection n) =
      (δ : ℂ)⁻¹ ^ 2 * htr.normalizedQuotientTrace hδ (n + 1) x := by
  rw [normalizedQuotientTrace_apply, htr.positiveQuotientTrace_jonesStrandIncl_mul_jonesProjection,
    normalizedQuotientTrace_apply, pow_succ]
  ring

end JonesTower

section CStarTower

variable {δ : ℝ} [Fact (IsSelfAdjoint (δ : ℂ))]
  {tr : ∀ n : ℕ, TemperleyLieb ℂ (δ : ℂ) n →ₗ[ℂ] ℂ} (htr : IsMarkovTrace ℂ (δ : ℂ) tr)

/-- The C⋆-algebra structure on `htr.Quotient n` (`δ ∈ jonesLoopParameters`) induced by the operator
norm of left multiplication on the GNS Hilbert space of `positiveQuotientTrace`. -/
@[expose, implicit_reducible]
def cstarAlgebraQuotient (hδ : δ ∈ jonesLoopParameters) (n : ℕ) : CStarAlgebra (htr.Quotient n) :=
  letI := htr.finiteDimensional_quotient hδ n
  (htr.positiveQuotientTrace hδ n).cstarAlgebra (htr.nullSubmodule_positiveQuotientTrace hδ n)

instance instFiniteDimensionalQuotient [hδ : Fact (δ ∈ jonesLoopParameters)] (n : ℕ) :
    FiniteDimensional ℂ (htr.Quotient n) :=
  htr.finiteDimensional_quotient hδ.out n

noncomputable instance instCStarAlgebraQuotient [hδ : Fact (δ ∈ jonesLoopParameters)] (n : ℕ) :
    CStarAlgebra (htr.Quotient n) :=
  htr.cstarAlgebraQuotient hδ.out n

noncomputable instance instPartialOrderQuotient [Fact (δ ∈ jonesLoopParameters)] (n : ℕ) :
    PartialOrder (htr.Quotient n) :=
  CStarAlgebra.spectralOrder (htr.Quotient n)

instance instStarOrderedRingQuotient [Fact (δ ∈ jonesLoopParameters)] (n : ℕ) :
    StarOrderedRing (htr.Quotient n) :=
  CStarAlgebra.spectralOrderedRing (htr.Quotient n)

/-- Every strand map `htr.jonesStrandIncl` (`n ≥ 0`) is an isometric unital `⋆`-homomorphism for the
GNS C⋆-norms on the positive Jones quotients. -/
theorem isometry_jonesStrandIncl [hδ : Fact (δ ∈ jonesLoopParameters)] (n : ℕ) :
    Isometry (htr.jonesStrandIncl hδ.out n) :=
  NonUnitalStarAlgHom.isometry (htr.jonesStrandIncl hδ.out n)
    (htr.jonesStrandIncl_injective hδ.out n)

theorem norm_jonesStrandIncl [hδ : Fact (δ ∈ jonesLoopParameters)] (n : ℕ) (x : htr.Quotient n) :
    ‖htr.jonesStrandIncl hδ.out n x‖ = ‖x‖ :=
  NonUnitalStarAlgHom.norm_map (htr.jonesStrandIncl hδ.out n)
    (htr.jonesStrandIncl_injective hδ.out n) x

theorem quotientExpect_nonneg [hδ : Fact (δ ∈ jonesLoopParameters)] {n : ℕ}
    {y : htr.Quotient (n + 1)} (hy : 0 ≤ y) :
    0 ≤ htr.quotientExpect hδ.out n y := by
  let _ : NonUnitalContinuousFunctionalCalculus ℝ (htr.Quotient (n + 1)) IsSelfAdjoint :=
    IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus
  let _ : NonnegSpectrumClass ℝ (htr.Quotient (n + 1)) :=
    CStarAlgebra.instNonnegSpectrumClass'
  obtain ⟨r, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hy
  obtain ⟨m, z, hz⟩ := htr.exists_sum_star_mul_self_quotientExpect_star_mul_self hδ.out r
  rw [hz]
  exact Finset.sum_nonneg fun i _ ↦ star_mul_self_nonneg (z i)

/-- **C⋆-conditional expectation on the positive Jones quotient tower.** Bundles `quotientExpect`
as a unital positive bimodule retraction onto `jonesStrandIncl`; by
`CStarConditionalExpectation.instCompletelyPositiveMapClass`, it is automatically completely
positive and coerces to `htr.Quotient (n + 1) →CP htr.Quotient n`. -/
def cstarConditionalExpectation [hδ : Fact (δ ∈ jonesLoopParameters)] (n : ℕ) :
    CStarConditionalExpectation (htr.jonesStrandIncl hδ.out n) where
  toPositiveLinearMap := .mk₀ (htr.quotientExpect hδ.out n) fun _ hy ↦
    htr.quotientExpect_nonneg hy
  map_one' := htr.quotientExpect_one hδ.out n
  map_mul_left' := htr.quotientExpect_mul_left hδ.out
  map_mul_right' := htr.quotientExpect_mul_right hδ.out

@[simp]
theorem cstarConditionalExpectation_apply [hδ : Fact (δ ∈ jonesLoopParameters)] (n : ℕ)
    (y : htr.Quotient (n + 1)) :
    cstarConditionalExpectation htr n y = htr.quotientExpect hδ.out n y :=
  (rfl)

/-- Reinterpret `cstarConditionalExpectation` as a `CompletelyPositiveMap`. -/
def completelyPositiveExpectation [Fact (δ ∈ jonesLoopParameters)] (n : ℕ) :
    htr.Quotient (n + 1) →CP htr.Quotient n :=
  cstarConditionalExpectation htr n

@[simp]
theorem completelyPositiveExpectation_apply [hδ : Fact (δ ∈ jonesLoopParameters)] (n : ℕ)
    (y : htr.Quotient (n + 1)) :
    completelyPositiveExpectation htr n y = htr.quotientExpect hδ.out n y :=
  (rfl)

end CStarTower

end IsMarkovTrace

end TauCeti.TemperleyLieb
