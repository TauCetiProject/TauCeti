/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import TauCeti.Analysis.InnerProductSpace.FullFockSpace.Field
public import TauCeti.Analysis.InnerProductSpace.Gram.PosSemidef
public import TauCeti.Combinatorics.NoncrossingPartition.Pairing
public import TauCeti.Combinatorics.PlanarMatching.Basic
public import TauCeti.Probability.FreeProbability.Semicircular.Law
public import TauCeti.Probability.FreeProbability.Semicircular.System
public import TauCeti.Probability.FreeProbability.StarIndependence
public import TauCeti.Probability.FreeProbability.WeakClosure
import TauCeti.Analysis.CStarAlgebra.GNS.Basic
import TauCeti.Data.Finset.Basic

/-!
# Full Fock space realization of semicircular systems and `⋆`-freeness

Let `H` be an inner product space over `𝕜` (`ℝ` or `ℂ`), and let `vacuumState 𝕜 H` be the vacuum
vector functional `T ↦ ⟪vacuum, T vacuum⟫_𝕜` on `FullFockSpace 𝕜 H →L[𝕜] FullFockSpace 𝕜 H`.

1. **Free Wick formula and joint free cumulants (`ℓ(u) + ℓ(w)*`).** For any finite ordered set `s`
   of positions and families `u, w : α → H`, the vacuum expectation of the ordered product of
   `creation 𝕜 (u i) + annihilation 𝕜 (w i)` along `s` is the sum over noncrossing pairings of `s`
   of the pair weights `⟪w a, u b⟫_𝕜` (`a < b`). Equivalently, the joint free cumulants of
   `i ↦ creation 𝕜 (u i) + annihilation 𝕜 (w i)` vanish in all orders `n ≠ 2`, while
   `κ₂(ℓ(u₁) + ℓ(w₁)*, ℓ(u₂) + ℓ(w₂)*) = ⟪w₁, u₂⟫_𝕜`.

2. **Semicircular systems and `⋆`-freeness from orthogonality.** Specialising `u = w = h`, the
   self-adjoint field operators `i ↦ field 𝕜 (h i)` form a semicircular system with covariance
   `Matrix.gram 𝕜 h`; in particular each `field 𝕜 h` is semicircular of variance `(‖h‖ ^ 2 : 𝕜)`
   and `(field 𝕜 (h i))` is freely independent if and only if `(h i)` is pairwise orthogonal.
   Strengthening to generating sets `S : ι → Set H`, the unital `⋆`-subalgebras
   `StarAlgebra.adjoin 𝕜 (creation 𝕜 '' S i)`, their norm closures, and their weak operator
   closures — as well as the unital subalgebras `Algebra.adjoin 𝕜 (field 𝕜 '' S i)` — are freely
   independent under `vacuumState 𝕜 H` if and only if the sets `S i` are pairwise orthogonal.

3. **Semicircle C⋆-laws, real Hilbert space complexification, and covariance realization.** Over
   `ℂ`, `field ℂ h` has law `semicircleReal 0 (‖h‖₊ ^ 2)` and `r • field ℂ h + m` has law
   `semicircleReal m (Real.toNNReal (r ^ 2) * ‖h‖₊ ^ 2)`. Embedding a real inner product space `X`
   into its `L²` complexification `WithLp 2 (Complexification X)` via `realField` turns every
   family `x : ι → X` into a self-adjoint semicircular system in a complex C⋆-probability space
   with covariance `(Matrix.gram ℝ x).map ((↑) : ℝ → ℂ)`, and turns pairwise orthogonal real
   subspaces into `⋆`-free subalgebras. Combining this with the Gram realization
   `Matrix.PosSemidef.exists_gram_eq` and GNS `⋆`-moment positivity characterizes positive
   semidefiniteness for both complex and real matrices `C` of arbitrary index type `ι` by the
   existence of a self-adjoint semicircular system in a C⋆-probability space with covariance `C`
   (respectively `C.map ((↑) : ℝ → ℂ)`).

## Main results

* `TauCeti.FullFockSpace.vacuumState_prod_creation_add_annihilation`,
  `TauCeti.FullFockSpace.vacuumState_prod_field`,
  `TauCeti.FullFockSpace.vacuumState_prod_ofFn_field_eq_sum_planarMatching`: the free Wick formula
  on full Fock space.
* `TauCeti.FullFockSpace.freeCumulant_vacuumState_creation_add_annihilation`,
  `TauCeti.FullFockSpace.freeCumulant_vacuumState_field`: joint free cumulants of creation +
  annihilation and field operators.
* `TauCeti.FullFockSpace.isSemicircularSystem_vacuumState_field`,
  `TauCeti.FullFockSpace.isSemicircular_vacuumState_field`: field operators form a semicircular
  system with Gram covariance.
* In `TauCeti.FullFockSpace`, `isFreelyIndependent_vacuumState_starAlgebraAdjoin_creation_iff`,
  `isStarFreelyIndependentElements_vacuumState_creation_iff`,
  `isFreelyIndependent_vacuumState_adjoin_field_iff`,
  `isFreelyIndependent_vacuumState_topologicalClosure_starAlgebraAdjoin_creation_iff`, and
  `isFreelyIndependent_vacuumState_weakOperatorClosure_starAlgebraAdjoin_creation_iff`:
  `⋆`-freeness and subalgebra freeness are equivalent to pairwise orthogonality.
* `TauCeti.FullFockSpace.law_vacuumState_field`,
  `TauCeti.FullFockSpace.law_vacuumState_smul_field_add_algebraMap`,
  `TauCeti.FullFockSpace.law_vacuumState_field_ofReal_sqrt_add_algebraMap`: C⋆-algebraic semicircle
  laws of field operators and their affine images.
* In `TauCeti.FullFockSpace`, `isSemicircularSystem_vacuumState_realField`,
  `law_vacuumState_smul_realField_add_algebraMap`,
  `isFreelyIndependent_vacuumState_starAlgebraAdjoin_creation_complexifyL2_iff`, and
  `isFreelyIndependent_vacuumState_adjoin_realField_iff`: Fock realization over complexified real
  inner product spaces.
* `Matrix.PosSemidef.exists_isSemicircularSystem_vacuumState_field`,
  `Matrix.PosSemidef.exists_isSemicircularSystem_vacuumState_realField`,
  `Matrix.PosSemidef.exists_euclideanSpace_isSemicircularSystem_vacuumState_realField`,
  `Matrix.posSemidef_iff_exists_cstar_isSelfAdjoint_and_isSemicircularSystem`,
  `Matrix.posSemidef_real_iff_exists_cstar_isSelfAdjoint_and_isSemicircularSystem`: every
  positive-semidefinite covariance matrix is realized on full Fock space, characterizing complex
  and real positive-semidefinite matrices via C⋆-semicircular systems.

## References

* D. V. Voiculescu, K. J. Dykema, A. Nica, *Free Random Variables*, CRM Monograph Series, Vol. 1,
  American Mathematical Society, 1992, §2.6.
* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, London Mathematical
  Society Lecture Note Series, Vol. 335, Cambridge University Press, 2006, Lectures 7, 8, and 11
  (Propositions 7.18 and 11.24, Corollary 11.25).
-/

public section

noncomputable section

open Finset Matrix MeasureTheory NNReal TauCeti.Probability
open scoped ComplexOrder InnerProductSpace Pointwise

namespace TauCeti

universe u v

namespace FullFockSpace

/-! ### Free Wick formula and free cumulants of `ℓ(u) + ℓ(w)*` -/

section Wick

variable {𝕜 : Type u} {H : Type v} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  {α : Type*} [LinearOrder α]

/-- Shorthand for the ordered product of `creation 𝕜 (u i) + annihilation 𝕜 (w i)` along `s`. -/
private def prodGenOp (u w : α → H) (s : Finset α) :
    FullFockSpace 𝕜 H →L[𝕜] FullFockSpace 𝕜 H :=
  (s.sort.map fun i => creation 𝕜 (u i) + annihilation 𝕜 (w i)).prod

private theorem prodGenOp_empty (u w : α → H) : prodGenOp (𝕜 := 𝕜) u w ∅ = 1 := by
  simp [prodGenOp]

private theorem prodGenOp_nonempty {s : Finset α} (hs : s.Nonempty) (u w : α → H) :
    prodGenOp (𝕜 := 𝕜) u w s =
      (creation 𝕜 (u (s.min' hs)) + annihilation 𝕜 (w (s.min' hs))) *
        prodGenOp (𝕜 := 𝕜) u w {y ∈ s | s.min' hs < y} := by
  have hins : insert (s.min' hs) {y ∈ s | s.min' hs < y} = s := by
    rw [filter_min'_lt_eq_erase hs, insert_erase (s.min'_mem hs)]
  have hsort : s.sort = s.min' hs :: {y ∈ s | s.min' hs < y}.sort := by
    conv_lhs => rw [← hins]
    exact sort_insert _ (fun y hy => (mem_filter.1 hy).2.le) fun h => (mem_filter.1 h).2.false
  rw [prodGenOp, hsort, List.map_cons, List.prod_cons, ← prodGenOp]

private theorem inner_vacuum_prodGenOp_of_ih (u w : α → H) {t : Finset α} (ht : t.Nonempty)
    (ih_after : ∀ (a : H) (v : List H),
      ⟪wordVector 𝕜 (a :: v), prodGenOp (𝕜 := 𝕜) u w {z ∈ t | t.min' ht < z} vacuum⟫_𝕜 =
        ∑ y ∈ {z ∈ t | t.min' ht < z},
          ⟪a, u y⟫_𝕜 *
            ⟪vacuum, prodGenOp (𝕜 := 𝕜) u w {z ∈ {z ∈ t | t.min' ht < z} | z < y} vacuum⟫_𝕜 *
            ⟪wordVector 𝕜 v,
              prodGenOp (𝕜 := 𝕜) u w {z ∈ {z ∈ t | t.min' ht < z} | y < z} vacuum⟫_𝕜) :
    ⟪vacuum, prodGenOp (𝕜 := 𝕜) u w t vacuum⟫_𝕜 =
      ∑ y ∈ t with t.min' ht < y,
        ⟪w (t.min' ht), u y⟫_𝕜 *
          ⟪vacuum, prodGenOp (𝕜 := 𝕜) u w {z ∈ t | t.min' ht < z ∧ z < y} vacuum⟫_𝕜 *
          ⟪vacuum, prodGenOp (𝕜 := 𝕜) u w {z ∈ t | y < z} vacuum⟫_𝕜 := by
  set m := t.min' ht
  have hvac : ⟪vacuum, prodGenOp (𝕜 := 𝕜) u w t vacuum⟫_𝕜 =
      ⟪wordVector 𝕜 [w m], prodGenOp (𝕜 := 𝕜) u w {z ∈ t | m < z} vacuum⟫_𝕜 := by
    rw [prodGenOp_nonempty ht, mul_apply_eq_comp, add_apply,
      inner_add_right, inner_vacuum_creation, zero_add, inner_annihilation_right,
      wordVector_cons, wordVector_nil]
  rw [hvac, ih_after (w m) [], wordVector_nil]
  refine sum_congr rfl fun y hy => ?_
  have hmy : m < y := (mem_filter.1 hy).2
  have h1 : {z ∈ {z ∈ t | m < z} | z < y} = {z ∈ t | m < z ∧ z < y} := filter_filter _ _ _
  have h2 : {z ∈ {z ∈ t | m < z} | y < z} = {z ∈ t | y < z} := by
    rw [filter_filter]
    exact filter_congr fun z _ => ⟨And.right, fun hyz => ⟨hmy.trans hyz, hyz⟩⟩
  rw [h1, h2]

/-- Annihilation branch of the stack-pop induction: pushing `w (s.min' hs)` onto `a :: v` and
evolving over `{z ∈ s | s.min' hs < z}` produces the sum over `x > s.min' hs` with `{z ∈ s | z < x}`
reassembled via `inner_vacuum_prodGenOp_of_ih`. -/
private theorem inner_wordVector_min'_cons_prodGenOp {s : Finset α} (hs : s.Nonempty)
    (u w : α → H) (a : H) (v : List H)
    (ih : ∀ (r : Finset α), r ⊂ s → ∀ (b : H) (l : List H),
      ⟪wordVector 𝕜 (b :: l), prodGenOp (𝕜 := 𝕜) u w r vacuum⟫_𝕜 =
        ∑ x ∈ r, ⟪b, u x⟫_𝕜 *
          ⟪vacuum, prodGenOp (𝕜 := 𝕜) u w {z ∈ r | z < x} vacuum⟫_𝕜 *
          ⟪wordVector 𝕜 l, prodGenOp (𝕜 := 𝕜) u w {z ∈ r | x < z} vacuum⟫_𝕜) :
    ⟪wordVector 𝕜 (w (s.min' hs) :: a :: v),
        prodGenOp (𝕜 := 𝕜) u w {z ∈ s | s.min' hs < z} vacuum⟫_𝕜 =
      ∑ x ∈ s with s.min' hs < x, ⟪a, u x⟫_𝕜 *
        ⟪vacuum, prodGenOp (𝕜 := 𝕜) u w {z ∈ s | z < x} vacuum⟫_𝕜 *
        ⟪wordVector 𝕜 v, prodGenOp (𝕜 := 𝕜) u w {z ∈ s | x < z} vacuum⟫_𝕜 := by
  set m := s.min' hs
  set t := {z ∈ s | m < z} with ht_def
  have hts : t ⊂ s := filter_ssubset.2 ⟨m, s.min'_mem hs, lt_irrefl m⟩
  rw [ih t hts (w m) (a :: v)]
  have hexpand (y : α) (hy : y ∈ t) :
      ⟪w m, u y⟫_𝕜 * ⟪vacuum, prodGenOp (𝕜 := 𝕜) u w {z ∈ t | z < y} vacuum⟫_𝕜 *
          ⟪wordVector 𝕜 (a :: v), prodGenOp (𝕜 := 𝕜) u w {z ∈ t | y < z} vacuum⟫_𝕜 =
        ∑ x ∈ t with y < x, ⟪a, u x⟫_𝕜 *
          (⟪w m, u y⟫_𝕜 * ⟪vacuum, prodGenOp (𝕜 := 𝕜) u w {z ∈ t | z < y} vacuum⟫_𝕜 *
            ⟪vacuum, prodGenOp (𝕜 := 𝕜) u w {z ∈ {z ∈ t | y < z} | z < x} vacuum⟫_𝕜) *
          ⟪wordVector 𝕜 v, prodGenOp (𝕜 := 𝕜) u w {z ∈ s | x < z} vacuum⟫_𝕜 := by
    rw [ih _ ((filter_ssubset.2 ⟨y, hy, lt_irrefl y⟩).trans hts) a v, mul_sum]
    refine sum_congr rfl fun x hx => ?_
    have hmx : m < x := (mem_filter.1 (mem_filter.1 hx).1).2
    have hgt : {z ∈ {z ∈ t | y < z} | x < z} = {z ∈ s | x < z} := by
      ext z; simp only [mem_filter, ht_def]
      exact ⟨fun ⟨⟨⟨hzs, _⟩, _⟩, hxz⟩ => ⟨hzs, hxz⟩,
        fun ⟨hzs, hxz⟩ => ⟨⟨⟨hzs, hmx.trans hxz⟩, (mem_filter.1 hx).2.trans hxz⟩, hxz⟩⟩
    rw [hgt]; ring
  rw [sum_congr rfl hexpand]
  simp_rw [sum_filter (p := fun x => _ < x)]
  rw [sum_comm]
  simp_rw [← sum_filter (p := fun y => y < _)]
  refine sum_congr rfl fun x hx => ?_
  obtain ⟨hxs, hmx⟩ := mem_filter.1 hx
  set ux := {z ∈ s | z < x}
  have hux_ne : ux.Nonempty := ⟨m, mem_filter.2 ⟨s.min'_mem hs, hmx⟩⟩
  have hmin_ux : ux.min' hux_ne = m := le_antisymm
    (min'_le _ _ (mem_filter.2 ⟨s.min'_mem hs, hmx⟩))
    (le_min' _ _ _ fun z hz => s.min'_le z (mem_filter.1 hz).1)
  have hux_ss : {z ∈ ux | ux.min' hux_ne < z} ⊂ s :=
    lt_of_le_of_lt (filter_subset _ ux) (filter_ssubset.2 ⟨x, hxs, lt_irrefl x⟩)
  rw [← sum_mul, ← mul_sum, inner_vacuum_prodGenOp_of_ih u w hux_ne (ih _ hux_ss)]
  congr 2
  have hflt : {y ∈ t | y < x} = {y ∈ ux | ux.min' hux_ne < y} := by
    ext y
    simp only [mem_filter, ux, ht_def, hmin_ux]
    tauto
  rw [hflt]
  refine sum_congr rfl fun y hy => ?_
  have hyx : y < x := (mem_filter.1 (mem_filter.1 hy).1).2
  have hmy : m < y := hmin_ux ▸ (mem_filter.1 hy).2
  have h1 : {z ∈ t | z < y} = {z ∈ ux | ux.min' hux_ne < z ∧ z < y} := by
    ext z; simp only [mem_filter, ux, ht_def, hmin_ux]
    exact ⟨fun ⟨⟨hzs, hmz⟩, hzy⟩ => ⟨⟨hzs, hzy.trans hyx⟩, hmz, hzy⟩,
      fun ⟨⟨hzs, _⟩, hmz, hzy⟩ => ⟨⟨hzs, hmz⟩, hzy⟩⟩
  have h2 : {z ∈ {z ∈ t | y < z} | z < x} = {z ∈ ux | y < z} := by
    ext z; simp only [mem_filter, ux, ht_def]
    exact ⟨fun ⟨⟨⟨hzs, _⟩, hyz⟩, hzx⟩ => ⟨⟨hzs, hzx⟩, hyz⟩,
      fun ⟨⟨hzs, hzx⟩, hyz⟩ => ⟨⟨⟨hzs, hmy.trans hyz⟩, hyz⟩, hzx⟩⟩
  rw [h1, h2, hmin_ux]

/-- Stack-pop factorization for `prodGenOp`: pairing `wordVector 𝕜 (a :: v)` against
`prodGenOp u w s vacuum` sums over the position `x ∈ s` whose creation part `u x` contracts with
`a`, leaving the vacuum expectation before `x` and the remaining stack `v` after `x`. -/
private theorem inner_wordVector_cons_prodGenOp (s : Finset α) (u w : α → H) (a : H) (v : List H) :
    ⟪wordVector 𝕜 (a :: v), prodGenOp (𝕜 := 𝕜) u w s vacuum⟫_𝕜 =
      ∑ x ∈ s, ⟪a, u x⟫_𝕜 *
        ⟪vacuum, prodGenOp (𝕜 := 𝕜) u w {z ∈ s | z < x} vacuum⟫_𝕜 *
        ⟪wordVector 𝕜 v, prodGenOp (𝕜 := 𝕜) u w {z ∈ s | x < z} vacuum⟫_𝕜 := by
  induction hn : #s using Nat.strong_induction_on generalizing s a v with
  | _ n ih =>
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp [prodGenOp_empty]
  set m := s.min' hs
  set t := {z ∈ s | m < z} with ht_def
  rw [prodGenOp_nonempty hs, mul_apply_eq_comp, add_apply,
    inner_add_right, wordVector_cons, inner_creation_creation, inner_annihilation_right,
    ← wordVector_cons, ← wordVector_cons]
  have hm_term : ⟪a, u m⟫_𝕜 * ⟪wordVector 𝕜 v, prodGenOp (𝕜 := 𝕜) u w t vacuum⟫_𝕜 =
      ⟪a, u m⟫_𝕜 * ⟪vacuum, prodGenOp (𝕜 := 𝕜) u w {z ∈ s | z < m} vacuum⟫_𝕜 *
        ⟪wordVector 𝕜 v, prodGenOp (𝕜 := 𝕜) u w {z ∈ s | m < z} vacuum⟫_𝕜 := by
    have hlt_m : {z ∈ s | z < m} = ∅ :=
      filter_eq_empty_iff.2 fun z hz => not_lt.2 (s.min'_le z hz)
    simp [hlt_m, prodGenOp_empty, ht_def]
  have hins : insert m t = s := by
    rw [ht_def, filter_min'_lt_eq_erase hs, insert_erase (s.min'_mem hs)]
  have hmt_not : m ∉ t := fun h => (mem_filter.1 h).2.false
  have hsum := sum_insert
    (f := fun x => ⟪a, u x⟫_𝕜 * ⟪vacuum, prodGenOp (𝕜 := 𝕜) u w {z ∈ s | z < x} vacuum⟫_𝕜 *
      ⟪wordVector 𝕜 v, prodGenOp (𝕜 := 𝕜) u w {z ∈ s | x < z} vacuum⟫_𝕜) hmt_not
  rw [hins] at hsum
  rw [hm_term, inner_wordVector_min'_cons_prodGenOp hs u w a v
    (fun r hr b l => ih #r (hn ▸ card_lt_card hr) r b l rfl), hsum]

/-- **Free Wick formula for `creation + annihilation` operators.** The vacuum expectation of the
ordered product of `creation 𝕜 (u i) + annihilation 𝕜 (w i)` along `s` is the sum over noncrossing
pairings of `s`, with each arc `(a, b)` (`a < b`) weighted by `⟪w a, u b⟫_𝕜`. -/
theorem vacuumState_prod_creation_add_annihilation (s : Finset α) (u w : α → H) :
    vacuumState 𝕜 H ((s.sort.map fun i => creation 𝕜 (u i) + annihilation 𝕜 (w i)).prod) =
      ∑ P : {P : NoncrossingPartition s // P.1.IsPairing},
        ∏ B ∈ P.1.1.parts, NoncrossingPartition.pairWeight (fun i j => ⟪w i, u j⟫_𝕜) B := by
  rw [vacuumState_apply, ← prodGenOp]
  induction hn : #s using Nat.strong_induction_on generalizing s with
  | _ n ih =>
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp [prodGenOp_empty]
  rw [inner_vacuum_prodGenOp_of_ih u w hs
      (fun a v => inner_wordVector_cons_prodGenOp _ u w a v),
    NoncrossingPartition.sum_isPairing_prod_pairWeight_eq_sum hs]
  refine sum_congr rfl fun y hy => ?_
  obtain ⟨hys, _⟩ := mem_filter.1 hy
  have hlt1 : #{z ∈ s | s.min' hs < z ∧ z < y} < n :=
    hn ▸ card_lt_card (filter_ssubset.2 ⟨y, hys, fun h => h.2.false⟩)
  have hlt2 : #{z ∈ s | y < z} < n :=
    hn ▸ card_lt_card (filter_ssubset.2 ⟨y, hys, lt_irrefl y⟩)
  rw [ih _ hlt1 _ rfl, ih _ hlt2 _ rfl]

/-- **Joint free cumulants of `creation + annihilation` operators.** Only the second free cumulants
survive, with `κ₂(ℓ(u₁) + ℓ(w₁)*, ℓ(u₂) + ℓ(w₂)*) = ⟪w₁, u₂⟫_𝕜`. -/
theorem freeCumulant_vacuumState_creation_add_annihilation {s : Finset α} (hs : s.Nonempty)
    (u w : α → H) :
    freeCumulant (vacuumState 𝕜 H).toLinearMap
        (fun i => creation 𝕜 (u i) + annihilation 𝕜 (w i)) s =
      NoncrossingPartition.pairWeight (fun i j => ⟪w i, u j⟫_𝕜) s :=
  freeCumulant_eq_of_forall_apply_prod_eq_sum_prod _ _ _
    (fun X _ _ => (vacuumState_prod_creation_add_annihilation X u w).trans
      (NoncrossingPartition.sum_prod_pairWeight_eq_sum_isPairing X _).symm) hs

/-- **Free Wick formula for field operators** along a finite ordered set `s`. -/
theorem vacuumState_prod_field (s : Finset α) (h : α → H) :
    vacuumState 𝕜 H ((s.sort.map fun i => field 𝕜 (h i)).prod) =
      ∑ P : {P : NoncrossingPartition s // P.1.IsPairing},
        ∏ B ∈ P.1.1.parts, NoncrossingPartition.pairWeight (fun i j => ⟪h i, h j⟫_𝕜) B := by
  simp_rw [field_def]
  exact vacuumState_prod_creation_add_annihilation s h h

/-- **Free Wick formula for field operators** indexed by `Fin n`. -/
theorem vacuumState_prod_ofFn_field {n : ℕ} (h : Fin n → H) :
    vacuumState 𝕜 H (List.ofFn fun i => field 𝕜 (h i)).prod =
      ∑ P : {P : NoncrossingPartition (univ : Finset (Fin n)) // P.1.IsPairing},
        ∏ B ∈ P.1.1.parts, NoncrossingPartition.pairWeight (fun i j => ⟪h i, h j⟫_𝕜) B := by
  rw [← vacuumState_prod_field, Fin.sort_univ, List.ofFn_eq_map]

/-- **Free Wick formula in planar-matching form**: the vacuum expectation of a product of `n`
field operators is the sum over `PlanarMatching n` of the inner products along the arcs. -/
theorem vacuumState_prod_ofFn_field_eq_sum_planarMatching {n : ℕ} (h : Fin n → H) :
    vacuumState 𝕜 H (List.ofFn fun i => field 𝕜 (h i)).prod =
      ∑ D : PlanarMatching n, ∏ a ∈ univ with a < D.1.val a, ⟪h a, h (D.1.val a)⟫_𝕜 := by
  rw [vacuumState_prod_ofFn_field,
    ← PerfectMatching.sum_isNoncrossingMatching_prod_eq_sum_isPairing]

/-- **Joint free cumulants of field operators** on full Fock space. -/
theorem freeCumulant_vacuumState_field {s : Finset α} (hs : s.Nonempty) (h : α → H) :
    freeCumulant (vacuumState 𝕜 H).toLinearMap (fun i => field 𝕜 (h i)) s =
      NoncrossingPartition.pairWeight (fun i j => ⟪h i, h j⟫_𝕜) s := by
  simp_rw [field_def]
  exact freeCumulant_vacuumState_creation_add_annihilation hs h h

end Wick

/-! ### Semicircular systems and `⋆`-freeness on full Fock space -/

section SemicircularAndStarFree

variable {𝕜 : Type u} {H : Type v} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  {ι : Type*}

/-- **Fock realization of semicircular systems.** For any family of vectors `h : ι → H`, the field
operators `i ↦ field 𝕜 (h i)` form a semicircular system for `vacuumState 𝕜 H` with covariance
`Matrix.gram 𝕜 h`. -/
theorem isSemicircularSystem_vacuumState_field (h : ι → H) :
    IsSemicircularSystem (vacuumState 𝕜 H).toLinearMap (fun i => field 𝕜 (h i))
      (Matrix.gram 𝕜 h) where
  apply_one := vacuumState_one
  freeCumulant_two w := by
    have huniv : (univ : Finset (Fin 2)) = {0, 1} := by decide
    have h01 : (0 : Fin 2) < 1 := by decide
    rw [Function.comp_def, freeCumulant_vacuumState_field univ_nonempty, huniv,
      NoncrossingPartition.pairWeight_pair _ h01, Matrix.gram_apply]
  freeCumulant_eq_zero {n} hn₀ hn₂ w := by
    have : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn₀⟩⟩
    rw [Function.comp_def, freeCumulant_vacuumState_field univ_nonempty,
      NoncrossingPartition.pairWeight_eq_zero_of_card_ne_two]
    simpa using hn₂

/-- Every field operator `field 𝕜 h` is semicircular of variance `(‖h‖ ^ 2 : 𝕜)` for
`vacuumState 𝕜 H`. -/
theorem isSemicircular_vacuumState_field (h : H) :
    IsSemicircular (vacuumState 𝕜 H).toLinearMap (field 𝕜 h) (‖h‖ ^ 2 : 𝕜) := by
  simpa [Matrix.gram_apply, inner_self_eq_norm_sq_to_K] using
    (isSemicircularSystem_vacuumState_field fun _ : Unit => h).isSemicircular ()

/-- Field operators `(field 𝕜 (h i))` are freely independent under `vacuumState 𝕜 H` if and only
if the vectors `(h i)` are pairwise orthogonal. -/
theorem isFreelyIndependentElements_vacuumState_field_iff (h : ι → H) :
    IsFreelyIndependentElements (vacuumState 𝕜 H).toLinearMap (fun i => field 𝕜 (h i)) ↔
      Pairwise fun i j => ⟪h i, h j⟫_𝕜 = 0 :=
  (isSemicircularSystem_vacuumState_field h).isFreelyIndependentElements_iff

private theorem exists_creation_add_annihilation_of_mem_union {S : Set H}
    {a : FullFockSpace 𝕜 H →L[𝕜] FullFockSpace 𝕜 H}
    (ha : a ∈ creation 𝕜 '' S ∪ star (creation 𝕜 '' S)) :
    ∃ u w : H, (u ∈ S ∨ u = 0) ∧ (w ∈ S ∨ w = 0) ∧ a = creation 𝕜 u + annihilation 𝕜 w := by
  rcases ha with ⟨x, hx, rfl⟩ | ha
  · exact ⟨x, 0, Or.inl hx, Or.inr rfl, by simp⟩
  · obtain ⟨x, hx, hstar⟩ := Set.mem_star.1 ha
    refine ⟨0, x, Or.inr rfl, Or.inl hx, ?_⟩
    simpa using congrArg star hstar.symm

/-- **`⋆`-freeness of creation/annihilation algebras is pairwise orthogonality.** For a family of
subsets `S : ι → Set H`, the unital `⋆`-subalgebras `StarAlgebra.adjoin 𝕜 (creation 𝕜 '' S i)` are
freely independent under `vacuumState 𝕜 H` if and only if the sets `S i` are pairwise orthogonal. -/
theorem isFreelyIndependent_vacuumState_starAlgebraAdjoin_creation_iff (S : ι → Set H) :
    IsFreelyIndependent (vacuumState 𝕜 H).toLinearMap
        (fun i => (StarAlgebra.adjoin 𝕜 (creation 𝕜 '' S i)).toSubalgebra) ↔
      Pairwise fun i j => ∀ x ∈ S i, ∀ y ∈ S j, ⟪x, y⟫_𝕜 = 0 := by
  refine ⟨fun hfree i j hij x hx y hy => ?_, fun horth => ?_⟩
  · -- Test freeness on the two-letter alternating word `[ℓ(x)*, ℓ(y)]`.
    have hx_mem : annihilation 𝕜 x ∈ StarAlgebra.adjoin 𝕜 (creation 𝕜 '' S i) := by
      rw [← star_creation]
      exact star_mem (StarAlgebra.subset_adjoin 𝕜 _ ⟨x, hx, rfl⟩)
    have hy_mem : creation 𝕜 y ∈ StarAlgebra.adjoin 𝕜 (creation 𝕜 '' S j) :=
      StarAlgebra.subset_adjoin 𝕜 _ ⟨y, hy, rfl⟩
    have hword := isFreelyIndependent_iff.1 hfree
      [(i, annihilation 𝕜 x), (j, creation 𝕜 y)] (by simp) (by simp [hij])
      (by simp [hx_mem, hy_mem]) (by simp)
    simpa using hword
  · -- Apply the generated-algebra free-cumulant test to `creation` and `annihilation`.
    simp_rw [StarAlgebra.adjoin_toSubalgebra]
    refine isFreelyIndependent_adjoin_of_freeCumulant_eq_zero vacuumState_one
      fun n a ℓ ha k k' hkk' => ?_
    have : Nonempty (Fin n) := ⟨k⟩
    choose u w hu hw ha_eq using fun q => exists_creation_add_annihilation_of_mem_union (ha q)
    rw [funext ha_eq, freeCumulant_vacuumState_creation_add_annihilation univ_nonempty]
    rcases eq_or_ne n 2 with rfl | hn₂
    · have huniv : (univ : Finset (Fin 2)) = {0, 1} := by decide
      have h01 : (0 : Fin 2) < 1 := by decide
      have hℓ01 : ℓ 0 ≠ ℓ 1 := fun h =>
        hkk' (by fin_cases k <;> fin_cases k' <;> simp [h])
      rw [huniv, NoncrossingPartition.pairWeight_pair _ h01]
      rcases hw 0 with hw0 | hw0 <;> rcases hu 1 with hu1 | hu1
      · exact horth hℓ01 (w 0) hw0 (u 1) hu1
      · simp [hu1]
      · simp [hw0]
      · simp [hw0]
    · exact NoncrossingPartition.pairWeight_eq_zero_of_card_ne_two _ (by simpa using hn₂)

/-- A family of creation operators `i ↦ creation 𝕜 (h i)` is `⋆`-freely independent under
`vacuumState 𝕜 H` if and only if the vectors `h i` are pairwise orthogonal. -/
theorem isStarFreelyIndependentElements_vacuumState_creation_iff (h : ι → H) :
    IsStarFreelyIndependentElements (vacuumState 𝕜 H).toLinearMap (fun i => creation 𝕜 (h i)) ↔
      Pairwise fun i j => ⟪h i, h j⟫_𝕜 = 0 := by
  simpa [isStarFreelyIndependentElements_iff] using
    isFreelyIndependent_vacuumState_starAlgebraAdjoin_creation_iff fun i => {h i}

/-- The unital subalgebras `Algebra.adjoin 𝕜 (field 𝕜 '' S i)` generated by field operators on
subsets `S i` are freely independent under `vacuumState 𝕜 H` if and only if the sets `S i` are
pairwise orthogonal. -/
theorem isFreelyIndependent_vacuumState_adjoin_field_iff (S : ι → Set H) :
    IsFreelyIndependent (vacuumState 𝕜 H).toLinearMap
        (fun i => Algebra.adjoin 𝕜 (field 𝕜 '' S i)) ↔
      Pairwise fun i j => ∀ x ∈ S i, ∀ y ∈ S j, ⟪x, y⟫_𝕜 = 0 := by
  refine ⟨fun hfree i j hij x hx y hy => ?_, fun horth => ?_⟩
  · have hx_mem : field 𝕜 x ∈ Algebra.adjoin 𝕜 (field 𝕜 '' S i) :=
      Algebra.subset_adjoin ⟨x, hx, rfl⟩
    have hy_mem : field 𝕜 y ∈ Algebra.adjoin 𝕜 (field 𝕜 '' S j) :=
      Algebra.subset_adjoin ⟨y, hy, rfl⟩
    have hword := isFreelyIndependent_iff.1 hfree
      [(i, field 𝕜 x), (j, field 𝕜 y)] (by simp) (by simp [hij])
      (by simp [hx_mem, hy_mem]) (by simp)
    simpa using hword
  · refine ((isFreelyIndependent_vacuumState_starAlgebraAdjoin_creation_iff S).2 horth).mono
      fun i => ?_
    refine Algebra.adjoin_le ?_
    rintro _ ⟨x, hx, rfl⟩
    have hc : creation 𝕜 x ∈ StarAlgebra.adjoin 𝕜 (creation 𝕜 '' S i) :=
      StarAlgebra.subset_adjoin 𝕜 _ ⟨x, hx, rfl⟩
    rw [field_def]
    exact StarSubalgebra.mem_toSubalgebra.2 (add_mem hc (star_creation (𝕜 := 𝕜) x ▸ star_mem hc))

/-- Norm-closed C⋆-subalgebras generated by creation operators on subsets `S i` are freely
independent under `vacuumState 𝕜 H` if and only if the sets `S i` are pairwise orthogonal. -/
theorem isFreelyIndependent_vacuumState_topologicalClosure_starAlgebraAdjoin_creation_iff
    (S : ι → Set H) :
    IsFreelyIndependent (vacuumState 𝕜 H).toLinearMap
        (fun i => (StarAlgebra.adjoin 𝕜 (creation 𝕜 '' S i)).topologicalClosure.toSubalgebra) ↔
      Pairwise fun i j => ∀ x ∈ S i, ∀ y ∈ S j, ⟪x, y⟫_𝕜 = 0 := by
  simp_rw [StarSubalgebra.topologicalClosure_toSubalgebra_comm]
  rw [isFreelyIndependent_topologicalClosure_iff vacuumState_one continuous_vacuumState,
    isFreelyIndependent_vacuumState_starAlgebraAdjoin_creation_iff]

/-- Weak-operator closures of the unital `⋆`-subalgebras generated by creation operators on subsets
`S i` are freely independent under `vacuumState 𝕜 H` if and only if the sets `S i` are pairwise
orthogonal. -/
theorem isFreelyIndependent_vacuumState_weakOperatorClosure_starAlgebraAdjoin_creation_iff
    (S : ι → Set H) :
    IsFreelyIndependent
        ((vacuumState 𝕜 H).toLinearMap.comp (ContinuousLinearMapWOT.algEquiv 𝕜).toLinearMap)
        (fun i => (((StarAlgebra.adjoin 𝕜 (creation 𝕜 '' S i)).toSubalgebra).map
          (ContinuousLinearMapWOT.algEquiv 𝕜).symm.toAlgHom).topologicalClosure) ↔
      Pairwise fun i j => ∀ x ∈ S i, ∀ y ∈ S j, ⟪x, y⟫_𝕜 = 0 :=
  (isFreelyIndependent_weakOperatorClosure_iff_of_vectorState vacuumState_one vacuum
    vacuumState_apply).trans (isFreelyIndependent_vacuumState_starAlgebraAdjoin_creation_iff S)

end SemicircularAndStarFree

/-! ### Complex C⋆-laws of Fock field operators -/

section ComplexLaw

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- **Semicircle law of a Fock field operator.** Under the vacuum state `vacuumState ℂ H`, the
self-adjoint operator `field ℂ h` has law `semicircleReal 0 (‖h‖₊ ^ 2)`. -/
theorem law_vacuumState_field (h : H) :
    PositiveLinearMap.law (vacuumState ℂ H) (field ℂ h) = semicircleReal 0 (‖h‖₊ ^ 2) := by
  rw [PositiveLinearMap.law_eq_semicircleReal_iff (vacuumState ℂ H) (isSelfAdjoint_field h)]
  simpa using isSemicircular_vacuumState_field (𝕜 := ℂ) h

/-- Shifting `field ℂ h` by a real scalar `m` gives law `semicircleReal m (‖h‖₊ ^ 2)`. -/
theorem law_vacuumState_field_add_algebraMap (h : H) (m : ℝ) :
    PositiveLinearMap.law (vacuumState ℂ H)
        (field ℂ h + algebraMap ℝ (FullFockSpace ℂ H →L[ℂ] FullFockSpace ℂ H) m) =
      semicircleReal m (‖h‖₊ ^ 2) := by
  have : IsScalarTower ℝ ℂ (FullFockSpace ℂ H) := Real.isScalarTower
  have halg :
      algebraMap ℝ (FullFockSpace ℂ H →L[ℂ] FullFockSpace ℂ H) m =
        algebraMap ℂ (FullFockSpace ℂ H →L[ℂ] FullFockSpace ℂ H) (m : ℂ) := by
    ext x : 1
    simp only [Algebra.algebraMap_eq_smul_one, smul_apply, one_apply_eq_self]
    exact (algebraMap_smul ℂ m x).symm
  rw [halg]
  simpa using PositiveLinearMap.law_add_algebraMap_ofReal_of_law_eq_semicircleReal
    (vacuumState ℂ H) (law_vacuumState_field h) m

/-- Affine rescaling and shifting of a Fock field operator realizes `semicircleReal` with arbitrary
centre and rescaled variance. -/
theorem law_vacuumState_smul_field_add_algebraMap (h : H) (r m : ℝ) :
    PositiveLinearMap.law (vacuumState ℂ H)
        (r • field ℂ h +
          algebraMap ℝ (FullFockSpace ℂ H →L[ℂ] FullFockSpace ℂ H) m) =
      semicircleReal m (Real.toNNReal (r ^ 2) * ‖h‖₊ ^ 2) := by
  have : IsScalarTower ℝ ℂ H := Real.isScalarTower
  have hnorm : ‖r • h‖₊ ^ 2 = Real.toNNReal (r ^ 2) * ‖h‖₊ ^ 2 := by
    ext
    simp [nnNorm_smul, mul_pow, Real.coe_toNNReal _ (sq_nonneg r)]
  rw [← field_complex_real_smul, law_vacuumState_field_add_algebraMap, hnorm]

/-- Every semicircle law `semicircleReal m v` on `ℝ` is realized by the canonical shifted field
operator `field ℂ (√v : ℂ) + m` on the full Fock space `FullFockSpace ℂ ℂ` over the one-dimensional
one-particle space `ℂ`. -/
theorem law_vacuumState_field_ofReal_sqrt_add_algebraMap (m : ℝ) (v : ℝ≥0) :
    PositiveLinearMap.law (vacuumState ℂ ℂ)
        (field ℂ ((√(v : ℝ) : ℝ) : ℂ) +
          algebraMap ℝ (FullFockSpace ℂ ℂ →L[ℂ] FullFockSpace ℂ ℂ) m) =
      semicircleReal m v := by
  rw [law_vacuumState_field_add_algebraMap (H := ℂ)]
  congr 1
  ext
  simp

end ComplexLaw

/-! ### Real inner product spaces via complexification -/

section RealComplexification

variable {X : Type v} [NormedAddCommGroup X] [InnerProductSpace ℝ X] {ι : Type*}

/-- For any family `x : ι → X` in a real inner product space, `i ↦ realField (x i)` is a
self-adjoint semicircular system in the complex C⋆-algebra
`FullFockSpace ℂ (WithLp 2 (Complexification X)) →L[ℂ] _` with real Gram covariance
`(Matrix.gram ℝ x).map ((↑) : ℝ → ℂ)`. -/
theorem isSemicircularSystem_vacuumState_realField (x : ι → X) :
    IsSemicircularSystem (vacuumState ℂ (WithLp 2 (Complexification X))).toLinearMap
      (fun i => realField (x i)) ((Matrix.gram ℝ x).map ((↑) : ℝ → ℂ)) := by
  have hgram : Matrix.gram ℂ (fun i => WithLp.complexificationOfRealₗᵢ X (x i)) =
      (Matrix.gram ℝ x).map ((↑) : ℝ → ℂ) := by
    ext i j
    simp [Matrix.gram_apply]
  simp_rw [realField_def, ← hgram]
  exact isSemicircularSystem_vacuumState_field (𝕜 := ℂ) _

/-- Every `realField x` is semicircular of variance `(‖x‖ ^ 2 : ℂ)` under the vacuum state. -/
theorem isSemicircular_vacuumState_realField (x : X) :
    IsSemicircular (vacuumState ℂ (WithLp 2 (Complexification X))).toLinearMap
      (realField x) ((‖x‖ ^ 2 : ℝ) : ℂ) := by
  simpa [realField_def] using
    isSemicircular_vacuumState_field (𝕜 := ℂ) (WithLp.complexificationOfRealₗᵢ X x)

/-- Under the vacuum state, `realField x` has law `semicircleReal 0 (‖x‖₊ ^ 2)`. -/
theorem law_vacuumState_realField (x : X) :
    PositiveLinearMap.law (vacuumState ℂ (WithLp 2 (Complexification X))) (realField x) =
      semicircleReal 0 (‖x‖₊ ^ 2) := by
  rw [realField_def, law_vacuumState_field, LinearIsometry.nnNorm_map]

/-- Shifting `realField x` by a real scalar `m` gives law `semicircleReal m (‖x‖₊ ^ 2)`. -/
theorem law_vacuumState_realField_add_algebraMap (x : X) (m : ℝ) :
    PositiveLinearMap.law (vacuumState ℂ (WithLp 2 (Complexification X)))
        (realField x + algebraMap ℝ
          (FullFockSpace ℂ (WithLp 2 (Complexification X)) →L[ℂ]
            FullFockSpace ℂ (WithLp 2 (Complexification X))) m) =
      semicircleReal m (‖x‖₊ ^ 2) := by
  rw [realField_def, law_vacuumState_field_add_algebraMap, LinearIsometry.nnNorm_map]

/-- Affine rescaling and shifting of `realField x` realizes `semicircleReal` with centre `m` and
variance `Real.toNNReal (r ^ 2) * ‖x‖₊ ^ 2`. -/
theorem law_vacuumState_smul_realField_add_algebraMap (x : X) (r m : ℝ) :
    PositiveLinearMap.law (vacuumState ℂ (WithLp 2 (Complexification X)))
        (r • realField x + algebraMap ℝ
          (FullFockSpace ℂ (WithLp 2 (Complexification X)) →L[ℂ]
            FullFockSpace ℂ (WithLp 2 (Complexification X))) m) =
      semicircleReal m (Real.toNNReal (r ^ 2) * ‖x‖₊ ^ 2) := by
  rw [realField_def, law_vacuumState_smul_field_add_algebraMap, LinearIsometry.nnNorm_map]

/-- Real-vector field operators `(realField (x i))` are freely independent if and only if `(x i)`
is pairwise orthogonal in `X`. -/
theorem isFreelyIndependentElements_vacuumState_realField_iff (x : ι → X) :
    IsFreelyIndependentElements (vacuumState ℂ (WithLp 2 (Complexification X))).toLinearMap
        (fun i => realField (x i)) ↔
      Pairwise fun i j => ⟪x i, x j⟫_ℝ = 0 := by
  simp_rw [realField_def]
  rw [isFreelyIndependentElements_vacuumState_field_iff (𝕜 := ℂ)]
  simp [Complex.ofReal_eq_zero]

/-- For real subspaces `S : ι → Submodule ℝ X`, the unital `⋆`-subalgebras generated by creation
operators on their complexifications `(S i).complexifyL2` are freely independent under the vacuum
state if and only if the subspaces `S i` are pairwise orthogonal (`S i ≤ (S j)ᗮ`). -/
theorem isFreelyIndependent_vacuumState_starAlgebraAdjoin_creation_complexifyL2_iff
    (S : ι → Submodule ℝ X) :
    IsFreelyIndependent (vacuumState ℂ (WithLp 2 (Complexification X))).toLinearMap
        (fun i => (StarAlgebra.adjoin ℂ
          (creation ℂ ''
            ((S i).complexifyL2 : Set (WithLp 2 (Complexification X))))).toSubalgebra) ↔
      Pairwise fun i j => S i ≤ (S j)ᗮ := by
  have horth (i j : ι) :
      (∀ z ∈ ((S i).complexifyL2 : Set (WithLp 2 (Complexification X))),
          ∀ w ∈ ((S j).complexifyL2 : Set (WithLp 2 (Complexification X))), ⟪z, w⟫_ℂ = 0) ↔
        S i ≤ (S j)ᗮ :=
    ((S i).complexifyL2.isOrtho_iff_inner_eq (V := (S j).complexifyL2)).symm.trans
      (Submodule.isOrtho_complexifyL2_iff.trans Submodule.isOrtho_iff_le)
  rw [isFreelyIndependent_vacuumState_starAlgebraAdjoin_creation_iff]
  simp_rw [horth]

/-- For real subspaces `S : ι → Submodule ℝ X`, the unital subalgebras generated by `realField` on
`S i` are freely independent under the vacuum state if and only if the subspaces `S i` are pairwise
orthogonal (`S i ≤ (S j)ᗮ`). -/
theorem isFreelyIndependent_vacuumState_adjoin_realField_iff (S : ι → Submodule ℝ X) :
    IsFreelyIndependent (vacuumState ℂ (WithLp 2 (Complexification X))).toLinearMap
        (fun i => Algebra.adjoin ℂ (realField '' (S i : Set X))) ↔
      Pairwise fun i j => S i ≤ (S j)ᗮ := by
  have himage (i : ι) :
      realField '' (S i : Set X) =
        field ℂ '' (WithLp.complexificationOfRealₗᵢ X '' (S i : Set X)) := by
    rw [← Set.image_comp, Function.comp_def]
    simp_rw [← realField_def]
  have horth (i j : ι) :
      (∀ z ∈ WithLp.complexificationOfRealₗᵢ X '' (S i : Set X),
          ∀ w ∈ WithLp.complexificationOfRealₗᵢ X '' (S j : Set X), ⟪z, w⟫_ℂ = 0) ↔
        S i ≤ (S j)ᗮ := by
    simp only [Set.forall_mem_image, WithLp.complexificationOfRealₗᵢ_apply,
      WithLp.complexification_inner_toLp_ofReal, Complex.ofReal_eq_zero]
    exact ((S i).isOrtho_iff_inner_eq (V := S j)).symm.trans Submodule.isOrtho_iff_le
  simp_rw [himage, isFreelyIndependent_vacuumState_adjoin_field_iff, horth]

end RealComplexification

end FullFockSpace

end TauCeti

/-! ### Canonical 1D Fock semicircle law equivalence -/

namespace PositiveLinearMap

open TauCeti TauCeti.FullFockSpace

/-- An element `a` of a C⋆-algebra has law `semicircleReal m v` if and only if it has the same law
as the canonical shifted Fock field operator `field ℂ (√v : ℂ) + m` on `FullFockSpace ℂ ℂ`. -/
theorem law_eq_semicircleReal_iff_law_eq_law_vacuumState_field_ofReal_sqrt_add_algebraMap
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] (φ : A →ₚ[ℂ] ℂ) {a : A}
    (m : ℝ) (v : ℝ≥0) :
    law φ a = semicircleReal m v ↔
      law φ a =
        law (vacuumState ℂ ℂ)
          (field ℂ ((√(v : ℝ) : ℝ) : ℂ) +
            algebraMap ℝ (FullFockSpace ℂ ℂ →L[ℂ] FullFockSpace ℂ ℂ) m) := by
  rw [law_vacuumState_field_ofReal_sqrt_add_algebraMap]

end PositiveLinearMap

/-! ### Full Fock realization of positive-semidefinite covariance matrices -/

namespace Matrix

open TauCeti TauCeti.FullFockSpace

/-- Every positive-semidefinite matrix `C : Matrix ι ι 𝕜` of arbitrary index type `ι` over `𝕜`
(`ℝ` or `ℂ`) is the covariance of a Fock semicircular system of self-adjoint field operators over a
complete Hilbert space over `𝕜`. -/
theorem PosSemidef.exists_isSemicircularSystem_vacuumState_field {𝕜 : Type u} {ι : Type v}
    [RCLike 𝕜] {C : Matrix ι ι 𝕜} (hC : C.PosSemidef) :
    ∃ (H : Type (max u v)) (_ : NormedAddCommGroup H) (_ : InnerProductSpace 𝕜 H)
      (_ : CompleteSpace H) (h : ι → H),
      IsSemicircularSystem (vacuumState 𝕜 H).toLinearMap (fun i => field 𝕜 (h i)) C := by
  obtain ⟨H, _, _, _, h, rfl⟩ := hC.exists_gram_eq
  exact ⟨H, inferInstance, inferInstance, inferInstance, h,
    isSemicircularSystem_vacuumState_field h⟩

/-- Every real positive-semidefinite matrix `C : Matrix ι ι ℝ` of arbitrary index type `ι` is
realized via self-adjoint `realField` operators on the full Fock space over the complexification of
a complete real Hilbert space `X`, with covariance `C.map ((↑) : ℝ → ℂ)`. -/
theorem PosSemidef.exists_isSemicircularSystem_vacuumState_realField {ι : Type u}
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) :
    ∃ (X : Type u) (_ : NormedAddCommGroup X) (_ : InnerProductSpace ℝ X) (_ : CompleteSpace X)
      (x : ι → X),
      IsSemicircularSystem (vacuumState ℂ (WithLp 2 (Complexification X))).toLinearMap
        (fun i => realField (x i)) (C.map ((↑) : ℝ → ℂ)) := by
  obtain ⟨X, _, _, _, x, rfl⟩ := hC.exists_gram_eq
  exact ⟨X, inferInstance, inferInstance, inferInstance, x,
    isSemicircularSystem_vacuumState_realField x⟩

/-- Every finite-index real positive-semidefinite matrix `C : Matrix ι ι ℝ` is realized by
self-adjoint `realField` operators on the full Fock space over the complexification of
`EuclideanSpace ℝ ι`. -/
theorem PosSemidef.exists_euclideanSpace_isSemicircularSystem_vacuumState_realField {ι : Type u}
    [Fintype ι] {C : Matrix ι ι ℝ} (hC : C.PosSemidef) :
    ∃ x : ι → EuclideanSpace ℝ ι,
      IsSemicircularSystem
        (vacuumState ℂ (WithLp 2 (Complexification (EuclideanSpace ℝ ι)))).toLinearMap
        (fun i => realField (x i)) (C.map ((↑) : ℝ → ℂ)) := by
  obtain ⟨x, rfl⟩ := hC.exists_gram_euclideanSpace_eq
  exact ⟨x, isSemicircularSystem_vacuumState_realField x⟩

/-- **Characterization of complex semicircular covariance matrices.** A complex matrix
`C : Matrix ι ι ℂ` of arbitrary index type `ι` is positive semidefinite if and only if `C` is the
covariance of a self-adjoint semicircular system in a complex C⋆-probability space. -/
theorem posSemidef_iff_exists_cstar_isSelfAdjoint_and_isSemicircularSystem {ι : Type u}
    {C : Matrix ι ι ℂ} :
    C.PosSemidef ↔
      ∃ (A : Type u) (_ : CStarAlgebra A) (_ : PartialOrder A) (_ : StarOrderedRing A)
        (φ : A →ₚ[ℂ] ℂ) (s : ι → A),
        (∀ i, IsSelfAdjoint (s i)) ∧ IsSemicircularSystem φ.toLinearMap s C := by
  refine ⟨fun hC => ?_, fun ⟨A, _, _, _, φ, s, hs, hsys⟩ =>
    φ.posSemidef_of_forall_apply_mul_eq hs fun i j => hsys.apply_mul i j⟩
  obtain ⟨H, _, _, _, h, hsys⟩ := hC.exists_isSemicircularSystem_vacuumState_field
  exact ⟨FullFockSpace ℂ H →L[ℂ] FullFockSpace ℂ H,
    inferInstance, inferInstance, inferInstance,
    vacuumState ℂ H,
    fun i => field ℂ (h i),
    fun i => isSelfAdjoint_field (h i),
    hsys⟩

/-- **Characterization of real semicircular covariance matrices.** A real matrix `C : Matrix ι ι ℝ`
of arbitrary index type `ι` is positive semidefinite if and only if `C.map ((↑) : ℝ → ℂ)` is the
covariance of a self-adjoint semicircular system in a complex C⋆-probability space. -/
theorem posSemidef_real_iff_exists_cstar_isSelfAdjoint_and_isSemicircularSystem {ι : Type u}
    {C : Matrix ι ι ℝ} :
    C.PosSemidef ↔
      ∃ (A : Type u) (_ : CStarAlgebra A) (_ : PartialOrder A) (_ : StarOrderedRing A)
        (φ : A →ₚ[ℂ] ℂ) (s : ι → A),
        (∀ i, IsSelfAdjoint (s i)) ∧
          IsSemicircularSystem φ.toLinearMap s (C.map ((↑) : ℝ → ℂ)) := by
  rw [← posSemidef_map_complex_ofReal_iff,
    posSemidef_iff_exists_cstar_isSelfAdjoint_and_isSemicircularSystem]

end Matrix
