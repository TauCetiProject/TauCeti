/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Floor.Defs
public import TauCeti.Combinatorics.Hypergraph.Colored.EditDiscrepancy
public import TauCeti.Combinatorics.Hypergraph.PairColor.Regular
public import TauCeti.Combinatorics.Hypergraph.Triadic.Basic
public import TauCeti.Combinatorics.Hypergraph.Triadic.RegularityLemma
public import TauCeti.Combinatorics.Hypergraph.Triadic.TopRegularization
import Mathlib.Combinatorics.SimpleGraph.Regularity.Equitabilise
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import TauCeti.Combinatorics.Hypergraph.Triadic.Recoloring
import TauCeti.Data.Nat.Factorial.Basic

/-!
# Strong regular approximation of colored three-uniform hypergraphs

For any positive tolerance `ε`, positive regularity schedule `F`, rank schedule `R`, and
vertex-cell floor `t₀`, every coloring `H : Colored3Graph κ V` of the unordered triples of a
finite vertex set `V` with `regularityBound3 (Fintype.card κ) ε F R t₀ ≤ Fintype.card V` admits
a *strong regular approximation* `(H', C)`: a nearby coloring `H'` together with a triadic complex
`C` whose vertex cells form an equipartition into at least `t₀` cells and whose selected polyads
decompose the injective triples, such that

* `H` approximates `H'` within `ε` in edit discrepancy (`H.Approximates3 H' ε`),
* the lower skeleton of `C` is regular for the schedule `F` (`C.skeleton.LowerSkeletonRegular F`),
* `H'` is `(F C.complexity, R C.complexity)`-top-regular over all polyads of `C` outside an
  `ε`-proportion of the injective triples, and
* `C.ComplexityBounded (regularityBound3 (Fintype.card κ) ε F R t₀)`, a complexity bound
  independent of `|V|`.

## Main definitions

* `TauCeti.regularityBound3`: host-size and complexity bound for strong regular approximation of
  colored three-uniform hypergraphs.
* `TauCeti.Colored3Graph.IsStrongRegularApproximation3`: the bundled regularity, approximation,
  and complexity-bound predicate for `(H', C)`.

## Main results

* `TauCeti.regularityBound3_def`: unfolding equation for `regularityBound3`.
* `TauCeti.le_regularityBound3`, `TauCeti.four_le_regularityBound3`,
  `TauCeti.regularityBound3_pos`: unconditional floor and positivity bounds for `regularityBound3`.
* `TauCeti.Colored3Graph.exists_strong_regular_approximation3`: every colored three-uniform
  hypergraph on at least `regularityBound3 (Fintype.card κ) ε F R t₀` vertices admits a strong
  regular approximation with vertex cells controlled at `t₀`.

## References

* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007), Theorem 2.3 and the regular approximation lemma.
* T. Tao, *Szemerédi's regularity lemma revisited*, Contrib. Discrete Math. 1 (2006), the
  energy-gap stopping argument.
* N. Alon, E. Fischer, M. Krivelevich and M. Szegedy, *Efficient testing of large graphs*,
  Combinatorica 20 (2000), the strong regularity lemma and coupled edge modification.
-/

public section

open Finset Finpartition Real

namespace TauCeti

private noncomputable def triadicRank1Tol (F : ℕ → ℝ) (R : ℕ → ℕ) (k : ℕ) : ℝ :=
  F k ^ 2 / (2 : ℝ) ^ R k

private noncomputable def triadicFineTheta (F : ℕ → ℝ) (R : ℕ → ℕ) (k : ℕ) : ℝ :=
  triadicRank1Tol F R k ^ 2 / 4

private noncomputable def triadicFineTol (q₃ : ℕ) (F : ℕ → ℝ) (R : ℕ → ℕ) (k : ℕ) : ℝ :=
  triadicRank1Tol F R k ^ 2 / (8 * ((q₃ : ℝ) + 1))

private noncomputable def triadicFineBeta (q₃ : ℕ) (ε : ℝ) (F : ℕ → ℝ) (R : ℕ → ℕ) (k : ℕ) : ℝ :=
  min (ε / (2 * ((q₃ : ℝ) + 1))) (triadicFineTol q₃ F R k)

private noncomputable def triadicFineMass (ε : ℝ) (F : ℕ → ℝ) (R : ℕ → ℕ) (k : ℕ) : ℝ :=
  ε * triadicFineTheta F R k / 2

private noncomputable def triadicEnergyGap (q₃ : ℕ) (ε : ℝ) : ℝ :=
  (ε / (2 * ((q₃ : ℝ) + 1))) ^ 2

private noncomputable def triadicRecoloringCutoff (q₃ : ℕ) (ε : ℝ) (F : ℕ → ℝ) (R : ℕ → ℕ)
    (k nV : ℕ) : ℝ :=
  221 * (3 * (nV : ℝ) ^ 2 + q₃ + 7) / triadicFineBeta q₃ ε F R k ^ 2

private theorem triadicRank1Tol_pos {F : ℕ → ℝ} (hF : ∀ n, 0 < F n) (R : ℕ → ℕ) (k : ℕ) :
    0 < triadicRank1Tol F R k := by
  have := hF k
  unfold triadicRank1Tol
  positivity

private theorem triadicFineTheta_pos {F : ℕ → ℝ} (hF : ∀ n, 0 < F n) (R : ℕ → ℕ) (k : ℕ) :
    0 < triadicFineTheta F R k := by
  have := triadicRank1Tol_pos hF R k
  unfold triadicFineTheta
  positivity

private theorem triadicFineTol_pos (q₃ : ℕ) {F : ℕ → ℝ} (hF : ∀ n, 0 < F n) (R : ℕ → ℕ)
    (k : ℕ) : 0 < triadicFineTol q₃ F R k := by
  have := triadicRank1Tol_pos hF R k
  unfold triadicFineTol
  positivity

private theorem triadicFineMass_pos {ε : ℝ} (hε : 0 < ε) {F : ℕ → ℝ} (hF : ∀ n, 0 < F n)
    (R : ℕ → ℕ) (k : ℕ) : 0 < triadicFineMass ε F R k := by
  have := triadicFineTheta_pos hF R k
  unfold triadicFineMass
  positivity

private theorem triadicFineBeta_pos (q₃ : ℕ) {ε : ℝ} (hε : 0 < ε) {F : ℕ → ℝ}
    (hF : ∀ n, 0 < F n) (R : ℕ → ℕ) (k : ℕ) : 0 < triadicFineBeta q₃ ε F R k :=
  lt_min (by positivity) (triadicFineTol_pos q₃ hF R k)

private theorem triadicEnergyGap_pos (q₃ : ℕ) {ε : ℝ} (hε : 0 < ε) :
    0 < triadicEnergyGap q₃ ε := by
  unfold triadicEnergyGap
  positivity

private noncomputable def triadicCoarseBound (q₃ : ℕ) (ε : ℝ) (F : ℕ → ℝ) (R : ℕ → ℕ)
    (t₀ : ℕ) : ℕ :=
  strongTriadicRegularityBound F (triadicEnergyGap q₃ ε) (triadicFineTol q₃ F R)
    (triadicFineMass ε F R) (fun _ ↦ 1) (max t₀ 1)

private noncomputable def triadicCompCap (q₃ : ℕ) (ε : ℝ) (F : ℕ → ℝ) (R : ℕ → ℕ) (t₀ : ℕ) :
    ℕ :=
  let B := triadicCoarseBound q₃ ε F R t₀
  B + B + B ^ 3 * B ^ 3

private noncomputable def triadicRefinementCap (q₃ : ℕ) (ε : ℝ) (F : ℕ → ℝ) (R : ℕ → ℕ)
    (t₀ : ℕ) : ℕ :=
  let B := triadicCoarseBound q₃ ε F R t₀
  let Bcomp := triadicCompCap q₃ ε F R t₀
  (range (B + 1)).sup fun t ↦ (range (B + 1)).sup fun m ↦ (range (Bcomp + 1)).sup fun k ↦
    topRegularRefinementBound t 1 (triadicFineTol q₃ F R k) (triadicFineMass ε F R k) m

private noncomputable def triadicHostCap (q₃ : ℕ) (ε : ℝ) (F : ℕ → ℝ) (R : ℕ → ℕ) (t₀ : ℕ) :
    ℕ :=
  let B := triadicCoarseBound q₃ ε F R t₀
  let Bcomp := triadicCompCap q₃ ε F R t₀
  let Dmax := triadicRefinementCap q₃ ε F R t₀
  let Pmax : ℝ := B ^ 3 * Dmax ^ 3
  (range (Bcomp + 1)).sup fun k ↦
    ⌈2 * Pmax * 221 * ((q₃ : ℝ) + 10) /
      (triadicFineBeta q₃ ε F R k ^ 2 * triadicFineMass ε F R k)⌉₊

/-- Host-size and complexity bound for strong regular approximation of colored three-uniform
hypergraphs with `q₃` top colors, edit and exceptional-mass tolerance `ε`, regularity schedule `F`,
rank schedule `R`, and minimum vertex-cell count `t₀`. Whenever `0 < ε` and `∀ n, 0 < F n`, any
host `V` with `regularityBound3 q₃ ε F R t₀ ≤ |V|` supports a strong regular approximation whose
complex has complexity at most `regularityBound3 q₃ ε F R t₀`
(see `Colored3Graph.exists_strong_regular_approximation3`). -/
noncomputable def regularityBound3 (q₃ : ℕ) (ε : ℝ) (F : ℕ → ℝ) (R : ℕ → ℕ) (t₀ : ℕ) : ℕ :=
  max (max (max t₀ 6) (max (triadicCoarseBound q₃ ε F R t₀)
    (triadicCompCap q₃ ε F R t₀))) (triadicHostCap q₃ ε F R t₀)

/-- Unfolding lemma for `regularityBound3`. -/
theorem regularityBound3_def (q₃ : ℕ) (ε : ℝ) (F : ℕ → ℝ) (R : ℕ → ℕ) (t₀ : ℕ) :
    regularityBound3 q₃ ε F R t₀ =
      let δ k := F k ^ 2 / (2 : ℝ) ^ R k
      let θ k := δ k ^ 2 / 4
      let η k := δ k ^ 2 / (8 * ((q₃ : ℝ) + 1))
      let β k := min (ε / (2 * ((q₃ : ℝ) + 1))) (η k)
      let μ k := ε * θ k / 2
      let g := (ε / (2 * ((q₃ : ℝ) + 1))) ^ 2
      let B := strongTriadicRegularityBound F g η μ (fun _ ↦ 1) (max t₀ 1)
      let Bcomp := B + B + B ^ 3 * B ^ 3
      let Dmax := (range (B + 1)).sup fun t ↦ (range (B + 1)).sup fun m ↦
        (range (Bcomp + 1)).sup fun k ↦ topRegularRefinementBound t 1 (η k) (μ k) m
      let Pmax : ℝ := B ^ 3 * Dmax ^ 3
      let Nhost := (range (Bcomp + 1)).sup fun k ↦
        ⌈2 * Pmax * 221 * ((q₃ : ℝ) + 10) / (β k ^ 2 * μ k)⌉₊
      max (max (max t₀ 6) (max B Bcomp)) Nhost :=
  (rfl)

private theorem six_le_regularityBound3 (q₃ : ℕ) (ε : ℝ) (F : ℕ → ℝ) (R : ℕ → ℕ) (t₀ : ℕ) :
    6 ≤ regularityBound3 q₃ ε F R t₀ := by
  unfold regularityBound3
  omega

private theorem max_one_le_regularityBound3 (q₃ : ℕ) (ε : ℝ) (F : ℕ → ℝ) (R : ℕ → ℕ) (t₀ : ℕ) :
    max t₀ 1 ≤ regularityBound3 q₃ ε F R t₀ := by
  unfold regularityBound3
  omega

private theorem triadicCoarseBound_le_regularityBound3 (q₃ : ℕ) (ε : ℝ) (F : ℕ → ℝ) (R : ℕ → ℕ)
    (t₀ : ℕ) : triadicCoarseBound q₃ ε F R t₀ ≤ regularityBound3 q₃ ε F R t₀ := by
  unfold regularityBound3
  omega

private theorem triadicCompCap_le_regularityBound3 (q₃ : ℕ) (ε : ℝ) (F : ℕ → ℝ) (R : ℕ → ℕ)
    (t₀ : ℕ) : triadicCompCap q₃ ε F R t₀ ≤ regularityBound3 q₃ ε F R t₀ := by
  unfold regularityBound3
  omega

private theorem triadicHostCap_le_regularityBound3 (q₃ : ℕ) (ε : ℝ) (F : ℕ → ℝ) (R : ℕ → ℕ)
    (t₀ : ℕ) : triadicHostCap q₃ ε F R t₀ ≤ regularityBound3 q₃ ε F R t₀ := by
  unfold regularityBound3
  omega

private theorem topRegularRefinementBound_le_triadicRefinementCap {q₃ : ℕ} {ε : ℝ} {F : ℕ → ℝ}
    {R : ℕ → ℕ} {t₀ t m k : ℕ} (ht : t ≤ triadicCoarseBound q₃ ε F R t₀)
    (hm : m ≤ triadicCoarseBound q₃ ε F R t₀) (hk : k ≤ triadicCompCap q₃ ε F R t₀) :
    topRegularRefinementBound t 1 (triadicFineTol q₃ F R k) (triadicFineMass ε F R k) m ≤
      triadicRefinementCap q₃ ε F R t₀ := by
  unfold triadicRefinementCap
  refine le_trans ?_ (Finset.le_sup (mem_range.2 (Nat.lt_succ_of_le ht)))
  refine le_trans ?_ (Finset.le_sup (mem_range.2 (Nat.lt_succ_of_le hm)))
  refine le_trans ?_ (Finset.le_sup (mem_range.2 (Nat.lt_succ_of_le hk)))
  rfl

private theorem ceil_le_triadicHostCap {q₃ : ℕ} {ε : ℝ} {F : ℕ → ℝ} {R : ℕ → ℕ} {t₀ k : ℕ}
    (hk : k ≤ triadicCompCap q₃ ε F R t₀) :
    ⌈2 * ((triadicCoarseBound q₃ ε F R t₀ : ℝ) ^ 3 *
        (triadicRefinementCap q₃ ε F R t₀ : ℝ) ^ 3) * 221 * ((q₃ : ℝ) + 10) /
      (triadicFineBeta q₃ ε F R k ^ 2 * triadicFineMass ε F R k)⌉₊ ≤
      triadicHostCap q₃ ε F R t₀ := by
  unfold triadicHostCap
  refine le_trans ?_ (Finset.le_sup (mem_range.2 (Nat.lt_succ_of_le hk)))
  rfl

/-- `regularityBound3` is always at least the requested vertex-cell floor `t₀`. -/
theorem le_regularityBound3 (q₃ : ℕ) (ε : ℝ) (F : ℕ → ℝ) (R : ℕ → ℕ) (t₀ : ℕ) :
    t₀ ≤ regularityBound3 q₃ ε F R t₀ := by
  unfold regularityBound3
  omega

/-- `regularityBound3` is always at least `4`. -/
theorem four_le_regularityBound3 (q₃ : ℕ) (ε : ℝ) (F : ℕ → ℝ) (R : ℕ → ℕ) (t₀ : ℕ) :
    4 ≤ regularityBound3 q₃ ε F R t₀ :=
  (by decide : 4 ≤ 6).trans (six_le_regularityBound3 q₃ ε F R t₀)

/-- `regularityBound3` is always positive. -/
theorem regularityBound3_pos (q₃ : ℕ) (ε : ℝ) (F : ℕ → ℝ) (R : ℕ → ℕ) (t₀ : ℕ) :
    0 < regularityBound3 q₃ ε F R t₀ :=
  lt_of_lt_of_le (by decide) (four_le_regularityBound3 q₃ ε F R t₀)

namespace Colored3Graph

variable {κ V : Type*} [DecidableEq κ] [Fintype κ] [Fintype V] [DecidableEq V]

variable (H H' : Colored3Graph κ V) (C : TriadicComplex3 V) in
/-- **Strong regular approximation of a colored three-uniform hypergraph.** A coloring `H'` and a
triadic complex `C` form a strong regular approximation of `H` at tolerance `ε`, regularity
schedule `F`, rank schedule `R`, and vertex-cell floor `t₀` when:

* `H` approximates `H'` within `ε` in edit discrepancy;
* the selected polyads of `C` decompose all injective triples;
* the lower skeleton of `C` is regular for the schedule `F`;
* `H'` is `(F C.complexity, R C.complexity)`-top-regular over all polyads of `C` outside an
  `ε`-proportion of the injective triples; and
* the complexity of `C` is at most `regularityBound3 (Fintype.card κ) ε F R t₀`. -/
def IsStrongRegularApproximation3 (ε : ℝ) (F : ℕ → ℝ) (R : ℕ → ℕ) (t₀ : ℕ) : Prop :=
  H.Approximates3 H' ε ∧ C.IsPolyadDecomposition ∧ C.skeleton.LowerSkeletonRegular F ∧
    H'.TopRegularOverMostPolyads C (F C.complexity) ε (R C.complexity) ∧
    C.ComplexityBounded (regularityBound3 (Fintype.card κ) ε F R t₀)

/-- Unfolded form of `Colored3Graph.IsStrongRegularApproximation3`. -/
theorem isStrongRegularApproximation3_iff {H H' : Colored3Graph κ V} {C : TriadicComplex3 V}
    {ε : ℝ} {F : ℕ → ℝ} {R : ℕ → ℕ} {t₀ : ℕ} :
    H.IsStrongRegularApproximation3 H' C ε F R t₀ ↔
      H.Approximates3 H' ε ∧ C.IsPolyadDecomposition ∧ C.skeleton.LowerSkeletonRegular F ∧
        H'.TopRegularOverMostPolyads C (F C.complexity) ε (R C.complexity) ∧
        C.ComplexityBounded (regularityBound3 (Fintype.card κ) ε F R t₀) :=
  Iff.rfl

private theorem triadicFine_tol_le (q₃ : ℕ) (ε : ℝ) (F : ℕ → ℝ) (R : ℕ → ℕ) (K : ℕ) :
    2 * ((q₃ : ℝ) * (triadicFineTol q₃ F R K + triadicFineBeta q₃ ε F R K) +
      triadicFineTheta F R K) ≤ triadicRank1Tol F R K ^ 2 := by
  have hβ : triadicFineBeta q₃ ε F R K ≤ triadicFineTol q₃ F R K := min_le_right _ _
  have h1 : triadicFineTol q₃ F R K + triadicFineBeta q₃ ε F R K ≤ 2 * triadicFineTol q₃ F R K := by
    linarith
  have h2 : (q₃ : ℝ) * (2 * triadicFineTol q₃ F R K) ≤ triadicRank1Tol F R K ^ 2 / 4 := by
    dsimp only [triadicFineTol]
    field_simp
    nlinarith [sq_nonneg (triadicRank1Tol F R K), Nat.cast_nonneg (α := ℝ) q₃]
  have hqη : (q₃ : ℝ) * (triadicFineTol q₃ F R K + triadicFineBeta q₃ ε F R K) ≤
      triadicRank1Tol F R K ^ 2 / 4 :=
    (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)).trans h2
  dsimp only [triadicFineTheta]
  linarith

private theorem triadicFine_edit_le (q₃ : ℕ) {ε : ℝ} (hε : 0 < ε) (F : ℕ → ℝ) (R : ℕ → ℕ)
    (K : ℕ) :
    (q₃ : ℝ) * (√(triadicEnergyGap q₃ ε) + triadicFineBeta q₃ ε F R K) ≤ ε := by
  have hsqrt : √(triadicEnergyGap q₃ ε) = ε / (2 * ((q₃ : ℝ) + 1)) := sqrt_sq (by positivity)
  have hβ_le : triadicFineBeta q₃ ε F R K ≤ ε / (2 * ((q₃ : ℝ) + 1)) := min_le_left _ _
  have hq_le : (q₃ : ℝ) * (ε / (2 * ((q₃ : ℝ) + 1)) + ε / (2 * ((q₃ : ℝ) + 1))) ≤ ε := by
    field_simp
    linarith
  exact (mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)).trans hq_le

private theorem triadicRecoloringCutoff_nonneg (q₃ : ℕ) (ε : ℝ) (F : ℕ → ℝ) (R : ℕ → ℕ)
    (k nV : ℕ) : 0 ≤ triadicRecoloringCutoff q₃ ε F R k nV := by
  unfold triadicRecoloringCutoff
  positivity

private theorem le_triadicFineBeta_sq_mul_triadicRecoloringCutoff (q₃ : ℕ) {ε : ℝ} (hε : 0 < ε)
    {F : ℕ → ℝ} (hF : ∀ n, 0 < F n) (R : ℕ → ℕ) (k nV : ℕ) :
    221 * (3 * (nV : ℝ) ^ 2 + q₃ + 7) ≤
      triadicFineBeta q₃ ε F R k ^ 2 * triadicRecoloringCutoff q₃ ε F R k nV := by
  have hβ := triadicFineBeta_pos q₃ hε hF R k
  dsimp only [triadicRecoloringCutoff]
  rw [mul_div_cancel₀ _ (pow_ne_zero 2 hβ.ne')]

private theorem mul_triadicRecoloringCutoff_div_descFactorial_le (q₃ : ℕ) {ε : ℝ} (hε : 0 < ε)
    {F : ℕ → ℝ} (hF : ∀ n, 0 < F n) (R : ℕ → ℕ) (K nV B Dmax P : ℕ) (hnV6 : 6 ≤ nV)
    (hP : P ≤ B ^ 3 * Dmax ^ 3)
    (hhost : ⌈2 * ((B : ℝ) ^ 3 * (Dmax : ℝ) ^ 3) * 221 * ((q₃ : ℝ) + 10) /
      (triadicFineBeta q₃ ε F R K ^ 2 * triadicFineMass ε F R K)⌉₊ ≤ nV) :
    (P : ℝ) * triadicRecoloringCutoff q₃ ε F R K nV / nV.descFactorial 3 ≤
      triadicFineMass ε F R K := by
  have hμ := triadicFineMass_pos hε hF R K
  have hβ := triadicFineBeta_pos q₃ hε hF R K
  set β := triadicFineBeta q₃ ε F R K
  set μ := triadicFineMass ε F R K
  have hhost_real :
      2 * ((B : ℝ) ^ 3 * (Dmax : ℝ) ^ 3) * 221 * ((q₃ : ℝ) + 10) / (β ^ 2 * μ) ≤ nV :=
    (Nat.le_ceil _).trans (by exact_mod_cast hhost)
  have hDpoly : (P : ℝ) ≤ (B : ℝ) ^ 3 * (Dmax : ℝ) ^ 3 := by exact_mod_cast hP
  have hV_sq : (7 : ℝ) ≤ (nV : ℝ) ^ 2 := by
    have : (6 : ℝ) ≤ nV := by exact_mod_cast hnV6
    nlinarith
  have hV_pos : (0 : ℝ) < nV := by
    have : (6 : ℝ) ≤ nV := by exact_mod_cast hnV6
    linarith
  have hN₀_le :
      triadicRecoloringCutoff q₃ ε F R K nV ≤ 221 * ((q₃ : ℝ) + 10) * (nV : ℝ) ^ 2 / β ^ 2 := by
    dsimp only [triadicRecoloringCutoff]
    rw [mul_assoc 221]
    refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (by norm_num)) (sq_nonneg _)
    nlinarith [Nat.cast_nonneg (α := ℝ) q₃, hV_sq]
  have hpow3 : (nV : ℝ) ^ 3 ≤ 2 * (nV.descFactorial 3 : ℝ) := by
    exact_mod_cast Nat.pow_three_le_two_mul_descFactorial_three hnV6
  have hdesc_pos : (0 : ℝ) < nV.descFactorial 3 := by linarith [pow_pos hV_pos 3]
  rw [div_le_iff₀ hdesc_pos]
  have h1 : (P : ℝ) * triadicRecoloringCutoff q₃ ε F R K nV ≤
      ((B : ℝ) ^ 3 * (Dmax : ℝ) ^ 3) * (221 * ((q₃ : ℝ) + 10) * (nV : ℝ) ^ 2 / β ^ 2) :=
    mul_le_mul hDpoly hN₀_le (triadicRecoloringCutoff_nonneg q₃ ε F R K nV) (by positivity)
  have h2 : 2 * ((B : ℝ) ^ 3 * (Dmax : ℝ) ^ 3) * 221 * ((q₃ : ℝ) + 10) ≤ μ * β ^ 2 * nV := by
    rw [div_le_iff₀ (by positivity)] at hhost_real
    linarith
  calc (P : ℝ) * triadicRecoloringCutoff q₃ ε F R K nV
      ≤ ((B : ℝ) ^ 3 * (Dmax : ℝ) ^ 3) *
          (221 * ((q₃ : ℝ) + 10) * (nV : ℝ) ^ 2 / β ^ 2) := h1
    _ = (2 * ((B : ℝ) ^ 3 * (Dmax : ℝ) ^ 3) * 221 * ((q₃ : ℝ) + 10)) *
          (nV : ℝ) ^ 2 / (2 * β ^ 2) := by ring
    _ ≤ (μ * β ^ 2 * nV) * (nV : ℝ) ^ 2 / (2 * β ^ 2) := by gcongr
    _ = μ * ((nV : ℝ) ^ 3 / 2) := by field_simp [hβ.ne']
    _ ≤ μ * (nV.descFactorial 3 : ℝ) := mul_le_mul_of_nonneg_left (by linarith) hμ.le

private theorem triadicFine_mass_le (q₃ : ℕ) {ε : ℝ} (hε : 0 < ε) {F : ℕ → ℝ} (hF : ∀ n, 0 < F n)
    (R : ℕ → ℕ) (K nV B Dmax P : ℕ) (hnV6 : 6 ≤ nV) (hP : P ≤ B ^ 3 * Dmax ^ 3)
    (hhost : ⌈2 * ((B : ℝ) ^ 3 * (Dmax : ℝ) ^ 3) * 221 * ((q₃ : ℝ) + 10) /
      (triadicFineBeta q₃ ε F R K ^ 2 * triadicFineMass ε F R K)⌉₊ ≤ nV) :
    (triadicFineMass ε F R K +
        P * triadicRecoloringCutoff q₃ ε F R K nV / nV.descFactorial 3) /
      triadicFineTheta F R K ≤ ε := by
  have hθ := triadicFineTheta_pos hF R K
  have hsmall := mul_triadicRecoloringCutoff_div_descFactorial_le q₃ hε hF R K nV B Dmax P hnV6 hP
    hhost
  rw [div_le_iff₀ hθ]
  have hμ_eq : 2 * triadicFineMass ε F R K = ε * triadicFineTheta F R K := by
    dsimp only [triadicFineMass]
    ring
  linarith

private theorem complexity_le_triadicCompCap {C : TriadicComplex3 V} {q₃ : ℕ} {ε : ℝ} {F : ℕ → ℝ}
    {R : ℕ → ℕ} {t₀ : ℕ} (ht : #C.skeleton.vertexPart.parts ≤ triadicCoarseBound q₃ ε F R t₀)
    (hm : C.pairColorCount ≤ triadicCoarseBound q₃ ε F R t₀) :
    C.complexity ≤ triadicCompCap q₃ ε F R t₀ :=
  C.complexity_le.trans (by dsimp only [triadicCompCap]; gcongr)

/-- **Strong regular approximation of colored three-uniform hypergraphs.** For any finite palette
`κ`, tolerance `ε > 0`, positive regularity schedule `F`, rank schedule `R`, and vertex-cell floor
`t₀`, every colored three-uniform hypergraph `H` on at least
`regularityBound3 (Fintype.card κ) ε F R t₀` vertices admits a coloring `H'` and a triadic complex
`C` whose vertex cells form an equipartition into at least `t₀` cells and which satisfy
`H.IsStrongRegularApproximation3 H' C ε F R t₀`. -/
theorem exists_strong_regular_approximation3 (H : Colored3Graph κ V) {ε : ℝ} (hε : 0 < ε)
    {F : ℕ → ℝ} (hF : ∀ n, 0 < F n) (R : ℕ → ℕ) (t₀ : ℕ)
    (hV : regularityBound3 (Fintype.card κ) ε F R t₀ ≤ Fintype.card V) :
    ∃ (H' : Colored3Graph κ V) (C : TriadicComplex3 V),
      C.VertexCellsControlled t₀ ∧ H.IsStrongRegularApproximation3 H' C ε F R t₀ := by
  set q₃ := Fintype.card κ
  -- Step 1: obtain a regular coarse complex `C` and fine refinement `D` with small energy gap.
  obtain ⟨P₀, hP₀, hP₀_card⟩ := Finpartition.exists_equipartition_card_eq (univ : Finset V)
    (n := max t₀ 1) (by positivity)
    (by rw [card_univ]; exact (max_one_le_regularityBound3 q₃ ε F R t₀).trans hV)
  have hB' : strongTriadicRegularityBound F (triadicEnergyGap q₃ ε)
      (triadicFineTol q₃ F R) (triadicFineMass ε F R) (fun _ ↦ 1) #P₀.parts ≤ Fintype.card V := by
    rw [hP₀_card]
    exact (triadicCoarseBound_le_regularityBound3 q₃ ε F R t₀).trans hV
  obtain ⟨C, D, f, hCt, hCm, hDcard, hCP₀, hCeq, hDV, hCreg, hf, -, hCpol, hDpol, hDreg, hgap⟩ :=
    H.exists_strong_topRegularOverMostPolyads_lowerSkeletonRegular P₀ hP₀
      (triadicEnergyGap_pos q₃ hε) hF (triadicFineTol_pos q₃ hF R) (triadicFineMass_pos hε hF R)
      (fun _ ↦ 1) hB'
  rw [hP₀_card] at hCt hCm
  have hCcomp : C.complexity ≤ triadicCompCap q₃ ε F R t₀ := complexity_le_triadicCompCap hCt hCm
  have hD_le : D.pairColorCount ≤ triadicRefinementCap q₃ ε F R t₀ :=
    hDcard.trans (topRegularRefinementBound_le_triadicRefinementCap hCt hCm hCcomp)
  -- Step 2: coupled triple recoloring across the energy gap on `(C, D)`.
  set K := C.complexity
  obtain ⟨H', happrox, htop₁⟩ := hDreg.exists_approximates3_of_polyadEnergy_sub_le
    (C.isPolyadDecomposition_of_polyads_eq_univ hCpol)
    (D.isPolyadDecomposition_of_polyads_eq_univ hDpol) hDV.le f (fun p ↦ (hf p).symm) hgap
    (triadicFineTol_pos q₃ hF R K).le (triadicRank1Tol_pos hF R K)
    (triadicFineBeta_pos q₃ hε hF R K) (triadicFineTheta_pos hF R K)
    (le_triadicFineBeta_sq_mul_triadicRecoloringCutoff q₃ hε hF R K (Fintype.card V))
    (triadicFine_tol_le q₃ ε F R K)
  -- Step 3: conclude edit approximation and amplify coarse top regularity to rank `R K`.
  have hDpoly : Fintype.card (Polyad3 D.skeleton) ≤
      triadicCoarseBound q₃ ε F R t₀ ^ 3 * triadicRefinementCap q₃ ε F R t₀ ^ 3 :=
    (card_polyad3_le D.skeleton).trans (by
      rw [hDV, Fintype.card_fin]
      exact Nat.mul_le_mul (Nat.pow_le_pow_left hCt 3) (Nat.pow_le_pow_left hD_le 3))
  have htop' : H'.TopRegularOverMostPolyads C (F K) ε (R K) :=
    (htop₁.mono le_rfl (triadicFine_mass_le q₃ hε hF R K (Fintype.card V)
      (triadicCoarseBound q₃ ε F R t₀) (triadicRefinementCap q₃ ε F R t₀)
      (Fintype.card (Polyad3 D.skeleton)) ((six_le_regularityBound3 q₃ ε F R t₀).trans hV)
      hDpoly ((ceil_le_triadicHostCap hCcomp).trans
        ((triadicHostCap_le_regularityBound3 q₃ ε F R t₀).trans hV))) le_rfl).of_rank_one_div_pow
      (hF K)
  exact ⟨H', C,
    C.vertexCellsControlled_iff.2 ⟨hCeq, (le_max_left t₀ 1).trans (hP₀_card ▸ card_mono hCP₀)⟩,
    happrox.mono (triadicFine_edit_le q₃ hε F R K),
    C.isPolyadDecomposition_of_polyads_eq_univ hCpol, hCreg, htop',
    C.complexityBounded_iff.2
      (hCcomp.trans (triadicCompCap_le_regularityBound3 q₃ ε F R t₀))⟩

end Colored3Graph

end TauCeti
