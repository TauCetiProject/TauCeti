/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.Colored.EditDiscrepancy
public import TauCeti.Combinatorics.Hypergraph.Triadic.StrongTopRegularization

import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import TauCeti.Combinatorics.Enumerative.RandomColoring
import TauCeti.Combinatorics.Hypergraph.Polyad.Perm
import TauCeti.Combinatorics.Hypergraph.Triadic.Recoloring.CoarsePassage
import TauCeti.Data.Fintype.EmbeddingFiber
import TauCeti.LinearAlgebra.Matrix.Stochastic

/-!
# Coupled triple recoloring and strong top-regular approximation

Strong top regularization (`Colored3Graph.exists_strong_topRegularOverMostPolyads`) produces a
coarse complex `C` and a fine palette refinement `D` with small polyad energy gap `g` such that `H`
is top-regular over most polyads of `D` at schedules evaluated at `C.complexity`. Passing top
regularity directly down to `C` without editing `H` forces `g` below the coarse tolerance, so
only the rank can be scheduled at `C.complexity`.

Allowing a small global edit discrepancy `H.Approximates3 H' ε` removes that obstruction. On each
large fine polyad `Q` over `D.skeleton`, we couple `H` to a recoloring `H'` targeting the coarse
parent density `c ↦ H.relativeDensity c (Q.coarsen hV f)`:

1. **Simplex transition coupling:** `Matrix.exists_mem_rowStochastic_vecMul_eq` supplies a
   row-stochastic transition matrix `M` pushing the fine density `p` to the coarse parent density
   `q` with exact off-diagonal mass `max (p c₀ - q c₀) 0 ≤ |p c₀ - q c₀|`.
2. **Orbit-glued low-discrepancy recoloring:** unordered `3`-subsets are grouped by
   `(Equiv.Perm (Fin 3))ᵐᵒᵖ`-orbits of their fine polyads (`Polyad3.perm`), on which `#Q.support`
   and fine/coarse relative densities are invariant. Applying
   `TauCeti.exists_forall_abs_card_filter_sub_mul_card_lt` across all six ordered-fiber
   multiplicities (`Finset.card_filter_ofFinEmb_eq_sum_factorial`) and role permutations yields a
   single coloring `H'` tracking `H.relativeDensity c P` on every good fine child while keeping
   global edit discrepancy controlled by `g`.
3. **Coarse regularity and rank amplification:** summing over fine children yields coarse rank-one
   top regularity (`TopRegularOverMostPolyads.exists_approximates3_of_polyadEnergy_sub_le`), which
   `TopRegularOverMostPolyads.of_rank_one_div_pow` amplifies to any scheduled rank `r C.complexity`.

Combining this with `Colored3Graph.exists_strong_topRegularOverMostPolyads` (and handling small
hosts discretely by giving each ordered distinct pair its own color) yields
`Colored3Graph.exists_approximates3_topRegularOverMostPolyads`: for any `ε > 0`, positive schedules
`δ μ : ℕ → ℝ`, and rank schedule `r : ℕ → ℕ`, every lower skeleton `S` on any finite `V` admits a
palette refinement `C` with `C.pairColorCount ≤ topRegularApproximationPaletteBound ...` and an
`ε`-close coloring `H'` that is `(δ C.complexity, r C.complexity)`-top-regular off a
`μ C.complexity`-proportion of the injective triples.

## Main definitions

* `TauCeti.recoloringTolerance`, `TauCeti.recoloringMass`: the fine tolerance and exceptional
  proportion from which scheduled coupled recoloring reaches given coarse schedules.
* `TauCeti.recoloringHostBound`: the host size required by scheduled coupled recoloring.
* `TauCeti.topRegularApproximationPaletteBound`: host-independent bound on `C.pairColorCount`.

## Main results

* `TauCeti.Colored3Graph.TopRegularOverMostPolyads.exists_approximates3_of_polyadEnergy_sub_le`:
  coupled recoloring from fine rank-one top regularity across a small polyad energy gap.
* `TauCeti.Colored3Graph.TopRegularOverMostPolyads.exists_approximates3_of_recoloringHostBound_le`:
  scheduled coupled recoloring on a host of size at least `recoloringHostBound`.
* `TauCeti.Colored3Graph.exists_approximates3_topRegularOverMostPolyads`: scheduled strong
  top-regular approximation over any lower skeleton on any finite vertex set.

## References

* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007), the regular approximation lemma.
* N. Alon, E. Fischer, M. Krivelevich and M. Szegedy, *Efficient testing of large graphs*,
  Combinatorica 20 (2000), the strong regularity lemma.
* N. Alon and J. H. Spencer, *The Probabilistic Method*, 4th ed., Wiley (2016), Appendix A
  (Hoeffding concentration).
-/

public section

open Finset
open scoped Matrix

namespace TauCeti

section Helpers

/-- Index type for the discrepancy tests attached to a canonical orbit representative `Q₀`: a
role permutation `σ`, a subpolyad of `Q₀.perm σ`, and an ordered-fiber multiplicity `k + 1` in
`{1, …, 6}`. -/
private abbrev TestIdx {κ₂ V : Type*} [Fintype V] [DecidableEq V] {T : PairSkeleton3 κ₂ V}
    (Q₀ : Polyad3 T) : Type _ :=
  Σ σ : Equiv.Perm (Fin 3), Subpolyad3 (Q₀.perm σ) × Fin (Nat.factorial 3)

private theorem card_testIdx_le {κ₂ V : Type*} [Fintype V] [DecidableEq V]
    {T : PairSkeleton3 κ₂ V} (Q₀ : Polyad3 T) :
    Fintype.card (TestIdx Q₀) ≤ 36 * 2 ^ (3 * Fintype.card V ^ 2) := by
  classical
  dsimp only [TestIdx]
  rw [Fintype.card_sigma]
  calc ∑ σ : Equiv.Perm (Fin 3), Fintype.card (Subpolyad3 (Q₀.perm σ) × Fin (Nat.factorial 3))
      ≤ ∑ _σ : Equiv.Perm (Fin 3), 2 ^ (3 * Fintype.card V ^ 2) * Nat.factorial 3 := by
        refine sum_le_sum fun σ _ ↦ ?_
        rw [Fintype.card_prod, Fintype.card_fin]
        exact Nat.mul_le_mul_right _ (card_subpolyad3_le (Q₀.perm σ))
    _ = 36 * 2 ^ (3 * Fintype.card V ^ 2) := by
        rw [sum_const, card_univ, Fintype.card_perm, Fintype.card_fin, smul_eq_mul]
        norm_num [Nat.factorial]
        ring

private theorem pos_of_support_lower_bound {n q : ℕ} {β N₀ : ℝ}
    (hN₀ : 221 * (3 * (n : ℝ) ^ 2 + q + 7) ≤ β ^ 2 * N₀) : 0 < N₀ := by
  by_contra! hle
  have : β ^ 2 * N₀ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hle
  have hpos : (0 : ℝ) < 221 * (3 * (n : ℝ) ^ 2 + q + 7) := by positivity
  linarith

open Real in
/-- The polynomial support lower bound `221 * (3 |V|² + |κ| + 7) ≤ β² N₀` ensures both positivity
of `N₀` and the Hoeffding union-bound inequality for `TestIdx Q₀` at deviation `(β / 21) #Q₀`. -/
private theorem testIdx_union_bound {κ κ₂ V : Type*} [Fintype κ] [Fintype V] [DecidableEq V]
    {T : PairSkeleton3 κ₂ V} {β N₀ : ℝ} (hβ : 0 < β)
    (hN₀ : 221 * (3 * (Fintype.card V : ℝ) ^ 2 + Fintype.card κ + 7) ≤ β ^ 2 * N₀)
    (Q₀ : Polyad3 T) (hQ₀ : N₀ ≤ (#Q₀.support : ℝ)) :
    0 < (β / 21) * (#Q₀.support : ℝ) ∧
      2 * Fintype.card (TestIdx Q₀) * Fintype.card κ *
        exp (-2 * ((β / 21) * (#Q₀.support : ℝ)) ^ 2 / (#Q₀.support : ℝ)) < 1 := by
  set n := Fintype.card V
  set B : ℝ := 3 * (n : ℝ) ^ 2 + Fintype.card κ + 7
  have hQpos : (0 : ℝ) < #Q₀.support := (pos_of_support_lower_bound hN₀).trans_le hQ₀
  refine ⟨by positivity, ?_⟩
  have hcard2 : 2 * Fintype.card (TestIdx Q₀) ≤ 2 ^ (3 * n ^ 2 + 7) := by
    have h1 := Nat.mul_le_mul_left 2 (card_testIdx_le Q₀)
    have h27 : (2 : ℕ) ^ 7 = 128 := by norm_num
    rw [pow_add, h27]
    linarith
  have hIexp : (2 : ℝ) * Fintype.card (TestIdx Q₀) ≤ exp (3 * (n : ℝ) ^ 2 + 7) := by
    have h2e : (2 : ℝ) ≤ exp 1 := by linarith [add_one_le_exp (1 : ℝ)]
    calc (2 : ℝ) * Fintype.card (TestIdx Q₀)
        ≤ (2 : ℝ) ^ (3 * n ^ 2 + 7) := by exact_mod_cast hcard2
      _ ≤ exp 1 ^ (3 * n ^ 2 + 7) := pow_le_pow_left₀ (by norm_num) h2e _
      _ = exp (3 * (n : ℝ) ^ 2 + 7) := by rw [← exp_natCast_mul, mul_one]; push_cast; rfl
  have hKexp : (Fintype.card κ : ℝ) ≤ exp (Fintype.card κ) := by
    linarith [add_one_le_exp (Fintype.card κ : ℝ)]
  have hexp_eq : -2 * ((β / 21) * (#Q₀.support : ℝ)) ^ 2 / (#Q₀.support : ℝ) =
      -(2 / 441) * (β ^ 2 * (#Q₀.support : ℝ)) := by field_simp [hQpos.ne']; ring
  have hBN : 221 * B ≤ β ^ 2 * (#Q₀.support : ℝ) :=
    hN₀.trans (mul_le_mul_of_nonneg_left hQ₀ (by positivity))
  have hexp_lt : -2 * ((β / 21) * (#Q₀.support : ℝ)) ^ 2 / (#Q₀.support : ℝ) < -B := by
    have hBpos : 0 < B := by positivity
    rw [hexp_eq]; linarith
  calc 2 * (Fintype.card (TestIdx Q₀) : ℝ) * Fintype.card κ *
          exp (-2 * ((β / 21) * (#Q₀.support : ℝ)) ^ 2 / (#Q₀.support : ℝ))
      ≤ exp (3 * (n : ℝ) ^ 2 + 7) * exp (Fintype.card κ) *
          exp (-2 * ((β / 21) * (#Q₀.support : ℝ)) ^ 2 / (#Q₀.support : ℝ)) := by gcongr
    _ < exp (3 * (n : ℝ) ^ 2 + 7) * exp (Fintype.card κ) * exp (-B) := by gcongr
    _ = 1 := by rw [← exp_add, ← exp_add]; convert exp_zero; dsimp only [B]; ring

/-- Canonical representative of the `(Equiv.Perm (Fin 3))ᵐᵒᵖ`-orbit of a fine polyad `Q`. -/
private noncomputable def canonPolyad {κ₂ V : Type*} [Fintype V] [DecidableEq V]
    {T : PairSkeleton3 κ₂ V} (Q : Polyad3 T) : Polyad3 T :=
  (Quotient.mk (MulAction.orbitRel (Equiv.Perm (Fin 3))ᵐᵒᵖ (Polyad3 T)) Q).out

private theorem exists_perm_canonPolyad {κ₂ V : Type*} [Fintype V] [DecidableEq V]
    {T : PairSkeleton3 κ₂ V} (Q : Polyad3 T) :
    ∃ σ : Equiv.Perm (Fin 3), (canonPolyad Q).perm σ = Q := by
  have hq : canonPolyad Q ∈ MulAction.orbit (Equiv.Perm (Fin 3))ᵐᵒᵖ Q :=
    Quotient.exact (Quotient.out_eq
      (Quotient.mk (MulAction.orbitRel (Equiv.Perm (Fin 3))ᵐᵒᵖ (Polyad3 T)) Q))
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_symm.1 hq
  exact ⟨g.unop, hg⟩

private theorem canonPolyad_perm {κ₂ V : Type*} [Fintype V] [DecidableEq V]
    {T : PairSkeleton3 κ₂ V} (Q : Polyad3 T) (σ : Equiv.Perm (Fin 3)) :
    canonPolyad (Q.perm σ) = canonPolyad Q :=
  congrArg Quotient.out (Quotient.sound ⟨MulOpposite.op σ, rfl⟩)

private theorem card_support_canonPolyad {κ₂ V : Type*} [Fintype V] [DecidableEq V]
    {T : PairSkeleton3 κ₂ V} (Q : Polyad3 T) :
    #(canonPolyad Q).support = #Q.support := by
  obtain ⟨σ, hσ⟩ := exists_perm_canonPolyad Q
  conv_rhs => rw [← hσ]
  exact ((canonPolyad Q).card_support_perm σ).symm

/-- Canonical fine-polyad orbit representative assigned to an unordered `3`-subset `s`. -/
private noncomputable def canonTriple {κ₂ V : Type*} [Fintype V] [DecidableEq V]
    (T : PairSkeleton3 κ₂ V) (s : Set.powersetCard V 3) : Polyad3 T :=
  let e := (Set.powersetCard.ofFinEmb_surjective 3 V s).choose
  canonPolyad (Polyad3.ofTriple T ⟨e.toFun, e.inj'⟩)

private theorem canonTriple_ofFinEmb_eq {κ₂ V : Type*} [Fintype V] [DecidableEq V]
    {T : PairSkeleton3 κ₂ V} {Q : Polyad3 T} {x : {x : Fin 3 → V // Function.Injective x}}
    (hx : x ∈ Q.support) :
    canonTriple T (Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩) = canonPolyad Q := by
  set s := Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩
  let e := (Set.powersetCard.ofFinEmb_surjective 3 V s).choose
  have he : Set.powersetCard.ofFinEmb 3 V e = s :=
    (Set.powersetCard.ofFinEmb_surjective 3 V s).choose_spec
  obtain ⟨σ, hσ⟩ := (Set.powersetCard.ofFinEmb_eq_iff_exists_perm ⟨x.val, x.property⟩ e).1 he.symm
  let x₀ : {x : Fin 3 → V // Function.Injective x} := ⟨e.toFun, e.inj'⟩
  have hx_eq : x = ⟨x₀.val ∘ σ, x₀.property.comp σ.injective⟩ := Subtype.ext hσ
  have hQ_eq : Q = (Polyad3.ofTriple T x₀).perm σ := by
    rw [Polyad3.mem_support_iff_eq_ofTriple.1 hx, hx_eq, Polyad3.ofTriple_comp_perm]
  dsimp only [canonTriple]
  rw [hQ_eq, canonPolyad_perm]

private theorem card_filter_color_fiberwise {κ V : Type*} [Fintype κ] [DecidableEq κ]
    (H : Colored3Graph κ V) (W : Finset {x : Fin 3 → V // Function.Injective x})
    (P : Set.powersetCard V 3 → Prop) [DecidablePred P] :
    #{x ∈ W | P (Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩)} =
      ∑ c₀ : κ, #{x ∈ W | H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩) = c₀ ∧
        P (Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩)} := by
  classical
  rw [card_eq_sum_card_fiberwise
    (f := fun x ↦ H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩))
    (t := univ) (fun _ _ ↦ mem_univ _)]
  exact sum_congr rfl fun c₀ _ ↦ congrArg card (ext fun x ↦ by simp only [mem_filter]; tauto)

private theorem mul_add_le_of_div_two_add_one (q : ℕ) {a x y : ℝ} (ha : 0 ≤ a)
    (hx : x = a / (2 * ((q : ℝ) + 1))) (hy : y ≤ x) : (q : ℝ) * (x + y) ≤ a := by
  calc (q : ℝ) * (x + y) ≤ (q : ℝ) * (2 * x) :=
        mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg q)
    _ ≤ a := by rw [hx, ← mul_assoc, mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith

private theorem small_polyad_mass_le {v q cardD : ℕ} {P β μ' : ℝ}
    (hv4 : 4 ≤ v) (hDP : (cardD : ℝ) ≤ P) (hP : 0 ≤ P) (hβ : 0 < β) (hμ' : 0 < μ')
    (hv_real : 4 * P * 221 * ((q : ℝ) + 10) / (β ^ 2 * μ') < v) :
    (cardD : ℝ) * (221 * (3 * (v : ℝ) ^ 2 + q + 7) / β ^ 2) / v.descFactorial 3 ≤ μ' := by
  have hv_desc : v ^ 3 ≤ 4 * v.descFactorial 3 := by
    rw [Nat.descFactorial_succ, Nat.descFactorial_succ, Nat.descFactorial_one]
    have h1 : v ≤ 2 * (v - 1) := by omega
    have h2 : v ≤ 2 * (v - 2) := by omega
    calc v ^ 3 = v * (v * v) := by ring
      _ ≤ v * ((2 * (v - 1)) * (2 * (v - 2))) := Nat.mul_le_mul_left v (Nat.mul_le_mul h1 h2)
      _ = 4 * ((v - 2) * ((v - 1) * v)) := by ring
  have hv_desc_pos : (0 : ℝ) < v.descFactorial 3 := by
    have : 0 < v.descFactorial 3 := by
      have := (pow_pos (by omega : 0 < v) 3).trans_le hv_desc; omega
    exact_mod_cast this
  have hN₀_le : 221 * (3 * (v : ℝ) ^ 2 + q + 7) / β ^ 2 ≤
      221 * ((q : ℝ) + 10) * (v : ℝ) ^ 2 / β ^ 2 := by
    refine div_le_div_of_nonneg_right ?_ (sq_nonneg _)
    have hv1 : (1 : ℝ) ≤ (v : ℝ) ^ 2 := by exact_mod_cast (by nlinarith : 1 ≤ v ^ 2)
    have hqv : (q : ℝ) ≤ q * (v : ℝ) ^ 2 := le_mul_of_one_le_right (Nat.cast_nonneg q) hv1
    linarith
  have hv_mul : 4 * P * 221 * ((q : ℝ) + 10) ≤ (v : ℝ) * (β ^ 2 * μ') :=
    ((div_lt_iff₀ (mul_pos (pow_pos hβ 2) hμ')).1 hv_real).le
  rw [div_le_iff₀ hv_desc_pos]
  calc (cardD : ℝ) * (221 * (3 * (v : ℝ) ^ 2 + q + 7) / β ^ 2)
      ≤ P * (221 * ((q : ℝ) + 10) * (v : ℝ) ^ 2 / β ^ 2) :=
        mul_le_mul hDP hN₀_le (by positivity) hP
    _ = (4 * P * 221 * ((q : ℝ) + 10)) * ((v : ℝ) ^ 2 / (4 * β ^ 2)) := by field_simp [hβ.ne']
    _ ≤ ((v : ℝ) * (β ^ 2 * μ')) * ((v : ℝ) ^ 2 / (4 * β ^ 2)) :=
        mul_le_mul_of_nonneg_right hv_mul (by positivity)
    _ = μ' * ((v : ℝ) ^ 3 / 4) := by field_simp [hβ.ne']
    _ ≤ μ' * v.descFactorial 3 := by
        have hv_descR : (v : ℝ) ^ 3 ≤ 4 * (v.descFactorial 3 : ℝ) := by exact_mod_cast hv_desc
        exact mul_le_mul_of_nonneg_left (by linarith) hμ'.le

end Helpers

/-! ### Explicit bounds for scheduled top-regular approximation -/

/-- The fine tolerance in scheduled coupled recoloring: to reach `(δ n, r n)`-top regularity over
a coarse complex of complexity `n` for a palette of `q` top colors, a fine palette refinement is
required to be rank-one top-regular at this tolerance. -/
noncomputable def recoloringTolerance (q : ℕ) (δ : ℕ → ℝ) (r : ℕ → ℕ) (n : ℕ) : ℝ :=
  ((δ n) ^ 2 / (2 : ℝ) ^ r n) ^ 2 / (8 * ((q : ℝ) + 1))

/-- Unfolding lemma for `recoloringTolerance`. -/
theorem recoloringTolerance_def (q : ℕ) (δ : ℕ → ℝ) (r : ℕ → ℕ) (n : ℕ) :
    recoloringTolerance q δ r n = ((δ n) ^ 2 / (2 : ℝ) ^ r n) ^ 2 / (8 * ((q : ℝ) + 1)) :=
  (rfl)

/-- The fine tolerance is positive wherever the coarse tolerance is. -/
theorem recoloringTolerance_pos (q : ℕ) {δ : ℕ → ℝ} (r : ℕ → ℕ) {n : ℕ} (hδ : 0 < δ n) :
    0 < recoloringTolerance q δ r n := by
  rw [recoloringTolerance_def]
  positivity

/-- The fine exceptional proportion in scheduled coupled recoloring: to reach an exceptional
proportion `μ n` over a coarse complex of complexity `n`, a fine palette refinement is required
to be top-regular off this proportion. -/
noncomputable def recoloringMass (δ μ : ℕ → ℝ) (r : ℕ → ℕ) (n : ℕ) : ℝ :=
  μ n * (((δ n) ^ 2 / (2 : ℝ) ^ r n) ^ 2 / 4) / 2

/-- Unfolding lemma for `recoloringMass`. -/
theorem recoloringMass_def (δ μ : ℕ → ℝ) (r : ℕ → ℕ) (n : ℕ) :
    recoloringMass δ μ r n = μ n * (((δ n) ^ 2 / (2 : ℝ) ^ r n) ^ 2 / 4) / 2 :=
  (rfl)

/-- The fine exceptional proportion is positive wherever the coarse tolerance and exceptional
proportion are. -/
theorem recoloringMass_pos {δ μ : ℕ → ℝ} (r : ℕ → ℕ) {n : ℕ} (hδ : 0 < δ n) (hμ : 0 < μ n) :
    0 < recoloringMass δ μ r n := by
  rw [recoloringMass_def]
  positivity

/-- The host size required by scheduled coupled recoloring with edit budget `ε`, over a coarse
complex of complexity at most `K` whose fine palette refinement has at most `P` polyads: each fine
polyad with fewer triples than the Hoeffding support bound is left unrecolored, and on such a
host these polyads carry a negligible proportion of the triples. -/
noncomputable def recoloringHostBound (q : ℕ) (ε : ℝ) (δ μ : ℕ → ℝ) (r : ℕ → ℕ) (K P : ℕ) :
    ℕ :=
  max 4 ((range (K + 1)).sup fun n ↦
    ⌊4 * (P : ℝ) * 221 * ((q : ℝ) + 10) /
      ((min (ε / (2 * ((q : ℝ) + 1))) (recoloringTolerance q δ r n)) ^ 2 *
        recoloringMass δ μ r n)⌋₊ + 1)

/-- Unfolding lemma for `recoloringHostBound`. -/
theorem recoloringHostBound_def (q : ℕ) (ε : ℝ) (δ μ : ℕ → ℝ) (r : ℕ → ℕ) (K P : ℕ) :
    recoloringHostBound q ε δ μ r K P =
      max 4 ((range (K + 1)).sup fun n ↦
        ⌊4 * (P : ℝ) * 221 * ((q : ℝ) + 10) /
          ((min (ε / (2 * ((q : ℝ) + 1))) (recoloringTolerance q δ r n)) ^ 2 *
            recoloringMass δ μ r n)⌋₊ + 1) :=
  (rfl)

/-- Host-independent upper bound on `C.pairColorCount` in
`Colored3Graph.exists_approximates3_topRegularOverMostPolyads`, for top palette size `q`, `t`
vertex cells, `m` initial pair colors, edit budget `ε`, positive schedules `δ` and `μ`, and rank
schedule `r`. The square of the host bound absorbs the discrete palette refinement on small
hosts. -/
noncomputable def topRegularApproximationPaletteBound (q t : ℕ) (ε : ℝ) (δ μ : ℕ → ℝ)
    (r : ℕ → ℕ) (m : ℕ) : ℕ :=
  let M := strongTopRegularityBound t ((ε / (2 * ((q : ℝ) + 1))) ^ 2) (recoloringTolerance q δ r)
    (recoloringMass δ μ r) (fun _ ↦ 1) m
  let M' := strongTopRegularityStep t (recoloringTolerance q δ r) (recoloringMass δ μ r)
    (fun _ ↦ 1) M
  max M (recoloringHostBound q ε δ μ r (t + M + t ^ 3 * M ^ 3) (t ^ 3 * M' ^ 3) ^ 2)

/-- Unfolding lemma for `topRegularApproximationPaletteBound`. -/
theorem topRegularApproximationPaletteBound_def (q t : ℕ) (ε : ℝ) (δ μ : ℕ → ℝ) (r : ℕ → ℕ)
    (m : ℕ) :
    topRegularApproximationPaletteBound q t ε δ μ r m =
      let M := strongTopRegularityBound t ((ε / (2 * ((q : ℝ) + 1))) ^ 2)
        (recoloringTolerance q δ r) (recoloringMass δ μ r) (fun _ ↦ 1) m
      let M' := strongTopRegularityStep t (recoloringTolerance q δ r) (recoloringMass δ μ r)
        (fun _ ↦ 1) M
      max M (recoloringHostBound q ε δ μ r (t + M + t ^ 3 * M ^ 3) (t ^ 3 * M' ^ 3) ^ 2) :=
  (rfl)

namespace Colored3Graph

section EnergyGapRecoloring

variable {κ V : Type*} [Fintype V] [DecidableEq V] [DecidableEq κ]

private theorem relativeDensity_canonPolyad {κ₂ : Type*} {T : PairSkeleton3 κ₂ V}
    (H : Colored3Graph κ V) (Q : Polyad3 T) (c : κ) :
    H.relativeDensity c (canonPolyad Q) = H.relativeDensity c Q := by
  obtain ⟨σ₀, hσ₀⟩ := exists_perm_canonPolyad Q
  conv_rhs => rw [← hσ₀]
  exact (H.relativeDensity_perm c (canonPolyad Q) σ₀).symm

private theorem relativeDensity_coarsen_canonPolyad {κ₁ κ₂ : Type*} {S : PairSkeleton3 κ₁ V}
    {T : PairSkeleton3 κ₂ V} (hV : T.vertexPart ≤ S.vertexPart) (f : κ₂ → κ₁)
    (hf : ∀ p, S.pairColors.color p = f (T.pairColors.color p))
    (H : Colored3Graph κ V) {Q : Polyad3 T} (hQ : Q.support.Nonempty) (c : κ) :
    H.relativeDensity c ((canonPolyad Q).coarsen hV f) = H.relativeDensity c (Q.coarsen hV f) := by
  obtain ⟨σ₀, hσ₀⟩ := exists_perm_canonPolyad Q
  have hcan_ne : (canonPolyad Q).support.Nonempty := by
    rw [← card_pos, card_support_canonPolyad]
    exact hQ.card_pos
  conv_rhs => rw [← hσ₀]
  rw [Polyad3.coarsen_perm_of_support_nonempty _ hcan_ne σ₀ hV f hf, H.relativeDensity_perm]

/-- Orbit-glued coupled recoloring: produces a coloring `H'` and row-stochastic transition
matrices `M Q₀` pushing fine densities to coarse parent densities on every fine polyad `Q` with
`N₀ ≤ #Q.support`, tracking `M` within `β * #Q.support` on every subpolyad while leaving smaller
fine polyads untouched. -/
private theorem exists_coupled_recoloring [Fintype κ]
    {H : Colored3Graph κ V} {C D : TriadicComplex3 V} {β N₀ : ℝ}
    (hV : D.skeleton.vertexPart ≤ C.skeleton.vertexPart)
    (f : Fin D.pairColorCount → Fin C.pairColorCount)
    (hf : ∀ p, C.skeleton.pairColors.color p = f (D.skeleton.pairColors.color p))
    (hβ : 0 < β)
    (hN₀ : 221 * (3 * (Fintype.card V : ℝ) ^ 2 + Fintype.card κ + 7) ≤ β ^ 2 * N₀) :
    ∃ (H' : Colored3Graph κ V) (M : Polyad3 D.skeleton → Matrix κ κ ℝ),
      (∀ Q : Polyad3 D.skeleton, N₀ ≤ (#Q.support : ℝ) →
        M (canonPolyad Q) ∈ Matrix.rowStochastic ℝ κ ∧
        (fun c₀ ↦ (H.relativeDensity c₀ (canonPolyad Q) : ℝ)) ᵥ* M (canonPolyad Q) =
          (fun c ↦ (H.relativeDensity c ((canonPolyad Q).coarsen hV f) : ℝ)) ∧
        (∀ c₀, (H.relativeDensity c₀ (canonPolyad Q) : ℝ) * (1 - M (canonPolyad Q) c₀ c₀) =
          max ((H.relativeDensity c₀ (canonPolyad Q) : ℝ) -
            H.relativeDensity c₀ ((canonPolyad Q).coarsen hV f)) 0) ∧
        ∀ (S' : Subpolyad3 Q) (c₀ c : κ),
          |(#{x ∈ S'.support | H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩) = c₀ ∧
              H'.color (Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩) = c} : ℝ) -
            M (canonPolyad Q) c₀ c *
              #{x ∈ S'.support | H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.val,
                  x.property⟩) = c₀}| ≤
            β * #Q.support) ∧
      (∀ Q : Polyad3 D.skeleton, ¬N₀ ≤ (#Q.support : ℝ) → H.editedOn H' Q.support = ∅) := by
  classical
  have hN₀_pos : 0 < N₀ := pos_of_support_lower_bound hN₀
  let L (Q₀ : Polyad3 D.skeleton) (c₀ : κ) (idx : TestIdx Q₀) : Finset (Set.powersetCard V 3) :=
    univ.filter fun s ↦ H.color s = c₀ ∧
      #{x ∈ idx.2.1.support | Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩ = s} = idx.2.2.val +
          1
  have hL_card (Q₀ : Polyad3 D.skeleton) (c₀ : κ) (idx : TestIdx Q₀) :
      #(L Q₀ c₀ idx) ≤ #Q₀.support := by
    obtain ⟨σ, S', k⟩ := idx
    calc #(L Q₀ c₀ ⟨σ, S', k⟩)
        = ∑ _s ∈ L Q₀ c₀ ⟨σ, S', k⟩, 1 := by simp
      _ ≤ ∑ s ∈ L Q₀ c₀ ⟨σ, S', k⟩,
            #{x ∈ S'.support | Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩ = s} :=
          sum_le_sum fun s hs ↦ by rw [(mem_filter.1 hs).2.2]; omega
      _ ≤ ∑ s : Set.powersetCard V 3,
            #{x ∈ S'.support | Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩ = s} :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ ↦ Nat.zero_le _
      _ = #S'.support := (card_eq_sum_card_fiberwise fun _ _ ↦ mem_univ _).symm
      _ ≤ #(Q₀.perm σ).support := card_le_card S'.support_subset
      _ = #Q₀.support := Q₀.card_support_perm σ
  have hcouple (Q₀ : Polyad3 D.skeleton) :
      ∃ (M : Matrix κ κ ℝ) (φ : κ → Set.powersetCard V 3 → κ),
        N₀ ≤ (#Q₀.support : ℝ) →
          M ∈ Matrix.rowStochastic ℝ κ ∧
          (fun c₀ ↦ (H.relativeDensity c₀ Q₀ : ℝ)) ᵥ* M =
            (fun c ↦ (H.relativeDensity c (Q₀.coarsen hV f) : ℝ)) ∧
          (∀ c₀, (H.relativeDensity c₀ Q₀ : ℝ) * (1 - M c₀ c₀) =
            max ((H.relativeDensity c₀ Q₀ : ℝ) - H.relativeDensity c₀ (Q₀.coarsen hV f)) 0) ∧
          ∀ c₀ (idx : TestIdx Q₀) c,
            |(#{s ∈ L Q₀ c₀ idx | φ c₀ s = c} : ℝ) - M c₀ c * #(L Q₀ c₀ idx)| <
              (β / 21) * #Q₀.support := by
    by_cases hQ₀ : N₀ ≤ (#Q₀.support : ℝ)
    · have hQ₀_ne : Q₀.support.Nonempty := card_pos.1 (by exact_mod_cast hN₀_pos.trans_le hQ₀)
      have hP₀_ne : (Q₀.coarsen hV f).support.Nonempty :=
        hQ₀_ne.mono (Polyad3.support_subset_coarsen hV f hf Q₀)
      have hsum : (∑ c, (H.relativeDensity c Q₀ : ℝ)) =
          ∑ c, (H.relativeDensity c (Q₀.coarsen hV f) : ℝ) := by
        exact_mod_cast (H.sum_relativeDensity hQ₀_ne).trans (H.sum_relativeDensity hP₀_ne).symm
      obtain ⟨M, hMmem, hMpush, hMdiag⟩ := Matrix.exists_mem_rowStochastic_vecMul_eq hsum
        (fun c ↦ mod_cast H.relativeDensity_nonneg c _)
      obtain ⟨ha, hub⟩ := testIdx_union_bound (κ := κ) hβ hN₀ Q₀ hQ₀
      have hφ (c₀ : κ) : ∃ φ₀ : Set.powersetCard V 3 → κ, ∀ (idx : TestIdx Q₀) c,
          |(#{s ∈ L Q₀ c₀ idx | φ₀ s = c} : ℝ) - M c₀ c * #(L Q₀ c₀ idx)| <
            (β / 21) * #Q₀.support :=
        exists_forall_abs_card_filter_sub_mul_card_lt
          (fun c ↦ Matrix.nonneg_of_mem_rowStochastic hMmem)
          (Matrix.sum_row_of_mem_rowStochastic hMmem c₀) (L Q₀ c₀) (hL_card Q₀ c₀) ha hub
      choose φ hφ using hφ
      exact ⟨M, φ, fun _ ↦ ⟨hMmem, hMpush, hMdiag, hφ⟩⟩
    · exact ⟨0, fun c₀ _ ↦ c₀, fun h' ↦ absurd h' hQ₀⟩
  choose M φ hMφ using hcouple
  let H' : Colored3Graph κ V :=
    ⟨fun s ↦ if N₀ ≤ (#(canonTriple D.skeleton s).support : ℝ) then
      φ (canonTriple D.skeleton s) (H.color s) s else H.color s⟩
  refine ⟨H', M, fun Q hQ ↦ ?_, fun Q hQ ↦ ?_⟩
  · set Q₀ := canonPolyad Q
    obtain ⟨σ₀, hσ₀⟩ := exists_perm_canonPolyad Q
    have hQ₀_card : #Q₀.support = #Q.support := card_support_canonPolyad Q
    have hQ₀ : N₀ ≤ (#Q₀.support : ℝ) := by rwa [hQ₀_card]
    obtain ⟨hMmem, hMpush, hMdiag, hφ_disc⟩ := hMφ Q₀ hQ₀
    refine ⟨hMmem, hMpush, hMdiag, fun S' c₀ c ↦ ?_⟩
    let S₀ : Subpolyad3 (Q₀.perm σ₀) :=
      S'.inclusion (hσ₀ ▸ Subset.rfl) (hσ₀ ▸ Subset.rfl) (hσ₀ ▸ Subset.rfl)
    have hS₀ : S₀.support = S'.support := Subpolyad3.support_inclusion _ _ _ S'
    have hH'_on_L (k : Fin (Nat.factorial 3)) :
        #{s : Set.powersetCard V 3 | (H.color s = c₀ ∧ H'.color s = c) ∧
            #{x ∈ S'.support | Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩ = s} = k.val + 1} =
          #{s ∈ L Q₀ c₀ ⟨σ₀, S₀, k⟩ | φ Q₀ c₀ s = c} := by
      refine congrArg card (ext fun s ↦ ?_)
      simp only [L, mem_filter, mem_univ, true_and, hS₀]
      by_cases hm : #{x ∈ S'.support | Set.powersetCard.ofFinEmb 3 V ⟨x.val,
          x.property⟩ = s} = k.val + 1
      · obtain ⟨x, hx⟩ := card_pos.1 (by omega : 0 < #{x ∈ S'.support |
          Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩ = s})
        obtain ⟨hxS, hxs⟩ := mem_filter.1 hx
        have hcan : canonTriple D.skeleton s = Q₀ :=
          hxs ▸ canonTriple_ofFinEmb_eq (S'.support_subset hxS)
        by_cases hc₀ : H.color s = c₀ <;> simp [H', hcan, hQ₀, hc₀, hm]
      · simp [hm]
    rw [S'.support.card_filter_ofFinEmb_eq_sum_factorial fun s ↦ H.color s = c₀,
      S'.support.card_filter_ofFinEmb_eq_sum_factorial fun s ↦ H.color s = c₀ ∧ H'.color s = c]
    simp_rw [hH'_on_L]
    have h1' (k : Fin (Nat.factorial 3)) :
        #{s : Set.powersetCard V 3 | H.color s = c₀ ∧
            #{x ∈ S'.support | Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩ = s} = k.val + 1} =
          #(L Q₀ c₀ ⟨σ₀, S₀, k⟩) := by simp only [L, hS₀]
    simp_rw [h1']
    push_cast
    rw [mul_sum, ← sum_sub_distrib]
    let d (k : Fin (Nat.factorial 3)) : ℝ :=
      (#{s ∈ L Q₀ c₀ ⟨σ₀, S₀, k⟩ | φ Q₀ c₀ s = c} : ℝ) - M Q₀ c₀ c * #(L Q₀ c₀ ⟨σ₀, S₀, k⟩)
    calc |∑ k : Fin (Nat.factorial 3), ((k.val + 1 : ℝ) *
            #{s ∈ L Q₀ c₀ ⟨σ₀, S₀, k⟩ | φ Q₀ c₀ s = c} -
            M Q₀ c₀ c * ((k.val + 1 : ℝ) * #(L Q₀ c₀ ⟨σ₀, S₀, k⟩)))|
        = |∑ k, (k.val + 1 : ℝ) * d k| := congrArg abs (sum_congr rfl fun k _ ↦ by dsimp [d]; ring)
      _ ≤ ∑ k, |(k.val + 1 : ℝ) * d k| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ k : Fin (Nat.factorial 3), (k.val + 1 : ℝ) * ((β / 21) * #Q₀.support) := by
          refine sum_le_sum fun k _ ↦ ?_
          rw [abs_mul, abs_of_nonneg (by positivity)]
          exact mul_le_mul_of_nonneg_left (hφ_disc c₀ ⟨σ₀, S₀, k⟩ c).le (by positivity)
      _ = β * #Q.support := by
          rw [← sum_mul, hQ₀_card]
          have hsum21 : ∑ k : Fin (Nat.factorial 3), ((k : ℕ) + 1 : ℝ) = 21 := by
            exact_mod_cast (by decide : ∑ k : Fin (Nat.factorial 3), ((k : ℕ) + 1) = 21)
          rw [hsum21]; ring
  · rw [eq_empty_iff_forall_notMem]
    intro x hx
    obtain ⟨hxQ, hne⟩ := (H.mem_editedOn H' Q.support x).1 hx
    have hnot : ¬N₀ ≤
        (#(canonTriple D.skeleton (Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩)).support : ℝ)
            := by
      rwa [canonTriple_ofFinEmb_eq hxQ, card_support_canonPolyad Q]
    exact hne (by simp [H', hnot])

/-- Deterministic global edit-discrepancy bound for any coupled recoloring witnessing `M`. -/
private theorem approximates3_of_coupled_recoloring [Fintype κ]
    {H H' : Colored3Graph κ V} {C D : TriadicComplex3 V}
    {M : Polyad3 D.skeleton → Matrix κ κ ℝ} {β N₀ g : ℝ}
    (hV : D.skeleton.vertexPart ≤ C.skeleton.vertexPart)
    (f : Fin D.pairColorCount → Fin C.pairColorCount)
    (hf : ∀ p, C.skeleton.pairColors.color p = f (D.skeleton.pairColors.color p))
    (hgap : H.polyadEnergy D.skeleton - H.polyadEnergy C.skeleton ≤ g)
    (hβ : 0 < β) (hN₀_pos : 0 < N₀)
    (hdiag : ∀ Q : Polyad3 D.skeleton, N₀ ≤ (#Q.support : ℝ) →
      ∀ c₀, (H.relativeDensity c₀ (canonPolyad Q) : ℝ) * (1 - M (canonPolyad Q) c₀ c₀) =
        max ((H.relativeDensity c₀ (canonPolyad Q) : ℝ) -
          H.relativeDensity c₀ ((canonPolyad Q).coarsen hV f)) 0)
    (hkeep : ∀ Q : Polyad3 D.skeleton, N₀ ≤ (#Q.support : ℝ) →
      ∀ (S' : Subpolyad3 Q) (c₀ c : κ),
        |(#{x ∈ S'.support | H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩) = c₀ ∧
            H'.color (Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩) = c} : ℝ) -
          M (canonPolyad Q) c₀ c *
            #{x ∈ S'.support | H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩) = c₀}| ≤
          β * #Q.support)
    (hsmall : ∀ Q : Polyad3 D.skeleton, ¬N₀ ≤ (#Q.support : ℝ) → H.editedOn H' Q.support = ∅) :
    H.Approximates3 H' (Fintype.card κ * (√g + β)) := by
  let e₃ : {x : Fin 3 → V // Function.Injective x} → Set.powersetCard V 3 :=
    fun x ↦ Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩
  have hedit_Q (Q : Polyad3 D.skeleton) :
      (#(H.editedOn H' Q.support) : ℝ) ≤
        (∑ c₀, #Q.support *
          |(H.relativeDensity c₀ Q : ℝ) - H.relativeDensity c₀ (Q.coarsen hV f)|) +
          Fintype.card κ * β * #Q.support := by
    by_cases hQ : N₀ ≤ (#Q.support : ℝ)
    · have hQ_ne : Q.support.Nonempty := card_pos.1 (by exact_mod_cast hN₀_pos.trans_le hQ)
      set Q₀ := canonPolyad Q
      have hpart : #(H.editedOn H' Q.support) =
          ∑ c₀ : κ, #{x ∈ Q.support | H.color (e₃ x) = c₀ ∧ H.color (e₃ x) ≠ H'.color (e₃ x)} := by
        rw [editedOn_def]
        exact card_filter_color_fiberwise H Q.support fun s ↦ H.color s ≠ H'.color s
      rw [hpart, Nat.cast_sum]
      have hbound_c₀ (c₀ : κ) :
          (#{x ∈ Q.support | H.color (e₃ x) = c₀ ∧ H.color (e₃ x) ≠ H'.color (e₃ x)} : ℝ) ≤
            #Q.support *
              |(H.relativeDensity c₀ Q : ℝ) - H.relativeDensity c₀ (Q.coarsen hV f)| +
              β * #Q.support := by
        have hkeep_c₀ := hkeep Q hQ (Subpolyad3.ofSubcells Q Q.c₀ Q.c₁ Q.c₂) c₀ c₀
        rw [Subpolyad3.support_ofSubcells_cells] at hkeep_c₀
        let s₀ := {x ∈ Q.support | H.color (e₃ x) = c₀}
        have hsplit : #{x ∈ Q.support | H.color (e₃ x) = c₀ ∧ H.color (e₃ x) ≠ H'.color (e₃ x)} +
            #{x ∈ Q.support | H.color (e₃ x) = c₀ ∧ H'.color (e₃ x) = c₀} = #s₀ := by
          rw [← card_filter_add_card_filter_not (s := s₀) (p := fun x ↦ H'.color (e₃ x) = c₀),
            add_comm]
          congr 1 <;> refine congrArg card (ext fun x ↦ ?_) <;> simp only [s₀, mem_filter]
          · exact and_assoc.symm
          · exact ⟨fun ⟨hx, hc₀, hne⟩ ↦ ⟨⟨hx, hc₀⟩, fun hc' ↦ hne (hc₀.trans hc'.symm)⟩,
              fun ⟨⟨hx, hc₀⟩, hne⟩ ↦ ⟨hx, hc₀, fun hc' ↦ hne (hc'.symm.trans hc₀)⟩⟩
        have hdens : (#s₀ : ℝ) = (H.relativeDensity c₀ Q₀ : ℝ) * #Q.support := by
          rw [relativeDensity_canonPolyad H Q c₀, H.relativeDensity_def]
          exact_mod_cast (H.relDensityOn_mul_card c₀ Q.support).symm
        have hkeep_lo : M Q₀ c₀ c₀ * ((H.relativeDensity c₀ Q₀ : ℝ) * #Q.support) -
            β * #Q.support ≤
            (#{x ∈ Q.support | H.color (e₃ x) = c₀ ∧ H'.color (e₃ x) = c₀} : ℝ) := by
          dsimp only [Q₀, s₀, e₃] at hdens ⊢
          rw [hdens] at hkeep_c₀
          linarith [(abs_le.1 hkeep_c₀).1]
        have hsplitR :
            (#{x ∈ Q.support | H.color (e₃ x) = c₀ ∧ H.color (e₃ x) ≠ H'.color (e₃ x)} : ℝ) +
            (#{x ∈ Q.support | H.color (e₃ x) = c₀ ∧ H'.color (e₃ x) = c₀} : ℝ) =
            (H.relativeDensity c₀ Q₀ : ℝ) * #Q.support := by
          rw [← Nat.cast_add, hsplit, hdens]
        have hdiag_le : (H.relativeDensity c₀ Q₀ : ℝ) * (1 - M Q₀ c₀ c₀) ≤
            |(H.relativeDensity c₀ Q : ℝ) - H.relativeDensity c₀ (Q.coarsen hV f)| := by
          rw [hdiag Q hQ c₀, relativeDensity_canonPolyad H Q c₀,
            relativeDensity_coarsen_canonPolyad hV f hf H hQ_ne c₀]
          exact max_le (le_abs_self _) (abs_nonneg _)
        have hdiag_Q := mul_le_mul_of_nonneg_right hdiag_le (Nat.cast_nonneg (α := ℝ) #Q.support)
        nlinarith
      calc _ ≤ ∑ c₀ : κ, (#Q.support *
              |(H.relativeDensity c₀ Q : ℝ) - H.relativeDensity c₀ (Q.coarsen hV f)| +
              β * #Q.support) := sum_le_sum fun c₀ _ ↦ hbound_c₀ c₀
        _ = (∑ c₀, #Q.support *
              |(H.relativeDensity c₀ Q : ℝ) - H.relativeDensity c₀ (Q.coarsen hV f)|) +
              Fintype.card κ * β * #Q.support := by
            rw [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul]; ring
    · rw [hsmall Q hQ, card_empty, Nat.cast_zero]
      exact add_nonneg (sum_nonneg fun _ _ ↦ mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _))
        (by positivity)
  have hbi : #(H.editedOn H' univ) = ∑ Q : Polyad3 D.skeleton, #(H.editedOn H' Q.support) := by
    rw [← Polyad3.sum_card_inter_support (S := D.skeleton) (H.editedOn H' univ)]
    refine sum_congr rfl fun Q _ ↦ congrArg card (ext fun x ↦ ?_)
    simp only [mem_inter, mem_editedOn, mem_univ, true_and, and_comm]
  have hsumQ : ∑ Q : Polyad3 D.skeleton, (#Q.support : ℝ) = (Fintype.card V).descFactorial 3 := by
    exact_mod_cast Polyad3.sum_card_support_eq_descFactorial D.skeleton
  refine approximates3_of_card_editedOn_univ_le (by positivity) ?_
  calc (#(H.editedOn H' univ) : ℝ)
      = ∑ Q : Polyad3 D.skeleton, (#(H.editedOn H' Q.support) : ℝ) := by exact_mod_cast hbi
    _ ≤ ∑ Q : Polyad3 D.skeleton, ((∑ c₀, #Q.support *
          |(H.relativeDensity c₀ Q : ℝ) - H.relativeDensity c₀ (Q.coarsen hV f)|) +
          Fintype.card κ * β * #Q.support) := sum_le_sum fun Q _ ↦ hedit_Q Q
    _ = (∑ c₀, ∑ Q : Polyad3 D.skeleton, #Q.support *
          |(H.relativeDensity c₀ Q : ℝ) - H.relativeDensity c₀ (Q.coarsen hV f)|) +
          Fintype.card κ * β * (Fintype.card V).descFactorial 3 := by
        rw [sum_add_distrib, sum_comm, ← mul_sum, hsumQ]
    _ ≤ (∑ _c₀ : κ, √g * (Fintype.card V).descFactorial 3) +
          Fintype.card κ * β * (Fintype.card V).descFactorial 3 := by
        gcongr with c₀
        exact H.sum_card_support_mul_abs_relativeDensity_coarsen_le_of_color_eq hV f hf hgap c₀
    _ = Fintype.card κ * (√g + β) * (Fintype.card V).descFactorial 3 := by
        rw [sum_const, card_univ, nsmul_eq_mul]; ring
    _ ≤ Fintype.card κ * (√g + β) * (Fintype.card V : ℝ) ^ 3 := by
        gcongr; exact_mod_cast Nat.descFactorial_le_pow (Fintype.card V) 3

/-- On a large `(η, 1)`-top-regular fine child `Q` of `P`, a coupled recoloring pushes fine
subpolyad counts onto `H.relativeDensity c P` within `|κ| * (η + β) * #Q.support`. -/
private theorem recolored_child_dev_le [Fintype κ]
    {H H' : Colored3Graph κ V} {C D : TriadicComplex3 V}
    {M : Polyad3 D.skeleton → Matrix κ κ ℝ} {η β : ℝ}
    (hV : D.skeleton.vertexPart ≤ C.skeleton.vertexPart)
    (f : Fin D.pairColorCount → Fin C.pairColorCount)
    (hf : ∀ p, C.skeleton.pairColors.color p = f (D.skeleton.pairColors.color p))
    {P : Polyad3 C.skeleton} {Q : Polyad3 D.skeleton} (hQP : Q.coarsen hV f = P)
    (hQ_ne : Q.support.Nonempty) (hQreg : H.IsTopRegularOverPolyad Q η 1)
    (hMmem : M (canonPolyad Q) ∈ Matrix.rowStochastic ℝ κ)
    (hMpush : (fun c₀ ↦ (H.relativeDensity c₀ (canonPolyad Q) : ℝ)) ᵥ* M (canonPolyad Q) =
      (fun c ↦ (H.relativeDensity c ((canonPolyad Q).coarsen hV f) : ℝ)))
    (hsub : ∀ (S' : Subpolyad3 Q) (c₀ c : κ),
      |(#{x ∈ S'.support | H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩) = c₀ ∧
          H'.color (Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩) = c} : ℝ) -
        M (canonPolyad Q) c₀ c *
          #{x ∈ S'.support | H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩) = c₀}| ≤
        β * #Q.support)
    (c : κ) (S' : Subpolyad3 Q) :
    |(H'.relDensityOn c S'.support : ℝ) - H.relativeDensity c P| * #S'.support ≤
      Fintype.card κ * (η + β) * #Q.support := by
  set Q₀ := canonPolyad Q
  let a (c₀ : κ) : ℝ := #{x ∈ S'.support |
    H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩) = c₀ ∧
    H'.color (Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩) = c}
  let b (c₀ : κ) : ℝ := #{x ∈ S'.support |
    H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩) = c₀}
  have hnew : (H'.relDensityOn c S'.support : ℝ) * #S'.support = ∑ c₀, a c₀ := by
    have hmul : (H'.relDensityOn c S'.support : ℝ) * #S'.support =
        (#{x ∈ S'.support | H'.color (Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩) = c} : ℝ)
            := by
      exact_mod_cast H'.relDensityOn_mul_card c S'.support
    rw [hmul, card_filter_color_fiberwise H S'.support fun s ↦ H'.color s = c, Nat.cast_sum]
  have hpush_c : ∑ c₀, (H.relativeDensity c₀ Q₀ : ℝ) * M Q₀ c₀ c =
      H.relativeDensity c (Q₀.coarsen hV f) := by
    simpa [Matrix.vecMul, dotProduct] using congrFun hMpush c
  have htarget : (H.relativeDensity c P : ℝ) * #S'.support =
      ∑ c₀, M Q₀ c₀ c * ((H.relativeDensity c₀ Q : ℝ) * #S'.support) := by
    rw [← hQP, ← relativeDensity_coarsen_canonPolyad hV f hf H hQ_ne c, ← hpush_c, sum_mul]
    exact sum_congr rfl fun c₀ _ ↦ by rw [relativeDensity_canonPolyad H Q c₀]; ring
  rw [← abs_of_nonneg (Nat.cast_nonneg (α := ℝ) #S'.support), ← abs_mul, sub_mul,
    hnew, htarget, ← sum_sub_distrib]
  calc |∑ c₀, (a c₀ - M Q₀ c₀ c * ((H.relativeDensity c₀ Q : ℝ) * #S'.support))|
      ≤ ∑ c₀, |a c₀ - M Q₀ c₀ c * ((H.relativeDensity c₀ Q : ℝ) * #S'.support)| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ _c₀ : κ, (η + β) * #Q.support := by
        refine sum_le_sum fun c₀ _ ↦ ?_
        have hb : b c₀ = (H.relDensityOn c₀ S'.support : ℝ) * #S'.support := by
          dsimp only [b]; exact_mod_cast (H.relDensityOn_mul_card c₀ S'.support).symm
        have hM0 : 0 ≤ M Q₀ c₀ c := Matrix.nonneg_of_mem_rowStochastic hMmem
        have hM1 : M Q₀ c₀ c ≤ 1 := Matrix.le_one_of_mem_rowStochastic hMmem
        have hreg_c₀ : |(H.relDensityOn c₀ S'.support : ℝ) - H.relativeDensity c₀ Q| *
            #S'.support ≤ η * #Q.support := by
          simpa only [Subpolyad3.unionSupport_unique] using
            hQreg.abs_relDensityOn_unionSupport_sub_mul_card_le_of_card_le c₀ (by simp)
              (fun _ : Fin 1 ↦ S')
        have hdiff : a c₀ - M Q₀ c₀ c * ((H.relativeDensity c₀ Q : ℝ) * #S'.support) =
            (a c₀ - M Q₀ c₀ c * b c₀) +
            M Q₀ c₀ c * (((H.relDensityOn c₀ S'.support : ℝ) - H.relativeDensity c₀ Q) *
              #S'.support) := by rw [hb]; ring
        have htri : |a c₀ - M Q₀ c₀ c * ((H.relativeDensity c₀ Q : ℝ) * #S'.support)| ≤
            |a c₀ - M Q₀ c₀ c * b c₀| +
            M Q₀ c₀ c * (|(H.relDensityOn c₀ S'.support : ℝ) - H.relativeDensity c₀ Q| *
              #S'.support) := by
          rw [hdiff]
          refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
          rw [abs_mul, abs_of_nonneg hM0, abs_mul, Nat.abs_cast]
        have hM_term := (mul_le_mul hM1 hreg_c₀
          (mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _)) (by norm_num)).trans_eq (one_mul _)
        linarith [hsub S' c₀ c]
    _ = Fintype.card κ * (η + β) * #Q.support := by
        rw [sum_const, card_univ, nsmul_eq_mul]; ring

/-- **Coupled triple recoloring across a small polyad energy gap.** Let `D` refine `C` along a
pair-color projection `f` recovering `C.skeleton.pairColors.color`, with both complexes selecting
polyad decompositions, and suppose `H` is `(η, 1)`-top-regular over all polyads of `D` outside a
`μ`-proportion of the injective triples, with polyad energy gap from `C` to `D` at most `g`. For
`0 ≤ η` and `0 < δ, β, θ`, when `N₀` satisfies the Hoeffding support bound
`221 (3 |V|² + |κ| + 7) ≤ β² N₀` and `2 (|κ| (η + β) + θ) ≤ δ²`, there is a coloring `H'` within
edit discrepancy `|κ| (√g + β)` of `H` that is `(δ, 1)`-top-regular over all polyads of `C` outside
a proportion of the injective triples bounded by
`(μ + card (Polyad3 D.skeleton) * N₀ / |V|.descFactorial 3) / θ`. -/
theorem TopRegularOverMostPolyads.exists_approximates3_of_polyadEnergy_sub_le [Fintype κ]
    {H : Colored3Graph κ V} {C D : TriadicComplex3 V} {η μ δ β θ N₀ g : ℝ}
    (h : H.TopRegularOverMostPolyads D η μ 1)
    (hC : C.IsPolyadDecomposition) (hD : D.IsPolyadDecomposition)
    (hV : D.skeleton.vertexPart ≤ C.skeleton.vertexPart)
    (f : Fin D.pairColorCount → Fin C.pairColorCount)
    (hf : ∀ p, C.skeleton.pairColors.color p = f (D.skeleton.pairColors.color p))
    (hgap : H.polyadEnergy D.skeleton - H.polyadEnergy C.skeleton ≤ g)
    (hη : 0 ≤ η) (hδ : 0 < δ) (hβ : 0 < β) (hθ : 0 < θ)
    (hN₀ : 221 * (3 * (Fintype.card V : ℝ) ^ 2 + Fintype.card κ + 7) ≤ β ^ 2 * N₀)
    (htol : 2 * (Fintype.card κ * (η + β) + θ) ≤ δ ^ 2) :
    ∃ H' : Colored3Graph κ V,
      H.Approximates3 H' (Fintype.card κ * (√g + β)) ∧
      H'.TopRegularOverMostPolyads C δ
        ((μ + Fintype.card (Polyad3 D.skeleton) * N₀ /
          (Fintype.card V).descFactorial 3) / θ) 1 := by
  classical
  have hN₀_pos : 0 < N₀ := pos_of_support_lower_bound hN₀
  obtain ⟨H', M, hbig, hsmall⟩ :=
    exists_coupled_recoloring (H := H) (C := C) (D := D) hV f hf hβ hN₀
  refine ⟨H', approximates3_of_coupled_recoloring hV f hf hgap hβ hN₀_pos
    (fun Q hQ ↦ (hbig Q hQ).2.2.1) (fun Q hQ ↦ (hbig Q hQ).2.2.2) hsmall, ?_⟩
  let Good : Polyad3 D.skeleton → Prop := fun Q ↦
    N₀ ≤ (#Q.support : ℝ) ∧ H.IsTopRegularOverPolyad Q η 1
  have hbad : ∑ Q : Polyad3 D.skeleton with True ∧ ¬Good Q, (#Q.support : ℝ) ≤
      μ * (Fintype.card V).descFactorial 3 + Fintype.card (Polyad3 D.skeleton) * N₀ := by
    let s₁ := univ.filter fun Q : Polyad3 D.skeleton ↦ ¬N₀ ≤ (#Q.support : ℝ)
    let s₂ := univ.filter fun Q : Polyad3 D.skeleton ↦ ¬H.IsTopRegularOverPolyad Q η 1
    have hunion : (univ.filter fun Q : Polyad3 D.skeleton ↦ True ∧ ¬Good Q) = s₁ ∪ s₂ := by
      ext Q; simp only [Good, s₁, s₂, mem_union, mem_filter, mem_univ, true_and, not_and]
      tauto
    have hsmall_sum : ∑ Q ∈ s₁, (#Q.support : ℝ) ≤ Fintype.card (Polyad3 D.skeleton) * N₀ := by
      calc ∑ Q ∈ s₁, (#Q.support : ℝ)
          ≤ ∑ _Q ∈ s₁, N₀ := sum_le_sum fun Q hQ ↦ (not_le.1 (mem_filter.1 hQ).2).le
        _ ≤ ∑ _Q : Polyad3 D.skeleton, N₀ :=
            sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ ↦ hN₀_pos.le
        _ = Fintype.card (Polyad3 D.skeleton) * N₀ := by rw [sum_const, card_univ, nsmul_eq_mul]
    have hirr_D : ∑ Q ∈ s₂, (#Q.support : ℝ) ≤ μ * (Fintype.card V).descFactorial 3 := by
      simpa only [s₂] using h.sum_card_support_univ_le hD
    have hinter : 0 ≤ ∑ Q ∈ s₁ ∩ s₂, (#Q.support : ℝ) := sum_nonneg fun _ _ ↦ Nat.cast_nonneg _
    rw [hunion]
    linarith [sum_union_inter (s₁ := s₁) (s₂ := s₂) (f := fun Q ↦ (#Q.support : ℝ))]
  have hε' : 0 ≤ (μ + Fintype.card (Polyad3 D.skeleton) * N₀ /
      (Fintype.card V).descFactorial 3) / θ := by
    have := h.nonneg; positivity
  refine topRegularOverMostPolyads_of_good_children (H := H) hC hV f hf (fun _ ↦ True) Good
    (τ := Fintype.card κ * (η + β)) (repMass := 0)
    (badMass := μ * (Fintype.card V).descFactorial 3 + Fintype.card (Polyad3 D.skeleton) * N₀)
    hδ (by positivity) hθ hε' htol ?_ (by simp) (by convert hbad) (fun hdesc ↦ ?_)
  · intro P Q _ hQP hGQ c S'
    have hQ_ne : Q.support.Nonempty := card_pos.1 (by exact_mod_cast hN₀_pos.trans_le hGQ.1)
    obtain ⟨hMmem, hMpush, -, hsub⟩ := hbig Q hGQ.1
    rw [abs_mul, Nat.abs_cast]
    exact recolored_child_dev_le hV f hf hQP hQ_ne hGQ.2 hMmem hMpush hsub c S'
  · have hdescR : (0 : ℝ) < (Fintype.card V).descFactorial 3 := Nat.cast_pos.2 hdesc
    rw [zero_add, div_le_iff₀ hθ]
    exact le_of_eq (by field_simp [hθ.ne', hdescR.ne'])

/-- **Scheduled coupled recoloring across a small polyad energy gap.** Let `D` refine `C` along a
pair-color projection `f` recovering `C.skeleton.pairColors.color`, with both complexes selecting
polyad decompositions, let `n = C.complexity`, and let `ε`, `δ n` and `μ n` be positive. Suppose
that `H` is rank-one top-regular over all polyads of `D` at tolerance `recoloringTolerance q δ r n`
outside a `recoloringMass δ μ r n`-proportion of the injective triples, where `q` is the number of
top colors, and that the polyad energy gap from `C` to `D` is at most `(ε / (2 (q + 1)))²`. On a
host of size at least `recoloringHostBound q ε δ μ r K P`, where `n ≤ K` and `D` has at most `P`
polyads, there is a coloring `H'` within edit discrepancy `ε` of `H` that is
`(δ n, r n)`-top-regular over `C` outside a `μ n`-proportion of the injective triples. -/
theorem TopRegularOverMostPolyads.exists_approximates3_of_recoloringHostBound_le [Fintype κ]
    {H : Colored3Graph κ V} {C D : TriadicComplex3 V} {ε : ℝ} {δ μ : ℕ → ℝ} {r : ℕ → ℕ}
    (h : H.TopRegularOverMostPolyads D (recoloringTolerance (Fintype.card κ) δ r C.complexity)
      (recoloringMass δ μ r C.complexity) 1)
    (hC : C.IsPolyadDecomposition) (hD : D.IsPolyadDecomposition)
    (hV : D.skeleton.vertexPart ≤ C.skeleton.vertexPart)
    (f : Fin D.pairColorCount → Fin C.pairColorCount)
    (hf : ∀ p, C.skeleton.pairColors.color p = f (D.skeleton.pairColors.color p))
    (hgap : H.polyadEnergy D.skeleton - H.polyadEnergy C.skeleton ≤
      (ε / (2 * ((Fintype.card κ : ℝ) + 1))) ^ 2)
    (hε : 0 < ε) (hδ : 0 < δ C.complexity) (hμ : 0 < μ C.complexity) {K P : ℕ}
    (hK : C.complexity ≤ K) (hP : Fintype.card (Polyad3 D.skeleton) ≤ P)
    (hcard : recoloringHostBound (Fintype.card κ) ε δ μ r K P ≤ Fintype.card V) :
    ∃ H' : Colored3Graph κ V, H.Approximates3 H' ε ∧
      H'.TopRegularOverMostPolyads C (δ C.complexity) (μ C.complexity) (r C.complexity) := by
  set q := Fintype.card κ
  set n := C.complexity
  set γ : ℝ := ε / (2 * ((q : ℝ) + 1))
  set δ₁ : ℝ := (δ n) ^ 2 / (2 : ℝ) ^ r n
  set θ : ℝ := δ₁ ^ 2 / 4
  set β : ℝ := min γ (recoloringTolerance q δ r n)
  have hγ : 0 < γ := by positivity
  have hδ₁ : 0 < δ₁ := by positivity
  have hθ : 0 < θ := by positivity
  have hη : 0 < recoloringTolerance q δ r n := recoloringTolerance_pos q r hδ
  have hμ' : 0 < recoloringMass δ μ r n := recoloringMass_pos r hδ hμ
  have hβ : 0 < β := lt_min hγ hη
  -- The host is large enough for the Hoeffding support bound at complexity `n ≤ K`.
  rw [recoloringHostBound_def] at hcard
  have hv4 : 4 ≤ Fintype.card V := (le_max_left _ _).trans hcard
  have hv_sup : ⌊4 * (P : ℝ) * 221 * ((q : ℝ) + 10) / (β ^ 2 * recoloringMass δ μ r n)⌋₊ + 1 ≤
      Fintype.card V :=
    (le_sup (f := fun k ↦ ⌊4 * (P : ℝ) * 221 * ((q : ℝ) + 10) /
      ((min γ (recoloringTolerance q δ r k)) ^ 2 * recoloringMass δ μ r k)⌋₊ + 1)
      (mem_range.2 (Nat.lt_succ_of_le hK))).trans ((le_max_right _ _).trans hcard)
  have hv_real : 4 * (P : ℝ) * 221 * ((q : ℝ) + 10) / (β ^ 2 * recoloringMass δ μ r n) <
      Fintype.card V :=
    (Nat.lt_floor_add_one _).trans_le (by exact_mod_cast hv_sup)
  set N₀ : ℝ := 221 * (3 * (Fintype.card V : ℝ) ^ 2 + q + 7) / β ^ 2
  have hN₀ : 221 * (3 * (Fintype.card V : ℝ) ^ 2 + q + 7) ≤ β ^ 2 * N₀ := by
    rw [mul_div_cancel₀ _ (pow_ne_zero 2 hβ.ne')]
  have htol : 2 * ((q : ℝ) * (recoloringTolerance q δ r n + β) + θ) ≤ δ₁ ^ 2 := by
    have hqη : (q : ℝ) * (recoloringTolerance q δ r n + β) ≤ δ₁ ^ 2 / 4 :=
      mul_add_le_of_div_two_add_one q (by positivity)
        (by rw [recoloringTolerance_def, div_div]; congr 1; ring) (min_le_right _ _)
    dsimp only [θ]
    linarith
  -- Recolor at rank one, then amplify the rank.
  obtain ⟨H', happrox, hreg₁⟩ :=
    h.exists_approximates3_of_polyadEnergy_sub_le hC hD hV f hf hgap hη.le hδ₁ hβ hθ hN₀ htol
  refine ⟨H', happrox.mono ?_, (hreg₁.mono le_rfl ?_ le_rfl).of_rank_one_div_pow hδ⟩
  · rw [Real.sqrt_sq hγ.le]
    exact mul_add_le_of_div_two_add_one q hε.le rfl (min_le_left _ _)
  · have hsmall := small_polyad_mass_le hv4 (by exact_mod_cast hP) (Nat.cast_nonneg _) hβ hμ'
      hv_real
    rw [div_le_iff₀ hθ]
    have : recoloringMass δ μ r n + recoloringMass δ μ r n = μ n * θ := by
      rw [recoloringMass_def]; ring
    linarith

/-- Discrete palette refinement: giving every ordered distinct pair its own pair color yields a
triadic complex over `S.vertexPart` with at most `|V|²` pair colors whose polyads each have
support cardinality at most `1`, so every coloring is top-regular over every polyad. -/
private theorem exists_discrete_topRegularOverMostPolyads {κ₂ : Type*}
    (H : Colored3Graph κ V) (S : PairSkeleton3 κ₂ V) {δ μ : ℕ → ℝ}
    (hδ : ∀ n, 0 < δ n) (hμ : ∀ n, 0 < μ n) (r : ℕ → ℕ) :
    ∃ (C : TriadicComplex3 V) (π : Fin C.pairColorCount → κ₂),
      C.pairColorCount ≤ Fintype.card V ^ 2 ∧
      C.skeleton.vertexPart = S.vertexPart ∧
      (∀ p, π (C.skeleton.pairColors.color p) = S.pairColors.color p) ∧
      (∀ c, π (C.skeleton.pairColors.rev c) = S.pairColors.rev (π c)) ∧
      C.polyads = univ ∧
      H.TopRegularOverMostPolyads C (δ C.complexity) (μ C.complexity) (r C.complexity) := by
  let discrete : PairColorSystem {p : V × V // p.1 ≠ p.2} V :=
    ⟨id, fun p ↦ ⟨p.val.swap, p.property.symm⟩, fun ⟨⟨_, _⟩, _⟩ ↦ rfl, fun _ ↦ rfl⟩
  let e := Fintype.equivFin {p : V × V // p.1 ≠ p.2}
  let C : TriadicComplex3 V :=
    ⟨Fintype.card {p : V × V // p.1 ≠ p.2}, ⟨S.vertexPart, discrete.relabel e⟩, univ⟩
  let π : Fin C.pairColorCount → κ₂ := fun c ↦ S.pairColors.color (e.symm c)
  refine ⟨C, π, (Fintype.card_subtype_le _).trans_eq (by rw [Fintype.card_prod, sq]), rfl,
    fun p ↦ by simp [C, π, discrete], fun c ↦ by simp [C, π, discrete, S.pairColors.color_rev],
    rfl, topRegularOverMostPolyads_of_forall (fun P _ ↦ ?_) (hμ C.complexity).le⟩
  refine H.isTopRegularOverPolyad_of_card_support_le_one P (r C.complexity) ?_ (hδ C.complexity)
  refine card_le_one.2 fun x hx y hy ↦ Subtype.ext <| funext fun i ↦ ?_
  have h₀₁ : coordPair x 0 1 (by decide) = coordPair y 0 1 (by decide) :=
    e.injective (by
      have h1 := ((P.mem_pairSupport₀₁ _).1 (coordPair_mem_pairSupport₀₁ hx)).2.2
      have h2 := ((P.mem_pairSupport₀₁ _).1 (coordPair_mem_pairSupport₀₁ hy)).2.2
      simpa [C, discrete] using h1.trans h2.symm)
  have h₀₂ : coordPair x 0 2 (by decide) = coordPair y 0 2 (by decide) :=
    e.injective (by
      have h1 := ((P.mem_pairSupport₀₂ _).1 (coordPair_mem_pairSupport₀₂ hx)).2.2
      have h2 := ((P.mem_pairSupport₀₂ _).1 (coordPair_mem_pairSupport₀₂ hy)).2.2
      simpa [C, discrete] using h1.trans h2.symm)
  have h₀₁' := congrArg (fun p : {p : V × V // p.1 ≠ p.2} ↦ (p : V × V)) h₀₁
  have h₀₂' := congrArg (fun p : {p : V × V // p.1 ≠ p.2} ↦ (p : V × V)) h₀₂
  simp only [coe_coordPair, Prod.mk.injEq] at h₀₁' h₀₂'
  match i with
  | ⟨0, _⟩ => exact h₀₁'.1
  | ⟨1, _⟩ => exact h₀₁'.2
  | ⟨2, _⟩ => exact h₀₂'.2

/-- **Scheduled strong top-regular approximation.** Let `ε > 0`, let `δ μ : ℕ → ℝ` be positive
schedules, and let `r : ℕ → ℕ` be a rank schedule. On every finite vertex set `V`, every lower
skeleton `S` admits a palette refinement `C` with the vertex cells of `S`, all its polyads, and
`C.pairColorCount` bounded independently of `V` by
`topRegularApproximationPaletteBound (Nat.card κ) #S.vertexPart.parts ε δ μ r (Fintype.card κ₂)`,
together with an `ε`-close coloring `H'` that is `(δ C.complexity, r C.complexity)`-top-regular
off a `μ C.complexity`-proportion of the injective triples. -/
theorem exists_approximates3_topRegularOverMostPolyads [Finite κ] [Fintype κ₂]
    (H : Colored3Graph κ V) (S : PairSkeleton3 κ₂ V) {ε : ℝ} (hε : 0 < ε)
    {δ μ : ℕ → ℝ} (hδ : ∀ n, 0 < δ n) (hμ : ∀ n, 0 < μ n) (r : ℕ → ℕ) :
    ∃ (C : TriadicComplex3 V) (π : Fin C.pairColorCount → κ₂) (H' : Colored3Graph κ V),
      C.pairColorCount ≤ topRegularApproximationPaletteBound (Nat.card κ)
        #S.vertexPart.parts ε δ μ r (Fintype.card κ₂) ∧
      C.skeleton.vertexPart = S.vertexPart ∧
      (∀ p, π (C.skeleton.pairColors.color p) = S.pairColors.color p) ∧
      (∀ c, π (C.skeleton.pairColors.rev c) = S.pairColors.rev (π c)) ∧
      C.polyads = univ ∧
      H.Approximates3 H' ε ∧
      H'.TopRegularOverMostPolyads C (δ C.complexity) (μ C.complexity) (r C.complexity) := by
  have := Fintype.ofFinite κ
  rw [Nat.card_eq_fintype_card]
  set q := Fintype.card κ
  set t := #S.vertexPart.parts
  set η := recoloringTolerance q δ r
  set μ' := recoloringMass δ μ r
  set γ : ℝ := ε / (2 * ((q : ℝ) + 1))
  set M := strongTopRegularityBound t (γ ^ 2) η μ' (fun _ ↦ 1) (Fintype.card κ₂)
  set M' := strongTopRegularityStep t η μ' (fun _ ↦ 1) M
  set N := recoloringHostBound q ε δ μ r (t + M + t ^ 3 * M ^ 3) (t ^ 3 * M' ^ 3)
  have hbound : topRegularApproximationPaletteBound q t ε δ μ r (Fintype.card κ₂) =
      max M (N ^ 2) := by
    rw [topRegularApproximationPaletteBound_def]
  rw [hbound]
  by_cases hcard : N ≤ Fintype.card V
  · obtain ⟨C, D, π, f, hCcard, hDcard, hCV, hDV, hπ, hrev, hf, -, hCpol, hDpol, hDreg, hgap⟩ :=
      H.exists_strong_topRegularOverMostPolyads S (g := γ ^ 2) (η := η) (μ := μ')
        (by positivity) (fun n ↦ recoloringTolerance_pos q r (hδ n))
        (fun n ↦ recoloringMass_pos r (hδ n) (hμ n)) (fun _ ↦ 1)
    have hCcomp : C.complexity ≤ t + M + t ^ 3 * M ^ 3 :=
      C.complexity_le.trans (by rw [hCV]; gcongr)
    have hDM' : D.pairColorCount ≤ M' :=
      hDcard.trans (topRegularRefinementBound_le_strongTopRegularityStep η μ' (fun _ ↦ 1) hCcard
        hCcomp)
    have hDpoly : Fintype.card (Polyad3 D.skeleton) ≤ t ^ 3 * M' ^ 3 :=
      (card_polyad3_le D.skeleton).trans (by rw [hDV, Fintype.card_fin]; gcongr)
    obtain ⟨H', happrox, hreg⟩ := hDreg.exists_approximates3_of_recoloringHostBound_le
      (C.isPolyadDecomposition_of_polyads_eq_univ hCpol)
      (D.isPolyadDecomposition_of_polyads_eq_univ hDpol) (hDV.trans hCV.symm).le f
      (fun p ↦ (hf p).symm) hgap hε (hδ _) (hμ _) hCcomp hDpoly hcard
    exact ⟨C, π, H', hCcard.trans (le_max_left _ _), hCV, hπ, hrev, hCpol, happrox, hreg⟩
  · obtain ⟨C, π, hCcard, hCV, hπ, hrev, hCpol, hreg⟩ :=
      exists_discrete_topRegularOverMostPolyads H S hδ hμ r
    refine ⟨C, π, H, (hCcard.trans (Nat.pow_le_pow_left (not_le.1 hcard).le 2)).trans
      (le_max_right _ _), hCV, hπ, hrev, hCpol, H.approximates3_self hε.le, hreg⟩

end EnergyGapRecoloring

end Colored3Graph

end TauCeti
