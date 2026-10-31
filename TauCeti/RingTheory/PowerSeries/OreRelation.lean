/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Data.Fintype.Card
import TauCeti.RingTheory.Algebraic.LinearIndependent
import TauCeti.RingTheory.PowerSeries.Cartier

/-!
# Ore relations for algebraic power series over a finite field

Let `K` be a finite field with `q` elements and let `f ∈ K⟦X⟧` be algebraic over `K[X]`. Then `f`
satisfies an *Ore relation* `∑_{i ≤ m} aᵢ • f ^ q ^ i = 0` with polynomial coefficients
`aᵢ ∈ K[X]` and `a₀ ≠ 0` (`PowerSeries.exists_ore_relation`).

Dividing an Ore relation by `a₀` writes `f` in terms of its own iterated Frobenius powers; this
is how Christol's theorem shows that the Cartier operators preserve a finite set containing `f`,
so that the coefficient sequence of `f` is `q`-automatic.

## References

* G. Christol, T. Kamae, M. Mendès France, G. Rauzy, *Suites algébriques, automates et
  substitutions*, Bull. Soc. Math. France 108 (1980), Section 7.
* B. Adamczewski, R. Yassawi, *A note on Christol's theorem*, Section 1.
-/

public section

open Polynomial

namespace PowerSeries

variable {K : Type*} [Field K] [Fintype K]

/-- The descent step: if a relation `∑_{i ≤ n} aᵢ • f ^ q ^ i = 0` has `a₀ = 0` and
`a_{j + 1} ≠ 0`, a Cartier operator turns it into a relation `∑_{i < n} bᵢ • f ^ q ^ i = 0` with
`b_j ≠ 0` and `bᵢ = 0` whenever `a_{i + 1} = 0`. -/
private lemma exists_relation_of_relation_of_coeff_zero_eq_zero {f : K⟦X⟧} {n j : ℕ}
    {a : ℕ → K[X]} (h0 : a 0 = 0) (hj : a (j + 1) ≠ 0)
    (hrel : ∑ i ∈ Finset.range (n + 1), a i • f ^ (Fintype.card K ^ i) = 0) :
    ∃ b : ℕ → K[X], (∀ i, a (i + 1) = 0 → b i = 0) ∧ b j ≠ 0 ∧
      ∑ i ∈ Finset.range n, b i • f ^ (Fintype.card K ^ i) = 0 := by
  set q := Fintype.card K
  -- Since `a_{j + 1} = ∑_{r < q} X ^ r * (Λ_r a_{j + 1}) ^ q`, some `Λ_r a_{j + 1}` is nonzero.
  obtain ⟨r, hr, hne⟩ : ∃ r < q, cartier K q r (a (j + 1) : K⟦X⟧) ≠ 0 := by
    by_contra! h
    refine hj (Polynomial.coe_eq_zero_iff.mp ?_)
    rw [eq_sum_X_pow_mul_cartier_pow (a (j + 1) : K⟦X⟧)]
    refine Finset.sum_eq_zero fun r hr' ↦ ?_
    rw [h r (Finset.mem_range.mp hr'), zero_pow Fintype.card_ne_zero, mul_zero]
  choose b hb using fun i ↦ exists_cartier_coe_polynomial_eq q r Fintype.card_ne_zero (a (i + 1))
  refine ⟨b, fun i hi ↦ ?_, fun h ↦ hne ?_, ?_⟩
  · rw [← Polynomial.coe_eq_zero_iff, ← (hb i).2, hi, Polynomial.coe_zero, map_zero]
  · rw [(hb j).2, h, Polynomial.coe_zero]
  · rw [Finset.sum_range_succ', h0, zero_smul, add_zero] at hrel
    rw [← map_zero (cartier K q r), ← hrel, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    -- A polynomial acts on power series by multiplication by its coercion.
    simp only [Algebra.smul_def, algebraMap_apply', Algebra.algebraMap_self, map_id, id_eq]
    rw [pow_succ, pow_mul, mul_comm (a (i + 1) : K⟦X⟧), cartier_pow_card_mul r hr, (hb i).2,
      mul_comm]

/-- **Ore relations for algebraic power series.** Over a finite field `K` with `q` elements, a
power series `f` algebraic over `K[X]` satisfies a relation `∑_{i ≤ m} aᵢ • f ^ q ^ i = 0` with
coefficients `aᵢ ∈ K[X]` and `a₀ ≠ 0`. -/
theorem exists_ore_relation {f : K⟦X⟧} (hf : IsAlgebraic K[X] f) :
    ∃ (m : ℕ) (a : ℕ → K[X]), a 0 ≠ 0 ∧
      ∑ i ∈ Finset.range (m + 1), a i • f ^ (Fintype.card K ^ i) = 0 := by
  classical
  set q := Fintype.card K
  -- The powers `f ^ q ^ i` satisfy some nontrivial `K[X]`-linear relation because `f` is
  -- algebraic. If the least index `j` with `a_j ≠ 0` is positive, some Cartier operator
  -- `Λ_r = cartier K q r` with `r < q` does not vanish on `a_j`, and since
  -- `Λ_r (aᵢ • f ^ q ^ i) = Λ_r aᵢ • f ^ q ^ (i - 1)` for `i ≥ 1`, applying `Λ_r` gives a relation
  -- whose least nonzero index is `j - 1`. Descending to `j = 0` gives the Ore relation.
  suffices H : ∀ j n (a : ℕ → K[X]), (∀ i < j, a i = 0) → a j ≠ 0 → j ≤ n →
      ∑ i ∈ Finset.range (n + 1), a i • f ^ (q ^ i) = 0 →
      ∃ (m : ℕ) (a : ℕ → K[X]), a 0 ≠ 0 ∧ ∑ i ∈ Finset.range (m + 1), a i • f ^ (q ^ i) = 0 by
    -- Some nontrivial relation among `f, f ^ q, …, f ^ q ^ d` exists since `f` is algebraic.
    obtain ⟨d, hd⟩ := hf.exists_card_le_of_linearIndependent_pow
    obtain ⟨g, hg, i₀, hi₀⟩ := Fintype.not_linearIndependent_iff.mp fun h ↦
      (Nat.lt_succ_self d).not_ge <| (Fintype.card_fin (d + 1)).symm.trans_le <|
        hd (fun i : Fin (d + 1) ↦ q ^ (i : ℕ)) h
    set a : ℕ → K[X] := fun i ↦ if h : i < d + 1 then g ⟨i, h⟩ else 0 with ha_def
    have ha : ∃ i, a i ≠ 0 := ⟨i₀, by simpa [ha_def, Fin.is_le] using hi₀⟩
    have hle : Nat.find ha ≤ d := by
      by_contra! h
      exact Nat.find_spec ha (dite_eq_right_iff.mpr fun h' ↦ absurd h' (by omega))
    refine H (Nat.find ha) d a (fun i hi ↦ not_not.mp (Nat.find_min ha hi)) (Nat.find_spec ha)
      hle ?_
    rw [← Fin.sum_univ_eq_sum_range (fun i ↦ a i • f ^ (q ^ i))]
    simpa [ha_def, Fin.is_le] using hg
  intro j
  induction j with
  | zero => exact fun n a _ ha0 _ hrel ↦ ⟨n, a, ha0, hrel⟩
  | succ j ih =>
    intro n a hlt hj hjn hrel
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    obtain ⟨b, hb0, hbj, hbrel⟩ :=
      exists_relation_of_relation_of_coeff_zero_eq_zero (hlt 0 j.succ_pos) hj hrel
    exact ih n b (fun i hi ↦ hb0 i (hlt _ (by omega))) hbj (by omega) hbrel

end PowerSeries
