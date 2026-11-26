/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import TauCeti.Dynamics.MarkoffHurwitz.Simplex
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Accelerated projective Markoff–Hurwitz branches

For `n = d + 2`, the unaccelerated Markoff–Hurwitz linear generators `γ_j` (`j : Fin (d + 1)`,
implemented as `TauCeti.MarkoffHurwitz.hurwitzGen`) act on homogeneous coordinates
`y : Fin (d + 2) → ℝ` by deleting `y_j` and appending the sum of the remaining `d + 1` coordinates
(including `y_{d+1}`). Accelerating runs of the top generator `γ_d` yields the countable alphabet
`a = (A, j) : ℕ × Fin d` of linear maps `γ_d^A ∘ γ_j` (`TauCeti.MarkoffHurwitz.branchLinearMap`),
whose projective action on `orderedSimplex d` has denominator
`branchDenom a x = 1 + (A + 1) (1 - x_j)`, rational map `branchMap a x`, and roof delay
`branchDelay a x = log (branchDenom a x)`.

This file establishes the algebraic and analytic API of the accelerated branches:
* preservation of `orderedConeHyperplane d` and `orderedCone d` by `hurwitzGen` and
  `branchLinearMap`, preservation and one-step unique recovery of `hurwitzGen` on
  `strictOrderedCone d`, and the homogeneous cocycle relation;
* invariance `MapsTo (branchMap a) (orderedSimplex d) (orderedSimplex d)` and smoothness
  `ContDiffOn ℝ n` of `branchMap a` and `branchDelay a` on `{x | 0 < branchDenom a x}`;
* sharp enclosures `(A + 3) / 2 ≤ branchDenom a x ≤ A + 2` and
  `log (3 / 2) ≤ branchDelay a x ≤ log (A + 2)` on `orderedSimplex d`;
* exact Fréchet derivative of `branchDelay a` and uniform bound
  `‖fderivWithin ℝ (branchDelay a) (orderedSimplex d) x‖ < 2`;
* positive-base complex weight identities `(branchDenom a x : ℂ) ^ (-s) =
  Complex.exp (-s * branchDelay a x)` and
  `‖(branchDenom a x : ℂ) ^ (-s)‖ = branchDenom a x ^ (-s.re)`.

## References

* A. Gamburd, M. Magee, and R. Ronan, *An asymptotic formula for integer points on
  Markoff–Hurwitz varieties*, Annals of Mathematics 190 (2019), 751–809, p. 756 (footnote 5),
  Lemma 33, and (4.3)–(4.7).
-/

public noncomputable section

open Set Topology

namespace TauCeti.MarkoffHurwitz

/-! ### Unaccelerated and accelerated homogeneous linear generators -/

/-- The `j`-th unaccelerated Markoff–Hurwitz linear generator `γ_j` on `Fin (d + 2) → ℝ`: delete
coordinate `Fin.castSucc j` and append the sum of the remaining `d + 1` coordinates
(Gamburd–Magee–Ronan 2019, (1.6) and §4.1). -/
def hurwitzGen {d : ℕ} (j : Fin (d + 1)) : (Fin (d + 2) → ℝ) →ₗ[ℝ] (Fin (d + 2) → ℝ) where
  toFun y := Fin.snoc (fun k : Fin (d + 1) => y ((Fin.castSucc j).succAbove k))
    (∑ k : Fin (d + 1), y ((Fin.castSucc j).succAbove k))
  map_add' x y := by
    ext i; refine Fin.lastCases ?_ (fun _ => ?_) i <;> simp [Finset.sum_add_distrib]
  map_smul' c x := by
    ext i; refine Fin.lastCases ?_ (fun _ => ?_) i <;> simp [Finset.mul_sum]

/-- First `d + 1` coordinates of `hurwitzGen j y`. -/
@[simp]
theorem hurwitzGen_castSucc {d : ℕ} (j k : Fin (d + 1)) (y : Fin (d + 2) → ℝ) :
    hurwitzGen j y (Fin.castSucc k) = y ((Fin.castSucc j).succAbove k) := by simp [hurwitzGen]

/-- Last coordinate of `hurwitzGen j y`. -/
@[simp]
theorem hurwitzGen_last {d : ℕ} (j : Fin (d + 1)) (y : Fin (d + 2) → ℝ) :
    hurwitzGen j y (Fin.last (d + 1)) = ∑ k : Fin (d + 1), y ((Fin.castSucc j).succAbove k) := by
  simp [hurwitzGen]

/-- The `(d + 1)`-th coordinate (`Fin.castSucc (Fin.last d)`) of `hurwitzGen j y` is always the
previous last coordinate `y (Fin.last (d + 1))`. -/
theorem hurwitzGen_castSucc_last {d : ℕ} (j : Fin (d + 1)) (y : Fin (d + 2) → ℝ) :
    hurwitzGen j y (Fin.castSucc (Fin.last d)) = y (Fin.last (d + 1)) := by simp

/-- For `i : Fin d`, the `i`-th coordinate of `hurwitzGen j y` deletes `j` within `Fin (d + 1)`. -/
theorem hurwitzGen_castSucc_castSucc {d : ℕ} (j : Fin (d + 1)) (i : Fin d)
    (y : Fin (d + 2) → ℝ) :
    hurwitzGen j y (Fin.castSucc (Fin.castSucc i)) = y (Fin.castSucc (j.succAbove i)) := by
  rw [hurwitzGen_castSucc]; congr 1
  by_cases hlt : Fin.castSucc i < j
  · rw [Fin.succAbove_of_castSucc_lt _ _ (Fin.castSucc_lt_castSucc_iff.mpr hlt),
      Fin.succAbove_of_castSucc_lt _ _ hlt]
  · have hle : j ≤ Fin.castSucc i := not_lt.mp hlt
    rw [Fin.succAbove_of_le_castSucc _ _ (Fin.castSucc_le_castSucc_iff.mpr hle),
      Fin.succAbove_of_le_castSucc _ _ hle, Fin.succ_castSucc]

/-- Every output of `hurwitzGen j` lies on `orderedConeHyperplane d`. -/
theorem hurwitzGen_mem_hyperplane {d : ℕ} (j : Fin (d + 1)) (y : Fin (d + 2) → ℝ) :
    hurwitzGen j y ∈ orderedConeHyperplane d := by simp

/-- On `orderedConeHyperplane d`, the last coordinate of `hurwitzGen j y` equals
`2 * y_{d+1} - y_j`. -/
theorem hurwitzGen_last_of_mem_hyperplane {d : ℕ} (j : Fin (d + 1)) {y : Fin (d + 2) → ℝ}
    (hy : y ∈ orderedConeHyperplane d) :
    hurwitzGen j y (Fin.last (d + 1)) = 2 * y (Fin.last (d + 1)) - y (Fin.castSucc j) := by
  have hsplit := Fin.sum_univ_succAbove y (Fin.castSucc j)
  rw [Fin.sum_univ_castSucc, mem_orderedConeHyperplane_iff.mp hy] at hsplit
  linarith [hurwitzGen_last j y]

/-- Every generator `hurwitzGen j` maps `orderedCone d` into itself. -/
theorem hurwitzGen_mem_orderedCone {d : ℕ} (j : Fin (d + 1)) {y : Fin (d + 2) → ℝ}
    (hy : y ∈ orderedCone d) : hurwitzGen j y ∈ orderedCone d := by
  have hylast := last_pos_of_mem_orderedCone hy
  rw [mem_orderedCone_iff] at hy ⊢
  refine ⟨fun h0 => ?_,
    Fin.lastCases (by rw [hurwitzGen_last]; exact Finset.sum_nonneg fun _ _ => hy.2.1 _)
      fun k => by rw [hurwitzGen_castSucc]; exact hy.2.1 _,
    ?_, mem_orderedConeHyperplane_iff.mp (hurwitzGen_mem_hyperplane j y)⟩
  · have : y (Fin.last (d + 1)) = 0 := by simpa using congrFun h0 (Fin.castSucc (Fin.last d))
    linarith
  · refine Fin.lastCases (fun b hb => by obtain rfl := le_antisymm (Fin.le_last b) hb; exact le_rfl)
      fun a => Fin.lastCases (fun _ => by
        rw [hurwitzGen_castSucc, hurwitzGen_last]
        exact Finset.single_le_sum (fun _ _ => hy.2.1 _) (Finset.mem_univ a)) fun b hab => ?_
    rw [hurwitzGen_castSucc, hurwitzGen_castSucc]
    exact hy.2.2.1 ((Fin.strictMono_succAbove (Fin.castSucc j)).monotone
      (Fin.castSucc_le_castSucc_iff.mp hab))

/-- Every unaccelerated generator `hurwitzGen j` strictly increases `y_{d+1}` on
`strictOrderedCone d`. -/
theorem last_lt_hurwitzGen_last_of_mem_strictOrderedCone {d : ℕ} (j : Fin (d + 1))
    {y : Fin (d + 2) → ℝ} (hy : y ∈ strictOrderedCone d) :
    y (Fin.last (d + 1)) < hurwitzGen j y (Fin.last (d + 1)) := by
  rw [mem_strictOrderedCone_iff] at hy
  rw [hurwitzGen_last_of_mem_hyperplane j hy.2.2]
  linarith [hy.2.1 (Fin.castSucc_lt_last j)]

/-- For `1 ≤ d`, every unaccelerated generator `hurwitzGen j` maps `strictOrderedCone d` into
itself. -/
theorem hurwitzGen_mem_strictOrderedCone {d : ℕ} (hd : 1 ≤ d) (j : Fin (d + 1))
    {y : Fin (d + 2) → ℝ} (hy : y ∈ strictOrderedCone d) :
    hurwitzGen j y ∈ strictOrderedCone d := by
  have hlast_gt := last_lt_hurwitzGen_last_of_mem_strictOrderedCone j hy
  rw [mem_strictOrderedCone_iff] at hy ⊢
  rcases hy with ⟨hypos, hystrict, _⟩
  refine ⟨Fin.lastCases (lt_trans (hypos _) hlast_gt) fun k => by simp [hypos], fun a b hab => ?_,
    hurwitzGen_mem_hyperplane j y⟩
  induction a using Fin.lastCases with
  | last => exact absurd hab (not_lt_of_ge (Fin.le_last b))
  | cast k =>
    induction b using Fin.lastCases with
    | cast b' =>
      simpa using hystrict ((Fin.strictMono_succAbove (Fin.castSucc j))
        (Fin.castSucc_lt_castSucc_iff.mp hab))
    | last =>
      obtain ⟨m, hmk⟩ : ∃ m : Fin (d + 1), m ≠ k :=
        if hk0 : k = 0 then ⟨Fin.last d, by rw [hk0, ne_eq, Fin.ext_iff]; simp; omega⟩
        else ⟨0, Ne.symm hk0⟩
      have hle := Finset.sum_le_sum_of_subset_of_nonneg
        (f := fun r : Fin (d + 1) => y ((Fin.castSucc j).succAbove r))
        (Finset.subset_univ ({k, m} : Finset (Fin (d + 1)))) fun r _ _ => (hypos _).le
      rw [Finset.sum_pair hmk.symm] at hle
      rw [hurwitzGen_castSucc, hurwitzGen_last]
      linarith [hypos ((Fin.castSucc j).succAbove m)]

/-- One-step unique recovery on `strictOrderedCone d`: if `hurwitzGen j₁ y₁ = hurwitzGen j₂ y₂`
for `y₁, y₂ ∈ strictOrderedCone d`, then `j₁ = j₂` and `y₁ = y₂`
(Gamburd–Magee–Ronan 2019, p. 756, footnote 5). -/
theorem hurwitzGen_inj_on_strictOrderedCone {d : ℕ} {j₁ j₂ : Fin (d + 1)}
    {y₁ y₂ : Fin (d + 2) → ℝ} (hy₁ : y₁ ∈ strictOrderedCone d) (hy₂ : y₂ ∈ strictOrderedCone d)
    (heq : hurwitzGen j₁ y₁ = hurwitzGen j₂ y₂) : j₁ = j₂ ∧ y₁ = y₂ := by
  have hlast : y₁ (Fin.last (d + 1)) = y₂ (Fin.last (d + 1)) := by
    simpa using congrFun heq (Fin.castSucc (Fin.last d))
  have hdel : y₁ (Fin.castSucc j₁) = y₂ (Fin.castSucc j₂) := by
    have hlast_img := congrFun heq (Fin.last (d + 1))
    rw [hurwitzGen_last_of_mem_hyperplane j₁ (mem_strictOrderedCone_iff.mp hy₁).2.2,
      hurwitzGen_last_of_mem_hyperplane j₂ (mem_strictOrderedCone_iff.mp hy₂).2.2, hlast]
      at hlast_img
    linarith
  have hnotlt : ∀ {p q : Fin (d + 1)} {u v : Fin (d + 2) → ℝ},
      u ∈ strictOrderedCone d → v ∈ strictOrderedCone d →
      hurwitzGen p u = hurwitzGen q v → u (Fin.castSucc p) = v (Fin.castSucc q) → ¬ p < q := by
    intro p q u v hu hv hpq hdel_uv hlt
    rw [mem_strictOrderedCone_iff] at hu hv
    have hp_ne : p ≠ Fin.last d := ne_of_lt (lt_of_lt_of_le hlt (Fin.le_last q))
    let i : Fin d := p.castPred hp_ne
    have hi : Fin.castSucc i = p := Fin.castSucc_castPred p hp_ne
    have himg := congrFun hpq (Fin.castSucc (Fin.castSucc i))
    rw [hurwitzGen_castSucc_castSucc, hurwitzGen_castSucc_castSucc,
      Fin.succAbove_of_le_castSucc p i (le_of_eq hi.symm),
      Fin.succAbove_of_castSucc_lt q i (hi.symm ▸ hlt), hi] at himg
    linarith [hu.2.1 (Fin.castSucc_lt_castSucc_iff.mpr (hi ▸ Fin.castSucc_lt_succ)),
      hv.2.1 (Fin.castSucc_lt_castSucc_iff.mpr hlt)]
  obtain rfl : j₁ = j₂ := by
    rcases lt_trichotomy j₁ j₂ with hlt | rfl | hgt
    · exact absurd hlt (hnotlt hy₁ hy₂ heq hdel)
    · rfl
    · exact absurd hgt (hnotlt hy₂ hy₁ heq.symm hdel.symm)
  refine ⟨rfl, funext fun m => ?_⟩
  by_cases hm : m = Fin.castSucc j₁
  · rwa [hm]
  · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hm
    simpa using congrFun heq (Fin.castSucc k)

/-- Iterating the top generator `hurwitzGen (Fin.last d)` `A` times on `orderedConeHyperplane d`
fixes the first `d` coordinates and advances the last two by arithmetic progression with step
`z_{d+1} - z_d`. -/
theorem hurwitzGen_last_pow_of_mem_hyperplane {d : ℕ} (A : ℕ) {z : Fin (d + 2) → ℝ}
    (hz : z ∈ orderedConeHyperplane d) :
    ((hurwitzGen (Fin.last d) ^ A) z =
      Fin.snoc
        (Fin.snoc (fun i : Fin d => z (Fin.castSucc (Fin.castSucc i)))
          (z (Fin.castSucc (Fin.last d)) +
            (A : ℝ) * (z (Fin.last (d + 1)) - z (Fin.castSucc (Fin.last d)))))
        (z (Fin.castSucc (Fin.last d)) +
          ((A : ℝ) + 1) * (z (Fin.last (d + 1)) - z (Fin.castSucc (Fin.last d))))) := by
  induction A with
  | zero =>
    ext m
    refine Fin.lastCases ?_ (Fin.lastCases (by simp) fun _ => by simp) m
    simp only [pow_zero, one_apply_eq_self, Fin.snoc_last, CharP.cast_eq_zero, zero_add, one_mul]
    linarith
  | succ A ih =>
    have hmem : (hurwitzGen (Fin.last d) ^ A) z ∈ orderedConeHyperplane d := by
      rcases A with _ | B; · simpa using hz
      rw [pow_succ']; exact hurwitzGen_mem_hyperplane _ _
    rw [pow_succ', mul_apply_eq_comp]
    ext m
    refine Fin.lastCases ?_ (Fin.lastCases ?_ fun i => ?_) m
    · rw [hurwitzGen_last_of_mem_hyperplane _ hmem, ih]
      simp only [Fin.snoc_last, Fin.snoc_castSucc, Nat.cast_add, Nat.cast_one]; ring
    · rw [hurwitzGen_castSucc_last, ih]; simp [Nat.cast_add]
    · rw [hurwitzGen_castSucc_castSucc, ih,
        Fin.succAbove_of_castSucc_lt _ _ (Fin.castSucc_lt_last i)]
      simp

/-- The accelerated Markoff–Hurwitz linear branch `γ_d^A ∘ γ_j` associated to the letter
`a = (A, j) : ℕ × Fin d` (Gamburd–Magee–Ronan 2019, §4.1). -/
def branchLinearMap {d : ℕ} (a : ℕ × Fin d) : (Fin (d + 2) → ℝ) →ₗ[ℝ] (Fin (d + 2) → ℝ) :=
  (hurwitzGen (Fin.last d) ^ a.1) ∘ₗ hurwitzGen (Fin.castSucc a.2)

/-- Evaluation of `branchLinearMap a` as `(hurwitzGen (Fin.last d) ^ a.1)` after
`hurwitzGen (Fin.castSucc a.2)`. -/
theorem branchLinearMap_apply {d : ℕ} (a : ℕ × Fin d) (y : Fin (d + 2) → ℝ) :
    branchLinearMap a y = (hurwitzGen (Fin.last d) ^ a.1) (hurwitzGen (Fin.castSucc a.2) y) := (rfl)

/-- Every output of `branchLinearMap a` lies on `orderedConeHyperplane d`. -/
theorem branchLinearMap_mem_hyperplane {d : ℕ} (a : ℕ × Fin d) (y : Fin (d + 2) → ℝ) :
    branchLinearMap a y ∈ orderedConeHyperplane d := by
  rw [branchLinearMap_apply]
  rcases a.1 with _ | B; · simp
  rw [pow_succ']; exact hurwitzGen_mem_hyperplane _ _

/-- Every accelerated linear branch `branchLinearMap a` maps `orderedCone d` into itself. -/
theorem branchLinearMap_mem_orderedCone {d : ℕ} (a : ℕ × Fin d) {y : Fin (d + 2) → ℝ}
    (hy : y ∈ orderedCone d) : branchLinearMap a y ∈ orderedCone d := by
  rw [branchLinearMap_apply]
  induction a.1 with
  | zero => simpa using hurwitzGen_mem_orderedCone (Fin.castSucc a.2) hy
  | succ B ih => rw [pow_succ']; exact hurwitzGen_mem_orderedCone (Fin.last d) ih

/-! ### Projective denominator, branch map, and homogeneous cocycle identity -/

/-- The denominator `q_a(w) = 1 + (A + 1) (1 - w_j)` of the accelerated branch `a = (A, j)`
(Gamburd–Magee–Ronan 2019, Lemma 33, (4.6)). -/
def branchDenom {d : ℕ} (a : ℕ × Fin d) (x : Fin d → ℝ) : ℝ :=
  1 + ((a.1 : ℝ) + 1) * (1 - x a.2)

/-- Coordinate formula for `branchDenom a x`. -/
theorem branchDenom_apply {d : ℕ} (a : ℕ × Fin d) (x : Fin d → ℝ) :
    branchDenom a x = 1 + ((a.1 : ℝ) + 1) * (1 - x a.2) := (rfl)

/-- The accelerated projective branch `F_a` in chart coordinates: delete `w_j` from
`(w₁, …, w_{d+1})` and divide by `branchDenom a x` (Gamburd–Magee–Ronan 2019, Lemma 33, (4.5)). -/
def branchMap {d : ℕ} (a : ℕ × Fin d) (x : Fin d → ℝ) : Fin d → ℝ :=
  fun i => (Fin.snoc (α := fun _ => ℝ) x (1 - ∑ k, x k) ((Fin.castSucc a.2).succAbove i)) /
    branchDenom a x

/-- Unfolded formula for `branchMap a x`. -/
theorem branchMap_def {d : ℕ} (a : ℕ × Fin d) (x : Fin d → ℝ) :
    branchMap a x = fun i =>
      (Fin.snoc (α := fun _ => ℝ) x (1 - ∑ k, x k) ((Fin.castSucc a.2).succAbove i)) /
        branchDenom a x := (rfl)

/-- Coordinate formula for `branchMap a x` in terms of `chartToSimplex x`. -/
theorem branchMap_apply {d : ℕ} (a : ℕ × Fin d) (x : Fin d → ℝ) (i : Fin d) :
    branchMap a x i = chartToSimplex x ((Fin.castSucc a.2).succAbove i) / branchDenom a x := by
  rw [branchMap_def, ← chartToSimplex_def]

/-- Explicit coordinate formula for `branchLinearMap a (orderedSimplexLift x)` at every
`x : Fin d → ℝ` (Gamburd–Magee–Ronan 2019, Lemma 33). -/
theorem branchLinearMap_orderedSimplexLift_eq {d : ℕ} (a : ℕ × Fin d) (x : Fin d → ℝ) :
    branchLinearMap a (orderedSimplexLift x) =
      Fin.snoc
        (Fin.snoc (fun i : Fin d => chartToSimplex x ((Fin.castSucc a.2).succAbove i))
          (1 + (a.1 : ℝ) * (1 - x a.2)))
        (branchDenom a x) := by
  let z := hurwitzGen (Fin.castSucc a.2) (orderedSimplexLift x)
  have hz : z ∈ orderedConeHyperplane d := hurwitzGen_mem_hyperplane _ _
  have hz_last : z (Fin.last (d + 1)) = 2 - x a.2 := by
    simpa [z] using hurwitzGen_last_of_mem_hyperplane (Fin.castSucc a.2)
      (mem_orderedConeHyperplane_iff.mpr (sum_castSucc_orderedSimplexLift x))
  have hz_sub : z (Fin.castSucc (Fin.last d)) = 1 := by simp [z]
  have hz_first : ∀ i : Fin d,
      z (Fin.castSucc (Fin.castSucc i)) = chartToSimplex x ((Fin.castSucc a.2).succAbove i) :=
    fun i => by dsimp only [z]; rw [hurwitzGen_castSucc_castSucc, orderedSimplexLift_castSucc]
  rw [branchLinearMap_apply, hurwitzGen_last_pow_of_mem_hyperplane a.1 hz]
  simp only [hz_first, hz_sub, hz_last, branchDenom_apply]
  congr 1 <;> [congr 1; skip] <;> ring

/-- The last coordinate of `branchLinearMap a (orderedSimplexLift x)` is `branchDenom a x`. -/
@[simp]
theorem branchLinearMap_orderedSimplexLift_last {d : ℕ} (a : ℕ × Fin d) (x : Fin d → ℝ) :
    branchLinearMap a (orderedSimplexLift x) (Fin.last (d + 1)) = branchDenom a x := by
  rw [branchLinearMap_orderedSimplexLift_eq, Fin.snoc_last]

/-- Whenever `branchDenom a x ≠ 0`, the non-chart top simplex coordinate of `branchMap a x` is
`(1 + A (1 - x_j)) / branchDenom a x` (Gamburd–Magee–Ronan 2019, (4.5)). -/
theorem one_sub_sum_branchMap {d : ℕ} (a : ℕ × Fin d) {x : Fin d → ℝ}
    (hq : branchDenom a x ≠ 0) :
    1 - ∑ i : Fin d, branchMap a x i = (1 + (a.1 : ℝ) * (1 - x a.2)) / branchDenom a x := by
  have hmem := mem_orderedConeHyperplane_iff.mp
    (branchLinearMap_mem_hyperplane a (orderedSimplexLift x))
  rw [branchLinearMap_orderedSimplexLift_eq, Fin.snoc_last, Fin.sum_univ_castSucc] at hmem
  simp only [Fin.snoc_castSucc, Fin.snoc_last] at hmem
  simp only [branchMap_apply, ← Finset.sum_div]
  field_simp
  linarith

/-- Whenever `branchDenom a x ≠ 0`, `branchLinearMap a` scales `orderedSimplexLift x` into
`orderedSimplexLift (branchMap a x)` with factor `branchDenom a x`. -/
theorem branchLinearMap_orderedSimplexLift {d : ℕ} (a : ℕ × Fin d) {x : Fin d → ℝ}
    (hq : branchDenom a x ≠ 0) :
    branchLinearMap a (orderedSimplexLift x) =
      branchDenom a x • orderedSimplexLift (branchMap a x) := by
  rw [branchLinearMap_orderedSimplexLift_eq]
  ext m
  refine Fin.lastCases (by simp) (Fin.lastCases ?_ fun i => ?_) m
  · simp [one_sub_sum_branchMap a hq, mul_div_cancel₀ _ hq]
  · simp [branchMap_apply, mul_div_cancel₀ _ hq]

/-- On `orderedSimplex d`, `branchDenom a x` is at least `(A + 3) / 2`. -/
theorem le_branchDenom_of_mem_orderedSimplex {d : ℕ} (a : ℕ × Fin d) {x : Fin d → ℝ}
    (hx : x ∈ orderedSimplex d) : ((a.1 : ℝ) + 3) / 2 ≤ branchDenom a x := by
  rw [branchDenom_apply]
  nlinarith [apply_le_half_of_mem_orderedSimplex hx a.2, a.1.cast_nonneg (α := ℝ)]

/-- On `orderedSimplex d`, `branchDenom a x` is at most `A + 2`. -/
theorem branchDenom_le_of_mem_orderedSimplex {d : ℕ} (a : ℕ × Fin d) {x : Fin d → ℝ}
    (hx : x ∈ orderedSimplex d) : branchDenom a x ≤ (a.1 : ℝ) + 2 := by
  rw [branchDenom_apply]
  nlinarith [apply_nonneg_of_mem_orderedSimplex hx a.2, a.1.cast_nonneg (α := ℝ)]

/-- On `orderedSimplex d`, `branchDenom a x` is at least `3 / 2`. -/
theorem three_div_two_le_branchDenom_of_mem_orderedSimplex {d : ℕ} (a : ℕ × Fin d)
    {x : Fin d → ℝ} (hx : x ∈ orderedSimplex d) : (3 : ℝ) / 2 ≤ branchDenom a x :=
  (by linarith [a.1.cast_nonneg (α := ℝ)] : (3 : ℝ) / 2 ≤ ((a.1 : ℝ) + 3) / 2).trans
    (le_branchDenom_of_mem_orderedSimplex a hx)

/-- On `orderedSimplex d`, `branchDenom a x > 1`. -/
theorem one_lt_branchDenom_of_mem_orderedSimplex {d : ℕ} (a : ℕ × Fin d) {x : Fin d → ℝ}
    (hx : x ∈ orderedSimplex d) : 1 < branchDenom a x :=
  lt_of_lt_of_le (by norm_num) (three_div_two_le_branchDenom_of_mem_orderedSimplex a hx)

/-- On `orderedSimplex d`, `branchDenom a x > 0`. -/
theorem branchDenom_pos_of_mem_orderedSimplex {d : ℕ} (a : ℕ × Fin d) {x : Fin d → ℝ}
    (hx : x ∈ orderedSimplex d) : 0 < branchDenom a x :=
  lt_trans zero_lt_one (one_lt_branchDenom_of_mem_orderedSimplex a hx)

/-- Homogeneous cocycle relation on `orderedCone d`: `branchLinearMap a y` equals
`y_{d+1} * branchDenom a (orderedConeProject y)` times the lifted image point
`orderedSimplexLift (branchMap a (orderedConeProject y))`
(Gamburd–Magee–Ronan 2019, Lemma 33). -/
theorem branchLinearMap_eq_smul_orderedSimplexLift {d : ℕ} (a : ℕ × Fin d) {y : Fin (d + 2) → ℝ}
    (hy : y ∈ orderedCone d) :
    branchLinearMap a y =
      (y (Fin.last (d + 1)) * branchDenom a (orderedConeProject y)) •
        orderedSimplexLift (branchMap a (orderedConeProject y)) := by
  have hx := orderedConeProject_mem_orderedSimplex hy
  have hq := (branchDenom_pos_of_mem_orderedSimplex a hx).ne'
  nth_rw 1 [← last_smul_orderedSimplexLift_orderedConeProject hy]
  rw [map_smul, branchLinearMap_orderedSimplexLift a hq, smul_smul]

/-- For `y ∈ orderedCone d`, the last coordinate of `branchLinearMap a y` is
`y_{d+1} * branchDenom a (orderedConeProject y)`. -/
theorem branchLinearMap_last_of_mem_orderedCone {d : ℕ} (a : ℕ × Fin d) {y : Fin (d + 2) → ℝ}
    (hy : y ∈ orderedCone d) :
    branchLinearMap a y (Fin.last (d + 1)) =
      y (Fin.last (d + 1)) * branchDenom a (orderedConeProject y) := by
  rw [branchLinearMap_eq_smul_orderedSimplexLift a hy]; simp

/-- Projective equivariance on `orderedCone d`: `orderedConeProject` intertwines `branchLinearMap a`
with `branchMap a`. -/
theorem orderedConeProject_branchLinearMap {d : ℕ} (a : ℕ × Fin d) {y : Fin (d + 2) → ℝ}
    (hy : y ∈ orderedCone d) :
    orderedConeProject (branchLinearMap a y) = branchMap a (orderedConeProject y) := by
  have hqpos := branchDenom_pos_of_mem_orderedSimplex a (orderedConeProject_mem_orderedSimplex hy)
  rw [branchLinearMap_eq_smul_orderedSimplexLift a hy,
    orderedConeProject_smul (mul_pos (last_pos_of_mem_orderedCone hy) hqpos).ne',
    orderedConeProject_orderedSimplexLift]

/-- Every accelerated branch `branchMap a` maps `orderedSimplex d` into itself. -/
theorem mapsTo_branchMap_orderedSimplex {d : ℕ} (a : ℕ × Fin d) :
    MapsTo (branchMap a) (orderedSimplex d) (orderedSimplex d) := fun x hx => by
  have hy := orderedSimplexLift_mem_orderedCone_iff.mpr hx
  have hproj := orderedConeProject_branchLinearMap a hy
  rw [orderedConeProject_orderedSimplexLift] at hproj
  exact hproj ▸ orderedConeProject_mem_orderedSimplex (branchLinearMap_mem_orderedCone a hy)

/-- Pointwise form of `mapsTo_branchMap_orderedSimplex`. -/
theorem branchMap_mem_orderedSimplex {d : ℕ} (a : ℕ × Fin d) {x : Fin d → ℝ}
    (hx : x ∈ orderedSimplex d) : branchMap a x ∈ orderedSimplex d :=
  mapsTo_branchMap_orderedSimplex a hx

/-! ### Open domain, smoothness, and delay calculus -/

/-- The positivity locus `{x | 0 < branchDenom a x}` is an open subset of `Fin d → ℝ`. -/
theorem isOpen_branchDenom_pos {d : ℕ} (a : ℕ × Fin d) :
    IsOpen {x : Fin d → ℝ | 0 < branchDenom a x} := by
  unfold branchDenom; exact isOpen_lt continuous_const (by fun_prop)

/-- `orderedSimplex d` is contained in the open set `{x | 0 < branchDenom a x}`. -/
theorem orderedSimplex_subset_branchDenom_pos {d : ℕ} (a : ℕ × Fin d) :
    orderedSimplex d ⊆ {x : Fin d → ℝ | 0 < branchDenom a x} :=
  fun _ hx => branchDenom_pos_of_mem_orderedSimplex a hx

/-- `branchDenom a` is smooth (`ContDiff ℝ n` for every `n : WithTop ℕ∞`, including `∞` and `ω`)
on all of `Fin d → ℝ`. -/
theorem contDiff_branchDenom {d : ℕ} {n : WithTop ℕ∞} (a : ℕ × Fin d) :
    ContDiff ℝ n (branchDenom a) := by unfold branchDenom; fun_prop

/-- `branchMap a` is `ContDiffOn ℝ n` (for every `n : WithTop ℕ∞`) on
`{x | 0 < branchDenom a x}`. -/
theorem contDiffOn_branchMap_branchDenom_pos {d : ℕ} {n : WithTop ℕ∞} (a : ℕ × Fin d) :
    ContDiffOn ℝ n (branchMap a) {x : Fin d → ℝ | 0 < branchDenom a x} := by
  refine contDiffOn_pi.mpr fun i => ContDiffOn.div ?_ (contDiff_branchDenom a).contDiffOn
    fun _ hx => ne_of_gt hx
  refine ContDiff.contDiffOn (Fin.lastCases ?_ (fun m => ?_) ((Fin.castSucc a.2).succAbove i))
  · simp only [Fin.snoc_last]; fun_prop
  · simp only [Fin.snoc_castSucc]; exact contDiff_apply ℝ (fun _ : Fin d => ℝ) m

/-- `branchMap a` is `ContDiffOn ℝ n` on `orderedSimplex d` for every `n : WithTop ℕ∞`. -/
theorem contDiffOn_branchMap_orderedSimplex {d : ℕ} {n : WithTop ℕ∞} (a : ℕ × Fin d) :
    ContDiffOn ℝ n (branchMap a) (orderedSimplex d) :=
  (contDiffOn_branchMap_branchDenom_pos a).mono (orderedSimplex_subset_branchDenom_pos a)

/-- `branchMap a` is continuous on `orderedSimplex d`. -/
theorem continuousOn_branchMap_orderedSimplex {d : ℕ} (a : ℕ × Fin d) :
    ContinuousOn (branchMap a) (orderedSimplex d) :=
  (contDiffOn_branchMap_orderedSimplex (n := 0) a).continuousOn

/-- The roof delay `τ_a(w) = log q_a(w)` of the accelerated branch `a`
(Gamburd–Magee–Ronan 2019, §4.1). -/
def branchDelay {d : ℕ} (a : ℕ × Fin d) (x : Fin d → ℝ) : ℝ :=
  Real.log (branchDenom a x)

/-- Unfolded formula for `branchDelay a x`. -/
theorem branchDelay_apply {d : ℕ} (a : ℕ × Fin d) (x : Fin d → ℝ) :
    branchDelay a x = Real.log (branchDenom a x) := (rfl)

/-- Exponential of `branchDelay a x` where `0 < branchDenom a x`. -/
theorem exp_branchDelay {d : ℕ} (a : ℕ × Fin d) {x : Fin d → ℝ} (hq : 0 < branchDenom a x) :
    Real.exp (branchDelay a x) = branchDenom a x := Real.exp_log hq

/-- On `orderedSimplex d`, `branchDelay a x` is at least `log ((A + 3) / 2)`. -/
theorem log_add_three_div_two_le_branchDelay_of_mem_orderedSimplex {d : ℕ} (a : ℕ × Fin d)
    {x : Fin d → ℝ} (hx : x ∈ orderedSimplex d) :
    Real.log (((a.1 : ℝ) + 3) / 2) ≤ branchDelay a x :=
  Real.log_le_log (by positivity) (le_branchDenom_of_mem_orderedSimplex a hx)

/-- Uniform spectral-floor bound on `orderedSimplex d`: `log (3 / 2) ≤ branchDelay a x`. -/
theorem log_three_div_two_le_branchDelay_of_mem_orderedSimplex {d : ℕ} (a : ℕ × Fin d)
    {x : Fin d → ℝ} (hx : x ∈ orderedSimplex d) :
    Real.log (3 / 2) ≤ branchDelay a x :=
  Real.log_le_log (by norm_num) (three_div_two_le_branchDenom_of_mem_orderedSimplex a hx)

/-- On `orderedSimplex d`, `branchDelay a x` is at most `log (A + 2)`. -/
theorem branchDelay_le_log_add_two_of_mem_orderedSimplex {d : ℕ} (a : ℕ × Fin d) {x : Fin d → ℝ}
    (hx : x ∈ orderedSimplex d) : branchDelay a x ≤ Real.log ((a.1 : ℝ) + 2) :=
  Real.log_le_log (branchDenom_pos_of_mem_orderedSimplex a hx)
    (branchDenom_le_of_mem_orderedSimplex a hx)

/-- `branchDelay a x` is strictly positive at every point of `orderedSimplex d`. -/
theorem branchDelay_pos_of_mem_orderedSimplex {d : ℕ} (a : ℕ × Fin d) {x : Fin d → ℝ}
    (hx : x ∈ orderedSimplex d) : 0 < branchDelay a x :=
  Real.log_pos (one_lt_branchDenom_of_mem_orderedSimplex a hx)

/-- `branchDelay a` is `ContDiffOn ℝ n` on `{x | 0 < branchDenom a x}` for every
`n : WithTop ℕ∞`. -/
theorem contDiffOn_branchDelay_branchDenom_pos {d : ℕ} {n : WithTop ℕ∞} (a : ℕ × Fin d) :
    ContDiffOn ℝ n (branchDelay a) {x : Fin d → ℝ | 0 < branchDenom a x} :=
  (contDiff_branchDenom a).contDiffOn.log fun _ hx => ne_of_gt hx

/-- `branchDelay a` is `ContDiffOn ℝ n` on `orderedSimplex d` for every `n : WithTop ℕ∞`. -/
theorem contDiffOn_branchDelay_orderedSimplex {d : ℕ} {n : WithTop ℕ∞} (a : ℕ × Fin d) :
    ContDiffOn ℝ n (branchDelay a) (orderedSimplex d) :=
  (contDiffOn_branchDelay_branchDenom_pos a).mono (orderedSimplex_subset_branchDenom_pos a)

/-- Exact Fréchet derivative of `branchDenom a` at any `x : Fin d → ℝ`. -/
theorem hasFDerivAt_branchDenom {d : ℕ} (a : ℕ × Fin d) (x : Fin d → ℝ) :
    HasFDerivAt (branchDenom a)
      (-(((a.1 : ℝ) + 1) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) a.2)) x := by
  have hmul := (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) a.2).hasFDerivAt
    (x := x)).const_sub (1 : ℝ)).const_mul ((a.1 : ℝ) + 1)
  rw [smul_neg] at hmul
  exact hmul.const_add (1 : ℝ)

/-- Exact Fréchet derivative of `branchDelay a = log ∘ branchDenom a` wherever
`branchDenom a x ≠ 0`. -/
theorem hasFDerivAt_branchDelay {d : ℕ} (a : ℕ × Fin d) {x : Fin d → ℝ}
    (hq : branchDenom a x ≠ 0) :
    HasFDerivAt (branchDelay a)
      (-((((a.1 : ℝ) + 1) / branchDenom a x) •
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) a.2)) x := by
  unfold branchDelay
  convert (hasFDerivAt_branchDenom a x).log hq using 1
  ext v; simp [div_eq_inv_mul]; ring

/-- Partial derivatives of `branchDelay a` along the coordinate directions `Pi.single k 1`:
`-(A + 1) / branchDenom a x` in slot `a.2`, and `0` in all other slots. -/
theorem fderiv_branchDelay_apply_single {d : ℕ} (a : ℕ × Fin d) {x : Fin d → ℝ}
    (hq : branchDenom a x ≠ 0) (k : Fin d) :
    fderiv ℝ (branchDelay a) x (Pi.single k 1) =
      if k = a.2 then -(((a.1 : ℝ) + 1) / branchDenom a x) else 0 := by
  rw [(hasFDerivAt_branchDelay a hq).fderiv]
  by_cases hk : k = a.2 <;> simp [hk]

/-- Exact operator norm of `fderiv ℝ (branchDelay a) x` with respect to the sup norm on `Fin d → ℝ`
wherever `0 < branchDenom a x`. -/
theorem norm_fderiv_branchDelay {d : ℕ} (a : ℕ × Fin d) {x : Fin d → ℝ}
    (hq : 0 < branchDenom a x) :
    ‖fderiv ℝ (branchDelay a) x‖ = ((a.1 : ℝ) + 1) / branchDenom a x := by
  have hc : 0 ≤ ((a.1 : ℝ) + 1) / branchDenom a x := div_nonneg (by positivity) hq.le
  rw [(hasFDerivAt_branchDelay a hq.ne').fderiv, norm_neg]
  refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ hc fun v => ?_) ?_
  · rw [smul_apply, ContinuousLinearMap.proj_apply, norm_smul, Real.norm_of_nonneg hc]
    exact mul_le_mul_of_nonneg_left (norm_le_pi_norm v a.2) hc
  · have : Nonempty (Fin d) := ⟨a.2⟩
    simpa [Real.norm_of_nonneg hc] using ((((a.1 : ℝ) + 1) / branchDenom a x) •
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) a.2).le_opNorm (fun _ => 1)

/-- On `orderedSimplex d`, `fderivWithin ℝ (branchDelay a) (orderedSimplex d) x` agrees with the
ambient derivative `fderiv ℝ (branchDelay a) x`. -/
theorem fderivWithin_branchDelay_orderedSimplex {d : ℕ} (a : ℕ × Fin d) {x : Fin d → ℝ}
    (hx : x ∈ orderedSimplex d) :
    fderivWithin ℝ (branchDelay a) (orderedSimplex d) x = fderiv ℝ (branchDelay a) x := by
  have hq := (branchDenom_pos_of_mem_orderedSimplex a hx).ne'
  rw [(hasFDerivAt_branchDelay a hq).fderiv]
  exact (hasFDerivAt_branchDelay a hq).hasFDerivWithinAt.fderivWithin
    (uniqueDiffOn_orderedSimplex d x hx)

/-- On `orderedSimplex d`, the logarithmic derivative satisfies
`‖fderivWithin ℝ (branchDelay a) (orderedSimplex d) x‖ ≤ 2 (A + 1) / (A + 3)`. -/
theorem norm_fderivWithin_branchDelay_le_of_mem_orderedSimplex {d : ℕ} (a : ℕ × Fin d)
    {x : Fin d → ℝ} (hx : x ∈ orderedSimplex d) :
    ‖fderivWithin ℝ (branchDelay a) (orderedSimplex d) x‖ ≤
      2 * ((a.1 : ℝ) + 1) / ((a.1 : ℝ) + 3) := by
  rw [fderivWithin_branchDelay_orderedSimplex a hx,
    norm_fderiv_branchDelay a (branchDenom_pos_of_mem_orderedSimplex a hx)]
  refine (div_le_div_of_nonneg_left (by positivity) (by positivity)
    (le_branchDenom_of_mem_orderedSimplex a hx)).trans_eq ?_
  field_simp

/-- Uniform logarithmic-derivative bound `< 2` across all letters `a` and points `x` in
`orderedSimplex d` (Gamburd–Magee–Ronan 2019, §4.2). -/
theorem norm_fderivWithin_branchDelay_lt_two_of_mem_orderedSimplex {d : ℕ} (a : ℕ × Fin d)
    {x : Fin d → ℝ} (hx : x ∈ orderedSimplex d) :
    ‖fderivWithin ℝ (branchDelay a) (orderedSimplex d) x‖ < 2 :=
  (norm_fderivWithin_branchDelay_le_of_mem_orderedSimplex a hx).trans_lt
    ((div_lt_iff₀ (by positivity)).mpr (by linarith))

/-! ### Complex branch weights `q_a^{-s}` -/

/-- Wherever `0 < branchDenom a x`, the complex power `(branchDenom a x : ℂ) ^ (-s)` equals
`Complex.exp (-s * branchDelay a x)`. -/
theorem branchDenom_cpow_neg_eq_exp {d : ℕ} (a : ℕ × Fin d) {x : Fin d → ℝ}
    (hq : 0 < branchDenom a x) (s : ℂ) :
    (branchDenom a x : ℂ) ^ (-s) = Complex.exp (-s * (branchDelay a x : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hq.ne'), branchDelay_apply,
    Complex.ofReal_log hq.le, mul_comm]

/-- Wherever `0 < branchDenom a x`, the norm of `(branchDenom a x : ℂ) ^ (-s)` is the real power
`branchDenom a x ^ (-s.re)`. -/
theorem norm_branchDenom_cpow_neg {d : ℕ} (a : ℕ × Fin d) {x : Fin d → ℝ}
    (hq : 0 < branchDenom a x) (s : ℂ) :
    ‖(branchDenom a x : ℂ) ^ (-s)‖ = branchDenom a x ^ (-s.re) := by
  simpa using Complex.norm_cpow_eq_rpow_re_of_pos hq (-s)

/-- At a real parameter `σ : ℝ` and nonnegative denominator, `(branchDenom a x : ℂ) ^ (-σ)` agrees
with the real power `branchDenom a x ^ (-σ)` coerced to `ℂ`. -/
theorem branchDenom_cpow_neg_ofReal {d : ℕ} (a : ℕ × Fin d) {x : Fin d → ℝ}
    (hq : 0 ≤ branchDenom a x) (σ : ℝ) :
    (branchDenom a x : ℂ) ^ (-(σ : ℂ)) = ((branchDenom a x ^ (-σ) : ℝ) : ℂ) := by
  rw [← Complex.ofReal_neg, ← Complex.ofReal_cpow hq]

/-- At a real parameter `σ : ℝ` and positive denominator, the real branch weight
`branchDenom a x ^ (-σ)` is strictly positive. -/
theorem branchDenom_rpow_neg_pos {d : ℕ} (a : ℕ × Fin d) {x : Fin d → ℝ}
    (hq : 0 < branchDenom a x) (σ : ℝ) :
    0 < branchDenom a x ^ (-σ) := Real.rpow_pos_of_pos hq (-σ)

end TauCeti.MarkoffHurwitz
