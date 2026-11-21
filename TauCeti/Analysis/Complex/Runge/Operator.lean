/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Topology.FilledIn
import Mathlib.Topology.Separation.Regular
import TauCeti.Analysis.Complex.Pompeiu.Discretization
import TauCeti.Analysis.Complex.Runge.SimpleFraction

/-!
# The finite-rank Runge approximation operator

A **Runge compact pair** `TauCeti.IsRungeCompactPair Ω K` consists of an open set `Ω ⊆ ℂ` and a
compact subset `K ⊆ Ω` that is filled in `Ω` (`TauCeti.IsFilledIn K Ω`, meaning no connected
component of `Ω \ K` is relatively compact in `Ω`).

For any Runge compact pair `(Ω, K)` and any open neighbourhood `U ⊇ K`, this file shows that there
exists a compact neighbourhood `L` of `K` with `K ⊆ interior L ⊆ L ⊆ U ∩ Ω` such that, for every
`ε > 0`, one can choose finitely many nodes `ζ j ∈ interior L`, weights `w j`, and `Ω`-holomorphic
functions `g j` — all independent of `f` and of the target complex normed space `W` — satisfying

`sup_{z ∈ K} ‖f z - ∑ j, (w j * g j z) • f (ζ j)‖ ≤ ε * B`

for every `U`-holomorphic function `f : ℂ → W` and every upper bound `B ≥ 0` of `‖f‖` on `L`
(`TauCeti.exists_finite_rank_runge_operator`). Choosing `ζ j`, `w j`, and `g j` independently of
`f` makes `f ↦ ∑ j, (w j * g j) • f (ζ j)` a finite-rank linear evaluation operator, so applying it
fiberwise preserves continuous, smooth, or holomorphic dependence on external parameters in
addition to yielding uniform Runge approximation for normed-space-valued functions
(`TauCeti.Analysis.Complex.Runge.Approximation`).

## Main declarations and results

* `TauCeti.IsRungeCompactPair`: predicate asserting `IsOpen Ω`, `IsCompact K`, `K ⊆ Ω`, and
  `TauCeti.IsFilledIn K Ω`, with projection eliminators and `@[simp]` empty-set normal forms.
* `TauCeti.exists_finite_rank_runge_operator`: existence of the compact neighbourhood `L ⊆ U ∩ Ω`
  and `f`-independent finite-rank evaluation approximants with operator norm bound `ε * B` for
  arbitrary complex normed targets.

## References

* A. Rainer, *Advanced Complex Analysis*, Theorems 10.3 and 11.1.
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed.,
  Theorem 1.3.9.
-/

public section

open Complex Metric Set Topology

universe u

namespace TauCeti

/-- A **Runge compact pair**: an open set `Ω ⊆ ℂ` and a compact subset `K ⊆ Ω` that is filled in
`Ω` (no connected component of `Ω \ K` has compact closure contained in `Ω`). -/
def IsRungeCompactPair (Ω K : Set ℂ) : Prop :=
  IsOpen Ω ∧ IsCompact K ∧ K ⊆ Ω ∧ IsFilledIn K Ω

/-- Unfolding `TauCeti.IsRungeCompactPair`. -/
theorem isRungeCompactPair_iff {Ω K : Set ℂ} :
    IsRungeCompactPair Ω K ↔ IsOpen Ω ∧ IsCompact K ∧ K ⊆ Ω ∧ IsFilledIn K Ω :=
  (Iff.rfl)

/-- The ambient set of a Runge compact pair is open. -/
protected theorem IsRungeCompactPair.isOpen {Ω K : Set ℂ} (h : IsRungeCompactPair Ω K) :
    IsOpen Ω :=
  h.1

/-- The compact member of a Runge compact pair is compact. -/
protected theorem IsRungeCompactPair.isCompact {Ω K : Set ℂ} (h : IsRungeCompactPair Ω K) :
    IsCompact K :=
  h.2.1

/-- The compact member of a Runge compact pair is contained in the ambient set. -/
protected theorem IsRungeCompactPair.subset {Ω K : Set ℂ} (h : IsRungeCompactPair Ω K) :
    K ⊆ Ω :=
  h.2.2.1

/-- The compact member of a Runge compact pair is filled in the ambient set. -/
protected theorem IsRungeCompactPair.isFilledIn {Ω K : Set ℂ} (h : IsRungeCompactPair Ω K) :
    IsFilledIn K Ω :=
  h.2.2.2

/-- The empty set forms a Runge compact pair with `Ω` if and only if `Ω` is open. -/
@[simp]
theorem isRungeCompactPair_empty_right {Ω : Set ℂ} :
    IsRungeCompactPair Ω ∅ ↔ IsOpen Ω := by
  refine ⟨fun h => h.isOpen, fun hΩ => ⟨hΩ, isCompact_empty, empty_subset Ω, ?_⟩⟩
  rw [isFilledIn_iff_forall_mem_filledHull_sdiff_not_connectedComponentIn_subset
    isClosed_empty hΩ (empty_subset Ω),
    filledHull_eq_self (by simpa using isPreconnected_univ)
      (by simpa using NormedSpace.unbounded_univ ℂ ℂ)]
  simp

/-- A set `K` forms a Runge compact pair with `∅` if and only if `K = ∅`. -/
@[simp]
theorem isRungeCompactPair_empty_left {K : Set ℂ} :
    IsRungeCompactPair ∅ K ↔ K = ∅ :=
  ⟨fun h => subset_empty_iff.mp h.subset,
    fun h => h ▸ isRungeCompactPair_empty_right.mpr isOpen_empty⟩

/-- **Finite-rank Runge operator.** For a Runge compact pair `(Ω, K)` and an open neighbourhood
`U ⊇ K`, there exists a compact neighbourhood `L` of `K` inside `U ∩ Ω` such that for every
`ε > 0` there are finitely many nodes `ζ j ∈ interior L`, weights `w j`, and `Ω`-holomorphic
functions `g j` (independent of `f` and the complex normed target `W`) approximating every
`U`-holomorphic function `f : ℂ → W` on `K` within `ε * B` for any upper bound `B ≥ 0` of `‖f‖`
on `L`. -/
theorem exists_finite_rank_runge_operator {Ω K U : Set ℂ}
    (hRunge : IsRungeCompactPair Ω K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ L : Set ℂ, IsCompact L ∧ K ⊆ interior L ∧ L ⊆ U ∩ Ω ∧
      ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, ∃ ζ : Fin N → ℂ, ∃ w : Fin N → ℂ,
          ∃ g : Fin N → ℂ → ℂ,
            (∀ j, ζ j ∈ interior L) ∧
            (∀ j, DifferentiableOn ℂ (g j) Ω) ∧
            ∀ {W : Type u} [NormedAddCommGroup W] [NormedSpace ℂ W] (f : ℂ → W),
              DifferentiableOn ℂ f U →
              ∀ B : ℝ, 0 ≤ B → (∀ z ∈ L, ‖f z‖ ≤ B) →
                ∀ z ∈ K,
                  ‖f z - ∑ j, (w j * g j z) • f (ζ j)‖ ≤ ε * B := by
  obtain ⟨hΩ, hK, hKΩ, hfill⟩ := hRunge
  rcases K.eq_empty_or_nonempty with rfl | _
  · exact ⟨∅, isCompact_empty, by simp, empty_subset _, fun _ _ =>
      ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, fun j => j.elim0, fun j => j.elim0,
        fun _ _ _ _ _ _ hz => hz.elim⟩⟩
  -- Shrink `U ∩ Ω` to a relatively compact open neighbourhood `V` with compact closure `L`.
  obtain ⟨V, hV, hKV, hVUO, hVc⟩ :=
    exists_open_between_and_isCompact_closure hK (hU.inter hΩ) (subset_inter hKU hKΩ)
  let L : Set ℂ := closure V
  have hVL : V ⊆ interior L := hV.subset_interior_iff.mpr subset_closure
  have hKL : K ⊆ interior L := hKV.trans hVL
  refine ⟨L, hVc, hKL, hVUO, fun ε hε => ?_⟩
  -- Discretize Cauchy–Pompeiu on `K` inside `V` and approximate each simple fraction on `Ω`.
  obtain ⟨N, ζ, w, hζ, hdisc⟩ :=
    hK.exists_norm_sub_sum_mul_sub_inv_smul_le.{u} hV hKV (ε := ε / 2) (half_pos hε)
  let W₀ : ℝ := max (∑ i, ‖w i‖) 1
  have hW₀ : 0 < W₀ := zero_lt_one.trans_le (le_max_right _ _)
  have happrox : ∀ j : Fin N, ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Ω ∧
      ∀ z ∈ K, ‖(z - ζ j)⁻¹ - g z‖ < ε / 2 / W₀ := fun j =>
    hfill.exists_differentiableOn_norm_inv_sub_lt hΩ hK hKΩ (hζ j).2 (by positivity)
  choose g hg_diff hg_lt using happrox
  refine ⟨N, ζ, w, g, fun j => hVL (hζ j).1, hg_diff, fun {W} _ _ f hf B hB hLB z hz => ?_⟩
  have herr₁ : ‖f z - ∑ j, (w j * (z - ζ j)⁻¹) • f (ζ j)‖ ≤ (ε / 2) * B :=
    hdisc f B (hf.mono (subset_closure.trans (hVUO.trans inter_subset_left)))
      (fun y hy => hLB y (subset_closure hy)) z hz
  have herr₂ : ‖∑ j, (w j * (z - ζ j)⁻¹) • f (ζ j) - ∑ j, (w j * g j z) • f (ζ j)‖ ≤
      (ε / 2) * B := by
    have hdiff :
        ∑ j, (w j * (z - ζ j)⁻¹) • f (ζ j) - ∑ j, (w j * g j z) • f (ζ j) =
          ∑ j, (w j * ((z - ζ j)⁻¹ - g j z)) • f (ζ j) := by
      simp only [← Finset.sum_sub_distrib, ← sub_smul, ← mul_sub]
    rw [hdiff]
    calc ‖∑ j, (w j * ((z - ζ j)⁻¹ - g j z)) • f (ζ j)‖
        ≤ ∑ j, ‖(w j * ((z - ζ j)⁻¹ - g j z)) • f (ζ j)‖ := norm_sum_le _ _
      _ ≤ ∑ j, ‖w j‖ * (ε / 2 / W₀) * B := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [norm_smul, norm_mul]
          exact mul_le_mul (mul_le_mul_of_nonneg_left (hg_lt j z hz).le (norm_nonneg _))
            (hLB (ζ j) (subset_closure (hζ j).1)) (norm_nonneg _) (by positivity)
      _ = (∑ j, ‖w j‖) * (ε / 2 / W₀ * B) := by simp only [← Finset.sum_mul, mul_assoc]
      _ ≤ W₀ * (ε / 2 / W₀ * B) := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ = (ε / 2) * B := by rw [← mul_assoc, mul_div_cancel₀ _ hW₀.ne']
  calc ‖f z - ∑ j, (w j * g j z) • f (ζ j)‖
      ≤ ‖f z - ∑ j, (w j * (z - ζ j)⁻¹) • f (ζ j)‖ +
          ‖∑ j, (w j * (z - ζ j)⁻¹) • f (ζ j) - ∑ j, (w j * g j z) • f (ζ j)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (ε / 2) * B + (ε / 2) * B := add_le_add herr₁ herr₂
    _ = ε * B := by ring

end TauCeti
