/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Topology.FilledHull
import TauCeti.Algebra.Polynomial.BigOperators
import TauCeti.Analysis.Complex.Pompeiu.Discretization
import TauCeti.Analysis.Complex.Runge.Rational.SimpleFraction

/-!
# Rational Runge approximation with prescribed finite poles

Let `K ⊆ ℂ` be a compact set and `A ⊆ ℂ` a prescribed set of poles meeting every bounded connected
component of `Kᶜ`. Combining simple-fraction pole pushing
(`IsCompact.exists_rational_norm_inv_sub_lt` in
`TauCeti.Analysis.Complex.Runge.Rational.SimpleFraction`) with discretization of the Cauchy–Pompeiu
formula (`IsCompact.exists_norm_sub_sum_mul_sub_inv_smul_le`), this file constructs:

* `IsCompact.exists_rational_norm_sub_sum_smul_le`: a finite-rank operator with rational kernels
  `p i / q i` (poles in `A \ K`) and nodes `ζ i ∈ V \ K`, satisfying an `ε * M` operator bound for
  all `F`-valued functions holomorphic on `V` and bounded by `M`.
* `IsCompact.exists_rational_norm_sub_sum_smul_lt`: strict `ε`-approximation of a given `F`-valued
  function holomorphic near `K` by a linear combination of `f (ζ i)` with rational kernels.
* `IsCompact.exists_rational_norm_sub_lt`: uniform rational approximation of a scalar function
  holomorphic near `K` by a single quotient `p / q` with poles in `A \ K`.

## References

* A. Rainer, *Advanced Complex Analysis*, Theorem 11.7, p. 29.
* W. Rudin, *Real and Complex Analysis*, 3rd ed., Theorem 13.6.
-/

public section

open Metric Polynomial Set

universe u

namespace TauCeti

/-- **Finite-rank rational Runge approximation operator.** Let `K ⊆ ℂ` be compact, `V ⊆ ℂ` an open
neighbourhood of `K`, and `A ⊆ ℂ` a set meeting every bounded connected component of `Kᶜ`. For
every `ε > 0` there are finitely many points `ζ i ∈ V \ K` and rational kernels `p i / q i` with
poles in `A \ K` such that every `f : ℂ → F` into a complex normed space, holomorphic on `V` and
bounded by `M` there, satisfies `‖f w - ∑ i, ((p i).eval w / (q i).eval w) • f (ζ i)‖ ≤ ε * M` for
all `w ∈ K`. The points and rational kernels depend only on `K`, `V`, `A`, and `ε`. -/
theorem _root_.IsCompact.exists_rational_norm_sub_sum_smul_le {K V A : Set ℂ} (hK : IsCompact K)
    (hV : IsOpen V) (hKV : K ⊆ V)
    (hA : ∀ x ∈ filledHull K \ K, (A ∩ connectedComponentIn Kᶜ x).Nonempty)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : ℕ) (ζ : Fin N → ℂ) (p q : Fin N → ℂ[X]),
      (∀ i, ζ i ∈ V \ K) ∧ (∀ i, q i ≠ 0) ∧ (∀ i z, (q i).eval z = 0 → z ∈ A \ K) ∧
      ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℂ F] (f : ℂ → F) (M : ℝ),
        DifferentiableOn ℂ f V → (∀ z ∈ V, ‖f z‖ ≤ M) →
        ∀ w ∈ K, ‖f w - ∑ i, ((p i).eval w / (q i).eval w) • f (ζ i)‖ ≤ ε * M := by
  obtain ⟨N, ζ, c, hζ, hdisc⟩ :=
    hK.exists_norm_sub_sum_mul_sub_inv_smul_le.{u} hV hKV (half_pos hε)
  set S : ℝ := ∑ i : Fin N, ‖c i‖
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  have hS1 : 0 < S + 1 := by linarith
  set δ : ℝ := ε / (2 * (S + 1))
  have hδ : 0 < δ := by positivity
  choose p_i q_i hq_i hqA_i happrox using fun i : Fin N ↦
    hK.exists_rational_norm_inv_sub_lt (hζ i).2 (fun haH ↦ hA _ ⟨haH, (hζ i).2⟩) hδ
  refine ⟨N, ζ, fun i ↦ C (c i) * p_i i, q_i, hζ, hq_i, hqA_i,
    fun {F} _ _ f M hf hM w hw ↦ ?_⟩
  have hM0 : 0 ≤ M := (norm_nonneg (f w)).trans (hM w (hKV hw))
  have hsplit : f w - ∑ i, ((C (c i) * p_i i).eval w / (q_i i).eval w) • f (ζ i) =
      (f w - ∑ i, (c i * (w - ζ i)⁻¹) • f (ζ i)) +
        ∑ i, (c i * ((w - ζ i)⁻¹ - (p_i i).eval w / (q_i i).eval w)) • f (ζ i) := by
    rw [sub_add, ← Finset.sum_sub_distrib]
    refine congrArg (f w - ·) (Finset.sum_congr rfl fun i _ ↦ ?_)
    rw [← sub_smul, eval_mul, eval_C]
    congr 1; ring
  have htail :
      ‖∑ i, (c i * ((w - ζ i)⁻¹ - (p_i i).eval w / (q_i i).eval w)) • f (ζ i)‖ ≤ ε / 2 * M := by
    calc ‖∑ i, (c i * ((w - ζ i)⁻¹ - (p_i i).eval w / (q_i i).eval w)) • f (ζ i)‖
        ≤ ∑ i, ‖(c i * ((w - ζ i)⁻¹ - (p_i i).eval w / (q_i i).eval w)) • f (ζ i)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ i, ‖c i‖ * δ * M := Finset.sum_le_sum fun i _ ↦ by
          rw [norm_smul, norm_mul]
          exact mul_le_mul (mul_le_mul_of_nonneg_left (happrox i w hw).le (norm_nonneg _))
            (hM (ζ i) (hζ i).1) (norm_nonneg _) (by positivity)
      _ = S * δ * M := by simp [S, Finset.sum_mul]
      _ ≤ (S + 1) * δ * M := by gcongr; linarith
      _ = ε / 2 * M := by simp only [δ]; field_simp [hS1.ne']
  rw [hsplit]
  calc ‖(f w - ∑ i, (c i * (w - ζ i)⁻¹) • f (ζ i)) +
          ∑ i, (c i * ((w - ζ i)⁻¹ - (p_i i).eval w / (q_i i).eval w)) • f (ζ i)‖
      ≤ ‖f w - ∑ i, (c i * (w - ζ i)⁻¹) • f (ζ i)‖ +
          ‖∑ i, (c i * ((w - ζ i)⁻¹ - (p_i i).eval w / (q_i i).eval w)) • f (ζ i)‖ :=
        norm_add_le _ _
    _ ≤ ε / 2 * M + ε / 2 * M := add_le_add (hdisc f M hf hM w hw) htail
    _ = ε * M := by ring

/-- **Strict rational-kernel Runge approximation (vector-valued).** Let `K ⊆ ℂ` be compact, `U ⊆ ℂ`
an open neighbourhood of `K`, `A ⊆ ℂ` a set meeting every bounded connected component of `Kᶜ`, and
`f : ℂ → F` a function into a complex normed space holomorphic on `U`. For every `ε > 0` there are
finitely many nodes `ζ i` and rational kernels `p i / q i` with poles in `A \ K` such that
`‖f w - ∑ i, ((p i).eval w / (q i).eval w) • f (ζ i)‖ < ε` for all `w ∈ K`. -/
theorem _root_.IsCompact.exists_rational_norm_sub_sum_smul_lt {K U A : Set ℂ} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U)
    (hA : ∀ x ∈ filledHull K \ K, (A ∩ connectedComponentIn Kᶜ x).Nonempty)
    {F : Type u} [NormedAddCommGroup F] [NormedSpace ℂ F] {f : ℂ → F}
    (hf : DifferentiableOn ℂ f U) {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : ℕ) (ζ : Fin N → ℂ) (p q : Fin N → ℂ[X]),
      (∀ i, q i ≠ 0) ∧ (∀ i z, (q i).eval z = 0 → z ∈ A \ K) ∧
      ∀ w ∈ K, ‖f w - ∑ i, ((p i).eval w / (q i).eval w) • f (ζ i)‖ < ε := by
  obtain ⟨L, hL, hKL, hLU⟩ := exists_compact_between hK hU hKU
  obtain ⟨M₀, hM₀⟩ := hL.bddAbove_image (hf.continuousOn.mono hLU).norm
  set M : ℝ := max M₀ 0
  have hM : ∀ z ∈ interior L, ‖f z‖ ≤ M := fun z hz ↦
    (hM₀ ⟨z, interior_subset hz, rfl⟩).trans (le_max_left _ _)
  obtain ⟨N, ζ, p, q, -, hq, hqA, hop⟩ := hK.exists_rational_norm_sub_sum_smul_le.{u}
    isOpen_interior hKL hA (ε := ε / (2 * (M + 1))) (by positivity)
  refine ⟨N, ζ, p, q, hq, hqA, fun w hw ↦ ?_⟩
  have hlt : ε / (2 * (M + 1)) * M < ε := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [le_max_right M₀ 0]
  exact (hop f M (hf.mono (interior_subset.trans hLU)) hM w hw).trans_lt hlt

/-- **Rational Runge approximation with prescribed poles.** Let `K ⊆ ℂ` be compact and `A ⊆ ℂ`
meet every bounded connected component of `Kᶜ`. Then every function holomorphic on an open
neighbourhood `U` of `K` can be uniformly approximated on `K` by rational functions whose finite
poles lie in `A \ K`. -/
theorem _root_.IsCompact.exists_rational_norm_sub_lt {K U A : Set ℂ} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U)
    (hA : ∀ x ∈ filledHull K \ K, (A ∩ connectedComponentIn Kᶜ x).Nonempty)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) {ε : ℝ} (hε : 0 < ε) :
    ∃ p q : ℂ[X], q ≠ 0 ∧ (∀ z, q.eval z = 0 → z ∈ A \ K) ∧
      ∀ z ∈ K, ‖f z - p.eval z / q.eval z‖ < ε := by
  obtain ⟨N, ζ, p_i, q_i, hq_i, hqA_i, happrox⟩ :=
    hK.exists_rational_norm_sub_sum_smul_lt hU hKU hA hf hε
  obtain ⟨p, q, hq, hqA, hval⟩ :=
    Polynomial.exists_eval_div_eq_sum_mul_div Finset.univ (fun i ↦ f (ζ i)) p_i q_i
      fun i _ ↦ hq_i i
  refine ⟨p, q, hq, fun z hz ↦ ?_, fun w hw ↦ ?_⟩
  · obtain ⟨i, -, hqi⟩ := hqA z hz
    exact hqA_i i z hqi
  · have hqne : ∀ i ∈ (Finset.univ : Finset (Fin N)), (q_i i).eval w ≠ 0 := fun i _ h0 ↦
      (hqA_i i w h0).2 hw
    have hsum : p.eval w / q.eval w = ∑ i, ((p_i i).eval w / (q_i i).eval w) • f (ζ i) := by
      rw [hval w hqne]
      exact Finset.sum_congr rfl fun i _ ↦ by simp [mul_comm]
    rw [hsum]
    exact happrox w hw

end TauCeti
