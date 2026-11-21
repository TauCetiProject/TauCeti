/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Runge.SimpleFraction
import TauCeti.Analysis.Complex.Pompeiu.Discretization

/-!
# Finite-rank Runge approximation operators

Let `K` be a compact subset of an open set `Ω ⊆ ℂ` which is filled in `Ω` (`TauCeti.IsFilledIn K Ω`,
meaning no connected component of `Ω \ K` is relatively compact in `Ω`), and let `V ⊇ K` be open.
For every `ε > 0`, this file constructs finitely many evaluation points `ζ i ∈ V \ K`, weights
`c i : ℂ`, and holomorphic functions `g i : ℂ → ℂ` on `Ω` such that every function `f : ℂ → F`
into any complex normed space, holomorphic on `V` and bounded by `M` there, satisfies

`‖f w - ∑ i, (c i * g i w) • f (ζ i)‖ ≤ ε * M`  for all `w ∈ K`

(`TauCeti.IsFilledIn.exists_norm_sub_sum_mul_smul_le`). Writing
`A f w = ∑ i, (c i * g i w) • f (ζ i)` and taking `V = interior L` for a compact collar `L ⊆ U`
with `K ⊆ interior L` inside an open neighbourhood `U ⊇ K` on which `f` is holomorphic specializes
the estimate to `sup_K ‖f - A f‖ ≤ ε * sup_L ‖f‖` with `ζ i ∈ interior L \ K`. Because `ζ`, `c`,
and `g` depend only on `K`, `V`, `Ω`, and `ε` — neither on `f` nor on the target space `F` — the
resulting linear operator `A` commutes with differentiation in external smooth parameters and
preserves holomorphic dependence on external complex parameters.

The proof combines the discretized Cauchy–Pompeiu formula
(`IsCompact.exists_norm_sub_sum_mul_sub_inv_smul_le`), which approximates `f` uniformly on `K` by
fixed simple fractions `(w - ζ i)⁻¹`, with simple-fraction Runge approximation
(`TauCeti.IsFilledIn.exists_differentiableOn_norm_inv_sub_lt`), which replaces each `(w - ζ i)⁻¹`
on `K` by a function `g i` holomorphic on `Ω`. As an immediate consequence we obtain Runge's
approximation theorem for holomorphic maps into any complex normed space
(`TauCeti.IsFilledIn.exists_differentiableOn_norm_sub_lt`).

## Main results

* `TauCeti.IsFilledIn.exists_norm_sub_sum_mul_smul_le`: the finite-rank Runge operator with
  uniform error bound `ε * M`, independent of the target space `F`.
* `TauCeti.IsFilledIn.exists_differentiableOn_norm_sub_lt`: Runge's approximation theorem for
  holomorphic functions with values in a complex normed space.

## References

* A. Rainer, *Advanced Complex Analysis*, lecture notes, Theorems 10.3 and 11.1.
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed.,
  North-Holland, 1990, Theorem 1.3.1.
-/

public section

open Set

universe u

namespace TauCeti

/-- **The finite-rank Runge operator.** Let `K` be a compact subset filled in an open set `Ω ⊆ ℂ`,
and let `V ⊇ K` be open. For every `ε > 0` there are finitely many evaluation points `ζ i ∈ V \ K`,
weights `c i : ℂ`, and functions `g i : ℂ → ℂ` holomorphic on `Ω` such that every `f : ℂ → F`
into a complex normed space, holomorphic on `V` and bounded by `M` there, satisfies
`‖f w - ∑ i, (c i * g i w) • f (ζ i)‖ ≤ ε * M` for all `w ∈ K`.

The data `(N, ζ, c, g)` depend only on `K`, `V`, `Ω`, and `ε`, not on `f` or `F`. -/
theorem IsFilledIn.exists_norm_sub_sum_mul_smul_le {K V Ω : Set ℂ} (hfill : IsFilledIn K Ω)
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) (hV : IsOpen V) (hKV : K ⊆ V)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : ℕ) (ζ : Fin N → ℂ) (c : Fin N → ℂ) (g : Fin N → ℂ → ℂ),
      (∀ i, ζ i ∈ V \ K) ∧ (∀ i, DifferentiableOn ℂ (g i) Ω) ∧
      ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℂ F] (f : ℂ → F) (M : ℝ),
        DifferentiableOn ℂ f V → (∀ z ∈ V, ‖f z‖ ≤ M) →
        ∀ w ∈ K, ‖f w - ∑ i, (c i * g i w) • f (ζ i)‖ ≤ ε * M := by
  -- Discretize the Cauchy–Pompeiu formula at accuracy `ε / 2`, then approximate each pole on `K`.
  obtain ⟨N, ζ, c, hζ, hdisc⟩ :=
    hK.exists_norm_sub_sum_mul_sub_inv_smul_le.{u} hV hKV (half_pos hε)
  set S : ℝ := ∑ i, ‖c i‖
  have hδ : 0 < (ε / 2) / (S + 1) := by positivity
  have hrunge (i : Fin N) : ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Ω ∧
      ∀ w ∈ K, ‖(w - ζ i)⁻¹ - g w‖ < (ε / 2) / (S + 1) :=
    hfill.exists_differentiableOn_norm_inv_sub_lt hΩ hK hKΩ (hζ i).2 hδ
  choose g hg hgap using hrunge
  refine ⟨N, ζ, c, g, hζ, hg, fun {F} _ _ f M hf hM w hw ↦ ?_⟩
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM w (hKV hw))
  have hsplit : f w - ∑ i, (c i * g i w) • f (ζ i) =
      (f w - ∑ i, (c i * (w - ζ i)⁻¹) • f (ζ i)) +
        ∑ i, (c i * ((w - ζ i)⁻¹ - g i w)) • f (ζ i) := by
    simp_rw [mul_sub, sub_smul, Finset.sum_sub_distrib]
    abel
  have htail : ‖∑ i, (c i * ((w - ζ i)⁻¹ - g i w)) • f (ζ i)‖ ≤ ε / 2 * M := by
    calc
      ‖∑ i, (c i * ((w - ζ i)⁻¹ - g i w)) • f (ζ i)‖
          ≤ ∑ i, ‖(c i * ((w - ζ i)⁻¹ - g i w)) • f (ζ i)‖ := norm_sum_le _ _
      _ ≤ ∑ i, ‖c i‖ * ((ε / 2) / (S + 1)) * M := by
        refine Finset.sum_le_sum fun i _ ↦ ?_
        rw [norm_smul, norm_mul]
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hgap i w hw).le (norm_nonneg _))
          (hM (ζ i) (hζ i).1) (norm_nonneg _) (by positivity)
      _ = S * ((ε / 2) / (S + 1)) * M := by simp only [← Finset.sum_mul, S]
      _ ≤ (S + 1) * ((ε / 2) / (S + 1)) * M := by gcongr; linarith
      _ = ε / 2 * M := by rw [mul_div_cancel₀ _ (by positivity)]
  rw [hsplit]
  calc
    ‖(f w - ∑ i, (c i * (w - ζ i)⁻¹) • f (ζ i)) +
        ∑ i, (c i * ((w - ζ i)⁻¹ - g i w)) • f (ζ i)‖
        ≤ ‖f w - ∑ i, (c i * (w - ζ i)⁻¹) • f (ζ i)‖ +
          ‖∑ i, (c i * ((w - ζ i)⁻¹ - g i w)) • f (ζ i)‖ := norm_add_le _ _
    _ ≤ ε / 2 * M + ε / 2 * M := add_le_add (hdisc f M hf hM w hw) htail
    _ = ε * M := by ring

/-- **Runge's approximation theorem** for functions into a complex normed space. If a compact set
`K` is filled in an open set `Ω ⊆ ℂ` and `f : ℂ → F` is holomorphic on an open neighbourhood `V`
of `K`, then `f` is uniformly approximable on `K` by functions holomorphic on `Ω`. -/
theorem IsFilledIn.exists_differentiableOn_norm_sub_lt {K V Ω : Set ℂ} (hfill : IsFilledIn K Ω)
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) (hV : IsOpen V) (hKV : K ⊆ V)
    {F : Type u} [NormedAddCommGroup F] [NormedSpace ℂ F] {f : ℂ → F}
    (hf : DifferentiableOn ℂ f V) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℂ → F, DifferentiableOn ℂ g Ω ∧ ∀ w ∈ K, ‖f w - g w‖ < ε := by
  obtain ⟨L, hL, hKL, hLV⟩ := exists_compact_between hK hV hKV
  obtain ⟨M, hM⟩ := hL.exists_bound_of_continuousOn (hf.continuousOn.mono hLV)
  set M' : ℝ := max M 1
  have hM' : 0 < M' := lt_of_lt_of_le zero_lt_one (le_max_right M 1)
  obtain ⟨N, ζ, c, g, -, hg, happrox⟩ :=
    hfill.exists_norm_sub_sum_mul_smul_le.{u} hΩ hK hKΩ isOpen_interior hKL
      (ε := (ε / 2) / M') (by positivity)
  refine ⟨fun w ↦ ∑ i, (c i * g i w) • f (ζ i), ?_, fun w hw ↦ ?_⟩
  · exact DifferentiableOn.fun_sum fun i _ ↦ ((hg i).const_mul (c i)).smul_const (f (ζ i))
  · have hle := happrox f M' (hf.mono (interior_subset.trans hLV))
      (fun z hz ↦ (hM z (interior_subset hz)).trans (le_max_left M 1)) w hw
    rw [div_mul_cancel₀ _ hM'.ne'] at hle
    exact hle.trans_lt (half_lt_self hε)

end TauCeti
