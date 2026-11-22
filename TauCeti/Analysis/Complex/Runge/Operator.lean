/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Topology.FilledIn
import TauCeti.Analysis.Complex.Pompeiu.Discretization
import TauCeti.Analysis.Complex.Runge.SimpleFraction

/-!
# The finite-rank Runge approximation operator

A **Runge compact pair** `TauCeti.IsRungeCompactPair Ω K` consists of an open set `Ω ⊆ ℂ` and a
compact subset `K ⊆ Ω` that is filled in `Ω` (`TauCeti.IsFilledIn K Ω`, meaning no connected
component of `Ω \ K` is relatively compact in `Ω`).

For any compact set `K` filled in an open set `Ω ⊆ ℂ` and any open neighbourhood `V ⊇ K`, this
file constructs finitely many evaluation points `ζ i ∈ V \ K`, weights `c i : ℂ`, and holomorphic
functions `g i : ℂ → ℂ` on `Ω` — all independent of `f` and of the target complex normed space `F`
— such that every `V`-holomorphic function `f : ℂ → F` bounded by `M` on `V` satisfies

`‖f w - ∑ i, (c i * g i w) • f (ζ i)‖ ≤ ε * M`  for all `w ∈ K`

(`TauCeti.IsFilledIn.exists_norm_sub_sum_mul_smul_le`). Specializing `V` to the interior of a
compact collar `L ⊆ U ∩ Ω` around `K` inside an open neighbourhood `U ⊇ K` yields uniform Runge
approximation in any complex normed space (`TauCeti.Analysis.Complex.Runge.Approximation`), while
applying the finite-rank operator fiberwise preserves continuous, smooth, and holomorphic dependence
on external parameters (`TauCeti.Analysis.Complex.Runge.FiniteRank`).

The proof combines the discretized Cauchy–Pompeiu formula
(`IsCompact.exists_norm_sub_sum_mul_sub_inv_smul_le`), which approximates `f` uniformly on `K` by
fixed simple fractions `(w - ζ i)⁻¹`, with simple-fraction Runge approximation
(`TauCeti.IsFilledIn.exists_differentiableOn_norm_inv_sub_lt`), which replaces each `(w - ζ i)⁻¹`
on `K` by a function `g i` holomorphic on `Ω`.

## Main declarations and results

* `TauCeti.IsRungeCompactPair`: predicate asserting `IsOpen Ω`, `IsCompact K`, `K ⊆ Ω`, and
  `TauCeti.IsFilledIn K Ω`, with projection eliminators and `@[simp]` empty-set normal forms.
* `TauCeti.IsFilledIn.exists_norm_sub_sum_mul_smul_le`: existence of the finite-rank evaluation
  operator with uniform operator error bound `ε * M`, independent of the function and target space.

## References

* A. Rainer, *Advanced Complex Analysis*, Theorems 10.3 and 11.1.
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed.,
  Theorem 1.3.9.
-/

public section

open Set

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

end TauCeti
