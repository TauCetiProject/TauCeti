/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.ENNReal.BigOperators
public import TauCeti.Data.Finsupp.Sum
public import TauCeti.Data.Finsupp.Weight

/-!
# Reciprocal natural weights in the extended nonnegative reals

For finitely many coordinates, the weight of `d` with reciprocal natural weights `r` is the
real sum of ratios `∑ i, d i / r i` whenever `d ≤ r`. The bound permits zero weights: their
exponents must also be zero, so they contribute zero to both sums. This identifies extended
nonnegative weights with ordinary real ratios without requiring every weight to be positive.

On a product `κ × ι` of blocks indexed by `κ`, the weight giving the coordinate `(h, i₀ h)` of
each block the reciprocal natural weight `(d h)⁻¹` and every other coordinate the weight `0` is
the sum `∑ h, n (h, i₀ h) / d h`. More generally, for a block map `b : S → B`, pulling the
reciprocal weights `(d h)⁻¹` back to `S` (`Finsupp.weight_inv_natCast_comp`) or to `B ⊕ S`
(`Finsupp.weight_inv_natCast_sumElim`) evaluates `(d h)⁻¹` on `γ.mapDomain b` or
`κ + β.mapDomain b`, and for finitely many blocks sums the block ratios
`γ.mapDomain b h / d h` or `(κ h + β.mapDomain b h) / d h`.
-/

public section

namespace Finsupp

open scoped ENNReal

variable {σ : Type*}

/-- If `d ≤ r`, the reciprocal natural weight of `d` in `ℝ≥0∞` is the real sum
`∑ᵢ dᵢ / rᵢ`. Zero weights are allowed, since their corresponding exponents are zero. -/
theorem weight_inv_natCast_eq_ofReal_sum_div [Fintype σ] {r : σ → ℕ}
    {d : σ →₀ ℕ} (hdr : ∀ i, d i ≤ r i) :
    d.weight (fun j ↦ (r j : ℝ≥0∞)⁻¹) = ENNReal.ofReal (∑ i, (d i : ℝ) / r i) := by
  rw [ENNReal.ofReal_sum_of_nonneg fun i _ ↦ by positivity, Finsupp.weight_apply,
    Finsupp.sum_fintype _ _ (by simp)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rcases Nat.eq_zero_or_pos (d i) with h | h
  · simp [h]
  · rw [ENNReal.ofReal_div_of_pos (Nat.cast_pos.2 (h.trans_le (hdr i))),
      ENNReal.ofReal_natCast, ENNReal.ofReal_natCast, nsmul_eq_mul, div_eq_mul_inv]

/-- On blocks `κ × ι`, the weight that is `(d h)⁻¹` at the coordinate `(h, i₀ h)` of each block
and `0` elsewhere is the sum `∑ h, n (h, i₀ h) / d h` in `ℝ≥0∞`. -/
theorem weight_ite_inv_natCast_eq_sum_div {κ ι : Type*} [Fintype κ] [Finite ι] [DecidableEq ι]
    (i₀ : κ → ι) (d : κ → ℕ) (n : κ × ι →₀ ℕ) :
    n.weight (fun p ↦ if p.2 = i₀ p.1 then (d p.1 : ℝ≥0∞)⁻¹ else 0) =
      ∑ h, (n (h, i₀ h) : ℝ≥0∞) / d h := by
  have := Fintype.ofFinite ι
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun h _ ↦ ?_
  rw [Fintype.sum_eq_single (i₀ h) fun i hi ↦ by simp [hi]]
  simp [div_eq_mul_inv]

/-- Pulling reciprocal natural weights `(d h)⁻¹` on blocks `B` back along a block map `b : S → B`
evaluates `(d h)⁻¹` on the block-degree pushforward `γ.mapDomain b`. -/
theorem weight_inv_natCast_comp {B S : Type*} (b : S → B) (d : B → ℕ) (γ : S →₀ ℕ) :
    γ.weight (fun j ↦ ((d ∘ b) j : ℝ≥0∞)⁻¹) =
      (γ.mapDomain b).weight (fun h ↦ (d h : ℝ≥0∞)⁻¹) :=
  (weight_mapDomain (fun h ↦ (d h : ℝ≥0∞)⁻¹) b γ).symm

/-- On `B ⊕ S`, reciprocal natural weights for `Sum.elim d (d ∘ b)` evaluate on `κ.sumElim β` to
the reciprocal natural weight of `κ + β.mapDomain b` on `B`. -/
theorem weight_inv_natCast_sumElim {B S : Type*} (b : S → B) (d : B → ℕ)
    (κ : B →₀ ℕ) (β : S →₀ ℕ) :
    (κ.sumElim β).weight (fun v ↦ ((Sum.elim d (d ∘ b) v : ℕ) : ℝ≥0∞)⁻¹) =
      (κ + β.mapDomain b).weight (fun h ↦ (d h : ℝ≥0∞)⁻¹) := by
  have hcomp : (fun v ↦ ((Sum.elim d (d ∘ b) v : ℕ) : ℝ≥0∞)⁻¹) =
      (fun h ↦ (d h : ℝ≥0∞)⁻¹) ∘ Sum.elim id b := by
    ext (_ | _) <;> rfl
  rw [hcomp, ← weight_mapDomain, mapDomain_sumElim, mapDomain_id]

/-- Pulling a reciprocal natural weight vector `(d h)⁻¹` on finitely many blocks `B` back along a
block map `b : S → B` sums the block degrees `γ.mapDomain b h / d h` in `ℝ≥0∞`. -/
theorem weight_inv_natCast_comp_eq_sum_mapDomain_div {B S : Type*} [Fintype B] (b : S → B)
    (d : B → ℕ) (γ : S →₀ ℕ) :
    γ.weight (fun j ↦ (d (b j) : ℝ≥0∞)⁻¹) = ∑ h, (γ.mapDomain b h : ℝ≥0∞) / d h := by
  rw [show (fun j ↦ (d (b j) : ℝ≥0∞)⁻¹) = fun j ↦ ((d ∘ b) j : ℝ≥0∞)⁻¹ from rfl,
    weight_inv_natCast_comp b d γ, weight_eq_sum]
  simp [div_eq_mul_inv]

/-- On `B ⊕ S`, giving `.inl h` and every `.inr j` with `b j = h` the reciprocal natural weight
`(d h)⁻¹` evaluates on `κ.sumElim β` to `∑ h, (κ h + β.mapDomain b h) / d h` in `ℝ≥0∞`. -/
theorem weight_inv_natCast_sumElim_eq_sum_div {B S : Type*} [Fintype B] (b : S → B)
    (d : B → ℕ) (κ : B →₀ ℕ) (β : S →₀ ℕ) :
    (κ.sumElim β).weight (fun v ↦ ((Sum.elim d (d ∘ b) v : ℕ) : ℝ≥0∞)⁻¹) =
      ∑ h, ((κ h + β.mapDomain b h : ℕ) : ℝ≥0∞) / d h := by
  rw [weight_inv_natCast_sumElim b d κ β, weight_eq_sum]
  simp [div_eq_mul_inv]

end Finsupp
