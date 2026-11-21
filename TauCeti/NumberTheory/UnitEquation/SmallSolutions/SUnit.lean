/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.SUnits.Packing
public import TauCeti.NumberTheory.UnitEquation.SmallSolutions.Basic

/-!
# Counting the nondegenerate solutions of small height

Let `Γ` be a group of `n`-tuples of `S`-units of a number field `K`, of rank at most `r`, and let
`q ≥ 1`. Evertse, Schlickewei and Schmidt split the solutions `y = x z` of a unit equation, with
`x ∈ Γ` and `z` a small perturbation, into those with `x` of small height and those with `x` of
large height. This file bounds the number of nondegenerate solutions in the first regime: those
with absolute affine logarithmic height `h_aff(x) ≤ 4 n log n` and scalar-sum height
`h_s(z) < 1 / (2 q)`.

For `n ≥ 1` the packing bound
`TauCeti.NumberField.SUnit.exists_finset_scalarSumHeight_div_lt_of_absoluteLogHeightAff_le`
gives at most `(16 n³ q) ^ r` centres `b ∈ Γ` such that each such `x` has `h_s(x / b) < 1 / (2 q)`
for one of them. Then `y = b w` with `w = (x / b) z`, and `h_s(w) < 1 / q` by subadditivity of
`h_s`. The general count `TauCeti.encard_isNondegenerateSolution_le_card_mul` turns this into the
bound: the solutions `y` number at most `⌊(16 n³ q) ^ r⌋` times the supremum in `ℕ∞`, over
`b ∈ Γ`, of the numbers of nondegenerate solutions of scalar-sum height less than `1 / q` of the
translated equation `∑ aᵢ bᵢ wᵢ = 1`. For `n = 0` there are no solutions, since the equation
reads `0 = 1`, so the bound holds without the packing. Both sides are cardinalities in `ℕ∞`, and
the statement holds unconditionally.

For `q = exp ((4 n) ^ (3 n))` Evertse, Schlickewei and Schmidt bound the second factor by `q`
(their Proposition 11.1, the bound for the nondegenerate points of small height on a hyperplane,
which rests on Schmidt's theorem on small points of subvarieties of tori). That bound is not
proved here; combined with it, the result below gives the count `q (16 n³ q) ^ r`.

## Main results

* `TauCeti.NumberField.SUnit.encard_isNondegenerateSolution_le_of_absoluteLogHeightAff_le`: the
  nondegenerate solutions `y = x z` with `x ∈ Γ`, `h_aff(x) ≤ 4 n log n` and `h_s(z) < 1 / (2 q)`
  number at most `⌊(16 n³ q) ^ r⌋` times the supremum in `ℕ∞`, over `b ∈ Γ`, of the numbers of
  nondegenerate solutions `w` with `h_s(w) < 1 / q` of the translated equation
  `∑ aᵢ bᵢ wᵢ = 1`.

## References

* J.-H. Evertse, H. P. Schlickewei and W. M. Schmidt, *Linear equations in variables
  which lie in a multiplicative group*, Annals of Mathematics 155 (2002), §§7–8, Lemma 11.2 and
  Corollary 11.3.
* W. M. Schmidt, *Heights of points on subvarieties of 𝔾ₘⁿ*, in: Number Theory (Paris 1993–94),
  London Math. Soc. Lecture Note Ser. 235, Cambridge University Press (1996), 157–187.
-/

public section

open Finset Height IsDedekindDomain NumberField

namespace TauCeti.NumberField.SUnit

variable {K : Type*} [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))

/-- **The nondegenerate solutions of small height.** Let `Γ` be a group of `n`-tuples of
`S`-units of rank at most `r`, and let `q ≥ 1`. The nondegenerate solutions of `∑ aᵢ yᵢ = 1` of
the form `y = x z`, with `x ∈ Γ` of absolute affine logarithmic height at most `4 n log n` and
`h_s(z) < 1 / (2 q)`, number at most `⌊(16 n³ q) ^ r⌋` times the supremum in `ℕ∞`, over `b ∈ Γ`,
of the numbers of nondegenerate solutions `w` with scalar-sum height `h_s(w) < 1 / q` of the
translated equation `∑ aᵢ bᵢ wᵢ = 1`. For `n = 0` there are no solutions, and the packing is
only used for `n ≥ 1`. -/
theorem encard_isNondegenerateSolution_le_of_absoluteLogHeightAff_le {n : ℕ}
    {Γ : Subgroup (Fin n → (S : Set (HeightOneSpectrum (𝓞 K))).unit K)} {r : ℕ}
    (hr : Module.rank ℤ (Additive Γ) ≤ r) {q : ℝ} (hq : 1 ≤ q) (a : Fin n → K) :
    {y : Fin n → K | IsNondegenerateSolution a y ∧ ∃ x ∈ Γ, ∃ z : Fin n → K,
      absoluteLogHeightAff (fun i ↦ ((x i : Kˣ) : K)) ≤ 4 * n * Real.log n ∧
        scalarSumHeight z < 1 / (2 * q) ∧ y = (fun i ↦ ((x i : Kˣ) : K)) * z}.encard ≤
      ⌊(16 * n ^ 3 * q) ^ r⌋₊ * ⨆ b ∈ Γ, {w : Fin n → K |
        IsNondegenerateSolution (a * fun i ↦ ((b i : Kˣ) : K)) w ∧
          scalarSumHeight w < 1 / q}.encard := by
  classical
  let v : (Fin n → (S : Set (HeightOneSpectrum (𝓞 K))).unit K) → Fin n → K :=
    fun b i ↦ ((b i : Kˣ) : K)
  -- With no unknowns the equation reads `0 = 1`.
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Set.encard_eq_zero.2 (Set.eq_empty_of_forall_notMem fun y hy ↦ by
      simpa using hy.1.sum_eq_one)]
    exact zero_le
  obtain ⟨B, hBΓ, hBcard, hcover⟩ :=
    exists_finset_scalarSumHeight_div_lt_of_absoluteLogHeightAff_le S hn hr hq
  calc _ ≤ {y | IsNondegenerateSolution a y ∧ ∃ b ∈ B.image v,
        ∃ w ∈ {w | scalarSumHeight w < 1 / q}, y = b * w}.encard := by
        refine Set.encard_le_encard fun y ⟨hyn, x, hxΓ, z, hx, hz, hy⟩ ↦ ?_
        obtain ⟨b, hb, hxb⟩ := hcover x hxΓ hx
        -- `y = b ((x / b) z)`, where `h_s((x / b) z) < 1 / (2 q) + 1 / (2 q) = 1 / q`.
        refine ⟨hyn, v b, mem_image_of_mem v hb, v (x / b) * z, ?_, ?_⟩
        · calc scalarSumHeight (v (x / b) * z) ≤ scalarSumHeight (v (x / b)) + scalarSumHeight z :=
                scalarSumHeight_mul_le _ _ (fun _ ↦ Algebra.IsAlgebraic.isAlgebraic _)
                  (fun _ ↦ Algebra.IsAlgebraic.isAlgebraic _)
            _ < 1 / (2 * q) + 1 / (2 * q) := add_lt_add hxb hz
            _ = 1 / q := by
                rw [← add_div, one_add_one_eq_two, div_mul_cancel_left₀ two_ne_zero, one_div]
        · rw [hy, ← mul_assoc]
          congr 1
          funext i
          simp only [v, Pi.mul_apply, Pi.div_apply, Subgroup.coe_div, Units.val_div_eq_div_val]
          exact (mul_div_cancel₀ _ (Units.ne_zero _)).symm
    _ ≤ #(B.image v) * ⨆ b ∈ B.image v,
        {w | IsNondegenerateSolution (a * b) w ∧ w ∈ {w | scalarSumHeight w < 1 / q}}.encard :=
        encard_isNondegenerateSolution_le_card_mul _ _ _
    _ ≤ _ := by
        rw [iSup_finset_image]
        exact mul_le_mul' (Nat.cast_le.2 (card_image_le.trans (Nat.le_floor hBcard)))
          (biSup_mono fun b hb ↦ hBΓ b hb)

end TauCeti.NumberField.SUnit
