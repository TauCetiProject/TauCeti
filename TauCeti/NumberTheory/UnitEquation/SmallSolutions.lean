/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Card.Arithmetic
public import TauCeti.NumberTheory.NumberField.SUnits.Packing
public import TauCeti.NumberTheory.UnitEquation.Nondegenerate

/-!
# Counting the nondegenerate solutions of small height

Let `Γ` be a group of `n`-tuples of `S`-units of a number field `K`, of rank at most `r`, and let
`q ≥ 1`. Evertse, Schlickewei and Schmidt split the solutions `y = x z` of a unit equation, with
`x ∈ Γ` and `z` a small perturbation, into those with `x` of small height and those with `x` of
large height. This file bounds the number of nondegenerate solutions in the first regime: those
with absolute affine logarithmic height `h_aff(x) ≤ 4 n log n` and scalar-sum height
`h_s(z) < 1 / (2 q)`.

The packing bound
`TauCeti.NumberField.SUnit.exists_finset_scalarSumHeight_div_lt_of_absoluteLogHeightAff_le`
gives at most `(16 n³ q) ^ r` centres `b ∈ Γ` such that each such `x` has `h_s(x / b) < 1 / (2 q)`
for one of them. Then `w = y / b = (x / b) z` has `h_s(w) < 1 / q`, and it is a nondegenerate
solution of the translated equation `∑ aᵢ bᵢ wᵢ = 1` exactly when `y` is one of `∑ aᵢ yᵢ = 1`
(`TauCeti.isNondegenerateSolution_mul_div_iff`). Distinct solutions `y` with the same centre give
distinct points `w`. So the solutions `y` number at most `⌊(16 n³ q) ^ r⌋` times the largest
number of nondegenerate solutions of scalar-sum height less than `1 / q` of a translated
equation. Both sides are cardinalities in `ℕ∞`, and the statement holds unconditionally.

For `q = exp ((4 n) ^ (3 n))` Evertse, Schlickewei and Schmidt bound the second factor by `q`
(their Proposition 11.1, the bound for the nondegenerate points of small height on a hyperplane,
which rests on Schmidt's theorem on small points of subvarieties of tori). That bound is not
proved here; combined with it, the result below gives the count `q (16 n³ q) ^ r`. The counting
step itself, `TauCeti.encard_le_card_mul_of_scalarSumHeight_div_lt`, holds over every field of
characteristic zero and for every finite set of centres.

## Main results

* `TauCeti.encard_le_card_mul_of_scalarSumHeight_div_lt`: nondegenerate solutions within
  scalar-sum distance `ε` of a finite set `B` of centres number at most `|B|` times the largest
  number of small nondegenerate solutions of a translated equation.
* `TauCeti.NumberField.SUnit.encard_le_of_absoluteLogHeightAff_le`: the nondegenerate solutions
  `y = x z` with `x ∈ Γ`, `h_aff(x) ≤ 4 n log n` and `h_s(z) < 1 / (2 q)` number at most
  `⌊(16 n³ q) ^ r⌋` times the largest number of nondegenerate solutions `w` with
  `h_s(w) < 1 / q` of a translated equation `∑ aᵢ bᵢ wᵢ = 1`, `b ∈ Γ`.

## References

* J.-H. Evertse, H. P. Schlickewei and W. M. Schmidt, *Linear equations in variables
  which lie in a multiplicative group*, Annals of Mathematics 155 (2002), §§7–8, Lemma 11.2 and
  Corollary 11.3.
* W. M. Schmidt, *Heights of points on subvarieties of 𝔾ₘⁿ*, in: Number Theory (Paris 1993–94),
  London Math. Soc. Lecture Note Ser. 235, Cambridge University Press (1996), 157–187.
-/

public section

open Finset

namespace TauCeti

variable {F : Type*} [Field F] [CharZero F] {ι : Type*} [Fintype ι]

/-- **Counting solutions through centres.** Let `B` be a finite set of tuples with nonzero
coordinates. The nondegenerate solutions `y` of `∑ aᵢ yᵢ = 1` with `h_s(y / b) < ε` for some
`b ∈ B` number at most `|B|` times the largest number of nondegenerate solutions `w` of a
translated equation `∑ aᵢ bᵢ wᵢ = 1`, `b ∈ B`, with scalar-sum height `h_s(w) < ε`. -/
theorem encard_le_card_mul_of_scalarSumHeight_div_lt {a : ι → F} {B : Finset (ι → F)}
    (hB : ∀ b ∈ B, ∀ i, b i ≠ 0) (ε : ℝ) :
    {y | IsNondegenerateSolution a y ∧ ∃ b ∈ B, scalarSumHeight (y / b) < ε}.encard ≤
      #B * ⨆ b ∈ B, {w | IsNondegenerateSolution (a * b) w ∧ scalarSumHeight w < ε}.encard := by
  set T : (ι → F) → Set (ι → F) :=
    fun b ↦ {w | IsNondegenerateSolution (a * b) w ∧ scalarSumHeight w < ε}
  -- Each solution `y` with centre `b` is the image of the small solution `y / b` of the
  -- translated equation under multiplication by `b`.
  calc _ ≤ (⋃ b ∈ B, (· * b) '' T b).encard := by
        refine Set.encard_le_encard fun y ⟨hy, b, hb, hyb⟩ ↦ Set.mem_iUnion₂.2 ⟨b, hb, y / b,
          ⟨(isNondegenerateSolution_mul_div_iff (hB b hb)).2 hy, hyb⟩, ?_⟩
        exact funext fun i ↦ div_mul_cancel₀ _ (hB b hb i)
    _ ≤ ∑ b ∈ B, ((· * b) '' T b).encard := B.set_encard_biUnion_le _
    _ ≤ ∑ b ∈ B, (T b).encard := sum_le_sum fun b _ ↦ Set.encard_image_le _ _
    _ ≤ #B • ⨆ b ∈ B, (T b).encard :=
        sum_le_card_nsmul _ _ _ fun b hb ↦ le_iSup₂ (f := fun b (_ : b ∈ B) ↦ (T b).encard) b hb
    _ = _ := nsmul_eq_mul _ _

end TauCeti

open Height IsDedekindDomain NumberField

namespace TauCeti.NumberField.SUnit

variable {K : Type*} [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))

/-- Translating a perturbed tuple by a centre: if `h_s(x / b) < 1 / (2 q)` and
`h_s(z) < 1 / (2 q)`, then `h_s(x z / b) < 1 / q`. -/
private theorem scalarSumHeight_mul_div_lt {n : ℕ}
    {x b : Fin n → (S : Set (HeightOneSpectrum (𝓞 K))).unit K} {z : Fin n → K} {q : ℝ}
    (hxb : scalarSumHeight (fun i ↦ (((x / b) i : Kˣ) : K)) < 1 / (2 * q))
    (hz : scalarSumHeight z < 1 / (2 * q)) :
    scalarSumHeight ((fun i ↦ ((x i : Kˣ) : K)) * z / fun i ↦ ((b i : Kˣ) : K)) < 1 / q := by
  have hxzb : (fun i ↦ ((x i : Kˣ) : K)) * z / (fun i ↦ ((b i : Kˣ) : K)) =
      (fun i ↦ (((x / b) i : Kˣ) : K)) * z := by
    ext i
    simp only [Pi.mul_apply, Pi.div_apply, Subgroup.coe_div, Units.val_div_eq_div_val]
    ring
  rw [hxzb]
  calc _ ≤ scalarSumHeight (fun i ↦ (((x / b) i : Kˣ) : K)) + scalarSumHeight z :=
        scalarSumHeight_mul_le _ _ (fun _ ↦ Algebra.IsAlgebraic.isAlgebraic _)
          (fun _ ↦ Algebra.IsAlgebraic.isAlgebraic _)
    _ < 1 / (2 * q) + 1 / (2 * q) := add_lt_add hxb hz
    _ = 1 / q := by field_simp; ring

/-- **The nondegenerate solutions of small height.** Let `Γ` be a group of `n`-tuples of
`S`-units of rank at most `r`, and let `q ≥ 1`. The nondegenerate solutions of `∑ aᵢ yᵢ = 1` of
the form `y = x z`, with `x ∈ Γ` of absolute affine logarithmic height at most `4 n log n` and
`h_s(z) < 1 / (2 q)`, number at most `⌊(16 n³ q) ^ r⌋` times the largest number of nondegenerate
solutions `w` with scalar-sum height `h_s(w) < 1 / q` of a translated equation
`∑ aᵢ bᵢ wᵢ = 1`, `b ∈ Γ`. -/
theorem encard_le_of_absoluteLogHeightAff_le {n : ℕ}
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
  calc _ ≤ {y | IsNondegenerateSolution a y ∧
        ∃ b ∈ B.image v, scalarSumHeight (y / b) < 1 / q}.encard := by
        refine Set.encard_le_encard fun y ⟨hyn, x, hxΓ, z, hx, hz, hy⟩ ↦ ?_
        obtain ⟨b, hb, hxb⟩ := hcover x hxΓ hx
        exact ⟨hyn, v b, mem_image_of_mem v hb, hy ▸ scalarSumHeight_mul_div_lt S hxb hz⟩
    _ ≤ #(B.image v) * ⨆ b ∈ B.image v,
        {w | IsNondegenerateSolution (a * b) w ∧ scalarSumHeight w < 1 / q}.encard :=
        encard_le_card_mul_of_scalarSumHeight_div_lt (fun _ hb ↦ by
          obtain ⟨b, -, rfl⟩ := mem_image.1 hb
          exact fun i ↦ Units.ne_zero _) _
    _ ≤ _ := by
        gcongr
        · exact card_image_le.trans (Nat.le_floor hBcard)
        · refine iSup₂_le fun _ hb ↦ ?_
          obtain ⟨b, hbB, rfl⟩ := mem_image.1 hb
          exact le_iSup₂_of_le (f := fun b (_ : b ∈ Γ) ↦ {w : Fin n → K |
            IsNondegenerateSolution (a * v b) w ∧ scalarSumHeight w < 1 / q}.encard)
            b (hBΓ b hbB) le_rfl

end TauCeti.NumberField.SUnit
