/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.SUnits.Packing
public import TauCeti.NumberTheory.UnitEquation.Nondegenerate

/-!
# Counting the nondegenerate solutions of small height

Let `Γ` be a group of `n`-tuples of `S`-units of a number field `K`, of rank at most `r`, and let
`q ≥ 1`; for smaller `q` the hypothesis below leaves no such solutions. Evertse, Schlickewei and
Schmidt split the solutions `y = x z` of a unit equation, with `x ∈ Γ` and `z` a small
perturbation, into those with `x` of small height and those with `x` of large height. This file
counts the nondegenerate solutions in the first regime: those with absolute affine logarithmic
height `h_aff(x) ≤ 4 n log n` and scalar-sum height `h_s(z) < 1 / (2 q)`.

The packing bound
`TauCeti.NumberField.SUnit.exists_finset_scalarSumHeight_div_lt_of_absoluteLogHeightAff_le`
gives at most `(16 n³ q) ^ r` centres `b ∈ Γ` such that each such `x` has `h_s(x / b) < 1 / (2 q)`
for one of them. Then `w = y / b = (x / b) z` has `h_s(w) < 1 / q`, and it is a nondegenerate
solution of the translated equation `∑ aᵢ bᵢ wᵢ = 1` exactly when `y` is one of `∑ aᵢ yᵢ = 1`
(`TauCeti.isNondegenerateSolution_mul_div_iff`). Distinct solutions `y` with the same centre give
distinct points `w`. So if each translated equation has at most `q` nondegenerate solutions of
scalar-sum height less than `1 / q`, there are at most `q (16 n³ q) ^ r` nondegenerate solutions
`y`.

That bound for the translated equations is a hypothesis here, which this file does not prove.
For `q = exp ((4 n) ^ (3 n))` and arbitrary nonzero coefficients it is the bound of
Evertse, Schlickewei and Schmidt for the nondegenerate points of small height on a hyperplane
(their Proposition 11.1, which rests on Schmidt's theorem on small points of subvarieties of
tori). The counting step itself, `TauCeti.card_le_card_mul_of_scalarSumHeight_div_lt`, holds over
every field of characteristic zero and for every finite set of centres.

## Main results

* `TauCeti.card_le_card_mul_of_scalarSumHeight_div_lt`: nondegenerate solutions within scalar-sum
  distance `ε` of a finite set `B` of centres number at most `|B|` times a bound for the small
  nondegenerate solutions of the translated equations.
* `TauCeti.NumberField.SUnit.card_le_of_absoluteLogHeightAff_le`: the nondegenerate solutions
  `y = x z` with `x ∈ Γ`, `h_aff(x) ≤ 4 n log n` and `h_s(z) < 1 / (2 q)` number at most
  `q (16 n³ q) ^ r`, given the bound `q` for the translated equations.

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
coordinates such that, for each `b ∈ B`, every finite set of nondegenerate solutions `w` of
`∑ aᵢ bᵢ wᵢ = 1` with scalar-sum height `h_s(w) < ε` has at most `Q` elements. Then every finite
set of nondegenerate solutions `y` of `∑ aᵢ yᵢ = 1`, each with `h_s(y / b) < ε` for some `b ∈ B`,
has at most `|B| Q` elements. -/
theorem card_le_card_mul_of_scalarSumHeight_div_lt {a : ι → F} {B : Finset (ι → F)}
    (hB : ∀ b ∈ B, ∀ i, b i ≠ 0) {ε Q : ℝ}
    (hQ : ∀ b ∈ B, ∀ N : Finset (ι → F),
      (∀ w ∈ N, IsNondegenerateSolution (a * b) w ∧ scalarSumHeight w < ε) → (#N : ℝ) ≤ Q)
    {M : Finset (ι → F)}
    (hM : ∀ y ∈ M, IsNondegenerateSolution a y ∧ ∃ b ∈ B, scalarSumHeight (y / b) < ε) :
    (#M : ℝ) ≤ #B * Q := by
  classical
  choose! c hcB hc using fun y hy ↦ (hM y hy).2
  -- Dividing by the centre `b` maps the solutions with centre `b` injectively to small
  -- nondegenerate solutions of the translated equation.
  have hfib (b : ι → F) (hb : b ∈ B) : (#{y ∈ M | c y = b} : ℝ) ≤ Q := by
    have hinj : Set.InjOn (· / b) ({y ∈ M | c y = b} : Finset (ι → F)) := fun y _ y' _ h ↦
      funext fun i ↦ (div_left_inj₀ (hB b hb i)).1 (congrFun h i)
    rw [← card_image_of_injOn hinj]
    refine hQ b hb _ fun w hw ↦ ?_
    obtain ⟨y, hy, rfl⟩ := mem_image.1 hw
    obtain ⟨hyM, rfl⟩ := mem_filter.1 hy
    exact ⟨(isNondegenerateSolution_mul_div_iff (hB _ hb)).2 (hM y hyM).1, hc y hyM⟩
  calc (#M : ℝ) = ∑ b ∈ B, (#{y ∈ M | c y = b} : ℝ) := by
        exact_mod_cast card_eq_sum_card_fiberwise fun y hy ↦ hcB y hy
    _ ≤ ∑ _b ∈ B, Q := sum_le_sum hfib
    _ = #B * Q := by rw [sum_const, nsmul_eq_mul]

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
`S`-units of rank at most `r`, and let `q` be real. Suppose that, for every `b ∈ Γ`, every finite
set of nondegenerate solutions `w` of `∑ aᵢ bᵢ wᵢ = 1` with scalar-sum height `h_s(w) < 1 / q`
has at most `q` elements. Then every finite set of nondegenerate solutions of `∑ aᵢ yᵢ = 1` of
the form `y = x z`, with `x ∈ Γ` of absolute affine logarithmic height at most `4 n log n` and
`h_s(z) < 1 / (2 q)`, has at most `q (16 n³ q) ^ r` elements. -/
theorem card_le_of_absoluteLogHeightAff_le {n : ℕ}
    {Γ : Subgroup (Fin n → (S : Set (HeightOneSpectrum (𝓞 K))).unit K)} {r : ℕ}
    (hr : Module.rank ℤ (Additive Γ) ≤ r) {q : ℝ} (a : Fin n → K)
    (hsmall : ∀ b ∈ Γ, ∀ N : Finset (Fin n → K),
      (∀ w ∈ N, IsNondegenerateSolution (a * fun i ↦ ((b i : Kˣ) : K)) w ∧
        scalarSumHeight w < 1 / q) → (#N : ℝ) ≤ q)
    {M : Finset (Fin n → K)}
    (hM : ∀ y ∈ M, IsNondegenerateSolution a y ∧ ∃ x ∈ Γ, ∃ z : Fin n → K,
      absoluteLogHeightAff (fun i ↦ ((x i : Kˣ) : K)) ≤ 4 * n * Real.log n ∧
        scalarSumHeight z < 1 / (2 * q) ∧ y = (fun i ↦ ((x i : Kˣ) : K)) * z) :
    (#M : ℝ) ≤ q * (16 * n ^ 3 * q) ^ r := by
  classical
  let v : (Fin n → (S : Set (HeightOneSpectrum (𝓞 K))).unit K) → Fin n → K :=
    fun b i ↦ ((b i : Kˣ) : K)
  have hv (b) : ∀ i, v b i ≠ 0 := fun i ↦ Units.ne_zero _
  have hq0 : 0 ≤ q := by simpa using hsmall 1 Γ.one_mem ∅ (by simp)
  -- With no unknowns the equation reads `0 = 1`. For `q < 1` the centre `x` itself would make
  -- `{y / x}` a set of one small nondegenerate solution of a translated equation.
  by_cases hnq : 0 < n ∧ 1 ≤ q
  swap
  · have hM0 : M = ∅ := eq_empty_of_forall_notMem fun y hy ↦ by
      obtain ⟨hyn, x, hxΓ, z, -, hz, rfl⟩ := hM y hy
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simpa using hyn.sum_eq_one
      have hxx : scalarSumHeight (fun i ↦ (((x / x) i : Kˣ) : K)) < 1 / (2 * q) := by
        simpa [scalarSumHeight_def] using (scalarSumHeight_nonneg z).trans_lt hz
      have h1 := hsmall x hxΓ {v x * z / v x} fun w hw ↦ by
        rw [mem_singleton.1 hw]
        exact ⟨(isNondegenerateSolution_mul_div_iff (hv x)).2 hyn,
          scalarSumHeight_mul_div_lt S hxx hz⟩
      rw [card_singleton, Nat.cast_one] at h1
      exact hnq ⟨hn, h1⟩
    rw [hM0, card_empty, Nat.cast_zero]
    positivity
  obtain ⟨B, hBΓ, hBcard, hcover⟩ :=
    exists_finset_scalarSumHeight_div_lt_of_absoluteLogHeightAff_le S hnq.1 hr hnq.2
  have hcount := card_le_card_mul_of_scalarSumHeight_div_lt (B := B.image v) (ε := 1 / q)
    (fun _ hb ↦ by
      obtain ⟨b, -, rfl⟩ := mem_image.1 hb
      exact hv b)
    (fun _ hb N hN ↦ by
      obtain ⟨b, hbB, rfl⟩ := mem_image.1 hb
      exact hsmall b (hBΓ b hbB) N hN)
    (M := M) fun y hy ↦ by
      obtain ⟨hyn, x, hxΓ, z, hx, hz, rfl⟩ := hM y hy
      obtain ⟨b, hb, hxb⟩ := hcover x hxΓ hx
      exact ⟨hyn, v b, mem_image_of_mem v hb, scalarSumHeight_mul_div_lt S hxb hz⟩
  calc (#M : ℝ) ≤ #(B.image v) * q := hcount
    _ ≤ #B * q := by gcongr; exact_mod_cast card_image_le
    _ ≤ (16 * n ^ 3 * q) ^ r * q := by gcongr
    _ = q * (16 * n ^ 3 * q) ^ r := mul_comm _ _

end TauCeti.NumberField.SUnit
