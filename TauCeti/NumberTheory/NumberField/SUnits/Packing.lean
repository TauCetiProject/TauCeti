/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.CoveringNumber
public import TauCeti.NumberTheory.NumberField.SUnits.ScalarHeightNorm

/-!
# Packing groups of `S`-unit tuples of finite rank by the scalar height

Let `Γ` be a group of tuples of `S`-units of a number field, of rank at most `r`, and measure a
tuple `x` by its scalar-sum height `h_s(x) = ∑ i, h(x i)`. The distance `h_s(x / y)` between two
tuples vanishes exactly when `x / y` is torsion. This file proves the packing bound for it:
a finite subset of `Γ` in which `h_s ≤ C` and whose distinct points satisfy `h_s(x / y) ≥ δ > 0`
has at most `(1 + 2 C / δ) ^ r` elements. Consequently the tuples of `Γ` with `h_s ≤ C` lie within
`h_s`-distance less than `δ` of at most `(1 + 2 C / δ) ^ r` of them.

The scalar-sum height is a seminorm of the logarithmic images of the coordinates
(`TauCeti.NumberField.SUnit.scalarSumHeightSeminorm_logEmbedding`), so this is the volumetric
packing bound `Seminorm.card_le_of_rank_le` in the real span of the logarithmic image of `Γ`.
Torsion has zero logarithms, and the bound does not depend on its size or on the field.

With `C = 4 n² log n` and `δ = 1 / (2 q)` for `n`-tuples and `q ≥ 1`, the tuples of absolute
affine logarithmic height at most `4 n log n` lie within scalar-sum distance less than `1 / (2 q)`
of at most `(16 n³ q) ^ r` centres in `Γ`. This is the small-height regime in counting the
solutions of unit equations in groups of finite rank, where the centres translate the equation
to one with solutions of small height.

## Main results

* `TauCeti.NumberField.SUnit.card_le_of_scalarSumHeight_le`: the packing bound.
* `TauCeti.NumberField.SUnit.exists_finset_scalarSumHeight_div_lt`: at most `(1 + 2 C / δ) ^ r`
  centres in `Γ` for the tuples of `Γ` with `h_s ≤ C`.
* `TauCeti.NumberField.SUnit.exists_finset_scalarSumHeight_div_lt_of_absoluteLogHeightAff_le`:
  at most `(16 n³ q) ^ r` centres for the tuples of affine height at most `4 n log n`.

## References

* J.-H. Evertse, H. P. Schlickewei and W. M. Schmidt, *Linear equations in variables
  which lie in a multiplicative group*, Annals of Mathematics 155 (2002), §§7–8 and §11.
-/

public section

open Height IsDedekindDomain NumberField

namespace TauCeti.NumberField.SUnit

variable {K : Type*} [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable {κ : Type*} [Fintype κ]

/-- The coordinatewise `S`-logarithmic embedding of a group of tuples of `S`-units. -/
private noncomputable def tupleLogEmbedding
    (Γ : Subgroup (κ → (S : Set (HeightOneSpectrum (𝓞 K))).unit K)) :
    Additive Γ →+ (κ → logSpace S) :=
  AddMonoidHom.pi fun k ↦ (logEmbedding S).comp ((Pi.evalMonoidHom _ k).comp Γ.subtype).toAdditive

omit [Fintype κ] in
/-- The coordinates of the logarithmic image are the logarithms of the coordinates. -/
private theorem tupleLogEmbedding_ofMul
    (Γ : Subgroup (κ → (S : Set (HeightOneSpectrum (𝓞 K))).unit K)) (x : Γ) :
    tupleLogEmbedding S Γ (Additive.ofMul x) = fun k ↦ logEmbedding S (Additive.ofMul (x.val k)) :=
  (rfl)

/-- The scalar-sum height seminorm of the logarithmic image is the scalar-sum height. -/
private theorem scalarSumHeightSeminorm_tupleLogEmbedding
    (Γ : Subgroup (κ → (S : Set (HeightOneSpectrum (𝓞 K))).unit K)) (x : Γ) :
    scalarSumHeightSeminorm S (tupleLogEmbedding S Γ (Additive.ofMul x)) =
      scalarSumHeight (fun k ↦ ((x.val k : Kˣ) : K)) := by
  rw [tupleLogEmbedding_ofMul, scalarSumHeightSeminorm_logEmbedding]

/-- The scalar-sum height seminorm of the logarithmic image of a difference is the scalar-sum
height of the quotient. -/
private theorem scalarSumHeightSeminorm_tupleLogEmbedding_sub
    (Γ : Subgroup (κ → (S : Set (HeightOneSpectrum (𝓞 K))).unit K)) (x y : Γ) :
    scalarSumHeightSeminorm S
        (tupleLogEmbedding S Γ (Additive.ofMul x) - tupleLogEmbedding S Γ (Additive.ofMul y)) =
      scalarSumHeight (fun k ↦ (((x.val / y.val) k : Kˣ) : K)) := by
  rw [← map_sub, ← ofMul_div, scalarSumHeightSeminorm_tupleLogEmbedding, Subgroup.coe_div]

/-- **Packing by the scalar height.** In a group `Γ` of tuples of `S`-units of rank at most `r`,
a finite set of tuples of scalar-sum height at most `C ≥ 0`, any two distinct of which have
quotient of scalar-sum height at least `δ > 0`, has at most `(1 + 2 C / δ) ^ r` elements. -/
theorem card_le_of_scalarSumHeight_le
    {Γ : Subgroup (κ → (S : Set (HeightOneSpectrum (𝓞 K))).unit K)} {r : ℕ}
    (hr : Module.rank ℤ (Additive Γ) ≤ r)
    {s : Finset (κ → (S : Set (HeightOneSpectrum (𝓞 K))).unit K)} (hsΓ : ∀ x ∈ s, x ∈ Γ)
    {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 < δ)
    (hsC : ∀ x ∈ s, scalarSumHeight (fun k ↦ ((x k : Kˣ) : K)) ≤ C)
    (hsδ : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → δ ≤ scalarSumHeight (fun k ↦ (((x / y) k : Kˣ) : K))) :
    (s.card : ℝ) ≤ (1 + 2 * C / δ) ^ r := by
  classical
  let t : Finset (Additive Γ) := (s.subtype (· ∈ Γ)).map Additive.ofMul.toEmbedding
  have ht : t.card = s.card := by
    rw [Finset.card_map, Finset.card_subtype, Finset.filter_true_of_mem hsΓ]
  have hmem {x : Additive Γ} (hx : x ∈ t) : x.toMul.val ∈ s := by
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.1 hx
    exact Finset.mem_subtype.1 hy
  rw [← ht]
  refine Seminorm.card_le_of_rank_le (scalarSumHeightSeminorm S) (tupleLogEmbedding S Γ) hr hC hδ
    (fun x hx ↦ ?_) (fun x hx y hy hxy ↦ ?_)
  · rw [← ofMul_toMul x, scalarSumHeightSeminorm_tupleLogEmbedding]
    exact hsC _ (hmem hx)
  · rw [← ofMul_toMul x, ← ofMul_toMul y, scalarSumHeightSeminorm_tupleLogEmbedding_sub]
    refine hsδ _ (hmem hx) _ (hmem hy) fun h ↦ hxy ?_
    exact Additive.toMul.injective (Subtype.ext h)

/-- **Centres for the tuples of bounded scalar height.** In a group `Γ` of tuples of `S`-units of
rank at most `r`, for `C ≥ 0` and `δ > 0`, there are at most `(1 + 2 C / δ) ^ r` tuples `b ∈ Γ`
of scalar-sum height at most `C` such that every `x ∈ Γ` of scalar-sum height at most `C` has
`h_s(x / b) < δ` for one of them. -/
theorem exists_finset_scalarSumHeight_div_lt
    {Γ : Subgroup (κ → (S : Set (HeightOneSpectrum (𝓞 K))).unit K)} {r : ℕ}
    (hr : Module.rank ℤ (Additive Γ) ≤ r) {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 < δ) :
    ∃ B : Finset (κ → (S : Set (HeightOneSpectrum (𝓞 K))).unit K),
      (∀ b ∈ B, b ∈ Γ ∧ scalarSumHeight (fun k ↦ ((b k : Kˣ) : K)) ≤ C) ∧
      (B.card : ℝ) ≤ (1 + 2 * C / δ) ^ r ∧
      ∀ x ∈ Γ, scalarSumHeight (fun k ↦ ((x k : Kˣ) : K)) ≤ C →
        ∃ b ∈ B, scalarSumHeight (fun k ↦ (((x / b) k : Kˣ) : K)) < δ := by
  let A : Set (Additive Γ) :=
    {x | scalarSumHeight (fun k ↦ ((x.toMul.val k : Kˣ) : K)) ≤ C}
  obtain ⟨B, hBA, hB, hcover⟩ := Seminorm.exists_finset_card_le_of_rank_le
    (scalarSumHeightSeminorm S) (tupleLogEmbedding S Γ) hr (A := A) hC hδ fun x hx ↦ by
      rw [← ofMul_toMul x, scalarSumHeightSeminorm_tupleLogEmbedding]
      exact hx
  let e : Additive Γ ↪ (κ → (S : Set (HeightOneSpectrum (𝓞 K))).unit K) :=
    Additive.toMul.toEmbedding.trans (Function.Embedding.subtype _)
  have he (b : Additive Γ) : e b = b.toMul.val := rfl
  refine ⟨B.map e, fun b hb ↦ ?_, by rwa [Finset.card_map], fun x hxΓ hx ↦ ?_⟩
  · obtain ⟨b, hbB, rfl⟩ := Finset.mem_map.1 hb
    rw [he]
    exact ⟨b.toMul.property, hBA hbB⟩
  · obtain ⟨b, hb, hxb⟩ := hcover (Additive.ofMul ⟨x, hxΓ⟩) hx
    refine ⟨e b, Finset.mem_map_of_mem e hb, ?_⟩
    rwa [← ofMul_toMul b, scalarSumHeightSeminorm_tupleLogEmbedding_sub, ← he] at hxb

/-- **Centres for the tuples of small affine height.** Let `Γ` be a group of `n`-tuples of
`S`-units of rank at most `r`, with `n ≥ 1`, and let `q ≥ 1`. There are at most `(16 n³ q) ^ r`
tuples `b ∈ Γ` such that every `x ∈ Γ` of absolute affine logarithmic height at most `4 n log n`
has `h_s(x / b) < 1 / (2 q)` for one of them. -/
theorem exists_finset_scalarSumHeight_div_lt_of_absoluteLogHeightAff_le {n : ℕ} (hn : 1 ≤ n)
    {Γ : Subgroup (Fin n → (S : Set (HeightOneSpectrum (𝓞 K))).unit K)} {r : ℕ}
    (hr : Module.rank ℤ (Additive Γ) ≤ r) {q : ℝ} (hq : 1 ≤ q) :
    ∃ B : Finset (Fin n → (S : Set (HeightOneSpectrum (𝓞 K))).unit K), (∀ b ∈ B, b ∈ Γ) ∧
      (B.card : ℝ) ≤ (16 * n ^ 3 * q) ^ r ∧
      ∀ x ∈ Γ, absoluteLogHeightAff (fun i ↦ ((x i : Kˣ) : K)) ≤ 4 * n * Real.log n →
        ∃ b ∈ B, scalarSumHeight (fun i ↦ (((x / b) i : Kˣ) : K)) < 1 / (2 * q) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  obtain ⟨B, hBΓ, hB, hcover⟩ := exists_finset_scalarSumHeight_div_lt S hr
    (C := 4 * n ^ 2 * Real.log n) (δ := 1 / (2 * q)) (by positivity) (by positivity)
  refine ⟨B, fun b hb ↦ (hBΓ b hb).1, hB.trans (pow_le_pow_left₀ (by positivity) ?_ r),
    fun x hxΓ hx ↦ hcover x hxΓ ?_⟩
  · -- `1 + 16 n² q log n ≤ 16 n³ q`, from `log n ≤ n - 1` and `1 ≤ 16 n² q`.
    have h1 : Real.log n ≤ n - 1 := Real.log_le_sub_one_of_pos (by positivity)
    have h2 : 1 ≤ 16 * (n : ℝ) ^ 2 * q := by nlinarith
    have h3 : 16 * (n : ℝ) ^ 2 * q * Real.log n ≤ 16 * n ^ 2 * q * (n - 1) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h4 : 1 + 2 * (4 * (n : ℝ) ^ 2 * Real.log n) / (1 / (2 * q)) =
        1 + 16 * n ^ 2 * q * Real.log n := by
      field_simp
      ring
    rw [h4]
    nlinarith
  · calc scalarSumHeight (fun i ↦ ((x i : Kˣ) : K))
        ≤ n * absoluteLogHeightAff (fun i ↦ ((x i : Kˣ) : K)) :=
          scalarSumHeight_le_mul_absoluteLogHeightAff _
            fun i ↦ Algebra.IsAlgebraic.isAlgebraic _
      _ ≤ n * (4 * n * Real.log n) := by gcongr
      _ = 4 * n ^ 2 * Real.log n := by ring

end TauCeti.NumberField.SUnit
