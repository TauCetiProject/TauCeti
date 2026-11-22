/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import TauCeti.Topology.Algebra.Valued.DiscreteValuationRing
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Frobenius eigenvectors over complete discretely valued fields

Let `K` be a complete nonarchimedean field whose valuation ring `𝒪[K]` is a discrete valuation
ring, and let `σ` be a `q`-Frobenius lift on `K` for some `q > 1`: a ring endomorphism with
`‖σ a - a ^ q‖ < 1` whenever `‖a‖ ≤ 1`, so that `σ` induces the `q`-th power map on the residue
field `𝓀[K]`. Such a lift forces `q` to vanish in `𝓀[K]` as soon as `𝓀[K]` is infinite.

When moreover `σ` preserves norms and `𝓀[K]` is algebraically closed, the `σ`-semilinear
equation `σ c = u * c` has solutions for every `u` with `‖u‖ ≤ 1`, close to any approximate
solution: this is a form of Lang's theorem. A correction `c ↦ c + e * z`, where `e` is the current
error and the residue of `z` is a root of a polynomial `X ^ q - a X + b` over `𝓀[K]`, lowers the
error by the factor `‖ϖ‖` of a uniformizer, and completeness gives the limit.

For the field `K^σ` of elements fixed by `σ` this gives the following.

* `K^σ` attains every norm of `K`: its value group is that of `K`.
* Every root of `X ^ q - X` in `𝓀[K]` is the residue of an element of `K^σ`.

These are the inputs for identifying the coefficient field of `σ`-semilinear structures, such as
Frobenius structures on differential modules, over a field with algebraically closed residue
field. For the Witt vectors of an algebraically closed field, Mathlib proves a related statement
by a Witt-vector computation (`WittVector.exists_frobenius_solution_fractionRing`).

## Main results

* `Valued.integer.natCast_eq_zero_of_norm_apply_sub_pow_lt_one`: a `q`-Frobenius lift on a field
  with infinite residue field forces `(q : 𝓀[K]) = 0`.
* `RingHom.exists_apply_eq_mul_and_norm_sub_le`: an approximate solution `c₀` of `σ c = u * c`
  lies within `‖σ c₀ - u * c₀‖` of an exact solution.
* `RingHom.exists_norm_eq_one_and_apply_eq_mul`: for `‖u‖ = 1`, `σ c = u * c` has a solution of
  norm `1`.
* `RingHom.exists_apply_eq_self_and_norm_eq`: every norm of `K` is the norm of an element fixed
  by `σ`.
* `RingHom.exists_apply_eq_self_and_residue_eq`: every root of `X ^ q - X` in `𝓀[K]` is the residue
  of an element of `𝒪[K]` fixed by `σ`.

## References

* N. Tsuzuki, *Minimal slope conjecture of F-isocrystals*, arXiv:1910.03871, Appendix A,
  Lemma A.1(2) and its proof.
-/

public section

open Filter IsLocalRing Polynomial Topology
open scoped NormedField Valued

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] (σ : K →+* K) {q : ℕ}
  (hσq : ∀ a : K, ‖a‖ ≤ 1 → ‖σ a - a ^ q‖ < 1)
include hσq

variable {σ} in
/-- A `q`-Frobenius lift `σ` on a field with infinite residue field forces `q` to vanish in the
residue field: the `q`-th power map, the reduction of `σ`, is additive. -/
theorem Valued.integer.natCast_eq_zero_of_norm_apply_sub_pow_lt_one [Infinite 𝓀[K]] (hq : 1 < q) :
    (q : 𝓀[K]) = 0 := by
  have hadd (ξ : 𝓀[K]) : (ξ + 1) ^ q = ξ ^ q + 1 := by
    obtain ⟨a, rfl⟩ := residue_surjective ξ
    rw [← map_one (residue 𝒪[K]), ← map_add, ← map_pow, ← map_pow, ← map_add,
      residue_eq_residue_iff_norm_sub_lt_one]
    have h₁ := hσq (a + 1) (mem_iff.1 (a + 1).property)
    have h₂ := hσq a (mem_iff.1 a.property)
    push_cast at h₁ ⊢
    have : ((a : K) + 1) ^ q - ((a : K) ^ q + 1) =
        (σ a - (a : K) ^ q) + -(σ ((a : K) + 1) - ((a : K) + 1) ^ q) := by
      rw [map_add, map_one]
      ring
    rw [this]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt h₂ (by rwa [norm_neg]))
  have hP : ((X + 1) ^ q - X ^ q - 1 : 𝓀[K][X]) = 0 :=
    zero_of_eval_zero _ fun ξ ↦ by simp [hadd]
  have hcoeff := congrArg (fun P : 𝓀[K][X] ↦ P.coeff (q - 1)) hP
  have h₁ : q - 1 ≠ q := by omega
  have h₂ : q - 1 ≠ 0 := by omega
  simpa [coeff_X_add_one_pow, coeff_X_pow, coeff_one, h₁, h₂,
    Nat.choose_symm (n := q) (k := 1) hq.le] using hcoeff

namespace RingHom

/-- Under a `q`-Frobenius lift `σ`, an element `z` of `𝒪[K]` whose residue is a root of the
reduction of `X ^ q - a X + b` satisfies `‖σ z - a z + b‖ < 1`. -/
private theorem norm_apply_sub_mul_add_lt_one {z a b : 𝒪[K]}
    (h : residue 𝒪[K] z ^ q - residue 𝒪[K] a * residue 𝒪[K] z + residue 𝒪[K] b = 0) :
    ‖σ z - a * z + b‖ < 1 := by
  have hres : ‖((z ^ q - a * z + b : 𝒪[K]) : K)‖ < 1 :=
    Valued.integer.residue_eq_zero_iff_norm_lt_one.1 (by simpa using h)
  have : σ z - a * z + b = (σ z - (z : K) ^ q) + ((z ^ q - a * z + b : 𝒪[K]) : K) := by
    push_cast
    ring
  rw [this]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt
    (max_lt (hσq z (Valued.integer.mem_iff.1 z.property)) hres)

variable [IsAlgClosed 𝓀[K]]

/-- Over an algebraically closed residue field, for all `a b : 𝒪[K]` there is `z : 𝒪[K]` with
`‖σ z - a z + b‖ < 1`: the residue of `z` is a root of the reduction of `X ^ q - a X + b`. -/
private theorem exists_norm_apply_sub_mul_add_lt_one (hq : 1 < q) (a b : 𝒪[K]) :
    ∃ z : 𝒪[K], ‖σ z - a * z + b‖ < 1 := by
  let P : 𝓀[K][X] := X ^ q - (C (residue 𝒪[K] a) * X - C (residue 𝒪[K] b))
  have hdeg : (C (residue 𝒪[K] a) * X - C (residue 𝒪[K] b) : 𝓀[K][X]).degree <
      (X ^ q : 𝓀[K][X]).degree :=
    (degree_sub_le _ _).trans_lt <|
      (max_le (degree_C_mul_X_le _) (degree_C_le.trans zero_le_one)).trans_lt
        (by rw [degree_X_pow]; exact_mod_cast hq)
  have hP : P.degree ≠ 0 := by
    rw [degree_sub_eq_left_of_degree_lt hdeg, degree_X_pow]
    exact_mod_cast (zero_lt_one.trans hq).ne'
  obtain ⟨ξ, hξ⟩ := IsAlgClosed.exists_root P hP
  obtain ⟨z, rfl⟩ := residue_surjective ξ
  refine ⟨z, norm_apply_sub_mul_add_lt_one σ hσq ?_⟩
  have : residue 𝒪[K] z ^ q - (residue 𝒪[K] a * residue 𝒪[K] z - residue 𝒪[K] b) = 0 := by
    simpa [P] using hξ
  linear_combination this

/-- Over an algebraically closed residue field, for `u : 𝒪[K]` of norm `1` there is `z : 𝒪[K]` of
norm `1` with `‖σ z - u z‖ < 1`: the residue of `z` is a nonzero root of the reduction of
`X ^ q - u X`. -/
private theorem exists_norm_eq_one_and_norm_apply_sub_mul_lt_one (hq : 1 < q) {u : 𝒪[K]}
    (hu : ‖(u : K)‖ = 1) : ∃ z : 𝒪[K], ‖(z : K)‖ = 1 ∧ ‖σ z - u * z‖ < 1 := by
  have hu₀ : residue 𝒪[K] u ≠ 0 := by
    rw [Ne, Valued.integer.residue_eq_zero_iff_norm_lt_one, hu]
    exact lt_irrefl 1
  obtain ⟨ξ, hξ⟩ := IsAlgClosed.exists_root (X ^ (q - 1) - C (residue 𝒪[K] u)) (by
    rw [degree_X_pow_sub_C (by omega)]
    exact_mod_cast (by omega : q - 1 ≠ 0))
  have hξu : ξ ^ (q - 1) = residue 𝒪[K] u := by simpa [sub_eq_zero] using hξ
  have hξ₀ : ξ ≠ 0 := by
    rintro rfl
    exact hu₀ (by rw [← hξu, zero_pow (by omega)])
  obtain ⟨z, rfl⟩ := residue_surjective ξ
  refine ⟨z, le_antisymm (Valued.integer.mem_iff.1 z.property) (not_lt.1 fun h ↦
    hξ₀ (Valued.integer.residue_eq_zero_iff_norm_lt_one.2 h)), ?_⟩
  simpa using norm_apply_sub_mul_add_lt_one σ hσq (b := 0) (by
    rw [map_zero, add_zero, ← hξu, ← pow_succ, Nat.sub_add_cancel hq.le, sub_self])

variable [IsDiscreteValuationRing 𝒪[K]] (hσ : ∀ a, ‖σ a‖ = ‖a‖)
include hσ

/-- One step of successive approximation for `σ c = u * c`: a correction of `c` by at most the
error `‖σ c - u * c‖` multiplies the error by at most the norm of a uniformizer `ϖ`. -/
private theorem exists_norm_sub_le_and_norm_apply_sub_mul_le (hq : 1 < q) {ϖ : 𝒪[K]}
    (hϖ : Irreducible ϖ) {u : K} (hu : ‖u‖ ≤ 1) (c : K) :
    ∃ c' : K, ‖c' - c‖ ≤ ‖σ c - u * c‖ ∧ ‖σ c' - u * c'‖ ≤ ‖ϖ‖ * ‖σ c - u * c‖ := by
  obtain ⟨e, he⟩ : ∃ e, e = σ c - u * c := ⟨_, rfl⟩
  rw [← he]
  rcases eq_or_ne e 0 with rfl | he₀
  · exact ⟨c, by simp [← he]⟩
  have hσe : σ e ≠ 0 := (map_ne_zero σ).2 he₀
  have hdiv : ‖e / σ e‖ = 1 := by rw [norm_div, hσ, div_self (norm_ne_zero_iff.2 he₀)]
  let a : 𝒪[K] := ⟨u * e / σ e, Valued.integer.mem_iff.2 (by rwa [mul_div_assoc, norm_mul, hdiv,
    mul_one])⟩
  let b : 𝒪[K] := ⟨e / σ e, Valued.integer.mem_iff.2 hdiv.le⟩
  obtain ⟨z, hz⟩ := exists_norm_apply_sub_mul_add_lt_one σ hσq hq a b
  refine ⟨c + e * z, ?_, ?_⟩
  · rw [add_sub_cancel_left, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (Valued.integer.mem_iff.1 z.property)
  · have hkey : σ (c + e * z) - u * (c + e * z) = σ e * (σ z - a * z + b) := by
      simp only [a, b, map_add, map_mul]
      field_simp
      linear_combination -he
    rw [hkey, norm_mul, hσ, mul_comm]
    exact mul_le_mul_of_nonneg_right (hϖ.norm_le_of_norm_lt_one hz) (norm_nonneg _)

variable [CompleteSpace K]

/-- **Lang's theorem for a Frobenius lift.** Let `K` be complete with discrete valuation ring and
algebraically closed residue field, and `σ` a norm-preserving `q`-Frobenius lift (`q > 1`). For
every `u` with `‖u‖ ≤ 1` and every `c₀ : K`, the equation `σ c = u * c` has a solution `c` with
`‖c - c₀‖ ≤ ‖σ c₀ - u * c₀‖`. -/
theorem exists_apply_eq_mul_and_norm_sub_le (hq : 1 < q) {u : K} (hu : ‖u‖ ≤ 1) (c₀ : K) :
    ∃ c, σ c = u * c ∧ ‖c - c₀‖ ≤ ‖σ c₀ - u * c₀‖ := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hr := Valued.integer.norm_irreducible_lt_one hϖ
  choose f hf₁ hf₂ using exists_norm_sub_le_and_norm_apply_sub_mul_le σ hσq hσ hq hϖ hu
  -- Iterate the correction step from `c₀`; the errors decay geometrically with ratio `‖ϖ‖`.
  let c : ℕ → K := fun n ↦ f^[n] c₀
  have hc (n : ℕ) : c (n + 1) = f (c n) := Function.iterate_succ_apply' f n c₀
  have hE (n : ℕ) : ‖σ (c n) - u * c n‖ ≤ ‖ϖ‖ ^ n * ‖σ c₀ - u * c₀‖ := by
    induction n with
    | zero => simp [c]
    | succ n ih =>
      rw [hc, pow_succ', mul_assoc]
      exact (hf₂ _).trans (mul_le_mul_of_nonneg_left ih (norm_nonneg _))
  have hstep (n : ℕ) : ‖c (n + 1) - c n‖ ≤ ‖σ c₀ - u * c₀‖ :=
    (hc n ▸ hf₁ _).trans ((hE n).trans
      (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hr.le)))
  have hdist (n : ℕ) : dist (c n) (c (n + 1)) ≤ ‖σ c₀ - u * c₀‖ * ‖ϖ‖ ^ n := by
    rw [dist_comm, dist_eq_norm, hc, mul_comm]
    exact (hf₁ _).trans (hE n)
  obtain ⟨c', hc'⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric _ _ hr hdist)
  refine ⟨c', ?_, ?_⟩
  · -- The errors tend both to `σ c' - u * c'`, by continuity, and to `0`.
    have hσc : Continuous σ := (AddMonoidHomClass.isometry_of_norm σ hσ).continuous
    have h₁ : Tendsto (fun n ↦ σ (c n) - u * c n) atTop (𝓝 (σ c' - u * c')) :=
      ((hσc.tendsto c').comp hc').sub (hc'.const_mul u)
    have h₂ : Tendsto (fun n ↦ σ (c n) - u * c n) atTop (𝓝 0) :=
      squeeze_zero_norm hE (by
        simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hr).mul_const
          ‖σ c₀ - u * c₀‖)
    exact sub_eq_zero.1 (tendsto_nhds_unique h₁ h₂)
  · -- Every correction is at most the initial error, so the ultrametric inequality bounds the
    -- distance from `c₀` uniformly along the sequence.
    have hb (n : ℕ) : ‖c n - c₀‖ ≤ ‖σ c₀ - u * c₀‖ := by
      induction n with
      | zero => simp [c]
      | succ n ih =>
        rw [← sub_add_sub_cancel _ (c n)]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hstep n) ih)
    exact le_of_tendsto' (hc'.sub_const c₀).norm hb

/-- For `‖u‖ = 1`, the equation `σ c = u * c` has a solution of norm `1`. -/
theorem exists_norm_eq_one_and_apply_eq_mul (hq : 1 < q) {u : K} (hu : ‖u‖ = 1) :
    ∃ c, ‖c‖ = 1 ∧ σ c = u * c := by
  obtain ⟨z, hz₁, hz⟩ := exists_norm_eq_one_and_norm_apply_sub_mul_lt_one σ hσq hq
    (u := ⟨u, Valued.integer.mem_iff.2 hu.le⟩) hu
  obtain ⟨c, hc, hcz⟩ := exists_apply_eq_mul_and_norm_sub_le σ hσq hσ hq hu.le z
  refine ⟨c, ?_, hc⟩
  rw [← sub_add_cancel c z, ← hz₁]
  exact IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by linarith) |>.trans
    (max_eq_right (by linarith))

/-- Every norm of `K` is the norm of an element fixed by `σ`: the field fixed by `σ` has the same
value group as `K`. -/
theorem exists_apply_eq_self_and_norm_eq (hq : 1 < q) (x : K) : ∃ b, σ b = b ∧ ‖b‖ = ‖x‖ := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact ⟨0, map_zero σ, rfl⟩
  have hσx : σ x ≠ 0 := (map_ne_zero σ).2 hx
  obtain ⟨c, hc₁, hc⟩ := exists_norm_eq_one_and_apply_eq_mul σ hσq hσ hq (u := x / σ x)
    (by rw [norm_div, hσ, div_self (norm_ne_zero_iff.2 hx)])
  refine ⟨c * x, ?_, by rw [norm_mul, hc₁, one_mul]⟩
  rw [map_mul, hc]
  field_simp

/-- Every root of `X ^ q - X` in the residue field `𝓀[K]` is the residue of an element of `𝒪[K]`
fixed by `σ`. -/
theorem exists_apply_eq_self_and_residue_eq (hq : 1 < q) {ξ : 𝓀[K]} (hξ : ξ ^ q = ξ) :
    ∃ b : 𝒪[K], σ b = b ∧ residue 𝒪[K] b = ξ := by
  obtain ⟨a, rfl⟩ := residue_surjective ξ
  have ha := Valued.integer.mem_iff.1 a.property
  have haq : ‖(a : K) ^ q - a‖ < 1 := by
    simpa using (Valued.integer.residue_eq_residue_iff_norm_sub_lt_one (x := a ^ q) (y := a)).1
      (by rwa [map_pow])
  obtain ⟨b, hb, hba⟩ := exists_apply_eq_mul_and_norm_sub_le σ hσq hσ hq (u := 1) (by simp) a
  have hba' : ‖b - a‖ < 1 := hba.trans_lt <| by
    rw [one_mul, ← sub_add_sub_cancel _ ((a : K) ^ q)]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt (hσq a ha) haq)
  have hb₁ : ‖b‖ ≤ 1 := by
    rw [← sub_add_cancel b a]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hba'.le ha)
  exact ⟨⟨b, Valued.integer.mem_iff.2 hb₁⟩, by simpa using hb,
    Valued.integer.residue_eq_residue_iff_norm_sub_lt_one.2 hba'⟩

end RingHom
