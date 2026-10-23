/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Lp.Basic
public import Mathlib.Analysis.Normed.Module.Bases
public import TauCeti.Analysis.Normed.Module.Bases.Basic
public import TauCeti.Analysis.Normed.Module.Bases.Reflexive

/-!
# The coordinate basis of `lp`

For `1 ≤ p < ∞`, the unit coordinate vectors form an unconditional Schauder basis of
`ℓ^p(ι, 𝕜)`. Its coordinate functionals are evaluation, and its finite projections retain
exactly the selected coordinates. All these projections are contractions. In particular,
they supply finite-rank contractive approximations of the identity.

For `ι = ℕ` the coordinate basis is boundedly complete as a classical Schauder basis
(`lp.isBoundedlyComplete_toSchauderBasis_unconditionalBasis`): bounded partial sums
`∑ i < n, a i • eᵢ` bound the partial sums of `‖a i‖ ^ p`, so `a` lies in `ℓᵖ`.

The construction uses Mathlib's `lp.hasSum_single` and `lp.evalCLM`. Neither completeness of
the scalar field nor countability of the index type is needed.

## References

* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, Chapter 1.
-/

public section

open scoped lp ENNReal

namespace lp

variable {ι 𝕜 : Type*} [DecidableEq ι] [NontriviallyNormedField 𝕜]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The unit coordinate vectors are an unconditional Schauder basis of `lp` at finite
exponents. -/
noncomputable def unconditionalBasis (hp : p ≠ ⊤) :
    UnconditionalSchauderBasis ι 𝕜 ℓ^p(ι, 𝕜) where
  basis i := lp.single p i 1
  coord := evalCLM 𝕜 (fun _ : ι ↦ 𝕜) p
  ortho i j := by simp [Pi.single_apply]
  expansion x := by
    simpa only [evalCLM_apply, ← lp.single_smul, smul_eq_mul, mul_one]
      using lp.hasSum_single hp x

/-- The basis vectors are the unit coordinate vectors. -/
@[simp]
theorem unconditionalBasis_apply (hp : p ≠ ⊤) (i : ι) :
    unconditionalBasis (ι := ι) (𝕜 := 𝕜) hp i = lp.single p i 1 := (rfl)

/-- The coordinate functionals of the coordinate basis are evaluation maps. -/
@[simp]
theorem unconditionalBasis_coord (hp : p ≠ ⊤) (i : ι) :
    (unconditionalBasis (ι := ι) (𝕜 := 𝕜) hp).coord i =
      evalCLM 𝕜 (fun _ : ι ↦ 𝕜) p i := (rfl)

/-- A finite basis projection retains precisely its selected coordinates. -/
theorem unconditionalBasis_proj_apply (hp : p ≠ ⊤) (s : Finset ι)
    (x : ℓ^p(ι, 𝕜)) (i : ι) :
    (unconditionalBasis hp).proj s x i = if i ∈ s then x i else 0 := by
  classical
  rw [← evalCLM_apply (𝕜 := 𝕜) i ((unconditionalBasis hp).proj s x),
    GeneralSchauderBasis.proj_apply, map_sum]
  simp [unconditionalBasis_coord, lp.single_apply, Pi.single_apply]

/-- All finite coordinate projections of `lp` are contractions. -/
theorem norm_unconditionalBasis_proj_le (hp : p ≠ ⊤) (s : Finset ι) :
    ‖(unconditionalBasis (ι := ι) (𝕜 := 𝕜) hp).proj s‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x ↦ ?_
  rw [one_mul]
  apply norm_mono (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  intro i
  rw [unconditionalBasis_proj_apply]
  split_ifs <;> simp

/-- For `1 ≤ p < ∞`, the coordinate basis of `ℓᵖ` is boundedly complete. -/
theorem isBoundedlyComplete_toSchauderBasis_unconditionalBasis (hp : p ≠ ⊤) :
    (unconditionalBasis (ι := ℕ) (𝕜 := 𝕜) hp).toSchauderBasis.IsBoundedlyComplete := by
  have hp₀ : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' hp
  rw [SchauderBasis.isBoundedlyComplete_iff]
  rintro a ⟨C, hC⟩
  have hsum (n : ℕ) : ∑ i ∈ Finset.range n, ‖a i‖ ^ p.toReal ≤ C ^ p.toReal := by
    have h := hC (Set.mem_range_self n)
    simp only [UnconditionalSchauderBasis.coe_toSchauderBasis, unconditionalBasis_apply,
      ← lp.single_smul, smul_eq_mul, mul_one] at h
    rw [← lp.norm_sum_single hp₀]
    exact Real.rpow_le_rpow (norm_nonneg _) h hp₀.le
  have ha : Memℓp a p :=
    (memℓp_gen_iff hp₀).2 (summable_of_sum_range_le (fun _ ↦ by positivity) hsum)
  exact ⟨⟨a, ha⟩, fun i ↦ by simp⟩

end lp
