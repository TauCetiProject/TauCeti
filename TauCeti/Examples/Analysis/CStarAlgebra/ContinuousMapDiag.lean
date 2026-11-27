/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousMap
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Topology.UnitInterval
public import Mathlib.Topology.UrysohnsLemma
public import TauCeti.Analysis.CStarAlgebra.ContinuousMap.UnitInterval
public import TauCeti.Analysis.CStarAlgebra.State.Space
public import TauCeti.Analysis.Normed.Lp.Diagonal.Positive
public import TauCeti.MeasureTheory.Constructions.UnitInterval
public import TauCeti.Topology.ContinuousMap.Compact
import Mathlib.Topology.MetricSpace.Basic

/-!
# Concrete examples for `C([0,1])` sampling representations and functionals

Worked examples for the diagonal sampling representation of `C([0,1])` on `ℓ²` at the points
`1/(n+1)`, together with the norms of the integral / evaluation / weighted functionals on
`C([0,1])`, including the concrete weights `6t²` and `3t²`. The reusable diagonal-operator
identity used here is `lp.star_diagonalCLM`.
-/

public section

open scoped unitInterval ComplexOrder lp ENNReal InnerProductSpace Topology
open ContinuousMap Filter MeasureTheory Set

namespace TauCeti.ContinuousMapDiagExample

/-! ### Diagonal sampling at `1/(n+1)` -/

/-! ### Sampling points and the coefficient sequence -/

/-- The sampling points `1, 1/2, 1/3, …` of the unit interval, indexed by `ℕ` via
`n ↦ 1/(n+1)`. -/
noncomputable def samplePoint (n : ℕ) : unitInterval :=
  ⟨((n + 1 : ℕ) : ℝ)⁻¹, ⟨by positivity, inv_le_one_of_one_le₀ (by exact_mod_cast Nat.succ_pos n)⟩⟩

@[simp]
theorem coe_samplePoint (n : ℕ) : (samplePoint n : ℝ) = ((n + 1 : ℕ) : ℝ)⁻¹ :=
  (rfl)

theorem samplePoint_injective : Function.Injective samplePoint := by
  intro m n h
  have := congrArg Subtype.val h
  simp only [coe_samplePoint, inv_inj, Nat.cast_inj] at this
  exact Nat.succ_injective this

theorem tendsto_samplePoint_zero : Tendsto samplePoint atTop (nhds (0 : unitInterval)) := by
  refine (tendsto_subtype_rng (f := samplePoint) (x := (0 : unitInterval))).2 ?_
  simp only [coe_samplePoint]
  exact tendsto_inv_atTop_zero.comp
    ((tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1))

private theorem memℓp_sample (f : C(unitInterval, ℂ)) :
    Memℓp (fun n : ℕ => f (samplePoint n)) ∞ :=
  memℓp_infty ⟨‖f‖, fun y hy => by
    obtain ⟨n, rfl⟩ := hy
    exact f.norm_coe_le_norm (samplePoint n)⟩

/-- The bounded sequence of samples of a continuous function at `1/(n+1)`. -/
noncomputable def sampleLpInfty (f : C(unitInterval, ℂ)) : ℓ^∞(ℕ, ℂ) :=
  ⟨fun n => f (samplePoint n), memℓp_sample f⟩

@[simp]
theorem sampleLpInfty_apply (f : C(unitInterval, ℂ)) (n : ℕ) :
    sampleLpInfty f n = f (samplePoint n) :=
  (rfl)

@[simp]
theorem sampleLpInfty_zero : sampleLpInfty (0 : C(unitInterval, ℂ)) = 0 := by
  ext; simp

@[simp]
theorem sampleLpInfty_one : sampleLpInfty (1 : C(unitInterval, ℂ)) = 1 := by
  ext; simp

@[simp]
theorem sampleLpInfty_add (f g : C(unitInterval, ℂ)) :
    sampleLpInfty (f + g) = sampleLpInfty f + sampleLpInfty g := by
  ext; simp

@[simp]
theorem sampleLpInfty_smul (c : ℂ) (f : C(unitInterval, ℂ)) :
    sampleLpInfty (c • f) = c • sampleLpInfty f := by
  ext; simp

@[simp]
theorem sampleLpInfty_mul (f g : C(unitInterval, ℂ)) :
    sampleLpInfty (f * g) = sampleLpInfty f * sampleLpInfty g := by
  ext; simp

@[simp]
theorem sampleLpInfty_star (f : C(unitInterval, ℂ)) :
    sampleLpInfty (star f) = star (sampleLpInfty f) := by
  ext n
  simp [lp.star_apply]

theorem norm_sampleLpInfty_le (f : C(unitInterval, ℂ)) : ‖sampleLpInfty f‖ ≤ ‖f‖ :=
  lp.norm_le_of_forall_le (norm_nonneg f) fun n => by
    simpa using f.norm_coe_le_norm (samplePoint n)

/-! ### The diagonal sampling representation -/

/-- Diagonal sampling representation of `C([0,1])` on `ℓ²(ℕ, ℂ)`: `f` acts by multiplication by
the bounded sequence `f(1/(n+1))`. -/
noncomputable def diagLpStarAlgHom :
    C(unitInterval, ℂ) →⋆ₐ[ℂ] (ℓ^2(ℕ, ℂ) →L[ℂ] ℓ^2(ℕ, ℂ)) where
  toFun f := lp.diagonalCLM (sampleLpInfty f)
  map_one' := by
    simp only [sampleLpInfty_one, lp.diagonalCLM_one]
    rfl
  map_mul' f g := by
    simp only [sampleLpInfty_mul, lp.diagonalCLM_mul]
    rfl
  map_zero' := by simp
  map_add' f g := by simp [lp.diagonalCLM_add]
  commutes' c := by
    ext x n
    simp [Algebra.algebraMap_eq_smul_one, sampleLpInfty_smul, lp.diagonalCLM_smul,
      lp.diagonalCLM_one]
  map_star' f := by
    simp only [sampleLpInfty_star]
    exact (lp.star_diagonalCLM (sampleLpInfty f)).symm

@[simp]
theorem diagLpStarAlgHom_apply (f : C(unitInterval, ℂ)) (x : ℓ^2(ℕ, ℂ)) (n : ℕ) :
    diagLpStarAlgHom f x n = f (samplePoint n) * x n := by
  simp [diagLpStarAlgHom, lp.diagonalCLM_apply]

theorem norm_diagLpStarAlgHom_le (f : C(unitInterval, ℂ)) :
    ‖(diagLpStarAlgHom f : ℓ^2(ℕ, ℂ) →L[ℂ] ℓ^2(ℕ, ℂ))‖ ≤ ‖f‖ := by
  simpa [diagLpStarAlgHom, lp.norm_diagonalCLM] using norm_sampleLpInfty_le f

/-! ### Nonfaithfulness -/

/-- A continuous bump supported in `(1/2, 1)` samples to zero at every `1/(n+1)`, since none of
those points lie in `(1/2, 1)`. -/
theorem exists_ne_zero_eq_zero_diagLpStarAlgHom :
    ∃ f : C(unitInterval, ℂ), f ≠ 0 ∧ diagLpStarAlgHom f = 0 := by
  classical
  -- Vanish on `{t ≤ 1/2} ∪ {1}`, so every sample point `1/(n+1)` is killed.
  let A : Set unitInterval := {t | (t : ℝ) ≤ (1 / 2 : ℝ)} ∪ {1}
  let B : Set unitInterval := {⟨(3 / 4 : ℝ), by norm_num⟩}
  have hA : IsClosed A :=
    (isClosed_le continuous_subtypeVal continuous_const).union isClosed_singleton
  have hB : IsClosed B := isClosed_singleton
  have hdisj : Disjoint A B := by
    refine disjoint_iff_inf_le.2 ?_
    rintro t ⟨htA, htB⟩
    have htB' : t = ⟨(3 / 4 : ℝ), by norm_num⟩ := by simpa [B] using htB
    subst htB'
    have : (3 / 4 : ℝ) ≤ 1 / 2 ∨ (3 / 4 : ℝ) = 1 := by
      rcases htA with h | h
      · exact Or.inl h
      · exact Or.inr (congrArg Subtype.val (mem_singleton_iff.1 h))
    norm_num at this
  obtain ⟨φ, hφA, hφB, _⟩ := exists_continuous_zero_one_of_isClosed hA hB hdisj
  refine ⟨⟨fun t => (φ t : ℂ), by fun_prop⟩, ?_, ?_⟩
  · intro hf
    have hφ1 : φ ⟨(3 / 4 : ℝ), by norm_num⟩ = 1 := by
      simpa [B] using hφB (mem_singleton _)
    have := congrArg (fun g : C(unitInterval, ℂ) => g ⟨(3 / 4 : ℝ), by norm_num⟩) hf
    simp only [ContinuousMap.coe_mk, ContinuousMap.zero_apply, Complex.ofReal_eq_zero] at this
    exact one_ne_zero (hφ1.symm.trans this)
  · ext x n
    have hn : samplePoint n ∈ A := by
      cases n with
      | zero =>
          right
          exact Subtype.ext (by simp [samplePoint])
      | succ n =>
          left
          -- `samplePoint (n+1) = 1/(n+2) ≤ 1/2`.
          have : (samplePoint n.succ : ℝ) ≤ 1 / 2 := by
            simp only [coe_samplePoint, Nat.cast_succ]
            have h2 : (2 : ℝ) ≤ (n : ℝ) + 1 + 1 := by
              exact_mod_cast (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le n)))
            have h3 : ((n : ℝ) + 1 + 1)⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h2
            rw [one_div]
            exact h3
          exact this
    simp [diagLpStarAlgHom_apply, hφA hn]

theorem not_injective_diagLpStarAlgHom : ¬ Function.Injective diagLpStarAlgHom := by
  obtain ⟨f, hf0, hf⟩ := exists_ne_zero_eq_zero_diagLpStarAlgHom
  exact fun hinj => hf0 (hinj (hf.trans (map_zero diagLpStarAlgHom).symm))

/-! ### The cyclic sampling vector -/

private theorem summable_cyclicSample_norm_sq :
    Summable fun n : ℕ => ‖(((n + 1 : ℕ) : ℝ)⁻¹ : ℂ)‖ ^ (2 : ℝ) := by
  refine ((Real.summable_one_div_nat_add_rpow (1 : ℝ) 2).2 (by norm_num)).congr fun n => ?_
  have hnorm : ‖(((n + 1 : ℕ) : ℝ)⁻¹ : ℂ)‖ = ((n + 1 : ℕ) : ℝ)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg (Nat.cast_nonneg _)]
  rw [hnorm, abs_of_nonneg (by positivity), one_div, ← Real.inv_rpow (by positivity)]
  push_cast
  rfl

/-- The square-summable sequence `(1/(n+1))ₙ` on `ℓ²(ℕ, ℂ)`. -/
noncomputable def cyclicSample : ℓ^2(ℕ, ℂ) :=
  ⟨fun n => (((n + 1 : ℕ) : ℝ)⁻¹ : ℂ), memℓp_gen summable_cyclicSample_norm_sq⟩

@[simp]
theorem cyclicSample_apply (n : ℕ) :
    cyclicSample n = (((n + 1 : ℕ) : ℝ)⁻¹ : ℂ) :=
  (rfl)

theorem cyclicSample_ne_zero (n : ℕ) : cyclicSample n ≠ 0 := by
  rw [cyclicSample_apply]
  exact inv_ne_zero (Complex.ofReal_ne_zero.2 (Nat.cast_ne_zero.2 n.succ_ne_zero))

/-- A continuous bump equal to `1` at `samplePoint i` and vanishing on the rest of the compact
set of sample points together with their limit `0`. -/
private theorem exists_bump_at_samplePoint (i : ℕ) :
    let S : Set unitInterval := insert 0 (Set.range samplePoint)
    ∃ g : C(unitInterval, ℂ),
      g (samplePoint i) = 1 ∧ ∀ t ∈ S \ {samplePoint i}, g t = 0 := by
  classical
  let S : Set unitInterval := insert 0 (Set.range samplePoint)
  have hSclosed : IsClosed S := tendsto_samplePoint_zero.isCompact_insert_range.isClosed
  -- `samplePoint i` is isolated in `S`: its neighbours in `S` lie in `(·, a]` or `[b, ·)`.
  let a : ℝ := ((i + 2 : ℕ) : ℝ)⁻¹
  let b : ℝ := ((i : ℝ) + 1 / 2)⁻¹
  let A : Set unitInterval := S ∩ ({t | (t : ℝ) ≤ a} ∪ {t | b ≤ (t : ℝ)})
  let B : Set unitInterval := {samplePoint i}
  have hap : a < ((i + 1 : ℕ) : ℝ)⁻¹ :=
    inv_strictAnti₀ (by positivity) (by push_cast; linarith)
  have hpb : ((i + 1 : ℕ) : ℝ)⁻¹ < b :=
    inv_strictAnti₀ (by positivity) (by push_cast; linarith)
  have hA : IsClosed A :=
    hSclosed.inter ((isClosed_le continuous_subtypeVal continuous_const).union
      (isClosed_le continuous_const continuous_subtypeVal))
  have hB : IsClosed B := isClosed_singleton
  have hdisj : Disjoint A B := by
    refine disjoint_singleton_right.2 fun hp => ?_
    rcases hp.2 with h | h
    · exact absurd (lt_of_lt_of_le hap h) (lt_irrefl _)
    · exact absurd (lt_of_lt_of_le hpb h) (lt_irrefl _)
  have hsub : S \ {samplePoint i} ⊆ A := by
    rintro t ⟨htS, htne⟩
    refine ⟨htS, ?_⟩
    rcases htS with rfl | ⟨j, rfl⟩
    · left
      -- The limit point `0` satisfies `0 ≤ a = 1/(i+2)`.
      have : (0 : ℝ) ≤ a := by positivity
      exact this
    · have hji : j ≠ i := fun h => htne (by rw [h]; rfl)
      rcases lt_or_gt_of_ne hji with h | h
      · right
        -- Neighbours with `j < i` satisfy `b ≤ samplePoint j`.
        have : b ≤ (samplePoint j : ℝ) := by
          simp only [coe_samplePoint]
          refine inv_anti₀ (by positivity) ?_
          have : (j : ℝ) + 1 ≤ i := by exact_mod_cast h
          push_cast
          linarith
        exact this
      · left
        -- Neighbours with `j > i` satisfy `samplePoint j ≤ a`.
        have : (samplePoint j : ℝ) ≤ a := by
          simp only [coe_samplePoint]
          refine inv_anti₀ (by positivity) ?_
          have : (i : ℝ) + 1 ≤ j := by exact_mod_cast h
          push_cast
          linarith
        exact this
  obtain ⟨φ, hφA, hφB, _⟩ := exists_continuous_zero_one_of_isClosed hA hB hdisj
  refine ⟨⟨fun t => (φ t : ℂ), by fun_prop⟩, ?_, ?_⟩
  · simpa [B] using congrArg (fun x : ℝ => (x : ℂ)) (hφB (mem_singleton _))
  · intro t ht
    simpa using congrArg (fun x : ℝ => (x : ℂ)) (hφA (hsub ht))

/-- Continuous functions matching prescribed values on a finite set of sample points and vanishing
at all other sample points. -/
theorem exists_eq_on_samplePoint (s : Finset ℕ) (v : ℕ → ℂ) :
    ∃ f : C(unitInterval, ℂ),
      (∀ i ∈ s, f (samplePoint i) = v i) ∧ ∀ j ∉ s, f (samplePoint j) = 0 := by
  classical
  let S : Set unitInterval := insert 0 (Set.range samplePoint)
  choose g hg1 hg0 using fun i : s => exists_bump_at_samplePoint (i : ℕ)
  refine ⟨∑ i : s, (v i) • g i, ?_, ?_⟩
  · intro j hj
    simp only [ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single (⟨j, hj⟩ : s)]
    · simp [hg1 ⟨j, hj⟩]
    · intro i _ hne
      have hiS : samplePoint j ∈ S \ {samplePoint (i : ℕ)} := by
        refine ⟨Or.inr ⟨j, rfl⟩, ?_⟩
        simp [samplePoint_injective.ne (Subtype.coe_ne_coe.2 hne).symm]
      simp [hg0 i _ hiS]
    · simp
  · intro j hj
    simp only [ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul]
    refine Finset.sum_eq_zero fun i _ => ?_
    have hjS : samplePoint j ∈ S \ {samplePoint (i : ℕ)} := by
      refine ⟨Or.inr ⟨j, rfl⟩, ?_⟩
      simp [samplePoint_injective.ne (Ne.symm (ne_of_mem_of_not_mem i.property hj))]
    simp [hg0 i _ hjS]

/-- Finite-support vectors lie in the orbit of `cyclicSample` under diagonal sampling. -/
theorem exists_diagLpStarAlgHom_apply_cyclicSample_eq (s : Finset ℕ) (c : ℕ → ℂ) :
    ∃ f : C(unitInterval, ℂ),
      diagLpStarAlgHom f cyclicSample = ∑ i ∈ s, (c i) • lp.single 2 i (1 : ℂ) := by
  classical
  obtain ⟨f, hf, hf0⟩ := exists_eq_on_samplePoint s fun i => c i * (cyclicSample i)⁻¹
  refine ⟨f, ?_⟩
  ext n
  simp only [diagLpStarAlgHom_apply, lp.coeFn_sum, lp.coeFn_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, lp.single_apply, Pi.single_apply]
  by_cases hn : n ∈ s
  · simp only [hf n hn, mul_assoc]
    field_simp [cyclicSample_ne_zero n]
    simp [hn]
  · simp only [hf0 n hn, zero_mul]
    simp [hn]

/-- The orbit of `cyclicSample` under `diagLpStarAlgHom` is dense in `ℓ²`. -/
theorem denseRange_diagLpStarAlgHom_apply_cyclicSample :
    DenseRange fun f : C(unitInterval, ℂ) => diagLpStarAlgHom f cyclicSample := by
  classical
  let F : C(unitInterval, ℂ) →ₗ[ℂ] ℓ^2(ℕ, ℂ) :=
    { toFun := fun f => diagLpStarAlgHom f cyclicSample
      map_add' := by intros; simp [map_add]
      map_smul' := by intros; simp [map_smul] }
  have hsingle (i : ℕ) : lp.single 2 i (1 : ℂ) ∈ LinearMap.range F := by
    obtain ⟨f, hf⟩ := exists_diagLpStarAlgHom_apply_cyclicSample_eq {i} fun _ => 1
    exact ⟨f, by simpa [F, Finset.sum_singleton] using hf⟩
  have hspan :
      Submodule.span ℂ (Set.range fun i : ℕ => lp.single 2 i (1 : ℂ)) ≤ LinearMap.range F :=
    Submodule.span_le.2 (by
      rintro _ ⟨i, rfl⟩
      exact hsingle i)
  have hdense :
      Dense ((Submodule.span ℂ (Set.range fun i : ℕ => lp.single 2 i (1 : ℂ)) :
        Submodule ℂ ℓ^2(ℕ, ℂ)) : Set ℓ^2(ℕ, ℂ)) := by
    intro x
    refine mem_closure_of_tendsto (lp.hasSum_single (p := 2) (by decide) x)
      (Eventually.of_forall fun s => ?_)
    refine Submodule.sum_mem _ fun i _ => ?_
    have h : lp.single 2 i (x i) = x i • (lp.single 2 i (1 : ℂ) : ℓ^2(ℕ, ℂ)) := by
      rw [← lp.single_smul]
      simp
    rw [h]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hrange : (LinearMap.range F : Set ℓ^2(ℕ, ℂ)) =
      Set.range fun f : C(unitInterval, ℂ) => diagLpStarAlgHom f cyclicSample :=
    LinearMap.coe_range F
  rw [DenseRange, ← hrange]
  exact hdense.mono (fun _ hx => hspan hx)

/-! ### Volume, evaluation, and weighted-integral examples -/

/-- Integration against volume on `[0,1]` has norm `1`. -/
example : ‖ContinuousMap.unitIntervalVolumeIntegral.toContinuousLinearMap‖ = 1 :=
  ContinuousMap.norm_unitIntervalVolumeIntegral

/-- Evaluation at `0` has norm `1`. -/
example : ‖ContinuousMap.evalCLM ℂ (M := ℂ) (0 : unitInterval)‖ = 1 :=
  ContinuousMap.norm_evalCLM (K := unitInterval) (𝕜 := ℂ) (E := ℂ) (0 : unitInterval)

/-! ### Concrete weights `6t²` and `3t²` -/

/-- The continuous weight `t ↦ 6 t²` on the unit interval. -/
noncomputable def sixTSq : C(unitInterval, ℝ) :=
  ⟨fun t => 6 * (t : ℝ) ^ 2, by fun_prop⟩

@[simp]
theorem sixTSq_apply (t : unitInterval) : sixTSq t = 6 * (t : ℝ) ^ 2 :=
  (rfl)

theorem sixTSq_nonneg (t : unitInterval) : 0 ≤ sixTSq t := by
  simp only [sixTSq_apply]
  positivity

/-- The continuous weight `t ↦ 3 t²` on the unit interval. -/
noncomputable def threeTSq : C(unitInterval, ℝ) :=
  ⟨fun t => 3 * (t : ℝ) ^ 2, by fun_prop⟩

@[simp]
theorem threeTSq_apply (t : unitInterval) : threeTSq t = 3 * (t : ℝ) ^ 2 :=
  (rfl)

theorem threeTSq_nonneg (t : unitInterval) : 0 ≤ threeTSq t := by
  simp only [threeTSq_apply]
  positivity

/-- The integral of `t ↦ t²` against volume on the unit interval is `1/3`. -/
theorem integral_pow_two_unitInterval :
    ∫ t : unitInterval, ((t : ℝ) ^ 2) = (1 : ℝ) / 3 := by
  rw [← TauCeti.intervalIntegral_eq_integral_unitInterval (f := fun t : ℝ => t ^ 2)]
  norm_num [integral_pow]

theorem integral_sixTSq : ∫ t, sixTSq t ∂(volume : Measure unitInterval) = 2 := by
  calc ∫ t, sixTSq t ∂(volume : Measure unitInterval)
      = ∫ t, 6 * (t : ℝ) ^ 2 ∂(volume : Measure unitInterval) := by
          simp only [sixTSq_apply]
    _ = 6 * ∫ t, ((t : ℝ) ^ 2) ∂(volume : Measure unitInterval) :=
          MeasureTheory.integral_const_mul _ _
    _ = 2 := by rw [integral_pow_two_unitInterval]; norm_num

theorem integral_threeTSq : ∫ t, threeTSq t ∂(volume : Measure unitInterval) = 1 := by
  calc ∫ t, threeTSq t ∂(volume : Measure unitInterval)
      = ∫ t, 3 * (t : ℝ) ^ 2 ∂(volume : Measure unitInterval) := by
          simp only [threeTSq_apply]
    _ = 3 * ∫ t, ((t : ℝ) ^ 2) ∂(volume : Measure unitInterval) :=
          MeasureTheory.integral_const_mul _ _
    _ = 1 := by rw [integral_pow_two_unitInterval]; norm_num

/-- The weight-`6t²` functional has norm `2`. -/
example : ‖(ContinuousMap.weightedIntegral (volume : Measure unitInterval) sixTSq
    sixTSq_nonneg).toContinuousLinearMap‖ = 2 := by
  rw [ContinuousMap.norm_weightedIntegral, integral_sixTSq]

/-- The weight-`3t²` functional is a state. -/
example : StrongDual.toWeakDual
    (ContinuousMap.weightedIntegral (volume : Measure unitInterval) threeTSq
      threeTSq_nonneg).toContinuousLinearMap ∈
    TauCeti.stateSpace (C(unitInterval, ℂ)) := by
  refine TauCeti.mem_stateSpace_iff_map_one.2 ⟨?_, ?_⟩
  · intro a ha
    exact (ContinuousMap.weightedIntegral (volume : Measure unitInterval) threeTSq
      threeTSq_nonneg).map_nonneg ha
  · have h1 : ContinuousMap.weightedIntegral (volume : Measure unitInterval) threeTSq
        threeTSq_nonneg 1 = 1 := by
      rw [ContinuousMap.weightedIntegral_one, integral_threeTSq, Complex.ofReal_one]
    simpa [StrongDual.toWeakDual_apply] using h1

/-- Sampling at `1/(n+1)` is not faithful: a bump in `(1/2, 1)` acts as zero. -/
example : ¬ Function.Injective diagLpStarAlgHom :=
  not_injective_diagLpStarAlgHom

/-- The sequence `(1/(n+1))ₙ` is cyclic for diagonal sampling. -/
example : DenseRange fun f : C(unitInterval, ℂ) => diagLpStarAlgHom f cyclicSample :=
  denseRange_diagLpStarAlgHom_apply_cyclicSample

end TauCeti.ContinuousMapDiagExample
