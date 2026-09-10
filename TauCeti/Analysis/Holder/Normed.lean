/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.Basic

/-!
# The Banach space of global Hölder functions

This file equips bounded continuous Hölder functions with the norm

`‖f‖_[C^α] = ‖f‖_∞ + [f]_α`

and proves that this norm is complete when the codomain is complete.  The supremum term controls
the pointwise limit of a Cauchy sequence, while the Hölder term controls its increments uniformly.
Thus the limiting function is again Hölder and convergence holds in both terms of the norm.

The resulting Banach space is the zeroth-order member of the `C^{k,α}` scale used for Schauder
estimates.  The definition uses Mathlib's `MemHolder` and `nnHolderNorm` rather than introducing a
parallel notion of Hölder continuity.

## Main declarations

* `TauCeti.HolderSpace`: bounded continuous globally `α`-Hölder functions.
* `TauCeti.HolderSpace.instNormedAddCommGroup`: the supremum-plus-Hölder normed group structure.
* `TauCeti.HolderSpace.instCompleteSpace`: completeness when the codomain is complete.

## References

L. C. Evans, *Partial Differential Equations*, Section 5.1; D. Gilbarg and N. Trudinger,
*Elliptic Partial Differential Equations of Second Order*, Section 4.1.
-/

public section

noncomputable section

namespace TauCeti

open Filter Topology
open scoped NNReal BoundedContinuousFunction

universe u v

variable (α : ℝ≥0) (X : Type u) (Y : Type v) [MetricSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- The space of bounded continuous globally `α`-Hölder functions, equipped below with the
supremum-plus-Hölder norm. The wrapper separates this norm from the inherited supremum norm on
the underlying submodule. -/
structure HolderSpace where
  /-- The underlying bounded continuous Hölder function. -/
  toHolderSubmodule : holderSubmodule (X := X) (Y := Y) α

namespace HolderSpace

variable {α : ℝ≥0} {X : Type u} {Y : Type v} [MetricSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

instance : CoeFun (HolderSpace α X Y) fun _ ↦ X → Y := ⟨fun f ↦ f.1.1⟩

/-- The underlying bounded continuous function. -/
def toBoundedContinuousFunction (f : HolderSpace α X Y) : X →ᵇ Y := f.1.1

/-- Promote a bounded continuous Hölder function to the Hölder space. -/
def ofBoundedContinuousFunction (f : X →ᵇ Y) (hf : MemHolder α (f : X → Y)) :
    HolderSpace α X Y :=
  ⟨⟨f, (mem_holderSubmodule_iff f).mpr hf⟩⟩

@[simp]
theorem toBoundedContinuousFunction_ofBoundedContinuousFunction (f : X →ᵇ Y)
    (hf : MemHolder α (f : X → Y)) :
    (ofBoundedContinuousFunction f hf).toBoundedContinuousFunction = f := (rfl)

@[simp]
theorem toBoundedContinuousFunction_apply (f : HolderSpace α X Y) (x : X) :
    f.toBoundedContinuousFunction x = f x := (rfl)

/-- A Hölder-space element satisfies the global Hölder condition. -/
theorem memHolder (f : HolderSpace α X Y) :
    MemHolder α (f.toBoundedContinuousFunction : X → Y) :=
  (mem_holderSubmodule_iff f.toHolderSubmodule.1).mp f.toHolderSubmodule.2

/-- Two Hölder-space elements are equal when they agree pointwise. -/
@[ext]
theorem ext {f g : HolderSpace α X Y} (h : ∀ x, f x = g x) : f = g := by
  cases f with
  | mk f =>
    cases g with
    | mk g =>
      congr 1
      apply Subtype.ext
      ext x
      exact h x

instance : Zero (HolderSpace α X Y) := ⟨⟨0⟩⟩

instance : Add (HolderSpace α X Y) := ⟨fun f g ↦ ⟨f.1 + g.1⟩⟩

instance : Neg (HolderSpace α X Y) := ⟨fun f ↦ ⟨-f.1⟩⟩

instance : Sub (HolderSpace α X Y) := ⟨fun f g ↦ ⟨f.1 - g.1⟩⟩

instance : SMul ℝ (HolderSpace α X Y) := ⟨fun c f ↦ ⟨c • f.1⟩⟩

instance : SMul ℕ (HolderSpace α X Y) := ⟨fun n f ↦ ⟨n • f.1⟩⟩

instance : SMul ℤ (HolderSpace α X Y) := ⟨fun n f ↦ ⟨n • f.1⟩⟩

@[simp] theorem toBoundedContinuousFunction_zero :
    (0 : HolderSpace α X Y).toBoundedContinuousFunction = 0 := (rfl)

@[simp] theorem toBoundedContinuousFunction_add (f g : HolderSpace α X Y) :
    (f + g).toBoundedContinuousFunction = f.toBoundedContinuousFunction +
      g.toBoundedContinuousFunction := (rfl)

@[simp] theorem toBoundedContinuousFunction_neg (f : HolderSpace α X Y) :
    (-f).toBoundedContinuousFunction = -f.toBoundedContinuousFunction := (rfl)

@[simp] theorem toBoundedContinuousFunction_sub (f g : HolderSpace α X Y) :
    (f - g).toBoundedContinuousFunction = f.toBoundedContinuousFunction -
      g.toBoundedContinuousFunction := (rfl)

@[simp] theorem toBoundedContinuousFunction_smul (c : ℝ) (f : HolderSpace α X Y) :
    (c • f).toBoundedContinuousFunction = c • f.toBoundedContinuousFunction := (rfl)

@[simp] theorem toBoundedContinuousFunction_nsmul (n : ℕ) (f : HolderSpace α X Y) :
    (n • f).toBoundedContinuousFunction = n • f.toBoundedContinuousFunction := (rfl)

@[simp] theorem toBoundedContinuousFunction_zsmul (n : ℤ) (f : HolderSpace α X Y) :
    (n • f).toBoundedContinuousFunction = n • f.toBoundedContinuousFunction := (rfl)

/-- The underlying bounded continuous function determines a Hölder-space element. -/
theorem toBoundedContinuousFunction_injective :
    Function.Injective (toBoundedContinuousFunction : HolderSpace α X Y → X →ᵇ Y) :=
  fun _ _ h ↦ ext fun x ↦ DFunLike.congr_fun h x

instance : AddCommGroup (HolderSpace α X Y) :=
  Function.Injective.addCommGroup toBoundedContinuousFunction
    toBoundedContinuousFunction_injective toBoundedContinuousFunction_zero
    toBoundedContinuousFunction_add toBoundedContinuousFunction_neg
    toBoundedContinuousFunction_sub (fun f n ↦ toBoundedContinuousFunction_nsmul n f)
    (fun f n ↦ toBoundedContinuousFunction_zsmul n f)

instance : Module ℝ (HolderSpace α X Y) :=
  Function.Injective.module ℝ
    ({ toFun := toBoundedContinuousFunction
       map_zero' := toBoundedContinuousFunction_zero
       map_add' := toBoundedContinuousFunction_add } : HolderSpace α X Y →+ (X →ᵇ Y))
    toBoundedContinuousFunction_injective toBoundedContinuousFunction_smul

/-- The supremum-plus-Hölder norm, combining uniform size with the global Hölder seminorm. -/
instance instNorm : Norm (HolderSpace α X Y) where
  norm f := holderNorm α f.toBoundedContinuousFunction

/-- The Hölder-space norm is the supremum-plus-Hölder norm of the underlying bounded continuous
function.  This is the single unfolding of `instNorm`; every other norm computation rewrites with
it instead of reducing through the wrapper again. -/
theorem norm_eq_holderNorm (f : HolderSpace α X Y) :
    ‖f‖ = holderNorm α f.toBoundedContinuousFunction := (rfl)

/-- The Hölder-space norm is the sum of the supremum norm and the global Hölder seminorm. -/
@[simp]
theorem norm_def (f : HolderSpace α X Y) :
    ‖f‖ = ‖f.toBoundedContinuousFunction‖ +
      nnHolderNorm α (f.toBoundedContinuousFunction : X → Y) := by
  rw [norm_eq_holderNorm, holderNorm_def]

noncomputable instance instNormedAddCommGroup : NormedAddCommGroup (HolderSpace α X Y) :=
  let core : NormedSpace.Core ℝ (HolderSpace α X Y) :=
    { norm_nonneg := fun f ↦ by
        rw [norm_eq_holderNorm]
        exact holderNorm_nonneg f.toBoundedContinuousFunction
      norm_smul := fun c f ↦ by
        rw [norm_eq_holderNorm, norm_eq_holderNorm, toBoundedContinuousFunction_smul]
        exact holderNorm_smul c f.toBoundedContinuousFunction f.memHolder
      norm_triangle := fun f g ↦ by
        rw [norm_eq_holderNorm, norm_eq_holderNorm, norm_eq_holderNorm,
          toBoundedContinuousFunction_add]
        exact holderNorm_add_le f.toBoundedContinuousFunction g.toBoundedContinuousFunction
          f.memHolder g.memHolder
      norm_eq_zero_iff := fun f ↦ by
        constructor
        · intro hf
          apply ext
          intro x
          apply norm_eq_zero.mp
          exact le_antisymm
            ((f.toBoundedContinuousFunction.norm_coe_le_norm x).trans
              ((norm_le_holderNorm f.toBoundedContinuousFunction).trans_eq
                ((norm_eq_holderNorm f).symm.trans hf)))
            (norm_nonneg (f x))
        · rintro rfl
          rw [norm_eq_holderNorm, toBoundedContinuousFunction_zero]
          exact holderNorm_zero α }
  NormedAddCommGroup.ofCore core

noncomputable instance instNormedSpace : NormedSpace ℝ (HolderSpace α X Y) :=
  { toModule := inferInstance
    norm_smul_le := fun c f ↦ by
      rw [norm_eq_holderNorm, norm_eq_holderNorm, toBoundedContinuousFunction_smul]
      exact (holderNorm_smul c f.toBoundedContinuousFunction f.memHolder).le }

/-- The supremum norm is controlled by the Hölder-space norm. -/
theorem norm_toBoundedContinuousFunction_le (f : HolderSpace α X Y) :
    ‖f.toBoundedContinuousFunction‖ ≤ ‖f‖ :=
  norm_le_holderNorm f.toBoundedContinuousFunction

/-- Forgetting the Hölder bound is a continuous linear map to bounded continuous functions. -/
def toBoundedContinuousFunctionCLM : HolderSpace α X Y →L[ℝ] (X →ᵇ Y) :=
  LinearMap.mkContinuous
    { toFun := toBoundedContinuousFunction
      map_add' := toBoundedContinuousFunction_add
      map_smul' := toBoundedContinuousFunction_smul } 1 fun f ↦ by
        rw [one_mul]
        exact norm_toBoundedContinuousFunction_le f

@[simp]
theorem toBoundedContinuousFunctionCLM_apply (f : HolderSpace α X Y) :
    toBoundedContinuousFunctionCLM f = f.toBoundedContinuousFunction := (rfl)

/-- Forgetting the Hölder bound has operator norm at most one. -/
theorem norm_toBoundedContinuousFunctionCLM_le_one :
    ‖toBoundedContinuousFunctionCLM (α := α) (X := X) (Y := Y)‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

private theorem holderWith_sub_of_tendsto_of_norm_sub_le {u : ℕ → HolderSpace α X Y}
    {F : X →ᵇ Y} (hF : Tendsto (fun n ↦ (u n).toBoundedContinuousFunction) atTop (𝓝 F))
    (N : ℕ) (C : ℝ≥0) (hbound : ∀ n ≥ N, ‖u n - u N‖ ≤ C) :
    HolderWith C α (fun x ↦ F x - u N x) := by
  intro x y
  have hx : Tendsto (fun n ↦ (u n).toBoundedContinuousFunction x) atTop (𝓝 (F x)) :=
    ((BoundedContinuousFunction.evalCLM ℝ x).continuous.tendsto F).comp hF
  have hy : Tendsto (fun n ↦ (u n).toBoundedContinuousFunction y) atTop (𝓝 (F y)) :=
    ((BoundedContinuousFunction.evalCLM ℝ y).continuous.tendsto F).comp hF
  refine le_of_tendsto ((hx.sub tendsto_const_nhds).edist (hy.sub tendsto_const_nhds)) ?_
  filter_upwards [eventually_ge_atTop N] with n hn
  have hseminorm :
      nnHolderNorm α ((u n - u N).toBoundedContinuousFunction : X → Y) ≤ C := by
    exact_mod_cast (nnHolderNorm_le_holderNorm
      (u n - u N).toBoundedContinuousFunction).trans (hbound n hn)
  refine ((u n - u N).memHolder.holderWith x y).trans ?_
  gcongr

private theorem norm_sub_limit_toBoundedContinuousFunction_le
    {u : ℕ → HolderSpace α X Y} {F : X →ᵇ Y}
    (hF : Tendsto (fun n ↦ (u n).toBoundedContinuousFunction) atTop (𝓝 F))
    (N : ℕ) (C : ℝ) (hbound : ∀ n ≥ N, ‖u n - u N‖ ≤ C) :
    ‖F - (u N).toBoundedContinuousFunction‖ ≤ C := by
  rw [← dist_eq_norm]
  refine le_of_tendsto (hF.dist tendsto_const_nhds) ?_
  filter_upwards [eventually_ge_atTop N] with n hn
  calc
    dist (u n).toBoundedContinuousFunction (u N).toBoundedContinuousFunction =
        ‖(u n - u N).toBoundedContinuousFunction‖ := by
      rw [dist_eq_norm, toBoundedContinuousFunction_sub]
    _ ≤ ‖u n - u N‖ := norm_toBoundedContinuousFunction_le _
    _ ≤ C := hbound n hn

/-- Bounded global `α`-Hölder functions form a Banach space when the codomain is Banach. -/
noncomputable instance instCompleteSpace [CompleteSpace Y] : CompleteSpace (HolderSpace α X Y) :=
  Metric.complete_of_cauchySeq_tendsto fun u hu ↦ by
    have hu' : CauchySeq (fun n ↦ (u n).toBoundedContinuousFunction) :=
      (toBoundedContinuousFunctionCLM (α := α) (X := X) (Y := Y)).uniformContinuous.comp_cauchySeq
        hu
    obtain ⟨F, hF⟩ := cauchySeq_tendsto_of_complete hu'
    rcases Metric.cauchySeq_iff.mp hu 1 zero_lt_one with ⟨N₀, hN₀⟩
    have hbound₀ : ∀ n ≥ N₀, ‖u n - u N₀‖ ≤ (1 : ℝ) := by
      intro n hn
      simpa only [dist_eq_norm] using (hN₀ n hn N₀ le_rfl).le
    have hholderDiff₀ : HolderWith 1 α (fun x ↦ F x - u N₀ x) :=
      holderWith_sub_of_tendsto_of_norm_sub_le hF N₀ 1 hbound₀
    have hholderF : MemHolder α (F : X → Y) := by
      have h := hholderDiff₀.memHolder.add (u N₀).memHolder
      have heq : ((fun x ↦ F x - u N₀ x) +
          ((u N₀).toBoundedContinuousFunction : X → Y)) = (F : X → Y) := by
        funext x
        exact sub_add_cancel (F x) (u N₀ x)
      rw [heq] at h
      exact h
    let f : HolderSpace α X Y := ofBoundedContinuousFunction F hholderF
    refine ⟨f, Metric.tendsto_atTop.2 fun ε hε ↦ ?_⟩
    let C : ℝ≥0 := ⟨ε / 4, (div_nonneg hε.le (by norm_num))⟩
    have hC : (C : ℝ) = ε / 4 := rfl
    rcases Metric.cauchySeq_iff.mp hu (ε / 4) (div_pos hε (by norm_num)) with ⟨N, hN⟩
    have hbound : ∀ n ≥ N, ‖u n - u N‖ ≤ C := by
      intro n hn
      rw [hC]
      simpa only [dist_eq_norm] using (hN n hn N le_rfl).le
    have hholderDiff : HolderWith C α (fun x ↦ F x - u N x) :=
      holderWith_sub_of_tendsto_of_norm_sub_le hF N C hbound
    have hsup : ‖F - (u N).toBoundedContinuousFunction‖ ≤ C := by
      exact_mod_cast norm_sub_limit_toBoundedContinuousFunction_le hF N C hbound
    refine ⟨N, fun n hn ↦ ?_⟩
    have hfF : f.toBoundedContinuousFunction = F :=
      toBoundedContinuousFunction_ofBoundedContinuousFunction F hholderF
    have hseminorm :
        nnHolderNorm α ((f - u N).toBoundedContinuousFunction : X → Y) ≤ C := by
      rw [toBoundedContinuousFunction_sub, hfF]
      exact hholderDiff.nnholderNorm_le
    have hsup' : ‖(f - u N).toBoundedContinuousFunction‖ ≤ C := by
      rw [toBoundedContinuousFunction_sub, hfF]
      exact hsup
    have hlimit : ‖u N - f‖ ≤ 2 * C := by
      rw [norm_sub_rev, norm_def]
      calc
        ‖(f - u N).toBoundedContinuousFunction‖ +
            (nnHolderNorm α ((f - u N).toBoundedContinuousFunction : X → Y) : ℝ) ≤
            (C : ℝ) + C := add_le_add hsup' (by exact_mod_cast hseminorm)
        _ = 2 * (C : ℝ) := by ring
    rw [dist_eq_norm]
    calc
      ‖u n - f‖ ≤ ‖u n - u N‖ + ‖u N - f‖ := by
        calc
          ‖u n - f‖ = ‖(u n - u N) + (u N - f)‖ := congrArg norm (by abel)
          _ ≤ ‖u n - u N‖ + ‖u N - f‖ := norm_add_le _ _
      _ ≤ C + 2 * C := add_le_add (hbound n hn) hlimit
      _ < ε := by
        rw [hC]
        linarith

/-- The Hölder seminorm is controlled by the Hölder-space norm. -/
theorem nnHolderNorm_le (f : HolderSpace α X Y) :
    (nnHolderNorm α (f.toBoundedContinuousFunction : X → Y) : ℝ) ≤ ‖f‖ :=
  nnHolderNorm_le_holderNorm f.toBoundedContinuousFunction

end HolderSpace

end TauCeti
