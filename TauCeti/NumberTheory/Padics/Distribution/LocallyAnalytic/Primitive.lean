/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Distribution.LocallyAnalytic.Derivative

import TauCeti.Analysis.Normed.Field.NatCast
import TauCeti.Order.Filter.Cofinite.Basic

/-!
# Primitives of locally analytic functions on ℤₚ

In characteristic zero an analytic function of level `h` has a primitive of level `h + 1`,
normalized to vanish at the natural representative of every residue class at that level.
Re-expansion to the smaller discs bounds the degree-`n` coefficient by a factor of `‖p‖^n`.
This exponential decay absorbs the growth from dividing by `n + 1` in termwise integration.
The construction is a continuous linear map between these two stages.

Consequently differentiation is surjective on the algebraic direct limit, and its kernel
consists of the locally constant functions. This describes the ambiguity of a primitive.

## Main declarations

* `TauCeti.AnalyticStage.primitive` integrates after one level of re-expansion.
* `TauCeti.AnalyticStage.derivative_primitive` computes its derivative.
* `TauCeti.AnalyticStage.eq_primitive_iff` characterizes the normalized primitive.
* `TauCeti.LocallyAnalytic.derivative_surjective` gives existence of locally analytic primitives.

## References

* J. Kohlhaase, *The cohomology of locally analytic representations*, J. reine angew. Math.
  651 (2011), §4, Corollary 4.3.
-/

public section

open Filter Topology
open scoped ZeroAtInfty

namespace TauCeti

variable {p : ℕ} [hp : Fact p.Prime]
variable {E : Type*} [NormedAddCommGroup E]

local instance {K : Type*} [Field K] [CharZero K] : NeZero (p : K) :=
  ⟨Nat.cast_ne_zero.mpr hp.out.ne_zero⟩

namespace AnalyticStage

variable {h : ℕ} [IsUltrametricDist E]

section Primitive

variable {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E]
  [Module ℤ_[p] E] [IsBoundedSMul ℤ_[p] E] [SMulCommClass ℤ_[p] 𝕜 E] [CompleteSpace E]

private noncomputable def primitiveCoeff (c : AnalyticStage p h E)
    (i : ZMod (p ^ (h + 1)) × ℕ) : E :=
  ((p : 𝕜) ^ (h + 1) * (i.2 : 𝕜)⁻¹) • transition 𝕜 c (i.1, i.2 - 1)

private theorem tendsto_primitiveWeight :
    Tendsto (fun n : ℕ ↦ ‖(n : 𝕜)⁻¹‖ * ‖(p : ℤ_[p])‖ ^ (n - 1)) atTop (𝓝 0) :=
  NormedField.tendsto_norm_inv_natCast_mul_pow_pred 𝕜
    (norm_nonneg _) (PadicInt.norm_p_lt_one (p := p))

private theorem norm_primitiveCoeff_le (c : AnalyticStage p h E)
    (i : ZMod (p ^ (h + 1)) × ℕ) :
    ‖primitiveCoeff (𝕜 := 𝕜) c i‖ ≤
      ‖(i.2 : 𝕜)⁻¹‖ * ‖(p : ℤ_[p])‖ ^ (i.2 - 1) * (‖(p : 𝕜) ^ (h + 1)‖ * ‖c‖) := by
  rw [primitiveCoeff, norm_smul, norm_mul]
  calc
    _ ≤ (‖(p : 𝕜) ^ (h + 1)‖ * ‖(i.2 : 𝕜)⁻¹‖) *
        (‖(p : ℤ_[p])‖ ^ (i.2 - 1) * ‖c‖) := by
      gcongr
      exact norm_transition_apply_le 𝕜 c i.1 (i.2 - 1)
    _ = _ := by ring

private theorem tendsto_primitiveCoeff (c : AnalyticStage p h E) :
    Tendsto (primitiveCoeff (𝕜 := 𝕜) c) cofinite (𝓝 0) := by
  apply squeeze_zero_norm (norm_primitiveCoeff_le c)
  have hw := tendsto_primitiveWeight (p := p) (𝕜 := 𝕜)
  rw [← Nat.cofinite_eq_atTop] at hw
  simpa only [zero_mul, Function.comp_apply] using
    (hw.comp Filter.tendsto_snd_cofinite).mul_const (‖(p : 𝕜) ^ (h + 1)‖ * ‖c‖)

private noncomputable def primitiveLinearMap :
    AnalyticStage p h E →ₗ[𝕜] AnalyticStage p (h + 1) E where
  toFun c := ZeroAtInftyContinuousMap.mkOfDiscrete (primitiveCoeff (𝕜 := 𝕜) c)
    (tendsto_primitiveCoeff c)
  map_add' c d := by
    ext i
    simp [primitiveCoeff, smul_add]
  map_smul' a c := by
    ext i
    simp [primitiveCoeff, smul_comm _ a]

private theorem primitiveLinearMap_apply (c : AnalyticStage p h E)
    (i : ZMod (p ^ (h + 1)) × ℕ) :
    primitiveLinearMap (𝕜 := 𝕜) c i = primitiveCoeff (𝕜 := 𝕜) c i :=
  congrFun (ZeroAtInftyContinuousMap.coe_mkOfDiscrete _ (tendsto_primitiveCoeff c)) i

/-- The termwise primitive after re-expansion to level `h + 1`, with constant coefficient zero
on each disc. In characteristic zero its derivative is the re-expanded input. -/
noncomputable def primitive : AnalyticStage p h E →L[𝕜] AnalyticStage p (h + 1) E :=
  { primitiveLinearMap with
    cont := by
      obtain ⟨B, hB⟩ := (tendsto_primitiveWeight (p := p) (𝕜 := 𝕜)).bddAbove_range
      refine AddMonoidHomClass.continuous_of_bound (primitiveLinearMap (𝕜 := 𝕜))
        (B * ‖(p : 𝕜) ^ (h + 1)‖) fun c ↦ ?_
      have hB₀ : 0 ≤ B := by
        simpa only [Nat.cast_zero, inv_zero, norm_zero, zero_mul] using hB (Set.mem_range_self 0)
      refine (ZeroAtInftyContinuousMap.norm_le (mul_nonneg (mul_nonneg hB₀ (norm_nonneg _))
        (norm_nonneg c))).mpr fun i ↦ ?_
      rw [mul_assoc, primitiveLinearMap_apply]
      exact (norm_primitiveCoeff_le (𝕜 := 𝕜) c i).trans
        (mul_le_mul_of_nonneg_right (hB (Set.mem_range_self i.2)) (by positivity)) }

/-- The primitive integrates each positive-degree coefficient and has zero constant term. -/
theorem primitive_apply (c : AnalyticStage p h E) (i : ZMod (p ^ (h + 1)) × ℕ) :
    primitive (𝕜 := 𝕜) c i =
      ((p : 𝕜) ^ (h + 1) * (i.2 : 𝕜)⁻¹) • transition 𝕜 c (i.1, i.2 - 1) :=
  primitiveLinearMap_apply c i

/-- The primitive has constant coefficient zero at every level-`h + 1` centre. -/
@[simp]
theorem primitive_apply_zero (c : AnalyticStage p h E) (a : ZMod (p ^ (h + 1))) :
    primitive (𝕜 := 𝕜) c (a, 0) = 0 := by
  simp [primitive_apply]

/-- The coefficient in degree `n + 1` integrates the re-expanded coefficient in degree `n`.
The factor `p^(h+1)` converts integration in the normalized coordinate to integration in `x`. -/
@[simp]
theorem primitive_apply_succ (c : AnalyticStage p h E) (a : ZMod (p ^ (h + 1))) (n : ℕ) :
    primitive (𝕜 := 𝕜) c (a, n + 1) =
      ((p : 𝕜) ^ (h + 1) * ((n + 1 : ℕ) : 𝕜)⁻¹) • transition 𝕜 c (a, n) := by
  simp [primitive_apply]

/-- Differentiating the primitive gives the input function re-expanded on the smaller discs. -/
@[simp]
theorem derivative_primitive [CharZero 𝕜] (c : AnalyticStage p h E) :
    derivative 𝕜 (primitive (𝕜 := 𝕜) c) = transition 𝕜 c := by
  ext ⟨a, n⟩
  rw [derivative_apply, primitive_apply_succ, ← Nat.cast_smul_eq_nsmul 𝕜, smul_smul, smul_smul]
  have hn : ((n + 1 : ℕ) : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  have hp' : (p : 𝕜) ^ (h + 1) ≠ 0 := pow_ne_zero _ (NeZero.ne _)
  set b : 𝕜 := (p : 𝕜) ^ (h + 1)
  have hscalar : b⁻¹ * ((n + 1 : ℕ) : 𝕜) * (b * ((n + 1 : ℕ) : 𝕜)⁻¹) = 1 := by
    field_simp
  rw [hscalar, one_smul]

/-- The normalized primitive is the unique stage vector whose derivative is the re-expanded
input and whose constant coefficient is zero on each disc. -/
theorem eq_primitive_iff [CharZero 𝕜] (c : AnalyticStage p h E)
    (g : AnalyticStage p (h + 1) E) :
    g = primitive (𝕜 := 𝕜) c ↔ derivative 𝕜 g = transition 𝕜 c ∧ ∀ a, g (a, 0) = 0 := by
  constructor
  · rintro rfl
    simp
  · rintro ⟨hg, hzero⟩
    have hderiv : derivative 𝕜 (g - primitive (𝕜 := 𝕜) c) = 0 := by simp [hg]
    have hcoeff := (mem_polynomialSubmodule 𝕜 (g - primitive (𝕜 := 𝕜) c)).mp
      ((derivative_eq_zero_iff 𝕜 _).mp hderiv)
    apply sub_eq_zero.mp
    ext ⟨a, n⟩
    cases n with
    | zero => simp [hzero]
    | succ n => simpa only [zero_apply] using hcoeff a (n + 1) (Nat.succ_pos n)

end Primitive

end AnalyticStage

namespace LocallyAnalytic

open AnalyticStage

variable [Module ℤ_[p] E] [IsBoundedSMul ℤ_[p] E] [IsUltrametricDist E] [CompleteSpace E]

/-- Every locally analytic function admits a locally analytic primitive. A representative at
level `h` gives a primitive at level `h + 1`. -/
theorem derivative_surjective {𝕜 : Type*} [NormedField 𝕜] [CharZero 𝕜] [NormedSpace 𝕜 E]
    [SMulCommClass ℤ_[p] 𝕜 E] :
    Function.Surjective (derivative (p := p) (E := E) 𝕜) := by
  intro f
  obtain ⟨h, c, rfl⟩ := exists_ofStage 𝕜 f
  exact ⟨ofStage 𝕜 (h + 1) (AnalyticStage.primitive (𝕜 := 𝕜) c), by simp⟩

end LocallyAnalytic

end TauCeti
