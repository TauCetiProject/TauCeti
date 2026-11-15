/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Perfectoid.UniformTilt.Quotient
public import TauCeti.RingTheory.Perfectoid.Padic
public import TauCeti.NumberTheory.Padics.Complex.Basic

/-!
# Examples of quotients of the integral tilt

These examples test the isomorphism `B♭° ⧸ (π) ≃+* B° ⧸ (π♯)` for `B = ℂ_p`, with a
pseudouniformiser `ϖ` of `ℂ_p` with compatible `p`-power roots `ϖ ^ (1 / p ^ n)`:

* the element `ϖ♭ = (ϖ ^ (1 / p ^ n))ₙ` of `B♭°` satisfies the hypotheses, giving
  `B♭° ⧸ (ϖ♭) ≃+* B° ⧸ (ϖ)`;
* the isomorphism sends the class of `ϖ♭ ^ (1 / p) = (ϖ ^ (1 / p ^ (n + 1)))ₙ` to the class of
  `ϖ ^ (1 / p)`, which is nonzero because `‖ϖ‖ < ‖ϖ ^ (1 / p)‖`; so `ϖ♭ ^ (1 / p) ∉ (ϖ♭)`.
-/

public section

open TauCeti.Huber TauCeti.Perfectoid

namespace TauCeti.Examples.UniformTiltQuotient

variable (p : ℕ) [hp : Fact p.Prime]

/-- `p` is topologically nilpotent in `ℂ_p`, as `‖p‖ < 1`. -/
local instance : Fact (IsTopologicallyNilpotent (p : ℂ_[p])) :=
  ⟨tendsto_pow_atTop_nhds_zero_of_norm_lt_one (PadicComplex.norm_p_lt_one p)⟩

variable {p} (ϖ : PseudoUniformizerRoots p ℂ_[p])

/-- The element `ϖ♭ ^ (1 / p ^ k) = (ϖ ^ (1 / p ^ (n + k)))ₙ` of the integral tilt `ℂ_p♭°`. -/
noncomputable def rootTilt (k : ℕ) :
    uniformTilt.plusSubring p (isRingOfIntegralElements_powerBoundedSubring ℂ_[p]) :=
  ⟨uniformTilt.mk (fun n ↦ ϖ.root (n + k)) fun n ↦ by
      rw [Nat.add_right_comm]
      exact ϖ.root_succ_pow (n + k),
    by
      rw [uniformTilt.mem_plusSubring_iff_coeff_zero, uniformTilt.coeff_mk, zero_add,
        ← ϖ.coe_rootPB]
      exact (ϖ.rootPB k).2⟩

theorem plusSharp_rootTilt (k : ℕ) :
    uniformTilt.plusSharp p (isRingOfIntegralElements_powerBoundedSubring ℂ_[p]) (rootTilt ϖ k) =
      ϖ.rootPB k :=
  Subtype.ext <| by
    rw [uniformTilt.coe_plusSharp, rootTilt, uniformTilt.coeff_mk, zero_add, ϖ.coe_rootPB]

theorem isUnit_coeff_zero_rootTilt :
    IsUnit (uniformTilt.coeff p ℂ_[p] 0 (rootTilt ϖ 0 : uniformTilt p ℂ_[p])) := by
  rw [rootTilt, uniformTilt.coeff_mk]
  exact ϖ.isPseudoUniformizer_root_zero.isUnit

theorem plusSharp_rootTilt_zero_dvd :
    uniformTilt.plusSharp p (isRingOfIntegralElements_powerBoundedSubring ℂ_[p]) (rootTilt ϖ 0) ∣
      p := by
  rw [plusSharp_rootTilt]
  exact (dvd_pow_self _ hp.out.ne_zero).trans (ϖ.rootPB_pow_dvd 0)

/-- `ℂ_p♭° ⧸ (ϖ♭) ≃+* ℂ_p° ⧸ (ϖ)`. -/
noncomputable example :
    uniformTilt.plusSubring p (isRingOfIntegralElements_powerBoundedSubring ℂ_[p]) ⧸
        Ideal.span {rootTilt ϖ 0} ≃+*
      powerBoundedSubring ℂ_[p] ⧸ Ideal.span {ϖ.rootPB 0} :=
  (uniformTilt.sharpQuotEquiv _ (isUnit_coeff_zero_rootTilt ϖ) (plusSharp_rootTilt_zero_dvd ϖ)
    (uniformTilt.sharpQuot_surjective _ _)).trans (Ideal.quotEquivOfEq (by rw [plusSharp_rootTilt]))

/-- `ϖ ^ (1 / p)` is not divisible by `ϖ` in `ℂ_p°`: `‖ϖ‖ = ‖ϖ ^ (1 / p)‖ ^ p < ‖ϖ ^ (1 / p)‖`. -/
theorem rootPB_one_notMem_span_rootPB_zero : ϖ.rootPB 1 ∉ Ideal.span {ϖ.rootPB 0} := by
  rw [Ideal.mem_span_singleton]
  rintro ⟨c, hc⟩
  have hc' : ϖ.root 1 = ϖ.root 1 ^ p * (c : ℂ_[p]) := by
    rw [ϖ.root_succ_pow 0]
    simpa using congrArg Subtype.val hc
  have hc1 : ‖(c : ℂ_[p])‖ ≤ 1 :=
    isPowerBounded_iff_norm_le_one.mp (mem_powerBoundedSubring.mp c.2)
  obtain ⟨h0, h1⟩ := isPseudoUniformizer_iff_norm_lt_one.mp (ϖ.isPseudoUniformizer_root 1)
  have hle : ‖ϖ.root 1‖ ≤ ‖ϖ.root 1‖ ^ p :=
    calc ‖ϖ.root 1‖ = ‖ϖ.root 1‖ ^ p * ‖(c : ℂ_[p])‖ := by rw [← norm_pow, ← norm_mul, ← hc']
      _ ≤ ‖ϖ.root 1‖ ^ p := mul_le_of_le_one_right (by positivity) hc1
  exact absurd hle (not_le.mpr (pow_lt_self_of_lt_one₀ (norm_pos_iff.mpr h0) h1 hp.out.one_lt))

/-- The isomorphism sends the class of `ϖ♭ ^ (1 / p)` to the class of `ϖ ^ (1 / p)`. -/
theorem sharpQuotEquiv_mk_rootTilt_one :
    uniformTilt.sharpQuotEquiv _ (isUnit_coeff_zero_rootTilt ϖ) (plusSharp_rootTilt_zero_dvd ϖ)
        (uniformTilt.sharpQuot_surjective _ _) (Ideal.Quotient.mk _ (rootTilt ϖ 1)) =
      Ideal.Quotient.mk _ (ϖ.rootPB 1) := by
  rw [uniformTilt.sharpQuotEquiv_mk, plusSharp_rootTilt, plusSharp_rootTilt]

/-- `ϖ♭ ^ (1 / p)` does not lie in the ideal `(ϖ♭)` of `ℂ_p♭°`. -/
theorem rootTilt_one_notMem_span_rootTilt_zero :
    rootTilt ϖ 1 ∉ Ideal.span {rootTilt ϖ 0} := by
  rw [← Ideal.Quotient.eq_zero_iff_mem,
    ← (uniformTilt.sharpQuotEquiv _ (isUnit_coeff_zero_rootTilt ϖ)
      (plusSharp_rootTilt_zero_dvd ϖ) (uniformTilt.sharpQuot_surjective _ _)).map_eq_zero_iff,
    sharpQuotEquiv_mk_rootTilt_one, Ideal.Quotient.eq_zero_iff_mem, plusSharp_rootTilt]
  exact rootPB_one_notMem_span_rootPB_zero ϖ

end TauCeti.Examples.UniformTiltQuotient
