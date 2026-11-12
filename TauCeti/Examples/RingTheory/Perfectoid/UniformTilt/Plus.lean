/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Perfectoid.Padic
public import TauCeti.NumberTheory.Padics.Complex.Basic
public import TauCeti.RingTheory.Perfectoid.UniformTilt.Plus
public import Mathlib.Algebra.CharP.Quotient

/-!
# Examples of the integral tilt

These examples test the integral tilt `B♭⁺ = lim_{x ↦ x ^ p} B°` of `B = ℂ_p` and its comparison
`B♭⁺ ≃+* PreTilt B° p` with Mathlib's tilt, for a pseudouniformiser `ϖ` of `ℂ_p` with compatible
`p`-power roots `ϖ ^ (1 / p ^ n)`, which exists as `ℂ_p` is perfectoid:

* the element `ϖ♭ = (ϖ ^ (1 / p ^ n))ₙ` of the tilt lies in the integral tilt;
* the element `ϖ♭⁻¹ = (ϖ ^ (-1 / p ^ n))ₙ` does not, its zeroth coordinate `ϖ⁻¹` not being
  power-bounded, so the integral tilt is a proper subring of the tilt;
* the zeroth coordinate of the image of `ϖ♭` in `PreTilt B° p = lim_{x ↦ x ^ p} B° ⧸ p` is the
  class of `ϖ`, which is nonzero, as `ϖ ^ p ∣ p` forces `‖p‖ < ‖ϖ‖`.

## References

* P. Scholze, *Étale cohomology of diamonds*, Lemma 3.10.
-/

public section

open TauCeti.Huber TauCeti.Perfectoid

namespace TauCeti.Examples.UniformTiltPlus

variable (p : ℕ) [hp : Fact p.Prime]

/-- `p` is topologically nilpotent in `ℂ_p`, as `‖p‖ < 1`. -/
local instance : Fact (IsTopologicallyNilpotent (p : ℂ_[p])) :=
  ⟨tendsto_pow_atTop_nhds_zero_of_norm_lt_one (PadicComplex.norm_p_lt_one p)⟩

/-- The power-bounded subring of `ℂ_p` is a ring of integral elements. -/
theorem isRingOfIntegralElements_padicComplex :
    IsRingOfIntegralElements (powerBoundedSubring ℂ_[p]) := by
  simpa only [Pair.powerBounded_plus] using (Pair.powerBounded ℂ_[p]).isRingOfIntegralElements

/-- `ℂ_p° ⧸ p` has characteristic `p`, as `p` is not a unit of `ℂ_p°`. -/
local instance : CharP (powerBoundedSubring ℂ_[p] ⧸ Ideal.span {(p : powerBoundedSubring ℂ_[p])})
    p :=
  CharP.quotient _ p fun ⟨u, hu⟩ ↦ by
    -- a unit `p` of `ℂ_p°` would have `‖p‖ ≥ 1`
    have hu' : (p : ℂ_[p]) * ((u⁻¹ : (powerBoundedSubring ℂ_[p])ˣ) : ℂ_[p]) = 1 := by
      have h := congrArg Subtype.val u.mul_inv
      rwa [hu, Subring.coe_mul, Subring.coe_natCast, Subring.coe_one] at h
    have h1 : ‖((u⁻¹ : (powerBoundedSubring ℂ_[p])ˣ) : ℂ_[p])‖ ≤ 1 :=
      isPowerBounded_iff_norm_le_one.mp (mem_powerBoundedSubring.mp (u⁻¹).1.2)
    have h2 := congrArg norm hu'
    rw [norm_mul, norm_one] at h2
    have := PadicComplex.norm_p_lt_one p
    nlinarith [norm_nonneg (p : ℂ_[p])]

/-- `ℂ_p°` is `p`-adically complete. -/
local instance :
    IsAdicComplete (Ideal.span {(p : powerBoundedSubring ℂ_[p])}) (powerBoundedSubring ℂ_[p]) :=
  IsUniform.isAdicComplete_span_singleton _ <| by
    rw [Subring.coe_natCast]
    exact isPseudoUniformizer_natCast_padicComplex p

variable (ϖ : PseudoUniformizerRoots p ℂ_[p])

/-- `ϖ♭ = (ϖ ^ (1 / p ^ n))ₙ` lies in the integral tilt. -/
theorem mk_root_mem_plusSubring : uniformTilt.mk ϖ.root ϖ.root_succ_pow ∈
    uniformTilt.plusSubring p (isRingOfIntegralElements_padicComplex p) := by
  rw [uniformTilt.mem_plusSubring_iff_coeff_zero, uniformTilt.coeff_mk, ← ϖ.coe_rootPB]
  exact (ϖ.rootPB 0).2

/-- `ϖ♭⁻¹ = (ϖ ^ (-1 / p ^ n))ₙ` does not lie in the integral tilt: `‖ϖ⁻¹‖ > 1`. -/
theorem mk_inv_root_not_mem_plusSubring :
    uniformTilt.mk (fun n ↦ (ϖ.root n)⁻¹) (fun n ↦ by rw [inv_pow, ϖ.root_succ_pow]) ∉
      uniformTilt.plusSubring p (isRingOfIntegralElements_padicComplex p) := by
  rw [uniformTilt.mem_plusSubring_iff_coeff_zero, uniformTilt.coeff_mk, mem_powerBoundedSubring,
    isPowerBounded_iff_norm_le_one, norm_inv, not_le]
  obtain ⟨h0, h1⟩ := isPseudoUniformizer_iff_norm_lt_one.mp ϖ.isPseudoUniformizer_root_zero
  exact (one_lt_inv₀ (norm_pos_iff.mpr h0)).mpr h1

/-- The zeroth coordinate of the image of `ϖ♭` in `PreTilt ℂ_p° p`, the class of `ϖ` modulo `p`, is
nonzero. -/
theorem coeff_zero_plusEquiv_mk_root_ne_zero :
    Perfection.coeff _ p 0 (uniformTilt.plusEquiv (isRingOfIntegralElements_padicComplex p)
      (Ideal.span {(p : powerBoundedSubring ℂ_[p])}) ⟨_, mk_root_mem_plusSubring p ϖ⟩) ≠ 0 := by
  rw [uniformTilt.coeff_plusEquiv, Ne, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  -- `ϖ = p * c` and `p = ϖ ^ p * d` with `c, d ∈ ℂ_p°` would give `‖ϖ‖ ≤ ‖ϖ‖ ^ p`
  rintro ⟨c, hc⟩
  obtain ⟨d, hd⟩ := ϖ.rootPB_pow_dvd 0
  have hc' : ϖ.root 0 = p * (c : ℂ_[p]) := by
    simpa using congrArg Subtype.val hc
  have hd' : (p : ℂ_[p]) = ϖ.root 0 ^ p * (d : ℂ_[p]) := by
    simpa using congrArg Subtype.val hd
  have hc1 : ‖(c : ℂ_[p])‖ ≤ 1 :=
    isPowerBounded_iff_norm_le_one.mp (mem_powerBoundedSubring.mp c.2)
  have hd1 : ‖(d : ℂ_[p])‖ ≤ 1 :=
    isPowerBounded_iff_norm_le_one.mp (mem_powerBoundedSubring.mp d.2)
  obtain ⟨h0, h1⟩ := isPseudoUniformizer_iff_norm_lt_one.mp ϖ.isPseudoUniformizer_root_zero
  have hle : ‖ϖ.root 0‖ ≤ ‖ϖ.root 0‖ ^ p :=
    calc ‖ϖ.root 0‖ = ‖(p : ℂ_[p])‖ * ‖(c : ℂ_[p])‖ := by rw [hc', norm_mul]
      _ ≤ ‖(p : ℂ_[p])‖ := mul_le_of_le_one_right (norm_nonneg _) hc1
      _ = ‖ϖ.root 0‖ ^ p * ‖(d : ℂ_[p])‖ := by rw [hd', norm_mul, norm_pow]
      _ ≤ ‖ϖ.root 0‖ ^ p := mul_le_of_le_one_right (by positivity) hd1
  exact absurd hle (not_le.mpr (pow_lt_self_of_lt_one₀ (norm_pos_iff.mpr h0) h1 hp.out.one_lt))

end TauCeti.Examples.UniformTiltPlus
