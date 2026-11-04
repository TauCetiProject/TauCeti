/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Perfectoid.UniformTilt.Sharp
public import TauCeti.RingTheory.Perfectoid.Padic
public import TauCeti.NumberTheory.Padics.Complex.Basic

/-!
# The sharp map on the integral tilt of the p-adic complex numbers

These checks test the sharp map on the integral tilt `B♭⁺ = lim_{x ↦ x ^ p} B°` of `B = ℂ_p`, for
a pseudouniformiser `ϖ` with compatible `p`-power roots `ϖ ^ (1 / p ^ n)`. Write
`ϖ♭ = (ϖ ^ (1 / p ^ n))ₙ` and `ϖ♭ ^ (1 / p) = (ϖ ^ (1 / p ^ (n + 1)))ₙ`:

* the sharp of `ϖ♭ ^ (1 / p)` is `ϖ ^ (1 / p)`, so `sharpQuotEquiv` sends the class of
  `ϖ♭ ^ (1 / p)` modulo `ϖ♭` to the class of `ϖ ^ (1 / p)` modulo `ϖ`;
* that class is nonzero, since `‖ϖ‖ < ‖ϖ ^ (1 / p)‖`; through the isomorphism, `ϖ♭ ^ (1 / p)` is
  not a multiple of `ϖ♭` in `B♭⁺`;
* its `p`-th power vanishes in `ℂ_p° ⧸ ϖ`, so the quotient is not reduced.

## References

* P. Scholze, *Étale cohomology of diamonds*, Lemma 3.10.
-/

public section

open TauCeti.Huber TauCeti.Perfectoid

namespace TauCeti.Examples.UniformTiltSharp

variable (p : ℕ) [hp : Fact p.Prime]

/-- `p` is topologically nilpotent in `ℂ_p`, as `‖p‖ < 1`. -/
local instance : Fact (IsTopologicallyNilpotent (p : ℂ_[p])) :=
  ⟨tendsto_pow_atTop_nhds_zero_of_norm_lt_one (PadicComplex.norm_p_lt_one p)⟩

variable {p} (ϖ : PseudoUniformizerRoots p ℂ_[p])

/-- `ϖ♭ ^ (1 / p ^ k) = (ϖ ^ (1 / p ^ (n + k)))ₙ` in the integral tilt of `ℂ_p`. -/
noncomputable def rootTilt (k : ℕ) :
    uniformTilt.plusSubring p (isRingOfIntegralElements_powerBoundedSubring ℂ_[p]) :=
  ⟨uniformTilt.mk (fun n ↦ ϖ.root (n + k)) fun n ↦ by
      rw [Nat.add_right_comm]
      exact ϖ.root_succ_pow (n + k),
    uniformTilt.mem_plusSubring_iff_coeff_zero.mpr <| by
      rw [uniformTilt.coeff_mk, zero_add, ← ϖ.coe_rootPB]
      exact (ϖ.rootPB k).2⟩

/-- The sharp of `ϖ♭ ^ (1 / p ^ k)` is `ϖ ^ (1 / p ^ k)`. -/
theorem sharpPlus_rootTilt (k : ℕ) :
    uniformTilt.sharpPlus _ (rootTilt ϖ k) = ϖ.rootPB k :=
  Subtype.ext <| by
    rw [uniformTilt.coe_sharpPlus, rootTilt, uniformTilt.coeff_mk, zero_add, ϖ.coe_rootPB]

/-- The sharp `ϖ` of `ϖ♭` is a unit of `ℂ_p`. -/
theorem isUnit_coeff_zero_rootTilt :
    IsUnit (uniformTilt.coeff p ℂ_[p] 0 (rootTilt ϖ 0 : uniformTilt p ℂ_[p])) := by
  rw [← uniformTilt.coe_sharpPlus, sharpPlus_rootTilt, ϖ.coe_rootPB]
  exact ϖ.isPseudoUniformizer_root_zero.isUnit

/-- The sharp `ϖ` of `ϖ♭` divides `p` in `ℂ_p°`. -/
theorem sharpPlus_rootTilt_zero_dvd :
    uniformTilt.sharpPlus _ (rootTilt ϖ 0) ∣ (p : powerBoundedSubring ℂ_[p]) := by
  rw [sharpPlus_rootTilt]
  exact (dvd_pow_self _ hp.out.ne_zero).trans (ϖ.rootPB_pow_dvd 0)

/-- `sharpQuotEquiv` sends the class of `ϖ♭ ^ (1 / p)` modulo `ϖ♭` to the class of
`ϖ ^ (1 / p)` modulo `ϖ`. -/
theorem sharpQuotEquiv_mk_rootTilt_one :
    uniformTilt.sharpQuotEquiv _ (isUnit_coeff_zero_rootTilt ϖ) (sharpPlus_rootTilt_zero_dvd ϖ)
      (Ideal.Quotient.mk _ (rootTilt ϖ 1)) =
      Ideal.Quotient.mk _ (ϖ.rootPB 1) := by
  simp only [uniformTilt.sharpQuotEquiv_mk, sharpPlus_rootTilt]

/-- `ϖ ^ (1 / p)` is not a multiple of `ϖ` in `ℂ_p°`: `‖ϖ‖ = ‖ϖ ^ (1 / p)‖ ^ p < ‖ϖ ^ (1 / p)‖`. -/
theorem rootPB_one_not_mem_span :
    ϖ.rootPB 1 ∉ Ideal.span {uniformTilt.sharpPlus _ (rootTilt ϖ 0)} := by
  rw [sharpPlus_rootTilt, Ideal.mem_span_singleton']
  rintro ⟨c, hc⟩
  have hc' : (c : ℂ_[p]) * ϖ.root 0 = ϖ.root 1 := by
    simpa only [Subring.coe_mul, ϖ.coe_rootPB] using congrArg Subtype.val hc
  have hc1 : ‖(c : ℂ_[p])‖ ≤ 1 :=
    isPowerBounded_iff_norm_le_one.mp (mem_powerBoundedSubring.mp c.2)
  obtain ⟨h0, h1⟩ := isPseudoUniformizer_iff_norm_lt_one.mp (ϖ.isPseudoUniformizer_root 1)
  have hle : ‖ϖ.root 1‖ ≤ ‖ϖ.root 1‖ ^ p :=
    calc ‖ϖ.root 1‖ = ‖(c : ℂ_[p])‖ * ‖ϖ.root 0‖ := by rw [← hc', norm_mul]
      _ ≤ ‖ϖ.root 0‖ := mul_le_of_le_one_left (norm_nonneg _) hc1
      _ = ‖ϖ.root 1‖ ^ p := by rw [← ϖ.root_succ_pow 0, norm_pow]
  exact absurd hle (not_le.mpr (pow_lt_self_of_lt_one₀ (norm_pos_iff.mpr h0) h1 hp.out.one_lt))

/-- The class of `ϖ♭ ^ (1 / p)` modulo `ϖ♭` is nonzero, as its image under `sharpQuotEquiv`
is. -/
theorem mk_rootTilt_one_ne_zero :
    Ideal.Quotient.mk (Ideal.span {rootTilt ϖ 0}) (rootTilt ϖ 1) ≠ 0 := by
  rw [Ne, ← (uniformTilt.sharpQuotEquiv _ (isUnit_coeff_zero_rootTilt ϖ)
    (sharpPlus_rootTilt_zero_dvd ϖ)).map_eq_zero_iff, sharpQuotEquiv_mk_rootTilt_one,
    Ideal.Quotient.eq_zero_iff_mem]
  exact rootPB_one_not_mem_span ϖ

/-- The `p`-th power of the sharp of `ϖ♭ ^ (1 / p)` vanishes modulo `ϖ`, although the sharp itself
does not: `ℂ_p° ⧸ ϖ` is not reduced. -/
theorem sharpQuot_rootTilt_one_pow :
    uniformTilt.sharpQuot _ (sharpPlus_rootTilt_zero_dvd ϖ) (rootTilt ϖ 1) ^ p = 0 ∧
      uniformTilt.sharpQuot _ (sharpPlus_rootTilt_zero_dvd ϖ) (rootTilt ϖ 1) ≠ 0 := by
  refine ⟨?_, ?_⟩
  · rw [uniformTilt.sharpQuot_apply, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    simp only [sharpPlus_rootTilt, ϖ.rootPB_succ_pow]
    exact Ideal.mem_span_singleton_self _
  · rw [uniformTilt.sharpQuot_apply, Ne, Ideal.Quotient.eq_zero_iff_mem]
    simpa only [sharpPlus_rootTilt] using rootPB_one_not_mem_span ϖ

end TauCeti.Examples.UniformTiltSharp
