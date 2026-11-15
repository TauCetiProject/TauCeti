/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Perfectoid.Untilt.Primitive

/-!
# Checks for the untilt along an ideal of the Witt vectors

* Degenerate case: for `ϖ = 0` the untilt is the zero ring, whatever the ideal.
* Recovery: over `𝔽_p` with `ϖ = 1`, the untilt along the primitive ideal `(p)` is `𝔽_p`, through
  `TauCeti.Perfectoid.untilt.spanPEquiv`, which sends `x♯` to `x`.
* Non-example: over `𝔽_p` with `ϖ = 1`, the untilt along the ideal `(p ^ 2)`, which has no
  distinguished generator, is not reduced, unlike every perfectoid Tate ring: `p ≠ 0` but
  `p ^ 2 = 0` there.
* For any data, the untilt is a Tate ring with pseudouniformiser `ϖ♯`, and the Hausdorff and
  completeness results apply to the untilt along `p + [ϖ] α` over any perfect ring of
  characteristic `p` which is `ϖ`-adically complete for a nonzerodivisor `ϖ`.
-/

public section

open Ideal TauCeti.Huber TauCeti.Perfectoid
open WittVector (teichmuller)
open scoped nonZeroDivisors

namespace TauCeti.Examples.UntiltChecks

variable (p : ℕ) [hp : Fact p.Prime]

/-! ### The zero ring -/

/-- **Degenerate case**: for `ϖ = 0` the untilt is the zero ring, since `[0] = 0` is inverted. -/
example {S : Type*} [CommRing S] (J : Ideal (WittVector p S)) :
    Subsingleton (untilt p (0 : S) J) :=
  IsLocalization.subsingleton (M := Submonoid.powers (Ideal.Quotient.mk J (teichmuller p 0)))
    ⟨1, by simp [WittVector.teichmuller_zero]⟩

/-! ### Untilts of `𝔽_p` -/

/-- `𝔽_p` is a localization of itself away from `1`. -/
instance isLocalizationAway_one : IsLocalization.Away (1 : ZMod p) (ZMod p) :=
  IsLocalization.away_of_isUnit_of_bijective _ isUnit_one Function.bijective_id

/-- **Recovery**: the untilt of `𝔽_p` along `(p)` with respect to `ϖ = 1` is `𝔽_p`. -/
noncomputable example : untilt p (1 : ZMod p) (span {(p : WittVector p (ZMod p))}) ≃+* ZMod p :=
  untilt.spanPEquiv p 1 (ZMod p)

/-- The recovery isomorphism sends `x♯` to `x`. -/
example (x : ZMod p) : untilt.spanPEquiv p 1 (ZMod p) (untilt.sharp p 1 _ x) = x :=
  untilt.spanPEquiv_sharp p 1 (ZMod p) x

/-- `p` does not lie in `(p ^ 2)` in `𝕎 𝔽_p`: otherwise `p` would be a unit, and its zeroth Witt
coordinate `0` would be a unit of `𝔽_p`. -/
theorem natCast_notMem_span_sq :
    (p : WittVector p (ZMod p)) ∉ span {(p : WittVector p (ZMod p)) ^ 2} := by
  intro h
  obtain ⟨c, hc⟩ := mem_span_singleton'.mp h
  -- `p (p c - 1) = 0` and `p` is a nonzerodivisor, so `p c = 1`.
  have h1 : (p : WittVector p (ZMod p)) * c = 1 := by
    have h0 : (c * p - 1) * (p : WittVector p (ZMod p)) = 0 := by
      linear_combination hc
    have := WittVector.eq_zero_of_p_mul_eq_zero _ h0
    linear_combination this
  have := congrArg (WittVector.coeff · 0) h1
  simp only [WittVector.mul_coeff_zero, WittVector.coeff_p_zero, zero_mul,
    WittVector.one_coeff_zero] at this
  exact zero_ne_one this

/-- **Non-example**: the untilt of `𝔽_p` along `(p ^ 2)` with respect to `ϖ = 1` is not reduced,
because `p` is a nonzero nilpotent element. -/
example : ¬ IsReduced (untilt p (1 : ZMod p) (span {(p : WittVector p (ZMod p)) ^ 2})) := by
  set J := span {(p : WittVector p (ZMod p)) ^ 2}
  have hinj : Function.Injective (algebraMap (WittVector p (ZMod p) ⧸ J) (untilt p 1 J)) :=
    IsLocalization.injective _ (M := Submonoid.powers (Ideal.Quotient.mk J (teichmuller p 1)))
      (Submonoid.powers_le.mpr (by rw [map_one, map_one]; exact one_mem _))
  intro hred
  have hp0 : (p : untilt p 1 J) = 0 := by
    refine hred.eq_zero _ ⟨2, ?_⟩
    rw [← map_natCast (algebraMap (WittVector p (ZMod p)) (untilt p 1 J)), ← map_pow]
    exact untilt.algebraMap_eq_zero_of_mem p 1 J (subset_span rfl)
  rw [← map_natCast (algebraMap (WittVector p (ZMod p)) (untilt p 1 J)), untilt.algebraMap_apply,
    ← map_zero (algebraMap (WittVector p (ZMod p) ⧸ J) (untilt p 1 J))] at hp0
  exact natCast_notMem_span_sq p (Ideal.Quotient.eq_zero_iff_mem.mp (hinj hp0))

/-! ### The general results -/

/-- The untilt is a Tate ring, and `ϖ♯` is a pseudouniformiser, for any `ϖ` and `J`. -/
example {S : Type*} [CommRing S] (ϖ : S) (J : Ideal (WittVector p S)) :
    IsTateRing (untilt p ϖ J) ∧ IsPseudoUniformizer (untilt.sharp p ϖ J ϖ) :=
  ⟨inferInstance, untilt.isPseudoUniformizer_sharp p ϖ J⟩

/-- **Compatibility**: over a perfect ring of characteristic `p` which is `ϖ`-adically complete for
a nonzerodivisor `ϖ`, the untilt along the distinguished element `p + [ϖ] α` is a complete
Hausdorff Tate ring, and `A⁺ ⧸ (ϖ♯) ≃+* S ⧸ (ϖ)`. -/
example {S : Type*} [CommRing S] [CharP S p] [PerfectRing S p] (ϖ : S) (hϖ : ϖ ∈ S⁰)
    [IsAdicComplete (span {ϖ}) S] (α : WittVector p S) :
    let ξ := (p : WittVector p S) + teichmuller p ϖ * α
    T2Space (untilt p ϖ (span {ξ})) ∧ CompleteSpace (untilt p ϖ (span {ξ})) ∧
      Nonempty (untiltPlus p ϖ (span {ξ}) ⧸
          span {(⟨untilt.sharp p ϖ _ ϖ, untilt.sharp_mem_untiltPlus p ϖ _ ϖ⟩ :
            untiltPlus p ϖ (span {ξ}))} ≃+* S ⧸ span {ϖ}) := by
  intro ξ
  have hξ : ξ.IsDistinguished :=
    WittVector.isDistinguished_p_add_teichmuller_mul_of_isAdicComplete (I := span {ϖ})
      (subset_span rfl) α
  have hξ₀ : ϖ ∣ ξ.coeff 0 :=
    ⟨α.coeff 0, by simp [ξ, WittVector.add_coeff_zero, WittVector.mul_coeff_zero,
      WittVector.coeff_p_zero, WittVector.teichmuller_coeff_zero]⟩
  have hξ₀' : ξ.coeff 0 ∈ (span {ϖ}).radical := le_radical (mem_span_singleton.mpr hξ₀)
  exact ⟨untilt.t2Space hξ hξ₀' hϖ, untilt.completeSpace hξ hξ₀' hϖ,
    ⟨untilt.quotEquiv hξ hξ₀ hϖ⟩⟩

end TauCeti.Examples.UntiltChecks
