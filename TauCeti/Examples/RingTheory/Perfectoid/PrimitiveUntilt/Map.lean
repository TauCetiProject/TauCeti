/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Examples.RingTheory.Perfectoid.PrimitiveUntilt.Basic
public import TauCeti.RingTheory.Perfectoid.PrimitiveUntilt.Map
public import TauCeti.RingTheory.Huber.Prod

/-!
# Checks for the sharp map, functoriality, quotients, and `(p)`-recovery of untilts

These checks exercise `TauCeti.RingTheory.Perfectoid.PrimitiveUntilt.Map` on:

* a zero characteristic-`p` base, where every untilt is zero and `sharp` vanishes identically;
* the perfectoid tilt `(ℂ_p♭, ℂ_p♭°)` and a mixed-characteristic primitive element `ξ = p - [ϖ]`,
  checking `sharp (ϖ ^ 2) = p ^ 2`, non-additivity of `sharp` for `p = 2` (`sharp (ϖ + ϖ) = 0`
  while `sharp ϖ + sharp ϖ = 4 ≠ 0`), and the quotient identification `A⁺ ⧸ (sharp ϖ) ≃+* R⁺ ⧸ (ϖ)`;
* functoriality `untilt.map` for enlarging `(p)` to `⊤`, enlarging `(p ^ 2)` to `(p)`
  (non-injective: the nonzero class of `p` is sent to `0`), and the first projection on the
  non-domain product `ℂ_p♭ × ℂ_p♭` (sending `sharp (1, 0) ↦ 1` and `sharp (0, 1) ↦ 0`);
* characteristic-`p` recovery `spanPEquivSelf : untilt p (ℂ_p♭, ℂ_p♭°) (p) ≃+* ℂ_p♭` and its
  homeomorphism property.
-/

public section

open Filter Ideal Topology TauCeti.Examples.PrimitiveUntilt TauCeti.Huber TauCeti.Perfectoid
open WittVector (teichmuller)

namespace TauCeti.Examples.PrimitiveUntiltMap

variable (p : ℕ) [hp : Fact p.Prime]

/-! ### Zero characteristic-`p` base -/

-- Over a zero characteristic-`p` base, every untilt is zero and `sharp` sends everything to `0`.
example {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [IsTateRing R]
    [Subsingleton R] (P : Pair R) (J : Ideal (WittVector p P.plus)) (x : R) :
    Subsingleton (untilt p P J) ∧ untilt.sharp p P J x = 0 := by
  have : Subsingleton (WittVector p P.plus) := ⟨fun a b ↦ WittVector.ext fun n ↦
    Subsingleton.elim _ _⟩
  have : Subsingleton (untilt p P J) :=
    (algebraMap (WittVector p P.plus ⧸ J) (untilt p P J)).codomain_trivial
  exact ⟨inferInstance, Subsingleton.elim _ _⟩

/-! ### Computations on `sharp` along `ξ = p - [ϖ]` -/

-- Along `ξ = p - [ϖ]`, `sharp ϖ = p` and `sharp (ϖ ^ 2) = p ^ 2`.
example :
    untilt.sharp p (pair p) (span {xi p}) (varpi p : uniformTilt p ℂ_[p]) = p ∧
    untilt.sharp p (pair p) (span {xi p}) ((varpi p : uniformTilt p ℂ_[p]) ^ 2) = p ^ 2 :=
  ⟨sharp_varpi p, by rw [map_pow, sharp_varpi p]⟩

-- Non-additivity of `sharp`: for `p = 2` and `ξ = 2 - [ϖ]`, `sharp (ϖ + ϖ) = 0`, whereas
-- `sharp ϖ + sharp ϖ = 4 ≠ 0`.
example :
    untilt.sharp 2 (pair 2) (span {xi 2})
        ((varpi 2 : uniformTilt 2 ℂ_[2]) + (varpi 2 : uniformTilt 2 ℂ_[2])) = 0 ∧
      untilt.sharp 2 (pair 2) (span {xi 2}) (varpi 2 : uniformTilt 2 ℂ_[2]) +
        untilt.sharp 2 (pair 2) (span {xi 2}) (varpi 2 : uniformTilt 2 ℂ_[2]) ≠ 0 := by
  have : Nontrivial (untilt 2 (pair 2) (span {xi 2})) := nontrivial_untilt_xi 2
  have hadd : (varpi 2 : uniformTilt 2 ℂ_[2]) + (varpi 2 : uniformTilt 2 ℂ_[2]) = 0 := by
    have h2 : (2 : uniformTilt 2 ℂ_[2]) = 0 := by
      simpa using CharP.cast_eq_zero (uniformTilt 2 ℂ_[2]) 2
    rw [← two_mul, h2, zero_mul]
  have hsp : untilt.sharp 2 (pair 2) (span {xi 2}) (varpi 2 : uniformTilt 2 ℂ_[2]) = 2 := by
    simpa using sharp_varpi 2
  have hu2 : IsUnit (2 : untilt 2 (pair 2) (span {xi 2})) := by
    rw [← hsp]
    exact (untilt.isPseudoUniformizer_sharp (isPseudoUniformizer_varpi 2)).isUnit
  refine ⟨by rw [hadd, map_zero], ?_⟩
  rw [hsp, ← two_mul]
  exact (hu2.mul hu2).ne_zero

-- `quotientSharpEquiv` identifies `A⁺ ⧸ (sharp ϖ)` with `ℂ_p♭° ⧸ (ϖ)` along `ξ = p - [ϖ]`.
example (a : (pair p).plus) :
    have hξ₀ : varpi p ∣ (xi p).coeff 0 := ⟨-1, by rw [coeff_zero_xi p, mul_neg_one]⟩
    untilt.quotientSharpEquiv (isPrimitive_xi p) hξ₀
      (Ideal.Quotient.mk _ ⟨untilt.sharp p (pair p) (span {xi p}) a,
        untilt.sharp_mem_untiltPlus a⟩) =
      Ideal.Quotient.mk (span {varpi p}) a := by
  exact untilt.quotientSharpEquiv_mk_sharp (isPrimitive_xi p) _ a

/-! ### Functoriality `untilt.map` -/

-- Enlarging `(p)` to `⊤` kills the nonzero unit `sharp 1 = 1`.
example :
    let f := untilt.map (p := p) (P := pair p) (Q := pair p)
      (J := span {(p : WittVector p (pair p).plus)}) (J' := ⊤)
      (RingHom.id _) (fun _ hx ↦ hx) (fun _ _ ↦ Submodule.mem_top)
    untilt.sharp p (pair p) (span {(p : WittVector p (pair p).plus)}) 1 ≠ 0 ∧
      f (untilt.sharp p (pair p) (span {(p : WittVector p (pair p).plus)}) 1) = 0 := by
  have : Subsingleton (untilt p (pair p) ⊤) :=
    IsLocalization.subsingleton
      (M := (untiltDenominators p (pair p)).map (Ideal.Quotient.mk ⊤))
      ⟨1, one_mem _, Ideal.Quotient.eq_zero_iff_mem.mpr Submodule.mem_top⟩
  have : Nontrivial (untilt p (pair p) (span {(p : WittVector p (pair p).plus)})) :=
    (untilt.spanPEquivSelf p (pair p)).toRingHom.domain_nontrivial
  refine ⟨by rw [map_one]; exact one_ne_zero, Subsingleton.elim _ _⟩

-- Enlarging the ideal from `(p ^ 2)` to `(p)` gives a non-injective map killing the nonzero
-- class of `p`.
example :
    let J₂ : Ideal (WittVector p (pair p).plus) := span {(p : WittVector p (pair p).plus) ^ 2}
    let J₁ : Ideal (WittVector p (pair p).plus) := span {(p : WittVector p (pair p).plus)}
    let f := untilt.map (p := p) (P := pair p) (Q := pair p) (J := J₂) (J' := J₁)
      (RingHom.id _) (fun _ hx ↦ hx) (fun w hw ↦ by
        rw [Ideal.mem_comap]
        have hid : WittVector.map (p := p) ((RingHom.id _).restrict (pair p).plus (pair p).plus
            fun _ hx ↦ hx) = RingHom.id _ := by
          ext n; simp
        rw [hid, RingHom.id_apply]
        obtain ⟨c, rfl⟩ := mem_span_singleton.mp hw
        exact mem_span_singleton.mpr ⟨p * c, by ring⟩)
    (p : untilt p (pair p) J₂) ≠ 0 ∧ f (p : untilt p (pair p) J₂) = 0 := by
  intro J₂ J₁ f
  refine ⟨fun hp0 ↦ ?_, ?_⟩
  · have hEq : algebraMap (WittVector p (pair p).plus ⧸ J₂) (untilt p (pair p) J₂)
        (Ideal.Quotient.mk J₂ (p : WittVector p (pair p).plus)) =
        algebraMap (WittVector p (pair p).plus ⧸ J₂) (untilt p (pair p) J₂) 0 := by
      simpa using hp0
    obtain ⟨⟨s, hs⟩, hs0⟩ := (IsLocalization.eq_iff_exists
      ((untiltDenominators p (pair p)).map (Ideal.Quotient.mk J₂))
      (untilt p (pair p) J₂)).mp hEq
    obtain ⟨d, hd, rfl⟩ := hs
    obtain ⟨a, ha, rfl⟩ := mem_untiltDenominators.mp hd
    rw [mul_zero, ← map_mul, Ideal.Quotient.eq_zero_iff_mem] at hs0
    obtain ⟨c, hc⟩ := mem_span_singleton.mp hs0
    have hcoeff := congrArg (WittVector.coeff · 1) hc
    have hlhs : (teichmuller p a * (p : WittVector p (pair p).plus)).coeff 1 = a ^ p := by
      rw [WittVector.mul_charP_coeff_succ, WittVector.teichmuller_coeff_zero]
    have hrhs : (((p : WittVector p (pair p).plus) ^ 2) * c).coeff 1 = 0 := by
      rw [sq, mul_comm ((p : WittVector p (pair p).plus) * p) c, ← mul_assoc,
        WittVector.mul_charP_coeff_succ, WittVector.mul_charP_coeff_zero,
        zero_pow hp.out.ne_zero]
    rw [hlhs, hrhs] at hcoeff
    have ha0 : (a : uniformTilt p ℂ_[p]) ^ p = 0 := congrArg Subtype.val hcoeff
    exact (ha.pow p).ne_zero ha0
  · rw [map_natCast]
    have hzero : (p : untilt p (pair p) J₁) =
        algebraMap (WittVector p (pair p).plus ⧸ J₁) (untilt p (pair p) J₁)
          (Ideal.Quotient.mk J₁ (p : WittVector p (pair p).plus)) := by
      simp
    rw [hzero, Ideal.Quotient.eq_zero_iff_mem.mpr (mem_span_singleton_self _), map_zero]

-- On the non-domain product `ℂ_p♭ × ℂ_p♭`, `untilt.map` along the first projection sends
-- `sharp (1, 0) ↦ 1` and `sharp (0, 1) ↦ 0`.
example :
    let Q := Pair.powerBounded (uniformTilt p ℂ_[p] × uniformTilt p ℂ_[p])
    let hfplus : ∀ x ∈ Q.plus, RingHom.fst _ _ x ∈ (pair p).plus := fun x hx ↦ by
      rw [Pair.powerBounded_plus, mem_powerBoundedSubring]
      exact (Q.isRingOfIntegralElements.isPowerBounded_of_mem hx).map_of_isOpenMap
        continuous_fst.continuousAt isOpenMap_fst
    let f := untilt.map (p := p) (P := Q) (Q := pair p)
      (J := span {(p : WittVector p Q.plus)}) (J' := span {(p : WittVector p (pair p).plus)})
      (RingHom.fst _ _) hfplus (fun w hw ↦ by
        rw [Ideal.mem_comap]
        obtain ⟨c, rfl⟩ := mem_span_singleton.mp hw
        rw [map_mul, map_natCast]
        exact Ideal.mul_mem_right _ _ (mem_span_singleton_self _))
    f (untilt.sharp p Q (span {(p : WittVector p Q.plus)}) (1, 0)) = 1 ∧
      f (untilt.sharp p Q (span {(p : WittVector p Q.plus)}) (0, 1)) = 0 := by
  intro Q hfplus f
  exact ⟨by rw [untilt.map_sharp]; simp, by rw [untilt.map_sharp]; simp⟩

/-! ### Recovery along `(p)` -/

-- `spanPEquivSelf` recovers `ℂ_p♭` as a topological ring from its untilt along `(p)`.
example (x : uniformTilt p ℂ_[p]) :
    untilt.spanPEquivSelf p (pair p)
        (untilt.sharp p (pair p) (span {(p : WittVector p (pair p).plus)}) x) = x ∧
      IsHomeomorph (untilt.spanPEquivSelf p (pair p)) :=
  ⟨untilt.spanPEquivSelf_sharp p (pair p) x, untilt.isHomeomorph_spanPEquivSelf p (pair p)⟩

end TauCeti.Examples.PrimitiveUntiltMap
