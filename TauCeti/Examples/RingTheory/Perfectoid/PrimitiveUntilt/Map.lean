/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Subring
public import TauCeti.RingTheory.Perfectoid.PrimitiveUntilt.Map
public import TauCeti.RingTheory.Perfectoid.UniformTilt.Gauge
public import TauCeti.RingTheory.Perfectoid.Padic
public import TauCeti.RingTheory.Huber.Pair.Complete
public import TauCeti.RingTheory.Huber.Perfect
public import TauCeti.RingTheory.Huber.Prod
public import TauCeti.NumberTheory.Padics.Complex.Basic

/-!
# Checks for the sharp map, functoriality, quotients, and `(p)`-recovery of untilts

These checks exercise `TauCeti.RingTheory.Perfectoid.PrimitiveUntilt.Map` on:

* a zero characteristic-`p` base, where every untilt is zero and `sharp` vanishes identically;
* the perfectoid tilt `(ℂ_p♭, ℂ_p♭°)` and a mixed-characteristic primitive element `ξ = p - [ϖ]`,
  checking `sharp (ϖ ^ 2) = p ^ 2`, non-additivity of `sharp` for `p = 2` (`sharp (ϖ + ϖ) = 0`
  while `sharp ϖ + sharp ϖ = 4 ≠ 0`), and the quotient identification `A⁺ ⧸ (sharp ϖ) ≃+* R⁺ ⧸ (ϖ)`;
* functoriality `untilt.map` for enlarging `(p)` to `⊤`, reducing `(p ^ 2)` to `(p)` (non-injective:
  the nonzero class of `p` is sent to `0`), and the first projection on the non-domain product
  `ℂ_p♭ × ℂ_p♭` (sending `sharp (1, 0) ↦ 1` and `sharp (0, 1) ↦ 0`);
* characteristic-`p` recovery `pRecovery : untilt p (ℂ_p♭, ℂ_p♭°) (p) ≃+* ℂ_p♭` and its
  homeomorphism property.
-/

public section

open Filter Ideal Topology TauCeti.Huber TauCeti.Perfectoid
open WittVector (teichmuller)

namespace TauCeti.Examples.PrimitiveUntiltMap

variable (p : ℕ) [hp : Fact p.Prime]

local instance : Fact (IsTopologicallyNilpotent (p : ℂ_[p])) :=
  ⟨tendsto_pow_atTop_nhds_zero_of_norm_lt_one (PadicComplex.norm_p_lt_one p)⟩

private noncomputable def parameter : PseudoUniformizerRoots p ℂ_[p] :=
  Classical.choice (nonempty_pseudoUniformizerRoots_of_isAlgClosed (PadicComplex.norm_p_lt_one p))

local instance : IsTateRing (uniformTilt p ℂ_[p]) :=
  uniformTilt.isTateRing_of_sharp (ϖ := (parameter p).toTilt)
    (by simpa using (parameter p).isPseudoUniformizer_root_zero)

local instance : IsUniform (uniformTilt p ℂ_[p]) := IsUniform.of_perfectRing p

private noncomputable abbrev pair : Pair (uniformTilt p ℂ_[p]) := Pair.powerBounded _

/-- The integral pseudouniformiser `ϖ = (parameter p).toTilt ∈ ℂ_p♭°`. -/
private noncomputable def varpi : (pair p).plus :=
  ⟨(parameter p).toTilt, by
    rw [Pair.powerBounded_plus, mem_powerBoundedSubring]
    exact IsPowerBounded.of_isTopologicallyNilpotent <|
      (uniformTilt.isTopologicallyNilpotent_iff_coeff_zero (p := p) (B := ℂ_[p])
        (x := (parameter p).toTilt)).mpr <| by
        simpa using (parameter p).isPseudoUniformizer_root_zero.isTopologicallyNilpotent⟩

private theorem isPseudoUniformizer_varpi :
    IsPseudoUniformizer (varpi p : uniformTilt p ℂ_[p]) := by
  rw [isPseudoUniformizer_iff, uniformTilt.isUnit_iff_coeff_zero,
    uniformTilt.isTopologicallyNilpotent_iff_coeff_zero]
  exact isPseudoUniformizer_iff.mp (by simpa [varpi] using
    (parameter p).isPseudoUniformizer_root_zero)

/-- The mixed-characteristic primitive element `ξ = p - [ϖ] ∈ 𝕎(ℂ_p♭°)`. -/
private noncomputable def xi : WittVector p (pair p).plus :=
  (p : WittVector p (pair p).plus) - teichmuller p (varpi p)

private theorem isPrimitive_xi : (xi p).IsPrimitive := by
  have hϖ := isPseudoUniformizer_varpi p
  have hAdic : IsAdic (span {varpi p}) :=
    (pair p).plus.isAdic_span_singleton_of_isOpen_of_isBounded
      (pair p).isRingOfIntegralElements.isOpen (pair p).isRingOfIntegralElements.isBounded
      hϖ (varpi p).property
  have := (pair p).isRingOfIntegralElements.isAdicComplete_span_singleton (varpi p) hϖ
  have hξ : xi p = (p : WittVector p (pair p).plus) + teichmuller p (varpi p) * (-1) := by
    simp [xi, sub_eq_add_neg]
  rw [hξ]
  exact WittVector.isPrimitive_p_add_teichmuller_mul_of_isAdic hAdic
    (mem_span_singleton_self (varpi p)) (-1)

private theorem nontrivial_untilt_xi :
    Nontrivial (untilt p (pair p) (span {xi p})) := by
  rw [nontrivial_iff]
  refine ⟨1, 0, fun h10 ↦ ?_⟩
  have hq : (1 : WittVector p (pair p).plus ⧸ span {xi p}) = 0 :=
    untilt.algebraMap_injective (isPrimitive_xi p) (by simpa using h10)
  have hmem : (1 : WittVector p (pair p).plus) ∈ span {xi p} := by
    rwa [← Ideal.Quotient.eq_zero_iff_mem, map_one]
  obtain ⟨c, hc⟩ := mem_span_singleton.mp hmem
  have h0 := congrArg (WittVector.constantCoeff (p := p) (R := (pair p).plus)) hc
  simp only [map_one, map_mul, WittVector.constantCoeff_apply, xi,
    WittVector.sub_coeff_zero, WittVector.coeff_p_zero, WittVector.teichmuller_coeff_zero,
    zero_sub] at h0
  have hmul : ((-(c.coeff 0) : (pair p).plus) : uniformTilt p ℂ_[p]) *
      (varpi p : uniformTilt p ℂ_[p]) = 1 := by
    have hsub := congrArg Subtype.val h0
    simp only [OneMemClass.coe_one, Subring.coe_mul, Subring.coe_neg] at hsub
    rw [Subring.coe_neg]
    linear_combination -hsub
  have hnil : IsTopologicallyNilpotent (1 : uniformTilt p ℂ_[p]) := by
    rw [← hmul]
    exact ((pair p).isRingOfIntegralElements.isPowerBounded_of_mem
      (-(c.coeff 0)).property).isTopologicallyNilpotent_mul
      (isPseudoUniformizer_varpi p).isTopologicallyNilpotent
  obtain ⟨n, hn⟩ := hnil.exists_pow_mem_of_mem_nhds (isOpen_ne.mem_nhds zero_ne_one)
  exact hn (one_pow n)

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
    untilt.sharp p (pair p) (span {xi p}) ((varpi p : uniformTilt p ℂ_[p]) ^ 2) = p ^ 2 := by
  have hsp : untilt.sharp p (pair p) (span {xi p}) (varpi p : uniformTilt p ℂ_[p]) = p := by
    rw [untilt.sharp_apply]
    have hmk : Ideal.Quotient.mk (span {xi p}) (teichmuller p (varpi p)) =
        Ideal.Quotient.mk (span {xi p}) (p : WittVector p (pair p).plus) := by
      rw [Ideal.Quotient.eq]
      have hneg : teichmuller p (varpi p) - (p : WittVector p (pair p).plus) = -(xi p) := by
        simp [xi]
      rw [hneg]
      exact Submodule.neg_mem _ (mem_span_singleton_self _)
    rw [hmk, map_natCast, map_natCast]
  exact ⟨hsp, by rw [map_pow, hsp]⟩

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
    rw [untilt.sharp_apply]
    have hmk : Ideal.Quotient.mk (span {xi 2}) (teichmuller 2 (varpi 2)) =
        Ideal.Quotient.mk (span {xi 2}) (2 : WittVector 2 (pair 2).plus) := by
      rw [Ideal.Quotient.eq]
      have hneg : teichmuller 2 (varpi 2) - (2 : WittVector 2 (pair 2).plus) = -(xi 2) := by
        simp [xi]
      rw [hneg]
      exact Submodule.neg_mem _ (mem_span_singleton_self _)
    rw [hmk, map_ofNat, map_ofNat]
  have hu2 : IsUnit (2 : untilt 2 (pair 2) (span {xi 2})) := by
    rw [← hsp]
    exact (untilt.isPseudoUniformizer_sharp (isPseudoUniformizer_varpi 2)).isUnit
  refine ⟨by rw [hadd, map_zero], ?_⟩
  rw [hsp, show (2 : untilt 2 (pair 2) (span {xi 2})) + 2 = 2 * 2 by ring]
  exact (hu2.mul hu2).ne_zero

-- `quotientSharpEquiv` identifies `A⁺ ⧸ (sharp ϖ)` with `ℂ_p♭° ⧸ (ϖ)` along `ξ = p - [ϖ]`.
example (a : (pair p).plus) :
    have hξ₀ : varpi p ∣ (xi p).coeff 0 := by
      refine ⟨-1, ?_⟩
      simp [xi, WittVector.sub_coeff_zero, WittVector.coeff_p_zero]
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
    (untilt.pRecovery p (pair p)).toRingHom.domain_nontrivial
  refine ⟨by rw [map_one]; exact one_ne_zero, Subsingleton.elim _ _⟩

-- Decreasing the ideal from `(p)` to `(p ^ 2)` gives a non-injective map killing the nonzero
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
      rw [sq, show (p : WittVector p (pair p).plus) * p * c = (c * p) * p by ring,
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
      exact (Q.isRingOfIntegralElements.isPowerBounded_of_mem hx).map continuous_fst.continuousAt
        fun _ hV ↦ isOpenMap_fst.image_mem_nhds hV
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

-- `pRecovery` recovers `ℂ_p♭` as a topological ring from its untilt along `(p)`.
example (x : uniformTilt p ℂ_[p]) :
    untilt.pRecovery p (pair p)
        (untilt.sharp p (pair p) (span {(p : WittVector p (pair p).plus)}) x) = x ∧
      IsHomeomorph (untilt.pRecovery p (pair p)) :=
  ⟨untilt.pRecovery_sharp p (pair p) x, untilt.isHomeomorph_pRecovery p (pair p)⟩

end TauCeti.Examples.PrimitiveUntiltMap
