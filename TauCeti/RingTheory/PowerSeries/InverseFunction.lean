/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.Evaluation
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
import TauCeti.RingTheory.PowerSeries.Rescale
import TauCeti.RingTheory.MvPowerSeries.Substitution

/-!
# The inverse function theorem for integral power series

Let `f = a X + ⋯` be an integral power series without constant term. On an adic ideal,
a unit linear coefficient makes evaluation bijective. More generally, if `a` divides `c`
and `a c` is regular, evaluation maps `c I` bijectively onto `a c I`.
Indeed, `f(c X) = a c g(X)` with `g = X + ⋯`, and the compositional inverse of `g`
converges on `I`.

Over a complete discrete valuation ring with maximal ideal `𝔪`, if `(a) = 𝔪 ^ e`,
this gives a bijection `𝔪 ^ k → 𝔪 ^ (k + e)` for every `k > e`. It computes the
exact image, not merely the valuation of each value. Applied to a formal-group
homomorphism, this is the small-neighbourhood input to its local kernel/cokernel index.

## References

* J. Silverman, *The Arithmetic of Elliptic Curves*, IV.3 and IV.6.
* E. F. Schaefer, *Class groups and Selmer groups*, J. Number Theory 56 (1996), Lemma 3.8.
-/

public section

namespace PowerSeries

variable {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R]
  [CompleteSpace R] [T2Space R] [IsTopologicalRing R] [IsLinearTopology R R]
  {I : Ideal R} [Fact (IsAdic I)] {f : R⟦X⟧}

/-- Evaluation of a power series with zero constant term and unit linear coefficient is a
bijection of every adic ideal onto itself. -/
theorem bijOn_eval₂_of_isUnit (hf : constantCoeff f = 0) (ha : IsUnit (coeff 1 f)) :
    Set.BijOn (fun x ↦ eval₂ (RingHom.id R) x f) (I : Set R) I := by
  let g := f.substInvOfIsUnit ha
  have hg : constantCoeff g = 0 := constantCoeff_substInvOfIsUnit _ _
  have hI : IsAdic I := Fact.out
  have hmem {x : R} (hx : x ∈ I) {p : R⟦X⟧} (hp : constantCoeff p = 0) :
      eval₂ (RingHom.id R) x p ∈ I := by
    simpa only [coe_aeval, Algebra.algebraMap_self] using
      aeval_mem_of_constantCoeff_eq_zero (hI.isTopologicallyNilpotent_of_mem hx) hp hx
  have hinv {x : R} (hx : x ∈ I) {p q : R⟦X⟧} (hp : constantCoeff p = 0)
      (hpq : subst p q = X) :
      eval₂ (RingHom.id R) (eval₂ (RingHom.id R) x p) q = x := by
    have h := congrArg (aeval (R := R) (hI.isTopologicallyNilpotent_of_mem hx)) hpq
    rw [aeval_subst (HasSubst.of_constantCoeff_zero hp) (continuous_aeval _)
      (isTopologicallyNilpotent_aeval_of_constantCoeff_eq_zero
        (hI.isTopologicallyNilpotent_of_mem hx) hp), aeval_X] at h
    simpa only [coe_aeval, Algebra.algebraMap_self] using h
  refine ⟨fun x hx ↦ hmem hx hf, ?_, ?_⟩
  · intro x hx y hy hxy
    dsimp only at hxy
    have hx' := hinv hx hf (subst_substInvOfIsUnit_left f hf ha)
    have hy' := hinv hy hf (subst_substInvOfIsUnit_left f hf ha)
    rw [hxy] at hx'
    exact hx'.symm.trans hy'
  · intro y hy
    exact ⟨eval₂ (RingHom.id R) y g, hmem hy hg,
      hinv hy hg (subst_substInvOfIsUnit_right f hf ha)⟩

/-- If the linear coefficient `a` of `f` divides `c`, evaluation carries `c I` bijectively
onto `a c I`, provided `a c` is regular. This permits nonunit linear coefficients. -/
theorem bijOn_eval₂_span_singleton_mul (hf : constantCoeff f = 0)
    {c : R} (hc : coeff 1 f ∣ c) (hac : IsRegular (coeff 1 f * c)) :
    Set.BijOn (fun x ↦ eval₂ (RingHom.id R) x f)
      (↑(Ideal.span {c} * I) : Set R) (↑(Ideal.span {coeff 1 f * c} * I) : Set R) := by
  obtain ⟨g, hg0, hg1, hfg⟩ := exists_rescale_eq_C_mul hf hc
  have hg := bijOn_eval₂_of_isUnit (I := I) hg0 (hg1 ▸ isUnit_one)
  have heval {s : R} (hs : s ∈ I) :
      eval₂ (RingHom.id R) (c * s) f =
        (coeff 1 f * c) * eval₂ (RingHom.id R) s g := by
    have hI : IsAdic I := Fact.out
    have hcs := hI.isTopologicallyNilpotent_of_mem (I.mul_mem_left c hs)
    have h := aeval_rescale (hI.isTopologicallyNilpotent_of_mem hs) c hcs f
    rw [hfg, map_mul, aeval_C] at h
    simpa only [coe_aeval, Algebra.algebraMap_self, smul_eq_mul, RingHom.id_apply] using h.symm
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨s, hs, rfl⟩ := Ideal.mem_span_singleton_mul.mp hx
    dsimp only
    rw [heval hs]
    exact Ideal.mem_span_singleton_mul.mpr ⟨_, hg.mapsTo hs, rfl⟩
  · intro x hx y hy hxy
    obtain ⟨s, hs, rfl⟩ := Ideal.mem_span_singleton_mul.mp hx
    obtain ⟨t, ht, rfl⟩ := Ideal.mem_span_singleton_mul.mp hy
    dsimp only at hxy
    rw [heval hs, heval ht] at hxy
    rw [hg.injOn hs ht (hac.left hxy)]
  · intro y hy
    obtain ⟨t, ht, rfl⟩ := Ideal.mem_span_singleton_mul.mp hy
    obtain ⟨s, hs, hst⟩ := hg.surjOn ht
    exact ⟨c * s, Ideal.mem_span_singleton_mul.mpr ⟨s, hs, rfl⟩,
      by simpa only [heval hs] using congrArg (fun z ↦ (coeff 1 f * c) * z) hst⟩

section DiscreteValuationRing

variable [IsDomain R] [IsDiscreteValuationRing R]
  [Fact (IsAdic (IsLocalRing.maximalIdeal R))]

/-- Over a complete discrete valuation ring, a series with zero constant term and linear
coefficient of valuation `e` maps `𝔪 ^ k` bijectively onto `𝔪 ^ (k + e)` when `e < k`. -/
theorem bijOn_eval₂_maximalIdeal_pow (hf : constantCoeff f = 0) {e k : ℕ}
    (ha : Ideal.span {coeff 1 f} = IsLocalRing.maximalIdeal R ^ e) (hek : e < k) :
    Set.BijOn (fun x ↦ eval₂ (RingHom.id R) x f)
      (↑(IsLocalRing.maximalIdeal R ^ k) : Set R)
      (↑(IsLocalRing.maximalIdeal R ^ (k + e)) : Set R) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hpow (j : ℕ) : IsLocalRing.maximalIdeal R ^ j = Ideal.span {ϖ ^ j} := by
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
  have hac : coeff 1 f ∣ ϖ ^ (k - 1) := by
    rw [← Ideal.span_singleton_le_span_singleton, ha, hpow]
    exact Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow ϖ (by omega))
  have hk : IsLocalRing.maximalIdeal R ^ k =
      Ideal.span {ϖ ^ (k - 1)} * IsLocalRing.maximalIdeal R := by
    rw [← hpow, ← pow_succ, Nat.sub_add_cancel (by omega)]
  have hke : IsLocalRing.maximalIdeal R ^ (k + e) =
      Ideal.span {coeff 1 f * ϖ ^ (k - 1)} * IsLocalRing.maximalIdeal R := by
    rw [← Ideal.span_singleton_mul_span_singleton, ha, ← hpow, mul_assoc, ← pow_succ,
      ← pow_add]
    congr 1
    omega
  have hne : coeff 1 f * ϖ ^ (k - 1) ≠ 0 := by
    intro h
    rw [h, Ideal.span_singleton_eq_bot.mpr rfl, Ideal.bot_mul] at hke
    exact pow_ne_zero _
      (IsDiscreteValuationRing.not_a_field R) hke
  rw [hk, hke]
  exact bijOn_eval₂_span_singleton_mul hf hac (.of_ne_zero hne)

end DiscreteValuationRing

end PowerSeries
