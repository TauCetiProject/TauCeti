/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Dagger.Distinguished
public import TauCeti.RingTheory.PowerSeries.Weierstrass.Preparation

/-!
# Weierstrass division and preparation for overconvergent series in one variable

A series in `R⟨X⟩†` distinguished of degree `s` at the unit radius stays distinguished of that
same degree at some radius strictly greater than one. Division and preparation at that radius
therefore produce overconvergent quotients and units. Their uniqueness follows at unit radius.

Division and preparation hold over any complete ultrametric normed commutative ring, provided
the divisor is multiplicatively distinguished: its distinguished coefficient is a
norm-multiplicative unit. The norm on the coefficient ring need not be multiplicative.

The algebra is `washnitzerAlgebra Unit R`, whose underlying formal series are `PowerSeries R`.
No completeness of this algebra is asserted: completeness is used only for the coefficient
ring when applying `TauCeti.PowerSeries.IsMulDistinguished.exists_mul_add_eq` and its
preparation theorem.

## References

* E. Grosse-Klönne, *Rigid analytic spaces with overconvergent structure sheaf*,
  J. reine angew. Math. 519 (2000), §1.3(i)–(ii).
* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §§5.2.1–5.2.2.
-/

public section

namespace TauCeti.Dagger

open TauCeti.PowerSeries

section Ring

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]

/-- Weierstrass division in `R⟨X⟩†`: a divisor multiplicatively distinguished of degree `s` at
radius one gives a unique overconvergent quotient and a remainder with every coefficient in
degree `≥ s` zero. -/
theorem existsUnique_mul_add_eq_of_isMulDistinguished_one
    {f : washnitzerAlgebra Unit R} {s : ℕ}
    (hf : IsMulDistinguished 1 s (f : PowerSeries R)) (g : washnitzerAlgebra Unit R) :
    ∃! p : washnitzerAlgebra Unit R × washnitzerAlgebra Unit R,
      (∀ m, s ≤ m → PowerSeries.coeff m (p.2 : PowerSeries R) = 0) ∧ p.1 * f + p.2 = g := by
  obtain ⟨ρ₀, hρ₀, hgρ₀⟩ := mem_washnitzerAlgebra.mp g.2
  obtain ⟨ρ, hρ, hρρ₀, hfr, hfd⟩ :=
    exists_isDistinguished_of_isDistinguished_one hf.toIsDistinguished hρ₀
  have hgr : PowerSeries.IsRestricted ρ (g : PowerSeries R) :=
    MvPowerSeries.isRestricted_of_le hgρ₀ (fun _ ↦ zero_le_one.trans hρ.le) fun _ ↦ hρρ₀
  obtain ⟨q, r, hq, hr, hqr⟩ :=
    (IsMulDistinguished.mk hfd hf.isNormMulUnit_coeff).exists_mul_add_eq
      (zero_lt_one.trans hρ) hfr hgr
  rw [mul_comm] at hqr
  let Q : washnitzerAlgebra Unit R := ⟨q, mem_washnitzerAlgebra.mpr ⟨ρ, hρ, hq⟩⟩
  let rW : washnitzerAlgebra Unit R :=
    ⟨r, mem_washnitzerAlgebra.mpr ⟨2, one_lt_two, isRestricted_of_forall_coeff_eq_zero hr⟩⟩
  refine ⟨(Q, rW), ⟨hr, Subtype.ext hqr⟩, fun p ⟨hp, heq⟩ ↦ ?_⟩
  obtain ⟨heqQ, heqR⟩ := hf.toIsDistinguished.eq_and_eq_of_mul_add_eq_mul_add one_pos
    hf.norm_mul_coeff
    (isRestricted_of_mem_washnitzerAlgebra p.1.2 zero_le_one le_rfl)
    (isRestricted_of_mem_washnitzerAlgebra Q.2 zero_le_one le_rfl) hp hr
    ((congrArg (fun a : washnitzerAlgebra Unit R ↦ (a : PowerSeries R)) heq).trans hqr.symm)
  exact Prod.ext (Subtype.ext heqQ) (Subtype.ext heqR)

/-- Weierstrass preparation in `R⟨X⟩†`: a series multiplicatively distinguished of degree `s` at
radius one has a unique factorisation as an overconvergent unit times a monic polynomial of
degree `s`. -/
theorem existsUnique_isUnit_isMonicOfDegree_mul_eq_of_isMulDistinguished_one
    {f : washnitzerAlgebra Unit R} {s : ℕ}
    (hf : IsMulDistinguished 1 s (f : PowerSeries R)) :
    ∃! p : washnitzerAlgebra Unit R × Polynomial R,
      IsUnit p.1 ∧ p.2.IsMonicOfDegree s ∧
        p.1 * washnitzerAlgebra.ofPolynomial R p.2 = f := by
  obtain ⟨ρ, hρ, _, hfr, hfd⟩ :=
    exists_isDistinguished_of_isDistinguished_one hf.toIsDistinguished one_lt_two
  have : Fact (0 < ρ) := ⟨zero_lt_one.trans hρ⟩
  have hfm : IsMulDistinguished ρ s (f : PowerSeries R) := ⟨hfd, hf.isNormMulUnit_coeff⟩
  obtain ⟨e, ω, he, hω, _, heω⟩ := hfm.exists_isNormMulUnit_isMonicOfDegree_mul_eq hfr
  let ι : PowerSeries.IsRestricted.subring (R := R) ρ →+* washnitzerAlgebra Unit R :=
    (PowerSeries.IsRestricted.subring (R := R) ρ).subtype.codRestrict _
      fun a ↦ mem_washnitzerAlgebra.mpr ⟨ρ, hρ, a.2⟩
  have heω' : ((ι e : washnitzerAlgebra Unit R) : PowerSeries R) * ω = f := by
    simpa [ι, RingHom.codRestrict_apply] using heω
  refine ⟨(ι e, ω), ⟨he.isUnit.map ι, hω, Subtype.ext (by simpa using heω')⟩,
    fun p ⟨hp, hm, heq⟩ ↦ ?_⟩
  obtain ⟨hu, hpoly⟩ := hf.eq_and_eq_of_mul_eq_of_mul_eq one_pos
    (hp.map (washnitzerAlgebra.toTate Unit R))
    ((he.isUnit.map ι).map (washnitzerAlgebra.toTate Unit R)) hm hω
    (by simpa using congrArg (fun a : washnitzerAlgebra Unit R ↦ (a : PowerSeries R)) heq)
    (by rw [washnitzerAlgebra.coe_toTate]; exact heω')
  exact Prod.ext (washnitzerAlgebra.toTate_injective hu) hpoly

end Ring

end TauCeti.Dagger
