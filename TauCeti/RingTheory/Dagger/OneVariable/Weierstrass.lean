/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Dagger.Distinguished
public import TauCeti.RingTheory.PowerSeries.Weierstrass.Preparation
public import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Weierstrass division and preparation for overconvergent series in one variable

A series in `K⟨X⟩†` distinguished of degree `s` at the unit radius stays distinguished of that
same degree at some radius strictly greater than one. Division and preparation at that radius
therefore produce overconvergent quotients and units. Their uniqueness follows at unit radius.
In particular, every nonzero overconvergent series in one variable is a unit times a monic
polynomial. Every ideal is principal, and every nonzero ideal has a monic polynomial generator.

Division and preparation hold over any complete ultrametric normed commutative ring with
multiplicative norm, provided the distinguished coefficient is a unit. The ideal-theory results
use a field.

The algebra is `washnitzerAlgebra Unit K`, whose underlying formal series are `PowerSeries K`.
No completeness of this algebra is asserted: completeness is used only for the coefficient
ring when applying `TauCeti.PowerSeries.IsDistinguished.exists_mul_add_eq` and its
preparation theorem. The ideal argument follows the least-distinguished-degree argument of
`TauCeti.PowerSeries.IsDistinguished.span_singleton_eq_of_forall_le`.

## References

* E. Grosse-Klönne, *Rigid analytic spaces with overconvergent structure sheaf*,
  J. reine angew. Math. 519 (2000), §1.3(i)–(ii) and §1.4(1).
* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §§5.2.1–5.2.2.
-/

public section

namespace TauCeti.Dagger

open TauCeti.PowerSeries

section Ring

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [NormMulClass R] [CompleteSpace R]

/-- Weierstrass division in `R⟨X⟩†`: a divisor distinguished of degree `s` at radius one, with a
unit leading coefficient, gives a unique overconvergent quotient and a remainder with every
coefficient in degree `≥ s` zero. -/
theorem existsUnique_mul_add_eq_of_isDistinguished_one
    {f : washnitzerAlgebra Unit R} {s : ℕ}
    (hf : IsDistinguished 1 s (f : PowerSeries R))
    (hu : IsUnit (PowerSeries.coeff s (f : PowerSeries R))) (g : washnitzerAlgebra Unit R) :
    ∃! p : washnitzerAlgebra Unit R × washnitzerAlgebra Unit R,
      (∀ m, s ≤ m → PowerSeries.coeff m (p.2 : PowerSeries R) = 0) ∧ p.1 * f + p.2 = g := by
  obtain ⟨ρ₀, hρ₀, hgρ₀⟩ := mem_washnitzerAlgebra.mp g.2
  obtain ⟨ρ, hρ, hρρ₀, hfr, hfd⟩ := exists_isDistinguished_of_isDistinguished_one hf hρ₀
  have hgr : PowerSeries.IsRestricted ρ (g : PowerSeries R) :=
    MvPowerSeries.isRestricted_of_le hgρ₀ (fun _ ↦ zero_le_one.trans hρ.le) fun _ ↦ hρρ₀
  obtain ⟨q, r, hq, hr, hqr⟩ :=
    hfd.exists_mul_add_eq hu (zero_lt_one.trans hρ) hfr hgr
  let Q : washnitzerAlgebra Unit R := ⟨q, mem_washnitzerAlgebra.mpr ⟨ρ, hρ, hq⟩⟩
  let rW : washnitzerAlgebra Unit R :=
    ⟨r, mem_washnitzerAlgebra.mpr ⟨2, one_lt_two, isRestricted_of_forall_coeff_eq_zero hr⟩⟩
  refine ⟨(Q, rW), ⟨hr, Subtype.ext hqr⟩, fun p ⟨hp, heq⟩ ↦ ?_⟩
  obtain ⟨heqQ, heqR⟩ := hf.eq_and_eq_of_mul_add_eq_mul_add one_pos (fun _ ↦ norm_mul _ _)
    (isRestricted_of_mem_washnitzerAlgebra p.1.2 zero_le_one le_rfl)
    (isRestricted_of_mem_washnitzerAlgebra Q.2 zero_le_one le_rfl) hp hr
    ((congrArg (fun a : washnitzerAlgebra Unit R ↦ (a : PowerSeries R)) heq).trans hqr.symm)
  exact Prod.ext (Subtype.ext heqQ) (Subtype.ext heqR)

/-- Weierstrass preparation in `R⟨X⟩†`: a series distinguished of degree `s` at radius one, with a
unit leading coefficient, has a unique factorisation as an overconvergent unit times a monic
polynomial of degree `s`. -/
theorem existsUnique_isUnit_isMonicOfDegree_mul_eq_of_isDistinguished_one
    {f : washnitzerAlgebra Unit R} {s : ℕ}
    (hf : IsDistinguished 1 s (f : PowerSeries R))
    (hu : IsUnit (PowerSeries.coeff s (f : PowerSeries R))) :
    ∃! p : washnitzerAlgebra Unit R × Polynomial R,
      IsUnit p.1 ∧ p.2.IsMonicOfDegree s ∧
        p.1 * washnitzerAlgebra.ofPolynomial R p.2 = f := by
  obtain ⟨ρ, hρ, _, hfr, hfd⟩ := exists_isDistinguished_of_isDistinguished_one hf one_lt_two
  obtain ⟨e, ω, he, hω, heω⟩ := hfd.exists_isUnit_isMonicOfDegree_mul_eq
    hu (zero_lt_one.trans hρ) hfr
  let ι : PowerSeries.IsRestricted.subring (R := R) ρ →+* washnitzerAlgebra Unit R :=
    (PowerSeries.IsRestricted.subring (R := R) ρ).subtype.codRestrict _
      fun a ↦ mem_washnitzerAlgebra.mpr ⟨ρ, hρ, a.2⟩
  have heω' : ((ι e : washnitzerAlgebra Unit R) : PowerSeries R) * ω = f := by
    simpa [ι, RingHom.codRestrict_apply] using heω
  refine ⟨(ι e, ω), ⟨he.map ι, hω, Subtype.ext (by simpa using heω')⟩,
    fun p ⟨hp, hm, heq⟩ ↦ ?_⟩
  obtain ⟨hu, hpoly⟩ := hf.eq_and_eq_of_mul_eq_mul one_pos
    (hp.map (washnitzerAlgebra.toTate Unit R))
    ((he.map ι).map (washnitzerAlgebra.toTate Unit R)) hm hω
    (by simpa using congrArg (fun a : washnitzerAlgebra Unit R ↦ (a : PowerSeries R)) heq)
    (by rw [washnitzerAlgebra.coe_toTate]; exact heω')
  exact Prod.ext (washnitzerAlgebra.toTate_injective hu) hpoly

end Ring

section Field

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Every nonzero overconvergent series in one variable is an overconvergent unit times a monic
polynomial; the polynomial is distinguished of its own degree at radius one. -/
theorem exists_isUnit_isMonicOfDegree_mul_eq {f : washnitzerAlgebra Unit K} (hf : f ≠ 0) :
    ∃ (e : washnitzerAlgebra Unit K) (ω : Polynomial K) (s : ℕ),
      IsUnit e ∧ ω.IsMonicOfDegree s ∧ IsDistinguished 1 s (ω : PowerSeries K) ∧
        e * washnitzerAlgebra.ofPolynomial K ω = f := by
  obtain ⟨s, hs⟩ := washnitzerAlgebra.exists_isDistinguished_one hf
  obtain ⟨⟨e, ω⟩, ⟨he, hω, heω⟩, _⟩ :=
    existsUnique_isUnit_isMonicOfDegree_mul_eq_of_isDistinguished_one hs hs.coeff_ne_zero.isUnit
  have heω' : (e : PowerSeries K) * (ω : PowerSeries K) = f := by
    simpa using congrArg (fun a : washnitzerAlgebra Unit K ↦ (a : PowerSeries K)) heω
  exact ⟨e, ω, s, he, hω, IsDistinguished.of_isUnit_mul
    (by simpa only [washnitzerAlgebra.coe_toTate, heω'] using hs) one_pos
    (he.map (washnitzerAlgebra.toTate Unit K)), heω⟩

/-- An element of an ideal of `K⟨X⟩†` generates it when its unit-radius distinguished degree
is least among the distinguished degrees of the elements of that ideal. -/
theorem span_singleton_eq_of_forall_le
    {I : Ideal (washnitzerAlgebra Unit K)} {f : washnitzerAlgebra Unit K} {s : ℕ}
    (hfI : f ∈ I) (hf : IsDistinguished 1 s (f : PowerSeries K))
    (hmin : ∀ g ∈ I, ∀ t, IsDistinguished 1 t (g : PowerSeries K) → s ≤ t) :
    Ideal.span {f} = I := by
  refine le_antisymm (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hfI)) fun g hg ↦ ?_
  obtain ⟨⟨q, r⟩, ⟨hr, hqr⟩, _⟩ :=
    existsUnique_mul_add_eq_of_isDistinguished_one hf hf.coeff_ne_zero.isUnit g
  have hrI : r ∈ I := by
    have heq : r = g - q * f := by rw [← hqr]; ring
    rw [heq]
    exact sub_mem hg (I.mul_mem_left _ hfI)
  have hr0 : r = 0 := by
    by_contra hne
    obtain ⟨t, ht⟩ := washnitzerAlgebra.exists_isDistinguished_one hne
    exact ht.coeff_ne_zero (hr t (hmin r hrI t ht))
  rw [← hqr, hr0, add_zero]
  exact Ideal.mem_span_singleton.mpr ⟨q, mul_comm q f⟩

/-- The Monsky–Washnitzer algebra in one variable over a complete ultrametric normed field is
a principal ideal ring, hence a noetherian unique factorisation domain. -/
instance washnitzerAlgebra.isPrincipalIdealRing_unit :
    IsPrincipalIdealRing (washnitzerAlgebra Unit K) := by
  classical
  refine ⟨fun I ↦ ?_⟩
  rcases eq_or_ne I ⊥ with rfl | hI
  · exact ⟨⟨0, by simp⟩⟩
  obtain ⟨g, hgI, hg⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  have hex : ∃ s, ∃ f ∈ I, IsDistinguished 1 s (f : PowerSeries K) := by
    obtain ⟨s, hs⟩ := washnitzerAlgebra.exists_isDistinguished_one hg
    exact ⟨s, g, hgI, hs⟩
  obtain ⟨f, hfI, hf⟩ := Nat.find_spec hex
  exact ⟨⟨f, (span_singleton_eq_of_forall_le hfI hf
    fun g hg t ht ↦ Nat.find_le ⟨g, hg, ht⟩).symm⟩⟩

/-- Every nonzero ideal of `K⟨X⟩†` has a monic polynomial generator, distinguished of its own
degree at unit radius. The zero ideal is excluded because its only generator is zero. -/
theorem exists_isMonicOfDegree_span_singleton_eq
    {I : Ideal (washnitzerAlgebra Unit K)} (hI : I ≠ ⊥) :
    ∃ (ω : Polynomial K) (s : ℕ),
      ω.IsMonicOfDegree s ∧ IsDistinguished 1 s (ω : PowerSeries K) ∧
        Ideal.span {washnitzerAlgebra.ofPolynomial K ω} = I := by
  obtain ⟨f, hf⟩ := (IsPrincipalIdealRing.principal I).principal
  have hf0 : f ≠ 0 := fun h ↦ hI (hf.trans (Ideal.span_singleton_eq_bot.mpr h))
  obtain ⟨e, ω, s, he, hm, hd, heω⟩ := exists_isUnit_isMonicOfDegree_mul_eq hf0
  refine ⟨ω, s, hm, hd, ?_⟩
  rw [← Ideal.span_singleton_mul_left_unit he, heω]
  exact hf.symm

end Field

end TauCeti.Dagger
