/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Dagger.WashnitzerAlgebra
public import TauCeti.RingTheory.PowerSeries.Weierstrass.Preparation
public import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Weierstrass division and preparation for overconvergent series in one variable

A series in `K⟨X⟩†` distinguished of degree `s` at the unit radius stays distinguished of that
same degree at some radius strictly greater than one. Division and preparation at that radius
therefore produce overconvergent quotients and units. Their uniqueness follows at unit radius.
In particular, every nonzero overconvergent series in one variable is a unit times a monic
polynomial. Every ideal is principal, and every nonzero ideal has a monic polynomial generator.

The algebra is `washnitzerAlgebra Unit K`, whose underlying formal series are `PowerSeries K`.
No completeness of this algebra is asserted: completeness is used only for the coefficient
field when applying `TauCeti.PowerSeries.IsDistinguished.exists_mul_add_eq` and its
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

section Radius

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R]

/-- A one-variable overconvergent series distinguished at radius one remains distinguished of
the same degree at some radius greater than one, within any prescribed upper bound. -/
theorem exists_isDistinguished_of_isDistinguished_one
    {f : washnitzerAlgebra Unit R} {s : ℕ}
    (hf : IsDistinguished 1 s (f : PowerSeries R)) {ρ₀ : ℝ} (hρ₀ : 1 < ρ₀) :
    ∃ ρ > (1 : ℝ), ρ ≤ ρ₀ ∧ PowerSeries.IsRestricted ρ (f : PowerSeries R) ∧
      IsDistinguished ρ s (f : PowerSeries R) := by
  -- The strict bound on the tail persists at a radius greater than one.
  let t : PowerSeries R :=
    (f : PowerSeries R) - (PowerSeries.trunc (s + 1) (f : PowerSeries R) : Polynomial R)
  have htW : t ∈ washnitzerAlgebra Unit R :=
    sub_mem f.2 (mem_washnitzerAlgebra.mpr ⟨2, one_lt_two, isRestricted_polynomial _⟩)
  have hnorm : ∀ m, ‖PowerSeries.coeff m t‖ < ‖PowerSeries.coeff s (f : PowerSeries R)‖ := by
    intro m
    simp only [t, map_sub, Polynomial.coeff_coe, PowerSeries.coeff_trunc]
    split_ifs with hm
    · simpa using norm_pos_iff.2 hf.coeff_ne_zero
    · simpa [← hf.norm_coeff_mul_pow_eq] using hf.norm_coeff_mul_pow_lt m (by omega)
  obtain ⟨ρ₁, hρ₁, _, htail⟩ := exists_isRestricted_forall_norm_coeff_mul_pow_lt htW
    (fun u ↦ by
      rw [← PowerSeries.coeff_def (rfl : u () = u ())]
      exact hnorm (u ()))
  obtain ⟨ρ₂, hρ₂, hfρ₂⟩ := mem_washnitzerAlgebra.mp f.2
  let ρ := min ρ₁ (min ρ₂ ρ₀)
  have hρ : 1 < ρ := lt_min hρ₁ (lt_min hρ₂ hρ₀)
  have hρ0 : 0 ≤ ρ := zero_le_one.trans hρ.le
  have hfr : PowerSeries.IsRestricted ρ (f : PowerSeries R) :=
    MvPowerSeries.isRestricted_of_le hfρ₂ (fun _ ↦ hρ0)
      (fun _ ↦ (min_le_right _ _).trans (min_le_left _ _))
  have hlt (m : ℕ) (hm : s < m) :
      ‖PowerSeries.coeff m (f : PowerSeries R)‖ * ρ ^ m <
        ‖PowerSeries.coeff s (f : PowerSeries R)‖ * ρ ^ s := by
    have ht := htail (Finsupp.single () m)
    simp only [Finsupp.degree_single] at ht
    have htm : PowerSeries.coeff m t = PowerSeries.coeff m (f : PowerSeries R) := by
      simp [t, PowerSeries.coeff_trunc, show ¬m < s + 1 by omega]
    rw [PowerSeries.coeff_coeToMvPowerSeries, htm] at ht
    exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hρ0 (min_le_left _ _) m)
      (norm_nonneg _)).trans_lt (ht.trans_le
        (le_mul_of_one_le_right (norm_nonneg _) (one_le_pow₀ hρ.le)))
  -- Earlier coefficients remain dominated because the radius has increased.
  have hle (m : ℕ) : ‖PowerSeries.coeff m (f : PowerSeries R)‖ * ρ ^ m ≤
      ‖PowerSeries.coeff s (f : PowerSeries R)‖ * ρ ^ s := by
    rcases le_or_gt m s with hm | hm
    · have hc := PowerSeries.le_gaussNorm norm 1 (f : PowerSeries R) hf.hasGaussNorm m
      rw [← hf.norm_coeff_mul_pow_eq] at hc
      simp only [one_pow, mul_one] at hc
      exact mul_le_mul hc (pow_le_pow_right₀ hρ.le hm) (by positivity) (norm_nonneg _)
    · exact (hlt m hm).le
  have heq := gaussNorm_eq_of_forall_le hle
  exact ⟨ρ, hρ, (min_le_right _ _).trans (min_le_right _ _), hfr,
    ⟨heq.symm, fun m hm ↦ heq ▸ hlt m hm⟩⟩

end Radius

section Field

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Weierstrass division in `K⟨X⟩†`: a divisor distinguished of degree `s` at radius one gives
a unique overconvergent quotient and a remainder with every coefficient in degree `≥ s` zero. -/
theorem existsUnique_mul_add_eq_of_isDistinguished_one
    {f : washnitzerAlgebra Unit K} {s : ℕ}
    (hf : IsDistinguished 1 s (f : PowerSeries K)) (g : washnitzerAlgebra Unit K) :
    ∃! p : washnitzerAlgebra Unit K × washnitzerAlgebra Unit K,
      (∀ m, s ≤ m → PowerSeries.coeff m (p.2 : PowerSeries K) = 0) ∧ p.1 * f + p.2 = g := by
  obtain ⟨ρ₀, hρ₀, hgρ₀⟩ := mem_washnitzerAlgebra.mp g.2
  obtain ⟨ρ, hρ, hρρ₀, hfr, hfd⟩ := exists_isDistinguished_of_isDistinguished_one hf hρ₀
  have hgr : PowerSeries.IsRestricted ρ (g : PowerSeries K) :=
    MvPowerSeries.isRestricted_of_le hgρ₀ (fun _ ↦ zero_le_one.trans hρ.le) fun _ ↦ hρρ₀
  obtain ⟨q, r, hq, hr, hqr⟩ :=
    hfd.exists_mul_add_eq hfd.coeff_ne_zero.isUnit (zero_lt_one.trans hρ) hfr hgr
  let Q : washnitzerAlgebra Unit K := ⟨q, mem_washnitzerAlgebra.mpr ⟨ρ, hρ, hq⟩⟩
  let R : washnitzerAlgebra Unit K :=
    ⟨r, mem_washnitzerAlgebra.mpr ⟨2, one_lt_two, isRestricted_of_forall_coeff_eq_zero hr⟩⟩
  refine ⟨(Q, R), ⟨hr, Subtype.ext hqr⟩, fun p ⟨hp, heq⟩ ↦ ?_⟩
  obtain ⟨heqQ, heqR⟩ := hf.eq_and_eq_of_mul_add_eq_mul_add one_pos (fun _ ↦ norm_mul _ _)
    (isRestricted_of_mem_washnitzerAlgebra p.1.2 zero_le_one le_rfl)
    (isRestricted_of_mem_washnitzerAlgebra Q.2 zero_le_one le_rfl) hp hr
    ((congrArg (fun a : washnitzerAlgebra Unit K ↦ (a : PowerSeries K)) heq).trans hqr.symm)
  exact Prod.ext (Subtype.ext heqQ) (Subtype.ext heqR)

/-- Weierstrass preparation in `K⟨X⟩†`: a series distinguished of degree `s` at radius one has
a unique factorisation as an overconvergent unit times a monic polynomial of degree `s`. -/
theorem existsUnique_isUnit_isMonicOfDegree_mul_eq_of_isDistinguished_one
    {f : washnitzerAlgebra Unit K} {s : ℕ}
    (hf : IsDistinguished 1 s (f : PowerSeries K)) :
    ∃! p : washnitzerAlgebra Unit K × Polynomial K,
      IsUnit p.1 ∧ p.2.IsMonicOfDegree s ∧
        (p.1 : PowerSeries K) * (p.2 : PowerSeries K) = (f : PowerSeries K) := by
  obtain ⟨ρ, hρ, _, hfr, hfd⟩ := exists_isDistinguished_of_isDistinguished_one hf one_lt_two
  obtain ⟨e, ω, he, hω, heω⟩ := hfd.exists_isUnit_isMonicOfDegree_mul_eq
    hfd.coeff_ne_zero.isUnit (zero_lt_one.trans hρ) hfr
  let ι : PowerSeries.IsRestricted.subring (R := K) ρ →+* washnitzerAlgebra Unit K :=
    (PowerSeries.IsRestricted.subring (R := K) ρ).subtype.codRestrict _
      fun a ↦ mem_washnitzerAlgebra.mpr ⟨ρ, hρ, a.2⟩
  refine ⟨(ι e, ω), ⟨he.map ι, hω, heω⟩, fun p ⟨hp, hm, heq⟩ ↦ ?_⟩
  obtain ⟨hu, hpoly⟩ := hf.eq_and_eq_of_mul_eq_mul one_pos
    (hp.map (washnitzerAlgebra.toTate Unit K))
    ((he.map ι).map (washnitzerAlgebra.toTate Unit K)) hm hω
    (by simpa only [washnitzerAlgebra.coe_toTate] using heq)
    (by rw [washnitzerAlgebra.coe_toTate]; exact heω)
  exact Prod.ext (washnitzerAlgebra.toTate_injective hu) hpoly

/-- Every nonzero overconvergent series in one variable is an overconvergent unit times a monic
polynomial; the polynomial is distinguished of its own degree at radius one. -/
theorem exists_isUnit_isMonicOfDegree_mul_eq {f : washnitzerAlgebra Unit K} (hf : f ≠ 0) :
    ∃ (e : washnitzerAlgebra Unit K) (ω : Polynomial K) (s : ℕ),
      IsUnit e ∧ ω.IsMonicOfDegree s ∧ IsDistinguished 1 s (ω : PowerSeries K) ∧
        (e : PowerSeries K) * (ω : PowerSeries K) = (f : PowerSeries K) := by
  obtain ⟨s, hs⟩ := exists_isDistinguished one_pos
    (isRestricted_of_mem_washnitzerAlgebra f.2 zero_le_one le_rfl) (by simpa using hf)
  obtain ⟨⟨e, ω⟩, ⟨he, hω, heω⟩, _⟩ :=
    existsUnique_isUnit_isMonicOfDegree_mul_eq_of_isDistinguished_one hs
  exact ⟨e, ω, s, he, hω, IsDistinguished.of_isUnit_mul
    (by simpa only [washnitzerAlgebra.coe_toTate, heω] using hs) one_pos
    (he.map (washnitzerAlgebra.toTate Unit K)), heω⟩

/-- An element of an ideal of `K⟨X⟩†` generates it when its unit-radius distinguished degree
is least among the distinguished degrees of the elements of that ideal. -/
theorem span_singleton_eq_of_forall_le
    {I : Ideal (washnitzerAlgebra Unit K)} {f : washnitzerAlgebra Unit K} {s : ℕ}
    (hfI : f ∈ I) (hf : IsDistinguished 1 s (f : PowerSeries K))
    (hmin : ∀ g ∈ I, ∀ t, IsDistinguished 1 t (g : PowerSeries K) → s ≤ t) :
    Ideal.span {f} = I := by
  refine le_antisymm (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hfI)) fun g hg ↦ ?_
  obtain ⟨⟨q, r⟩, ⟨hr, hqr⟩, _⟩ := existsUnique_mul_add_eq_of_isDistinguished_one hf g
  have hrI : r ∈ I := by
    have heq : r = g - q * f := by rw [← hqr]; ring
    rw [heq]
    exact sub_mem hg (I.mul_mem_left _ hfI)
  have hr0 : r = 0 := by
    by_contra hne
    obtain ⟨t, ht⟩ := exists_isDistinguished one_pos
      (isRestricted_of_mem_washnitzerAlgebra r.2 zero_le_one le_rfl) (by simpa using hne)
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
    obtain ⟨s, hs⟩ := exists_isDistinguished one_pos
      (isRestricted_of_mem_washnitzerAlgebra g.2 zero_le_one le_rfl) (by simpa using hg)
    exact ⟨s, g, hgI, hs⟩
  obtain ⟨f, hfI, hf⟩ := Nat.find_spec hex
  exact ⟨⟨f, (span_singleton_eq_of_forall_le hfI hf
    fun g hg t ht ↦ Nat.find_le ⟨g, hg, ht⟩).symm⟩⟩

/-- Every nonzero ideal of `K⟨X⟩†` has a monic polynomial generator, distinguished of its own
degree at unit radius. The zero ideal is excluded because its only generator is zero. -/
theorem exists_isMonicOfDegree_span_singleton_eq
    {I : Ideal (washnitzerAlgebra Unit K)} (hI : I ≠ ⊥) :
    ∃ (g : washnitzerAlgebra Unit K) (ω : Polynomial K) (s : ℕ),
      ω.IsMonicOfDegree s ∧ IsDistinguished 1 s (ω : PowerSeries K) ∧
        (g : PowerSeries K) = (ω : PowerSeries K) ∧ Ideal.span {g} = I := by
  obtain ⟨f, hf⟩ := (IsPrincipalIdealRing.principal I).principal
  have hf0 : f ≠ 0 := fun h ↦ hI (hf.trans (Ideal.span_singleton_eq_bot.mpr h))
  obtain ⟨e, ω, s, he, hm, hd, heω⟩ := exists_isUnit_isMonicOfDegree_mul_eq hf0
  let g : washnitzerAlgebra Unit K :=
    ⟨(ω : PowerSeries K), mem_washnitzerAlgebra.mpr ⟨2, one_lt_two, isRestricted_polynomial _⟩⟩
  have hfactor : e * g = f := Subtype.ext heω
  refine ⟨g, ω, s, hm, hd, rfl, ?_⟩
  rw [← Ideal.span_singleton_mul_left_unit he g, hfactor]
  exact hf.symm

end Field

end TauCeti.Dagger
