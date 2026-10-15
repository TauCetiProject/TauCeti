/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.Weierstrass.Preparation
public import Mathlib.RingTheory.AdjoinRoot

/-!
# Quotients by distinguished restricted power series

Weierstrass division identifies the quotient of restricted series by a distinguished monic
polynomial with its polynomial quotient. Preparation extends this description to any distinguished
restricted series with a unit dominant coefficient. In particular, these quotients are finite free
over the coefficient ring. This is the finite-module step in the induction proving noetherianity
of Tate algebras: after making a series distinguished in the last variable, its quotient is finite
over the Tate algebra in the remaining variables.

The radius may be any positive real number, and the coefficients may lie in a complete ultrametric
normed commutative ring with multiplicative norm. No noetherian or field hypothesis is required.

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §§5.2.1–5.2.2 and §5.2.6.

The polynomial-to-series quotient comparison follows the construction of Mathlib's
`Polynomial.IsDistinguishedAt.algEquivQuotient`, for adically complete rings and unrestricted
series. Here Gauss-norm Weierstrass division supplies the existence and uniqueness instead.
-/

public section

namespace TauCeti.PowerSeries

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [NormMulClass R]
  {c : ℝ} {s : ℕ} {p : Polynomial R}

/-- Divisibility of polynomials by a distinguished monic polynomial is unchanged on passing
to restricted series. The assertion needs uniqueness of division, but not completeness. -/
theorem IsDistinguished.polynomialToRestricted_dvd_iff
    (hp : IsDistinguished c s (p : PowerSeries R)) (hc : 0 < c)
    (hm : p.IsMonicOfDegree s) (g : Polynomial R) :
    polynomialToRestricted c p ∣ polynomialToRestricted c g ↔ p ∣ g := by
  have : Nontrivial R := nontrivial_of_ne _ _ hp.coeff_ne_zero
  refine ⟨fun h ↦ ?_, fun h ↦ map_dvd (polynomialToRestricted c) h⟩
  obtain ⟨a, ha⟩ := h
  have hdiv : (g : PowerSeries R) = (g /ₘ p : PowerSeries R) * (p : PowerSeries R)
      + (g %ₘ p : PowerSeries R) := by
    exact_mod_cast (Polynomial.modByMonic_add_div g p).symm.trans (by ring)
  have hr : ∀ n, s ≤ n → (g %ₘ p : PowerSeries R).coeff n = 0 := by
    intro n hn
    rw [Polynomial.coeff_coe]
    apply Polynomial.coeff_eq_zero_of_degree_lt
    exact (Polynomial.degree_modByMonic_lt g hm.monic).trans_le
      (by rw [Polynomial.degree_eq_natDegree hm.ne_zero, hm.natDegree_eq]; exact_mod_cast hn)
  have heq : (a : PowerSeries R) * (p : PowerSeries R) + 0 =
      (g /ₘ p : PowerSeries R) * (p : PowerSeries R) + (g %ₘ p : PowerSeries R) := by
    have hcoe := congrArg (fun x : PowerSeries.IsRestricted.subring (R := R) c ↦
      (x : PowerSeries R)) ha
    simp only [coe_polynomialToRestricted, Subring.coe_mul] at hcoe
    simpa [mul_comm] using hcoe.symm.trans hdiv
  have hzero := (hp.eq_and_eq_of_mul_add_eq_mul_add hc a.2
    (isRestricted_polynomial (g /ₘ p)) (fun n _ ↦ by simp) hr heq).2
  exact (Polynomial.modByMonic_eq_zero_iff_dvd hm.monic).mp
    (Polynomial.coe_injective R (by simpa using hzero.symm))

section Complete

variable [CompleteSpace R]

/-- The inclusion of polynomials induces the quotient comparison for a distinguished monic
polynomial. Its inverse sends a series class to the class of its Weierstrass remainder. -/
noncomputable def IsDistinguished.polynomialQuotientEquiv
    (hp : IsDistinguished c s (p : PowerSeries R)) (hc : 0 < c)
    (hm : p.IsMonicOfDegree s) :
    (Polynomial R ⧸ Ideal.span {p}) ≃ₐ[R]
      (PowerSeries.IsRestricted.subring (R := R) c ⧸
        Ideal.span {polynomialToRestricted c p}) := by
  have hmap : Ideal.span {p} ≤
      (Ideal.span {polynomialToRestricted c p}).comap (polynomialToRestricted c) :=
    Ideal.span_le.mpr fun a ha ↦ by
      simp only [Set.mem_singleton_iff] at ha
      subst a
      exact Ideal.subset_span (Set.mem_singleton _)
  let F := Ideal.quotientMapₐ (Ideal.span {polynomialToRestricted c p})
    (polynomialToRestricted c) hmap
  apply AlgEquiv.ofBijective F
  constructor
  · apply Ideal.quotientMap_injective' (H := hmap)
    intro g hg
    exact Ideal.mem_span_singleton.mpr <|
      (hp.polynomialToRestricted_dvd_iff hc hm g).mp (Ideal.mem_span_singleton.mp hg)
  · intro x
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hu : IsUnit ((polynomialToRestricted c p : PowerSeries R).coeff s) := by
      simp [← hm.natDegree_eq, hm.monic.coeff_natDegree]
    have hp' : IsDistinguished c s (polynomialToRestricted c p : PowerSeries R) := by
      simpa only [coe_polynomialToRestricted] using hp
    obtain ⟨q, r, hr, hqr⟩ := hp'.exists_mul_add_eq_subring hc hu g
    refine ⟨Ideal.Quotient.mk _ (PowerSeries.trunc s (r : PowerSeries R)), ?_⟩
    rw [Ideal.quotient_map_mkₐ]
    rw [polynomialToRestricted_trunc_eq_of_coeff_eq_zero r hr, ← hqr, map_add, map_mul]
    simp

/-- On a polynomial representative, the comparison is the usual polynomial inclusion. -/
@[simp]
theorem IsDistinguished.polynomialQuotientEquiv_mk
    (hp : IsDistinguished c s (p : PowerSeries R)) (hc : 0 < c)
    (hm : p.IsMonicOfDegree s) (g : Polynomial R) :
    hp.polynomialQuotientEquiv hc hm (Ideal.Quotient.mk _ g) =
      Ideal.Quotient.mk _ (polynomialToRestricted c g) := by
  -- `AlgEquiv.ofBijective` retains the quotient map as its forward map.
  unfold polynomialQuotientEquiv
  exact Ideal.quotient_map_mkₐ (I := Ideal.span {p})
    (J := Ideal.span {polynomialToRestricted c p}) (polynomialToRestricted c)
    (by simp [Ideal.span_le])

/-- The inverse comparison sends the class of a polynomial to its polynomial quotient class. -/
@[simp]
theorem IsDistinguished.polynomialQuotientEquiv_symm_mk
    (hp : IsDistinguished c s (p : PowerSeries R)) (hc : 0 < c)
    (hm : p.IsMonicOfDegree s) (g : Polynomial R) :
    (hp.polynomialQuotientEquiv hc hm).symm
        (Ideal.Quotient.mk _ (polynomialToRestricted c g)) = Ideal.Quotient.mk _ g := by
  rw [← hp.polynomialQuotientEquiv_mk hc hm]
  exact (hp.polynomialQuotientEquiv hc hm).symm_apply_apply _

/-- Given a Weierstrass decomposition of any restricted series, the inverse comparison sends
its class to the polynomial quotient class of the truncated remainder. -/
theorem IsDistinguished.polynomialQuotientEquiv_symm_mk_of_mul_add_eq
    (hp : IsDistinguished c s (p : PowerSeries R)) (hc : 0 < c)
    (hm : p.IsMonicOfDegree s) (g q r : PowerSeries.IsRestricted.subring (R := R) c)
    (hr : ∀ n, s ≤ n → (r : PowerSeries R).coeff n = 0)
    (hqr : q * polynomialToRestricted c p + r = g) :
    (hp.polynomialQuotientEquiv hc hm).symm (Ideal.Quotient.mk _ g) =
      Ideal.Quotient.mk _ (PowerSeries.trunc s (r : PowerSeries R)) := by
  have heq : Ideal.Quotient.mk (Ideal.span {polynomialToRestricted c p}) g =
      Ideal.Quotient.mk _ (polynomialToRestricted c (PowerSeries.trunc s (r : PowerSeries R))) := by
    rw [polynomialToRestricted_trunc_eq_of_coeff_eq_zero r hr, ← hqr, map_add, map_mul]
    simp
  rw [heq, hp.polynomialQuotientEquiv_symm_mk hc hm]

/-- A distinguished restricted series with a unit dominant coefficient has the same quotient
algebra as a monic polynomial of its distinguished degree. -/
theorem IsDistinguished.exists_polynomialQuotientEquiv
    {f : PowerSeries.IsRestricted.subring (R := R) c}
    (hf : IsDistinguished c s (f : PowerSeries R)) (hc : 0 < c)
    (hu : IsUnit ((f : PowerSeries R).coeff s)) :
    ∃ p : Polynomial R, p.IsMonicOfDegree s ∧
      Nonempty ((Polynomial R ⧸ Ideal.span {p}) ≃ₐ[R]
        (PowerSeries.IsRestricted.subring (R := R) c ⧸ Ideal.span {f})) := by
  obtain ⟨e, p, he, hm, hmul⟩ := hf.exists_isUnit_isMonicOfDegree_mul_eq hu hc f.2
  have hfp : e * polynomialToRestricted c p = f := Subtype.ext (by simpa using hmul)
  have hp : IsDistinguished c s (p : PowerSeries R) :=
    (hmul.symm ▸ hf).of_isUnit_mul hc he
  have hI : Ideal.span {polynomialToRestricted c p} = Ideal.span {f} := by
    rw [← hfp, Ideal.span_singleton_mul_left_unit he]
  exact ⟨p, hm, ⟨(hp.polynomialQuotientEquiv hc hm).trans
    (Ideal.quotientEquivAlgOfEq R hI)⟩⟩

/-- The quotient by a distinguished restricted series with a unit dominant coefficient is
a finite module over the coefficient ring. -/
theorem IsDistinguished.finite_quotient
    {f : PowerSeries.IsRestricted.subring (R := R) c}
    (hf : IsDistinguished c s (f : PowerSeries R)) (hc : 0 < c)
    (hu : IsUnit ((f : PowerSeries R).coeff s)) :
    Module.Finite R (PowerSeries.IsRestricted.subring (R := R) c ⧸ Ideal.span {f}) := by
  obtain ⟨p, hm, ⟨e⟩⟩ := hf.exists_polynomialQuotientEquiv hc hu
  have := hm.monic.finite_quotient
  exact Module.Finite.of_surjective e.toLinearMap e.surjective

/-- The quotient by a distinguished restricted series with a unit dominant coefficient is
free over the coefficient ring. -/
theorem IsDistinguished.free_quotient
    {f : PowerSeries.IsRestricted.subring (R := R) c}
    (hf : IsDistinguished c s (f : PowerSeries R)) (hc : 0 < c)
    (hu : IsUnit ((f : PowerSeries R).coeff s)) :
    Module.Free R (PowerSeries.IsRestricted.subring (R := R) c ⧸ Ideal.span {f}) := by
  obtain ⟨p, hm, ⟨e⟩⟩ := hf.exists_polynomialQuotientEquiv hc hu
  have := hm.monic.free_quotient
  exact Module.Free.of_equiv e.toLinearEquiv

end Complete

end TauCeti.PowerSeries
