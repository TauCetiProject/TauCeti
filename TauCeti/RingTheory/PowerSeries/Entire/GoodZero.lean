/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Polynomial.Taylor
public import TauCeti.RingTheory.PowerSeries.Entire.Division

/-!
# Good zeros of entire power series

Let `f` be a power series over a commutative topological ring `R` and write `Δᵏ f` for its Hasse
derivatives (`PowerSeries.hasseDeriv`). The series `f` has a **good zero of order `h`** at `a : R`
if `(Δʲ f)(a) = 0` for every `j < h` and `(Δʰ f)(a)` is a unit. Order zero means that `f(a)` itself
is a unit. Over a field this is a zero of multiplicity exactly `h`; over a general coefficient
ring, the unit condition on the first nonvanishing Hasse derivative is what allows `X - a` to be
split off exactly `h` times, as needed for the spectral projectors attached to zeros of Fredholm
determinants. No factorial is inverted, so the notion keeps its meaning in positive
characteristic and over rings with nilpotents.

For an entire series over a complete normed ring, the good zeros of order `h` at `a` are exactly
the factorisations `f = (X - a)ʰ g` with `g` entire and `g(a)` a unit
(`PowerSeries.IsEntire.isGoodZero_iff`). This follows from the evaluated Leibniz rule
`(Δʲ ((X - a)ᵐ g))(a) = (Δʲ⁻ᵐ g)(a)` for `m ≤ j`, and `0` otherwise
(`PowerSeries.IsEntire.evalAt_hasseDeriv_X_sub_C_pow_mul`), together with the factor theorem for
entire series (`PowerSeries.IsEntire.exists_eq_X_sub_C_pow_mul`). Consequently orders add under
products, and when `f(0) = 1` a good zero of positive order is a unit, so the factor `(X - a)ʰ`
may be renormalised to `(1 - a⁻¹ X)ʰ`.

## Main definitions

* `PowerSeries.IsGoodZero f a h`: `f` has a good zero of order `h` at `a`.

## Main results

* `PowerSeries.IsGoodZero.unique`: over a nontrivial ring the order of a good zero is unique.
* `PowerSeries.isGoodZero_coe_iff`, `PowerSeries.isGoodZero_coe_iff_of_field`: for polynomials
  the order is the root multiplicity, and over a ring the quotient by `(X - a)ʰ` must be a unit
  at `a`.
* `PowerSeries.IsEntire.isGoodZero_iff`: factorisation of an entire series at a good zero.
* `PowerSeries.IsGoodZero.mul`: the orders of good zeros of entire series add under products.
* `PowerSeries.IsGoodZero.isUnit` and `PowerSeries.IsGoodZero.exists_eq_one_sub_C_mul_X_pow_mul`:
  for `f(0) = 1`, a good zero `a` of positive order `h` is a unit and `f = (1 - a⁻¹ X)ʰ G` with
  `G` entire, `G(0) = 1` and `G(a)` a unit.
* `PowerSeries.IsGoodZero.map`: good zeros of entire series are preserved by continuous
  coefficient homomorphisms.

## References

* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. 127 (1997),
  417–479, Appendix A4.
* C. Johansson and J. Newton, *Extended eigenvarieties for overconvergent cohomology*,
  Algebra Number Theory 13 (2019), §2.2.
-/

public section

namespace PowerSeries

section TopologicalRing

variable {R : Type*} [CommRing R] [TopologicalSpace R] {f : R⟦X⟧} {a : R} {h k : ℕ}

/-- A power series `f` has a **good zero of order `h`** at `a` if its Hasse derivatives of order
less than `h` vanish at `a` and its Hasse derivative of order `h` is a unit at `a`. For `h = 0`
this says that `f(a)` is a unit. Values at `a` are the infinite sums `PowerSeries.evalAt`, so the
notion is meaningful for entire series over a complete normed ring. -/
def IsGoodZero (f : R⟦X⟧) (a : R) (h : ℕ) : Prop :=
  (∀ j < h, (hasseDeriv j f).evalAt a = 0) ∧ IsUnit ((hasseDeriv h f).evalAt a)

/-- Unfolding of `PowerSeries.IsGoodZero`. -/
theorem isGoodZero_iff :
    f.IsGoodZero a h ↔
      (∀ j < h, (hasseDeriv j f).evalAt a = 0) ∧ IsUnit ((hasseDeriv h f).evalAt a) :=
  Iff.rfl

/-- A good zero of order `0` is a point at which the value is a unit. -/
@[simp]
theorem isGoodZero_zero_iff : f.IsGoodZero a 0 ↔ IsUnit (f.evalAt a) := by
  simp [isGoodZero_iff, hasseDeriv_zero]

/-- At a good zero of order `h`, the Hasse derivatives of order less than `h` vanish. -/
theorem IsGoodZero.evalAt_hasseDeriv_eq_zero (hf : f.IsGoodZero a h) {j : ℕ} (hj : j < h) :
    (hasseDeriv j f).evalAt a = 0 :=
  hf.1 j hj

/-- At a good zero of order `h`, the Hasse derivative of order `h` is a unit. -/
theorem IsGoodZero.isUnit_evalAt_hasseDeriv (hf : f.IsGoodZero a h) :
    IsUnit ((hasseDeriv h f).evalAt a) :=
  hf.2

/-- At a good zero of positive order, the series vanishes. -/
theorem IsGoodZero.evalAt_eq_zero (hf : f.IsGoodZero a h) (hh : 0 < h) : f.evalAt a = 0 := by
  simpa [hasseDeriv_zero] using hf.evalAt_hasseDeriv_eq_zero hh

/-- Over a nontrivial ring, the order of a good zero is unique. -/
theorem IsGoodZero.unique [Nontrivial R] (hh : f.IsGoodZero a h) (hk : f.IsGoodZero a k) :
    h = k := by
  rcases lt_trichotomy h k with hlt | rfl | hlt
  · exact absurd (hk.evalAt_hasseDeriv_eq_zero hlt ▸ hh.isUnit_evalAt_hasseDeriv) not_isUnit_zero
  · rfl
  · exact absurd (hh.evalAt_hasseDeriv_eq_zero hlt ▸ hk.isUnit_evalAt_hasseDeriv) not_isUnit_zero

/-- The series `(X - a)ʰ` has a good zero of order `h` at `a`. -/
@[simp]
theorem isGoodZero_X_sub_C_pow : ((X - C a) ^ h : R⟦X⟧).IsGoodZero a h := by
  simp +contextual [isGoodZero_iff, evalAt_hasseDeriv_X_sub_C_pow, Nat.ne_of_lt]

/-- **Good zeros of polynomials.** Over a nontrivial ring, a polynomial `p` has a good zero of
order `h` at `a` exactly when `h` is the multiplicity of `a` as a root of `p` and the quotient of
`p` by `(X - a)ʰ` is a unit at `a`. -/
theorem isGoodZero_coe_iff [Nontrivial R] {p : Polynomial R} :
    (p : R⟦X⟧).IsGoodZero a h ↔
      p.rootMultiplicity a = h ∧
        IsUnit ((p /ₘ (Polynomial.X - Polynomial.C a) ^ h).eval a) := by
  simp_rw [isGoodZero_iff, evalAt_hasseDeriv_coe]
  have hT := Polynomial.natTrailingDegree_taylor p a
  constructor
  · rintro ⟨hlt, hunit⟩
    have hne : (Polynomial.taylor a p).coeff h ≠ 0 := hunit.ne_zero
    have hdeg : p.rootMultiplicity a = h := by
      rw [← hT]
      exact le_antisymm (Polynomial.natTrailingDegree_le_of_ne_zero hne)
        (Polynomial.le_natTrailingDegree (fun h0 ↦ hne (by simp [h0])) hlt)
    refine ⟨hdeg, ?_⟩
    rwa [← hdeg, ← Polynomial.coeff_taylor_rootMultiplicity, hdeg]
  · rintro ⟨rfl, hunit⟩
    refine ⟨fun j hj ↦ Polynomial.coeff_eq_zero_of_lt_natTrailingDegree (by rwa [hT]), ?_⟩
    rwa [Polynomial.coeff_taylor_rootMultiplicity]

/-- Over a field, a polynomial has a good zero of order `h` at `a` exactly when it is nonzero and
`a` is a root of multiplicity `h`. -/
theorem isGoodZero_coe_iff_of_field {K : Type*} [Field K] [TopologicalSpace K]
    {p : Polynomial K} {a : K} {h : ℕ} :
    (p : K⟦X⟧).IsGoodZero a h ↔ p ≠ 0 ∧ p.rootMultiplicity a = h := by
  rw [isGoodZero_coe_iff, isUnit_iff_ne_zero]
  constructor
  · rintro ⟨rfl, hne⟩
    exact ⟨fun hp ↦ hne (by simp [hp]), rfl⟩
  · rintro ⟨hp, rfl⟩
    exact ⟨rfl, Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero a hp⟩

end TopologicalRing

section Normed

variable {R : Type*} [NormedCommRing R] [CompleteSpace R] {f g : R⟦X⟧} {a : R} {h k : ℕ}

/-- For entire `g`, the series `(X - a)ʰ g` has a good zero of order `h` at `a` exactly when
`g(a)` is a unit. -/
@[simp]
theorem IsEntire.isGoodZero_X_sub_C_pow_mul_iff (hg : g.IsEntire) :
    ((X - C a) ^ h * g).IsGoodZero a h ↔ IsUnit (g.evalAt a) := by
  simp only [isGoodZero_iff, hg.evalAt_hasseDeriv_X_sub_C_pow_mul, le_refl, ite_true,
    Nat.sub_self, hasseDeriv_zero, LinearMap.id_apply, and_iff_right_iff_imp]
  intro _ j hj
  simp [Nat.not_le.mpr hj]

/-- **Factorisation at a good zero.** An entire series `f` has a good zero of order `h` at `a`
exactly when `f = (X - a)ʰ g` for an entire series `g` with `g(a)` a unit. -/
theorem IsEntire.isGoodZero_iff (hf : f.IsEntire) :
    f.IsGoodZero a h ↔ ∃ g : R⟦X⟧, g.IsEntire ∧ f = (X - C a) ^ h * g ∧ IsUnit (g.evalAt a) := by
  refine ⟨fun hfa ↦ ?_, fun ⟨g, hg, hfg, hga⟩ ↦ hfg ▸ hg.isGoodZero_X_sub_C_pow_mul_iff.mpr hga⟩
  obtain ⟨g, hg, rfl⟩ := hf.exists_eq_X_sub_C_pow_mul hfa.1
  exact ⟨g, hg, rfl, hg.isGoodZero_X_sub_C_pow_mul_iff.mp hfa⟩

/-- **Orders of good zeros add.** If entire series `f` and `g` have good zeros of orders `h` and
`k` at `a`, then `f * g` has a good zero of order `h + k` at `a`. -/
theorem IsGoodZero.mul (hf : f.IsEntire) (hg : g.IsEntire) (hfa : f.IsGoodZero a h)
    (hga : g.IsGoodZero a k) : (f * g).IsGoodZero a (h + k) := by
  obtain ⟨f₁, hf₁, rfl, hf₁a⟩ := hf.isGoodZero_iff.mp hfa
  obtain ⟨g₁, hg₁, rfl, hg₁a⟩ := hg.isGoodZero_iff.mp hga
  rw [mul_mul_mul_comm, ← pow_add, (hf₁.mul hg₁).isGoodZero_X_sub_C_pow_mul_iff, hf₁.evalAt_mul hg₁]
  exact hf₁a.mul hg₁a

/-- **Good zeros of normalised series are units.** If an entire series `f` with `f(0) = 1` has a
good zero of positive order at `a`, then `a` is a unit. -/
theorem IsGoodZero.isUnit (hf : f.IsEntire) (h0 : constantCoeff f = 1) (hfa : f.IsGoodZero a h)
    (hh : 0 < h) : IsUnit a :=
  hf.isUnit_of_evalAt_eq_zero h0 (hfa.evalAt_eq_zero hh)

/-- **Normalised factorisation at a good zero.** If an entire series `f` with `f(0) = 1` has a
good zero of order `h` at `a`, then `f = (1 - a⁻¹ X)ʰ G` with `G` entire, `G(0) = 1` and `G(a)` a
unit. For `h > 0` the point `a` is a unit (`PowerSeries.IsGoodZero.isUnit`); for `h = 0` the
factor `(1 - a⁻¹ X)ʰ` is `1` and `G = f`. -/
theorem IsGoodZero.exists_eq_one_sub_C_mul_X_pow_mul (hf : f.IsEntire)
    (h0 : constantCoeff f = 1) (hfa : f.IsGoodZero a h) :
    ∃ G : R⟦X⟧, G.IsEntire ∧ constantCoeff G = 1 ∧ IsUnit (G.evalAt a) ∧
      f = (1 - C (Ring.inverse a) * X) ^ h * G := by
  rcases Nat.eq_zero_or_pos h with rfl | hh
  · exact ⟨f, hf, h0, isGoodZero_zero_iff.mp hfa, by simp⟩
  obtain ⟨u, rfl⟩ := hfa.isUnit hf h0 hh
  obtain ⟨g, hg, rfl, hga⟩ := hf.isGoodZero_iff.mp hfa
  -- `X - u = (-u) (1 - u⁻¹ X)`, and the scalar `(-u)ʰ` is absorbed into the cofactor.
  have hfac : (X - C (u : R) : R⟦X⟧) = C (-(u : R)) * (1 - C (Ring.inverse (u : R)) * X) := by
    have hu : C (u : R) * C (Ring.inverse (u : R)) = (1 : R⟦X⟧) := by
      simp [← map_mul]
    rw [map_neg]
    linear_combination (-X) * hu
  have hfg : (X - C (u : R)) ^ h * g =
      (1 - C (Ring.inverse (u : R)) * X) ^ h * (C ((-(u : R)) ^ h) * g) := by
    rw [hfac, mul_pow, map_pow]
    ring
  have hG : (C ((-(u : R)) ^ h) * g).IsEntire := (isEntire_C _).mul hg
  refine ⟨_, hG, ?_, ?_, hfg⟩
  · have := congrArg constantCoeff hfg
    simpa [h0] using this.symm
  · rw [(isEntire_C _).evalAt_mul hg, evalAt_C, Algebra.algebraMap_self_apply]
    exact ((u.isUnit.neg).pow h).mul hga

/-- **Good zeros under coefficient maps.** A continuous ring homomorphism `φ` sends a good zero
`a` of order `h` of an entire series `f` to a good zero `φ a` of order `h` of the mapped series. -/
theorem IsGoodZero.map {S : Type*} [CommRing S] [TopologicalSpace S] [T2Space S]
    (hf : f.IsEntire) (φ : R →+* S) (hφ : Continuous φ) (hfa : f.IsGoodZero a h) :
    (PowerSeries.map φ f).IsGoodZero (φ a) h := by
  simp_rw [isGoodZero_iff, hasseDeriv_map, (hf.hasseDeriv _).evalAt_map φ hφ]
  exact ⟨fun j hj ↦ by rw [hfa.evalAt_hasseDeriv_eq_zero hj, map_zero],
    hfa.isUnit_evalAt_hasseDeriv.map φ⟩

end Normed

end PowerSeries
