/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Etale.IndEtale
public import TauCeti.RingTheory.Etale.Normal
import Mathlib.RingTheory.Polynomial.UniversalFactorizationRing
import TauCeti.RingTheory.IntegralClosure.IntegrallyClosed
import TauCeti.RingTheory.Polynomial.ScaleRoots

/-!
# Normality of local rings that are ind-étale over a normal ring

Let `A` be a local ring that is ind-étale over a ring `R`, and let `𝔭` be the prime of `R` under
the maximal ideal of `A`. If the local ring `R_𝔭` is an integrally closed domain, then so is `A`.
Henselizations and strict henselizations of a local ring are local and ind-étale over it, so they
are integrally closed domains when the local ring is (Stacks, Lemma 10.156.6 (06DI)).

The argument is stagewise. Write `A` as a filtered colimit of étale `R`-algebras `D`, with maps
`g : D → A`, and let `𝔮 = g⁻¹(𝔪_A)`. Since `g` is an `R`-algebra map, `𝔮` lies over `𝔭`, so the
local ring `D_𝔮` is an integrally closed domain (Stacks, Lemma 10.163.9 (033C), in the form
`TauCeti.Algebra.Etale.isDomain_localization_atPrime_of_localization_under`). Elements of `D`
outside `𝔮` become units in `A`, so `g` factors through `D_𝔮`. A relation `a * b = 0`, or an
equation of integral dependence of `a / b` over `A`, is a finite polynomial condition on finitely
many elements, so it already holds at some stage `D`
(`TauCeti.Algebra.IndEtale.exists_etale_aeval_eq_zero`); it is then resolved in `D_𝔮` and the
resolution is carried to `A`.

## Main results

* `TauCeti.Algebra.IndEtale.isDomain_of_isLocalRing`: a local ring ind-étale over `R` is a domain
  when `R_𝔭` is an integrally closed domain.
* `TauCeti.Algebra.IndEtale.isIntegrallyClosed_of_isLocalRing`: under the same hypotheses, it is
  integrally closed.

## References

* [Stacks Project, Lemma 10.156.6 (06DI)](https://stacks.math.columbia.edu/tag/06DI)
* [Stacks Project, Lemma 10.163.9 (033C)](https://stacks.math.columbia.edu/tag/033C)
-/

public section

open IsLocalRing Polynomial

universe u

namespace TauCeti.Algebra.IndEtale

variable {R A : Type u} [CommRing R] [CommRing A] [_root_.Algebra R A] [IsLocalRing A]

section Stage

variable {D : Type*} [CommRing D] [_root_.Algebra R D] (g : D →ₐ[R] A)

/-- The map `g : D → A` into a local ring sends the complement of `g⁻¹(𝔪_A)` to units. -/
private theorem isUnit_of_mem_primeCompl (s : ((maximalIdeal A).comap g).primeCompl) :
    IsUnit (g s) :=
  notMem_maximalIdeal.mp s.property

/-- The map `D_𝔮 → A` through which `g : D → A` factors, for `𝔮 = g⁻¹(𝔪_A)`. -/
private noncomputable def localizationLift :
    Localization.AtPrime ((maximalIdeal A).comap g) →+* A :=
  IsLocalization.lift (isUnit_of_mem_primeCompl g)

private theorem localizationLift_algebraMap (d : D) :
    localizationLift g (algebraMap D _ d) = g d :=
  IsLocalization.lift_eq _ d

variable [_root_.Algebra.Etale R D] [IsDomain (Localization.AtPrime ((maximalIdeal A).under R))]
  [IsIntegrallyClosed (Localization.AtPrime ((maximalIdeal A).under R))]

/-- For an étale `R`-algebra `D` with an `R`-algebra map `g : D → A`, the localization of `D` at
`g⁻¹(𝔪_A)` is an integrally closed domain when that of `R` at the prime under `𝔪_A` is. -/
private theorem isDomain_and_isIntegrallyClosed_localization :
    IsDomain (Localization.AtPrime ((maximalIdeal A).comap g)) ∧
      IsIntegrallyClosed (Localization.AtPrime ((maximalIdeal A).comap g)) := by
  -- The prime `g⁻¹(𝔪_A)` of `D` lies over the prime of `R` under `𝔪_A`.
  have h : ((maximalIdeal A).comap g).under R = (maximalIdeal A).under R := by
    ext r
    simp [Ideal.under]
  -- Transport the hypotheses on the localization of `R` along `h`.
  have transport (P : Ideal R) [P.IsPrime] (hP : P = (maximalIdeal A).under R) :
      IsDomain (Localization.AtPrime P) ∧ IsIntegrallyClosed (Localization.AtPrime P) := by
    subst hP
    exact ⟨inferInstance, inferInstance⟩
  obtain ⟨_, _⟩ := transport _ h
  exact ⟨Etale.isDomain_localization_atPrime_of_localization_under R _,
    Etale.isIntegrallyClosed_localization_atPrime_of_localization_under R _⟩

/-- **Integral dependence is resolved at an étale stage.** Let `g : D → A` be an `R`-algebra map
from an étale `R`-algebra. If `u / v` is a root of a monic polynomial `q` over `D`, in the
denominator-free form `(q.scaleRoots v)(u) = 0`, then `g v` divides `g u` in `A`: `v` divides `u`
in the normal domain `D_𝔮`, `𝔮 = g⁻¹(𝔪_A)`, through which `g` factors. -/
private theorem map_dvd_map_of_eval_scaleRoots_eq_zero {q : D[X]} (hq : q.Monic) {u v : D}
    (h : (q.scaleRoots v).eval u = 0) : g v ∣ g u := by
  obtain ⟨_, _⟩ := isDomain_and_isIntegrallyClosed_localization g
  let φ := algebraMap D (Localization.AtPrime ((maximalIdeal A).comap g))
  have hL : ((q.map φ).scaleRoots (φ v)).eval (φ u) = 0 := by
    rw [← map_eval_scaleRoots _ (hq.natDegree_map φ), h, map_zero]
  simpa only [φ, localizationLift_algebraMap] using
    map_dvd (localizationLift g) (IsIntegrallyClosed.dvd_of_eval_scaleRoots_eq_zero (hq.map φ) hL)

end Stage

/-- **Integral dependence descends to an étale stage.** If `a / b` is a root of a monic polynomial
`p` over `A`, in the denominator-free form `(p.scaleRoots b)(a) = 0`, then so is `u / v` for a monic
`q` over an étale `R`-algebra `D` with an `R`-algebra map `g : D → A` sending `u` to `a` and `v`
to `b`. The equation is a polynomial condition on `a`, `b` and the lower coefficients of `p`. -/
private theorem exists_etale_eval_scaleRoots_eq_zero [IndEtale R A] {p : A[X]} (hp : p.Monic)
    {a b : A} (hab : (p.scaleRoots b).eval a = 0) :
    ∃ (D : Type u) (_ : CommRing D) (_ : _root_.Algebra R D) (_ : _root_.Algebra.Etale R D)
      (g : D →ₐ[R] A) (q : D[X]) (u v : D),
      q.Monic ∧ g u = a ∧ g v = b ∧ (q.scaleRoots v).eval u = 0 := by
  -- This is the equation `P = 0` in the lower coefficients of `p` and in `a` and `b`, where `P`
  -- is built from the free monic polynomial `Q` of degree `n`.
  set n := p.natDegree
  let Q : (MvPolynomial (Fin n ⊕ Fin 2) R)[X] :=
    (freeMonic R n).map (MvPolynomial.rename Sum.inl).toRingHom
  have hQ : Q.Monic := (monic_freeMonic R n).map _
  let P := (Q.scaleRoots (MvPolynomial.X (Sum.inr 1))).eval (MvPolynomial.X (Sum.inr 0))
  have hP {T : Type u} [CommRing T] [Nontrivial T] (φ : MvPolynomial (Fin n ⊕ Fin 2) R →+* T) :
      φ P = ((Q.map φ).scaleRoots (φ (MvPolynomial.X (Sum.inr 1)))).eval
        (φ (MvPolynomial.X (Sum.inr 0))) :=
    map_eval_scaleRoots φ (hQ.natDegree_map φ) _ _
  let x : Fin n ⊕ Fin 2 → A := Sum.elim (fun i ↦ p.coeff i) ![a, b]
  have hx : MvPolynomial.aeval x P = 0 := by
    -- `Q` specializes to `p`, which is the universal property of the free monic polynomial.
    have hpQ : Q.map (MvPolynomial.aeval x).toRingHom = p := by
      rw [Polynomial.map_map, AlgHom.toRingHom_eq_coe, AlgHom.toRingHom_eq_coe,
        ← AlgHom.comp_toRingHom, MvPolynomial.aeval_comp_rename]
      -- Compare coefficients: below degree `n` they are the variables, sent to `p.coeff k`; at
      -- `n` it is `1`, and above `n` it is `0`.
      ext k
      rw [coeff_map, coeff_freeMonic]
      split_ifs with hk hk'
      · simp [x]
      · simp [hk', n, hp.coeff_natDegree]
      · simp [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_ne (not_lt.mp hk) (Ne.symm hk'))]
    have h := hP (MvPolynomial.aeval x).toRingHom
    rw [hpQ] at h
    simpa [x, hab] using h
  -- The equation holds at an étale stage `g : D → A`.
  obtain ⟨D, _, _, _, g, y, hy, hPy⟩ := exists_etale_aeval_eq_zero x P hx
  have : Nontrivial D := g.toRingHom.domain_nontrivial
  have hrel := hP (MvPolynomial.aeval y).toRingHom
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_X] at hrel
  have hgy (i : Fin n ⊕ Fin 2) : g (y i) = x i := congrFun hy i
  exact ⟨D, inferInstance, inferInstance, inferInstance, g, Q.map (MvPolynomial.aeval y).toRingHom,
    y (Sum.inr 0), y (Sum.inr 1), hQ.map _, by simpa [x] using hgy (Sum.inr 0),
    by simpa [x] using hgy (Sum.inr 1), hrel.symm.trans hPy⟩

variable [IndEtale R A] [IsDomain (Localization.AtPrime ((maximalIdeal A).under R))]
  [IsIntegrallyClosed (Localization.AtPrime ((maximalIdeal A).under R))]

variable (R A) in
include R in
/-- **Local rings ind-étale over a normal ring are domains.** Let `A` be a local ring which is
ind-étale over `R`. If the localization of `R` at the prime under the maximal ideal of `A` is an
integrally closed domain, then `A` is a domain. -/
@[stacks 06DI "domain part, for local rings ind-étale over a normal ring"]
theorem isDomain_of_isLocalRing : IsDomain A := by
  have : NoZeroDivisors A := ⟨fun {a b} hab ↦ by
    -- The relation `a * b = 0` already holds at an étale stage `g : D → A`.
    obtain ⟨D, _, _, _, g, y, hy, hP⟩ := exists_etale_aeval_eq_zero (R := R) ![a, b]
      (MvPolynomial.X 0 * MvPolynomial.X 1) (by simpa using hab)
    obtain ⟨_, -⟩ := isDomain_and_isIntegrallyClosed_localization g
    -- In the domain `D_𝔮` one of the two factors vanishes, and `g` factors through `D_𝔮`.
    have hL : algebraMap D (Localization.AtPrime ((maximalIdeal A).comap g)) (y 0) *
        algebraMap D _ (y 1) = 0 := by
      rw [← map_mul, show y 0 * y 1 = 0 by simpa using hP, map_zero]
    rcases mul_eq_zero.mp hL with h | h
    · left
      rw [← show g (y 0) = a from congrFun hy 0, ← localizationLift_algebraMap g, h, map_zero]
    · right
      rw [← show g (y 1) = b from congrFun hy 1, ← localizationLift_algebraMap g, h, map_zero]⟩
  exact NoZeroDivisors.to_isDomain A

variable (R A) in
include R in
/-- **Local rings ind-étale over a normal ring are integrally closed.** Let `A` be a local ring
which is ind-étale over `R`. If the localization of `R` at the prime under the maximal ideal of
`A` is an integrally closed domain, then `A` is an integrally closed domain. -/
@[stacks 06DI "for local rings ind-étale over a normal ring"]
theorem isIntegrallyClosed_of_isLocalRing : IsIntegrallyClosed A := by
  have := isDomain_of_isLocalRing R A
  refine (isIntegrallyClosed_iff (FractionRing A)).mpr fun {x} ⟨p, hp, hpx⟩ ↦ ?_
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := A) x
  -- Clearing denominators in `p (a / b) = 0` gives `(p.scaleRoots b)(a) = 0` in `A`.
  have hab : (p.scaleRoots b).eval a = 0 := by
    apply IsFractionRing.injective A (FractionRing A)
    rw [← eval₂_hom, map_zero]
    exact scaleRoots_eval₂_eq_zero_of_eval₂_div_eq_zero (IsFractionRing.injective A _) hpx hb
  -- The equation already holds at an étale stage `g : D → A`, where it is resolved.
  obtain ⟨D, _, _, _, g, q, u, v, hq, rfl, rfl, huv⟩ :=
    exists_etale_eval_scaleRoots_eq_zero (R := R) hp hab
  obtain ⟨c, hc⟩ := map_dvd_map_of_eval_scaleRoots_eq_zero g hq huv
  refine ⟨c, ?_⟩
  rw [eq_div_iff (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb), ← map_mul, hc,
    mul_comm]

end TauCeti.Algebra.IndEtale
