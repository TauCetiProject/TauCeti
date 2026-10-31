/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Polynomial.Eisenstein.Basic

/-!
# Integrally closed algebras and subrings

For a field `k` and a nontrivial commutative `k`-algebra `A`, being integrally closed in `A`
means every element of `A` algebraic over `k` is a constant. An algebraically closed field is
integrally closed in every domain algebra.

If `R` is integrally closed in `A`, divisibility in `R` can be tested on `n`-th powers by any
element of `R` that becomes a unit in `A`: a quotient `b / a` in `A` whose `n`-th power lies in `R`
is integral over `R`. This is the non-domain form of Mathlib's `IsIntegrallyClosed.pow_dvd_pow_iff`.

If `x ∈ R` is a nonzerodivisor and `R ⧸ (x)` is reduced, then `R` is integrally closed in its
localization `R[1/x]`: if `a / x` is integral over `R` then `a ^ n` is divisible by `x`, so `a` is,
and one removes the powers of `x` from a denominator one at a time. For instance, this applies to
the root `y` of `A[y] ⧸ (y ^ e - f)` for `e ≥ 1`, a nonzerodivisor `f` and a reduced `A ⧸ (f)`:
the quotient by `y` is `A ⧸ (f)`.

If a subring `S` of `B` is integrally closed in `B`, then its preimage under a ring homomorphism
`f : A → B` is integrally closed in `A`: an element of `A` integral over the preimage is sent by
`f` to an element integral over `S`, which therefore lies in `S`.

## Main results

* `TauCeti.isIntegrallyClosedIn_iff_forall_isAlgebraic`: the elementwise criterion for a field
  to be integrally closed in a nontrivial commutative algebra.
* `TauCeti.isIntegrallyClosedIn_of_isAlgClosed`: an algebraically closed field is integrally
  closed in every domain algebra.
* `IsIntegrallyClosedIn.pow_dvd_pow_iff`: for `a ∈ R` invertible in `A` and `n ≠ 0`,
  `a ^ n ∣ b ^ n ↔ a ∣ b` in `R`.
* `IsIntegrallyClosedIn.of_ringEquiv`: transport along a semilinear ring isomorphism.
* `IsIntegrallyClosedIn.of_isLocalization_of_le_powers`: `R` is integrally closed in its
  localization at any submonoid of the powers of a nonzerodivisor `x` with `R ⧸ (x)` reduced.
* `IsIntegrallyClosedIn.of_isLocalization_away`: the case of the localization `R[1/x]`.
* `Subring.isIntegrallyClosedIn_comap`: the preimage of an integrally closed subring is integrally
  closed.
* `Subring.mem_of_pow_mem_of_isIntegrallyClosedIn`: a subring integrally closed in `A` contains
  every element some positive power of which it contains.
-/

public section

namespace TauCeti

variable {k A : Type*} [Field k] [CommRing A] [Algebra k A]

/-- A field `k` is integrally closed in a nontrivial commutative `k`-algebra `A` exactly when
every element of `A` algebraic over `k` lies in the image of `k`. -/
theorem isIntegrallyClosedIn_iff_forall_isAlgebraic [Nontrivial A] :
    IsIntegrallyClosedIn k A ↔ ∀ x : A, IsAlgebraic k x → ∃ c : k, algebraMap k A c = x := by
  constructor
  · intro h x hx
    exact (isIntegrallyClosedIn_iff.mp h).2 hx.isIntegral
  · intro h
    exact isIntegrallyClosedIn_iff.mpr ⟨(algebraMap k A).injective, fun hx ↦ h _ hx.isAlgebraic⟩

/-- An algebraically closed field is integrally closed in every domain algebra. -/
theorem isIntegrallyClosedIn_of_isAlgClosed [IsAlgClosed k] [IsDomain A] :
    IsIntegrallyClosedIn k A :=
  isIntegrallyClosedIn_iff.mpr ⟨(algebraMap k A).injective, fun {z} hz ↦
    minpoly.mem_range_of_degree_eq_one k z
      (IsAlgClosed.degree_eq_one_of_irreducible k (minpoly.irreducible hz))⟩

end TauCeti

namespace IsIntegrallyClosedIn

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [IsIntegrallyClosedIn R A]

/-- If `R` is integrally closed in `A` and `a ∈ R` is a unit in `A`, then for `n ≠ 0`,
`a ^ n` divides `b ^ n` in `R` exactly when `a` divides `b` in `R`. Compare
`IsIntegrallyClosed.pow_dvd_pow_iff`, which asks `R` to be a domain integrally closed in its
fraction field. -/
theorem pow_dvd_pow_iff {n : ℕ} (hn : n ≠ 0) {a b : R} (ha : IsUnit (algebraMap R A a)) :
    a ^ n ∣ b ^ n ↔ a ∣ b := by
  refine ⟨fun ⟨c, hc⟩ ↦ ?_, fun h ↦ pow_dvd_pow_of_dvd h n⟩
  obtain ⟨u, hu⟩ := ha
  have hpow : (algebraMap R A b * ↑u⁻¹) ^ n = algebraMap R A c := by
    rw [mul_pow, ← map_pow, hc]
    simp [← hu, mul_right_comm, ← mul_pow]
  obtain ⟨d, hd⟩ := exists_algebraMap_eq_of_isIntegral_pow (Nat.pos_of_ne_zero hn)
    (hpow ▸ isIntegral_algebraMap)
  refine ⟨d, IsIntegralClosure.algebraMap_injective R R A ?_⟩
  simp [hd, ← hu, mul_left_comm (u : A)]

omit [IsIntegrallyClosedIn R A] in
/-- **Integral closedness is invariant under semilinear isomorphisms**: if `τ : A ≃+* B` carries
the image of `R` onto the image of `S` along `σ : R ≃+* S`, and `R` is integrally closed in `A`,
then `S` is integrally closed in `B`. Over the identity of `R` this is
`AlgEquiv.isIntegrallyClosedIn`. -/
theorem of_ringEquiv {S B : Type*} [CommRing S] [CommRing B] [Algebra S B]
    (h : IsIntegrallyClosedIn R A) (σ : R ≃+* S) (τ : A ≃+* B)
    (hτ : ∀ r, τ (algebraMap R A r) = algebraMap S B (σ r)) : IsIntegrallyClosedIn S B := by
  obtain ⟨hinj, hint⟩ := isIntegrallyClosedIn_iff.mp h
  have hsymm (s : S) : τ.symm (algebraMap S B s) = algebraMap R A (σ.symm s) :=
    τ.symm_apply_eq.mpr (by rw [hτ, σ.apply_symm_apply])
  refine isIntegrallyClosedIn_iff.mpr ⟨fun s t hst ↦ σ.symm.injective (hinj ?_), fun {x} hx ↦ ?_⟩
  · rw [← hsymm, ← hsymm, hst]
  · obtain ⟨r, hr⟩ := hint (hx.map_of_comp_eq (σ.symm : S →+* R) (τ.symm : B →+* A)
      (RingHom.ext fun s ↦ (hsymm s).symm))
    exact ⟨σ r, by rw [← hτ, hr, RingEquiv.coe_toRingHom, τ.apply_symm_apply]⟩

omit [IsIntegrallyClosedIn R A] in
/-- **A ring is integrally closed in its localization at a nonzerodivisor with reduced quotient.**
If `x ∈ R` is a nonzerodivisor and `R ⧸ (x)` is reduced, then `R` is integrally closed in its
localization `A` at any submonoid `M` of the powers of `x`, such as the powers of `x ^ e`. -/
theorem of_isLocalization_of_le_powers {x : R} (hx : x ∈ nonZeroDivisors R)
    [IsReduced (R ⧸ Ideal.span {x})] (M : Submonoid R) (hM : M ≤ Submonoid.powers x)
    [IsLocalization M A] : IsIntegrallyClosedIn R A := by
  have hM₀ : M ≤ nonZeroDivisors R := hM.trans (Submonoid.powers_le.mpr hx)
  have hinj : Function.Injective (algebraMap R A) := IsLocalization.injective A hM₀
  have hxA : algebraMap R A x ∈ nonZeroDivisors A :=
    IsLocalization.map_nonZeroDivisors_le M A ⟨x, hx, rfl⟩
  -- `x` divides `a` whenever `a / x` is integral over `R`, since `(x)` is a radical ideal
  have hdvd {w : A} (hw : IsIntegral R w) {a : R} (ha : algebraMap R A x * w = algebraMap R A a) :
      x ∣ a := by
    obtain ⟨p, hp, hpw⟩ := hw
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]
    refine IsNilpotent.eq_zero ⟨p.natDegree, ?_⟩
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    exact Polynomial.dvd_pow_natDegree_of_eval₂_eq_zero hinj hp x a w hpw ha
  refine isIntegrallyClosedIn_iff.mpr ⟨hinj, fun {z} hz ↦ ?_⟩
  obtain ⟨⟨a, m⟩, ha⟩ := IsLocalization.surj M z
  obtain ⟨n, hn⟩ := hM m.2
  rw [← hn] at ha
  clear hn
  -- induction on the exponent of the denominator `x ^ n` of `z`
  induction n generalizing a with
  | zero => exact ⟨a, by simpa using ha.symm⟩
  | succ n ih =>
    obtain ⟨c, rfl⟩ := hdvd (hz.mul (isIntegral_algebraMap (x := x ^ n)))
      (by rw [← ha]; simp only [map_mul, map_pow, pow_succ]; ring)
    refine ih c ?_
    rw [← mul_cancel_left_mem_nonZeroDivisors hxA, ← map_mul, ← ha]
    simp only [map_mul, map_pow, pow_succ]
    ring

omit [IsIntegrallyClosedIn R A] in
/-- If `x ∈ R` is a nonzerodivisor and `R ⧸ (x)` is reduced, then `R` is integrally closed in its
localization away from `x`. -/
theorem of_isLocalization_away {x : R} (hx : x ∈ nonZeroDivisors R)
    [IsReduced (R ⧸ Ideal.span {x})] [IsLocalization.Away x A] : IsIntegrallyClosedIn R A :=
  of_isLocalization_of_le_powers hx (Submonoid.powers x) le_rfl

end IsIntegrallyClosedIn

namespace Subring

variable {A B : Type*} [CommRing A] [CommRing B]

/-- **The preimage of an integrally closed subring is integrally closed**: if `S` is integrally
closed in `B`, then `S.comap f` is integrally closed in `A` for every ring homomorphism
`f : A →+* B`. -/
instance isIntegrallyClosedIn_comap (f : A →+* B) (S : Subring B) [IsIntegrallyClosedIn S B] :
    IsIntegrallyClosedIn (S.comap f) A :=
  Subring.isIntegrallyClosedIn_iff.mpr fun _ hx ↦ (Subring.isIntegrallyClosedIn_iff (S := S)).mp
    inferInstance (hx.map_of_comp_eq (f.restrict _ S fun _ hy ↦ hy) f rfl)

/-- A subring `S` integrally closed in `A` contains every element `a` some positive power of which
lies in `S`, as `a` is then integral over `S`. -/
theorem mem_of_pow_mem_of_isIntegrallyClosedIn {S : Subring A} [IsIntegrallyClosedIn S A] {a : A}
    {n : ℕ} (hn : 0 < n) (ha : a ^ n ∈ S) : a ∈ S := by
  have hpow : IsIntegral S (a ^ n) := isIntegral_algebraMap (R := S) (x := (⟨a ^ n, ha⟩ : S))
  obtain ⟨y, hy⟩ := IsIntegrallyClosedIn.exists_algebraMap_eq_of_isIntegral_pow hn hpow
  exact hy ▸ y.2

end Subring
