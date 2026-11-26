/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.RingTheory.Ideal.Span
public import TauCeti.Algebra.MonoidAlgebra.RayRelPrime
public import TauCeti.Algebra.MvPolynomial.Division
public import TauCeti.Algebra.MvPolynomial.Laurent.Polynomial

/-!
# Units and relative primality between polynomial and Laurent rings

Inverting the variables via `MvPolynomial.toLaurent : MvPolynomial K R →ₐ[R] LaurentRing R K`
turns every monic monomial `monomial n 1` into a unit while preserving all divisibility relations
that are prime to the coordinate hyperplanes `Xᵢ = 0`. Over a commutative semiring `R` without zero
divisors, this file characterizes the polynomials that become units in the Laurent ring, establishes
descent and unconditional ascent of `IsRelPrime` along `MvPolynomial.toLaurent`, and transfers ray
relative primality from `AddMonoidAlgebra` to both `LaurentRing R K` and `MvPolynomial K R`.

In `LaurentRing ℤ (Fin 2)` (and in multivariable polynomial or Laurent rings of dimension at least
two), `IsRelPrime` is strictly weaker than ideal coprimality `IsCoprime`: for instance `1 + X 0`
and `1 + X 1` have only unit common divisors yet both vanish under evaluation at `(-1, -1)`, so
the ideal they span is proper.

## Main results

* `MvPolynomial.isUnit_toLaurent_iff`: over a nontrivial semiring without zero divisors,
  `toLaurent p` is a unit iff `p = monomial n r` with `r` a unit.
* `MvPolynomial.isUnit_iff_isUnit_toLaurent_and_forall_not_X_dvd`: `p` is a unit of
  `MvPolynomial K R` iff `toLaurent p` is a unit and no variable `Xᵢ` divides `p`.
* `MvPolynomial.isRelPrime_of_toLaurent`: if `toLaurent p` and `toLaurent q` are relatively prime
  and no variable `Xᵢ` divides both `p` and `q`, then `IsRelPrime p q`.
* `MvPolynomial.toLaurent_dvd_toLaurent_iff_of_forall_not_X_dvd`: when no variable divides `g`,
  `toLaurent g ∣ toLaurent p ↔ g ∣ p`.
* `MvPolynomial.isRelPrime_toLaurent` and `MvPolynomial.isRelPrime_iff_isRelPrime_toLaurent`:
  `IsRelPrime` ascends unconditionally along `toLaurent`, giving the full equivalence
  `IsRelPrime p q ↔ IsRelPrime (toLaurent p) (toLaurent q) ∧ ∀ i, ¬ (X i ∣ p ∧ X i ∣ q)`.
* `MvPolynomial.isRelPrime_prod_one_add_monomial` and
  `TauCeti.LaurentRing.isRelPrime_prod_one_add_smul_X`: relative primality of binomials and finite
  products of binomials along `ℤ`-linearly independent rays in `MvPolynomial K R` and along
  distinct variables in `LaurentRing R K`.
-/

public section

open AddMonoidAlgebra TauCeti

namespace MvPolynomial

section CommSemiring

variable {R K : Type*} [CommSemiring R] [NoZeroDivisors R]

/-- Over a nontrivial commutative semiring without zero divisors, `toLaurent p` is a unit of
`LaurentRing R K` if and only if `p` is a monomial with a unit coefficient. -/
theorem isUnit_toLaurent_iff [Nontrivial R] {p : MvPolynomial K R} :
    IsUnit (toLaurent p) ↔ ∃ (n : K →₀ ℕ) (r : R), IsUnit r ∧ p = monomial n r := by
  refine ⟨fun hu ↦ ?_, ?_⟩
  · obtain ⟨m, r, -, hr, heq⟩ := (AddMonoidAlgebra.isUnit_iff_exists_single _).mp hu
    have hm_supp : m ∈ (toLaurent p).coeff.support := by
      simpa [heq] using hr.ne_zero
    have hm_nonneg : ∀ i, 0 ≤ m i :=
      mem_range_toLaurent_iff.mp (AlgHom.mem_range_self toLaurent p) m hm_supp
    let n : K →₀ ℕ := m.mapRange Int.toNat Int.toNat_zero
    have hnm : n.mapRange Nat.cast Nat.cast_zero = m := by
      ext i
      simpa [n] using hm_nonneg i
    refine ⟨n, r, hr, toLaurent_injective ?_⟩
    rw [heq, toLaurent_monomial, hnm]
  · rintro ⟨n, r, hr, rfl⟩
    rw [toLaurent_monomial]
    exact (AddMonoidAlgebra.isUnit_single_iff _ r).mpr ⟨⟨toAddUnits _, rfl⟩, hr⟩

/-- Over a nontrivial commutative semiring without zero divisors, `p : MvPolynomial K R` is a unit
if and only if `toLaurent p` is a unit and no variable `Xᵢ` divides `p`. -/
theorem isUnit_iff_isUnit_toLaurent_and_forall_not_X_dvd [Nontrivial R] {p : MvPolynomial K R} :
    IsUnit p ↔ IsUnit (toLaurent p) ∧ ∀ i : K, ¬ X i ∣ p := by
  refine ⟨fun hp ↦ ⟨hp.map toLaurent, fun i hXi ↦ ?_⟩, fun ⟨hu, hX⟩ ↦ ?_⟩
  · have huX : IsUnit (X i : MvPolynomial K R) := isUnit_of_dvd_unit hXi hp
    have hu0 : IsUnit (0 : R) := by simpa using huX.map constantCoeff
    exact not_isUnit_zero hu0
  · obtain ⟨n, r, hr, rfl⟩ := isUnit_toLaurent_iff.mp hu
    have hn0 : n = 0 := by
      ext i
      by_contra hni
      exact hX i (X_dvd_monomial.mpr (Or.inr hni))
    rw [hn0, monomial_zero']
    exact hr.map C

/-- **Descent of relative primality from `LaurentRing` to `MvPolynomial`.** If `toLaurent p` and
`toLaurent q` are relatively prime and no variable `Xᵢ` divides both `p` and `q`, then `p` and `q`
are relatively prime in `MvPolynomial K R`. -/
theorem isRelPrime_of_toLaurent {p q : MvPolynomial K R}
    (hL : IsRelPrime (toLaurent p) (toLaurent q))
    (hX : ∀ i : K, ¬ (X i ∣ p ∧ X i ∣ q)) : IsRelPrime p q := by
  rcases subsingleton_or_nontrivial R with _ | _
  · exact fun d _ _ ↦ isUnit_of_subsingleton d
  refine fun d hdp hdq ↦ isUnit_iff_isUnit_toLaurent_and_forall_not_X_dvd.mpr
    ⟨hL (map_dvd toLaurent hdp) (map_dvd toLaurent hdq),
      fun i hXd ↦ hX i ⟨dvd_trans hXd hdp, dvd_trans hXd hdq⟩⟩

/-- **Finite products of binomials along `ℤ`-linearly independent exponent rays in `MvPolynomial`
are relatively prime.** -/
theorem isRelPrime_prod_one_add_monomial {a b : K →₀ ℕ}
    (hlin : LinearIndependent ℤ
      ![a.mapRange (Nat.cast : ℕ → ℤ) Nat.cast_zero, b.mapRange (Nat.cast : ℕ → ℤ) Nat.cast_zero])
    {κ₁ κ₂ : Type*} (s : Finset κ₁) (u : Finset κ₂) (c : κ₁ → R) (d : κ₂ → R) :
    IsRelPrime (∏ r ∈ s, (1 + monomial a (c r) : MvPolynomial K R))
      (∏ t ∈ u, (1 + monomial b (d t) : MvPolynomial K R)) := by
  rcases subsingleton_or_nontrivial R with _ | _
  · exact fun h _ _ ↦ isUnit_of_subsingleton h
  have ha0 : a ≠ 0 := fun ha ↦ by simpa [ha] using hlin.ne_zero 0
  have hconst : constantCoeff (∏ r ∈ s, (1 + monomial a (c r) : MvPolynomial K R)) ≠ 0 := by
    rw [map_prod, Finset.prod_eq_one fun r _ ↦ by classical simp [constantCoeff_monomial, ha0]]
    exact one_ne_zero
  refine isRelPrime_of_toLaurent ?_ fun i h ↦ not_X_dvd_of_constantCoeff_ne_zero hconst i h.1
  simpa only [map_prod, map_add, map_one, toLaurent_monomial] using
    AddMonoidAlgebra.isRelPrime_prod_one_add_single hlin s u c d

/-- **Binomials `1 + monomial a c` and `1 + monomial b d` along `ℤ`-linearly independent exponent
rays in `MvPolynomial` are relatively prime.** -/
theorem isRelPrime_one_add_monomial {a b : K →₀ ℕ}
    (hlin : LinearIndependent ℤ
      ![a.mapRange (Nat.cast : ℕ → ℤ) Nat.cast_zero, b.mapRange (Nat.cast : ℕ → ℤ) Nat.cast_zero])
    (c d : R) :
    IsRelPrime (1 + monomial a c : MvPolynomial K R) (1 + monomial b d : MvPolynomial K R) := by
  simpa using isRelPrime_prod_one_add_monomial hlin ({()} : Finset Unit) ({()} : Finset Unit)
    (fun _ ↦ c) (fun _ ↦ d)

end CommSemiring

/-! ### Ascent of relative primality from `MvPolynomial` to `LaurentRing` -/

section Ascent

variable {R K : Type*} [CommSemiring R] [NoZeroDivisors R]

/-- If no variable `Xᵢ` divides `g`, divisibility by `toLaurent g` in `LaurentRing R K` descends to
divisibility by `g` in `MvPolynomial K R`. -/
theorem dvd_of_toLaurent_dvd_of_forall_not_X_dvd {g p : MvPolynomial K R}
    (hX : ∀ i : K, ¬ X i ∣ g) (hdvd : toLaurent g ∣ toLaurent p) : g ∣ p := by
  obtain ⟨u, hu⟩ := hdvd
  obtain ⟨m, u₁, hu₁, -⟩ := LaurentRing.exists_mul_toLaurent_monomial u
  have hdvd_mon : g ∣ monomial m 1 * p := ⟨u₁, toLaurent_injective <| by
    rw [map_mul, mul_comm _ (toLaurent p), hu, mul_assoc, hu₁, map_mul]⟩
  exact (dvd_monomial_one_mul_iff_of_forall_not_X_dvd hX).mp hdvd_mon

/-- When no variable `Xᵢ` divides `g`, `toLaurent` reflects and preserves divisibility by `g`. -/
theorem toLaurent_dvd_toLaurent_iff_of_forall_not_X_dvd {g p : MvPolynomial K R}
    (hX : ∀ i : K, ¬ X i ∣ g) : toLaurent g ∣ toLaurent p ↔ g ∣ p :=
  ⟨dvd_of_toLaurent_dvd_of_forall_not_X_dvd hX, map_dvd toLaurent⟩

/-- **Unconditional ascent of relative primality along `toLaurent`.** Over a commutative semiring
without zero divisors, relatively prime polynomials remain relatively prime in the Laurent ring. -/
theorem isRelPrime_toLaurent {p q : MvPolynomial K R} (hpq : IsRelPrime p q) :
    IsRelPrime (toLaurent p) (toLaurent q) := by
  rcases subsingleton_or_nontrivial R with _ | _
  · exact fun f _ _ ↦ isUnit_of_subsingleton f
  intro f hfp hfq
  by_cases hf0 : f = 0
  · subst hf0
    exact absurd (hpq (toLaurent_eq_zero.mp (zero_dvd_iff.mp hfp) ▸ dvd_rfl)
      (toLaurent_eq_zero.mp (zero_dvd_iff.mp hfq) ▸ dvd_rfl)) not_isUnit_zero
  obtain ⟨n, g₀, hfg₀, -⟩ := LaurentRing.exists_mul_toLaurent_monomial f
  obtain ⟨vn, hvn⟩ := isUnit_toLaurent_monomial_one (R := R) n
  have hg₀0 : g₀ ≠ 0 := fun h0 ↦ hf0 <|
    (mul_eq_zero.mp (by rwa [h0, map_zero, ← hvn] at hfg₀)).resolve_right vn.ne_zero
  obtain ⟨k, g, rfl, hgX⟩ := exists_eq_monomial_mul_and_forall_not_X_dvd hg₀0
  let vk : LaurentRing R K := toLaurent (monomial k (1 : R))
  let winv : LaurentRing R K := ((vn⁻¹ : (LaurentRing R K)ˣ) : LaurentRing R K)
  have hf_eq : f = vk * toLaurent g * winv := by
    rw [← mul_one f, ← Units.mul_inv vn, ← mul_assoc, hvn, hfg₀, map_mul]
  have hg_dvd_f : toLaurent g ∣ f := ⟨vk * winv, by rw [hf_eq, mul_assoc, mul_left_comm]⟩
  have hug : IsUnit (toLaurent g) :=
    (hpq (dvd_of_toLaurent_dvd_of_forall_not_X_dvd hgX (dvd_trans hg_dvd_f hfp))
      (dvd_of_toLaurent_dvd_of_forall_not_X_dvd hgX (dvd_trans hg_dvd_f hfq))).map toLaurent
  exact hf_eq ▸ (((isUnit_toLaurent_monomial_one k).mul hug).mul vn⁻¹.isUnit)

/-- **Characterization of polynomial relative primality via `LaurentRing`.** Over a nontrivial
commutative semiring without zero divisors, two polynomials `p` and `q` are relatively prime if and
only if `toLaurent p` and `toLaurent q` are relatively prime and no variable `Xᵢ` divides both `p`
and `q`. -/
theorem isRelPrime_iff_isRelPrime_toLaurent [Nontrivial R] {p q : MvPolynomial K R} :
    IsRelPrime p q ↔ IsRelPrime (toLaurent p) (toLaurent q) ∧ ∀ i : K, ¬ (X i ∣ p ∧ X i ∣ q) :=
  ⟨fun h ↦ ⟨isRelPrime_toLaurent h, fun _ ⟨hp, hq⟩ ↦
      not_isUnit_zero (by simpa using (h hp hq).map constantCoeff : IsUnit (0 : R))⟩,
    fun ⟨hL, hX⟩ ↦ isRelPrime_of_toLaurent hL hX⟩

end Ascent

end MvPolynomial

namespace TauCeti.LaurentRing

section CoordinateRays

variable {R K : Type*} [CommSemiring R] [NoZeroDivisors R]

/-- Finite products of linear binomials in distinct Laurent variables are relatively prime. -/
theorem isRelPrime_prod_one_add_smul_X {i j : K} (hij : i ≠ j)
    {κ₁ κ₂ : Type*} (s : Finset κ₁) (u : Finset κ₂) (c : κ₁ → R) (d : κ₂ → R) :
    IsRelPrime (∏ r ∈ s, (1 + c r • X i : LaurentRing R K))
      (∏ t ∈ u, (1 + d t • X j : LaurentRing R K)) := by
  have hlin : LinearIndependent ℤ ![Finsupp.single i (1 : ℤ), Finsupp.single j (1 : ℤ)] := by
    have h := (Finsupp.basisSingleOne (ι := K) (R := ℤ)).linearIndependent.comp ![i, j]
      fun a b hab ↦ by fin_cases a <;> fin_cases b <;> simp_all
    convert h using 1
    ext k
    fin_cases k <;> simp [Finsupp.coe_basisSingleOne]
  simpa only [X_def, smul_single, smul_eq_mul, mul_one] using
    AddMonoidAlgebra.isRelPrime_prod_one_add_single hlin s u c d

/-- Linear binomials `1 + c • X i` and `1 + d • X j` in distinct Laurent variables are relatively
prime. -/
theorem isRelPrime_one_add_smul_X {i j : K} (hij : i ≠ j) (c d : R) :
    IsRelPrime (1 + c • X i : LaurentRing R K) (1 + d • X j : LaurentRing R K) := by
  simpa using isRelPrime_prod_one_add_smul_X hij ({()} : Finset Unit) ({()} : Finset Unit)
    (fun _ ↦ c) (fun _ ↦ d)

/-- `1 + X i` and `1 + X j` are relatively prime in `LaurentRing R K` whenever `i ≠ j`. -/
theorem isRelPrime_one_add_X {i j : K} (hij : i ≠ j) :
    IsRelPrime (1 + X i : LaurentRing R K) (1 + X j : LaurentRing R K) := by
  simpa using isRelPrime_one_add_smul_X (R := R) hij 1 1

end CoordinateRays

/-! ### Checks -/

example : IsRelPrime (1 + X 0 : LaurentRing ℤ (Fin 2)) (1 + X 1) := isRelPrime_one_add_X (by decide)

/-- `1 + X 0` and `1 + X 1` are `IsRelPrime` in `LaurentRing ℤ (Fin 2)` yet span a proper ideal. -/
example : Ideal.span ({1 + X 0, 1 + X 1} : Set (LaurentRing ℤ (Fin 2))) ≠ ⊤ := fun htop ↦ by
  let φ : LaurentRing ℤ (Fin 2) →ₐ[ℤ] ℤ := aeval fun _ ↦ (-1 : ℤˣ)
  have hle : Ideal.span ({1 + X 0, 1 + X 1} : Set (LaurentRing ℤ (Fin 2))) ≤
      RingHom.ker φ.toRingHom := Ideal.span_le.mpr <| by rintro p (rfl | rfl) <;> simp [φ]
  have h1 : (1 : LaurentRing ℤ (Fin 2)) ∈ RingHom.ker φ.toRingHom :=
    hle (htop.symm ▸ Submodule.mem_top)
  simp [φ] at h1

example : ¬ IsRelPrime (1 + X 0 : LaurentRing ℤ (Fin 2)) (1 + X 0 ^ 3) := fun hrel ↦ by
  have hu := (hrel dvd_rfl ⟨1 - X 0 + X 0 ^ 2, by ring⟩).map (aeval fun _ ↦ (-1 : ℤˣ))
  simp at hu

end TauCeti.LaurentRing
