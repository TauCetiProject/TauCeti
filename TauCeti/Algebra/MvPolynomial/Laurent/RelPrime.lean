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
that are prime to the coordinate hyperplanes `Xᵢ = 0`. Over a coefficient ring `R` without zero
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

variable {R K : Type*} [CommSemiring R]

/-- Every monic polynomial monomial becomes a unit in `LaurentRing R K`. -/
theorem isUnit_toLaurent_monomial_one (n : K →₀ ℕ) :
    IsUnit (toLaurent (monomial n (1 : R))) := by
  let m : K →₀ ℤ := n.mapRange Nat.cast Nat.cast_zero
  refine isUnit_iff_exists.mpr ⟨single (-m) 1, ?_, ?_⟩
  · simp [m, single_mul_single, AddMonoidAlgebra.one_def]
  · simp [m, single_mul_single, AddMonoidAlgebra.one_def]

section NoZeroDivisors

variable [NoZeroDivisors R]

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
  · intro d _ _
    exact isUnit_of_subsingleton d
  intro d hdp hdq
  have huL : IsUnit (toLaurent d) := hL (map_dvd toLaurent hdp) (map_dvd toLaurent hdq)
  exact isUnit_iff_isUnit_toLaurent_and_forall_not_X_dvd.mpr
    ⟨huL, fun i hXd ↦ hX i ⟨dvd_trans hXd hdp, dvd_trans hXd hdq⟩⟩

/-- Specialization of `MvPolynomial.isRelPrime_of_toLaurent` when no variable divides `p`. -/
theorem isRelPrime_of_toLaurent_of_forall_not_X_dvd_left {p q : MvPolynomial K R}
    (hL : IsRelPrime (toLaurent p) (toLaurent q))
    (hp : ∀ i : K, ¬ X i ∣ p) : IsRelPrime p q :=
  isRelPrime_of_toLaurent hL fun i h ↦ hp i h.1

/-- Specialization of `MvPolynomial.isRelPrime_of_toLaurent` when `p` has nonzero constant term. -/
theorem isRelPrime_of_toLaurent_of_constantCoeff_ne_zero_left {p q : MvPolynomial K R}
    (hL : IsRelPrime (toLaurent p) (toLaurent q))
    (hp : constantCoeff p ≠ 0) : IsRelPrime p q :=
  isRelPrime_of_toLaurent_of_forall_not_X_dvd_left hL (not_X_dvd_of_constantCoeff_ne_zero hp)

/-- **Finite products of binomials along `ℤ`-linearly independent exponent rays in `MvPolynomial`
are relatively prime.** -/
theorem isRelPrime_prod_one_add_monomial {a b : K →₀ ℕ}
    (hlin : LinearIndependent ℤ
      ![a.mapRange (Nat.cast : ℕ → ℤ) Nat.cast_zero, b.mapRange (Nat.cast : ℕ → ℤ) Nat.cast_zero])
    {κ₁ κ₂ : Type*} (s : Finset κ₁) (u : Finset κ₂) (c : κ₁ → R) (d : κ₂ → R) :
    IsRelPrime (∏ r ∈ s, (1 + monomial a (c r) : MvPolynomial K R))
      (∏ t ∈ u, (1 + monomial b (d t) : MvPolynomial K R)) := by
  rcases subsingleton_or_nontrivial R with _ | _
  · intro h _ _
    exact isUnit_of_subsingleton h
  have ha0 : a ≠ 0 := by
    intro ha
    have h0 : a.mapRange (Nat.cast : ℕ → ℤ) Nat.cast_zero ≠ 0 := by simpa using hlin.ne_zero 0
    simp [ha] at h0
  have hconst : constantCoeff (∏ r ∈ s, (1 + monomial a (c r) : MvPolynomial K R)) ≠ 0 := by
    classical
    rw [map_prod, Finset.prod_congr rfl fun r _ ↦ ?_, Finset.prod_const_one]
    · exact one_ne_zero
    · simp [constantCoeff_monomial, ha0]
  refine isRelPrime_of_toLaurent_of_constantCoeff_ne_zero_left ?_ hconst
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

end NoZeroDivisors

end CommSemiring

/-! ### Ascent of relative primality from `MvPolynomial` to `LaurentRing` -/

section CommRing

variable {R K : Type*} [CommRing R] [NoZeroDivisors R]

/-- If no variable `Xᵢ` divides `g`, divisibility by `toLaurent g` in `LaurentRing R K` descends to
divisibility by `g` in `MvPolynomial K R`. -/
theorem dvd_of_toLaurent_dvd_of_forall_not_X_dvd {g p : MvPolynomial K R}
    (hX : ∀ i : K, ¬ X i ∣ g) (hdvd : toLaurent g ∣ toLaurent p) : g ∣ p := by
  obtain ⟨u, hu⟩ := hdvd
  obtain ⟨m, u₁, hu₁, -⟩ := LaurentRing.exists_mul_toLaurent_monomial u
  have hmul : toLaurent (monomial m 1 * p) = toLaurent (g * u₁) := by
    rw [map_mul, mul_comm _ (toLaurent p), hu, mul_assoc, hu₁, map_mul]
  have hdvd_mon : g ∣ monomial m 1 * p := ⟨u₁, toLaurent_injective hmul⟩
  obtain ⟨k, r, -, hrp, hgr⟩ := dvd_monomial_mul_iff_exists.mp hdvd_mon
  have hk0 : k = 0 := by
    ext i
    by_contra hki
    have hXi : X i ∣ monomial k (1 : R) := X_dvd_monomial.mpr (Or.inr hki)
    exact hX i (hgr ▸ dvd_mul_of_dvd_left hXi r)
  have hgr' : g = r := by simpa [hk0] using hgr
  exact hgr' ▸ hrp

/-- When no variable `Xᵢ` divides `g`, `toLaurent` reflects and preserves divisibility by `g`. -/
theorem toLaurent_dvd_toLaurent_iff_of_forall_not_X_dvd {g p : MvPolynomial K R}
    (hX : ∀ i : K, ¬ X i ∣ g) : toLaurent g ∣ toLaurent p ↔ g ∣ p :=
  ⟨dvd_of_toLaurent_dvd_of_forall_not_X_dvd hX, map_dvd toLaurent⟩

/-- **Unconditional ascent of relative primality along `toLaurent`.** Over a commutative ring
without zero divisors, relatively prime polynomials remain relatively prime in the Laurent ring. -/
theorem isRelPrime_toLaurent {p q : MvPolynomial K R} (hpq : IsRelPrime p q) :
    IsRelPrime (toLaurent p) (toLaurent q) := by
  rcases subsingleton_or_nontrivial R with _ | _
  · intro f _ _
    exact isUnit_of_subsingleton f
  intro f hfp hfq
  by_cases hf0 : f = 0
  · subst hf0
    have hp0 : p = 0 := toLaurent_eq_zero.mp (zero_dvd_iff.mp hfp)
    have hq0 : q = 0 := toLaurent_eq_zero.mp (zero_dvd_iff.mp hfq)
    exact absurd (hpq (hp0 ▸ dvd_rfl) (hq0 ▸ dvd_rfl)) not_isUnit_zero
  obtain ⟨n, g₀, hfg₀, -⟩ := LaurentRing.exists_mul_toLaurent_monomial f
  obtain ⟨vn, hvn⟩ := isUnit_toLaurent_monomial_one (R := R) n
  have hg₀0 : g₀ ≠ 0 := by
    intro h0
    rw [h0, map_zero, ← hvn] at hfg₀
    exact hf0 ((mul_eq_zero.mp hfg₀).resolve_right vn.ne_zero)
  obtain ⟨k, g, rfl, hgX⟩ := exists_eq_monomial_mul_and_forall_not_X_dvd hg₀0
  have huk : IsUnit (toLaurent (monomial k (1 : R))) := isUnit_toLaurent_monomial_one k
  let vk : LaurentRing R K := toLaurent (monomial k (1 : R))
  let winv : LaurentRing R K := ((vn⁻¹ : (LaurentRing R K)ˣ) : LaurentRing R K)
  have hvw : (vn : LaurentRing R K) * winv = 1 := Units.mul_inv vn
  have hf_eq : f = vk * toLaurent g * winv := by
    calc
      f = f * ((vn : LaurentRing R K) * winv) := by rw [hvw, mul_one]
      _ = f * toLaurent (monomial n 1) * winv := by rw [← mul_assoc, hvn]
      _ = vk * toLaurent g * winv := by rw [hfg₀, map_mul]
  have hg_dvd_f : toLaurent g ∣ f := ⟨vk * winv, by rw [hf_eq]; ring⟩
  have hgp : g ∣ p := dvd_of_toLaurent_dvd_of_forall_not_X_dvd hgX (dvd_trans hg_dvd_f hfp)
  have hgq : g ∣ q := dvd_of_toLaurent_dvd_of_forall_not_X_dvd hgX (dvd_trans hg_dvd_f hfq)
  have hug : IsUnit (toLaurent g) := (hpq hgp hgq).map toLaurent
  exact hf_eq ▸ ((huk.mul hug).mul vn⁻¹.isUnit)

/-- **Characterization of polynomial relative primality via `LaurentRing`.** Over a domain, two
polynomials `p` and `q` are relatively prime if and only if `toLaurent p` and `toLaurent q` are
relatively prime and no variable `Xᵢ` divides both `p` and `q`. -/
theorem isRelPrime_iff_isRelPrime_toLaurent [Nontrivial R] {p q : MvPolynomial K R} :
    IsRelPrime p q ↔ IsRelPrime (toLaurent p) (toLaurent q) ∧ ∀ i : K, ¬ (X i ∣ p ∧ X i ∣ q) :=
  ⟨fun h ↦ ⟨isRelPrime_toLaurent h, fun _ ⟨hp, hq⟩ ↦ prime_X.not_isUnit (h hp hq)⟩,
    fun ⟨hL, hX⟩ ↦ isRelPrime_of_toLaurent hL hX⟩

/-- When no variable `Xᵢ` divides `p`, `toLaurent p` and `toLaurent q` are relatively prime in
`LaurentRing R K` if and only if `p` and `q` are relatively prime in `MvPolynomial K R`. -/
theorem isRelPrime_toLaurent_iff_of_forall_not_X_dvd_left {p q : MvPolynomial K R}
    (hp : ∀ i : K, ¬ X i ∣ p) : IsRelPrime (toLaurent p) (toLaurent q) ↔ IsRelPrime p q :=
  ⟨fun h ↦ isRelPrime_of_toLaurent_of_forall_not_X_dvd_left h hp, isRelPrime_toLaurent⟩

/-- When `p` has nonzero constant term, `toLaurent p` and `toLaurent q` are relatively prime in
`LaurentRing R K` if and only if `p` and `q` are relatively prime in `MvPolynomial K R`. -/
theorem isRelPrime_toLaurent_iff_of_constantCoeff_ne_zero_left {p q : MvPolynomial K R}
    (hp : constantCoeff p ≠ 0) : IsRelPrime (toLaurent p) (toLaurent q) ↔ IsRelPrime p q :=
  isRelPrime_toLaurent_iff_of_forall_not_X_dvd_left (not_X_dvd_of_constantCoeff_ne_zero hp)

end CommRing

end MvPolynomial

namespace TauCeti.LaurentRing

section CoordinateRays

variable {R K : Type*}

/-- Distinct standard basis vectors in `K →₀ ℤ` are `ℤ`-linearly independent. -/
theorem linearIndependent_single_ne {i j : K} (hij : i ≠ j) :
    LinearIndependent ℤ ![Finsupp.single i (1 : ℤ), Finsupp.single j (1 : ℤ)] := by
  classical
  refine Fintype.linearIndependent_iff.mpr fun g hg k ↦ ?_
  have hi := congrArg (fun m : K →₀ ℤ ↦ m i) hg
  have hj := congrArg (fun m : K →₀ ℤ ↦ m j) hg
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Finsupp.add_apply, Finsupp.smul_apply, Finsupp.zero_apply, Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne hij, Finsupp.single_eq_of_ne hij.symm, smul_eq_mul, mul_one, mul_zero,
    add_zero, zero_add] at hi hj
  fin_cases k
  · exact hi
  · exact hj

section CommSemiring

variable [CommSemiring R] [NoZeroDivisors R]

/-- Finite products of linear binomials in distinct Laurent variables are relatively prime. -/
theorem isRelPrime_prod_one_add_smul_X {i j : K} (hij : i ≠ j)
    {κ₁ κ₂ : Type*} (s : Finset κ₁) (u : Finset κ₂) (c : κ₁ → R) (d : κ₂ → R) :
    IsRelPrime (∏ r ∈ s, (1 + c r • X i : LaurentRing R K))
      (∏ t ∈ u, (1 + d t • X j : LaurentRing R K)) := by
  simpa only [X_def] using
    AddMonoidAlgebra.isRelPrime_prod_one_add_smul_single (linearIndependent_single_ne hij) s u c d

/-- Linear binomials `1 + c • X i` and `1 + d • X j` in distinct Laurent variables are relatively
prime. -/
theorem isRelPrime_one_add_smul_X {i j : K} (hij : i ≠ j) (c d : R) :
    IsRelPrime (1 + c • X i : LaurentRing R K) (1 + d • X j : LaurentRing R K) := by
  simpa only [X_def] using
    AddMonoidAlgebra.isRelPrime_one_add_smul_single (linearIndependent_single_ne hij) c d

/-- `1 + X i` and `1 + X j` are relatively prime in `LaurentRing R K` whenever `i ≠ j`. -/
theorem isRelPrime_one_add_X {i j : K} (hij : i ≠ j) :
    IsRelPrime (1 + X i : LaurentRing R K) (1 + X j : LaurentRing R K) := by
  simpa using isRelPrime_one_add_smul_X (R := R) hij 1 1

end CommSemiring

end CoordinateRays

/-! ### Checks -/

/-- `1 + X 0` and `1 + X 1` are relatively prime in `LaurentRing ℤ (Fin 2)`. -/
example : IsRelPrime (1 + X 0 : LaurentRing ℤ (Fin 2)) (1 + X 1) :=
  isRelPrime_one_add_X (by decide)

/-- Although `1 + X 0` and `1 + X 1` are `IsRelPrime` in `LaurentRing ℤ (Fin 2)`, the ideal they
generate is proper because both vanish under evaluation at `(-1, -1)`. -/
example : Ideal.span ({1 + X 0, 1 + X 1} : Set (LaurentRing ℤ (Fin 2))) ≠ ⊤ := by
  intro htop
  let φ : LaurentRing ℤ (Fin 2) →ₐ[ℤ] ℤ := aeval fun _ ↦ (-1 : ℤˣ)
  have hle : Ideal.span ({1 + X 0, 1 + X 1} : Set (LaurentRing ℤ (Fin 2))) ≤
      RingHom.ker φ.toRingHom := by
    refine Ideal.span_le.mpr ?_
    rintro p (rfl | rfl) <;> simp [φ, RingHom.mem_ker]
  have h1 : (1 : LaurentRing ℤ (Fin 2)) ∈ RingHom.ker φ.toRingHom :=
    hle (htop.symm ▸ Submodule.mem_top)
  simp [φ, RingHom.mem_ker] at h1

/-- Along the same coordinate ray, `1 + X 0` and `1 + X 0 ^ 3` are not relatively prime in
`LaurentRing ℤ (Fin 2)` since `1 + X 0` is a non-unit common divisor. -/
example : ¬ IsRelPrime (1 + X 0 : LaurentRing ℤ (Fin 2)) (1 + X 0 ^ 3) := by
  intro hrel
  have hdvd : (1 + X 0 : LaurentRing ℤ (Fin 2)) ∣ 1 + X 0 ^ 3 :=
    ⟨1 - X 0 + X 0 ^ 2, by ring⟩
  have hu : IsUnit (1 + X 0 : LaurentRing ℤ (Fin 2)) := hrel dvd_rfl hdvd
  let φ : LaurentRing ℤ (Fin 2) →ₐ[ℤ] ℤ := aeval fun _ ↦ (-1 : ℤˣ)
  have hu0 : IsUnit (φ (1 + X 0)) := hu.map φ
  simp [φ] at hu0

end TauCeti.LaurentRing
