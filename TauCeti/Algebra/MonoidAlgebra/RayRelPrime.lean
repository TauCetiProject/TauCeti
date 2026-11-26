/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.RingTheory.Coprime.Basic
public import TauCeti.Algebra.Group.UniqueProds.TorsionFree
public import TauCeti.Algebra.MonoidAlgebra.Grading
public import TauCeti.Algebra.MonoidAlgebra.Units
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.Abel
import TauCeti.GroupTheory.Divisible.Basic

/-!
# Relative primality along independent rays in torsion-free group algebras

Using the weighted degree width API (`TauCeti.GradedAlgebra.degWidth` on
`AddMonoidAlgebra.gradeBy R w` from `TauCeti.Algebra.MonoidAlgebra.Grading`), this file applies
rational functionals `w : L →+ ℚ` (`TauCeti.exists_addMonoidHom_apply_eq_zero_and_apply_eq`,
constructed via Baer's criterion) to divisibility in the group algebra `R[L]` of a torsion-free
commutative group `L` over `[CommSemiring R] [NoZeroDivisors R]`: any divisor of a nonzero element
supported on `ℤ • a` has ray-collinear support differences, common divisors along `ℤ`-linearly
independent rays are monomials, and finite products of binomials `1 + single a (c r)` along
`ℤ`-linearly independent rays are relatively prime without any finite-generation hypothesis on `L`.

## Main results

* `AddMonoidAlgebra.exists_zsmul_sub_eq_zsmul_of_dvd_of_support_subset_zsmul`: support differences
  of divisors of nonzero elements supported on `ℤ • a` lie in the `ℤ`-saturation of `ℤ • a`.
* `AddMonoidAlgebra.exists_eq_single_of_dvd_of_support_subset_zsmul`: common divisors of nonzero
  elements supported on `ℤ`-linearly independent rays are monomials.
* `AddMonoidAlgebra.isRelPrime_of_support_subset_zsmul`,
  `AddMonoidAlgebra.isRelPrime_prod_one_add_single`, `AddMonoidAlgebra.isRelPrime_one_add_single`:
  relative primality of ray-supported elements and finite products of ray binomials.
-/

public section

namespace AddMonoidAlgebra

open TauCeti.GradedAlgebra

section RayDivisibility

variable {R L : Type*} [CommSemiring R] [NoZeroDivisors R] [AddCommGroup L] [IsAddTorsionFree L]

/-- **Divisors of ray-supported elements have ray-collinear support differences.** If `h ∣ P` for a
nonzero `P : R[L]` whose support lies in `ℤ • a`, then for any two exponents `x, y` in the support
of `h`, some nonzero integer multiple of `x - y` lies in `ℤ • a`. -/
theorem exists_zsmul_sub_eq_zsmul_of_dvd_of_support_subset_zsmul {a : L} {h P : R[L]}
    (hdvd : h ∣ P) (hP0 : P ≠ 0) (hP : (P.coeff.support : Set L) ⊆ Set.range (· • a : ℤ → L))
    {x y : L} (hx : x ∈ h.coeff.support) (hy : y ∈ h.coeff.support) :
    ∃ (n k : ℤ), n ≠ 0 ∧ n • (x - y) = k • a := by
  by_contra! H
  obtain ⟨w, hwa, hwxy⟩ := TauCeti.exists_addMonoidHom_apply_eq_zero_and_apply_eq H (1 : ℚ)
  have hPmem : P ∈ gradeBy R w 0 := (mem_gradeBy_iff R w 0 P).mpr fun m hm ↦ by
    obtain ⟨k, rfl⟩ := hP hm
    simp [hwa]
  have hwidthP : degWidth (gradeBy R w) P = 0 := degWidth_of_mem (gradeBy R w) hPmem
  have hwidthh : degWidth (gradeBy R w) h = 0 :=
    le_antisymm (hwidthP ▸ degWidth_le_of_dvd (gradeBy R w) hdvd hP0)
      (degWidth_nonneg (gradeBy R w) h)
  have hweq : w x = w y :=
    (degWidth_gradeBy_eq_zero_iff_forall_mem_support w).mp hwidthh x hx y hy
  have hw0 : w (x - y) = 0 := by rw [map_sub, hweq, sub_self]
  exact zero_ne_one (hw0.symm.trans hwxy)

/-- **Common divisors along `ℤ`-linearly independent rays are monomials.** If `a, b : L` are
`ℤ`-linearly independent and `h : R[L]` divides both a nonzero `P` supported on `ℤ • a` and a
nonzero `Q` supported on `ℤ • b`, then `h` is a single monomial `single d r`. -/
theorem exists_eq_single_of_dvd_of_support_subset_zsmul {a b : L}
    (hlin : LinearIndependent ℤ ![a, b]) {h P Q : R[L]}
    (hdvdP : h ∣ P) (hdvdQ : h ∣ Q) (hP0 : P ≠ 0) (hQ0 : Q ≠ 0)
    (hP : (P.coeff.support : Set L) ⊆ Set.range (· • a : ℤ → L))
    (hQ : (Q.coeff.support : Set L) ⊆ Set.range (· • b : ℤ → L)) :
    ∃ (d : L) (r : R), h = single d r := by
  have hh0 : h ≠ 0 := by
    rintro rfl
    exact hP0 (zero_dvd_iff.mp hdvdP)
  obtain ⟨d, hd⟩ := Finsupp.support_nonempty_iff.mpr (mt coeff_eq_zero.mp hh0)
  refine ⟨d, h.coeff d, coeff_inj.mp (Finsupp.support_subset_singleton.mp fun x hx ↦ ?_)⟩
  rw [Finset.mem_singleton]
  obtain ⟨n₁, k₁, hn₁, h1⟩ :=
    exists_zsmul_sub_eq_zsmul_of_dvd_of_support_subset_zsmul hdvdP hP0 hP hx hd
  obtain ⟨n₂, k₂, hn₂, h2⟩ :=
    exists_zsmul_sub_eq_zsmul_of_dvd_of_support_subset_zsmul hdvdQ hQ0 hQ hx hd
  have hrel : (n₂ * k₁) • a + (-(n₁ * k₂)) • b = 0 := by
    simp only [mul_smul, neg_smul, ← h1, ← h2, smul_comm n₂ n₁]
    abel
  have hn₂k₁ : n₂ * k₁ = 0 :=
    Fintype.linearIndependent_iff.mp hlin ![n₂ * k₁, -(n₁ * k₂)]
      (by simpa [Fin.sum_univ_two] using hrel) 0
  have hk₁ : k₁ = 0 := (mul_eq_zero.mp hn₂k₁).resolve_left hn₂
  refine sub_eq_zero.mp (by_contra fun hne ↦ hn₁ ?_)
  have h0 : n₁ • (x - d) = (0 : ℤ) • (x - d) := by simp [h1, hk₁]
  exact (IsAddTorsionFree.zsmul_left_inj hne).mp h0

/-- **Relative primality along `ℤ`-linearly independent rays.** In the group algebra `R[L]` of a
torsion-free commutative group over a commutative semiring without zero divisors, if `P` is
supported on `ℤ • a` and has at least one unit coefficient while `Q ≠ 0` is supported on `ℤ • b`
for `ℤ`-linearly independent `a, b : L`, then `IsRelPrime P Q`. -/
theorem isRelPrime_of_support_subset_zsmul {a b : L} (hlin : LinearIndependent ℤ ![a, b])
    {P Q : R[L]} (hP : (P.coeff.support : Set L) ⊆ Set.range (· • a : ℤ → L))
    (hQ : (Q.coeff.support : Set L) ⊆ Set.range (· • b : ℤ → L))
    (hQ0 : Q ≠ 0) (hPunit : ∃ m : L, IsUnit (P.coeff m)) :
    IsRelPrime P Q := by
  rcases subsingleton_or_nontrivial R with _ | _
  · intro h _ _
    exact isUnit_of_subsingleton h
  intro h hdvdP hdvdQ
  obtain ⟨m₀, hm₀⟩ := hPunit
  have hP0 : P ≠ 0 := fun h0 ↦ hm₀.ne_zero (by simp [h0])
  obtain ⟨d, r, rfl⟩ :=
    exists_eq_single_of_dvd_of_support_subset_zsmul hlin hdvdP hdvdQ hP0 hQ0 hP hQ
  obtain ⟨u, hu⟩ := hdvdP
  have hdvd_coeff : r ∣ P.coeff m₀ :=
    ⟨u.coeff (m₀ - d), by conv_lhs => rw [hu, ← add_sub_cancel d m₀, coeff_single_mul_add]⟩
  have hr : IsUnit r := isUnit_of_dvd_unit hdvd_coeff hm₀
  exact (isUnit_single_iff d r).mpr ⟨⟨toAddUnits d, rfl⟩, hr⟩

end RayDivisibility

/-! ### Finite products of ray binomials `1 + single a (c r)` -/

section RayBinomials

/-- Every exponent in the support of `∏ r ∈ s, (1 + single a (c r))` is a natural-number multiple
of `a`. -/
theorem support_prod_one_add_single_subset_nsmul {R L κ : Type*} [CommSemiring R] [AddCommMonoid L]
    (s : Finset κ) (a : L) (c : κ → R) :
    (((∏ r ∈ s, (1 + single a (c r) : R[L])).coeff.support : Set L)) ⊆
      Set.range (· • a : ℕ → L) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro m hm
    rw [Finset.prod_empty, one_def] at hm
    exact ⟨0, by simp [Finset.mem_singleton.mp (Finsupp.support_single_subset hm)]⟩
  | insert r s hr ih =>
    intro m hm
    rw [Finset.prod_insert hr] at hm
    obtain ⟨m₁, hm₁, m₂, hm₂, rfl⟩ := Finset.mem_add.mp (support_coeff_mul_subset _ _ hm)
    obtain ⟨n₂, hn₂⟩ := ih hm₂
    dsimp only at hn₂
    rcases Finset.mem_union.mp (Finsupp.support_add hm₁) with h1 | h1
    · rw [one_def] at h1
      exact ⟨n₂, by simp [Finset.mem_singleton.mp (Finsupp.support_single_subset h1), hn₂]⟩
    · exact ⟨1 + n₂, by
        dsimp only
        rw [Finset.mem_singleton.mp (Finsupp.support_single_subset h1), ← hn₂, add_nsmul,
          one_nsmul]⟩

/-- Every exponent in the support of `∏ r ∈ s, (1 + single a (c r))` is an integer multiple of
`a`. -/
theorem support_prod_one_add_single_subset_zsmul {R L κ : Type*} [CommSemiring R] [AddCommGroup L]
    (s : Finset κ) (a : L) (c : κ → R) :
    (((∏ r ∈ s, (1 + single a (c r) : R[L])).coeff.support : Set L)) ⊆
      Set.range (· • a : ℤ → L) := fun _ hm ↦ by
  obtain ⟨n, hn⟩ := support_prod_one_add_single_subset_nsmul s a c hm
  exact ⟨n, by simpa [natCast_zsmul] using hn⟩

/-- For a nonzero element `a` of a torsion-free additive commutative group `L`, the constant term
of `∏ r ∈ s, (1 + single a (c r))` is `1`. -/
@[simp]
theorem coeff_zero_prod_one_add_single {R L κ : Type*} [CommSemiring R] [AddCommGroup L]
    [IsAddTorsionFree L] {a : L} (ha : a ≠ 0) (s : Finset κ) (c : κ → R) :
    (∏ r ∈ s, (1 + single a (c r) : R[L])).coeff 0 = 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [one_def]
  | insert r s hr ih =>
    set P : R[L] := ∏ t ∈ s, (1 + single a (c t))
    rw [Finset.prod_insert hr, add_mul, one_mul, coeff_add, Finsupp.add_apply, ih]
    have hneg : P.coeff (-a) = 0 := by_contra fun hne ↦ by
      obtain ⟨n, hn⟩ :=
        support_prod_one_add_single_subset_nsmul s a c (Finsupp.mem_support_iff.mpr hne)
      have h0 : ((n : ℤ) + 1) • a = (0 : ℤ) • a := by
        dsimp only at hn
        rw [add_smul, one_smul, natCast_zsmul, hn, neg_add_cancel, zero_smul]
      have hn0 : (n : ℤ) + 1 = 0 := (IsAddTorsionFree.zsmul_left_inj ha).mp h0
      omega
    have hmul : (single a (c r) * P).coeff 0 = 0 := by
      rw [← add_neg_cancel a, coeff_single_mul_add, hneg, mul_zero]
    rw [hmul, add_zero]

section TorsionFree

variable {R L : Type*} [CommSemiring R] [NoZeroDivisors R] [AddCommGroup L] [IsAddTorsionFree L]

/-- **Finite products of binomials along `ℤ`-linearly independent rays are relatively prime.** -/
theorem isRelPrime_prod_one_add_single {a b : L} (hlin : LinearIndependent ℤ ![a, b])
    {κ₁ κ₂ : Type*} (s : Finset κ₁) (u : Finset κ₂) (c : κ₁ → R) (d : κ₂ → R) :
    IsRelPrime (∏ r ∈ s, (1 + single a (c r) : R[L]))
      (∏ t ∈ u, (1 + single b (d t) : R[L])) := by
  rcases subsingleton_or_nontrivial R with _ | _
  · exact fun h _ _ ↦ isUnit_of_subsingleton h
  have ha : a ≠ 0 := by simpa using hlin.ne_zero 0
  have hb : b ≠ 0 := by simpa using hlin.ne_zero 1
  have hQ0 : (∏ t ∈ u, (1 + single b (d t) : R[L])) ≠ 0 := fun h0 ↦
    zero_ne_one (α := R) (by simpa [h0] using coeff_zero_prod_one_add_single (R := R) hb u d)
  refine isRelPrime_of_support_subset_zsmul hlin
    (support_prod_one_add_single_subset_zsmul s a c)
    (support_prod_one_add_single_subset_zsmul u b d) hQ0 ⟨0, ?_⟩
  rw [coeff_zero_prod_one_add_single ha s c]
  exact isUnit_one

/-- **Binomials `1 + single a c` and `1 + single b d` along `ℤ`-linearly independent rays are
relatively prime.** -/
theorem isRelPrime_one_add_single {a b : L} (hlin : LinearIndependent ℤ ![a, b]) (c d : R) :
    IsRelPrime (1 + single a c : R[L]) (1 + single b d : R[L]) := by
  simpa using isRelPrime_prod_one_add_single hlin ({()} : Finset Unit) ({()} : Finset Unit)
    (fun _ ↦ c) (fun _ ↦ d)

end TorsionFree

end RayBinomials

end AddMonoidAlgebra
