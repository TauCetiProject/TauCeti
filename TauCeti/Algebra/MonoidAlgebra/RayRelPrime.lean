/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Degree
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.RingTheory.Coprime.Basic
public import TauCeti.Algebra.Group.UniqueProds.TorsionFree
public import TauCeti.Algebra.MonoidAlgebra.Grading
public import TauCeti.Algebra.MonoidAlgebra.Units
public import TauCeti.RingTheory.GradedAlgebra.Degree.Width
import Mathlib.Algebra.Category.Grp.Injective
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.LinearAlgebra.Span.Basic

/-!
# Weighted degree width and relative primality along independent rays in group algebras

For an additive monoid homomorphism `w : M →+ ι` into a linearly ordered commutative monoid or
group, the grading `AddMonoidAlgebra.gradeBy R w` of `R[M]` endows every nonzero element `x` with a
least weight `minDeg (gradeBy R w) x`, a greatest weight `maxDeg (gradeBy R w) x`, and (when `ι` is
an ordered group) a nonnegative degree width `degWidth (gradeBy R w) x`. The first part of this
file connects these graded invariants to the exponent support `x.coeff.support` and to Mathlib's
`AddMonoidAlgebra.supDegree` and `AddMonoidAlgebra.infDegree`.

The second part applies degree width under rational additive functionals `w : L →+ ℚ` (constructed
by Baer's criterion for divisible `ℤ`-modules) to divisibility in the group algebra `R[L]` of a
torsion-free commutative group `L` over a commutative semiring `R` without zero divisors:

* If `h ∣ P` for a nonzero `P : R[L]` supported on the cyclic subgroup `ℤ • a`, then every
  functional `w : L →+ ℚ` vanishing on `a` assigns `P` width `0`, hence assigns `h` width `0`, so
  `w` is constant on `h.coeff.support`. Consequently every difference of exponents in the support
  of `h` has a nonzero integer multiple in `ℤ • a`
  (`AddMonoidAlgebra.exists_zsmul_sub_eq_zsmul_of_dvd_of_support_subset_zsmul`).
* If `a, b : L` are `ℤ`-linearly independent, any common divisor `h` of nonzero `P` supported on
  `ℤ • a` and nonzero `Q` supported on `ℤ • b` has singleton support, i.e. is a monomial
  `single d r` (`AddMonoidAlgebra.exists_eq_single_of_dvd_of_support_subset_zsmul`).
* If, in addition, `P` has at least one unit coefficient, then `r` divides that unit coefficient
  and is therefore a unit, making `single d r` a unit of `R[L]`; hence `IsRelPrime P Q`
  (`AddMonoidAlgebra.isRelPrime_of_support_subset_zsmul`).
* Specializing to factors of the form `1 + single a c` (which have constant term `coeff 0 = 1`
  along any nonzero ray) yields unconditional relative primality of finite products
  `∏ r ∈ s, (1 + single a (c r))` and `∏ t ∈ u, (1 + single b (d t))` along `ℤ`-linearly
  independent rays (`AddMonoidAlgebra.isRelPrime_prod_one_add_single` and
  `AddMonoidAlgebra.isRelPrime_one_add_single`). No finite-generation hypothesis on `L` is needed.

## Main results

* `AddMonoidAlgebra.supDegree_withBot_eq_maxDeg_gradeBy`,
  `AddMonoidAlgebra.infDegree_withTop_eq_minDeg_gradeBy`: compatibility of `maxDeg` and `minDeg`
  for `gradeBy R w` with `supDegree` and `infDegree`.
* `AddMonoidAlgebra.degWidth_gradeBy_eq_zero_iff_forall_mem_support`: `degWidth (gradeBy R w) x = 0`
  iff `w` is constant on `x.coeff.support`.
* `AddMonoidAlgebra.exists_zsmul_sub_eq_zsmul_of_dvd_of_support_subset_zsmul`: differences of
  supported exponents of any divisor of a nonzero element supported on `ℤ • a` lie in the
  `ℤ`-saturation of `ℤ • a`.
* `AddMonoidAlgebra.exists_eq_single_of_dvd_of_support_subset_zsmul`: common divisors of nonzero
  elements supported on `ℤ`-linearly independent rays are monomials.
* `AddMonoidAlgebra.isRelPrime_of_support_subset_zsmul`: relative primality of nonzero elements
  supported on `ℤ`-linearly independent rays when one has a unit coefficient.
* `AddMonoidAlgebra.isRelPrime_prod_one_add_single`, `AddMonoidAlgebra.isRelPrime_one_add_single`:
  relative primality of binomials `1 + single a c` and of finite products thereof along
  `ℤ`-linearly independent rays.
-/

public section

namespace AddMonoidAlgebra

open TauCeti.GradedAlgebra

section WeightDegree

variable {R M ι : Type*} [CommSemiring R] [AddMonoid M] [DecidableEq ι]

section AddCommMonoid

variable [AddCommMonoid ι] [LinearOrder ι] (w : M →+ ι)

/-- Every supported exponent of `x : R[M]` has weight at least `minDeg (gradeBy R w) x`. -/
theorem minDeg_gradeBy_le_of_mem_support {x : R[M]} {m : M} (hm : m ∈ x.coeff.support) :
    minDeg (gradeBy R w) x ≤ w m :=
  minDeg_le_of_decompose_ne_zero (gradeBy R w)
    ((coe_decompose_gradeBy_ne_zero_iff w x (w m)).mpr ⟨m, hm, rfl⟩)

/-- Every supported exponent of `x : R[M]` has weight at most `maxDeg (gradeBy R w) x`. -/
theorem le_maxDeg_gradeBy_of_mem_support {x : R[M]} {m : M} (hm : m ∈ x.coeff.support) :
    w m ≤ maxDeg (gradeBy R w) x :=
  le_maxDeg_of_decompose_ne_zero (gradeBy R w)
    ((coe_decompose_gradeBy_ne_zero_iff w x (w m)).mpr ⟨m, hm, rfl⟩)

/-- For nonzero `x : R[M]`, `minDeg (gradeBy R w) x` is attained at some supported exponent. -/
theorem exists_mem_support_minDeg_gradeBy {x : R[M]} (hx : x ≠ 0) :
    ∃ m ∈ x.coeff.support, w m = minDeg (gradeBy R w) x := by
  have hne := minHomogPart_ne_zero (gradeBy R w) hx
  rw [minHomogPart_def] at hne
  exact (coe_decompose_gradeBy_ne_zero_iff w x _).mp hne

/-- For nonzero `x : R[M]`, `maxDeg (gradeBy R w) x` is attained at some supported exponent. -/
theorem exists_mem_support_maxDeg_gradeBy {x : R[M]} (hx : x ≠ 0) :
    ∃ m ∈ x.coeff.support, w m = maxDeg (gradeBy R w) x := by
  have hne := maxHomogPart_ne_zero (gradeBy R w) hx
  rw [maxHomogPart_def] at hne
  exact (coe_decompose_gradeBy_ne_zero_iff w x _).mp hne

/-- For nonzero `x : R[M]`, `supDegree` along `w : M → WithBot ι` agrees with
`maxDeg (gradeBy R w) x`. -/
theorem supDegree_withBot_eq_maxDeg_gradeBy {x : R[M]} (hx : x ≠ 0) :
    x.supDegree (fun m ↦ (w m : WithBot ι)) = maxDeg (gradeBy R w) x := by
  refine le_antisymm
    (Finset.sup_le fun m hm ↦ WithBot.coe_le_coe.mpr (le_maxDeg_gradeBy_of_mem_support w hm)) ?_
  obtain ⟨m, hm, hwm⟩ := exists_mem_support_maxDeg_gradeBy w hx
  rw [← hwm]
  exact Finset.le_sup (f := fun m ↦ (w m : WithBot ι)) hm

/-- For nonzero `x : R[M]`, `infDegree` along `w : M → WithTop ι` agrees with
`minDeg (gradeBy R w) x`. -/
theorem infDegree_withTop_eq_minDeg_gradeBy {x : R[M]} (hx : x ≠ 0) :
    x.infDegree (fun m ↦ (w m : WithTop ι)) = minDeg (gradeBy R w) x := by
  refine le_antisymm ?_
    (Finset.le_inf fun m hm ↦ WithTop.coe_le_coe.mpr (minDeg_gradeBy_le_of_mem_support w hm))
  obtain ⟨m, hm, hwm⟩ := exists_mem_support_minDeg_gradeBy w hx
  rw [← hwm]
  exact Finset.inf_le (f := fun m ↦ (w m : WithTop ι)) hm

end AddCommMonoid

section AddCommGroup

variable [AddCommGroup ι] [LinearOrder ι] (w : M →+ ι)

/-- The difference of weights of any two supported exponents of `x` is bounded above by
`degWidth (gradeBy R w) x`. -/
theorem le_degWidth_gradeBy_of_mem_support [IsOrderedAddMonoid ι] {x : R[M]} {m₁ m₂ : M}
    (hm₁ : m₁ ∈ x.coeff.support) (hm₂ : m₂ ∈ x.coeff.support) :
    w m₁ - w m₂ ≤ degWidth (gradeBy R w) x := by
  rw [degWidth_def]
  exact sub_le_sub (le_maxDeg_gradeBy_of_mem_support w hm₁)
    (minDeg_gradeBy_le_of_mem_support w hm₂)

/-- The degree width of `x : R[M]` along `w` vanishes if and only if `w` takes the same value on
all supported exponents of `x`. -/
theorem degWidth_gradeBy_eq_zero_iff_forall_mem_support {x : R[M]} :
    degWidth (gradeBy R w) x = 0 ↔
      ∀ m₁ ∈ x.coeff.support, ∀ m₂ ∈ x.coeff.support, w m₁ = w m₂ := by
  rw [degWidth_eq_zero_iff]
  refine ⟨fun ⟨d, hd⟩ m₁ hm₁ m₂ hm₂ ↦ by rw [hd m₁ hm₁, hd m₂ hm₂], fun h ↦ ?_⟩
  by_cases hx : x = 0
  · exact ⟨0, hx ▸ Submodule.zero_mem _⟩
  · obtain ⟨m₀, hm₀⟩ := Finsupp.support_nonempty_iff.mpr (mt coeff_eq_zero.mp hx)
    exact ⟨w m₀, fun m hm ↦ h m hm m₀ hm₀⟩

end AddCommGroup

end WeightDegree

/-! ### Divisibility and relative primality along rays in torsion-free group algebras -/

/-- If no nonzero integer multiple of `d` lies in `ℤ • a`, Baer's criterion extends the projection
onto `d` to an additive homomorphism `w : L →+ ℚ` with `w a = 0` and `w d = 1`. -/
private theorem exists_addMonoidHom_rat_eq_zero_and_eq_one {L : Type*} [AddCommGroup L]
    {a d : L} (hd : ∀ n : ℤ, n ≠ 0 → ∀ k : ℤ, n • d ≠ k • a) :
    ∃ w : L →+ ℚ, w a = 0 ∧ w d = 1 := by
  let S : Submodule ℤ L := Submodule.span ℤ {a}
  let i : S × ℤ →+ L :=
    { toFun p := (p.1 : L) + p.2 • d
      map_zero' := by simp
      map_add' p q := by simp [add_smul]; abel }
  have hi : Function.Injective i := (injective_iff_map_eq_zero i).mpr fun ⟨x, v⟩ hxv ↦ by
    have hv : v = 0 := by_contra fun hv ↦ by
      obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp x.2
      have heq : v • d = (-k) • a := by
        rw [neg_smul, hk, eq_neg_iff_add_eq_zero, add_comm]
        exact hxv
      exact hd v hv (-k) heq
    subst hv
    have hx0 : (x : L) = 0 := by simpa [i] using hxv
    exact Prod.ext (Subtype.ext hx0) rfl
  let g : S × ℤ →+ ℚ := (Int.castAddHom ℚ).comp (AddMonoidHom.snd S ℤ)
  obtain ⟨w, hw⟩ := (Module.Baer.of_divisible ℚ).extension_property_addMonoidHom i hi g
  have hwa : w a = 0 := by
    simpa [i, g] using DFunLike.congr_fun hw (⟨a, Submodule.mem_span_singleton_self a⟩, 0)
  have hwd : w d = 1 := by
    simpa [i, g] using DFunLike.congr_fun hw (0, 1)
  exact ⟨w, hwa, hwd⟩

section RayDivisibility

variable {R L : Type*} [CommSemiring R] [NoZeroDivisors R] [AddCommGroup L] [HasUniqueDiv L]

/-- **Divisors of ray-supported elements have ray-collinear support differences.** If `h ∣ P` for a
nonzero `P : R[L]` whose support lies in `ℤ • a`, then for any two exponents `x, y` in the support
of `h`, some nonzero integer multiple of `x - y` lies in `ℤ • a`. -/
theorem exists_zsmul_sub_eq_zsmul_of_dvd_of_support_subset_zsmul {a : L} {h P : R[L]}
    (hdvd : h ∣ P) (hP0 : P ≠ 0) (hP : (P.coeff.support : Set L) ⊆ Set.range (· • a : ℤ → L))
    {x y : L} (hx : x ∈ h.coeff.support) (hy : y ∈ h.coeff.support) :
    ∃ (n k : ℤ), n ≠ 0 ∧ n • (x - y) = k • a := by
  by_contra! H
  obtain ⟨w, hwa, hwxy⟩ := exists_addMonoidHom_rat_eq_zero_and_eq_one fun n hn k ↦ H n k hn
  have hPmem : P ∈ gradeBy R w 0 := fun m hm ↦ by
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
    rw [mul_smul, ← h1, ← mul_smul, mul_comm n₂ n₁, mul_smul, h2, ← mul_smul, neg_smul,
      add_neg_cancel]
  have hn₂k₁ : n₂ * k₁ = 0 :=
    Fintype.linearIndependent_iff.mp hlin ![n₂ * k₁, -(n₁ * k₂)]
      (by simpa [Fin.sum_univ_two] using hrel) 0
  have hk₁ : k₁ = 0 := (mul_eq_zero.mp hn₂k₁).resolve_left hn₂
  have hxd : n₁ • (x - d) = n₁ • (0 : L) := by simp [h1, hk₁]
  exact sub_eq_zero.mp ((zsmul_right_inj hn₁).mp hxd)

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

/-- Symmetric form of `AddMonoidAlgebra.isRelPrime_of_support_subset_zsmul` with the unit
coefficient hypothesis on the second factor. -/
theorem isRelPrime_of_support_subset_zsmul_right {a b : L} (hlin : LinearIndependent ℤ ![a, b])
    {P Q : R[L]} (hP : (P.coeff.support : Set L) ⊆ Set.range (· • a : ℤ → L))
    (hQ : (Q.coeff.support : Set L) ⊆ Set.range (· • b : ℤ → L))
    (hP0 : P ≠ 0) (hQunit : ∃ m : L, IsUnit (Q.coeff m)) :
    IsRelPrime P Q := by
  have hlin' : LinearIndependent ℤ ![b, a] := by
    have h := hlin.comp ![1, 0] (by decide)
    convert h using 1
    ext i
    fin_cases i <;> rfl
  exact (isRelPrime_of_support_subset_zsmul hlin' hQ hP hP0 hQunit).symm

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
    have hm0 : m = 0 := Finset.mem_singleton.mp (Finsupp.support_single_subset hm)
    exact ⟨0, by simp [hm0]⟩
  | insert r s hr ih =>
    intro m hm
    rw [Finset.prod_insert hr] at hm
    obtain ⟨m₁, hm₁, m₂, hm₂, rfl⟩ := Finset.mem_add.mp (support_coeff_mul_subset _ _ hm)
    obtain ⟨n₂, hn₂⟩ := ih hm₂
    dsimp only at hn₂
    rcases Finset.mem_union.mp (Finsupp.support_add hm₁) with h1 | h1
    · rw [one_def] at h1
      have hm₁0 : m₁ = 0 := Finset.mem_singleton.mp (Finsupp.support_single_subset h1)
      exact ⟨n₂, by simp [hm₁0, hn₂]⟩
    · have hm₁a : m₁ = a := Finset.mem_singleton.mp (Finsupp.support_single_subset h1)
      exact ⟨1 + n₂, by dsimp only; rw [hm₁a, ← hn₂, add_nsmul, one_nsmul]⟩

/-- Every exponent in the support of `∏ r ∈ s, (1 + single a (c r))` is an integer multiple of
`a`. -/
theorem support_prod_one_add_single_subset_zsmul {R L κ : Type*} [CommSemiring R] [AddCommGroup L]
    (s : Finset κ) (a : L) (c : κ → R) :
    (((∏ r ∈ s, (1 + single a (c r) : R[L])).coeff.support : Set L)) ⊆
      Set.range (· • a : ℤ → L) := fun m hm ↦ by
  obtain ⟨n, hn⟩ := support_prod_one_add_single_subset_nsmul s a c hm
  exact ⟨n, by simpa [natCast_zsmul] using hn⟩

/-- For a nonzero element `a` of a torsion-free additive commutative group `L`, the constant term
of `∏ r ∈ s, (1 + single a (c r))` is `1`: all non-constant contributions lie in positive multiples
of `a` and therefore never cancel `0`. -/
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
    have hneg : P.coeff (-a) = 0 := by
      by_contra hne
      obtain ⟨n, hn⟩ :=
        support_prod_one_add_single_subset_nsmul s a c (Finsupp.mem_support_iff.mpr hne)
      dsimp only at hn
      have h0 : ((n : ℤ) + 1) • a = (0 : ℤ) • a := by
        rw [add_smul, one_smul, natCast_zsmul, hn, neg_add_cancel, zero_smul]
      have hn0 : (n : ℤ) + 1 = 0 := (IsAddTorsionFree.zsmul_left_inj ha).mp h0
      omega
    have hmul : (single a (c r) * P).coeff 0 = 0 := by
      rw [← add_neg_cancel a, coeff_single_mul_add, hneg, mul_zero]
    rw [hmul, add_zero]

section UniqueDiv

variable {R L : Type*} [CommSemiring R] [NoZeroDivisors R] [AddCommGroup L] [HasUniqueDiv L]

/-- **Finite products of binomials along `ℤ`-linearly independent rays are relatively prime.** -/
theorem isRelPrime_prod_one_add_single {a b : L} (hlin : LinearIndependent ℤ ![a, b])
    {κ₁ κ₂ : Type*} (s : Finset κ₁) (u : Finset κ₂) (c : κ₁ → R) (d : κ₂ → R) :
    IsRelPrime (∏ r ∈ s, (1 + single a (c r) : R[L]))
      (∏ t ∈ u, (1 + single b (d t) : R[L])) := by
  rcases subsingleton_or_nontrivial R with _ | _
  · intro h _ _
    exact isUnit_of_subsingleton h
  have ha : a ≠ 0 := by simpa using hlin.ne_zero 0
  have hb : b ≠ 0 := by simpa using hlin.ne_zero 1
  have hQ0 : (∏ t ∈ u, (1 + single b (d t) : R[L])) ≠ 0 := fun h0 ↦ by
    have h1 := coeff_zero_prod_one_add_single (R := R) hb u d
    rw [h0, coeff_zero, Finsupp.zero_apply] at h1
    exact zero_ne_one h1
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

/-- Variant of `AddMonoidAlgebra.isRelPrime_prod_one_add_single` written with scalar multiples
`c r • single a 1`. -/
theorem isRelPrime_prod_one_add_smul_single {a b : L} (hlin : LinearIndependent ℤ ![a, b])
    {κ₁ κ₂ : Type*} (s : Finset κ₁) (u : Finset κ₂) (c : κ₁ → R) (d : κ₂ → R) :
    IsRelPrime (∏ r ∈ s, (1 + c r • single a (1 : R) : R[L]))
      (∏ t ∈ u, (1 + d t • single b (1 : R) : R[L])) := by
  simpa [smul_single] using isRelPrime_prod_one_add_single hlin s u c d

/-- Variant of `AddMonoidAlgebra.isRelPrime_one_add_single` written with scalar multiples
`c • single a 1` and `d • single b 1`. -/
theorem isRelPrime_one_add_smul_single {a b : L} (hlin : LinearIndependent ℤ ![a, b]) (c d : R) :
    IsRelPrime (1 + c • single a (1 : R) : R[L]) (1 + d • single b (1 : R) : R[L]) := by
  simpa [smul_single] using isRelPrime_one_add_single hlin c d

end UniqueDiv

end RayBinomials

end AddMonoidAlgebra
