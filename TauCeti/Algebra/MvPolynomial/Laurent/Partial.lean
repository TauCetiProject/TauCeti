/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MvPolynomial.Laurent.Polynomial
public import TauCeti.Algebra.MonoidAlgebra.Basis
public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.Logic.Equiv.Set

/-!
# Partially Laurent coefficient rings

Partially Laurent rings allow a chosen subset of variables to be inverted while the other
variables remain polynomial. They serve as ground rings for cluster algebras when only some
frozen variables are inverted. The scalar coefficient semiring is denoted by `R`.

`partiallyLaurent R S` is the subalgebra of the full Laurent ring spanned by monomials whose
exponents outside `S` are nonnegative. `partiallyLaurentBasis` gives unique coordinates in
these monomials. `toPartiallyLaurent` embeds polynomials, and `partiallyLaurentEmptyEquiv`
identifies the case `S = ∅` with the polynomial ring. `isLocalization_partiallyLaurent` and
`isLocalization_partiallyLaurent_of_subset` invert the selected variables and then any newly
selected variables. `partialCoeffMap` transports these constructions along coefficient maps,
including noninjective maps. `partialAeval` evaluates in a commutative algebra with units
required only for selected variables. `partiallyLaurent_eq_adjoin` and
`partiallyLaurent_le_iff` characterize generation by the
variables and selected inverse variables. Algebra maps to arbitrary, possibly noncommutative,
semiring targets are determined by the polynomial variables. Variable maps preserving the
selected sets give `partialRename`, and bijections reindex the selected sets by their images.

The variable and inverted sets may both be infinite: each element has finite support. The
construction and localization theorems work over any commutative coefficient semiring.

## References

* S. Fomin and A. Zelevinsky, *Cluster algebras IV: Coefficients*, §2.
-/

public section

namespace TauCeti.LaurentRing

variable {K : Type*}

/-- Exponents of monomials whose negative powers use only variables in `S`. -/
def nonnegOutside (S : Set K) : AddSubmonoid (K →₀ ℤ) where
  carrier := {m | ∀ i ∉ S, 0 ≤ m i}
  zero_mem' := by simp
  add_mem' hm hn i hi := add_nonneg (hm i hi) (hn i hi)

@[simp]
theorem mem_nonnegOutside {S : Set K} {m : K →₀ ℤ} :
    m ∈ nonnegOutside S ↔ ∀ i ∉ S, 0 ≤ m i := (Iff.rfl)

variable (R : Type*) [CommSemiring R] (S : Set K)

/-- The injective `R`-algebra map from the monoid algebra of `nonnegOutside S` to
`LaurentRing R K`, induced by the inclusion of the permitted exponents. -/
noncomputable def partialInclusion :
    AddMonoidAlgebra R (nonnegOutside S) →ₐ[R] LaurentRing R K :=
  AddMonoidAlgebra.mapDomainAlgHom R R (nonnegOutside S).subtype

theorem partialInclusion_apply (p : AddMonoidAlgebra R (nonnegOutside S)) :
    partialInclusion R S p = AddMonoidAlgebra.mapDomain Subtype.val p := by
  simp [partialInclusion]

/-- The partially Laurent subalgebra permits negative powers exactly in the variables in `S`. -/
noncomputable def partiallyLaurent : Subalgebra R (LaurentRing R K) :=
  (partialInclusion R S).range

variable {R S}

/-- The monomial realization of the partially Laurent ring is faithful over every coefficient
semiring, including those with zero divisors. -/
theorem partialInclusion_injective : Function.Injective (partialInclusion R S) := by
  intro p q h
  apply AddMonoidAlgebra.mapDomain_injective Subtype.val_injective
  simpa only [partialInclusion_apply] using h

@[simp]
theorem partialInclusion_inj {p q : AddMonoidAlgebra R (nonnegOutside S)} :
    partialInclusion R S p = partialInclusion R S q ↔ p = q := partialInclusion_injective.eq_iff

@[simp]
theorem partialInclusion_eq_zero {p : AddMonoidAlgebra R (nonnegOutside S)} :
    partialInclusion R S p = 0 ↔ p = 0 :=
  map_eq_zero_iff _ partialInclusion_injective

@[simp]
theorem range_partialInclusion : (partialInclusion R S).range = partiallyLaurent R S := (rfl)

@[simp]
theorem partialInclusion_single (m : nonnegOutside S) (r : R) :
    partialInclusion R S (AddMonoidAlgebra.single m r) =
      AddMonoidAlgebra.single (m : K →₀ ℤ) r := by simp [partialInclusion_apply]

@[simp]
theorem coeff_partialInclusion (p : AddMonoidAlgebra R (nonnegOutside S))
    (m : nonnegOutside S) : (partialInclusion R S p).coeff m = p.coeff m := by
  classical
  rw [partialInclusion_apply, AddMonoidAlgebra.coeff_mapDomain]
  exact Finsupp.mapDomain_apply_of_injective Subtype.val_injective p.coeff m

/-- Membership is the nonnegativity of every supported exponent outside the inverted set. -/
theorem mem_partiallyLaurent_iff {f : LaurentRing R K} :
    f ∈ partiallyLaurent R S ↔ ∀ m ∈ f.coeff.support, ∀ i ∉ S, 0 ≤ m i := by
  classical
  rw [partiallyLaurent, AlgHom.mem_range]
  constructor
  · rintro ⟨p, rfl⟩ m hm i hi
    rw [partialInclusion_apply, AddMonoidAlgebra.coeff_mapDomain] at hm
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hm)
    exact a.property i hi
  · intro hf
    refine ⟨AddMonoidAlgebra.comapDomain Subtype.val Subtype.val_injective f, ?_⟩
    rw [partialInclusion_apply]
    apply AddMonoidAlgebra.mapDomain_comapDomain
    intro m hm
    exact ⟨⟨m, hf m hm⟩, rfl⟩

/-- Increasing the set of inverted variables increases the partially Laurent subalgebra. -/
theorem partiallyLaurent_mono {T : Set K} (h : S ⊆ T) :
    partiallyLaurent R S ≤ partiallyLaurent R T := by
  intro f hf
  exact mem_partiallyLaurent_iff.2 fun m hm i hi ↦
    mem_partiallyLaurent_iff.1 hf m hm i (fun hs ↦ hi (h hs))

/-- With no variables inverted, the subalgebra is exactly the image of polynomials. -/
@[simp]
theorem partiallyLaurent_empty :
    partiallyLaurent R (∅ : Set K) =
      (MvPolynomial.toLaurent : MvPolynomial K R →ₐ[R] LaurentRing R K).range := by
  apply SetLike.ext
  intro f
  rw [mem_partiallyLaurent_iff, MvPolynomial.mem_range_toLaurent_iff]
  simp

/-- Inverting every variable gives the entire Laurent ring. -/
@[simp]
theorem partiallyLaurent_univ : partiallyLaurent R (Set.univ : Set K) = ⊤ := by
  ext f
  simp [mem_partiallyLaurent_iff]

/-- A monomial belongs precisely when its coefficient vanishes or its exponent is permitted. -/
@[simp]
theorem single_mem_partiallyLaurent_iff (m : K →₀ ℤ) (r : R) :
    AddMonoidAlgebra.single m r ∈ partiallyLaurent R S ↔
      r = 0 ∨ ∀ i ∉ S, 0 ≤ m i := by
  classical
  by_cases hr : r = 0
  · simp [hr]
  · simp [mem_partiallyLaurent_iff, hr]

/-- Every monomial with permitted exponents belongs to the partially Laurent subalgebra. -/
@[simp high]
theorem single_mem_partiallyLaurent (m : nonnegOutside S) (r : R) :
    AddMonoidAlgebra.single (m : K →₀ ℤ) r ∈ partiallyLaurent R S :=
  single_mem_partiallyLaurent_iff _ _ |>.2 (Or.inr m.property)

/-- A variable power belongs if the coefficient semiring is trivial, the variable is inverted,
or the exponent is nonnegative. -/
theorem val_unitX_zpow_mem_partiallyLaurent_iff (i : K) (n : ℤ) :
    ((unitX i ^ n : (LaurentRing R K)ˣ) : LaurentRing R K) ∈ partiallyLaurent R S ↔
      (1 : R) = 0 ∨ i ∈ S ∨ 0 ≤ n := by
  classical
  rw [val_unitX_zpow, single_mem_partiallyLaurent_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · by_cases hi : i ∈ S
      · exact Or.inr (Or.inl hi)
      · exact Or.inr (Or.inr (by simpa using h i hi))
  · rintro (h | hi | hn)
    · exact Or.inl h
    · exact Or.inr fun j hj ↦ by simp [show i ≠ j from fun h ↦ hj (h ▸ hi)]
    · exact Or.inr fun j _ ↦ by by_cases h : i = j <;> simp [h, hn]

/-- Every ordinary variable belongs to every partially Laurent subalgebra. -/
@[simp]
theorem X_mem_partiallyLaurent (i : K) : (X i : LaurentRing R K) ∈ partiallyLaurent R S := by
  simpa using (val_unitX_zpow_mem_partiallyLaurent_iff (R := R) (S := S) i 1).2
    (Or.inr (Or.inr zero_le_one))

/-- The inverse of a variable belongs whenever that variable is among those inverted. -/
theorem val_inv_unitX_mem_partiallyLaurent {i : K} (hi : i ∈ S) :
    ((unitX i)⁻¹ : (LaurentRing R K)ˣ).val ∈ partiallyLaurent R S := by
  simpa using (val_unitX_zpow_mem_partiallyLaurent_iff (R := R) (S := S) i (-1)).2
    (Or.inr (Or.inl hi))

/-- The partially Laurent ring is the monoid algebra of its permitted exponents. -/
noncomputable def partiallyLaurentEquiv :
    AddMonoidAlgebra R (nonnegOutside S) ≃ₐ[R] partiallyLaurent R S :=
  AlgEquiv.ofInjective (partialInclusion R S) partialInclusion_injective

/-- The monoid-algebra realization sends each permitted monomial to the same ambient monomial. -/
@[simp]
theorem coe_partiallyLaurentEquiv_apply (p : AddMonoidAlgebra R (nonnegOutside S)) :
    (partiallyLaurentEquiv p : LaurentRing R K) = partialInclusion R S p := by
  exact AlgEquiv.ofInjective_apply _ _ p

/-- The inverse monoid-algebra realization returns the given ambient Laurent polynomial. -/
@[simp]
theorem partialInclusion_partiallyLaurentEquiv_symm (f : partiallyLaurent R S) :
    partialInclusion R S (partiallyLaurentEquiv.symm f) = (f : LaurentRing R K) := by
  rw [← coe_partiallyLaurentEquiv_apply, AlgEquiv.apply_symm_apply]

/-- The permitted monomials form a basis of the partially Laurent ring. -/
noncomputable def partiallyLaurentBasis (R : Type*) [CommSemiring R] (S : Set K) :
    Module.Basis (nonnegOutside S) R (partiallyLaurent R S) :=
  (AddMonoidAlgebra.basis (nonnegOutside S) R).map partiallyLaurentEquiv.toLinearEquiv

@[simp]
theorem coe_partiallyLaurentBasis_apply (m : nonnegOutside S) :
    (partiallyLaurentBasis R S m : LaurentRing R K) =
      AddMonoidAlgebra.single (m : K →₀ ℤ) 1 := by
  simp [partiallyLaurentBasis, AddMonoidAlgebra.basis_apply, partialInclusion_apply]

@[simp]
theorem coeff_partiallyLaurentEquiv_symm (f : partiallyLaurent R S) (m : nonnegOutside S) :
    (partiallyLaurentEquiv.symm f).coeff m = (f : LaurentRing R K).coeff m := by
  rw [← coeff_partialInclusion, partialInclusion_partiallyLaurentEquiv_symm]

@[simp]
theorem partiallyLaurentBasis_repr_apply (f : partiallyLaurent R S) (m : nonnegOutside S) :
    (partiallyLaurentBasis R S).repr f m = (f : LaurentRing R K).coeff m := by
  simp [partiallyLaurentBasis, AlgEquiv.coe_symm_toLinearEquiv]

/-- Ordinary polynomials belong to every partially Laurent ring. -/
@[simp]
theorem toLaurent_mem_partiallyLaurent (p : MvPolynomial K R) :
    MvPolynomial.toLaurent p ∈ partiallyLaurent R S := by
  apply partiallyLaurent_mono (R := R) (Set.empty_subset S)
  rw [partiallyLaurent_empty]
  exact MvPolynomial.toLaurent.mem_range_self p

/-- The canonical polynomial map into the partially Laurent ring. -/
noncomputable def toPartiallyLaurent : MvPolynomial K R →ₐ[R] partiallyLaurent R S :=
  MvPolynomial.toLaurent.codRestrict (partiallyLaurent R S) toLaurent_mem_partiallyLaurent

@[simp]
theorem coe_toPartiallyLaurent (p : MvPolynomial K R) :
    (toPartiallyLaurent (S := S) p : LaurentRing R K) = MvPolynomial.toLaurent p := (rfl)

theorem toPartiallyLaurent_injective :
    Function.Injective (toPartiallyLaurent : MvPolynomial K R → partiallyLaurent R S) :=
  fun _ _ h ↦ MvPolynomial.toLaurent_injective (by simpa using congrArg Subtype.val h)

@[simp]
theorem toPartiallyLaurent_inj {p q : MvPolynomial K R} :
    toPartiallyLaurent (S := S) p = toPartiallyLaurent q ↔ p = q :=
  toPartiallyLaurent_injective.eq_iff

@[simp]
theorem toPartiallyLaurent_eq_zero {p : MvPolynomial K R} :
    toPartiallyLaurent (S := S) p = 0 ↔ p = 0 :=
  map_eq_zero_iff _ toPartiallyLaurent_injective

/-- Polynomial inclusion is compatible with enlarging the inverted set. -/
@[simp]
theorem inclusion_toPartiallyLaurent {T : Set K} (hST : S ⊆ T) (p : MvPolynomial K R) :
    Subalgebra.inclusion (partiallyLaurent_mono (R := R) hST) (toPartiallyLaurent p) =
      toPartiallyLaurent p := by
  apply Subtype.ext
  simp

/-- Inverting no variables identifies the partially Laurent ring with the polynomial ring. -/
noncomputable def partiallyLaurentEmptyEquiv :
    MvPolynomial K R ≃ₐ[R] partiallyLaurent R (∅ : Set K) :=
  (AlgEquiv.ofInjective MvPolynomial.toLaurent MvPolynomial.toLaurent_injective).trans
    (Subalgebra.equivOfEq _ _ partiallyLaurent_empty.symm)

@[simp]
theorem partiallyLaurentEmptyEquiv_apply (p : MvPolynomial K R) :
    partiallyLaurentEmptyEquiv p = toPartiallyLaurent (S := ∅) p := by
  apply Subtype.ext
  simp [partiallyLaurentEmptyEquiv, AlgEquiv.ofInjective_apply, coe_toPartiallyLaurent]

@[simp]
theorem toLaurent_partiallyLaurentEmptyEquiv_symm (f : partiallyLaurent R (∅ : Set K)) :
    MvPolynomial.toLaurent (partiallyLaurentEmptyEquiv.symm f) = (f : LaurentRing R K) := by
  rw [← coe_toPartiallyLaurent, ← partiallyLaurentEmptyEquiv_apply, AlgEquiv.apply_symm_apply]

@[simp]
theorem coeff_partiallyLaurentEmptyEquiv_symm (f : partiallyLaurent R (∅ : Set K))
    (n : K →₀ ℕ) :
    (partiallyLaurentEmptyEquiv.symm f).coeff n =
      (f : LaurentRing R K).coeff (n.mapRange Nat.cast Nat.cast_zero) := by
  rw [← MvPolynomial.coeff_toLaurent, toLaurent_partiallyLaurentEmptyEquiv_symm]

/-- Every element of a partially Laurent ring has a polynomial numerator and a denominator
monomial supported entirely on the inverted variables. -/
theorem exists_coe_mul_toLaurent_monomial (f : partiallyLaurent R S) :
    ∃ n : K →₀ ℕ, (∀ i ∉ S, n i = 0) ∧ ∃ p : MvPolynomial K R,
      (f : LaurentRing R K) * MvPolynomial.toLaurent (MvPolynomial.monomial n 1) =
        MvPolynomial.toLaurent p := by
  obtain ⟨n, p, hp, hn⟩ := exists_mul_toLaurent_monomial (f : LaurentRing R K)
  exact ⟨n, fun i hi ↦ hn i (fun m hm ↦ mem_partiallyLaurent_iff.1 f.property m hm i hi),
    p, hp⟩

/-- The multiplicative submonoid of polynomials generated by the variables indexed by `S`. -/
noncomputable def partialDenominators (R : Type*) [CommSemiring R] (S : Set K) :
    Submonoid (MvPolynomial K R) :=
  Submonoid.closure (MvPolynomial.X '' S)

theorem partialDenominators_def :
    partialDenominators R S = Submonoid.closure (MvPolynomial.X '' S) := (rfl)

theorem X_mem_partialDenominators {i : K} (hi : i ∈ S) :
    MvPolynomial.X i ∈ partialDenominators R S := Submonoid.subset_closure ⟨i, hi, rfl⟩

/-- A monoid map sends every allowed denominator to a unit whenever it sends each
selected variable to a unit. The target monoid need not be commutative. -/
theorem isUnit_map_of_mem_partialDenominators {M F : Type*} [Monoid M]
    [FunLike F (MvPolynomial K R) M] [MonoidHomClass F (MvPolynomial K R) M]
    (f : F) (hf : ∀ i ∈ S, IsUnit (f (MvPolynomial.X i)))
    {p : MvPolynomial K R} (hp : p ∈ partialDenominators R S) : IsUnit (f p) :=
  ((Submonoid.closure_le (S := (IsUnit.submonoid M).comap (f : MvPolynomial K R →* M))).mpr
    (by rintro _ ⟨i, hi, rfl⟩; exact hf i hi)) hp

/-- Every monic monomial supported on the inverted variables is an allowed denominator. -/
theorem monomial_mem_partialDenominators {n : K →₀ ℕ} (hn : ∀ i ∉ S, n i = 0) :
    MvPolynomial.monomial n (1 : R) ∈ partialDenominators R S := by
  classical
  rw [MvPolynomial.monomial_eq, MvPolynomial.C_1, one_mul]
  refine Submonoid.prod_mem _ fun i hi ↦ pow_mem (Submonoid.subset_closure ?_) _
  refine ⟨i, ?_, rfl⟩
  by_contra h
  exact Finsupp.mem_support_iff.1 hi (hn i h)

/-- Allowed denominators are exactly monic monomials supported on the selected variables. -/
theorem mem_partialDenominators_iff (p : MvPolynomial K R) :
    p ∈ partialDenominators R S ↔
      ∃ n : K →₀ ℕ, (∀ i ∉ S, n i = 0) ∧ p = MvPolynomial.monomial n 1 := by
  classical
  constructor
  · rw [partialDenominators_def]
    intro hp
    induction hp using Submonoid.closure_induction with
    | mem p hp =>
      obtain ⟨i, hi, rfl⟩ := hp
      exact ⟨Finsupp.single i 1, fun j hj ↦ by
        simp [show i ≠ j from fun h ↦ hj (h ▸ hi)], by simp [MvPolynomial.X]⟩
    | one => exact ⟨0, by simp, by simp⟩
    | mul p q _ _ hp hq =>
      obtain ⟨n, hn, rfl⟩ := hp
      obtain ⟨m, hm, rfl⟩ := hq
      exact ⟨n + m, fun i hi ↦ by simp [hn i hi, hm i hi], by simp⟩
  · rintro ⟨n, hn, rfl⟩
    exact monomial_mem_partialDenominators hn

/-- An inverted variable is a unit already in the partially Laurent ring. -/
noncomputable def partialUnitX (i : S) : (partiallyLaurent R S)ˣ where
  val := ⟨X i, X_mem_partiallyLaurent (R := R) (S := S) (i : K)⟩
  inv := ⟨((unitX i)⁻¹ : (LaurentRing R K)ˣ).val, val_inv_unitX_mem_partiallyLaurent i.property⟩
  val_inv := by
    apply Subtype.ext
    simp only [Subalgebra.coe_mul, Subalgebra.coe_one, ← val_unitX, Units.mul_inv]
  inv_val := by
    apply Subtype.ext
    simp only [Subalgebra.coe_mul, Subalgebra.coe_one, ← val_unitX, Units.inv_mul]

@[simp]
theorem val_partialUnitX (i : S) :
    (partialUnitX (R := R) i : partiallyLaurent R S) =
      toPartiallyLaurent (MvPolynomial.X (i : K)) := by
  apply Subtype.ext
  simp [partialUnitX]

/-- A selected variable is a unit in the partially Laurent ring. -/
theorem isUnit_toPartiallyLaurent_X {i : K} (hi : i ∈ S) :
    IsUnit (toPartiallyLaurent (S := S) (MvPolynomial.X i) : partiallyLaurent R S) :=
  ⟨partialUnitX ⟨i, hi⟩, val_partialUnitX _⟩

@[simp]
theorem toPartiallyLaurent_X_mul_val_inv_partialUnitX (i : S) :
    toPartiallyLaurent (MvPolynomial.X (i : K)) *
      (((partialUnitX (R := R) i)⁻¹).val : partiallyLaurent R S) = 1 := by
  rw [← val_partialUnitX]
  exact Units.mul_inv _

@[simp]
theorem val_inv_partialUnitX_mul_toPartiallyLaurent_X (i : S) :
    (((partialUnitX (R := R) i)⁻¹).val : partiallyLaurent R S) *
      toPartiallyLaurent (MvPolynomial.X (i : K)) = 1 := by
  rw [← val_partialUnitX]
  exact Units.inv_mul _

@[simp]
theorem coe_val_inv_partialUnitX (i : S) :
    (((partialUnitX (R := R) i)⁻¹).val : LaurentRing R K) = ((unitX (i : K))⁻¹).val := (rfl)

@[simp]
theorem coe_val_partialUnitX_zpow (i : S) (n : ℤ) :
    (((partialUnitX (R := R) i) ^ n).val : LaurentRing R K) =
      ((unitX (i : K) ^ n : (LaurentRing R K)ˣ) : LaurentRing R K) := by
  let f := Units.map (partiallyLaurent R S).val.toMonoidHom
  have h : f (partialUnitX i) = unitX (R := R) (i : K) := by
    apply Units.ext
    simp [f]
  simp [← h, ← map_zpow, f]

/-- Enlarging the inverted set preserves the chosen variable units. -/
@[simp]
theorem map_inclusion_partialUnitX {T : Set K} (hST : S ⊆ T) (i : S) :
    Units.map (Subalgebra.inclusion (partiallyLaurent_mono (R := R) hST) :
      partiallyLaurent R S →* partiallyLaurent R T) (partialUnitX i) =
      partialUnitX ⟨(i : K), hST i.property⟩ := by
  apply Units.ext
  simp only [Units.coe_map, AlgHom.coe_toMonoidHom, val_partialUnitX]
  exact inclusion_toPartiallyLaurent hST _

@[simp]
theorem inclusion_val_inv_partialUnitX {T : Set K} (hST : S ⊆ T) (i : S) :
    Subalgebra.inclusion (partiallyLaurent_mono (R := R) hST) ((partialUnitX i)⁻¹).val =
      ((partialUnitX (R := R) ⟨(i : K), hST i.property⟩)⁻¹).val := by
  apply Subtype.ext
  simp

@[simp]
theorem inclusion_val_partialUnitX_zpow {T : Set K} (hST : S ⊆ T) (i : S) (n : ℤ) :
    Subalgebra.inclusion (partiallyLaurent_mono (R := R) hST) ((partialUnitX i)^n).val =
      ((partialUnitX (R := R) ⟨(i : K), hST i.property⟩)^n).val := by
  apply Subtype.ext
  simp

/-- The partially Laurent ring carries the canonical polynomial-algebra structure. -/
noncomputable instance partialAlgebraMvPolynomial :
    Algebra (MvPolynomial K R) (partiallyLaurent R S) :=
  (toPartiallyLaurent : MvPolynomial K R →ₐ[R] partiallyLaurent R S).toRingHom.toAlgebra

@[simp]
theorem algebraMap_eq_toPartiallyLaurent (p : MvPolynomial K R) :
    algebraMap (MvPolynomial K R) (partiallyLaurent R S) p = toPartiallyLaurent p := (rfl)

instance : IsScalarTower R (MvPolynomial K R) (partiallyLaurent R S) :=
  .of_algebraMap_eq fun r ↦ by simp

instance : IsScalarTower (MvPolynomial K R) (partiallyLaurent R S) (LaurentRing R K) :=
  .of_algebraMap_eq fun p ↦ by simp

/-- The partially Laurent ring is exactly the localization of polynomials at
the chosen variables. This holds for an arbitrary, possibly infinite inverted set. -/
instance isLocalization_partiallyLaurent :
    IsLocalization (partialDenominators R S) (partiallyLaurent R S) where
  map_units y := isUnit_map_of_mem_partialDenominators
    (algebraMap (MvPolynomial K R) (partiallyLaurent R S))
    (fun _ hi ↦ isUnit_toPartiallyLaurent_X hi) y.property
  surj f := by
    obtain ⟨n, hn, p, hp⟩ := exists_coe_mul_toLaurent_monomial f
    refine ⟨(p, ⟨MvPolynomial.monomial n 1, monomial_mem_partialDenominators hn⟩), ?_⟩
    apply Subtype.ext
    simpa using hp
  exists_of_eq h := ⟨1, by
    simpa using (toPartiallyLaurent_injective (S := S)
      (by simpa only [algebraMap_eq_toPartiallyLaurent] using h))⟩

/-- Enlarging the inverted set localizes at precisely the newly inverted variables. -/
theorem isLocalization_partiallyLaurent_of_subset {T : Set K} (hST : S ⊆ T) :
    letI := (Subalgebra.inclusion (partiallyLaurent_mono (R := R) hST)).toRingHom.toAlgebra
    IsLocalization
      (Algebra.algebraMapSubmonoid (partiallyLaurent R S) (partialDenominators R (T \ S)))
      (partiallyLaurent R T) := by
  let := (Subalgebra.inclusion (partiallyLaurent_mono (R := R) hST)).toRingHom.toAlgebra
  have : IsScalarTower (MvPolynomial K R) (partiallyLaurent R S) (partiallyLaurent R T) :=
    .of_algebraMap_eq fun p ↦ Subtype.ext (by simp [RingHom.algebraMap_toAlgebra])
  have hden : partialDenominators R S ≤ partialDenominators R T :=
    Submonoid.closure_mono (Set.image_mono hST)
  have : IsLocalization
      (Algebra.algebraMapSubmonoid (partiallyLaurent R T) (partialDenominators R S))
      (partiallyLaurent R T) := by
    apply IsLocalization.of_le_isUnit
    rintro _ ⟨p, hp, rfl⟩
    exact IsLocalization.map_units (partiallyLaurent R T) ⟨p, hden hp⟩
  let M := Algebra.algebraMapSubmonoid (partiallyLaurent R S) (partialDenominators R (T \ S))
  let N := Algebra.algebraMapSubmonoid (partiallyLaurent R S) (partialDenominators R T)
  have : IsLocalization N (partiallyLaurent R T) :=
    IsLocalization.commutes (partiallyLaurent R S) (partiallyLaurent R T)
      (partiallyLaurent R T) (partialDenominators R S) (partialDenominators R T)
  have hMN : M ≤ N := by
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨p, Submonoid.closure_mono (Set.image_mono Set.sdiff_subset) hp, rfl⟩
  have hdiv : ∀ n ∈ N, ∃ m ∈ M, n ∣ m := by
    rintro _ ⟨p, hp, rfl⟩
    rw [partialDenominators] at hp
    induction hp using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨i, hiT, rfl⟩ := hx
      by_cases hiS : i ∈ S
      · have hu := IsLocalization.map_units (partiallyLaurent R S)
          (⟨MvPolynomial.X i, Submonoid.subset_closure ⟨i, hiS, rfl⟩⟩ : partialDenominators R S)
        exact ⟨1, M.one_mem, isUnit_iff_dvd_one.mp hu⟩
      · exact ⟨_, ⟨MvPolynomial.X i, Submonoid.subset_closure ⟨i, ⟨hiT, hiS⟩, rfl⟩, rfl⟩,
          dvd_refl _⟩
    | one => exact ⟨1, M.one_mem, by simp⟩
    | mul x y _ _ hx hy =>
      obtain ⟨m, hm, hxm⟩ := hx
      obtain ⟨n, hn, hyn⟩ := hy
      exact ⟨m * n, M.mul_mem hm hn, by simpa only [map_mul] using mul_dvd_mul hxm hyn⟩
  exact (IsLocalization.iff_of_le_of_exists_dvd M N hMN hdiv).mpr inferInstance

section Evaluation

variable {A : Type*} [Semiring A] [Algebra R A]

/-- Algebra maps out of a partially Laurent ring are determined by the polynomial variables.
The target algebra need not be commutative. -/
@[ext high + 1]
theorem partialAlgHom_ext {f g : partiallyLaurent R S →ₐ[R] A}
    (h : ∀ i, f (toPartiallyLaurent (MvPolynomial.X i)) =
      g (toPartiallyLaurent (MvPolynomial.X i))) : f = g :=
  IsLocalization.algHom_ext (partialDenominators R S) (MvPolynomial.algHom_ext h)

end Evaluation

section Aeval

variable {A : Type*} [CommSemiring A]

/-- The ring-hom localization lift evaluates the polynomial inclusion as prescribed. -/
@[simp]
theorem lift_toPartiallyLaurent (f : MvPolynomial K R →+* A)
    (hf : ∀ y : partialDenominators R S, IsUnit (f y)) (p : MvPolynomial K R) :
    (IsLocalization.lift hf : partiallyLaurent R S →+* A) (toPartiallyLaurent p) = f p := by
  have h := IsLocalization.lift_eq (S := partiallyLaurent R S) hf p
  rw [algebraMap_eq_toPartiallyLaurent] at h
  exact h

/-- Over any scalar-tower base, the localization lift evaluates the polynomial
inclusion as prescribed. -/
@[simp]
theorem liftAlgHom_toPartiallyLaurent {R₀ : Type*} [CommSemiring R₀]
    [Algebra R₀ (MvPolynomial K R)] [Algebra R₀ (partiallyLaurent R S)]
    [IsScalarTower R₀ (MvPolynomial K R) (partiallyLaurent R S)] [Algebra R₀ A]
    (f : MvPolynomial K R →ₐ[R₀] A)
    (hf : ∀ y : partialDenominators R S, IsUnit (f y)) (p : MvPolynomial K R) :
    (IsLocalization.liftAlgHom hf : partiallyLaurent R S →ₐ[R₀] A) (toPartiallyLaurent p) =
      f p :=
  (IsLocalization.liftAlgHom_apply _ _).trans (lift_toPartiallyLaurent (f : _ →+* A) hf p)

variable [Algebra R A]

/-- Evaluate at arbitrary elements of a commutative algebra, with units required only for
selected variables. Commutativity ensures the prescribed elements define a polynomial map. -/
noncomputable def partialAeval (x : K → A) (hx : ∀ i ∈ S, IsUnit (x i)) :
    partiallyLaurent R S →ₐ[R] A :=
  IsLocalization.liftAlgHom (M := partialDenominators R S) (f := MvPolynomial.aeval x)
    (fun y ↦ isUnit_map_of_mem_partialDenominators (MvPolynomial.aeval x)
      (fun i hi ↦ by simpa using hx i hi) y.property)

/-- Partial evaluation extends the usual polynomial evaluation. -/
@[simp]
theorem partialAeval_toPartiallyLaurent (x : K → A) (hx : ∀ i ∈ S, IsUnit (x i))
    (p : MvPolynomial K R) :
    partialAeval (R := R) x hx (toPartiallyLaurent p) = MvPolynomial.aeval x p := by
  simp [partialAeval]

/-- The image of a selected variable as a unit is the unit specified by its value. -/
@[simp]
theorem map_partialAeval_partialUnitX (x : K → A) (hx : ∀ i ∈ S, IsUnit (x i)) (i : S) :
    Units.map (partialAeval (R := R) x hx : partiallyLaurent R S →* A) (partialUnitX i) =
      (hx i i.property).unit := by
  apply Units.ext
  simp

/-- Partial evaluation sends an inverted variable to the inverse of its prescribed unit. -/
@[simp]
theorem partialAeval_val_inv_partialUnitX (x : K → A) (hx : ∀ i ∈ S, IsUnit (x i)) (i : S) :
    partialAeval (R := R) x hx ((partialUnitX i)⁻¹).val = ((hx i i.property).unit⁻¹).val := by
  have h := congrArg (fun u : Aˣ ↦ (u⁻¹).val)
    (map_partialAeval_partialUnitX (R := R) x hx i)
  rw [← map_inv] at h
  simpa only [Units.coe_map, AlgHom.coe_toMonoidHom] using h

/-- Partial evaluation carries integer powers of selected variables to their unit powers. -/
@[simp]
theorem partialAeval_val_partialUnitX_zpow (x : K → A) (hx : ∀ i ∈ S, IsUnit (x i))
    (i : S) (n : ℤ) :
    partialAeval (R := R) x hx ((partialUnitX i ^ n).val) =
      (((hx i i.property).unit ^ n : Aˣ) : A) := by
  have h := congrArg (fun u : Aˣ ↦ (u ^ n).val)
    (map_partialAeval_partialUnitX (R := R) x hx i)
  rw [← map_zpow] at h
  simpa only [Units.coe_map, AlgHom.coe_toMonoidHom] using h

/-- Values on polynomial variables uniquely specify the partial evaluation map. -/
theorem partialAeval_unique (f : partiallyLaurent R S →ₐ[R] A) (x : K → A)
    (hx : ∀ i ∈ S, IsUnit (x i))
    (h : ∀ i, f (toPartiallyLaurent (MvPolynomial.X i)) = x i) : f = partialAeval (R := R) x hx :=
  partialAlgHom_ext fun i ↦ by simp [h]

/-- Full Laurent evaluation restricts to the corresponding partial evaluation. -/
theorem aeval_comp_partiallyLaurent_val (x : K → Aˣ) :
    (aeval (R := R) x).comp (partiallyLaurent R S).val =
      partialAeval (R := R) (fun i ↦ (x i : A)) (fun i _ ↦ (x i).isUnit) := by
  apply partialAlgHom_ext
  intro i
  simp

/-- Enlarging the inverted set commutes with evaluation whenever the new variables are units. -/
theorem partialAeval_comp_inclusion {T : Set K} (hST : S ⊆ T) (x : K → A)
    (hx : ∀ i ∈ T, IsUnit (x i)) :
    (partialAeval (R := R) x hx).comp (Subalgebra.inclusion (partiallyLaurent_mono (R := R) hST)) =
      partialAeval (R := R) x (fun i hi ↦ hx i (hST hi)) :=
  partialAlgHom_ext fun i ↦ by
    simp only [AlgHom.comp_apply]
    rw [inclusion_toPartiallyLaurent (R := R) hST]
    simp

/-- Full evaluation on an element of the partial ring agrees with partial evaluation. -/
@[simp]
theorem aeval_coe_partiallyLaurent (x : K → Aˣ) (p : partiallyLaurent R S) :
    aeval (R := R) x (p : LaurentRing R K) =
      partialAeval (R := R) (fun i ↦ (x i : A)) (fun i _ ↦ (x i).isUnit) p :=
  DFunLike.congr_fun (aeval_comp_partiallyLaurent_val x) p

/-- Partial evaluation commutes with inclusion in a larger partial ring. -/
@[simp]
theorem partialAeval_inclusion {T : Set K} (hST : S ⊆ T) (x : K → A)
    (hx : ∀ i ∈ T, IsUnit (x i)) (p : partiallyLaurent R S) :
    partialAeval (R := R) x hx (Subalgebra.inclusion (partiallyLaurent_mono hST) p) =
      partialAeval (R := R) x (fun i hi ↦ hx i (hST hi)) p :=
  DFunLike.congr_fun (partialAeval_comp_inclusion hST x hx) p

/-- Evaluation at the partial ring's own variables is the identity. -/
@[simp]
theorem partialAeval_X_left :
    partialAeval (R := R) (fun i ↦ toPartiallyLaurent (MvPolynomial.X i))
      (fun _ hi ↦ isUnit_toPartiallyLaurent_X hi) = AlgHom.id R (partiallyLaurent R S) :=
  partialAlgHom_ext fun _ ↦ by simp

/-- Partial evaluation is natural under algebra homomorphisms of the target. -/
theorem comp_partialAeval {B : Type*} [CommSemiring B] [Algebra R B]
    (φ : A →ₐ[R] B) (x : K → A) (hx : ∀ i ∈ S, IsUnit (x i)) :
    φ.comp (partialAeval (R := R) x hx) =
      partialAeval (R := R) (fun i ↦ φ (x i)) (fun i hi ↦ (hx i hi).map φ) :=
  partialAlgHom_ext fun _ ↦ by simp

end Aeval

/-- A subalgebra contains the partial ring exactly when it contains every variable and
the inverse of each selected variable. -/
theorem partiallyLaurent_le_iff (B : Subalgebra R (LaurentRing R K)) :
    partiallyLaurent R S ≤ B ↔
      (∀ i, (X i : LaurentRing R K) ∈ B) ∧
        ∀ i ∈ S, ((unitX i)⁻¹ : (LaurentRing R K)ˣ).val ∈ B := by
  constructor
  · intro h
    exact ⟨fun i ↦ h (X_mem_partiallyLaurent i),
      fun _ hi ↦ h (val_inv_unitX_mem_partiallyLaurent hi)⟩
  · rintro ⟨hX, hInv⟩
    let x (i : K) : B := ⟨X i, hX i⟩
    have hx (i : K) (hi : i ∈ S) : IsUnit (x i) := by
      refine ⟨⟨x i, ⟨((unitX i)⁻¹).val, hInv i hi⟩, ?_, ?_⟩, rfl⟩
      · apply Subtype.ext
        simpa only [Subalgebra.coe_mul, Subalgebra.coe_one, x, ← val_unitX] using
          Units.mul_inv (unitX (R := R) i)
      · apply Subtype.ext
        simpa only [Subalgebra.coe_mul, Subalgebra.coe_one, x, ← val_unitX] using
          Units.inv_mul (unitX (R := R) i)
    let f := partialAeval (R := R) x hx
    have hf : B.val.comp f = (partiallyLaurent R S).val :=
      partialAlgHom_ext fun _ ↦ by simp [f, x]
    intro p hp
    have h := DFunLike.congr_fun hf (⟨p, hp⟩ : partiallyLaurent R S)
    have hval : (f ⟨p, hp⟩ : LaurentRing R K) = p := h
    rw [← hval]
    exact (f ⟨p, hp⟩).property

/-- Variables and the selected inverse variables generate the partial ring as an algebra. -/
theorem partiallyLaurent_eq_adjoin :
    partiallyLaurent R S = Algebra.adjoin R
      (Set.range (X : K → LaurentRing R K) ∪
        (fun i ↦ ((unitX i)⁻¹ : (LaurentRing R K)ˣ).val) '' S) := by
  apply le_antisymm
  · apply (partiallyLaurent_le_iff _).2
    exact ⟨fun i ↦ Algebra.subset_adjoin (Or.inl ⟨i, rfl⟩),
      fun i hi ↦ Algebra.subset_adjoin (Or.inr ⟨i, hi, rfl⟩)⟩
  · apply Algebra.adjoin_le
    rintro _ (⟨i, rfl⟩ | ⟨i, hi, rfl⟩)
    · exact X_mem_partiallyLaurent i
    · exact val_inv_unitX_mem_partiallyLaurent hi


section Coefficients

variable {A B : Type*} [CommSemiring A] [CommSemiring B]

/-- Changing coefficients preserves the exponent condition, even for noninjective maps. -/
theorem mapRingHom_mem_partiallyLaurent (φ : R →+* A) {f : LaurentRing R K}
    (hf : f ∈ partiallyLaurent R S) :
    AddMonoidAlgebra.mapRingHom (K →₀ ℤ) φ f ∈ partiallyLaurent A S := by
  rw [partiallyLaurent, AlgHom.mem_range] at hf ⊢
  obtain ⟨p, rfl⟩ := hf
  refine ⟨AddMonoidAlgebra.mapRingHom _ φ p, ?_⟩
  simpa [partialInclusion_apply] using DFunLike.congr_fun
      (AddMonoidAlgebra.mapRingHom_comp_mapDomainRingHom φ (nonnegOutside S).subtype).symm p

/-- Coefficient homomorphisms restrict to partially Laurent rings with the same inverted set. -/
noncomputable def partialCoeffMap (φ : R →+* A) :
    partiallyLaurent R S →+* partiallyLaurent A S :=
  (AddMonoidAlgebra.mapRingHom (K →₀ ℤ) φ).restrict
    (partiallyLaurent R S) (partiallyLaurent A S) (fun _ ↦ mapRingHom_mem_partiallyLaurent φ)

@[simp]
theorem coe_partialCoeffMap (φ : R →+* A) (f : partiallyLaurent R S) :
    (partialCoeffMap φ f : LaurentRing A K) = AddMonoidAlgebra.mapRingHom (K →₀ ℤ) φ f := (rfl)

/-- Injective changes of coefficients remain injective on the partially Laurent ring. -/
theorem partialCoeffMap_injective (φ : R →+* A) (hφ : Function.Injective φ) :
    Function.Injective (partialCoeffMap (S := S) φ) := by
  intro f g h
  apply Subtype.ext
  apply AddMonoidAlgebra.map_injective φ.toAddMonoidHom hφ
  simpa only [coe_partialCoeffMap, AddMonoidAlgebra.coe_mapRingHom,
    RingHom.toAddMonoidHom_eq_coe] using congrArg Subtype.val h

@[simp]
theorem partialCoeffMap_id : partialCoeffMap (S := S) (RingHom.id R) = RingHom.id _ := by
  apply RingHom.ext
  intro f
  apply Subtype.ext
  ext m
  simp

/-- Restricting coefficient maps is compatible with their composition. -/
theorem partialCoeffMap_comp (φ : R →+* A) (ψ : A →+* B) :
    (partialCoeffMap (S := S) ψ).comp (partialCoeffMap φ) = partialCoeffMap (ψ.comp φ) := by
  apply RingHom.ext
  intro f
  apply Subtype.ext
  ext m
  simp

@[simp]
theorem partialCoeffMap_partialCoeffMap (φ : R →+* A) (ψ : A →+* B)
    (f : partiallyLaurent R S) :
    partialCoeffMap ψ (partialCoeffMap φ f) = partialCoeffMap (ψ.comp φ) f :=
  DFunLike.congr_fun (partialCoeffMap_comp φ ψ) f

/-- Coefficient change commutes with the polynomial inclusion into a partially Laurent ring. -/
@[simp]
theorem partialCoeffMap_toPartiallyLaurent (φ : R →+* A) (p : MvPolynomial K R) :
    partialCoeffMap (S := S) φ (toPartiallyLaurent p) =
      toPartiallyLaurent (S := S) (MvPolynomial.map φ p) := by
  apply Subtype.ext
  simp [MvPolynomial.toLaurent_map]

/-- Coefficient change preserves the selected variable units. -/
@[simp]
theorem map_partialCoeffMap_partialUnitX (φ : R →+* A) (i : S) :
    Units.map (↑(partialCoeffMap (S := S) φ) :
      partiallyLaurent R S →* partiallyLaurent A S)
      (partialUnitX i) = partialUnitX i := by
  apply Units.ext
  simp

@[simp]
theorem partialCoeffMap_val_inv_partialUnitX (φ : R →+* A) (i : S) :
    partialCoeffMap φ ((partialUnitX i)⁻¹).val = ((partialUnitX (R := A) i)⁻¹).val := by
  have h := congrArg (fun u : (partiallyLaurent A S)ˣ ↦ (u⁻¹).val)
    (map_partialCoeffMap_partialUnitX φ i)
  simpa only [← map_inv, Units.coe_map, RingHom.toMonoidHom_eq_coe,
    MonoidHom.coe_ofClass] using h

@[simp]
theorem partialCoeffMap_val_partialUnitX_zpow (φ : R →+* A) (i : S) (n : ℤ) :
    partialCoeffMap φ ((partialUnitX i)^n).val = ((partialUnitX (R := A) i)^n).val := by
  have h := congrArg (fun u : (partiallyLaurent A S)ˣ ↦ (u^n).val)
    (map_partialCoeffMap_partialUnitX φ i)
  simpa only [← map_zpow, Units.coe_map, RingHom.toMonoidHom_eq_coe,
    MonoidHom.coe_ofClass] using h

/-- Changing coefficients preserves each permitted basis monomial. -/
@[simp]
theorem partialCoeffMap_partiallyLaurentBasis (φ : R →+* A) (m : nonnegOutside S) :
    partialCoeffMap φ (partiallyLaurentBasis R S m) =
      partiallyLaurentBasis A S m := by
  apply Subtype.ext
  simp

/-- Enlarging the inverted set commutes with arbitrary coefficient homomorphisms. -/
@[simp]
theorem partialCoeffMap_inclusion (φ : R →+* A) {T : Set K} (hST : S ⊆ T)
    (f : partiallyLaurent R S) :
    partialCoeffMap φ (Subalgebra.inclusion (partiallyLaurent_mono (R := R) hST) f) =
      Subalgebra.inclusion (partiallyLaurent_mono (R := A) hST) (partialCoeffMap φ f) := by
  apply Subtype.ext
  simp

@[simp]
theorem partialCoeffMap_algebraMap (φ : R →+* A) (r : R) :
    partialCoeffMap (S := S) φ (algebraMap R (partiallyLaurent R S) r) =
      algebraMap A (partiallyLaurent A S) (φ r) := by
  apply Subtype.ext
  simp

/-- Evaluation after scalar extension agrees with the original partial evaluation. -/
@[simp]
theorem partialAeval_partialCoeffMap_algebraMap [Algebra R A] [Algebra R B] [Algebra A B]
    [IsScalarTower R A B] (x : K → B) (hx : ∀ i ∈ S, IsUnit (x i))
    (p : partiallyLaurent R S) :
    partialAeval (R := A) x hx (partialCoeffMap (algebraMap R A) p) =
      partialAeval (R := R) x hx p := by
  let f : partiallyLaurent R S →ₐ[R] B :=
    { toRingHom := (partialAeval (R := A) x hx).toRingHom.comp
        (partialCoeffMap (algebraMap R A))
      commutes' := by intro r; simp [IsScalarTower.algebraMap_apply R A B] }
  exact DFunLike.congr_fun (partialAlgHom_ext (f := f) fun _ ↦ by simp [f]) p

end Coefficients

section Renaming

variable {K' K'' : Type*} {T : Set K'} {U : Set K''}

/-- Renaming preserves the exponent condition when selected variables remain selected.
The variable map can identify different variables. -/
theorem rename_mem_partiallyLaurent {f : K → K'} (hST : Set.MapsTo f S T)
    {p : LaurentRing R K} (hp : p ∈ partiallyLaurent R S) :
    rename f p ∈ partiallyLaurent R T := by
  let g : partiallyLaurent R S →ₐ[R] partiallyLaurent R T :=
    partialAeval (R := R) (fun i ↦ toPartiallyLaurent (MvPolynomial.X (f i)))
      (fun i hi ↦ isUnit_toPartiallyLaurent_X (hST hi))
  have heq : (partiallyLaurent R T).val.comp g =
      (rename f).comp (partiallyLaurent R S).val := by
    apply partialAlgHom_ext
    intro i
    simp [g]
  have hval := DFunLike.congr_fun heq (⟨p, hp⟩ : partiallyLaurent R S)
  simp only [AlgHom.comp_apply, Subalgebra.val_apply] at hval
  exact hval ▸ (g ⟨p, hp⟩).property

/-- Restrict variable renaming to the chosen partially Laurent rings. -/
noncomputable def partialRename (f : K → K') (hST : Set.MapsTo f S T) :
    partiallyLaurent R S →ₐ[R] partiallyLaurent R T :=
  ((rename f).comp (partiallyLaurent R S).val).codRestrict (partiallyLaurent R T)
    (fun p ↦ rename_mem_partiallyLaurent hST p.property)

@[simp]
theorem coe_partialRename (f : K → K') (hST : Set.MapsTo f S T) (p : partiallyLaurent R S) :
    (partialRename f hST p : LaurentRing R K') = rename f (p : LaurentRing R K) := by
  simpa only [partialRename, AlgHom.comp_apply, Subalgebra.val_apply] using
    (AlgHom.coe_codRestrict ((rename f).comp (partiallyLaurent R S).val)
      (partiallyLaurent R T) (fun p ↦ rename_mem_partiallyLaurent hST p.property) p)

/-- Renaming commutes with the canonical polynomial map. -/
@[simp]
theorem partialRename_toPartiallyLaurent (f : K → K') (hST : Set.MapsTo f S T)
    (p : MvPolynomial K R) :
    partialRename f hST (toPartiallyLaurent p) =
      toPartiallyLaurent (MvPolynomial.rename f p) := by
  apply Subtype.ext
  simp [rename_toLaurent]

/-- Injective variable maps restrict to injective maps on partial rings. -/
theorem partialRename_injective {f : K → K'} (hf : Function.Injective f)
    (hST : Set.MapsTo f S T) : Function.Injective (partialRename (R := R) f hST) := by
  intro p q h
  exact Subtype.ext (rename_injective hf (by simpa using congrArg Subtype.val h))

/-- Renaming carries a selected variable unit to the selected image unit. -/
@[simp]
theorem map_partialRename_partialUnitX (f : K → K') (hST : Set.MapsTo f S T) (i : S) :
    Units.map (partialRename (R := R) f hST : partiallyLaurent R S →* partiallyLaurent R T)
      (partialUnitX i) = partialUnitX ⟨f i, hST i.property⟩ := by
  apply Units.ext
  simp

@[simp]
theorem partialRename_val_inv_partialUnitX (f : K → K') (hST : Set.MapsTo f S T) (i : S) :
    partialRename (R := R) f hST ((partialUnitX i)⁻¹).val =
      ((partialUnitX (R := R) ⟨f i, hST i.property⟩)⁻¹).val := by
  have h := congrArg (fun u : (partiallyLaurent R T)ˣ ↦ (u⁻¹).val)
    (map_partialRename_partialUnitX f hST i)
  simpa only [← map_inv, Units.coe_map, AlgHom.coe_toMonoidHom] using h

@[simp]
theorem partialRename_val_partialUnitX_zpow (f : K → K') (hST : Set.MapsTo f S T)
    (i : S) (n : ℤ) :
    partialRename (R := R) f hST ((partialUnitX i)^n).val =
      ((partialUnitX (R := R) ⟨f i, hST i.property⟩)^n).val := by
  have h := congrArg (fun u : (partiallyLaurent R T)ˣ ↦ (u^n).val)
    (map_partialRename_partialUnitX f hST i)
  simpa only [← map_zpow, Units.coe_map, AlgHom.coe_toMonoidHom] using h

/-- Evaluating renamed variables is evaluation at their prescribed images. -/
theorem partialAeval_comp_partialRename {A : Type*} [CommSemiring A] [Algebra R A]
    (f : K → K') (hST : Set.MapsTo f S T) (x : K' → A)
    (hx : ∀ i ∈ T, IsUnit (x i)) :
    (partialAeval (R := R) x hx).comp (partialRename f hST) =
      partialAeval (R := R) (x ∘ f) (fun i hi ↦ hx (f i) (hST hi)) :=
  partialAlgHom_ext fun _ ↦ by simp

@[simp]
theorem partialAeval_partialRename {A : Type*} [CommSemiring A] [Algebra R A]
    (f : K → K') (hST : Set.MapsTo f S T) (x : K' → A)
    (hx : ∀ i ∈ T, IsUnit (x i)) (p : partiallyLaurent R S) :
    partialAeval (R := R) x hx (partialRename f hST p) =
      partialAeval (R := R) (x ∘ f) (fun i hi ↦ hx (f i) (hST hi)) p :=
  DFunLike.congr_fun (partialAeval_comp_partialRename f hST x hx) p

@[simp]
theorem partialRename_id :
    partialRename (R := R) (S := S) id (Set.mapsTo_id S) = AlgHom.id R (partiallyLaurent R S) :=
  partialAlgHom_ext fun _ ↦ by simp

/-- Composition of variable maps gives composition of the restricted renamings. -/
theorem partialRename_comp (f : K → K') (g : K' → K'')
    (hST : Set.MapsTo f S T) (hTU : Set.MapsTo g T U) :
    (partialRename (R := R) g hTU).comp (partialRename f hST) =
      partialRename (g ∘ f) (hTU.comp hST) :=
  partialAlgHom_ext fun _ ↦ by simp

@[simp]
theorem partialRename_partialRename (f : K → K') (g : K' → K'')
    (hST : Set.MapsTo f S T) (hTU : Set.MapsTo g T U) (p : partiallyLaurent R S) :
    partialRename g hTU (partialRename f hST p) =
      partialRename (g ∘ f) (hTU.comp hST) p :=
  DFunLike.congr_fun (partialRename_comp f g hST hTU) p

/-- A bijection of variables reindexes the selected variables by its image. -/
noncomputable def partialRenameEquiv (R : Type*) [CommSemiring R] (S : Set K) (e : K ≃ K') :
    partiallyLaurent R S ≃ₐ[R] partiallyLaurent R (e '' S) :=
  AlgEquiv.ofAlgHom (partialRename e (Set.mapsTo_image e S))
    (partialRename e.symm (Set.mapsTo_iff_image_subset.mpr (e.symm_image_image S).le))
    (partialAlgHom_ext fun _ ↦ by simp) (partialAlgHom_ext fun _ ↦ by simp)

@[simp]
theorem partialRenameEquiv_apply (e : K ≃ K') (p : partiallyLaurent R S) :
    partialRenameEquiv R S e p = partialRename (T := e '' S) e (Set.mapsTo_image e S) p := by rfl

@[simp]
theorem partialRenameEquiv_symm_apply (e : K ≃ K') (p : partiallyLaurent R (e '' S)) :
    (partialRenameEquiv R S e).symm p =
      partialRename e.symm (Set.mapsTo_iff_image_subset.mpr (e.symm_image_image S).le) p := by
  rfl

theorem coe_partialRenameEquiv_symm_apply (e : K ≃ K') (p : partiallyLaurent R (e '' S)) :
    ((partialRenameEquiv R S e).symm p : LaurentRing R K) =
      rename e.symm (p : LaurentRing R K') := by
  simp

/-- Arbitrary coefficient changes commute with variable renaming on partially Laurent rings. -/
@[simp]
theorem partialCoeffMap_partialRename {A : Type*} [CommSemiring A] (φ : R →+* A)
    (f : K → K') (hST : Set.MapsTo f S T) (p : partiallyLaurent R S) :
    partialCoeffMap φ (partialRename f hST p) = partialRename f hST (partialCoeffMap φ p) := by
  apply Subtype.ext
  simp [mapRingHom_rename]

end Renaming

end TauCeti.LaurentRing
