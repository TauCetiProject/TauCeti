/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MvPolynomial.Laurent.Polynomial
public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.RingTheory.Localization.Basic

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
including noninjective maps.

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
    partialInclusion R S p = AddMonoidAlgebra.mapDomain Subtype.val p := (rfl)

/-- The partially Laurent subalgebra permits negative powers exactly in the variables in `S`. -/
noncomputable def partiallyLaurent : Subalgebra R (LaurentRing R K) :=
  (partialInclusion R S).range

variable {R S}

/-- The monomial realization of the partially Laurent ring is faithful over every coefficient
semiring, including those with zero divisors. -/
theorem partialInclusion_injective : Function.Injective (partialInclusion R S) := by
  exact AddMonoidAlgebra.mapDomain_injective Subtype.val_injective

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
theorem inv_unitX_mem_partiallyLaurent {i : K} (hi : i ∈ S) :
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
  rw [← coeff_partialInclusion]
  have h : partialInclusion R S (partiallyLaurentEquiv.symm f) = (f : LaurentRing R K) := by
    rw [← coe_partiallyLaurentEquiv_apply, AlgEquiv.apply_symm_apply]
  rw [h]

@[simp]
theorem partiallyLaurentBasis_repr_apply (f : partiallyLaurent R S) (m : nonnegOutside S) :
    (partiallyLaurentBasis R S).repr f m = (f : LaurentRing R K).coeff m := by
  simp only [partiallyLaurentBasis, Module.Basis.map_repr, LinearEquiv.trans_apply]
  exact coeff_partiallyLaurentEquiv_symm f m

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
  fun _ _ h ↦ MvPolynomial.toLaurent_injective (congrArg Subtype.val h)

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
  inv := ⟨((unitX i)⁻¹ : (LaurentRing R K)ˣ).val, inv_unitX_mem_partiallyLaurent i.property⟩
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
  rw [← h, ← map_zpow]
  rfl

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
  map_units := by
    rintro ⟨y, hy⟩
    dsimp only
    rw [partialDenominators] at hy
    induction hy using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨i, hi, rfl⟩ := hx
      refine ⟨partialUnitX ⟨i, hi⟩, ?_⟩
      apply Subtype.ext
      simp [partialUnitX, MvPolynomial.toLaurent_X]
    | one => simp
    | mul x y _ _ hx hy => simpa using hx.mul hy
  surj f := by
    obtain ⟨n, hn, p, hp⟩ := exists_coe_mul_toLaurent_monomial f
    refine ⟨(p, ⟨MvPolynomial.monomial n 1, monomial_mem_partialDenominators hn⟩), ?_⟩
    apply Subtype.ext
    simpa using hp
  exists_of_eq h := ⟨1, by simpa using toPartiallyLaurent_injective h⟩

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

section Coefficients

variable {A B : Type*} [CommSemiring A] [CommSemiring B]

/-- Changing coefficients preserves the exponent condition, even for noninjective maps. -/
theorem mapRingHom_mem_partiallyLaurent (φ : R →+* A) {f : LaurentRing R K}
    (hf : f ∈ partiallyLaurent R S) :
    AddMonoidAlgebra.mapRingHom (K →₀ ℤ) φ f ∈ partiallyLaurent A S := by
  rw [partiallyLaurent, AlgHom.mem_range] at hf ⊢
  obtain ⟨p, rfl⟩ := hf
  refine ⟨AddMonoidAlgebra.mapRingHom _ φ p, ?_⟩
  simpa only [RingHom.comp_apply, partialInclusion, AddMonoidAlgebra.mapDomainAlgHom,
    AlgHom.coe_mk] using
    DFunLike.congr_fun
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
  exact AddMonoidAlgebra.map_injective φ.toAddMonoidHom hφ (congrArg Subtype.val h)

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
  rfl

end Coefficients

end TauCeti.LaurentRing
