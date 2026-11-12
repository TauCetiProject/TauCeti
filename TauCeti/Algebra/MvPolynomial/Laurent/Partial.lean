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

The partially Laurent ring inverts exactly a chosen set of variables. It is realized inside
the Laurent ring as the span of monomials with nonnegative exponents outside that set.
The index set and the set of inverted variables may both be infinite; each polynomial still
has finite support. No domain hypothesis on the coefficient ring is needed.

## References

* S. Fomin and A. Zelevinsky, *Cluster algebras IV: Coefficients*, §2.
-/

public section

namespace TauCeti.LaurentRing

variable {K : Type*}

/-- Exponents of monomials whose negative powers use only variables in `S`. -/
def nonnegativeOutside (S : Set K) : AddSubmonoid (K →₀ ℤ) where
  carrier := {m | ∀ i ∉ S, 0 ≤ m i}
  zero_mem' := by simp
  add_mem' hm hn i hi := add_nonneg (hm i hi) (hn i hi)

@[simp]
theorem mem_nonnegativeOutside {S : Set K} {m : K →₀ ℤ} :
    m ∈ nonnegativeOutside S ↔ ∀ i ∉ S, 0 ≤ m i := (Iff.rfl)

variable (R : Type*) [CommSemiring R] (S : Set K)

/-- The faithful monomial map from the exponent monoid of the partially Laurent ring. -/
noncomputable def partialInclusion :
    AddMonoidAlgebra R (nonnegativeOutside S) →ₐ[R] LaurentRing R K :=
  AddMonoidAlgebra.mapDomainAlgHom R R (nonnegativeOutside S).subtype

theorem partialInclusion_apply (p : AddMonoidAlgebra R (nonnegativeOutside S)) :
    partialInclusion R S p = AddMonoidAlgebra.mapDomain Subtype.val p := (rfl)

/-- The coefficient subalgebra in which precisely the variables in `S` may have negative powers. -/
noncomputable def partiallyLaurent : Subalgebra R (LaurentRing R K) :=
  (partialInclusion R S).range

variable {R S}

/-- The monomial realization of the partially Laurent ring is faithful over every coefficient
semiring, including those with zero divisors. -/
theorem partialInclusion_injective : Function.Injective (partialInclusion R S) := by
  exact AddMonoidAlgebra.mapDomain_injective Subtype.val_injective

/-- Membership is the nonnegativity of every supported exponent outside the inverted set. -/
theorem mem_partiallyLaurent_iff {f : LaurentRing R K} :
    f ∈ partiallyLaurent R S ↔ ∀ m ∈ f.coeff.support, ∀ i ∉ S, 0 ≤ m i := by
  classical
  change f ∈ (partialInclusion R S).range ↔ _
  rw [AlgHom.mem_range]
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

/-- Increasing the set of inverted variables increases the coefficient subalgebra. -/
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

/-- Every monomial with permitted exponents belongs to the coefficient subalgebra. -/
theorem single_mem_partiallyLaurent (m : nonnegativeOutside S) (r : R) :
    AddMonoidAlgebra.single (m : K →₀ ℤ) r ∈ partiallyLaurent R S := by
  refine ⟨AddMonoidAlgebra.single m r, ?_⟩
  simp [partialInclusion_apply]

/-- In a nontrivial coefficient ring, the exponent condition can be read from a monomial. -/
@[simp]
theorem single_one_mem_partiallyLaurent_iff [Nontrivial R] (m : K →₀ ℤ) :
    AddMonoidAlgebra.single m (1 : R) ∈ partiallyLaurent R S ↔
      ∀ i ∉ S, 0 ≤ m i := by
  classical
  simp [mem_partiallyLaurent_iff]

/-- Every ordinary variable belongs to every partially Laurent subalgebra. -/
theorem X_mem_partiallyLaurent (i : K) : (X i : LaurentRing R K) ∈ partiallyLaurent R S := by
  classical
  rw [X_def]
  apply single_mem_partiallyLaurent ⟨Finsupp.single i 1, ?_⟩ 1
  intro j _
  by_cases h : i = j <;> simp [h]

/-- The inverse of a variable belongs whenever that variable is among those inverted. -/
theorem inv_unitX_mem_partiallyLaurent {i : K} (hi : i ∈ S) :
    ((unitX i)⁻¹ : (LaurentRing R K)ˣ).val ∈ partiallyLaurent R S := by
  classical
  rw [val_inv_unitX]
  apply single_mem_partiallyLaurent ⟨Finsupp.single i (-1), ?_⟩ 1
  intro j hj
  have hij : i ≠ j := fun h ↦ hj (h ▸ hi)
  simp [hij]

/-- The partially Laurent coefficient ring is the monoid algebra of its permitted exponents. -/
noncomputable def partiallyLaurentEquiv :
    AddMonoidAlgebra R (nonnegativeOutside S) ≃ₐ[R] partiallyLaurent R S :=
  AlgEquiv.ofInjective (partialInclusion R S) partialInclusion_injective

/-- The monoid-algebra realization sends each permitted monomial to the same ambient monomial. -/
@[simp]
theorem partiallyLaurentEquiv_apply (p : AddMonoidAlgebra R (nonnegativeOutside S)) :
    (partiallyLaurentEquiv p : LaurentRing R K) = partialInclusion R S p := by
  exact AlgEquiv.ofInjective_apply _ _ p

/-- The permitted monomials form a basis of the partially Laurent coefficient ring. -/
noncomputable def partiallyLaurentBasis :
    Module.Basis (nonnegativeOutside S) R (partiallyLaurent R S) :=
  (AddMonoidAlgebra.basis (nonnegativeOutside S) R).map partiallyLaurentEquiv.toLinearEquiv

@[simp]
theorem partiallyLaurentBasis_apply (m : nonnegativeOutside S) :
    (partiallyLaurentBasis (R := R) m : LaurentRing R K) =
      AddMonoidAlgebra.single (m : K →₀ ℤ) 1 := by
  simp [partiallyLaurentBasis, AddMonoidAlgebra.basis_apply, partialInclusion_apply]

/-- Ordinary polynomials belong to every partially Laurent coefficient ring. -/
theorem toLaurent_mem_partiallyLaurent (p : MvPolynomial K R) :
    MvPolynomial.toLaurent p ∈ partiallyLaurent R S := by
  have h : MvPolynomial.toLaurent p ∈
      (MvPolynomial.toLaurent : MvPolynomial K R →ₐ[R] LaurentRing R K).range :=
    (AlgHom.mem_range _).2 ⟨p, rfl⟩
  exact mem_partiallyLaurent_iff.2 fun m hm i _ ↦
    MvPolynomial.mem_range_toLaurent_iff.1 h m hm i

/-- The canonical polynomial map into the partially Laurent coefficient ring. -/
noncomputable def toPartiallyLaurent : MvPolynomial K R →ₐ[R] partiallyLaurent R S :=
  MvPolynomial.toLaurent.codRestrict (partiallyLaurent R S) toLaurent_mem_partiallyLaurent

@[simp]
theorem coe_toPartiallyLaurent (p : MvPolynomial K R) :
    (toPartiallyLaurent (S := S) p : LaurentRing R K) = MvPolynomial.toLaurent p := (rfl)

theorem toPartiallyLaurent_injective :
    Function.Injective (toPartiallyLaurent : MvPolynomial K R → partiallyLaurent R S) :=
  fun _ _ h ↦ MvPolynomial.toLaurent_injective (congrArg Subtype.val h)

/-- Inverting no variables identifies the coefficient ring with the polynomial ring. -/
noncomputable def partiallyLaurentEmptyEquiv :
    MvPolynomial K R ≃ₐ[R] partiallyLaurent R (∅ : Set K) :=
  AlgEquiv.ofBijective toPartiallyLaurent ⟨toPartiallyLaurent_injective, by
    intro f
    have hf : ∀ m ∈ (f : LaurentRing R K).coeff.support, ∀ i, 0 ≤ m i := by
      simpa using mem_partiallyLaurent_iff.1 f.property
    obtain ⟨p, hp⟩ := (AlgHom.mem_range _).1 (MvPolynomial.mem_range_toLaurent_iff.2 hf)
    exact ⟨p, Subtype.ext hp⟩⟩

/-- Every element of a partially Laurent ring has a polynomial numerator and a denominator
monomial supported entirely on the inverted variables. -/
theorem exists_polynomial_denominator (f : partiallyLaurent R S) :
    ∃ n : K →₀ ℕ, (∀ i ∉ S, n i = 0) ∧ ∃ p : MvPolynomial K R,
      (f : LaurentRing R K) * MvPolynomial.toLaurent (MvPolynomial.monomial n 1) =
        MvPolynomial.toLaurent p := by
  classical
  obtain ⟨q, hq⟩ := (AlgHom.mem_range _).1 f.property
  rw [← hq]
  clear hq f
  induction q using AddMonoidAlgebra.induction_linear with
  | zero => exact ⟨0, by simp, 0, by simp⟩
  | add q r hq hr =>
    obtain ⟨n, hn, p, hp⟩ := hq
    obtain ⟨k, hk, t, ht⟩ := hr
    refine ⟨n + k, fun i hi ↦ by simp [hn i hi, hk i hi],
      p * MvPolynomial.monomial k 1 + t * MvPolynomial.monomial n 1, ?_⟩
    have hnk : (MvPolynomial.monomial (n + k) 1 : MvPolynomial K R) =
        MvPolynomial.monomial n 1 * MvPolynomial.monomial k 1 := by
      rw [MvPolynomial.monomial_mul_monomial, one_mul]
    rw [map_add, hnk, map_mul, map_add, map_mul, map_mul, ← hp, ← ht]
    ring
  | single m r =>
    refine ⟨(-(m : K →₀ ℤ)).mapRange Int.toNat Int.toNat_zero, ?_,
      MvPolynomial.monomial ((m : K →₀ ℤ).mapRange Int.toNat Int.toNat_zero) r, ?_⟩
    · intro i hi
      simp only [Finsupp.mapRange_apply, Finsupp.neg_apply]
      exact Int.toNat_eq_zero.mpr (neg_nonpos.mpr (m.property i hi))
    · rw [partialInclusion_apply, AddMonoidAlgebra.mapDomain_single,
        MvPolynomial.toLaurent_monomial, MvPolynomial.toLaurent_monomial,
        AddMonoidAlgebra.single_mul_single, mul_one]
      congr 1
      ext i
      simp only [Finsupp.add_apply, Finsupp.mapRange_apply, Finsupp.neg_apply]
      omega

/-- The variables allowed as polynomial denominators. -/
noncomputable def partialDenominators (R : Type*) [CommSemiring R] (S : Set K) :
    Submonoid (MvPolynomial K R) :=
  Submonoid.closure (MvPolynomial.X '' S)

/-- Every monomial supported on the inverted variables is an allowed denominator. -/
theorem monomial_mem_partialDenominators {n : K →₀ ℕ} (hn : ∀ i ∉ S, n i = 0) :
    MvPolynomial.monomial n (1 : R) ∈ partialDenominators R S := by
  classical
  rw [MvPolynomial.monomial_eq, MvPolynomial.C_1, one_mul]
  refine Submonoid.prod_mem _ fun i hi ↦ pow_mem (Submonoid.subset_closure ?_) _
  refine ⟨i, ?_, rfl⟩
  by_contra h
  exact Finsupp.mem_support_iff.1 hi (hn i h)

/-- An inverted variable is a unit already in the partially Laurent ring. -/
noncomputable def partialUnitX (i : S) : (partiallyLaurent R S)ˣ where
  val := ⟨X i, X_mem_partiallyLaurent (R := R) (S := S) (i : K)⟩
  inv := ⟨((unitX i)⁻¹ : (LaurentRing R K)ˣ).val, inv_unitX_mem_partiallyLaurent i.property⟩
  val_inv := by
    apply Subtype.ext
    change X (i : K) * ((unitX i)⁻¹ : (LaurentRing R K)ˣ).val = 1
    rw [← val_unitX]
    exact (unitX (R := R) (i : K)).val_inv
  inv_val := by
    apply Subtype.ext
    change ((unitX i)⁻¹ : (LaurentRing R K)ˣ).val * X (i : K) = 1
    rw [← val_unitX]
    exact (unitX (R := R) (i : K)).inv_val

/-- The partially Laurent ring carries the canonical polynomial-algebra structure. -/
noncomputable instance partialAlgebraMvPolynomial :
    Algebra (MvPolynomial K R) (partiallyLaurent R S) :=
  (toPartiallyLaurent : MvPolynomial K R →ₐ[R] partiallyLaurent R S).toRingHom.toAlgebra

@[simp]
theorem partial_algebraMap_eq (p : MvPolynomial K R) :
    algebraMap (MvPolynomial K R) (partiallyLaurent R S) p = toPartiallyLaurent p := (rfl)

instance : IsScalarTower R (MvPolynomial K R) (partiallyLaurent R S) :=
  .of_algebraMap_eq fun r ↦ by simp

/-- The partially Laurent coefficient ring is exactly the localization of polynomials at
the chosen variables. This holds for an arbitrary, possibly infinite inverted set. -/
instance partialIsLocalization :
    IsLocalization (partialDenominators R S) (partiallyLaurent R S) where
  map_units := by
    rintro ⟨y, hy⟩
    change y ∈ Submonoid.closure (MvPolynomial.X '' S) at hy
    change IsUnit (algebraMap (MvPolynomial K R) (partiallyLaurent R S) y)
    induction hy using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨i, hi, rfl⟩ := hx
      refine ⟨partialUnitX ⟨i, hi⟩, ?_⟩
      apply Subtype.ext
      simp [partialUnitX, MvPolynomial.toLaurent_X]
    | one => simp
    | mul x y _ _ hx hy => simpa using hx.mul hy
  surj f := by
    obtain ⟨n, hn, p, hp⟩ := exists_polynomial_denominator f
    refine ⟨(p, ⟨MvPolynomial.monomial n 1, monomial_mem_partialDenominators hn⟩), ?_⟩
    apply Subtype.ext
    simpa using hp
  exists_of_eq h := ⟨1, by simpa using toPartiallyLaurent_injective h⟩

/-- Enlarging the inverted set localizes at precisely the newly inverted variables. -/
theorem isLocalization_partiallyLaurent {T : Set K} (hST : S ⊆ T) :
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
    change p ∈ Submonoid.closure (MvPolynomial.X '' T) at hp
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
theorem map_mem_partiallyLaurent (φ : R →+* A) {f : LaurentRing R K}
    (hf : f ∈ partiallyLaurent R S) :
    AddMonoidAlgebra.mapRingHom (K →₀ ℤ) φ f ∈ partiallyLaurent A S := by
  classical
  apply mem_partiallyLaurent_iff.2
  intro m hm i hi
  apply mem_partiallyLaurent_iff.1 hf m _ i hi
  apply Finsupp.mem_support_iff.2
  intro hz
  exact Finsupp.mem_support_iff.1 hm (by simp [AddMonoidAlgebra.coeff_mapRingHom, hz])

/-- Coefficient homomorphisms restrict to partially Laurent rings with the same inverted set. -/
noncomputable def partialCoeffMap (φ : R →+* A) :
    partiallyLaurent R S →+* partiallyLaurent A S where
  toFun f := ⟨AddMonoidAlgebra.mapRingHom (K →₀ ℤ) φ f, map_mem_partiallyLaurent φ f.property⟩
  map_zero' := Subtype.ext (map_zero _)
  map_one' := Subtype.ext (map_one _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)

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

/-- Coefficient change commutes with the polynomial inclusion into a partially Laurent ring. -/
@[simp]
theorem partialCoeffMap_toPartiallyLaurent (φ : R →+* A) (p : MvPolynomial K R) :
    partialCoeffMap (S := S) φ (toPartiallyLaurent p) =
      toPartiallyLaurent (S := S) (MvPolynomial.map φ p) := by
  apply Subtype.ext
  simp [MvPolynomial.toLaurent_map]

/-- Changing coefficients preserves each permitted basis monomial. -/
@[simp]
theorem partialCoeffMap_basis (φ : R →+* A) (m : nonnegativeOutside S) :
    partialCoeffMap φ (partiallyLaurentBasis (R := R) m) =
      partiallyLaurentBasis (R := A) m := by
  apply Subtype.ext
  simp

/-- Enlarging the inverted set commutes with arbitrary coefficient homomorphisms. -/
theorem partialCoeffMap_inclusion (φ : R →+* A) {T : Set K} (hST : S ⊆ T)
    (f : partiallyLaurent R S) :
    partialCoeffMap φ (Subalgebra.inclusion (partiallyLaurent_mono (R := R) hST) f) =
      Subalgebra.inclusion (partiallyLaurent_mono (R := A) hST) (partialCoeffMap φ f) := by
  apply Subtype.ext
  rfl

end Coefficients

end TauCeti.LaurentRing
