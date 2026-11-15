/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import TauCeti.Algebra.Regular.Submonoid
public import TauCeti.RingTheory.Localization.AddUnits
public import TauCeti.RingTheory.Localization.Defs

/-!
# Total quotient semirings via regular localization

For a commutative semiring `A`, `TauCeti.TotalQuotient A` is the localization of `A` at its
submonoid of regular elements `TauCeti.regularSubmonoid A`. Because multiplication by every
denominator is injective, the canonical map `algebraMap A (TotalQuotient A)` is always injective,
even when `A` has zero divisors.

## Main declarations

* `TauCeti.TotalQuotient`: localization `Localization (regularSubmonoid A)` of a commutative
  semiring `A` at its regular elements.
* `TauCeti.TotalQuotient.algebraMap_injective` and `TauCeti.TotalQuotient.isUnit_algebraMap_iff`:
  `A` embeds into `TotalQuotient A`, and an element of `A` becomes a unit if and only if it is
  regular.
* `TauCeti.TotalQuotient.lift` and `TauCeti.TotalQuotient.exists_ringHom_comp_algebraMap_iff`:
  a semiring homomorphism `f : A →+* B` extends (uniquely) to `TotalQuotient A →+* B` if and only if
  it sends every regular element of `A` to a unit of `B`.
* `TauCeti.TotalQuotient.instSemifield`: when `A` is a domain semiring (`IsDomain A`, meaning `A`
  is nontrivial and every nonzero element is regular), `TotalQuotient A` is a `Semifield` (adapting
  `IsFractionRing.toField` from `CommRing` to `CommSemiring`).
* `TauCeti.TotalQuotient.awayRingEquiv`: for a regular element `e : A`,
  `TotalQuotient (Localization.Away e) ≃+* TotalQuotient A`, commuting with base maps and lifts.
* `TauCeti.TotalQuotient.equivFractionRing`: for a commutative ring `A`, `TotalQuotient A` is
  canonically `A`-algebra isomorphic to `FractionRing A`.

## References

* S. Fomin and A. Zelevinsky, *Cluster algebras IV: Coefficients*, Compos. Math. 143 (2007), §2.
-/

public section

namespace TauCeti

/-- The total quotient semiring `Reg(A)⁻¹ A` of a commutative semiring `A`, obtained by localizing
at `TauCeti.regularSubmonoid A`. -/
abbrev TotalQuotient (A : Type*) [CommSemiring A] : Type _ :=
  Localization (regularSubmonoid A)

namespace TotalQuotient

section CommSemiring

variable {A B C : Type*} [CommSemiring A] [CommSemiring B] [CommSemiring C]

/-- Localizing at regular elements embeds `A` injectively into `TotalQuotient A`, even when `A` has
zero divisors. -/
theorem algebraMap_injective (A : Type*) [CommSemiring A] :
    Function.Injective (algebraMap A (TotalQuotient A)) :=
  IsLocalization.injectiveₛ (M := regularSubmonoid A) (S := TotalQuotient A)
    fun _ hm => mem_regularSubmonoid.mp hm

@[simp]
theorem algebraMap_eq_iff {a b : A} :
    algebraMap A (TotalQuotient A) a = algebraMap A (TotalQuotient A) b ↔ a = b :=
  (algebraMap_injective A).eq_iff

@[simp]
theorem algebraMap_eq_zero_iff {a : A} :
    algebraMap A (TotalQuotient A) a = 0 ↔ a = 0 :=
  map_eq_zero_iff (algebraMap A (TotalQuotient A)) (algebraMap_injective A)

/-- An element of `A` has regular image in `TotalQuotient A` if and only if it is regular in `A`. -/
@[simp]
theorem isRegular_algebraMap_iff {a : A} :
    IsRegular (algebraMap A (TotalQuotient A) a) ↔ IsRegular a := by
  rw [← IsLocalization.mk'_one (M := regularSubmonoid A) (TotalQuotient A) a]
  exact IsLocalization.isRegular_mk' (S := TotalQuotient A)
    (M := regularSubmonoid A) fun _ hm => mem_regularSubmonoid.mp hm

/-- An element of `A` becomes a unit in `TotalQuotient A` if and only if it is regular in `A`. -/
@[simp]
theorem isUnit_algebraMap_iff {a : A} :
    IsUnit (algebraMap A (TotalQuotient A) a) ↔ IsRegular a :=
  ⟨fun hu => isRegular_algebraMap_iff.mp hu.isRegular,
    fun ha => IsLocalization.map_units (TotalQuotient A) ⟨a, mem_regularSubmonoid.mpr ha⟩⟩

/-! ### Universal property -/

/-- Two semiring homomorphisms out of `TotalQuotient A` are equal as soon as they agree on `A`. -/
@[ext]
theorem ringHom_ext {R : Type*} [Semiring R] {F G : TotalQuotient A →+* R}
    (h : ∀ a : A, F (algebraMap A (TotalQuotient A) a) = G (algebraMap A (TotalQuotient A) a)) :
    F = G :=
  IsLocalization.ringHom_ext (regularSubmonoid A) (RingHom.ext h)

/-- A semiring homomorphism `f : A →+* B` extends to `TotalQuotient A →+* B` if and only if `f`
maps every regular element of `A` to a unit of `B`. -/
theorem exists_ringHom_comp_algebraMap_iff (f : A →+* B) :
    (∃ F : TotalQuotient A →+* B, F.comp (algebraMap A (TotalQuotient A)) = f) ↔
      ∀ a : A, IsRegular a → IsUnit (f a) :=
  ⟨fun ⟨F, hF⟩ _ ha => hF ▸ (isUnit_algebraMap_iff.mpr ha).map F,
    fun hf => ⟨IsLocalization.lift (M := regularSubmonoid A)
      (fun y => hf y (mem_regularSubmonoid.mp y.2)), IsLocalization.lift_comp _⟩⟩

/-- The unique extension of `f : A →+* B` to `TotalQuotient A →+* B` when `f` sends regular
elements to units. -/
noncomputable def lift (f : A →+* B) (hf : ∀ a : A, IsRegular a → IsUnit (f a)) :
    TotalQuotient A →+* B :=
  IsLocalization.lift (M := regularSubmonoid A) fun y => hf y (mem_regularSubmonoid.mp y.2)

@[simp]
theorem lift_algebraMap (f : A →+* B) (hf : ∀ a : A, IsRegular a → IsUnit (f a)) (a : A) :
    lift f hf (algebraMap A (TotalQuotient A) a) = f a :=
  IsLocalization.lift_eq _ a

@[simp]
theorem lift_comp_algebraMap (f : A →+* B) (hf : ∀ a : A, IsRegular a → IsUnit (f a)) :
    (lift f hf).comp (algebraMap A (TotalQuotient A)) = f :=
  IsLocalization.lift_comp _

theorem lift_mk' (f : A →+* B) (hf : ∀ a : A, IsRegular a → IsUnit (f a))
    (a : A) (b : regularSubmonoid A) :
    lift f hf (IsLocalization.mk' (TotalQuotient A) a b) =
      f a * ↑(hf b (mem_regularSubmonoid.mp b.2)).unit⁻¹ :=
  IsLocalization.lift_mk' _ a b

/-- Uniqueness of the extension to `TotalQuotient A`. -/
theorem lift_unique {f : A →+* B} (hf : ∀ a : A, IsRegular a → IsUnit (f a))
    {F : TotalQuotient A →+* B}
    (hF : ∀ a : A, F (algebraMap A (TotalQuotient A) a) = f a) :
    F = lift f hf :=
  ringHom_ext fun a => (hF a).trans (lift_algebraMap f hf a).symm

/-- Lifting the canonical map `A →+* TotalQuotient A` recovers the identity homomorphism. -/
@[simp]
theorem lift_algebraMap_self :
    lift (algebraMap A (TotalQuotient A))
      (fun _ ha => isUnit_algebraMap_iff.mpr ha) = RingHom.id (TotalQuotient A) :=
  (lift_unique _ fun _ => rfl).symm

/-- Composition with `TotalQuotient.lift` is again a `TotalQuotient.lift`. -/
theorem comp_lift (g : B →+* C) (f : A →+* B) (hf : ∀ a : A, IsRegular a → IsUnit (f a)) :
    g.comp (lift f hf) = lift (g.comp f) (fun a ha => (hf a ha).map g) :=
  lift_unique _ fun a => by simp

/-- If `f : A →+* B` is injective and maps regular elements to units, its extension to
`TotalQuotient A` is injective. -/
theorem lift_injective_of_injective {f : A →+* B} (hf : ∀ a : A, IsRegular a → IsUnit (f a))
    (hinj : Function.Injective f) :
    Function.Injective (lift f hf) :=
  IsLocalization.lift_injective_of_injective (fun y => hf y (mem_regularSubmonoid.mp y.2)) hinj

/-! ### Localization away from a regular element -/

section Away

variable {e : A}

/-- For a regular element `e : A`, the canonical semiring homomorphism from `Localization.Away e`
into `TotalQuotient A`. -/
noncomputable def awayToTotalQuotient (he : IsRegular e) :
    Localization.Away e →+* TotalQuotient A :=
  IsLocalization.Away.lift e (isUnit_algebraMap_iff.mpr he)

@[simp]
theorem awayToTotalQuotient_algebraMap (he : IsRegular e) (a : A) :
    awayToTotalQuotient he (algebraMap A (Localization.Away e) a) =
      algebraMap A (TotalQuotient A) a :=
  IsLocalization.Away.lift_eq e (isUnit_algebraMap_iff.mpr he) a

/-- Every regular element of `Localization.Away e` (with `e` regular) maps to a unit under any
homomorphism out of `Localization.Away e` whose restriction to `A` inverts regular elements. -/
theorem isUnit_map_of_isRegular_away (he : IsRegular e) {g : Localization.Away e →+* B}
    (hg : ∀ a : A, IsRegular a → IsUnit (g (algebraMap A (Localization.Away e) a)))
    {x : Localization.Away e} (hx : IsRegular x) :
    IsUnit (g x) := by
  have hpow : ∀ m ∈ Submonoid.powers e, IsRegular m := by
    rintro _ ⟨n, rfl⟩
    exact he.pow n
  obtain ⟨⟨r, m⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers e) x
  obtain ⟨n, hm⟩ := m.2
  have hr : IsRegular r :=
    (IsLocalization.isRegular_mk' (S := Localization.Away e) hpow).mp hx
  have hunit_den : IsUnit (g (algebraMap A (Localization.Away e) m)) :=
    hm ▸ hg (e ^ n) (he.pow n)
  rw [← Units.isUnit_mul_units _ hunit_den.unit, IsUnit.unit_spec, ← map_mul,
    IsLocalization.mk'_spec]
  exact hg r hr

/-- Regular elements of `A` remain regular in `Localization.Away e` when `e` is regular. -/
theorem isRegular_algebraMap_away (he : IsRegular e) {a : A} (ha : IsRegular a) :
    IsRegular (algebraMap A (Localization.Away e) a) := by
  have hpow : ∀ m ∈ Submonoid.powers e, IsRegular m := by
    rintro _ ⟨n, rfl⟩
    exact he.pow n
  rw [← IsLocalization.mk'_one (M := Submonoid.powers e) (Localization.Away e) a]
  exact (IsLocalization.isRegular_mk' (S := Localization.Away e) hpow).mpr ha

/-- Localizing away from a regular element `e` before forming `TotalQuotient` gives the same
semiring up to canonical isomorphism: `T(A[e⁻¹]) ≃+* T(A)`. -/
noncomputable def awayRingEquiv (he : IsRegular e) :
    TotalQuotient (Localization.Away e) ≃+* TotalQuotient A :=
  RingEquiv.ofRingHom
    (lift (awayToTotalQuotient he) fun _ hx => isUnit_map_of_isRegular_away he (fun a ha => by
      rw [awayToTotalQuotient_algebraMap]
      exact isUnit_algebraMap_iff.mpr ha) hx)
    (lift ((algebraMap (Localization.Away e) (TotalQuotient (Localization.Away e))).comp
        (algebraMap A (Localization.Away e)))
      fun _ ha => isUnit_algebraMap_iff.mpr (isRegular_algebraMap_away he ha))
    (by
      ext a
      simp)
    (by
      apply IsLocalization.ringHom_ext (regularSubmonoid (Localization.Away e))
      apply IsLocalization.ringHom_ext (Submonoid.powers e)
      ext a
      simp)

@[simp]
theorem awayRingEquiv_algebraMap (he : IsRegular e) (x : Localization.Away e) :
    awayRingEquiv he (algebraMap (Localization.Away e) _ x) = awayToTotalQuotient he x := by
  simp [awayRingEquiv]

@[simp]
theorem awayRingEquiv_symm_algebraMap (he : IsRegular e) (a : A) :
    (awayRingEquiv he).symm (algebraMap A (TotalQuotient A) a) =
      algebraMap (Localization.Away e) _ (algebraMap A (Localization.Away e) a) := by
  simp [awayRingEquiv]

/-- `awayRingEquiv` commutes with universal lifts (`TotalQuotient.lift`). -/
theorem lift_comp_awayRingEquiv (he : IsRegular e) (f : A →+* B)
    (hf : ∀ a : A, IsRegular a → IsUnit (f a)) :
    (lift f hf).comp (awayRingEquiv he : TotalQuotient (Localization.Away e) →+* TotalQuotient A) =
      lift (IsLocalization.Away.lift e (hf e he))
        (fun _ hx => isUnit_map_of_isRegular_away he
          (fun a ha => by simpa [IsLocalization.Away.lift_eq] using hf a ha) hx) := by
  apply IsLocalization.ringHom_ext (regularSubmonoid (Localization.Away e))
  apply IsLocalization.ringHom_ext (Submonoid.powers e)
  ext a
  simp

end Away

end CommSemiring

/-! ### Domain semirings and semifield structure -/

section Domain

variable {A : Type*} [CommSemiring A]

/-- Over a cancellative commutative semiring `A`, `regularSubmonoid A = A⁰`, so `TotalQuotient A`
is a fraction semiring of `A`. -/
instance instIsFractionRing (A : Type*) [CommSemiring A] [IsCancelMulZero A] :
    IsFractionRing A (TotalQuotient A) :=
  IsLocalization.of_le (regularSubmonoid A) (nonZeroDivisors A)
    (regularSubmonoid_le_nonZeroDivisors A) fun r hr => by
      rw [← regularSubmonoid_eq_nonZeroDivisors_of_isCancelMulZero A] at hr
      exact IsLocalization.map_units (TotalQuotient A) ⟨r, hr⟩

/-- Over a cancellative commutative semiring `B`, any `B`-fraction semiring `K`
(`IsFractionRing B K`) is canonically `B`-algebra isomorphic to `TotalQuotient B`. -/
noncomputable def equivOfIsFractionRing (B K : Type*) [CommSemiring B] [IsCancelMulZero B]
    [CommSemiring K] [Algebra B K] [IsFractionRing B K] :
    TotalQuotient B ≃ₐ[B] K :=
  IsLocalization.algEquiv (nonZeroDivisors B) (TotalQuotient B) K

/-- A commutative semiring is a domain (`IsDomain A`) if and only if it is nontrivial and every
nonzero element is regular. -/
theorem isDomain_iff_nontrivial_and_forall_ne_zero_isRegular :
    IsDomain A ↔ Nontrivial A ∧ ∀ a : A, a ≠ 0 → IsRegular a := by
  rw [isDomain_iff_cancelMulZero_and_nontrivial, and_comm, isCancelMulZero_iff_forall_isRegular]

variable [IsDomain A]

/-- Inverse in `TotalQuotient A` when `A` is a domain semiring. -/
protected noncomputable def inv (z : TotalQuotient A) : TotalQuotient A :=
  open Classical in
  if hz : z = 0 then 0
  else
    IsLocalization.mk' (TotalQuotient A) ↑(IsLocalization.sec (regularSubmonoid A) z).2
      ⟨(IsLocalization.sec (regularSubmonoid A) z).1,
        mem_regularSubmonoid.mpr (.of_ne_zero (IsLocalization.sec_fst_ne_zero hz))⟩

protected theorem inv_zero : TotalQuotient.inv (0 : TotalQuotient A) = 0 := by
  rw [TotalQuotient.inv]
  exact dite_eq_left rfl

protected theorem mul_inv_cancel {z : TotalQuotient A} (hz : z ≠ 0) :
    z * TotalQuotient.inv z = 1 := by
  classical
  rw [TotalQuotient.inv, dite_eq_right hz, ← IsUnit.mul_left_inj
    (IsLocalization.map_units (TotalQuotient A) ⟨(IsLocalization.sec (regularSubmonoid A) z).1,
      mem_regularSubmonoid.mpr (.of_ne_zero (IsLocalization.sec_fst_ne_zero hz))⟩),
    one_mul, mul_assoc, IsLocalization.mk'_spec, ← IsLocalization.eq_mk'_iff_mul_eq]
  exact (IsLocalization.mk'_sec (M := regularSubmonoid A) (TotalQuotient A) z).symm

/-- For a domain semiring `A` (nontrivial, with every nonzero element regular), `TotalQuotient A`
is a `Semifield`. -/
noncomputable instance instSemifield : Semifield (TotalQuotient A) where
  __ := (inferInstance : CommSemiring (TotalQuotient A))
  __ := (IsLocalization.toLocalizationMap (regularSubmonoid A) (TotalQuotient A)).nontrivial
    fun h0 => not_isRegular_zero (mem_regularSubmonoid.mp h0)
  inv := TotalQuotient.inv
  inv_zero := TotalQuotient.inv_zero
  mul_inv_cancel _ hz := TotalQuotient.mul_inv_cancel hz
  nnqsmul := _
  nnqsmul_def _ _ := rfl

@[simp]
theorem mk'_eq_div (a : A) (b : regularSubmonoid A) :
    IsLocalization.mk' (TotalQuotient A) a b =
      algebraMap A (TotalQuotient A) a / algebraMap A (TotalQuotient A) b := by
  refine IsLocalization.mk'_eq_iff_eq_mul.mpr ?_
  rw [eq_comm]
  exact div_mul_cancel₀ _ (algebraMap_eq_zero_iff.not.mpr (mem_regularSubmonoid.mp b.2).ne_zero)

@[simp]
theorem mk_eq_div (a : A) (b : regularSubmonoid A) :
    (Localization.mk a b : TotalQuotient A) =
      algebraMap A (TotalQuotient A) a / algebraMap A (TotalQuotient A) b := by
  rw [Localization.mk_eq_mk', mk'_eq_div]

/-- Every element of `TotalQuotient A` over a domain semiring is a ratio `a / b` with `b ≠ 0`. -/
theorem div_surjective (z : TotalQuotient A) :
    ∃ a b : A, b ≠ 0 ∧ algebraMap A (TotalQuotient A) a / algebraMap A (TotalQuotient A) b = z := by
  obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective (regularSubmonoid A) z
  exact ⟨a, b, (mem_regularSubmonoid.mp b.2).ne_zero, (mk'_eq_div a b).symm⟩

end Domain

/-! ### Comparison with `FractionRing` for commutative rings -/

section CommRing

/-- Over a commutative ring `A`, `regularSubmonoid A = A⁰`, so `TotalQuotient A` satisfies
`IsFractionRing A (TotalQuotient A)`. -/
instance instIsFractionRingOfCommRing (A : Type*) [CommRing A] :
    IsFractionRing A (TotalQuotient A) :=
  IsLocalization.of_le (regularSubmonoid A) (nonZeroDivisors A)
    (regularSubmonoid_le_nonZeroDivisors A) fun r hr => by
      rw [← regularSubmonoid_eq_nonZeroDivisors A] at hr
      exact IsLocalization.map_units (TotalQuotient A) ⟨r, hr⟩

/-- For a commutative ring `A`, `regularSubmonoid A = A⁰`, so `TotalQuotient A` is canonically
`A`-algebra isomorphic to Mathlib's `FractionRing A`. -/
noncomputable def equivFractionRing (A : Type*) [CommRing A] :
    TotalQuotient A ≃ₐ[A] FractionRing A :=
  IsLocalization.algEquiv (nonZeroDivisors A) (TotalQuotient A) (FractionRing A)

end CommRing

/-! ### Check: injectivity with zero divisors -/

-- `ℕ × ℕ` has zero divisors `(1, 0) * (0, 1) = 0`, yet `algebraMap` into `TotalQuotient (ℕ × ℕ)`
-- remains injective.
example : ((1, 0) : ℕ × ℕ) ≠ 0 ∧ ((0, 1) : ℕ × ℕ) ≠ 0 ∧
    ((1, 0) : ℕ × ℕ) * (0, 1) = 0 ∧
    Function.Injective (algebraMap (ℕ × ℕ) (TotalQuotient (ℕ × ℕ))) :=
  ⟨by decide, by decide, rfl, algebraMap_injective (ℕ × ℕ)⟩

end TotalQuotient

end TauCeti
