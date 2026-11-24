/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DedekindDomain.SInteger.ClassGroup
public import TauCeti.RingTheory.DedekindDomain.SInteger.Unit.OfUnits
public import TauCeti.AlgebraicGeometry.WeilDivisor.Dedekind.ClassGroup

/-!
# The unit and class group sequence of the `S`-integers

Let `R` be a Dedekind domain with fraction field `K`, let `S` be an arbitrary set of height-one
primes of `R` and write `𝒪_S = S.integer K`. This file constructs the exact sequence

```text
0 → Rˣ → 𝒪_Sˣ → ⨁_{v ∈ S} ℤ → Cl(R) → Cl(𝒪_S) → 0
```

with the following sign conventions. The middle map `Set.unitOrd` sends an `S`-unit to its
**positive orders** at the primes of `S`: a uniformizer at `v` has order `1` there. It is the
principal Weil divisor of the unit (`OrderSystem.principalDivisor` of
`OrderSystem.ofDedekindDomain`), which is supported on `S` (`Set.mapDomain_unitOrd`), read as a
tuple indexed by `S`. Mathlib's valuation `v.valuation K` and Tau Ceti's `Set.unitValuation` give a
uniformizer the exponent `-1`, so `Set.unitOrd` negates the additive exponents of
`Set.unitValuation` (`Set.unitOrd_apply_eq_neg_toAdd_unitValuation`). The next map
`Set.invDivisorClass` sends a tuple `(n_v)` to `∏ [v] ^ (-n_v)`, the **inverse** of the usual
divisor class, that is, the negative of the Weil divisor class
(`Set.invDivisorClass_eq_neg_classGroupAddEquiv`). Negation and inversion preserve images and
kernels, so exactness does not depend on these signs. They are chosen so that the sequence matches
the localization sequence of `K₀`, where the class of the residue field `𝒪/v` is `[𝒪] - [v]`, with
class `[v]⁻¹` in the Picard group, and the boundary map on `K₁` takes positive orders.

Here `𝒪_Sˣ` is represented by Mathlib's group `S.unit K` of `S`-units, identified with the units
of `S.integer K` by `Set.unitEquivUnitsInteger`; `Rˣ` maps to it by `TauCeti.SUnit.unitOfUnits`,
and the last map is extension of ideal classes `ClassGroup.extendedHom R (S.integer K)`.

The set `S` need not be finite: an `S`-unit has nonzero order at only finitely many primes, so its
orders form a finitely supported tuple, an element of the direct sum `↥S →₀ ℤ` rather than of the
product.

## Main definitions

* `Set.unitOrd`: the positive-order map `S.unit K → ⨁_{v ∈ S} ℤ`.
* `Set.invDivisorClass`: the inverse divisor-class map `⨁_{v ∈ S} ℤ → Cl(R)`,
  `(n_v) ↦ ∏ [v] ^ (-n_v)`.

## Main results

* `Set.exact_unitOfUnits_unitOrd`: exactness at the `S`-units, the kernel of `Set.unitOrd` being
  the units of `R`; injectivity of `Rˣ → 𝒪_Sˣ` is `TauCeti.SUnit.unitOfUnits_injective`.
* `Set.exact_unitOrd_invDivisorClass`: exactness at `⨁_{v ∈ S} ℤ`, the tuples of positive orders
  of `S`-units being exactly those whose inverse divisor class is trivial.
* `Set.exact_invDivisorClass_extendedHom`: exactness at `Cl(R)`, by `range_invDivisorClass` and
  `IsDedekindDomain.ker_integer_extendedHom`. Surjectivity of `Cl(R) → Cl(𝒪_S)` is
  `IsDedekindDomain.integer_extendedHom_surjective`.
* `Set.unitOrd_inclusion` and `Set.invDivisorClass_mapDomain_inclusion`: both maps are compatible
  with enlarging `S`.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Exercise I.3.8, p. 29,
  and Chapter V, 6.6.1, p. 409.
-/

public section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum TauCeti.AlgebraicGeometry
  TauCeti.AlgebraicGeometry.WeilDivisor

namespace Set

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  (S : Set (HeightOneSpectrum R)) (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

/-- A unit of `K` is an `S`-unit exactly when its principal divisor is supported on `S`. -/
theorem mem_unit_iff_support_principalDivisor_subset {x : Kˣ} :
    x ∈ S.unit K ↔
      ↑((OrderSystem.ofDedekindDomain R K).principalDivisor (.ofMul x)).support ⊆ S := by
  refine (mem_unit_iff S K).trans (forall_congr' fun v ↦ ?_)
  rw [Finset.mem_coe, mem_support_principalDivisor_iff_valuation_ne_one, toMul_ofMul]
  exact not_imp_comm

/-- The positive-order map on `S`-units: the coordinate at `v ∈ S` of the image of `u` is the
order `ord_v(u)` of `u` at `v`, normalized so that a uniformizer at `v` has order `1`. It is the
principal divisor of `u` restricted to the primes of `S`, so it takes values in the direct sum
`↥S →₀ ℤ` even for infinite `S`. -/
noncomputable def unitOrd : Additive (S.unit K) →+ (↥S →₀ ℤ) :=
  (Finsupp.subtypeDomainAddMonoidHom (p := (· ∈ S))).comp
    ((OrderSystem.ofDedekindDomain R K).principalHom.comp (S.unit K).subtype.toAdditive)

/-- The coordinate of `Set.unitOrd` at `v` is the `v`-adic order of the unit. -/
@[simp]
theorem unitOrd_apply (u : Additive (S.unit K)) (v : ↥S) :
    S.unitOrd K u v = adicOrd R K v (.ofMul ((u.toMul : S.unit K) : Kˣ)) := by
  simp only [unitOrd, Finsupp.subtypeDomainAddMonoidHom, AddMonoidHom.comp_apply,
    AddMonoidHom.coe_mk, ZeroHom.coe_mk, Finsupp.subtypeDomain_apply,
    OrderSystem.principalHom_apply, MonoidHom.toAdditive_apply_apply, Subgroup.coe_subtype]
  -- `coeff D v` is `D v` by definition
  exact OrderSystem.coeff_principalDivisor (OrderSystem.ofDedekindDomain R K) _ v

/-- The coordinate of `Set.unitOrd` at `v` is the negated additive exponent of
`Set.unitValuation` at `v`: Mathlib's valuation gives a uniformizer the exponent `-1`, while its
positive order is `1`. -/
theorem unitOrd_apply_eq_neg_toAdd_unitValuation (u : Additive (S.unit K)) (v : ↥S) :
    S.unitOrd K u v = -Multiplicative.toAdd (S.unitValuation K u.toMul v) := by
  rw [unitOrd_apply, adicOrd_ofMul, unitValuation_apply, ← valuationOfNeZero_eq,
    ← WithZero.toAdd_unzero_eq_log WithZero.coe_ne_zero, WithZero.unzero_coe]

/-- The principal divisor of an `S`-unit is supported on `S`, where its coefficients are the
positive orders `Set.unitOrd`. -/
theorem mapDomain_unitOrd (u : Additive (S.unit K)) :
    (S.unitOrd K u).mapDomain Subtype.val =
      (OrderSystem.ofDedekindDomain R K).principalDivisor (.ofMul ((u.toMul : S.unit K) : Kˣ)) := by
  classical
  rw [← Function.Embedding.coe_subtype, ← Finsupp.embDomain_eq_mapDomain,
    ← Finsupp.extendDomain_eq_embDomain_subtype, unitOrd, AddMonoidHom.comp_apply,
    AddMonoidHom.comp_apply, OrderSystem.principalHom_apply]
  exact Finsupp.extendDomain_subtypeDomain _ fun _ hw ↦
    (mem_unit_iff_support_principalDivisor_subset S K).mp u.toMul.property hw

/-- An `S`-unit has positive order zero at every prime of `S` exactly when it is a unit at every
prime, that is, an `∅`-unit. -/
theorem unitOrd_eq_zero_iff (u : Additive (S.unit K)) :
    S.unitOrd K u = 0 ↔ ((u.toMul : S.unit K) : Kˣ) ∈ (∅ : Set (HeightOneSpectrum R)).unit K := by
  rw [mem_unit_iff_support_principalDivisor_subset, Set.subset_empty_iff, Finset.coe_eq_empty,
    Finsupp.support_eq_empty, ← mapDomain_unitOrd,
    ← Finsupp.mapDomain_zero (f := (Subtype.val : ↥S → HeightOneSpectrum R)),
    (Finsupp.mapDomain_injective Subtype.val_injective).eq_iff]

/-- **Exactness at the `S`-units.** The `S`-units of positive order zero at every prime of `S` are
exactly the images of the units of `R`. -/
theorem exact_unitOfUnits_unitOrd :
    Function.Exact (TauCeti.SUnit.unitOfUnits S K).toAdditive (S.unitOrd K) := by
  intro u
  rw [unitOrd_eq_zero_iff, mem_unit_empty_iff]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨.ofMul a, ?_⟩
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Units.ext
    simpa using ha
  · rintro ⟨a, rfl⟩
    exact ⟨a.toMul, by simp⟩

/-- The inverse divisor-class map `(n_v) ↦ ∏ [v] ^ (-n_v)` from the free abelian group on `S` to
the class group of `R`. The inverse matches the positive orders of `Set.unitOrd`: the positive
orders of an `S`-unit give a trivial class (`Set.exact_unitOrd_invDivisorClass`). -/
noncomputable def invDivisorClass : (↥S →₀ ℤ) →+ Additive (ClassGroup R) :=
  Finsupp.liftAddHom fun v ↦ zmultiplesHom _ (.ofMul (v : HeightOneSpectrum R).classGroupMk⁻¹)

/-- The inverse divisor class of `n` times the basis vector at `v` is `[v] ^ (-n)`. -/
@[simp]
theorem invDivisorClass_single (v : ↥S) (n : ℤ) :
    S.invDivisorClass (Finsupp.single v n) =
      .ofMul ((v : HeightOneSpectrum R).classGroupMk ^ (-n)) := by
  simp [invDivisorClass, zpow_neg]

/-- The inverse divisor class of a tuple supported on `S` is the negative of the class of the
corresponding Weil divisor, under the identification `classGroupAddEquiv` of the divisor class
group with the ideal class group. -/
theorem invDivisorClass_eq_neg_classGroupAddEquiv (n : ↥S →₀ ℤ) :
    S.invDivisorClass n = -classGroupAddEquiv R K
      ((OrderSystem.ofDedekindDomain R K).divisorClass (n.mapDomain Subtype.val)) := by
  induction n using Finsupp.induction_linear with
  | zero => simp
  | add n m hn hm => rw [map_add, hn, hm, Finsupp.mapDomain_add, map_add, map_add, neg_add]
  | single v n =>
    rw [invDivisorClass_single, Finsupp.mapDomain_single, single_eq_zsmul_ofPoint, map_zsmul,
      map_zsmul, classGroupAddEquiv_divisorClass_ofPoint, zpow_neg, ofMul_inv, ofMul_zpow]

/-- The image of the inverse divisor-class map is the subgroup generated by the classes of the
primes of `S`. -/
theorem range_invDivisorClass :
    S.invDivisorClass.range = (Subgroup.closure (classGroupMk '' S)).toAddSubgroup := by
  apply le_antisymm
  · rintro _ ⟨n, rfl⟩
    induction n using Finsupp.induction_linear with
    | zero => exact zero_mem _
    | add n m hn hm => rw [map_add]; exact add_mem hn hm
    | single v n =>
      rw [invDivisorClass_single, Additive.mem_toAddSubgroup, toMul_ofMul]
      exact Subgroup.zpow_mem _ (Subgroup.subset_closure (Set.mem_image_of_mem _ v.property)) _
  · rw [← OrderIso.le_symm_apply, Subgroup.closure_le]
    rintro _ ⟨v, hv, rfl⟩
    rw [SetLike.mem_coe, AddSubgroup.mem_toSubgroup']
    exact ⟨Finsupp.single ⟨v, hv⟩ (-1), by rw [invDivisorClass_single, neg_neg, zpow_one]⟩

/-- **Exactness at the free abelian group on `S`.** A tuple supported on `S` is the tuple of
positive orders of an `S`-unit exactly when its inverse divisor class is trivial. -/
theorem exact_unitOrd_invDivisorClass : Function.Exact (S.unitOrd K) S.invDivisorClass := by
  intro n
  rw [invDivisorClass_eq_neg_classGroupAddEquiv S K, neg_eq_zero, AddEquivClass.map_eq_zero_iff,
    OrderSystem.divisorClass_eq_zero_iff, OrderSystem.mem_principalSubgroup]
  constructor
  · rintro ⟨x, hx⟩
    have hxS : x.toMul ∈ S.unit K := (mem_unit_iff_support_principalDivisor_subset S K).mpr
      fun w hw ↦ by
        classical
        rw [ofMul_toMul, hx] at hw
        obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hw)
        exact v.property
    refine ⟨.ofMul ⟨x.toMul, hxS⟩, Finsupp.mapDomain_injective Subtype.val_injective ?_⟩
    rw [mapDomain_unitOrd, toMul_ofMul, ofMul_toMul, hx]
  · rintro ⟨u, rfl⟩
    exact ⟨_, (mapDomain_unitOrd S K u).symm⟩

/-- **Exactness at the class group of `R`.** The ideal classes that become principal in the
`S`-integers are exactly the inverse divisor classes of tuples supported on `S`. -/
theorem exact_invDivisorClass_extendedHom :
    Function.Exact S.invDivisorClass (ClassGroup.extendedHom R (S.integer K)).toAdditive := by
  intro c
  rw [← AddMonoidHom.coe_range, SetLike.mem_coe, range_invDivisorClass,
    Additive.mem_toAddSubgroup, ← ker_integer_extendedHom K S, MonoidHom.mem_ker,
    MonoidHom.toAdditive_apply_apply, ← toMul_eq_one, toMul_ofMul]

variable {S} in
/-- **Enlarging `S`, on `S`-units.** For `S ⊆ S'`, the positive orders of an `S`-unit regarded as
an `S'`-unit are its positive orders at the primes of `S`, extended by zero to `S'`. -/
theorem unitOrd_inclusion {S' : Set (HeightOneSpectrum R)} (h : S ⊆ S')
    (u : Additive (S.unit K)) :
    S'.unitOrd K (.ofMul (Subgroup.inclusion (unit_mono K h) u.toMul)) =
      (S.unitOrd K u).mapDomain (Set.inclusion h) := by
  apply Finsupp.mapDomain_injective Subtype.val_injective
  rw [← Finsupp.mapDomain_comp, Set.val_comp_inclusion, mapDomain_unitOrd, mapDomain_unitOrd,
    toMul_ofMul, Subgroup.coe_inclusion]

variable {S} in
/-- **Enlarging `S`, on divisor classes.** For `S ⊆ S'`, extending a tuple supported on `S` by
zero to `S'` does not change its inverse divisor class. -/
theorem invDivisorClass_mapDomain_inclusion {S' : Set (HeightOneSpectrum R)} (h : S ⊆ S')
    (n : ↥S →₀ ℤ) :
    S'.invDivisorClass (n.mapDomain (Set.inclusion h)) = S.invDivisorClass n := by
  induction n using Finsupp.induction_linear with
  | zero => simp
  | add n m hn hm => rw [Finsupp.mapDomain_add, map_add, map_add, hn, hm]
  | single v n => rw [Finsupp.mapDomain_single, invDivisorClass_single, invDivisorClass_single,
      Set.coe_inclusion]

end Set
