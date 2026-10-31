/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
public import Mathlib.Algebra.MonoidAlgebra.Support

/-!
# Units of additive monoid algebras

Over a nontrivial semiring without zero divisors, an additive monoid with two unique sums has
only monomial units in its monoid algebra. The coefficient must be a unit of the coefficient
semiring and the exponent must be an additive unit of the monoid. In particular, for an
additive submonoid `S` of a lattice, the permitted exponents are precisely those `a ∈ S` with
`-a ∈ S`. No saturation or finite generation assumption on `S` is needed.

`AddMonoidAlgebra.unitsEquiv` identifies the unit group with the product of the coefficient
unit group and the additive unit group of the monoid (written multiplicatively).
The support argument uses Mathlib's `TwoUniqueSums` and
`AddMonoidAlgebra.coeff_mul_add_of_uniqueAdd`: a product with singleton support cannot have
two distinct uniquely represented sums with nonzero coefficients.

## References

* W. Bruns and J. Gubeladze, *Polytopes, Rings, and K-Theory*, Chapter 2, units of monoid rings.
-/

public section

namespace AddMonoidAlgebra

variable {R M : Type*} [Semiring R] [AddMonoid M]

/-- A coefficient unit and an additive unit exponent determine a monomial unit. -/
noncomputable def unitsSingle : Rˣ × Multiplicative (AddUnits M) →* (AddMonoidAlgebra R M)ˣ where
  toFun p :=
    { val := single (p.2.toAdd : M) (p.1 : R)
      inv := single ((-p.2.toAdd : AddUnits M) : M) ((p.1⁻¹ : Rˣ) : R)
      val_inv := by simp [single_mul_single, ← AddUnits.val_add, one_def]
      inv_val := by simp [single_mul_single, ← AddUnits.val_add, one_def] }
  map_one' := Units.ext (by simp [one_def])
  map_mul' p q := Units.ext (by simp [single_mul_single, AddUnits.val_add])

@[simp]
theorem coe_unitsSingle (p : Rˣ × Multiplicative (AddUnits M)) :
    (unitsSingle p : AddMonoidAlgebra R M) = single (p.2.toAdd : M) (p.1 : R) :=
  (rfl)

/-- A monomial is a unit exactly when its exponent and coefficient are units. This does not
require a domain or a unique-sums hypothesis. -/
@[simp]
theorem isUnit_single_iff [Nontrivial R] (a : M) (r : R) :
    IsUnit (single a r : AddMonoidAlgebra R M) ↔ IsAddUnit a ∧ IsUnit r := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨g, hfg, hgf⟩ := isUnit_iff_exists.mp h
    have ha : IsAddUnit a := by
      rw [isAddUnit_iff_exists_and_exists]
      constructor
      · by_contra! hn
        have hz := coeff_single_mul_of_forall_add_ne r g hn
        simp [hfg] at hz
      · by_contra! hn
        have hz := coeff_mul_single_of_forall_add_ne r g hn
        simp [hgf] at hz
    obtain ⟨u, rfl⟩ := ha
    have hr := congrArg (fun x : AddMonoidAlgebra R M ↦ x.coeff 0) hfg
    have hs := congrArg (fun x : AddMonoidAlgebra R M ↦ x.coeff 0) hgf
    rw [coeff_single_mul_eq_mul_coeff ((-u : AddUnits M) : M)
      (fun _ _ ↦ AddUnits.add_eq_zero_iff_neg_eq.trans eq_comm)] at hr
    rw [coeff_mul_single_eq_coeff_mul ((-u : AddUnits M) : M)
      (fun _ _ ↦ AddUnits.add_eq_zero_iff_eq_neg)] at hs
    exact ⟨u.isAddUnit, isUnit_iff_exists.mpr
      ⟨g.coeff ((-u : AddUnits M) : M), by simpa using hr, by simpa using hs⟩⟩
  · rintro ⟨⟨u, rfl⟩, ⟨v, rfl⟩⟩
    exact (unitsSingle (v, Multiplicative.ofAdd u)).isUnit

/-- The coefficient unit and the additive unit exponent of a monomial unit are unique. -/
theorem unitsSingle_injective [Nontrivial R] :
    Function.Injective (unitsSingle (R := R) (M := M)) := by
  intro p q h
  have heq := congrArg (fun u : (AddMonoidAlgebra R M)ˣ ↦ (u : AddMonoidAlgebra R M)) h
  simp only [coe_unitsSingle] at heq
  obtain ⟨ha, hr⟩ := (single_inj.mp heq).resolve_right (fun h ↦ p.1.ne_zero h.1)
  apply Prod.ext
  · exact Units.ext hr
  · exact congrArg Multiplicative.ofAdd (AddUnits.ext ha)

section NoZeroDivisors

variable [Nontrivial R] [NoZeroDivisors R] [TwoUniqueSums M]

/-- A factor of a product equal to one has exactly one exponent in its support. -/
theorem card_support_coeff_eq_one_of_mul_eq_one (f g : AddMonoidAlgebra R M)
    (hfg : f * g = 1) : f.coeff.support.card = 1 := by
  classical
  have hf : f.coeff.support.Nonempty := Finsupp.support_nonempty_iff.mpr
    (mt coeff_eq_zero.mp (left_ne_zero_of_mul_eq_one hfg))
  have hg : g.coeff.support.Nonempty := Finsupp.support_nonempty_iff.mpr
    (mt coeff_eq_zero.mp (right_ne_zero_of_mul_eq_one hfg))
  have hcard : f.coeff.support.card * g.coeff.support.card ≤ 1 := by
    by_contra! h
    obtain ⟨p, hp, q, hq, hpq, hu, hv⟩ := TwoUniqueSums.uniqueAdd_of_one_lt_card h
    rw [Finset.mem_product] at hp hq
    have hzero (a b : M) (ha : a ∈ f.coeff.support) (hb : b ∈ g.coeff.support)
        (hab : UniqueAdd f.coeff.support g.coeff.support a b) : a + b = 0 := by
      have hn : (f * g).coeff (a + b) ≠ 0 := by
        rw [coeff_mul_add_of_uniqueAdd hab]
        exact mul_ne_zero (Finsupp.mem_support_iff.mp ha) (Finsupp.mem_support_iff.mp hb)
      have hm : a + b ∈ (1 : AddMonoidAlgebra R M).coeff.support := by
        simpa [hfg] using Finsupp.mem_support_iff.mpr hn
      simpa using hm
    have heq := hu hq.1 hq.2 ((hzero _ _ hq.1 hq.2 hv).trans (hzero _ _ hp.1 hp.2 hu).symm)
    exact hpq (Prod.ext heq.1.symm heq.2.symm)
  exact eq_one_of_mul_le_one_left (Finset.card_pos.mpr hf) (Finset.card_pos.mpr hg) hcard

/-- Every unit is a monomial with a unit coefficient and an additively invertible exponent. -/
theorem isUnit_iff_exists_single (f : AddMonoidAlgebra R M) :
    IsUnit f ↔ ∃ (a : M) (r : R), IsAddUnit a ∧ IsUnit r ∧ f = single a r := by
  classical
  refine ⟨fun hf ↦ ?_, ?_⟩
  · obtain ⟨g, hfg, -⟩ := isUnit_iff_exists.mp hf
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp (card_support_coeff_eq_one_of_mul_eq_one f g hfg)
    have hfa : f = single a (f.coeff a) := coeff_inj.mp (Finsupp.support_subset_singleton.mp ha.le)
    have hu := (isUnit_single_iff a (f.coeff a)).mp (hfa ▸ hf)
    exact ⟨a, f.coeff a, hu.1, hu.2, hfa⟩
  · rintro ⟨a, r, ha, hr, rfl⟩
    exact (isUnit_single_iff a r).mpr ⟨ha, hr⟩

/-- Every unit of the monoid algebra is in the image of the monomial-unit map. -/
theorem unitsSingle_surjective : Function.Surjective (unitsSingle (R := R) (M := M)) := by
  intro u
  obtain ⟨a, r, ⟨v, rfl⟩, ⟨w, rfl⟩, hu⟩ := (isUnit_iff_exists_single _).mp u.isUnit
  exact ⟨(w, Multiplicative.ofAdd v), Units.ext hu.symm⟩

/-- The unit group of the monoid algebra is the product of the coefficient units and the
additive units of the exponent monoid. -/
noncomputable def unitsEquiv :
    (AddMonoidAlgebra R M)ˣ ≃* Rˣ × Multiplicative (AddUnits M) :=
  (MulEquiv.ofBijective unitsSingle ⟨unitsSingle_injective, unitsSingle_surjective⟩).symm

@[simp]
theorem unitsEquiv_symm_apply (p : Rˣ × Multiplicative (AddUnits M)) :
    (unitsEquiv (R := R) (M := M)).symm p = unitsSingle p :=
  (rfl)

@[simp]
theorem unitsEquiv_unitsSingle (p : Rˣ × Multiplicative (AddUnits M)) :
    unitsEquiv (unitsSingle p) = p :=
  (unitsEquiv (R := R) (M := M)).apply_symm_apply p

end NoZeroDivisors

section AddSubmonoid

variable {G : Type*} [AddCommGroup G] [TwoUniqueSums G]
  [Nontrivial R] [NoZeroDivisors R] {S : AddSubmonoid G}

/-- For a submonoid of a lattice (or any group with two unique sums), the unit exponents are
exactly those whose negatives also belong to the submonoid. -/
theorem isUnit_iff_exists_single_neg_mem (f : AddMonoidAlgebra R S) :
    IsUnit f ↔ ∃ (a : S) (r : R), IsUnit r ∧ -(a : G) ∈ S ∧ f = single a r := by
  let : TwoUniqueSums S := TwoUniqueSums.of_injective_addHom
    S.subtype.toAddHom Subtype.val_injective inferInstance
  have hunit (a : S) : IsAddUnit a ↔ -(a : G) ∈ S := by
    rw [isAddUnit_iff_exists]
    constructor
    · rintro ⟨b, hab, -⟩
      have hab' : (a : G) + (b : G) = 0 := congrArg Subtype.val hab
      exact (eq_neg_of_add_eq_zero_right hab') ▸ b.property
    · intro ha
      exact ⟨⟨-(a : G), ha⟩, Subtype.ext (add_neg_cancel _), Subtype.ext (neg_add_cancel _)⟩
  simp only [isUnit_iff_exists_single, hunit, and_left_comm]

end AddSubmonoid

end AddMonoidAlgebra
