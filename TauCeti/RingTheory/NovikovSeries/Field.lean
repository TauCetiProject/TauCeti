/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.IsField
public import TauCeti.RingTheory.NovikovSeries.Functoriality

/-!
# When a Novikov ring is a field

Over a field, an injective period map makes every nonzero Novikov series invertible.
Normalize its unique least-period term to obtain `1 - b`, where `b` has strictly
positive support. The inverse then comes from the convergent geometric series.
No discreteness of the period group is required.

Conversely, a Novikov ring can be a field only when its coefficient ring is a field
and its period map is injective. A nonzero period-kernel element gives a nonzero
element `1 - e^h` killed by pushforward along the period map. Thus retaining a
nontrivial period kernel really can obstruct the field property; it cannot be
discarded when constructing coefficient fields for total quotients.

The theorem `TauCeti.NovikovSeries.isField_iff` uses the native `IsField` predicate,
from which `IsField.toField` supplies a field structure. The normalization and
invertibility results also work over division rings, yielding the leading-term
factorization `a = single h (a.coeff h) * (1 + b)` at the least-period exponent
(`TauCeti.NovikovSeries.exists_mem_posIdeal_and_eq_single_mul_one_add_of_injective` and
`TauCeti.NovikovSeries.exists_mem_posIdeal_and_eq_single_order_mul_one_add`).

This is the leading-term normalization also used by Mathlib's `HahnSeries.inv`
in `Mathlib/RingTheory/HahnSeries/Summable.lean`. Here the geometric series
converges in the finite-cutoff Novikov topology, so its sum retains the stronger
Novikov support condition, rather than only a well-founded Hahn support.

## References

* A. Pajitnov, *Circle-valued Morse Theory*, de Gruyter 2006, Chapter 3.
* M. Hutchings, *Reidemeister torsion in generalized Morse theory*,
  Forum Math. 14 (2002), Section 2.
-/

public section

noncomputable section

namespace TauCeti.NovikovSeries

variable {R H : Type*}

section DivisionRing

variable [AddGroup H] {N : H →+ ℝ} [DivisionRing R]

/-- **Leading-term factorization with injective periods.** Over a division ring `R` and an
injective period map `N`, every nonzero series `a` factors at its least-period exponent `h`
(`N h = a.order`) as `single h (a.coeff h) * (1 + b)` with `b ∈ posIdeal R N`. -/
theorem exists_mem_posIdeal_and_eq_single_mul_one_add_of_injective
    (hN : Function.Injective N) {a : NovikovSeries R H N} (ha : a ≠ 0) :
    ∃ h : H, N h = a.order ∧ ∃ b : nonnegSubring R N, b ∈ posIdeal R N ∧
      a = single h (a.coeff h) * (1 + (b : NovikovSeries R H N)) := by
  classical
  obtain ⟨h, hr, hh⟩ := exists_coeff_ne_zero_and_period_eq_order ha
  let b : NovikovSeries R H N := single (-h) (a.coeff h)⁻¹ * a - 1
  have hb : ∀ g, N g ≤ 0 → b.coeff g = 0 := by
    intro g hg
    by_cases hg0 : g = 0
    · subst g
      simp [b, coeff_sub, coeff_one, coeff_single_mul, hr]
    · have hglt : N g < 0 := lt_of_le_of_ne hg fun he =>
        hg0 (hN (he.trans (map_zero N).symm))
      have hag : a.coeff (h + g) = 0 :=
        coeff_eq_zero_of_lt_order (by rw [map_add, hh]; linarith)
      simp [b, coeff_sub, coeff_one, coeff_single_mul, hg0, hag]
  let b' : nonnegSubring R N := ⟨b, mem_nonnegSubring.2 fun g hg => hb g hg.le⟩
  have hinv : (single h (a.coeff h) : NovikovSeries R H N) *
      single (-h) (a.coeff h)⁻¹ = 1 := by
    simp [single_mul_single, hr]
  exact ⟨h, hh, b', mem_posIdeal.2 hb, by simp [b', b, add_sub_cancel, ← mul_assoc, hinv]⟩

/-- With injective periods, every nonzero series is its least-period monomial times
`1 - b`, where `b` belongs to the strictly positive ideal. -/
theorem exists_single_mul_one_sub_of_injective (hN : Function.Injective N)
    {a : NovikovSeries R H N} (ha : a ≠ 0) :
    ∃ (h : H) (r : Rˣ) (b : nonnegSubring R N),
      b ∈ posIdeal R N ∧ a = single h (r : R) * (1 - (b : NovikovSeries R H N)) := by
  obtain ⟨h, -, b, hb, ha_eq⟩ := exists_mem_posIdeal_and_eq_single_mul_one_add_of_injective hN ha
  have hr : a.coeff h ≠ 0 := fun hr => ha (by simpa [hr] using ha_eq)
  exact ⟨h, Units.mk0 (a.coeff h) hr, -b, neg_mem hb, by simpa [sub_eq_add_neg] using ha_eq⟩

/-- **Leading-term factorization in the real Novikov division ring.** Over a division ring `R`,
every nonzero series `a` in `NovikovSeries R ℝ (AddMonoidHom.id ℝ)` factors at `a.order` as
`single a.order (a.coeff a.order) * (1 + b)` with `b ∈ posIdeal R (AddMonoidHom.id ℝ)`. -/
theorem exists_mem_posIdeal_and_eq_single_order_mul_one_add
    {a : NovikovSeries R ℝ (AddMonoidHom.id ℝ)} (ha : a ≠ 0) :
    ∃ b : nonnegSubring R (AddMonoidHom.id ℝ), b ∈ posIdeal R (AddMonoidHom.id ℝ) ∧
      a = single a.order (a.coeff a.order) * (1 + (b : NovikovSeries R ℝ (AddMonoidHom.id ℝ))) := by
  obtain ⟨t, ht, b, hb, ha_eq⟩ :=
    exists_mem_posIdeal_and_eq_single_mul_one_add_of_injective Function.injective_id ha
  rw [AddMonoidHom.id_apply] at ht
  exact ⟨b, hb, ht ▸ ha_eq⟩

/-- A nonzero series over a division ring is invertible when the period map is injective. -/
theorem isUnit_of_injective (hN : Function.Injective N)
    {a : NovikovSeries R H N} (ha : a ≠ 0) : IsUnit a := by
  obtain ⟨h, r, b, hb, rfl⟩ := exists_single_mul_one_sub_of_injective hN ha
  exact (isUnit_single h r.isUnit).mul
    ((isUnit_one_sub_of_mem_posIdeal hb).map (nonnegSubring R N).subtype)

end DivisionRing

section CommRing

variable [AddCommGroup H] {N : H →+ ℝ} [CommRing R]

/-- A Novikov ring is a field exactly when the coefficient ring is a field and
the period map is injective. This includes dense period groups and the trivial
exponent group. -/
theorem isField_iff : IsField (NovikovSeries R H N) ↔ IsField R ∧ Function.Injective N := by
  classical
  constructor
  · intro hf
    let := hf.toField
    have : Nontrivial R := by
      by_contra hR
      have : Subsingleton R := not_nontrivial_iff_subsingleton.1 hR
      have h01 : (0 : NovikovSeries R H N) = 1 := by
        ext g
        exact Subsingleton.elim _ _
      exact zero_ne_one h01
    have hR : IsField R :=
      { exists_pair_ne := exists_pair_ne R
        mul_comm := mul_comm
        mul_inv_cancel := fun {r} hr => by
          obtain ⟨b, hb⟩ := hf.mul_inv_cancel
            (a := single 0 r) (by simpa using hr)
          refine ⟨b.coeff 0, ?_⟩
          simpa [coeff_single_zero_mul] using congrArg (fun a => a.coeff 0) hb }
    refine ⟨hR, ?_⟩
    let f : NovikovSeries R H N →+* NovikovSeries R ℝ (AddMonoidHom.id ℝ) :=
      mapRingHom (RingHom.id R) N ⟨1, one_pos, by simp⟩
    intro h k hhk
    have hsingle : (single h 1 : NovikovSeries R H N) = single k 1 := by
      apply f.injective
      simpa [f] using congrArg (fun t => (single t 1 :
        NovikovSeries R ℝ (AddMonoidHom.id ℝ))) hhk
    by_contra hne
    have := congrArg (fun a => a.coeff h) hsingle
    simp [coeff_single_of_ne hne] at this
  · rintro ⟨hR, hN⟩
    let := hR.toField
    exact
      { exists_pair_ne := exists_pair_ne (NovikovSeries R H N)
        mul_comm := mul_comm
        mul_inv_cancel := fun ha => isUnit_iff_exists_inv.1 (isUnit_of_injective hN ha) }

end CommRing

end TauCeti.NovikovSeries
