/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Finite generators in a localization away from an element

Finite-type algebras that are localizations admit finite sets of numerators controlling
surjectivity of ring maps into them.
-/

public section

namespace IsLocalization.Away

/-- A finite-type map into `A[r⁻¹]` admits finitely many numerators in `A` such that a ring map
into `A[r⁻¹]` is surjective whenever its range contains the base ring and these numerators,
and `r` has a unit lift. The base ring need not act on `A` or on the source of the ring map. -/
lemma exists_finset_surjective_of_finiteType
    {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra A B] (r : A) [IsLocalization.Away r B]
    (φ : R →+* B) (hφ : φ.FiniteType) :
    ∃ s : Finset A, ∀ {C : Type*} [CommRing C] (g : C →+* B),
      (∀ x, φ x ∈ g.range) →
      (∀ a ∈ s, algebraMap A B a ∈ g.range) →
      (∃ c : C, IsUnit c ∧ g c = algebraMap A B r) → Function.Surjective g := by
  classical
  let := φ.toAlgebra
  obtain ⟨t, ht⟩ := hφ.out
  refine ⟨t.image (fun b ↦ (IsLocalization.Away.sec r b).1), ?_⟩
  intro C _ g hR hs ⟨c, hc, hcr⟩
  let D : Subalgebra R B := { g.range with algebraMap_mem' := hR }
  have htD : Algebra.adjoin R (t : Set B) ≤ D := by
    refine Algebra.adjoin_le ?_
    intro b hb
    obtain ⟨a, ha⟩ := hs _ (Finset.mem_image.mpr ⟨b, hb, rfl⟩)
    obtain ⟨v, hv⟩ := hc
    let n := (IsLocalization.Away.sec r b).2
    have hv' : g (v : C) = algebraMap A B r := (congrArg g hv).trans hcr
    refine ⟨a * (↑(v⁻¹) : C) ^ n, ?_⟩
    apply (IsLocalization.Away.algebraMap_pow_isUnit r n).mul_right_cancel
    calc
      g (a * (↑(v⁻¹) : C) ^ n) * algebraMap A B r ^ n =
          g (a * ((↑(v⁻¹) : C) * ↑v) ^ n) := by
        rw [← hv', ← map_pow, ← map_mul, mul_assoc, ← mul_pow]
      _ = algebraMap A B (IsLocalization.Away.sec r b).1 := by simpa using ha
      _ = b * algebraMap A B r ^ n := by
        simpa only [n, map_pow] using (IsLocalization.Away.sec_spec r b).symm
  exact Algebra.eq_top_iff.mp (top_unique (ht ▸ htD))

end IsLocalization.Away
