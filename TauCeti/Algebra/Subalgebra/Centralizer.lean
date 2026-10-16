/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Tower
public import Mathlib.LinearAlgebra.Dimension.Free

/-!
# A centralizer as an algebra over a commutative subalgebra

If `S` is a commutative subalgebra of `A`, its centralizer `C` is naturally an
`S`-algebra. Subalgebras of `C` over `S` correspond to subalgebras of `A` over the
original base containing `S` and contained in `C`. The correspondence preserves
the underlying elements and records the degree multiplication in a field tower.

This permits enlargement of subfields inside a division algebra: an extension constructed
in the centralizer is transported back to a subalgebra of the original algebra containing
the original subfield.

## References

* R. S. Pierce, *Associative Algebras*, Springer GTM 88 (1982), Chapter 13.
-/

public section

namespace Subalgebra

open scoped IsMulCommutative

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
  (S : Subalgebra R A) [IsMulCommutative S]

/-- A commutative subalgebra acts on its centralizer by multiplication. -/
instance centralizerAlgebra : Algebra S (centralizer R (S : Set A)) :=
  (inclusion (fun _ hx ↦ (mem_centralizer_iff R).mpr fun _ hy ↦
    setLike_mul_comm hy hx)).toRingHom.toAlgebra' fun s c ↦
      Subtype.ext ((mem_centralizer_iff R).mp c.property s s.property)

/-- The structure map from a commutative subalgebra to its centralizer is inclusion. -/
@[simp]
theorem coe_algebraMap_centralizer (s : S) :
    (algebraMap S (centralizer R (S : Set A)) s : A) = s := (rfl)

/-- The scalar action on the centralizer is multiplication in the ambient algebra. -/
@[simp]
theorem coe_smul_centralizer (s : S) (c : centralizer R (S : Set A)) :
    ((s • c : centralizer R (S : Set A)) : A) = (s : A) * (c : A) := by
  simp [Algebra.smul_def]

/-- The centralizer's action by the commutative subalgebra extends its original base action. -/
instance isScalarTower_centralizerAlgebra :
    IsScalarTower R S (centralizer R (S : Set A)) :=
  IsScalarTower.of_algebraMap_eq fun r ↦ Subtype.ext (by simp)

/-- Subalgebras of a centralizer over its commutative scalar subalgebra correspond
to ambient subalgebras lying between the scalar subalgebra and its centralizer. -/
def centralizerSubalgebraOrderIso :
    Subalgebra S (centralizer R (S : Set A)) ≃o
      {T : Subalgebra R A // S ≤ T ∧ T ≤ centralizer R (S : Set A)} where
  toFun T := ⟨(T.restrictScalars R).map (centralizer R (S : Set A)).val, by
    constructor
    · intro s hs
      exact ⟨algebraMap S (centralizer R (S : Set A)) ⟨s, hs⟩,
        T.algebraMap_mem ⟨s, hs⟩, by simp⟩
    · rintro _ ⟨c, _, rfl⟩
      exact c.property⟩
  invFun T :=
    { (T.val.comap (centralizer R (S : Set A)).val).toSubsemiring with
      algebraMap_mem' := fun s ↦ by
        -- The new subalgebra retains the carrier of this preimage subalgebra.
        exact (by simpa only [coe_algebraMap_centralizer] using T.property.1 s.property :
          ((algebraMap S (centralizer R (S : Set A)) s) : A) ∈ T.val) }
  left_inv T := by
    ext c
    -- The inverse construction inherits the carrier of the scalar-restricted preimage.
    exact ⟨fun ⟨d, hd, hdc⟩ ↦ Subtype.ext hdc ▸ hd, fun hc ↦ ⟨c, hc, rfl⟩⟩
  right_inv T := by
    apply Subtype.ext
    ext a
    simp only [mem_map, mem_restrictScalars, val_apply]
    exact ⟨fun ⟨_, hc, hca⟩ ↦ hca ▸ hc,
      fun ha ↦ ⟨⟨a, T.property.2 ha⟩, ha, rfl⟩⟩
  map_rel_iff' := by
    intro T U
    constructor
    · intro h c hc
      obtain ⟨d, hd, hdc⟩ := h (mem_map.mpr ⟨c, hc, rfl⟩)
      exact Subtype.ext hdc ▸ hd
    · intro h a ha
      obtain ⟨c, hc, rfl⟩ := ha
      exact mem_map.mpr ⟨c, h hc, rfl⟩

/-- The forward correspondence restricts scalars and includes into the ambient algebra. -/
theorem centralizerSubalgebraOrderIso_apply
    (T : Subalgebra S (centralizer R (S : Set A))) :
    (S.centralizerSubalgebraOrderIso T).val =
      (T.restrictScalars R).map (centralizer R (S : Set A)).val := (rfl)

/-- An element of the centralizer belongs to the transported subalgebra exactly
when it belongs to the original subalgebra over `S`. -/
@[simp]
theorem mem_centralizerSubalgebraOrderIso
    (T : Subalgebra S (centralizer R (S : Set A)))
    (c : centralizer R (S : Set A)) :
    (c : A) ∈ (S.centralizerSubalgebraOrderIso T).val ↔ c ∈ T := by
  rw [centralizerSubalgebraOrderIso_apply]
  simp only [mem_map, mem_restrictScalars, val_apply]
  exact ⟨fun ⟨d, hd, hdc⟩ ↦ Subtype.ext hdc ▸ hd, fun hc ↦ ⟨c, hc, rfl⟩⟩

/-- The inverse correspondence tests ambient membership after including the centralizer. -/
@[simp]
theorem mem_centralizerSubalgebraOrderIso_symm
    (T : {T : Subalgebra R A // S ≤ T ∧ T ≤ centralizer R (S : Set A)})
    (c : centralizer R (S : Set A)) :
    c ∈ S.centralizerSubalgebraOrderIso.symm T ↔ (c : A) ∈ T.val := (Iff.rfl)

/-- The scalar subalgebra corresponds to the bottom subalgebra of the centralizer over `S`. -/
@[simp]
theorem centralizerSubalgebraOrderIso_bot :
    (S.centralizerSubalgebraOrderIso ⊥).val = S := by
  rw [centralizerSubalgebraOrderIso_apply]
  ext a
  simp only [mem_map, mem_restrictScalars, Algebra.mem_bot]
  constructor
  · rintro ⟨c, ⟨s, rfl⟩, rfl⟩
    simp
  · intro ha
    exact ⟨algebraMap S (centralizer R (S : Set A)) ⟨a, ha⟩,
      ⟨⟨a, ha⟩, rfl⟩, by simp⟩

/-- The whole centralizer corresponds to the top subalgebra over `S`. -/
@[simp]
theorem centralizerSubalgebraOrderIso_top :
    (S.centralizerSubalgebraOrderIso ⊤).val = centralizer R (S : Set A) := by
  rw [centralizerSubalgebraOrderIso_apply]
  ext a
  simp only [mem_map, mem_restrictScalars, Algebra.mem_top, true_and, val_apply]
  exact ⟨fun ⟨c, hca⟩ ↦ hca ▸ c.property, fun ha ↦ ⟨⟨a, ha⟩, rfl⟩⟩

/-- A nontrivial extension inside the centralizer gives a strict enlargement of the
original scalar subalgebra inside the ambient algebra. -/
theorem lt_centralizerSubalgebraOrderIso_iff
    (T : Subalgebra S (centralizer R (S : Set A))) :
    S < (S.centralizerSubalgebraOrderIso T).val ↔ ⊥ < T := by
  have h := S.centralizerSubalgebraOrderIso.lt_iff_lt (x := ⊥) (y := T)
  rw [← Subtype.coe_lt_coe] at h
  simpa only [centralizerSubalgebraOrderIso_bot] using h

/-- The transported subalgebra has the dimension prescribed by the scalar tower.
In particular, for subfields this is multiplication of extension degrees. -/
theorem finrank_centralizerSubalgebraOrderIso [StrongRankCondition R]
    [StrongRankCondition S] [Module.Free R S]
    (T : Subalgebra S (centralizer R (S : Set A))) [Module.Free S T] :
    Module.finrank R (S.centralizerSubalgebraOrderIso T).val =
      Module.finrank R S * Module.finrank S T := by
  rw [centralizerSubalgebraOrderIso_apply]
  exact ((T.restrictScalars R).equivMapOfInjective
    (centralizer R (S : Set A)).val Subtype.val_injective).toLinearEquiv.finrank_eq.symm.trans
      (Module.finrank_mul_finrank R S T).symm

end Subalgebra
