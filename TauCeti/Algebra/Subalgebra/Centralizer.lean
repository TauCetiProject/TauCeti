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
  toFun T := ⟨(T.restrictScalars R).map (centralizer R (S : Set A)).val,
    fun s hs ↦ mem_map.mpr ⟨algebraMap S _ ⟨s, hs⟩,
      (mem_restrictScalars R).mpr (T.algebraMap_mem _), rfl⟩,
    map_le.mpr fun c _ ↦ c.property⟩
  invFun T :=
    { (T.val.comap (centralizer R (S : Set A)).val).toSubsemiring with
      algebraMap_mem' := fun s ↦ by simpa using T.property.1 s.property }
  left_inv T := by ext; simp
  right_inv T := Subtype.ext <| map_comap_eq_self <| by rw [range_val]; exact T.property.2
  map_rel_iff' {T U} := by
    simp only [Equiv.coe_fn_mk, Subtype.mk_le_mk]
    rw [map_le, comap_map_eq_self_of_injective Subtype.val_injective]
    simp [← SetLike.coe_subset_coe]

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
  simp [centralizerSubalgebraOrderIso_apply]

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
  refine le_antisymm ?_ (S.centralizerSubalgebraOrderIso ⊥).property.1
  rw [centralizerSubalgebraOrderIso_apply, map_le]
  intro c hc
  obtain ⟨s, rfl⟩ := Algebra.mem_bot.mp ((mem_restrictScalars R).mp hc)
  simp

/-- The whole centralizer corresponds to the top subalgebra over `S`. -/
@[simp]
theorem centralizerSubalgebraOrderIso_top :
    (S.centralizerSubalgebraOrderIso ⊤).val = centralizer R (S : Set A) := by
  simp [centralizerSubalgebraOrderIso_apply, range_val]

/-- A nontrivial extension inside the centralizer gives a strict enlargement of the
original scalar subalgebra inside the ambient algebra. -/
theorem lt_centralizerSubalgebraOrderIso_iff
    (T : Subalgebra S (centralizer R (S : Set A))) :
    S < (S.centralizerSubalgebraOrderIso T).val ↔ ⊥ < T := by
  simpa only [← Subtype.coe_lt_coe, centralizerSubalgebraOrderIso_bot] using
    S.centralizerSubalgebraOrderIso.lt_iff_lt (x := ⊥) (y := T)

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
