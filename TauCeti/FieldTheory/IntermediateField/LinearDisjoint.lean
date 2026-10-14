/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.LinearDisjoint
public import Mathlib.FieldTheory.Relrank

/-!
# Relative degrees under linearly disjoint base change

If `A` is finite over `k` and linearly disjoint from `B` over `k`, adjoining `A` preserves the
relative degree of an intermediate extension `B/C`. This is the field-tower calculation behind
the degree comparison for algebraic function fields after extending their constants.

The main result is `IntermediateField.relfinrank_sup_sup_eq_relfinrank_of_linearDisjoint`. Apply it
as `A.relfinrank_sup_sup_eq_relfinrank_of_linearDisjoint B C hCB h`, where `hCB : C ≤ B` and
`h : A.LinearDisjoint B`; the finite-dimensionality of `A` is supplied by an instance. The
declarations live in Mathlib's `IntermediateField` namespace so that this dot notation works.

`IntermediateField.LinearDisjoint.linearIndependent_algebraMap_comp` extends scalars on the other
side: if the image of `k'` in a common overfield `E` is linearly disjoint from `F` over `k`, a
family of `F` linearly independent over `k` stays linearly independent over `k'` in `E`.
`TauCeti.linearDisjoint_fieldRange_of_forall_finiteDimensional` reduces that linear disjointness,
for algebraic `k' / k`, to the finite subextensions of `k' / k`.
-/

public section

noncomputable section

open scoped IntermediateField

namespace TauCeti

universe u v

variable {k : Type u} {L : Type v} [Field k] [Field L] [Algebra k L]

/-- Extending scalars from `D` to its compositum with `A` amounts to adjoining `A` to `D`. -/
theorem _root_.IntermediateField.extendScalars_sup_right_eq_adjoin (A D : IntermediateField k L) :
    IntermediateField.extendScalars (le_sup_right : D ≤ A ⊔ D) =
      IntermediateField.adjoin D (A : Set L) := by
  apply IntermediateField.restrictScalars_injective k
  rw [IntermediateField.extendScalars_restrictScalars,
    IntermediateField.restrictScalars_adjoin_eq_sup, sup_comm,
    IntermediateField.adjoin_self]

/-- An algebraic extension linearly disjoint from `D` has the same degree after adjoining `D`. -/
theorem _root_.IntermediateField.relfinrank_sup_right_eq_finrank_of_linearDisjoint
    (A D : IntermediateField k L) [Algebra.IsAlgebraic k A] (hAD : A.LinearDisjoint D) :
    IntermediateField.relfinrank D (A ⊔ D) =
      Module.finrank k A := by
  rw [IntermediateField.relfinrank_eq_finrank_of_le (le_sup_right : D ≤ A ⊔ D),
    IntermediateField.extendScalars_sup_right_eq_adjoin]
  exact congrArg Cardinal.toNat hAD.adjoin_rank_eq_rank_left_of_isAlgebraic_left

/-- Base change by a finite linearly disjoint extension preserves the degree of an intermediate
field extension. -/
theorem _root_.IntermediateField.relfinrank_sup_sup_eq_relfinrank_of_linearDisjoint
    (A B C : IntermediateField k L) (hCB : C ≤ B)
    [FiniteDimensional k A] (h : A.LinearDisjoint B) :
    IntermediateField.relfinrank (A ⊔ C) (A ⊔ B) =
      IntermediateField.relfinrank C B := by
  have hAB := A.relfinrank_sup_right_eq_finrank_of_linearDisjoint B h
  have hAC := A.relfinrank_sup_right_eq_finrank_of_linearDisjoint C (h.of_le_right hCB)
  have hmulB := IntermediateField.relfinrank_mul_relfinrank hCB
    (le_sup_right : B ≤ A ⊔ B)
  have hmulC := IntermediateField.relfinrank_mul_relfinrank
    (le_sup_right : C ≤ A ⊔ C) (sup_le_sup_left hCB A)
  rw [hAB] at hmulB
  rw [hAC] at hmulC
  have hpos : 0 < Module.finrank k A := Module.finrank_pos
  exact (Nat.eq_of_mul_eq_mul_left hpos (by rw [hmulC, ← hmulB, mul_comm])).symm

section ExtendScalars

variable {k' : Type*} {F : Type*} {E : Type*} [Field k'] [Field F] [Field E]
variable [Algebra k k'] [Algebra k F] [Algebra k E] [Algebra k' E] [Algebra F E]
variable [IsScalarTower k k' E] [IsScalarTower k F E]

/-- **Linear independence over `k` persists over `k'` under linear disjointness**: if the image of
`k'` in `E` and `F` are linearly disjoint over `k`, then a family of elements of `F` linearly
independent over `k` stays linearly independent over `k'` inside `E`. -/
theorem _root_.IntermediateField.LinearDisjoint.linearIndependent_algebraMap_comp
    (H : (IsScalarTower.toAlgHom k k' E).fieldRange.LinearDisjoint F) {ι : Type*} {v : ι → F}
    (hv : LinearIndependent k v) : LinearIndependent k' (algebraMap F E ∘ v) :=
  (H.linearIndependent_right' hv).map_of_injective_injective
    (IsScalarTower.toAlgHom k k' E).equivFieldRange (AddMonoidHom.id E) (by simp) (by simp)
    fun _ _ ↦ by
      simp only [AddMonoidHom.id_apply, Algebra.smul_def, IntermediateField.algebraMap_apply,
        AlgHom.equivFieldRange_apply_coe, IsScalarTower.toAlgHom_apply]

/-- **Linear disjointness from the finite subextensions**: if `k' / k` is algebraic and the image
in `E` of every finite subextension `M` of `k' / k` is linearly disjoint from `F` over `k`, then so
is the image of `k'`.  Finitely many elements of `k'` lie in a finite subextension. -/
theorem linearDisjoint_fieldRange_of_forall_finiteDimensional [Algebra.IsAlgebraic k k']
    (h : ∀ M : IntermediateField k k', FiniteDimensional k M →
      (IsScalarTower.toAlgHom k M E).fieldRange.LinearDisjoint F) :
    (IsScalarTower.toAlgHom k k' E).fieldRange.LinearDisjoint F := by
  set K := (IsScalarTower.toAlgHom k k' E).fieldRange
  let e := (IsScalarTower.toAlgHom k k' E).equivFieldRange
  have he (y : K) : algebraMap k' E (e.symm y) = y := by
    conv_rhs => rw [← e.apply_symm_apply y]
    rw [AlgHom.equivFieldRange_apply_coe, IsScalarTower.toAlgHom_apply]
  let b := Module.Basis.ofVectorSpace k K
  refine .of_basis_left b (linearIndependent_iff_finset_linearIndependent.2 fun s ↦ ?_)
  -- the finitely many basis vectors indexed by `s` come from a finite subextension `M`
  let M : IntermediateField k k' :=
    IntermediateField.adjoin k (Set.range fun i : s ↦ e.symm (b i))
  have : FiniteDimensional k M := IntermediateField.finiteDimensional_adjoin fun _ _ ↦
    (Algebra.IsAlgebraic.isAlgebraic _).isIntegral
  let KM := (IsScalarTower.toAlgHom k M E).fieldRange
  let v : s → KM := fun i ↦
    ⟨b i, ⟨⟨e.symm (b i), IntermediateField.subset_adjoin k _ ⟨i, rfl⟩⟩, he (b i)⟩⟩
  have hb : LinearIndependent k (K.val ∘ b) :=
    b.linearIndependent.map' K.val.toLinearMap (LinearMap.ker_eq_bot.2 Subtype.val_injective)
  have hv : LinearIndependent k v :=
    .of_comp KM.val.toLinearMap (hb.comp _ Subtype.val_injective)
  -- `v` and the basis vectors indexed by `s` have the same underlying elements of `E`
  convert (h M this).linearIndependent_left hv using 1
  ext i
  simp [v]

end ExtendScalars

end TauCeti
