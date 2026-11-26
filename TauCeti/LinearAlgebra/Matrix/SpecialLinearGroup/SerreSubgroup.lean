/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Index
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Transvection
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Index
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Transvection.FinTwo

/-!
# Serre's relative elementary subgroup of `SL₂`

Let `A` be a commutative ring and `I` an ideal of `A`. *Serre's relative elementary subgroup*
`Eˢ(A, I)` is the normal closure in `SL₂(A)` of the upper transvections `e₀₁(t) = [[1, t], [0, 1]]`
with `t ∈ I`. It lies in the principal congruence subgroup `Γ₂(I)`, the kernel of reduction
modulo `I`. The ambient group of the normal closure is all of `SL₂(A)`: the relative elementary
group `E₂(A, I)` is the normal closure of the same transvections in the elementary subgroup
`E₂(A)` only, and is therefore contained in `Eˢ(A, I)`. Conjugating by
the Weyl element `[[0, -1], [1, 0]]` exchanges the upper and the lower transvections, so `Eˢ(A, I)`
also contains every lower transvection `e₁₀(t)` with `t ∈ I`.

These subgroups give the congruence levels of Serre's solution of the congruence subgroup problem
for `SL₂` over rings of `S`-integers. The first step of that argument is that every finite-index
subgroup `H` of `SL₂(A)` contains a nonzero level `Eˢ(A, I)` as soon as `A` has characteristic
zero. The proof is short: the transvections `e₀₁(t)` lying in the normal core `N` of `H` form a
subgroup of finite index `m` of the additive group of `A`, so `e₀₁(m a) ∈ N` for every `a`, and
`N`, being normal, then contains the normal closure of these transvections. Nothing beyond
`m ≠ 0` is used, so the argument applies to every root of `SL_ι(A)` for every finite index type
`ι` (`Subgroup.exists_normalClosure_transvection_span_le`). In characteristic zero the ideal
`m A` is nonzero; this holds without any assumption on the unit group of `A`.

The class of a matrix of `Γ₂(I)` modulo `Eˢ(A, I)` depends only on its first row: two
determinant-one matrices with the same first row differ by a lower transvection on the left, which
lies in `Eˢ(A, I)` as soon as both matrices are congruent to `1` modulo `I`.

## Main definitions

* `Ideal.serreElementarySubgroup I`: Serre's relative elementary subgroup `Eˢ(A, I)` of
  `SL₂(A)`.

## Main results

* `Ideal.serreElementarySubgroup_le_iff`: a normal subgroup contains `Eˢ(A, I)` exactly when it
  contains the upper transvections at level `I`; `Ideal.serreElementarySubgroup_le_ker_iff` is
  the same statement for the kernel of a homomorphism.
* `Ideal.transvection_one_zero_mem_serreElementarySubgroup`: the lower transvections at level `I`
  lie in `Eˢ(A, I)`.
* `Ideal.serreElementarySubgroup_le_ker_map`: `Eˢ(A, I)` lies in the principal congruence
  subgroup of level `I`.
* `Ideal.serreElementarySubgroup_mono`, `Ideal.serreElementarySubgroup_bot`,
  `Ideal.map_serreElementarySubgroup_le`: monotonicity, the zero level, and transport along ring
  homomorphisms.
* `Ideal.closure_transvections_le_serreElementarySubgroup`: `Eˢ(A, I)` contains every
  transvection with parameter in `I`, hence the subgroup they generate.
* `Ideal.serreElementarySubgroup_top_of_closure_eq_top`: when transvections generate `SL₂(A)`,
  the unit level is all of `SL₂(A)`; `Ideal.serreElementarySubgroup_top_of_field` and
  `Ideal.serreElementarySubgroup_top_int` are the cases of a field and of `ℤ`.
* `Ideal.mul_inv_mem_serreElementarySubgroup_of_row_zero_eq`: two matrices of `Γ₂(I)` with the
  same first row are congruent modulo `Eˢ(A, I)`.
* `Subgroup.exists_serreElementarySubgroup_le`: in characteristic zero, every finite-index
  subgroup of `SL₂(A)` contains `Eˢ(A, I)` for some nonzero ideal `I`.

## References

* J.-P. Serre, *Le problème des groupes de congruence pour SL2*, Ann. of Math. (2) 92 (1970),
  489–527, §1.4, Proposition 1.
-/

public section

open Matrix (SpecialLinearGroup TransvectionStruct)
open Matrix.SpecialLinearGroup

namespace Ideal

variable {A : Type*} [CommRing A] (I : Ideal A)

/-- **Serre's relative elementary subgroup** `Eˢ(A, I)`: the normal closure in `SL₂(A)` of the
upper transvections `[[1, t], [0, 1]]` with `t ∈ I`. -/
def serreElementarySubgroup : Subgroup (SpecialLinearGroup (Fin 2) A) :=
  Subgroup.normalClosure (transvection (zero_ne_one : (0 : Fin 2) ≠ 1) '' I)

/-- Serre's relative elementary subgroup is the normal closure in `SL₂(A)` of the upper
transvections with parameter in `I`. -/
theorem serreElementarySubgroup_def :
    I.serreElementarySubgroup =
      Subgroup.normalClosure (transvection (zero_ne_one : (0 : Fin 2) ≠ 1) '' I) :=
  (rfl)

/-- Serre's relative elementary subgroup is normal in `SL₂(A)`. -/
instance normal_serreElementarySubgroup : I.serreElementarySubgroup.Normal :=
  Subgroup.normalClosure_normal

variable {I}

/-- The upper transvections at level `I` lie in Serre's relative elementary subgroup. -/
theorem transvection_zero_one_mem_serreElementarySubgroup {t : A} (ht : t ∈ I) :
    transvection (zero_ne_one : (0 : Fin 2) ≠ 1) t ∈ I.serreElementarySubgroup :=
  Subgroup.subset_normalClosure ⟨t, ht, rfl⟩

/-- A normal subgroup of `SL₂(A)` contains Serre's relative elementary subgroup at level `I`
exactly when it contains the upper transvections at level `I`. -/
theorem serreElementarySubgroup_le_iff {N : Subgroup (SpecialLinearGroup (Fin 2) A)} [N.Normal] :
    I.serreElementarySubgroup ≤ N ↔
      ∀ t ∈ I, transvection (zero_ne_one : (0 : Fin 2) ≠ 1) t ∈ N := by
  refine ⟨fun h t ht ↦ h (transvection_zero_one_mem_serreElementarySubgroup ht), fun h ↦ ?_⟩
  refine Subgroup.normalClosure_le_normal ?_
  rintro _ ⟨t, ht, rfl⟩
  exact h t ht

/-- A homomorphism kills Serre's relative elementary subgroup at level `I` exactly when it kills
the upper transvections at level `I`. -/
theorem serreElementarySubgroup_le_ker_iff {G : Type*} [Group G]
    (φ : SpecialLinearGroup (Fin 2) A →* G) :
    I.serreElementarySubgroup ≤ φ.ker ↔
      ∀ t ∈ I, φ (transvection (zero_ne_one : (0 : Fin 2) ≠ 1) t) = 1 :=
  serreElementarySubgroup_le_iff

/-- The lower transvections at level `I` lie in Serre's relative elementary subgroup. -/
theorem transvection_one_zero_mem_serreElementarySubgroup {t : A} (ht : t ∈ I) :
    transvection (one_ne_zero : (1 : Fin 2) ≠ 0) t ∈ I.serreElementarySubgroup := by
  -- conjugation by the Weyl element `[[0, -1], [1, 0]]`, a product of three transvections,
  -- turns the upper transvection with parameter `-t` into the lower one with parameter `t`
  set w : SpecialLinearGroup (Fin 2) A :=
    transvection (zero_ne_one : (0 : Fin 2) ≠ 1) (-1) *
      transvection (one_ne_zero : (1 : Fin 2) ≠ 0) 1 *
        transvection (zero_ne_one : (0 : Fin 2) ≠ 1) (-1)
  have hw : w * transvection (zero_ne_one : (0 : Fin 2) ≠ 1) (-t) =
      transvection (one_ne_zero : (1 : Fin 2) ≠ 0) t * w := by
    refine Matrix.SpecialLinearGroup.ext _ _ fun i j ↦ ?_
    simp only [w, coe_mul, coe_transvection_zero_one, coe_transvection_one_zero]
    fin_cases i <;> fin_cases j <;> simp
  rw [eq_mul_inv_of_mul_eq hw.symm]
  exact I.normal_serreElementarySubgroup.conj_mem _
    (transvection_zero_one_mem_serreElementarySubgroup (I.neg_mem ht)) w

/-- Every transvection of `SL₂(A)` with parameter in `I` lies in Serre's relative elementary
subgroup at level `I`. -/
theorem _root_.Matrix.TransvectionStruct.toSpecialLinearGroup_mem_serreElementarySubgroup
    (t : TransvectionStruct (Fin 2) A) (ht : t.c ∈ I) :
    t.toSpecialLinearGroup ∈ I.serreElementarySubgroup := by
  obtain ⟨i, j, hij, c⟩ := t
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact transvection_zero_one_mem_serreElementarySubgroup ht
  · exact transvection_one_zero_mem_serreElementarySubgroup ht
  · exact absurd rfl hij

/-- Serre's relative elementary subgroup grows with the ideal. -/
theorem serreElementarySubgroup_mono {J : Ideal A} (hIJ : I ≤ J) :
    I.serreElementarySubgroup ≤ J.serreElementarySubgroup :=
  Subgroup.normalClosure_mono (Set.image_mono hIJ)

/-- At the zero level, Serre's relative elementary subgroup is trivial. -/
@[simp]
theorem serreElementarySubgroup_bot :
    (⊥ : Ideal A).serreElementarySubgroup = ⊥ := by
  refine eq_bot_iff.2 (serreElementarySubgroup_le_iff.2 fun t ht ↦ ?_)
  rw [(Submodule.mem_bot A).1 ht, transvection_coeff_zero]
  exact Subgroup.one_mem _

/-- Serre's relative elementary subgroup lies in the principal congruence subgroup of the same
level, the kernel of reduction modulo `I`. -/
theorem serreElementarySubgroup_le_ker_map :
    I.serreElementarySubgroup ≤ (SpecialLinearGroup.map (Ideal.Quotient.mk I)).ker := by
  refine (serreElementarySubgroup_le_ker_iff _).2 fun t ht ↦ ?_
  rw [map_transvection, Ideal.Quotient.eq_zero_iff_mem.2 ht, transvection_coeff_zero]

/-- A ring homomorphism `f` carrying `I` into `J` carries Serre's relative elementary subgroup
at level `I` into the one at level `J`. -/
theorem map_serreElementarySubgroup_le {B : Type*} [CommRing B] (f : A →+* B) {J : Ideal B}
    (hIJ : I.map f ≤ J) :
    I.serreElementarySubgroup.map (SpecialLinearGroup.map f) ≤ J.serreElementarySubgroup := by
  refine Subgroup.map_le_iff_le_comap.2 (serreElementarySubgroup_le_iff.2 fun t ht ↦ ?_)
  rw [Subgroup.mem_comap, map_transvection]
  exact transvection_zero_one_mem_serreElementarySubgroup (hIJ (Ideal.mem_map_of_mem f ht))

/-- Two matrices of the principal congruence subgroup of level `I` with the same first row are
congruent modulo Serre's relative elementary subgroup. -/
theorem mul_inv_mem_serreElementarySubgroup_of_row_zero_eq
    {M N : SpecialLinearGroup (Fin 2) A}
    (hM : M ∈ (SpecialLinearGroup.map (Ideal.Quotient.mk I)).ker)
    (hN : N ∈ (SpecialLinearGroup.map (Ideal.Quotient.mk I)).ker)
    (h : (M : Matrix (Fin 2) (Fin 2) A).row 0 = (N : Matrix (Fin 2) (Fin 2) A).row 0) :
    N * M⁻¹ ∈ I.serreElementarySubgroup := by
  obtain ⟨t, rfl⟩ := exists_eq_transvection_mul_of_row_zero_eq h
  rw [mul_inv_cancel_right]
  refine transvection_one_zero_mem_serreElementarySubgroup ?_
  -- the lower transvection `N * M⁻¹` is itself congruent to `1` modulo `I`
  have hmem := Subgroup.mul_mem _ hN (Subgroup.inv_mem _ hM)
  rw [mul_inv_cancel_right, MonoidHom.mem_ker, map_transvection,
    ← transvection_coeff_zero (one_ne_zero : (1 : Fin 2) ≠ 0)] at hmem
  exact Ideal.Quotient.eq_zero_iff_mem.1 (transvection_injective _ hmem)

variable (I) in
/-- Serre's relative elementary subgroup at level `I` contains the subgroup of `SL₂(A)` generated
by the transvections with parameter in `I`. -/
theorem closure_transvections_le_serreElementarySubgroup :
    Subgroup.closure {g | ∃ t : TransvectionStruct (Fin 2) A, t.c ∈ I ∧ t.toSpecialLinearGroup = g}
      ≤ I.serreElementarySubgroup := by
  rw [Subgroup.closure_le]
  rintro _ ⟨t, ht, rfl⟩
  exact t.toSpecialLinearGroup_mem_serreElementarySubgroup ht

/-- If the transvections generate `SL₂(A)`, then Serre's relative elementary subgroup at the unit
level is all of `SL₂(A)`. -/
theorem serreElementarySubgroup_top_of_closure_eq_top
    (h : Subgroup.closure (Set.range (TransvectionStruct.toSpecialLinearGroup :
      TransvectionStruct (Fin 2) A → SpecialLinearGroup (Fin 2) A)) = ⊤) :
    (⊤ : Ideal A).serreElementarySubgroup = ⊤ := by
  refine eq_top_iff.2 (le_trans ?_ (closure_transvections_le_serreElementarySubgroup ⊤))
  rw [← h]
  exact Subgroup.closure_mono fun _ ⟨t, ht⟩ ↦ ⟨t, Submodule.mem_top, ht⟩

/-- Over a field, Serre's relative elementary subgroup at the unit level is all of `SL₂`. -/
@[simp]
theorem serreElementarySubgroup_top_of_field (K : Type*) [Field K] :
    (⊤ : Ideal K).serreElementarySubgroup = ⊤ :=
  serreElementarySubgroup_top_of_closure_eq_top closure_range_toSpecialLinearGroup_eq_top_of_field

/-- Over `ℤ`, Serre's relative elementary subgroup at the unit level is all of `SL₂(ℤ)`. -/
@[simp]
theorem serreElementarySubgroup_top_int :
    (⊤ : Ideal ℤ).serreElementarySubgroup = ⊤ :=
  serreElementarySubgroup_top_of_closure_eq_top closure_range_toSpecialLinearGroup_eq_top

end Ideal

namespace Subgroup

variable {A : Type*} [CommRing A] [CharZero A]

/-- **Serre's levels of finite-index subgroups.** In characteristic zero, every finite-index
subgroup of `SL₂(A)` contains Serre's relative elementary subgroup `Eˢ(A, I)` for some nonzero
ideal `I`. No assumption on the units of `A` is needed. -/
theorem exists_serreElementarySubgroup_le (H : Subgroup (SpecialLinearGroup (Fin 2) A))
    [H.FiniteIndex] : ∃ I : Ideal A, I ≠ ⊥ ∧ I.serreElementarySubgroup ≤ H := by
  obtain ⟨m, hm, hH⟩ := H.exists_normalClosure_transvection_span_le zero_ne_one
  exact ⟨_, by simpa [Ideal.span_singleton_eq_bot] using hm, hH⟩

end Subgroup
