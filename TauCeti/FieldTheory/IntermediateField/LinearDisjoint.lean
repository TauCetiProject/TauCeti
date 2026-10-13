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

If `A` is algebraic over `k` and linearly disjoint from `B` over `k`, adjoining `A` preserves the
relative degree of an intermediate extension `B/C`. This is the field-tower calculation behind
the degree comparison for algebraic function fields after extending their constants, where `A`
is a constant field extension, finite or not, for instance an algebraic closure.

The proof shows that a family in `B` linearly independent over `C` stays linearly independent over
`A ⊔ C`. Every element of `A ⊔ C` is an `A`-linear combination of a `k`-basis `γ` of `C`, because
the compositum with an algebraic extension is the ring it generates; and for a `C`-basis `β` of
`B` the products `γ m * β i` form a `k`-basis of `B`, which linear disjointness keeps linearly
independent over `A`.

## Main results

* `IntermediateField.coe_sup_eq_span_of_isAlgebraic`: for `A` algebraic, `A ⊔ D` is the `A`-span
  of `D`.
* `IntermediateField.LinearDisjoint.linearIndependent_sup_of_isAlgebraic`: linear independence
  over `C ≤ B` persists over `A ⊔ C`.
* `IntermediateField.relrank_sup_sup_eq_relrank_of_linearDisjoint` and
  `IntermediateField.relfinrank_sup_sup_eq_relfinrank_of_linearDisjoint`:
  `[A ⊔ B : A ⊔ C] = [B : C]`. Apply them as
  `A.relfinrank_sup_sup_eq_relfinrank_of_linearDisjoint B C hCB h`, where `hCB : C ≤ B` and
  `h : A.LinearDisjoint B`; the algebraicity of `A` is supplied by an instance.

The declarations live in Mathlib's `IntermediateField` namespace so that this dot notation works.
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

/-- **The compositum with an algebraic extension is a span.** If `A` is algebraic over `k`, the
compositum `A ⊔ D` is the `A`-span of `D`: it is the ring `A[D]`, and `D` is closed under
multiplication. -/
theorem _root_.IntermediateField.coe_sup_eq_span_of_isAlgebraic (A D : IntermediateField k L)
    [Algebra.IsAlgebraic k A] :
    ((A ⊔ D : IntermediateField k L) : Set L) = Submodule.span A (D : Set L) := by
  have hclosure : (Submonoid.closure (D : Set L) : Set L) ⊆ Submodule.span A (D : Set L) :=
    fun _ hy ↦ Submodule.subset_span
      ((Submonoid.closure_le (S := D.toSubalgebra.toSubmonoid)).mpr subset_rfl hy)
  rw [← IntermediateField.adjoin_self k D, ← IntermediateField.restrictScalars_adjoin_eq_sup,
    IntermediateField.adjoin_self, IntermediateField.coe_restrictScalars,
    ← IntermediateField.coe_toSubalgebra,
    IntermediateField.adjoin_intermediateField_toSubalgebra_of_isAlgebraic_left,
    ← Subalgebra.coe_toSubmodule, Algebra.adjoin_eq_span_of_subset A hclosure]

/-- **Linear disjointness survives adjoining part of the other side.** Let `A` be algebraic over
`k` and linearly disjoint from `B`, and let `C ≤ B`. A family in `B` that is linearly
independent over `C` stays linearly independent over the compositum `A ⊔ C`. -/
theorem _root_.IntermediateField.LinearDisjoint.linearIndependent_sup_of_isAlgebraic
    {A B C : IntermediateField k L} [Algebra.IsAlgebraic k A] (h : A.LinearDisjoint B)
    (hCB : C ≤ B) {ι : Type*} {β : ι → L} (hβB : ∀ i, β i ∈ B) (hβ : LinearIndependent C β) :
    LinearIndependent (A ⊔ C : IntermediateField k L) β := by
  classical
  let γ := Module.Basis.ofVectorSpace k C
  let γ' : _ → L := fun m ↦ (γ m : L)
  -- the products `γ m * β i` are linearly independent over `k`, hence over `A`
  have hprod : LinearIndependent A fun p : ι × _ ↦ γ' p.2 * β p.1 := by
    have hk : LinearIndependent k fun p : _ × ι ↦ γ p.1 • β p.2 :=
      linearIndependent_smul γ.linearIndependent hβ
    have hkB : LinearIndependent k fun p : _ × ι ↦
        (⟨γ p.1 • β p.2, B.mul_mem (hCB (γ p.1).2) (hβB p.2)⟩ : B) :=
      .of_comp B.val.toLinearMap hk
    have hA := h.linearIndependent_right hkB
    exact (hA.comp (Equiv.prodComm _ _) (Equiv.injective _))
  -- every element of `A ⊔ C` is an `A`-combination of the `γ m`
  have hspan : ∀ x ∈ (A ⊔ C : IntermediateField k L),
      x ∈ Submodule.span A (Set.range γ') := by
    intro x hx
    have hC : (C : Set L) ⊆ Submodule.span A (Set.range γ') := by
      intro c hc
      have hck : c ∈ Submodule.span k (Set.range γ') := by
        have hmem := γ.mem_span (⟨c, hc⟩ : C)
        have := Submodule.mem_map_of_mem (f := C.val.toLinearMap) hmem
        rwa [Submodule.map_span, ← Set.range_comp] at this
      exact Submodule.span_le_restrictScalars k A _ hck
    rw [← SetLike.mem_coe, IntermediateField.coe_sup_eq_span_of_isAlgebraic] at hx
    exact Submodule.span_le.mpr hC hx
  rw [linearIndependent_iff']
  intro s g hg i hi
  choose c hc using fun j ↦ (Finsupp.mem_span_range_iff_exists_finsupp).mp (hspan _ (g j).2)
  let T := s.biUnion fun j ↦ (c j).support
  have hgT : ∀ j ∈ s, ((g j : L)) = ∑ m ∈ T, ((c j m : A) : L) * γ' m := fun j hj ↦ by
    rw [← hc j, Finsupp.sum_of_support_subset _
      (Finset.subset_biUnion_of_mem (fun j ↦ (c j).support) hj)]
    · simp only [Algebra.smul_def, IntermediateField.algebraMap_apply, T]
    · intro m _
      simp
  have hzero : ∑ p ∈ s ×ˢ T, c p.1 p.2 • (γ' p.2 * β p.1) = 0 := by
    rw [Finset.sum_product, ← hg]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [Algebra.smul_def, IntermediateField.algebraMap_apply, hgT j hj, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    rw [Algebra.smul_def, IntermediateField.algebraMap_apply, mul_assoc]
  have hc0 := (linearIndependent_iff'.mp hprod) (s ×ˢ T) (fun p ↦ c p.1 p.2) hzero
  refine Subtype.ext ?_
  rw [hgT i hi, ZeroMemClass.coe_zero]
  refine Finset.sum_eq_zero fun m hm ↦ ?_
  rw [hc0 (i, m) (Finset.mem_product.mpr ⟨hi, hm⟩), ZeroMemClass.coe_zero, zero_mul]

/-- **Base change by an algebraic linearly disjoint extension preserves relative degrees.** If `A`
is algebraic over `k` and linearly disjoint from `B`, then adjoining `A` does not change the
relative degree of an intermediate extension `B / C`: `[A ⊔ B : A ⊔ C] = [B : C]`, as cardinals. -/
theorem _root_.IntermediateField.relrank_sup_sup_eq_relrank_of_linearDisjoint
    (A B C : IntermediateField k L) (hCB : C ≤ B) [Algebra.IsAlgebraic k A]
    (h : A.LinearDisjoint B) :
    IntermediateField.relrank (A ⊔ C) (A ⊔ B) = IntermediateField.relrank C B := by
  have hle : A ⊔ C ≤ A ⊔ B := sup_le_sup_left hCB A
  let β₀ := Module.Basis.ofVectorSpace C (IntermediateField.extendScalars hCB)
  let β : _ → L := fun i ↦ (β₀ i : L)
  have hβB : ∀ i, β i ∈ B := fun i ↦ (β₀ i).2
  have hβ : LinearIndependent C β :=
    β₀.linearIndependent.map' (IntermediateField.extendScalars hCB).val.toLinearMap
      (LinearMap.ker_eq_bot.2 Subtype.val_injective)
  have hβ' := h.linearIndependent_sup_of_isAlgebraic hCB hβB hβ
  -- the span of `β` over `A ⊔ C` absorbs spans over smaller fields of sets it contains
  have hmono : ∀ S : IntermediateField k L, S ≤ A ⊔ C → ∀ t : Set L,
      t ⊆ Submodule.span (A ⊔ C : IntermediateField k L) (Set.range β) →
      ∀ x ∈ Submodule.span S t,
        x ∈ Submodule.span (A ⊔ C : IntermediateField k L) (Set.range β) := by
    intro S hS t ht x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact ht hx
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul a x _ hx => exact Submodule.smul_mem _ (⟨a, hS a.2⟩ : (A ⊔ C : IntermediateField k L)) hx
  -- `A ⊔ B` is spanned over `A ⊔ C` by the basis `β` of `B / C`
  have hspan : Subalgebra.toSubmodule (IntermediateField.extendScalars hle).toSubalgebra =
      Submodule.span (A ⊔ C : IntermediateField k L) (Set.range β) := by
    refine le_antisymm (fun x hx ↦ ?_) (Submodule.span_le.mpr ?_)
    · have hB : (B : Set L) ⊆ Submodule.span (A ⊔ C : IntermediateField k L) (Set.range β) := by
        intro b hb
        have hmem := β₀.mem_span (⟨b, hb⟩ : IntermediateField.extendScalars hCB)
        have := Submodule.mem_map_of_mem
          (f := (IntermediateField.extendScalars hCB).val.toLinearMap) hmem
        rw [Submodule.map_span, ← Set.range_comp] at this
        exact hmono C le_sup_right _ Submodule.subset_span b this
      have hAB : x ∈ Submodule.span A (B : Set L) := by
        rw [← SetLike.mem_coe, ← IntermediateField.coe_sup_eq_span_of_isAlgebraic]
        exact hx
      exact hmono A le_sup_left _ hB x hAB
    · rintro _ ⟨i, rfl⟩
      exact le_sup_right (a := A) (hβB i)
  rw [IntermediateField.relrank_eq_rank_of_le hle, IntermediateField.relrank_eq_rank_of_le hCB,
    ← IntermediateField.rank_eq_rank_subalgebra, ← Subalgebra.rank_toSubmodule, hspan,
    rank_span hβ', ← β₀.mk_eq_rank'', Cardinal.mk_range_eq _ hβ'.injective]

/-- Base change by an algebraic linearly disjoint extension preserves the degree of an intermediate
field extension. -/
theorem _root_.IntermediateField.relfinrank_sup_sup_eq_relfinrank_of_linearDisjoint
    (A B C : IntermediateField k L) (hCB : C ≤ B)
    [Algebra.IsAlgebraic k A] (h : A.LinearDisjoint B) :
    IntermediateField.relfinrank (A ⊔ C) (A ⊔ B) =
      IntermediateField.relfinrank C B :=
  congrArg Cardinal.toNat (A.relrank_sup_sup_eq_relrank_of_linearDisjoint B C hCB h)

end TauCeti
