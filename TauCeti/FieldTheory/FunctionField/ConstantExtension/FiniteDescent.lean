/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.ConstantExtension.Algebraic

/-!
# Finite descent in an algebraic constant extension

An arbitrary extension of constants is the directed union of the extensions obtained by adjoining
finitely many constants.  When the constant extension is algebraic, each of these intermediate
constant fields is finite-dimensional over the original constants.  Consequently every element,
finite set, or finitely generated intermediate field in the full compositum already occurs over a
finite constant subextension.

This is the finite-descent step used to pass results proved for finite constant extensions to an
algebraic closure of the constant field.  In the function-field setting, it lets finite algebraic
data be placed in a finite constant extension before applying degree, genus, and Riemann--Roch
comparison theorems.

## Main results

* `TauCeti.constantCompositum_eq_iSup_adjoin_finset`: a constant compositum is the supremum of
  the composita obtained from finitely generated constant subfields.
* `TauCeti.exists_finset_of_mem_constantCompositum`: one element of a constant compositum is
  defined over finitely many constants.
* `TauCeti.exists_finiteDimensional_constantSubfield_of_finset_subset_constantCompositum`: a
  finite set in an algebraic constant compositum is defined over one finite constant subextension.
* `TauCeti.exists_finiteDimensional_constantSubfield_of_fg_le_constantCompositum`: a finitely
  generated intermediate field in the compositum descends to one finite constant subextension.
* `TauCeti.exists_finiteDimensional_constantSubfield_of_finiteDimensional_le_constantCompositum`:
  a finite-dimensional intermediate field descends to one finite constant subextension.

## Reference

H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Section III.6.
-/

public section

open scoped IntermediateField

namespace TauCeti

universe u u' v v'

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F']

omit [Algebra k F] [Algebra k F'] [IsScalarTower k k' F'] [IsScalarTower k F F'] in
/-- Enlarging an intermediate field of constants enlarges its compositum with `F`. -/
theorem constantCompositum_mono {L M : IntermediateField k k'} (h : L ≤ M) :
    constantCompositum F L F' ≤ constantCompositum F M F' := by
  rw [constantCompositum_def, constantCompositum_def]
  apply IntermediateField.adjoin.mono
  rintro _ ⟨c, rfl⟩
  exact ⟨⟨c, h c.2⟩, rfl⟩

omit [Algebra k F] [Algebra k F'] [IsScalarTower k k' F'] [IsScalarTower k F F'] in
/-- **A constant compositum is the directed union of its finitely generated constant
subextensions.**  No algebraicity hypothesis is needed for this lattice identity. -/
theorem constantCompositum_eq_iSup_adjoin_finset :
    constantCompositum F k' F' =
      ⨆ S : Finset k', constantCompositum F (IntermediateField.adjoin k (S : Set k')) F' := by
  apply le_antisymm
  · rw [constantCompositum_def]
    refine IntermediateField.adjoin_le_iff.mpr ?_
    rintro _ ⟨c, rfl⟩
    apply (le_iSup (fun S : Finset k' ↦
      constantCompositum F (IntermediateField.adjoin k (S : Set k')) F') {c})
    rw [constantCompositum_def]
    let d : IntermediateField.adjoin k (({c} : Finset k') : Set k') :=
      ⟨c, IntermediateField.subset_adjoin k (({c} : Finset k') : Set k') (by simp)⟩
    apply IntermediateField.subset_adjoin F _
    refine ⟨d, ?_⟩
    rw [IsScalarTower.algebraMap_apply
      (IntermediateField.adjoin k (({c} : Finset k') : Set k')) k' F' d,
      IntermediateField.algebraMap_apply]
  · refine iSup_le fun S ↦ ?_
    rw [constantCompositum_def, constantCompositum_def]
    apply IntermediateField.adjoin.mono
    rintro _ ⟨c, rfl⟩
    exact ⟨c.1, by
      rw [IsScalarTower.algebraMap_apply
        (IntermediateField.adjoin k (S : Set k')) k' F' c,
        IntermediateField.algebraMap_apply]⟩

omit [Algebra k F] [Algebra k F'] [IsScalarTower k k' F'] [IsScalarTower k F F'] in
/-- **An element of a constant compositum uses only finitely many constants.**  If `x` belongs to
`F · k'`, there is a finite set `S ⊆ k'` such that `x` already belongs to `F · k(S)`. -/
theorem exists_finset_of_mem_constantCompositum {x : F'}
    (hx : x ∈ constantCompositum F k' F') :
    ∃ S : Finset k',
      x ∈ constantCompositum F (IntermediateField.adjoin k (S : Set k')) F' := by
  classical
  rw [constantCompositum_def] at hx
  obtain ⟨T, hT, hxT⟩ := IntermediateField.exists_finset_of_mem_adjoin hx
  let C : Set k' := algebraMap k' F' ⁻¹' (T : Set F')
  have hC : C.Finite :=
    Set.Finite.preimage (algebraMap k' F').injective.injOn T.finite_toSet
  let S : Finset k' := hC.toFinset
  refine ⟨S, mem_of_le_of_mem ?_ hxT⟩
  rw [IntermediateField.adjoin_le_iff]
  intro y hy
  obtain ⟨c, rfl⟩ := hT hy
  rw [constantCompositum_def]
  apply IntermediateField.subset_adjoin
  have hcC : c ∈ C := by
    simpa only [C, Set.mem_preimage] using hy
  have hcS : c ∈ S := by
    simpa only [S, Set.Finite.mem_toFinset] using hcC
  let d : IntermediateField.adjoin k (S : Set k') :=
    ⟨c, IntermediateField.subset_adjoin k (S : Set k') hcS⟩
  refine ⟨d, ?_⟩
  rw [IsScalarTower.algebraMap_apply
    (IntermediateField.adjoin k (S : Set k')) k' F' d,
    IntermediateField.algebraMap_apply]

omit [Algebra k F] [Algebra k F'] [IsScalarTower k k' F'] [IsScalarTower k F F'] in
/-- **One element in an algebraic constant compositum descends to a finite constant
subextension.** -/
theorem exists_finiteDimensional_constantSubfield_of_mem_constantCompositum
    [Algebra.IsAlgebraic k k'] {x : F'} (hx : x ∈ constantCompositum F k' F') :
    ∃ L : IntermediateField k k',
      FiniteDimensional k L ∧ x ∈ constantCompositum F L F' := by
  obtain ⟨S, hxS⟩ := exists_finset_of_mem_constantCompositum
    (k := k) (k' := k') (F := F) (F' := F') hx
  let L := IntermediateField.adjoin k (S : Set k')
  let _ : Finite (S : Set k') := Set.toFinite _
  let _ : FiniteDimensional k L :=
    IntermediateField.finiteDimensional_adjoin fun c _ ↦
      Algebra.IsIntegral.isIntegral c
  exact ⟨L, inferInstance, hxS⟩

omit [Algebra k F] [Algebra k F'] [IsScalarTower k k' F'] [IsScalarTower k F F'] in
/-- **A finite set in an algebraic constant compositum descends simultaneously to one finite
constant subextension.** -/
theorem exists_finiteDimensional_constantSubfield_of_finset_subset_constantCompositum
    [Algebra.IsAlgebraic k k'] (S : Finset F')
    (hS : ∀ x ∈ S, x ∈ constantCompositum F k' F') :
    ∃ L : IntermediateField k k', FiniteDimensional k L ∧
      ∀ x ∈ S, x ∈ constantCompositum F L F' := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      refine ⟨⊥, inferInstance, ?_⟩
      simp
  | @insert x S hx ih =>
      obtain ⟨L, hL, hxL⟩ :=
        exists_finiteDimensional_constantSubfield_of_mem_constantCompositum
          (k := k) (k' := k') (F := F) (F' := F') (hS x (by simp))
      obtain ⟨M, hM, hSM⟩ := ih fun y hy ↦ hS y (by simp [hy])
      let _ : FiniteDimensional k L := hL
      let _ : FiniteDimensional k M := hM
      let N := L ⊔ M
      let _ : FiniteDimensional k N := IntermediateField.finiteDimensional_sup L M
      refine ⟨N, inferInstance, fun y hy ↦ ?_⟩
      rw [Finset.mem_insert] at hy
      rcases hy with rfl | hy
      · exact constantCompositum_mono (F := F) (F' := F') le_sup_left hxL
      · exact constantCompositum_mono (F := F) (F' := F') le_sup_right (hSM y hy)

omit [Algebra k F] [Algebra k F'] [IsScalarTower k k' F'] [IsScalarTower k F F'] in
/-- **A finitely generated field inside an algebraic constant compositum descends to a finite
constant subextension.**  This packages simultaneous finite descent in the form used for finite
algebraic data: if `E / F` is generated by finitely many elements and `E ⊆ F · k'`, then some
finite-dimensional `L / k` satisfies `E ⊆ F · L`. -/
theorem exists_finiteDimensional_constantSubfield_of_fg_le_constantCompositum
    [Algebra.IsAlgebraic k k'] {E : IntermediateField F F'} (hE : E.FG)
    (hle : E ≤ constantCompositum F k' F') :
    ∃ L : IntermediateField k k',
      FiniteDimensional k L ∧ E ≤ constantCompositum F L F' := by
  obtain ⟨S, hS⟩ := hE
  have hScomp : ∀ x ∈ S, x ∈ constantCompositum F k' F' := by
    intro x hx
    apply hle
    rw [← hS]
    exact IntermediateField.subset_adjoin F (S : Set F') hx
  obtain ⟨L, hL, hSL⟩ :=
    exists_finiteDimensional_constantSubfield_of_finset_subset_constantCompositum
      (k := k) (k' := k') (F := F) (F' := F') S hScomp
  refine ⟨L, hL, ?_⟩
  rw [← hS, IntermediateField.adjoin_le_iff]
  exact hSL

omit [Algebra k F] [Algebra k F'] [IsScalarTower k k' F'] [IsScalarTower k F F'] in
/-- **A finite-dimensional field inside an algebraic constant compositum descends to a finite
constant subextension.**  This is the direct interface for finite algebraic data: if `E / F` is
finite-dimensional and `E ⊆ F · k'`, then some finite-dimensional `L / k` satisfies
`E ⊆ F · L`. -/
theorem
    exists_finiteDimensional_constantSubfield_of_finiteDimensional_le_constantCompositum
    [Algebra.IsAlgebraic k k'] {E : IntermediateField F F'} [FiniteDimensional F E]
    (hle : E ≤ constantCompositum F k' F') :
    ∃ L : IntermediateField k k',
      FiniteDimensional k L ∧ E ≤ constantCompositum F L F' := by
  apply exists_finiteDimensional_constantSubfield_of_fg_le_constantCompositum
    (k := k) (k' := k') (F := F) (F' := F')
  · exact E.fg_of_fg_toSubalgebra
      (Subalgebra.fg_of_fg_toSubmodule Submodule.FG.of_finite)
  · exact hle

end TauCeti
