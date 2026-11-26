/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Killing
public import Mathlib.Algebra.Lie.Semisimple.Basic
import TauCeti.Algebra.Lie.Basic
import TauCeti.Algebra.Lie.Killing.Basic

/-!
# The compact and noncompact ideals

For a Lie algebra `L` over an ordered field, the *compact ideal* is the sum of the simple ideals
(atoms of the lattice of Lie ideals, as in Mathlib's `LieAlgebra.IsSemisimple`) on which the Killing
form of `L` is negative definite, and the *noncompact ideal* is the sum of the other simple ideals.
A semisimple Lie algebra is the direct sum of the two. In a finite-dimensional semisimple Lie
algebra, a simple ideal lies in the compact ideal exactly when it is a compact Lie algebra, that is,
its own Killing form is negative definite. An equivalence of Lie algebras carries the compact ideal
to the compact ideal and the noncompact ideal to the noncompact ideal; in particular both are stable
under every automorphism. When the Killing form is nondegenerate each is the Killing orthogonal
complement of the other.

## Main definitions

* `LieAlgebra.compactIdeal`, `LieAlgebra.noncompactIdeal`: the sum of the simple ideals on which
  the Killing form is, respectively is not, negative definite.

## Main results

* `LieAlgebra.le_compactIdeal_iff_of_isAtom`, `LieAlgebra.le_noncompactIdeal_iff_of_isAtom`: in a
  finite-dimensional semisimple Lie algebra, a simple ideal lies in the compact ideal exactly when
  its own Killing form is negative definite, and in the noncompact ideal otherwise.
* `LieAlgebra.isCompl_compactIdeal_noncompactIdeal`: a semisimple Lie algebra is the direct sum of
  its compact and noncompact ideals.
* `LieAlgebra.compactIdeal_eq_killingCompl`, `LieAlgebra.noncompactIdeal_eq_killingCompl`, with
  the membership tests `LieAlgebra.mem_compactIdeal_iff` and `LieAlgebra.mem_noncompactIdeal_iff`:
  for a finite-dimensional Lie algebra with nondegenerate Killing form, each ideal is the Killing
  orthogonal complement of the other.
* `LieEquiv.map_compactIdeal`, `LieEquiv.map_noncompactIdeal`: an equivalence of Lie algebras
  carries the compact and noncompact ideals to the compact and noncompact ideals.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Chapter VI, §2.
-/

public section

open LieModule

namespace LieAlgebra

variable (K L : Type*) [Field K] [LinearOrder K] [LieRing L] [LieAlgebra K L]

/-- The *compact ideal* of a Lie algebra over an ordered field: the sum of the simple ideals on
which the Killing form is negative definite. -/
noncomputable def compactIdeal : LieIdeal K L :=
  sSup {I | IsAtom I ∧ ∀ x ∈ I, x ≠ 0 → killingForm K L x x < 0}

/-- The *noncompact ideal* of a Lie algebra over an ordered field: the sum of the simple ideals on
which the Killing form is not negative definite. -/
noncomputable def noncompactIdeal : LieIdeal K L :=
  sSup {I | IsAtom I ∧ ¬ ∀ x ∈ I, x ≠ 0 → killingForm K L x x < 0}

/-- The compact ideal is the sum of the simple ideals with negative definite Killing form. The
definition is not exposed, so this is how it is unfolded. -/
theorem compactIdeal_def : compactIdeal K L =
    sSup {I | IsAtom I ∧ ∀ x ∈ I, x ≠ 0 → killingForm K L x x < 0} :=
  (rfl)

/-- The noncompact ideal is the sum of the other simple ideals. The definition is not exposed, so
this is how it is unfolded. -/
theorem noncompactIdeal_def : noncompactIdeal K L =
    sSup {I | IsAtom I ∧ ¬ ∀ x ∈ I, x ≠ 0 → killingForm K L x x < 0} :=
  (rfl)

variable {K L}

/-- A simple ideal with negative definite Killing form lies in the compact ideal. -/
theorem le_compactIdeal_of_isAtom {I : LieIdeal K L} (hI : IsAtom I)
    (h : ∀ x ∈ I, x ≠ 0 → killingForm K L x x < 0) : I ≤ compactIdeal K L :=
  compactIdeal_def K L ▸ le_sSup ⟨hI, h⟩

/-- A simple ideal whose Killing form is not negative definite lies in the noncompact ideal. -/
theorem le_noncompactIdeal_of_isAtom {I : LieIdeal K L} (hI : IsAtom I)
    (h : ¬ ∀ x ∈ I, x ≠ 0 → killingForm K L x x < 0) : I ≤ noncompactIdeal K L :=
  noncompactIdeal_def K L ▸ le_sSup ⟨hI, h⟩

/-- The compact ideal lies in `J` exactly when every simple ideal with negative definite Killing
form does. -/
theorem compactIdeal_le_iff {J : LieIdeal K L} :
    compactIdeal K L ≤ J ↔
      ∀ I : LieIdeal K L, IsAtom I → (∀ x ∈ I, x ≠ 0 → killingForm K L x x < 0) → I ≤ J := by
  simp only [compactIdeal_def, sSup_le_iff, Set.mem_ofPred_eq, and_imp]

/-- The noncompact ideal lies in `J` exactly when every simple ideal whose Killing form is not
negative definite does. -/
theorem noncompactIdeal_le_iff {J : LieIdeal K L} :
    noncompactIdeal K L ≤ J ↔
      ∀ I : LieIdeal K L, IsAtom I → (¬ ∀ x ∈ I, x ≠ 0 → killingForm K L x x < 0) → I ≤ J := by
  simp only [noncompactIdeal_def, sSup_le_iff, Set.mem_ofPred_eq, and_imp]

/-- A semisimple Lie algebra over an ordered field is the direct sum of its compact ideal and its
noncompact ideal. -/
theorem isCompl_compactIdeal_noncompactIdeal [IsSemisimple K L] :
    IsCompl (compactIdeal K L) (noncompactIdeal K L) := by
  have hind := (IsSemisimple.sSupIndep_isAtom (R := K) (L := L))
  refine ⟨?_, codisjoint_iff.mpr ?_⟩
  · have himage : ∀ Q : LieIdeal K L → Prop, sSup {I | IsAtom I ∧ Q I} =
        ⨆ J ∈ {J : {I : LieIdeal K L | IsAtom I} | Q J}, (J : LieIdeal K L) := fun Q ↦ by
      rw [← sSup_image]
      congr 1
      ext I
      simp [and_comm]
    rw [compactIdeal_def, noncompactIdeal_def, himage, himage]
    exact ((sSupIndep_iff _).mp hind).disjoint_biSup_biSup
      (Set.disjoint_left.mpr fun _ h₁ h₂ ↦ h₂ h₁)
  · rw [compactIdeal_def, noncompactIdeal_def, ← sSup_union, ← IsSemisimple.sSup_atoms_eq_top]
    congr 1
    ext I
    simp only [Set.mem_union, Set.mem_ofPred_eq, ← and_or_left, or_not, and_true]

/-- **A simple ideal lies in the compact ideal exactly when it is a compact Lie algebra**: in a
finite-dimensional semisimple Lie algebra, an atom `I` satisfies `I ≤ compactIdeal K L` exactly
when its own Killing form is negative definite. -/
theorem le_compactIdeal_iff_of_isAtom [FiniteDimensional K L] [IsSemisimple K L]
    {I : LieIdeal K L} (hI : IsAtom I) :
    I ≤ compactIdeal K L ↔ ∀ x : I, x ≠ 0 → killingForm K I x x < 0 := by
  rw [← LieIdeal.forall_killingForm_neg_iff]
  refine ⟨fun hle ↦ ?_, le_compactIdeal_of_isAtom hI⟩
  by_contra h
  exact hI.1 (eq_bot_iff.mpr ((isCompl_compactIdeal_noncompactIdeal (K := K) (L := L)).disjoint
    hle (le_noncompactIdeal_of_isAtom hI h)))

/-- **A simple ideal lies in the noncompact ideal exactly when it is not a compact Lie algebra**:
in a finite-dimensional semisimple Lie algebra, an atom `I` satisfies `I ≤ noncompactIdeal K L`
exactly when its own Killing form is not negative definite. -/
theorem le_noncompactIdeal_iff_of_isAtom [FiniteDimensional K L] [IsSemisimple K L]
    {I : LieIdeal K L} (hI : IsAtom I) :
    I ≤ noncompactIdeal K L ↔ ¬ ∀ x : I, x ≠ 0 → killingForm K I x x < 0 := by
  refine ⟨fun hle h ↦ hI.1 (eq_bot_iff.mpr ?_), fun h ↦ le_noncompactIdeal_of_isAtom hI
    (I.forall_killingForm_neg_iff.not.mpr h)⟩
  exact (isCompl_compactIdeal_noncompactIdeal (K := K) (L := L)).disjoint
    ((le_compactIdeal_iff_of_isAtom hI).mpr h) hle

section IsKilling

variable [FiniteDimensional K L] [IsKilling K L]

/-- When the Killing form is nondegenerate, the compact ideal is the Killing orthogonal complement
of the noncompact ideal. -/
theorem compactIdeal_eq_killingCompl :
    compactIdeal K L = (noncompactIdeal K L).killingCompl :=
  isCompl_compactIdeal_noncompactIdeal.symm.right_unique (noncompactIdeal K L).isCompl_killingCompl

/-- When the Killing form is nondegenerate, the noncompact ideal is the Killing orthogonal
complement of the compact ideal. -/
theorem noncompactIdeal_eq_killingCompl :
    noncompactIdeal K L = (compactIdeal K L).killingCompl :=
  isCompl_compactIdeal_noncompactIdeal.right_unique (compactIdeal K L).isCompl_killingCompl

/-- When the Killing form is nondegenerate, an element lies in the compact ideal exactly when it is
Killing orthogonal to the noncompact ideal. -/
theorem mem_compactIdeal_iff {x : L} :
    x ∈ compactIdeal K L ↔ ∀ y ∈ noncompactIdeal K L, killingForm K L y x = 0 := by
  rw [compactIdeal_eq_killingCompl, LieIdeal.mem_killingCompl]

/-- When the Killing form is nondegenerate, an element lies in the noncompact ideal exactly when it
is Killing orthogonal to the compact ideal. -/
theorem mem_noncompactIdeal_iff {x : L} :
    x ∈ noncompactIdeal K L ↔ ∀ y ∈ compactIdeal K L, killingForm K L y x = 0 := by
  rw [noncompactIdeal_eq_killingCompl, LieIdeal.mem_killingCompl]

end IsKilling

end LieAlgebra

namespace LieEquiv

open LieAlgebra

variable {K L L' : Type*} [Field K] [LinearOrder K] [LieRing L] [LieAlgebra K L] [LieRing L']
  [LieAlgebra K L']

omit [LinearOrder K] in
private theorem map_sSup_isAtom (e : L ≃ₗ⁅K⁆ L') {P : LieIdeal K L → Prop}
    {Q : LieIdeal K L' → Prop} (hPQ : ∀ I, Q (I.map e.toLieHom) ↔ P I) :
    (sSup {I | IsAtom I ∧ P I}).map e.toLieHom = sSup {J | IsAtom J ∧ Q J} := by
  rw [← LieIdeal.orderIsoMapComap_apply, map_sSup, OrderIso.image_eq_preimage_symm]
  congr 1
  ext J
  rw [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_ofPred_eq, OrderIso.isAtom_iff, ← hPQ,
    ← LieIdeal.orderIsoMapComap_apply, OrderIso.apply_symm_apply]

/-- An equivalence of Lie algebras carries the compact ideal to the compact ideal. -/
@[simp]
theorem map_compactIdeal (e : L ≃ₗ⁅K⁆ L') :
    (compactIdeal K L).map e.toLieHom = compactIdeal K L' := by
  rw [compactIdeal_def, compactIdeal_def]
  exact map_sSup_isAtom e (forall_killingForm_map_neg_iff e)

/-- An equivalence of Lie algebras carries the noncompact ideal to the noncompact ideal. -/
@[simp]
theorem map_noncompactIdeal (e : L ≃ₗ⁅K⁆ L') :
    (noncompactIdeal K L).map e.toLieHom = noncompactIdeal K L' := by
  rw [noncompactIdeal_def, noncompactIdeal_def]
  exact map_sSup_isAtom e fun I ↦ (forall_killingForm_map_neg_iff e I).not

end LieEquiv
