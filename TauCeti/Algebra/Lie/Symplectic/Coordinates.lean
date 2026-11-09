/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Symplectic.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Lie
public import Mathlib.Data.Sym.Sym2

/-!
# Matrix root coordinates for the symplectic Lie algebra

A symplectic Lie matrix has the form `[[A, B], [C, -Aᵀ]]`, where `B` and `C` are symmetric.
Its independent entries are therefore indexed by ordered pairs for `A` and unordered pairs
for each of `B` and `C`. `rootEntryEquiv` gives these coordinates and `rootEntryBasis` their
basis. The diagonal entries of `A` are the coordinate Cartan vectors; the remaining vectors
are the difference roots and the positive and negative sum roots, including the long roots.
A repeated unordered pair contributes one matrix entry, not twice that entry.

These coordinates give an integral matrix basis for symplectic realizations of folded Lie
algebras. They work over every commutative ring, including characteristic two, and do not
assert that distinct integral roots remain distinct as Lie algebra weights in that characteristic.

The construction uses `Sym2.lift` for symmetric entries and `Module.Basis.ofEquivFun` for the
basis, together with `Matrix.mem_symplecticLieAlgebra_iff` for the block equations.
`TauCeti.GLSymplecticFin.RootSubgroupIndex.val_rootEntryBasis_rootEntryIndex` identifies all
root vectors with the existing normalized root-subgroup tangent matrices.

## References

* V. G. Kac, *Infinite dimensional Lie algebras*, third edition, §7.9.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate III.
-/

public section

open Matrix LieAlgebra.Symplectic

namespace TauCeti.LieAlgebra.Symplectic

variable (l : Type*) [Fintype l] [DecidableEq l] (R : Type*) [CommRing R]

/-- Independent matrix-entry labels for the symplectic Lie algebra: the first block and the
unordered pairs of each symmetric off-diagonal block. -/
abbrev RootEntryIndex := (l × l) ⊕ (Sym2 l ⊕ Sym2 l)

/-- Independent entries identify the symplectic Lie algebra with its coordinate module.
The inverse fills the last block with the negative transpose of the first. -/
-- On explicit sum constructors and unordered pairs, entry evaluation through `fromBlocks`,
-- `Matrix.of` and `Sym2.lift` is definitional. The `rfl` proofs below use these reductions,
-- including pointwise addition and scalar multiplication in the Lie subalgebra.
def rootEntryEquiv : sp l R ≃ₗ[R] (RootEntryIndex l → R) where
  toFun X := Sum.elim (fun p ↦ X.val (.inl p.1) (.inl p.2))
    (Sum.elim
      (Sym2.lift ⟨fun i j ↦ X.val (.inl i) (.inr j),
        (mem_symplecticLieAlgebra_iff X.val).mp X.property |>.1⟩)
      (Sym2.lift ⟨fun i j ↦ X.val (.inr i) (.inl j),
        (mem_symplecticLieAlgebra_iff X.val).mp X.property |>.2.1⟩))
  invFun c := ⟨fromBlocks (Matrix.of fun i j ↦ c (.inl (i, j)))
    (Matrix.of fun i j ↦ c (.inr (.inl s(i, j))))
    (Matrix.of fun i j ↦ c (.inr (.inr s(i, j))))
    (Matrix.of fun i j ↦ -c (.inl (j, i))), by
      rw [mem_symplecticLieAlgebra_iff]
      simp only [fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
        fromBlocks_apply₁₁]
      exact ⟨fun i j ↦ congrArg (fun p ↦ c (.inr (.inl p))) (Sym2.eq_swap),
        fun i j ↦ congrArg (fun p ↦ c (.inr (.inr p))) (Sym2.eq_swap), fun _ _ ↦ rfl⟩⟩
  left_inv X := by
    apply Subtype.ext
    ext (i | i) (j | j)
    · rfl
    · rfl
    · rfl
    · exact ((mem_symplecticLieAlgebra_iff X.val).mp X.property).2.2 i j |>.symm
  right_inv c := by
    funext p
    rcases p with ⟨i, j⟩ | (p | p)
    · rfl
    · induction p using Sym2.inductionOn with | _ i j => rfl
    · induction p using Sym2.inductionOn with | _ i j => rfl
  map_add' X Y := by
    funext p
    rcases p with ⟨i, j⟩ | (p | p)
    · rfl
    · induction p using Sym2.inductionOn with | _ i j => rfl
    · induction p using Sym2.inductionOn with | _ i j => rfl
  map_smul' a X := by
    funext p
    rcases p with ⟨i, j⟩ | (p | p)
    · rfl
    · induction p using Sym2.inductionOn with | _ i j => rfl
    · induction p using Sym2.inductionOn with | _ i j => rfl

/-- The first family of coordinates consists of the upper-left entries. -/
@[simp]
theorem rootEntryEquiv_apply_inl (X : sp l R) (i j : l) :
    rootEntryEquiv l R X (.inl (i, j)) = X.val (.inl i) (.inl j) :=
  (rfl)

/-- The second family consists of the symmetric upper-right entries. -/
@[simp]
theorem rootEntryEquiv_apply_inr_inl (X : sp l R) (i j : l) :
    rootEntryEquiv l R X (.inr (.inl s(i, j))) = X.val (.inl i) (.inr j) :=
  (rfl)

/-- The third family consists of the symmetric lower-left entries. -/
@[simp]
theorem rootEntryEquiv_apply_inr_inr (X : sp l R) (i j : l) :
    rootEntryEquiv l R X (.inr (.inr s(i, j))) = X.val (.inr i) (.inl j) :=
  (rfl)

/-- Reconstruction from independent entries in block form. -/
@[simp]
theorem val_rootEntryEquiv_symm (c : RootEntryIndex l → R) :
    ((rootEntryEquiv l R).symm c).val =
      fromBlocks (Matrix.of fun i j ↦ c (.inl (i, j)))
        (Matrix.of fun i j ↦ c (.inr (.inl s(i, j))))
        (Matrix.of fun i j ↦ c (.inr (.inr s(i, j))))
        (Matrix.of fun i j ↦ -c (.inl (j, i))) :=
  (rfl)

/-- The matrix root basis of the symplectic Lie algebra, with coordinate Cartan vectors in the
first family's diagonal. Repeated unordered pairs give long-root vectors with coefficient one. -/
noncomputable def rootEntryBasis : Module.Basis (RootEntryIndex l) R (sp l R) :=
  Module.Basis.ofEquivFun (rootEntryEquiv l R)

/-- The root basis reads exactly the independent matrix entries. -/
@[simp]
theorem rootEntryBasis_repr (X : sp l R) (p : RootEntryIndex l) :
    (rootEntryBasis l R).repr X p = rootEntryEquiv l R X p := by
  rw [rootEntryBasis, Module.Basis.ofEquivFun_repr_apply]

/-- The first family consists of a matrix unit in the upper-left block and its negative
transpose in the lower-right block. -/
@[simp]
theorem val_rootEntryBasis_inl (i j : l) :
    (rootEntryBasis l R (.inl (i, j))).val =
      single (.inl i) (.inl j) 1 - single (.inr j) (.inr i) 1 := by
  classical
  rw [rootEntryBasis, Module.Basis.coe_ofEquivFun, val_rootEntryEquiv_symm]
  ext (a | a) (b | b) <;>
    simp [Matrix.single_apply, Pi.single_apply, Prod.ext_iff, eq_comm, and_comm]

/-- An unordered pair gives a symmetric upper-right matrix unit. The diagonal has coefficient
one, so this formula also gives the long-root vector in characteristic two. -/
@[simp]
theorem val_rootEntryBasis_inr_inl (p : Sym2 l) :
    (rootEntryBasis l R (.inr (.inl p))).val =
      fromBlocks 0 (Matrix.of fun i j ↦ if s(i, j) = p then 1 else 0) 0 0 := by
  classical
  rw [rootEntryBasis, Module.Basis.coe_ofEquivFun, val_rootEntryEquiv_symm]
  ext (a | a) (b | b) <;> simp [Pi.single_apply, eq_comm]

/-- An unordered pair gives a symmetric lower-left matrix unit, again without doubling the
diagonal long-root vector. -/
@[simp]
theorem val_rootEntryBasis_inr_inr (p : Sym2 l) :
    (rootEntryBasis l R (.inr (.inr p))).val =
      fromBlocks 0 0 (Matrix.of fun i j ↦ if s(i, j) = p then 1 else 0) 0 := by
  classical
  rw [rootEntryBasis, Module.Basis.coe_ofEquivFun, val_rootEntryEquiv_symm]
  ext (a | a) (b | b) <;> simp [Pi.single_apply, eq_comm]

end TauCeti.LieAlgebra.Symplectic

namespace TauCeti.GLSymplecticFin.RootSubgroupIndex

open TauCeti.LieAlgebra.Symplectic

variable {m : ℕ}

/-- The independent-entry label of a standard symplectic root. The labels not reached here
are exactly the diagonal Cartan entries of the upper-left block. -/
def rootEntryIndex : RootSubgroupIndex m → RootEntryIndex (Fin m)
  | .positiveLong i => .inr (.inl s(i, i))
  | .negativeLong i => .inr (.inr s(i, i))
  | .difference i j _ => .inl (i, j)
  | .positiveSum i j _ => .inr (.inl s(i, j))
  | .negativeSum i j _ => .inr (.inr s(i, j))

/-- A positive long root uses a repeated upper-right pair. -/
@[simp]
theorem rootEntryIndex_positiveLong (i : Fin m) :
    (positiveLong i).rootEntryIndex = .inr (.inl s(i, i)) := (rfl)

/-- A negative long root uses a repeated lower-left pair. -/
@[simp]
theorem rootEntryIndex_negativeLong (i : Fin m) :
    (negativeLong i).rootEntryIndex = .inr (.inr s(i, i)) := (rfl)

/-- A difference root uses the corresponding ordered upper-left pair. -/
@[simp]
theorem rootEntryIndex_difference (i j : Fin m) (hij : i ≠ j) :
    (difference i j hij).rootEntryIndex = .inl (i, j) := (rfl)

/-- A positive sum root uses an unordered upper-right pair. -/
@[simp]
theorem rootEntryIndex_positiveSum (i j : Fin m) (hij : i < j) :
    (positiveSum i j hij).rootEntryIndex = .inr (.inl s(i, j)) := (rfl)

/-- A negative sum root uses an unordered lower-left pair. -/
@[simp]
theorem rootEntryIndex_negativeSum (i j : Fin m) (hij : i < j) :
    (negativeSum i j hij).rootEntryIndex = .inr (.inr s(i, j)) := (rfl)

/-- Distinct standard roots have distinct independent-entry labels. -/
theorem rootEntryIndex_injective : Function.Injective (rootEntryIndex (m := m)) := by
  intro root root' h
  cases root <;> cases root' <;> simp_all [rootEntryIndex] <;> omega

/-- The root labels are exactly the independent-entry labels other than the Cartan diagonal. -/
theorem range_rootEntryIndex :
    Set.range (rootEntryIndex (m := m)) = {p | ∀ i, p ≠ .inl (i, i)} := by
  ext p
  constructor
  · rintro ⟨root, rfl⟩ i
    cases root <;> grind [rootEntryIndex]
  · intro h
    rcases p with ⟨i, j⟩ | (p | p)
    · exact ⟨difference i j (by simpa [eq_comm] using h i), rfl⟩
    · induction p using Sym2.inductionOn with
      | _ i j =>
        rcases lt_trichotomy i j with hij | rfl | hji
        · exact ⟨positiveSum i j hij, rfl⟩
        · exact ⟨positiveLong i, rfl⟩
        · exact ⟨positiveSum j i hji, by simp [rootEntryIndex, Sym2.eq_swap]⟩
    · induction p using Sym2.inductionOn with
      | _ i j =>
        rcases lt_trichotomy i j with hij | rfl | hji
        · exact ⟨negativeSum i j hij, rfl⟩
        · exact ⟨negativeLong i, rfl⟩
        · exact ⟨negativeSum j i hji, by simp [rootEntryIndex, Sym2.eq_swap]⟩

/-- Every standard root-subgroup tangent vector is the corresponding matrix root basis vector,
with its original parameter normalization, including at the long roots. -/
theorem val_rootEntryBasis_rootEntryIndex (root : RootSubgroupIndex m) (R : Type*) [CommRing R] :
    (rootEntryBasis (Fin m) R root.rootEntryIndex).val = root.tangentMatrix (1 : R) := by
  cases root with
  | difference i j hij =>
      rw [rootEntryIndex, val_rootEntryBasis_inl, tangentMatrix_difference]
  | positiveLong i =>
      rw [rootEntryIndex, val_rootEntryBasis_inr_inl, tangentMatrix_positiveLong]
      ext (a | a) (b | b) <;> simp [Matrix.single_apply, eq_comm, and_comm]
  | negativeLong i =>
      rw [rootEntryIndex, val_rootEntryBasis_inr_inr, tangentMatrix_negativeLong]
      ext (a | a) (b | b) <;> simp [Matrix.single_apply, eq_comm, and_comm]
  | positiveSum i j hij =>
      rw [rootEntryIndex, val_rootEntryBasis_inr_inl, tangentMatrix_positiveSum]
      ext (a | a) (b | b) <;>
        simp only [fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
          fromBlocks_apply₂₂, Matrix.of_apply, Matrix.zero_apply, Matrix.add_apply,
          Matrix.single_apply, Sym2.eq_iff] <;> grind
  | negativeSum i j hij =>
      rw [rootEntryIndex, val_rootEntryBasis_inr_inr, tangentMatrix_negativeSum]
      ext (a | a) (b | b) <;>
        simp only [fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
          fromBlocks_apply₂₂, Matrix.of_apply, Matrix.zero_apply, Matrix.add_apply,
          Matrix.single_apply, Sym2.eq_iff] <;> grind

end TauCeti.GLSymplecticFin.RootSubgroupIndex
