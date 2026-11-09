/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.NormTwoShell.TypeD
public import TauCeti.LinearAlgebra.Matrix.OrderedSignCover.Reindex
public import TauCeti.LinearAlgebra.RootSystem.DiagramPermutations

/-!
# Numbered signed root orbits of D₄ triality

The twelve positive roots are listed in Bourbaki simple-root coordinates, with the central
vertex at index `1`. Together with their negatives they enumerate the entire norm-two shell.
The numbered triality `(0 2 3)` has six orbits on the positive roots.

`TauCeti.D4Triality.rootEquiv` proves completeness of the enumeration using
`TauCeti.typeDNormTwoShellEquiv`. `TauCeti.D4Triality.sameCycle_next_iff` identifies exactly
its root orbits. `TauCeti.D4Triality.minimalPeriod_representative` certifies their actual
lengths, and `TauCeti.D4Triality.prod_rootSign_orbit` computes monodromy over those lengths.
`TauCeti.D4Triality.inversionSign_root` computes the pinning signs from the
ordered sign cover, and `TauCeti.D4Triality.orbitCoeff_next` gives the coefficients of the
signed invariant root vectors. The two nonconstant sign patterns cannot be omitted when
constructing the fixed Lie algebra. The finite coordinate, index, and sign tables are exposed
for exact certificate computation; the shell-enumerating equivalence remains abstract.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IV.
* V. G. Kac, *Infinite dimensional Lie algebras*, third edition, §7.9.
-/

public section

namespace TauCeti.D4Triality

open _root_.Matrix

/-- The positive roots of D₄ in simple-root coordinates, grouped into triality orbits. -/
@[expose] def positiveRoot : Fin 12 → Fin 4 → ℤ :=
  ![![1, 0, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1], ![0, 1, 0, 0],
    ![1, 1, 0, 0], ![0, 1, 1, 0], ![0, 1, 0, 1],
    ![1, 1, 1, 0], ![0, 1, 1, 1], ![1, 1, 0, 1],
    ![1, 1, 1, 1], ![1, 2, 1, 1]]

/-- `false` selects a positive root and `true` its negative. -/
def root (negative : Bool) (i : Fin 12) : (CartanMatrix.D 4).normTwoShell :=
  ⟨if negative then -positiveRoot i else positiveRoot i, by
    rw [mem_normTwoShell]
    cases negative <;> fin_cases i <;> decide⟩

theorem coe_root (negative : Bool) (i : Fin 12) :
    (root negative i : Fin 4 → ℤ) = if negative then -positiveRoot i else positiveRoot i :=
  (rfl)

private theorem root_bijective : Function.Bijective (Function.uncurry root) := by
  let e := (DynkinType.typeDRootEquiv 4 (by decide)).trans
    (typeDNormTwoShellEquiv (by decide))
  have : Finite (CartanMatrix.D 4).normTwoShell := Finite.of_equiv _ e
  apply (Nat.bijective_iff_injective_and_card _).mpr
  constructor
  · intro a b h
    have h' := congrArg Subtype.val h
    revert h'
    rcases a with ⟨a, i⟩
    rcases b with ⟨b, j⟩
    cases a <;> cases b <;> fin_cases i <;> fin_cases j <;> decide
  · rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    decide

/-- The twenty-four explicitly listed signed roots enumerate the entire norm-two shell of D₄. -/
noncomputable def rootEquiv : (Bool × Fin 12) ≃ (CartanMatrix.D 4).normTwoShell :=
  Equiv.ofBijective (Function.uncurry root) root_bijective

@[simp]
theorem rootEquiv_apply (negative : Bool) (i : Fin 12) :
    rootEquiv (negative, i) = root negative i :=
  (rfl)

/-- D₄ has exactly twenty-four roots. -/
theorem natCard_roots : Nat.card (CartanMatrix.D 4).normTwoShell = 24 := by
  rw [← Nat.card_congr rootEquiv, Nat.card_eq_fintype_card]
  decide

/-- A vector occurs in the list exactly when it is a root with nonnegative simple-root
coordinates. -/
theorem mem_range_positiveRoot_iff (a : Fin 4 → ℤ) :
    a ∈ Set.range positiveRoot ↔ a ∈ (CartanMatrix.D 4).normTwoShell ∧ 0 ≤ a := by
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨(root false i).property, by fin_cases i <;> decide⟩
  · rintro ⟨ha, hpos⟩
    obtain ⟨⟨negative, i⟩, h⟩ := rootEquiv.surjective ⟨a, ha⟩
    have hval := congrArg Subtype.val h
    cases negative
    · exact ⟨i, hval⟩
    · have : ¬ 0 ≤ (root true i : Fin 4 → ℤ) := by fin_cases i <;> decide
      exact (this (hval ▸ hpos)).elim

/-- There are exactly twelve positive roots in the numbered simple-root coordinates. -/
theorem natCard_positiveRoots :
    Nat.card {a : Fin 4 → ℤ // a ∈ (CartanMatrix.D 4).normTwoShell ∧ 0 ≤ a} = 12 := by
  let f : Fin 12 → {a : Fin 4 → ℤ // a ∈ (CartanMatrix.D 4).normTwoShell ∧ 0 ≤ a} :=
    fun i ↦ ⟨positiveRoot i, (mem_range_positiveRoot_iff _).mp ⟨i, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j h
      have hval : positiveRoot i = positiveRoot j := congrArg Subtype.val h
      have hroot : rootEquiv (false, i) = rootEquiv (false, j) := by
        apply Subtype.ext
        simpa only [rootEquiv_apply, coe_root, Bool.false_eq_true, ↓reduceIte] using hval
      exact (Prod.mk.inj (rootEquiv.injective hroot)).2
    · intro a
      obtain ⟨i, hi⟩ := (mem_range_positiveRoot_iff a.1).mpr a.2
      exact ⟨i, Subtype.ext hi⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf)]
  exact Nat.card_fin 12

/-- The triality permutation of the twelve positive-root indices. -/
@[expose] def next : Equiv.Perm (Fin 12) where
  toFun := ![1, 2, 0, 3, 5, 6, 4, 8, 9, 7, 10, 11]
  invFun := ![2, 0, 1, 3, 6, 4, 5, 9, 7, 8, 10, 11]
  left_inv := by decide
  right_inv := by decide

/-- The order-three relation on the root table. -/
@[simp]
theorem next_pow_three : next ^ 3 = 1 := by decide

/-- Labels for the six distinct positive-root orbits. -/
@[expose] def orbit : Fin 12 → Fin 6 := ![0, 0, 0, 1, 2, 2, 2, 3, 3, 3, 4, 5]

/-- A fixed representative in each positive-root orbit. -/
@[expose] def representative : Fin 6 → Fin 12 := ![0, 3, 4, 7, 10, 11]

@[simp]
theorem orbit_representative (o : Fin 6) : orbit (representative o) = o := by decide +revert

/-- The positive-root orbits have lengths three, one, three, three, one, one. -/
@[expose] def orbitLength : Fin 6 → ℕ := ![3, 1, 3, 3, 1, 1]

/-- Every positive-root index occurs in exactly one of the six listed orbits. -/
theorem existsUnique_orbit (i : Fin 12) :
    ∃! o : Fin 6, ∃ k : Fin (orbitLength o), (next ^ k.val) (representative o) = i := by
  unfold ExistsUnique
  fin_cases i <;> decide +kernel

/-- Each stated orbit length is the actual minimal positive period. -/
theorem minimalPeriod_representative (o : Fin 6) :
    Function.minimalPeriod next (representative o) = orbitLength o := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  fin_cases o <;> first
    | exact Function.minimalPeriod_eq_one_iff_isFixedPt.mpr (by decide)
    | exact Function.minimalPeriod_eq_prime (p := 3) (by decide) (by decide)

/-- The labels distinguish exactly the triality orbits, not merely invariant subsets. -/
theorem sameCycle_next_iff (i j : Fin 12) : next.SameCycle i j ↔ orbit i = orbit j := by
  decide +revert

/-- The Cartan matrix is preserved by the numbered triality. -/
theorem reindex_cartanMatrix :
    (CartanMatrix.D 4).reindex trialityPermD4 trialityPermD4 = CartanMatrix.D 4 := by
  ext i j
  simpa only [Matrix.reindex_apply, Matrix.submatrix_apply, DynkinType.cartanMatrix_D,
    Equiv.apply_symm_apply] using
    (cartanMatrix_D4_trialityPermD4 (trialityPermD4.symm i) (trialityPermD4.symm j)).symm

/-- Triality on all twenty-four roots in the explicit enumeration. -/
@[simp]
theorem normTwoShellCongr_root (negative : Bool) (i : Fin 12) :
    normTwoShellCongr reindex_cartanMatrix (root negative i) = root negative (next i) := by
  apply Subtype.ext
  rw [coe_normTwoShellCongr_apply]
  ext j
  obtain ⟨j, rfl⟩ := trialityPermD4.surjective j
  simp only [Function.comp_apply, Equiv.symm_apply_apply]
  cases negative <;> fin_cases i <;> fin_cases j <;> simp [coe_root, positiveRoot, next]

/-- Signs of the pinned triality on the positive roots, also valid for their negatives. -/
@[expose] def rootSign : Fin 12 → ℤˣ := ![1, 1, 1, 1, -1, 1, -1, -1, -1, 1, 1, 1]

/-- The signs are computed from the ordered sign cover, rather than chosen to force invariance. -/
@[simp]
theorem inversionSign_root (negative : Bool) (i : Fin 12) :
    inversionSign (CartanMatrix.D 4) trialityPermD4 (root negative i) = rootSign i := by
  rw [coe_root, inversionSign_def, inversionForm_apply]
  cases negative <;> fin_cases i <;>
    norm_num [positiveRoot, rootSign, CartanMatrix.D, Fin.sum_univ_succ, Finset.sum_filter,
      Int.negOnePow_eq_one_iff, even_iff_two_dvd]

/-- Coefficients of the signed orbit vectors, normalized to one at the representatives. -/
@[expose] def orbitCoeff : Fin 12 → ℤ := ![1, 1, 1, 1, 1, -1, -1, 1, -1, 1, 1, 1]

@[simp]
theorem orbit_next (i : Fin 12) : orbit (next i) = orbit i := by decide +revert

@[simp]
theorem orbitCoeff_representative (o : Fin 6) : orbitCoeff (representative o) = 1 := by
  decide +revert

/-- The coefficient recurrence includes the actual pinning signs. -/
theorem orbitCoeff_next (i : Fin 12) :
    orbitCoeff (next i) = orbitCoeff i * (rootSign i : ℤ) := by decide +revert

/-- The product of the signs along three successive triality steps is one. -/
theorem rootSign_cycle (i : Fin 12) :
    rootSign i * rootSign (next i) * rootSign (next (next i)) = 1 := by decide +revert

/-- Monodromy along the actual orbit length is one, including singleton orbits. -/
theorem prod_rootSign_orbit (o : Fin 6) :
    ∏ k : Fin (orbitLength o), rootSign ((next ^ k.val) (representative o)) = 1 := by
  fin_cases o <;> decide +kernel

end TauCeti.D4Triality
