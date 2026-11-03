/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.NormTwoShell.Reindex
public import TauCeti.LinearAlgebra.Matrix.NormTwoShell.TypeD
public import TauCeti.LinearAlgebra.RootSystem.DiagramPermutations

/-!
# Root and sign data for triality of the signed D₄ Lie algebra

The twelve positive roots are listed in Bourbaki simple-root coordinates, with the central
node at index `1`. Triality cycles the outer nodes `0 → 2 → 3 → 0`. The table is exhaustive:
every norm-two vector is exactly one listed positive root or its negative. It supplies explicit
root indices for finite bracket calculations without a choice of root representatives.

The pinned action on section root vectors is not the unsigned permutation of this table.
`TauCeti.D4Triality.reindex_root` records every sign, and
`TauCeti.D4Triality.reindex_orbitVector` verifies the resulting signed orbit sums. There are
three singleton and three length-three positive-root orbits, and the same negative-root orbits.
The product of the three successive signs is always one.

These are data for calculating the fixed Lie algebra, not an identification of that algebra
with a normalized Chevalley form of type G₂.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IV.
* V. G. Kac, *Infinite dimensional Lie algebras*, third edition, §§7.8–7.9.

The signed section and its pinned action are those of `Matrix.ShellLieAlgebra.reindex`.
-/

public section

namespace TauCeti.D4Triality

open _root_.Matrix

/-- The positive D₄ roots in simple-root coordinates, grouped into triality orbits. -/
def positiveRoot (i : Fin 12) : Fin 4 → ℤ :=
  ![![1, 0, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1],
    ![0, 1, 0, 0],
    ![1, 1, 0, 0], ![0, 1, 1, 0], ![0, 1, 0, 1],
    ![1, 1, 1, 0], ![0, 1, 1, 1], ![1, 1, 0, 1],
    ![1, 1, 1, 1], ![1, 2, 1, 1]] i

/-- The explicit positive-root table. -/
theorem positiveRoot_def : positiveRoot =
    ![![1, 0, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1],
      ![0, 1, 0, 0],
      ![1, 1, 0, 0], ![0, 1, 1, 0], ![0, 1, 0, 1],
      ![1, 1, 1, 0], ![0, 1, 1, 1], ![1, 1, 0, 1],
      ![1, 1, 1, 1], ![1, 2, 1, 1]] := (rfl)

/-- The signed list of all roots: `false` is positive and `true` is negative. -/
def rootCoordinates (s : Bool) (i : Fin 12) : Fin 4 → ℤ :=
  if s then -positiveRoot i else positiveRoot i

@[simp]
theorem rootCoordinates_false (i : Fin 12) : rootCoordinates false i = positiveRoot i := (rfl)

@[simp]
theorem rootCoordinates_true (i : Fin 12) : rootCoordinates true i = -positiveRoot i := (rfl)

/-- Each listed vector has norm two for the Bourbaki Cartan matrix. -/
theorem rootCoordinates_mem (s : Bool) (i : Fin 12) :
    rootCoordinates s i ∈ (CartanMatrix.D 4).normTwoShell := by
  cases s <;> fin_cases i <;>
    norm_num [rootCoordinates, positiveRoot, mem_normTwoShell, dotProduct,
      mulVec, CartanMatrix.D, Fin.sum_univ_succ]

/-- The explicit root indexed by a sign and a row of the positive-root table. -/
def root (s : Bool) (i : Fin 12) : (CartanMatrix.D 4).normTwoShell :=
  ⟨rootCoordinates s i, rootCoordinates_mem s i⟩

@[simp]
theorem coe_root (s : Bool) (i : Fin 12) :
    (root s i : Fin 4 → ℤ) = rootCoordinates s i := (rfl)

/-- The root table has no repetitions, including between the two signs. -/
theorem root_injective : Function.Injective (fun p : Bool × Fin 12 ↦ root p.1 p.2) := by
  have h : Function.Injective (fun p : Bool × Fin 12 ↦ rootCoordinates p.1 p.2) := by
    decide +kernel
  intro p q hpq
  exact h (congrArg Subtype.val hpq)

@[simp]
theorem root_eq_root {s t : Bool} {i k : Fin 12} :
    root s i = root t k ↔ s = t ∧ i = k := by
  constructor
  · intro h
    exact Prod.mk.inj (root_injective h)
  · rintro ⟨rfl, rfl⟩
    rfl

/-- The signed table enumerates the entire norm-two shell, not only a subset of roots. -/
theorem root_surjective : Function.Surjective (fun p : Bool × Fin 12 ↦ root p.1 p.2) := by
  classical
  let e := (DynkinType.typeDRootEquiv 4 (by decide)).trans
    (typeDNormTwoShellEquiv (by decide : 4 ≤ 4))
  let := Fintype.ofEquiv (Fin 24) e
  have hcard : Fintype.card (Bool × Fin 12) =
      Fintype.card (CartanMatrix.D 4).normTwoShell := by
    simpa using Fintype.card_congr e
  exact ((Fintype.bijective_iff_injective_and_card _).mpr ⟨root_injective, hcard⟩).surjective

/-- A root has precisely one sign and one index in the positive-root table. -/
theorem existsUnique_root (a : (CartanMatrix.D 4).normTwoShell) :
    ∃! p : Bool × Fin 12, root p.1 p.2 = a :=
  Function.Bijective.existsUnique ⟨root_injective, root_surjective⟩ a

/-- All coordinates in the positive half are nonnegative. -/
theorem positiveRoot_nonneg (i : Fin 12) (j : Fin 4) : 0 ≤ positiveRoot i j := by
  fin_cases i <;> fin_cases j <;> decide

/-- Triality on the positive-root indices; it preserves the sign of a root. -/
def rootPerm : Equiv.Perm (Fin 12) where
  toFun := (![1, 2, 0, 3, 5, 6, 4, 8, 9, 7, 10, 11] : Fin 12 → Fin 12)
  invFun := (![2, 0, 1, 3, 6, 4, 5, 9, 7, 8, 10, 11] : Fin 12 → Fin 12)
  left_inv := by decide
  right_inv := by decide

@[simp]
theorem rootPerm_apply (i : Fin 12) :
    rootPerm i = (![1, 2, 0, 3, 5, 6, 4, 8, 9, 7, 10, 11] : Fin 12 → Fin 12) i := (rfl)

@[simp]
theorem rootPerm_symm_apply (i : Fin 12) :
    rootPerm.symm i = (![2, 0, 1, 3, 6, 4, 5, 9, 7, 8, 10, 11] : Fin 12 → Fin 12) i := (rfl)

/-- The order-three relation on the root table. -/
@[simp]
theorem rootPerm_pow_three : rootPerm ^ 3 = 1 := by decide

/-- The invariant simple-root relabelling of the D₄ Cartan matrix. -/
theorem reindex_cartan : (CartanMatrix.D 4).reindex trialityPermD4 trialityPermD4 =
    CartanMatrix.D 4 := by
  ext i j
  simpa only [DynkinType.cartanMatrix_D, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.apply_symm_apply] using
    (cartanMatrix_D4_trialityPermD4 (trialityPermD4.symm i) (trialityPermD4.symm j)).symm

/-- The coefficient table respects the pinned, forward triality permutation of the nodes. -/
theorem rootCoordinates_comp (s : Bool) (i : Fin 12) :
    rootCoordinates s i ∘ trialityPermD4.symm = rootCoordinates s (rootPerm i) := by
  cases s <;> fin_cases i <;> ext j <;>
    obtain ⟨k, rfl⟩ := trialityPermD4.surjective j <;>
    simp only [Function.comp_apply, Equiv.symm_apply_apply] <;> fin_cases k <;>
    norm_num [rootCoordinates, positiveRoot, rootPerm]

/-- The explicit root table intertwines triality with the permutation of the norm-two shell. -/
@[simp]
theorem normTwoShellCongr_root (s : Bool) (i : Fin 12) :
    normTwoShellCongr reindex_cartan (root s i) = root s (rootPerm i) := by
  apply Subtype.ext
  exact (coe_normTwoShellCongr_apply reindex_cartan _).trans (rootCoordinates_comp s i)

/-- The pinned section signs on the positive-root table; the negative root has the same sign. -/
def rootSign (i : Fin 12) : ℤˣ :=
  ![1, 1, 1, 1, -1, 1, -1, -1, -1, 1, 1, 1] i

@[simp]
theorem rootSign_apply (i : Fin 12) :
    rootSign i = (![1, 1, 1, 1, -1, 1, -1, -1, -1, 1, 1, 1] : Fin 12 → ℤˣ) i := (rfl)

/-- Every inversion sign is computed against the actual ordered-section convention. -/
@[simp]
theorem inversionSign_positiveRoot (i : Fin 12) :
    inversionSign (CartanMatrix.D 4) trialityPermD4 (positiveRoot i) = rootSign i := by
  fin_cases i <;>
    norm_num [positiveRoot, rootSign,
      inversionSign_def, inversionForm_apply, Fin.sum_univ_succ, CartanMatrix.D] <;>
    norm_num [Int.negOnePow_eq_one_iff]; decide

/-- The six representatives of the positive-root orbits. -/
def orbitRepresentative : Fin 6 → Fin 12 := ![0, 3, 4, 7, 10, 11]

theorem orbitRepresentative_apply (j : Fin 6) :
    orbitRepresentative j = (![0, 3, 4, 7, 10, 11] : Fin 6 → Fin 12) j := (rfl)

/-- The positive-root orbits have lengths three, one, three, three, one, one. -/
def orbitLength : Fin 6 → ℕ := ![3, 1, 3, 3, 1, 1]

@[simp]
theorem orbitLength_apply (j : Fin 6) : orbitLength j = (![3, 1, 3, 3, 1, 1] : Fin 6 → ℕ) j :=
  (rfl)

/-- Every positive-root index occurs in exactly one of the six listed orbits. -/
theorem existsUnique_orbit (i : Fin 12) :
    ∃! j : Fin 6, ∃ k : Fin (orbitLength j), (rootPerm ^ k.val) (orbitRepresentative j) = i := by
  unfold ExistsUnique
  fin_cases i <;> decide +kernel

/-- Each stated orbit length is the actual minimal positive period. -/
theorem minimalPeriod_orbitRepresentative (j : Fin 6) :
    Function.minimalPeriod rootPerm (orbitRepresentative j) = orbitLength j := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  fin_cases j <;> first
    | exact Function.minimalPeriod_eq_one_iff_isFixedPt.mpr (by decide)
    | exact Function.minimalPeriod_eq_prime (p := 3) (by decide) (by decide)

/-- The monodromy of every listed orbit is one: the product uses the actual orbit length,
not a three-term sum that would repeat a singleton orbit. -/
theorem prod_rootSign_orbit (j : Fin 6) :
    ∏ k : Fin (orbitLength j), rootSign ((rootPerm ^ k.val) (orbitRepresentative j)) = 1 := by
  fin_cases j <;> decide +kernel

/-- The triality action on every signed section root vector, with all signs retained. -/
theorem reindex_root (s : Bool) (i : Fin 12) :
    ShellLieAlgebra.reindex trialityPermD4 reindex_cartan
        (ShellLieAlgebra.root (CartanMatrix.D 4) (root s i)) =
      rootSign i • ShellLieAlgebra.root (CartanMatrix.D 4) (root s (rootPerm i)) := by
  rw [ShellLieAlgebra.reindex_root, coe_root, normTwoShellCongr_root]
  cases s <;> simp only [rootCoordinates_false, rootCoordinates_true, inversionSign_neg,
    inversionSign_positiveRoot]

/-- The distinct signed orbit sum at the chosen representative. Singleton orbits contribute
one section root vector, not three times that vector. -/
noncomputable def orbitVector (s : Bool) (j : Fin 6) : ShellLieAlgebra (CartanMatrix.D 4) :=
  let i := orbitRepresentative j
  if orbitLength j = 1 then ShellLieAlgebra.root (CartanMatrix.D 4) (root s i)
  else
    ShellLieAlgebra.root (CartanMatrix.D 4) (root s i) +
      rootSign i • ShellLieAlgebra.root (CartanMatrix.D 4) (root s (rootPerm i)) +
      (rootSign i * rootSign (rootPerm i)) •
        ShellLieAlgebra.root (CartanMatrix.D 4) (root s (rootPerm (rootPerm i)))

/-- The distinct signed orbit sums are fixed by the pinned action. -/
@[simp]
theorem reindex_orbitVector (s : Bool) (j : Fin 6) :
    ShellLieAlgebra.reindex trialityPermD4 reindex_cartan (orbitVector s j) = orbitVector s j := by
  cases s <;> fin_cases j <;>
    norm_num [orbitVector, orbitLength, orbitRepresentative, map_add, Units.smul_def,
      rootPerm, rootSign] <;> abel

/-- The signed orbit vector as a singleton or a three-term distinct sum. -/
theorem orbitVector_def (s : Bool) (j : Fin 6) :
    orbitVector s j =
      let i := orbitRepresentative j
      if orbitLength j = 1 then ShellLieAlgebra.root (CartanMatrix.D 4) (root s i)
      else
        ShellLieAlgebra.root (CartanMatrix.D 4) (root s i) +
          rootSign i • ShellLieAlgebra.root (CartanMatrix.D 4) (root s (rootPerm i)) +
          (rootSign i * rootSign (rootPerm i)) •
            ShellLieAlgebra.root (CartanMatrix.D 4) (root s (rootPerm (rootPerm i))) := (rfl)

/-- Each orbit sum has coefficient one at its own representative and zero at the other eleven
representatives. These coordinates retain the distinction between positive and negative roots. -/
@[simp]
theorem repr_orbitVector (s t : Bool) (j k : Fin 6) :
    (ShellLieAlgebra.basis (CartanMatrix.D 4)).repr (orbitVector s j)
        (.inr (root t (orbitRepresentative k))) = if s = t ∧ j = k then 1 else 0 := by
  classical
  fin_cases j <;> fin_cases k <;>
    norm_num [orbitVector, orbitLength, orbitRepresentative, rootPerm, rootSign,
      ← ShellLieAlgebra.basis_inr, Units.smul_def, Finsupp.single_apply,
      eq_comm (a := t)]

/-- The twelve signed distinct-orbit sums are integrally linearly independent. -/
theorem linearIndependent_orbitVector :
    LinearIndependent ℤ (fun p : Bool × Fin 6 ↦ orbitVector p.1 p.2) := by
  let c : ShellLieAlgebra (CartanMatrix.D 4) →ₗ[ℤ] (Bool × Fin 6 → ℤ) :=
    LinearMap.pi fun p ↦ (ShellLieAlgebra.basis (CartanMatrix.D 4)).coord
      (.inr (root p.1 (orbitRepresentative p.2)))
  apply LinearIndependent.of_comp c
  convert (Pi.basisFun ℤ (Bool × Fin 6)).linearIndependent using 1
  ext p q
  simp only [c, Function.comp_apply, LinearMap.pi_apply, Module.Basis.coord_apply, repr_orbitVector,
    Pi.basisFun_apply, Pi.single_apply, Prod.ext_iff]
  simp only [eq_comm]

end TauCeti.D4Triality
