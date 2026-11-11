/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.Roots
public import TauCeti.LinearAlgebra.Matrix.OrderedSignCover.Reindex
public import TauCeti.LinearAlgebra.RootSystem.DiagramPermutations
import TauCeti.GroupTheory.Perm.Basic
public import TauCeti.GroupTheory.Perm.Cycle.Coeff
-- The finite certificates evaluate the existing private coordinate table and numbered permutation.
import all TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.E6.Basic
import all TauCeti.LinearAlgebra.RootSystem.DiagramPermutations

/-!
# Signed root orbits of the E₆ diagram reversal

The existing seventy-two Bourbaki-numbered coroots enumerate the entire norm-two shell of
`CartanMatrix.E 6`, in simple-root coordinates. The numbered diagram reversal acts on this
list by `TauCeti.E6Shell.reversal`. Its forty-eight orbits have explicit representatives:
twenty-four singleton orbits and twenty-four pairs. The first twenty-four representatives
are positive roots and the remaining ones are their negatives.

The ordered-cover lift is not the unsigned root permutation. `rootSign` records every
inversion sign: fourteen pairs have sign minus one at both ends. Every singleton has sign
one, so all root cycles have positive monodromy. These certificates supply the root indices
and signs for constructing invariant root vectors, without identifying the resulting fixed
integral lattice with a normalized folded Chevalley lattice.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, Plate V.
* V. G. Kac, *Infinite dimensional Lie algebras*, third edition, §§7.8–7.9.

The root coordinates are reused from `TauCeti.DynkinType.e6Coroot`; no second root table is
introduced. The sign convention is `Matrix.inversionSign`, not a choice of signs on orbits.
-/

public section

open Matrix
open TauCeti.DynkinType

namespace TauCeti.E6Shell

/-- Every listed E₆ coroot has norm two in simple-root coordinates. -/
theorem coroot_mem_normTwoShell (i : Fin 72) :
    e6Coroot i ∈ (CartanMatrix.E 6).normTwoShell := by
  rw [mem_normTwoShell, ← e6Root_eq_mulVec, dotProduct_comm]
  exact e6Root_dotProduct_e6Coroot_self i

/-- The existing pinned E₆ table enumerates the whole norm-two shell, not just a subset. -/
theorem mem_normTwoShell_iff {a : Fin 6 → ℤ} :
    a ∈ (CartanMatrix.E 6).normTwoShell ↔ ∃ i, e6Coroot i = a := by
  refine ⟨fun ha ↦ ?_, by rintro ⟨i, rfl⟩; exact coroot_mem_normTwoShell i⟩
  let x : E6.rootLattice isSimplyLaced_E6 :=
    ⟨fun j ↦ (a j : ℚ), (E6.mem_rootLattice_carrier_iff _ _).mpr fun j ↦ ⟨a j, rfl⟩⟩
  have hx : (E6.rootLattice isSimplyLaced_E6).norm x = 2 := by
    rw [Matrix.mem_normTwoShell] at ha
    have hn := E6.norm_rootLattice_intCast isSimplyLaced_E6 a
    have ha' : a ᵥ* CartanMatrix.E 6 ⬝ᵥ a = 2 := by
      rwa [dotProduct_mulVec] at ha
    simp only [cartanMatrix_E6] at hn
    exact hn.trans (by exact_mod_cast ha')
  obtain ⟨i, hi⟩ := (E6.norm_rootLattice_eq_two_iff isSimplyLaced_E6 valid_E6 x).mp hx
  refine ⟨i, funext fun j ↦ ?_⟩
  -- The generic coordinate lemma expects Fin E6.rank. The explicit type guides elaboration
  -- from our Fin 6 index, since E6.rank reduces to 6.
  have hj := (E6.coe_rootLatticeRoot_apply isSimplyLaced_E6 valid_E6 i
    (show Fin E6.rank from j)).symm.trans
      (congrArg (fun y : E6.rootLattice isSimplyLaced_E6 ↦ y.val j) hi)
  rw [simplyConnectedRootDatum_E6] at hj
  dsimp only [e6SimplyConnectedRootDatum, x] at hj
  exact_mod_cast hj

/-- The pinned root indices as the norm-two shell of the E₆ Gram matrix. -/
noncomputable def rootEquiv : Fin 72 ≃ (CartanMatrix.E 6).normTwoShell :=
  Equiv.ofBijective (fun i ↦ ⟨e6Coroot i, coroot_mem_normTwoShell i⟩)
    ⟨fun _ _ h ↦ e6Coroot.injective (congrArg Subtype.val h), fun a ↦ by
      obtain ⟨i, hi⟩ := mem_normTwoShell_iff.mp a.2
      exact ⟨i, Subtype.ext hi⟩⟩

@[simp]
theorem coe_rootEquiv (i : Fin 72) : (rootEquiv i : Fin 6 → ℤ) = e6Coroot i := (rfl)

private def reversalTable : Fin 72 → Fin 72 := ![
  5, 1, 4, 3, 2, 0, 10, 8, 7, 9, 6, 15, 12, 14, 13, 11, 19, 20,
  18, 16, 17, 24, 22, 23, 21, 27, 26, 25, 30, 29, 28, 32, 31, 33, 34, 35,
  41, 37, 40, 39, 38, 36, 46, 44, 43, 45, 42, 51, 48, 50, 49, 47, 55, 56,
  54, 52, 53, 60, 58, 59, 57, 63, 62, 61, 66, 65, 64, 68, 67, 69, 70, 71]

private theorem reversalTable_involutive : Function.Involutive reversalTable := by
  unfold Function.Involutive
  decide +kernel

/-- The numbered E₆ diagram reversal on the existing seventy-two root indices. -/
def reversal : Equiv.Perm (Fin 72) := Function.Involutive.toPerm _ reversalTable_involutive

/-- The root-index reversal is an involution. -/
theorem reversal_involutive : Function.Involutive reversal := reversalTable_involutive

/-- The root-index table is exactly the Bourbaki diagram reversal in simple-root coordinates. -/
theorem coroot_reversal (i : Fin 72) : e6Coroot (reversal i) = e6Coroot i ∘ graphPermE6.symm := by
  unfold e6Coroot
  decide +kernel +revert

/-- The E₆ Gram matrix is invariant under the numbered reversal, in reindex form. -/
theorem reversal_reindex : (CartanMatrix.E 6).reindex graphPermE6 graphPermE6 =
    CartanMatrix.E 6 := by
  ext i j
  simpa only [Matrix.reindex_apply, Matrix.submatrix_apply, graphPermE6_symm, cartanMatrix_E6] using
    cartanMatrix_E6_graphPermE6 i j

/-- Compatibility of the explicit enumeration with the intrinsic norm-shell permutation. -/
@[simp]
theorem rootEquiv_reversal (i : Fin 72) :
    rootEquiv (reversal i) =
      normTwoShellCongr reversal_reindex (rootEquiv i) := by
  apply Subtype.ext
  rw [coe_rootEquiv, coe_normTwoShellCongr_apply, coe_rootEquiv]
  exact coroot_reversal i

/-- The least numbered root in each reversal orbit, positives first and then their negatives. -/
def representative : Fin 48 ↪ Fin 72 where
  toFun := ![0, 1, 2, 3, 6, 7, 9, 11, 12, 13, 16, 17, 18, 21, 22, 23, 25, 26,
    28, 29, 31, 33, 34, 35, 36, 37, 38, 39, 42, 43, 45, 47, 48, 49, 52, 53,
    54, 57, 58, 59, 61, 62, 64, 65, 67, 69, 70, 71]
  inj' := by decide +kernel

/-- The orbit number of every root in the pinned table. -/
def orbitIndex : Fin 72 → Fin 48 := ![
  0, 1, 2, 3, 2, 0, 4, 5, 5, 6, 4, 7, 8, 9, 9, 7, 10, 11,
  12, 10, 11, 13, 14, 15, 13, 16, 17, 16, 18, 19, 18, 20, 20, 21, 22, 23,
  24, 25, 26, 27, 26, 24, 28, 29, 29, 30, 28, 31, 32, 33, 33, 31, 34, 35,
  36, 34, 35, 37, 38, 39, 37, 40, 41, 40, 42, 43, 42, 44, 44, 45, 46, 47]

@[simp]
theorem orbitIndex_representative (j : Fin 48) : orbitIndex (representative j) = j := by
  decide +kernel +revert

@[simp]
theorem orbitIndex_reversal (i : Fin 72) : orbitIndex (reversal i) = orbitIndex i := by
  decide +kernel +revert

/-- Each orbit consists precisely of its representative and its reversal, allowing coincidence. -/
theorem eq_representative_or_reversal (i : Fin 72) :
    i = representative (orbitIndex i) ∨ i = reversal (representative (orbitIndex i)) := by
  decide +kernel +revert

/-- The orbit table classifies the actual cycles of the root-index permutation. -/
theorem sameCycle_iff (i j : Fin 72) :
    reversal.SameCycle i j ↔ orbitIndex i = orbitIndex j := by
  rw [reversal_involutive.sameCycle_iff]
  constructor
  · rintro (rfl | rfl) <;> simp
  · intro h
    have hi := eq_representative_or_reversal i
    have hj := eq_representative_or_reversal j
    rw [h] at hi
    have hrev (a : Fin 72) : reversal (reversal a) = a := reversal_involutive a
    rcases hi with hi | hi <;> rcases hj with hj | hj <;> grind only

/-- Explicit orbit coordinates for the quotient by the reversal cycles. -/
def orbitEquiv : Quotient (Equiv.Perm.SameCycle.setoid reversal) ≃ Fin 48 where
  toFun := Quotient.lift orbitIndex fun i j h ↦ (sameCycle_iff i j).mp h
  invFun j := Quotient.mk _ (representative j)
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h i => exact Quotient.sound ((sameCycle_iff _ _).mpr (orbitIndex_representative _))
  right_inv := orbitIndex_representative

@[simp]
theorem orbitEquiv_mk (i : Fin 72) : orbitEquiv (Quotient.mk _ i) = orbitIndex i := (rfl)

@[simp]
theorem orbitEquiv_symm_apply (j : Fin 48) :
    orbitEquiv.symm j = Quotient.mk _ (representative j) := (rfl)

/-- The root reversal has exactly forty-eight cycles. -/
theorem card_rootOrbits : Nat.card (Quotient (Equiv.Perm.SameCycle.setoid reversal)) = 48 := by
  rw [Nat.card_congr orbitEquiv, Nat.card_eq_fintype_card, Fintype.card_fin]

/-- The first half of the orbit representatives is positive in the pinned enumeration. -/
theorem representative_lt_36_iff (j : Fin 48) : (representative j).val < 36 ↔ j.val < 24 := by
  decide +kernel +revert

/-- There are twenty-four singleton root orbits. -/
theorem card_singletonOrbits :
    Fintype.card {j : Fin 48 // reversal (representative j) = representative j} = 24 := by
  decide +kernel

/-- There are twenty-four two-element root orbits. -/
theorem card_pairOrbits :
    Fintype.card {j : Fin 48 // reversal (representative j) ≠ representative j} = 24 := by
  decide +kernel

/-- The positive half of the pinned table is exactly the nonnegative part of the shell. -/
theorem coroot_nonneg_iff (i : Fin 72) : (∀ j, 0 ≤ e6Coroot i j) ↔ i.val < 36 := by
  unfold e6Coroot
  decide +kernel +revert

/-- The inversion sign on the pinned E₆ root table. -/
def rootSign (i : Fin 72) : ℤˣ :=
  if i ∈ ({6, 7, 8, 10, 13, 14, 16, 19, 21, 24, 25, 27, 31, 32,
    42, 43, 44, 46, 49, 50, 52, 55, 57, 60, 61, 63, 67, 68} : Finset (Fin 72)) then -1 else 1

/-- Evaluate the lift sign from membership in the explicit negative-root-index table. -/
theorem rootSign_def (i : Fin 72) :
    rootSign i =
      if i ∈ ({6, 7, 8, 10, 13, 14, 16, 19, 21, 24, 25, 27, 31, 32,
        42, 43, 44, 46, 49, 50, 52, 55, 57, 60, 61, 63, 67, 68} : Finset (Fin 72))
      then -1 else 1 := (rfl)

/-- The recorded signs are the signs of the pinned ordered-cover lift. -/
theorem inversionSign_coroot (i : Fin 72) :
    inversionSign (CartanMatrix.E 6) graphPermE6 (e6Coroot i) = rootSign i := by
  rw [inversionSign_def, inversionForm_apply]
  unfold e6Coroot
  decide +kernel +revert

@[simp]
theorem rootSign_reversal (i : Fin 72) : rootSign (reversal i) = rootSign i := by
  decide +kernel +revert

/-- Every fixed root has positive lift sign; no singleton is a negative cycle. -/
theorem rootSign_eq_one_of_fixed {i : Fin 72} (hi : reversal i = i) : rootSign i = 1 := by
  revert i
  decide +kernel

/-- Every root cycle has positive monodromy for the pinned ordered-cover lift. -/
theorem monodromy_eq_one (i : Fin 72) :
    reversal.monodromy
      (fun i ↦ inversionSign (CartanMatrix.E 6) graphPermE6 (e6Coroot i)) i = 1 := by
  let : DecidableRel reversal.SameCycle := fun i j ↦
    decidable_of_iff (orbitIndex i = orbitIndex j) (sameCycle_iff i j).symm
  simp only [inversionSign_coroot]
  rw [Equiv.Perm.monodromy_eq_prod]
  simp only [sameCycle_iff]
  decide +kernel +revert

end TauCeti.E6Shell
