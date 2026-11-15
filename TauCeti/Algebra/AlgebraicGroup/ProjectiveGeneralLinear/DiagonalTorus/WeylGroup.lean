/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.ProjectiveGeneralLinear.DiagonalTorus.RootDatum
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.RootDatum.WeylGroup
public import TauCeti.LinearAlgebra.RootSystem.Weyl.ReflectionPerm

/-!
# The Weyl group of the projective diagonal root datum

The Weyl group of the adjoint type-A datum on the normalized diagonal torus of
`PGL_{r+1}` is the symmetric group on the `r + 1` coordinate lines. Its reflections
are transpositions, and a permutation `e` sends each basis character `ε_i - ε_r`
to `ε_{e(i)} - ε_{e(r)}`. Thus the action permutes all coordinate differences.
The last coordinate is normalized to zero, so a permutation moving it
does not merely permute the remaining `r` coordinates.

The comparison uses the existing coordinate-difference Weyl-group computation:
the full coordinate datum and the adjoint datum have the same reflection permutations,
and their Weyl actions on root indices are faithful. The character action is then determined by
the roots `ε_i - ε_r`, which form a basis of the adjoint character lattice.
These are integral root-datum statements, including rank zero. They do not identify
a normalizer quotient of rational points or a scheme-theoretic normalizer.

## References

* J. S. Milne, *Algebraic Groups* (2017), §21.
* J. E. Humphreys, *Linear Algebraic Groups* (1975), §§26–27.
* `TauCeti.Algebra.AlgebraicGroup.SplitTorus.RootDatum.WeylGroup`,
  for the symmetric-group identification for coordinate differences.
-/

public section

namespace TauCeti.ProjectiveGeneralLinear

open SplitTorus

universe u

noncomputable section

variable {r : ℕ}

private theorem diagonal_reflectionPerm_eq :
    (coordinateRootDatum (Fin (r + 1))).reflectionPerm =
      (diagonalRootDatum.{u} r).reflectionPerm := by
  funext p
  exact Equiv.ext fun q ↦ by
    rw [coordinateRootDatum_reflectionPerm, diagonalRootDatum_reflectionPerm]

private def coordinateWeylGroupEquiv :
    (coordinateRootDatum (Fin (r + 1))).weylGroup ≃*
      (diagonalRootDatum.{u} r).weylGroup :=
  RootPairing.weylGroupEquivOfReflectionPermEq _ _ diagonal_reflectionPerm_eq
    coordinateRootDatum_weylGroupToPerm_injective
    (RootPairing.weylGroupToPerm_injective_of_span_eq_top _
      (rootSpan_diagonalRootDatum_eq_top r))

/-- The Weyl group of the projective diagonal root datum is the symmetric group on
the `r + 1` coordinate lines. -/
def diagonalPermMulEquivWeylGroup (r : ℕ) :
    Equiv.Perm (Fin (r + 1)) ≃* (diagonalRootDatum.{u} r).weylGroup :=
  coordinatePermMulEquivWeylGroup.trans coordinateWeylGroupEquiv

/-- A coordinate permutation acts simultaneously on both indices of a root. -/
@[simp]
theorem diagonalPermMulEquivWeylGroup_indexEquiv_apply
    (e : Equiv.Perm (Fin (r + 1))) (p : CoordinateRootIndex (Fin (r + 1))) :
    (diagonalPermMulEquivWeylGroup.{u} r e).1.indexEquiv p =
      coordinatePermRootIndex e p := by
  have h : (coordinateWeylGroupEquiv
      (coordinatePermMulEquivWeylGroup e)).1.indexEquiv p =
      (coordinatePermMulEquivWeylGroup e).1.indexEquiv p :=
    congrArg (fun f : Equiv.Perm (CoordinateRootIndex (Fin (r + 1))) ↦ f p)
    (RootPairing.weylGroupToPerm_weylGroupEquivOfReflectionPermEq _ _
      diagonal_reflectionPerm_eq _ _ (coordinatePermMulEquivWeylGroup e))
  exact h.trans (coordinatePermMulEquivWeylGroup_indexEquiv_apply e p)

/-- A transposition is the reflection in the corresponding projective root. -/
@[simp]
theorem diagonalPermMulEquivWeylGroup_swap (i j : Fin (r + 1)) (hij : i ≠ j) :
    diagonalPermMulEquivWeylGroup.{u} r (Equiv.swap i j) =
      RootPairing.weylGroup.ofIdx (diagonalRootDatum.{u} r) ⟨(i, j), hij⟩ := by
  rw [diagonalPermMulEquivWeylGroup, MulEquiv.trans_apply,
    coordinatePermMulEquivWeylGroup_swap i j hij]
  exact RootPairing.weylGroupEquivOfReflectionPermEq_ofIdx _ _ _ _ _ _

/-- The inverse Weyl-group equivalence sends a root reflection to its transposition. -/
@[simp]
theorem diagonalPermMulEquivWeylGroup_symm_ofIdx
    (p : CoordinateRootIndex (Fin (r + 1))) :
    (diagonalPermMulEquivWeylGroup.{u} r).symm
        (RootPairing.weylGroup.ofIdx (diagonalRootDatum.{u} r) p) =
      Equiv.swap p.1.1 p.1.2 := by
  apply (diagonalPermMulEquivWeylGroup r).injective
  rw [MulEquiv.apply_symm_apply, diagonalPermMulEquivWeylGroup_swap _ _ p.2]

/-- On a basis character `ε_i - ε_r`, a permutation gives `ε_{e(i)} - ε_{e(r)}`,
expressed in the normalized projective coordinates. -/
@[simp]
theorem diagonalPermMulEquivWeylGroup_smul_single
    (e : Equiv.Perm (Fin (r + 1))) (i : ULift.{u} (Fin r)) :
    diagonalPermMulEquivWeylGroup.{u} r e • Finsupp.single i 1 =
      (diagonalRootDatum.{u} r).root
        (coordinatePermRootIndex e
          ⟨(i.down.castSucc, Fin.last r), (Fin.castSucc_lt_last i.down).ne⟩) := by
  rw [← diagonalRootDatum_root_castSucc_last]
  simpa only [RootPairing.weylGroupToPerm_apply,
    diagonalPermMulEquivWeylGroup_indexEquiv_apply] using
    (diagonalRootDatum.{u} r).weylGroup_apply_root (diagonalPermMulEquivWeylGroup r e)
      ⟨(i.down.castSucc, Fin.last r), (Fin.castSucc_lt_last i.down).ne⟩

/-- The Weyl action on an arbitrary character in normalized projective coordinates.
The subtracted term accounts for moving the distinguished last coordinate. -/
@[simp↓]
theorem diagonalPermMulEquivWeylGroup_smul_apply
    (e : Equiv.Perm (Fin (r + 1))) (x : ULift.{u} (Fin r) →₀ ℤ)
    (i : ULift.{u} (Fin r)) :
    (diagonalPermMulEquivWeylGroup.{u} r e • x) i =
      x.sum (fun j c ↦ c *
        ((if e j.down.castSucc = i.down.castSucc then 1 else 0) -
          (if e (Fin.last r) = i.down.castSucc then 1 else 0))) := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [smul_add, hx, hy, Finsupp.sum_add_index, add_mul]
  | single j c =>
      have hsingle : Finsupp.single j c = c • Finsupp.single j (1 : ℤ) := by simp
      rw [hsingle, smul_comm, diagonalPermMulEquivWeylGroup_smul_single]
      simp [diagonalRootDatum_root_apply, diagonalTorusWeight_apply,
        coordinatePermRootIndex_coe]

/-- The projective diagonal Weyl group has order `(r + 1)!`, including rank zero. -/
theorem card_weylGroup_diagonalRootDatum (r : ℕ) :
    Nat.card (diagonalRootDatum.{u} r).weylGroup = Nat.factorial (r + 1) := by
  rw [Nat.card_congr (diagonalPermMulEquivWeylGroup.{u} r).symm.toEquiv,
    Nat.card_perm, Nat.card_fin]

end

end TauCeti.ProjectiveGeneralLinear
