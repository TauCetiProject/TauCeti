/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.NormTwoShell.Reindex
public import TauCeti.LinearAlgebra.Matrix.NormTwoShell.TrialityD4

/-!
# Signed invariant root vectors of D₄ triality

`TauCeti.D4Triality.invariantRoot` gives the twelve signed invariant root vectors of the
pinned D₄ triality. Its six positive-root orbit vectors and six negative-root orbit vectors
are fixed and linearly independent over the integers. Their root coordinates are explicit,
and their Cartan coordinates vanish. `TauCeti.D4Triality.invariantRoot_eq` expands each vector
as a singleton or a signed three-term sum, without repeating fixed roots. They permit bracket
calculations in the fixed Lie algebra without choosing representatives of abstract orbit quotients.

The construction uses the complete numbered root enumeration of
`TauCeti.LinearAlgebra.Matrix.NormTwoShell.TrialityD4` and
`Matrix.ShellLieAlgebra.reindex` for the actual pinned action, not a separately assumed action.
In particular the height-two and height-three orbit vectors are signed sums. The negative
root vectors use the ordered section, not inverse lifts of the positive root vectors.

## References

* V. G. Kac, *Infinite dimensional Lie algebras*, third edition, §7.9.
-/

public section

namespace TauCeti.D4Triality

open _root_.Matrix

/-- The twelve signed invariant root vectors: six positive-root orbits and their negatives.
The coefficients at the selected representatives are all one. -/
noncomputable def invariantRoot (negative : Bool) (o : Fin 6) :
    ShellLieAlgebra (CartanMatrix.D 4) :=
  ∑ i : Fin 12 with orbit i = o,
    orbitCoeff i • ShellLieAlgebra.root (CartanMatrix.D 4) (root negative i)

/-- Each invariant root vector is a distinct signed orbit sum. Singleton orbits contribute
one section root vector, not three times that vector. -/
theorem invariantRoot_eq (negative : Bool) (o : Fin 6) :
    invariantRoot negative o =
      let i := representative o
      if orbitLength o = 1 then ShellLieAlgebra.root (CartanMatrix.D 4) (root negative i)
      else
        ShellLieAlgebra.root (CartanMatrix.D 4) (root negative i) +
          rootSign i • ShellLieAlgebra.root (CartanMatrix.D 4) (root negative (next i)) +
          (rootSign i * rootSign (next i)) •
            ShellLieAlgebra.root (CartanMatrix.D 4) (root negative (next (next i))) := by
  rw [invariantRoot, Finset.sum_filter]
  fin_cases o <;>
    norm_num [orbitLength, representative, orbit, orbitCoeff, rootSign,
      next, Fin.sum_univ_succ, Units.smul_def] <;> abel

/-- Each displayed signed orbit vector is fixed by the actual pinned triality. -/
@[simp]
theorem reindex_invariantRoot (negative : Bool) (o : Fin 6) :
    ShellLieAlgebra.reindex trialityPermD4 reindex_cartanMatrix (invariantRoot negative o) =
      invariantRoot negative o := by
  classical
  unfold invariantRoot
  rw [map_sum]
  simp only [map_zsmul, ShellLieAlgebra.reindex_root, inversionSign_root,
    normTwoShellCongr_root, Units.smul_def, smul_smul, ← orbitCoeff_next]
  simpa only [Finset.sum_filter] using Fintype.sum_equiv next (fun i ↦ if orbit i = o then
    orbitCoeff (next i) • ShellLieAlgebra.root (CartanMatrix.D 4) (root negative (next i)) else 0)
    (fun i ↦ if orbit i = o then
      orbitCoeff i • ShellLieAlgebra.root (CartanMatrix.D 4) (root negative i) else 0)
    (by intro i; simp)

/-- Root coordinates of the invariant vectors; in particular their supports are disjoint. -/
@[simp]
theorem basis_repr_invariantRoot (negative negative' : Bool) (o : Fin 6) (i : Fin 12) :
    (ShellLieAlgebra.basis (CartanMatrix.D 4)).repr (invariantRoot negative o)
        (.inr (root negative' i)) =
      if negative = negative' ∧ orbit i = o then orbitCoeff i else 0 := by
  classical
  have hinj (j : Fin 12) : root negative j = root negative' i ↔ negative = negative' ∧ j = i := by
    simpa only [rootEquiv_apply, Prod.mk.injEq] using
      (rootEquiv.injective.eq_iff (a := (negative, j)) (b := (negative', i)))
  simp only [invariantRoot, map_sum, map_smul,
    ← ShellLieAlgebra.basis_inr, Module.Basis.repr_self]
  simp only [Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finsupp.single_apply, Sum.inr.injEq, hinj]
  by_cases h : negative = negative' <;> simp [h]

/-- The invariant root vectors have no Cartan component. -/
@[simp]
theorem basis_repr_invariantRoot_inl (negative : Bool) (o : Fin 6) (i : Fin 4) :
    (ShellLieAlgebra.basis (CartanMatrix.D 4)).repr (invariantRoot negative o) (.inl i) = 0 := by
  simp [invariantRoot, ← ShellLieAlgebra.basis_inr]

/-- The twelve invariant root vectors are linearly independent over the integers. -/
theorem linearIndependent_invariantRoot :
    LinearIndependent ℤ (Function.uncurry invariantRoot) := by
  refine LinearIndependent.of_pairwise_dual_eq_zero_one _
    (fun p ↦ (Finsupp.lapply (.inr (root p.1 (representative p.2)))).comp
      (ShellLieAlgebra.basis (CartanMatrix.D 4)).repr.toLinearMap) ?_ ?_
  · intro p q hpq
    have h : ¬ (q.1 = p.1 ∧ p.2 = q.2) :=
      fun h ↦ hpq (Prod.ext h.1.symm h.2)
    simp [Function.uncurry_def, h]
  · intro p
    simp [Function.uncurry_def]

end TauCeti.D4Triality
