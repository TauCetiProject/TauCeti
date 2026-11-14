/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.SimpleGraph.IntegralNullVector
public import TauCeti.Combinatorics.SimpleGraph.Finite
public import TauCeti.LinearAlgebra.RootSystem.AffineDynkinType.Basic

/-!
# Integral null vectors and affine marks

The native affine marks have coordinate gcd one, fixed by their value one at the affine node.
Because every mark is positive, `TauCeti.AffineDynkinType.natMarks` packages `t.marks` as an
`ℕ`-valued primitive additive function on `t.graph`. Under any actual isomorphism to a graphical
affine diagram, every natural-valued additive function is its coordinate gcd times the transported
marks. In particular, the unique positive primitive integral null vector is the transported native
marks. This comparison does not assume that a chosen vertex of the original graph has mark one.

See Kac, *Infinite dimensional Lie algebras*, 3rd edition, Chapter 4, for affine marks and
positive additive functions.

## Main definitions and results

* `TauCeti.AffineDynkinType.gcd_marks`: the integer marks have coordinate gcd `1`.
* `TauCeti.AffineDynkinType.natMarks`: the marks as an `ℕ`-valued vector `(t.marks ·).toNat`,
  with `coe_natMarks`, `natMarks_affineNode`, `gcd_natMarks`, and
  `sum_natMarks_neighborFinset_eq_two_mul`.
* `SimpleGraph.Iso.eq_gcd_smul_marks_comp`: every `ℕ`-valued null vector of `2I - A` on a graph
  isomorphic to a valid graphical affine diagram is its coordinate gcd times the transported marks.
-/

public section

open Finset

namespace TauCeti.AffineDynkinType

/-- The affine-node normalization makes the native marks primitive. -/
-- Apply before the concrete mark vectors are expanded.
@[simp↓]
theorem gcd_marks (t : AffineDynkinType) : univ.gcd t.marks = 1 := by
  rw [← Finset.normalize_gcd, normalize_eq_one, isUnit_iff_dvd_one]
  simpa using (univ.gcd_dvd (f := t.marks) (mem_univ t.affineNode))

/-- The native marks of an affine diagram viewed as `ℕ`-valued weights `(t.marks i).toNat`. -/
def natMarks (t : AffineDynkinType) (i : Fin t.nodes) : ℕ :=
  (t.marks i).toNat

/-- Evaluating `TauCeti.AffineDynkinType.natMarks` takes `Int.toNat` of `t.marks`. -/
theorem natMarks_apply (t : AffineDynkinType) (i : Fin t.nodes) :
    t.natMarks i = (t.marks i).toNat :=
  (rfl)

/-- Casting `TauCeti.AffineDynkinType.natMarks` back to `ℤ` recovers `t.marks`. -/
@[simp]
theorem coe_natMarks (t : AffineDynkinType) (i : Fin t.nodes) :
    (t.natMarks i : ℤ) = t.marks i :=
  Int.toNat_of_nonneg (t.marks_pos i).le

/-- Every coordinate of `TauCeti.AffineDynkinType.natMarks` is positive. -/
theorem natMarks_pos (t : AffineDynkinType) (i : Fin t.nodes) : 0 < t.natMarks i := by
  exact_mod_cast (t.coe_natMarks i).symm ▸ t.marks_pos i

/-- At `affineNode`, `TauCeti.AffineDynkinType.natMarks` equals `1`. -/
@[simp]
theorem natMarks_affineNode (t : AffineDynkinType) : t.natMarks t.affineNode = 1 := by
  exact_mod_cast (t.coe_natMarks t.affineNode).trans t.marks_affineNode

/-- The `ℕ`-valued marks have coordinate gcd `1`. -/
@[simp]
theorem gcd_natMarks (t : AffineDynkinType) : univ.gcd t.natMarks = 1 :=
  Nat.dvd_one.mp (t.natMarks_affineNode ▸ univ.gcd_dvd (f := t.natMarks) (mem_univ t.affineNode))

/-- On a valid graphical affine diagram, `TauCeti.AffineDynkinType.natMarks` satisfies the
neighbor-sum balance `∑ j ∈ neighborFinset i, natMarks j = 2 * natMarks i`. -/
theorem sum_natMarks_neighborFinset_eq_two_mul {t : AffineDynkinType} (ht : t.Valid)
    (hg : t.IsGraphical) (i : Fin t.nodes) :
    ∑ j ∈ t.graph.neighborFinset i, t.natMarks j = 2 * t.natMarks i := by
  have hs := sum_marks_neighborFinset_eq_two_mul ht hg i
  simp_rw [← coe_natMarks] at hs
  exact_mod_cast hs

end TauCeti.AffineDynkinType

namespace SimpleGraph

variable {V : Type*} [Fintype V]
  {G : SimpleGraph V} [DecidableRel G.Adj] {t : TauCeti.AffineDynkinType}

/-- An isomorphism with a graphical affine diagram identifies every natural-valued null vector
with its coordinate gcd times the native marks. Thus gcd one fixes the primitive normalization. -/
theorem Iso.eq_gcd_smul_marks_comp (e : G ≃g t.graph) (ht : t.Valid) (hg : t.IsGraphical)
    {a : V → ℕ} (ha : ∀ i, ∑ j ∈ G.neighborFinset i, a j = 2 * a i) :
    (fun i ↦ (a i : ℤ)) = ((univ.gcd a : ℕ) : ℤ) • (t.marks ∘ e) := by
  let δ : V → ℕ := fun k ↦ t.natMarks (e k)
  have hmarks (i : V) : ∑ j ∈ G.neighborFinset i, δ j = 2 * δ i := by
    dsimp only [δ]
    rw [e.sum_neighborFinset_comp]
    exact t.sum_natMarks_neighborFinset_eq_two_mul ht hg (e i)
  have hprim : univ.gcd δ = 1 := by
    refine Nat.dvd_one.mp ?_
    have h1 : δ (e.symm t.affineNode) = 1 := by simp [δ]
    exact h1 ▸ univ.gcd_dvd (f := δ) (mem_univ (e.symm t.affineNode))
  have hG := e.preconnected_iff.mpr
    (TauCeti.AffineDynkinType.graph_connected ht).preconnected
  have heq := hG.eq_gcd_smul_of_sum_eq_two_mul hmarks hprim ha
  ext i
  have hi := congrFun heq i
  simp only [δ, Pi.smul_apply, smul_eq_mul, Function.comp_apply] at hi ⊢
  rw [hi, Nat.cast_mul, t.coe_natMarks]

end SimpleGraph
