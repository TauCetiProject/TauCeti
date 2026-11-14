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
Under any actual isomorphism to a graphical affine diagram, every natural-valued additive
function is its coordinate gcd times the transported marks. In particular, the unique positive
primitive integral null vector is the transported native marks. This comparison does not
assume that a chosen vertex of the original graph has mark one.

See Kac, *Infinite dimensional Lie algebras*, 3rd edition, Chapter 4, for affine marks and
positive additive functions.
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

end TauCeti.AffineDynkinType

namespace SimpleGraph

variable {V : Type*} [Fintype V]
  {G : SimpleGraph V} [DecidableRel G.Adj] {t : TauCeti.AffineDynkinType}

/-- An isomorphism with a graphical affine diagram identifies every natural-valued null vector
with its coordinate gcd times the native marks. Thus gcd one fixes the primitive normalization. -/
theorem Iso.eq_gcd_smul_marks_comp (e : G ≃g t.graph) (ht : t.Valid) (hg : t.IsGraphical)
    {a : V → ℕ} (ha : ∀ i, ∑ j ∈ G.neighborFinset i, a j = 2 * a i) :
    (fun i ↦ (a i : ℤ)) = ((univ.gcd a : ℕ) : ℤ) • (t.marks ∘ e) := by
  let δ : V → ℕ := fun i ↦ (t.marks (e i)).toNat
  have hcast (i : V) : (δ i : ℤ) = t.marks (e i) :=
    Int.toNat_of_nonneg (t.marks_pos (e i)).le
  have hmarks (i : V) : ∑ j ∈ G.neighborFinset i, δ j = 2 * δ i := by
    have hs : ∑ j ∈ G.neighborFinset i, t.marks (e j) = 2 * t.marks (e i) := by
      rw [e.sum_neighborFinset_comp]
      exact TauCeti.AffineDynkinType.sum_marks_neighborFinset_eq_two_mul ht hg (e i)
    simp_rw [← hcast] at hs
    exact_mod_cast hs
  have hprim : univ.gcd δ = 1 := by
    apply Nat.dvd_one.mp
    have hdvd : ((univ.gcd δ : ℕ) : ℤ) ∣ univ.gcd t.marks := by
      apply Finset.dvd_gcd
      intro j _
      obtain ⟨i, rfl⟩ := e.surjective j
      rw [← hcast]
      exact_mod_cast (univ.gcd_dvd (f := δ) (mem_univ i))
    rw [t.gcd_marks] at hdvd
    exact_mod_cast hdvd
  have hG := e.preconnected_iff.mpr
    (TauCeti.AffineDynkinType.graph_connected ht).preconnected
  have heq := hG.eq_gcd_smul_of_sum_eq_two_mul hmarks hprim ha
  ext i
  have hi := congrFun heq i
  simp only [Pi.smul_apply, smul_eq_mul, Function.comp_apply] at hi ⊢
  rw [hi, Nat.cast_mul, hcast]

end SimpleGraph
