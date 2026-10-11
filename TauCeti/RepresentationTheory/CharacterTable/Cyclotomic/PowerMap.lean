/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.End.FiniteOrder
public import Mathlib.RepresentationTheory.Character
public import TauCeti.RingTheory.Cyclotomic.Basic

/-!
# Power maps on exact cyclotomic character values

When `g ^ e = 1` (equivalently, the order of `g` divides `e`), an exact cyclotomic integer
in `Cyclotomic e` representing `χ(g)` can be evaluated at another primitive root. Replacing the
distinguished root by its `n`-th power gives `χ(g ^ n)`. This formulation uses ring homomorphisms
from the exact integer ring, so it applies before extending them to fields.
It supplies the power-map identity needed to align modular residues for cyclotomic lifting.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, §12.4.
* I. M. Isaacs, *Character Theory of Finite Groups*, Lemma 9.16.
-/

public section

namespace Representation

open TauCeti Module

variable {G V : Type*} [Monoid G] [AddCommGroup V] [Module ℂ V]
  [FiniteDimensional ℂ V] {e : ℕ} [NeZero e]

/-- Evaluating an exact cyclotomic character value at the `n`-th power of the distinguished
root gives the character value at `g ^ n`, provided `g ^ e = 1` (the order of `g` divides `e`). -/
theorem map_cyclotomic_character_eq_character_pow (ρ : Representation ℂ G V)
    {g : G} (hg : g ^ e = 1) {x : Cyclotomic e}
    (hx : Cyclotomic.complexEmbedding x = ρ.character g)
    (φ : Cyclotomic e →+* ℂ) {n : ℕ}
    (hφ : φ (Cyclotomic.zeta e) = Cyclotomic.complexRoot e ^ n) :
    φ x = ρ.character (g ^ n) := by
  classical
  let f : Module.End ℂ V := ρ g
  let S := (Module.End.finite_hasEigenvalue f).toFinset
  have hf : f ^ e = 1 := by simp [f, ← map_pow, hg]
  have hroot (μ : ℂ) (hμ : μ ∈ S) : μ ^ e = 1 :=
    Module.End.pow_eq_one_of_hasEigenvalue hf
      ((Module.End.finite_hasEigenvalue f).mem_toFinset.mp hμ)
  let a (μ : ℂ) : ℕ := if h : μ ^ e = 1 then
    (Cyclotomic.isPrimitiveRoot_complexRoot.eq_pow_of_pow_eq_one h).choose else 0
  have ha (μ : ℂ) (hμ : μ ∈ S) : Cyclotomic.complexRoot e ^ a μ = μ := by
    simp only [a, dite_eq_left (hroot μ hμ)]
    exact (Cyclotomic.isPrimitiveRoot_complexRoot.eq_pow_of_pow_eq_one
      (hroot μ hμ)).choose_spec.2
  have htrace (m : ℕ) : ρ.character (g ^ m) =
      ∑ μ ∈ S, (finrank ℂ (f.eigenspace μ) : ℂ) * μ ^ m := by
    simp only [Representation.character, map_pow]
    exact Module.End.trace_pow_eq_sum_eigenvalue_pow
      (Nat.cast_ne_zero.mpr (NeZero.ne e)) hf m
  have hexact : x = ∑ μ ∈ S,
      (finrank ℂ (f.eigenspace μ) : Cyclotomic e) * Cyclotomic.zeta e ^ a μ := by
    apply Cyclotomic.complexEmbedding_injective
    rw [hx]
    simp only [map_sum, map_mul, map_natCast, map_pow, Cyclotomic.complexEmbedding_zeta]
    rw [← pow_one g, htrace 1]
    exact Finset.sum_congr rfl fun μ hμ ↦ by rw [pow_one, ha μ hμ]
  rw [hexact, htrace]
  simp only [map_sum, map_mul, map_natCast, map_pow, hφ]
  exact Finset.sum_congr rfl fun μ hμ ↦ by rw [pow_right_comm, ha μ hμ]

end Representation
