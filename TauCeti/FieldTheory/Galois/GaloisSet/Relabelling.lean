/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.GaloisSet.Basic
import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Relabelling finite Galois sets

Permutations of the labels act on labelled Galois sets by conjugating their permutation
representations. Two labelled Galois sets lie in the same orbit exactly when there is an
equivariant bijection between them. The stabilizer consists of the equivariant permutations,
or equivalently the centralizer of the image of the Galois representation. Thus orbit–stabilizer
counts the labellings of an isomorphism class with the automorphism multiplicity required in
mass formulas.

## References

* M. Bhargava, *Mass formulae for extensions of local fields, and conjectures on the density
  of number field discriminants*, IMRN 2007, rnm052, §2.
* K. S. Kedlaya, *Mass formulas for local Galois representations*, IMRN 2007, rnm021.
-/

public section

noncomputable section

namespace TauCeti.GaloisSet

variable {K : Type*} [Field K] {n : ℕ}

/-- Relabelling conjugates the permutation representation and preserves its open kernel. -/
instance : SMul (Equiv.Perm (Fin n)) (GaloisSet K n) where
  smul e ρ := ⟨(MulAut.conj e).toMonoidHom.comp ρ.val, by
    rw [MonoidHom.ker_comp_of_injective _ _ (MulAut.conj e).injective]
    exact ρ.property⟩

/-- Relabelling by `e` transports the action through `e`. -/
@[simp]
theorem smul_val_apply (ρ : GaloisSet K n) (e : Equiv.Perm (Fin n))
    (σ : Gal(SeparableClosure K/K)) (i : Fin n) :
    (e • ρ).val σ i = e (ρ.val σ (e.symm i)) :=
  (rfl)

/-- The conjugation of representations is an action of the permutation group. -/
instance : MulAction (Equiv.Perm (Fin n)) (GaloisSet K n) where
  one_smul ρ := by
    ext σ i
    simp [Equiv.Perm.one_def]
  mul_smul e f ρ := by
    ext σ i
    simp [Equiv.Perm.mul_def]

/-- Relabelling leaves the kernel of the Galois representation unchanged. -/
@[simp]
theorem ker_smul (ρ : GaloisSet K n) (e : Equiv.Perm (Fin n)) :
    (e • ρ).val.ker = ρ.val.ker :=
  MonoidHom.ker_comp_of_injective _ _ (MulAut.conj e).injective

/-- A relabelling identifies two actions exactly when it is equivariant. -/
theorem smul_eq_iff (ρ τ : GaloisSet K n) (e : Equiv.Perm (Fin n)) :
    e • ρ = τ ↔ ∀ σ i, e (ρ.val σ i) = τ.val σ (e i) := by
  constructor
  · intro h σ i
    have := congrArg (fun μ : GaloisSet K n ↦ μ.val σ (e i)) h
    simpa using this
  · intro h
    apply ext
    intro σ i
    simpa using h σ (e.symm i)

/-- Orbits under relabelling are precisely equivariant isomorphism classes. -/
theorem mem_orbit_iff (ρ τ : GaloisSet K n) :
    τ ∈ MulAction.orbit (Equiv.Perm (Fin n)) ρ ↔
      ∃ e : Equiv.Perm (Fin n), ∀ σ i, e (ρ.val σ i) = τ.val σ (e i) := by
  simp only [MulAction.mem_orbit_iff, smul_eq_iff]

/-- A permutation fixes a labelled Galois set exactly when it is equivariant. -/
theorem mem_stabilizer_iff (ρ : GaloisSet K n) (e : Equiv.Perm (Fin n)) :
    e ∈ MulAction.stabilizer (Equiv.Perm (Fin n)) ρ ↔
      ∀ σ i, e (ρ.val σ i) = ρ.val σ (e i) := by
  rw [MulAction.mem_stabilizer_iff, smul_eq_iff]

/-- The automorphisms of a labelled Galois set centralize the Galois image. -/
theorem stabilizer_eq_centralizer (ρ : GaloisSet K n) :
    MulAction.stabilizer (Equiv.Perm (Fin n)) ρ =
      Subgroup.centralizer (Set.range ρ.val) := by
  ext e
  simp only [mem_stabilizer_iff, Subgroup.mem_centralizer_iff, Set.forall_mem_range]
  constructor
  · intro h σ
    exact Equiv.ext fun i ↦ (h σ i).symm
  · intro h σ i
    exact (congrArg (fun f : Equiv.Perm (Fin n) ↦ f i) (h σ)).symm

/-- Relabellings preserve transitivity. -/
@[simp]
theorem isTransitive_smul_iff (ρ : GaloisSet K n) (e : Equiv.Perm (Fin n)) :
    (e • ρ).IsTransitive ↔ ρ.IsTransitive := by
  simp only [isTransitive_iff, smul_val_apply]
  constructor
  · intro h i j
    obtain ⟨σ, hσ⟩ := h (e i) (e j)
    exact ⟨σ, e.injective (by simpa using hσ)⟩
  · intro h i j
    obtain ⟨σ, hσ⟩ := h (e.symm i) (e.symm j)
    exact ⟨σ, by simp [hσ]⟩

/-- The trivial representation is fixed by every relabelling. -/
@[simp]
theorem smul_trivial {e : Equiv.Perm (Fin n)} : e • trivial K n = trivial K n := by
  ext σ i
  simp

end TauCeti.GaloisSet
