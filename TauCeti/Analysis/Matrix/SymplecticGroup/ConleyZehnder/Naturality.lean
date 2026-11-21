/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
public import TauCeti.Analysis.Matrix.SymplecticGroup.ConleyZehnder.Zero
public import TauCeti.Analysis.Matrix.SymplecticGroup.Connected
import TauCeti.LinearAlgebra.Eigenspace.Matrix

/-!
# Naturality of the Conley–Zehnder index

The Conley–Zehnder index of a path `Ψ` of symplectic matrices
(`TauCeti.GLSymplectic.conleyZehnderIndex`) is invariant under conjugation by a constant
symplectic matrix: `CZ(P Ψ P⁻¹) = CZ(Ψ)` (`TauCeti.GLSymplectic.conleyZehnderIndex_map_conj`).
This is the naturality axiom of the index; together with the loop axiom it describes how the index
changes under a change of symplectic trivialization.

The proof goes through the zero axiom
(`TauCeti.GLSymplectic.conleyZehnderIndex_eq_zero_of_finrank_eigenspace_eq`). The symplectic group
is path connected, so `P` is joined to the identity by a path `δ`, and
`(s, t) ↦ δ s Ψ(t) (δ s)⁻¹` is a homotopy from `Ψ` to `P Ψ P⁻¹`. Its paths
`s ↦ δ s Ψ(0) (δ s)⁻¹` and `s ↦ δ s Ψ(1) (δ s)⁻¹` through the endpoints run through conjugates of
a fixed matrix, so they have index zero, and the two paths have the same index.

## Main results

* `TauCeti.GLSymplectic.conleyZehnderIndex_map_conj`: naturality under conjugation by a constant
  symplectic matrix.

## References

* J. Robbin and D. Salamon, *The Maslov index for paths*, Topology **32** (1993), 827–844,
  Theorem 2.3 (the naturality axiom).
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. **7**, AMS, 1999 (the naturality axiom of the Conley–Zehnder index).
-/

public section

open Matrix Module Module.End TauCeti
open scoped unitInterval

namespace TauCeti.GLSymplectic

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Naturality of the Conley–Zehnder index.** Conjugating a path of symplectic matrices by a
constant symplectic matrix `P` does not change its Conley–Zehnder index: `CZ(P Ψ P⁻¹) = CZ(Ψ)`. -/
theorem conleyZehnderIndex_map_conj (P : GLSymplectic n ℝ) {A B : GLSymplectic n ℝ}
    (γ : Path A B) :
    conleyZehnderIndex (γ.map (f := fun X ↦ P * X * P⁻¹) (by fun_prop)) =
      conleyZehnderIndex γ := by
  let δ := PathConnectedSpace.somePath (1 : GLSymplectic n ℝ) P
  -- The homotopy `(s, t) ↦ δ s γ(t) (δ s)⁻¹` from `γ` to its conjugate by `P`.
  let F : ContinuousMap.Homotopy (⟨γ, γ.continuous⟩ : C(I, GLSymplectic n ℝ))
      ⟨fun t ↦ P * γ t * P⁻¹, by fun_prop⟩ :=
    { toFun := fun p ↦ δ p.1 * γ p.2 * (δ p.1)⁻¹
      continuous_toFun := by fun_prop
      map_zero_left := fun t ↦ by simp [δ]
      map_one_left := fun t ↦ by simp [δ] }
  -- `F` evaluates by its defining formula; Mathlib has no `coe_mk` lemma for homotopies.
  have hF_apply (p : I × I) : F p = δ p.1 * γ p.2 * (δ p.1)⁻¹ := rfl
  -- Its paths through the endpoints run through conjugates of a fixed matrix.
  have hedge (x : I) : conleyZehnderIndex (F.evalAt x) = 0 := by
    refine conleyZehnderIndex_eq_zero_of_finrank_eigenspace_eq _
      (k := finrank ℝ (eigenspace (toLin' ((γ x : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)) 1))
      fun s ↦ ?_
    have hF : ((F.evalAt x s : GLSymplectic n ℝ) : GL (n ⊕ n) ℝ) =
        (δ s : GL (n ⊕ n) ℝ) * (γ x : GL (n ⊕ n) ℝ) * (δ s : GL (n ⊕ n) ℝ)⁻¹ := by
      rw [ContinuousMap.Homotopy.evalAt_apply, hF_apply, Subgroup.coe_mul, Subgroup.coe_mul,
        Subgroup.coe_inv]
    rw [hF, Units.val_mul, Units.val_mul]
    exact finrank_eigenspace_toLin'_conj (δ s : GL (n ⊕ n) ℝ) _ 1
  have h := conleyZehnderIndex_eq_of_homotopic (Path.Homotopic.map_trans_evalAt F Path.id)
  rw [conleyZehnderIndex_trans, conleyZehnderIndex_trans, hedge, hedge, add_zero, zero_add] at h
  -- Along `Path.id`, the two maps are `γ` and its conjugate, with endpoints written differently.
  rw [conleyZehnderIndex_def, conleyZehnderIndex_def, neg_inj] at h
  rw [conleyZehnderIndex_def, conleyZehnderIndex_def, neg_inj]
  refine Eq.trans ?_ (h.symm.trans ?_) <;>
    exact UnitaryGroup.maslovIndex_eq_of_souriau_eq _ _ fun _ ↦ by simp [Path.map_coe]

end TauCeti.GLSymplectic
