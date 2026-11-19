/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.SymplecticGroup.ConleyZehnder.Zero

/-!
# The homotopy axiom for the Conley–Zehnder index

The Conley–Zehnder index of a path of symplectic matrices
(`TauCeti.GLSymplectic.conleyZehnderIndex`) is invariant under homotopies relative to the
endpoints (`TauCeti.GLSymplectic.conleyZehnderIndex_eq_of_homotopic`). This file proves the
stronger **homotopy axiom**, in which the endpoints may move: if `F` is a homotopy of paths of
symplectic matrices along which the eigenvalue `1` keeps the same geometric multiplicity at the
start and, possibly a different one, at the end, then the two paths have the same index
(`TauCeti.GLSymplectic.conleyZehnderIndex_eq_of_homotopy_of_finrank_eigenspace_eq`).

The main case is that of paths starting at the identity and ending at matrices without the
eigenvalue `1`, the linearized return maps of nondegenerate periodic orbits: the index is
constant along homotopies through such paths
(`TauCeti.GLSymplectic.conleyZehnderIndex_eq_of_homotopy_of_not_hasEigenvalue_one`). This is the
form in which the index grades nondegenerate orbits independently of choices. A trivialization of
the linearized flow along a capped orbit is only determined up to homotopy, and the index of the
resulting path does not depend on the choice within its homotopy class.

It is the homotopy axiom of the Maslov index of paths of unitary frames
(`Matrix.UnitaryGroup.maslovIndex_eq_of_homotopy_of_rootMultiplicity_eq`), applied to the unitary
frames of the graphs of `F`: the graph of a symplectic matrix meets the diagonal in its fixed
vectors, so the eigenvalue `1` of the Souriau map of its graph frame has the multiplicity of the
eigenvalue `1` of the matrix
(`TauCeti.GLSymplectic.rootMultiplicity_one_charpoly_souriau_graphUnitaryFrame`).

## Main results

* `TauCeti.GLSymplectic.conleyZehnderIndex_eq_of_homotopy_of_finrank_eigenspace_eq`: the homotopy
  axiom, with endpoints along which the eigenvalue `1` has constant multiplicity.
* `TauCeti.GLSymplectic.conleyZehnderIndex_eq_of_homotopy_of_not_hasEigenvalue_one`: the homotopy
  axiom for paths from the identity to matrices without the eigenvalue `1`.

## References

* J. Robbin and D. Salamon, *The Maslov index for paths*, Topology **32** (1993), 827–844,
  Sections 2 and 4 (the zero axiom and homotopies with endpoints in fixed strata).
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. **7**, AMS, 1999 (the homotopy axiom of the Conley–Zehnder index).
-/

public section

open Matrix Module Module.End TauCeti
open scoped unitInterval

namespace TauCeti.GLSymplectic

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **The homotopy axiom for the Conley–Zehnder index.** Let `F` be a homotopy from the path
`γ₀` to the path `γ₁` of symplectic matrices, with moving endpoints, such that the eigenvalue `1`
of `F (s, 0)` has the same geometric multiplicity for every `s`, and so does the eigenvalue `1` of
`F (s, 1)`. Then `γ₀` and `γ₁` have the same Conley–Zehnder index. -/
theorem conleyZehnderIndex_eq_of_homotopy_of_finrank_eigenspace_eq
    {A₀ B₀ A₁ B₁ : GLSymplectic n ℝ} (γ₀ : Path A₀ B₀) (γ₁ : Path A₁ B₁)
    (F : C(I × I, GLSymplectic n ℝ)) (h₀ : ∀ t, F (0, t) = γ₀ t) (h₁ : ∀ t, F (1, t) = γ₁ t)
    {k₀ k₁ : ℕ}
    (hk₀ : ∀ s, finrank ℝ (eigenspace
      (toLin' ((F (s, 0) : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)) 1) = k₀)
    (hk₁ : ∀ s, finrank ℝ (eigenspace
      (toLin' ((F (s, 1) : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)) 1) = k₁) :
    conleyZehnderIndex γ₀ = conleyZehnderIndex γ₁ := by
  -- Apply the homotopy axiom of the Maslov index to the unitary graph frames of `F`.
  rw [conleyZehnderIndex_def, conleyZehnderIndex_def, neg_inj]
  exact UnitaryGroup.maslovIndex_eq_of_homotopy_of_rootMultiplicity_eq _ _
    ((⟨graphUnitaryFrame, continuous_graphUnitaryFrame⟩ : C(GLSymplectic n ℝ, _)).comp F)
    (fun t ↦ by simp [h₀]) (fun t ↦ by simp [h₁])
    (fun s ↦ (rootMultiplicity_one_charpoly_souriau_graphUnitaryFrame _).trans (hk₀ s))
    fun s ↦ (rootMultiplicity_one_charpoly_souriau_graphUnitaryFrame _).trans (hk₁ s)

/-- **The homotopy axiom for paths from the identity.** Let `F` be a homotopy from the path `γ₀`
to the path `γ₁` of symplectic matrices through paths starting at the identity and ending at
matrices without the eigenvalue `1`. Then `γ₀` and `γ₁` have the same Conley–Zehnder index. -/
theorem conleyZehnderIndex_eq_of_homotopy_of_not_hasEigenvalue_one {B₀ B₁ : GLSymplectic n ℝ}
    (γ₀ : Path 1 B₀) (γ₁ : Path 1 B₁) (F : C(I × I, GLSymplectic n ℝ))
    (h₀ : ∀ t, F (0, t) = γ₀ t) (h₁ : ∀ t, F (1, t) = γ₁ t) (hF₀ : ∀ s, F (s, 0) = 1)
    (hF₁ : ∀ s, ¬HasEigenvalue
      (toLin' ((F (s, 1) : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)) 1) :
    conleyZehnderIndex γ₀ = conleyZehnderIndex γ₁ :=
  conleyZehnderIndex_eq_of_homotopy_of_finrank_eigenspace_eq γ₀ γ₁ F h₀ h₁
    (k₀ := finrank ℝ (eigenspace
      (toLin' (((1 : GLSymplectic n ℝ) : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)) 1))
    (k₁ := 0) (fun s ↦ by rw [hF₀ s])
    fun s ↦ Submodule.finrank_eq_zero.2 (not_ne_iff.1 (mt hasEigenvalue_iff.2 (hF₁ s)))

end TauCeti.GLSymplectic
