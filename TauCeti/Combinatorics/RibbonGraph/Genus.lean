/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.RibbonGraph.EulerCharacteristic

/-!
# Genus of a bipartite ribbon graph

The rotations of a finite bipartite ribbon graph encode a permutation triple after numbering
the edges. The comparison of their Euler characteristics gives parity and the connected Euler
bound for the graph. Its combinatorial genus is therefore a natural number satisfying
`χ = 2 - 2g` when the graph is connected. It agrees with the genus of any numbered triple,
independently of the choice of numbering, and is preserved by graph isomorphisms.

For a connected graph, this is the genus of the oriented combinatorial surface determined by
the rotation system; no analytic surface is needed. For a disconnected graph, `genus` is the
truncated quotient `((2 - χ) / 2).toNat`, which need not be the surface genus.

## References

* S. K. Lando, A. K. Zvonkin, *Graphs on Surfaces and Their Applications*, Encyclopaedia of
  Mathematical Sciences 141, Springer 2004, §1.3 and §1.5.
-/

public section

namespace TauCeti

universe u

namespace BipartiteRibbonGraph

variable (Γ : BipartiteRibbonGraph.{u})

/-- The combinatorial genus of a bipartite ribbon graph. It has its geometric meaning for a
connected graph; the defining truncated quotient need not be a genus for a disconnected graph. -/
noncomputable def genus : ℕ := ((2 - Γ.eulerChar) / 2).toNat

/-- The genus is obtained from the graph's Euler characteristic. -/
theorem genus_def : Γ.genus = ((2 - Γ.eulerChar) / 2).toNat := (rfl)

/-- The genus of a numbered ribbon graph is the genus of its permutation triple. -/
@[simp] theorem genus_toPermutationTriple {n : ℕ} (ν : Γ.E ≃ Fin n) :
    (Γ.toPermutationTriple ν).genus = Γ.genus := by
  rw [PermutationTriple.genus_def, genus_def, Γ.eulerChar_toPermutationTriple]

/-- A connected graph's genus is exactly the quotient `(2 - χ) / 2` in the integers. -/
theorem IsConnected.natCast_genus (hΓ : Γ.IsConnected) :
    (Γ.genus : ℤ) = (2 - Γ.eulerChar) / 2 := by
  let ν := Fintype.equivFin Γ.E
  rw [← Γ.genus_toPermutationTriple ν, ← Γ.eulerChar_toPermutationTriple ν]
  exact ((Γ.isConnected_toPermutationTriple ν).mpr hΓ).natCast_genus

/-- The Euler characteristic of a connected bipartite ribbon graph is `2 - 2g`. -/
theorem IsConnected.two_sub_two_mul_genus (hΓ : Γ.IsConnected) :
    2 - 2 * (Γ.genus : ℤ) = Γ.eulerChar := by
  let ν := Fintype.equivFin Γ.E
  rw [← Γ.genus_toPermutationTriple ν, ← Γ.eulerChar_toPermutationTriple ν]
  exact ((Γ.isConnected_toPermutationTriple ν).mpr hΓ).two_sub_two_mul_genus

/-- Isomorphic ribbon graphs have the same combinatorial genus. -/
theorem Iso.genus_eq {Δ : BipartiteRibbonGraph.{u}} (f : Γ.Iso Δ) :
    Γ.genus = Δ.genus := by
  rw [genus_def, genus_def, f.eulerChar_eq]

end BipartiteRibbonGraph

namespace PermutationTriple

/-- Passing from a permutation triple to its ribbon graph preserves the combinatorial genus. -/
@[simp] theorem genus_ribbonGraph {n : ℕ} (t : PermutationTriple n) :
    t.ribbonGraph.genus = t.genus := by
  rw [BipartiteRibbonGraph.genus_def, genus_def, eulerChar_ribbonGraph]

end PermutationTriple

end TauCeti
