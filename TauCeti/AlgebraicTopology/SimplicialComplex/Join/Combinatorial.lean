/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Simplex.Join
public import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Stellar.Join

/-!
# Joins of combinatorial balls and spheres

The join of two combinatorial spheres is a combinatorial sphere. Joining a combinatorial
sphere with a combinatorial ball, or two combinatorial balls, gives a combinatorial ball.
In each case dimensions add with an extra `1`.

These results classify links expressed as a join of a simplex boundary with another link,
as occurs at the new vertex of a stellar subdivision. Unlike the standard-model calculations
in `Simplex.Join`, the factors here may themselves have undergone arbitrary stellar moves
and injective relabelings. The transport uses
`PreAbstractSimplicialComplex.StellarEquivalentUpToRelabeling.join`.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapters 2 and 3 (joins and combinatorial balls and spheres).
* W. B. R. Lickorish, *Simplicial moves on complexes and manifolds*, Geom. Topol. Monogr. 2
  (1999), 299–320.
-/

public section

namespace PreAbstractSimplicialComplex

variable {α β : Type*} [DecidableEq α] [DecidableEq β]
  {K : PreAbstractSimplicialComplex α} {L : PreAbstractSimplicialComplex β} {m n : ℕ}

/-- The join of combinatorial `m`- and `n`-spheres is a combinatorial `(m + n + 1)`-sphere. -/
theorem IsCombinatorialSphere.join (hK : IsCombinatorialSphere K m)
    (hL : IsCombinatorialSphere L n) :
    IsCombinatorialSphere (PreAbstractSimplicialComplex.join K L) (m + n + 1) := by
  obtain ⟨V, hV, heK⟩ := isCombinatorialSphere_iff.mp hK
  obtain ⟨W, hW, heL⟩ := isCombinatorialSphere_iff.mp hL
  exact .of_stellarEquivalentUpToRelabeling (heK.join heL)
    (isCombinatorialSphere_join_simplexBoundary_simplexBoundary hV hW)

/-- The join of a combinatorial `m`-sphere and a combinatorial `n`-ball is a combinatorial
`(m + n + 1)`-ball. -/
theorem IsCombinatorialSphere.join_ball (hK : IsCombinatorialSphere K m)
    (hL : IsCombinatorialBall L n) :
    IsCombinatorialBall (PreAbstractSimplicialComplex.join K L) (m + n + 1) := by
  obtain ⟨V, hV, heK⟩ := isCombinatorialSphere_iff.mp hK
  obtain ⟨W, hW, heL⟩ := isCombinatorialBall_iff.mp hL
  exact .of_stellarEquivalentUpToRelabeling (heK.join heL)
    (isCombinatorialBall_join_simplexBoundary_simplex hV hW)

/-- The join of combinatorial `m`- and `n`-balls is a combinatorial `(m + n + 1)`-ball. -/
theorem IsCombinatorialBall.join (hK : IsCombinatorialBall K m)
    (hL : IsCombinatorialBall L n) :
    IsCombinatorialBall (PreAbstractSimplicialComplex.join K L) (m + n + 1) := by
  obtain ⟨V, hV, heK⟩ := isCombinatorialBall_iff.mp hK
  obtain ⟨W, hW, heL⟩ := isCombinatorialBall_iff.mp hL
  apply IsCombinatorialBall.of_stellarEquivalentUpToRelabeling (heK.join heL)
  rw [join_simplex_simplex]
  apply isCombinatorialBall_simplex
  simp only [Finset.card_disjSum, hV, hW]
  omega

end PreAbstractSimplicialComplex
