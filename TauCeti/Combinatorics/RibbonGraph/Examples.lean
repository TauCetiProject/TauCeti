/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PermutationTriple.Examples
public import TauCeti.Combinatorics.RibbonGraph.Genus

/-!
# Examples of dessins d'enfants

This file realizes the standard small permutation triples as finite bipartite ribbon graphs and
computes their cells.  In positive degree `n`, the cyclic dessin is an `n`-star: one black
vertex, `n` white vertices, `n` edges, and one face; in degree zero it is the formal empty dessin,
with no edges, vertices, or faces.  The dessin of `z ↦ 4z(1 - z)` is a two-edge segment.  The
degree-four Euclidean example has one vertex of each colour and two faces, so it lies on a torus.
The degree-three symmetric example has one black vertex, two white vertices, and two faces.

The definitions use the general construction from permutation triples.  The cell counts below
spell out the resulting graphs without choosing representatives for their quotient vertex and
face types, and the Euler characteristic and genus computations agree with the corresponding
triple invariants.  The definitions are computable and exposed, so their invariants also evaluate
directly: for instance, `torusDessin.genus = 1` holds by `decide`, and `#eval torusDessin.eulerChar`
returns `0`.

## References

* S. K. Lando, A. K. Zvonkin, *Graphs on Surfaces and Their Applications*, Encyclopaedia of
  Mathematical Sciences 141, Springer 2004, §1.3 and §1.5.
* E. Girondo, G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins d'Enfants*,
  London Mathematical Society Student Texts 79, Cambridge University Press 2012, §4.2.
-/

public section

namespace TauCeti

namespace BipartiteRibbonGraph

open PermutationTriple

/-! ### The cyclic star -/

/-- The dessin of the cyclic triple of degree `n`.  In positive degree it is the `n`-star. -/
@[expose] def cyclicDessin (n : ℕ) : BipartiteRibbonGraph :=
  (cyclicTriple n).ribbonGraph

/-- The cyclic dessin is the ribbon graph constructed from the cyclic permutation triple. -/
theorem cyclicDessin_def : cyclicDessin n = (cyclicTriple n).ribbonGraph := (rfl)

/-- The cyclic dessin has `n` edges. -/
@[simp] theorem card_E_cyclicDessin : Fintype.card (cyclicDessin n).E = n := by
  rw [cyclicDessin_def]
  exact PermutationTriple.card_E_ribbonGraph _

/-- In positive degree, the cyclic dessin has one black vertex. -/
@[simp] theorem card_B_cyclicDessin (hn : n ≠ 0) : Fintype.card (cyclicDessin n).B = 1 := by
  rw [cyclicDessin_def, PermutationTriple.card_B_ribbonGraph, ← cycleCounts_σ0,
    cycleCounts_cyclicTriple hn]

/-- The degree-zero cyclic dessin has no black vertices. -/
@[simp] theorem card_B_cyclicDessin_zero : Fintype.card (cyclicDessin 0).B = 0 := by
  decide

/-- Every edge of the cyclic dessin has its own white vertex. -/
@[simp] theorem card_W_cyclicDessin : Fintype.card (cyclicDessin n).W = n := by
  rw [cyclicDessin_def, PermutationTriple.card_W_ribbonGraph, cyclicTriple_σ1, orbitCount_one,
    Nat.card_eq_fintype_card, Fintype.card_fin]

/-- In positive degree, the cyclic dessin has one face. -/
@[simp] theorem faceCount_cyclicDessin (hn : n ≠ 0) : (cyclicDessin n).faceCount = 1 := by
  rw [cyclicDessin_def, PermutationTriple.faceCount_ribbonGraph, ← cycleCounts_σinf,
    cycleCounts_cyclicTriple hn]

/-- The degree-zero cyclic dessin has no faces. -/
@[simp] theorem faceCount_cyclicDessin_zero : (cyclicDessin 0).faceCount = 0 := by
  decide

/-- The cyclic dessin is connected exactly in positive degree. -/
@[simp] theorem isConnected_cyclicDessin_iff : (cyclicDessin n).IsConnected ↔ n ≠ 0 := by
  simp [cyclicDessin_def]

/-- In positive degree, the cyclic dessin has Euler characteristic two. -/
@[simp] theorem eulerChar_cyclicDessin (hn : n ≠ 0) : (cyclicDessin n).eulerChar = 2 := by
  simp [cyclicDessin_def, eulerChar_cyclicTriple hn]

/-- The degree-zero cyclic dessin has Euler characteristic zero. -/
@[simp] theorem eulerChar_cyclicDessin_zero : (cyclicDessin 0).eulerChar = 0 := by
  decide

/-- In positive degree, the cyclic dessin has genus zero. -/
@[simp] theorem genus_cyclicDessin (hn : n ≠ 0) : (cyclicDessin n).genus = 0 := by
  simp [cyclicDessin_def, genus_cyclicTriple hn]

/-- The truncated genus formula assigns genus one to the degree-zero cyclic dessin. -/
@[simp] theorem genus_cyclicDessin_zero : (cyclicDessin 0).genus = 1 := by
  decide

/-! ### The segment dessin -/

/-- The two-edge segment dessin associated to the map `z ↦ 4z(1 - z)`. -/
@[expose] def segmentDessin : BipartiteRibbonGraph :=
  chebyshevTriple.ribbonGraph

/-- The segment dessin is the ribbon graph constructed from the Chebyshev permutation triple. -/
theorem segmentDessin_def : segmentDessin = chebyshevTriple.ribbonGraph := (rfl)

/-- The segment dessin has two edges. -/
@[simp] theorem card_E_segmentDessin : Fintype.card segmentDessin.E = 2 := by
  rw [segmentDessin_def]
  exact PermutationTriple.card_E_ribbonGraph _

/-- The segment dessin has two black vertices. -/
@[simp] theorem card_B_segmentDessin : Fintype.card segmentDessin.B = 2 := by
  rw [segmentDessin_def, PermutationTriple.card_B_ribbonGraph, ← cycleCounts_σ0,
    cycleCounts_eq_card_cycleData, cycleData_chebyshevTriple]
  rfl

/-- The segment dessin has one white vertex. -/
@[simp] theorem card_W_segmentDessin : Fintype.card segmentDessin.W = 1 := by
  rw [segmentDessin_def, PermutationTriple.card_W_ribbonGraph, ← cycleCounts_σ1,
    cycleCounts_eq_card_cycleData, cycleData_chebyshevTriple]
  rfl

/-- The segment dessin has one face. -/
@[simp] theorem faceCount_segmentDessin : segmentDessin.faceCount = 1 := by
  rw [segmentDessin_def, PermutationTriple.faceCount_ribbonGraph, ← cycleCounts_σinf,
    cycleCounts_eq_card_cycleData, cycleData_chebyshevTriple]
  rfl

/-- The segment dessin is connected. -/
@[simp] theorem isConnected_segmentDessin : segmentDessin.IsConnected := by
  simpa [segmentDessin_def] using isConnected_chebyshevTriple

/-- The segment dessin has Euler characteristic two. -/
@[simp] theorem eulerChar_segmentDessin : segmentDessin.eulerChar = 2 := by
  simp [segmentDessin_def, eulerChar_chebyshevTriple]

/-- The segment dessin has genus zero. -/
@[simp] theorem genus_segmentDessin : segmentDessin.genus = 0 := by
  simp [segmentDessin_def, genus_chebyshevTriple]

/-! ### The torus dessin -/

/-- The four-edge dessin associated to `torusTriple`. -/
@[expose] def torusDessin : BipartiteRibbonGraph :=
  torusTriple.ribbonGraph

/-- The torus dessin is the ribbon graph constructed from the Euclidean genus-one triple. -/
theorem torusDessin_def : torusDessin = torusTriple.ribbonGraph := (rfl)

/-- The torus dessin has four edges. -/
@[simp] theorem card_E_torusDessin : Fintype.card torusDessin.E = 4 := by
  rw [torusDessin_def]
  exact PermutationTriple.card_E_ribbonGraph _

/-- The torus dessin has one black vertex. -/
@[simp] theorem card_B_torusDessin : Fintype.card torusDessin.B = 1 := by
  rw [torusDessin_def, PermutationTriple.card_B_ribbonGraph, ← cycleCounts_σ0,
    cycleCounts_torusTriple]

/-- The torus dessin has one white vertex. -/
@[simp] theorem card_W_torusDessin : Fintype.card torusDessin.W = 1 := by
  rw [torusDessin_def, PermutationTriple.card_W_ribbonGraph, ← cycleCounts_σ1,
    cycleCounts_torusTriple]

/-- The torus dessin has two faces. -/
@[simp] theorem faceCount_torusDessin : torusDessin.faceCount = 2 := by
  rw [torusDessin_def, PermutationTriple.faceCount_ribbonGraph, ← cycleCounts_σinf,
    cycleCounts_torusTriple]

/-- The torus dessin is connected. -/
@[simp] theorem isConnected_torusDessin : torusDessin.IsConnected := by
  simpa [torusDessin_def] using isConnected_torusTriple

/-- The torus dessin has Euler characteristic zero. -/
@[simp] theorem eulerChar_torusDessin : torusDessin.eulerChar = 0 := by
  simp [torusDessin_def, eulerChar_torusTriple]

/-- The torus dessin has genus one. -/
@[simp] theorem genus_torusDessin : torusDessin.genus = 1 := by
  simp [torusDessin_def, genus_torusTriple]

/-! ### The symmetric degree-three dessin -/

/-- The three-edge dessin associated to the triple with monodromy group `S₃`. -/
@[expose] def s3Dessin : BipartiteRibbonGraph :=
  s3Triple.ribbonGraph

/-- The symmetric degree-three dessin is the ribbon graph constructed from `s3Triple`. -/
theorem s3Dessin_def : s3Dessin = s3Triple.ribbonGraph := (rfl)

/-- The symmetric degree-three dessin has three edges. -/
@[simp] theorem card_E_s3Dessin : Fintype.card s3Dessin.E = 3 := by
  rw [s3Dessin_def]
  exact PermutationTriple.card_E_ribbonGraph _

/-- The symmetric degree-three dessin has one black vertex. -/
@[simp] theorem card_B_s3Dessin : Fintype.card s3Dessin.B = 1 := by
  rw [s3Dessin_def, PermutationTriple.card_B_ribbonGraph, ← cycleCounts_σ0,
    cycleCounts_eq_card_cycleData, cycleData_s3Triple]
  rfl

/-- The symmetric degree-three dessin has two white vertices. -/
@[simp] theorem card_W_s3Dessin : Fintype.card s3Dessin.W = 2 := by
  rw [s3Dessin_def, PermutationTriple.card_W_ribbonGraph, ← cycleCounts_σ1,
    cycleCounts_eq_card_cycleData, cycleData_s3Triple]
  rfl

/-- The symmetric degree-three dessin has two faces. -/
@[simp] theorem faceCount_s3Dessin : s3Dessin.faceCount = 2 := by
  rw [s3Dessin_def, PermutationTriple.faceCount_ribbonGraph, ← cycleCounts_σinf,
    cycleCounts_eq_card_cycleData, cycleData_s3Triple]
  rfl

/-- The symmetric degree-three dessin is connected. -/
@[simp] theorem isConnected_s3Dessin : s3Dessin.IsConnected := by
  simpa [s3Dessin_def] using isConnected_s3Triple

/-- The symmetric degree-three dessin has Euler characteristic two. -/
@[simp] theorem eulerChar_s3Dessin : s3Dessin.eulerChar = 2 := by
  simp [s3Dessin_def, eulerChar_s3Triple]

/-- The symmetric degree-three dessin has genus zero. -/
@[simp] theorem genus_s3Dessin : s3Dessin.genus = 0 := by
  simp [s3Dessin_def, genus_s3Triple]

end BipartiteRibbonGraph

end TauCeti
