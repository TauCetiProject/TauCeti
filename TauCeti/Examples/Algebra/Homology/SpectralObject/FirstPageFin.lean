/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Algebra.Homology.SpectralObject.FirstPageFin

/-!
# Checks for the clamped indices of the recipe `coreE₂CohomologicalFin`

For `l = 2` and the page `r = 3`, the indices `i₀ ≤ i₁ ≤ i₂ ≤ i₃` of the object at `(p, q)` are
`(0, 0, 1, 2)` at `q = 0` and `(0, 1, 2, 2)` at `q = 1`, all in `Fin 3`. The unclamped integer
formulas `q - r + 2` and `q + r - 1` would give `-1` at `q = 0` and `3` at `q = 1`, outside
`Fin 3`. At `q = 1` the indices `i₂` and `i₃` agree, so nothing enters the top row on the page
`3`. On the page `2` the indices are `(q, q, q + 1, q + 1)`, which is the first-page computation.
-/

namespace TauCeti.Examples

open CategoryTheory.Abelian.SpectralObject

example (p : ℤ) : (coreE₂CohomologicalFin 2).i₀ 3 (p, 0) = 0 := by ext; simp
example (p : ℤ) : (coreE₂CohomologicalFin 2).i₁ (p, 0) = 0 := rfl
example (p : ℤ) : (coreE₂CohomologicalFin 2).i₂ (p, 0) = 1 := rfl
example (p : ℤ) : (coreE₂CohomologicalFin 2).i₃ 3 (p, 0) = 2 := by ext; simp [Fin.clamp]

example (p : ℤ) : (coreE₂CohomologicalFin 2).i₀ 3 (p, 1) = 0 := by ext; simp
example (p : ℤ) : (coreE₂CohomologicalFin 2).i₁ (p, 1) = 1 := rfl
example (p : ℤ) : (coreE₂CohomologicalFin 2).i₂ (p, 1) = 2 := rfl
example (p : ℤ) : (coreE₂CohomologicalFin 2).i₃ 3 (p, 1) = 2 := by ext; simp [Fin.clamp]

-- On the page `2`, the indices are those of the first-page computation.
example (l : ℕ) (pq : ℤ × Fin l) :
    (coreE₂CohomologicalFin l).i₀ 2 pq = (coreE₂CohomologicalFin l).i₁ pq ∧
      (coreE₂CohomologicalFin l).i₂ pq = (coreE₂CohomologicalFin l).i₃ 2 pq :=
  ⟨SpectralSequenceDataCore.hi₀₁ pq, SpectralSequenceDataCore.hi₂₃ pq⟩

end TauCeti.Examples
