/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.Algebra.Category.ModuleCat.EpiMono

/-!
# Dimensions of the low-degree cochain groups

Let `A` be a representation of a group `G` over a field `k`. This file records the two
rank–nullity counts relating the one-cocycles `Z¹(G, A)`, the one-coboundaries `B¹(G, A)`, the
invariants `H⁰(G, A) = A^G` and the first cohomology `H¹(G, A)`:

* `finrank B¹ + finrank A^G = finrank A`, since `B¹` is the image of `a ↦ (g ↦ ρ g a - a)`,
  whose kernel is `A^G` (`groupCohomology.finrank_coboundaries₁_add_finrank_invariants`);
* `finrank H¹ + finrank B¹ = finrank Z¹` when `Z¹` is finite-dimensional, since `H¹` is the
  quotient of `Z¹` by `B¹` (`groupCohomology.finrank_H1_add_finrank_coboundaries₁`). This holds
  for instance when `G` is finitely generated and `A` is finite-dimensional, as a one-cocycle is
  determined by its values on generators.

Together they give `finrank H¹ = finrank Z¹ - finrank A + finrank A^G`, the form in which
Euler-characteristic computations of `H¹` use them.
-/

public section

open CategoryTheory Module

universe u

namespace groupCohomology

variable {k G : Type u} [Field k] [Group G] (A : Rep k G)

/-- **Rank–nullity for the coboundaries.** The one-coboundaries are the image of
`a ↦ (g ↦ ρ g a - a)`, whose kernel is the space of invariants. -/
theorem finrank_coboundaries₁_add_finrank_invariants [FiniteDimensional k A] :
    finrank k (coboundaries₁ A) + finrank k A.ρ.invariants = finrank k A := by
  rw [← d₀₁_ker_eq_invariants]
  exact LinearMap.finrank_range_add_finrank_ker (d₀₁ A).hom

/-- **Rank–nullity for the first cohomology.** When the one-cocycles form a finite-dimensional
space, `H¹` is their quotient by the one-coboundaries. -/
theorem finrank_H1_add_finrank_coboundaries₁ [FiniteDimensional k (cocycles₁ A)] :
    finrank k (H1 A) + finrank k (coboundaries₁ A) = finrank k (cocycles₁ A) := by
  have hsurj : Function.Surjective (H1π A).hom :=
    (ModuleCat.epi_iff_surjective (H1π A)).1 inferInstance
  have hker : LinearMap.ker (H1π A).hom = (coboundaries₁ A).comap (cocycles₁ A).subtype := by
    ext x
    exact H1π_eq_zero_iff x
  have := LinearMap.finrank_range_add_finrank_ker (H1π A).hom
  rw [LinearMap.range_eq_top.2 hsurj, finrank_top, hker,
    (Submodule.comapSubtypeEquivOfLe (coboundaries₁_le_cocycles₁ A)).finrank_eq] at this
  exact this

end groupCohomology
