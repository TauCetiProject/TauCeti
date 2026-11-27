/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Relative
public import TauCeti.Geometry.Manifold.Boundary.Collar.Deformation
import TauCeti.AlgebraicTopology.Cohomology.HomotopyInvariance
import TauCeti.AlgebraicTopology.Cohomology.Triple

/-!
# Relative cohomology modulo a collar of positive depth

Let `c : N × [0, 1) → X` be a collar of `f : N → X` (`TauCeti.IsCollar`), and for `0 < t` let
`Cₜ = c(N × [0, t))` be its part of depth less than `t` (`TauCeti.collarPart`). The collar deforms
`Cₜ` onto the boundary `f(N)` relative to `f(N)` (`TauCeti.IsCollar.collarDeformation`), so the
pair `(Cₜ, f(N))` has no relative cohomology, and by the long exact sequence of the triple
`(X, Cₜ, f(N))` restriction `Hᵏ(X, Cₜ) ⟶ Hᵏ(X, f(N))` is an isomorphism
(`TauCeti.IsCollar.isIso_singularCohomologyMap_ofSubsetMap_collarPart`).

This is the cohomology form of `TauCeti.IsCollar.isIso_localHomologyRestriction_compl_collarPart`.
For a compact manifold with collared boundary it reads the cohomology relative to the boundary on
the complement of an open collar, a compact subset of the interior, as in Lefschetz duality.

## Main results

* `TauCeti.IsCollar.isIso_singularCohomologyMap_ofSubsetMap_collarPart`: for `0 < t`, restriction
  `Hᵏ(X, Cₜ) ⟶ Hᵏ(X, f(N))` is an isomorphism, for coefficients in any abelian category.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3, proof of Theorem 3.43.
-/

public section

open CategoryTheory Limits Set

namespace TauCeti

universe w u v

variable {X : Type w} {N : Type*} [TopologicalSpace X] [TopologicalSpace N] {f : N → X}
  {c : N × Ico (0 : ℝ) 1 → X} {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C]

/-- **Cohomology relative to a collar of positive depth.** For a collar `c` of `f`, `0 < t`, and
`S = f(N) ⊆ T = c(N × [0, t))`, restriction `Hᵏ(X, T) ⟶ Hᵏ(X, S)` is an isomorphism, by the long
exact sequence of the triple `(X, T, S)`: the collar deforms `T` onto `S` relative to `S`. This is
the cohomology form of `TauCeti.IsCollar.isIso_localHomologyRestriction_compl_collarPart`. -/
theorem IsCollar.isIso_singularCohomologyMap_ofSubsetMap_collarPart (hc : IsCollar f c)
    {S T : Set (TopCat.of X)} (hST : S ⊆ T) (hS : S = range f) {t : ℝ} (ht : 0 < t)
    (hT : T = collarPart c t) (R : C) (k : Type*) [Ring k] [Linear k C] (M : C) (n : ℕ) :
    IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := M)
      (TopPair.ofSubsetMap (𝟙 (TopCat.of X)) hST) n) := by
  subst hS hT
  have hz (m : ℕ) := TopPair.isZero_singularCohomology_ofInclusion_of_homotopyRel hST _
    (hc.collarDeformation ht) R k M m
  have := TopTriple.isIso_singularCohomologyMap_totalToOuter_of_isZero
    (TopTriple.ofSubset (X := TopCat.of X) hST) R k M n (hz n) fun m _ ↦ hz m
  rwa [TopTriple.totalToOuter_app_ofSubset] at this

end TauCeti
