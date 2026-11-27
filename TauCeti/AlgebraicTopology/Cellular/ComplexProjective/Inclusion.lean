/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.ComplexProjective.Basic
public import TauCeti.AlgebraicTopology.Cellular.Comparison
public import TauCeti.Topology.ComplexProjectiveSpace.Inclusion

/-!
# The inclusion `CPⁿ ⊆ CPⁿ⁺¹` on singular homology

`CPⁿ` is the `(2n + 1)`-skeleton of `CPⁿ⁺¹`, which has a single further cell, of dimension
`2n + 2` (`TauCeti.ComplexProjectiveSpace.skeletonLT_eq_range_inclusion`,
`TauCeti.ComplexProjectiveSpace.skeletonLT_cwComplex_eq_univ`). Attaching it leaves homology
unchanged below degree `2n + 1` (`TauCeti.isIso_singularHomologyMap_of_range_eq_skeletonLT`), and
in degree `2n + 1` both homology groups vanish. So the inclusion induces isomorphisms
`Hₖ(CPⁿ; R) ≅ Hₖ(CPⁿ⁺¹; R)` for every `k ≠ 2n + 2`, with coefficients in any abelian category
with coproducts (`TauCeti.ComplexProjectiveSpace.isIso_singularHomologyMap_inclusion`).

These degreewise isomorphisms are the input for computing the homology of `CP∞` as a colimit,
which is not done here.

## Main results

* `TauCeti.ComplexProjectiveSpace.isIso_singularHomologyMap_inclusion`: `Hₖ(CPⁿ) ≅ Hₖ(CPⁿ⁺¹)` for
  `k ≠ 2n + 2`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Chapter 0, Example 0.6, and Section 2.2, Lemma 2.34.
-/

public section

noncomputable section

open CategoryTheory Limits Set Topology Topology.RelCWComplex

universe v u

namespace TauCeti.ComplexProjectiveSpace

attribute [local instance] cwComplex Abelian.hasFiniteBiproducts

variable {n : ℕ} {A : Type u} [Category.{v} A] [HasCoproducts.{0} A] [Abelian A] (R : A)

/-- **`Hₖ(CPⁿ) ≅ Hₖ(CPⁿ⁺¹)` for `k ≠ 2n + 2`.** The inclusion `CPⁿ → CPⁿ⁺¹` induces an
isomorphism on singular homology in every degree other than `2n + 2`, with coefficients in any
abelian category with coproducts: `CPⁿ⁺¹` is `CPⁿ` with one cell of dimension `2n + 2` attached.
In degree `2n + 1` both groups vanish. -/
theorem isIso_singularHomologyMap_inclusion {k : ℕ} (hk : k ≠ 2 * n + 2) :
    IsIso (((AlgebraicTopology.singularHomologyFunctor A k).obj R).map
      (TopCat.ofHom (inclusion n))) := by
  by_cases hk' : k = 2 * n + 1
  · -- In the odd degree `2n + 1` both homology groups vanish.
    have hX := isZero_singularHomology_of_odd (n := n) R (k := k) ⟨n, hk'⟩
    have hY := isZero_singularHomology_of_odd (n := n + 1) R (k := k) ⟨n, hk'⟩
    exact ⟨hY.to_ _, hX.eq_of_src _ _, hY.eq_of_src _ _⟩
  exact isIso_singularHomologyMap_of_range_eq_skeletonLT
    (univ : Set (ComplexProjectiveSpace (n + 1))) R (isClosedEmbedding_inclusion n).isEmbedding
    (skeletonLT_eq_range_inclusion n).symm
    (skeletonLT_cwComplex_eq_univ n) hk (by omega)

end TauCeti.ComplexProjectiveSpace
