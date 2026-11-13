/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Cup.Basic
public import TauCeti.AlgebraicTopology.Cohomology.UniversalCoefficient
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.TopHomology

/-!
# The cohomology of a compact manifold vanishes above its dimension

Let `M` be a compact Hausdorff space modelled on a real normed space of finite dimension `n`, that
is, a compact topological `n`-manifold without boundary, and let `k` be a commutative ring over
which every module has projective dimension at most one, such as `ℤ` or any principal ideal
domain. For a projective coefficient module `R`, the singular homology `Hⱼ(M; R)` is projective for
every `j ≥ n` (`TauCeti.projective_singularHomology_of_compactSpace`) and zero for `j > n`. The
universal coefficient theorem therefore gives

`Hᵐ(M; R, N) = 0` for every `m > n` and every module `N`

(`TauCeti.isZero_singularCohomology_of_compactSpace`). In degree `n + 1` this is the vanishing of
the `Ext¹(Hₙ(M; R), N)` term, which needs the projectivity of the top homology: the vanishing of
homology above the dimension alone does not suffice. For `k = R = N = ℤ` and a closed
three-manifold `Y` this is `H⁴(Y; ℤ) = 0`.

Consequently, cup products of classes pulled back from `M` vanish in every degree above `n`
(`TauCeti.singularCup_singularCohomologyMap_eq_zero`): by naturality of the cup product
(`TopCat.singularCup_naturality`), `f^* a ⌣ f^* b = f^* (a ⌣ b)` lies in the image of
`Hᵖ⁺q(M) = 0`. For the projection `p : S¹ × Y → Y` of a product four-manifold onto a closed
three-manifold, this says that integral classes `e = p^* e_Y` and `κ = p^* κ_Y` pulled back from
`Y` satisfy `e ⌣ e = 0` and `κ ⌣ e = 0` in `H⁴(S¹ × Y; ℤ)` itself, not only modulo torsion.
In particular the Seiberg–Witten dimension `⟨e² - κ e, [S¹ × Y]⟩` of such a label is zero.

## Main results

* `TauCeti.isZero_singularCohomology_of_compactSpace`: `Hᵐ(M; R, N) = 0` for `m > n`.
* `TauCeti.singularCup_singularCohomologyMap_eq_zero`: the cup product of two classes pulled back
  from `M` along a continuous map vanishes when the sum of their degrees exceeds `n`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3, Lemma 3.27 and Theorem 3.26 (the top homology of a closed manifold), and
  Section 3.1, Theorem 3.2 (the universal coefficient theorem).
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory Module

universe w

namespace TauCeti

variable {k : Type w} [CommRing k] [∀ V : ModuleCat.{w} k, HasProjectiveDimensionLE V 1]
  {M E : Type w} [TopologicalSpace M] [T2Space M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [ChartedSpace E M] [CompactSpace M]

/-- **The cohomology of a compact manifold vanishes above its dimension.** Let `k` be a commutative
ring over which every module has projective dimension at most one, such as `ℤ`, and let `R` be a
projective `k`-module. For a compact Hausdorff space `M` modelled on a real normed space of finite
dimension `n`, `Hᵐ(M; R, N) = 0` for every `m > n` and every `k`-module `N`. For `k = R = N = ℤ`
and a closed three-manifold this is `H⁴(M; ℤ) = 0`. -/
theorem isZero_singularCohomology_of_compactSpace (R N : ModuleCat.{w} k) [Module.Projective k R]
    {n m : ℕ} (hn : finrank ℝ E = n) (hm : n < m) :
    IsZero ((TopCat.of M).singularCohomology R k N m) := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  have := projective_singularHomology_of_compactSpace R (M := M) hn (Nat.le_of_lt_succ hm)
  exact (TopCat.of M).isZero_singularCohomology_succ_of_projective_homology R N j
    (isZero_singularHomology_of_compactSpace R (M := M) hn (by omega))

/-- **Cup products of pulled-back classes vanish above the dimension.** Let `M` be a compact
Hausdorff space modelled on a real normed space of finite dimension `n`, and let `f : X ⟶ M` be a
continuous map. Over a commutative ring `k` over which every module has projective dimension at
most one, such as `ℤ`, with a projective coefficient module `T`, the cup product of the pullbacks
of two classes `α ∈ Hᵖ(M)` and `β ∈ H^q(M)` with `p + q > n` vanishes: it is the pullback of
`α ⌣ β ∈ H^(p+q)(M; T, P) = 0`. For the projection `S¹ × Y ⟶ Y` onto a closed three-manifold and
`p = q = 2`, the squares and products of integral classes pulled back from `Y` vanish in
`H⁴(S¹ × Y; ℤ)`. -/
theorem singularCup_singularCohomologyMap_eq_zero {X : TopCat.{w}} (f : X ⟶ TopCat.of M)
    {R S T A B P : ModuleCat.{w} k} [Module.Projective k T] (u : T ⟶ R ⊗ S) (μ : A ⊗ B ⟶ P)
    {n p q m : ℕ} (hn : finrank ℝ E = n) (h : p + q = m) (hm : n < m)
    (α : (TopCat.of M).singularCohomology R k A p) (β : (TopCat.of M).singularCohomology S k B q) :
    X.singularCup k u μ p q m h (TopCat.singularCohomologyMap f p α)
      (TopCat.singularCohomologyMap f q β) = 0 := by
  have := ModuleCat.subsingleton_of_isZero
    (isZero_singularCohomology_of_compactSpace (M := M) T P hn hm)
  rw [TopCat.singularCup_naturality, Subsingleton.elim ((TopCat.of M).singularCup k u μ p q m h α β)
    0, map_zero]

end TauCeti
