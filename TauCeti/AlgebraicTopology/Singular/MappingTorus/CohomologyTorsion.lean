/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Ext.QuotientRange
public import TauCeti.Algebra.Module.Torsion.Basic
public import TauCeti.AlgebraicTopology.Cohomology.UniversalCoefficient.Torsion
public import TauCeti.AlgebraicTopology.Singular.MappingTorus.Wang
public import Mathlib.RingTheory.Ideal.Int

/-!
# The torsion of the second cohomology of a mapping torus

Let `φ : F ≃ₜ F` be a homeomorphism and `T_φ` its mapping torus, with singular homology taken
with coefficients in a commutative ring `k`. The Wang sequence

  `Hₙ₊₁(F) ⟶ Hₙ₊₁(F) ⟶ Hₙ₊₁(T_φ) ⟶ Hₙ(F) ⟶ Hₙ(F)`,

with maps `𝟙 - φ_*`, the fibre inclusion and the Wang connecting morphism `δ`, gives a short
exact sequence

  `0 ⟶ Hₙ₊₁(F) ⧸ range (𝟙 - φ_*) ⟶ Hₙ₊₁(T_φ) ⟶ Hₙ(F) ⟶ 0`

whenever `δ` is onto (`TauCeti.MappingTorus.wangCokernelShortComplex_shortExact`, in
`TauCeti.AlgebraicTopology.Singular.MappingTorus.Wang`), as it is in degree `n = 0` for a
path-connected fibre. If moreover `Hₙ(F)` is projective, restriction to the
cokernel of `𝟙 - φ_*` is an isomorphism

  `Ext¹(Hₙ₊₁(T_φ), Y) ≃ Ext¹(Hₙ₊₁(F) ⧸ range (𝟙 - φ_*), Y)`

for every module `Y` (`TauCeti.MappingTorus.extOneHomologySuccEquiv`). In degree `n = 0`, `H₀(F)`
is free, so this holds for every path-connected `F` with no further hypothesis.

Now let `k` be a principal ideal domain, let `F` be path-connected, let `H₁(F; k)` be free of
finite rank, and suppose `det (𝟙 - φ_*) ≠ 0` on it. The presentation
`0 → H₁(F) → H₁(F) → H₁(F) ⧸ range (𝟙 - φ_*) → 0` computes `Ext¹` of the cokernel as the
cokernel of the transpose of `𝟙 - φ_*` (`LinearMap.extOneQuotientRangeEquiv`), a torsion module
of the cardinality of `k ⧸ (det (𝟙 - φ_*))`. By the universal coefficient theorem the torsion of
`H²(T_φ; k)` is the image of `Ext¹(H₁(T_φ; k), k)`
(`TopCat.torsion_singularCohomology_eq_range_singularExtToCohomology`). Hence the torsion
submodule of `H²(T_φ; k)` has the cardinality of `k ⧸ (det (𝟙 - φ_*))`
(`TauCeti.MappingTorus.card_torsion_cohomology_two_eq_card_quotient_span_det`), and over `ℤ` it is
finite of order `|det (1 - φ_*)|`
(`TauCeti.MappingTorus.card_torsion_cohomology_two_eq_natAbs_det`).

For a closed connected oriented surface `F` and `φ_*` without eigenvalue one on `H₁(F; ℤ)`, so
that `b₁(Y_φ) = 1`, this counts the torsion classes in `H²(Y_φ; ℤ)`: modulo torsion
`H²(Y_φ; ℤ)` has rank one, and each of its classes has exactly `|det (1 - φ_*)|` integral lifts.
The same number is the order of the torsion of `H₁(Y_φ; ℤ)`
(`TauCeti.MappingTorus.card_torsion_homology_one_eq_natAbs_det`).

## Main results

* `TauCeti.MappingTorus.extOneHomologySuccEquiv`: `Ext¹(Hₙ₊₁(T_φ), Y)` is `Ext¹` of the cokernel
  of `𝟙 - φ_*` when moreover `Hₙ(F)` is projective.
* `TauCeti.MappingTorus.card_torsion_cohomology_two_eq_card_quotient_span_det`: the torsion of
  `H²(T_φ; k)` has the cardinality of `k ⧸ (det (𝟙 - φ_*))`.
* `TauCeti.MappingTorus.card_torsion_cohomology_two_eq_natAbs_det`: over `ℤ` its order is
  `|det (1 - φ_*)|`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.2, Example 2.48 (the Wang sequence of a mapping torus), and Section 3.1,
  Theorem 3.2 and Corollary 3.3 (the universal coefficient theorem).
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology HomologicalComplex Abelian

universe w

namespace TauCeti.MappingTorus

variable {k : Type w} [CommRing k] {F : Type w} [TopologicalSpace F] (φ : F ≃ₜ F)

/-- **`Ext¹` of the homology of a mapping torus.** If the Wang connecting morphism
`Hₙ₊₁(T_φ) ⟶ Hₙ(F)` is onto and `Hₙ(F)` is projective, restriction along the fibre inclusion is
an isomorphism `Ext¹(Hₙ₊₁(T_φ), Y) ≃ Ext¹(Hₙ₊₁(F) ⧸ range (𝟙 - φ_*), Y)`, for every module `Y`.
In degree `n = 0` both hypotheses hold when `F` is path-connected. -/
def extOneHomologySuccEquiv (n : ℕ) [Epi (wangδ φ (ModuleCat.of k k) n)]
    [Projective ((((singularChainComplexFunctor (ModuleCat.{w} k)).obj (ModuleCat.of k k)).obj
      (TopCat.of F)).homology n)] (Y : ModuleCat.{w} k) :
    Ext.{w} ((((singularChainComplexFunctor (ModuleCat.{w} k)).obj (ModuleCat.of k k)).obj
        (TopCat.of (MappingTorus φ))).homology (n + 1)) Y 1 ≃ₗ[k]
      Ext.{w} (ModuleCat.of k ((((singularChainComplexFunctor (ModuleCat.{w} k)).obj
        (ModuleCat.of k k)).obj (TopCat.of F)).homology (n + 1) ⧸ LinearMap.range
          (LinearMap.id - (homologyMap (monodromyChainMap φ (ModuleCat.of k k)) (n + 1)).hom)))
        Y 1 :=
  -- the third object of `wangCokernelShortComplex φ n` is by definition `Hₙ(F)`
  have : Projective (wangCokernelShortComplex (k := k) φ n).X₃ := ‹_›
  LinearEquiv.ofBijective (Ext.precompOfLinear (Ext.mk₀ (wangCokernelShortComplex φ n).f) k Y
    (zero_add 1))
    ((wangCokernelShortComplex_shortExact φ n).precomp_mk₀_f_bijective_of_projective Y 0)

/-- The isomorphism `TauCeti.MappingTorus.extOneHomologySuccEquiv` is precomposition with the
first map of the Wang short complex. -/
@[simp]
theorem extOneHomologySuccEquiv_apply (n : ℕ) [Epi (wangδ φ (ModuleCat.of k k) n)]
    [Projective ((((singularChainComplexFunctor (ModuleCat.{w} k)).obj (ModuleCat.of k k)).obj
      (TopCat.of F)).homology n)] (Y : ModuleCat.{w} k)
    (e : Ext.{w} ((((singularChainComplexFunctor (ModuleCat.{w} k)).obj (ModuleCat.of k k)).obj
        (TopCat.of (MappingTorus φ))).homology (n + 1)) Y 1) :
    extOneHomologySuccEquiv φ n Y e =
      (Ext.mk₀ (wangCokernelShortComplex φ n).f).comp e (zero_add 1) :=
  (rfl)

variable [IsDomain k] [IsPrincipalIdealRing k] [PathConnectedSpace F]
  [Module.Free k ((((singularChainComplexFunctor (ModuleCat.{w} k)).obj
    (ModuleCat.of k k)).obj (TopCat.of F)).homology 1)]
  [Module.Finite k ((((singularChainComplexFunctor (ModuleCat.{w} k)).obj
    (ModuleCat.of k k)).obj (TopCat.of F)).homology 1)]

/-- **The torsion of the second cohomology of a mapping torus** over a principal ideal domain: if
`F` is path-connected, `H₁(F; k)` is free of finite rank and `det (𝟙 - φ_*) ≠ 0` on it, the
torsion submodule of `H²(T_φ; k)` has the same `Nat.card` as `k ⧸ (det (𝟙 - φ_*))`. Both sides
are `0` when these modules are infinite. -/
theorem card_torsion_cohomology_two_eq_card_quotient_span_det
    (hdet : (LinearMap.id -
      (homologyMap (monodromyChainMap φ (ModuleCat.of k k)) 1).hom).det ≠ 0) :
    Nat.card (Submodule.torsion k ((TopCat.of (MappingTorus φ)).singularCohomology
        (ModuleCat.of k k) k (ModuleCat.of k k) 2)) =
      Nat.card (k ⧸ Ideal.span {(LinearMap.id -
        (homologyMap (monodromyChainMap φ (ModuleCat.of k k)) 1).hom).det}) := by
  have : Projective ((((singularChainComplexFunctor (ModuleCat.{w} k)).obj
      (ModuleCat.of k k)).obj (TopCat.of F)).homology 0) :=
    ModuleCat.projective_of_free (Module.Free.chooseBasis k _)
  let e := extOneHomologySuccEquiv φ 0 (ModuleCat.of k k)
  have htors : Module.IsTorsion k (Ext.{w} ((((singularChainComplexFunctor (ModuleCat.{w} k)).obj
      (ModuleCat.of k k)).obj (TopCat.of (MappingTorus φ))).homology 1) (ModuleCat.of k k) 1) :=
    (LinearMap.isTorsion_ext_quotient_range (mem_nonZeroDivisors_of_ne_zero hdet)).of_injective
      (f := e.toLinearMap) e.injective
  -- `singularHomologyFunctor` is by definition the homology of the singular chain complex, and
  -- the source `Hₙ₊₁(T_φ)` of `e` at `n = 0` is by definition `H₁(T_φ)`, so `htors` and `e` apply
  -- to the `H₁(T_φ)` of the universal coefficient theorem
  exact ((TopCat.card_torsion_singularCohomology_eq_card_ext (n := 1) htors).trans
    (Nat.card_congr e.toEquiv)).trans
    (LinearMap.card_ext_one_quotient_range_eq_card_quotient_span_det hdet)

section Int

/- Integral cohomology is taken with the `ℤ`-linear structure `ModuleCat.instLinear` of
`ModuleCat ℤ`, the one the universal coefficient theorem is stated with for a general ring, rather
than the structure `Linear.preadditiveIntLinear` of an arbitrary preadditive category. -/
attribute [local instance high] ModuleCat.instLinear

/-- **The order of the torsion of the second cohomology of a mapping torus.** If `F` is
path-connected, `H₁(F; ℤ)` is free of finite rank and `det (1 - φ_*) ≠ 0` on it, the torsion
subgroup of `H²(T_φ; ℤ)` has order `|det (1 - φ_*)|`. -/
theorem card_torsion_cohomology_two_eq_natAbs_det {F : Type} [TopologicalSpace F]
    [PathConnectedSpace F] (φ : F ≃ₜ F)
    [Module.Free ℤ ((((singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
      (ModuleCat.of ℤ ℤ)).obj (TopCat.of F)).homology 1)]
    [Module.Finite ℤ ((((singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
      (ModuleCat.of ℤ ℤ)).obj (TopCat.of F)).homology 1)]
    (hdet : (LinearMap.id -
      (homologyMap (monodromyChainMap φ (ModuleCat.of ℤ ℤ)) 1).hom).det ≠ 0) :
    Nat.card (Submodule.torsion ℤ ((TopCat.of (MappingTorus φ)).singularCohomology
        (ModuleCat.of ℤ ℤ) ℤ (ModuleCat.of ℤ ℤ) 2)) =
      (LinearMap.id - (homologyMap (monodromyChainMap φ (ModuleCat.of ℤ ℤ)) 1).hom).det.natAbs := by
  rw [card_torsion_cohomology_two_eq_card_quotient_span_det φ hdet, ← Int.span_natAbs,
    Int.card_ideal_quot]

end Int

end TauCeti.MappingTorus
