/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Coinduced.IndexTwo
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Corestriction.TrivialF2
public import TauCeti.RepresentationTheory.Homological.ContCohomology.HomologySequence

/-!
# The index-two exact sequence of restriction and corestriction

Let `U` be an open subgroup of index two in a profinite group `G`, and let `M` be a discrete
`G`-module killed by two. The coinduction unit and the trace form the short exact sequence
`0 → M → Coind_U^G M → M → 0` (`TauCeti.DiscreteCoind.indexTwoShortExact`). Shapiro's isomorphism
`Hⁿ(G, Coind_U^G M) ≅ Hⁿ(U, M)` turns the coefficient map of the unit into restriction and the
coefficient map of the trace into corestriction, so the long exact sequence of continuous
cohomology becomes

```text
⋯ → Hⁿ(G, M) --res--> Hⁿ(U, M) --cor--> Hⁿ(G, M) --δ--> Hⁿ⁺¹(G, M) --res--> Hⁿ⁺¹(U, M) → ⋯
```

in every degree, where `δ` is the connecting map of the coefficient sequence. This file proves
exactness at its three repeating nodes and specializes exactness at `Hⁿ(U, M)` to trivial `𝔽₂`
coefficients. On the explicit low-degree model, the degree-zero connecting map of the same
sequence sends `1 ∈ H⁰(G, 𝔽₂)` to the character of `G` with kernel `U`
(`TauCeti.ContCohomology.indexTwoShortExact_explicitDelta0`).

Index exactly two is needed: at index two the kernel of the trace on `Coind_U^G M` is the image
of the unit (`TauCeti.DiscreteCoind.trace_eq_zero_iff_exists_unit_of_index_two`), which fails at
larger index. For `S₃ ⊇ C₂` with trivial `𝔽₂` coefficients, restriction and corestriction in
degree one are both surjective, so the composite sequence cannot be exact at `H¹(C₂, 𝔽₂)`.

## Main results

* `TauCeti.ContinuousCohomology.exact_res_corestriction_of_index_two`: exactness at `Hⁿ(U, M)`,
  the image of restriction is the kernel of corestriction.
* `TauCeti.ContinuousCohomology.exact_corestriction_delta_of_index_two`: exactness at `Hⁿ(G, M)`,
  the image of corestriction is the kernel of `δ`.
* `TauCeti.ContinuousCohomology.exact_delta_res_of_index_two`: exactness at `Hⁿ⁺¹(G, M)`, the
  image of `δ` is the kernel of restriction.
* `TauCeti.exact_trivialF2ResMap_trivialF2CorMap_of_index_two`: exactness at `Hⁿ(U, 𝔽₂)` for
  trivial `𝔽₂` coefficients.

## References

* J. Kr. Arason, *Cohomologische Invarianten quadratischer Formen*, J. Algebra **36** (1975),
  448–491, the exact sequence of a quadratic extension.
* A. Kozlowski, *The Evens–Kahn formula for the total Stiefel–Whitney class*,
  Proc. Amer. Math. Soc. **91** (1984), 309–313, Lemma 2.4.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (1.3.2).
-/

public section

open CategoryTheory

namespace TauCeti.ContinuousCohomology

open TauCeti.ContCohomology

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] (U : Subgroup G) (hU : IsOpen (U : Set G))
  (M : Type u) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction G M] [ContinuousSMul G M]

/-- **Exactness at `Hⁿ(U, M)`** for an open subgroup `U` of index two and a discrete `G`-module
`M` killed by two: a class of `Hⁿ(U, M)` has zero corestriction exactly when it is a
restriction. -/
theorem exact_res_corestriction_of_index_two (hU2 : U.index = 2) (hM : ∀ m : M, 2 • m = 0)
    (n : ℕ) :
    letI : U.FiniteIndex := ⟨by omega⟩
    Function.Exact (res U (ofDiscreteModule ℤ G M) n) (corestriction U M hU n) := by
  let _ : U.FiniteIndex := ⟨by omega⟩
  rw [← coeffMap_unit_comp_shapiroMap, corestriction_def,
    ← shapiroIso_hom U (U.isClosed_of_isOpen hU)]
  have h := (DiscreteCoind.indexTwoShortExact G U M hU2 hU hM).longExact_exact₂ n
  simp only [DiscreteCoind.indexTwoShortExact_incl, DiscreteCoind.indexTwoShortExact_proj] at h
  exact (LinearEquiv.conj_exact_iff_exact _ _
    (shapiroIso U (U.isClosed_of_isOpen hU) M n).toContinuousLinearEquiv.toLinearEquiv).2 h

/-- **Exactness at `Hⁿ(G, M)`** for an open subgroup `U` of index two and a discrete `G`-module
`M` killed by two: a class of `Hⁿ(G, M)` is a corestriction exactly when the connecting map `δ`
of the coefficient sequence `0 → M → Coind_U^G M → M → 0` kills it. -/
theorem exact_corestriction_delta_of_index_two (hU2 : U.index = 2) (hM : ∀ m : M, 2 • m = 0)
    (n : ℕ) :
    letI : U.FiniteIndex := ⟨by omega⟩
    Function.Exact (corestriction U M hU n)
      ((DiscreteCoind.indexTwoShortExact G U M hU2 hU hM).delta n) := by
  let _ : U.FiniteIndex := ⟨by omega⟩
  rw [corestriction_def]
  have h := (DiscreteCoind.indexTwoShortExact G U M hU2 hU hM).longExact_exact₃ n
  simp only [DiscreteCoind.indexTwoShortExact_proj] at h
  exact (LinearEquiv.precomp_exact_iff_exact (e := (shapiroIso U (U.isClosed_of_isOpen hU) M
    n).symm.toContinuousLinearEquiv.toLinearEquiv)).2 h

/-- **Exactness at `Hⁿ⁺¹(G, M)`** for an open subgroup `U` of index two and a discrete `G`-module
`M` killed by two: a class of `Hⁿ⁺¹(G, M)` restricts to zero on `U` exactly when it is in the
image of the connecting map `δ` of the coefficient sequence `0 → M → Coind_U^G M → M → 0`. -/
theorem exact_delta_res_of_index_two (hU2 : U.index = 2) (hM : ∀ m : M, 2 • m = 0) (n : ℕ) :
    letI : U.FiniteIndex := ⟨by omega⟩
    Function.Exact ((DiscreteCoind.indexTwoShortExact G U M hU2 hU hM).delta n)
      (res U (ofDiscreteModule ℤ G M) (n + 1)) := by
  let _ : U.FiniteIndex := ⟨by omega⟩
  rw [← coeffMap_unit_comp_shapiroMap, ← shapiroIso_hom U (U.isClosed_of_isOpen hU)]
  have h := (DiscreteCoind.indexTwoShortExact G U M hU2 hU hM).longExact_exact₁ n
  simp only [DiscreteCoind.indexTwoShortExact_incl] at h
  exact (LinearEquiv.postcomp_exact_iff_exact (e := (shapiroIso U (U.isClosed_of_isOpen hU) M
    (n + 1)).toContinuousLinearEquiv.toLinearEquiv)).2 h

end TauCeti.ContinuousCohomology

namespace TauCeti

universe u

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]
  (U : Subgroup G) (hU : IsOpen (U : Set G))

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass continuousSMul_trivialF2

/-- **Exactness at `Hⁿ(U, 𝔽₂)`** for an open subgroup `U` of index two and trivial `𝔽₂`
coefficients: a class of `Hⁿ(U, 𝔽₂)` has zero corestriction exactly when it is a restriction. -/
theorem exact_trivialF2ResMap_trivialF2CorMap_of_index_two (hU2 : U.index = 2) (n : ℕ) :
    letI : U.FiniteIndex := ⟨by omega⟩
    Function.Exact (trivialF2ResMap G U n) (trivialF2CorMap G U hU n) := by
  let _ : U.FiniteIndex := ⟨by omega⟩
  -- Generalize the coefficient object over `G`, so that its identification with
  -- `ofDiscreteModule ℤ G (trivialF2 G).V` can be substituted away; the claim is then
  -- `exact_res_corestriction_of_index_two`. After restriction, `res_ofDiscreteModule` lands the
  -- transport in `continuousCohomology n (ofDiscreteModule ℤ U _)`, the domain of corestriction.
  have key : ∀ (X : TopRep ℤ G) (hX : ofDiscreteModule ℤ G (trivialF2 G).V = X),
      Function.Exact (ContinuousCohomology.res U X n ≫
          eqToHom ((congrArg (fun Z => continuousCohomology n (TopRep.res U.subtype Z))
            hX.symm).trans (congrArg (continuousCohomology n) (res_ofDiscreteModule (R := ℤ) U))))
        (ContinuousCohomology.corestriction U (trivialF2 G).V hU n ≫
          eqToHom (congrArg (continuousCohomology n) hX)) := by
    rintro X rfl
    simp only [eqToHom_refl, Category.comp_id]
    exact ContinuousCohomology.exact_res_corestriction_of_index_two U hU _ hU2
      (trivialF2_two_nsmul_eq_zero G) n
  -- Over `U`, the identification of `ofDiscreteModule ℤ U (trivialF2 G).V` with `trivialF2 U`
  -- replaces the middle object.
  have h := (LinearEquiv.conj_exact_iff_exact _ _ (eqToIso (congrArg (continuousCohomology n)
    (ofDiscreteModule_subgroup_trivialF2 G U))).toContinuousLinearEquiv.toLinearEquiv).2
    (key _ (ofDiscreteModule_trivialF2 G))
  -- The two `eqToHom`s after restriction meet at `continuousCohomology n (ofDiscreteModule ℤ U _)`
  -- and compose to the one in `trivialF2ResMap`.
  have hres : (ContinuousCohomology.res U (trivialF2 G) n ≫
        eqToHom ((congrArg (fun Z => continuousCohomology n (TopRep.res U.subtype Z))
          (ofDiscreteModule_trivialF2 G).symm).trans
            (congrArg (continuousCohomology n) (res_ofDiscreteModule (R := ℤ) U)))) ≫
      eqToHom (congrArg (continuousCohomology n) (ofDiscreteModule_subgroup_trivialF2 G U)) =
        trivialF2ResMap G U n := by
    rw [Category.assoc, eqToHom_trans, trivialF2ResMap_def]
  rw [← hres, trivialF2CorMap_def]
  exact h

end TauCeti
