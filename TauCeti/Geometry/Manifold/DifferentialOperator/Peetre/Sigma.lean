/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialOperator.Peetre.Basic
public import TauCeti.Geometry.Manifold.DifferentialOperator.Sigma
public import TauCeti.Geometry.Manifold.VectorField.AddCircle

/-!
# Peetre's theorem gives no global order bound

Peetre's theorem bounds the order of a local operator only over compact sets. On the countable
disjoint union `Σ j : ℕ, AddCircle p` of circles, let `P` act by the `j`-th power `∂_t ^ j` of the
derivative on the `j`-th circle (`TauCeti.sigmaOperator`). It is local: `(P f) x = 0` when `f`
vanishes near `x`. A compact set meets only finitely many circles, and the order of `P` is bounded
over it, as Peetre's theorem (`LinearMap.exists_apply_eq_zero_of_mem_smoothVanishingIdeal_pow`)
asserts. But `∂_t ^ (r + 1)` does not have order at most `r`, so `P` is not a differential operator
of any finite order. The compactness hypothesis of
`LinearMap.exists_mem_differentialOperators_iff_apply_eq_zero_of_eventuallyEq`, which identifies
local operators with differential operators, therefore cannot be dropped.

## Main results

* `AddCircle.sigmaOperator_pow_timeDerivation_apply_eq_zero_of_eventuallyEq`: the operator acting
  by `∂_t ^ j` on the `j`-th of countably many circles is local.
* `AddCircle.exists_sigmaOperator_pow_timeDerivation_apply_eq_zero_of_mem_smoothVanishingIdeal_pow`:
  it has finite order over each compact set.
* `AddCircle.sigmaOperator_pow_timeDerivation_notMem_differentialOperators`: it has no finite
  order.

## References

* J. Peetre, *Réctification à l'article « Une caractérisation abstraite des opérateurs
  différentiels »*, Math. Scand. 8 (1960), 116–120.
* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer,
  1993, Theorem 19.1 (Peetre's theorem: local finite order over compact sets).
-/

public section

open Filter
open scoped ContDiff Manifold Topology

namespace AddCircle

open TauCeti

variable (p : ℝ) [Fact (0 < p)]

/-- On the disjoint union of countably many circles, the operator acting by `∂_t ^ j` on the
`j`-th circle is local. -/
theorem sigmaOperator_pow_timeDerivation_apply_eq_zero_of_eventuallyEq
    {f : C^∞⟮𝓘(ℝ), Σ _ : ℕ, AddCircle p; ℝ⟯} {x : Σ _ : ℕ, AddCircle p}
    (hf : (f : (Σ _ : ℕ, AddCircle p) → ℝ) =ᶠ[𝓝 x] 0) :
    sigmaOperator (fun j ↦ (timeDerivation p : Module.End ℝ C^∞⟮𝓘(ℝ), AddCircle p; ℝ⟯) ^ j) f
      x = 0 :=
  sigmaOperator_apply_eq_zero_of_eventuallyEq (fun j g y hg ↦ by
    simpa using differentialOperators_apply_eq_of_eventuallyEq
      (SetLike.pow_mem_graded j (timeDerivation p).mem_differentialOperators_one)
      BoundarylessManifold.isInteriorPoint (g := 0) hg) hf

/-- On the disjoint union of countably many circles, the operator acting by `∂_t ^ j` on the
`j`-th circle has finite order over every compact set `K`: for some `r`, its value at each point
`x ∈ K` vanishes on the `(r + 1)`-st power of the ideal of smooth functions vanishing at `x`. -/
theorem exists_sigmaOperator_pow_timeDerivation_apply_eq_zero_of_mem_smoothVanishingIdeal_pow
    {K : Set (Σ _ : ℕ, AddCircle p)} (hK : IsCompact K) :
    ∃ r : ℕ, ∀ x ∈ K, ∀ f ∈ smoothVanishingIdeal 𝓘(ℝ) x ^ (r + 1),
      sigmaOperator (fun j ↦ (timeDerivation p : Module.End ℝ C^∞⟮𝓘(ℝ), AddCircle p; ℝ⟯) ^ j) f
        x = 0 :=
  LinearMap.exists_apply_eq_zero_of_mem_smoothVanishingIdeal_pow
    (ContMDiffMap.coeFnLinearMap ∘ₗ
      sigmaOperator fun j ↦ (timeDerivation p : Module.End ℝ C^∞⟮𝓘(ℝ), AddCircle p; ℝ⟯) ^ j)
    isOpen_univ
    (fun _ _ _ hf ↦ sigmaOperator_pow_timeDerivation_apply_eq_zero_of_eventuallyEq p hf)
    (fun f ↦ (sigmaOperator _ f).contMDiff.continuous.continuousOn) hK (Set.subset_univ K)

/-- **Peetre's theorem gives no global order bound.** On the disjoint union of countably many
circles, the operator acting by `∂_t ^ j` on the `j`-th circle is not a differential operator of
any finite order `r`, since `∂_t ^ (r + 1)` does not have order at most `r`. -/
theorem sigmaOperator_pow_timeDerivation_notMem_differentialOperators (r : ℕ) :
    sigmaOperator (fun j ↦ (timeDerivation p : Module.End ℝ C^∞⟮𝓘(ℝ), AddCircle p; ℝ⟯) ^ j) ∉
      differentialOperators ℝ C^∞⟮𝓘(ℝ), Σ _ : ℕ, AddCircle p; ℝ⟯
        C^∞⟮𝓘(ℝ), Σ _ : ℕ, AddCircle p; ℝ⟯ C^∞⟮𝓘(ℝ), Σ _ : ℕ, AddCircle p; ℝ⟯ r :=
  fun h ↦ timeDerivation_ne_zero p <| (Derivation.pow_succ_mem_differentialOperators_iff _ r).1 <|
    sigmaOperator_mem_differentialOperators_iff.1 h (r + 1)

end AddCircle
