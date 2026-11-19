/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ClassifyingSpace.FiniteCyclic
public import TauCeti.AlgebraicTopology.ClassifyingSpace.Prod
public import TauCeti.AlgebraicTopology.Cohomology.UniversalCoefficient.Field

/-!
# The mod `p` cohomology of the classifying space of `ℤ/p × ℤ/p`

Let `k` be a field and let `G` and `H` be finite cyclic groups whose orders vanish in `k`, for
instance two cyclic groups of order `p` and `k = 𝔽_p`. This file shows that the singular
cohomology of Milnor's classifying space `B(G × H)` with coefficients in `k` has dimension `d + 1`
in every degree `d` (`TauCeti.finrank_classifyingSpace_prod_singularCohomology_of_isCyclic`).

The dimension grows without bound, so `B(ℤ/p × ℤ/p)` has nonzero mod `p` cohomology in every
degree. This is what forbids free actions of `ℤ/p × ℤ/p` on spheres: the quotient of such an
action would lead to a model of `B(ℤ/p × ℤ/p)` whose mod `p` cohomology is at most one-dimensional
in some degree `n + 1`, while it is `n + 2`-dimensional.

The computation goes through homology. Over a field, cohomology and homology have the same
dimension in every degree (`TopCat.finrank_singularCohomology`), and `Hᵢ(BG; k)` is
one-dimensional for every `i` by the homology of a finite cyclic group
(`TauCeti.finrank_classifyingSpace_singularHomology_of_natCast_card_eq_zero`). The comparison map
`B(G × H) ⟶ BG × BH` induces isomorphisms on homology
(`TauCeti.isIso_singularHomologyMap_classifyingSpaceProdMap`), and the Künneth formula
(`TopCat.finrank_singularHomology_tensor`) gives
`dim H_d(BG × BH; k) = ∑_{a + b = d} dim Hₐ(BG; k) · dim H_b(BH; k) = d + 1`.

## Main results

* `TauCeti.finrank_classifyingSpace_prod_singularCohomology_of_isCyclic`: if the orders of the
  finite cyclic groups `G` and `H` vanish in `k`, then `H^d(B(G × H); k)` has dimension `d + 1`;
  for instance for `G = H = ℤ/p` and `k = 𝔽_p`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.B (the Künneth
  formula), and Section 4.2, Exercise 28 (free actions of `ℤ/p × ℤ/p` on spheres).
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory AlgebraicTopology

universe u

namespace TauCeti

variable (k : Type u) [Field k]

/-- Over a field in which the order of a finite cyclic group `G` vanishes, the homology of `BG`
with coefficients in the monoidal unit is finite-dimensional in every degree. -/
private lemma finite_classifyingSpace_singularHomology_unit {G : Type u} [Group G] [Finite G]
    [IsCyclic G] (hG : (Nat.card G : k) = 0) (i : ℕ) :
    Module.Finite k (((singularHomologyFunctor (ModuleCat.{u} k) i).obj
      (𝟙_ (ModuleCat.{u} k))).obj (TopCat.of (classifyingSpace G))) :=
  -- The monoidal unit of `ModuleCat k` is `ModuleCat.of k k`, and the homology functor applied to
  -- it is the homology of `singularChains k`, both by definition.
  Module.finite_of_finrank_eq_succ
    (finrank_classifyingSpace_singularHomology_of_natCast_card_eq_zero k hG i)

/-- **The cohomology of `B(G × H)` for finite cyclic groups `G` and `H` with coefficients in a
field of characteristic dividing both orders.** If the orders of `G` and `H` vanish in the field
`k`, then `H^d(B(G × H); k)` has dimension `d + 1` for every `d`. For `G = H = ℤ/p` and
`k = ZMod p`, `p` prime, this is the mod `p` cohomology of `B(ℤ/p × ℤ/p)`. -/
theorem finrank_classifyingSpace_prod_singularCohomology_of_isCyclic {G H : Type u} [Group G]
    [Finite G] [IsCyclic G] [Group H] [Finite H] [IsCyclic H] (hG : (Nat.card G : k) = 0)
    (hH : (Nat.card H : k) = 0) (d : ℕ) :
    Module.finrank k ((TopCat.of (classifyingSpace (G × H))).singularCohomology
      (ModuleCat.of k k) k (ModuleCat.of k k) d) = d + 1 := by
  have := finite_classifyingSpace_singularHomology_unit k hG
  have := finite_classifyingSpace_singularHomology_unit k hH
  have : Module.Projective k (𝟙_ (ModuleCat.{u} k)) :=
    have := Module.Free.of_divisionRing k (𝟙_ (ModuleCat.{u} k))
    Module.Projective.of_free
  -- The comparison map `B(G × H) ⟶ BG × BH`, followed by the left unitor `𝟙_ ⊗ 𝟙_ ≅ 𝟙_` of the
  -- coefficients. Its composition uses that the monoidal unit of `ModuleCat k` is
  -- `ModuleCat.of k k` by definition. `isIso_singularHomologyMap_classifyingSpaceProdMap` is a
  -- theorem rather than an instance, so it is supplied to `asIso` explicitly.
  have e : ((singularHomologyFunctor (ModuleCat.{u} k) d).obj (ModuleCat.of k k)).obj
        (TopCat.of (classifyingSpace (G × H))) ≅
      ((singularHomologyFunctor (ModuleCat.{u} k) d).obj
        (𝟙_ (ModuleCat.{u} k) ⊗ 𝟙_ (ModuleCat.{u} k))).obj
        (TopCat.of (classifyingSpace G) ⊗ TopCat.of (classifyingSpace H)) :=
    @asIso _ _ _ _ _ (isIso_singularHomologyMap_classifyingSpaceProdMap G H k d) ≪≫
      (((singularHomologyFunctor (ModuleCat.{u} k) d).mapIso
        (λ_ (𝟙_ (ModuleCat.{u} k)))).app _).symm
  rw [TopCat.finrank_singularCohomology, e.toLinearEquiv.finrank_eq,
    TopCat.finrank_singularHomology_tensor]
  -- Each summand `dim Hₐ(BG; k) · dim H_b(BH; k)` is `1 · 1`, again because the monoidal unit is
  -- `ModuleCat.of k k` by definition; the antidiagonal of `d` has `d + 1` elements.
  rw [Finset.sum_congr rfl fun x _ ↦ (congrArg₂ (· * ·)
    (finrank_classifyingSpace_singularHomology_of_natCast_card_eq_zero k hG x.1)
    (finrank_classifyingSpace_singularHomology_of_natCast_card_eq_zero k hH x.2)).trans
      (one_mul 1)]
  simp

end TauCeti
