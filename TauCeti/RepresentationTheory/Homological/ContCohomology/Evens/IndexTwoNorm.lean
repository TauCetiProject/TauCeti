/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Evens.Class

/-!
# The index-two Evens norm on degree-one classes

With trivial `𝔽₂` coefficients, continuous first cohomology is the group of continuous
homomorphisms to `𝔽₂`: a continuous `1`-cocycle for the trivial action is a homomorphism, and
there are no nonzero coboundaries. This file names the class `homClass H α` of a continuous
homomorphism `α : H → 𝔽₂` in Mathlib's `continuousCohomology 1 (trivialF2 H)`, identifies it with
the `TopRep.cochainClass` of the homogeneous cochain of `α`, and shows that `homClass` is a
bijection from continuous homomorphisms onto degree-one classes.

For an open subgroup `U` of index two in `G`, the graph class
`TauCeti.ContCohomology.graphClass U hU α` of `Evens/Class.lean` is a function of a continuous
homomorphism `α : U → 𝔽₂`. Through `homClass` it descends to the index-two degree-one Evens norm
```
Nᴱᵛ : H¹(U, 𝔽₂) → H²(G, 𝔽₂),
```
`evensNormIndexTwo`, whose defining equation is `evensNormIndexTwo_homClass`. The norm is a
function and not an additive map.

## Main definitions

* `TauCeti.ContCohomology.homClass`: the class of a continuous homomorphism to `𝔽₂`.
* `TauCeti.ContCohomology.evensNormIndexTwo`: the index-two degree-one Evens norm.

## Main results

* `TauCeti.ContCohomology.homClass_eq_cochainClass`: `homClass` is the class of the homogeneous
  cochain `inhomogeneousCochain1` of the homomorphism.
* `TauCeti.ContCohomology.homClass_surjective`: every degree-one class is the class of a continuous
  homomorphism.
* `TauCeti.ContCohomology.homClass_inj`: two continuous homomorphisms have the same class exactly
  when they are equal.
* `TauCeti.ContCohomology.graphClass_representative_independent`: the graph class depends only on
  the class of the homomorphism.
* `TauCeti.ContCohomology.evensNormIndexTwo_homClass`: the norm of the class of a homomorphism is
  its graph class.

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*, Trans. Amer.
  Math. Soc. **108** (1963), 54–65.
* A. Kozlowski, *The Evens–Kahn formula for the total Stiefel–Whitney class*, Proc. Amer. Math.
  Soc. **91** (1984), 309–313, Lemma 2.4.
-/

public section

open CategoryTheory

namespace TauCeti.ContCohomology

universe u

section HomClass

variable (H : Type u) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

attribute [local instance] TopRep.distribMulAction

/-- `H` acts continuously on the trivial coefficients `𝔽₂`, which are smooth discrete. -/
local instance : ContinuousSMul H (trivialF2 H).V :=
  (isSmoothDiscrete_trivialF2 H).continuousSMul

/-- The class of a continuous homomorphism `α : H → 𝔽₂` in `continuousCohomology 1 (trivialF2 H)`:
the explicit class of `α`, read as a continuous `1`-cocycle for the trivial action, carried to the
canonical object by the degree-one comparison. `homClass_eq_cochainClass` identifies it with the
class of the homogeneous cochain of `α`. -/
noncomputable def homClass (α : H →* Multiplicative (ZMod 2)) (hα : Continuous α) :
    continuousCohomology 1 (trivialF2 H) :=
  (eqToHom (congrArg (continuousCohomology 1) (ofDiscreteModule_trivialF2 H))).hom
    (explicitH1AddEquivContinuousCohomology H (trivialF2 H).V (evensHomCocycle α hα))

/-- `homClass` is the degree-one comparison applied to the explicit class of the homomorphism. -/
theorem homClass_def (α : H →* Multiplicative (ZMod 2)) (hα : Continuous α) :
    homClass H α hα =
      (eqToHom (congrArg (continuousCohomology 1) (ofDiscreteModule_trivialF2 H))).hom
        (explicitH1AddEquivContinuousCohomology H (trivialF2 H).V (evensHomCocycle α hα)) :=
  (rfl)

/-- **The class of a continuous homomorphism is the class of its cochain:** `homClass H α` is the
`TopRep.cochainClass` of the homogeneous cochain `(h₀, h₁) ↦ α (h₀⁻¹ * h₁)`, read additively. -/
theorem homClass_eq_cochainClass (α : H →* Multiplicative (ZMod 2)) (hα : Continuous α) :
    homClass H α hα =
      (trivialF2 H).cochainClass 1
        (inhomogeneousCochain1 (fun h => Multiplicative.toAdd (α h)) (continuous_toAdd.comp hα))
        (inhomogeneousCochain1_d_eq_zero _ _ fun g h => by simp [map_mul, toAdd_mul]) :=
  eqToHom_explicitH1AddEquivContinuousCohomology_eq_cochainClass _ _ _
    (fun h => by rw [coe_evensHomCocycle]) _

/-- **Every degree-one class is the class of a continuous homomorphism.** With trivial `𝔽₂`
coefficients the continuous `1`-cocycles are the continuous homomorphisms and there are no nonzero
coboundaries, so `H¹(H, 𝔽₂)` is the group of continuous homomorphisms `H → 𝔽₂`. -/
theorem homClass_surjective (x : continuousCohomology 1 (trivialF2 H)) :
    ∃ (α : H →* Multiplicative (ZMod 2)) (hα : Continuous α), homClass H α hα = x := by
  have htriv (g : H) (m : (trivialF2 H).V) : g • m = m := by
    rw [TopRep.distribMulAction_smul, trivialF2_ρ_apply_apply]
  let φ := Additive.toMul (H1EquivOfSmulEqSelf htriv
    ((explicitH1AddEquivContinuousCohomology H (trivialF2 H).V).symm
      ((eqToHom (congrArg (continuousCohomology 1) (ofDiscreteModule_trivialF2 H).symm)).hom x)))
  let α : H →* Multiplicative (ZMod 2) :=
    (trivialF2Equiv H).toMultiplicative.toMonoidHom.comp φ.toMonoidHom
  have hα : Continuous α :=
    (continuous_of_discreteTopology : Continuous (trivialF2Equiv H).toMultiplicative).comp
      φ.continuous
  refine ⟨α, hα, ?_⟩
  have hφ : (evensHomCocycle α hα : H1 H (trivialF2 H).V) =
      (explicitH1AddEquivContinuousCohomology H (trivialF2 H).V).symm
        ((eqToHom (congrArg (continuousCohomology 1) (ofDiscreteModule_trivialF2 H).symm)).hom
          x) := by
    apply (H1EquivOfSmulEqSelf htriv).injective
    rw [H1EquivOfSmulEqSelf_mk]
    apply Additive.toMul.injective
    ext h
    simp [α, φ, Z1EquivOfSmulEqSelf_apply]
  rw [homClass_def, hφ, AddEquiv.apply_symm_apply, ← ConcreteCategory.comp_apply, eqToHom_trans,
    eqToHom_refl, ConcreteCategory.id_apply]

/-- **Two continuous homomorphisms have the same class exactly when they are equal.** With
trivial `𝔽₂` coefficients there are no nonzero degree-one coboundaries. -/
@[simp]
theorem homClass_inj {α β : H →* Multiplicative (ZMod 2)} (hα : Continuous α)
    (hβ : Continuous β) : homClass H α hα = homClass H β hβ ↔ α = β := by
  refine ⟨fun hcl => ?_, fun h => by subst h; rfl⟩
  have htriv (g : H) (m : (trivialF2 H).V) : g • m = m := by
    rw [TopRep.distribMulAction_smul, trivialF2_ρ_apply_apply]
  rw [homClass_def, homClass_def] at hcl
  have hexpl := (explicitH1AddEquivContinuousCohomology H (trivialF2 H).V).injective
    ((ConcreteCategory.bijective_of_isIso
      (eqToHom (congrArg (continuousCohomology 1) (ofDiscreteModule_trivialF2 H)))).injective hcl)
  have hchar := congrArg (fun z => Additive.toMul (H1EquivOfSmulEqSelf htriv z)) hexpl
  ext h
  simpa only [H1EquivOfSmulEqSelf_mk, Z1EquivOfSmulEqSelf_apply, coe_evensHomCocycle,
    EmbeddingLike.apply_eq_iff_eq] using DFunLike.congr_fun hchar h

end HomClass

section EvensNorm

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]

/-- **The graph class depends only on the class of the homomorphism:** continuous homomorphisms
`U → 𝔽₂` with the same class in `H¹(U, 𝔽₂)` have the same graph class. This is what makes
`graphClass` a function on `H¹(U, 𝔽₂)`. -/
theorem graphClass_representative_independent (U : OpenSubgroup G)
    (hU : U.toSubgroup.index = 2) (α β : U.toSubgroup →* Multiplicative (ZMod 2))
    (hα : Continuous α) (hβ : Continuous β)
    (hcl : homClass U.toSubgroup α hα = homClass U.toSubgroup β hβ) :
    graphClass U hU α hα = graphClass U hU β hβ := by
  obtain rfl := (homClass_inj U.toSubgroup hα hβ).1 hcl
  rfl

/-- **The index-two degree-one Evens norm** `Nᴱᵛ : H¹(U, 𝔽₂) → H²(G, 𝔽₂)` for an open subgroup
`U` of index two: the graph class of a continuous homomorphism representing the class, which
`homClass_surjective` provides and `graphClass_representative_independent` makes irrelevant. On
the class of `α` it is `graphClass U hU α` (`evensNormIndexTwo_homClass`). It is a function and not
an additive map. -/
noncomputable def evensNormIndexTwo (U : OpenSubgroup G) (hU : U.toSubgroup.index = 2)
    (x : continuousCohomology 1 (trivialF2 U.toSubgroup)) :
    continuousCohomology 2 (trivialF2 G) :=
  graphClass U hU (homClass_surjective U.toSubgroup x).choose
    (homClass_surjective U.toSubgroup x).choose_spec.choose

/-- **The defining equation of the index-two norm:** on the class of a continuous homomorphism it
is the graph class. -/
@[simp]
theorem evensNormIndexTwo_homClass (U : OpenSubgroup G) (hU : U.toSubgroup.index = 2)
    (α : U.toSubgroup →* Multiplicative (ZMod 2)) (hα : Continuous α) :
    evensNormIndexTwo U hU (homClass U.toSubgroup α hα) = graphClass U hU α hα :=
  graphClass_representative_independent U hU _ α _ hα
    (homClass_surjective U.toSubgroup _).choose_spec.choose_spec

end EvensNorm

end TauCeti.ContCohomology
