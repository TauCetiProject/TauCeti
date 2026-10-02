/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Evens.Class

/-!
# The index-two Evens norm on degree-one classes

For trivial `𝔽₂` coefficients, continuous first cohomology is the group of continuous
homomorphisms to `𝔽₂`. This file identifies a homomorphism with its canonical cohomology class and
uses that identification to descend the choice-free graph class of
`TauCeti.ContCohomology.graphClass` to a function

```text
Nᴱᵛ : H¹(U, 𝔽₂) → H²(G, 𝔽₂)
```

when `U` is an open subgroup of index two. The norm is deliberately a plain function: its
polarization, rather than additivity, is one of its characteristic identities.

## Main definitions

* `TauCeti.ContCohomology.homClass`: the canonical class of a continuous homomorphism to `𝔽₂`.
* `TauCeti.ContCohomology.evensNormIndexTwo`: the graph class descended to canonical `H¹`.

## Main results

* `TauCeti.ContCohomology.homClass_surjective`: every canonical degree-one class has a continuous
  homomorphism representative.
* `TauCeti.ContCohomology.homClass_eq_iff`: two continuous homomorphisms determine the same class
  exactly when they are equal.
* `TauCeti.ContCohomology.graphClass_representative_independent`: the graph class depends only on
  the canonical degree-one class.
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

variable {H G : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

local instance continuousSMul_trivialF2_norm (K : Type u) [Group K] [TopologicalSpace K] :
    ContinuousSMul K (trivialF2 K).V where
  continuous_smul := by
    simpa only [TopRep.distribMulAction_smul, trivialF2_ρ_apply_apply] using
      (continuous_snd : Continuous (fun p : K × (trivialF2 K).V => p.2))

/-- The canonical continuous-cohomology class of a continuous homomorphism to `𝔽₂`.

The representative is first read as a continuous inhomogeneous cocycle, then carried to Mathlib's
canonical homogeneous complex by the degree-one comparison. -/
noncomputable def homClass (H : Type u) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (α : H →* Multiplicative (ZMod 2)) (hα : Continuous α) :
    continuousCohomology 1 (trivialF2 H) :=
  (trivialF2 H).explicitH1AddEquivContinuousCohomologyOfDiscrete
    (evensHomCocycle α hα : H1 H (trivialF2 H).V)

/-- `homClass` is the degree-one comparison applied to the explicit class of the homomorphism. -/
theorem homClass_eq_explicitH1AddEquivContinuousCohomology
    (α : H →* Multiplicative (ZMod 2)) (hα : Continuous α) :
    homClass H α hα =
      (trivialF2 H).explicitH1AddEquivContinuousCohomologyOfDiscrete
        (evensHomCocycle α hα : H1 H (trivialF2 H).V) :=
  (rfl)

private theorem trivialF2_smul_eq (K : Type u) [Group K]
    (g : K) (m : (trivialF2 K).V) : g • m = m := by
  rw [TopRep.distribMulAction_smul, trivialF2_ρ_apply_apply]

private noncomputable def classCharacter
    (x : continuousCohomology 1 (trivialF2 H)) : H →* Multiplicative (ZMod 2) :=
  (trivialF2Equiv H).toMultiplicative.toMonoidHom.comp
    (Additive.toMul (H1EquivOfSmulEqSelf (trivialF2_smul_eq H)
      ((trivialF2 H).explicitH1AddEquivContinuousCohomologyOfDiscrete.symm x))).toMonoidHom

private theorem continuous_classCharacter
    (x : continuousCohomology 1 (trivialF2 H)) : Continuous (classCharacter x) :=
  (continuous_of_discreteTopology : Continuous
    (trivialF2Equiv H).toMultiplicative).comp
      (Additive.toMul (H1EquivOfSmulEqSelf (trivialF2_smul_eq H)
        ((trivialF2 H).explicitH1AddEquivContinuousCohomologyOfDiscrete.symm x))).continuous

private theorem evensHomCocycle_classCharacter
    (x : continuousCohomology 1 (trivialF2 H)) :
    (evensHomCocycle (classCharacter x) (continuous_classCharacter x) :
        H1 H (trivialF2 H).V) =
      (trivialF2 H).explicitH1AddEquivContinuousCohomologyOfDiscrete.symm x := by
  apply (H1EquivOfSmulEqSelf (trivialF2_smul_eq H)).injective
  rw [H1EquivOfSmulEqSelf_mk]
  apply Additive.toMul.injective
  ext h
  simp [classCharacter, Z1EquivOfSmulEqSelf_apply]

/-- Every canonical degree-one class with trivial `𝔽₂` coefficients is represented by a
continuous homomorphism to `𝔽₂`. -/
theorem homClass_surjective
    (x : continuousCohomology 1 (trivialF2 H)) :
    ∃ (α : H →* Multiplicative (ZMod 2)) (hα : Continuous α), homClass H α hα = x := by
  refine ⟨classCharacter x, continuous_classCharacter x, ?_⟩
  rw [homClass_eq_explicitH1AddEquivContinuousCohomology,
    evensHomCocycle_classCharacter, AddEquiv.apply_symm_apply]

/-- Two continuous homomorphisms to `𝔽₂` determine the same canonical degree-one class exactly
when they are equal. -/
@[simp]
theorem homClass_eq_iff (α β : H →* Multiplicative (ZMod 2))
    (hα : Continuous α) (hβ : Continuous β) :
    homClass H α hα = homClass H β hβ ↔ α = β := by
  constructor
  · intro hcl
    have hexplicit :
        (evensHomCocycle α hα : H1 H (trivialF2 H).V) =
          (evensHomCocycle β hβ : H1 H (trivialF2 H).V) := by
      apply (trivialF2 H).explicitH1AddEquivContinuousCohomologyOfDiscrete.injective
      exact hcl
    apply MonoidHom.ext
    intro h
    have hchars := congrArg Additive.toMul
      (congrArg (H1EquivOfSmulEqSelf (trivialF2_smul_eq H)) hexplicit)
    have hh := congrArg Multiplicative.toAdd (DFunLike.congr_fun hchars h)
    exact Multiplicative.toAdd.injective <| (trivialF2Equiv H).symm.injective <| by
      simpa only [H1EquivOfSmulEqSelf_mk, Z1EquivOfSmulEqSelf_apply,
        coe_evensHomCocycle, AddEquiv.apply_symm_apply, toAdd_ofAdd] using hh
  · rintro rfl
    rfl

/-- Continuous homomorphisms with the same canonical degree-one class have the same graph class. -/
theorem graphClass_representative_independent [LocallyCompactSpace G]
    (U : OpenSubgroup G) (hU : U.toSubgroup.index = 2)
    (α β : U.toSubgroup →* Multiplicative (ZMod 2)) (hα : Continuous α) (hβ : Continuous β)
    (hcl : homClass U.toSubgroup α hα = homClass U.toSubgroup β hβ) :
    graphClass U hU α hα = graphClass U hU β hβ := by
  rw [homClass_eq_iff] at hcl
  subst β
  rfl

/-- The index-two degree-one Evens norm, obtained by descending the graph class from continuous
homomorphisms to canonical first cohomology. It is a function rather than an additive map. -/
noncomputable def evensNormIndexTwo [LocallyCompactSpace G]
    (U : OpenSubgroup G) (hU : U.toSubgroup.index = 2)
    (x : continuousCohomology 1 (trivialF2 U.toSubgroup)) :
    continuousCohomology 2 (trivialF2 G) :=
  graphClass U hU (homClass_surjective x).choose (homClass_surjective x).choose_spec.choose

/-- On the class of a continuous homomorphism, the index-two Evens norm is its graph class. -/
theorem evensNormIndexTwo_homClass [LocallyCompactSpace G]
    (U : OpenSubgroup G) (hU : U.toSubgroup.index = 2)
    (α : U.toSubgroup →* Multiplicative (ZMod 2)) (hα : Continuous α) :
    evensNormIndexTwo U hU (homClass U.toSubgroup α hα) = graphClass U hU α hα := by
  exact graphClass_representative_independent U hU _ α _ hα
    (homClass_surjective (homClass U.toSubgroup α hα)).choose_spec.choose_spec

end TauCeti.ContCohomology
