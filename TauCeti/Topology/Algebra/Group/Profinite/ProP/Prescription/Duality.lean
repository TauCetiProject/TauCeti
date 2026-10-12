/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Duality.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Prescription.Basic

/-!
# The prescription property from Tate's duality map

Let `G` be a topological group, `χ : G →ₜ* ℤ_pˣ` a continuous character and `I(χ)/pⁱ` its twisted
coefficients. Tate's duality map in degree two with coefficients `I(χ)/pⁿ`,
`α₂ : H²(G, M) → Hom(H⁰(G, Hom(M, I(χ)/pⁿ)), H²(G, I(χ)/pⁿ))`, is the adjoint of the evaluation
pairing (`TauCeti.ContCohomology.dualityMap2`). Its injectivity on the twist `M = I(χ)/pⁱ` itself,
for `i + j = n`, forces multiplication by `pʲ` to be injective on `H²(G, I(χ)/pⁱ) → H²(G, I(χ)/pⁿ)`:
a class killed by the multiplication pairs to zero with every invariant endomorphism of `I(χ)/pⁿ`
restricted along it, and every invariant homomorphism `I(χ)/pⁱ → I(χ)/pⁿ` is such a restriction
(`TauCeti.ZModTwist.surjective_explicitCoeff0_precomp_mulPow`). Injectivity of multiplication by `p`
on `H²` between consecutive levels is Labute's cohomological form of the prescription property
(`TauCeti.hasPrescriptionProperty_iff_forall_injective_explicitCoeff2_mulPow`), so a character whose
duality maps `α₂` are injective between consecutive levels has the prescription property.

This is the mechanism by which a duality theorem identifies the canonical character of a Demushkin
group, which is the unique character with the prescription property: a duality with values in
`H²(G, I(χ)/pⁿ)` that is perfect, or merely injective in degree two, on the twists of `χ` can only
hold for the canonical character.

## Main results

* `TauCeti.ZModTwist.injective_explicitCoeff2_mulPow_of_injective_dualityMap2`: if `α₂` with values
  in `H²(G, I(χ)/pⁿ)` is injective on `I(χ)/pⁱ`, `i + j = n`, then multiplication by `pʲ` is
  injective on `H²(G, I(χ)/pⁱ) → H²(G, I(χ)/pⁿ)`.
* `TauCeti.hasPrescriptionProperty_of_forall_injective_dualityMap2`: **a character whose duality
  maps `α₂` are injective between consecutive levels has the prescription property.**

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132, §2,
  Proposition 6.
* J.-P. Serre, *Structure de certains pro-p-groupes (d'après Demuškin)*, Séminaire Bourbaki 8
  (1962/63), exposé 252, §9.
-/

public section

namespace TauCeti

open ContCohomology

universe u

variable {p : ℕ} [Fact p.Prime] {G : Type u} [Group G] [TopologicalSpace G] [ContinuousMul G]
  (χ : G →ₜ* ℤ_[p]ˣ)

namespace ZModTwist

/-- **Injectivity of `α₂` on a twist gives injectivity of the multiplication on `H²`.** If Tate's
duality map `α₂ : H²(G, I(χ)/pⁱ) → Hom(H⁰(G, Hom(I(χ)/pⁱ, I(χ)/pⁿ)), H²(G, I(χ)/pⁿ))` is injective,
`i + j = n`, then multiplication by `pʲ` is injective on `H²(G, I(χ)/pⁱ) → H²(G, I(χ)/pⁿ)`. -/
theorem injective_explicitCoeff2_mulPow_of_injective_dualityMap2 {i j n : ℕ} (h : i + j = n)
    (hα : Function.Injective (dualityMap2 G (ZModTwist χ i) (ZModTwist χ n))) :
    Function.Injective
      (explicitCoeff2 G (ZModTwist χ i) (mulPow χ h) continuous_of_discreteTopology) :=
  explicitCoeff2_injective_of_dualityMap2_injective (mulPow χ h) hα
    (surjective_explicitCoeff0_precomp_mulPow χ h)

end ZModTwist

/-- **A character whose duality maps `α₂` are injective between consecutive levels has the
prescription property**: if, for every `i`, Tate's duality map with values in `H²(G, I(χ)/pⁱ⁺¹)`
is injective on `I(χ)/pⁱ`, then every reduction `H¹(G, I(χ)/pⁱ) → H¹(G, I(χ)/p)` is surjective. -/
theorem hasPrescriptionProperty_of_forall_injective_dualityMap2
    (h : ∀ i : ℕ, Function.Injective (dualityMap2 G (ZModTwist χ i) (ZModTwist χ (i + 1)))) :
    HasPrescriptionProperty χ :=
  (hasPrescriptionProperty_iff_forall_injective_explicitCoeff2_mulPow χ).2 fun i n hn ↦ by
    subst hn
    exact ZModTwist.injective_explicitCoeff2_mulPow_of_injective_dualityMap2 χ rfl (h i)

end TauCeti
