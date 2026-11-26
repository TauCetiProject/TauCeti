/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.CompactSupport.Duality.Manifold
public import TauCeti.AlgebraicTopology.Cohomology.Cap.Kronecker

import TauCeti.CategoryTheory.Linear.Int

/-!
# Poincaré duality for the integral cup pairing

Let `M` be a closed manifold of dimension `n`, that is a compact Hausdorff space charted on a real
normed space of finite dimension `n`, with a homological orientation `o`. Poincaré duality
(`TauCeti.HomologicalOrientation.bijective_singularCapAddHom_fundamentalClass`) is stated in the
convention of fundamental classes: singular chains with coefficients in `ULift ℤ`, and the
`ℤ`-linear structure of `ModuleCat ℤ` as a preadditive category. The cup pairing
`TopCat.singularCupPairing` and capping with a homology class `TopCat.singularCapLinearMap` use
instead chain coefficients and cochain values the unit object `ℤ` of `ModuleCat ℤ`, with the
`ℤ`-linear structure of a category of modules; this is also the convention of the Künneth
decompositions of products with circles, such as `TopCat.singularCohomologyAddCircleProdSlantEquiv`.

This file transports Poincaré duality to the second convention. Write `[M]_ℤ ∈ Hₙ(M; ℤ)`
(`TauCeti.HomologicalOrientation.intFundamentalClass`) for the fundamental class read with chain
coefficients `ℤ`, its image under the coefficient isomorphism `TauCeti.uliftIntIso`. Then capping
with `[M]_ℤ` is a bijection

`Hᵖ(M; ℤ) → H_q(M; ℤ)`, `α ↦ [M]_ℤ ⌢ α`, `p + q = n`

(`TauCeti.HomologicalOrientation.bijective_singularCapLinearMap_intFundamentalClass`). Since
`⟨β, [M]_ℤ ⌢ α⟩ = ⟨α ⌣ β, [M]_ℤ⟩`, every homology class `x ∈ H_q(M; ℤ)` has a Poincaré dual
`α ∈ Hᵖ(M; ℤ)`, with `⟨α ⌣ β, [M]_ℤ⟩ = ⟨β, x⟩` for every `β ∈ H^q(M; ℤ)`
(`TauCeti.HomologicalOrientation.exists_forall_singularCupPairing_eq_singularKronecker`). This is
how integral intersection numbers on a closed manifold are computed by evaluating classes on
homology classes. For instance, a class `v ∈ H²(Y; ℤ)` on a closed oriented three-manifold `Y`
with `⟨v, x⟩ = 1` on some `x ∈ H₂(Y; ℤ)` has a partner `a ∈ H¹(Y; ℤ)` with `⟨a ⌣ v, [Y]_ℤ⟩ = 1`.
The dual class is not unique in general, since torsion of `H_q(M; ℤ)` is invisible to the integral
Kronecker pairing.

The proof compares the two cap products by their naturality in the chain coefficients
(`TopCat.singularCapLinearMap_singularCohomologyChainCoefficientMap`) and by their independence
of the presentation of the `ℤ`-linear structure (`TopCat.singularCap_eqToHom`).

## Main results

* `TauCeti.HomologicalOrientation.bijective_singularCapLinearMap_intFundamentalClass`: capping with
  the integral fundamental class `[M]_ℤ` is bijective.
* `TauCeti.HomologicalOrientation.exists_forall_singularCupPairing_eq_singularKronecker`: every
  integral homology class has a Poincaré dual for the cup pairing on `[M]_ℤ`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3, Theorem 3.30 (Poincaré duality for closed manifolds) and the identity
  `⟨ψ, x ⌢ φ⟩ = ⟨φ ⌣ ψ, x⟩` before it.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory Module AlgebraicTopology

namespace TauCeti.HomologicalOrientation

variable {M E : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
  {n : ℕ} (o : HomologicalOrientation M E n) (hn : finrank ℝ E = n)

attribute [local instance 1100] ModuleCat.instLinear

attribute [local instance] MonoidalPreadditive.monoidalLinearInt in
/-- **Poincaré duality for the integral fundamental class.** For a closed manifold `M` of
dimension `n` with a homological orientation, capping with the fundamental class read with chain
coefficients `ℤ` is a bijection `Hᵖ(M; ℤ) → H_q(M; ℤ)`, `α ↦ [M]_ℤ ⌢ α`, for `p + q = n`, in the
convention of `TopCat.singularCapLinearMap` and `TopCat.singularCupPairing`. -/
theorem bijective_singularCapLinearMap_intFundamentalClass {p q : ℕ} (h : p + q = n) :
    Function.Bijective ((TopCat.of M).singularCapLinearMap ℤ h (o.intFundamentalClass hn)) := by
  let e := eqToHom (congrArg (fun L : Linear ℤ (ModuleCat.{0} ℤ) ↦
    @TopCat.singularCohomology _ _ _ _ (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ _ L
      (𝟙_ (ModuleCat.{0} ℤ)) (TopCat.of M) p) (Subsingleton.elim Linear.preadditiveIntLinear
        ModuleCat.instLinear))
  let c := ((TopCat.of M).singularCohomologyChainCoefficientIso ℤ (𝟙_ (ModuleCat.{0} ℤ))
    uliftIntIso.symm p).hom
  -- `c ∘ e` changes the `ℤ`-linear structure and then the chain coefficients; after it, capping
  -- with `[M]_ℤ` is the cap product of `bijective_singularCapAddHom_fundamentalClass`.
  have hc : Function.Bijective (c ∘ e) :=
    (ConcreteCategory.bijective_of_isIso c).comp (ConcreteCategory.bijective_of_isIso e)
  refine (Function.Bijective.of_comp_iff _ hc).1 ?_
  convert o.bijective_singularCapAddHom_fundamentalClass hn (𝟙_ (ModuleCat.{0} ℤ)) p q h using 1
  funext α
  simp only [Function.comp_apply, c, e, TopCat.singularCohomologyChainCoefficientIso_hom,
    Iso.symm_hom]
  rw [intFundamentalClass_def,
    TopCat.singularCapLinearMap_singularCohomologyChainCoefficientMap _ _ h uliftIntIso
      (o.fundamentalClass hn),
    TopCat.singularCap_eqToHom _ _ (Subsingleton.elim _ _)]
  -- The `ℤ`-linear structure of the cap product is the one of the cohomology, not the synthesized
  -- one, so `singularCapAddHom_apply` takes it by unification.
  exact (@TopCat.singularCapAddHom_apply _ _ _ _ (_) (_) _ _ _ _ _ _ _ _ _ _ _ _ _ α).symm

/-- **Poincaré duals of integral homology classes.** On a closed manifold `M` of dimension `n` with
a homological orientation, every class `x ∈ H_q(M; ℤ)` has a Poincaré dual `α ∈ Hᵖ(M; ℤ)`,
`p + q = n`, for the cup pairing on the integral fundamental class `[M]_ℤ`:
`⟨α ⌣ β, [M]_ℤ⟩ = ⟨β, x⟩` for every `β ∈ H^q(M; ℤ)`. -/
theorem exists_forall_singularCupPairing_eq_singularKronecker {p q : ℕ} (h : p + q = n)
    (x : ((singularHomologyFunctor (ModuleCat.{0} ℤ) q).obj (𝟙_ (ModuleCat.{0} ℤ))).obj
      (TopCat.of M)) :
    ∃ α : (TopCat.of M).singularCohomology (𝟙_ (ModuleCat.{0} ℤ)) ℤ (𝟙_ (ModuleCat.{0} ℤ)) p,
      ∀ β : (TopCat.of M).singularCohomology (𝟙_ (ModuleCat.{0} ℤ)) ℤ (𝟙_ (ModuleCat.{0} ℤ)) q,
        (TopCat.of M).singularCupPairing ℤ h (o.intFundamentalClass hn) α β =
          ((TopCat.of M).singularKronecker ℤ q β).hom x := by
  obtain ⟨α, hα⟩ := (o.bijective_singularCapLinearMap_intFundamentalClass hn h).2 x
  exact ⟨α, fun β ↦ by
    rw [TopCat.singularCupPairing_eq_singularKronecker_singularCapLinearMap, hα]⟩

end TauCeti.HomologicalOrientation
