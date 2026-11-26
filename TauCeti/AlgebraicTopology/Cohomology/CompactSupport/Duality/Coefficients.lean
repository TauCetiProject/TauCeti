/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Cap.RestrictScalars
public import TauCeti.AlgebraicTopology.Cohomology.CompactSupport.Duality.Manifold
public import TauCeti.AlgebraicTopology.Cohomology.Sphere.IntersectionForm
public import TauCeti.AlgebraicTopology.Cohomology.UniversalCoefficient.CapDuality

import TauCeti.CategoryTheory.Linear.Int

/-!
# Poincaré duality for an oriented closed manifold with coefficients in a ring

Let `M` be a compact Hausdorff manifold of dimension `n` with a homological orientation `o`, and
let `k` be a commutative ring. The fundamental class over `k`,
`[M]_k = TauCeti.HomologicalOrientation.fundamentalClassOver k`, is the image of the integral
fundamental class `[M]` in `Hₙ(M; k)` under the change of coefficients `ℤ → k`
(`TopCat.restrictScalarsHomologyMap`), where homology and cohomology over `k` are formed from
singular chains over `k`. This file proves Poincaré duality over `k`: capping with `[M]_k` is a
bijection `Hᵖ(M; k) → H_q(M; k)` for `p + q = n`
(`TauCeti.HomologicalOrientation.bijective_singularCapLinearMap_fundamentalClassOver`).

The integral theorem `TauCeti.HomologicalOrientation.bijective_singularCap_fundamentalClass` already
gives duality with coefficients in any abelian group, for integral chains; here the coefficient
group is `k`. Restricting cochains over `k` to integral chains is an isomorphism of cochain
complexes, singular homology commutes with restriction of scalars, and the cap product is
compatible with both comparisons (`TopCat.restrictScalarsHomologyMap_comp_map_singularCap`), so the
cap product with `[M]_k` is the integral duality isomorphism between the comparisons.

Over a field `k` this makes the cup pairing `(α, β) ↦ ⟨α ⌣ β, [M]_k⟩` of `Hᵖ(M; k)` with
`H^q(M; k)` nondegenerate
(`TauCeti.HomologicalOrientation.nondegenerate_singularCupPairing_fundamentalClassOver`),
by the duality between cap products and the cup pairing over a field. For an ordered field and
`n = 2p + d + 1` with `p + d + 1` even, this discharges the nondegeneracy hypothesis of the
computation of the indices of inertia of the cup pairing on `Sᵈ⁺¹ × M` against `[Sᵈ⁺¹] × [M]_k`:
both are `dim Hᵖ(M; k)`
(`TauCeti.HomologicalOrientation.sigPos_singularCupPairing_sphere_fundamentalClassOver` and
`TauCeti.HomologicalOrientation.sigNeg_singularCupPairing_sphere_fundamentalClassOver`).
For a closed oriented three-manifold `Y` with finite-dimensional real cohomology, `k = ℝ`, `d = 0`
and `p = 1`, this is `b₂⁺ = b₂⁻ = b₁(Y)` for the real cup pairing of `S¹ × Y` against
`[S¹] × [Y]_ℝ`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3, Theorem 3.30 and Proposition 3.38.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicTopology Module

namespace TauCeti.HomologicalOrientation

variable {M E : Type} [TopologicalSpace M] [T2Space M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]

section CommRing

variable {n : ℕ} (o : HomologicalOrientation M E n) (hn : finrank ℝ E = n) (k : Type)
  [CommRing k]

/-- **Poincaré duality with coefficients in a commutative ring.** For a compact Hausdorff manifold
`M` without boundary of dimension `n` with a homological orientation, and a commutative ring `k`,
capping with the fundamental class `[M]_k ∈ Hₙ(M; k)` over `k` is a bijection
`Hᵖ(M; k) → H_q(M; k)` for `p + q = n`, with homology and cohomology formed from singular chains
over `k`. -/
theorem bijective_singularCapLinearMap_fundamentalClassOver [CompactSpace M] {p q : ℕ}
    (h : p + q = n) :
    Function.Bijective ((TopCat.of M).singularCapLinearMap k h (o.fundamentalClassOver hn k)) := by
  -- The integral duality theorem is stated for the `ℤ`-linear structure of a preadditive
  -- category, the comparison for that of a category of modules; they agree by uniqueness.
  have hPD (_ : Linear ℤ (ModuleCat.{0} ℤ)) [MonoidalLinear ℤ (ModuleCat.{0} ℤ)] :
      Function.Bijective fun β : (TopCat.of M).singularCohomology
        (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ
          ((ModuleCat.restrictScalars (Int.castRingHom k)).obj (𝟙_ (ModuleCat k))) p ↦
        ((TopCat.of M).singularCap ℤ (ρ_ _).inv (ρ_ _).hom p q n h β).hom
          (o.fundamentalClass hn) := by
    obtain rfl := Subsingleton.elim ‹Linear ℤ (ModuleCat.{0} ℤ)› Linear.preadditiveIntLinear
    exact o.bijective_singularCap_fundamentalClass hn _ p q h
  -- The two comparisons, read with the carriers of the cohomology and homology over `k`, which
  -- are those of their restrictions of scalars.
  have hT : Function.Bijective fun α : (TopCat.of M).singularCohomology (𝟙_ (ModuleCat k)) k
      (𝟙_ (ModuleCat k)) p ↦ (TopCat.of M).restrictScalarsCohomologyMap (Int.castRingHom k)
        (ModuleCat.uliftUnitToRestrictScalars _) p α :=
    ConcreteCategory.bijective_of_isIso ((TopCat.of M).restrictScalarsCohomologyMap
      (Int.castRingHom k) (ModuleCat.uliftUnitToRestrictScalars _) p)
  have hΘ : Function.Bijective fun x ↦ @id (((singularHomologyFunctor (ModuleCat k) q).obj
      (𝟙_ (ModuleCat k))).obj (TopCat.of M))
        ((TopCat.of M).restrictScalarsHomologyMap (Int.castRingHom k) (𝟙 _) q x) :=
    ConcreteCategory.bijective_of_isIso ((TopCat.of M).restrictScalarsHomologyMap
      (Int.castRingHom k) (𝟙 _) q)
  convert hΘ.comp ((hPD ModuleCat.instLinear).comp hT) using 1
  funext α
  rw [TopCat.singularCapLinearMap_apply, fundamentalClassOver_def]
  exact ConcreteCategory.congr_hom ((TopCat.of M).restrictScalarsHomologyMap_comp_map_singularCap
    (Int.castRingHom k) (ModuleCat.uliftUnitToRestrictScalars _) p q n h α) (o.fundamentalClass hn)

end CommRing

section Field

variable {n : ℕ} (o : HomologicalOrientation M E n) (hn : finrank ℝ E = n) {k : Type} [Field k]

/-- **The cup pairing of a closed oriented manifold over a field is nondegenerate**: for a compact
Hausdorff manifold `M` of dimension `n` with a homological orientation and a field `k`, the cup
pairing `(α, β) ↦ ⟨α ⌣ β, [M]_k⟩` of `Hᵖ(M; k)` with `H^q(M; k)`, `p + q = n`, is nondegenerate. -/
theorem nondegenerate_singularCupPairing_fundamentalClassOver [CompactSpace M] {p q : ℕ}
    (h : p + q = n) :
    ((TopCat.of M).singularCupPairing k h (o.fundamentalClassOver hn k)).Nondegenerate :=
  ⟨((TopCat.of M).injective_singularCapLinearMap_iff k h _).1
      (o.bijective_singularCapLinearMap_fundamentalClassOver hn k h).1,
    ((TopCat.of M).separatingRight_singularCupPairing_iff k h (by omega) _).2
      (o.bijective_singularCapLinearMap_fundamentalClassOver hn k (by omega)).1⟩

end Field

section Signature

variable {k : Type} [Field k] [CompactSpace M] {d p : ℕ}
  (o : HomologicalOrientation M E (p + p + (d + 1))) (hn : finrank ℝ E = p + p + (d + 1))

/-- The cup pairing of `Hᵖ⁺ᵈ⁺¹(M; k)` with `Hᵖ(M; k)` against `[M]_k` separates the classes of
`Hᵖ(M; k)`. -/
private theorem injective_flip_singularCupPairing_fundamentalClassOver :
    Function.Injective ((TopCat.of M).singularCupPairing k (p := p + (d + 1)) (q := p)
      (by omega) (o.fundamentalClassOver hn k)).flip :=
  LinearMap.ker_eq_bot.1 (LinearMap.separatingRight_iff_flip_ker_eq_bot.1
    (o.nondegenerate_singularCupPairing_fundamentalClassOver hn (by omega)).2)

variable [LinearOrder k] [IsStrictOrderedRing k]

/-- **The positive index of inertia of the cup pairing on `Sᵈ⁺¹ × M`**: for a compact oriented
manifold `M` of dimension `2p + d + 1` with `p + d + 1` even and an ordered field `k` over which
`Hᵖ⁺ᵈ⁺¹(M; k)` and `Hᵖ(M; k)` are finite dimensional, the cup pairing on `Hᵖ⁺ᵈ⁺¹(Sᵈ⁺¹ × M; k)`
against `[Sᵈ⁺¹] × [M]_k` has positive index of inertia `dim Hᵖ(M; k)`. For a closed oriented
three-manifold `Y` with finite-dimensional real cohomology, `k = ℝ`, `d = 0` and `p = 1`, this gives
`b₂⁺ = b₁(Y)` for the real cup pairing of `S¹ × Y` against `[S¹] × [Y]_ℝ`; identifying this class
with the fundamental class of `S¹ × Y` is not done here. -/
theorem sigPos_singularCupPairing_sphere_fundamentalClassOver (hp : Even (p + (d + 1)))
    [FiniteDimensional k ((TopCat.of M).singularCohomology (𝟙_ (ModuleCat k)) k
      (𝟙_ (ModuleCat k)) (p + (d + 1)))]
    [FiniteDimensional k ((TopCat.of M).singularCohomology (𝟙_ (ModuleCat k)) k
      (𝟙_ (ModuleCat k)) p)] :
    sigPos (LinearMap.BilinMap.toQuadraticMap
      ((TopCat.sphere.{0} (d + 1) ⊗ TopCat.of M).singularCupPairing k (p := p + (d + 1))
        (q := p + (d + 1)) (by omega)
        (((singularHomologyFunctor (ModuleCat k) (p + p + (d + 1) + (d + 1))).map
          (λ_ (𝟙_ (ModuleCat k))).hom).app (TopCat.sphere.{0} (d + 1) ⊗ TopCat.of M)
          (TopCat.singularHomologyCross (TopCat.sphere.{0} (d + 1)) (TopCat.of M)
            (𝟙_ (ModuleCat k)) (𝟙_ (ModuleCat k)) (d + 1) (p + p + (d + 1))
            (p + p + (d + 1) + (d + 1)) (by omega)
            (TauCeti.singularHomologyTopCatSphereGenerator k d ⊗ₜ
              o.fundamentalClassOver hn k))))) =
      finrank k ((TopCat.of M).singularCohomology (𝟙_ (ModuleCat k)) k (𝟙_ (ModuleCat k)) p) :=
  TopCat.sigPos_singularCupPairing_sphere_singularHomologyCross_of_injective_flip hn (by omega)
    hp _ (o.injective_flip_singularCupPairing_fundamentalClassOver hn)

/-- **The negative index of inertia of the cup pairing on `Sᵈ⁺¹ × M`**: under the hypotheses of
`TauCeti.HomologicalOrientation.sigPos_singularCupPairing_sphere_fundamentalClassOver`, the cup
pairing on `Hᵖ⁺ᵈ⁺¹(Sᵈ⁺¹ × M; k)` against `[Sᵈ⁺¹] × [M]_k` has negative index of inertia
`dim Hᵖ(M; k)`. For a closed oriented three-manifold `Y` with finite-dimensional real cohomology,
`k = ℝ`, `d = 0` and `p = 1`, this gives `b₂⁻ = b₁(Y)` for the real cup pairing of `S¹ × Y` against
`[S¹] × [Y]_ℝ`; identifying this class with the fundamental class of `S¹ × Y` is not done here. -/
theorem sigNeg_singularCupPairing_sphere_fundamentalClassOver (hp : Even (p + (d + 1)))
    [FiniteDimensional k ((TopCat.of M).singularCohomology (𝟙_ (ModuleCat k)) k
      (𝟙_ (ModuleCat k)) (p + (d + 1)))]
    [FiniteDimensional k ((TopCat.of M).singularCohomology (𝟙_ (ModuleCat k)) k
      (𝟙_ (ModuleCat k)) p)] :
    sigNeg (LinearMap.BilinMap.toQuadraticMap
      ((TopCat.sphere.{0} (d + 1) ⊗ TopCat.of M).singularCupPairing k (p := p + (d + 1))
        (q := p + (d + 1)) (by omega)
        (((singularHomologyFunctor (ModuleCat k) (p + p + (d + 1) + (d + 1))).map
          (λ_ (𝟙_ (ModuleCat k))).hom).app (TopCat.sphere.{0} (d + 1) ⊗ TopCat.of M)
          (TopCat.singularHomologyCross (TopCat.sphere.{0} (d + 1)) (TopCat.of M)
            (𝟙_ (ModuleCat k)) (𝟙_ (ModuleCat k)) (d + 1) (p + p + (d + 1))
            (p + p + (d + 1) + (d + 1)) (by omega)
            (TauCeti.singularHomologyTopCatSphereGenerator k d ⊗ₜ
              o.fundamentalClassOver hn k))))) =
      finrank k ((TopCat.of M).singularCohomology (𝟙_ (ModuleCat k)) k (𝟙_ (ModuleCat k)) p) :=
  TopCat.sigNeg_singularCupPairing_sphere_singularHomologyCross_of_injective_flip hn (by omega)
    hp _ (o.injective_flip_singularCupPairing_fundamentalClassOver hn)

end Signature

end TauCeti.HomologicalOrientation
