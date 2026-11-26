/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.CompactSupport.Duality.Coefficients
public import TauCeti.AlgebraicTopology.Singular.Torus.AddCircle

/-!
# The intersection form of `(ℝ / Tℤ) × M`

Let `M` be a compact connected oriented manifold of dimension `2p + 1` with `p + 1` even, and `k`
an ordered field over which `Hᵖ⁺¹(M; k)` and `Hᵖ(M; k)` are finite dimensional. For `T > 0` the
product `X = (ℝ / Tℤ) × M` is a closed manifold of dimension `2p + 2`. For any homological
orientation of `X`, and any manifold structure on it, this file shows that the cup pairing on
`Hᵖ⁺¹(X; k)` against the fundamental class `[X]_k` has both indices of inertia equal to
`dim Hᵖ(M; k)`
(`TauCeti.HomologicalOrientation.sigPos_singularCupPairing_addCircle_prod_fundamentalClassOver`,
`TauCeti.HomologicalOrientation.sigNeg_singularCupPairing_addCircle_prod_fundamentalClassOver`).

For a closed connected oriented three-manifold `Y` with finite-dimensional real cohomology,
`k = ℝ` and `p = 1`, this is `b₂⁺(X) = b₂⁻(X) = b₁(Y)` for the real intersection form of
`X = (ℝ / Tℤ) × Y`, for either orientation of `X`. For `T = 1` this is the four-manifold
`(ℝ / ℤ)_s × Y` on which the Seiberg–Witten invariants of a product with a circle are computed.

The circle `ℝ / Tℤ` is homeomorphic to the unit circle `S¹ ⊆ ℝ²`, through the complex unit circle
(`AddCircle.homeomorphSphere`), so `X` is homeomorphic to `S¹ × M`. The computation for manifolds
homeomorphic to `Sᵈ⁺¹ × M`
(`TauCeti.HomologicalOrientation.sigPos_singularCupPairing_fundamentalClassOver_of_homeomorph`)
then applies with `d = 0`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3, Theorem 3.30 and Proposition 3.38.
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory Module

namespace TauCeti.HomologicalOrientation

variable {M E : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
  (T : ℝ) [Fact (0 < T)] {k : Type} [Field k] [LinearOrder k] [IsStrictOrderedRing k] {p : ℕ}
  (o : HomologicalOrientation M E (p + p + 1)) (hn : finrank ℝ E = p + p + 1)
  {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [ChartedSpace E' (AddCircle T × M)]
  (oX : HomologicalOrientation (AddCircle T × M) E' (p + p + 1 + 1))
  (hX : finrank ℝ E' = p + p + 1 + 1)

include o hn in
/-- **The positive index of inertia of the intersection form of `(ℝ / Tℤ) × M`.** For a compact
connected oriented manifold `M` of dimension `2p + 1` with `p + 1` even, an ordered field `k` over
which `Hᵖ⁺¹(M; k)` and `Hᵖ(M; k)` are finite dimensional, and any homological orientation of
`(ℝ / Tℤ) × M`, the cup pairing on `Hᵖ⁺¹((ℝ / Tℤ) × M; k)` against the fundamental class over `k`
has positive index of inertia `dim Hᵖ(M; k)`. For a closed connected oriented three-manifold `Y`
with finite-dimensional real cohomology, `k = ℝ` and `p = 1`, this is
`b₂⁺((ℝ / Tℤ) × Y) = b₁(Y)`. -/
theorem sigPos_singularCupPairing_addCircle_prod_fundamentalClassOver (hp : Even (p + 1))
    [FiniteDimensional k ((TopCat.of M).singularCohomology (𝟙_ (ModuleCat k)) k
      (𝟙_ (ModuleCat k)) (p + 1))]
    [FiniteDimensional k ((TopCat.of M).singularCohomology (𝟙_ (ModuleCat k)) k
      (𝟙_ (ModuleCat k)) p)] :
    sigPos (LinearMap.BilinMap.toQuadraticMap
      ((TopCat.of (AddCircle T × M)).singularCupPairing k (p := p + 1) (q := p + 1) (by omega)
        (oX.fundamentalClassOver hX k))) =
      finrank k ((TopCat.of M).singularCohomology (𝟙_ (ModuleCat k)) k (𝟙_ (ModuleCat k)) p) :=
  o.sigPos_singularCupPairing_fundamentalClassOver_of_homeomorph (d := 0) hn oX hX
    ((AddCircle.homeomorphSphere (Fact.out : 0 < T).ne').prodCongr (Homeomorph.refl M)) hp

include o hn in
/-- **The negative index of inertia of the intersection form of `(ℝ / Tℤ) × M`.** Under the
hypotheses of
`TauCeti.HomologicalOrientation.sigPos_singularCupPairing_addCircle_prod_fundamentalClassOver`,
the cup pairing on `Hᵖ⁺¹((ℝ / Tℤ) × M; k)` against the fundamental class over `k` has negative
index of inertia `dim Hᵖ(M; k)`. For a closed connected oriented three-manifold `Y` with
finite-dimensional real cohomology, `k = ℝ` and `p = 1`, this is `b₂⁻((ℝ / Tℤ) × Y) = b₁(Y)`. -/
theorem sigNeg_singularCupPairing_addCircle_prod_fundamentalClassOver (hp : Even (p + 1))
    [FiniteDimensional k ((TopCat.of M).singularCohomology (𝟙_ (ModuleCat k)) k
      (𝟙_ (ModuleCat k)) (p + 1))]
    [FiniteDimensional k ((TopCat.of M).singularCohomology (𝟙_ (ModuleCat k)) k
      (𝟙_ (ModuleCat k)) p)] :
    sigNeg (LinearMap.BilinMap.toQuadraticMap
      ((TopCat.of (AddCircle T × M)).singularCupPairing k (p := p + 1) (q := p + 1) (by omega)
        (oX.fundamentalClassOver hX k))) =
      finrank k ((TopCat.of M).singularCohomology (𝟙_ (ModuleCat k)) k (𝟙_ (ModuleCat k)) p) :=
  o.sigNeg_singularCupPairing_fundamentalClassOver_of_homeomorph (d := 0) hn oX hX
    ((AddCircle.homeomorphSphere (Fact.out : 0 < T).ne').prodCongr (Homeomorph.refl M)) hp

end TauCeti.HomologicalOrientation
