/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.BorderedHolomorphic.DoubledBundle
public import TauCeti.AlgebraicTopology.Cohomology.FundamentalClass
public import TauCeti.Geometry.Manifold.Complex.FundamentalClass
public import TauCeti.Topology.VectorBundle.FiniteRank.DoubleAlong.WhitneySum
public import TauCeti.Topology.VectorBundle.FiniteRank.FirstChernClass

/-!
# The Maslov index of a bundle pair

Let `M` be a compact Hausdorff Riemann surface with boundary and `(C, F)` a bundle pair over `M`:
a complex core `C` real along the boundary, `F` being the real coordinate subbundle over the
boundary. The **Maslov index** `μ(C, F) = c₁(E_F)[Σ_ℂ]`
(`TauCeti.FiniteRankBundleCore.maslovIndex`) is the first Chern class of the doubled bundle
`E_F = TauCeti.SchottkyDouble.doubledBundleCore C hC`, evaluated on the fundamental class of the
canonical orientation of the Schottky double `Σ_ℂ`, a compact Riemann surface without boundary.

The doubled bundle used here is the topological double of `C` along the boundary, which involves
no choices. The first Chern class only depends on a complex vector bundle up to topological
isomorphism, so the Maslov index is natural under isomorphisms of bundle pairs
(`TauCeti.FiniteRankBundleCore.maslovIndex_eq_of_iso`): an isomorphism `e : C ≅ C'` whose fibre
maps over the boundary commute with coordinatewise conjugation, that is, which carries `F` onto
`F'`, doubles to an isomorphism of the doubled bundles commuting with the lifted involutions
(`TauCeti.FiniteRankBundleCore.doubleAlongIso`,
`TauCeti.FiniteRankBundleCore.doubleAlongMap_totalSpaceMap_doubleAlongSwap`).

In particular the Maslov index is independent of the choices made to give the doubled bundle a
smooth structure. Each collar form `G` of `C` supplied by
`TauCeti.SchottkyDouble.exists_iso_contMDiffOn_coordChange_doubledBundleCore`, for any collar
projection, comparison and neighbourhood of the boundary, comes with an isomorphism `G ≅ C`
commuting with conjugation over the boundary. So the smooth doubled bundle of `G` is
isomorphic to the topological double of `C`, compatibly with the lifted involutions, and `G` and
`C` have the same Maslov index.

The trivial pair `(ℂⁿ, ℝⁿ)` has Maslov index zero (`maslovIndex_trivial`): its double is the
trivial bundle over `Σ_ℂ` (`TauCeti.FiniteRankBundleCore.doubleAlongTrivialIso`).

Adding the trivial pair as a direct summand does not change the Maslov index
(`maslovIndex_trivial_whitneySum`, `maslovIndex_whitneySum_trivial`): the double of a Whitney sum
is the Whitney sum of the doubles (`TauCeti.FiniteRankBundleCore.doubleAlongWhitneySumIso`), and a
trivial summand does not change the first Chern class. This is the additivity of the Maslov index
under direct sums when one summand is trivial.

## Main definitions

* `TauCeti.FiniteRankBundleCore.maslovIndex`: the Maslov index `μ(C, F) = c₁(E_F)[Σ_ℂ]` of a
  bundle pair over a compact Riemann surface with boundary.

## Main results

* `TauCeti.FiniteRankBundleCore.maslovIndex_eq_of_iso`: isomorphic bundle pairs have the same
  Maslov index.
* `TauCeti.FiniteRankBundleCore.maslovIndex_trivial`: the trivial pair has Maslov index zero.
* `TauCeti.FiniteRankBundleCore.maslovIndex_trivial_whitneySum`,
  `TauCeti.FiniteRankBundleCore.maslovIndex_whitneySum_trivial`: adding the trivial pair as a
  direct summand does not change the Maslov index.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix C.3 (the boundary Maslov index as `c₁(E_F)[Σ_ℂ]`).
-/

public section

noncomputable section

open CategoryTheory
open scoped Manifold

namespace TauCeti.FiniteRankBundleCore

variable {M : Type} [TopologicalSpace M] [ChartedSpace ClosedUpperHalfPlane M]
  [HasGroupoid M borderedHolomorphicGroupoid] [T2Space M] [CompactSpace M]

local notation "A" => (borderedInterior M : Set M)ᶜ

/-- **The Maslov index of a bundle pair** `μ(C, F) = c₁(E_F)[Σ_ℂ]`, for a complex core `C` over a
compact Riemann surface with boundary `M`, real along the boundary with real subbundle `F`: the
first Chern class of the doubled bundle `E_F` (`TauCeti.SchottkyDouble.doubledBundleCore`)
evaluated on the fundamental class of the canonical orientation of the Schottky double. -/
def maslovIndex (C : FiniteRankBundleCore ℂ M) (hC : C.IsRealAlong A) : ℤ :=
  ((complexHomologicalOrientation (SchottkyDouble M)).evalFundamentalClass
    Complex.finrank_real_complex (ModuleCat.of ℤ (ULift.{0} ℤ)) (ContinuousMap.id _)
    (SchottkyDouble.doubledBundleCore C hC).firstChernClass).down

/-- The Maslov index is the first Chern class of the doubled bundle evaluated on the fundamental
class of the Schottky double. -/
theorem maslovIndex_def (C : FiniteRankBundleCore ℂ M) (hC : C.IsRealAlong A) :
    C.maslovIndex hC =
      ((complexHomologicalOrientation (SchottkyDouble M)).evalFundamentalClass
        Complex.finrank_real_complex (ModuleCat.of ℤ (ULift.{0} ℤ)) (ContinuousMap.id _)
        (SchottkyDouble.doubledBundleCore C hC).firstChernClass).down :=
  (rfl)

/-- **Naturality of the Maslov index.** Isomorphic bundle pairs have the same Maslov index: an
isomorphism `e : C ≅ C'` whose fibre maps over the boundary commute with coordinatewise
conjugation, so carry the real subbundle of `C` onto that of `C'`, doubles to an isomorphism of
the doubled bundles. -/
theorem maslovIndex_eq_of_iso {C C' : FiniteRankBundleCore ℂ M} (hC : C.IsRealAlong A)
    (hC' : C'.IsRealAlong A) (e : C ≅ C')
    (he : ∀ a ∈ A, ∀ v, e.hom.fiberMap a (star v) = star (e.hom.fiberMap a v)) :
    C.maslovIndex hC = C'.maslovIndex hC' := by
  rw [maslovIndex_def, maslovIndex_def, SchottkyDouble.doubledBundleCore_eq,
    SchottkyDouble.doubledBundleCore_eq, firstChernClass_eq_of_iso (doubleAlongIso hC hC' e he)]

/-- **The trivial pair `(ℂⁿ, ℝⁿ)` has Maslov index zero**: its doubled bundle is trivial. -/
@[simp]
theorem maslovIndex_trivial (n : ℕ) :
    (trivial ℂ M n).maslovIndex (isRealAlong_trivial n A) = 0 := by
  rw [maslovIndex_def, SchottkyDouble.doubledBundleCore_eq,
    firstChernClass_eq_of_iso (doubleAlongTrivialIso n), firstChernClass_trivial, map_zero,
    ULift.zero_down]

/-- **Adding a trivial summand does not change the Maslov index**:
`μ((ℂⁿ, ℝⁿ) ⊕ (C, F)) = μ(C, F)`. -/
@[simp]
theorem maslovIndex_trivial_whitneySum (n : ℕ) (C : FiniteRankBundleCore ℂ M)
    (hC : C.IsRealAlong A) :
    (whitneySum (trivial ℂ M n) C).maslovIndex ((isRealAlong_trivial n A).whitneySum hC) =
      C.maslovIndex hC := by
  rw [maslovIndex_def, maslovIndex_def, SchottkyDouble.doubledBundleCore_eq,
    SchottkyDouble.doubledBundleCore_eq,
    firstChernClass_eq_of_iso (doubleAlongWhitneySumIso (isRealAlong_trivial n A) hC ≪≫
      whitneyMapIso (doubleAlongTrivialIso n) (Iso.refl _)),
    firstChernClass_trivial_whitneySum]

/-- **Adding a trivial summand does not change the Maslov index**:
`μ((C, F) ⊕ (ℂⁿ, ℝⁿ)) = μ(C, F)`. -/
@[simp]
theorem maslovIndex_whitneySum_trivial (C : FiniteRankBundleCore ℂ M) (hC : C.IsRealAlong A)
    (n : ℕ) :
    (whitneySum C (trivial ℂ M n)).maslovIndex (hC.whitneySum (isRealAlong_trivial n A)) =
      C.maslovIndex hC := by
  rw [maslovIndex_def, maslovIndex_def, SchottkyDouble.doubledBundleCore_eq,
    SchottkyDouble.doubledBundleCore_eq,
    firstChernClass_eq_of_iso (doubleAlongWhitneySumIso hC (isRealAlong_trivial n A) ≪≫
      whitneyMapIso (Iso.refl _) (doubleAlongTrivialIso n)),
    firstChernClass_whitneySum_trivial]

end TauCeti.FiniteRankBundleCore
