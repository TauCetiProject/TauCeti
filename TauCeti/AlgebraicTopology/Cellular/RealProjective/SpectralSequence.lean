/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.RealProjective.Homology
public import TauCeti.AlgebraicTopology.Singular.FilteredSpace.Cellular

/-!
# The skeletal spectral sequence of real projective space

The spectral sequence of the skeletal filtration of a CW complex `B`
(`TauCeti.skeletalSpectralSequence`) has as first page the cellular chain complex of `B`, on the
line `k ↦ (1 - 2k, k - 1)` (`TauCeti.skeletalSpectralSequencePageTwoIso`), and as second page the
singular homology of `B` (`TauCeti.skeletalSpectralSequencePageThreeXIso`). This file reads both
pages off for real projective space `RPᴺ` with its CW structure of one cell in each dimension
`0, …, N` (`TauCeti.RealProjectiveSpace.cwComplex`), whose cellular differential from the
`(k + 1)`-cell to the `k`-cell is `0` for even `k` and twice a unit for odd `k`.

* The first page is `R` at each cell `k ≤ N`
  (`TauCeti.RealProjectiveSpace.skeletalSpectralSequenceFirstPageLinearEquiv`), in particular
  nonzero (`TauCeti.RealProjectiveSpace.not_isZero_skeletalSpectralSequence_page_two_X`).
* The first differential from the `(k + 1)`-cell to the `k`-cell vanishes for even `k`
  (`TauCeti.RealProjectiveSpace.skeletalSpectralSequence_page_two_d_eq_zero_of_even`), and for odd
  `k` it is multiplication by `2` in suitable coordinates
  (`TauCeti.RealProjectiveSpace.exists_linearEquiv_skeletalSpectralSequence_page_two_d_eq_two_mul`).
* The second page is `R` in degree `0`
  (`TauCeti.RealProjectiveSpace.skeletalSpectralSequencePageThreeXZeroLinearEquiv`), `R / 2R` in
  odd degrees `k < N`
  (`TauCeti.RealProjectiveSpace.skeletalSpectralSequencePageThreeXLinearEquivOfOdd`), so
  `ℤ/2` with integral coefficients
  (`TauCeti.RealProjectiveSpace.skeletalSpectralSequencePageThreeXIntLinearEquivOfOdd`), and the
  `2`-torsion of `R` in even degrees `0 < k ≤ N`
  (`TauCeti.RealProjectiveSpace.skeletalSpectralSequencePageThreeXLinearEquivOfEven`), so zero when
  `2` is not a zero divisor
  (`TauCeti.RealProjectiveSpace.isZero_skeletalSpectralSequence_page_three_X_of_even`).

For the real projective plane `RP²` with integral coefficients, the first page is `ℤ` at the
cells of dimensions `0`, `1` and `2`, with differential `2` from dimension `2` to dimension `1` and
`0` from dimension `1` to dimension `0`, and the second page is `ℤ`, `ℤ/2` and `0` there. So the
relative groups of the first page are not yet the second page: the first differential of this
filtration does not vanish.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Example 2.42, the cellular chain complex of `RPᴺ`.
* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  Section 2.2, the spectral sequence of a filtered complex.
-/

public section

noncomputable section

open CategoryTheory Limits Set Topology Topology.RelCWComplex

namespace TauCeti.RealProjectiveSpace

attribute [local instance] cwComplex

variable {N k : ℕ} (R : Type) [Ring R]

/-- **The first page of the skeletal spectral sequence of `RPᴺ`.** For `k ≤ N`, the object at
`(1 - 2k, k - 1)` is `R`, through the coordinate of the single `k`-cell. -/
def skeletalSpectralSequenceFirstPageLinearEquiv (hk : k ≤ N) :
    ((skeletalSpectralSequence (RealProjectiveSpace N) (ModuleCat.of R R)).page 2).X
      (skeletalLineEmbedding.f k) ≃ₗ[R] R :=
  (skeletalSpectralSequenceFirstPageXIso (ModuleCat.of R R) k).toLinearEquiv ≪≫ₗ
    cellularChainCoord _ R (cwComplexCell hk)

/-- The coordinate `TauCeti.RealProjectiveSpace.skeletalSpectralSequenceFirstPageLinearEquiv`
sends an element of the first page to the coordinate of the corresponding cellular chain. -/
lemma skeletalSpectralSequenceFirstPageLinearEquiv_apply (hk : k ≤ N)
    (x : ((skeletalSpectralSequence (RealProjectiveSpace N) (ModuleCat.of R R)).page 2).X
      (skeletalLineEmbedding.f k)) :
    skeletalSpectralSequenceFirstPageLinearEquiv R hk x =
      cellularChainCoord _ R (cwComplexCell hk)
        ((skeletalSpectralSequenceFirstPageXIso (ModuleCat.of R R) k).hom x) :=
  (rfl)

/-- **The first differential of `RPᴺ` vanishes out of odd cells.** For even `k`, the differential
of the first page of the skeletal spectral sequence of `RPᴺ` from `(-1 - 2k, k)` to
`(1 - 2k, k - 1)`, from the `(k + 1)`-cell to the `k`-cell, is zero. -/
theorem skeletalSpectralSequence_page_two_d_eq_zero_of_even (hk : Even k) :
    ((skeletalSpectralSequence (RealProjectiveSpace N) (ModuleCat.of R R)).page 2).d
      (skeletalLineEmbedding.f (k + 1)) (skeletalLineEmbedding.f k) = 0 := by
  rw [skeletalSpectralSequence_page_two_d_eq, cellularChainComplex_d_eq_zero_of_even R hk]
  simp

/-- **The first differential of `RPᴺ` out of even cells is twice a unit.** For odd `k` with
`k + 1 ≤ N`, in the coordinates
`TauCeti.RealProjectiveSpace.skeletalSpectralSequenceFirstPageLinearEquiv`, the differential of
the first page of the skeletal spectral sequence of `RPᴺ` from the `(k + 1)`-cell to the `k`-cell
is right multiplication by `2 u` for a unit `u`. -/
theorem exists_skeletalSpectralSequenceFirstPageLinearEquiv_page_two_d (hk : Odd k)
    (hkN : k + 1 ≤ N) :
    ∃ u : Rˣ, ∀ x, skeletalSpectralSequenceFirstPageLinearEquiv R (by lia : k ≤ N)
      (((skeletalSpectralSequence (RealProjectiveSpace N) (ModuleCat.of R R)).page 2).d
        (skeletalLineEmbedding.f (k + 1)) (skeletalLineEmbedding.f k) x) =
      skeletalSpectralSequenceFirstPageLinearEquiv R hkN x * (2 * u) := by
  obtain ⟨u, hu⟩ := exists_cellularChainCoord_d_eq_two_mul_of_odd R hk
    (cwComplexCell (by lia : k ≤ N)) (cwComplexCell hkN)
  refine ⟨u, fun x ↦ ?_⟩
  simpa [skeletalSpectralSequence_page_two_d_eq, skeletalSpectralSequenceFirstPageLinearEquiv_apply]
    using hu ((skeletalSpectralSequenceFirstPageXIso (ModuleCat.of R R) (k + 1)).hom x)

/-- The first page of the skeletal spectral sequence of `RPᴺ` is nonzero at every cell: for
`k ≤ N` and `R` nontrivial, the object at `(1 - 2k, k - 1)` is `R`. -/
theorem not_isZero_skeletalSpectralSequence_page_two_X [Nontrivial R] (hk : k ≤ N) :
    ¬ IsZero (((skeletalSpectralSequence (RealProjectiveSpace N) (ModuleCat.of R R)).page 2).X
      (skeletalLineEmbedding.f k)) := fun h ↦
  have := ModuleCat.subsingleton_of_isZero h
  not_subsingleton R (skeletalSpectralSequenceFirstPageLinearEquiv R hk).symm.toEquiv.subsingleton

/-- **The second page of the skeletal spectral sequence of `RPᴺ` in degree `0`.** The object at
`(1, -1)` on the page after the first is `H₀(RPᴺ; R) ≅ R`. -/
def skeletalSpectralSequencePageThreeXZeroLinearEquiv :
    ((skeletalSpectralSequence (RealProjectiveSpace N) (ModuleCat.of R R)).page 3).X
      (skeletalLineEmbedding.f 0) ≃ₗ[R] R :=
  have := finite_cwComplex (n := N)
  (skeletalSpectralSequencePageThreeXIso (ModuleCat.of R R) 0).toLinearEquiv ≪≫ₗ
    singularHomologyZeroLinearEquiv R

/-- **The second page of the skeletal spectral sequence of `RPᴺ` in odd degrees.** For odd
`k < N`, the object at `(1 - 2k, k - 1)` on the page after the first is
`Hₖ(RPᴺ; R) ≅ R / 2R`, although on the first page it is `R`. -/
def skeletalSpectralSequencePageThreeXLinearEquivOfOdd (hk : Odd k) (hkN : k < N) :
    ((skeletalSpectralSequence (RealProjectiveSpace N) (ModuleCat.of R R)).page 3).X
      (skeletalLineEmbedding.f k) ≃ₗ[R] R ⧸ R ∙ (2 : R) :=
  have := finite_cwComplex (n := N)
  (skeletalSpectralSequencePageThreeXIso (ModuleCat.of R R) k).toLinearEquiv ≪≫ₗ
    singularHomologyLinearEquivOfOdd R hk hkN

/-- **The second page of the skeletal spectral sequence of `RPᴺ` in even degrees.** For even `k`
with `0 < k ≤ N`, the object at `(1 - 2k, k - 1)` on the page after the first is the `2`-torsion
`{r : R | r * 2 = 0}` of `R`, although on the first page it is `R`. -/
def skeletalSpectralSequencePageThreeXLinearEquivOfEven (hk : Even k) (hk0 : k ≠ 0)
    (hkN : k ≤ N) :
    ((skeletalSpectralSequence (RealProjectiveSpace N) (ModuleCat.of R R)).page 3).X
      (skeletalLineEmbedding.f k) ≃ₗ[R] LinearMap.ker (LinearMap.toSpanSingleton R R 2) :=
  have := finite_cwComplex (n := N)
  (skeletalSpectralSequencePageThreeXIso (ModuleCat.of R R) k).toLinearEquiv ≪≫ₗ
    singularHomologyLinearEquivOfEven R hk hk0 hkN

/-- **The second page of the integral skeletal spectral sequence of `RPᴺ` in odd degrees.** For
odd `k < N`, the object at `(1 - 2k, k - 1)` on the page after the first is
`Hₖ(RPᴺ; ℤ) ≅ ℤ/2`, although on the first page it is `ℤ`. -/
def skeletalSpectralSequencePageThreeXIntLinearEquivOfOdd (hk : Odd k) (hkN : k < N) :
    ((skeletalSpectralSequence (RealProjectiveSpace N) (ModuleCat.of ℤ ℤ)).page 3).X
      (skeletalLineEmbedding.f k) ≃ₗ[ℤ] ZMod 2 :=
  have := finite_cwComplex (n := N)
  (skeletalSpectralSequencePageThreeXIso (ModuleCat.of ℤ ℤ) k).toLinearEquiv ≪≫ₗ
    singularHomologyIntLinearEquivOfOdd hk hkN

/-- **The second page of the skeletal spectral sequence of `RPᴺ` in even degrees.** If right
multiplication by `2` is injective on `R`, then for even `k > 0` the object at `(1 - 2k, k - 1)` on
the page after the first vanishes, although on the first page it is `R` for `k ≤ N`. -/
theorem isZero_skeletalSpectralSequence_page_three_X_of_even (h2 : IsRightRegular (2 : R))
    (hk : Even k) (hk0 : k ≠ 0) :
    IsZero (((skeletalSpectralSequence (RealProjectiveSpace N) (ModuleCat.of R R)).page 3).X
      (skeletalLineEmbedding.f k)) :=
  have := finite_cwComplex (n := N)
  (isZero_singularHomology_of_even R h2 hk hk0).of_iso
    (skeletalSpectralSequencePageThreeXIso (ModuleCat.of R R) k)

/-- **The first differential of `RPᴺ` out of even cells is `2`.** For odd `k` with `k + 1 ≤ N`,
the objects of the first page of the skeletal spectral sequence of `RPᴺ` at the `(k + 1)`-cell
and at the `k`-cell are both `R`, in coordinates in which the differential between them is
multiplication by `2`. For `RP²` and `k = 1` this is the differential `2` from the cell of
dimension `2` to the cell of dimension `1`. -/
theorem exists_linearEquiv_skeletalSpectralSequence_page_two_d_eq_two_mul (hk : Odd k)
    (hkN : k + 1 ≤ N) :
    ∃ (φ : ((skeletalSpectralSequence (RealProjectiveSpace N) (ModuleCat.of R R)).page 2).X
        (skeletalLineEmbedding.f (k + 1)) ≃ₗ[R] R)
      (ψ : ((skeletalSpectralSequence (RealProjectiveSpace N) (ModuleCat.of R R)).page 2).X
        (skeletalLineEmbedding.f k) ≃ₗ[R] R), ∀ x,
      ψ (((skeletalSpectralSequence (RealProjectiveSpace N) (ModuleCat.of R R)).page 2).d
        (skeletalLineEmbedding.f (k + 1)) (skeletalLineEmbedding.f k) x) = 2 * φ x := by
  obtain ⟨u, hu⟩ := exists_skeletalSpectralSequenceFirstPageLinearEquiv_page_two_d R hk hkN
  refine ⟨skeletalSpectralSequenceFirstPageLinearEquiv R hkN ≪≫ₗ
      DistribMulAction.toLinearEquiv R R (Units.opEquiv.symm (MulOpposite.op u)),
    skeletalSpectralSequenceFirstPageLinearEquiv R (by lia), fun x ↦ ?_⟩
  rw [LinearEquiv.trans_apply, DistribMulAction.toLinearEquiv_apply, Units.smul_def,
    Units.coe_opEquiv_symm, MulOpposite.unop_op, op_smul_eq_mul, hu, ← mul_assoc, ← mul_assoc,
    (Commute.ofNat_right _ 2).eq]

end TauCeti.RealProjectiveSpace
