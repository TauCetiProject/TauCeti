/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.Singular
public import TauCeti.AlgebraicTopology.Cellular.RealProjective.Basic
public import Mathlib.Data.ZMod.QuotientRing

/-!
# The singular homology of real projective space

The CW structure `TauCeti.RealProjectiveSpace.cwComplex` on `RPᴺ` has one cell in each dimension
`0, …, N`, so with coefficients in a ring `R` its cellular chain complex has one copy of `R` in each
degree `k ≤ N` and nothing above. Its differential out of degree `k + 1` is zero for even `k` and
right multiplication by twice a unit for odd `k < N`
(`TauCeti.RealProjectiveSpace.exists_cellularIncidence_cwComplex_eq_two_mul_of_odd`). Reading off
the homology of this complex and transporting it along the cellular–singular comparison
`TauCeti.cellularSingularHomologyIso` computes the singular homology of `RPᴺ`. The undetermined
units do not affect the answer.

## Main declarations

* `TauCeti.RealProjectiveSpace.singularHomologyZeroLinearEquiv`: `H₀(RPᴺ; R) ≅ R`.
* `TauCeti.RealProjectiveSpace.singularHomologyLinearEquivOfOdd`: for odd `k < N`,
  `Hₖ(RPᴺ; R) ≅ R / 2R`.
* `TauCeti.RealProjectiveSpace.singularHomologyLinearEquivOfEven`: for even `k` with
  `0 < k ≤ N`, `Hₖ(RPᴺ; R)` is the `2`-torsion of `R`.
* `TauCeti.RealProjectiveSpace.singularHomologyTopLinearEquivOfOdd`: for odd `N`,
  `H_N(RPᴺ; R) ≅ R`.
* `TauCeti.RealProjectiveSpace.isZero_singularHomology_of_lt`: `Hₖ(RPᴺ; R) = 0` for `k > N`.
* `TauCeti.RealProjectiveSpace.isZero_singularHomology_of_even`: `Hₖ(RPᴺ; R) = 0` for even
  `k > 0` when right multiplication by `2` is injective on `R`.
* `TauCeti.RealProjectiveSpace.singularHomologyIntLinearEquivOfOdd` and
  `TauCeti.RealProjectiveSpace.isZero_singularHomology_int_of_even`: integrally, `Hₖ(RPᴺ; ℤ)` is
  `ℤ/2` for odd `k < N` and vanishes for even `k > 0`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.2, Example 2.42.
-/

public section

noncomputable section

open CategoryTheory Limits Set Topology Topology.RelCWComplex

namespace TauCeti.RealProjectiveSpace

attribute [local instance] cwComplex

variable {N k : ℕ} (R : Type) [Ring R]

/-- For `k ≤ N`, the `k`-cell of `RPᴺ`. -/
private def theCell (hk : k ≤ N) : cell (univ : Set (RealProjectiveSpace N)) k :=
  Classical.choice (nonempty_cell_cwComplex hk)

/-- The cellular chain complex of `RPᴺ` with coefficients in `R`. -/
local notation "K" => cellularChainComplex (univ : Set (RealProjectiveSpace N)) (ModuleCat.of R R)

/-- The cellular chain group of `RPᴺ` in the degree of a cell `c` is `R`, through the coordinate
of `c`. -/
private def chainCoord (c : cell (univ : Set (RealProjectiveSpace N)) k) : (K).X k ≃ₗ[R] R :=
  (eqToIso (cellularChainComplex_X _ _ k)).toLinearEquiv ≪≫ₗ
    (cellularChainBasis (univ : Set (RealProjectiveSpace N)) R k).repr ≪≫ₗ
      Finsupp.uniqueLinearEquiv R R c

/-- In the coordinates `chainCoord`, the cellular differential is right multiplication by the
incidence number. -/
private lemma chainCoord_d (c : cell (univ : Set (RealProjectiveSpace N)) k)
    (c' : cell (univ : Set (RealProjectiveSpace N)) (k + 1)) (x : (K).X (k + 1)) :
    chainCoord R c ((K).d (k + 1) k x) =
      chainCoord R c' x * cellularIncidence (univ : Set (RealProjectiveSpace N)) R k c c' := by
  simp only [chainCoord, LinearEquiv.trans_apply, Finsupp.uniqueLinearEquiv_apply]
  rw [cellularChainComplex_d]
  simp only [Iso.toLinearEquiv_apply, eqToIso.hom, ← ConcreteCategory.comp_apply, Category.assoc,
    eqToHom_trans, eqToHom_refl, Category.comp_id]
  rw [ConcreteCategory.comp_apply, cellularChainBasis_repr_differential_apply,
    Finset.sum_eq_single c' (fun b _ hb ↦ absurd (Subsingleton.elim b c') hb)
      (fun h ↦ by rw [Finsupp.notMem_support_iff.1 h, zero_mul])]

/-- For even `k`, the differential of the cellular chain complex of `RPᴺ` out of degree `k + 1`
vanishes. -/
private lemma d_eq_zero_of_even (hk : Even k) : (K).d (k + 1) k = 0 := by
  rw [cellularChainComplex_d, (cellularDifferential_eq_zero_iff _ R k).2 fun c c' ↦
    cellularIncidence_cwComplex_eq_zero_of_even R hk c c']
  simp

/-- For odd `k`, the differential of the cellular chain complex of `RPᴺ` out of degree `k`
vanishes. -/
private lemma d_eq_zero_of_odd (hk : Odd k) : (K).d k (k - 1) = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by have := hk.pos; omega⟩
  exact d_eq_zero_of_even R (by simpa [Nat.odd_add_one] using hk)

/-- Above the top dimension, the differential of the cellular chain complex of `RPᴺ` vanishes. -/
private lemma d_eq_zero_of_le (hk : N ≤ k) : (K).d (k + 1) k = 0 := by
  rw [cellularChainComplex_d, (cellularDifferential_eq_zero_iff _ R k).2 fun _ c' ↦
    absurd (le_of_cell_cwComplex c') (by omega)]
  simp

/-- For odd `k`, in the coordinates `chainCoord`, the differential of the cellular chain complex
of `RPᴺ` out of degree `k + 1` is right multiplication by twice a unit. -/
private lemma exists_chainCoord_d_of_odd (hk : Odd k)
    (c : cell (univ : Set (RealProjectiveSpace N)) k)
    (c' : cell (univ : Set (RealProjectiveSpace N)) (k + 1)) :
    ∃ u : Rˣ, ∀ x, chainCoord R c ((K).d (k + 1) k x) = chainCoord R c' x * (2 * u) := by
  obtain ⟨u, hu⟩ := exists_cellularIncidence_cwComplex_eq_two_mul_of_odd R hk c c'
  exact ⟨u, fun x ↦ by rw [chainCoord_d, hu]⟩

/-- For odd `k < N`, the coordinate `chainCoord` carries the boundaries in degree `k` of the
cellular chain complex of `RPᴺ` onto `R ∙ 2`. -/
private lemma map_range_d_eq_span_two (hk : Odd k) (hkN : k < N) :
    (LinearMap.range ((K).d (k + 1) k).hom).map (chainCoord R (theCell hkN.le) : _ →ₗ[R] R) =
      R ∙ (2 : R) := by
  obtain ⟨u, hu⟩ := exists_chainCoord_d_of_odd R hk (theCell hkN.le) (theCell hkN)
  ext y
  simp only [Submodule.mem_map, LinearMap.mem_range, Submodule.mem_span_singleton, smul_eq_mul]
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    refine ⟨chainCoord R (theCell hkN) x * u, ?_⟩
    rw [mul_assoc, ← (Commute.ofNat_left 2 (u : R)).eq]
    exact (hu x).symm
  · rintro ⟨a, rfl⟩
    refine ⟨_, ⟨(chainCoord R (theCell hkN)).symm (a * ↑u⁻¹), rfl⟩, (hu _).trans ?_⟩
    rw [LinearEquiv.apply_symm_apply, (Commute.ofNat_left 2 (u : R)).eq, mul_assoc,
      Units.inv_mul_cancel_left]

/-- For odd `k` with `k + 1 ≤ N`, the coordinate `chainCoord` carries the cycles in degree `k + 1`
of the cellular chain complex of `RPᴺ` onto the `2`-torsion of `R`. -/
private lemma map_ker_d_eq_ker_two (hk : Odd k) (hkN : k + 1 ≤ N) :
    (LinearMap.ker ((K).d (k + 1) k).hom).map (chainCoord R (theCell hkN) : _ →ₗ[R] R) =
      LinearMap.ker (LinearMap.toSpanSingleton R R (2 : R)) := by
  obtain ⟨u, hu⟩ := exists_chainCoord_d_of_odd R hk (theCell (by omega)) (theCell hkN)
  have key (x : (K).X (k + 1)) : (K).d (k + 1) k x = 0 ↔
      chainCoord R (theCell hkN) x * 2 = 0 := by
    rw [← (chainCoord R (theCell (by omega))).map_eq_zero_iff, hu, ← mul_assoc,
      Units.mul_left_eq_zero]
  ext y
  simp only [Submodule.mem_map, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, smul_eq_mul]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (key x).1 hx
  · intro hy
    exact ⟨(chainCoord R (theCell hkN)).symm y, (key _).2 (by simpa using hy), by simp⟩

/-- The cellular homology of `RPᴺ` in a degree `k ≤ N` where both adjacent differentials vanish
is `R`. -/
private def cellularHomologyLinearEquivOfZero (hk : k ≤ N) (hin : (K).d (k + 1) k = 0)
    (hout : (K).d k (k - 1) = 0) : (K).homology k ≃ₗ[R] R :=
  ((K).homologyIsoSc' (k + 1) k (k - 1) (by simp) (by cases k <;> simp) ≪≫
      ((K).sc' (k + 1) k (k - 1)).asIsoHomologyι hout ≪≫
        ((K).sc' (k + 1) k (k - 1)).moduleCatOpcyclesIso).toLinearEquiv ≪≫ₗ
    Submodule.quotEquivOfEqBot _ (by
      rw [LinearMap.range_eq_bot]
      exact congrArg ModuleCat.Hom.hom hin) ≪≫ₗ
    chainCoord R (theCell hk)

/-- For odd `k < N`, the cellular homology of `RPᴺ` in degree `k` is `R / 2R`. -/
private def cellularHomologyLinearEquivOfOdd (hk : Odd k) (hkN : k < N) :
    (K).homology k ≃ₗ[R] R ⧸ R ∙ (2 : R) :=
  ((K).homologyIsoSc' (k + 1) k (k - 1) (by simp) (by cases k <;> simp) ≪≫
      ((K).sc' (k + 1) k (k - 1)).asIsoHomologyι (d_eq_zero_of_odd R hk) ≪≫
        ((K).sc' (k + 1) k (k - 1)).moduleCatOpcyclesIso).toLinearEquiv ≪≫ₗ
    Submodule.Quotient.equiv _ _ (chainCoord R (theCell hkN.le)) (map_range_d_eq_span_two R hk hkN)

/-- For even `k` with `0 < k ≤ N`, the cellular homology of `RPᴺ` in degree `k` is the
`2`-torsion of `R`. -/
private def cellularHomologyLinearEquivOfEven (hk : Even k) (hk0 : k ≠ 0) (hkN : k ≤ N) :
    (K).homology k ≃ₗ[R] LinearMap.ker (LinearMap.toSpanSingleton R R (2 : R)) :=
  ((K).homologyIsoSc' (k + 1) k (k - 1) (by simp) (by cases k <;> simp) ≪≫
      (((K).sc' (k + 1) k (k - 1)).asIsoHomologyπ (d_eq_zero_of_even R hk)).symm ≪≫
        ((K).sc' (k + 1) k (k - 1)).moduleCatCyclesIso).toLinearEquiv ≪≫ₗ
    LinearEquiv.ofSubmodules (chainCoord R (theCell hkN)) _ _ (by
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      exact map_ker_d_eq_ker_two R (by simpa [Nat.even_add_one] using hk) hkN)

/-- The singular homology of `RPᴺ` is the homology of its cellular chain complex. -/
private def singularHomologyIsoCellular (k : ℕ) :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} R) k).obj (ModuleCat.of R R)).obj
        (TopCat.of (RealProjectiveSpace N)) ≅ (K).homology k :=
  have := finite_cwComplex (n := N)
  have h : IsIso ((complexBasePair (univ : Set (RealProjectiveSpace N))).singularHomologyπ
      (C := ModuleCat.{0} R) (ModuleCat.of R R) k) := by infer_instance
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} R) k).obj
      (ModuleCat.of R R)).mapIso (TopCat.isoOfHomeo (Homeomorph.Set.univ _)).symm ≪≫
    @asIso _ _ _ _ ((complexBasePair (univ : Set (RealProjectiveSpace N))).singularHomologyπ
      (C := ModuleCat.{0} R) (ModuleCat.of R R) k) h ≪≫
    (cellularSingularHomologyIso _ (ModuleCat.of R R) k).symm

/-- **`H₀` of real projective space.** `H₀(RPᴺ; R) ≅ R`. -/
def singularHomologyZeroLinearEquiv :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} R) 0).obj (ModuleCat.of R R)).obj
      (TopCat.of (RealProjectiveSpace N)) ≃ₗ[R] R :=
  (singularHomologyIsoCellular R 0).toLinearEquiv ≪≫ₗ
    cellularHomologyLinearEquivOfZero R (Nat.zero_le N) (d_eq_zero_of_even R .zero)
      ((K).shape 0 0 (by simp))

/-- **Odd-degree homology of real projective space.** For odd `k < N`,
`Hₖ(RPᴺ; R) ≅ R / 2R`. -/
def singularHomologyLinearEquivOfOdd (hk : Odd k) (hkN : k < N) :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} R) k).obj (ModuleCat.of R R)).obj
      (TopCat.of (RealProjectiveSpace N)) ≃ₗ[R] R ⧸ R ∙ (2 : R) :=
  (singularHomologyIsoCellular R k).toLinearEquiv ≪≫ₗ cellularHomologyLinearEquivOfOdd R hk hkN

/-- **Even-degree homology of real projective space.** For even `k` with `0 < k ≤ N`,
`Hₖ(RPᴺ; R)` is the `2`-torsion `{r : R | r * 2 = 0}` of `R`. -/
def singularHomologyLinearEquivOfEven (hk : Even k) (hk0 : k ≠ 0) (hkN : k ≤ N) :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} R) k).obj (ModuleCat.of R R)).obj
      (TopCat.of (RealProjectiveSpace N)) ≃ₗ[R] LinearMap.ker (LinearMap.toSpanSingleton R R 2) :=
  (singularHomologyIsoCellular R k).toLinearEquiv ≪≫ₗ
    cellularHomologyLinearEquivOfEven R hk hk0 hkN

/-- **Top homology of an odd-dimensional real projective space.** For odd `N`,
`H_N(RPᴺ; R) ≅ R`. -/
def singularHomologyTopLinearEquivOfOdd (hN : Odd N) :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} R) N).obj (ModuleCat.of R R)).obj
      (TopCat.of (RealProjectiveSpace N)) ≃ₗ[R] R :=
  (singularHomologyIsoCellular R N).toLinearEquiv ≪≫ₗ
    cellularHomologyLinearEquivOfZero R le_rfl (d_eq_zero_of_le R le_rfl) (d_eq_zero_of_odd R hN)

/-- The singular homology of `RPᴺ` vanishes above degree `N`. -/
theorem isZero_singularHomology_of_lt (hk : N < k) :
    IsZero (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} R) k).obj
      (ModuleCat.of R R)).obj (TopCat.of (RealProjectiveSpace N))) := by
  have := finite_cwComplex (n := N)
  have : IsEmpty (cell (univ : Set (RealProjectiveSpace N)) k) :=
    ⟨fun c ↦ absurd (le_of_cell_cwComplex c) (by omega)⟩
  exact (isZero_singularHomology_complexBasePair_of_isEmpty_cell _ _ k).of_iso
    (singularHomologyIsoCellular R k ≪≫ cellularSingularHomologyIso _ _ k)

/-- **Odd-degree integral homology of real projective space.** For odd `k < N`,
`Hₖ(RPᴺ; ℤ) ≅ ℤ/2`. -/
def singularHomologyIntLinearEquivOfOdd (hk : Odd k) (hkN : k < N) :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) k).obj (ModuleCat.of ℤ ℤ)).obj
      (TopCat.of (RealProjectiveSpace N)) ≃ₗ[ℤ] ZMod 2 :=
  singularHomologyLinearEquivOfOdd ℤ hk hkN ≪≫ₗ
    (Int.quotientSpanNatEquivZMod 2).toAddEquiv.toIntLinearEquiv

/-- **Even-degree homology of real projective space without `2`-torsion.** If right
multiplication by `2` is injective on `R`, then `Hₖ(RPᴺ; R) = 0` for even `k > 0`. -/
theorem isZero_singularHomology_of_even (h2 : IsRightRegular (2 : R)) (hk : Even k)
    (hk0 : k ≠ 0) :
    IsZero (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} R) k).obj
      (ModuleCat.of R R)).obj (TopCat.of (RealProjectiveSpace N))) := by
  rcases le_or_gt k N with hkN | hkN
  · have : Subsingleton (LinearMap.ker (LinearMap.toSpanSingleton R R 2)) :=
      ⟨fun a b ↦ Subtype.ext <| by
        have ha := a.2
        have hb := b.2
        simp only [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, smul_eq_mul] at ha hb
        exact h2 (ha.trans hb.symm)⟩
    exact ModuleCat.isZero_iff_subsingleton.2
      (singularHomologyLinearEquivOfEven R hk hk0 hkN).toEquiv.subsingleton
  · exact isZero_singularHomology_of_lt R hkN

/-- **Even-degree integral homology of real projective space.** For even `k > 0`,
`Hₖ(RPᴺ; ℤ) = 0`. -/
theorem isZero_singularHomology_int_of_even (hk : Even k) (hk0 : k ≠ 0) :
    IsZero (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) k).obj
      (ModuleCat.of ℤ ℤ)).obj (TopCat.of (RealProjectiveSpace N))) :=
  isZero_singularHomology_of_even ℤ (isRegular_iff_ne_zero.2 two_ne_zero).right hk hk0

end TauCeti.RealProjectiveSpace
