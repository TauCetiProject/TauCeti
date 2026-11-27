/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ModuleCat.Basic
public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.Singular
public import TauCeti.AlgebraicTopology.Cellular.RealProjective.Basic
public import TauCeti.AlgebraicTopology.UniversalCover.RealProjective.Projectivization
public import TauCeti.LinearAlgebra.LinearMap.Ker
public import TauCeti.LinearAlgebra.LinearMap.Range
public import Mathlib.Data.ZMod.QuotientRing

/-!
# The singular homology of real projective space

The CW structure `TauCeti.RealProjectiveSpace.cwComplex` on `RPᴺ` has one cell in each dimension
`0, …, N`, so with coefficients in a ring `R` its cellular chain complex has one copy of `R` in each
degree `k ≤ N` and nothing above. Its differential out of degree `k + 1` is zero for even `k` and
right multiplication by twice a unit for odd `k < N`
(`TauCeti.RealProjectiveSpace.exists_cellularIncidence_cwComplex_eq_two_mul_of_odd`). Reading off
the homology of this complex, in the one-cell coordinates `TauCeti.cellularChainCoord`, and
transporting it along the cellular–singular comparison `TauCeti.cellularSingularHomologyIsoUniv`
computes the singular homology of `RPᴺ`. The undetermined units do not affect the answer.

## Main declarations

* `TauCeti.RealProjectiveSpace.singularHomologyZeroLinearEquiv`: `H₀(RPᴺ; R) ≅ R`.
* `TauCeti.RealProjectiveSpace.singularHomologyLinearEquivOfOdd`: for odd `k < N`,
  `Hₖ(RPᴺ; R) ≅ R / 2R`.
* `TauCeti.RealProjectiveSpace.singularHomologyLinearEquivOfEven`: for even `k` with
  `0 < k ≤ N`, `Hₖ(RPᴺ; R)` is the `2`-torsion of `R`.
* `TauCeti.RealProjectiveSpace.singularHomologyTopLinearEquivOfOdd`: for odd `N`,
  `H_N(RPᴺ; R) ≅ R`.
* `TauCeti.RealProjectiveSpace.cellularChainComplex_d_eq_zero_of_even` and
  `TauCeti.RealProjectiveSpace.exists_cellularChainCoord_d_eq_two_mul_of_odd`: the cellular
  differential out of degree `k + 1` vanishes for even `k`, and for odd `k` it is right
  multiplication by twice a unit in the coordinates of the cells
  `TauCeti.RealProjectiveSpace.cwComplexCell`.
* `TauCeti.RealProjectiveSpace.cellularChainComplex_d_eq_zero_of_two_eq_zero`: if `2 = 0` in `R`,
  every cellular differential of `RPᴺ` vanishes.
* `TauCeti.RealProjectiveSpace.isZero_singularHomology_of_lt`: `Hₖ(RPᴺ; R) = 0` for `k > N`.
* `TauCeti.RealProjectiveSpace.isZero_singularHomology_of_even`: `Hₖ(RPᴺ; R) = 0` for even
  `k > 0` when right multiplication by `2` is injective on `R`.
* `TauCeti.RealProjectiveSpace.singularHomologyIntLinearEquivOfOdd` and
  `TauCeti.RealProjectiveSpace.isZero_singularHomology_int_of_even`: integrally, `Hₖ(RPᴺ; ℤ)` is
  `ℤ/2` for odd `k < N` and vanishes for even `k > 0`.
* `TauCeti.RealProjectiveSpace.two_nsmul_singularHomology_one_eq_zero`: for `N ≠ 1`, every class
  of `H₁(RPᴺ; ℤ)` is killed by `2`.
* `TauCeti.RealProjectiveSpace.finrank_singularHomology_of_two_eq_zero`: over a division ring in
  which `2 = 0`, `Hₖ(RPᴺ; R)` is one-dimensional for `k ≤ N` and zero above.
* `TauCeti.RealProjectiveSpace.finrank_range_cellularChainComplex_d_of_two_ne_zero`: over a
  division ring in which `2 ≠ 0`, the cellular differential from degree `k + 1` to degree `k` has
  rank `1` for odd `k < N` and `0` otherwise.
* `TauCeti.RealProjectiveSpace.finrank_singularHomology_of_two_ne_zero`: over a division ring in
  which `2 ≠ 0`, `Hₖ(RPᴺ; R)` is one-dimensional only in degree `0` and, for odd `N`, in degree
  `N`.
* `TauCeti.RealProjectiveSpace.finrank_singularHomology_projectivization_of_two_eq_zero`,
  `TauCeti.RealProjectiveSpace.finrank_singularHomology_projectivization_of_two_ne_zero`,
  `TauCeti.RealProjectiveSpace.singularHomologyProjectivizationLinearEquivOfOdd`,
  `TauCeti.RealProjectiveSpace.singularHomologyProjectivizationIntLinearEquivOfOdd` and
  `TauCeti.RealProjectiveSpace.isZero_singularHomology_projectivization_of_even`: the same
  statements on the projectivization `ℙ ℝ (Fin (N + 1) → ℝ)`, transported along
  `TauCeti.RealProjectiveSpace.homeomorphProjectivization` by
  `TauCeti.RealProjectiveSpace.singularHomologyProjectivizationIso`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.2, Example 2.42.
-/

public section

noncomputable section

open CategoryTheory Limits Set Topology Topology.RelCWComplex
open scoped LinearAlgebra.Projectivization

namespace TauCeti.RealProjectiveSpace

attribute [local instance] cwComplex

variable {N k : ℕ} (R : Type) [Ring R]

/-- For `k ≤ N`, the `k`-cell of `RPᴺ`, the unique cell of dimension `k` of
`TauCeti.RealProjectiveSpace.cwComplex`. -/
def cwComplexCell (hk : k ≤ N) : cell (univ : Set (RealProjectiveSpace N)) k :=
  Classical.choice (nonempty_cell_cwComplex hk)

/-- The cellular chain complex of `RPᴺ` with coefficients in `R`. -/
local notation "K" => cellularChainComplex (univ : Set (RealProjectiveSpace N)) (ModuleCat.of R R)

/-- For even `k`, the differential of the cellular chain complex of `RPᴺ` out of degree `k + 1`
vanishes. -/
theorem cellularChainComplex_d_eq_zero_of_even (hk : Even k) : (K).d (k + 1) k = 0 := by
  rw [cellularChainComplex_d, (cellularDifferential_eq_zero_iff _ R k).2 fun c c' ↦
    cellularIncidence_cwComplex_eq_zero_of_even R hk c c']
  simp

/-- For odd `k`, the differential of the cellular chain complex of `RPᴺ` out of degree `k`
vanishes. -/
private lemma d_eq_zero_of_odd (hk : Odd k) : (K).d k (k - 1) = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by have := hk.pos; omega⟩
  exact cellularChainComplex_d_eq_zero_of_even R (by simpa [Nat.odd_add_one] using hk)

/-- If `2 = 0` in `R`, every differential of the cellular chain complex of `RPᴺ` vanishes: it is
zero or right multiplication by twice a unit. -/
theorem cellularChainComplex_d_eq_zero_of_two_eq_zero (h2 : (2 : R) = 0) :
    (K).d (k + 1) k = 0 := by
  rcases Nat.even_or_odd k with hk | hk
  · exact cellularChainComplex_d_eq_zero_of_even R hk
  rw [cellularChainComplex_d, (cellularDifferential_eq_zero_iff _ R k).2 fun c c' ↦ ?_]
  · simp
  obtain ⟨u, hu⟩ := exists_cellularIncidence_cwComplex_eq_two_mul_of_odd R hk c c'
  rw [hu, h2, zero_mul]

/-- Above the top dimension, the differential of the cellular chain complex of `RPᴺ` vanishes. -/
private lemma d_eq_zero_of_le (hk : N ≤ k) : (K).d (k + 1) k = 0 := by
  rw [cellularChainComplex_d, (cellularDifferential_eq_zero_iff _ R k).2 fun _ c' ↦
    absurd (le_of_cell_cwComplex c') (by omega)]
  simp

/-- For odd `k`, in the coordinates `TauCeti.cellularChainCoord`, the differential of the cellular
chain complex of `RPᴺ` out of degree `k + 1` is right multiplication by twice a unit. -/
theorem exists_cellularChainCoord_d_eq_two_mul_of_odd (hk : Odd k)
    (c : cell (univ : Set (RealProjectiveSpace N)) k)
    (c' : cell (univ : Set (RealProjectiveSpace N)) (k + 1)) :
    ∃ u : Rˣ, ∀ x,
      cellularChainCoord _ R c ((K).d (k + 1) k x) = cellularChainCoord _ R c' x * (2 * u) := by
  obtain ⟨u, hu⟩ := exists_cellularIncidence_cwComplex_eq_two_mul_of_odd R hk c c'
  exact ⟨u, fun x ↦ by rw [cellularChainCoord_d, hu]⟩

/-- For odd `k`, in the coordinates `TauCeti.cellularChainCoord`, the differential of the cellular
chain complex of `RPᴺ` out of degree `k + 1` is right multiplication by twice a unit, as a
commuting square of linear maps. -/
private lemma exists_toSpanSingleton_comp_eq (hk : Odd k)
    (c : cell (univ : Set (RealProjectiveSpace N)) k)
    (c' : cell (univ : Set (RealProjectiveSpace N)) (k + 1)) :
    ∃ u : Rˣ, LinearMap.toSpanSingleton R R (2 * u) ∘ₗ (cellularChainCoord _ R c' : _ →ₗ[R] R) =
      (cellularChainCoord _ R c : _ →ₗ[R] R) ∘ₗ ((K).d (k + 1) k).hom := by
  obtain ⟨u, hu⟩ := exists_cellularChainCoord_d_eq_two_mul_of_odd R hk c c'
  exact ⟨u, LinearMap.ext fun x ↦ (hu x).symm⟩

/-- For odd `k < N`, the coordinate `TauCeti.cellularChainCoord` carries the boundaries in degree
`k` of the cellular chain complex of `RPᴺ` onto `R ∙ 2`. -/
private lemma map_range_d_eq_span_two (hk : Odd k) (hkN : k < N) :
    (LinearMap.range ((K).d (k + 1) k).hom).map
        (cellularChainCoord _ R (cwComplexCell hkN.le) : _ →ₗ[R] R) =
      R ∙ (2 : R) := by
  obtain ⟨u, hu⟩ :=
    exists_toSpanSingleton_comp_eq R hk (cwComplexCell hkN.le) (cwComplexCell hkN)
  rw [LinearMap.map_range_eq_range_of_comp_eq _ (cellularChainCoord _ R _).surjective hu,
    LinearMap.range_toSpanSingleton, (Commute.ofNat_left 2 (u : R)).eq, ← smul_eq_mul,
    ← Units.smul_def, Submodule.span_singleton_group_smul_eq]

/-- For odd `k` with `k + 1 ≤ N`, the coordinate `TauCeti.cellularChainCoord` carries the cycles
in degree `k + 1` of the cellular chain complex of `RPᴺ` onto the `2`-torsion of `R`. -/
private lemma map_ker_d_eq_ker_two (hk : Odd k) (hkN : k + 1 ≤ N) :
    (LinearMap.ker ((K).d (k + 1) k).hom).map
        (cellularChainCoord _ R (cwComplexCell hkN) : _ →ₗ[R] R) =
      LinearMap.ker (LinearMap.toSpanSingleton R R (2 : R)) := by
  obtain ⟨u, hu⟩ :=
    exists_toSpanSingleton_comp_eq R hk (cwComplexCell (by omega)) (cwComplexCell hkN)
  rw [LinearMap.map_ker_eq_ker_of_comp_eq _ (cellularChainCoord _ R _).surjective
    (cellularChainCoord _ R _).injective hu]
  ext y
  simp [← mul_assoc]

/-- **Ranks of the cellular differentials of `RPᴺ` away from characteristic two.** If `2 ≠ 0` in
the division ring `F`, the differential of the cellular chain complex of `RPᴺ` from degree `k + 1`
to degree `k` has rank `1` for odd `k < N`, where it is multiplication by twice a unit, and rank
`0` otherwise. For `RP²` the differentials `d₁` and `d₂` have ranks `0` and `1`. -/
theorem finrank_range_cellularChainComplex_d_of_two_ne_zero {F : Type} [DivisionRing F]
    (h2 : (2 : F) ≠ 0) :
    Module.finrank F (LinearMap.range ((cellularChainComplex (univ : Set (RealProjectiveSpace N))
      (ModuleCat.of F F)).d (k + 1) k).hom) = if Odd k ∧ k < N then 1 else 0 := by
  split_ifs with hk
  · rw [← LinearEquiv.finrank_map_eq (cellularChainCoord _ F (cwComplexCell hk.2.le)),
      map_range_d_eq_span_two F hk.1 hk.2, IsSimpleModule.span_singleton_eq_top F h2,
      finrank_top, Module.finrank_self]
  · have hd : (cellularChainComplex (univ : Set (RealProjectiveSpace N))
        (ModuleCat.of F F)).d (k + 1) k = 0 := by
      rcases Nat.even_or_odd k with hke | hko
      · exact cellularChainComplex_d_eq_zero_of_even F hke
      · exact d_eq_zero_of_le F (by grind)
    rw [hd, ModuleCat.hom_zero, LinearMap.range_zero, finrank_bot]

/-- The singular homology of `RPᴺ` is the homology of its cellular chain complex. -/
private def singularHomologyIsoCellular (k : ℕ) :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} R) k).obj (ModuleCat.of R R)).obj
        (TopCat.of (RealProjectiveSpace N)) ≅ (K).homology k :=
  have := finite_cwComplex (n := N)
  (cellularSingularHomologyIsoUniv (ModuleCat.of R R) k).symm

/-- **`H₀` of real projective space.** `H₀(RPᴺ; R) ≅ R`. -/
def singularHomologyZeroLinearEquiv :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} R) 0).obj (ModuleCat.of R R)).obj
      (TopCat.of (RealProjectiveSpace N)) ≃ₗ[R] R :=
  (singularHomologyIsoCellular R 0).toLinearEquiv ≪≫ₗ
    (K).homologyEquivOfDEqZero (by simp) (by simp)
      (cellularChainCoord _ R (cwComplexCell N.zero_le))
      (cellularChainComplex_d_eq_zero_of_even R .zero) ((K).shape 0 0 (by simp))

/-- **Odd-degree homology of real projective space.** For odd `k < N`,
`Hₖ(RPᴺ; R) ≅ R / 2R`. -/
def singularHomologyLinearEquivOfOdd (hk : Odd k) (hkN : k < N) :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} R) k).obj (ModuleCat.of R R)).obj
      (TopCat.of (RealProjectiveSpace N)) ≃ₗ[R] R ⧸ R ∙ (2 : R) :=
  (singularHomologyIsoCellular R k).toLinearEquiv ≪≫ₗ
    (K).homologyEquivQuotOfOutgoingDEqZero (by simp) (by cases k <;> simp)
      (cellularChainCoord _ R (cwComplexCell hkN.le)) (d_eq_zero_of_odd R hk)
      (map_range_d_eq_span_two R hk hkN)

/-- **Even-degree homology of real projective space.** For even `k` with `0 < k ≤ N`,
`Hₖ(RPᴺ; R)` is the `2`-torsion `{r : R | r * 2 = 0}` of `R`. -/
def singularHomologyLinearEquivOfEven (hk : Even k) (hk0 : k ≠ 0) (hkN : k ≤ N) :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} R) k).obj (ModuleCat.of R R)).obj
      (TopCat.of (RealProjectiveSpace N)) ≃ₗ[R] LinearMap.ker (LinearMap.toSpanSingleton R R 2) :=
  (singularHomologyIsoCellular R k).toLinearEquiv ≪≫ₗ
    (K).homologyEquivOfIncomingDEqZero (k := k - 1) (by simp) (by cases k <;> simp)
      (cellularChainCoord _ R (cwComplexCell hkN)) (cellularChainComplex_d_eq_zero_of_even R hk) (by
        obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        exact map_ker_d_eq_ker_two R (by simpa [Nat.even_add_one] using hk) hkN)

/-- **Top homology of an odd-dimensional real projective space.** For odd `N`,
`H_N(RPᴺ; R) ≅ R`. -/
def singularHomologyTopLinearEquivOfOdd (hN : Odd N) :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} R) N).obj (ModuleCat.of R R)).obj
      (TopCat.of (RealProjectiveSpace N)) ≃ₗ[R] R :=
  (singularHomologyIsoCellular R N).toLinearEquiv ≪≫ₗ
    (K).homologyEquivOfDEqZero (by simp) (by cases N <;> simp)
      (cellularChainCoord _ R (cwComplexCell le_rfl)) (d_eq_zero_of_le R le_rfl)
      (d_eq_zero_of_odd R hN)

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
        have ha := a.property
        have hb := b.property
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

/-- For `N ≠ 1`, every class of `H₁(RPᴺ; ℤ)` is killed by `2`: the group is `ℤ/2` for `N ≥ 2`
and `0` for `N = 0`. -/
theorem two_nsmul_singularHomology_one_eq_zero (hN : N ≠ 1)
    (x : ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
      (ModuleCat.of ℤ ℤ)).obj (TopCat.of (RealProjectiveSpace N))) :
    2 • x = 0 := by
  rcases Nat.lt_or_gt_of_ne hN with hN | hN
  · exact ModuleCat.subsingleton_of_isZero (isZero_singularHomology_of_lt ℤ hN) |>.elim _ _
  let e := singularHomologyIntLinearEquivOfOdd (N := N) odd_one hN
  apply e.injective
  rw [map_nsmul, map_zero]
  generalize e x = y
  revert y
  decide

/-- **Homology of real projective space in characteristic two.** If `2 = 0` in the division ring
`R`, then `Hₖ(RPᴺ; R)` is one-dimensional for `k ≤ N` and zero for `k > N`. -/
theorem finrank_singularHomology_of_two_eq_zero {R : Type} [DivisionRing R] (h2 : (2 : R) = 0)
    (k : ℕ) :
    Module.finrank R (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} R) k).obj
      (ModuleCat.of R R)).obj (TopCat.of (RealProjectiveSpace N))) = if k ≤ N then 1 else 0 := by
  split_ifs with hkN
  · rcases Nat.even_or_odd k with hk | hk
    · rcases eq_or_ne k 0 with rfl | hk0
      · exact (singularHomologyZeroLinearEquiv R).finrank_eq.trans (Module.finrank_self R)
      · have hker : LinearMap.ker (LinearMap.toSpanSingleton R R 2) = ⊤ := by
          rw [h2, LinearMap.toSpanSingleton_zero, LinearMap.ker_zero]
        exact ((singularHomologyLinearEquivOfEven R hk hk0 hkN).trans
          (LinearEquiv.ofTop _ hker)).finrank_eq.trans (Module.finrank_self R)
    · rcases hkN.lt_or_eq with hkN | rfl
      · have hspan : R ∙ (2 : R) = ⊥ := by rw [h2, Submodule.span_singleton_eq_bot]
        exact ((singularHomologyLinearEquivOfOdd R hk hkN).trans
          (Submodule.quotEquivOfEqBot _ hspan)).finrank_eq.trans (Module.finrank_self R)
      · exact (singularHomologyTopLinearEquivOfOdd R hk).finrank_eq.trans (Module.finrank_self R)
  · have := ModuleCat.isZero_iff_subsingleton.1
      (isZero_singularHomology_of_lt (N := N) R (Nat.lt_of_not_le hkN))
    exact Module.finrank_zero_of_subsingleton

/-- **Betti numbers of real projective space away from characteristic two.** If `2 ≠ 0` in the
division ring `F`, for instance `F = ℚ`, then `H₀(RPᴺ; F)` is one-dimensional, so is `H_N(RPᴺ; F)`
for odd `N`, and every other `Hₖ(RPᴺ; F)` vanishes. -/
theorem finrank_singularHomology_of_two_ne_zero {F : Type} [DivisionRing F] (h2 : (2 : F) ≠ 0)
    (k : ℕ) :
    Module.finrank F (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} F) k).obj
      (ModuleCat.of F F)).obj (TopCat.of (RealProjectiveSpace N))) =
      if k = 0 ∨ k = N ∧ Odd N then 1 else 0 := by
  rcases eq_or_ne k 0 with rfl | hk0
  · simp [(singularHomologyZeroLinearEquiv F).finrank_eq]
  rcases k.even_or_odd with hk | hk
  · rw [ModuleCat.finrank_eq_zero_of_isZero (isZero_singularHomology_of_even F
      (isRegular_iff_ne_zero.2 h2).right hk hk0)]
    grind
  rcases lt_trichotomy k N with hlt | rfl | hlt
  · have : Subsingleton (F ⧸ F ∙ (2 : F)) := by
      rw [IsSimpleModule.span_singleton_eq_top F h2]
      infer_instance
    rw [(singularHomologyLinearEquivOfOdd F hk hlt).finrank_eq, Module.finrank_zero_of_subsingleton]
    grind
  · simp [(singularHomologyTopLinearEquivOfOdd F hk).finrank_eq, hk]
  · rw [ModuleCat.finrank_eq_zero_of_isZero (isZero_singularHomology_of_lt F hlt)]
    grind

/-! ### The projectivization carrier -/

/-- The singular homology of `RPᴺ` is isomorphic to that of `ℙ ℝ (Fin (N + 1) → ℝ)`, along
`homeomorphProjectivization`. -/
def singularHomologyProjectivizationIso (k : ℕ) :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} R) k).obj (ModuleCat.of R R)).obj
      (TopCat.of (RealProjectiveSpace N)) ≅
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} R) k).obj (ModuleCat.of R R)).obj
        (TopCat.of (ℙ ℝ (Fin (N + 1) → ℝ))) :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} R) k).obj
    (ModuleCat.of R R)).mapIso (TopCat.isoOfHomeo (X := TopCat.of (RealProjectiveSpace N))
      (homeomorphProjectivization N))

/-- **Homology of `ℙ ℝ (Fin (N + 1) → ℝ)` in characteristic two.** If `2 = 0` in the division ring
`R`, then `Hₖ(ℙ ℝ (Fin (N + 1) → ℝ); R)` is one-dimensional for `k ≤ N` and zero for `k > N`. -/
theorem finrank_singularHomology_projectivization_of_two_eq_zero {R : Type} [DivisionRing R]
    (h2 : (2 : R) = 0) (k : ℕ) :
    Module.finrank R (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} R) k).obj
      (ModuleCat.of R R)).obj (TopCat.of (ℙ ℝ (Fin (N + 1) → ℝ)))) =
      if k ≤ N then 1 else 0 :=
  (singularHomologyProjectivizationIso (N := N) R k).toLinearEquiv.finrank_eq.symm.trans
    (finrank_singularHomology_of_two_eq_zero h2 k)

/-- **Homology of `ℙ ℝ (Fin (N + 1) → ℝ)` away from characteristic two.** If `2 ≠ 0` in the
division ring `F`, for instance `F = ℚ`, then `Hₖ(ℙ ℝ (Fin (N + 1) → ℝ); F)` is one-dimensional in
degree `0` and, for odd `N`, in degree `N`, and vanishes in every other degree. -/
theorem finrank_singularHomology_projectivization_of_two_ne_zero {F : Type} [DivisionRing F]
    (h2 : (2 : F) ≠ 0) (k : ℕ) :
    Module.finrank F (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} F) k).obj
      (ModuleCat.of F F)).obj (TopCat.of (ℙ ℝ (Fin (N + 1) → ℝ)))) =
      if k = 0 ∨ k = N ∧ Odd N then 1 else 0 :=
  (singularHomologyProjectivizationIso (N := N) F k).toLinearEquiv.finrank_eq.symm.trans
    (finrank_singularHomology_of_two_ne_zero h2 k)

/-- For odd `k < N`, `Hₖ(ℙ ℝ (Fin (N + 1) → ℝ); R) ≅ R / 2R`. -/
def singularHomologyProjectivizationLinearEquivOfOdd (hk : Odd k) (hkN : k < N) :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} R) k).obj (ModuleCat.of R R)).obj
      (TopCat.of (ℙ ℝ (Fin (N + 1) → ℝ))) ≃ₗ[R] R ⧸ R ∙ (2 : R) :=
  (singularHomologyProjectivizationIso (N := N) R k).toLinearEquiv.symm ≪≫ₗ
    singularHomologyLinearEquivOfOdd R hk hkN

/-- If right multiplication by `2` is injective on `R`, then `Hₖ(ℙ ℝ (Fin (N + 1) → ℝ); R)`
vanishes for every even `k > 0`. -/
theorem isZero_singularHomology_projectivization_of_even (h2 : IsRightRegular (2 : R))
    (hk : Even k) (hk0 : k ≠ 0) :
    IsZero (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} R) k).obj
      (ModuleCat.of R R)).obj (TopCat.of (ℙ ℝ (Fin (N + 1) → ℝ)))) :=
  (isZero_singularHomology_of_even (N := N) R h2 hk hk0).of_iso
    (singularHomologyProjectivizationIso (N := N) R k).symm

/-- **Odd-degree integral homology of `ℙ ℝ (Fin (N + 1) → ℝ)`.** For odd `k < N`,
`Hₖ(ℙ ℝ (Fin (N + 1) → ℝ); ℤ) ≅ ℤ/2`. -/
def singularHomologyProjectivizationIntLinearEquivOfOdd (hk : Odd k) (hkN : k < N) :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) k).obj (ModuleCat.of ℤ ℤ)).obj
      (TopCat.of (ℙ ℝ (Fin (N + 1) → ℝ))) ≃ₗ[ℤ] ZMod 2 :=
  (singularHomologyProjectivizationIso (N := N) ℤ k).symm.toLinearEquiv ≪≫ₗ
    singularHomologyIntLinearEquivOfOdd hk hkN

end TauCeti.RealProjectiveSpace
