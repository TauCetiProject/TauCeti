/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.EdgeIncidence
public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.Singular
public import TauCeti.AlgebraicTopology.Cellular.Lacunary
public import TauCeti.AlgebraicTopology.Cellular.SphereMappingCone.Coordinates
public import Mathlib.Data.ZMod.QuotientRing

/-!
# The singular homology of a Moore space

Attaching an `(n + 2)`-cell to the sphere `Sⁿ⁺¹` along a map `f : Sⁿ⁺¹ → Sⁿ⁺¹` of degree `m` gives
the space `X = Sⁿ⁺¹ ∪_f Dⁿ⁺²` (`TauCeti.sphereMappingCone f`), a CW complex with one cell in each of
the dimensions `0`, `n + 1` and `n + 2` (`TauCeti.sphereMappingConeCWComplex`). With coefficients in
a ring `R`, its cellular chain complex is `R` in these three degrees and `0` elsewhere, and in the
oriented coordinates of `TauCeti.sphereMappingConeSphereCoord` the differential out of degree
`n + 2` is right multiplication by `m` (`TauCeti.sphereMappingConeSphereCoord_d`). The other
differentials vanish: the differential out of degree `n + 1` lands in the zero group when `n ≥ 1`,
and when `n = 0` both ends of the `1`-cell lie at the single `0`-cell, so its incidence number is
`1 - 1 = 0` (`TauCeti.cellularIncidence_zero_eq_zero_of_subsingleton`). Reading off the
homology of this complex and transporting it along the cellular–singular comparison
`TauCeti.cellularSingularHomologyIsoOfCWComplex` gives

* `H₀(X; R) ≅ R` (`TauCeti.sphereMappingConeSingularHomologyZeroLinearEquiv`);
* `H_{n+1}(X; R) ≅ R / R m` (`TauCeti.sphereMappingConeSingularHomologyLinearEquiv`);
* `H_{n+2}(X; R) ≅ {r : R | r * m = 0}`, the `m`-torsion of `R`
  (`TauCeti.sphereMappingConeSingularHomologyTopLinearEquiv`), which vanishes when right
  multiplication by `m` is injective (`TauCeti.isZero_sphereMappingCone_singularHomology_top`);
* `Hₖ(X; R) = 0` in every other degree
  (`TauCeti.isZero_sphereMappingCone_singularHomology_of_ne`).

Only the last two differentials depend on `f`, so `H₀` and the vanishing in the other degrees hold
for every `f`, and the degree enters only through `H_{n+1}` and `H_{n+2}`.

Integrally `X` is the Moore space `M(ℤ/m, n + 1)`: `H_{n+1}(X; ℤ) ≅ ℤ/m`
(`TauCeti.sphereMappingConeSingularHomologyIntLinearEquiv`) and `H_{n+2}(X; ℤ) = 0` for `m ≠ 0`
(`TauCeti.isZero_sphereMappingCone_singularHomology_int_top`). If `m` is a unit in `R`, all
positive-degree homology with coefficients in `R` vanishes
(`TauCeti.isZero_sphereMappingCone_singularHomology_of_isUnit`). For instance the Moore space
`M(ℤ/3, 2) = S² ∪_f D³`, with `f` of degree `3`, has the mod-`2` homology of a point while its
integral homology is not that of a point.

## Main declarations

* `TauCeti.sphereMappingConeSingularHomologyZeroLinearEquiv`: `H₀(Sⁿ⁺¹ ∪_f Dⁿ⁺²; R) ≅ R`.
* `TauCeti.sphereMappingConeSingularHomologyLinearEquiv`: `H_{n+1}(Sⁿ⁺¹ ∪_f Dⁿ⁺²; R) ≅ R / R m`.
* `TauCeti.sphereMappingConeSingularHomologyTopLinearEquiv`: `H_{n+2}(Sⁿ⁺¹ ∪_f Dⁿ⁺²; R)` is the
  `m`-torsion of `R`.
* `TauCeti.isZero_sphereMappingCone_singularHomology_of_ne`: the homology vanishes in the other
  degrees.
* `TauCeti.isZero_sphereMappingCone_singularHomology_top`: `H_{n+2}` vanishes when right
  multiplication by `m` is injective.
* `TauCeti.isZero_sphereMappingCone_singularHomology_of_isUnit`: the space is `R`-acyclic when the
  degree is a unit of `R`.
* `TauCeti.sphereMappingConeSingularHomologyIntLinearEquiv`,
  `TauCeti.isZero_sphereMappingCone_singularHomology_int_top`: the integral homology of the Moore
  space `M(ℤ/m, n + 1)`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.2, Example 2.40 (the Moore spaces `Sⁿ ∪_f eⁿ⁺¹`).
-/

public section

noncomputable section

open CategoryTheory Limits Metric Set Topology Topology.RelCWComplex

universe u

namespace TauCeti

section Ring

variable {ι : Type u} [Fintype ι] {n : ℕ} (h : Fintype.card ι = n + 1 + 1)
  (R : Type u) [Ring R]
  (f : C(sphere (0 : EuclideanSpace ℝ (Fin (n + 1 + 1))) 1, sphere (0 : EuclideanSpace ℝ ι) 1))

/-! ### The cells -/

/-- The sphere mapping cone `Sⁿ⁺¹ ∪_f Dⁿ⁺²` has exactly one cell in each of the dimensions `0`,
`n + 1` and `n + 2`, and none in any other dimension. -/
private lemma nat_card_cell (k : ℕ) :
    letI := sphereMappingConeCWComplex h f
    Nat.card (cell (sphereMappingCone f) k) =
      if k = 0 ∨ k = n + 1 ∨ k = n + 1 + 1 then 1 else 0 := by
  rw [nat_card_cell_sphereMappingConeCWComplex h f k]
  by_cases h0 : k = 0
  · subst h0; simp
  by_cases h1 : k = n + 1
  · subst h1; simp
  by_cases h2 : k = n + 1 + 1
  · subst h2; simp
  simp [h0, h1, h2]

/-- In a dimension other than `0`, `n + 1` and `n + 2`, the sphere mapping cone has no cell. -/
private lemma isEmpty_cell {k : ℕ} (h0 : k ≠ 0) (h1 : k ≠ n + 1) (h2 : k ≠ n + 1 + 1) :
    letI := sphereMappingConeCWComplex h f
    IsEmpty (cell (sphereMappingCone f) k) := by
  let := sphereMappingConeCWComplex h f
  have := finite_sphereMappingConeCWComplex h f
  have : Finite (cell (sphereMappingCone f) k) := RelCWComplex.FiniteType.finite_cell k
  have hc := nat_card_cell h f k
  simp only [show ¬(k = 0 ∨ k = n + 1 ∨ k = n + 1 + 1) by omega, ↓reduceIte] at hc
  exact Finite.card_eq_zero_iff.mp hc

/-- In the dimensions `0`, `n + 1` and `n + 2`, the sphere mapping cone has a unique cell. -/
private lemma nat_card_cell_eq_one {k : ℕ} (hk : k = 0 ∨ k = n + 1 ∨ k = n + 1 + 1) :
    letI := sphereMappingConeCWComplex h f
    Nat.card (cell (sphereMappingCone f) k) = 1 := by
  rw [nat_card_cell h f k]
  simp [hk]

/-- The sphere mapping cone has a single `0`-cell. -/
private lemma subsingleton_and_nonempty_cell_zero :
    letI := sphereMappingConeCWComplex h f
    Subsingleton (cell (sphereMappingCone f) 0) ∧ Nonempty (cell (sphereMappingCone f) 0) := by
  let := sphereMappingConeCWComplex h f
  have := finite_sphereMappingConeCWComplex h f
  have : Finite (cell (sphereMappingCone f) 0) := RelCWComplex.FiniteType.finite_cell 0
  exact Nat.card_eq_one_iff_unique.mp (nat_card_cell_eq_one h f (by omega))

/-- The `0`-cell of the sphere mapping cone. -/
private def cellZero :
    letI := sphereMappingConeCWComplex h f
    cell (sphereMappingCone f) 0 :=
  Classical.choice (subsingleton_and_nonempty_cell_zero h f).2

/-! ### The cellular differentials -/

/-- The cellular differential of `Sⁿ⁺¹ ∪_f Dⁿ⁺²` out of degree `n + 1` vanishes. For `n ≥ 1` its
target carries no cell, and for `n = 0` both ends of the `1`-cell lie at the single `0`-cell. -/
private lemma cellularChainComplex_d_succ_eq_zero :
    letI := sphereMappingConeCWComplex h f
    (cellularChainComplex (sphereMappingCone f) (ModuleCat.of R R)).d (n + 1) n = 0 := by
  let := sphereMappingConeCWComplex h f
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have := (subsingleton_and_nonempty_cell_zero h f).1
    rw [cellularChainComplex_d, (cellularDifferential_eq_zero_iff _ R 0).2 fun i j ↦
      cellularIncidence_zero_eq_zero_of_subsingleton R i j]
    simp
  · exact cellularChainComplex_d_eq_zero_of_isEmpty_or _ _
      (.inr (isEmpty_cell h f (by omega) (by omega) (by omega)))

/-- The cellular differential of `Sⁿ⁺¹ ∪_f Dⁿ⁺²` out of degree `n + 3` vanishes: its source carries
no cell. -/
private lemma cellularChainComplex_d_top_eq_zero :
    letI := sphereMappingConeCWComplex h f
    (cellularChainComplex (sphereMappingCone f) (ModuleCat.of R R)).d (n + 1 + 1 + 1)
      (n + 1 + 1) = 0 := by
  let := sphereMappingConeCWComplex h f
  exact cellularChainComplex_d_eq_zero_of_isEmpty_or _ _
    (.inl (isEmpty_cell h f (by omega) (by omega) (by omega)))

/-- The cellular differential of `Sⁿ⁺¹ ∪_f Dⁿ⁺²` out of degree `1` vanishes: for `n = 0` this is
`cellularChainComplex_d_succ_eq_zero`, and for `n ≥ 1` there is no `1`-cell. -/
private lemma cellularChainComplex_d_one_eq_zero :
    letI := sphereMappingConeCWComplex h f
    (cellularChainComplex (sphereMappingCone f) (ModuleCat.of R R)).d 1 0 = 0 := by
  let := sphereMappingConeCWComplex h f
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact cellularChainComplex_d_succ_eq_zero h R f
  · exact cellularChainComplex_d_eq_zero_of_isEmpty_or _ _
      (.inl (isEmpty_cell h f (by omega) (by omega) (by omega)))

/-- The cellular homology of `Sⁿ⁺¹ ∪_f Dⁿ⁺²` in degree `0` is `R`. -/
private def cellularHomologyZeroLinearEquiv :
    letI := sphereMappingConeCWComplex h f
    (cellularChainComplex (sphereMappingCone f) (ModuleCat.of R R)).homology 0 ≃ₗ[R] R :=
  letI := sphereMappingConeCWComplex h f
  letI := (subsingleton_and_nonempty_cell_zero h f).1
  let K := cellularChainComplex (sphereMappingCone f) (ModuleCat.of R R)
  (K.homologyIsoSc' 1 0 0 (by simp) (by simp) ≪≫
      (K.sc' 1 0 0).asIsoHomologyι (K.shape 0 0 (by simp)) ≪≫
        (K.sc' 1 0 0).moduleCatOpcyclesIso).toLinearEquiv ≪≫ₗ
    Submodule.quotEquivOfEqBot _ (by
      rw [LinearMap.range_eq_bot]
      exact congrArg ModuleCat.Hom.hom (cellularChainComplex_d_one_eq_zero h R f)) ≪≫ₗ
    cellularChainCoord _ R (cellZero h f)

/-- The `(n + 1)`-cell of the sphere `Sⁿ⁺¹`, the unique cell of positive dimension of
`TauCeti.sphereCWComplex`. -/
private def sphereCell :
    letI := sphereCWComplex h; cell (sphere (0 : EuclideanSpace ℝ ι) 1) (n + 1) :=
  Classical.choice (by
    let := sphereCWComplex h
    have := finite_sphereCWComplex h
    have hc := nat_card_cell_sphereCWComplex h (n + 1)
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, zero_add] at hc
    exact (Nat.card_pos_iff.mp (by omega)).1)

variable (b : OrthonormalBasis (Fin (n + 1 + 1)) ℝ (EuclideanSpace ℝ ι)) {m : ℤ}
  (hf : (reducedSingularHomologyTopCatSphereIso (ModuleCat.of R R) (n + 1)).inv ≫
      (reducedSingularHomologyFunctor (ModuleCat.of R R) (n + 1)).map
        (TopCat.ofHom (f.comp ⟨ULift.down, continuous_uliftDown⟩)) =
    m • (reducedSingularHomologySphereIso (ModuleCat.of R R) b).inv)

include hf in
/-- In the oriented coordinate of the `(n + 1)`-cell, the boundaries in degree `n + 1` of the
cellular chain complex of `Sⁿ⁺¹ ∪_f Dⁿ⁺²` are the left ideal `R m`. -/
private lemma map_range_d_eq_span :
    letI := sphereMappingConeCWComplex h f
    (LinearMap.range ((cellularChainComplex (sphereMappingCone f) (ModuleCat.of R R)).d
        (n + 1 + 1) (n + 1)).hom).map
        (sphereMappingConeSphereCoord h R b (sphereCell h) f : _ →ₗ[R] R) =
      R ∙ (m : R) := by
  let := sphereMappingConeCWComplex h f
  have hd := sphereMappingConeSphereCoord_d h R b (sphereCell h) f m hf
  ext y
  simp only [Submodule.mem_map, LinearMap.mem_range, Submodule.mem_span_singleton, smul_eq_mul]
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨sphereMappingConeTopCoord h R f x, (hd x).symm⟩
  · rintro ⟨a, rfl⟩
    refine ⟨_, ⟨(sphereMappingConeTopCoord h R f).symm a, rfl⟩, (hd _).trans ?_⟩
    rw [LinearEquiv.apply_symm_apply]

include hf in
/-- In the coordinate of the `(n + 2)`-cell, the cycles in degree `n + 2` of the cellular chain
complex of `Sⁿ⁺¹ ∪_f Dⁿ⁺²` are the `m`-torsion of `R`. -/
private lemma map_ker_d_eq_ker :
    letI := sphereMappingConeCWComplex h f
    (LinearMap.ker ((cellularChainComplex (sphereMappingCone f) (ModuleCat.of R R)).d
        (n + 1 + 1) (n + 1)).hom).map (sphereMappingConeTopCoord h R f : _ →ₗ[R] R) =
      LinearMap.ker (LinearMap.toSpanSingleton R R (m : R)) := by
  let := sphereMappingConeCWComplex h f
  have hd := sphereMappingConeSphereCoord_d h R b (sphereCell h) f m hf
  have key (x : (cellularChainComplex (sphereMappingCone f) (ModuleCat.of R R)).X (n + 1 + 1)) :
      (cellularChainComplex (sphereMappingCone f) (ModuleCat.of R R)).d (n + 1 + 1) (n + 1) x =
          0 ↔ sphereMappingConeTopCoord h R f x * m = 0 := by
    rw [← (sphereMappingConeSphereCoord h R b (sphereCell h) f).map_eq_zero_iff, hd]
  ext y
  simp only [Submodule.mem_map, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, smul_eq_mul]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (key x).1 hx
  · intro hy
    exact ⟨(sphereMappingConeTopCoord h R f).symm y,
      (key _).2 (by rwa [LinearEquiv.apply_symm_apply]), LinearEquiv.apply_symm_apply _ _⟩

/-! ### Cellular homology -/

include hf in
/-- The cellular homology of `Sⁿ⁺¹ ∪_f Dⁿ⁺²` in degree `n + 1` is `R / R m`. -/
private def cellularHomologyLinearEquiv :
    letI := sphereMappingConeCWComplex h f
    (cellularChainComplex (sphereMappingCone f) (ModuleCat.of R R)).homology (n + 1) ≃ₗ[R]
      R ⧸ R ∙ (m : R) :=
  letI := sphereMappingConeCWComplex h f
  let K := cellularChainComplex (sphereMappingCone f) (ModuleCat.of R R)
  (K.homologyIsoSc' (n + 1 + 1) (n + 1) n (by simp) (by simp) ≪≫
      (K.sc' (n + 1 + 1) (n + 1) n).asIsoHomologyι (cellularChainComplex_d_succ_eq_zero h R f) ≪≫
        (K.sc' (n + 1 + 1) (n + 1) n).moduleCatOpcyclesIso).toLinearEquiv ≪≫ₗ
    Submodule.Quotient.equiv _ _ (sphereMappingConeSphereCoord h R b (sphereCell h) f)
      (map_range_d_eq_span h R f b hf)

include hf in
/-- The cellular homology of `Sⁿ⁺¹ ∪_f Dⁿ⁺²` in degree `n + 2` is the `m`-torsion of `R`. -/
private def cellularHomologyTopLinearEquiv :
    letI := sphereMappingConeCWComplex h f
    (cellularChainComplex (sphereMappingCone f) (ModuleCat.of R R)).homology (n + 1 + 1) ≃ₗ[R]
      LinearMap.ker (LinearMap.toSpanSingleton R R (m : R)) :=
  letI := sphereMappingConeCWComplex h f
  let K := cellularChainComplex (sphereMappingCone f) (ModuleCat.of R R)
  (K.homologyIsoSc' (n + 1 + 1 + 1) (n + 1 + 1) (n + 1) (by simp) (by simp) ≪≫
      ((K.sc' (n + 1 + 1 + 1) (n + 1 + 1) (n + 1)).asIsoHomologyπ
        (cellularChainComplex_d_top_eq_zero h R f)).symm ≪≫
        (K.sc' (n + 1 + 1 + 1) (n + 1 + 1) (n + 1)).moduleCatCyclesIso).toLinearEquiv ≪≫ₗ
    LinearEquiv.ofSubmodules (sphereMappingConeTopCoord h R f) _ _
      (map_ker_d_eq_ker h R f b hf)

/-- The singular homology of `Sⁿ⁺¹ ∪_f Dⁿ⁺²` is the homology of its cellular chain complex. -/
private def singularHomologyIsoCellular (k : ℕ) :
    letI := sphereMappingConeCWComplex h f
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) k).obj
        (ModuleCat.of R R)).obj (TopCat.of (sphereMappingCone f)) ≅
      (cellularChainComplex (sphereMappingCone f) (ModuleCat.of R R)).homology k :=
  letI := sphereMappingConeCWComplex h f
  have := finite_sphereMappingConeCWComplex h f
  (cellularSingularHomologyIsoOfCWComplex (sphereMappingCone f) (ModuleCat.of R R) k).symm

/-! ### Singular homology -/

/-- **The homology of a Moore space in degree `0`.** For every `f : Sⁿ⁺¹ → Sⁿ⁺¹`,
`H₀(Sⁿ⁺¹ ∪_f Dⁿ⁺²; R) ≅ R`. -/
def sphereMappingConeSingularHomologyZeroLinearEquiv :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) 0).obj
        (ModuleCat.of R R)).obj (TopCat.of (sphereMappingCone f)) ≃ₗ[R] R :=
  (singularHomologyIsoCellular h R f 0).toLinearEquiv ≪≫ₗ cellularHomologyZeroLinearEquiv h R f

include hf in
/-- **The homology of a Moore space in the dimension of its sphere.** For `f : Sⁿ⁺¹ → Sⁿ⁺¹` of
degree `m`, in the sense that `f` sends the standard generator of `H_redₙ₊₁(Sⁿ⁺¹; R)` to `m` times
the generator determined by the orthonormal basis `b`, `H_{n+1}(Sⁿ⁺¹ ∪_f Dⁿ⁺²; R) ≅ R / R m`. -/
def sphereMappingConeSingularHomologyLinearEquiv :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) (n + 1)).obj
        (ModuleCat.of R R)).obj (TopCat.of (sphereMappingCone f)) ≃ₗ[R] R ⧸ R ∙ (m : R) :=
  (singularHomologyIsoCellular h R f (n + 1)).toLinearEquiv ≪≫ₗ
    cellularHomologyLinearEquiv h R f b hf

include hf in
/-- **The top homology of a Moore space.** For `f : Sⁿ⁺¹ → Sⁿ⁺¹` of degree `m`,
`H_{n+2}(Sⁿ⁺¹ ∪_f Dⁿ⁺²; R)` is the `m`-torsion `{r : R | r * m = 0}` of `R`. -/
def sphereMappingConeSingularHomologyTopLinearEquiv :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) (n + 1 + 1)).obj
        (ModuleCat.of R R)).obj (TopCat.of (sphereMappingCone f)) ≃ₗ[R]
      LinearMap.ker (LinearMap.toSpanSingleton R R (m : R)) :=
  (singularHomologyIsoCellular h R f (n + 1 + 1)).toLinearEquiv ≪≫ₗ
    cellularHomologyTopLinearEquiv h R f b hf

include h in
/-- **The homology of a Moore space vanishes in the other positive degrees.** For every
`f : Sⁿ⁺¹ → Sⁿ⁺¹`, `Hₖ(Sⁿ⁺¹ ∪_f Dⁿ⁺²; R) = 0` for `k` other than `0`, `n + 1` and `n + 2`. -/
theorem isZero_sphereMappingCone_singularHomology_of_ne {k : ℕ} (h0 : k ≠ 0) (h1 : k ≠ n + 1)
    (h2 : k ≠ n + 1 + 1) :
    IsZero (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) k).obj
      (ModuleCat.of R R)).obj (TopCat.of (sphereMappingCone f))) := by
  let := sphereMappingConeCWComplex h f
  have := finite_sphereMappingConeCWComplex h f
  have := isEmpty_cell h f h0 h1 h2
  exact (isZero_singularHomology_complexBasePair_of_isEmpty_cell _ _ k).of_iso
    (singularHomologyIsoCellular h R f k ≪≫ cellularSingularHomologyIso _ _ k)

include h hf in
/-- **The top homology of a Moore space vanishes without `m`-torsion.** If `f : Sⁿ⁺¹ → Sⁿ⁺¹` has
degree `m` and right multiplication by `m` is injective on `R`, then
`H_{n+2}(Sⁿ⁺¹ ∪_f Dⁿ⁺²; R) = 0`. -/
theorem isZero_sphereMappingCone_singularHomology_top (hm : IsRightRegular (m : R)) :
    IsZero (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) (n + 1 + 1)).obj
      (ModuleCat.of R R)).obj (TopCat.of (sphereMappingCone f))) := by
  have : Subsingleton (LinearMap.ker (LinearMap.toSpanSingleton R R (m : R))) :=
    ⟨fun x y ↦ Subtype.ext <| by
      have hx := x.property
      have hy := y.property
      simp only [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, smul_eq_mul] at hx hy
      exact hm (hx.trans hy.symm)⟩
  exact ModuleCat.isZero_iff_subsingleton.2
    (sphereMappingConeSingularHomologyTopLinearEquiv h R f b hf).toEquiv.subsingleton

include h hf in
/-- **A Moore space is acyclic over a ring in which its degree is a unit.** If `f : Sⁿ⁺¹ → Sⁿ⁺¹`
has degree `m` and `m` is a unit of `R`, then `Hₖ(Sⁿ⁺¹ ∪_f Dⁿ⁺²; R) = 0` for every `k ≠ 0`. For
instance the Moore space `M(ℤ/3, 2) = S² ∪_f D³`, with `f` of degree `3`, has the homology of a
point with coefficients in `ZMod 2`. -/
theorem isZero_sphereMappingCone_singularHomology_of_isUnit (hm : IsUnit (m : R)) {k : ℕ}
    (hk : k ≠ 0) :
    IsZero (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) k).obj
      (ModuleCat.of R R)).obj (TopCat.of (sphereMappingCone f))) := by
  by_cases h1 : k = n + 1
  · subst h1
    have : Subsingleton (R ⧸ R ∙ (m : R)) :=
      Submodule.Quotient.subsingleton_iff.2 <| eq_top_iff.2 fun y _ ↦
        Submodule.mem_span_singleton.2 ⟨y * ↑hm.unit⁻¹, by simp [smul_eq_mul, mul_assoc]⟩
    exact ModuleCat.isZero_iff_subsingleton.2
      (sphereMappingConeSingularHomologyLinearEquiv h R f b hf).toEquiv.subsingleton
  by_cases h2 : k = n + 1 + 1
  · subst h2
    exact isZero_sphereMappingCone_singularHomology_top h R f b hf hm.isRegular.right
  exact isZero_sphereMappingCone_singularHomology_of_ne h R f hk h1 h2

end Ring

/-! ### Integral homology -/

section Int

variable {ι : Type} [Fintype ι] {n : ℕ} (h : Fintype.card ι = n + 1 + 1)
  (f : C(sphere (0 : EuclideanSpace ℝ (Fin (n + 1 + 1))) 1, sphere (0 : EuclideanSpace ℝ ι) 1))
  (b : OrthonormalBasis (Fin (n + 1 + 1)) ℝ (EuclideanSpace ℝ ι)) {m : ℤ}
  (hf : (reducedSingularHomologyTopCatSphereIso (ModuleCat.of ℤ ℤ) (n + 1)).inv ≫
      (reducedSingularHomologyFunctor (ModuleCat.of ℤ ℤ) (n + 1)).map
        (TopCat.ofHom (f.comp ⟨ULift.down, continuous_uliftDown⟩)) =
    m • (reducedSingularHomologySphereIso (ModuleCat.of ℤ ℤ) b).inv)

include hf in
/-- **The Moore space `M(ℤ/m, n + 1)`.** For `f : Sⁿ⁺¹ → Sⁿ⁺¹` of degree `m`,
`H_{n+1}(Sⁿ⁺¹ ∪_f Dⁿ⁺²; ℤ) ≅ ℤ/m`. -/
def sphereMappingConeSingularHomologyIntLinearEquiv :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 1)).obj
        (ModuleCat.of ℤ ℤ)).obj (TopCat.of (sphereMappingCone f)) ≃ₗ[ℤ] ZMod m.natAbs :=
  sphereMappingConeSingularHomologyLinearEquiv h ℤ f b hf ≪≫ₗ
    Submodule.quotEquivOfEq _ _ (by simp [Ideal.span]) ≪≫ₗ
    (Int.quotientSpanEquivZMod m).toAddEquiv.toIntLinearEquiv

include h hf in
/-- **The top integral homology of a Moore space vanishes.** For `f : Sⁿ⁺¹ → Sⁿ⁺¹` of degree
`m ≠ 0`, `H_{n+2}(Sⁿ⁺¹ ∪_f Dⁿ⁺²; ℤ) = 0`. -/
theorem isZero_sphereMappingCone_singularHomology_int_top (hm : m ≠ 0) :
    IsZero (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 1 + 1)).obj
      (ModuleCat.of ℤ ℤ)).obj (TopCat.of (sphereMappingCone f))) :=
  isZero_sphereMappingCone_singularHomology_top h ℤ f b hf
    (by simpa using (IsRegular.of_ne_zero hm).right)

end Int

end TauCeti
