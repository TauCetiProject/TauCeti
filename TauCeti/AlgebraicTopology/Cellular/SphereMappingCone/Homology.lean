/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ModuleCat.Basic
public import TauCeti.AlgebraicTopology.Cellular.EdgeIncidence
public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.Singular
public import TauCeti.AlgebraicTopology.Cellular.Lacunary
public import TauCeti.AlgebraicTopology.Cellular.SphereMappingCone.Coordinates
public import TauCeti.LinearAlgebra.LinearMap.Ker
public import TauCeti.LinearAlgebra.LinearMap.Range
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

Integrally `H_{n+1}(X; ℤ) ≅ ℤ/m` for every `m`
(`TauCeti.sphereMappingConeSingularHomologyIntLinearEquiv`), and `H_{n+2}(X; ℤ) = 0` for `m ≠ 0`
(`TauCeti.isZero_sphereMappingCone_singularHomology_int_top`), so for `m ≠ 0` the space `X` is the
Moore space `M(ℤ/m, n + 1)`; for `m = 0` it has the homology of `Sⁿ⁺¹ ∨ Sⁿ⁺²`. If `m` is a unit
in `R`, all positive-degree homology with coefficients in `R` vanishes
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
  `TauCeti.isZero_sphereMappingCone_singularHomology_int_top`: the integral homology, that of the
  Moore space `M(ℤ/m, n + 1)` for `m ≠ 0`.

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

/-! ### The cellular differentials -/

/-- The cellular differential of `Sⁿ⁺¹ ∪_f Dⁿ⁺²` out of degree `n + 1` vanishes. For `n ≥ 1` its
target carries no cell, and for `n = 0` both ends of the `1`-cell lie at the single `0`-cell. -/
private lemma cellularChainComplex_d_succ_eq_zero :
    letI := sphereMappingConeCWComplex h f
    (cellularChainComplex (sphereMappingCone f) (ModuleCat.of R R)).d (n + 1) n = 0 := by
  let := sphereMappingConeCWComplex h f
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · let := uniqueCellZeroSphereMappingConeCWComplex h f one_ne_zero
    rw [cellularChainComplex_d, (cellularDifferential_eq_zero_iff _ R 0).2 fun i j ↦
      cellularIncidence_zero_eq_zero_of_subsingleton R i j]
    simp
  · exact cellularChainComplex_d_eq_zero_of_isEmpty_or _ _
      (.inr (isEmpty_cell_sphereMappingConeCWComplex h f (by omega) (by omega) (by omega)))

/-- The cellular differential of `Sⁿ⁺¹ ∪_f Dⁿ⁺²` out of degree `n + 3` vanishes: its source carries
no cell. -/
private lemma cellularChainComplex_d_top_eq_zero :
    letI := sphereMappingConeCWComplex h f
    (cellularChainComplex (sphereMappingCone f) (ModuleCat.of R R)).d (n + 1 + 1 + 1)
      (n + 1 + 1) = 0 := by
  let := sphereMappingConeCWComplex h f
  exact cellularChainComplex_d_eq_zero_of_isEmpty_or _ _
    (.inl (isEmpty_cell_sphereMappingConeCWComplex h f (by omega) (by omega) (by omega)))

/-- The cellular differential of `Sⁿ⁺¹ ∪_f Dⁿ⁺²` out of degree `1` vanishes: for `n = 0` this is
`cellularChainComplex_d_succ_eq_zero`, and for `n ≥ 1` there is no `1`-cell. -/
private lemma cellularChainComplex_d_one_eq_zero :
    letI := sphereMappingConeCWComplex h f
    (cellularChainComplex (sphereMappingCone f) (ModuleCat.of R R)).d 1 0 = 0 := by
  let := sphereMappingConeCWComplex h f
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact cellularChainComplex_d_succ_eq_zero h R f
  · exact cellularChainComplex_d_eq_zero_of_isEmpty_or _ _
      (.inl (isEmpty_cell_sphereMappingConeCWComplex h f (by omega) (by omega) (by omega)))

variable (b : OrthonormalBasis (Fin (n + 1 + 1)) ℝ (EuclideanSpace ℝ ι)) {m : ℤ}
  (hf : (reducedSingularHomologyTopCatSphereIso (ModuleCat.of R R) (n + 1)).inv ≫
      (reducedSingularHomologyFunctor (ModuleCat.of R R) (n + 1)).map
        (TopCat.ofHom (f.comp ⟨ULift.down, continuous_uliftDown⟩)) =
    m • (reducedSingularHomologySphereIso (ModuleCat.of R R) b).inv)

include hf in
/-- In the oriented coordinates of its cells, the cellular differential of `Sⁿ⁺¹ ∪_f Dⁿ⁺²` out of
degree `n + 2` is right multiplication by `m`, as a commuting square of linear maps. -/
private lemma toSpanSingleton_comp_topCoord :
    letI := sphereMappingConeCWComplex h f
    LinearMap.toSpanSingleton R R (m : R) ∘ₗ (sphereMappingConeTopCoord h R f : _ →ₗ[R] R) =
      (sphereMappingConeSphereCoord h R b (uniqueCellSphereCWComplex h n.succ_ne_zero).default f :
          _ →ₗ[R] R) ∘ₗ
        ((cellularChainComplex (sphereMappingCone f) (ModuleCat.of R R)).d (n + 1 + 1)
          (n + 1)).hom := by
  let := sphereMappingConeCWComplex h f
  exact LinearMap.ext fun x ↦ (sphereMappingConeSphereCoord_d h R b
    (uniqueCellSphereCWComplex h n.succ_ne_zero).default f m hf x).symm

/-! ### Cellular homology -/

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
  letI := sphereMappingConeCWComplex h f
  letI := uniqueCellZeroSphereMappingConeCWComplex h f n.succ_ne_zero
  (singularHomologyIsoCellular h R f 0).toLinearEquiv ≪≫ₗ
    HomologicalComplex.homologyEquivOfDEqZero
      (cellularChainComplex (sphereMappingCone f) (ModuleCat.of R R)) (by simp) (by simp)
      (cellularChainCoord _ R default) (cellularChainComplex_d_one_eq_zero h R f)
      ((cellularChainComplex (sphereMappingCone f) (ModuleCat.of R R)).shape 0 0 (by simp))

include hf in
/-- **The homology of a Moore space in the dimension of its sphere.** For `f : Sⁿ⁺¹ → Sⁿ⁺¹` of
degree `m`, in the sense that `f` sends the standard generator of `H_redₙ₊₁(Sⁿ⁺¹; R)` to `m` times
the generator determined by the orthonormal basis `b`, `H_{n+1}(Sⁿ⁺¹ ∪_f Dⁿ⁺²; R) ≅ R / R m`. -/
def sphereMappingConeSingularHomologyLinearEquiv :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) (n + 1)).obj
        (ModuleCat.of R R)).obj (TopCat.of (sphereMappingCone f)) ≃ₗ[R] R ⧸ R ∙ (m : R) :=
  letI := sphereMappingConeCWComplex h f
  (singularHomologyIsoCellular h R f (n + 1)).toLinearEquiv ≪≫ₗ
    HomologicalComplex.homologyEquivQuotOfOutgoingDEqZero
      (cellularChainComplex (sphereMappingCone f) (ModuleCat.of R R)) (by simp) (by simp)
      (sphereMappingConeSphereCoord h R b (uniqueCellSphereCWComplex h n.succ_ne_zero).default f)
      (cellularChainComplex_d_succ_eq_zero h R f)
      ((LinearMap.map_range_eq_range_of_comp_eq _ (sphereMappingConeTopCoord h R f).surjective
        (toSpanSingleton_comp_topCoord h R f b hf)).trans (LinearMap.range_toSpanSingleton _))

include hf in
/-- **The top homology of a Moore space.** For `f : Sⁿ⁺¹ → Sⁿ⁺¹` of degree `m`,
`H_{n+2}(Sⁿ⁺¹ ∪_f Dⁿ⁺²; R)` is the `m`-torsion `{r : R | r * m = 0}` of `R`. -/
def sphereMappingConeSingularHomologyTopLinearEquiv :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) (n + 1 + 1)).obj
        (ModuleCat.of R R)).obj (TopCat.of (sphereMappingCone f)) ≃ₗ[R]
      LinearMap.ker (LinearMap.toSpanSingleton R R (m : R)) :=
  letI := sphereMappingConeCWComplex h f
  (singularHomologyIsoCellular h R f (n + 1 + 1)).toLinearEquiv ≪≫ₗ
    HomologicalComplex.homologyEquivOfIncomingDEqZero
      (cellularChainComplex (sphereMappingCone f) (ModuleCat.of R R)) (by simp) (by simp)
      (sphereMappingConeTopCoord h R f) (cellularChainComplex_d_top_eq_zero h R f)
      (LinearMap.map_ker_eq_ker_of_comp_eq _ (sphereMappingConeTopCoord h R f).surjective
        (sphereMappingConeSphereCoord h R b (uniqueCellSphereCWComplex h n.succ_ne_zero).default
          f).injective (toSpanSingleton_comp_topCoord h R f b hf))

include h in
/-- **The homology of a Moore space vanishes in the other positive degrees.** For every
`f : Sⁿ⁺¹ → Sⁿ⁺¹`, `Hₖ(Sⁿ⁺¹ ∪_f Dⁿ⁺²; R) = 0` for `k` other than `0`, `n + 1` and `n + 2`. -/
theorem isZero_sphereMappingCone_singularHomology_of_ne {k : ℕ} (h0 : k ≠ 0) (h1 : k ≠ n + 1)
    (h2 : k ≠ n + 1 + 1) :
    IsZero (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) k).obj
      (ModuleCat.of R R)).obj (TopCat.of (sphereMappingCone f))) := by
  let := sphereMappingConeCWComplex h f
  have := finite_sphereMappingConeCWComplex h f
  have := isEmpty_cell_sphereMappingConeCWComplex h f h0 h1 h2
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
/-- **The integral homology in the dimension of the sphere.** For `f : Sⁿ⁺¹ → Sⁿ⁺¹` of degree
`m`, `H_{n+1}(Sⁿ⁺¹ ∪_f Dⁿ⁺²; ℤ) ≅ ℤ/m`. For `m ≠ 0` this is the Moore space `M(ℤ/m, n + 1)`
(`TauCeti.isZero_sphereMappingCone_singularHomology_int_top`), and for `m = 0` it is `ℤ`. -/
def sphereMappingConeSingularHomologyIntLinearEquiv :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 1)).obj
        (ModuleCat.of ℤ ℤ)).obj (TopCat.of (sphereMappingCone f)) ≃ₗ[ℤ] ZMod m.natAbs :=
  sphereMappingConeSingularHomologyLinearEquiv h ℤ f b hf ≪≫ₗ
    Submodule.quotEquivOfEq _ _ Ideal.submodule_span_eq ≪≫ₗ
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
