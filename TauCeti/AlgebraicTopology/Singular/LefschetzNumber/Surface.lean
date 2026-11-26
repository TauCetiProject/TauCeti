/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.CompactSupport.Duality.Coefficients
public import TauCeti.AlgebraicTopology.Cohomology.UniversalCoefficient.Field
public import TauCeti.AlgebraicTopology.Singular.LefschetzNumber.Basic
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.FlatCoefficients
public import TauCeti.AlgebraicTopology.Singular.Reduced
import Mathlib.Algebra.Module.Rat
import Mathlib.RingTheory.Flat.TorsionFree
import TauCeti.LinearAlgebra.BilinearForm.Isometry.Charpoly

/-!
# The Lefschetz zeta function of a self-map of a closed oriented surface

Let `M` be a closed connected surface with a homological orientation, `k` a field of
characteristic zero and `f : M → M` a continuous map of degree `d`. On homology with coefficients
in `k`, the map `f` acts as the identity on `H₀(M; k) = k`, since `M` is path-connected; by `d` on
`H₂(M; k) = k`, through its fundamental class
(`TauCeti.HomologicalOrientation.singularHomologyMap_eq_degree_smul_id`); and the homology
vanishes above degree two. Writing `P = f_* : H₁(M; k) → H₁(M; k)`, the Lefschetz number is
therefore

`L(f) = 1 - tr P + d`

(`TauCeti.HomologicalOrientation.lefschetzNumber_eq_one_sub_trace_add_degree`), and the general
determinant formula `ContinuousMap.lefschetzZeta_mul_prod_even_eq_prod_odd` for the Lefschetz zeta
function `ζ_f = exp (∑ₙ L(fⁿ) tⁿ / n)` becomes

`ζ_f · (1 - t) (1 - d t) = det (1 - t P)`

(`TauCeti.HomologicalOrientation.lefschetzZeta_mul_eq_reverse_charpoly`). The finite CW type of
`M` is an explicit hypothesis there, which makes `H₁(M; k)` finite-dimensional. For a map of
degree one, such as an orientation-preserving homeomorphism, this is the homology determinant
formula

`ζ_f = det (1 - t P) / (1 - t)²`

(`TauCeti.HomologicalOrientation.lefschetzZeta_eq_reverse_charpoly_mul_inv_of_degree_eq_one`).

**Maps of degree one.** A map of degree one preserves the cup pairing
`(α, β) ↦ ⟨α ⌣ β, [M]_k⟩` on `H¹(M; k)`
(`TauCeti.HomologicalOrientation.isIsometry_singularCohomologyMap_of_degree_eq_one`). This
pairing is nondegenerate by Poincaré duality and, when `2 ≠ 0` in `k`, alternating by graded
commutativity, so in a symplectic basis `f^*` is a symplectic matrix, and `P = f_*` is its
transpose. Writing `2 g = dim H₁(M; k)` and `p (t) = det (1 - t P)`, the identities for
symplectic matrices of `TauCeti.LinearAlgebra.BilinearForm.Isometry.Charpoly` give

* self-reciprocity, `t ^ (2 g) p (1 / t) = p (t)`
  (`TauCeti.HomologicalOrientation.reflect_reverse_charpoly_singularHomologyMap_one`);
* the reciprocal-polynomial identity `p' (1) = g det (1 - P)`
  (`TauCeti.HomologicalOrientation.derivative_eval_one_reverse_charpoly_singularHomologyMap_one`);
* the coarse coefficients of the Lefschetz zeta function: the coefficient of `t ^ a` in `ζ_f` is
  `det (1 - P) (a + 1 - g)` for every `a ≥ 2 g - 1`
  (`TauCeti.HomologicalOrientation.coeff_lefschetzZeta_of_degree_eq_one`).

For the orientation-preserving monodromy `φ` of a surface mapping torus, the coefficients of
`ζ_φ` from degree `2 g - 1` on are thus `det (1 - P) (a + 1 - g)`. When every iterate of `φ` has
only nondegenerate fixed points, the Lefschetz fixed point theorem, which is not proved here,
identifies `ζ_φ` with the dynamical zeta function that counts the periodic points of `φ` weighted
by their fixed-point indices `±1`, rather than the unweighted Artin–Mazur zeta function.

## Main results

* `TauCeti.HomologicalOrientation.lefschetzNumber_eq_one_sub_trace_add_degree`:
  `L(f) = 1 - tr (f_* | H₁(M; k)) + deg f`.
* `TauCeti.HomologicalOrientation.lefschetzZeta_mul_eq_reverse_charpoly`:
  `ζ_f · (1 - t) (1 - (deg f) t) = det (1 - t f_* | H₁(M; k))`.
* `TauCeti.HomologicalOrientation.lefschetzZeta_eq_reverse_charpoly_mul_inv`: the same identity
  solved for `ζ_f`.
* `TauCeti.HomologicalOrientation.lefschetzZeta_eq_reverse_charpoly_mul_inv_of_degree_eq_one`:
  for a map of degree one, `ζ_f = det (1 - t f_* | H₁(M; k)) / (1 - t)²`.
* `TauCeti.HomologicalOrientation.reflect_reverse_charpoly_singularHomologyMap_one`,
  `TauCeti.HomologicalOrientation.derivative_eval_one_reverse_charpoly_singularHomologyMap_one`:
  for a map of degree one, `det (1 - t f_* | H₁(M; k))` is self-reciprocal, and its derivative at
  `1` is `g det (1 - f_*)` with `2 g = dim H₁(M; k)`.
* `TauCeti.HomologicalOrientation.coeff_lefschetzZeta_of_degree_eq_one`: for a map of degree one,
  the coefficient of `t ^ a` in `ζ_f` is `det (1 - f_*) (a + 1 - g)` for `a ≥ 2 g - 1`.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.C (the Lefschetz number).
* S. Smale, *Differentiable dynamical systems*, Bull. Amer. Math. Soc. 73 (1967), 747–817 (the
  Lefschetz zeta function and its determinant formula).
-/

public section

noncomputable section

open CategoryTheory Module TauCeti
open scoped PowerSeries

namespace TauCeti.HomologicalOrientation

variable {M E : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
  (o : HomologicalOrientation M E 2) (hE : finrank ℝ E = 2) (k : Type) [Field k]

omit [ConnectedSpace M] in
include hE in
/-- The homology of a compact surface vanishes above degree two. -/
private theorem subsingleton_singularChains_homology_of_notMem_range_three :
    ∀ i ∉ Finset.range 3, Subsingleton (((singularChains k).obj (TopCat.of M)).homology i) :=
  fun _ hi ↦ ModuleCat.isZero_iff_subsingleton.1 (isZero_singularHomology_of_compactSpace
    (M := M) (ModuleCat.of k k) hE (by simp at hi; omega))

omit [T2Space M] [CompactSpace M] [FiniteDimensional ℝ E] in
include E in
/-- `M` is path-connected, so `H₀(M; k) = k`, on which a self-map acts by the identity. -/
private theorem finrank_homology_zero_and_singularHomologyMap_zero (f : C(M, M)) :
    finrank k (((singularChains k).obj (TopCat.of M)).homology 0) = 1 ∧
      ContinuousMap.singularHomologyMap k 0 f = LinearMap.id := by
  have := ChartedSpace.locallyPathConnectedSpace E M
  have : PathConnectedSpace M := pathConnectedSpace_iff_connectedSpace.mpr inferInstance
  exact ⟨finrank_singularHomology₀_eq_one (TopCat.of M), congrArg ModuleCat.Hom.hom
    (singularHomology₀_map_eq_id_of_pathConnectedSpace (ModuleCat.of k k) (TopCat.ofHom f))⟩

/-- **The Lefschetz number of a self-map of a closed oriented surface.** For a self-map `f` of a
compact connected homologically oriented surface and a field `k` of characteristic zero,
`L(f) = 1 - tr (f_* | H₁(M; k)) + deg f`. -/
theorem lefschetzNumber_eq_one_sub_trace_add_degree [Algebra ℚ k] (f : C(M, M)) :
    f.lefschetzNumber k =
      1 - LinearMap.trace k _ (ContinuousMap.singularHomologyMap k 1 f) + o.degree o hE f := by
  have : HasUniqueDiv k := .of_module_rat k
  obtain ⟨h₀, hf₀⟩ := finrank_homology_zero_and_singularHomologyMap_zero (E := E) k f
  have h₂ := o.finrank_singularChains_homology_eq_one hE k
  have := Module.finite_of_finrank_eq_succ h₀
  have := Module.finite_of_finrank_eq_succ h₂
  rw [ContinuousMap.lefschetzNumber_eq_sum
      (subsingleton_singularChains_homology_of_notMem_range_three hE k),
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, hf₀,
    o.singularHomologyMap_eq_degree_smul_id hE, LinearMap.trace_id, map_smul, LinearMap.trace_id,
    h₀, h₂]
  simp
  ring

omit [T2Space M] [CompactSpace M] [FiniteDimensional ℝ E] in
include E in
/-- A self-map acts on `H₀(M; k) = k` by the identity, so `det (1 - t f_* | H₀(M; k)) = 1 - t`. -/
private theorem reverse_charpoly_singularHomologyMap_zero [FiniteCWType M] (f : C(M, M)) :
    (ContinuousMap.singularHomologyMap k 0 f).charpoly.reverse = 1 - Polynomial.X := by
  obtain ⟨h₀, hf₀⟩ := finrank_homology_zero_and_singularHomologyMap_zero (E := E) k f
  rw [hf₀, ← one_smul k LinearMap.id, LinearMap.reverse_charpoly_smul_id, h₀]
  simp

/-- A self-map acts on `H₂(M; k) = k` by its degree `d`, so
`det (1 - t f_* | H₂(M; k)) = 1 - d t`. -/
private theorem reverse_charpoly_singularHomologyMap_two [Algebra ℚ k] [FiniteCWType M]
    (f : C(M, M)) :
    (ContinuousMap.singularHomologyMap k 2 f).charpoly.reverse =
      1 - Polynomial.C (o.degree o hE f : k) * Polynomial.X := by
  have : HasUniqueDiv k := .of_module_rat k
  rw [o.singularHomologyMap_eq_degree_smul_id hE, LinearMap.reverse_charpoly_smul_id,
    o.finrank_singularChains_homology_eq_one hE k, pow_one]

/-- **The Lefschetz zeta function of a self-map of a closed oriented surface.** For a self-map `f`
of a compact connected homologically oriented surface of finite CW type and a field `k` of
characteristic zero, `ζ_f · (1 - t) (1 - (deg f) t) = det (1 - t f_* | H₁(M; k))`. -/
theorem lefschetzZeta_mul_eq_reverse_charpoly [Algebra ℚ k] [FiniteCWType M] (f : C(M, M)) :
    f.lefschetzZeta k * ((1 - PowerSeries.X) *
      (1 - PowerSeries.C (o.degree o hE f : k) * PowerSeries.X)) =
      ((ContinuousMap.singularHomologyMap k 1 f).charpoly.reverse : k⟦X⟧) := by
  have h := ContinuousMap.lefschetzZeta_mul_prod_even_eq_prod_odd
    (subsingleton_singularChains_homology_of_notMem_range_three hE k) f
  rw [show {i ∈ Finset.range 3 | Even i} = {0, 2} by decide,
    show {i ∈ Finset.range 3 | Odd i} = {1} by decide, Finset.prod_pair (by norm_num),
    Finset.prod_singleton, reverse_charpoly_singularHomologyMap_zero (E := E) k f,
    o.reverse_charpoly_singularHomologyMap_two hE k f] at h
  simpa [mul_assoc, Polynomial.coe_C, -map_intCast, -eq_intCast] using h

/-- **The Lefschetz zeta function of a self-map of a closed oriented surface**, solved for `ζ_f`:
`ζ_f = det (1 - t f_* | H₁(M; k)) / ((1 - t) (1 - (deg f) t))`. -/
theorem lefschetzZeta_eq_reverse_charpoly_mul_inv [Algebra ℚ k] [FiniteCWType M] (f : C(M, M)) :
    f.lefschetzZeta k = ((ContinuousMap.singularHomologyMap k 1 f).charpoly.reverse : k⟦X⟧) *
      ((1 - PowerSeries.X) * (1 - PowerSeries.C (o.degree o hE f : k) * PowerSeries.X))⁻¹ :=
  (PowerSeries.eq_mul_inv_iff_mul_eq (by simp)).2
    (o.lefschetzZeta_mul_eq_reverse_charpoly hE k f)

/-- **The homology determinant formula for a surface map of degree one.** For a self-map `f` of
degree one of a compact connected homologically oriented surface of finite CW type, such as an
orientation-preserving homeomorphism, `ζ_f = det (1 - t f_* | H₁(M; k)) / (1 - t)²`. -/
theorem lefschetzZeta_eq_reverse_charpoly_mul_inv_of_degree_eq_one [Algebra ℚ k]
    [FiniteCWType M] {f : C(M, M)} (hf : o.degree o hE f = 1) :
    f.lefschetzZeta k = ((ContinuousMap.singularHomologyMap k 1 f).charpoly.reverse : k⟦X⟧) *
      ((1 - PowerSeries.X) ^ 2)⁻¹ := by
  rw [o.lefschetzZeta_eq_reverse_charpoly_mul_inv hE k f, hf]
  simp [sq]

/-! ### Self-maps of degree one act symplectically -/

section Symplectic

open MonoidalCategory

/-- For a self-map `f` of degree one and a field `k` with `2 ≠ 0`, the cup pairing on `H¹(M; k)`
against `[M]_k` is a nondegenerate alternating form of which `f^*` is an isometry. -/
private theorem isAlt_and_nondegenerate_and_isIsometry_singularCupPairing (h2 : (2 : k) ≠ 0)
    {f : C(M, M)} (hf : o.degree o hE f = 1) :
    letI B := (TopCat.of M).singularCupPairing k (show 1 + 1 = 2 from rfl)
      (o.fundamentalClassOver hE k)
    B.IsAlt ∧ B.Nondegenerate ∧
      BilinForm.IsIsometry B (TopCat.singularCohomologyMap (TopCat.ofHom f) 1).hom :=
  ⟨(TopCat.of M).isAlt_singularCupPairing k (IsRegular.of_ne_zero h2).left odd_one _ _,
    o.nondegenerate_singularCupPairing_fundamentalClassOver hE _,
    o.isIsometry_singularCohomologyMap_of_degree_eq_one hE k _ hf⟩

variable [FiniteCWType M]

omit [T2Space M] [CompactSpace M] [ConnectedSpace M] in
/-- Over a field, `H¹(M; k)` is finite-dimensional, like `H₁(M; k)`. -/
private theorem finite_singularCohomology_one :
    Module.Finite k ((TopCat.of M).singularCohomology (𝟙_ (ModuleCat k)) k (𝟙_ (ModuleCat k)) 1) :=
  -- The singular homology functor is by definition the homology of `singularChains k`
  -- (`TauCeti.singularHomologyFunctor_obj_obj`).
  ((TopCat.of M).finite_singularCohomology_iff 1).2
    (finiteDimensional_singularChains_homology M k 1)

omit [T2Space M] [CompactSpace M] [ConnectedSpace M] in
/-- Over a field, `f_*` on `H₁(M; k)` has the characteristic polynomial, the dimension and the
determinant `det (1 - ·)` of `f^*` on `H¹(M; k)`, its transpose. -/
private theorem charpoly_and_finrank_and_det_singularHomologyMap_one (f : C(M, M)) :
    haveI := finite_singularCohomology_one (M := M) k
    (ContinuousMap.singularHomologyMap k 1 f).charpoly =
        (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat k)) (k := k) (M := 𝟙_ (ModuleCat k))
          (TopCat.ofHom f) 1).hom.charpoly ∧
      finrank k (((singularChains k).obj (TopCat.of M)).homology 1) =
        finrank k ((TopCat.of M).singularCohomology (𝟙_ (ModuleCat k)) k (𝟙_ (ModuleCat k)) 1) ∧
      LinearMap.det (LinearMap.id - ContinuousMap.singularHomologyMap k 1 f) =
        LinearMap.det (LinearMap.id - (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat k))
          (k := k) (M := 𝟙_ (ModuleCat k)) (TopCat.ofHom f) 1).hom) := by
  -- `f_*` is by definition the map of the singular homology functor on `f`
  -- (`ContinuousMap.singularHomologyMap_eq_singularHomologyFunctor_map`).
  have := finite_singularCohomology_one (M := M) k
  have : Module.Finite k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat k) 1).obj
      (ModuleCat.of k k)).obj (TopCat.of M)) := finiteDimensional_singularChains_homology M k 1
  exact ⟨(TopCat.charpoly_singularCohomologyMap _ 1).symm,
    ((TopCat.of M).finrank_singularCohomology 1).symm,
    (TopCat.det_id_sub_singularCohomologyMap _ 1).symm⟩

/-- **Self-reciprocity for a surface map of degree one.** For a self-map `f` of degree one of a
compact connected homologically oriented surface of finite CW type, such as an
orientation-preserving homeomorphism, and a field `k` with `2 ≠ 0`, the polynomial
`p (t) = det (1 - t f_* | H₁(M; k))` satisfies `t ^ (2 g) p (1 / t) = p (t)`, where
`2 g = dim H₁(M; k)`. -/
theorem reflect_reverse_charpoly_singularHomologyMap_one (h2 : (2 : k) ≠ 0) {f : C(M, M)}
    (hf : o.degree o hE f = 1) :
    (ContinuousMap.singularHomologyMap k 1 f).charpoly.reverse.reflect
        (finrank k (((singularChains k).obj (TopCat.of M)).homology 1)) =
      (ContinuousMap.singularHomologyMap k 1 f).charpoly.reverse := by
  obtain ⟨hB, hnd, hf'⟩ := o.isAlt_and_nondegenerate_and_isIsometry_singularCupPairing hE k h2 hf
  have := finite_singularCohomology_one (M := M) k
  obtain ⟨hchar, hrank, -⟩ := charpoly_and_finrank_and_det_singularHomologyMap_one k f
  rw [hchar, hrank]
  exact hf'.reflect_reverse_charpoly hB hnd

/-- **The reciprocal-polynomial identity for a surface map of degree one.** For a self-map `f` of
degree one of a compact connected homologically oriented surface of finite CW type and a field
`k` with `2 ≠ 0`, the polynomial `p (t) = det (1 - t f_* | H₁(M; k))` satisfies
`p' (1) = g det (1 - f_*)`, where `2 g = dim H₁(M; k)`. -/
theorem derivative_eval_one_reverse_charpoly_singularHomologyMap_one (h2 : (2 : k) ≠ 0)
    {f : C(M, M)} (hf : o.degree o hE f = 1) :
    (ContinuousMap.singularHomologyMap k 1 f).charpoly.reverse.derivative.eval 1 =
      ((finrank k (((singularChains k).obj (TopCat.of M)).homology 1) / 2 : ℕ) : k) *
        LinearMap.det (LinearMap.id - ContinuousMap.singularHomologyMap k 1 f) := by
  obtain ⟨hB, hnd, hf'⟩ := o.isAlt_and_nondegenerate_and_isIsometry_singularCupPairing hE k h2 hf
  have := finite_singularCohomology_one (M := M) k
  obtain ⟨hchar, hrank, hdet⟩ := charpoly_and_finrank_and_det_singularHomologyMap_one k f
  rw [hchar, hrank, hdet, ← Module.End.one_eq_id]
  exact hf'.derivative_eval_one_reverse_charpoly hB hnd

/-- **The coarse coefficients of the Lefschetz zeta function of a surface map of degree one.** For
a self-map `f` of degree one of a compact connected homologically oriented surface of finite CW
type, such as an orientation-preserving homeomorphism, and a field `k` of characteristic zero,
the coefficient of `t ^ a` in the Lefschetz zeta function
`ζ_f = det (1 - t f_* | H₁(M; k)) / (1 - t)²` is `det (1 - f_*) (a + 1 - g)` for every
`a ≥ 2 g - 1`, where `2 g = dim H₁(M; k)`. -/
theorem coeff_lefschetzZeta_of_degree_eq_one [Algebra ℚ k] {f : C(M, M)}
    (hf : o.degree o hE f = 1) {a : ℕ}
    (ha : finrank k (((singularChains k).obj (TopCat.of M)).homology 1) ≤ a + 1) :
    PowerSeries.coeff a (f.lefschetzZeta k) =
      LinearMap.det (LinearMap.id - ContinuousMap.singularHomologyMap k 1 f) *
        ((a : k) + 1 - ((finrank k (((singularChains k).obj (TopCat.of M)).homology 1) / 2 : ℕ) :
          k)) := by
  have : CharZero k := algebraRat.charZero k
  have h2 : (2 : k) ≠ 0 := two_ne_zero
  obtain ⟨hB, hnd, hf'⟩ := o.isAlt_and_nondegenerate_and_isIsometry_singularCupPairing hE k h2 hf
  have := finite_singularCohomology_one (M := M) k
  obtain ⟨hchar, hrank, hdet⟩ := charpoly_and_finrank_and_det_singularHomologyMap_one k f
  rw [hrank] at ha ⊢
  -- Over a field, `((1 - t) ^ 2)⁻¹ = (∑ tⁿ) ^ 2`.
  have hinv : ((1 - PowerSeries.X : k⟦X⟧) ^ 2)⁻¹ = PowerSeries.mk 1 ^ 2 :=
    ((PowerSeries.eq_inv_iff_mul_eq_one (by simp)).2
      (by rw [← mul_pow, PowerSeries.mk_one_mul_one_sub_eq_one, one_pow])).symm
  rw [o.lefschetzZeta_eq_reverse_charpoly_mul_inv_of_degree_eq_one hE k hf, hchar, hdet, hinv,
    ← Module.End.one_eq_id]
  exact hf'.coeff_coe_reverse_charpoly_mul_mk_one_sq hB hnd ha

end Symplectic


end TauCeti.HomologicalOrientation
