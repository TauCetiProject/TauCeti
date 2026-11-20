/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.ComplexProjectiveSpace.Hopf.LoopSpace
public import TauCeti.AlgebraicTopology.Singular.MappingTorus.Refl
public import TauCeti.AlgebraicTopology.Homotopy.LoopSpace.Hurewicz
public import TauCeti.AlgebraicTopology.Singular.Homotopy.WeakHomotopyEquivalence
public import TauCeti.AlgebraicTopology.Singular.Cubical.Based.Retraction
public import TauCeti.AlgebraicTopology.Homotopy.LoopSpace.Sphere.Basic
import TauCeti.Analysis.InnerProductSpace.Euclidean.Space

/-!
# The homology of the loop space of `CPⁿ`

Let `q : S²ⁿ⁺¹ → CPⁿ` be the Hopf fibration, `n ≥ 1`, and `ΩCPⁿ` the Moore loop space at the image
of a unit vector `v`. The based Hopf product `j ⋆ Ωq : S¹ × ΩS²ⁿ⁺¹ → ΩCPⁿ` is a weak homotopy
equivalence (`TauCeti.ComplexProjectiveSpace.exists_isWeakHomotopyEquivalence_hopfProduct`), and
the homology of `ΩS²ⁿ⁺¹` is `R` in the degrees divisible by `2n` and zero in the others
(`TauCeti.singularHomologyMooreLoopSpaceSphereIso` and
`TauCeti.isZero_singularHomology_mooreLoopSpace_sphere`). This file reads off the
homology of `ΩCPⁿ` from the homology of a product with a circle
(`TauCeti.isIso_singularHomologyMap_prodMk_const_one_succ_iff`,
`TauCeti.isZero_singularHomology_circle_prod_succ_iff` and
`TauCeti.singularHomologyCircleProdSuccIso`), with coefficients in any ring `R`: it is `R` in the
degrees `0` and `1` modulo `2n` and zero in the others.

* `H_{k+1}(ΩCPⁿ; R) = 0` when `2n` divides neither `k + 1` nor `k`
  (`TauCeti.ComplexProjectiveSpace.isZero_singularHomology_mooreLoopSpace`);
* the looped Hopf map `Ωq : ΩS²ⁿ⁺¹ → ΩCPⁿ` induces an isomorphism
  `H_{k+1}(ΩS²ⁿ⁺¹; R) ≅ H_{k+1}(ΩCPⁿ; R)` when `2n` does not divide `k`
  (`TauCeti.ComplexProjectiveSpace.isIso_singularHomologyMap_mooreLoopSpaceMap`), and so
  `H_{2nj}(ΩCPⁿ; R) ≅ R` for every `j`
  (`TauCeti.ComplexProjectiveSpace.singularHomologyMooreLoopSpaceIso`);
* `H_{2nj+1}(ΩCPⁿ; R) ≅ R` for every `j`
  (`TauCeti.ComplexProjectiveSpace.singularHomologyMooreLoopSpaceSuccIso`), through
  `H_{2nj+1}(S¹ × ΩS²ⁿ⁺¹) ≅ H_{2nj}(ΩS²ⁿ⁺¹)`.

The restriction of `j ⋆ Ωq` to `{1} × ΩS²ⁿ⁺¹` is `Ωq`, since `j 1` is the unit
(`TauCeti.ComplexProjectiveSpace.hopfProduct_comp_prodMk_const_one`), and `Hₖ(ΩS²ⁿ⁺¹)` vanishes
when `2n` does not divide `k`, so the inclusion at `1` is an isomorphism on `H_{k+1}`.

With integer coefficients, composing with the Hurewicz isomorphism of the loop space gives the
explicit generator of `H_{2n}(ΩCPⁿ; ℤ) ≅ ℤ`: it is the image under `Ωq` of the Hurewicz class of
the loop of spheres adjoint to a generator of `π_{2n+1}(S²ⁿ⁺¹) ≅ ℤ`
(`TauCeti.ComplexProjectiveSpace.mooreLoopSpaceHomologyAddEquiv` and
`TauCeti.ComplexProjectiveSpace.mooreLoopSpaceHomologyIntAddEquiv`). These are stated for `CPⁿ⁺¹`,
so that the degree `2n + 2` is a positive numeral offset.

## Main results

* `TauCeti.ComplexProjectiveSpace.isZero_singularHomology_mooreLoopSpace`: `H_{k+1}(ΩCPⁿ; R) = 0`
  when `2n` divides neither `k + 1` nor `k`.
* `TauCeti.ComplexProjectiveSpace.isIso_singularHomologyMap_mooreLoopSpaceMap`:
  `Ωq : H_{k+1}(ΩS²ⁿ⁺¹; R) ≅ H_{k+1}(ΩCPⁿ; R)` when `2n` does not divide `k`.
* `TauCeti.ComplexProjectiveSpace.singularHomologyMooreLoopSpaceIso`: `H_{2nj}(ΩCPⁿ; R) ≅ R`.
* `TauCeti.ComplexProjectiveSpace.singularHomologyMooreLoopSpaceSuccIso`:
  `H_{2nj+1}(ΩCPⁿ; R) ≅ R`.
* `TauCeti.ComplexProjectiveSpace.mooreLoopSpaceHomologyAddEquiv`:
  `π_{2n+3}(S²ⁿ⁺³) ≃+ H_{2n+2}(ΩCPⁿ⁺¹; ℤ)`, through `Ωq` and the Hurewicz isomorphism.
* `TauCeti.ComplexProjectiveSpace.mooreLoopSpaceHomologyIntAddEquiv`:
  `H_{2n+2}(ΩCPⁿ⁺¹; ℤ) ≃+ ℤ`, given an orthonormal basis of `ℂⁿ⁺²` over `ℝ`.

## References

* A. Hatcher, *Algebraic Topology*, Example 4.45 and Section 2.2, Example 2.48.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4 (Proposition 6.38).
-/

public section

noncomputable section

open CategoryTheory Limits Metric AlgebraicTopology
open scoped Topology Topology.Homotopy

namespace TauCeti.ComplexProjectiveSpace

variable {n : ℕ} (v : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1)

/-- The homology of `ΩS²ⁿ⁺¹` vanishes in the degrees not divisible by `2n`. -/
private lemma isZero_singularHomology_mooreLoopSpace_oddSphere (hn : n ≠ 0) (R : Type)
    [Ring R] {k : ℕ} (hk : ¬ 2 * n ∣ k) :
    IsZero (((singularHomologyFunctor (ModuleCat.{0} R) k).obj (ModuleCat.of R R)).obj
      (TopCat.of (MooreLoopSpace (sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) v))) :=
  isZero_singularHomology_mooreLoopSpace_sphere
    (finrank_real_euclideanSpace_complex n) (by omega) v R (by simpa using hk)

/-- **The homology of `ΩCPⁿ` vanishes in the positive degrees that are not `0` or `1` modulo
`2n`**: `H_{k+1}(ΩCPⁿ; R) = 0` when `2n` divides neither `k + 1` nor `k`, with coefficients in any
ring, for `n ≥ 1`. -/
theorem isZero_singularHomology_mooreLoopSpace (hn : n ≠ 0) (R : Type) [Ring R] {k : ℕ}
    (hk₁ : ¬ 2 * n ∣ k + 1) (hk : ¬ 2 * n ∣ k) :
    IsZero (((singularHomologyFunctor (ModuleCat.{0} R) (k + 1)).obj (ModuleCat.of R R)).obj
      (TopCat.of (MooreLoopSpace (ComplexProjectiveSpace n) (mk n v)))) := by
  obtain ⟨j, -, hw⟩ := exists_isWeakHomotopyEquivalence_hopfProduct v hn
  have := hw.isIso_singularHomologyMap (ModuleCat.of R R) (k + 1)
  refine IsZero.of_iso ?_ (asIso (((singularHomologyFunctor (ModuleCat.{0} R) (k + 1)).obj
    (ModuleCat.of R R)).map (TopCat.ofHom (hopfProduct v j)))).symm
  -- `ΩCPⁿ` is weakly equivalent to `S¹ × ΩS²ⁿ⁺¹`, whose `Hₖ₊₁` vanishes with `Hₖ₊₁` and `Hₖ` of
  -- `ΩS²ⁿ⁺¹`.
  exact (isZero_singularHomology_circle_prod_succ_iff _ k).2
    ⟨isZero_singularHomology_mooreLoopSpace_oddSphere v hn R hk₁,
      isZero_singularHomology_mooreLoopSpace_oddSphere v hn R hk⟩

/-- The looped Hopf map `Ωq : ΩS²ⁿ⁺¹ → ΩCPⁿ` is an isomorphism on `Hₖ` whenever the inclusion
`ΩS²ⁿ⁺¹ → S¹ × ΩS²ⁿ⁺¹` at `1` is, since it is that inclusion followed by the weak homotopy
equivalence `j ⋆ Ωq`. -/
private lemma isIso_singularHomologyMap_mooreLoopSpaceMap_of_isIso (hn : n ≠ 0) (R : Type)
    [Ring R] (k : ℕ)
    (h : IsIso (((singularHomologyFunctor (ModuleCat.{0} R) k).obj (ModuleCat.of R R)).map
      (TopCat.ofHom ((ContinuousMap.const _ (1 : Circle)).prodMk (ContinuousMap.id
        (MooreLoopSpace (sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) v)))))) :
    IsIso (((singularHomologyFunctor (ModuleCat.{0} R) k).obj (ModuleCat.of R R)).map
      (TopCat.ofHom
        (MooreLoopSpace.map (x := v) ⟨mk n, continuous_mk n⟩ rfl).toContinuousMap)) := by
  obtain ⟨j, hj, hw⟩ := exists_isWeakHomotopyEquivalence_hopfProduct v hn
  rw [← hopfProduct_comp_prodMk_const_one v hj, TopCat.ofHom_comp, Functor.map_comp]
  have := hw.isIso_singularHomologyMap (ModuleCat.of R R) k
  infer_instance

/-- **The looped Hopf map `Ωq : ΩS²ⁿ⁺¹ → ΩCPⁿ` is an isomorphism on `H_{k+1}` when `2n` does not
divide `k`**, with coefficients in any ring, for `n ≥ 1`. In particular it is one on `H_{2nj}` for
every `j ≥ 1`. -/
theorem isIso_singularHomologyMap_mooreLoopSpaceMap (hn : n ≠ 0) (R : Type) [Ring R] {k : ℕ}
    (hk : ¬ 2 * n ∣ k) :
    IsIso (((singularHomologyFunctor (ModuleCat.{0} R) (k + 1)).obj (ModuleCat.of R R)).map
      (TopCat.ofHom
        (MooreLoopSpace.map (x := v) ⟨mk n, continuous_mk n⟩ rfl).toContinuousMap)) :=
  -- The inclusion at `1` is an isomorphism on `Hₖ₊₁`, since `Hₖ(ΩS²ⁿ⁺¹)` vanishes.
  isIso_singularHomologyMap_mooreLoopSpaceMap_of_isIso v hn R (k + 1)
    ((isIso_singularHomologyMap_prodMk_const_one_succ_iff _ k).2
      (isZero_singularHomology_mooreLoopSpace_oddSphere v hn R hk))

/-- The looped Hopf map `Ωq : ΩS²ⁿ⁺¹ → ΩCPⁿ` is an isomorphism on `H_{2nj}` for every `j`. -/
private lemma isIso_singularHomologyMap_mooreLoopSpaceMap_mul (hn : n ≠ 0) (R : Type) [Ring R]
    (j : ℕ) :
    IsIso (((singularHomologyFunctor (ModuleCat.{0} R) (2 * n * j)).obj (ModuleCat.of R R)).map
      (TopCat.ofHom
        (MooreLoopSpace.map (x := v) ⟨mk n, continuous_mk n⟩ rfl).toContinuousMap)) := by
  rcases j with _ | j
  · -- In degree `0` the inclusion at `1` is an isomorphism.
    exact isIso_singularHomologyMap_mooreLoopSpaceMap_of_isIso v hn R 0 inferInstance
  · -- `2n(j + 1) = k + 1` with `k = 2nj + 2n - 1`, which `2n` does not divide.
    obtain ⟨k, hk⟩ : ∃ k, 2 * n * (j + 1) = k + 1 := ⟨2 * n * j + (2 * n - 1), by
      rw [Nat.mul_succ]; omega⟩
    rw [hk]
    refine isIso_singularHomologyMap_mooreLoopSpaceMap v hn R fun h ↦ ?_
    have := Nat.dvd_one.1 ((Nat.dvd_add_right h).1 (hk ▸ dvd_mul_right (2 * n) (j + 1)))
    omega

/-- **The homology of `ΩCPⁿ` in the degrees divisible by `2n`**: `H_{2nj}(ΩCPⁿ; R) ≅ R` for every
`j`, with coefficients in any ring, for `n ≥ 1`. It is the inverse of the isomorphism induced by
the looped Hopf map `Ωq : ΩS²ⁿ⁺¹ → ΩCPⁿ`, followed by
`TauCeti.singularHomologyMooreLoopSpaceSphereIso`. -/
def singularHomologyMooreLoopSpaceIso (hn : n ≠ 0) (R : Type) [Ring R] (j : ℕ) :
    ((singularHomologyFunctor (ModuleCat.{0} R) (2 * n * j)).obj (ModuleCat.of R R)).obj
        (TopCat.of (MooreLoopSpace (ComplexProjectiveSpace n) (mk n v))) ≅ ModuleCat.of R R :=
  have := isIso_singularHomologyMap_mooreLoopSpaceMap_mul v hn R j
  (asIso (((singularHomologyFunctor (ModuleCat.{0} R) (2 * n * j)).obj (ModuleCat.of R R)).map
      (TopCat.ofHom
        (MooreLoopSpace.map (x := v) ⟨mk n, continuous_mk n⟩ rfl).toContinuousMap))).symm ≪≫
    eqToIso (by rw [Nat.add_sub_cancel, mul_comm]) ≪≫
    singularHomologyMooreLoopSpaceSphereIso (finrank_real_euclideanSpace_complex n) (by omega) v
      R j

/-- **The homology of `ΩCPⁿ` in the degrees `1` modulo `2n`**: `H_{2nj+1}(ΩCPⁿ; R) ≅ R` for every
`j`, with coefficients in any ring, for `n ≥ 1`. Through the weak homotopy equivalence
`j ⋆ Ωq : S¹ × ΩS²ⁿ⁺¹ → ΩCPⁿ` it is `H_{2nj+1}(S¹ × ΩS²ⁿ⁺¹) ≅ H_{2nj}(ΩS²ⁿ⁺¹)`
(`TauCeti.singularHomologyCircleProdSuccIso`), followed by
`TauCeti.singularHomologyMooreLoopSpaceSphereIso`. -/
def singularHomologyMooreLoopSpaceSuccIso (hn : n ≠ 0) (R : Type) [Ring R] (j : ℕ) :
    ((singularHomologyFunctor (ModuleCat.{0} R) (2 * n * j + 1)).obj (ModuleCat.of R R)).obj
        (TopCat.of (MooreLoopSpace (ComplexProjectiveSpace n) (mk n v))) ≅ ModuleCat.of R R :=
  have hw := (exists_isWeakHomotopyEquivalence_hopfProduct v hn).choose_spec.2
  have := hw.isIso_singularHomologyMap (ModuleCat.of R R) (2 * n * j + 1)
  (asIso (((singularHomologyFunctor (ModuleCat.{0} R) (2 * n * j + 1)).obj
      (ModuleCat.of R R)).map (TopCat.ofHom (hopfProduct v
        (exists_isWeakHomotopyEquivalence_hopfProduct v hn).choose)))).symm ≪≫
    singularHomologyCircleProdSuccIso _
      (isZero_singularHomology_mooreLoopSpace_oddSphere v hn R fun h ↦ by
        -- `2n ≥ 2` does not divide `2nj + 1`.
        have := Nat.dvd_one.1 ((Nat.dvd_add_right (dvd_mul_right _ _)).1 h)
        omega) ≪≫
    eqToIso (by rw [Nat.add_sub_cancel, mul_comm]) ≪≫
    singularHomologyMooreLoopSpaceSphereIso (finrank_real_euclideanSpace_complex n) (by omega) v
      R j

/-! ### The integral generator -/

section Integral

variable (v : sphere (0 : EuclideanSpace ℂ (Fin (n + 2))) 1)

private instance isIso_homologyMap_mooreLoopSpaceMap :
    IsIso (HomologicalComplex.homologyMap ((singularChains ℤ).map
      (TopCat.ofHom (MooreLoopSpace.map (x := v) ⟨mk (n + 1), continuous_mk (n + 1)⟩
        rfl).toContinuousMap)) (2 * n + 2)) := by
  have h := isIso_singularHomologyMap_mooreLoopSpaceMap v n.succ_ne_zero ℤ (k := 2 * n + 1)
    (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))
  -- `singularHomologyFunctor` is by definition the homology of the singular chain complex, and
  -- the degree `2 * n + 1 + 1` of `h` reduces to `2 * n + 2` by `Nat` arithmetic.
  exact h

/-- **`H_{2n+2}(ΩCPⁿ⁺¹; ℤ) ≅ π_{2n+3}(S²ⁿ⁺³)`**: the Hurewicz isomorphism
`π_{2n+3}(S²ⁿ⁺³) ≅ H_{2n+2}(ΩS²ⁿ⁺³; ℤ)` of the loop space, followed by the isomorphism induced by
the looped Hopf map `Ωq`. -/
def mooreLoopSpaceHomologyAddEquiv :
    Additive (π_ (2 * n + 3) (sphere (0 : EuclideanSpace ℂ (Fin (n + 2))) 1) v) ≃+
      ((singularChains ℤ).obj
        (TopCat.of (MooreLoopSpace (ComplexProjectiveSpace (n + 1)) (mk (n + 1) v)))).homology
          (2 * n + 2) :=
  (MooreLoopSpace.homologyAddEquiv v (2 * n)
      (fun k _ ↦ subsingleton_homotopyGroup_sphere (N := Fin (k + 1)) (by simp; omega) v)).trans
    (asIso (HomologicalComplex.homologyMap ((singularChains ℤ).map
      (TopCat.ofHom (MooreLoopSpace.map (x := v) ⟨mk (n + 1), continuous_mk (n + 1)⟩
        rfl).toContinuousMap)) (2 * n + 2))).toLinearEquiv.toAddEquiv

/-- `TauCeti.ComplexProjectiveSpace.mooreLoopSpaceHomologyAddEquiv` sends a class of
`π_{2n+3}(S²ⁿ⁺³)` to the image under `Ωq` of its Hurewicz class in the loop space. -/
theorem mooreLoopSpaceHomologyAddEquiv_apply
    (a : Additive (π_ (2 * n + 3) (sphere (0 : EuclideanSpace ℂ (Fin (n + 2))) 1) v)) :
    mooreLoopSpaceHomologyAddEquiv v a =
      (HomologicalComplex.homologyMap ((singularChains ℤ).map
        (TopCat.ofHom (MooreLoopSpace.map (x := v) ⟨mk (n + 1), continuous_mk (n + 1)⟩
          rfl).toContinuousMap)) (2 * n + 2)).hom
        (MooreLoopSpace.homologyAddEquiv v (2 * n)
          (fun k _ ↦ subsingleton_homotopyGroup_sphere (N := Fin (k + 1)) (by simp; omega) v) a) :=
  (rfl)

/-- **`H_{2n+2}(ΩCPⁿ⁺¹; ℤ) ≅ ℤ`.** The inverse of `mooreLoopSpaceHomologyAddEquiv`, followed by
the isomorphism `π_{2n+3}(S²ⁿ⁺³) ≅ ℤ` determined by an orthonormal basis `b` of `ℂⁿ⁺²` over `ℝ`.
The class corresponding to `1` is the image under `Ωq` of the Hurewicz class of the generator of
`π_{2n+3}(S²ⁿ⁺³)` fixed by `b`. -/
def mooreLoopSpaceHomologyIntAddEquiv
    (b : OrthonormalBasis (Fin (2 * n + 4)) ℝ (EuclideanSpace ℂ (Fin (n + 2)))) :
    ((singularChains ℤ).obj
        (TopCat.of (MooreLoopSpace (ComplexProjectiveSpace (n + 1)) (mk (n + 1) v)))).homology
          (2 * n + 2) ≃+ ℤ :=
  (mooreLoopSpaceHomologyAddEquiv v).symm.trans (homotopyGroupSphereAddEquiv (n := 2 * n + 1) b v)

/-- The generator `1` of `ℤ` corresponds under `mooreLoopSpaceHomologyIntAddEquiv` to the image
under `Ωq` of the Hurewicz class of the generator of `π_{2n+3}(S²ⁿ⁺³)` fixed by `b`. -/
theorem mooreLoopSpaceHomologyIntAddEquiv_symm_apply
    (b : OrthonormalBasis (Fin (2 * n + 4)) ℝ (EuclideanSpace ℂ (Fin (n + 2)))) (m : ℤ) :
    (mooreLoopSpaceHomologyIntAddEquiv v b).symm m =
      mooreLoopSpaceHomologyAddEquiv v
        ((homotopyGroupSphereAddEquiv (n := 2 * n + 1) b v).symm m) :=
  (rfl)

end Integral

end TauCeti.ComplexProjectiveSpace
